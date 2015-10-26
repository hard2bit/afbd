/*
 * An antiforensics block device driver for Western Digital (Marvell & Marvell ROYL) hard drives
 *
 *	PCI SATA device address: 01.f5
 * 	I/O ports at b080 [size=8] <---
 *	I/O ports at b000 [size=4]
 *	I/O ports at ac00 [size=8] <---
 *
 *	COMPILE:	make -C /lib/modules/`uname -r`/build M=`pwd` modules
 *        (In order for the compiler to compile this code, you'll need to download 
 *        the Linux headers package from your repository. Valid for kernel versions
 *        such that 2.6 < kv < 3.16, until someone handles the new kernel changes at
 *        the block layer -regarding the struct request-.)
 *	USE:		insmod afbd.ko
 *	REMOVE:		rmmod afbd.ko
 *
 *
 * ATA TASK REGISTERS 0-7
 *
 *  REGISTER 0: Base Port
 *  REGISTER 1: Error STATUS (read)
 *  REGISTER 2: Sector count to transfer
 *
 *  REGISTERS 3-5
 *    R3 - 0:7 = Sector address LBA 0 (0:7)
 *    R4 - 0:7 = Sector address LBA 1 (8:15)
 *    R5 - 0:7 = Sector address LBA 2 (16:23)
 *
 *  REGISTER 6
 *    Bit 0:3 = LBA bits (24:27)
 *    Bit 4   = Select Master (0) or Slave (1) drive
 *    Bit 5   = Always set to 1
 *    Bit 6   = Set to 1 for LBA Mode Access
 *    Bit 7   = Always set to 1
 *
 *  REGISTER 7 (issue command when written to, read STATUS when read from)
 *    Example: 0xEC (Identify device)
 *
 *
 *	AFBD - ANTIFORENSICS BLOCK DEVICE, by Daniel O'Grady Rueda <daniel.ogrady@hard2bit.com>
 *  Based on the extra-simple block device example driver for kernel 2.6.31+ by Pat Patterson (2003 Eklektix, Inc.,
 *  2010 Pat Patterson <pat at superpat dot com>) and on the WD POC developed by Ariel Berkman <ariel@recover.co.il> from Recover Information Technologies LTD.
 *
 * (C) Copyright 2014 Daniel O'Grady Rueda <daniel.ogrady@hard2bit.com> - Hard2bit Data Forensics
 * (C) 2010 Pat Patterson <pat at superpat dot com>
 * (C) 2003 Eklektix, Inc.
 *
 * This program is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   This program is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with this program.  If not, see <http://www.gnu.org/licenses/>.
 
 
 */

#include <linux/module.h>
#include <linux/moduleparam.h>
#include <linux/init.h>

#include <linux/kernel.h> /* printk() */
#include <linux/fs.h>     /* everything else */
#include <linux/errno.h>  /* error codes */
#include <linux/types.h>  /* size_t */
#include <linux/vmalloc.h>
#include <linux/genhd.h>
#include <linux/blkdev.h>
#include <linux/hdreg.h>


/*********************************
 *         DEFINE BLOCK          *
 *********************************/

#define REALLY_SLOW_IO

// Status register
#define ATA_SR_BSY     0x80
#define ATA_SR_DRDY    0x40
#define ATA_SR_DF      0x20
#define ATA_SR_DSC     0x10
#define ATA_SR_DRQ     0x08
#define ATA_SR_CORR    0x04
#define ATA_SR_IDX     0x02
#define ATA_SR_ERR     0x01

// Error register
#define ATA_ER_BBK      0x80
#define ATA_ER_UNC      0x40
#define ATA_ER_MC       0x20
#define ATA_ER_IDNF     0x10
#define ATA_ER_MCR      0x08
#define ATA_ER_ABRT     0x04
#define ATA_ER_TK0NF    0x02
#define ATA_ER_AMNF     0x01

// Kernel's sector size
#define KERNEL_SECTOR_SIZE 512


/*********************************
 *   LICENSE AND MODULE VERSION  *
 *********************************/

MODULE_LICENSE("Dual BSD/GPL");
static char *Version = "0.1";


/*********************************
 *    DRIVER MODULE VARIABLES    *
 *********************************/

static int major_num = 0;
module_param(major_num, int, 0);

static int phy_block_size = 512;        // For now we assume it's 512, as most of devices have 512 bytes currently.
module_param(phy_block_size, int, 0);   // Bind the physical block size to the module.

static unsigned char regs = 0;
static unsigned int busy=0, drdy=0, df=0, dsc=0, drq=0, corr=0, idx=0, err=0, ready=0, drsc=0;    // Status register bits
static unsigned int bbk=0, unc=0, mc=0, idnf=0, mcr=0, abrt=0, tk0nf=0, amnf=0;                   // Error register bits
static int p0=0, p1=0, p2=0, p3=0, p4=0, p5=0, p6=0, p7=0;                                        // I/O port address

static int baseport = 0xb080;	// Obtained through lspci -v, lspci -D and ls -l /sys/bus/pci/devices/
				// 0000\:00\:1f.5/host4/target4\:0\:0/4\:0\:0\:0/block/, for the PoC.
static int sa_spt = 0;          // Sectors per track in SA zone
static int sa_cyl = 0;          // Tracks per head corresponding to SA zone
static int vheads = 0;          // Number of heads in device
static int aheads = 0;          // Number of available heads for the driver (vheads - 2)
static int headmask = 0;        // Head map

static int nsectors = -1;       // Device size in sectors

module_param(nsectors, int, 0);


/*********************************
 *   DRIVER MODULE STRUCTURES    *
 *********************************/

 // PCHS block for translation
static struct pchs {
    int c;
    unsigned short h;
    unsigned short s;
};

static struct logical_heads {
    unsigned short h0;
    unsigned short h1;
    unsigned short h2;
    unsigned short h3;
    unsigned short h4;
    unsigned short h5;
    unsigned short h6;
    unsigned short h7;
} lheads;
 
// Device ID
static struct dev_id {
    short general_conf;
    short ob[9];
    char sn[20];
    short ob1[3];
    char fwver[8];
    char model[40];
    short f1;
    short res1;
    short cap[2];
    short ob2[9];
    int lba28sec;
    short ob3;
    short mwdmamodes;
    short piomodes;
    short ob4[15];
    short verma;
    short vermi;
    short features[6];
    short dmamodes;
    short secerasetime;
    short ensecerasetime;
    short apm;
    short mpr;
    short hwrs;
    short ob5[6];
    int lba48sec;
    short ob6[13];
    short wps;
    short ob7[8];
    short rms;
    short secstat;
    char vendorspec[62];
    short cpapower;
    char reserved_cf[30];
    char media_sn[60];
    char res[98];
    short in;
};

// Request queue
static struct request_queue *Queue;

// Device representation struct
static struct afd_device {
    unsigned long size;
    spinlock_t lock;
    char model[64];
    struct gendisk *gd;
} Device;

// For performance testing
static struct timespec timest;


/*********************************
 *       FUNCTION HEADERS        *
 *********************************/
 
static void afd_transfer(struct afd_device* dev, sector_t sector,                // Handles an I/O transfer.
    unsigned long nsect, char* buffer, int write);
static void afd_request(struct request_queue* q);                                // Handles an I/O request.
int afd_getgeo(struct block_device* block_device, struct hd_geometry* geo);      // Need to implement in order to use fdisk and the like.
static int __init afd_init(void);                                                // Initialze drive parameters.
static void __exit afd_exit(void);                                               // Free resources.
static void read_regs(void);                                                     // Read drive's status register.
static void status(int times);                                                   // Print drive status n times.
static int waitready(int secs);                                                  // Wait for device setting readiness status.
static int waitnobusy(int secs);                                                 // Wait for device clearing busy status.
static int waitdrq(int secs);                                                    // Wait for device setting data request status.
static int waitnodrq(int secs);                                                  // Wait for device clearing data request status.

static int vsc_mode_on(void);                                                    // Prepare the device to accept vendor specific commands.
static int vsc_mode_off(void);                                                   // End VSCE mode.
static void write_buffer (char* sector);                                         // Write 512 bytes buffer (256w) to the device.
static void read_buffer (char* sector);                                          // Read 512 bytes (256w) into char buffer.

static int get_saspt(char* cp5, int royl);                                       // Read Service Area's zone Sector Per Track integer.
static int get_sacyl(char* cp1);                                                 // Read Service Area's track count.
static int get_vheads(char* cp1);                                                // Get the number of installed & active heads.
static int get_headmask(char* cp1);                                              // Get the active head binary mask.
static int get_dev_family_code(char* model, char* family_code);                  // WD Marvell 2 or 3 digits family code.
static int set_logical_heads(int headmask);                                      // Need a means for quickly translating logical heads to physical ones.
static int is_compatible(char* family_code, int* royl);                          // Check for compatibility given family code. NOT IMPLEMENTED.

static int get_dev_id(struct dev_id* d);                                         // Read ATA Device ID
static int read_dev_pchs(char* buffer, short head, int track,                    // Read device physical sectors in CHS format into char buffer.
    short sector, short scount);
static int write_dev_pchs(char* buffer, short head, int track,                   // Write char buffer into drive using physical CHS format.
    short sector, short scount);
static sector_t xlate_pchs(struct pchs chs);                                     // Translate a PCHS sector into LBA equivalent.
static struct pchs xlate_pba(sector_t pba);                                      // Translate an LBA sector into its CHS coordinates.
static int write_block(char* buffer, sector_t pba, unsigned long scount);        // Write data block to device.
static int read_block(char* buffer, sector_t pba, unsigned long scount);         // Read block
static int send_longvsc_cmd(short command, short p1, short p2,                   // Send ATA command to the device.
    short p3, short p4, short p5, short p6);
static int dev_pre_xfer_cmd(unsigned char length);                               // Set buffer length to operate with through the ATA port.
static int send_vsc_cmd(short command, short para1, short para2);                // Send command
static int dev_get_cp(short cp, char** out_buff, int * len);                     // Read device configuration page
static void flip (char* buf, int len);                                           // Flip every two bytes in the chain.
static void usleep(int millis);	                                                 // We need our own implementation of usleep. Single writing operations to port 0x80 should take about 1 ms.
static void print_status(char * msg);

/*********************************
 *   FUNCTION IMPLEMENTATIONS    *
 *********************************/

/*
 * Handle an I/O request.
 */
static void afd_transfer(struct afd_device *dev, sector_t sector,
        unsigned long nsect, char *buffer, int write) {
    unsigned long offset = sector * phy_block_size;
    unsigned long nbytes = nsect * phy_block_size;

    if ((offset + nbytes) > dev->size) {
        printk (KERN_NOTICE "afd: Beyond-end write (%ld %ld)\n", offset, nbytes);
        return;
    }
    if (write) {
        write_block(buffer, sector, nsect);
    } else {
        read_block(buffer, sector, nsect);
    }
}

static void afd_request(struct request_queue * q) {
    struct request * req;
    req = blk_fetch_request(q);
   
    while (req != NULL) {
        if (req == NULL || (req->cmd_type != REQ_TYPE_FS)) {
            printk (KERN_NOTICE "Skip non-CMD request\n");
            __blk_end_request_all(req, -EIO);
            continue;
        }
        afd_transfer(&Device, blk_rq_pos(req), blk_rq_cur_sectors(req),
                req->buffer, rq_data_dir(req));
        if ( ! __blk_end_request_cur(req, 0) ) {
            req = blk_fetch_request(q);
        }
    }
}

/*
 * The HDIO_GETGEO ioctl is handled in blkdev_ioctl(), which
 * calls this. We need to implement getgeo, since we can't
 * use tools such as fdisk to partition the drive otherwise.
 */
int afd_getgeo(struct block_device * block_device, struct hd_geometry * geo) {
    long size;
    size = Device.size * (phy_block_size / KERNEL_SECTOR_SIZE);
    geo->cylinders = sa_cyl - 1;
    geo->heads = vheads;
    geo->sectors = sa_spt;
    geo->start = 0;
    return 0;
}

static struct block_device_operations afd_ops = {
    .owner  = THIS_MODULE,
    .getgeo = afd_getgeo
};

static int __init afd_init(void) {

    p0 = baseport;   

    p1 = p0+1;
    p2 = p1+1;
    p3 = p2+1;
    p4 = p3+1;
    p5 = p4+1;
    p6 = p5+1;
    p7 = p6+1;

    char model[64];
    char family_code[4];
    int royl;
    struct dev_id id;
    char* cp_buff;
    int cp_len;
    int unused_sectors;
    int unused_bytes;
    int error = 0;

    get_dev_id(&id);
    memset(family_code, 0, 4);
    memset(model, 0, 64);
    memcpy(model, id.model, 40);
    flip(model, 40);
    printk (KERN_NOTICE "afd: Detected device: %s\n", model);
    memcpy(Device.model, model, 40);

    get_dev_family_code(model, family_code);
    if (!is_compatible(family_code, &royl)) {
        printk (KERN_NOTICE "afd: Device is family %s is not compatible. Exiting.\n", family_code);
        goto out;
    }

    printk (KERN_NOTICE "afd: Family code detected: %s.\n", family_code);

    if (dev_get_cp(0x01, &cp_buff, &cp_len) == 0) {
        sa_cyl = get_sacyl(cp_buff);
        vheads = get_vheads(cp_buff);
        aheads = vheads - 2;
        headmask = get_headmask(cp_buff);
        set_logical_heads(headmask);
        printk (KERN_NOTICE "afd: Installed heads: %d.\n", vheads);
    } else {
        printk (KERN_NOTICE "afd: Error reading configuration page 0x01. Exiting.\n");
        goto out;
    }
    vfree(*&cp_buff);

    if (dev_get_cp(0x05, &cp_buff, &cp_len) == 0) {
        sa_spt = get_saspt(cp_buff, royl);
        printk (KERN_NOTICE "afd: SA SPT detected: %d.\n", sa_spt);
    } else {
        printk (KERN_NOTICE "afd: Error reading configuration page 0x05. Exiting.\n");
        goto out;
    }
    vfree(*&cp_buff);

    if (error) {
        printk (KERN_NOTICE "afd: Error reading configuration pages. Exiting.\n");
        goto out;
    }

    unused_sectors = sa_cyl * sa_spt * aheads;
    unused_bytes = sa_cyl * sa_spt * aheads * phy_block_size;

    printk(KERN_NOTICE "afd: SPT=%d, usable heads=%d, hmap=%02xh, avail. cylinders=%d, log-to-phy hmap=[%hd,%hd,%hd,%hd,%hd,%hd,%hd,%hd], usable sectors=%d [%d bytes]\n", sa_spt, aheads, headmask, sa_cyl, lheads.h0, lheads.h1, lheads.h2, lheads.h3, lheads.h4, lheads.h5, lheads.h6, lheads.h7, unused_sectors, unused_bytes);

    if (aheads <= 0) {
        printk(KERN_WARNING "afd: HDD has not enough heads in order to continue. Aborting.\n");
        goto out;
    }

    nsectors = (sa_cyl - 1) * sa_spt * (aheads);      // Device reserved area usable space in sectors. We'll skip cylinder -1 here.
    Device.size = nsectors * phy_block_size;           // Device reserved area usable space in bytes
   
    spin_lock_init(&Device.lock);
    /*
     * Get a request queue.
     */
    Queue = blk_init_queue(afd_request, &Device.lock);
    if (Queue == NULL)
        goto out;
    blk_queue_logical_block_size(Queue, phy_block_size);
    /*
     * Get registered.
     */
    major_num = register_blkdev(major_num, "afd");
    if (major_num < 0) {
        printk(KERN_WARNING "afd: unable to get major number\n");
        goto out;
    }
    /*
     * And the gendisk structure.
     */
    Device.gd = alloc_disk(16);
    if (!Device.gd)
        goto out_unregister;
    Device.gd->major = major_num;
    Device.gd->first_minor = 0;
    Device.gd->fops = &afd_ops;
    Device.gd->private_data = &Device;
    strcpy(Device.gd->disk_name, "afd");
    set_capacity(Device.gd, nsectors);
    Device.gd->queue = Queue;
    add_disk(Device.gd);

    return 0;

out_unregister:
    unregister_blkdev(major_num, "afd");
out:
    return -ENOMEM;
}

static void __exit afd_exit(void) {
    del_gendisk(Device.gd);
    put_disk(Device.gd);
    unregister_blkdev(major_num, "afd");
    blk_cleanup_queue(Queue);
}

/** Unused */
static sector_t xlate_pchs(struct pchs chs) {
    sector_t pba = ((chs.c * aheads) + chs.h) * sa_spt + chs.s + 1;
    return pba;
}

static struct pchs xlate_pba(sector_t _pba) {
    struct pchs chs;
    int pba = (int)(_pba);
    int phy_h = (pba / sa_spt) % aheads;
    chs.c = -sa_cyl + ((pba / (sa_spt * aheads)));

    switch (phy_h) {
        case 0:
            chs.h = lheads.h0;
            break;
        case 1:
            chs.h = lheads.h1;
            break;
        case 2:
            chs.h = lheads.h2;
            break;
        case 3:
            chs.h = lheads.h3;
            break;
        case 4:
            chs.h = lheads.h4;
            break;
        case 5:
            chs.h = lheads.h5;
            break;
        case 6:
            chs.h = lheads.h6;
            break;
    }

    chs.s = (short)((pba % sa_spt) + 1);
    printk(KERN_NOTICE "afd: XLATE PBA=%d --> CHS=%d,%hd,%hd.\n", pba, chs.c, chs.h, chs.s);
    return chs;
}

/****************************************************
 *    Read data block from the device - PBA function.    *
 ****************************************************/
static int read_block(char * buffer, sector_t pba, unsigned long scount) {
    char * sector;
    sector = vmalloc(phy_block_size);
    struct pchs _chs;
    int sc = 0;
    unsigned int buff_position = 0;
    for (sc=0; sc<scount; sc++) {
        _chs = xlate_pba(pba);
	int _cylinder = _chs.c;
	short _head = _chs.h;
	short _sector = _chs.s;
        if (0 == read_dev_pchs(sector, _head, _cylinder, _sector, 1)) {
	    //printk(KERN_WARNING "afd: read_block OK at sector %d (block %d), CHS=%d,%hd,%hd.\n", pba, sc, _cylinder, _head, _sector);
	} else {
            printk(KERN_WARNING "afd: read_block FAILED at sector %d (block %d), CHS=%d,%hd,%hd.\n", pba, sc, _cylinder, _head, _sector);
            vfree(sector);
            return 1;
        }
        memcpy(buffer + buff_position, sector, phy_block_size);
        buff_position += phy_block_size;
    }
    vfree(sector);
    return 0;
}


/*
 *    Read data block from the device - PCHS function.
 */
static int read_dev_pchs (char * buffer, short head, int track, short sector, short scount) {

    int sectorsread = 0;
    long int sectorslow;
    long int sectorshigh;
    char a[phy_block_size];
    int len = 0;
    int rc = 0;

    outb(0xa0, p6);    // Select master

    getnstimeofday(&timest);
    //printk(KERN_WARNING "afd: starting READ at %d.%lu\n", timest.tv_sec, timest.tv_nsec);

    read_regs();

    if (waitready(3)) {
        printk(KERN_WARNING "afd: read_dev_pchs - Drive not ready, aborting.\n");
        return(1);
    }
   
    if (vsc_mode_on()) {   
        printk(KERN_WARNING "afd: read_dev_pchs - Failed to start VSC mode, aborting.\n");
        return (1);
    }

    rc = send_longvsc_cmd(0x000c, 0x0001, (track & 0xffff), (track >> 16) & 0xffff, head, sector, scount);
    if (rc) {
        printk(KERN_WARNING "afd: read_dev_pchs - send VSC fail, aborting.\n");
        return(1);
    }

    if (waitnodrq(3)) {
        printk(KERN_WARNING "afd: read_dev_pchs - DRQ still ON, aborting.\n");
        return(1);
    }

    sectorslow = inb(p4);
    sectorshigh = inb(p5);
    len = sectorslow + (sectorshigh << 8);

    if (len < 1) {
        printk(KERN_WARNING "afd: read_dev_pchs - Nothing to read, aborting.\n");
        return(1);
    }

    sectorsread = 0;

    while (len > sectorsread) {
        rc = dev_pre_xfer_cmd(1);
        if (rc) {
            printk(KERN_WARNING "afd: read_dev_pchs - Data transfer preparation failed, aborting.\n");
            return(1);
        }

        read_regs();
        while (drq) {
            memset(a, 0, phy_block_size);
            read_buffer(a);
            memcpy(buffer + (sectorsread * phy_block_size), a, phy_block_size);
            sectorsread++;
            rc = waitready(60);
           
            if (rc) return(1);

            read_regs();
            if (err) {
                printk(KERN_WARNING "afd: read_dev_pchs - The error register was set, aborting.\n");
                return(1);   
            }
        }
    }

    if (sectorsread != len) {
        printk(KERN_WARNING "afd: read_dev_pchs - Reading incomplete.\n");
        return(1);
    }

    getnstimeofday(&timest);
    //printk(KERN_WARNING "afd: finishing READ at %d.%lu\n", timest.tv_sec, timest.tv_nsec);

    return(0);
}

/****************************************************
 *    Write data block to the device - PBA function.    *
 ****************************************************/
static int write_block(char * buffer, sector_t pba, unsigned long scount) {
    char * sector;
    sector = vmalloc(phy_block_size);
    struct pchs chs;
    int sc = 0;
    for (sc=0; sc<scount; sc++) {
        memcpy(sector, buffer, phy_block_size);
        chs = xlate_pba(pba);
        if (0 == write_dev_pchs(sector, chs.h, chs.c, chs.s, 1));
        else {
            printk(KERN_WARNING "afd: write_block failed at block %d.\n", sc);
            vfree(sector);
            return 1;
        }
    }
    vfree(sector);
    return 0;
}
/*
 *    Write data block to the device - PCHS function.
 */
static int write_dev_pchs (char * buffer, short head, int track, short sector, short scount) {
    int sectorswritten = 0;
    long int sectorslow;
    long int sectorshigh;
    char a[phy_block_size];
    int len;
    int rc;

    outb(0xa0, p6);

    getnstimeofday(&timest);
    printk(KERN_WARNING "afd: starting WRITE at %d.%lu\n", timest.tv_sec, timest.tv_nsec);

    if (waitready(3)) {
        printk(KERN_WARNING "afd: write_dev_pchs - drive not ready, aborting.\n");
        return(1);
    }
   
    if (vsc_mode_on()) {   
        printk(KERN_WARNING "afd: write_dev_pchs - cannot enter VSC mode, aborting.\n");
        return (1);
    }

    rc = send_longvsc_cmd(0x000c, 0x0002, (track & 0xffff), (track >> 16) & 0xffff, head, sector, scount);
    if (rc != 0) {
        printk(KERN_WARNING "afd: write_dev_pchs - send ATA command fail, aborting.\n");
        return(1);
    }
    read_regs();
    if (drq) {
        printk(KERN_WARNING "afd: write_dev_pchs - DRQ still ON, aborting.\n");
        return(1);
    }

    sectorslow = inb(p4);
    sectorshigh = inb(p5);
    len = sectorslow + (sectorshigh << 8);

    if (len < 1) return(1);

    sectorswritten = 0;

    while (len > sectorswritten) {
        if (dev_pre_xfer_cmd(1)) {
            printk(KERN_WARNING "afd: write_dev_pchs - write prepare command failed, aborting.\n");
            return(1);
        }
        read_regs();
        while (drq) {
            if (memcpy(a,buffer+(sectorswritten*512),512)) {
                write_buffer(a);
            } else {
                printk(KERN_WARNING "afd: write_dev_pchs - error reading input buffer, aborting.\n");
            }
            sectorswritten++;

            rc = waitready(10);
            if (rc < 0)  {   
                printk(KERN_WARNING "afd: write_dev_pchs - drive not ready, aborting.\n");
                return(1);
            }
            read_regs();
            if (err)  {
                printk(KERN_WARNING "afd: write_dev_pchs - error status was set while writing.\n");
                return(1);
            }
        }
    }

    if (sectorswritten != len) {   
        printk(KERN_WARNING "afd: write_dev_pchs - written buffer smaller than original buffer.\n");
        return(1);
    }

    getnstimeofday(&timest);
    printk(KERN_WARNING "afd: finishing WRITE at %d.%lu\n", timest.tv_sec, timest.tv_nsec);

    return(0);
}

static int send_longvsc_cmd(short command, short par1, short par2, short par3, short par4, short par5, short par6)
{
    char a[phy_block_size];
    int rc;

    memset(a, 0, phy_block_size);

    a[1]=(command>>8) & 0xff ;
    a[0]=(command & 0x00ff);

    a[3]=(par1>>8) & 0xff;
    a[2]=(par1 & 0x00ff);

    a[5]=(par2>>8) & 0xff;
    a[4]=(par2 & 0x00ff);

    a[7]=(par3>>8) & 0xff;
    a[6]=(par3 & 0x00ff);

    a[9]=(par4>>8) & 0xff;
    a[8]=(par4 & 0x00ff);

    a[11]=(par5>>8) & 0xff;
    a[10]=(par5 & 0x00ff);

    a[13]=(par6>>8) & 0xff;
    a[12]=(par6 & 0x00ff);


    outb(0xa0, p6);
    read_regs();

    if (busy) {
        printk(KERN_WARNING "afd: send_longvsc_cmd - drive is BSY, aborting.\n");
        return 1;
    }

    outb(0xd6,p1);	//Write SMART log  
    outb(0x01,p2);	//Sector count = 1
    outb(0xbe,p3);	//SMART log address, 0xB0-0xBF vendor specific
    outb(0x4f,p4);	//Always 0x4F (ATA std.)
    outb(0xc2,p5);	//Always 0xC2 (ATA std.)
    outb(0xa0,p6);	//Select master
    outb(0xb0,p7);	//SMART command

    read_regs();

    rc = waitnobusy(60);
    if (rc) {
        printk(KERN_WARNING "afd: send_longvsc_cmd - drive is BSY [waitnobusy(60)], aborting.\n");
        return(1);
    }
   
    read_regs();
    if (!drq) {
        printk(KERN_WARNING "afd: send_longvsc_cmd - DRQ: (%d), aborting.\n", drq);
        return(1);
    }

    write_buffer(a);

    rc = waitnobusy(5);
    if (rc) {
        printk(KERN_WARNING "afd: send_longvsc_cmd - drive is BSY [waitnobusy(5)=%d], aborting.\n", rc);
        return(1);
    }

    read_regs();
    if (err) {           
        printk(KERN_WARNING "afd: send_longvsc_cmd - Error register was set while sending the command.\n");
        return(1);
    }

    return(0);
}

/*
 *    Read ATA STATUS register.
 */
static void read_regs(void) {
    unsigned char s;
    s = inb(p7);
    regs = s;
   
    busy = ATA_SR_BSY == (s & ATA_SR_BSY);
    drdy = ATA_SR_DRDY == (s & ATA_SR_DRDY);         //drive ready
    df = ATA_SR_DF == (s & ATA_SR_DF);
    dsc = ATA_SR_DSC == (s & ATA_SR_DSC);            // drive seek complete
    drq = ATA_SR_DRQ == (s & ATA_SR_DRQ);
    corr = ATA_SR_CORR == (s & ATA_SR_CORR);
    idx = ATA_SR_IDX == (s & ATA_SR_IDX);
    err = ATA_SR_ERR == (s & ATA_SR_ERR);

    ready = drsc = drdy & dsc;   
}

/*
 *    READ SMART LOG Command - prepare for data transfer (R/W)
 */
static int dev_pre_xfer_cmd(unsigned char length) {
    int rc = 0;
    outb(0xa0, p6);    // Select master

    rc = waitnobusy(3);
    if (rc)    {   
        printk(KERN_WARNING "afd: dev_pre_xfer_cmd - drive is BSY, aborting.\n");
        return 1;
    }
   
    outb(0xd5,p1);
    outb(length,p2);
    outb(0xbf,p3);
    outb(0x4f,p4);
    outb(0xc2,p5);
    outb(0xa0,p6);
    outb(0xb0,p7);

    rc = waitnobusy(60);
    if (rc) {
        printk(KERN_WARNING "afd: dev_pre_xfer_cmd - drive is BSY after I/O waiting, aborting.\n");
        return(1);
    }

    if (0 != waitdrq(3)) {
        printk(KERN_WARNING "afd: dev_pre_xfer_cmd - drive didn't set the DRQ flag, aborting.\n");
        return(1);
    }

    return(0);
}

/*
 * Get drive's configuration page
 */
static int dev_get_cp(short cp, char ** out_buff, int * len) {
    char buff[phy_block_size];
    char * new_buff;
    unsigned char i;
    int rc = 0;

    read_regs();
    outb(0xa0, p6);

    read_regs();
    if (busy) {
        printk(KERN_WARNING "afd: dev_get_cp - drive is BSY, aborting.\n");
        return(1);   
    }
   
    if (vsc_mode_on()) {
        printk(KERN_WARNING "afd: dev_get_cp - setting VCS mode on failed, aborting.\n");
        return(1);
    }

    rc = send_vsc_cmd(0x000d, cp, 0x0000);
    if (rc) {
        printk(KERN_WARNING "afd: dev_get_cp - send_vsc_cmd failed, aborting.\n");
        return(1);
    }

    read_regs();
    if (drq) {
        printk(KERN_WARNING "afd: dev_get_cp - DRQ flag is still on, aborting.\n");
        return(1);
    }   

    (* len) = inb(p4);                             // Read length
    new_buff = vmalloc((*len) * phy_block_size);   // Allocate for reading page

    rc = dev_pre_xfer_cmd((*len));
    if (rc) {
        printk(KERN_WARNING "afd: dev_get_cp - dev_pre_xfer_cmd failed, aborting.\n");
        return(1);
    }

    for (i=0; i<(*len); i++) {
        if (0 == waitdrq(3)) {
            read_buffer(buff);
            memcpy(new_buff + (i * phy_block_size), buff, phy_block_size);
            waitnobusy(3);
        }
    }
    (*out_buff) = new_buff;

        printk (KERN_NOTICE "afd: CP Length: %d, CP 0x%hd: \n", *len, cp);
        int c;
        for (c=0; c < *len*512; c++) {
            unsigned char l = new_buff[c];
            printk ("0x%02x ", l);
            if ((c % 16) == 15) {
                printk ("\n");
            }
        }
        printk ("\n");

    return(0);
}

/*
 * VSC mode ON
 */
static int vsc_mode_on(void) {
    int rc;
    outb(0xa0, p6);    // Select master

    rc = waitnobusy(3);
    if (rc) {
        printk(KERN_WARNING "afd: vsc_mode_on - drive is busy, aborting.\n");
        return(1);
    }

    outb(0x45,p1);
    outb(0x00,p2);
    outb(0x00,p3);
    outb(0x44,p4);
    outb(0x57,p5);
    outb(0xA0,p6);
    outb(0x80,p7);

    rc = waitnobusy(10);
    if (rc) {
        printk(KERN_WARNING "afd: vsc_mode_on - drive is busy after 10 seconds, aborting.\n");
        return(1);
    }

    if(waitnodrq(3)) {
        printk(KERN_WARNING "afd: vsc_mode_on - drive didn't clear the DRQ flag, aborting.\n");
        return(1);
    }

    return(0);
   
}

/*
 * VSC mode OFF
 */
static int vsc_mode_off(void) {
    int rc;
    outb(0xa0, p6);    // Select master

    rc = waitnobusy(3);
    if (rc) {
        printk(KERN_WARNING "afd: vsc_mode_off - drive is busy, aborting.\n");
        return(1);
    }

    outb(0x44,p1);
    outb(0x00,p2);
    outb(0x00,p3);
    outb(0x44,p4);
    outb(0x57,p5);
    outb(0xA0,p6);
    outb(0x80,p7);

    rc = waitnobusy(10);
    if (rc) {
        printk(KERN_WARNING "afd: vsc_mode_off - drive is busy after 10 seconds, aborting.\n");
        return(1);
    }

    read_regs();
    if (drq) {
        printk(KERN_WARNING "afd: vsc_mode_off - drive didn0t clear the DRQ flag, aborting.\n");
        return(1);
    }
    return(0);
}

int send_vsc_cmd(short command, short par1, short par2) {

    char a[512];
    int rc;

    memset(a, 0, 512);

    a[1] = (char)(command>>8) & 0xff ;
    a[0] = (char)(command & 0xff);

    a[3] = (char)(par1>>8) & 0xff;
    a[2] = (char)(par1 & 0xff);

    a[5] = (char)(par2>>8) & 0xff;
    a[4] = (char)(par2 & 0xff);

    printk(KERN_WARNING "afd: VSC=");
    int c;
    for (c=0; c < 8; c++) {
        unsigned char l = a[c];
        printk ("0x%02x ", l);
        if ((c % 16) == 15) {
            printk ("\n");
        }
    }

    // select master
    outb(0xa0, p6);

    rc = waitnobusy(3);
    if (rc) {
        printk(KERN_WARNING "afd: dev_send_command - drive busy, aborting.\n");
        return 1;
    }

    outb(0xd6, p1);
    outb(0x01, p2);
    outb(0xbe, p3);
    outb(0x4f, p4);
    outb(0xc2, p5);
    outb(0xa0, p6);
    outb(0xb0, p7);

    rc = waitnobusy(3);
    if (rc) {

        printk(KERN_WARNING "afd: dev_send_command - drive busy, aborting.\n");
        return(1);
    }

    read_regs();
    if (!drq) {
        printk(KERN_WARNING "afd: dev_send_command - DRQ: %d, aborting.\n", drq);
        return(1);
    }

    write_buffer(a);

    rc = waitnobusy(10);
    if (rc) {
        printk(KERN_WARNING "afd: dev_send_command - drive busy: %d, aborting.\n", rc);
        return(1);
    }

    read_regs();
    if (err) {
        printk(KERN_WARNING "afd: dev_send_command - finished with errors.\n");   
        return(1);
    }

    return(0);
}

/*
 * Service Area
 */
static int get_saspt(char * cp5, int royl) {
    int offset = 0;
    short spt = 0;

    if (royl) {
        offset = 0x6c;
    } else {
        offset = 0x28;
    }

    memcpy(&spt, cp5 + offset, 2);

    return(spt);
}


static int get_sacyl(char * cp1) {
    int offset = 0x24;
    short cyl = 0;

    memcpy(&cyl, cp1 + offset, 2);

    return(cyl);
}

static int get_vheads(char* cp1) {
    int offset = 0x1E;
    short vh = 0;

    memcpy(&vh, cp1 + offset, 1);

    return(vh);
}

static int get_headmask(char* cp1) {
    int offset = 0x1F;
    short hm = 0;

    memcpy(&hm, cp1 + offset, 1);

    return(hm);
}

static int set_logical_heads(int headmask) {
    int curr, skipped, i;
    int* _lheads_x;
    curr = 0;
    skipped = 0;
    for (i=0; i<8; i++) {
        int h = 1 << i;
        if (headmask & h) {
            if (skipped++ >= 2) {
                switch (curr) {
                    case 0:
                        lheads.h0 = i;
                        break;
                    case 1:
                        lheads.h1 = i;
                        break;
                    case 2:
                        lheads.h2 = i;
                        break;
                    case 3:
                        lheads.h3 = i;
                        break;
                    case 4:
                        lheads.h4 = i;
                        break;
                    case 5:
                        lheads.h5 = i;
                        break;
                    case 6:
                        lheads.h6 = i;
                        break;
                    default:
                        break;
                }
                curr += 1;
            }
        }
    }
    return 0;
}

/*
 * Timings...
 */
static int waitdrq(int secs) {

    int wait_time = 500;
    int retries = secs * 1000000/(wait_time);

    read_regs();
    while ((!drq) && (retries >= 0)) {
        usleep (wait_time);
        retries--;
        read_regs();
    }   
    if (retries>0)
        return (0);
    else
        return(1);
   
}

static int waitnodrq(int secs) {

    int wait_time = 500;
    int retries = secs * 1000000 / (wait_time);

    read_regs();
    while ((drq) && (retries>=0)) {
        usleep (wait_time);
        retries--;
        read_regs();
    }   

    if (retries>0)
        return (0);
    else
        return(1);
}

static int waitready(int secs) {
   
    int wait_time = 500;
    int retries=secs * 1000000/(wait_time);

    read_regs();
    while ( (!ready) && (retries>=0)) {
        usleep (wait_time);
        retries--;
        read_regs();
    }   
   
    if (retries>0)
        return (0);
    else
        return(1);
   
}

int waitnobusy(int secs) {

    int wait_time = 500;
    int retries = secs*1000000/(wait_time);

    read_regs();
    while ((busy) && (retries>=0)) {
        usleep (wait_time);
        retries--;
        read_regs();
    }   
   
    if ((retries==0) && busy)
        return (1);
    else
        return(0);
   
}

/*
 * Drive ID
 */
static int get_dev_id (struct dev_id *d) {

    read_regs();
    printk(KERN_WARNING "afd: get_drive_id - STATUS BEFORE: BSY=%d DRD=%d DSC=%d.\n", busy, drdy, dsc);

    outb(0xa0, p6);    // Select master
    outb(0xec, p7); // Get ID ATA command

    if (waitdrq(10)) {
        printk(KERN_WARNING "afd: get_drive_id - drive not ready, aborting.\n");
    }

    // read buffer
    char buff[512];
    memset(buff, 0, 512);
    read_buffer (buff);

    memcpy(d, buff, sizeof(struct dev_id));

    return(0);   
}

/* Get the family code. Returns the size of the code, or 0 if not found */
static int get_dev_family_code(char* model, char* family_code) {
    char* hyphen;
    char* end;
    hyphen = strchr(model, '-');
    if (hyphen != NULL) {
        end = strchr(hyphen, ' ');
        if (end != NULL) {
		size_t fullfam_len = end - hyphen;
            	if (fullfam_len == 7) {
		   memcpy(family_code, hyphen+3, 2);
		   return 2;
		} else if (fullfam_len == 8) {
		   memcpy(family_code, hyphen+3, 3);
		   return 3;
		} else {
		    printk(KERN_WARNING "afd: Family unknown. Length = %d.\n", fullfam_len);
		}
        }
    }
    return 0;
}

/*****************************************
 * Return 1 if compatible                *
 * NOT IMPLEMENTED !!!                   *
 *                                       */
static int is_compatible(char* family_code, int* royl) {
    *royl = 0; //Manually set to NOT ROYL. Change for other models until implemented.
    return 1;
}

/*
 * Write buffer to I/O port
 */
static void write_buffer (char* sector) {
    outsw(p0, sector, 256);
}

/*
 * Read buffer from I/O port
 */
static void read_buffer (char* sector) {
    insw(p0, sector, 256);
}

void flip (char* buf, int len) {
    int i=0;
    for (i=0; i<len-1; i+=2) {
        char k;
        k = buf[i];
        buf[i] = buf[i+1];
        buf[i+1] = k;
    }
}

static void print_status(char * msg) {
    printk(KERN_NOTICE "afd: %s - DRIVE STATUS: BSY=%d DRD=%d DSC=%d ERR=%d INF=%d.\n", msg, busy, drdy, dsc, err, idnf);
}

static void usleep (int millis) {
    int i=0;
    for (i=0; i<millis; i++) outb(0x00, 0x80);
}

/*
 * Register module actions
 */
module_init(afd_init);
module_exit(afd_exit);
