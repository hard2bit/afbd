/*
 * An antiforensics block device driver for Western Digital (Marvell) hard drives
 *
 *	PCI SATA device address: 01.f5
 * 	I/O ports at b080 [size=8] <---
 *	I/O ports at b000 [size=4]
 *	I/O ports at ac00 [size=8] <---
 *
 *	COMPILE:	make -C /lib/modules/`uname -r`/build M=`pwd` modules
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
 * (C) 2013 Ariel Berkman <ariel@recover.co.il>
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
#include <linux/fs.h>     /* everything... */
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

static int logical_block_size = 512;
module_param(logical_block_size, int, 0);

static unsigned char regs = 0;
static unsigned int busy=0, drdy=0, df=0, dsc=0, drq=0, corr=0, idx=0, err=0, ready=0, drsc=0;    // Status register bits
static unsigned int bbk=0, unc=0, mc=0, idnf=0, mcr=0, abrt=0, tk0nf=0, amnf=0;                // Error register bits
static int p0=0, p1=0, p2=0, p3=0, p4=0, p5=0, p6=0, p7=0;                                        // I/O port address

static int baseport = 0xb080;	// Obtained through lspci -v, lspci -D and ls -l /sys/bus/pci/devices/
				// 0000\:00\:1f.5/host4/target4\:0\:0/4\:0\:0\:0/block/, for the PoC.
static int sa_spt = 0;            // Sectors per track in SA zone
static int sa_tracks = 0;        // Tracks per head corresponding to SA zone
static int num_of_heads = 0;    // Number of heads in device
static int nsectors = -1;        // Device size in sectors

module_param(nsectors, int, 0);


/*********************************
 *   DRIVER MODULE STRUCTURES    *
 *********************************/

 // PCHS block for translation
static struct pchs {
    int c;
    short h;
    short s;
};
 
// Drive ID
static struct ide_id {
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
    short ob5[6]; // +1
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

// Drive's zone table header
static struct zone_header {
    short u1;
    short zones;
    char u2[0x10];
};

// Drive's zone records
static struct zone_rec {
    int start_cyl;
    int end_cyl;
    int start_sec;
    char pad[2];
    int end_sec;
    char pad2[2];
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


/*********************************
 *       FUNCTION HEADERS        *
 *********************************/
 
static void afd_transfer(struct afd_device *dev, sector_t sector,                // Handles an I/O transfer.
    unsigned long nsect, char *buffer, int write);
static void afd_request(struct request_queue *q);                                // Handles an I/O request.
int afd_getgeo(struct block_device * block_device, struct hd_geometry * geo);    // Need to implement in order to use fdisk and the like.
static int __init afd_init(void);                                                // Initialze drive parameters.
static void __exit afd_exit(void);                                                // Free resources.
static void read_regs();                                                        // Read drive's status register.
static void status(int times);                                                    // Print drive status n times.
static int waitready(int secs);                                                    // Wait for device setting readiness status.
static int waitnobusy(int secs);                                                // Wait for device clearing busy status.
static int waitdrq(int secs);                                                    // Wait for device setting data request status.
static int waitnodrq(int secs);                                                    // Wait for device clearing data request status.
static int vsc_mode_on();                                                        // Prepare the device to accept vendor specific commands.
static int vsc_mode_off();                                                        // End VSCE mode.
static void write_buffer (char * sector);                                        // Write 512 bytes buffer (256w) to the device.
static void read_buffer (char * sector);                                            // Read 512 bytes (256w) into char buffer.
static int get_sa_spt(char * buf);                                                // Read Service Area's zone Sector Per Track integer.
static int get_sa_tracks(char * buf, int size);                                    // Read Service Area's track count.
static int get_dev_id(struct ide_id * d);                                        // Read ATA Device ID
static int read_dev_pchs(char * buffer, short head, int track,                    // Read device physical sectors in CHS format into char buffer.
    short sector, short scount);
static int write_dev_pchs(char * buffer, short head, int track,                    // Write char buffer into drive using physical CHS format.
    short sector, short scount);
static sector_t xlate_pchs(struct pchs chs);                                            // Translate a PCHS sector into LBA equivalent.
static struct pchs xlate_pba(sector_t pba);                                            // Translate an LBA sector into its CHS coordinates.
static int write_block(char * buffer, sector_t pba, unsigned long scount);        // Write data block to device.
static int read_block(char * buffer, sector_t pba, unsigned long scount);        // Read block
static int send_lba48_cmd(short command, short p1, short p2,                    // Send ATA command to the device.
    short p3, short p4, short p5, short p6);
static int dev_rw_buffer_cmd(unsigned char length);                                // Set buffer length to operate with through the ATA port.
static int dev_send_cmd(short command, short para1, short para2);                // Send command
static int dev_get_cp(short cp, char ** out_buff, int * len);                    // Read device configuration page
static void flip (char * buf, int len);                                            // Flip every two bytes in the chain.
static void usleep(int millis);													// We need our own implementation of usleep. Single writing operations to port 0x80 should take about 1 ms.
static void print_status(char * msg);

/*********************************
 *   FUNCTION IMPLEMENTATIONS    *
 *********************************/

/*
 * Handle an I/O request.
 */
static void afd_transfer(struct afd_device *dev, sector_t sector,
        unsigned long nsect, char *buffer, int write) {
    unsigned long offset = sector * logical_block_size;
    unsigned long nbytes = nsect * logical_block_size;

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
    size = Device.size * (logical_block_size / KERNEL_SECTOR_SIZE);
    geo->cylinders = sa_tracks - 1;
    geo->heads = num_of_heads;
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

    struct ide_id id;
    get_dev_id(&id);
    char model[64];
    memset(model, 0, 64);
    memcpy(model, id.model, 40);
    flip(model, 40);
    printk (KERN_NOTICE "afd: Detected device: %s\n", model);
    memcpy(Device.model, model, 40);
   
    char * out_buff;
    int len;
    if (dev_get_cp(0x05, &out_buff, &len) == 0) {
        sa_spt = get_sa_spt(out_buff);
        sa_tracks = get_sa_tracks(out_buff, len * logical_block_size);
        num_of_heads = 4;    // constant for now.

        printk (KERN_NOTICE "afd: SA SPT: (%d); SA tracks: (%d); Usable heads: (%d); Unused reversed space: %d sectors [%d bytes]\n", sa_spt, sa_tracks, num_of_heads, sa_tracks * sa_spt * (num_of_heads), sa_tracks * sa_spt * (num_of_heads) * logical_block_size);
    }
    nsectors = (sa_tracks - 1) * sa_spt * (num_of_heads);    // Device reserved area usable space in sectors
    Device.size = nsectors * logical_block_size;        // Device reserved area usable space in bytes
   
    spin_lock_init(&Device.lock);
    /*
     * Get a request queue.
     */
    Queue = blk_init_queue(afd_request, &Device.lock);
    if (Queue == NULL)
        goto out;
    blk_queue_logical_block_size(Queue, logical_block_size);
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
    sector_t pba = ((chs.c * num_of_heads) + chs.h) * sa_spt + chs.s + 1;
    return pba;
}

static struct pchs xlate_pba(sector_t _pba) {
    struct pchs chs;
    int pba = (int)(_pba);
    chs.c = -1 - (pba / (sa_spt * num_of_heads));
    chs.h = (short)((((pba / sa_spt) % num_of_heads) + 2));
    chs.s = (short)(((pba % sa_spt) + 1));
    //printk(KERN_NOTICE "afd: PBA=%d, CHS=%d,%d,%d.\n", pba, chs.c, chs.h, chs.s);
    return chs;
}

/****************************************************
 *    Read data block from the device - PBA function.    *
 ****************************************************/
static int read_block(char * buffer, sector_t pba, unsigned long scount) {
    char * sector;
    sector = vmalloc(logical_block_size);
    struct pchs _chs;
    int sc = 0;
    unsigned int buff_position = 0;
    for (sc=0; sc<scount; sc++) {
        _chs = xlate_pba(pba);
	int _cylinder = _chs.c;
	short _head = _chs.h;
	short _sector = _chs.s;
        if (0 == read_dev_pchs(sector, _head, _cylinder, _sector, 1)) {
	    //printk(KERN_WARNING "afd: read_block OK at sector %d (block %d), CHS=%d,%d,%d.\n", pba, sc, _cylinder, _head, _sector);
	} else {
            printk(KERN_WARNING "afd: read_block FAILED at sector %d (block %d), CHS=%d,%d,%d.\n", pba, sc, _cylinder, _head, _sector);
            vfree(sector);
            return 1;
        }
        memcpy(buffer + buff_position, sector, logical_block_size);
        buff_position += logical_block_size;
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
    char a[logical_block_size];
    int len = 0;
    int rc = 0;

    //read_regs();
    //printk(KERN_WARNING "afd: read_dev_pchs - about to read: C=%d, H=%d, S=%d, count=%d.\n", track, head, sector, scount);
    //print_status("Before selecting master");

    outb(0xa0, p6);    // Select master

    read_regs();
    print_status("After selecting master");

    if (waitready(3)) {
        printk(KERN_WARNING "afd: read_dev_pchs - Drive not ready, aborting.\n");
        return(1);
    }
   
    if (vsc_mode_on()) {   
        printk(KERN_WARNING "afd: read_dev_pchs - Failed to start VSC mode, aborting.\n");
        return (1);
    }

    rc = send_lba48_cmd(0x000c, 0x0001, (track & 0xffff), (track >> 16) & 0xffff, head, sector, scount);
    if (rc) {
        printk(KERN_WARNING "afd: read_dev_pchs - send ATA command fail, aborting.\n");
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
        printk(KERN_WARNING "afd: read_dev_pchs - Length less than 1, aborting.\n");
        return(1);
    }

    sectorsread = 0;

    while (len > sectorsread) {
        rc = dev_rw_buffer_cmd(1);
        if (rc) {
            printk(KERN_WARNING "afd: read_dev_pchs - dev_rw_buffer_cmd failed, aborting.\n");
            return(1);
        }

        read_regs();
        while (drq) {
            memset(a, 0, logical_block_size);
            read_buffer(a);
            memcpy(buffer + (sectorsread * logical_block_size), a, logical_block_size);
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

    return(0);
}

/****************************************************
 *    Write data block to the device - PBA function.    *
 ****************************************************/
static int write_block(char * buffer, sector_t pba, unsigned long scount) {
    char * sector;
    sector = vmalloc(logical_block_size);
    struct pchs chs;
    int sc = 0;
    for (sc=0; sc<scount; sc++) {
        memcpy(sector, buffer, logical_block_size);
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
    char a[logical_block_size];
    int len;
    int rc;

    outb(0xa0, p6);

    if (waitready(3)) {
        printk(KERN_WARNING "afd: write_dev_pchs - drive not ready, aborting.\n");
        return(1);
    }
   
    if (vsc_mode_on()) {   
        printk(KERN_WARNING "afd: write_dev_pchs - cannot enter VSC mode, aborting.\n");
        return (1);
    } else {
        //printk(KERN_NOTICE "afd: write_dev_pchs - VSC mode ON.\n");
    }

    rc = send_lba48_cmd(0x000c, 0x0002, (track & 0xffff), (track >> 16) & 0xffff, head, sector, scount);
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
        if (dev_rw_buffer_cmd(1)) {
            printk(KERN_WARNING "afd: write_dev_pchs - write buffer command failed, aborting.\n");
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

    return(0);
}

static int send_lba48_cmd(short command, short par1, short par2, short par3, short par4, short par5, short par6)
{
    char a[logical_block_size];
    int rc;

    //read_regs();
    //print_status("About to send full command");

    memset(a, 0, logical_block_size);

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
    //print_status("Intention to send command notified.");

    if (busy) {
        printk(KERN_WARNING "afd: send_lba48_cmd - drive is BSY, aborting.\n");
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
    //print_status("Command sent.");

    rc = waitnobusy(60);
    if (rc) {
        printk(KERN_WARNING "afd: send_lba48_cmd - drive is BSY [waitnobusy(60)], aborting.\n");
        return(1);
    }
   
    read_regs();
    if (!drq) {
        printk(KERN_WARNING "afd: send_lba48_cmd - DRQ: (%d), aborting.\n", drq);
        return(1);
    }

    write_buffer(a);

    rc = waitnobusy(5);
    if (rc) {
        printk(KERN_WARNING "afd: send_lba48_cmd - drive is BSY [waitnobusy(5)=%d], aborting.\n", rc);
        return(1);
    }

    read_regs();
    //print_status("Finished sending command...");
    if (err) {           
        printk(KERN_WARNING "afd: send_lba48_cmd - Error register was set while sending the command.\n");
        return(1);
    }

    return(0);
}

/*
 *    Read ATA registers.
 */
static void read_regs() {
    unsigned char s;
    s = inb(p7);
    regs = s;
   
    busy = ATA_SR_BSY == (s & ATA_SR_BSY);
    drdy = ATA_SR_DRDY == (s & ATA_SR_DRDY);        //drive ready
    df = ATA_SR_DF == (s & ATA_SR_DF);
    dsc = ATA_SR_DSC == (s & ATA_SR_DSC);            // drive seek complete
    drq = ATA_SR_DRQ == (s & ATA_SR_DRQ);
    corr = ATA_SR_CORR == (s & ATA_SR_CORR);
    idx = ATA_SR_IDX == (s & ATA_SR_IDX);
    err = ATA_SR_ERR == (s & ATA_SR_ERR);

    ready = drsc = drdy & dsc;   
}

/*
 *    RW buffer ATA command
 */
static int dev_rw_buffer_cmd(unsigned char length) {
    int rc = 0;
    outb(0xa0, p6);    // Select master

    rc = waitnobusy(3);
    if (rc)    {   
        printk(KERN_WARNING "afd: dev_rw_buffer_cmd - drive is BSY, aborting.\n");
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
        printk(KERN_WARNING "afd: dev_rw_buffer_cmd - drive is BSY after I/O waiting, aborting.\n");
        return(1);
    }

    if (0 != waitdrq(3)) {
        printk(KERN_WARNING "afd: dev_rw_buffer_cmd - drive didn't set the DRQ flag, aborting.\n");
        return(1);
    }

    return(0);
}

/*
 * Get drive's configuration page
 */
static int dev_get_cp(short cp, char ** out_buff, int * len) {
    char buff[logical_block_size];
    char * new_buff;
    unsigned char i;
    int rc = 0;

    read_regs();
    printk(KERN_WARNING "afd: dev_get_cp - STATUS BEFORE: BSY=%d DRD=%d DSC=%d.\n", busy, drdy, dsc);

    // choose primary port
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

    rc = dev_send_cmd(0x000d, cp, 0x0000);
    if (rc) {
        printk(KERN_WARNING "afd: dev_get_cp - dev_send_cmd failed, aborting.\n");
        return(1);
    }

    read_regs();
    if (drq) {
        printk(KERN_WARNING "afd: dev_get_cp - DRQ flag is still on, aborting.\n");
        return(1);
    }   

    (* len) = inb(p4);    // Read length

    new_buff = vmalloc((*len) * logical_block_size);

    rc = dev_rw_buffer_cmd((*len));
    if (rc) {
        printk(KERN_WARNING "afd: dev_get_cp - dev_rw_buffer_cmd failed, aborting.\n");
        return(1);
    }

    for (i=0; i<(*len); i++) {
        if (0 == waitdrq(3)) {
            read_buffer(buff);
            memcpy(new_buff + (i * logical_block_size), buff, logical_block_size);
            waitnobusy(3);
        }
    }
    (*out_buff) = new_buff;
    return(0);
}

/*
 * VSC mode ON
 */
static int vsc_mode_on() {
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
static int vsc_mode_off() {
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

int dev_send_cmd(short command, short par1, short par2) {

    char a[512];
    int rc;

    memset(a, 0, 512);

    a[1] = (command>>8) & 0xff ;
    a[0] = (command & 0x00ff);

    a[3] = (par1>>8) & 0xff;
    a[2] = (par1 & 0x00ff);

    a[5] = (par2>>8) & 0xff;
    a[4] = (par2 & 0x00ff);

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
static int get_sa_spt(char * buff) {
    int pos = 0;
    short spt;

    pos += sizeof(struct zone_header);
    pos += sizeof(struct zone_rec);

    memcpy(&spt, buff + pos, 2);

    return(spt);
}


static int get_sa_tracks(char * buff, int size) {
    struct zone_rec rec1;
    if ( (sizeof(struct zone_header) + sizeof(struct zone_rec)) < size ) {
        memcpy(&rec1, buff + sizeof(struct zone_header), sizeof(struct zone_rec));
        return(abs(rec1.start_cyl));
    } else {
        return(0);
    }
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
static int get_dev_id (struct ide_id *d) {

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

    memcpy(d, buff, sizeof(struct ide_id));

    return(0);   
}

/*
 * Write buffer to I/O port
 */
static void write_buffer (char * sector) {
    outsw(p0, sector, 256);
}

/*
 * Read buffer from I/O port
 */
static void read_buffer (char * sector) {
    insw(p0, sector, 256);
}

void flip (char * buf, int len) {
    int i=0;
    for (i=0; i<len-1; i+=2) {
        char k;
        k = buf[i];
        buf[i] = buf[i+1];
        buf[i+1] = k;
    }
}

static void print_status(char * msg) {
	//printk(KERN_NOTICE "afd: %s - DRIVE STATUS: BSY=%d DRD=%d DSC=%d ERR=%d INF=%d.\n", msg, busy, drdy, dsc, err, idnf);
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
