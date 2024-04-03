/*
 * (C) Copyright 2024 Jiyuan Zhang
 *
 * Author: Jiyuan Zhang <jiyuanz3@illinois.edu>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; version 2
 * of the License.
 *
 * Usage:
 *     echo [mode]<pid_dec>[,start_addr_hex,stop_addr_hex] > /proc/ptdump
 *     cat /proc/ptdump
 *
 * Mode:
 *     'P': Dump all available addresses. This is the default mode if no mode is specified
 *     'V': Virtual machine mode (Dump EPT of given KVM-based hypervisor PID)
 *     'U': User psudo-mode (Shortcut to specify user address range, overridden by start and stop address)
 *     'K': Kernel psudo-mode (Shortcut to specify kernel address range, overridden by start and stop address)
 *
 * Example Input:
 *     "1": Dump all page tables of PID 1
 *     "P1": Dump all page tables of PID 1
 *     "V1": Dump VM EPT managed by hypervisor PID 1
 *     "U1": Dump user space page tables of PID 1
 *     "K1": Dump kernel space page tables of PID 1
 *     "P1,1234abc,4321efg": Dump page tables of PID 1 in range [0x1234abc,0x4321efg)
 *     "U1,1234abc,4321efg": Dump page tables of PID 1 in range [0x1234abc,0x4321efg)
 *     "V1,1234abc,4321efg": Dump EPT tables of VM PID 1 in range [0x1234abc,0x4321efg)
 */

#include <linux/proc_fs.h>
#include <linux/mm.h>
#include <linux/module.h>
#include <linux/seq_file.h>
#include <linux/sort.h>
#include <linux/slab.h>
#include <linux/sched.h>
#include <linux/sched/mm.h>
#include <linux/security.h>
#include <linux/kvm_host.h>
#include <linux/ptrace.h>
#include <linux/kprobes.h>

#include <asm/pgtable.h>
#include <asm/pgtable_64.h>

//
// Globals
//

enum {
	NORMAL_MODE = 'P',
	VMROOT_MODE = 'V',
	USER_PSUDOMODE = 'U',
	KERNEL_PSUDOMODE = 'K',
};

#define is_normal_mode() (state.global.mode == NORMAL_MODE)
#define is_vmroot_mode() (state.global.mode == VMROOT_MODE)
#define is_user_psudomode() (state.global.mode == USER_PSUDOMODE)
#define is_kernel_psudomode() (state.global.mode == KERNEL_PSUDOMODE)

// From arch/x86/kvm/mmu.h
#define PT64_ROOT_5LEVEL 5
#define PT64_ROOT_4LEVEL 4
#define PT32_ROOT_LEVEL 2
#define PT32E_ROOT_LEVEL 3

static struct {
	struct {
		ulong user_lo;
		ulong user_hi;
		pid_t pid;
		char mode;
	} global;

	struct {
		ulong root_hpa;
		pid_t active_vm;
		int table_type;
		int maxphys;
		bool direct_map;
	} vmroot;
} state = {
	.global = {
		.user_lo = 0,
		.user_hi = -1UL,
		.pid = 1,
		.mode = NORMAL_MODE,
	},
	.vmroot = {
		.root_hpa = 0,
		.active_vm = 1,
		.table_type = PT64_ROOT_4LEVEL,
		.maxphys = 47,
		.direct_map = true,
	},
};

//
// Common Infra
//

enum {
	PGD_LVL,
	P4D_LVL,
	PUD_LVL,
	PMD_LVL,
	PTE_LVL,
};

static long unsigned int cr3_pfn(pgd_t *root)
{
	void *vcr3 = root;
	return __pa(vcr3) >> PAGE_SHIFT;
}

#define define_page_type_ops(type, upper) \
typedef struct page_##type##_ops { \
	bool (*none)(type##_t entry); \
	unsigned long (*pfn)(type##_t entry); \
	\
	bool (*bad)(type##_t entry); \
	bool (*leaf)(type##_t entry); \
	type##_t *(*offset)(upper##_t *ptr, unsigned long address); \
} page_##type##_ops;

define_page_type_ops(pgd, pgd);
define_page_type_ops(p4d, pgd);
define_page_type_ops(pud, p4d);
define_page_type_ops(pmd, pud);
define_page_type_ops(pte, pmd);

typedef struct page_table_ops {
	page_pgd_ops pgd;
	page_p4d_ops p4d;
	page_pud_ops pud;
	page_pmd_ops pmd;
	page_pte_ops pte;

	void (*unmap_pte_nullable)(pte_t *addr);
} page_table_ops;

// If we ever called pte_bad, this is the safenet
static bool pte_bad_not_implemented(pte_t val)
{
	WARN(1, "pte_bad should not be called\n");
	return false;
}

//
// Default Table Structure
//

#define forward_normal(ret, name, type) static ret normal_##name(type##_t val) { return name(val); }
#define forward_normal_offset(name, type, upper) static type##_t *normal_##name(upper##_t *ptr, unsigned long address) { return name(ptr, address); }

#define forward_normal_tree(ret, suffix) \
	forward_normal(ret, pgd_##suffix, pgd) \
	forward_normal(ret, p4d_##suffix, p4d) \
	forward_normal(ret, pud_##suffix, pud) \
	forward_normal(ret, pmd_##suffix, pmd)

#define forward_normal_all(ret, suffix) \
	forward_normal_tree(ret, suffix) \
	forward_normal(ret, pte_##suffix, pte)

forward_normal_all(bool, none)
forward_normal_all(unsigned long, pfn)

forward_normal_tree(bool, bad)
forward_normal_tree(bool, leaf)

forward_normal_offset(pgd_offset_pgd, pgd, pgd)
forward_normal_offset(p4d_offset, p4d, pgd)
forward_normal_offset(pud_offset, pud, p4d)
forward_normal_offset(pmd_offset, pmd, pud)
forward_normal_offset(pte_offset_map, pte, pmd)

static bool normal_pte_leaf(pte_t val) { return true; }
static void normal_unmap_pte(pte_t *val) { pte_unmap(val); }

static page_table_ops normal_ops = {
	.pgd = {
		.none = normal_pgd_none,
		.pfn = normal_pgd_pfn,
		.bad = normal_pgd_bad,
		.leaf = normal_pgd_leaf,
		.offset = normal_pgd_offset_pgd,
	},

	.p4d = {
		.none = normal_p4d_none,
		.pfn = normal_p4d_pfn,
		.bad = normal_p4d_bad,
		.leaf = normal_p4d_leaf,
		.offset = normal_p4d_offset,
	},

	.pud = {
		.none = normal_pud_none,
		.pfn = normal_pud_pfn,
		.bad = normal_pud_bad,
		.leaf = normal_pud_leaf,
		.offset = normal_pud_offset,
	},

	.pmd = {
		.none = normal_pmd_none,
		.pfn = normal_pmd_pfn,
		.bad = normal_pmd_bad,
		.leaf = normal_pmd_leaf,
		.offset = normal_pmd_offset,
	},

	.pte = {
		.none = normal_pte_none,
		.pfn = normal_pte_pfn,
		.bad = pte_bad_not_implemented,
		.leaf = normal_pte_leaf,
		.offset = normal_pte_offset_map,
	},

	.unmap_pte_nullable = normal_unmap_pte,
};

//
// VM EPT Table Structure
//

// Intel SDM Vol. 3C Pg. 28-12
// Figure 28-1. Formats of EPTP and EPT Paging-Structure Entries

#define EPT_PHYS_MAX ((1UL << state.vmroot.maxphys) - 1)
#define EPT_PFN_MASK (EPT_PHYS_MAX & (~((1 << 12) - 1)))

#define ept_functions(type, upper)										\
static bool ept_##type##_none(type##_t entry)							\
{																		\
	unsigned long val = entry.type;										\
	return (val & 0x7) == 0;											\
}																		\
																		\
static __maybe_unused bool ept_##type##_bad(type##_t entry)				\
{																		\
	return false;														\
}																		\
																		\
static unsigned long ept_##type##_pfn(type##_t entry)					\
{																		\
	unsigned long val = entry.type;										\
	return (val & EPT_PFN_MASK) >> 12;									\
}																		\
																		\
static __maybe_unused bool ept_##type##_leaf(type##_t entry)			\
{																		\
	unsigned long val = entry.type;										\
	return !!(val & 0x80);												\
}																		\
																		\
static __maybe_unused void* ept_##type##_page_vaddr(type##_t entry)		\
{																		\
	unsigned long val = entry.type;										\
	return __va(val & EPT_PFN_MASK);									\
}																		\
																		\
static __maybe_unused type##_t* ept_##type##_offset(upper##_t *entry, unsigned long address) \
{																		\
	return (((type##_t*) ept_##upper##_page_vaddr(*entry)) + type##_index(address)); \
}

ept_functions(pgd, pgd)
ept_functions(p4d, pgd)
ept_functions(pud, p4d)
ept_functions(pmd, pud)
ept_functions(pte, pmd)

static inline p4d_t *ept_p4d_offset_4or5(pgd_t *pgd, unsigned long address)
{
	if (state.vmroot.table_type != PT64_ROOT_5LEVEL)
		return (p4d_t *)pgd;

	return (p4d_t *)ept_pgd_page_vaddr(*pgd) + p4d_index(address);
}

static page_table_ops ept_ops = {
	.pgd = {
		.none = ept_pgd_none,
		.pfn = ept_pgd_pfn,
		.bad = ept_pgd_bad,
		.leaf = ept_pgd_leaf,
		.offset = ept_pgd_offset,
	},

	.p4d = {
		.none = ept_p4d_none,
		.pfn = ept_p4d_pfn,
		.bad = ept_p4d_bad,
		.leaf = ept_p4d_leaf,
		.offset = ept_p4d_offset_4or5,
	},

	.pud = {
		.none = ept_pud_none,
		.pfn = ept_pud_pfn,
		.bad = ept_pud_bad,
		.leaf = ept_pud_leaf,
		.offset = ept_pud_offset,
	},

	.pmd = {
		.none = ept_pmd_none,
		.pfn = ept_pmd_pfn,
		.bad = ept_pmd_bad,
		.leaf = ept_pmd_leaf,
		.offset = ept_pmd_offset,
	},

	.pte = {
		.none = ept_pte_none,
		.pfn = ept_pte_pfn,
		.bad = pte_bad_not_implemented,
		.leaf = ept_pte_leaf,
		.offset = ept_pte_offset,
	},

	.unmap_pte_nullable = NULL,
};

//
// Table Walker
//

static void print_entry(struct seq_file *s, ulong va, pgd_t *root, pgd_t *pgd, p4d_t *p4d, pud_t *pud, pmd_t *pmd, pte_t *pte, int level, page_table_ops *ops)
{
	ulong cr3a = 0, pgda = 0, p4da = 0, puda = 0, pmda = 0, ptea = 0;
	bool leaf = false;
	char *desc;

	cr3a = cr3_pfn(root);

	if (pgd && !leaf) {
		pgda = ops->pgd.pfn(*pgd);
		leaf = ops->pgd.leaf(*pgd);
	}
	if (p4d && !leaf) {
		p4da = ops->p4d.pfn(*p4d);
		leaf = ops->p4d.leaf(*p4d);
	}
	if (pud && !leaf) {
		puda = ops->pud.pfn(*pud);
		leaf = ops->pud.leaf(*pud);
	}
	if (pmd && !leaf) {
		pmda = ops->pmd.pfn(*pmd);
		leaf = ops->pmd.leaf(*pmd);
	}
	if (pte && !leaf) {
		ptea = ops->pte.pfn(*pte);
		leaf = ops->pte.leaf(*pte);
	}

	// Do not print unmapped pages
	if (!leaf)
		return;

	switch(level) {
		case PGD_LVL: desc = "PGD?"; break;
		case P4D_LVL: desc = "P4D?"; break;
		case PUD_LVL: desc = "1GPG"; break;
		case PMD_LVL: desc = "2MPG"; break;
		case PTE_LVL: desc = "4KPG"; break;
		default: desc = "BADP"; break;
	}

	seq_printf(s, "%016lx,%lx,%lx,%lx,%lx,%lx,%lx,%s\n", va, cr3a, pgda, p4da, puda, pmda, ptea, desc);
}

static void handle_leaf_page(struct seq_file *s, ulong va, pgd_t *root, pgd_t *pgd, p4d_t *p4d, pud_t *pud, pmd_t *pmd, pte_t *pte, int level, page_table_ops *ops)
{
	print_entry(s, va, root, pgd, p4d, pud, pmd, pte, level, ops);
}

static void table_walker(struct seq_file *s, unsigned long *paddr, pgd_t *root, page_table_ops *ops)
{
	unsigned long addr = *paddr;
	int gran = PGD_LVL;

	pgd_t *pgd = NULL;
	p4d_t *p4d = NULL;
	pud_t *pud = NULL;
	pmd_t *pmd = NULL;
	pte_t *pte = NULL;

	pgd = ops->pgd.offset(root, addr);

	if (pgd && !ops->pgd.none(*pgd)) {
		gran = P4D_LVL;

		if (ops->pgd.leaf(*pgd)) {
			handle_leaf_page(s, addr, root, pgd, p4d, pud, pmd, pte, PGD_LVL, ops);
			gran = PGD_LVL;
			goto done;
		}

		if (!ops->pgd.bad(*pgd))
			p4d = ops->p4d.offset(pgd, addr);
	}
	if (p4d && !ops->p4d.none(*p4d)) {
		gran = PUD_LVL;

		if (ops->p4d.leaf(*p4d)) {
			handle_leaf_page(s, addr, root, pgd, p4d, pud, pmd, pte, P4D_LVL, ops);
			gran = P4D_LVL;
			goto done;
		}

		if (!ops->p4d.bad(*p4d))
			pud = ops->pud.offset(p4d, addr);
	}
	if (pud && !ops->pud.none(*pud)) {
		gran = PMD_LVL;

		if (ops->pud.leaf(*pud)) {
			handle_leaf_page(s, addr, root, pgd, p4d, pud, pmd, pte, PUD_LVL, ops);
			gran = PUD_LVL;
			goto done;
		}

		if (!ops->pud.bad(*pud))
			pmd = ops->pmd.offset(pud, addr);
	}
	if (pmd && !ops->pmd.none(*pmd)) {
		gran = PTE_LVL;

		if (ops->pmd.leaf(*pmd)) {
			handle_leaf_page(s, addr, root, pgd, p4d, pud, pmd, pte, PMD_LVL, ops);
			gran = PMD_LVL;
			goto done;
		}

		if (!ops->pmd.bad(*pmd))
			pte = ops->pte.offset(pmd, addr);
	}
	if (pte && !ops->pte.none(*pte)) {
		gran = PTE_LVL;

		if (ops->pte.leaf(*pte))
			handle_leaf_page(s, addr, root, pgd, p4d, pud, pmd, pte, PTE_LVL, ops);

		if (ops->unmap_pte_nullable)
			ops->unmap_pte_nullable(pte);

		goto done;
	}

done:
	switch(gran) {
	default: WARN(1, "Invalid presence value\n"); fallthrough;
	case PGD_LVL: addr = ALIGN(addr + 1, PGDIR_SIZE); break;
	case P4D_LVL: addr = ALIGN(addr + 1, P4D_SIZE); break;
	case PUD_LVL: addr = ALIGN(addr + 1, PUD_SIZE); break;
	case PMD_LVL: addr = ALIGN(addr + 1, PMD_SIZE); break;
	case PTE_LVL: addr = ALIGN(addr + 1, PAGE_SIZE); break;
	}

	*paddr = addr;
}

//
// Proc File
//

static struct mm_struct *get_mm_from_pid(pid_t pid)
{
	struct task_struct *task;
	struct mm_struct *mm;

	task = pid_task(find_vpid(pid), PIDTYPE_PID);
	if (!task) {
		return NULL;
	}

	mm = get_task_mm(task);

	if (!mm) {
		return NULL;
	}

	return mm;
}

static int pt_seq_show(struct seq_file *s, void *v)
{
	ulong *spos = v;

	if (!*spos) {
		pr_warn(
			"Dumping page table for %s %d in range [0x%016lx, 0x%016lx)\n", 
			is_vmroot_mode() ? "VM" : "process",
			state.global.pid, state.global.user_lo, state.global.user_hi
		);

		seq_printf(s, "Dumping page table for %s %d in range [0x%016lx, 0x%016lx)\n", 
			is_vmroot_mode() ? "VM" : "process",
			state.global.pid, state.global.user_lo, state.global.user_hi
		);

		*spos = state.global.user_lo;
	}

	// Only EPT needs special walker, SPT does not
	if (is_vmroot_mode() && state.vmroot.direct_map) {
		// Not captured yet
		if (state.vmroot.active_vm != state.global.pid) {
			seq_printf(s, "VM enter event not fired, please wait a while.\n");
			return -EAGAIN;
		}

		// Thank you, Intel
		if (state.vmroot.table_type != PT64_ROOT_4LEVEL && state.vmroot.table_type != PT64_ROOT_5LEVEL) {
			seq_printf(s, "Legacy VM mapping mode is not supported.\n");
			return -EINVAL;
		}

		table_walker(s, spos, __va(state.vmroot.root_hpa), &ept_ops);
	}
	else {
		struct mm_struct *mm = get_mm_from_pid(state.global.pid);

		if (!mm) {
			seq_printf(s, "Cannot access mm_struct for %d\n", state.global.pid);
			return -EINVAL;
		}

		table_walker(s, spos, mm->pgd, &normal_ops);

		mmput(mm);
	}

	return 0;
}

static void *pt_seq_start(struct seq_file *s, loff_t *pos)
{
	loff_t *spos;

	// Do not restart terminated sequence
	if (*pos == -1UL)
		return NULL;

	spos = kmalloc(sizeof(loff_t), GFP_KERNEL);
	if (!spos)
		return NULL;

	*spos = *pos;
	return spos;
}

static void *pt_seq_next(struct seq_file *s, void *v, loff_t *pos)
{
	loff_t *spos = v;
	ulong sposv = *spos;
	ulong posv = *pos;

	// Stall or overflow
	if (sposv <= posv)
		goto terminate;

	// User don't care
	if (sposv >= state.global.user_hi)
		goto terminate;

	// No need to go beyond
	if (is_vmroot_mode() && sposv >= EPT_PHYS_MAX)
		goto terminate;

	// Go past user space
	if (is_normal_mode() && sposv >= TASK_SIZE_MAX) {
		// Jump to kernel space
		if (sposv < PAGE_OFFSET)
			*spos = PAGE_OFFSET;
	}

	*pos = *spos;

	return spos;

terminate:
	*spos = -1UL;
	*pos = -1UL;
	return NULL;
}

static void pt_seq_stop(struct seq_file *s, void *v)
{
	kfree(v);
}

ssize_t pt_write(struct file *file, const char __user *buf, size_t count, loff_t *ppos)
{
	char mybuf[65] = { 0 };
	char *myptr = mybuf;
	size_t mylen = sizeof(mybuf) - 1;
	int ret = 0;

	if (count < mylen) {
		mylen = count;
	}

	if (!mylen)
		return count;

	if (copy_from_user(myptr, buf, mylen))
		return -1;

	state.global.mode = myptr[0];
	if (state.global.mode < '0' || '9' < state.global.mode) {
		myptr++;
		mylen--;

		if (!mylen)
			return count;
	}
	else {
		state.global.mode = NORMAL_MODE;
	}

	ret = sscanf(myptr, "%d,%lx,%lx", &state.global.pid, &state.global.user_lo, &state.global.user_hi);
	if (ret == 3) {
		if (state.global.user_hi < state.global.user_lo) {
			ulong tmp = state.global.user_lo;
			state.global.user_lo = state.global.user_hi;
			state.global.user_hi = tmp;
		}

		if (is_user_psudomode() || is_kernel_psudomode())
			state.global.mode = NORMAL_MODE;
	}
	else if (ret == 1) {
		state.global.user_lo = 0;
		state.global.user_hi = -1UL;

		if (is_user_psudomode())
			state.global.user_hi = TASK_SIZE_MAX;

		if (is_kernel_psudomode())
			state.global.user_lo = PAGE_OFFSET;
	}
	else {
		pr_warn("Invalid input query: %s\n", myptr);
		state.global.user_lo = 0;
		state.global.user_hi = -1UL;
		state.global.pid = current->pid;
	}

	

	return count;
}

static struct seq_operations pt_seq_ops = {
	.start = pt_seq_start,
	.next  = pt_seq_next,
	.stop  = pt_seq_stop,
	.show  = pt_seq_show,
};

static int pt_open(struct inode *inode, struct file *file)
{
	return seq_open(file, &pt_seq_ops);
};

static struct proc_ops pt_file_ops = {
	.proc_open    = pt_open,
	.proc_read    = seq_read,
	.proc_write   = pt_write,
	.proc_lseek   = seq_lseek,
	.proc_release = seq_release
};

//
// Probe KVM
//

static int extract_tdp_root(struct kprobe *p, struct pt_regs *regs)
{
	struct kvm_vcpu *cpu = (void *) regs_get_kernel_argument(regs, 0);
	struct kvm_mmu *mmu = cpu->arch.mmu;

	if (cpu->kvm->userspace_pid == state.global.pid) {
		pid_t oldpid = state.vmroot.active_vm;

		state.vmroot.active_vm = cpu->kvm->userspace_pid;
		state.vmroot.root_hpa = mmu->root.hpa;
		state.vmroot.table_type = mmu->root_role.level;
		state.vmroot.direct_map = mmu->root_role.direct;
		state.vmroot.maxphys = cpu->arch.maxphyaddr;

		if (oldpid != state.vmroot.active_vm) {
			pr_warn("Got VM %d: Type %d %s page table with root 0x%lx mapping %d bit phys addr.\n",
				state.vmroot.active_vm, state.vmroot.table_type, state.vmroot.direct_map ? "nested" : "shadow", state.vmroot.root_hpa, state.vmroot.maxphys);
		}
	}

	return 0;
}

static struct kprobe kp = {
	.symbol_name = "vcpu_load",
	.pre_handler = extract_tdp_root,
};

//
// Module Manager
//

int init_module_dumper(void)
{
	int ret;

	struct proc_dir_entry *pt_file = proc_create("ptdump", 0666, NULL, &pt_file_ops);
	if (!pt_file)
		return -ENOMEM;

	ret = register_kprobe(&kp);
	if (ret < 0) {
		pr_err("register_kprobe failed, returned %d\n", ret);
		remove_proc_entry("ptdump", NULL);
		return ret;
	}

	return 0;
}

void cleanup_module_dumper(void)
{
	unregister_kprobe(&kp);
	remove_proc_entry("ptdump", NULL);
}

late_initcall(init_module_dumper)
module_exit(cleanup_module_dumper)

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Jiyuan Zhang <jiyuanz3@illinois.edu>");
MODULE_DESCRIPTION("Kernel debugging helper that dumps pagetables");
