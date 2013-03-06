// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#[doc(hidden)];
#[forbid(managed_heap_memory)];

use cast::transmute;
use io::{fd_t, WriterUtil};
use libc::{c_char, c_void, c_uint, intptr_t, uintptr_t, size_t};
use libc;
use managed::raw::{BoxRepr, BoxHeaderRepr,
                   RC_MANAGED_UNIQUE, RC_IMMORTAL};
use option::{Option,Some,None};
use ptr::{mut_null, null, to_unsafe_ptr, offset};
use sys::size_of;
use sys::{TypeDesc, size_of};
use task::each_retained_ptr;
use uint;
use vec;
use unstable::exchange_alloc;
use unstable::intrinsics::ctlz64;
use container::{Container, Mutable, Map};
use trie;
use rt::swap_registers;

#[cfg(notest)] use ptr::to_unsafe_ptr;

/**
 * Runtime structures
 *
 * NB: These must match the representation in the C++ runtime.
 */

type DropGlue<'self> = &'self fn(**TypeDesc, *c_void);
type FreeGlue<'self> = &'self fn(**TypeDesc, *c_void);

type TaskID = uintptr_t;

#[cfg(target_word_size = "64")]
pub struct StackSegment {
    prev: *StackSegment,
    next: *StackSegment,
    end: uintptr_t,
    valgrind_id: c_uint,
    rust_task: *Task,
    canary: uintptr_t,
    data: u8
}

#[cfg(target_word_size = "32")]
pub struct StackSegment {
    prev: *StackSegment,
    next: *StackSegment,
    end: uintptr_t,
    valgrind_id: c_uint,
    pad: u32,
    rust_task: *Task,
    canary: uintptr_t,
    data: u8
}

struct Scheduler { priv opaque: () }
struct SchedulerLoop { priv opaque: () }
struct Kernel { priv opaque: () }
struct Env { priv opaque: () }
struct AllocHeader { priv opaque: () }
struct MemoryRegion { priv opaque: () }

#[cfg(target_arch="x86")]
#[cfg(target_arch="arm")]
struct Registers {
    data: [u32, ..16]
}

#[cfg(target_arch="mips")]
struct Registers {
    data: [u32, ..32]
}

#[cfg(target_arch="x86")]
#[cfg(target_arch="arm")]
#[cfg(target_arch="mips")]
struct Context {
    regs: Registers,
    next: *Context,
    pad: [u32, ..3]
}

#[cfg(target_arch="x86_64")]
struct Registers {
    data: [u64, ..22]
}

#[cfg(target_arch="x86_64")]
struct Context {
    regs: Registers,
    next: *Context,
    pad: uintptr_t
}

pub struct BoxedRegion {
    env: *Env,
    backing_region: *MemoryRegion,
    live_allocs: *BoxRepr,
}

#[cfg(target_arch="x86")]
#[cfg(target_arch="arm")]
#[cfg(target_arch="mips")]
pub struct Task {
    // Public fields
    refcount: intptr_t,                 // 0
    id: TaskID,                         // 4
    pad: [u32, ..2],                    // 8
    ctx: Context,                       // 16
    stack_segment: *StackSegment,       // 96
    runtime_sp: uintptr_t,              // 100
    scheduler: *Scheduler,              // 104
    scheduler_loop: *SchedulerLoop,     // 108

    // Fields known only to the runtime
    kernel: *Kernel,                    // 112
    name: *c_char,                      // 116
    list_index: i32,                    // 120
    boxed_region: BoxedRegion,          // 128
    gc: *c_void,                        // 132
}

#[cfg(target_arch="x86_64")]
pub struct Task {
    // Public fields
    refcount: intptr_t,
    id: TaskID,
    ctx: Context,
    stack_segment: *StackSegment,
    runtime_sp: uintptr_t,
    scheduler: *Scheduler,
    scheduler_loop: *SchedulerLoop,

    // Fields known only to the runtime
    kernel: *Kernel,
    name: *c_char,
    list_index: i32,
    boxed_region: BoxedRegion,
    gc: *c_void,
}

// A transmuted ~to one of these is held in the task.
// The annihilator drops it. Until then, all GC runs
// through it.

struct HeapRecord {
    size: uint,
    is_marked: bool
}

pub struct Gc {
    task: *Task,
    debug_gc: bool,
    actually_gc: bool,
    report_gc_stats: bool,

    gc_in_progress: bool,
    free_buffer: trie::TrieMap<()>,
    heap: trie::TrieMap<HeapRecord>,
    lowest: uint,
    highest: uint,

    threshold: uint,

    n_collections: uint,
    n_ns_marking: Stat,
    n_ns_sweeping: Stat,
    n_ns_total: Stat,
    n_boxes_marked: Stat,
    n_bytes_marked: Stat,
    n_boxes_swept: Stat,
    n_bytes_swept: Stat,
    n_boxes_annihilated: Stat,
    n_bytes_annihilated: Stat,
}

#[cfg(unix)]
fn debug_mem() -> bool {
    ::rt::env::get().debug_mem
}

pub impl Gc {
    fn get_task_gc() -> &mut Gc {
        unsafe {
            let tp : *Task = transmute(rust_get_task());
            let task : &mut Task = transmute(tp);
            if task.gc == null() {
                task.gc = transmute(~Gc::new(tp));
            }
            let p: &mut ~Gc = transmute(&(task.gc));
            &mut (**p)
        }
    }


    #[cfg(unix)]
    fn debug_gc() -> bool {
        use os;
        use libc;
        do os::as_c_charp("RUST_DEBUG_GC") |p| {
            unsafe { libc::getenv(p) != null() }
        }
    }

    #[cfg(unix)]
    fn report_gc_stats() -> bool {
        use os;
        use libc;
        do os::as_c_charp("RUST_REPORT_GC_STATS") |p| {
            unsafe { libc::getenv(p) != null() }
        }
    }

    #[cfg(unix)]
    fn actually_gc() -> bool {
        use os;
        use libc;
        do os::as_c_charp("RUST_ACTUALLY_GC") |p| {
            unsafe { libc::getenv(p) != null() }
        }
    }

    #[cfg(windows)]
    fn debug_gc() -> bool {
        false
    }

    #[cfg(windows)]
    fn report_gc_stats() -> bool {
        false
    }
    
    #[cfg(windows)]
    fn actually_gc() -> bool {
        false
    }

    fn new(t: *Task) -> Gc {
        Gc {
            task: t,
            debug_gc: Gc::debug_gc(),
            actually_gc: Gc::actually_gc(),
            report_gc_stats: Gc::report_gc_stats(),

            gc_in_progress: false,
            free_buffer: trie::TrieMap::new(),
            heap: trie::TrieMap::new(),
            lowest: 0,
            highest: 0,

            threshold: 1024,

            n_collections: 0,
            n_ns_marking: Stat::new(),
            n_ns_sweeping: Stat::new(),
            n_ns_total: Stat::new(),
            n_boxes_marked: Stat::new(),
            n_bytes_marked: Stat::new(),
            n_boxes_swept: Stat::new(),
            n_bytes_swept: Stat::new(),
            n_boxes_annihilated: Stat::new(),
            n_bytes_annihilated: Stat::new(),
        }
    }

    #[inline(always)]
    fn stderr_fd() -> fd_t {
        libc::STDERR_FILENO as fd_t
    }

    #[inline(always)]
    fn debug_str(&self, s: &str) {
        if self.debug_gc {
            Gc::stderr_fd().write_str(s)
        }
    }

    #[inline(always)]
    fn debug_uint(&self, n: uint) {
        if self.debug_gc {
            Gc::stderr_fd().write_uint(n)
        }
    }

    #[inline(always)]
    fn debug_str_hex(&self, s: &str, p: uint) {
        if self.debug_gc {
            Gc::write_str_hex(s, p);
        }
    }

    #[inline(always)]
    fn debug_str_range(&self, s: &str,
                       p: uint, len: uint) {
        if self.debug_gc {
            let e = Gc::stderr_fd();
            e.write_str(s);
            e.write_str(": [");
            e.write_hex_uint(p);
            e.write_str(", ");
            e.write_hex_uint(p + len);
            e.write_str(") = ");
            e.write_uint(len);
            e.write_str(" bytes\n");
        }
    }

    fn write_str_uint(s: &str, n: uint) {
        let e = Gc::stderr_fd();
        e.write_str(s);
        e.write_str(": ");
        e.write_uint(n);
        e.write_str("\n");
    }

    fn write_str_hex(s: &str, n: uint) {
        let e = Gc::stderr_fd();
        e.write_str(s);
        e.write_str(": ");
        e.write_hex_uint(n);
        e.write_str("\n");
    }

    fn report_stat(s: &str, t: &mut Stat) {
        let e = Gc::stderr_fd();
        e.write_str("    ");
        e.write_str(s);
        e.write_str(": ");
        e.write_uint(t.curr as uint);
        t.flush();
        e.write_str(" curr, ");
        e.write_uint(t.total as uint);
        e.write_str(" total (hist:");
        for vec::eachi(t.hist) |i, elt| {
            if *elt != 0 {
                e.write_str(" ");
                e.write_uint(i);
                e.write_str(":");
                e.write_uint(*elt as uint);
            }
        }
        e.write_str(")\n");
    }

    fn report_stats(&mut self, phase: &str) {
        if self.report_gc_stats {
            let e = Gc::stderr_fd();
            e.write_str("\n--- ");
            e.write_str(phase);
            e.write_str(" stats ---\n");
            Gc::write_str_uint("    n_collections",
                               self.n_collections);
            Gc::report_stat("n_ns_marking",
                            &mut self.n_ns_marking);
            Gc::report_stat("n_ns_sweeping",
                            &mut self.n_ns_sweeping);
            Gc::report_stat("n_ns_total",
                            &mut self.n_ns_total);

            Gc::report_stat("n_boxes_marked",
                            &mut self.n_boxes_marked);
            Gc::report_stat("n_bytes_marked",
                            &mut self.n_bytes_marked);
            Gc::report_stat("n_boxes_swept",
                            &mut self.n_boxes_swept);
            Gc::report_stat("n_bytes_swept",
                            &mut self.n_bytes_swept);
            Gc::report_stat("n_boxes_annihilated",
                            &mut self.n_boxes_annihilated);
            Gc::report_stat("n_bytes_annihilated",
                            &mut self.n_bytes_annihilated);
        }
    }

    fn note_alloc(&mut self, ptr: uint, sz: uint, align: uint) {
        assert!(!self.gc_in_progress);
        let h = HeapRecord {
            size: exchange_alloc::get_box_size(sz, align),
            is_marked: false
        };
        self.debug_str_range("gc::note_malloc", ptr, h.size);
        self.heap.insert(ptr, h);
        if ! self.actually_gc {
            return;
        }
        if self.heap.len() > self.threshold {
            self.debug_str("commencing gc at threshold: ");
            self.debug_uint(self.threshold);
            self.debug_str("\n");
            let prev = self.heap.len();
            unsafe {
                self.gc();
            }
            self.debug_str("gc complete, heap count: ");
            self.debug_uint(self.heap.len());
            self.debug_str(" (freed ");
            self.debug_uint(prev - self.heap.len());
            self.debug_str(" boxes)\n");
            if self.heap.len() * 2 > self.threshold {
                self.debug_str("gc did not recover enough, \
                                raising threshold to: ");
                self.debug_uint(self.threshold * 2);
                self.debug_str("\n");
                self.threshold *= 2;
            }
        }
    }

    fn note_free(&mut self, ptr: uint) {
        self.debug_str_hex("gc::note_free", ptr);
        if self.gc_in_progress {
            self.free_buffer.insert(ptr, ());
        } else {
            self.heap.remove(&ptr);
            if ! self.actually_gc {
                return;
            }
            if self.heap.len() < (self.threshold / 4) {
                self.debug_str("lowering gc threshold to: ");
                self.debug_uint(self.threshold / 2);
                self.debug_str("\n");
                self.threshold /= 2;
            }
        }
    }

    fn note_realloc(&mut self, from: uint, to: uint, sz: uint) {
        assert!(!self.gc_in_progress);
        if self.debug_gc {
            let e = Gc::stderr_fd();
            e.write_str("gc::note_realloc: ");
            e.write_hex_uint(from);
            e.write_str(" -> [");
            e.write_hex_uint(to);
            e.write_str(", ");
            e.write_hex_uint(to + sz);
            e.write_str(")\n");
        }
        self.heap.remove(&from);
        let h = HeapRecord {
            size: sz,
            is_marked: false
        };
        self.heap.insert(to, h);
    }

    fn check_consistency(&mut self, phase: &str) {
        let mut tmp = trie::TrieMap::new();
        for self.each_live_alloc |box| {
            let box = box as uint;
            if ! self.heap.contains_key(&box) {
                Gc::stderr_fd().write_str(phase);
                Gc::write_str_hex(" inconsistency: gc heap \
                                   missing live alloc ptr",
                                  box)
            }
            tmp.insert(box, ());
        }
        for self.heap.each_key |box| {
            if ! tmp.contains_key(box) {
                Gc::stderr_fd().write_str(phase);
                Gc::write_str_hex(" inconsistency: live allocs \
                                   missing gc heap ptr",
                                  *box)
            }
        }
        if self.heap.len() != tmp.len() {
            Gc::stderr_fd().write_str(phase);
            Gc::write_str_uint(" inconsistency: num gc heap ptr",
                               self.heap.len());
            Gc::stderr_fd().write_str(phase);
            Gc::write_str_uint(" inconsistency: num live alloc ptrs",
                               tmp.len());
        }
    }

    unsafe fn each_live_alloc(&self, f: &fn(box: *mut BoxRepr) -> bool) {
        let box = (*self.task).boxed_region.live_allocs;
        let mut box: *mut BoxRepr = transmute(copy box);
        while box != mut_null() {
            let next = transmute(copy (*box).header.next);
            if ! f(box) {
                break
            }
            box = next
        }
    }
                  
    unsafe fn drop_boxes(actually_drop: bool,
                                debug_flag: bool,
                                boxes_dropped: &mut Stat,
                                bytes_dropped: &mut Stat,
                                free_buffer: &mut trie::TrieMap<()>,
                                each: &fn(&fn(*mut BoxRepr, uint) -> bool)) {
        
        for each |boxp, _size| {
            if free_buffer.contains_key(&(boxp as uint)) {
                loop;
            }
            let box: &mut BoxRepr = transmute(boxp);
            if box.header.ref_count == RC_MANAGED_UNIQUE {
                loop;
            }
            if debug_flag {
                Gc::write_str_hex("(drop boxes) pass #1: setting immortal",
                                  boxp as uint);
            }
            if actually_drop {
                box.header.ref_count = RC_IMMORTAL;
            }
        }

        for each |boxp, _size| {
            if free_buffer.contains_key(&(boxp as uint)) {
                loop;
            }
            let box: &BoxRepr = transmute(boxp);
            if box.header.ref_count == RC_MANAGED_UNIQUE {
                loop;
            }
            let tydesc: *TypeDesc = transmute(box.header.type_desc);
            let drop_glue: DropGlue = transmute(((*tydesc).drop_glue, 0));
            if debug_flag {
                Gc::write_str_hex("(drop boxes) pass #2: running drop glue",
                                  boxp as uint);
            }
            if actually_drop {
                drop_glue(to_unsafe_ptr(&tydesc),
                          transmute(&(*box).data));
            }
        }

        for each |boxp, size| {
            if free_buffer.contains_key(&(boxp as uint)) {
                loop;
            }
            let box: &BoxRepr = transmute(boxp);
            if box.header.ref_count == RC_MANAGED_UNIQUE {
                loop;
            }
            if debug_flag {
                Gc::write_str_hex("(drop boxes) pass #3: freeing",
                                  boxp as uint);
            }
            if actually_drop {
                boxes_dropped.curr += 1;
                bytes_dropped.curr += size as i64;
                rust_upcall_free(transmute(box));
                free_buffer.insert(boxp as uint, ());
            }
        }
    }

    unsafe fn mark_object(&mut self,
                          level: uint,
                          addr: uint) {

        if addr < self.lowest || addr > self.highest {
            self.debug_str_hex("implausible heap addr", addr);
            return;
        }

        self.debug_str_hex("searching for prev object", addr);
        let (obj, record) = match self.heap.prev(addr) {
            None => {
                self.debug_str_hex("no object found", addr);
                return
            }
            Some((obj,rptr)) => (obj, *rptr)
        };

        if addr > obj + record.size {
            self.debug_str_range("address past object-end",
                                 obj, record.size);
            // We picked the object previous to the probe addr; but that
            // object might not extend all the way to _include_ the probe
            // addr. If not, skip.
            return;
        }

        if record.is_marked {
            self.debug_str_hex("object already marked", obj);
            // if we've already visited, don't visit again.
            return;
        }
        let record = HeapRecord {
            is_marked: true,
            ..record
        };
        self.heap.insert(obj, record);

        self.n_boxes_marked.curr += 1;
        self.n_bytes_marked.curr += record.size as i64;

        let adj = size_of::<BoxHeaderRepr>();
        self.mark_range("marking object", level + 1,
                        obj + adj, record.size - adj);
    }
                         
    unsafe fn mark_stack(&mut self) {

        // We want to avoid marking frames below us, so we
        // take a base address from the current frame and
        // pass it into the stack-marker.
        let base = 0;
        let base : uint = transmute(&base);
        let mut segment = (*self.task).stack_segment;
        while segment != null() {
            let mut ptr: uint = transmute(&(*segment).data);
            let mut end: uint = transmute(copy (*segment).end);
            if ptr <= base && base < end {
                self.debug_str_hex("limiting stack-marking to base",
                                   base);
                ptr = base;
            }
            self.mark_range("marking stack segment",
                            0, ptr, end-ptr);
            segment = (*segment).prev;
        }
    }

    unsafe fn mark_range(&mut self,
                         s: &str, level: uint,
                         p: uint, sz: uint) {
        self.debug_str("level ");
        self.debug_uint(level);
        self.debug_str(": ");
        self.debug_str_range(s, p, sz);
        let mut curr = p;
        let end = p + sz;
        while curr + size_of::<uint>() <= end {
            self.mark_object(level, *(curr as *uint));
            curr += 1;
        }
    }

    unsafe fn mark(&mut self) {

        self.lowest = match self.heap.next(0) {
            None => 0,
            Some((k, _)) => k
        };
        self.highest = match self.heap.prev(uint::max_value) {
            None => uint::max_value,
            Some((k, r)) => k + r.size
        };

        self.debug_str_hex("lowest heap ptr", self.lowest);
        self.debug_str_hex("highest heap ptr", self.highest);
        
        self.mark_stack();

        
        self.debug_str("marking TLS values\n");
        do each_retained_ptr(transmute(self.task)) |p| {
            self.debug_str_hex("marking TLS value",
                               transmute(p));
            self.mark_object(0, transmute(p));
        }

        // Awkward but necessary: registers must be 16-byte
        // aligned on x64 due to dumping xmm state using
        // movapd. So we don't use the Registers structure.
        self.debug_str("marking registers\n");
        let regs = [0u64, ..64];
        let r : uint = transmute(&regs);
        let r = (r + 16) & (!15);
        swap_registers(transmute(r), transmute(r));
        for regs.each |r| {
            self.mark_object(0, transmute(*r));
        }
    }

    unsafe fn sweep(&mut self) {        
        do Gc::drop_boxes(self.actually_gc,
                          self.debug_gc,
                          &mut self.n_boxes_swept,
                          &mut self.n_bytes_swept,
                          &mut self.free_buffer) |step| {
            for self.heap.mutate_values |ptr, record| {
                if record.is_marked {
                    loop;
                }
                step(transmute(ptr), record.size);
            }
        }

        // Clear all mark bits
        for self.heap.mutate_values |_, record| {
            record.is_marked = false;
        }

        // Clean out the free buffer
        for self.free_buffer.each_key |ptr| {
            self.heap.remove(ptr);
            ()
        }

        self.free_buffer.clear();
    }

    unsafe fn gc(&mut self) {

        let mut start = 0;
        let mut end = 0;
        let mut mark_start = 0;
        let mut mark_end = 0;
        let mut sweep_start = 0;
        let mut sweep_end = 0;

        precise_time_ns(&mut start);

        // NB: need this here before we lock down the GC, to make sure
        // TLS is initialized; easiest approach. It allocates a @Dvec.
        do each_retained_ptr(transmute(self.task)) |_| { }

        self.debug_str("gc starting\n");
        self.gc_in_progress = true;
        self.check_consistency("pre-gc");

        precise_time_ns(&mut mark_start);
        self.mark();
        precise_time_ns(&mut mark_end);

        precise_time_ns(&mut sweep_start);
        self.sweep();
        precise_time_ns(&mut sweep_end);

        self.check_consistency("post-gc");
        self.gc_in_progress = false; 
        self.debug_str("gc finished\n");

        self.n_collections += 1;
        precise_time_ns(&mut end);

        self.n_ns_marking.curr += (mark_end - mark_start) as i64;
        self.n_ns_sweeping.curr += (sweep_end - sweep_start) as i64;
        self.n_ns_total.curr += (end - start) as i64;

        self.report_stats("gc");
    }

    unsafe fn annihilate(&mut self) {
        self.debug_str("annihilation starting\n");
        self.check_consistency("pre-annihilate");
        self.gc_in_progress = true;

        do Gc::drop_boxes(true,
                          self.debug_gc,
                          &mut self.n_boxes_annihilated,
                          &mut self.n_bytes_annihilated,
                          &mut self.free_buffer) |step| {
            for self.heap.mutate_values |ptr, record| {
                step(transmute(ptr), record.size);
            }
        }
        for self.free_buffer.each_key |ptr| {
            self.heap.remove(ptr);
            ()
        }
        self.gc_in_progress = false;
        self.check_consistency("post-annihilate");
        self.debug_str("annihilation finished\n");
        self.report_stats("annihilation");
    }
}

pub struct Stat {
    curr: i64,
    total: i64,
    hist: [i64, ..64],
}

pub impl Stat {
    fn flush(&mut self) {
        self.total += self.curr;
        unsafe {
            self.hist[64 - ctlz64(self.curr)] += 1;
        }
        self.curr = 0;
    }
    fn new() -> Stat {
        Stat {
            curr: 0,
            total: 0,
            hist: [0, ..64]
        }
    }
}


/*
 * Box annihilation
 *
 * This runs at task death to free all boxes.
 */


/// Destroys all managed memory (i.e. @ boxes) held by the current task.
#[cfg(notest)]
#[lang="annihilate"]
pub unsafe fn annihilate() {
    let gc : &mut Gc = Gc::get_task_gc();
    gc.annihilate();
    let task: &Task = transmute(rust_get_task());
    let _dropme: ~Gc = transmute(task.gc);
}

pub fn gc() {
    unsafe {
        Gc::get_task_gc().gc();
    }
}

#[link_name = "rustrt"]
extern {
    fn precise_time_ns(ns: &mut u64);

    #[rust_stack]
    // FIXME (#4386): Unable to make following method private.
    fn rust_get_task() -> *c_void;

    #[rust_stack]
    fn rust_upcall_free(ptr: *c_char);
}

