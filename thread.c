#include "threads/thread.h"
#include <debug.h>
#include <stddef.h>
#include <random.h>
#include <stdio.h>
#include <string.h>
#include "threads/flags.h"
#include "threads/interrupt.h"
#include "threads/intr-stubs.h"
#include "threads/palloc.h"
#include "threads/switch.h"
#include "threads/synch.h"
#include "threads/vaddr.h"
#include "devices/timer.h"
#ifdef USERPROG
#include "userprog/process.h"
#endif

/* Random value for struct thread's `magic' member.
   Used to detect stack overflow.  See the big comment at the top
   of thread.h for details. */
#define THREAD_MAGIC 0xcd6abf4b

/* List of processes in THREAD_READY state, that is, processes
   that are ready to run but not actually running. */
static struct list ready_list[PRI_MAX + 1]; // ready_list를 priority에 따라 여러개의 queue로 구성한다.

/* timer_sleep()에 의해 blocked state가 된 thread들이 insert 
   되어있는 queue. */
static struct list sleep_list;

/* List of all processes.  Processes are added to this list
   when they are first scheduled and removed when they exit. */
static struct list all_list;

/* Idle thread. */
static struct thread *idle_thread;

/* Initial thread, the thread running init.c:main(). */
static struct thread *initial_thread;

/* Lock used by allocate_tid(). */
static struct lock tid_lock;

/* Stack frame for kernel_thread(). */
struct kernel_thread_frame 
  {
    void *eip;                  /* Return address. */
    thread_func *function;      /* Function to call. */
    void *aux;                  /* Auxiliary data for function. */
  };

/* Statistics. */
static long long idle_ticks;    /* # of timer ticks spent idle. */
static long long kernel_ticks;  /* # of timer ticks in kernel threads. */
static long long user_ticks;    /* # of timer ticks in user programs. */
static int64_t global_tick;     /* thread들의 wakeup_tick들 중 최소값. */

/* fixed point(17.14) number에서의 1. */
static int f = 1 << 14; 

/* load average(fixed point로 표현된 실수) */
int load_average; 

/* Scheduling. */
#define TIME_SLICE 4            /* # of timer ticks to give each thread. */
static unsigned thread_ticks;   /* # of timer ticks since last yield. */

/* If false (default), use round-robin scheduler.
   If true, use multi-level feedback queue scheduler.
   Controlled by kernel command-line option "-o mlfqs". */
bool thread_mlfqs;
bool thread_report_latency;

static void kernel_thread (thread_func *, void *aux);

static void idle (void *aux UNUSED);
static struct thread *running_thread (void);
static struct thread *next_thread_to_run (void);
static void init_thread (struct thread *, const char *name, int priority);
static bool is_thread (struct thread *) UNUSED;
static void *alloc_frame (struct thread *, size_t size);
static void schedule (void);
void thread_schedule_tail (struct thread *prev);
static tid_t allocate_tid (void);

/* Initializes the threading system by transforming the code
   that's currently running into a thread.  This can't work in
   general and it is possible in this case only because loader.S
   was careful to put the bottom of the stack at a page boundary.

   Also initializes the run queue and the tid lock.

   After calling this function, be sure to initialize the page
   allocator before trying to create any threads with
   thread_create().

   It is not safe to call thread_current() until this function
   finishes. */
void
thread_init (void) 
{
  int i;
  ASSERT (intr_get_level () == INTR_OFF);

  lock_init (&tid_lock);
  list_init (&sleep_list); /* sleep_list 초기화. */
  list_init (&all_list);
  for(i = 0 ; i<=PRI_MAX ; i++)
  list_init (&ready_list[i]); /* 모든 ready_list 초기화. */

  /* Set up a thread structure for the running thread. */
  initial_thread = running_thread ();
  init_thread (initial_thread, "main", PRI_DEFAULT);
  initial_thread->status = THREAD_RUNNING;
  initial_thread->tid = allocate_tid ();
}

/* Starts preemptive thread scheduling by enabling interrupts.
   Also creates the idle thread. */
void
thread_start (void) 
{
  /* Create the idle thread. */
  struct semaphore idle_started;
  sema_init (&idle_started, 0);
  thread_create ("idle", PRI_MIN, idle, &idle_started);

  /* Start preemptive thread scheduling. */
  intr_enable ();

  /* Wait for the idle thread to initialize idle_thread. */
  sema_down (&idle_started);
}

/* Called by the timer interrupt handler at each timer tick.
   Thus, this function runs in an external interrupt context. */
void
thread_tick (void) 
{
  struct thread *t = thread_current ();

  /* Update statistics. */
  if (t == idle_thread)
    idle_ticks++;
#ifdef USERPROG
  else if (t->pagedir != NULL)
    user_ticks++;
#endif
  else
    kernel_ticks++;

  /* Enforce preemption. */
  if (++thread_ticks >= TIME_SLICE)
    intr_yield_on_return ();
}

/* Prints thread statistics. */
void
thread_print_stats (void) 
{
  printf ("Thread: %lld idle ticks, %lld kernel ticks, %lld user ticks\n",
          idle_ticks, kernel_ticks, user_ticks);
}

/* Creates a new kernel thread named NAME with the given initial
   PRIORITY, which executes FUNCTION passing AUX as the argument,
   and adds it to the ready queue.  Returns the thread identifier
   for the new thread, or TID_ERROR if creation fails.

   If thread_start() has been called, then the new thread may be
   scheduled before thread_create() returns.  It could even exit
   before thread_create() returns.  Contrariwise, the original
   thread may run for any amount of time before the new thread is
   scheduled.  Use a semaphore or some other form of
   synchronization if you need to ensure ordering.

   The code provided sets the new thread's `priority' member to
   PRIORITY, but no actual priority scheduling is implemented.
   Priority scheduling is the goal of Problem 1-3. */
tid_t
thread_create (const char *name, int priority,
               thread_func *function, void *aux) 
{
  struct thread *t;
  struct kernel_thread_frame *kf;
  struct switch_entry_frame *ef;
  struct switch_threads_frame *sf;
  tid_t tid;

  ASSERT (function != NULL);

  /* Allocate thread. */
  t = palloc_get_page (PAL_ZERO);
  if (t == NULL)
    return TID_ERROR;

  /* Initialize thread. */
  init_thread (t, name, priority);
  tid = t->tid = allocate_tid ();

  /* Stack frame for kernel_thread(). */
  kf = alloc_frame (t, sizeof *kf);
  kf->eip = NULL;
  kf->function = function;
  kf->aux = aux;

  /* Stack frame for switch_entry(). */
  ef = alloc_frame (t, sizeof *ef);
  ef->eip = (void (*) (void)) kernel_thread;

  /* Stack frame for switch_threads(). */
  sf = alloc_frame (t, sizeof *sf);
  sf->eip = switch_entry;
  sf->ebp = 0;

  /* Add to run queue. */
  thread_unblock (t);

  /* 만약 새로운 thread의 priority가 현재 thread의 priority보다 크다면,
     cmp_cur_begin_priority를 통해 알맞게 thread_yield를 수행한다. */
  cmp_cur_begin_priority ();

  return tid;
}

/* Puts the current thread to sleep.  It will not be scheduled
   again until awoken by thread_unblock().

   This function must be called with interrupts turned off.  It
   is usually a better idea to use one of the synchronization
   primitives in synch.h. */
void
thread_block (void) 
{
  ASSERT (!intr_context ());
  ASSERT (intr_get_level () == INTR_OFF);

  thread_current ()->status = THREAD_BLOCKED;
  schedule ();
}

/* Transitions a blocked thread T to the ready-to-run state.
   This is an error if T is not blocked.  (Use thread_yield() to
   make the running thread ready.)

   This function does not preempt the running thread.  This can
   be important: if the caller had disabled interrupts itself,
   it may expect that it can atomically unblock a thread and
   update other data. */
void
thread_unblock (struct thread *t) 
{
  enum intr_level old_level;

  ASSERT (is_thread (t));

  old_level = intr_disable ();
  ASSERT (t->status == THREAD_BLOCKED);
  list_push_back (&ready_list[t->priority], &t->elem); // ready_list[i]에는 priority가 i인 thread를 insert한다.
  t->status = THREAD_READY;
  intr_set_level (old_level);
}

/* Returns the name of the running thread. */
const char *
thread_name (void) 
{
  return thread_current ()->name;
}

/* Returns the running thread.
   This is running_thread() plus a couple of sanity checks.
   See the big comment at the top of thread.h for details. */
struct thread *
thread_current (void) 
{
  struct thread *t = running_thread ();
  
  /* Make sure T is really a thread.
     If either of these assertions fire, then your thread may
     have overflowed its stack.  Each thread has less than 4 kB
     of stack, so a few big automatic arrays or moderate
     recursion can cause stack overflow. */
  ASSERT (is_thread (t));
  ASSERT (t->status == THREAD_RUNNING);

  return t;
}

/* Returns the running thread's tid. */
tid_t
thread_tid (void) 
{
  return thread_current ()->tid;
}

/* Deschedules the current thread and destroys it.  Never
   returns to the caller. */
void
thread_exit (void) 
{
  ASSERT (!intr_context ());

#ifdef USERPROG
  process_exit ();
#endif

  /* Remove thread from all threads list, set our status to dying,
     and schedule another process.  That process will destroy us
     when it calls thread_schedule_tail(). */
  intr_disable ();
  if(thread_report_latency)
  msg("Thread <%s> completed in <%d> ticks.", thread_current()->name, timer_ticks() - thread_current()->latency_tick);
  list_remove (&thread_current()->allelem);
  thread_current ()->status = THREAD_DYING;
  schedule ();
  NOT_REACHED ();
}

/* Yields the CPU.  The current thread is not put to sleep and
   may be scheduled again immediately at the scheduler's whim. */
void
thread_yield (void) 
{
  struct thread *cur = thread_current ();
  enum intr_level old_level;
  
  ASSERT (!intr_context ());

  old_level = intr_disable ();
  if (cur != idle_thread) 
    list_push_back (&ready_list[cur->priority], &cur->elem); // ready_list[i]에는 priority가 i인 thread를 insert한다.
  cur->status = THREAD_READY;
  schedule ();
  intr_set_level (old_level);
}

/* thread가 idle한 thread가 아니라면 sleep_list에 insert하고 state를
   block state로 변경한다. 그리고 wakeup_tick에 ticks를 저장함으로써
   sleep된 tread가 어느 시점에 wake up 해야하는지를 기록한다. 탐색 효율
   을 위해 wakeup_tick들 중 최소값을 global tick에 저장한다. */
void
thread_sleep (int64_t ticks_to_wakeup)
{
    struct thread *cur = thread_current ();
    enum intr_level old_level;

    ASSERT(!intr_context());

    old_level = intr_disable();
    if (cur != idle_thread)
    {  
        save_global_tick (ticks_to_wakeup);
        cur->status = THREAD_BLOCKED;
        cur->wakeup_tick = ticks_to_wakeup;
        list_push_back (&sleep_list, &cur->elem);  
    }
    schedule ();
    intr_set_level (old_level);
}

/* thread들의 wake_up_tick들 중, 최소값을 global tick에 저장한다. */
void
save_global_tick (int64_t ticks)
{
    if (global_tick > ticks)
        global_tick = ticks;
}

 /* 현재 ticks가 global_tick보다 클 때 timer_interrupt에 의해 호출된다.
    (global_tick이 wakeup_tick의 최소값이므로 위와 같은 조건에서 반드시
    깨워야하는 thread가 존재하기 때문이다.)
    global_tick을 충분히 큰 값으로 초기화하고, sleep_list 안에 있는 thread
    들을 head부터 tail까지 탐색하며 wakeup_tick을 확인한다. wake up할 시간이
    되거나 지난 thread의 경우에는 sleep_list에서 thread를 제거하고, 
    ready state로 변경한 후, ready_list에 insert한다. 아직 wake up 할 때가
    아닌 thread의 경우에는 sleep_list에 남아있으므로 global_tick을 update하여
    wakeup_tick의 최소값을 재설정한다. */
void
thread_wakeup (int64_t cur_ticks)
{
    global_tick = INT64_MAX;

    struct thread *checking_thread;
    struct list_elem *checking_thread_elem; 
    
    for (checking_thread_elem = list_begin (&sleep_list); checking_thread_elem != list_tail (&sleep_list); checking_thread_elem = list_next (checking_thread_elem))
    {
      checking_thread = list_entry (checking_thread_elem, struct thread, elem);
      
      if (checking_thread->wakeup_tick <= cur_ticks)
      {
        checking_thread_elem->prev->next = checking_thread_elem->next;
        checking_thread_elem->next->prev = checking_thread_elem->prev;
        checking_thread_elem = checking_thread_elem->prev; 
        checking_thread->status = THREAD_READY;
        list_push_back (&ready_list[checking_thread->priority], &checking_thread->elem);
      }
      else
        save_global_tick (checking_thread->wakeup_tick);
    }
}

/* global_tick을 return한다. */
int64_t
return_global_tick (void)
{
    return global_tick;
}

/* list를 내림차순으로 정렬하기 위한 compare function. */
bool 
cmp_priority (const struct list_elem *a, const struct list_elem *b, void *aux)
{
  struct thread *a_thread = list_entry (a, struct thread, elem);
  struct thread *b_thread = list_entry (b, struct thread, elem); 

  if (a_thread->priority > b_thread->priority)
    return true;
  else
    return false;
}

/* donations list를 내림차순으로 정렬하기 위한 compare function. */
bool 
cmp_priority_for_d (const struct list_elem *a, const struct list_elem *b, void *aux)
{
  struct thread *a_thread = list_entry (a, struct thread, d_elem);
  struct thread *b_thread = list_entry (b, struct thread, d_elem); 

  if (a_thread->priority > b_thread->priority)
    return true;
  else
    return false;
}

/* 비어있지 않은 ready list들 중 가장 높은 priority에 대응되는 것을 찾고,
   해당 priority와 현재 thread의 priority를 비교하여 알맞게 thread_yield
   를 수행한다. */
void
cmp_cur_begin_priority (void)
{
  struct thread *cur = thread_current ();
  int i;
  for (i = PRI_MAX ; i >= 0 ; i--)
  {
    if (!list_empty(&ready_list[i]))
      break;
  }
  if (cur->priority < i)
    thread_yield ();
}

/* Invoke function 'func' on all threads, passing along 'aux'.
   This function must be called with interrupts off. */
void
thread_foreach (thread_action_func *func, void *aux)
{
  struct list_elem *e;

  ASSERT (intr_get_level () == INTR_OFF);

  for (e = list_begin (&all_list); e != list_end (&all_list);
       e = list_next (e))
    {
      struct thread *t = list_entry (e, struct thread, allelem);
      func (t, aux);
    }
}

/* Sets the current thread's priority to NEW_PRIORITY. */
void
thread_set_priority (int new_priority) 
{
  enum intr_level old_level;
  old_level = intr_disable ();
  struct thread *cur = thread_current ();
  struct thread *highest_donor;

  if (!thread_mlfqs)
  {
    cur-> original_priority = new_priority;

    /* 현재 priority를 변경했을 때, donations list에 있는 priority보다 작을 수
       있으므로 이러한 경우 priority donation을 다시 진행한다. */
    list_sort (&cur->donations, cmp_priority_for_d, NULL);
    highest_donor = list_entry (list_begin (&cur->donations), struct thread, d_elem);
    if (cur->original_priority < highest_donor->priority)
      cur->priority = highest_donor->priority;
    else
      cur->priority = cur->original_priority;

    /* 새로 설정된 priority가 ready_list의 head thread의 priority
     보다 작을 수 있으므로, cmp_cur_begin_priority를 수행한다. */
    cmp_cur_begin_priority ();
  }
  intr_set_level(old_level);
}

/* Advanced scheduling에서 priority를 계산하는 function. */
void
calculate_priority (struct thread *t)
{
  if (t != idle_thread)
  {
    t->priority = x_to_n_near (sub_xn (sub_xy (n_to_x(PRI_MAX), divide_xn (t->recent_cpu, 4)), t->nice * 2)); 
    
    if (t->priority < 0) 
      t->priority = 0;
    if (t->priority > PRI_MAX) 
      t->priority = PRI_MAX; 
    
    if (t->status == THREAD_READY)
    {
      list_remove (&t->elem);
      list_push_back (&ready_list[t->priority], &t->elem);
    }
  }
}

/* Advanced scheduling에서 recent_cpu를 계산하는 function. */
void
calculate_recent_cpu (struct thread *t)
{
  if (t != idle_thread)
    t->recent_cpu = add_xn (mult_xy (divide_xy (mult_xn (load_average, 2), add_xn (mult_xn (load_average, 2), 1)), t->recent_cpu), t->nice);
}

/* Advanced scheduling에서 load_average를 계산하는 function. */
void
calculate_load_average (void)
{
  struct thread *cur = thread_current ();
  int ready_threads = 0, i;
  
  for(i = 0 ; i <= PRI_MAX ; i++)
    ready_threads += list_size (&ready_list[i]);
  
  if (cur != idle_thread)
    ready_threads += 1;
  
  load_average = add_xy (divide_xy ( mult_xy (n_to_x (59), load_average), n_to_x (60)), divide_xy ( mult_xn (n_to_x (1), ready_threads), n_to_x (60))); 
}

/* Advanced scheduling에서 recent_cpu를 1만큼 증가시키는 function. */
void
increase_cpu (void)
{
  struct thread *cur = thread_current ();

  if (cur != idle_thread)
    cur->recent_cpu =add_xn (cur->recent_cpu, 1);
}

/* Advanced scheduling에서 모든 thread의 priority를 다시 계산하는 function. */
void
recalculate_priority (void)
{
  struct thread *t;
  struct list_elem *e;

  for (e = list_begin (&all_list); e != list_tail (&all_list); e = list_next (e))
  {
    t = list_entry (e, struct thread, allelem);
    calculate_priority (t);
  }
}

/* Advanced scheduling에서 모든 thread의 recent_cpu를 다시 계산하는 function. */
void
recalculate_recent_cpu (void)
{
  struct thread *t;
  struct list_elem *e;

  for (e = list_begin (&all_list); e != list_tail (&all_list); e = list_next (e))
  {
    t = list_entry (e, struct thread, allelem);
    calculate_recent_cpu (t);
  }
}

/* Returns the current thread's priority. */
int
thread_get_priority (void) 
{
  return thread_current ()->priority;
}

/* Sets the current thread's nice value to NICE. */
void
thread_set_nice (int nice UNUSED) 
{
  struct thread *cur = thread_current ();
  enum intr_level old_level;
  old_level = intr_disable ();
  cur->nice = nice;
  intr_set_level (old_level);
}

/* Returns the current thread's nice value. */
int
thread_get_nice (void) 
{
  struct thread *cur = thread_current ();
  enum intr_level old_level;
  old_level = intr_disable ();
  int nice = cur -> nice;
  intr_set_level (old_level);
  return nice;
}

/* Returns 100 times the system load average. */
int
thread_get_load_avg (void) 
{
  enum intr_level old_level;
  old_level = intr_disable ();
  int load_average_return = x_to_n_near (mult_xn (load_average, 100));
  intr_set_level (old_level);
  return load_average_return;
}

/* Returns 100 times the current thread's recent_cpu value. */
int
thread_get_recent_cpu (void) 
{
  struct thread *cur = thread_current ();
  enum intr_level old_level;
  old_level = intr_disable ();
  int recent_cpu = x_to_n_near (mult_xn (cur->recent_cpu, 100));
  intr_set_level (old_level);
  return recent_cpu;
} 


/* Idle thread.  Executes when no other thread is ready to run.

   The idle thread is initially put on the ready list by
   thread_start().  It will be scheduled once initially, at which
   point it initializes idle_thread, "up"s the semaphore passed
   to it to enable thread_start() to continue, and immediately
   blocks.  After that, the idle thread never appears in the
   ready list.  It is returned by next_thread_to_run() as a
   special case when the ready list is empty. */
static void
idle (void *idle_started_ UNUSED) 
{
  struct semaphore *idle_started = idle_started_;
  idle_thread = thread_current ();
  sema_up (idle_started);

  for (;;) 
    {
      /* Let someone else run. */
      intr_disable ();
      thread_block ();

      /* Re-enable interrupts and wait for the next one.

         The `sti' instruction disables interrupts until the
         completion of the next instruction, so these two
         instructions are executed atomically.  This atomicity is
         important; otherwise, an interrupt could be handled
         between re-enabling interrupts and waiting for the next
         one to occur, wasting as much as one clock tick worth of
         time.

         See [IA32-v2a] "HLT", [IA32-v2b] "STI", and [IA32-v3a]
         7.11.1 "HLT Instruction". */
      asm volatile ("sti; hlt" : : : "memory");
    }
}

/* Function used as the basis for a kernel thread. */
static void
kernel_thread (thread_func *function, void *aux) 
{
  ASSERT (function != NULL);

  intr_enable ();       /* The scheduler runs with interrupts off. */
  function (aux);       /* Execute the thread function. */
  thread_exit ();       /* If function() returns, kill the thread. */
}

/* Returns the running thread. */
struct thread *
running_thread (void) 
{
  uint32_t *esp;

  /* Copy the CPU's stack pointer into `esp', and then round that
     down to the start of a page.  Because `struct thread' is
     always at the beginning of a page and the stack pointer is
     somewhere in the middle, this locates the curent thread. */
  asm ("mov %%esp, %0" : "=g" (esp));
  return pg_round_down (esp);
}

/* Returns true if T appears to point to a valid thread. */
static bool
is_thread (struct thread *t)
{
  return t != NULL && t->magic == THREAD_MAGIC;
}

/* Does basic initialization of T as a blocked thread named
   NAME. */
static void
init_thread (struct thread *t, const char *name, int priority)
{
  enum intr_level old_level;

  ASSERT (t != NULL);
  ASSERT (PRI_MIN <= priority && priority <= PRI_MAX);
  ASSERT (name != NULL);

  memset (t, 0, sizeof *t);
  t->status = THREAD_BLOCKED;
  strlcpy (t->name, name, sizeof t->name);
  t->stack = (uint8_t *) t + PGSIZE;
  t->priority = priority;
  t->magic = THREAD_MAGIC;
  /* Priority donation을 위한 변수 초기화. */
  t->wait_on_lock = NULL; 
  list_init (&t->donations);
  t->original_priority = priority;
  /* Advanced scheduling을 위한 변수 초기화. */
  t->nice = 0;
  t->recent_cpu = 0;
  t->latency_tick = timer_ticks();
 
  old_level = intr_disable ();
  list_push_back (&all_list, &t->allelem);
  intr_set_level (old_level);
}

/* Allocates a SIZE-byte frame at the top of thread T's stack and
   returns a pointer to the frame's base. */
static void *
alloc_frame (struct thread *t, size_t size) 
{
  /* Stack data is always allocated in word-size units. */
  ASSERT (is_thread (t));
  ASSERT (size % sizeof (uint32_t) == 0);

  t->stack -= size;
  return t->stack;
}

/* Chooses and returns the next thread to be scheduled.  Should
   return a thread from the run queue, unless the run queue is
   empty.  (If the running thread can continue running, then it
   will be in the run queue.)  If the run queue is empty, return
   idle_thread. */
static struct thread *
next_thread_to_run (void) 
{
  int i;

  /* 비어있지 않은 ready list 중 가장 대응되는 priority가 높은 list를 찾고
     해당 list에서 가장 앞에 있는 thread를 다음 running thread로 선택한다. */
  for (i = PRI_MAX ; i >= 0 ; i--)
  {
    if (!list_empty (&ready_list[i]))
      break;
  }
  if (i < 0)
    return idle_thread;
  else
    return list_entry (list_pop_front (&ready_list[i]), struct thread, elem);
}

/* Completes a thread switch by activating the new thread's page
   tables, and, if the previous thread is dying, destroying it.

   At this function's invocation, we just switched from thread
   PREV, the new thread is already running, and interrupts are
   still disabled.  This function is normally invoked by
   thread_schedule() as its final action before returning, but
   the first time a thread is scheduled it is called by
   switch_entry() (see switch.S).

   It's not safe to call printf() until the thread switch is
   complete.  In practice that means that printf()s should be
   added at the end of the function.

   After this function and its caller returns, the thread switch
   is complete. */
void
thread_schedule_tail (struct thread *prev)
{
  struct thread *cur = running_thread ();
  
  ASSERT (intr_get_level () == INTR_OFF);

  /* Mark us as running. */
  cur->status = THREAD_RUNNING;

  /* Start new time slice. */
  thread_ticks = 0;

#ifdef USERPROG
  /* Activate the new address space. */
  process_activate ();
#endif

  /* If the thread we switched from is dying, destroy its struct
     thread.  This must happen late so that thread_exit() doesn't
     pull out the rug under itself.  (We don't free
     initial_thread because its memory was not obtained via
     palloc().) */
  if (prev != NULL && prev->status == THREAD_DYING && prev != initial_thread) 
    {
      ASSERT (prev != cur);
      palloc_free_page (prev);
    }
}

/* Schedules a new process.  At entry, interrupts must be off and
   the running process's state must have been changed from
   running to some other state.  This function finds another
   thread to run and switches to it.

   It's not safe to call printf() until thread_schedule_tail()
   has completed. */
static void
schedule (void) 
{
  struct thread *cur = running_thread ();
  struct thread *next = next_thread_to_run ();
  struct thread *prev = NULL;

  ASSERT (intr_get_level () == INTR_OFF);
  ASSERT (cur->status != THREAD_RUNNING);
  ASSERT (is_thread (next));

  if (cur != next)
    prev = switch_threads (cur, next);
  thread_schedule_tail (prev);
}

/* Returns a tid to use for a new thread. */
static tid_t
allocate_tid (void) 
{
  static tid_t next_tid = 1;
  tid_t tid;

  lock_acquire (&tid_lock);
  tid = next_tid++;
  lock_release (&tid_lock);

  return tid;
}

/* fixed point(17.14) number와 관련된 operations. */
int
n_to_x (int n)
{
  return n * f;
}

int
x_to_n_zero (int x)
{
  return x / f;
}

int
x_to_n_near (int x)
{
  if (x >= 0)
    return (x + f / 2) / f;
  else
    return (x - f / 2) / f;
}

int
add_xy (int x, int y)
{
  return x + y;
}

int
sub_xy (int x, int y)
{
  return x - y;
}

int
add_xn (int x, int n)
{
  return x + n * f;
}

int
sub_xn (int x, int n)
{
  return x - n * f;
}

int
mult_xy (int x, int y)
{
  return ((int64_t) x) * y / f;
}

int
mult_xn (int x, int n)
{
  return x * n;
}

int
divide_xy (int x, int y)
{
  return ((int64_t) x) * f / y;
}

int
divide_xn (int x, int n)
{
  return x / n;
}


/* Offset of `stack' member within `struct thread'.
   Used by switch.S, which can't figure it out on its own. */
uint32_t thread_stack_ofs = offsetof (struct thread, stack);
