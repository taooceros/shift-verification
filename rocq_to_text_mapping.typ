// One-to-One Mapping: Rocq Proofs to Paper Text
// This document provides exact correspondence between formal definitions and prose.

#set document(title: "Rocq-to-Text Mapping for SHIFT Proofs")
#set page(margin: 1.5cm, numbering: "1")
#set text(font: "New Computer Modern", size: 9pt)
#set heading(numbering: "1.1")
#set raw(theme: none)

#let rocq(code) = {
  block(
    fill: rgb("#f8f8f8"),
    stroke: 0.5pt + rgb("#ddd"),
    inset: 8pt,
    radius: 3pt,
    width: 100%,
    raw(code, lang: "coq")
  )
}

#let prose(body) = {
  block(
    stroke: (left: 3pt + rgb("#4a90d9")),
    inset: (left: 10pt, y: 6pt),
    body
  )
}

#let proofstep(tactic, expl) = {
  grid(
    columns: (1fr, 1fr),
    column-gutter: 8pt,
    raw(tactic, lang: "coq"),
    text(fill: rgb("#555"), size: 8pt)[#expl],
  )
}

#let annotated-proof(..steps) = {
  block(
    fill: rgb("#f0f4f8"),
    stroke: 0.5pt + rgb("#ccd"),
    inset: 8pt,
    radius: 3pt,
    width: 100%,
    [
      #text(weight: "bold", size: 8pt)[Line-by-line proof annotation:]
      #v(4pt)
      #table(
        columns: (auto, 1fr),
        inset: 4pt,
        stroke: (x: none, y: 0.3pt + rgb("#ddd")),
        align: (left, left),
        ..steps.pos().map(((t, e)) => (raw(t, lang: "coq"), text(size: 8pt)[#e])).flatten()
      )
    ]
  )
}

#let mapping(rocq_name, file, line, text_desc) = {
  block(
    inset: (y: 4pt),
    [
      #text(weight: "bold", size: 10pt)[`#rocq_name`] #h(1fr) #text(fill: gray, size: 8pt)[#file:#line]
      #v(2pt)
      #text(fill: rgb("#333"))[#text_desc]
    ]
  )
}

= Rocq-to-Text Mapping: SHIFT Impossibility Proofs

This document provides exact correspondence between Rocq definitions/theorems and their textual descriptions for paper integration.

#line(length: 100%, stroke: 0.5pt)

= Core Definitions (`Core/`)

== Memory Model (`Core/Memory.v`)

#mapping("Addr", "Memory.v", "11", [Memory addresses, modeled as natural numbers.])
#rocq("Definition Addr := nat.")
#prose[An _address_ $a in NN$ identifies a location in RDMA-accessible memory.]

#mapping("Val", "Memory.v", "14", [Values stored in memory, modeled as natural numbers.])
#rocq("Definition Val := nat.")
#prose[A _value_ $v in NN$ represents data stored at a memory address.]

#mapping("Memory", "Memory.v", "22", [Memory as a total function from addresses to values.])
#rocq("Definition Memory := Addr -> Val.")
#prose[_Memory_ is a function $m : "Addr" -> "Val"$ mapping each address to its current value.]

#mapping("init_memory", "Memory.v", "25", [Initial memory state where all addresses contain 0.])
#rocq("Definition init_memory : Memory := fun _ => 0.")
#prose[The _initial memory_ $m_0$ satisfies $m_0(a) = 0$ for all addresses $a$.]

#mapping("mem_read", "Memory.v", "28", [Read operation: returns value at address.])
#rocq("Definition mem_read (m : Memory) (a : Addr) : Val := m a.")
#prose[A _read_ of address $a$ in memory $m$ returns $m(a)$.]

#mapping("mem_write", "Memory.v", "31-32", [Write operation: creates new memory with updated value.])
#rocq("Definition mem_write (m : Memory) (a : Addr) (v : Val) : Memory :=
  fun a' => if Nat.eqb a' a then v else m a'.")
#prose[A _write_ of value $v$ to address $a$ produces memory $m'$ where $m'(a) = v$ and $m'(a') = m(a')$ for $a' != a$.]

#line(length: 100%, stroke: 0.5pt)

== RDMA Operations (`Core/Operations.v`)

#mapping("Op", "Operations.v", "12-16", [RDMA operation types.])
#rocq("Inductive Op : Type :=
  | OpWrite : Addr -> Val -> Op       (* RDMA Write *)
  | OpRead : Addr -> Op               (* RDMA Read *)
  | OpFADD : Addr -> nat -> Op        (* Fetch-and-Add *)
  | OpCAS : Addr -> Val -> Val -> Op. (* Compare-and-Swap *)")
#prose[An _RDMA operation_ is one of:
- $"Write"(a, v)$: write value $v$ to address $a$
- $"Read"(a)$: read value at address $a$
- $"FADD"(a, delta)$: atomically add $delta$ to address $a$, return old value
- $"CAS"(a, "exp", "new")$: if $m(a) = "exp"$, write $"new"$; return (success, old value)]

#mapping("OpResult", "Operations.v", "20-24", [Results returned by operations.])
#rocq("Inductive OpResult : Type :=
  | ResWriteAck : OpResult
  | ResReadVal : Val -> OpResult
  | ResFADDVal : Val -> OpResult
  | ResCASResult : bool -> Val -> OpResult.")
#prose[An _operation result_ is the value returned to the sender:
- Write returns acknowledgment
- Read returns the value read
- FADD returns the old value before addition
- CAS returns (success flag, old value)]

#mapping("exec_fadd", "Operations.v", "37-40", [FADD execution semantics.])
#rocq("Definition exec_fadd (m : Memory) (a : Addr) (delta : nat) : Memory * OpResult :=
  let old_val := mem_read m a in
  let new_val := old_val + delta in
  (mem_write m a new_val, ResFADDVal old_val).")
#prose[$"exec"_"FADD"(m, a, delta)$ atomically:
1. Reads $v_"old" = m(a)$
2. Writes $m(a) := v_"old" + delta$
3. Returns $v_"old"$]

#mapping("exec_cas", "Operations.v", "43-48", [CAS execution semantics.])
#rocq("Definition exec_cas (m : Memory) (a : Addr) (expected new_val : Val) : Memory * OpResult :=
  let old_val := mem_read m a in
  if Nat.eqb old_val expected then
    (mem_write m a new_val, ResCASResult true old_val)
  else
    (m, ResCASResult false old_val).")
#prose[$"exec"_"CAS"(m, a, "exp", "new")$ atomically:
1. Reads $v_"old" = m(a)$
2. If $v_"old" = "exp"$: writes $m(a) := "new"$, returns $(sans("true"), v_"old")$
3. Else: memory unchanged, returns $(sans("false"), v_"old")$]

#mapping("exec_write", "Operations.v", "29-30", [Write execution semantics.])
#rocq("Definition exec_write (m : Memory) (a : Addr) (v : Val) : Memory * OpResult :=
  (mem_write m a v, ResWriteAck).")
#prose[$"exec"_"Write"(m, a, v)$ writes value $v$ to address $a$ and returns `ResWriteAck`. No informational return value.]

#mapping("exec_read", "Operations.v", "33-34", [Read execution semantics.])
#rocq("Definition exec_read (m : Memory) (a : Addr) : Memory * OpResult :=
  (m, ResReadVal (mem_read m a)).")
#prose[$"exec"_"Read"(m, a)$ returns the current value $m(a)$ without modifying memory.]

#mapping("exec_op", "Operations.v", "51-57", [General operation dispatch.])
#rocq("Definition exec_op (m : Memory) (op : Op) : Memory * OpResult :=
  match op with
  | OpWrite a v => exec_write m a v
  | OpRead a => exec_read m a
  | OpFADD a delta => exec_fadd m a delta
  | OpCAS a exp new_v => exec_cas m a exp new_v
  end.")
#prose[$"exec"_"op"$ dispatches to the appropriate execution function based on the operation type.]

#mapping("write_idempotent", "Operations.v", "62-66", [Write operations are idempotent.])
#rocq("Lemma write_idempotent : forall m a v,
  fst (exec_write (fst (exec_write m a v)) a v) = fst (exec_write m a v).")
#prose[*Lemma (Write Idempotency):* For any memory $m$, address $a$, and value $v$: executing $"Write"(a,v)$ twice produces the same memory state as executing it once.]

#mapping("fadd_not_idempotent", "Operations.v", "69-92", [FADD is not idempotent when delta != 0.])
#rocq("Lemma fadd_not_idempotent : forall m a delta,
  delta <> 0 ->
  fst (exec_fadd (fst (exec_fadd m a delta)) a delta) <> fst (exec_fadd m a delta).")
#prose[*Lemma (FADD Non-Idempotency):* For $delta != 0$: executing $"FADD"(a, delta)$ twice yields $m(a) = v_"old" + 2 delta$, not $v_"old" + delta$. Therefore FADD is not idempotent.]

#line(length: 100%, stroke: 0.5pt)

== Execution Traces (`Core/Traces.v`)

#mapping("Event", "Traces.v", "12-28", [Events in a distributed execution.])
#rocq("Inductive Event : Type :=
  | EvSend : Op -> Event              (* Sender posts operation *)
  | EvTimeout : Op -> Event           (* Sender observes timeout *)
  | EvCompletion : Op -> OpResult -> Event
  | EvPacketLost : Op -> Event        (* Packet lost in network *)
  | EvAckLost : Op -> Event           (* ACK lost in network *)
  | EvReceive : Op -> Event           (* Receiver gets packet *)
  | EvExecute : Op -> OpResult -> Event
  | EvAppConsume : Addr -> Val -> Event
  | EvAppReuse : Addr -> Val -> Event.")
#prose[An _event_ records an occurrence in the distributed system:
- *Sender-side*: Send, Completion, Timeout
- *Network*: PacketLost, AckLost
- *Receiver-side*: Receive, Execute
- *Application*: Consume (read data), Reuse (overwrite buffer)]

#mapping("Trace", "Traces.v", "31", [A trace is a sequence of events.])
#rocq("Definition Trace := list Event.")
#prose[A _trace_ $cal(T)$ is a sequence of events representing one possible execution.]

#mapping("SenderObs", "Traces.v", "36-39", [What the sender can observe.])
#rocq("Inductive SenderObs : Type :=
  | ObsSent : Op -> SenderObs
  | ObsCompleted : Op -> OpResult -> SenderObs
  | ObsTimeout : Op -> SenderObs.")
#prose[A _sender observation_ is one of: operation sent, completion received, or timeout. The sender *cannot* observe network events (PacketLost, AckLost) or receiver events (Execute).]

#mapping("sender_view", "Traces.v", "42-49", [Projection to sender-observable events.])
#rocq("Fixpoint sender_view (t : Trace) : list SenderObs :=
  match t with
  | [] => []
  | EvSend op :: rest => ObsSent op :: sender_view rest
  | EvCompletion op res :: rest => ObsCompleted op res :: sender_view rest
  | EvTimeout op :: rest => ObsTimeout op :: sender_view rest
  | _ :: rest => sender_view rest  (* Cannot observe! *)
  end.")
#prose[The _sender view_ $sigma(cal(T))$ projects a trace to only sender-observable events. This is the *central abstraction*: the sender's decision can only depend on $sigma(cal(T))$.]

#mapping("sender_indistinguishable", "Traces.v", "54-55", [Two traces with identical sender views.])
#rocq("Definition sender_indistinguishable (t1 t2 : Trace) : Prop :=
  sender_view t1 = sender_view t2.")
#prose[Traces $cal(T)_1$ and $cal(T)_2$ are _sender-indistinguishable_ if $sigma(cal(T)_1) = sigma(cal(T)_2)$.]

#mapping("op_executed", "Traces.v", "66-67", [Operation was executed at receiver.])
#rocq("Definition op_executed (t : Trace) (op : Op) : Prop :=
  exists res, In (EvExecute op res) t.")
#prose[Operation $"op"$ was _executed_ in trace $cal(T)$ if $"EvExecute"("op", r) in cal(T)$ for some result $r$.]

#mapping("sender_saw_timeout", "Traces.v", "74-75", [Sender observed timeout for operation.])
#rocq("Definition sender_saw_timeout (t : Trace) (op : Op) : Prop :=
  In (EvTimeout op) t.")
#prose[The sender _saw timeout_ for operation $"op"$ if $"EvTimeout"("op") in cal(T)$.]

#mapping("memory_after_events", "Traces.v", "80-89", [Memory state after executing events.])
#rocq("Fixpoint memory_after_events (m : Memory) (events : list Event) : Memory :=
  match events with
  | [] => m
  | EvExecute op _ :: rest =>
      let (m', _) := exec_op m op in
      memory_after_events m' rest
  | EvAppReuse a v :: rest =>
      memory_after_events (mem_write m a v) rest
  | _ :: rest => memory_after_events m rest
  end.")
#prose[Compute the memory state after a sequence of events. Only `EvExecute` (applying `exec_op`) and `EvAppReuse` (writing a new value) modify memory. Other events (sends, receives, losses, timeouts) leave memory unchanged.]

#mapping("final_memory (Traces)", "Traces.v", "92-93", [Memory state at end of trace.])
#rocq("Definition final_memory (t : Trace) : Memory :=
  memory_after_events init_memory t.")
#prose[The _final memory_ of a trace is the result of executing all events starting from `init_memory`.]

#line(length: 100%, stroke: 0.5pt)

== Overlay Properties (`Core/Properties.v`)

#mapping("Overlay", "Properties.v", "109", [An overlay decision function.])
#rocq("Definition Overlay := Trace -> Op -> bool.")
#prose[An _overlay_ is a function $O : cal(T) times "Op" -> {"retransmit", "skip"}$ that can observe the full trace to make retransmission decisions.]

#mapping("IsTransparent", "Properties.v", "114-117", [Transparency constraint on overlays.])
#rocq("Definition IsTransparent (overlay : Overlay) : Prop :=
  forall t1 t2 op,
    sender_view t1 = sender_view t2 ->
    overlay t1 op = overlay t2 op.")
#prose[An overlay is _transparent_ if its decision depends *only* on the sender view: whenever two traces have identical sender views ($sigma(cal(T)_1) = sigma(cal(T)_2)$), the overlay must make the same retransmission decision. This is the key constraint — the overlay cannot use information beyond what the sender observes.]

#mapping("TransparentOverlay", "Properties.v", "120-123", [A transparent failover mechanism.])
#rocq("Record TransparentOverlay := {
  decide_retransmit : Overlay;
  transparency : IsTransparent decide_retransmit;
}.")
#prose[A _transparent overlay_ bundles an overlay function with a proof of its transparency. The `transparency` field witnesses that the overlay's decisions depend only on `sender_view`.]

#mapping("execution_count", "Properties.v", "70-76", [Count executions of an operation.])
#rocq("Fixpoint execution_count (t : Trace) (op : Op) : nat :=
  match t with
  | [] => 0
  | EvExecute op' _ :: rest =>
      (if op_eq op op' then 1 else 0) + execution_count rest op
  | _ :: rest => execution_count rest op
  end.")
#prose[$"count"(cal(T), "op")$ counts how many times operation $"op"$ was executed in trace $cal(T)$.]

#mapping("AtMostOnce", "Properties.v", "79-80", [At-most-once execution semantics.])
#rocq("Definition AtMostOnce (t : Trace) : Prop :=
  forall op, execution_count t op <= 1.")
#prose[A trace satisfies _at-most-once_ if every operation executes at most once.]

#pagebreak()

= Theorem 1: Indistinguishability (`Theorem1/`)

== Protocol Parameters (`Theorem1/Indistinguishability.v`)

#mapping("W_D", "Indistinguishability.v", "22", [Data write operation constructor.])
#rocq("Definition W_D (v : Val) : Op := OpWrite A_data v.")
#prose[$W_D(v)$: an RDMA Write of value $v$ to the data address `A_data`.]

#mapping("W_F", "Indistinguishability.v", "25", [Flag write operation.])
#rocq("Definition W_F : Op := OpWrite A_flag 1.")
#prose[$W_F$: an RDMA Write of value 1 to the flag address `A_flag`, signaling data is ready.]

== Trace Construction (`Theorem1/Indistinguishability.v`)

#mapping("T1_packet_loss", "Indistinguishability.v", "32-36", [Trace where packet is lost.])
#rocq("Definition T1_packet_loss (V1 : Val) : Trace :=
  [ EvSend (W_D V1);
    EvPacketLost (W_D V1);
    EvTimeout (W_D V1) ].")
#prose[$cal(T)_1$ (Packet Loss): Sender posts write, packet lost in network, sender times out. Operation *not executed*. Correct action: *retransmit*.]

#mapping("T2_ack_loss", "Indistinguishability.v", "44-55", [Trace where ACK is lost but operation executed.])
#rocq("Definition T2_ack_loss (V1 V_new : Val) : Trace :=
  [ EvSend (W_D V1);
    EvReceive (W_D V1);
    EvExecute (W_D V1) ResWriteAck;
    EvSend W_F; EvReceive W_F; EvExecute W_F ResWriteAck;
    EvAppConsume A_data V1;
    EvAppReuse A_data V_new;
    EvAckLost (W_D V1);
    EvTimeout (W_D V1) ].")
#prose[$cal(T)_2$ (ACK Loss): Sender posts write, receiver executes it, flag set, app consumes data and reuses buffer with new value $V'$, ACK lost, sender times out. Operation *was executed*. Correct action: *do not retransmit* (would corrupt $V'$).]

#mapping("indistinguishable_wrt_WD_execution", "Indistinguishability.v", "77-101", [Key lemma: same sender view, different execution status.])
#rocq("Lemma indistinguishable_wrt_WD_execution : forall V1 V_new,
  sender_saw_timeout (T1_packet_loss V1) (W_D V1) /\\
  sender_saw_timeout (T2_ack_loss V1 V_new) (W_D V1) /\\
  ~ op_executed (T1_packet_loss V1) (W_D V1) /\\
  op_executed (T2_ack_loss V1 V_new) (W_D V1).")
#prose[*Lemma (Indistinguishability):* Both traces produce timeout observation. $cal(T)_1$: operation not executed. $cal(T)_2$: operation executed. The sender view is *identical* but execution status *differs*.]

== Main Impossibility (`Theorem1/Impossibility.v`)

#mapping("ProvidesSafety", "Impossibility.v", "65-71", [Safety: no ghost writes.])
#rocq("Definition ProvidesSafety (overlay : TransparentOverlay) : Prop :=
  forall t op V_new,
    In (EvAppReuse A_data V_new) t ->
    op_executed t op ->
    overlay.(decide_retransmit) t op = false.")
#prose[_Safety_: If operation was executed and memory was reused, the overlay must *not* retransmit (to avoid overwriting new data). Note: `decide_retransmit` takes the full trace `t`, but the `transparency` proof ensures the decision depends only on `sender_view t`.]

#mapping("ProvidesLiveness", "Impossibility.v", "76-83", [Liveness: lost packets retransmitted.])
#rocq("Definition ProvidesLiveness (overlay : TransparentOverlay) : Prop :=
  forall t op,
    In (EvSend op) t ->
    ~ op_executed t op ->
    sender_saw_timeout t op ->
    overlay.(decide_retransmit) t op = true.")
#prose[_Liveness_: If operation was sent but not executed (packet lost), and sender timed out, the overlay *must* retransmit.]

#mapping("Transparent", "Impossibility.v", "48-52", [Transparency constraint on overlay.])
#rocq("Definition Transparent (overlay : TransparentOverlay) : Prop :=
  IsTransparent overlay.(decide_retransmit).")
#prose[_Transparency_: if two traces have identical sender views, the overlay must make the same retransmission decision. This is now defined as `IsTransparent` applied to the overlay's decision function, ensuring the overlay cannot use information beyond `sender_view`.]

#mapping("SilentReceiver", "Impossibility.v", "27-29", [No application-level ACKs.])
#rocq("Definition SilentReceiver : Prop :=
  forall t : Trace, forall e : Event,
    In e t -> ~ AppAckEvent e.")
#prose[_Silent receiver_: the protocol does not generate application-level acknowledgments. The sender learns nothing beyond transport-level signals.]

#mapping("MemoryReuseAllowed", "Impossibility.v", "42-45", [Application may reuse memory after consuming.])
#rocq("Definition MemoryReuseAllowed : Prop :=
  forall V1 V_new, exists t,
    In (EvAppConsume A_data V1) t /\\ In (EvAppReuse A_data V_new) t.")
#prose[_Memory reuse_: after consuming data, the application may immediately overwrite the buffer with new data $V'$.]

#mapping("T1_concrete", "Impossibility.v", "112-115", [Concrete packet-loss trace.])
#rocq("Definition T1_concrete : Trace :=
  [ EvSend op; EvPacketLost op; EvTimeout op ].")
#prose[$cal(T)_1$: sender sends `op`, packet is lost, sender times out. Operation *not executed*.]

#mapping("T2_concrete", "Impossibility.v", "124-130", [Concrete ACK-loss trace with memory reuse.])
#rocq("Definition T2_concrete : Trace :=
  [ EvSend op; EvReceive op; EvExecute op ResWriteAck;
    EvAppReuse A_data V_new; EvAckLost op; EvTimeout op ].")
#prose[$cal(T)_2$: sender sends `op`, receiver executes it, app reuses memory, ACK lost, sender times out. Operation *was executed*.]

#mapping("T1_has_send", "Impossibility.v", "167-170", [T1 contains a send event.])
#rocq("Lemma T1_has_send : In (EvSend op) T1_concrete.")
#prose[The packet-loss trace $cal(T)_1$ contains `EvSend op`.]

#mapping("T1_not_executed", "Impossibility.v", "140-149", [T1 does not execute the operation.])
#rocq("Lemma T1_not_executed : ~ op_executed T1_concrete op.")
#prose[$cal(T)_1$ has no `EvExecute` event for `op` — the operation was *not* executed (packet was lost before reaching receiver).]

#mapping("T1_has_timeout", "Impossibility.v", "160-164", [T1 contains a timeout.])
#rocq("Lemma T1_has_timeout : sender_saw_timeout T1_concrete op.")
#prose[$cal(T)_1$ contains `EvTimeout op` — the sender observed a timeout.]

#mapping("T2_executed", "Impossibility.v", "152-157", [T2 executes the operation.])
#rocq("Lemma T2_executed : op_executed T2_concrete op.")
#prose[$cal(T)_2$ contains `EvExecute op ResWriteAck` — the operation *was* executed at the receiver.]

#mapping("T2_has_reuse", "Impossibility.v", "173-177", [T2 contains memory reuse.])
#rocq("Lemma T2_has_reuse : In (EvAppReuse A_data V_new) T2_concrete.")
#prose[$cal(T)_2$ contains `EvAppReuse A_data V_new` — the application has reused the memory buffer with new data $V'$.]

#mapping("sender_views_equal", "Impossibility.v", "133-137", [Both traces have identical sender view.])
#rocq("Lemma sender_views_equal :
  sender_view T1_concrete = sender_view T2_concrete.
Proof. unfold T1_concrete, T2_concrete. simpl. reflexivity. Qed.")
#prose[*Lemma:* $sigma(cal(T)_1) = sigma(cal(T)_2) = ["ObsSent"(W_D), "ObsTimeout"(W_D)]$.]
#annotated-proof(
  ("unfold T1_concrete, T2_concrete.", [*Initial state* — _Context:_ (section variables `V1`, `V_new : Val`, `op := OpWrite A_data V1`). _Goal:_ `sender_view T1_concrete = sender_view T2_concrete`. \
  Inline the definitions of both concrete traces. _Goal becomes:_ `sender_view [EvSend op; EvPacketLost op; EvTimeout op] = sender_view [EvSend op; EvReceive op; EvExecute op ResWriteAck; EvAppReuse A_data V_new; EvAckLost op; EvTimeout op]`.]),
  ("simpl.", [Compute `sender_view` on each list: the fixpoint filters out non-sender events (`EvPacketLost`, `EvReceive`, `EvExecute`, `EvAppReuse`, `EvAckLost`), keeping only `EvSend` $->$ `ObsSent` and `EvTimeout` $->$ `ObsTimeout`. _Goal becomes:_ `[ObsSent op; ObsTimeout op] = [ObsSent op; ObsTimeout op]`.]),
  ("reflexivity.", [The two sides are syntactically identical. Rocq's definitional equality closes the goal. _No goals remaining._]),
)

#mapping("impossibility_safe_retransmission", "Impossibility.v", "175-229", [*THEOREM 1*: No transparent overlay provides both safety and liveness.])
#rocq("Theorem impossibility_safe_retransmission :
  forall overlay : TransparentOverlay,
    Transparent overlay ->
    SilentReceiver -> MemoryReuseAllowed ->
    ~ (ProvidesSafety overlay /\\ ProvidesLiveness overlay).
Proof.
  intros overlay Htrans Hsilent Hreuse [Hsafe Hlive].
  pose (V1 := 1). pose (V_new := 2).
  pose (the_op := OpWrite A_data V1).
  pose (t1 := T1_concrete V1). pose (t2 := T2_concrete V1 V_new).
  assert (Hlive_T1 : overlay.(decide_retransmit) t1 the_op = true).
  { apply (Hlive ...). apply T1_has_send. apply T1_not_executed. apply T1_has_timeout. }
  assert (Hsafe_T2 : overlay.(decide_retransmit) t2 the_op = false).
  { apply (Hsafe ...). apply T2_has_reuse. apply T2_executed. }
  assert (Hviews_eq : sender_view t1 = sender_view t2).
  { apply sender_views_equal. }
  assert (Hdec_eq : overlay.(decide_retransmit) t1 the_op =
                    overlay.(decide_retransmit) t2 the_op).
  { apply Htrans. exact Hviews_eq. }
  rewrite Hlive_T1 in Hdec_eq. rewrite Hsafe_T2 in Hdec_eq.
  discriminate.
Qed.")
#prose[*Theorem 1 (Impossibility of Safe Retransmission):* Under transparency, no overlay can provide both safety and liveness.]
#annotated-proof(
  ("intros overlay Htrans Hsilent Hreuse [Hsafe Hlive].", [*Initial state* — _Goal:_ `forall overlay, Transparent overlay -> SilentReceiver -> ... -> ~ (ProvidesSafety overlay /\\ ProvidesLiveness overlay)`. \
  Introduce all hypotheses. The `~` unfolds to `... -> False`. The final `[Hsafe Hlive]` destructs the conjunction. _Context:_ `overlay : TransparentOverlay`, `Htrans : Transparent overlay`, `Hsilent : SilentReceiver`, `Hreuse : MemoryReuseAllowed`, `Hsafe : ProvidesSafety overlay`, `Hlive : ProvidesLiveness overlay`. _Goal:_ `False`.]),
  ("pose (V1 := 1). pose (V_new := 2).", [Bind concrete values. _Context adds:_ `V1 := 1 : nat`, `V_new := 2 : nat`. _Goal:_ `False` (unchanged).]),
  ("pose (the_op := OpWrite A_data V1).", [_Context adds:_ `the_op := OpWrite A_data 1 : Op`. _Goal:_ `False`.]),
  ("pose (t1 := T1_concrete V1).", [_Context adds:_ `t1 := T1_concrete 1 : Trace` (the packet-loss trace). _Goal:_ `False`.]),
  ("pose (t2 := T2_concrete V1 V_new).", [_Context adds:_ `t2 := T2_concrete 1 2 : Trace` (the ACK-loss + reuse trace). _Goal:_ `False`.]),
  ("assert (Hlive_T1 : ... = true). { apply Hlive ... }", [Establishes `Hlive_T1 : decide_retransmit overlay t1 the_op = true`. The sub-proof applies `Hlive` (liveness) to $cal(T)_1$: sent (`T1_has_send`), not executed (`T1_not_executed`), timed out (`T1_has_timeout`), so the overlay must retransmit. Note: `decide_retransmit` now takes the trace directly. _Goal:_ `False` (unchanged after assert is discharged).]),
  ("assert (Hsafe_T2 : ... = false). { apply Hsafe ... }", [Establishes `Hsafe_T2 : decide_retransmit overlay t2 the_op = false`. The sub-proof applies `Hsafe` (safety) to $cal(T)_2$: memory reused (`T2_has_reuse`), operation executed (`T2_executed`), so the overlay must not retransmit. _Goal:_ `False`.]),
  ("assert (Hviews_eq : sender_view t1 = sender_view t2).", [Establishes `Hviews_eq : sender_view t1 = sender_view t2` via `sender_views_equal`. Both traces yield `[ObsSent op; ObsTimeout op]`. _Goal:_ `False`.]),
  ("assert (Hdec_eq : ...). { apply Htrans. exact Hviews_eq. }", [Establishes `Hdec_eq : decide_retransmit overlay t1 the_op = decide_retransmit overlay t2 the_op` by applying `Htrans` (transparency): `Htrans` is `IsTransparent decide_retransmit`, so identical sender views $=>$ identical decisions even though the traces differ. _Goal:_ `False`.]),
  ("rewrite Hlive_T1 in Hdec_eq.", [Substitute the LHS of `Hdec_eq` using `Hlive_T1`. _`Hdec_eq` becomes:_ `true = decide_retransmit overlay t2 the_op`. _Goal:_ `False`.]),
  ("rewrite Hsafe_T2 in Hdec_eq.", [Substitute the RHS using `Hsafe_T2`. _`Hdec_eq` becomes:_ `true = false`. _Goal:_ `False`.]),
  ("discriminate.", [`true` and `false` are distinct constructors of `bool`. `discriminate` derives `False` from `true = false`. _No goals remaining._]),
)

#pagebreak()

= Theorem 2: Non-Idempotency (`Theorem2/`)

== Idempotency Definition (`Theorem2/Atomics.v`)

#mapping("Idempotent", "Atomics.v", "26-29", [Formal definition of idempotency.])
#rocq("Definition Idempotent (op : Op) (m : Memory) : Prop :=
  let (m1, r1) := exec_op m op in
  let (m2, r2) := exec_op m1 op in
  m1 = m2 /\\ r1 = r2.")
#prose[Operation $"op"$ is _idempotent_ on memory $m$ iff executing twice yields:
1. Same memory state: $m_1 = m_2$
2. Same result: $r_1 = r_2$]

#mapping("fadd_non_idempotent", "Atomics.v", "33-70", [*THEOREM 2a*: FADD is not idempotent.])
#rocq("Theorem fadd_non_idempotent : forall a delta m,
  delta > 0 -> ~ Idempotent (OpFADD a delta) m.")
#prose[*Theorem 2a (FADD Non-Idempotency):* For $delta > 0$, $"FADD"(a, delta)$ is not idempotent.

*Proof:* Let $m(a) = v$. After one FADD: $m_1(a) = v + delta$. After retry: $m_2(a) = v + 2 delta$. Since $delta > 0$: $v + delta != v + 2 delta$. $square$]

#mapping("cas_idempotent_iff", "Atomics.v", "75-110", [CAS idempotency characterization.])
#rocq("Theorem cas_idempotent_iff : forall a expected new_val m,
  Idempotent (OpCAS a expected new_val) m <->
  (mem_read m a <> expected \\/ expected = new_val).")
#prose[*Theorem:* CAS is idempotent iff either:
1. It fails (current value $!=$ expected), OR
2. $"expected" = "new_val"$ (no actual change)

Otherwise (successful CAS with actual change): *not idempotent*.]

== FADD Retry (`Theorem2/FADD.v`)

#mapping("single_fadd_value", "FADD.v", "35-40", [Value after one FADD.])
#rocq("Lemma single_fadd_value :
  mem_read state_after_one target_addr = delta.")
#prose[After one $"FADD"(a, delta)$ from initial state: $m(a) = delta$.]

#mapping("double_fadd_value", "FADD.v", "42-50", [Value after two FADDs.])
#rocq("Lemma double_fadd_value :
  mem_read state_after_two target_addr = 2 * delta.")
#prose[After retry (two FADDs): $m(a) = 2 delta$.]

#mapping("fadd_retry_state_corruption", "FADD.v", "59-65", [FADD retry corrupts state.])
#rocq("Theorem fadd_retry_state_corruption :
  mem_read state_after_two target_addr <> mem_read state_after_one target_addr.")
#prose[*Theorem:* FADD retry produces incorrect state: $2 delta != delta$ when $delta > 0$.]

== CAS Concurrent Scenario (`Theorem2/CAS.v`)

#mapping("cas_double_success", "CAS.v", "106-113", [*THEOREM 2b*: CAS can succeed twice.])
#rocq("Theorem cas_double_success :
  result_1 = ResCASResult true 0 /\\
  result_3 = ResCASResult true 0.")
#prose[*Theorem 2b (CAS Double Success):* Under concurrent modification, a CAS retry can succeed even after the original succeeded (ABA problem).

*Construction:*
1. $S."CAS"(0 -> 1)$ succeeds, $m(a) = 1$
2. Concurrent $P."CAS"(1 -> 0)$ succeeds, $m(a) = 0$
3. $S$ retries $"CAS"(0 -> 1)$: *succeeds again!*

Single logical CAS executed twice. $P$'s modification silently overwritten.]

== Combined Result (`Theorem2/Atomics.v`)

#mapping("no_transparent_overlay_non_idempotent", "Atomics.v", "328-355", [No transparent overlay for non-idempotent ops.])
#rocq("Theorem no_transparent_overlay_non_idempotent :
  IndistinguishableExecutionStatus ->
  forall (overlay : TransparentOverlay) (op : Op) (m : Memory),
    ~ Idempotent op m ->
    ~ (LiveRetransmit overlay /\\
       (forall t, op_executed t op -> overlay.(decide_retransmit) t op = false)).")
#prose[*Theorem (Combined):* Given indistinguishable execution status (Theorem 1) and non-idempotency (Theorem 2), no transparent overlay can provide both liveness (retry on packet loss) and safety (no retry after execution). Note: `decide_retransmit` now takes the trace directly; the transparency proof (in the `TransparentOverlay` record) ensures decisions depend only on `sender_view`.]

#mapping("no_transparent_overlay_atomics", "Atomics.v", "358-387", [Corollary for atomic operations.])
#rocq("Corollary no_transparent_overlay_atomics :
  IndistinguishableExecutionStatus ->
  forall (overlay : TransparentOverlay),
    (forall a delta, delta > 0 ->
      ~ (LiveRetransmit overlay /\\
         (forall t, op_executed t (OpFADD a delta) ->
           overlay.(decide_retransmit) t (OpFADD a delta) = false))) /\\
    (forall a expected new_val, ... ->
      ~ (LiveRetransmit overlay /\\
         (forall t, op_executed t (OpCAS a expected new_val) ->
           overlay.(decide_retransmit) t (OpCAS a expected new_val) = false))).")
#prose[*Corollary:* No transparent overlay supports FADD (with $delta > 0$) or successful CAS (with $"exp" != "new"$). The inline safety condition requires that the overlay not retransmit when the operation has been executed.]

#pagebreak()

= Theorem 3: Consensus Hierarchy (`Theorem3/`)

== Consensus Framework (`Theorem3/ConsensusNumber.v`)

#mapping("before_process", "ConsensusNumber.v", "85-89", [Processes that executed before a given process.])
#rocq("Fixpoint before_process (exec : list nat) (i : nat) : list nat :=
  match exec with
  | [] => []
  | x :: xs => if Nat.eqb x i then [] else x :: before_process xs i
  end.")
#prose[`before_process exec i` returns the list of processes that executed before process $i$ in execution order `exec`. Scans the list until finding $i$, collecting all predecessors.]

#mapping("winner", "ConsensusNumber.v", "91", [First process to execute.])
#rocq("Definition winner (exec : list nat) : nat := hd 0 exec.")
#prose[The _winner_ of an execution is the first process in the execution order.]

#mapping("writers_before", "ConsensusNumber.v", "667-668", [Prior writers in an execution.])
#rocq("Definition writers_before (exec : list nat) (i : nat) : list nat :=
  before_process exec i.")
#prose[`writers_before exec i` $=$ `before_process exec i`: the processes that wrote to memory before process $i$ executed. Determines the memory state that $i$ observes.]

#mapping("solo_0", "ConsensusNumber.v", "731-732", [Solo execution of process 0.])
#rocq("Definition solo_0 : list nat := [0].
Definition solo_1 : list nat := [1].")
#prose[_Solo executions_: `solo_0 = [0]` and `solo_1 = [1]`. In a solo execution, only one process runs. Critically, `writers_before solo_0 0 = []` and `writers_before solo_1 1 = []` — both solo processes see empty (initial) memory.]

#mapping("ConsensusNum", "ConsensusNumber.v", "400-404", [Consensus number type.])
#rocq("Definition ConsensusNum := option nat.  (* None = infinity *)
Definition cn_one : ConsensusNum := Some 1.
Definition cn_two : ConsensusNum := Some 2.
Definition cn_infinity : ConsensusNum := None.")
#prose[_Consensus number_ is modeled as `option nat`, where `None` represents $infinity$. Constants: $"CN" = 1$, $"CN" = 2$, $"CN" = infinity$.]

#mapping("cn_lt", "ConsensusNumber.v", "414-419", [Strict ordering on consensus numbers.])
#rocq("Definition cn_lt (c1 c2 : ConsensusNum) : Prop :=
  match c1, c2 with
  | Some n1, Some n2 => n1 < n2
  | Some _, None => True
  | None, _ => False
  end.")
#prose[$"cn"_"lt"(c_1, c_2)$: strict ordering. Any finite CN is less than $infinity$; $infinity$ is not less than anything.]

#mapping("rdma_read_cn", "ConsensusNumber.v", "1146-1149", [RDMA consensus number assignments.])
#rocq("Definition rdma_read_cn : ConsensusNum := cn_one.    (* CN(Read) = 1 *)
Definition rdma_write_cn : ConsensusNum := cn_one.   (* CN(Write) = 1 *)
Definition rdma_fadd_cn : ConsensusNum := cn_two.    (* CN(FADD) = 2 *)
Definition rdma_cas_cn : ConsensusNum := cn_infinity. (* CN(CAS) = inf *)")
#prose[RDMA consensus number assignments: $"CN"("Read") = "CN"("Write") = 1$, $"CN"("FADD") = 2$, $"CN"("CAS") = infinity$.]

#mapping("valid_rw_observation", "ConsensusNumber.v", "681-684", [Constraint on read/write observations.])
#rocq("Definition valid_rw_observation (obs : list nat -> nat -> nat) : Prop :=
  forall exec1 exec2 i j,
    writers_before exec1 i = writers_before exec2 j ->
    obs exec1 i = obs exec2 j.")
#prose[_Read/Write Observation Constraint_: Observation depends only on memory state (prior writes). If two executions have the same prior write history at positions $i, j$, observations must be equal. This captures: reads see memory values, writes return only acknowledgment.]

#mapping("valid_fadd_observation", "ConsensusNumber.v", "214-217", [Constraint on FADD observations.])
#rocq("Definition valid_fadd_observation (obs : list nat -> nat -> nat) : Prop :=
  forall exec1 exec2 i,
    same_elements (procs_before_as_set exec1 i) (procs_before_as_set exec2 i) ->
    obs exec1 i = obs exec2 i.")
#prose[_FADD Observation Constraint_: Observation depends only on the *set* of prior processes (not order). This captures: FADD returns sum, and addition is commutative ($delta_0 + delta_1 = delta_1 + delta_0$).]

#mapping("procs_before_as_set", "ConsensusNumber.v", "202-210", [Prior processes as a multiset.])
#rocq("Definition procs_before_as_set (exec : list nat) (i : nat) : list nat :=
  before_process exec i.

Definition same_elements (l1 l2 : list nat) : Prop :=
  forall x, count_occ Nat.eq_dec l1 x = count_occ Nat.eq_dec l2 x.")
#prose[`procs_before_as_set exec i` returns the multiset of processes before $i$. `same_elements` holds when two lists have identical element counts — i.e., they are permutations of each other.]

#mapping("exec_012 / exec_102", "ConsensusNumber.v", "221-222", [Critical executions for FADD CN=2 proof.])
#rocq("Definition exec_012 : list nat := [0; 1; 2].
Definition exec_102 : list nat := [1; 0; 2].")
#prose[Two 3-process executions that differ only in the order of P0 and P1. Process P2 executes last in both. Since `procs_before_as_set exec_012 2 = {0,1} = procs_before_as_set exec_102 2`, P2 sees the same FADD observation in both (commutativity of addition).]

#mapping("inp", "ConsensusNumber.v", "238", [Identity input function.])
#rocq("Definition inp (i : nat) : nat := i.")
#prose[Each process $i$'s input is $i$ itself. So the validity requirement is: the decision must equal the winner's ID.]

#mapping("p2_same_prior_set", "ConsensusNumber.v", "225-235", [P2 sees same prior process set in both executions.])
#rocq("Lemma p2_same_prior_set :
  same_elements (procs_before_as_set exec_012 2) (procs_before_as_set exec_102 2).")
#prose[*Lemma:* `procs_before_as_set exec_012 2 = {0,1}` and `procs_before_as_set exec_102 2 = {1,0}`. These are the same multiset (just reordered), so `same_elements` holds. This is the key commutativity fact.]

#mapping("fadd_p2_indistinguishable_general", "ConsensusNumber.v", "249-258", [P2 sees same observation in both FADD executions.])
#rocq("Theorem fadd_p2_indistinguishable_general :
  forall obs : list nat -> nat -> nat,
    valid_fadd_observation obs ->
    obs exec_012 2 = obs exec_102 2.")
#prose[*Lemma:* For any valid FADD observation function, process 2 sees the same value in `exec_012` and `exec_102`. This follows from `valid_fadd_observation` and `p2_same_prior_set`.]

#mapping("valid_cas_observation", "ConsensusNumber.v", "1073-1076", [Constraint on CAS observations.])
#rocq("Definition valid_cas_observation (obs : list nat -> nat -> nat) : Prop :=
  forall exec i, exec <> [] -> obs exec i = winner exec.")
#prose[_CAS Observation Constraint_: Observation equals the winner (first process to execute). This is *derived* from CAS semantics: first CAS to sentinel wins, all later fail, all read the winner's value.]

#mapping("readwrite_2consensus_impossible_same_protocol", "ConsensusNumber.v", "761-778", [*CN(Register) = 1*: Cannot solve 2-consensus.])
#rocq("Theorem readwrite_2consensus_impossible_same_protocol :
  forall obs : list nat -> nat -> nat,
    valid_rw_observation obs ->
    ~ exists (decide : nat -> nat),
        decide (obs solo_0 0) = 0 /\\
        decide (obs solo_1 1) = 1.
Proof.
  intros obs Hvalid [decide [Hval0 Hval1]].
  assert (Hsame : obs solo_0 0 = obs solo_1 1).
  { unfold valid_rw_observation in Hvalid. apply Hvalid. reflexivity. }
  rewrite Hsame in Hval0.
  rewrite Hval0 in Hval1.
  discriminate.
Qed.")
#prose[*Theorem (Register CN = 1):* No read/write protocol can solve 2-consensus.]
#annotated-proof(
  ("intros obs Hvalid [decide [Hval0 Hval1]].", [*Initial state* — _Goal:_ `forall obs, valid_rw_observation obs -> ~ exists decide, decide (obs solo_0 0) = 0 /\\ decide (obs solo_1 1) = 1`. \
  The `~` unfolds to `... -> False`. Introduce `obs`, `Hvalid`, then destruct the existential and conjunction. _Context:_ `obs : list nat -> nat -> nat`, `Hvalid : valid_rw_observation obs`, `decide : nat -> nat`, `Hval0 : decide (obs solo_0 0) = 0`, `Hval1 : decide (obs solo_1 1) = 1`. _Goal:_ `False`.]),
  ("assert (Hsame : obs solo_0 0 = obs solo_1 1).", [Begin sub-proof for the claim that both solo executions produce the same observation. _Sub-goal:_ `obs solo_0 0 = obs solo_1 1`.]),
  ("{ unfold valid_rw_observation in Hvalid.", [Expand `valid_rw_observation` in `Hvalid`. _`Hvalid` becomes:_ `forall exec1 exec2 i j, writers_before exec1 i = writers_before exec2 j -> obs exec1 i = obs exec2 j`. _Sub-goal:_ `obs solo_0 0 = obs solo_1 1` (unchanged).]),
  ("  apply Hvalid.", [Apply `Hvalid` with `exec1 := solo_0`, `i := 0`, `exec2 := solo_1`, `j := 1`. _Sub-goal becomes:_ `writers_before solo_0 0 = writers_before solo_1 1`.]),
  ("  reflexivity. }", [`writers_before solo_0 0` computes to `before_process [0] 0 = []` (no writers precede P0 in `[0]`). `writers_before solo_1 1` computes to `before_process [1] 1 = []` (no writers precede P1 in `[1]`). Both are `[]`, so `reflexivity` closes the sub-goal. _This is the fundamental insight: both solo processes see identical (empty) memory._ \
  _Context adds:_ `Hsame : obs solo_0 0 = obs solo_1 1`. _Goal:_ `False`.]),
  ("rewrite Hsame in Hval0.", [Rewrite `obs solo_0 0` to `obs solo_1 1` in `Hval0` using `Hsame`. _`Hval0` becomes:_ `decide (obs solo_1 1) = 0`. _Goal:_ `False`.]),
  ("rewrite Hval0 in Hval1.", [Both `Hval0` and `Hval1` now refer to `decide (obs solo_1 1)`. Substitute the value from `Hval0`. _`Hval1` becomes:_ `0 = 1`. _Goal:_ `False`.]),
  ("discriminate.", [`0` and `1` are distinct constructors (`O` vs `S O`). `discriminate` derives `False`. _No goals remaining._]),
)

#mapping("fadd_cannot_solve_3consensus", "ConsensusNumber.v", "261-278", [*SUPPLEMENTARY — CN(FADD) = 2*: Cannot solve 3-consensus.])
#rocq("Theorem fadd_cannot_solve_3consensus :
  forall obs : list nat -> nat -> nat,
    valid_fadd_observation obs ->
    ~ exists (decide : nat -> nat),
        decide (obs exec_012 2) = inp (winner exec_012) /\\
        decide (obs exec_102 2) = inp (winner exec_102).
Proof.
  intros obs Hvalid [decide [Hval012 Hval102]].
  assert (Hsame : obs exec_012 2 = obs exec_102 2).
  { exact (fadd_p2_indistinguishable_general obs Hvalid). }
  rewrite Hsame in Hval012.
  simpl in Hval012, Hval102.
  rewrite Hval012 in Hval102.
  discriminate.
Qed.")
#prose[*SUPPLEMENTARY — Theorem (FADD CN = 2):* FADD cannot solve 3-consensus. This result validates our model but is not required for the main impossibility theorem.]
#annotated-proof(
  ("intros obs Hvalid [decide [Hval012 Hval102]].", [*Initial state* — _Goal:_ `forall obs, valid_fadd_observation obs -> ~ exists decide, decide (obs exec_012 2) = inp (winner exec_012) /\\ decide (obs exec_102 2) = inp (winner exec_102)`. \
  Introduce and destruct. _Context:_ `obs : list nat -> nat -> nat`, `Hvalid : valid_fadd_observation obs`, `decide : nat -> nat`, `Hval012 : decide (obs exec_012 2) = inp (winner exec_012)`, `Hval102 : decide (obs exec_102 2) = inp (winner exec_102)`. _Goal:_ `False`.]),
  ("assert (Hsame : obs exec_012 2 = obs exec_102 2).", [Claim: process 2 sees the same observation in both executions. _Sub-goal:_ `obs exec_012 2 = obs exec_102 2`.]),
  ("{ exact (fadd_p2_indistinguishable_general obs Hvalid). }", [Apply the indistinguishability lemma directly. It uses `valid_fadd_observation` and the fact that `procs_before_as_set exec_012 2 = {0,1} = procs_before_as_set exec_102 2` (same set, just reordered). Since FADD addition is commutative ($delta_0 + delta_1 = delta_1 + delta_0$), observations must be equal. \
  _Context adds:_ `Hsame : obs exec_012 2 = obs exec_102 2`. _Goal:_ `False`.]),
  ("rewrite Hsame in Hval012.", [Rewrite using `Hsame`. _`Hval012` becomes:_ `decide (obs exec_102 2) = inp (winner exec_012)`. _Goal:_ `False`.]),
  ("simpl in Hval012, Hval102.", [Compute `winner exec_012 = hd 0 [0;1;2] = 0`, `inp 0 = 0`; `winner exec_102 = hd 0 [1;0;2] = 1`, `inp 1 = 1`. _`Hval012` becomes:_ `decide (obs exec_102 2) = 0`. _`Hval102` becomes:_ `decide (obs exec_102 2) = 1`. _Goal:_ `False`.]),
  ("rewrite Hval012 in Hval102.", [Both hypotheses refer to `decide (obs exec_102 2)`. Substitute. _`Hval102` becomes:_ `0 = 1`. _Goal:_ `False`.]),
  ("discriminate.", [`0 ≠ 1`. `discriminate` derives `False`. _No goals remaining._]),
)

#mapping("valid_cas_no_ambiguity", "ConsensusNumber.v", "1111-1123", [*SUPPLEMENTARY — CN(CAS) = $infinity$*: Can solve any $n$-consensus.])
#rocq("Theorem valid_cas_no_ambiguity :
  forall obs : list nat -> nat -> nat,
    valid_cas_observation obs ->
    forall exec1 exec2,
      exec1 <> [] -> exec2 <> [] ->
      winner exec1 <> winner exec2 ->
      forall i, obs exec1 i <> obs exec2 i.")
#prose[*SUPPLEMENTARY — Theorem (CAS CN = $infinity$):* Any valid CAS observation allows solving $n$-consensus for all $n$. This result validates our model but is not required for the main impossibility theorem.

*Proof:* CAS observations directly reveal the winner. Different winners $->$ different observations $->$ always distinguishable. $square$]

== Failover as 2-Consensus (`Theorem3/FailoverConsensus.v`)

#mapping("FailoverDecision", "FailoverConsensus.v", "38-40", [Failover decision space.])
#rocq("Inductive FailoverDecision :=
  | Commit  (* Original CAS was executed; do NOT retry *)
  | Abort.  (* Original CAS was NOT executed; retry is SAFE *)")
#prose[A _failover decision_ is either *Commit* (operation executed, skip retry) or *Abort* (operation not executed, do retry).]

#mapping("PastKnowledge", "FailoverConsensus.v", "45-47", [What actually happened.])
#rocq("Inductive PastKnowledge :=
  | PastExecuted      (* CAS was executed at receiver *)
  | PastNotExecuted.  (* CAS was not executed *)")
#prose[The _past process_ knows the ground truth: was the CAS executed or not?]

#mapping("FutureObservation", "FailoverConsensus.v", "50-52", [What the future process can see.])
#rocq("Inductive FutureObservation :=
  | FutureSeesTimeout       (* Sender observed timeout *)
  | FutureSeesCompletion.   (* Sender received completion ACK *)")
#prose[The _future process_ observes only transport-level signals. Critically, `FutureSeesTimeout` occurs in both the packet-loss and ACK-loss scenarios.]

#mapping("scenario1/2 definitions", "FailoverConsensus.v", "206-213", [The two failover scenarios.])
#rocq("Definition scenario1_future : FutureObservation := FutureSeesTimeout.
Definition scenario1_correct : FailoverDecision := Abort.
Definition scenario2_future : FutureObservation := FutureSeesTimeout.
Definition scenario2_correct : FailoverDecision := Commit.")
#prose[Scenario 1 (packet lost): future sees timeout, correct decision is Abort (retry). Scenario 2 (ACK lost): future sees timeout, correct decision is Commit (don't retry). *Same observation, different correct decisions.*]

#mapping("VerificationMechanism", "FailoverConsensus.v", "257", [A function from memory to decision.])
#rocq("Definition VerificationMechanism := Memory -> bool.
(* Encoding: true = Commit, false = Abort *)")
#prose[A _verification mechanism_ is any function $V : "Memory" -> "bool"$ that inspects remote memory and returns a failover decision. Under transparency, V is limited to using reads.]

#mapping("History", "FailoverConsensus.v", "261-263", [What actually happened to the CAS.])
#rocq("Inductive History :=
  | HistExecuted : Memory -> History       (* CAS was executed *)
  | HistNotExecuted : Memory -> History.   (* CAS was not executed *)")
#prose[A _history_ records whether the CAS was executed, along with the memory state. Both variants carry a memory parameter because ABA can reset memory to any state.]

#mapping("history_executed", "FailoverConsensus.v", "265-269", [Was the CAS executed?])
#rocq("Definition history_executed (h : History) : bool :=
  match h with
  | HistExecuted _ => true
  | HistNotExecuted _ => false
  end.")
#prose[Extracts the execution status as a boolean: `true` for executed, `false` for not executed.]

#mapping("final_memory (Failover)", "FailoverConsensus.v", "271-275", [Memory state at end of history.])
#rocq("Definition final_memory (h : History) : Memory :=
  match h with
  | HistExecuted m => m
  | HistNotExecuted m => m
  end.")
#prose[The final memory state. *Key ABA property:* both `HistExecuted m` and `HistNotExecuted m` yield the same memory $m$. This is the formal encoding of the ABA problem.]

#mapping("correct_decision_for", "FailoverConsensus.v", "278-279", [The correct failover decision for a history.])
#rocq("Definition correct_decision_for (h : History) : bool :=
  history_executed h.")
#prose[The correct decision equals the execution status: `true` (Commit) if executed, `false` (Abort) if not. A correct verification mechanism must satisfy $V(m_"final") = "correct"_"decision"_"for"(h)$ for all histories.]

#mapping("H0 / H1", "FailoverConsensus.v", "289-292", [The two ABA-indistinguishable histories.])
#rocq("Definition H1 : History := HistExecuted init_mem.   (* CAS executed, ABA reset *)
Definition H0 : History := HistNotExecuted init_mem. (* CAS not executed *)")
#prose[$H_1$ (executed) and $H_0$ (not executed) both have `final_memory = init_mem` due to ABA. But `correct_decision_for H1 = true` while `correct_decision_for H0 = false`.]

#mapping("no_correct_future_decision", "FailoverConsensus.v", "230-243", [No correct decision function exists.])
#rocq("Theorem no_correct_future_decision :
  ~ exists f : FutureObservation -> FailoverDecision,
      f scenario1_future = scenario1_correct /\\
      f scenario2_future = scenario2_correct.
Proof.
  intros [f [H1 H2]].
  unfold scenario1_future, scenario2_future in *.
  unfold scenario1_correct, scenario2_correct in *.
  rewrite H1 in H2.
  discriminate.
Qed.")
#prose[*Theorem:* No deterministic function from sender observation to failover decision is correct.]
#annotated-proof(
  ("intros [f [H1 H2]].", [*Initial state* — _Goal:_ `~ exists f, f scenario1_future = scenario1_correct /\\ f scenario2_future = scenario2_correct`. \
  The `~` unfolds to `... -> False`. Destruct the existential and conjunction. _Context:_ `f : FutureObservation -> FailoverDecision`, `H1 : f scenario1_future = scenario1_correct`, `H2 : f scenario2_future = scenario2_correct`. _Goal:_ `False`.]),
  ("unfold scenario1_future, scenario2_future in *.", [Inline definitions: `scenario1_future := FutureSeesTimeout`, `scenario2_future := FutureSeesTimeout`. _`H1` becomes:_ `f FutureSeesTimeout = scenario1_correct`. _`H2` becomes:_ `f FutureSeesTimeout = scenario2_correct`. _Goal:_ `False`.]),
  ("unfold scenario1_correct, scenario2_correct in *.", [Inline: `scenario1_correct := Abort`, `scenario2_correct := Commit`. _`H1` becomes:_ `f FutureSeesTimeout = Abort`. _`H2` becomes:_ `f FutureSeesTimeout = Commit`. _Goal:_ `False`.]),
  ("rewrite H1 in H2.", [Since `f FutureSeesTimeout` appears in both, substitute using `H1`. _`H2` becomes:_ `Abort = Commit`. _Goal:_ `False`.]),
  ("discriminate.", [`Abort` and `Commit` are distinct constructors of `FailoverDecision`. `discriminate` derives `False`. _No goals remaining._]),
)

#mapping("solves_failover", "FailoverConsensus.v", "282-283", [Definition of solving failover.])
#rocq("Definition solves_failover (V : VerificationMechanism) : Prop :=
  forall h : History, V (final_memory h) = correct_decision_for h.")
#prose[A verification mechanism $V$ _solves failover_ if for every possible history $h$, $V(m_"final") = "correct decision for" h$.]

#mapping("H0_H1_same_memory", "FailoverConsensus.v", "295-296", [ABA: both histories have same memory.])
#rocq("Lemma H0_H1_same_memory : final_memory H0 = final_memory H1.")
#prose[*Lemma (ABA Problem):* History $H_0$ (not executed) and $H_1$ (executed then reset) have *identical* final memory.]

#mapping("failover_unsolvable", "FailoverConsensus.v", "304-331", [*Direct ABA Argument*: No verification mechanism solves failover.])
#rocq("Theorem failover_unsolvable :
  forall V : VerificationMechanism, ~ solves_failover V.
Proof.
  intros V Hsolves.
  unfold solves_failover in Hsolves.
  specialize (Hsolves H0) as HV0.
  specialize (Hsolves H1) as HV1.
  assert (Hmem_eq : final_memory H0 = final_memory H1).
  { apply H0_H1_same_memory. }
  rewrite Hmem_eq in HV0.
  rewrite HV0 in HV1.
  discriminate.
Qed.")
#prose[*Theorem (Failover Unsolvable, direct):* No verification mechanism can solve failover.]
#annotated-proof(
  ("intros V Hsolves.", [*Initial state* — _Context:_ `init_mem : Memory` (section variable). _Goal:_ `forall V : VerificationMechanism, ~ solves_failover V`. \
  The `~` unfolds to `solves_failover V -> False`. _Context adds:_ `V : VerificationMechanism` (i.e., `Memory -> bool`), `Hsolves : solves_failover V`. _Goal:_ `False`.]),
  ("unfold solves_failover in Hsolves.", [Expand definition. _`Hsolves` becomes:_ `forall h : History, V (final_memory h) = correct_decision_for h`. _Goal:_ `False`.]),
  ("specialize (Hsolves H0) as HV0.", [Instantiate `Hsolves` with `H0 := HistNotExecuted init_mem`. _Context adds:_ `HV0 : V (final_memory H0) = correct_decision_for H0`. Computationally: `final_memory (HistNotExecuted init_mem) = init_mem` and `correct_decision_for (HistNotExecuted _) = false`, so this represents `V init_mem = false`. _Goal:_ `False`.]),
  ("specialize (Hsolves H1) as HV1.", [Instantiate with `H1 := HistExecuted init_mem`. _Context adds:_ `HV1 : V (final_memory H1) = correct_decision_for H1`. Computationally: `final_memory (HistExecuted init_mem) = init_mem` and `correct_decision_for (HistExecuted _) = true`, so this represents `V init_mem = true`. _Goal:_ `False`.]),
  ("assert (Hmem_eq : final_memory H0 = final_memory H1).", [_Sub-goal:_ `final_memory H0 = final_memory H1`.]),
  ("{ apply H0_H1_same_memory. }", [Both `final_memory (HistNotExecuted init_mem)` and `final_memory (HistExecuted init_mem)` compute to `init_mem`. The lemma holds by `reflexivity`. _Context adds:_ `Hmem_eq : final_memory H0 = final_memory H1`. _Goal:_ `False`.]),
  ("rewrite Hmem_eq in HV0.", [Rewrite `final_memory H0` to `final_memory H1` in `HV0`. _`HV0` becomes:_ `V (final_memory H1) = correct_decision_for H0` (i.e., `V (final_memory H1) = false`). _Goal:_ `False`.]),
  ("rewrite HV0 in HV1.", [Both `HV0` and `HV1` now refer to `V (final_memory H1)`. Substitute. _`HV1` becomes:_ `correct_decision_for H0 = correct_decision_for H1`, which computes to `false = true`. _Goal:_ `False`.]),
  ("discriminate.", [`false` and `true` are distinct constructors of `bool`. `discriminate` derives `False`. _No goals remaining._]),
)

#mapping("failover_solver_yields_2consensus", "FailoverConsensus.v", "677-703", [*Positive Reduction*: Failover solver yields read-based 2-consensus protocol.])
#rocq("Lemma failover_solver_yields_2consensus :
  forall V : VerificationMechanism,
    solves_failover V ->
    exists obs : list nat -> nat -> nat,
      valid_rw_observation obs /\\
      exists decide : nat -> nat,
        decide (obs solo_0 0) = 0 /\\
        decide (obs solo_1 1) = 1.
Proof.
  intros V Hsolves.
  exists (fun _ _ => if V init_memory then 0 else 1).
  split.
  - unfold valid_rw_observation. intros. reflexivity.
  - exists (fun x => if Nat.eqb x 0 then 0 else 1).
    pose proof (Hsolves (HistExecuted init_memory)) as Hexec.
    pose proof (Hsolves (HistNotExecuted init_memory)) as Hnot.
    unfold final_memory, correct_decision_for, history_executed in *.
    rewrite Hexec in Hnot. discriminate.
Qed.")
#prose[*Lemma (Positive Reduction):* A correct failover solver yields a read-based observation function (satisfying `valid_rw_observation`) and decision function satisfying solo validity for 2-consensus.]
#annotated-proof(
  ("intros V Hsolves.", [*Initial state* — _Goal:_ `forall V, solves_failover V -> exists obs, valid_rw_observation obs /\\ exists decide, decide (obs solo_0 0) = 0 /\\ decide (obs solo_1 1) = 1`. \
  _Context:_ `V : VerificationMechanism` (i.e., `Memory -> bool`), `Hsolves : solves_failover V`. _Goal:_ `exists obs, valid_rw_observation obs /\\ exists decide, decide (obs solo_0 0) = 0 /\\ decide (obs solo_1 1) = 1`.]),
  ("exists (fun _ _ => if V init_memory then 0 else 1).", [Provide the observation function witness: a *constant* function (ignores execution and process ID), returning 0 if `V init_memory = true`, else 1. This models the ABA constraint: a read-based mechanism can only observe `init_memory` regardless of history. _Goal:_ `valid_rw_observation (fun _ _ => ...) /\\ exists decide, decide (if V init_memory then 0 else 1) = 0 /\\ decide (if V init_memory then 0 else 1) = 1`.]),
  ("split.", [Split the conjunction. _Subgoal 1:_ `valid_rw_observation (fun _ _ => if V init_memory then 0 else 1)`. _Subgoal 2:_ `exists decide, decide (if V init_memory then 0 else 1) = 0 /\\ decide (if V init_memory then 0 else 1) = 1`.]),
  ("- unfold valid_rw_observation. intros. reflexivity.", [_Subgoal 1._ Unfold: goal becomes `forall exec1 exec2 i j, writers_before exec1 i = writers_before exec2 j -> (if V init_memory then 0 else 1) = (if V init_memory then 0 else 1)`. After `intros`, both sides are identical regardless of the hypothesis. `reflexivity` closes it. _Subgoal 1 done._]),
  ("- exists (fun x => if Nat.eqb x 0 then 0 else 1).", [_Subgoal 2._ Provide the decision function: maps 0 $->$ 0, anything else $->$ 1. _Goal:_ `(if Nat.eqb (if V init_memory then 0 else 1) 0 then 0 else 1) = 0 /\\ (if Nat.eqb (if V init_memory then 0 else 1) 0 then 0 else 1) = 1`.]),
  ("  pose proof (Hsolves (HistExecuted init_memory)) as Hexec.", [_Context adds:_ `Hexec : V (final_memory (HistExecuted init_memory)) = correct_decision_for (HistExecuted init_memory)`. _Goal:_ unchanged.]),
  ("  pose proof (Hsolves (HistNotExecuted init_memory)) as Hnot.", [_Context adds:_ `Hnot : V (final_memory (HistNotExecuted init_memory)) = correct_decision_for (HistNotExecuted init_memory)`. _Goal:_ unchanged.]),
  ("  unfold final_memory, correct_decision_for, history_executed in *.", [Compute all definitions in context and goal. `final_memory (HistExecuted m) = m`, `final_memory (HistNotExecuted m) = m`, `correct_decision_for h = history_executed h`, `history_executed (HistExecuted _) = true`, `history_executed (HistNotExecuted _) = false`. _`Hexec` becomes:_ `V init_memory = true`. _`Hnot` becomes:_ `V init_memory = false`. The goal's `if` expressions also simplify according to `V init_memory`.]),
  ("  rewrite Hexec in Hnot.", [Substitute `V init_memory` with `true` (from `Hexec`) in `Hnot`. _`Hnot` becomes:_ `true = false`. _Goal:_ unchanged.]),
  ("  discriminate.", [`true = false` in context is a contradiction. Since the context is inconsistent, Rocq can prove any goal — including the remaining conjunction. _No goals remaining._ \
  _Key insight:_ `solves_failover V` is itself contradictory (V cannot return both `true` and `false` on the same input `init_memory`), so the existential witnesses need not "really" work. The proof constructs them purely to trigger the CN=1 impossibility.]),
)

#mapping("failover_impossible_by_read_cn", "FailoverConsensus.v", "715-726", [*THEOREM 3 Core*: Failover impossible via Register CN=1.])
#rocq("Theorem failover_impossible_by_read_cn :
  forall V : VerificationMechanism,
    ~ solves_failover V.
Proof.
  intros V Hsolves.
  destruct (failover_solver_yields_2consensus V Hsolves)
    as [obs [Hvalid [decide [Hval0 Hval1]]]].
  apply (readwrite_2consensus_impossible_same_protocol obs Hvalid).
  exists decide. exact (conj Hval0 Hval1).
Qed.")
#prose[*Theorem 3 (Failover Impossible by Register CN=1):* No verification mechanism can solve failover. This derives the impossibility FROM the CN=1 theorem, not as a separate ABA argument.]
#annotated-proof(
  ("intros V Hsolves.", [*Initial state* — _Goal:_ `forall V : VerificationMechanism, ~ solves_failover V`. \
  The `~` unfolds to `solves_failover V -> False`. _Context:_ `V : VerificationMechanism`, `Hsolves : solves_failover V`. _Goal:_ `False`.]),
  ("destruct (failover_solver_yields_2consensus V Hsolves)", [Apply the positive reduction lemma to `V` and `Hsolves`. It returns a proof of `exists obs, valid_rw_observation obs /\\ exists decide, ...`. The `destruct` extracts the witnesses.]),
  ("  as [obs [Hvalid [decide [Hval0 Hval1]]]].", [Destruct the nested existentials and conjunctions. _Context adds:_ `obs : list nat -> nat -> nat`, `Hvalid : valid_rw_observation obs`, `decide : nat -> nat`, `Hval0 : decide (obs solo_0 0) = 0`, `Hval1 : decide (obs solo_1 1) = 1`. _Goal:_ `False`.]),
  ("apply (readwrite_2consensus_impossible_same_protocol obs Hvalid).", [Apply the Register CN=1 impossibility theorem with `obs` and `Hvalid`. This theorem has conclusion `~ exists decide, decide (obs solo_0 0) = 0 /\\ decide (obs solo_1 1) = 1`, which unfolds to `(exists decide, ...) -> False`. Applying it to the goal `False` changes the goal to the premise. _Goal becomes:_ `exists decide, decide (obs solo_0 0) = 0 /\\ decide (obs solo_1 1) = 1`.]),
  ("exists decide.", [Provide the `decide` witness from the destructed positive reduction. _Goal becomes:_ `decide (obs solo_0 0) = 0 /\\ decide (obs solo_1 1) = 1`.]),
  ("exact (conj Hval0 Hval1).", [`conj` constructs `A /\\ B` from proofs of `A` and `B`. Provide `Hval0` and `Hval1` as the two conjuncts. _No goals remaining._ \
  The full chain: `Hsolves` $->$ positive reduction yields `obs`, `decide`, `Hval0`, `Hval1` $->$ CN=1 theorem demands they cannot exist $->$ but they do $->$ `False`.]),
)

== Main Result (`Theorem3/Hierarchy.v`)

#mapping("TransparentFailover", "Hierarchy.v", "31-40", [Transparent failover mechanism record.])
#rocq("Record TransparentFailover := {
  can_read_remote : Addr -> Memory -> Val;
  no_metadata_writes : Prop;
  decision_from_reads : list (Addr * Val) -> bool;
}.")
#prose[A _transparent failover_ mechanism can only: (1) read remote memory, (2) cannot write additional metadata, (3) must decide based solely on read results. This captures the transparency constraint from SHIFT.]

#mapping("verification_via_reads", "Hierarchy.v", "46-48", [Reads are genuine memory reads.])
#rocq("Definition verification_via_reads (tf : TransparentFailover) : Prop :=
  forall m addr,
    tf.(can_read_remote) addr m = mem_read m addr.")
#prose[The mechanism's read operation is a genuine memory read: `can_read_remote addr m = m(addr)`. No side channels or metadata.]

#mapping("provides_reliable_cas", "Hierarchy.v", "65-67", [Reliable CAS via transparent failover.])
#rocq("Definition provides_reliable_cas (tf : TransparentFailover) : Prop :=
  exists V : VerificationMechanism, solves_failover V.")
#prose[A transparent failover mechanism _provides reliable CAS_ if there exists a `VerificationMechanism` that solves failover for all histories. The main theorem proves this is impossible.]

#mapping("transparent_cas_failover_impossible", "Hierarchy.v", "81-92", [*THEOREM 3 Main*: Transparent failover impossible.])
#rocq("Theorem transparent_cas_failover_impossible :
  forall tf : TransparentFailover,
    verification_via_reads tf ->
    tf.(no_metadata_writes) ->
    ~ provides_reliable_cas tf.
Proof.
  intros tf Hreads Hno_meta.
  unfold provides_reliable_cas.
  intros [V Hsolves].
  exact (failover_impossible_by_read_cn V Hsolves).
Qed.")
#prose[*Theorem 3 (Main Impossibility):* Transparent failover for CAS is impossible.]
#annotated-proof(
  ("intros tf Hreads Hno_meta.", [*Initial state* — _Goal:_ `forall tf, verification_via_reads tf -> tf.(no_metadata_writes) -> ~ provides_reliable_cas tf`. \
  _Context:_ `tf : TransparentFailover`, `Hreads : verification_via_reads tf`, `Hno_meta : tf.(no_metadata_writes)`. _Goal:_ `~ provides_reliable_cas tf`.]),
  ("unfold provides_reliable_cas.", [Expand the definition. _Goal becomes:_ `~ (exists V : VerificationMechanism, solves_failover V)`, i.e., `(exists V, solves_failover V) -> False`.]),
  ("intros [V Hsolves].", [Assume the existential for contradiction and destruct it. _Context adds:_ `V : VerificationMechanism` (i.e., `Memory -> bool`), `Hsolves : solves_failover V`. _Goal:_ `False`.]),
  ("exact (failover_impossible_by_read_cn V Hsolves).", [`failover_impossible_by_read_cn` has type `forall V, solves_failover V -> False`. Applying it to `V` and `Hsolves` yields a proof of `False` directly. _No goals remaining._ \
  This single term encapsulates the full reduction chain: `Hsolves` $->$ positive reduction $->$ CN=1 barrier $->$ contradiction. Note: `Hreads` and `Hno_meta` are not used in the proof term — they justify *why* the mechanism is limited to reads, but `failover_impossible_by_read_cn` holds for *any* `VerificationMechanism`. The transparency constraints narrow the interface; the CN theorem shows even that narrowed interface is insufficient.]),
)

#mapping("reads_have_cn_1", "Hierarchy.v", "136-137", [Reads have consensus number 1.])
#rocq("Theorem reads_have_cn_1_verified : rdma_read_cn = cn_one.")
#prose[$"CN"("Read") = 1$, verified via `valid_rw_observation`.]

#mapping("failover_needs_cn_2", "FailoverConsensus.v", "633-637", [Failover needs CN $>=$ 2.])
#rocq("Theorem failover_needs_cn_2 : cn_lt cn_one (Some 2).")
#prose[Failover requires $"CN" >= 2$.]

#line(length: 100%, stroke: 0.5pt)

= Summary Table

#figure(
  table(
    columns: (auto, auto, 1fr, auto),
    inset: 6pt,
    stroke: 0.5pt,
    [*Rocq Theorem*], [*File:Line*], [*Paper Statement*], [*Technique*],
    [`impossibility_safe_retransmission`], [Impossibility.v:181], [Thm 1: No overlay provides safety + liveness], [Trace construction],
    [`fadd_non_idempotent`], [Atomics.v:33], [Thm 2a: FADD retry yields $2 delta != delta$], [Arithmetic],
    [`cas_double_success`], [CAS.v:106], [Thm 2b: CAS retry succeeds twice (ABA)], [Interleaving],
    [`no_transparent_overlay_atomics`], [Atomics.v:355], [Thm 2 Combined: No overlay for atomics], [Thm 1 + 2],
    [`readwrite_2consensus_impossible...`], [ConsensusNumber.v:761], [CN(Read) = 1: solo indistinguishable], [Herlihy],
    [`failover_solver_yields_2consensus`], [FailoverConsensus.v:680], [Solver $->$ read-based 2-consensus], [Reduction],
    [`failover_impossible_by_read_cn`], [FailoverConsensus.v:725], [Thm 3 Core: No $V$ solves failover (via CN=1)], [CN chain],
    [`transparent_cas_failover_impossible`], [Hierarchy.v:78], [Thm 3 Main: Transparent failover impossible], [CN hierarchy],
  ),
  caption: [One-to-one mapping of key theorems]
)
