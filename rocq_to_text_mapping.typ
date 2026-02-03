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

#mapping("write_idempotent", "Operations.v", "62-66", [Write operations are idempotent.])
#rocq("Lemma write_idempotent : forall m a v,
  fst (exec_write (fst (exec_write m a v)) a v) = fst (exec_write m a v).")
#prose[*Lemma (Write Idempotency):* For any memory $m$, address $a$, and value $v$: executing $"Write"(a,v)$ twice produces the same memory state as executing it once.]

#mapping("fadd_not_idempotent", "Operations.v", "69-92", [FADD is not idempotent when delta > 0.])
#rocq("Lemma fadd_not_idempotent : forall m a delta,
  delta <> 0 ->
  fst (exec_fadd (fst (exec_fadd m a delta)) a delta) <> fst (exec_fadd m a delta).")
#prose[*Lemma (FADD Non-Idempotency):* For $delta > 0$: executing $"FADD"(a, delta)$ twice yields $m(a) = v_"old" + 2 delta$, not $v_"old" + delta$. Therefore FADD is not idempotent.]

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

#line(length: 100%, stroke: 0.5pt)

== Overlay Properties (`Core/Properties.v`)

#mapping("TransparentOverlay", "Properties.v", "110-117", [A transparent failover mechanism.])
#rocq("Record TransparentOverlay := {
  decide_retransmit : list SenderObs -> Op -> bool;
  decision_deterministic : forall obs1 obs2 op,
    obs1 = obs2 ->
    decide_retransmit obs1 op = decide_retransmit obs2 op;
}.")
#prose[A _transparent overlay_ is a retransmission decision function $D : sigma(cal(T)) times "Op" -> {"retransmit", "skip"}$ that depends *only* on the sender view. No persistent metadata, no receiver-side modifications.]

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

#mapping("ProvidesSafety", "Impossibility.v", "71-77", [Safety: no ghost writes.])
#rocq("Definition ProvidesSafety (overlay : TransparentOverlay) : Prop :=
  forall t op V_new,
    In (EvAppReuse A_data V_new) t ->
    op_executed t op ->
    overlay.(decide_retransmit) (sender_view t) op = false.")
#prose[_Safety_: If operation was executed and memory was reused, the overlay must *not* retransmit (to avoid overwriting new data).]

#mapping("ProvidesLiveness", "Impossibility.v", "82-89", [Liveness: lost packets retransmitted.])
#rocq("Definition ProvidesLiveness (overlay : TransparentOverlay) : Prop :=
  forall t op,
    In (EvSend op) t ->
    ~ op_executed t op ->
    sender_saw_timeout t op ->
    overlay.(decide_retransmit) (sender_view t) op = true.")
#prose[_Liveness_: If operation was sent but not executed (packet lost), and sender timed out, the overlay *must* retransmit.]

#mapping("sender_views_equal", "Impossibility.v", "133-137", [Both traces have identical sender view.])
#rocq("Lemma sender_views_equal :
  sender_view T1_concrete = sender_view T2_concrete.
Proof. unfold T1_concrete, T2_concrete. simpl. reflexivity. Qed.")
#prose[*Lemma:* $sigma(cal(T)_1) = sigma(cal(T)_2) = ["ObsSent"(W_D), "ObsTimeout"(W_D)]$.]

#mapping("impossibility_safe_retransmission", "Impossibility.v", "181-238", [*THEOREM 1*: No transparent overlay provides both safety and liveness.])
#rocq("Theorem impossibility_safe_retransmission :
  forall overlay : TransparentOverlay,
    Transparent overlay ->
    SilentReceiver -> MemoryReuseAllowed -> NoExactlyOnce ->
    ~ (ProvidesSafety overlay /\\ ProvidesLiveness overlay).")
#prose[*Theorem 1 (Impossibility of Safe Retransmission):* Under transparency, no overlay can provide both safety and liveness.

*Proof:* By construction of $cal(T)_1, cal(T)_2$:
- Liveness on $cal(T)_1$ (packet lost): $D(sigma(cal(T)_1)) = "retransmit"$
- Safety on $cal(T)_2$ (executed, reused): $D(sigma(cal(T)_2)) = "skip"$
- But $sigma(cal(T)_1) = sigma(cal(T)_2)$ and $D$ is a function
- Contradiction: $"retransmit" = "skip"$ $square$]

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

#mapping("no_transparent_overlay_non_idempotent", "Atomics.v", "328-352", [No transparent overlay for non-idempotent ops.])
#rocq("Theorem no_transparent_overlay_non_idempotent :
  IndistinguishableExecutionStatus ->
  forall (overlay : TransparentOverlay) (op : Op) (m : Memory),
    ~ Idempotent op m ->
    ~ (LiveRetransmit overlay /\\
       (forall t, op_executed t op -> decide_retransmit (sender_view t) op = false)).")
#prose[*Theorem (Combined):* Given indistinguishable execution status (Theorem 1) and non-idempotency (Theorem 2), no transparent overlay can provide both liveness (retry on packet loss) and safety (no retry after execution).]

#mapping("no_transparent_overlay_atomics", "Atomics.v", "355-384", [Corollary for atomic operations.])
#rocq("Corollary no_transparent_overlay_atomics :
  IndistinguishableExecutionStatus ->
  forall (overlay : TransparentOverlay),
    (forall a delta, delta > 0 -> ~ (LiveRetransmit overlay /\\ SafeNoRetry overlay (OpFADD a delta))) /\\
    (forall a expected new_val, ... -> ~ (LiveRetransmit overlay /\\ SafeNoRetry overlay (OpCAS ...))).")
#prose[*Corollary:* No transparent overlay supports FADD (with $delta > 0$) or successful CAS (with $"exp" != "new"$).]

#pagebreak()

= Theorem 3: Consensus Hierarchy (`Theorem3/`)

== Consensus Framework (`Theorem3/ConsensusNumber.v`)

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
        decide (obs solo_1 1) = 1.")
#prose[*Theorem (Register CN = 1):* No read/write protocol can solve 2-consensus.

*Proof:* Solo executions $[0]$ and $[1]$ have same prior state (empty). Any valid R/W observation gives same value for both. But validity requires deciding 0 for $[0]$ and 1 for $[1]$. Contradiction. $square$]

#mapping("fadd_cannot_solve_3consensus", "ConsensusNumber.v", "261-278", [*CN(FADD) = 2*: Cannot solve 3-consensus.])
#rocq("Theorem fadd_cannot_solve_3consensus :
  forall obs : list nat -> nat -> nat,
    valid_fadd_observation obs ->
    ~ exists (decide : nat -> nat),
        decide (obs exec_012 2) = inp (winner exec_012) /\\
        decide (obs exec_102 2) = inp (winner exec_102).")
#prose[*Theorem (FADD CN = 2):* FADD cannot solve 3-consensus.

*Proof:* In executions $[0,1,2]$ and $[1,0,2]$, process 2 sees the same set ${0,1}$ ran before (sums are equal: $delta_0 + delta_1 = delta_1 + delta_0$). But winners differ (0 vs 1). $square$]

#mapping("valid_cas_no_ambiguity", "ConsensusNumber.v", "1092-1104", [*CN(CAS) = $infinity$*: Can solve any $n$-consensus.])
#rocq("Theorem valid_cas_no_ambiguity :
  forall obs : list nat -> nat -> nat,
    valid_cas_observation obs ->
    forall exec1 exec2,
      exec1 <> [] -> exec2 <> [] ->
      winner exec1 <> winner exec2 ->
      forall i, obs exec1 i <> obs exec2 i.")
#prose[*Theorem (CAS CN = $infinity$):* Any valid CAS observation allows solving $n$-consensus for all $n$.

*Proof:* CAS observations directly reveal the winner. Different winners $->$ different observations $->$ always distinguishable. $square$]

== Failover as 2-Consensus (`Theorem3/FailoverConsensus.v`)

#mapping("FailoverDecision", "FailoverConsensus.v", "38-40", [Failover decision space.])
#rocq("Inductive FailoverDecision :=
  | Commit  (* Original CAS was executed; do NOT retry *)
  | Abort.  (* Original CAS was NOT executed; retry is SAFE *)")
#prose[A _failover decision_ is either *Commit* (operation executed, skip retry) or *Abort* (operation not executed, do retry).]

#mapping("no_correct_future_decision", "FailoverConsensus.v", "230-243", [No correct decision function exists.])
#rocq("Theorem no_correct_future_decision :
  ~ exists f : FutureObservation -> FailoverDecision,
      f scenario1_future = scenario1_correct /\\
      f scenario2_future = scenario2_correct.")
#prose[*Theorem:* No deterministic function from sender observation to failover decision is correct.

*Proof:* Both scenarios produce $"FutureSeesTimeout"$. Scenario 1 requires Abort. Scenario 2 requires Commit. But $f("Timeout")$ can only return one value. $square$]

#mapping("solves_failover", "FailoverConsensus.v", "282-283", [Definition of solving failover.])
#rocq("Definition solves_failover (V : VerificationMechanism) : Prop :=
  forall h : History, V (final_memory h) = correct_decision_for h.")
#prose[A verification mechanism $V$ _solves failover_ if for every possible history $h$, $V(m_"final") = "correct decision for" h$.]

#mapping("H0_H1_same_memory", "FailoverConsensus.v", "295-296", [ABA: both histories have same memory.])
#rocq("Lemma H0_H1_same_memory : final_memory H0 = final_memory H1.")
#prose[*Lemma (ABA Problem):* History $H_0$ (not executed) and $H_1$ (executed then reset) have *identical* final memory.]

#mapping("failover_unsolvable", "FailoverConsensus.v", "304-331", [*THEOREM 3 Core*: No verification mechanism solves failover.])
#rocq("Theorem failover_unsolvable :
  forall V : VerificationMechanism, ~ solves_failover V.")
#prose[*Theorem 3 (Failover Unsolvable):* No verification mechanism can solve failover.

*Proof:*
- $H_0$: CAS not executed $->$ $V(m) = "false"$ (Abort)
- $H_1$: CAS executed, ABA reset $->$ $V(m) = "true"$ (Commit)
- But $"final_memory"(H_0) = "final_memory"(H_1) = m$
- So $V(m) = "true"$ AND $V(m) = "false"$. Contradiction. $square$]

== Main Result (`Theorem3/Hierarchy.v`)

#mapping("transparent_cas_failover_impossible", "Hierarchy.v", "78-89", [*THEOREM 3 Main*: Transparent failover impossible.])
#rocq("Theorem transparent_cas_failover_impossible :
  forall tf : TransparentFailover,
    verification_via_reads tf ->
    tf.(no_metadata_writes) ->
    ~ provides_reliable_cas tf.")
#prose[*Theorem 3 (Main Impossibility):* Transparent failover for CAS is impossible.

*Proof structure:*
1. Failover requires solving 2-consensus (distinguishing $H_0$ from $H_1$)
2. Transparency limits verification to read-only operations
3. $"CN"("Read") = 1 < 2$
4. By Herlihy's hierarchy, CN=1 primitives cannot solve 2-consensus $square$]

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
    [`failover_unsolvable`], [FailoverConsensus.v:304], [Thm 3 Core: No $V$ solves failover], [ABA],
    [`transparent_cas_failover_impossible`], [Hierarchy.v:78], [Thm 3 Main: Transparent failover impossible], [CN hierarchy],
  ),
  caption: [One-to-one mapping of key theorems]
)
