theory Stateless_Next_Publication
  imports Stateless_Slot_Liveness
begin

section \<open>Same-term publication from a free slot\<close>

definition stateless_next_ready where
  "stateless_next_ready n t b st \<longleftrightarrow>
    (let x = slot_exec st; s = shared_state x; a = processes x n in
      active_slot st = None \<and> slot_leading st \<and> app_term a = t \<and>
      holds_grant s (endpoint x n) t \<and> reserved_term s = t \<and>
      latest_issued s t = Some b \<and> b \<in> approvals s \<and> app_accepted a = position b \<and>
      running_application a = None)"

definition next_slot_move where
  "next_slot_move n st st' \<longleftrightarrow> st = st' \<or> stateless_slot_step n st st'"

lemma next_slot_real:
  "stateless_slot_step n st st' \<Longrightarrow> next_slot_move n st st'"
  by (simp add: next_slot_move_def)

lemma next_slot_core_move:
  assumes "window_move (slot_exec st) x"
    "incarnation (processes x n) = incarnation (processes (slot_exec st) n)"
    "app_term (processes x n) = app_term (processes (slot_exec st) n)"
    "issued (shared_state x) = issued (shared_state (slot_exec st))"
  shows "next_slot_move n st (st\<lparr>slot_exec := x\<rparr>)"
proof -
  from assms(1) have "x = slot_exec st \<or> stateless_exec_step (slot_exec st) x"
    unfolding window_move_def by auto
  then show ?thesis
  proof
    assume "x = slot_exec st"
    then show ?thesis by (simp add: next_slot_move_def)
  next
    assume step: "stateless_exec_step (slot_exec st) x"
    have "stateless_slot_step n st (st\<lparr>slot_exec := x, slot_leading :=
      (slot_leading st \<and> app_term (processes x n) = app_term (processes (slot_exec st) n))\<rparr>)"
      by (rule stateless_slot_step.core[OF step assms(2)]) (simp add: assms(4))
    thus ?thesis by (simp add: next_slot_move_def assms(3))
  qed
qed

lemma next_slot_signal:
  "dispatch_publication_signal n i sig st = st' \<Longrightarrow> next_slot_move n st st'"
  by (auto intro: next_slot_real stateless_slot_step.dispatch)

lemma next_slot_moves_reachable:
  assumes "stateless_slot_reachable n st" "(next_slot_move n ^^ k) st st'"
  shows "stateless_slot_reachable n st'"
  using assms(2)
proof (induction k arbitrary: st')
  case 0
  then show ?case using assms(1) by simp
next
  case (Suc k)
  from Suc.prems obtain mid where "(next_slot_move n ^^ k) st mid" "next_slot_move n mid st'"
    by (rule relpowp_Suc_E)
  from Suc.IH[OF this(1)] this(2) show ?case unfolding next_slot_move_def
    by (metis stateless_slot_reachable.step)
qed

text \<open>
  The successful publication path starts after the previous completion
  has cleared the slot and any resulting leadership work has run. It
  uses the existing accepted and approved tip as its parent. No election
  or recovery search is needed. The path assumes timely service of the
  durable manifest write, the fence, self delivery, the target wait
  and the local applier, while no lease or local term change intervenes.
  The fence is checked against the exact live register term. Guessing
  lease ownership from the process's last confirmed grant would allow a
  stale attempt after an effective CAS whose caller never got a reply.

  The quorum future and its successful fence result are separate. The
  self reply and the end of the target wait enable the local applier
  decision. After the applier succeeds, the callback path needs both
  the work preceding the final mutex acquisition and service of that
  acquisition. The final state is the precise slot-clear boundary.
  Deferred term changes or follow-up leadership and master service
  work can still affect admission of a subsequent publication.
\<close>

locale stateless_next_publication =
  fixes n :: node and t payload :: nat and b :: lineage and st :: stateless_slot_state
    and F :: config and m :: state_manifest and files
  assumes reach: "stateless_slot_reachable n st"
    and ready: "stateless_next_ready n t b st"
    and manifest: "manifest_history m = stateless_update (endpoint (slot_exec st) n) t payload F b"
    and synced: "files_match files m"
begin

abbreviation x where "x \<equiv> slot_exec st"
abbreviation s where "s \<equiv> shared_state x"
abbreviation a where "a \<equiv> processes x n"
abbreviation who where "who \<equiv> endpoint x n"
abbreviation h where "h \<equiv> stateless_update who t payload F b"
abbreviation key where "key \<equiv> position h"
abbreviation q where "q \<equiv> Apply_Request n key"
abbreviation gen where "gen \<equiv> next_object_generation st"

lemma next_readyD:
  shows "active_slot st = None" "slot_leading st" "app_term a = t"
    "holds_grant s who t" "reserved_term s = t" "latest_issued s t = Some b"
    "b \<in> approvals s" "app_accepted a = position b" "running_application a = None"
  using ready by (simp_all add: stateless_next_ready_def Let_def)

lemma next_core_reachable: "stateless_execution_reachable x"
  by (rule slot_state_projects[OF reach])

lemma next_shared_reachable: "stateless_reachable s"
  using stateless_execution_projection[OF next_core_reachable] by blast

lemma next_key_increases: "position b < position h"
proof -
  from stateless_invariants[OF next_shared_reachable] next_readyD(6)
  have "term_of b = t" by (auto simp: stateless_ok_def issued_ok_def)
  then show ?thesis by (simp add: new_tip_fields)
qed

lemma next_history_fresh: "h \<notin> issued s"
proof
  assume "h \<in> issued s"
  from stateless_invariants[OF next_shared_reachable] have ii: "issued_ok s"
    by (simp add: stateless_ok_def)
  obtain prior where "latest_issued s (term_of h) = Some prior" "position h \<le> position prior"
    using issued_latest[OF ii \<open>h \<in> issued s\<close>] by blast
  with next_readyD(6) have "position h \<le> position b" by (simp add: new_tip_fields)
  with next_key_increases show False by simp
qed

end

locale stateless_slot_publication =
  fixes n :: node and t :: nat and h :: lineage and st :: stateless_slot_state
    and m :: state_manifest and files
  assumes reachable: "stateless_slot_reachable n st"
    and leading: "active_slot st = None" "slot_leading st"
    and grant: "holds_grant (shared_state (slot_exec st)) (endpoint (slot_exec st) n) t"
    and fence: "reserved_term (shared_state (slot_exec st)) = t"
    and local_term: "app_term (processes (slot_exec st) n) = t"
    and idle: "running_application (processes (slot_exec st) n) = None"
    and history: "owner h = n" "term_of h = t" "h \<notin> issued (shared_state (slot_exec st))"
    and advances: "rank_term (app_accepted (processes (slot_exec st) n)) = t \<Longrightarrow>
      app_accepted (processes (slot_exec st) n) < position h"
    and register_history: "stateless_exec_step (slot_exec st) ((slot_exec st)\<lparr>shared_state :=
      (shared_state (slot_exec st))\<lparr>issued := insert h (issued (shared_state (slot_exec st))),
        latest_issued := (latest_issued (shared_state (slot_exec st)))(t \<mapsto> h)\<rparr>\<rparr>)"
    and image: "manifest_history m = h" "files_match files m"
begin

abbreviation x where "x \<equiv> slot_exec st"
abbreviation s where "s \<equiv> shared_state x"
abbreviation a where "a \<equiv> processes x n"
abbreviation who where "who \<equiv> endpoint x n"
abbreviation key where "key \<equiv> position h"
abbreviation q where "q \<equiv> Apply_Request n key"
abbreviation gen where "gen \<equiv> next_object_generation st"

lemma through_application:
  obtains z p where
    "(next_slot_move n ^^ 16) st z"
    "active_slot z = Some p" "object_phase p = Local_Apply_Queued" "object_history p = h"
    "object_generation p = gen" "object_incarnation p = incarnation a"
    "matching_local_application n (slot_exec z) p key"
    "installed (processes (slot_exec z) n) = Some key"
    "h \<in> notifications (shared_state (slot_exec z))"
    "stateless_next_ready n t h (z\<lparr>active_slot := None\<rparr>)"
proof -
  let ?issued = "s\<lparr>issued := insert h (issued s), latest_issued := (latest_issued s)(t \<mapsto> h)\<rparr>"
  let ?stored = "?issued\<lparr>completed_images := insert h (completed_images ?issued), visible_image := (visible_image ?issued)(t \<mapsto> h)\<rparr>"
  let ?approved = "?stored\<lparr>approvals := insert h (approvals ?stored), frontier := h\<rparr>"
  let ?notified = "?approved\<lparr>notifications := insert h (notifications ?approved)\<rparr>"
  let ?x1 = "x\<lparr>shared_state := ?issued\<rparr>"
  let ?x2 = "?x1\<lparr>in_flight := insert (State_Packet h who) (in_flight x)\<rparr>"
  let ?x3 = "?x2\<lparr>shared_state := ?stored\<rparr>"
  let ?accepted = "a\<lparr>app_accepted := key\<rparr>"
  let ?x4 = "?x3\<lparr>processes := (processes x)(n := ?accepted)\<rparr>"
  let ?x6 = "?x4\<lparr>shared_state := ?approved\<rparr>"
  let ?x7 = "?x6\<lparr>shared_state := ?notified\<rparr>"
  define sent_commit where "sent_commit = ?x7\<lparr>in_flight := insert (Commit_Packet h who) (in_flight ?x7)\<rparr>"
  let ?x9 = "sent_commit"
  let ?offered = "?accepted\<lparr>offered := Some key, self_ready := insert q (self_ready ?accepted)\<rparr>"
  define self_commit where "self_commit = ?x9\<lparr>processes := (processes x)(n := ?offered)\<rparr>"
  let ?x10 = "self_commit"
  let ?queued = "?offered\<lparr>self_ready := self_ready ?offered - {q},
    queued_applications := insert q (queued_applications ?offered)\<rparr>"
  let ?x14 = "?x10\<lparr>processes := (processes x)(n := ?queued)\<rparr>"
  let ?sampled = "?queued\<lparr>queued_applications := queued_applications ?queued - {q},
    running_application := Some (q,key)\<rparr>"
  let ?x15 = "?x14\<lparr>processes := (processes x)(n := ?sampled)\<rparr>"
  let ?applied = "?sampled\<lparr>running_application := None, installed := Some key,
    application_successes := insert (incarnation ?sampled,q,key) (application_successes ?sampled)\<rparr>"
  let ?x16 = "?x15\<lparr>processes := (processes x)(n := ?applied)\<rparr>"

  note fields = history(1,2)
  note register = register_history
  have core_reachable: "stateless_execution_reachable x" by (rule slot_state_projects[OF reachable])
  have shared_reachable: "stateless_reachable s" using stateless_execution_projection[OF core_reachable] by blast
  have send: "stateless_exec_step ?x1 ?x2"
    using stateless_exec_step.send_state[where x="?x1" and n=n and h=h] by simp
  have stored_reachable: "stateless_reachable (shared_state ?x2)"
    using stateless_execution_projection[OF stateless_execution_reachable.step[OF stateless_execution_reachable.step[OF core_reachable register] send]]
    by blast
  have store: "stateless_exec_step ?x2 ?x3"
    using stateless_exec_manifest_install[where x="?x2" and t=t, OF stored_reachable _ image(2)]
    by (simp add: image(1))
  have accept: "stateless_exec_step ?x3 ?x4"
    using stateless_exec_step.receive_state[where x="?x3" and n=n and h=h and a=a]
      local_term advances fields(2) by simp
  have floor: "confirmed_floor s \<le> t"
    using stateless_floor_below_reservation[OF shared_reachable] fence by simp
  have approves: "stateless_step ?stored ?approved"
    using matching_window_fence_approves[where s="?stored" and h=h and seen=t and t=t]
      fence floor by simp
  have approve: "stateless_exec_step ?x4 ?x6"
    using stateless_exec_step.storage[where x="?x4" and s="?approved"] approves by simp
  have notifies: "stateless_step ?approved ?notified"
    using stateless_step.notify_commit[where s="?approved" and h=h] by simp
  have notify: "stateless_exec_step ?x6 ?x7"
    using stateless_exec_step.storage[where x="?x6" and s="?notified"] notifies by simp
  have send_commit: "stateless_exec_step ?x7 ?x9"
    using stateless_exec_step.send_commit[where x="?x7" and n=n and h=h]
    by (simp add: sent_commit_def)
  have same_proc: "processes ?x9 = (processes x)(n := ?accepted)"
    by (simp add: sent_commit_def)
  have wire: "Commit_Packet h (endpoint ?x9 n) \<in> in_flight ?x9"
    by (simp add: sent_commit_def)
  have receive_commit: "stateless_exec_step ?x9 ?x10"
    using stateless_exec_step.receive_commit[where x="?x9" and n=n and h=h and a="?accepted" and b="?offered", OF wire]
      fields local_term by (simp add: same_proc self_commit_def)
  have offered_proc: "processes ?x10 = (processes x)(n := ?offered)"
    by (simp add: self_commit_def)
  have queue: "window_move ?x10 ?x14"
    using window_local_queue[where x="?x10" and c=n and q=q] by (simp add: offered_proc)
  have sample: "window_move ?x14 ?x15"
    using window_local_sample[where x="?x14" and c=n and q=q and k=key] idle by simp
  have applied: "window_move ?x15 ?x16"
    using window_local_apply[where x="?x15" and c=n and q=q and k=key] by simp

  let ?p = "new_publication_object (incarnation a) gen h"
  let ?r1 = "st\<lparr>slot_exec := ?x1, active_slot := Some ?p, next_object_generation := Suc gen\<rparr>"
  let ?r2 = "?r1\<lparr>slot_exec := ?x2\<rparr>"
  let ?r3 = "?r1\<lparr>slot_exec := ?x3\<rparr>"
  let ?r4 = "?r1\<lparr>slot_exec := ?x4\<rparr>"
  let ?p5 = "?p\<lparr>object_phase := Waiting_For_Fence\<rparr>"
  let ?r5 = "?r4\<lparr>active_slot := Some ?p5\<rparr>"
  let ?r6 = "?r5\<lparr>slot_exec := ?x6\<rparr>"
  let ?r7 = "?r5\<lparr>slot_exec := ?x7\<rparr>"
  let ?p8 = "?p\<lparr>object_phase := Fence_Approved\<rparr>"
  let ?r8 = "?r7\<lparr>active_slot := Some ?p8\<rparr>"
  let ?r9 = "?r8\<lparr>slot_exec := ?x9\<rparr>"
  let ?r10 = "?r8\<lparr>slot_exec := ?x10\<rparr>"
  let ?p11 = "?p8\<lparr>object_self_reply := Some True\<rparr>"
  let ?r11 = "?r10\<lparr>active_slot := Some ?p11\<rparr>"
  let ?p12 = "?p11\<lparr>object_target_wait_ended := True\<rparr>"
  let ?r12 = "?r10\<lparr>active_slot := Some ?p12\<rparr>"
  let ?p13 = "?p12\<lparr>object_phase := Local_Apply_Queued\<rparr>"
  let ?r13 = "?r10\<lparr>active_slot := Some ?p13\<rparr>"
  let ?r14 = "?r13\<lparr>slot_exec := ?x14\<rparr>"
  let ?r15 = "?r13\<lparr>slot_exec := ?x15\<rparr>"
  let ?r16 = "?r13\<lparr>slot_exec := ?x16\<rparr>"

  have r1: "next_slot_move n st ?r1"
    by (rule next_slot_real, rule stateless_slot_step.register[OF leading register])
      (use history local_term in simp_all)
  have r2: "next_slot_move n ?r1 ?r2"
    by (rule next_slot_core_move) (use window_move_real[OF send] in simp_all)
  have r3: "next_slot_move n ?r2 ?r3"
    using next_slot_core_move[where n=n and st="?r2" and x="?x3"] window_move_real[OF store] by simp
  have r4: "next_slot_move n ?r3 ?r4"
    using next_slot_core_move[where n=n and st="?r3" and x="?x4"] window_move_real[OF accept] by simp
  have r5: "next_slot_move n ?r4 ?r5"
    by (rule next_slot_signal[where i=gen and sig=Reach_Quorum])
      (simp add: dispatch_publication_signal_def new_publication_object_def)
  have r6: "next_slot_move n ?r5 ?r6"
    by (rule next_slot_core_move) (use window_move_real[OF approve] in simp_all)
  have r7: "next_slot_move n ?r6 ?r7"
    using next_slot_core_move[where n=n and st="?r6" and x="?x7"] window_move_real[OF notify] by simp
  have r8: "next_slot_move n ?r7 ?r8"
    by (rule next_slot_signal[where i=gen and sig="Finish_Fence True"])
      (simp add: dispatch_publication_signal_def new_publication_object_def)
  have r9: "next_slot_move n ?r8 ?r9"
    by (rule next_slot_core_move) (use window_move_real[OF send_commit] in \<open>simp_all add: sent_commit_def\<close>)
  have r10: "next_slot_move n ?r9 ?r10"
    using next_slot_core_move[where n=n and st="?r9" and x="?x10"] window_move_real[OF receive_commit]
    by (simp add: sent_commit_def self_commit_def)
  have r11: "next_slot_move n ?r10 ?r11"
    by (rule next_slot_signal[where i=gen and sig="Receive_Self_Reply True"])
      (simp add: dispatch_publication_signal_def new_publication_object_def publication_waiting_def self_commit_def fields)
  have r12: "next_slot_move n ?r11 ?r12"
    by (rule next_slot_signal[where i=gen and sig=End_Target_Wait])
      (simp add: dispatch_publication_signal_def new_publication_object_def publication_waiting_def self_commit_def)
  have r13: "next_slot_move n ?r12 ?r13"
    by (rule next_slot_signal[where i=gen and sig=Queue_Local_Apply])
      (simp add: dispatch_publication_signal_def new_publication_object_def publication_waiting_def self_commit_def)
  have r14: "next_slot_move n ?r13 ?r14"
    by (rule next_slot_core_move) (use queue in \<open>simp_all add: self_commit_def\<close>)
  have r15: "next_slot_move n ?r14 ?r15"
    using next_slot_core_move[where n=n and st="?r14" and x="?x15"] sample by simp
  have r16: "next_slot_move n ?r15 ?r16"
    using next_slot_core_move[where n=n and st="?r15" and x="?x16"] applied by simp

  note four = four_steps[where R="next_slot_move n"]
  note extend = counted_path_append[where R="next_slot_move n"]
  note p1 = four[OF r1 r2 r3 r4]
  note p2 = four[OF r5 r6 r7 r8]
  note p3 = four[OF r9 r10 r11 r12]
  note p4 = four[OF r13 r14 r15 r16]
  have count: "(4 + 4) + (4 + 4) = (16::nat)" by simp
  have path: "(next_slot_move n ^^ 16) st ?r16"
    using extend[OF extend[OF p1 p2] extend[OF p3 p4]]
    unfolding count .
  show thesis
    by (rule that[of ?r16 ?p13, OF path])
      (use grant in \<open>simp_all add: sent_commit_def self_commit_def matching_local_application_def
        new_publication_object_def stateless_next_ready_def holds_grant_def Let_def fields local_term leading fence\<close>)
qed

end

context stateless_next_publication
begin

lemma next_publication_locale: "stateless_slot_publication n t h st m files"
proof -
  have register: "stateless_exec_step x (x\<lparr>shared_state :=
    s\<lparr>issued := insert h (issued s), latest_issued := (latest_issued s)(t \<mapsto> h)\<rparr>\<rparr>)"
    by (rule stateless_exec_step.next_publish[where base=b and n=n and t=t and F=F and payload=payload])
      (use next_readyD in simp_all)
  show ?thesis
    by unfold_locales (use reach next_readyD next_history_fresh next_key_increases register manifest synced
      in \<open>simp_all add: new_tip_fields\<close>)
qed

lemma next_publication_through_application:
  obtains z p where
    "(next_slot_move n ^^ 16) st z"
    "active_slot z = Some p" "object_phase p = Local_Apply_Queued"
    "matching_local_application n (slot_exec z) p key"
    "installed (processes (slot_exec z) n) = Some key"
    "h \<in> notifications (shared_state (slot_exec z))"
    "stateless_next_ready n t h (z\<lparr>active_slot := None\<rparr>)"
proof -
  interpret publication: stateless_slot_publication n t h st m files
    by (rule next_publication_locale)
  from publication.through_application obtain z p where properties:
    "(next_slot_move n ^^ 16) st z"
    "active_slot z = Some p" "object_phase p = Local_Apply_Queued"
    "matching_local_application n (slot_exec z) p key"
    "installed (processes (slot_exec z) n) = Some key"
    "h \<in> notifications (shared_state (slot_exec z))"
    "stateless_next_ready n t h (z\<lparr>active_slot := None\<rparr>)" by blast
  show thesis by (rule that[OF properties])
qed

end

section \<open>Servicing the staged successor publication\<close>

lemma serviced_next_trace_projects:
  assumes path: "\<And>i. i < k \<Longrightarrow> next_slot_move n (f i) (f (Suc i))"
  shows "next_slot_move n (serviced_stateless_trace k sel f j) (serviced_stateless_trace k sel f (Suc j))"
proof -
  let ?D = "serial_done k sel j"
  from completed_work_change[of "{..<k}" "\<lambda>i. {..<i}" sel j] show ?thesis
  proof (elim disjE)
    assume "serial_done k sel (Suc j) = ?D"
    then show ?thesis by (simp add: serviced_stateless_trace_def next_slot_move_def)
  next
    assume "\<exists>a. sel j = Some a \<and> work_ready {..<k} (\<lambda>i. {..<i}) ?D a \<and>
      serial_done k sel (Suc j) = insert a ?D"
    then obtain a where ready: "work_ready {..<k} (\<lambda>i. {..<i}) ?D a"
      and added: "serial_done k sel (Suc j) = insert a ?D" by blast
    have prefix: "?D = {..<card ?D}" by (rule serial_work_is_prefix[OF ordered_completed_work])
    from ready have job: "a < k" and new: "a \<notin> ?D" and deps: "{..<a} \<subseteq> ?D"
      by (auto simp: work_ready_def)
    have le: "{..<a} \<subseteq> {..<card ?D}" by (subst prefix[symmetric]) (rule deps)
    have not_member: "a \<notin> {..<card ?D}" by (subst prefix[symmetric]) (rule new)
    have count: "card ?D < k" using le not_member job by simp
    have sub: "?D \<subseteq> {..<k}" using ordered_completed_work by (rule ordered_work_def[THEN iffD1, THEN conjunct1])
    have fin: "finite ?D" by (rule finite_subset[OF sub]) simp
    have next_count: "card (serial_done k sel (Suc j)) = Suc (card ?D)"
      unfolding added by (rule card_insert_disjoint[OF fin new])
    show ?thesis unfolding serviced_stateless_trace_def next_count by (rule path[OF count])
  qed
qed

lemma concatenate_next_traces:
  assumes head: "\<And>j. next_slot_move n (r j) (r (Suc j))"
    and tail: "\<And>j. next_slot_move n (s j) (s (Suc j))"
    and link: "r k = s 0"
  defines "run \<equiv> (\<lambda>j. if j < k then r j else s (j - k))"
  shows "run 0 = r 0"
    "\<And>j. next_slot_move n (run j) (run (Suc j))"
    "run (k + u) = s u"
proof -
  show "run 0 = r 0" unfolding run_def using link by auto
  fix j
  show "next_slot_move n (run j) (run (Suc j))"
  proof (cases "Suc j < k")
    case True
    then have "j < k" by simp
    from True this show ?thesis by (simp add: run_def head)
  next
    case False
    show ?thesis
    proof (cases "j < k")
      case True
      with False have "Suc j = k" by simp
      from True False this link have "run j = r j" "run (Suc j) = r (Suc j)" by (simp_all add: run_def)
      then show ?thesis by (simp add: head)
    next
      case False
      then have "Suc j - k = Suc (j - k)" by simp
      with False show ?thesis by (simp add: run_def tail)
    qed
  qed
  show "run (k + u) = s u" by (simp add: run_def)
qed

context stateless_slot_publication
begin

theorem serviced_publication_releases_slot:
  fixes sel :: "nat \<Rightarrow> nat option"
  assumes service: "bounded_service {..<16} (\<lambda>i. {..<i}) sel B horizon"
    and head_time: "16 * B \<le> horizon"
    and completion: "bounded_service (completion_jobs key) (completion_dependencies key) callbacks C horizon'"
    and tail_time: "3 * C \<le> horizon'"
  obtains run where "run 0 = st" "\<And>j. next_slot_move n (run j) (run (Suc j))"
    "stateless_slot_reachable n (run (16 * B + 3 * C))"
    "h \<in> notifications (shared_state (slot_exec (run (16 * B + 3 * C))))"
    "installed (processes (slot_exec (run (16 * B + 3 * C))) n) = Some key"
    "active_slot (run (16 * B + 3 * C)) = None"
    "stateless_next_ready n t h (run (16 * B + 3 * C))"
    "\<exists>p. active_slot (run (16 * B)) = Some p \<and> object_phase p = Local_Apply_Queued \<and>
      object_history p = h \<and> object_generation p = gen \<and> object_incarnation p = incarnation a \<and>
      matching_local_application n (slot_exec (run (16 * B))) p key"
    "incarnation (processes (slot_exec (run (16 * B + 3 * C))) n) = incarnation a"
proof -
  obtain z p where path: "(next_slot_move n ^^ 16) st z"
    and app: "active_slot z = Some p" "object_phase p = Local_Apply_Queued"
      "matching_local_application n (slot_exec z) p key"
    and identity: "object_history p = h" "object_generation p = gen" "object_incarnation p = incarnation a"
    and results: "installed (processes (slot_exec z) n) = Some key"
      "h \<in> notifications (shared_state (slot_exec z))"
      "stateless_next_ready n t h (z\<lparr>active_slot := None\<rparr>)"
    by (rule through_application) blast
  obtain f where f: "f 0 = st" "f 16 = z"
    "\<And>i. i < 16 \<Longrightarrow> next_slot_move n (f i) (f (Suc i))"
    using path unfolding relpowp_fun_conv by blast
  let ?r = "serviced_stateless_trace 16 sel f"
  have r_start: "?r 0 = st" using f(1) by (simp add: serviced_stateless_trace_def)
  have r_end: "?r (16 * B) = z"
    using serviced_stateless_trace_end[OF service head_time, of f] f(2) by simp
  have r_step: "next_slot_move n (?r j) (?r (Suc j))" for j
    by (rule serviced_next_trace_projects[where k=16 and sel=sel and f=f, OF f(3)])
  let ?s = "\<lambda>j. completion_projection n z (object_generation p) key
    (completed_work (completion_jobs key) (completion_dependencies key) callbacks j)"
  note finished = serviced_stateless_callback_clears_slot[OF app completion tail_time]
  have s_step: "next_slot_move n (?s j) (?s (Suc j))" for j
    using finished(2)[of j] by (simp add: next_slot_move_def)
  have link: "?r (16 * B) = ?s 0" using r_end finished(1) by simp
  let ?run = "\<lambda>j. if j < 16 * B then ?r j else ?s (j - 16 * B)"
  note combined = concatenate_next_traces[where r="?r" and s="?s" and k="16 * B", OF r_step s_step link]
  have init: "?run 0 = st" using combined(1) r_start by simp
  have moves: "next_slot_move n (?run j) (?run (Suc j))" for j by (rule combined(2))
  have path': "\<And>j. ?run j = ?run (Suc j) \<or> stateless_slot_step n (?run j) (?run (Suc j))"
    using moves unfolding next_slot_move_def .
  have init_reach: "stateless_slot_reachable n (?run 0)" using init reachable by simp
  have reached: "stateless_slot_reachable n (?run (16 * B + 3 * C))"
    by (rule stateless_slot_trace_reachable[OF init_reach path'])
  have at_end: "?run (16 * B + 3 * C) = ?s (3 * C)" by (rule combined(3))
  have cleared: "active_slot (?run (16 * B + 3 * C)) = None"
    unfolding at_end by (rule finished(3))
  have exec: "slot_exec (?run (16 * B + 3 * C)) = slot_exec z"
    unfolding at_end by (rule finished(4))
  have leading: "slot_leading (?run (16 * B + 3 * C)) = slot_leading z"
    unfolding at_end by (rule finished(5))
  have notified: "h \<in> notifications (shared_state (slot_exec (?run (16 * B + 3 * C))))"
    unfolding exec by (rule results(2))
  have installed: "installed (processes (slot_exec (?run (16 * B + 3 * C))) n) = Some key"
    unfolding exec by (rule results(1))
  have next_ready: "stateless_next_ready n t h (?run (16 * B + 3 * C))"
    using results(3) finished(3-5)
    unfolding at_end stateless_next_ready_def by (simp add: Let_def)
  have app_cut: "?run (16 * B) = z" using combined(3)[of 0] link r_end by simp
  have tracks: "\<exists>p. active_slot z = Some p \<and> object_phase p = Local_Apply_Queued \<and>
    object_history p = h \<and> object_generation p = gen \<and> object_incarnation p = incarnation a \<and>
    matching_local_application n (slot_exec z) p key" using app identity by blast
  have incarnation: "incarnation (processes (slot_exec (?run (16 * B + 3 * C))) n) = incarnation a"
    unfolding exec using identity(3) app(3) by (simp add: matching_local_application_def)
  show thesis by (rule that[of "?run", OF init moves reached notified installed cleared next_ready _ incarnation])
    (unfold app_cut, rule tracks)
qed

end

context stateless_next_publication
begin

theorem subsequent_stateless_publication_releases_slot:
  fixes sel :: "nat \<Rightarrow> nat option"
  assumes service: "bounded_service {..<16} (\<lambda>i. {..<i}) sel B horizon"
    and head_time: "16 * B \<le> horizon"
    and completion: "bounded_service (completion_jobs key) (completion_dependencies key) callbacks C horizon'"
    and tail_time: "3 * C \<le> horizon'"
  obtains run where "run 0 = st" "\<And>j. next_slot_move n (run j) (run (Suc j))"
    "stateless_slot_reachable n (run (16 * B + 3 * C))"
    "h \<in> notifications (shared_state (slot_exec (run (16 * B + 3 * C))))"
    "installed (processes (slot_exec (run (16 * B + 3 * C))) n) = Some key"
    "active_slot (run (16 * B + 3 * C)) = None"
    "stateless_next_ready n t h (run (16 * B + 3 * C))"
proof -
  interpret publication: stateless_slot_publication n t h st m files
    by (rule next_publication_locale)
  from publication.serviced_publication_releases_slot[OF service head_time completion tail_time]
  obtain run where result: "run 0 = st" "\<And>j. next_slot_move n (run j) (run (Suc j))"
    "stateless_slot_reachable n (run (16 * B + 3 * C))"
    "h \<in> notifications (shared_state (slot_exec (run (16 * B + 3 * C))))"
    "installed (processes (slot_exec (run (16 * B + 3 * C))) n) = Some key"
    "active_slot (run (16 * B + 3 * C)) = None"
    "stateless_next_ready n t h (run (16 * B + 3 * C))" by blast
  show thesis by (rule that[OF result])
qed

end

section \<open>Failed completion and a superseding lease\<close>

lemma failure_in_current_term_requires_recovery:
  assumes "active_slot st = Some p" "object_incarnation p = incarnation (processes (slot_exec st) n)"
    "object_phase p = Publication_Failed" "term_of (object_history p) = app_term (processes (slot_exec st) n)"
  defines "cleared \<equiv> dispatch_publication_signal n (object_generation p) Clear_Failure st"
  shows "stateless_slot_step n st cleared" "active_slot cleared = None" "\<not> slot_leading cleared"
    "\<not> stateless_next_ready n u b cleared"
  unfolding cleared_def
  using failed_publication_releases[OF assms(1-3)] assms(4)
  by (auto simp: stateless_next_ready_def Let_def intro: stateless_slot_step.dispatch)

text \<open>
  The stateless beforeCommit hook checks the live register term against
  the publication term. A higher reservation therefore makes an exact
  successful fence impossible even if no successful claim callback has
  confirmed the higher term. When the fence rejection, failed self reply
  and terminal target wait are serviced, the failure callback clears the
  slot and leaves candidate mode for an attempt still in the local term.
\<close>

lemma higher_reservation_disables_successful_fence:
  assumes "term_of h < reserved_term (shared_state (slot_exec st))"
    "seen = reserved_term (shared_state (slot_exec st))"
  shows "seen \<noteq> term_of h"
  using assms by simp

lemma serviced_higher_lease_rejects_fence:
  assumes live: "active_slot st = Some p" "object_incarnation p = incarnation (processes (slot_exec st) n)"
    and waiting: "object_phase p = Waiting_For_Fence"
    and observed: "term_of (object_history p) < reserved_term (shared_state (slot_exec st))"
      "seen = reserved_term (shared_state (slot_exec st))"
  defines "rejected \<equiv> dispatch_publication_signal n (object_generation p)
    (Finish_Fence (seen = term_of (object_history p))) st"
  shows "stateless_slot_step n st rejected"
    "active_slot rejected = Some (p\<lparr>object_phase := Fence_Rejected\<rparr>)"
    "slot_exec rejected = slot_exec st"
proof -
  show "stateless_slot_step n st rejected" unfolding rejected_def by (rule stateless_slot_step.dispatch)
  have mismatch: "seen \<noteq> term_of (object_history p)"
    by (rule higher_reservation_disables_successful_fence[OF observed])
  show "active_slot rejected = Some (p\<lparr>object_phase := Fence_Rejected\<rparr>)" "slot_exec rejected = slot_exec st"
    using live waiting mismatch by (simp_all add: rejected_def dispatch_publication_signal_def)
qed

lemma rejected_current_fence_releases_to_recovery:
  assumes live: "active_slot st = Some p" "object_incarnation p = incarnation (processes (slot_exec st) n)"
    and ready: "object_phase p = Fence_Rejected" "object_self_reply p = Some False" "object_target_wait_ended p"
    and current: "term_of (object_history p) = app_term (processes (slot_exec st) n)"
  defines "queued \<equiv> dispatch_publication_signal n (object_generation p) Queue_Local_Apply st"
    and "cleared \<equiv> dispatch_publication_signal n (object_generation p) Clear_Failure
      (dispatch_publication_signal n (object_generation p) Queue_Local_Apply st)"
  shows "stateless_slot_step n st queued" "stateless_slot_step n queued cleared"
    "active_slot cleared = None" "\<not> slot_leading cleared"
    "\<not> stateless_next_ready n u b cleared"
proof -
  let ?q = "p\<lparr>object_phase := Publication_Failed\<rparr>"
  have shape: "queued = st\<lparr>active_slot := Some ?q\<rparr>"
    using live ready by (simp add: queued_def dispatch_publication_signal_def publication_waiting_def)
  show "stateless_slot_step n st queued" unfolding queued_def by (rule stateless_slot_step.dispatch)
  have failures:
    "active_slot queued = Some ?q" "object_incarnation ?q = incarnation (processes (slot_exec queued) n)"
    "object_phase ?q = Publication_Failed" "term_of (object_history ?q) = app_term (processes (slot_exec queued) n)"
    using live current by (simp_all add: shape)
  show "stateless_slot_step n queued cleared" "active_slot cleared = None" "\<not> slot_leading cleared"
    "\<not> stateless_next_ready n u b cleared" unfolding cleared_def queued_def[symmetric]
    using failure_in_current_term_requires_recovery[OF failures] by simp_all
qed

end
