theory Stateless_Manifest_Retention
  imports Stateless_Storage
begin

section \<open>Remote rename effects and deletion snapshots\<close>

text \<open>
  A log entry is an actual remote segments-object write, even if the
  caller eventually gets an exception. The queue is the union of all
  captured deletion batches. Keeping successful and failed requests in
  the queue overapproximates delayed callbacks, partial deletes and retries.
  Data blobs, local pending segments and other terms are outside this log.
\<close>

record manifest_io =
  rename_log :: "nat list"
  live_generations :: "nat set"
  obsolete_generations :: "nat set"
  queued_generations :: "nat set"
  write_fenced :: bool

definition manifest_io_initial where
  "manifest_io_initial =
    \<lparr>rename_log = [], live_generations = {}, obsolete_generations = {},
      queued_generations = {}, write_fenced = False\<rparr>"

definition before_previous_rename where
  "before_previous_rename earlier batch \<longleftrightarrow>
    (case earlier of [] \<Rightarrow> batch = {} | latest # _ \<Rightarrow> \<forall>g\<in>batch. g < latest)"

text \<open>
  The batch is captured inside Directory.rename, before Lucene reaches
  the checkpoint that can mark the immediately preceding commit obsolete.
  An unsuccessful PUT can have a late effect but returns without capturing
  a batch. An error after the capture can leave both the object and the
  queued batch. In either case the same writer cannot publish again in
  that term. After fencing the model allows late failed-write effects
  without another batch. A prepare failure has no remote manifest effect.
\<close>

inductive manifest_io_step where
  prepare_failure: "manifest_io_step s s"
| rename:
    "(write_fenced s \<Longrightarrow> failed \<and> batch = {}) \<Longrightarrow>
     (\<And>old. old \<in> set (rename_log s) \<Longrightarrow> old < gen) \<Longrightarrow>
     batch \<subseteq> obsolete_generations s \<Longrightarrow>
     manifest_io_step s
       (s\<lparr>rename_log := gen # rename_log s, live_generations := insert gen (live_generations s),
          queued_generations := queued_generations s \<union> batch, write_fenced := failed\<rparr>)"
| mark_obsolete:
    "rename_log s = latest # earlier \<Longrightarrow> gen < latest \<Longrightarrow>
     manifest_io_step s (s\<lparr>obsolete_generations := insert gen (obsolete_generations s)\<rparr>)"
| finalization_failure:
    "manifest_io_step s (s\<lparr>write_fenced := True\<rparr>)"
| retry_delete:
    "removed \<subseteq> queued_generations s \<Longrightarrow>
     manifest_io_step s (s\<lparr>live_generations := live_generations s - removed\<rparr>)"

definition protected_generations where "protected_generations s = set (take 2 (rename_log s))"

definition manifest_io_ok where
  "manifest_io_ok s \<longleftrightarrow>
    protected_generations s \<subseteq> live_generations s \<and>
    protected_generations s \<inter> queued_generations s = {} \<and>
    before_previous_rename (rename_log s) (queued_generations s \<union> obsolete_generations s)"

lemma manifest_io_step_preserves:
  assumes step: "manifest_io_step s s'" and old: "manifest_io_ok s"
  shows "manifest_io_ok s'"
  using step
proof cases
  case prepare_failure
  then show ?thesis using old by simp
next
  case (rename failed batch gen)
  show ?thesis
  proof (cases "rename_log s")
    case Nil
    with old rename(1,4) show ?thesis
      by (simp add: manifest_io_ok_def protected_generations_def before_previous_rename_def)
  next
    case (Cons latest older)
    have advance: "latest < gen" using rename(3)[of latest] Cons by simp
    have older: "g < latest" if "g \<in> queued_generations s \<union> obsolete_generations s" for g
      using old Cons that by (simp add: manifest_io_ok_def before_previous_rename_def)
    have queued: "g < latest" if "g \<in> queued_generations s \<union> batch \<union> obsolete_generations s" for g
      using rename(4) that by (auto intro: older)
    have older_than_new: "g < gen" if "g \<in> queued_generations s \<union> batch \<union> obsolete_generations s" for g
      by (rule less_trans[OF queued[OF that] advance])
    from old rename(1) Cons queued older_than_new show ?thesis
      by (auto simp: manifest_io_ok_def protected_generations_def before_previous_rename_def)
  qed
next
  case mark_obsolete
  with old show ?thesis by (auto simp: manifest_io_ok_def protected_generations_def before_previous_rename_def)
next
  case finalization_failure
  then show ?thesis using old by (simp add: manifest_io_ok_def protected_generations_def)
next
  case retry_delete
  with old show ?thesis by (auto simp: manifest_io_ok_def protected_generations_def)
qed

theorem asynchronous_deletes_preserve_latest_two:
  assumes "rtranclp manifest_io_step manifest_io_initial s"
  shows "protected_generations s \<subseteq> live_generations s"
    "protected_generations s \<inter> queued_generations s = {}"
proof -
  have "manifest_io_ok s" using assms
  proof induction
    case base
    show ?case by (simp add: manifest_io_ok_def manifest_io_initial_def protected_generations_def before_previous_rename_def)
  next
    case (step a b)
    show ?case by (rule manifest_io_step_preserves[OF step.hyps(2) step.IH])
  qed
  then show "protected_generations s \<subseteq> live_generations s"
    "protected_generations s \<inter> queued_generations s = {}" unfolding manifest_io_ok_def by blast+
qed

corollary any_pending_retry_preserves_protected:
  assumes "rtranclp manifest_io_step manifest_io_initial s"
    "removed \<subseteq> queued_generations s"
  shows "protected_generations s \<subseteq> live_generations s - removed"
  using asynchronous_deletes_preserve_latest_two[OF assms(1)] assms(2) by blast

end
