theory Bounded_Service
  imports Main
begin

section \<open>Bounded service of enabled operations\<close>

text \<open>
  A schedule selects an operation or idles at each tick. An operation
  can take effect after its prerequisites have finished. Independent
  operations can run in any order. Ticks can model elapsed time once
  operation and scheduling bounds are expressed in that unit.
\<close>

definition work_ready where
  "work_ready jobs dependencies done a \<longleftrightarrow>
    a \<in> jobs \<and> a \<notin> done \<and> dependencies a \<subseteq> done"

fun completed_work where
  "completed_work jobs dependencies select 0 = {}"
| "completed_work jobs dependencies select (Suc i) =
    (let done = completed_work jobs dependencies select i in
      case select i of None \<Rightarrow> done
      | Some a \<Rightarrow> if work_ready jobs dependencies done a then insert a done else done)"

definition bounded_service where
  "bounded_service jobs dependencies select delay horizon \<longleftrightarrow>
    (\<forall>i a. i + delay \<le> horizon \<longrightarrow>
      work_ready jobs dependencies (completed_work jobs dependencies select i) a \<longrightarrow>
      (\<exists>j. i \<le> j \<and> j < i + delay \<and> select j = Some a))"

lemma completed_work_mono:
  "i \<le> j \<Longrightarrow> completed_work jobs dependencies select i \<subseteq> completed_work jobs dependencies select j"
proof (induction rule: inc_induct)
  case base
  show ?case by simp
next
  case (step i)
  have "completed_work jobs dependencies select i \<subseteq> completed_work jobs dependencies select (Suc i)"
    by (auto simp: Let_def split: option.splits)
  with step.IH show ?case by blast
qed

lemma selected_work_completes:
  assumes service: "bounded_service jobs dependencies select delay horizon"
    and time: "i + delay \<le> horizon"
    and ready: "work_ready jobs dependencies (completed_work jobs dependencies select i) a"
  shows "a \<in> completed_work jobs dependencies select (i + delay)"
proof -
  obtain j where ij: "i \<le> j" "j < i + delay" and chosen: "select j = Some a"
    using service time ready unfolding bounded_service_def by blast
  have "a \<in> completed_work jobs dependencies select (Suc j)"
  proof (cases "a \<in> completed_work jobs dependencies select j")
    case True
    show ?thesis using True completed_work_mono[of j "Suc j" jobs dependencies select] by auto
  next
    case False
    with ready completed_work_mono[OF ij(1), of jobs dependencies select]
    have "work_ready jobs dependencies (completed_work jobs dependencies select j) a"
      unfolding work_ready_def by blast
    then show ?thesis by (simp add: chosen)
  qed
  with completed_work_mono[of "Suc j" "i + delay" jobs dependencies select] ij(2) show ?thesis by auto
qed

lemma bounded_service_finishes_group:
  assumes service: "bounded_service jobs dependencies select delay horizon"
    and time: "i + delay \<le> horizon"
    and batch: "batch \<subseteq> jobs" "\<And>a. a \<in> batch \<Longrightarrow> dependencies a \<subseteq> completed_work jobs dependencies select i"
  shows "batch \<subseteq> completed_work jobs dependencies select (i + delay)"
proof
  fix a
  assume a: "a \<in> batch"
  show "a \<in> completed_work jobs dependencies select (i + delay)"
  proof (cases "a \<in> completed_work jobs dependencies select i")
    case True
    with completed_work_mono[of i "i + delay" jobs dependencies select] show ?thesis by auto
  next
    case False
    with batch a have "work_ready jobs dependencies (completed_work jobs dependencies select i) a"
      by (auto simp: work_ready_def)
    from selected_work_completes[OF service time this] show ?thesis .
  qed
qed

definition ordered_work where
  "ordered_work jobs dependencies done \<longleftrightarrow>
    done \<subseteq> jobs \<and> (\<forall>a\<in>done. dependencies a \<subseteq> done)"

lemma ordered_completed_work:
  "ordered_work jobs dependencies (completed_work jobs dependencies select i)"
proof (induction i)
  case 0
  show ?case by (simp add: ordered_work_def)
next
  case (Suc i)
  have "ordered_work jobs dependencies (insert a (completed_work jobs dependencies select i))"
     if "work_ready jobs dependencies (completed_work jobs dependencies select i) a" for a
     using Suc.IH that unfolding work_ready_def ordered_work_def by blast
  with Suc.IH show ?case by (auto simp: Let_def split: option.splits)
qed

lemma completed_work_change:
  "(completed_work jobs dependencies select (Suc i) = completed_work jobs dependencies select i) \<or>
   (\<exists>a. select i = Some a \<and> work_ready jobs dependencies (completed_work jobs dependencies select i) a \<and>
      completed_work jobs dependencies select (Suc i) = insert a (completed_work jobs dependencies select i))"
  by (cases "select i") (auto simp: Let_def)

theorem bounded_service_finishes_plan:
  assumes service: "bounded_service jobs dependencies select delay horizon"
    and valid: "\<And>before batch after a. waves = before @ batch # after \<Longrightarrow> a \<in> batch \<Longrightarrow>
       a \<in> jobs \<and> dependencies a \<subseteq> \<Union>(set before)"
    and prefix: "waves = before @ rest"
    and time: "length before * delay \<le> horizon"
  shows "\<Union>(set before) \<subseteq> completed_work jobs dependencies select (length before * delay)"
  using prefix time
proof (induction before arbitrary: rest rule: rev_induct)
  case Nil
  show ?case by simp
next
  case (snoc batch before)
  let ?i = "length before * delay"
  have shape: "waves = before @ batch # rest" using snoc.prems(1) by simp
  have horizon: "?i + delay \<le> horizon" using snoc.prems(2) by simp
  have prior: "\<Union>(set before) \<subseteq> completed_work jobs dependencies select ?i"
    by (rule snoc.IH[OF shape]) (use horizon in simp)
  have "batch \<subseteq> completed_work jobs dependencies select (?i + delay)"
    by (rule bounded_service_finishes_group[OF service horizon])
      (use valid[OF shape] prior in blast)+
  with prior completed_work_mono[of ?i "?i + delay" jobs dependencies select] show ?case
    by (auto simp: add.commute)
qed

end
