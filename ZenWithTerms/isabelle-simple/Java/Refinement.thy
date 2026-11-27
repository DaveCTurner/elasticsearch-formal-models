theory Refinement
  imports "Simulation/Disk" "Simulation/Election" "Simulation/Client_Value" "Simulation/Publish_Request" "Simulation/Publish_Response_Commit"
begin


section \<open>Every call is simulated\<close>

text \<open>
  A Java call that respects the caller contract is simulated by at most one transition of the
  abstract model. A call that changes the persisted state of a node, or that publishes or commits,
  is a transition. A call that the class rejects, or that only changes the transient state of a
  node, is a stutter: the abstract state does not change.
\<close>

context simulation
begin

theorem simulate_call:
  assumes contract: "caller_contract initial_configuration initial_value state action"
  shows "\<exists>next_abstract_state.
           (next_abstract_state = abstract_state
            \<or> abstract_model.transition initial_configuration abstract_state next_abstract_state)
           \<and> linked initial_configuration (java_call state action) next_abstract_state"
proof (cases action)
  case (Java_Set_Initial_State node initial_position new_value initial_accepted_config initial_committed_config)
  then have contract_for_case:
    "caller_contract
         initial_configuration
         initial_value
         state
         (Java_Set_Initial_State
              node
              initial_position
              new_value
              initial_accepted_config
              initial_committed_config)"
    using contract by simp
  then show ?thesis using simulate_set_initial_state[OF contract_for_case] Java_Set_Initial_State by simp
next
  case (Java_Handle_Start_Join voter candidate new_term)
  then have contract_for_case:
    "caller_contract
         initial_configuration
         initial_value
         state
         (Java_Handle_Start_Join voter candidate new_term)"
    using contract by simp
  then show ?thesis using simulate_handle_start_join[OF contract_for_case] Java_Handle_Start_Join by simp
next
  case (Java_Handle_Join voter voter_role candidate join_term voter_position)
  then have contract_for_case:
    "caller_contract
         initial_configuration
         initial_value
         state
         (Java_Handle_Join voter voter_role candidate join_term voter_position)"
    using contract by simp
  then show ?thesis using simulate_handle_join[OF contract_for_case] Java_Handle_Join by simp
next
  case (Java_Handle_Client_Value leader new_term version new_value new_config previous_config)
  then have contract_for_case:
    "caller_contract
         initial_configuration
         initial_value
         state
         (Java_Handle_Client_Value leader new_term version new_value new_config previous_config)"
    using contract by simp
  then show ?thesis using simulate_handle_client_value[OF contract_for_case] Java_Handle_Client_Value by simp
next
  case (Java_Handle_Publish_Request node request new_value)
  then have contract_for_case:
    "caller_contract
         initial_configuration
         initial_value
         state
         (Java_Handle_Publish_Request node request new_value)"
    using contract by simp
  then show ?thesis using simulate_handle_publish_request[OF contract_for_case] Java_Handle_Publish_Request by simp
next
  case (Java_Handle_Publish_Response voter voter_role leader position)
  then have contract_for_case:
    "caller_contract
         initial_configuration
         initial_value
         state
         (Java_Handle_Publish_Response voter voter_role leader position)"
    using contract by simp
  then show ?thesis using simulate_handle_publish_response[OF contract_for_case] Java_Handle_Publish_Response by simp
next
  case (Java_Handle_Commit node leader position)
  then have contract_for_case:
    "caller_contract
         initial_configuration
         initial_value
         state
         (Java_Handle_Commit node leader position)"
    using contract by simp
  then show ?thesis using simulate_handle_commit[OF contract_for_case] Java_Handle_Commit by simp
next
  case (Java_Restart node new_role new_value)
  then have contract_for_case:
    "caller_contract
         initial_configuration
         initial_value
         state
         (Java_Restart node new_role new_value)"
    using contract by simp
  then show ?thesis using simulate_restart_node[OF contract_for_case] Java_Restart by simp
next
  case (Java_Persist_Term node)
  then have contract_for_case:
    "caller_contract initial_configuration initial_value state (Java_Persist_Term node)"
    using contract by simp
  then show ?thesis using simulate_persist_term[OF contract_for_case] Java_Persist_Term by simp
next
  case (Java_Persist_State node)
  then have contract_for_case:
    "caller_contract initial_configuration initial_value state (Java_Persist_State node)"
    using contract by simp
  then show ?thesis using simulate_persist_state[OF contract_for_case] Java_Persist_State by simp
qed

end

theorem java_dynamic_refinement:
  assumes reach: "java_reachable initial_configuration initial_value versions state"
  shows "\<exists>abstract_state. abstract_model.dynamic_reachable initial_configuration abstract_state
                          \<and> linked initial_configuration state abstract_state"
  using reach
proof (induction rule: java_reachable.induct)
  case init
  show ?case by (intro exI[of _ "abstract_model.bootstrapped initial_configuration"] conjI)
      (rule abstract_model.dynamic_reachable.boot[OF init.hyps(2)], rule linked_initial)
next
  case (advance state action)
  then obtain abstract_state where abstract_state:
    "abstract_model.dynamic_reachable initial_configuration abstract_state"
    "linked initial_configuration state abstract_state" by blast
  show ?case
  proof (cases "java_call state action = state")
    case True
    with abstract_state show ?thesis by (intro exI[of _ abstract_state]) simp
  next
    case False
    have nonempty: "initial_configuration \<noteq> {}"
      using abstract_state(1) abstract_model.dynamic_reachable_nonempty by blast
    interpret simulation initial_configuration state abstract_state by (unfold_locales; fact)
    from simulate_call[OF advance.hyps(2)[rule_format, OF False]]
    obtain next_abstract_state where
      step: "next_abstract_state = abstract_state
             \<or> abstract_model.transition initial_configuration abstract_state next_abstract_state"
      and link: "linked initial_configuration (java_call state action) next_abstract_state" by blast
    have "abstract_model.dynamic_reachable initial_configuration next_abstract_state"
      using abstract_state(1) step by (auto intro: abstract_model.dynamic_reachable.advance)
    with link show ?thesis by blast
  qed
qed

end
