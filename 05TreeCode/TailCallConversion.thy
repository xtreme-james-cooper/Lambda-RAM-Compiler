theory TailCallConversion
  imports TailCall TreeCode
begin

fun add_tail_calls :: "tree_code list \<Rightarrow> tail_code list" where
  "add_tail_calls [] = []"
| "add_tail_calls (TLookup x # cd) = 
    TCLookup x # (if cd = [] then [TCReturn] else add_tail_calls cd)"
| "add_tail_calls (TPushCon k # cd) = 
    TCPushCon k # (if cd = [] then [TCReturn] else add_tail_calls cd)"
| "add_tail_calls (TPushLam cd' # cd) = 
    TCPushLam (add_tail_calls cd') # (if cd = [] then [TCReturn] else add_tail_calls cd)"
| "add_tail_calls (TEnter # cd) = (if cd = [] then [TCReturn] else add_tail_calls cd)"
| "add_tail_calls (TApply # cd) = (if cd = [] then [TCTailCall] else TCApply # add_tail_calls cd)"

fun 

theorem correcth [simp]: "\<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> unheap \<Sigma>\<^sub>h \<leadsto>\<^sub>b unheap \<Sigma>\<^sub>h'"
  by simp

theorem completeh [simp]: "tail_callify \<Sigma>\<^sub>t \<leadsto>\<^sub>b \<Sigma>\<^sub>t\<^sub>c' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>h'. \<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<and> \<Sigma>\<^sub>b' = unheap \<Sigma>\<^sub>h'"
  by simp


end