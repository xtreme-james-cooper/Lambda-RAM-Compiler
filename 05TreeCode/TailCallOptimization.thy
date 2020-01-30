theory TailCallOptimization
  imports TreeCode "../00Utils/Iteration"
begin

fun tco :: "tree_code list \<Rightarrow> tree_code list" where
  "tco [] = []"
| "tco (TApply # TReturn # cd) = TJump # tco cd"
| "tco (TPushLam cd' # cd) = TPushLam (tco cd') # tco cd"
| "tco (op # cd) = op # tco cd"

primrec tco_val :: "tclosure \<Rightarrow> tclosure" where
  "tco_val (TConst k) = TConst k"
| "tco_val (TLam t cd) = TLam t (tco cd)"

primrec tco_state :: "tree_code_state \<Rightarrow> tree_code_state" where
  "tco_state (TS vs envs cd) = TS (map tco_val vs) (map (map tco_val) envs) (tco cd)"

fun untco :: "tree_code list \<Rightarrow> tree_code list" where
  "untco [] = []"
| "untco (TJump # cd) = TApply # TReturn # untco cd"
| "untco (TPushLam cd' # cd) = TPushLam (untco cd') # untco cd"
| "untco (op # cd) = op # untco cd"

primrec untco_val :: "tclosure \<Rightarrow> tclosure" where
  "untco_val (TConst k) = TConst k"
| "untco_val (TLam t cd) = TLam t (untco cd)"

primrec untco_state :: "tree_code_state \<Rightarrow> tree_code_state" where
  "untco_state (TS vs envs cd) = TS (map untco_val vs) (map (map untco_val) envs) (untco cd)"

fun no_jumps :: "tree_code list \<Rightarrow> bool" where
  "no_jumps [] = True"
| "no_jumps (TJump # cd) = False"
| "no_jumps (TPushLam cd' # cd) = (no_jumps cd' \<and> no_jumps cd)"
| "no_jumps (op # cd) = no_jumps cd"

primrec no_jumps_val :: "tclosure \<Rightarrow> bool" where
  "no_jumps_val (TConst k) = True"
| "no_jumps_val (TLam t cd) = no_jumps cd"

primrec no_jumps_state :: "tree_code_state \<Rightarrow> bool" where
  "no_jumps_state (TS vs envs cd) = 
    (list_all no_jumps_val vs \<and> list_all (list_all no_jumps_val) envs \<and> no_jumps cd)"

fun no_unjumps :: "tree_code list \<Rightarrow> bool" where
  "no_unjumps [] = True"
| "no_unjumps (TApply # TReturn # cd) = False"
| "no_unjumps (TPushLam cd' # cd) = (no_unjumps cd' \<and> no_unjumps cd)"
| "no_unjumps (op # cd) = no_unjumps cd"

primrec no_unjumps_val :: "tclosure \<Rightarrow> bool" where
  "no_unjumps_val (TConst k) = True"
| "no_unjumps_val (TLam t cd) = no_unjumps cd"

primrec no_unjumps_state :: "tree_code_state \<Rightarrow> bool" where
  "no_unjumps_state (TS vs envs cd) = 
    (list_all no_unjumps_val vs \<and> list_all (list_all no_unjumps_val) envs \<and> no_unjumps cd)"

lemma [simp]: "no_unjumps (tco cd)"
proof (induction cd rule: tco.induct)
  case ("4_27" cd)
  thus ?case by (cases cd rule: tco.cases) simp_all
qed simp_all

lemma [simp]: "no_jumps (untco cd)"
  by (induction cd rule: tco.induct) simp_all

lemma [simp]: "no_jumps cd \<Longrightarrow> untco (tco cd) = cd"
  by (induction cd rule: tco.induct) simp_all

lemma [simp]: "no_jumps_val v \<Longrightarrow> untco_val (tco_val v) = v"
  by (induction v) simp_all

lemma [simp]: "list_all no_jumps_val vs \<Longrightarrow> map (untco_val \<circ> tco_val) vs = vs"
  by (induction vs) simp_all

lemma [simp]: "list_all (list_all no_jumps_val) vss \<Longrightarrow> map (map (untco_val \<circ> tco_val)) vss = vss"
  by (induction vss) simp_all

lemma [simp]: "no_jumps_state \<Sigma> \<Longrightarrow> untco_state (tco_state \<Sigma>) = \<Sigma>"
  by (induction \<Sigma>) simp_all

lemma [simp]: "no_unjumps cd \<Longrightarrow> tco (untco cd) = cd"
  by (induction cd rule: tco.induct) simp_all

lemma [simp]: "no_unjumps_val v \<Longrightarrow> tco_val (untco_val v) = v"
  by (induction v) simp_all

lemma [simp]: "list_all no_unjumps_val vs \<Longrightarrow> map (tco_val \<circ> untco_val) vs = vs"
  by (induction vs) simp_all

lemma [simp]: "list_all (list_all no_unjumps_val) vss \<Longrightarrow> map (map (tco_val \<circ> untco_val)) vss = vss"
  by (induction vss) simp_all

lemma [simp]: "no_unjumps_state \<Sigma> \<Longrightarrow> tco_state (untco_state \<Sigma>) = \<Sigma>"
  by (induction \<Sigma>) simp_all

theorem correcttco [simp]: "\<Sigma> \<leadsto>\<^sub>t \<Sigma>' \<Longrightarrow> tco_state \<Sigma> \<leadsto>\<^sub>t tco_state \<Sigma>'"
  by simp

theorem completetco [simp]: "tco_state \<Sigma> \<leadsto>\<^sub>t \<Sigma>' \<Longrightarrow> \<exists>\<Sigma>''. \<Sigma> \<leadsto>\<^sub>t \<Sigma>'' \<and> \<Sigma>' = tco_state \<Sigma>''"
  by simp

lemma iter_tco_eval [simp]: "iter (\<leadsto>\<^sub>t) \<Sigma> \<Sigma>' \<Longrightarrow> iter (\<leadsto>\<^sub>t) (tco_state \<Sigma>) (tco_state \<Sigma>')"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) (simp, metis iter_step correcttco)

end