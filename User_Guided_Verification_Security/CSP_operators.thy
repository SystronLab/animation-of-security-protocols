section \<open> Extra CSP operators to support verification of security protocols \<close>
theory CSP_operators
  imports "Interaction_Trees.ITree_Extraction"
          "Interaction_Trees.ITree_Deadlock"
          "ITree_UTP.ITree_CSP"

begin

unbundle Z_Relation_Syntax

subsection \<open> List functions \<close>
primrec list_diff :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"list_diff [] ys = []" |
"list_diff (x#xs) ys = (if x \<in> (set ys) then (list_diff xs ys) else (x # list_diff xs ys))"

primrec list_inter :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"list_inter [] ys = []" |
"list_inter (x#xs) ys = (if x \<in> (set ys) then (x # list_inter xs ys) else (list_inter xs ys))"

subsection \<open> CSP processes \<close>

definition par_hide where
"par_hide P s Q = (hide (P \<parallel>\<^bsub> s \<^esub> Q) s)"

text \<open> Events are hidden based on their order in a list. \<close>
definition hidep (infixl "\<setminus>\<^sub>p" 90) where 
"hidep P es = foldl (\<lambda> Q e. hide Q {e}) P es"

definition par_hidep where
"par_hidep P s Q = (hidep (P \<parallel>\<^bsub> set s \<^esub> Q) s)"

text \<open> A process's state must be discarded before being in parallel composition. \<close>
definition discard_state where
"discard_state P = do {P ; skip}"

text \<open> @{text "outp_choice_from_list c P A"} for each element v of A, output v on channel c and then behave like P(v), 
  similar to an index external choice @{text "[]v:A @ (c!v ; P(v))"} if B is distinct. \<close>
definition outp_choice_from_list :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> ('e, 'b) itree) \<Rightarrow> 'a list \<Rightarrow> ('e, 'b) itree" where
"outp_choice_from_list c P A = Vis (pfun_of_alist (map (\<lambda>x. (build\<^bsub>c\<^esub> x, P x)) A))"

definition outp_choice_from_set :: "('a \<Longrightarrow>\<^sub>\<triangle> 'e) \<Rightarrow> ('a \<Rightarrow> ('e, 'b) itree) \<Rightarrow> 'a set \<Rightarrow> ('e, 'b) itree" where
"outp_choice_from_set c P A = Vis (\<lambda> a \<in> build\<^bsub>c\<^esub> ` A \<bullet> P (the (match\<^bsub>c\<^esub> a)))"

lemma outp_choice_from_list_code [code_unfold]:
  "wb_prism c \<Longrightarrow> outp_choice_from_set c P (set xs) = outp_choice_from_list c P xs"
  unfolding outp_choice_from_list_def outp_choice_from_set_def
  by (simp only: set_map [THEN sym] inter_set_filter pabs_set filter_map comp_def, simp add: comp_def)

primrec inter_csp_list :: "(('e, 'a) itree) list \<Rightarrow> ('e, unit) itree" where
"inter_csp_list [] = skip" |
"inter_csp_list (P#Ps) = (do {P;skip} \<interleave> inter_csp_list Ps)"

(* Alternative definition using foldl 
definition inter_csp_list' :: "(('e, 'a) itree) list \<Rightarrow> ('e, unit) itree" where
"inter_csp_list' Px = foldl (\<lambda>q p. (do {p ; skip} \<interleave> q)) skip Px"
*)

definition indexed_inter_csp_list :: "'a list \<Rightarrow> ('a \<Rightarrow> (('e, _) itree)) \<Rightarrow> ('e, unit) itree" ("\<interleave>\<^bsub>_\<^esub> @ _" [55, 56] 56)
  where "indexed_inter_csp_list A Px = inter_csp_list (map Px A)"

primrec seq_csp_list :: "(('e, 'a) htree) list \<Rightarrow> ('e, 'a) htree" where
"seq_csp_list [] s = Ret s" |
"seq_csp_list (P#Ps) s = (P s \<bind> (seq_csp_list Ps))"

definition indexed_seq_csp_list :: "'a list \<Rightarrow> ('a \<Rightarrow> ('e, 'b) htree) \<Rightarrow> ('e, 'b) htree" (";\<^bsub>_\<^esub> @ _" [55, 56] 56)
  where "indexed_seq_csp_list A Ps s = seq_csp_list (map Ps A) s"

end
