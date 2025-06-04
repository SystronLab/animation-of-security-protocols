subsection \<open> Configuration for NSPK3 \<close>
theory NSWJ3_config
  imports "ITree_Security.Sec_Messages"
begin
type_synonym max_agents = 2
type_synonym max_pks = 4
type_synonym max_sks = 4
type_synonym max_nonces = 4
type_synonym max_expg = 1
type_synonym max_bitmasks = 3
type_synonym max_bitmask_length = 2

type_synonym dnonce = "max_nonces dnonce"
type_synonym dmsg = "(max_agents, max_nonces, max_pks, max_sks, max_expg, max_bitmasks, max_bitmask_length) dmsg"
type_synonym dagent = "max_agents dagent"
type_synonym dkey = "(max_pks, max_sks) dkey"
type_synonym chan = "(max_agents, max_nonces, max_pks, max_sks, max_expg, max_bitmasks, max_bitmask_length) chan"
type_synonym dbitmask = "(max_bitmasks, max_bitmask_length) dbitmask"

subsection \<open> Configuration and general definitions \<close>
abbreviation "Alice \<equiv> Agent (nmk 0) :: dagent"
abbreviation "Bob \<equiv> Agent (nmk 1) :: dagent"
abbreviation "AllAgents' \<equiv> [Alice, Bob, Intruder] :: dagent list"
abbreviation "AllAgentsButIntruder' \<equiv> [Alice, Bob]"
abbreviation "AllAgentsLst' \<equiv> AgentsLst AllAgents' :: dmsg list"
abbreviation "AllNonces' \<equiv> [nmk 0, nmk 1, nmk 2] :: dnonce list"
abbreviation "AllNoncesLst' \<equiv> NoncesLst AllNonces' :: dmsg list"
abbreviation "AllPKs' \<equiv> [Kp (nmk 0), Kp (nmk 1), Kp (nmk 2)] :: dkey list"
abbreviation "AllPKsLst' \<equiv> PKsLst AllPKs' :: dmsg list"
abbreviation "AllSKs' \<equiv> [Ks (nmk 0), Ks (nmk 1), Ks (nmk 2)] :: dkey list"
abbreviation "AllSKsLst' \<equiv> SKsLst AllSKs' :: dmsg list"
(* For this protocol, we use the same bits (nmk 1) for jamming as watermarking *)
abbreviation "AllBitms' \<equiv> [Null, Bm (nmk 0) (nmk 1), Bm (nmk 1) (nmk 1), Bm (nmk 2) (nmk 1)] :: dbitmask list"
abbreviation "AllBitmsLst' \<equiv> BitMLst AllBitms' :: dmsg list"

text \<open> All pairs of agents that form a communication from a source to a destination \<close>
definition "AllOtherAgents A \<equiv> [B. B \<leftarrow> AllAgentsButIntruder', B \<noteq> A]"
definition "AllCommsAgents = [(A, B). A \<leftarrow> AllAgentsButIntruder', B \<leftarrow> AllOtherAgents A]"
definition "AllOtherAgents' A \<equiv> [B. B \<leftarrow> AllAgents', B \<noteq> A]"
definition "AllCommsAgents' = [(A, B). A \<leftarrow> AllAgents', B \<leftarrow> AllOtherAgents' A]"

abbreviation NonceMap :: "dagent \<Zpfun> dnonce"  where 
"NonceMap \<equiv> {Alice \<mapsto> nmk 0, Bob \<mapsto> nmk 1, Intruder \<mapsto> nmk 2}"

abbreviation bitmask_map :: "dagent \<Zpfun> dbitmask"  where 
"bitmask_map \<equiv> {Alice \<mapsto> Bm (nmk 0) (nmk 1), Bob \<mapsto> Bm (nmk 1) (nmk 1), Intruder \<mapsto> Bm (nmk 2) (nmk 1)}"

(*
abbreviation SKeyMap :: "dagent \<Zpfun> dkey"  where
"SKeyMap \<equiv> {Alice \<mapsto> Ks (nmk 0), Bob \<mapsto> Ks (nmk 1), Intruder \<mapsto> Ks (nmk 2)}"

abbreviation PKeyMap :: "dagent \<Zpfun> dkey"  where 
"PKeyMap \<equiv> {Alice \<mapsto> Kp (nmk 0), Bob \<mapsto> Kp (nmk 1), Intruder \<mapsto> Kp (nmk 2), Server \<mapsto> Kp (nmk 3)}"

definition pks :: "dagent \<Rightarrow> dkey" where
"pks a = pk_of_sk (SKeyMap(a))"

abbreviation "MSK A \<equiv> MK (SKeyMap A)"
abbreviation "MPK A \<equiv> MK (pks A)"
*)

text \<open> @{text "Eve1"} for @{text "{Alice \<mapsto> True, Bob \<mapsto> False}"}, 
  @{text "Eve2"} for @{text "{Alice \<mapsto> False, Bob \<mapsto> True}"},
  @{text "Eve3"} for @{text "{Alice \<mapsto> True, Bob \<mapsto> True}"},
  @{text "Eve4"} for @{text "{Alice \<mapsto> False, Bob \<mapsto> False}"},
\<close>
datatype deve = Eve1 | Eve2 | Eve3 | Eve4
(*
instantiation deve :: enum
begin

definition enum_deve :: "deve list" where
"enum_deve = [Eve1, Eve2, Eve3]"

definition enum_all_deve :: "(deve \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_deve P = (\<forall>b :: deve \<in> set enum_class.enum. P b)"

definition enum_ex_deve :: "(deve \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_deve P = (\<exists>b :: deve \<in> set enum_class.enum. P b)"

instance 
  apply (intro_classes)
  prefer 2
  apply (simp_all add: enum_deve_def)+
  using deve.exhaust apply blast
  apply (simp_all add: enum_deve_def enum_all_deve_def enum_ex_deve_def)
  apply (auto)
  apply (metis deve.exhaust)
  by (metis deve.exhaust)
end
*)

text \<open> Different spatial locations of an eavesdropper in terms of jamming ranges of Alice and Bob\<close>
abbreviation intruder_in_range_map :: "deve \<Rightarrow> dagent \<Zpfun> bool"  where 
"intruder_in_range_map eve \<equiv> case eve of 
  Eve1 \<Rightarrow> {Alice \<mapsto> True, Bob \<mapsto> False} |
  Eve2 \<Rightarrow> {Alice \<mapsto> False, Bob \<mapsto> True} |
  Eve3 \<Rightarrow> {Alice \<mapsto> True, Bob \<mapsto> True} |
  Eve4 \<Rightarrow> {Alice \<mapsto> False, Bob \<mapsto> False}
"

definition "mkbma A \<equiv> (MBitm ((bitmask_map(A))))"
abbreviation "bm_or_null_b b A \<equiv> (if b then mkbma A else MBitm Null)"
abbreviation "bm_or_null A eve \<equiv> bm_or_null_b (intruder_in_range_map eve A) A"

abbreviation "Secrets_Nonces \<equiv> removeAll (MNon (NonceMap Intruder)) AllNoncesLst'"
definition "AllSecrets = ((Secrets_Nonces @ [mkbma Alice, mkbma Bob]) :: dmsg list)"

value "AllSecrets"

definition InitKnows :: "dmsg list" where 
"InitKnows = AllAgentsLst' @ [MNon (NonceMap Intruder), MBitm (bitmask_map(Intruder))]"

value "InitKnows"

end
