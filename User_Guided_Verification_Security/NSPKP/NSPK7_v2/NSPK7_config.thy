subsection \<open> Configuration for NSPK7 \<close>
theory NSPK7_config
  imports "ITree_Security.Sec_Messages"
begin
type_synonym max_agents = 2
type_synonym max_pks = 4
type_synonym max_sks = 4
type_synonym max_nonces = 4
type_synonym max_expg = 1
type_synonym max_bitmasks = 1
type_synonym max_bitmask_length = 1

type_synonym dnonce = "max_nonces dnonce"
type_synonym dmsg = "(max_agents, max_nonces, max_pks, max_sks, max_expg, max_bitmasks, max_bitmask_length) dmsg"
type_synonym dagent = "max_agents dagent"
type_synonym dkey = "(max_pks, max_sks) dkey"
type_synonym chan = "(max_agents, max_nonces, max_pks, max_sks, max_expg, max_bitmasks, max_bitmask_length) chan"

subsection \<open> Configuration and general definitions \<close>
abbreviation "Alice \<equiv> Agent (nmk 0) :: dagent"
abbreviation "Bob \<equiv> Agent (nmk 1) :: dagent"
text \<open> The following definitions exclude server's. \<close>
abbreviation "AllAgents' \<equiv> [Alice, Bob, Intruder] :: dagent list"
abbreviation "AllAgentsLst' \<equiv> AgentsLst AllAgents' :: dmsg list"
abbreviation "AllNonces' \<equiv> [nmk 0, nmk 1, nmk 2] :: dnonce list"
abbreviation "AllNoncesLst' \<equiv> NoncesLst AllNonces' :: dmsg list"
abbreviation "AllPKs' \<equiv> [Kp (nmk 0), Kp (nmk 1), Kp (nmk 2)] :: dkey list"
abbreviation "AllPKsLst' \<equiv> PKsLst AllPKs' :: dmsg list"
abbreviation "AllSKs' \<equiv> [Ks (nmk 0), Ks (nmk 1), Ks (nmk 2)] :: dkey list"
abbreviation "AllSKsLst' \<equiv> SKsLst AllSKs' :: dmsg list"

abbreviation NonceMap :: "dagent \<Zpfun> dnonce"  where 
"NonceMap \<equiv> {Alice \<mapsto> nmk 0, Bob \<mapsto> nmk 1, Intruder \<mapsto> nmk 2, Server \<mapsto> nmk 3}"

abbreviation SKeyMap :: "dagent \<Zpfun> dkey"  where
"SKeyMap \<equiv> {Alice \<mapsto> Ks (nmk 0), Bob \<mapsto> Ks (nmk 1), Intruder \<mapsto> Ks (nmk 2), Server \<mapsto> Ks (nmk 3)}"
(*
abbreviation PKeyMap :: "dagent \<Zpfun> dkey"  where 
"PKeyMap \<equiv> {Alice \<mapsto> Kp (nmk 0), Bob \<mapsto> Kp (nmk 1), Intruder \<mapsto> Kp (nmk 2), Server \<mapsto> Kp (nmk 3)}"
*)

definition pks :: "dagent \<Rightarrow> dkey" where
"pks a = pk_of_sk (SKeyMap(a))"

abbreviation "MSK A \<equiv> MK (SKeyMap A)"
abbreviation "MPK A \<equiv> MK (pks A)"

abbreviation "Secrets_Nonces \<equiv> removeAll (MNon (NonceMap Intruder)) AllNoncesLst'"
abbreviation "Secrets_SKs \<equiv> removeAll (MK (Ks (NonceMap Intruder))) AllSKsLst'"
definition "AllSecrets = ((Secrets_Nonces @ Secrets_SKs) :: dmsg list)"

value "AllSecrets"

definition InitKnows :: "dmsg list" where 
"InitKnows = AllAgentsLst @ AllPKsLst' @ [MNon (NonceMap Intruder), MSK Intruder, MPK Intruder]"

value "InitKnows"

end
