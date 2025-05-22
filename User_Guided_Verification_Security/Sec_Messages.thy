section \<open> The definition of messages for the modelling of security protocols \<close>
theory Sec_Messages
  imports "ITree_Security.CSP_operators"
          "ITree_Security.FSNat"
begin

declare [[show_types]]

declare [[typedef_overloaded]]

subsection \<open> General definitions \<close>

subsubsection \<open> Agents \<close>
datatype ('a::len) dagent = Agent (ag: "'a fsnat") | Intruder | Server

value "ag (Agent (nmk 1):: 2 dagent)"

definition aglist :: "(('a::len) dagent) list" where
"aglist = map Agent (fsnatlist)"

lemma distinct_aglist: "distinct (aglist)"
  apply (simp add: aglist_def fsnatlist_def distinct_map inj_on_def)
  using fsnat_of_nat_inject by blast

lemma dagent_univ: 
  shows "set ([Intruder, Server] @ aglist) = UNIV"
  apply (simp add: aglist_def fsnatlist_def image_def)
  apply (auto)
  by (metis dagent.exhaust_sel nat_of_fsnat nat_of_fsnat_inverse)

instantiation dagent :: (len) enum
begin
definition enum_dagent :: "('a::len) dagent list" where
"enum_dagent = [Intruder, Server] @ aglist"

definition enum_all_dagent :: "(('a::len) dagent \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_dagent P = (\<forall>b :: 'a dagent \<in> set enum_class.enum. P b)"

definition enum_ex_dagent :: "(('a::len)dagent \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_dagent P = (\<exists>b :: 'a dagent \<in> set enum_class.enum. P b)"

instance
  apply (intro_classes)
  prefer 2
  apply (simp_all add: enum_dagent_def)+
  using distinct_aglist apply (metis aglist_def dagent.distinct(1) dagent.distinct(3) ex_map_conv)
  apply (simp_all add: enum_dagent_def enum_all_dagent_def enum_ex_dagent_def)
  apply (auto)
  using dagent_univ apply auto[1]
  by (metis UNIV_I UnE dagent_univ empty_set equals0D set_ConsD set_append)+
end

value "enum_class.enum::(2 dagent) list"

subsubsection \<open> Nonces \<close>

type_synonym ('a) dnonce = "fsnat['a]"

type_synonym ('a) dexpg = "fsnat['a]"

subsubsection \<open> Keys \<close>
datatype ('k::len,'s::len) dkey = Kp (kp: "fsnat['k]") | Ks (ks: "fsnat['s]")

fun is_Ks :: "('k::len, 's::len) dkey \<Rightarrow> \<bool>"  where
"is_Ks (Kp _) = False" | 
"is_Ks (Ks _) = True"

definition sk_of_pk where 
"sk_of_pk pk = Ks (kp (pk))"

definition pk_of_sk where 
"pk_of_sk pk = Kp (ks (pk))"

definition pklist :: "(('k::len,'s::len) dkey) list" where
"pklist = map Kp (fsnatlist) @ map Ks (fsnatlist)"

lemma dkey_univ:  
  shows "set pklist = UNIV"
  apply (simp add: pklist_def fsnatlist_def)
  apply (auto)
  by (smt (verit, del_insts) dkey.exhaust image_eqI nat_of_fsnat nat_of_fsnat_inverse)

instantiation dkey :: (len, len) enum
begin
definition enum_dkey :: "('k::len, 's::len) dkey list" where
"enum_dkey = pklist"

definition enum_all_dkey :: "(('k::len, 's::len) dkey \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_dkey P = (\<forall>b :: ('k::len, 's::len) dkey \<in> set enum_class.enum. P b)"

definition enum_ex_dkey :: "(('k::len, 's::len) dkey \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_dkey P = (\<exists>b :: ('k::len, 's::len) dkey \<in> set enum_class.enum. P b)"

instance
proof (intro_classes)
  show univ_eq: "UNIV = set (enum_class.enum :: ('k::len, 's::len) dkey list)"
    by (simp add: dkey_univ enum_dkey_def image_def enum_fsnat_def fsnatlist_def)

  show "distinct (enum_class.enum :: ('k::len, 's::len) dkey list)"
    apply (simp add: enum_dkey_def enum_fsnat_def fsnatlist_def pklist_def)
    apply (simp add: distinct_map, auto)
    apply (smt (verit) atLeastLessThan_iff comp_apply dkey.sel(1) inj_onI mod_less fsnat_of_nat_inverse)
    by (smt (verit) atLeastLessThan_iff comp_apply dkey.sel(2) inj_onI mod_less fsnat_of_nat_inverse)
  
  fix P :: "('k::len, 's::len) dkey \<Rightarrow> bool"
  show "enum_class.enum_all P = Ball UNIV P"
    and "enum_class.enum_ex P = Bex UNIV P" 
    by (simp_all add: univ_eq enum_all_dkey_def enum_ex_dkey_def)
qed
end

subsubsection \<open> Bitmask \<close>
text \<open> In @{text "dbitmask"}, we use the first fsnat to differentiate different bitmasks (how many 
bitmasks), and the second fsnat to represent the number of samples used for watermarking and jamming. 
So @{text "(3, 4) dbitmask"} denotes a type with three bitmasks and each bitmask having samples up to 4. 
We usually use 4 for watermarking and then may choose a smaller number such as 3 for jamming to save 
energy. \<close>
datatype ('a::len, 'b::len) dbitmask = Null | Bm (bm: "'a fsnat") (ln: "'b fsnat")

definition bmlist :: "(('a::len, 'b::len) dbitmask) list" where
"bmlist = concat (map (\<lambda>a::fsnat['a]. map (Bm a) fsnatlist) fsnatlist)"
(* "bmlist = concat (map (\<lambda>b. map (\<lambda>l. Bm b l) (fsnatlist::(fsnat['b::len]) list)) (fsnatlist::(fsnat['a::len]) list))" *)

(* "bmlist = [Bm a b. a \<leftarrow> (fsnatlist::(fsnat['a::len]) list), b \<leftarrow> (fsnatlist::(fsnat['b::len]) list)]" *)

thm "map_concat"

value "bmlist :: (2,3) dbitmask list"

value "(Bm (nmk 3) (nmk 2)) :: (2,3) dbitmask"

lemma distinct_map_Bm_fsnatlist: "distinct (map (Bm a) fsnatlist)"
  apply (simp add: distinct_map)
  by (simp add: distinct_fsnat inj_on_def)

lemma distinct_bmlist: "distinct (bmlist)"
  apply (simp add: bmlist_def)
  apply (rule distinct_concat)
  apply (simp add: fsnatlist_def distinct_map inj_on_def)
  apply (meson fsnat_of_nat_inject len_gt_0)
  using distinct_map_Bm_fsnatlist apply auto[1]
  by force

lemma dbitmask_univ: 
  shows "set ([Null] @ bmlist) = UNIV"
  apply (simp add: bmlist_def)
  apply (auto)
  using dbitmask.exhaust_sel by (metis UNIV_I fsnatlist_univ range_eqI)

instantiation dbitmask :: (len, len) enum
begin
definition enum_dbitmask :: "('a::len, 'b::len) dbitmask list" where
"enum_dbitmask = [Null] @ bmlist"

definition enum_all_dbitmask :: "(('a::len, 'b::len) dbitmask \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_dbitmask P = (\<forall>b :: ('a::len, 'b::len) dbitmask \<in> set enum_class.enum. P b)"

definition enum_ex_dbitmask :: "(('a::len, 'b::len) dbitmask \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_dbitmask P = (\<exists>b :: ('a::len, 'b::len) dbitmask \<in> set enum_class.enum. P b)"

instance
  apply (intro_classes)
  prefer 2
  apply (simp_all add: enum_dbitmask_def)+
  apply (rule conjI)
  apply (simp add: bmlist_def)
  apply blast
  apply (simp add: distinct_bmlist)
  apply (simp_all add: enum_dbitmask_def enum_all_dbitmask_def enum_ex_dbitmask_def)
  apply (auto)
  using dbitmask_univ apply auto[1]
  by (metis UNIV_I UnE dbitmask_univ empty_set equals0D set_ConsD set_append)+
end

instantiation dbitmask :: (len, len) order
begin

lift_definition less_eq_dbitmask :: "('a::len, 'b::len) dbitmask \<Rightarrow> ('a::len, 'b::len) dbitmask \<Rightarrow> bool"
  is "\<lambda>a b. case a of Null \<Rightarrow> True | Bm x1 y1 \<Rightarrow> (case b of Null \<Rightarrow> False | Bm x2 y2 \<Rightarrow> (x1 = x2) \<and> y1 \<le> y2)" .

lift_definition less_dbitmask :: "('a::len, 'b::len) dbitmask \<Rightarrow> ('a::len, 'b::len) dbitmask \<Rightarrow> bool"
  is "\<lambda>a b. case (a,b) of (Null, Null) \<Rightarrow> False | (Null, Bm x2 y2) \<Rightarrow> True | (Bm x1 y1, Null) \<Rightarrow> False | 
  (Bm x1 y1, Bm x2 y2) \<Rightarrow> (x1 = x2) \<and> (y1 < y2)" .

instance
  apply (standard)
  apply (simp_all add: less_eq_dbitmask_def less_dbitmask_def)
  apply (smt (verit) dbitmask.case_eq_if nless_le order_antisym_conv)
  apply (simp add: dbitmask.case_eq_if)
  apply (smt (z3) dbitmask.case_eq_if order.trans)
  by (smt (z3) dbitmask.case_eq_if dbitmask.exhaust_sel nle_le)
end

(* True *)
value "((Bm (nmk 1) (nmk 2)) :: (2,3) dbitmask) \<le> (Bm (nmk 1) (nmk 2))"
value "((Bm (nmk 1) (nmk 1)) :: (2,3) dbitmask) \<le> (Bm (nmk 1) (nmk 2))"

(* False *)
value "((Bm (nmk 3) (nmk 2)) :: (2,3) dbitmask) \<le> (Bm (nmk 1) (nmk 1))"

subsubsection \<open> Messages \<close>
datatype ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg 
=   MAg   (ma: "'a dagent")
  | MNon  (mn: "'n dnonce")
  | MK    (mk: "('k, 's) dkey")
  | MPair (mc1: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg") (mc2: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg")
  \<comment> \<open> Asymmetric encryption \<close>
  | MAEnc  (mem: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg") (mek: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg")
  \<comment> \<open> Digital signature \<close>
  | MSig  (msd: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg") (msk: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg")
  \<comment> \<open> Symmetric encryption \<close>
  | MSEnc (msem: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg") (msek: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg")
  \<comment> \<open> The base g in a modular exponentiation @{text "(g\<^sup>a mod p)"} \<close>
  | MExpg (eg: "'g dexpg")
  \<comment> \<open> The power @{text "g\<^sup>a"} in a modular exponentiation @{text "(g\<^sup>a mod p)"} \<close>
  | MModExp (mmem: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg") (mmek: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg")
  | MBitm (mbm: "('bm, 'bl) dbitmask")
  | MWat (mwm: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg") (mwb: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg")
  | MJam (mjm: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg") (mjb: "('a, 'n, 'k, 's, 'g, 'bm, 'bl) dmsg")

text \<open> Generate linorder for all these types in order to support comparison between dmsg, particularly 
for MPair to reduce the number of messages that intruder can build because we can treat 
@{text "MPair a1 a2"} and @{text "MPair a2 a1"} as the same, and 
@{text "MPair (MPair a3 a1) a2"} and @{text "MPair a2 (MPair a3 a1)"} also as the same. 
\<close>

text\<open>Concrete syntax for dmsg \<close>
syntax
  "_PairMsg" :: "['a, args] \<Rightarrow> 'a * 'b"  ("(2\<lbrace>_,/ _\<rbrace>\<^sub>m)")
  "_AEncryptMsg" :: "['a, 'a] \<Rightarrow> 'a"      ("(2{_}\<^sup>a\<^bsub>_\<^esub>)")
  "_SEncryptMsg" :: "['a, 'a] \<Rightarrow> 'a"     ("(2{_}\<^sup>s\<^bsub>_\<^esub>)")
  "_SignMsg" :: "['a, 'a] \<Rightarrow> 'a"         ("(2{_}\<^sup>d\<^bsub>_\<^esub>)")
  "_ModExpMsg" :: "['a, 'a] \<Rightarrow> 'a"       (infixl "^\<^sub>m" 50)
  "_MExpg" :: "'a \<Rightarrow> 'a" ("g\<^sub>m _")
  "_WatMsg" :: "['a, 'a] \<Rightarrow> 'a"          ("(2{_}\<^sup>w\<^bsub>_\<^esub>)")
  "_JamMsg" :: "['a, 'a] \<Rightarrow> 'a"          ("(2{_}\<^sup>j\<^bsub>_\<^esub>)")
translations
  "\<lbrace>w, x, y, z\<rbrace>\<^sub>m" \<rightleftharpoons> "\<lbrace>w, \<lbrace>x, \<lbrace>y, z\<rbrace>\<^sub>m\<rbrace>\<^sub>m\<rbrace>\<^sub>m"
  "\<lbrace>x, y, z\<rbrace>\<^sub>m" \<rightleftharpoons> "\<lbrace>x, \<lbrace>y, z\<rbrace>\<^sub>m\<rbrace>\<^sub>m"
  "\<lbrace>x, y\<rbrace>\<^sub>m" \<rightleftharpoons> "CONST MPair x y"
  "{m}\<^sup>a\<^bsub>k\<^esub>" \<rightleftharpoons> "CONST MAEnc m k"
  "{m}\<^sup>d\<^bsub>k\<^esub>" \<rightleftharpoons> "CONST MSig m k"
  "{m}\<^sup>s\<^bsub>k\<^esub>" \<rightleftharpoons> "CONST MSEnc m k"
  "m^\<^sub>me" \<rightleftharpoons> "CONST MModExp m e"
  "g\<^sub>m e"  \<rightleftharpoons> "CONST MExpg e"
  "{m}\<^sup>w\<^bsub>bm\<^esub>" \<rightleftharpoons> "CONST MWat m bm"
  "{m}\<^sup>j\<^bsub>bm\<^esub>" \<rightleftharpoons> "CONST MJam m bm"

abbreviation "mkbm m l \<equiv> MBitm (Bm (nmk m) (nmk l))"
abbreviation "mkag x \<equiv> MAg (Agent (nmk x))"
abbreviation "mknon x \<equiv> MNon (nmk x)"
abbreviation "mkpk x \<equiv> MK (Kp (nmk x))"
abbreviation "mksk x \<equiv> MK (Ks (nmk x))"

value "{MNon (nmk 1)}\<^sup>a\<^bsub>MK (Ks (nmk 1))\<^esub> :: (2,4,4,4,1,1,1) dmsg"
value "{MNon (nmk 1)}\<^sup>d\<^bsub>MK (Ks (nmk 1))\<^esub>  :: (2,4,4,4,1,1,1) dmsg"
value "\<lbrace>MNon (nmk 1), MK (Kp (nmk 1))\<rbrace>\<^sub>m  :: (2,4,4,4,1,1,1) dmsg"
value "(g\<^sub>m (nmk 1)) ^\<^sub>m (MNon (nmk 1)) ^\<^sub>m (MNon (nmk 1))  :: (2,4,4,4,1,1,1) dmsg"

definition is_MKs:: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> bool" where 
"is_MKs m = (is_MK m \<and> (is_Ks (mk m)))"

value "is_MKs ((MK (Ks (nmk 1))) :: (2,4,4,4,1,1,1) dmsg)"

paragraph \<open> Message functions \<close>
fun length:: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> nat" where
"length (MAg _) = 1" |
"length (MNon _) = 1" |
"length (MK _) = 1" |
"length (MPair m1 m2) = length m1 + length m2" |
"length (MAEnc m k) = length m" |
"length (MSig m k) = length m" |
"length (MSEnc m k) = length m" |
"length (MExpg _) = 1" |
"length (MModExp m k) = length m" |
"length (MBitm _) = 1" |
"length (MWat m k) = length m" |
"length (MJam m k) = length m"

fun num_aenc:: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> nat" where
"num_aenc (MAg _) = 0" |
"num_aenc (MNon _) = 0" |
"num_aenc (MK _) = 0" |
"num_aenc (MPair m1 m2) = max (num_aenc m1) (num_aenc m2)" |
"num_aenc (MAEnc m k) = 1 + num_aenc m" |
"num_aenc (MSig m k) = num_aenc m" |
"num_aenc (MSEnc m k) = num_aenc m" |
"num_aenc (MExpg _) = 0" |
"num_aenc (MModExp m k) = num_aenc m" |
"num_aenc (MBitm _) = 0" |
"num_aenc (MWat m k) = num_aenc m" |
"num_aenc (MJam m k) = num_aenc m"

fun atomic :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"atomic (MAg m) = [(MAg m)]" |
"atomic (MNon m) = [(MNon m)]" |
"atomic (MK m) = [(MK m)]" |
"atomic (MPair m1 m2) = List.union (atomic m1) (atomic m2)" |
"atomic (MAEnc m k) = atomic m" |
"atomic (MSig m k) = atomic m" |
"atomic (MSEnc m k) = atomic m" |
"atomic (MExpg m) = [(MExpg m)]" |
"atomic (MModExp m k) = atomic m" |
"atomic (MBitm b) = [(MBitm b)]" |
"atomic (MWat m k) = atomic m" |
"atomic (MJam m k) = atomic m"

definition atomics :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
                       ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"atomics xs = List.concat (map atomic xs)"

fun dupl :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> bool" where
"dupl (MAg _) = False" |
"dupl (MNon _) = False" |
"dupl (MK _) = False" |
"dupl (MPair m1 m2) = ((dupl m1) \<or> (dupl m2) \<or> (filter (\<lambda>s. List.member (atomic m1) s) (atomic m2) \<noteq> []))" |
"dupl (MAEnc m k) = dupl m" |
"dupl (MSig m k) = dupl m" |
"dupl (MSEnc m k) = dupl m" |
"dupl (MExpg _) = False" |
"dupl (MModExp m k) = dupl m" |
"dupl (MBitm b) = False" |
"dupl (MWat m k) = dupl m" |
"dupl (MJam m k) = dupl m"

abbreviation "dupl2 m1 m2 \<equiv> (dupl m1) \<or> (dupl m2) \<or> (filter (\<lambda>s. List.member (atomic m1) s) (atomic m2) \<noteq> [])"

text \<open> Create a MPair from a list of messages \<close>
fun create_cmp :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
                   ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg option" where
"create_cmp [] = None" |
"create_cmp (x#[y]) = Some (MPair x y)" |
"create_cmp (x#ys) = (case (create_cmp ys) of 
  None \<Rightarrow> None |
  Some y \<Rightarrow> Some (MPair x y))
"

value "create_cmp [mknon 1, mkag 1, mkpk 1, mksk 1] :: (2, 4, 4, 4, 4, 2, 2) dmsg option"

text \<open> Transform a MPair into a list of sorted messages \<close>
fun mpair_to_list :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> 
                      ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"mpair_to_list (MPair m1 m2) = List.union (mpair_to_list m1) (mpair_to_list m2)" |
"mpair_to_list a = [a]"

value "mpair_to_list (MPair 
  (MPair 
      (MSEnc (MPair (MAg (Agent (nmk 1))) (MNon (nmk 0))) (MK (Ks (nmk 0)))) 
      (MAg (Agent (nmk 0)))
  )
  (MNon (nmk 1))
) :: (2,4,4,2,2,1,1) dmsg list"


definition "extract_dkey xs = map (mk)  (filter is_MK xs)"
definition "extract_dkeys xs = (filter is_Ks (extract_dkey xs))"
definition "extract_dkeyp xs = (filter is_Kp (extract_dkey xs))"
definition "extract_nonces xs = (filter is_MNon xs)"

value "extract_dkeys [((MK (Ks (nmk 1))) :: (2,4,4,2,2,1,1) dmsg)]"

subsection \<open> Message inferences \<close>
text \<open> @{text "break_lst xs ys as"} break down a list of messages and ys is the list of messages that 
have been broken down previously, and as is the set of atomic messages (parts), used to decide if it
is necessary to carry further break down or not for an encrypted or signed message. \<close>
fun break_lst::"('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg set \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 'k::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"break_lst [] ams as = ams" |
"break_lst ((MK k)#xs) ams as = (break_lst xs (List.insert (MK k) ams) as)" |
"break_lst ((MAg A)#xs) ams as = (break_lst xs (List.insert (MAg A) ams) as)" |
"break_lst ((MNon A)#xs) ams as = (break_lst xs (List.insert (MNon A) ams) as)" |
\<comment> \<open> A and B might be mutual dependent, such as @{text "\<lbrace>{g\<^sub>m ^\<^sub>m (na)}\<^sub>s\<^bsub>SK A\<^esub> , MKp (PK A)\<rbrace>\<^sub>m"}. 
  We could proceed as follows, but now the @{text "{g\<^sub>m ^\<^sub>m (na)}\<^sub>s\<^bsub>SK A\<^esub>"} would be in the @{text "ams"} 
though it still can be breakdown.
\<close>
(* The right way might be "break_lst (A#(B#xs)) ams" but it is hard to prove it will be terminated *)
"break_lst ((MPair A B)#xs) ams as = (
    break_lst xs (remdups ((break_lst [A] ams as) @ (break_lst [B] ams as) @ ams)) as
  )" |
"break_lst ((MAEnc A (MK (Kp k)))#xs) ams as = 
  \<comment> \<open> If the corresponding private key is in as \<close>
  (if (MK (Ks k)) \<in> as then
    (if List.member ams (MK (Ks k)) then
      break_lst (A#xs) (List.insert (MAEnc A (MK (Kp k))) ams) as
    else 
      let rams = break_lst xs ams as
      in  if List.member rams (MK (Ks k)) then
          break_lst (A#xs) (List.insert (MAEnc A (MK (Kp k))) ams) as
        else
          break_lst xs (List.insert (MAEnc A (MK (Kp k))) (ams)) as
    )
  else
    break_lst xs (List.insert (MAEnc A (MK (Kp k))) (ams)) as
)" |
"break_lst ((MSig A (MK (Ks k)))#xs) ams as = 
  \<comment> \<open> If the corresponding public key is in as \<close>
  (if (MK (Kp k)) \<in> as then
    (if List.member ams (MK (Kp k)) then
      break_lst (A#xs) (List.insert (MSig A (MK (Ks k))) ams) as
    else 
      let rams = break_lst xs ams as
      in if List.member rams (MK (Kp k)) then
          \<comment> \<open> TODO: do we need to re-do it again for xs? It seems so because A may have more info. 
          Current solution is to apply @{text break_lst} twice. \<close>
          break_lst (A#xs) (List.insert (MSig A (MK (Ks k))) ams) as
        else
          break_lst xs (List.insert (MSig A (MK (Ks k))) (ams)) as
    )
  else 
    break_lst xs (List.insert (MSig A (MK (Ks k))) (ams)) as
)" |
\<comment> \<open> Particularly, we are looking at the k having a form @{text "((g\<^sub>m ^\<^sub>m a) ^\<^sub>m b)"}. 
  @{text "{m}\<^sub>S\<^bsub>((g\<^sub>m ^\<^sub>m a) ^\<^sub>m b)\<^esub> "} can be broken if (@{text "(g\<^sub>m ^\<^sub>m a)"} and @{text "b"})
  or (@{text "(g\<^sub>m ^\<^sub>m b)"} and @{text "a"}) in the messages because 
  @{text "((g\<^sub>m ^\<^sub>m a) ^\<^sub>m b)"} is equal to @{text "((g\<^sub>m ^\<^sub>m b) ^\<^sub>m a)"}.
\<close>
"break_lst ((MSEnc m k)#xs) ams as = (case k of
  \<comment> \<open> If symmetric encryption using a private key, \<close>
  (MK (Ks k)) \<Rightarrow> (if (MK (Ks k)) \<in> as then
    (if List.member ams (MK (Ks k)) then
      break_lst (m#xs) (List.insert (MSEnc m (MK (Ks k))) ams) as
    else 
      let rams = break_lst xs ams as
      in  if List.member rams (MK (Ks k)) then
          break_lst (m#xs) (List.insert (MAEnc m (MK (Ks k))) ams) as
        else
          break_lst xs (List.insert (MAEnc m (MK (Ks k))) (ams)) as
    )
  else
    break_lst xs (List.insert (MAEnc m (MK (Ks k))) (ams)) as
  ) |
  \<comment> \<open> If the key is a modular exponentiation used in Diffie-Hellman, \<close>
  (((g\<^sub>m gn) ^\<^sub>m a) ^\<^sub>m b) \<Rightarrow> 
     (if (List.member ams (((g\<^sub>m gn) ^\<^sub>m a)) \<and> List.member ams (b)) \<or> 
         (List.member ams (((g\<^sub>m gn) ^\<^sub>m b)) \<and> List.member ams (a)) \<or> 
         (List.member ams ((g\<^sub>m gn)) \<and> List.member ams (a) \<and> List.member ams (b)) then 
          break_lst (m#xs) (List.insert (MSEnc m k) ams) as
        else 
          let rams = break_lst xs ams as
          in if (List.member rams (((g\<^sub>m gn) ^\<^sub>m a)) \<and> List.member rams (b)) \<or> 
               (List.member rams (((g\<^sub>m gn) ^\<^sub>m b)) \<and> List.member rams (a)) \<or> 
               (List.member rams ((g\<^sub>m gn)) \<and> List.member rams (a) \<and> List.member rams (b)) then 
              break_lst (m#xs) (List.insert (MSEnc m k) ams) as
            else
              break_lst xs (List.insert (MSEnc m k) (ams)) as
    ) |
  \<comment> \<open> Otherwise, we won't break it \<close>
  _ \<Rightarrow> break_lst xs (List.insert (MSEnc m k) (ams)) as
) "
| 
"break_lst ((MExpg a)#xs) ams as = break_lst xs (List.insert (MExpg a) (ams)) as" |
\<comment> \<open> We cannot break anything from a^b but the message should be kept \<close>
"break_lst ((a ^\<^sub>m b)#xs) ams as = break_lst xs (List.insert (a ^\<^sub>m b) (ams)) as" |
"break_lst ((MBitm b)#xs) ams as = (break_lst xs (List.insert (MBitm b) ams) as)" |
\<comment> \<open> What can we break down from a watermarked message?
We can always know m from a watermarked message wat(m, bm)
\<close>
"break_lst (({m}\<^sup>w\<^bsub>b\<^esub> )#xs) ams as = break_lst xs (List.insert (m) (ams)) as" |
\<comment> \<open> We can break jam(m, b) if and only if we know b \<close>
"break_lst (({m}\<^sup>j\<^bsub>(MBitm b)\<^esub> )#xs) ams as = \<comment> \<open> If the corresponding bitmask is in as \<close>
  (if b \<noteq> Null then
    \<comment> \<open> m should be a watermarked message using the same bitmask but may use less bits
    \<close>
    (if is_MWat m \<and> b \<le> mbm (mwb m) \<and> (MBitm (b)) \<in> as then
      (if List.member ams (MBitm (b)) then
        break_lst (m#xs) (List.insert ({m}\<^sup>j\<^bsub>(MBitm b)\<^esub> ) ams) as
      else 
        let rams = break_lst xs ams as
        in  if List.member rams (MBitm (b)) then
            break_lst (m#xs) (List.insert ({m}\<^sup>j\<^bsub>(MBitm b)\<^esub> ) ams) as
          else
            break_lst xs (List.insert ({m}\<^sup>j\<^bsub>(MBitm b)\<^esub> ) (ams)) as
      )
    else
      \<comment> \<open> If not watermarked or ..., but the jamming bitmask is known, we still can learn the message. \<close>
      (if List.member ams (MBitm (b)) then
        break_lst (m#xs) (List.insert ({m}\<^sup>j\<^bsub>(MBitm b)\<^esub> ) ams) as
      else 
        break_lst xs (List.insert ({m}\<^sup>j\<^bsub>(MBitm b)\<^esub> ) (ams)) as
      )
    )
  else
    break_lst (m#xs) (List.insert ({m}\<^sup>j\<^bsub>(MBitm b)\<^esub> ) ams) as
)" |
"break_lst (x#xs) ams as = break_lst xs (List.insert (x) (ams)) as"

definition "breakl xs = break_lst xs [] (set (atomics xs))"

text \<open> Our strategy to deal with @{text "(MPair A B)"} is the application of breakl twice. \<close>
definition "breakm xs = 
  (let as = (set (atomics xs));
       ys = break_lst xs [] as
   in break_lst ys [] as)"

value "breakl ([MAg (Agent (nmk 1)), MAg (Agent (nmk 0))] :: (2,4,4,4,2,2,2) dmsg list)"
value "breakl ([{MAg (Agent (nmk 1))}\<^sup>a\<^bsub>(MK (Kp (nmk 1)))\<^esub> , (MK (Ks (nmk 1)))]:: (2,4,4,4,2,2,2) dmsg list)"
value "breakl ([\<lbrace>
  {(g\<^sub>m (nmk 1)) ^\<^sub>m (MNon (nmk 0))}\<^sup>d\<^bsub>(MK (Ks (nmk 1)))\<^esub> , 
  MK (Kp (nmk 1)), MAg (Agent (nmk 21)) \<rbrace>\<^sub>m] :: (2,4,4,4,2,2,2) dmsg list)"
text \<open> In the following example, we expect the signed modular exponentiation will be derived. \<close>
value "breakm ([\<lbrace> 
  {(g\<^sub>m (nmk 1)) ^\<^sub>m (MNon (nmk 0))}\<^sup>d\<^bsub>(MK (Ks (nmk 1)))\<^esub> , 
  MK (Kp (nmk 1)), 
  MAg (Agent (nmk 21)) 
\<rbrace>\<^sub>m] :: (2,4,4,4,2,2,2) dmsg list)"

value "breakl [{{(mknon 1)}\<^sup>w\<^bsub>(mkbm 0 2)\<^esub> }\<^sup>j\<^bsub>(mkbm 0 2)\<^esub> , (mkbm 0 2)] :: (2,4,4,4,2,2,2) dmsg list"

value "breakl [mkag 1, mkag 0, (mknon 0), {(mknon 1)}\<^sup>j\<^bsub>(mkbm 0 2)\<^esub> , (mkbm 0 1)] :: (2,4,4,4,2,2,2) dmsg list"

text \<open> Should @{text "(mknon 1)"} be learned. \<close>
value "breakm [mkag 1, mkag 0, (mknon 0), {(mknon 1)}\<^sup>j\<^bsub>(mkbm 0 2)\<^esub> , (mkbm 0 2)] :: (2,4,4,4,2,2,2) dmsg list"

text \<open> Assume @{text "((g\<^sub>m x) ^\<^sub>m a ^\<^sub>m b) = ((g\<^sub>m x) ^\<^sub>m b ^\<^sub>m a)"}, use this function to swap a and b. \<close>
fun swap_mod_exp :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg" where 
"swap_mod_exp ((g\<^sub>m x) ^\<^sub>m a ^\<^sub>m b) = ((g\<^sub>m x) ^\<^sub>m b ^\<^sub>m a)" |
"swap_mod_exp m = m"

(*
chantype chan = terminate :: "unit"

definition PP::"(chan, (3, 3, 3, 3, 3) dmsg list) itree" where "PP = 
(Ret (breakl [{MAg (Agent (mkagent TYPE(3) 1))}\<^sup>a\<^bsub>(MK (Kp (mkkey TYPE(3) 1)))\<^esub> , (MK (Ks (mkkey TYPE(3) 1)))]) \<box> stop)"
value (*[simp]*) "PP"
code_thms PP
export_code "PP" in Haskell
*)

(*
text \<open> @{text "pair2 xs ys l"}: pair message once for each element of @{text "xs"} with 
every element of @{text "ys"} if they are different, their length does not exceed the given @{text 
"l"} which denotes the maximum length of a composed message. 
\<close>
fun pair2 :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
    ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> nat \<Rightarrow> 
    ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"pair2 [] ys l = []" |
"pair2 (x#xs) ys l = (let cs = pair2 xs ys l in
  (map (\<lambda>n. (MPair x n)) \<comment> \<open> Sort the components in MPair \<close>
    (filter 
      \<comment> \<open> they are not the same, length won't exceed l, and they are not private keys  \<close>
      (\<lambda>y. y \<noteq> x \<and> length x + length y \<le> l \<and> \<not> dupl2 x y \<and> \<not> is_MK x \<and> \<not> is_MK y) 
    ys)
  ) @ cs)"

value "length \<lbrace>(MAg (Server))::(2,2,4,4,1) dmsg, (MNon (nmk 1))\<rbrace>\<^sub>m"
value "pair2 [MNon (nmk 1)::(2,2,4,4,1) dmsg, \<lbrace>(MAg (Agent (nmk 0))), (MNon (nmk 2))\<rbrace>\<^sub>m] 
             [MNon (nmk 2), \<lbrace>(MAg (Agent (nmk 1))), (MNon (nmk 2))\<rbrace>\<^sub>m] 3"
\<comment> \<open> We expect [] because equal or duplicate cases \<close>
value "pair2 [MNon (nmk 1)::(2,2,4,4,1) dmsg, \<lbrace>(MAg (Agent (nmk 1))), (MNon (nmk 1))\<rbrace>\<^sub>m] 
             [MNon (nmk 1), \<lbrace>(MAg (Agent (nmk 1))), (MNon (nmk 1))\<rbrace>\<^sub>m] 3"

text \<open> @{text "aenc\<^sub>1 xs ks"}: asymmetric encrypt of each element of @{text "xs"} using 
every key of @{text "ks"} \<close>
fun aenc\<^sub>1 :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> ('k, 's) dkey list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"aenc\<^sub>1 [] pks = []" |
"aenc\<^sub>1 (x#xs) pks = (if is_MKs x then aenc\<^sub>1 xs pks \<comment> \<open> Ignore private keys because we won't send private keys directly\<close>
  else (map (\<lambda>k. MAEnc x (MK k)) pks) @ aenc\<^sub>1 xs pks)"

text \<open> @{text "n"} is the limit of number of asymmetric encryption. \<close>
fun aenc\<^sub>n :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> ('k, 's) dkey list \<Rightarrow> nat \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"aenc\<^sub>n [] pks n = []" |
"aenc\<^sub>n (x#xs) pks n = (if is_MKs x \<or> num_aenc x \<ge> n then aenc\<^sub>n xs pks n \<comment> \<open> Ignore private keys because we won't send private keys directly and if the number of encryption exeeds.\<close>
  else (map (\<lambda>k. MAEnc x (MK k)) pks) @ aenc\<^sub>n xs pks n)"

value "aenc\<^sub>1 [MNon (nmk 0)::(2,2,4,4,1) dmsg, \<lbrace>(MAg (Agent (nmk 1))), (MNon (nmk 0))\<rbrace>\<^sub>m] 
  [Kp (nmk 0), Kp (nmk 1), Kp (nmk 2)]"

definition "aenc\<^sub>1' xs = (aenc\<^sub>1 xs (extract_dkeyp xs))"
definition "aenc\<^sub>n' xs = (aenc\<^sub>n xs (extract_dkeyp xs))"

text \<open> @{text "dsig\<^sub>1 xs ks"}: digital signature of each element of @{text "xs"} using 
every key of @{text "ks"} \<close>
fun dsig\<^sub>1 :: "dmsg list \<Rightarrow> dkey list \<Rightarrow> dmsg list" where
"dsig\<^sub>1 [] sks = []" |
"dsig\<^sub>1 (x#xs) sks = (if is_MKs x then dsig\<^sub>1 xs sks 
  else (map (\<lambda>k. MSig x (MK k)) sks) @ dsig\<^sub>1 xs sks)"

value "dsig\<^sub>1 [MNon (nmk 0), \<lbrace>(MAg (Agent (nmk 1))), (MNon (nmk 0))\<rbrace>\<^sub>m] [Ks (nmk 3)]"

definition "dsig\<^sub>1' xs = dsig\<^sub>1 xs (extract_dkeys xs)"

text \<open> @{text "senc\<^sub>1 xs eks"}: symmetric encrypt of each element of @{text "xs"} using 
every key of @{text "eks"} (a set of MModExp)  \<close>
fun senc\<^sub>1 :: "dmsg list \<Rightarrow> dkey list \<Rightarrow> dmsg list" where
"senc\<^sub>1 [] eks = []" |
"senc\<^sub>1 (x#xs) eks = (if is_MKs x then senc\<^sub>1 xs eks 
  else (map (\<lambda>k. MSEnc x (MK k)) eks) @ senc\<^sub>1 xs eks)"

definition "senc\<^sub>1' xs = senc\<^sub>1 xs (extract_dkeys xs)"

value "senc\<^sub>1' [MNon (nmk 0), (MAg (Agent (nmk 1))), (MNon (nmk 1)), 
  (g\<^sub>m (nmk 1)) ^\<^sub>m (MNon (nmk 0)) ^\<^sub>m (MNon (nmk 1)), MK (Ks (nmk 4))]"

text \<open> @{text "senc\<^sub>1 xs eks"}: encrypt each element of @{text "xs"} with 
every key of @{text "eks"} (a set of MModExp)  \<close>
fun sencm\<^sub>1 :: "dmsg list \<Rightarrow> dmsg list \<Rightarrow> dmsg list" where
"sencm\<^sub>1 [] eks = []" |
"sencm\<^sub>1 (x#xs) eks = (if is_MKs x then sencm\<^sub>1 xs eks 
  else (map (\<lambda>k. MSEnc x k) eks) @ sencm\<^sub>1 xs eks)"

definition "sencm\<^sub>1' xs = sencm\<^sub>1 xs (filter is_MModExp xs)"

value "sencm\<^sub>1' [MNon (nmk 0), (MAg (Agent (nmk 1))), (MNon (nmk 1)), 
  (g\<^sub>m (nmk 1)) ^\<^sub>m (MNon (nmk 0)) ^\<^sub>m (MNon (nmk 1))]"

text \<open> Apply @{text "^\<^sub>m"} up to twice, based on @{text "g\<^sub>m"} \<close>
definition mod_exp2 :: "dmsg list \<Rightarrow> dmsg list" where
"mod_exp2 xs = (let mes = (map (\<lambda>n. (g\<^sub>m (nmk 0)) ^\<^sub>m n) xs) 
   in mes @ concat (map (\<lambda>m. (map (\<lambda>n. m ^\<^sub>m n) xs)) mes)
)"

value "mod_exp2 [MNon (nmk 0), MNon (nmk 1)]"

definition "mod_exp2' xs = (if List.member xs g\<^sub>m (nmk 0) then mod_exp2 xs else [])"

text \<open> Apply @{text "^\<^sub>m"} up to once to @{text "g\<^sub>m ^\<^sub>m a"} \<close>
fun mod_exp1 :: "dmsg list \<Rightarrow> dmsg list \<Rightarrow> dmsg list" where
"mod_exp1 [] ys = []" |
"mod_exp1 (((g\<^sub>m x) ^\<^sub>m a)#xs) ys = (map (\<lambda>n. ((g\<^sub>m x) ^\<^sub>m a) ^\<^sub>m n) ys) @ mod_exp1 xs ys" | 
"mod_exp1 (x#xs) ys = mod_exp1 xs ys"

value "mod_exp1 [(g\<^sub>m (nmk 0)) ^\<^sub>m (MNon (nmk 0))] [(MNon (nmk 0)), (MNon (nmk 1))]"

definition "mod_exp1' xs = (mod_exp1 xs (extract_nonces xs))"

text \<open> @{text "build1\<^sub>n knows pks sks nc ne l"} where 
@{text "knows"} is a list of atomic messages;
@{text "pks"} - a list of public keys;
@{text "sks"} - a list of private keys; 
@{text "nc"} - the number of times of composition;  
@{text "ne"} - the number of times of encryption (symmetric this case); 
@{text "l"} - the maximum length of a composed message
\<close>
fun build\<^sub>ns::"dmsg list \<Rightarrow> dkey list \<Rightarrow> dkey list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> dmsg list" where
\<comment> \<open> Original xs is always in the result \<close>
"build\<^sub>ns xs pks sks 0 0 l = xs" |
"build\<^sub>ns xs pks sks (Suc nc) 0 l = (build\<^sub>ns (List.union (pair2 xs xs l) xs) pks sks nc 0 l)" | 
"build\<^sub>ns xs pks sks 0 (Suc ne) l = (build\<^sub>ns (List.union (senc\<^sub>1' xs) xs) pks sks 0 ne l)" |
\<comment> \<open> Original xs + new messages after composition + new messages after encryption \<close>
"build\<^sub>ns xs pks sks (Suc nc) (Suc ne) l = (if ne = 0 then
  \<comment> \<open> If only one encryption, we treat it as outermost so composition first \<close>
  (build\<^sub>ns (List.union (pair2 xs xs l) xs) pks sks nc (Suc 0) l)
else 
  (List.union 
  \<comment> \<open> New messages after composition \<close>
    (build\<^sub>ns (List.union (pair2 xs xs l) xs) pks sks nc (Suc ne) l)
  \<comment> \<open> New messages after encryption \<close>
    (build\<^sub>ns (List.union (senc\<^sub>1' xs) xs) pks sks (Suc nc) ne l)
  )
)"

fun build\<^sub>na::"dmsg list \<Rightarrow> dkey list \<Rightarrow> dkey list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> dmsg list" where
\<comment> \<open> Original xs is always in the result \<close>
"build\<^sub>na xs pks sks 0 0 l = xs" |
"build\<^sub>na xs pks sks (Suc nc) 0 l = (build\<^sub>na (List.union (pair2 xs xs l) xs) pks sks nc 0 l)" | 
"build\<^sub>na xs pks sks 0 (Suc ne) l = (build\<^sub>na (List.union (aenc\<^sub>1' xs) xs) pks sks 0 ne l)" |
\<comment> \<open> Original xs + new messages after composition + new messages after encryption \<close>
"build\<^sub>na xs pks sks (Suc nc) (Suc ne) l = (if ne = 0 then
  \<comment> \<open> If only one encryption, we treat it as outermost so composition first \<close>
  (build\<^sub>na (List.union (pair2 xs xs l) xs) pks sks nc (Suc 0) l)
else 
  (List.union 
  \<comment> \<open> New messages after composition \<close>
    (build\<^sub>na (List.union (pair2 xs xs l) xs) pks sks nc (Suc ne) l)
  \<comment> \<open> New messages after encryption \<close>
    (build\<^sub>na (List.union (aenc\<^sub>1' xs) xs) pks sks (Suc nc) ne l)
  )
)"

fun build\<^sub>nd::"dmsg list \<Rightarrow> dkey list \<Rightarrow> dkey list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> dmsg list" where
\<comment> \<open> Original xs is always in the result \<close>
"build\<^sub>nd xs pks sks 0 0 l = xs" |
"build\<^sub>nd xs pks sks (Suc nc) 0 l = (build\<^sub>nd (List.union (pair2 xs xs l) xs) pks sks nc 0 l)" | 
"build\<^sub>nd xs pks sks 0 (Suc ne) l = (build\<^sub>nd (List.union (dsig\<^sub>1' xs) xs) pks sks 0 ne l)" |
\<comment> \<open> Original xs + new messages after composition + new messages after encryption \<close>
"build\<^sub>nd xs pks sks (Suc nc) (Suc ne) l = (if ne = 0 then
  \<comment> \<open> If only one encryption, we treat it as outermost so composition first \<close>
  (build\<^sub>nd (List.union (pair2 xs xs l) xs) pks sks nc (Suc 0) l)
else 
  (List.union 
  \<comment> \<open> New messages after composition \<close>
    (build\<^sub>nd (List.union (pair2 xs xs l) xs) pks sks nc (Suc ne) l)
  \<comment> \<open> New messages after encryption \<close>
    (build\<^sub>nd (List.union (dsig\<^sub>1' xs) xs) pks sks (Suc nc) ne l)
  )
)"

value "let xs = sort [MNon (nmk 0), (MAg (Agent (nmk 1))), MK (Kp (nmk 0))]
  in build\<^sub>ns xs (extract_dkeyp xs) (extract_dkeys xs) 0 0 2"

value "let xs = sort [MNon (nmk 0), MK (Kp (nmk 1))]
  in build\<^sub>ns xs (extract_dkeyp xs) (extract_dkeys xs) 1 1 2"
*)

text \<open> Instead of building up messages, we can alternatively ask whether the supplied messages can 
be built up from the given atomic message. \<close>
fun buildable :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg set \<Rightarrow> bool" where
"buildable m ms = (if m \<in> ms then True else 
  (case m of 
    (MAg a) \<Rightarrow> False |
    (MNon a) \<Rightarrow> False |
    (MK a) \<Rightarrow> False |
    (MPair m1 m2) \<Rightarrow> buildable m1 ms \<and> buildable m2 ms |
    (MAEnc m k) \<Rightarrow> buildable m ms \<and> buildable k ms |
    (MSig m k) \<Rightarrow> buildable m ms \<and> buildable k ms |
    (MSEnc m k) \<Rightarrow> buildable m ms \<and> buildable k ms |
    (MExpg a) \<Rightarrow> False |
    (MModExp m k) \<Rightarrow> buildable m ms \<and> buildable k ms |
    (MBitm b) \<Rightarrow> False |
    (MWat m k) \<Rightarrow> buildable m ms \<and> buildable k ms |
    (MJam m k) \<Rightarrow> buildable m ms \<and> buildable k ms
  )
)
"

value "buildable (MAg (Agent (nmk 0)) :: (2,4,4,2,2,2,1) dmsg) {MAg (Agent (nmk 1)), MAg (Agent (nmk 0))}"
value "buildable (MAg (Agent (nmk 1)) :: (2,4,4,2,2,2,1) dmsg) {MAg (Agent (nmk 0))}"

definition filter_buildable :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg set \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"filter_buildable xs ms = [x. x \<leftarrow> xs, buildable x ms]"

text \<open> To get the last element from a tuple of 4 elements \<close>
definition last4 :: "'a \<times> 'b \<times> 'c \<times> 'd \<Rightarrow> 'd" where
"last4 x = snd (snd (snd x))"

(*
text \<open> @{text "pair2 xs ys l"}: pair message once for each element of @{text "xs"} with 
every element of @{text "ys"} if they are different, their length does not exceed the given @{text 
"l"} which denotes the maximum length of a composed message. 
\<close>
fun pair2 :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> nat \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"pair2 [] ys l = []" |
"pair2 (x#xs) ys l = 
\<comment> \<open> If a watermarked or jammed message, ignore it.\<close>
\<^cancel>\<open>(if is_MWat x \<or> is_MJam x then pair2 xs ys l
 else \<close>
(let cs = pair2 xs ys l in
    (map (\<lambda>n. msort (MPair x n)) \<comment> \<open> Sort the components in MPair \<close>
      (filter 
        \<comment> \<open> they are not the same, length won't exceed l, and they are not watermarked and jammed \<close>
        (\<lambda>y. y \<noteq> x \<and> length x + length y \<le> l \<and> \<not> is_MWat y \<and> \<not> is_MJam y) 
      ys)
    ) @ cs)
\<^cancel>\<open>)\<close>"

text \<open> @{text "wat msgs bitms"} - watermark all messages in @{text "msgs"} with each bitmark from bitms\<close>
fun wat :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"wat [] bms = []" |
"wat (x#xs) bms = 
  \<comment> \<open> Ignore bitmasks, watermarked, and jammed messages because we won't watermark these messages \<close>
  (if is_MBitm x \<or> is_MJam x \<or> is_MWat x then wat xs bms 
   else (map (\<lambda>k. MWat x k) bms) @ wat xs bms)"

value "wat [mknon 0, \<lbrace>(mkag 1), (mknon 0)\<rbrace>\<^sub>m] [mkbm 0, mkbm 1] :: (2,4,4,2,2,2) dmsg list "

definition "wat' xs = (wat xs (filter is_MBitm xs))"

text \<open> @{text "jam msgs bitms"} - jam all messages in @{text "msgs"} with each bitmark from bitms\<close>
fun jam :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> 
  ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"jam [] bms = []" |
"jam (x#xs) bms = (if is_MBitm x then jam xs bms \<comment> \<open> Ignore bitmasks\<close>
  else (map (\<lambda>k. MJam x k) bms) @ jam xs bms)"

definition "jam' xs = (jam xs (filter is_MBitm xs))"

text \<open> Watermarked input messages using bitmarks in those messages \<close>
definition buildw :: "('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list \<Rightarrow> nat 
  \<Rightarrow> ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) dmsg list" where
"buildw xs n = (let 
    \<comment> \<open> We won't pair watermarked or jammed messages \<close>
    xs' = filter (\<lambda>m. \<not> (is_MWat m \<or> is_MJam m)) xs;
    ps = (pair2 xs' xs' n);
    cs = (List.union ps xs)
  in
    wat' cs
    \<^cancel>\<open>(List.union (wat' cs) cs)\<close>
)"

value "buildw [mknon 0, mknon 1, mkbm 2] 2"
*)

subsection \<open> All instances \<close>

definition "AllAgents = ((enum_class.enum:: ('a::len) dagent list))"
definition "AgentsMsgs as = MAg ` (set as)"
definition "AgentsLst as = map MAg as"
abbreviation "AllAgentsLst \<equiv> AgentsLst AllAgents"
value "(AgentsMsgs AllAgents) :: (2,4,4,2,2,1,1) dmsg set"
value "(AgentsLst AllAgents) :: (2,4,4,2,2,1,1) dmsg list"

definition "AllPKs = map Kp (enum_class.enum:: (('k::len) fsnat list))"
definition "PKsMsgs pks = MK ` (set pks)"
definition "PKsLst pks = map MK pks"
abbreviation "AllPKsLst \<equiv> PKsLst AllPKs"
value "(PKsMsgs AllPKs) :: (2,4,4,2,2,1,1) dmsg set"
value "(PKsLst AllPKs) :: (2,4,4,2,2,1,1) dmsg list"

definition "AllSKs = map Ks (enum_class.enum:: (('k::len) fsnat list))"
definition "SKsMsgs sks = MK ` (set sks)"
definition "SKsLst sks = map MK sks"
abbreviation "AllSKsLst \<equiv> SKsLst AllSKs"

value "(SKsMsgs AllSKs) :: (2,4,4,2,2,1,1) dmsg set"

definition "AllNonces = (enum_class.enum:: ('a::len) dnonce list)"
definition "NoncesMsgs xs = MNon ` (set xs)"
definition "NoncesLst xs = map MNon xs"
abbreviation "AllNoncesLst \<equiv> NoncesLst AllNonces"
value "(NoncesMsgs AllNonces) :: (2,4,4,2,2,1,1) dmsg set"

definition "AllExpGs = (enum_class.enum:: ('a::len) dexpg list)"
definition "ExpGMsgs xs = MExpg ` (set xs)"
definition "ExpGLst xs = map MExpg xs"
abbreviation "AllExpGLst \<equiv> ExpGLst AllExpGs"
value "(ExpGMsgs AllExpGs) :: (2,4,4,2,2,1,1) dmsg set"

definition "AllBitMs = (enum_class.enum:: ('a::len, 'b::len) dbitmask list)"
definition "BitMMsgs xs = MBitm ` (set xs)"
definition "BitMLst xs = map MBitm xs"
abbreviation "AllBitMLst \<equiv> BitMLst AllBitMs"
value "(BitMMsgs AllBitMs) :: (2,4,4,2,2,1,1) dmsg set"

subsection \<open> Signals and Channels \<close>

datatype ('a::len, 'n::len) dsig = ClaimSecret (sag:"'a dagent") (sn: "'n dnonce") (sp: "\<bbbP> ('a dagent)")
  | StartProt "'a dagent" "'a dagent" "'n dnonce" "'n dnonce"
  | EndProt "'a dagent" "'a dagent" "'n dnonce" "'n dnonce"

chantype ('a::len, 'n::len, 'k::len, 's::len, 'g::len, 'bm::len, 'bl::len) chan =
  env   :: "'a::{len,typerep} dagent \<times> 'a dagent"
\<comment> \<open> @{text "(src, medium, dst, m)"} Send a message m from src to dst through medium. If the medium is 
  Intruder, it just means to a public network/channel. Otherwise, it is private. \<close>
  send  :: "'a dagent \<times> 'a dagent \<times> 'a dagent \<times> ('a::{len,typerep}, 'n::{len,typerep}, 
    'k::{len,typerep}, 's::{len,typerep}, 'g::{len,typerep}, 'bm::{len,typerep}, 'bl::{len,typerep}) dmsg"
\<comment> \<open> @{text "(src, medium, dst, m)"} Send a message m from src to dst through medium. If the medium is 
  Intruder, it just means to a public network/channel. Otherwise, it is private. \<close>
  cjam   :: "('a::{len,typerep}, 'n::{len,typerep}, 'k::{len,typerep}, 's::{len,typerep}, 
    'g::{len,typerep}, 'bm::{len,typerep}, 'bl::{len,typerep}) dmsg"
  cdejam :: "('a::{len,typerep}, 'n::{len,typerep}, 'k::{len,typerep}, 's::{len,typerep}, 
    'g::{len,typerep}, 'bm::{len,typerep}, 'bl::{len,typerep}) dmsg"
  recv  :: "'a dagent \<times> 'a dagent \<times> 'a dagent \<times> ('a::{len,typerep}, 'n::{len,typerep}, 
    'k::{len,typerep}, 's::{len,typerep}, 'g::{len,typerep}, 'bm::{len,typerep}, 'bl::{len,typerep}) dmsg"
  leak  :: "('a::{len,typerep}, 'n::{len,typerep}, 'k::{len,typerep}, 's::{len,typerep}, 
    'g::{len,typerep}, 'bm::{len,typerep}, 'bl::{len,typerep}) dmsg"
  sig   :: "('a::{len,typerep}, 'n::{len,typerep}) dsig"
  terminate :: "unit"

print_bnfs

text \<open> Use abbreviation hear and fake for send and recv to avoid renaming later in Intruder \<close>
abbreviation "hear \<equiv> send"
abbreviation "fake \<equiv> recv"
abbreviation "relay \<equiv> recv"

definition send_to_network where
"send_to_network A B m = outp send (A, Intruder, B, m)"

definition send_privately where
"send_privately A B m = outp send (A, A, B, m)"

definition recv_from_network where
"recv_from_network A ms = inp_in recv (set [(Intruder, Intruder, A, m). m \<leftarrow> ms])"

definition recv_privately where
"recv_privately A B ms = inp_in recv (set [(A, A, B, m). m \<leftarrow> ms])"

end
