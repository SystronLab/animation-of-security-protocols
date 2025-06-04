theory FSNat 
  imports "HOL-Library.Numeral_Type"
          "HOL-Library.Type_Length"
begin

declare [[show_types]]
declare [[typedef_overloaded]]

subsection \<open> General definitions \<close>

typedef (overloaded) ('n::len) fsnat = "{0..<LENGTH('n)}::nat set"
  morphisms nat_of_fsnat fsnat_of_nat
  by (rule_tac x="0" in exI, auto)

lift_definition nmk :: "nat \<Rightarrow> ('a::len) fsnat" is 
"\<lambda> x. fsnat_of_nat (x mod (LENGTH('a)))" .

code_datatype nmk
declare nat_of_fsnat_inverse [simp]
declare fsnat_of_nat_inverse [simp]
declare nmk_def [simp]

syntax 
  "_fsnat" :: "type \<Rightarrow> type" ("fsnat[_]" [0] 100)

translations 
  (type) "fsnat['n]" == (type) "('n) fsnat"

lemma nat_of_fsnat_code [code]: "(nat_of_fsnat (nmk x::('a fsnat)) = x mod (LENGTH('a::len)))"
  by (simp)

definition fsnatlist :: "(fsnat['a::len]) list" where
"fsnatlist = map (nmk) [0..<LENGTH('a)]"

lemma distinct_fsnat: "distinct (fsnatlist)"
  apply (simp add: fsnatlist_def distinct_map inj_on_def)
  by (meson atLeastAtMost_iff atLeastLessThan_iff less_imp_le_nat fsnat_of_nat_inject)

definition all_fsnat :: "(('a::len) fsnat \<Rightarrow> bool) \<Rightarrow> bool"
where
  "all_fsnat P \<longleftrightarrow> (\<forall>xs \<in> set (fsnatlist). P xs)"

definition ex_fsnat :: "(('a::len) fsnat \<Rightarrow> bool) \<Rightarrow> bool"
where
  "ex_fsnat P \<longleftrightarrow> (\<exists>xs \<in> set (fsnatlist). P xs)"

lemma fsnatlist_univ:
  shows "set (fsnatlist) = UNIV"
  apply (simp add: fsnatlist_def image_def)
  apply (auto)
  by (meson fsnat_of_nat_cases)

instantiation fsnat :: (len) enum
begin

definition enum_fsnat :: "(('a::len) fsnat) list" where
"enum_fsnat = fsnatlist"

definition enum_all_fsnat :: "(('a::len) fsnat \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_fsnat P = all_fsnat P"

definition enum_ex_fsnat :: "(('a::len) fsnat \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_fsnat P = ex_fsnat P"

instance 
  by (intro_classes)
     (simp_all add: enum_fsnat_def distinct_fsnat enum_distinct fsnatlist_univ enum_all_fsnat_def enum_ex_fsnat_def all_fsnat_def ex_fsnat_def)
end

value "enum_class.enum::(2 fsnat) list"
value "nmk 0::(2 fsnat)"

instantiation fsnat :: (len) equal
begin

lift_definition equal_fsnat :: \<open>fsnat['a] \<Rightarrow> fsnat['a] \<Rightarrow> bool\<close>
  is \<open>\<lambda>k l. nat_of_fsnat k = nat_of_fsnat l\<close> .

instance apply (intro_classes)
  apply(auto simp add: equal_fsnat_def, transfer, auto)
  by (simp add: nat_of_fsnat_inject)
end

lemma fsnat_eq_iff:
  "m = n \<longleftrightarrow> nat_of_fsnat m = nat_of_fsnat n"
  by (simp add: nat_of_fsnat_inject)

instantiation fsnat :: (len) linorder
begin
definition less_eq_fsnat: "x \<le> y \<longleftrightarrow> nat_of_fsnat x \<le> nat_of_fsnat y"
definition less_fsnat: "x < y \<longleftrightarrow> nat_of_fsnat x < nat_of_fsnat y"

instance
  by standard
    (auto simp add: less_eq_fsnat less_fsnat not_le fsnat_eq_iff min.coboundedI1 mult.commute)
end

lemma mod_less_eq: 
  assumes "(a::nat) \<le> b"
  assumes "b < n"
  shows "(a mod n) \<le> (b mod n)"
proof -
  have f1: "a div n * n + a mod n = a" using div_mult_mod_eq by blast
  have f2: "b div n * n + b mod n = b" using div_mult_mod_eq by blast
  show ?thesis
    using assms f1 f2 by (metis add_leE mod_less)
qed

lemma nmk_less_eq:
"m \<le> n \<and> n < LENGTH('a) \<longrightarrow> ((nmk m) :: ('a::{len} fsnat)) \<le> nmk n"
  by (auto simp add: less_eq_fsnat)

end
