theory Chap3
  imports Main Chap1_Properties
begin



section "commutative monoid"

typedecl m

consts m_mult :: "m \<Rightarrow> m \<Rightarrow> m" (infixr "\<^bold>\<sqdot>\<^sub>m" 55)
consts m_one :: "m" ("\<^bold>1\<^sub>m")
consts m_ord :: "m \<Rightarrow> m \<Rightarrow> bool" (infixr "\<^bold>\<le>\<^sub>m" 50)


axiomatization where
m_assoc: "assoc (\<^bold>\<sqdot>\<^sub>m)" and
m_commu: "commu (\<^bold>\<sqdot>\<^sub>m)" and
m_idemp: "unitE (\<^bold>\<sqdot>\<^sub>m) \<^bold>1\<^sub>m"


type_synonym p = "m \<Rightarrow> bool"
type_synonym p_cl = "p \<Rightarrow> p"
type_synonym p_set = "p \<Rightarrow> bool"
consts p_ord :: "p \<Rightarrow> p \<Rightarrow> bool" (infixr "\<^bold>\<le>\<^sub>p" 50)





section "Closure Operator"


subsection "Definition"

definition upperBound :: "p \<Rightarrow> p" ("_\<^sup>\<rightarrow>" 55) where
"X\<^sup>\<rightarrow> \<equiv> \<lambda> u. \<forall> x. X x \<and> x \<^bold>\<le>\<^sub>m u"
definition lowerBound :: "p \<Rightarrow> p" ("_\<^sup>\<leftarrow>" 55) where
"X\<^sup>\<leftarrow> \<equiv> \<lambda> v. \<forall> x. X x \<and> v \<^bold>\<le>\<^sub>m x"

definition C2 :: "p \<Rightarrow> p" where
"C2 X = ((X\<^sup>\<rightarrow>)\<^sup>\<leftarrow>)"




subsection "Closure Condition via single proofs"

lemma "\<forall>a. (a \<^bold>\<le>\<^sub>p (C2 a))" sorry
lemma "\<forall> a b. a \<^bold>\<le>\<^sub>p b \<longrightarrow> (C2 a) \<^bold>\<le>\<^sub>p (C2 b)" sorry
lemma "\<forall> a. (Cl (Cl a)) \<^bold>\<le>\<^sub>p (Cl a)" sorry
lemma "\<forall> a b. (Op (Cl a) (Cl b)) \<^bold>\<le>\<^sub>p (Cl (Op a b))" sorry

definition p_one :: "p" ("\<^bold>1\<^sub>p") where
"\<^bold>1\<^sub>p \<equiv> \<lambda> m. m = (\<^bold>1\<^sub>m)"

lemma baseOfC2: "UBase C2 = (\<^bold>1\<^sub>p) " sorry




subsection "Closure Conditions via Galois Connection"

declare [[show_types]]

(* also possible: Closure Conditions from galois property *)

type_synonym 'w cl  = \<open>'w \<Rightarrow> 'w\<close> (* type for closure operator *)
type_synonym 'w rel  = \<open>'w \<Rightarrow> 'w \<Rightarrow> bool\<close> (* type for closure operator *)

definition antitone_gal 
:: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
"antitone_gal s t Ord \<equiv> \<forall> V U. Ord V (s U) \<longleftrightarrow> Ord U (t V)"

definition Cond1 :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
"Cond1 Cl Ord \<equiv> \<forall>A. Ord A (Cl A)"
definition Cond2 :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"Cond2 Cl Ord \<equiv> \<forall>A B. (Ord A B) \<longrightarrow> (Ord (Cl A) (Cl B))"
definition Cond3 :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"Cond3 Cl Equi \<equiv> \<forall>A. Equi (Cl (Cl A)) (Cl A)"

definition "general_Cl Cl Ord Equi \<equiv> 
  (Cond1 Cl Ord \<and> Cond2 Cl Ord \<and> Cond3 Cl Equi)"

definition m_equi :: "m \<Rightarrow> m \<Rightarrow> bool" (infixr "\<^bold>\<approx>\<^sub>m" 55) where
"m_equi \<equiv> \<lambda> x y. x \<^bold>\<le>\<^sub>m y \<and> y \<^bold>\<le>\<^sub>m x"


lemma 
  assumes "antitone_gal s t (\<^bold>\<le>\<^sub>m)"
  shows "general_Cl (t \<circ> s) (\<^bold>\<le>\<^sub>m) (\<^bold>\<approx>\<^sub>m)" 
    and "general_Cl (s \<circ> t) (\<^bold>\<le>\<^sub>m) (\<^bold>\<approx>\<^sub>m)"
  sorry


end