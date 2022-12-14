theory Chap1_Lemma1
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


(* definition even  \<equiv>\<forall>x. \<exists> y:: m. Prod (Suc Suc Zero) y = x \<longrightarrow>   *)

(* \<forall> x1 x2 x3. even x1 x2 x3 \<longrightarrow> assoc x1 x2 x3 *)


section "commutative residuated lattice"


subsection "Definitions"

type_synonym p = "m \<Rightarrow> bool"
type_synonym p_op = "p \<Rightarrow> p \<Rightarrow> p"

definition p_meet :: p_op (infixr "\<^bold>\<inter>\<^sub>p" 55) where
"X \<^bold>\<inter>\<^sub>p Y \<equiv> \<lambda> m. X m \<and> Y m" 
definition p_join :: p_op (infixr "\<^bold>\<union>\<^sub>p" 55) where
"X \<^bold>\<union>\<^sub>p Y \<equiv> \<lambda> m. X m \<or> Y m"
definition p_mult :: p_op (infixr "\<^bold>\<star>\<^sub>p" 55) where
"X \<^bold>\<star>\<^sub>p Y \<equiv> \<lambda> m. \<exists> a b. X a \<and> Y b \<and> (a \<^bold>\<sqdot>\<^sub>m b) = m"
definition p_impl :: p_op (infixr "\<^bold>\<Rrightarrow>\<^sub>p" 55) where
"X \<^bold>\<Rrightarrow>\<^sub>p Y \<equiv> \<lambda> m. \<forall> c. X c \<longrightarrow> Y (m \<^bold>\<sqdot>\<^sub>m c)"
consts p_zero :: "p" ("\<^bold>0\<^sub>p")
definition p_one :: "p" ("\<^bold>1\<^sub>p") where
"\<^bold>1\<^sub>p \<equiv> \<lambda> m. m = (\<^bold>1\<^sub>m)"
definition p_bot :: "p" ("\<^bold>\<bottom>\<^sub>p") where
"\<^bold>\<bottom>\<^sub>p \<equiv> \<lambda> m. False"
definition p_top :: "p" ("\<^bold>\<top>\<^sub>p") where
"\<^bold>\<top>\<^sub>p \<equiv> \<lambda> m. True"
definition p_ord ::"p \<Rightarrow> p \<Rightarrow> bool" (infixr"\<^bold>\<le>\<^sub>p"51) where 
(*"p1 \<^bold>\<le>\<^sub>p p2 \<equiv> \<forall> m. (p1 \<^bold>\<inter>\<^sub>p p2) m \<longleftrightarrow> p1 m"*)
(* this might be also contravariant *)
"p1 \<^bold>\<le>\<^sub>p p2 \<equiv> \<forall> m. (p1 m \<longrightarrow> p2 m)"



subsection "Properties Proof"

subsubsection "commutative monoid with the unit 1"
(*
definition "commu Op \<equiv> \<forall> a b. Op a b = Op b a"
definition "unitE Op One \<equiv> \<forall> a. Op a One = a"
definition "assoc Op \<equiv> \<forall> x y z. Op (Op x y) z = Op x (Op y z)"
*)

lemma p_commu_mult: "commu (\<^bold>\<star>\<^sub>p)"
  apply (unfold commu_def p_mult_def)
proof (rule, rule, rule)
  fix a b m
  show "(\<exists>aa ba. a aa \<and> b ba \<and> aa \<^bold>\<sqdot>\<^sub>m ba = m) = (\<exists>aa ba. b aa \<and> a ba \<and> aa \<^bold>\<sqdot>\<^sub>m ba = m)" proof
    show "\<exists>aa ba. a aa \<and> b ba \<and> aa \<^bold>\<sqdot>\<^sub>m ba = m \<Longrightarrow> \<exists>aa ba. b aa \<and> a ba \<and> aa \<^bold>\<sqdot>\<^sub>m ba = m" proof -
      assume 1: "\<exists>aa ba. a aa \<and> b ba \<and> aa \<^bold>\<sqdot>\<^sub>m ba = m"
      then obtain aa ba where "a aa \<and> b ba \<and> aa \<^bold>\<sqdot>\<^sub>m ba = m" by auto
      hence "a aa \<and> b ba \<and> ba \<^bold>\<sqdot>\<^sub>m aa = m" using commu_def m_commu by metis
      thus "\<exists>aa ba. b aa \<and> a ba \<and> aa \<^bold>\<sqdot>\<^sub>m ba = m" by auto
    qed
    show " \<exists>aa ba. b aa \<and> a ba \<and> aa \<^bold>\<sqdot>\<^sub>m ba = m \<Longrightarrow> \<exists>aa ba. a aa \<and> b ba \<and> aa \<^bold>\<sqdot>\<^sub>m ba = m"
      by (meson commu_def m_commu) qed qed
lemma p_unitE_mult: "unitE (\<^bold>\<star>\<^sub>p) (\<^bold>1\<^sub>p)"
  apply (unfold unitE_def p_one_def p_mult_def)
proof (rule, rule)
  fix a m
  show "(\<exists>aa b. a aa \<and> b = \<^bold>1\<^sub>m \<and> aa \<^bold>\<sqdot>\<^sub>m b = m) = a m" proof
    show "\<exists>aa b. a aa \<and> b = \<^bold>1\<^sub>m \<and> aa \<^bold>\<sqdot>\<^sub>m b = m \<Longrightarrow> a m" proof -
      assume 1: "\<exists>aa b. a aa \<and> b = \<^bold>1\<^sub>m \<and> aa \<^bold>\<sqdot>\<^sub>m b = m"
      then obtain aa b where 2: "a aa \<and> b = \<^bold>1\<^sub>m \<and> aa \<^bold>\<sqdot>\<^sub>m b = m" by auto
      then have "a aa \<and> (aa \<^bold>\<sqdot>\<^sub>m \<^bold>1\<^sub>m = m)" by auto
      then have "a aa \<and> (aa = m)" using m_idemp unitE_def by metis
      thus "a m" by auto qed
  next
    show "a m \<Longrightarrow> \<exists>aa b. a aa \<and> b = \<^bold>1\<^sub>m \<and> aa \<^bold>\<sqdot>\<^sub>m b = m" using m_idemp by (simp add: unitE_def)
  qed qed
lemma p_assoc_mult: "assoc (\<^bold>\<star>\<^sub>p)"
  apply (unfold assoc_def p_mult_def) 
proof (rule, rule, rule, rule)
  fix x y z m
  show "(\<exists>a b. (\<exists>aa b. x aa \<and> y b \<and> aa \<^bold>\<sqdot>\<^sub>m b = a) \<and> z b \<and> a \<^bold>\<sqdot>\<^sub>m b = m) = (\<exists>a b. x a \<and> (\<exists>a ba. y a \<and> z ba \<and> a \<^bold>\<sqdot>\<^sub>m ba = b) \<and> a \<^bold>\<sqdot>\<^sub>m b = m)"
  proof
    show "\<exists>a b. (\<exists>aa b. x aa \<and> y b \<and> aa \<^bold>\<sqdot>\<^sub>m b = a) \<and> z b \<and> a \<^bold>\<sqdot>\<^sub>m b = m \<Longrightarrow> \<exists>a b. x a \<and> (\<exists>a ba. y a \<and> z ba \<and> a \<^bold>\<sqdot>\<^sub>m ba = b) \<and> a \<^bold>\<sqdot>\<^sub>m b = m"
    proof -
      assume 1: "\<exists>a b. (\<exists>aa bb. x aa \<and> y bb \<and> aa \<^bold>\<sqdot>\<^sub>m bb = a) \<and> z b \<and> a \<^bold>\<sqdot>\<^sub>m b = m"
      then obtain a b aa bb where 3: "x aa \<and> y bb \<and> aa \<^bold>\<sqdot>\<^sub>m bb = a \<and> z b \<and> a \<^bold>\<sqdot>\<^sub>m b = m" by auto
      hence "x aa \<and> y bb \<and> z b \<and> (aa \<^bold>\<sqdot>\<^sub>m bb) \<^bold>\<sqdot>\<^sub>m b = m" by auto
      hence "x aa \<and> y bb \<and> z b \<and> aa \<^bold>\<sqdot>\<^sub>m (bb \<^bold>\<sqdot>\<^sub>m b) = m" using m_assoc assoc_def by metis
      hence "\<exists> aa b' bb b. x aa \<and> y bb \<and> z b \<and> bb \<^bold>\<sqdot>\<^sub>m b = b' \<and> z b \<and> aa \<^bold>\<sqdot>\<^sub>m b' = m" by blast
      thus "\<exists>aa b'. x aa \<and> (\<exists>bb b. y bb \<and> z b \<and> bb \<^bold>\<sqdot>\<^sub>m b = b') \<and> aa \<^bold>\<sqdot>\<^sub>m b' = m" by auto qed
  next
    show "\<exists>a b. x a \<and> (\<exists>a ba. y a \<and> z ba \<and> a \<^bold>\<sqdot>\<^sub>m ba = b) \<and> a \<^bold>\<sqdot>\<^sub>m b = m \<Longrightarrow> \<exists>a b. (\<exists>aa b. x aa \<and> y b \<and> aa \<^bold>\<sqdot>\<^sub>m b = a) \<and> z b \<and> a \<^bold>\<sqdot>\<^sub>m b = m" 
      by (metis assoc_def m_assoc) qed qed



subsubsection "bounded lattice for Meet"

(*
definition "commu Op \<equiv> \<forall> a b. Op a b = Op b a"
definition "assoc Op \<equiv> \<forall> x y z. Op (Op x y) z = Op x (Op y z)"
definition "idemp Op \<equiv> \<forall> a. Op a a = a"
definition "great Op Top \<equiv> extre Op Top"
*)

lemma p_commu_meet: "commu (\<^bold>\<inter>\<^sub>p)" 
  apply (unfold commu_def p_meet_def)
proof (rule, rule, rule)
  fix a b :: p fix  m :: m
  show "(a m \<and> b m) = (b m \<and> a m)" by auto qed
lemma p_assoc_meet: "assoc (\<^bold>\<inter>\<^sub>p)" 
  apply (unfold assoc_def p_meet_def)
proof (rule, rule, rule, rule)
  fix x y z :: p fix m :: m
  show "((x m \<and> y m) \<and> z m) = (x m \<and> y m \<and> z m)" by simp qed
lemma p_idemp_meet: "idemp (\<^bold>\<inter>\<^sub>p)" 
  apply (unfold idemp_def p_meet_def) proof (rule, rule)
  fix a :: p fix m :: m
  show "(a m \<and> a m) = a m"  by simp qed
lemma p_great_meet: "great (\<^bold>\<inter>\<^sub>p) (\<^bold>\<top>\<^sub>p)"
  apply (unfold great_def extre_def p_meet_def p_top_def) proof (rule, rule)
  fix a :: p fix m :: m
  show "(a m \<and> True) = a m" by simp qed



subsubsection "bounded lattice for Join"

(*
definition "commu Op \<equiv> \<forall> a b. Op a b = Op b a"
definition "assoc Op \<equiv> \<forall> x y z. Op (Op x y) z = Op x (Op y z)"
definition "idemp Op \<equiv> \<forall> a. Op a a = a"
definition "least Op Top \<equiv> extre Op Top"
*)

lemma p_commu_join: "commu (\<^bold>\<union>\<^sub>p)" 
  apply (unfold commu_def p_join_def)
proof (rule, rule, rule)
  fix a b :: p fix  m :: m
  show "(a m \<or> b m) = (b m \<or> a m)" by auto qed
lemma p_assoc_join: "assoc (\<^bold>\<union>\<^sub>p)" 
  apply (unfold assoc_def p_join_def)
proof (rule, rule, rule, rule)
  fix x y z :: p fix m :: m
  show "((x m \<or> y m) \<or> z m) = (x m \<or> y m \<or> z m)" by simp qed
lemma p_idemp_join: "idemp (\<^bold>\<union>\<^sub>p)" 
  apply (unfold idemp_def p_join_def) proof (rule, rule)
  fix a :: p fix m :: m
  show "(a m \<or> a m) = a m"  by simp qed
lemma p_least_join: "least (\<^bold>\<union>\<^sub>p) (\<^bold>\<bottom>\<^sub>p)"
  apply (unfold least_def extre_def p_join_def p_bot_def) proof (rule, rule)
  fix a :: p fix m :: m
  show "(a m \<or> False) = a m" by simp qed



subsubsection "bounded lattice for Join and Meet"

(*definition "absor Op1 Op2 \<equiv> \<forall> a b. Op1 a (Op2 a b) = a"*)

lemma p_absorb_meetjoin: "absorb (\<^bold>\<inter>\<^sub>p) (\<^bold>\<union>\<^sub>p)"
  apply (unfold absorb_def p_meet_def p_join_def) proof (rule, rule, rule)
  fix a b :: p fix m :: m
  show "(a m \<and> (a m \<or> b m)) = a m" by auto qed
lemma p_absorb_joinmeet: "absorb (\<^bold>\<union>\<^sub>p) (\<^bold>\<inter>\<^sub>p)" 
  apply (unfold absorb_def p_meet_def p_join_def) proof (rule, rule, rule)
  fix a b :: p fix m :: m
  show "(a m \<or> a m \<and> b m) = a m" by auto qed


subsubsection "residuated lattice"

lemma p_resid_law: "resid (\<^bold>\<le>\<^sub>p) (\<^bold>\<star>\<^sub>p) (\<^bold>\<Rrightarrow>\<^sub>p)"
  apply (unfold resid_def p_mult_def p_impl_def p_ord_def) 
(*  by (metis commu_def m_commu)*)
proof (rule, rule, rule)
  fix x y z :: p
  show "(\<forall>m. (\<exists>a b. x a \<and> y b \<and> a \<^bold>\<sqdot>\<^sub>m b = m) \<longrightarrow> z m) = (\<forall>a. x a \<longrightarrow> (\<forall>b. y b \<longrightarrow> z (a \<^bold>\<sqdot>\<^sub>m b)))" proof (rule)
    show " \<forall>m. (\<exists>a' b'. x a' \<and> y b' \<and> a' \<^bold>\<sqdot>\<^sub>m b' = m) \<longrightarrow> z m \<Longrightarrow> \<forall>a. x a \<longrightarrow> (\<forall>b. y b \<longrightarrow> z (a \<^bold>\<sqdot>\<^sub>m b))" proof (rule, rule, rule, rule)
      fix a b :: m
      assume 1: "\<forall>m. (\<exists>a' b'. x a' \<and> y b' \<and> a' \<^bold>\<sqdot>\<^sub>m b' = m) \<longrightarrow> z m"
      assume 2: "x a"
      assume 3: "y b"
      show "z (a \<^bold>\<sqdot>\<^sub>m b)" proof -
        let ?m' = "a \<^bold>\<sqdot>\<^sub>m b"
        from 2 3 have "x a \<and> y b \<and> a \<^bold>\<sqdot>\<^sub>m b = ?m'" by simp
        hence "\<exists>a' b'. x a' \<and> y b' \<and> a' \<^bold>\<sqdot>\<^sub>m b' = ?m'" by auto
        hence "z ?m'" using 1 by simp
        thus "z (a \<^bold>\<sqdot>\<^sub>m b)" by simp
      qed
    qed
  next
    show "\<forall>a. x a \<longrightarrow> (\<forall>b. y b \<longrightarrow> z (a \<^bold>\<sqdot>\<^sub>m b)) \<Longrightarrow> \<forall>m. (\<exists>a b. x a \<and> y b \<and> a \<^bold>\<sqdot>\<^sub>m b = m) \<longrightarrow> z m"
      by auto
  qed qed




  

  
  
  subsubsection "complete lattice"

(* how to state this ? *)

abbreviation "upper_bound U S \<equiv> \<forall>X. (S X) \<longrightarrow> X \<^bold>\<preceq> U"

abbreviation 
"is_supremum U S \<equiv> upper_bound U S \<and> (\<forall>X. upper_bound X S \<longrightarrow> U \<^bold>\<preceq> X)"

lemma sup_char: "is_supremum \<^bold>\<Or>S S"

abbreviation "upper_bound U \<equiv> \<forall> X.  X \<^bold>\<preceq> U"


end