theory Chap1_Proposition3
  imports Main Chap1_Properties
begin


section "commutative residuated PowerSet Lattice Definition"

subsection "declaration"

typedecl m
type_synonym p = "m \<Rightarrow> bool"
type_synonym p_op = "p \<Rightarrow> p \<Rightarrow> p"

consts p_meet :: p_op (infixr "\<^bold>\<inter>\<^sub>p" 55)
consts p_join :: p_op (infixr "\<^bold>\<union>\<^sub>p" 55)
consts p_mult :: p_op (infixr "\<^bold>\<star>\<^sub>p" 55)
consts p_impl :: p_op (infixr "\<^bold>\<Rrightarrow>\<^sub>p" 55)
consts p_zero :: "p" ("\<^bold>0\<^sub>p")
consts p_one :: "p" ("\<^bold>1\<^sub>p") 
consts p_bot :: "p" ("\<^bold>\<bottom>\<^sub>p")
consts p_top :: "p" ("\<^bold>\<top>\<^sub>p")
consts p_ord :: "p \<Rightarrow> p \<Rightarrow> bool" (infixr"\<^bold>\<le>\<^sub>p"51)



subsection "axiomatisation"

axiomatization where

(* commutative monoid with the unit 1:
definition "commu Op \<equiv> \<forall> a b. Op a b = Op b a"
definition "unitE Op One \<equiv> \<forall> a. Op a One = a"
definition "assoc Op \<equiv> \<forall> x y z. Op (Op x y) z = Op x (Op y z)"*)
p_commu_mult: "commu (\<^bold>\<star>\<^sub>p)" and
p_idemp_mult: "unitE (\<^bold>\<star>\<^sub>p) \<^bold>1\<^sub>p" and
p_assoc_mult: "assoc (\<^bold>\<star>\<^sub>p)" and

(* ordered monoid *)
p_ordered: "order (\<^bold>\<le>\<^sub>p) (\<^bold>\<star>\<^sub>p)" and
p_refl_order: "reflex (\<^bold>\<le>\<^sub>p)" and
p_antisy_order: "antisy (\<^bold>\<le>\<^sub>p)" and
p_transi_order: "transi (\<^bold>\<le>\<^sub>p)" and


(*  bounded lattice for Meet
definition "commu Op \<equiv> \<forall> a b. Op a b = Op b a"
definition "assoc Op \<equiv> \<forall> x y z. Op (Op x y) z = Op x (Op y z)"
definition "idemp Op \<equiv> \<forall> a. Op a a = a"
definition "great Op Top \<equiv> extre Op Top" *)
p_commu_meet: "commu (\<^bold>\<inter>\<^sub>p)" and
p_assoc_meet: "assoc (\<^bold>\<inter>\<^sub>p)" and
p_idemp_meet: "idemp (\<^bold>\<inter>\<^sub>p)" and
p_great_meet: "great (\<^bold>\<inter>\<^sub>p) (\<^bold>\<top>\<^sub>p)" and

(*  bounded lattice for Join
definition "commu Op \<equiv> \<forall> a b. Op a b = Op b a"
definition "assoc Op \<equiv> \<forall> x y z. Op (Op x y) z = Op x (Op y z)"
definition "idemp Op \<equiv> \<forall> a. Op a a = a"
definition "least Op Top \<equiv> extre Op Top"
*)
p_commu_join: "commu (\<^bold>\<union>\<^sub>p)" and
p_assoc_join: "assoc (\<^bold>\<union>\<^sub>p)" and
p_idemp_join: "idemp (\<^bold>\<union>\<^sub>p)" and
p_least_join: "least (\<^bold>\<union>\<^sub>p) (\<^bold>\<bottom>\<^sub>p)" and

(*  bounded lattice for Join and Meet
definition "absor Op1 Op2 \<equiv> \<forall> a b. Op1 a (Op2 a b) = a"*)
p_absorb_meetjoin: "absor (\<^bold>\<inter>\<^sub>p) (\<^bold>\<union>\<^sub>p)" and
p_absorb_joinmeet: "absor (\<^bold>\<union>\<^sub>p) (\<^bold>\<inter>\<^sub>p)" and

(*  residuated lattice
definition "resid Ord Mult Impl \<equiv> 
\<forall> x y z. Ord (Mult x y) z = Ord x (Impl y z)"*)
p_resid_law: "resid (\<^bold>\<le>\<^sub>p) (\<^bold>\<star>\<^sub>p) (\<^bold>\<Rrightarrow>\<^sub>p)"





section "Closure Operator Axiomatisation"


type_synonym p_cl = "p \<Rightarrow> p"

consts ClOp :: p_cl

axiomatization where
cl_expan: "cl_expan ClOp (\<^bold>\<le>\<^sub>p)" and
cl_mono: "cl_mono ClOp (\<^bold>\<le>\<^sub>p)" and
cl_idem: "cl_idem ClOp (\<^bold>\<le>\<^sub>p)" and
cl_distr: "cl_distr ClOp (\<^bold>\<le>\<^sub>p) (\<^bold>\<star>\<^sub>p)"




section "residuated lattice as closure algebra"

subsection "Definitions"

type_synonym c_op = "p \<Rightarrow> p_cl \<Rightarrow> p \<Rightarrow> p"

definition c_meet :: c_op ("_ \<^bold>\<inter>[_] _" 55) where
"X \<^bold>\<inter>[Cl] Y \<equiv> Cl (\<lambda> m. (X \<^bold>\<inter>\<^sub>p Y) m)" 
definition c_join :: c_op ("_ \<^bold>\<union>[_] _" 55) where
"X \<^bold>\<union>[Cl] Y \<equiv> Cl (\<lambda> m. (X \<^bold>\<union>\<^sub>p Y) m)"
definition c_mult :: c_op ("_ \<^bold>\<star>[_] _" 55)where
"X \<^bold>\<star>[Cl] Y \<equiv> Cl (\<lambda> m. (X \<^bold>\<star>\<^sub>p Y) m)"
definition c_impl :: c_op (" _ \<^bold>\<Rrightarrow>[_] _" 55) where
"X \<^bold>\<Rrightarrow>[Cl] Y \<equiv> Cl (\<lambda> m. (X \<^bold>\<Rrightarrow>\<^sub>p Y) m)"
(*consts c_zero :: "p" ("\<^bold>0\<^sub>c")*)
definition c_zero :: "p_cl \<Rightarrow> p" ("\<^bold>0[_]") where
"\<^bold>0[Cl] \<equiv> Cl (\<^bold>0\<^sub>p)"
definition c_one :: "p_cl \<Rightarrow> p" ("\<^bold>1[_]") where
"\<^bold>1[Cl] \<equiv> Cl (\<^bold>1\<^sub>p)"
definition c_bot :: "p_cl \<Rightarrow> p" ("\<^bold>\<bottom>[_]") where
"\<^bold>\<bottom>[Cl] \<equiv> Cl (\<^bold>\<bottom>\<^sub>p)"
definition c_top :: "p_cl \<Rightarrow> p" ("\<^bold>\<top>[_]") where
"\<^bold>\<top>[Cl] \<equiv> (\<^bold>\<top>\<^sub>p)"
definition c_ord :: "p \<Rightarrow> p \<Rightarrow> bool" (infixr "\<^bold>\<le>\<^sub>c" 50) where
"X \<^bold>\<le>\<^sub>c Y \<equiv> X \<^bold>\<le>\<^sub>p Y"



subsection "C-closedness of operations"

(* why not just putting it around*)
lemma c_closed_impl:
  assumes clA: "cClosed ClOp A"
  assumes clB: "cClosed ClOp B"
  shows "cClosed ClOp (A \<^bold>\<Rrightarrow>[ClOp] B)"
  apply (unfold c_impl_def cClosed_def) proof (rule)
  fix x
  show "ClOp (ClOp (A \<^bold>\<Rrightarrow>\<^sub>p B)) x = ClOp (A \<^bold>\<Rrightarrow>\<^sub>p B) x" 
    using cl_expan cl_idem  cl_expan_def cl_idem_def 
          commu_def order_def p_commu_mult p_ordered 
    by metis
qed

lemma c_closed_mult:
  assumes clA: "cClosed ClOp A"
  assumes clB: "cClosed ClOp B"
  shows "cClosed ClOp (A \<^bold>\<star>[ClOp] B)"
  apply (unfold c_mult_def cClosed_def) proof (rule)
  fix x
  show "ClOp (ClOp (A \<^bold>\<star>\<^sub>p B)) x = ClOp (A \<^bold>\<star>\<^sub>p B) x " 
    using cl_expan cl_idem  cl_expan_def cl_idem_def 
          commu_def order_def p_commu_mult p_ordered 
    by metis
qed

lemma c_closed_meet:
  assumes clA: "cClosed ClOp A"
  assumes clB: "cClosed ClOp B"
  shows "cClosed ClOp (A \<^bold>\<inter>[ClOp] B)"
  apply (unfold c_meet_def cClosed_def) proof (rule)
  fix x
  show "ClOp (ClOp (A \<^bold>\<inter>\<^sub>p B)) x = ClOp (A \<^bold>\<inter>\<^sub>p B) x"
    using cl_expan cl_idem  cl_expan_def cl_idem_def 
          commu_def order_def p_commu_mult p_ordered
    by metis
qed

lemma c_closed_join:
  assumes clA: "cClosed ClOp A"
  assumes clB: "cClosed ClOp B"
  shows "cClosed ClOp (A \<^bold>\<union>[ClOp] B)"
  apply (unfold c_join_def cClosed_def) proof (rule)
  fix x
  show "ClOp (ClOp (A \<^bold>\<union>\<^sub>p B)) x = ClOp (A \<^bold>\<union>\<^sub>p B) x"
    using cl_expan cl_idem  cl_expan_def cl_idem_def 
          commu_def order_def p_commu_mult p_ordered
    by metis
qed

lemma c_closed_zero:
  shows "cClosed ClOp (\<^bold>0[ClOp])"
  apply (unfold c_zero_def cClosed_def) proof (rule)
  fix x
  show "ClOp (ClOp \<^bold>0\<^sub>p) x = ClOp \<^bold>0\<^sub>p x"
    using cl_expan cl_idem  cl_expan_def cl_idem_def 
          commu_def order_def p_commu_mult p_ordered
    by metis
qed


lemma c_closed_one:
  shows "cClosed ClOp (\<^bold>1[ClOp])"
  apply (unfold c_one_def cClosed_def) proof (rule)
  fix x
  show "ClOp (ClOp \<^bold>1\<^sub>p) x = ClOp \<^bold>1\<^sub>p x"
    using cl_expan cl_idem  cl_expan_def cl_idem_def 
          commu_def order_def p_commu_mult p_ordered
    by metis
qed

lemma c_closed_bot:
  shows "cClosed ClOp (\<^bold>\<bottom>[ClOp])"
  apply (unfold c_bot_def cClosed_def) proof (rule)
  fix x
  show "ClOp (ClOp \<^bold>\<bottom>\<^sub>p) x = ClOp \<^bold>\<bottom>\<^sub>p x"
    using cl_expan cl_idem  cl_expan_def cl_idem_def 
          commu_def order_def p_commu_mult p_ordered
    by metis
qed

lemma c_closed_top:
  shows "cClosed ClOp (\<^bold>\<top>[ClOp])"
  apply (unfold c_top_def cClosed_def) proof (rule)
  fix x
  show "ClOp \<^bold>\<top>\<^sub>p x = \<^bold>\<top>\<^sub>p x"
    using cl_expan cl_idem  cl_expan_def cl_idem_def 
          commu_def order_def p_commu_mult p_ordered
          p_refl_order p_antisy_order p_transi_order
    (* partial order axioms are missing *)
    sorry
  oops


subsection "Proofs for residuated lattice proofs"

subsubsection "commutative monoid with the unit 1"
(*
definition "commu Op \<equiv> \<forall> a b. Op a b = Op b a"
definition "unitE Op One \<equiv> \<forall> a. Op a One = a"
definition "assoc Op \<equiv> \<forall> x y z. Op (Op x y) z = Op x (Op y z)"
*)


lemma c_commu_mult: 
  assumes "cClosed ClOp a"
  assumes "cClosed ClOp b"
  shows "(a \<^bold>\<star>[ClOp] b) = (b \<^bold>\<star>[ClOp] a)"
  by (metis c_mult_def commu_def p_commu_mult)
lemma c_unitE_mult: 
  assumes "cClosed ClOp a"
  shows "(a \<^bold>\<star>[ClOp] (\<^bold>1[ClOp])) = a"
  apply (unfold c_mult_def c_one_def) proof (rule)
  fix x
  show "ClOp (a \<^bold>\<star>\<^sub>p ClOp \<^bold>1\<^sub>p) x = a x"
    using p_refl_order p_antisy_order p_transi_order
    by (metis assms cClosed_def cl_expan cl_expan_def commu_def order_def p_commu_mult p_idemp_mult p_ordered unitE_def)
qed
lemma c_assoc_mult: 
  assumes "cClosed ClOp a"
  assumes "cClosed ClOp b"
  assumes "cClosed ClOp c"
  shows "((a \<^bold>\<star>[ClOp] b) \<^bold>\<star>[ClOp] c) = (a \<^bold>\<star>[ClOp] (b \<^bold>\<star>[ClOp] c))"
  apply (unfold c_mult_def)
  using p_assoc_mult assms
  oops
(*  by (smt (z3) assoc_def cl_distr cl_distr_def cl_expan cl_expan_def cl_idem cl_idem_def cl_mono cl_mono_def commu_def order_def p_commu_mult p_ordered)*)


subsubsection "bounded lattice for Meet"

lemma c_commu_meet: 
  assumes "cClosed ClOp a"
  assumes "cClosed ClOp b"
  shows "(a \<^bold>\<inter>[ClOp] b) = (b \<^bold>\<inter>[ClOp] a)"
  by (metis c_meet_def commu_def p_commu_meet)

lemma c_assoc_meet: 
  assumes "cClosed ClOp a"
  assumes "cClosed ClOp b"
  assumes "cClosed ClOp c"
  shows "((a \<^bold>\<inter>[ClOp] b) \<^bold>\<inter>[ClOp] c) = (a \<^bold>\<inter>[ClOp] (b \<^bold>\<inter>[ClOp] c))"
  apply (unfold c_meet_def)
  using p_commu_meet c_closed_meet antisy_def assms 
        c_meet_def c_mult_def c_unitE_mult cl_expan 
        cl_expan_def cl_idem cl_idem_def idemp_def 
        p_antisy_order p_idemp_meet
  oops

lemma c_idem_meet: 
  assumes "cClosed ClOp a"
  shows "(a \<^bold>\<inter>[ClOp] a) = a"
  by (smt (verit) antisy_def assms c_meet_def c_mult_def c_unitE_mult cl_expan cl_expan_def cl_idem cl_idem_def idemp_def p_antisy_order p_idemp_meet)

lemma c_great_meet: 
  assumes "cClosed ClOp a"
  shows "(a \<^bold>\<inter>[ClOp] \<^bold>\<top>[ClOp]) = a"
  apply (unfold c_meet_def)
    using p_commu_meet c_closed_meet antisy_def assms 
        c_meet_def c_mult_def c_unitE_mult cl_expan 
        cl_expan_def cl_idem cl_idem_def idemp_def 
        p_antisy_order p_idemp_meet
    by (smt (verit) c_top_def extre_def great_def p_great_meet)



subsubsection "bounded lattice for Join"


lemma c_commu_join: 
  assumes "cClosed ClOp a"
  assumes "cClosed ClOp b"
  shows "(a \<^bold>\<union>[ClOp] b) = (b \<^bold>\<union>[ClOp] a)"
  by (metis c_join_def commu_def p_commu_join)

lemma c_assoc_meet: 
  assumes "cClosed ClOp a"
  assumes "cClosed ClOp b"
  assumes "cClosed ClOp c"
  shows "((a \<^bold>\<union>[ClOp] b) \<^bold>\<union>[ClOp] c) = (a \<^bold>\<union>[ClOp] (b \<^bold>\<union>[ClOp] c))"
  apply (unfold c_join_def)
  using p_commu_join c_closed_join antisy_def assms 
        c_join_def c_mult_def c_unitE_mult cl_expan 
        cl_expan_def cl_idem cl_idem_def idemp_def 
        p_antisy_order p_idemp_join
  oops

lemma c_idem_join: 
  assumes "cClosed ClOp a"
  shows "(a \<^bold>\<union>[ClOp] a) = a"
  by (smt (verit) antisy_def assms c_join_def c_mult_def c_unitE_mult cl_expan cl_expan_def cl_idem cl_idem_def idemp_def p_antisy_order p_idemp_join)

lemma c_least_join: 
  assumes "cClosed ClOp a"
  shows "(a \<^bold>\<union>[ClOp] \<^bold>\<bottom>[ClOp]) = a"
  apply (unfold c_join_def c_bot_def)
    using p_commu_join c_closed_join antisy_def assms 
        c_join_def c_mult_def c_unitE_mult cl_expan 
        cl_expan_def cl_idem cl_idem_def idemp_def 
        p_antisy_order p_idemp_join assms
    oops



subsubsection "bounded lattice for Join and Meet"

lemma c_absorb_meetjoin: 
  assumes "cClosed ClOp a"
  assumes "cClosed ClOp b"
  shows "(a \<^bold>\<inter>[ClOp] (a \<^bold>\<union>[ClOp] b)) = a"
  apply (unfold c_meet_def c_join_def)
  oops

lemma c_absorb_joinmeet: 
  assumes "cClosed ClOp a"
  assumes "cClosed ClOp b"
  shows "(a \<^bold>\<union>[ClOp] (a \<^bold>\<inter>[ClOp] b)) = a"
  apply (unfold c_meet_def c_join_def)
  oops


  subsubsection "residuated lattice"

(* definition "resid Ord Mult Impl \<equiv> 
\<forall> x y z. Ord (Mult x y) z = Ord x (Impl y z)" *)

lemma c_assoc_meet: 
  assumes "cClosed ClOp a"
  assumes "cClosed ClOp b"
  assumes "cClosed ClOp c"
  shows "((x \<^bold>\<star>[ClOp] y) \<^bold>\<le>\<^sub>c z) = (x \<^bold>\<le>\<^sub>c (y \<^bold>\<Rrightarrow>[ClOp] z))"
  apply (unfold c_mult_def c_ord_def c_impl_def)
  oops



end