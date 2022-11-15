theory Chap2_Theorem5
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


section "Downward Closedness"

type_synonym p = "m \<Rightarrow> bool"
type_synonym p_cl = "p \<Rightarrow> p"


definition downwardClosed :: "p \<Rightarrow> bool" where
"downwardClosed P \<equiv> \<forall> x. (P x \<longrightarrow> (\<forall> y. (y \<^bold>\<le>\<^sub>m x) \<longrightarrow> P y ))"
definition downwardClosedOp :: "p_cl \<Rightarrow> bool" where
"downwardClosedOp Cl \<equiv> \<forall> X. (cClosed Cl X \<longrightarrow> downwardClosed X)"

definition downSet :: "m \<Rightarrow> p" (" \<langle>_] ") where
"\<langle> b ] \<equiv> \<lambda> x. (x \<^bold>\<le>\<^sub>m b)"
definition UBase :: "p_cl \<Rightarrow> p" where
"UBase Cl \<equiv> \<lambda> b. cClosed Cl \<langle> b ]"



section "Closure Conditions"


type_synonym p_op = "p \<Rightarrow> p \<Rightarrow> p"
type_synonym p_rel = "p \<Rightarrow> p \<Rightarrow> bool"
type_synonym p_set = "p \<Rightarrow> bool"

consts ClOp :: p_cl
consts p_order :: p_rel (infixr "\<^bold>\<le>\<^sub>p" 55)
consts p_prod :: p_op (infixr "\<^bold>\<star>\<^sub>p" 55)
consts p_impl :: p_op (infixr "\<^bold>\<Rrightarrow>\<^sub>p" 55)


axiomatization where
cl_expan: "cl_expan ClOp (\<^bold>\<le>\<^sub>p)" and
cl_mono: "cl_mono ClOp (\<^bold>\<le>\<^sub>p)" and
cl_idem: "cl_idem ClOp (\<^bold>\<le>\<^sub>p)" and
cl_distr: "cl_distr ClOp (\<^bold>\<le>\<^sub>p) (\<^bold>\<star>\<^sub>p)" and
cl_downClosed: "\<forall> X. cClosed ClOp X \<longrightarrow> downwardClosed X"
(* condition 2 is missing *)



section "Theorem 5"


definition hMap :: "m \<Rightarrow> p" where
"hMap b = \<langle> b ]"
(* is a complete embedding, i.e. an order isomorphism, 
which preserves all existing products and residuals in U,
and also all existing (infinite) joins and meets in U, 
where U is the base for C in M *)


section "order isomorphism"

definition "preserv Base PConn CConn Map 
\<equiv> \<forall> x y. Base x \<and> Base y \<and> Base (PConn x y) \<longrightarrow> CConn (Map x) (Map y)"



axiomatization where
m_ord_refl: "\<forall> x. x \<^bold>\<le>\<^sub>m x" and
m_ord_antisym: "\<forall> x y. x \<^bold>\<le>\<^sub>m y \<and> y \<^bold>\<le>\<^sub>m x \<longrightarrow> x = y" and
m_ord_trans: "\<forall> x y z. x \<^bold>\<le>\<^sub>m y \<longrightarrow> x \<^bold>\<sqdot>\<^sub>m z \<^bold>\<le>\<^sub>m y \<^bold>\<sqdot>\<^sub>m z"and
m_ord_mono: "\<forall> x y z. x \<^bold>\<le>\<^sub>m y \<and> y \<^bold>\<le>\<^sub>m z \<longrightarrow> x \<^bold>\<le>\<^sub>m z"

definition c_mult :: "p \<Rightarrow> p_cl \<Rightarrow> p \<Rightarrow> p" ("_ \<^bold>\<star>[_] _" 55)where
"X \<^bold>\<star>[Cl] Y \<equiv> Cl (\<lambda> m. (X \<^bold>\<star>\<^sub>p Y) m)"



lemma preserve_mult:
  assumes 1: "(UBase ClOp a) \<and> (UBase ClOp b)"
  assumes 2: "UBase ClOp (a \<^bold>\<sqdot>\<^sub>m b)"
  shows "((hMap a) \<^bold>\<star>[ClOp] (hMap b)) = hMap (a \<^bold>\<sqdot>\<^sub>m b)"
proof -
  have "((hMap a) \<^bold>\<star>[ClOp] (hMap b)) = (\<langle> a ] \<^bold>\<star>[ClOp] \<langle> b ])"
    by (simp add: hMap_def)
  also have "... = ClOp (\<langle> a ] \<^bold>\<star>\<^sub>p \<langle> b ])"
    by (simp add: c_mult_def)
  also have "... = \<langle> a \<^bold>\<sqdot>\<^sub>m b ]"
    sorry (* <==== here has to be the least cClosed fixpoint argument*)
  also have "... = hMap (a \<^bold>\<sqdot>\<^sub>m b)"
    by (simp add: hMap_def)
  finally show ?thesis .
qed


definition c_impl :: "p \<Rightarrow> p_cl \<Rightarrow> p \<Rightarrow> p" (" _ \<^bold>\<Rrightarrow>[_] _" 55) where
"X \<^bold>\<Rrightarrow>[Cl] Y \<equiv> Cl (\<lambda> m. (X \<^bold>\<Rrightarrow>\<^sub>p Y) m)"
consts m_impl :: "m \<Rightarrow> m \<Rightarrow> m" (infixr "\<^bold>\<rightarrow>\<^sub>m" 55)


lemma preserve_impl:
  assumes 1: "(UBase ClOp a) \<and> (UBase ClOp b)"
  assumes 2: "UBase ClOp (a \<^bold>\<sqdot>\<^sub>m b)"
  shows "((hMap a) \<^bold>\<Rrightarrow>[ClOp] (hMap b)) = hMap (a \<^bold>\<rightarrow>\<^sub>m b)"
proof -
  have "((hMap a) \<^bold>\<Rrightarrow>[ClOp] (hMap b)) = (\<langle> a ] \<^bold>\<Rrightarrow>[ClOp] \<langle> b ])"
    by (simp add: hMap_def)
  also have "... = ClOp (\<langle> a ] \<^bold>\<Rrightarrow>\<^sub>p \<langle> b ])"
    by (simp add: c_impl_def)
  also have "... = \<langle> a \<^bold>\<rightarrow>\<^sub>m b ]"
    sorry (* <==== here has to be the maximal cClosed set  argument*)
  also have "... = hMap (a \<^bold>\<rightarrow>\<^sub>m b)"
    by (simp add: hMap_def)
  finally show ?thesis .


qed


end