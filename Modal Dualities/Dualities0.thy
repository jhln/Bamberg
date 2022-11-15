theory Dualities0
imports Main
begin



(*
lemma "(\<forall> w. (A \<^bold>\<rightarrow> \<C>[R](\<C>[R] A)) w) = (\<forall>a b c. R a b \<and> R b c \<longrightarrow> R a c)"
  oops
lemma "((\<forall> w. (A \<^bold>\<rightarrow> \<C>[R](\<C>[R] A) ) w) \<and> (\<forall> w. (A \<^bold>\<rightarrow> \<C>[R] A ) w)) = (\<forall>a b c. R a b \<and> R b c \<longrightarrow> R a c)"
*)


(* Relation type *)

type_synonym 'a \<rho> = \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>

(* accessibility relation properties and correspondence formula *)

definition reflexive :: "'a \<rho> \<Rightarrow> bool" where
\<open>reflexive R \<equiv> \<forall>w. R w w\<close> (* \<box>p \<rightarrow> p *)
definition transitive :: "'a \<rho> \<Rightarrow> bool" where
\<open>transitive R \<equiv> \<forall>a b c. R a b \<and> R b c \<longrightarrow> R a c\<close> (* \<box>p \<rightarrow> \<box>\<box>p *)
definition symmetric :: "'a \<rho> \<Rightarrow> bool" where
\<open>symmetric R \<equiv> \<forall>u v. R u v \<longrightarrow> R v u\<close> (* p \<rightarrow> \<box>\<diamondsuit>p *)
definition serial :: "'a \<rho> \<Rightarrow> bool" where
\<open>serial R \<equiv> \<forall>u. \<exists>v. R u v\<close> (* \<box>p \<rightarrow> \<diamondsuit>p *)
definition euclidean :: "'a \<rho> \<Rightarrow> bool" where
\<open>euclidean R \<equiv> \<forall>r s t. R r s \<and> R r t \<longrightarrow> R s t\<close> (* \<diamondsuit>p \<rightarrow> \<box>\<diamondsuit>p *)



(* modal logic embedding *)

(*type for propositions as 
(characteristic functions of) sets*)
type_synonym 'w \<sigma> = \<open>'w \<Rightarrow> bool\<close>

definition top::"'w \<sigma>" 
("\<^bold>\<top>") where 
"\<^bold>\<top> \<equiv> \<lambda> w. True" 
definition neg::"'w \<sigma> \<Rightarrow> 'w \<sigma>" 
("\<^bold>\<not>_"[52]53) where 
"\<^bold>\<not> \<phi> \<equiv> \<lambda> w. \<not> (\<phi> w)" 
definition conj::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" 
(infixr"\<^bold>\<and>"51) where 
"\<phi> \<^bold>\<and> \<psi> \<equiv> \<lambda>w. (\<phi> w) \<and> (\<psi> w)"   
definition disj::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>"
(infixr"\<^bold>\<or>"50)  where 
"\<phi> \<^bold>\<or> \<psi> \<equiv> \<lambda> w. (\<phi> w) \<or> (\<psi> w)"   
definition impl::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" 
(infixr"\<^bold>\<rightarrow>"49)  where 
"\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<lambda> w. (\<phi> w) \<longrightarrow> (\<psi> w)"
definition equ::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" 
(infixr"\<^bold>\<leftrightarrow>"49)  where 
"\<phi> \<^bold>\<leftrightarrow> \<psi> \<equiv> \<lambda> w. (\<phi> w) \<longleftrightarrow> (\<psi> w)"
definition box::"'w \<rho> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" 
("\<^bold>\<box>\<^sub>_ _") where 
"\<^bold>\<box>\<^sub>R \<phi> \<equiv> \<lambda> w. \<forall> v. (R w v) \<longrightarrow> (\<phi> v)"
definition dia::"'w \<rho> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" 
("\<^bold>\<diamondsuit>\<^sub>_ _") where 
"\<^bold>\<diamondsuit>\<^sub>R \<phi> \<equiv> \<lambda> w. \<exists> q. (R w q) \<and> (\<phi> q)"

end