theory Chapter0 
imports Main
begin

section "Predefinitions"

type_synonym 'w \<sigma> = \<open>'w \<Rightarrow> bool\<close> (* set of worlds - propositions *)
type_synonym 'w pow  = \<open>'w \<sigma> \<Rightarrow> bool\<close> (* powerset of set of worlds - set of propositions *)
type_synonym 'w cl  = \<open>'w \<sigma> \<Rightarrow> 'w \<sigma>\<close> (* type for closure operator *)
type_synonym 'w rel  = \<open>'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> bool\<close> (* type for closure operator *)


abbreviation "isEmpty S \<equiv> \<forall>x. \<not>S x"
abbreviation "nonEmpty S \<equiv> \<exists>x. S x"
abbreviation containment (infix "\<sqsubseteq>" 100) 
  where "D \<sqsubseteq> S \<equiv>  \<forall>X. D X \<longrightarrow> S X" (*read as "all Ds are contained in S"*)
(*
definition sub_coll :: "('w \<sigma> \<Rightarrow> bool) \<Rightarrow> ('w \<sigma> \<Rightarrow> bool) \<Rightarrow> bool" (infixr "\<^bold>\<sqsubseteq>" 50)
  where "D \<^bold>\<sqsubseteq> T \<equiv> \<forall> A . D A \<longrightarrow> T A"
*)

(* inclusion-based order structure on sets *)
definition subset::"'w rel" (infixr "\<^bold>\<preceq>" 45) 
  where "A \<^bold>\<preceq> B \<equiv> \<forall>w. (A w) \<longrightarrow> (B w)"
abbreviation superset::"'w rel" (infixr "\<^bold>\<succeq>" 45) 
  where "B \<^bold>\<succeq> A \<equiv> A \<^bold>\<preceq> B"
definition setequ::"'w rel" (infixr "\<^bold>\<approx>" 45) 
  where "A \<^bold>\<approx> B \<equiv>  \<forall>w. (A w) \<longleftrightarrow> (B w)"

(**These (trivial) lemmas are intended to help automated tools.*)
lemma setequ_char: "\<phi> \<^bold>\<approx> \<psi> \<equiv> \<forall>w. \<phi> w \<longleftrightarrow> \<psi> w" by (rule setequ_def)
lemma setequ_equ: "\<phi> \<^bold>\<approx> \<psi> \<equiv> \<phi> = \<psi>"  proof - (*why so complicated?*)
  have lr: "\<phi> \<^bold>\<approx> \<psi> \<Longrightarrow> \<phi> = \<psi>" unfolding setequ_char by auto
  have rl: "\<phi> = \<psi> \<Longrightarrow> \<phi> \<^bold>\<approx> \<psi>" unfolding setequ_char by simp
  from lr rl show "\<phi> \<^bold>\<approx> \<psi> \<equiv> \<phi> = \<psi>" by linarith
qed

definition singleton ("\<lbrace>_\<rbrace>") where "\<lbrace>x\<rbrace> \<equiv> \<lambda>y. y=x"
lemma singleton_diff: "\<forall>p q. p \<noteq> q \<longleftrightarrow> \<not>(\<lbrace>p\<rbrace> \<^bold>\<approx> \<lbrace>q\<rbrace>)" by (metis singleton_def setequ_equ)


(* bounded Lattice operators *)
definition meet::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<and>" 54) 
  where "A \<^bold>\<and> B \<equiv> \<lambda>w. (A w) \<and> (B w)"
definition join::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<or>" 53) 
  where "A \<^bold>\<or> B \<equiv> \<lambda>w. (A w) \<or> (B w)"
definition top::"'w \<sigma>" ("\<^bold>\<top>")    
  where "\<^bold>\<top> \<equiv> \<lambda>w. True"
definition bottom::"'w \<sigma>" ("\<^bold>\<bottom>") 
  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"

(* Boolean algebra operators *)
definition compl::"'w \<sigma> \<Rightarrow> 'w \<sigma>" ("\<^bold>\<midarrow>_"[57]58)
  where "\<^bold>\<midarrow>A  \<equiv> \<lambda>w. \<not>(A w)" (** (set-)complement*)
definition impl::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<rightarrow>" 51)
  where "A \<^bold>\<rightarrow> B \<equiv> \<lambda>w. (A w) \<longrightarrow> (B w)" (** (set-)implication*)
definition diff::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<leftharpoonup>" 51) 
  where "A \<^bold>\<leftharpoonup> B \<equiv> \<lambda>w. (A w) \<and> \<not>(B w)" (** (set-)difference*)
definition dimpl::"'w \<sigma> \<Rightarrow> 'w \<sigma> \<Rightarrow> 'w \<sigma>" (infixr "\<^bold>\<leftrightarrow>" 51) 
  where "A \<^bold>\<leftrightarrow> B \<equiv> (A \<^bold>\<rightarrow> B) \<^bold>\<and> (B \<^bold>\<rightarrow> A)" (** double implication*)

(* infinite Boolean algebras *)
(**We start by defining infinite meet (infimum) and infinite join (supremum) operations,*)
definition infimum:: "('w \<sigma> \<Rightarrow> bool) \<Rightarrow> 'w \<sigma>" ("\<^bold>\<And>_") 
  where "\<^bold>\<And>S \<equiv> \<lambda>w. \<forall>X. S X \<longrightarrow> X w"
definition supremum::"('w \<sigma> \<Rightarrow> bool) \<Rightarrow> 'w \<sigma>" ("\<^bold>\<Or>_") 
  where "\<^bold>\<Or>S \<equiv> \<lambda>w. \<exists>X. S X  \<and>  X w"

(* closedness/stabillity properties *)

(**Some additional relevant definitions and properties*)

definition "meet_closed S \<equiv>  \<forall>X Y. (S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<and> Y)"
definition "join_closed S \<equiv>  \<forall>X Y. (S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<or> Y)"

(* closed under arbitrary (resp. nonempty) supremum/infimum.*)
definition "infimum_closed S  \<equiv> \<forall>D. D \<sqsubseteq> S \<longrightarrow> S(\<^bold>\<And>D)" (*observe that D can be empty*)
definition "supremum_closed S \<equiv> \<forall>D. D \<sqsubseteq> S \<longrightarrow> S(\<^bold>\<Or>D)"
definition "infimum_closed' S  \<equiv> \<forall>D. nonEmpty D \<and> D \<sqsubseteq> S \<longrightarrow> S(\<^bold>\<And>D)"
definition "supremum_closed' S \<equiv> \<forall>D. nonEmpty D \<and> D \<sqsubseteq> S \<longrightarrow> S(\<^bold>\<Or>D)"

definition "upwards_closed S \<equiv> \<forall>X Y. S X \<and> X \<^bold>\<preceq> Y \<longrightarrow> S Y"
definition "downwards_closed S \<equiv> \<forall>X Y. S X \<and> X \<^bold>\<succeq> Y \<longrightarrow> S Y"

(* Duality *)


(* dual of a unary operator *)
definition op_dual::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("(_\<^sup>d)") 
  where "\<phi>\<^sup>d \<equiv> \<lambda>X. \<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>X))"



end