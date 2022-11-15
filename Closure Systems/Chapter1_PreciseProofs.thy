theory Chapter1_PreciseProofs
  imports Chapter0
begin

section "1 Topology  Definition"

(* A topology on a set X is a collection T of subsets of X, 
including the empty set \<emptyset> and X itself, 
in which T is closed under arbitrary union and finite intersection *)

definition closed_topo :: "('w \<sigma> \<Rightarrow> bool) \<Rightarrow> bool"
  where "closed_topo T \<equiv> T \<^bold>\<top> \<and> T \<^bold>\<bottom> 
                \<and> supremum_closed T
                \<and> meet_closed T"

definition open_topo :: "('w \<sigma> \<Rightarrow> bool) \<Rightarrow> bool"
  where "open_topo T \<equiv> T \<^bold>\<top> \<and> T \<^bold>\<bottom> 
                \<and> infimum_closed T
                \<and> join_closed T"



section "2 Closure Operator Axioms"

(*
Associated with any topology T is the topological closure operator, 
denoted Cl, which gives, for any subset A \<subseteq> X, 
the smallest closed set containing A. 

Obviously, a set A is closed if and only if Cl(A) = A. 
Therefore, we can treat T as the collection of all fixed points of the Cl operator. 
Here and below, we call a set A \<subseteq> X a fixed point of an operator Op 
if and only if Op(A) = A.
*)

(* fix point definition *)
definition fixpoint_op::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> 'w \<sigma>)" ("(_\<^sup>f\<^sup>p)") 
  where "\<phi>\<^sup>f\<^sup>p  \<equiv> \<lambda>X. (\<phi> X) \<^bold>\<leftrightarrow> X"
definition fixpoint_pred::"('w \<sigma> \<Rightarrow> 'w \<sigma>) \<Rightarrow> ('w \<sigma> \<Rightarrow> bool)" ("fp")
  where "fp \<phi> \<equiv> \<lambda>X. \<phi> X \<^bold>\<approx> X"


(*
Denote P(X) as the powerset of X. 
Then Cl as defined above is viewed as an operator Cl : P(X) \<rightarrow> P(X) 
that satisfies the following properties (for any sets A, B \<subseteq> X):
[CO1] Cl(\<emptyset>) = \<emptyset>;
[CO2] A \<subseteq> Cl(A);
[CO3] Cl(Cl(A)) = Cl(A);
[CO4] Cl(A \<union> B) = Cl(A) \<union> Cl(B).
*)

(* Normality (NORM) *)
definition CO1::"'w cl \<Rightarrow> bool" ("NORM") 
  where "CO1 Cl \<equiv> (Cl \<^bold>\<bottom>) \<^bold>\<approx> \<^bold>\<bottom>"
(* Expansive (EXPN) *)
definition CO2::"'w cl \<Rightarrow> bool" ("EXPN") 
  where "CO2 Cl \<equiv> \<forall>A. A \<^bold>\<preceq> Cl A"
(* Idempotent (IDEM) *)
definition CO3::"'w cl \<Rightarrow> bool" ("IDEM") 
  where "CO3 Cl \<equiv> \<forall>A. (Cl A) \<^bold>\<approx> Cl(Cl A)"
(* Additivity (ADDI) *)
definition CO4::"'w cl \<Rightarrow> bool" ("ADDI") 
  where "CO4 Cl \<equiv> \<forall>A B. Cl(A \<^bold>\<or> B) \<^bold>\<approx> (Cl A) \<^bold>\<or> (Cl B)"

definition closure_op :: "'w cl \<Rightarrow> bool"
  where "closure_op \<equiv> CO1 \<^bold>\<and> CO2 \<^bold>\<and> CO3 \<^bold>\<and> CO4"

(*
named_theorems closure_def (*to group together order-related definitions*)
declare 
  CO1_def[closure_def] 
  CO2_def[closure_def]
  CO3_def[closure_def] 
  CO4_def[closure_def]
*)

(*
Indeed, any operator Cl on P(X)
that satisfies the above four axioms (called Kuratowski Closure Axioms) 
defines a topological closure operator. 
Its fixed points {A| Cl(A) = A} form a set system
that can be properly identified as a collection of closed sets 
*)



section "1nd Topo-Condition for bottom-element"


(* sledgehammer proof *)
lemma 
  assumes "CO1 Cl"
  shows "(fp Cl) \<^bold>\<bottom>"
  by (meson CO1_def assms fixpoint_pred_def)


lemma 
  assumes 1: "CO1 Cl"
  shows "(fp Cl) \<^bold>\<bottom>" 
proof (unfold bottom_def fixpoint_pred_def setequ_equ, rule)
  fix w
  have "(Cl \<^bold>\<bottom>) \<^bold>\<approx> \<^bold>\<bottom>" using CO1_def assms by auto
  hence "(Cl (\<lambda>w. False)) w = (\<lambda>w. False) w" 
    using bottom_def setequ_def by (metis setequ_equ)
  thus "(Cl (\<lambda>w. False)) w = False" by (simp)
qed


section "2nd Topo-Condition for top-element"

lemma 
  assumes "CO2 Cl"
  shows "(fp Cl) \<^bold>\<top>"
  by (metis (mono_tags, lifting) 
        CO2_def assms 
        fixpoint_pred_def 
        setequ_def subset_def top_def)


lemma 
  fixes Cl
  assumes 1: "CO2 Cl"
  shows "(fp Cl) \<^bold>\<top>" 
  apply (unfold top_def fixpoint_pred_def setequ_equ)
proof (rule, rule iffI)
  fix w
  show l2r: "Cl (\<lambda>w. True) w \<Longrightarrow> True" by simp
next
  fix w
  show r2l: "True \<Longrightarrow> (Cl (\<lambda>w. True)) w"
  proof -
    have "\<forall>A. A \<^bold>\<preceq> Cl A" using CO2_def assms by auto
    hence "(\<lambda>w. True) \<^bold>\<preceq> Cl (\<lambda>w. True)" by simp
    thus "True \<Longrightarrow> (Cl (\<lambda>w. True)) w" by (simp add: subset_def)
  qed
qed



section "3rd topo-condition for infimum_closed (fp Cl)"

(* tbc *)




section "4rd topo-condition for join_closed (fp Cl)"

lemma
  fixes Cl
  assumes co2: "CO2 Cl"
  assumes co4: "CO4 Cl"
  shows "join_closed (fp Cl)" 
  (*by (smt (verit) CO4_def assms fixpoint_pred_def join_closed_def setequ_equ)*)
  apply (unfold join_closed_def fixpoint_pred_def setequ_equ join_def)
proof (rule, rule, rule, rule)
  fix X Y w
  assume fixP: "Cl X = X \<and> Cl Y = Y"
  show "Cl (\<lambda>w. X w \<or> Y w) w = (X w \<or> Y w)"
  proof
    assume clXY: "Cl (\<lambda>w. X w \<or> Y w) w"
    show "X w \<or> Y w" 
      (*by (metis CO4_def clXY co4 fixP join_def setequ_char setequ_equ)*)
    proof -
      from clXY have rw: "Cl (\<lambda>w. X w \<or> Y w) \<^bold>\<approx> Cl(X \<^bold>\<or> Y)" by (simp add: join_def setequ_equ)
      have "Cl(X \<^bold>\<or> Y) \<^bold>\<approx> (Cl X) \<^bold>\<or> (Cl Y)" using assms CO4_def by auto
      hence "Cl(X \<^bold>\<or> Y) \<^bold>\<approx> (X \<^bold>\<or> Y)" using fixP by simp
      hence "Cl (\<lambda>w. (X w) \<or> (Y w)) w \<longleftrightarrow> (\<lambda>w. (X w) \<or> (Y w)) w" using join_def setequ_def rw by metis
      hence "Cl (\<lambda>w. (X w) \<or> (Y w)) w \<longrightarrow> (X w \<or> Y w)" by simp
      thus ?thesis by (simp add: clXY)
    qed
  next
    assume XY: "X w \<or> Y w"
    show "Cl (\<lambda>w. X w \<or> Y w) w" 
    proof -
      have "\<forall>A. A \<^bold>\<preceq> Cl A" using co2 CO2_def by auto
      thus ?thesis by (metis XY subset_def)
    qed
  qed
qed

end
