theory Chapter1
  imports Chapter0
begin

section "1 Topology  Definition"

(* A topology on a set X is a collection T of subsets of X, 
including the empty set \<emptyset> and X itself, 
in which T is closed under arbitrary union and finite intersection *)


definition open_topo :: "('w \<sigma> \<Rightarrow> bool) \<Rightarrow> bool"
  where "open_topo T \<equiv> T \<^bold>\<top> \<and> T \<^bold>\<bottom> 
                \<and> supremum_closed T
                \<and> meet_closed T"

definition closed_topo :: "('w \<sigma> \<Rightarrow> bool) \<Rightarrow> bool"
  where "closed_topo T \<equiv> T \<^bold>\<top> \<and> T \<^bold>\<bottom> 
                \<and> join_closed T
                \<and> infimum_closed T"

                


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

named_theorems closure_def (*to group together order-related definitions*)
declare 
  CO1_def[closure_def] 
  CO2_def[closure_def]
  CO3_def[closure_def] 
  CO4_def[closure_def]

(*
Indeed, any operator Cl on P(X)
that satisfies the above four axioms (called Kuratowski Closure Axioms) 
defines a topological closure operator. 
Its fixed points {A| Cl(A) = A} form a set system
that can be properly identified as a collection of closed sets 
*)

lemma 
  (*assumes "closure_op Cl"*)
  fixes Cl
  assumes "closure_op Cl"
  shows "closed_topo (fp Cl)"
  unfolding closed_topo_def
proof 
  show "fp Cl \<^bold>\<top>"
  proof (unfold fixpoint_pred_def setequ_def top_def, rule, rule)
    fix w
    show l2r: "Cl (\<lambda>w. True) w \<Longrightarrow> True" by simp
  next
    fix w
    show r2l: "True \<Longrightarrow> (Cl (\<lambda>w. True)) w" 
    proof -
      have "\<forall>A. A \<^bold>\<preceq> Cl A" 
        using CO2_def assms closure_op_def meet_def by metis
    hence "(\<lambda>w. True) \<^bold>\<preceq> Cl (\<lambda>w. True)" by simp
    thus "True \<Longrightarrow> (Cl (\<lambda>w. True)) w" by (simp add: subset_def)
  qed
qed
next
  show "fp Cl \<^bold>\<bottom> \<and> join_closed (fp Cl) \<and> infimum_closed (fp Cl)"
    apply (rule conjI)
  proof -


    from assms 
    have "CO2 Cl" by (simp add: closure_op_def meet_def)
    thus "\<And>w. Cl (\<lambda>w. True) w" 
      by (simp add: CO2_def subset_def)
  qed
next
  show "fp Cl \<^bold>\<bottom> \<and> join_closed (fp Cl) \<and> infimum_closed (fp Cl)"
  proof
    from assms 
    have 1: "CO1 Cl" by (simp add: closure_op_def meet_def)
    thus "fp Cl \<^bold>\<bottom>" by (simp add: CO1_def fixpoint_pred_def)
  next
    show "join_closed (fp Cl) \<and> infimum_closed (fp Cl)" 
      apply ( rule conjI )
       apply ( unfold join_closed_def join_def fixpoint_pred_def setequ_def)
       apply (rule allI, rule allI, rule impI, rule allI, rule iffI)
      apply auto
    proof -
      from assms
      have 4: "CO4 Cl" by (simp add: closure_op_def meet_def)
      thus "\<And>X Y w. Cl (\<lambda>w. X w \<or> Y w) w \<Longrightarrow> \<forall>w. Cl X w = X w \<Longrightarrow> \<forall>w. Cl Y w = Y w \<Longrightarrow> \<not> Y w \<Longrightarrow> X w" 
        by (simp add: CO4_def join_def setequ_equ)
    next
      show "\<And>X Y w. \<forall>w. Cl X w = X w \<Longrightarrow> \<forall>w. Cl Y w = Y w \<Longrightarrow> X w \<Longrightarrow> Cl (\<lambda>w. X w \<or> Y w) w"
      proof -
        from assms
        have 4: "CO4 Cl" by (simp add: closure_op_def meet_def)
        thus "\<And>X Y w. \<forall>w. Cl X w = X w \<Longrightarrow> \<forall>w. Cl Y w = Y w \<Longrightarrow> X w \<Longrightarrow> Cl (\<lambda>w. X w \<or> Y w) w"
          by (simp add: CO4_def join_def setequ_equ)
      qed
    next
      show "\<And>X Y w. \<forall>w. Cl X w = X w \<Longrightarrow> \<forall>w. Cl Y w = Y w \<Longrightarrow> Y w \<Longrightarrow> Cl (\<lambda>w. X w \<or> Y w) w"
      proof -
        from assms
        have 4: "CO4 Cl" by (simp add: closure_op_def meet_def)
        thus "\<And>X Y w. \<forall>w. Cl X w = X w \<Longrightarrow> \<forall>w. Cl Y w = Y w \<Longrightarrow> Y w \<Longrightarrow> Cl (\<lambda>w. X w \<or> Y w) w"
          by (simp add: CO4_def join_def setequ_equ)
      qed
    next
      show "infimum_closed (\<lambda>X. \<forall>w. Cl X w = X w)"
        apply (unfold infimum_closed_def infimum_def)
        apply (rule allI, rule impI, rule allI, rule iffI)
        apply (rule allI )
      proof
        show "\<And>D w X. D \<sqsubseteq> (\<lambda>X. \<forall>w. Cl X w = X w) \<Longrightarrow> Cl (\<lambda>w. D \<sqsubseteq> (\<lambda>X. X w)) w \<Longrightarrow> D X \<Longrightarrow> X w" sledgehammer





(*
We can then take set-complement of each of these closed sets 
to obtain another collection (i.e., another system of sets), 
which properly form an (open set) topology
*)

lemma 
  assumes "closure_op Cl" 
  shows "open_topo (\<lambda>X. fp Cl (\<^bold>\<midarrow> X))" sorry




section "3 Interior Operator Axioms"

(*
Dual to the topological closure operator 
is the topological interior operator Int, 
which satisfies the following four axioms (for any sets A, B \<subseteq> X):
[IO1] Int(X) = X;
[IO2] Int(A) \<subseteq> A;
[IO3] Int(Int(A)) = Int(A);
[IO4] Int(A \<inter> B) = Int(A) \<inter> Int(B).
The fixed points of Int, the set system {A |Int(A) = A}, 
form a system of subsets of X that will be called “open sets”, 
hence defining the topological space (X, T).
*)


(* dual Normality (DNRM).*)
definition IO1::"'w cl \<Rightarrow> bool" ("DNRM") where "IO1 Int' \<equiv> (Int' \<^bold>\<top>) \<^bold>\<approx> \<^bold>\<top>" 
(* Expansive dual - contractive (CNTR).*)
definition IO2::"'w cl \<Rightarrow> bool" ("CNTR") where "IO2 Int' \<equiv> \<forall>A. Int' A \<^bold>\<preceq> A"
(* Idempotent (IDEM) *)
definition IO3::"'w cl \<Rightarrow> bool" ("IDEM") where "IO3 Int' \<equiv> \<forall>A. (Int' A) \<^bold>\<approx> Int'(Int' A)"
(* Additivity (ADDI) *)
definition IO4::"'w cl \<Rightarrow> bool" ("MULT") where "IO4 Int' \<equiv> \<forall>A B. Int' (A \<^bold>\<and> B) \<^bold>\<approx> (Int' A) \<^bold>\<and> (Int' B)"

definition interior_op :: "'w cl \<Rightarrow> bool"
  where "interior_op  \<equiv> IO1 \<^bold>\<and> IO2 \<^bold>\<and> IO3 \<^bold>\<and> IO4"

lemma assumes "interior_op Int'" shows "open_topo (fp Int')" sorry




section "4 Comprehension and Outlook"

(* ...

The equivalence of the above two axiomatically defined operators on P(X) in specifying any topology T is well known. In addition to the closure or interior operators defining
a topological space, there are other four set operators widely used as primitive operators
in topology.

They are the exterior operator, the boundary operator, the derived-set operator,
and the dually defined co-derived-set operator. All these operators have been shown to be
able to specify an identical topology T —they are equivalent to one another, as with Cl
and Int operators. We call these various inter-related set operators specifying the one
and the same topology a Topological System, while still use (X, T ) to denote it. Each of
the six above-mentioned operators P(X) \<rightarrow> P(X) provides equivalent characterizations
of (X, T ). In a Topological System, the various operators, when taken together, provide
comprehensive topological semantics to ground first-order modal logic.

In parallel to these various axiomatizations of a Topological System, it is also long
established that the topological closure operator can be relaxed to the more general setting
of a Closure System in which the closure operator satisfies, instead of [CO1]–[CO4], three
similar axioms (see below), without enforcing axiom [CO1] (related to “groundedness”)
and axiom [CO4] (related to “stable under union”). The fixed points associated with
this generalized closure operator are called (generalized) closed sets. Viewed in this way, the
closed set system of a Topological System is just a special case of a generalized Closure
System. Other applications of the Closure System include Matroid, Antimatroid/Learning
Space [4–7], or Concept Lattice [8], in which the generalized closure operator is enhanced
with an additional exchange axiom, anti-exchange axiom, or a Galois connection.

...

*)

end
