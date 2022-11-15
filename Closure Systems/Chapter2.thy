theory Chapter2
  imports Chapter1
begin

section "0 Intro"

(*
Topological Systems are specified, equivalently, by either the collection of open sets,
or the collection of closed sets as set systems. In addition to the topological closure and
topological interior operators for characterizing a topology, there are four other operators
commonly used in topology, namely exterior operator, boundary operator, derived-set
operator, and co-derived-set operator. 

Each of these can also be used to completely characterize a Topological System, as shown by the work of [14–17,19]. *)


section "1 Exterior Operator Axioms"

(*
We first discuss the exterior operator in a topological space. 
Given a topological interior operator Int : P(X) \<rightarrow> P(X), 
one can define the so-called topological exterior operator 
related to Int by Ext(A) = Int(A\<^sup>c) where A\<^sup>c \<equiv> X \ A denotes set-complement of
A. 
*)

definition exterior_from_interior :: "'w cl \<Rightarrow> 'w cl" 
  where "exterior_from_interior Int' \<equiv> \<lambda>A. Int' (\<^bold>\<midarrow> A)"

(*
The question of whether one can do the converse, 
namely axiomatically characterize Ext as a primitive operator 
from which Cl and Int operators are derived from, 
was answered affirmatively first by Zarycki [19] 
and then reported by Gabai [14] nearly half a century later. 

In other words, one can specify the Topological System 
by a topological exterior operator Ext axiomatically defined as follows.

Definition 1: (Topological Exterior Operator).
An operator Ext: P(X) \<rightarrow> P(X) is called a topological exterior operator 
if for any sets A, B \<subseteq> X, Ext satisfies the following four axioms:
[EO1] Ext(\<emptyset>) = X;
[EO2] A \<inter> Ext(A) = \<emptyset>;
[EO3] Ext(X \ Ext(A)) = Ext(A);
[EO4] Ext(A \<union> B) = Ext(A) \<inter> Ext(B).
*)


definition EO1::"'w cl \<Rightarrow> bool" where "EO1 Ext \<equiv> (Ext \<^bold>\<bottom>) \<^bold>\<approx> \<^bold>\<top>" 
definition EO2::"'w cl \<Rightarrow> bool" where "EO2 Ext \<equiv> \<forall>A. A \<^bold>\<and> Ext A \<^bold>\<approx> \<^bold>\<bottom>"
definition EO3::"'w cl \<Rightarrow> bool" where "EO3 Ext \<equiv> \<forall>A. Ext(\<^bold>\<midarrow> Ext A) \<^bold>\<approx> (Ext A)"
definition EO4::"'w cl \<Rightarrow> bool" where "EO4 Ext \<equiv> \<forall>A B. Ext(A \<^bold>\<or> B) \<^bold>\<approx> (Ext A) \<^bold>\<and> (Ext B)"

definition exterior_op :: "'w cl \<Rightarrow> bool"
  where "exterior_op \<equiv> EO1 \<^bold>\<and> EO2 \<^bold>\<and> EO3 \<^bold>\<and> EO4"

lemma assumes "interior_op Ext" shows "open_topo (\<lambda> E. Ext (\<^bold>\<midarrow> E) \<^bold>\<approx> E)" sorry

(*
Note that the three topological operators Ext, Int, and Cl 
are related to one another by the following relations:

Int(A) = Ext(A\<^sup>c) \<Leftarrow>\<Rightarrow> Int(A\<^sup>c) = Ext(A) ;
Cl(A) = (Ext(A))\<^sup>c \<Leftarrow>\<Rightarrow> (Cl(A))\<^sup>c = Ext(A) ;
Cl(A) = (Int(A\<^sup>c))\<^sup>c \<Leftarrow>\<Rightarrow> Cl(A\<^sup>c) = (Int(A))\<^sup>c
*)

lemma 
  assumes "interior_cl Int'" and "exterior_cl Ext"
  shows "Int' A \<^bold>\<approx> Ext (\<^bold>\<midarrow> A) \<longleftrightarrow> Int' (\<^bold>\<midarrow> A) \<^bold>\<approx> Ext A" sorry
lemma 
  assumes "exterior_cl Ext" and "closure_cl Cl"
  shows "Cl A \<^bold>\<approx> \<^bold>\<midarrow> (Ext A) \<longleftrightarrow> \<^bold>\<midarrow> (Cl A) \<^bold>\<approx> Ext A" sorry
lemma 
  assumes "interior_cl Int'" and "closure_cl Cl"
  shows "(Cl A \<^bold>\<approx> \<^bold>\<midarrow> (Int' (\<^bold>\<midarrow> A))) \<longleftrightarrow> (Cl (\<^bold>\<midarrow> A) \<^bold>\<approx> \<^bold>\<midarrow> (Int' A))"
  sorry



section "2 Boundary Operator Axioms"


(*
Definition 2: (Topological Boundary Operator).
An operator Fr: P(X) \<rightarrow> P(X) is called 
a topological boundary (or frontier) operator 
if for any sets A, B \<subseteq> X, Fr satisfies the following five axioms:

[FO1] Fr(\<emptyset>) = \<emptyset>;
[FO2] Fr(A) = Fr(A\<^sup>c);
[FO3] A \<subseteq> B \<Rightarrow> Fr(A) \<subseteq> B \<union> Fr(B);
[FO4] Fr(Fr(A)) \<subseteq> Fr(A);
[FO5] Fr(A \<union> B) \<subseteq> Fr(A) \<union> Fr(B).
*)

definition FO1::"'w cl \<Rightarrow> bool" where "FO1 Fr \<equiv> (Fr \<^bold>\<bottom>) \<^bold>\<approx> \<^bold>\<bottom>" 
definition FO2::"'w cl \<Rightarrow> bool" where "FO2 Fr \<equiv> \<forall>A. Fr A \<^bold>\<approx> Fr (\<^bold>\<midarrow> A)"
definition FO3::"'w cl \<Rightarrow> bool" where "FO3 Fr \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> Fr A \<^bold>\<preceq> (B \<^bold>\<or> Fr B)"
definition FO4::"'w cl \<Rightarrow> bool" where "FO4 Fr \<equiv> \<forall>A. Fr(Fr A) \<^bold>\<preceq> (Fr A)"
definition FO5::"'w cl \<Rightarrow> bool" where "FO5 Fr \<equiv> \<forall>A B. Fr (A \<^bold>\<or> B) \<^bold>\<preceq> (Fr A) \<^bold>\<or> (Fr B)"

definition boundary_op :: "'w cl \<Rightarrow> bool"
  where "boundary_op \<equiv> FO1 \<^bold>\<and> FO2 \<^bold>\<and> FO3 \<^bold>\<and> FO4 \<^bold>\<and> FO5"

(*
Note that axiom [FO2] dictates that the boundary Fr(A) of A 
is the same as the boundary Fr(A\<^sup>c) of A\<^sup>c; 
in other words, A and A\<^sup>c \<equiv> X \ A share the “common” boundary points
*)

lemma assumes "boundary_op Fr" shows "Fr A \<^bold>\<approx> Fa (\<^bold>\<midarrow>A)" sorry

(*
With respect to a boundary (also called frontier) operator Fr, 
we can construct T = {E \<in> P(X) | Fr(E\<^sup>c) \<subseteq> E\<^sup>c}. 
The collection T so constructed is a topology. For A \<subseteq> X,
Fr(A) is the boundary of A in the topological space (X, T ). 
Moreover, T is the only topology with the given boundary structure
*)

lemma 
  assumes "boundary_op Fr" 
  shows "closed_topo (\<lambda> E. Fr (\<^bold>\<midarrow>E) \<^bold>\<preceq> (\<^bold>\<midarrow>E))" sorry

(*
We now investigate the role of axiom [FO5], 
the axiom to be removed when relaxing to a generalized Closure System.

Proposition 1:
[FO4] and [FO5] imply
[FO4]\<^sup>* Fr(A \<union> Fr(A)) \<subseteq> Fr(A),
which then implies Fr(A \<union> Fr(A)) \<subseteq> A \<union> Fr(A).
*)
definition FO4'::"'w cl \<Rightarrow> bool" where "FO4' Fr \<equiv> \<forall>A. Fr(A \<^bold>\<or> Fr A) \<^bold>\<preceq> (Fr A)"
definition FO4''::"'w cl \<Rightarrow> bool" where "FO4'' Fr \<equiv> \<forall>A. Fr(A \<^bold>\<or> Fr A) \<^bold>\<preceq> (A \<^bold>\<or> Fr A)"

lemma assumes "(FO4 \<^bold>\<and> FO5) Fr" shows "FO4 Fr" by (metis assms meet_def)
(*
Proof. 
By [FO5], Fr(A \<union> Fr(A)) \<subseteq> Fr(A) \<union> Fr(Fr(A)). 
Because of [FO4], Fr(A) \<union> Fr(Fr(A)) = Fr(A). 
Then Fr(A \<union>Fr(A)) \<subseteq> Fr(A) holds. 
Obviously, Fr(A \<union>Fr(A)) \<subseteq> A \<union>Fr(A) also holds.
*)

(*
If we drop axiom [FO5] in the definition of Fr, we do not have [FO4]\<^sup>*. 
On the other hand, we have the following result.

Proposition 2:
[FO2], [FO3] and [FO4]\<^sup>* implies [FO4]
*)

lemma
  fixes Fr :: "'w cl"
  assumes 1: "FO2 Fr" and 2: "FO3 Fr" and 3: "FO4' Fr"
  shows "FO4 Fr"
  sorry

(*
Proof:

Suppose a set operator Fr only satisfies [FO2] and [FO3] in Definition 10. 
For any A \<subseteq> X, Fr(A) \<subseteq> A \<union> Fr(A). 

An application of [FO3] gives 
Fr(Fr(A)) \<subseteq> A \<union> Fr(A) \<union> Fr(A \<union> Fr(A)) = A \<union> Fr(A), 
where the last step invokes [FO4]\<^sup>*. 
Then Fr(Fr(A)) \<subseteq> A \<union> Fr(A) holds. 
Likewise, for the complement X\<^sup>c \<equiv> X \ A, Fr(Fr(A\<^sup>c)) \<subseteq> A\<^sup>c \<union> Fr(A\<^sup>c) holds. 

By (FO2), we have Fr(Fr(A)) \<subseteq> A \<union> Fr(A) and Fr(Fr(A)) \<subseteq> A\<^sup>c \<union> Fr(A).

Therefore, 
Fr(Fr(A)) \<subseteq> (A \<union> Fr(A)) \<inter> (A\<^sup>c \<union> Fr(A)) 
= (A \<inter> A\<^sup>c) \<union> Fr(A)) = \<emptyset> \<union> Fr(A) = Fr(A), 
i.e., Fr(Fr(A)) \<subseteq> Fr(A).

*)

(*
From the above two Propositions, 
it follows that axiom [FO4] in the axiomatic definition of Fr 
can be equivalently replaced by [FO4]\<^sup>*. 

Then we have an alternative axiomatization of topological boundary operator Fr.

Definition 3: (Topological Boundary Operator, Alternative Definition).

An operator Fr: P(X) \<rightarrow> P(X) is called a topological boundary operator 
if for any sets A, B \<subseteq> X, Fr satisfies the following five axioms:
[FO1] Fr(\<emptyset>) = \<emptyset>;
[FO2] Fr(A) = Fr(A\<^sup>c);
[FO3] A \<subseteq> B \<Rightarrow> Fr(A) \<subseteq> B \<union> Fr(B);
[FO4]\<^sup>* Fr(A \<union> Fr(A)) \<subseteq> Fr(A);
[FO5] Fr(A \<union> B) \<subseteq> Fr(A) \<union> Fr(B).
*)

definition boundary_op' :: "'w cl \<Rightarrow> bool"
  where "boundary_op' \<equiv> FO1 \<^bold>\<and> FO2 \<^bold>\<and> FO3 \<^bold>\<and> FO4' \<^bold>\<and> FO5"

(*
It is possible to further partition Fr(A) into two non-intersecting sets, 
A \<inter> Fr(A) and A\<^sup>c \<inter> Fr(A). See discussions in the first paragraph of Section 2
*)



section "3 Derived-Set Operator Axioms"

(*
We will now turn to the derived-set operator and the co-derived-set operator. Derived
set arises out of studying the limit points (called accumulation points, see Section 4.2.2) of
topologically converging sequences
*)


(*
We follow the scheme by Harvey.

Definition 4: (Topological Derived-Set Operator).

An operator Der: P(X) \<rightarrow> P(X) is called a topological derived-set operator 
if for any sets A, B \<subseteq> X, Der satisfies the following four axioms:

[DO1] Der(\<emptyset>) = \<emptyset>;
[DO2] x \<in> Der(A) \<Leftarrow>\<Rightarrow> x \<in> Der(A \ {x});
[DO3] Der(A \<union> Der(A)) \<subseteq> A \<union> Der(A);
[DO4] Der(A \<union> B) = Der(A) \<union> Der(B).
*)


definition DO1::"'w cl \<Rightarrow> bool" where "DO1 Der \<equiv> (Der \<^bold>\<bottom>) \<^bold>\<approx> \<^bold>\<bottom>" 
definition DO2::"'w cl \<Rightarrow> bool" where "DO2 Der \<equiv> \<forall> A x. Der A x \<longleftrightarrow> Der (A \<^bold>\<leftharpoonup> \<lbrace>x\<rbrace>) x"
definition DO3::"'w cl \<Rightarrow> bool" where "DO3 Der \<equiv> \<forall>A. Der (A \<^bold>\<or> Der A) \<^bold>\<preceq> (A \<^bold>\<or> Der A)"
definition DO4::"'w cl \<Rightarrow> bool" where "DO4 Der \<equiv> \<forall>A B. Der (A \<^bold>\<or> B) \<^bold>\<approx> (Der A \<^bold>\<or> Der B)"

definition derivSet_op :: "'w cl \<Rightarrow> bool" 
  where "derivSet_op \<equiv> DO1 \<^bold>\<and> DO2 \<^bold>\<and> DO3 \<^bold>\<and> DO4"

definition DO3'::"'w cl \<Rightarrow> bool" where "DO3' Der \<equiv> \<forall>A. Der (Der A) \<^bold>\<preceq> (A \<^bold>\<or> Der A)"

(* Proposition 3:

A topological derived-set operator Der has the following property:
[DO3]\<^sup>* Der(Der(A)) \<subseteq> A \<union> Der(A) for any A \<subseteq> X.

Moreover, [DO3]\<^sup>* is equivalent to [DO3] under [DO4]. *)

(*
Proof. First, we show that the topological derived-set operator Der is monotone: for
any A, B \<subseteq> X, A \<subseteq> B implies Der(A) \<subseteq> Der(B). By [DO4] and assuming A \<subseteq> B,
Der(A \<union> B) = Der(B) = Der(A) \<union> Der(B), which implies Der(A) \<subseteq> Der(B).
*)

lemma monotone_derivSet_op:
  fixes Der
  assumes "A \<^bold>\<preceq> B" and "derivSet_op Der"
  shows "Der A \<^bold>\<preceq> Der B" sorry

lemma assumes "derivSet_op Der" shows "D03' Der" sorry

(* continue proof:

For any A \<subseteq> X, Der(A) \<subseteq> A \<union> Der(A) holds. 
By the monotone property of Der and [DO3], 
we have Der(Der(A)) \<subseteq> Der(A \<union> Der(A)) \<subseteq> A \<union> Der(A). 
Then Der(Der(A)) \<subseteq> A \<union> Der(A), so [DO3]\<^sup>* holds.

On the other hand, suppose Der only satisfies [DO4]: 
Der(A \<union> B) = Der(A) \<union> Der(B). 
Then Der(A \<union> Der(A)) = Der(A) \<union> Der(Der(A)). 
By [DO3]\<^sup>*, Der(A \<union> Der(A)) \<subseteq> A \<union> Der(A), i.e., [DO3] holds. 
Therefore, [DO3]\<^sup>* is equivalent to [DO3] under [DO4].
*)

(*
From the above proposition, 
it follows that we can equivalently substitute [DO3]\<^sup>* for [DO3] 
in the definition of Der
*)

(*
Denote [DO2]\<^sup>* x \<notin> Der({x}) for any x \<in> X
*)

definition DO2'::"'w cl \<Rightarrow> bool" where "DO2' Der \<equiv> \<forall> x. \<not> (Der \<lbrace>x\<rbrace>) x"

(* Spira [15] showed that axiom [DO2] is equivalent to [DO2]\<^sup>* 
under axioms [DO1] and [DO4]*)

lemma 
  fixes Der
  assumes "DO1 Der" and "DO4 Der"
  shows "DO2 Der \<longleftrightarrow> DO2' Der" sorry

(*
Therefore, we have an alternative, simpler axiomatic version 
for topological derived-set operator.

Definition 5: (Topological Derived-Set Operator, Alternative Definition).
An operator Der: P(X) \<rightarrow> P(X) is called a topological derived-set operator 
if for any sets A, B \<subseteq> X, Der satisfies the following four axioms:
[DO1] Der(\<emptyset>) = \<emptyset>;
[DO2]\<^sup>* For any x \<in> X, x 6\<in> Der({x});
[DO3]\<^sup>*  Der(Der(A)) \<subseteq> A \<union> Der(A);
[DO4] Der(A \<union> B) = Der(A) \<union> Der(B).
*)

definition der_op :: "'w cl \<Rightarrow> bool" 
  where "der_op \<equiv> DO1 \<^bold>\<and> DO2' \<^bold>\<and> DO3' \<^bold>\<and> DO4"


section "4 Co-Derived-Set Operator"

(*
From a derived-set operator Der, we can dually define an operator Cod 
through complementation: for any A \<subseteq> X, Cod(A) = (Der(A\<^sup>c))\<^sup>c. 
Equivalently, Der(A) =(Cod(A\<^sup>c))\<^sup>c. *)

definition cod_from_der :: "'w cl \<Rightarrow> 'w cl" 
  where "cod_from_der Der \<equiv> \<lambda> A. \<^bold>\<midarrow> Der (\<^bold>\<midarrow> A)"
definition der_from_cod :: "'w cl \<Rightarrow> 'w cl" 
  where "der_from_cod Cod \<equiv> \<lambda> A. \<^bold>\<midarrow> Cod (\<^bold>\<midarrow> A)"


(*
Steinsvold [16] used the co-derived-set operator as the semantics for belief in
his Ph.D. Thesis

Definition 6: (Topological Co-Derived-Set Operator).

An operator Cod: P(X) \<rightarrow> P(X) is called a topological co-derived-set operator 
if for any sets A, B \<subseteq> X, Cod satisfies the following four axioms:
[CD1] Cod (X) = X;
[CD2] x \<in> Cod(A) \<Leftarrow>\<Rightarrow> x \<in> Cod(A \<union> {x});
[CD3] Cod(A \<inter> Cod(A)) \<supseteq> A \<inter> Cod(A);
[CD4] Cod(A \<inter> B) = Cod(A) \<inter> Cod(B).
*)


definition CD1::"'w cl \<Rightarrow> bool" where "CD1 Cod \<equiv> (Cod \<^bold>\<top>) \<^bold>\<approx> \<^bold>\<top>" 
definition CD2::"'w cl \<Rightarrow> bool" where "CD2 Cod \<equiv> \<forall> A x. Cod A x \<longleftrightarrow> Cod (A \<^bold>\<or> \<lbrace>x\<rbrace>) x"
definition CD3::"'w cl \<Rightarrow> bool" where "CD3 Cod \<equiv> \<forall>A. (A \<^bold>\<and> Cod A) \<^bold>\<preceq> Cod (A \<^bold>\<or> Cod A) "
definition CD4::"'w cl \<Rightarrow> bool" where "CD4 Cod \<equiv> \<forall>A B. Cod (A \<^bold>\<and> B) \<^bold>\<approx> (Cod A \<^bold>\<or> Cod B)"

definition cod_od :: "'w cl \<Rightarrow> bool" 
  where "cod_od \<equiv> CD1 \<^bold>\<and> CD2 \<^bold>\<and> CD3 \<^bold>\<and> CD4"


(*
Both derived set and co-derived set can be used to define a topology. 
Any subset A \<subseteq> X is stipulated as being closed when Der(A) \<subseteq> A. 
Then the collection T = {E \<in> P(X) | E\<^sup>c is closed} = {E \<in> P(X) | Der(E\<^sup>c) \<subseteq> E\<^sup>c} 
will specify a Topological System on X, 
with the derived-set operator induced by T being just Der. 
*)

lemma assumes "der_op Der" shows "closed_topo (\<lambda>E . Der (\<^bold>\<midarrow> E) \<^bold>\<preceq> (\<^bold>\<midarrow> E))" sorry

(*
Moreover, T is the only topology satisfying this condition. *)

(*Johannes: ... how to show that?*)


(*
Dually, T' = {E \<in> P(X) | E \<subseteq> Cod(E)} also specifies a Topological System on X. 
The above two topological systems are indeed identical, i.e.,
T = T'. 
*)
lemma assumes "cod_op Cod" shows "closed_topo (\<lambda>E . E \<^bold>\<preceq> (Cod E))" sorry

(*
So, a derived-set operator and its dual co-derived-set operator 
generate the same topology.
*)

lemma assumes "cod_op Cod" and "der_op Der"
  shows "E \<^bold>\<preceq> (Cod E) \<longleftrightarrow> Der (\<^bold>\<midarrow> E) \<^bold>\<preceq> (\<^bold>\<midarrow> E)"
  sorry


section "5 Resumee"

(*
Up till this point, we see that a Topological System can be uniquely specified by any
of the following six operators: Cl,Int, Ext, Fr, Der, Cod. These six operators, with their
respective set of axioms, are rigidly interlocked.
*)


end