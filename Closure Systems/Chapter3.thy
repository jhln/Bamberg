theory Chapter3
  imports Chapter2
begin


(*
In this Section, we first review the relaxation from a topological closure operator
(in a Topological System) to a generalized closure operator (in a Closure System), also
denoted Cl here. We use the terminology Closure System to refer to the set system associated
with this generalized closure operator (and related operators) to be discussed below, and
reserve the terminology Topological System to refer exclusively to the topology (in the usual
sense) character
*)

(*
To study a Closure System, we start with the generalized closure operator. It turns
out that in analogous to the situation of a Topological System, the three axioms for a
generalized closure operator Cl can turn equivalently to an axiom system for a generalized
interior operator Int and an axiom system for a generalized exterior operator Ext. Note
that all operators treated from now on refer to the “generalized” version, despite using the
same bold-face symbols (and sometimes omitting the word “generalized”).
*)


section "1  Generalized Closure, Interior, and Exterior Operators"


(*
We first recall the standard definition of a generalized closure operator.

Definition 7: (Closure Operator).

An operator Cl: P(X) \<rightarrow> P(X) is called a generalized closure operator 
(or simply, closure operator)
if for any sets A, B \<subseteq> X, Cl satisfies the following three axioms:
[C1] A \<subseteq> Cl(A);
[C2] A \<subseteq> B \<Rightarrow> Cl(A) \<subseteq> Cl(B);
[C3] Cl(Cl(A)) = Cl(A)
*)

definition C1 :: "'w cl \<Rightarrow> bool" where "C1 Cl \<equiv> \<forall>A. A \<^bold>\<preceq> Cl A"
definition C2 :: "'w cl \<Rightarrow> bool" where "C2 Cl \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> Cl A \<^bold>\<preceq> Cl B"
definition C3 :: "'w cl \<Rightarrow> bool" where "C3 Cl \<equiv> \<forall>A. Cl(Cl A) \<^bold>\<approx> (Cl A)"

definition general_Cl :: "'w cl \<Rightarrow> bool" 
  where "general_Cl \<equiv> C1 \<^bold>\<and> C2 \<^bold>\<and> C3"

(*
Dually, we also have the axiomatic definition of a generalized interior operator, 
which is also well known.

Definition 8: (Interior Operator).

An operator Int: P(X) \<rightarrow> P(X) is called the generalized interior operator 
(or simply, interior operator) 
if for any sets A, B \<subseteq> X, Int satisfies the following three axioms:
[I1] Int(A) \<subseteq> A;
[I2] A \<subseteq> B \<Rightarrow> Int(A) \<subseteq> Int(B);
[I3] Int(Int(A)) = Int(A).
*)

definition I1 :: "'w cl \<Rightarrow> bool" where "I1 Int' \<equiv> \<forall>A. Int' A \<^bold>\<preceq> A"
definition I2 :: "'w cl \<Rightarrow> bool" where "I2 Int' \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> Int' A \<^bold>\<preceq> Int' B"
definition I3 :: "'w cl \<Rightarrow> bool" where "I3 Int' \<equiv> \<forall>A. Int'(Int' A) \<^bold>\<approx> (Int' A)"

definition general_Int' :: "'w cl \<Rightarrow> bool" 
  where "general_Int' \<equiv> I1 \<^bold>\<and> I2 \<^bold>\<and> I3"

(*
The interior operator Int is dual to the closure operator Cl, 
in the sense that for any A \<subset> X, Int(A) = (Cl(A\<^sup>c))\<^sup>c and Cl(A) = (Int(A\<^sup>c))\<^sup>c.
*)

lemma fixes Cl 
  assumes "general_Cl Cl" shows "general_Int' (\<lambda> A. \<^bold>\<midarrow> Cl (\<^bold>\<midarrow> A))" sorry

lemma fixes Int' 
  assumes "general_Int' Int'" shows "general_Cl (\<lambda> A . \<^bold>\<midarrow> Int' (\<^bold>\<midarrow> A))" sorry



(*
In light of the identity between an exterior operator 
and an interior operator operating on any subset A of X: Int(A) \<equiv> Ext(A\<^sup>c), 
the axiomatic definition of a generalized exterior operator is obtained 
(in analogous to how the topological exterior operator is defined
in relation to the definitions of topological closure 
and topological interior operators) as follows.
*)


(*
Definition 9: (Exterior Operator).

An operator Ext: P(X) \<rightarrow> P(X) is called a generalized exterior operator 
(or simply, exterior operator) 
if for any sets A, B \<subseteq> X, Ext satisfies the following three axioms:
[E1] A \<inter> Ext(A) = \<emptyset>;
[E2] A \<subseteq> B \<Rightarrow> Ext(A) \<supseteq> Ext(B);
[E3] Ext(X \ Ext(A)) = Ext(A).
*)

definition E1 :: "'w cl \<Rightarrow> bool" where "E1 Ext \<equiv> \<forall>A. A \<^bold>\<and> Ext A \<^bold>\<approx> \<^bold>\<bottom>"
definition E2 :: "'w cl \<Rightarrow> bool" where "E2 Ext \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> Ext A \<^bold>\<succeq> Ext B"
definition E3 :: "'w cl \<Rightarrow> bool" where "E3 Ext \<equiv> \<forall>A. Ext(\<^bold>\<midarrow> (Ext A)) \<^bold>\<approx> (Ext A)"

definition general_Ext :: "'w cl \<Rightarrow> bool" 
  where "general_Ext \<equiv> E1 \<^bold>\<and> E2 \<^bold>\<and> E3"


section "2 Generalized Boundary Operator"

(*
We now turn to generalized boundary (or frontier) operator. 
A careful comparison of how a topological closure operator can be relaxed 
to become a generalized closure operator, 
we see that [FO1] and [FO5] in the definition of topological boundary operator
can be dropped to obtain a generalized boundary operator. 
[FO2] expresses the essence of “boundary” (or “frontier”) of a closed set. 
[FO3] shows Fr is “monotone” in some sense.
[FO4]\<^sup>* corresponds to the “idempotency” of the closure operator. 
Therefore, we only retain [FO2], [FO3] and [FO4]\<^sup>* to obtain the definition 
of generalized boundary operator.
*)


(*
Definition 10: (Boundary Operator).

An operator Fr: P(X) \<rightarrow> P(X) is called a generalized boundary operator 
(or simply, boundary operator) 
if for any sets A, B \<subseteq> X, Fr satisfies the following three axioms:
[F1] Fr(A) = Fr(X \ A);
[F2] A \<subseteq> B \<Rightarrow> Fr(A) \<subseteq> B \<union> Fr(B);
[F3] Fr(A \<union> Fr(A)) \<subseteq> Fr(A).
*)

definition F1 :: "'w cl \<Rightarrow> bool" where "F1 Fr \<equiv> \<forall>A. Fr A \<^bold>\<approx> Fr (\<^bold>\<midarrow> A)"
definition F2 :: "'w cl \<Rightarrow> bool" where "F2 Fr \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> Fr A \<^bold>\<preceq> B \<^bold>\<or> Fr B"
definition F3 :: "'w cl \<Rightarrow> bool" where "F3 Fr \<equiv> \<forall>A. Fr(A \<^bold>\<or> (Fr A)) \<^bold>\<preceq> (Fr A)"

definition general_Fr :: "'w cl \<Rightarrow> bool"
  where "general_Fr \<equiv> F1 \<^bold>\<and> F2 \<^bold>\<and> F3"


(*
Proposition 4.
The boundary operator Fr has the following property:
[F3]\<^sup>* Fr(Fr(A)) \<subseteq> Fr(A) for any A \<subseteq> X.
*)
definition F3' :: "'w cl \<Rightarrow> bool" where "F3' Fr \<equiv> \<forall>A. Fr(Fr A) \<^bold>\<preceq> (Fr A)"

lemma fixes Fr assumes "general_Fr Fr" shows "F3' Fr" sorry

(*Proof. See the proof of Proposition 2*)


(*
As we recall, [F3]\<^sup>* as stated above is axiom [FO4] 
in the topological boundary operator.
However, [F3]\<^sup>* cannot be an alternative axiom 
in the definition of generalized boundary operator. 
In fact, [F3]\<^sup>* is strictly weaker than [F3] under [F1] and [F2]. 
It can be seen from the following example.
Example 1. Let X = {1, 2, 3}. ...
*)


(*
Boundary operators and closure operators have a one-to-one correspondence in Topological Systems. Likewise, for their generalizations in Closure Systems, we expect such
correspondence to still hold.
*)

(*
Theorem 1: (From Fr to Cl).
Let Fr: P(X) \<rightarrow> P(X) be a boundary operator. 
Define the operator Cl as Cl(A) =: A \<union> Fr(A) for any subset A of X. 
Then Cl as defined is a (generalized) closure operator.
*)

definition cl_from_fr :: "'w cl \<Rightarrow> 'w cl" 
  where "cl_from_fr Fr \<equiv> \<lambda>A. A \<^bold>\<or> Fr A"

lemma 
  fixes Fr :: "'w cl" 
  assumes "general_Fr Fr"
  shows "general_Cl (cl_from_fr Fr)"
  sorry

(*
Proof: 

To prove [C1], for any subset A of X, we have A \<subseteq> A \<union> Fr(A) = Cl(A), 
where the last step is by our definition of the operator Cl. 
Therefore, A \<subseteq> Cl(A).

To prove [C2], given A \<subseteq> B \<subseteq> X, axiom [F2] gives Fr(A) \<subseteq> B \<union> Fr(B). 
Therefore, we have A \<union> Fr(A) \<subseteq> B \<union> Fr(B). 
This, by the definition of Cl, is nothing but Cl(A) \<subseteq> Cl(B).

To prove [C3], applying the definition of Cl twice, 
we have Cl(Cl(A))=Cl(A \<union> Fr(A))= A \<union> Fr(A) \<union> Fr(A \<union> Fr(A)). 
By axiom [F3], then Cl(A \<union> Fr(A)) = A \<union> Fr(A) = Cl(A), 
that is, Cl(Cl(A)) = Cl(A) holds.
*)

(*Conversely, we also can obtain a boundary operator from a closure operator.*)

(*
Theorem 2. (From Cl to Fr).
Let Cl: P(X) \<rightarrow> P(X) be a closure operator. 
Define Fr(A) := Cl(A) \<inter> Cl(A\<^sup>c) for any subset A of X. 
Then Fr as defined is a (generalized) boundary operator.
*)

definition fr_from_cl :: "'w cl \<Rightarrow> 'w cl" 
  where "fr_from_cl Cl \<equiv> \<lambda>A. Cl A \<^bold>\<and> Cl (\<^bold>\<midarrow> A)"

lemma 
  fixes Cl :: "'w cl" 
  assumes "general_Cl Cl"
  shows "general_Fr (fr_from_cl Cl)"
  sorry

(*
Proof. 

To prove [F1], from the definition of Fr, 
Fr(A\<^sup>c) = Cl(A\<^sup>c) \<inter> Cl((A\<^sup>c)\<^sup>c) = Cl(A\<^sup>c) \<inter> Cl(A) = Fr(A).

To prove [F2], first by axiom [C1], A \<subseteq> Cl(A). 
Again, by axiom [C1], A \<union> Cl(A\<^sup>c) \<supseteq> A \<union> A\<^sup>c = X, so A \<union> Cl(A\<^sup>c) = X. 
Therefore, apply the definition of Fr, 
A \<union> Fr(A) = A \<union> (Cl(A) \<inter> Cl(A\<^sup>c)) = (A \<union> Cl(A)) \<inter> (A \<union> Cl(A\<^sup>c)) 
= Cl(A) \<inter> X = Cl(A). 
By axiom [C2], for any subsets A, B \<subseteq> X with A \<subseteq> B, Cl(A) \<subseteq> Cl(B), 
i.e., Fr as defined satisfies [F2].

To prove [F3], from the above proof of [F2], 
it follows that A \<union> Fr(A) = Cl(A) for any A \<subseteq> X. 
We only need to check Fr(Cl(A)) \<subseteq> Fr(A). 
Again, by the definition of Fr, Fr(Cl(A)) = Cl(Cl(A)) \<inter> Cl((Cl(A))\<^sup>c). 
The first term on the right-hand side, by axiom [C3], 
becomes Cl(Cl(A)) = Cl(A). 
To deal with the second term, Cl((Cl(A))\<^sup>c),
by axiom [C1] we have A \<subseteq> Cl(A), which implies (Cl(A))\<^sup>c \<subseteq> A\<^sup>c; 
then apply axiom [C2], Cl((Cl(A))\<^sup>c) \<subseteq> Cl(A\<^sup>c). 
Therefore, Fr(Cl(A)) = Cl(Cl(A)) \<inter> Cl((Cl(A))\<^sup>c) \<subseteq> Cl(A) \<inter> Cl(A\<^sup>c) = Fr(A).
*)

(*
In the proof of Theorem 1, we have not used [F1] in the definition of generalized
boundary operator. So, we can further weaken the notion of generalized boundary set
operator as follows.
*)

(*
Definition 11: (Pre-Boundary Operator Pb).

An operator on P(X) is called a Pre-Boundary Operator, denoted Pb, 
if Pb satisfies the following two conditions:

[Pb1] A \<subseteq> B \<Rightarrow> Pb(A) \<subseteq> B \<union> Pb(B);
[Pb2] Pb(A \<union> Pb(A)) \<subseteq> Pb(A).
*)

definition Pb1 :: "'w cl \<Rightarrow> bool" where "Pb1 Pb \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> Pb A \<^bold>\<preceq> B \<^bold>\<or> Pb B"
definition Pb2 :: "'w cl \<Rightarrow> bool" where "Pb2 Pb \<equiv> \<forall>A. Pb(A \<^bold>\<or> (Pb A)) \<^bold>\<preceq> (Pb A)"

definition general_Pb :: "'w cl \<Rightarrow> bool"
  where "general_Pb \<equiv> Pb1 \<^bold>\<and> Pb2"

(*
Theorem 3:

Let Pb be a pre-boundary operator.

1. Define Cl as Cl(A) =: A \<union> Pb(A) for any subset A of X.
Then Cl is a (generalized) closure operator.

2. Define Fr(A) =: Cl(A) \<inter> Cl(A\<^sup>c) as the (generalized) boundary operator 
associated with Cl. Then the following two statements are equivalent:
  (i) For any subset A \<subseteq> X, Pb(A) = Pb(A\<^sup>c);
  (ii) For any subset A \<subseteq> X, Pb(A) = Fr(A).
*)

definition cl_from_pb :: "'w cl \<Rightarrow> 'w cl" 
  where "cl_from_pb Pb \<equiv> \<lambda>A. A \<^bold>\<or> Pb A"

lemma 
  fixes Pb :: "'w cl" 
  assumes "general_Pb Pb" 
  shows "general_Cl (cl_from_pb Pb)"
  sorry

lemma 
  fixes Pb :: "'w cl" 
  assumes "general_Pb Pb"
  shows "\<forall> A. Pb A \<^bold>\<approx> Pb (\<^bold>\<midarrow> A) \<longleftrightarrow> 
              Pb A \<^bold>\<approx> (fr_from_cl (cl_from_pb Pb)) (\<^bold>\<midarrow> A)"
  sorry


(*
Proof. 

For Statement 1:
Follow the proof of Theorem 1. 

We now prove Statement 2:
From (i) to (ii). 

By the construction of Fr, 
for any subset A \<subseteq> X, 
Fr(A) = Cl(A) \<inter> Cl(A\<^sup>c) = (A \<union> Pb(A)) \<inter> (A\<^sup>c \<union> Pb(A\<^sup>c))
= (A \<inter> A\<^sup>c) \<union> (A \<inter> Pb (A\<^sup>c)) \<union> (A\<^sup>c \<inter> Pb(A)) \<union> (Pb(A) \<inter> Pb(A\<^sup>c)) 
= (A \<inter> Pb (A\<^sup>c)) \<union> (A\<^sup>c \<inter> Pb(A)) \<union> (Pb(A) \<inter> Pb(A\<^sup>c)). 

By (i), 
for any subset A \<subseteq> X, Pb(A) = Pb(A\<^sup>c), 
then Fr(A) = (A \<inter> Pb (A)) \<union> (A\<^sup>c \<inter> Pb(A)) \<union> (Pb(A) \<inter> Pb(A)) 
= (A \<inter> Pb (A)) \<union> (A\<^sup>c \<inter> Pb(A)) \<union> Pb(A) 
= Pb(A), i.e., 
(i) implies (ii).

From (ii) to (i). 
This is through the definition of Fr, 
with axiom (F1) stating that Fr(A) = Fr(A\<^sup>c). 
Given (ii) which states Pb = Fr, 
then (i) is obvious by the definition of Fr(A).
*)

(*
From the above theorem, we can see 
that in the axiomatic definition of a boundary operator, 
axiom [F1], Fr(A) = Fr(A\<^sup>c), is indispensable, 
which guarantees the one-to-one correspondence between boundary operators 
and closure operators.
*)


section "3 Generalized Derived-Set Operator"

(*
In this section, we consider the generalized derived-set operator. 
Compared with how one obtains the generalized closure operator 
from the topological closure operator,
axiom [DO1] of the topological derived-set operator should be omitted 
and [DO5] should be weakened to just being monotone. 

From Proposition 2 and its proof, we expect to retain axiom [DO3]. 
Axiom [DO2] will also be retained, since it shows the essence 
of the notion of a derived set. 

Combining the above considerations, we have the following definition of
generalized derived-set operator.

Definition 12: (Derived-Set Operator Der).

An operator Der: P(X) \<rightarrow> P(X) is called a generalized derived-set operator 
(or simply, derived-set operator) 
if for any sets A, B \<subseteq> X, Der satisfies the following three axioms:

[D1] x \<in> Der(A) \<Leftarrow>\<Rightarrow> x \<in> Der(A \ {x});
[D2] A \<subseteq> B \<Rightarrow> Der(A) \<subseteq> Der(B);
[D3] Der(A \<union> Der(A)) \<subseteq> A \<union> Der(A).
*)

definition D1 :: "'w cl \<Rightarrow> bool" where "D1 Der \<equiv> \<forall>A x. Der A x \<longleftrightarrow> Der (A \<^bold>\<leftharpoonup> \<lbrace>x\<rbrace>) x"
definition D2 :: "'w cl \<Rightarrow> bool" where "D2 Der \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> Der A \<^bold>\<preceq> Der B"
definition D3 :: "'w cl \<Rightarrow> bool" where "D3 Der \<equiv> \<forall>A. Der(A \<^bold>\<or> (Der A)) \<^bold>\<preceq> (A \<^bold>\<or> Der A)"

definition general_Der :: "'w cl \<Rightarrow> bool"
  where "general_Der \<equiv> D1 \<^bold>\<and> D2 \<^bold>\<and> D3"

(*
Proposition 5:
A derived-set operator Der satisfies 
[D3]\<^sup>* Der(Der(A)) \<subseteq> A \<union> Der(A), for any A \<subseteq> X.
*)

definition D3' :: "'w cl \<Rightarrow> bool" where "D3' Der \<equiv> \<forall>A. Der(Der A) \<^bold>\<preceq> (A \<^bold>\<or> Der A)"

lemma 
  fixes Der 
  assumes "general_Der Der" 
  shows "D3' Der" 
  sorry
(*  by (smt (z3) D2_def D3'_def D3_def assms general_Der_def join_def meet_def subset_def) *)


(*
Proof. See proof of Proposition 3.
*)

(*
In the case of topological derived-set operator, 
property [DO3] and [DO3]\<^sup>* are substitutable. 
However, their equivalence does not hold in the situation of a generalized
derived-set operator. 

In fact, [D3]\<^sup>* is strictly weaker than [D3] in the case of generalized
derived-set operator. The following example can illustrate this ....
*)

(*
Derived-set operators and closure operators have a one-to-one correspondence in
Topological Systems. Likewise, for their generalizations in Closure Systems, we expect
such correspondence to still hold.
*)

(*
Theorem 4: (From Der to Cl).
Let Der: P(X) \<rightarrow> P(X) be a derived-set operator. 
Define Cl as Cl(A) =: A \<union> Der(A) for any subset A of X. 
Then Cl as defined is a closure operator.
*)

definition cl_from_der :: "'w cl \<Rightarrow> 'w cl"
  where "cl_from_der Der \<equiv> \<lambda> A . A \<^bold>\<or> Der A"

lemma 
  fixes Der
  assumes "general_Der Der" 
  shows "general_Cl (cl_from_der Der)"
  sorry

(*
Proof. 

To prove [C1], since A \<subseteq> A \<union> Der(A) for any subset A of X, 
we apply the definition of the operator Cl, Cl(A) = A \<union> Der(A), 
and obtain A \<subseteq> Cl(A).

To prove [C2], suppose A \<subseteq> B \<subseteq> X. 
By [D2], Der(A) \<subseteq> Der(B). Therefore A \<union> Der(A) \<subseteq> B \<union> Der(B). 
According to our definition, this is Cl(A) \<subseteq> Cl(B).

To prove [C3], apply the definition of Cl twice, 
we have Cl(Cl(A))=Cl(A \<union> Der(A))= A \<union> Der(A) \<union> Der(A \<union> Der(A)). 
By [D3], then Cl(A \<union> Der(A)) = A \<union> Der(A) = Cl(A), that is, 
the law of idempotency Cl(Cl(A)) = Cl(A) holds.
*)

(*
Conversely, we also can obtain a derived-set operator from a closure operator.
*)

(*
Theorem 5: (From Cl to Der).
Let Cl: P(X) \<rightarrow> P(X) be a closure operator. 
Define Der(A) := {x \<in> X | x \<in> Cl(A \ {x})} for any subset A of X. 
Then Der as defined is a derived-set operator
*)

definition der_from_cl :: "'w cl \<Rightarrow> 'w cl"
  where "der_from_cl Cl \<equiv> \<lambda> A . (\<lambda> x. Cl (A \<^bold>\<leftharpoonup> \<lbrace>x\<rbrace>) x)"

lemma 
  fixes Cl 
  assumes "general_Cl Cl" 
  shows "general_Der (der_from_cl Cl)"
  sorry


(*
Proof. 

To prove [D1], 
assume that x \<in> Der(A), 
then by the definition of Der, 
it follows x \<in> Cl(A \ {x}). 
Since A \ {x} = (A \ {x}) \ {x}, 
we have x \<in> Cl(A \ {x}) = Cl((A \ {x}) \ {x}). 
Again, by the definition of Der, x \<in> Der(A \ {x}) holds. 
Every step in the above can be reversed. 
Therefore, x \<in> Der(A) \<Leftarrow>\<Rightarrow> x \<in> Der(A \ {x}) holds.

To prove [D2], 
given that any subsets A, B \<subseteq> X, A \<subseteq> B, we have A \ {x} \<subseteq> B \ {x}.
For any x \<in> Der(A), apply the definition of Der, we have x \<in> Cl(A \ {x}). 
By [C2], we have x \<in> Cl(A \ {x}) \<subseteq> Cl(B \ {x}). 
Again, by the definition of Der, x \<in> Der(B).
Therefore, Der(A) \<subseteq> Der(B) holds.

To prove [D3], 
let us first show A \<union> Der(A) = Cl(A) for any A \<subseteq> X. 
For any x \<in> Der(A), we have x \<in> Cl(A \ {x}) by the definition of Der. 
Since Cl(A \ {x}) \<subseteq> Cl(A) by [C2], then x \<in> Cl(A). 
So Der(A) \<subseteq> Cl(A). 
Together with [C1], A \<union> Der(A) \<subseteq> Cl(A) holds. 
On the other hand, 
for every x \<in> Cl(A), assume that x 6\<in> A, 
then A = A \ {x}.
So x \<in> Cl(A) = Cl(A \ {x}), 
namely again by the definition of Der, x \<in> Der(A), 
so Cl(A) \<subseteq> A \<union> Der(A). 
Therefore, A \<union> Der(A) = Cl(A). 
Because of this Der(A) \<subseteq> Cl(A). 
So Der(A \<union> Der(A)) =Der(Cl(A)) \<subseteq> Cl(Cl(A)) = Cl(A), by [C3]. 
Therefore, Der(A \<union> Der(A)) \<subseteq> Cl(A) = A \<union> Der(A), which is [D3].
*)


(*
In the proof of Theorem 4, we have not used [D1] 
in the definition of generalized derived-set operator Der. 
A further weakening of the generalized derived-set operator can be obtained.
*)

(*
Definition 13: (Pre-Derived-Set Operator Pd).

An operator on P(X) is called a pre-derived-set operator, denoted Pd, 
if Pd satisfies the following conditions:

[Pd1] A \<subseteq> B \<Rightarrow> Pd(A) \<subseteq> Pd(B);
[Pd2] Pd(A \<union> Pd(A)) \<subseteq> A \<union> Pd(A).
*)

definition Pd1 :: "'w cl \<Rightarrow> bool" where "Pd1 Pd \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> Pd A \<^bold>\<preceq> Pd B"
definition Pd2 :: "'w cl \<Rightarrow> bool" where "Pd2 Pd \<equiv> \<forall>A. Pd(A \<^bold>\<or> (Pd A)) \<^bold>\<preceq> (A \<^bold>\<or> Pd A)"

definition general_Pd :: "'w cl \<Rightarrow> bool"
  where "general_Pd \<equiv> Pd1 \<^bold>\<and> Pd2"

(*
Theorem 6:

Let Pd be a pre-derived-set operator.

1. Define the operator Cl by Cl(A) =: A \<union> Pd(A) for any subset A of X. 
Then Cl is a (generalized) closure operator.

2. Define the operartor Der by Der(A) = {x \<in> X | x \<in> Cl(A \ {x})}. 
Then the following two statements are equivalent:
  (i) For any subset A \<subseteq> X, x \<in> Pd(A) \<Leftarrow>\<Rightarrow> x \<in> Pd(A \ {x});
  (ii) For any subset A \<subseteq> X, Pd(A) = Der(A).
*)

definition cl_from_pd :: "'w cl \<Rightarrow> 'w cl" 
  where "cl_from_pd Pd \<equiv> \<lambda>A. A \<^bold>\<or> Pd A"

lemma 
  fixes Pd :: "'w cl" 
  assumes "general_Pd Pd"
  shows "general_Cl (cl_from_pd Pd)"
  sorry

lemma 
  fixes Pd :: "'w cl" 
  assumes "general_Pd Pd"
  shows "\<forall> A x. (Pd A x \<longleftrightarrow> Pd (A \<^bold>\<leftharpoonup> \<lbrace>x\<rbrace>) x) \<longleftrightarrow> 
                (Pd A \<^bold>\<approx> (der_from_cl (cl_from_pd Pb)) A)"
  sorry

(*
Proof. 

For Statement 1: 
see the proof of Theorem 4. 

So, we now prove Statement 2:

From (i) to (ii).
Assume that (i) holds, 
namely for any subset A \<subseteq> X, x \<in> Pd(A) \<Leftarrow>\<Rightarrow> x \<in> Pd(A \ {x}). 
By the definitions of Cl and Der, 
for any x \<in> Der(A), then x \<in> Cl(A \ {x}) = (A \ {x}) \<union> Pd(A \ {x}), 
which implies x \<in> Pd(A \ {x}). 
By the given condition (i), 
we have x \<in> Pd(A), then Der(A) \<subseteq> Pd(A). 
Similarly, for the other direction,
for any x \<in> Pd(A), by the given condition (i), 
x \<in> Pd(A \ {x}), so x \<in> Cl(A \ {x}) by the definition of Cl. 
Again, by the definition of Der, x \<in> Der(A). 
Therefore, Pd(A) \<subseteq> Der(A).
That is to say, (ii) holds.

From (ii) to (i). 
If (ii) holds, Pd is a generalized derived-set operator. 
Then Pd satisfies (i). 
So, the proof is completed.
*)



section "4 Generalized Co-Derived-Set Operator"

(*
Dual to a generalized derived-set operator, 
we can define a generalized co-derivedset operator.
*)

(*
Definition 14. (Co-Derived-Set Operator Cod).

A generalized co-derived-set operator 
(or simply, co-derived-set operator), denoted Cod, 
is defined as an operator on P(X) which satisfies:

[A1] x \<in> Cod(A) \<Leftarrow>\<Rightarrow> x \<in> Cod(A \<union> {x});
[A2] A \<subseteq> B \<Rightarrow> Cod(A) \<subseteq> Cod(B);
[A3] Cod(A \<inter> Cod(A)) \<supseteq> A \<inter> Cod(A).
*)

definition A1 :: "'w cl \<Rightarrow> bool" where "A1 Cod \<equiv> \<forall>A x. Cod A x \<longleftrightarrow> Cod (A \<^bold>\<or> \<lbrace>x\<rbrace>) x"
definition A2 :: "'w cl \<Rightarrow> bool" where "A2 Cod \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> Cod A \<^bold>\<preceq> Cod B"
definition A3 :: "'w cl \<Rightarrow> bool" where "A3 Cod \<equiv> \<forall>A. Cod(A \<^bold>\<and> (Cod A)) \<^bold>\<succeq> (A \<^bold>\<and> Cod A)"

definition general_Cod :: "'w cl \<Rightarrow> bool"
  where "general_Cod \<equiv> A1 \<^bold>\<and> A2 \<^bold>\<and> A3"


(*
That the derived-set operator Der is dual to the co-derived-set operator Cod 
is reflected in Cod(A) = (Der(A\<^sup>c))\<^sup>c and Der(A) = (Cod(A\<^sup>c))\<^sup>c.*)

lemma assumes "general_Der Der" shows "general_Cod (\<lambda> A. \<^bold>\<midarrow> Der (\<^bold>\<midarrow> A))" sorry
lemma assumes "general_Cod Cod" shows "general_Der (\<lambda> A. \<^bold>\<midarrow> Cod (\<^bold>\<midarrow> A))" sorry

(*
Combining the duality of derived-set operator and the co-derived-set operator with
the duality of the closure operator and the interior operator, we have the following results
(proof omitted) complementary to previous theorems for derived-set operators.
*)

(*
Theorem 7. (From Cod to Int).
Let Cod: P(X) \<rightarrow> P(X) be a co-derived-set operator. 
Define Int(A) =: A \<inter> Cod(A) for any subset A of X. 
Then Int as defined is an interior operator.
*)

definition int_from_cod :: "'w cl \<Rightarrow> 'w cl" 
  where "int_from_cod Cod \<equiv> \<lambda>A. A \<^bold>\<and> Cod A"

lemma 
  fixes Cod :: "'w cl" 
  assumes "general_Cod Cod"
  shows "general_Int' (int_from_cod Cod)"
  sorry

(*
Theorem 8. (From Int to Cod).
Let Int: P(X) \<rightarrow> P(X) be an interior operator. 
Define Cod(A) := {x \<in> X | x \<in> Int(A \<union> {x})} for any subset A of X. 
Then Cod as defined is a co-derived-set operator
*)

definition cod_from_int :: "'w cl \<Rightarrow> 'w cl"
  where "cod_from_int Int' \<equiv> \<lambda> A . (\<lambda> x. Int' (A \<^bold>\<or> \<lbrace>x\<rbrace>) x)"

lemma 
  fixes Int' :: "'w cl" 
  assumes "general_Int' Cod"
  shows "general_Cod (cod_from_int Int')"
  sorry


(*
Definition 15. (Pre-Co-Derived-Set Operator Pcd).
An operator on P(X) is called a pre-co-derived-set operator, denoted Pcd, 
if it satisfies the following conditions:

[Pcd1] A \<subseteq> B \<Rightarrow> Pcd(A) \<subseteq> Pcd(B);
[Pcd2] Pcd(A \<union> Pcd(A)) \<supseteq> A \<union> Pcd(A).
*)

definition Pcd1 :: "'w cl \<Rightarrow> bool" where "Pcd1 Pcd \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> Pcd A \<^bold>\<preceq> Pcd B"
definition Pcd2 :: "'w cl \<Rightarrow> bool" where "Pcd2 Pcd \<equiv> \<forall>A. Pcd(A \<^bold>\<or> (Pcd A)) \<^bold>\<succeq> (A \<^bold>\<or> Pcd A)"

definition general_Pcd :: "'w cl \<Rightarrow> bool"
  where "general_Pcd \<equiv> Pcd1 \<^bold>\<and> Pcd2"

(*
Theorem 9.

Let Pcd be a pre-co-derived-set operator. 
For any subset A \<subseteq> X, denote Int as the interior operator generated by Pcd: 
Int(A) =: A \<inter> Pcd(A), 
and Cod as the resulting co-derived-set operator:
Cod(A) = {x \<in> X | x \<in> Int(A \<union> {x})}. 

Then the following two statements are equivalent:
(i) For any subset A \<subseteq> X, x \<in> Pcd(A) \<Leftarrow>\<Rightarrow> x \<in> Pcd(A \<union> {x});
(ii) For any subset A \<subseteq> X, Pcd(A) = Cod(A).
*)


definition int_from_pcd :: "'w cl \<Rightarrow> 'w cl"
  where "int_from_pcd Pcd \<equiv> \<lambda> A . A \<^bold>\<and> Pcd A"

lemma 
  fixes Pcd :: "'w cl" 
  assumes "general_Pcd Pcd"
  shows "\<forall> A x. (Pcd A x \<longleftrightarrow> Pcd (A \<^bold>\<or> \<lbrace>x\<rbrace>) x) \<longleftrightarrow> 
                (Pcd A \<^bold>\<approx> (cod_from_int (int_from_pcd Pcb)) A)"
  sorry


section "5 Relations between Various Characterizations"

(*
Following the formulation of generalized closure operator Cl and generalized interior
operator Int, we have, in the previous subsections, proposed axiomatic systems for four
related generalized set operators: generalized exterior operator Ext, generalized boundary
operator Fr, generalized derived-set operator Der, and generalized co-derived-set operator
Cod. The prefix “generalized” can be omitted if the context clearly refers to the “generalized” Closure System. These six operators provide a complete generalization (for the case
of Closure System) of the suite of six corresponding operators encountered in topology
(in the Topological System). The generalized operators we obtained, Fr, Der, Cod, are
in one-to-one correspondence to the operator Cl and the immediately related operators
Int, Ext. Given any operator, the remaining five operators can be specified. The results are
summarized in the following figure (Figure 1).

...

1. Int(A) = Ext(A\<^sup>c), 
1\<^sup>*. Ext(A) = Int(A\<^sup>c).
2. Cod(A) = {x \<in> X | x \<in> Int(A \<union> {x})}, 
2\<^sup>*. Int(A) = A \<inter> Cod(A).
3. Cl(A) = (Ext(A))\<^sup>c, 
3\<^sup>*. Ext(A) = (Cl(A))\<^sup>c.
4. Cl(A) = (Int(A\<^sup>c))\<^sup>c, 
4\<^sup>*. Int(A) = (Cl(A\<^sup>c))\<^sup>c.
5. Der(A) = (Cod(A\<^sup>c))\<^sup>c, 
5\<^sup>*. Cod(A) = (Der(A\<^sup>c))\<^sup>c.
6. Cl(A) = A \<union> Fr(A), 
6\<^sup>*. Fr(A) = Cl(A) \<inter> Cl(A\<^sup>c).
7. Der(A) := {x \<in> X | x \<in> Cl(A \ {x})}, 
7\<^sup>*. Cl(A) = A \<union> Der(A).
8. Cl(A) = A \<union> Pb(A).
9. Cl(A) = A \<union> Pd(A).
*)



section "6 Closure/Interior Operators from Galois Connection"

(*
In this subsection, 
we make the observation that closure/interior operators may arise naturally 
from Galois connection, namely a pair of monotone maps between two sets. 
This construction of closure/interior operators provides a completely 
dualistic view of a closure system as composition of two half-systems.
*)

(*
Let X,Y be sets, 
Pow(X),Pow(Y) be their corresponding power sets, 
and  s : P(X) \<rightarrow> P(Y) and t : P(Y) \<rightarrow> P(X) be a pair of functions

In addition, we recall
• s is said to be monotone if 
whenever U1 \<subseteq> U2 \<subseteq> X, we have s(U1) \<subseteq> s(U2) \<subseteq> Y ;
• t is said to be monotone if 
whenever V1 \<subseteq> V2 \<subseteq> Y, we have t(V1) \<subseteq> t(V2) \<subseteq> X
*)

(**Monotonicity (MONO).*)
definition MONO::"(('x \<Rightarrow> bool) \<Rightarrow> ('y \<Rightarrow> bool)) \<Rightarrow> bool" ("MONO")
  where "MONO \<phi> \<equiv> \<forall>A B. A \<^bold>\<preceq> B \<longrightarrow> \<phi> A \<^bold>\<preceq> \<phi> B"

(*
Definition 16. The pair of functions (s, t) is called
(i) an antitone Galois connection if: V \<subseteq> s(U) if and only if U \<subseteq> t(V);
(ii) a monotone Galois connection if: s(U) \<subseteq> V if and only if U \<subseteq> t(V);
(iii) a Lagois connection [20] if: s(U) \<subseteq> V if and only if t(V) \<subseteq> U.
for each U \<in> P(X) and V \<in> P(Y).
*)

type_synonym ('x,'y) op = "('x \<Rightarrow> bool) \<Rightarrow> ('y \<Rightarrow> bool)"

definition antitone_gal :: "('x,'y) op \<Rightarrow> ('y,'x) op \<Rightarrow> bool"
  where "antitone_gal s t \<equiv> \<forall> V U. V \<^bold>\<preceq> s U \<longleftrightarrow> U \<^bold>\<preceq> t V"
definition monotone_gal :: "('x,'y) op \<Rightarrow> ('y,'x) op \<Rightarrow> bool"
  where "monotone_gal s t \<equiv> \<forall> V U. s U \<^bold>\<preceq> V \<longleftrightarrow> U \<^bold>\<preceq> t V"
definition lagois_conn :: "('x,'y) op \<Rightarrow> ('y,'x) op \<Rightarrow> bool"
  where "lagois_conn s t \<equiv> \<forall> V U. s U \<^bold>\<preceq> V \<longleftrightarrow> t V \<^bold>\<preceq> U" 

(*
The monotone Galois connection is 
order-preserving (monotone) between P(X) and P(Y), 
while the antitone Galois and the Lagois connection are 
order-reversing (antimonotone) between the two powersets
*)


(*
It is well known that closure operators can be derived 
from Galois connections in a natural way. 
More generally, it is easy to show that

(i) In the antitone Galois connection case:
    t \<circ> s is a closure operator on P(X), and 
    s \<circ> t is a closure operator on P(Y);
(ii) In the monotone Galois connection case:
     t \<circ> s is a closure operator on P(X), and 
     s \<circ> t is an interior operator on P(Y);
(iii) In the anti-Galois connection case:
     t \<circ> s is an interior operator on P(X), and 
     s \<circ> t is an interior operator on P(Y).
*)

lemma 
  assumes "antitone_gal s t"
  shows "general_Cl (t \<circ> s)" and "general_Cl (s \<circ> t)"
  sorry

lemma 
  assumes "monotone_gal s t"
  shows "general_Cl (t \<circ> s)" and "general_Int' (s \<circ> t)"
  sorry

lemma 
  assumes "lagois_conn s t"
  shows "general_Int' (t \<circ> s)" and "general_Int' (s \<circ> t)"
  sorry

(*
Case (i) 
is the well-known case for generating a pair of closure operators 
from the (antitone) Galois connections, 
used in the Formal Concept Analysis [8]. 

Case (ii) 
generates one closure operator and one interior operator 
from the (monotone) Galois connections, as used in rough set theory 
and concept lattice [21–23]. 

Both Case (i) and (ii) are popular in theoretical computer science. 

Case (iii) produces a pair of interior operators, 
a variant of the other two kinds, see Ref. [20].
*)



end

