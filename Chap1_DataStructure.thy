theory Chap1_DataStructure
  imports 
    Main 
    "Deriving/Comparator_Generator/Compare_Order_Instances"
begin


section "residuated lattice"

datatype s =
    P int ("\<llangle>_\<rrangle>" 55)
    | Var nat ("\<guillemotleft>_\<guillemotright>" 55)
    | Meet s s (infixr "\<^bold>\<inter>\<^sub>s" 55)
    | Join s s (infixr "\<^bold>\<union>\<^sub>s" 55)
    | Prod s s (infixr "\<^bold>\<cdot>\<^sub>s" 55)
    | Impl s s (infixr "\<^bold>\<rightarrow>\<^sub>s" 55)
    | Zero ("\<^bold>0\<^sub>s")
    | One ("\<^bold>1\<^sub>s")
    | Bot ("\<^bold>\<bottom>\<^sub>s")
    | Top ("\<^bold>\<top>\<^sub>s")

derive compare_order s

value "P 8 \<le> P 8"
value "P 8 \<le> P 7"
value "P 8 \<le> P 7"

thm add_ac






section "TestQuotient"

definition testRel :: "s \<Rightarrow> s \<Rightarrow> bool" where
"testRel s1 s2 \<equiv> True"

quotient_type TestQuot = "s" / "testRel"
  morphisms Rep_S Abs_S
proof (rule equivpI)
  show "reflp testRel" unfolding reflp_def testRel_def
    by simp
  show "symp testRel" unfolding symp_def testRel_def
    by simp
  show "transp testRel" unfolding transp_def testRel_def
    by simp
qed




section "Quotient by Lattice Laws"

(*
function laws :: "s \<Rightarrow> s \<Rightarrow> bool" where
s_commu_mult: "laws (Prod s1a s1b) (Prod s2a s2b) = ((s1a = s2a) \<and> (s1b = s2b))" |
s_unitR_mult:  "laws (Prod s1a \<^bold>1\<^sub>s) s2 = (s1a = s2)" |
s_unitL_mult:  "laws (Prod \<^bold>1\<^sub>s s1a) s2 = (s1a = s2)"
proof -*)


definition laws :: "s \<Rightarrow> s \<Rightarrow> bool" where
"laws s1 s2 \<equiv>
(case s1 of (Prod \<^bold>1\<^sub>s s1a)
\<Rightarrow> s1a = s2)"







section "quotient exercise for Ints from Nats"

definition intRel :: "(nat * nat) => (nat * nat) => bool" where
  "intRel  \<equiv> \<lambda> (x, y) (u, v). (x + v = u + y)"

lemma intRel_iff [simp]: "intRel (x,y) (u,v) \<longleftrightarrow> x + v = u + y"
proof
  show "intRel (x, y) (u, v) \<Longrightarrow> x + v = u + y"
    by (auto simp: intRel_def)
  show "x + v = u + y \<Longrightarrow> intRel (x, y) (u, v)"
    by (auto simp: intRel_def)
qed

quotient_type int = "nat * nat" / "intRel"
  morphisms Rep_Integ Abs_Integ
proof (rule equivpI)
  show "reflp intRel" by (auto simp: reflp_def)
  show "symp intRel" by (auto simp: symp_def)
  show "transp intRel" by (auto simp: transp_def)
qed


find_theorems "Abs_Integ" 
find_theorems name: "Int.plus_int*"

lift_definition int_plus:: "int \<Rightarrow> int \<Rightarrow> int"
  is "\<lambda>(a,b)(c,d). (a+c, b+d)"
  apply  clarify
  by simp

lemma plus_comm: "int_plus x y = int_plus y x"
  apply transfer
  apply clarify
  by (simp add: intrel_def)


end