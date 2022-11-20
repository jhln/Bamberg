theory Chap1_DataStructure_BooleanAlgebra_extended
  imports 
    Main 
    "Deriving/Comparator_Generator/Compare_Order_Instances"
begin



section "5 element term algebra"

datatype s =
    S1 | S2 | S3
    | Meet s s (infixr "\<^bold>\<inter>" 55)
    | Join s s (infixr "\<^bold>\<union>" 55)
    | Nega s ("\<^bold>\<not> _" 55)
    | Zero ("\<^bold>0")
    | One ("\<^bold>1")

thm "s.induct"
thm "s.rec"
(* derive lexicographic ordering for datatype definition by given package *)
derive compare_order s
thm add_ac





section "powerset representation as boolean algebra interpretation 
( also called 'the shallow embedding method'),
maybe  as a Functor formalizable ..."

datatype c = C1 | C2 | C3

fun translate :: "s \<Rightarrow> (c \<Rightarrow> bool)" where
"translate S1 = (\<lambda> c. c = C1)" |
"translate S2 = (\<lambda> c. c = C2)" |
"translate S3 = (\<lambda> c. c = C3)" |
"translate (Meet s1 s2) = (\<lambda> c. (translate s1) c \<and> (translate s2) c)" |
"translate (Join s1 s2) = (\<lambda> c. (translate s1) c \<or> (translate s2) c)" |
"translate (Nega x) = (\<lambda> c. \<not> (translate x) c)" |
"translate Zero = (\<lambda> _. False)" |
"translate One = (\<lambda> _. True)"


subsection "extended powerset type actually only 
shows up for more than elements"

datatype c' = 
  ZeroSet | C1Set | C2Set | C3Set |
  C1C2Set | C1C3Set | C2C3Set | OneSet |
  MeetSet c' c' | JoinSet c' c' | NegSet c'

fun reduce :: "s \<Rightarrow> c'" where
"reduce S1 = C1Set" |
"reduce S2 = C2Set" |
"reduce S3 = C3Set" |
"reduce (Meet S1 S2) = ZeroSet" |
"reduce (Meet S1 S3) = ZeroSet" |
"reduce (Meet S2 S3) = ZeroSet" |
(* ... more sub cases are missing ... *)
"reduce (Meet s1 s2) = MeetSet (reduce s1) (reduce s2)" |
"reduce (Join S1 S2) = C1C2Set" |
"reduce (Join S1 S3) = C1C3Set" |
"reduce (Join S2 S3) = C2C3Set" |
(* ... more sub cases are missing ... *)
"reduce (Join s1 s2) = JoinSet (reduce s1) (reduce s2)" |
"reduce (Nega S1) = C2C3Set" |
"reduce (Nega S2) = C1C3Set" |
"reduce (Nega S3) = C1C2Set" |
(* ... more sub cases are missing ... *)
"reduce (Nega x) = NegSet (reduce x)" |
"reduce Zero = ZeroSet" |
"reduce One = OneSet"


(*
or in a general normalisation function, that is not coorectly done here:

fun meetSet :: "c' \<Rightarrow> c' \<Rightarrow> c'" 
  and  joinSet :: "c' \<Rightarrow> c' \<Rightarrow> c'" 
  and negSet :: "c' \<Rightarrow> c'" where
"meetSet ZeroSet _ = ZeroSet" |
"meetSet _ ZeroSet = ZeroSet" |
"meetSet OneSet c = c" |
"meetSet c OneSet = c" |
"meetSet C1Set C2Set = ZeroSet" |
"meetSet C2Set C1Set = ZeroSet" |
"meetSet C1Set C1Set = C1Set" |
"meetSet C2Set C2Set = C2Set" |
"meetSet (MeetSet x y) z = meetSet (meetSet x y) z" |
"meetSet (JoinSet x y) z = meetSet (joinSet x y) z" |
"meetSet (NegSet x) z = meetSet (negSet x) z" |
"meetSet z (MeetSet x y) = meetSet z (meetSet x y)" |
"meetSet z (JoinSet x y) = meetSet z (joinSet x y)" |
"meetSet z (NegSet x) = meetSet z (negSet x)" |
"joinSet ZeroSet c = c" |
"joinSet c ZeroSet = c" |
"joinSet OneSet _ = OneSet" |
"joinSet _ OneSet = OneSet" |
"joinSet C1Set C2Set = OneSet" |
"joinSet C2Set C1Set = OneSet" |
"joinSet C1Set C1Set = C1Set" |
"joinSet C2Set C2Set = C2Set" |
"joinSet (MeetSet x y) z = joinSet (meetSet x y) z" |
"joinSet (JoinSet x y) z = joinSet (joinSet x y) z" |
"joinSet (NegSet x) z = joinSet (negSet x) z" |
"joinSet z (MeetSet x y) = joinSet z (meetSet x y)" |
"joinSet z (JoinSet x y) = joinSet z (joinSet x y)" |
"joinSet z (NegSet x) = joinSet z (negSet x)" |
"negSet ZeroSet = OneSet" |
"negSet OneSet = ZeroSet" |
"negSet C1Set = C2Set" |
"negSet C2Set = C1Set" |
"negSet (MeetSet x y) = negSet (meetSet x y)" |
"negSet (JoinSet x y) = negSet (joinSet x y)" |
"negSet (NegSet x) = negSet (negSet x)"

*)


end