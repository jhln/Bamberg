theory Dualities1
  imports  Dualities0
begin



section "from left to right proofs"

section "from frame-property to truth"
lemma l2r_B: "\<forall> R. symmetric R \<longrightarrow> (\<forall>w. (p \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>R \<^bold>\<diamondsuit>\<^sub>R p) w)"
proof ( unfold symmetric_def impl_def box_def dia_def, 
        rule, rule, rule, rule, rule)
  fix R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fix w v
  assume symm: "\<forall>u v. R u v \<longrightarrow> R v u"
  assume 1: "p w"
  show "R w v \<longrightarrow> (\<exists>va. R v va \<and> p va)"
  proof
    assume wRv: "R w v"
    show "(\<exists>va. R v va \<and> p va)"
    proof 
      have vRw: "R v w" using symm wRv by auto
      thus "R v w \<and> p w" using 1 by blast
    qed
  qed
qed


(*case for B: 
to show that the schema is true in a model 
we need to show that all of its instances are true 
at all worlds in the model. 
So let \<phi> \<rightarrow> \<box>\<diamondsuit>\<phi> be a given instance of B, 
and let w \<in> W be an arbitrary world.
Suppose the antecedent \<phi> is true at w, 
in order to show that \<box>\<diamondsuit>\<phi> is true at w. 
So we need to show that \<diamondsuit>\<phi> is true at all w\<Zprime> accessible from w. 
Now, for any w\<Zprime> such that Rww\<Zprime> we have, 
using the hypothesis of symmetry, that also Rw\<Zprime>w (see Figure 2.1). 
Since M, w \<tturnstile> \<phi>, we have M, w\<Zprime> \<tturnstile> \<diamondsuit>\<phi>. 
Since w\<Zprime> was an arbitrary world such that Rww\<Zprime>, we have M, w \<tturnstile> \<box>\<diamondsuit>\<phi>.
*)

lemma l2r_B': "symmetric R \<Longrightarrow> (\<forall>w. (p \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>R \<^bold>\<diamondsuit>\<^sub>R p) w)"
  apply (rule allI, unfold impl_def symmetric_def)
proof
  fix w
  assume sym: "\<forall>u v. R u v \<longrightarrow> R v u"
      and pW: "p w"
  show "(\<^bold>\<box>\<^sub>R \<^bold>\<diamondsuit>\<^sub>R p) w"
  proof (unfold box_def, rule allI, rule impI)
    fix v
    assume "R w v"
    from this sym 
    have symR: "R v w" by blast
    from symR and pW 
    show "(\<^bold>\<diamondsuit>\<^sub>R p) v" by (meson dia_def)
  qed
qed


lemma l2r_T: "reflexive R \<Longrightarrow> (\<forall> w. ((\<^bold>\<box>\<^sub>R p) \<^bold>\<rightarrow> p) w)" 
  apply (unfold impl_def reflexive_def)
proof
  fix w
  assume refl: "\<forall>w. R w w"
  show "(\<^bold>\<box>\<^sub>R p) w \<longrightarrow> p w"
  proof (rule impI, unfold box_def)
    assume boxW: "\<forall>v. R w v \<longrightarrow> p v"
    from this and refl 
    show "p w" by simp
  qed
qed


lemma l2r_4: "transitive R \<Longrightarrow> (\<forall> w. ((\<^bold>\<box>\<^sub>R p) \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>R (\<^bold>\<box>\<^sub>R p))) w )"
proof 
  fix w
  assume trans: "transitive R"
  show "(( \<^bold>\<box>\<^sub>R p) \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>R \<^bold>\<box>\<^sub>R p)) w"
  proof (unfold impl_def box_def, rule impI)
    assume wP: "\<forall>v. R w v \<longrightarrow> p v"
    show "\<forall>v. R w v \<longrightarrow> (\<forall>va. R v va \<longrightarrow> p va)"
    proof (rule allI, rule impI)
      fix v
      assume wRv: "R w v"
      show "\<forall>va. R v va \<longrightarrow> p va"
      proof (rule allI, rule impI)
        fix va
        assume vRva: "R v va"
        from trans wRv vRva 
        have "R w va" by (meson transitive_def)
        from this and wP 
        show "p va" by simp
      qed
    qed
  qed
qed


lemma l2r_D: "serial R \<longrightarrow> (\<forall> w. ((\<^bold>\<box>\<^sub>R p) \<^bold>\<rightarrow> (\<^bold>\<diamondsuit>\<^sub>R p)) w)" 
  apply (rule impI, rule allI, unfold serial_def)
proof -
  fix w
  assume seri: "\<forall>u. \<exists>v. R u v"
  show "((\<^bold>\<box>\<^sub>R p) \<^bold>\<rightarrow> (\<^bold>\<diamondsuit>\<^sub>R p)) w"
  proof (unfold impl_def box_def dia_def, rule impI)
    assume boxW: "\<forall>v. R w v \<longrightarrow> p v"
    from seri obtain v where vDef:"R w v" by auto
    from boxW have vV: "p v" 
      by (simp add: vDef)
    hence "R w v \<and> p v" using vV
      by (simp add: vDef)
    thus "\<exists>v. R w v \<and> p v" by (rule exI)
  qed
qed


lemma l2r_5: "\<forall> R. euclidean R \<longrightarrow> (\<forall> w. ((\<^bold>\<diamondsuit>\<^sub>R p) \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>R (\<^bold>\<diamondsuit>\<^sub>R p))) w)"
proof (unfold euclidean_def, rule, rule impI, rule)
  fix R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fix w
  assume eucl: "\<forall>r s t. R r s \<and> R r t \<longrightarrow> R s t "
  show  "((\<^bold>\<diamondsuit>\<^sub>R p) \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>R (\<^bold>\<diamondsuit>\<^sub>R p))) w"
  proof (unfold impl_def box_def dia_def, rule impI, rule)
    fix v
    assume diaW: "\<exists>q. R w q \<and> p q"
    then obtain l where lDef: "R w l \<and> p l" by auto
    show "R w v \<longrightarrow> (\<exists> q. R v q \<and> p q)"
    proof (rule)
      assume wRv: "R w v"
      show "\<exists> q. R v q \<and> p q"
      proof -
        have "R v l" using eucl wRv lDef by blast
        thus ?thesis using lDef by auto
      qed
    qed
  qed
qed


end
