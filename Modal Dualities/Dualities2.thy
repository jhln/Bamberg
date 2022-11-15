theory Dualities2
imports Dualities0
begin

nitpick_params[assms = true, user_axioms=true]


datatype a = Hallo


section "from right to left proofs"

lemma r2l_D: "(\<forall> p w. ((\<^bold>\<box>\<^sub>R p) \<^bold>\<rightarrow> (\<^bold>\<diamondsuit>\<^sub>R p)) w) \<longrightarrow> serial R " 
  (*by (metis box_def dia_def impl_def serial_def)*)
proof (rule, unfold serial_def, rule, rule ccontr)
  fix u
  assume D: "\<forall> p w. ((\<^bold>\<box>\<^sub>R p) \<^bold>\<rightarrow> (\<^bold>\<diamondsuit>\<^sub>R p)) w"
  then have uD: "\<forall> p. ((\<^bold>\<box>\<^sub>R p) \<^bold>\<rightarrow> (\<^bold>\<diamondsuit>\<^sub>R p)) u" by simp
  assume non_seri: "\<not> (\<exists> v. R u v)"
  from non_seri have box: "\<forall> p. (\<^bold>\<box>\<^sub>R p) u" using box_def by metis
  from non_seri have dia: "\<not> (\<forall> p. (\<^bold>\<diamondsuit>\<^sub>R p) u)" using dia_def by metis
  from D box dia show False using impl_def by metis
qed

(*Suppose D is valid in F = \<langle>W, R\<rangle>, i.e., F \<Turnstile> \<box>p \<rightarrow> \<diamondsuit>p. 
Let M = \<langle>W, R, V \<rangle> be a model based on F, and w \<in> W. 
We have to show that there is a v such that Rwv. 
Suppose not: then both M, w \<tturnstile> \<box>\<phi> and M, w \<tturnstile>/ \<diamondsuit>\<phi>
for any \<phi>, including p. 
But then M, w \<tturnstile>/ \<box>p \<rightarrow> \<diamondsuit>p, contradicting the
assumption that F \<Turnstile> \<box>p \<rightarrow> \<diamondsuit>p. *)


lemma r2l_T: "(\<forall> w p. ((\<^bold>\<box>\<^sub>R p) \<^bold>\<rightarrow> p) w) \<longrightarrow> reflexive R" 
  (*by (metis box_def impl_def reflexive_def)*)
proof (rule, unfold reflexive_def impl_def)
  assume valid_T: "\<forall> w p. (\<^bold>\<box>\<^sub>R p) w \<longrightarrow> p w"
  show "\<forall>w. R w w"
  proof 
    fix w
    obtain p where "\<forall> u. p u \<longleftrightarrow> R w u" by auto
    hence pU: "\<forall> u. R w u \<longrightarrow> p u" by simp
    hence Box_pW: "(\<^bold>\<box>\<^sub>R p) w" by (simp add: box_def)
    hence pW: "p w" using valid_T by auto
    from this show "R w w" by (simp add: \<open>\<forall>u. p u = R w u\<close>)
  qed
qed


(*Suppose T is valid in F, i.e., F \<Turnstile> \<box>p \<rightarrow> p. 
Let w \<in> W be an arbitrary world; we need to show Rww. 
Let u \<in> V (p) if and only if Rwu 
(when q is other than p, V (q) is arbitrary, say V (q) = \<emptyset>). 
Let M = \<langle>W, R, V \<rangle>. 
By construction, for all u such that Rwu: 
M, u \<tturnstile> p, and hence M, w \<tturnstile> \<box>p.
But by hypothesis \<box>p\<rightarrow>p is true at w, so that M, w \<tturnstile> p, 
but by definition of V this is possible only if Rww.
*)
declare[[show_types]]

definition converse::"('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool)" 
  where "converse R \<equiv> \<lambda>x y. R y x"

lemma r2l_B: "\<forall> R. (\<forall> p w . (p \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>R (\<^bold>\<diamondsuit>\<^sub>R p))) w) \<longrightarrow> symmetric R" 
proof (rule, rule impI, unfold symmetric_def, rule ccontr)
  fix R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assume B: "\<forall>(p::'a \<Rightarrow> bool) w::'a. (p \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>R \<^bold>\<diamondsuit>\<^sub>R p) w"
  assume non_sym: "\<not> (\<forall>u v. R u v \<longrightarrow> R v u)"
  then obtain u v where uRv: "R u v \<and> \<not> (R v u)" by auto
  let ?p = "\<lambda> w. \<not> R v w"
  (*have defP: "(\<forall> w. ?p w \<longleftrightarrow> \<not> R v w)" by simp
  hence*) 
  have "\<exists> p. (\<forall> w. p w \<longleftrightarrow> \<not> R v w)" by auto 
  then obtain p where "\<forall> w. p w \<longleftrightarrow> \<not> (R v w)" by auto
  hence pU: "p u" by (simp add: uRv)
  hence "\<not> (\<exists> w. R v w \<and> p w)"
    using \<open>\<forall>w::'a. (p::'a \<Rightarrow> bool) w = (\<not> (R::'a \<Rightarrow> 'a \<Rightarrow> bool) (v::'a) w)\<close> by auto
  hence "\<not> ((\<^bold>\<diamondsuit>\<^sub>R p) v)" by (metis dia_def) 
  hence "\<not> (\<^bold>\<box>\<^sub>R (\<^bold>\<diamondsuit>\<^sub>R p)) u" by (metis box_def uRv)
  hence "\<not> (p \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>R (\<^bold>\<diamondsuit>\<^sub>R p))) u" by (simp add: impl_def pU)
  thus False by (simp add: B)
qed

(* We prove the contrapositive: Suppose F is not symmetric, 
we show that B, i.e., p \<rightarrow> \<box>\<diamondsuit>p is not valid in F = \<langle>W, R\<rangle>. 
If F is not symmetric, there are u, v \<in> W such that Ruv but not Rvu. 
Define V such that w \<in> V (p) if and only if not Rvw 
(and V is arbitrary otherwise). 
Let M = \<langle>W, R, V \<rangle>.
Now, by definition of V , M, w \<tturnstile> p for all w such that not Rvw, 
in particular, M, u \<tturnstile> p since not Rvu. 
Also, since Rvw iff w /\<in> V (p), there is no w 
such that Rvw and M, w \<tturnstile> p, and hence M, v /\<tturnstile> \<diamondsuit>p. 
Since Ruv, also M, u /\<tturnstile> \<box>\<diamondsuit>p. 
It follows that M, u /\<tturnstile> p \<rightarrow> \<box>\<diamondsuit>p, and so B is not valid in F
*)



lemma r2l_4: "\<forall> R. (\<forall> w p. ((\<^bold>\<box>\<^sub>R p) \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>R (\<^bold>\<box>\<^sub>R p))) w ) \<longrightarrow> transitive R"
  (*by (metis box_def impl_def transitive_def)*)
proof (rule, rule, unfold transitive_def impl_def)
  fix R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assume valid_4: "\<forall> w p. (\<^bold>\<box>\<^sub>R p) w \<longrightarrow> (\<^bold>\<box>\<^sub>R (\<^bold>\<box>\<^sub>R p)) w"
  show "\<forall>a b c. R a b \<and> R b c \<longrightarrow> R a c"
  proof (rule, rule, rule, rule)
    fix a b c
    assume tran: "R a b \<and> R b c"
    show "R a c"
    proof -
      obtain p where pDef: "\<forall> z. p z \<longleftrightarrow> R a z" by auto
      hence "\<forall> z. R a z \<longrightarrow> p z" by auto
      hence box_pA: "(\<^bold>\<box>\<^sub>R p) a" by (simp add: box_def)
      hence boxbox_pA:"(\<^bold>\<box>\<^sub>R (\<^bold>\<box>\<^sub>R p)) a" using valid_4 by (simp)
      hence "\<forall>w. R a w \<longrightarrow> (\<forall>w'. R w w' \<longrightarrow> p w')" using box_def by metis
      hence "p c" using tran by auto
      thus "R a c" by (simp add: pDef)
    qed
  qed
qed       


(* Suppose 4 is valid in F = \<langle>W, R\<rangle>, i.e., F \<Turnstile> \<box>p \<rightarrow> \<box>\<box>p, 
and let u, v, w \<in> W be arbitrary worlds such that Ruv and Rvw; 
we need to show that Ruw. 
Define V such that z \<in> V (p) if and only if Ruz (and V is
arbitrary otherwise). 
Let M = \<langle>W, R, V \<rangle>. By definition of V , M, z \<tturnstile> p for all z 
such that Ruz, and hence M, u \<tturnstile> \<box>p. But by hypothesis 4,
\<box>p \<rightarrow> \<box>\<box>p, is true at u, so that M, u \<tturnstile> \<box>\<box>p. 
Since Ruv and Rvw, we have M, w \<tturnstile> p, 
but by definition of V this is possible only if Ruw, as desired.
*)


lemma r2l_5: "\<forall> R. (\<forall> w p. ((\<^bold>\<diamondsuit>\<^sub>R p) \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>R (\<^bold>\<diamondsuit>\<^sub>R p))) w) \<longrightarrow> euclidean R" 
proof (rule, unfold euclidean_def, rule, rule ccontr)
  fix R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assume T5: "(\<forall> w p. ((\<^bold>\<diamondsuit>\<^sub>R p) \<^bold>\<rightarrow> (\<^bold>\<box>\<^sub>R (\<^bold>\<diamondsuit>\<^sub>R p))) w)"
  assume "\<not> (\<forall>r s t. R r s \<and> R r t \<longrightarrow> R s t)"
  then obtain w u v where xRy: "R w u \<and> R w v \<and> \<not> R u v" by auto
  let ?p = "\<lambda> z. \<not> R u z"
  have defP:  "(\<forall> z. ?p z \<longleftrightarrow> \<not> R u z)" by simp
  hence "\<exists> p. (\<forall> z. p z \<longleftrightarrow> \<not> R u z)" by auto
  then obtain p where pDef: "\<forall> z. p z \<longleftrightarrow> \<not> (R u z)" by auto
  hence pV: "p v" by (simp add: xRy)
  hence ante: "(\<^bold>\<diamondsuit>\<^sub>R p) w" using xRy dia_def by metis
  hence "\<not> (\<exists> y. R u y \<and> p y)" by (simp add: pDef)
  hence "\<not> (\<^bold>\<diamondsuit>\<^sub>R p) u" using xRy dia_def by metis
  hence post: "\<not> (\<^bold>\<box>\<^sub>R (\<^bold>\<diamondsuit>\<^sub>R p)) w" using xRy box_def by metis
  from ante post T5 show False by (simp add: impl_def)
qed



(* We proceed contrapositively, 
assuming that the frame F = \<langle>W, R\<rangle> is not euclidean, 
and show that it falsifies 5, i.e., F ⊭ \<diamondsuit>p \<rightarrow> \<box>\<diamondsuit>p. 
Suppose there are worlds u, v, w \<in> W 
such that Rwu and Rwv but not Ruv. 
Define V such that for all worlds z, z \<in> V (p) 
if and only if it is not the case that Ruz. 
Let M = \<langle>W, R, V \<rangle>. 
Then by hypothesis M, v \<tturnstile> p and since Rwv also M, w \<tturnstile> \<diamondsuit>p. 
However, there is no world y such that Ruy and M, y \<tturnstile> p so M, 
u /\<tturnstile> \<diamondsuit>p. Since Rwu, it follows that M, w /\<tturnstile> \<box>\<diamondsuit>p, so that
5, \<diamondsuit>p \<rightarrow> \<box>\<diamondsuit>p, fails at w
*)



lemma
  assumes 1: "\<not>A"
  shows "A \<longrightarrow> B"
proof -
  {
  assume "A"
  from 1 this have "B" by (rule notE)
  } then show "A \<longrightarrow> B" by (rule impI)
qed



lemma
  assumes 1: "\<not>A"
  shows "A \<longrightarrow> B"
proof -
  {
  assume "A"
  have "B" sorry
  } then show "A \<longrightarrow> B" by (rule impI)
qed

lemma
  assumes 1: "\<not>A"
  shows "A \<longrightarrow> B"
proof
  assume 2: "A"
  show "B" 
  proof -
    from 1 2 show B by (rule notE)
  qed
qed


lemma
  assumes 1: "\<not>A"
  shows "A \<longrightarrow> B"
proof
  assume 2: "A"
  from 1 2 show B by (rule notE)
qed



lemma 
  assumes "\<forall> X. p X"
  shows "\<exists> X. p X"
proof -
  have "p A" using assms(1) by (rule allE)
  thus "\<exists>X. p X" by (rule exI)
qed


lemma
  assumes "\<exists> x. P x \<and> Q x"
  shows "\<exists> x. P x"
proof -
  from assms obtain x where "P x \<and> Q x" by (rule exE)
  hence "P x" by (rule conjunct1)
  thus "\<exists> x. P x" by (rule exI)
qed


(*overlord , verbose, debug *)

end