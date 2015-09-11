theory MultiplicationRusse
imports Main
begin

record 's algorithm = 
  init :: 's
  trans :: "('s \<times> 's) set"

inductive
  reachable :: "'s algorithm \<Rightarrow> 's \<Rightarrow> bool"
  for A :: "'s algorithm"
  where
    reachable_0:  "reachable A (init A)"
  | reachable_n:  "\<lbrakk> reachable A s; (s,t) \<in> (trans A) \<rbrakk> 
    \<Longrightarrow> reachable A t"

definition invariant where 
  "invariant A P \<equiv> (\<forall> s . reachable A s \<longrightarrow> P s)"

theorem invariantI:
  fixes A P
  assumes "P (init A)"
  and "\<And> s t . \<lbrakk>reachable A s; P s; (s,t) \<in> trans A\<rbrakk> 
    \<Longrightarrow> P t"
  shows "invariant A P"
proof (auto simp add:invariant_def)
  fix s
  assume "reachable A s"
  thus "P s"
  proof (induct rule:reachable.induct)
    show "P (init A)" using assms by auto
  next
    fix s t
    assume "reachable A s" and "P s" 
      and "(s, t) \<in> trans A"
    thus "P t" using assms(2) by simp
  qed
qed

theorem invariant_imp:
  fixes A P Q
  assumes "invariant A P"
  and "\<And> s . P s \<Longrightarrow> Q s"
  shows "invariant A Q"
using assms
by (auto simp add:invariant_def)

datatype ligne = l1 | l2 | l3 | l4 | l5

record MultVars =
  ligne :: ligne
  x :: nat
  y :: nat
  r :: nat

sledgehammer_params[timeout=600]

locale Mult =
  fixes a b :: nat
begin

definition MultRusse where
  "MultRusse \<equiv> \<lparr>
    init = \<lparr>ligne = l1, x = a, y = b, r = 0\<rparr>,
    trans = { (s,t) .
      ligne s = l1 
        \<and> (if (x s \<noteq> 0) 
          then t = s\<lparr>ligne := l2\<rparr> 
          else t = s\<lparr>ligne := l5\<rparr>)
      \<or> ligne s = l2 
        \<and> (if (x s mod 2 = 1) 
          then t = s\<lparr>ligne := l3, r := (r s) + (y s)\<rparr>
          else t = s\<lparr>ligne := l3\<rparr>)
      \<or> ligne s = l3 \<and> t = s\<lparr>ligne := l4, x := (x s) div 2\<rparr>
      \<or> ligne s = l4 \<and> t = s\<lparr>ligne := l1, y := (y s) * 2\<rparr>
    }
  \<rparr>"

definition valide :: "MultVars \<Rightarrow> bool" where
  "valide s \<equiv> 
    ligne s = l5 \<longrightarrow> r s = a*b"

definition ind :: "MultVars \<Rightarrow> bool" where
  "ind s \<equiv>
    (ligne s \<in> {l1,l2,l5} \<longrightarrow> r s + (x s)*(y s) = a*b)
    \<and> (ligne s = l3 \<longrightarrow> r s + (x s)*(y s) = 
        (if ((x s) mod 2 = 0) then a*b else a*b + (y s)))
    \<and> (ligne s = l4 \<longrightarrow> r s + 2*(x s)*(y s) = a*b)
    \<and> (ligne s = l5 \<longrightarrow> x s = 0)"

declare 
  MultRusse_def [simp]
  valide_def [simp]
  ind_def [simp]
  split_if [split]
  split_if_asm [split]

lemma "ind s \<Longrightarrow> valide s"
by auto

lemma ind_inv:
  "invariant MultRusse ind"
proof (rule invariantI)
  show "ind (init MultRusse)" by auto
next
  fix s t
  assume 1:"ind s"
  and 2:"(s,t) \<in> trans MultRusse"
  show "ind t"
  proof (cases "ligne s")
    case l1
    hence 3:"if (x s \<noteq> 0) 
             then t = s\<lparr>ligne := l2\<rparr> 
             else t = s\<lparr>ligne := l5\<rparr>"
      using 2 by force
    show ?thesis
    proof (cases "x s \<noteq> 0")
      case True
      with 3 have "t = s\<lparr>ligne := l2\<rparr>" by auto
      with 1 l1 show ?thesis by auto
    next
      case False
      with 3 have "t = s\<lparr>ligne := l5\<rparr>" by auto
      with 1 l1 False show ?thesis by auto
    qed
  next
    case l2 
    hence 3:
      "if (x s mod 2 = 1) 
        then t = s\<lparr>ligne := l3, r := (r s) + (y s)\<rparr>
        else t = s\<lparr>ligne := l3\<rparr>"
      using 2 by force
    show ?thesis
    proof (cases "x s mod 2 = 1")
      case True
      have "t = s\<lparr>ligne := l3, r := (r s) + (y s)\<rparr>" 
        using True 3 by auto
      thus ?thesis using 1 l2 True by auto
    next
      case False
      have "t = s\<lparr>ligne := l3\<rparr>" 
        using False 3 by auto
      thus ?thesis using 1 l2 False by auto
    qed
  next
    case l3 
    hence 3:"t = s\<lparr>ligne := l4, x := (x s) div 2\<rparr>"
      using 2 by force
    show ?thesis 
    proof (cases "x s mod 2 = 0")
      case True
      thus ?thesis using 1 3 l3 by auto
    next
      case False
      have "x s \<noteq> 0" using False by linarith
      hence 4:"2*(x s div 2)*(y s) = (x s)*(y s) - (y s)"
        by (metis False diff_mult_distrib2 mult.commute mult_numeral_1_right numeral_One parity semiring_numeral_div_class.mult_div_cancel)
      hence "r s + (2*(x s div 2)*(y s)) = r s + ((x s)*(y s) - (y s))" by metis
      hence "r s + 2*(x s div 2)*(y s) = r s + ((x s)*(y s) - (y s))" by metis
      also have "... = r s + (x s)*(y s) - (y s)" using `x s \<noteq> 0` by fastforce
      finally have "r s + 2*(x s div 2)*(y s) = r s + (x s)*(y s) - (y s)" .
      moreover have "r s + (x s)*(y s) = a*b + y s" using 1 l3 False by auto
      ultimately have "r s + 2*(x s div 2)*(y s) = a*b" by auto 
      thus ?thesis using 1 3 l3 False by auto
    qed
  next
    case l4
    hence 3:"t = s\<lparr>ligne := l1, y := (y s) * 2\<rparr>" 
      using 2 by force
    thus ?thesis using 1 l4 by auto
  next
    case l5
    thus ?thesis using 2 by force
  qed
qed

end

end
