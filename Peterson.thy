theory Peterson
imports Main
begin

text {*
The Peterson mutual exclusion algorithm (for 2 processes numbered 0 and 1). Code for process i:
while (true)
  v1: idle_i = false
  v2: turn = (i+1) mod 2
  v3: await idle_[(i+1) mod 2] or turn = i
  v4: critical section
  v5: idle_i = true *}

section {* Specification of the algorithm *}

typedecl State
  -- "The state of the system"

type_synonym 'a StateFun = "State \<Rightarrow> 'a"
-- "The type of variables"

datatype label1 = p1_l1 | p1_l2 | p1_l3 | p1_l4 
datatype label2 = p2_l1 | p2_l2 | p2_l3 | p2_l4 

datatype Proc = P1 | P2

(*The variables*)
consts
  pc1       ::       "label1 StateFun"
  pc2       ::       "label2 StateFun"
  flag1     ::       "bool StateFun"
  flag2     ::       "bool StateFun"
  turn      ::       "Proc StateFun"

definition unchanged :: "('a StateFun) \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "unchanged \<equiv> \<lambda> fun s s' . fun s = fun s'"

definition transition :: "(State \<times> State) set" where
  "transition \<equiv>
      {(s,s').
        (pc1 s = p1_l1 \<and> pc1 s' = p1_l2 \<and> flag1 s' = True \<and> unchanged (\<lambda> s . (pc2 s, flag2 s, turn s)) s s')
        \<or>(pc1 s = p1_l2 \<and> pc1 s' = p1_l3 \<and> turn s' = P2  \<and> unchanged (\<lambda> s .(pc2 s, flag1 s, flag2 s)) s s')
        \<or>(pc1 s = p1_l3 \<and> pc1 s' = p1_l4 \<and> (flag2 s = False \<or> turn s = P1)  \<and> unchanged (\<lambda> s . (pc2 s, flag1 s, flag2 s, turn s)) s s')
        \<or>(pc1 s = p1_l4 \<and> pc1 s' = p1_l1 \<and> flag1 s' = False  \<and> unchanged (\<lambda> s . (pc2 s, flag1 s, flag2 s, turn s)) s s')

        \<or>(pc2 s = p2_l1 \<and> pc2 s' = p2_l2 \<and> flag2 s' = True \<and> unchanged (\<lambda> s . (pc1 s, flag1 s, turn s)) s s')
        \<or>(pc2 s = p2_l2 \<and> pc2 s' = p2_l3 \<and> turn s' = P1 \<and> unchanged (\<lambda> s . (pc1 s, flag1 s, flag2 s)) s s')
        \<or>(pc2 s = p2_l3 \<and> pc2 s' = p2_l4 \<and> (flag1 s = False \<or> turn s = P2) \<and> unchanged (\<lambda> s . (pc1 s, flag1 s, flag2 s, turn s)) s s')
        \<or>(pc2 s = p2_l4 \<and> pc2 s' = p2_l1 \<and> flag2 s' = False \<and> unchanged (\<lambda> s . (pc1 s, flag1 s, turn s)) s s')
    }"

definition initial :: "State set" where
  "initial \<equiv> {s.
  pc1 s = p1_l1
  \<and> pc2 s = p2_l1
  \<and> flag1 s = False 
  \<and> flag2 s = False
  \<and> turn s = P1}"

definition safe :: "State set" where
  -- "Definition of the safety property of the algorithm"
  "safe \<equiv> {s. \<not> (pc1 s = p1_l4 \<and> pc2 s = p2_l4) }"

section {*Safety proof*}

definition ind_inv :: "State set \<Rightarrow> bool" where
-- "The definition of an inductive state invariant"
  "ind_inv p \<equiv> initial \<subseteq> p \<and> (\<forall> s s'. (s : p \<and> (s,s') \<in> transition) \<longrightarrow> s' : p)"

subsection {* Four invariants that imply the safety property *}

definition inv1_p1 :: "State set" where
  "inv1_p1 \<equiv> {s. pc1 s : {p1_l2, p1_l3, p1_l4} \<longrightarrow> (flag1 s = True)}"

definition inv1_p2 :: "State set" where
  "inv1_p2 \<equiv> {s. pc2 s : {p2_l2, p2_l3, p2_l4} \<longrightarrow> (flag2 s = True)}"

definition inv2_p1 :: "State set" where
  "inv2_p1 \<equiv> {s. pc1 s = p1_l4 \<longrightarrow> (flag2 s = False \<or> turn s = P1 \<or> pc2 s = p2_l2)}"

definition inv2_p2 :: "State set" where
  "inv2_p2 \<equiv> {s. pc2 s = p2_l4 \<longrightarrow> (flag1 s = False \<or> turn s = P2 \<or> pc1 s = p1_l2)}"

lemma invariants_inductive: "ind_inv inv1_p1 \<and> ind_inv inv2_p2 \<and> ind_inv inv1_p2 \<and> ind_inv inv2_p1"
  -- "Proof that the invariants are inductive"
unfolding ind_inv_def initial_def inv1_p1_def inv1_p2_def inv2_p1_def inv2_p2_def transition_def unchanged_def 
by auto

theorem safety: "inv1_p1 Int inv1_p2 Int inv2_p1 Int inv2_p2 \<subseteq> safe" 
  -- "Proof that the invariants imply the safety property"
unfolding inv1_p1_def inv1_p2_def inv2_p1_def inv2_p2_def safe_def 
by auto

end