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

type_synonym 'a StateFun = "State => 'a" 
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

definition unchanged :: "('a StateFun) => State => State => bool" where
  "unchanged == % fun s s' . fun s = fun s'"

definition transition :: "(State * State) set" where
  "transition ==
      {(s,s').
        (pc1 s = p1_l1 & pc1 s' = p1_l2 & flag1 s' = True & unchanged (% s . (pc2 s, flag2 s, turn s)) s s')
        |(pc1 s = p1_l2 & pc1 s' = p1_l3 & turn s' = P2  & unchanged (% s .(pc2 s, flag1 s, flag2 s)) s s')
        |(pc1 s = p1_l3 & pc1 s' = p1_l4 & (flag2 s = False | turn s = P1)  & unchanged (% s . (pc2 s, flag1 s, flag2 s, turn s)) s s')
        |(pc1 s = p1_l4 & pc1 s' = p1_l1 & flag1 s' = False  & unchanged (% s . (pc2 s, flag1 s, flag2 s, turn s)) s s')

        |(pc2 s = p2_l1 & pc2 s' = p2_l2 & flag2 s' = True & unchanged (% s . (pc1 s, flag1 s, turn s)) s s')
        |(pc2 s = p2_l2 & pc2 s' = p2_l3 & turn s' = P1 & unchanged (% s . (pc1 s, flag1 s, flag2 s)) s s')
        |(pc2 s = p2_l3 & pc2 s' = p2_l4 & (flag1 s = False | turn s = P2) & unchanged (% s . (pc1 s, flag1 s, flag2 s, turn s)) s s')
        |(pc2 s = p2_l4 & pc2 s' = p2_l1 & flag2 s' = False & unchanged (% s . (pc1 s, flag1 s, turn s)) s s')
    }"

definition initial :: "State set" where
  "initial == {s.
  pc1 s = p1_l1
  & pc2 s = p2_l1
  & flag1 s = False 
  & flag2 s = False
  & turn s = P1}"

definition safe :: "State set" where
  -- "Definition of the safety property of the algorithm"
  "safe == {s. ~ (pc1 s = p1_l4 & pc2 s = p2_l4) }"

section {*Safety proof*}

definition ind_inv :: "State set => bool" where
-- "The definition of an inductive state invariant"
  "ind_inv p == initial <= p & (ALL s s'. (s : p & (s,s') : transition) --> s' : p)"

subsection {* Four invariants that imply the safety property *}

definition inv1_p1 :: "State set" where
  "inv1_p1 == {s. pc1 s : {p1_l2, p1_l3, p1_l4} --> (flag1 s = True)}"

definition inv1_p2 :: "State set" where
  "inv1_p2 == {s. pc2 s : {p2_l2, p2_l3, p2_l4} --> (flag2 s = True)}"

definition inv2_p1 :: "State set" where
  "inv2_p1 == {s. pc1 s = p1_l4 --> (flag2 s = False | turn s = P1 | pc2 s = p2_l2)}"

definition inv2_p2 :: "State set" where
  "inv2_p2 == {s. pc2 s = p2_l4 --> (flag1 s = False | turn s = P2 | pc1 s = p1_l2)}"

lemma invariants_inductive: "ind_inv inv1_p1 & ind_inv inv2_p2 & ind_inv inv1_p2 & ind_inv inv2_p1"
  -- "Proof that the invariants are inductive"
unfolding ind_inv_def initial_def inv1_p1_def inv1_p2_def inv2_p1_def inv2_p2_def transition_def unchanged_def 
by auto

theorem safety: "inv1_p1 Int inv1_p2 Int inv2_p1 Int inv2_p2 <= safe" 
  -- "Proof that the invariants imply the safety property"
unfolding inv1_p1_def inv1_p2_def inv2_p1_def inv2_p2_def safe_def 
by auto

end