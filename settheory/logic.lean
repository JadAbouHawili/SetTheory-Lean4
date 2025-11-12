import settheory.MathlibTheorems

theorem notleft_right {P Q : Prop} (Or : P ∨ Q) (notleft : ¬P) : Q := by
  cases Or
  contradiction
  assumption

theorem notright_left {P Q : Prop} (Or : P ∨ Q) (notright : ¬Q) : P := by
  cases Or
  assumption
  contradiction

        #check ne_eq
        #check ne_false_of_eq_true
        #check ne_true_of_eq_false
example {P : Prop} (h : P) (h': ¬P) : False := by
  show_term contradiction
#check of_eq_true
#check of_eq_false

#check imp_false
#check implies_true
#check true_implies
#check true_imp_iff
#check false_implies
#check true_iff
#check false_iff
#check iff_false
#check Or.elim
-- not_true not_false_eq_true not_true_eq_false

  #check or_imp
  #check imp_or
  #check imp_or'
  #check Or.imp

#check neq_of_not_iff
--#check or_not_of_imp
--#check imp_iff_not_or
variable {emTruth : (P : Prop) → P = True ∨ P = False}

#check true_ne_false
#check not_true_eq_false
--#check refl
#check eq_self
--     #check Implies.trans
     #check trans
     #check Eq.trans

-- docs for the apply tactic
/-
Having
```
h : P → Q

Goal:
Q
```
then `apply h` will change the goal from `Q` to `P` , because proving `P` would give you `Q`.
-/


#check not_iff
#check and_iff_not_or_not
#check iff_iff_and_or_not_and_not

#check not_iff_not
#check xor_iff_not_iff
#check xor_iff_iff_not
#check xor_iff_not_iff'
#check iff_iff_and_or_not_and_not
#check or_self

#check HEq
#check Eq

  #check Classical.not_and_iff_or_not_not
  #check not_and
  #check or_iff_right_of_imp
  #check not_and_of_not_or_not
  #check not_or

#check iff_iff_eq
#check iff_true_right
#check Int.sign_eq_neg_one_iff_neg

  #check iff_of_true
  #check iff_false_right
  #check iff_true_right
  #check iff_of_false

#check not_imp
#check and_imp

#check iff_iff_implies_and_implies
#check not_imp_not
theorem IffToIf {p : Prop} {q: Prop} (h : p ↔ q) : (p → q) ∧ (¬p → ¬q) := by 
  rw [not_imp_not]
  exact iff_iff_implies_and_implies.mp h

  --constructor
  --· exact h.mp
  --· exact Function.mt (h.mpr)

theorem IfToIff{p : Prop} {q: Prop} (h : p → q) (h' : ¬p → ¬q) : p ↔ q := by 
  rw [not_imp_not] at h'
  exact iff_iff_implies_and_implies.mpr ⟨h,h'⟩

  --constructor
  --· assumption
  --· intro hq
  --  exact (Function.mtr h') hq
#check imp_or
#check imp_not_self

theorem eq_of_or_not
{A B w : Type}
{p : Type → Prop}
(AorB : w = A ∨ w = B)
(npA : ¬(p A))
(pw : p w)
: w = B := by
  rcases AorB with h|h
  rw [h] at pw
  contradiction
  assumption
