import settheory.MathlibTheorems
import settheory.setTheorems


#print Xor'
#check Xor'
#check not_xor
/-
def Xor' (a b : Prop) := (a ∧ ¬ b) ∨ (b ∧ ¬ a)

# Exclusive Or 

## Rewriting Xor'
`Xor' p q` can be rewritten as:
```
(p ∧ ¬q) ∨ (¬p ∧ q)
```
To rewrite `Xor'` in the goal:
```
rw [Xor']
```

To rewrite `Xor'` in hypothesis `h`:
```
rw [Xor'] at h
```

# Xor
To introduce Xor, introduce as the negation of if and only if. Xor is inequivalence, Xor is such that exactly one of the propositions is truei.e exclusive or. 
-/

theorem XorToOr_set 
{K : Type} {A : K} (S : Set K) (S' : Set K) (h : S ∩ S' = ∅)
: Xor' (A ∈ S) (A ∈ S') ↔ A ∈ S ∨ A ∈ S' := by
  rw [xor_iff_or_and_not_and]
  rw [not_and_or]
  constructor
  intro a1
  · have : A ∈ S ↔ A ∉ S' := by{
    constructor
    · intro h1
      intro h2
      have := Set.mem_inter h1 h2
      rw [h] at this
      contradiction
    · intro h1
      simp [h1] at a1
      assumption
      }
    simp [this]
    apply em'
  · intro a1
    constructor
    assumption
    rcases a1 with ha1|ha2
    simp [ha1]
    intro
    contradiction
    simp [ha2]
    intro
    contradiction

theorem XorToOr_Finset {Inhabitant : Type} {inst : DecidableEq Inhabitant}{S : Finset Inhabitant } {S' : Finset Inhabitant} (A : Inhabitant)
(h : S ∩ S' = ∅ ) : Xor' (A ∈ S) (A ∈ S') ↔ A ∈ S ∨ A ∈ S' := by
  constructor
  unfold Xor' at *
  · intro h'
    rcases h' with h_1|h_1
    · exact Or.inl (h_1.left)
    · exact Or.inr (h_1.left)
  · intro h'
    unfold Xor'
    cases h'
    · left
      constructor
      assumption
      intro
      contradiction
    · right
      constructor
      assumption
      intro
      contradiction

