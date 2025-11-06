import settheory.MathlibTheorems
import settheory.logic

#check Finset.mem_inter
theorem disjoint_finset
{K : Type}
{inst : DecidableEq K} {left : Finset K} {right : Finset K}
{A : K}
(h : left ∩ right = ∅)
(hk : A ∈ left)
(hkn : A ∈ right) : False := by
  have := Finset.mem_inter_of_mem hk hkn
  rw [h] at this
  contradiction
macro_rules
| `(tactic| contradiction) =>
  do `(tactic |solve  | ( apply disjoint_finset ; repeat assumption ) )

theorem disjoint_set
{K : Type}
{left : Set K} {right : Set K}
{A : K}
(h : left ∩ right = ∅)
(hk : A ∈ left)
(hkn : A ∈ right)  : False := by
  have := Set.mem_inter hk hkn
  rw [h] at this
  contradiction

macro_rules
| `(tactic| contradiction) => 
  do `(tactic |solve  | ( apply disjoint_set ; repeat assumption ) )


theorem inleft_notinright_finset
{K : Type}
{S S' : Finset K}
{inst : DecidableEq K}
{A : K}
(h : S ∩ S' = ∅)
(h' : A ∈ S) : A ∉ S' := by
  intro a
  have := Finset.mem_inter_of_mem h' a
  rw [h] at this
  contradiction

theorem notinleft_inright
{K : Type}
{S S' : Finset K}
{A : K}
(SorS' : A ∈ S or A ∈ S')
(h' : A ∉ S) : A ∈ S' := by
  exact notleft_right SorS' h'

theorem inright_notinleft_finset
{K : Type}
{S S' : Finset K}
{inst : DecidableEq K}
{A : K}
(h : S ∩ S' = ∅)
(h' : A ∈ S') : A ∉ S := by
  intro a
  contradiction

theorem notinright_inleft
{K : Type}
{S S' : Finset K}
{A : K}
(SorS' : A ∈ S ∨ A ∈ S')
(h' : A ∉ S') : A ∈ S := by
  exact notright_left SorS' h'

-------------------
theorem inleft_notinrightIff

{K : Type}
{S S' : Finset K}
{A : K}
{inst : DecidableEq K}
(h : S ∩ S' = ∅)
(SorS' : A ∈ S ∨ A ∈ S')
: A ∈ S ↔  ¬(A ∈ S') := by
  constructor
  · exact inleft_notinright_finset h
  · exact notinright_inleft SorS'

theorem notinleft_inrightIff
{K : Type}
{S S' : Finset K}
{A : K}
{inst : DecidableEq K}
(h : S ∩ S' = ∅)
(SorS' : A ∈ S ∨ A ∈ S')
: A ∉ S ↔  A ∈ S' := by
  constructor
  · exact notinleft_inright SorS'
  · exact inright_notinleft_finset h

theorem inright_notinleftIff
{K : Type}
{S S' : Finset K}
{A : K}
{inst : DecidableEq K}
(h : S ∩ S' = ∅)
(SorS' : A ∈ S ∨ A ∈ S')
: A ∈ S' ↔  A ∉ S := by
  constructor
  · exact inright_notinleft_finset h
  · exact notleft_right SorS'

theorem notinright_inleftIff
{K : Type}
{S S' : Finset K}
{A : K}
{inst : DecidableEq K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
 : A ∉ S' ↔  A ∈ S := by
  constructor
  · exact notinright_inleft SorS'
  · exact inleft_notinright_finset h
