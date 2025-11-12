
import settheory.MathlibTheorems
import settheory.auxiliary.univ

theorem is_singleton
{K : Type}
{A : K} {S : Finset K}
(AinS : A ∈ S) (OneS : S.card = 1 )
: S={A} := by
/- simpler solution
  have ⟨a,hA⟩  := Finset.card_eq_one.mp OneS
  rw [hA] at AinS
  rw [Finset.mem_singleton] at AinS
  rw [AinS]
  assumption
  -/
  have OneS2 := Finset.card_eq_one.mp OneS
  #check Finset.nontrivial_iff_ne_singleton
  #check Finset.one_lt_card_iff_nontrivial
  #check Finset.Nontrivial

  by_contra ne_singleton
  push_neg at ne_singleton
  have := (Finset.nontrivial_iff_ne_singleton AinS).mpr ne_singleton
  rw [Finset.one_lt_card_iff_nontrivial.symm] at this
  rw [OneS] at this
  contradiction

/-
  have OneS2 := Finset.card_eq_one.mp OneS
  #check Finset.nontrivial_iff_ne_singleton
  #check Finset.one_lt_card_iff_nontrivial
  #check Finset.Nontrivial

  by_contra ne_singleton
  push_neg at ne_singleton
  have := (Finset.nontrivial_iff_ne_singleton AinS).mpr ne_singleton
  unfold Finset.Nontrivial at this
  unfold Set.Nontrivial at this
  have ⟨x,hx,y,hy,xney⟩ := this 
  #check full
  #check card_eq
  #check Finset.nontrivial_iff_ne_singleton 
  exact xney (card_eq OneS hx hy )
  -/

theorem singleton_iff_exists 

{K : Type}
{S : Finset K}
{B : K} (BinS : B ∈ S): S={B} ↔ ∃x, S={x} := by
  constructor
  · intro singleton
    use B
  · rw [Finset.card_eq_one.symm] 
    exact is_singleton BinS


theorem full_singleton  
{K : Type}
{S : Finset K} 
{A B : K}
(singleton : S = { B })
(AinS: A ∈ S)
(AneB : A ≠ B)
: False := by {
   rw [singleton] at AinS 
   have AeqB := Finset.mem_singleton.mp AinS
   contradiction
---
  --#check Finset.eq_singleton_iff_unique_mem
  --have exist: ∃x, S={x} := by use B
  --rw [Finset.card_eq_one.symm] at exist 
  --#check card_eq
  --exact AneB (card_eq exist AinS

  --exact AneB (card_eq (by rw [Finset.card_eq_one] ; use B) AinS (by rw [singleton] ; exact Finset.mem_singleton.mpr rfl))

  --by_contra BinS
  --exact AneB (card_eq One AinS BinS)
}


#check Finset.eq_singleton_iff_unique_mem
#check Finset.mem_singleton
#check Finset.mem_inter_of_mem
theorem mem_of_eq_singleton 
{K : Type}
{S : Finset K} {A : K} (h : S={A}) : A ∈ S := by 
  rw [h]
  is_mem
  --exact (Finset.eq_singleton_iff_unique_mem.mp h).left

  /-
  symm at h
  have := Finset.subset_of_eq h
  exact Finset.singleton_subset_iff.mp this
  -/
theorem singleton_iff_card_eq_one 
{K : Type}
{S : Finset K}
{B : K}
{all1 : ∀(x:K), x=B}
: S={B} ↔ S.card=1 := by 
  constructor
  · intro singleton
    rw [Finset.card_eq_one]
    #check Classical.not_forall_not
    use B
  · intro One
    rw [Finset.card_eq_one] at One
    have ⟨x,hx⟩ := One
    have := all1 x
    rw [this] at hx
    rw [Finset.eq_singleton_iff_unique_mem] 
    constructor
    #check mem_of_eq_singleton  
    exact mem_of_eq_singleton hx
    intro y
    intro yinS
    have := all1 y
    assumption

theorem not_in_of_singleton  
{K : Type}
{S : Finset K} 
{A B : K}
(singleton : S={B})
(AneB : A ≠ B)
: A ∉ S := by {
  by_contra AinS
  exact full_singleton singleton AinS AneB
  --exact AneB (card_eq (by rw [Finset.card_eq_one] ; use B) AinS (by rw [singleton] ; exact Finset.mem_singleton.mpr rfl))

  --by_contra BinS
  --exact AneB (card_eq One AinS BinS)
}

  #check Finset.subset_of_eq
  --#check Finset.card_eq_of_equiv
  #check Finset.card_le_card
  --have := Finset.card_eq_of_equiv (by exact Equiv.setCongr singleton )
  #check Finset.nontrivial_iff_ne_singleton
-- A ∈ S and S.card=1 , so S={A}
theorem eq_singleton_card_one 

{K : Type}
{A : K} {S : Finset K } 
(singleton : S={A}) : S.card=1 := by 
  rw [Finset.card_eq_one]
  use A
  --#check congrArg
  --have : S.card=({A} : Finset K).card  := by
  --  exact congrArg Finset.card singleton
  --rw [this]
  --exact rfl

/-
  #check Finset.subset_of_eq
--  #check Finset.card_le_of_subset
  #check Finset.card_eq_of_equiv
  --have := Finset.card_eq_of_equiv (by exact Equiv.setCongr singleton )
  have Sin := Finset.subset_of_eq singleton
  have Sless := (Finset.eq_iff_card_le_of_subset Sin).mp
 -- have Sless := Finset.card_le_of_subset Sin
  have Aless:  (({A}:Finset K).card) ≤ S.card  := by 
     exact (Finset.eq_iff_card_ge_of_superset Sin).mpr (id (Eq.symm singleton))
  #check Finset.eq_iff_card_le_of_subset
  #check Finset.card_le_one_iff_subset_singleton
--  have Aless := (Finset.eq_iff_card_le_of_subset Ain).mp

  exact (Nat.le_antisymm Aless Sless).symm


  --rw [(Finset.nontrivial_iff_ne_singleton).symm] at ne_singleton
-/


theorem card_eq_one_iff_singletons
{K : Type}
{A B C : K} {S : Finset K}
(all : ∀(x : K), x = A ∨ x = B ∨ x = C)
: S.card =1 ↔  S = {A} ∨ S = {B} ∨ S = {C}
  := by 
  constructor
  · intro OneS
    rw [Finset.card_eq_one] at OneS
    have ⟨x,hx⟩ := OneS
    have Ors := all x
    rcases Ors with h_1|h_2
    · rw [h_1] at hx
      -- A ∈ S and S.card=1 , so S={A}
      #check full_singleton
      left
      assumption
    · rcases h_2 with h_11|h_22
      -- identical reasoning
      · right
        left
        rw [h_11] at hx
        assumption

      · right
        right
        rw [h_22] at hx
        assumption

  · intro singletons
    rcases singletons with h_1|h_2
    ·
      exact eq_singleton_card_one h_1
    · rcases h_2 with h_11|h_22
      · exact eq_singleton_card_one h_11
      · exact eq_singleton_card_one h_22

theorem card_eq_one_iff_singletons_univ
{K : Type}
  (A B C : K) {S : Finset K} 
(U : (Set.univ)  = ({A,B,C} : Set K))
--(all : ∀(x : K), x = A ∨ x = B ∨ x = C)
: S.card = 1 ↔ S = {A} ∨ S = {B} ∨ S = {C} := by
  have all := univ_or.mp U
  exact card_eq_one_iff_singletons all


theorem singleton_iff_card_eq_one3 
{Inhabitant : Type}
{A B C : Inhabitant}
{S : Finset Inhabitant}
{all : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C}
: S = {A} ∨ S = {B} ∨ S = {C} ↔ S.card = 1 := by
    constructor
    intro eq
    rw [Finset.card_eq_one]
    rcases eq with h|h|h
    use A ; use B ; use C

    intro Scard
    rw [Finset.card_eq_one] at Scard
    have ⟨a,singleton⟩ := Scard
    rcases all a with h|h|h

    rw [h] at singleton
    left
    assumption

    rw [h] at singleton
    right ; left
    assumption

    rw [h] at singleton
    right ; right
    assumption


theorem not_eq_singleton_already_full
{K : Type}
{A B: K}
{Knave : Finset K}
(AneB : A ≠ B)
(AKnave : A ∈ Knave)

: Knave ≠ {B} := by
        intro knaveB
        rw [knaveB] at AKnave
        mem_finset at AKnave
        contradiction
