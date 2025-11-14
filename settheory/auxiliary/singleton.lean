
import settheory.MathlibTheorems
import settheory.auxiliary.univ
set_option linter.style.multiGoal false

theorem card_eq_one_of_eq_singleton
{K : Type}
{A : K} {S : Finset K }
(singleton : S = {A}) : S.card=1 := by
  rw [singleton]
  rfl


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



#check Finset.eq_singleton_iff_unique_mem
#check Finset.mem_singleton
#check Finset.mem_inter_of_mem
theorem mem_of_eq_singleton 
{K : Type}
{S : Finset K} {A : K} (h : S={A}) : A ∈ S := by 
  rw [h]
  mem_finset
  --exact (Finset.eq_singleton_iff_unique_mem.mp h).left

  /-
  symm at h
  have := Finset.subset_of_eq h
  exact Finset.singleton_subset_iff.mp this
  -/

#check Classical.not_forall_not
theorem singleton_iff_card_eq_one 
{K : Type}
{S : Finset K}
{B : K}
{all1 : ∀ (x : K), x = B}
: S={B} ↔ S.card=1 := by
  constructor
  · intro singleton
    exact card_eq_one_of_eq_singleton singleton
  · intro One

    rw [Finset.eq_singleton_iff_unique_mem] 
    constructor
    rw [Finset.card_eq_one] at One
    have ⟨x,hx⟩ := One
    have := all1 x
    rw [this] at hx
    exact mem_of_eq_singleton hx
    intro y yinS
    exact all1 y


  #check Finset.subset_of_eq
  --#check Finset.card_eq_of_equiv
  #check Finset.card_le_card
  --have := Finset.card_eq_of_equiv (by exact Equiv.setCongr singleton )
  #check Finset.nontrivial_iff_ne_singleton
-- A ∈ S and S.card=1 , so S={A}

  #check Finset.subset_of_eq
  #check Finset.le_card_iff_exists_subset_card
  #check Finset.card_eq_iff_eq_univ
  #check Equiv.setCongr
  #check Finset.eq_iff_card_le_of_subset
  #check (Finset.nontrivial_iff_ne_singleton)
#check congrArg

theorem card_eq_one_iff_singletons
{K : Type}
{A B C : K} {S : Finset K}
(all : ∀ (x : K), x = A ∨ x = B ∨ x = C)
: S.card =1 ↔  S = {A} ∨ S = {B} ∨ S = {C}
  := by
  constructor
  · intro OneS
    rw [Finset.card_eq_one] at OneS
    have ⟨x,hx⟩ := OneS
    have Ors := all x
    rcases Ors with h_1|h_2
    · rw [h_1] at hx
      left
      assumption
    · rcases h_2 with h_11|h_22
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
      #check Finset.card_singleton
      rw [h_1]
      apply Finset.card_singleton
    · rcases h_2 with h_11|h_22
      · exact card_eq_one_of_eq_singleton h_11
      · exact card_eq_one_of_eq_singleton h_22

theorem card_eq_one_iff_singletons_univ
{K : Type}
  (A B C : K) {S : Finset K} 
(U : (Set.univ) = ({A,B,C} : Set K))
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
    ·
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
{A B : K}
{Knave : Finset K}
(AneB : A ≠ B)
(AKnave : A ∈ Knave)
: Knave ≠ {B} := by
 intro knaveB
 rw [knaveB] at AKnave
 mem_finset at AKnave
 contradiction

#check Finset.eq_singleton_iff_unique_mem
theorem full_singleton
{K : Type}
{S : Finset K} 
{A B : K}
(singleton : S = { B })
(AinS : A ∈ S)
(AneB : A ≠ B)
: False := by {
  rw [singleton] at AinS
  mem_finset at AinS
  contradiction
}

theorem not_in_of_singleton  
{K : Type}
{S : Finset K} 
{A B : K}
(singleton : S = {B})
(AneB : A ≠ B)
: A ∉ S := by {
  intro AinS
  exact full_singleton singleton AinS AneB
}
