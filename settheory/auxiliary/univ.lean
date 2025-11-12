import settheory.MathlibTheorems


#check Finset.univ_inter

-- go from set to finset

theorem univ_iff_all {K : Type} {inst : Fintype K} {inst2 : DecidableEq K} {A B C : K}
: Finset.univ = ({A,B,C} : Finset K) ↔  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by 

  constructor
  · intro U x
    have this:= Finset.mem_univ x
    rw [U] at this
    mem_finset at this
    assumption
  · --aesop
    intro U
    ext a
    mem_finset
    simp
    exact U a

theorem univ_iff_all2
{K : Type} {inst : Fintype K} {inst2 : DecidableEq K}
{A B : K} : Finset.univ = ({A,B} : Finset K) ↔  ∀ (x : K), x = A ∨ x = B := by

  constructor
  -- repeated reasoning, make into a theorem or tactic
  ·
    intro U
    intro x
    have xinU := Finset.mem_univ x
    rw [U] at xinU
    mem_finset at xinU
    assumption

  · intro all
    apply Finset.eq_of_subset_of_card_le
    intro x
    intro hx
    rcases all x with h|h
    · rw [h]
      is_mem
    · rw [h]
      is_mem
    apply Finset.card_le_card
    apply Finset.subset_univ

#check Finset.univ_subset_iff
#check Finset.subset_univ
#check Set.subset_univ
theorem set_subset_univ_explicit
{Inhabitant : Type}
{inst: DecidableEq Inhabitant}
{A B C : Inhabitant}
 {S : Finset Inhabitant}
 {inst : Fintype Inhabitant}
 (all3 : ∀(x : Inhabitant) , x = A ∨ x = B ∨ x = C)
: S ⊆ ({A,B,C} : Finset Inhabitant) := by 

  rw [(univ_iff_all).symm] at all3
  rw [←all3]
  exact Finset.subset_univ S
/-
-- proof without going into using univ theorems , keep it , useful reasoning
    have : S ⊆ {A,B,C} := by
      intro x
      intro xK
      rcases all3 x with h_1|h_1
      · rw [h_1]
        is_mem
      · rcases h_1 with h_2|h_2
        · rw [h_2]
          is_mem
        · rw [h_2]
          is_mem
    assumption
-/

macro "by_universe" : tactic =>
  `(tactic| (apply set_subset_univ_explicit; assumption))

-- replace to mem_set logic, prefer mem_set
---------------------------------------
-- Set


theorem forward
{K : Type}
{A B C : K} (all3 : ∀ (x : K), x = A ∨ x = B ∨ x = C) : (@Set.univ K)  = {A,B,C} := by 
  symm
  exact Set.eq_univ_of_univ_subset fun ⦃a⦄ a_1 => by exact all3 a
/-
  #check Set.univ_subset_iff
  #check Set.eq_univ_of_univ_subset
  apply Set.eq_of_subset_of_subset

  --exact fun ⦃a⦄ a_1 => all3 a
  · intro x
    intro xU
    exact all3 x

  · intro x
    rw [eq_true (Set.mem_univ x)]
    rw [implies_true]
    trivial

    --exact fun _ => trivial
    ---
    --intro x
    --intro xABC
    --exact trivial
    -/

theorem backward
{K : Type}
{A B C : K} (h : (Set.univ)  = ({A,B,C} : Set K) ):  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by 
  intro x
  have : x ∈ Set.univ := by trivial
  rw [h] at this
  exact this

#check Set.eq_univ_of_univ_subset
#check Set.eq_of_forall_subset_iff
#check Set.eq_of_forall_subset_iff
theorem univ_or
{K : Type}
{A B C : K} :  (Set.univ)  = ({A,B,C} : Set K)  ↔  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by 
  constructor
  exact fun a x => backward a x

  aesop?
  --exact forward

#check iff_mpr_iff_true_intro
#check iff_of_true
#check Set.eq_univ_of_univ_subset
example
{K : Type}
  (A B C : K) (all3 : ∀ (x : K), x = A ∨ x = B ∨ x = C) : @Set.univ K = {A,B,C} := by

  --ext x
  --constructor
  --· intro xUniv
  --  exact all3 x
  --· exact fun a => trivial

  --aesop

  --ext x
  --constructor
  --aesop
  --aesop

  ext y
  apply iff_of_true
  trivial
  exact all3 y

  --simp_all
  --simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff]
  --aesop?

---------------------------------------------------------

-- try using Set.univ as an axiom instead and see if there are any advantages

theorem every_elt_in_univ 
{K : Type}
{inst : DecidableEq K} {A B C : K} 
{inst2 : Fintype K}
{all : ∀ (x : K), x = A ∨ x = B ∨ x = C}
: ∀(x:K), x ∈ ({A,B,C} : Finset K) := by

  --aesop
  --intro x
  --mem_finset
  --exact all x


  have : Finset.univ = {A,B,C} := univ_iff_all.mpr all
  rw [←this]
  intro x
  exact Finset.mem_univ x
