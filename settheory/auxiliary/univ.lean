import mathlibtesting.MathlibTheorems

example
{K : Type}
  (A B C: K) (all3 : ∀(x : K), x = A ∨ x = B ∨ x = C) : @Set.univ K = {A,B,C} := by
  unfold Set.univ
  exact (Set.eq_univ_of_univ_subset fun ⦃a⦄ a_1 => all3 a).symm

  --apply Set.ext
  --intro x
  --constructor
  --sorry
  --sorry

  --· intro xUniv
  --  by_contra
  --· exact fun a => trivial





#check instDecidableEqBool

#check Finset.univ_inter
#check Finset.empty_inter
#check Finset.Nonempty
#check Finset.empty
#check not_iff_not.mpr Finset.not_nonempty_iff_eq_empty
#check Finset.not_nonempty_iff_eq_empty.mpr

-- go from set to finset
theorem univ_iff_all {K : Type} {inst : Fintype K} {inst2 : DecidableEq K} {A B C : K}   : Finset.univ = ({A,B,C} : Finset K) ↔  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by 

  constructor
  · intro U
    intro x
    have this:= Finset.mem_univ x
    rw [U] at this
    mem_finset at this
    assumption
  · intro U
    apply Finset.ext
    intro a
    constructor
    · intro aU
      rcases U a with h|h
      · rw [h]
        exact Finset.mem_insert_self A {B, C}
      · rcases h with h_1|h_1
        · rw [h_1]
          is_mem
        · rw [h_1]
          is_mem
    · exact fun a_1 => Finset.mem_univ a



theorem univ_iff_all2
{K : Type}
{inst : Fintype K} {inst2 : DecidableEq K} {A B : K}   : Finset.univ = ({A,B} : Finset K) ↔  ∀ (x : K), x = A ∨ x = B := by
  constructor
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
  have : x ∈ Set.univ := by exact trivial
  rw [h] at this
  exact this

theorem univ_or
{K : Type}
{A B C : K} :  (Set.univ)  = ({A,B,C} : Set K)  ↔  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by 
  constructor
  exact fun a x => backward a x
  #check forward
  exact forward




















--------------------------------------------------------------------------------------------------------------

-- can use to intuitively explain other things like x ∈ {A} means x=A etc.. start from it and then say more generally ...
-- mem1_iff_or for x ∈ {A}
-- mem2_iff_or for x ∈ {A,B} , can use repeat rw way

-- try using Set.univ as an axiom instead and see if there are any advantages
#check Finset.univ

theorem mem_iff_or 
{K : Type}
(A B C: K) (x : K) : x ∈ ({A,B,C} : Set K) ↔  x = A ∨ x =B ∨ x = C := by
  constructor
  · intro xIn
    exact xIn
  · intro Ors
    exact Ors

theorem mem2_iff_or_finset
{K : Type}
{inst : DecidableEq K} 
{A B : K} {x : K} : x ∈ ({A,B} : Finset K) ↔  x = A ∨ x =B := by
  constructor
  · intro xIn
    mem_finset at xIn
    assumption
  · intro xIn
    mem_finset
    assumption

theorem mem_iff_or_finset
{K : Type}
{inst : DecidableEq K}
{A B C: K} {x : K} : x ∈ ({A,B,C} : Finset K) ↔  x = A ∨ x =B ∨ x = C := by
  constructor
  · intro xIn
    mem_finset at xIn
    assumption
  · intro Ors
    mem_finset
    assumption





theorem univ_set_iff_or 
{K : Type}
{x : K}
{inst : DecidableEq K} {A B C : K} 
{inst3 : DecidableEq Bool}
{inst2 : Fintype K}
: (x = A ∨ x = B ∨ x = C) ↔ x ∈ ({A,B,C} : Finset K) := by 
  #check univ_iff_all
  --rw [univ_iff_all inst2 inst] 
  constructor 
  · 
    #check mem_iff_or
    intro ors
    have := (@mem_iff_or_finset _ inst _ _ _ x).mpr ors
    assumption
    --exact fun a ↦ (fun {K} {inst} {A B C x} ↦ mem_iff_or_finset.mpr) a

    --intro all
    --have U : Finset.univ = {A, B, C} := (univ_iff_all inst2 inst).mpr (all)
    --rw [←U]
    --exact Finset.mem_univ x
  · intro mem
    exact mem_iff_or_finset.mp mem



theorem every_elt_in_univ 
{K : Type}
{inst : DecidableEq K} {A B C : K} 
{inst2 : Fintype K}
{all : ∀ (x : K), x = A ∨ x = B ∨ x = C}
: ∀(x:K), x ∈ ({A,B,C} : Finset K) := by 
  --have : Finset.univ = {A,B,C} := univ_iff_all.mpr all
  rw [(univ_iff_all).symm] at all
  rw [←all]
  intro x
  exact Finset.mem_univ x
