import settheory.MathlibTheorems
import settheory.logic
import settheory.auxiliary.singleton
import settheory.setTheorems


#check Finset.card_eq_one
#check Finset.card_le_one_iff
theorem two_in_card_eq_one {K : Type} {A B : K} {S : (Finset K)} (h : S.card =1) (AinS : A ∈ S) ( BinS : B ∈ S) : A=B := by
  rw [Finset.card_eq_one] at h
  have ⟨a,ha⟩ := h
  rw [ha] at AinS
  rw[ha] at BinS
  mem_finset at BinS
  mem_finset at AinS
  rw [←BinS] at AinS
  assumption
/-
  --cleaner
  have := Nat.le_of_eq h
  rw [Finset.card_le_one_iff] at this
  exact this AinS BinS
-/


#check Finset.singleton_subset_iff
#check Finset.subset_of_eq
#check Set.eq_singleton_iff_unique_mem
theorem full
{K : Type}
{A : K}
{S : Finset K}
{B : K}
(AinS: A ∈ S)
(One : S.card =1)
(AneB : A ≠ B)
: B ∉ S := by {
  by_contra BinS
  exact AneB (two_in_card_eq_one One AinS BinS)
}

theorem full3 {K : Type}

{A B C: K}
{inst : DecidableEq K}  {S : Finset K}
{inst2: Fintype K}
{all3 : ∀ (x : K), x = A ∨ x = B ∨ x = C}
  (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) : S = {A,B,C} := by
    have h : {A,B,C} ⊆ S := by
      intro a h
      mem_finset at h
      rcases h with eq|eq|eq
      repeat (rw [eq] ; assumption)
    have univ : {A,B,C} = Finset.univ := sorry
    rw [univ] at h
    rw [univ]
    exact Finset.univ_subset_iff.mp h
    /-
    apply Finset.Subset.antisymm
    · intro a
      intro aInKnave
      mem_finset
      exact all3 a
    · intro a aIn
      mem_finset at aIn
      rcases aIn with eq|eq|eq
      repeat (rw [eq] ; assumption)
    -/


theorem set_full3
{Inhabitant: Type}
{inst: DecidableEq Inhabitant}
{inst2: Fintype Inhabitant}
{A B C : Inhabitant}
{ S : Finset Inhabitant} (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) 

{all3 : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C}
: S = {A,B,C}
:= by
    apply full3
    assumption
    exact all3
    repeat assumption


#check mem_of_eq_singleton
theorem one_in_of_card_eq_one
{K : Type}
{inst : DecidableEq K}
{inst2 : Fintype K}
{A B C : K}
{S : Finset K}  (U : Finset.univ = {A,B,C}) (h : S.card = 1)
(AneB : A ≠ B)
(BneC : B ≠ C)
(AneC : A ≠ C)
: A ∈ S ∧ B ∉ S ∧ C ∉ S ∨ A ∉ S ∧ B ∈ S ∧ C ∉ S ∨ A ∉ S ∧ B ∉ S ∧ C ∈ S := by
  rw [Finset.card_eq_one] at h
  have ⟨a,h'⟩ := h 
  have U' : S ⊆ Finset.univ := by exact Finset.subset_univ S
  rw [U] at U'
  rw [h'] at U'
  simp at U'
  have : a ∈ S := by exact mem_of_eq_singleton h'
  aesop

  /-
  rw [card_eq_one_iff_singletons_univ A B C U ] at h
  rcases h with h_1|h_1
  · left
    constructor
    · exact mem_of_eq_singleton h_1
    · constructor
      ·         exact not_in_of_singleton h_1 (AneB.symm)
      · exact not_in_of_singleton h_1 (AneC.symm)

  -- similarly
  · rcases h_1 with h|h
    · right
      left
      constructor
      · exact not_in_of_singleton h AneB
      · constructor
        · exact mem_of_eq_singleton h
        · exact not_in_of_singleton h BneC.symm

    · right
      right
      constructor
      · exact not_in_of_singleton h AneC
      · constructor
        · exact not_in_of_singleton h BneC
        · exact mem_of_eq_singleton h
  -/

theorem all2_in_one_other_empty 
{K : Type}
{A B : K}
{inst : Fintype K} {inst2 : DecidableEq K}
{S S' : Finset K}
(h : S ∩ S' = ∅) (all : ∀ (x : K), x = A ∨ x = B) (hA : A ∈ S) (hB : B ∈ S)
: S' = ∅ := by 
  have : S = (Finset.univ) := by 
    have := (@univ_iff_all2 K inst inst2  ).mpr all
    rw [this]
    apply Finset.ext
    intro a
    constructor
    · intro aSprime
      mem_finset
      exact all a
    · intro h
      mem_finset at h
      rcases h with h|h <;> (rw[h] ; assumption)

  rw [this] at h
  rw [Finset.inter_comm] at h
  rw [Finset.inter_univ] at h
  assumption

  --by_contra nonemp
----  have := (not_iff_not.mpr Finset.not_nonempty_iff_eq_empty).mpr nonemp
  --rw [(not_iff_not.mpr Finset.not_nonempty_iff_eq_empty).symm] at nonemp

  --push_neg at nonemp
  ---- now use helper theorem
  --unfold Finset.Nonempty at nonemp 
  --have ⟨x,hx⟩ := nonemp 
  --rcases all x with h_1|h_2
  --· rw [h_1] at hx
  --  exact disjoint h hA hx 
  --· rw [h_2] at hx
  --  exact disjoint h hB hx

theorem all3_in_one_other_empty 
{K : Type}
{inst : DecidableEq K} {A B C : K} {S S' : Finset K}
{all3 : ∀ (x : K), x = A ∨ x = B ∨ x = C}
(hA : A ∈ S)
(hB : B ∈ S)
(hC : C ∈ S)
(h : S ∩ S' = ∅)
: S'=∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro x xInS'
  rcases all3 x with h_1|h_2
  · rw [h_1] at xInS'
    exact disjoint_finset h hA xInS'
  · rcases h_2 with h_3|h_4
    · rw [h_3] at xInS'
      exact disjoint_finset h hB xInS'
    · rw [h_4] at xInS'
      exact disjoint_finset h hC xInS'

#check Finset.Subset.antisymm
  #check Set.eq_of_subset_of_subset
  #check Finset.eq_of_superset_of_card_ge
  #check Finset.eq_of_subset_of_card_le
  #check Finset.card_le_univ
  #check Finset.subset_univ

theorem S_union_S'_eq_univ
{K : Type}
{inst : DecidableEq K} {inst2 : Fintype K}
{S S' : Finset K}
(Or : ∀ (x : K), x ∈ S ∨ x ∈ S')
: S ∪ S' = Finset.univ := by  
  ext a
  simp
  exact Or a

theorem S_union_S'_eq_univ_explicit
{K : Type}
{inst : DecidableEq K} {inst2 : Fintype K}
{A B C : K} {S S' : Finset K}
(Or : ∀ (x : K), x ∈ S ∨ x ∈ S')
(all3 : ∀ (x : K), x = A ∨ x = B ∨ x = C)
: S ∪ S' = {A,B,C} := by
  have : S ∪ S' = Finset.univ := by apply S_union_S'_eq_univ Or
  rw [this]
  exact univ_iff_all.mpr all3


#check Finset.empty_union
theorem empty_eq_all 
{K : Type}
{inst : DecidableEq K} {A B C : K} {S S' : Finset K}
{inst2 : Fintype K}
{all3 : ∀ (x : K), x = A ∨ x = B ∨ x = C}
{Or : ∀ (x : K), x ∈ S ∨ x ∈ S'}
(Semp : S = ∅) : S' ={A,B,C} := by 
  have : S ∪ S' = {A,B,C} :=by 
    (expose_names; apply S_union_S'_eq_univ_explicit Or all3)
    assumption
  simp [Semp] at this
  assumption

theorem all3_in_one_other_eq_all 
{K : Type}
{inst : DecidableEq K} {A B C : K} {S : Finset K}
{all3 : ∀ (x : K), x = A ∨ x = B ∨ x = C}
(hA : A ∈ S)
(hB : B ∈ S)
(hC : C ∈ S)
: S={A,B,C} := by 
  ext a
  mem_finset
  constructor
  · aesop
  · intro h'
    rcases all3 a with h|h|h
    repeat rw [h] ; assumption

#check Finset.ext_iff
theorem everyone_in_set_eq 
{K : Type}
{inst : DecidableEq K} {S : Finset K} {A B C : K} 
  (all3 : ∀ (x : K), x = A ∨ x = B ∨ x = C) 
  : (A ∈ S ∧ B ∈ S ∧ C ∈ S) ↔ (S = ({A,B,C} : Finset K) ) := by 
  constructor
  · intro allS
    ext a
    constructor
    · intro aKn
      mem_finset
      exact all3 a
    · intro aIn
      mem_finset at aIn
      rcases aIn with h|h|h
<;> rw [h]
      · exact allS.left
      · exact allS.right.left
      · exact allS.right.right

  · intro SEveryone
    rw [SEveryone]
    aesop

theorem all_in_one
  {Inhabitant : Type}
  {inst : DecidableEq Inhabitant}
  {A B C : Inhabitant}
  {S : Finset Inhabitant} 
  {all3 : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C}
  (hA : A ∈ S)
  (hB : B ∈ S)
  (hC : C ∈ S)
  : S = {A,B,C}
  := by
    #check Finset.eq_of_subset_of_card_le
    exact (everyone_in_set_eq all3).mp ⟨hA,hB,hC⟩

theorem not_all_in_one_in_other 
{K : Type}
{inst : DecidableEq K} {A B C : K} {S S' : Finset K}
{inst2 : Fintype K}
(all : ∀ (x : K), x = A ∨ x = B ∨ x = C)
(Or : ∀ (x : K), x ∈ S ∨ x ∈ S')
(notall : S ≠ ({A,B,C} : Finset K)) : S' ≠ ∅ := by
  intro S'emp
  -- make into theorem
  have : S ∪ S' = {A,B,C} := by
    (expose_names; apply S_union_S'_eq_univ_explicit Or all)
    assumption
  simp [S'emp] at this
  contradiction

theorem not_eq_singleton_of_not_mem
{K : Type}
{A : K} {S : Finset K} (h : A ∉ S) : S ≠ {A} := by
  intro eq
  have := mem_of_eq_singleton eq
  contradiction

theorem already_full 
{K : Type}
{A B : K}
{S : Finset K}
(hA : A ∈ S)
(either_single : S={A} ∨ S={B})
(AneB : A ≠ B)
: S={A} := by
  rcases either_single with h|h
  assumption

  rw [h] at hA
  rw [Finset.mem_singleton] at hA
  exfalso
  contradiction

theorem full2_helper
{K : Type}
{A B C : K}
(S : Finset K)
{inst : DecidableEq K}
(pair : S = {A,B})

(AneB : A ≠ B)
(BneC : B ≠ C)
(AneC : A ≠ C)
: C ∉ S := by {
  intro CinS
  rw [pair] at CinS
  mem_finset at CinS

  cases CinS
  symm at AneC
  contradiction
  symm at BneC
  contradiction
}

theorem full2
{K : Type}
{A B C : K}
(S : Finset K)
{inst : DecidableEq K}
{inst2 : Fintype K}
(AinS : A ∈ S)
(BinS : B ∈ S)
(Two : S.card = 2)
(AneB : A ≠ B)
(BneC : B ≠ C)
(AneC : A ≠ C)
(all : ∀(x:K),x=A ∨ x=B ∨ x=C)
: C ∉ S := by {
  rw [Finset.card_eq_two] at Two
  have ⟨x,y,_,main⟩ := Two
  #check full2_helper
  -- full2_helper not as helpful as anticipated
  sorry
  /-
  #check Finset.card_le_two
  intro CinS
  #check Finset.card_eq_two
  have two := Two
  rw [Finset.card_eq_two] at Two

  --have ⟨x,y,xney,Seqxy⟩ := Two
  --rw [Seqxy] at AinS  
  --rw [Seqxy] at BinS  
  --rw [Seqxy] at CinS  

  have : S.card=3 := by 
    rw [Finset.card_eq_three]
    use A
    use B
    use C
    constructor
    assumption
    constructor
    assumption
    constructor
    assumption
    #check univ_iff_all 
    #check Finset.eq_iff_card_le_of_subset
    rw [(univ_iff_all).symm] at all
    have : {A,B,C} ⊆ S := by
      intro x
      intro hx
      rw [mem_iff_or_finset] at hx
      rcases hx  with h|h
      rw [←h] at AinS
      assumption
      rcases h with h_1|h_1
      rw[h_1] 
      assumption
      rw[h_1] 
      assumption

    #check Finset.eq_of_subset_of_card_le
    --#check Finset.card_le_of_subset
    apply Finset.eq_of_subset_of_card_le
    rw [←all]
    apply Finset.subset_univ S
    --#check Finset.card_le_of_subset
    -- make my own theorem which would avoid using Finset.card_le_of_subset
    apply Finset.card_le_card
    assumption
    --sorry
  rw [two] at this
  contradiction
-/
}
