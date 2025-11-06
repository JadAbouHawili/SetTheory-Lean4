import mathlibtesting.MathlibTheorems
-- set to finset
#check Set.toFinset
theorem memToFinset 
{K : Type}
{A:K}
  (Knight : Set K ) {finKnight : Fintype Knight}  (AKnight : A ∈ Knight) : A ∈ (Set.toFinset Knight) := by
  exact Set.mem_toFinset.mpr AKnight
