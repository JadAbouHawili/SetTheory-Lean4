
import mathlibtesting.MathlibTheorems

-- coe
#check Set.toFinset

#check Finset.toSet

    #check Finset.coe_inj
    #check Finset.coe_inter
    #check Finset.coe_empty
#check Set.mem_toFinset

      #check Finset.mem_coe
      #check Finset.coe_inj
      #check Finset.mem_coe.mpr 
      #check Finset.mem_coe.symm 
      #check Finset.mem_def.mp 
        #check Set.mem_toFinset
        #check Set.toFinset
#check Finset.coe_inj.symm
#check Finset.coe_inter
#check Finset.coe_empty

-- two options
#check Finset.toSet -- natural way
#check Set.toFinset -- needs fintype instance
#check Fintype


--#check Finset.toSet Finset.univ
--#check Finset.coe_inj
--#check Finset.coe_inj
#check Finset.toSet
-- very interesting
#check Set.toFinset_univ
#check Set.toFinset
example
{A B C : Type} 
{inst : DecidableEq Type}
{inst2 : Fintype Type}
: 2=2 := by
  have : Finset.univ = {A,B} ↔ Set.univ = {A,B} := by 
    constructor
    · intro Fu
      sorry
    · intro Fu
      -- what does this do
      rw [Finset.coe_inj.symm]
      sorry

example
{A B C : Type} 
{inst : DecidableEq Type}
{inst2 : Fintype Type}
: 2=2 := by
  have : (Finset.univ : Finset Type) = ↑(Set.univ : Set Type) := by 
    sorry
  rfl

