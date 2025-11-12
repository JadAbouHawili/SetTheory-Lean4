import settheory.setTheorems
import Mathlib.Tactic.Tauto

#check Set.mem_def

#check Set.ext_iff
#check Set.pair_comm
#check Finset.pair_comm

-- no need to use this because mem_insert_iff would where simp would solve A=A
#check Set.mem_insert_of_mem
#check Set.mem_insert_iff

theorem perm3 : ({A,B,C}:Set K) = ({C,B,A}:Set K) := by
  perm

example
  : ({A,B} : Set Type)={B,A} := by
{
  perm
}

-- need analysis of is_mem , is_mem as far as i remember is checking if the first element matches the claimed member and doing apply using Set.mem_insert to remove the top element and progress
#check Set.mem_insert_iff
#check Set.mem_insert
example : x ∈ ({A, B,C} : Set Type) ↔ x = A ∨ x = B ∨ x = C := by {
  -- replaces mem_iff_or
  simp [Set.mem_insert_iff]
}


#check Set
#check setOf

#check Set.insert

#check Set.insert_comm
#check Set.mem_insert

#check Set.mem_singleton_iff
#check Set.mem_singleton_of_eq

variable (K : Type)
variable (A B C : K)
example {inst : DecidableEq K} : ({A,B,C}:Finset K) = ({C,B,A}:Finset K) := by
  aesop
example {inst : DecidableEq K} : ({A,B}:Finset K) = ({B,A}:Finset K) := by
  aesop
