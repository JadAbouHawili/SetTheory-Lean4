import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic.Have

infixr:35 " and " => And
infixr:30 " or  "  => Or

--hypothesis
macro "remove_top" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic |  rw[ Finset.subset_insert_iff_of_not_mem] at $t1 <;> try assumption)
--goal
macro "remove_top" : tactic =>
do`(tactic |  rw[ Finset.subset_insert_iff_of_not_mem] <;> try assumption)

macro "perm" : tactic => `(tactic| (ext ; aesop))

--hypothesis
macro "remove_top" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic |  rw[ Set.subset_insert_iff_of_not_mem] at $t1 <;> try assumption)
--goal
macro "remove_top" : tactic =>
do`(tactic |  rw[ Set.subset_insert_iff_of_not_mem] <;> try assumption)


macro "mem_finset": tactic =>
  do`(tactic| repeat simp only [Finset.mem_insert,Finset.mem_singleton,true_or,or_true] )

macro "mem_finset" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
  do`(tactic| repeat simp only [Finset.mem_insert,Finset.mem_singleton] at $t1)

#check Set.mem_singleton_iff
#check Set.mem_singleton
#check Set.mem_insert
#check Finset.mem_singleton

#check Set.mem_singleton_iff
#check Set.mem_insert_iff
macro "mem_set": tactic =>
  do`(tactic| repeat simp only [Set.mem_insert_iff,Set.mem_singleton_iff,true_or,or_true] )
macro "mem_set" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
  do`(tactic| repeat simp only [Set.mem_insert_iff,Set.mem_singleton_iff,true_or,or_true] at $t1)

--  a ∈ {a}
#check Finset.mem_singleton_self
-- a ∈ insert a s
#check Finset.mem_insert_self
-- a ∈ s → a ∈ insert b s
#check Finset.mem_insert_of_mem
