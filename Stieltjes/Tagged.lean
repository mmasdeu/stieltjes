import Stieltjes.Partition

open Real Topology Interval NonemptyInterval BigOperators Fintype Prepartition Finset
set_option autoImplicit false

open scoped Classical
noncomputable section

structure Tagging (I : MyInterval) extends Prepartition I where
  tag : MyInterval → ℝ
  tag_mem_Icc : ∀ J, tag J ∈ J.Closure

namespace Tagging

variable {I : MyInterval}

def Darboux (f : ℝ → ℝ) (α : ℝ → ℝ) (P : Tagging I) :=
  ∑ J in P.intervals, f (P.tag J) * (α J.upper - α J.lower)

def isPartition (P : Tagging I) := P.toPrepartition.isPartition

lemma key {P : Prepartition I} (f : ℝ → ℝ):
∑ x in P.intervals, f x.upper = ∑ u in P.upperset, f u := by
  unfold upperset
  rw [sum_image]
  exact fun x a y a_1 a_2 ↦ eq_if_eq_upper a a_1 a_2

lemma key' {P : Prepartition I} (f : ℝ → ℝ):
∑ x in P.intervals, f x.lower = ∑ l in P.lowerset, f l := by
  unfold lowerset
  rw [sum_image]
  exact fun x a y a_1 a_2 ↦ eq_if_eq_lower a a_1 a_2

lemma telescope {X Y : Finset ℝ} {f : ℝ → ℝ} :
∑ x in X, f x - ∑ x in Y, f x
= ∑ x in (X \ Y), f x - ∑ x in (Y \ X), f x := by
  simp [sub_eq_sub_iff_add_eq_add,←sum_union disjoint_sdiff, add_comm, union_comm]

theorem Darboux_const (c : ℝ) (α : ℝ → ℝ) (P : Tagging I) (h : P.isPartition) :
  Darboux (λ _ : ℝ ↦ c) α P = c * (α I.upper - α I.lower) := by
  unfold Darboux
  simp
  calc
  _ = ∑ x in P.intervals, c * α x.upper - ∑ x in P.intervals, c * α x.lower := by {rw [← @Finset.sum_sub_distrib]; congr; ext; ring}
  _ = ∑ x in P.intervals, ((c • α) · ) x.upper - ∑ x in P.intervals, ((c • α) · ) x.lower := by simp
  _ = ∑ u in P.upperset, c * α u - ∑ l in P.lowerset, c * α l := by {rw [key, key']; simp}
  _ = ∑ u in (P.upperset \ P.lowerset), c * α u - ∑ l in (P.lowerset \ P.upperset), c * α l := telescope
  _ = ∑ u in {I.upper}, c * α u - ∑ l in {I.lower}, c * α l := by rw [upper_minus_lower h, lower_minus_upper h]
  _ = c * (α I.upper - α I.lower) := by {simp; ring}
