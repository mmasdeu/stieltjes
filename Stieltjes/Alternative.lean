import Mathlib.Tactic
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Interval

open Real Topology Interval NonemptyInterval BigOperators Fintype

set_option autoImplicit false

open scoped Classical
noncomputable section

example (a:ℝ)(h: a< a): False := by exact (lt_self_iff_false a).mp h

/-- A nonempty interval -/
@[ext 990]
structure MyInterval where
  (lower upper : ℝ)
  (lower_lt_upper : lower < upper)

namespace MyInterval

variable (I J : MyInterval)

instance : Inhabited (MyInterval) :=
  ⟨⟨0, 1, zero_lt_one⟩⟩

instance : Membership ℝ (MyInterval) :=
⟨fun x I ↦ x ∈ Set.Ioc I.lower I.upper⟩

theorem mem_def (I : MyInterval) (x : ℝ) : x ∈ I ↔ x ∈ Set.Ioc I.lower I.upper := by rfl

theorem upper_mem (I : MyInterval) : I.upper ∈ I := by
  rw[mem_def, @Set.right_mem_Ioc]
  exact I.lower_lt_upper

theorem le_lower_non_mem (I : MyInterval) (x:ℝ) (h: x ≤ I.lower):
x ∉ I := by
  intro H
  rw [mem_def] at H
  exact ((lt_iff_not_ge I.lower x).mp H.1 ) h

theorem gt_upper_non_mem (I : MyInterval) (x:ℝ) (h: I.upper < x):
x ∉ I := by
  intro H
  rw [mem_def] at H
  exact ((lt_iff_not_ge I.upper x).mp h) H.2

instance CoeSet : Coe (MyInterval) (Set ℝ) := ⟨λ I ↦ {x | x ∈ I}⟩

instance : LE (MyInterval) :=
  ⟨fun I J ↦ ∀ {x}, x ∈ I → x ∈ J⟩

@[simp]
theorem le_def (I J : MyInterval) : I ≤ J ↔ ∀ x ∈ I, x ∈ J := Iff.rfl

theorem le_extr  (I J : MyInterval) : I ≤ J ↔ I.upper ≤ J.upper ∧ J.lower ≤ I.lower :=
  (Set.Ioc_subset_Ioc_iff (I.lower_lt_upper))

@[ext]
theorem eq_iff' (I J : MyInterval) (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J:= by
  rw [MyInterval.ext_iff I J ]
  have hh1 := (le_extr I J).mp (fun {x} ↦ (h x).mp)
  have hh2 := (le_extr J I).mp (fun {x} ↦ (h x).mpr )
  exact ⟨le_antisymm_iff.mpr ⟨hh2.2, hh1.2⟩,le_antisymm_iff.mpr ⟨hh1.1, hh2.1⟩⟩

instance partialOrder : PartialOrder (MyInterval) where
  le := (· ≤ ·)
  le_refl := by
    simp
    done
  le_trans := by
    intro I J K hIJ hJK
    simp at hIJ hJK
    tauto
  le_antisymm := by
    intro I J hIJ hJI
    simp at hIJ hJI
    ext x
    tauto

def Disjoint (I J : MyInterval) : Prop := (I : Set ℝ) ∩ J = ∅

def Closure (I: MyInterval) := Set.Icc I.lower I.upper

end MyInterval

@[ext]
structure Prepartition (I : MyInterval) where
  intervals : Finset MyInterval
  le_of_mem' : ∀ J ∈ intervals, J ≤ I
  pairwiseDisjoint : Set.Pairwise (↑intervals) (MyInterval.Disjoint)

namespace Prepartition

variable {I : MyInterval}

instance : Membership MyInterval (Prepartition I):=
  ⟨fun J P ↦ J ∈ P.intervals⟩

theorem injective_intervals : Function.Injective (intervals : Prepartition I → Finset (MyInterval)) := by
  rintro ⟨s₁, h₁, h₁'⟩ ⟨s₂, h₂, h₂'⟩ (rfl : s₁ = s₂)
  rfl

theorem upper_le_upper_I {P : Prepartition I} {J: MyInterval} (h : J ∈ P.intervals) : J.upper ≤  I.upper := 
  ((MyInterval.le_extr J I).mp (P.le_of_mem' J h)).1

theorem lower_I_le_lower {P : Prepartition I} {J: MyInterval} (h : J ∈ P.intervals) : I.lower ≤ J.lower := by
  apply ((MyInterval.le_extr _ _).mp _).2; exact P.le_of_mem' J h

section

variable {P : Prepartition I} {J1 J2 : MyInterval}
(hJ1: J1 ∈ P.intervals) (hJ2: J2 ∈ P.intervals)

theorem eq_if_common_point {x : ℝ} (hx1 : x ∈ J1) (hx2 : x ∈ J2)
: J1 = J2 := by
  by_contra H
  have ex : x∈ (J1 : Set ℝ)∩J2 := Set.mem_inter hx1 hx2
  rw [ P.pairwiseDisjoint hJ1 hJ2 H ] at ex
  exact ex

theorem eq_if_le (h : J1 ≤ J2) : J1 = J2 := by
  by_contra H
  have ex1 : J1.upper ∈ J1 := MyInterval.upper_mem J1
  have ex :  J1.upper ∈ (J1 : Set ℝ) ∩ J2 :=Set.mem_inter ex1 (h ex1)
  rw [ P.pairwiseDisjoint hJ1 hJ2 H ] at ex
  exact ex

theorem eq_if_eq_lower (hl : J1.lower = J2.lower) :
 J1 = J2 := by
  rcases le_or_gt J1.upper J2.upper with h | h
  · have: J1 ≤ J2:= (MyInterval.le_extr J1 J2).mpr ⟨h, le_of_eq hl.symm⟩
    exact eq_if_le hJ1 hJ2 this
  · have: J2 ≤ J1:= (MyInterval.le_extr J2 J1).mpr ⟨le_of_lt h, le_of_eq hl⟩
    exact (eq_if_le hJ2 hJ1 this).symm

theorem eq_if_eq_upper (hu : J1.upper = J2.upper) :
 J1 = J2 := by
  have hj1 : J1.upper ∈ J1 := by exact MyInterval.upper_mem J1
  have hj2 : J1.upper ∈ J2 := by {rw [hu]; exact MyInterval.upper_mem J2}
  apply @eq_if_common_point I P _ _ hJ1 hJ2 J1.upper hj1 hj2

theorem eq_if_lower_lt_upper (h1: J1.lower < J2.upper)
(h2: J2.lower < J1.upper): J1 = J2 := by
  rcases le_or_gt J1.upper J2.upper with h | h
  · have ex : J1.upper ∈ J2 :=
    (MyInterval.mem_def J2 J1.upper).mp ⟨ h2, h ⟩
    exact (eq_if_common_point hJ1 hJ2 (MyInterval.upper_mem J1) ex)
  · have ex : J2.upper ∈ J1 :=
      (MyInterval.mem_def J1 J2.upper).mp ⟨ h1, le_of_lt h ⟩
    exact (eq_if_common_point hJ2 hJ1 (MyInterval.upper_mem J2) ex).symm

theorem lower_eq_upper_if_lower_in (hl : J1.lower ∈ J2):
J1.lower = J2.upper := by
  have hle : J1.lower ≤  J2.upper := ((MyInterval.mem_def J2 J1.lower).mp hl).2
  have hge : J1.lower ≥ J2.upper := by
    by_contra H
    rcases lt_or_ge J2.lower J1.upper with h | h
    · have ee := eq_if_lower_lt_upper hJ2 hJ1 h (lt_of_le_not_le hle H)
      rw [ee] at hl
      have cc := ((MyInterval.mem_def J1 J1.lower).mp hl).1
      exact (lt_self_iff_false J1.lower).mp cc
    · have ll := le_of_lt (gt_of_ge_of_gt h J1.lower_lt_upper)
      exact (J2.le_lower_non_mem J1.lower ll) hl
  exact le_antisymm hle hge

end

@[simp]
def single (I J : MyInterval) (h : J ≤ I) : Prepartition I :=
  ⟨{J}, by simpa, by simp⟩


/--
A Prepartition of an interval I is a Partition if it covers all of I
-/
def isPartition (P : Prepartition I) : Prop :=
  ∀ x ∈ I, ∃ J ∈ P, x ∈ J

theorem isPartition_nonempty (P : Prepartition I)(h : P.isPartition):
    ∃ J: MyInterval, J ∈ P := by
  let ⟨ J, hJ1, _⟩ := h I.upper (MyInterval.upper_mem I)
  use J

instance : LE (Prepartition I) :=
  ⟨fun P P' => ∀ ⦃I⦄, I ∈ P → ∃ I' ∈ P', I ≤ I'⟩

lemma eq_antisym' {P Q : Prepartition I} (hPQ : P ≤ Q) (hQP : Q ≤ P)
: ∀ J ∈ P, J ∈ Q := by
  intro J h
  obtain ⟨I',hI1,hI2⟩ := hPQ h
  obtain ⟨J',hJ1,hJ2⟩ := hQP hI1
  have hJJ' : J≤ J' := fun {x} a => hJ2 (hI2 a)
  have hJJ': J=J' := eq_if_le h hJ1 hJJ'
  have : I'= J := MyInterval.partialOrder.le_antisymm I' J (hJJ'▸ hJ2) hI2
  exact (MyInterval.partialOrder.le_antisymm I' J (hJJ'▸ hJ2) hI2) ▸ hI1

instance partialOrder : PartialOrder (Prepartition I) where
  le := (· ≤ ·)
  le_refl := by
    intro P
    intro I hI
    use I
  le_trans := by
    intro a b c hab hbc
    intro J hJ
    obtain ⟨I', hI1,hI2⟩ := hab hJ
    obtain ⟨J', hJ1,hJ2⟩ := hbc hI1
    use J'
    exact ⟨hJ1, fun a => hJ2 (hI2 a) ⟩
  le_antisymm := by
    intro a b hab hba
    ext I
    exact ⟨eq_antisym' hab hba _,eq_antisym' hba hab _⟩

instance : OrderTop (Prepartition I) where
  top := single I I (by tauto)
  le_top := by
    intro P
    intro J hJ
    use I
    constructor
    · exact Finset.singleton_subset_iff.mp fun ⦃I⦄ I => I
    · exact P.le_of_mem' J hJ

theorem lower_in {P : Prepartition I} {J: MyInterval} (h: J ∈ P)
  (hN: I.lower < J.lower) :  J.lower ∈ I  := by
  have aux : J.lower < I.upper := by exact gt_of_ge_of_gt ( upper_le_upper_I h) (J.lower_lt_upper)
  rw [MyInterval.mem_def]
  exact ⟨hN, le_of_lt aux⟩


structure TaggedPrepartition (I : MyInterval) extends Prepartition I where
  tag : MyInterval → ℝ
  tag_mem_Icc : ∀ J, tag J ∈ J.Closure

def TaggedPrepartition.isPartition (P : TaggedPrepartition I) := P.toPrepartition.isPartition

def upperset (P : Prepartition I): Finset ℝ  :=
  Finset.image (λ J ↦ J.upper) P.intervals

theorem upperset_nonempty (P : Prepartition I)(h : P.isPartition): (upperset P).Nonempty:= by
  rw [upperset]
  simp
  let ⟨J,hJ⟩ := isPartition_nonempty P h
  use J
  exact hJ

theorem upperset_mem (P : Prepartition I) (x:ℝ) : x ∈ upperset P ↔ ∃ J ∈ P, J.upper = x := by
  exact Finset.mem_image

theorem upperset_mem_of_mem (P : Prepartition I) (J:MyInterval) (h:J∈ P): J.upper ∈ P.upperset:=
  Finset.mem_image_of_mem _ h

theorem upper_I {P : Prepartition I} (h : P.isPartition):
    ∃ J ∈ P, J.upper = I.upper := by 
  let ⟨ J, hJ1, hJ2⟩ := h I.upper I.upper_mem
  have l2 := ((MyInterval.le_extr J I).mp (P.le_of_mem' J hJ1)).1 
  use J
  exact ⟨hJ1, le_antisymm l2 (hJ2.2) ⟩ 

def lowerset (P : Prepartition I): Finset ℝ  :=
  Finset.image (λ J ↦ J.lower) P.intervals

theorem lowerset_nonempty (P : Prepartition I)(h : P.isPartition): (lowerset P).Nonempty:= by
  rw [lowerset]
  simp
  let ⟨J,hJ⟩ := isPartition_nonempty P h
  use J
  exact hJ

theorem lowerset_mem (P : Prepartition I) (x : ℝ) : x ∈ lowerset P ↔ ∃ J ∈ P, J.lower = x := by
  exact Finset.mem_image

theorem lowerset_mem_of_mem (P : Prepartition I) (J:MyInterval) (h : J ∈ P) : J.lower ∈ P.lowerset:=
  Finset.mem_image_of_mem _ h

theorem lower_upper {P : Prepartition I} {J: MyInterval} (hJ: J ∈ P)
    (hN: I.lower < J.lower) (h : P.isPartition) : ∃ JJ ∈ P.intervals, JJ.upper = J.lower := by
  have hI : J.lower ∈ I  := lower_in hJ hN
  let ⟨JJ, hJJ1, hJJ2⟩ := h (J.lower : ℝ) hI
  use JJ
  exact ⟨hJJ1, by exact (lower_eq_upper_if_lower_in hJ hJJ1 hJJ2).symm⟩

theorem upper_lower {P : Prepartition I} {J: MyInterval}
(hJ: J ∈ P) (hN: J.upper ≠ I.upper) (h : P.isPartition):
    ∃ J' ∈ P.intervals, J'.lower =  J.upper := by
  let S := Finset.filter (J.upper < ·) P.upperset
  have NeS : S.Nonempty := by 
    rw [Finset.nonempty_coe_sort.symm]
    simp
    use I.upper
    rw [@Finset.mem_filter]
    exact ⟨(upperset_mem P I.upper).mpr (upper_I h), lt_of_le_of_ne (upper_le_upper_I hJ) hN ⟩ 
  let m := Finset.min' S NeS
  have minS : m ∈ S :=  Finset.min'_mem S NeS
  have minP : m ∈ P.upperset := Finset.mem_of_mem_filter m minS
  let ⟨J',hJ1,hJ2⟩:= (upperset_mem P m).mp minP
  have JleJ' : J.upper < J'.upper:= hJ2 ▸ (Finset.mem_filter.mp minS).2
  have HltJ': J.lower < J'.upper := lt_trans J.lower_lt_upper JleJ'
  use J'
  constructor
  · exact hJ1
  · have gee : J'.lower ≥  J.upper := by 
      by_contra H
      have JeJ':= eq_if_lower_lt_upper hJ hJ1 HltJ' (lt_of_not_ge H)
      have: J.upper = J'.upper := congrArg MyInterval.upper JeJ'
      rw [this] at JleJ'
      exact (lt_self_iff_false J'.upper).mp JleJ'
    have lee : J'.lower ≤ J.upper := by 
      have hh : I.lower < J'.lower := by 
        have t1 : I.lower < J.upper := by 
          have := ((MyInterval.le_extr J I).mp (P.le_of_mem' J hJ)).2
          exact lt_of_le_of_lt this J.lower_lt_upper 
        exact lt_of_lt_of_le t1 gee 
      let ⟨ Ju,hJu1,hJu2⟩:= lower_upper hJ1 hh h 
      have : Ju.upper < m:=  hJ2 ▸ hJu2 ▸ J'.lower_lt_upper
      rw [hJu2.symm] 
      have hu: Ju.upper ∈ P.upperset  := upperset_mem_of_mem P Ju hJu1  
      rw [@Finset.lt_min'_iff] at this 
      by_contra Hn
      exact (lt_self_iff_false Ju.upper).mp (this Ju.upper (Finset.mem_filter.mpr ⟨hu, not_le.mp Hn⟩))
    exact le_antisymm lee gee

theorem lower_I {P : Prepartition I} (h : P.isPartition):
    ∃ J ∈ P, J.lower = I.lower := by
  by_contra H
  have HH :∀ J ∈ P, I.lower < J.lower := by
    intro J hJ
    have h2: J.lower ≠ I.lower := not_and.mp (not_exists.mp H J) hJ
    exact lt_of_le_of_ne (lower_I_le_lower hJ ) (id (Ne.symm h2))
  let l:=P.lowerset.min' (lowerset_nonempty P h)
  have ex : ∃ J ∈ P, J.lower = l := by
    have :=  Finset.min'_mem (P.lowerset) (lowerset_nonempty P h)
    simp [lowerset_mem] at this
    exact this
  have fo: ∀ J∈ P, l≤ J.lower:= by
    intro J hJ
    exact Finset.min'_le P.lowerset J.lower (lowerset_mem_of_mem P J hJ)
  have ne: ∀ J∈ P, l∉ J := fun J a => MyInterval.le_lower_non_mem J l (fo J a)
  have HHH : ∀ J∈ P.intervals,  ∃ JJ ∈ P.intervals, JJ.upper = J.lower :=
    fun J a => lower_upper a (HH J a) h
  have HHHH : ∀ J∈ P.intervals, J.lower ∈ I:= by
    intro J hJ
    let ⟨JJ,hJJ1,hJJ2⟩ :=HHH J hJ
    rw [←hJJ2]
    exact (le_of_mem' P JJ hJJ1 ) ( MyInterval.upper_mem JJ)
  have linI : l∈ I:= by
    let ⟨lJ,hlJ1,hlJ2⟩:= ex
    rw [hlJ2.symm]
    exact HHHH lJ hlJ1
  have : ¬∀ (x : MyInterval), x ∈ P →  ¬ (l ∈ x) := by
    have:=not_forall_not.mpr (h l linI)
    simp_rw [not_and] at this
    exact this
  exact this ne

def Darboux (f : ℝ → ℝ) (α : ℝ → ℝ) (P : TaggedPrepartition I) :=
  ∑ J in P.intervals, f (P.tag J) * (α J.upper - α J.lower)

lemma upper_minus_lower {P : Prepartition I} (h : P.isPartition) :
  (P.upperset) \ (P.lowerset) = ({I.upper} : Finset ℝ) := by
  ext x
  constructor
  · simp
    intro hu hl
    rw [upperset_mem] at hu 
    obtain ⟨J,⟨hJ, hJ'⟩⟩ := hu
    subst hJ'
    by_contra hkey
    apply hl
    rw [lowerset_mem]
    exact upper_lower hJ hkey h
  · simp
    intro hx
    subst hx
    constructor
    · rw [upperset_mem]
      apply upper_I h
    · rw [lowerset_mem]
      simp 
      intro J hJ
      suffices : J.lower < I.upper
      · linarith
      linarith [upper_le_upper_I hJ, J.lower_lt_upper] 

lemma lower_minus_upper {P : Prepartition I} (h : P.isPartition) : 
    (P.lowerset) \ (P.upperset) = ({I.lower} : Finset ℝ) := by
  ext x
  constructor
  · simp
    intro hl hu
    rw [lowerset_mem] at hl
    obtain ⟨J,⟨hJ, hJ'⟩⟩ := hl
    subst hJ'
    by_contra hkey
    apply hu
    rw [upperset_mem]
    apply lower_upper hJ _ h
    suffices : I.lower ≤ J.lower
    · exact lt_of_le_of_ne' this hkey
    exact lower_I_le_lower hJ
  · simp
    intro hx
    subst hx
    constructor
    · rw [lowerset_mem]
      apply lower_I h
    · rw [upperset_mem]
      simp 
      intro J hJ
      suffices : I.lower < J.upper
      · linarith
      linarith [lower_I_le_lower hJ, J.lower_lt_upper] 

lemma telescope (X Y : Finset ℝ) (f : ℝ → ℝ) :
∑ x in X, f x - ∑ x in Y, f x
= ∑ x in (X \ Y), f x - ∑ x in (Y \ X), f x := by 
  rw [sub_eq_sub_iff_add_eq_add]
  have h1:= @Finset.disjoint_sdiff _ _ X Y  
  have h2:= @Finset.disjoint_sdiff _ _ Y X  
  rw [(Finset.sum_union h1).symm,add_comm,(Finset.sum_union h2).symm]
  simp_rw [Finset.union_sdiff_symm]

lemma key {P : Prepartition I} (f : ℝ → ℝ):
∑ x in P.intervals, f x.upper = ∑ u in P.upperset, f u := by
  unfold upperset
  rw [Finset.sum_image]
  intro x hx y hy hxy
  apply eq_if_eq_upper hx hy hxy
  done

lemma key' {P : Prepartition I} (f : ℝ → ℝ):
∑ x in P.intervals, f x.lower = ∑ l in P.lowerset, f l := by
  unfold lowerset
  rw [Finset.sum_image]
  intro x hx y hy hxy
  apply eq_if_eq_lower hx hy hxy
  done

theorem Darboux_const (c : ℝ) (α : ℝ → ℝ) (P : TaggedPrepartition I) (h : P.isPartition) :
  Darboux (λ _ : ℝ ↦ c) α P = c * (α I.upper - α I.lower) := by
  unfold Darboux
  simp
  calc
  _ = ∑ x in P.intervals, c * α x.upper - ∑ x in P.intervals, c * α x.lower := by {rw [← @Finset.sum_sub_distrib]; congr; ext; ring}
  _ =  ∑ x in P.intervals, ((c • α) · ) x.upper - ∑ x in P.intervals, ((c • α) · ) x.lower := by simp
  _ = ∑ u in P.upperset, c * α u - ∑ l in P.lowerset, c * α l := by {rw [key, key']; simp}
  _ = ∑ u in (P.upperset \ P.lowerset), c * α u - ∑ l in (P.lowerset \ P.upperset), c * α l := telescope _ _ _
  _ = ∑ u in {I.upper}, c * α u - ∑ l in {I.lower}, c * α l := by rw [upper_minus_lower h, lower_minus_upper h]
  _ = c * (α I.upper - α I.lower) := by {simp; ring}
