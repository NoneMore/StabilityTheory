import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Topology.DerivedSet

open Set

universe u

section

variable {X : Type u} [TopologicalSpace X]

/-- The transfinite iteration of the derived-set operator on a set. -/
def iteratedDerivedSet (s : Set X) : Ordinal → Set X :=
  fun a =>
    Ordinal.limitRecOn (motive := fun _ => Set X) a
      s
      (fun _ t => derivedSet t)
      (fun a _ ih => ⋂ b : Set.Iio a, ih b.1 b.2)

@[simp]
theorem iteratedDerivedSet_zero (s : Set X) :
    iteratedDerivedSet s 0 = s := by
  simp [iteratedDerivedSet]

@[simp]
theorem iteratedDerivedSet_succ (s : Set X) (a : Ordinal) :
    iteratedDerivedSet s (Order.succ a) = derivedSet (iteratedDerivedSet s a) := by
  simp only [iteratedDerivedSet, Ordinal.limitRecOn_succ]

theorem iteratedDerivedSet_limit (s : Set X) {a : Ordinal} (ha : Order.IsSuccLimit a) :
    iteratedDerivedSet s a = ⋂ b : Set.Iio a, iteratedDerivedSet s b := by
  simp_all only [iteratedDerivedSet, iInter_coe_set, mem_Iio, Ordinal.limitRecOn_limit]

theorem isClosed_iteratedDerivedSet [T1Space X] {s : Set X} (hs : IsClosed s) :
    ∀ a, IsClosed (iteratedDerivedSet s a) := by
  intro a
  induction a using Ordinal.limitRecOn with
  | zero => simpa
  | succ a ha =>
    simp only [iteratedDerivedSet_succ]
    exact isClosed_derivedSet _
  | limit a ha ha' =>
    simp only [iteratedDerivedSet_limit s ha]
    refine isClosed_iInter ?_
    aesop

theorem iteratedDerivedSet_antitone [T1Space X] (s : Set X) (hs : IsClosed s) :
    Antitone (iteratedDerivedSet s) := by
  intro a b hab
  induction b using Ordinal.limitRecOn with
  | zero => aesop
  | succ b ih =>
    by_cases! h : a ≤ b
    · trans iteratedDerivedSet s b
      · simp only [iteratedDerivedSet_succ]
        refine le_iff_subset.mpr ?_
        exact (isClosed_iff_derivedSet_subset (iteratedDerivedSet s b)).mp
          (isClosed_iteratedDerivedSet hs b)
      · exact ih h
    · have : a = Order.succ b := by
        apply Order.succ_le_of_lt at h
        exact le_antisymm hab h
      simp [this]
  | limit b hb ih =>
    intro x hx
    rcases lt_or_eq_of_le hab with hlt | rfl
    · rw [iteratedDerivedSet_limit s hb] at hx
      exact hx (iteratedDerivedSet s a) (by
        simp only [mem_range, Subtype.exists, mem_Iio,
        exists_prop]
        exists a)
    · assumption

theorem iteratedDerivedSet_mono :
    Monotone (fun s : Set X => iteratedDerivedSet s) := by
  intro a b hab o
  induction o using Ordinal.limitRecOn with
  | zero => aesop
  | succ o ih =>
    simp only [iteratedDerivedSet_succ]
    exact derivedSet_mono _ _ ih
  | limit o ho ih =>
    simp only [iteratedDerivedSet_limit a ho, iteratedDerivedSet_limit b ho]
    intro x hx
    simp only [iInter_coe_set, mem_Iio, mem_iInter] at ⊢ hx
    aesop

end
