import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.FixedPointApproximants
import Mathlib.Topology.DerivedSet

open Set Cardinal

universe u v

namespace CantorBendixson

section

variable {X : Type v} [TopologicalSpace X]

/-- The transfinite iteration of the derived-set operator on a set. -/
def iteratedDerivedSet (s : Set X) : Ordinal.{u} → Set X :=
  fun a =>
    Ordinal.limitRecOn (motive := fun _ => Set X) a
      s
      (fun _ t => derivedSet t)
      (fun a _ ih => ⋂ b : Set.Iio a, ih b.1 b.2)

@[inherit_doc CantorBendixson.iteratedDerivedSet]
scoped[CantorBendixson] notation:max s "ᵈ[" a "]" => iteratedDerivedSet s a

@[simp]
theorem iteratedDerivedSet_zero (s : Set X) :
    sᵈ[0] = s := by
  simp [iteratedDerivedSet]

@[simp]
theorem iteratedDerivedSet_succ (s : Set X) (a : Ordinal) :
    sᵈ[Order.succ a] = derivedSet (sᵈ[a]) := by
  simp only [iteratedDerivedSet, Ordinal.limitRecOn_succ]

@[simp]
theorem iteratedDerivedSet_succ' (s : Set X) (a : Ordinal) :
    sᵈ[a+1] = derivedSet (sᵈ[a]) := by
  simp [← Order.succ_eq_add_one]

theorem iteratedDerivedSet_limit (s : Set X) {a : Ordinal} (ha : Order.IsSuccLimit a) :
    sᵈ[a] = ⋂ b : Set.Iio a, sᵈ[b] := by
  simp_all only [iteratedDerivedSet, iInter_coe_set, mem_Iio, Ordinal.limitRecOn_limit]

theorem isClosed_iteratedDerivedSet [T1Space X] {s : Set X} (hs : IsClosed s) :
    ∀ a, IsClosed (sᵈ[a]) := by
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

theorem iteratedDerivedSet_succ_subset {s : Set X} (hs : IsClosed s) (a : Ordinal.{u}) :
    sᵈ[Order.succ a] ⊆ sᵈ[a] := by
  induction a using Ordinal.limitRecOn with
  | zero =>
    simpa only [iteratedDerivedSet_zero, iteratedDerivedSet_succ] using
      (isClosed_iff_derivedSet_subset s).mp hs
  | succ a ih =>
    simp only [iteratedDerivedSet_succ] at *
    refine derivedSet_mono _ _ ih
  | limit a ha ih =>
    simp only [iteratedDerivedSet_succ, iteratedDerivedSet_limit s ha]
    intro x hx
    simp only [mem_iInter]
    intro b
    apply ih b.1 b.2
    simpa only [iteratedDerivedSet_succ] using
      (derivedSet_mono _ _ (fun y hy => (Set.mem_iInter.mp hy) b) hx)

theorem iteratedDerivedSet_antitone {s : Set X} (hs : IsClosed s) :
    Antitone (iteratedDerivedSet s) := by
  intro a b hab
  induction b using Ordinal.limitRecOn with
  | zero => aesop
  | succ b ih =>
    by_cases! h : a ≤ b
    · exact le_trans (iteratedDerivedSet_succ_subset hs b) (ih h)
    · suffices this : a = Order.succ b by simp [this]
      exact eq_of_ge_of_le (Order.succ_le_iff.mpr h) hab
  | limit b hb ih =>
    rcases (le_iff_lt_or_eq.mp hab) with hlt | rfl
    · simp only [iteratedDerivedSet_limit s hb]
      intro x hx
      simp only [mem_iInter] at hx
      simpa using hx ⟨a,hlt⟩
    rfl

theorem iteratedDerivedSet_mono :
    Monotone (fun s : Set X => iteratedDerivedSet.{u} s) := by
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

abbrev stayOn (s : Set X) (a : Ordinal.{u}) : Prop :=
    ∀ b : Ordinal.{u}, a ≤ b →
    sᵈ[b] = sᵈ[a]

/-- The iterated derived-set sequence eventually stabilizes. -/
theorem iteratedDerivedSet_stay {s : Set X} (hs : IsClosed s) :
    ∃ a : Ordinal.{v}, stayOn s a := by
  suffices h : ∃ a : Ordinal.{v}, sᵈ[a+1] = sᵈ[a] by
    obtain ⟨a,ha⟩ := h
    refine ⟨a, ?_⟩
    intro b hab
    induction b using Ordinal.limitRecOn with
    | zero => aesop
    | succ b ih =>
      by_cases h : a ≤ b
      · simpa [ih h] using ha
      · suffices this : a = b+1 by simp [this]
        exact eq_of_ge_of_le (Order.succ_le_iff.mpr (lt_of_not_ge h)) hab
    | limit b hb ih =>
      rcases lt_or_eq_of_le hab with hab' | rfl
      · apply le_antisymm
        · exact iteratedDerivedSet_antitone hs hab
        · rw [iteratedDerivedSet_limit s hb]
          intro x hx
          simp only [mem_iInter]
          intro o
          rcases lt_or_ge o.1 a with hoa | hao
          · exact iteratedDerivedSet_antitone hs (le_of_lt hoa) hx
          · simpa [ih o.1 o.2 hao] using hx
      rfl
  let f : Ordinal.{v} → Set X := iteratedDerivedSet s
  let κ : Ordinal.{v} := (Order.succ #(Set X)).ord
  have hni : ¬ Set.InjOn f (Set.Iio κ) :=
    Cardinal.not_injective_limitation_set f
  rw [Set.injOn_iff_injective, Function.not_injective_iff] at hni
  obtain ⟨a, b, hab, habn⟩ := hni
  wlog hlt : a < b generalizing a b
  · replace hlt : b < a :=
      lt_of_le_of_ne (not_lt.mp hlt) (id habn.symm)
    exact this b a hab.symm habn.symm hlt
  · exists a
    refine le_antisymm (iteratedDerivedSet_antitone hs le_self_add) ?_
    have : sᵈ[↑a] = sᵈ[↑b] :=
      Filter.principal_eq_iff_eq.mp (congrArg Filter.principal hab)
    rw [this]
    exact iteratedDerivedSet_antitone hs (Order.add_one_le_iff.mpr hlt)

/-- The perfect kernel of a set, defined as the intersection of all iterated derived sets. -/
def perfectKernel (s : Set X) : Set X :=
  ⋂ a : Ordinal.{u}, sᵈ[a]

theorem perfectKernel_subset_iteratedDerivedSet (s : Set X) (a : Ordinal.{u}) :
    perfectKernel.{u} s ⊆ sᵈ[a] := by
  intro x hx
  rw [perfectKernel] at hx
  exact (Set.mem_iInter.mp hx) a

theorem perfectKernel_mono {s t : Set X} (hst : s ⊆ t) :
    perfectKernel.{u} s ⊆ perfectKernel.{u} t := by
  simp only [perfectKernel]
  suffices h : ∀ o : Ordinal.{u}, sᵈ[o] ⊆ tᵈ[o] by
    exact iInter_mono'' h
  exact iteratedDerivedSet_mono hst

theorem perfect_perfectKernel {s : Set X} (hs : IsClosed s) :
    Perfect (perfectKernel.{v} s) := by
  obtain ⟨a,ha⟩ := iteratedDerivedSet_stay hs
  have hkernel : perfectKernel.{v} s = sᵈ[a] := by
    refine le_antisymm (perfectKernel_subset_iteratedDerivedSet s a) ?_
    intro x hx
    rw [perfectKernel]
    refine Set.mem_iInter.mpr ?_
    intro b
    rcases lt_or_ge b a with hba | hab
    · exact iteratedDerivedSet_antitone hs (le_of_lt hba) hx
    · simpa [ha b hab] using hx
  rw [hkernel]
  refine perfect_iff_eq_derivedSet.mpr ?_
  simpa [iteratedDerivedSet_succ'] using (ha (a + 1) le_self_add).symm

/--
The pointwise Cantor-Bendixson rank of a point of a set, with value `⊤`
when the point survives every successor stage.
-/
noncomputable def cbRank (s : Set X) (x : s) : WithTop Ordinal :=
  sInf
    ((↑) '' {a : Ordinal.{u} | x.1 ∉ sᵈ[a + 1]})

theorem cbRank_le_iff {s : Set X} (hs : IsClosed s) {x : s} {a : Ordinal.{u}} :
    cbRank s x ≤ (a : WithTop Ordinal.{u}) ↔ x.1 ∉ sᵈ[a + 1] := by
  constructor <;> intro h
  · intro hx
    have hsucc : (WithTop.some (a+1)) ≤ cbRank s x := by
      rw [cbRank, le_sInf_iff]
      rintro _ ⟨b, hb, rfl⟩
      exact WithTop.coe_le_coe.mpr <| by
        by_contra hab
        have : b + 1 ≤ a + 1 := by
          simp_all only [Order.add_one_le_iff, not_lt, Order.lt_add_one_iff]
        exact hb ((iteratedDerivedSet_antitone hs this) hx)
    exact
      (not_le_of_gt
        (WithTop.coe_lt_coe.mpr (by simp))) (hsucc.trans h)
  · exact sInf_le ⟨a, h, rfl⟩

theorem le_cbRank_iff {s : Set X} (hs : IsClosed s) {x : s} {a : Ordinal.{u}} :
    (a : WithTop Ordinal.{u}) ≤ cbRank s x ↔ x.1 ∈ sᵈ[a] := by
  constructor
  · intro h
    induction a using Ordinal.limitRecOn with
    | zero => simp
    | succ a ih =>
        by_contra hx
        have h' : cbRank s x ≤ (a : WithTop Ordinal.{u}) := by
          exact (cbRank_le_iff hs).mpr (by simpa [← Order.succ_eq_add_one] using hx)
        have hsuc :
            ¬ ((WithTop.some (a+1)) ≤ ↑a) := by
          exact not_le_of_gt (WithTop.coe_lt_coe.mpr (by simp))
        exact hsuc (h.trans h')
    | limit a ha ih =>
        rw [iteratedDerivedSet_limit s ha]
        refine Set.mem_iInter.mpr ?_
        intro b
        exact ih b.1 b.2 ((WithTop.coe_le_coe.mpr (le_of_lt b.2)).trans h)
  · intro hx
    rw [cbRank, le_sInf_iff]
    rintro _ ⟨b, hb, rfl⟩
    exact WithTop.coe_le_coe.mpr <| by
      by_contra hab
      have hba : b + 1 ≤ a := by
        simpa [Order.lt_add_one_iff] using lt_of_not_ge hab
      exact hb ((iteratedDerivedSet_antitone hs hba) hx)

theorem cbRank_eq_iff {s : Set X} (hs : IsClosed s) {x : s} {a : Ordinal.{u}} :
    cbRank s x = (a : WithTop Ordinal.{u}) ↔
      x.1 ∈ sᵈ[a] ∧ x.1 ∉ sᵈ[a + 1] := by
  constructor
  · intro h
    constructor
    · exact (le_cbRank_iff hs).mp h.ge
    · exact (cbRank_le_iff hs).mp h.le
  · rintro ⟨hxa, hxna⟩
    exact le_antisymm ((cbRank_le_iff hs).mpr hxna) ((le_cbRank_iff hs).mpr hxa)

theorem cbRank_eq_top_iff {s : Set X} {x : s} :
    cbRank.{u} s x = ⊤ ↔ x.1 ∈ perfectKernel.{u} s := by
  simp only [sInf_eq_top, mem_image, mem_setOf_eq, cbRank, perfectKernel,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    WithTop.coe_ne_top, imp_false, not_not, mem_iInter]
  constructor
  · intro h a
    induction a using Ordinal.limitRecOn with
    | zero => simp
    | succ b ih => exact h b
    | limit a ha ih =>
      simpa [iteratedDerivedSet_limit s ha]
  · intro h a
    exact h (a + 1)

theorem cbRank_mono {s t : Set X} (hst : s ⊆ t) (x : s) :
    cbRank.{u} s x ≤ cbRank t ⟨x.1, hst x.2⟩ := by
  simp only [cbRank, le_sInf_iff, mem_image, mem_setOf_eq,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro a ha
  have := iteratedDerivedSet_mono.{u} hst (a+1)
  simp only [le_eq_subset] at this
  have : ↑x ∉ sᵈ[a + 1] := (mem_compl_iff sᵈ[a + 1] ↑x).mp fun a ↦ ha (this a)
  replace this : ↑a ∈ (WithTop.some '' {a | x.1 ∉ sᵈ[a + 1]}) := by
    exact mem_image_of_mem WithTop.some this
  exact CompleteSemilatticeInf.sInf_le (WithTop.some '' {a | ↑x ∉ sᵈ[a + 1]}) (↑a) this

end

end CantorBendixson
