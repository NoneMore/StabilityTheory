import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.FixedPointApproximants
import Mathlib.Topology.DerivedSet
import Mathlib.Topology.Perfect

open Set Cardinal

universe u

namespace CantorBendixson

section

variable {X : Type u} [TopologicalSpace X]

/-- The isolated points of a set, i.e. the points not in its derived set. -/
def isolatedPoints (A : Set X) : Set X :=
  A \ derivedSet A

theorem mem_isolatedPoints_iff {A : Set X} {x : X} :
    x ∈ isolatedPoints A ↔
      x ∈ A ∧ ∃ U, IsOpen U ∧ x ∈ U ∧ A ∩ U = {x} := by
  rw [isolatedPoints, mem_diff, mem_derivedSet, accPt_iff_nhds]
  constructor
  · rintro ⟨hxA, hx⟩
    push_neg at hx
    rcases hx with ⟨U, hUx, hU⟩
    rcases mem_nhds_iff.mp hUx with ⟨V, hVU, hVopen, hxV⟩
    refine ⟨hxA, V, hVopen, hxV, Set.eq_singleton_iff_unique_mem.2 ?_⟩
    exact ⟨⟨hxA, hxV⟩, fun y hy ↦ hU y ⟨hVU hy.2, hy.1⟩⟩
  · rintro ⟨hxA, U, hUopen, hxU, hAU⟩
    refine ⟨hxA, ?_⟩
    push_neg
    refine ⟨U, IsOpen.mem_nhds hUopen hxU, ?_⟩
    intro y hy
    simpa [inter_comm, hAU] using hy


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

theorem iteratedDerivedSet_eq_of_perfect {s : Set X} (hs : Perfect s) :
    ∀ a : Ordinal.{u}, sᵈ[a] = s := by
  intro a
  induction a using Ordinal.limitRecOn with
  | zero => simp
  | succ a ha =>
    simp only [Order.succ_eq_add_one, iteratedDerivedSet_succ', ha]
    exact (perfect_iff_eq_derivedSet.mp hs).symm
  | limit a ha ih =>
    rw [iteratedDerivedSet_limit s ha]
    ext x
    constructor
    · intro hx
      have h0 : x ∈ sᵈ[(0 : Ordinal.{u})] := by
        exact (Set.mem_iInter.mp hx) ⟨0, by simpa using ha.bot_lt⟩
      simpa using h0
    · intro hx
      refine Set.mem_iInter.mpr ?_
      intro i
      simpa [ih i.1 i.2] using hx

theorem isClosed_iteratedDerivedSet {s : Set X} (hs : IsClosed s) :
    ∀ a, IsClosed (sᵈ[a]) := by
  intro a
  induction a using Ordinal.limitRecOn with
  | zero => simpa
  | succ a ha =>
    simp_all [isClosed_iff_derivedSet_subset, derivedSet_mono]
  | limit a ha ih =>
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

theorem stayOn.mono {s : Set X} {a b : Ordinal.{u}} (h : stayOn.{u} s a) (hle : a ≤ b) :
    stayOn.{u} s b := by
  simp only [stayOn] at *
  intro c hle'
  simpa [h b hle] using (h c <| le_trans hle hle')

/-- If the iterated derived set stops changing at a successor stage,
it stays constant from there on. -/
theorem stayOn_of_iteratedDerivedSet_succ_eq
    {s : Set X} (hs : IsClosed s) {a : Ordinal.{u}}
    (ha : sᵈ[a + 1] = sᵈ[a]) :
    stayOn.{u} s a := by
  intro b hab
  induction b using Ordinal.limitRecOn with
  | zero => aesop
  | succ b ih =>
    by_cases h : a ≤ b
    · simpa [ih h] using ha
    · suffices this : a = b + 1 by simp [this]
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
    · rfl

/-- The iterated derived-set sequence eventually stabilizes. -/
theorem iteratedDerivedSet_stay {s : Set X} (hs : IsClosed s) :
    ∃ a : Ordinal.{u}, stayOn s a := by
  suffices h : ∃ a : Ordinal.{u}, sᵈ[a+1] = sᵈ[a] by
    obtain ⟨a,ha⟩ := h
    exact ⟨a, stayOn_of_iteratedDerivedSet_succ_eq hs ha⟩
  let f : Ordinal.{u} → Set X := iteratedDerivedSet s
  let κ : Ordinal.{u} := (Order.succ #(Set X)).ord
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

theorem perfectKernel_subset (s : Set X) :
    perfectKernel.{u} s ⊆ s := by
  nth_rw 2 [← iteratedDerivedSet_zero s]
  exact perfectKernel_subset_iteratedDerivedSet s 0

theorem perfectKernel_mono {s t : Set X} (hst : s ⊆ t) :
    perfectKernel.{u} s ⊆ perfectKernel.{u} t := by
  simp only [perfectKernel]
  suffices h : ∀ o : Ordinal.{u}, sᵈ[o] ⊆ tᵈ[o] by
    exact iInter_mono'' h
  exact iteratedDerivedSet_mono hst

theorem isClosed_perfectKernel {s : Set X} (hs : IsClosed s) :
    IsClosed (perfectKernel.{u} s) :=
  isClosed_iInter (isClosed_iteratedDerivedSet hs)

@[simp]
theorem perfectKernel_empty :
    perfectKernel.{u} (∅ : Set X) = ∅ := by
  simpa using perfectKernel_subset ∅

theorem perfectKernel_eq_iteratedDerivedSet {s : Set X} (hs : IsClosed s) :
    ∃ a : Ordinal.{u}, stayOn s a ∧ perfectKernel.{u} s = sᵈ[a] := by
  obtain ⟨a, ha⟩ := iteratedDerivedSet_stay hs
  refine ⟨a, ha, le_antisymm (perfectKernel_subset_iteratedDerivedSet s a) ?_⟩
  rw [perfectKernel]
  refine Set.subset_iInter fun i x hx => ?_
  rcases lt_or_ge i a with hi | hi
  · exact iteratedDerivedSet_antitone hs (le_of_lt hi) hx
  · simpa [ha i hi] using hx

theorem subset_perfectKernel_of_perfect {P s : Set X}
    (hP : Perfect P) (hPs : P ⊆ s) :
    P ⊆ perfectKernel.{u} s := by
  rw [perfectKernel]
  refine Set.subset_iInter fun i x hx => ?_
  exact (iteratedDerivedSet_mono.{u} hPs i) <| by
    simpa [iteratedDerivedSet_eq_of_perfect hP i] using hx

theorem perfect_perfectKernel {s : Set X} (hs : IsClosed s) :
    Perfect (perfectKernel.{u} s) := by
  obtain ⟨a, ha, hkernel⟩ := perfectKernel_eq_iteratedDerivedSet hs
  rw [hkernel]
  refine perfect_iff_eq_derivedSet.mpr ?_
  simpa [iteratedDerivedSet_succ'] using (ha (a + 1) le_self_add).symm

theorem perfectKernel_idem {s : Set X} (hs : IsClosed s) :
    perfectKernel.{u} (perfectKernel.{u} s) = perfectKernel.{u} s := by
  nth_rw 1 [perfectKernel]
  exact iInter_eq_const <|
    iteratedDerivedSet_eq_of_perfect (perfect_perfectKernel hs)

/-- The set-level Cantor-Bendixson rank, defined as the least stabilization stage. -/
noncomputable def setCBRank (s : Set X) : Ordinal.{u} :=
  sInf {a : Ordinal.{u} | stayOn.{u} s a}

theorem setCBRank_stay {s : Set X} (hs : IsClosed s) :
    stayOn.{u} s (setCBRank s) := by
  rw [setCBRank]
  obtain ⟨a, ha⟩ := iteratedDerivedSet_stay hs
  exact csInf_mem (s := {a : Ordinal.{u} | stayOn.{u} s a}) ⟨a, ha⟩

/-- The derived-set chain strictly drops exactly before the stabilization stage. -/
theorem lt_setCBRank_iff_nonempty_layer {s : Set X} (hs : IsClosed s)
    {a : Ordinal.{u}} :
    a < setCBRank s ↔ (isolatedPoints (sᵈ[a])).Nonempty := by
  rw [isolatedPoints, ← iteratedDerivedSet_succ']
  constructor <;> intro h
  · by_contra! h'
    replace h' : sᵈ[a+1] = sᵈ[a]  := by
      refine Subset.antisymm_iff.mpr ⟨iteratedDerivedSet_antitone hs le_self_add,
        diff_eq_empty.mp h'⟩
    apply stayOn_of_iteratedDerivedSet_succ_eq hs at h'
    simp only [setCBRank] at h
    rw [lt_iff_not_ge] at h
    exact h (csInf_le' h')
  · contrapose! h
    replace h : stayOn s a := (setCBRank_stay hs).mono h
    simp only [h (a + 1) (le_self_add), sdiff_self, bot_eq_empty]

theorem perfectKernel_eq_iteratedDerivedSet_setCBRank {s : Set X} (hs : IsClosed s) :
    perfectKernel.{u} s = sᵈ[setCBRank s] := by
  obtain ⟨a, ha, ha'⟩ := perfectKernel_eq_iteratedDerivedSet hs
  exact ha'.trans <| setCBRank_stay hs a <| by
    rw [setCBRank]
    exact csInf_le' ha

theorem setCBRank_le_ord_succ {s : Set X} (hs : IsClosed s) :
    setCBRank s ≤ (Order.succ #s).ord := by
  let κ := (Order.succ #s).ord
  change _ ≤ κ
  by_contra! hκ
  have hne : ∀ a : Set.Iio κ, sᵈ[↑a + 1] ≠ sᵈ[↑a] := by
    intro a hstay
    exact not_lt_of_gt hκ <|
      lt_of_le_of_lt (csInf_le' (stayOn_of_iteratedDerivedSet_succ_eq hs hstay)) a.2
  have h : ∀ a : Set.Iio κ, ((sᵈ[↑a]) \ sᵈ[↑a + 1]).Nonempty := by
    intro a
    exact nonempty_of_ssubset <|
      Set.ssubset_iff_subset_ne.mpr ⟨iteratedDerivedSet_antitone hs le_self_add, hne a⟩
  let f : Set.Iio κ → s := fun a => ⟨(h a).some, by
    have hmem : (h a).some ∈ sᵈ[↑a] := (Set.mem_diff _).mp (h a).some_mem |>.1
    have hsub : sᵈ[↑a] ⊆ s := by
      simpa using
        (iteratedDerivedSet_antitone hs (show (0 : Ordinal.{u}) ≤ ↑a from by simp))
    exact hsub hmem⟩
  have finj : Function.Injective f := by
    intro a b hab
    by_contra! hne
    wlog hlt : a < b generalizing a b with hswap
    · have hgt : b < a :=
        lt_of_le_of_ne (not_lt.mp (hswap hab hne)) hne.symm
      exact hswap hab.symm hne.symm hgt
    · have hfb : ↑(f b) ∈ sᵈ[↑a + 1] := by
        apply mem_of_subset_of_mem (iteratedDerivedSet_antitone hs <| by simpa using hlt)
        change (h b).some ∈ sᵈ[↑b]
        exact ((Set.mem_diff _).mp (h b).some_mem).1
      rw [← hab] at hfb
      exact ((Set.mem_diff _).mp (h a).some_mem).2 hfb
  let g : Ordinal.{u} → s := fun a => if ha : a < κ then f ⟨a, ha⟩ else
     f ⟨0, by simp [κ, Cardinal.lt_ord]⟩
  exact Cardinal.not_injective_limitation_set g <| fun a ha b hb hab =>
    by
      change a < κ at ha
      change b < κ at hb
      have hab' : f ⟨a, ha⟩ = f ⟨b, hb⟩ := by
        dsimp [g] at hab
        rwa [dif_pos ha, dif_pos hb] at hab
      exact congrArg Subtype.val (finj hab')

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
      x.1 ∈ isolatedPoints (sᵈ[a]) := by
  simp only [isolatedPoints, ← iteratedDerivedSet_succ']
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

theorem setOf_cbRank_lt_top_eq_diff_perfectKernel {s : Set X} :
    (↑{x : s | cbRank.{u} s x < ⊤} : Set X) = s \ perfectKernel.{u} s := by
  ext x
  simp only [mem_image, mem_setOf_eq, Subtype.exists, exists_and_right, exists_eq_right,
    mem_diff]
  constructor
  · rintro ⟨hx, hrank⟩
    simp only [lt_top_iff_ne_top, cbRank_eq_top_iff.not] at hrank
    exact ⟨hx, hrank⟩
  · rintro ⟨hxs, hxk⟩
    exists hxs
    simp only [lt_top_iff_ne_top, cbRank_eq_top_iff.not]
    exact hxk

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

theorem cbRank_lt_setCBRank_iff {s : Set X} (hs : IsClosed s) {x : s} :
    cbRank.{u} s x < (setCBRank s : WithTop Ordinal.{u}) ↔
      x.1 ∉ perfectKernel.{u} s := by
  constructor
  · rw [← cbRank_eq_top_iff]
    exact fun a ↦ LT.lt.ne_top a
  · intro hx
    contrapose! hx
    simpa [perfectKernel_eq_iteratedDerivedSet_setCBRank hs] using
      (le_cbRank_iff hs).mp hx

/-- Telescoping decomposition of the scattered part into isolated layers. -/
theorem diff_perfectKernel_eq_iUnion_layers {s : Set X} (hs : IsClosed s) :
    s \ perfectKernel.{u} s = ⋃ a : Set.Iio (setCBRank s), isolatedPoints (sᵈ[a]) := by
  ext x
  constructor
  · rintro hx
    let x' : s := ⟨x, hx.1⟩
    have hrank : cbRank s x' < ↑(setCBRank s) :=
      (cbRank_lt_setCBRank_iff hs).2 hx.2
    let a : Ordinal.{u} := (cbRank s x').untop (ne_top_of_lt hrank)
    refine mem_iUnion.2 ⟨⟨a, (WithTop.untop_lt_iff (ne_top_of_lt hrank)).2 hrank⟩, ?_⟩
    simpa [a] using
      (cbRank_eq_iff hs).1 (Eq.symm <| WithTop.coe_untop (cbRank s x') (ne_top_of_lt hrank))
  · rw [perfectKernel_eq_iteratedDerivedSet_setCBRank hs]
    simp only [isolatedPoints, ← iteratedDerivedSet_succ', iUnion_coe_set, mem_Iio, mem_iUnion,
      exists_prop, mem_diff]
    rintro ⟨a, ha, hxa, hxa'⟩
    refine ⟨?_, ?_⟩
    · apply mem_of_subset_of_mem ?_ hxa
      nth_rw 2 [← iteratedDerivedSet_zero s]
      exact iteratedDerivedSet_antitone hs (zero_le a)
    · exact fun hxk => hxa' <|
        iteratedDerivedSet_antitone hs (Order.add_one_le_iff.mpr ha) hxk

theorem cbRank_lt_ord_succ {s : Set X} (hs : IsClosed s) {x : s}
    (hx : x.1 ∉ perfectKernel.{u} s) :
    cbRank.{u} s x < ((Order.succ #s).ord : WithTop Ordinal.{u}) := by
  rw [← cbRank_lt_setCBRank_iff hs] at hx
  exact lt_of_lt_of_le hx <| WithTop.coe_le_coe.mpr <| setCBRank_le_ord_succ hs

/-- A set is scattered if it contains no nonempty perfect subset. -/
def IsScattered (s : Set X) : Prop :=
  ¬ ∃ P : Set X, P.Nonempty ∧ Perfect P ∧ P ⊆ s

theorem perfectKernel_eq_empty_iff {s : Set X} (hs : IsClosed s) :
    perfectKernel.{u} s = ∅ ↔ IsScattered s := by
  constructor
  · intro h
    by_contra!
    simp only [IsScattered, not_exists, not_and, not_forall, not_not] at this
    obtain ⟨P,hPne,hP,hPs⟩ := this
    have : P = ∅ := by simpa [h] using subset_perfectKernel_of_perfect hP hPs
    aesop
  · intro h
    simp only [IsScattered, not_exists, not_and] at h
    contrapose! h
    exact ⟨(perfectKernel s), h, (perfect_perfectKernel hs), perfectKernel_subset s⟩

theorem isScattered_diff_perfectKernel {s : Set X} :
    IsScattered (s \ perfectKernel.{u} s) := by
  by_contra! h
  simp only [IsScattered, not_exists, not_and, not_forall, not_not] at h
  obtain ⟨P,hPne,hP,hPss⟩ := h
  have := subset_perfectKernel_of_perfect hP (subset_trans hPss diff_subset)
  replace this : P = ∅ := by
    simpa only [← subset_empty_iff, diff_inter_self] using subset_inter hPss this
  aesop

/--
The intrinsic Cantor-Bendixson decomposition attached to `perfectKernel`:
the closed set `s` splits as its scattered part and its perfect kernel.
-/
theorem cantorBendixson_decomposition {s : Set X} (hs : IsClosed s) :
    IsScattered (s \ perfectKernel.{u} s) ∧
      Perfect (perfectKernel.{u} s) ∧
      s = (s \ perfectKernel.{u} s) ∪ perfectKernel.{u} s :=
    ⟨isScattered_diff_perfectKernel,
      perfect_perfectKernel hs,
      (diff_union_of_subset (perfectKernel_subset s)).symm⟩

section SecondCountable

open TopologicalSpace

variable [SecondCountableTopology X]

/-- An isolated point admits a countable-basis neighborhood isolating it inside the ambient set. -/
theorem exists_countableBasis_of_mem_isolatedPoints {A : Set X} {x : X}
    (hx : x ∈ isolatedPoints A) :
    ∃ U : countableBasis X, x ∈ (U : Set X) ∧ A ∩ U ⊆ {x} := by
  obtain ⟨hxA, U, hUo, hxU, hAU⟩ := mem_isolatedPoints_iff.mp hx
  obtain ⟨V, hV, hxV, hVU⟩ := (isBasis_countableBasis X).exists_subset_of_mem_open hxU hUo
  refine ⟨⟨V, hV⟩, hxV, ?_⟩
  trans A ∩ U
  · exact inter_subset_inter (subset_refl A) hVU
  simp only [hAU, subset_refl]

/-- In a second-countable space, every set has countably many isolated points. -/
theorem countable_isolatedPoints (A : Set X) :
    (isolatedPoints A).Countable := by
  classical
  choose f hf_mem hf_sub using
    fun x : isolatedPoints A => exists_countableBasis_of_mem_isolatedPoints x.2
  have hf_inj : Function.Injective f := by
    intro x y hxy
    rw [Subtype.ext_iff]
    have hyf : y.1 ∈ (f x : Set X) := by simpa [hxy] using hf_mem y
    have hy : y.1 ∈ (f x : Set X) ∩ A := mem_inter hyf (mem_isolatedPoints_iff.mp y.2).1
    exact (hf_sub x hy.symm).symm
  haveI : Countable (countableBasis X) := (countable_countableBasis X).to_subtype
  exact hf_inj.countable.to_set

theorem countable_isolated_layer {s : Set X} :
    ∀ (a : ↑(Iio (setCBRank s))), (isolatedPoints (sᵈ[↑a])).Countable := fun _ =>
      countable_isolatedPoints _

/-- Only countably many successor stages can have a nonempty CB layer. -/
theorem countable_strictDropStages {s : Set X} (hs : IsClosed s) :
    Countable {a : Ordinal.{u} | (isolatedPoints (sᵈ[a])).Nonempty} := by
  classical
  let I := {a : Ordinal.{u} | (isolatedPoints (sᵈ[a])).Nonempty}
  have h_basis : ∀ (a : I),
      ∃ (x : isolatedPoints (sᵈ[a])), ∃ U : countableBasis X,
      x.1 ∈ (U : Set X) ∧ sᵈ[a] ∩ U ⊆ {x.1} := by
    intro a
    obtain ⟨x,hx⟩ := a.2
    exists ⟨x,hx⟩
    obtain ⟨U,hxU,hsU⟩ := exists_countableBasis_of_mem_isolatedPoints hx
    refine ⟨U,mem_preimage.mp hxU,?_⟩
    simp only [subset_singleton_iff, mem_inter_iff, and_imp] at ⊢ hsU
    intro y hy hy'
    exact hsU y hy hy'
  choose f g hfg_in hfg_sub using h_basis
  have hg_inj : Function.Injective g := by
    intro a b hab
    rw [Subtype.ext_iff]
    wlog hlt : a < b generalizing a b
    · push_neg at hlt
      rcases lt_or_eq_of_le hlt with h | rfl
      · exact (this hab.symm h).symm
      rfl
    have hfb : (f b).1 ∈ sᵈ[↑a] ∩ ↑(g a) := by
      refine ⟨?_,?_⟩
      · exact iteratedDerivedSet_antitone hs (le_of_lt hlt) <|
          (mem_of_mem_inter_left (f b).2)
      · simpa [hab] using hfg_in b
    have hfab : (f a).1 = (f b).1 := by
      simpa using (hfg_sub a hfb).symm
    have hfa : (f a).1 ∈ derivedSet sᵈ[a] := by
      rw [hfab, ← iteratedDerivedSet_succ']
      exact iteratedDerivedSet_antitone hs (Order.add_one_le_iff.mpr hlt) <|
        (mem_of_mem_inter_left (f b).2)
    exact False.elim <| (f a).2.2 hfa
  haveI : Countable (countableBasis X) := (countable_countableBasis X).to_subtype
  exact hg_inj.countable.to_set

theorem countable_setCBRank {s : Set X} (hs : IsClosed s) :
    Countable ↑(Iio (setCBRank s)) := by
  -- Rewrite `a < setCBRank s` as nonemptiness of the `a`-th layer.
  simp only [countable_coe_iff]
  suffices heq : Iio (setCBRank s) = {a : Ordinal.{u} | (isolatedPoints (sᵈ[a])).Nonempty} by
    simpa [heq] using countable_strictDropStages hs
  ext x
  exact lt_setCBRank_iff_nonempty_layer hs

theorem countable_diff_perfectKernel {s : Set X} (hs : IsClosed s) :
    (s \ perfectKernel.{u} s).Countable := by
  rw [diff_perfectKernel_eq_iUnion_layers hs]
  haveI := countable_setCBRank hs
  refine countable_iUnion_iff.mpr ?_
  exact countable_isolated_layer

/--
The Cantor-Bendixson decomposition theorem in second countable spaces:
the scattered part is countable, and the perfect part is `perfectKernel s`.
-/
theorem exists_countable_union_perfectKernel_of_isClosed {s : Set X} (hs : IsClosed s) :
    ∃ V : Set X, V.Countable ∧ Perfect (perfectKernel.{u} s) ∧
      s = V ∪ perfectKernel.{u} s := by
  exists (s \ perfectKernel.{u} s)
  refine ⟨countable_diff_perfectKernel hs,
    perfect_perfectKernel hs,
    Eq.symm (diff_union_of_subset (perfectKernel_subset s))⟩

theorem countable_setOf_cbRank_lt_top {s : Set X} (hs : IsClosed s) :
    (↑{x : s | cbRank.{u} s x < ⊤} : Set X).Countable := by
  rw [setOf_cbRank_lt_top_eq_diff_perfectKernel]
  exact countable_diff_perfectKernel hs

end SecondCountable

end

end CantorBendixson
