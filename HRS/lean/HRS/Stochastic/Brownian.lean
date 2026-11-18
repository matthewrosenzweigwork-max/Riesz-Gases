import HRS.Stochastic.Filtration

/-!
# Brownian motion relative to a filtration

Package SI-01, part 1.  A family `W : ℝ≥0 → Ω → ι → ℝ` of `card ι` Brownian motions relative to
a filtration `ℱ : Filtration ℝ mΩ` (`IsBrownianFiltration`): adapted, everywhere continuous,
`W 0 = 0`, and for `s ≤ t` the increment `W t - W s` is independent of `ℱ s` with law
`N(0, (t - s) I)`.

The index set `ι` of the coordinates is an arbitrary `Fintype` (the task's `Fin n` is the case
`ι = Fin n`; the particle system of `HRS/Dynamics/Setup.lean` uses `ι = Fin N × Fin d`, see
`HRS/Stochastic/Bridge.lean`), so no re-indexing is ever needed.

Main statements:
* `IsBrownianFiltration.isBrownianReal`, `IsBrownianFiltration.iIndepFun_coord`: each coordinate is
  a Mathlib Brownian motion and the coordinates are jointly independent (this recovers
  `HRS.IsVectorBrownian`, see `Bridge.lean`).
* `IsBrownianFiltration.martingale`, `martingale_sq_sub`, `martingale_mul`: `W^k`, `(W^k)² - t`
  and `W^k W^l` (`k ≠ l`) are martingales over real time (with `W` frozen at `0` on `(-∞, 0]`).
* `exists_isBrownianFiltration`: from coordinatewise Brownian motions, jointly independent and
  independent of a measurable initial datum `X₀`, one obtains an everywhere continuous
  measurable modification `W'` and the augmented generated filtration
  `generatedFiltration P X₀ _ W' _`, for which `IsBrownianFiltration` holds and `X₀` is
  `ℱ t`-measurable for all `t`.  (Source: the particle system `H:eq:intro-particles`, M L170-178,
  "independent Brownian motions, independent of the initial configuration".)
* `tendsto_sumIncrements_sq`: quadratic variation of Brownian motion in `L²` along partitions
  with mesh `→ 0` (the only pathwise quadratic-variation input used by Itô's formula).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]

/-- `W` is a family of `card ι` independent standard Brownian motions relative to `ℱ`
(a "Brownian filtration"): `ℱ` contains the null sets, `W t` is `ℱ t`-measurable, paths are
everywhere continuous with `W 0 = 0`, and for `s ≤ t` the increment `W t - W s` is independent of
`ℱ s` and distributed as `N(0, (t - s) I_ι)`. -/
structure IsBrownianFiltration (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ) :
    Prop where
  complete : IsCompleteFiltration P ℱ
  adapted : ∀ t : ℝ≥0, Measurable[ℱ t] (W t)
  zero : ∀ ω, W 0 ω = 0
  cont : ∀ ω, Continuous fun t => W t ω
  indep_incr : ∀ s t : ℝ≥0, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance) (ℱ s) P
  gaussian_incr : ∀ s t : ℝ≥0, s ≤ t →
    HasLaw (fun ω => W t ω - W s ω) (Measure.pi fun _ : ι => gaussianReal 0 (t - s)) P

/-! ### Gaussian moments -/

lemma integral_sq_gaussianReal_zero (v : ℝ≥0) : ∫ x, x ^ 2 ∂gaussianReal 0 v = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (by fun_prop)] at h
  simpa [integral_id_gaussianReal] using h

lemma integral_pow_four_gaussianReal_zero (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  have h := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 v) (by
    rw [integrableExpSet_id_gaussianReal]; simp) 4
  rw [mgf_id_gaussianReal] at h
  simp only [zero_mul, zero_add] at h
  have hd : ∀ (p p' : ℝ → ℝ), (∀ t, HasDerivAt p (p' t) t) → ∀ t,
      HasDerivAt (fun t => p t * Real.exp (v * t ^ 2 / 2))
        ((p' t + p t * (v * t)) * Real.exp (v * t ^ 2 / 2)) t := by
    intro p p' hp t
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (v * t ^ 2 / 2))
        (Real.exp (v * t ^ 2 / 2) * (v * t)) t := by
      have : HasDerivAt (fun t : ℝ => v * t ^ 2 / 2) (v * t) t := by
        have := (((hasDerivAt_pow 2 t).const_mul (v:ℝ)).div_const 2)
        convert this using 1
        simp; ring
      exact this.exp
    convert (hp t).mul h1 using 1
    ring
  have key : ∀ (p p' : ℝ → ℝ), (∀ t, HasDerivAt p (p' t) t) →
      deriv (fun t => p t * Real.exp (v * t ^ 2 / 2)) =
        fun t => (p' t + p t * (v * t)) * Real.exp (v * t ^ 2 / 2) := by
    intro p p' hp; funext t; exact (hd p p' hp t).deriv
  have e0 : iteratedDeriv 1 (fun t : ℝ => Real.exp (v * t ^ 2 / 2)) =
      fun t => (v * t) * Real.exp (v * t ^ 2 / 2) := by
    rw [iteratedDeriv_one]
    have := key (fun _ => 1) (fun _ => 0) (fun t => hasDerivAt_const t 1)
    simpa using this
  have e1 : iteratedDeriv 2 (fun t : ℝ => Real.exp (v * t ^ 2 / 2)) =
      fun t => (v + v^2 * t^2) * Real.exp (v * t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, e0]
    have := key (fun t => v * t) (fun _ => v) (fun t => by simpa using (hasDerivAt_id t).const_mul (v:ℝ))
    rw [this]; funext t; ring
  have e2 : iteratedDeriv 3 (fun t : ℝ => Real.exp (v * t ^ 2 / 2)) =
      fun t => (3 * v^2 * t + v^3 * t^3) * Real.exp (v * t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, e1]
    have := key (fun t => v + v^2 * t^2) (fun t => 2 * v^2 * t) (fun t => by
      have := ((hasDerivAt_pow 2 t).const_mul (v^2:ℝ)).const_add (v:ℝ)
      exact this.congr_deriv (by simp; ring))
    rw [this]; funext t; ring
  have e3 : iteratedDeriv 4 (fun t : ℝ => Real.exp (v * t ^ 2 / 2)) 0 = 3 * v ^ 2 := by
    rw [iteratedDeriv_succ, e2]
    have := key (fun t => 3 * v^2 * t + v^3 * t^3) (fun t => 3 * v^2 + 3 * v^3 * t^2) (fun t => by
      have := (((hasDerivAt_id t).const_mul (3 * v^2:ℝ))).add ((hasDerivAt_pow 3 t).const_mul (v^3:ℝ))
      exact this.congr_deriv (by simp; ring))
    rw [this]; simp
  rw [e3] at h
  simpa using h.symm


/-! ### Independence lemmas for σ-algebras -/

lemma iIndepFun_of_indep_prefix {ι : Type*} [LinearOrder ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ∀ i, Ω → β i)
    (h : ∀ i, Indep (MeasurableSpace.comap (f i) inferInstance)
      (⨆ j < i, MeasurableSpace.comap (f j) inferInstance) P) : iIndepFun f P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro sets _; simp
  | insert a s ha ih =>
    intro sets hsets
    have haS : a ∉ s := fun hmem => lt_irrefl _ (ha a hmem)
    rw [Finset.prod_insert haS, Finset.set_biInter_insert,
      ← ih (fun i hi => hsets i (Finset.mem_insert_of_mem hi))]
    have h1 : MeasurableSet[MeasurableSpace.comap (f a) inferInstance] (f a ⁻¹' sets a) :=
      ⟨sets a, hsets a (Finset.mem_insert_self _ _), rfl⟩
    have h2 : MeasurableSet[⨆ j < a, MeasurableSpace.comap (f j) inferInstance]
        (⋂ i ∈ s, f i ⁻¹' sets i) := by
      refine Finset.measurableSet_biInter s fun i hi => ?_
      have : MeasurableSet[MeasurableSpace.comap (f i) inferInstance] (f i ⁻¹' sets i) :=
        ⟨sets i, hsets i (Finset.mem_insert_of_mem hi), rfl⟩
      exact (le_iSup₂_of_le (f := fun j (_ : j < a) => MeasurableSpace.comap (f j) inferInstance)
        i (ha i hi) le_rfl) _ this
    exact ((h a).indepSet_of_measurableSet h1 h2).measure_inter_eq_mul


lemma iIndep_sup_of_indep_iSup {ι : Type*} [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ι → MeasurableSpace Ω) (hA : ∀ k, A k ≤ mΩ) (hB : ∀ k, B k ≤ mΩ)
    (iA : iIndep A P) (iB : iIndep B P) (h : Indep (⨆ k, A k) (⨆ k, B k) P) :
    iIndep (fun k => A k ⊔ B k) P := by
  let π : ι → Set (Set Ω) := fun k => {s | ∃ a b, MeasurableSet[A k] a ∧ MeasurableSet[B k] b ∧
    s = a ∩ b}
  refine iIndepSets.iIndep (fun k => sup_le (hA k) (hB k)) π ?_ ?_ ?_
  · intro k s hs t ht _
    obtain ⟨a, b, ha, hb, rfl⟩ := hs
    obtain ⟨a', b', ha', hb', rfl⟩ := ht
    exact ⟨a ∩ a', b ∩ b', ha.inter ha', hb.inter hb', by ext; simp; tauto⟩
  · intro k
    apply le_antisymm
    · refine sup_le (fun a ha => MeasurableSpace.measurableSet_generateFrom ⟨a, Set.univ, ha,
        MeasurableSet.univ, by simp⟩) (fun b hb => MeasurableSpace.measurableSet_generateFrom
        ⟨Set.univ, b, MeasurableSet.univ, hb, by simp⟩)
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨a, b, ha, hb, rfl⟩
      exact (le_sup_left (a := A k) (b := B k) _ ha).inter (le_sup_right (a := A k) (b := B k) _ hb)
  · rw [iIndepSets_iff]
    intro S f hf
    choose! a b ha hb hab using hf
    have hAS : MeasurableSet[⨆ k, A k] (⋂ i ∈ S, a i) :=
      Finset.measurableSet_biInter S fun i hi => (le_iSup A i) _ (ha i hi)
    have hBS : MeasurableSet[⨆ k, B k] (⋂ i ∈ S, b i) :=
      Finset.measurableSet_biInter S fun i hi => (le_iSup B i) _ (hb i hi)
    have e : (⋂ i ∈ S, f i) = (⋂ i ∈ S, a i) ∩ (⋂ i ∈ S, b i) := by
      ext x; simp only [Set.mem_iInter, Set.mem_inter_iff]
      constructor
      · intro hx; exact ⟨fun i hi => by have := hx i hi; rw [hab i hi] at this; exact this.1,
          fun i hi => by have := hx i hi; rw [hab i hi] at this; exact this.2⟩
      · intro hx i hi; rw [hab i hi]; exact ⟨hx.1 i hi, hx.2 i hi⟩
    rw [e, (h.indepSet_of_measurableSet hAS hBS).measure_inter_eq_mul,
      iA.meas_biInter ha, iB.meas_biInter hb, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hab i hi]
    have hi1 : MeasurableSet[⨆ k, A k] (a i) := (le_iSup A i) _ (ha i hi)
    have hi2 : MeasurableSet[⨆ k, B k] (b i) := (le_iSup B i) _ (hb i hi)
    exact ((h.indepSet_of_measurableSet hi1 hi2).measure_inter_eq_mul).symm


section
open Classical in
lemma iSup_eq_generateFrom_iInter {ι : Type*} [Finite ι] (Y : ι → MeasurableSpace Ω) :
    (⨆ k, Y k) = MeasurableSpace.generateFrom
      {s | ∃ a : ι → Set Ω, (∀ k, MeasurableSet[Y k] (a k)) ∧ s = ⋂ k, a k} := by
  apply le_antisymm
  · refine iSup_le fun k a ha => MeasurableSpace.measurableSet_generateFrom ?_
    refine ⟨fun j => if j = k then a else Set.univ, fun j => ?_, ?_⟩
    · by_cases hj : j = k
      · subst hj; simpa using ha
      · simp [hj]
    · ext x; simp only [Set.mem_iInter]
      constructor
      · intro hx j; by_cases hj : j = k
        · subst hj; simpa using hx
        · simp [hj]
      · intro hx; simpa using hx k
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨a, ha, rfl⟩
    exact MeasurableSet.iInter fun k => (le_iSup Y k) _ (ha k)

lemma isPiSystem_iInter {ι : Type*} (Y : ι → MeasurableSpace Ω) :
    IsPiSystem {s | ∃ a : ι → Set Ω, (∀ k, MeasurableSet[Y k] (a k)) ∧ s = ⋂ k, a k} := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩ _
  refine ⟨fun k => a k ∩ a' k, fun k => (ha k).inter (ha' k), ?_⟩
  ext x; simp only [Set.mem_iInter, Set.mem_inter_iff]
  exact ⟨fun h k => ⟨h.1 k, h.2 k⟩, fun h => ⟨fun k => (h k).1, fun k => (h k).2⟩⟩
end

lemma indep_iSup_of_pairs {ι : Type*} [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (C Y Z : ι → MeasurableSpace Ω) (hCle : ∀ k, C k ≤ mΩ)
    (hC : iIndep C P) (hY : ∀ k, Y k ≤ C k) (hZ : ∀ k, Z k ≤ C k)
    (hYZ : ∀ k, Indep (Y k) (Z k) P) :
    Indep (⨆ k, Y k) (⨆ k, Z k) P := by
  refine IndepSets.indep (iSup_le fun k => (hY k).trans (hCle k))
    (iSup_le fun k => (hZ k).trans (hCle k)) (isPiSystem_iInter Y) (isPiSystem_iInter Z)
    (iSup_eq_generateFrom_iInter Y) (iSup_eq_generateFrom_iInter Z) ?_
  rw [IndepSets_iff]
  rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  have e : (⋂ k, a k) ∩ (⋂ k, b k) = ⋂ k, (a k ∩ b k) := by
    ext x; simp only [Set.mem_iInter, Set.mem_inter_iff]
    exact ⟨fun h k => ⟨h.1 k, h.2 k⟩, fun h => ⟨fun k => (h k).1, fun k => (h k).2⟩⟩
  have hab : ∀ k, P (a k ∩ b k) = P (a k) * P (b k) := fun k =>
    ((hYZ k).indepSet_of_measurableSet (ha k) (hb k)).measure_inter_eq_mul
  have hYC : ∀ k, MeasurableSet[C k] (a k) := fun k => (hY k) _ (ha k)
  have hZC : ∀ k, MeasurableSet[C k] (b k) := fun k => (hZ k) _ (hb k)
  rw [e, hC.meas_iInter (fun k => (hYC k).inter (hZC k)), hC.meas_iInter hYC,
    hC.meas_iInter hZC, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => hab k


lemma indep_sup_right_of_indep {M0 M1 M2 : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω}
    (P : Measure Ω)
    [IsProbabilityMeasure P] (h0 : M0 ≤ _mΩ) (h1 : M1 ≤ _mΩ) (h2 : M2 ≤ _mΩ)
    (h12 : Indep M1 M2 P) (h0_12 : Indep M0 (M1 ⊔ M2) P) : Indep M1 (M0 ⊔ M2) P := by
  let p2 : Set (Set Ω) := {s | ∃ a b, MeasurableSet[M0] a ∧ MeasurableSet[M2] b ∧ s = a ∩ b}
  refine IndepSets.indep h1 (sup_le h0 h2) (p1 := {s | MeasurableSet[M1] s}) (p2 := p2)
    (fun s hs t ht _ => @MeasurableSet.inter Ω M1 _ _ hs ht) ?_
    (@MeasurableSpace.generateFrom_measurableSet Ω M1).symm ?_ ?_
  · rintro _ ⟨a, b, ha, hb, rfl⟩ _ ⟨a', b', ha', hb', rfl⟩ _
    exact ⟨a ∩ a', b ∩ b', @MeasurableSet.inter Ω M0 _ _ ha ha',
      @MeasurableSet.inter Ω M2 _ _ hb hb', by ext; simp; tauto⟩
  · apply le_antisymm
    · refine sup_le (fun a ha => MeasurableSpace.measurableSet_generateFrom ⟨a, Set.univ, ha,
        @MeasurableSet.univ Ω M2, by simp⟩) (fun b hb => MeasurableSpace.measurableSet_generateFrom
        ⟨Set.univ, b, @MeasurableSet.univ Ω M0, hb, by simp⟩)
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨a, b, ha, hb, rfl⟩
      exact @MeasurableSet.inter Ω (M0 ⊔ M2) _ _ (le_sup_left (a := M0) (b := M2) _ ha)
        (le_sup_right (a := M0) (b := M2) _ hb)
  · rw [IndepSets_iff]
    rintro m _ hm ⟨a, b, ha, hb, rfl⟩
    have hmb : MeasurableSet[M1 ⊔ M2] (m ∩ b) :=
      @MeasurableSet.inter Ω (M1 ⊔ M2) _ _ (le_sup_left (a := M1) (b := M2) _ hm)
        (le_sup_right (a := M1) (b := M2) _ hb)
    have hb' : MeasurableSet[M1 ⊔ M2] b := le_sup_right (a := M1) (b := M2) _ hb
    have e : m ∩ (a ∩ b) = a ∩ (m ∩ b) := by ext; simp; tauto
    rw [e, (h0_12.indepSet_of_measurableSet ha hmb).measure_inter_eq_mul,
      (h12.indepSet_of_measurableSet hm hb).measure_inter_eq_mul,
      (h0_12.indepSet_of_measurableSet ha hb').measure_inter_eq_mul]
    ring

lemma indep_of_null_or_conull {N M : MeasurableSpace Ω} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (hN : ∀ s, MeasurableSet[N] s → MeasurableSet s ∧ (P s = 0 ∨ P sᶜ = 0))
    (_hM : M ≤ _mΩ) : Indep N M P := by
  rw [Indep_iff]
  intro s t hs ht
  obtain ⟨hsm, h | h⟩ := hN s hs
  · rw [h, zero_mul]; exact measure_mono_null Set.inter_subset_left h
  · have : P s = 1 := by
      have := prob_compl_eq_zero_iff hsm |>.1 h
      exact this
    rw [this, one_mul]
    have : s =ᵐ[P] Set.univ := by
      rw [ae_eq_univ]; exact h
    rw [measure_congr (this.inter (ae_eq_refl t))]; simp


lemma lintegral_enorm_sq_sub_sum {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Fin n → Ω → ℝ) (hU : ∀ i, MemLp (U i) 2 P)
    (hind : Pairwise fun i j => IndepFun (U i) (U j) P) (c : ℝ)
    (hc : ∑ i, ∫ ω, U i ω ∂P = c) :
    ∫⁻ ω, ‖∑ i, U i ω - c‖ₑ ^ 2 ∂P = ENNReal.ofReal (∑ i, variance (U i) P) := by
  have hS : MemLp (fun ω => ∑ i, U i ω) 2 P := memLp_finsetSum Finset.univ fun i _ => hU i
  have hmean : ∫ ω, ∑ i, U i ω ∂P = c := by
    rw [integral_finsetSum _ fun i _ => (hU i).integrable one_le_two, hc]
  have h1 : ∫⁻ ω, ‖∑ i, U i ω - c‖ₑ ^ 2 ∂P = evariance (fun ω => ∑ i, U i ω) P := by
    simp only [evariance, hmean]
  rw [h1, ← ofReal_variance hS]
  congr 1
  have := IndepFun.variance_sum (X := U) (s := Finset.univ) (μ := P) (fun i _ => hU i)
    (fun i _ j _ hij => hind hij)
  simpa [Finset.sum_fn] using this



section PartitionLemmas
namespace Partition
variable {a b : ℝ} (π : Partition a b)

theorem pt_nonneg (ha : 0 ≤ a) (i : Fin (π.n + 1)) : 0 ≤ π.pt i := by
  have := π.mono (Fin.zero_le i)
  rw [π.first] at this
  linarith

theorem pt_le (i : Fin π.n) : π.pt i.castSucc ≤ π.pt i.succ := π.mono (Fin.castSucc_le_succ i)

theorem sum_telescope (n : ℕ) (f : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have := ih (fun i => f i.castSucc)
    simp only [Fin.succ_castSucc] at this ⊢
    rw [this]
    simp

theorem sum_length : ∑ i : Fin π.n, (π.pt i.succ - π.pt i.castSucc) = b - a := by
  rw [sum_telescope, π.first, π.last]

theorem length_le_mesh (i : Fin π.n) : π.pt i.succ - π.pt i.castSucc ≤ π.mesh := by
  unfold mesh
  have := Finset.le_sup' (fun j : Fin (π.n + 1) =>
    if h : (j : ℕ) < π.n then π.pt ⟨j + 1, by omega⟩ - π.pt j else 0) (Finset.mem_univ i.castSucc)
  convert this using 1
  simp
  rfl

end Partition

end PartitionLemmas

namespace IsBrownianFiltration

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}

theorem measurable (hW : IsBrownianFiltration P ℱ W) (t : ℝ≥0) : Measurable (W t) :=
  (hW.adapted t).mono (ℱ.le _) le_rfl

theorem measurable_coord (hW : IsBrownianFiltration P ℱ W) (t : ℝ≥0) (k : ι) :
    Measurable fun ω => W t ω k :=
  (measurable_pi_apply k).comp (hW.measurable t)


/-! #### Laws of increments -/

/-- Each coordinate of an increment is `N(0, t - s)`. -/
theorem hasLaw_incr_coord (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {s t : ℝ≥0} (hst : s ≤ t) (k : ι) :
    HasLaw (fun ω => W t ω k - W s ω k) (gaussianReal 0 (t - s)) P :=
  ((measurePreserving_eval (fun _ : ι => gaussianReal 0 (t - s)) k).hasLaw).comp
    (hW.gaussian_incr s t hst)

/-- Each coordinate `W t k` is `N(0, t)`. -/
theorem hasLaw_coord (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    (t : ℝ≥0) (k : ι) : HasLaw (fun ω => W t ω k) (gaussianReal 0 t) P := by
  have h := hasLaw_incr_coord hW (by simp : (0 : ℝ≥0) ≤ t) k
  simpa [hW.zero] using h

/-- The coordinates of one increment are independent. -/
theorem iIndepFun_incr_coords (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {s t : ℝ≥0} (hst : s ≤ t) : iIndepFun (fun (k : ι) ω => W t ω k - W s ω k) P :=
  (iIndepFun_iff_hasLaw_pi_pi (hasLaw_incr_coord hW hst)).2 (hW.gaussian_incr s t hst)

theorem memLp_coord (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P] (t : ℝ≥0) (k : ι)
    {p : ℝ≥0∞} (hp : p ≠ ∞) : MemLp (fun ω => W t ω k) p P :=
  (hasLaw_coord hW t k).memLp (memLp_id_gaussianReal' p hp)

theorem memLp_incr_coord (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {s t : ℝ≥0} (hst : s ≤ t) (k : ι) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun ω => W t ω k - W s ω k) p P :=
  (hasLaw_incr_coord hW hst k).memLp (memLp_id_gaussianReal' p hp)

theorem integral_incr_coord (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {s t : ℝ≥0} (hst : s ≤ t) (k : ι) : ∫ ω, (W t ω k - W s ω k) ∂P = 0 := by
  have := (hasLaw_incr_coord hW hst k).integral_eq
  simpa [integral_id_gaussianReal] using this

/-- The increment `W t - W s` is independent of every `ℱ s`-measurable random variable. -/
theorem indepFun_incr (hW : IsBrownianFiltration P ℱ W) {s t : ℝ≥0} (hst : s ≤ t)
    {E : Type*} [MeasurableSpace E] {Z : Ω → E} (hZ : Measurable[ℱ s] Z) :
    IndepFun (fun ω => W t ω - W s ω) Z P :=
  indep_of_indep_of_le_right (hW.indep_incr s t hst) hZ.comap_le

theorem measurable_coord_of_le (hW : IsBrownianFiltration P ℱ W) {r s : ℝ≥0} (hrs : r ≤ s) (k : ι) :
    Measurable[ℱ (s : ℝ)] (fun ω => W r ω k) :=
  (measurable_pi_apply k).comp ((hW.adapted r).mono (ℱ.mono (by exact_mod_cast hrs)) le_rfl)

omit [Fintype ι] in
theorem comap_incr_coord_le_comap (s t : ℝ≥0) (k : ι) :
    MeasurableSpace.comap (fun ω => W t ω k - W s ω k) inferInstance ≤
      MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance :=
  ((measurable_pi_apply k).comp (comap_measurable (fun ω => W t ω - W s ω))).comap_le

theorem comap_incr_coord_le (hW : IsBrownianFiltration P ℱ W) {r s : ℝ≥0} (hrs : r ≤ s) (k : ι) :
    MeasurableSpace.comap (fun ω => W s ω k - W r ω k) inferInstance ≤ ℱ (s : ℝ) :=
  Measurable.comap_le ((measurable_coord_of_le hW le_rfl k).sub (measurable_coord_of_le hW hrs k))

theorem comap_coord_le (hW : IsBrownianFiltration P ℱ W) {r s : ℝ≥0} (hrs : r ≤ s) (k : ι) :
    MeasurableSpace.comap (fun ω => W r ω k) inferInstance ≤ ℱ (s : ℝ) :=
  Measurable.comap_le (measurable_coord_of_le hW hrs k)


set_option warn.classDefReducibility false in
/-- The σ-algebra generated by the coordinate `k` of `W` at the times in `s`. -/
def coordSigma (W : ℝ≥0 → Ω → ι → ℝ) (s : Finset ℝ≥0) (k : ι) : MeasurableSpace Ω :=
  ⨆ r ∈ s, MeasurableSpace.comap (fun ω => W r ω k) inferInstance

omit [Fintype ι] in
theorem coordSigma_mono (W : ℝ≥0 → Ω → ι → ℝ) {s s' : Finset ℝ≥0} (h : s ⊆ s') (k : ι) :
    coordSigma W s k ≤ coordSigma W s' k :=
  iSup₂_le fun r hr => le_iSup₂_of_le (f := fun r (_ : r ∈ s') =>
    MeasurableSpace.comap (fun ω => W r ω k) inferInstance) r (h hr) le_rfl

theorem iIndep_coordSigma (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    (s : Finset ℝ≥0) : iIndep (fun k => coordSigma W s k) P := by
  induction s using Finset.induction_on_max with
  | empty =>
    refine iIndep_of_iIndep_of_le (iIndepFun_incr_coords hW (le_refl (0 : ℝ≥0))).iIndep fun k => ?_
    simp [coordSigma]
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · have hi := (iIndepFun_incr_coords hW (by positivity : (0 : ℝ≥0) ≤ a)).iIndep
      refine iIndep_of_iIndep_of_le hi fun k => ?_
      refine iSup₂_le fun r hr => ?_
      have hr' : r = a := by simpa using hr
      subst hr'
      have : (fun ω => W r ω k) = fun ω => W r ω k - W 0 ω k := by funext ω; simp [hW.zero]
      rw [this]
    · set m := s.max' hs with hm
      have hmle : ∀ r ∈ s, r ≤ m := fun r hr => s.le_max' r hr
      have hma : m ≤ a := (ha m (s.max'_mem hs)).le
      have hB := (iIndepFun_incr_coords hW hma).iIndep
      have hAle : ∀ k, coordSigma W s k ≤ ℱ (m : ℝ) := fun k =>
        iSup₂_le fun r hr => comap_coord_le hW (hmle r hr) k
      have hBle : ∀ k, MeasurableSpace.comap (fun ω => W a ω k - W m ω k) inferInstance ≤ mΩ :=
        fun k => (comap_incr_coord_le_comap m a k).trans
          (Measurable.comap_le ((hW.measurable a).sub (hW.measurable m)))
      have hG := iIndep_sup_of_indep_iSup P (coordSigma W s)
        (fun k => MeasurableSpace.comap (fun ω => W a ω k - W m ω k) inferInstance)
        (fun k => (hAle k).trans (ℱ.le _)) hBle ih hB ?_
      · refine iIndep_of_iIndep_of_le hG fun k => ?_
        refine iSup₂_le fun r hr => ?_
        rcases Finset.mem_insert.1 hr with rfl | hr
        · have h1 : Measurable[coordSigma W s k ⊔ MeasurableSpace.comap
              (fun ω => W r ω k - W m ω k) inferInstance] (fun ω => W r ω k - W m ω k) :=
            (comap_measurable (fun ω => W r ω k - W m ω k)).mono le_sup_right le_rfl
          have h2 : Measurable[coordSigma W s k ⊔ MeasurableSpace.comap
              (fun ω => W r ω k - W m ω k) inferInstance] (fun ω => W m ω k) :=
            (comap_measurable (fun ω => W m ω k)).mono
              (le_sup_of_le_left (le_iSup₂_of_le (f := fun r (_ : r ∈ s) =>
                MeasurableSpace.comap (fun ω => W r ω k) inferInstance) m (s.max'_mem hs) le_rfl))
              le_rfl
          have h3 := h1.add h2
          have : (fun ω => W r ω k) = (fun ω => W r ω k - W m ω k) + (fun ω => W m ω k) := by
            funext ω; simp
          rw [this]
          exact h3.comap_le
        · exact le_sup_of_le_left (le_iSup₂_of_le (f := fun r (_ : r ∈ s) =>
            MeasurableSpace.comap (fun ω => W r ω k) inferInstance) r hr le_rfl)
      · exact indep_of_indep_of_le (hW.indep_incr m a hma).symm (iSup_le hAle)
          (iSup_le fun k => comap_incr_coord_le_comap m a k)

omit [Fintype ι] in
theorem comap_path_eq (W : ℝ≥0 → Ω → ι → ℝ) (k : ι) :
    MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => W t ω k) inferInstance =
      ⨆ s : Finset ℝ≥0, coordSigma W s k := by
  apply le_antisymm
  · have : MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => W t ω k) inferInstance =
        ⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => W t ω k) inferInstance := by
      rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      simp only [MeasurableSpace.comap_comp]
      rfl
    rw [this]
    refine iSup_le fun t => le_iSup_of_le ({t} : Finset ℝ≥0) ?_
    exact le_iSup₂_of_le (f := fun r (_ : r ∈ ({t} : Finset ℝ≥0)) =>
      MeasurableSpace.comap (fun ω => W r ω k) inferInstance) t (Finset.mem_singleton_self t) le_rfl
  · refine iSup_le fun s => iSup₂_le fun r _ => ?_
    exact ((measurable_pi_apply r).comp
      (comap_measurable (fun ω => fun t : ℝ≥0 => W t ω k))).comap_le


/-- Each coordinate is a Brownian motion in Mathlib's sense. -/
theorem isBrownianReal (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P] (k : ι) :
    IsBrownianReal (fun t ω => W t ω k) P := by
  have hinc : HasIndepIncrements (fun t ω => W t ω k) P := by
    intro n t ht
    refine iIndepFun_of_indep_prefix P _ (fun i => ?_)
    refine indep_of_indep_of_le (hW.indep_incr (t i.castSucc) (t i.succ)
      (ht (Fin.castSucc_le_succ i))) (comap_incr_coord_le_comap _ _ k) ?_
    refine iSup₂_le fun j hj => ?_
    exact (comap_incr_coord_le hW (ht (Fin.castSucc_le_succ j)) k).trans
      (ℱ.mono (by exact_mod_cast ht (Fin.succ_le_castSucc_iff.2 hj)))
  exact ⟨HasIndepIncrements.isPreBrownianReal_of_hasLaw (fun t => hasLaw_coord hW t k) hinc,
    Filter.Eventually.of_forall fun ω => (continuous_apply k).comp (hW.cont ω)⟩


/-- The coordinates are jointly independent (as processes). -/
theorem iIndepFun_coord (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P] :
    iIndepFun (fun (k : ι) ω => fun t : ℝ≥0 => W t ω k) P := by
  have hmeas : ∀ k, Measurable fun ω => fun t : ℝ≥0 => W t ω k := fun k =>
    Measurable.of_eval fun t => hW.measurable_coord t k
  refine iIndepSets.iIndep (fun k => (hmeas k).comap_le)
    (fun k => ⋃ s : Finset ℝ≥0, {A | MeasurableSet[coordSigma W s k] A}) ?_ ?_ ?_
  · intro k
    refine isPiSystem_iUnion_of_directed_le _ (fun s => ?_) ?_
    · intro A hA B hB _
      exact @MeasurableSet.inter Ω (coordSigma W s k) _ _ hA hB
    · intro s s'
      exact ⟨s ∪ s', fun A hA => coordSigma_mono W Finset.subset_union_left k _ hA,
        fun A hA => coordSigma_mono W Finset.subset_union_right k _ hA⟩
  · intro k
    exact (comap_path_eq W k).trans
      (MeasurableSpace.generateFrom_iUnion_measurableSet (fun s => coordSigma W s k)).symm
  · rw [iIndepSets_iff]
    intro S f hf
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hf
    choose! s hs using hf
    have := (iIndep_coordSigma hW (S.biUnion s)).meas_biInter (S := S) (s := f)
      (fun i hi => coordSigma_mono W (Finset.subset_biUnion_of_mem s hi) i _ (hs i hi))
    exact this

/-- `E[(W_t^k - W_s^k)²] = t - s`. -/
theorem integral_incr_sq (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {s t : ℝ≥0} (hst : s ≤ t) (k : ι) :
    ∫ ω, (W t ω k - W s ω k) ^ 2 ∂P = (t : ℝ) - s := by
  have := (hasLaw_incr_coord hW hst k).integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  rw [integral_sq_gaussianReal_zero, NNReal.coe_sub hst] at this
  exact this

/-- `E[(W_t^k - W_s^k)(W_t^l - W_s^l)] = 0` for `k ≠ l`. -/
theorem integral_incr_mul_of_ne (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {s t : ℝ≥0} (hst : s ≤ t) {k l : ι} (hkl : k ≠ l) :
    ∫ ω, (W t ω k - W s ω k) * (W t ω l - W s ω l) ∂P = 0 := by
  have hind := (iIndepFun_incr_coords hW hst).indepFun hkl
  have h := hind.integral_fun_mul_eq_mul_integral
    (hasLaw_incr_coord hW hst k).aemeasurable.aestronglyMeasurable
    (hasLaw_incr_coord hW hst l).aemeasurable.aestronglyMeasurable
  rw [h]
  have := integral_incr_coord hW hst k
  rw [this, zero_mul]

/-- `E[(W_t^k - W_s^k)^4] = 3 (t - s)²`. -/
theorem integral_incr_fourth (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {s t : ℝ≥0} (hst : s ≤ t) (k : ι) :
    ∫ ω, (W t ω k - W s ω k) ^ 4 ∂P = 3 * ((t : ℝ) - s) ^ 2 := by
  have := (hasLaw_incr_coord hW hst k).integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
  rw [integral_pow_four_gaussianReal_zero, NNReal.coe_sub hst] at this
  exact this

/-- Conditional mean of an increment given the past vanishes. -/
theorem condExp_incr (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {s t : ℝ≥0} (hst : s ≤ t) (k : ι) :
    P[fun ω => W t ω k - W s ω k | ℱ s] =ᵐ[P] 0 := by
  have hmeas : Measurable fun ω => W t ω - W s ω := (hW.measurable t).sub (hW.measurable s)
  have hm : StronglyMeasurable[MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance]
      (fun ω => W t ω k - W s ω k) :=
    Measurable.stronglyMeasurable
      ((measurable_pi_apply k).comp (comap_measurable (fun ω => W t ω - W s ω)))
  have h := condExp_indep_eq hmeas.comap_le (ℱ.le s) hm (hW.indep_incr s t hst)
  filter_upwards [h] with ω hω
  rw [hω, integral_incr_coord hW hst k]
  rfl

/-- Conditional second moments of increments given the past: `δ_{kl} (t - s)`. -/
theorem condExp_incr_mul [DecidableEq ι] (hW : IsBrownianFiltration P ℱ W)
    [IsProbabilityMeasure P] {s t : ℝ≥0} (hst : s ≤ t) (k l : ι) :
    P[fun ω => (W t ω k - W s ω k) * (W t ω l - W s ω l) | ℱ s] =ᵐ[P]
      fun _ => if k = l then ((t : ℝ) - s) else 0 := by
  have hmeas : Measurable fun ω => W t ω - W s ω := (hW.measurable t).sub (hW.measurable s)
  have hm : StronglyMeasurable[MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance]
      (fun ω => (W t ω k - W s ω k) * (W t ω l - W s ω l)) :=
    Measurable.stronglyMeasurable
      (((measurable_pi_apply k).comp (comap_measurable (fun ω => W t ω - W s ω))).mul
        ((measurable_pi_apply l).comp (comap_measurable (fun ω => W t ω - W s ω))))
  have h := condExp_indep_eq hmeas.comap_le (ℱ.le s) hm (hW.indep_incr s t hst)
  filter_upwards [h] with ω hω
  rw [hω]
  by_cases hkl : k = l
  · subst hkl
    simp only [ite_true]
    simpa [sq] using integral_incr_sq hW hst k
  · simp only [hkl, ite_false]
    exact integral_incr_mul_of_ne hW hst hkl

theorem adapted_ofNNRealTime_aux (hW : IsBrownianFiltration P ℱ W) :
    Adapted ℱ (ofNNRealTime W) := by
  intro t
  by_cases ht : 0 ≤ t
  · have h1 : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht
    have h := hW.adapted (Real.toNNReal t)
    rw [h1] at h
    exact h
  · have h1 : Real.toNNReal t = 0 := Real.toNNReal_of_nonpos (not_le.1 ht).le
    show Measurable[ℱ t] (W (Real.toNNReal t))
    rw [h1]
    have h2 : W 0 = fun _ => 0 := funext fun ω => hW.zero ω
    rw [h2]
    exact measurable_const

/-! #### Real-time increments -/

theorem indep_incr_real (hW : IsBrownianFiltration P ℱ W) {s t : ℝ} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun ω => ofNNRealTime W t ω - ofNNRealTime W s ω) inferInstance) (ℱ s) P :=
  indep_of_indep_of_le_right (hW.indep_incr _ _ (Real.toNNReal_le_toNNReal hst))
    (ℱ.mono (Real.le_coe_toNNReal s))

theorem measurable_ofNNRealTime_coord (hW : IsBrownianFiltration P ℱ W) (t : ℝ) (k : ι) :
    Measurable fun ω => ofNNRealTime W t ω k :=
  hW.measurable_coord _ k

omit [Fintype ι] in
theorem comapMeasurable_incr_real (s t : ℝ) (k : ι) :
    Measurable[MeasurableSpace.comap
      (fun ω => ofNNRealTime W t ω - ofNNRealTime W s ω) inferInstance]
      (fun ω => ofNNRealTime W t ω k - ofNNRealTime W s ω k) :=
  (measurable_pi_apply k).comp
    (comap_measurable (fun ω => ofNNRealTime W t ω - ofNNRealTime W s ω))

theorem le_comap_incr_real (hW : IsBrownianFiltration P ℱ W) (s t : ℝ) :
    MeasurableSpace.comap (fun ω => ofNNRealTime W t ω - ofNNRealTime W s ω) inferInstance ≤ mΩ :=
  Measurable.comap_le ((hW.measurable _).sub (hW.measurable _))

theorem integrable_coord_real (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    (t : ℝ) (k : ι) : Integrable (fun ω => ofNNRealTime W t ω k) P :=
  (memLp_coord hW _ k ENNReal.one_ne_top).integrable le_rfl

theorem memLp_two_coord_real (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    (t : ℝ) (k : ι) : MemLp (fun ω => ofNNRealTime W t ω k) 2 P :=
  memLp_coord hW _ k ENNReal.ofNat_ne_top

theorem memLp_two_incr_real (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {s t : ℝ} (hst : s ≤ t) (k : ι) :
    MemLp (fun ω => ofNNRealTime W t ω k - ofNNRealTime W s ω k) 2 P :=
  memLp_incr_coord hW (Real.toNNReal_le_toNNReal hst) k ENNReal.ofNat_ne_top

/-- Conditional mean of a real-time increment. -/
theorem condExp_incr_real (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {s t : ℝ} (hst : s ≤ t) (k : ι) :
    P[fun ω => ofNNRealTime W t ω k - ofNNRealTime W s ω k | ℱ s] =ᵐ[P] 0 := by
  have h := condExp_indep_eq (le_comap_incr_real hW s t) (ℱ.le s)
    (comapMeasurable_incr_real (W := W) s t k).stronglyMeasurable (indep_incr_real hW hst)
  filter_upwards [h] with ω hω
  rw [hω]
  exact integral_incr_coord hW (Real.toNNReal_le_toNNReal hst) k

/-- Conditional second moment of a real-time increment. -/
theorem condExp_incr_sq_real (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {s t : ℝ} (hst : s ≤ t) (k : ι) :
    P[fun ω => (ofNNRealTime W t ω k - ofNNRealTime W s ω k) ^ 2 | ℱ s] =ᵐ[P]
      fun _ => max t 0 - max s 0 := by
  have hm : StronglyMeasurable[MeasurableSpace.comap
      (fun ω => ofNNRealTime W t ω - ofNNRealTime W s ω) inferInstance]
      (fun ω => (ofNNRealTime W t ω k - ofNNRealTime W s ω k) ^ 2) :=
    ((comapMeasurable_incr_real (W := W) s t k).pow_const 2).stronglyMeasurable
  have h := condExp_indep_eq (le_comap_incr_real hW s t) (ℱ.le s) hm (indep_incr_real hW hst)
  filter_upwards [h] with ω hω
  rw [hω]
  have := integral_incr_sq hW (Real.toNNReal_le_toNNReal hst) k
  rw [Real.coe_toNNReal', Real.coe_toNNReal'] at this
  exact this

/-- Conditional product of two distinct real-time increments. -/
theorem condExp_incr_mul_real_of_ne (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {s t : ℝ} (hst : s ≤ t) {k l : ι} (hkl : k ≠ l) :
    P[fun ω => (ofNNRealTime W t ω k - ofNNRealTime W s ω k) *
      (ofNNRealTime W t ω l - ofNNRealTime W s ω l) | ℱ s] =ᵐ[P] 0 := by
  have hm : StronglyMeasurable[MeasurableSpace.comap
      (fun ω => ofNNRealTime W t ω - ofNNRealTime W s ω) inferInstance]
      (fun ω => (ofNNRealTime W t ω k - ofNNRealTime W s ω k) *
        (ofNNRealTime W t ω l - ofNNRealTime W s ω l)) :=
    ((comapMeasurable_incr_real (W := W) s t k).mul
      (comapMeasurable_incr_real (W := W) s t l)).stronglyMeasurable
  have h := condExp_indep_eq (le_comap_incr_real hW s t) (ℱ.le s) hm (indep_incr_real hW hst)
  filter_upwards [h] with ω hω
  rw [hω]
  exact integral_incr_mul_of_ne hW (Real.toNNReal_le_toNNReal hst) hkl

/-- Pulling an `ℱ s`-measurable factor out of the conditional expectation of an increment. -/
theorem condExp_mul_incr_real (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {s t : ℝ} (hst : s ≤ t) (k : ι) {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ s] g)
    (hgΔ : Integrable (fun ω => g ω * (ofNNRealTime W t ω k - ofNNRealTime W s ω k)) P) :
    P[fun ω => g ω * (ofNNRealTime W t ω k - ofNNRealTime W s ω k) | ℱ s] =ᵐ[P] 0 := by
  have hΔ : Integrable (fun ω => ofNNRealTime W t ω k - ofNNRealTime W s ω k) P :=
    (memLp_two_incr_real hW hst k).integrable one_le_two
  have h : P[fun ω => g ω * (ofNNRealTime W t ω k - ofNNRealTime W s ω k) | ℱ s] =ᵐ[P]
      g * P[fun ω => ofNNRealTime W t ω k - ofNNRealTime W s ω k | ℱ s] :=
    condExp_mul_of_stronglyMeasurable_left (μ := P) hg hgΔ hΔ
  filter_upwards [h, condExp_incr_real hW hst k] with ω h1 h2
  rw [h1, Pi.mul_apply, h2, Pi.zero_apply, mul_zero]

theorem stronglyMeasurable_ofNNRealTime_coord (hW : IsBrownianFiltration P ℱ W) (t : ℝ) (k : ι) :
    StronglyMeasurable[ℱ t] (fun ω => ofNNRealTime W t ω k) :=
  ((measurable_pi_apply k).comp (adapted_ofNNRealTime_aux hW t)).stronglyMeasurable

/-- `W^k` (frozen at `0` on negative times) is a martingale over real time. -/
theorem martingale (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P] (k : ι) :
    Martingale (fun (t : ℝ) ω => ofNNRealTime W t ω k) ℱ P := by
  refine ⟨fun t => stronglyMeasurable_ofNNRealTime_coord hW t k, fun s t hst => ?_⟩
  have hs := stronglyMeasurable_ofNNRealTime_coord hW s k
  have i1 : Integrable (fun ω => ofNNRealTime W t ω k - ofNNRealTime W s ω k) P :=
    (memLp_two_incr_real hW hst k).integrable one_le_two
  have i2 : Integrable (fun ω => ofNNRealTime W s ω k) P := integrable_coord_real hW s k
  have e1 := condExp_add i1 i2 (ℱ s) (μ := P)
  have e2 : P[fun ω => ofNNRealTime W s ω k | ℱ s] = fun ω => ofNNRealTime W s ω k :=
    condExp_of_stronglyMeasurable (ℱ.le s) hs i2
  have key : (fun ω => ofNNRealTime W t ω k) =
      (fun ω => ofNNRealTime W t ω k - ofNNRealTime W s ω k) +
        (fun ω => ofNNRealTime W s ω k) := by
    funext ω; simp
  beta_reduce
  rw [key]
  filter_upwards [e1, condExp_incr_real hW hst k] with ω h1 h2
  rw [h1, Pi.add_apply, h2, e2]
  simp

/-- `(W^k_t)² - t` is a martingale over real time (with `t ↦ max t 0`). -/
theorem martingale_sq_sub (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P] (k : ι) :
    Martingale (fun (t : ℝ) ω => ofNNRealTime W t ω k ^ 2 - max t 0) ℱ P := by
  refine ⟨fun t => ?_, fun s t hst => ?_⟩
  · exact ((stronglyMeasurable_ofNNRealTime_coord hW t k).pow 2).sub stronglyMeasurable_const
  have ha := stronglyMeasurable_ofNNRealTime_coord hW s k
  have hL2a := memLp_two_coord_real hW s k
  have hL2d := memLp_two_incr_real hW hst k
  have i1 : Integrable (fun ω => (ofNNRealTime W t ω k - ofNNRealTime W s ω k) ^ 2) P :=
    hL2d.integrable_sq
  have i2 : Integrable (fun ω => 2 * (ofNNRealTime W s ω k *
      (ofNNRealTime W t ω k - ofNNRealTime W s ω k))) P :=
    (hL2a.integrable_mul hL2d).const_mul 2
  have i3 : Integrable (fun ω => ofNNRealTime W s ω k ^ 2 - max t 0) P :=
    hL2a.integrable_sq.sub (integrable_const _)
  have i4 : Integrable (fun ω => ofNNRealTime W s ω k *
      (ofNNRealTime W t ω k - ofNNRealTime W s ω k)) P := hL2a.integrable_mul hL2d
  have e3 : P[fun ω => ofNNRealTime W s ω k ^ 2 - max t 0 | ℱ s] =
      fun ω => ofNNRealTime W s ω k ^ 2 - max t 0 :=
    condExp_of_stronglyMeasurable (ℱ.le s) ((ha.pow 2).sub stronglyMeasurable_const) i3
  have key : (fun ω => ofNNRealTime W t ω k ^ 2 - max t 0) =
      ((fun ω => (ofNNRealTime W t ω k - ofNNRealTime W s ω k) ^ 2) +
        (fun ω => 2 * (ofNNRealTime W s ω k *
          (ofNNRealTime W t ω k - ofNNRealTime W s ω k)))) +
        (fun ω => ofNNRealTime W s ω k ^ 2 - max t 0) := by
    funext ω; simp only [Pi.add_apply]; ring
  beta_reduce
  rw [key]
  have e1 := condExp_add (i1.add i2) i3 (ℱ s) (μ := P)
  have e2 := condExp_add i1 i2 (ℱ s) (μ := P)
  have e4 : P[fun ω => 2 * (ofNNRealTime W s ω k *
      (ofNNRealTime W t ω k - ofNNRealTime W s ω k)) | ℱ s] =ᵐ[P] 0 := by
    have := condExp_smul (μ := P) (2 : ℝ) (fun ω => ofNNRealTime W s ω k *
      (ofNNRealTime W t ω k - ofNNRealTime W s ω k)) (ℱ s)
    filter_upwards [this, condExp_mul_incr_real hW hst k ha i4] with ω h1 h2
    have h1' : P[fun ω => 2 * (ofNNRealTime W s ω k *
      (ofNNRealTime W t ω k - ofNNRealTime W s ω k)) | ℱ s] ω =
        2 * P[fun ω => ofNNRealTime W s ω k *
      (ofNNRealTime W t ω k - ofNNRealTime W s ω k) | ℱ s] ω := h1
    rw [h1', h2]; simp
  filter_upwards [e1, e2, condExp_incr_sq_real hW hst k, e4] with ω h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, e3]
  simp only [Pi.zero_apply]
  ring

/-- `W^k_t W^l_t` is a martingale for `k ≠ l`. -/
theorem martingale_mul (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P] {k l : ι}
    (hkl : k ≠ l) :
    Martingale (fun (t : ℝ) ω => ofNNRealTime W t ω k * ofNNRealTime W t ω l) ℱ P := by
  refine ⟨fun t => ?_, fun s t hst => ?_⟩
  · exact (stronglyMeasurable_ofNNRealTime_coord hW t k).mul
      (stronglyMeasurable_ofNNRealTime_coord hW t l)
  have hak := stronglyMeasurable_ofNNRealTime_coord hW s k
  have hal := stronglyMeasurable_ofNNRealTime_coord hW s l
  have hL2ak := memLp_two_coord_real hW s k
  have hL2al := memLp_two_coord_real hW s l
  have hL2dk := memLp_two_incr_real hW hst k
  have hL2dl := memLp_two_incr_real hW hst l
  have i1 : Integrable (fun ω => (ofNNRealTime W t ω k - ofNNRealTime W s ω k) *
      (ofNNRealTime W t ω l - ofNNRealTime W s ω l)) P := hL2dk.integrable_mul hL2dl
  have i2 : Integrable (fun ω => ofNNRealTime W s ω k *
      (ofNNRealTime W t ω l - ofNNRealTime W s ω l)) P := hL2ak.integrable_mul hL2dl
  have i3 : Integrable (fun ω => ofNNRealTime W s ω l *
      (ofNNRealTime W t ω k - ofNNRealTime W s ω k)) P := hL2al.integrable_mul hL2dk
  have i4 : Integrable (fun ω => ofNNRealTime W s ω k * ofNNRealTime W s ω l) P :=
    hL2ak.integrable_mul hL2al
  have e4 : P[fun ω => ofNNRealTime W s ω k * ofNNRealTime W s ω l | ℱ s] =
      fun ω => ofNNRealTime W s ω k * ofNNRealTime W s ω l :=
    condExp_of_stronglyMeasurable (ℱ.le s) (hak.mul hal) i4
  have key : (fun ω => ofNNRealTime W t ω k * ofNNRealTime W t ω l) =
      ((fun ω => (ofNNRealTime W t ω k - ofNNRealTime W s ω k) *
        (ofNNRealTime W t ω l - ofNNRealTime W s ω l)) +
        (fun ω => ofNNRealTime W s ω k *
          (ofNNRealTime W t ω l - ofNNRealTime W s ω l))) +
        ((fun ω => ofNNRealTime W s ω l *
          (ofNNRealTime W t ω k - ofNNRealTime W s ω k)) +
         (fun ω => ofNNRealTime W s ω k * ofNNRealTime W s ω l)) := by
    funext ω; simp only [Pi.add_apply]; ring
  beta_reduce
  rw [key]
  have e1 := condExp_add (i1.add i2) (i3.add i4) (ℱ s) (μ := P)
  have e2 := condExp_add i1 i2 (ℱ s) (μ := P)
  have e3 := condExp_add i3 i4 (ℱ s) (μ := P)
  filter_upwards [e1, e2, e3, condExp_incr_mul_real_of_ne hW hst hkl,
    condExp_mul_incr_real hW hst l hak i2, condExp_mul_incr_real hW hst k hal i3] with
    ω h1 h2 h3 h4 h5 h6
  rw [h1, Pi.add_apply, h2, h3, Pi.add_apply, Pi.add_apply, h4, h5, h6, e4]
  simp

/-! #### Quadratic variation along partitions -/

/-- The increment vector of `W` over the `i`-th subinterval of a partition. -/
def partIncr (W : ℝ≥0 → Ω → ι → ℝ) {a b : ℝ} (π : Partition a b) (i : Fin π.n) (ω : Ω) : ι → ℝ :=
  W (π.pt i.succ).toNNReal ω - W (π.pt i.castSucc).toNNReal ω

theorem indepFun_partIncr (hW : IsBrownianFiltration P ℱ W) {a b : ℝ}
    (π : Partition a b) {i j : Fin π.n} (hij : i < j) :
    IndepFun (partIncr W π j) (partIncr W π i) P := by
  have hle : ((π.pt i.succ).toNNReal : ℝ) ≤ ((π.pt j.castSucc).toNNReal : ℝ) := by
    exact_mod_cast Real.toNNReal_le_toNNReal (π.mono (Fin.succ_le_castSucc_iff.2 hij))
  have hZ : Measurable[ℱ ((π.pt j.castSucc).toNNReal : ℝ)] (partIncr W π i) := by
    have h1 := (hW.adapted (π.pt i.succ).toNNReal).mono (ℱ.mono hle) le_rfl
    have h2 := (hW.adapted (π.pt i.castSucc).toNNReal).mono
      (ℱ.mono (hle.trans' (by exact_mod_cast Real.toNNReal_le_toNNReal (π.pt_le i)))) le_rfl
    exact h1.sub h2
  exact hW.indepFun_incr (Real.toNNReal_le_toNNReal (π.pt_le j)) hZ

theorem integral_partIncr_sq (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P] {a b : ℝ}
    (ha : 0 ≤ a) (π : Partition a b) (i : Fin π.n) (k : ι) :
    ∫ ω, (partIncr W π i ω k) ^ 2 ∂P = π.pt i.succ - π.pt i.castSucc := by
  have := integral_incr_sq hW (Real.toNNReal_le_toNNReal (π.pt_le i)) k
  rw [Real.coe_toNNReal _ (π.pt_nonneg ha _), Real.coe_toNNReal _ (π.pt_nonneg ha _)] at this
  exact this

theorem integral_partIncr_fourth (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {a b : ℝ} (ha : 0 ≤ a) (π : Partition a b) (i : Fin π.n) (k : ι) :
    ∫ ω, (partIncr W π i ω k) ^ 4 ∂P = 3 * (π.pt i.succ - π.pt i.castSucc) ^ 2 := by
  have := integral_incr_fourth hW (Real.toNNReal_le_toNNReal (π.pt_le i)) k
  rw [Real.coe_toNNReal _ (π.pt_nonneg ha _), Real.coe_toNNReal _ (π.pt_nonneg ha _)] at this
  exact this


theorem measurable_partIncr_coord (hW : IsBrownianFiltration P ℱ W) {a b : ℝ}
    (π : Partition a b) (i : Fin π.n) (k : ι) : Measurable fun ω => partIncr W π i ω k :=
  (measurable_pi_apply k).comp ((hW.measurable _).sub (hW.measurable _))

theorem memLp_partIncr_sq (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P] {a b : ℝ}
    (π : Partition a b) (i : Fin π.n) (k : ι) :
    MemLp (fun ω => (partIncr W π i ω k) ^ 2) 2 P := by
  have h4 : MemLp (fun ω => partIncr W π i ω k) 4 P :=
    memLp_incr_coord hW (Real.toNNReal_le_toNNReal (π.pt_le i)) k (by simp)
  have := h4.integrable_norm_pow (p := 4) (by norm_num)
  refine (memLp_two_iff_integrable_sq (((measurable_partIncr_coord hW π i k).pow_const 2)
    |>.aestronglyMeasurable)).2 ?_
  have e : ∀ x : ℝ, ‖x‖ ^ 4 = (x ^ 2) ^ 2 := fun x => by
    rw [Real.norm_eq_abs, ← sq_abs x]; ring
  exact this.congr (Filter.Eventually.of_forall fun ω => e _)


theorem variance_partIncr_sq (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P] {a b : ℝ}
    (ha : 0 ≤ a) (π : Partition a b) (i : Fin π.n) (k : ι) :
    variance (fun ω => (partIncr W π i ω k) ^ 2) P = 2 * (π.pt i.succ - π.pt i.castSucc) ^ 2 := by
  rw [variance_eq_sub (memLp_partIncr_sq hW π i k)]
  have h1 : (fun ω => (partIncr W π i ω k) ^ 2) ^ 2 = fun ω => (partIncr W π i ω k) ^ 4 := by
    funext ω; simp only [Pi.pow_apply]; ring
  have h2 : ∫ ω, ((fun ω => (partIncr W π i ω k) ^ 2) ^ 2) ω ∂P =
      3 * (π.pt i.succ - π.pt i.castSucc) ^ 2 := by
    rw [h1]; exact integral_partIncr_fourth hW ha π i k
  rw [h2, integral_partIncr_sq hW ha π i k]
  ring

theorem lintegral_sq_sub_le (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P] (k : ι)
    {a b : ℝ} (ha : 0 ≤ a) (π : Partition a b) :
    ∫⁻ ω, ‖π.sumIncrements
      (fun s t => (W (Real.toNNReal t) ω k - W (Real.toNNReal s) ω k) ^ 2) - (b - a)‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (2 * π.mesh * (b - a)) := by
  have key := lintegral_enorm_sq_sub_sum P (fun i ω => (partIncr W π i ω k) ^ 2)
    (fun i => memLp_partIncr_sq hW π i k) ?_ (b - a) ?_
  · refine key.trans_le (ENNReal.ofReal_le_ofReal ?_)
    simp only [variance_partIncr_sq hW ha π _ k]
    rw [← Partition.sum_length π, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h0 : 0 ≤ π.pt i.succ - π.pt i.castSucc := sub_nonneg.2 (π.pt_le i)
    have := π.length_le_mesh i
    nlinarith
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact ((indepFun_partIncr hW π h).comp
        (φ := fun v : ι → ℝ => (v k) ^ 2) (ψ := fun v : ι → ℝ => (v k) ^ 2)
        (by fun_prop) (by fun_prop)).symm
    · exact (indepFun_partIncr hW π h).comp
        (φ := fun v : ι → ℝ => (v k) ^ 2) (ψ := fun v : ι → ℝ => (v k) ^ 2)
        (by fun_prop) (by fun_prop)
  · simp only [integral_partIncr_sq hW ha π _ k]
    exact Partition.sum_length π


theorem indepFun_partIncr_coords (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {a b : ℝ} (π : Partition a b) (i : Fin π.n) {k l : ι} (hkl : k ≠ l) :
    IndepFun (fun ω => partIncr W π i ω k) (fun ω => partIncr W π i ω l) P :=
  (iIndepFun_incr_coords hW (Real.toNNReal_le_toNNReal (π.pt_le i))).indepFun hkl

theorem integral_partIncr_mul (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {a b : ℝ} (π : Partition a b) (i : Fin π.n) {k l : ι} (hkl : k ≠ l) :
    ∫ ω, partIncr W π i ω k * partIncr W π i ω l ∂P = 0 :=
  integral_incr_mul_of_ne hW (Real.toNNReal_le_toNNReal (π.pt_le i)) hkl

theorem memLp_partIncr_mul (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {a b : ℝ} (π : Partition a b) (i : Fin π.n) {k l : ι} (hkl : k ≠ l) :
    MemLp (fun ω => partIncr W π i ω k * partIncr W π i ω l) 2 P := by
  refine (memLp_two_iff_integrable_sq (((measurable_partIncr_coord hW π i k).mul
    (measurable_partIncr_coord hW π i l)).aestronglyMeasurable)).2 ?_
  have hind : IndepFun (fun ω => (partIncr W π i ω k) ^ 2) (fun ω => (partIncr W π i ω l) ^ 2) P :=
    (indepFun_partIncr_coords hW π i hkl).comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
      (by fun_prop) (by fun_prop)
  have h := IndepFun.integrable_mul hind ((memLp_partIncr_sq hW π i k).integrable one_le_two)
    ((memLp_partIncr_sq hW π i l).integrable one_le_two)
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.mul_apply]; ring


theorem variance_partIncr_mul (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P] {a b : ℝ}
    (ha : 0 ≤ a) (π : Partition a b) (i : Fin π.n) {k l : ι} (hkl : k ≠ l) :
    variance (fun ω => partIncr W π i ω k * partIncr W π i ω l) P =
      (π.pt i.succ - π.pt i.castSucc) ^ 2 := by
  rw [variance_eq_sub (memLp_partIncr_mul hW π i hkl)]
  have hind : IndepFun (fun ω => (partIncr W π i ω k) ^ 2) (fun ω => (partIncr W π i ω l) ^ 2) P :=
    (indepFun_partIncr_coords hW π i hkl).comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
      (by fun_prop) (by fun_prop)
  have h2 : ∫ ω, ((fun ω => partIncr W π i ω k * partIncr W π i ω l) ^ 2) ω ∂P =
      (π.pt i.succ - π.pt i.castSucc) ^ 2 := by
    have : ∀ ω, ((fun ω => partIncr W π i ω k * partIncr W π i ω l) ^ 2) ω =
        (partIncr W π i ω k) ^ 2 * (partIncr W π i ω l) ^ 2 := fun ω => by
      simp only [Pi.pow_apply]; ring
    simp_rw [this]
    rw [hind.integral_fun_mul_eq_mul_integral
      ((memLp_partIncr_sq hW π i k).aestronglyMeasurable)
      ((memLp_partIncr_sq hW π i l).aestronglyMeasurable),
      integral_partIncr_sq hW ha π i k, integral_partIncr_sq hW ha π i l]
    ring
  have h3 : P[fun ω => partIncr W π i ω k * partIncr W π i ω l] = 0 :=
    integral_partIncr_mul hW π i hkl
  rw [h2, h3]; ring

theorem lintegral_mul_le (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P] {k l : ι}
    (hkl : k ≠ l) {a b : ℝ} (ha : 0 ≤ a) (π : Partition a b) :
    ∫⁻ ω, ‖π.sumIncrements
      (fun s t => (W (Real.toNNReal t) ω k - W (Real.toNNReal s) ω k) *
        (W (Real.toNNReal t) ω l - W (Real.toNNReal s) ω l))‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (π.mesh * (b - a)) := by
  have key := lintegral_enorm_sq_sub_sum P (fun i ω => partIncr W π i ω k * partIncr W π i ω l)
    (fun i => memLp_partIncr_mul hW π i hkl) ?_ 0 ?_
  · simp only [sub_zero] at key
    refine key.trans_le (ENNReal.ofReal_le_ofReal ?_)
    simp only [variance_partIncr_mul hW ha π _ hkl]
    rw [← Partition.sum_length π, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h0 : 0 ≤ π.pt i.succ - π.pt i.castSucc := sub_nonneg.2 (π.pt_le i)
    have := π.length_le_mesh i
    nlinarith
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact ((indepFun_partIncr hW π h).comp
        (φ := fun v : ι → ℝ => v k * v l) (ψ := fun v : ι → ℝ => v k * v l)
        (by fun_prop) (by fun_prop)).symm
    · exact (indepFun_partIncr hW π h).comp
        (φ := fun v : ι → ℝ => v k * v l) (ψ := fun v : ι → ℝ => v k * v l)
        (by fun_prop) (by fun_prop)
  · simp only [integral_partIncr_mul hW π _ hkl, Finset.sum_const_zero]


/-- `W t` is in every `L^p`, `p < ∞` (not in `L^∞`: Gaussian coordinates are unbounded). -/
theorem memLp (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P] (t : ℝ≥0) (k : ι)
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp (fun ω => W t ω k) p P :=
  memLp_coord hW t k hp

/-- Quadratic variation of Brownian motion along partitions, in `L²`: for `0 ≤ a ≤ b` and
partitions `π n` of `[a, b]` with mesh `→ 0`,
`∑_i (W^k_{t_{i+1}} - W^k_{t_i})² → b - a` in `L²(P)` (stated with the lower integral, so no
junk value can make it vacuous). -/
theorem tendsto_sumIncrements_sq (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    (k : ι) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (π : ℕ → Partition a b)
    (hmesh : Tendsto (fun n => (π n).mesh) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ ω, ‖(π n).sumIncrements
      (fun s t => (W (Real.toNNReal t) ω k - W (Real.toNNReal s) ω k) ^ 2) - (b - a)‖ₑ ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hb : Tendsto (fun n => ENNReal.ofReal (2 * (π n).mesh * (b - a))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal ((hmesh.const_mul 2).mul_const (b - a))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun n => zero_le)
    (fun n => lintegral_sq_sub_le hW k ha (π n))

/-- Cross quadratic variation of two different coordinates along partitions vanishes in `L²`. -/
theorem tendsto_sumIncrements_mul_of_ne (hW : IsBrownianFiltration P ℱ W) [IsProbabilityMeasure P]
    {k l : ι} (hkl : k ≠ l) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (π : ℕ → Partition a b)
    (hmesh : Tendsto (fun n => (π n).mesh) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ ω, ‖(π n).sumIncrements
      (fun s t => (W (Real.toNNReal t) ω k - W (Real.toNNReal s) ω k) *
        (W (Real.toNNReal t) ω l - W (Real.toNNReal s) ω l))‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
  have hb : Tendsto (fun n => ENNReal.ofReal ((π n).mesh * (b - a))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (hmesh.mul_const (b - a))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun n => zero_le)
    (fun n => lintegral_mul_le hW hkl ha (π n))

/-- The real-time process `ofNNRealTime W` is adapted to `ℱ` (and everywhere continuous). -/
theorem adapted_ofNNRealTime (hW : IsBrownianFiltration P ℱ W) :
    Adapted ℱ (ofNNRealTime W) :=
  adapted_ofNNRealTime_aux hW

theorem isProgressive_ofNNRealTime (hW : IsBrownianFiltration P ℱ W) :
    IsProgressive ℱ (ofNNRealTime W) :=
  (StronglyAdapted.isStronglyProgressive_of_continuous
    (fun t => (adapted_ofNNRealTime hW t).stronglyMeasurable)
    (fun ω => continuous_ofNNRealTime W ω (hW.cont ω))).isProgressive

end IsBrownianFiltration

/-! ### Construction from Mathlib Brownian motions and independent initial data -/

/-- Dyadic approximation from below, `⌊2ⁿ t⌋ / 2ⁿ`. -/
def dyadicFloor (n : ℕ) (t : ℝ≥0) : ℝ≥0 := ((⌊(t : ℝ) * 2 ^ n⌋₊ : ℕ) : ℝ≥0) / 2 ^ n

theorem tendsto_dyadicFloor (t : ℝ≥0) : Tendsto (fun n => dyadicFloor n t) atTop (𝓝 t) := by
  rw [← NNReal.tendsto_coe]
  have hpos : ∀ n : ℕ, (0 : ℝ) < 2 ^ n := fun n => by positivity
  have h1 : ∀ n, (dyadicFloor n t : ℝ) ≤ t := fun n => by
    simp only [dyadicFloor, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
    rw [div_le_iff₀ (hpos n)]
    exact Nat.floor_le (by positivity)
  have h2 : ∀ n, (t : ℝ) - (1 / 2) ^ n ≤ (dyadicFloor n t : ℝ) := fun n => by
    simp only [dyadicFloor, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
    rw [le_div_iff₀ (hpos n), sub_mul, one_div, inv_pow, inv_mul_cancel₀ (hpos n).ne']
    have := Nat.lt_floor_add_one ((t : ℝ) * 2 ^ n)
    linarith
  have h3 : Tendsto (fun n : ℕ => (t : ℝ) - (1 / 2) ^ n) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ))
      (by norm_num) (by norm_num))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h3 tendsto_const_nhds h2 h1

theorem exists_measurable_continuous_modification (P : Measure Ω) (W : ℝ≥0 → Ω → ι → ℝ)
    (hW : ∀ k, IsBrownianReal (fun t ω => W t ω k) P) :
    ∃ W' : ℝ≥0 → Ω → ι → ℝ, (∀ t, Measurable (W' t)) ∧ (∀ ω, Continuous fun t => W' t ω) ∧
      (∀ ω, W' 0 ω = 0) ∧ ∀ᵐ ω ∂P, ∀ t, W' t ω = W t ω := by
  classical
  have haem : ∀ t, AEMeasurable (W t) P := fun t =>
    aemeasurable_pi_iff.2 fun k => (hW k).toIsPreBrownianReal.aemeasurable t
  let X : ℝ≥0 → Ω → ι → ℝ := fun t => (haem t).mk (W t)
  have hXm : ∀ t, Measurable (X t) := fun t => (haem t).measurable_mk
  have hXW : ∀ t, X t =ᵐ[P] W t := fun t => (haem t).ae_eq_mk.symm
  let Z : ℝ≥0 → Ω → ι → ℝ := fun t ω => limUnder atTop (fun n => X (dyadicFloor n t) ω)
  have hZm : ∀ t, Measurable (Z t) := fun t =>
    (StronglyMeasurable.limUnder (fun n => (hXm (dyadicFloor n t)).stronglyMeasurable)).measurable
  have hE : ∀ᵐ ω ∂P, ∀ m n : ℕ, X ((m : ℝ≥0) / 2 ^ n) ω = W ((m : ℝ≥0) / 2 ^ n) ω := by
    rw [ae_all_iff]; intro m; rw [ae_all_iff]; intro n; exact hXW _
  have hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω := by
    have : ∀ᵐ ω ∂P, ∀ k, Continuous fun t => W t ω k := ae_all_iff.2 fun k => (hW k).cont
    filter_upwards [this] with ω h using continuous_pi h
  have hZW : ∀ᵐ ω ∂P, ∀ t, Z t ω = W t ω := by
    filter_upwards [hE, hcont] with ω h1 h2 t
    have : (fun n => X (dyadicFloor n t) ω) = fun n => W (dyadicFloor n t) ω :=
      funext fun n => h1 _ n
    simp only [Z, this]
    exact ((h2.tendsto t).comp (tendsto_dyadicFloor t)).limUnder_eq
  have hZc : ∀ᵐ ω ∂P, Continuous fun t => Z t ω := by
    filter_upwards [hZW, hcont] with ω h1 h2
    have : (fun t => Z t ω) = fun t => W t ω := funext h1
    rw [this]; exact h2
  obtain ⟨Y, hYm, hYc, hYZ⟩ := exists_continuous_modification P Z hZm hZc
  have h0 : ∀ᵐ ω ∂P, W 0 ω = 0 := by
    have : ∀ᵐ ω ∂P, ∀ k, W 0 ω k = 0 := ae_all_iff.2 fun k => (hW k).eval_zero_ae_eq_zero
    filter_upwards [this] with ω h using funext h
  refine ⟨fun t ω => Y t ω - Y 0 ω, fun t => (hYm t).sub (hYm 0), fun ω => (hYc ω).sub continuous_const,
    fun ω => by simp, ?_⟩
  filter_upwards [hYZ, hZW, h0] with ω h1 h2 h3 t
  simp only [h1 t, h1 0, h2 t, h2 0, h3, sub_zero]



omit [Fintype ι] in
theorem comap_pi_eq_iSup {Ω' : Type*} (f : Ω' → ι → ℝ) :
    MeasurableSpace.comap f inferInstance =
      ⨆ k : ι, MeasurableSpace.comap (fun ω => f ω k) inferInstance := by
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp]
  rfl

theorem indep_incr_generated {E : Type*} [MeasurableSpace E] (P : Measure Ω)
    [IsProbabilityMeasure P] (W' : ℝ≥0 → Ω → ι → ℝ) (hW'm : ∀ t, Measurable (W' t))
    (hB' : ∀ k, IsBrownianReal (fun t ω => W' t ω k) P)
    (hind' : iIndepFun (fun (k : ι) ω => fun t : ℝ≥0 => W' t ω k) P)
    (X₀ : Ω → E) (hX₀ : Measurable X₀)
    (hX₀W' : IndepFun X₀ (fun ω => fun t : ℝ≥0 => W' t ω) P) (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => W' t ω - W' s ω) inferInstance)
      (generatedFiltration P X₀ hX₀ W' hW'm (s : ℝ)) P := by
  classical
  let C : ι → MeasurableSpace Ω := fun k =>
    MeasurableSpace.comap (fun ω (u : ℝ≥0) => W' u ω k) inferInstance
  let Y : ι → MeasurableSpace Ω := fun k =>
    MeasurableSpace.comap (fun ω => W' t ω k - W' s ω k) inferInstance
  let Z : ι → MeasurableSpace Ω := fun k =>
    ⨆ r : ℝ≥0, ⨆ (_ : r ≤ s), MeasurableSpace.comap (fun ω => W' r ω k) inferInstance
  have hpathm : ∀ k, Measurable fun ω (u : ℝ≥0) => W' u ω k := fun k =>
    Measurable.of_eval fun u => (measurable_pi_apply k).comp (hW'm u)
  have hCle : ∀ k, C k ≤ mΩ := fun k => (hpathm k).comap_le
  have hC : iIndep C P := hind'
  have hCm : ∀ k (r : ℝ≥0), Measurable[C k] fun ω => W' r ω k := fun k r =>
    (measurable_pi_apply r).comp (comap_measurable (fun ω (u : ℝ≥0) => W' u ω k))
  have hYC : ∀ k, Y k ≤ C k := fun k => Measurable.comap_le ((hCm k t).sub (hCm k s))
  have hZC : ∀ k, Z k ≤ C k := fun k => iSup₂_le fun r _ => Measurable.comap_le (hCm k r)
  have hYZ : ∀ k, Indep (Y k) (Z k) P := by
    intro k
    have h := (IndepFun_iff_Indep _ _ _).1 ((hB' k).toIsPreBrownianReal.indepFun_shift s)
    refine indep_of_indep_of_le h ?_ ?_
    · refine Measurable.comap_le ?_
      have h1 : Measurable[MeasurableSpace.comap (fun ω (u : ℝ≥0) => W' (s + u) ω k - W' s ω k)
          inferInstance] fun ω => W' (s + (t - s)) ω k - W' s ω k :=
        (measurable_pi_apply (t - s)).comp (comap_measurable
          (fun ω (u : ℝ≥0) => W' (s + u) ω k - W' s ω k))
      rwa [add_tsub_cancel_of_le hst] at h1
    · refine iSup₂_le fun r hr => Measurable.comap_le ?_
      exact (measurable_pi_apply (⟨r, hr⟩ : Set.Iic s)).comp
        (comap_measurable (fun ω (u : Set.Iic s) => W' (u : ℝ≥0) ω k))
  have hYZ' := indep_iSup_of_pairs P C Y Z hCle hC hYC hZC hYZ
  -- the σ-algebra of the whole path
  have hpathvec : Measurable fun ω (u : ℝ≥0) => W' u ω := Measurable.of_eval hW'm
  have hPm : ∀ k (r : ℝ≥0), Measurable[MeasurableSpace.comap (fun ω (u : ℝ≥0) => W' u ω)
      inferInstance] fun ω => W' r ω k := fun k r =>
    (measurable_pi_apply k).comp ((measurable_pi_apply r).comp
      (comap_measurable (fun ω (u : ℝ≥0) => W' u ω)))
  have hYle : (⨆ k, Y k) ≤ MeasurableSpace.comap (fun ω (u : ℝ≥0) => W' u ω) inferInstance :=
    iSup_le fun k => Measurable.comap_le ((hPm k t).sub (hPm k s))
  have hZle : (⨆ k, Z k) ≤ MeasurableSpace.comap (fun ω (u : ℝ≥0) => W' u ω) inferInstance :=
    iSup_le fun k => iSup₂_le fun r _ => Measurable.comap_le (hPm k r)
  have hX₀I : Indep (MeasurableSpace.comap X₀ inferInstance)
      (MeasurableSpace.comap (fun ω (u : ℝ≥0) => W' u ω) inferInstance) P :=
    (IndepFun_iff_Indep _ _ _).1 hX₀W'
  have hmΩ1 : (⨆ k, Y k) ≤ mΩ := hYle.trans hpathvec.comap_le
  have hmΩ2 : (⨆ k, Z k) ≤ mΩ := hZle.trans hpathvec.comap_le
  have h1 : Indep (⨆ k, Y k) (MeasurableSpace.comap X₀ inferInstance ⊔ ⨆ k, Z k) P :=
    indep_sup_right_of_indep P hX₀.comap_le hmΩ1 hmΩ2 hYZ'
      (indep_of_indep_of_le_right hX₀I (sup_le hYle hZle))
  have hmΩ3 : (MeasurableSpace.comap X₀ inferInstance ⊔ ⨆ k, Z k) ≤ mΩ :=
    sup_le hX₀.comap_le hmΩ2
  have hN : Indep (nullSets P) ((⨆ k, Y k) ⊔ (MeasurableSpace.comap X₀ inferInstance ⊔ ⨆ k, Z k)) P :=
    indep_of_null_or_conull P (fun u hu => (measurableSet_nullSets_iff P u).1 hu)
      (sup_le hmΩ1 hmΩ3)
  have h2 : Indep (⨆ k, Y k) (nullSets P ⊔ (MeasurableSpace.comap X₀ inferInstance ⊔ ⨆ k, Z k)) P :=
    indep_sup_right_of_indep P (nullSets_le P) hmΩ1 hmΩ3 h1 hN
  have hM1 : MeasurableSpace.comap (fun ω => W' t ω - W' s ω) inferInstance ≤ ⨆ k, Y k := by
    rw [comap_pi_eq_iSup]
    exact iSup_le fun k => le_iSup Y k
  refine indep_of_indep_of_le h2 hM1 ?_
  show (MeasurableSpace.comap X₀ inferInstance ⊔
      ⨆ (r : ℝ≥0) (_ : (r : ℝ) ≤ (s : ℝ)), MeasurableSpace.comap (W' r) inferInstance) ⊔
        nullSets P ≤ _
  refine sup_le (sup_le (le_sup_of_le_right le_sup_left) (iSup₂_le fun r hr => ?_)) le_sup_left
  rw [comap_pi_eq_iSup (W' r)]
  refine iSup_le fun k => ?_
  exact le_sup_of_le_right (le_sup_of_le_right (le_iSup_of_le k
    (le_iSup₂_of_le (f := fun r (_ : r ≤ s) =>
      MeasurableSpace.comap (fun ω => W' r ω k) inferInstance) r (by exact_mod_cast hr) le_rfl)))


/-- From coordinatewise Brownian motions `W^k` (Mathlib's `IsBrownianReal`), jointly independent
and independent of a measurable initial datum `X₀`, there is an everywhere continuous measurable
modification `W'` (indistinguishable from `W`) such that `W'` is Brownian relative to the
augmented generated filtration `ℱ t = σ(X₀) ⊔ σ(W'_s : s ≤ t) ⊔ nullSets P`, and `X₀` is
`ℱ t`-measurable for every `t`.  This is the bridge from the hypotheses of `particle_wellposed`
(`IsVectorBrownian`, `IndepFun X₀ W`) to the setting of the stochastic integral. -/
theorem exists_isBrownianFiltration {E : Type*} [MeasurableSpace E] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ι → ℝ)
    (hW : ∀ k, IsBrownianReal (fun t ω => W t ω k) P)
    (hind : iIndepFun (fun (k : ι) ω => fun t : ℝ≥0 => W t ω k) P)
    (X₀ : Ω → E) (hX₀ : Measurable X₀)
    (hX₀W : IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P) :
    ∃ (W' : ℝ≥0 → Ω → ι → ℝ) (hW' : ∀ t, Measurable (W' t)),
      (∀ᵐ ω ∂P, ∀ t, W' t ω = W t ω) ∧
      IsBrownianFiltration P (generatedFiltration P X₀ hX₀ W' hW') W' := by
  obtain ⟨W', hW'm, hW'c, hW'0, hW'ae⟩ := exists_measurable_continuous_modification P W hW
  refine ⟨W', hW'm, hW'ae, ?_⟩
  have hae_t : ∀ t k, (fun ω => W t ω k) =ᵐ[P] (fun ω => W' t ω k) := fun t k => by
    filter_upwards [hW'ae] with ω h using (congrFun (h t) k).symm
  have hB' : ∀ k, IsBrownianReal (fun t ω => W' t ω k) P := fun k =>
    ⟨(hW k).toIsPreBrownianReal.congr (fun t => hae_t t k),
      Filter.Eventually.of_forall fun ω => (continuous_apply k).comp (hW'c ω)⟩
  have hpath : ∀ k, (fun ω (t : ℝ≥0) => W t ω k) =ᵐ[P] (fun ω (t : ℝ≥0) => W' t ω k) := fun k => by
    filter_upwards [hW'ae] with ω h using funext fun t => (congrFun (h t) k).symm
  have hind' : iIndepFun (fun (k : ι) ω => fun t : ℝ≥0 => W' t ω k) P :=
    (iIndepFun_congr hpath).1 hind
  have hX₀W' : IndepFun X₀ (fun ω => fun t : ℝ≥0 => W' t ω) P :=
    hX₀W.congr (ae_eq_refl _) (by
      filter_upwards [hW'ae] with ω h using funext fun t => (h t).symm)
  refine ⟨generatedFiltration_isComplete P X₀ hX₀ W' hW'm,
    fun t => generatedFiltration_measurable_W P X₀ hX₀ W' hW'm t t le_rfl, hW'0, hW'c,
    fun s t hst => indep_incr_generated P W' hW'm hB' hind' X₀ hX₀ hX₀W' s t hst, ?_⟩
  intro s t hst
  have hlaw : ∀ k, HasLaw (fun ω => W' t ω k - W' s ω k) (gaussianReal 0 (t - s)) P := fun k => by
    have h := (hB' k).toIsPreBrownianReal.hasLaw_sub t s
    convert h using 2
    apply NNReal.eq
    rw [coe_nndist, NNReal.coe_sub hst, Real.dist_eq, abs_of_nonneg]
    · rfl
    · simp [hst]
  have hi : iIndepFun (fun (k : ι) ω => W' t ω k - W' s ω k) P :=
    hind'.comp (fun _ (p : ℝ≥0 → ℝ) => p t - p s)
      (fun _ => ((measurable_pi_apply t).sub (measurable_pi_apply s)))
  exact (iIndepFun_iff_hasLaw_pi_pi hlaw).1 hi

/-- The initial datum is measurable at every time of the generated filtration (restated for the
Brownian setting; it is `generatedFiltration_measurable_init`). -/
theorem generatedFiltration_measurable_init' {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (P : Measure Ω) (X₀ : Ω → E) (hX₀ : Measurable X₀) (W : ℝ≥0 → Ω → F)
    (hW : ∀ t, Measurable (W t)) (t : ℝ) :
    Measurable[generatedFiltration P X₀ hX₀ W hW t] X₀ :=
  generatedFiltration_measurable_init P X₀ hX₀ W hW t

/-- A Brownian filtration remains Brownian for the same `W` under an enlargement `ℱ ≤ 𝒢` of the
filtration as long as increments stay independent of `𝒢 s`; in particular the trivial
enlargement by an independent initial σ-algebra. (Used to pass from the Brownian filtration of
the noise to the filtration containing the initial coupling `(X₀, η°)`, M L10537.) -/
theorem IsBrownianFiltration.of_le {P : Measure Ω} {ℱ 𝒢 : Filtration ℝ mΩ}
    {W : ℝ≥0 → Ω → ι → ℝ} (hW : IsBrownianFiltration P ℱ W) (hle : ∀ t, ℱ t ≤ 𝒢 t)
    (hind : ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance) (𝒢 s) P) :
    IsBrownianFiltration P 𝒢 W where
  complete := fun t s hs hs0 => hle t _ (hW.complete t s hs hs0)
  adapted := fun t => (hW.adapted t).mono (hle t) le_rfl
  zero := hW.zero
  cont := hW.cont
  indep_incr := hind
  gaussian_incr := hW.gaussian_incr

end HRS
