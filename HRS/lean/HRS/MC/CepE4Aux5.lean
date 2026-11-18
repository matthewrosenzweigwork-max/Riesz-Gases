import HRS.MC.CepE4Aux4

/-!
# Packet CEPE4, auxiliary 5: the a priori `L²` bound for a fixed Yosida index

Pathwise Gronwall for `Y = Z - σ' w` against the forcing `Λ = ∫_0^T |w_r| dr`, which is in `L²`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE4

open HRS HRS.MC.Cepa

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- Cauchy–Schwarz on an interval. -/
theorem e4_cs {f : ℝ → ℝ} (hf : Continuous f) {T : ℝ} (hT : 0 ≤ T) :
    (∫ r in (0 : ℝ)..T, f r) ^ 2 ≤ T * ∫ r in (0 : ℝ)..T, f r ^ 2 := by
  rcases hT.eq_or_lt with h0 | hpos
  · subst h0; simp
  set c : ℝ := (∫ r in (0 : ℝ)..T, f r) / T with hc
  have h1 : 0 ≤ ∫ r in (0 : ℝ)..T, (f r - c) ^ 2 :=
    intervalIntegral.integral_nonneg hT fun r _ => sq_nonneg _
  have h2 : ∫ r in (0 : ℝ)..T, (f r - c) ^ 2 =
      (∫ r in (0 : ℝ)..T, f r ^ 2) - 2 * c * (∫ r in (0 : ℝ)..T, f r) + c ^ 2 * T := by
    have e : ∀ r, (f r - c) ^ 2 = (f r ^ 2 - 2 * c * f r) + c ^ 2 := fun r => by ring
    simp_rw [e]
    have hc1 : Continuous fun r => f r ^ 2 := hf.pow 2
    have hc2 : Continuous fun r => 2 * c * f r := continuous_const.mul hf
    rw [intervalIntegral.integral_add
      ((show Continuous fun r => f r ^ 2 - 2 * c * f r from hc1.sub hc2).intervalIntegrable 0 T)
      intervalIntegrable_const, intervalIntegral.integral_sub (hc1.intervalIntegrable 0 T)
      (hc2.intervalIntegrable 0 T), intervalIntegral.integral_const_mul]
    simp
    ring
  have h3 : c * T = ∫ r in (0 : ℝ)..T, f r := by rw [hc]; field_simp
  have : (∫ r in (0 : ℝ)..T, f r ^ 2) - 2 * c * (∫ r in (0 : ℝ)..T, f r) + c ^ 2 * T =
      (∫ r in (0 : ℝ)..T, f r ^ 2) - (∫ r in (0 : ℝ)..T, f r) ^ 2 / T := by
    rw [← h3]; field_simp; ring
  rw [h2, this] at h1
  have : (∫ r in (0 : ℝ)..T, f r) ^ 2 / T ≤ ∫ r in (0 : ℝ)..T, f r ^ 2 := by linarith
  rw [div_le_iff₀ hpos] at this
  linarith

theorem e4_Lambda_memLp [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {w : ℝ → Ω → Ch N}
    (h : E4Noise P ℱ N w) {T : ℝ} (hT : 0 ≤ T) :
    MemLp (fun ω => ∫ r in (0 : ℝ)..T, ‖w r ω‖) 2 P := by
  have hn : Integrable (fun p : ℝ × Ω => ‖w p.1 p.2‖) ((e4_mu T).prod P) := by
    refine ((e4_wsq_integrable h T).add (integrable_const (1 : ℝ))).mono' (e4_w_joint h).norm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by
      simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Pi.add_apply]
      nlinarith [sq_nonneg (‖w p.1 p.2‖ - 1)]
  have hΛ : Integrable (fun ω => ∫ r in (0 : ℝ)..T, ‖w r ω‖) P := by
    have := hn.integral_prod_right
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [intervalIntegral.integral_of_le hT]
  refine (memLp_two_iff_integrable_sq hΛ.aestronglyMeasurable).2 ?_
  have hn2 : Integrable (fun ω => ∫ r in (0 : ℝ)..T, ‖w r ω‖ ^ 2) P := by
    have := (e4_wsq_integrable h T).integral_prod_right
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [intervalIntegral.integral_of_le hT]
  refine (hn2.const_mul T).mono'
    (hΛ.aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (∫ r in (0 : ℝ)..T, ‖w r ω‖))]
    exact e4_cs (f := fun r => ‖w r ω‖) (h.cont ω).norm hT

/-- Deterministic pathwise bound. -/
theorem e4_pathwise_bound {Bf : Ch N → Ch N} (hBc : Continuous Bf) {β0 Lb : ℝ} (hβ0 : 0 ≤ β0)
    (hLb : 0 ≤ Lb) (hBb : ∀ z, ‖Bf z‖ ≤ β0 + Lb * ‖z‖) {Z w : ℝ → Ch N} (hZ : Continuous Z)
    (hw : Continuous w) {z0 : Ch N} {σ' T : ℝ} (hT : 0 ≤ T)
    (heq : ∀ t : ℝ, 0 ≤ t → Z t = z0 + (∫ s in (0 : ℝ)..t, Bf (Z s)) + σ' • w t) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖Z t‖ ≤ Real.exp (Lb * T) * (‖z0‖ + β0 * T + Lb * |σ'| * ∫ r in (0 : ℝ)..T, ‖w r‖) +
      |σ'| * ‖w t‖ := by
  set Y : ℝ → Ch N := fun t => z0 + ∫ s in (0 : ℝ)..t, Bf (Z s) with hY
  have hbc : Continuous fun s => Bf (Z s) := hBc.comp hZ
  have hYc : Continuous Y := by
    have : Continuous fun t => ∫ s in (0 : ℝ)..t, Bf (Z s) := by
      refine continuous_iff_continuousAt.2 fun t => ?_
      exact (hbc.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt
    exact continuous_const.add this
  have hZY : ∀ t, 0 ≤ t → ‖Z t‖ ≤ ‖Y t‖ + |σ'| * ‖w t‖ := by
    intro t ht
    rw [heq t ht]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
  set Λ : ℝ := ∫ r in (0 : ℝ)..T, ‖w r‖ with hΛ
  have hwn : Continuous fun r => ‖w r‖ := hw.norm
  have hΛ0 : 0 ≤ Λ := intervalIntegral.integral_nonneg hT fun r _ => norm_nonneg _
  set a : ℝ := ‖z0‖ + β0 * T + Lb * |σ'| * Λ with ha
  have ha0 : 0 ≤ a := by positivity
  have c1 : Continuous fun s => Lb * ‖Y s‖ := continuous_const.mul hYc.norm
  have c2 : Continuous fun s => Lb * |σ'| * ‖w s‖ := continuous_const.mul hwn
  have c3 : Continuous fun s => β0 + Lb * ‖Y s‖ := continuous_const.add c1
  have hmain : ∀ t ∈ Icc (0 : ℝ) T, ‖Y t‖ ≤ a + ∫ r in (0 : ℝ)..t, (Lb * ‖Y r‖ + 0) := by
    intro t ht
    have hint1 : ‖∫ s in (0 : ℝ)..t, Bf (Z s)‖ ≤ ∫ s in (0 : ℝ)..t, ‖Bf (Z s)‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.1
    have hle : ∫ s in (0 : ℝ)..t, ‖Bf (Z s)‖ ≤
        ∫ s in (0 : ℝ)..t, (β0 + Lb * ‖Y s‖ + Lb * |σ'| * ‖w s‖) := by
      refine intervalIntegral.integral_mono_on ht.1 (hbc.norm.intervalIntegrable _ _)
        ((c3.add c2).intervalIntegrable _ _) fun s hs => ?_
      have h1 := hBb (Z s)
      have h2 := hZY s hs.1
      have h3 : Lb * ‖Z s‖ ≤ Lb * (‖Y s‖ + |σ'| * ‖w s‖) := mul_le_mul_of_nonneg_left h2 hLb
      nlinarith
    have hsplit : ∫ s in (0 : ℝ)..t, (β0 + Lb * ‖Y s‖ + Lb * |σ'| * ‖w s‖) =
        β0 * t + (∫ s in (0 : ℝ)..t, Lb * ‖Y s‖) + Lb * |σ'| * ∫ s in (0 : ℝ)..t, ‖w s‖ := by
      rw [intervalIntegral.integral_add (c3.intervalIntegrable _ _) (c2.intervalIntegrable _ _),
        intervalIntegral.integral_add intervalIntegrable_const (c1.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul]
      simp
      ring
    have hwt : ∫ s in (0 : ℝ)..t, ‖w s‖ ≤ Λ :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 (Filter.Eventually.of_forall fun r => norm_nonneg _)
        (hwn.intervalIntegrable _ _)
    have hYb : ‖Y t‖ ≤ ‖z0‖ + ‖∫ s in (0 : ℝ)..t, Bf (Z s)‖ := norm_add_le _ _
    have hLbt : Lb * |σ'| * ∫ s in (0 : ℝ)..t, ‖w s‖ ≤ Lb * |σ'| * Λ :=
      mul_le_mul_of_nonneg_left hwt (by positivity)
    have hβt : β0 * t ≤ β0 * T := mul_le_mul_of_nonneg_left ht.2 hβ0
    simp only [add_zero]
    linarith
  have hgr := e4_gronwall_aff (φ := fun t => ‖Y t‖) (T := T) (κ := Lb) (a := a) (b := 0) hT hLb le_rfl ha0
    hYc.norm.continuousOn hmain
  intro t ht
  have := hgr t ht
  have h2 := hZY t ht.1
  simp only [zero_mul, add_zero] at this
  linarith

/-- Clamping a path to nonnegative times. -/
def e4_clamp (Z : ℝ → Ω → Ch N) : ℝ → Ω → Ch N := fun t => Z (max t 0)

theorem e4_setup_of_solution [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ}) {σ' : ℝ}
    {z0 : Ω → Ch N} {R : ℝ} (hR : ∀ ω, ‖z0 ω‖ ≤ R) {Bf : Ch N → Ch N} (hBc : Continuous Bf)
    {β0 Lb : ℝ} (hβ0 : 0 ≤ β0) (hLb : 0 ≤ Lb) (hBb : ∀ z, ‖Bf z‖ ≤ β0 + Lb * ‖z‖)
    {Z : ℝ → Ω → Ch N} (hZc : ∀ ω, Continuous fun t => Z t ω)
    (hZF : ∀ t, 0 ≤ t → Measurable[ℱ t] (Z t))
    (heq : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Z t ω = z0 ω + (∫ s in (0 : ℝ)..t, Bf (Z s ω)) + σ' • cep_noise π W' t ω)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ A : Ω → ℝ, E4Setup P ℱ N T σ' (cep_noise π W') (e4_clamp Z) A := by
  have hw := e4_noise_cep hW' hπ
  refine ⟨fun ω => Real.exp (Lb * T) * (R + β0 * T + Lb * |σ'| * ∫ r in (0 : ℝ)..T, ‖cep_noise π W' r ω‖),
    ⟨hw, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro ω
    exact (hZc ω).comp (continuous_id.max continuous_const)
  · intro t
    exact (hZF (max t 0) (le_max_right _ _)).mono (ℱ.le _) le_rfl
  · intro t ht
    simp only [e4_clamp, max_eq_left ht]
    exact hZF t ht
  · have h1 : MemLp (fun _ : Ω => R + β0 * T) 2 P := memLp_const _
    have h2 := (e4_Lambda_memLp hw hT).const_mul (Lb * |σ'|)
    exact (h1.add h2).const_mul _
  · filter_upwards [heq] with ω hω s hs
    have := e4_pathwise_bound hBc hβ0 hLb hBb (hZc ω) (hw.cont ω) hT (σ' := σ') (z0 := z0 ω)
      (Z := fun t => Z t ω) (w := fun t => cep_noise π W' t ω) hω s hs
    simp only [e4_clamp, max_eq_left hs.1]
    refine this.trans ?_
    have : Real.exp (Lb * T) * (‖z0 ω‖ + β0 * T + Lb * |σ'| * ∫ r in (0 : ℝ)..T, ‖cep_noise π W' r ω‖) ≤
        Real.exp (Lb * T) * (R + β0 * T + Lb * |σ'| * ∫ r in (0 : ℝ)..T, ‖cep_noise π W' r ω‖) :=
      mul_le_mul_of_nonneg_left (by linarith [hR ω]) (Real.exp_pos _).le
    linarith

end HRS.MC.CepE4
