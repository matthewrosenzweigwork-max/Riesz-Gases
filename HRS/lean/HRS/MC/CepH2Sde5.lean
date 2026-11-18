import HRS.MC.CepH2Sde3
import HRS.MC.CepH2Sde4

/-!
# CEPH2, S2b (part 2): second moments of the transverse part along the flow
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ}

theorem h2_cs_time {n : ℝ → ℝ} (hn : Continuous n) {T : ℝ} (hT : 0 < T) :
    (∫ s in (0 : ℝ)..T, n s) ^ 2 ≤ T * ∫ s in (0 : ℝ)..T, n s ^ 2 := by
  set I := ∫ s in (0 : ℝ)..T, n s with hI
  set J := ∫ s in (0 : ℝ)..T, n s ^ 2 with hJ
  set c := I / T with hc
  have h0 : 0 ≤ ∫ s in (0 : ℝ)..T, (n s - c) ^ 2 :=
    intervalIntegral.integral_nonneg hT.le fun s _ => sq_nonneg _
  have hi1 : IntervalIntegrable (fun s => n s ^ 2) volume 0 T := (hn.pow 2).intervalIntegrable 0 T
  have hi2 : IntervalIntegrable (fun s => 2 * c * n s) volume 0 T :=
    (continuous_const.mul hn).intervalIntegrable 0 T
  have hi3 : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume 0 T := intervalIntegrable_const
  have e : ∫ s in (0 : ℝ)..T, (n s - c) ^ 2 = J - 2 * c * I + c ^ 2 * T := by
    have : ∀ s, (n s - c) ^ 2 = (n s ^ 2 - 2 * c * n s) + c ^ 2 := fun s => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_add (hi1.sub hi2) hi3, intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_const_mul]
    simp [hJ, hI, mul_comm]
  rw [e] at h0
  have : c * T = I := by rw [hc]; field_simp
  have h2 : 2 * c * I = 2 * c ^ 2 * T := by rw [← this]; ring
  nlinarith [this]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Sum of squares of the coordinates of the Brownian motion at real time `s`. -/
def h2_q (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  ∑ k : Fin N, (W' (Real.toNNReal s) ω (k, 0)) ^ 2

theorem h2_noise_sq (π : Ω → Equiv.Perm (Fin N)) (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ) (t : ℝ) (ω : Ω) :
    ‖cep_noise π W' t ω‖ ^ 2 = h2_q W' t ω := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [h2_q, cep_noise, Real.norm_eq_abs, sq_abs]
  exact Equiv.sum_comp (π ω) (fun k => (W' (Real.toNNReal t) ω (k, 0)) ^ 2)

theorem h2_continuous_q {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hc : ∀ ω, Continuous fun t => W' t ω) (ω : Ω) :
    Continuous fun s => h2_q W' s ω := by
  unfold h2_q
  refine continuous_finset_sum _ fun k _ => ?_
  exact (((continuous_apply (k, 0)).comp (hc ω)).comp continuous_real_toNNReal).pow 2

theorem h2_continuous_noise {π : Ω → Equiv.Perm (Fin N)} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    (hc : ∀ ω, Continuous fun t => W' t ω) (ω : Ω) : Continuous fun t => cep_noise π W' t ω := by
  unfold cep_noise
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => ?_)
  exact ((continuous_apply (π ω k, 0)).comp (hc ω)).comp continuous_real_toNNReal

theorem h2_measurable_q [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') (s : ℝ) : Measurable (h2_q W' s) := by
  unfold h2_q
  exact Finset.measurable_sum _ fun k _ => (hW'.measurable_coord _ (k, 0)).pow_const 2

theorem h2_measurable_q_uncurry [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W') :
    Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => h2_q W' s ω) :=
  measurable_uncurry_of_continuous_of_measurable (fun ω => h2_continuous_q hW'.cont ω)
    (h2_measurable_q hW')

theorem h2_lintegral_q [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ ω, ENNReal.ofReal (h2_q W' s ω) ∂P = ENNReal.ofReal (N * s) := by
  have hint : ∀ k : Fin N, Integrable (fun ω => (W' (Real.toNNReal s) ω (k, 0)) ^ 2) P := fun k =>
    (hW'.memLp_coord (Real.toNNReal s) (k, 0) ENNReal.ofNat_ne_top).integrable_sq
  have h1 : Integrable (fun ω => h2_q W' s ω) P := integrable_finset_sum _ fun k _ => hint k
  rw [← ofReal_integral_eq_lintegral_ofReal h1
    (ae_of_all _ fun ω => Finset.sum_nonneg fun k _ => sq_nonneg _)]
  congr 1
  unfold h2_q
  rw [integral_finset_sum _ fun k _ => hint k]
  have : ∀ k : Fin N, ∫ ω, (W' (Real.toNNReal s) ω (k, 0)) ^ 2 ∂P = s := fun k => by
    have := (hW'.hasLaw_coord (Real.toNNReal s) (k, 0)).integral_comp (f := fun x : ℝ => x ^ 2)
      (by fun_prop)
    rw [integral_sq_gaussianReal_zero, Real.coe_toNNReal _ hs] at this
    exact this
  simp [this]


variable [NeZero N]

/-- Pathwise bound for the squared transverse norm. -/
theorem h2_pathwise_sq {Z Nz : ℝ → Ch N} {B : Ch N → Ch N} (hZc : Continuous Z)
    (hNc : Continuous Nz) {σ' a₀ b : ℝ} (hσ : 0 ≤ σ') (ha₀ : 0 ≤ a₀) (hb : 0 ≤ b) (hB : Continuous B)
    (hBb : ∀ z, ‖B z‖ ≤ a₀ + b * ‖h2_perp z‖)
    (hZeq : ∀ t : ℝ, 0 ≤ t → Z t = Z 0 + (∫ s in Icc (0 : ℝ) t, B (Z s)) + σ' • Nz t) {T : ℝ} (hT : 0 < T)
    {q : ℝ → ℝ} (hqc : Continuous q) (hq : ∀ s, ‖Nz s‖ ^ 2 = q s) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖h2_perp (Z t)‖ ^ 2 ≤ 6 * Real.exp (b * T) ^ 2 * ‖h2_perp (Z 0)‖ ^ 2 +
      6 * Real.exp (b * T) ^ 2 * (a₀ * T) ^ 2 +
      6 * Real.exp (b * T) ^ 2 * ((b * σ') ^ 2 * T) * (∫ s in (0 : ℝ)..T, q s) + 2 * σ' ^ 2 * q t := by
  intro t ht
  have h := h2_pathwise_moment hZc hNc hσ ha₀ hb hB hBb hZeq hT.le t ht
  set E := Real.exp (b * T) with hE
  set p0 := ‖h2_perp (Z 0)‖ with hp0
  set I := ∫ s in (0 : ℝ)..T, ‖h2_perp (Nz s)‖ with hI
  set n := ‖h2_perp (Nz t)‖ with hn
  have hnc : Continuous fun s => ‖h2_perp (Nz s)‖ := h2_continuous_perp.norm.comp hNc
  have hI2 : I ^ 2 ≤ T * ∫ s in (0 : ℝ)..T, q s := by
    refine (h2_cs_time hnc hT).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hT.le
    refine intervalIntegral.integral_mono_on hT.le ((hnc.pow 2).intervalIntegrable 0 T)
      (hqc.intervalIntegrable 0 T) fun s _ => ?_
    rw [← hq s]
    exact pow_le_pow_left₀ (norm_nonneg _) (h2_norm_perp_le _) 2
  have hn2 : n ^ 2 ≤ q t := by
    rw [← hq t]; exact pow_le_pow_left₀ (norm_nonneg _) (h2_norm_perp_le _) 2
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hT.le fun s _ => norm_nonneg _
  have hE0 : 0 < E := Real.exp_pos _
  have hx : 0 ≤ ‖h2_perp (Z t)‖ := norm_nonneg _
  have hy : 0 ≤ E * (p0 + a₀ * T + b * σ' * I) := by positivity
  have h1 : ‖h2_perp (Z t)‖ ^ 2 ≤ (E * (p0 + a₀ * T + b * σ' * I) + σ' * n) ^ 2 :=
    pow_le_pow_left₀ hx (by simpa [mul_add, add_assoc, mul_assoc] using h) 2
  have h2 : (E * (p0 + a₀ * T + b * σ' * I) + σ' * n) ^ 2 ≤
      2 * (E * (p0 + a₀ * T + b * σ' * I)) ^ 2 + 2 * (σ' * n) ^ 2 := by
    nlinarith [sq_nonneg (E * (p0 + a₀ * T + b * σ' * I) - σ' * n)]
  have h3 : (p0 + a₀ * T + b * σ' * I) ^ 2 ≤ 3 * (p0 ^ 2 + (a₀ * T) ^ 2 + (b * σ' * I) ^ 2) := by
    nlinarith [sq_nonneg (p0 - a₀ * T), sq_nonneg (p0 - b * σ' * I), sq_nonneg (a₀ * T - b * σ' * I)]
  have h4 : (b * σ' * I) ^ 2 ≤ (b * σ') ^ 2 * (T * ∫ s in (0 : ℝ)..T, q s) := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left hI2 (sq_nonneg _)
  have h5 : (σ' * n) ^ 2 ≤ σ' ^ 2 * q t := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left hn2 (sq_nonneg _)
  have h6 : (E * (p0 + a₀ * T + b * σ' * I)) ^ 2 ≤ E ^ 2 * (3 * (p0 ^ 2 + (a₀ * T) ^ 2 +
      (b * σ') ^ 2 * (T * ∫ s in (0 : ℝ)..T, q s))) := by
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left (h3.trans ?_) (sq_nonneg _)
    nlinarith [h4]
  calc ‖h2_perp (Z t)‖ ^ 2 ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ 2 * (E ^ 2 * (3 * (p0 ^ 2 + (a₀ * T) ^ 2 +
      (b * σ') ^ 2 * (T * ∫ s in (0 : ℝ)..T, q s)))) + 2 * (σ' ^ 2 * q t) := by linarith
    _ = _ := by ring

end HRS.MC.CepH2
