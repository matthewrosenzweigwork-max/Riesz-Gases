import HRS.MC.CepE4Aux6

/-!
# Packet CEPE5B, auxiliary 8: the `n`-uniform Lyapunov estimates (copy of the proof of `e4_uniform`)

For the drift `-G + F` the expectation of `∫_0^T ⟨Z_s - ρ, G(Z_s)⟩ ds` and of `∫_0^T ½|Z_s - ρ|² ds` are bounded by
explicit constants not depending on the particular `G` (only on `K1`, `cF1`, `cF2`, `R`, `ρ`, `σ'`, `T`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE4

open HRS HRS.MC.Cepa

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

section Uniform

variable [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {T σ' : ℝ} {w Z : ℝ → Ω → Ch N} {A : Ω → ℝ}

theorem e5b_lyap (S : E4Setup P ℱ N T σ' w Z A) {z0 : Ω → Ch N} (hz0 : Measurable[ℱ 0] z0) {R : ℝ}
    (hR : ∀ ω, ‖z0 ω‖ ≤ R) (ρ : Ch N) {G F : Ch N → Ch N} (hGc : Continuous G) (hFc : Continuous F)
    {βG LG βF LF : ℝ} (hβG : 0 ≤ βG) (hLG : 0 ≤ LG) (hβF : 0 ≤ βF) (hLF : 0 ≤ LF)
    (hGb : ∀ z, ‖G z‖ ≤ βG + LG * ‖z‖) (hFb : ∀ z, ‖F z‖ ≤ βF + LF * ‖z‖)
    (heq : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Z t ω = z0 ω + (∫ s in (0 : ℝ)..t, (-G (Z s ω) + F (Z s ω))) + σ' • w t ω)
    {K1 cF1 cF2 : ℝ} (hK1 : 0 ≤ K1) (hc1 : 0 ≤ cF1) (hc2 : 0 ≤ cF2)
    (hG1 : ∀ z, -K1 ≤ inner ℝ (z - ρ) (G z))
    (hF : ∀ z, inner ℝ (z - ρ) (F z) ≤ cF1 + cF2 * ((1 / 2) * ‖z - ρ‖ ^ 2)) (hT : 0 ≤ T) :
    (∫ ω, (∫ s in (0 : ℝ)..T, inner ℝ (Z s ω - ρ) (G (Z s ω))) ∂P ≤
      (1 / 2) * (R + ‖ρ‖) ^ 2 + (1 / 2) * σ' ^ 2 * (N * T) + cF1 * T + cF2 *
        (Real.exp (cF2 * T) * (((1 / 2) * (R + ‖ρ‖) ^ 2 + (1 / 2) * σ' ^ 2 * (N * T)) + (K1 + cF1) * T)) * T) ∧
    (∫ ω, (∫ s in (0 : ℝ)..T, (1 / 2) * ‖Z s ω - ρ‖ ^ 2) ∂P ≤
      (Real.exp (cF2 * T) * (((1 / 2) * (R + ‖ρ‖) ^ 2 + (1 / 2) * σ' ^ 2 * (N * T)) + (K1 + cF1) * T)) * T) := by
  classical
  have hz0m : Measurable z0 := hz0.mono (ℱ.le 0) le_rfl
  set gG : Ch N → ℝ := fun z => inner ℝ (z - ρ) (G z) with hgG
  set gF : Ch N → ℝ := fun z => inner ℝ (z - ρ) (F z) with hgF
  set gq : Ch N → ℝ := fun z => (1 / 2) * ‖z - ρ‖ ^ 2 with hgq
  have qG : E4Quad gG := ⟨e4_inner_cont hGc ρ, _, _, by positivity, by positivity,
    e4_inner_bound hβG hLG hGb ρ⟩
  have qF : E4Quad gF := ⟨e4_inner_cont hFc ρ, _, _, by positivity, by positivity,
    e4_inner_bound hβF hLF hFb ρ⟩
  have qq : E4Quad gq := ⟨continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2), ‖ρ‖ ^ 2, 1,
    by positivity, zero_le_one, e4_q_bound ρ⟩
  set Bf : Ch N → Ch N := fun z => -G z + F z with hBf
  have hBc : Continuous Bf := hGc.neg.add hFc
  have hBb : ∀ z, ‖Bf z‖ ≤ (βG + βF) + (LG + LF) * ‖z‖ := fun z => by
    have h1 := norm_add_le (-G z) (F z)
    rw [norm_neg] at h1
    have h2 := hGb z
    have h3 := hFb z
    simp only [hBf]
    nlinarith
  set IG : ℝ → ℝ := fun t => ∫ ω, (∫ s in (0 : ℝ)..t, gG (Z s ω)) ∂P with hIG
  set IF : ℝ → ℝ := fun t => ∫ ω, (∫ s in (0 : ℝ)..t, gF (Z s ω)) ∂P with hIF
  set Iq : ℝ → ℝ := fun t => ∫ ω, (∫ s in (0 : ℝ)..t, gq (Z s ω)) ∂P with hIq
  set v : ℝ → ℝ := fun s => ∫ ω, gq (Z s ω) ∂P with hv
  set v0 : ℝ := ∫ ω, gq (z0 ω) ∂P with hv0
  -- the identity
  have hid : ∀ t ∈ Icc (0 : ℝ) T, v t = v0 + (-(IG t) + IF t) + (1 / 2) * σ' ^ 2 * (N * t) := by
    intro t ht
    obtain ⟨_, h⟩ := e4_second_moment S hz0 hR ρ hBc (by positivity : 0 ≤ βG + βF) (by positivity : 0 ≤ LG + LF)
      hBb heq ht.1 ht.2
    have hinner : ∀ ω, (∫ s in (0 : ℝ)..t, inner ℝ (Z s ω - ρ) (Bf (Z s ω))) =
        ∫ s in (0 : ℝ)..t, ((-1) * gG (Z s ω) + 1 * gF (Z s ω)) := by
      intro ω
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [hBf, hgG, hgF, inner_add_right, inner_neg_right]
      ring
    simp_rw [hinner] at h
    rw [e4Q_lin S ht.1 ht.2 qG qF (-1) 1] at h
    simp only [hv, hv0, hIG, hIF]
    simp only [hgq]
    rw [h]
    ring
  -- lower bound on `IG`
  have hIGlo : ∀ t ∈ Icc (0 : ℝ) T, -(K1 * t) ≤ IG t := by
    intro t ht
    have h := e4Q_int_le S ht.1 ht.2 qG.neg (e4Quad_zero) (d := K1) (fun z => by
      have := hG1 z
      simp only [hgG]
      linarith)
    have e1 : ∫ ω, (∫ s in (0 : ℝ)..t, -gG (Z s ω)) ∂P = -(IG t) := by
      simp only [hIG, intervalIntegral.integral_neg, integral_neg]
    simp only [intervalIntegral.integral_zero, integral_zero, zero_add] at h
    rw [e1] at h
    linarith
  -- upper bound on `IF`
  have hIFup : ∀ t ∈ Icc (0 : ℝ) T, IF t ≤ cF1 * t + cF2 * Iq t := by
    intro t ht
    have h := e4Q_int_le S ht.1 ht.2 qF (qq.const_mul cF2) (d := cF1) (fun z => by
      have := hF z
      simp only [hgF, hgq]
      linarith)
    have e1 : ∫ ω, (∫ s in (0 : ℝ)..t, cF2 * gq (Z s ω)) ∂P = cF2 * Iq t := by
      simp only [hIq, intervalIntegral.integral_const_mul, integral_const_mul]
    rw [e1] at h
    simp only [hIF]
    linarith
  -- `Iq` as the integral of `v`
  have hIqv : ∀ t ∈ Icc (0 : ℝ) T, IntervalIntegrable v volume 0 t ∧ Iq t = ∫ s in (0 : ℝ)..t, v s :=
    fun t ht => e4Q_fubini S ht.1 ht.2 qq
  have hv0b : v0 ≤ (1 / 2) * (R + ‖ρ‖) ^ 2 := by
    have hint : Integrable (fun ω => gq (z0 ω)) P := by
      refine Integrable.of_bound (C := (1 / 2) * (R + ‖ρ‖) ^ 2) (hz0m.sub_const ρ |>.norm.pow_const 2 |>.const_mul _).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      have h1 : ‖z0 ω - ρ‖ ≤ R + ‖ρ‖ := (norm_sub_le _ _).trans (by linarith [hR ω])
      have h2 : ‖z0 ω - ρ‖ ^ 2 ≤ (R + ‖ρ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      simp only [hgq, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      linarith
    have := integral_mono_of_nonneg (μ := P) (f := fun ω => gq (z0 ω)) (g := fun _ => (1 / 2) * (R + ‖ρ‖) ^ 2)
      (Filter.Eventually.of_forall fun ω => by simp only [hgq]; positivity) (integrable_const _)
      (Filter.Eventually.of_forall fun ω => by
        have h1 : ‖z0 ω - ρ‖ ≤ R + ‖ρ‖ := (norm_sub_le _ _).trans (by linarith [hR ω])
        have h2 : ‖z0 ω - ρ‖ ^ 2 ≤ (R + ‖ρ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        simp only [hgq]
        linarith)
    simpa using this
  have hv_nonneg : ∀ t, 0 ≤ v t := fun t => integral_nonneg fun ω => by simp only [hgq]; positivity
  set v0b : ℝ := (1 / 2) * (R + ‖ρ‖) ^ 2 with hv0bdef
  have hv0b0 : 0 ≤ v0b := by positivity
  have hσN : 0 ≤ (1 / 2) * σ' ^ 2 * (N * T) := by positivity
  -- Grönwall
  have hv_int : IntervalIntegrable v volume 0 T := (hIqv T ⟨hT, le_rfl⟩).1
  have hgron : ∀ t ∈ Icc (0 : ℝ) T, v t ≤ Real.exp (cF2 * T) * ((v0b + (1 / 2) * σ' ^ 2 * (N * T)) + (K1 + cF1) * T) := by
    refine e4_gronwall_int (v := v) (T := T) (κ := cF2) (a0 := v0b + (1 / 2) * σ' ^ 2 * (N * T)) (b := K1 + cF1)
      hT hc2 (by positivity) (by positivity) hv_int fun t ht => ?_
    have h1 := hid t ht
    have h2 := hIGlo t ht
    have h3 := hIFup t ht
    obtain ⟨hvi, hIq'⟩ := hIqv t ht
    have h4 : ∫ r in (0 : ℝ)..t, (cF2 * v r + (K1 + cF1)) = cF2 * (∫ r in (0 : ℝ)..t, v r) + (K1 + cF1) * t := by
      rw [intervalIntegral.integral_add (hvi.const_mul cF2) intervalIntegrable_const,
        intervalIntegral.integral_const_mul]
      simp
      ring
    rw [h4]
    have h5 : (1 / 2) * σ' ^ 2 * (N * t) ≤ (1 / 2) * σ' ^ 2 * (N * T) := by
      have : (N : ℝ) * t ≤ N * T := mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg _)
      have : 0 ≤ (1 / 2) * σ' ^ 2 := by positivity
      nlinarith
    rw [hIq'] at h3
    nlinarith
  -- final estimate
  set M : ℝ := Real.exp (cF2 * T) * ((v0b + (1 / 2) * σ' ^ 2 * (N * T)) + (K1 + cF1) * T) with hM
  have hIqT : Iq T ≤ M * T := by
    obtain ⟨hvi, hIq'⟩ := hIqv T ⟨hT, le_rfl⟩
    rw [hIq']
    have := intervalIntegral.integral_mono_on hT hvi (intervalIntegrable_const (c := M)) fun s hs => hgron s hs
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    linarith
  have hIGT : IG T ≤ v0b + (1 / 2) * σ' ^ 2 * (N * T) + cF1 * T + cF2 * M * T := by
    have h1 := hid T ⟨hT, le_rfl⟩
    have h3 := hIFup T ⟨hT, le_rfl⟩
    have h4 := hv_nonneg T
    have h5 : cF2 * Iq T ≤ cF2 * (M * T) := mul_le_mul_of_nonneg_left hIqT hc2
    nlinarith
  exact ⟨hIGT, hIqT⟩

end Uniform

end HRS.MC.CepE4
