import HRS.MC.CepE4Aux5

/-!
# Packet CEPE4, auxiliary 6: Fubini helpers and the `n`-uniform estimate
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE4

open HRS HRS.MC.Cepa

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

section Helpers

variable [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {T σ' : ℝ} {w Z : ℝ → Ω → Ch N} {A : Ω → ℝ}

/-- Time-integrals of a quadratic-growth function of the path are integrable in `ω`. -/
theorem e4_int_inner (S : E4Setup P ℱ N T σ' w Z A) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {g : Ch N → ℝ}
    (hg : Continuous g) {c0 c1 : ℝ} (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hgb : ∀ z, |g z| ≤ c0 + c1 * ‖z‖ ^ 2) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..t, g (Z s ω)) P := by
  have := (e4_g_integrable S ht0 htT hg hc0 hc1 hgb).integral_prod_right
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  rw [intervalIntegral.integral_of_le ht0]

/-- Fubini for a quadratic-growth function of the path. -/
theorem e4_fubini (S : E4Setup P ℱ N T σ' w Z A) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {g : Ch N → ℝ}
    (hg : Continuous g) {c0 c1 : ℝ} (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hgb : ∀ z, |g z| ≤ c0 + c1 * ‖z‖ ^ 2) :
    IntervalIntegrable (fun s => ∫ ω, g (Z s ω) ∂P) volume 0 t ∧
    ∫ ω, (∫ s in (0 : ℝ)..t, g (Z s ω)) ∂P = ∫ s in (0 : ℝ)..t, ∫ ω, g (Z s ω) ∂P := by
  have hint := e4_g_integrable S ht0 htT hg hc0 hc1 hgb
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht0]
    exact hint.integral_prod_left
  · simp_rw [intervalIntegral.integral_of_le ht0]
    exact (integral_integral_swap (μ := e4_mu t) (ν := P) (f := fun s ω => g (Z s ω)) hint).symm

end Helpers

/-- Grönwall for an interval-integrable (not necessarily continuous) function. -/
theorem e4_gronwall_int {v : ℝ → ℝ} {T κ a0 b : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hb : 0 ≤ b) (ha : 0 ≤ a0)
    (hv : IntervalIntegrable v volume 0 T)
    (h : ∀ t ∈ Icc (0 : ℝ) T, v t ≤ a0 + ∫ r in (0 : ℝ)..t, (κ * v r + b)) :
    ∀ t ∈ Icc (0 : ℝ) T, v t ≤ Real.exp (κ * T) * (a0 + b * T) := by
  set ψ : ℝ → ℝ := fun t => a0 + ∫ r in (0 : ℝ)..t, (κ * v r + b) with hψ
  have hvT : IntegrableOn v (Icc 0 T) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT] at hv
    exact hv
  have hfi : IntegrableOn (fun r => κ * v r + b) (Icc 0 T) :=
    (hvT.const_mul κ).add (integrableOn_const (by simp))
  have hψc : ContinuousOn ψ (Icc 0 T) := by
    have : ContinuousOn (fun t => ∫ r in (0 : ℝ)..t, (κ * v r + b)) (Icc 0 T) := by
      have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T) (μ := volume)
        (f := fun r => κ * v r + b) (by rwa [uIcc_of_le hT])
      rwa [uIcc_of_le hT] at this
    exact continuousOn_const.add this
  have hψI : ∀ t ∈ Icc (0 : ℝ) T, IntervalIntegrable ψ volume 0 t := fun t ht =>
    (hψc.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hvψ : ∀ t ∈ Icc (0 : ℝ) T, v t ≤ ψ t := fun t ht => h t ht
  have hvI : ∀ t ∈ Icc (0 : ℝ) T, IntervalIntegrable v volume 0 t := fun t ht =>
    hv.mono_set (by rw [uIcc_of_le hT, uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)
  have hψψ : ∀ t ∈ Icc (0 : ℝ) T, ψ t ≤ a0 + ∫ r in (0 : ℝ)..t, (κ * ψ r + b) := by
    intro t ht
    have : ∫ r in (0 : ℝ)..t, (κ * v r + b) ≤ ∫ r in (0 : ℝ)..t, (κ * ψ r + b) := by
      refine intervalIntegral.integral_mono_on ht.1 (((hvI t ht).const_mul κ).add intervalIntegrable_const)
        (((hψI t ht).const_mul κ).add intervalIntegrable_const) fun r hr => ?_
      have := hvψ r ⟨hr.1, hr.2.trans ht.2⟩
      nlinarith
    simp only [hψ]
    linarith
  have := e4_gronwall_aff (φ := ψ) hT hκ hb ha hψc hψψ
  exact fun t ht => (hvψ t ht).trans (this t ht)

section Helpers2

variable [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {T σ' : ℝ} {w Z : ℝ → Ω → Ch N} {A : Ω → ℝ}

/-- Monotonicity of the expected time integral, up to a constant. -/
theorem e4_int_le (S : E4Setup P ℱ N T σ' w Z A) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {g1 g2 : Ch N → ℝ}
    (hg1 : Continuous g1) (hg2 : Continuous g2) {a0 a1 b0 b1 : ℝ} (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hb0 : 0 ≤ b0)
    (hb1 : 0 ≤ b1) (hg1b : ∀ z, |g1 z| ≤ a0 + a1 * ‖z‖ ^ 2) (hg2b : ∀ z, |g2 z| ≤ b0 + b1 * ‖z‖ ^ 2)
    {d : ℝ} (h : ∀ z, g1 z ≤ g2 z + d) :
    ∫ ω, (∫ s in (0 : ℝ)..t, g1 (Z s ω)) ∂P ≤ ∫ ω, (∫ s in (0 : ℝ)..t, g2 (Z s ω)) ∂P + d * t := by
  have i1 := e4_int_inner S ht0 htT hg1 ha0 ha1 hg1b
  have i2 := e4_int_inner S ht0 htT hg2 hb0 hb1 hg2b
  have : ∫ ω, (∫ s in (0 : ℝ)..t, g1 (Z s ω)) ∂P ≤ ∫ ω, ((∫ s in (0 : ℝ)..t, g2 (Z s ω)) + d * t) ∂P := by
    refine integral_mono i1 (i2.add (integrable_const _)) fun ω => ?_
    simp only
    have hc1 : Continuous fun s => g1 (Z s ω) := hg1.comp (S.Zc ω)
    have hc2 : Continuous fun s => g2 (Z s ω) := hg2.comp (S.Zc ω)
    calc ∫ s in (0 : ℝ)..t, g1 (Z s ω) ≤ ∫ s in (0 : ℝ)..t, (g2 (Z s ω) + d) :=
          intervalIntegral.integral_mono_on ht0 (hc1.intervalIntegrable _ _)
            ((hc2.add continuous_const).intervalIntegrable _ _) fun s _ => h _
      _ = (∫ s in (0 : ℝ)..t, g2 (Z s ω)) + d * t := by
          rw [intervalIntegral.integral_add (hc2.intervalIntegrable _ _) intervalIntegrable_const]
          simp [mul_comm]
  rw [integral_add i2 (integrable_const _)] at this
  simpa using this

end Helpers2

theorem e4_q_bound (ρ z : Ch N) :
    |(1 / 2) * ‖z - ρ‖ ^ 2| ≤ ‖ρ‖ ^ 2 + 1 * ‖z‖ ^ 2 := by
  have h := norm_sub_le z ρ
  rw [abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (‖z‖ - ‖ρ‖), norm_nonneg z, norm_nonneg ρ, norm_nonneg (z - ρ)]

theorem e4_l1_bound {G : Ch N → Ch N} {β L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L) (hGb : ∀ z, ‖G z‖ ≤ β + L * ‖z‖)
    (z : Ch N) : abs (∑ k, |(G z) k|) ≤ (N * β + N * L) + (N * L) * ‖z‖ ^ 2 := by
  have h1 : ∑ k, |(G z) k| ≤ ∑ _k : Fin N, ‖G z‖ := Finset.sum_le_sum fun k _ => by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (G z) k
  have h2 : ∑ _k : Fin N, ‖G z‖ = N * ‖G z‖ := by simp
  have h3 := hGb z
  have hz := norm_nonneg z
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  rw [abs_of_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)]
  have h4 : (N : ℝ) * ‖G z‖ ≤ N * (β + L * ‖z‖) := mul_le_mul_of_nonneg_left h3 hN
  have h5 : (0 : ℝ) ≤ ‖z‖ ^ 2 - ‖z‖ + 1 := by nlinarith [sq_nonneg (‖z‖ - 1 / 2)]
  nlinarith [mul_nonneg (mul_nonneg hN hL) h5]

/-- Continuous functions of quadratic growth. -/
def E4Quad (g : Ch N → ℝ) : Prop :=
  Continuous g ∧ ∃ c0 c1 : ℝ, 0 ≤ c0 ∧ 0 ≤ c1 ∧ ∀ z, |g z| ≤ c0 + c1 * ‖z‖ ^ 2

theorem E4Quad.neg {g : Ch N → ℝ} (h : E4Quad g) : E4Quad (fun z => -g z) := by
  obtain ⟨hc, c0, c1, h0, h1, hb⟩ := h
  exact ⟨hc.neg, c0, c1, h0, h1, fun z => by simpa using hb z⟩

theorem E4Quad.const_mul {g : Ch N → ℝ} (h : E4Quad g) (c : ℝ) : E4Quad (fun z => c * g z) := by
  obtain ⟨hc, c0, c1, h0, h1, hb⟩ := h
  refine ⟨continuous_const.mul hc, |c| * c0, |c| * c1, by positivity, by positivity, fun z => ?_⟩
  rw [abs_mul]
  have := mul_le_mul_of_nonneg_left (hb z) (abs_nonneg c)
  linarith

theorem E4Quad.add {g h : Ch N → ℝ} (hg : E4Quad g) (hh : E4Quad h) : E4Quad (fun z => g z + h z) := by
  obtain ⟨hc, c0, c1, h0, h1, hb⟩ := hg
  obtain ⟨hc', d0, d1, g0, g1, hb'⟩ := hh
  refine ⟨hc.add hc', c0 + d0, c1 + d1, by positivity, by positivity, fun z => ?_⟩
  have := abs_add_le (g z) (h z)
  have := hb z
  have := hb' z
  nlinarith

theorem e4Quad_zero : E4Quad (fun _ : Ch N => (0 : ℝ)) :=
  ⟨continuous_const, 0, 0, le_rfl, le_rfl, fun z => by simp⟩

theorem e4Quad_const (c : ℝ) : E4Quad (fun _ : Ch N => c) :=
  ⟨continuous_const, |c|, 0, abs_nonneg _, le_rfl, fun z => by simp⟩

section QuadAPI

variable [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {T σ' : ℝ} {w Z : ℝ → Ω → Ch N} {A : Ω → ℝ}

theorem e4Q_int_inner (S : E4Setup P ℱ N T σ' w Z A) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {g : Ch N → ℝ}
    (hg : E4Quad g) : Integrable (fun ω => ∫ s in (0 : ℝ)..t, g (Z s ω)) P := by
  obtain ⟨hc, c0, c1, h0, h1, hb⟩ := hg
  exact e4_int_inner S ht0 htT hc h0 h1 hb

theorem e4Q_fubini (S : E4Setup P ℱ N T σ' w Z A) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {g : Ch N → ℝ}
    (hg : E4Quad g) :
    IntervalIntegrable (fun s => ∫ ω, g (Z s ω) ∂P) volume 0 t ∧
    ∫ ω, (∫ s in (0 : ℝ)..t, g (Z s ω)) ∂P = ∫ s in (0 : ℝ)..t, ∫ ω, g (Z s ω) ∂P := by
  obtain ⟨hc, c0, c1, h0, h1, hb⟩ := hg
  exact e4_fubini S ht0 htT hc h0 h1 hb

theorem e4Q_int_le (S : E4Setup P ℱ N T σ' w Z A) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {g1 g2 : Ch N → ℝ}
    (hg1 : E4Quad g1) (hg2 : E4Quad g2) {d : ℝ} (h : ∀ z, g1 z ≤ g2 z + d) :
    ∫ ω, (∫ s in (0 : ℝ)..t, g1 (Z s ω)) ∂P ≤ ∫ ω, (∫ s in (0 : ℝ)..t, g2 (Z s ω)) ∂P + d * t := by
  obtain ⟨hc1, a0, a1, ha0, ha1, hb1⟩ := hg1
  obtain ⟨hc2, b0, b1, hb0, hb1', hb2⟩ := hg2
  exact e4_int_le S ht0 htT hc1 hc2 ha0 ha1 hb0 hb1' hb1 hb2 h

theorem e4Q_lin (S : E4Setup P ℱ N T σ' w Z A) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {g h : Ch N → ℝ}
    (hg : E4Quad g) (hh : E4Quad h) (c d : ℝ) :
    ∫ ω, (∫ s in (0 : ℝ)..t, (c * g (Z s ω) + d * h (Z s ω))) ∂P =
      c * (∫ ω, (∫ s in (0 : ℝ)..t, g (Z s ω)) ∂P) + d * (∫ ω, (∫ s in (0 : ℝ)..t, h (Z s ω)) ∂P) := by
  have cg : ∀ ω, Continuous fun s => g (Z s ω) := fun ω => hg.1.comp (S.Zc ω)
  have ch : ∀ ω, Continuous fun s => h (Z s ω) := fun ω => hh.1.comp (S.Zc ω)
  have e : ∀ ω, (∫ s in (0 : ℝ)..t, (c * g (Z s ω) + d * h (Z s ω))) =
      c * (∫ s in (0 : ℝ)..t, g (Z s ω)) + d * (∫ s in (0 : ℝ)..t, h (Z s ω)) := by
    intro ω
    have c1 : Continuous fun s => c * g (Z s ω) := continuous_const.mul (cg ω)
    have c2 : Continuous fun s => d * h (Z s ω) := continuous_const.mul (ch ω)
    rw [intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp_rw [e]
  have i1 : Integrable (fun ω => c * (∫ s in (0 : ℝ)..t, g (Z s ω))) P := (e4Q_int_inner S ht0 htT hg).const_mul c
  have i2 : Integrable (fun ω => d * (∫ s in (0 : ℝ)..t, h (Z s ω))) P := (e4Q_int_inner S ht0 htT hh).const_mul d
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul]

end QuadAPI

/-- The explicit bound of `e4_uniform`. -/
def e4_bound (N : ℕ) (R ρn σ' T K1 K2 cF1 cF2 : ℝ) : ℝ :=
  8 * N * ((1 / 2) * (R + ρn) ^ 2 + (1 / 2) * σ' ^ 2 * (N * T) + cF1 * T +
    cF2 * (Real.exp (cF2 * T) * ((1 / 2) * (R + ρn) ^ 2 + (1 / 2) * σ' ^ 2 * (N * T) + (K1 + cF1) * T)) * T) + K2 * T

section Uniform

variable [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {T σ' : ℝ} {w Z : ℝ → Ω → Ch N} {A : Ω → ℝ}

theorem e4_uniform (S : E4Setup P ℱ N T σ' w Z A) {z0 : Ω → Ch N} (hz0 : Measurable[ℱ 0] z0) {R : ℝ}
    (hR : ∀ ω, ‖z0 ω‖ ≤ R) (ρ : Ch N) {G F : Ch N → Ch N} (hGc : Continuous G) (hFc : Continuous F)
    {βG LG βF LF : ℝ} (hβG : 0 ≤ βG) (hLG : 0 ≤ LG) (hβF : 0 ≤ βF) (hLF : 0 ≤ LF)
    (hGb : ∀ z, ‖G z‖ ≤ βG + LG * ‖z‖) (hFb : ∀ z, ‖F z‖ ≤ βF + LF * ‖z‖)
    (heq : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Z t ω = z0 ω + (∫ s in (0 : ℝ)..t, (-G (Z s ω) + F (Z s ω))) + σ' • w t ω)
    {K1 K2 cF1 cF2 : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hc1 : 0 ≤ cF1) (hc2 : 0 ≤ cF2)
    (hG1 : ∀ z, -K1 ≤ inner ℝ (z - ρ) (G z))
    (hG2 : ∀ z, ∑ k, |(G z) k| ≤ 8 * N * inner ℝ (z - ρ) (G z) + K2)
    (hF : ∀ z, inner ℝ (z - ρ) (F z) ≤ cF1 + cF2 * ((1 / 2) * ‖z - ρ‖ ^ 2)) (hT : 0 ≤ T) :
    ∫ ω, (∫ s in (0 : ℝ)..T, ∑ k, |(G (Z s ω)) k|) ∂P ≤ e4_bound N R ‖ρ‖ σ' T K1 K2 cF1 cF2 := by
  classical
  have hz0m : Measurable z0 := hz0.mono (ℱ.le 0) le_rfl
  set gG : Ch N → ℝ := fun z => inner ℝ (z - ρ) (G z) with hgG
  set gF : Ch N → ℝ := fun z => inner ℝ (z - ρ) (F z) with hgF
  set gq : Ch N → ℝ := fun z => (1 / 2) * ‖z - ρ‖ ^ 2 with hgq
  set gN : Ch N → ℝ := fun z => ∑ k, |(G z) k| with hgN
  have qG : E4Quad gG := ⟨e4_inner_cont hGc ρ, _, _, by positivity, by positivity,
    e4_inner_bound hβG hLG hGb ρ⟩
  have qF : E4Quad gF := ⟨e4_inner_cont hFc ρ, _, _, by positivity, by positivity,
    e4_inner_bound hβF hLF hFb ρ⟩
  have qq : E4Quad gq := ⟨continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2), ‖ρ‖ ^ 2, 1,
    by positivity, zero_le_one, e4_q_bound ρ⟩
  have qN : E4Quad gN := ⟨continuous_finset_sum _ fun k _ => ((EuclideanSpace.proj k).continuous.comp hGc).abs,
    _, _, by positivity, by positivity, e4_l1_bound hβG hLG hGb⟩
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
  have hfin := e4Q_int_le S hT le_rfl qN (qG.const_mul (8 * N)) (d := K2) (fun z => by
    have := hG2 z
    simp only [hgN, hgG]
    linarith)
  have e1 : ∫ ω, (∫ s in (0 : ℝ)..T, (8 * (N : ℝ)) * gG (Z s ω)) ∂P = (8 * N) * IG T := by
    simp only [hIG, intervalIntegral.integral_const_mul, integral_const_mul]
  rw [e1] at hfin
  have h8 : (8 * (N : ℝ)) * IG T ≤ (8 * N) * (v0b + (1 / 2) * σ' ^ 2 * (N * T) + cF1 * T + cF2 * M * T) :=
    mul_le_mul_of_nonneg_left hIGT (by positivity)
  unfold e4_bound
  rw [hM, hv0bdef] at h8
  simp only [hgN] at hfin
  linarith

end Uniform

end HRS.MC.CepE4
