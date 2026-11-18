import HRS.MC.S7E1
import HRS.MC.S7E1b

/-!
# Packet `s7_E2_subcritical_cauchy`

Route.  `E0b` gives the chaos limit `Q_0` of `hTransport` (an `L^2` kernel for `s < d/2` by `E1b`).  The
difference `Q_eps - Q_0` is the chaos limit of `h_eps - h_0` (the coefficients are linear in the kernel, and
`||x + y||^2 <= 2 ||x||^2 + 2 ||y||^2`).  By the upper half of `E1`, `E (Q_eps - Q_0)^2 <= (1/2) ||(h_eps - h_0)°||^2`,
and the canonical centring is a.e. linear, so the right side is `(1/2) ||h°_eps - h°_0||^2 -> 0` by
`localDiv_subcritical`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.Sec7.E2

open HRS HRS.Sec7

variable {d : ℕ} {ρ : Torus d → ℝ}

theorem e2_enorm_sq_add_le (x y : ℝ) : ‖x + y‖ₑ ^ 2 ≤ 2 * (‖x‖ₑ ^ 2 + ‖y‖ₑ ^ 2) := by
  simp only [Real.enorm_eq_ofReal_abs]
  rw [← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_pow (abs_nonneg _),
    ← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [sq_abs, sq_abs, sq_abs]
  nlinarith [sq_nonneg (x - y)]

theorem e2_enorm_sq_sub_le (x y : ℝ) : ‖x - y‖ₑ ^ 2 ≤ 2 * (‖x‖ₑ ^ 2 + ‖y‖ₑ ^ 2) := by
  rw [sub_eq_add_neg]
  simpa [enorm_neg] using e2_enorm_sq_add_le x (-y)

theorem e2_memLp_sub {a b : Torus d → Torus d → ℝ} {μ : Measure (Torus d × Torus d)}
    (ha : MemLp (Function.uncurry a) 2 μ) (hb : MemLp (Function.uncurry b) 2 μ) :
    MemLp (Function.uncurry (fun x y => a x y - b x y)) 2 μ := by
  have := ha.sub hb
  exact this.ae_eq (Filter.Eventually.of_forall fun z => rfl)

theorem e2_H_sub (hρ : SmoothPosDensity ρ) {e : ℕ → Torus d → ℝ} (he : IsONBL2Zero (withDensityReal ρ) e)
    {a b : Torus d → Torus d → ℝ}
    (ha : MemLp (Function.uncurry a) 2 ((withDensityReal ρ).prod (withDensityReal ρ)))
    (hb : MemLp (Function.uncurry b) 2 ((withDensityReal ρ).prod (withDensityReal ρ))) (i j : ℕ) :
    E0b.e0bH ρ e (fun x y => a x y - b x y) i j = E0b.e0bH ρ e a i j - E0b.e0bH ρ e b i j := by
  have := isProb_withDensityReal hρ.density
  have hW : MemLp (fun z : Torus d × Torus d => e i z.1 * e j z.2) 2
      ((withDensityReal ρ).prod (withDensityReal ρ)) :=
    E0b.e0b_tensor_memLp (he.memLp i) (he.memLp j)
  have ia : Integrable (fun z : Torus d × Torus d => a z.1 z.2 * (e i z.1 * e j z.2))
      ((withDensityReal ρ).prod (withDensityReal ρ)) := ha.integrable_mul hW
  have ib : Integrable (fun z : Torus d × Torus d => b z.1 z.2 * (e i z.1 * e j z.2))
      ((withDensityReal ρ).prod (withDensityReal ρ)) := hb.integrable_mul hW
  rw [E1.e1_H_prod hρ he (e2_memLp_sub ha hb), E1.e1_H_prod hρ he ha, E1.e1_H_prod hρ he hb,
    ← integral_sub ia ib]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [sub_mul]

/-- the canonical centring is a.e. linear on `L^2` kernels -/
theorem e2_cc_sub {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a b : Torus d → Torus d → ℝ}
    (ha : MemLp (Function.uncurry a) 2 (μ.prod μ)) (hb : MemLp (Function.uncurry b) 2 (μ.prod μ)) :
    (fun z : Torus d × Torus d => canonicalCenter μ (fun x y => a x y - b x y) z.1 z.2) =ᵐ[μ.prod μ]
      fun z => canonicalCenter μ a z.1 z.2 - canonicalCenter μ b z.1 z.2 := by
  have ia : Integrable (Function.uncurry a) (μ.prod μ) := ha.integrable one_le_two
  have ib : Integrable (Function.uncurry b) (μ.prod μ) := hb.integrable one_le_two
  have rowx : ∀ᵐ z ∂(μ.prod μ), Integrable (fun y => a z.1 y) μ ∧ Integrable (fun y => b z.1 y) μ := by
    have h1 := ia.prod_right_ae
    have h2 := ib.prod_right_ae
    have := (h1.and h2)
    exact Measure.quasiMeasurePreserving_fst.ae this
  have coly : ∀ᵐ z ∂(μ.prod μ), Integrable (fun x => a x z.2) μ ∧ Integrable (fun x => b x z.2) μ := by
    have h1 := ia.prod_left_ae
    have h2 := ib.prod_left_ae
    have := (h1.and h2)
    exact Measure.quasiMeasurePreserving_snd.ae this
  have ra : Integrable (fun x => ∫ y, a x y ∂μ) μ := ia.integral_prod_left
  have rb : Integrable (fun x => ∫ y, b x y ∂μ) μ := ib.integral_prod_left
  have rowae : ∀ᵐ x ∂μ, Integrable (fun y => a x y) μ ∧ Integrable (fun y => b x y) μ := by
    filter_upwards [ia.prod_right_ae, ib.prod_right_ae] with x h1 h2 using ⟨h1, h2⟩
  have dbl : ∫ x', ∫ y', (a x' y' - b x' y') ∂μ ∂μ =
      (∫ x', ∫ y', a x' y' ∂μ ∂μ) - ∫ x', ∫ y', b x' y' ∂μ ∂μ := by
    rw [← integral_sub ra rb]
    refine integral_congr_ae ?_
    filter_upwards [rowae] with x hx
    exact integral_sub hx.1 hx.2
  filter_upwards [rowx, coly] with z hr hc
  simp only [canonicalCenter]
  rw [integral_sub hr.1 hr.2, integral_sub hc.1 hc.2, dbl]
  ring

section Chaos

variable {s β : ℝ} {e : ℕ → Torus d → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {G : ℕ → Ω → ℝ}

theorem e2_chaos_sub (hρ : SmoothPosDensity ρ) (he : IsONBL2Zero (withDensityReal ρ) e)
    (hG : s7_GaussData d s β ρ e P G) {a b : Torus d → Torus d → ℝ}
    (ha : MemLp (Function.uncurry a) 2 ((withDensityReal ρ).prod (withDensityReal ρ)))
    (hb : MemLp (Function.uncurry b) 2 ((withDensityReal ρ).prod (withDensityReal ρ)))
    {Qa Qb : Ω → ℝ} (hQa : Measurable Qa) (hQb : Measurable Qb)
    (hca : s7_IsChaosLimit d s β ρ e P G a Qa) (hcb : s7_IsChaosLimit d s β ρ e P G b Qb) :
    s7_IsChaosLimit d s β ρ e P G (fun x y => a x y - b x y) (fun ω => Qa ω - Qb ω) := by
  set C : ℕ → ℕ → ℝ := fun x y => susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e x) (e y)
    with hCdef
  have hGm := hG.1
  set SA : ℕ → Ω → ℝ := fun L ω => (1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
    (∫ x, ∫ y, a x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ)) *
      (G i ω * G j ω - C i j) with hSA
  set SB : ℕ → Ω → ℝ := fun L ω => (1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
    (∫ x, ∫ y, b x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ)) *
      (G i ω * G j ω - C i j) with hSB
  have mA : ∀ L, Measurable (SA L) := fun L =>
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      (((hGm i).mul (hGm j)).sub_const _).const_mul _).const_mul _
  have mB : ∀ L, Measurable (SB L) := fun L =>
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      (((hGm i).mul (hGm j)).sub_const _).const_mul _).const_mul _
  have hcoef : ∀ i j : ℕ, (∫ x, ∫ y, (a x y - b x y) * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ)) =
      (∫ x, ∫ y, a x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ)) -
        ∫ x, ∫ y, b x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ) :=
    fun i j => e2_H_sub hρ he ha hb i j
  unfold s7_IsChaosLimit at hca hcb ⊢
  simp_rw [hcoef]
  have hpt : ∀ (L : ℕ) ω, ‖(Qa ω - Qb ω) - (1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      ((∫ x, ∫ y, a x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ)) -
        ∫ x, ∫ y, b x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ)) *
        (G i ω * G j ω - C i j)‖ₑ ^ 2 ≤
      2 * (‖Qa ω - SA L ω‖ₑ ^ 2 + ‖Qb ω - SB L ω‖ₑ ^ 2) := by
    intro L ω
    have : (Qa ω - Qb ω) - (1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      ((∫ x, ∫ y, a x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ)) -
        ∫ x, ∫ y, b x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ)) *
        (G i ω * G j ω - C i j) = (Qa ω - SA L ω) - (Qb ω - SB L ω) := by
      simp only [hSA, hSB, sub_mul, Finset.sum_sub_distrib, mul_sub]
      ring
    rw [this]
    exact e2_enorm_sq_sub_le _ _
  have hup : Tendsto (fun L : ℕ => 2 * (∫⁻ ω, ‖Qa ω - SA L ω‖ₑ ^ 2 ∂P + ∫⁻ ω, ‖Qb ω - SB L ω‖ₑ ^ 2 ∂P))
      atTop (𝓝 0) := by
    have hca' : Tendsto (fun L : ℕ => ∫⁻ ω, ‖Qa ω - SA L ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := hca
    have hcb' : Tendsto (fun L : ℕ => ∫⁻ ω, ‖Qb ω - SB L ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := hcb
    have := ENNReal.Tendsto.const_mul (hca'.add hcb') (Or.inr (by simp : (2 : ℝ≥0∞) ≠ ∞))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => bot_le) (fun L => ?_)
  calc ∫⁻ ω, ‖(Qa ω - Qb ω) - (1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      ((∫ x, ∫ y, a x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ)) -
        ∫ x, ∫ y, b x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ)) *
        (G i ω * G j ω - C i j)‖ₑ ^ 2 ∂P
      ≤ ∫⁻ ω, 2 * (‖Qa ω - SA L ω‖ₑ ^ 2 + ‖Qb ω - SB L ω‖ₑ ^ 2) ∂P := lintegral_mono fun ω => hpt L ω
    _ = 2 * (∫⁻ ω, ‖Qa ω - SA L ω‖ₑ ^ 2 ∂P + ∫⁻ ω, ‖Qb ω - SB L ω‖ₑ ^ 2 ∂P) := by
      rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left]
      exact ((hQa.sub (mA L)).enorm.pow_const 2)

end Chaos

/-! ### The packet -/

theorem s7_E2_subcritical_cauchy_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ}
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) (e : ℕ → Torus d → ℝ) (he : IsONBL2Zero (withDensityReal ρ) e)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ)
    (hG : s7_GaussData d s β ρ e P G) (Q : ℝ → Ω → ℝ)
    (hQ : ∀ ε, 0 < ε → Measurable (Q ε) ∧ s7_IsChaosLimit d s β ρ e P G (hCut d s φ ε) (Q ε)) :
    ∃ Q₀ : Ω → ℝ, Measurable Q₀ ∧ s7_IsChaosLimit d s β ρ e P G (hTransport d s φ) Q₀ ∧
      Tendsto (fun ε : ℝ => ∫⁻ ω, ‖Q ε ω - Q₀ ω‖ₑ ^ 2 ∂P) (𝓝[>] 0) (𝓝 0) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  have hprob := isProb_withDensityReal hρ.density
  obtain ⟨hcut, ⟨hTm, hTs⟩, hTL⟩ := E1b.s7_E1b_cutoff_kernel_admissible_proof hd hs0 hsd ρ hρ φ hφ
  have hL0 := hTL hs
  obtain ⟨Q₀, hQ₀m, hQ₀⟩ := E0b.s7_E0b_chaos_exists_proof hd hs0 hsd hβ ρ hρ e he P G hG
    (hTransport d s φ) hTm hTs hL0
  obtain ⟨c, hc0, hc1, hE1⟩ := E1.s7_E1_variance_sandwich_proof hd hs0 hsd hβ ρ hρ
  refine ⟨Q₀, hQ₀m, hQ₀, ?_⟩
  set μ := withDensityReal ρ with hμ
  set k : ℝ → Torus d → Torus d → ℝ := fun ε x y => hCut d s φ ε x y - hTransport d s φ x y with hk
  -- the bound for each ε > 0
  have hbound : ∀ ε : ℝ, 0 < ε → ∫⁻ ω, ‖Q ε ω - Q₀ ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (1 / 2 * s7_hcNorm2 d ρ (k ε)) := by
    intro ε hε
    obtain ⟨hcm, hcsymm, hcL⟩ := hcut ε hε
    obtain ⟨hQm, hQc⟩ := hQ ε hε
    have hch := e2_chaos_sub hρ he hG hcL hL0 hQm hQ₀m hQc hQ₀
    have hkm : Measurable (Function.uncurry (k ε)) := hcm.sub hTm
    have hks : ∀ x y, k ε x y = k ε y x := fun x y => by
      simp only [hk]; rw [hcsymm x y, hTs x y]
    have hkL : MemLp (Function.uncurry (k ε)) 2 (μ.prod μ) := e2_memLp_sub hcL hL0
    obtain ⟨hmem, -, -, hle⟩ := hE1 e he P G hG (k ε) hkm hks hkL (fun ω => Q ε ω - Q₀ ω)
      (hQm.sub hQ₀m).aemeasurable hch
    have h1 : ∫⁻ ω, ‖Q ε ω - Q₀ ω‖ₑ ^ 2 ∂P = ENNReal.ofReal (∫ ω, (Q ε ω - Q₀ ω) ^ 2 ∂P) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hmem.integrable_sq) (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
      refine lintegral_congr fun ω => ?_
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [h1]
    exact ENNReal.ofReal_le_ofReal hle
  -- the right side tends to zero
  have hdiff : Tendsto (fun ε : ℝ => eLpNorm (fun p : Torus d × Torus d =>
      canonicalCenter μ (hCut d s φ ε) p.1 p.2 - canonicalCenter μ (hTransport d s φ) p.1 p.2) 2
      (μ.prod μ)) (𝓝[>] 0) (𝓝 0) := (localDiv_subcritical hd hs0 hs ρ hρ φ hφ).2
  have hnorm : Tendsto (fun ε : ℝ => s7_hcNorm2 d ρ (k ε)) (𝓝[>] 0) (𝓝 0) := by
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hdiff
    have h2 := (h1.pow 2)
    simp only [ENNReal.toReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    obtain ⟨hcm, hcsymm, hcL⟩ := hcut ε hε'
    have hkm : Measurable (Function.uncurry (k ε)) := hcm.sub hTm
    have hkL : MemLp (Function.uncurry (k ε)) 2 (μ.prod μ) := e2_memLp_sub hcL hL0
    have hccL := E1Aux3.e1c_memLp (μ := μ) hkm hkL
    have hae := e2_cc_sub (μ := μ) hcL hL0
    unfold s7_hcNorm2
    have heq : eLpNorm (fun p : Torus d × Torus d =>
        canonicalCenter μ (hCut d s φ ε) p.1 p.2 - canonicalCenter μ (hTransport d s φ) p.1 p.2) 2 (μ.prod μ) =
        eLpNorm (Function.uncurry (canonicalCenter μ (k ε))) 2 (μ.prod μ) :=
      (eLpNorm_congr_ae hae).symm
    show (ENNReal.toReal (eLpNorm (fun p : Torus d × Torus d =>
        canonicalCenter μ (hCut d s φ ε) p.1 p.2 - canonicalCenter μ (hTransport d s φ) p.1 p.2) 2
        (μ.prod μ))) ^ 2 = _
    rw [heq]
    exact E0b.e0b_sq_eq hccL
  have hrhs : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 / 2 * s7_hcNorm2 d ρ (k ε))) (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (hnorm.const_mul (1 / 2 : ℝ))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrhs
    (Filter.Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε

end HRS.MC.Sec7.E2

end
