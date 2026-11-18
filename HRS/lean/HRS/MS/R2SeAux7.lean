import HRS.MS.R2SeAux6

/-!
# S9.9 `r2_static_edgeworth`, packet 7: moment, bias and law-of-large-numbers bounds under `Q_{N,γ}`

Worker S99, namespace `S99`.  For the particle law `P = S46.s46_P d s a β γ N = Q_{N,γ}(μ)`, `ν = firstMarginal P`:

* `s99_Y_L2`: `E Y_u² ≤ (K‖u‖_∞)²` for bounded measurable `u`, `Y_u = √N(μ_N(u) - ν(u))` (S9.5, linear bound);
* `s99_bias`: `|ν(u) - μ(u)| ≤ K‖u‖_∞/N` (`S46Static.marg`, `δ_N = 1/N` for `s < d/2`);
* `s99_T_L2`: `E(μ_N(u) - μ(u))² ≤ (K‖u‖_∞)²/N`;
* `s99_Bq`: for a corrector `χ` (`‖D²χ‖ ≤ B₂`), the quadratic statistic `Bq = N(F^h_N - E F^h_N)`,
  `h = commutatorKernel d s (∇χ)`, satisfies `E Bq² ≤ (K B₂)²` and `E|Bq| ≤ K B₂` (S9.5, pair energy bound).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- The quadratic statistic `Bq = N(F^h_N - E F^h_N)` of a corrector, `h = commutatorKernel d s (∇χ)`. -/
def Bq (d : ℕ) (s a β γ : ℝ) (N : ℕ) (χ : Euc d → ℝ) (X : EucConfig d N) : ℝ :=
  (N : ℝ) * (pairEnergy (commutatorKernel d s (gradient χ)) X (thermalMeasure d s a β) -
    ∫ Y, pairEnergy (commutatorKernel d s (gradient χ)) Y (thermalMeasure d s a β)
      ∂(S46.s46_P d s a β γ N))

theorem s99_sqrt_Rp (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ C c BU Cs : ℝ}
    (hT : ThermalData d s a β C c BU) (hN : 2 ≤ N) (hS : S46.S46Static d s a β γ Cs N)
    {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ) {B2 : ℝ} (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2)
    (X : EucConfig d N) :
    Real.sqrt N * s45_Rp (thermalMeasure d s a β) (S46.s46_nu d s a β γ N) (S46.s46_P d s a β γ N)
        (commutatorKernel d s (gradient χ)) X = -(Bq d s a β γ N χ X) / Real.sqrt N := by
  rw [s99_Rp_eq hd hs0 hsd hT hN hS hχ hB2 X]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsq : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 hN0).ne'
  have hsq2 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  unfold Bq
  rw [eq_div_iff hsq]
  generalize pairEnergy (commutatorKernel d s (gradient χ)) X (thermalMeasure d s a β) -
    ∫ Y, pairEnergy (commutatorKernel d s (gradient χ)) Y (thermalMeasure d s a β)
      ∂(S46.s46_P d s a β γ N) = t
  calc Real.sqrt N * -t * Real.sqrt N = -(Real.sqrt N * Real.sqrt N) * t := by ring
    _ = -((N : ℝ) * t) := by rw [hsq2]; ring

section Mom

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : S45.ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)

include hd hs0 hs ha hβ hγ hT hS

theorem s99_Y_L2 : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ B : ℝ, 0 ≤ B → ∀ u : Euc d → ℝ,
    Measurable u → (∀ x, |u x| ≤ B) →
    Integrable (fun X : EucConfig d N =>
      (s45_Yi N u (pair (S46.s46_nu d s a β γ N) u) X) ^ 2) (S46.s46_P d s a β γ N) ∧
    ∫ X, (s45_Yi N u (pair (S46.s46_nu d s a β γ N) u) X) ^ 2 ∂(S46.s46_P d s a β γ N) ≤
      (K * B) ^ 2 := by
  obtain ⟨C₁, hC₁, -, h3, -⟩ := s99_mom hd hs0 hs ha hβ hγ hT hS 2 (by norm_num)
  refine ⟨C₁, hC₁, fun N hN B hB u hu hub => ?_⟩
  have hN1 : 1 ≤ N := by omega
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
  set P := S46.s46_P d s a β γ N with hPdef
  set ν := S46.s46_nu d s a β γ N with hνdef
  haveI hν : IsProbabilityMeasure ν := s99_nu_prob hN1
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  set μ := thermalMeasure d s a β with hμdef
  set Z : EucConfig d N → ℝ := fun X => Real.sqrt N * (pair (empirical X) u - pair μ u) with hZdef
  have hmeas : Measurable Z :=
    measurable_const.mul ((s45_measurable_pair_empirical hN1 hu).sub measurable_const)
  have h3' : eLpNorm Z 2 P ≤ ENNReal.ofReal (C₁ * B) := by
    simpa [hZdef] using h3 N hN B hB u hu hub
  obtain ⟨hZmem, hZ2⟩ := s99_l2_bound (mul_nonneg hC₁ hB) hmeas.aestronglyMeasurable h3'
  set β0 : ℝ := Real.sqrt N * (pair ν u - pair μ u) with hβ0
  have hY : ∀ X : EucConfig d N, s45_Yi N u (pair ν u) X = Z X - β0 := fun X => by
    simp only [s45_Yi, hβ0, hZdef]; ring
  have hEZ : ∫ X, Z X ∂P = β0 := by
    have hb1 : ∀ X : EucConfig d N, |pair (empirical X) u| ≤ B := fun X =>
      s45_abs_pair_empirical_le hN1 hub X
    have hint1 : Integrable (fun X : EucConfig d N => pair (empirical X) u) P :=
      Integrable.of_bound (s45_measurable_pair_empirical hN1 hu).aestronglyMeasurable B
        (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hb1 X)
    simp only [hZdef]
    rw [integral_const_mul, integral_sub hint1 (integrable_const _),
      s45_E_pair_empirical hN1 (hS N hN).exch hu hub, integral_const]
    simp [hβ0]
    left; rfl
  have hYbd : ∀ X : EucConfig d N, |s45_Yi N u (pair ν u) X| ≤ 2 * Real.sqrt N * B := by
    intro X
    simp only [s45_Yi]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 := s45_abs_pair_empirical_le hN1 hub X
    have h2 : |pair ν u| ≤ B := HRS.MS.Tc5.tc5_pair_le (fun x => by rw [Real.norm_eq_abs]; exact hub x)
    calc Real.sqrt N * |pair (empirical X) u - pair ν u|
        ≤ Real.sqrt N * (|pair (empirical X) u| + |pair ν u|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt N * (B + B) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Real.sqrt_nonneg _)
      _ = 2 * Real.sqrt N * B := by ring
  have hYmeas : Measurable fun X : EucConfig d N => s45_Yi N u (pair ν u) X :=
    measurable_const.mul ((s45_measurable_pair_empirical hN1 hu).sub measurable_const)
  have hYint : Integrable (fun X : EucConfig d N => (s45_Yi N u (pair ν u) X) ^ 2) P := by
    refine Integrable.of_bound (hYmeas.pow_const 2).aestronglyMeasurable ((2 * Real.sqrt N * B) ^ 2)
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hYbd X) 2
  refine ⟨hYint, ?_⟩
  have e : ∫ X, (s45_Yi N u (pair ν u) X) ^ 2 ∂P = (∫ X, (Z X) ^ 2 ∂P) - β0 ^ 2 := by
    have h1 : ∫ X, (s45_Yi N u (pair ν u) X) ^ 2 ∂P = ∫ X, (Z X - β0) ^ 2 ∂P := by
      congr 1; funext X; rw [hY X]
    rw [h1]
    have h2 : variance Z P = ∫ X, (Z X - β0) ^ 2 ∂P := by
      rw [variance_eq_integral hmeas.aemeasurable, hEZ]
    have h3 : variance Z P = (∫ X, (Z X) ^ 2 ∂P) - β0 ^ 2 := by
      rw [variance_eq_sub hZmem]; simp only [Pi.pow_apply, hEZ]
    rw [← h2, h3]
  rw [e]
  have h2 : ∫ X, (Z X) ^ 2 ∂P ≤ (C₁ * B) ^ 2 := hZ2
  nlinarith [sq_nonneg β0]

theorem s99_bias : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ B : ℝ, 0 ≤ B → ∀ u : Euc d → ℝ,
    Measurable u → (∀ x, |u x| ≤ B) →
    |pair (S46.s46_nu d s a β γ N) u - pair (thermalMeasure d s a β) u| ≤ K * B / N := by
  refine ⟨max Cs 0, le_max_right _ _, fun N hN B hB u hu hub => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  set μ := thermalMeasure d s a β with hμdef
  obtain ⟨φN, hφNm, hνeq, hφNb, hφN2, hφNn⟩ := (hS N hN).marg
  have hCs0 : 0 ≤ Cs := le_trans (hφNb 0).1 (hφNb 0).2
  have hpν : pair (S46.s46_nu d s a β γ N) u = ∫ x, φN x * u x ∂μ := by
    unfold pair
    rw [hνeq, integral_withDensity_eq_integral_toReal_smul]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul]
      rw [ENNReal.toReal_ofReal (hφNb x).1]
    · exact hφNm.ennreal_ofReal
    · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hum : AEStronglyMeasurable u μ := hu.aestronglyMeasurable
  have hu_int : Integrable u μ := Integrable.of_bound hum B
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hub x)
  have hφu_int : Integrable (fun x => φN x * u x) μ :=
    Integrable.of_bound (hφNm.mul hu).aestronglyMeasurable (Cs * B)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (by rw [abs_of_nonneg (hφNb x).1]; exact (hφNb x).2) (hub x) (abs_nonneg _)
          hCs0)
  have hdiff : pair (S46.s46_nu d s a β γ N) u - pair μ u = ∫ x, (φN x - 1) * u x ∂μ := by
    rw [hpν]; unfold pair
    rw [← integral_sub hφu_int hu_int]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hdiff]
  have hg : MemLp (fun x => |φN x - 1|) 2 μ := hφN2.abs
  have hgint : Integrable (fun x => |φN x - 1|) μ := hg.integrable (by norm_num)
  have h1 : |∫ x, (φN x - 1) * u x ∂μ| ≤ B * ∫ x, |φN x - 1| ∂μ := by
    calc |∫ x, (φN x - 1) * u x ∂μ| ≤ ∫ x, |(φN x - 1) * u x| ∂μ := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ) (fun x => (φN x - 1) * u x)
      _ ≤ ∫ x, B * |φN x - 1| ∂μ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
            (hgint.const_mul B) (Filter.Eventually.of_forall fun x => ?_)
          show |(φN x - 1) * u x| ≤ B * |φN x - 1|
          rw [abs_mul, mul_comm B]
          exact mul_le_mul_of_nonneg_left (hub x) (abs_nonneg _)
      _ = B * ∫ x, |φN x - 1| ∂μ := by rw [integral_const_mul]
  have h2 : ∫ x, |φN x - 1| ∂μ ≤ l2Norm μ (fun x => φN x - 1) := by
    have hv := variance_nonneg (fun x => |φN x - 1|) μ
    rw [variance_eq_sub hg] at hv
    have hI0 : 0 ≤ ∫ x, |φN x - 1| ∂μ := integral_nonneg fun x => abs_nonneg _
    unfold l2Norm
    refine Real.le_sqrt_of_sq_le ?_
    have e : ∫ x, (φN x - 1) ^ 2 ∂μ = ∫ x, (|φN x - 1|) ^ 2 ∂μ := by
      congr 1; funext x; rw [sq_abs]
    rw [e]
    simpa [Pi.pow_apply] using (sub_nonneg.1 hv)
  have hδ : HRS.deltaN d s N = 1 / N := by
    have := HRS.MS.R2Mt.s92_mul_deltaN (d := d) (N := N) hs hN
    field_simp
    linarith
  calc |∫ x, (φN x - 1) * u x ∂μ| ≤ B * ∫ x, |φN x - 1| ∂μ := h1
    _ ≤ B * l2Norm μ (fun x => φN x - 1) := mul_le_mul_of_nonneg_left h2 hB
    _ ≤ B * (Cs * HRS.deltaN d s N) := mul_le_mul_of_nonneg_left hφNn hB
    _ ≤ max Cs 0 * B / N := by
        rw [hδ]
        have : Cs ≤ max Cs 0 := le_max_left _ _
        have h3 : B * (Cs * (1 / (N : ℝ))) = (B * Cs) / N := by ring
        rw [h3, mul_comm (max Cs 0) B]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this hB) hN0.le

theorem s99_T_L2 : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ B : ℝ, 0 ≤ B → ∀ u : Euc d → ℝ,
    Measurable u → (∀ x, |u x| ≤ B) →
    ∫ X, (pair (empirical X) u - pair (thermalMeasure d s a β) u) ^ 2 ∂(S46.s46_P d s a β γ N) ≤
      (K * B) ^ 2 / N := by
  obtain ⟨C₁, hC₁, -, h3, -⟩ := s99_mom hd hs0 hs ha hβ hγ hT hS 2 (by norm_num)
  refine ⟨C₁, hC₁, fun N hN B hB u hu hub => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
  set Z : EucConfig d N → ℝ := fun X => Real.sqrt N *
    (pair (empirical X) u - pair (thermalMeasure d s a β) u) with hZdef
  have hmeas : Measurable Z :=
    measurable_const.mul ((s45_measurable_pair_empirical hN1 hu).sub measurable_const)
  have h3' : eLpNorm Z 2 (S46.s46_P d s a β γ N) ≤ ENNReal.ofReal (C₁ * B) := by
    simpa [hZdef] using h3 N hN B hB u hu hub
  obtain ⟨hZmem, hZ2⟩ := s99_l2_bound (mul_nonneg hC₁ hB) hmeas.aestronglyMeasurable h3'
  have e : ∀ X : EucConfig d N, (Z X) ^ 2 = N * (pair (empirical X) u -
      pair (thermalMeasure d s a β) u) ^ 2 := fun X => by
    simp only [hZdef]; rw [mul_pow, Real.sq_sqrt hN0.le]
  have : ∫ X, (Z X) ^ 2 ∂(S46.s46_P d s a β γ N) = N * ∫ X, (pair (empirical X) u -
      pair (thermalMeasure d s a β) u) ^ 2 ∂(S46.s46_P d s a β γ N) := by
    simp_rw [e]; rw [integral_const_mul]
  rw [this] at hZ2
  rw [le_div_iff₀ hN0]
  linarith

theorem s99_Bq_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ {χ : Euc d → ℝ}, ContDiff ℝ 2 χ →
    ∀ {B2 : ℝ}, (∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) →
    Integrable (fun X : EucConfig d N => (Bq d s a β γ N χ X) ^ 2) (S46.s46_P d s a β γ N) ∧
    ∫ X, (Bq d s a β γ N χ X) ^ 2 ∂(S46.s46_P d s a β γ N) ≤ (K * B2) ^ 2 ∧
    Integrable (fun X : EucConfig d N => Bq d s a β γ N χ X) (S46.s46_P d s a β γ N) ∧
    ∫ X, |Bq d s a β γ N χ X| ∂(S46.s46_P d s a β γ N) ≤ K * B2 := by
  obtain ⟨C₁, hC₁, h1, -, -⟩ := s99_mom hd hs0 hs ha hβ hγ hT hS 1 le_rfl
  obtain ⟨C₂, hC₂, h2, -, -⟩ := s99_mom hd hs0 hs ha hβ hγ hT hS 2 (by norm_num)
  refine ⟨(s + 1) * max C₁ C₂, mul_nonneg (by linarith) (le_max_of_le_left hC₁), fun N hN χ hχ B2 hB2 => ?_⟩
  have hN1 : 1 ≤ N := by omega
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have hv1 : ContDiff ℝ 1 (gradient χ) := s45_contDiff_gradient hχ
  have hvd : Differentiable ℝ (gradient χ) := hv1.differentiable one_ne_zero
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  set Λ : ℝ≥0 := ⟨B2, hB20⟩ with hΛdef
  have hLip : LipschitzWith Λ (gradient χ) := lipschitzWith_of_nnnorm_fderiv_le hvd (fun x => by
    have := hB2 x
    rw [← NNReal.coe_le_coe, coe_nnnorm]; exact this)
  have hker := s99_comm_isBounded (d := d) hs0 Λ hLip
  have hB0 : 0 ≤ (s + 1) * (Λ : ℝ) := by
    have : (0 : ℝ) ≤ Λ := Λ.coe_nonneg
    have : 0 ≤ s + 1 := by linarith
    positivity
  have hBqm : Measurable (fun X : EucConfig d N => Bq d s a β γ N χ X) := by
    unfold Bq
    exact measurable_const.mul ((HRS.MS.Wr.wr9_measurable_pairEnergy (HRS.MS.Comm.comm_meas (s := s) (gradient χ)
      hv1.continuous.measurable)).sub measurable_const)
  have hm1 := (h1 N hN _ hB0 _ hker).2
  have hm2 := (h2 N hN _ hB0 _ hker).2
  have hBq1 : eLpNorm (fun X : EucConfig d N => Bq d s a β γ N χ X) 1 (S46.s46_P d s a β γ N) ≤
      ENNReal.ofReal (max C₁ C₂ * ((s + 1) * (Λ : ℝ))) := by
    have hm1' : eLpNorm (fun X : EucConfig d N => Bq d s a β γ N χ X) 1 (S46.s46_P d s a β γ N) ≤
        ENNReal.ofReal (C₁ * ((s + 1) * (Λ : ℝ))) := by
      simp only [ENNReal.ofReal_one] at hm1; exact hm1
    exact hm1'.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hB0))
  have hBq2 : eLpNorm (fun X : EucConfig d N => Bq d s a β γ N χ X) 2 (S46.s46_P d s a β γ N) ≤
      ENNReal.ofReal (max C₁ C₂ * ((s + 1) * (Λ : ℝ))) := by
    have : eLpNorm (fun X : EucConfig d N => Bq d s a β γ N χ X) (ENNReal.ofReal 2)
        (S46.s46_P d s a β γ N) ≤ ENNReal.ofReal (C₂ * ((s + 1) * (Λ : ℝ))) := hm2
    have h2' : eLpNorm (fun X : EucConfig d N => Bq d s a β γ N χ X) 2 (S46.s46_P d s a β γ N) ≤
        ENNReal.ofReal (C₂ * ((s + 1) * (Λ : ℝ))) := by
      have e2 : ENNReal.ofReal 2 = 2 := by simp
      rw [e2] at this; exact this
    exact h2'.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) hB0))
  have hKB : max C₁ C₂ * ((s + 1) * (Λ : ℝ)) = (s + 1) * max C₁ C₂ * B2 := by
    have hΛB : (Λ : ℝ) = B2 := rfl
    rw [hΛB]; ring
  have hKnn : 0 ≤ max C₁ C₂ * ((s + 1) * (Λ : ℝ)) := mul_nonneg (le_max_of_le_left hC₁) hB0
  obtain ⟨hmem2, hint2⟩ := s99_l2_bound hKnn hBqm.aestronglyMeasurable hBq2
  obtain ⟨hint1, hint1b⟩ := s99_l1_bound hKnn hBqm.aestronglyMeasurable hBq1
  rw [hKB] at hint2 hint1b
  exact ⟨hmem2.integrable_sq, hint2, hint1, hint1b⟩

end Mom

end S99

end
