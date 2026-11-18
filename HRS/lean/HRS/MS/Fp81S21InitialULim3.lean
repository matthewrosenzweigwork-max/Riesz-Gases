import HRS.MS.Fp81S21InitialULim2
import HRS.MS.Fp81S21InitialCancel5
import HRS.MS.R2SeAux41

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45 S99
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-! The actual-law linear and quadratic limit coefficients combine by the
already established cubic cancellation identity.  This is the series-level
identification; it does not require the later third-derivative expansion of a
continuous trilinear form. -/

/-- The cubic coefficient at the actual initial law. -/
def fp81s21_initial_kap3 {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (φ : ℕ → Euc p.d → ℝ) (j k m : ℕ) : ℝ :=
  ∫ x, r26t3_a R (φ j) x * r26t3_a R (φ k) x * r26t3_a R (φ m) x
    ∂(r26t3_mu R 0)

/-- The actual-law cubic coefficients have the feature-product envelope. -/
theorem fp81s21_initial_kap3_bound
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) (j k m : ℕ) :
    |fp81s21_initial_kap3 R φ j k m| ≤
      F.K ^ 3 * (cbNorm (fp81s21_J1 p.d) (φ j) *
        cbNorm (fp81s21_J1 p.d) (φ k) *
        cbNorm (fp81s21_J1 p.d) (φ m)) := by
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  let b : ℕ → ℝ := fun i => cbNorm (fp81s21_J1 p.d) (φ i)
  have hb0 : ∀ i, 0 ≤ b i := fun i => by
    dsimp [b]
    exact HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hKi : ∀ i x, |r26t3_a R (φ i) x| ≤ F.K * b i := by
    intro i x
    have hs := HRS.MS.Tc5.tc5_cb_sup_le (F.amem i) x
    calc
      |r26t3_a R (φ i) x| ≤ cbNorm (fp81s21_k0 p.d) (r26t3_a R (φ i)) := by
        simpa [Real.norm_eq_abs] using hs
      _ ≤ F.K * b i := by simpa [b] using F.anorm i
  let g : Euc p.d → ℝ := fun x =>
    r26t3_a R (φ j) x * r26t3_a R (φ k) x * r26t3_a R (φ m) x
  have hgmeas : Measurable g := by
    exact ((((F.amem j).1.continuous.mul (F.amem k).1.continuous).mul
      (F.amem m).1.continuous)).measurable
  have hbound : ∀ x, ‖g x‖ ≤
      (F.K * b j) * (F.K * b k) * (F.K * b m) := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc
      |r26t3_a R (φ j) x| * |r26t3_a R (φ k) x| *
          |r26t3_a R (φ m) x| ≤
        (F.K * b j) * (F.K * b k) * (F.K * b m) := by
          exact mul_le_mul (mul_le_mul (hKi j x) (hKi k x)
            (abs_nonneg _) (mul_nonneg F.hK (hb0 j)))
            (hKi m x) (abs_nonneg _)
            (mul_nonneg (mul_nonneg F.hK (hb0 j))
              (mul_nonneg F.hK (hb0 k)))
      _ = _ := by ring
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := r26t3_mu R 0) (f := g)
    (C := (F.K * b j) * (F.K * b k) * (F.K * b m))
    (Filter.Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at hnorm
  calc
    |fp81s21_initial_kap3 R φ j k m| ≤
        (F.K * b j) * (F.K * b k) * (F.K * b m) := by
          simpa [g, fp81s21_initial_kap3] using hnorm
    _ = F.K ^ 3 * (b j * b k * b m) := by ring

/-- Actual `cc` coefficients for a fixed first feature have an absolutely
summable second and response index envelope. -/
theorem fp81s21_initialCancel_cc_bound
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (E : InitialSteinEnv R)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) (hγ : 0 < p.γ) (j k m : ℕ) :
    |fp81s21_initialCancel_cc R F j k m| ≤
      (((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
        (p.γ⁻¹ * F.K) *
        (cbNorm (fp81s21_J1 p.d) (φ j) *
          cbNorm (fp81s21_J1 p.d) (φ k))) *
        (F.K * cbNorm (fp81s21_J1 p.d) (φ m)) := by
  have b0 : ∀ i, 0 ≤ cbNorm (fp81s21_J1 p.d) (φ i) := fun i =>
    HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hW := fp81s21_initial_wF_cb hφ.1 F hγ j k
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  let w := InitialFamData.wF F j k
  let b : ℕ → ℝ := fun i => cbNorm (fp81s21_J1 p.d) (φ i)
  have hwabs : ∀ x, |w x| ≤ cbNorm (fp81s21_k0 p.d) w := by
    intro x
    have h := HRS.MS.Tc5.tc5_cb_sup_le hW.1 x
    simpa [Real.norm_eq_abs] using h
  have haabs : ∀ x, |r26t3_a R (φ m) x| ≤ F.K * b m := by
    intro x
    have hs := HRS.MS.Tc5.tc5_cb_sup_le (F.amem m) x
    calc
      |r26t3_a R (φ m) x| ≤ cbNorm (fp81s21_k0 p.d) (r26t3_a R (φ m)) := by
        simpa [Real.norm_eq_abs] using hs
      _ ≤ F.K * b m := by simpa [b] using F.anorm m
  have hK0 : 0 ≤ cbNorm (fp81s21_k0 p.d) w :=
    HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hAm0 : 0 ≤ F.K * b m := mul_nonneg F.hK (b0 m)
  have hWbd : cbNorm (fp81s21_k0 p.d) w ≤
      ((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
        (p.γ⁻¹ * F.K * b j) * b k := by
    simpa [b] using hW.2
  have hWbd' : cbNorm (fp81s21_k0 p.d) w ≤
      ((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
        (p.γ⁻¹ * F.K) * (b j * b k) := by
    calc
      _ ≤ ((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
          (p.γ⁻¹ * F.K * b j) * b k := hWbd
      _ = _ := by ring
  let g : Euc p.d → ℝ := fun x => w x * r26t3_a R (φ m) x
  have hgmeas : Measurable g :=
    (hW.1.1.continuous.mul (F.amem m).1.continuous).measurable
  have hgBound : ∀ x, ‖g x‖ ≤ cbNorm (fp81s21_k0 p.d) w * (F.K * b m) := by
    intro x
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hwabs x) (haabs x) (abs_nonneg _) hK0
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := r26t3_mu R 0) (f := g)
    (C := cbNorm (fp81s21_k0 p.d) w * (F.K * b m))
    (Filter.Eventually.of_forall hgBound)
  rw [Real.norm_eq_abs] at hnorm
  calc
    |fp81s21_initialCancel_cc R F j k m| ≤
        cbNorm (fp81s21_k0 p.d) w * (F.K * b m) := by
          simpa [g, w, fp81s21_initialCancel_cc] using hnorm
    _ ≤ (((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
        (p.γ⁻¹ * F.K) * (b j * b k)) * (F.K * b m) := by
          exact mul_le_mul_of_nonneg_right hWbd' hAm0
    _ = _ := by ring

/-- Absolute bound on an actual-law `Alim` coefficient, uniform over the
Stein class. -/
theorem fp81s21_initial_Alim_bound
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    {f : SeqL2 → ℝ} (hf : SteinCl f) (q : ℕ × ℕ) :
    |fp81s21_initial_Alim F G f q| ≤
      (((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
        (p.γ⁻¹ * F.K) * F.K *
        (∑' j, cbNorm (fp81s21_J1 p.d) (φ j))) *
        (cbNorm (fp81s21_J1 p.d) (φ q.1) *
          cbNorm (fp81s21_J1 p.d) (φ q.2)) := by
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hb0 : ∀ j, 0 ≤ b j := fun j => by
    dsimp [b]
    exact HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hFK0 : 0 ≤ F.K := F.hK
  have hbs : Summable b := hφ.2
  let Sb : ℝ := ∑' j, b j
  have hSb0 : 0 ≤ Sb := tsum_nonneg hb0
  let Kw : ℝ := ((fp81s21_k0 p.d : ℝ) + 1) *
    2 ^ fp81s21_k0 p.d * (p.γ⁻¹ * F.K)
  have hKw0 : 0 ≤ Kw := by
    have hdim : 0 ≤ (fp81s21_k0 p.d : ℝ) + 1 := by positivity
    have hpow : 0 ≤ (2 : ℝ) ^ fp81s21_k0 p.d := by positivity
    exact mul_nonneg (mul_nonneg hdim hpow)
      (mul_nonneg (inv_nonneg.2 hγ.le) F.hK)
  have hcc : ∀ m, |fp81s21_initial_kap (R := R)
      (InitialFamData.wF F q.1 q.2) φ m| ≤
      Kw * (b q.1 * b q.2) * (F.K * b m) := by
    intro m
    have h := fp81s21_initialCancel_cc_bound R E hφ F hγ q.1 q.2 m
    calc
      |fp81s21_initial_kap (R := R) (InitialFamData.wF F q.1 q.2) φ m| ≤
          (((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
            (p.γ⁻¹ * F.K) * (b q.1 * b q.2)) * (F.K * b m) := by
              simpa [fp81s21_initial_kap, fp81s21_initialCancel_cc, b] using h
      _ = Kw * (b q.1 * b q.2) * (F.K * b m) := by
        dsimp [Kw]
  have hGb : ∀ m, |∫ z, S99.pd (S99.pd (S99.pd f q.1) q.2) m z ∂G| ≤ 1 := by
    intro m
    have h := norm_integral_le_of_norm_le_const (μ := G)
      (f := S99.pd (S99.pd (S99.pd f q.1) q.2) m) (C := 1)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        exact (((hf.pd q.1).pd q.2).pd m).abs_le z)
    simpa [Real.norm_eq_abs] using h
  unfold fp81s21_initial_Alim
  rw [abs_neg]
  have hg : HasSum (fun m => Kw * (b q.1 * b q.2) * F.K * b m)
      (Kw * (b q.1 * b q.2) * F.K * Sb) := hbs.hasSum.mul_left _
  have hsum := tsum_of_norm_bounded hg
    (f := fun m => fp81s21_initial_kap (R := R)
      (InitialFamData.wF F q.1 q.2) φ m *
        ∫ z, S99.pd (S99.pd (S99.pd f q.1) q.2) m z ∂G)
    (fun m => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc
        |fp81s21_initial_kap (R := R)
            (InitialFamData.wF F q.1 q.2) φ m| *
            |∫ z, S99.pd (S99.pd (S99.pd f q.1) q.2) m z ∂G| ≤
          (Kw * (b q.1 * b q.2) * (F.K * b m)) * 1 :=
            mul_le_mul (hcc m) (hGb m) (abs_nonneg _)
            (mul_nonneg (mul_nonneg hKw0 (mul_nonneg (hb0 q.1) (hb0 q.2)))
              (mul_nonneg hFK0 (hb0 m)))
        _ = _ := by ring)
  rw [Real.norm_eq_abs] at hsum
  calc
    |∑' m, fp81s21_initial_kap (R := R)
        (InitialFamData.wF F q.1 q.2) φ m *
          ∫ z, S99.pd (S99.pd (S99.pd f q.1) q.2) m z ∂G| ≤
        Kw * (b q.1 * b q.2) * F.K * Sb := hsum
    _ = Kw * F.K * Sb * (b q.1 * b q.2) := by ring
    _ = (((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
        (p.γ⁻¹ * F.K) * F.K * Sb) * (b q.1 * b q.2) := by
          dsimp [Kw]
    _ = _ := by dsimp [Sb, b]

/-- For each leading feature, the actual-law linear and quadratic limits
combine into the negative half of the cubic coefficient series. -/
theorem fp81s21_initial_jident
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    {f : SeqL2 → ℝ} (hf : SteinCl f) (j : ℕ) :
    (∑' k, fp81s21_initial_Alim F G f (j, k)) +
        (1 / 2) * ∑' l, ∑' q,
          fp81s21_initial_Qk R φ
            (commutatorKernel p.d p.s (gradient (F.χ j))) l q *
            S99.T3 G f j l q =
      -(1 / 2) * ∑' k, ∑' m,
        fp81s21_initial_kap3 R φ j k m * S99.T3 G f j k m := by
  let b : ℕ → ℝ := fun i => cbNorm (fp81s21_J1 p.d) (φ i)
  have hb0 : ∀ i, 0 ≤ b i := fun i => by
    dsimp [b]
    exact HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  have hbb : Summable (fun q : ℕ × ℕ => b q.1 * b q.2) :=
    Summable.mul_of_nonneg hbs hbs (fun i => hb0 i) (fun i => hb0 i)
  have hFK0 : 0 ≤ F.K := F.hK
  let Kw : ℝ := ((fp81s21_k0 p.d : ℝ) + 1) *
    2 ^ fp81s21_k0 p.d * (p.γ⁻¹ * F.K)
  have hKw0 : 0 ≤ Kw := by
    have hdim : 0 ≤ (fp81s21_k0 p.d : ℝ) + 1 := by positivity
    have hpow : 0 ≤ (2 : ℝ) ^ fp81s21_k0 p.d := by positivity
    exact mul_nonneg (mul_nonneg hdim hpow)
      (mul_nonneg (inv_nonneg.2 hγ.le) F.hK)
  let Ij : ℝ := ∫ z : Euc p.d × Euc p.d,
    |commutatorKernel p.d p.s (gradient (F.χ j)) z.1 z.2|
      ∂((r26t3_mu R 0).prod (r26t3_mu R 0))
  have hIj0 : 0 ≤ Ij := integral_nonneg fun z => abs_nonneg _
  have hχ2 : ContDiff ℝ 2 (F.χ j) := (F.smooth j).of_le (by
    exact_mod_cast (show 2 ≤ fp81s21_k0 p.d + 1 by
      unfold fp81s21_k0
      omega))
  have hB2 : ∀ x, ‖fderiv ℝ (gradient (F.χ j)) x‖ ≤ F.K * b j := by
    intro x
    exact (S45.s45_norm_fderiv_gradient hχ2 x).trans (F.deriv j x 1 (by
      unfold fp81s21_k0
      omega))
  have hB20 : 0 ≤ F.K * b j := mul_nonneg hFK0 (hb0 j)
  have hv1 : ContDiff ℝ 1 (gradient (F.χ j)) := s45_contDiff_gradient hχ2
  have hvd : Differentiable ℝ (gradient (F.χ j)) :=
    hv1.differentiable one_ne_zero
  let Λ : ℝ≥0 := ⟨F.K * b j, hB20⟩
  have hLip : LipschitzWith Λ (gradient (F.χ j)) :=
    lipschitzWith_of_nnnorm_fderiv_le hvd (fun x => by
      have hx := hB2 x
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hx)
  have hkernel : IsBoundedPairKernel p.s ((p.s + 1) * (F.K * b j))
      (commutatorKernel p.d p.s (gradient (F.χ j))) := by
    have hk := S99.s99_comm_isBounded (d := p.d) p.hs0 Λ hLip
    change IsBoundedPairKernel p.s ((p.s + 1) * (Λ : ℝ)) _ at hk
    rw [show (Λ : ℝ) = F.K * b j from rfl] at hk
    exact hk
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have hwr := fp81s21_initial_kernel_wr8 hδ hδh R hkernel
  have hzero : Integrable (Function.uncurry fun (_ _ : Euc p.d) => (0 : ℝ))
      ((r26t3_mu R 0).prod (r26t3_mu R 0)) := integrable_const (0 : ℝ)
  have hQ0 : ∀ l q, fp81s21_initial_Qk R φ (fun _ _ => (0 : ℝ)) l q = 0 := by
    intro l q
    unfold fp81s21_initial_Qk
    simp
  let A : ℕ × ℕ → ℝ := fun q =>
    fp81s21_initialCancel_cc R F j q.1 q.2 * S99.T3 G f j q.1 q.2
  let Q : ℕ × ℕ → ℝ := fun q =>
    fp81s21_initial_Qk R φ
      (commutatorKernel p.d p.s (gradient (F.χ j))) q.1 q.2 *
        S99.T3 G f j q.1 q.2
  let Kc : ℕ × ℕ → ℝ := fun q =>
    fp81s21_initial_kap3 R φ j q.1 q.2 * S99.T3 G f j q.1 q.2
  have hAs : Summable A := by
    refine Summable.of_norm_bounded
      (hbb.mul_left (Kw * F.K * b j)) (fun q => ?_)
    change |fp81s21_initialCancel_cc R F j q.1 q.2 *
      S99.T3 G f j q.1 q.2| ≤ (Kw * F.K * b j) * (b q.1 * b q.2)
    rw [abs_mul]
    have hcc := fp81s21_initialCancel_cc_bound R E hφ F hγ j q.1 q.2
    have hT := S99.T3_abs_le G hf j q.1 q.2
    calc
      |fp81s21_initialCancel_cc R F j q.1 q.2| *
          |S99.T3 G f j q.1 q.2| ≤
        (Kw * (b j * b q.1) * (F.K * b q.2)) * 1 := by
          apply mul_le_mul hcc hT (abs_nonneg _) ?_
          exact mul_nonneg (mul_nonneg hKw0 (mul_nonneg (hb0 j) (hb0 q.1)))
            (mul_nonneg hFK0 (hb0 q.2))
      _ = (Kw * F.K * b j) * (b q.1 * b q.2) := by ring
  have hAsw : Summable (fun q : ℕ × ℕ => A (q.2, q.1)) :=
    (Equiv.summable_iff (Equiv.prodComm ℕ ℕ)).2 hAs
  have hQs : Summable Q := by
    have hQbd : ∀ l q,
        |fp81s21_initial_Qk R φ
            (commutatorKernel p.d p.s (gradient (F.χ j))) l q| ≤
          F.K ^ 2 * Ij * (b l * b q) := by
      intro l q
      have h := fp81s21_initial_Qk_diff E hφ F hwr.prod hzero l q
      rw [hQ0 l q, sub_zero] at h
      calc
        |fp81s21_initial_Qk R φ
            (commutatorKernel p.d p.s (gradient (F.χ j))) l q| ≤
            F.K * b l * (F.K * b q) * Ij := by simpa [Ij, b] using h
        _ = F.K ^ 2 * Ij * (b l * b q) := by ring
    refine Summable.of_norm_bounded (hbb.mul_left (F.K ^ 2 * Ij))
      (fun q => ?_)
    change |fp81s21_initial_Qk R φ
        (commutatorKernel p.d p.s (gradient (F.χ j))) q.1 q.2 *
      S99.T3 G f j q.1 q.2| ≤ F.K ^ 2 * Ij * (b q.1 * b q.2)
    rw [abs_mul]
    have hQ := hQbd q.1 q.2
    have hT := S99.T3_abs_le G hf j q.1 q.2
    calc
      |fp81s21_initial_Qk R φ
          (commutatorKernel p.d p.s (gradient (F.χ j))) q.1 q.2| *
          |S99.T3 G f j q.1 q.2| ≤
        (F.K ^ 2 * Ij * (b q.1 * b q.2)) * 1 := by
          apply mul_le_mul hQ hT (abs_nonneg _) ?_
          exact mul_nonneg (mul_nonneg (sq_nonneg F.K) hIj0)
            (mul_nonneg (hb0 q.1) (hb0 q.2))
      _ = F.K ^ 2 * Ij * (b q.1 * b q.2) := by ring
  have hKs : Summable Kc := by
    refine Summable.of_norm_bounded
      (hbb.mul_left (F.K ^ 3 * b j)) (fun q => ?_)
    change |fp81s21_initial_kap3 R φ j q.1 q.2 *
      S99.T3 G f j q.1 q.2| ≤ (F.K ^ 3 * b j) * (b q.1 * b q.2)
    rw [abs_mul]
    have hK := fp81s21_initial_kap3_bound E hφ F j q.1 q.2
    have hT := S99.T3_abs_le G hf j q.1 q.2
    calc
      |fp81s21_initial_kap3 R φ j q.1 q.2| *
          |S99.T3 G f j q.1 q.2| ≤
        (F.K ^ 3 * (b j * b q.1 * b q.2)) * 1 := by
          apply mul_le_mul hK hT (abs_nonneg _) ?_
          have hprod : 0 ≤ cbNorm (fp81s21_J1 p.d) (φ j) *
              cbNorm (fp81s21_J1 p.d) (φ q.1) *
              cbNorm (fp81s21_J1 p.d) (φ q.2) :=
            mul_nonneg
              (mul_nonneg (HRS.MS.Tc5.tc5_cb_nonneg _ _)
                (HRS.MS.Tc5.tc5_cb_nonneg _ _))
              (HRS.MS.Tc5.tc5_cb_nonneg _ _)
          change 0 ≤ (F.K ^ 2 * F.K) *
            (cbNorm (fp81s21_J1 p.d) (φ j) *
              cbNorm (fp81s21_J1 p.d) (φ q.1) *
              cbNorm (fp81s21_J1 p.d) (φ q.2))
          exact mul_nonneg (mul_nonneg (sq_nonneg F.K) F.hK) hprod
      _ = F.K ^ 3 * b j * (b q.1 * b q.2) := by ring
  have hpt : ∀ q : ℕ × ℕ,
      Kc q = A q + A (q.2, q.1) - Q q := by
    intro q
    obtain ⟨k, m⟩ := q
    have hc := fp81s21_initialCancel_cancel hδ hδh R E hγ hφ F j k m
    have hcc1 : fp81s21_initialCancel_cc R F j k m =
        fp81s21_initial_kap (R := R) (InitialFamData.wF F j k) φ m := rfl
    have hcc2 : fp81s21_initialCancel_cc R F j m k =
        fp81s21_initial_kap (R := R) (InitialFamData.wF F j m) φ k := rfl
    have hcoef : fp81s21_initial_kap3 R φ j k m =
        fp81s21_initial_kap (R := R) (InitialFamData.wF F j k) φ m +
          fp81s21_initial_kap (R := R) (InitialFamData.wF F j m) φ k -
            fp81s21_initial_Qk R φ
              (commutatorKernel p.d p.s (gradient (F.χ j))) k m := by
      simpa [fp81s21_initial_kap3, fp81s21_initial_kap,
        fp81s21_initialCancel_cc, fp81s21_initialCancel_Qk,
        fp81s21_initial_Qk] using hc.symm
    change fp81s21_initial_kap3 R φ j k m * S99.T3 G f j k m =
      fp81s21_initialCancel_cc R F j k m * S99.T3 G f j k m +
        fp81s21_initialCancel_cc R F j m k * S99.T3 G f j m k -
          fp81s21_initial_Qk R φ
            (commutatorKernel p.d p.s (gradient (F.χ j))) k m *
              S99.T3 G f j k m
    rw [hcc1, hcc2, hcoef, S99.T3_symm G hf j m k]
    ring
  have hswap : ∑' q : ℕ × ℕ, A (q.2, q.1) = ∑' q, A q :=
    (Equiv.prodComm ℕ ℕ).tsum_eq A
  have hKsum : ∑' q, Kc q = 2 * ∑' q, A q - ∑' q, Q q := by
    have hfun : (fun q : ℕ × ℕ => Kc q) = fun q => A q + A (q.2, q.1) - Q q :=
      funext hpt
    rw [hfun, (hAs.add hAsw).tsum_sub hQs, hAs.tsum_add hAsw, hswap]
    ring
  have e1 : ∑' k, fp81s21_initial_Alim F G f (j, k) = -∑' q, A q := by
    rw [hAs.tsum_prod, ← tsum_neg]
    refine tsum_congr fun k => ?_
    unfold fp81s21_initial_Alim
    congr 1
  have e2 : ∑' l, ∑' q,
      fp81s21_initial_Qk R φ
        (commutatorKernel p.d p.s (gradient (F.χ j))) l q *
          S99.T3 G f j l q = ∑' q, Q q := by
    rw [hQs.tsum_prod]
  have e3 : ∑' k, ∑' m,
      fp81s21_initial_kap3 R φ j k m * S99.T3 G f j k m = ∑' q, Kc q := by
    rw [hKs.tsum_prod]
  rw [e1, e2, e3, hKsum]
  ring

/-- Identification of the sum of the actual-law linear and quadratic limits
with the cubic coefficient series. -/
theorem fp81s21_initial_limit_ident
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    {f : SeqL2 → ℝ} (hf : SteinCl f) :
    (∑' q : ℕ × ℕ, fp81s21_initial_Alim F G f q) +
        (∑' j, (1 / 2) * ∑' l, ∑' q,
          fp81s21_initial_Qk R φ
            (commutatorKernel p.d p.s (gradient (F.χ j))) l q *
            S99.T3 G f j l q) =
      -(1 / 2) * ∑' j, ∑' k, ∑' m,
        fp81s21_initial_kap3 R φ j k m * S99.T3 G f j k m := by
  let b : ℕ → ℝ := fun i => cbNorm (fp81s21_J1 p.d) (φ i)
  have hb0 : ∀ i, 0 ≤ b i := fun i => by
    dsimp [b]
    exact HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  have hbb : Summable (fun q : ℕ × ℕ => b q.1 * b q.2) :=
    Summable.mul_of_nonneg hbs hbs (fun i => hb0 i) (fun i => hb0 i)
  have hAs : Summable (fun q : ℕ × ℕ => fp81s21_initial_Alim F G f q) := by
    refine Summable.of_norm_bounded
      (hbb.mul_left (((fp81s21_k0 p.d : ℝ) + 1) *
        2 ^ fp81s21_k0 p.d * (p.γ⁻¹ * F.K) * F.K * ∑' i, b i))
      (fun q => ?_)
    rw [Real.norm_eq_abs]
    have h := fp81s21_initial_Alim_bound E hγ hφ F (G := G) hf q
    simpa [b, mul_assoc] using h
  have hSA : Summable (fun j => ∑' k, fp81s21_initial_Alim F G f (j, k)) :=
    hAs.prod
  have hU : Summable (fun j => ∑' k, ∑' m,
      fp81s21_initial_kap3 R φ j k m * S99.T3 G f j k m) := by
    let Sb : ℝ := ∑' i, b i
    have hSb0 : 0 ≤ Sb := tsum_nonneg hb0
    have hUinner : ∀ j k,
        |∑' m, fp81s21_initial_kap3 R φ j k m * S99.T3 G f j k m| ≤
          F.K ^ 3 * b j * b k * Sb := by
      intro j k
      have hg : HasSum (fun m => F.K ^ 3 * b j * b k * b m)
          (F.K ^ 3 * b j * b k * Sb) := hbs.hasSum.mul_left _
      have hh := tsum_of_norm_bounded hg
        (f := fun m => fp81s21_initial_kap3 R φ j k m * S99.T3 G f j k m)
        (fun m => by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          have hK := fp81s21_initial_kap3_bound E hφ F j k m
          have hT := S99.T3_abs_le G hf j k m
          calc
            |fp81s21_initial_kap3 R φ j k m| *
                |S99.T3 G f j k m| ≤
              (F.K ^ 3 * (b j * b k * b m)) * 1 := by
                apply mul_le_mul hK hT (abs_nonneg _) ?_
                have hprod : 0 ≤ cbNorm (fp81s21_J1 p.d) (φ j) *
                    cbNorm (fp81s21_J1 p.d) (φ k) *
                    cbNorm (fp81s21_J1 p.d) (φ m) :=
                  mul_nonneg
                    (mul_nonneg (HRS.MS.Tc5.tc5_cb_nonneg _ _)
                      (HRS.MS.Tc5.tc5_cb_nonneg _ _))
                    (HRS.MS.Tc5.tc5_cb_nonneg _ _)
                change 0 ≤ (F.K ^ 2 * F.K) *
                  (cbNorm (fp81s21_J1 p.d) (φ j) *
                    cbNorm (fp81s21_J1 p.d) (φ k) *
                    cbNorm (fp81s21_J1 p.d) (φ m))
                exact mul_nonneg (mul_nonneg (sq_nonneg F.K) F.hK) hprod
            _ = F.K ^ 3 * b j * b k * b m := by ring)
      simpa [Real.norm_eq_abs, Sb] using hh
    refine Summable.of_norm_bounded
      (hbs.mul_left (F.K ^ 3 * (∑' i, b i) ^ 2))
      (fun j => ?_)
    rw [Real.norm_eq_abs]
    have hg : HasSum (fun k => F.K ^ 3 * b j * Sb * b k)
        (F.K ^ 3 * b j * Sb * Sb) := hbs.hasSum.mul_left _
    have hh := tsum_of_norm_bounded hg
      (f := fun k => ∑' m,
        fp81s21_initial_kap3 R φ j k m * S99.T3 G f j k m)
      (fun k => by
        have h := hUinner j k
        simpa [Real.norm_eq_abs, mul_assoc] using h.trans (le_of_eq (by ring)))
    calc
      |∑' k, ∑' m, fp81s21_initial_kap3 R φ j k m * S99.T3 G f j k m| ≤
          (F.K ^ 3 * b j * Sb) * Sb := by
            simpa [Real.norm_eq_abs, Sb] using hh
      _ = F.K ^ 3 * Sb ^ 2 * b j := by ring
  have hid : ∀ j,
      (∑' k, fp81s21_initial_Alim F G f (j, k)) +
          (1 / 2) * ∑' l, ∑' q,
            fp81s21_initial_Qk R φ
              (commutatorKernel p.d p.s (gradient (F.χ j))) l q *
              S99.T3 G f j l q =
        -(1 / 2) * ∑' k, ∑' m,
          fp81s21_initial_kap3 R φ j k m * S99.T3 G f j k m :=
    fun j => fp81s21_initial_jident hδ hδh R E hγ hφ F hf j
  have hB : ∀ j,
      (1 / 2) * ∑' l, ∑' q,
          fp81s21_initial_Qk R φ
            (commutatorKernel p.d p.s (gradient (F.χ j))) l q *
            S99.T3 G f j l q =
        -(1 / 2) * (∑' k, ∑' m,
          fp81s21_initial_kap3 R φ j k m * S99.T3 G f j k m) -
          ∑' k, fp81s21_initial_Alim F G f (j, k) := by
    intro j
    have h := hid j
    linarith
  have hSB : Summable (fun j => (1 / 2) * ∑' l, ∑' q,
      fp81s21_initial_Qk R φ
        (commutatorKernel p.d p.s (gradient (F.χ j))) l q *
        S99.T3 G f j l q) := by
    have hfun : (fun j => (1 / 2) * ∑' l, ∑' q,
        fp81s21_initial_Qk R φ
          (commutatorKernel p.d p.s (gradient (F.χ j))) l q *
          S99.T3 G f j l q) =
      fun j => -(1 / 2) * (∑' k, ∑' m,
        fp81s21_initial_kap3 R φ j k m * S99.T3 G f j k m) -
        ∑' k, fp81s21_initial_Alim F G f (j, k) := funext hB
    rw [hfun]
    exact (hU.mul_left _).sub hSA
  rw [hAs.tsum_prod, ← hSA.tsum_add hSB]
  simp_rw [hid]
  rw [tsum_mul_left]

#print axioms fp81s21_initial_kap3_bound
#print axioms fp81s21_initialCancel_cc_bound
#print axioms fp81s21_initial_Alim_bound
#print axioms fp81s21_initial_jident
#print axioms fp81s21_initial_limit_ident

end HRS.Fp81.S21

end
