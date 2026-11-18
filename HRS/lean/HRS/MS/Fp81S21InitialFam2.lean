import HRS.MS.Fp81S21InitialFam
import HRS.MS.R2SeAux2

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS (Euc MemCb cbNorm)
open HRS.Whole
open HRS.MS.R26T3

/-- The normalized response-gradient observable for the actual initial family correctors. -/
def InitialFamData.wF {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {φ : ℕ → Euc p.d → ℝ} (F : InitialFamData R φ) (j l : ℕ) (x : Euc p.d) : ℝ :=
  p.γ⁻¹ * ⟪gradient (F.χ j) x, gradient (φ l) x⟫

theorem fp81s21_initial_pair_wF
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ} {N : ℕ} (hN : 1 ≤ N)
    {φ : ℕ → Euc p.d → ℝ} (F : InitialFamData R φ) (j l : ℕ)
    (X : EucConfig p.d N) :
    HRS.Whole.pair (HRS.Whole.empirical X) (InitialFamData.wF F j l) =
      p.γ⁻¹ * HRS.Whole.pair (HRS.Whole.empirical X)
        (fun x => ⟪gradient (F.χ j) x, gradient (φ l) x⟫) := by
  have hNpos : 0 < N := by omega
  rw [HRS.Whole.pair_empirical hNpos, HRS.Whole.pair_empirical hNpos]
  unfold InitialFamData.wF
  rw [← Finset.mul_sum]
  ring

/-- The initial `wF` observables have the same high-order product bound as S9.9. -/
theorem fp81s21_initial_wF_cb
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : ∀ j, MemCb (fp81s21_J1 p.d) (φ j))
    (F : InitialFamData R φ) (hγ : 0 < p.γ) (j l : ℕ) :
    MemCb (fp81s21_k0 p.d) (InitialFamData.wF F j l) ∧
      cbNorm (fp81s21_k0 p.d) (InitialFamData.wF F j l) ≤
        ((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
          (p.γ⁻¹ * F.K * cbNorm (fp81s21_J1 p.d) (φ j)) *
            cbNorm (fp81s21_J1 p.d) (φ l) := by
  have hv : ContDiff ℝ (fp81s21_k0 p.d : WithTop ℕ∞)
      (fun y => p.γ⁻¹ • gradient (F.χ j) y) :=
    HRS.MS.S98.s98_gL_contDiff (F.smooth j) p.γ⁻¹
  have hBv : ∀ x, ∀ i ≤ fp81s21_k0 p.d,
      ‖iteratedFDeriv ℝ i (fun y => p.γ⁻¹ • gradient (F.χ j) y) x‖ ≤
        p.γ⁻¹ * F.K * cbNorm (fp81s21_J1 p.d) (φ j) := by
    intro x i hi
    refine (HRS.MS.S98.s98_gL_iter (F.smooth j) p.γ⁻¹ hi x).trans ?_
    rw [abs_of_nonneg (inv_nonneg.2 hγ.le), mul_assoc]
    exact mul_le_mul_of_nonneg_left (F.deriv j x i hi) (inv_nonneg.2 hγ.le)
  have hψ := HRS.MS.Tc5.tc5_cb_mono (fp81s21_J1_ge_k0 p.d) (hφ l)
  have hprod := S99.s99_inner_cb hv hBv hψ.1
  have he : InitialFamData.wF F j l =
      fun x => ⟪p.γ⁻¹ • gradient (F.χ j) x, gradient (φ l) x⟫ := by
    funext x
    unfold InitialFamData.wF
    rw [real_inner_smul_left]
  rw [he]
  refine ⟨hprod.1, hprod.2.trans ?_⟩
  have hB0 : 0 ≤ p.γ⁻¹ * F.K * cbNorm (fp81s21_J1 p.d) (φ j) := by
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hγ.le) F.hK)
      (HRS.MS.Tc5.tc5_cb_nonneg (fp81s21_J1 p.d) (φ j))
  have hconst : 0 ≤ ((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d *
      (p.γ⁻¹ * F.K * cbNorm (fp81s21_J1 p.d) (φ j)) := by positivity
  exact mul_le_mul_of_nonneg_left hψ.2 hconst

/-- Recover the S4.7 feature contract from the nonthermal S9.9 family record. -/
theorem InitialFamData.feat
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {φ : ℕ → Euc p.d → ℝ} (F : InitialFamData R φ)
    (hγ : 0 < p.γ) (j : ℕ) :
    S47.S47Feat p.d p.s (R.ρ 0) p.γ (φ j) (F.χ j)
      (F.K * cbNorm (fp81s21_J1 p.d) (φ j)) := by
  let μ := HRS.Whole.withDensityReal (R.ρ 0)
  let aφ := r26t3_a R (φ j)
  have hχ2 : ContDiff ℝ 2 (F.χ j) := (F.smooth j).of_le (by
    have hk := fp81s21_k0_ge_one p.d
    exact_mod_cast (show 2 ≤ fp81s21_k0 p.d + 1 by omega))
  refine ⟨hχ2, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [S45.s45_norm_gradient, ← norm_iteratedFDeriv_one]
    exact F.deriv j x 0 (Nat.zero_le _)
  · intro x
    exact (S45.s45_norm_fderiv_gradient hχ2 x).trans
      (F.deriv j x 1 (by have hk := fp81s21_k0_ge_one p.d; omega))
  · have hgenf : weightedGen (R.ρ 0) (F.χ j) = fun x => p.γ * aφ x :=
      funext (F.gen j)
    filter_upwards [(F.resp j).2] with x hx
    unfold HRS.Whole.susceptibilityOp
    rw [hgenf, HRS.MS.S98.s98_kop_smul (g := rieszKernel p.d p.s)
      (μ := μ) (c := p.γ) (f := aφ) (x := x)]
    calc p.γ⁻¹ * (p.γ * aφ x) + p.γ * HRS.Whole.Kop (rieszKernel p.d p.s) μ aφ x =
          aφ x + p.γ * HRS.Whole.Kop (rieszKernel p.d p.s) μ aφ x := by field_simp
      _ = HRS.Whole.projMean μ (φ j) x := hx
  · have hgenf : weightedGen (R.ρ 0) (F.χ j) = fun x => p.γ * aφ x :=
      funext (F.gen j)
    rw [hgenf]
    exact (F.resp j).1.1.const_mul p.γ

/-- S47 itself supplies one corrector bound for the entire input family, with the constant
chosen before the feature index. -/
theorem fp81s21_initial_s47_correctors_exists
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : 0 < p.γ)
    (φ : ℕ → Euc p.d → ℝ)
    (hφ : ∀ j, MemCb (fp81s21_J1 p.d) (φ j)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j, ∃ χ : Euc p.d → ℝ,
      S47.S47Feat p.d p.s (R.ρ 0) p.γ (φ j) χ
        (B * cbNorm (fp81s21_J1 p.d) (φ j)) := by
  have hsd : p.s < p.d := by
    have hd0 : (0 : ℝ) ≤ (p.d : ℝ) / 2 := by positivity
    linarith [p.hs]
  have hJ : (p.d : ℝ) / 2 + 2 < (fp81s21_J1 p.d : ℝ) := by
    unfold fp81s21_J1
    push_cast
    have hd0 : (0 : ℝ) ≤ (p.d : ℝ) := Nat.cast_nonneg p.d
    linarith
  have hU0 := s21f_unifref_init p hδ hδh R
  obtain ⟨B, hB, hcorr⟩ := S47.s47_corrector_unif p.hd p.hs0 hsd
    (fp81s21_J1 p.d) hJ p.a p.a p.β p.β p.γ p.γ p.ha p.hβ hγ δ
  refine ⟨B, hB, fun j => ?_⟩
  exact hcorr p.a ⟨le_rfl, le_rfl⟩ p.β ⟨le_rfl, le_rfl⟩ p.γ ⟨le_rfl, le_rfl⟩
    (R.ρ 0) hU0 (φ j) (hφ j)

/-- For each feature, the scaled S9.9 corrector gives an explicit root-compatible velocity
`γ⁻¹ ∇χ`. The root S03 theorem exports only an existential velocity; this theorem supplies
the matching witness and its divergence equation. The cosine observation family `r26t3_qwin`
is outside this packet: it has no `MemCb` or summability producer here. -/
theorem fp81s21_initial_rootVelocity
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    {R : Trajectory p δ} (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (F : InitialFamData R φ) (j : ℕ) :
    ∃ v : Euc p.d → Euc p.d,
      HasCbBound (fp81s21_k0 p.d)
        (p.γ⁻¹ * F.K * cbNorm (fp81s21_J1 p.d) (φ j)) v ∧
      (∀ x, -(movDiv (fun y => R.ρ 0 y • v y) x) =
        R.ρ 0 x * r26t3_a R (φ j) x) ∧
      v = fun y => p.γ⁻¹ • gradient (F.χ j) y := by
  let χphys : Euc p.d → ℝ := p.γ⁻¹ • F.χ j
  let v : Euc p.d → Euc p.d := gradient χphys
  have hχ1 : ContDiff ℝ 1 (F.χ j) := (F.smooth j).of_le (by
    have hk := fp81s21_k0_ge_one p.d
    exact_mod_cast (show 1 ≤ fp81s21_k0 p.d + 1 by omega))
  have hχ2 : ContDiff ℝ 2 (F.χ j) := (F.smooth j).of_le (by
    have hk := fp81s21_k0_ge_one p.d
    exact_mod_cast (show 2 ≤ fp81s21_k0 p.d + 1 by omega))
  have hχphys : ContDiff ℝ ((fp81s21_k0 p.d + 1 : ℕ) : WithTop ℕ∞) χphys := by
    have hs := (F.smooth j).const_smul p.γ⁻¹
    change ContDiff ℝ ((fp81s21_k0 p.d + 1 : ℕ) : WithTop ℕ∞)
      (fun y => p.γ⁻¹ • F.χ j y)
    exact hs
  have hχphys2 : ContDiff ℝ 2 χphys := hχphys.of_le (by
    have hk := fp81s21_k0_ge_one p.d
    exact_mod_cast (show 2 ≤ fp81s21_k0 p.d + 1 by omega))
  have hvEq : v = fun y => p.γ⁻¹ • gradient (F.χ j) y := by
    funext y
    have hdif : DifferentiableAt ℝ (F.χ j) y := (hχ1.differentiable (by norm_num)) y
    unfold v χphys gradient
    have hfd : fderiv ℝ (p.γ⁻¹ • F.χ j) y = p.γ⁻¹ • fderiv ℝ (F.χ j) y :=
      (hdif.hasFDerivAt.const_smul p.γ⁻¹).fderiv
    rw [hfd]
    simp only [map_smul]
  have hbound : HasCbBound (fp81s21_k0 p.d)
      (p.γ⁻¹ * F.K * cbNorm (fp81s21_J1 p.d) (φ j)) v := by
    refine ⟨?_, ?_⟩
    · have h := HRS.MS.S98.s98_gL_contDiff (F.smooth j) p.γ⁻¹
      simpa only [hvEq] using h
    · intro i hi x
      rw [hvEq]
      refine (HRS.MS.S98.s98_gL_iter (F.smooth j) p.γ⁻¹ hi x).trans ?_
      rw [abs_of_nonneg (inv_nonneg.2 hγ.le), mul_assoc]
      exact mul_le_mul_of_nonneg_left (F.deriv j x i hi) (inv_nonneg.2 hγ.le)
  have hphysgen : ∀ x, weightedGen (R.ρ 0) χphys x = r26t3_a R (φ j) x := by
    intro x
    rw [fp81s21_weightedGen_smul (R.ρ 0) (F.χ j) p.γ⁻¹ x hχ2,
      F.gen j x]
    field_simp
  obtain ⟨hρsmooth, hρpos⟩ := s21h2_s03_smooth hδ hδh R
  have hρ1 : ContDiff ℝ 1 (R.ρ 0) := hρsmooth.of_le (by norm_cast)
  have hgradρ : ∀ x, gradient (R.ρ 0) x = R.ρ 0 x •
      gradient (fun y => Real.log (R.ρ 0 y)) x := by
    intro x
    rw [s21f_gradient_log hρsmooth hρpos x, smul_smul]
    rw [mul_inv_cancel₀ (hρpos x).ne', one_smul]
  have hdiv : ∀ x, -(movDiv (fun y => R.ρ 0 y • v y) x) =
      R.ρ 0 x * r26t3_a R (φ j) x := by
    intro x
    have hmv := s21h2_s03_movDiv hρ1 hχphys2 x
    calc -(movDiv (fun y => R.ρ 0 y • v y) x) =
          -(inner ℝ (gradient (R.ρ 0) x) (gradient χphys x) +
            R.ρ 0 x * Laplacian.laplacian χphys x) := by
              rw [hmv]
      _ = R.ρ 0 x * (-Laplacian.laplacian χphys x -
            inner ℝ (gradient (fun y => Real.log (R.ρ 0 y)) x)
              (gradient χphys x)) := by
              rw [hgradρ x, real_inner_smul_left]
              ring
      _ = R.ρ 0 x * r26t3_a R (φ j) x := by
              rw [← hphysgen x]
              rfl
  exact ⟨v, hbound, hdiv, hvEq⟩

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_initial_pair_wF
#print axioms HRS.Fp81.S21.fp81s21_initial_wF_cb
#print axioms HRS.Fp81.S21.InitialFamData.feat
#print axioms HRS.Fp81.S21.fp81s21_initial_s47_correctors_exists
#print axioms HRS.Fp81.S21.fp81s21_initial_rootVelocity
