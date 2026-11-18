import HRS.MS.Fp81S21InitialStein
import HRS.MS.S21H2_S03
import HRS.MS.R2SeAux10

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

/-- The feature and corrector orders inherited from S9.9. -/
def fp81s21_J1 (d : ℕ) : ℕ := 4 * d + 40

def fp81s21_k0 (d : ℕ) : ℕ := 2 * d + 10

theorem fp81s21_k0_ge_one (d : ℕ) : 1 ≤ fp81s21_k0 d := by
  unfold fp81s21_k0
  omega

theorem fp81s21_J1_ge_k0 (d : ℕ) : fp81s21_k0 d + 1 ≤ fp81s21_J1 d := by
  unfold fp81s21_k0 fp81s21_J1
  omega

theorem fp81s21_k0_lt_J1 (d : ℕ) :
    ((fp81s21_k0 d : ℕ) : ℝ) + 1 + (d : ℝ) / 2 < (fp81s21_J1 d : ℝ) := by
  unfold fp81s21_k0 fp81s21_J1
  push_cast
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  linarith

/-- Nonthermal S9.9 family data at the actual initial density `R.ρ 0`.

The corrector is in the S9.9 normalization: `weightedGen ρ χ = γ aφ`. -/
structure InitialFamData {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (φ : ℕ → Euc p.d → ℝ) where
  K : ℝ
  hK : 0 ≤ K
  χ : ℕ → Euc p.d → ℝ
  smooth : ∀ j, ContDiff ℝ ((fp81s21_k0 p.d + 1 : ℕ) : WithTop ℕ∞) (χ j)
  deriv : ∀ j x, ∀ i ≤ fp81s21_k0 p.d,
    ‖iteratedFDeriv ℝ (i + 1) (χ j) x‖ ≤ K * cbNorm (fp81s21_J1 p.d) (φ j)
  gen : ∀ j x,
    weightedGen (R.ρ 0) (χ j) x = p.γ * r26t3_a R (φ j) x
  resp : ∀ j,
    HRS.Whole.IsResponse (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ (φ j) (r26t3_a R (φ j))
  amem : ∀ j, MemCb (fp81s21_k0 p.d) (r26t3_a R (φ j))
  anorm : ∀ j,
    cbNorm (fp81s21_k0 p.d) (r26t3_a R (φ j)) ≤ K * cbNorm (fp81s21_J1 p.d) (φ j)

/-- The scalar Poisson witness used by the root S03 transport construction, with its
high-order derivatives exposed. The response representative is the actual initial one. -/
theorem fp81s21_initial_scalar_corrector_exists
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Euc p.d → ℝ, MemCb (r26t3_J p.d) q →
      ∃ χ : Euc p.d → ℝ,
        ContDiff ℝ ((r26t3_k p.d + 1 : ℕ) : WithTop ℕ∞) χ ∧
        (∀ x, ∀ j ≤ r26t3_k p.d,
          ‖iteratedFDeriv ℝ (j + 1) χ x‖ ≤ C * cbNorm (r26t3_J p.d) q) ∧
        (∀ x, weightedGen (R.ρ 0) χ x = r26t3_a R q x) := by
  have hkd : r26t3_k p.d = 2 * p.d + 10 := rfl
  have hd1 : 1 ≤ p.d := by have := p.hd; omega
  have hm2 : 2 ≤ r26t3_k p.d + 1 := by rw [hkd]; omega
  obtain ⟨hsm, hpos⟩ := s21h2_s03_smooth hδ hδh R
  obtain ⟨B, Mb, m₂, hB, hgrad, hinv, hint, hmom⟩ :=
    r26t3_initial_drift hδ hδh R (r26t3_k p.d + 1)
  obtain ⟨Cm, hCm⟩ := HRS.MS.PoisFinal.affine_poisson_deriv_proof (d := p.d) hd1
    (p.β * p.a) Mb m₂ (mul_pos p.hβ p.ha) (r26t3_k p.d + 1) hm2
  obtain ⟨C₂, hC₂0, hR⟩ := r26t3_response_smooth hδ hδh R hγ
  refine ⟨|Cm| * C₂, mul_nonneg (abs_nonneg _) hC₂0, fun q hq => ?_⟩
  obtain ⟨hRa, hRc, hRL, -⟩ := hR q hq
  have hD0 : 0 ≤ C₂ * cbNorm (r26t3_J p.d) q :=
    mul_nonneg hC₂0 (s21h2_s03_cbNorm_nonneg _)
  have hbd : ∀ j, 1 ≤ j → j ≤ r26t3_k p.d + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (r26t3_a R q) x‖ ≤ C₂ * cbNorm (r26t3_J p.d) q := fun j _ hj x =>
    (s21h2_s03_iter_le hRa (by omega) x).trans hRc
  have hr : ContDiff ℝ ((r26t3_k p.d + 1 : ℕ) : WithTop ℕ∞) (r26t3_a R q) :=
    hRa.1.of_le (by norm_cast; omega)
  obtain ⟨χ, hχC, -, -, hχP, hχD⟩ :=
    hCm B hB (r26t3_mu R 0) hinv hint hmom (r26t3_a R q) hr _ hbd hRL.2
  refine ⟨χ, hχC, ?_, fun x => ?_⟩
  · intro x j hj
    have h := hχD (j + 1) (by omega) (by omega) x
    calc ‖iteratedFDeriv ℝ (j + 1) χ x‖ ≤ Cm * (C₂ * cbNorm (r26t3_J p.d) q) := h
      _ ≤ |Cm| * (C₂ * cbNorm (r26t3_J p.d) q) :=
        mul_le_mul_of_nonneg_right (le_abs_self Cm) hD0
      _ = |Cm| * C₂ * cbNorm (r26t3_J p.d) q := by ring
  · have hP := hχP x
    simp only [poissonOp] at hP
    unfold weightedGen
    rw [hgrad x]
    have he : inner ℝ (-(p.β * p.a) • x + B x) (gradient χ x) =
        -inner ℝ ((p.β * p.a) • x - B x) (gradient χ x) := by
      simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
      ring
    rw [he]
    nlinarith

/-- Scaling the physical S03 Poisson corrector by `γ` gives the S9.9 normalization. -/
theorem fp81s21_weightedGen_smul {d : ℕ} (ρ χ : Euc d → ℝ) (c : ℝ) (x : Euc d)
    (hχ : ContDiff ℝ 2 χ) :
    weightedGen ρ (c • χ) x = c * weightedGen ρ χ x := by
  have hχd : DifferentiableAt ℝ χ x := (hχ.differentiable (by norm_num)) x
  have hgrad : gradient (c • χ) x = c • gradient χ x := by
    unfold gradient
    have hfd : fderiv ℝ (c • χ) x = c • fderiv ℝ χ x := by
      exact (hχd.hasFDerivAt.const_smul c).fderiv
    rw [hfd]
    simp only [map_smul]
  have hlap : Laplacian.laplacian (c • χ) x = c * Laplacian.laplacian χ x := by
    rw [InnerProductSpace.laplacian_smul c (hχ.contDiffAt (x := x))]
    rfl
  unfold weightedGen
  rw [hlap, hgrad, inner_smul_right]
  ring

/-- The nonthermal high-order family corrector at the actual preparation density. The uniform
constant is selected before the feature index. -/
theorem fp81s21_initialFamData_exists
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : 0 < p.γ)
    (φ : ℕ → Euc p.d → ℝ)
    (hφ : ∀ j, MemCb (fp81s21_J1 p.d) (φ j)) :
    Nonempty (InitialFamData R φ) := by
  have hkd : r26t3_k p.d = fp81s21_k0 p.d := by
    simp [r26t3_k, fp81s21_k0]
  have hJd : r26t3_J p.d = fp81s21_J1 p.d := by
    simp [r26t3_J, fp81s21_J1]
  obtain ⟨Cc, hCc0, hCc⟩ :=
    fp81s21_initial_scalar_corrector_exists hδ hδh R hγ
  obtain ⟨Ca, hCa0, hCa⟩ := r26t3_response_smooth hδ hδh R hγ
  have hK0 : 0 ≤ max (p.γ * Cc) Ca :=
    le_max_of_le_right hCa0
  let K : ℝ := max (p.γ * Cc) Ca
  have hK : 0 ≤ K := hK0
  have hq : ∀ j, MemCb (r26t3_J p.d) (φ j) := by
    intro j
    simpa only [hJd] using hφ j
  have hex : ∀ j : ℕ, ∃ χj : Euc p.d → ℝ,
      ContDiff ℝ ((fp81s21_k0 p.d + 1 : ℕ) : WithTop ℕ∞) χj ∧
      (∀ x, ∀ i ≤ fp81s21_k0 p.d,
        ‖iteratedFDeriv ℝ (i + 1) χj x‖ ≤ K * cbNorm (fp81s21_J1 p.d) (φ j)) ∧
      (∀ x, weightedGen (R.ρ 0) χj x = p.γ * r26t3_a R (φ j) x) := by
    intro j
    obtain ⟨χ₀, hχ₀smooth, hχ₀deriv, hχ₀gen⟩ := hCc (φ j) (hq j)
    let χj : Euc p.d → ℝ := p.γ • χ₀
    have hχjsmooth : ContDiff ℝ ((fp81s21_k0 p.d + 1 : ℕ) : WithTop ℕ∞) χj := by
      have hs := hχ₀smooth.const_smul p.γ
      rw [hkd] at hs
      change ContDiff ℝ ((fp81s21_k0 p.d + 1 : ℕ) : WithTop ℕ∞)
        (fun x => p.γ • χ₀ x)
      exact hs
    have hχjderiv : ∀ x, ∀ i ≤ fp81s21_k0 p.d,
        ‖iteratedFDeriv ℝ (i + 1) χj x‖ ≤ K * cbNorm (fp81s21_J1 p.d) (φ j) := by
      intro x i hi
      have hreg : ContDiffAt ℝ ((i + 1 : ℕ) : WithTop ℕ∞) χ₀ x :=
        (hχ₀smooth.of_le (by norm_cast; omega)).contDiffAt
      have hiter := iteratedFDeriv_const_smul_apply'
        (𝕜 := ℝ) (a := p.γ) (f := χ₀) (i := i + 1) (x := x) hreg
      have he : iteratedFDeriv ℝ (i + 1) χj x =
          p.γ • iteratedFDeriv ℝ (i + 1) χ₀ x := by
        change iteratedFDeriv ℝ (i + 1) (p.γ • χ₀) x = _
        exact hiter
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
      have hbase := hχ₀deriv x i hi
      have hmul : p.γ * (Cc * cbNorm (r26t3_J p.d) (φ j)) ≤
          K * cbNorm (fp81s21_J1 p.d) (φ j) := by
        rw [hJd]
        have hb := HRS.MS.Tc5.tc5_cb_nonneg (fp81s21_J1 p.d) (φ j)
        calc p.γ * (Cc * cbNorm (fp81s21_J1 p.d) (φ j)) =
              (p.γ * Cc) * cbNorm (fp81s21_J1 p.d) (φ j) := by ring
          _ ≤ K * cbNorm (fp81s21_J1 p.d) (φ j) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hb
      calc p.γ * ‖iteratedFDeriv ℝ (i + 1) χ₀ x‖ ≤
            p.γ * (Cc * cbNorm (r26t3_J p.d) (φ j)) := mul_le_mul_of_nonneg_left hbase hγ.le
        _ ≤ K * cbNorm (fp81s21_J1 p.d) (φ j) := hmul
    have hχjgen : ∀ x, weightedGen (R.ρ 0) χj x = p.γ * r26t3_a R (φ j) x := by
      intro x
      have hχ₀two : ContDiff ℝ 2 χ₀ := hχ₀smooth.of_le (by
        have hle : (2 : ℕ) ≤ r26t3_k p.d + 1 := by
          rw [hkd]
          unfold fp81s21_k0
          have hd := p.hd
          omega
        exact_mod_cast hle)
      rw [fp81s21_weightedGen_smul (R.ρ 0) χ₀ p.γ x
        hχ₀two, hχ₀gen x]
    exact ⟨χj, hχjsmooth, hχjderiv, hχjgen⟩
  choose χ hχsmooth hχderiv hχgen using hex
  refine ⟨⟨K, hK, χ, hχsmooth, hχderiv, hχgen, ?_, ?_, ?_⟩⟩
  · intro j
    obtain ⟨hRa, -, hRL, heq⟩ := hCa (φ j) (hq j)
    exact ⟨hRL, Filter.Eventually.of_forall heq⟩
  · intro j
    obtain ⟨hRa, -, -, -⟩ := hCa (φ j) (hq j)
    exact (HRS.MS.Tc5.tc5_cb_mono (m := fp81s21_k0 p.d) (J := r26t3_k p.d + 2)
      (by simp [fp81s21_k0, r26t3_k]) hRa).1
  · intro j
    obtain ⟨hRa, hRc, -, -⟩ := hCa (φ j) (hq j)
    have hnorm : 0 ≤ cbNorm (fp81s21_J1 p.d) (φ j) :=
      HRS.MS.Tc5.tc5_cb_nonneg _ _
    have hmono := (HRS.MS.Tc5.tc5_cb_mono (m := fp81s21_k0 p.d)
      (J := r26t3_k p.d + 2) (by simp [fp81s21_k0, r26t3_k]) hRa).2
    calc cbNorm (fp81s21_k0 p.d) (r26t3_a R (φ j)) ≤
          cbNorm (r26t3_k p.d + 2) (r26t3_a R (φ j)) := hmono
      _ ≤ Ca * cbNorm (r26t3_J p.d) (φ j) := hRc
      _ ≤ K * cbNorm (fp81s21_J1 p.d) (φ j) := by
        rw [hJd]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hnorm

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_k0_ge_one
#print axioms HRS.Fp81.S21.fp81s21_J1_ge_k0
#print axioms HRS.Fp81.S21.fp81s21_k0_lt_J1
#print axioms HRS.Fp81.S21.fp81s21_initial_scalar_corrector_exists
#print axioms HRS.Fp81.S21.fp81s21_weightedGen_smul
#print axioms HRS.Fp81.S21.fp81s21_initialFamData_exists
