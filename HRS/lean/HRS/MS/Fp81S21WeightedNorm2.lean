import HRS.MS.Fp81S21WeightedNorm
import HRS.MS.ProClosureS111WeightedEvaluation
import HRS.MS.FeatDecAux8
import HRS.MS.R26T8AF05e

/-! Comparison of the compact-test weighted dual norm with the negative
Sobolev norm on Schwartz tests. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux
  HRS.MS.ProClosureS111 HRS.MS.FixEq HRS.MS.S85

variable {d r : ℕ} {Pw : ℝ}

/-- A constant depending only on the weighted chart parameters compares
`dualNormE` with the weighted negative Sobolev norm for functionals that
are homogeneous on compact smooth tests. -/
theorem fp81s21_dualNormE_le_r2NegSobNorm
    (hP : (d : ℝ) < 2 * Pw) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : (Euc d → ℝ) → ℝ,
      (∀ c f, IsR2Test f → T (c • f) = c * T f) →
      dualNormE r Pw T ≤ ENNReal.ofReal C * r2NegSobNorm r Pw T := by
  obtain ⟨C0, hC0, hSob⟩ := weighted_conjugate_sobolev_bound d r Pw hP
  let C : ℝ := C0 + 1
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC.le, fun T hhom => ?_⟩
  unfold dualNormE
  refine iSup_le fun f => iSup_le fun hf => ?_
  let w : ℝ≥0∞ := weightedSobolevE r Pw f
  have hpos : 0 < w := hf.2.2.1
  have hfin : w < ⊤ := hf.2.2.2
  have htest : IsR2Test f := ⟨hf.1, hf.2.1⟩
  have hconj := hSob f htest
  let g : Euc d → ℝ := fun x => jbracket x ^ (-Pw) * f x
  have hgcd : ContDiff ℝ ∞ g := (s85_jbpow_contDiff (-Pw)).mul htest.1
  have hgcs : HasCompactSupport g := htest.2.mul_left
  let ψ₀ : SchwartzMap (Euc d) ℝ := hgcs.toSchwartzMap hgcd
  have hwrealpos : 0 < w.toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  let s : ℝ := C * w.toReal
  have hs : 0 < s := mul_pos hC hwrealpos
  let ψ : SchwartzMap (Euc d) ℝ := s⁻¹ • ψ₀
  have hψ₀ : (ψ₀ : Euc d → ℝ) = g := by
    funext x
    rfl
  have hnormE_g : HRS.Whole.sobolevNormE (r : ℝ) g =
      ENNReal.ofReal (HRS.Whole.sobolevNorm (r : ℝ) g) := by
    unfold HRS.Whole.sobolevNormE HRS.Whole.sobolevNorm
    rw [if_pos hconj.1]
  have hψEscale : HRS.Whole.sobolevNormE (r : ℝ) (ψ : Euc d → ℝ) ≤
      ENNReal.ofReal |s⁻¹| * HRS.Whole.sobolevNormE (r : ℝ) (ψ₀ : Euc d → ℝ) := by
    have h := HRS.MS.R26T8A.r26t8a_f05e_sob_scale (s⁻¹) (r : ℝ) (ψ₀ : Euc d → ℝ)
    change HRS.Whole.sobolevNormE (r : ℝ) (fun x => s⁻¹ * ψ₀ x) ≤ _
    exact h
  have hratio : (C0 * w.toReal) / (C * w.toReal) ≤ 1 := by
    apply (div_le_iff₀ hs).2
    rw [one_mul]
    dsimp [s, C]
    nlinarith [mul_nonneg (sub_nonneg.mpr hC0) (le_of_lt hwrealpos)]
  have hψball : HRS.Whole.sobolevNormE (r : ℝ) (ψ : Euc d → ℝ) ≤ 1 := by
    calc
      _ ≤ ENNReal.ofReal |s⁻¹| * ENNReal.ofReal (HRS.Whole.sobolevNorm (r : ℝ) g) := by
          simpa only [hψ₀, hnormE_g] using hψEscale
      _ = ENNReal.ofReal (|s⁻¹| * HRS.Whole.sobolevNorm (r : ℝ) g) :=
          (ENNReal.ofReal_mul (abs_nonneg _)).symm
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (by
          rw [abs_of_pos (inv_pos.mpr hs)]
          calc
            s⁻¹ * HRS.Whole.sobolevNorm (r : ℝ) g ≤
                s⁻¹ * (C0 * w.toReal) := mul_le_mul_of_nonneg_left hconj.2 (by positivity)
            _ = (C0 * w.toReal) / (C * w.toReal) := by
                dsimp [s]
                rw [div_eq_mul_inv]
                ring
            _ ≤ 1 := hratio)
      _ = 1 := by norm_num
  have htestball : HRS.Whole.sobolevNormE (r : ℝ) (ψ : Euc d → ℝ) ≤ 1 := hψball
  have hpoint : (fun x => jbracket x ^ Pw * (ψ : Euc d → ℝ) x) =
      s⁻¹ • f := by
    funext x
    simp only [ψ, SchwartzMap.smul_apply, smul_eq_mul, ψ₀,
      HasCompactSupport.toSchwartzMap_toFun]
    have hp : jbracket x ^ Pw * jbracket x ^ (-Pw) = 1 := by
      rw [← Real.rpow_add (s57p_jbracket_pos x)]
      simp
    calc
      jbracket x ^ Pw * (s⁻¹ * (jbracket x ^ (-Pw) * f x)) =
          s⁻¹ * ((jbracket x ^ Pw * jbracket x ^ (-Pw)) * f x) := by ring
      _ = s⁻¹ * f x := by rw [hp]; ring
  have hvalue : T (fun x => jbracket x ^ Pw * (ψ : Euc d → ℝ) x) =
      s⁻¹ * T f := by
    rw [hpoint]
    exact hhom s⁻¹ f htest
  have hunitval : ENNReal.ofReal |T (fun x => jbracket x ^ Pw *
      (ψ : Euc d → ℝ) x)| ≤ r2NegSobNorm r Pw T := by
    unfold r2NegSobNorm
    exact le_iSup_of_le ψ (le_iSup_of_le htestball le_rfl)
  have hrealScale : s * |T (fun x => jbracket x ^ Pw *
      (ψ : Euc d → ℝ) x)| = |T f| := by
    rw [hvalue, abs_mul, abs_of_pos (inv_pos.mpr hs)]
    field_simp
  have hscaleENN : ENNReal.ofReal |T f| = ENNReal.ofReal s *
      ENNReal.ofReal |T (fun x => jbracket x ^ Pw *
        (ψ : Euc d → ℝ) x)| := by
    rw [← ENNReal.ofReal_mul hs.le, hrealScale]
  have hsENN : ENNReal.ofReal s = ENNReal.ofReal C * w := by
    rw [show s = C * w.toReal by rfl, ENNReal.ofReal_mul hC.le,
      ENNReal.ofReal_toReal hfin.ne]
  have hnum : ENNReal.ofReal |T f| ≤
      (ENNReal.ofReal C * r2NegSobNorm r Pw T) * w := by
    calc
      ENNReal.ofReal |T f| = ENNReal.ofReal s *
          ENNReal.ofReal |T (fun x => jbracket x ^ Pw *
            (ψ : Euc d → ℝ) x)| := hscaleENN
      _ ≤ ENNReal.ofReal s * r2NegSobNorm r Pw T := mul_le_mul' le_rfl hunitval
      _ = (ENNReal.ofReal C * r2NegSobNorm r Pw T) * w := by
          rw [hsENN]
          ac_rfl
  refine ENNReal.div_le_of_le_mul ?_
  simpa [w] using hnum

#print axioms HRS.Fp81.S21.fp81s21_dualNormE_le_r2NegSobNorm

end HRS.Fp81.S21
