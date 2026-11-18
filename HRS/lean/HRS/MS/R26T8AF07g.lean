import HRS.MS.R26T8AF07f
import HRS.MS.R26T8AF05e
import HRS.MS.R26T8AF07d

/-!
# S8.2 observed-time layer, packet T8A.F07 (helper 07g): Sobolev bound of the local generator on `SobSmooth` functions

`sobolevNormE r (localP u) ≤ C · (sobolevNormE (r+2) u + sobolevNormE r (Euler u) + sobolevNormE (r+1) u)`
for every `SobSmooth` `u`, with `C` independent of `u`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_f07g_le (X S : ℝ≥0∞) (a C : ℝ) (ha : a ≤ C) (hX : X ≤ ENNReal.ofReal a * S) :
    X ≤ ENNReal.ofReal C * S :=
  hX.trans (r26t8a_f05e_mulR (ENNReal.ofReal_le_ofReal ha) S)

theorem r26t8a_f07g (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Euc d → ℝ, r26t8a_SobSmooth u →
      sobolevNormE (r : ℝ) (fun x => r26t8a_localP a beta rho u x) ≤
        ENNReal.ofReal C * (sobolevNormE ((r : ℝ) + 2) u + sobolevNormE (r : ℝ) (r26t8a_Euler u) +
          sobolevNormE ((r : ℝ) + 1) u) := by
  obtain ⟨CF, hCF0, hCF⟩ := r26t8a_f07e d hd a beta ha hbeta rho hrho r
  set C : ℝ := |beta⁻¹| * (d : ℝ) + |a| + CF with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    have := abs_nonneg beta⁻¹
    have := (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    have := abs_nonneg a
    positivity
  refine ⟨C, hC0, fun u hu => ?_⟩
  -- the three pieces of the local generator
  have hfun : (fun x => r26t8a_localP a beta rho u x) =
      fun x => ((fun x => beta⁻¹ * Laplacian.laplacian u x) x - (fun x => a * r26t8a_Euler u x) x) -
        (fun x => inner ℝ (forceMean rho x) (gradient u x)) x := by
    funext x
    simp only [r26t8a_localP, r26t8a_Euler]
  rw [hfun]
  have hsub1 := HRS.MS.SA12BD.sa12_sobolevNormE_sub (r : ℝ)
    (fun x => (fun x => beta⁻¹ * Laplacian.laplacian u x) x - (fun x => a * r26t8a_Euler u x) x)
    (fun x => inner ℝ (forceMean rho x) (gradient u x))
  have hsub2 := HRS.MS.SA12BD.sa12_sobolevNormE_sub (r : ℝ)
    (fun x => beta⁻¹ * Laplacian.laplacian u x) (fun x => a * r26t8a_Euler u x)
  refine hsub1.trans ?_
  refine (add_le_add hsub2 le_rfl).trans ?_
  have hLap := r26t8a_f07d_lap_sob hu (r : ℝ)
  have hX : sobolevNormE (r : ℝ) (fun x => beta⁻¹ * Laplacian.laplacian u x) ≤
      ENNReal.ofReal (|beta⁻¹| * (d : ℝ)) * sobolevNormE ((r : ℝ) + 2) u := by
    calc sobolevNormE (r : ℝ) (fun x => beta⁻¹ * Laplacian.laplacian u x)
        ≤ ENNReal.ofReal |beta⁻¹| * sobolevNormE (r : ℝ) (fun x => Laplacian.laplacian u x) :=
          r26t8a_f05e_sob_scale _ _ _
      _ ≤ ENNReal.ofReal |beta⁻¹| * ((d : ℝ≥0∞) * sobolevNormE ((r : ℝ) + 2) u) :=
          r26t8a_f05d_mulL hLap _
      _ = ENNReal.ofReal (|beta⁻¹| * (d : ℝ)) * sobolevNormE ((r : ℝ) + 2) u := by
          rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_natCast, mul_assoc]
  have hY : sobolevNormE (r : ℝ) (fun x => a * r26t8a_Euler u x) ≤
      ENNReal.ofReal |a| * sobolevNormE (r : ℝ) (r26t8a_Euler u) :=
    r26t8a_f05e_sob_scale _ _ _
  have hZ := hCF u hu
  have hp1 : 0 ≤ |beta⁻¹| * (d : ℝ) := by positivity
  have hCb1 : |beta⁻¹| * (d : ℝ) ≤ C := by linarith [hC, abs_nonneg a, hCF0]
  have hCb2 : |a| ≤ C := by linarith [hC, hp1, hCF0]
  have hCb3 : CF ≤ C := by linarith [hC, hp1, abs_nonneg a]
  have hXc := r26t8a_f07g_le _ _ _ _ hCb1 hX
  have hYc := r26t8a_f07g_le _ _ _ _ hCb2 hY
  have hZc := r26t8a_f07g_le _ _ _ _ hCb3 hZ
  refine (add_le_add (add_le_add hXc hYc) hZc).trans (le_of_eq ?_)
  ring

end HRS.MS.R26T8A

end
