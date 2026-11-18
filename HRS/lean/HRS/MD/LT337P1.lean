import HRS.Energy.Coercivity
import HRS.PDE.KernelInputsD1
import HRS.PDE.Toolbox.CoeffBounds
import HRS.Kernel.GradReg

/-!
# Packet LT1 (chunk D): the Lipschitz bound of the mean-field transport field

`lt1_lipschitz_proof` is the statement `HRS.MD.LT337.lt1_lipschitz` (M L3147).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS

namespace HRS.MD.LT337P1

variable {d N : ℕ}

/-- A `C^1` vector field on the torus is Lipschitz for `tdist` with constant `cbNorm 1`
(copy of `dynconv_lipschitzVF`, to avoid importing the heavy `DynConvAux1`). -/
theorem lt1_lipschitzVF_of_ck {v : Torus d → Euc d} (hv : Torus.IsCk 1 v) :
    IsLipschitzVF (Torus.cbNorm 1 v) v := by
  have hv' : Torus.IsCk ((1 : ℕ) : WithTop ℕ∞) v := by exact_mod_cast hv
  have hL : ∀ y, ‖fderiv ℝ (Torus.lift v) y‖ ≤ Torus.cbNorm 1 v := fun y => by
    have e : ‖iteratedFDeriv ℝ 1 (Torus.lift v) y‖ = ‖fderiv ℝ (Torus.lift v) y‖ := by
      rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0), norm_iteratedFDeriv_zero]
    rw [← e]
    exact KernelGrad.norm_iteratedFDeriv_le_cbNorm hv' le_rfl y
  have h1 : Differentiable ℝ (Torus.lift v) := hv.differentiable one_ne_zero
  intro x y
  set r := KernelGrad.centeredRep (x - y) with hr
  have hmk : Torus.mk (Torus.rep y + r) = x := by
    rw [KernelGrad.mk_add, Torus.mk_rep, hr, KernelGrad.mk_centeredRep]; abel
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := Torus.lift v) (fun u _ => h1 u)
    (fun u _ => hL u) convex_univ (Set.mem_univ (Torus.rep y)) (Set.mem_univ (Torus.rep y + r))
  have e1 : Torus.lift v (Torus.rep y + r) = v x := by simp [Torus.lift, hmk]
  have e2 : Torus.lift v (Torus.rep y) = v y := by simp [Torus.lift, Torus.mk_rep]
  rw [e1, e2, add_sub_cancel_left] at this
  exact this

theorem lt1_lipschitz_proof (hd : 2 ≤ d) (Λ ΛV Mb : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (D : DynData d), D.s = (d : ℝ) - 2 →
      (∀ v : Euc d, ‖Torus.matVec D.M v‖ ≤ Mb * ‖v‖) → Torus.IsCk 2 D.V → Torus.cbNorm 2 D.V ≤ ΛV →
      ∀ ρ : Torus d → ℝ, Torus.IsCk 3 ρ → Torus.cbNorm 3 ρ ≤ Λ →
        IsLipschitzVF L (meanFieldDrift D ρ) := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : (d : ℝ) - 2 < d := by linarith
  obtain ⟨C, hC⟩ := PDE.convGradConv_cbNorm_of_one_le (d := d) (s := (d : ℝ) - 2) hd1 hs0 hsd 1
  refine ⟨|Mb| * (|C| * |Λ|) + |ΛV|, by positivity, fun D hs hM hV hVb ρ hρ hρb => ?_⟩
  have hρ2 : Torus.IsCk (1 + 1) ρ := hρ.of_le (by norm_num)
  obtain ⟨hG, hGb⟩ := hC ρ hρ2
  have hρb2 : Torus.cbNorm (1 + 1) ρ ≤ Λ := (KernelGrad.cbNorm_mono (by norm_num)).trans hρb
  have hG1 : Torus.cbNorm 1
      (convGradConv (periodicRieszGrad d ((d : ℝ) - 2)) ρ) ≤ |C| * |Λ| := by
    have h0 : 0 ≤ Torus.cbNorm (1 + 1) ρ := KernelGrad.cbNorm_nonneg' ρ _
    calc _ ≤ C * Torus.cbNorm (1 + 1) ρ := hGb
      _ ≤ |C| * Torus.cbNorm (1 + 1) ρ := mul_le_mul_of_nonneg_right (le_abs_self C) h0
      _ ≤ |C| * |Λ| := mul_le_mul_of_nonneg_left (hρb2.trans (le_abs_self Λ)) (abs_nonneg _)
  have hLG := lt1_lipschitzVF_of_ck hG
  have hV2 : Torus.IsCk (1 + 1) D.V := hV
  have hgV : Torus.IsCk 1 (Torus.grad D.V) := PDE.isCk_grad 1 D.V hV2
  have hgVb : Torus.cbNorm 1 (Torus.grad D.V) ≤ |ΛV| :=
    (PDE.cbNorm_grad_le 1 D.V hV2).trans (hVb.trans (le_abs_self ΛV))
  have hLV := lt1_lipschitzVF_of_ck hgV
  have hMb : ∀ v : Euc d, ‖Torus.matVec D.M v‖ ≤ |Mb| * ‖v‖ := fun v =>
    (hM v).trans (mul_le_mul_of_nonneg_right (le_abs_self Mb) (norm_nonneg _))
  intro x y
  unfold meanFieldDrift
  rw [hs]
  have hlin : Torus.matVec D.M (convGradConv (periodicRieszGrad d ((d : ℝ) - 2)) ρ x) -
      Torus.matVec D.M (convGradConv (periodicRieszGrad d ((d : ℝ) - 2)) ρ y) =
      Torus.matVec D.M (convGradConv (periodicRieszGrad d ((d : ℝ) - 2)) ρ x -
        convGradConv (periodicRieszGrad d ((d : ℝ) - 2)) ρ y) := by
    unfold Torus.matVec; rw [map_sub]
  have hx := hLG x y
  have hy := hLV x y
  have htd : 0 ≤ KernelGrad.tdist x y := norm_nonneg _
  have e : (Torus.matVec D.M (convGradConv (periodicRieszGrad d ((d : ℝ) - 2)) ρ x) - Torus.grad D.V x) -
      (Torus.matVec D.M (convGradConv (periodicRieszGrad d ((d : ℝ) - 2)) ρ y) - Torus.grad D.V y) =
      (Torus.matVec D.M (convGradConv (periodicRieszGrad d ((d : ℝ) - 2)) ρ x -
        convGradConv (periodicRieszGrad d ((d : ℝ) - 2)) ρ y)) -
      (Torus.grad D.V x - Torus.grad D.V y) := by
    rw [← hlin]; abel
  rw [e]
  calc _ ≤ ‖Torus.matVec D.M (convGradConv (periodicRieszGrad d ((d : ℝ) - 2)) ρ x -
        convGradConv (periodicRieszGrad d ((d : ℝ) - 2)) ρ y)‖ +
        ‖Torus.grad D.V x - Torus.grad D.V y‖ := norm_sub_le _ _
    _ ≤ |Mb| * (Torus.cbNorm 1 (convGradConv (periodicRieszGrad d ((d : ℝ) - 2)) ρ) *
          KernelGrad.tdist x y) + Torus.cbNorm 1 (Torus.grad D.V) * KernelGrad.tdist x y := by
        gcongr
        · exact (hMb _).trans (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
    _ ≤ |Mb| * (|C| * |Λ| * KernelGrad.tdist x y) + |ΛV| * KernelGrad.tdist x y := by
        gcongr
    _ = _ := by ring

end HRS.MD.LT337P1
