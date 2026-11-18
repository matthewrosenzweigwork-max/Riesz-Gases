import HRS.MC.CepP3Aux6

/-!
# Packet P3, Aux7: `fkeIto` of a section of a periodic function equals `L`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP3

open HRS

variable {d N : ℕ}

/-- A periodic function `G` on the covering space, viewed as a time-dependent function on `Config`
through the section `repC`. -/
def PhiOf (G : ℝ × (Fin N → Euc d) → ℝ) : ℝ → Config d N → ℝ := fun r x => G (r, repC x)

theorem configLift_PhiOf (G : ℝ × (Fin N → Euc d) → ℝ) (hper : ∀ (w : Fin N → Lattice d) p, G (tau w p) = G p)
    (r : ℝ) (Y : Fin N → Euc d) : configLift (PhiOf G) r Y = G (r, Y) := by
  show G (r, repC (mkC Y)) = G (r, Y)
  rw [repC_mkC]
  have : (r, Y - lat (flo Y)) = tau (-flo Y) (r, Y) := by
    simp [tau, lat_neg, sub_eq_add_neg]
  rw [this, hper]

theorem fkeIto_eq_Lop (D : DynData d) {G : ℝ × (Fin N → Euc d) → ℝ} (hG : ContDiff ℝ 2 G)
    (hper : ∀ (w : Fin N → Lattice d) p, G (tau w p) = G p) {T r : ℝ} (hr : r ∈ Ioo 0 T)
    (Y : Fin N → Euc d) :
    fkeIto D T (PhiOf G) r Y = Lop D.invβ (bC D) G (r, Y) := by
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hlift : configLift (PhiOf G) = fun r Y => G (r, Y) :=
    funext fun r => funext fun Y => configLift_PhiOf G hper r Y
  have h1 : derivWithin (fun r' => G (r', Y)) (Icc 0 T) r = fderiv ℝ G (r, Y) (1, 0) := by
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hr.1 hr.2)]
    exact (hasDerivAt_slice_time hGd Y r).deriv
  have h2 : fderiv ℝ (fun Z => G (r, Z)) Y (driftVec D (fun j => Torus.mk (Y j)))
      = fderiv ℝ G (r, Y) (0, bC D (r, Y)) := by
    rw [fderiv_slice_space hGd]
    rfl
  have hk : ∀ k : Fin N × Fin d,
      fderiv ℝ (fderiv ℝ (fun Z => G (r, Z))) Y (liftedNoise D k) (liftedNoise D k)
        = (2 * D.invβ) * fderiv ℝ (fderiv ℝ G) (r, Y) (0, configBasis d N k) (0, configBasis d N k) := by
    intro k
    rw [fderiv2_slice_space hG]
    have hc : liftedNoise D k = Real.sqrt (2 * D.invβ) • configBasis d N k := rfl
    have h2' : Real.sqrt (2 * D.invβ) ^ 2 = 2 * D.invβ := Real.sq_sqrt (by linarith [D.hβ])
    rw [hc]
    have e : ((0 : ℝ), Real.sqrt (2 * D.invβ) • configBasis d N k)
        = Real.sqrt (2 * D.invβ) • ((0 : ℝ), configBasis d N k) := by simp
    rw [e]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    linear_combination (fderiv ℝ (fderiv ℝ G) (r, Y) (0, configBasis d N k)
      (0, configBasis d N k)) * h2'
  unfold fkeIto
  simp only [hlift]
  rw [h1, h2, Finset.sum_congr rfl (fun k _ => hk k), ← Finset.mul_sum]
  unfold Lop
  ring

end HRS.MC.CepP3
