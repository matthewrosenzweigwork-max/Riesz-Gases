import HRS.MS.R26T8AP11f12
import HRS.MS.R26T8AP11f4

/-!
# S8.2 T8A P11f (part 13): joint jets of `Stil ρ Q` for `|u-y| ≥ 1/4`
`r26t8a_f13_Stil_jets`: `‖D^j (uncurry (Stil ρ Q)) (u,y)‖ ≤ BS * Cρ * A * e^{-c|u|²} * jb(u)^M * jb(y)^M` for `|u-y| ≥ 1/4`,
`j ≤ k`, given `Conormal (k+2) b M σ' A Q` and Gaussian jet bounds `‖D^jρ u‖ ≤ Cρ e^{-c|u|²}` (`j ≤ k+1`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_f13_jet_fst {g : Euc d → ℝ} {m : ℕ} (hg : ContDiff ℝ (m : WithTop ℕ∞) g) (p : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ m (fun q : Euc d × Euc d => g q.1) p‖ ≤ ‖iteratedFDeriv ℝ m g p.1‖ := by
  have hfun : (fun q : Euc d × Euc d => g q.1) = g ∘ (ContinuousLinearMap.fst ℝ (Euc d) (Euc d)) := rfl
  rw [hfun, (ContinuousLinearMap.fst ℝ (Euc d) (Euc d)).iteratedFDeriv_comp_right hg p le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hn : ‖ContinuousLinearMap.fst ℝ (Euc d) (Euc d)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by simpa using norm_fst_le w
  have hprod : ∏ _j : Fin m, ‖ContinuousLinearMap.fst ℝ (Euc d) (Euc d)‖ ≤ 1 := by
    calc ∏ _j : Fin m, ‖ContinuousLinearMap.fst ℝ (Euc d) (Euc d)‖
        = ‖ContinuousLinearMap.fst ℝ (Euc d) (Euc d)‖ ^ m := by simp
      _ ≤ 1 := pow_le_one₀ (norm_nonneg _) hn
  calc _ ≤ ‖iteratedFDeriv ℝ m g p.1‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = _ := mul_one _

theorem r26t8a_f13_dirderiv_jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → ℝ) (a : E) (i : ℕ)
    (hG : ContDiff ℝ ((i + 1 : ℕ) : WithTop ℕ∞) G) (x : E) :
    ‖iteratedFDeriv ℝ i (fun w => fderiv ℝ G w a) x‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ (i + 1) G x‖ := by
  have hfun : (fun w => fderiv ℝ G w a) = (ContinuousLinearMap.apply ℝ ℝ a) ∘ (fderiv ℝ G) := by
    funext w; rfl
  have hd : ContDiff ℝ (i : WithTop ℕ∞) (fderiv ℝ G) := hG.fderiv_right (m := i) (by push_cast; exact le_rfl)
  rw [hfun]
  refine ((ContinuousLinearMap.apply ℝ ℝ a).norm_iteratedFDeriv_comp_left (hd.contDiffAt (x := x)) le_rfl).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun T => by
    simpa [mul_comm] using T.le_opNorm a

end HRS.MS.R26T8A
