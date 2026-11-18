import HRS.MS.R2WinErrAux10

/-!
# S10.4 packet E1b: the window feature is `C^k` with bound `C θ_b(r)` (from the orbit bounds of S10.3)

* `s104_gradComp_bound`: `R2OrbitGrad C k t ψ A c` (second bound of `W:r2:window-orbit-global`) gives, for every `r ∈ [0,t]` and `a`,
  `∂_a U(r,t)ψ ∈ C^k` with `‖D^j ∂_aU(r,t)ψ‖ ≤ A e^{-c(t-r)}`; when no classical adjoint solution exists `propagatorW = 0` and the bound is trivial.
* `s104_window_feature` (below): the window feature `r2WindowFeature` is `C^k` in `x` with `‖D^jΓ_{b,r,a}‖ ≤ B θ_b(r)`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.R2WinErr

open HRS HRS.Whole HRS.MS.Go

variable {d : ℕ}

/-- The window decay profile `θ_b(r) = e^{-c(b-r)}` for `r < b`, `1` for `r ≥ b`. -/
def s104_theta (c b r : ℝ) : ℝ := if r < b then Real.exp (-c * (b - r)) else 1

lemma s104_theta_pos (c b r : ℝ) : 0 < s104_theta c b r := by
  unfold s104_theta; split_ifs
  · exact Real.exp_pos _
  · exact one_pos

lemma s104_theta_le_one {c : ℝ} (hc : 0 ≤ c) (b r : ℝ) : s104_theta c b r ≤ 1 := by
  unfold s104_theta; split_ifs with h
  · rw [Real.exp_le_one_iff]
    have : 0 ≤ b - r := by linarith
    nlinarith
  · exact le_rfl

lemma s104_theta2_eq (c b r : ℝ) : s104_theta2 c b r = s104_theta c b r ^ 2 := by
  unfold s104_theta2 s104_theta
  split_ifs
  · rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  · norm_num

lemma s104_cbNormVecE_le {K : ℕ} {v : Euc d → Euc d} {A : ℝ} (hA : 0 ≤ A)
    (h : cbNormVecE K v ≤ ENNReal.ofReal A) : ∀ j ≤ K, ∀ x, ‖iteratedFDeriv ℝ j v x‖ ≤ A := by
  intro j hj x
  have h1 : ENNReal.ofReal ‖iteratedFDeriv ℝ j v x‖ ≤ cbNormVecE K v := by
    unfold cbNormVecE
    refine le_trans (le_iSup (fun x => ENNReal.ofReal ‖iteratedFDeriv ℝ j v x‖) x) ?_
    exact Finset.single_le_sum (f := fun i => ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ i v x‖)
      (fun _ _ => zero_le) (Finset.mem_range.2 (by omega))
  exact (ENNReal.ofReal_le_ofReal_iff hA).1 (h1.trans h)

lemma s104_gradComp_bound (C : WholeCoeff d) {k : ℕ} {t : ℝ} {ψ : Euc d → ℝ} {A c : ℝ} (hA : 0 ≤ A)
    (h : R2OrbitGrad C k t ψ A c) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) (a : Fin d) :
    ContDiff ℝ k (fun x => gradComp a (propagatorW C r t ψ) x) ∧
    ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => gradComp a (propagatorW C r t ψ) x) x‖ ≤
      A * Real.exp (-c * (t - r)) := by
  have hA' : 0 ≤ A * Real.exp (-c * (t - r)) := by positivity
  by_cases hex : ∃ f, IsClassicalAdjointW C t ψ f
  · have hp : propagatorW C r t ψ = hex.choose r := by
      unfold propagatorW; rw [dif_pos hex]
    rw [hp]
    obtain ⟨hcd, hcb⟩ := h hex.choose hex.choose_spec r hr
    set v : Euc d → Euc d := fun x => gradient (hex.choose r) x with hv
    have hbd := s104_cbNormVecE_le hA' hcb
    have hproj : (fun x => gradComp a (hex.choose r) x) = fun x => (EuclideanSpace.proj a : Euc d →L[ℝ] ℝ) (v x) := by
      funext x; rfl
    have hn : ‖(EuclideanSpace.proj a : Euc d →L[ℝ] ℝ)‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
      simpa using PiLp.norm_apply_le x a
    rw [hproj]
    refine ⟨(EuclideanSpace.proj a : Euc d →L[ℝ] ℝ).contDiff.comp hcd, fun j hj x => ?_⟩
    have := (EuclideanSpace.proj a : Euc d →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left hcd.contDiffAt (x := x)
      (n := j) (by exact_mod_cast hj)
    refine this.trans ?_
    exact (mul_le_of_le_one_left (norm_nonneg _) hn).trans (hbd j hj x)
  · have hp : propagatorW C r t ψ = 0 := by
      unfold propagatorW; rw [dif_neg hex]
    rw [hp]
    have hz : (fun x : Euc d => gradComp a (0 : Euc d → ℝ) x) = fun _ => (0 : ℝ) := by
      funext x; simp [gradComp, gradient]
    rw [hz]
    refine ⟨contDiff_const, fun j hj x => ?_⟩
    rcases j with _ | j
    · simp; positivity
    · rw [iteratedFDeriv_const_of_ne (by omega)]; simpa using hA'

lemma s104_window_feature_eq (C : WholeCoeff d) (m T b r : ℝ) (a : Fin d) (x : Euc d) :
    r2WindowFeature C m T (gradComp a) b r x =
      KSpace.mk (ellVec (d := d) m (fun α => gradComp a (propagatorW C r (max b r) (oscTestFun m α)) x))
        (open Classical in if h : MemLp (fun u : ℝ => ellVec (d := d) m (fun α =>
            if u ∈ Set.Icc (0 : ℝ) T then (if r < b + u then gradComp a (propagatorW C r (b + u)
              (generatorW C (b + u) (oscTestFun m α))) x else 0) else 0)) 2
          (volume.restrict (Set.Icc (0 : ℝ) T)) then h.toLp _ else 0)
        (ellVec (d := d) m (fun α => if b ≤ r then gradComp a (oscTestFun m α) x else 0)) := by
  classical
  unfold r2WindowFeature
  dsimp only
  congr 1
  · -- the middle slot
    set f : ℝ → OscDual d m := fun u => if r < b + u then ellVec m fun α => gradComp a
      (propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun m α))) x else 0 with hf
    set Fv : ℝ → OscDual d m := fun u => ellVec (d := d) m (fun α =>
      if u ∈ Set.Icc (0 : ℝ) T then (if r < b + u then gradComp a (propagatorW C r (b + u)
        (generatorW C (b + u) (oscTestFun m α))) x else 0) else 0) with hFv
    have hfF : f =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)] Fv := by
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun u hu => ?_)
      simp only [hf, hFv, hu, if_true]
      by_cases hru : r < b + u
      · simp [hru]
      · simp only [hru, if_false]
        exact (s55f_ellVec_zero m).symm
    by_cases hmf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T))
    · have hF : MemLp Fv 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := hmf.ae_eq hfF
      rw [dif_pos hmf, dif_pos hF]
      exact MemLp.toLp_congr hmf hF hfF
    · have hF : ¬ MemLp Fv 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := fun h => hmf (h.ae_eq hfF.symm)
      rw [dif_neg hmf, dif_neg hF]
  · split_ifs with h
    · rfl
    · exact (s55f_ellVec_zero m).symm

end HRS.MS.R2WinErr
