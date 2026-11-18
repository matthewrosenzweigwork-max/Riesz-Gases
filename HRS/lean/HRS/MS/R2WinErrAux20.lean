import HRS.MS.R2WinErrAux19

/-!
# S10.4 input `hobs` for the stationary trajectory

`s104_hobs_stat`: `u ↦ 1_{r<b+u} ∂_aU(r,b+u)L_{b+u}φ_α(x)` is a.e.-strongly measurable on `[0,T]` for the stationary coefficient
(`r ≥ 0`): it equals `∂_aG1(b+u-r)(x)` with `G1 τ = U(0,τ)Lφ_α` jointly continuous (`s53_grad_continuous`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS HRS.Whole HRS.MS.S53

variable {d : ℕ}

theorem s104_hobs_stat (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρβ) (T b r : ℝ) (hT : 0 ≤ T) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (a' : Fin d) (α : MultiIndex d) (x : Euc d) :
    AEStronglyMeasurable (fun u : ℝ => if r < b + u then gradComp a' (propagatorW
      ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) r (b + u) (generatorW
        ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) (b + u)
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) x else 0) (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  simp only [wholeSpaceIndex]
  have hT0 : 0 ≤ b + T := by linarith
  obtain ⟨G0, G1, G2, hG⟩ := s104_stat_orbit hd hs0 hsd ha hβ hρ α hT0
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρβ) with hC
  have hcont : S53Cont (b + T) G1 := s53_cont_of_diff hG.cb1 hG.cb2 hG.diff12
  have hjc := s53_grad_continuous hT0 hG.cb1 hcont
  set h : ℝ → ℝ := fun u => if r < b + u then
    gradient (G1 (s53_clamp (b + T) (b + u - r))) x a' else 0 with hh
  have hmeas : AEStronglyMeasurable h (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    have hcf : Continuous fun u : ℝ => gradient (G1 (s53_clamp (b + T) (b + u - r))) x a' := by
      have h1 : Continuous fun u : ℝ => gradient (G1 (s53_clamp (b + T) (b + u - r))) x :=
        hjc.comp (Continuous.prodMk (by fun_prop) continuous_const)
      exact (EuclideanSpace.proj a' : Euc d →L[ℝ] ℝ).continuous.comp h1
    have : h = (Set.Ioi (-(b - r))).indicator (fun u => gradient (G1 (s53_clamp (b + T) (b + u - r))) x a') := by
      funext u
      simp only [hh, Set.indicator_apply, Set.mem_Ioi]
      split_ifs with h1 h2 h2
      · rfl
      · exfalso; linarith
      · exfalso; linarith
      · rfl
    rw [this]
    exact (hcf.aestronglyMeasurable.indicator measurableSet_Ioi)
  refine hmeas.congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun u hu => ?_)
  by_cases hru : r < b + u
  · simp only [hh, if_pos hru]
    have hbu : b + u ∈ Set.Icc (0 : ℝ) (b + T) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hrt : r ∈ Set.Icc (0 : ℝ) (b + u) := ⟨hr, hru.le⟩
    have hgen : generatorW C (b + u) (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) =
        generatorW C 0 (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) := rfl
    rw [hgen, s104_prop_shift hd hs0 hsd ha hβ hρ hrt (hG.ex1 (b + u) hbu)]
    have hτ : b + u - r ∈ Set.Icc (0 : ℝ) (b + T) := ⟨by linarith, by linarith [hu.2]⟩
    rw [← hG.eq1 _ hτ, s53_clamp_of_mem hτ]
    rfl
  · simp only [hh, if_neg hru]

end HRS.MS.R2WinErr
