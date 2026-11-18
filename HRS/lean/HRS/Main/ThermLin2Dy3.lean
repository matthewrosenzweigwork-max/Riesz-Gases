import HRS.Main.GFEVAux16
import HRS.Main.ThermLin2Dy2

/-!
# THERMLIN 2, packet `Dy`, part 3: the pairing of the Dyson identity with `z ∈ E_m`

(i) `tl2dy_eval_duhamel_ioc`: a copy of `GF.gfev_eval_duhamel_abs` (GFEVAux15) with the bound required only on `(u,u']`;
(ii) the proof of `tl2_dyson_pairing`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

theorem tl2dy_eval_duhamel_ioc {m : ℝ} {f g : ℝ → Torus d → ℝ} {u u' B : ℝ} (huu' : u ≤ u')
    (hfu : MemSobolev m (f u)) (hfu' : MemSobolev m (f u'))
    (hg : ∀ s ∈ Set.Ioc u u', MemSobolev m (g s) ∧ sobolevNorm m (g s) ≤ B)
    (hint : ∀ k, IntervalIntegrable (fun s => Torus.funRealCoeff (g s) k) volume u u')
    (hcoef : ∀ k, Torus.funRealCoeff (f u) k - Torus.funRealCoeff (f u') k =
      ∫ s in u..u', Torus.funRealCoeff (g s) k)
    (z : NegSobolev d m) :
    NegSobolev.eval z (f u) - NegSobolev.eval z (f u') = ∫ s in u..u', NegSobolev.eval z (g s) := by
  classical
  set ζ : NonzeroLattice d → ℝ := fun k => NegSobolev.fourierCoeff z k with hζ
  set zS : Finset (NonzeroLattice d) → NegSobolev d m := fun S => q48bFin m S ζ with hzS
  have hts : Tendsto zS atTop (𝓝 z) := tendsto_trunc z
  -- finite version
  have hfin : ∀ S : Finset (NonzeroLattice d), NegSobolev.eval (zS S) (f u) - NegSobolev.eval (zS S) (f u') =
      ∫ s in u..u', NegSobolev.eval (zS S) (g s) := by
    intro S
    simp only [hzS, q48b_eval_fin]
    rw [← Finset.sum_sub_distrib]
    have : ∀ k ∈ S, ζ k * Torus.funRealCoeff (f u) k - ζ k * Torus.funRealCoeff (f u') k =
        ∫ s in u..u', ζ k * Torus.funRealCoeff (g s) k := by
      intro k _
      rw [intervalIntegral.integral_const_mul, ← hcoef k]; ring
    rw [Finset.sum_congr rfl this, ← intervalIntegral.integral_finset_sum]
    exact fun k _ => (hint k).const_mul _
  -- left side converges
  have hL : Tendsto (fun S => NegSobolev.eval (zS S) (f u) - NegSobolev.eval (zS S) (f u')) atTop
      (𝓝 (NegSobolev.eval z (f u) - NegSobolev.eval z (f u'))) :=
    (((gfev_eval_continuous hfu).tendsto z).comp hts).sub (((gfev_eval_continuous hfu').tendsto z).comp hts)
  -- right side converges (dominated convergence)
  have hR : Tendsto (fun S => ∫ s in u..u', NegSobolev.eval (zS S) (g s)) atTop
      (𝓝 (∫ s in u..u', NegSobolev.eval z (g s))) := by
    simp only [intervalIntegral.integral_of_le huu']
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (‖z‖ + 1) * B) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun S => ?_
      have : (fun s => NegSobolev.eval (zS S) (g s)) = fun s => ∑ k ∈ S, ζ k * Torus.funRealCoeff (g s) k := by
        funext s; simp only [hzS, q48b_eval_fin]
      rw [this]
      refine Finset.aestronglyMeasurable_fun_sum (f := fun k s => ζ k * Torus.funRealCoeff (g s) k)
        (μ := volume.restrict (Set.Ioc u u')) S fun k _ => ?_
      exact ((hint k).1.aestronglyMeasurable).const_mul _
    · have hev : ∀ᶠ S in atTop, ‖zS S‖ ≤ ‖z‖ + 1 := by
        have := (continuous_norm.tendsto z).comp hts
        filter_upwards [this.eventually (gt_mem_nhds (by linarith : ‖z‖ < ‖z‖ + 1))] with S hS using hS.le
      filter_upwards [hev] with S hS
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
      obtain ⟨hm, hB⟩ := hg s hs
      rw [Real.norm_eq_abs]
      refine (gfev_abs_eval_le (zS S) hm).trans ?_
      exact mul_le_mul hS hB (Real.sqrt_nonneg _) (by positivity)
    · exact integrable_const _
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
      exact ((gfev_eval_continuous (hg s hs).1).tendsto z).comp hts
  have := tendsto_nhds_unique (hL.congr fun S => hfin S) hR
  exact this


end HRS.GF
