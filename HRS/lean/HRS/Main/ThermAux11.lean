import HRS.Main.ThermAux1
import HRS.Sections.Q40bAux2
import HRS.Main.GFB2Aux2

/-!
# THERM helper 11: continuity of measure-valued paths in `E_m`, and the trajectory of `PreparedData`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- The mean-field trajectory of `PreparedData` is a smooth positive trajectory. -/
theorem therm_traj (S : PreparedData d) :
    IsSmoothPositiveTrajectory d S.s S.β S.V S.ρ0 S.ρ :=
  ⟨S.hs0, S.hsd, S.hβ, S.hV, S.hρ0, fun K hK => by
    obtain ⟨ρc, h1, h2⟩ := S.hρ K hK
    exact ⟨ρc, h1, fun t _ => congrFun h2 t⟩⟩

/-- Continuity of a path of probability measures in `E_m`, from continuity of the coefficients. -/
theorem therm_cont_ofMeasureDiff {m : ℝ} (hm2 : (d : ℝ) < 2 * m) {α : Type*} [TopologicalSpace α]
    (μ ν : α → Measure (Torus d)) [∀ a, IsProbabilityMeasure (μ a)]
    [∀ a, IsProbabilityMeasure (ν a)]
    (hμ : ∀ k, Continuous fun a => Torus.measureRealCoeff (μ a) k)
    (hν : ∀ k, Continuous fun a => Torus.measureRealCoeff (ν a) k) :
    Continuous fun a => NegSobolev.ofMeasureDiff m (μ a) (ν a) := by
  refine GF.gfb2_continuous_of_coords _ (fun k => 8 * Lattice.jp k.1 ^ (-(2 * m)))
    (((summable_jp_rpow (d := d) m hm2)).mul_left 8) (fun a k => ?_) (fun k => ?_)
  · rw [coord_ofMeasureDiff hm2]
    have h1 := Torus.abs_measureRealCoeff_le (μ a) k
    have h2 := Torus.abs_measureRealCoeff_le (ν a) k
    simp only [measure_univ, ENNReal.toReal_one, mul_one] at h1 h2
    have h3 : |Torus.measureRealCoeff (μ a) k - Torus.measureRealCoeff (ν a) k| ≤ 2 * Real.sqrt 2 :=
      (abs_sub _ _).trans (by linarith)
    rw [mul_pow, Torus.jp_rpow_sq]
    have h4 : (Torus.measureRealCoeff (μ a) k - Torus.measureRealCoeff (ν a) k) ^ 2 ≤ 8 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h3 2
      rw [sq_abs] at this
      calc _ ≤ (2 * Real.sqrt 2) ^ 2 := this
        _ = 8 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
    calc Lattice.jp k.1 ^ (2 * -m) * (Torus.measureRealCoeff (μ a) k - Torus.measureRealCoeff (ν a) k) ^ 2
        ≤ Lattice.jp k.1 ^ (2 * -m) * 8 :=
          mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg (Torus.jp_pos k.1).le _)
      _ = 8 * Lattice.jp k.1 ^ (-(2 * m)) := by rw [mul_comm]; congr 2; ring
  · simp only [coord_ofMeasureDiff hm2]
    exact continuous_const.mul ((hμ k).sub (hν k))

/-- `t ↦ ∫ ψ ρ^t` is continuous on `[0,T]` along the trajectory. -/
theorem therm_weak_cont (S : PreparedData d) (T : ℝ) (ψ : Torus d → ℝ) (hψ : Continuous ψ) :
    ContinuousOn (fun t => ∫ x, ψ x * S.ρ t x) (Set.Icc 0 T) := by
  have hjc := Q40b.q40b_jointCont (by have := S.hd; omega) (therm_traj S) T
  have hF : Continuous (Function.uncurry fun (t : Set.Icc (0 : ℝ) T) (x : Torus d) => ψ x * S.ρ t.1 x) := by
    have h1 : Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => (p.1.1, p.2) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have h2 : Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => S.ρ p.1.1 p.2 :=
      hjc.comp_continuous h1 (fun p => ⟨p.1.2, Set.mem_univ _⟩)
    exact (hψ.comp continuous_snd).mul h2
  have := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Torus d))) hF
    isCompact_univ
  rw [continuousOn_iff_continuous_restrict]
  simpa [Measure.restrict_univ, Function.comp_def, Set.restrict_def] using this

theorem therm_density (S : PreparedData d) {t : ℝ} (ht : 0 ≤ t) : IsProbDensity (S.ρ t) :=
  (Q40b.q40b_meanField (by have := S.hd; omega) (therm_traj S) (T := t + 1) (by linarith)).density t
    ⟨ht, by linarith⟩

end Main

end HRS
