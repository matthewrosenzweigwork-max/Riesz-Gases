import HRS.Uniform.Q12W3

/-!
# Q12, part W3c: strict positivity of the heat kernel and of smeared densities
-/

noncomputable section

open HRS MeasureTheory Filter Topology Set
open HRS.CoercAux
open scoped ENNReal NNReal BigOperators Real

namespace HRS.Uniform.Q12

variable {d : ℕ}

theorem q12_heatK_pos {t : ℝ} (hu : 0 < t) (x : Torus d) : 0 < heatK d t x := by
  choose y hy1 hy2 using fun i => exists_rep (x i)
  have hxy : x = fun i => ((y i : ℝ) : UnitAddCircle) := funext hy2
  set S : Fin d → ℂ := fun i => ∑' n : ℤ, Complex.exp (2 * π * Complex.I * n * (y i) - t * (n:ℂ)^2) with hS
  set f : Fin d → ℤ → ℂ := fun i n => Complex.exp (2 * π * Complex.I * n * (y i) - t * (n:ℂ)^2) with hf
  have hfn : ∀ i, Summable fun m => ‖f i m‖ := by
    intro i
    refine (summable_exp_sq t hu).congr fun m => ?_
    simp only [hf]
    rw [Complex.norm_exp]
    congr 1
    rw [show ((m:ℂ)) = ((m:ℝ):ℂ) by simp]
    simp [pow_two, Complex.mul_re]
  obtain ⟨hsum, hhas⟩ := pi_hasSum d f hfn
  have hterm : ∀ k : Lattice d, Real.exp (-t * Lattice.enorm k ^ 2) * Torus.cosMode k x =
      (∏ i, f i (k i)).re := by
    intro k
    have h1 : ∏ i, f i (k i) = ((Real.exp (-t * Lattice.enorm k ^ 2) : ℝ) : ℂ) * Torus.mode k x := by
      rw [hxy, mode_eq_prod]
      have h2 : ∏ i, f i (k i) = (∏ i, Complex.exp (-((t:ℂ) * ((k i : ℤ):ℂ)^2))) *
          ∏ i, Complex.exp (2 * π * Complex.I * (k i : ℤ) * (y i : ℝ)) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp only [hf]
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [h2, ← Complex.exp_sum, Complex.ofReal_exp, enorm_sq]
      congr 2
      push_cast
      rw [neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [h1, Complex.re_ofReal_mul]
    rfl
  have hre : heatK d t x = (∏ i, S i).re := by
    unfold heatK
    simp_rw [hterm]
    rw [← Complex.re_tsum hsum.of_norm, hhas.tsum_eq]
  have hS' : ∀ i, S i = ((Real.sqrt (π / t) * ∑' n : ℤ, Real.exp (-(π^2 * ((n:ℝ) - y i)^2 / t)) : ℝ) : ℂ) :=
    fun i => theta_eq t (y i) hu
  have hpos : ∀ i, 0 < Real.sqrt (π / t) * ∑' n : ℤ, Real.exp (-(π^2 * ((n:ℝ) - y i)^2 / t)) := by
    intro i
    refine mul_pos (Real.sqrt_pos.2 (by positivity)) ?_
    have hsm : Summable fun n : ℤ => Real.exp (-(π^2 * ((n:ℝ) - y i)^2 / t)) := by
      refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
        (summable_exp_sq (π ^ 2 / (4 * t)) (by positivity))
      apply Real.exp_le_exp.2
      have := sq_sub_ge (y i) (hy1 i) n
      have h4 : 0 ≤ π ^ 2 / t := by positivity
      calc -(π ^ 2 * ((n : ℝ) - y i) ^ 2 / t) = -((π ^ 2 / t) * ((n : ℝ) - y i) ^ 2) := by ring
        _ ≤ -((π ^ 2 / t) * ((n : ℝ) ^ 2 / 4)) := by nlinarith
        _ = -(π ^ 2 / (4 * t)) * (n : ℝ) ^ 2 := by field_simp
    exact hsm.tsum_pos (fun n => (Real.exp_pos _).le) 0 (Real.exp_pos _)
  rw [hre]
  simp_rw [hS']
  rw [← Complex.ofReal_prod, Complex.ofReal_re]
  exact Finset.prod_pos fun i _ => hpos i

lemma q12_smearDens_pos {t : ℝ} (ht : 0 < t) (ν : Measure (Torus d)) [IsProbabilityMeasure ν]
    (z : Torus d) : 0 < smearDens d t ν z := by
  have hc : Continuous fun y : Torus d => heatK d t (z - y) :=
    (continuous_heatK ht).comp (continuous_const.sub continuous_id)
  obtain ⟨y₀, -, hy₀⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := Torus d))
    hc.continuousOn
  have hcpos : 0 < heatK d t (z - y₀) := q12_heatK_pos ht _
  have hge : ∀ y, heatK d t (z - y₀) ≤ heatK d t (z - y) := fun y => hy₀ (Set.mem_univ y)
  unfold smearDens
  calc 0 < heatK d t (z - y₀) := hcpos
    _ = ∫ y, heatK d t (z - y₀) ∂ν := by simp
    _ ≤ ∫ y, heatK d t (z - y) ∂ν := integral_mono (integrable_const _)
        (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hge

end HRS.Uniform.Q12
