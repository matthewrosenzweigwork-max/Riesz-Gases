import HRS.Torus.Sobolev
import HRS.Prob.Metrics
import HRS.Energy.StaticLimitGauss

/-!
# Basic facts for the static field limits that do not mention the Gibbs energy
(work package STAT-4.21)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS

section Wmean

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B] [CompleteSpace B]

theorem ofReal_norm_integral_sub_le_wE1 (P Q : Measure B) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hP : Integrable (fun x : B => x) P) (hQ : Integrable (fun x : B => x) Q) :
    ENNReal.ofReal ‖∫ x, x ∂P - ∫ y, y ∂Q‖ ≤ wassersteinE 1 P Q := by
  unfold wassersteinE
  refine le_iInf fun π => ?_
  obtain ⟨h1, h2⟩ := π.2
  haveI : IsProbabilityMeasure π.1 := IsCoupling.isProbabilityMeasure π.2
  have i1 : Integrable (fun z : B × B => z.1) π.1 := by
    have : Integrable (fun x : B => x) (π.1.map Prod.fst) := by rw [h1]; exact hP
    exact (integrable_map_measure aestronglyMeasurable_id measurable_fst.aemeasurable).1 this
  have i2 : Integrable (fun z : B × B => z.2) π.1 := by
    have : Integrable (fun x : B => x) (π.1.map Prod.snd) := by rw [h2]; exact hQ
    exact (integrable_map_measure aestronglyMeasurable_id measurable_snd.aemeasurable).1 this
  have e1 : ∫ x, x ∂P = ∫ z, z.1 ∂π.1 := by
    have := integral_map (μ := π.1) (f := fun x : B => x) measurable_fst.aemeasurable aestronglyMeasurable_id
    rw [h1] at this; exact this
  have e2 : ∫ y, y ∂Q = ∫ z, z.2 ∂π.1 := by
    have := integral_map (μ := π.1) (f := fun x : B => x) measurable_snd.aemeasurable aestronglyMeasurable_id
    rw [h2] at this; exact this
  rw [e1, e2, ← integral_sub i1 i2]
  have hint : Integrable (fun z : B × B => ‖z.1 - z.2‖) π.1 := (i1.sub i2).norm
  calc ENNReal.ofReal ‖∫ z, (z.1 - z.2) ∂π.1‖ ≤ ENNReal.ofReal (∫ z, ‖z.1 - z.2‖ ∂π.1) :=
        ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)
    _ = ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π.1 :=
        ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z => norm_nonneg _)
    _ = (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π.1) ^ (1 / (1 : ℝ)) := by simp

end Wmean

section Coord

variable {d N : ℕ} {m : ℝ}

/-- Coordinate functional on `E_m`. -/
def negCoordCLM (k : NonzeroLattice d) : NegSobolev d m →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun F => NegSobolev.coord F k, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }
    1 (fun F => by
      have := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) k
      show ‖(show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) k‖ ≤ 1 * ‖F‖
      rw [one_mul]; exact this)

theorem negCoordCLM_apply (k : NonzeroLattice d) (F : NegSobolev d m) :
    negCoordCLM k F = NegSobolev.coord F k := rfl

theorem integral_empirical (X : Config d N) {f : Torus d → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂(empirical X) = (N : ℝ)⁻¹ * ∑ i, f (X i) := by
  unfold empirical
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac' _ _ hf.stronglyMeasurable, Finset.mul_sum]
  · intro i _
    exact integrable_dirac enorm_lt_top

theorem continuous_realMode' (k : NonzeroLattice d) : Continuous (Torus.realMode k : Torus d → ℝ) := by
  unfold Torus.realMode
  split_ifs
  · exact continuous_const.mul (Torus.continuous_cosMode _)
  · exact continuous_const.mul (Torus.continuous_sinMode _)

theorem coord_ofMeasureDiff (hm : (d : ℝ) < 2 * m) (μ ν : Measure (Torus d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.ofMeasureDiff m μ ν) k =
      Lattice.jp k.1 ^ (-m) * (Torus.measureRealCoeff μ k - Torus.measureRealCoeff ν k) := by
  have h := NegSobolev.fourierCoeff_ofMeasureDiff hm μ ν k
  unfold NegSobolev.fourierCoeff at h
  rw [← h, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  simp

theorem norm_ofMeasureDiff_le (hm : (d : ℝ) < 2 * m) (μ ν : Measure (Torus d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ‖NegSobolev.ofMeasureDiff m μ ν‖ ≤
      Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) := by
  set F := NegSobolev.ofMeasureDiff m μ ν
  obtain ⟨hs2, hn⟩ := NegSobolev.coord_sq F
  have hs := summable_jp_rpow (d := d) m hm
  have hb : ∀ k : NonzeroLattice d, NegSobolev.coord F k ^ 2 ≤ 8 * Lattice.jp k.1 ^ (-(2 * m)) := by
    intro k
    rw [show NegSobolev.coord F k = _ from coord_ofMeasureDiff hm μ ν k, mul_pow, Torus.jp_rpow_sq,
      show 2 * -m = -(2 * m) by ring]
    have h1 := Torus.abs_measureRealCoeff_le μ k
    have h2 := Torus.abs_measureRealCoeff_le ν k
    simp only [measure_univ, ENNReal.toReal_one, mul_one] at h1 h2
    have h3 : |Torus.measureRealCoeff μ k - Torus.measureRealCoeff ν k| ≤ 2 * Real.sqrt 2 := by
      calc _ ≤ _ := abs_sub _ _
        _ ≤ Real.sqrt 2 + Real.sqrt 2 := add_le_add h1 h2
        _ = _ := by ring
    have h4 : (Torus.measureRealCoeff μ k - Torus.measureRealCoeff ν k) ^ 2 ≤ 8 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h3 2
      rw [sq_abs] at this
      calc _ ≤ _ := this
        _ = 8 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have hj : 0 ≤ Lattice.jp k.1 ^ (-(2 * m)) := Real.rpow_nonneg (Torus.jp_pos _).le _
    nlinarith
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  rw [hn, ← tsum_mul_left]
  exact Summable.tsum_le_tsum hb hs2 (hs.mul_left 8)

end Coord

end HRS
