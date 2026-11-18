import HRS.Main.A1014Aux3

/-!
# Packet A1014, part 5: the `L²` Parseval bound in `E_m = NegSobolev d m`

`a1014_lintegral_sq_norm_le`: if `(E Q_j²)^{1/2} ≤ b_j` with `b` summable, then `(E‖Q‖²)^{1/2} ≤ ∑_j b_j`
(Parseval and Tonelli: `E‖Q‖² = ∑_j E Q_j² ≤ ∑_j b_j² ≤ (∑_j b_j)²`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A1014

variable {d : ℕ}

/-- the unit vector of the coordinate `k` of `E_m`. -/
def a1014unit (m : ℝ) (k : NonzeroLattice d) : NegSobolev d m :=
  (lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2)

theorem a1014unit_inner {m : ℝ} (k : NonzeroLattice d) (F : NegSobolev d m) :
    inner ℝ (a1014unit m k) F = NegSobolev.coord F k := by
  classical
  have h := lp.inner_single_left (𝕜 := ℝ) (G := fun _ : NonzeroLattice d => ℝ) k (1 : ℝ)
    (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F)
  refine h.trans ?_
  simp [NegSobolev.coord]

theorem a1014_coord_continuous (m : ℝ) (j : NonzeroLattice d) :
    Continuous fun F : NegSobolev d m => NegSobolev.coord F j := by
  have e : (fun F : NegSobolev d m => NegSobolev.coord F j) =
      fun F => innerSL ℝ (a1014unit m j) F := by
    funext F; rw [innerSL_apply_apply, a1014unit_inner]
  rw [e]; exact (innerSL ℝ (a1014unit m j)).continuous

theorem a1014_lp2 (X : ℝ≥0∞) {y : ℝ} (hy : 0 ≤ y) (h : X ≤ ENNReal.ofReal (y ^ 2)) :
    X ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal y := by
  refine (ENNReal.rpow_le_rpow h (by norm_num)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  congr 1
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hy]

theorem a1014_tsum_sq_le {b : NonzeroLattice d → ℝ} (hb0 : ∀ j, 0 ≤ b j) (hbs : Summable b) :
    Summable (fun j => b j ^ 2) ∧ ∑' j, b j ^ 2 ≤ (∑' j, b j) ^ 2 := by
  have hB0 : 0 ≤ ∑' j, b j := tsum_nonneg hb0
  have hsum : Summable (fun j => b j ^ 2) := by
    refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) (hbs.mul_left (∑' j, b j))
    have hj : b j ≤ ∑' j, b j := hbs.le_tsum j (fun i _ => hb0 i)
    rw [sq]
    exact mul_le_mul_of_nonneg_right hj (hb0 j) |>.trans_eq (by ring)
  refine ⟨hsum, hsum.tsum_le_of_sum_le fun s => ?_⟩
  calc ∑ j ∈ s, b j ^ 2 ≤ (∑ j ∈ s, b j) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => hb0 j)
    _ ≤ (∑' j, b j) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => hb0 j)
          (hbs.sum_le_tsum s (fun j _ => hb0 j)) 2

theorem a1014_lintegral_sq_norm_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m : ℝ}
    (Q : Ω → NegSobolev d m) (hQ : AEMeasurable Q P) (b : NonzeroLattice d → ℝ)
    (hb0 : ∀ j, 0 ≤ b j) (hbs : Summable b)
    (hc : ∀ j, ∫⁻ ω, ENNReal.ofReal (NegSobolev.coord (Q ω) j ^ 2) ∂P ≤ ENNReal.ofReal (b j ^ 2)) :
    (∫⁻ ω, ENNReal.ofReal (‖Q ω‖ ^ (2 : ℝ)) ∂P) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (∑' j, b j) := by
  obtain ⟨hb2s, hb2le⟩ := a1014_tsum_sq_le hb0 hbs
  refine a1014_lp2 _ (tsum_nonneg hb0) ?_
  calc ∫⁻ ω, ENNReal.ofReal (‖Q ω‖ ^ (2 : ℝ)) ∂P
      = ∫⁻ ω, ∑' j, ENNReal.ofReal (NegSobolev.coord (Q ω) j ^ 2) ∂P := by
        refine lintegral_congr fun ω => ?_
        obtain ⟨h1, h2⟩ := NegSobolev.coord_sq (Q ω)
        rw [Real.rpow_two, h2, ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) h1]
    _ = ∑' j, ∫⁻ ω, ENNReal.ofReal (NegSobolev.coord (Q ω) j ^ 2) ∂P := by
        refine lintegral_tsum fun j => ?_
        exact (((a1014_coord_continuous m j).measurable.comp_aemeasurable hQ).pow_const 2
          ).ennreal_ofReal
    _ ≤ ∑' j, ENNReal.ofReal (b j ^ 2) := ENNReal.tsum_le_tsum hc
    _ = ENNReal.ofReal (∑' j, b j ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) hb2s).symm
    _ ≤ ENNReal.ofReal ((∑' j, b j) ^ 2) := ENNReal.ofReal_le_ofReal hb2le

end HRS.Main.A1014
