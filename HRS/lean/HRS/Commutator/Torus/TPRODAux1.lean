import HRS.Commutator.Torus.Defs
import HRS.PDE.Fourier

/-!
# T-PROD helper file 1: Parseval in `ℝ≥0∞`, `sobSqT` through a Bessel representative, Fatou for `sobSqT`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- Parseval for a real `L²` function, in `ℝ≥0∞`. -/
lemma tprod_parseval_enn {H : Torus d → ℝ} (hH : MemLp H 2 volume) :
    ∑' k : Lattice d, ‖Torus.fcoef H k‖ₑ ^ 2 = eLpNorm H 2 volume ^ 2 := by
  have hC : MemLp (fun x => ((H x : ℝ) : ℂ)) 2 volume := hH.ofReal
  have hP := HRS.PDE.hasSum_parseval _ _ hC hC
  have hcoef : ∀ k, Torus.funFourierCoeff (fun x => ((H x : ℝ) : ℂ)) k = Torus.fcoef H k := by
    intro k
    rw [HRS.PDE.funFourierCoeff_eq_int]
    rfl
  have e1 : ∀ k : Lattice d, conj (Torus.funFourierCoeff (fun x => ((H x : ℝ) : ℂ)) k) *
      Torus.funFourierCoeff (fun x => ((H x : ℝ) : ℂ)) k = ((‖Torus.fcoef H k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [hcoef k, Complex.conj_mul']
    push_cast
    ring
  have e2 : ∀ t : Torus d, conj (((H t : ℝ) : ℂ)) * ((H t : ℝ) : ℂ) = (((H t) ^ 2 : ℝ) : ℂ) := by
    intro t
    rw [Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [e1, e2] at hP
  have hP' : HasSum (fun k : Lattice d => ‖Torus.fcoef H k‖ ^ 2) (∫ t, (H t) ^ 2) := by
    rw [integral_complex_ofReal] at hP
    exact Complex.hasSum_ofReal.1 hP
  have h1 : ∑' k : Lattice d, ‖Torus.fcoef H k‖ₑ ^ 2 = ENNReal.ofReal (∫ t, (H t) ^ 2) := by
    rw [← hP'.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hP'.summable]
    refine tsum_congr fun k => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [h1]
  have h2 : eLpNorm H 2 volume ^ 2 = ∫⁻ t, ‖H t‖ₑ ^ 2 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      hH.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [h2]
  have hi : Integrable (fun t => (H t) ^ 2) volume := by
    have := hH.integrable_sq
    exact this
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun t => by positivity)]
  refine lintegral_congr fun t => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  congr 1
  simp [sq_abs]

/-- The squared Bessel norm of a coefficient sequence represented by an `L²` function. -/
lemma tprod_sobSq_eq {H : Torus d → ℝ} (hH : MemLp H 2 volume) {η α : ℝ} {c : Lattice d → ℂ}
    (hc : ∀ k : Lattice d, Torus.fcoef H k =
      (((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (α / 2) : ℝ) : ℂ) * c k) :
    sobSqT η α c = ENNReal.ofReal (η ^ d) * eLpNorm H 2 volume ^ 2 := by
  rw [← tprod_parseval_enn hH]
  unfold sobSqT
  congr 1
  refine tsum_congr fun k => ?_
  have hx : 0 ≤ 1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2 := by positivity
  have hm : 0 ≤ (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (α / 2) :=
    Real.rpow_nonneg hx _
  have e1 : ‖(((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (α / 2) : ℝ) : ℂ)‖ₑ =
      ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (α / 2)) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hm]
  rw [hc k, enorm_mul, mul_pow, e1, ← ENNReal.ofReal_pow hm]
  congr 2
  generalize 1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2 = X at hx
  rw [← Real.rpow_natCast (X ^ (α / 2)) 2, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

/-- Fatou for `sobSqT`: a pointwise limit of coefficient sequences with `sobSqT ≤ B` has `sobSqT ≤ B`. -/
lemma tprod_sobSq_fatou {η t : ℝ} {c : Lattice d → ℂ} {cN : ℕ → Lattice d → ℂ} {B : ℝ≥0∞}
    (hlim : ∀ k, Tendsto (fun N => cN N k) atTop (𝓝 (c k)))
    (hB : ∀ N, sobSqT η t (cN N) ≤ B) : sobSqT η t c ≤ B := by
  unfold sobSqT at hB ⊢
  set a : ℝ≥0∞ := ENNReal.ofReal (η ^ d) with ha
  set w : Lattice d → ℝ≥0∞ := fun k =>
    ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ t) with hw
  rw [ENNReal.tsum_eq_iSup_sum, ENNReal.mul_iSup]
  refine iSup_le fun S => ?_
  have hT : Tendsto (fun N => a * ∑ k ∈ S, w k * ‖cN N k‖ₑ ^ 2) atTop
      (𝓝 (a * ∑ k ∈ S, w k * ‖c k‖ₑ ^ 2)) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_finsetSum _ fun k _ => ?_
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
    exact ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp (hlim k))
  refine le_of_tendsto' hT fun N => ?_
  refine le_trans ?_ (hB N)
  gcongr
  exact ENNReal.sum_le_tsum S

end HRS.Commutator.TorusNote
