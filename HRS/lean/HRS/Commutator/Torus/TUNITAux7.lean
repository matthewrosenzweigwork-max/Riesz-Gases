import HRS.Commutator.Torus.TUNITAux6
import HRS.Commutator.Torus.TPRODAux1

/-!
# T-UNIT-a helpers, part 7: Sobolev duality on `𝕋^d`

Prefix `tunit_`.  For real `L²` functions `ρ, H`:
`η^d |∫ ρ H| ≤ (sobSqT η (-α) ρ̂)^{1/2} (sobSqT η α Ĥ)^{1/2}` (Parseval and Cauchy–Schwarz, in `ℝ≥0∞`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- Cauchy–Schwarz for series in `ℝ≥0∞`. -/
theorem tunit_cs_tsum {ι : Type*} [Countable ι] (a b : ι → ℝ≥0∞) :
    ∑' j, a j * b j ≤ (∑' j, a j ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) * (∑' j, b j ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  letI : MeasurableSpace ι := ⊤
  haveI : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := Measure.count (α := ι))
    Real.HolderConjugate.two_two (f := a) (g := b) (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable
  simp only [lintegral_count, Pi.mul_apply] at h
  exact h

/-- The Parseval pairing of two real `L²` functions. -/
theorem tunit_parseval_pair {ρ H : Torus d → ℝ} (hρ : MemLp ρ 2 volume) (hH : MemLp H 2 volume) :
    ((∫ x, ρ x * H x : ℝ) : ℂ) = ∑' k : Lattice d, conj (Torus.fcoef ρ k) * Torus.fcoef H k := by
  have hF : MemLp (fun x => ((ρ x : ℝ) : ℂ)) 2 volume := hρ.ofReal
  have hG : MemLp (fun x => ((H x : ℝ) : ℂ)) 2 volume := hH.ofReal
  have hP := HRS.PDE.hasSum_parseval _ _ hF hG
  have hcoef : ∀ (A : Torus d → ℝ) (k : Lattice d),
      Torus.funFourierCoeff (fun x => ((A x : ℝ) : ℂ)) k = Torus.fcoef A k := by
    intro A k
    rw [HRS.PDE.funFourierCoeff_eq_int]
    rfl
  simp_rw [hcoef] at hP
  have e2 : ∀ t : Torus d, conj (((ρ t : ℝ) : ℂ)) * ((H t : ℝ) : ℂ) = ((ρ t * H t : ℝ) : ℂ) := by
    intro t
    rw [Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [e2] at hP
  rw [integral_complex_ofReal] at hP
  exact hP.tsum_eq.symm

/-- Sobolev duality: `η^d |∫ ρ H| ≤ (sobSqT η (-α) ρ̂)^{1/2} (sobSqT η α Ĥ)^{1/2}`. -/
theorem tunit_duality {ρ H : Torus d → ℝ} (hρ : MemLp ρ 2 volume) (hH : MemLp H 2 volume)
    {η : ℝ} (hη : 0 < η) (α : ℝ) :
    ENNReal.ofReal (η ^ d) * ENNReal.ofReal |∫ x, ρ x * H x| ≤
      (sobSqT η (-α) (fun k => Torus.fcoef ρ k)) ^ ((1 : ℝ) / 2) *
        (sobSqT η α (fun k => Torus.fcoef H k)) ^ ((1 : ℝ) / 2) := by
  set w : Lattice d → ℝ := fun k => 1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2 with hw
  have hw1 : ∀ k, 0 < w k := fun k => by simp only [hw]; positivity
  set a : Lattice d → ℝ≥0∞ := fun k => ENNReal.ofReal ((w k) ^ (-α / 2)) * ‖Torus.fcoef ρ k‖ₑ with ha
  set b : Lattice d → ℝ≥0∞ := fun k => ENNReal.ofReal ((w k) ^ (α / 2)) * ‖Torus.fcoef H k‖ₑ with hb
  have hI : ENNReal.ofReal |∫ x, ρ x * H x| ≤ ∑' k, a k * b k := by
    have h1 : ENNReal.ofReal |∫ x, ρ x * H x| = ‖((∫ x, ρ x * H x : ℝ) : ℂ)‖ₑ := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    rw [h1, tunit_parseval_pair hρ hH]
    refine enorm_tsum_le_tsum_enorm.trans (le_of_eq (tsum_congr fun k => ?_))
    rw [enorm_mul, RCLike.enorm_conj]
    have hk : ENNReal.ofReal ((w k) ^ (-α / 2)) * ENNReal.ofReal ((w k) ^ (α / 2)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hw1 k).le _), ← Real.rpow_add (hw1 k)]
      have : -α / 2 + α / 2 = 0 := by ring
      rw [this, Real.rpow_zero, ENNReal.ofReal_one]
    calc ‖Torus.fcoef ρ k‖ₑ * ‖Torus.fcoef H k‖ₑ
        = (ENNReal.ofReal ((w k) ^ (-α / 2)) * ENNReal.ofReal ((w k) ^ (α / 2))) *
            (‖Torus.fcoef ρ k‖ₑ * ‖Torus.fcoef H k‖ₑ) := by rw [hk, one_mul]
      _ = a k * b k := by simp only [ha, hb]; ring
  have hsq : ∀ (t : ℝ) (F : Lattice d → ℂ),
      ∑' k, (ENNReal.ofReal ((w k) ^ (t / 2)) * ‖F k‖ₑ) ^ (2 : ℝ) =
        ∑' k, ENNReal.ofReal ((w k) ^ t) * ‖F k‖ₑ ^ 2 := by
    intro t F
    refine tsum_congr fun k => ?_
    rw [ENNReal.rpow_two, mul_pow, ← ENNReal.ofReal_pow (Real.rpow_nonneg (hw1 k).le _),
      ← Real.rpow_natCast, ← Real.rpow_mul (hw1 k).le]
    congr 3
    push_cast
    ring
  have hcs := tunit_cs_tsum a b
  have e1 : ∑' k, a k ^ (2 : ℝ) = ∑' k, ENNReal.ofReal ((w k) ^ (-α)) * ‖Torus.fcoef ρ k‖ₑ ^ 2 :=
    hsq (-α) (fun k => Torus.fcoef ρ k)
  have e2 : ∑' k, b k ^ (2 : ℝ) = ∑' k, ENNReal.ofReal ((w k) ^ α) * ‖Torus.fcoef H k‖ₑ ^ 2 :=
    hsq α (fun k => Torus.fcoef H k)
  have hη0 : (0 : ℝ) ≤ η ^ d := by positivity
  have hsplit : ENNReal.ofReal (η ^ d) =
      (ENNReal.ofReal (η ^ d)) ^ ((1 : ℝ) / 2) * (ENNReal.ofReal (η ^ d)) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  calc ENNReal.ofReal (η ^ d) * ENNReal.ofReal |∫ x, ρ x * H x|
      ≤ ENNReal.ofReal (η ^ d) * ((∑' k, a k ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
          (∑' k, b k ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) := by
        gcongr
        exact hI.trans hcs
    _ = (ENNReal.ofReal (η ^ d) * ∑' k, a k ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
          (ENNReal.ofReal (η ^ d) * ∑' k, b k ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        nth_rewrite 1 [hsplit]
        ring
    _ = (sobSqT η (-α) (fun k => Torus.fcoef ρ k)) ^ ((1 : ℝ) / 2) *
          (sobSqT η α (fun k => Torus.fcoef H k)) ^ ((1 : ℝ) / 2) := by
        rw [e1, e2]
        rfl

end HRS.Commutator.TorusNote
