import HRS.Commutator.Torus.TPOSAux4

/-!
# T-POS helpers, part 5: `f_η^𝕋` and `g_η^𝕋` Fourier coefficients

The periodised truncation `perio f_η`: summability, integrability, mean, Fourier coefficients; the
coefficients of `fTorus` and `gTorus` (`tr_coef_formula`, first two clauses).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

lemma tpos_fTrunc_measurable (hη : 0 < η) : Measurable (Whole.fTrunc s η : Euc d → ℝ) := by
  have : (Whole.fTrunc s η : Euc d → ℝ) = fun x => η ^ (-s) * Whole.fTrunc s 1 (η⁻¹ • x) := by
    funext x; exact tpos_fTrunc_scale hη x
  rw [this]
  exact (Whole.measurable_fTrunc.comp (measurable_const_smul _)).const_mul _

lemma tpos_fTrunc_summable (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) (y : Euc d) :
    Summable fun m : Lattice d => Whole.fTrunc s η (y + Lattice.toEuc m) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith
  have hcp := Whole.cPhi_pos d hs0 hs2
  have h2 : (0 : ℝ) < 2 * (d : ℝ) + 4 - s := by linarith
  refine tpos_summable_shift (h := Whole.fTrunc s η) (C := Whole.cPhi d s / (2 * (d : ℝ) + 4 - s) *
      η ^ (2 * (d : ℝ) + 4 - s)) (r := 2 * (d : ℝ) + 4) (by positivity) (by linarith) ?_ y
  intro z hz
  rw [abs_of_nonneg (tpos_fTrunc_nonneg hs0 hs2 η z)]
  exact tpos_fTrunc_le hs0 hs2 hη hz

lemma tpos_perio_fTrunc_integrable (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) :
    Integrable (perio (Whole.fTrunc s η : Euc d → ℝ) : Torus d → ℝ) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  exact tpos_integrable_perio (tpos_fTrunc_measurable hη) (tpos_integrable_fTrunc hs0 hsd hη)
    (tpos_fTrunc_nonneg hs0 (by linarith) η) (tpos_fTrunc_summable hs0 hsd hη)

lemma tpos_integral_perio_fTrunc (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) :
    ∫ x : Torus d, perio (Whole.fTrunc s η : Euc d → ℝ) x =
      Whole.cPhi d s * (∫ x : Euc d, Whole.phi x) / ((d : ℝ) - s) * η ^ ((d : ℝ) - s) := by
  rw [tpos_integral_perio (tpos_fTrunc_measurable hη) (tpos_integrable_fTrunc hs0 hsd hη)
    (tpos_fTrunc_summable hs0 hsd hη), tpos_integral_fTrunc hs0 hsd hη]

lemma tpos_fTorus_integrable (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) :
    Integrable (fTorus s η : Torus d → ℝ) := by
  unfold fTorus
  exact ((tpos_perio_fTrunc_integrable hs0 hsd hη).sub (integrable_const _)).const_mul _

lemma tpos_integrable_mode_mul (n : Lattice d) {u : Torus d → ℝ} (hu : Integrable u) :
    Integrable (fun x => Torus.mode n x * (u x : ℂ)) :=
  hu.ofReal.bdd_mul (Torus.continuous_mode n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (Torus.norm_mode n x).le)

lemma tpos_fourier_zero (f : Euc d → ℝ) :
    𝓕 (fun y : Euc d => ((f y : ℝ) : ℂ)) 0 = ((∫ y, f y : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  simp [integral_complex_ofReal]

lemma tpos_fcoef_fTorus (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) (k : Lattice d) :
    Torus.fcoef (fTorus s η : Torus d → ℝ) k =
      (((if k = 0 then 0 else tScale s * fHatEta d s η (Lattice.toEuc k) : ℝ)) : ℂ) := by
  set P : Torus d → ℝ := perio (Whole.fTrunc s η : Euc d → ℝ) with hP
  set c : ℝ := ∫ y : Torus d, P y with hc
  have hPint : Integrable P := tpos_perio_fTrunc_integrable hs0 hsd hη
  have hco : ∀ k : Lattice d, Torus.fcoef P k = 𝓕 (fun y : Euc d => ((Whole.fTrunc s η y : ℝ) : ℂ))
      (Lattice.toEuc k) := fun k => tpos_fcoef_perio (tpos_fTrunc_measurable hη)
        (tpos_integrable_fTrunc hs0 hsd hη) (tpos_fTrunc_summable hs0 hsd hη) k
  have hmode : Integrable (fun x : Torus d => Torus.mode (-k) x) := Torus.integrable_mode (-k)
  have h1 : Torus.fcoef (fTorus s η : Torus d → ℝ) k =
      ((tScale s : ℝ) : ℂ) * (Torus.fcoef P k - (c : ℂ) * ∫ x : Torus d, Torus.mode (-k) x) := by
    unfold Torus.fcoef
    have : ∀ x : Torus d, Torus.mode (-k) x * ((fTorus s η x : ℝ) : ℂ) =
        ((tScale s : ℝ) : ℂ) * (Torus.mode (-k) x * ((P x : ℝ) : ℂ) - (c : ℂ) * Torus.mode (-k) x) := by
      intro x
      simp only [fTorus, hP, hc]
      push_cast
      ring
    simp_rw [this]
    rw [integral_const_mul, integral_sub (tpos_integrable_mode_mul (-k) hPint) (hmode.const_mul _),
      integral_const_mul]
  rw [h1, Torus.integral_mode]
  by_cases hk : k = 0
  · subst hk
    have hneg : (-(0 : Lattice d)) = 0 := neg_zero
    rw [hco, hneg]
    have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
    rw [this, tpos_fourier_zero]
    have hint : ∫ y : Euc d, Whole.fTrunc s η y = c := by
      rw [hc, hP, tpos_integral_perio (tpos_fTrunc_measurable hη) (tpos_integrable_fTrunc hs0 hsd hη)
        (tpos_fTrunc_summable hs0 hsd hη)]
    rw [hint]
    simp
  · have : ¬ (-k = 0) := fun h => hk (neg_eq_zero.1 h)
    rw [if_neg this, if_neg hk, hco, tpos_fourier_fTrunc hs0 hsd hη]
    push_cast
    ring


lemma tpos_fcoef_gTorus (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η)
    (k : Lattice d) :
    Torus.fcoef (gTorus s η : Torus d → ℝ) k = ((gTcoef d s η k : ℝ) : ℂ) := by
  have hd0 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd' : s < (d : ℝ) := by linarith
  have hint : Integrable (periodicRiesz d s : Torus d → ℝ) :=
    KernelAux.integrable_periodicRiesz (by omega) hs0 hsd'
  have hFint := tpos_fTorus_integrable (d := d) hs0 hsd hη
  have hae : (gTorus s η : Torus d → ℝ) =ᵐ[volume] fun x => periodicRiesz d s x - fTorus s η x := by
    filter_upwards [KernelAux.torus_ae_ne (by omega : 0 < d)] with x hx
    simp [gTorus, hx]
  unfold Torus.fcoef
  have h1 : ∫ x : Torus d, Torus.mode (-k) x * ((gTorus s η x : ℝ) : ℂ) =
      ∫ x : Torus d, (Torus.mode (-k) x * ((periodicRiesz d s x : ℝ) : ℂ) -
        Torus.mode (-k) x * ((fTorus s η x : ℝ) : ℂ)) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]; push_cast; ring
  rw [h1, integral_sub (tpos_integrable_mode_mul (-k) hint) (tpos_integrable_mode_mul (-k) hFint),
    KernelAux.integral_periodicRiesz_mode (by omega) hs0 hsd' k]
  have h2 := tpos_fcoef_fTorus hs0 hsd hη k
  unfold Torus.fcoef at h2
  rw [h2]
  unfold gTcoef rieszCoeff
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, if_false]
    push_cast
    ring

end HRS.Commutator.TorusNote
