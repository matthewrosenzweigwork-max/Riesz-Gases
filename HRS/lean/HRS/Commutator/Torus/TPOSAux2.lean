import HRS.Commutator.Torus.TPOSAux1

/-!
# T-POS helpers, part 2: Fourier transform of `f_η`

`𝓕 f_1 = f̂_1` (Fubini over the scale integral) and, by scaling, `𝓕 f_η = fHatEta`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

lemma tpos_fourier_f1 (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (ξ : Euc d) :
    𝓕 (fun x : Euc d => ((Whole.fTrunc s 1 x : ℝ) : ℂ)) ξ = ((Whole.f1Hat s ξ : ℝ) : ℂ) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hs : s < d := by linarith
  rw [Real.fourier_eq']
  set E : Euc d → ℂ := fun x => Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ) * Complex.I)) with hE
  have h1 : ∀ x : Euc d, Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ) * Complex.I)) •
      ((Whole.fTrunc s 1 x : ℝ) : ℂ) =
      ∫ t in Set.Ioc (0 : ℝ) 1, E x * ((Whole.cPhi d s * Whole.fInt s (x, t) : ℝ) : ℂ) := by
    intro x
    rw [integral_const_mul, integral_complex_ofReal, integral_const_mul, smul_eq_mul]
    rfl
  simp_rw [h1]
  have hI : Integrable (fun p : Euc d × ℝ => Whole.fInt s p)
      (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := Whole.integrable_fInt hs
  have hint : Integrable (fun p : Euc d × ℝ => E p.1 * ((Whole.cPhi d s * Whole.fInt s p : ℝ) : ℂ))
      (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    have hc : Continuous (fun p : Euc d × ℝ => E p.1) := by
      simp only [hE]
      fun_prop
    exact (hI.const_mul (Whole.cPhi d s)).ofReal.bdd_mul hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        simp only [hE]
        rw [Complex.norm_exp_ofReal_mul_I])
  rw [integral_integral_swap (f := fun (x : Euc d) (t : ℝ) =>
    E x * ((Whole.cPhi d s * Whole.fInt s (x, t) : ℝ) : ℂ)) hint]
  have h2 : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∫ x : Euc d, E x * ((Whole.cPhi d s * Whole.fInt s (x, t) : ℝ) : ℂ) =
      ((Whole.cPhi d s * (t ^ ((d : ℝ) - s - 1) * Whole.phiHatR d (t * ‖ξ‖)) : ℝ) : ℂ) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hF := Whole.cmxSA_fourier_comp t ht0 (fun x : Euc d => ((Whole.phi x : ℝ) : ℂ)) ξ
    simp only [Real.fourier_eq'] at hF
    have e1 : ∀ x : Euc d, E x * ((Whole.cPhi d s * Whole.fInt s (x, t) : ℝ) : ℂ) =
        ((Whole.cPhi d s * t ^ ((d : ℝ) - s - 1) * t ^ (-(d : ℝ)) : ℝ) : ℂ) *
          (Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ) * Complex.I)) •
            ((Whole.phi (t⁻¹ • x) : ℝ) : ℂ)) := by
      intro x
      simp only [hE, Whole.fInt, Whole.phiT, smul_eq_mul]
      rw [Real.rpow_sub_one ht0.ne']
      push_cast
      field_simp
    simp_rw [e1]
    rw [integral_const_mul, hF]
    have := Whole.fourier_phi (d := d) (t • ξ)
    simp only [Real.fourier_eq'] at this
    rw [this]
    have hn : ‖t • ξ‖ = t * ‖ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    rw [hn]
    have h3 : (t ^ (-(d : ℝ)) : ℝ) * t ^ d = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add ht0]; simp
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    linear_combination (Whole.cPhi d s * t ^ ((d : ℝ) - s - 1) * Whole.phiHatR d (t * ‖ξ‖)) * h3
  rw [setIntegral_congr_fun measurableSet_Ioc h2, integral_complex_ofReal, integral_const_mul,
    Whole.f1Hat_eq]

lemma tpos_fourier_fTrunc (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) (ξ : Euc d) :
    𝓕 (fun x : Euc d => ((Whole.fTrunc s η x : ℝ) : ℂ)) ξ = ((fHatEta d s η ξ : ℝ) : ℂ) := by
  have hc := Whole.cmxSA_fourier_comp η hη (fun z : Euc d => ((Whole.fTrunc s 1 z : ℝ) : ℂ)) ξ
  have key : ∫ v : Euc d, Complex.exp ((↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I)) •
      ((Whole.fTrunc s 1 (η⁻¹ • v) : ℝ) : ℂ) =
      ((η ^ d : ℝ) : ℂ) * ((Whole.f1Hat s (η • ξ) : ℝ) : ℂ) := by
    rw [← tpos_fourier_f1 hs0 hsd (η • ξ), ← hc]
    simp only [Real.fourier_eq']
  rw [Real.fourier_eq']
  have e : ∀ x : Euc d, Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ) * Complex.I)) •
      ((Whole.fTrunc s η x : ℝ) : ℂ) =
      ((η ^ (-s) : ℝ) : ℂ) * (Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ) * Complex.I)) •
        ((Whole.fTrunc s 1 (η⁻¹ • x) : ℝ) : ℂ)) := by
    intro x
    rw [tpos_fTrunc_scale hη x, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  simp_rw [e]
  rw [integral_const_mul, key, tpos_fHatEta_scale hη]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  have h3 : η ^ (-s) * η ^ d = η ^ ((d : ℝ) - s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hη]; congr 1; ring
  rw [← h3]; ring

end HRS.Commutator.TorusNote
