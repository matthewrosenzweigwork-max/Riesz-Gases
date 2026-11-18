import HRS.Commutator.Whole.LOWVAux8

/-!
# CMX-LOWV auxiliary 9: properties of `a = ψ_Λ * σ`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole HRS.Commutator.Whole.SAMP2

variable {d : ℕ}

theorem lowv_a_props {Λ : ℝ} (hΛ0 : 0 < Λ) (σ : SMeas d) (hσ : IsAdmissible σ) :
    ∃ (a : Euc d → ℝ) (φ : SchwartzMap (Euc d) ℂ),
      (∀ x, a x = σ.int (fun z => psiL Λ (x - z))) ∧ (∀ x, φ x = ((a x : ℝ) : ℂ)) ∧
      (∀ ξ, 𝓕 (⇑φ) ξ = cmxFB_gL d Λ ξ * σ.fourier ξ) ∧ Continuous a ∧
      Integrable (fun y : Euc d => (1 + ‖y‖) * |a y|) ∧ (∃ M : ℝ, ∀ x, |a x| ≤ M) ∧
      Integrable (fun x : Euc d => a x ^ 2) ∧ ∫ x, a x = σ.mass := by
  obtain ⟨φ, hφx, hφF⟩ := lowv_a_exists hΛ0 σ hσ
  set a : Euc d → ℝ := fun x => σ.int (fun z => psiL Λ (x - z)) with hadef
  have hφa : ∀ x, φ x = ((a x : ℝ) : ℂ) := hφx
  have habs : ∀ x, |a x| = ‖φ x‖ := fun x => by
    rw [hφa x, Complex.norm_real, Real.norm_eq_abs]
  have hac : Continuous a := by
    have : a = fun x => (φ x).re := by funext x; rw [hφa x]; simp
    rw [this]; exact Complex.continuous_re.comp φ.continuous
  have hai : Integrable (fun y : Euc d => (1 + ‖y‖) * |a y|) := by
    have := cmxFB_integrable_pow_mul φ 1
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [habs, pow_one]
  obtain ⟨C0, hC00, hC0⟩ := cmxFB_decay φ 0
  have hM : ∀ x, |a x| ≤ C0 := fun x => by
    rw [habs]; simpa using hC0 x
  obtain ⟨ha1, -⟩ := lowv_a_int_aux hac hai
  have ha2 : Integrable (fun x : Euc d => a x ^ 2) := by
    refine (ha1.const_mul C0).mono' (hac.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_pow, sq]
    calc |a x| * |a x| ≤ C0 * |a x| := by gcongr; exact hM x
      _ = _ := rfl
  refine ⟨a, φ, fun x => rfl, hφa, hφF, hac, hai, ⟨C0, hM⟩, ha2, ?_⟩
  -- the mass
  have h1 : 𝓕 (⇑φ) 0 = ∫ x, φ x := by
    rw [Real.fourier_eq]
    simp
  have h2 : 𝓕 (⇑φ) 0 = σ.fourier 0 := by
    rw [hφF]
    have : cmxFB_gL d Λ (0 : Euc d) = 1 := by
      unfold cmxFB_gL
      simp [cmxFB_chi_one (d := d) (ξ := 0) (by simp)]
    rw [this, one_mul]
  have h3 : σ.fourier 0 = ((σ.mass : ℝ) : ℂ) := by
    obtain ⟨hp, hn⟩ := hσ.1
    haveI := hp
    haveI := hn
    unfold SMeas.fourier SMeas.mass SMeas.int
    simp [integral_const]
  have h4 : ((∫ x, a x : ℝ) : ℂ) = ((σ.mass : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← h3, ← h2, h1]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact (hφa x).symm
  exact_mod_cast h4

end HRS.Commutator.Whole
