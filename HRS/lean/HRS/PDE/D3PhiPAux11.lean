import HRS.PDE.D3PhiPAux10

/-!
# D3PHIP, helper 11: `L^p` tools for packet C1 (`d3phi_approx_Lp`)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

theorem d3pp_int_le {q : Measure (Torus n)} [IsProbabilityMeasure q] {F : Torus n → ℝ}
    (hF : AEStronglyMeasurable F q) {p : ℝ≥0∞} (hp : 1 ≤ p) (hfin : eLpNorm F p q ≠ ⊤) :
    ‖∫ x, F x ∂q‖ ≤ (eLpNorm F p q).toReal := by
  refine (norm_integral_le_lintegral_norm F).trans ?_
  have h1 : (∫⁻ x, ENNReal.ofReal ‖F x‖ ∂q) = eLpNorm F 1 q := by
    rw [eLpNorm_one_eq_lintegral_enorm hF]
    simp only [ofReal_norm_eq_enorm]
  rw [h1]
  exact ENNReal.toReal_mono hfin (eLpNorm_le_eLpNorm_of_exponent_le hp)

theorem d3pp_smooth_pos_approx (q : Measure (Torus n)) [IsProbabilityMeasure q] {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) {f : Torus n → ℝ} (hf : MemLp f p q) (hf0 : ∀ x, 0 ≤ f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Torus n → ℝ, Torus.IsSmooth g ∧ (∀ x, 0 < g x) ∧
      eLpNorm (fun x => g x - f x) p q ≤ ENNReal.ofReal ε := by
  obtain ⟨φ, hφ, -⟩ := hf.exists_boundedContinuous_eLpNorm_sub_le hpt
    (ε := ENNReal.ofReal (ε / 3)) (by simp; positivity)
  set ψ0 : Torus n → ℝ := fun x => max (φ x) 0 with hψ0
  have cψ0 : Continuous ψ0 := φ.continuous.max continuous_const
  have h1 : eLpNorm (f - ψ0) p q ≤ ENNReal.ofReal (ε / 3) := by
    refine le_trans (eLpNorm_mono_ae (g := f - ⇑φ) ?_ ?_) hφ
    · exact hf.aestronglyMeasurable.sub cψ0.aestronglyMeasurable
    · refine ae_of_all _ fun x => ?_
      simp only [Pi.sub_apply, Real.norm_eq_abs, hψ0]
      have := hf0 x
      rcases le_total (φ x) 0 with h | h
      · rw [max_eq_right h]
        rw [sub_zero, abs_of_nonneg this, abs_of_nonneg (by linarith)]
        linarith
      · rw [max_eq_left h]
  set δ : ℝ := ε / 9 with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨ψ, hψs, hψ⟩ := d1_exists_smooth_approx cψ0 hδpos
  refine ⟨fun x => ψ x + 2 * δ, ?_, fun x => ?_, ?_⟩
  · have := d1_isSmooth_comb 1 (2 * δ) hψs (d1_isSmooth_const (n := n) 1)
    simpa using this
  · have := hψ x
    have h0 : 0 ≤ ψ0 x := le_max_right _ _
    rw [abs_le] at this
    linarith [this.1, this.2]
  · have h2 : eLpNorm (fun x => ψ x + 2 * δ - ψ0 x) p q ≤ ENNReal.ofReal (ε / 3) := by
      refine (eLpNorm_le_of_ae_bound (C := 3 * δ) ?_ (ae_of_all _ fun x => ?_)).trans ?_
      · exact ((d1c_continuous_of_isSmooth hψs).add continuous_const |>.sub cψ0).aestronglyMeasurable
      · have := hψ x
        rw [abs_le] at this
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [this.1, this.2]
      · simp only [measure_univ, ENNReal.one_rpow, one_mul]
        exact ENNReal.ofReal_le_ofReal (by rw [hδ]; linarith)
    have h3 : (fun x => ψ x + 2 * δ - f x) =
        (fun x => ψ x + 2 * δ - ψ0 x) + (fun x => ψ0 x - f x) := by
      funext x; simp
    have h4 : eLpNorm (fun x => ψ0 x - f x) p q ≤ ENNReal.ofReal (ε / 3) := by
      have : (fun x => ψ0 x - f x) = -(f - ψ0) := by funext x; simp
      rw [this, eLpNorm_neg]; exact h1
    rw [h3]
    refine (eLpNorm_add_le hp1).trans ?_
    calc _ ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) := add_le_add h2 h4
      _ = ENNReal.ofReal (ε / 3 + ε / 3) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)

end HRS
