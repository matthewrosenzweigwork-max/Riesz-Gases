import HRS.PDE.MovFAux2
import HRS.PDE.MovSXFinal

/-!
# MOVF Aux3: bridge C (initial `L^{p₀}` bound for `alltime_Lp`, `β₀ > 0`)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

/-- `ofReal (∫ e^{-bNF}) = ∫⁻ ...` for the singular Riesz energy. -/
theorem movf_ofReal_gibbsNormalizer (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : IsProbDensity ρ) (hc : Continuous ρ) (hN : 0 < N) {b : ℝ} (hb : 0 ≤ b) :
    ENNReal.ofReal (gibbsNormalizer (periodicRiesz d s) N b (withDensityReal ρ)) =
      ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-b * N *
        modulatedEnergy (fun x y => periodicRiesz d s (x - y) - 0 * (0 : ℝ)) X (withDensityReal ρ)))
          ∂(Measure.pi fun _ => withDensityReal ρ) := by
  haveI := isProb_withDensityReal hρ
  obtain ⟨hm, C, hC⟩ := movf_energy_facts hd hs0 hsd hρ hc hN (N := N)
  have hi : Integrable (fun X : Config d N => Real.exp (-b * N *
      modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)))
      (Measure.pi fun _ : Fin N => withDensityReal ρ) := by
    have := movf_exp_integrable (Measure.pi fun _ : Fin N => withDensityReal ρ)
      (F := fun X : Config d N => N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ))
      (measurable_const.mul hm) (c := N * C) (fun X => by
        have := hC X
        have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith) hb
    refine this.congr (Eventually.of_forall fun X => ?_)
    simp only; ring_nf
  unfold gibbsNormalizer
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => (Real.exp_pos _).le)]
  refine lintegral_congr fun X => ?_
  simp [modulatedEnergyKernel]

theorem movf_pressure_bounds (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {μ : Torus d → ℝ}
    (hμ : IsProbDensity μ) (hck : Torus.IsCk 2 μ) (hpos : ∀ x, 0 < μ x) {βm βp : ℝ} (hβm : 0 < βm) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ b ∈ Set.Icc βm βp,
      Real.exp (-(C * N * deltaN d s N)) ≤ gibbsNormalizer (periodicRiesz d s) N b (withDensityReal μ) ∧
      gibbsNormalizer (periodicRiesz d s) N b (withDensityReal μ) ≤ Real.exp (C * N * deltaN d s N) := by
  have hc : Continuous μ := mova_continuous_of_isCk hck
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  have hc₀ : 0 < μ x0 := hpos x0
  have hlow : ∀ x, μ x0 ≤ μ x := fun x => isMinOn_iff.1 hx0 x (Set.mem_univ x)
  obtain ⟨B0, hB0⟩ := periodicRiesz_ge_of_one_le (d := d) hd hs0 hsd
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + (B0 + 1) := fun z _ => by
    have := hB0 z; linarith
  obtain ⟨θ₀, C, hθ₀, hC0, H⟩ := movT_pressure_two_sided_C2_proof hd s hs0 hsd (B0 + 1) hw βm βp hβm
    (μ x0) hc₀ (Torus.cbNorm 2 μ) 0
  refine ⟨C, fun N hN b hb => ?_⟩
  have hb0 : 0 ≤ b := (hβm.trans_le hb.1).le
  have hN0 : 0 < N := by omega
  obtain ⟨h1, h2⟩ := H μ hμ hck hlow le_rfl (fun _ _ => 0) measurable_const (fun _ _ => rfl)
    (fun x y => by simp) N hN b hb 0 (by simp [hθ₀.le])
  rw [← movf_ofReal_gibbsNormalizer hd hs0 hsd hμ hc hN0 hb0] at h1 h2
  have hK : 0 < gibbsNormalizer (periodicRiesz d s) N b (withDensityReal μ) := by
    haveI := isProb_withDensityReal hμ
    obtain ⟨hm, Cc, hCc⟩ := movf_energy_facts hd hs0 hsd hμ hc hN0 (N := N)
    have := integral_exp_pos (μ := Measure.pi fun _ : Fin N => withDensityReal μ)
      (f := fun X : Config d N => -b * N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal μ))
      (by
        have := movf_exp_integrable (Measure.pi fun _ : Fin N => withDensityReal μ)
          (F := fun X : Config d N => N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal μ))
          (measurable_const.mul hm) (c := N * Cc) (fun X => by
            have := hCc X
            have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
            nlinarith) hb0
        refine this.congr (Eventually.of_forall fun X => ?_)
        simp only; ring_nf)
    exact this
  constructor
  · exact (ENNReal.ofReal_le_ofReal_iff hK.le).1 h1
  · exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 h2

theorem movf_gibbsNormalizer_eq (g : Torus d → ℝ) (N : ℕ) (b : ℝ) (μ : Measure (Torus d)) :
    gibbsNormalizer g N b μ =
      ∫ X : Config d N, Real.exp (-b * (N * modulatedEnergyKernel g X μ)) ∂(Measure.pi fun _ => μ) := by
  unfold gibbsNormalizer
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only; ring_nf

theorem movf_prepared_initial_Lp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {μ : Torus d → ℝ}
    (hμ : IsProbDensity μ) (hck : Torus.IsCk 2 μ) (hpos : ∀ x, 0 < μ x) {β₀ β p₀ : ℝ} (hβ₀ : 0 < β₀)
    (hβ : 0 < β) (hp₀ : 1 < p₀) (hcoef : 0 < p₀ * β₀ - (p₀ - 1) * β) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      modulatedGibbs (periodicRiesz d s) N β₀ (withDensityReal μ) ≪
        modulatedGibbs (periodicRiesz d s) N β (withDensityReal μ) ∧
      eLpNorm ((modulatedGibbs (periodicRiesz d s) N β₀ (withDensityReal μ)).rnDeriv
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal μ))) (ENNReal.ofReal p₀)
        (modulatedGibbs (periodicRiesz d s) N β (withDensityReal μ)) ≤
        ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  haveI := isProb_withDensityReal hμ
  have hc : Continuous μ := mova_continuous_of_isCk hck
  obtain ⟨C, hC⟩ := movf_pressure_bounds hd hs0 hsd hμ hck hpos
    (βm := min β₀ (min β (p₀ * β₀ - (p₀ - 1) * β)))
    (βp := max β₀ (max β (p₀ * β₀ - (p₀ - 1) * β))) (lt_min hβ₀ (lt_min hβ hcoef))
  refine ⟨2 * C, fun N hN => ?_⟩
  have hN0 : 0 < N := by omega
  obtain ⟨hm, Cc, hCc⟩ := movf_energy_facts hd hs0 hsd hμ hc hN0 (N := N)
  have hF : Measurable fun X : Config d N =>
      (N : ℝ) * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal μ) := measurable_const.mul hm
  have hcF : ∀ X : Config d N, -((N : ℝ) * Cc) ≤
      (N : ℝ) * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal μ) := fun X => by
    have := hCc X
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hQ : ∀ b : ℝ, 0 ≤ b → modulatedGibbs (periodicRiesz d s) N b (withDensityReal μ) =
      (Measure.pi fun _ : Fin N => withDensityReal μ).tilted (fun X : Config d N =>
        -b * ((N : ℝ) * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal μ))) := by
    intro b hb
    rw [movf_modGibbs_eq_tilted hd hs0 hsd hμ hc hN0 hb]
    congr 1
    funext X; ring
  rw [hQ β₀ hβ₀.le, hQ β hβ.le]
  obtain ⟨hac, hnorm⟩ := movf_lp_tilted (Measure.pi fun _ : Fin N => withDensityReal μ) hF hcF
    hβ₀.le hβ.le hp₀ (movf_exp_integrable _ hF hcF hcoef.le)
  refine ⟨hac, ?_⟩
  rw [hnorm]
  refine ENNReal.ofReal_le_ofReal ?_
  have hZ : ∀ b : ℝ, b = β₀ ∨ b = β ∨ b = p₀ * β₀ - (p₀ - 1) * β →
      Real.exp (-(C * N * deltaN d s N)) ≤ ∫ X : Config d N, Real.exp (-b * ((N : ℝ) *
        modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal μ))) ∂(Measure.pi fun _ => withDensityReal μ) ∧
      ∫ X : Config d N, Real.exp (-b * ((N : ℝ) * modulatedEnergyKernel (periodicRiesz d s) X
        (withDensityReal μ))) ∂(Measure.pi fun _ => withDensityReal μ) ≤ Real.exp (C * N * deltaN d s N) := by
    intro b hb
    have hbm : b ∈ Set.Icc (min β₀ (min β (p₀ * β₀ - (p₀ - 1) * β)))
        (max β₀ (max β (p₀ * β₀ - (p₀ - 1) * β))) := by
      rcases hb with rfl | rfl | rfl
      · exact ⟨min_le_left _ _, le_max_left _ _⟩
      · exact ⟨(min_le_right _ _).trans (min_le_left _ _), (le_max_left _ _).trans (le_max_right _ _)⟩
      · exact ⟨(min_le_right _ _).trans (min_le_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
    have := hC N hN b hbm
    rw [movf_gibbsNormalizer_eq] at this
    exact this
  set A := C * N * deltaN d s N with hA
  obtain ⟨hb1, hb2⟩ := hZ β (Or.inr (Or.inl rfl))
  obtain ⟨h01, h02⟩ := hZ β₀ (Or.inl rfl)
  obtain ⟨hg1, hg2⟩ := hZ _ (Or.inr (Or.inr rfl))
  set Zb := ∫ X : Config d N, Real.exp (-β * ((N : ℝ) *
        modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal μ))) ∂(Measure.pi fun _ => withDensityReal μ)
    with hZb
  set Z0 := ∫ X : Config d N, Real.exp (-β₀ * ((N : ℝ) *
        modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal μ))) ∂(Measure.pi fun _ => withDensityReal μ)
    with hZ0
  set Zg := ∫ X : Config d N, Real.exp (-(p₀ * β₀ - (p₀ - 1) * β) * ((N : ℝ) *
        modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal μ))) ∂(Measure.pi fun _ => withDensityReal μ)
    with hZg
  have hZbp : 0 < Zb := lt_of_lt_of_le (Real.exp_pos _) hb1
  have hZ0p : 0 < Z0 := lt_of_lt_of_le (Real.exp_pos _) h01
  have hZgp : 0 < Zg := lt_of_lt_of_le (Real.exp_pos _) hg1
  have hp0 : 0 < p₀ := by linarith
  have e1 : Zb ^ (p₀ - 1) ≤ Real.exp (A * (p₀ - 1)) := by
    rw [Real.exp_mul]; exact Real.rpow_le_rpow hZbp.le hb2 (by linarith)
  have e2 : Z0 ^ (-p₀) ≤ Real.exp (A * p₀) := by
    rw [Real.rpow_neg hZ0p.le, ← Real.inv_rpow hZ0p.le, Real.exp_mul]
    refine Real.rpow_le_rpow (inv_nonneg.2 hZ0p.le) ?_ hp0.le
    rw [inv_le_comm₀ hZ0p (Real.exp_pos _), ← Real.exp_neg]
    exact h01
  have e3 : Zb ^ (p₀ - 1) * Z0 ^ (-p₀) * Zg ≤ Real.exp (2 * p₀ * A) := by
    calc Zb ^ (p₀ - 1) * Z0 ^ (-p₀) * Zg ≤ Real.exp (A * (p₀ - 1)) * Real.exp (A * p₀) * Real.exp A := by
          gcongr
    _ = Real.exp (2 * p₀ * A) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc (Zb ^ (p₀ - 1) * Z0 ^ (-p₀) * Zg) ^ (1 / p₀) ≤ (Real.exp (2 * p₀ * A)) ^ (1 / p₀) :=
        Real.rpow_le_rpow (by positivity) e3 (by positivity)
    _ = Real.exp (2 * C * N * deltaN d s N) := by
        rw [← Real.exp_mul]; congr 1; rw [hA]; field_simp

end HRS

end
