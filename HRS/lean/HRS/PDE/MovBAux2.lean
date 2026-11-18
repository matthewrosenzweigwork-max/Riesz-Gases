import HRS.PDE.MovBAux1
import HRS.Appendix.B15EAux7

/-!
# MOVB, part 2: bridges between the configuration language (`movT_Q`, `movT_srcReg`) and the D3 language on `𝕋^{Nd}`

* `movb_Q_eq_gibbs`: `Q^M_r = b15c_gibbsRefGen κ (U^M - κ ∑φ_r)` (the tilt makes `q^r = Q^M_r`).
* `movb_gibbs_eq`: `d1_gibbsMeasure κ (d3_tiltPot κ (b15d_U D M) (bigPsi φ_r)) = Q^M_r.map e`.
* `movb_source_eq`: `d3_source κ U ψ ψt r (e X) + ∫ ψt_r dq^r = movT_srcReg D N M ρ ρt r X`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem movb_smul_eq_of_prob {α : Type*} [MeasurableSpace α] {ν : Measure α} {c c' : ℝ≥0∞}
    (h : IsProbabilityMeasure (c • ν)) (h' : IsProbabilityMeasure (c' • ν)) : c • ν = c' • ν := by
  have h1 : c * ν univ = 1 := by
    have := h.measure_univ; rwa [Measure.smul_apply, smul_eq_mul] at this
  have h2 : c' * ν univ = 1 := by
    have := h'.measure_univ; rwa [Measure.smul_apply, smul_eq_mul] at this
  have hne0 : ν univ ≠ 0 := fun h0 => by simp [h0] at h1
  have hnet : ν univ ≠ ⊤ := fun ht => by
    by_cases hc : c = 0
    · simp [hc] at h1
    · simp [ht, hc] at h1
  have : c = c' := by
    have := h1.trans h2.symm
    exact (ENNReal.mul_left_inj hne0 hnet).1 this
  rw [this]

/-- The tilt makes the Gibbs measure of the one-body-tilted potential equal to `Q^M_r`. -/
theorem movb_Q_eq_gibbs (hN : 0 < N) (D : DynData d) (hκ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V) (M : ℝ)
    {ρ0 : Torus d → ℝ} (hdens : IsProbDensity ρ0) (hρc : Continuous ρ0) (hpos : ∀ x, 0 < ρ0 x)
    {φ : Torus d → ℝ} (hφc : Continuous φ)
    (hφeq : ∀ x, φ x = D.invβ⁻¹ * (D.V x + convFun (b15c_gReg d D.s M) ρ0 x) + Real.log (ρ0 x)) :
    modulatedGibbs (b15c_gReg d D.s M) N D.invβ⁻¹ (withDensityReal ρ0) =
      b15c_gibbsRefGen D.invβ (fun X : Config d N => b15c_potentialReg D M X - D.invβ * ∑ i, φ (X i)) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ0) := isProb_withDensityReal hdens
  have hgc : Continuous (b15c_gReg d D.s M) :=
    b15c_isSmooth_continuous (b15c_gReg_isSmooth (b15_one_le_d D) D.hs0 D.hsd M)
  have hVc := mova_continuous_of_isCk hV
  have hUc : Continuous (b15c_potentialReg (N := N) D M) := b15c_potentialReg_continuous D hVc M
  have hU'c : Continuous (fun X : Config d N => b15c_potentialReg D M X - D.invβ * ∑ i, φ (X i)) :=
    hUc.sub (continuous_const.mul (continuous_finset_sum _ fun i _ => hφc.comp (continuous_apply i)))
  have hQ : IsProbabilityMeasure
      (modulatedGibbs (b15c_gReg d D.s M) N D.invβ⁻¹ (withDensityReal ρ0)) :=
    modulatedGibbs_prob_of_continuous hgc _ _
  haveI hG := b15e_gibbsRefGen_isProb D.invβ hU'c
  set R : Config d N → ℝ≥0∞ := fun X => ∏ i, ENNReal.ofReal (ρ0 (X i)) with hR
  have hRm : Measurable R := Finset.measurable_prod _ fun i _ =>
    ENNReal.measurable_ofReal.comp (hdens.measurable.comp (measurable_pi_apply i))
  have hRlt : ∀ X, R X < ∞ := fun X => ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top
  set Wφ : Config d N → ℝ≥0∞ := fun X =>
    ENNReal.ofReal (Real.exp (-(D.invβ⁻¹ * b15c_potentialReg D M X) + ∑ i, φ (X i))) with hWφ
  set c3 : ℝ := Real.exp (-(D.invβ⁻¹ * N / 2) * mova_c3 (b15c_gReg d D.s M) (withDensityReal ρ0)) with hc3
  have hc3pos : 0 < c3 := Real.exp_pos _
  have hQeq : modulatedGibbs (b15c_gReg d D.s M) N D.invβ⁻¹ (withDensityReal ρ0) =
      ((ENNReal.ofReal (gibbsNormalizer (b15c_gReg d D.s M) N D.invβ⁻¹ (withDensityReal ρ0)))⁻¹ *
        ENNReal.ofReal c3) • (volume : Measure (Config d N)).withDensity Wφ := by
    unfold modulatedGibbs
    rw [pi_withDensityReal_eq ρ0 hdens.measurable, withDensity_withDensity_nonmeas _ hRm hRlt]
    have hRE : (R * fun X => ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
        modulatedEnergyKernel (b15c_gReg d D.s M) X (withDensityReal ρ0)))) =
        ENNReal.ofReal c3 • Wφ := by
      funext X
      have hRX : R X = ENNReal.ofReal (∏ i, ρ0 (X i)) := by
        rw [hR]; exact ENNReal.ofReal_prod_of_nonneg (fun i _ => (hpos _).le) |>.symm
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      rw [hRX, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => (hpos _).le),
        ← ENNReal.ofReal_mul hc3pos.le]
      congr 1
      rw [mul_comm (∏ i, ρ0 (X i))]
      exact mova_weight_eq hN D M hdens hpos hφeq X
    rw [hRE, withDensity_smul' _ _ ENNReal.ofReal_ne_top, smul_smul]
  have hGeq : b15c_gibbsRefGen D.invβ
      (fun X : Config d N => b15c_potentialReg D M X - D.invβ * ∑ i, φ (X i)) =
      (b15c_gibbsPartitionGen D.invβ
        (fun X : Config d N => b15c_potentialReg D M X - D.invβ * ∑ i, φ (X i)))⁻¹ •
        (volume : Measure (Config d N)).withDensity Wφ := by
    unfold b15c_gibbsRefGen
    congr 2
    funext X
    simp only [hWφ, b15c_gibbsWeightGen]
    congr 1
    have hne : D.invβ ≠ 0 := hκ.ne'
    field_simp
    ring
  rw [hGeq]
  rw [hQeq] at hQ ⊢
  rw [hGeq] at hG
  exact movb_smul_eq_of_prob hQ hG


theorem movb_gibbs_eq (hN : 0 < N) (D : DynData d) (hκ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V) (M : ℝ)
    {ρ0 : Torus d → ℝ} (hdens : IsProbDensity ρ0) (hρc : Continuous ρ0) (hpos : ∀ x, 0 < ρ0 x)
    {φ : Torus d → ℝ} (hφc : Continuous φ)
    (hφeq : ∀ x, φ x = D.invβ⁻¹ * (D.V x + convFun (b15c_gReg d D.s M) ρ0 x) + Real.log (ρ0 x)) :
    d1_gibbsMeasure D.invβ (d3_tiltPot D.invβ (b15d_U (N := N) D M) (mova_bigPsi (N := N) φ)) =
      (modulatedGibbs (b15c_gReg d D.s M) N D.invβ⁻¹ (withDensityReal ρ0)).map (d1_configEquiv d N) := by
  rw [movb_Q_eq_gibbs hN D hκ hV M hdens hρc hpos hφc hφeq, b15e_gibbsRefGen_map]
  congr 1

theorem movb_source_eq (hN : 0 < N) (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ))
    (hκ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V) (M : ℝ) {ρ ρt : ℝ → Torus d → ℝ} {r : ℝ}
    (hdens : IsProbDensity (ρ r)) (hρc : Continuous (ρ r)) (hpos : ∀ x, 0 < ρ r x)
    (hφ2 : Torus.IsCk 2 (movT_phi D M ρ r)) (X : Config d N) :
    d3_source D.invβ (b15d_U (N := N) D M) (fun r => mova_bigPsi (N := N) (movT_phi D M ρ r))
        (fun r => mova_bigPsi (N := N) (movT_phit D M ρ ρt r)) r (d1_configEquiv d N X) +
      ∫ y, mova_bigPsi (N := N) (movT_phit D M ρ ρt r) y
        ∂(d1_gibbsMeasure D.invβ (d3_tiltPot D.invβ (b15d_U (N := N) D M)
          (mova_bigPsi (N := N) (movT_phi D M ρ r)))) =
      movT_srcReg D N M ρ ρt r X := by
  have hφc := mova_continuous_of_isCk hφ2
  rw [movb_gibbs_eq hN D hκ hV M hdens hρc hpos hφc (fun x => rfl),
    integral_map_equiv]
  have hdrift : d1_gradDrift (b15d_U (N := N) D M) = d1_pushField (b15d_configDriftReg D M) :=
    funext fun x => (b15d_pushField_eq_gradDrift D hM hV M x).symm
  have hgen : d1_gen D.invβ (d1_gradDrift (b15d_U (N := N) D M)) (mova_bigPsi (N := N) (movT_phi D M ρ r))
      (d1_configEquiv d N X) = d1_configGen D.invβ (b15d_configDriftReg D M)
        (fun X => ∑ i, movT_phi D M ρ r (X i)) X := by
    rw [hdrift, d1_gen_config]
    congr 1
    funext Y
    exact mova_bigPsi_comp _ Y
  have hφ1 : Torus.IsCk 1 (movT_phi D M ρ r) := mova_isCk_one_of_two hφ2
  unfold d3_source movT_srcReg movT_psi movT_psit movT_Q
  beta_reduce
  rw [hgen, mova_bigPsi_grad_sq hφ1]
  simp only [mova_bigPsi_comp]

end HRS
