import HRS.MC.SEdgeVocab
import HRS.MC.SEdgeB1
import HRS.MC.SEdgeB4b
import HRS.MC.SEdgeB5b
import HRS.MC.SEdgeB7
import HRS.MC.SEdgeB9sym
import HRS.MC.SEdgeB10a
import HRS.MC.SEdgeB10b
import HRS.MC.SEdgeB12

/-!
# Packet B13b: the linear statistic against `psi(W_N)` (relocated proof of `sed_B13b_linear_limit`)

From the centred Stein identity B5b (with the smooth data of B1 for `w`):
`E[Y_w psi(W_N)] = sum_c E[A_c d_c psi(W_N)] - beta N^{-1/2} E[B psi(W_N)]`.
Split `A_c = mu(A_c) + (A_c - mu(A_c))`; `mu(v_w . grad phi_c) = mu(w r_c)` (B9sym); the fluctuation is
`O(N^{-1/2})` in `L^1` (LLN, B10a's `b10_A_l1`), the `B` term is `O(N^{-1/2})` (`b10_B_l1`), and the
remaining main term converges by the CLT B10b applied to the bounded continuous `d_c psi`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B13b

open HRS.Sec7

section Aux

variable {p : ℕ}

theorem b13b_dpsi_cont {ψ : EuclideanSpace ℝ (Fin p) → ℝ} (hψ : MemCb 1 ψ) (c : Fin p) :
    Continuous (fun x => fderiv ℝ ψ x (stdVec c)) :=
  (hψ.1.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem b13b_dpsi_bdd {ψ : EuclideanSpace ℝ (Fin p) → ℝ} (hψ : MemCb 1 ψ) (c : Fin p) :
    ∃ M, ∀ x, |fderiv ℝ ψ x (stdVec c)| ≤ M := by
  obtain ⟨M, hM⟩ := hψ.2 1 le_rfl
  refine ⟨M, fun x => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ 1 ψ x‖ ≤ M := hM ⟨x, rfl⟩
  rw [norm_iteratedFDeriv_one] at h1
  have h2 := (fderiv ℝ ψ x).le_opNorm (stdVec c)
  rw [Real.norm_eq_abs] at h2
  have h3 : ‖stdVec (p := p) c‖ = 1 := by simp [stdVec]
  rw [h3, mul_one] at h2
  exact h2.trans h1

theorem b13b_psi_bdd {ψ : EuclideanSpace ℝ (Fin p) → ℝ} (hψ : MemCb 1 ψ) :
    ∃ M, ∀ x, |ψ x| ≤ M := by
  obtain ⟨M, hM⟩ := hψ.2 0 (Nat.zero_le _)
  refine ⟨M, fun x => ?_⟩
  have := hM ⟨x, rfl⟩
  simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this

end Aux

section Main

variable {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
  {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
include hd hs0 hs hβ hρ

theorem sed_B13b_linear_limit_proof {p : ℕ} {φ : Fin p → Torus d → ℝ}
    (hφ : ∀ a, Torus.IsSmooth (φ a))
    {w : Torus d → ℝ} (hw : Torus.IsSmooth w) {ψ : EuclideanSpace ℝ (Fin p) → ℝ}
    (hψ : MemCb 1 ψ) :
    Tendsto (fun N : ℕ => ∫ X, sed_Y (sed_Q d s N β ρ) w X *
        ψ (centeredStat (sed_Q d s N β ρ) φ X) ∂(sed_Q d s N β ρ)) atTop
      (𝓝 (∑ c, (∫ x, w x * responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ c) x
          ∂(withDensityReal ρ)) *
        ∫ z, fderiv ℝ ψ z (stdVec c) ∂(multivariateGaussian 0 (sed_Cmat d s β ρ φ)))) := by
  have hP : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  -- smooth data for `w` and for each `phi_c`
  obtain ⟨rw', vw, hrws, hvws, -, hrespw, -, hdivw⟩ :=
    HRS.MC.SEdge.B1.sed_B1_regular_proof hd hs0 hs hβ hρ hw
  choose rc vc hrcs hvcs hrcae hrespc hmeanc hdivc using
    fun c => HRS.MC.SEdge.B1.sed_B1_regular_proof hd hs0 hs hβ hρ (hφ c)
  have hint := (HRS.MC.SEdge.B4b.sed_B4b_energy_proof hd hs0 hs hβ hρ hvws).1
  -- the coefficients
  set m : Fin p → ℝ := fun c => ∫ x, sed_drift vw (φ c) x ∂(withDensityReal ρ) with hm
  have hmc : ∀ c, m c = ∫ x, w x * responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ c) x
      ∂(withDensityReal ρ) := by
    intro c
    obtain ⟨h1, h2⟩ := HRS.MC.SEdge.B9sym.sed_B9sym_response_proof hd hs0 hs hβ hρ hw (hφ c)
      hrws (hrcs c) hvws hdivw hrespw (hrespc c)
    show ∫ x, sed_drift vw (φ c) x ∂(withDensityReal ρ) = _
    rw [h1]
    have h3 : ∫ x, rw' x * φ c x ∂(withDensityReal ρ) = ∫ x, φ c x * rw' x ∂(withDensityReal ρ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    rw [h3, h2]
    refine integral_congr_ae ?_
    filter_upwards [hrcae c] with x hx
    rw [hx]
  simp_rw [← hmc]
  -- bounds
  choose KA hKA using fun c => HRS.MC.SEdge.B10a.b10_A_l1 hd hs0 hs hβ hρ hvws (hφ c)
  obtain ⟨KB, hKB⟩ := HRS.MC.SEdge.B10a.b10_B_l1 hd hs0 hs hβ hρ hvws
  choose M1 hM1 using fun c => b13b_dpsi_bdd hψ c
  obtain ⟨M0, hM0⟩ := b13b_psi_bdd hψ
  -- main term
  have hmain : Tendsto (fun N : ℕ => ∑ c, m c * ∫ X, fderiv ℝ ψ (centeredStat (sed_Q d s N β ρ) φ X)
        (stdVec c) ∂(sed_Q d s N β ρ)) atTop
      (𝓝 (∑ c, m c * ∫ z, fderiv ℝ ψ z (stdVec c)
        ∂(multivariateGaussian 0 (sed_Cmat d s β ρ φ)))) := by
    refine tendsto_finsetSum _ fun c _ => ?_
    exact (HRS.MC.SEdge.B10b.sed_B10b_clt_proof hd hs0 hs hβ hρ hφ (b13b_dpsi_cont hψ c)
      ⟨M1 c, hM1 c⟩).const_mul _
  -- error term
  set K : ℝ := ∑ c, max (M1 c) 0 * KA c + β * (max M0 0 * KB) with hK
  have herr : Tendsto (fun N : ℕ => ∫ X, sed_Y (sed_Q d s N β ρ) w X *
        ψ (centeredStat (sed_Q d s N β ρ) φ X) ∂(sed_Q d s N β ρ) -
      ∑ c, m c * ∫ X, fderiv ℝ ψ (centeredStat (sed_Q d s N β ρ) φ X)
        (stdVec c) ∂(sed_Q d s N β ρ)) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (g := fun N : ℕ => K / Real.sqrt N) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hQ : IsProbabilityMeasure (sed_Q d s N β ρ) :=
        HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hβ hρ N hN
      set Q := sed_Q d s N β ρ with hQdef
      have hWm : Measurable (centeredStat Q φ) :=
        HRS.MC.SEdge.B10b.b10b_meas hd hs0 hs hβ hρ hN hφ Q
      have hstein := HRS.MC.SEdge.B5b.sed_B5b_stein_centred_proof hd hs0 hs hβ hρ hN hrws hvws
        hdivw hrespw (hint N hN) hφ hψ
      rw [hstein, Real.norm_eq_abs]
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
      -- measurability / boundedness of the pieces
      have hg : ∀ c, Measurable (fun X => fderiv ℝ ψ (centeredStat Q φ X) (stdVec c)) :=
        fun c => (b13b_dpsi_cont hψ c).measurable.comp hWm
      have hgi : ∀ c, Integrable (fun X => fderiv ℝ ψ (centeredStat Q φ X) (stdVec c)) Q :=
        fun c => Integrable.of_bound (hg c).aestronglyMeasurable (M1 c)
          (Eventually.of_forall fun X => by simpa [Real.norm_eq_abs] using hM1 c _)
      have hAi : ∀ c, Integrable (fun X : Config d N => sed_A vw (φ c) X) Q := by
        intro c
        obtain ⟨hAm, MA, hMA⟩ := HRS.MC.SEdge.B12.b12_A_facts (N := N) hN hvws (hφ c)
        exact Integrable.of_bound hAm.aestronglyMeasurable MA
          (Eventually.of_forall fun X => by simpa [Real.norm_eq_abs] using hMA X)
      have hdiff : ∀ c, Integrable (fun X : Config d N => m c - sed_A vw (φ c) X) Q :=
        fun c => (integrable_const _).sub (hAi c)
      have hT1 : ∀ c, |∫ X, sed_A vw (φ c) X * fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) ∂Q -
            m c * ∫ X, fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) ∂Q| ≤
          max (M1 c) 0 * (KA c / Real.sqrt N) := by
        intro c
        have e : ∫ X, sed_A vw (φ c) X * fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) ∂Q -
            m c * ∫ X, fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) ∂Q =
            -∫ X, (m c - sed_A vw (φ c) X) * fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) ∂Q := by
          have : ∫ X, (m c - sed_A vw (φ c) X) * fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) ∂Q =
              m c * ∫ X, fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) ∂Q -
              ∫ X, sed_A vw (φ c) X * fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) ∂Q := by
            rw [← integral_const_mul, ← integral_sub]
            · refine integral_congr_ae (Eventually.of_forall fun X => ?_)
              ring
            · exact (hgi c).const_mul _
            · obtain ⟨hAm, MA, hMA⟩ := HRS.MC.SEdge.B12.b12_A_facts (N := N) hN hvws (hφ c)
              refine Integrable.of_bound (hAm.mul (hg c)).aestronglyMeasurable (MA * M1 c)
                (Eventually.of_forall fun X => ?_)
              rw [Real.norm_eq_abs, abs_mul]
              exact mul_le_mul (hMA X) (hM1 c _) (abs_nonneg _) ((abs_nonneg _).trans (hMA X))
          rw [this]; ring
        rw [e, abs_neg]
        refine (HRS.MC.SEdge.B10a.b10_wbound (G := fun X =>
          fderiv ℝ ψ (centeredStat Q φ X) (stdVec c)) (M := max (M1 c) 0) (hdiff c)
          (fun X => (hM1 c _).trans (le_max_left _ _))).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
        have := hKA c N hN
        exact this
      have hT2 : |β / Real.sqrt N * ∫ X, sed_B d s ρ β vw X * ψ (centeredStat Q φ X) ∂Q| ≤
          β / Real.sqrt N * (max M0 0 * KB) := by
        have hBi : Integrable (fun X : Config d N => sed_B d s ρ β vw X) Q := by
          unfold sed_B
          exact ((hint N hN).sub (integrable_const _)).const_mul _
        rw [abs_mul, abs_of_nonneg (div_nonneg hβ hsN.le)]
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hβ hsN.le)
        refine (HRS.MC.SEdge.B10a.b10_wbound (G := fun X => ψ (centeredStat Q φ X))
          (M := max M0 0) hBi (fun X => (hM0 _).trans (le_max_left _ _))).trans ?_
        exact mul_le_mul_of_nonneg_left (hKB N hN) (le_max_right _ _)
      have hsplit : ∑ c, ∫ X, sed_A vw (φ c) X * fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) ∂Q -
            β / Real.sqrt N * ∫ X, sed_B d s ρ β vw X * ψ (centeredStat Q φ X) ∂Q -
          ∑ c, m c * ∫ X, fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) ∂Q =
          ∑ c, (∫ X, sed_A vw (φ c) X * fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) ∂Q -
            m c * ∫ X, fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) ∂Q) -
          β / Real.sqrt N * ∫ X, sed_B d s ρ β vw X * ψ (centeredStat Q φ X) ∂Q := by
        rw [Finset.sum_sub_distrib]; ring
      rw [hsplit]
      calc _ ≤ |∑ c, (∫ X, sed_A vw (φ c) X * fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) ∂Q -
            m c * ∫ X, fderiv ℝ ψ (centeredStat Q φ X) (stdVec c) ∂Q)| +
          |β / Real.sqrt N * ∫ X, sed_B d s ρ β vw X * ψ (centeredStat Q φ X) ∂Q| :=
            abs_sub _ _
        _ ≤ ∑ c, max (M1 c) 0 * (KA c / Real.sqrt N) + β / Real.sqrt N * (max M0 0 * KB) := by
            refine add_le_add ?_ hT2
            exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => hT1 c)
        _ = K / Real.sqrt N := by
            have e1 : ∑ c, max (M1 c) 0 * (KA c / Real.sqrt N) =
                (∑ c, max (M1 c) 0 * KA c) / Real.sqrt N := by
              rw [Finset.sum_div]
              exact Finset.sum_congr rfl fun c _ => by ring
            rw [e1, hK]
            ring
    · refine tendsto_const_nhds.div_atTop ?_
      exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have := hmain.add herr
  simp only [add_zero] at this
  refine this.congr fun N => ?_
  ring

end Main


end HRS.MC.SEdge.B13b
