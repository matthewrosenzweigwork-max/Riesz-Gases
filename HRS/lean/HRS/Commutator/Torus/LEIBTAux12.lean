import HRS.Commutator.Torus.LEIBTAux11

/-!
# LEIB-T helpers, part 12: the pointwise error bound for the Bessel derivative of a cut-off almost periodic function
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma leibt_fourier_inversion (χ : SchwartzMap 𝔼 ℂ) (z : 𝔼) :
    χ z = ∫ v : 𝔼, leibt_e z v * (𝓕 χ : SchwartzMap 𝔼 ℂ) v := by
  have h0 : (𝓕⁻ (𝓕 χ : SchwartzMap 𝔼 ℂ) : SchwartzMap 𝔼 ℂ) = χ := FourierTransform.fourierInv_fourier_eq χ
  have h : (𝓕⁻ (𝓕 χ : SchwartzMap 𝔼 ℂ) : SchwartzMap 𝔼 ℂ) z = χ z := by rw [h0]
  rw [← h, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  rw [leibt_e_comm z v]
  rfl

lemma leibt_invF_rho (α : ℝ) (ψ : SchwartzMap 𝔼 ℂ) (a : 𝔼) (t : ℝ) (w : 𝔼) :
    (𝓕⁻ (leibt_rho α ψ a t) : SchwartzMap 𝔼 ℂ) w =
      ∫ ζ : 𝔼, leibt_e w ζ * (leibt_theta α a t ζ * ψ ζ) := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  rw [leibt_e_comm w v, leibt_rho_apply]
  rfl

lemma leibt_error_bound (α : ℝ) (χ : SchwartzMap 𝔼 ℂ) (K : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ (c : Lattice d → ℂ) (lam : Lattice d → 𝔼)
      (hc : ∀ k : ℕ, Summable fun i => ‖c i‖ * (1 + ‖lam i‖) ^ k)
      (G W : 𝔼 → ℂ) (Wc : SchwartzMap 𝔼 ℂ) (hWc : ⇑Wc = W)
      (hG : ∀ y, HasSum (fun i => c i * leibt_m α (lam i) * leibt_e (lam i) y) (G y))
      {N : ℝ} (hN : 1 ≤ N)
      (hW : ∀ y, HasSum (fun i => c i * (leibt_e (lam i) y * χ (N⁻¹ • y))) (W y)) (x : 𝔼),
      ‖HRS.Commutator.Whole.XLI.Fm α Wc x - G x * χ (N⁻¹ • x)‖ ≤
        C * (∑' i, ‖c i‖ * (1 + ‖lam i‖) ^ k) * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹ := by
  obtain ⟨C, k, hC, hdec⟩ := leibt_rho_decay (d := d) α (𝓕 χ) K
  refine ⟨C, k, hC, fun c lam hc G W Wc hWc hG {N} hN hW x => ?_⟩
  have hN0 : 0 < N := by linarith
  have hNinv0 : 0 < N⁻¹ := inv_pos.2 hN0
  have hNinv1 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
  set ψ : SchwartzMap 𝔼 ℂ := 𝓕 χ with hψ
  have hW' : ∀ y, HasSum (fun i => c i * (leibt_e (lam i) y * χ (N⁻¹ • y))) (Wc y) := by
    intro y; rw [hWc]; exact hW y
  have hA := leibt_series_bessel α χ hN c lam hc Wc hW' x
  have hB : HasSum (fun i => c i * leibt_m α (lam i) * leibt_e (lam i) x * χ (N⁻¹ • x)) (G x * χ (N⁻¹ • x)) :=
    (hG x).mul_right _
  have hD := hA.sub hB
  obtain ⟨B, k₀, hB0, hsh⟩ := leibt_shift_bound (d := d) α ψ
  -- termwise identification
  have hterm : ∀ i, c i * (leibt_e (lam i) x * leibt_Phi α ψ N (lam i) x) -
      c i * leibt_m α (lam i) * leibt_e (lam i) x * χ (N⁻¹ • x) =
      c i * leibt_e (lam i) x * (𝓕⁻ (leibt_rho α ψ (lam i) N⁻¹) : SchwartzMap 𝔼 ℂ) (N⁻¹ • x) := by
    intro i
    rw [leibt_invF_rho]
    have hint1 : Integrable (fun ζ : 𝔼 => leibt_e (N⁻¹ • x) ζ * (leibt_m α (lam i + N⁻¹ • ζ) * ψ ζ)) := by
      have h1 := (hsh N hN (lam i)).1
      refine (h1.norm).mono' ?_ (Filter.Eventually.of_forall fun ζ => ?_)
      · have := leibt_continuous_e (N⁻¹ • x)
        have hm := (HRS.Commutator.Whole.XLI.bsymX_temperate (d := d) α).1.continuous
        exact (this.mul ((hm.comp (continuous_const.add (continuous_const_smul _))).mul ψ.continuous)).aestronglyMeasurable
      · rw [norm_mul, leibt_norm_e, one_mul]
    have hint2 : Integrable (fun ζ : 𝔼 => leibt_m α (lam i) * (leibt_e (N⁻¹ • x) ζ * ψ ζ)) := by
      refine (((ψ.integrable.norm).const_mul ‖leibt_m α (lam i)‖)).mono' ?_ (Filter.Eventually.of_forall fun ζ => ?_)
      · have := leibt_continuous_e (N⁻¹ • x)
        exact (continuous_const.mul (this.mul ψ.continuous)).aestronglyMeasurable
      · rw [norm_mul, norm_mul, leibt_norm_e, one_mul]
    have e1 : ∫ ζ : 𝔼, leibt_e (N⁻¹ • x) ζ * (leibt_theta α (lam i) N⁻¹ ζ * ψ ζ) =
        leibt_Phi α ψ N (lam i) x - leibt_m α (lam i) * χ (N⁻¹ • x) := by
      unfold leibt_Phi
      have hpt : ∀ ζ : 𝔼, leibt_e (N⁻¹ • x) ζ * (leibt_theta α (lam i) N⁻¹ ζ * ψ ζ) =
          leibt_e (N⁻¹ • x) ζ * (leibt_m α (lam i + N⁻¹ • ζ) * ψ ζ) -
            leibt_m α (lam i) * (leibt_e (N⁻¹ • x) ζ * ψ ζ) := by
        intro ζ; simp only [leibt_theta]; ring
      simp_rw [hpt]
      rw [integral_sub hint1 hint2, integral_const_mul, ← leibt_fourier_inversion χ (N⁻¹ • x)]
    rw [e1]
    ring
  have hbound : ∀ i, ‖c i * (leibt_e (lam i) x * leibt_Phi α ψ N (lam i) x) -
      c i * leibt_m α (lam i) * leibt_e (lam i) x * χ (N⁻¹ • x)‖ ≤
      ‖c i‖ * (1 + ‖lam i‖) ^ k * (C * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹) := by
    intro i
    rw [hterm, norm_mul, norm_mul, leibt_norm_e, mul_one]
    have h1 := hdec (lam i) N⁻¹ hNinv0 hNinv1 (N⁻¹ • x)
    have hpos : 0 < (1 + ‖N⁻¹ • x‖) ^ K := by positivity
    have h2 : ‖(𝓕⁻ (leibt_rho α ψ (lam i) N⁻¹) : SchwartzMap 𝔼 ℂ) (N⁻¹ • x)‖ ≤
        C * N⁻¹ * (1 + ‖lam i‖) ^ k * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹ := by
      rw [← mul_le_mul_iff_of_pos_left hpos]
      calc (1 + ‖N⁻¹ • x‖) ^ K * ‖(𝓕⁻ (leibt_rho α ψ (lam i) N⁻¹) : SchwartzMap 𝔼 ℂ) (N⁻¹ • x)‖
          ≤ C * N⁻¹ * (1 + ‖lam i‖) ^ k := h1
        _ = (1 + ‖N⁻¹ • x‖) ^ K * (C * N⁻¹ * (1 + ‖lam i‖) ^ k * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹) := by
          field_simp
    calc ‖c i‖ * ‖(𝓕⁻ (leibt_rho α ψ (lam i) N⁻¹) : SchwartzMap 𝔼 ℂ) (N⁻¹ • x)‖
        ≤ ‖c i‖ * (C * N⁻¹ * (1 + ‖lam i‖) ^ k * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹) := by gcongr
      _ = _ := by ring
  have hsumk : HasSum (fun i => ‖c i‖ * (1 + ‖lam i‖) ^ k * (C * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹))
      ((∑' i, ‖c i‖ * (1 + ‖lam i‖) ^ k) * (C * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹)) :=
    (hc k).hasSum.mul_right _
  have := hD.norm_le_of_bounded hsumk hbound
  calc ‖HRS.Commutator.Whole.XLI.Fm α Wc x - G x * χ (N⁻¹ • x)‖
      ≤ (∑' i, ‖c i‖ * (1 + ‖lam i‖) ^ k) * (C * N⁻¹ * ((1 + ‖N⁻¹ • x‖) ^ K)⁻¹) := this
    _ = _ := by ring

end HRS.Commutator.TorusNote
