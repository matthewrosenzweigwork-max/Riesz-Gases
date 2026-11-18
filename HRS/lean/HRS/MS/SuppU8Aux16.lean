import HRS.MS.SuppU8Aux15

/-!
# Worker U8 aux 16: the core theorem
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace HRS.U8

variable {d : ℕ}

theorem u8_rpow_le_one (z : ℝ) (hz : 0 ≤ z) (e : ℝ) (he : 0 ≤ e) : (1 + z) ^ (-e) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)

theorem u8_core (hd : 1 ≤ d) (α b : ℝ) (hα : 0 < α) (hb : 0 < b) (hbd : b < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : EuclideanSpace ℝ (Fin d) → ℝ) (B : ℝ), 0 ≤ B →
      ContDiff ℝ ((⌊α⌋₊ + 1 : ℕ) : WithTop ℕ∞) v →
      (∀ z, |v z| ≤ B * (1 + ‖z‖) ^ (-b)) →
      (∀ z, ‖iteratedFDeriv ℝ (⌊α⌋₊ + 1) v z‖ ≤ B * (1 + ‖z‖) ^ (-(b + ((⌊α⌋₊ + 1 : ℕ) : ℝ)))) →
      ∃ w : EuclideanSpace ℝ (Fin d) → ℝ, AEStronglyMeasurable w ∧
        (∀ x, |w x| ≤ C * B * (1 + ‖x‖) ^ (-(b + α))) ∧
        ∀ φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ,
          Integrable (fun x => ((v x : ℝ) : ℂ) *
            (𝓕⁻ (fun ξ : EuclideanSpace ℝ (Fin d) =>
              (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ)) x) ∧
          Integrable (fun x => ((w x : ℝ) : ℂ) * φ x) ∧
          ∫ x, ((v x : ℝ) : ℂ) *
              (𝓕⁻ (fun ξ : EuclideanSpace ℝ (Fin d) =>
                (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x) =
            ∫ x, ((w x : ℝ) : ℂ) * φ x := by
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, ℓ = ⌊α⌋₊ + 1 := ⟨_, rfl⟩
  rw [← hℓ]
  have hαℓ : α < ℓ := by rw [hℓ]; exact_mod_cast Nat.lt_floor_add_one α
  have hm : 1 ≤ ℓ := by omega
  have hαm : α < 2 * (ℓ : ℝ) := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hm
    linarith
  obtain ⟨M, hM0, hM⟩ := u8_sym_eq hd ℓ hm α hα hαm
  obtain ⟨C1, hC1nn, hC1⟩ := u8_pointwise hd α b hα hb hbd ℓ ℓ hm hαℓ (by omega)
  obtain ⟨b2, hb2, hb2d, hb2α⟩ := u8_d_param hd α hα
  obtain ⟨C2, hC2nn, hC2⟩ := u8_pointwise hd α b2 hα hb2 hb2d ℓ ℓ hm hαℓ (by omega)
  refine ⟨C1 / M, by positivity, ?_⟩
  intro v B hB hv hv0 hv1
  obtain ⟨I, hI⟩ : ∃ I : EuclideanSpace ℝ (Fin d) → ℝ, I = fun x =>
      ∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L ℓ y) v x := ⟨_, rfl⟩
  have hv0' : ∀ z, ‖v z‖ ≤ B * (1 + ‖z‖) ^ (-b) := fun z => by
    rw [Real.norm_eq_abs]; exact hv0 z
  have hPv : ∀ x, Integrable (fun y => ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L ℓ y) v x) ∧
      ∫ y, ‖‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L ℓ y) v x‖ ≤
        C1 * B * (1 + ‖x‖) ^ (-(b + α)) ∧ |I x| ≤ C1 * B * (1 + ‖x‖) ^ (-(b + α)) := by
    intro x
    obtain ⟨h1, h2, h3⟩ := hC1 ℝ v B hB hv hv0' hv1 x
    exact ⟨h1, h2, by rw [hI]; simpa using h3⟩
  have hwm : AEStronglyMeasurable (fun x => M⁻¹ * I x) := by
    rw [hI]
    exact (u8_Lam_aesm ℓ α v hv.continuous).const_mul M⁻¹
  have hwb : ∀ x, |M⁻¹ * I x| ≤ C1 / M * B * (1 + ‖x‖) ^ (-(b + α)) := by
    intro x
    rw [abs_mul, abs_of_pos (inv_pos.2 hM0)]
    calc M⁻¹ * |I x| ≤ M⁻¹ * (C1 * B * (1 + ‖x‖) ^ (-(b + α))) :=
          mul_le_mul_of_nonneg_left (hPv x).2.2 (inv_nonneg.2 hM0.le)
      _ = C1 / M * B * (1 + ‖x‖) ^ (-(b + α)) := by ring
  refine ⟨fun x => M⁻¹ * I x, hwm, hwb, ?_⟩
  · intro φ
    obtain ⟨vC, hvC⟩ : ∃ vC : EuclideanSpace ℝ (Fin d) → ℂ, vC = fun x => ((v x : ℝ) : ℂ) :=
      ⟨_, rfl⟩
    have e : ∀ x, ((v x : ℝ) : ℂ) = vC x := fun x => by rw [hvC]
    simp only [e]
    have hvCc : Continuous vC := by
      rw [hvC]; exact Complex.continuous_ofReal.comp hv.continuous
    have hvCs : ContDiff ℝ ℓ vC := by
      rw [hvC]; exact Complex.ofRealCLM.contDiff.comp hv
    have hvC0 : ∀ z, ‖vC z‖ ≤ B * (1 + ‖z‖) ^ (-b) := by
      intro z; rw [hvC]; simpa using hv0 z
    have hvC1 : ∀ z, ‖iteratedFDeriv ℝ ℓ vC z‖ ≤ B * (1 + ‖z‖) ^ (-(b + (ℓ : ℝ))) := by
      intro z
      have := LinearIsometry.norm_iteratedFDeriv_comp_left Complex.ofRealLI
        (hv.contDiffAt (x := z)) (i := ℓ) le_rfl
      have e2 : vC = ⇑Complex.ofRealLI ∘ v := by rw [hvC]; rfl
      rw [e2, this]; exact hv1 z
    have hvCb : ∀ x, ‖vC x‖ ≤ B := fun x =>
      (hvC0 x).trans (mul_le_of_le_one_right hB (u8_rpow_le_one _ (norm_nonneg x) b hb.le))
    have hPv := fun x => hC1 ℂ vC B hB hvCs hvC0 hvC1 x
    obtain ⟨Bφ, hBφ, hφ0, hφ1⟩ := u8_schwartz_bounds φ ℓ b2 hb2.le
    have hφs : ContDiff ℝ ℓ (⇑φ) := by exact_mod_cast φ.smooth ℓ
    have hPφ := fun x => hC2 ℂ (⇑φ) Bφ hBφ hφs hφ0 hφ1 x
    have hdual := u8_duality hd ℓ α (⇑φ) vC φ.continuous φ.integrable hvCc B hvCb (b2 + α)
      (C2 * Bφ) (C1 * B) hb2α (fun x => (hPφ x).1) (fun x => (hPφ x).2.1)
      (fun x => (hPv x).1) (fun x => (hPv x).2.1.trans
        (mul_le_of_le_one_right (by positivity) (u8_rpow_le_one _ (norm_nonneg x) _ (by positivity))))
    have hLam : ∀ x, ∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L ℓ y) vC x = ((I x : ℝ) : ℂ) := by
      intro x
      rw [hI]
      simp only
      rw [← integral_complex_ofReal]
      congr 1; funext y
      rw [hvC, u8_fd_ofReal, Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]
    have hΨ : ∀ x, 𝓕⁻ (fun ξ : EuclideanSpace ℝ (Fin d) =>
        (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x =
        ((M⁻¹ : ℝ) : ℂ) * ∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L ℓ y) (⇑φ) x := by
      intro x
      rw [u8_Lam_eq hd ℓ hm α hα hαm M hM φ x]
      have : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
      push_cast
      field_simp
    simp_rw [hΨ]
    refine ⟨?_, ?_, ?_⟩
    · have hmaj : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
          B * (C2 * Bφ) * (1 + ‖x‖) ^ (-(b2 + α))) :=
        (integrable_one_add_norm (by simpa using hb2α)).const_mul _
      have hint : Integrable (fun x => vC x * ∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L ℓ y) (⇑φ) x) := by
        refine Integrable.mono' hmaj (hvCc.aestronglyMeasurable.mul
          (u8_Lam_aesm ℓ α (⇑φ) φ.continuous)) (Filter.Eventually.of_forall (fun x => ?_))
        rw [norm_mul]
        calc ‖vC x‖ * ‖∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L ℓ y) (⇑φ) x‖
            ≤ B * (C2 * Bφ * (1 + ‖x‖) ^ (-(b2 + α))) :=
              mul_le_mul (hvCb x) (hPφ x).2.2 (norm_nonneg _) hB
          _ = B * (C2 * Bφ) * (1 + ‖x‖) ^ (-(b2 + α)) := by ring
      have := hint.const_mul ((M⁻¹ : ℝ) : ℂ)
      refine this.congr (Filter.Eventually.of_forall (fun x => ?_))
      simp only
      ring
    · show Integrable (fun x => (((M⁻¹ * I x : ℝ)) : ℂ) * φ x)
      have hwm' : AEStronglyMeasurable (fun x => (((M⁻¹ * I x : ℝ)) : ℂ)) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable hwm
      exact φ.integrable.bdd_mul (c := C1 / M * B) hwm' (Filter.Eventually.of_forall (fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (hwb x).trans (mul_le_of_le_one_right (by positivity)
          (u8_rpow_le_one _ (norm_nonneg x) _ (by positivity)))))
    · show ∫ x, vC x * (((M⁻¹ : ℝ) : ℂ) * ∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L ℓ y) (⇑φ) x) =
        ∫ x, (((M⁻¹ * I x : ℝ)) : ℂ) * φ x
      have h1 : ∀ x, vC x * (((M⁻¹ : ℝ) : ℂ) * ∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L ℓ y) (⇑φ) x)
          = ((M⁻¹ : ℝ) : ℂ) * (vC x * ∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L ℓ y) (⇑φ) x) :=
        fun x => by ring
      have h2 : ∀ x, (((M⁻¹ * I x : ℝ)) : ℂ) * φ x =
          ((M⁻¹ : ℝ) : ℂ) * ((∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L ℓ y) vC x) * φ x) := by
        intro x; rw [hLam]; push_cast; ring
      simp_rw [h1, h2]
      rw [integral_const_mul, integral_const_mul, hdual]

end HRS.U8
