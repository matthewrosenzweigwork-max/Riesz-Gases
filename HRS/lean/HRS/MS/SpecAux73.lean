import HRS.MS.SpecAux72

/-!
# S8L: integrability on `V × V` for the Gaussian interpolation (S8.7, Gaussian log-Sobolev)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_int_gd`, `s8p_int_gd2`: integrability of `H · gd` and of
`H · gd ⊗ gd` for continuous `H` of linear (bilinear) growth; `s8p_H1`-`s8p_H4` are the four integrands that occur in the
integration by parts identity `s8p_KL` (next file), with growth bounds and integrability on `V × V`.
-/

noncomputable section

open MeasureTheory Real

namespace HRS.MS.Spec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Integrability of `H · gd` for continuous `H` of linear growth. -/
theorem s8p_int_gd {H : V → ℝ} (hH : Continuous H) {K : ℝ} (hb : ∀ x, |H x| ≤ K * (1 + ‖x‖)) :
    Integrable (fun x => H x * s8p_gd x) := by
  have h1 : Integrable (fun x : V => K * (s8p_gd x + ‖x‖ * s8p_gd x)) :=
    (s8p_gd_integrable.add s8p_gd_mul_norm_integrable).const_mul K
  refine Integrable.mono' h1 (hH.mul s8p_gd_continuous).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos x).le, Real.norm_eq_abs]
  calc |H x| * s8p_gd x ≤ K * (1 + ‖x‖) * s8p_gd x :=
        mul_le_mul_of_nonneg_right (hb x) (s8p_gd_pos x).le
    _ = K * (s8p_gd x + ‖x‖ * s8p_gd x) := by ring

/-- Integrability on the product of `H · gd ⊗ gd` for continuous `H` of bilinear growth. -/
theorem s8p_int_gd2 {H : V × V → ℝ} (hH : Continuous H) {K : ℝ}
    (hb : ∀ p, |H p| ≤ K * ((1 + ‖p.1‖) * (1 + ‖p.2‖))) :
    Integrable (fun p : V × V => H p * s8p_gd p.1 * s8p_gd p.2) (volume.prod volume) := by
  have h0 : Integrable (fun x : V => (1 + ‖x‖) * s8p_gd x) := by
    refine (s8p_gd_integrable.add s8p_gd_mul_norm_integrable).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]; ring
  have h1 := (h0.mul_prod h0).const_mul K
  refine Integrable.mono' h1 ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact ((hH.mul (s8p_gd_continuous.comp continuous_fst)).mul
      (s8p_gd_continuous.comp continuous_snd)).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Real.norm_of_nonneg (s8p_gd_pos p.1).le,
      Real.norm_of_nonneg (s8p_gd_pos p.2).le, Real.norm_eq_abs]
    have h2 := (s8p_gd_pos p.1).le
    have h3 := (s8p_gd_pos p.2).le
    calc |H p| * s8p_gd p.1 * s8p_gd p.2 ≤ K * ((1 + ‖p.1‖) * (1 + ‖p.2‖)) * s8p_gd p.1 * s8p_gd p.2 := by
          apply mul_le_mul_of_nonneg_right _ h3
          exact mul_le_mul_of_nonneg_right (hb p) h2
      _ = K * (((1 + ‖p.1‖) * s8p_gd p.1) * ((1 + ‖p.2‖) * s8p_gd p.2)) := by ring


section KL

variable {f ψ : V → ℝ} {M0 M1 B0 B1 : ℝ}

/-- The four integrands (all of the form `H p * gd p.1 * gd p.2`). -/
def s8p_H1 (f ψ : V → ℝ) (θ : ℝ) (p : V × V) : ℝ :=
  ψ p.1 * (Real.cos θ * fderiv ℝ f (Real.cos θ • p.1 + Real.sin θ • p.2) p.2)

def s8p_H2 (f ψ : V → ℝ) (θ : ℝ) (p : V × V) : ℝ :=
  ψ p.1 * (Real.sin θ * fderiv ℝ f (Real.cos θ • p.1 + Real.sin θ • p.2) p.1)

def s8p_H3 (f ψ : V → ℝ) (θ : ℝ) (p : V × V) : ℝ :=
  fderiv ℝ ψ p.1 p.2 * f (Real.cos θ • p.1 + Real.sin θ • p.2)

def s8p_H4 (f ψ : V → ℝ) (θ : ℝ) (p : V × V) : ℝ :=
  ψ p.1 * inner ℝ p.1 p.2 * f (Real.cos θ • p.1 + Real.sin θ • p.2)

theorem s8p_clm_le (L : V →L[ℝ] ℝ) (v : V) : |L v| ≤ ‖L‖ * ‖v‖ := by
  simpa [Real.norm_eq_abs] using L.le_opNorm v

theorem s8p_prod_bd (x y : V) : ‖x‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) ∧ ‖y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) ∧
    ‖x‖ * ‖y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
  have := norm_nonneg x; have := norm_nonneg y
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem s8p_H_cont (hf : S8pBdd f M0 M1) (hψ : S8pBdd ψ B0 B1) (θ : ℝ) :
    Continuous (s8p_H1 f ψ θ) ∧ Continuous (s8p_H2 f ψ θ) ∧ Continuous (s8p_H3 f ψ θ) ∧
      Continuous (s8p_H4 f ψ θ) := by
  have hQ : Continuous fun p : V × V => f (Real.cos θ • p.1 + Real.sin θ • p.2) :=
    hf.cont'.comp (by fun_prop)
  have hK : Continuous fun p : V × V => fderiv ℝ f (Real.cos θ • p.1 + Real.sin θ • p.2) :=
    (hf.cont.continuous_fderiv one_ne_zero).comp (by fun_prop)
  have hD : Continuous fun p : V × V => fderiv ℝ ψ p.1 :=
    (hψ.cont.continuous_fderiv one_ne_zero).comp continuous_fst
  have hp : Continuous fun p : V × V => ψ p.1 := hψ.cont'.comp continuous_fst
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold s8p_H1
    exact hp.mul (continuous_const.mul (hK.clm_apply continuous_snd))
  · unfold s8p_H2
    exact hp.mul (continuous_const.mul (hK.clm_apply continuous_fst))
  · unfold s8p_H3
    exact (hD.clm_apply continuous_snd).mul hQ
  · unfold s8p_H4
    exact (hp.mul (continuous_fst.inner continuous_snd)).mul hQ

theorem s8p_H_bd (hf : S8pBdd f M0 M1) (hψ : S8pBdd ψ B0 B1) (θ : ℝ) (p : V × V) :
    |s8p_H1 f ψ θ p| ≤ (B0 * M1 + B1 * M0 + B0 * M0) * ((1 + ‖p.1‖) * (1 + ‖p.2‖)) ∧
    |s8p_H2 f ψ θ p| ≤ (B0 * M1 + B1 * M0 + B0 * M0) * ((1 + ‖p.1‖) * (1 + ‖p.2‖)) ∧
    |s8p_H3 f ψ θ p| ≤ (B0 * M1 + B1 * M0 + B0 * M0) * ((1 + ‖p.1‖) * (1 + ‖p.2‖)) ∧
    |s8p_H4 f ψ θ p| ≤ (B0 * M1 + B1 * M0 + B0 * M0) * ((1 + ‖p.1‖) * (1 + ‖p.2‖)) := by
  obtain ⟨h1, h2, h3⟩ := s8p_prod_bd p.1 p.2
  have hB0 : 0 ≤ B0 := (abs_nonneg _).trans (hψ.bd0 0)
  have hB1 : 0 ≤ B1 := (norm_nonneg _).trans (hψ.bd1 0)
  have hM0 := hf.M0_nonneg
  have hM1 := hf.M1_nonneg
  have hc := Real.abs_cos_le_one θ
  have hs := Real.abs_sin_le_one θ
  have hψp := hψ.bd0 p.1
  have hQ := hf.bd0 (Real.cos θ • p.1 + Real.sin θ • p.2)
  have hKy := s8p_clm_le (fderiv ℝ f (Real.cos θ • p.1 + Real.sin θ • p.2)) p.2
  have hKx := s8p_clm_le (fderiv ℝ f (Real.cos θ • p.1 + Real.sin θ • p.2)) p.1
  have hK1 := hf.bd1 (Real.cos θ • p.1 + Real.sin θ • p.2)
  have hDy := s8p_clm_le (fderiv ℝ ψ p.1) p.2
  have hD1 := hψ.bd1 p.1
  have hin : |inner ℝ p.1 p.2| ≤ ‖p.1‖ * ‖p.2‖ := by
    simpa [Real.norm_eq_abs] using abs_real_inner_le_norm p.1 p.2
  have hab : 0 ≤ (1 + ‖p.1‖) * (1 + ‖p.2‖) := by positivity
  have e1 : |s8p_H1 f ψ θ p| ≤ B0 * M1 * ((1 + ‖p.1‖) * (1 + ‖p.2‖)) := by
    unfold s8p_H1
    rw [abs_mul, abs_mul]
    calc _ ≤ B0 * (1 * (M1 * ‖p.2‖)) := by
          apply mul_le_mul hψp (mul_le_mul hc (hKy.trans (mul_le_mul_of_nonneg_right hK1 (norm_nonneg _))) (abs_nonneg _) zero_le_one) (by positivity) hB0
      _ ≤ B0 * M1 * ((1 + ‖p.1‖) * (1 + ‖p.2‖)) := by nlinarith [mul_nonneg hB0 hM1]
  have e2 : |s8p_H2 f ψ θ p| ≤ B0 * M1 * ((1 + ‖p.1‖) * (1 + ‖p.2‖)) := by
    unfold s8p_H2
    rw [abs_mul, abs_mul]
    calc _ ≤ B0 * (1 * (M1 * ‖p.1‖)) := by
          apply mul_le_mul hψp (mul_le_mul hs (hKx.trans (mul_le_mul_of_nonneg_right hK1 (norm_nonneg _))) (abs_nonneg _) zero_le_one) (by positivity) hB0
      _ ≤ B0 * M1 * ((1 + ‖p.1‖) * (1 + ‖p.2‖)) := by nlinarith [mul_nonneg hB0 hM1]
  have e3 : |s8p_H3 f ψ θ p| ≤ B1 * M0 * ((1 + ‖p.1‖) * (1 + ‖p.2‖)) := by
    unfold s8p_H3
    rw [abs_mul]
    calc _ ≤ (B1 * ‖p.2‖) * M0 :=
          mul_le_mul (hDy.trans (mul_le_mul_of_nonneg_right hD1 (norm_nonneg _))) hQ (abs_nonneg _) (by positivity)
      _ ≤ B1 * M0 * ((1 + ‖p.1‖) * (1 + ‖p.2‖)) := by nlinarith [mul_nonneg hB1 hM0]
  have e4 : |s8p_H4 f ψ θ p| ≤ B0 * M0 * ((1 + ‖p.1‖) * (1 + ‖p.2‖)) := by
    unfold s8p_H4
    rw [abs_mul, abs_mul]
    calc _ ≤ (B0 * (‖p.1‖ * ‖p.2‖)) * M0 :=
          mul_le_mul (mul_le_mul hψp hin (abs_nonneg _) hB0) hQ (abs_nonneg _) (by positivity)
      _ ≤ B0 * M0 * ((1 + ‖p.1‖) * (1 + ‖p.2‖)) := by nlinarith [mul_nonneg hB0 hM0]
  have := mul_nonneg hB0 hM1; have := mul_nonneg hB1 hM0; have := mul_nonneg hB0 hM0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem s8p_H_int (hf : S8pBdd f M0 M1) (hψ : S8pBdd ψ B0 B1) (θ : ℝ) :
    Integrable (fun p : V × V => s8p_H1 f ψ θ p * s8p_gd p.1 * s8p_gd p.2) (volume.prod volume) ∧
    Integrable (fun p : V × V => s8p_H2 f ψ θ p * s8p_gd p.1 * s8p_gd p.2) (volume.prod volume) ∧
    Integrable (fun p : V × V => s8p_H3 f ψ θ p * s8p_gd p.1 * s8p_gd p.2) (volume.prod volume) ∧
    Integrable (fun p : V × V => s8p_H4 f ψ θ p * s8p_gd p.1 * s8p_gd p.2) (volume.prod volume) := by
  obtain ⟨c1, c2, c3, c4⟩ := s8p_H_cont hf hψ θ
  exact ⟨s8p_int_gd2 c1 (fun p => (s8p_H_bd hf hψ θ p).1), s8p_int_gd2 c2 (fun p => (s8p_H_bd hf hψ θ p).2.1),
    s8p_int_gd2 c3 (fun p => (s8p_H_bd hf hψ θ p).2.2.1),
    s8p_int_gd2 c4 (fun p => (s8p_H_bd hf hψ θ p).2.2.2)⟩

end KL

end HRS.MS.Spec
