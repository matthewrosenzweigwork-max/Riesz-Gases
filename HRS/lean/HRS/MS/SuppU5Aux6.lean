import Mathlib
import HRS.MS.SuppU5Aux5

/-!
# Packet U5 (aux 6): the abstract Hilbert-space assembly
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix

noncomputable section

namespace HRS.U5

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- `W_1 ≤ E‖Z - W‖` for two random elements on one probability space. -/
lemma u5_w1_le_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z W : Ω → E} (hZ : Measurable Z) (hW : Measurable W) (hi : Integrable (fun ω => ‖Z ω - W ω‖) P) :
    wassersteinE 1 (P.map Z) (P.map W) ≤ ENNReal.ofReal (∫ ω, ‖Z ω - W ω‖ ∂P) := by
  refine (wassersteinE_le_of_coupling P 1 le_rfl Z W hZ.aemeasurable hW.aemeasurable).trans ?_
  simp only [Real.rpow_one, div_one, ENNReal.rpow_one]
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => norm_nonneg _)]

/-- Second moments by monotone truncation. -/
lemma u5_lintegral_sq_le {g : ℕ → E}
    (hpar : ∀ x, HasSum (fun n => (⟪g n, x⟫) ^ 2) (‖x‖ ^ 2))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {F : Ω → E} (hF : Measurable F) {c : ℝ}
    (hc : ∀ L : ℕ, ∫⁻ ζ, ENNReal.ofReal (‖u5_tau g L (F ζ)‖ ^ 2) ∂P ≤ ENNReal.ofReal c) :
    ∫⁻ ζ, ‖F ζ‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal c := by
  have hmeas : ∀ L : ℕ, Measurable fun ζ => ENNReal.ofReal (‖u5_tau g L (F ζ)‖ ^ 2) := fun L =>
    ENNReal.measurable_ofReal.comp (((u5_tau g L).continuous.measurable.comp hF).norm.pow_const 2)
  have hlim := lintegral_tendsto_of_tendsto_of_monotone (μ := P)
    (f := fun L ζ => ENNReal.ofReal (‖u5_tau g L (F ζ)‖ ^ 2))
    (F := fun ζ => ‖F ζ‖ₑ ^ 2) (fun L => (hmeas L).aemeasurable)
    (ae_of_all _ fun ζ L M hLM => ENNReal.ofReal_le_ofReal (by
      have := (monotone_nat_of_le_succ fun L => u5_tau_sq_mono hpar L (F ζ)) hLM
      exact this))
    (ae_of_all _ fun ζ => by
      have h := ENNReal.tendsto_ofReal (u5_tau_sq_tendsto hpar (F ζ))
      have e : ENNReal.ofReal (‖F ζ‖ ^ 2) = ‖F ζ‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
      rwa [e] at h)
  exact le_of_tendsto' hlim hc


lemma u5_integrable_of_lintegral_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {F : Ω → E} (hF : Measurable F) {c : ℝ} (hc : ∫⁻ ζ, ‖F ζ‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal c) :
    Integrable (fun ζ => ‖F ζ‖) P := by
  have hmem : MemLp F 2 P := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    swap
    · exact hF.aestronglyMeasurable
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
    exact lt_of_le_of_lt hc ENNReal.ofReal_lt_top
  exact (hmem.integrable one_le_two).norm


lemma u5_approx_tendsto {g : ℕ → E} (hg0 : ∀ n, ‖g n‖ = 0 ∨ ‖g n‖ = 1)
    (hgo : ∀ m n, m ≠ n → ⟪g m, g n⟫ = 0) (hpar : ∀ x, HasSum (fun n => (⟪g n, x⟫) ^ 2) (‖x‖ ^ 2))
    {Ω₁ : Type*} [MeasurableSpace Ω₁] (Q : Measure Ω₁) [IsProbabilityMeasure Q]
    (F : Ω₁ → E) (hF : Measurable F) (hFi : Integrable (fun ζ => ‖F ζ‖) Q) :
    Tendsto (fun L => ∫ ζ, ‖F ζ - u5_iota g L (u5_tau g L (F ζ))‖ ∂Q) atTop (𝓝 0) := by
  have hιτm : ∀ L, Measurable fun (F : E) => u5_iota g L (u5_tau g L F) := fun L =>
    (u5_iota g L).continuous.measurable.comp (u5_tau g L).continuous.measurable
  have := tendsto_integral_of_dominated_convergence (μ := Q) (F := fun L ζ => ‖F ζ - u5_iota g L (u5_tau g L (F ζ))‖)
    (f := fun _ => (0 : ℝ)) (bound := fun ζ => 2 * ‖F ζ‖)
    (fun L => ((hF.sub ((hιτm L).comp hF)).norm).aestronglyMeasurable)
    (hFi.const_mul 2)
    (fun L => ae_of_all _ fun ζ => by
      rw [Real.norm_eq_abs, abs_norm]
      calc ‖F ζ - u5_iota g L (u5_tau g L (F ζ))‖ ≤ ‖F ζ‖ + ‖u5_iota g L (u5_tau g L (F ζ))‖ :=
            norm_sub_le _ _
        _ ≤ ‖F ζ‖ + ‖F ζ‖ := by
            gcongr; exact u5_iota_tau_norm_le hg0 hgo hpar L _
        _ = 2 * ‖F ζ‖ := by ring)
    (ae_of_all _ fun ζ => u5_sub_iota_tau_tendsto hg0 hgo hpar (F ζ))
  simpa using this

/-- The law of the coordinatewise image of a configuration. -/
lemma u5_law_vec {Ω : Type*} [MeasurableSpace Ω] {d N L : ℕ} (μ : Measure (Eu d)) [IsProbabilityMeasure μ]
    (P : Measure Ω) (X : Ω → Fin N → Eu d) (hX : Measurable X)
    (hXl : P.map X = Measure.pi fun _ : Fin N => μ) {f : Eu d → Ek L} (hf : Measurable f) :
    P.map (fun ζ i => f (X ζ i)) = Measure.pi fun _ : Fin N => μ.map f := by
  have hm : Measurable (fun (ω : Fin N → Eu d) (i : Fin N) => f (ω i)) :=
    Measurable.of_eval fun i => hf.comp (measurable_pi_apply i)
  have : (fun ζ i => f (X ζ i)) = (fun (ω : Fin N → Eu d) (i : Fin N) => f (ω i)) ∘ X := rfl
  rw [this, ← Measure.map_map hm hX, hXl, Measure.pi_map_pi (fun _ => hf.aemeasurable)]


set_option maxHeartbeats 1000000 in
/-- Second moment of the normalised sum of centred bounded i.i.d. vectors. -/
lemma u5_pi_lint {L N : ℕ} (hN : 1 ≤ N) (ρ : Measure (Ek L)) [IsProbabilityMeasure ρ] {b : ℝ}
    (hb : ∀ᵐ y ∂ρ, ‖y‖ ≤ b) (h0 : ∀ c, ∫ y, y c ∂ρ = 0) :
    ∫⁻ ω, ENNReal.ofReal (‖(Real.sqrt N)⁻¹ • ∑ i, ω i‖ ^ 2) ∂(Measure.pi fun _ : Fin N => ρ) =
      ENNReal.ofReal (∫ y, ‖y‖ ^ 2 ∂ρ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hs0 : 0 ≤ (Real.sqrt N)⁻¹ := inv_nonneg.2 hsqrt.le
  have hb0 : 0 ≤ b := by
    obtain ⟨y0, hy0⟩ := hb.exists
    exact (norm_nonneg _).trans hy0
  have hNs : (N : ℝ) * ((Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹) = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    field_simp
  have hmeas : Measurable fun ω : Fin N → Ek L => ‖(Real.sqrt N)⁻¹ • ∑ i, ω i‖ ^ 2 :=
    (((Finset.measurable_sum _ fun i _ => measurable_pi_apply i).const_smul (Real.sqrt N)⁻¹).norm).pow_const 2
  have hint : Integrable (fun ω : Fin N → Ek L => ‖(Real.sqrt N)⁻¹ • ∑ i, ω i‖ ^ 2)
      (Measure.pi fun _ : Fin N => ρ) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable (((Real.sqrt N)⁻¹ * (N * b)) ^ 2)
      ((u5_ae_pi (N := N) hb).mono fun ω hω => ?_)
    rw [Real.norm_eq_abs, abs_pow, abs_norm, norm_smul, Real.norm_of_nonneg hs0]
    refine pow_le_pow_left₀ ?_ ?_ 2
    · positivity
    · refine mul_le_mul_of_nonneg_left ?_ hs0
      calc ‖∑ i, ω i‖ ≤ ∑ i, ‖ω i‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin N, b := Finset.sum_le_sum fun i _ => hω i
        _ = N * b := by simp
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by positivity)]
  congr 1
  simp_rw [norm_smul, Real.norm_of_nonneg hs0, mul_pow]
  rw [integral_const_mul]
  have := u5_pi_sum_sq (N := N) ρ (fun y => y) measurable_id hb h0
  rw [this, ← mul_assoc, show (Real.sqrt N)⁻¹ ^ 2 * (N : ℝ) = 1 by nlinarith [hNs], one_mul]

lemma u5_gauss_lint {L : ℕ} (ρ : Measure (Ek L)) [IsProbabilityMeasure ρ]
    (h2 : Integrable (fun y : Ek L => ‖y‖ ^ 2) ρ) :
    ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 2) ∂(multivariateGaussian (0 : Ek L) (Yurinskii.momentMatrix ρ)) =
      ENNReal.ofReal (∫ y, ‖y‖ ^ 2 ∂ρ) := by
  have hQ := Yurinskii.momentMatrix_posSemidef ρ h2
  rw [← ofReal_integral_eq_lintegral_ofReal (Yurinskii.integrable_norm_pow_gauss 2 (by norm_num))
    (ae_of_all _ fun _ => by positivity), Yurinskii.integral_norm_sq_gauss hQ,
    Yurinskii.trace_momentMatrix ρ h2]

set_option maxHeartbeats 1000000 in
theorem u5_assembly {d N : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N) (μ : Measure (Eu d)) [IsProbabilityMeasure μ]
    {m₂ : ℝ} (hm2 : Integrable (fun x : Eu d => ‖x‖ ^ 2) μ) (hm : ∫ x, ‖x‖ ^ 2 ∂μ ≤ m₂)
    (Rm : Submodule ℝ E) (hRm : Rmᗮ = ⊥) (J : Eu d → E) (hJm : Measurable J) {b Λ : ℝ}
    (hb0 : 0 ≤ b) (hΛ0 : 0 ≤ Λ) (hb : ∀ x, ‖J x‖ ≤ b) (hΛ : ∀ x y, ‖J x - J y‖ ≤ Λ * ‖x - y‖)
    (hmean : ∀ w ∈ Rm, ∫ x, ⟪w, J x⟫ ∂μ = 0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Fin N → Eu d)
    (hX : Measurable X) (hXl : P.map X = Measure.pi fun _ : Fin N => μ)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (I : Ω' → E)
    (hI : Measurable I)
    (hIl : ∀ (L : ℕ) (w : Fin L → E), (∀ a, w a ∈ Rm) →
      P'.map (fun ζ => (WithLp.toLp 2 fun a => ⟪w a, I ζ⟫ : Ek L)) =
        multivariateGaussian 0 (Matrix.of fun a b => ∫ x, ⟪w a, J x⟫ * ⟪w b, J x⟫ ∂μ)) :
    (wassersteinE 1 (P.map fun ζ => (Real.sqrt N)⁻¹ • ∑ i, J (X ζ i)) (P'.map I) ≤
      ENNReal.ofReal (u5_C0 d m₂ * (Λ + b) * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))))) ∧
    (∫⁻ ζ, ‖(Real.sqrt N)⁻¹ • ∑ i, J (X ζ i)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (b ^ 2)) ∧
    (∫⁻ ζ, ‖I ζ‖ₑ ^ 2 ∂P' ≤ ENNReal.ofReal (b ^ 2)) := by
  obtain ⟨g, hgR, hg0, hgo, hpar⟩ := u5_orthoseq Rm hRm
  set s : ℝ := (Real.sqrt N)⁻¹ with hs
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hs0 : 0 ≤ s := inv_nonneg.2 hsqrt.le
  have hNs : (N : ℝ) * (s * s) = 1 := by
    rw [hs, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    field_simp
  set S₀ : Ω → E := fun ζ => s • ∑ i, J (X ζ i) with hS₀
  have hS₀m : Measurable S₀ :=
    (Finset.measurable_sum _ fun i _ => hJm.comp ((measurable_pi_apply i).comp hX)).const_smul s
  set JL : (L : ℕ) → Eu d → Ek L := fun L x => u5_tau g L (J x) with hJL
  have hJLm : ∀ L, Measurable (JL L) := fun L => (u5_tau g L).continuous.measurable.comp hJm
  have hJLb : ∀ L x, ‖JL L x‖ ≤ b := fun L x => (u5_tau_norm_le hpar L _).trans (hb x)
  have hJLL : ∀ L x y, ‖JL L x - JL L y‖ ≤ Λ * ‖x - y‖ := fun L x y => by
    rw [hJL]; simp only []; rw [← map_sub]; exact (u5_tau_norm_le hpar L _).trans (hΛ x y)
  have hJL0 : ∀ L (c : Fin L), ∫ x, JL L x c ∂μ = 0 := fun L c => by
    simp only [hJL, u5_tau_apply]
    exact hmean (g c) (hgR c)
  have hS0τ : ∀ ζ L, u5_tau g L (S₀ ζ) = s • ∑ i, JL L (X ζ i) := fun ζ L => by
    simp [hS₀, hJL, map_smul, map_sum]
  have hlawS : ∀ L, P.map (fun ζ => u5_tau g L (S₀ ζ)) =
      (Measure.pi fun _ : Fin N => μ.map (JL L)).map (fun ω => s • ∑ i, ω i) := fun L => by
    have hm1 : Measurable (fun (ω : Fin N → Ek L) => s • ∑ i, ω i) :=
      (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).const_smul s
    have hvm : Measurable (fun ζ (i : Fin N) => JL L (X ζ i)) :=
      Measurable.of_eval fun i => (hJLm L).comp ((measurable_pi_apply i).comp hX)
    rw [← u5_law_vec μ P X hX hXl (hJLm L), Measure.map_map hm1 hvm]
    congr 1
    ext ζ : 1
    simp [hS0τ]
  have hlawI : ∀ L, P'.map (fun ζ => u5_tau g L (I ζ)) =
      multivariateGaussian 0 (Yurinskii.momentMatrix (μ.map (JL L))) := fun L => by
    have h := hIl L (fun a : Fin L => g a) (fun a => hgR a)
    have e1 : (fun ζ => (WithLp.toLp 2 fun a : Fin L => ⟪g a, I ζ⟫ : Ek L)) =
        fun ζ => u5_tau g L (I ζ) := by
      ext ζ a; simp [u5_tau_apply]
    rw [e1] at h
    rw [h]
    congr 1
    ext a b
    simp only [Matrix.of_apply, Yurinskii.momentMatrix]
    rw [integral_map (hJLm L).aemeasurable (by fun_prop : Measurable fun y : Ek L => y a * y b).aestronglyMeasurable]
    simp [hJL, u5_tau_apply]
  -- the second moments
  have hρb : ∀ L, ∀ᵐ y ∂(μ.map (JL L)), ‖y‖ ≤ b := fun L => by
    rw [ae_map_iff (hJLm L).aemeasurable (measurableSet_le measurable_norm measurable_const)]
    exact ae_of_all _ (hJLb L)
  have hρ2 : ∀ L, Integrable (fun y : Ek L => ‖y‖ ^ 2) (μ.map (JL L)) := fun L => by
    refine Integrable.of_bound (measurable_norm.pow_const 2).aestronglyMeasurable (b ^ 2)
      ((hρb L).mono fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_pow, abs_norm]; exact pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hρm2 : ∀ L, ∫ y, ‖y‖ ^ 2 ∂(μ.map (JL L)) ≤ b ^ 2 := fun L => by
    calc ∫ y, ‖y‖ ^ 2 ∂(μ.map (JL L)) ≤ ∫ _y, b ^ 2 ∂(μ.map (JL L)) :=
          integral_mono_ae (hρ2 L) (integrable_const _) ((hρb L).mono fun y hy =>
            pow_le_pow_left₀ (norm_nonneg _) hy 2)
      _ = b ^ 2 := by simp
  have hρ0 : ∀ L (c : Fin L), ∫ y, y c ∂(μ.map (JL L)) = 0 := fun L c => by
    rw [integral_map (hJLm L).aemeasurable (by fun_prop : Measurable fun y : Ek L => y c).aestronglyMeasurable]
    exact hJL0 L c
  have hmomS : ∫⁻ ζ, ‖S₀ ζ‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (b ^ 2) := by
    refine u5_lintegral_sq_le hpar P hS₀m (fun L => ?_)
    have h1 : ∫⁻ ζ, ENNReal.ofReal (‖u5_tau g L (S₀ ζ)‖ ^ 2) ∂P =
        ∫⁻ ω, ENNReal.ofReal (‖s • ∑ i, ω i‖ ^ 2) ∂(Measure.pi fun _ : Fin N => μ.map (JL L)) := by
      have hf : Measurable fun z : Ek L => ENNReal.ofReal (‖z‖ ^ 2) :=
        ENNReal.measurable_ofReal.comp (measurable_norm.pow_const 2)
      have hm1 : Measurable (fun (ω : Fin N → Ek L) => s • ∑ i, ω i) :=
        (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).const_smul s
      have e1 := lintegral_map (μ := P) (g := fun ζ => u5_tau g L (S₀ ζ)) hf
        ((u5_tau g L).continuous.measurable.comp hS₀m)
      have e2 := lintegral_map (μ := Measure.pi fun _ : Fin N => μ.map (JL L))
        (g := fun ω : Fin N → Ek L => s • ∑ i, ω i) hf hm1
      rw [← e1, ← e2, hlawS L]
    rw [h1, u5_pi_lint hN _ (hρb L) (hρ0 L)]
    exact ENNReal.ofReal_le_ofReal (hρm2 L)
  have hmomI : ∫⁻ ζ, ‖I ζ‖ₑ ^ 2 ∂P' ≤ ENNReal.ofReal (b ^ 2) := by
    refine u5_lintegral_sq_le hpar P' hI (fun L => ?_)
    have h1 : ∫⁻ ζ, ENNReal.ofReal (‖u5_tau g L (I ζ)‖ ^ 2) ∂P' =
        ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 2) ∂(multivariateGaussian (0 : Ek L)
          (Yurinskii.momentMatrix (μ.map (JL L)))) := by
      have hf : Measurable fun z : Ek L => ENNReal.ofReal (‖z‖ ^ 2) :=
        ENNReal.measurable_ofReal.comp (measurable_norm.pow_const 2)
      have e1 := lintegral_map (μ := P') (g := fun ζ => u5_tau g L (I ζ)) hf
        ((u5_tau g L).continuous.measurable.comp hI)
      rw [← e1, hlawI L]
    rw [h1, u5_gauss_lint _ (hρ2 L)]
    exact ENNReal.ofReal_le_ofReal (hρm2 L)
  refine ⟨?_, hmomS, hmomI⟩
  have hSint : Integrable (fun ζ => ‖S₀ ζ‖) P := u5_integrable_of_lintegral_sq P hS₀m hmomS
  have hIint : Integrable (fun ζ => ‖I ζ‖) P' := u5_integrable_of_lintegral_sq P' hI hmomI
  have hιb : ∀ L, ‖u5_iota g L‖ ≤ 1 := fun L =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
      simpa using u5_iota_norm_le hg0 hgo L y
  -- the approximation errors
  have hιτm : ∀ L, Measurable fun (F : E) => u5_iota g L (u5_tau g L F) := fun L =>
    (u5_iota g L).continuous.measurable.comp (u5_tau g L).continuous.measurable
  have hA := u5_approx_tendsto hg0 hgo hpar P S₀ hS₀m hSint
  have hC := u5_approx_tendsto hg0 hgo hpar P' I hI hIint
  -- the triangle inequality for each `L` and slack `t`
  have hkey : ∀ L : ℕ, ∀ t : ℝ, 0 < t →
      wassersteinE 1 (P.map S₀) (P'.map I) ≤
        ENNReal.ofReal (∫ ζ, ‖S₀ ζ - u5_iota g L (u5_tau g L (S₀ ζ))‖ ∂P) +
        ENNReal.ofReal (u5_C0 d m₂ * (Λ + (b + t)) * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10)))) +
        ENNReal.ofReal (∫ ζ, ‖I ζ - u5_iota g L (u5_tau g L (I ζ))‖ ∂P') := by
    intro L t ht
    have hT1 : wassersteinE 1 (P.map S₀) (P.map fun ζ => u5_iota g L (u5_tau g L (S₀ ζ))) ≤
        ENNReal.ofReal (∫ ζ, ‖S₀ ζ - u5_iota g L (u5_tau g L (S₀ ζ))‖ ∂P) := by
      refine u5_w1_le_integral P hS₀m ((hιτm L).comp hS₀m) ?_
      refine Integrable.mono' (hSint.const_mul 2) ((hS₀m.sub ((hιτm L).comp hS₀m)).norm.aestronglyMeasurable)
        (ae_of_all _ fun ζ => ?_)
      rw [Real.norm_eq_abs, abs_norm]
      calc ‖S₀ ζ - u5_iota g L (u5_tau g L (S₀ ζ))‖ ≤ ‖S₀ ζ‖ + ‖u5_iota g L (u5_tau g L (S₀ ζ))‖ :=
            norm_sub_le _ _
        _ ≤ ‖S₀ ζ‖ + ‖S₀ ζ‖ := by gcongr; exact u5_iota_tau_norm_le hg0 hgo hpar L _
        _ = 2 * ‖S₀ ζ‖ := by ring
    have hT3 : wassersteinE 1 (P'.map fun ζ => u5_iota g L (u5_tau g L (I ζ))) (P'.map I) ≤
        ENNReal.ofReal (∫ ζ, ‖I ζ - u5_iota g L (u5_tau g L (I ζ))‖ ∂P') := by
      have := u5_w1_le_integral P' (Z := fun ζ => u5_iota g L (u5_tau g L (I ζ))) (W := I) ((hιτm L).comp hI) hI (by
        refine Integrable.mono' (hIint.const_mul 2) ((((hιτm L).comp hI).sub hI).norm.aestronglyMeasurable)
          (ae_of_all _ fun ζ => ?_)
        rw [Real.norm_eq_abs, abs_norm]
        calc ‖u5_iota g L (u5_tau g L (I ζ)) - I ζ‖ ≤ ‖u5_iota g L (u5_tau g L (I ζ))‖ + ‖I ζ‖ :=
              norm_sub_le _ _
          _ ≤ ‖I ζ‖ + ‖I ζ‖ := by gcongr; exact u5_iota_tau_norm_le hg0 hgo hpar L _
          _ = 2 * ‖I ζ‖ := by ring)
      refine this.trans (le_of_eq ?_)
      have e : ∫ ζ, ‖u5_iota g L (u5_tau g L (I ζ)) - I ζ‖ ∂P' =
          ∫ ζ, ‖I ζ - u5_iota g L (u5_tau g L (I ζ))‖ ∂P' :=
        integral_congr_ae (ae_of_all _ fun ζ => norm_sub_rev _ _)
      rw [e]
    have hT2 : wassersteinE 1 (P.map fun ζ => u5_iota g L (u5_tau g L (S₀ ζ)))
        (P'.map fun ζ => u5_iota g L (u5_tau g L (I ζ))) ≤
        ENNReal.ofReal (u5_C0 d m₂ * (Λ + (b + t)) * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10)))) := by
      have e1 : (P.map fun ζ => u5_iota g L (u5_tau g L (S₀ ζ))) =
          (P.map fun ζ => u5_tau g L (S₀ ζ)).map (u5_iota g L) := by
        have := Measure.map_map (μ := P) (u5_iota g L).continuous.measurable
          ((u5_tau g L).continuous.measurable.comp hS₀m)
        exact this.symm
      have e2 : (P'.map fun ζ => u5_iota g L (u5_tau g L (I ζ))) =
          (P'.map fun ζ => u5_tau g L (I ζ)).map (u5_iota g L) := by
        have := Measure.map_map (μ := P') (u5_iota g L).continuous.measurable
          ((u5_tau g L).continuous.measurable.comp hI)
        exact this.symm
      rw [e1, e2]
      refine (u5_wasserstein_map_le (u5_iota g L) (hιb L) _ _).trans ?_
      rw [hlawS L, hlawI L]
      have := u5_core_final (d := d) (k := L) (N := N) hd hN μ hm2 hm (JL L) (hJLm L)
        (b := b + t) (Λ := Λ) (by linarith) hΛ0 (fun x => (hJLb L x).trans (by linarith)) (hJLL L) (hJL0 L)
      exact this
    have htri1 := wassersteinE_triangle 1 le_rfl (P.map S₀)
      (P.map fun ζ => u5_iota g L (u5_tau g L (S₀ ζ))) (P'.map I)
    have htri2 := wassersteinE_triangle 1 le_rfl (P.map fun ζ => u5_iota g L (u5_tau g L (S₀ ζ)))
      (P'.map fun ζ => u5_iota g L (u5_tau g L (I ζ))) (P'.map I)
    calc wassersteinE 1 (P.map S₀) (P'.map I) ≤ _ := htri1
      _ ≤ _ := add_le_add hT1 htri2
      _ ≤ _ := add_le_add le_rfl (add_le_add hT2 hT3)
      _ = _ := (add_assoc _ _ _).symm
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  set C1 : ℝ := u5_C0 d m₂ * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) with hC1
  have hC1nn : 0 ≤ C1 := mul_nonneg (u5_C0_nonneg d m₂) (by positivity)
  have hηr : (0 : ℝ) < η := by exact_mod_cast hη
  set t : ℝ := η / (3 * (C1 + 1)) with ht
  have htpos : 0 < t := by positivity
  have hC1t : C1 * t ≤ η / 3 := by
    rw [ht, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hηr]
  have hBt : u5_C0 d m₂ * (Λ + (b + t)) * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) =
      u5_C0 d m₂ * (Λ + b) * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) + C1 * t := by
    rw [hC1]; ring
  have hev := (hA.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / 3))).and
    (hC.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / 3)))
  obtain ⟨L, hL1, hL2⟩ := hev.exists
  have hk := hkey L t htpos
  rw [hBt] at hk
  have hB0 : 0 ≤ u5_C0 d m₂ * (Λ + b) * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) := by
    have := u5_C0_nonneg d m₂
    positivity
  have ha0 : 0 ≤ ∫ ζ, ‖S₀ ζ - u5_iota g L (u5_tau g L (S₀ ζ))‖ ∂P := integral_nonneg fun _ => norm_nonneg _
  have hc0 : 0 ≤ ∫ ζ, ‖I ζ - u5_iota g L (u5_tau g L (I ζ))‖ ∂P' := integral_nonneg fun _ => norm_nonneg _
  have hBt0 : 0 ≤ u5_C0 d m₂ * (Λ + b) * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) + C1 * t :=
    add_nonneg hB0 (mul_nonneg hC1nn htpos.le)
  refine hk.trans ?_
  rw [← ENNReal.ofReal_add ha0 hBt0, ← ENNReal.ofReal_add (add_nonneg ha0 hBt0) hc0]
  calc ENNReal.ofReal (∫ ζ, ‖S₀ ζ - u5_iota g L (u5_tau g L (S₀ ζ))‖ ∂P +
        (u5_C0 d m₂ * (Λ + b) * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) + C1 * t) +
        ∫ ζ, ‖I ζ - u5_iota g L (u5_tau g L (I ζ))‖ ∂P') ≤
      ENNReal.ofReal (u5_C0 d m₂ * (Λ + b) * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) + (η : ℝ)) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (u5_C0 d m₂ * (Λ + b) * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10)))) + η := by
        rw [ENNReal.ofReal_add hB0 η.coe_nonneg, ENNReal.ofReal_coe_nnreal]

end Assembly

end HRS.U5
