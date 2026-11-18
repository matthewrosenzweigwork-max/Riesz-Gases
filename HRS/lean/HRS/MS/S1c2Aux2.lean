import HRS.MS.S1c2Aux1

/-!
# S1C2 aux 2: the `L^p` bound of the absolute central-difference singular integral

For `u ∈ C^ℓ(ℝ^d; E)` and `0 < r < ℓ`, `1 < p < ∞`, the function
`W u x = ∫ |y|^{-d-r} ‖Δ_y^{(2ℓ)} u (x)‖ dy` (`ℝ≥0∞`-valued) satisfies
`∫ W^p ≤ c₁ ∫ ‖D^ℓ u‖^p + c₂ ∫ ‖u‖^p` with constants `c₁, c₂ < ∞` depending only on `(d, r, p, ℓ)`.
The proof splits `y` into the unit ball (weighted Minkowski with weight `|y|^σ`, `r < σ < ℓ`, and the Taylor
bound) and its complement (Minkowski and the crude bound).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HRS.S1C2

open HRS.U8

variable {d : ℕ}

/-- `ofReal (‖y‖^a)` as an `ℝ≥0∞`. -/
def pw (a : ℝ) (y : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ := ENNReal.ofReal (‖y‖ ^ a)

theorem pw_measurable (a : ℝ) : Measurable (pw (d := d) a) :=
  ENNReal.measurable_ofReal.comp (measurable_norm.pow_const a)

theorem pw_mul (a b : ℝ) {y : EuclideanSpace ℝ (Fin d)} (hy : y ≠ 0) :
    pw a y * pw b y = pw (a + b) y := by
  unfold pw
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_add (norm_pos_iff.2 hy)]

theorem pw_rpow (a q : ℝ) (hq : 0 ≤ q) (y : EuclideanSpace ℝ (Fin d)) :
    pw a y ^ q = pw (a * q) y := by
  unfold pw
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hq,
    ← Real.rpow_mul (norm_nonneg _)]

theorem s1c2_ae_ne_zero (hd : 1 ≤ d) : ∀ᵐ y : EuclideanSpace ℝ (Fin d) ∂volume, y ≠ 0 := by
  have : NeZero d := ⟨by omega⟩
  have h : (volume : Measure (EuclideanSpace ℝ (Fin d))) {0} = 0 := measure_singleton 0
  rw [ae_iff]
  simpa using h

theorem s1c2_near_fin (hd : 1 ≤ d) (η : ℝ) (hη : 0 < η) :
    ∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1, pw (η - d) y < ∞ :=
  (u8_near_int hd η 1 hη one_pos).1.lintegral_lt_top

theorem s1c2_far_fin (hd : 1 ≤ d) (η : ℝ) (hη : 0 < η) :
    ∫⁻ y in (ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ, pw (-(d : ℝ) - η) y < ∞ := by
  have h := (u8_far_int hd η 1 hη one_pos).1.lintegral_lt_top
  have e : (fun y : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal
      (((ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ.indicator
        (fun y => ‖y‖ ^ (-(d : ℝ) - η))) y)) =
      (ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ.indicator (fun y => pw (-(d : ℝ) - η) y) := by
    funext y
    by_cases hy : y ∈ (ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ <;> simp [hy, pw]
  rw [e, lintegral_indicator measurableSet_ball.compl] at h
  exact h

/-- The kernel `|y|^{-d-r}` times the absolute central difference of order `2ℓ`. -/
def s1c2_W (d : ℕ) (r : ℝ) (ℓ : ℕ) {E : Type*} [NormedAddCommGroup E]
    (u : EuclideanSpace ℝ (Fin d) → E) (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ∫⁻ y, pw (-((d : ℝ) + r)) y * ‖u8_fd (u8_L ℓ y) u x‖ₑ

theorem s1c2_G_meas (ℓ : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : EuclideanSpace ℝ (Fin d) → E} (hu : Continuous u) :
    Measurable (Function.uncurry fun (x : EuclideanSpace ℝ (Fin d)) y =>
      ‖u8_fd (u8_L ℓ y) u x‖ₑ) :=
  (((u8_L_cont_joint ℓ hu).comp continuous_swap).enorm).measurable

theorem s1c2_near_bound (hd : 1 ≤ d) {r p : ℝ} (hr : 0 < r) (hp : 1 < p) (ℓ : ℕ)
    (hrℓ : r < ℓ) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (u : EuclideanSpace ℝ (Fin d) → E), ContDiff ℝ ℓ u →
      ∫⁻ x, (∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
          pw (-((d : ℝ) + r)) y * ‖u8_fd (u8_L ℓ y) u x‖ₑ) ^ p ≤
        c * Ip volume p (iteratedFDeriv ℝ ℓ u) := by
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = (r + ℓ) / 2 := ⟨_, rfl⟩
  have hσr : r < σ := by rw [hσ]; linarith
  have hη' : 0 < (ℓ : ℝ) * p - r - σ * (p - 1) := by
    rw [hσ]; nlinarith
  set K : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := pw (-((d : ℝ) + r)) with hK
  set θ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := pw σ with hθ
  set ψ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := pw (-σ) with hψ
  set B : Set (EuclideanSpace ℝ (Fin d)) := ball 0 1 with hB
  set ν : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict B with hν
  have hae0 : ∀ᵐ y ∂ν, y ≠ 0 := ae_restrict_of_ae (s1c2_ae_ne_zero hd)
  have hθψ : ∀ᵐ y ∂ν, θ y * ψ y = 1 := by
    filter_upwards [hae0] with y hy
    rw [hθ, hψ, pw_mul _ _ hy]
    simp [pw]
  set cy : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun y =>
    ((2 : ℝ≥0∞) ^ ℓ * ENNReal.ofReal (‖y‖ ^ ℓ)) ^ p with hcy
  refine ⟨(∫⁻ y, K y * θ y ∂ν) ^ (p - 1) * ∫⁻ y, K y * θ y * ψ y ^ p * cy y ∂ν, ?_, ?_⟩
  · -- finiteness
    have h1 : ∫⁻ y, K y * θ y ∂ν < ∞ := by
      have : ∫⁻ y, K y * θ y ∂ν = ∫⁻ y in B, pw ((σ - r) - d) y := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae0] with y hy
        rw [hK, hθ, pw_mul _ _ hy]
        have e : -((d : ℝ) + r) + σ = (σ - r) - d := by ring
        rw [e]
      rw [this]
      exact s1c2_near_fin hd _ (by linarith)
    have h2 : ∫⁻ y, K y * θ y * ψ y ^ p * cy y ∂ν < ∞ := by
      have : ∫⁻ y, K y * θ y * ψ y ^ p * cy y ∂ν =
          ((2 : ℝ≥0∞) ^ ℓ) ^ p * ∫⁻ y in B, pw (((ℓ : ℝ) * p - r - σ * (p - 1)) - d) y := by
        rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0
          (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))]
        refine lintegral_congr_ae ?_
        filter_upwards [hae0] with y hy
        have h1 : pw (-((d : ℝ) + r)) y * pw σ y = pw (-((d : ℝ) + r) + σ) y := pw_mul _ _ hy
        have h2 : pw (-σ) y ^ p = pw (-σ * p) y := pw_rpow _ _ hp0 y
        have h3 : pw (-((d : ℝ) + r) + σ) y * pw (-σ * p) y =
            pw (-((d : ℝ) + r) + σ + -σ * p) y := pw_mul _ _ hy
        have h4 : ENNReal.ofReal (‖y‖ ^ ℓ) ^ p = pw ((ℓ : ℝ) * p) y := by
          rw [← pw_rpow _ _ hp0]
          simp [pw, Real.rpow_natCast]
        have h5 : pw (-((d : ℝ) + r) + σ + -σ * p) y * pw ((ℓ : ℝ) * p) y =
            pw (((ℓ : ℝ) * p - r - σ * (p - 1)) - d) y := by
          rw [pw_mul _ _ hy]
          have e : -((d : ℝ) + r) + σ + -σ * p + (ℓ : ℝ) * p = ((ℓ : ℝ) * p - r - σ * (p - 1)) - d := by
            ring
          rw [e]
        rw [hK, hθ, hψ, hcy]
        calc pw (-((d : ℝ) + r)) y * pw σ y * pw (-σ) y ^ p *
              ((2 ^ ℓ * ENNReal.ofReal (‖y‖ ^ ℓ)) ^ p)
            = (pw (-((d : ℝ) + r)) y * pw σ y) * pw (-σ) y ^ p *
              (((2 : ℝ≥0∞) ^ ℓ) ^ p * ENNReal.ofReal (‖y‖ ^ ℓ) ^ p) := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ hp0]
          _ = ((2 : ℝ≥0∞) ^ ℓ) ^ p * ((pw (-((d : ℝ) + r) + σ) y * pw (-σ * p) y) *
              pw ((ℓ : ℝ) * p) y) := by rw [h1, h2, h4]; ring
          _ = _ := by rw [h3, h5]
      rw [this]
      exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp0
        (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)) (s1c2_near_fin hd _ hη')
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) h1.ne)
      h2.ne
  · intro E _ _ _ u hu
    have hmk := s1c2_mink (volume : Measure (EuclideanSpace ℝ (Fin d))) ν hp K θ ψ
      (pw_measurable _) (pw_measurable _) (pw_measurable _) hθψ
      (fun x y => ‖u8_fd (u8_L ℓ y) u x‖ₑ) (s1c2_G_meas ℓ hu.continuous)
    refine hmk.trans ?_
    have hmeas : Measurable (fun y : EuclideanSpace ℝ (Fin d) => K y * θ y * ψ y ^ p * cy y) :=
      (((pw_measurable _).mul (pw_measurable _)).mul ((pw_measurable _).pow_const p)).mul
        ((measurable_const.mul (ENNReal.measurable_ofReal.comp
          (measurable_norm.pow_const ℓ))).pow_const p)
    calc (∫⁻ y, K y * θ y ∂ν) ^ (p - 1) *
          ∫⁻ y, K y * θ y * ψ y ^ p * ∫⁻ x, ‖u8_fd (u8_L ℓ y) u x‖ₑ ^ p ∂volume ∂ν
        ≤ (∫⁻ y, K y * θ y ∂ν) ^ (p - 1) *
          ∫⁻ y, K y * θ y * ψ y ^ p * (cy y * Ip volume p (iteratedFDeriv ℝ ℓ u)) ∂ν := by
          refine mul_le_mul_right (lintegral_mono (fun y => ?_)) _
          exact mul_le_mul_right (s1c2_uL_Ip_near hp ℓ u hu y) _
      _ = _ := by
          rw [mul_assoc]
          congr 1
          rw [← lintegral_mul_const'' _ hmeas.aemeasurable]
          refine lintegral_congr (fun y => ?_)
          ring

theorem s1c2_far_bound (hd : 1 ≤ d) {r p : ℝ} (hr : 0 < r) (hp : 1 < p) (ℓ : ℕ) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (u : EuclideanSpace ℝ (Fin d) → E), Continuous u →
      ∫⁻ x, (∫⁻ y in (ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ,
          pw (-((d : ℝ) + r)) y * ‖u8_fd (u8_L ℓ y) u x‖ₑ) ^ p ≤
        c * Ip volume p u := by
  have hp0 : 0 ≤ p := by linarith
  set K : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := pw (-((d : ℝ) + r)) with hK
  set ν : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict (ball 0 1)ᶜ with hν
  have hfin : ∫⁻ y, K y ∂ν < ∞ := by
    have : ∫⁻ y, K y ∂ν = ∫⁻ y in (ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ,
        pw (-(d : ℝ) - r) y := by
      refine lintegral_congr (fun y => ?_)
      rw [hK]; rw [neg_add']
    rw [this]
    exact s1c2_far_fin hd r hr
  refine ⟨(∫⁻ y, K y ∂ν) ^ (p - 1) * ((∫⁻ y, K y ∂ν) * ((2 : ℝ≥0∞) ^ (2 * ℓ)) ^ p), ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) hfin.ne)
      (ENNReal.mul_ne_top hfin.ne (ENNReal.rpow_ne_top_of_nonneg hp0
        (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)))
  · intro E _ _ u hu
    have hmk := s1c2_mink (volume : Measure (EuclideanSpace ℝ (Fin d))) ν hp K (fun _ => 1)
      (fun _ => 1) (pw_measurable _) measurable_const measurable_const
      (Filter.Eventually.of_forall (fun _ => by simp))
      (fun x y => ‖u8_fd (u8_L ℓ y) u x‖ₑ) (s1c2_G_meas ℓ hu)
    simp only [mul_one, ENNReal.one_rpow] at hmk
    refine hmk.trans ?_
    calc (∫⁻ y, K y ∂ν) ^ (p - 1) * ∫⁻ y, K y * ∫⁻ x, ‖u8_fd (u8_L ℓ y) u x‖ₑ ^ p ∂volume ∂ν
        ≤ (∫⁻ y, K y ∂ν) ^ (p - 1) *
          ∫⁻ y, K y * (((2 : ℝ≥0∞) ^ (2 * ℓ)) ^ p * Ip volume p u) ∂ν := by
          refine mul_le_mul_right (lintegral_mono (fun y => ?_)) _
          exact mul_le_mul_right (s1c2_uL_Ip_far hp ℓ u hu y) _
      _ = _ := by
          rw [mul_assoc]
          congr 1
          have e : ∀ y, K y * (((2 : ℝ≥0∞) ^ (2 * ℓ)) ^ p * Ip volume p u) =
              (K y * ((2 : ℝ≥0∞) ^ (2 * ℓ)) ^ p) * Ip volume p u := fun y => by ring
          simp_rw [e]
          have hm0 : Measurable K := pw_measurable _
          have hm1 : Measurable (fun y : EuclideanSpace ℝ (Fin d) =>
              K y * ((2 : ℝ≥0∞) ^ (2 * ℓ)) ^ p) := hm0.mul measurable_const
          rw [lintegral_mul_const'' _ hm1.aemeasurable, lintegral_mul_const'' _ hm0.aemeasurable]

/-- The `L^p` bound of the absolute singular integral. -/
theorem s1c2_W_bound (hd : 1 ≤ d) {r p : ℝ} (hr : 0 < r) (hp : 1 < p) (ℓ : ℕ)
    (hrℓ : r < ℓ) :
    ∃ c₁ c₂ : ℝ≥0∞, c₁ ≠ ∞ ∧ c₂ ≠ ∞ ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] (u : EuclideanSpace ℝ (Fin d) → E), ContDiff ℝ ℓ u →
      ∫⁻ x, (s1c2_W d r ℓ u x) ^ p ≤
        c₁ * Ip volume p (iteratedFDeriv ℝ ℓ u) + c₂ * Ip volume p u := by
  obtain ⟨cN, hcN, hN⟩ := s1c2_near_bound hd hr hp ℓ hrℓ
  obtain ⟨cF, hcF, hF⟩ := s1c2_far_bound hd hr hp ℓ
  have h2 : (2 : ℝ≥0∞) ^ (p - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top
  refine ⟨2 ^ (p - 1) * cN, 2 ^ (p - 1) * cF, ENNReal.mul_ne_top h2 hcN,
    ENNReal.mul_ne_top h2 hcF, ?_⟩
  intro E _ _ _ u hu
  set Nf : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun x =>
    ∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1,
      pw (-((d : ℝ) + r)) y * ‖u8_fd (u8_L ℓ y) u x‖ₑ with hNf
  set Ff : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun x =>
    ∫⁻ y in (ball (0 : EuclideanSpace ℝ (Fin d)) 1)ᶜ,
      pw (-((d : ℝ) + r)) y * ‖u8_fd (u8_L ℓ y) u x‖ₑ with hFf
  have hW : ∀ x, s1c2_W d r ℓ u x = Nf x + Ff x := fun x =>
    (lintegral_add_compl _ measurableSet_ball).symm
  have hNm : Measurable Nf := by
    have : Measurable (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        pw (-((d : ℝ) + r)) q.2 * ‖u8_fd (u8_L ℓ q.2) u q.1‖ₑ) :=
      ((pw_measurable _).comp measurable_snd).mul (s1c2_G_meas ℓ hu.continuous)
    exact this.lintegral_prod_right'
  calc ∫⁻ x, (s1c2_W d r ℓ u x) ^ p = ∫⁻ x, (Nf x + Ff x) ^ p := by simp_rw [hW]
    _ ≤ ∫⁻ x, 2 ^ (p - 1) * (Nf x ^ p + Ff x ^ p) :=
        lintegral_mono (fun x => ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp.le)
    _ = 2 ^ (p - 1) * ((∫⁻ x, Nf x ^ p) + ∫⁻ x, Ff x ^ p) := by
        rw [lintegral_const_mul' _ _ h2, lintegral_add_left (hNm.pow_const p)]
    _ ≤ 2 ^ (p - 1) * (cN * Ip volume p (iteratedFDeriv ℝ ℓ u) + cF * Ip volume p u) := by
        exact mul_le_mul_right (add_le_add (hN E u hu) (hF E u hu.continuous)) _
    _ = _ := by ring

end HRS.S1C2
