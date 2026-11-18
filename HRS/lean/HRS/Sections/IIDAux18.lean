import HRS.Sections.IIDAux17

/-!
# IID helper chain, part 18: assembly of the mixture comparison.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.IID

section MixFinal

open HRS.InitialDataAux

variable {d : ℕ}

set_option maxHeartbeats 800000 in
theorem mixture_aux (hd : 2 ≤ d) (m : ℝ) (hm : (d : ℝ) / 2 < m) (c : ℝ) (hc : 0 < c)
    (a : ℝ) (b : Torus d → ℝ) (hbm : Measurable b) (hbL : MemLp b ⊤ (volume : Measure (Torus d))) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, c ≤ ρ x) →
      pair (withDensityReal ρ) b = 0 →
      ∀ γ : Measure (NegSobolev d m),
      IsCenteredGaussianWithCov m γ (iidCov (withDensityReal ρ)) →
      ∀ N : ℕ, 2 ≤ N → 4 * a ^ 2 * (eLpNorm b ⊤ (volume : Measure (Torus d))).toReal ^ 2 ≤ N →
        smoothDist 2
            (law ((2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 + a * b x / Real.sqrt N) * ρ x) +
                (2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 - a * b x / Real.sqrt N) * ρ x))
              (fun X : Config d N => etaE m X (withDensityReal ρ)))
            ((2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F + NegSobolev.ofFun m (fun x => a * b x * ρ x)) +
              (2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F - NegSobolev.ofFun m (fun x => a * b x * ρ x))) ≤
          Cm * (N : ℝ) ^ (-((m - (d : ℝ) / 2) / (2 * m))) ∧
        wassersteinE 1
            (law ((2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 + a * b x / Real.sqrt N) * ρ x) +
                (2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 - a * b x / Real.sqrt N) * ρ x))
              (fun X : Config d N => etaE m X (withDensityReal ρ)))
            ((2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F + NegSobolev.ofFun m (fun x => a * b x * ρ x)) +
              (2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F - NegSobolev.ofFun m (fun x => a * b x * ρ x))) ≤
          ENNReal.ofReal (Cm * (Real.log (Real.exp 1 * N) / Real.sqrt N) ^
            ((m - (d : ℝ) / 2) / (m + (d : ℝ) / 2))) ∧
        wassersteinE 2
            (law ((2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 + a * b x / Real.sqrt N) * ρ x) +
                (2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 - a * b x / Real.sqrt N) * ρ x))
              (fun X : Config d N => etaE m X (withDensityReal ρ)))
            ((2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F + NegSobolev.ofFun m (fun x => a * b x * ρ x)) +
              (2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F - NegSobolev.ofFun m (fun x => a * b x * ρ x))) ≤
          ENNReal.ofReal (Cm * ((Real.log (Real.exp 1 * N) / Real.sqrt N) ^
            ((m - (d : ℝ) / 2) / (m + (d : ℝ) / 2))) ^ ((1 : ℝ) / 3)) := by
  have hm2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨Cs, Cw, Cz, M, hCs, hCw, hCz, hM, hgen⟩ := comparison_gen hd m hm (c / 2) (by positivity)
  set B₀ : ℝ := (eLpNorm b ⊤ (volume : Measure (Torus d))).toReal with hB₀
  have hB00 : 0 ≤ B₀ := ENNReal.toReal_nonneg
  obtain ⟨b', hb'm, hb'B, hbb'⟩ := clip_exists hbm hbL
  set K : ℝ := Cz * |a| * B₀ with hK
  have hK0 : 0 ≤ K := by positivity
  set Cm : ℝ := max (max (Cs + K) (Cw + 1 + K))
    (Real.sqrt (2 * M ^ ((1 : ℝ) / 3)) * (Cw + 1 + K) ^ ((1 : ℝ) / 3)) with hCm
  refine ⟨Cm, by positivity, ?_⟩
  intro ρ hρ hρc hpair γ hγ N hN2 hN4
  haveI : IsProbabilityMeasure γ := by haveI := hγ.1.1; infer_instance
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hN : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  set ε : ℝ := a / Real.sqrt N with hε
  have hε2 : |ε| * B₀ ≤ 1 / 2 := by
    have h1 : 2 * |a| * B₀ ≤ Real.sqrt N := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [sq_abs a]
    rw [hε, abs_div, abs_of_pos hsN, div_mul_eq_mul_div, div_le_iff₀ hsN]
    linarith
  -- ∫ ρ b' = 0
  have h0 : ∫ x, ρ x * b' x = 0 := by
    have e1 : pair (withDensityReal ρ) b = ∫ x, ρ x * b x := by
      unfold pair; exact integral_withDensityReal_eq ρ hρ.measurable hρ.nonneg b
    rw [e1] at hpair
    rw [← hpair]
    refine integral_congr_ae ?_
    filter_upwards [hbb'] with x hx
    rw [hx]
  -- the two densities
  set q₁ : Torus d → ℝ := fun x => (1 + ε * b' x) * ρ x with hq₁
  set q₂ : Torus d → ℝ := fun x => (1 + (-ε) * b' x) * ρ x with hq₂
  have hε2' : |-ε| * B₀ ≤ 1 / 2 := by rwa [abs_neg]
  have hqp₁ : IsProbDensity q₁ := qd_prob hρ hb'm hb'B hε2 h0
  have hqp₂ : IsProbDensity q₂ := qd_prob hρ hb'm hb'B hε2' h0
  have hs₁ := sign_facts hm2 hgen hρ hρc hb'm hb'B h0 hε2 hγ hN
  have hs₂ := sign_facts hm2 hgen hρ hρc hb'm hb'B h0 hε2' hγ hN
  -- identification of the measures in the statement
  have hmeas₁ : withDensityReal (fun x => (1 + a * b x / Real.sqrt N) * ρ x) = withDensityReal q₁ := by
    refine withDensityReal_congr ?_
    filter_upwards [hbb'] with x hx
    simp only [hq₁, hε, ← hx]; ring
  have hmeas₂ : withDensityReal (fun x => (1 - a * b x / Real.sqrt N) * ρ x) = withDensityReal q₂ := by
    refine withDensityReal_congr ?_
    filter_upwards [hbb'] with x hx
    simp only [hq₂, hε, ← hx]; ring
  -- the shift
  set s : NegSobolev d m := NegSobolev.ofFun m (fun x => a * b' x * ρ x) with hs
  have hint : Integrable (fun x => a * b' x * ρ x) := by
    have := (integrable_mul_bdd (integrable_of_pd hρ) hb'm hb'B).const_mul a
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  have hshift₁ : Real.sqrt N • NegSobolev.ofMeasureDiff m (withDensityReal q₁) (withDensityReal ρ) = s :=
    sqrtN_ofMeasureDiff hm2 hqp₁ hρ hint (fun x => by
      simp only [hq₁, hε]; field_simp; ring)
  have hshift₂ : Real.sqrt N • NegSobolev.ofMeasureDiff m (withDensityReal q₂) (withDensityReal ρ) = -s := by
    have := sqrtN_ofMeasureDiff hm2 hqp₂ hρ hint.neg (c0 := Real.sqrt N) (f := fun x => -(a * b' x * ρ x))
      (fun x => by simp only [hq₂, hε]; field_simp; ring)
    rw [this, hs]
    exact ofFun_neg hm2 hint
  have hfl₁ : ∀ X : Config d N, fld m N (withDensityReal ρ) X = fld m N (withDensityReal q₁) X + s :=
    fun X => by rw [fld_shift hm2 hN hqp₁ hρ X, hshift₁]
  have hfl₂ : ∀ X : Config d N, fld m N (withDensityReal ρ) X = fld m N (withDensityReal q₂) X + -s :=
    fun X => by rw [fld_shift hm2 hN hqp₂ hρ X, hshift₂]
  have hsfun : NegSobolev.ofFun m (fun x => a * b x * ρ x) = s := by
    rw [hs]; exact ofFun_congr (by filter_upwards [hbb'] with x hx; simp only [hx])
  have hlaw := law_mix hm2 hN hρ hqp₁ hqp₂ s hfl₁ hfl₂
  have hsub : (fun F : NegSobolev d m => F - s) = fun F => F + -s := by funext F; simp [sub_eq_add_neg]
  simp only [hmeas₁, hmeas₂, hsfun, hsub]
  have hetaeq : (fun X : Config d N => etaE m X (withDensityReal ρ)) = fld m N (withDensityReal ρ) := rfl
  rw [hetaeq]
  unfold law
  rw [hlaw]
  obtain ⟨hsd₁, hcb₁⟩ := hs₁
  obtain ⟨hsd₂, hcb₂⟩ := hs₂
  set e2 : ℝ := (N : ℝ) ^ (-((m - (d : ℝ) / 2) / (2 * m))) with he2
  set j : ℝ := (Real.log (Real.exp 1 * N) / Real.sqrt N) ^
    ((m - (d : ℝ) / 2) / (m + (d : ℝ) / 2)) with hj
  have hΛ1 : 1 ≤ Real.log (Real.exp 1 * N) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
    have : 0 ≤ Real.log N := Real.log_nonneg hN1
    linarith
  have hj0 : 0 < j := Real.rpow_pos_of_pos (div_pos (by linarith) hsN) _
  have hεe : |ε| = |a| * (1 / Real.sqrt N) := by
    rw [hε, abs_div, abs_of_pos hsN]; ring
  have hκe : |ε| * B₀ ≤ |a| * B₀ * e2 := by
    rw [hεe]
    have := inv_sqrt_le_e2 hm hN
    calc |a| * (1 / Real.sqrt N) * B₀ = |a| * B₀ * (1 / Real.sqrt N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
  have hκj : |ε| * B₀ ≤ |a| * B₀ * j := by
    rw [hεe]
    have := inv_sqrt_le_W hm hN
    calc |a| * (1 / Real.sqrt N) * B₀ = |a| * B₀ * (1 / Real.sqrt N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
  have he20 : 0 ≤ e2 := Real.rpow_nonneg hN0.le _
  have hmax1 : Cs + K ≤ Cm := (le_max_left _ _).trans (le_max_left _ _)
  have hmax2 : Cw + 1 + K ≤ Cm := (le_max_right _ _).trans (le_max_left _ _)
  have hmax3 : Real.sqrt (2 * M ^ ((1 : ℝ) / 3)) * (Cw + 1 + K) ^ ((1 : ℝ) / 3) ≤ Cm := le_max_right _ _
  set ν₁ := (Measure.pi fun _ : Fin N => withDensityReal q₁).map (fld m N (withDensityReal q₁)) with hν₁
  set ν₂ := (Measure.pi fun _ : Fin N => withDensityReal q₂).map (fld m N (withDensityReal q₂)) with hν₂
  haveI := isProb_withDensityReal hqp₁
  haveI := isProb_withDensityReal hqp₂
  have hF₁ : Measurable (fld m N (withDensityReal q₁)) := (continuous_fld hm2 hN _).measurable
  have hF₂ : Measurable (fld m N (withDensityReal q₂)) := (continuous_fld hm2 hN _).measurable
  haveI : IsProbabilityMeasure ν₁ := isProb_map' hF₁
  haveI : IsProbabilityMeasure ν₂ := isProb_map' hF₂
  haveI : IsProbabilityMeasure (ν₁.map fun x => x + s) := isProb_map' (measurable_add_const s)
  haveI : IsProbabilityMeasure (ν₂.map fun x => x + -s) := isProb_map' (measurable_add_const (-s))
  haveI : IsProbabilityMeasure (γ.map fun x => x + s) := isProb_map' (measurable_add_const s)
  haveI : IsProbabilityMeasure (γ.map fun x => x + -s) := isProb_map' (measurable_add_const (-s))
  have hJ1 : 0 ≤ Cw * j + Cz * (|ε| * B₀) := by positivity
  have hJ2 : 0 ≤ Cw * j + Cz * (|-ε| * B₀) := by positivity
  have hcb := CB.mix hJ1 hJ2 hM.le hM.le (hcb₁.shift s) (hcb₂.shift (-s))
  have hJ' : (Cw * j + Cz * (|ε| * B₀) + (Cw * j + Cz * (|-ε| * B₀))) / 2 ≤ (Cw + 1 + K) * j := by
    rw [abs_neg]
    have : Cz * (|ε| * B₀) ≤ K * j := by
      calc Cz * (|ε| * B₀) ≤ Cz * (|a| * B₀ * j) := mul_le_mul_of_nonneg_left hκj hCz
        _ = K * j := by rw [hK]; ring
    linarith
  have hcb' := hcb.mono' hJ' (le_of_eq (by ring : (M + M) / 2 = M))
  have hJpos : 0 < (Cw + 1 + K) * j := by positivity
  refine ⟨?_, ?_, ?_⟩
  · calc _ ≤ (1 / 2) * smoothDist 2 (ν₁.map fun x => x + s) (γ.map fun x => x + s) +
          (1 / 2) * smoothDist 2 (ν₂.map fun x => x + -s) (γ.map fun x => x + -s) := smoothDist_mix_le
      _ ≤ (1 / 2) * smoothDist 2 ν₁ γ + (1 / 2) * smoothDist 2 ν₂ γ := by
          gcongr
          · exact smoothDist_translate_le s
          · exact smoothDist_translate_le (-s)
      _ ≤ (1 / 2) * (Cs * e2 + Cz * (|ε| * B₀)) + (1 / 2) * (Cs * e2 + Cz * (|-ε| * B₀)) := by
          gcongr
      _ ≤ (Cs + K) * e2 := by
          rw [abs_neg]
          have : Cz * (|ε| * B₀) ≤ K * e2 := by
            calc Cz * (|ε| * B₀) ≤ Cz * (|a| * B₀ * e2) := mul_le_mul_of_nonneg_left hκe hCz
              _ = K * e2 := by rw [hK]; ring
          linarith
      _ ≤ Cm * e2 := mul_le_mul_of_nonneg_right hmax1 he20
  · refine hcb'.w1.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right hmax2 hj0.le
  · refine (hcb'.w2 hJpos hM).trans (ENNReal.ofReal_le_ofReal ?_)
    have hj3 : 0 ≤ j ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hj0.le _
    have e1 : Real.sqrt (2 * M ^ ((1 : ℝ) / 3) * (((Cw + 1 + K) * j) ^ ((1 : ℝ) / 3)) ^ 2) =
        (Real.sqrt (2 * M ^ ((1 : ℝ) / 3)) * (Cw + 1 + K) ^ ((1 : ℝ) / 3)) * j ^ ((1 : ℝ) / 3) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
        Real.mul_rpow (by positivity) hj0.le]
      ring
    rw [e1]
    exact mul_le_mul_of_nonneg_right hmax3 hj3

end MixFinal

end HRS.IID
