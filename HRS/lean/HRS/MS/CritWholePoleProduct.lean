import HRS.MS.CritWholePoleCmp

/-!
# S8.1 XS, TT04: small polynomial loss of the pole law against the product measure

`Q_{n,b}` against `μ^n` by the generic Hölder step `ProdTransfer.AL` and the whole-space pressure bound
`euclidean_pressure_pos` (`h = 0`, `θ = 0`) at `b` and `2b`, `|log K| ≤ C log(e n)` at the critical exponent; `n = 1`
by the bounded one-body exponent.  Then the pole law is dominated by `Q_{n, nβ/N}` (`s81b_pole_comparison`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr

namespace HRS.Whole.S81b

variable {d : ℕ}

/-- `AL` for the modulated Gibbs law, given the three normalizer bounds. -/
theorem s81b_Q_AL (hd : 1 ≤ d) {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {n : ℕ} {b A : ℝ}
    (hw : Integrable (fun X : EucConfig d n => Real.exp (-b * n * modulatedEnergy (critG d) X μ))
      (Measure.pi fun _ : Fin n => μ))
    (hw2 : Integrable (fun X : EucConfig d n => Real.exp (-(2 * b) * n * modulatedEnergy (critG d) X μ))
      (Measure.pi fun _ : Fin n => μ))
    (hlo : Real.exp (-A) ≤ gibbsNormalizer (critG d) n b μ)
    (hhi : gibbsNormalizer (critG d) n b μ ≤ Real.exp A)
    (hhi2 : gibbsNormalizer (critG d) n (2 * b) μ ≤ Real.exp A)
    (q : ℝ) (hq : 2 ≤ q) (F : EucConfig d n → ℝ) (hF : Measurable F) :
    eLpNorm F 2 (modulatedGibbs (critG d) n b μ) ≤
      ENNReal.ofReal (Real.exp (3 * A / (2 * q))) *
        eLpNorm F (ENNReal.ofReal (2 * q)) (Measure.pi fun _ : Fin n => μ) := by
  set ν : Measure (EucConfig d n) := Measure.pi fun _ : Fin n => μ with hν
  set φ : EucConfig d n → ℝ := fun X => -b * n * modulatedEnergy (critG d) X μ with hφ
  have hφm : Measurable φ := by
    have hs0 : 0 < ((d : ℝ) / 2) := by
      have : (0 : ℝ) < d := by exact_mod_cast hd
      positivity
    have hg : Measurable (critG d) := wr13a_g_meas hs0
    have hc : Measurable (convMeasure (critG d) μ) := wr13a_conv_meas hs0 μ
    have h1 : Measurable fun X : EucConfig d n => ∑ i, ∑ j ∈ Finset.univ.erase i, critG d (X i - X j) :=
      Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
        hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
    have h2 : Measurable fun X : EucConfig d n => ∑ i, convMeasure (critG d) μ (X i) :=
      Finset.measurable_sum _ fun i _ => hc.comp (measurable_pi_apply i)
    exact ((((h1.const_mul _).sub (h2.const_mul _)).add_const _).const_mul _)
  have hZ : ∫⁻ a, ENNReal.ofReal (Real.exp (φ a)) ∂ν = ENNReal.ofReal (gibbsNormalizer (critG d) n b μ) :=
    (ofReal_integral_eq_lintegral_ofReal hw (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)).symm
  have hZ2 : ∫⁻ a, ENNReal.ofReal (Real.exp (2 * φ a)) ∂ν =
      ENNReal.ofReal (gibbsNormalizer (critG d) n (2 * b) μ) := by
    have := (ofReal_integral_eq_lintegral_ofReal hw2
      (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)).symm
    refine Eq.trans (lintegral_congr fun X => ?_) this
    simp only [hφ]; congr 2; ring
  have := ProdTransfer.AL ν φ hφm A (by rw [hZ]; exact ENNReal.ofReal_le_ofReal hlo)
    (by rw [hZ]; exact ENNReal.ofReal_le_ofReal hhi) (by rw [hZ2]; exact ENNReal.ofReal_le_ofReal hhi2)
    q hq F hF
  unfold modulatedGibbs
  rw [← hZ]
  exact this

/-- One particle: the Gibbs exponent is bounded by `b Mg`. -/
theorem s81b_one_particle (hd : 1 ≤ d) {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Mg : ℝ}
    (hconv : ∀ z, convMeasure (critG d) μ z ≤ Mg) (hMg : 0 ≤ Mg) {b : ℝ} (hb : 0 ≤ b) :
    Integrable (fun X : EucConfig d 1 => Real.exp (-b * (1 : ℕ) * modulatedEnergy (critG d) X μ))
      (Measure.pi fun _ : Fin 1 => μ) ∧
    Real.exp (-(b * Mg)) ≤ gibbsNormalizer (critG d) 1 b μ ∧
    gibbsNormalizer (critG d) 1 b μ ≤ Real.exp (b * Mg) := by
  have hs0 : 0 < ((d : ℝ) / 2) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have hc0 : ∀ z, 0 ≤ convMeasure (critG d) μ z := fun z => wr13a_conv_nonneg hs0 μ z
  have hI2 : 0 ≤ energyPairing (critG d) μ μ ∧ energyPairing (critG d) μ μ ≤ Mg := by
    unfold energyPairing
    refine ⟨integral_nonneg fun x => hc0 x, ?_⟩
    calc ∫ x, ∫ y, critG d (x - y) ∂μ ∂μ ≤ ∫ x, Mg ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => hc0 x) (integrable_const _)
            (Filter.Eventually.of_forall hconv)
      _ = Mg := by simp
  have hbd : ∀ X : EucConfig d 1, |(-b) * ((1 : ℕ) : ℝ) * modulatedEnergy (critG d) X μ| ≤ b * Mg := by
    intro X
    have hE : modulatedEnergy (critG d) X μ = -convMeasure (critG d) μ (X 0) +
        (1 / 2) * energyPairing (critG d) μ μ := by
      unfold modulatedEnergy
      simp
    have h0 := hc0 (X 0)
    have h1 := hconv (X 0)
    rw [hE, abs_le]
    constructor <;> push_cast <;> nlinarith [hI2.1, hI2.2]
  have hm : Measurable fun X : EucConfig d 1 => -b * ((1 : ℕ) : ℝ) * modulatedEnergy (critG d) X μ := by
    have hg : Measurable (critG d) := wr13a_g_meas hs0
    have hc : Measurable (convMeasure (critG d) μ) := wr13a_conv_meas hs0 μ
    have h1 : Measurable fun X : EucConfig d 1 => ∑ i, ∑ j ∈ Finset.univ.erase i, critG d (X i - X j) :=
      Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
        hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
    have h2 : Measurable fun X : EucConfig d 1 => ∑ i, convMeasure (critG d) μ (X i) :=
      Finset.measurable_sum _ fun i _ => hc.comp (measurable_pi_apply i)
    exact ((((h1.const_mul _).sub (h2.const_mul _)).add_const _).const_mul _)
  have hint : Integrable (fun X : EucConfig d 1 => Real.exp (-b * ((1 : ℕ) : ℝ) * modulatedEnergy (critG d) X μ))
      (Measure.pi fun _ : Fin 1 => μ) :=
    Integrable.of_bound (C := Real.exp (b * Mg)) (Real.measurable_exp.comp hm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (le_trans (le_abs_self _) (hbd X)))
  refine ⟨hint, ?_, ?_⟩
  · unfold gibbsNormalizer
    calc Real.exp (-(b * Mg)) = ∫ X : EucConfig d 1, Real.exp (-(b * Mg)) ∂(Measure.pi fun _ : Fin 1 => μ) := by simp
      _ ≤ _ := integral_mono (integrable_const _) hint fun X =>
          Real.exp_le_exp.2 (by linarith [(abs_le.1 (hbd X)).1])
  · unfold gibbsNormalizer
    calc _ ≤ ∫ X : EucConfig d 1, Real.exp (b * Mg) ∂(Measure.pi fun _ : Fin 1 => μ) :=
          integral_mono hint (integrable_const _) fun X =>
            Real.exp_le_exp.2 (le_trans (le_abs_self _) (hbd X))
      _ = _ := by simp

theorem s81b_deltaN_crit (hd : 1 ≤ d) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * deltaN d ((d : ℝ) / 2) n = Real.log (Real.exp 1 * n) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp only [deltaN, lt_self_iff_false, if_false, if_true]
  field_simp

theorem s81b_Q_transfer (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) :
    ∃ q : ℕ, 2 ≤ q ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ n : ℕ, 1 ≤ n → ∀ b ∈ Set.Icc (βm / 2) βp, ∀ F : EucConfig d n → ℝ, Measurable F →
        eLpNorm F 2 (modulatedGibbs (critG d) n b (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * ((n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 16)) *
            eLpNorm F ((2 * q : ℕ) : ℝ≥0∞) (Measure.pi fun _ : Fin n => withDensityReal ρ) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < ((d : ℝ) / 2) := by linarith
  have hsd : ((d : ℝ) / 2) < d := by linarith
  obtain ⟨θ₀, hθ₀, Cp, hP⟩ := euclidean_pressure_pos hd hs0 hsd M 0 (βm / 2) (2 * βp) 0 (by positivity)
  set Cp' : ℝ := max Cp 0 with hCp'
  have hCp0 : 0 ≤ Cp' := le_max_right _ _
  set q : ℕ := max 2 ⌈24 * Cp'⌉₊ with hq
  have hq2 : 2 ≤ q := le_max_left _ _
  have hq24 : 24 * Cp' ≤ (q : ℝ) := by
    have : (⌈24 * Cp'⌉₊ : ℝ) ≤ q := by exact_mod_cast le_max_right 2 ⌈24 * Cp'⌉₊
    exact (Nat.le_ceil _).trans this
  set Mg : ℝ := max (potentialBound d ((d : ℝ) / 2) M) 0 with hMgdef
  have hMg : 0 ≤ Mg := le_max_right _ _
  refine ⟨q, hq2, Real.exp (1 / 16 + 3 * (βp * Mg)), by positivity, fun ρ hρ hM n hn b hb F hF => ?_⟩
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have : IsProbabilityMeasure (withDensityReal ρ) := wr13a_isProb_density hρ
  have hconv := wr13a_conv_le_density hd1 hs0 hsd hρ hM
  have hb0 : 0 ≤ b := by have := hb.1; linarith
  have hβp : 0 ≤ βp := hb0.trans hb.2
  have hcast : ENNReal.ofReal (2 * (q : ℝ)) = ((2 * q : ℕ) : ℝ≥0∞) := by
    rw [show (2 * (q : ℝ)) = ((2 * q : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  rw [← hcast]
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · -- one particle
    obtain rfl : n = 1 := by omega
    have hMgc : ∀ z, convMeasure (critG d) (withDensityReal ρ) z ≤ Mg := fun z =>
      (hconv z).trans (le_max_left _ _)
    obtain ⟨hw1, hl1, hh1⟩ := s81b_one_particle hd1 hMgc hMg hb0
    obtain ⟨hw2, hl2, hh2⟩ := s81b_one_particle hd1 hMgc hMg (by linarith : 0 ≤ 2 * b)
    have hbM : b * Mg ≤ βp * Mg := mul_le_mul_of_nonneg_right hb.2 hMg
    have hpM : 0 ≤ βp * Mg := mul_nonneg hβp hMg
    have hbM0 : 0 ≤ b * Mg := mul_nonneg hb0 hMg
    have hA := s81b_Q_AL hd1 (A := 2 * (βp * Mg)) (n := 1) (b := b) hw1 (by
        refine hw2.congr (Filter.Eventually.of_forall fun X => ?_); rfl)
      (hl1.trans' (Real.exp_le_exp.2 (by linarith)))
      (hh1.trans (Real.exp_le_exp.2 (by linarith)))
      (hh2.trans (Real.exp_le_exp.2 (by linarith))) q hqR F hF
    refine hA.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    have h1 : 3 * (2 * (βp * Mg)) / (2 * (q : ℝ)) ≤ 3 * (βp * Mg) := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    calc Real.exp (3 * (2 * (βp * Mg)) / (2 * (q : ℝ))) ≤ Real.exp (1 / 16 + 3 * (βp * Mg)) :=
          Real.exp_le_exp.2 (by linarith)
      _ ≤ _ := le_mul_of_one_le_right (Real.exp_pos _).le
          (Real.one_le_rpow (by norm_num) (by norm_num))
  · -- at least two particles
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpress : ∀ b' ∈ Set.Icc (βm / 2) (2 * βp),
        Integrable (fun X : EucConfig d n => Real.exp (-b' * n * modulatedEnergy (critG d) X (withDensityReal ρ)))
          (Measure.pi fun _ : Fin n => withDensityReal ρ) ∧
        Real.exp (-(Cp' * Real.log (Real.exp 1 * n))) ≤ gibbsNormalizer (critG d) n b' (withDensityReal ρ) ∧
        gibbsNormalizer (critG d) n b' (withDensityReal ρ) ≤ Real.exp (Cp' * Real.log (Real.exp 1 * n)) := by
      intro b' hb'
      obtain ⟨hG, hlog⟩ := hP ρ hρ hM (fun h => absurd h hs0.ne') (fun _ _ => 0)
        ⟨measurable_const, fun _ _ => rfl, fun x y _ => by simp⟩ n hn2 b' hb' 0 (by simp [hθ₀.le])
      have hk : (fun x y : Euc d => rieszKernel d ((d : ℝ) / 2) (x - y) - 0 * (fun (_ _ : Euc d) => (0 : ℝ)) x y) =
          fun x y => critG d (x - y) := by funext x y; simp [critG]
      rw [hk] at hG hlog
      have hZ : 0 < gibbsNormalizer (critG d) n b' (withDensityReal ρ) := hG.normalizer_pos
      have hΛ : 0 ≤ Real.log (Real.exp 1 * n) := by
        rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
        have := Real.log_nonneg hnR
        linarith
      have hlog' : |Real.log (gibbsNormalizer (critG d) n b' (withDensityReal ρ))| ≤
          Cp' * Real.log (Real.exp 1 * n) := by
        have e : Cp * (n : ℝ) * deltaN d ((d : ℝ) / 2) n = Cp * Real.log (Real.exp 1 * n) := by
          rw [mul_assoc, s81b_deltaN_crit hd1 hn]
        refine (hlog.trans (le_of_eq e)).trans ?_
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hΛ
      refine ⟨hG.weight_integrable, ?_, ?_⟩
      · exact (Real.le_log_iff_exp_le hZ).1 (by linarith [(abs_le.1 hlog').1])
      · exact (Real.log_le_iff_le_exp hZ).1 (by linarith [(abs_le.1 hlog').2])
    have hbI : b ∈ Set.Icc (βm / 2) (2 * βp) := ⟨hb.1, by linarith [hb.2]⟩
    have hb2I : 2 * b ∈ Set.Icc (βm / 2) (2 * βp) :=
      ⟨by linarith [hb.1], by linarith [hb.2]⟩
    obtain ⟨hw1, hl1, hh1⟩ := hpress b hbI
    obtain ⟨hw2, -, hh2⟩ := hpress (2 * b) hb2I
    have hA := s81b_Q_AL hd1 (n := n) (b := b) (A := Cp' * Real.log (Real.exp 1 * n)) hw1 hw2 hl1 hh1 hh2
      q hqR F hF
    refine hA.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    have hΛ : Real.log (Real.exp 1 * n) = 1 + Real.log n := by
      rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hnR
    have h1 : 3 * (Cp' * Real.log (Real.exp 1 * n)) / (2 * (q : ℝ)) ≤ Real.log (Real.exp 1 * n) / 16 := by
      rw [div_le_iff₀ (by positivity)]
      have : 0 ≤ Real.log (Real.exp 1 * n) := by rw [hΛ]; linarith
      nlinarith [mul_nonneg this (sub_nonneg.2 hq24)]
    have hn0 : (0 : ℝ) < n := by linarith
    calc Real.exp (3 * (Cp' * Real.log (Real.exp 1 * n)) / (2 * (q : ℝ)))
        ≤ Real.exp (Real.log (Real.exp 1 * n) / 16) := Real.exp_le_exp.2 h1
      _ = Real.exp (1 / 16) * (n : ℝ) ^ ((1 : ℝ) / 16) := by
          rw [hΛ, Real.rpow_def_of_pos hn0, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (1 / 16 + 3 * (βp * Mg)) * ((n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 16) := by
          refine mul_le_mul (Real.exp_le_exp.2 (by have := mul_nonneg hβp hMg; linarith)) ?_
            (Real.rpow_nonneg hn0.le _) (Real.exp_pos _).le
          exact Real.rpow_le_rpow hn0.le (by push_cast; linarith) (by norm_num)

theorem s81b_pole_product_transfer (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ q : ℕ, 2 ≤ q ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N →
      ∀ x : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ F : EucConfig d (N - 1) → ℝ, Measurable F →
        eLpNorm F 2 (pole D N x t) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ ((1 : ℝ) / 16)) *
            eLpNorm F ((2 * q : ℕ) : ℝ≥0∞) (product D (N - 1)) := by
  obtain ⟨q, hq, C2, hC2, hQ⟩ := s81b_Q_transfer hd M βm βp hβm
  obtain ⟨C3, hC31, hC3⟩ := s81b_pole_comparison hd M βm βp hβm hβ
  refine ⟨q, hq, C3 ^ ((1 : ℝ) / 2) * C2, by positivity, fun D N hN x t ht F hF => ?_⟩
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hN0 : (0 : ℝ) < N := by positivity
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hbmem : ((N - 1 : ℕ) : ℝ) * D.beta / N ∈ Set.Icc (βm / 2) βp := by
    rw [hn1]
    constructor
    · rw [le_div_iff₀ hN0]
      nlinarith [D.beta_mem.1]
    · rw [div_le_iff₀ hN0]
      nlinarith [D.beta_mem.2]
  have hQ' := hQ D.rho D.prob D.bound (N - 1) (by omega) _ hbmem F hF
  have hN1 : N - 1 + 1 = N := by omega
  rw [hN1] at hQ'
  obtain ⟨-, hdom⟩ := hC3 D N hN x t ht
  have h1 : eLpNorm F 2 (pole D N x t) ≤ eLpNorm F 2 (ENNReal.ofReal C3 •
      modulatedGibbs (critG d) (N - 1) (((N - 1 : ℕ) : ℝ) * D.beta / N) (mu D)) :=
    eLpNorm_mono_measure F hdom
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num) F _ hF.aestronglyMeasurable] at h1
  refine h1.trans ?_
  have e1 : ((1 : ℝ≥0∞) / 2).toReal = 1 / 2 := by simp
  simp only [e1, smul_eq_mul]
  calc ENNReal.ofReal C3 ^ ((1 : ℝ) / 2) * eLpNorm F 2 (modulatedGibbs (critG d) (N - 1)
          (((N - 1 : ℕ) : ℝ) * D.beta / N) (mu D))
      ≤ ENNReal.ofReal C3 ^ ((1 : ℝ) / 2) * (ENNReal.ofReal (C2 * (N : ℝ) ^ ((1 : ℝ) / 16)) *
          eLpNorm F ((2 * q : ℕ) : ℝ≥0∞) (product D (N - 1))) := mul_le_mul' le_rfl hQ'
    _ = _ := by
        rw [← mul_assoc, ENNReal.ofReal_rpow_of_nonneg (by linarith) (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

end HRS.Whole.S81b
