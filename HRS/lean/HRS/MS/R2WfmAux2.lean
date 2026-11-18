import HRS.MS.R2WfmAux1
import HRS.MS.R2QtAux1
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# HRS.MS.R2WfmAux2 -- `round2_weighted_field_moments` (S9.7), part 2: the abstract frame lemma

Packet S97.  Generic (no particle system): for a probability space `(Ω,P)` and a family of linear functionals `T ω` on test
functions with the pathwise Fourier synthesis `T ω (⟨x⟩^P ψ) = ∫ (A_ψ u_ω - B_ψ v_ω) dξ`, and `L^r(P)` bounds
`‖u(ξ)‖, ‖v(ξ)‖ ≤ κ wt(ξ)`, `r > 2`, `m ≥ d/2 + 5/2`:
`E‖T‖_{-m,P}^r ≤ C` and the same for the centred functional (`s97_frame`).  Ingredients: Cauchy–Schwarz in `ξ`
(`s97_path`), weighted Jensen (`s97_wjensen`), Tonelli (`s97_moment`), `‖∫ f‖ₑ ≤ ∫⁻ ‖f‖ₑ` for centring.
-/

open MeasureTheory
open scoped FourierTransform ENNReal NNReal

noncomputable section
namespace HRS.MS.R2Wfm
open HRS.Whole
open HRS.PDE.ToolboxRd.FourierAux (wt wt_pos one_le_wt fourierL2_schwartz continuous_wt)

variable {d : ℕ}

theorem s97_wt_ge (ξ : Euc d) : (1 + ‖ξ‖) ^ 2 / 2 ≤ wt ξ := by
  unfold wt
  have h1 : (0:ℝ) ≤ ‖ξ‖ := norm_nonneg _
  have hpi : 9 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  nlinarith [sq_nonneg (1 - ‖ξ‖), sq_nonneg ‖ξ‖, mul_nonneg h1 h1]

theorem s97_wt_int {a : ℝ} (ha : a < -(d : ℝ) / 2) : Integrable (fun ξ : Euc d => wt ξ ^ a) := by
  have hint : Integrable (fun ξ : Euc d => (1 + ‖ξ‖) ^ (-(-2 * a))) (volume : Measure (Euc d)) :=
    integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; linarith)
  refine (hint.const_mul (2 ^ (-a))).mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
  · exact (((continuous_wt (d := d)).rpow_const (fun x => Or.inl (wt_pos x).ne'))).aestronglyMeasurable
  · have ha0 : a ≤ 0 := by
      have : (0:ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have h1 : wt ξ ^ a ≤ ((1 + ‖ξ‖) ^ 2 / 2) ^ a :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (s97_wt_ge ξ) ha0
    have h2 : ((1 + ‖ξ‖) ^ 2 / 2) ^ a = 2 ^ (-a) * (1 + ‖ξ‖) ^ (-(-2 * a)) := by
      have hb : (0:ℝ) < 1 + ‖ξ‖ := by positivity
      rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_natCast, ← Real.rpow_mul hb.le]
      rw [div_eq_inv_mul]
      congr 2
      push_cast
      ring
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (wt_pos ξ) _)]
    exact h1.trans h2.le


/-- Weighted Jensen/Hölder in `ℝ≥0∞`. -/
theorem s97_wjensen {α : Type*} [MeasurableSpace α] (μ : Measure α) {h w : α → ℝ≥0∞}
    (hh : Measurable h) (hw : Measurable w) {q : ℝ} (hq : 1 < q) :
    (∫⁻ x, h x * w x ∂μ) ^ q ≤ (∫⁻ x, w x ∂μ) ^ (q - 1) * ∫⁻ x, h x ^ q * w x ∂μ := by
  have hq0 : 0 < q := by linarith
  set p := Real.conjExponent q with hp
  have hpq : q.HolderConjugate p := Real.HolderConjugate.conjExponent hq
  have hqp : p.HolderConjugate q := hpq.symm
  have hp0 : 0 < p := hqp.pos
  have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (f := fun x => h x * w x ^ (1 / q))
    (g := fun x => w x ^ (1 / p)) (hh.mul (hw.pow_const _)).aemeasurable (hw.pow_const _).aemeasurable
  have e1 : ∀ x, (h x * w x ^ (1 / q)) * w x ^ (1 / p) = h x * w x := by
    intro x
    rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
    have : 1 / q + 1 / p = 1 := by
      have := hpq.inv_add_inv_eq_one
      simpa [one_div] using this
    rw [this, ENNReal.rpow_one]
  have e2 : ∀ x, (h x * w x ^ (1 / q)) ^ q = h x ^ q * w x := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
  have e3 : ∀ x, (w x ^ (1 / p)) ^ p = w x := by
    intro x
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  simp only [Pi.mul_apply, e1, e2, e3] at h1
  calc (∫⁻ x, h x * w x ∂μ) ^ q
      ≤ (((∫⁻ x, h x ^ q * w x ∂μ) ^ (1 / q)) * (∫⁻ x, w x ∂μ) ^ (1 / p)) ^ q :=
        ENNReal.rpow_le_rpow h1 hq0.le
    _ = (∫⁻ x, w x ∂μ) ^ (q - 1) * ∫⁻ x, h x ^ q * w x ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, one_div,
          inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one, mul_comm]
        have h2 : q⁻¹ + p⁻¹ = 1 := hpq.inv_add_inv_eq_one
        have h3 : 1 / p * q = q - 1 := by
          have h4 : p⁻¹ = 1 - q⁻¹ := by linarith
          rw [one_div, h4]; field_simp
        rw [h3]


theorem s97_moment (d : ℕ) {m q κ : ℝ} (hq : 1 < q) (hm : (d : ℝ) / 2 + 5 / 2 ≤ m) (hκ : 0 ≤ κ) :
    ∃ C : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (U V : Ω → Euc d → ℝ≥0∞), Measurable (fun p : Ω × Euc d => U p.1 p.2) →
      Measurable (fun p : Ω × Euc d => V p.1 p.2) →
      (∀ ξ, ∫⁻ ω, U ω ξ ^ (2 * q) ∂P ≤ ENNReal.ofReal ((κ * wt ξ) ^ (2 * q))) →
      (∀ ξ, ∫⁻ ω, V ω ξ ^ (2 * q) ∂P ≤ ENNReal.ofReal ((κ * wt ξ) ^ (2 * q))) →
      ∫⁻ ω, (∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (-m)) * (U ω ξ ^ 2 + V ω ξ ^ 2)) ^ q ∂P ≤ ENNReal.ofReal C := by
  set γ : ℝ := ((d : ℝ) + 1) / 2 with hγ
  have hq0 : 0 < q := by linarith
  set w1 : Euc d → ℝ≥0∞ := fun ξ => ENNReal.ofReal (wt ξ ^ (-γ)) with hw1
  have hw1m : Measurable w1 :=
    ENNReal.measurable_ofReal.comp ((continuous_wt (d := d)).rpow_const (fun x => Or.inl (wt_pos x).ne')).measurable
  have hZ : (∫⁻ ξ, w1 ξ) ≠ ⊤ := by
    have := (s97_wt_int (d := d) (a := -γ) (by rw [hγ]; linarith)).lintegral_lt_top
    exact this.ne
  set a : ℝ := q * (γ + 2 - m) - γ with ha
  have ha1 : a < -(d : ℝ) / 2 := by
    have h1 : γ + 2 - m ≤ 0 := by rw [hγ]; linarith
    have h2 : q * (γ + 2 - m) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq0.le h1
    have h3 : a ≤ -γ := by rw [ha]; linarith
    rw [hγ] at h3; linarith
  set J : ℝ≥0∞ := ∫⁻ ξ : Euc d, ENNReal.ofReal (wt ξ ^ a) with hJ
  have hJt : J ≠ ⊤ := (s97_wt_int (d := d) ha1).lintegral_lt_top.ne
  set C0 : ℝ≥0∞ := (∫⁻ ξ, w1 ξ) ^ (q - 1) * (2 ^ (q - 1) * (2 * ENNReal.ofReal (κ ^ (2 * q)) * J)) with hC0
  have hC0t : C0 ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) hZ) (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)) (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hJt))
  refine ⟨C0.toReal, fun {Ω} _ P _ U V hU hV hbU hbV => ?_⟩
  rw [ENNReal.ofReal_toReal hC0t]
  set h : Ω → Euc d → ℝ≥0∞ := fun ω ξ => ENNReal.ofReal (wt ξ ^ (γ - m)) * (U ω ξ ^ 2 + V ω ξ ^ 2) with hh
  have hF : ∀ ω ξ, ENNReal.ofReal (wt ξ ^ (-m)) * (U ω ξ ^ 2 + V ω ξ ^ 2) = h ω ξ * w1 ξ := by
    intro ω ξ
    simp only [hh, hw1]
    have : wt ξ ^ (-m) = wt ξ ^ (γ - m) * wt ξ ^ (-γ) := by
      rw [← Real.rpow_add (wt_pos ξ)]; congr 1; ring
    rw [this, ENNReal.ofReal_mul (Real.rpow_nonneg (wt_pos ξ).le _)]
    ring
  have hwm : Measurable (fun ξ : Euc d => ENNReal.ofReal (wt ξ ^ (γ - m))) :=
    ENNReal.measurable_ofReal.comp ((continuous_wt (d := d)).rpow_const (fun x => Or.inl (wt_pos x).ne')).measurable
  have hUm : ∀ ω, Measurable (U ω) := fun ω => Measurable.of_uncurry_left hU
  have hVm : ∀ ω, Measurable (V ω) := fun ω => Measurable.of_uncurry_left hV
  have hhm : ∀ ω, Measurable (h ω) := fun ω => hwm.mul (((hUm ω).pow_const 2).add ((hVm ω).pow_const 2))
  have hjen : ∀ ω, (∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (-m)) * (U ω ξ ^ 2 + V ω ξ ^ 2)) ^ q ≤
      (∫⁻ ξ, w1 ξ) ^ (q - 1) * ∫⁻ ξ, h ω ξ ^ q * w1 ξ := by
    intro ω
    simp_rw [hF]
    exact s97_wjensen volume (hhm ω) hw1m hq
  set G : Ω → Euc d → ℝ≥0∞ := fun ω ξ => ENNReal.ofReal (wt ξ ^ ((γ - m) * q - γ)) *
    (2 ^ (q - 1) * (U ω ξ ^ (2 * q) + V ω ξ ^ (2 * q))) with hG
  have hpt : ∀ ω ξ, h ω ξ ^ q * w1 ξ ≤ G ω ξ := by
    intro ω ξ
    have h1 : (U ω ξ ^ 2 + V ω ξ ^ 2) ^ q ≤ 2 ^ (q - 1) * (U ω ξ ^ (2 * q) + V ω ξ ^ (2 * q)) := by
      refine (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq.le).trans (le_of_eq ?_)
      congr 2
      · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; push_cast; rfl
      · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; push_cast; rfl
    have h2 : ENNReal.ofReal (wt ξ ^ (γ - m)) ^ q * w1 ξ = ENNReal.ofReal (wt ξ ^ ((γ - m) * q - γ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) hq0.le, hw1,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) q),
        ← Real.rpow_mul (wt_pos ξ).le, ← Real.rpow_add (wt_pos ξ), ← sub_eq_add_neg]
    calc h ω ξ ^ q * w1 ξ = (ENNReal.ofReal (wt ξ ^ (γ - m)) ^ q * w1 ξ) * (U ω ξ ^ 2 + V ω ξ ^ 2) ^ q := by
          rw [hh]; simp only; rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]; ring
      _ ≤ ENNReal.ofReal (wt ξ ^ ((γ - m) * q - γ)) * (2 ^ (q - 1) * (U ω ξ ^ (2 * q) + V ω ξ ^ (2 * q))) := by
          rw [h2]; exact mul_le_mul' le_rfl h1
  have hGm : Measurable (fun p : Ω × Euc d => G p.1 p.2) := by
    have hwm2 : Measurable (fun p : Ω × Euc d => ENNReal.ofReal (wt p.2 ^ ((γ - m) * q - γ))) :=
      ENNReal.measurable_ofReal.comp (((continuous_wt (d := d)).rpow_const
        (fun x => Or.inl (wt_pos x).ne')).measurable.comp measurable_snd)
    exact hwm2.mul (measurable_const.mul ((hU.pow_const _).add (hV.pow_const _)))
  have hUξ : ∀ ξ, Measurable (fun ω => U ω ξ) := fun ξ => hU.comp (measurable_id.prodMk measurable_const)
  have hVξ : ∀ ξ, Measurable (fun ω => V ω ξ) := fun ξ => hV.comp (measurable_id.prodMk measurable_const)
  have e2 : ∀ ξ : Euc d, ENNReal.ofReal (wt ξ ^ ((γ - m) * q - γ)) * ENNReal.ofReal ((κ * wt ξ) ^ (2 * q)) =
      ENNReal.ofReal (κ ^ (2 * q)) * ENNReal.ofReal (wt ξ ^ a) := by
    intro ξ
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (wt_pos ξ).le _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hκ _), Real.mul_rpow hκ (wt_pos ξ).le]
    congr 1
    rw [mul_left_comm, ← Real.rpow_add (wt_pos ξ)]
    congr 2
    rw [ha]; ring
  have hinner : ∀ ξ, ∫⁻ ω, G ω ξ ∂P ≤
      (ENNReal.ofReal (κ ^ (2 * q)) * (2 ^ (q - 1) * 2)) * ENNReal.ofReal (wt ξ ^ a) := by
    intro ξ
    have e1 : ∫⁻ ω, G ω ξ ∂P = ENNReal.ofReal (wt ξ ^ ((γ - m) * q - γ)) *
        (2 ^ (q - 1) * (∫⁻ ω, U ω ξ ^ (2 * q) ∂P + ∫⁻ ω, V ω ξ ^ (2 * q) ∂P)) := by
      simp only [hG]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)),
        lintegral_add_left ((hUξ ξ).pow_const _)]
    calc ∫⁻ ω, G ω ξ ∂P = _ := e1
      _ ≤ ENNReal.ofReal (wt ξ ^ ((γ - m) * q - γ)) * (2 ^ (q - 1) *
          (ENNReal.ofReal ((κ * wt ξ) ^ (2 * q)) + ENNReal.ofReal ((κ * wt ξ) ^ (2 * q)))) := by
          gcongr
          · exact hbU ξ
          · exact hbV ξ
      _ = (ENNReal.ofReal (wt ξ ^ ((γ - m) * q - γ)) * ENNReal.ofReal ((κ * wt ξ) ^ (2 * q))) * (2 ^ (q - 1) * 2) := by
          ring
      _ = _ := by rw [e2 ξ]; ring
  have hZq : (∫⁻ ξ, w1 ξ) ^ (q - 1) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) hZ
  have hK : ENNReal.ofReal (κ ^ (2 * q)) * (2 ^ (q - 1) * 2) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)) (by norm_num))
  calc ∫⁻ ω, (∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (-m)) * (U ω ξ ^ 2 + V ω ξ ^ 2)) ^ q ∂P
      ≤ ∫⁻ ω, (∫⁻ ξ, w1 ξ) ^ (q - 1) * (∫⁻ ξ, G ω ξ) ∂P :=
        lintegral_mono fun ω => (hjen ω).trans (mul_le_mul' le_rfl (lintegral_mono fun ξ => hpt ω ξ))
    _ = (∫⁻ ξ, w1 ξ) ^ (q - 1) * ∫⁻ ω, (∫⁻ ξ, G ω ξ) ∂P := lintegral_const_mul' _ _ hZq
    _ = (∫⁻ ξ, w1 ξ) ^ (q - 1) * ∫⁻ ξ, ∫⁻ ω, G ω ξ ∂P := by
        rw [lintegral_lintegral_swap hGm.aemeasurable]
    _ ≤ (∫⁻ ξ, w1 ξ) ^ (q - 1) * ∫⁻ ξ, (ENNReal.ofReal (κ ^ (2 * q)) * (2 ^ (q - 1) * 2)) *
          ENNReal.ofReal (wt ξ ^ a) := mul_le_mul' le_rfl (lintegral_mono hinner)
    _ = C0 := by
        rw [lintegral_const_mul' _ _ hK, hC0, hJ]
        ring


theorem s97_cs_real (A B u v : ℝ) : |A * u - B * v| ≤ Real.sqrt (A ^ 2 + B ^ 2) * Real.sqrt (u ^ 2 + v ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg (A * v + B * u)]

theorem s97_path (m : ℕ) (Pw : ℝ) (T : (Euc d → ℝ) → ℝ) (u v : Euc d → ℝ)
    (hu : Measurable u) (hv : Measurable v)
    (hsyn : ∀ ψ : SchwartzMap (Euc d) ℝ, sobolevNormE (m : ℝ) (fun x => ψ x) ≤ 1 →
      T (fun x => jbracket x ^ Pw * ψ x) = ∫ ξ, (s97_A ψ ξ * u ξ - s97_B ψ ξ * v ξ)) :
    r2NegSobNorm m Pw T ≤ (∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (-(m : ℝ))) *
      (ENNReal.ofReal |u ξ| ^ 2 + ENNReal.ofReal |v ξ| ^ 2)) ^ (1 / 2 : ℝ) := by
  unfold r2NegSobNorm
  refine iSup₂_le fun ψ hψ => ?_
  obtain ⟨hA, hB, hint, hinv, hder, hnorm⟩ := s97_synth ψ (m : ℝ) hψ
  rw [hsyn ψ hψ]
  set g1 : Euc d → ℝ≥0∞ := fun ξ => ENNReal.ofReal (wt ξ ^ ((m : ℝ) / 2) * Real.sqrt (s97_A ψ ξ ^ 2 + s97_B ψ ξ ^ 2)) with hg1
  set g2 : Euc d → ℝ≥0∞ := fun ξ => ENNReal.ofReal (wt ξ ^ (-(m : ℝ) / 2) * Real.sqrt (u ξ ^ 2 + v ξ ^ 2)) with hg2
  have hwc : ∀ t : ℝ, Continuous (fun ξ : Euc d => wt ξ ^ t) := fun t =>
    (continuous_wt (d := d)).rpow_const (fun x => Or.inl (wt_pos x).ne')
  have hg1m : Measurable g1 :=
    ENNReal.measurable_ofReal.comp (((hwc _).mul (by have := hA; have := hB; fun_prop)).measurable)
  have hg2m : Measurable g2 :=
    ENNReal.measurable_ofReal.comp (((hwc _).measurable.mul ((hu.pow_const 2).add (hv.pow_const 2)).sqrt))
  have hpt : ∀ ξ, ‖s97_A ψ ξ * u ξ - s97_B ψ ξ * v ξ‖ₑ ≤ g1 ξ * g2 ξ := by
    intro ξ
    rw [Real.enorm_eq_ofReal_abs, hg1, hg2, ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (Real.sqrt_nonneg _))]
    refine ENNReal.ofReal_le_ofReal ?_
    refine (s97_cs_real _ _ _ _).trans (le_of_eq ?_)
    have : wt ξ ^ ((m : ℝ) / 2) * wt ξ ^ (-(m : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add (wt_pos ξ)]; rw [show (m : ℝ) / 2 + -(m : ℝ) / 2 = 0 by ring, Real.rpow_zero]
    calc Real.sqrt (s97_A ψ ξ ^ 2 + s97_B ψ ξ ^ 2) * Real.sqrt (u ξ ^ 2 + v ξ ^ 2)
        = (wt ξ ^ ((m : ℝ) / 2) * wt ξ ^ (-(m : ℝ) / 2)) * (Real.sqrt (s97_A ψ ξ ^ 2 + s97_B ψ ξ ^ 2) * Real.sqrt (u ξ ^ 2 + v ξ ^ 2)) := by rw [this, one_mul]
      _ = _ := by ring
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure (Euc d))
    (Real.HolderConjugate.two_two) hg1m.aemeasurable hg2m.aemeasurable
  have hg1sq : ∀ ξ, g1 ξ ^ (2 : ℝ) = ENNReal.ofReal (wt ξ ^ (m : ℝ) * (s97_A ψ ξ ^ 2 + s97_B ψ ξ ^ 2)) := by
    intro ξ
    rw [hg1]; simp only
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (Real.sqrt_nonneg _)),
      mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (wt_pos ξ).le]
    congr 3
    push_cast; ring
  have hg2sq : ∀ ξ, g2 ξ ^ (2 : ℝ) = ENNReal.ofReal (wt ξ ^ (-(m : ℝ))) *
      (ENNReal.ofReal |u ξ| ^ 2 + ENNReal.ofReal |v ξ| ^ 2) := by
    intro ξ
    rw [hg2]; simp only
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (Real.sqrt_nonneg _)),
      mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (wt_pos ξ).le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (wt_pos ξ).le _), ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, sq_abs]
    congr 3
    push_cast; ring
  have h1 : ∫⁻ ξ, g1 ξ ^ (2 : ℝ) ≤ 1 := by
    simp_rw [hg1sq]; exact hnorm
  calc ENNReal.ofReal |∫ ξ, (s97_A ψ ξ * u ξ - s97_B ψ ξ * v ξ)|
      = ‖∫ ξ, (s97_A ψ ξ * u ξ - s97_B ψ ξ * v ξ)‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
    _ ≤ ∫⁻ ξ, ‖s97_A ψ ξ * u ξ - s97_B ψ ξ * v ξ‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ ξ, (g1 * g2) ξ := lintegral_mono hpt
    _ ≤ _ := hCS
    _ ≤ 1 ^ (1 / (2 : ℝ)) * _ := by
        gcongr
    _ = _ := by
        simp_rw [hg2sq]; simp


theorem s97_lint_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ) (hf : AEStronglyMeasurable f P) {r : ℝ} (hr : 0 < r) :
    ∫⁻ ω, ENNReal.ofReal |f ω| ^ r ∂P = eLpNorm f (ENNReal.ofReal r) P ^ r := by
  have h0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
  rw [eLpNorm_eq_eLpNorm' h0 ENNReal.ofReal_ne_top hf, ENNReal.toReal_ofReal hr.le,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hr]
  simp_rw [Real.enorm_eq_ofReal_abs]

theorem s97_negnorm_sub (m : ℕ) (Pw : ℝ) (f g : (Euc d → ℝ) → ℝ) :
    r2NegSobNorm m Pw (fun φ => f φ - g φ) ≤ r2NegSobNorm m Pw f + r2NegSobNorm m Pw g := by
  unfold r2NegSobNorm
  refine iSup₂_le fun ψ hψ => ?_
  calc ENNReal.ofReal |f (fun x => jbracket x ^ Pw * ψ x) - g (fun x => jbracket x ^ Pw * ψ x)|
      ≤ ENNReal.ofReal |f (fun x => jbracket x ^ Pw * ψ x)| + ENNReal.ofReal |g (fun x => jbracket x ^ Pw * ψ x)| := by
        rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (abs_sub _ _)
    _ ≤ _ := add_le_add (le_iSup₂ (f := fun (ψ : SchwartzMap (Euc d) ℝ) (_ : sobolevNormE (m : ℝ) (fun x => ψ x) ≤ 1) =>
          ENNReal.ofReal |f (fun x => jbracket x ^ Pw * ψ x)|) ψ hψ)
        (le_iSup₂ (f := fun (ψ : SchwartzMap (Euc d) ℝ) (_ : sobolevNormE (m : ℝ) (fun x => ψ x) ≤ 1) =>
          ENNReal.ofReal |g (fun x => jbracket x ^ Pw * ψ x)|) ψ hψ)


theorem s97_frame (d : ℕ) (m : ℕ) (hm : (d : ℝ) / 2 + 5 / 2 ≤ m) {r κ : ℝ} (hr : 2 < r) (hκ : 0 ≤ κ) :
    ∃ C : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Pw : ℝ)
      (T : Ω → (Euc d → ℝ) → ℝ) (u v : Ω → Euc d → ℝ),
      Measurable (fun p : Ω × Euc d => u p.1 p.2) → Measurable (fun p : Ω × Euc d => v p.1 p.2) →
      (∀ ω (ψ : SchwartzMap (Euc d) ℝ), sobolevNormE (m : ℝ) (fun x => ψ x) ≤ 1 →
        T ω (fun x => jbracket x ^ Pw * ψ x) = ∫ ξ, (s97_A ψ ξ * u ω ξ - s97_B ψ ξ * v ω ξ)) →
      (∀ ξ, eLpNorm (fun ω => u ω ξ) (ENNReal.ofReal r) P ≤ ENNReal.ofReal (κ * wt ξ)) →
      (∀ ξ, eLpNorm (fun ω => v ω ξ) (ENNReal.ofReal r) P ≤ ENNReal.ofReal (κ * wt ξ)) →
      ∃ G G' : Ω → ℝ≥0∞, Measurable G ∧ Measurable G' ∧
        (∀ ω, r2NegSobNorm m Pw (T ω) ^ r ≤ G ω) ∧
        (∀ ω, r2NegSobNorm m Pw (fun φ => T ω φ - ∫ Y, T Y φ ∂P) ^ r ≤ G' ω) ∧
        ∫⁻ ω, G ω ∂P ≤ ENNReal.ofReal C ∧ ∫⁻ ω, G' ω ∂P ≤ ENNReal.ofReal C := by
  have hq : 1 < r / 2 := by linarith
  have hr0 : 0 < r := by linarith
  obtain ⟨C1, hC1⟩ := s97_moment d (m := (m : ℝ)) hq hm hκ
  refine ⟨2 ^ r * max C1 0, fun {Ω} _ P _ Pw T u v hu hv hsyn hbu hbv => ?_⟩
  set U : Ω → Euc d → ℝ≥0∞ := fun ω ξ => ENNReal.ofReal |u ω ξ| with hUdef
  set V : Ω → Euc d → ℝ≥0∞ := fun ω ξ => ENNReal.ofReal |v ω ξ| with hVdef
  have hU : Measurable (fun p : Ω × Euc d => U p.1 p.2) :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hu)
  have hV : Measurable (fun p : Ω × Euc d => V p.1 p.2) :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hv)
  have h2q : 2 * (r / 2) = r := by ring
  have hwtc : ∀ ξ : Euc d, (0:ℝ) ≤ κ * wt ξ := fun ξ => mul_nonneg hκ (wt_pos ξ).le
  have hbU : ∀ ξ, ∫⁻ ω, U ω ξ ^ (2 * (r / 2)) ∂P ≤ ENNReal.ofReal ((κ * wt ξ) ^ (2 * (r / 2))) := by
    intro ξ
    rw [h2q]
    have hmeas : AEStronglyMeasurable (fun ω => u ω ξ) P :=
      (hu.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    have := s97_lint_eq P (fun ω => u ω ξ) hmeas hr0
    simp only [hUdef]
    rw [this, ← ENNReal.ofReal_rpow_of_nonneg (hwtc ξ) hr0.le]
    exact ENNReal.rpow_le_rpow (hbu ξ) hr0.le
  have hbV : ∀ ξ, ∫⁻ ω, V ω ξ ^ (2 * (r / 2)) ∂P ≤ ENNReal.ofReal ((κ * wt ξ) ^ (2 * (r / 2))) := by
    intro ξ
    rw [h2q]
    have hmeas : AEStronglyMeasurable (fun ω => v ω ξ) P :=
      (hv.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    have := s97_lint_eq P (fun ω => v ω ξ) hmeas hr0
    simp only [hVdef]
    rw [this, ← ENNReal.ofReal_rpow_of_nonneg (hwtc ξ) hr0.le]
    exact ENNReal.rpow_le_rpow (hbv ξ) hr0.le
  have hmom := hC1 P U V hU hV hbU hbV
  set I : Ω → ℝ≥0∞ := fun ω => ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (-(m : ℝ))) * (U ω ξ ^ 2 + V ω ξ ^ 2) with hI
  have hIm : Measurable I := by
    have hw : Measurable (fun ξ : Euc d => ENNReal.ofReal (wt ξ ^ (-(m : ℝ)))) :=
      ENNReal.measurable_ofReal.comp ((continuous_wt (d := d)).rpow_const (fun x => Or.inl (wt_pos x).ne')).measurable
    exact Measurable.lintegral_prod_right' (f := fun p : Ω × Euc d =>
      ENNReal.ofReal (wt p.2 ^ (-(m : ℝ))) * (U p.1 p.2 ^ 2 + V p.1 p.2 ^ 2))
      ((hw.comp measurable_snd).mul ((hU.pow_const 2).add (hV.pow_const 2)))
  set N : Ω → ℝ≥0∞ := fun ω => I ω ^ (1 / 2 : ℝ) with hN
  have hNm : Measurable N := hIm.pow_const _
  have hpath : ∀ ω, r2NegSobNorm m Pw (T ω) ≤ N ω := fun ω =>
    s97_path m Pw (T ω) (u ω) (v ω) (hu.comp (measurable_const.prodMk measurable_id))
      (hv.comp (measurable_const.prodMk measurable_id)) (hsyn ω)
  have hNr : ∀ ω, N ω ^ r = I ω ^ (r / 2) := by
    intro ω; rw [hN]; simp only; rw [← ENNReal.rpow_mul]; congr 1; ring
  have hNint : ∫⁻ ω, N ω ^ r ∂P ≤ ENNReal.ofReal C1 := by
    simp_rw [hNr]; exact hmom
  have hC : ENNReal.ofReal C1 ≤ ENNReal.ofReal (max C1 0) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have h2r : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 ^ r) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow (by norm_num) hr0.le)
  have hfin : ENNReal.ofReal (2 ^ r * max C1 0) = ENNReal.ofReal (2 ^ r) * ENNReal.ofReal (max C1 0) :=
    ENNReal.ofReal_mul (by positivity)
  have h2rr : (2 : ℝ≥0∞) ^ r = ENNReal.ofReal (2 ^ r) := by
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [h2, ENNReal.ofReal_rpow_of_nonneg (by norm_num) hr0.le]
  have hE : r2NegSobNorm m Pw (fun φ => ∫ Y, T Y φ ∂P) ≤ ∫⁻ ω, N ω ∂P := by
    unfold r2NegSobNorm
    refine iSup₂_le fun ψ hψ => ?_
    calc ENNReal.ofReal |∫ Y, T Y (fun x => jbracket x ^ Pw * ψ x) ∂P|
        = ‖∫ Y, T Y (fun x => jbracket x ^ Pw * ψ x) ∂P‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
      _ ≤ ∫⁻ Y, ‖T Y (fun x => jbracket x ^ Pw * ψ x)‖ₑ ∂P := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ ω, N ω ∂P := by
        refine lintegral_mono fun Y => ?_
        rw [Real.enorm_eq_ofReal_abs]
        refine le_trans ?_ (hpath Y)
        exact le_iSup₂ (f := fun (ψ : SchwartzMap (Euc d) ℝ) (_ : sobolevNormE (m : ℝ) (fun x => ψ x) ≤ 1) =>
          ENNReal.ofReal |T Y (fun x => jbracket x ^ Pw * ψ x)|) ψ hψ
  set M1 : ℝ≥0∞ := ∫⁻ ω, N ω ∂P with hM1
  have hJ : M1 ^ r ≤ ∫⁻ ω, N ω ^ r ∂P := by
    have := HRS.MS.R2Mt.s92_jensen_enn P hNm (q := r) (by linarith)
    exact this
  have hcen : ∀ ω, r2NegSobNorm m Pw (fun φ => T ω φ - ∫ Y, T Y φ ∂P) ≤ N ω + M1 := fun ω =>
    (s97_negnorm_sub m Pw (T ω) (fun φ => ∫ Y, T Y φ ∂P)).trans (add_le_add (hpath ω) hE)
  refine ⟨fun ω => N ω ^ r, fun ω => 2 ^ (r - 1) * (N ω ^ r + M1 ^ r), hNm.pow_const _,
    measurable_const.mul ((hNm.pow_const _).add measurable_const),
    fun ω => ENNReal.rpow_le_rpow (hpath ω) hr0.le,
    fun ω => (ENNReal.rpow_le_rpow (hcen ω) hr0.le).trans
      (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by linarith)), ?_, ?_⟩
  · calc ∫⁻ ω, N ω ^ r ∂P ≤ ENNReal.ofReal C1 := hNint
      _ ≤ ENNReal.ofReal (max C1 0) := hC
      _ ≤ _ := by rw [hfin]; exact le_mul_of_one_le_left bot_le h2r
  · calc ∫⁻ ω, 2 ^ (r - 1) * (N ω ^ r + M1 ^ r) ∂P
        = 2 ^ (r - 1) * (∫⁻ ω, N ω ^ r ∂P + M1 ^ r) := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)),
            lintegral_add_left (hNm.pow_const _)]
          simp
      _ ≤ 2 ^ (r - 1) * (∫⁻ ω, N ω ^ r ∂P + ∫⁻ ω, N ω ^ r ∂P) := by gcongr
      _ = 2 ^ r * ∫⁻ ω, N ω ^ r ∂P := by
          have : (2 : ℝ≥0∞) ^ r = 2 ^ (r - 1) * 2 := by
            conv_lhs => rw [show r = (r - 1) + 1 by ring]
            rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by norm_num), ENNReal.rpow_one]
          rw [this]; ring
      _ ≤ 2 ^ r * ENNReal.ofReal C1 := by gcongr
      _ ≤ _ := by
          rw [hfin, ← h2rr]
          exact mul_le_mul' le_rfl hC

end HRS.MS.R2Wfm
end
