import HRS.Commutator.Whole.ExternalAuxHLS10

/-!
# Assembly of the fractional-derivative representation (packet X-HLS, part 11)
-/

open MeasureTheory Filter Topology Metric Real Set
open scoped ENNReal NNReal FourierTransform ContDiff

noncomputable section

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

lemma cmxHLS_integrable_tsum {ι : Type*} [Countable ι] {F : ι → Euc d → ℂ}
    (hF_int : ∀ i, Integrable (F i)) (hs : Summable fun i => ∫ a, ‖F i a‖) :
    Integrable (fun a => ∑' i, F i a) := by
  have hmeas : AEStronglyMeasurable (fun a => ∑' i, F i a) volume :=
    (AEMeasurable.tsum (fun i => (hF_int i).1.aemeasurable)).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  have h1 : ∀ i, ∫⁻ a, ‖F i a‖ₑ = ‖∫ a, ‖F i a‖‖ₑ := by
    intro i
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF_int i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun a => norm_nonneg (F i a)))]
    simp only [coe_nnnorm]
  have h2 : ∑' i, ∫⁻ a, ‖F i a‖ₑ ≠ ⊤ := by
    rw [funext h1]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)
  unfold HasFiniteIntegral
  calc ∫⁻ a, ‖∑' i, F i a‖ₑ ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ := lintegral_mono fun a => enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ a, ‖F i a‖ₑ := lintegral_tsum fun i => (hF_int i).1.enorm
    _ < ⊤ := lt_top_iff_ne_top.2 h2


lemma cmxHLS_schwartz_lintegral {r : ℝ} (hr : 0 < r) (ψ : SchwartzMap (Euc d) ℂ) :
    ∫⁻ x, ‖ψ x‖ₑ ^ r ≠ ⊤ := by
  have h1 : eLpNorm (⇑ψ) (ENNReal.ofReal r) volume < ⊤ :=
    (ψ.memLp (ENNReal.ofReal r) volume).eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr) ENNReal.ofReal_ne_top
    ψ.continuous.aestronglyMeasurable, ENNReal.toReal_ofReal hr.le] at h1
  intro h
  rw [h, ENNReal.top_rpow_of_pos (by positivity)] at h1
  exact lt_irrefl _ h1

lemma cmxHLS_integrable_mul_Lq {q : ℝ} (hq : 1 < q) {W : Euc d → ℝ} (hWm : Measurable W)
    (hW : ∫⁻ x, ‖W x‖ₑ ^ q ≠ ⊤) (ψ : SchwartzMap (Euc d) ℂ) :
    Integrable (fun x => ((W x : ℝ) : ℂ) * ψ x) := by
  have hHq := Real.HolderConjugate.conjExponent hq
  have hq'0 : 0 < q.conjExponent := by have := hHq.symm.lt; linarith
  refine ⟨((Complex.measurable_ofReal.comp hWm).mul ψ.continuous.measurable).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hψ := cmxHLS_schwartz_lintegral hq'0 ψ
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hHq (f := fun x : Euc d => ‖W x‖ₑ)
    (g := fun x : Euc d => ‖ψ x‖ₑ) hWm.enorm.aemeasurable ψ.continuous.measurable.enorm.aemeasurable
  simp only [Pi.mul_apply] at hH
  have hrw : ∀ x : Euc d, ‖((W x : ℝ) : ℂ) * ψ x‖ₑ = ‖W x‖ₑ * ‖ψ x‖ₑ := fun x => by
    rw [enorm_mul, cmxHLS_enorm_ofReal]
  simp_rw [hrw]
  refine lt_of_le_of_lt hH (ENNReal.mul_lt_top ?_ ?_)
  · exact ENNReal.rpow_lt_top_of_nonneg (by have := hHq.pos; positivity) hW
  · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hψ


lemma cmxHLS_hint_rpow {s : ℝ} (hs : 0 ≤ s) (F : SchwartzMap (Euc d) ℂ) :
    Integrable (fun ξ : Euc d => (2 * π * ‖ξ‖) ^ s * ‖F ξ‖) := by
  have h := (cmxHLS_integrable_rpow_schwartz hs F).const_mul ((2 * π) ^ s)
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [Real.mul_rpow (by positivity) (norm_nonneg _)]
  ring

theorem cmxHLS_lhs_sum (hd : 1 ≤ d) {β : ℝ} (hβ : 1 < β) {v : Euc d → ℝ} (hvc : Continuous v)
    {A : ℝ} (hv : ∀ x, |v x| ≤ A * (1 + ‖x‖)) (F : SchwartzMap (Euc d) ℂ) :
    Integrable (fun x : Euc d => ((v x : ℝ) : ℂ) *
        𝓕⁻ (fun ξ : Euc d => (((2 * π * ‖ξ‖) ^ β : ℝ) : ℂ) * F ξ) x) ∧
      HasSum (fun j : ℤ => ∫ x : Euc d, ((v x : ℝ) : ℂ) * cmxHLS_piece β (⇑F) j x)
        (∫ x : Euc d, ((v x : ℝ) : ℂ) *
          𝓕⁻ (fun ξ : Euc d => (((2 * π * ‖ξ‖) ^ β : ℝ) : ℂ) * F ξ) x) := by
  have hA : 0 ≤ A := by
    have := hv 0
    simp only [norm_zero, add_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  obtain ⟨M, hM0, hM⟩ := cmxHLS_piece_L1 F β (d + 2) (⌈β⌉₊ + 1) (by omega) (by omega)
  obtain ⟨hf, -⟩ := cmxHLS_schwartz_dec F
  set Fj : ℤ → Euc d → ℂ := fun j x => ((v x : ℝ) : ℂ) * cmxHLS_piece β (⇑F) j x with hFj
  have hpc : ∀ j, Continuous (cmxHLS_piece β (⇑F) j) := fun j => cmxHLS_piece_continuous hf β j
  have hnorm : ∀ j x, ‖Fj j x‖ ≤ A * ((1 + ‖x‖) * ‖cmxHLS_piece β (⇑F) j x‖) := by
    intro j x
    rw [hFj]; simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := hv x
    calc |v x| * ‖cmxHLS_piece β (⇑F) j x‖ ≤ (A * (1 + ‖x‖)) * ‖cmxHLS_piece β (⇑F) j x‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := by ring
  have hFmeas : ∀ j, AEStronglyMeasurable (Fj j) volume := fun j =>
    (((Complex.continuous_ofReal.comp hvc).mul (hpc j))).aestronglyMeasurable
  have hFint : ∀ j, Integrable (Fj j) := fun j =>
    (((hM j).1).const_mul A).mono' (hFmeas j) (Eventually.of_forall fun x => hnorm j x)
  have hint2 : ∀ j, ∫ x, ‖Fj j x‖ ≤ A * (M * cmxHLS_t (β - 1) (⌈β⌉₊ + 1 - 1) j) := by
    intro j
    calc ∫ x, ‖Fj j x‖ ≤ ∫ x, A * ((1 + ‖x‖) * ‖cmxHLS_piece β (⇑F) j x‖) :=
          integral_mono (hFint j).norm (((hM j).1).const_mul A) (fun x => hnorm j x)
      _ = A * ∫ x, (1 + ‖x‖) * ‖cmxHLS_piece β (⇑F) j x‖ := integral_const_mul _ _
      _ ≤ A * (M * cmxHLS_t (β - 1) (⌈β⌉₊ + 1 - 1) j) :=
          mul_le_mul_of_nonneg_left (hM j).2 hA
  have ht : Summable (cmxHLS_t (β - 1) (⌈β⌉₊ + 1 - 1)) := by
    refine cmxHLS_t_summable (by linarith) ?_
    have := Nat.le_ceil β
    simp only [Nat.add_sub_cancel]
    push_cast
    linarith
  have hsum : Summable fun j => ∫ x, ‖Fj j x‖ :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun x => norm_nonneg _) hint2
      ((ht.mul_left M).mul_left A)
  have hint : Integrable (fun ξ : Euc d => (2 * π * ‖ξ‖) ^ β * ‖F ξ‖) :=
    cmxHLS_hint_rpow (by linarith) F
  have hlim : ∀ x : Euc d, ∑' j, Fj j x = ((v x : ℝ) : ℂ) *
      𝓕⁻ (fun ξ : Euc d => (((2 * π * ‖ξ‖) ^ β : ℝ) : ℂ) * F ξ) x := by
    intro x
    exact ((cmxHLS_piece_hasSum hd hf β hint x).mul_left _).tsum_eq
  have hI := cmxHLS_integrable_tsum hFint hsum
  have hH := hasSum_integral_of_summable_integral_norm hFint hsum
  simp only [hlim] at hI hH
  exact ⟨hI, hH⟩


theorem cmxHLS_rhs_sum (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) {W : Euc d → ℝ} (hWm : Measurable W)
    (hW : ∫⁻ x, ‖W x‖ₑ ^ q ≠ ⊤) (F : SchwartzMap (Euc d) ℂ) :
    HasSum (fun j : ℤ => ∫ x : Euc d, ((W x : ℝ) : ℂ) * cmxHLS_piece 0 (⇑F) j x)
      (∫ x : Euc d, ((W x : ℝ) : ℂ) *
        𝓕⁻ (fun ξ : Euc d => (((2 * π * ‖ξ‖) ^ (0 : ℝ) : ℝ) : ℂ) * F ξ) x) := by
  have hHq := Real.HolderConjugate.conjExponent hq
  set q' : ℝ := q.conjExponent with hq'
  have hq'1 : 1 < q' := hHq.symm.lt
  have hq'0 : 0 < q' := by linarith
  have hq0 : 0 < q := by linarith
  set e : ℝ := (0 : ℝ) + d - d / q' with he
  have he0 : 0 < e := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have : d / q' < d := by rw [div_lt_iff₀ hq'0]; nlinarith
    rw [he]; linarith
  obtain ⟨M, hM0, hM⟩ := cmxHLS_piece_Lr F 0 (d + 2) (⌈e⌉₊ + 1) (by omega) hq'1.le
  obtain ⟨hf, -⟩ := cmxHLS_schwartz_dec F
  set Fj : ℤ → Euc d → ℂ := fun j x => ((W x : ℝ) : ℂ) * cmxHLS_piece 0 (⇑F) j x with hFj
  have hpc : ∀ j, cmxHLS_piece 0 (⇑F) j = ⇑(cmxHLS_pieceS 0 F j) := fun j =>
    (cmxHLS_pieceS_coe 0 F j).symm
  have hFint : ∀ j, Integrable (Fj j) := fun j => by
    rw [hFj]; simp only [hpc j]
    exact cmxHLS_integrable_mul_Lq hq hWm hW _
  set B : ℝ≥0∞ := (∫⁻ x, ‖W x‖ₑ ^ q) ^ (1 / q) with hB
  have hBt : B ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hW
  have hint2 : ∀ j, ∫ x, ‖Fj j x‖ ≤ B.toReal * (M * cmxHLS_t e (⌈e⌉₊ + 1) j) := by
    intro j
    have hmeas : AEStronglyMeasurable (Fj j) volume := (hFint j).1
    rw [integral_norm_eq_lintegral_enorm hmeas]
    have hrw : ∀ x : Euc d, ‖Fj j x‖ₑ = ‖W x‖ₑ * ‖cmxHLS_piece 0 (⇑F) j x‖ₑ := fun x => by
      rw [hFj]; simp only [enorm_mul, cmxHLS_enorm_ofReal]
    simp_rw [hrw]
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hHq (f := fun x : Euc d => ‖W x‖ₑ)
      (g := fun x : Euc d => ‖cmxHLS_piece 0 (⇑F) j x‖ₑ) hWm.enorm.aemeasurable
      (cmxHLS_piece_continuous hf 0 j).measurable.enorm.aemeasurable
    simp only [Pi.mul_apply] at hH
    have hLr := hM j
    have hpos : 0 ≤ M * cmxHLS_t e (⌈e⌉₊ + 1) j := by
      have : 0 ≤ cmxHLS_t e (⌈e⌉₊ + 1) j := by unfold cmxHLS_t; positivity
      positivity
    have h2 : (∫⁻ x, ‖cmxHLS_piece 0 (⇑F) j x‖ₑ ^ q') ^ (1 / q') ≤
        ENNReal.ofReal (M * cmxHLS_t e (⌈e⌉₊ + 1) j) := by
      calc (∫⁻ x, ‖cmxHLS_piece 0 (⇑F) j x‖ₑ ^ q') ^ (1 / q')
          ≤ (ENNReal.ofReal ((M * cmxHLS_t e (⌈e⌉₊ + 1) j) ^ q')) ^ (1 / q') :=
            ENNReal.rpow_le_rpow hLr (by positivity)
        _ = ENNReal.ofReal (M * cmxHLS_t e (⌈e⌉₊ + 1) j) := by
            rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
              ← Real.rpow_mul hpos, mul_one_div_cancel hq'0.ne', Real.rpow_one]
    have h3 : ∫⁻ x, ‖W x‖ₑ * ‖cmxHLS_piece 0 (⇑F) j x‖ₑ ≤
        B * ENNReal.ofReal (M * cmxHLS_t e (⌈e⌉₊ + 1) j) :=
      hH.trans (mul_le_mul_right h2 _)
    have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top hBt ENNReal.ofReal_ne_top) h3
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos] at h4
    exact h4
  have ht : Summable (cmxHLS_t e (⌈e⌉₊ + 1)) := by
    refine cmxHLS_t_summable he0 ?_
    have := Nat.le_ceil e
    push_cast
    linarith
  have hsum : Summable fun j => ∫ x, ‖Fj j x‖ :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun x => norm_nonneg _) hint2
      ((ht.mul_left M).mul_left B.toReal)
  have hint : Integrable (fun ξ : Euc d => (2 * π * ‖ξ‖) ^ (0 : ℝ) * ‖F ξ‖) := by
    have := (F.integrable (μ := volume)).norm
    simpa using this
  have hlim : ∀ x : Euc d, ∑' j, Fj j x = ((W x : ℝ) : ℂ) *
      𝓕⁻ (fun ξ : Euc d => (((2 * π * ‖ξ‖) ^ (0 : ℝ) : ℝ) : ℂ) * F ξ) x := by
    intro x
    exact ((cmxHLS_piece_hasSum hd hf 0 hint x).mul_left _).tsum_eq
  have hH := hasSum_integral_of_summable_integral_norm hFint hsum
  simp only [hlim] at hH
  exact hH


/-- `(2π|ξ|)^{β+σ} · sym_{-σ} = sym_β`. -/
lemma cmxHLS_sym_shift (β σ : ℝ) (f : Euc d → ℂ) (j : ℤ) (ξ : Euc d) :
    (((2 * π * ‖ξ‖) ^ (β + σ) : ℝ) : ℂ) * cmxHLS_sym (-σ) f j ξ = cmxHLS_sym β f j ξ := by
  by_cases hξ : ξ = 0
  · subst hξ
    unfold cmxHLS_sym
    rw [smul_zero, cmxMY_rho_eq_zero_of_le (by simp)]
    simp
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    unfold cmxHLS_sym
    have : (2 * π * ‖ξ‖) ^ (β + σ) * (2 * π * ‖ξ‖) ^ (-σ) = (2 * π * ‖ξ‖) ^ β := by
      rw [← Real.rpow_add (by positivity)]; congr 1; ring
    rw [← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    rw [← mul_assoc, this]

lemma cmxHLS_piece_hyp {α β σ : ℝ} (hαβ : α = β + σ) {v w : Euc d → ℝ}
    (hrep : IsFracDerivRep α v w) (F : SchwartzMap (Euc d) ℂ) (j : ℤ) :
    Integrable (fun x : Euc d => ((v x : ℝ) : ℂ) * cmxHLS_piece β (⇑F) j x) ∧
      ∫ x : Euc d, ((v x : ℝ) : ℂ) * cmxHLS_piece β (⇑F) j x =
        ∫ x : Euc d, ((w x : ℝ) : ℂ) * cmxHLS_piece (-σ) (⇑F) j x := by
  obtain ⟨h1, h2, h3⟩ := hrep (cmxHLS_pieceS (-σ) F j)
  have hfun : (fun ξ : Euc d => (((2 * π * ‖ξ‖) ^ α : ℝ) : ℂ) *
      𝓕 (⇑(cmxHLS_pieceS (-σ) F j) : Euc d → ℂ) ξ) = cmxHLS_sym β (⇑F) j := by
    funext ξ
    rw [cmxHLS_fourier_pieceS, hαβ, cmxHLS_sym_shift]
  have hpc : (⇑(cmxHLS_pieceS (-σ) F j) : Euc d → ℂ) = cmxHLS_piece (-σ) (⇑F) j :=
    cmxHLS_pieceS_coe (-σ) F j
  rw [hfun] at h1 h3
  rw [hpc] at h3
  exact ⟨h1, h3⟩


/-- `𝓕⁻(𝓕 φ) = φ` for the zeroth multiplier. -/
lemma cmxHLS_inv_zero (φ : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    𝓕⁻ (fun ξ : Euc d => (((2 * π * ‖ξ‖) ^ (0 : ℝ) : ℝ) : ℂ) * (𝓕 φ : SchwartzMap (Euc d) ℂ) ξ) x =
      φ x := by
  have h : (𝓕⁻ (𝓕 φ : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ) = φ :=
    FourierTransform.fourierInv_fourier_eq φ
  have h2 : (𝓕⁻ (𝓕 φ : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ) x = φ x := by rw [h]
  rw [SchwartzMap.fourierInv_coe] at h2
  have h3 : (fun ξ : Euc d => (((2 * π * ‖ξ‖) ^ (0 : ℝ) : ℝ) : ℂ) *
      (𝓕 φ : SchwartzMap (Euc d) ℂ) ξ) = ⇑(𝓕 φ : SchwartzMap (Euc d) ℂ) := by
    funext ξ; simp
  rw [h3]
  exact h2

/-- **The fractional derivative representation**: `|∇|^{β+σ} v = w` with `w ∈ L^p` and `v` of linear
growth gives `|∇|^β v = c_σ I_σ w`. -/
theorem cmxHLS_fracRep (hd : 1 ≤ d) {σ p q β : ℝ} (hσ : 0 < σ) (hσd : σ < d) (hp : 1 < p)
    (hpq : p < q) (hrel : 1 / q = 1 / p - σ / d) (hβ : 1 < β) {v w : Euc d → ℝ}
    (hvc : Continuous v) {A : ℝ} (hv : ∀ x, |v x| ≤ A * (1 + ‖x‖)) (hwm : Measurable w)
    (hwp : ∫⁻ y, ‖w y‖ₑ ^ p ≠ ⊤) (hrep : IsFracDerivRep (β + σ) v w) :
    IsFracDerivRep β v (fun x => cmxHLS_c1 d σ * cmxHLS_RP σ w x) := by
  obtain ⟨C, hC, hRP⟩ := cmxHLS_RP_Lq hd hσ hp hpq hrel
  have hq1 : 1 < q := hp.trans hpq
  have hq0 : 0 < q := by linarith
  have hc1 := cmxHLS_c1_pos d hσ hσd
  set W : Euc d → ℝ := fun x => cmxHLS_c1 d σ * cmxHLS_RP σ w x with hWdef
  have hWm : Measurable W := (cmxHLS_RP_measurable σ hwm).const_mul _
  have hW : ∫⁻ x, ‖W x‖ₑ ^ q ≠ ⊤ := by
    have h1 : ∀ x, ‖W x‖ₑ ^ q = ENNReal.ofReal (cmxHLS_c1 d σ) ^ q * ‖cmxHLS_RP σ w x‖ₑ ^ q := by
      intro x
      rw [hWdef]; simp only
      rw [enorm_mul, Real.enorm_of_nonneg hc1.le, ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
    simp_rw [h1]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top)]
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top) ?_
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by have : 0 < q / p := by positivity
                                         exact this.le) hwp)) (hRP w hwm)
  intro φ
  have hFc : (⇑(𝓕 φ : SchwartzMap (Euc d) ℂ) : Euc d → ℂ) = 𝓕 ⇑φ := SchwartzMap.fourier_coe φ
  obtain ⟨hI, hS⟩ := cmxHLS_lhs_sum hd hβ hvc hv (𝓕 φ : SchwartzMap (Euc d) ℂ)
  have hR := cmxHLS_rhs_sum hd hq1 hWm hW (𝓕 φ : SchwartzMap (Euc d) ℂ)
  simp only [cmxHLS_inv_zero φ] at hR
  simp only [hFc] at hI
  refine ⟨hI, cmxHLS_integrable_mul_Lq hq1 hWm hW φ, ?_⟩
  have hseq : (fun j : ℤ => ∫ x : Euc d, ((v x : ℝ) : ℂ) *
        cmxHLS_piece β (⇑(𝓕 φ : SchwartzMap (Euc d) ℂ)) j x) =
      (fun j : ℤ => ∫ x : Euc d, ((W x : ℝ) : ℂ) *
        cmxHLS_piece 0 (⇑(𝓕 φ : SchwartzMap (Euc d) ℂ)) j x) := by
    funext j
    rw [(cmxHLS_piece_hyp rfl hrep (𝓕 φ : SchwartzMap (Euc d) ℂ) j).2]
    exact cmxHLS_pairing hd hσ hσd hp hpq hrel hwm hwp (𝓕 φ : SchwartzMap (Euc d) ℂ) j
  rw [hseq] at hS
  exact hS.unique hR

end HRS.Commutator.Whole
