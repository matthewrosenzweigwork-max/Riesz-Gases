import HRS.MS.PrepStatAux2

/-!
# HRS.MS.PrepStat -- the stationary-reference preparations (S3.2, packet S32)

`euclidean_preparations_stationary_proof : type_of% @HRS.Whole.euclidean_preparations_stationary`.

Proof (SCOPE_A S3.2).  With `Q = Q_{N,b}`, `f_t = law (X t)`, `π = μ^{⊗N}`, `T = N δ_N ≥ 1`:
* the initial law `f₀ ∈ {π, Q_{N,b₀}}` is `Q.withDensity r` with an explicit `r > 0`
  (`s32_tilt`, `s32_gibbs_zero`); `H(f₀ | Q) ≤ C N δ_N` is `euclidean_preparations_bounds_proof`;
* `s32_entropy_nonincreasing` (`PrepStatAux2`): the realization is reweighted by `r(X₀)⁻¹`
  (`PrepStatAux1`: it stays Brownian, independent of `X₀`, a strong solution since `P' ≪ P`), the
  hypothesis `hInv` is applied only to the reweighted realization, and the data-processing inequality
  `klDiv_map_le` gives `H(f_t | Q) ≤ H(P | P') = H(f₀ | Q)`;
* `H(f_t | π) = H(f_t | Q) + ∫ log φ df_t` (`s32_kl_refchange`, `s32_ref_tilt`, with
  `log φ = -log K - bN F`), bounded by `euclidean_pressure_proof` and
  `euclidean_pair_entropy_self_proof` (`E_f[N|F|] ≤ C(H + T)`);
* linear clause: `s32_linear_bound` (entropy inequality `wr9_dv_abs` against `π` and Hoeffding's lemma)
  with `λ = √δ_N / A`, `s32_linear_arith` (`T ≥ 1` gives `1/(N√δ) ≤ √δ`);
* commutator clause: `Comm_N(v) = 2 𝖥^{h_v}` (`s32_commN_eq`), `h_v = Λ h_{Λ⁻¹ v}` with `Λ⁻¹ v`
  `1`-Lipschitz (`s32_commKernel_scale`, `s32_lipschitz_scale`), `h_{Λ⁻¹v} ∈ IsBoundedPairKernel s (s+1)`
  for every `0 ≤ s` (`s32_comm_isBounded`; `commutatorKernel_isBounded_proof` alone needs `0 < s`) and
  `euclidean_pair_entropy_proof` with the constant `B = s + 1` fixed before `Λ`; `Λ = 0` is trivial.

Statement adjustments: none (the frozen statement is proved as stated; its `hInv` hypothesis is used only
for the reweighted realization, and the statement is vacuous, not false, if `hInv` is unsatisfiable).
Technical: the main theorem needs `set_option maxHeartbeats 3200000`.  Helper lemmas carry the prefix
`s32_`.  Tie in `HRS/MS/PrepStatTie.lean`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MS.PrepStat

open HRS.Whole HRS.MS.Wr

variable {d N : ℕ}

section Gibbs

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G : Euc d → Euc d → ℝ}

theorem s32_gibbs_zero : pairGibbs G N 0 μ = Measure.pi fun _ : Fin N => μ := by
  unfold pairGibbs pairNormalizer
  simp

theorem s32_gwd_zero {b : ℝ} (hW : GibbsWellDefined G N b μ) : GibbsWellDefined G N 0 μ := by
  refine ⟨hW.conv_integrable, hW.pair_integrable, ?_, ?_⟩
  · simp
  · unfold pairNormalizer; simp

theorem s32_normalizer_zero : pairNormalizer G N 0 μ = 1 := by
  unfold pairNormalizer; simp

/-- Two Gibbs laws are related by an explicit positive density. -/
theorem s32_tilt {a b : ℝ} (hGm : Measurable (Function.uncurry G)) (hWa : GibbsWellDefined G N a μ)
    (hWb : GibbsWellDefined G N b μ) :
    (pairGibbs G N b μ).withDensity (fun X => ENNReal.ofReal
        (pairNormalizer G N b μ / pairNormalizer G N a μ *
          Real.exp ((-a * N - -b * N) * pairEnergy G X μ))) = pairGibbs G N a μ :=
  prep_withDensity_ratio (Measure.pi fun _ : Fin N => μ) (F := fun X => pairEnergy G X μ)
    (wr9_measurable_pairEnergy hGm) hWa.normalizer_pos hWb.normalizer_pos

theorem s32_ratio_meas {a b : ℝ} (hGm : Measurable (Function.uncurry G)) :
    Measurable (fun X : EucConfig d N =>
      pairNormalizer G N b μ / pairNormalizer G N a μ *
          Real.exp ((-a * N - -b * N) * pairEnergy G X μ)) :=
  measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul
    (wr9_measurable_pairEnergy hGm)))

theorem s32_ratio_pos {a b : ℝ} (hWa : GibbsWellDefined G N a μ)
    (hWb : GibbsWellDefined G N b μ) (X : EucConfig d N) :
    0 < pairNormalizer G N b μ / pairNormalizer G N a μ *
          Real.exp ((-a * N - -b * N) * pairEnergy G X μ) :=
  mul_pos (div_pos hWb.normalizer_pos hWa.normalizer_pos) (Real.exp_pos _)

/-- `Q_b = (K_b⁻¹ e^{-bN F}) μ^{⊗N}` with the explicit logarithm of the density. -/
theorem s32_ref_tilt {b : ℝ} (hGm : Measurable (Function.uncurry G))
    (hW : GibbsWellDefined G N b μ) :
    ∃ φ : EucConfig d N → ℝ, Measurable φ ∧ (∀ X, 0 < φ X) ∧
      pairGibbs G N b μ =
        (Measure.pi fun _ : Fin N => μ).withDensity (fun X => ENNReal.ofReal (φ X)) ∧
      ∀ X, Real.log (φ X) = -Real.log (pairNormalizer G N b μ) - b * (N * pairEnergy G X μ) := by
  have h0 := s32_gwd_zero hW
  have ht := s32_tilt hGm h0 hW
  rw [s32_gibbs_zero] at ht
  set r : EucConfig d N → ℝ := fun X => pairNormalizer G N b μ / pairNormalizer G N 0 μ *
      Real.exp ((-0 * N - -b * N) * pairEnergy G X μ) with hr
  have hrm : Measurable r := s32_ratio_meas hGm
  have hrp : ∀ X, 0 < r X := s32_ratio_pos h0 hW
  have hinv := s32_inv_density (f0 := Measure.pi fun _ : Fin N => μ) (Q := pairGibbs G N b μ)
    hrm hrp ht.symm
  refine ⟨fun X => (r X)⁻¹, hrm.inv, fun X => inv_pos.2 (hrp X), hinv, fun X => ?_⟩
  simp only [hr, s32_normalizer_zero]
  rw [Real.log_inv, Real.log_mul (div_pos hW.normalizer_pos one_pos).ne' (Real.exp_pos _).ne',
    Real.log_exp, div_one]
  ring

end Gibbs

/-- The choice `λ = √δ / A` in the linear clause. -/
theorem s32_linear_arith {δ A H C1 : ℝ} (hN : 0 < N) (hT : 1 ≤ (N : ℝ) * δ) (hA : 0 < A)
    (hH : H ≤ C1 * ((N : ℝ) * δ)) (hC1 : 0 ≤ C1) :
    ((N : ℝ) * (Real.sqrt δ / A))⁻¹ * (H + ((N : ℝ) * A ^ 2 * (Real.sqrt δ / A) ^ 2 / 2 + 1)) ≤
      (C1 + 3 / 2) * A * Real.sqrt δ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : 0 < δ := by
    by_contra h
    push Not at h
    nlinarith
  set u := Real.sqrt δ with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 hδ
  have hu2 : u ^ 2 = δ := Real.sq_sqrt hδ.le
  have hX : H + ((N : ℝ) * A ^ 2 * (u / A) ^ 2 / 2 + 1) ≤ (C1 + 3 / 2) * ((N : ℝ) * u ^ 2) := by
    have e : (N : ℝ) * A ^ 2 * (u / A) ^ 2 / 2 = (N : ℝ) * u ^ 2 / 2 := by
      field_simp
    rw [e]
    rw [hu2] at *
    nlinarith
  have hpos : 0 < (N : ℝ) * (u / A) := by positivity
  calc ((N : ℝ) * (u / A))⁻¹ * (H + ((N : ℝ) * A ^ 2 * (u / A) ^ 2 / 2 + 1))
      ≤ ((N : ℝ) * (u / A))⁻¹ * ((C1 + 3 / 2) * ((N : ℝ) * u ^ 2)) :=
        mul_le_mul_of_nonneg_left hX (inv_nonneg.2 hpos.le)
    _ = (C1 + 3 / 2) * A * u := by field_simp

/-! ### The theorem -/

set_option maxHeartbeats 3200000 in
theorem euclidean_preparations_stationary_proof :
    HRS.Whole.EuclideanPreparationsStationaryStatement := by
  intro d s hd hs0 hsd M L b b0 hb hb0
  set bm : ℝ := min b b0 with hbm
  set bp : ℝ := max b b0 + 1 with hbp
  have hbm0 : 0 < bm := lt_min hb hb0
  have hbmp : bm < bp := by
    have := min_le_max (a := b) (b := b0); simp only [hbm, hbp]; linarith
  have hbI : b ∈ Set.Icc bm bp := ⟨min_le_left _ _, by simp only [hbp]; linarith [le_max_left b b0]⟩
  have hb0I : b0 ∈ Set.Icc bm bp :=
    ⟨min_le_right _ _, by simp only [hbp]; linarith [le_max_right b b0]⟩
  obtain ⟨Cb, hCb⟩ := euclidean_preparations_bounds_proof hd hs0 hsd M L b b0 hb hb0
  obtain ⟨θ0, hθ0, C0, hP⟩ := euclidean_pressure_proof hd hs0 hsd M L bm bp 0 hbm0 hbmp
  obtain ⟨cE, hcE, CE, hS⟩ := euclidean_pair_entropy_self_proof hd hs0 hsd M L bm bp hbm0 hbmp
  obtain ⟨cH, hcH, CH, hHh⟩ :=
    euclidean_pair_entropy_proof hd hs0 hsd M L bm bp (s + 1) hbm0 hbmp
  have hhz : IsBoundedPairKernel s 0 (fun _ _ : Euc d => (0 : ℝ)) :=
    ⟨measurable_const, fun _ _ => rfl, fun x y _ => by simp⟩
  set Cb' : ℝ := max Cb 0 with hCb'
  set C0' : ℝ := max C0 0 with hC0'
  set CE' : ℝ := max CE 0 with hCE'
  set CH' : ℝ := max CH 0 with hCH'
  have hCb'0 : 0 ≤ Cb' := le_max_right _ _
  have hC0'0 : 0 ≤ C0' := le_max_right _ _
  have hCE'0 : 0 ≤ CE' := le_max_right _ _
  have hCH'0 : 0 ≤ CH' := le_max_right _ _
  set C1 : ℝ := 2 * Cb' + C0' + b * CE' * (Cb' + 1) with hC1
  have hC10 : 0 ≤ C1 := by positivity
  set Cfin : ℝ := C1 + 3 / 2 + 2 * CH' * (Cb' + 1) + 1 with hCfin
  refine ⟨Cfin, ?_⟩
  intro ρ hρ hρM hlog V hth N hN hInv Ω _ P _ T X₀ W X hW hind hlaw hsol t ht
  have hμprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) :=
    Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set T' : ℝ := (N : ℝ) * deltaN d s N with hT'
  have hT1 : 1 ≤ T' := wr8_one_le_mul_deltaN hs0 N (by omega)
  have hN1 : 0 < N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hδ : 0 < deltaN d s N := by
    by_contra h
    push Not at h
    have : (N : ℝ) * deltaN d s N ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN0.le h
    linarith
  set G : Euc d → Euc d → ℝ := fun x y => rieszKernel d s (x - y) with hG
  have hGm : Measurable (Function.uncurry G) := wr9_rieszKernel_pair_meas s
  have hFm : Measurable (fun X : EucConfig d N => pairEnergy G X μ) := wr9_measurable_pairEnergy hGm
  have key : ∀ b' ∈ Set.Icc bm bp, GibbsWellDefined G N b' μ ∧
      |Real.log (pairNormalizer G N b' μ)| ≤ C0 * T' := by
    intro b' hb''
    obtain ⟨hW', hbd⟩ := hP ρ hρ hρM hlog (fun _ _ => 0) hhz N hN b' hb'' 0
      (by rw [abs_zero]; exact hθ0.le)
    simp only [zero_mul, sub_zero] at hW' hbd
    exact ⟨hW', by simpa only [hT', mul_assoc] using hbd⟩
  obtain ⟨hWb, hlogKb⟩ := key b hbI
  obtain ⟨hWb0, -⟩ := key b0 hb0I
  have hC0 : 0 ≤ C0 := wr9_nonneg_of_abs_le hlogKb hT1
  have hQprob : IsProbabilityMeasure (pairGibbs G N b μ) := wr9_gibbs_prob hWb
  set Q : Measure (EucConfig d N) := HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ with hQ
  have hQeq : Q = pairGibbs G N b μ := rfl
  have : IsProbabilityMeasure Q := hQprob
  set π : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ with hπ
  -- initial entropy
  have hH0 : InformationTheory.klDiv (law P X₀) Q ≤ ENNReal.ofReal (Cb' * T') := by
    obtain hsum := hCb ρ hρ hρM hlog N hN
    have hle : Cb * N * deltaN d s N ≤ Cb' * T' := by
      have : Cb * N * deltaN d s N = Cb * T' := by rw [hT']; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    have hsum' := hsum.trans (ENNReal.ofReal_le_ofReal hle)
    rcases hlaw with h | h
    · rw [h]
      exact le_trans (le_self_add) hsum'
    · rw [h]
      exact le_trans (le_add_self) hsum'
  -- the density of the initial law with respect to `Q`
  have hπ0 : π = pairGibbs G N 0 μ := (s32_gibbs_zero (G := G) (N := N) (μ := μ)).symm
  have hfr : ∃ r : EucConfig d N → ℝ, Measurable r ∧ (∀ x, 0 < r x) ∧
      law P X₀ = Q.withDensity (fun x => ENNReal.ofReal (r x)) := by
    rcases hlaw with h | h
    · refine ⟨_, s32_ratio_meas (a := 0) (b := b) hGm, s32_ratio_pos (s32_gwd_zero hWb) hWb, ?_⟩
      rw [h, hπ0]
      exact (s32_tilt hGm (s32_gwd_zero hWb) hWb).symm
    · refine ⟨_, s32_ratio_meas (a := b0) (b := b) hGm, s32_ratio_pos hWb0 hWb, ?_⟩
      rw [h]
      exact (s32_tilt hGm hWb0 hWb).symm
  obtain ⟨r, hr, hrpos, hlawr⟩ := hfr
  have hKL0 : InformationTheory.klDiv (law P X₀) Q ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH0
  have hmono := s32_entropy_nonincreasing (⟨s, -1, V, b⁻¹⟩ : WholeDyn d) Q hInv P T X₀ W X hW hind
    hr hrpos hlawr hKL0 hsol t ht
  have hXm : Measurable (X t) := hsol.adapted t
  set f : Measure (EucConfig d N) := P.map (X t) with hf
  have hHf : InformationTheory.klDiv f Q ≤ ENNReal.ofReal (Cb' * T') := hmono.trans hH0
  have hHfin : InformationTheory.klDiv f Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hHf
  have hHreal : (InformationTheory.klDiv f Q).toReal ≤ Cb' * T' :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hHf
  have hHnn : 0 ≤ (InformationTheory.klDiv f Q).toReal := ENNReal.toReal_nonneg
  -- the energy bound under `f`
  obtain ⟨hFint, hFbd⟩ := (hS ρ hρ hρM hlog N hN b hbI).2 f inferInstance
    (lt_top_iff_ne_top.2 hHfin)
  have hFint' : Integrable (fun X : EucConfig d N => (N : ℝ) * |pairEnergy G X μ|) f := hFint
  have hFbd' : ∫ X : EucConfig d N, (N : ℝ) * |pairEnergy G X μ| ∂f ≤
      CE' * ((InformationTheory.klDiv f Q).toReal + T') := by
    refine le_trans hFbd ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hHnn (by linarith))
  -- the entropy with respect to `μ^{⊗N}`
  obtain ⟨φ, hφm, hφpos, hQπ, hlogφ⟩ := s32_ref_tilt hGm hWb
  have hNF : Integrable (fun X : EucConfig d N => (N : ℝ) * pairEnergy G X μ) f := by
    have h1 : Integrable (fun X : EucConfig d N => ‖(N : ℝ) * pairEnergy G X μ‖) f :=
      hFint'.congr (Filter.Eventually.of_forall fun X => by
        simp only [norm_mul, Real.norm_eq_abs, abs_of_pos hN0])
    exact (integrable_norm_iff (hFm.const_mul _).aestronglyMeasurable).1 h1
  have hint_log : Integrable (fun X : EucConfig d N => Real.log (φ X)) f :=
    ((integrable_const (-Real.log (pairNormalizer G N b μ))).sub (hNF.const_mul b)).congr
      (Filter.Eventually.of_forall fun X => (hlogφ X).symm)
  obtain ⟨hπne, hπeq⟩ := s32_kl_refchange f Q π hφm hφpos hQπ hHfin hint_log
  have hlogint : ∫ X, Real.log (φ X) ∂f ≤ C0' * T' + b * (CE' * ((InformationTheory.klDiv f Q).toReal + T')) := by
    have h1 : ∫ X, Real.log (φ X) ∂f ≤
        ∫ X, (|Real.log (pairNormalizer G N b μ)| + b * ((N : ℝ) * |pairEnergy G X μ|)) ∂f := by
      refine integral_mono hint_log ((integrable_const _).add (hFint'.const_mul b)) fun X => ?_
      rw [hlogφ X]
      have hF1 : -(pairEnergy G X μ) ≤ |pairEnergy G X μ| := neg_le_abs _
      have hF2 : -((N : ℝ) * pairEnergy G X μ) ≤ (N : ℝ) * |pairEnergy G X μ| := by nlinarith
      have h3 := mul_le_mul_of_nonneg_left hF2 hb.le
      linarith [neg_le_abs (Real.log (pairNormalizer G N b μ))]
    refine h1.trans ?_
    rw [integral_add (integrable_const _) (hFint'.const_mul b), integral_const, integral_const_mul]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    have h4 : |Real.log (pairNormalizer G N b μ)| ≤ C0' * T' :=
      hlogKb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
    have h5 := mul_le_mul_of_nonneg_left hFbd' hb.le
    linarith
  have hπreal : (InformationTheory.klDiv f π).toReal ≤ (Cb' + C0' + b * CE' * (Cb' + 1)) * T' := by
    rw [hπeq]
    have h1 : b * (CE' * ((InformationTheory.klDiv f Q).toReal + T')) ≤
        b * (CE' * ((Cb' + 1) * T')) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hCE'0) hb.le
      nlinarith
    have h2 : 0 ≤ b * CE' * ((Cb' + 1) * T') := by positivity
    have h3 : 0 ≤ Cb' * T' := by positivity
    have h4 : 0 ≤ C0' * T' := by positivity
    have h5 : (Cb' + C0' + b * CE' * (Cb' + 1)) * T' =
        Cb' * T' + C0' * T' + b * CE' * ((Cb' + 1) * T') := by ring
    linarith [h1, h5, hlogint, hHreal]
  have hπreal' : (InformationTheory.klDiv f π).toReal ≤ C1 * T' := by
    refine hπreal.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
    rw [hC1]; linarith
  refine ⟨?_, ?_, ?_⟩
  · -- (1) the entropy bounds
    show InformationTheory.klDiv f Q + InformationTheory.klDiv f π ≤
      ENNReal.ofReal (Cfin * N * deltaN d s N)
    calc InformationTheory.klDiv f Q + InformationTheory.klDiv f π
        = ENNReal.ofReal (InformationTheory.klDiv f Q).toReal +
            ENNReal.ofReal (InformationTheory.klDiv f π).toReal := by
          rw [ENNReal.ofReal_toReal hHfin, ENNReal.ofReal_toReal hπne]
      _ = ENNReal.ofReal ((InformationTheory.klDiv f Q).toReal +
            (InformationTheory.klDiv f π).toReal) :=
          (ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg).symm
      _ ≤ ENNReal.ofReal (Cfin * N * deltaN d s N) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have e : Cfin * N * deltaN d s N = Cfin * T' := by rw [hT']; ring
          rw [e]
          have h1 : (InformationTheory.klDiv f Q).toReal + (InformationTheory.klDiv f π).toReal ≤
              Cb' * T' + (Cb' + C0' + b * CE' * (Cb' + 1)) * T' := add_le_add hHreal hπreal
          have h2 : Cb' * T' + (Cb' + C0' + b * CE' * (Cb' + 1)) * T' ≤ Cfin * T' := by
            have e2 : Cb' * T' + (Cb' + C0' + b * CE' * (Cb' + 1)) * T' = C1 * T' := by
              rw [hC1]; ring
            rw [e2]
            refine mul_le_mul_of_nonneg_right ?_ (by linarith)
            have : 0 ≤ 2 * CH' * (Cb' + 1) := by positivity
            rw [hCfin]; linarith
          linarith
  · -- (2) the linear clause
    intro a A ha hA
    have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
    have hgm : Measurable (fun X : EucConfig d N => |HRS.Whole.pair (HRS.Whole.empirical X) a -
        HRS.Whole.pair μ a|) := by
      have e : (fun X : EucConfig d N => |HRS.Whole.pair (HRS.Whole.empirical X) a -
          HRS.Whole.pair μ a|) =
          fun X => |(N : ℝ)⁻¹ * ∑ i, a (X i) - HRS.Whole.pair μ a| := by
        funext X; rw [s32_pair_empirical X ha]
      rw [e]
      exact continuous_abs.measurable.comp (((Finset.measurable_sum _ fun i _ =>
        ha.comp (measurable_pi_apply i)).const_mul _).sub_const _)
    by_cases hAz : A = 0
    · have ha0 : ∀ x, a x = 0 := fun x => abs_nonpos_iff.1 (by simpa [hAz] using hA x)
      have hz : ∀ ζ, |HRS.Whole.pair (HRS.Whole.empirical (X t ζ)) a - HRS.Whole.pair μ a| = 0 := by
        intro ζ
        rw [s32_pair_empirical _ ha]
        simp [ha0, HRS.Whole.pair]
      simp [hz, hAz]
    · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAz)
      have hlam : 0 < Real.sqrt (deltaN d s N) / A := div_pos (Real.sqrt_pos.2 hδ) hApos
      obtain ⟨hli, hlb⟩ := s32_linear_bound (μ := μ) ha hA hN1 f hπne hlam
      have hlb' := hlb.trans (s32_linear_arith (N := N) (δ := deltaN d s N) hN1 hT1 hApos
        (by simpa only [hT'] using hπreal') hC10)
      refine ⟨(integrable_map_measure hgm.aestronglyMeasurable hXm.aemeasurable).1 hli, ?_⟩
      have hint := integral_map hXm.aemeasurable hgm.aestronglyMeasurable (μ := P)
      have e2 : ∫ ζ, |HRS.Whole.pair (HRS.Whole.empirical (X t ζ)) a - HRS.Whole.pair μ a| ∂P =
          ∫ X, |HRS.Whole.pair (HRS.Whole.empirical X) a - HRS.Whole.pair μ a| ∂f := hint.symm
      rw [e2]
      refine hlb'.trans ?_
      have hsq : 0 ≤ Real.sqrt (deltaN d s N) := Real.sqrt_nonneg _
      have : C1 + 3 / 2 ≤ Cfin := by
        have : 0 ≤ 2 * CH' * (Cb' + 1) := by positivity
        rw [hCfin]; linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hA0) hsq
  · -- (3) the commutator clause
    intro v Λ hv
    have hcm := HRS.MS.Comm.comm_meas (d := d) (s := s) v hv.continuous.measurable
    have hgm : Measurable (fun X : EucConfig d N => |commN d s v X μ|) := by
      have e : (fun X : EucConfig d N => |commN d s v X μ|) =
          fun X => |2 * pairEnergy (commutatorKernel d s v) X μ| := by
        funext X; rw [s32_commN_eq]
      rw [e]
      exact continuous_abs.measurable.comp ((wr9_measurable_pairEnergy hcm).const_mul 2)
    by_cases hΛ : Λ = 0
    · subst hΛ
      have h0 : ∀ ζ, |commN d s v (X t ζ) μ| = 0 := fun ζ => by
        rw [s32_commN_zero s hv]; simp
      simp [h0]
    · have hv1 := s32_lipschitz_scale hΛ hv
      have hB := s32_comm_isBounded (d := d) hs0 hv1
      obtain ⟨-, hbd⟩ := hHh ρ hρ hρM hlog _ hB N hN b hbI
      obtain ⟨hi1, hb1⟩ := hbd f inferInstance (lt_top_iff_ne_top.2 hHfin)
      have hΛ0 : (0 : ℝ) ≤ Λ := Λ.coe_nonneg
      have hpt : ∀ X : EucConfig d N, |commN d s v X μ| = (2 * (Λ : ℝ) / N) *
          ((N : ℝ) * |pairEnergy (commutatorKernel d s ((Λ : ℝ)⁻¹ • v)) X μ|) := by
        intro X
        rw [s32_commN_eq]
        have e : commutatorKernel d s v = fun x y =>
            (Λ : ℝ) * commutatorKernel d s ((Λ : ℝ)⁻¹ • v) x y :=
          funext fun x => funext fun y => s32_commKernel_scale s hΛ v x y
        rw [e, s32_pairEnergy_const_mul, abs_mul, abs_mul, abs_of_nonneg hΛ0]
        rw [abs_two]
        field_simp
      have hi : Integrable (fun X : EucConfig d N => |commN d s v X μ|) f :=
        (hi1.const_mul (2 * (Λ : ℝ) / N)).congr (Filter.Eventually.of_forall fun X => (hpt X).symm)
      refine ⟨(integrable_map_measure hgm.aestronglyMeasurable hXm.aemeasurable).1 hi, ?_⟩
      have hint := integral_map hXm.aemeasurable hgm.aestronglyMeasurable (μ := P)
      have e2 : ∫ ζ, |commN d s v (X t ζ) μ| ∂P = ∫ X, |commN d s v X μ| ∂f := hint.symm
      rw [e2]
      have e3 : ∫ X, |commN d s v X μ| ∂f = (2 * (Λ : ℝ) / N) *
          ∫ X, (N : ℝ) * |pairEnergy (commutatorKernel d s ((Λ : ℝ)⁻¹ • v)) X μ| ∂f := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
      rw [e3]
      have hb2 : ∫ X, (N : ℝ) * |pairEnergy (commutatorKernel d s ((Λ : ℝ)⁻¹ • v)) X μ| ∂f ≤
          CH' * ((Cb' + 1) * T') := by
        refine hb1.trans ?_
        have h1 : CH * ((InformationTheory.klDiv f Q).toReal + (N : ℝ) * deltaN d s N) ≤
            CH' * ((InformationTheory.klDiv f Q).toReal + T') :=
          mul_le_mul (le_max_left _ _) le_rfl (add_nonneg hHnn (by linarith)) hCH'0
        refine h1.trans (mul_le_mul_of_nonneg_left ?_ hCH'0)
        nlinarith
      have hcoef : 0 ≤ 2 * (Λ : ℝ) / N := by positivity
      refine (mul_le_mul_of_nonneg_left hb2 hcoef).trans ?_
      have e4 : 2 * (Λ : ℝ) / N * (CH' * ((Cb' + 1) * T')) =
          (2 * CH' * (Cb' + 1)) * (Λ : ℝ) * deltaN d s N := by
        rw [hT']; field_simp
      rw [e4]
      have : 2 * CH' * (Cb' + 1) ≤ Cfin := by
        rw [hCfin]; linarith
      have hΛδ : 0 ≤ (Λ : ℝ) * deltaN d s N := by positivity
      nlinarith

end HRS.MS.PrepStat
