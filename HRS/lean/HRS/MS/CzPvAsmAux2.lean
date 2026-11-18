import HRS.MS.CzPvAsmAux1

/-!
# PV-ASM, part 2: the `L^p` extension, a.e. principal values and the second conjunct of `lp_screened_negative_order`

Packet PVASM (CZ development), namespace `HRS.CZ.PvAsm`; LINEAR kernel `K_i(z) = z_i/|z|^{d+1}` only.

* `pvasm_T_extend`: the operator `W ↦ pvOdd d 1 (u_i) W` (Schwartz) extends to a continuous linear map
  `T : L^p(ℝ) → L^p(ℝ)` of norm `≤ CT` (the Mikhlin bound of part 1).
* `pvasm_trunc_Lp_decomp`: for every `g ∈ L^p` and every `ε > 0`, at EVERY `x`,
  `T_ε g(x) = (φ_ε * T g)(x) + (Ψ_ε * g)(x)` (the truncation of an `L^p` function is an absolutely convergent
  integral by Hölder, `Ktr_ε ∈ L^{p'}`).
* `pvasm_ae_pv_Lp`: for `g ∈ L^p`, a.e. `x`, `T_ε g(x) → (T g)(x)` as `ε → 0+` (approximate identity at
  Lebesgue points of `T g` plus `ae_tendsto_Psi`), and `‖T_ε g‖_p ≤ C ‖g‖_p` for all `ε > 0` (the extension of
  `ElemTruncBound` to `L^p`).
* `lp_screened_negative_order_theta_one_lin`: for `a ∈ L^∞`, `W ∈ L^p`:
  `‖pvOdd d 1 (u_i) (a W)‖_p ≤ C ‖a‖_∞ ‖W‖_p` (the second conjunct of `lp_screened_negative_order`, for the
  linear `Ω(u) = u_i`; all `1 < p < ∞`, the frozen statement has `2 ≤ p`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap

noncomputable section

namespace HRS.CZ.PvAsm

open HRS.CZ.Pv HRS.CZ.Pvk HRS.CZ.Mik HRS.CZ.Sym

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### linearity of `pvOdd` on Schwartz functions -/

lemma pvasm_Ktr_bdd (hd : 1 ≤ d) (i : Fin d) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, ∀ y, |pvkKtr (pvasmK d i) ε y| ≤ c := by
  obtain ⟨L, hK⟩ := pvasm_kernel hd i
  exact ⟨_, pvk_Ktr_bound hd hK hε⟩

lemma pvasm_Ktr_meas (hd : 1 ≤ d) (i : Fin d) (ε : ℝ) : Measurable (pvkKtr (pvasmK d i) ε) := by
  obtain ⟨L, hK⟩ := pvasm_kernel hd i
  exact pvk_Ktr_meas hK ε

lemma pvasm_trunc_add (hd : 1 ≤ d) (i : Fin d) (W₁ W₂ : 𝓢(𝔼, ℝ)) {ε : ℝ} (hε : 0 < ε) (x : 𝔼) :
    pvTrunc d 1 (fun v : 𝔼 => v i) (⇑(W₁ + W₂)) ε x =
      pvTrunc d 1 (fun v : 𝔼 => v i) W₁ ε x + pvTrunc d 1 (fun v : 𝔼 => v i) W₂ ε x := by
  obtain ⟨c, hc⟩ := pvasm_Ktr_bdd hd i hε
  have hm := pvasm_Ktr_meas hd i ε
  have hi : ∀ W : 𝓢(𝔼, ℝ), Integrable fun z => pvkKtr (pvasmK d i) ε z * W (x - z) := fun W =>
    Integrable.bdd_mul (c := c) (W.integrable.comp_sub_left x) hm.aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hc z)
  simp only [pvasm_trunc_eq]
  rw [← integral_add (hi W₁) (hi W₂)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [add_apply]
  ring

lemma pvasm_trunc_smul (i : Fin d) (a : ℝ) (W : 𝓢(𝔼, ℝ)) (ε : ℝ) (x : 𝔼) :
    pvTrunc d 1 (fun v : 𝔼 => v i) (⇑(a • W)) ε x = a * pvTrunc d 1 (fun v : 𝔼 => v i) W ε x := by
  simp only [pvasm_trunc_eq]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [smul_apply, smul_eq_mul]
  ring

lemma pvasm_pvOdd_add (hd : 1 ≤ d) (i : Fin d) (W₁ W₂ : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) (⇑(W₁ + W₂)) x =
      HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W₁ x +
        HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W₂ x := by
  have h12 := pvasm_trunc_tendsto hd i (W₁ + W₂) x
  have h1 := (pvasm_trunc_tendsto hd i W₁ x).add (pvasm_trunc_tendsto hd i W₂ x)
  refine tendsto_nhds_unique h12 (h1.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (pvasm_trunc_add hd i W₁ W₂ hε x).symm

lemma pvasm_pvOdd_smul (hd : 1 ≤ d) (i : Fin d) (a : ℝ) (W : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) (⇑(a • W)) x =
      a * HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W x := by
  have h12 := pvasm_trunc_tendsto hd i (a • W) x
  have h1 := (pvasm_trunc_tendsto hd i W x).const_mul a
  refine tendsto_nhds_unique h12 (h1.congr' ?_)
  filter_upwards with ε
  exact (pvasm_trunc_smul i a W ε x).symm

/-! ### the extension to `L^p` -/

lemma pvasm_fact {p : ℝ} (hp : 1 < p) : Fact (1 ≤ ENNReal.ofReal p) :=
  ⟨by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le⟩

theorem pvasm_T_extend (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ i : Fin d,
      ∃ T : Lp ℝ (ENNReal.ofReal p) (volume : Measure 𝔼) →L[ℝ] Lp ℝ (ENNReal.ofReal p) (volume : Measure 𝔼),
        ‖T‖ ≤ CT ∧ ∀ W : 𝓢(𝔼, ℝ), T (W.toLp (ENNReal.ofReal p) volume) =ᵐ[volume]
          HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W := by
  obtain ⟨CT, hCT, hT⟩ := pvasm_T_eLpNorm hd hp
  refine ⟨CT, hCT, fun i => ?_⟩
  have hKc := isPvKernel_coord (d := d) i
  have hmem : ∀ W : 𝓢(𝔼, ℝ), MemLp (HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W)
      (ENNReal.ofReal p) volume := fun W => by
    exact lt_of_le_of_lt (hT i W)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (W.memLp _ _).eLpNorm_lt_top)
  let f : 𝓢(𝔼, ℝ) →ₗ[ℝ] Lp ℝ (ENNReal.ofReal p) (volume : Measure 𝔼) :=
    { toFun := fun W => (hmem W).toLp (HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W)
      map_add' := fun W₁ W₂ => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => pvasm_pvOdd_add hd i W₁ W₂ x)
      map_smul' := fun a W => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul a (hmem W)]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => by
          simpa using pvasm_pvOdd_smul hd i a W x) }
  let e : 𝓢(𝔼, ℝ) →ₗ[ℝ] Lp ℝ (ENNReal.ofReal p) (volume : Measure 𝔼) :=
    (SchwartzMap.toLpCLM ℝ ℝ (ENNReal.ofReal p) volume).toLinearMap
  have hdense : DenseRange e :=
    SchwartzMap.denseRange_toLpCLM (E := 𝔼) (F := ℝ) (p := ENNReal.ofReal p) ENNReal.ofReal_ne_top
  have hnorm : ∀ W : 𝓢(𝔼, ℝ), ‖f W‖ ≤ CT * ‖e W‖ := by
    intro W
    have h1 : ‖f W‖ = (eLpNorm (HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W)
        (ENNReal.ofReal p) volume).toReal := Lp.norm_toLp _ (hmem W)
    have h2 : ‖e W‖ = (eLpNorm (⇑W) (ENNReal.ofReal p) volume).toReal := SchwartzMap.norm_toLp
    rw [h1, h2]
    have hfin : ENNReal.ofReal CT * eLpNorm (⇑W) (ENNReal.ofReal p) volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (W.memLp _ _).eLpNorm_ne_top
    have h3 := ENNReal.toReal_mono hfin (hT i W)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCT] at h3
  refine ⟨f.extendOfNorm e, LinearMap.opNorm_extendOfNorm_le hdense hCT hnorm, fun W => ?_⟩
  have h := LinearMap.extendOfNorm_eq hdense ⟨_, hnorm⟩ W
  have e1 : W.toLp (ENNReal.ofReal p) volume = e W := rfl
  rw [e1, h]
  exact (hmem W).coeFn_toLp

/-! ### Hölder at a point -/

/-- Hölder: `∫ |κ(z) h(x-z)| dz ≤ ‖κ‖_{p'} ‖h‖_p` (`ENNReal`-valued) -/
lemma pvasm_holder_lint {p : ℝ} (hp : 1 < p) {κ h : 𝔼 → ℝ} (hκ : Measurable κ) (hh : Measurable h)
    (x : 𝔼) :
    ∫⁻ z, ‖κ z * h (x - z)‖ₑ ≤
      (∫⁻ z, ‖κ z‖ₑ ^ p.conjExponent) ^ (1 / p.conjExponent) * eLpNorm h (ENNReal.ofReal p) volume := by
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  have hp0 : 0 < p := by linarith
  have hne : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have h1 : ∫⁻ z, ‖κ z * h (x - z)‖ₑ = ∫⁻ z, (fun z => ‖h (x - z)‖ₑ) z * (fun z => ‖κ z‖ₑ) z := by
    refine lintegral_congr fun z => ?_
    simp only [enorm_mul]; ring
  rw [h1]
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
    (hh.comp (measurable_const.sub measurable_id)).enorm.aemeasurable hκ.enorm.aemeasurable).trans ?_
  have h2 : ∫⁻ z, ‖h (x - z)‖ₑ ^ p = ∫⁻ z, ‖h z‖ₑ ^ p :=
    lintegral_sub_left_eq_self (μ := (volume : Measure 𝔼)) (fun z => ‖h z‖ₑ ^ p) x
  have h3 : eLpNorm h (ENNReal.ofReal p) volume = (∫⁻ z, ‖h z‖ₑ ^ p) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne ENNReal.ofReal_ne_top hh.aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le]
  rw [h3, mul_comm]
  exact mul_le_mul' le_rfl (le_of_eq (by congr 1))

lemma pvasm_holder_int {p : ℝ} (hp : 1 < p) {κ h : 𝔼 → ℝ} (hκ : Measurable κ) (hh : Measurable h)
    (hq : ∫⁻ z, ‖κ z‖ₑ ^ p.conjExponent ≠ ⊤) (hhp : MemLp h (ENNReal.ofReal p) volume) (x : 𝔼) :
    Integrable (fun z => κ z * h (x - z)) ∧
      ‖∫ z, κ z * h (x - z)‖ₑ ≤
        (∫⁻ z, ‖κ z‖ₑ ^ p.conjExponent) ^ (1 / p.conjExponent) * eLpNorm h (ENNReal.ofReal p) volume := by
  have hb := pvasm_holder_lint hp hκ hh x
  have hq0 : (0 : ℝ) ≤ 1 / p.conjExponent := by
    have := Real.HolderConjugate.conjExponent hp |>.symm.pos
    positivity
  have hfin : (∫⁻ z, ‖κ z‖ₑ ^ p.conjExponent) ^ (1 / p.conjExponent) *
      eLpNorm h (ENNReal.ofReal p) volume < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq0 hq) hhp
  refine ⟨⟨((hκ.mul (hh.comp (measurable_const.sub measurable_id)))).aestronglyMeasurable,
    lt_of_le_of_lt hb hfin⟩, ?_⟩
  exact (enorm_integral_le_lintegral_enorm _).trans hb

/-- continuity of the pointwise pairing under `L^p` convergence -/
lemma pvasm_holder_tendsto {p : ℝ} (hp : 1 < p) {κ : 𝔼 → ℝ} (hκ : Measurable κ)
    (hq : ∫⁻ z, ‖κ z‖ₑ ^ p.conjExponent ≠ ⊤) {hn : ℕ → 𝔼 → ℝ} {h : 𝔼 → ℝ}
    (hnm : ∀ n, Measurable (hn n)) (hm : Measurable h)
    (hnp : ∀ n, MemLp (hn n) (ENNReal.ofReal p) volume) (hhp : MemLp h (ENNReal.ofReal p) volume)
    (hlim : Tendsto (fun n => eLpNorm (fun z => hn n z - h z) (ENNReal.ofReal p) volume) atTop (𝓝 0))
    (x : 𝔼) :
    Tendsto (fun n => ∫ z, κ z * hn n (x - z)) atTop (𝓝 (∫ z, κ z * h (x - z))) := by
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_enorm_tendsto_zero]
  set c : ℝ≥0∞ := (∫⁻ z, ‖κ z‖ₑ ^ p.conjExponent) ^ (1 / p.conjExponent) with hc
  have hq0 : (0 : ℝ) ≤ 1 / p.conjExponent := by
    have := Real.HolderConjugate.conjExponent hp |>.symm.pos
    positivity
  have hcfin : c ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg hq0 hq).ne
  have hbound : ∀ n, ‖(∫ z, κ z * hn n (x - z)) - ∫ z, κ z * h (x - z)‖ₑ ≤
      c * eLpNorm (fun z => hn n z - h z) (ENNReal.ofReal p) volume := by
    intro n
    have hI := pvasm_holder_int hp hκ ((hnm n).sub hm) hq ((hnp n).sub hhp) x
    have h1 := (pvasm_holder_int hp hκ (hnm n) hq (hnp n) x).1
    have h2 := (pvasm_holder_int hp hκ hm hq hhp x).1
    have : (∫ z, κ z * hn n (x - z)) - ∫ z, κ z * h (x - z) =
        ∫ z, κ z * (hn n (x - z) - h (x - z)) := by
      rw [← integral_sub h1 h2]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [mul_sub]
    rw [this]
    exact hI.2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => bot_le) hbound
  have := ENNReal.Tendsto.const_mul hlim (Or.inr hcfin)
  simpa using this

/-! ### kernels in `L^q` -/

lemma pvasm_Lq_bdd_int {κ : 𝔼 → ℝ} {q : ℝ} (hq : 1 ≤ q) {c : ℝ} (hb : ∀ z, |κ z| ≤ c)
    (hi : Integrable κ) : ∫⁻ z, ‖κ z‖ₑ ^ q ≠ ⊤ := by
  have hq1 : (0 : ℝ) ≤ q - 1 := by linarith
  have hpt : ∀ z, ‖κ z‖ₑ ^ q ≤ ENNReal.ofReal c ^ (q - 1) * ‖κ z‖ₑ := fun z => by
    have e : ‖κ z‖ₑ ^ q = ‖κ z‖ₑ ^ (q - 1) * ‖κ z‖ₑ ^ (1 : ℝ) := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ hq1 zero_le_one]; congr 1; ring
    rw [e, ENNReal.rpow_one]
    refine mul_le_mul' (ENNReal.rpow_le_rpow ?_ hq1) le_rfl
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (hb z)
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono hpt) ?_)
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq1 ENNReal.ofReal_ne_top)]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq1 ENNReal.ofReal_ne_top) hi.2

lemma pvasm_Lq_Ktr (hd : 1 ≤ d) (i : Fin d) {q : ℝ} (hq : 1 < q) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ z, ‖pvkKtr (pvasmK d i) ε z‖ₑ ^ q ≠ ⊤ := by
  obtain ⟨L, hK⟩ := pvasm_kernel hd i
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set A1 : 𝔼 → ℝ≥0∞ := (closedBall (0 : 𝔼) 1).indicator
    (fun _ => ENNReal.ofReal (L * (ε ^ d)⁻¹) ^ q) with hA1
  set A2 : 𝔼 → ℝ≥0∞ := {z : 𝔼 | 1 < ‖z‖}.indicator
    (fun z => ENNReal.ofReal (L ^ q * ‖z‖ ^ (-((d : ℝ) * q)))) with hA2
  have hT : MeasurableSet {z : 𝔼 | 1 < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hpt : ∀ z, ‖pvkKtr (pvasmK d i) ε z‖ₑ ^ q ≤ A1 z + A2 z := by
    intro z
    by_cases hz : ‖z‖ ≤ 1
    · have hzb : z ∈ closedBall (0 : 𝔼) 1 := by simpa using hz
      have hzt : z ∉ {z : 𝔼 | 1 < ‖z‖} := fun h => absurd (show 1 < ‖z‖ from h) (not_lt.2 hz)
      simp only [hA1, hA2, indicator_of_mem hzb, indicator_of_notMem hzt, add_zero]
      refine ENNReal.rpow_le_rpow ?_ hq0
      rw [← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal (pvk_Ktr_bound hd hK hε z)
    · have hz1 : 1 < ‖z‖ := not_le.1 hz
      have hzb : z ∉ closedBall (0 : 𝔼) 1 := by simpa using hz
      have hzt : z ∈ {z : 𝔼 | 1 < ‖z‖} := hz1
      simp only [hA1, hA2, indicator_of_notMem hzb, indicator_of_mem hzt, zero_add]
      have hn : 0 < ‖z‖ := by linarith
      have hb : |pvkKtr (pvasmK d i) ε z| ≤ L * (‖z‖ ^ d)⁻¹ := by
        unfold pvkKtr
        split_ifs with h
        · exact pvk_K_bound hd hK z
        · simp only [abs_zero]; exact mul_nonneg hK.nonneg (by positivity)
      have hLn : 0 ≤ L * (‖z‖ ^ d)⁻¹ := mul_nonneg hK.nonneg (by positivity)
      calc ‖pvkKtr (pvasmK d i) ε z‖ₑ ^ q ≤ ENNReal.ofReal (L * (‖z‖ ^ d)⁻¹) ^ q := by
            refine ENNReal.rpow_le_rpow ?_ hq0
            rw [← ofReal_norm, Real.norm_eq_abs]
            exact ENNReal.ofReal_le_ofReal hb
        _ = ENNReal.ofReal ((L * (‖z‖ ^ d)⁻¹) ^ q) := (ENNReal.ofReal_rpow_of_nonneg hLn hq0)
        _ = ENNReal.ofReal (L ^ q * ‖z‖ ^ (-((d : ℝ) * q))) := by
            congr 1
            rw [Real.mul_rpow hK.nonneg (by positivity), Real.inv_rpow (by positivity),
              ← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_neg (by positivity)]
  have hm1 : MeasurableSet (closedBall (0 : 𝔼) 1) := measurableSet_closedBall
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono hpt) ?_)
  rw [lintegral_add_left (measurable_const.indicator hm1)]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · rw [lintegral_indicator_const hm1]
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq0 ENNReal.ofReal_ne_top)
      measure_closedBall_lt_top
  · rw [lintegral_indicator hT]
    have hint : IntegrableOn (fun z : 𝔼 => L ^ q * ‖z‖ ^ (-((d : ℝ) * q))) {z : 𝔼 | 1 < ‖z‖} :=
      (pvapi_integrableOn_tail_rpow hd (s := (d : ℝ) * q) (by nlinarith)).const_mul (L ^ q)
    exact hint.lintegral_lt_top

/-! ### the approximate identity `φ_ε * G → G` at Lebesgue points -/

lemma pvasm_approx_id {φ : 𝔼 → ℝ} {Lφ M : ℝ} (hφ : PvkBump d φ Lφ M) {G : 𝔼 → ℝ}
    (hGs : StronglyMeasurable G) (hGl : LocallyIntegrable G volume) :
    ∀ᵐ x ∂(volume : Measure 𝔼),
      Tendsto (fun ε : ℝ => ∫ w, pvkDil ε φ w * G (x - w)) (𝓝[>] 0) (𝓝 (G x)) := by
  filter_upwards [pvk_leb_ratio hGl] with x hx
  have hM := pvk_bump_M_nonneg hφ
  set V : ℝ≥0∞ := volume (ball (0 : 𝔼) 1) with hV
  have hVfin : V ≠ ⊤ := measure_ball_lt_top.ne
  have hvol : ∀ ε : ℝ, 0 < ε → volume (closedBall x ε) = ENNReal.ofReal (ε ^ d) * V := fun ε hε => by
    rw [Measure.addHaar_closedBall _ _ hε.le, finrank_euclideanSpace_fin]
  set S : ℝ → ℝ≥0∞ := fun ε => ∫⁻ y in closedBall x ε, ‖G y - G x‖ₑ with hS
  have hT : MeasurePreserving (fun z : 𝔼 => x - z) volume volume :=
    Measure.measurePreserving_sub_left volume x
  have hA : ∀ r : ℝ, ∫⁻ z in closedBall (0 : 𝔼) r, ‖G (x - z) - G x‖ₑ = S r := by
    intro r
    have hpre : (fun z : 𝔼 => x - z) ⁻¹' closedBall x r = closedBall 0 r := by
      ext z; simp [mem_closedBall, dist_eq_norm]
    have := hT.setLIntegral_comp_preimage (s := closedBall x r) measurableSet_closedBall
      (f := fun y => ‖G y - G x‖ₑ) (hGs.sub stronglyMeasurable_const).enorm
    rw [hpre] at this; exact this
  have key : ∀ ε : ℝ, 0 < ε → S ε < ⊤ →
      ‖(∫ w, pvkDil ε φ w * G (x - w)) - G x‖ₑ ≤ ENNReal.ofReal M * V * (S ε / volume (closedBall x ε)) := by
    intro ε hε hSε
    have hφi := pvasm_dil_integrable hφ hε
    have hφc := pvasm_dil_cont hφ ε
    set f1 : 𝔼 → ℝ := fun w => pvkDil ε φ w * (G (x - w) - G x) with hf1
    have hGm : Measurable fun w : 𝔼 => G (x - w) := hGs.measurable.comp (measurable_const.sub measurable_id)
    have hf1m : Measurable f1 := hφc.measurable.mul (hGm.sub measurable_const)
    have hbound : ∫⁻ w, ‖f1 w‖ₑ ≤ ENNReal.ofReal (M * (ε ^ d)⁻¹) * S ε := by
      calc ∫⁻ w, ‖f1 w‖ₑ ≤ ∫⁻ w, (closedBall (0 : 𝔼) ε).indicator
            (fun w => ENNReal.ofReal (M * (ε ^ d)⁻¹) * ‖G (x - w) - G x‖ₑ) w := by
            refine lintegral_mono fun w => ?_
            by_cases hw : w ∈ closedBall (0 : 𝔼) ε
            · rw [indicator_of_mem hw]
              simp only [hf1, enorm_mul]
              refine mul_le_mul' ?_ le_rfl
              rw [← ofReal_norm, Real.norm_eq_abs]
              refine ENNReal.ofReal_le_ofReal ?_
              unfold pvkDil
              rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ε ^ d)⁻¹)]
              rw [mul_comm M]
              have hb : |φ (ε⁻¹ • w)| ≤ M := by
                rw [abs_of_nonneg (hφ.nonneg _)]; exact hφ.bdd _
              exact mul_le_mul_of_nonneg_left hb (by positivity)
            · rw [indicator_of_notMem hw]
              have hn : ε < ‖w‖ := by simpa [mem_closedBall, dist_zero_right] using hw
              have : φ (ε⁻¹ • w) = 0 := by
                apply hφ.supp
                rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε)]
                calc (1 : ℝ) = ε⁻¹ * ε := by field_simp
                  _ < ε⁻¹ * ‖w‖ := by gcongr
              simp [hf1, pvkDil, this]
        _ = ENNReal.ofReal (M * (ε ^ d)⁻¹) * ∫⁻ w in closedBall (0 : 𝔼) ε, ‖G (x - w) - G x‖ₑ := by
            rw [lintegral_indicator measurableSet_closedBall, lintegral_const_mul']
            · exact ENNReal.ofReal_ne_top
        _ = _ := by rw [hA]
    have hf1i : Integrable f1 volume :=
      ⟨hf1m.aestronglyMeasurable, lt_of_le_of_lt hbound
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSε)⟩
    have hf2i : Integrable (fun w => pvkDil ε φ w * G x) volume := hφi.mul_const _
    have hsum : (fun w => pvkDil ε φ w * G (x - w)) = fun w => f1 w + pvkDil ε φ w * G x := by
      funext w; simp only [hf1]; ring
    have hint1 : ∫ w, pvkDil ε φ w * G x = G x := by
      rw [integral_mul_const, pvk_dil_integral hε, hφ.integral_eq_one, one_mul]
    have : (∫ w, pvkDil ε φ w * G (x - w)) - G x = ∫ w, f1 w := by
      rw [hsum, integral_add hf1i hf2i, hint1]; ring
    rw [this]
    refine (enorm_integral_le_lintegral_enorm f1).trans (hbound.trans (le_of_eq ?_))
    have hv0 : volume (closedBall x ε) ≠ 0 := (measure_closedBall_pos volume x hε).ne'
    have hvf : volume (closedBall x ε) ≠ ⊤ := measure_closedBall_lt_top.ne
    have e1' : S ε / volume (closedBall x ε) * volume (closedBall x ε) = S ε :=
      ENNReal.div_mul_cancel hv0 hvf
    have e2 : ENNReal.ofReal (ε ^ d)⁻¹ * ENNReal.ofReal (ε ^ d) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]
    calc ENNReal.ofReal (M * (ε ^ d)⁻¹) * S ε
        = ENNReal.ofReal M * ENNReal.ofReal (ε ^ d)⁻¹ *
          (S ε / volume (closedBall x ε) * volume (closedBall x ε)) := by
          rw [e1', ENNReal.ofReal_mul hM]
      _ = ENNReal.ofReal M * ENNReal.ofReal (ε ^ d)⁻¹ *
          (S ε / volume (closedBall x ε) * (ENNReal.ofReal (ε ^ d) * V)) := by rw [hvol ε hε]
      _ = ENNReal.ofReal M * V * (S ε / volume (closedBall x ε)) *
          (ENNReal.ofReal (ε ^ d)⁻¹ * ENNReal.ofReal (ε ^ d)) := by ring
      _ = _ := by rw [e2, mul_one]
  -- conclude
  have hratio : Tendsto (fun ε : ℝ => S ε / volume (closedBall x ε)) (𝓝[>] 0) (𝓝 0) := hx
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal M * V * (S ε / volume (closedBall x ε))) (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hratio
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin) : _ ∨ ENNReal.ofReal M * V ≠ ⊤)
    simpa using this
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ S ε < ⊤ := by
    have h1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, S ε / volume (closedBall x ε) < ⊤ :=
      hratio.eventually (gt_mem_nhds ENNReal.zero_lt_top)
    filter_upwards [self_mem_nhdsWithin, h1] with ε hε h1ε
    refine ⟨hε, ?_⟩
    have hv0 : volume (closedBall x ε) ≠ 0 := (measure_closedBall_pos volume x hε).ne'
    have hvf : volume (closedBall x ε) ≠ ⊤ := measure_closedBall_lt_top.ne
    have := ENNReal.mul_lt_top h1ε hvf.lt_top
    rwa [ENNReal.div_mul_cancel hv0 hvf] at this
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_enorm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hev] with ε hε
  exact key ε hε.1 hε.2

/-! ### the main assembly for a strongly measurable `g ∈ L^p` -/

lemma pvasm_pvOdd_meas (hd : 1 ≤ d) (i : Fin d) (W : 𝓢(𝔼, ℝ)) :
    Measurable (HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W) := by
  have hKc := isPvKernel_coord (d := d) i
  obtain ⟨B1, L1, M1, h1⟩ := PvC2.of_schwartz W
  exact pvOdd_measurable_of_lip hd one_pos one_lt_two hKc h1.lipschitzWith fun x =>
    pvK_far_integrable_of_integrable hd one_pos hKc W.integrable x

lemma pvasm_conj_gt {p : ℝ} (hp : 1 < p) : 1 < p.conjExponent :=
  (Real.HolderConjugate.conjExponent hp).symm.lt

lemma pvasm_Lp_apply_bound {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (T : Lp ℝ (ENNReal.ofReal p) (volume : Measure 𝔼) →L[ℝ] Lp ℝ (ENNReal.ofReal p) (volume : Measure 𝔼))
    {CT : ℝ} (hCT : 0 ≤ CT) (hTn : ‖T‖ ≤ CT) {g : 𝔼 → ℝ} (hg : MemLp g (ENNReal.ofReal p) volume) :
    eLpNorm (⇑(T (hg.toLp g))) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal CT * eLpNorm g (ENNReal.ofReal p) volume := by
  have h1 : ‖T (hg.toLp g)‖ ≤ CT * ‖hg.toLp g‖ :=
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hTn (norm_nonneg _))
  have h2 : ‖hg.toLp g‖ = (eLpNorm g (ENNReal.ofReal p) volume).toReal := Lp.norm_toLp g hg
  have h3 : ‖T (hg.toLp g)‖ = (eLpNorm (⇑(T (hg.toLp g))) (ENNReal.ofReal p) volume).toReal :=
    Lp.norm_def _
  rw [h2, h3] at h1
  have hfin : eLpNorm (⇑(T (hg.toLp g))) (ENNReal.ofReal p) volume ≠ ⊤ := Lp.eLpNorm_ne_top _
  rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_toReal hg.eLpNorm_ne_top,
    ← ENNReal.ofReal_mul hCT]
  exact ENNReal.ofReal_le_ofReal h1

theorem pvasm_Lp_main_i (hd : 1 ≤ d) (i : Fin d) {p : ℝ} (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)] {CT : ℝ} (hCT : 0 ≤ CT)
    (T : Lp ℝ (ENNReal.ofReal p) (volume : Measure 𝔼) →L[ℝ] Lp ℝ (ENNReal.ofReal p) (volume : Measure 𝔼))
    (hTn : ‖T‖ ≤ CT)
    (hTW : ∀ W : 𝓢(𝔼, ℝ), T (W.toLp (ENNReal.ofReal p) volume) =ᵐ[volume]
      HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ g : 𝔼 → ℝ, StronglyMeasurable g → MemLp g (ENNReal.ofReal p) volume →
      ∃ G : 𝔼 → ℝ, StronglyMeasurable G ∧ MemLp G (ENNReal.ofReal p) volume ∧
        eLpNorm G (ENNReal.ofReal p) volume ≤ ENNReal.ofReal CT * eLpNorm g (ENNReal.ofReal p) volume ∧
        (∀ ε : ℝ, 0 < ε →
          eLpNorm (fun x => pvTrunc d 1 (fun v : 𝔼 => v i) g ε x) (ENNReal.ofReal p) volume ≤
            ENNReal.ofReal (CT + c) * eLpNorm g (ENNReal.ofReal p) volume) ∧
        ∀ᵐ x ∂(volume : Measure 𝔼),
          Tendsto (fun ε : ℝ => pvTrunc d 1 (fun v : 𝔼 => v i) g ε x) (𝓝[>] 0) (𝓝 (G x)) := by
  obtain ⟨L, hK⟩ := pvasm_kernel hd i
  obtain ⟨Lφ, M, hφ⟩ := pvkBump_of_contDiffBump
    (⟨1 / 2, 1, by norm_num, by norm_num⟩ : ContDiffBump (0 : 𝔼)) (by norm_num)
  set φ := (⟨1 / 2, 1, by norm_num, by norm_num⟩ : ContDiffBump (0 : 𝔼)).normed volume with hφdef
  have hΨi := Psi_integrable hd hK hφ
  have hΨm := pvk_Psi_measurable hd hK hφ
  obtain ⟨c2, hc2⟩ := pvasm_Psi_bdd hd hK hφ
  have hc0 : 0 ≤ ∫ z, ‖pvkPsi (pvasmK d i) φ z‖ := integral_nonneg fun z => norm_nonneg _
  refine ⟨∫ z, ‖pvkPsi (pvasmK d i) φ z‖, hc0, fun g hgs hgL => ?_⟩
  set P := ENNReal.ofReal p with hP
  have hp1 : (1 : ℝ≥0∞) ≤ P := Fact.out
  have hq1 := pvasm_conj_gt hp
  -- the limit function
  set x0 : Lp ℝ P (volume : Measure 𝔼) := hgL.toLp g with hx0
  set G : 𝔼 → ℝ := ⇑(T x0) with hG
  have hGL : MemLp G P volume := Lp.memLp _
  have hGs : StronglyMeasurable G := Lp.stronglyMeasurable _
  have hGnorm : eLpNorm G P volume ≤ ENNReal.ofReal CT * eLpNorm g P volume :=
    pvasm_Lp_apply_bound T hCT hTn hgL
  -- approximating Schwartz functions
  have hdense : DenseRange (SchwartzMap.toLpCLM ℝ ℝ P (volume : Measure 𝔼)) :=
    SchwartzMap.denseRange_toLpCLM (E := 𝔼) (F := ℝ) (p := P) ENNReal.ofReal_ne_top
  obtain ⟨u, hu_mem, hu_tendsto⟩ := mem_closure_iff_seq_limit.1 (hdense x0)
  choose W hW using hu_mem
  have hu' : ∀ n, u n = (W n).toLp P volume := fun n => (hW n).symm
  have E1 : Tendsto (fun n => eLpNorm (fun z => W n z - g z) P volume) atTop (𝓝 0) := by
    have := (Lp.tendsto_Lp_iff_tendsto_eLpNorm u g hgL).1 hu_tendsto
    refine this.congr fun n => ?_
    refine eLpNorm_congr_ae ?_
    rw [hu' n]
    filter_upwards [(W n).coeFn_toLp P volume] with z hz
    simp [hz]
  have E2 : Tendsto (fun n => eLpNorm (fun z => HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) (W n) z - G z)
      P volume) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => T (u n)) atTop (𝓝 (T x0)) := (T.continuous.tendsto _).comp hu_tendsto
    have h2 : T x0 = hGL.toLp G := (Lp.toLp_coeFn (T x0) hGL).symm
    rw [h2] at h1
    have := (Lp.tendsto_Lp_iff_tendsto_eLpNorm (fun n => T (u n)) G hGL).1 h1
    refine this.congr fun n => ?_
    refine eLpNorm_congr_ae ?_
    have := hTW (W n)
    rw [← hu' n] at this
    filter_upwards [this] with z hz
    simp [hz]
  -- the identity at every point
  have hWm : ∀ n, Measurable (⇑(W n)) := fun n => (W n).continuous.measurable
  have hWL : ∀ n, MemLp (⇑(W n)) P volume := fun n => (W n).memLp P volume
  have hTWm : ∀ n, Measurable (HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) (W n)) :=
    fun n => pvasm_pvOdd_meas hd i (W n)
  have hTWL : ∀ n, MemLp (HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) (W n)) P volume := by
    intro n
    have := hTW (W n)
    rw [← hu' n] at this
    exact (Lp.memLp (T (u n))).ae_eq this
  have hident : ∀ ε : ℝ, 0 < ε → ∀ x : 𝔼, pvTrunc d 1 (fun v : 𝔼 => v i) g ε x =
      (∫ w, pvkDil ε φ w * G (x - w)) + ∫ z, pvkDil ε (pvkPsi (pvasmK d i) φ) z * g (x - z) := by
    intro ε hε x
    have hφi := pvasm_dil_integrable hφ hε
    have t1 := pvasm_holder_tendsto hp (pvasm_Ktr_meas hd i ε) (pvasm_Lq_Ktr hd i hq1 hε) hWm
      hgs.measurable hWL hgL E1 x
    have hφb : ∀ z, |pvkDil ε φ z| ≤ (ε ^ d)⁻¹ * M := pvasm_dil_bdd (fun z => by
      rw [abs_of_nonneg (hφ.nonneg z)]; exact hφ.bdd z) hε
    have t2 := pvasm_holder_tendsto hp (pvasm_dil_cont hφ ε).measurable
      (pvasm_Lq_bdd_int hq1.le hφb hφi) hTWm hGs.measurable hTWL hGL E2 x
    have hΨb : ∀ z, |pvkDil ε (pvkPsi (pvasmK d i) φ) z| ≤ (ε ^ d)⁻¹ * c2 := pvasm_dil_bdd hc2 hε
    have hΨεi := pvk_dil_integrable hε hΨi
    have t3 := pvasm_holder_tendsto hp (pvk_dil_measurable hΨm ε)
      (pvasm_Lq_bdd_int hq1.le hΨb hΨεi) hWm hgs.measurable hWL hgL E1 x
    have hsum := t2.add t3
    have heq : ∀ n, (∫ w, pvkDil ε φ w * HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) (W n) (x - w)) +
        (∫ z, pvkDil ε (pvkPsi (pvasmK d i) φ) z * W n (x - z)) =
        ∫ z, pvkKtr (pvasmK d i) ε z * W n (x - z) := fun n => by
      rw [← pvasm_trunc_eq, pvasm_trunc_decomp hd i hK hφ hε (W n) x]
    simp only [heq] at hsum
    rw [pvasm_trunc_eq]
    exact tendsto_nhds_unique t1 hsum
  refine ⟨G, hGs, hGL, hGnorm, ?_, ?_⟩
  · -- the uniform truncation bound on `L^p`
    intro ε hε
    have hfun : (fun x => pvTrunc d 1 (fun v : 𝔼 => v i) g ε x) = fun x =>
        (∫ w, pvkDil ε φ w * G (x - w)) +
          ∫ z, pvkDil ε (pvkPsi (pvasmK d i) φ) z * g (x - z) := funext fun x => hident ε hε x
    rw [hfun]
    refine le_trans (eLpNorm_add_le (f := fun x => ∫ w, pvkDil ε φ w * G (x - w))
      (g := fun x => ∫ z, pvkDil ε (pvkPsi (pvasmK d i) φ) z * g (x - z)) (μ := volume) hp1) ?_
    have hA := young_Psi (F := ℝ) (Ψ := φ) (pvk_bump_cont hφ).measurable (pvk_bump_integrable hφ)
      hp.le (g := G) hGs.aestronglyMeasurable hε
    have hB := young_Psi (F := ℝ) (Ψ := pvkPsi (pvasmK d i) φ) hΨm hΨi hp.le
      (g := g) hgs.aestronglyMeasurable hε
    have hφn : ∫ z, ‖φ z‖ = 1 := by
      have : ∫ z, ‖φ z‖ = ∫ z, φ z :=
        integral_congr_ae (ae_of_all _ fun z => by
          simp [Real.norm_eq_abs, abs_of_nonneg (hφ.nonneg z)])
      rw [this, hφ.integral_eq_one]
    rw [hφn, ENNReal.ofReal_one, one_mul] at hA
    simp only [smul_eq_mul] at hA hB
    calc _ ≤ eLpNorm G P volume +
          ENNReal.ofReal (∫ z, ‖pvkPsi (pvasmK d i) φ z‖) * eLpNorm g P volume := add_le_add hA hB
      _ ≤ ENNReal.ofReal CT * eLpNorm g P volume +
          ENNReal.ofReal (∫ z, ‖pvkPsi (pvasmK d i) φ z‖) * eLpNorm g P volume :=
          add_le_add hGnorm le_rfl
      _ = _ := by rw [← add_mul, ENNReal.ofReal_add hCT hc0]
  · -- almost everywhere convergence
    filter_upwards [pvasm_approx_id hφ hGs (hGL.locallyIntegrable hp1),
      ae_tendsto_Psi (F := ℝ) hd hK hφ hp1 hgL] with x h1 h2
    have h3 : Tendsto (fun ε : ℝ => (∫ w, pvkDil ε φ w * G (x - w)) +
        ∫ z, pvkDil ε (pvkPsi (pvasmK d i) φ) z * g (x - z)) (𝓝[>] 0) (𝓝 (G x + 0)) := by
      refine h1.add ?_
      simpa only [smul_eq_mul] using h2
    rw [add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hident ε hε x).symm

/-! ### the statements for arbitrary `g ∈ L^p` -/

lemma pvasm_trunc_congr (i : Fin d) {g g' : 𝔼 → ℝ} (h : g =ᵐ[volume] g') (ε : ℝ) (x : 𝔼) :
    pvTrunc d 1 (fun v : 𝔼 => v i) g ε x = pvTrunc d 1 (fun v : 𝔼 => v i) g' ε x := by
  simp only [pvasm_trunc_eq]
  refine integral_congr_ae ?_
  filter_upwards [(Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae_eq_comp h]
    with z hz
  simp only [Function.comp] at hz
  rw [hz]

/-- **PV-ASM, deliverable (2)**: for `1 < p < ∞` there is `C` (depending on `d, p` only) such that for every
`g ∈ L^p` and every coordinate `i`: the truncations satisfy `‖T_ε g‖_p ≤ C ‖g‖_p` for all `ε > 0`, and there
is `G ∈ L^p` with `‖G‖_p ≤ C ‖g‖_p`, `T_ε g(x) → G(x)` as `ε → 0+` for a.e. `x`, hence
`pvOdd d 1 (u_i) g = G` a.e. (the principal value exists a.e.). -/
theorem pvasm_Lp_ae_pv (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin d) (g : 𝔼 → ℝ), MemLp g (ENNReal.ofReal p) volume →
      (∀ ε : ℝ, 0 < ε →
        eLpNorm (fun x => pvTrunc d 1 (fun v : 𝔼 => v i) g ε x) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal p) volume) ∧
      ∃ G : 𝔼 → ℝ, MemLp G (ENNReal.ofReal p) volume ∧
        eLpNorm G (ENNReal.ofReal p) volume ≤ ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal p) volume ∧
        (∀ᵐ x ∂(volume : Measure 𝔼),
          Tendsto (fun ε : ℝ => pvTrunc d 1 (fun v : 𝔼 => v i) g ε x) (𝓝[>] 0) (𝓝 (G x))) ∧
        HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) g =ᵐ[volume] G := by
  have := pvasm_fact hp
  obtain ⟨CT, hCT, hT⟩ := pvasm_T_extend hd hp
  choose T hTn hTW using hT
  have h := fun i : Fin d => pvasm_Lp_main_i hd i hp hCT (T i) (hTn i) (hTW i)
  choose c hc0 hc using h
  have hsum0 : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc0 i
  refine ⟨CT + ∑ i, c i, add_nonneg hCT hsum0, fun i g hg => ?_⟩
  have hae : g =ᵐ[volume] hg.aestronglyMeasurable.mk g := hg.aestronglyMeasurable.ae_eq_mk
  set g' := hg.aestronglyMeasurable.mk g with hg'
  have hgs : StronglyMeasurable g' := hg.aestronglyMeasurable.stronglyMeasurable_mk
  have hg'L : MemLp g' (ENNReal.ofReal p) volume := hg.ae_eq hae
  have hn : eLpNorm g' (ENNReal.ofReal p) volume = eLpNorm g (ENNReal.ofReal p) volume :=
    eLpNorm_congr_ae hae.symm
  obtain ⟨G, hGs, hGL, hGn, hTr, hlim⟩ := hc i g' hgs hg'L
  rw [hn] at hGn hTr
  have hcle : CT + c i ≤ CT + ∑ j, c j := by
    have := Finset.single_le_sum (f := c) (fun j _ => hc0 j) (Finset.mem_univ i)
    linarith
  refine ⟨fun ε hε => ?_, G, hGL, ?_, ?_, ?_⟩
  · have hfun : (fun x => pvTrunc d 1 (fun v : 𝔼 => v i) g ε x) =
        fun x => pvTrunc d 1 (fun v : 𝔼 => v i) g' ε x :=
      funext fun x => pvasm_trunc_congr i hae ε x
    rw [hfun]
    exact (hTr ε hε).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcle) le_rfl)
  · exact hGn.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl)
  · filter_upwards [hlim] with x hx
    simpa only [pvasm_trunc_congr i hae] using hx
  · filter_upwards [hlim] with x hx
    rw [pvOdd_def]
    have hx' : Tendsto (fun ε : ℝ => pvTrunc d 1 (fun v : 𝔼 => v i) g ε x) (𝓝[>] 0) (𝓝 (G x)) := by
      simpa only [pvasm_trunc_congr i hae] using hx
    exact hx'.limUnder_eq

/-- **`lp_screened_negative_order`, second conjunct, for the linear `Ω(u) = u_i`** (PV-ASM, deliverable (3)):
for `1 < p < ∞` there is `C` (depending on `d, p`) such that for every coordinate `i`, every `a ∈ L^∞` and
`W ∈ L^p`: `‖pvOdd d 1 (u_i) (a W)‖_p ≤ C ‖a‖_∞ ‖W‖_p`.  (The frozen statement has `2 ≤ p` and a general
`IsOddSmooth Ω`; here all `1 < p` and `Ω(u) = u_i`.) -/
theorem lp_screened_negative_order_theta_one_lin (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, ∀ (i : Fin d) (a W : 𝔼 → ℝ), MemLp a ⊤ volume → MemLp W (ENNReal.ofReal p) volume →
      eLpNorm (HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) fun x => a x * W x)
          (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm a ⊤ volume * eLpNorm W (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC0, hC⟩ := pvasm_Lp_ae_pv hd hp
  refine ⟨C, fun i a W ha hW => ?_⟩
  have hprod : eLpNorm (a • W) (ENNReal.ofReal p) volume ≤
      eLpNorm a ⊤ volume * eLpNorm W (ENNReal.ofReal p) volume :=
    eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm _ ha.aestronglyMeasurable
  have hg : MemLp (fun x => a x * W x) (ENNReal.ofReal p) volume := by
    have : (fun x => a x * W x) = a • W := rfl
    rw [this]
    exact lt_of_le_of_lt hprod (ENNReal.mul_lt_top ha hW)
  obtain ⟨-, G, hGL, hGn, -, hpv⟩ := hC i _ hg
  rw [eLpNorm_congr_ae hpv, mul_assoc]
  refine hGn.trans (mul_le_mul' le_rfl ?_)
  exact hprod

/-- the exact shape of the frozen second conjunct of `lp_screened_negative_order` for `Ω(u) = u_i`
(`2 ≤ p`; the frozen hypothesis `IsOddSmooth Ω` holds for the coordinate function, not needed here) -/
theorem lp_screened_negative_order_theta_one_coord (hd : 1 ≤ d) {p : ℝ} (hp : 2 ≤ p) (i : Fin d) :
    ∃ C : ℝ, ∀ a W : 𝔼 → ℝ, MemLp a ⊤ volume → MemLp W (ENNReal.ofReal p) volume →
      eLpNorm (HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) fun x => a x * W x)
          (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm a ⊤ volume * eLpNorm W (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC⟩ := lp_screened_negative_order_theta_one_lin hd (show 1 < p by linarith)
  exact ⟨C, fun a W ha hW => hC i a W ha hW⟩

end HRS.CZ.PvAsm
