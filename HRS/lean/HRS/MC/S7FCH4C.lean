import HRS.MC.S7FCH4B

/-!
# S7FCH4C: `L^p` calculus on `ℝ≥0∞` and the transport lemma (H4, part C)

`S7FCH4_transport`: for a coupling `π` of two laws `μ, ν` on `C([0,T];E_r)` and continuous integrable maps `Y, Y'` with
`‖Y u - Y' v‖ ≤ Λ (1 + ‖u‖ + ‖v‖)(‖u - v‖ + ε)`, the `W_q` distance of the pushed-forward pairs
`(u, ι(Y u - ∫Y dμ))` and `(v, ι(Y' v - ∫Y' dν))` is bounded by `δ + 2√T Λ M (δ + ε)` with `δ = ‖u - v‖_{L^{2q}(π)}`,
`M = ‖1 + ‖u‖ + ‖v‖‖_{L^{2q}(π)}`.
-/
open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.FCPlan
open scoped ENNReal NNReal
noncomputable section
namespace HRS.MC.Sec7.S7FCH4

/-- The `L^p(π)` "norm" of an `ℝ≥0∞`-valued function. -/
def S7FCH4_Lp {α : Type*} [MeasurableSpace α] (p : ℝ) (π : Measure α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ a, f a ^ p ∂π) ^ (1 / p)

section Lp
variable {α : Type*} [MeasurableSpace α] {π : Measure α}

theorem S7FCH4_Lp_mono {p : ℝ} (hp : 0 < p) {f g : α → ℝ≥0∞} (h : ∀ a, f a ≤ g a) :
    S7FCH4_Lp p π f ≤ S7FCH4_Lp p π g :=
  ENNReal.rpow_le_rpow (lintegral_mono fun a => ENNReal.rpow_le_rpow (h a) hp.le) (by positivity)

theorem S7FCH4_Lp_add {p : ℝ} (hp : 1 ≤ p) {f g : α → ℝ≥0∞} (hf : AEMeasurable f π)
    (hg : AEMeasurable g π) :
    S7FCH4_Lp p π (fun a => f a + g a) ≤ S7FCH4_Lp p π f + S7FCH4_Lp p π g :=
  ENNReal.lintegral_Lp_add_le hf hg hp

theorem S7FCH4_Lp_const_mul {p : ℝ} (hp : 0 < p) {c : ℝ≥0∞} (hc : c ≠ ⊤) (f : α → ℝ≥0∞) :
    S7FCH4_Lp p π (fun a => c * f a) = c * S7FCH4_Lp p π f := by
  unfold S7FCH4_Lp
  have h1 : ∀ a, (c * f a) ^ p = c ^ p * f a ^ p := fun a => ENNReal.mul_rpow_of_nonneg _ _ hp.le
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le hc),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
  congr 2
  field_simp
  simp

theorem S7FCH4_Lp_const [IsProbabilityMeasure π] {p : ℝ} (hp : 0 < p) (c : ℝ≥0∞) :
    S7FCH4_Lp p π (fun _ => c) = c := by
  unfold S7FCH4_Lp
  simp only [lintegral_const, measure_univ, mul_one]
  rw [← ENNReal.rpow_mul]
  rw [mul_one_div_cancel hp.ne']
  simp

theorem S7FCH4_Lp_mono_exp [IsProbabilityMeasure π] {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) {f : α → ℝ≥0∞}
    (hf : Measurable f) : S7FCH4_Lp p π f ≤ S7FCH4_Lp q π f :=
  HRS.lintegral_rpow_mono_meas π hf hp hpq

theorem S7FCH4_Lp_mul {p : ℝ} (hp : 0 < p) {f g : α → ℝ≥0∞} (hf : AEMeasurable f π)
    (hg : AEMeasurable g π) :
    S7FCH4_Lp p π (fun a => f a * g a) ≤ S7FCH4_Lp (2 * p) π f * S7FCH4_Lp (2 * p) π g := by
  unfold S7FCH4_Lp
  have hHC : Real.HolderConjugate 2 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq π hHC (f := fun a => f a ^ p) (g := fun a => g a ^ p)
    (hf.pow_const p) (hg.pow_const p)
  have e1 : ∀ a, (f a ^ p) ^ (2 : ℝ) = f a ^ (2 * p) := fun a => by
    rw [← ENNReal.rpow_mul]; congr 1; ring
  have e2 : ∀ a, (g a ^ p) ^ (2 : ℝ) = g a ^ (2 * p) := fun a => by
    rw [← ENNReal.rpow_mul]; congr 1; ring
  simp only [e1, e2] at H
  have e3 : ∀ a, (f a * g a) ^ p = f a ^ p * g a ^ p := fun a => ENNReal.mul_rpow_of_nonneg _ _ hp.le
  simp_rw [e3]
  calc (∫⁻ a, f a ^ p * g a ^ p ∂π) ^ (1 / p)
      ≤ ((∫⁻ a, f a ^ (2 * p) ∂π) ^ (1 / (2 : ℝ)) * (∫⁻ a, g a ^ (2 * p) ∂π) ^ (1 / (2 : ℝ))) ^ (1 / p) :=
        ENNReal.rpow_le_rpow H (by positivity)
    _ = _ := by
        have h12 : (1 / (2 : ℝ)) * (1 / p) = 1 / (2 * p) := by field_simp
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, h12]
end Lp


section Transport
variable {d : ℕ} {r T : ℝ}

theorem S7FCH4_transport (hT : 0 ≤ T) {q : ℝ} (hq : 1 ≤ q)
    (μ ν : Measure (PathSpace d r T)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Y Y' : PathSpace d r T → PathSpace d r T) (hY : Continuous Y) (hY' : Continuous Y')
    (hYi : Integrable Y μ) (hY'i : Integrable Y' ν)
    (π : Measure (PathSpace d r T × PathSpace d r T)) (hπ : IsCoupling π μ ν)
    (Λ ε : ℝ) (hΛ : 0 ≤ Λ) (hε : 0 ≤ ε)
    (hpt : ∀ u v, ‖Y u - Y' v‖ ≤ Λ * ((1 + ‖u‖ + ‖v‖) * (‖u - v‖ + ε))) :
    wassersteinE q (μ.map (fun u => (u, S7FCH4_iota hT (Y u - ∫ x, Y x ∂μ))))
      (ν.map (fun v => (v, S7FCH4_iota hT (Y' v - ∫ x, Y' x ∂ν)))) ≤
    S7FCH4_Lp (2 * q) π (fun z => ENNReal.ofReal ‖z.1 - z.2‖) +
      ENNReal.ofReal (2 * Real.sqrt T * Λ) *
        S7FCH4_Lp (2 * q) π (fun z => ENNReal.ofReal (1 + ‖z.1‖ + ‖z.2‖)) *
        (S7FCH4_Lp (2 * q) π (fun z => ENNReal.ofReal ‖z.1 - z.2‖) + ENNReal.ofReal ε) := by
  have := hπ.isProbabilityMeasure
  have hq0 : 0 < q := by linarith
  set C : PathSpace d r T := ∫ x, Y x ∂μ with hC
  set C' : PathSpace d r T := ∫ x, Y' x ∂ν with hC'
  set Ψ : PathSpace d r T → PathSpace d r T × L2Path d r T :=
    fun u => (u, S7FCH4_iota hT (Y u - C)) with hΨ
  set Ψ' : PathSpace d r T → PathSpace d r T × L2Path d r T :=
    fun v => (v, S7FCH4_iota hT (Y' v - C')) with hΨ'
  have hΨm : Measurable Ψ :=
    measurable_id.prodMk ((S7FCH4_iota_continuous hT).measurable.comp (hY.measurable.sub_const _))
  have hΨm' : Measurable Ψ' :=
    measurable_id.prodMk ((S7FCH4_iota_continuous hT).measurable.comp (hY'.measurable.sub_const _))
  set G : PathSpace d r T × PathSpace d r T →
      (PathSpace d r T × L2Path d r T) × (PathSpace d r T × L2Path d r T) :=
    fun z => (Ψ z.1, Ψ' z.2) with hG
  have hGm : Measurable G := (hΨm.comp measurable_fst).prodMk (hΨm'.comp measurable_snd)
  have hcoup : IsCoupling (π.map G) (μ.map Ψ) (ν.map Ψ') := by
    constructor
    · rw [Measure.map_map measurable_fst hGm]
      have : (Prod.fst ∘ G) = Ψ ∘ Prod.fst := rfl
      rw [this, ← Measure.map_map hΨm measurable_fst, hπ.1]
    · rw [Measure.map_map measurable_snd hGm]
      have : (Prod.snd ∘ G) = Ψ' ∘ Prod.snd := rfl
      rw [this, ← Measure.map_map hΨm' measurable_snd, hπ.2]
  refine (wassersteinE_le_cost hcoup).trans ?_
  -- integrability of the marginal compositions
  have hYi1 : Integrable (fun z : PathSpace d r T × PathSpace d r T => Y z.1) π := by
    have h := (integrable_map_measure (μ := π) (f := Prod.fst) (g := Y) hY.aestronglyMeasurable
      measurable_fst.aemeasurable).1 (by rw [hπ.1]; exact hYi)
    exact h
  have hYi2 : Integrable (fun z : PathSpace d r T × PathSpace d r T => Y' z.2) π := by
    have h := (integrable_map_measure (μ := π) (f := Prod.snd) (g := Y') hY'.aestronglyMeasurable
      measurable_snd.aemeasurable).1 (by rw [hπ.2]; exact hY'i)
    exact h
  have hCint : C = ∫ z, Y z.1 ∂π := by
    rw [hC, ← hπ.1, integral_map measurable_fst.aemeasurable hY.aestronglyMeasurable]
  have hC'int : C' = ∫ z, Y' z.2 ∂π := by
    rw [hC', ← hπ.2, integral_map measurable_snd.aemeasurable hY'.aestronglyMeasurable]
  set Fr : PathSpace d r T × PathSpace d r T → ℝ := fun z => ‖Y z.1 - Y' z.2‖ with hFr
  have hFrm : Measurable Fr := ((hY.comp continuous_fst).sub (hY'.comp continuous_snd)).norm.measurable
  have hFri : Integrable Fr π := (hYi1.sub hYi2).norm
  set I : ℝ := ∫ z, Fr z ∂π with hI
  have hI0 : 0 ≤ I := integral_nonneg fun z => norm_nonneg _
  have hCC : ‖C - C'‖ ≤ I := by
    rw [hCint, hC'int, ← integral_sub hYi1 hYi2]
    exact norm_integral_le_integral_norm _
  -- pointwise bound for the cost
  have hptcost : ∀ z : PathSpace d r T × PathSpace d r T,
      ‖(G z).1 - (G z).2‖ ≤ ‖z.1 - z.2‖ + Real.sqrt T * (Fr z + I) := by
    intro z
    have e : (G z).1 - (G z).2 = (z.1 - z.2, S7FCH4_iota hT ((Y z.1 - Y' z.2) - (C - C'))) := by
      show Ψ z.1 - Ψ' z.2 = _
      simp only [hΨ, hΨ', Prod.mk_sub_mk]
      congr 1
      rw [← S7FCH4_iota_sub]
      congr 1
      abel
    rw [e, Prod.norm_def]
    have hFnn : 0 ≤ Fr z := norm_nonneg _
    refine max_le (le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg T) (add_nonneg hFnn hI0))) ?_
    refine (S7FCH4_norm_iota_le hT _).trans ?_
    have : ‖(Y z.1 - Y' z.2) - (C - C')‖ ≤ Fr z + I := (norm_sub_le _ _).trans (add_le_add le_rfl hCC)
    have h2 : Real.sqrt T * ‖(Y z.1 - Y' z.2) - (C - C')‖ ≤ Real.sqrt T * (Fr z + I) :=
      mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg T)
    nlinarith [norm_nonneg (z.1 - z.2)]
  -- ENNReal bookkeeping
  have hsqrt0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  set cT : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt T) with hcT
  have hcTtop : cT ≠ ⊤ := ENNReal.ofReal_ne_top
  set a : PathSpace d r T × PathSpace d r T → ℝ≥0∞ := fun z => ENNReal.ofReal ‖z.1 - z.2‖ with ha
  set Fe : PathSpace d r T × PathSpace d r T → ℝ≥0∞ := fun z => ENNReal.ofReal (Fr z) with hFe
  set Ae : PathSpace d r T × PathSpace d r T → ℝ≥0∞ := fun z => ENNReal.ofReal (1 + ‖z.1‖ + ‖z.2‖) with hAe
  set J : ℝ≥0∞ := ENNReal.ofReal I with hJ
  have ham : Measurable a := ENNReal.measurable_ofReal.comp (continuous_fst.sub continuous_snd).norm.measurable
  have hFem : Measurable Fe := ENNReal.measurable_ofReal.comp hFrm
  have hAem : Measurable Ae := ENNReal.measurable_ofReal.comp
    ((continuous_const.add continuous_fst.norm).add continuous_snd.norm).measurable
  have hJeq : J = ∫⁻ z, Fe z ∂π :=
    ofReal_integral_eq_lintegral_ofReal hFri (ae_of_all _ fun z => norm_nonneg _)
  have hq2 : 1 ≤ 2 * q := by linarith
  have hq20 : 0 < 2 * q := by linarith
  have hcost : ∀ z : PathSpace d r T × PathSpace d r T,
      ENNReal.ofReal (‖(G z).1 - (G z).2‖ ^ q) = (ENNReal.ofReal ‖(G z).1 - (G z).2‖) ^ q :=
    fun z => ofReal_norm_rpow hq0.le
  -- left-hand side as an `Lp` norm
  have hlhs : (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ q) ∂(π.map G)) ^ (1 / q) ≤
      S7FCH4_Lp q π (fun z => ENNReal.ofReal ‖(G z).1 - (G z).2‖) := by
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    refine (lintegral_map_le _ hGm.aemeasurable).trans (le_of_eq (lintegral_congr fun z => hcost z))
  -- pointwise bound in `ℝ≥0∞`
  have hpw : ∀ z, ENNReal.ofReal ‖(G z).1 - (G z).2‖ ≤ a z + cT * (Fe z + J) := by
    intro z
    refine (ENNReal.ofReal_le_ofReal (hptcost z)).trans (le_of_eq ?_)
    have hFnn : 0 ≤ Fr z := norm_nonneg _
    rw [ENNReal.ofReal_add (norm_nonneg _) (mul_nonneg hsqrt0 (add_nonneg hFnn hI0)),
      ENNReal.ofReal_mul hsqrt0, ENNReal.ofReal_add hFnn hI0]
  have hJle : J ≤ S7FCH4_Lp q π Fe := by
    have h1 : S7FCH4_Lp 1 π Fe = J := by
      rw [hJeq]; unfold S7FCH4_Lp; simp
    rw [← h1]
    exact S7FCH4_Lp_mono_exp one_pos hq hFem
  -- bound on the `Fe` norm
  have hFeb : S7FCH4_Lp q π Fe ≤ ENNReal.ofReal Λ *
      (S7FCH4_Lp (2 * q) π Ae * (S7FCH4_Lp (2 * q) π a + ENNReal.ofReal ε)) := by
    have hpw2 : ∀ z, Fe z ≤ ENNReal.ofReal Λ * (Ae z * (a z + ENNReal.ofReal ε)) := by
      intro z
      refine (ENNReal.ofReal_le_ofReal (hpt z.1 z.2)).trans (le_of_eq ?_)
      have h1 : 0 ≤ 1 + ‖z.1‖ + ‖z.2‖ := by positivity
      rw [ENNReal.ofReal_mul hΛ, ENNReal.ofReal_mul h1, ENNReal.ofReal_add (norm_nonneg _) hε]
    calc S7FCH4_Lp q π Fe ≤ S7FCH4_Lp q π (fun z => ENNReal.ofReal Λ * (Ae z * (a z + ENNReal.ofReal ε))) :=
          S7FCH4_Lp_mono hq0 hpw2
      _ = ENNReal.ofReal Λ * S7FCH4_Lp q π (fun z => Ae z * (a z + ENNReal.ofReal ε)) :=
          S7FCH4_Lp_const_mul hq0 ENNReal.ofReal_ne_top _
      _ ≤ ENNReal.ofReal Λ * (S7FCH4_Lp (2 * q) π Ae * S7FCH4_Lp (2 * q) π (fun z => a z + ENNReal.ofReal ε)) := by
          gcongr
          exact S7FCH4_Lp_mul hq0 hAem.aemeasurable (ham.add_const _).aemeasurable
      _ ≤ _ := by
          gcongr
          refine (S7FCH4_Lp_add hq2 ham.aemeasurable aemeasurable_const).trans ?_
          rw [S7FCH4_Lp_const hq20]
  have haq : S7FCH4_Lp q π a ≤ S7FCH4_Lp (2 * q) π a := S7FCH4_Lp_mono_exp hq0 (by linarith) ham
  -- assemble
  have hmain : S7FCH4_Lp q π (fun z => ENNReal.ofReal ‖(G z).1 - (G z).2‖) ≤
      S7FCH4_Lp q π a + cT * (2 * S7FCH4_Lp q π Fe) := by
    calc S7FCH4_Lp q π (fun z => ENNReal.ofReal ‖(G z).1 - (G z).2‖)
        ≤ S7FCH4_Lp q π (fun z => a z + cT * (Fe z + J)) := S7FCH4_Lp_mono hq0 hpw
      _ ≤ S7FCH4_Lp q π a + S7FCH4_Lp q π (fun z => cT * (Fe z + J)) :=
          S7FCH4_Lp_add hq ham.aemeasurable ((hFem.add_const J).const_mul cT).aemeasurable
      _ = S7FCH4_Lp q π a + cT * S7FCH4_Lp q π (fun z => Fe z + J) := by
          rw [S7FCH4_Lp_const_mul hq0 hcTtop]
      _ ≤ S7FCH4_Lp q π a + cT * (S7FCH4_Lp q π Fe + J) := by
          gcongr
          refine (S7FCH4_Lp_add hq hFem.aemeasurable aemeasurable_const).trans ?_
          rw [S7FCH4_Lp_const hq0]
      _ ≤ S7FCH4_Lp q π a + cT * (2 * S7FCH4_Lp q π Fe) := by
          gcongr
          calc S7FCH4_Lp q π Fe + J ≤ S7FCH4_Lp q π Fe + S7FCH4_Lp q π Fe := by gcongr
            _ = 2 * S7FCH4_Lp q π Fe := by ring
  have hc2 : ENNReal.ofReal (2 * Real.sqrt T * Λ) = 2 * cT * ENNReal.ofReal Λ := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  calc (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ q) ∂(π.map G)) ^ (1 / q)
      ≤ S7FCH4_Lp q π (fun z => ENNReal.ofReal ‖(G z).1 - (G z).2‖) := hlhs
    _ ≤ S7FCH4_Lp q π a + cT * (2 * S7FCH4_Lp q π Fe) := hmain
    _ ≤ S7FCH4_Lp (2 * q) π a + cT * (2 * (ENNReal.ofReal Λ *
          (S7FCH4_Lp (2 * q) π Ae * (S7FCH4_Lp (2 * q) π a + ENNReal.ofReal ε)))) := by
        gcongr
    _ = _ := by
        rw [hc2]; ring

end Transport

end HRS.MC.Sec7.S7FCH4
