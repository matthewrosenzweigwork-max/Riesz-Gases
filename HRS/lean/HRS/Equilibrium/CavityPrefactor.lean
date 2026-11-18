/-
# HRS.Equilibrium.CavityPrefactor — the conditional density of the pole marginal (Lemma 4.6, `R:eq:prefactor`)

Continuation of `CavityResponse.lean`: the pole first marginal is `e^{-tλ g_+(x - y)} E[e^{-v_Y(y)}/Z_Y]`
(`critPole_formula`), the bounds on `v_Y` and `Z_Y`, and the proof of `cavity_response_proof`.
-/
import HRS.Equilibrium.CavityResponse

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace CavResp

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer

/-- Disintegration of a tilted product law along the first coordinate. -/
theorem firstCoord_disint {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {m : ℕ}
    (a : Torus d → ℝ) (Wm : Config d m → ℝ) (k : Torus d → Config d m → ℝ)
    (ha : Measurable a) (hWm : Measurable Wm) (hk : Measurable fun q : Torus d × Config d m => k q.1 q.2)
    (Wb : ℝ) (hWb : ∀ X : Config d (m + 1), a (X 0) + Wm (Fin.tail X) - k (X 0) (Fin.tail X) ≤ Wb)
    (hZ0 : ∀ Y' : Config d m, ∫⁻ y, ENNReal.ofReal (Real.exp (a y - k y Y')) ∂μ ≠ 0)
    (hZt : ∀ Y' : Config d m, ∫⁻ y, ENNReal.ofReal (Real.exp (a y - k y Y')) ∂μ ≠ ∞)
    {A : Set (Torus d)} (hA : MeasurableSet A) :
    (tiltMeasure (Measure.pi fun _ : Fin (m + 1) => μ)
        (fun X => a (X 0) + Wm (Fin.tail X) - k (X 0) (Fin.tail X))) {X | X 0 ∈ A} =
      ∫⁻ y in A, ENNReal.ofReal (Real.exp (a y)) *
        ∫⁻ X, ENNReal.ofReal (Real.exp (-k y (Fin.tail X))) /
          (∫⁻ y', ENNReal.ofReal (Real.exp (a y' - k y' (Fin.tail X))) ∂μ)
          ∂(tiltMeasure (Measure.pi fun _ : Fin (m + 1) => μ)
            (fun X => a (X 0) + Wm (Fin.tail X) - k (X 0) (Fin.tail X))) ∂μ := by
  set ν : Measure (Config d (m + 1)) := Measure.pi fun _ : Fin (m + 1) => μ with hν
  set νm : Measure (Config d m) := Measure.pi fun _ : Fin m => μ with hνm
  set Wf : Config d (m + 1) → ℝ := fun X => a (X 0) + Wm (Fin.tail X) - k (X 0) (Fin.tail X) with hWf
  have hT : Measurable fun X : Config d (m + 1) => Fin.tail X :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  have h0 : Measurable fun X : Config d (m + 1) => X 0 := measurable_pi_apply 0
  have hWfm : Measurable Wf :=
    ((ha.comp h0).add (hWm.comp hT)).sub (hk.comp (h0.prodMk hT))
  have hZ := tilt_normalizer_ne ν Wf hWfm Wb hWb
  set e : Config d (m + 1) → ℝ≥0∞ := fun X => ENNReal.ofReal (Real.exp (Wf X)) with he
  have hem : Measurable e := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hWfm)
  set Z : ℝ≥0∞ := ∫⁻ X, e X ∂ν with hZdef
  have hP : tiltMeasure ν Wf = Z⁻¹ • ν.withDensity e := rfl
  -- integrals against `P`
  have F1 : ∀ F : Config d (m + 1) → ℝ≥0∞, Measurable F →
      ∫⁻ X, F X ∂(tiltMeasure ν Wf) = Z⁻¹ * ∫⁻ X, F X * e X ∂ν := by
    intro F hF
    rw [hP, lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hem hF, smul_eq_mul]
    simp [mul_comm]
  have F2 : ∀ H : Config d (m + 1) → ℝ≥0∞, Measurable H →
      ∫⁻ X, H X ∂ν = ∫⁻ y, ∫⁻ Y', H (Fin.cons y Y') ∂νm ∂μ := fun H hH =>
    lintegral_pi_succ μ H hH
  have F3 : ∀ y Y', e (Fin.cons y Y') = ENNReal.ofReal (Real.exp (a y - k y Y')) *
      ENNReal.ofReal (Real.exp (Wm Y')) := by
    intro y Y'
    simp only [he, hWf, Fin.cons_zero, Fin.tail_cons]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  -- the normaliser in the cavity variable
  set Zt : Config d m → ℝ≥0∞ := fun Y' => ∫⁻ y, ENNReal.ofReal (Real.exp (a y - k y Y')) ∂μ with hZt_def
  have hE1m : Measurable fun q : Torus d × Config d m => ENNReal.ofReal (Real.exp (a q.1 - k q.1 q.2)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((ha.comp measurable_fst).sub hk))
  have hZtm : Measurable Zt := Measurable.lintegral_prod_left' hE1m
  have hWmE : Measurable fun Y' : Config d m => ENNReal.ofReal (Real.exp (Wm Y')) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hWm)
  -- the `y`-dependent test function
  set Ψ : Torus d → Config d m → ℝ≥0∞ := fun y Y' =>
    ENNReal.ofReal (Real.exp (-k y Y')) / Zt Y' with hΨ
  have hΨm : ∀ y, Measurable (Ψ y) := by
    intro y
    simp only [hΨ, div_eq_mul_inv]
    exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (hk.comp measurable_prodMk_left).neg)).mul hZtm.inv
  have hΨZ : ∀ y Y', Ψ y Y' * Zt Y' = ENNReal.ofReal (Real.exp (-k y Y')) := by
    intro y Y'
    simp only [hΨ]
    exact ENNReal.div_mul_cancel (hZ0 Y') (hZt Y')
  -- the right side, `J y`
  have hJ : ∀ y, ∫⁻ X, Ψ y (Fin.tail X) ∂(tiltMeasure ν Wf) =
      Z⁻¹ * ∫⁻ Y', ENNReal.ofReal (Real.exp (-k y Y')) * ENNReal.ofReal (Real.exp (Wm Y')) ∂νm := by
    intro y
    rw [F1 (fun X => Ψ y (Fin.tail X)) ((hΨm y).comp hT)]
    congr 1
    have hint : Measurable fun X : Config d (m + 1) => Ψ y (Fin.tail X) * e X := ((hΨm y).comp hT).mul hem
    rw [F2 _ hint]
    simp only [Fin.tail_cons, F3]
    have hswap : ∫⁻ y0, ∫⁻ Y', Ψ y Y' * (ENNReal.ofReal (Real.exp (a y0 - k y0 Y')) *
          ENNReal.ofReal (Real.exp (Wm Y'))) ∂νm ∂μ =
        ∫⁻ Y', ∫⁻ y0, Ψ y Y' * (ENNReal.ofReal (Real.exp (a y0 - k y0 Y')) *
          ENNReal.ofReal (Real.exp (Wm Y'))) ∂μ ∂νm := by
      refine lintegral_lintegral_swap (f := fun y0 Y' => Ψ y Y' * (ENNReal.ofReal (Real.exp (a y0 - k y0 Y')) *
          ENNReal.ofReal (Real.exp (Wm Y')))) ?_
      exact (((hΨm y).comp measurable_snd).mul (hE1m.mul (hWmE.comp measurable_snd))).aemeasurable
    rw [hswap]
    refine lintegral_congr fun Y' => ?_
    have hc : ∀ y0, Ψ y Y' * (ENNReal.ofReal (Real.exp (a y0 - k y0 Y')) *
        ENNReal.ofReal (Real.exp (Wm Y'))) =
        (Ψ y Y' * ENNReal.ofReal (Real.exp (Wm Y'))) * ENNReal.ofReal (Real.exp (a y0 - k y0 Y')) :=
      fun y0 => by ring
    simp_rw [hc]
    rw [lintegral_const_mul (f := fun y0 => ENNReal.ofReal (Real.exp (a y0 - k y0 Y'))) _
      (hE1m.comp measurable_prodMk_right)]
    calc (Ψ y Y' * ENNReal.ofReal (Real.exp (Wm Y'))) * Zt Y' =
        (Ψ y Y' * Zt Y') * ENNReal.ofReal (Real.exp (Wm Y')) := by ring
      _ = _ := by rw [hΨZ]
  -- the left side
  have hLHS : (tiltMeasure ν Wf) {X | X 0 ∈ A} =
      Z⁻¹ * ∫⁻ y in A, ∫⁻ Y', e (Fin.cons y Y') ∂νm ∂μ := by
    have hS : MeasurableSet {X : Config d (m + 1) | X 0 ∈ A} := h0 hA
    rw [hP, Measure.smul_apply, withDensity_apply _ hS, smul_eq_mul, ← lintegral_indicator hS,
      F2 _ (hem.indicator hS), ← lintegral_indicator hA]
    congr 1
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ A
    · have : ∀ Y' : Config d m, (Fin.cons y Y' : Config d (m + 1)) ∈ {X : Config d (m + 1) | X 0 ∈ A} := by
        intro Y'; simpa using hy
      have h1 : ∀ Y' : Config d m, Set.indicator {X : Config d (m + 1) | X 0 ∈ A} e (Fin.cons y Y') =
          e (Fin.cons y Y') := fun Y' => Set.indicator_of_mem (this Y') _
      simp only [h1, Set.indicator_of_mem hy]
    · have : ∀ Y' : Config d m, (Fin.cons y Y' : Config d (m + 1)) ∉ {X : Config d (m + 1) | X 0 ∈ A} := by
        intro Y'; simpa using hy
      have h1 : ∀ Y' : Config d m, Set.indicator {X : Config d (m + 1) | X 0 ∈ A} e (Fin.cons y Y') =
          0 := fun Y' => Set.indicator_of_notMem (this Y') _
      simp only [h1, Set.indicator_of_notMem hy, lintegral_zero]
  rw [hLHS]
  have hKm : ∀ y, ∫⁻ Y', e (Fin.cons y Y') ∂νm =
      ENNReal.ofReal (Real.exp (a y)) *
        ∫⁻ Y', ENNReal.ofReal (Real.exp (-k y Y')) * ENNReal.ofReal (Real.exp (Wm Y')) ∂νm := by
    intro y
    have hmeas : Measurable fun Y' : Config d m =>
        ENNReal.ofReal (Real.exp (-k y Y')) * ENNReal.ofReal (Real.exp (Wm Y')) :=
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (hk.comp measurable_prodMk_left).neg)).mul hWmE
    rw [← lintegral_const_mul (f := fun Y' => ENNReal.ofReal (Real.exp (-k y Y')) *
      ENNReal.ofReal (Real.exp (Wm Y'))) _ hmeas]
    refine lintegral_congr fun Y' => ?_
    have h1 : ENNReal.ofReal (Real.exp (a y - k y Y')) =
        ENNReal.ofReal (Real.exp (a y)) * ENNReal.ofReal (Real.exp (-k y Y')) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 2
    rw [F3, h1, mul_assoc]
  rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hZ.1)]
  refine lintegral_congr fun y => ?_
  rw [hKm y]
  have hJy : (∫⁻ X, ENNReal.ofReal (Real.exp (-k y (Fin.tail X))) /
      (∫⁻ y', ENNReal.ofReal (Real.exp (a y' - k y' (Fin.tail X))) ∂μ) ∂(tiltMeasure ν Wf)) =
      Z⁻¹ * ∫⁻ Y', ENNReal.ofReal (Real.exp (-k y Y')) * ENNReal.ofReal (Real.exp (Wm Y')) ∂νm := hJ y
  rw [hJy]
  ring


/-! ### The pole law as a single tilt of the product law -/

theorem tilt_tilt {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (w v : α → ℝ) (hw : Measurable w) (hv : Measurable v) (W : ℝ) (hW : ∀ a, w a ≤ W) :
    tiltMeasure (tiltMeasure ν w) v = tiltMeasure ν (fun a => w a + v a) := by
  haveI := tilt_isProb ν w hw W hW
  have hwv : Measurable fun a => w a + v a := hw.add hv
  rw [Glue.tiltMeasure_eq_tilted_of_measurable (tiltMeasure ν w) v hv,
    Glue.tiltMeasure_eq_tilted_of_measurable ν w hw, Glue.tiltMeasure_eq_tilted_of_measurable ν _ hwv]
  have hint : Integrable (fun a => Real.exp (w a)) ν :=
    Integrable.of_bound (C := Real.exp W) (Real.measurable_exp.comp hw).aestronglyMeasurable
      (Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 (hW a))
  exact tilted_tilted hint v

theorem conv_gPlus (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ y, 0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y ∧
      convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Cg := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨B, Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  have hCc := hK.Cc_nonneg
  refine ⟨Cc + |c|, by positivity, fun y => ⟨?_, ?_⟩⟩
  · exact integral_nonneg fun z => hc _
  · have hconv : convMeasure (gPlus d s c) (withDensityReal ρ) y =
        convMeasure (periodicRiesz d s) (withDensityReal ρ) y + c := by
      unfold convMeasure gPlus
      rw [integral_add (hK.int y) (integrable_const _)]
      simp
    rw [hconv]
    have := (abs_le.1 (hK.conv y)).2
    linarith [le_abs_self c]

theorem measurable_pairSum' {G : Torus d → ℝ} (hG : Measurable G) {n : ℕ} :
    Measurable fun Y : Config d n => pairSum G Y := measurable_pairSum hG

theorem pairSum_nonneg {G : Torus d → ℝ} (hG : ∀ z, 0 ≤ G z) {n : ℕ} (Y : Config d n) :
    0 ≤ pairSum G Y :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hG _

/-- The exponent of the pole law (kernel `g_+`) as a function on `Config d n`. -/
def poleExp (G : Torus d → ℝ) (μ : Measure (Torus d)) (n : ℕ) (lam β t : ℝ) (x : Torus d)
    (Y : Config d n) : ℝ :=
  (-lam * pairSum G Y + β * ∑ i, convMeasure G μ (Y i)) + (-(t * lam) * ∑ i, G (x - Y i))

theorem measurable_poleExp {G : Torus d → ℝ} (hG : Measurable G) (μ : Measure (Torus d)) [SFinite μ]
    (n : ℕ) (lam β t : ℝ) (x : Torus d) : Measurable (poleExp G μ n lam β t x) := by
  unfold poleExp
  exact (measurable_cavityW hG μ n lam β).add
    ((Finset.measurable_sum _ fun i _ => hG.comp (measurable_const.sub (measurable_pi_apply i))).const_mul _)

theorem poleExp_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (β : ℝ) (hβ : 0 < β)
    {lam t : ℝ} (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    ∃ Wb : ℝ, ∀ (n : ℕ) (x : Torus d) (Y : Config d n),
      poleExp (gPlus d s c) (withDensityReal ρ) n lam β t x Y ≤ Wb * n := by
  obtain ⟨Cg, hCg0, hCg⟩ := conv_gPlus hd hs0 hsd hρ hc
  refine ⟨β * Cg, fun n x Y => ?_⟩
  unfold poleExp
  have h1 : 0 ≤ pairSum (gPlus d s c) Y := pairSum_nonneg (fun z => hc z) Y
  have h2 : 0 ≤ ∑ i, gPlus d s c (x - Y i) := Finset.sum_nonneg fun i _ => hc _
  have h3 : ∑ i, convMeasure (gPlus d s c) (withDensityReal ρ) (Y i) ≤ n * Cg := by
    calc _ ≤ ∑ _i : Fin n, Cg := Finset.sum_le_sum fun i _ => (hCg _).2
      _ = n * Cg := by simp
  have h4 : 0 ≤ t * lam := mul_nonneg ht hlam
  nlinarith [mul_nonneg hlam h1, mul_nonneg h4 h2]

theorem critPole_single (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    {N : ℕ} (hN : 2 ≤ N) (x : Torus d) {t : ℝ} (ht : 0 ≤ t) :
    critPole d s c β ρ N x t =
      tiltMeasure (Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ)
        (poleExp (gPlus d s c) (withDensityReal ρ) (N - 1) (β / N) β t x) := by
  have hμ := isProbabilityMeasure_mu hρ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hG := measurable_gPlus hd hs0 hsd c
  obtain ⟨Cg, hCg0, hCg⟩ := conv_gPlus hd hs0 hsd hρ hc
  unfold critPole poleLaw cavityLaw
  refine tilt_tilt _ _ _ (measurable_cavityW hG _ _ _ _)
    ((Finset.measurable_sum _ fun i _ => hG.comp (measurable_const.sub (measurable_pi_apply i))).const_mul _)
    (β * (Cg * ((N - 1 : ℕ) : ℝ))) (fun Y => ?_) |>.trans ?_
  · have h1 : 0 ≤ pairSum (gPlus d s c) Y := pairSum_nonneg (fun z => hc z) Y
    have h3 : ∑ i, convMeasure (gPlus d s c) (withDensityReal ρ) (Y i) ≤ ((N - 1 : ℕ) : ℝ) * Cg := by
      calc _ ≤ ∑ _i : Fin (N - 1), Cg := Finset.sum_le_sum fun i _ => (hCg _).2
        _ = _ := by simp
    show -(β / N) * pairSum (gPlus d s c) Y +
        β * ∑ i, convMeasure (gPlus d s c) (withDensityReal ρ) (Y i) ≤ β * (Cg * ((N - 1 : ℕ) : ℝ))
    nlinarith [mul_nonneg hlam h1]
  · rfl

/-! ### Splitting off the first particle in the pole exponent -/

theorem poleExp_cons (G : Torus d → ℝ) (μ : Measure (Torus d)) {m : ℕ} (lam β t : ℝ) (x y : Torus d)
    (Y' : Config d m) :
    poleExp G μ (m + 1) lam β t x (Fin.cons y Y' : Config d (m + 1)) =
      (-(t * lam) * G (x - y)) + poleExp G μ m lam β t x Y' -
        (lam * ∑ j, G (y - Y' j) - β * convMeasure G μ y) := by
  unfold poleExp
  have h := cavityW_cons G μ lam β y Y'
  rw [h, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

theorem lintegral_exp_ne_zero {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Measurable f) : ∫⁻ a, ENNReal.ofReal (Real.exp (f a)) ∂μ ≠ 0 := by
  intro h0
  have hm : Measurable fun a => ENNReal.ofReal (Real.exp (f a)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hf)
  rw [lintegral_eq_zero_iff hm] at h0
  have h1 : ∀ᵐ a ∂μ, False := h0.mono fun a ha => by
    have := (ENNReal.ofReal_eq_zero.1 ha)
    exact absurd this (not_le.2 (Real.exp_pos _))
  obtain ⟨a, ha⟩ := h1.exists
  exact ha

theorem lintegral_exp_ne_top {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} {W : ℝ} (hW : ∀ a, f a ≤ W) : ∫⁻ a, ENNReal.ofReal (Real.exp (f a)) ∂μ ≠ ∞ := by
  apply ne_of_lt
  calc ∫⁻ a, ENNReal.ofReal (Real.exp (f a)) ∂μ ≤ ∫⁻ _a, ENNReal.ofReal (Real.exp W) ∂μ :=
        lintegral_mono fun a => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hW a))
    _ = ENNReal.ofReal (Real.exp W) := by simp
    _ < ∞ := ENNReal.ofReal_lt_top

theorem sum_erase_zero {m : ℕ} (f : Fin (m + 1) → ℝ) :
    ∑ j ∈ Finset.univ.erase (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)), f j = ∑ j : Fin m, f j.succ := by
  have h := Finset.add_sum_erase (Finset.univ : Finset (Fin (m + 1))) f
    (Finset.mem_univ (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)))
  rw [Fin.sum_univ_succ] at h
  have : f (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) = f 0 := rfl
  linarith

/-- The first marginal of the pole law (`R:eq:conditional-density`, source line 4279): the density
with respect to `μ` is `e^{-tλ g_+(x-y)}` times the conditional average of `e^{-v_Y(y)}/Z_Y`. -/
theorem critPole_formula (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (m : ℕ) (x : Torus d) {t : ℝ} (ht : 0 ≤ t) :
    firstMarginal (critPole d s c β ρ (m + 2) x t) ≪ withDensityReal ρ ∧
    ∀ᵐ y ∂(withDensityReal ρ),
      ((firstMarginal (critPole d s c β ρ (m + 2) x t)).rnDeriv (withDensityReal ρ) y).toReal =
        Real.exp (-(t * (β / ((m + 2 : ℕ) : ℝ))) * gPlus d s c (x - y)) *
          ∫ X, Real.exp (-(cavityField d s c β ρ (m + 2) (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) X y)) /
            (∫ y', Real.exp (-(t * (β / ((m + 2 : ℕ) : ℝ))) * gPlus d s c (x - y') -
              cavityField d s c β ρ (m + 2) (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) X y')
              ∂(withDensityReal ρ)) ∂(critPole d s c β ρ (m + 2) x t) := by
  have hμ := isProbabilityMeasure_mu hρ
  set μ := withDensityReal ρ with hμdef
  set G := gPlus d s c with hGdef
  set lam : ℝ := β / ((m + 2 : ℕ) : ℝ) with hlamdef
  have hN0 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hlam : 0 ≤ lam := by positivity
  have hGm : Measurable G := measurable_gPlus hd hs0 hsd c
  have hG0 : ∀ z, 0 ≤ G z := fun z => hc z
  obtain ⟨Cg, hCg0, hCg⟩ := conv_gPlus hd hs0 hsd hρ hc
  obtain ⟨Wc, hWc⟩ := poleExp_le hd hs0 hsd hρ hc β hβ hlam ht
  have hP : critPole d s c β ρ (m + 2) x t =
      tiltMeasure (Measure.pi fun _ : Fin (m + 1) => μ) (poleExp G μ (m + 1) lam β t x) :=
    critPole_single hd hs0 hsd β hβ hρ hc (N := m + 2) (by omega) x ht
  obtain ⟨a, ha⟩ : ∃ a : Torus d → ℝ, ∀ y, a y = -(t * lam) * G (x - y) := ⟨_, fun _ => rfl⟩
  obtain ⟨Wm, hWm⟩ : ∃ Wm : Config d m → ℝ, Wm = poleExp G μ m lam β t x := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : Torus d → Config d m → ℝ,
      ∀ y Y', k y Y' = lam * ∑ j, G (y - Y' j) - β * convMeasure G μ y := ⟨_, fun _ _ => rfl⟩
  have ham : Measurable a := by
    have : a = fun y => -(t * lam) * G (x - y) := funext ha
    rw [this]; exact (hGm.comp (measurable_const.sub measurable_id)).const_mul _
  have hWmm : Measurable Wm := by rw [hWm]; exact measurable_poleExp hGm μ m lam β t x
  have hk : Measurable fun q : Torus d × Config d m => k q.1 q.2 := by
    have : (fun q : Torus d × Config d m => k q.1 q.2) =
        fun q => lam * ∑ j, G (q.1 - q.2 j) - β * convMeasure G μ q.1 := funext fun q => hkdef _ _
    rw [this]
    exact ((Finset.measurable_sum _ fun j _ => hGm.comp (measurable_fst.sub
      ((measurable_pi_apply j).comp measurable_snd))).const_mul lam).sub
      (((measurable_convMeasure hGm μ).comp measurable_fst).const_mul β)
  have hid : ∀ X : Config d (m + 1), poleExp G μ (m + 1) lam β t x X =
      a (X 0) + Wm (Fin.tail X) - k (X 0) (Fin.tail X) := by
    intro X
    have := poleExp_cons G μ lam β t x (X 0) (Fin.tail X)
    rw [Fin.cons_self_tail] at this
    rw [this, ha, hWm, hkdef]
  have hfun : (fun X : Config d (m + 1) => a (X 0) + Wm (Fin.tail X) - k (X 0) (Fin.tail X)) =
      poleExp G μ (m + 1) lam β t x := (funext hid).symm
  have hWb : ∀ X : Config d (m + 1), a (X 0) + Wm (Fin.tail X) - k (X 0) (Fin.tail X) ≤
      Wc * ((m + 1 : ℕ) : ℝ) := fun X => by rw [← hid]; exact hWc (m + 1) x X
  -- the normaliser in the cavity variable
  have hint_le : ∀ (Y' : Config d m) (y : Torus d), a y - k y Y' ≤ β * Cg := by
    intro Y' y
    have h1 : 0 ≤ t * lam := mul_nonneg ht hlam
    have h2 : 0 ≤ G (x - y) := hG0 _
    have h3 : 0 ≤ ∑ j, G (y - Y' j) := Finset.sum_nonneg fun j _ => hG0 _
    have h4 := (hCg y).2
    have e1 : 0 ≤ (t * lam) * G (x - y) := mul_nonneg h1 h2
    have e2 : 0 ≤ lam * ∑ j, G (y - Y' j) := mul_nonneg hlam h3
    have e3 : β * convMeasure G μ y ≤ β * Cg := mul_le_mul_of_nonneg_left h4 hβ.le
    rw [ha, hkdef]
    linarith
  have hfm : ∀ Y' : Config d m, Measurable fun y => a y - k y Y' := by
    intro Y'
    have h1 : Measurable fun y : Torus d => (y, Y') := measurable_id.prodMk measurable_const
    exact ham.sub (hk.comp h1)
  have hZ0 : ∀ Y' : Config d m, ∫⁻ y, ENNReal.ofReal (Real.exp (a y - k y Y')) ∂μ ≠ 0 :=
    fun Y' => lintegral_exp_ne_zero μ (hfm Y')
  have hZt : ∀ Y' : Config d m, ∫⁻ y, ENNReal.ofReal (Real.exp (a y - k y Y')) ∂μ ≠ ∞ :=
    fun Y' => lintegral_exp_ne_top μ (hint_le Y')
  -- the law `P` and the density
  obtain ⟨P, hPdef⟩ : ∃ P : Measure (Config d (m + 1)),
      P = tiltMeasure (Measure.pi fun _ : Fin (m + 1) => μ) (poleExp G μ (m + 1) lam β t x) := ⟨_, rfl⟩
  haveI hPprob : IsProbabilityMeasure P := by
    rw [hPdef]
    exact tilt_isProb _ _ (measurable_poleExp hGm μ (m + 1) lam β t x) (Wc * ((m + 1 : ℕ) : ℝ))
      (hWc (m + 1) x)
  have hdis : ∀ {A : Set (Torus d)}, MeasurableSet A →
      P {X | X 0 ∈ A} = ∫⁻ y in A, ENNReal.ofReal (Real.exp (a y)) *
        ∫⁻ X, ENNReal.ofReal (Real.exp (-k y (Fin.tail X))) /
          (∫⁻ y', ENNReal.ofReal (Real.exp (a y' - k y' (Fin.tail X))) ∂μ) ∂P ∂μ := by
    intro A hA
    have := firstCoord_disint (μ := μ) a Wm k ham hWmm hk _ hWb hZ0 hZt hA
    rw [hfun] at this
    rw [hPdef]
    exact this
  obtain ⟨J, hJdef⟩ : ∃ J : Torus d → ℝ≥0∞, ∀ y, J y = ∫⁻ X, ENNReal.ofReal (Real.exp (-k y (Fin.tail X))) /
      (∫⁻ y', ENNReal.ofReal (Real.exp (a y' - k y' (Fin.tail X))) ∂μ) ∂P := ⟨_, fun _ => rfl⟩
  have hT : Measurable fun X : Config d (m + 1) => Fin.tail X :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  have hE1m : Measurable fun q : Torus d × Config d m => ENNReal.ofReal (Real.exp (a q.1 - k q.1 q.2)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((ham.comp measurable_fst).sub hk))
  have hZtm : Measurable fun Y' : Config d m => ∫⁻ y, ENNReal.ofReal (Real.exp (a y - k y Y')) ∂μ :=
    Measurable.lintegral_prod_left' hE1m
  have hJm : Measurable J := by
    have : J = fun y => ∫⁻ X, ENNReal.ofReal (Real.exp (-k y (Fin.tail X))) /
        (∫⁻ y', ENNReal.ofReal (Real.exp (a y' - k y' (Fin.tail X))) ∂μ) ∂P := funext hJdef
    rw [this]
    refine Measurable.lintegral_prod_right' (f := fun q : Torus d × Config d (m + 1) =>
      ENNReal.ofReal (Real.exp (-k q.1 (Fin.tail q.2))) /
        (∫⁻ y', ENNReal.ofReal (Real.exp (a y' - k y' (Fin.tail q.2))) ∂μ)) ?_
    simp only [div_eq_mul_inv]
    exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((hk.comp (measurable_fst.prodMk (hT.comp measurable_snd))).neg))).mul
      ((hZtm.comp (hT.comp measurable_snd)).inv)
  have hdensm : Measurable fun y => ENNReal.ofReal (Real.exp (a y)) * J y :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ham)).mul hJm
  have hfirst : firstMarginal P = μ.withDensity fun y => ENNReal.ofReal (Real.exp (a y)) * J y := by
    ext A hA
    rw [withDensity_apply _ hA]
    simp only [hJdef]
    rw [← hdis hA]
    unfold firstMarginal
    rw [dif_pos (Nat.succ_pos m), Measure.map_apply (measurable_pi_apply (⟨0, Nat.succ_pos m⟩ : Fin (m + 1))) hA]
    rfl
  have hPc : critPole d s c β ρ (m + 2) x t = P := hP.trans hPdef.symm
  have hac : firstMarginal P ≪ μ := by rw [hfirst]; exact withDensity_absolutelyContinuous _ _
  have hint_int : ∀ Y' : Config d m, Integrable (fun y => Real.exp (a y - k y Y')) μ := fun Y' =>
    Integrable.of_bound (C := Real.exp (β * Cg)) (Real.measurable_exp.comp (hfm Y')).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 (hint_le Y' y))
  have hZr : ∀ Y' : Config d m, ∫⁻ y, ENNReal.ofReal (Real.exp (a y - k y Y')) ∂μ =
      ENNReal.ofReal (∫ y, Real.exp (a y - k y Y') ∂μ) := fun Y' =>
    (ofReal_integral_eq_lintegral_ofReal (hint_int Y')
      (Eventually.of_forall fun y => (Real.exp_pos _).le)).symm
  have hZrpos : ∀ Y' : Config d m, 0 < ∫ y, Real.exp (a y - k y Y') ∂μ := fun Y' =>
    integral_exp_pos (hint_int Y')
  have hZrm : Measurable fun Y' : Config d m => ∫ y, Real.exp (a y - k y Y') ∂μ := by
    have : (fun Y' : Config d m => ∫ y, Real.exp (a y - k y Y') ∂μ) =
        fun Y' => (∫⁻ y, ENNReal.ofReal (Real.exp (a y - k y Y')) ∂μ).toReal := by
      funext Y'; rw [hZr, ENNReal.toReal_ofReal (hZrpos Y').le]
    rw [this]; exact hZtm.ennreal_toReal
  have hkeq : ∀ (X : Config d (m + 1)) (y : Torus d), k y (Fin.tail X) =
      cavityField d s c β ρ (m + 2) (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) X y := by
    intro X y
    rw [hkdef]
    unfold cavityField
    rw [sum_erase_zero (fun j => gPlus d s c (y - X j))]
    rfl
  refine ⟨by rw [hPc]; exact hac, ?_⟩
  rw [hPc]
  have hrn := Measure.rnDeriv_withDensity μ hdensm
  rw [← hfirst] at hrn
  filter_upwards [hrn] with y hy
  rw [hy, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, ha]
  congr 1
  -- `(J y).toReal`
  have hψm : Measurable fun X : Config d (m + 1) =>
      Real.exp (-k y (Fin.tail X)) / ∫ y', Real.exp (a y' - k y' (Fin.tail X)) ∂μ := by
    have h1 : Measurable fun X : Config d (m + 1) => k y (Fin.tail X) :=
      (hk.comp (measurable_const.prodMk hT))
    exact (Real.measurable_exp.comp h1.neg).div (hZrm.comp hT)
  have hψ0 : ∀ X : Config d (m + 1),
      0 ≤ Real.exp (-k y (Fin.tail X)) / ∫ y', Real.exp (a y' - k y' (Fin.tail X)) ∂μ :=
    fun X => div_nonneg (Real.exp_pos _).le (hZrpos _).le
  have hJy : J y = ∫⁻ X, ENNReal.ofReal (Real.exp (-k y (Fin.tail X)) /
      ∫ y', Real.exp (a y' - k y' (Fin.tail X)) ∂μ) ∂P := by
    rw [hJdef]
    refine lintegral_congr fun X => ?_
    rw [hZr, ENNReal.ofReal_div_of_pos (hZrpos _)]
  rw [hJy]
  refine (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hψ0) hψm.aestronglyMeasurable).symm.trans ?_
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only [hkeq, ha]

section Small

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ hc

theorem gplus_abs_conv_small (M : ℝ) :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ h : Torus d → ℝ, Measurable h → (∀ y, |h y| ≤ M) →
      ∀ e : ℝ, 0 ≤ e → e ≤ 1 → ∫ y, |h y| ∂(withDensityReal ρ) ≤ e → ∀ x : Torus d,
        ∫ y, gPlus d s c (x - y) * |h y| ∂(withDensityReal ρ) ≤ CM * Real.sqrt e := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Cc, -, -, -, h4, -, -⟩ := critical_integrals hd hcrit β hβ ρ hρ c hc
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_density_bound hρ
  have hρm : Measurable ρ := hρ.density.measurable
  have hgpm := measurable_gPlus hd hs0 hsd c
  obtain ⟨CM, hCM⟩ := h4 (Λ * M)
  refine ⟨|CM|, abs_nonneg _, fun h hm hb e he0 he1 hl x => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hb (Classical.arbitrary _))
  set w : Torus d → ℝ := fun y => ρ y * |h y| with hw
  have hwm : Measurable w := hρm.mul hm.abs
  have hwb : ∀ y, |w y| ≤ Λ * M := by
    intro y
    have h2 : |ρ y| ≤ Λ := by rw [abs_of_pos (hρ.pos y)]; exact hΛ y
    rw [hw]; simp only [abs_mul, abs_abs]
    exact mul_le_mul h2 (hb y) (abs_nonneg _) hΛ0.le
  have hhi : Integrable (fun y => |h y|) (withDensityReal ρ) :=
    Integrable.of_bound (C := M) hm.abs.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_abs]; exact hb y)
  have hl1 : ∫⁻ y, ‖w y‖ₑ ≤ ENNReal.ofReal e := by
    have e1 : ∀ y, ‖w y‖ₑ = ENNReal.ofReal (ρ y) * ENNReal.ofReal |h y| := by
      intro y
      simp only [hw, enorm_mul, Real.enorm_of_nonneg (hρ.density.nonneg y), Real.enorm_eq_ofReal_abs,
        abs_abs]
    simp_rw [e1]
    have hmρ : Measurable fun y => ENNReal.ofReal (ρ y) := ENNReal.measurable_ofReal.comp hρm
    have e2 : ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal |h y| =
        ∫⁻ y, ENNReal.ofReal |h y| ∂(withDensityReal ρ) := by
      show _ = ∫⁻ y, ENNReal.ofReal |h y| ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x))
      rw [lintegral_withDensity_eq_lintegral_mul _ hmρ
        (show Measurable fun y => ENNReal.ofReal |h y| from ENNReal.measurable_ofReal.comp hm.abs)]
      rfl
    rw [e2, ← ofReal_integral_eq_lintegral_ofReal hhi (Eventually.of_forall fun y => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hl
  have h1 := hCM w e hwm hwb he1 hl1 x
  have hmeasF : Measurable fun y => gPlus d s c (x - y) * |h y| :=
    (hgpm.comp (measurable_const.sub measurable_id)).mul hm.abs
  have hF0 : ∀ y, 0 ≤ gPlus d s c (x - y) * |h y| := fun y => mul_nonneg (hc _) (abs_nonneg _)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hF0) hmeasF.aestronglyMeasurable]
  have h2 : ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) * |h y|) ∂(withDensityReal ρ) =
      ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) * ‖w y‖ₑ := by
    show _ = _
    have hmρ : Measurable fun y => ENNReal.ofReal (ρ y) := ENNReal.measurable_ofReal.comp hρm
    unfold withDensityReal
    rw [lintegral_withDensity_eq_lintegral_mul _ hmρ
      (show Measurable fun y => ENNReal.ofReal (gPlus d s c (x - y) * |h y|) from
        ENNReal.measurable_ofReal.comp hmeasF)]
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply, hw, enorm_mul, Real.enorm_of_nonneg (hρ.density.nonneg y),
      Real.enorm_eq_ofReal_abs, abs_abs]
    have hg0 : 0 ≤ gPlus d s c (x - y) := hc _
    rw [ENNReal.ofReal_mul hg0]
    ring
  rw [h2]
  have h3 : (∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) * ‖w y‖ₑ).toReal ≤ |CM| * Real.sqrt e :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (h1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))))
  exact h3

end Small

theorem dens_facts {μ ν : Measure (Torus d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : ν ≪ μ) :
    Integrable (fun y => (ν.rnDeriv μ y).toReal) μ ∧ ∫ y, (ν.rnDeriv μ y).toReal ∂μ = 1 ∧
      ν = μ.withDensity (fun y => ENNReal.ofReal ((ν.rnDeriv μ y).toReal)) := by
  refine ⟨Measure.integrable_toReal_rnDeriv, ?_, ?_⟩
  · have h := integral_rnDeriv_smul hac (f := fun _ : Torus d => (1 : ℝ))
    simp only [smul_eq_mul, mul_one, integral_const, probReal_univ, one_smul] at h
    exact h
  · conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hac]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top ν μ] with x hx
    rw [ENNReal.ofReal_toReal hx.ne]

section L1q

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ)

include hd hcrit hβ hρ

theorem l1_q0_rate :
    ∃ Ce : ℝ, 0 ≤ Ce ∧ ∀ n : ℕ, 0 < n → ∀ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) →
      ∫ y, |1 - qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y| ∂(withDensityReal ρ) ≤
        Ce * deltaN d s (n + 1) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Mp, hMp1, hMp⟩ := pDens_bounds hd hs0 hsd hβ hρ
  obtain ⟨Mq, hMq0, hMq⟩ := qDens_bound hd hs0 hsd hβ hρ
  obtain ⟨C2, hC20, hC2⟩ := L2_all hd hs0 hsd hβ hρ
  obtain ⟨CL, hCL0, hCL⟩ := cavity_L2 hd hs0 hsd hβ hρ
  refine ⟨C2 + CL, by positivity, fun n hn lam hlamdef => ?_⟩
  obtain ⟨hlam, hln, hlam1⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlam' : lam = β / ((n + 1 : ℕ) : ℝ) := hlamdef
  have hδ0 : 0 ≤ deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hδinv : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ deltaN d s (n + 1) := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
  have hsδ : Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤ deltaN d s (n + 1) := by
    rw [Real.sqrt_le_left hδ0]
    have : deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ) ≤ deltaN d s (n + 1) ^ 2 := by
      rw [div_eq_mul_inv, sq]
      exact mul_le_mul_of_nonneg_left hδinv hδ0
    exact this
  have hacq := hMq (n + 1) hN
  have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ := by
    subst hlam'; exact hacq.1
  have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := by
    subst hlam'; exact hacq.2
  have hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp := by
    subst hlam'; exact fun y => (hMp (n + 1) hN y).2
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hp0 : ∀ y, 0 < pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y :=
    pDens_pos hd hs0 hsd hρ hlam hln
  set p := pDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hp
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set μ := withDensityReal ρ with hμdef
  have hq0 : ∀ y, 0 ≤ q y := fun y => ENNReal.toReal_nonneg
  set qb : Torus d → ℝ := fun y => min (q y) Mq with hqbdef
  have hqbm : Measurable qb := hqm.min measurable_const
  have hqbq : q =ᵐ[μ] qb := hqb.mono fun y hy => by simp only [hqbdef, min_eq_left hy]
  have hqb0 : ∀ y, 0 ≤ qb y := fun y => le_min (hq0 y) hMq0.le
  have hqbM : ∀ y, qb y ≤ Mq := fun y => min_le_right _ _
  have hp2 : Real.sqrt (∫ y, (p y - 1) ^ 2 ∂μ) ≤ C2 * deltaN d s (n + 1) :=
    Real.sqrt_le_iff.2 ⟨by positivity, hC2 n hn lam hlamdef⟩
  have hpq2 : Real.sqrt (∫ y, (p y - q y) ^ 2 ∂μ) ≤ CL * deltaN d s (n + 1) :=
    (hCL n hn lam hlamdef).trans (mul_le_mul_of_nonneg_left hsδ hCL0)
  have hpb' : ∀ y, |p y - 1| ≤ Mp + 1 := fun y => by
    rw [abs_le]; constructor <;> linarith [hp0 y, hpb y]
  have hpqb : ∀ y, |p y - qb y| ≤ Mp + Mq := fun y => by
    rw [abs_le]; constructor <;> linarith [hp0 y, hpb y, hqb0 y, hqbM y]
  have hl1a : ∫ y, |p y - 1| ∂μ ≤ C2 * deltaN d s (n + 1) :=
    (l1_le_sqrt (h := fun y => p y - 1) (hpm.sub measurable_const) hpb').trans hp2
  have hl1b : ∫ y, |p y - qb y| ∂μ ≤ CL * deltaN d s (n + 1) := by
    have e : ∫ y, (p y - qb y) ^ 2 ∂μ = ∫ y, (p y - q y) ^ 2 ∂μ :=
      integral_congr_ae (hqbq.mono fun y hy => by simp only [← hy])
    refine (l1_le_sqrt (h := fun y => p y - qb y) (hpm.sub hqbm) hpqb).trans ?_
    rw [e]; exact hpq2
  have hpi : Integrable p μ := Integrable.of_bound (C := Mp) hpm.aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (hp0 y)]; exact hpb y)
  have hqbi : Integrable qb μ := Integrable.of_bound (C := Mq) hqbm.aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hqb0 y)]; exact hqbM y)
  have h1 : Integrable (fun y => |p y - 1|) μ := (hpi.sub (integrable_const _)).abs
  have h2 : Integrable (fun y => |p y - qb y|) μ := (hpi.sub hqbi).abs
  have h3 : Integrable (fun y => |1 - qb y|) μ := ((integrable_const (1 : ℝ)).sub hqbi).abs
  have hle : ∫ y, |1 - qb y| ∂μ ≤ ∫ y, (|p y - 1| + |p y - qb y|) ∂μ := by
    refine integral_mono h3 (h1.add h2) fun y => ?_
    have := abs_add_le (1 - p y) (p y - qb y)
    rw [show (1 - p y) + (p y - qb y) = 1 - qb y by ring, abs_sub_comm 1 (p y)] at this
    exact this
  rw [integral_add h1 h2] at hle
  have e : ∫ y, |1 - q y| ∂μ = ∫ y, |1 - qb y| ∂μ :=
    integral_congr_ae (hqbq.mono fun y hy => by simp only [← hy])
  rw [e]
  nlinarith

end L1q

section PoleMarg

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ)

include hd hs0 hsd hβ hρ

/-- Every one-coordinate marginal of every pole law has density bounded by `M₁` with respect to `μ`. -/
theorem pole_marg_le :
    ∃ M1 : ℝ, 0 < M1 ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≪
          withDensityReal ρ ∧
        ∀ j : Fin (N - 1),
          (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
              (fun Y : Config d (N - 1) => Y j) ≤ ENNReal.ofReal M1 • withDensityReal ρ := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨C1, hC1, h1⟩ := PoleCavityAux.pole_density_clauses hd hs0 hsd β hβ ρ hρ
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  refine ⟨C1 * Real.exp (β * max B 0), by positivity, fun N hN x t ht => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hn1 : 0 < N - 1 := by omega
  obtain ⟨⟨hac, hle⟩, -⟩ := h1 N hN x t ht
  haveI := pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  haveI hνp := isProb_firstMarginal hn1 (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)
  refine ⟨hac, fun j => ?_⟩
  have hexch := MarginalAux.poleLaw_exchangeable hd hs0 hsd β hρ (N - 1) (β / N) hlam x t
  have hfm : firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) =
      (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
        (fun Y : Config d (N - 1) => Y ⟨0, hn1⟩) := by
    unfold firstMarginal; rw [dif_pos hn1]
  rw [hexch.marginal_eq j ⟨0, hn1⟩, ← hfm]
  refine Measure.le_iff'.2 fun A => ?_
  have hlam1 : β / N ≤ β := by
    rw [div_le_iff₀ hN0]
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  have hbd : ∀ᵐ y ∂(withDensityReal ρ),
      (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)).rnDeriv
        (withDensityReal ρ) y ≤ ENNReal.ofReal (C1 * Real.exp (β * max B 0)) := by
    filter_upwards [hle] with y hy
    refine hy.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC1.le))
    have h4 := hB (x - y)
    have h5 : 0 ≤ t * (β / N) := mul_nonneg ht.1 hlam
    have h6 : t * (β / N) ≤ β := by nlinarith [ht.2]
    have h7 : -B ≤ periodicRiesz d s (x - y) := by linarith
    nlinarith [le_max_left B 0]
  have hA : (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) A =
      ∫⁻ y in A, (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)).rnDeriv
        (withDensityReal ρ) y ∂(withDensityReal ρ) := by
    rw [Measure.setLIntegral_rnDeriv hac]
  rw [hA]
  calc _ ≤ ∫⁻ y in A, ENNReal.ofReal (C1 * Real.exp (β * max B 0)) ∂(withDensityReal ρ) :=
        lintegral_mono_ae (ae_restrict_of_ae hbd)
    _ = _ := by simp [Measure.smul_apply]

end PoleMarg


theorem critPole_eq_poleLaw (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {N : ℕ} (hN : 2 ≤ N) (x : Torus d) (t : ℝ) :
    critPole d s c β ρ N x t =
      poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  rw [critPole_eq_tilted hd hs0 hsd c β hβ hρ hN x t, critCavity_eq hd hs0 hsd c β hρ N,
    poleLaw_eq_tilted_cavity hd hs0 hsd β hρ (N - 1) (β / N) hlam x t]
  have : (fun Y : Config d (N - 1) => t * Xp d s c (β / N) x Y) = fun Y =>
      t * Xx (periodicRiesz d s) (β / N) x Y + t * (-((β / N) * ((N - 1 : ℕ) : ℝ) * c)) := by
    funext Y; rw [Xp_eq_Xx hd hs0 hsd c _ x Y]; ring
  rw [this]
  exact Calib.tilted_add_const _ _ _

section L1pole

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ)

include hd hcrit hβ hρ

theorem pole_marginal_l1 :
    ∃ Ce : ℝ, 0 ≤ Ce ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∫ y, |((firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)).rnDeriv
          (withDensityReal ρ) y).toReal - 1| ∂(withDensityReal ρ) ≤ Ce * deltaN d s N := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Ce0, hCe0, hCe⟩ := l1_q0_rate hd hcrit hβ hρ
  obtain ⟨Cd, hCd0, hCd⟩ := pole_dual hd hs0 hsd hβ hρ
  obtain ⟨M1, hM1, hMarg⟩ := pole_marg_le hd hs0 hsd hβ hρ
  obtain ⟨Mq, hMq0, hMq⟩ := qDens_bound hd hs0 hsd hβ hρ
  refine ⟨Ce0 + 2 * Cd, by positivity, fun N hN x t ht => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlamdef
  have hlamdef' : lam = β / ((n + 1 : ℕ) : ℝ) := rfl
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlam : 0 ≤ lam := by positivity
  have hδ0 : 0 ≤ deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hδinv : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ deltaN d s (n + 1) := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
  have hsδ : Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤ deltaN d s (n + 1) := by
    rw [Real.sqrt_le_left hδ0]
    have : deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ) ≤ deltaN d s (n + 1) ^ 2 := by
      rw [div_eq_mul_inv, sq]
      exact mul_le_mul_of_nonneg_left hδinv hδ0
    exact this
  haveI hPt := pole_isProb hd hs0 hsd β hρ n lam hlam x t ht.1
  haveI hP0 := cavity_isProb hd hs0 hsd β hρ n lam hlam
  haveI hνt := isProb_firstMarginal hn (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t)
  haveI hν0 := isProb_firstMarginal hn (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)
  have hact : firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t) ≪
      withDensityReal ρ := (hMarg (n + 1) (by omega) x t ht).1
  have hac0 : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ := (hMq (n + 1) (by omega)).1
  obtain ⟨hqti, hqt1, hqteq⟩ := dens_facts hact
  obtain ⟨hq0i, hq01, hq0eq⟩ := dens_facts hac0
  set μ := withDensityReal ρ with hμdef
  set qt : Torus d → ℝ := fun y => ((firstMarginal (poleLaw (periodicRiesz d s) μ n lam β x t)).rnDeriv μ y).toReal
    with hqt
  set q0 : Torus d → ℝ := fun y => ((firstMarginal (cavityLaw (periodicRiesz d s) μ n lam β)).rnDeriv μ y).toReal
    with hq0
  have hqtm : Measurable qt := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hq0m : Measurable q0 := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hqt0 : ∀ y, 0 ≤ qt y := fun y => ENNReal.toReal_nonneg
  have hq00 : ∀ y, 0 ≤ q0 y := fun y => ENNReal.toReal_nonneg
  -- the total variation bound
  have hTV : ∀ A : Set (Torus d), MeasurableSet A →
      |(∫ y in A, qt y ∂μ) - ∫ y in A, q0 y ∂μ| ≤ Cd * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
    intro A hA
    have e1 : ∫ y in A, qt y ∂μ =
        (firstMarginal (poleLaw (periodicRiesz d s) μ n lam β x t) A).toReal := by
      conv_rhs => rw [hqteq]
      rw [toReal_withDensity_apply (fun y => ENNReal.toReal_nonneg) hqti hA]
    have e2 : ∫ y in A, q0 y ∂μ =
        (firstMarginal (cavityLaw (periodicRiesz d s) μ n lam β) A).toReal := by
      conv_rhs => rw [hq0eq]
      rw [toReal_withDensity_apply (fun y => ENNReal.toReal_nonneg) hq0i hA]
    rw [e1, e2]
    have hf : Measurable (A.indicator fun _ : Torus d => (1 : ℝ)) := measurable_const.indicator hA
    have hfb : ∀ y, |A.indicator (fun _ : Torus d => (1 : ℝ)) y| ≤ 1 := fun y => by
      by_cases h : y ∈ A <;> simp [Set.indicator, h]
    have h1 := hCd (n + 1) (by omega) x t ht _ hf 1 hfb
    have e3 : ∀ m : Measure (Torus d), IsProbabilityMeasure m →
        ∫ y, A.indicator (fun _ : Torus d => (1 : ℝ)) y ∂m = (m A).toReal := by
      intro m _
      rw [integral_indicator_const _ hA]
      simp [Measure.real]
    have e4 := e3 (firstMarginal (poleLaw (periodicRiesz d s) μ n lam β x t)) hνt
    have e5 := e3 (firstMarginal (cavityLaw (periodicRiesz d s) μ n lam β)) hν0
    have h2 : Real.sqrt (∫ y, A.indicator (fun _ : Torus d => (1 : ℝ)) y ^ 2 ∂μ) ≤ 1 := by
      rw [Real.sqrt_le_one]
      have : ∫ y, A.indicator (fun _ : Torus d => (1 : ℝ)) y ^ 2 ∂μ ≤ ∫ _y, (1 : ℝ) ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _) (integrable_const _)
          (Eventually.of_forall fun y => ?_)
        have := hfb y
        nlinarith [abs_nonneg (A.indicator (fun _ : Torus d => (1 : ℝ)) y),
          sq_abs (A.indicator (fun _ : Torus d => (1 : ℝ)) y)]
      simpa using this
    rw [← e4, ← e5]
    have hlamE : β / ((n + 1 : ℕ) : ℝ) = lam := rfl
    refine h1.trans ?_
    have hs0' : 0 ≤ Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hCd0 hs0']
  have hl1 := l1_of_sets (μ := μ) hqtm hq0m hqti hq0i hqt1 hq01 hTV
  -- compare with `1`
  have hq0m' : Measurable fun y => 1 - q0 y := measurable_const.sub hq0m
  have h2 : Integrable (fun y => |qt y - q0 y|) μ := (hqti.sub hq0i).abs
  have h3 : Integrable (fun y => |1 - q0 y|) μ := ((integrable_const (1 : ℝ)).sub hq0i).abs
  have h4 : Integrable (fun y => |qt y - 1|) μ := (hqti.sub (integrable_const _)).abs
  have hle : ∫ y, |qt y - 1| ∂μ ≤ ∫ y, (|qt y - q0 y| + |1 - q0 y|) ∂μ := by
    refine integral_mono h4 (h2.add h3) fun y => ?_
    have := abs_add_le (qt y - q0 y) (q0 y - 1)
    rw [show (qt y - q0 y) + (q0 y - 1) = qt y - 1 by ring, abs_sub_comm (q0 y) 1] at this
    exact this
  rw [integral_add h2 h3] at hle
  have hl0 := hCe n hn lam hlamdef'
  have e6 : ∫ y, |1 - q0 y| ∂μ = ∫ y, |1 - qDens (periodicRiesz d s) μ n lam β y| ∂μ := rfl
  have hCdδ : Cd * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤ Cd * deltaN d s (n + 1) :=
    mul_le_mul_of_nonneg_left hsδ hCd0
  have hl0' : ∫ y, |1 - q0 y| ∂μ ≤ Ce0 * deltaN d s (n + 1) := by
    rw [e6]; exact hl0
  have hl1' : ∫ y, |qt y - q0 y| ∂μ ≤ 2 * (Cd * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ))) := hl1
  have hfin : ∫ y, |qt y - 1| ∂μ ≤ Ce0 * deltaN d s (n + 1) + 2 * (Cd * deltaN d s (n + 1)) := by
    linarith [hle, hl0', hl1', hCdδ]
  calc ∫ y, |qt y - 1| ∂μ ≤ _ := hfin
    _ = (Ce0 + 2 * Cd) * deltaN d s (n + 1) := by ring

end L1pole

end CavResp

end HRS

end
