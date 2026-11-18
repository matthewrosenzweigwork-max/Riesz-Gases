import HRS.Sections.Q40bAux9

/-!
# DYNCMP: Theorem 5.4 `dynamic_comparison`, step (4c): the bracket error with a finite-horizon entropy hypothesis

`dyncmp_Q_L1`, `dyncmp_cov_bound` are `q40b_Q_L1`, `q40b_cov_bound` (`Q40bAux8`: Hoeffding + Donsker-Varadhan, `N:eq:linear-entropy`
for the bracket density `Σ_N`, TeX `P:eq:noneq-trace`) with the entropy hypothesis `H(f^σ|(μ^σ)^{⊗N}) ≤ H` required only
for `σ ∈ [0,T]` (the original asks it for all `σ ≥ 0`); the proofs are unchanged.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section
namespace HRS.Q40b

variable {d N : ℕ}

section Bracket

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {p : ℕ}

theorem dyncmp_Q_L1 {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : Fin p → ℝ}
    {F ft : Fin p → ℝ → Torus d → ℝ} {Ca : Fin p → ℝ} {m : ℝ} (h : Br D ρ t F ft Ca m)
    (hN : 0 < N) {a b : Fin p} {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → Config d N}
    (hXm : ∀ r : ℝ≥0, Measurable (X r)) {H : ℝ} (hH0 : 0 ≤ H)
    {T : ℝ} (hTa : t a ≤ T) (hTb : t b ≤ T)
    (hent : ∀ σ ∈ Set.Icc (0 : ℝ) T, relEntropy (P.map (X σ.toNNReal))
      (Measure.pi fun _ : Fin N => withDensityReal (ρ σ)) ≤ ENNReal.ofReal H)
    {σ : ℝ} (hσ : σ ∈ Set.Icc 0 (min (t a) (t b))) :
    ∫ ω, |covMatrixProcess (qPhi D t F X) σ ω a b - qsb D ρ t F σ a b| ∂P ≤
      2 * D.invβ * ((Ca a * Real.exp (-m * (t a - σ))) * (Ca b * Real.exp (-m * (t b - σ)))) *
        Real.sqrt (2 * (H + Real.log 2) / N) := by
  have hq : 0 ≤ 2 * D.invβ := by linarith [D.hβ]
  have h1 : σ ∈ Set.Icc 0 (t a) := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have h2 : σ ∈ Set.Icc 0 (t b) := ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
  have hρ := h.rhoP σ hσ.1
  haveI : IsProbabilityMeasure (withDensityReal (ρ σ)) := isProb_withDensityReal hρ
  set ν := withDensityReal (ρ σ) with hν
  set g : Torus d → ℝ := fun x => inner ℝ (Torus.grad (F a σ) x) (Torus.grad (F b σ) x) with hgdef
  have hgc : Continuous g := (Duality.grad_continuous ((h.hF a).c2 σ h1)).inner
    (Duality.grad_continuous ((h.hF b).c2 σ h2))
  set B : ℝ := (Ca a * Real.exp (-m * (t a - σ))) * (Ca b * Real.exp (-m * (t b - σ))) with hB
  have hgB : ∀ x, |g x| ≤ B := fun x => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (h.grad a σ h1 x) (h.grad b σ h2 x) (norm_nonneg _)
      (mul_nonneg (h.hC0 a) (Real.exp_pos _).le)
  have hpt : ∀ ω, covMatrixProcess (qPhi D t F X) σ ω a b - qsb D ρ t F σ a b =
      2 * D.invβ * q40bY ν g (X σ.toNNReal ω) := by
    intro ω
    rw [q40b_sigma_formula hN, if_pos hσ]
    unfold qsb q40bY
    rw [Matrix.of_apply, if_pos hσ]
    have hint : ∫ y, g y ∂ν = ∫ x, inner ℝ (Torus.grad (F a σ) x) (Torus.grad (F b σ) x) * ρ σ x := by
      rw [hν, PDE.MFPairing.integral_withDensityReal hρ.measurable hρ.nonneg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hgdef]; ring
    rw [hint]
    ring
  have hmeas : Measurable (fun x : Config d N => |q40bY ν g x|) :=
    (q40b_measurable_Y ν hgc.measurable).abs
  have hKL : InformationTheory.klDiv (P.map (X σ.toNNReal))
      (Measure.pi fun _ : Fin N => ν) ≤ ENNReal.ofReal H := hent σ ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans hTa)⟩
  have hdv := q40b_dv_sqrt ν (P.map (X σ.toNNReal)) hgc.measurable hgB hN hH0 hKL
  have hcv : ∫ ω, |q40bY ν g (X σ.toNNReal ω)| ∂P = ∫ x, |q40bY ν g x| ∂(P.map (X σ.toNNReal)) :=
    (integral_map (hXm _).aemeasurable hmeas.aestronglyMeasurable).symm
  have hpt2 : ∀ ω, |covMatrixProcess (qPhi D t F X) σ ω a b - qsb D ρ t F σ a b| =
      2 * D.invβ * |q40bY ν g (X σ.toNNReal ω)| := fun ω => by
    rw [hpt ω, abs_mul, abs_of_nonneg hq]
  simp_rw [hpt2]
  rw [integral_const_mul, hcv]
  have := mul_le_mul_of_nonneg_left hdv hq
  calc 2 * D.invβ * ∫ x, |q40bY ν g x| ∂(P.map (X σ.toNNReal))
      ≤ 2 * D.invβ * (B * Real.sqrt (2 * (H + Real.log 2) / N)) := this
    _ = _ := by rw [hB]; ring



theorem dyncmp_cov_bound {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : Fin p → ℝ}
    {F ft : Fin p → ℝ → Torus d → ℝ} {Ca : Fin p → ℝ} {m : ℝ} (h : Br D ρ t F ft Ca m)
    (hN : 0 < N) {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → Config d N}
    (hXm : ∀ r : ℝ≥0, Measurable (X r))
    (hSgm : Measurable (Function.uncurry (covMatrixProcess (qPhi D t F X))))
    {H : ℝ} (hH0 : 0 ≤ H) {T : ℝ} (hT0 : 0 ≤ T) (hT : ∀ a, t a ≤ T)
    (hent : ∀ σ ∈ Set.Icc (0 : ℝ) T, relEntropy (P.map (X σ.toNNReal))
      (Measure.pi fun _ : Fin N => withDensityReal (ρ σ)) ≤ ENNReal.ofReal H) :
    covDiscrepancyMatrix P T (covMatrixProcess (qPhi D t F X)) (qsb D ρ t F) ≤
      (∑ a, ∑ b, 2 * D.invβ * Ca a * Ca b / (2 * m)) * Real.sqrt (2 * (H + Real.log 2) / N) := by
  set Sg := covMatrixProcess (qPhi D t F X) with hSg
  set sb := qsb D ρ t F with hsb
  set Δ : ℝ := Real.sqrt (2 * (H + Real.log 2) / N) with hΔ
  have hΔ0 : 0 ≤ Δ := Real.sqrt_nonneg _
  have hq : 0 ≤ 2 * D.invβ := by linarith [D.hβ]
  have hsbm := q40b_qsb_meas D h.t0 h.hF h.rhoJ
  -- the entrywise absolute error, jointly measurable and bounded
  set E : Fin p → Fin p → ℝ × Ω → ℝ := fun a b q => |Sg q.1 q.2 a b - sb q.1 a b| with hE
  have hEm : ∀ a b, Measurable (E a b) := by
    intro a b
    refine Measurable.abs (Measurable.sub ?_ ?_)
    · exact (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hSgm)
    · exact (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hsbm) |>.comp measurable_fst
  have hEb : ∀ a b q, E a b q ≤ 2 * (2 * D.invβ * Ca a * Ca b) := by
    intro a b q
    have h1 := q40b_Sg_bound h hN X q.1 q.2 a b
    have h2 := (q40b_qsb_entry_bound h q.1 a b).2
    calc E a b q ≤ |Sg q.1 q.2 a b| + |sb q.1 a b| := abs_sub _ _
      _ ≤ _ := by linarith
  have hE0 : ∀ a b q, 0 ≤ E a b q := fun a b q => abs_nonneg _
  set Gs : ℝ × Ω → ℝ := fun q => ∑ a, ∑ b, E a b q with hGs
  have hGsm : Measurable Gs := Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => hEm a b
  set Bs : ℝ := ∑ a : Fin p, ∑ b : Fin p, 2 * (2 * D.invβ * Ca a * Ca b) with hBs
  have hGsb : ∀ q, |Gs q| ≤ Bs := by
    intro q
    rw [abs_of_nonneg (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hE0 a b q)]
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hEb a b q
  have hGs0 : ∀ q, 0 ≤ Gs q := fun q =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hE0 a b q
  -- inner integrability in `σ`
  have hinner : ∀ ω, Integrable (fun σ => Gs (σ, ω)) (volume.restrict (Set.Icc 0 T)) := fun ω =>
    Measure.integrableOn_of_bounded (M := Bs) measure_Icc_lt_top.ne
      (hGsm.comp measurable_prodMk_right).aestronglyMeasurable
      (Filter.Eventually.of_forall fun σ => by simpa using hGsb (σ, ω))
  -- step 1: pointwise in `ω`
  have step1 : ∀ ω, ∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ) ≤ ∫ σ in Set.Icc 0 T, Gs (σ, ω) := by
    intro ω
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun σ => traceNormMatrix_nonneg _)
      (hinner ω) (Filter.Eventually.of_forall fun σ => ?_)
    refine (PDE.MFLinear.traceNormMatrix_le_sum _).trans (le_of_eq ?_)
    simp only [hGs, hE, Matrix.sub_apply]
  -- step 2: integrate in `ω`
  have hOutM : Measurable (fun ω => ∫ σ in Set.Icc 0 T, Gs (σ, ω)) :=
    measurable_setIntegral_Icc (fun q : ℝ × Ω => Gs q) hGsm 0 T
  have hOutI : Integrable (fun ω => ∫ σ in Set.Icc 0 T, Gs (σ, ω)) P := by
    refine Integrable.of_bound (C := Bs * (T - 0)) hOutM.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : ℝ) T) (C := Bs)
      (f := fun σ => Gs (σ, ω)) measure_Icc_lt_top (fun σ _ => by simpa using hGsb (σ, ω))
    rw [Real.norm_eq_abs] at this
    simpa [Real.volume_real_Icc_of_le hT0] using this
  have step2 : covDiscrepancyMatrix P T Sg sb ≤ ∫ ω, (∫ σ in Set.Icc 0 T, Gs (σ, ω)) ∂P := by
    unfold covDiscrepancyMatrix
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
      setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _) hOutI
      (Filter.Eventually.of_forall step1)
  -- step 3: swap the integrals
  have hprodI : Integrable (fun q : ℝ × Ω => Gs q) ((volume.restrict (Set.Icc 0 T)).prod P) :=
    Integrable.of_bound (C := Bs) hGsm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by simpa using hGsb q)
  have step3 : ∫ ω, (∫ σ in Set.Icc 0 T, Gs (σ, ω)) ∂P = ∫ σ in Set.Icc 0 T, (∫ ω, Gs (σ, ω) ∂P) :=
    (integral_integral_swap (f := fun σ ω => Gs (σ, ω)) hprodI).symm
  -- step 4: the bound for fixed `σ`
  set Kab : Fin p → Fin p → ℝ → ℝ := fun a b σ => (Set.Icc 0 (min (t a) (t b))).indicator
    (fun σ => 2 * D.invβ * ((Ca a * Real.exp (-m * (t a - σ))) * (Ca b * Real.exp (-m * (t b - σ)))) * Δ) σ
    with hKab
  have hEint : ∀ a b σ, Integrable (fun ω => E a b (σ, ω)) P := fun a b σ =>
    Integrable.of_bound (C := 2 * (2 * D.invβ * Ca a * Ca b))
      ((hEm a b).comp measurable_prodMk_left).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hE0 a b _)]; exact hEb a b _)
  have hKpt : ∀ a b σ, ∫ ω, E a b (σ, ω) ∂P ≤ Kab a b σ := by
    intro a b σ
    by_cases hσ : σ ∈ Set.Icc 0 (min (t a) (t b))
    · simp only [hKab, Set.indicator_of_mem hσ]
      exact dyncmp_Q_L1 h hN hXm hH0 (hT a) (hT b) hent hσ
    · simp only [hKab, Set.indicator_of_notMem hσ]
      have : ∀ ω, E a b (σ, ω) = 0 := by
        intro ω
        simp only [hE, hSg]
        rw [q40b_sigma_formula hN, if_neg hσ]
        simp only [hsb, qsb, Matrix.of_apply, if_neg hσ, sub_zero, abs_zero]
      simp [this]
  -- step 5: integrate in `σ`
  have hSsub : ∀ a b, Set.Icc (0 : ℝ) (min (t a) (t b)) ⊆ Set.Icc 0 T := fun a b σ hσ =>
    ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans (hT a))⟩
  have hKint : ∀ a b, Integrable (Kab a b) (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    intro a b
    have hfc : Continuous fun σ : ℝ => 2 * D.invβ * ((Ca a * Real.exp (-m * (t a - σ))) *
        (Ca b * Real.exp (-m * (t b - σ)))) * Δ := by fun_prop
    exact ((hfc.integrableOn_Icc (a := 0) (b := min (t a) (t b))).integrable_indicator
      measurableSet_Icc).integrableOn
  have step4 : ∫ σ in Set.Icc 0 T, (∫ ω, Gs (σ, ω) ∂P) ≤
      ∫ σ in Set.Icc 0 T, ∑ a, ∑ b, Kab a b σ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun σ =>
      integral_nonneg fun ω => hGs0 _) ?_ (Filter.Eventually.of_forall fun σ => ?_)
    · exact integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => hKint a b
    · have : ∫ ω, Gs (σ, ω) ∂P = ∑ a, ∑ b, ∫ ω, E a b (σ, ω) ∂P := by
        simp only [hGs]
        rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun b _ => hEint a b σ)]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_finset_sum _ (fun b _ => hEint a b σ)]
      show ∫ ω, Gs (σ, ω) ∂P ≤ ∑ a, ∑ b, Kab a b σ
      rw [this]
      exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hKpt a b σ
  have step5 : ∀ a b, ∫ σ in Set.Icc 0 T, Kab a b σ ≤ 2 * D.invβ * Ca a * Ca b / (2 * m) * Δ := by
    intro a b
    have hsub := hSsub a b
    have e1 : ∫ σ in Set.Icc 0 T, Kab a b σ = ∫ σ in Set.Icc (0 : ℝ) (min (t a) (t b)),
        2 * D.invβ * ((Ca a * Real.exp (-m * (t a - σ))) * (Ca b * Real.exp (-m * (t b - σ)))) * Δ := by
      have := setIntegral_indicator (μ := volume) (s := Set.Icc (0 : ℝ) T)
        (t := Set.Icc (0 : ℝ) (min (t a) (t b))) measurableSet_Icc
        (f := fun σ => 2 * D.invβ * ((Ca a * Real.exp (-m * (t a - σ))) *
          (Ca b * Real.exp (-m * (t b - σ)))) * Δ)
      rw [Set.inter_eq_right.2 hsub] at this
      exact this
    rw [e1]
    have e2 : ∀ σ : ℝ, 2 * D.invβ * ((Ca a * Real.exp (-m * (t a - σ))) *
        (Ca b * Real.exp (-m * (t b - σ)))) * Δ =
        (2 * D.invβ * Ca a * Ca b * Δ) * (Real.exp (-m * (t a - σ)) * Real.exp (-m * (t b - σ))) := by
      intro σ; ring
    simp_rw [e2]
    rw [integral_const_mul]
    have hmn : (0 : ℝ) ≤ min (t a) (t b) := le_min (h.t0 a) (h.t0 b)
    have := q40b_exp_int h.hm hmn (min_le_left (t a) (t b)) (min_le_right (t a) (t b))
    have hc : 0 ≤ 2 * D.invβ * Ca a * Ca b * Δ := by
      have := h.hC0 a; have := h.hC0 b; positivity
    calc (2 * D.invβ * Ca a * Ca b * Δ) * ∫ σ in Set.Icc (0 : ℝ) (min (t a) (t b)),
          Real.exp (-m * (t a - σ)) * Real.exp (-m * (t b - σ))
        ≤ (2 * D.invβ * Ca a * Ca b * Δ) * (1 / (2 * m)) := mul_le_mul_of_nonneg_left this hc
      _ = _ := by field_simp
  calc covDiscrepancyMatrix P T Sg sb ≤ ∫ ω, (∫ σ in Set.Icc 0 T, Gs (σ, ω)) ∂P := step2
    _ = ∫ σ in Set.Icc 0 T, (∫ ω, Gs (σ, ω) ∂P) := step3
    _ ≤ ∫ σ in Set.Icc 0 T, ∑ a, ∑ b, Kab a b σ := step4
    _ = ∑ a, ∑ b, ∫ σ in Set.Icc 0 T, Kab a b σ := by
        rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun b _ => hKint a b)]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_finset_sum _ (fun b _ => hKint a b)]
    _ ≤ ∑ a, ∑ b, 2 * D.invβ * Ca a * Ca b / (2 * m) * Δ :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => step5 a b
    _ = _ := by rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => ?_; rw [Finset.sum_mul]

end Bracket

end HRS.Q40b
