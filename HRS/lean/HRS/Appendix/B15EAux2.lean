import HRS.Appendix.B15EAux1

/-!
# Packet B15E, part 2: Gronwall stability of the regularised SDE in the potential, convergence of marginals

For Stage 1 of the assembly (see the plan in `B15EAux1.lean`): the level-`M` regularised SDE with potential
`V_k ≤ V`, `∇V_k → ∇V` uniformly, has solutions `Y^k` converging to the solution `Y` for `V` uniformly on
`[0,T]` almost surely (additive noise, same initial value: an integral Gronwall inequality for the
difference), hence all time marginals converge narrowly.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- Integral Gronwall inequality (sup bound): if `‖z s‖ ≤ c + L ∫_0^s ‖z‖` on `[0,T]` with `z` continuous,
then `‖z s‖ ≤ 2 c e^{(2L+2) s}`. -/
theorem b15e_gronwall_unif {E : Type*} [NormedAddCommGroup E] {T L c : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hc : 0 ≤ c) {z : ℝ → E} (hz : ContinuousOn z (Icc 0 T))
    (h : ∀ s ∈ Icc 0 T, ‖z s‖ ≤ c + L * ∫ r in (0:ℝ)..s, ‖z r‖) :
    ∀ s ∈ Icc 0 T, ‖z s‖ ≤ 2 * c * Real.exp ((2 * L + 2) * s) := by
  set lam : ℝ := 2 * L + 2 with hlam
  have hlampos : 0 < lam := by rw [hlam]; linarith
  set g : ℝ → ℝ := fun s => ‖z s‖ * Real.exp (-(lam * s)) with hg
  have hgc : ContinuousOn g (Icc 0 T) := by
    refine hz.norm.mul ?_
    exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
  obtain ⟨s0, hs0, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hT) hgc
  set A := g s0 with hA
  have hgle : ∀ s ∈ Icc 0 T, g s ≤ A := fun s hs => hmax hs
  -- pointwise bound ‖z r‖ ≤ A e^{λ r}
  have hzr : ∀ r ∈ Icc 0 T, ‖z r‖ ≤ A * Real.exp (lam * r) := by
    intro r hr
    have := hgle r hr
    simp only [hg] at this
    have h2 : ‖z r‖ = g r * Real.exp (lam * r) := by
      simp only [hg]; rw [mul_assoc, ← Real.exp_add]; simp
    rw [h2]
    exact mul_le_mul_of_nonneg_right (hgle r hr) (Real.exp_pos _).le
  have hint : ∀ s ∈ Icc 0 T, ∫ r in (0:ℝ)..s, ‖z r‖ ≤ A * Real.exp (lam * s) / lam := by
    intro s hs
    have hsub : Icc 0 s ⊆ Icc 0 T := Icc_subset_Icc_right hs.2
    have hzc : ContinuousOn (fun r => ‖z r‖) (Icc 0 s) := (hz.mono hsub).norm
    calc ∫ r in (0:ℝ)..s, ‖z r‖ ≤ ∫ r in (0:ℝ)..s, A * Real.exp (lam * r) := by
          refine intervalIntegral.integral_mono_on hs.1 ?_ ?_ fun r hr => hzr r ⟨hr.1, hr.2.trans hs.2⟩
          · exact (hzc.intervalIntegrable_of_Icc hs.1)
          · exact (by fun_prop : Continuous fun r : ℝ => A * Real.exp (lam * r)).intervalIntegrable _ _
      _ = A * ((Real.exp (lam * s) - 1) / lam) := by
          rw [intervalIntegral.integral_const_mul]
          congr 1
          have := integral_exp_mul_complex (a := (0:ℝ)) (b := s) (c := (lam : ℂ))
          simp only [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) hlampos.ne', smul_eq_mul]
          rw [integral_exp]
          simp; field_simp
      _ ≤ A * Real.exp (lam * s) / lam := by
          have hA0 : 0 ≤ A := (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
          rw [mul_div_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hA0
          exact div_le_div_of_nonneg_right (by linarith) hlampos.le
  have hA0 : 0 ≤ A := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hmain : ∀ s ∈ Icc 0 T, g s ≤ c + A / 2 := by
    intro s hs
    have h1 := h s hs
    have h2 := hint s hs
    have hLe : L * ∫ r in (0:ℝ)..s, ‖z r‖ ≤ L * (A * Real.exp (lam * s) / lam) :=
      mul_le_mul_of_nonneg_left h2 hL
    have hexp : 0 < Real.exp (-(lam * s)) := Real.exp_pos _
    have hmul : Real.exp (lam * s) * Real.exp (-(lam * s)) = 1 := by rw [← Real.exp_add]; simp
    have hLl : L / lam ≤ 1 / 2 := by
      rw [div_le_iff₀ hlampos]; rw [hlam]; linarith
    calc g s = ‖z s‖ * Real.exp (-(lam * s)) := rfl
      _ ≤ (c + L * (A * Real.exp (lam * s) / lam)) * Real.exp (-(lam * s)) :=
          mul_le_mul_of_nonneg_right (h1.trans (by linarith)) hexp.le
      _ = c * Real.exp (-(lam * s)) + (L / lam) * A * (Real.exp (lam * s) * Real.exp (-(lam * s))) := by
          ring
      _ ≤ c + A / 2 := by
          rw [hmul]
          have e1 : c * Real.exp (-(lam * s)) ≤ c := by
            have : Real.exp (-(lam * s)) ≤ 1 := by
              rw [Real.exp_le_one_iff]; have := hs.1; nlinarith
            nlinarith
          have e2 : (L / lam) * A * 1 ≤ A / 2 := by
            have := mul_le_mul_of_nonneg_right hLl hA0
            linarith
          linarith
  have hAle : A ≤ 2 * c := by
    have := hmain s0 hs0
    simp only [hA] at this ⊢
    linarith
  intro s hs
  have h1 := hgle s hs
  have h2 : ‖z s‖ = g s * Real.exp (lam * s) := by
    simp only [hg]; rw [mul_assoc, ← Real.exp_add]; simp
  rw [h2]
  calc g s * Real.exp (lam * s) ≤ (2 * c) * Real.exp (lam * s) :=
        mul_le_mul_of_nonneg_right (h1.trans hAle) (Real.exp_pos _).le
    _ = _ := by rw [hlam]

/-- **Pathwise stability** of additive-noise strong solutions in the drift: two solutions with the same
noise and initial value, drifts `b` (Lipschitz with constant `L`) and `b'` with `‖b' - b‖ ≤ ε`, stay within
`2 ε T e^{(2L+2) T}` of each other on `[0,T]` (almost surely). -/
theorem b15e_sde_stability {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ' : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {b b' : (Fin N → Euc d) → (Fin N → Euc d)} {σ : (Fin N × Fin d) → (Fin N → Euc d)}
    {Y₀ : Ω → Fin N → Euc d} {Y Y' : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsAdditiveSDESolution P ℱ' W' (fun _ => b) σ Y₀ (fun _ => ⊤) Y)
    (hY' : IsAdditiveSDESolution P ℱ' W' (fun _ => b') σ Y₀ (fun _ => ⊤) Y')
    {L : ℝ≥0} (hb : LipschitzWith L b) {ε : ℝ} (hε : 0 ≤ ε) (hbb : ∀ y, ‖b' y - b y‖ ≤ ε)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T,
      ‖Y' t ω - Y t ω‖ ≤ 2 * (ε * T) * Real.exp ((2 * (L : ℝ) + 2) * t) := by
  filter_upwards [hY.eq, hY'.eq] with ω h1 h2
  have hc : ContinuousOn (fun s => Y' s ω - Y s ω) (Icc 0 T) :=
    (hY'.cont ω T hT (WithTop.coe_lt_top T)).sub (hY.cont ω T hT (WithTop.coe_lt_top T))
  refine b15e_gronwall_unif (L := (L : ℝ)) hT L.coe_nonneg (mul_nonneg hε hT) hc ?_
  intro s hs
  obtain ⟨hi1, he1⟩ := h1 s hs.1 (WithTop.coe_lt_top s)
  obtain ⟨hi2, he2⟩ := h2 s hs.1 (WithTop.coe_lt_top s)
  have hsub : Icc 0 s ⊆ Icc 0 T := Icc_subset_Icc_right hs.2
  have hdiff : Y' s ω - Y s ω = ∫ r in (0:ℝ)..s, (b (Y' r ω) - b (Y r ω)) + (b' (Y' r ω) - b (Y' r ω)) := by
    rw [← setIntegral_Icc_eq_interval hs.1]
    have hi3 : IntegrableOn (fun r => b' (Y' r ω)) (Icc 0 s) := hi2
    have hi4 : IntegrableOn (fun r => b (Y r ω)) (Icc 0 s) := hi1
    have : ∀ r, (b (Y' r ω) - b (Y r ω)) + (b' (Y' r ω) - b (Y' r ω)) = b' (Y' r ω) - b (Y r ω) := by
      intro r; abel
    simp only [this]
    rw [integral_sub hi3 hi4, he1, he2]
    abel
  rw [hdiff]
  have hcont : ContinuousOn (fun r => ‖Y' r ω - Y r ω‖) (Icc 0 s) := (hc.mono hsub).norm
  have hI : IntervalIntegrable (fun r => ‖Y' r ω - Y r ω‖) volume 0 s :=
    hcont.intervalIntegrable_of_Icc hs.1
  set Lr : ℝ := (L : ℝ) with hLr
  have hI2 : IntervalIntegrable (fun r => ε + Lr * ‖Y' r ω - Y r ω‖) volume 0 s :=
    intervalIntegrable_const.add (hI.const_mul Lr)
  refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun r => ε + Lr * ‖Y' r ω - Y r ω‖)
    hs.1 (Eventually.of_forall fun r hr => ?_) hI2).trans ?_
  · have hrT : r ∈ Icc (0:ℝ) T := ⟨hr.1.le, hr.2.trans hs.2⟩
    calc ‖(b (Y' r ω) - b (Y r ω)) + (b' (Y' r ω) - b (Y' r ω))‖
        ≤ ‖b (Y' r ω) - b (Y r ω)‖ + ‖b' (Y' r ω) - b (Y' r ω)‖ := norm_add_le _ _
      _ ≤ Lr * ‖Y' r ω - Y r ω‖ + ε := by
          gcongr
          · have := hb.dist_le_mul (Y' r ω) (Y r ω)
            simpa [dist_eq_norm] using this
          · exact hbb _
      _ = _ := by ring
  · rw [intervalIntegral.integral_add intervalIntegrable_const (hI.const_mul Lr),
      intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    have h3 : s * ε ≤ ε * T := by nlinarith [hs.2, hε]
    linarith

/-- Convergence of integrals from a.s. pointwise convergence (generic). -/
theorem b15e_integral_tendsto_of_tendsto {Ω α : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace α]
    [TopologicalSpace α] {P : Measure Ω} [IsProbabilityMeasure P]
    {Xn : ℕ → Ω → α} {X : Ω → α} (hXn : ∀ n, Measurable (Xn n)) (hX : Measurable X)
    (h : ∀ᵐ ω ∂P, Tendsto (fun n => Xn n ω) atTop (𝓝 (X ω))) {φ : α → ℝ} (hφc : Continuous φ)
    (hφ : Measurable φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C) :
    Tendsto (fun n => ∫ x, φ x ∂(P.map (Xn n))) atTop (𝓝 (∫ x, φ x ∂(P.map X))) := by
  have e : ∀ Z : Ω → α, Measurable Z → ∫ x, φ x ∂(P.map Z) = ∫ ω, φ (Z ω) ∂P := fun Z hZ =>
    integral_map hZ.aemeasurable hφ.aestronglyMeasurable
  simp only [e _ (hXn _), e _ hX]
  refine tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => (hφ.comp (hXn n)).aestronglyMeasurable) (integrable_const C)
    (fun n => Filter.Eventually.of_forall fun ω => by simpa using hC _) ?_
  filter_upwards [h] with ω hω
  exact (hφc.tendsto _).comp hω

/-- **Narrow convergence of the time marginals** of regularised solutions `Y^k → Y` converging uniformly on
`[0,T]` (a.s.): for `t ∈ [0,T]` and continuous `φ`, `∫ φ dP^t_k → ∫ φ dP^t`. -/
theorem b15e_marginal_tendsto_unif {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ' : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {b : ℕ → (Fin N → Euc d) → (Fin N → Euc d)} {b0 : (Fin N → Euc d) → (Fin N → Euc d)}
    {σ : (Fin N × Fin d) → (Fin N → Euc d)}
    {Y₀ : Ω → Fin N → Euc d} {Yk : ℕ → ℝ → Ω → (Fin N → Euc d)} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hYk : ∀ k, IsAdditiveSDESolution P ℱ' W' (fun _ => b k) σ Y₀ (fun _ => ⊤) (Yk k))
    (hY : IsAdditiveSDESolution P ℱ' W' (fun _ => b0) σ Y₀ (fun _ => ⊤) Y)
    {T : ℝ} {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (hconv : ∀ᵐ ω ∂P, ∀ k, ∀ t ∈ Icc (0 : ℝ) T, ‖Yk k t ω - Y t ω‖ ≤ δ k)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {φ : Config d N → ℝ} (hφ : Continuous φ) :
    Tendsto (fun k => ∫ x, φ x ∂(selectedLaw P (b15c_regProcess (Yk k)) t)) atTop
      (𝓝 (∫ x, φ x ∂(selectedLaw P (b15c_regProcess Y) t))) := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Config d N)).exists_bound_of_continuousOn hφ.continuousOn
  unfold selectedLaw
  refine b15e_integral_tendsto_of_tendsto (fun k => b15c_regProcess_measurable (hYk k) _)
    (b15c_regProcess_measurable hY _) ?_ hφ hφ.measurable (C := C) (fun x => by simpa using hC x (mem_univ x))
  filter_upwards [hconv] with ω hω
  have ht' : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht0
  have hY1 : Tendsto (fun k => Yk k t ω) atTop (𝓝 (Y t ω)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hδ
    exact hω k t ⟨ht0, htT⟩
  have hmk : Continuous (fun Z : Fin N → Euc d => (fun i => Torus.mk (Z i) : Config d N)) :=
    continuous_pi fun i => Torus.continuous_mk.comp (continuous_apply i)
  have hY1' : Tendsto (fun k => Yk k (((Real.toNNReal t : ℝ≥0) : ℝ)) ω) atTop
      (𝓝 (Y (((Real.toNNReal t : ℝ≥0) : ℝ)) ω)) := by rw [ht']; exact hY1
  exact (hmk.tendsto _).comp hY1'

end HRS
