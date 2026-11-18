import HRS.Stochastic.Ito

/-!
# Stochastic differential equations with additive noise

Package SI-01, part 7.  `dY_t = b(t, Y_t) dt + ∑_k σ_k dW^k_t`, `Y_0 = Y₀`, in a finite-dimensional
normed space `E`, with `b` continuous and locally Lipschitz in `Y` on an open set `U`, up to the
exit time from `U` / explosion time.  Because the noise is additive, `Z = Y - ∑_k W^k σ_k` solves
the random ODE `Z' = b(t, Z + ∑_k W^k_t σ_k)` pathwise, so existence and uniqueness are
Picard–Lindelöf / Gronwall statements applied for each fixed continuous path `w` of the noise
(`ode_additive_unique`, `exists_ode_additive_maximal`); measurability in `ω` comes from the
explicit Picard iteration.  This is the route of Lemma B.1-maximal (M L11731-11757: truncation
to globally Lipschitz drifts, pasting, collision alternative) and of `IsStrongSolution`
(ISSUES §D1: "additive noise ⇒ no Itô integral in the definition").

The solution concept `IsAdditiveSDESolution P ℱ W b σ Y₀ τ Y`: `Y` adapted, `Y_0 = Y₀`, paths
continuous on `[0, t]` for `t < τ`, and a.s. for all `0 ≤ t < τ`
`Y_t = Y₀ + ∫_0^t b(s, Y_s) ds + ∑_k W^k_t σ_k` with `s ↦ b(s, Y_s)` integrable on `[0, t]`.
The bridge to `HRS.IsStrongSolution` (torus particle system) is in `HRS/Stochastic/Bridge.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `b : ℝ → E → E` is continuous on `[0, ∞) × U` and locally Lipschitz in the space variable,
uniformly on compact time intervals: for every compact `K ⊆ U` and every `T`, there is `L` with
`‖b t y - b t z‖ ≤ L ‖y - z‖` for `t ∈ [0, T]`, `y, z ∈ K`. -/
structure IsLocLipschitzDrift (U : Set E) (b : ℝ → E → E) : Prop where
  cont : ContinuousOn (Function.uncurry b) (Set.Ici 0 ×ˢ U)
  lip : ∀ K : Set E, IsCompact K → K ⊆ U → ∀ T : ℝ, ∃ L : ℝ≥0, ∀ t ∈ Set.Icc 0 T,
    LipschitzOnWith L (b t) K

/-- Globally Lipschitz drifts (uniformly in time on compacts), continuous on `[0,∞) × E`. -/
structure IsLipschitzDrift (b : ℝ → E → E) : Prop where
  cont : ContinuousOn (Function.uncurry b) (Set.Ici 0 ×ˢ Set.univ)
  lip : ∀ T : ℝ, ∃ L : ℝ≥0, ∀ t ∈ Set.Icc 0 T, LipschitzWith L (b t)

/-! ### Pathwise (deterministic) statements -/

/-- A pathwise solution of `y_t = y₀ + ∫_0^t b(s, y_s) ds + ∑_k w^k_t σ_k` on `[0, τ)` for a fixed
continuous noise path `w : ℝ≥0 → ι → ℝ`. -/
def IsPathSolution (b : ℝ → E → E) (σ : ι → E) (w : ℝ≥0 → ι → ℝ) (y₀ : E) (τ : WithTop ℝ)
    (y : ℝ → E) : Prop :=
  y 0 = y₀ ∧ ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ →
    ContinuousOn y (Set.Icc 0 t) ∧ IntegrableOn (fun s => b s (y s)) (Set.Icc 0 t) ∧
    y t = y₀ + (∫ s in Set.Icc 0 t, b s (y s)) + ∑ k, w (Real.toNNReal t) k • σ k

section PathAux

set_option linter.unusedSectionVars false

/-- The noise term `∑ k, w^k_t σ_k` read at real time. -/
def addNoise (σ : ι → E) (w : ℝ≥0 → ι → ℝ) (t : ℝ) : E := ∑ k, w (Real.toNNReal t) k • σ k

theorem continuous_addNoise (σ : ι → E) {w : ℝ≥0 → ι → ℝ} (hw : Continuous w) :
    Continuous (addNoise σ w) := by
  unfold addNoise
  refine continuous_finsetSum _ fun k _ => ?_
  exact ((continuous_apply k).comp (hw.comp continuous_real_toNNReal)).smul continuous_const

theorem addNoise_max (σ : ι → E) (w : ℝ≥0 → ι → ℝ) (t : ℝ) :
    addNoise σ w t = addNoise σ w (max t 0) := by
  have : (max t 0).toNNReal = t.toNNReal := by
    apply NNReal.coe_injective; simp [Real.coe_toNNReal']
  simp [addNoise, this]

theorem setIntegral_Icc_eq_interval {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {s : ℝ} (hs : 0 ≤ s) :
    ∫ r in Set.Icc 0 s, f r = ∫ r in (0:ℝ)..s, f r := by
  rw [intervalIntegral.integral_of_le hs, integral_Icc_eq_integral_Ioc]

theorem norm_integral_le_pow {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L M : ℝ} (n : ℕ) {t : ℝ} (ht : 0 ≤ t) {f : ℝ → F}
    (hf : ∀ s ∈ Set.Icc 0 t, ‖f s‖ ≤ L * (M * (L * s) ^ n / n.factorial)) :
    ‖∫ s in (0:ℝ)..t, f s‖ ≤ M * (L * t) ^ (n + 1) / (n + 1).factorial := by
  have h1 : ‖∫ s in (0:ℝ)..t, f s‖ ≤ ∫ s in (0:ℝ)..t, L * (M * (L * s) ^ n / n.factorial) := by
    apply intervalIntegral.norm_integral_le_of_norm_le ht
    · exact Filter.Eventually.of_forall fun s hs => hf s ⟨hs.1.le, hs.2⟩
    · exact (by fun_prop : Continuous fun s : ℝ => L * (M * (L * s) ^ n / n.factorial)).intervalIntegrable _ _
  refine h1.trans (le_of_eq ?_)
  have : (fun s : ℝ => L * (M * (L * s) ^ n / n.factorial)) =
      fun s => (L * M * L ^ n / n.factorial) * s ^ n := by
    ext s; rw [mul_pow]; ring
  rw [this, intervalIntegral.integral_const_mul, integral_pow]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem eq_zero_of_integral_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {d : ℝ → F} {T L M : ℝ} (hL : 0 ≤ L)
    (hM : ∀ s ∈ Set.Icc 0 T, ‖d s‖ ≤ M)
    (hd : ∀ s ∈ Set.Icc 0 T, ∃ f : ℝ → F, d s = ∫ r in (0:ℝ)..s, f r ∧
      ∀ r ∈ Set.Icc 0 s, ‖f r‖ ≤ L * ‖d r‖) :
    ∀ s ∈ Set.Icc 0 T, d s = 0 := by
  have key : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ‖d s‖ ≤ M * (L * s) ^ n / n.factorial := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hM s hs
    | succ n ih =>
      intro s hs
      obtain ⟨f, hfd, hf⟩ := hd s hs
      rw [hfd]
      refine norm_integral_le_pow n hs.1 fun r hr => (hf r hr).trans ?_
      exact mul_le_mul_of_nonneg_left (ih r ⟨hr.1, hr.2.trans hs.2⟩) hL
  intro s hs
  have h0 : Tendsto (fun n : ℕ => M * ((L * s) ^ n / n.factorial)) atTop (𝓝 (M * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (L * s)).const_mul M
  have : ‖d s‖ ≤ 0 := by
    refine ge_of_tendsto' (by simpa using h0) fun n => ?_
    simpa [mul_div_assoc] using key n s hs
  exact norm_le_zero_iff.1 this


end PathAux

/-- **Pathwise uniqueness** for additive noise: two pathwise solutions with values in `U`
coincide on `[0, min τ τ')` (Gronwall on `z = y - ∑_k w^k σ_k`). -/
theorem ode_additive_unique (U : Set E) (hU : IsOpen U) (b : ℝ → E → E)
    (hb : IsLocLipschitzDrift U b) (σ : ι → E) (w : ℝ≥0 → ι → ℝ) (hw : Continuous w) (y₀ : E)
    {τ τ' : WithTop ℝ} {y y' : ℝ → E} (hy : IsPathSolution b σ w y₀ τ y)
    (hy' : IsPathSolution b σ w y₀ τ' y') (hyU : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ → y t ∈ U)
    (hy'U : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ' → y' t ∈ U) :
    ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < min τ τ' → y t = y' t := by
  intro T hT0 hTlt
  have hτ : (T : WithTop ℝ) < τ := lt_of_lt_of_le hTlt (min_le_left _ _)
  have hτ' : (T : WithTop ℝ) < τ' := lt_of_lt_of_le hTlt (min_le_right _ _)
  have hcont : ContinuousOn y (Set.Icc 0 T) := (hy.2 T hT0 hτ).1
  have hcont' : ContinuousOn y' (Set.Icc 0 T) := (hy'.2 T hT0 hτ').1
  have hlt : ∀ s ∈ Set.Icc (0:ℝ) T, (s : WithTop ℝ) < τ ∧ (s : WithTop ℝ) < τ' := fun s hs =>
    ⟨lt_of_le_of_lt (by exact_mod_cast hs.2) hτ, lt_of_le_of_lt (by exact_mod_cast hs.2) hτ'⟩
  set K : Set E := y '' Set.Icc 0 T ∪ y' '' Set.Icc 0 T with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.image_of_continuousOn hcont).union (isCompact_Icc.image_of_continuousOn hcont')
  have hKU : K ⊆ U := by
    rintro _ (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact hyU s hs.1 (hlt s hs).1
    · exact hy'U s hs.1 (hlt s hs).2
  obtain ⟨L, hL⟩ := hb.lip K hKc hKU T
  have hyK : ∀ s ∈ Set.Icc (0:ℝ) T, y s ∈ K := fun s hs => Or.inl ⟨s, hs, rfl⟩
  have hy'K : ∀ s ∈ Set.Icc (0:ℝ) T, y' s ∈ K := fun s hs => Or.inr ⟨s, hs, rfl⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont.sub hcont')
  have := eq_zero_of_integral_bound (d := fun s => y s - y' s) (T := T) (L := (L : ℝ)) (M := M)
    L.2 (fun s hs => hM s hs) ?_
  · exact sub_eq_zero.1 (this T ⟨hT0, le_rfl⟩)
  intro s hs
  have hsτ := hlt s hs
  obtain ⟨_, hi, he⟩ := hy.2 s hs.1 hsτ.1
  obtain ⟨_, hi', he'⟩ := hy'.2 s hs.1 hsτ.2
  refine ⟨fun r => b r (y r) - b r (y' r), ?_, ?_⟩
  · rw [← setIntegral_Icc_eq_interval hs.1, integral_sub hi hi', he, he']
    abel
  · intro r hr
    have hrT : r ∈ Set.Icc (0:ℝ) T := ⟨hr.1, hr.2.trans hs.2⟩
    have := (hL r hrT).dist_le_mul (y r) (hyK r hrT) (y' r) (hy'K r hrT)
    simpa [dist_eq_norm] using this

section PicardAux

set_option linter.unusedSectionVars false

/-- The Picard iterates for `y_t = y₀ + ∫_0^t b(s, y_s) ds + ∑_k w^k_t σ_k`. -/
def picardIter (b : ℝ → E → E) (σ : ι → E) (w : ℝ≥0 → ι → ℝ) (y₀ : E) : ℕ → ℝ → E
  | 0 => fun t => y₀ + addNoise σ w t
  | n + 1 => fun t => y₀ + (∫ s in (0:ℝ)..max t 0, b (max s 0) (picardIter b σ w y₀ n s)) +
      addNoise σ w t

theorem picardIter_max (b : ℝ → E → E) (σ : ι → E) (w : ℝ≥0 → ι → ℝ) (y₀ : E) (n : ℕ) (t : ℝ) :
    picardIter b σ w y₀ n t = picardIter b σ w y₀ n (max t 0) := by
  cases n with
  | zero => simp only [picardIter]; rw [addNoise_max σ w t]
  | succ n => simp only [picardIter, max_assoc, max_self]; rw [addNoise_max σ w t]

theorem continuous_bpos_comp (b : ℝ → E → E) (hb : IsLipschitzDrift b) {z : ℝ → E}
    (hz : Continuous z) : Continuous fun s => b (max s 0) (z s) := by
  have : Continuous fun s : ℝ => (max s 0, z s) := (continuous_id.max continuous_const).prodMk hz
  exact hb.cont.comp_continuous this (fun s => ⟨Set.mem_Ici.2 (le_max_right _ _), Set.mem_univ _⟩)

theorem continuous_picardIter (b : ℝ → E → E) (hb : IsLipschitzDrift b) (σ : ι → E)
    {w : ℝ≥0 → ι → ℝ} (hw : Continuous w) (y₀ : E) (n : ℕ) :
    Continuous (picardIter b σ w y₀ n) := by
  induction n with
  | zero => exact continuous_const.add (continuous_addNoise σ hw)
  | succ n ih =>
    simp only [picardIter]
    refine (continuous_const.add ?_).add (continuous_addNoise σ hw)
    have hc := continuous_bpos_comp b hb ih
    exact (intervalIntegral.continuous_primitive (fun a c => hc.intervalIntegrable a c) 0).comp
      (continuous_id.max continuous_const)

theorem picardIter_diff_le (b : ℝ → E → E) (hb : IsLipschitzDrift b) (σ : ι → E)
    {w : ℝ≥0 → ι → ℝ} (hw : Continuous w) (y₀ : E) (T : ℝ) :
    ∃ L M : ℝ, 0 ≤ L ∧ ∀ n : ℕ, ∀ t ∈ Set.Icc (0:ℝ) T,
      ‖picardIter b σ w y₀ (n + 1) t - picardIter b σ w y₀ n t‖ ≤ M * (L * t) ^ n / n.factorial := by
  obtain ⟨L, hL⟩ := hb.lip T
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (((continuous_picardIter b hb σ hw y₀ 1).sub (continuous_picardIter b hb σ hw y₀ 0)).continuousOn
      (s := Set.Icc (0:ℝ) T))
  refine ⟨L, M, L.2, fun n => ?_⟩
  induction n with
  | zero => intro t ht; simpa using hM t ht
  | succ n ih =>
    intro t ht
    have key : picardIter b σ w y₀ (n + 2) t - picardIter b σ w y₀ (n + 1) t =
        ∫ s in (0:ℝ)..t, (b (max s 0) (picardIter b σ w y₀ (n + 1) s) -
          b (max s 0) (picardIter b σ w y₀ n s)) := by
      have h1 := continuous_bpos_comp b hb (continuous_picardIter b hb σ hw y₀ (n + 1))
      have h2 := continuous_bpos_comp b hb (continuous_picardIter b hb σ hw y₀ n)
      rw [intervalIntegral.integral_sub (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _)]
      simp only [picardIter, max_eq_left ht.1]
      abel
    rw [key]
    refine norm_integral_le_pow n ht.1 fun r hr => ?_
    have hrT : r ∈ Set.Icc (0:ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
    rw [max_eq_left hr.1]
    have := (hL r hrT).dist_le_mul (picardIter b σ w y₀ (n + 1) r) (picardIter b σ w y₀ n r)
    rw [dist_eq_norm, dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_left (ih r hrT) L.2)


/-- The limit of the Picard iterates. -/
def picardLim (b : ℝ → E → E) (σ : ι → E) (w : ℝ≥0 → ι → ℝ) (y₀ : E) : ℝ → E :=
  fun t => limUnder atTop (fun n => picardIter b σ w y₀ n t)

theorem picardIter_eq_sum (b : ℝ → E → E) (σ : ι → E) (w : ℝ≥0 → ι → ℝ) (y₀ : E) (t : ℝ)
    (N : ℕ) : picardIter b σ w y₀ N t = picardIter b σ w y₀ 0 t +
      ∑ n ∈ Finset.range N, (picardIter b σ w y₀ (n + 1) t - picardIter b σ w y₀ n t) := by
  rw [Finset.sum_range_sub (fun n => picardIter b σ w y₀ n t) N]; abel

theorem tendstoUniformlyOn_picardIter_Icc (b : ℝ → E → E) (hb : IsLipschitzDrift b) (σ : ι → E)
    {w : ℝ≥0 → ι → ℝ} (hw : Continuous w) (y₀ : E) (T : ℝ) :
    TendstoUniformlyOn (picardIter b σ w y₀) (picardLim b σ w y₀) atTop (Set.Icc 0 T) := by
  obtain ⟨L, M, hL, hLM⟩ := picardIter_diff_le b hb σ hw y₀ T
  have hu : Summable fun n : ℕ => M * (L * T) ^ n / n.factorial := by
    simpa [mul_div_assoc] using (Real.summable_pow_div_factorial (L * T)).mul_left M
  have hfu : ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0:ℝ) T →
      ‖picardIter b σ w y₀ (n + 1) t - picardIter b σ w y₀ n t‖ ≤ M * (L * T) ^ n / n.factorial := by
    intro n t ht
    refine (hLM n t ht).trans ?_
    have hM : 0 ≤ M := by
      have := hLM 0 t ht
      simp at this
      exact (norm_nonneg _).trans this
    have : (L * t) ^ n ≤ (L * T) ^ n :=
      pow_le_pow_left₀ (mul_nonneg hL ht.1) (mul_le_mul_of_nonneg_left ht.2 hL) n
    gcongr
  have hlim : ∀ t ∈ Set.Icc (0:ℝ) T, picardLim b σ w y₀ t = picardIter b σ w y₀ 0 t +
      ∑' n, (picardIter b σ w y₀ (n + 1) t - picardIter b σ w y₀ n t) := by
    intro t ht
    have hs : Summable fun n : ℕ => picardIter b σ w y₀ (n + 1) t - picardIter b σ w y₀ n t :=
      Summable.of_norm_bounded hu (fun n => hfu n t ht)
    have := (hs.hasSum.tendsto_sum_nat.const_add (picardIter b σ w y₀ 0 t))
    refine Tendsto.limUnder_eq ?_
    refine this.congr fun N => ?_
    exact (picardIter_eq_sum b σ w y₀ t N).symm
  have h := tendstoUniformlyOn_tsum_nat hu hfu
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with N hN t ht
  have := hN t ht
  rw [hlim t ht, picardIter_eq_sum b σ w y₀ t N, dist_add_left]
  exact this


theorem picardLim_max (b : ℝ → E → E) (σ : ι → E) (w : ℝ≥0 → ι → ℝ) (y₀ : E) (t : ℝ) :
    picardLim b σ w y₀ t = picardLim b σ w y₀ (max t 0) := by
  unfold picardLim
  congr 1
  ext n
  exact picardIter_max b σ w y₀ n t

theorem tendstoUniformlyOn_picardIter_Iic (b : ℝ → E → E) (hb : IsLipschitzDrift b) (σ : ι → E)
    {w : ℝ≥0 → ι → ℝ} (hw : Continuous w) (y₀ : E) (T : ℝ) :
    TendstoUniformlyOn (picardIter b σ w y₀) (picardLim b σ w y₀) atTop (Set.Iic T) := by
  have h := tendstoUniformlyOn_picardIter_Icc b hb σ hw y₀ (max T 0)
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with N hN t ht
  have hmem : max t 0 ∈ Set.Icc (0:ℝ) (max T 0) :=
    ⟨le_max_right _ _, max_le_max ht le_rfl⟩
  have := hN _ hmem
  rwa [← picardLim_max, ← picardIter_max] at this

theorem continuous_picardLim (b : ℝ → E → E) (hb : IsLipschitzDrift b) (σ : ι → E)
    {w : ℝ≥0 → ι → ℝ} (hw : Continuous w) (y₀ : E) : Continuous (picardLim b σ w y₀) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact ((tendstoUniformlyOn_picardIter_Iic b hb σ hw y₀ (t + 1)).continuousOn
    (Frequently.of_forall fun n => (continuous_picardIter b hb σ hw y₀ n).continuousOn)).continuousAt
    (Iic_mem_nhds (lt_add_one t))

theorem tendsto_picardIter (b : ℝ → E → E) (hb : IsLipschitzDrift b) (σ : ι → E)
    {w : ℝ≥0 → ι → ℝ} (hw : Continuous w) (y₀ : E) (t : ℝ) :
    Tendsto (fun n => picardIter b σ w y₀ n t) atTop (𝓝 (picardLim b σ w y₀ t)) :=
  (tendstoUniformlyOn_picardIter_Iic b hb σ hw y₀ t).tendsto_at (Set.mem_Iic.2 le_rfl)

theorem picardLim_eq (b : ℝ → E → E) (hb : IsLipschitzDrift b) (σ : ι → E)
    {w : ℝ≥0 → ι → ℝ} (hw : Continuous w) (y₀ : E) (t : ℝ) :
    picardLim b σ w y₀ t = y₀ + (∫ s in (0:ℝ)..max t 0, b (max s 0) (picardLim b σ w y₀ s)) +
      addNoise σ w t := by
  have h1 : Tendsto (fun n => picardIter b σ w y₀ (n + 1) t) atTop (𝓝 (picardLim b σ w y₀ t)) :=
    (tendsto_picardIter b hb σ hw y₀ t).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => picardIter b σ w y₀ (n + 1) t) atTop
      (𝓝 (y₀ + (∫ s in (0:ℝ)..max t 0, b (max s 0) (picardLim b σ w y₀ s)) + addNoise σ w t)) := by
    refine Tendsto.add (Tendsto.const_add y₀ ?_) tendsto_const_nhds
    obtain ⟨L, hL⟩ := hb.lip (max t 0)
    have hu : TendstoUniformlyOn (fun n s => b (max s 0) (picardIter b σ w y₀ n s))
        (fun s => b (max s 0) (picardLim b σ w y₀ s)) atTop (Set.uIcc 0 (max t 0)) := by
      rw [Set.uIcc_of_le (le_max_right _ _)]
      have h := tendstoUniformlyOn_picardIter_Icc b hb σ hw y₀ (max t 0)
      rw [Metric.tendstoUniformlyOn_iff] at h ⊢
      intro ε hε
      filter_upwards [h (ε / (L + 1)) (by positivity)] with N hN s hs
      have := hN s hs
      have hLs := (hL (max s 0) ⟨le_max_right _ _, by rw [max_eq_left hs.1]; exact hs.2⟩).dist_le_mul
        (picardLim b σ w y₀ s) (picardIter b σ w y₀ N s)
      calc _ ≤ L * dist (picardLim b σ w y₀ s) (picardIter b σ w y₀ N s) := hLs
        _ ≤ L * (ε / (L + 1)) := by gcongr
        _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [hε, L.2]
    refine hu.tendsto_intervalIntegral_of_continuousOn (Eventually.of_forall fun n => ?_)
    exact (continuous_bpos_comp b hb (continuous_picardIter b hb σ hw y₀ n)).continuousOn
  exact tendsto_nhds_unique h1 h2


theorem isPathSolution_picardLim (b : ℝ → E → E) (hb : IsLipschitzDrift b) (σ : ι → E)
    {w : ℝ≥0 → ι → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) (y₀ : E) :
    IsPathSolution b σ w y₀ ⊤ (picardLim b σ w y₀) := by
  have hc := continuous_picardLim b hb σ hw y₀
  refine ⟨?_, fun t ht _ => ⟨hc.continuousOn, ?_, ?_⟩⟩
  · rw [picardLim_eq b hb σ hw y₀ 0]; simp [addNoise, hw0]
  · have h := continuous_bpos_comp b hb hc
    have he : Set.EqOn (fun s => b (max s 0) (picardLim b σ w y₀ s))
        (fun s => b s (picardLim b σ w y₀ s)) (Set.Icc 0 t) := fun s hs => by
      simp [max_eq_left hs.1]
    exact h.integrableOn_Icc.congr_fun he measurableSet_Icc
  · rw [picardLim_eq b hb σ hw y₀ t, max_eq_left ht, ← setIntegral_Icc_eq_interval ht]
    have : ∫ s in Set.Icc (0:ℝ) t, b (max s 0) (picardLim b σ w y₀ s) =
        ∫ s in Set.Icc (0:ℝ) t, b s (picardLim b σ w y₀ s) :=
      setIntegral_congr_fun measurableSet_Icc (fun s hs => by simp [max_eq_left hs.1])
    rw [this]; rfl

end PicardAux

section PathwiseMax

set_option linter.unusedSectionVars false

theorem IsPathSolution.mono {b : ℝ → E → E} {σ : ι → E} {w : ℝ≥0 → ι → ℝ} {y₀ : E}
    {τ τ' : WithTop ℝ} {y : ℝ → E} (h : IsPathSolution b σ w y₀ τ y) (hle : τ' ≤ τ) :
    IsPathSolution b σ w y₀ τ' y :=
  ⟨h.1, fun t ht htτ => h.2 t ht (lt_of_lt_of_le htτ hle)⟩

theorem IsPathSolution.congr_drift {b b' : ℝ → E → E} {σ : ι → E} {w : ℝ≥0 → ι → ℝ} {y₀ : E}
    {τ : WithTop ℝ} {y : ℝ → E} (h : IsPathSolution b σ w y₀ τ y)
    (hbb : ∀ s : ℝ, 0 ≤ s → (s : WithTop ℝ) < τ → b' s (y s) = b s (y s)) :
    IsPathSolution b' σ w y₀ τ y := by
  refine ⟨h.1, fun t ht htτ => ?_⟩
  obtain ⟨hc, hi, he⟩ := h.2 t ht htτ
  have hcongr : ∀ s ∈ Set.Icc (0:ℝ) t, b' s (y s) = b s (y s) := fun s hs =>
    hbb s hs.1 (lt_of_le_of_lt (by exact_mod_cast hs.2) htτ)
  refine ⟨hc, hi.congr_fun (fun s hs => (hcongr s hs).symm) measurableSet_Icc, ?_⟩
  rw [he]
  congr 2
  exact setIntegral_congr_fun measurableSet_Icc (fun s hs => (hcongr s hs).symm)

theorem IsLipschitzDrift.toLoc {b : ℝ → E → E} (hb : IsLipschitzDrift b) :
    IsLocLipschitzDrift Set.univ b where
  cont := hb.cont
  lip := fun K _ _ T => by
    obtain ⟨L, hL⟩ := hb.lip T
    exact ⟨L, fun t ht => (hL t ht).lipschitzOnWith⟩

/-- The exit time of a path from a set (first time in the complement after time `0`). -/
def pexit (V : Set E) (y : ℝ → E) : WithTop ℝ :=
  hittingAfter (fun t (_ : Unit) => y t) Vᶜ 0 ()

theorem exitTime_eq_pexit (X : ℝ → Ω → E) (V : Set E) (ω : Ω) :
    exitTime X V 0 ω = pexit V (fun t => X t ω) := rfl

theorem pexit_nonneg (V : Set E) (y : ℝ → E) : ((0:ℝ) : WithTop ℝ) ≤ pexit V y :=
  le_hittingAfter _

theorem mem_of_lt_pexit {V : Set E} {y : ℝ → E} {t : ℝ} (ht0 : 0 ≤ t)
    (ht : (t : WithTop ℝ) < pexit V y) : y t ∈ V := by
  have := notMem_of_lt_hittingAfter ht ht0
  simpa using this

theorem le_pexit_of_forall {V : Set E} {y : ℝ → E} {ρ : WithTop ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < ρ → y t ∈ V) : ρ ≤ pexit V y := by
  unfold pexit hittingAfter
  split_ifs with hex
  · induction ρ using WithTop.recTopCoe with
    | top =>
      exfalso
      obtain ⟨j, hj0, hjV⟩ := hex
      exact hjV (h j hj0 (WithTop.coe_lt_top j))
    | coe r =>
      refine WithTop.coe_le_coe.2 (le_csInf hex ?_)
      rintro i ⟨hi0, hiV⟩
      by_contra hlt
      rw [not_le] at hlt
      exact hiV (h i hi0 (WithTop.coe_lt_coe.2 hlt))
  · exact le_top

theorem lt_pexit_of_forall_Icc {V : Set E} (hV : IsOpen V) {y : ℝ → E} (hy : Continuous y)
    {T : ℝ} (h : ∀ s ∈ Set.Icc (0:ℝ) T, y s ∈ V) (hT : 0 ≤ T) :
    (T : WithTop ℝ) < pexit V y := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hV.preimage hy) T (h T ⟨hT, le_rfl⟩)
  refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 (by linarith : T < T + ε / 2)) ?_
  refine le_pexit_of_forall fun t ht0 htlt => ?_
  have htle : t < T + ε / 2 := WithTop.coe_lt_coe.1 htlt
  by_cases htT : t ≤ T
  · exact h t ⟨ht0, htT⟩
  · rw [not_le] at htT
    exact hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)

theorem pos_pexit {V : Set E} (hV : IsOpen V) {y : ℝ → E} (hy : Continuous y) (h0 : y 0 ∈ V) :
    (0 : WithTop ℝ) < pexit V y := by
  have := lt_pexit_of_forall_Icc hV hy (T := 0) (fun s hs => by
    have : s = 0 := le_antisymm hs.2 hs.1
    rw [this]; exact h0) le_rfl
  simpa using this


/-- Globally Lipschitz truncation of a locally Lipschitz drift: agrees with `b` on a given compact
set `K ⊆ U` (for nonnegative times). -/
theorem exists_trunc_drift (U : Set E) (hU : IsOpen U) (b : ℝ → E → E)
    (hb : IsLocLipschitzDrift U b) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ b' : ℝ → E → E, IsLipschitzDrift b' ∧ ∀ t : ℝ, 0 ≤ t → ∀ y ∈ K, b' t y = b t y := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · refine ⟨fun _ _ => 0, ⟨continuousOn_const, fun T => ⟨0, fun t _ => ?_⟩⟩, by simp⟩
    intro x y
    simp
  obtain ⟨δ, hδ, hCU⟩ := hK.exists_cthickening_subset_open hU hKU
  set C := Metric.cthickening δ K with hC
  have hCc : IsCompact C := hK.cthickening
  set χ : E → ℝ := fun y => max (1 - Metric.infDist y K / δ) 0 with hχ
  have hχ0 : ∀ y, 0 ≤ χ y := fun y => le_max_right _ _
  have hχ1 : ∀ y, χ y ≤ 1 := fun y => by
    refine max_le ?_ zero_le_one
    have : 0 ≤ Metric.infDist y K / δ := div_nonneg Metric.infDist_nonneg hδ.le
    linarith
  have hχK : ∀ y ∈ K, χ y = 1 := fun y hy => by
    simp [hχ, Metric.infDist_zero_of_mem hy]
  have hχC : ∀ y, y ∉ C → χ y = 0 := fun y hy => by
    have : ¬ Metric.infDist y K < δ := fun h =>
      hy (Metric.thickening_subset_cthickening δ K ((Metric.mem_thickening_iff_infDist_lt hne).2 h))
    push Not at this
    simp only [hχ]
    refine max_eq_right ?_
    have : 1 ≤ Metric.infDist y K / δ := by rw [le_div_iff₀ hδ]; linarith
    linarith
  have hχd : ∀ y z, |χ y - χ z| ≤ (1 / δ) * ‖y - z‖ := fun y z => by
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have h1 : |Metric.infDist y K - Metric.infDist z K| ≤ ‖y - z‖ := by
      have := (Metric.lipschitz_infDist_pt K).dist_le_mul y z
      simpa [Real.dist_eq, dist_eq_norm] using this
    have : (1 - Metric.infDist y K / δ) - (1 - Metric.infDist z K / δ) =
        -(Metric.infDist y K - Metric.infDist z K) / δ := by ring
    rw [this, abs_div, abs_neg, abs_of_pos hδ, one_div, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right h1 hδ.le
  have hχc : Continuous χ := by
    have : LipschitzWith (1 / δ).toNNReal χ := LipschitzWith.of_dist_le_mul fun y z => by
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
      exact hχd y z
    exact this.continuous
  refine ⟨fun t y => χ y • b (max t 0) y, ⟨?_, ?_⟩, fun t ht y hy => ?_⟩
  · -- continuity
    intro p _
    obtain ⟨t, y⟩ := p
    by_cases hy : y ∈ U
    · have hg : ContinuousOn (fun q : ℝ × E => b (max q.1 0) q.2) (Set.univ ×ˢ U) := by
        have h1 : ContinuousOn (fun q : ℝ × E => (max q.1 0, q.2)) (Set.univ ×ˢ U) :=
          (continuous_fst.max continuous_const).prodMk continuous_snd |>.continuousOn
        refine hb.cont.comp h1 ?_
        intro q hq
        exact ⟨Set.mem_Ici.2 (le_max_right _ _), hq.2⟩
      have hgat : ContinuousAt (fun q : ℝ × E => b (max q.1 0) q.2) (t, y) :=
        hg.continuousAt ((isOpen_univ.prod hU).mem_nhds ⟨trivial, hy⟩)
      exact (((hχc.comp continuous_snd).continuousAt).smul hgat).continuousWithinAt
    · have hyC : y ∉ C := fun h => hy (hCU h)
      have hev : ∀ᶠ q : ℝ × E in 𝓝 (t, y), q.2 ∉ C :=
        ((Metric.isClosed_cthickening (E := K) (δ := δ)).isOpen_compl.preimage continuous_snd).mem_nhds hyC
      have : ContinuousAt (fun q : ℝ × E => χ q.2 • b (max q.1 0) q.2) (t, y) := by
        refine (continuousAt_const (y := (0 : E))).congr ?_
        filter_upwards [hev] with q hq
        simp [hχC q.2 hq]
      exact this.continuousWithinAt
  · -- Lipschitz
    intro T
    obtain ⟨L₀, hL₀⟩ := hb.lip C hCc hCU T
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod hCc).exists_bound_of_continuousOn
      (hb.cont.mono (Set.prod_mono Set.Icc_subset_Ici_self hCU))
    set M' := max M 0 with hM'
    refine ⟨L₀ + Real.toNNReal (M' / δ), fun t ht => ?_⟩
    have hmax : max t 0 = t := max_eq_left ht.1
    have hbM : ∀ z ∈ C, ‖b t z‖ ≤ M' := fun z hz =>
      (hM (t, z) ⟨ht, hz⟩).trans (le_max_left _ _)
    have hM'0 : 0 ≤ M' := le_max_right _ _
    have key : ∀ y z, y ∈ C → ‖χ y • b t y - χ z • b t z‖ ≤ (L₀ + M' / δ) * ‖y - z‖ := by
      intro y z hy
      by_cases hz : z ∈ C
      · have h1 : χ y • b t y - χ z • b t z =
            χ y • (b t y - b t z) + (χ y - χ z) • b t z := by
          simp only [smul_sub, sub_smul]; abel
        rw [h1]
        refine (norm_add_le _ _).trans ?_
        have e1 : ‖χ y • (b t y - b t z)‖ ≤ L₀ * ‖y - z‖ := by
          rw [norm_smul, Real.norm_of_nonneg (hχ0 y)]
          have := (hL₀ t ht).dist_le_mul y hy z hz
          rw [dist_eq_norm, dist_eq_norm] at this
          calc χ y * ‖b t y - b t z‖ ≤ 1 * ‖b t y - b t z‖ :=
                mul_le_mul_of_nonneg_right (hχ1 y) (norm_nonneg _)
            _ ≤ L₀ * ‖y - z‖ := by simpa using this
        have e2 : ‖(χ y - χ z) • b t z‖ ≤ M' / δ * ‖y - z‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          calc |χ y - χ z| * ‖b t z‖ ≤ (1 / δ * ‖y - z‖) * M' :=
                mul_le_mul (hχd y z) (hbM z hz) (norm_nonneg _) (by positivity)
            _ = M' / δ * ‖y - z‖ := by ring
        calc _ ≤ L₀ * ‖y - z‖ + M' / δ * ‖y - z‖ := add_le_add e1 e2
          _ = _ := by ring
      · have h0 : χ z = 0 := hχC z hz
        rw [h0, zero_smul, sub_zero, norm_smul, Real.norm_of_nonneg (hχ0 y)]
        have hd := hχd y z
        rw [h0, sub_zero, abs_of_nonneg (hχ0 y)] at hd
        calc χ y * ‖b t y‖ ≤ (1 / δ * ‖y - z‖) * M' :=
              mul_le_mul hd (hbM y hy) (norm_nonneg _) (by positivity)
          _ = M' / δ * ‖y - z‖ := by ring
          _ ≤ (L₀ + M' / δ) * ‖y - z‖ := by
              have : (0:ℝ) ≤ L₀ := L₀.2
              nlinarith [norm_nonneg (y - z)]
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    simp only [hmax]
    rw [dist_eq_norm, dist_eq_norm]
    push_cast
    rw [Real.coe_toNNReal _ (by positivity)]
    by_cases hy : y ∈ C
    · exact key y z hy
    · by_cases hz : z ∈ C
      · rw [norm_sub_rev, norm_sub_rev y z]; exact key z y hz
      · rw [hχC y hy, hχC z hz]; simp only [zero_smul, sub_self, norm_zero]
        have : (0:ℝ) ≤ L₀ := L₀.2
        positivity
  · show χ y • b (max t 0) y = b t y
    rw [max_eq_left ht, hχK y hy, one_smul]


/-- An exhaustion of `U` by open sets `V m` and compacts `K m` with `V m ⊆ K m ⊆ V (m+1)`,
together with globally Lipschitz truncations `bt m` of the drift that agree with it on `K m`. -/
structure Exhaustion (U : Set E) (b : ℝ → E → E) where
  V : ℕ → Set E
  K : ℕ → Set E
  bt : ℕ → ℝ → E → E
  isOpen_V : ∀ m, IsOpen (V m)
  isCompact_K : ∀ m, IsCompact (K m)
  V_sub_K : ∀ m, V m ⊆ K m
  K_sub_V : ∀ m, K m ⊆ V (m + 1)
  K_sub_U : ∀ m, K m ⊆ U
  cover : ∀ x ∈ U, ∃ m, x ∈ V m
  lip : ∀ m, IsLipschitzDrift (bt m)
  eq : ∀ m, ∀ t : ℝ, 0 ≤ t → ∀ y ∈ K m, bt m t y = b t y

theorem exists_exhaustion (U : Set E) (hU : IsOpen U) (b : ℝ → E → E)
    (hb : IsLocLipschitzDrift U b) : Nonempty (Exhaustion U b) := by
  let V : ℕ → Set E := fun n => {x | ‖x‖ < n + 1} ∩
    {x | ((n : ℝ≥0∞) + 1)⁻¹ < Metric.infEDist x Uᶜ}
  let K : ℕ → Set E := fun n => Metric.closedBall (0 : E) (n + 1) ∩
    {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ Metric.infEDist x Uᶜ}
  have hVo : ∀ n, IsOpen (V n) := fun n =>
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const Metric.continuous_infEDist)
  have hKc : ∀ n, IsCompact (K n) := fun n =>
    Metric.isCompact_of_isClosed_isBounded
      (Metric.isClosed_closedBall.inter (isClosed_le continuous_const Metric.continuous_infEDist))
      (Metric.isBounded_closedBall.subset Set.inter_subset_left)
  have hVK : ∀ n, V n ⊆ K n := fun n x hx =>
    ⟨mem_closedBall_zero_iff.2 hx.1.le, show ((n : ℝ≥0∞) + 1)⁻¹ ≤ Metric.infEDist x Uᶜ from le_of_lt hx.2⟩
  have hinv : ∀ n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := fun n =>
    ENNReal.inv_ne_zero.2 (by simp)
  have hKV : ∀ n, K n ⊆ V (n + 1) := fun n x hx => by
    refine ⟨?_, ?_⟩
    · have := mem_closedBall_zero_iff.1 hx.1
      show ‖x‖ < ((n + 1 : ℕ) : ℝ) + 1
      push_cast
      linarith
    · refine lt_of_lt_of_le ?_
        (show ((n : ℝ≥0∞) + 1)⁻¹ ≤ Metric.infEDist x Uᶜ from hx.2)
      refine ENNReal.inv_lt_inv.2 ?_
      push_cast
      exact ENNReal.lt_add_right (by simp) one_ne_zero
  have hKU : ∀ n, K n ⊆ U := fun n x hx => by
    by_contra hxU
    have := Metric.infEDist_zero_of_mem (s := Uᶜ) hxU
    have h2 := hx.2
    have h3 : ((n : ℝ≥0∞) + 1)⁻¹ ≤ 0 := this ▸ h2
    exact hinv n (nonpos_iff_eq_zero.1 h3)
  have hcover : ∀ x ∈ U, ∃ n, x ∈ V n := by
    intro x hx
    have hpos : Metric.infEDist x Uᶜ ≠ 0 := by
      have : 0 < Metric.infEDist x Uᶜ := by
        rw [Metric.infEDist_pos_iff_notMem_closure, hU.isClosed_compl.closure_eq]
        simpa using hx
      exact this.ne'
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hpos
    obtain ⟨m, hm⟩ := exists_nat_gt ‖x‖
    refine ⟨max n m, ?_, ?_⟩
    · show ‖x‖ < ((max n m : ℕ) : ℝ) + 1
      have : (m : ℝ) ≤ ((max n m : ℕ) : ℝ) := by exact_mod_cast le_max_right n m
      linarith
    · refine lt_of_le_of_lt ?_ hn
      refine ENNReal.inv_le_inv.2 ?_
      have : (n : ℝ≥0∞) ≤ ((max n m : ℕ) : ℝ≥0∞) := by exact_mod_cast le_max_left n m
      exact this.trans le_self_add
  choose bt hbt heq using fun n => exists_trunc_drift U hU b hb (hKc n) (hKU n)
  exact ⟨⟨V, K, bt, hVo, hKc, hVK, hKV, hKU, hcover, hbt, heq⟩⟩


theorem Exhaustion.monotone_V {U : Set E} {b : ℝ → E → E} (X : Exhaustion U b) : Monotone X.V :=
  monotone_nat_of_le_succ fun m => (X.V_sub_K m).trans (X.K_sub_V m)

theorem Exhaustion.monotone_K {U : Set E} {b : ℝ → E → E} (X : Exhaustion U b) : Monotone X.K :=
  monotone_nat_of_le_succ fun m => (X.K_sub_V m).trans (X.V_sub_K (m + 1))

section PathMax

variable {U : Set E} {b : ℝ → E → E}

/-- Data for the pathwise pasting: global solutions `ym m` of the truncated problems. -/
structure PathData (X : Exhaustion U b) (σ : ι → E) (w : ℝ≥0 → ι → ℝ) (y₀ : E)
    (ym : ℕ → ℝ → E) : Prop where
  contw : Continuous w
  sol : ∀ m, IsPathSolution (X.bt m) σ w y₀ ⊤ (ym m)
  cont : ∀ m, Continuous (ym m)
  neg : ∀ m, ∀ t : ℝ, t ≤ 0 → ym m t = y₀

/-- Lifetime of the pasted solution. -/
def lifetime (X : Exhaustion U b) (ym : ℕ → ℝ → E) : WithTop ℝ := ⨆ m, pexit (X.V m) (ym m)

open Classical in
/-- The pasted solution. -/
def pathY (X : Exhaustion U b) (ym : ℕ → ℝ → E) (y₀ : E) (t : ℝ) : E :=
  if h : ∃ m, (t : WithTop ℝ) < pexit (X.V m) (ym m) then ym (Nat.find h) t else y₀

variable {X : Exhaustion U b} {σ : ι → E} {w : ℝ≥0 → ι → ℝ} {y₀ : E} {ym : ℕ → ℝ → E}

theorem PathData.unique (hD : PathData X σ w y₀ ym) (m' : ℕ) {τ : WithTop ℝ} {y : ℝ → E}
    (hy : IsPathSolution (X.bt m') σ w y₀ τ y) :
    ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ → y t = ym m' t := fun t ht htτ =>
  ode_additive_unique Set.univ isOpen_univ (X.bt m') (X.lip m').toLoc σ w hD.contw y₀ hy
    (hD.sol m') (fun _ _ _ => Set.mem_univ _) (fun _ _ _ => Set.mem_univ _) t ht
    (by simpa using htτ)

theorem PathData.ym_eq (hD : PathData X σ w y₀ ym) {m m' : ℕ} (hmm : m ≤ m') {t : ℝ}
    (ht : 0 ≤ t) (htlt : (t : WithTop ℝ) < pexit (X.V m) (ym m)) : ym m t = ym m' t := by
  have h1 : IsPathSolution (X.bt m') σ w y₀ (pexit (X.V m) (ym m)) (ym m) := by
    refine ((hD.sol m).mono le_top).congr_drift fun s hs hslt => ?_
    have hV := mem_of_lt_pexit hs hslt
    rw [X.eq m' s hs _ (X.monotone_K hmm (X.V_sub_K m hV)), X.eq m s hs _ (X.V_sub_K m hV)]
  exact hD.unique m' h1 t ht htlt

theorem PathData.pexit_mono (hD : PathData X σ w y₀ ym) {m m' : ℕ} (hmm : m ≤ m') :
    pexit (X.V m) (ym m) ≤ pexit (X.V m') (ym m') := by
  refine le_pexit_of_forall fun t ht htlt => ?_
  rw [← hD.ym_eq hmm ht htlt]
  exact X.monotone_V hmm (mem_of_lt_pexit ht htlt)

theorem pathY_of_nonpos (hD : PathData X σ w y₀ ym) {t : ℝ} (ht : t ≤ 0) :
    pathY X ym y₀ t = y₀ := by
  unfold pathY
  split_ifs with h
  · exact hD.neg _ t ht
  · rfl

theorem pathY_eq (hD : PathData X σ w y₀ ym) {m : ℕ} {t : ℝ}
    (h : (t : WithTop ℝ) < pexit (X.V m) (ym m)) : pathY X ym y₀ t = ym m t := by
  have hex : ∃ m, (t : WithTop ℝ) < pexit (X.V m) (ym m) := ⟨m, h⟩
  unfold pathY
  simp only [hex, ↓reduceDIte]
  have hf := Nat.find_spec hex
  rcases le_or_gt t 0 with ht | ht
  · rw [hD.neg _ t ht, hD.neg _ t ht]
  · rw [hD.ym_eq (le_max_left (Nat.find hex) m) ht.le hf,
      hD.ym_eq (le_max_right (Nat.find hex) m) ht.le h]

theorem pathY_of_not {t : ℝ} (h : ¬ ∃ m, (t : WithTop ℝ) < pexit (X.V m) (ym m)) :
    pathY X ym y₀ t = y₀ := by
  unfold pathY
  simp only [h, ↓reduceDIte]

theorem pexit_le_lifetime (m : ℕ) : pexit (X.V m) (ym m) ≤ lifetime X ym :=
  le_ciSup (OrderTop.bddAbove (Set.range fun m => pexit (X.V m) (ym m))) m

theorem lt_lifetime_iff {t : ℝ} :
    (t : WithTop ℝ) < lifetime X ym ↔ ∃ m, (t : WithTop ℝ) < pexit (X.V m) (ym m) :=
  lt_ciSup_iff (OrderTop.bddAbove (Set.range fun m => pexit (X.V m) (ym m)))

theorem lifetime_nonneg : ((0:ℝ) : WithTop ℝ) ≤ lifetime X ym :=
  (pexit_nonneg _ _).trans (pexit_le_lifetime 0)

theorem PathData.lifetime_pos (hD : PathData X σ w y₀ ym) (hy₀ : y₀ ∈ U) :
    (0 : WithTop ℝ) < lifetime X ym := by
  obtain ⟨m, hm⟩ := X.cover y₀ hy₀
  refine lt_of_lt_of_le ?_ (pexit_le_lifetime m)
  exact pos_pexit (X.isOpen_V m) (hD.cont m) (by rw [hD.neg m 0 le_rfl]; exact hm)

theorem PathData.isPathSolution_pathY (hD : PathData X σ w y₀ ym) :
    IsPathSolution b σ w y₀ (lifetime X ym) (pathY X ym y₀) := by
  refine ⟨pathY_of_nonpos hD le_rfl, fun t ht htτ => ?_⟩
  obtain ⟨m, hm⟩ := lt_lifetime_iff.1 htτ
  have hmsol : IsPathSolution b σ w y₀ (pexit (X.V m) (ym m)) (ym m) := by
    refine ((hD.sol m).mono le_top).congr_drift fun s hs hslt => ?_
    exact (X.eq m s hs _ (X.V_sub_K m (mem_of_lt_pexit hs hslt))).symm
  obtain ⟨hc, hi, he⟩ := hmsol.2 t ht hm
  have hpe : ∀ s ∈ Set.Icc (0:ℝ) t, pathY X ym y₀ s = ym m s := fun s hs =>
    pathY_eq hD (lt_of_le_of_lt (by exact_mod_cast hs.2) hm)
  refine ⟨hc.congr hpe, hi.congr_fun (fun s hs => by rw [hpe s hs]) measurableSet_Icc, ?_⟩
  rw [pathY_eq hD hm, he]
  congr 2
  exact setIntegral_congr_fun measurableSet_Icc (fun s hs => by simp only [hpe s hs])

theorem PathData.pathY_mem (hD : PathData X σ w y₀ ym) {t : ℝ} (ht : 0 ≤ t)
    (htτ : (t : WithTop ℝ) < lifetime X ym) : pathY X ym y₀ t ∈ U := by
  obtain ⟨m, hm⟩ := lt_lifetime_iff.1 htτ
  rw [pathY_eq hD hm]
  exact X.K_sub_U m (X.V_sub_K m (mem_of_lt_pexit ht hm))

theorem PathData.key_eq (hD : PathData X σ w y₀ ym) (j : ℕ) {T : ℝ} {yb : ℝ → E}
    (hyb : IsPathSolution b σ w y₀ (T : WithTop ℝ) yb)
    (hVs : ∀ s : ℝ, 0 ≤ s → s < T → yb s ∈ X.V j) :
    ∀ s : ℝ, 0 ≤ s → s < T → ym j s = yb s := by
  have h1 : IsPathSolution (X.bt j) σ w y₀ (T : WithTop ℝ) yb :=
    hyb.congr_drift fun s hs hslt =>
      X.eq j s hs _ (X.V_sub_K j (hVs s hs (WithTop.coe_lt_coe.1 hslt)))
  intro s hs hsT
  exact (hD.unique j h1 s hs (WithTop.coe_lt_coe.2 hsT)).symm

theorem mem_of_forall_lt_of_isClosed {f : ℝ → E} (hf : Continuous f) {C : Set E}
    (hC : IsClosed C) {T : ℝ} (hT : 0 < T) (h : ∀ s : ℝ, 0 ≤ s → s < T → f s ∈ C) : f T ∈ C := by
  refine hC.mem_of_tendsto (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (b := 𝓝[<] T) ?_
  filter_upwards [Ioo_mem_nhdsLT hT] with s hs using h s hs.1.le hs.2

/-- A solution of the original problem staying in a closed subset `C` of `V j` up to time `T`
cannot exist if `T` is the lifetime of the pasted solution. -/
theorem PathData.false_of_closed (hD : PathData X σ w y₀ ym) {T : ℝ} (hT : 0 < T)
    (hlife : lifetime X ym = (T : WithTop ℝ)) {j : ℕ} {C : Set E} (hC : IsClosed C)
    (hCV : C ⊆ X.V j) {yb : ℝ → E} (hyb : IsPathSolution b σ w y₀ (T : WithTop ℝ) yb)
    (hVs : ∀ s : ℝ, 0 ≤ s → s < T → yb s ∈ C) : False := by
  have hk := hD.key_eq j hyb (fun s hs hsT => hCV (hVs s hs hsT))
  have hT' : ym j T ∈ C := mem_of_forall_lt_of_isClosed (hD.cont j) hC hT fun s hs hsT => by
    rw [hk s hs hsT]; exact hVs s hs hsT
  have : (T : WithTop ℝ) < pexit (X.V j) (ym j) := by
    refine lt_pexit_of_forall_Icc (X.isOpen_V j) (hD.cont j) (fun s hs => ?_) hT.le
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · rw [hk s hs.1 hlt]; exact hCV (hVs s hs.1 hlt)
    · rw [heq]; exact hCV hT'
  have h2 := this.trans_le (hlife ▸ pexit_le_lifetime j : pexit (X.V j) (ym j) ≤ (T : WithTop ℝ))
  exact lt_irrefl _ h2

theorem PathData.exit_alt (hD : PathData X σ w y₀ ym) (hy₀ : y₀ ∈ U) (hlt : lifetime X ym < ⊤) :
    ∀ K : Set E, IsCompact K → K ⊆ U → ∀ t₀ : ℝ, (t₀ : WithTop ℝ) < lifetime X ym →
      ∃ t : ℝ, t₀ < t ∧ (t : WithTop ℝ) < lifetime X ym ∧ pathY X ym y₀ t ∉ K := by
  intro K hK hKU t₀ ht₀
  obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.1 hlt.ne
  replace hT : lifetime X ym = (T : WithTop ℝ) := hT.symm
  have hTpos : 0 < T := by
    have := hD.lifetime_pos hy₀
    rw [hT] at this
    exact_mod_cast this
  have hsol := hD.isPathSolution_pathY
  rw [hT] at hsol
  by_contra hcon
  have hcon' : ∀ t : ℝ, t₀ < t → t < T → pathY X ym y₀ t ∈ K := by
    intro t h1 h2
    by_contra hnot
    exact hcon ⟨t, h1, by rw [hT]; exact WithTop.coe_lt_coe.2 h2, hnot⟩
  have ht₀T : t₀ < T := by rw [hT] at ht₀; exact_mod_cast ht₀
  set t₁ := max t₀ 0 with ht₁
  have ht₁T : t₁ < T := max_lt ht₀T hTpos
  have hcont : ContinuousOn (pathY X ym y₀) (Set.Icc 0 t₁) :=
    (hsol.2 t₁ (le_max_right _ _) (WithTop.coe_lt_coe.2 ht₁T)).1
  set Kp : Set E := K ∪ pathY X ym y₀ '' Set.Icc 0 t₁ with hKp
  have hKpc : IsCompact Kp := hK.union (isCompact_Icc.image_of_continuousOn hcont)
  have hKpU : Kp ⊆ U := by
    rintro _ (hx | ⟨s, hs, rfl⟩)
    · exact hKU hx
    · exact hD.pathY_mem hs.1 (by rw [hT]; exact WithTop.coe_lt_coe.2 (hs.2.trans_lt ht₁T))
  obtain ⟨j, hj⟩ := hKpc.elim_directed_cover X.V X.isOpen_V
    (fun x hx => Set.mem_iUnion.2 (X.cover x (hKpU hx))) X.monotone_V.directed_le
  refine hD.false_of_closed hTpos hT hKpc.isClosed hj hsol fun s hs hsT => ?_
  rcases le_or_gt s t₁ with h | h
  · exact Or.inr ⟨s, ⟨hs, h⟩, rfl⟩
  · exact Or.inl (hcon' s (lt_of_le_of_lt (le_max_left _ _) h) hsT)

theorem PathData.maximal (hD : PathData X σ w y₀ ym) (hy₀ : y₀ ∈ U) {τ' : WithTop ℝ}
    {y' : ℝ → E} (hy' : IsPathSolution b σ w y₀ τ' y')
    (hU' : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ' → y' t ∈ U) : τ' ≤ lifetime X ym := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.1 (hcon.trans_le le_top).ne
  replace hT : lifetime X ym = (T : WithTop ℝ) := hT.symm
  have hTpos : 0 < T := by
    have := hD.lifetime_pos hy₀
    rw [hT] at this
    exact_mod_cast this
  have hTτ : (T : WithTop ℝ) < τ' := hT ▸ hcon
  have hcont : ContinuousOn y' (Set.Icc 0 T) := (hy'.2 T hTpos.le hTτ).1
  have hKc : IsCompact (y' '' Set.Icc 0 T) := isCompact_Icc.image_of_continuousOn hcont
  have hKU : y' '' Set.Icc 0 T ⊆ U := by
    rintro _ ⟨s, hs, rfl⟩
    exact hU' s hs.1 (lt_of_le_of_lt (by exact_mod_cast hs.2) hTτ)
  obtain ⟨j, hj⟩ := hKc.elim_directed_cover X.V X.isOpen_V
    (fun x hx => Set.mem_iUnion.2 (X.cover x (hKU hx))) X.monotone_V.directed_le
  exact hD.false_of_closed hTpos hT hKc.isClosed hj (hy'.mono hTτ.le) fun s hs hsT =>
    ⟨s, ⟨hs, hsT.le⟩, rfl⟩

end PathMax


theorem picardLim_of_nonpos (b : ℝ → E → E) (hb : IsLipschitzDrift b) (σ : ι → E)
    {w : ℝ≥0 → ι → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) (y₀ : E) {t : ℝ} (ht : t ≤ 0) :
    picardLim b σ w y₀ t = y₀ := by
  rw [picardLim_eq b hb σ hw y₀ t, max_eq_right ht]
  simp [addNoise, Real.toNNReal_of_nonpos ht, hw0]

/-- Pathwise global existence for `w 0 = 0` (the hypothesis `w 0 = 0` is necessary for
`IsPathSolution`, since the equation at `t = 0` reads `y₀ = y₀ + ∑ w⁰_k σ_k`). -/
theorem exists_ode_additive_global_of_zero (b : ℝ → E → E) (hb : IsLipschitzDrift b) (σ : ι → E)
    (w : ℝ≥0 → ι → ℝ) (hw : Continuous w) (hw0 : w 0 = 0) (y₀ : E) :
    ∃ y : ℝ → E, IsPathSolution b σ w y₀ ⊤ y :=
  ⟨_, isPathSolution_picardLim b hb σ hw hw0 y₀⟩

theorem PathData.of_picardLim {U : Set E} {b : ℝ → E → E} (X : Exhaustion U b) (σ : ι → E) {w : ℝ≥0 → ι → ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) (y₀ : E) :
    PathData X σ w y₀ (fun m => picardLim (X.bt m) σ w y₀) :=
  ⟨hw, fun m => isPathSolution_picardLim (X.bt m) (X.lip m) σ hw hw0 y₀,
    fun m => continuous_picardLim (X.bt m) (X.lip m) σ hw y₀,
    fun m _ ht => picardLim_of_nonpos (X.bt m) (X.lip m) σ hw hw0 y₀ ht⟩

/-- **Pathwise maximal existence** for `w 0 = 0`. -/
theorem exists_ode_additive_maximal_of_zero (U : Set E) (hU : IsOpen U) (b : ℝ → E → E)
    (hb : IsLocLipschitzDrift U b) (σ : ι → E) (w : ℝ≥0 → ι → ℝ) (hw : Continuous w)
    (hw0 : w 0 = 0) (y₀ : E) (hy₀ : y₀ ∈ U) :
    ∃ (τ : WithTop ℝ) (y : ℝ → E), 0 < τ ∧ IsPathSolution b σ w y₀ τ y ∧
      (∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ → y t ∈ U) ∧
      (τ < ⊤ → ∀ K : Set E, IsCompact K → K ⊆ U →
        ∀ t₀ : ℝ, (t₀ : WithTop ℝ) < τ → ∃ t : ℝ, t₀ < t ∧ (t : WithTop ℝ) < τ ∧ y t ∉ K) ∧
      (∀ (τ' : WithTop ℝ) (y' : ℝ → E), IsPathSolution b σ w y₀ τ' y' →
        (∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ' → y' t ∈ U) → τ' ≤ τ) := by
  obtain ⟨X⟩ := exists_exhaustion U hU b hb
  have hD := PathData.of_picardLim X σ hw hw0 y₀
  exact ⟨_, _, hD.lifetime_pos hy₀, hD.isPathSolution_pathY, fun t ht htτ => hD.pathY_mem ht htτ,
    hD.exit_alt hy₀, fun τ' y' hy' hU' => hD.maximal hy₀ hy' hU'⟩

end PathwiseMax

/-- **Pathwise maximal existence**: for a continuous noise path and `y₀ ∈ U`, there is a maximal
pathwise solution on `[0, τ)` with values in `U`, which leaves every compact subset of `U` as
`t ↑ τ` when `τ < ∞` (explosion / exit alternative, M L11733-11735).  The noise path must start at
`0` (`w 0 = 0`; the equation at `t = 0` reads `y₀ = y₀ + ∑ w⁰_k σ_k`); Brownian paths do. -/
theorem exists_ode_additive_maximal (U : Set E) (hU : IsOpen U) (b : ℝ → E → E)
    (hb : IsLocLipschitzDrift U b) (σ : ι → E) (w : ℝ≥0 → ι → ℝ) (hw : Continuous w)
    (hw0 : w 0 = 0) (y₀ : E) (hy₀ : y₀ ∈ U) :
    ∃ (τ : WithTop ℝ) (y : ℝ → E), 0 < τ ∧ IsPathSolution b σ w y₀ τ y ∧
      (∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ → y t ∈ U) ∧
      (τ < ⊤ → ∀ K : Set E, IsCompact K → K ⊆ U →
        ∀ t₀ : ℝ, (t₀ : WithTop ℝ) < τ → ∃ t : ℝ, t₀ < t ∧ (t : WithTop ℝ) < τ ∧ y t ∉ K) ∧
      (∀ (τ' : WithTop ℝ) (y' : ℝ → E), IsPathSolution b σ w y₀ τ' y' →
        (∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ' → y' t ∈ U) → τ' ≤ τ) :=
  exists_ode_additive_maximal_of_zero U hU b hb σ w hw hw0 y₀ hy₀

/-- Globally Lipschitz drifts give global pathwise solutions (noise path starting at `0`). -/
theorem exists_ode_additive_global (b : ℝ → E → E) (hb : IsLipschitzDrift b) (σ : ι → E)
    (w : ℝ≥0 → ι → ℝ) (hw : Continuous w) (hw0 : w 0 = 0) (y₀ : E) :
    ∃ y : ℝ → E, IsPathSolution b σ w y₀ ⊤ y :=
  exists_ode_additive_global_of_zero b hb σ w hw hw0 y₀

/-! ### Strong solutions -/

/-- A strong solution of `dY = b(t, Y) dt + ∑_k σ_k dW^k`, `Y_0 = Y₀`, on `[0, τ)`: adapted, with
continuous paths before `τ`, satisfying the integrated equation a.s. for all `0 ≤ t < τ`. -/
structure IsAdditiveSDESolution (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (b : ℝ → E → E) (σ : ι → E) (Y₀ : Ω → E) (τ : Ω → WithTop ℝ) (Y : ℝ → Ω → E) : Prop where
  adapted : Adapted ℱ Y
  init : ∀ ω, Y 0 ω = Y₀ ω
  cont : ∀ ω, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ ω → ContinuousOn (fun s => Y s ω) (Set.Icc 0 t)
  eq : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ ω →
    IntegrableOn (fun s => b s (Y s ω)) (Set.Icc 0 t) ∧
    Y t ω = Y₀ ω + (∫ s in Set.Icc 0 t, b s (Y s ω)) + ∑ k, ofNNRealTime W t ω k • σ k

section Strong

set_option linter.unusedSectionVars false

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}

/-- A strong solution is, for a.e. `ω`, a pathwise solution driven by the path `W · ω`. -/
theorem IsAdditiveSDESolution.isPathSolution {b : ℝ → E → E} {σ : ι → E} {Y₀ : Ω → E}
    {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → E} (hY : IsAdditiveSDESolution P ℱ W b σ Y₀ τ Y) :
    ∀ᵐ ω ∂P, IsPathSolution b σ (fun t => W t ω) (Y₀ ω) (τ ω) (fun t => Y t ω) := by
  filter_upwards [hY.eq] with ω hω
  exact ⟨hY.init ω, fun t ht htτ => ⟨hY.cont ω t ht htτ, (hω t ht htτ).1, (hω t ht htτ).2⟩⟩

/-- **Pathwise uniqueness** of strong solutions with values in `U`. -/
theorem sde_pathwise_unique [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (U : Set E) (hU : IsOpen U) (b : ℝ → E → E) (hb : IsLocLipschitzDrift U b) (σ : ι → E)
    (Y₀ : Ω → E) {τ τ' : Ω → WithTop ℝ} {Y Y' : ℝ → Ω → E}
    (hY : IsAdditiveSDESolution P ℱ W b σ Y₀ τ Y) (hY' : IsAdditiveSDESolution P ℱ W b σ Y₀ τ' Y')
    (hYU : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ ω → Y t ω ∈ U)
    (hY'U : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ' ω → Y' t ω ∈ U) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < min (τ ω) (τ' ω) → Y t ω = Y' t ω := by
  filter_upwards [hY.isPathSolution, hY'.isPathSolution, hYU, hY'U] with ω h1 h2 h3 h4
  intro t ht htlt
  exact ode_additive_unique U hU b hb σ (fun s => W s ω) (hW.cont ω) (Y₀ ω) h1 h2 h3 h4 t ht htlt

theorem measurable_intervalIntegral_of_continuous {Ω' : Type*} {m : MeasurableSpace Ω'}
    (G : ℝ → Ω' → E) (hG : ∀ s, Measurable (G s)) (hc : ∀ ω, Continuous fun s => G s ω)
    {t : ℝ} (ht : 0 ≤ t) : Measurable fun ω => ∫ s in (0:ℝ)..t, G s ω := by
  have hj : Measurable (Function.uncurry G) :=
    measurable_uncurry_of_continuous_of_measurable hc hG
  have h := (StronglyMeasurable.integral_prod_left
    (μ := volume.restrict (Set.Ioc (0:ℝ) t)) hj.stronglyMeasurable).measurable
  have : (fun ω => ∫ s in (0:ℝ)..t, G s ω) = fun ω => ∫ s, G s ω ∂(volume.restrict (Set.Ioc 0 t)) := by
    ext ω; exact intervalIntegral.integral_of_le ht
  rw [this]; exact h

theorem measurable_of_cover {Ω' : Type*} {m : MeasurableSpace Ω'} (A : ℕ → Set Ω')
    (hA : ∀ n, MeasurableSet (A n)) (f : ℕ → Ω' → E) (hf : ∀ n, Measurable (f n))
    (g₀ g : Ω' → E) (hg₀ : Measurable g₀) (hg : ∀ n ω, ω ∈ A n → g ω = f n ω)
    (hg0 : ∀ ω, (∀ n, ω ∉ A n) → g ω = g₀ ω) : Measurable g := by
  refine measurable_of_isOpen fun S hS => ?_
  have : g ⁻¹' S = (⋃ n, A n ∩ f n ⁻¹' S) ∪ ((⋃ n, A n)ᶜ ∩ g₀ ⁻¹' S) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_compl_iff]
    constructor
    · intro h
      by_cases hex : ∃ n, ω ∈ A n
      · obtain ⟨n, hn⟩ := hex
        left
        exact ⟨n, hn, by rwa [← hg n ω hn]⟩
      · right
        have hex' : ∀ n, ω ∉ A n := fun n hn => hex ⟨n, hn⟩
        exact ⟨hex, by rwa [← hg0 ω hex']⟩
    · rintro (⟨n, hn, h⟩ | ⟨hn, h⟩)
      · rwa [hg n ω hn]
      · have : ∀ n, ω ∉ A n := fun n h' => hn ⟨n, h'⟩
        rwa [hg0 ω this]
  rw [this]
  exact (MeasurableSet.iUnion fun n => (hA n).inter (hf n hS.measurableSet)).union
    ((MeasurableSet.iUnion hA).compl.inter (hg₀ hS.measurableSet))

theorem measurable_addNoise (hW : IsBrownianFiltration P ℱ W) (σ : ι → E) (t : ℝ) :
    Measurable[ℱ t] (fun ω => addNoise σ (fun s => W s ω) t) := by
  rcases le_or_gt t 0 with ht | ht
  · have : (fun ω => addNoise σ (fun s => W s ω) t) = fun _ => 0 := by
      ext ω; simp [addNoise, Real.toNNReal_of_nonpos ht, hW.zero]
    rw [this]; exact measurable_const
  · unfold addNoise
    refine Finset.measurable_sum _ fun k _ => ?_
    have h := hW.adapted (Real.toNNReal t)
    rw [Real.coe_toNNReal t ht.le] at h
    exact ((measurable_pi_apply k).comp h).smul_const (σ k)

theorem IsLipschitzDrift.continuous_slice {b : ℝ → E → E} (hb : IsLipschitzDrift b) (s : ℝ) :
    Continuous (b (max s 0)) :=
  hb.cont.comp_continuous (Continuous.prodMk continuous_const continuous_id)
    (fun _ => ⟨Set.mem_Ici.2 (le_max_right _ _), Set.mem_univ _⟩)

theorem measurable_picardIter (hW : IsBrownianFiltration P ℱ W) (bt : ℝ → E → E)
    (hbt : IsLipschitzDrift bt) (σ : ι → E) {Y₀ : Ω → E} (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀)
    (n : ℕ) :
    ∀ t : ℝ, Measurable[ℱ t] (fun ω => picardIter bt σ (fun s => W s ω) (Y₀ ω) n t) := by
  induction n with
  | zero =>
    intro t
    simp only [picardIter]
    exact (hY₀ t).add (measurable_addNoise hW σ t)
  | succ n ih =>
    intro t
    simp only [picardIter]
    refine ((hY₀ t).add ?_).add (measurable_addNoise hW σ t)
    rcases le_or_gt t 0 with ht | ht
    · have : ∀ ω, ∫ s in (0:ℝ)..max t 0, bt (max s 0)
          (picardIter bt σ (fun s => W s ω) (Y₀ ω) n s) = 0 := by
        intro ω; rw [max_eq_right ht]; simp
      simp only [this]; exact measurable_const
    · let G : ℝ → Ω → E := fun s ω =>
        bt (max s 0) (picardIter bt σ (fun r => W r ω) (Y₀ ω) n (min s t))
      have hG : ∀ s, Measurable[ℱ t] (G s) := fun s =>
        (hbt.continuous_slice s).measurable.comp
          (Measurable.mono (ih (min s t)) (ℱ.mono (min_le_right s t)) le_rfl)
      have hc : ∀ ω, Continuous fun s => G s ω := fun ω =>
        continuous_bpos_comp bt hbt
          ((continuous_picardIter bt hbt σ (hW.cont ω) (Y₀ ω) n).comp
            (continuous_id.min continuous_const))
      have h := measurable_intervalIntegral_of_continuous (m := ℱ t) G hG hc ht.le
      have e : (fun ω => ∫ s in (0:ℝ)..max t 0, bt (max s 0)
          (picardIter bt σ (fun s => W s ω) (Y₀ ω) n s)) =
          fun ω => ∫ s in (0:ℝ)..t, G s ω := by
        ext ω
        rw [max_eq_left ht.le]
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [Set.uIcc_of_le ht.le] at hs
        simp only [G, min_eq_left hs.2]
      rw [e]; exact h

theorem measurable_picardLim (hW : IsBrownianFiltration P ℱ W) (bt : ℝ → E → E)
    (hbt : IsLipschitzDrift bt) (σ : ι → E) {Y₀ : Ω → E} (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀)
    (t : ℝ) : Measurable[ℱ t] (fun ω => picardLim bt σ (fun s => W s ω) (Y₀ ω) t) := by
  let _ : MeasurableSpace Ω := ℱ t
  exact measurable_of_tendsto_metrizable (fun n => measurable_picardIter hW bt hbt σ hY₀ n t)
    (tendsto_pi_nhds.2 fun ω => tendsto_picardIter bt hbt σ (hW.cont ω) (Y₀ ω) t)

theorem exists_sde_solution_global_exists (hW : IsBrownianFiltration P ℱ W) (b : ℝ → E → E)
    (hb : IsLipschitzDrift b) (σ : ι → E) {Y₀ : Ω → E} (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) :
    ∃ Y : ℝ → Ω → E, IsAdditiveSDESolution P ℱ W b σ Y₀ (fun _ => ⊤) Y := by
  refine ⟨fun t ω => picardLim b σ (fun s => W s ω) (Y₀ ω) t, ?_⟩
  refine ⟨measurable_picardLim hW b hb σ hY₀, fun ω => ?_,
    fun ω t _ _ => (continuous_picardLim b hb σ (hW.cont ω) (Y₀ ω)).continuousOn,
    Eventually.of_forall fun ω t ht _ => ?_⟩
  · exact picardLim_of_nonpos b hb σ (hW.cont ω) (hW.zero ω) (Y₀ ω) le_rfl
  · exact ((isPathSolution_picardLim b hb σ (hW.cont ω) (hW.zero ω) (Y₀ ω)).2 t ht
      (WithTop.coe_lt_top t)).2

/-- Pathwise uniqueness of global strong solutions, for nonnegative times. -/
theorem sde_global_unique_nonneg [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (b : ℝ → E → E) (hb : IsLipschitzDrift b) (σ : ι → E) (Y₀ : Ω → E) {Y Y' : ℝ → Ω → E}
    (hY : IsAdditiveSDESolution P ℱ W b σ Y₀ (fun _ => ⊤) Y)
    (hY' : IsAdditiveSDESolution P ℱ W b σ Y₀ (fun _ => ⊤) Y') :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Y t ω = Y' t ω := by
  have h := sde_pathwise_unique hW Set.univ isOpen_univ b hb.toLoc σ Y₀ hY hY'
    (Eventually.of_forall fun ω t _ _ => Set.mem_univ _)
    (Eventually.of_forall fun ω t _ _ => Set.mem_univ _)
  filter_upwards [h] with ω hω t ht
  exact hω t ht (by simp)

/-- Global strong existence together with pathwise uniqueness for `t ≥ 0` (the corrected form of
`exists_sde_solution_global`). -/
theorem exists_sde_solution_global_nonneg [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W) (b : ℝ → E → E) (hb : IsLipschitzDrift b) (σ : ι → E)
    (Y₀ : Ω → E) (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) :
    ∃ Y : ℝ → Ω → E, IsAdditiveSDESolution P ℱ W b σ Y₀ (fun _ => ⊤) Y ∧
      ∀ Y' : ℝ → Ω → E, IsAdditiveSDESolution P ℱ W b σ Y₀ (fun _ => ⊤) Y' →
        ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Y t ω = Y' t ω := by
  obtain ⟨Y, hY⟩ := exists_sde_solution_global_exists hW b hb σ hY₀
  exact ⟨Y, hY, fun Y' hY' => sde_global_unique_nonneg hW b hb σ Y₀ hY hY'⟩

/-- **Strong existence up to the exit/explosion time** (Lemma B.1-maximal, M L11731-11736):
for `Y₀` measurable at all times of `ℱ` with values in the open set `U`, there is a stopping time
`τ > 0` and a strong solution on `[0, τ)` with values in `U`; on `{τ < ∞}` the path leaves every
compact subset of `U` as `t ↑ τ` (so that "no exit from compacts on finite intervals" implies
global existence); `τ` dominates the lifetime of every other `U`-valued strong solution. -/
theorem exists_sde_solution_maximal [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (U : Set E) (hU : IsOpen U) (b : ℝ → E → E) (hb : IsLocLipschitzDrift U b) (σ : ι → E)
    (Y₀ : Ω → E) (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) (hY₀U : ∀ ω, Y₀ ω ∈ U) :
    ∃ (τ : Ω → WithTop ℝ) (Y : ℝ → Ω → E), IsStoppingTime ℱ τ ∧ (∀ ω, 0 < τ ω) ∧
      IsAdditiveSDESolution P ℱ W b σ Y₀ τ Y ∧
      (∀ ω, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ ω → Y t ω ∈ U) ∧
      (∀ ω, τ ω < ⊤ → ∀ K : Set E, IsCompact K → K ⊆ U →
        ∀ t₀ : ℝ, (t₀ : WithTop ℝ) < τ ω → ∃ t : ℝ, t₀ < t ∧ (t : WithTop ℝ) < τ ω ∧ Y t ω ∉ K) ∧
      (∀ (τ' : Ω → WithTop ℝ) (Y' : ℝ → Ω → E), IsAdditiveSDESolution P ℱ W b σ Y₀ τ' Y' →
        (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ' ω → Y' t ω ∈ U) →
        ∀ᵐ ω ∂P, τ' ω ≤ τ ω) := by
  obtain ⟨X⟩ := exists_exhaustion U hU b hb
  let Ym : ℕ → ℝ → Ω → E := fun m t ω => picardLim (X.bt m) σ (fun s => W s ω) (Y₀ ω) t
  have hD : ∀ ω, PathData X σ (fun s => W s ω) (Y₀ ω) (fun m s => Ym m s ω) := fun ω =>
    PathData.of_picardLim X σ (hW.cont ω) (hW.zero ω) (Y₀ ω)
  have hYm_meas : ∀ m t, Measurable[ℱ t] (Ym m t) := fun m t =>
    measurable_picardLim hW (X.bt m) (X.lip m) σ hY₀ t
  have hYm_cont : ∀ m ω, Continuous fun t => Ym m t ω := fun m ω =>
    continuous_picardLim (X.bt m) (X.lip m) σ (hW.cont ω) (Y₀ ω)
  have hstop_m : ∀ m, IsStoppingTime ℱ (exitTime (Ym m) (X.V m) 0) := fun m =>
    isStoppingTime_exitTime ℱ (Ym m) (hYm_meas m) (hYm_cont m) (X.isOpen_V m) 0
  let τ : Ω → WithTop ℝ := fun ω => lifetime X (fun m s => Ym m s ω)
  have hstop : IsStoppingTime ℱ τ := by
    intro t
    have : {ω | τ ω ≤ t} = ⋂ m, {ω | exitTime (Ym m) (X.V m) 0 ω ≤ t} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      show lifetime X (fun m s => Ym m s ω) ≤ t ↔ _
      unfold lifetime
      rw [ciSup_le_iff (OrderTop.bddAbove _)]
      exact forall_congr' fun m => Iff.rfl
    rw [this]
    exact MeasurableSet.iInter fun m => hstop_m m t
  let Y : ℝ → Ω → E := fun t ω => pathY X (fun m s => Ym m s ω) (Y₀ ω) t
  have hYadapted : ∀ t, Measurable[ℱ t] (Y t) := by
    intro t
    refine measurable_of_cover (m := ℱ t)
      (fun m => {ω | (t : WithTop ℝ) < exitTime (Ym m) (X.V m) 0 ω}) ?_ (fun m => Ym m t)
      (fun m => hYm_meas m t) Y₀ (Y t) (hY₀ t) ?_ ?_
    · intro m
      have e : {ω | (t : WithTop ℝ) < exitTime (Ym m) (X.V m) 0 ω} =
          {ω | exitTime (Ym m) (X.V m) 0 ω ≤ t}ᶜ := by
        ext ω; simp [not_le]
      rw [e]
      exact (hstop_m m t).compl
    · intro m ω hω
      exact pathY_eq (hD ω) hω
    · intro ω hω
      exact pathY_of_not (fun ⟨m, hm⟩ => hω m hm)
  refine ⟨τ, Y, hstop, fun ω => (hD ω).lifetime_pos (hY₀U ω),
    ⟨hYadapted, fun ω => pathY_of_nonpos (hD ω) le_rfl,
      fun ω t ht htτ => ((hD ω).isPathSolution_pathY.2 t ht htτ).1,
      Eventually.of_forall fun ω t ht htτ => ((hD ω).isPathSolution_pathY.2 t ht htτ).2⟩,
    fun ω t ht htτ => (hD ω).pathY_mem ht htτ,
    fun ω hlt => (hD ω).exit_alt (hY₀U ω) hlt, ?_⟩
  intro τ' Y' hY' hU'
  filter_upwards [hY'.isPathSolution, hU'] with ω h1 h2
  exact (hD ω).maximal (hY₀U ω) h1 h2

/-- Globally Lipschitz drifts: a pathwise unique global strong solution (M L11740: "the
regularized system with `K` replaced by `K_ε` has a pathwise unique global strong solution").
Uniqueness is asserted for `t ≥ 0`, the times on which `IsAdditiveSDESolution` constrains `Y`. -/
theorem exists_sde_solution_global [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (b : ℝ → E → E) (hb : IsLipschitzDrift b) (σ : ι → E) (Y₀ : Ω → E)
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) :
    ∃ Y : ℝ → Ω → E, IsAdditiveSDESolution P ℱ W b σ Y₀ (fun _ => ⊤) Y ∧
      ∀ Y' : ℝ → Ω → E, IsAdditiveSDESolution P ℱ W b σ Y₀ (fun _ => ⊤) Y' →
        ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Y t ω = Y' t ω :=
  exists_sde_solution_global_nonneg hW b hb σ Y₀ hY₀

/-- A global strong solution is an Itô process with constant diffusion coefficient, so Itô's
formula applies (`ito_formula_additive`). -/
theorem IsAdditiveSDESolution.eq_itoProcess [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W) {b : ℝ → E → E} {σ : ι → E} {Y₀ : Ω → E} {Y : ℝ → Ω → E}
    (hY : IsAdditiveSDESolution P ℱ W b σ Y₀ (fun _ => ⊤) Y) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Y t ω = itoProcess P ℱ W Y₀ (fun s ω => b s (Y s ω)) (fun _ _ => σ) t ω := by
  filter_upwards [hY.eq, localItoIntegralE_const hW σ] with ω h1 h2 t ht
  rw [(h1 t ht (WithTop.coe_lt_top t)).2, itoProcess, h2 t]

end Strong

end HRS
