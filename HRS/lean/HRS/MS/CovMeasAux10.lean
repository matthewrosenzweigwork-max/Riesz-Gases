import HRS.MS.CovMeasAux9

/-!
# S10.1 (worker S101B), part 10: abstract measurability tools (dyadic approximation from the right) and continuity of `s ↦ W_s`

`s101_aem_diag`: if `D_τ` is a family of bounded bilinear forms on `𝒦` such that for each grid time `t` the function
`τ ↦ D_τ(a_t, b_t)` is a.e.-measurable on `E ∩ (-∞,t)`, and `a_{t_n(τ)} → a'_τ`, `b_{t_n(τ)} → b'_τ` along the dyadic times
`t_n(τ) ↓ τ`, then `τ ↦ D_τ(a'_τ, b'_τ)` is a.e.-measurable on `E`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq

variable {d : ℕ}

lemma s101_aem_index {μ : Measure ℝ} (κ : ℝ → ℕ) (hκ : Measurable κ) (F : ℕ → ℝ → ℝ)
    (hF : ∀ k, AEMeasurable (F k) μ) : AEMeasurable (fun τ => F (κ τ) τ) μ := by
  choose h hhm hhe using hF
  have hall : ∀ᵐ τ ∂μ, ∀ k, F k τ = h k τ := ae_all_iff.2 hhe
  have hmeas : Measurable fun τ => h (κ τ) τ := by
    have : Measurable (fun p : ℝ × ℕ => h p.2 p.1) :=
      measurable_from_prod_countable_left (fun k => hhm k)
    exact this.comp (measurable_id.prodMk hκ)
  exact hmeas.aemeasurable.congr (hall.mono fun τ hτ => (hτ (κ τ)).symm)

/-- The dyadic grid time `(k+1)/2^n ∧ T`. -/
def s101tk (T : ℝ) (n k : ℕ) : ℝ := min T (((k : ℝ) + 1) / 2 ^ n)

/-- The dyadic approximation from the right `t_n(τ) = (⌊2^nτ⌋+1)/2^n ∧ T`. -/
def s101tn (T : ℝ) (n : ℕ) (τ : ℝ) : ℝ := s101tk T n ⌊τ * 2 ^ n⌋₊

lemma s101tk_mem {T : ℝ} (hT : 0 ≤ T) (n k : ℕ) : s101tk T n k ∈ Icc (0 : ℝ) T :=
  ⟨le_min hT (by positivity), min_le_left _ _⟩

lemma s101tn_lt {T τ : ℝ} (hτ : 0 ≤ τ) (hτT : τ < T) (n : ℕ) : τ < s101tn T n τ := by
  unfold s101tn s101tk
  refine lt_min hτT ?_
  rw [lt_div_iff₀ (by positivity)]
  exact Nat.lt_floor_add_one _

lemma s101tn_le {T τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) : s101tn T n τ ≤ τ + 1 / 2 ^ n := by
  unfold s101tn s101tk
  refine (min_le_right _ _).trans ?_
  rw [div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity)]
  have := Nat.floor_le (show 0 ≤ τ * 2 ^ n by positivity)
  linarith

lemma s101tn_tendsto {T τ : ℝ} (hτ : 0 ≤ τ) (hτT : τ < T) :
    Tendsto (fun n => s101tn T n τ) atTop (𝓝 τ) := by
  have h1 : Tendsto (fun n : ℕ => τ + 1 / (2 : ℝ) ^ n) atTop (𝓝 (τ + 0)) := by
    refine tendsto_const_nhds.add ?_
    have h0 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [one_div, inv_pow] using h0
  rw [add_zero] at h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
    (fun n => (s101tn_lt hτ hτT n).le) (fun n => s101tn_le hτ n)

theorem s101_aem_diag {m T : ℝ} (hT : 0 ≤ T) {ν : Measure ℝ} [NullSingletonClass ν] {E : Set ℝ}
    (hE : MeasurableSet E) (hEsub : E ⊆ Icc 0 T)
    (Dm : ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) (a b a' b' : ℝ → KSpace d m T)
    (H1 : ∀ t ∈ Icc (0 : ℝ) T, AEMeasurable (fun τ => Dm τ (a t) (b t)) (ν.restrict (E ∩ Iio t)))
    (H2 : ∀ τ ∈ E, τ < T → Tendsto (fun n => a (s101tn T n τ)) atTop (𝓝 (a' τ)) ∧
      Tendsto (fun n => b (s101tn T n τ)) atTop (𝓝 (b' τ))) :
    AEMeasurable (fun τ => Dm τ (a' τ) (b' τ)) (ν.restrict E) := by
  -- the approximants
  set F : ℕ → ℕ → ℝ → ℝ := fun n k τ =>
    if τ < s101tk T n k then Dm τ (a (s101tk T n k)) (b (s101tk T n k)) else 0 with hF
  have hFm : ∀ n k, AEMeasurable (F n k) (ν.restrict E) := by
    intro n k
    have h1 := H1 (s101tk T n k) (s101tk_mem hT n k)
    have h2 : AEMeasurable (fun τ => Dm τ (a (s101tk T n k)) (b (s101tk T n k)))
        ((ν.restrict E).restrict (Iio (s101tk T n k))) := by
      rw [Measure.restrict_restrict measurableSet_Iio, inter_comm]; exact h1
    have : F n k = (Iio (s101tk T n k)).indicator (fun τ => Dm τ (a (s101tk T n k)) (b (s101tk T n k))) := by
      funext τ; simp [hF, Set.indicator, mem_Iio]
    rw [this]
    exact (aemeasurable_indicator_iff measurableSet_Iio).2 h2
  have hS : ∀ n, AEMeasurable (fun τ => F n ⌊τ * 2 ^ n⌋₊ τ) (ν.restrict E) := by
    intro n
    refine s101_aem_index (fun τ => ⌊τ * 2 ^ n⌋₊) ?_ (F n) (hFm n)
    exact Nat.measurable_floor.comp (measurable_id.mul_const _)
  have hTnull : ∀ᵐ τ ∂(ν.restrict E), τ < T := by
    have : ν {T} = 0 := measure_singleton T
    have h2 : ∀ᵐ τ ∂ν, τ ≠ T := (measure_eq_zero_iff_ae_notMem.1 this).mono fun τ h => by simpa using h
    filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem hE] with τ h1 h3
    exact lt_of_le_of_ne (hEsub h3).2 h1
  refine aemeasurable_of_tendsto_metrizable_ae atTop hS ?_
  filter_upwards [hTnull, ae_restrict_mem hE] with τ hτT hτE
  have hτ0 : 0 ≤ τ := (hEsub hτE).1
  obtain ⟨ha, hb⟩ := H2 τ hτE hτT
  have heq : ∀ n, F n ⌊τ * 2 ^ n⌋₊ τ = Dm τ (a (s101tn T n τ)) (b (s101tn T n τ)) := by
    intro n
    have : τ < s101tk T n ⌊τ * 2 ^ n⌋₊ := s101tn_lt hτ0 hτT n
    simp only [hF, this, if_true]
    rfl
  simp_rw [heq]
  have hcont : Continuous fun p : KSpace d m T × KSpace d m T => Dm τ p.1 p.2 :=
    (Dm τ).continuous₂ |>.comp continuous_id
  exact (hcont.tendsto (a' τ, b' τ)).comp (ha.prodMk_nhds hb)

end HRS.MS.CovMeas
