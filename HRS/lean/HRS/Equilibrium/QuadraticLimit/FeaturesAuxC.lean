import Mathlib

/-!
# Lemma 7.5: CLT with quadratic growth (auxiliary development for `q08_clt_quadratic`, prefix `q08c_`)

Part 1: weak convergence plus convergence of the second moments implies convergence of the integrals
of continuous functions of quadratic growth (truncation argument).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

noncomputable section

namespace HRS.Q08

section UIC

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- Continuous cutoff: `1` on `‖s‖ ≤ R`, `0` on `‖s‖ ≥ R + 1`. -/
def q08c_cut (R : ℝ) (s : E) : ℝ := max 0 (min 1 (R + 1 - ‖s‖))

theorem q08c_cut_cont (R : ℝ) : Continuous (q08c_cut (E := E) R) := by
  unfold q08c_cut
  fun_prop

theorem q08c_cut_nonneg (R : ℝ) (s : E) : 0 ≤ q08c_cut R s := le_max_left _ _

theorem q08c_cut_le_one (R : ℝ) (s : E) : q08c_cut R s ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem q08c_cut_eq_one {R : ℝ} {s : E} (h : ‖s‖ ≤ R) : q08c_cut R s = 1 := by
  unfold q08c_cut
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem q08c_cut_pos {R : ℝ} {s : E} (h : 0 < q08c_cut R s) : ‖s‖ < R + 1 := by
  unfold q08c_cut at h
  by_contra hc
  push Not at hc
  have : min 1 (R + 1 - ‖s‖) ≤ 0 := (min_le_right _ _).trans (by linarith)
  have : max 0 (min 1 (R + 1 - ‖s‖)) = 0 := max_eq_left this
  linarith


theorem q08c_claimA {ν : Measure Ω} [IsFiniteMeasure ν] (Z : Ω → E) (hZ : Measurable Z)
    (hZi : Integrable (fun ω => ‖Z ω‖ ^ 2) ν)
    (Ψ : E → ℝ) (hΨ : Continuous Ψ) (C₀ : ℝ) (hgr : ∀ s, |Ψ s| ≤ C₀ * (1 + ‖s‖ ^ 2)) (R : ℝ) :
    |∫ ω, Ψ (Z ω) ∂ν - ∫ ω, Ψ (Z ω) * q08c_cut R (Z ω) ∂ν| ≤
      C₀ * ∫ ω, (1 + ‖Z ω‖ ^ 2) * (1 - q08c_cut R (Z ω)) ∂ν := by
  have hC0 : 0 ≤ C₀ := by
    have := hgr 0
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      mul_one] at this
    exact (abs_nonneg _).trans this
  have hw : Integrable (fun ω => 1 + ‖Z ω‖ ^ 2) ν := (integrable_const 1).add hZi
  have hΨm : Measurable (fun ω => Ψ (Z ω)) := hΨ.measurable.comp hZ
  have hτm : Measurable (fun ω => q08c_cut R (Z ω)) := (q08c_cut_cont R).measurable.comp hZ
  have hΨi : Integrable (fun ω => Ψ (Z ω)) ν :=
    Integrable.mono' (hw.const_mul C₀) hΨm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hgr (Z ω))
  have hΨτi : Integrable (fun ω => Ψ (Z ω) * q08c_cut R (Z ω)) ν := by
    refine Integrable.mono' (hw.const_mul C₀) (hΨm.mul hτm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (q08c_cut_nonneg R (Z ω))]
    calc |Ψ (Z ω)| * q08c_cut R (Z ω) ≤ |Ψ (Z ω)| * 1 :=
          mul_le_mul_of_nonneg_left (q08c_cut_le_one R _) (abs_nonneg _)
      _ ≤ C₀ * (1 + ‖Z ω‖ ^ 2) := by simpa using hgr (Z ω)
  have hwi : Integrable (fun ω => (1 + ‖Z ω‖ ^ 2) * (1 - q08c_cut R (Z ω))) ν := by
    refine Integrable.mono' hw (((measurable_const.add (hZ.norm.pow_const 2))).mul
      (measurable_const.sub hτm)).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := q08c_cut_nonneg R (Z ω)
    have h2 := q08c_cut_le_one R (Z ω)
    have h3 : 0 ≤ 1 + ‖Z ω‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h3 (by linarith))]
    nlinarith
  rw [← integral_sub hΨi hΨτi, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono (hΨi.sub hΨτi).abs (hwi.const_mul C₀) ?_)
  intro ω
  have h1 := q08c_cut_nonneg R (Z ω)
  have h2 := q08c_cut_le_one R (Z ω)
  have h3 := hgr (Z ω)
  show |Ψ (Z ω) - Ψ (Z ω) * q08c_cut R (Z ω)| ≤ C₀ * ((1 + ‖Z ω‖ ^ 2) * (1 - q08c_cut R (Z ω)))
  have : Ψ (Z ω) - Ψ (Z ω) * q08c_cut R (Z ω) = Ψ (Z ω) * (1 - q08c_cut R (Z ω)) := by ring
  rw [this, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - q08c_cut R (Z ω))]
  calc |Ψ (Z ω)| * (1 - q08c_cut R (Z ω)) ≤ (C₀ * (1 + ‖Z ω‖ ^ 2)) * (1 - q08c_cut R (Z ω)) :=
        mul_le_mul_of_nonneg_right h3 (by linarith)
    _ = _ := by ring


theorem q08c_tail_eq {ν : Measure Ω} [IsProbabilityMeasure ν] (Z : Ω → E) (hZ : Measurable Z)
    (hZi : Integrable (fun ω => ‖Z ω‖ ^ 2) ν) (R : ℝ) :
    ∫ ω, (1 + ‖Z ω‖ ^ 2) * (1 - q08c_cut R (Z ω)) ∂ν =
      1 + ∫ ω, ‖Z ω‖ ^ 2 ∂ν - ∫ ω, (1 + ‖Z ω‖ ^ 2) * q08c_cut R (Z ω) ∂ν := by
  have hw : Integrable (fun ω => 1 + ‖Z ω‖ ^ 2) ν := (integrable_const 1).add hZi
  have hτm : Measurable (fun ω => q08c_cut R (Z ω)) := (q08c_cut_cont R).measurable.comp hZ
  have hwτ : Integrable (fun ω => (1 + ‖Z ω‖ ^ 2) * q08c_cut R (Z ω)) ν := by
    refine Integrable.mono' hw ((measurable_const.add (hZ.norm.pow_const 2)).mul hτm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have h3 : 0 ≤ 1 + ‖Z ω‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h3 (q08c_cut_nonneg R _))]
    nlinarith [q08c_cut_le_one R (Z ω)]
  have e1 : ∀ ω, (1 + ‖Z ω‖ ^ 2) * (1 - q08c_cut R (Z ω)) =
      (1 + ‖Z ω‖ ^ 2) - (1 + ‖Z ω‖ ^ 2) * q08c_cut R (Z ω) := fun ω => by ring
  simp_rw [e1]
  rw [integral_sub hw hwτ, integral_add (integrable_const 1) hZi]
  simp

theorem q08c_delta_tendsto {γ : Measure E} [IsProbabilityMeasure γ]
    (hγ : Integrable (fun s : E => ‖s‖ ^ 2) γ) :
    Tendsto (fun R : ℕ => ∫ s, (1 + ‖s‖ ^ 2) * (1 - q08c_cut (R : ℝ) s) ∂γ) atTop (𝓝 0) := by
  have hw : Integrable (fun s : E => 1 + ‖s‖ ^ 2) γ := (integrable_const 1).add hγ
  have h := tendsto_integral_of_dominated_convergence (μ := γ)
    (F := fun (R : ℕ) (s : E) => (1 + ‖s‖ ^ 2) * (1 - q08c_cut (R : ℝ) s)) (f := fun _ => 0)
    (fun s => 1 + ‖s‖ ^ 2)
    (fun R => (((measurable_const.add (measurable_norm.pow_const 2))).mul
      (measurable_const.sub (q08c_cut_cont (E := E) (R : ℝ)).measurable)).aestronglyMeasurable)
    hw
    (fun R => Filter.Eventually.of_forall fun s => by
      have h1 := q08c_cut_nonneg (E := E) (R : ℝ) s
      have h2 := q08c_cut_le_one (E := E) (R : ℝ) s
      have h3 : 0 ≤ 1 + ‖s‖ ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h3 (by linarith))]
      nlinarith)
    (Filter.Eventually.of_forall fun s => by
      obtain ⟨R0, hR0⟩ := exists_nat_ge ‖s‖
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop R0] with R hR
      rw [q08c_cut_eq_one ((hR0.trans (by exact_mod_cast hR)))]
      simp)
  simpa using h


theorem q08c_uic {P : Measure Ω} [IsProbabilityMeasure P] {γ : Measure E} [IsProbabilityMeasure γ]
    (X : ℕ → Ω → E) (hX : ∀ N, Measurable (X N))
    (hconv : ∀ f : E →ᵇ ℝ, Tendsto (fun N => ∫ ω, f (X N ω) ∂P) atTop (𝓝 (∫ s, f s ∂γ)))
    (hγ : Integrable (fun s : E => ‖s‖ ^ 2) γ)
    (hP : ∀ N, Integrable (fun ω => ‖X N ω‖ ^ 2) P)
    (hm : ∀ᶠ N in atTop, ∫ ω, ‖X N ω‖ ^ 2 ∂P = ∫ s, ‖s‖ ^ 2 ∂γ)
    (Ψ : E → ℝ) (hΨ : Continuous Ψ) (C₀ : ℝ) (hgr : ∀ s, |Ψ s| ≤ C₀ * (1 + ‖s‖ ^ 2)) :
    Tendsto (fun N => ∫ ω, Ψ (X N ω) ∂P) atTop (𝓝 (∫ s, Ψ s ∂γ)) := by
  have hC0 : 0 ≤ C₀ := by
    have := hgr 0
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      mul_one] at this
    exact (abs_nonneg _).trans this
  set m := ∫ s, ‖s‖ ^ 2 ∂γ with hmdef
  -- bounded continuous test functions
  have hFb : ∀ (R : ℕ) (s : E), ‖Ψ s * q08c_cut (R : ℝ) s‖ ≤ C₀ * (1 + ((R : ℝ) + 1) ^ 2) := by
    intro R s
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (q08c_cut_nonneg _ _)]
    by_cases h : q08c_cut (R : ℝ) s = 0
    · rw [h, mul_zero]; positivity
    · have hpos : 0 < q08c_cut (R : ℝ) s := lt_of_le_of_ne (q08c_cut_nonneg _ _) (Ne.symm h)
      have hs := q08c_cut_pos hpos
      have hs0 := norm_nonneg s
      calc |Ψ s| * q08c_cut (R : ℝ) s ≤ |Ψ s| * 1 :=
            mul_le_mul_of_nonneg_left (q08c_cut_le_one _ _) (abs_nonneg _)
        _ ≤ C₀ * (1 + ‖s‖ ^ 2) := by simpa using hgr s
        _ ≤ C₀ * (1 + ((R : ℝ) + 1) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hC0
            nlinarith
  have hGb : ∀ (R : ℕ) (s : E), ‖(1 + ‖s‖ ^ 2) * q08c_cut (R : ℝ) s‖ ≤ 1 * (1 + ((R : ℝ) + 1) ^ 2) := by
    intro R s
    have h3 : 0 ≤ 1 + ‖s‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h3 (q08c_cut_nonneg _ _))]
    by_cases h : q08c_cut (R : ℝ) s = 0
    · rw [h, mul_zero]; positivity
    · have hpos : 0 < q08c_cut (R : ℝ) s := lt_of_le_of_ne (q08c_cut_nonneg _ _) (Ne.symm h)
      have hs := q08c_cut_pos hpos
      have hs0 := norm_nonneg s
      calc (1 + ‖s‖ ^ 2) * q08c_cut (R : ℝ) s ≤ (1 + ‖s‖ ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left (q08c_cut_le_one _ _) h3
        _ ≤ 1 * (1 + ((R : ℝ) + 1) ^ 2) := by nlinarith
  let F : ℕ → E →ᵇ ℝ := fun R => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s => Ψ s * q08c_cut (R : ℝ) s) (hΨ.mul (q08c_cut_cont _)) _ (hFb R)
  let G : ℕ → E →ᵇ ℝ := fun R => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s => (1 + ‖s‖ ^ 2) * q08c_cut (R : ℝ) s)
    ((continuous_const.add (continuous_norm.pow 2)).mul (q08c_cut_cont _)) _ (hGb R)
  have hFeq : ∀ R s, F R s = Ψ s * q08c_cut (R : ℝ) s := fun R s => rfl
  have hGeq : ∀ R s, G R s = (1 + ‖s‖ ^ 2) * q08c_cut (R : ℝ) s := fun R s => rfl
  -- the tail of the limit
  set δ : ℕ → ℝ := fun R => ∫ s, (1 + ‖s‖ ^ 2) * (1 - q08c_cut (R : ℝ) s) ∂γ with hδdef
  have hδ : Tendsto δ atTop (𝓝 0) := q08c_delta_tendsto hγ
  -- the tail of the sequence converges to the tail of the limit
  have htail : ∀ R : ℕ, Tendsto (fun N => ∫ ω, (1 + ‖X N ω‖ ^ 2) * (1 - q08c_cut (R : ℝ) (X N ω)) ∂P)
      atTop (𝓝 (δ R)) := by
    intro R
    have hγt : ∫ s, (1 + ‖s‖ ^ 2) * (1 - q08c_cut (R : ℝ) s) ∂γ =
        1 + ∫ s, ‖s‖ ^ 2 ∂γ - ∫ s, (1 + ‖s‖ ^ 2) * q08c_cut (R : ℝ) s ∂γ :=
      q08c_tail_eq (ν := γ) id measurable_id hγ (R : ℝ)
    have h1 : Tendsto (fun N => 1 + m - ∫ ω, G R (X N ω) ∂P) atTop (𝓝 (1 + m - ∫ s, G R s ∂γ)) :=
      tendsto_const_nhds.sub (hconv (G R))
    have e1 : δ R = 1 + m - ∫ s, G R s ∂γ := by
      simp only [hδdef, hGeq]
      rw [hγt]
    rw [e1]
    refine h1.congr' ?_
    filter_upwards [hm] with N hN
    rw [q08c_tail_eq (X N) (hX N) (hP N) (R : ℝ), hN]
    simp only [hGeq]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ' : Tendsto (fun R => C₀ * δ R) atTop (𝓝 (C₀ * 0)) := hδ.const_mul C₀
  rw [mul_zero] at hδ'
  obtain ⟨R, hR⟩ : ∃ R : ℕ, C₀ * δ R < ε / 4 :=
    (hδ'.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε / 4))).exists
  have h1 : ∀ᶠ N in atTop, C₀ * ∫ ω, (1 + ‖X N ω‖ ^ 2) * (1 - q08c_cut (R : ℝ) (X N ω)) ∂P < ε / 4 :=
    ((htail R).const_mul C₀).eventually (gt_mem_nhds hR)
  have h2 : ∀ᶠ N in atTop, |∫ ω, F R (X N ω) ∂P - ∫ s, F R s ∂γ| < ε / 4 := by
    have := hconv (F R)
    rw [Metric.tendsto_atTop] at this
    obtain ⟨N0, hN0⟩ := this (ε / 4) (by linarith)
    filter_upwards [eventually_ge_atTop N0] with N hN
    simpa [Real.dist_eq] using hN0 N hN
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (h1.and h2)
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨hN1, hN2⟩ := hN0 N hN
  have hA := q08c_claimA (X N) (hX N) (hP N) Ψ hΨ C₀ hgr (R : ℝ)
  have hB := q08c_claimA (ν := γ) id measurable_id hγ Ψ hΨ C₀ hgr (R : ℝ)
  have hδeq : δ R = ∫ s, (1 + ‖s‖ ^ 2) * (1 - q08c_cut (R : ℝ) s) ∂γ := rfl
  simp only [id] at hB
  rw [← hδeq] at hB
  simp only [hFeq] at hN2
  rw [Real.dist_eq]
  have key : |∫ ω, Ψ (X N ω) ∂P - ∫ s, Ψ s ∂γ| ≤
      |∫ ω, Ψ (X N ω) ∂P - ∫ ω, Ψ (X N ω) * q08c_cut (R : ℝ) (X N ω) ∂P| +
      |∫ ω, Ψ (X N ω) * q08c_cut (R : ℝ) (X N ω) ∂P - ∫ s, Ψ s * q08c_cut (R : ℝ) s ∂γ| +
      |∫ s, Ψ s * q08c_cut (R : ℝ) s ∂γ - ∫ s, Ψ s ∂γ| := by
    have := abs_add_three (∫ ω, Ψ (X N ω) ∂P - ∫ ω, Ψ (X N ω) * q08c_cut (R : ℝ) (X N ω) ∂P)
      (∫ ω, Ψ (X N ω) * q08c_cut (R : ℝ) (X N ω) ∂P - ∫ s, Ψ s * q08c_cut (R : ℝ) s ∂γ)
      (∫ s, Ψ s * q08c_cut (R : ℝ) s ∂γ - ∫ s, Ψ s ∂γ)
    convert this using 2
    ring
  have hB' : |∫ s, Ψ s * q08c_cut (R : ℝ) s ∂γ - ∫ s, Ψ s ∂γ| ≤ C₀ * δ R := by
    rw [abs_sub_comm]; exact hB
  linarith

end UIC


section Clt

variable {T : Type*} [MeasurableSpace T] {L : ℕ}

/-- The normalised vector of sums along the first `N` coordinates of an infinite sequence. -/
def q08c_V (u : Fin L → T → ℝ) (N : ℕ) (ω : ℕ → T) : EuclideanSpace ℝ (Fin L) :=
  WithLp.toLp 2 fun i : Fin L => (Real.sqrt N)⁻¹ * ∑ k ∈ Finset.range N, u i (ω k)

theorem q08c_V_meas (u : Fin L → T → ℝ) (hm : ∀ i, Measurable (u i)) (N : ℕ) :
    Measurable (q08c_V u N) := by
  unfold q08c_V
  refine (PiLp.continuous_toLp 2 _).measurable.comp ?_
  refine measurable_pi_iff.2 fun i => measurable_const.mul ?_
  exact Finset.measurable_sum _ fun k _ => (hm i).comp (measurable_pi_apply k)

theorem q08c_transfer (μ : Measure T) [IsProbabilityMeasure μ] (u : Fin L → T → ℝ)
    (hm : ∀ i, Measurable (u i)) (Ψ : EuclideanSpace ℝ (Fin L) → ℝ) (hΨ : Continuous Ψ) (N : ℕ) :
    ∫ X : Fin N → T, Ψ (WithLp.toLp 2 fun i : Fin L => (Real.sqrt N)⁻¹ * ∑ k : Fin N, u i (X k))
        ∂(Measure.pi fun _ => μ) =
      ∫ ω, Ψ (q08c_V u N ω) ∂(Measure.infinitePi fun _ : ℕ => μ) := by
  have hmap : (Measure.infinitePi fun _ : ℕ => μ).map (fun (ω : ℕ → T) (k : Fin N) => ω (k : ℕ)) =
      Measure.pi fun _ : Fin N => μ := by
    rw [Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => μ) (f := fun k : Fin N => (k : ℕ))
      Fin.val_injective, Measure.infinitePi_eq_pi]
  have hW : Measurable (fun X : Fin N → T => Ψ (WithLp.toLp 2 fun i : Fin L =>
      (Real.sqrt N)⁻¹ * ∑ k : Fin N, u i (X k))) := by
    refine hΨ.measurable.comp ((PiLp.continuous_toLp 2 _).measurable.comp ?_)
    refine measurable_pi_iff.2 fun i => measurable_const.mul ?_
    exact Finset.measurable_sum _ fun k _ => (hm i).comp (measurable_pi_apply k)
  rw [← hmap, integral_map (measurable_pi_iff.2 fun k => measurable_pi_apply _).aemeasurable hW.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [q08c_V, Finset.sum_range]


open ProbabilityTheory in
theorem q08c_coord_memLp (μ : Measure T) [IsProbabilityMeasure μ] (g : T → ℝ) (hg2 : MemLp g 2 μ)
    (k : ℕ) : MemLp (fun ω : ℕ → T => g (ω k)) 2 (Measure.infinitePi fun _ : ℕ => μ) :=
  hg2.comp_measurePreserving (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) k)

theorem q08c_coord_integral (μ : Measure T) [IsProbabilityMeasure μ] (g : T → ℝ) (hg : Measurable g)
    (k : ℕ) : ∫ ω : ℕ → T, g (ω k) ∂(Measure.infinitePi fun _ : ℕ => μ) = ∫ x, g x ∂μ := by
  have h := measurePreserving_eval_infinitePi (fun _ : ℕ => μ) k
  rw [← integral_map h.measurable.aemeasurable hg.aestronglyMeasurable, h.map_eq]

open ProbabilityTheory in
theorem q08c_sum_sq (μ : Measure T) [IsProbabilityMeasure μ] (g : T → ℝ) (hg : Measurable g)
    (hg2 : MemLp g 2 μ) (h0 : ∫ x, g x ∂μ = 0) (v : ℝ) (h1 : ∫ x, g x ^ 2 ∂μ = v) (N : ℕ) :
    MemLp (fun ω : ℕ → T => ∑ k ∈ Finset.range N, g (ω k)) 2 (Measure.infinitePi fun _ : ℕ => μ) ∧
      ∫ ω : ℕ → T, (∑ k ∈ Finset.range N, g (ω k)) ^ 2 ∂(Measure.infinitePi fun _ : ℕ => μ) = N * v := by
  have hX : ∀ k, MemLp (fun ω : ℕ → T => g (ω k)) 2 (Measure.infinitePi fun _ : ℕ => μ) := fun k => q08c_coord_memLp μ g hg2 k
  have hS : MemLp (fun ω : ℕ → T => ∑ k ∈ Finset.range N, g (ω k)) 2 (Measure.infinitePi fun _ : ℕ => μ) :=
    memLp_finsetSum (Finset.range N) (fun k _ => hX k)
  refine ⟨hS, ?_⟩
  have hmean : ∫ ω : ℕ → T, ∑ k ∈ Finset.range N, g (ω k) ∂(Measure.infinitePi fun _ : ℕ => μ) = 0 := by
    rw [integral_finsetSum _ (fun k _ => (hX k).integrable one_le_two)]
    simp only [q08c_coord_integral μ g hg, h0, Finset.sum_const_zero]
  have hvar := variance_of_integral_eq_zero hS.aemeasurable hmean
  have hind : Set.Pairwise (↑(Finset.range N) : Set ℕ) fun i j =>
      IndepFun (fun ω : ℕ → T => g (ω i)) (fun ω : ℕ → T => g (ω j)) (Measure.infinitePi fun _ : ℕ => μ) := by
    intro i _ j _ hij
    exact (iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ : ℕ => g) (fun _ => hg)).indepFun hij
  have hv := IndepFun.variance_sum (X := fun k (ω : ℕ → T) => g (ω k)) (s := Finset.range N)
    (fun k _ => hX k) hind
  have e : (∑ k ∈ Finset.range N, fun ω : ℕ → T => g (ω k)) =
      fun ω => ∑ k ∈ Finset.range N, g (ω k) := by
    ext ω; simp [Finset.sum_apply]
  rw [e] at hv
  rw [← hvar, hv]
  have hk : ∀ k, variance (fun ω : ℕ → T => g (ω k)) (Measure.infinitePi fun _ : ℕ => μ) = v := by
    intro k
    rw [variance_of_integral_eq_zero (hX k).aemeasurable (by
      rw [q08c_coord_integral μ g hg k, h0])]
    rw [q08c_coord_integral μ (fun x => g x ^ 2) (hg.pow_const 2) k, h1]
  simp [hk]


open ProbabilityTheory in
theorem q08c_V_second (μ : Measure T) [IsProbabilityMeasure μ] (u : Fin L → T → ℝ)
    (hm : ∀ i, Measurable (u i)) (h2 : ∀ i, MemLp (u i) 2 μ) (h0 : ∀ i, ∫ x, u i x ∂μ = 0)
    (ho : ∀ i j, ∫ x, u i x * u j x ∂μ = if i = j then 1 else 0) (N : ℕ) (hN : 1 ≤ N) :
    Integrable (fun ω => ‖q08c_V u N ω‖ ^ 2) (Measure.infinitePi fun _ : ℕ => μ) ∧
      ∫ ω, ‖q08c_V u N ω‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => μ) = L := by
  have hs : ∀ i, MemLp (fun ω : ℕ → T => ∑ k ∈ Finset.range N, u i (ω k)) 2
        (Measure.infinitePi fun _ : ℕ => μ) ∧
      ∫ ω : ℕ → T, (∑ k ∈ Finset.range N, u i (ω k)) ^ 2 ∂(Measure.infinitePi fun _ : ℕ => μ) = N * 1 := by
    intro i
    refine q08c_sum_sq μ (u i) (hm i) (h2 i) (h0 i) 1 ?_ N
    have := ho i i
    simpa [sq] using this
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : ∀ ω, ‖q08c_V u N ω‖ ^ 2 =
      ∑ i : Fin L, (N : ℝ)⁻¹ * (∑ k ∈ Finset.range N, u i (ω k)) ^ 2 := by
    intro ω
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [q08c_V, Real.norm_eq_abs, sq_abs, mul_pow]
    rw [inv_pow, Real.sq_sqrt hN0.le]
  simp_rw [e]
  refine ⟨integrable_finsetSum _ fun i _ => ((hs i).1.integrable_sq).const_mul _, ?_⟩
  rw [integral_finsetSum _ fun i _ => ((hs i).1.integrable_sq).const_mul _]
  simp_rw [integral_const_mul, (hs _).2]
  simp [mul_comm, hN0.ne']


end Clt

section GaussSide

open ProbabilityTheory Matrix MatrixOrder
open scoped RealInnerProductSpace

variable {L : ℕ}

theorem q08c_gauss_dir (t : EuclideanSpace ℝ (Fin L)) :
    HasLaw (fun s : EuclideanSpace ℝ (Fin L) => ⟪s, t⟫) (gaussianReal 0 (‖t‖ ^ 2).toNNReal)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (1 : Matrix (Fin L) (Fin L) ℝ)) where
  aemeasurable := by fun_prop
  map_eq := by
    rw [multivariateGaussian_zero_one]
    have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian (EuclideanSpace ℝ (Fin L))) (innerSL ℝ t)
    rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm] at h
    have e : (fun s : EuclideanSpace ℝ (Fin L) => ⟪s, t⟫) = ⇑(innerSL ℝ t) := by
      ext s; simp [real_inner_comm]
    rw [e]
    exact h

theorem q08c_gauss_coord_integral (i : Fin L) :
    ∫ s : EuclideanSpace ℝ (Fin L), s i ^ 2
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (1 : Matrix (Fin L) (Fin L) ℝ)) = 1 := by
  have hS : (1 : Matrix (Fin L) (Fin L) ℝ).PosSemidef := Matrix.PosSemidef.one
  have hmp := measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin L)))
    (S := (1 : Matrix (Fin L) (Fin L) ℝ)) hS (i := i)
  have hmean : ∫ s : EuclideanSpace ℝ (Fin L), s i
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (1 : Matrix (Fin L) (Fin L) ℝ)) = 0 := by
    have := integral_map (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin L))
      (1 : Matrix (Fin L) (Fin L) ℝ)) hmp.measurable.aemeasurable (f := fun y : ℝ => y) (by fun_prop)
    rw [hmp.map_eq, integral_id_gaussianReal] at this
    simpa using this.symm
  have hv := variance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin L)))
    (S := (1 : Matrix (Fin L) (Fin L) ℝ)) hS i
  rw [variance_of_integral_eq_zero (by fun_prop) hmean] at hv
  simpa using hv

theorem q08c_gauss_second :
    Integrable (fun s : EuclideanSpace ℝ (Fin L) => ‖s‖ ^ 2)
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (1 : Matrix (Fin L) (Fin L) ℝ)) ∧
      ∫ s : EuclideanSpace ℝ (Fin L), ‖s‖ ^ 2
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (1 : Matrix (Fin L) (Fin L) ℝ)) = L := by
  have hi : ∀ i : Fin L, Integrable (fun s : EuclideanSpace ℝ (Fin L) => s i ^ 2)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (1 : Matrix (Fin L) (Fin L) ℝ)) := by
    intro i
    have := IsGaussian.memLp_dual (multivariateGaussian (0 : EuclideanSpace ℝ (Fin L))
      (1 : Matrix (Fin L) (Fin L) ℝ)) (EuclideanSpace.proj i) 2 (by simp)
    exact this.integrable_sq
  have e : (fun s : EuclideanSpace ℝ (Fin L) => ‖s‖ ^ 2) = fun s => ∑ i, s i ^ 2 := by
    ext s; rw [EuclideanSpace.norm_sq_eq]; simp
  rw [e]
  refine ⟨integrable_finsetSum _ fun i _ => hi i, ?_⟩
  rw [integral_finsetSum _ fun i _ => hi i, Finset.sum_congr rfl fun i _ => q08c_gauss_coord_integral i]
  simp

end GaussSide

section DirClt

open ProbabilityTheory Matrix MatrixOrder
open scoped RealInnerProductSpace

variable {T : Type*} [MeasurableSpace T] {L : ℕ}

theorem q08c_dir_facts (μ : Measure T) [IsProbabilityMeasure μ] (u : Fin L → T → ℝ)
    (hm : ∀ i, Measurable (u i)) (h2 : ∀ i, MemLp (u i) 2 μ) (h0 : ∀ i, ∫ x, u i x ∂μ = 0)
    (ho : ∀ i j, ∫ x, u i x * u j x ∂μ = if i = j then 1 else 0) (t : EuclideanSpace ℝ (Fin L)) :
    Measurable (fun x => ∑ i, t i * u i x) ∧ MemLp (fun x => ∑ i, t i * u i x) 2 μ ∧
      ∫ x, ∑ i, t i * u i x ∂μ = 0 ∧ ∫ x, (∑ i, t i * u i x) ^ 2 ∂μ = ‖t‖ ^ 2 := by
  refine ⟨Finset.measurable_sum _ fun i _ => measurable_const.mul (hm i),
    memLp_finsetSum _ fun i _ => (h2 i).const_mul _, ?_, ?_⟩
  · rw [integral_finsetSum _ fun i _ => ((h2 i).integrable one_le_two).const_mul _]
    simp [integral_const_mul, h0]
  · have e : ∀ x, (∑ i, t i * u i x) ^ 2 = ∑ i, ∑ j, (t i * t j) * (u i x * u j x) := by
      intro x
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hint : ∀ i j, Integrable (fun x => (t i * t j) * (u i x * u j x)) μ := fun i j =>
      ((h2 i).integrable_mul (h2 j)).const_mul _
    simp_rw [e]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    simp_rw [integral_finsetSum _ fun j _ => hint _ j, integral_const_mul, ho]
    rw [EuclideanSpace.norm_sq_eq]
    simp [sq]


theorem q08c_inner_V (u : Fin L → T → ℝ) (t : EuclideanSpace ℝ (Fin L)) (N : ℕ) (ω : ℕ → T) :
    ⟪q08c_V u N ω, t⟫ = (Real.sqrt N)⁻¹ * ∑ k ∈ Finset.range N, ∑ i, t i * u i (ω k) := by
  simp only [q08c_V, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun x _ => ?_
  ring

theorem q08c_dir_clt (μ : Measure T) [IsProbabilityMeasure μ] (u : Fin L → T → ℝ)
    (hm : ∀ i, Measurable (u i)) (h2 : ∀ i, MemLp (u i) 2 μ) (h0 : ∀ i, ∫ x, u i x ∂μ = 0)
    (ho : ∀ i j, ∫ x, u i x * u j x ∂μ = if i = j then 1 else 0) (t : EuclideanSpace ℝ (Fin L)) :
    TendstoInDistribution (fun (N : ℕ) (ω : ℕ → T) => ⟪q08c_V u N ω, t⟫) atTop
      (fun s : EuclideanSpace ℝ (Fin L) => ⟪s, t⟫) (fun _ => Measure.infinitePi fun _ : ℕ => μ)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (1 : Matrix (Fin L) (Fin L) ℝ)) := by
  obtain ⟨hgm, hg2, hg0, hgv⟩ := q08c_dir_facts μ u hm h2 h0 ho t
  set g : T → ℝ := fun x => ∑ i, t i * u i x with hg
  set P : Measure (ℕ → T) := Measure.infinitePi fun _ : ℕ => μ with hP
  have hindep : iIndepFun (fun (k : ℕ) (ω : ℕ → T) => g (ω k)) P :=
    iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ : ℕ => g) (fun _ => hgm)
  have hmap : ∀ k : ℕ, P.map (fun ω : ℕ → T => g (ω k)) = μ.map g := by
    intro k
    have h1 : (fun ω : ℕ → T => g (ω k)) = g ∘ (fun ω : ℕ → T => ω k) := rfl
    rw [h1, ← Measure.map_map hgm (measurable_pi_apply k), Measure.infinitePi_map_eval]
  have hident : ∀ k : ℕ, IdentDistrib (fun ω : ℕ → T => g (ω k)) (fun ω : ℕ → T => g (ω 0)) P P := by
    intro k
    refine ⟨(hgm.comp (measurable_pi_apply k)).aemeasurable, (hgm.comp (measurable_pi_apply 0)).aemeasurable, ?_⟩
    rw [hmap k, hmap 0]
  have hX0 : MemLp (fun ω : ℕ → T => g (ω 0)) 2 P := q08c_coord_memLp μ g hg2 0
  have hmean : P[fun ω : ℕ → T => g (ω 0)] = 0 := by
    rw [q08c_coord_integral μ g hgm 0, hg0]
  have hvar : Var[fun ω : ℕ → T => g (ω 0); P] = ‖t‖ ^ 2 := by
    rw [variance_of_integral_eq_zero hX0.aemeasurable hmean]
    rw [q08c_coord_integral μ (fun x => g x ^ 2) (hgm.pow_const 2) 0, hgv]
  have hY := q08c_gauss_dir t
  rw [← hvar] at hY
  have h := tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun (k : ℕ) (ω : ℕ → T) => g (ω k))
    (P := P) hY hX0 hindep hident
  have e : (fun (N : ℕ) (ω : ℕ → T) => ⟪q08c_V u N ω, t⟫) = fun (N : ℕ) (ω : ℕ → T) =>
      (Real.sqrt N)⁻¹ * (∑ k ∈ Finset.range N, g (ω k) - N * P[fun ω : ℕ → T => g (ω 0)]) := by
    ext N ω
    rw [hmean, mul_zero, sub_zero, q08c_inner_V]
  rw [e]
  exact h


theorem q08c_clt (μ : Measure T) [IsProbabilityMeasure μ] (u : Fin L → T → ℝ)
    (hm : ∀ i, Measurable (u i)) (h2 : ∀ i, MemLp (u i) 2 μ) (h0 : ∀ i, ∫ x, u i x ∂μ = 0)
    (ho : ∀ i j, ∫ x, u i x * u j x ∂μ = if i = j then 1 else 0)
    (Ψ : EuclideanSpace ℝ (Fin L) → ℝ) (hΨ : Continuous Ψ) (C₀ : ℝ)
    (hgr : ∀ s, |Ψ s| ≤ C₀ * (1 + ‖s‖ ^ 2)) :
    Tendsto (fun N : ℕ => ∫ X : Fin N → T,
        Ψ (WithLp.toLp 2 fun i : Fin L => (Real.sqrt N)⁻¹ * ∑ k : Fin N, u i (X k))
          ∂(Measure.pi fun _ => μ)) atTop
      (𝓝 (∫ s, Ψ s ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L))
        (1 : Matrix (Fin L) (Fin L) ℝ)))) := by
  have e : (fun N : ℕ => ∫ X : Fin N → T,
        Ψ (WithLp.toLp 2 fun i : Fin L => (Real.sqrt N)⁻¹ * ∑ k : Fin N, u i (X k))
          ∂(Measure.pi fun _ => μ)) =
      fun N : ℕ => ∫ ω, Ψ (q08c_V u N ω) ∂(Measure.infinitePi fun _ : ℕ => μ) :=
    funext fun N => q08c_transfer μ u hm Ψ hΨ N
  rw [e]
  have hcw := (tendstoInDistribution_iff_tendstoInDistribution_inner
    (X := q08c_V u) (X' := fun s : EuclideanSpace ℝ (Fin L) => s)
    (P := Measure.infinitePi fun _ : ℕ => μ)
    (P' := multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (1 : Matrix (Fin L) (Fin L) ℝ))
    (by fun_prop) (fun N => (q08c_V_meas u hm N).aemeasurable)).2
    (fun t => q08c_dir_clt μ u hm h2 h0 ho t)
  have hconv := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    (fun N => (q08c_V_meas u hm N).aemeasurable) (by fun_prop)).1 hcw
  obtain ⟨hγi, hγm⟩ := q08c_gauss_second (L := L)
  refine q08c_uic (q08c_V u) (fun N => q08c_V_meas u hm N) (fun f => hconv f) hγi
    (fun N => ?_) ?_ Ψ hΨ C₀ hgr
  · rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      simp [q08c_V]
    · exact (q08c_V_second μ u hm h2 h0 ho N h).1
  · rw [hγm]
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (q08c_V_second μ u hm h2 h0 ho N hN).2

end DirClt

end HRS.Q08

end
