import HRS.MD.EQ29Vocab
import HRS.MD.EQTransShift

/-!
# EQ-TRANS assembly (chunk D): `eq_trans_assembly_proof`

`centering_transition` from the static CLT `eq_static_clt` (not proved: its statement is copied verbatim into the hypothesis) and the proved
deterministic shift `eq_shift_limit_proof`.  `linCoord (withDensityReal ρβ) φ = linCoord (firstMarginal ℙ_{N,β}) φ + centerShift`
(`linCoord_eq_add_centerShift`); Slutsky for a convergent shift (bounded Lipschitz test functions) and tightness for the divergent shifts.
The tie against `HRS.MD.EQ29.eq_trans_assembly` is `HRS/MD/EQAsmTransTie.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS

namespace MD

namespace EQAsmTrans

open HRS.Main HRS.MD.EQ29

variable {d : ℕ}

/-! ### Weak convergence on `ℝ` -/

theorem eqat_conv_congr {μ μ' : ℕ → Measure ℝ} {ν : Measure ℝ} (h : ConvergesInLaw μ ν)
    (hev : ∀ᶠ N in atTop, μ N = μ' N) : ConvergesInLaw μ' ν := fun f =>
  (h f).congr' (hev.mono fun N hN => by rw [hN])

/-- A function with bounded oscillation is bounded. -/
theorem eqat_norm_le {g : ℝ → ℝ} {C0 : ℝ} (hC0 : ∀ x y, dist (g x) (g y) ≤ C0) (x : ℝ) :
    ‖g x‖ ≤ ‖g 0‖ + C0 := by
  have h := hC0 x 0
  rw [Real.dist_eq] at h
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have := abs_sub_abs_le_abs_sub (g x) (g 0)
  linarith

/-- Slutsky for a deterministic shift: `μ_N ⇒ ν`, `c_N → c₀` give `μ_N(· + c_N) ⇒ ν(· + c₀)` (push-forwards). -/
theorem eqat_shift (μ : ℕ → Measure ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hμ : ∀ N, IsProbabilityMeasure (μ N)) (h : ConvergesInLaw μ ν)
    (c : ℕ → ℝ) (c0 : ℝ) (hc : Tendsto c atTop (𝓝 c0)) :
    ConvergesInLaw (fun N => (μ N).map (· + c N)) (ν.map (· + c0)) := by
  have hsh : ∀ a : ℝ, Measurable (fun x : ℝ => x + a) := fun a => measurable_id.add_const a
  intro f
  let PM : ℕ → ProbabilityMeasure ℝ := fun N => ⟨(μ N).map (· + c N), inferInstance⟩
  let PM0 : ProbabilityMeasure ℝ := ⟨ν.map (· + c0), inferInstance⟩
  have hT : Tendsto PM atTop (𝓝 PM0) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    intro g ⟨C0, hC0⟩ ⟨L, hL⟩
    have hgc : Continuous g := hL.continuous
    have hint : ∀ (l : Measure ℝ) (a : ℝ), ∫ x, g x ∂(l.map (· + a)) = ∫ x, g (x + a) ∂l := fun l a =>
      integral_map (hsh a).aemeasurable hgc.aestronglyMeasurable
    let g0 : ℝ →ᵇ ℝ :=
      ⟨⟨fun x => g (x + c0), hgc.comp (continuous_id.add continuous_const)⟩, ⟨C0, fun x y => hC0 _ _⟩⟩
    have h0 : Tendsto (fun N => ∫ x, g (x + c0) ∂(μ N)) atTop (𝓝 (∫ x, g (x + c0) ∂ν)) := h g0
    have hz : Tendsto (fun N => (L : ℝ) * dist (c N) c0) atTop (𝓝 0) := by
      have := (tendsto_iff_dist_tendsto_zero.1 hc).const_mul (L : ℝ)
      simpa using this
    change Tendsto (fun N => ∫ x, g x ∂((μ N).map (· + c N))) atTop (𝓝 (∫ x, g x ∂(ν.map (· + c0))))
    simp_rw [hint]
    refine h0.congr_dist (squeeze_zero (fun _ => dist_nonneg) (fun N => ?_) hz)
    haveI := hμ N
    have hi : ∀ a : ℝ, Integrable (fun x => g (x + a)) (μ N) := fun a =>
      Integrable.of_bound (hgc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (‖g 0‖ + C0) (Filter.Eventually.of_forall fun x => eqat_norm_le hC0 _)
    rw [Real.dist_eq, ← integral_sub (hi c0) (hi (c N))]
    have := norm_integral_le_of_norm_le_const (μ := μ N)
      (f := fun x => g (x + c0) - g (x + c N)) (C := (L : ℝ) * dist (c N) c0)
      (Filter.Eventually.of_forall fun x => by
        rw [← dist_eq_norm]
        refine (hL.dist_le_mul _ _).trans ?_
        rw [dist_add_left, dist_comm])
    simpa [Real.norm_eq_abs] using this
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hT) f
  exact this

/-- Tightness: a weakly convergent sequence (to a probability measure) puts mass `> 1 - ε` on a fixed
ball, eventually. -/
theorem eqat_tight (μ : ℕ → Measure ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hμ : ∀ N, IsProbabilityMeasure (μ N)) (h : ConvergesInLaw μ ν) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ᶠ N in atTop, 1 - ε < (μ N).real {x | |x| ≤ R} := by
  -- mass of a large ball under `ν`
  have hlim : Tendsto (fun n : ℕ => ν.real (Set.Icc (-(n : ℝ)) n)) atTop (𝓝 1) := by
    have hmono : Monotone fun n : ℕ => Set.Icc (-(n : ℝ)) n := fun a b hab =>
      Set.Icc_subset_Icc (neg_le_neg (by exact_mod_cast hab)) (by exact_mod_cast hab)
    have hU : (⋃ n : ℕ, Set.Icc (-(n : ℝ)) n) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_ge |x|
      exact ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    have := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rw [hU, measure_univ] at this
    have h2 := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp this
    exact h2
  obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds (show 1 - ε / 2 < 1 by linarith))).exists
  set R0 : ℝ := (n : ℝ) with hR0
  -- the continuous cut-off
  let fc : ℝ → ℝ := fun x => max 0 (min 1 (R0 + 1 - |x|))
  have hfc : Continuous fc := by fun_prop
  have hfb : ∀ x, ‖fc x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have : 0 ≤ fc x := le_max_left _ _
      linarith
    · exact max_le zero_le_one (min_le_left _ _)
  let F : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨fc, hfc⟩ 2 (fun x y => by
    rw [Real.dist_eq]
    have h1 := hfb x
    have h2 := hfb y
    rw [Real.norm_eq_abs, abs_le] at h1 h2
    show |fc x - fc y| ≤ 2
    rw [abs_le]; constructor <;> linarith)
  have hF : ∀ x, F x = fc x := fun x => rfl
  have h1 : ν.real (Set.Icc (-R0) R0) ≤ ∫ x, fc x ∂ν := by
    have : ν.real (Set.Icc (-R0) R0) = ∫ x, (Set.Icc (-R0) R0).indicator (1 : ℝ → ℝ) x ∂ν := by
      rw [integral_indicator_one measurableSet_Icc]
    rw [this]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Icc)
      (Integrable.of_bound hfc.aestronglyMeasurable 1 (Filter.Eventually.of_forall hfb)) fun x => ?_
    by_cases hx : x ∈ Set.Icc (-R0) R0
    · rw [Set.indicator_of_mem hx]
      obtain ⟨hx1, hx2⟩ := hx
      have : |x| ≤ R0 := abs_le.2 ⟨hx1, hx2⟩
      show 1 ≤ max 0 (min 1 (R0 + 1 - |x|))
      exact le_max_of_le_right (le_min le_rfl (by linarith))
    · rw [Set.indicator_of_notMem hx]
      exact le_max_left _ _
  have hconv := (h F)
  refine ⟨R0 + 1, ?_⟩
  have hev : ∀ᶠ N in atTop, 1 - ε < ∫ x, F x ∂(μ N) := by
    refine hconv.eventually (lt_mem_nhds ?_)
    have : ∫ x, F x ∂ν = ∫ x, fc x ∂ν := rfl
    rw [this]; linarith
  filter_upwards [hev] with N hN
  haveI := hμ N
  have h2 : ∫ x, F x ∂(μ N) ≤ (μ N).real {x | |x| ≤ R0 + 1} := by
    have : (μ N).real {x | |x| ≤ R0 + 1} = ∫ x, {x : ℝ | |x| ≤ R0 + 1}.indicator (1 : ℝ → ℝ) x ∂(μ N) := by
      rw [integral_indicator_one (isClosed_le continuous_abs continuous_const).measurableSet]
    rw [this]
    refine integral_mono (Integrable.of_bound F.continuous.aestronglyMeasurable 1
        (Filter.Eventually.of_forall hfb))
      ((integrable_const (1 : ℝ)).indicator (isClosed_le continuous_abs continuous_const).measurableSet) fun x => ?_
    by_cases hx : x ∈ {x : ℝ | |x| ≤ R0 + 1}
    · rw [Set.indicator_of_mem hx]
      exact (hfb x).trans' (by rw [hF, Real.norm_eq_abs]; exact le_abs_self _) |>.trans le_rfl
    · rw [Set.indicator_of_notMem hx]
      have : R0 + 1 - |x| ≤ 0 := by
        simp only [Set.mem_setOf_eq, not_le] at hx; linarith
      rw [hF]
      show max 0 (min 1 (R0 + 1 - |x|)) ≤ 0
      exact max_le le_rfl ((min_le_right _ _).trans this)
  linarith

/-- If the sets `S N` eventually contain every ball, the mass of `S N` tends to `1`. -/
theorem eqat_one (μ : ℕ → Measure ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hμ : ∀ N, IsProbabilityMeasure (μ N)) (h : ConvergesInLaw μ ν) (S : ℕ → Set ℝ)
    (hS : ∀ R : ℝ, ∀ᶠ N in atTop, {x : ℝ | |x| ≤ R} ⊆ S N) :
    Tendsto (fun N => μ N (S N)) atTop (𝓝 1) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have ha' : a.toReal < 1 := by
      have := (ENNReal.toReal_lt_toReal ha.ne_top ENNReal.one_ne_top).2 ha
      simpa using this
    obtain ⟨R, hR⟩ := eqat_tight μ ν hμ h (ε := 1 - a.toReal) (by linarith)
    filter_upwards [hR, hS R] with N h1 h2
    haveI := hμ N
    have h3 : a.toReal < (μ N (S N)).toReal := by
      have : (μ N).real {x | |x| ≤ R} ≤ (μ N).real (S N) := measureReal_mono h2 (measure_ne_top _ _)
      have h4 : (μ N).real (S N) = (μ N (S N)).toReal := rfl
      linarith
    exact (ENNReal.toReal_lt_toReal ha.ne_top (measure_ne_top _ _)).1 h3
  · intro a ha
    exact Filter.Eventually.of_forall fun N => by
      haveI := hμ N
      exact (prob_le_one).trans_lt ha

theorem eq_trans_assembly_proof (hd : 2 ≤ d)
    (hclt : ∀ (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
      (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
      (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (φ : Torus d → ℝ)
      (hφ : Torus.IsSmooth φ),
      ConvergesInLaw
        (fun N : ℕ => law (canonicalGibbs (periodicRiesz d s) V N β)
          (linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) φ))
        (gaussianLaw (susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ φ)))
    (hshift : type_of% (@HRS.MD.EQTransShift.eq_shift_limit_proof d)) :
    type_of% (@HRS.Main.centering_transition d) := by
  intro _ s hs0 hsd V hV β hβ ρβ hρβ φ hφ
  have hφc : Continuous φ :=
    HRS.PDE.MFAux.continuous_of_isCk (ContDiff.of_le
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from hφ) (by exact_mod_cast le_top))
  -- the statistic `A_N` and its law
  have hAm : ∀ (μ : Measure (Torus d)) (N : ℕ), Measurable (fun X : Config d N => linCoord μ φ X) := by
    intro μ N
    unfold linCoord
    exact measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      hφc.measurable.comp (measurable_pi_apply i))).sub measurable_const)
  set v : ℝ := susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ φ with hv
  set μ' : ℕ → Measure ℝ := fun N =>
    if 2 ≤ N then law (canonicalGibbs (periodicRiesz d s) V N β)
      (linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) φ)
    else gaussianLaw v with hμ'
  have hμ'p : ∀ N, IsProbabilityMeasure (μ' N) := by
    intro N
    simp only [hμ']
    split_ifs with hN
    · haveI := HRS.MD.EQTransShift.et_gibbs_prob hd hs0 hsd V hV hβ hρβ (N := N) (by omega)
      infer_instance
    · unfold gaussianLaw; infer_instance
  haveI : IsProbabilityMeasure (gaussianLaw v) := by unfold gaussianLaw; infer_instance
  have hev2 : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
  have hconv : ConvergesInLaw μ' (gaussianLaw v) :=
    eqat_conv_congr (hclt hd hs0 hsd V hV β hβ ρβ hρβ φ hφ)
      (hev2.mono fun N hN => by simp only [hμ', hN, ite_true])
  -- the law of the exactly-uncentered statistic is the shifted law
  have hlawB' : ∀ N : ℕ, 2 ≤ N →
      law (canonicalGibbs (periodicRiesz d s) V N β) (linCoord (withDensityReal ρβ) φ) =
        (μ' N).map (· + centerShift d s V β ρβ φ N) := by
    intro N hN
    have hfun : (linCoord (withDensityReal ρβ) φ : Config d N → ℝ) =
        (fun x => x + centerShift d s V β ρβ φ N) ∘
          (linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) φ) :=
      funext fun X => linCoord_eq_add_centerShift s V β ρβ φ X
    have hsh : Measurable (fun x : ℝ => x + centerShift d s V β ρβ φ N) := measurable_id.add_const _
    simp only [hμ', hN, ite_true]
    rw [hfun, Measure.map_map hsh (hAm _ N)]
  -- sets
  have hset : ∀ N : ℕ, 2 ≤ N → ∀ T : Set ℝ, MeasurableSet T →
      canonicalGibbs (periodicRiesz d s) V N β {X | linCoord (withDensityReal ρβ) φ X ∈ T} =
        μ' N {x | x + centerShift d s V β ρβ φ N ∈ T} := by
    intro N hN T hT
    have hsh : Measurable (fun x : ℝ => x + centerShift d s V β ρβ φ N) := measurable_id.add_const _
    calc canonicalGibbs (periodicRiesz d s) V N β {X | linCoord (withDensityReal ρβ) φ X ∈ T}
        = (law (canonicalGibbs (periodicRiesz d s) V N β) (linCoord (withDensityReal ρβ) φ)) T :=
          (Measure.map_apply (hAm _ N) hT).symm
      _ = ((μ' N).map (· + centerShift d s V β ρβ φ N)) T := by rw [hlawB' N hN]
      _ = _ := Measure.map_apply hsh hT
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hshift hd hs0 hsd V hV β hβ ρβ hρβ φ hφ
  refine ⟨fun hlt => ?_, fun heq => ?_, fun hgt hne => ?_, fun hgt hpos => ?_⟩
  · have := eqat_shift μ' (gaussianLaw v) hμ'p hconv _ _ (hs1 hlt)
    simp only [add_zero, Measure.map_id'] at this
    exact eqat_conv_congr this (hev2.mono fun N hN => (hlawB' N hN).symm)
  · have := eqat_shift μ' (gaussianLaw v) hμ'p hconv _ _ (hs2 heq)
    exact eqat_conv_congr this (hev2.mono fun N hN => (hlawB' N hN).symm)
  · intro M
    have hc := hs3 hgt hne
    have key := eqat_one μ' (gaussianLaw v) hμ'p hconv
      (fun N => {x : ℝ | M < |x + centerShift d s V β ρβ φ N|}) (fun R => by
        filter_upwards [tendsto_atTop.1 hc (M + R + 1)] with N hN x hx
        have hN' : M + R + 1 ≤ |centerShift d s V β ρβ φ N| := hN
        have hx' : |x| ≤ R := hx
        obtain ⟨hx1, hx2⟩ := abs_le.1 hx'
        show M < |x + centerShift d s V β ρβ φ N|
        rcases lt_abs.1 (show M + R < |centerShift d s V β ρβ φ N| by linarith) with h | h
        · refine lt_abs.2 (Or.inl ?_)
          linarith
        · refine lt_abs.2 (Or.inr ?_)
          linarith)
    refine key.congr' (hev2.mono fun N hN => ?_)
    exact (hset N hN {y | M < |y|} (measurableSet_lt measurable_const measurable_id.abs)).symm
  · intro M
    have hc := hs4 hgt hpos
    have key := eqat_one μ' (gaussianLaw v) hμ'p hconv
      (fun N => {x : ℝ | M < x + centerShift d s V β ρβ φ N}) (fun R => by
        filter_upwards [tendsto_atTop.1 hc (M + R + 1)] with N hN x hx
        have hN' : M + R + 1 ≤ centerShift d s V β ρβ φ N := hN
        have hx' : |x| ≤ R := hx
        obtain ⟨hx1, hx2⟩ := abs_le.1 hx'
        show M < x + centerShift d s V β ρβ φ N
        linarith)
    refine key.congr' (hev2.mono fun N hN => ?_)
    exact (hset N hN {y | M < y} (measurableSet_lt measurable_const measurable_id)).symm

-- Inline check: the conclusion is the frozen statement once `eq_static_clt` is supplied as an argument.
example (hd : 2 ≤ d) := fun hc =>
  (@eq_trans_assembly_proof d hd hc (@HRS.MD.EQTransShift.eq_shift_limit_proof d) :
    type_of% (@HRS.Main.centering_transition d))

end EQAsmTrans

end MD

end HRS
