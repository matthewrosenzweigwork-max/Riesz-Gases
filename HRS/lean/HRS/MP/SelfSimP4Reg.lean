import HRS.MP.SelfSimP4Kern
import HRS.Stochastic.SDE

/-!
# MP-SSP4REG: `p4_regularised_flow` (regularised strong solutions and setwise convergence of the laws)

Namespace `HRS.MP.SelfSimP4Impl`, helpers `p4r_`.  Theorem `p4_regularised_flow_proof`, tied to
`HRS.MP.SelfSimP4.p4_regularised_flow`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP4Impl

variable {d N : ℕ}

/-! ### Noise directions and the drift as an `IsLipschitzDrift` -/

/-- The noise directions `σ_k = √(2ν) e_k`. -/
def p4r_sigma (d N : ℕ) (ν : ℝ) (k : Fin N × Fin d) : EucConfig d N :=
  Real.sqrt (2 * ν) • configBasis d N k

theorem p4r_noise_sum (ν : ℝ) (c : Fin N × Fin d → ℝ) (i : Fin N) (j : Fin d) :
    (∑ k : Fin N × Fin d, c k • p4r_sigma d N ν k) i j = Real.sqrt (2 * ν) * c (i, j) := by
  simp [p4r_sigma, configBasis, Finset.sum_apply, Pi.single_apply, Fintype.sum_prod_type]
  ring

theorem p4r_noise_apply (ν : ℝ) (c : Fin N × Fin d → ℝ) (Wt W0 : Fin N → Euc d)
    (hc : ∀ i j, c (i, j) = Wt i j - W0 i j) (i : Fin N) :
    (∑ k : Fin N × Fin d, c k • p4r_sigma d N ν k) i = Real.sqrt (2 * ν) • (Wt i - W0 i) := by
  ext j
  rw [p4r_noise_sum, hc]
  simp

theorem p4r_isLipschitzDrift {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (N : ℕ) :
    HRS.IsLipschitzDrift (p4Drift k s N) where
  cont := (p4k_cont_drift hk N).continuousOn
  lip := fun T => by
    obtain ⟨K, hK⟩ := p4k_drift_lip_gen hk N (Real.toNNReal (Real.exp (|s| * T / 2)))
    refine ⟨K, fun t ht => hK t ?_⟩
    rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
    unfold aSelfSim
    refine Real.exp_le_exp.2 ?_
    have h1 : -s * t ≤ |s| * t := by nlinarith [neg_abs_le s, ht.1, abs_nonneg s, le_abs_self s]
    have h2 : |s| * t ≤ |s| * T := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg s)
    linarith


/-! ### Componentwise and vector form of the integrated equation -/

theorem p4r_comp_to_vec (ν : ℝ) (XT X0 : EucConfig d N) (F : ℝ → EucConfig d N) (A : Set ℝ)
    (hint : ∀ i, IntegrableOn (fun r => F r i) A) (WT W0 : Fin N → Euc d)
    (c : Fin N × Fin d → ℝ) (hc : ∀ i j, c (i, j) = WT i j - W0 i j)
    (heq : ∀ i, XT i = X0 i + (∫ r in A, F r i) + Real.sqrt (2 * ν) • (WT i - W0 i)) :
    XT = X0 + (∫ r in A, F r) + ∑ k : Fin N × Fin d, c k • p4r_sigma d N ν k := by
  funext i
  rw [Pi.add_apply, Pi.add_apply, eval_integral hint i, heq i, p4r_noise_apply ν c WT W0 hc i]

theorem p4r_vec_to_comp (ν : ℝ) (XT X0 : EucConfig d N) (F : ℝ → EucConfig d N) (A : Set ℝ)
    (hint : IntegrableOn F A) (WT W0 : Fin N → Euc d)
    (c : Fin N × Fin d → ℝ) (hc : ∀ i j, c (i, j) = WT i j - W0 i j)
    (heq : XT = X0 + (∫ r in A, F r) + ∑ k : Fin N × Fin d, c k • p4r_sigma d N ν k) :
    (∀ i, IntegrableOn (fun r => F r i) A) ∧
      ∀ i, XT i = X0 i + (∫ r in A, F r i) + Real.sqrt (2 * ν) • (WT i - W0 i) := by
  have hi : ∀ i, IntegrableOn (fun r => F r i) A := fun i => integrable_pi_iff.1 hint i
  refine ⟨hi, fun i => ?_⟩
  have := congrFun heq i
  rw [Pi.add_apply, Pi.add_apply, eval_integral hi i, p4r_noise_apply ν c WT W0 hc i] at this
  exact this


/-! ### The filtration wrapper `ℱ' t := ℱ (max t 0)` -/

/-- `ℱ' t = ℱ (max t 0)`: constant on `(-∞,0]`, so that a `ℱ 0`-measurable initial value is `ℱ' t`-measurable
for every real `t`. -/
def p4r_shiftFil {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ) : Filtration ℝ mΩ where
  seq t := ℱ (max t 0)
  mono' := fun _ _ h => ℱ.mono (max_le_max h le_rfl)
  le' := fun _ => ℱ.le _

theorem p4r_shiftFil_apply {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ) (t : ℝ) :
    p4r_shiftFil ℱ t = ℱ (max t 0) := rfl

theorem p4r_shiftFil_nnreal {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ) (t : ℝ≥0) :
    p4r_shiftFil ℱ (t : ℝ) = ℱ (t : ℝ) := by
  rw [p4r_shiftFil_apply, max_eq_left t.coe_nonneg]

theorem p4r_shiftFil_brownian {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ mΩ} {ι : Type*} [Fintype ι] {W' : ℝ≥0 → Ω → ι → ℝ}
    (h : IsBrownianFiltration P ℱ W') : IsBrownianFiltration P (p4r_shiftFil ℱ) W' where
  complete := fun t s hs hP => h.complete (max t 0) s hs hP
  adapted := fun t => by rw [p4r_shiftFil_nnreal]; exact h.adapted t
  zero := h.zero
  cont := h.cont
  indep_incr := fun s t hst => by rw [p4r_shiftFil_nnreal]; exact h.indep_incr s t hst
  gaussian_incr := h.gaussian_incr

/-! ### From an `IsAdditiveSDESolution` to a `P4AddSol` -/

theorem p4r_continuousOn_Ici {E : Type*} [TopologicalSpace E] {f : ℝ → E}
    (h : ∀ t : ℝ, 0 ≤ t → ContinuousOn f (Set.Icc 0 t)) : ContinuousOn f (Set.Ici 0) := by
  intro x hx
  have h1 := (h (x + 1) (by have : (0 : ℝ) ≤ x := hx; linarith)).continuousWithinAt
    ⟨hx, by linarith⟩
  refine h1.mono_of_mem_nhdsWithin ?_
  have : Set.Icc (0 : ℝ) (x + 1) ∈ 𝓝[Set.Ici 0] x := by
    rw [mem_nhdsWithin]
    refine ⟨Set.Iio (x + 1), isOpen_Iio, by simp, ?_⟩
    intro y hy
    exact ⟨hy.2, hy.1.le⟩
  exact this

theorem p4r_continuous_nnreal {E : Type*} [TopologicalSpace E] {f : ℝ → E}
    (h : ∀ t : ℝ, 0 ≤ t → ContinuousOn f (Set.Icc 0 t)) : Continuous fun t : ℝ≥0 => f (t : ℝ) :=
  (p4r_continuousOn_Ici h).comp_continuous NNReal.continuous_coe (fun t => t.2)

theorem p4r_addSol {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν S : ℝ} {b : ℝ → EucConfig d N → EucConfig d N} {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → EucConfig d N} (hF : IsWholeFilteredSolution P ℱ W' W Y)
    {Ys : ℝ → Ω → EucConfig d N}
    (hs : IsAdditiveSDESolution P (p4r_shiftFil ℱ) W' b (p4r_sigma d N ν) (Y 0) (fun _ => ⊤) Ys) :
    P4AddSol P ν b S ℱ W' W (fun t ζ => Ys (t : ℝ) ζ) := by
  have hcontR : ∀ ζ, Continuous fun t : ℝ≥0 => Ys (t : ℝ) ζ := fun ζ =>
    p4r_continuous_nnreal fun t ht => hs.cont ζ t ht (WithTop.coe_lt_top t)
  have hadR : Adapted ℱ (ofNNRealTime fun (t : ℝ≥0) (ζ : Ω) => Ys (t : ℝ) ζ) := by
    intro t
    by_cases ht : 0 ≤ t
    · have h1 : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht
      have h := hs.adapted t
      show Measurable[ℱ t] (fun ζ => Ys ((Real.toNNReal t : ℝ≥0) : ℝ) ζ)
      rw [h1]
      exact h.mono (le_of_eq (by rw [p4r_shiftFil_apply, max_eq_left ht])) le_rfl
    · have h1 : Real.toNNReal t = 0 := Real.toNNReal_of_nonpos (not_le.1 ht).le
      show Measurable[ℱ t] (fun ζ => Ys ((Real.toNNReal t : ℝ≥0) : ℝ) ζ)
      rw [h1]
      have h0 : (fun ζ => Ys (((0 : ℝ≥0)) : ℝ) ζ) = Y 0 := funext fun ζ => by
        simpa using hs.init ζ
      rw [h0]
      have h := hF.progressive.adapted t
      have e : ofNNRealTime Y t = Y 0 := by
        funext ζ
        simp [ofNNRealTime_apply, h1]
      rw [e] at h
      exact h
  refine ⟨⟨hF.brownian, hF.coords, fun t => (hs.adapted (t : ℝ)).mono (le_of_eq (p4r_shiftFil_nnreal ℱ t)) le_rfl, ?_⟩, hcontR, ?_⟩
  · exact (StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => (hadR t).stronglyMeasurable)
      (fun ζ => continuous_ofNNRealTime _ ζ (hcontR ζ))).isProgressive
  · filter_upwards [hs.eq, hF.coords] with ζ h hc t ht
    obtain ⟨hint, heq⟩ := h (t : ℝ) t.2 (WithTop.coe_lt_top _)
    have hcoordsT : ∀ i j, W' t ζ (i, j) = W t ζ i j - W 0 ζ i j := fun i j => by
      rw [hc t i j, ← hc 0 i j, hF.brownian.zero ζ]
      simp
    have heq' : Ys (t : ℝ) ζ = Ys 0 ζ + (∫ r in Set.Icc (0 : ℝ) t, b r (Ys r ζ)) +
        ∑ k : Fin N × Fin d, W' t ζ k • p4r_sigma d N ν k := by
      rw [heq]
      have : ofNNRealTime W' (t : ℝ) ζ = W' t ζ := by
        simp [ofNNRealTime_apply]
      rw [this, show Ys 0 ζ = Y 0 ζ from hs.init ζ]
    obtain ⟨hi, he⟩ := p4r_vec_to_comp ν (Ys (t : ℝ) ζ) (Ys 0 ζ) (fun r => b r (Ys r ζ))
      (Set.Icc 0 (t : ℝ)) hint (W t ζ) (W 0 ζ) (W' t ζ) hcoordsT heq'
    have hnn : ∀ r ∈ Set.Icc (0 : ℝ) t, Ys ((Real.toNNReal r : ℝ≥0) : ℝ) ζ = Ys r ζ :=
      fun r hr => by rw [Real.coe_toNNReal _ hr.1]
    refine ⟨fun i => (hi i).congr_fun (fun r hr => by simp only [hnn r hr]) measurableSet_Icc,
      fun i => ?_⟩
    have hI : ∫ r in Set.Icc (0 : ℝ) t, b r (Ys ((Real.toNNReal r : ℝ≥0) : ℝ) ζ) i =
        ∫ r in Set.Icc (0 : ℝ) t, b r (Ys r ζ) i :=
      setIntegral_congr_fun measurableSet_Icc fun r hr => by simp only [hnn r hr]
    simp only [NNReal.coe_zero]
    rw [hI]
    exact he i

/-! ### Drift agreement, separation, and the pathwise identification -/

theorem p4r_drift_eq {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (N : ℕ) (τ : ℝ)
    (Ξ : EucConfig d N) (hΞ : ∀ i j, i ≠ j → r₀ < ‖Ξ i - Ξ j‖) :
    p4Drift k s N τ Ξ = ssDrift d s N τ Ξ := by
  have hg : ∀ x : Euc d, r₀ < ‖x‖ → gradient k x = rieszKernelGrad d s x := by
    intro x hx
    have hev : k =ᶠ[𝓝 x] rieszKernel d s := by
      have : {y : Euc d | r₀ < ‖y‖} ∈ 𝓝 x :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds hx
      filter_upwards [this] with y hy using hk.eq_far y hy.le
    unfold rieszKernelGrad gradient
    rw [hev.fderiv_eq]
  have hs : ∀ i, ∑ j ∈ Finset.univ.erase i, gradient k (Ξ i - Ξ j) =
      ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d s (Ξ i - Ξ j) := fun i =>
    Finset.sum_congr rfl fun j hj => hg _ (hΞ i j (Finset.ne_of_mem_erase hj).symm)
  funext i
  simp only [p4Drift, ssDrift, hs i]

theorem p4r_isPathSolution (ν S : ℝ) (b : ℝ → EucConfig d N → EucConfig d N)
    (y : ℝ≥0 → EucConfig d N) (hy : Continuous y) (w' : ℝ≥0 → Fin N × Fin d → ℝ)
    (w : ℝ≥0 → Fin N → Euc d) (hc : ∀ t i j, w' t (i, j) = w t i j) (h0 : w' 0 = 0)
    (heqn : ∀ t : ℝ≥0, (t : ℝ) ≤ S →
      (∀ i, IntegrableOn (fun r : ℝ => b r (y (Real.toNNReal r)) i) (Set.Icc 0 (t : ℝ))) ∧
      ∀ i, y t i = y 0 i + (∫ r in Set.Icc (0 : ℝ) t, b r (y (Real.toNNReal r)) i) +
        Real.sqrt (2 * ν) • (w t i - w 0 i)) :
    IsPathSolution b (p4r_sigma d N ν) w' (y 0) (S : WithTop ℝ) (fun r => y (Real.toNNReal r)) := by
  refine ⟨by simp, fun t ht htS => ?_⟩
  have htS' : t ≤ S := by exact_mod_cast htS.le
  have hcw : ∀ i j, w' (Real.toNNReal t) (i, j) = w (Real.toNNReal t) i j - w 0 i j := by
    intro i j
    rw [hc, ← hc 0 i j, h0]
    simp
  have hle : ((Real.toNNReal t : ℝ≥0) : ℝ) ≤ S := by rw [Real.coe_toNNReal _ ht]; exact htS'
  obtain ⟨hint, he⟩ := heqn (Real.toNNReal t) hle
  rw [Real.coe_toNNReal _ ht] at hint he
  have hvec := p4r_comp_to_vec ν (y (Real.toNNReal t)) (y 0) (fun r => b r (y (Real.toNNReal r)))
    (Set.Icc 0 t) hint (w (Real.toNNReal t)) (w 0) (w' (Real.toNNReal t)) hcw he
  refine ⟨(hy.comp continuous_real_toNNReal).continuousOn, integrable_pi_iff.2 hint, ?_⟩
  simpa using hvec

theorem p4r_eqn_congr {ν S : ℝ} {b b' : ℝ → EucConfig d N → EucConfig d N}
    {y : ℝ≥0 → EucConfig d N} {w : ℝ≥0 → Fin N → Euc d}
    (hagree : ∀ r ∈ Set.Icc (0 : ℝ) S, b' r (y (Real.toNNReal r)) = b r (y (Real.toNNReal r)))
    (heqn : ∀ t : ℝ≥0, (t : ℝ) ≤ S →
      (∀ i, IntegrableOn (fun r : ℝ => b r (y (Real.toNNReal r)) i) (Set.Icc 0 (t : ℝ))) ∧
      ∀ i, y t i = y 0 i + (∫ r in Set.Icc (0 : ℝ) t, b r (y (Real.toNNReal r)) i) +
        Real.sqrt (2 * ν) • (w t i - w 0 i)) :
    ∀ t : ℝ≥0, (t : ℝ) ≤ S →
      (∀ i, IntegrableOn (fun r : ℝ => b' r (y (Real.toNNReal r)) i) (Set.Icc 0 (t : ℝ))) ∧
      ∀ i, y t i = y 0 i + (∫ r in Set.Icc (0 : ℝ) t, b' r (y (Real.toNNReal r)) i) +
        Real.sqrt (2 * ν) • (w t i - w 0 i) := by
  intro t ht
  obtain ⟨hi, he⟩ := heqn t ht
  have hr : ∀ r ∈ Set.Icc (0 : ℝ) t, r ∈ Set.Icc (0 : ℝ) S := fun r hr => ⟨hr.1, hr.2.trans ht⟩
  refine ⟨fun i => (hi i).congr_fun (fun r hr' => by rw [hagree r (hr r hr')])
    measurableSet_Icc, fun i => ?_⟩
  have hI : ∫ r in Set.Icc (0 : ℝ) t, b' r (y (Real.toNNReal r)) i =
      ∫ r in Set.Icc (0 : ℝ) t, b r (y (Real.toNNReal r)) i :=
    setIntegral_congr_fun measurableSet_Icc fun r hr' => by rw [hagree r (hr r hr')]
  rw [hI]
  exact he i

theorem p4r_sep {S : ℝ} (hS : 0 < S) {y : ℝ≥0 → EucConfig d N} (hy : Continuous y)
    (hne : ∀ t : ℝ≥0, (t : ℝ) ≤ S → ∀ i j, i ≠ j → y t i ≠ y t j) :
    ∀ᶠ M : ℕ in atTop, ∀ i j, i ≠ j → ∀ t : ℝ≥0, (t : ℝ) ≤ S →
      1 / ((M : ℝ) + 1) < ‖y t i - y t j‖ := by
  have hK : IsCompact (Set.Icc (0 : ℝ≥0) S.toNNReal) := isCompact_Icc
  have hle : ∀ t : ℝ≥0, (t : ℝ) ≤ S ↔ t ∈ Set.Icc (0 : ℝ≥0) S.toNNReal := fun t => by
    rw [Set.mem_Icc]
    simp [Real.le_toNNReal_iff_coe_le hS.le]
  refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun M h => absurd hij h
  · have hcont : Continuous fun t => ‖y t i - y t j‖ :=
      ((continuous_apply i).comp hy).sub ((continuous_apply j).comp hy) |>.norm
    obtain ⟨t₀, ht₀, hmin⟩ := hK.exists_isMinOn ⟨0, by simp⟩ hcont.continuousOn
    have hδ : 0 < ‖y t₀ i - y t₀ j‖ :=
      norm_pos_iff.2 (sub_ne_zero.2 (hne t₀ ((hle t₀).2 ht₀) i j hij))
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    filter_upwards [Filter.eventually_ge_atTop n] with M hM _ t ht
    have h1 : 1 / ((M : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      gcongr
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le hn (isMinOn_iff.1 hmin t ((hle t).1 ht)))

/-! ### The identification `Y^M = Y` on `[0,S]` for large `M`, and the theorem -/

theorem p4r_ident (s : ℝ) {N : ℕ} (invβ : ℝ) {S : ℝ} (hS : 0 < S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → EucConfig d N}
    (hY : SSAddSol P invβ (ssDrift d s N) S ℱ W' W Y) (hnc : SSNoCollision P S Y)
    {gM : ℕ → Euc d → ℝ} (hgM : ∀ M : ℕ, IsP4Kernel d s (1 / ((M : ℝ) + 1)) (gM M))
    {Ys : ℕ → ℝ → Ω → EucConfig d N}
    (hYs : ∀ M, IsAdditiveSDESolution P (p4r_shiftFil ℱ) W' (p4Drift (gM M) s N)
      (p4r_sigma d N invβ) (Y 0) (fun _ => ⊤) (Ys M)) :
    ∀ᵐ ζ ∂P, ∀ᶠ M : ℕ in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ S → Ys M (t : ℝ) ζ = Y t ζ := by
  have hF := hY.filtered
  have hpaths : ∀ᵐ ζ ∂P, ∀ M, IsPathSolution (p4Drift (gM M) s N) (p4r_sigma d N invβ)
      (fun t => W' t ζ) (Y 0 ζ) ⊤ (fun t => Ys M t ζ) :=
    ae_all_iff.2 fun M => (hYs M).isPathSolution
  filter_upwards [hY.eqn, hnc, hF.coords, hpaths] with ζ heqn hnoc hcoord hpath
  have hsep := p4r_sep hS (hY.cont ζ) (fun t ht i j hij hEq => hnoc t ht ⟨i, j, hij, hEq⟩)
  filter_upwards [hsep] with M hM
  have hagree : ∀ r ∈ Set.Icc (0 : ℝ) S, p4Drift (gM M) s N r (Y (Real.toNNReal r) ζ) =
      ssDrift d s N r (Y (Real.toNNReal r) ζ) := fun r hr =>
    p4r_drift_eq (hgM M) N r _ (fun i j hij => hM i j hij (Real.toNNReal r)
      (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2))
  have hyM := p4r_isPathSolution invβ S (p4Drift (gM M) s N) (fun t => Y t ζ) (hY.cont ζ)
    (fun t => W' t ζ) (fun t => W t ζ) (fun t i j => hcoord t i j) (funext fun k => by
      simpa using congrFun (hF.brownian.zero ζ) k) (p4r_eqn_congr (b := ssDrift d s N) (y := fun t => Y t ζ) (w := fun t => W t ζ) hagree heqn)
  have hu := ode_additive_unique Set.univ isOpen_univ (p4Drift (gM M) s N)
    (p4r_isLipschitzDrift (hgM M) N).toLoc (p4r_sigma d N invβ) (fun t => W' t ζ)
    (hF.brownian.cont ζ) (Y 0 ζ) hyM (hpath M) (fun _ _ _ => trivial) (fun _ _ _ => trivial)
  have hEq : Set.EqOn (fun u : ℝ => Ys M u ζ) (fun u : ℝ => Y (Real.toNNReal u) ζ) (Set.Ico 0 S) :=
    fun u hu0 => (hu u hu0.1 (by simpa using hu0.2)).symm
  have hc1 : ContinuousOn (fun u : ℝ => Ys M u ζ) (Set.Icc 0 S) :=
    (hYs M).cont ζ S hS.le (WithTop.coe_lt_top S)
  have hc2 : ContinuousOn (fun u : ℝ => Y (Real.toNNReal u) ζ) (Set.Icc 0 S) :=
    ((hY.cont ζ).comp continuous_real_toNNReal).continuousOn
  have hEq' := Set.EqOn.of_subset_closure hEq hc1 hc2 Set.Ico_subset_Icc_self
    (by rw [closure_Ico hS.ne])
  intro t ht
  have := hEq' ⟨NNReal.coe_nonneg t, ht⟩
  simpa using this

theorem p4_regularised_flow_proof (s : ℝ) {N : ℕ} (invβ : ℝ) (hβ : 0 < invβ) {S : ℝ} (hS : 0 < S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → EucConfig d N}
    (hY : SSAddSol P invβ (ssDrift d s N) S ℱ W' W Y) (hnc : SSNoCollision P S Y)
    {gM : ℕ → Euc d → ℝ} (hgM : ∀ M : ℕ, IsP4Kernel d s (1 / ((M : ℝ) + 1)) (gM M)) :
    ∃ YM : ℕ → ℝ≥0 → Ω → EucConfig d N,
      (∀ M, P4AddSol P invβ (p4Drift (gM M) s N) S ℱ W' W (YM M)) ∧
      (∀ M ζ, YM M 0 ζ = Y 0 ζ) ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ A : Set (EucConfig d N), MeasurableSet A →
        Tendsto (fun M => law P (YM M (Real.toNNReal τ)) A) atTop
          (𝓝 (law P (Y (Real.toNNReal τ)) A)) := by
  have hF := hY.filtered
  have hW' : IsBrownianFiltration P (p4r_shiftFil ℱ) W' := p4r_shiftFil_brownian hF.brownian
  have hY0 : ∀ t : ℝ, Measurable[p4r_shiftFil ℱ t] (Y 0) := fun t =>
    (hF.adapted 0).mono (ℱ.mono (le_max_right t 0)) le_rfl
  have hex : ∀ M : ℕ, ∃ Ys : ℝ → Ω → EucConfig d N,
      IsAdditiveSDESolution P (p4r_shiftFil ℱ) W' (p4Drift (gM M) s N) (p4r_sigma d N invβ)
        (Y 0) (fun _ => ⊤) Ys := fun M =>
    exists_sde_solution_global_exists hW' _ (p4r_isLipschitzDrift (hgM M) N) _ hY0
  choose Ys hYs using hex
  have hae := p4r_ident s invβ hS P hY hnc hgM hYs
  refine ⟨fun M t ζ => Ys M (t : ℝ) ζ, fun M => p4r_addSol hF (hYs M),
    fun M ζ => (hYs M).init ζ, ?_⟩
  intro τ hτ A hA
  have hτS : ((Real.toNNReal τ : ℝ≥0) : ℝ) ≤ S := by rw [Real.coe_toNNReal _ hτ.1]; exact hτ.2
  have hmeas : ∀ M, Measurable fun ζ => Ys M ((Real.toNNReal τ : ℝ≥0) : ℝ) ζ := fun M =>
    ((hYs M).adapted _).mono ((p4r_shiftFil ℱ).le _) le_rfl
  have hmY : Measurable (Y (Real.toNNReal τ)) := (hF.adapted _).mono (ℱ.le _) le_rfl
  simp only [Measure.map_apply (hmeas _) hA, Measure.map_apply hmY hA]
  refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop (hmY hA)
    (fun M => hmeas M hA) ?_
  filter_upwards [hae] with ζ h
  filter_upwards [h] with M hM
  simp only [Set.mem_preimage, hM _ hτS]

example := (@p4_regularised_flow_proof : type_of% @HRS.MP.SelfSimP4.p4_regularised_flow)

end HRS.MP.SelfSimP4Impl
