import HRS.MC.CepE6E11

/-!
# Packet CEPE6E, file 12: conjunct (e) of `cep_E6_limit_solution`

From the fixed-rational-time statement `cepe6e_R_zero` to all times by continuity of both sides.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6E

open HRS HRS.MC.Cepa HRS.MC.CepE4 HRS.MC.CepE5b HRS.MC.CepE6D HRS.MC.CepE6A

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- A function continuous on `[0,T]` that vanishes at all rationals of `[0,T]` vanishes on `[0,T)`. -/
theorem cepe6e_eq_zero_of_rat {E : Type*} [NormedAddCommGroup E] {g : ℝ → E} {T : ℝ}
    (hg : ContinuousOn g (Icc 0 T)) (hq : ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ T → g q = 0)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) : g t = 0 := by
  have hex : ∀ n : ℕ, ∃ q : ℚ, t < (q : ℝ) ∧ (q : ℝ) < min T (t + 1 / ((n : ℝ) + 1)) := fun n =>
    exists_rat_btwn (lt_min htT (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                                    linarith))
  choose q hq1 hq2 using hex
  have hqt : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 t) := by
    have h1 : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) atTop (𝓝 (t + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun n => (hq1 n).le)
      (fun n => ((hq2 n).trans_le (min_le_right _ _)).le)
  have hqin : ∀ n, (q n : ℝ) ∈ Icc 0 T := fun n =>
    ⟨ht0.trans (hq1 n).le, ((hq2 n).trans_le (min_le_left _ _)).le⟩
  have hcw : ContinuousWithinAt g (Icc 0 T) t := hg t ⟨ht0, htT.le⟩
  have hlim : Tendsto (fun n => g (q n)) atTop (𝓝 (g t)) :=
    hcw.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hqt, Eventually.of_forall hqin⟩)
  have h0 : ∀ n, g (q n) = 0 := fun n => hq (q n) (hqin n).1 (hqin n).2
  simp only [h0] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- **Conjunct (e)** of `cep_E6_limit_solution`, for the limit `Zl` of conjuncts (a)–(d). -/
theorem cepe6e_conjunct_e [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    (hz₀b : ∃ R : ℝ, ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n))
    {Zl : ℝ → Ω → Ch N} (hZlc : ∀ ω, Continuous fun t => Zl t ω)
    (hZlm : ∀ t, 0 ≤ t → Measurable[ℱ t] (Zl t))
    (hprob : ∀ T : ℝ, ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun n : ℕ =>
        P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl t ω‖}) Filter.atTop (𝓝 0))
    (hcl : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → Zl t ω ∈ closure (cep_Alcove N))
    (hnull : ∀ᵐ ω ∂P, ∀ T : ℝ, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0)
    (hgi : ∀ᵐ ω ∂P, ∀ T : ℝ, IntegrableOn
      (fun s : ℝ => ‖gradient (cep_chamberPot a N) (Zl s ω)‖) (Set.Icc 0 T))
    (hinv : ∀ᵐ ω ∂P, ∀ T : ℝ, IntegrableOn (fun s : ℝ => ∑ k : Fin N, ∑ l : Fin N,
      (if k < l then 1 / min (Zl s ω l - Zl s ω k) (1 - (Zl s ω l - Zl s ω k)) else 0)) (Set.Icc 0 T)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Zl t ω = z₀ ω +
      (∫ s in (0 : ℝ)..t, (-(gradient (cep_chamberPot a N) (Zl s ω)) + F (Zl s ω))) +
        σ' • cep_noise π W' t ω := by
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    refine Eventually.of_forall fun ω t _ => ?_
    ext i
    exact i.elim0
  have hN1 : 1 ≤ N := hN
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → z₀ ω + (∫ s in (0 : ℝ)..(q : ℝ), F (Zl s ω)) +
      σ' • cep_noise π W' (q : ℝ) ω - Zl (q : ℝ) ω =
      ∫ s in (0 : ℝ)..(q : ℝ), gradient (cep_chamberPot a N) (Zl s ω) := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 ≤ (q : ℝ)
    · filter_upwards [cepe6e_R_zero hW' hπ ha hJ hF σ' hz₀ hz₀A hz₀b hZ hZlc hZlm hprob hcl hnull hgi
        hinv hN1 hq] with ω h _ using h
    · exact Eventually.of_forall fun ω h => absurd h hq
  filter_upwards [hrat, hgi] with ω hr hg t ht
  have hFc : Continuous fun s => F (Zl s ω) := hF.continuous.comp (hZlc ω)
  have hGint : ∀ T : ℝ, 0 ≤ T → IntegrableOn (fun s => gradient (cep_chamberPot a N) (Zl s ω)) (Icc 0 T) := by
    intro T hT
    exact (integrable_norm_iff
      (((e6a_gradient_measurable a).comp (hZlc ω).measurable).aestronglyMeasurable)).1 (hg T)
  set g : ℝ → Ch N := fun s => z₀ ω + (∫ u in (0 : ℝ)..s, F (Zl u ω)) +
    σ' • cep_noise π W' s ω - Zl s ω - ∫ u in (0 : ℝ)..s, gradient (cep_chamberPot a N) (Zl u ω) with hgdef
  have hgc : ContinuousOn g (Icc 0 (t + 1)) := by
    have h1 : Continuous fun s => ∫ u in (0 : ℝ)..s, F (Zl u ω) := by
      exact intervalIntegral.continuous_primitive (fun a b => hFc.intervalIntegrable a b) 0
    have h2 : Continuous fun s : ℝ => cep_noise π W' s ω := e4_noise_cont hW'.cont π ω
    have h3 : ContinuousOn (fun s => ∫ u in (0 : ℝ)..s, gradient (cep_chamberPot a N) (Zl u ω))
        (Icc 0 (t + 1)) := by
      have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := t + 1) (μ := volume)
        (f := fun u => gradient (cep_chamberPot a N) (Zl u ω))
        (by rw [uIcc_of_le (by linarith)]; exact hGint (t + 1) (by linarith))
      rwa [uIcc_of_le (by linarith)] at this
    exact ((((continuous_const.add h1).add (h2.const_smul σ')).sub (hZlc ω)).continuousOn).sub h3
  have hg0 : g t = 0 := by
    refine cepe6e_eq_zero_of_rat hgc (fun q hq0 _ => ?_) ht (by linarith)
    simp only [hgdef]
    rw [hr q hq0]; exact sub_self _
  simp only [hgdef] at hg0
  have hGt : IntervalIntegrable (fun s => gradient (cep_chamberPot a N) (Zl s ω)) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht]; exact hGint t ht
  rw [intervalIntegral.integral_add (f := fun s => -(gradient (cep_chamberPot a N) (Zl s ω)))
    (g := fun s => F (Zl s ω)) hGt.neg (hFc.intervalIntegrable 0 t), intervalIntegral.integral_neg]
  have := sub_eq_zero.1 hg0
  rw [← this]
  abel

end HRS.MC.CepE6E
