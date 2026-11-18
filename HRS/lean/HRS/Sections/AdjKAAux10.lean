import HRS.Sections.AdjKAAux9

/-!
# ADJKA part 10: splitting the stochastic convolution into a finite-rank `E_j` part and an `E_m` tail
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjka_lintegral_trace_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T B : ℝ} (hT : 0 < T) (hB : 0 ≤ B) (f : ℝ → Ω → ℝ) (hf : ∀ u ω, f u ω ≤ B) {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ ω, (∫⁻ u in Icc 0 T, ENNReal.ofReal (f u ω)) ^ r ∂P ≤ ENNReal.ofReal ((T * B) ^ r) := by
  have h1 : ∀ ω, ∫⁻ u in Icc 0 T, ENNReal.ofReal (f u ω) ≤ ENNReal.ofReal (T * B) := fun ω => by
    calc ∫⁻ u in Icc 0 T, ENNReal.ofReal (f u ω) ≤ ∫⁻ _u in Icc 0 T, ENNReal.ofReal B :=
          lintegral_mono fun u => ENNReal.ofReal_le_ofReal (hf u ω)
      _ = ENNReal.ofReal B * ENNReal.ofReal T := by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc,
            sub_zero]
      _ = ENNReal.ofReal (T * B) := by rw [mul_comm (ENNReal.ofReal B), ← ENNReal.ofReal_mul hT.le]
  calc ∫⁻ ω, (∫⁻ u in Icc 0 T, ENNReal.ofReal (f u ω)) ^ r ∂P
      ≤ ∫⁻ _ω, (ENNReal.ofReal (T * B)) ^ r ∂P := lintegral_mono fun ω => ENNReal.rpow_le_rpow (h1 ω) hr
    _ = ENNReal.ofReal ((T * B) ^ r) := by
        rw [lintegral_const, measure_univ, mul_one, ENNReal.ofReal_rpow_of_nonneg (by positivity) hr]


theorem adjka_decomp (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (j : ℕ)
    (hj : (d : ℝ) + 2 ≤ j) (m : ℝ) (hjm : (j : ℝ) + 2 ≤ m) (T : ℝ) (hT : 0 < T) (p : ℝ) (hp : 2 ≤ p) :
    ∃ CB C2 : ℝ, 0 ≤ CB ∧ 0 ≤ C2 ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ) (μ : ℝ → Ω → Measure (Torus d)) (_ : ∀ r ω, IsProbabilityMeasure (μ r ω))
        (M : ℝ → Ω → NegSobolev d m),
        IsHilbertMartingaleWithCovariation P ℱ T M (fun r ω => covForm m β⁻¹ (μ r ω)) →
        ∀ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
          IsDualEvolution htr.dyn ρ m Vev →
          ∀ Z : ℝ → Ω → NegSobolev d m,
            (∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M 0 t (Z t)) →
            (∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Z t) P) →
            ∀ (S : Finset (NonzeroLattice d)) (ε : ℝ), 0 ≤ ε →
              (∀ k : NonzeroLattice d, k ∉ S → Lattice.jp k.1 ^ (-(2 * (m - (j : ℝ)))) ≤ ε) →
              ∃ (ZS : ℝ → Ω → NegSobolev d (j : ℝ)) (Zc : ℝ → Ω → NegSobolev d m),
                (∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (ZS t) P) ∧
                (∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Zc t) P) ∧
                (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
                  Z t ω = NegSobolev.embed m (ZS t ω) + Zc t ω) ∧
                ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖ZS t ω‖ₑ) ^ p ∂P ≤
                  ENNReal.ofReal (CB * (T * ((d : ℝ) * (2 * β⁻¹ * (2 * Q14.q14S d ((j : ℝ) - 1))))) ^ (p / 2)) ∧
                ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Zc t ω‖ₑ) ^ (2 : ℝ) ∂P ≤
                  ENNReal.ofReal (C2 * (T * ((d : ℝ) * (2 * β⁻¹ * (ε * (2 * Q14.q14S d ((j : ℝ) - 1))))))) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hj2 : (d : ℝ) / 2 + 2 < j := by linarith
  have hm2 : (d : ℝ) / 2 + 2 < m := by linarith
  have hjm' : (j : ℝ) ≤ m := by linarith
  have hq : 0 ≤ β⁻¹ := (inv_pos.2 htr.hβ).le
  obtain ⟨Vj, hVj, hVjp, hBj⟩ := adjk_evolution_moment_proof hd htr (j : ℝ) p hp
  obtain ⟨CB, hCB, hBj'⟩ := hBj T hT
  obtain ⟨Vm', hVm', hVmp, hBm⟩ := adjk_evolution_moment_proof hd htr m 2 le_rfl
  obtain ⟨C2, hC2, hBm'⟩ := hBm T hT
  refine ⟨CB, C2, hCB, hC2, ?_⟩
  intro Ω mΩ P _ ℱ μ hμ M hM Vev hVev Z hZ hZm S ε hε0 hε
  have hS0 : 0 ≤ Q14.q14S d ((j : ℝ) - 1) := Q14.q14S_nonneg d _
  set ι := adjkEmb d hjm' with hι
  set R := adjkR m (j : ℝ) S with hR
  set Lc : NegSobolev d m →L[ℝ] NegSobolev d m :=
    ContinuousLinearMap.id ℝ (NegSobolev d m) - adjkP m S with hLc
  have hMS := adjka_isHMC_map hM R
  have hNc := adjka_isHMC_map hM Lc
  -- trace bounds
  have hc2 : Real.sqrt (2 * β⁻¹) ^ 2 = 2 * β⁻¹ := Real.sq_sqrt (by positivity)
  have htrR : ∀ σ ω, traceNormForm (Kot.formComp (ContinuousLinearMap.adjoint R)
      (covForm m β⁻¹ (μ σ ω))) ≤ (d : ℝ) * (2 * β⁻¹ * (2 * Q14.q14S d ((j : ℝ) - 1))) := by
    intro σ ω
    haveI := hμ σ ω
    refine adjka_trace_family hm2 hq (μ σ ω) R _ (by positivity) fun l a => ?_
    rw [map_smul, norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _), hc2]
    exact mul_le_mul_of_nonneg_left (adjka_normR_le hj2 hm2 S l a) (by positivity)
  have htrC : ∀ σ ω, traceNormForm (Kot.formComp (ContinuousLinearMap.adjoint Lc)
      (covForm m β⁻¹ (μ σ ω))) ≤ (d : ℝ) * (2 * β⁻¹ * (ε * (2 * Q14.q14S d ((j : ℝ) - 1)))) := by
    intro σ ω
    haveI := hμ σ ω
    refine adjka_trace_family hm2 hq (μ σ ω) Lc _ (by positivity) fun l a => ?_
    rw [map_smul, norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _), hc2]
    exact mul_le_mul_of_nonneg_left (adjka_normTail_le hj2 hm2 S hε0 hε l a) (by positivity)
  -- B1 at level j for `R M`
  have hMS' : IsHilbertMartingaleWithCovariation P ℱ (0 + T) (fun τ ω => R (M τ ω))
      (fun σ ω => Kot.formComp (ContinuousLinearMap.adjoint R) (covForm m β⁻¹ (μ σ ω))) := by
    rw [zero_add]; exact hMS
  obtain ⟨ZS, hZSconv, hZScont, hZSmeas, hZSbd⟩ := hBj' Ω P ℱ 0 T le_rfl hT le_rfl
    (fun τ ω => R (M τ ω)) _ hMS'
  have hNc' : IsHilbertMartingaleWithCovariation P ℱ (0 + T) (fun τ ω => Lc (M τ ω))
      (fun σ ω => Kot.formComp (ContinuousLinearMap.adjoint Lc) (covForm m β⁻¹ (μ σ ω))) := by
    rw [zero_add]; exact hNc
  obtain ⟨Zc, hZcconv, hZccont, hZcmeas, hZcbd⟩ := hBm' Ω P ℱ 0 T le_rfl hT le_rfl
    (fun τ ω => Lc (M τ ω)) _ hNc'
  simp only [zero_add] at hZSconv hZScont hZSmeas hZSbd hZcconv hZccont hZcmeas hZcbd
  refine ⟨ZS, Zc, hZSmeas, hZcmeas, ?_, ?_, ?_⟩
  · intro t ht
    have hMt : ∀ τ ∈ Icc (0 : ℝ) t, AEStronglyMeasurable (M τ) P := fun τ hτ =>
      (hM.sq_int τ ⟨hτ.1, hτ.2.trans ht.2⟩).aestronglyMeasurable
    have h1 : IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m))
        (fun τ ω => ι (R (M τ ω))) 0 t (fun ω => ι (ZS t ω)) := by
      refine adjka_isStochConv_embed ι (adjkEmb_norm_le hjm') ?_ (hZSconv t ht)
      intro s' hs' hst x
      exact adjka_dual_embed hjm' hVj hVev hs' hst x
    have h2 : IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m))
        (fun τ ω => Lc (M τ ω)) 0 t (Zc t) := by
      refine adjka_isStochConv_congr_ev ?_ (hZcconv t ht)
      intro s' hs' hst
      exact adjka_dual_unique hVm' hVev hs' hst
    have hm1 : ∀ τ ∈ Icc (0 : ℝ) t, AEStronglyMeasurable (fun ω => ι (R (M τ ω))) P := fun τ hτ =>
      ι.continuous.comp_aestronglyMeasurable
        (hMS.sq_int τ ⟨hτ.1, hτ.2.trans ht.2⟩).aestronglyMeasurable
    have hm2' : ∀ τ ∈ Icc (0 : ℝ) t, AEStronglyMeasurable (fun ω => Lc (M τ ω)) P := fun τ hτ =>
      (hNc.sq_int τ ⟨hτ.1, hτ.2.trans ht.2⟩).aestronglyMeasurable
    have h3 := adjka_isStochConv_add (V := Vev) hm1 hm2' ((ι.continuous.measurable.comp_aemeasurable (hZSmeas t ht)))
      h1 h2
    have h4 : IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M 0 t
        (fun ω => ι (ZS t ω) + Zc t ω) := by
      refine adjka_isStochConv_congr_M (fun τ hτ ω => ?_) h3
      show ι (R (M τ ω)) + Lc (M τ ω) = M τ ω
      rw [hι, hR, adjka_emb_adjkR hjm', hLc, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
      abel
    have huniq := adjka_isStochConv_unique (V := Vev) ht.1 hMt (hZm t ht)
      ((ι.continuous.measurable.comp_aemeasurable (hZSmeas t ht)).add (hZcmeas t ht)) (hZ t ht) h4
    filter_upwards [huniq] with ω hω
    exact hω
  · refine hZSbd.trans ?_
    have hB0 : 0 ≤ (d : ℝ) * (2 * β⁻¹ * (2 * Q14.q14S d ((j : ℝ) - 1))) := by positivity
    have := adjka_lintegral_trace_le P hT hB0
      (fun u ω => traceNormForm (Kot.formComp (ContinuousLinearMap.adjoint R) (covForm m β⁻¹ (μ u ω))))
      htrR (r := p / 2) (by linarith)
    calc ENNReal.ofReal CB * ∫⁻ ω, (∫⁻ u in Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm
          (Kot.formComp (ContinuousLinearMap.adjoint R) (covForm m β⁻¹ (μ u ω))))) ^ (p / 2) ∂P
        ≤ ENNReal.ofReal CB * ENNReal.ofReal ((T * ((d : ℝ) * (2 * β⁻¹ * (2 * Q14.q14S d ((j : ℝ) - 1))))) ^ (p / 2)) :=
          mul_le_mul_of_nonneg_left this bot_le
      _ = _ := by rw [← ENNReal.ofReal_mul hCB]
  · refine hZcbd.trans ?_
    have hB0 : 0 ≤ (d : ℝ) * (2 * β⁻¹ * (ε * (2 * Q14.q14S d ((j : ℝ) - 1)))) := by positivity
    have := adjka_lintegral_trace_le P hT hB0
      (fun u ω => traceNormForm (Kot.formComp (ContinuousLinearMap.adjoint Lc) (covForm m β⁻¹ (μ u ω))))
      htrC (r := (2 : ℝ) / 2) (by norm_num)
    rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one] at this
    simp only [show (2 : ℝ) / 2 = 1 by norm_num, ENNReal.rpow_one] at hZcbd this ⊢
    calc ENNReal.ofReal C2 * ∫⁻ ω, (∫⁻ u in Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm
          (Kot.formComp (ContinuousLinearMap.adjoint Lc) (covForm m β⁻¹ (μ u ω))))) ∂P
        ≤ ENNReal.ofReal C2 * ENNReal.ofReal (T * ((d : ℝ) * (2 * β⁻¹ * (ε * (2 * Q14.q14S d ((j : ℝ) - 1)))))) :=
          mul_le_mul_of_nonneg_left this bot_le
      _ = _ := by rw [← ENNReal.ofReal_mul hC2]

end HRS.AdjK
