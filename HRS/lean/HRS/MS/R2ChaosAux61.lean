import HRS.MS.R2ChaosAux60

/-!
# HRS.MS.R2ChaosAux61 -- S9.6 (P5): conclusion (iii) for polynomial kernels

Packet S94 (S9.6), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.  Copy of `s94_part_iii` with `s94_pmoment_y` and `s94_pquad_ae_memLp`
(only `N ≥ 2` enters, the statement is asymptotic in `N`); `(i)` is an input.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole HRS.MS.R2Poly

variable {d : ℕ}

section PartIIIPoly

variable {s T b p K M L C₀ c₀ Pw : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_part_iii_poly (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ) (hG : HasR2GaussianUpper C₀ c₀ ρ) (hPw : 0 ≤ Pw)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) (hT : 0 < T) {B : ℝ} (hB : 0 ≤ B)
    {h : ℝ → Euc d → Euc d → ℝ} (hmeas : Measurable fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2)
    (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsR2PolyPairKernel s Pw B (h t))
    {F : ℝ → Ω' → ℝ} (hF2 : ∀ ζ, MemLp (fun t => F t ζ) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    {k : ℕ} {aa : Fin k → Euc d → ℝ} (haa : ∀ i, IsR2Test (aa i))
    (hi : TendstoInDistribution
      (fun N ζ => (r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ),
        fun i => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ))) atTop
      (fun ζ' => (r2L2Path T (fun t => F t ζ'), fun i => ξ (aa i) ζ')) P P') :
    ∀ r : ℝ, 1 ≤ r → Tendsto (fun N => HRS.wassersteinE r
      (HRS.law (P N) fun ζ => ((fun i => r2L2Path T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ)),
        r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ),
        r2IntPath T (fun t => r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ)))
      (HRS.law P' fun ζ' => ((fun i => r2L2Path T (fun t => r2PathEval T (ξ (aa i) ζ') t)),
        r2L2Path T (fun t => F t ζ'), r2IntPath T (fun t => F t ζ'))))
      atTop (𝓝 0) := by
  intro r hr
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  let g : R2L2 T × (Fin k → C(Set.Icc (0 : ℝ) T, ℝ)) → PiLp 2 (fun _ : Fin (k + 1) => R2L2 T) :=
    fun x => s94_mkH T (fun i => s94_iota T (x.2 i)) x.1
  have hgc : Continuous g := by
    refine s94_mkH_continuous.comp (Continuous.prodMk (continuous_pi fun i => ?_) continuous_fst)
    exact (s94_iota_continuous hT.le).comp ((continuous_apply i).comp continuous_snd)
  have hg := hi.continuous_comp hgc
  let μ := Whole.withDensityReal ρ
  let Y1 : ∀ N : ℕ, Ω N → R2L2 T × (Fin k → C(Set.Icc (0 : ℝ) T, ℝ)) := fun N ζ =>
    (r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
      fun i => r2ContPath T (r2EmpFluct μ (aa i) (X N) ζ))
  let Z1 : Ω' → R2L2 T × (Fin k → C(Set.Icc (0 : ℝ) T, ℝ)) := fun ζ' =>
    (r2L2Path T (fun t => F t ζ'), fun i => ξ (aa i) ζ')
  let yN : ∀ N : ℕ, Ω N → PiLp 2 (fun _ : Fin (k + 1) => R2L2 T) := fun N ζ =>
    s94_mkH T (fun i => r2L2Path T (r2EmpFluct μ (aa i) (X N) ζ))
      (r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ))
  have hyae : ∀ N, (g ∘ Y1 N) =ᵐ[P N] yN N := by
    intro N
    filter_upwards [hset.contX N] with ζ hX
    show s94_mkH T (fun i => s94_iota T (r2ContPath T (r2EmpFluct μ (aa i) (X N) ζ)))
      (r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ)) = _
    congr 1
    funext i
    exact s94_iota_contPath (s94_empFluct_continuous μ (X N) (haa i) ζ hX)
  -- moments
  have hmom : ∀ q : ℝ, 2 ≤ q → ∃ Mq : ℝ, 0 ≤ Mq ∧ ∀ᶠ N in atTop,
      ∫⁻ x, ENNReal.ofReal (‖x‖ ^ q)
        ∂((⟨(P N).map (g ∘ Y1 N), inferInstance⟩ : ProbabilityMeasure (PiLp 2 (fun _ : Fin (k + 1) => R2L2 T))) :
          Measure (PiLp 2 (fun _ : Fin (k + 1) => R2L2 T))) ≤ ENNReal.ofReal Mq := by
    intro q hq
    obtain ⟨Mq, hMq0, hMq⟩ := s94_pmoment_y hd hs0 hs hb hp hρ hG hPw hset hT hB hmeas hker haa hq
    refine ⟨Mq, hMq0, ?_⟩
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hmeasn : Measurable fun x : PiLp 2 (fun _ : Fin (k + 1) => R2L2 T) => ENNReal.ofReal (‖x‖ ^ q) :=
      ENNReal.measurable_ofReal.comp (continuous_norm.measurable.pow_const q)
    show ∫⁻ x, ENNReal.ofReal (‖x‖ ^ q) ∂((P N).map (g ∘ Y1 N)) ≤ _
    rw [lintegral_map' hmeasn.aemeasurable (hg.forall_aemeasurable N)]
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (hMq N hN)
    filter_upwards [hyae N] with ζ hζ
    show ENNReal.ofReal (‖g (Y1 N ζ)‖ ^ q) = ENNReal.ofReal (‖yN N ζ‖ ^ q)
    have hζ' : g (Y1 N ζ) = yN N ζ := hζ
    rw [hζ']
  have hW := s94_wass_H _ _ hg.tendsto hmom hr
  -- the frozen laws are push-forwards by `L`
  let Lm := s94_Lmap (k := k) hT.le
  have hLm : Measurable Lm := Lm.continuous.measurable
  have hae : ∀ N, 2 ≤ N → ∀ᵐ ζ ∂(P N), MemLp (fun t => r2QuadFluct μ h (P N) (X N) t ζ) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) := fun N hN => s94_pquad_ae_memLp hd hs0 hs hb hp hρ hG hPw hset hB hmeas hker hN
  have hY3 : ∀ N, 2 ≤ N → (fun ζ => ((fun i => r2L2Path T (r2EmpFluct μ (aa i) (X N) ζ)),
        r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
        r2IntPath T (fun t => r2QuadFluct μ h (P N) (X N) t ζ))) =ᵐ[P N] Lm ∘ (g ∘ Y1 N) := by
    intro N hN
    filter_upwards [hae N hN, hyae N] with ζ hζ hy
    simp only [Function.comp_apply] at hy ⊢
    rw [hy]
    show _ = Lm (yN N ζ)
    simp only [yN, Lm, s94_Lmap_mkH]
    rw [s94_r2IntPath_eq hT.le hζ]
  have hZ3 : ∀ ζ', (((fun i => r2L2Path T (fun t => r2PathEval T (ξ (aa i) ζ') t)),
        r2L2Path T (fun t => F t ζ'), r2IntPath T (fun t => F t ζ'))) = Lm ((g ∘ Z1) ζ') := by
    intro ζ'
    show _ = Lm (s94_mkH T (fun i => s94_iota T (ξ (aa i) ζ')) (r2L2Path T (fun t => F t ζ')))
    simp only [Lm, s94_Lmap_mkH]
    rw [s94_r2IntPath_eq hT.le (hF2 ζ')]
    rfl
  have hlawN : ∀ N, 2 ≤ N → HRS.law (P N) (fun ζ => ((fun i => r2L2Path T (r2EmpFluct μ (aa i) (X N) ζ)),
        r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
        r2IntPath T (fun t => r2QuadFluct μ h (P N) (X N) t ζ))) =
      ((P N).map (g ∘ Y1 N)).map Lm := by
    intro N hN
    rw [HRS.law, Measure.map_congr (hY3 N hN), AEMeasurable.map_map_of_aemeasurable hLm.aemeasurable
      (hg.forall_aemeasurable N)]
  have hlawZ : HRS.law P' (fun ζ' => ((fun i => r2L2Path T (fun t => r2PathEval T (ξ (aa i) ζ') t)),
        r2L2Path T (fun t => F t ζ'), r2IntPath T (fun t => F t ζ'))) = (P'.map (g ∘ Z1)).map Lm := by
    rw [HRS.law, show (fun ζ' => ((fun i => r2L2Path T (fun t => r2PathEval T (ξ (aa i) ζ') t)),
        r2L2Path T (fun t => F t ζ'), r2IntPath T (fun t => F t ζ'))) = Lm ∘ (g ∘ Z1) from funext hZ3,
      AEMeasurable.map_map_of_aemeasurable hLm.aemeasurable hg.aemeasurable_limit]
  haveI : ∀ N, IsProbabilityMeasure ((P N).map (g ∘ Y1 N)) := fun N => inferInstance
  haveI : IsProbabilityMeasure (P'.map (g ∘ Z1)) := inferInstance
  have hbound : ∀ N, HRS.wassersteinE r (((P N).map (g ∘ Y1 N)).map Lm) ((P'.map (g ∘ Z1)).map Lm) ≤
      ENNReal.ofReal ‖Lm‖ * HRS.wassersteinE r ((P N).map (g ∘ Y1 N)) (P'.map (g ∘ Z1)) := fun N =>
    s94_wass_map_clm_le Lm r hr _ _
  have hfun : ∀ N, 2 ≤ N → HRS.wassersteinE r
      (HRS.law (P N) fun ζ => ((fun i => r2L2Path T (r2EmpFluct μ (aa i) (X N) ζ)),
        r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
        r2IntPath T (fun t => r2QuadFluct μ h (P N) (X N) t ζ)))
      (HRS.law P' fun ζ' => ((fun i => r2L2Path T (fun t => r2PathEval T (ξ (aa i) ζ') t)),
        r2L2Path T (fun t => F t ζ'), r2IntPath T (fun t => F t ζ'))) =
      HRS.wassersteinE r (((P N).map (g ∘ Y1 N)).map Lm) ((P'.map (g ∘ Z1)).map Lm) :=
    fun N hN => by rw [hlawN N hN, hlawZ]
  have hmul : Tendsto (fun N => ENNReal.ofReal ‖Lm‖ * HRS.wassersteinE r ((P N).map (g ∘ Y1 N))
      (P'.map (g ∘ Z1))) atTop (𝓝 (ENNReal.ofReal ‖Lm‖ * 0)) :=
    ENNReal.Tendsto.const_mul hW (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hmul
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul (Eventually.of_forall fun N => bot_le) ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [hfun N hN]
  exact hbound N

end PartIIIPoly

end HRS.MS.R2Chaos
