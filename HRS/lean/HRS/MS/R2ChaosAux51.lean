import HRS.MS.R2ChaosAux50

/-!
# HRS.MS.R2ChaosAux51 -- (iii): `r`-Wasserstein convergence for every `r ≥ 1`

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_part_iii`: with `H = (L²(dt))^{k+1}` the laws of `(ξ_N(a_1..a_k), B_N)` converge weakly (continuous image of (i) through `ι`)
with uniform moments of all orders (`s94_moment_y`), hence in `W_r` for all `r ≥ 1` (`s94_wass_H`); the frozen law on
`(L²)^k × L² × C([0,T])` is the push-forward by the continuous linear `L : H → B3`, `y ↦ (y_1..y_k, y_{k+1}, J y_{k+1})`
(`wassersteinE_map_clm_le`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

section MapClm

variable {B B' : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup B'] [NormedSpace ℝ B'] [MeasurableSpace B'] [BorelSpace B']

theorem s94_wass_map_clm_le (L : B →L[ℝ] B') (p : ℝ) (hp : 1 ≤ p) (P Q : Measure B)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    HRS.wassersteinE p (P.map L) (Q.map L) ≤ ENNReal.ofReal ‖L‖ * HRS.wassersteinE p P Q := by
  have hLm : Measurable L := L.continuous.measurable
  have hp0 : 0 < p := by linarith
  have hprod : Measurable (Prod.map L L) := hLm.prodMap hLm
  have key : ∀ π : Measure (B × B), HRS.IsCoupling π P Q →
      HRS.wassersteinE p (P.map L) (Q.map L) ≤
        ENNReal.ofReal ‖L‖ * (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π) ^ (1 / p) := by
    intro π hπ
    have hmap : HRS.IsCoupling (π.map (Prod.map L L)) (P.map L) (Q.map L) := by
      constructor
      · rw [Measure.map_map measurable_fst hprod, show (Prod.fst ∘ Prod.map L L) = L ∘ Prod.fst from rfl,
          ← Measure.map_map hLm measurable_fst, hπ.1]
      · rw [Measure.map_map measurable_snd hprod, show (Prod.snd ∘ Prod.map L L) = L ∘ Prod.snd from rfl,
          ← Measure.map_map hLm measurable_snd, hπ.2]
    refine (HRS.wassersteinE_le_cost (p := p) hmap).trans ?_
    refine (ENNReal.rpow_le_rpow (lintegral_map_le (fun z : B' × B' => ENNReal.ofReal (‖z.1 - z.2‖ ^ p))
      hprod.aemeasurable) (by positivity)).trans ?_
    have hpt : ∀ z : B × B, ENNReal.ofReal (‖L z.1 - L z.2‖ ^ p) ≤
        ENNReal.ofReal ‖L‖ ^ p * ENNReal.ofReal (‖z.1 - z.2‖ ^ p) := by
      intro z
      have h1 : ‖L z.1 - L z.2‖ ≤ ‖L‖ * ‖z.1 - z.2‖ := by
        rw [← map_sub]; exact L.le_opNorm _
      have h2 : ‖L z.1 - L z.2‖ ^ p ≤ (‖L‖ * ‖z.1 - z.2‖) ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) h1 hp0.le
      rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] at h2
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ← ENNReal.ofReal_mul
        (Real.rpow_nonneg (norm_nonneg _) _)]
      exact ENNReal.ofReal_le_ofReal h2
    calc (∫⁻ z, ENNReal.ofReal (‖L z.1 - L z.2‖ ^ p) ∂π) ^ (1 / p)
        ≤ (∫⁻ z, ENNReal.ofReal ‖L‖ ^ p * ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π) ^ (1 / p) :=
          ENNReal.rpow_le_rpow (lintegral_mono fun z => hpt z) (by positivity)
      _ = ENNReal.ofReal ‖L‖ * (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π) ^ (1 / p) := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top),
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
  have hne : Nonempty (HRS.couplings P Q) := by
    refine ⟨⟨P.prod Q, ?_, ?_⟩⟩
    · simp [Measure.map_fst_prod]
    · simp [Measure.map_snd_prod]
  calc HRS.wassersteinE p (P.map L) (Q.map L)
      ≤ ⨅ π : HRS.couplings P Q, ENNReal.ofReal ‖L‖ *
          (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π.1) ^ (1 / p) :=
        le_iInf fun π => key π.1 π.2
    _ = ENNReal.ofReal ‖L‖ * HRS.wassersteinE p P Q := by
        unfold HRS.wassersteinE
        rw [ENNReal.mul_iInf' (fun h => absurd h ENNReal.ofReal_ne_top) (fun _ => hne)]

end MapClm

theorem s94_iota_contPath {T : ℝ} {f : ℝ → ℝ} (hf : Continuous f) :
    s94_iota T (r2ContPath T f) = r2L2Path T f := by
  have hc : Continuous fun t : Set.Icc (0 : ℝ) T => f t := hf.comp continuous_subtype_val
  rw [s94_r2ContPath_eq hc]
  unfold s94_iota
  refine s94_r2L2Path_congr fun t ht => ?_
  unfold r2PathEval
  simp [ht]

section PartIII

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_part_iii (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) (hT : 0 < T) {B C₁ : ℝ}
    {h : ℝ → Euc d → Euc d → ℝ} (hmeas : Measurable fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2)
    (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsBoundedPairKernel s B (h t))
    {n : ℕ → ℕ} {u : ∀ m, Fin (n m) → Euc d → ℝ} {Cm : ∀ m, ℝ → Fin (n m) → Fin (n m) → ℝ}
    (hu : ∀ m a, IsR2Test (u m a)) (hCm : ∀ m a b, Measurable fun t => Cm m t a b)
    (hCb : ∀ m, ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ t a b, |Cm m t a b| ≤ K0) (hCs : ∀ m t a b, Cm m t a b = Cm m t b a)
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) T, IsRound2Approx s C₁ B (Whole.withDensityReal ρ) (h t)
      (fun m => r2FiniteRankKernel (Cm m t) (u m)))
    {F : ℝ → Ω' → ℝ} (hFm : Measurable fun q : ℝ × Ω' => F q.1 q.2)
    (hF2 : ∀ ζ, MemLp (fun t => F t ζ) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    {ηF : ℕ → ℝ} (hηF0 : ∀ m, 0 ≤ ηF m) (hηF : Tendsto ηF atTop (𝓝 0))
    (hFη : ∀ m, ∫⁻ ζ', ∫⁻ t in Set.Icc (0 : ℝ) T, ‖s94Flim ξ P' (Cm m) (u m) t ζ' - F t ζ'‖ₑ ^ 2 ∂volume ∂P'
      ≤ ENNReal.ofReal (ηF m))
    {k : ℕ} {aa : Fin k → Euc d → ℝ} (haa : ∀ i, IsR2Test (aa i)) :
    ∀ r : ℝ, 1 ≤ r → Tendsto (fun N => HRS.wassersteinE r
      (HRS.law (P N) fun ζ => ((fun i => r2L2Path T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ)),
        r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ),
        r2IntPath T (fun t => r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ)))
      (HRS.law P' fun ζ' => ((fun i => r2L2Path T (fun t => r2PathEval T (ξ (aa i) ζ') t)),
        r2L2Path T (fun t => F t ζ'), r2IntPath T (fun t => F t ζ'))))
      atTop (𝓝 0) := by
  intro r hr
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  have hi := s94_part_i hd hs0 hs hb hp hρ hset hT hmeas hker hu hCm hCb hCs hA hFm hF2 hηF0 hηF hFη haa
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
    obtain ⟨Mq, hMq0, hMq⟩ := s94_moment_y hd hs0 hs hb hp hρ hset hT hmeas hker haa hq
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
  have hae : ∀ N, ∀ᵐ ζ ∂(P N), MemLp (fun t => r2QuadFluct μ h (P N) (X N) t ζ) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) := fun N => s94_quad_ae_memLp_all hd hs0 hs hb hp hρ hset hT hmeas hker N
  have hY3 : ∀ N, (fun ζ => ((fun i => r2L2Path T (r2EmpFluct μ (aa i) (X N) ζ)),
        r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
        r2IntPath T (fun t => r2QuadFluct μ h (P N) (X N) t ζ))) =ᵐ[P N] Lm ∘ (g ∘ Y1 N) := by
    intro N
    filter_upwards [hae N, hyae N] with ζ hζ hy
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
  have hlawN : ∀ N, HRS.law (P N) (fun ζ => ((fun i => r2L2Path T (r2EmpFluct μ (aa i) (X N) ζ)),
        r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
        r2IntPath T (fun t => r2QuadFluct μ h (P N) (X N) t ζ))) =
      ((P N).map (g ∘ Y1 N)).map Lm := by
    intro N
    rw [HRS.law, Measure.map_congr (hY3 N), AEMeasurable.map_map_of_aemeasurable hLm.aemeasurable
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
  have hfun : (fun N => HRS.wassersteinE r
      (HRS.law (P N) fun ζ => ((fun i => r2L2Path T (r2EmpFluct μ (aa i) (X N) ζ)),
        r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
        r2IntPath T (fun t => r2QuadFluct μ h (P N) (X N) t ζ)))
      (HRS.law P' fun ζ' => ((fun i => r2L2Path T (fun t => r2PathEval T (ξ (aa i) ζ') t)),
        r2L2Path T (fun t => F t ζ'), r2IntPath T (fun t => F t ζ')))) =
      fun N => HRS.wassersteinE r (((P N).map (g ∘ Y1 N)).map Lm) ((P'.map (g ∘ Z1)).map Lm) :=
    funext fun N => by rw [hlawN N, hlawZ]
  rw [hfun]
  have hmul : Tendsto (fun N => ENNReal.ofReal ‖Lm‖ * HRS.wassersteinE r ((P N).map (g ∘ Y1 N))
      (P'.map (g ∘ Z1))) atTop (𝓝 (ENNReal.ofReal ‖Lm‖ * 0)) :=
    ENNReal.Tendsto.const_mul hW (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hmul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul (fun N => bot_le) hbound

end PartIII

end HRS.MS.R2Chaos
