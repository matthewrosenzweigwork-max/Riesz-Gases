import HRS.MS.R2ChaosAux30

/-!
# HRS.MS.R2ChaosAux31 -- R3 (part 3): the time-integrated approximation estimate

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_R3`: `sup_N E ∫_0^T |B^{hm m}_N - B^h_N|² dt → 0` as `m → ∞` (dominated convergence in `t` for the pointwise-in-`t`
tail of S9.2, `s94_diff_bound_tail`; Tonelli to exchange `dt` and `dP_N`).
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

section R3d

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_R3 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {B C₁ : ℝ}
    {hm : ℕ → ℝ → Euc d → Euc d → ℝ} {h : ℝ → Euc d → Euc d → ℝ}
    (hmeas : Measurable fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2)
    (hmeasm : ∀ m, Measurable fun q : ℝ × Euc d × Euc d => hm m q.1 q.2.1 q.2.2)
    (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsBoundedPairKernel s B (h t))
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) T, IsRound2Approx s C₁ B (Whole.withDensityReal ρ) (h t) (fun m => hm m t)) :
    ∃ η : ℕ → ℝ, (∀ m, 0 ≤ η m) ∧ Tendsto η atTop (𝓝 0) ∧ ∀ m : ℕ, ∀ N : ℕ, 2 ≤ N →
      ∫⁻ ζ, ∫⁻ t in Set.Icc (0 : ℝ) T, ‖r2QuadFluct (Whole.withDensityReal ρ) (hm m) (P N) (X N) t ζ -
        r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ‖ₑ ^ 2 ∂volume ∂(P N) ≤ ENNReal.ofReal (η m) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨C, hCb, hCt⟩ := s94_diff_bound_tail hd hs0 hs hb hp hρ hset hker hA
  have hDm : ∀ m N, Measurable fun q : ℝ × Ω N => r2QuadFluct (Whole.withDensityReal ρ) (hm m) (P N) (X N) q.1 q.2 -
      r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) q.1 q.2 := fun m N =>
    (s94_quad_measurable (μ := Whole.withDensityReal ρ) (hmeasm m) (X N) (hset.measX N)).sub
      (s94_quad_measurable (μ := Whole.withDensityReal ρ) hmeas (X N) (hset.measX N))
  let e : ℕ → ℕ → ℝ → ℝ≥0∞ := fun m N t => ∫⁻ ζ, ‖r2QuadFluct (Whole.withDensityReal ρ) (hm m) (P N) (X N) t ζ -
      r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ‖ₑ ^ 2 ∂(P N)
  have he_meas : ∀ m N, Measurable (e m N) := fun m N =>
    ((hDm m N).enorm.pow_const 2).lintegral_prod_right' (ν := P N)
  let E : ℕ → ℝ → ℝ≥0∞ := fun m t => ⨆ N : {N : ℕ // 2 ≤ N}, e m N t
  have hE_meas : ∀ m, Measurable (E m) := fun m => Measurable.iSup fun N => he_meas m N
  have he_eq : ∀ m N t, e m N t = eLpNorm (fun ζ => r2QuadFluct (Whole.withDensityReal ρ) (hm m) (P N) (X N) t ζ -
      r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ) 2 (P N) ^ 2 := fun m N t =>
    s94_lintegral_sq_eq (((hDm m N).comp (measurable_prodMk_left (x := t))).aestronglyMeasurable)
  have hE_bound : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ m, E m t ≤ ENNReal.ofReal C ^ 2 := by
    intro t ht m
    refine iSup_le fun N => ?_
    rw [he_eq]
    exact pow_le_pow_left' (hCb t ht m N N.2) 2
  have hE_lim : ∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun m => E m t) atTop (𝓝 0) := by
    intro t ht
    have h1 := (ENNReal.continuous_pow 2).tendsto 0 |>.comp (hCt t ht)
    simp only [Function.comp_def, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun m => bot_le) (fun m => ?_)
    refine iSup_le fun N => ?_
    rw [he_eq]
    exact pow_le_pow_left' (le_iSup (fun N : {N : ℕ // 2 ≤ N} => eLpNorm (fun ζ =>
      r2QuadFluct (Whole.withDensityReal ρ) (hm m) (P N) (X N) t ζ -
        r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ) 2 (P N)) N) 2
  have hfin : ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal C ^ 2 ≠ ⊤ := by
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (by simp)
  have hDCT : Tendsto (fun m => ∫⁻ t in Set.Icc (0 : ℝ) T, E m t) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (Set.Icc (0 : ℝ) T))
      (F := E) (f := fun _ => 0) (fun _ => ENNReal.ofReal C ^ 2) hE_meas
      (fun m => (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun t ht => hE_bound t ht m)) hfin
      ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ hE_lim))
    simpa using this
  have hIfin : ∀ m, ∫⁻ t in Set.Icc (0 : ℝ) T, E m t ≠ ⊤ := fun m =>
    ne_top_of_le_ne_top hfin (lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2
      (ae_of_all _ fun t ht => hE_bound t ht m)))
  refine ⟨fun m => (∫⁻ t in Set.Icc (0 : ℝ) T, E m t).toReal, fun m => ENNReal.toReal_nonneg, ?_, ?_⟩
  · have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hDCT
    rw [ENNReal.toReal_zero] at this
    exact this
  · intro m N hN
    beta_reduce
    have hswap : ∫⁻ ζ, ∫⁻ t in Set.Icc (0 : ℝ) T, ‖r2QuadFluct (Whole.withDensityReal ρ) (hm m) (P N) (X N) t ζ -
        r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ‖ₑ ^ 2 ∂volume ∂(P N) =
        ∫⁻ t in Set.Icc (0 : ℝ) T, e m N t := by
      refine lintegral_lintegral_swap ?_
      exact (((hDm m N).enorm.pow_const 2).comp measurable_swap).aemeasurable
    rw [hswap, ENNReal.ofReal_toReal (hIfin m)]
    exact lintegral_mono fun t => le_iSup (fun N : {N : ℕ // 2 ≤ N} => e m N t) ⟨N, hN⟩

end R3d

end HRS.MS.R2Chaos
