import HRS.MH.WpSpec2

/-!
# WpQ3: `HRS.MH.Wp.gff_remainder_bound_ae`

Mechanical copy of `HRS.GF.gff_remainder_bound` (GFFinal1.lean:59-195) with `S.EnergyMomentFinite P N X` replaced by the two a.s.
facts it was used for: `hnnA` (a.s. nonnegativity of the completed energy on `[0,T]`) and `hintA` (a.s. integrability on `[0,T]`).
The only edit in the proof is the one line `obtain ⟨hen0, henI, -, -⟩ := gf_energy_integral_moment_proof ... hE`, replaced by
`have hen0 := hnnA`, `have henI := hintA`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.WpP

open HRS HRS.GF HRS.Uniform HRS.Uniform.Kot

theorem gff_remainder_bound_ae_proof : type_of% @HRS.MH.Wp.gff_remainder_bound_ae := by
  intro d b M K
  obtain ⟨C₀min, hC⟩ := gf_remainder_pointwise_proof b M K
  refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
  obtain ⟨C, hCpos, hptw⟩ := hC C₀ hC₀
  refine ⟨C, hCpos, ?_⟩
  intro S hS hMF N hN m hmγ EV hEV Ω mΩ P _ X₀ W X hX ℱ W' hF hnnA hintA Mart hMart Z hZ hZmeas hZc hΞc
  have hT : 0 ≤ S.T := S.hT.le
  have hσ : 0 ≤ sigN S N := sigN_nonneg S N
  have hen0 := hnnA
  have henI := hintA
  set R : ℝ → Ω → NegSobolev d m := fun t ω =>
    flucProc m (sigN S N) X (S.ρ N) t ω -
      EV.VE t 0 (EV.j (flucProc (S.γ : ℝ) (sigN S N) X (S.ρ N) 0 ω)) - Z t ω with hR
  set B : ℝ → Ω → ℝ := fun t ω =>
    C * sigN S N * ∫ r in (0 : ℝ)..t, S.energyCompletion N (X (Real.toNNReal r) ω) r with hB
  have hmain : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) S.T, ‖R t ω‖ ≤ B t ω := by
    refine gf_norm_of_pairings_proof P m S.T R B ?_ ?_ ?_
    · -- continuity of `R`
      filter_upwards [hZc, hΞc] with ω hz hξ
      have h1 : ContinuousOn (fun t => flucProc m (sigN S N) X (S.ρ N) t ω) (Set.Icc 0 S.T) :=
        continuousOn_iff_continuous_restrict.2 hξ
      have h2 : ContinuousOn (fun t : ℝ => EV.VE t 0
          (EV.j (flucProc (S.γ : ℝ) (sigN S N) X (S.ρ N) 0 ω))) (Set.Icc 0 S.T) := by
        have hc := hEV.maxHyp.1.cont_E (EV.j (flucProc (S.γ : ℝ) (sigN S N) X (S.ρ N) 0 ω))
        refine hc.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ?_
        exact ⟨le_rfl, ht.1, ht.2⟩
      exact (h1.sub h2).sub hz
    · -- continuity of `B`
      filter_upwards [henI] with ω hω
      have hu : IntegrableOn (fun r => S.energyCompletion N (X (Real.toNNReal r) ω) r)
          (Set.uIcc 0 S.T) := by rwa [Set.uIcc_of_le hT]
      have := intervalIntegral.continuousOn_primitive_interval hu
      rw [Set.uIcc_of_le hT] at this
      exact this.const_smul (C * sigN S N)
    · -- the pairing bound
      intro t ht φ hφ
      obtain ⟨hφ2, hφm⟩ := gf_smooth_mem_proof hφ m
      have h1 := gf_mild_identity_proof S M hMF N hN m K hmγ EV hEV P X₀ W X hX ℱ W' hF t ht φ hφ
      have h2 := gf_pair_identification_proof S M N m K EV hEV P ℱ W' W X hF Mart hMart t ht (Z t) (hZ t ht) φ hφ
        (gf_measurable_eval_pair (hZmeas t ht) (gf_smooth_mem_proof hφ m).2)
      filter_upwards [h1, h2, hen0, henI, hX.no_collision] with ω hm1 hm2 hnn hint hnc
      have hev : NegSobolev.eval (R t ω) φ =
          sigN S N * ∫ r in (0 : ℝ)..t, flucInteraction (S.dynM M N)
            (propagator (S.dynM M N) (S.ρ N) r t φ) (X (Real.toNNReal r) ω) (S.ρ N r) := by
        simp only [hR]
        rw [gf_eval_sub_proof _ _ hφ, gf_eval_sub_proof _ _ hφ, hm1, hm2]
        ring
      rw [hev, abs_mul, abs_of_nonneg hσ]
      have hbd : |∫ r in (0 : ℝ)..t, flucInteraction (S.dynM M N)
            (propagator (S.dynM M N) (S.ρ N) r t φ) (X (Real.toNNReal r) ω) (S.ρ N r)| ≤
          C * sobolevNorm m φ * ∫ r in (0 : ℝ)..t, S.energyCompletion N (X (Real.toNNReal r) ω) r := by
        have hint' : IntervalIntegrable (fun r => S.energyCompletion N (X (Real.toNNReal r) ω) r)
            MeasureTheory.volume 0 t := by
          rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]
          exact hint.mono_set (Set.Icc_subset_Icc le_rfl ht.2)
        rw [← Real.norm_eq_abs, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.norm_integral_le_of_norm_le ht.1 ?_
          (hint'.const_mul (C * sobolevNorm m φ))
        refine Filter.Eventually.of_forall fun r hr => ?_
        have hrT : r ∈ Set.Icc (0 : ℝ) S.T := ⟨hr.1.le, hr.2.trans ht.2⟩
        have hnc' := hnc (Real.toNNReal r) (by rw [Real.coe_toNNReal _ hr.1.le]; exact hrT.2)
        rw [Real.norm_eq_abs]
        exact hptw S hS hMF N hN m hmγ r t hr.1.le hr.2 ht.2 φ hφ2 hφm
          ((hEV.adjoint r t hr.1.le hr.2 ht.2 φ hφ2 hφm).2.1)
          ((hEV.adjoint r t hr.1.le hr.2 ht.2 φ hφ2 hφm).2.2) (X (Real.toNNReal r) ω) hnc'
      calc sigN S N * |∫ r in (0 : ℝ)..t, flucInteraction (S.dynM M N)
              (propagator (S.dynM M N) (S.ρ N) r t φ) (X (Real.toNNReal r) ω) (S.ρ N r)|
          ≤ sigN S N * (C * sobolevNorm m φ *
              ∫ r in (0 : ℝ)..t, S.energyCompletion N (X (Real.toNNReal r) ω) r) :=
            mul_le_mul_of_nonneg_left hbd hσ
        _ = B t ω * sobolevNorm m φ := by simp only [hB]; ring
  filter_upwards [hmain] with ω hω t ht
  exact hω t ht

end HRS.MH.WpP
