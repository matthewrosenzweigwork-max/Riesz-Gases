import HRS.MS.R26T8AB08a

/-!
# S8.2 T8A B08 (part b1): continuity in the observed time of the recent-block right-hand side
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

set_option maxHeartbeats 12800000 in
theorem r26t8a_b08b_cont (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m M C Cf c : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d)
    (x : ℝ → EucConfig d N) (hx : Continuous x) (a0 T : ℝ) (hT : 0 ≤ T) (ha0 : 0 ≤ a0)
    (hU : ∀ r ∈ Set.Icc (0 : ℝ) (a0 + T), x r ∉ eucCollisionSet d N) :
    ContinuousOn (fun t : ℝ => -r26t8a_QAge a beta m rho Psi alpha 0 0 (x (a0 + t)) +
        r26t8a_QAge a beta m rho Psi alpha 0 t (x a0) +
        ∫ r in Set.Icc 0 t, r26t8a_VAge a beta m rho Psi alpha 0 (t - r) (x (a0 + r))) (Set.Icc 0 T) := by
  classical
  obtain ⟨-, -, hDc, -⟩ := r26t8a_normal_age_FTC d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi
    horb alpha 0 (by norm_num)
  have hQ0 := r26t8a_o06_QAge_cont d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 0
    (by norm_num)
  have hQ1 := r26t8a_o06_QAge_cont d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 1
    (by norm_num)
  have hxU : ∀ s ∈ Set.Icc (0 : ℝ) T, x (a0 + s) ∉ eucCollisionSet d N :=
    fun s hs => hU _ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- first term
  have hp1 : ContinuousOn (fun t : ℝ => r26t8a_QAge a beta m rho Psi alpha 0 0 (x (a0 + t))) (Set.Icc 0 T) := by
    have hpath : ContinuousOn (fun t : ℝ => ((0 : ℝ), x (a0 + t))) (Set.Icc 0 T) :=
      (continuous_const.prodMk (hx.comp (continuous_const.add continuous_id))).continuousOn
    have hmaps : Set.MapsTo (fun t : ℝ => ((0 : ℝ), x (a0 + t))) (Set.Icc 0 T)
        (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) := fun t ht => ⟨Set.mem_Ici.2 le_rfl, hxU t ht⟩
    exact ContinuousOn.comp (g := fun p : ℝ × EucConfig d N => r26t8a_QAge a beta m rho Psi alpha 0 p.1 p.2)
      (f := fun t : ℝ => ((0 : ℝ), x (a0 + t))) hQ0 hpath hmaps
  have hp2 : ContinuousOn (fun t : ℝ => r26t8a_QAge a beta m rho Psi alpha 0 t (x a0)) (Set.Icc 0 T) := by
    have hpath : ContinuousOn (fun t : ℝ => (t, x a0)) (Set.Icc 0 T) :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hmaps : Set.MapsTo (fun t : ℝ => (t, x a0)) (Set.Icc 0 T) (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) :=
      fun t ht => ⟨Set.mem_Ici.2 ht.1, hU a0 ⟨ha0, by linarith [hT]⟩⟩
    exact ContinuousOn.comp (g := fun p : ℝ × EucConfig d N => r26t8a_QAge a beta m rho Psi alpha 0 p.1 p.2)
      (f := fun t : ℝ => (t, x a0)) hQ0 hpath hmaps
  -- the integral
  set V : ℝ × EucConfig d N → ℝ := fun q => r26t8a_VAge a beta m rho Psi alpha 0 q.1 q.2 with hV
  have hVc : ContinuousOn V (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) := by
    have e : V = fun q => r26t8a_DAge a beta m rho Psi alpha 0 q.1 q.2 - r26t8a_QAge a beta m rho Psi alpha 1 q.1 q.2 :=
      rfl
    rw [e]
    exact ContinuousOn.sub hDc hQ1
  set tc : ℝ → ℝ := fun t => max 0 (min t T) with htc
  have htc_c : Continuous tc := continuous_const.max (continuous_id.min continuous_const)
  have htc_mem : ∀ t, tc t ∈ Set.Icc (0 : ℝ) T := fun t => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  set rc : ℝ × ℝ → ℝ := fun p => max 0 (min p.2 (tc p.1)) with hrc
  have hrc_c : Continuous rc :=
    continuous_const.max (continuous_snd.min (htc_c.comp continuous_fst))
  have hrc_mem : ∀ p, rc p ∈ Set.Icc (0 : ℝ) (tc p.1) := fun p => ⟨le_max_left _ _, max_le (htc_mem p.1).1 (min_le_right _ _)⟩
  set K : ℝ × ℝ → ℝ := fun p => V (tc p.1 - rc p, x (a0 + rc p)) with hK
  have hKc : Continuous K := by
    refine hVc.comp_continuous ?_ (fun p => ?_)
    · exact ((htc_c.comp continuous_fst).sub hrc_c).prodMk (hx.comp (continuous_const.add hrc_c))
    · refine ⟨?_, hxU _ ⟨(hrc_mem p).1, (hrc_mem p).2.trans (htc_mem p.1).2⟩⟩
      simp only [Set.mem_Ici]
      linarith [(hrc_mem p).2]
  have hint : Continuous (fun t : ℝ => ∫ r in (0 : ℝ)..t, K (t, r)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (f := fun t r => K (t, r)) (a₀ := 0)
      (by exact hKc) continuous_id
  have hIc : ContinuousOn (fun t : ℝ => ∫ r in Set.Icc 0 t, r26t8a_VAge a beta m rho Psi alpha 0 (t - r) (x (a0 + r)))
      (Set.Icc 0 T) := by
    refine hint.continuousOn.congr (fun t ht => ?_)
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le ht.1] at hr
    have h1 : tc t = t := by simp only [htc]; rw [min_eq_left ht.2, max_eq_right ht.1]
    have h2 : rc (t, r) = r := by
      simp only [hrc, h1]; rw [min_eq_left hr.2, max_eq_right hr.1]
    simp only [hK, hV, h1, h2]
  exact (hp1.neg.add hp2).add hIc

end HRS.MS.R26T8A

end
