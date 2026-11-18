import HRS.MS.R26T8AB08a1

/-!
# S8.2 T8A B08 (part 2): continuity in the observed time of the age-form right-hand side along a collision-free path
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

set_option maxHeartbeats 12800000 in
theorem r26t8a_b08_cont (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m M C Cf c : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d)
    (x : ℝ → EucConfig d N) (hx : Continuous x) (a0 T l h : ℝ) (hT : 0 ≤ T) (hl : 0 ≤ l) (hlh : l ≤ h) (hha : h ≤ a0)
    (hU : ∀ r ∈ Set.Icc (0 : ℝ) (a0 + T), x r ∉ eucCollisionSet d N) :
    ContinuousOn (fun t : ℝ => -r26t8a_QAge a beta m rho Psi alpha 0 (a0 + t - h) (x h) +
        r26t8a_QAge a beta m rho Psi alpha 0 (a0 + t - l) (x l) +
        ∫ r in Set.Icc l h, r26t8a_VAge a beta m rho Psi alpha 0 (a0 + t - r) (x r)) (Set.Icc 0 T) := by
  classical
  obtain ⟨-, -, hDc, -⟩ := r26t8a_normal_age_FTC d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi
    horb alpha 0 (by norm_num)
  have hQ0 := r26t8a_o06_QAge_cont d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 0
    (by norm_num)
  have hQ1 := r26t8a_o06_QAge_cont d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 1
    (by norm_num)
  have ha0 : 0 ≤ a0 := hl.trans (hlh.trans hha)
  -- the two point terms
  have hpt : ∀ s : ℝ, s ∈ Set.Icc l h → ContinuousOn (fun t : ℝ =>
      r26t8a_QAge a beta m rho Psi alpha 0 (a0 + t - s) (x s)) (Set.Icc 0 T) := by
    intro s hs
    have hpath : ContinuousOn (fun t : ℝ => (a0 + t - s, x s)) (Set.Icc 0 T) :=
      (((continuous_const.add continuous_id).sub continuous_const).prodMk continuous_const).continuousOn
    have hmaps : Set.MapsTo (fun t : ℝ => (a0 + t - s, x s)) (Set.Icc 0 T) (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) :=
      fun t ht => ⟨by simp only [Set.mem_Ici]; linarith [ht.1, hs.2], hU s ⟨hl.trans hs.1, by linarith [hs.2, ht.2, hT]⟩⟩
    exact ContinuousOn.comp (g := fun p : ℝ × EucConfig d N => r26t8a_QAge a beta m rho Psi alpha 0 p.1 p.2)
      (f := fun t : ℝ => (a0 + t - s, x s)) hQ0 hpath hmaps
  -- the integral term
  set V : ℝ × EucConfig d N → ℝ := fun q => r26t8a_VAge a beta m rho Psi alpha 0 q.1 q.2 with hV
  have hVc : ContinuousOn V (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) := by
    have e : V = fun q => r26t8a_DAge a beta m rho Psi alpha 0 q.1 q.2 - r26t8a_QAge a beta m rho Psi alpha 1 q.1 q.2 :=
      rfl
    rw [e]
    exact ContinuousOn.sub hDc hQ1
  set tc : ℝ → ℝ := fun t => max 0 (min t T) with htc
  set rc : ℝ → ℝ := fun r => max l (min r h) with hrc
  have htc_c : Continuous tc := continuous_const.max (continuous_id.min continuous_const)
  have hrc_c : Continuous rc := continuous_const.max (continuous_id.min continuous_const)
  have hrc_mem : ∀ r, rc r ∈ Set.Icc l h := fun r => ⟨le_max_left _ _, max_le hlh (min_le_right _ _)⟩
  have htc_mem : ∀ t, tc t ∈ Set.Icc (0 : ℝ) T := fun t => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  set K : ℝ × ℝ → ℝ := fun p => V (a0 + tc p.1 - rc p.2, x (rc p.2)) with hK
  have hKc : Continuous K := by
    refine hVc.comp_continuous ?_ (fun p => ?_)
    · exact ((continuous_const.add (htc_c.comp continuous_fst)).sub (hrc_c.comp continuous_snd)).prodMk
        (hx.comp (hrc_c.comp continuous_snd))
    · refine ⟨?_, hU _ ⟨hl.trans (hrc_mem p.2).1, by linarith [(hrc_mem p.2).2, (htc_mem p.1).2, hT]⟩⟩
      simp only [Set.mem_Ici]
      linarith [(hrc_mem p.2).2, (htc_mem p.1).1]
  have hint : Continuous (fun t : ℝ => ∫ r in l..h, K (t, r)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun t r => K (t, r)) hKc l h
  have hIc : ContinuousOn (fun t : ℝ => ∫ r in Set.Icc l h, r26t8a_VAge a beta m rho Psi alpha 0 (a0 + t - r) (x r))
      (Set.Icc 0 T) := by
    refine hint.continuousOn.congr (fun t ht => ?_)
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlh]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le hlh] at hr
    have h1 : tc t = t := by simp only [htc]; rw [min_eq_left ht.2, max_eq_right ht.1]
    have h2 : rc r = r := by simp only [hrc]; rw [min_eq_left hr.2, max_eq_right hr.1]
    simp only [hK, hV, h1, h2]
  exact ((hpt h ⟨hlh, le_rfl⟩).neg.add (hpt l ⟨le_rfl, hlh⟩)).add hIc

end HRS.MS.R26T8A

end
