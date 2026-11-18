import HRS.MS.R26T8AP17h
import HRS.MS.EucRegH
import HRS.MS.R2InterpAux7
import HRS.MS.WadAux37
import HRS.MS.S82P2Local

/-!
# S8.2 local Newton layer, packet T8A.P17: the canonical commutator source has the required high conormal jets
`r26t8a_source_conormal` (the Pro statement with `HRS.Whole.withDensityReal`, as the unqualified name resolves to the torus version under `open HRS`).
Proof: `r26t8a_p17_h_conormal` for the kernel itself, the shared row lemma `r26t8a_row_lemma` for the row mean `a`, and the centring identity
`HSource = (1/2) h - (1/2) a(x) - (1/2) a(y) + c0/2` (`h` symmetric). The `import R26T8AP08` of the Pro statement is replaced by the row lemma.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_p17_poly_decay {c : ℝ} (hc : 0 < c) (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → (1 + r) ^ i * Real.exp (-c * r ^ 2) ≤ C * (1 + r) ^ (-(0 + (d : ℝ) + 1)) := by
  obtain ⟨C, hC, hCb⟩ := HRS.MS.Thm.rege_poly_gauss hc (i + d + 1)
  refine ⟨C, hC.le, fun r hr => ?_⟩
  have h1 := hCb r hr
  have h2 : Real.exp (-(c / 2) * r ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg r])
  have hpos : 0 < 1 + r := by linarith
  have hq : 0 ≤ (1 + r) ^ (-(0 + (d : ℝ) + 1)) := Real.rpow_nonneg hpos.le _
  have e : (1 + r) ^ i = (1 + r) ^ (-(0 + (d : ℝ) + 1)) * (1 + r) ^ (i + d + 1) := by
    rw [← Real.rpow_natCast (1 + r) (i + d + 1), ← Real.rpow_add hpos, ← Real.rpow_natCast (1 + r) i]
    congr 1; push_cast; ring
  calc (1 + r) ^ i * Real.exp (-c * r ^ 2)
      = (1 + r) ^ (-(0 + (d : ℝ) + 1)) * ((1 + r) ^ (i + d + 1) * Real.exp (-c * r ^ 2)) := by rw [e]; ring
    _ ≤ (1 + r) ^ (-(0 + (d : ℝ) + 1)) * (C * Real.exp (-(c / 2) * r ^ 2)) := mul_le_mul_of_nonneg_left h1 hq
    _ ≤ (1 + r) ^ (-(0 + (d : ℝ) + 1)) * (C * 1) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC.le) hq
    _ = C * (1 + r) ^ (-(0 + (d : ℝ) + 1)) := by ring

set_option maxHeartbeats 6400000 in
theorem r26t8a_source_conormal (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → TestBound (testOrder d) A f →
      CanonicalPair (HRS.Whole.withDensityReal rho) (HSource (HRS.Whole.withDensityReal rho) f) ∧
      (∀ x y, HSource (HRS.Whole.withDensityReal rho) f x y = HSource (HRS.Whole.withDensityReal rho) f y x) ∧
      Conormal (2 * iterationCount d + 10) 0 0 (criticalS d) (C * A) (HSource (HRS.Whole.withDensityReal rho) f) := by
  set kk : ℕ := 2 * iterationCount d + 10 with hkk
  have hkk2 : kk + 2 ≤ testOrder d := by unfold iterationCount testOrder at *; omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hs0 : 0 < criticalS d := r26t8a_p17_s_pos hd
  have hsd : criticalS d < d := by unfold criticalS; linarith
  obtain ⟨chi, hchi⟩ := r26t8a_p06_exists_cutoff d
  -- thermal data of the unique thermal density
  obtain ⟨hρinf, -, -, hjets, -, -⟩ := HRS.MS.Thm.euc_thermal_regularity_proof (d := d) (s := criticalS d) hd hs0 hsd a beta ha hbeta
  set ρ0 : Euc d → ℝ := thermalDensity d (criticalS d) a beta with hρ0
  have hdecay : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Euc d, ‖iteratedFDeriv ℝ i ρ0 y‖ ≤ K * (1 + ‖y‖) ^ (-(0 + (d : ℝ) + 1)) := by
    intro i
    obtain ⟨C1, hC1⟩ := hjets i
    obtain ⟨C2, hC20, hC2⟩ := r26t8a_p17_poly_decay (d := d) (c := beta * a / 2) (by positivity) i
    refine ⟨|C1| * C2, by positivity, fun y => ?_⟩
    have h1 := hC1 y
    have h2 := hC2 ‖y‖ (norm_nonneg y)
    have e : -beta * a * ‖y‖ ^ 2 / 2 = -(beta * a / 2) * ‖y‖ ^ 2 := by ring
    rw [e] at h1
    calc ‖iteratedFDeriv ℝ i ρ0 y‖ ≤ C1 * (1 + ‖y‖) ^ i * Real.exp (-(beta * a / 2) * ‖y‖ ^ 2) := h1
      _ ≤ |C1| * ((1 + ‖y‖) ^ i * Real.exp (-(beta * a / 2) * ‖y‖ ^ 2)) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C1) (by positivity)) (Real.exp_pos _).le
      _ ≤ |C1| * (C2 * (1 + ‖y‖) ^ (-(0 + (d : ℝ) + 1))) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = |C1| * C2 * (1 + ‖y‖) ^ (-(0 + (d : ℝ) + 1)) := by ring
  choose Kf hKf0 hKf using hdecay
  set K : ℝ := ∑ i ∈ Finset.range (kk + 1), Kf i with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => hKf0 i
  have hKi : ∀ i ≤ kk, ∀ y : Euc d, ‖iteratedFDeriv ℝ i ρ0 y‖ ≤ K * (1 + ‖y‖) ^ (-(0 + (d : ℝ) + 1)) := by
    intro i hi y
    have h1 : Kf i ≤ K := Finset.single_le_sum (f := Kf) (fun i _ => hKf0 i) (Finset.mem_range.2 (by omega))
    exact (hKf i y).trans (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (by positivity) _))
  obtain ⟨Crow, hCrow0, hCrow⟩ := r26t8a_row_lemma hd kk 0 0 (criticalS d) le_rfl hsd K hK0
  obtain ⟨Ch, hCh0, hCh⟩ := r26t8a_p17_h_conormal hd kk
  refine ⟨Ch * (1 / 2) + 3 / 2 * (Crow * Ch), by positivity, fun rho hrho f A hA hf => ?_⟩
  have hρeq := critical_thermal_eq d hd a beta ha hbeta hrho
  subst hρeq
  have hprob : HRS.Whole.IsProbDensity (thermalDensity d (criticalS d) a beta) := hrho.1.1
  haveI hpm : IsProbabilityMeasure (HRS.Whole.withDensityReal (thermalDensity d (criticalS d) a beta)) :=
    HRS.MS.Wad.s85_isProb hprob
  set μ := HRS.Whole.withDensityReal ρ0 with hμ
  have hρc : ContDiff ℝ (kk : WithTop ℕ∞) ρ0 := contDiff_infty.1 hρinf kk
  have hf' : TestBound (kk + 2) A f := ⟨hf.1, fun j hj hjk x => hf.2 j hj (hjk.trans hkk2) x⟩
  have hfC : ContDiff ℝ ∞ f := hf.1
  -- conormal of the kernel and of its half
  have hCh1 := hCh A hA f hf'
  have hhalf : TestBound (kk + 2) (|(1 / 2 : ℝ)| * A) (fun x => (1 / 2 : ℝ) * f x) := r26t8a_p17_testBound_smul hf' _
  have hCh2 := hCh (|(1 / 2 : ℝ)| * A) (by positivity) _ hhalf
  rw [r26t8a_p17_hSource_smul hfC] at hCh2
  -- the row mean
  set h := hSource f with hh
  have hsymm : ∀ x y, h x y = h y x := fun x y => HRS.MS.R2Interp.s102_commutatorKernel_symm _ _ x y
  have hrowC := hCrow ρ0 hρc hKi h (Ch * A) (by positivity) hCh1
  set aa : Euc d → ℝ := fun x => ∫ y', h x y' ∂μ with haa
  have haeq : aa = fun x => ∫ y, ρ0 y * h x y := by
    funext x; exact r26t8a_p17_integral_wd hprob (h x)
  have haC : ContDiff ℝ (kk : WithTop ℕ∞) aa := by rw [haeq]; exact hrowC.1
  have hajets : ∀ i ≤ kk, ∀ x, ‖iteratedFDeriv ℝ i aa x‖ ≤ Crow * (Ch * A) := by
    intro i hi x
    have := hrowC.2 i hi x
    rw [haeq]
    simpa [Real.rpow_zero] using this
  set Ba : ℝ := Crow * (Ch * A) with hBa
  have hBa0 : 0 ≤ Ba := by rw [hBa]; positivity
  -- integrability facts
  have hrowI : ∀ x, Integrable (h x) μ := fun x =>
    r26t8a_p17_integrable_wd hprob (r26t8a_row_integrable hd kk 0 (M := 0) le_rfl (criticalS d) hsd K hK0 hρc hKi (A := Ch * A) (by positivity) hCh1 x)
  have haI : Integrable aa μ := by
    refine Integrable.mono' (integrable_const Ba) (haC.continuous.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    have := hajets 0 (Nat.zero_le _) x
    simpa using this
  have hc0 : |∫ x, aa x ∂μ| ≤ Ba := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := aa) (C := Ba) (Eventually.of_forall fun x => by simpa using hajets 0 (Nat.zero_le _) x)
    simpa using this
  -- the centred source as a sum
  have hform : ∀ x y, HSource μ f x y = (1 / 2 : ℝ) * h x y + (-(1 / 2 : ℝ) * aa x) + (-(1 / 2 : ℝ) * aa y) +
      (1 / 2 : ℝ) * ∫ x', aa x' ∂μ := by
    intro x y
    unfold HSource
    rw [r26t8a_p17_center_form μ h hsymm]
    simp only [haa]
    ring
  refine ⟨?_, ?_, ?_⟩
  · have := r26t8a_p17_canonical μ h hsymm hrowI haI
    exact this
  · intro x y
    rw [hform, hform, hsymm x y]; ring
  · -- conormality
    have hg2 : ContDiff ℝ (kk : WithTop ℕ∞) (fun x => -(1 / 2 : ℝ) * aa x) := contDiff_const.mul haC
    have hg2j : ∀ i ≤ kk, ∀ x, ‖iteratedFDeriv ℝ i (fun x => -(1 / 2 : ℝ) * aa x) x‖ ≤ 1 / 2 * Ba := by
      intro i hi x
      rw [r26t8a_p17_jets_const_mul haC _ hi, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (hajets i hi x) (by norm_num)
    obtain ⟨cx, cy⟩ := r26t8a_p17_conormal_fx kk 0 (criticalS d) (1 / 2 * Ba) hg2 hg2j
    have hg4 : ContDiff ℝ (kk : WithTop ℕ∞) (fun _ : Euc d => (1 / 2 : ℝ) * ∫ x', aa x' ∂μ) := contDiff_const
    have hg4j : ∀ i ≤ kk, ∀ x : Euc d, ‖iteratedFDeriv ℝ i (fun _ : Euc d => (1 / 2 : ℝ) * ∫ x', aa x' ∂μ) x‖ ≤ 1 / 2 * Ba := by
      intro i hi x
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact mul_le_mul_of_nonneg_left hc0 (by norm_num)
      · rw [iteratedFDeriv_const_of_ne (by omega : i ≠ 0)]; simp; positivity
    obtain ⟨c4, -⟩ := r26t8a_p17_conormal_fx kk 0 (criticalS d) (1 / 2 * Ba) hg4 hg4j
    have hsum := r26t8a_N0_conormal_add hchi (r26t8a_N0_conormal_add hchi (r26t8a_N0_conormal_add hchi hCh2 cx) cy) c4
    have hAeq : Ch * (|(1 / 2 : ℝ)| * A) + 1 / 2 * Ba + 1 / 2 * Ba + 1 / 2 * Ba =
        (Ch * (1 / 2) + 3 / 2 * (Crow * Ch)) * A := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hBa]; ring
    rw [hAeq] at hsum
    refine r26t8a_N0_conormal_congr (fun x y _ => ?_) hsum
    rw [hform]

end HRS.MS.R26T8A
