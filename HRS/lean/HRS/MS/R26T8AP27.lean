import HRS.MS.R26T8AP27b

/-!
# S8.2 local Newton layer, packet T8A.P27: the pair inverse has a bounded norm and canonical rows
`Psi_R = int_0^oo tensorU U t R dt` (`pairInverseW`).  The time bound `b` of part a (P24 jets on `(0,1]`, clause 4b of the merged S8.3
on `(1,oo)`, both linear in `pairNormE M 8 R`) and `s8h2_param_set` give `C^8` and `pairNormE Psi <= C pairNormE R`
(`delta -> 0` removes the slack of the P24 jets); rows are integrable by the weighted bound and centering follows from P26 by Fubini (part b).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_pair_inverse_norm (d : ℕ) (hd : 2 ≤ d) (a beta M : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 < M) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (U : ℝ → (Euc d → ℝ) → Euc d → ℝ)
    (hU : IsWeightedSemigroup (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) M U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : Euc d → Euc d → ℝ,
      MemCMpair M 8 R → CanonicalPair (HRS.Whole.withDensityReal rho) R →
      CanonicalPair (HRS.Whole.withDensityReal rho) (pairInverseW U R) ∧
      pairNormE M 8 (pairInverseW U R) ≤ ENNReal.ofReal C*pairNormE M 8 R := by
  have hrho' : IsThermalEquilibrium d ((d : ℝ) / 2) a beta rho := hrho
  have h3 := s8f_clause3 hd ha hbeta hrho' hM hU
  have h4b := s8g_clause4b hd ha hbeta hrho' hM hU
  have hjint := s85_jb_integrable hrho'.1.1 (s84_thermal_gaussReg hd ha hbeta hrho') hM.le
  obtain ⟨C0, hC0, hjet⟩ := r26t8a_p24_jets hU h3 hM.le 8
  obtain ⟨Cj, c, hc, h4⟩ := h4b 8
  set Cj' : ℝ := max Cj 0 with hCj'
  have hCj'0 : 0 ≤ Cj' := le_max_right _ _
  set κ : ℝ := ∫ t in Set.Ioi (1 : ℝ), Real.exp (-c * t) with hκ
  have hκ0 : 0 ≤ κ := integral_nonneg fun t => (Real.exp_pos _).le
  have hCnn : 0 ≤ 3 * C0 + Cj' * κ := by positivity
  refine ⟨3 * C0 + Cj' * κ, hCnn, fun R hR hcan => ?_⟩
  have hdc : IsDoublyCentered (HRS.Whole.withDensityReal rho) R := hcan.2.2
  have hRp : S8hPair M 8 (Function.uncurry R) := s8h_pair_iff.1 hR
  have hR0 : MemCMpair M 0 R := s8h_pair_iff.2 (s8h2_pair_mono (Nat.zero_le 8) hRp)
  obtain ⟨hPtop, hν⟩ := r26t8a_p24_of_pair hRp
  set ν0 : ℝ := (pairNormE M 8 R).toReal with hν0
  have hν0n : 0 ≤ ν0 := ENNReal.toReal_nonneg
  have hPeq : pairNormE M 8 R = ENNReal.ofReal ν0 := (ENNReal.ofReal_toReal hPtop).symm
  have htime := fun δ (hδ : 0 < δ) => r26t8a_p27_time hU h3 hM.le hjet h4 hR hdc hδ
  have hreg : ∀ δ : ℝ, 0 < δ →
      ContDiff ℝ 8 (fun z => ∫ t in Set.Ioi (0 : ℝ), s8h2_S U t (Function.uncurry R) z) ∧
      ∀ k ≤ 8, ∀ z, ‖iteratedFDeriv ℝ k (fun z => ∫ t in Set.Ioi (0 : ℝ), s8h2_S U t (Function.uncurry R) z) z‖ ≤
        (3 * C0 * (ν0 + δ) + Cj' * ν0 * κ) * s8h_w M z := by
    intro δ hδ
    obtain ⟨hbi, hb0, hbint⟩ := r26t8a_p27_b_props (c1 := 3 * C0 * (ν0 + δ)) (c2 := Cj' * ν0) hc
      (by positivity) (by positivity)
    obtain ⟨h1, -, h3'⟩ := s8h2_param_set 8 (s8h_w_cont M) (fun z => (s8h_w_pos M z).le)
      (S := Set.Ioi (0 : ℝ)) measurableSet_Ioi (F := fun t => s8h2_S U t (Function.uncurry R))
      (fun t ht => (htime δ hδ t ht).1)
      (fun z => (s8h2_S_cont hd ha hbeta hrho' hU h3 hM.le hRp z).mono Set.Ioi_subset_Ici_self)
      hbi.integrableOn (fun t _ => hb0 t) (fun t ht => (htime δ hδ t ht).2)
    refine ⟨h1, fun k hk z => ?_⟩
    refine (h3' k hk z).trans (le_of_eq ?_)
    rw [hbint]
  have key : ∀ k ≤ 8, ∀ z, ‖iteratedFDeriv ℝ k (Function.uncurry (pairInverseW U R)) z‖ ≤
      ((3 * C0 + Cj' * κ) * ν0) * s8h_w M z := by
    intro k hk z
    have hw := s8h_w_pos M z
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hδ : 0 < ε / ((3 * C0 + 1) * s8h_w M z) := by positivity
    refine ((hreg _ hδ).2 k hk z).trans ?_
    have e : (3 * C0 * (ν0 + ε / ((3 * C0 + 1) * s8h_w M z)) + Cj' * ν0 * κ) * s8h_w M z =
        ((3 * C0 + Cj' * κ) * ν0) * s8h_w M z + 3 * C0 * ε / (3 * C0 + 1) := by
      field_simp
      ring
    rw [e]
    have : 3 * C0 * ε / (3 * C0 + 1) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hΨc : Continuous (Function.uncurry (pairInverseW U R)) := (hreg 1 one_pos).1.continuous
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) := s85_isProb hrho'.1.1
  set μ := HRS.Whole.withDensityReal rho with hμ
  have hb : ∀ z, ‖Function.uncurry (pairInverseW U R) z‖ ≤ ((3 * C0 + Cj' * κ) * ν0) * s8h_w M z := fun z => by
    have := key 0 (by norm_num) z
    rwa [norm_iteratedFDeriv_zero] at this
  have hjp : ∀ z : Euc d, 0 ≤ jbracket z ^ M := fun z => Real.rpow_nonneg (s83_jb_pos z).le _
  obtain ⟨hbi, hb0, -⟩ := r26t8a_p27_b_props (c1 := 3 * C0 * (ν0 + 1)) (c2 := Cj' * ν0) hc
    (by positivity) (by positivity)
  have hdel1 := htime 1 one_pos
  have hcanT := fun t (ht : 0 < t) =>
    r26t8a_tensor_canonical d hd a beta M ha hbeta hM rho hrho U hU R hR0 hcan t ht.le
  have hSc := fun z => s8h2_S_cont hd ha hbeta hrho' hU h3 hM.le hRp z
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y
    refine Integrable.mono' (hjint.const_mul (((3 * C0 + Cj' * κ) * ν0) * jbracket y ^ M))
      (hΨc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    refine (hb (x, y)).trans (le_of_eq ?_)
    simp only [s8h_w]
    ring
  · intro x
    refine Integrable.mono' (hjint.const_mul (((3 * C0 + Cj' * κ) * ν0) * jbracket x ^ M))
      (hΨc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    refine (hb (x, y)).trans (le_of_eq ?_)
    simp only [s8h_w]
    ring
  · intro y
    refine r26t8a_p27_fub (μ := μ) (fun t x => tensorU U t R x y)
      (b := r26t8a_p27_b (3 * C0 * (ν0 + 1)) (Cj' * ν0) c) (B := fun x => jbracket x ^ M * jbracket y ^ M)
      hbi.integrableOn hb0 (hjint.mul_const _) (fun x => mul_nonneg (hjp x) (hjp y))
      (fun t ht => (hdel1 t ht).1.continuous.comp (continuous_id.prodMk continuous_const))
      (fun x => (hSc (x, y)).mono Set.Ioi_subset_Ici_self)
      (fun t ht x => ?_) (fun t ht => (hcanT t ht).1.2.2.1 y)
    have := (hdel1 t ht).2 0 (by norm_num) (x, y)
    rw [norm_iteratedFDeriv_zero] at this
    exact this
  · intro x
    refine r26t8a_p27_fub (μ := μ) (fun t y => tensorU U t R x y)
      (b := r26t8a_p27_b (3 * C0 * (ν0 + 1)) (Cj' * ν0) c) (B := fun y => jbracket x ^ M * jbracket y ^ M)
      hbi.integrableOn hb0 (hjint.const_mul _) (fun y => mul_nonneg (hjp x) (hjp y))
      (fun t ht => (hdel1 t ht).1.continuous.comp (continuous_const.prodMk continuous_id))
      (fun y => (hSc (x, y)).mono Set.Ioi_subset_Ici_self)
      (fun t ht y => ?_) (fun t ht => (hcanT t ht).1.2.2.2 x)
    have := (hdel1 t ht).2 0 (by norm_num) (x, y)
    rw [norm_iteratedFDeriv_zero] at this
    exact this
  · calc pairNormE M 8 (pairInverseW U R) ≤ ENNReal.ofReal ((3 * C0 + Cj' * κ) * ν0) :=
          r26t8a_p24_norm_le (fun i hi z => key i hi z)
      _ = ENNReal.ofReal (3 * C0 + Cj' * κ) * pairNormE M 8 R := by
          rw [hPeq, ENNReal.ofReal_mul hCnn]

end HRS.MS.R26T8A
