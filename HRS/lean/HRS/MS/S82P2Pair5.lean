import HRS.MS.S82P2Pair4

/-!
# S8.2 (S82P2): the pair statistic is in `L²` of the weak reference law; variance bound under the
weak reference law (UNCOMPILED DRAFT)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

theorem s82p2_pair_memLp {d : ℕ} (hd : 2 ≤ d) {a beta C0 C1 M : ℝ} (hM : 0 ≤ M)
    (hbeta : 0 < beta) {rho : Euc d → ℝ} {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    (G c : ℝ) (hG : 0 < G) (hc : 0 < c) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho)
    (hW : WeakReferenceSetup d a beta rho q h C0) (hP : PinComparison beta rho q h C1)
    {A : ℝ} (hA : 0 ≤ A) {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ}
    (hQ : PairCorrector a beta rho M A f Q) {m : ℕ} (hm : 1 ≤ m) :
    MemLp (Phase2S82.pairStatistic (N := m + 1) Q) 2
      (referenceLaw q h (HRS.Whole.withDensityReal rho) beta (m + 1) (m + 1)
        (fun i : Fin 0 => i.elim0)) := by
  haveI hmu : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hρ
  obtain ⟨K0, hK00, hK0⟩ := s82p2_Q_sq_row hd M hM G c hG hc rho hρ hρG
  have hKq := hK0 a beta A hA f Q hQ
  set mu := HRS.Whole.withDensityReal rho with hmudef
  have hC1 := s82p2_pinCmp_nonneg hP
  have hN : 2 ≤ m + 1 := by omega
  let pins0 : Fin 0 → Euc d := fun i => i.elim0
  have hprob0 : IsProbabilityMeasure (referenceLaw q h mu beta (m + 1) (m + 1) pins0) :=
    hW.probability (m + 1) hN 0 (m + 1) (by omega) (by omega) pins0
  have hprob1 : ∀ z : Euc d, IsProbabilityMeasure (referenceLaw q h mu beta (m + 1) m
      (Fin.cons z pins0 : Fin (0 + 1) → Euc d)) := fun z =>
    hW.probability (m + 1) hN (0 + 1) m (by omega) (by omega) _
  set Mom := HRS.MS.S82N.s82n_Mom d (4 * M) G c with hMomdef
  have hjb : Measurable (fun z : Euc d => jbracket z ^ (4 * M)) := by
    have : Measurable (fun x : Euc d => jbracket x) := by unfold jbracket; fun_prop
    exact this.pow_const _
  -- each off-diagonal term
  have hterm : ∀ k l : Fin (m + 1), k ≠ l →
      MemLp (fun X : EucConfig d (m + 1) => Q (X k) (X l)) 2
        (referenceLaw q h mu beta (m + 1) (m + 1) pins0) := by
    intro k l hkl
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq (hkl.symm : l ≠ k)
    have hmeas : Measurable (fun X : EucConfig d (m + 1) => Q (X k) (X (k.succAbove j'))) :=
      s82p2_Q_meas_pair hQ k _
    refine (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 ⟨(hmeas.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun X => sq_nonneg _)]
    have hdis := s82p2_disintegration (mu := mu) hW.short.measurable hW.short.even beta (m + 1)
      (hW.hmeas (m + 1)) pins0 k hprob0 hprob1
      (fun X => ENNReal.ofReal ((Q (X k) (X (k.succAbove j'))) ^ 2))
      (ENNReal.measurable_ofReal.comp (hmeas.pow_const 2))
    refine lt_of_le_of_lt (le_of_eq hdis) ?_
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    have hdom0 := s82p2_marg_le_smul hP hN (p := 0) (n := m + 1) (by omega) (by omega) (by omega)
      pins0 k hprob0
    have hinner : ∀ x : Euc d, ∫⁻ X' : Fin m → Euc d, ENNReal.ofReal (Q x (X' j') ^ 2)
        ∂referenceLaw q h mu beta (m + 1) m (Fin.cons x pins0 : Fin (0 + 1) → Euc d) ≤
        ENNReal.ofReal (1 + 2 * C1) * ENNReal.ofReal (4 * A ^ 2 * K0 * jbracket x ^ (4 * M)) := by
      intro x
      have hmq : Measurable (fun z => ENNReal.ofReal (Q x z ^ 2)) :=
        ENNReal.measurable_ofReal.comp ((s82p2_Q_row_measurable hQ x).pow_const 2)
      have e1 : ∫⁻ X' : Fin m → Euc d, ENNReal.ofReal (Q x (X' j') ^ 2)
          ∂referenceLaw q h mu beta (m + 1) m (Fin.cons x pins0 : Fin (0 + 1) → Euc d) =
          ∫⁻ z, ENNReal.ofReal (Q x z ^ 2) ∂((referenceLaw q h mu beta (m + 1) m
            (Fin.cons x pins0 : Fin (0 + 1) → Euc d)).map (fun X' => X' j')) :=
        (lintegral_map hmq (measurable_pi_apply j')).symm
      rw [e1]
      calc ∫⁻ z, ENNReal.ofReal (Q x z ^ 2) ∂((referenceLaw q h mu beta (m + 1) m
              (Fin.cons x pins0 : Fin (0 + 1) → Euc d)).map (fun X' => X' j'))
          ≤ ∫⁻ z, ENNReal.ofReal (Q x z ^ 2) ∂(ENNReal.ofReal (1 + 2 * C1) • mu) :=
            lintegral_mono' (s82p2_marg_le_smul hP hN (p := 0 + 1) (n := m) (by omega) (by omega)
              (by omega) _ j' (hprob1 x)) le_rfl
        _ = ENNReal.ofReal (1 + 2 * C1) * ∫⁻ z, ENNReal.ofReal (Q x z ^ 2) ∂mu := by
            rw [lintegral_smul_measure, smul_eq_mul]
        _ ≤ _ := by gcongr; exact hKq x
    calc ∫⁻ x, ∫⁻ X' : Fin m → Euc d, ENNReal.ofReal (Q x (X' j') ^ 2)
          ∂referenceLaw q h mu beta (m + 1) m (Fin.cons x pins0 : Fin (0 + 1) → Euc d)
          ∂((referenceLaw q h mu beta (m + 1) (m + 1) pins0).map (fun X => X k))
        ≤ ∫⁻ x, ENNReal.ofReal (1 + 2 * C1) * ENNReal.ofReal (4 * A ^ 2 * K0 * jbracket x ^ (4 * M))
            ∂((referenceLaw q h mu beta (m + 1) (m + 1) pins0).map (fun X => X k)) :=
          lintegral_mono fun x => hinner x
      _ ≤ ∫⁻ x, ENNReal.ofReal (1 + 2 * C1) * ENNReal.ofReal (4 * A ^ 2 * K0 * jbracket x ^ (4 * M))
            ∂(ENNReal.ofReal (1 + 2 * C1) • mu) := lintegral_mono' hdom0 le_rfl
      _ < ⊤ := by
          rw [lintegral_smul_measure, smul_eq_mul, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          have h1 : ∫⁻ x, ENNReal.ofReal (4 * A ^ 2 * K0 * jbracket x ^ (4 * M)) ∂mu ≤
              ENNReal.ofReal (4 * A ^ 2 * K0) * ENNReal.ofReal Mom := by
            have : ∀ x : Euc d, ENNReal.ofReal (4 * A ^ 2 * K0 * jbracket x ^ (4 * M)) =
                ENNReal.ofReal (4 * A ^ 2 * K0) * ENNReal.ofReal (jbracket x ^ (4 * M)) :=
              fun x => ENNReal.ofReal_mul (by positivity)
            simp_rw [this]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            gcongr
            exact s82p2_jb_moment hd (4 * M) (by linarith) G c hG hc rho hρ hρG
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
              (lt_of_le_of_lt h1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)))
  -- sum up
  unfold Phase2S82.pairStatistic Phase2S82.pairSum
  refine MemLp.const_mul ?_ _
  refine memLp_finsetSum _ fun k _ => memLp_finsetSum _ fun l hl => ?_
  exact hterm k l (Finset.ne_of_mem_erase hl).symm

end HRS.MS.S82P2
