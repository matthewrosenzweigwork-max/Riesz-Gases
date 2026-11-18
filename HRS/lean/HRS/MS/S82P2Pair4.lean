import HRS.MS.S82P2Pair3

/-!
# S8.2 (S82P2): per-site resampling bound for the pair statistic (UNCOMPILED DRAFT)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

theorem s82p2_pair_resample_i {d : ℕ} (hd : 2 ≤ d) {a beta C0 C1 M : ℝ} (hM : 0 ≤ M)
    (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (G c : ℝ) (hG : 0 < G) (hc : 0 < c) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∃ CV : ℝ, 0 ≤ CV ∧ ∀ (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ),
      WeakReferenceSetup d a beta rho q h C0 → PinComparison beta rho q h C1 →
      ∀ (A : ℝ), 0 ≤ A → ∀ (f : Euc d → ℝ) (Q : Euc d → Euc d → ℝ),
      PairCorrector a beta rho M A f Q → ∀ m : ℕ, 1 ≤ m → ∀ i : Fin (m + 1),
      ∫⁻ X, ∫⁻ y, ENNReal.ofReal ((Phase2S82.pairStatistic (N := m + 1) Q (Function.update X i y) -
          Phase2S82.pairStatistic (N := m + 1) Q X) ^ 2)
          ∂resampleLaw q h (HRS.Whole.withDensityReal rho) beta (m + 1)
            (fun i : Fin 0 => i.elim0) i X
          ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta (m + 1) (m + 1)
            (fun i : Fin 0 => i.elim0) ≤
        ENNReal.ofReal (CV * A ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2) := by
  haveI hmu : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hρ
  obtain ⟨K0, hK00, hK0⟩ := s82p2_Q_sq_row hd M hM G c hG hc rho hρ hρG
  have hMom0 : 0 ≤ HRS.MS.S82N.s82n_Mom d (4 * M) G c :=
    HRS.MS.S82N.s82n_Mom_nonneg (by omega) _ G c (by linarith) hG.le hc
  set Mom := HRS.MS.S82N.s82n_Mom d (4 * M) G c with hMomdef
  refine ⟨|C0| * (1 + 2 * |C1|) * (32 * (|C0| ^ 2 * (2 + 2 * (1 + 2 * |C1|)) + (8 * |C1| ^ 2 +
    2 * |C1| ^ 2 * (1 + 2 * (1 / (1000 * beta))))) * K0 * 2 * Mom), by positivity, ?_⟩
  intro q h hW hP A hA f Q hQ m hm i
  have hC0 := hW.positive
  have hC1 := s82p2_pinCmp_nonneg hP
  rw [abs_of_pos hC0, abs_of_nonneg hC1]
  set Cs : ℝ := C0 ^ 2 * (2 + 2 * (1 + 2 * C1)) + (8 * C1 ^ 2 +
    2 * C1 ^ 2 * (1 + 2 * (1 / (1000 * beta)))) with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  have hK1 : 0 ≤ 1 + 2 * C1 := by linarith
  set mu := HRS.Whole.withDensityReal rho with hmudef
  have hsym := hQ.symmetric
  have hKq := hK0 a beta A hA f Q hQ
  have hN : 2 ≤ m + 1 := by omega
  have hNr : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  let pins0 : Fin 0 → Euc d := fun i => i.elim0
  have hprob0 : IsProbabilityMeasure (referenceLaw q h mu beta (m + 1) (m + 1) pins0) :=
    hW.probability (m + 1) hN 0 (m + 1) (by omega) (by omega) pins0
  have hprob1 : ∀ z : Euc d, IsProbabilityMeasure (referenceLaw q h mu beta (m + 1) m
      (Fin.cons z pins0 : Fin (0 + 1) → Euc d)) := fun z =>
    hW.probability (m + 1) hN (0 + 1) m (by omega) (by omega) _
  set F : EucConfig d (m + 1) → ℝ := Phase2S82.pairStatistic (N := m + 1) Q with hF
  have hFm : Measurable F := by
    rw [hF]
    unfold Phase2S82.pairStatistic Phase2S82.pairSum
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ =>
      Finset.measurable_sum _ fun l _ => ?_)
    exact s82p2_Q_meas_pair hQ k l
  let Θ : EucConfig d (m + 1) → ℝ≥0∞ := fun X =>
    ∫⁻ y, ENNReal.ofReal ((F (Function.update X i y) - F X) ^ 2) ∂mu
  have hΘ : Measurable Θ := by
    have : Measurable (fun p : EucConfig d (m + 1) × Euc d =>
        ENNReal.ofReal ((F (Function.update p.1 i p.2) - F p.1) ^ 2)) :=
      ENNReal.measurable_ofReal.comp
        (((hFm.comp measurable_update').sub (hFm.comp measurable_fst)).pow_const 2)
    exact this.lintegral_prod_right'
  -- Step A
  have hA1 : ∫⁻ X, ∫⁻ y, ENNReal.ofReal ((F (Function.update X i y) - F X) ^ 2)
        ∂resampleLaw q h mu beta (m + 1) pins0 i X ∂referenceLaw q h mu beta (m + 1) (m + 1) pins0 ≤
      ENNReal.ofReal C0 * ∫⁻ X, Θ X ∂referenceLaw q h mu beta (m + 1) (m + 1) pins0 := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun X => ?_
    calc ∫⁻ y, ENNReal.ofReal ((F (Function.update X i y) - F X) ^ 2)
          ∂resampleLaw q h mu beta (m + 1) pins0 i X
        ≤ ∫⁻ y, ENNReal.ofReal ((F (Function.update X i y) - F X) ^ 2)
            ∂(ENNReal.ofReal C0 • mu) :=
          lintegral_mono' (s82p2_resample_le hW hbeta hN (p := 0) (n := m + 1) (by omega)
            (by omega) pins0 i X) le_rfl
      _ = ENNReal.ofReal C0 * Θ X := by rw [lintegral_smul_measure, smul_eq_mul]
  -- Step B
  have hB := s82p2_disintegration (mu := mu) hW.short.measurable hW.short.even beta (m + 1)
    (hW.hmeas (m + 1)) pins0 i hprob0 hprob1 Θ hΘ
  -- Step C
  set κ : ℝ := 32 * Cs * K0 * A ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hC : ∀ x : Euc d, ∫⁻ X', Θ (i.insertNth x X')
      ∂referenceLaw q h mu beta (m + 1) m (Fin.cons x pins0 : Fin (0 + 1) → Euc d) ≤
      ∫⁻ y, ENNReal.ofReal (κ * (jbracket x ^ (4 * M) + jbracket y ^ (4 * M))) ∂mu := by
    intro x
    have e : ∀ X' : Fin m → Euc d, Θ (i.insertNth x X') =
        ∫⁻ y, ENNReal.ofReal ((2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) *
          ∑ j, (Q y (X' j) - Q x (X' j))) ^ 2) ∂mu := by
      intro X'
      simp only [Θ, hF]
      refine lintegral_congr fun y => ?_
      rw [s82p2_update_insertNth, s82p2_pairStat_diff hsym]
    simp_rw [e]
    have hmeasf : Measurable (fun p : (Fin m → Euc d) × Euc d =>
        ENNReal.ofReal ((2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) *
          ∑ j, (Q p.2 (p.1 j) - Q x (p.1 j))) ^ 2)) := by
      refine ENNReal.measurable_ofReal.comp ((measurable_const.mul
        (Finset.measurable_sum _ fun j _ => ?_)).pow_const 2)
      exact (hQ.measurable.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp
        measurable_fst))).sub (hQ.measurable.comp (measurable_const.prodMk
          ((measurable_pi_apply j).comp measurable_fst)))
    rw [lintegral_lintegral_swap hmeasf.aemeasurable]
    refine lintegral_mono fun y => ?_
    obtain ⟨hψm, hψ2, hψ0, hψb⟩ := s82p2_psi_facts hK00 hQ hKq x y
    refine (s82p2_pair_inner_xy hd hW hbeta hP G c hG hc hρ hρG hm x (fun z => Q y z - Q x z)
      hψm hψ2 hψ0).trans ?_
    apply ENNReal.ofReal_le_ofReal
    calc 4 * Cs / ((m + 1 : ℕ) : ℝ) ^ 2 * ∫ z, (Q y z - Q x z) ^ 2 ∂mu
        ≤ 4 * Cs / ((m + 1 : ℕ) : ℝ) ^ 2 * (8 * A ^ 2 * K0 * (jbracket x ^ (4 * M) + jbracket y ^ (4 * M))) :=
          mul_le_mul_of_nonneg_left hψb (by positivity)
      _ = κ * (jbracket x ^ (4 * M) + jbracket y ^ (4 * M)) := by rw [hκ]; ring
  -- Step D
  have hdom := s82p2_marg_le_smul hP hN (p := 0) (n := m + 1) (by omega) (by omega) (by omega)
    pins0 i hprob0
  have hjb : Measurable (fun z : Euc d => jbracket z ^ (4 * M)) := by
    have : Measurable (fun x : Euc d => jbracket x) := by unfold jbracket; fun_prop
    exact this.pow_const _
  have hD : ∫⁻ X, Θ X ∂referenceLaw q h mu beta (m + 1) (m + 1) pins0 ≤
      ENNReal.ofReal (1 + 2 * C1) * ENNReal.ofReal (2 * κ * Mom) := by
    rw [hB]
    calc ∫⁻ x, ∫⁻ X', Θ (i.insertNth x X')
          ∂referenceLaw q h mu beta (m + 1) m (Fin.cons x pins0 : Fin (0 + 1) → Euc d)
          ∂((referenceLaw q h mu beta (m + 1) (m + 1) pins0).map (fun X => X i))
        ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (κ * (jbracket x ^ (4 * M) + jbracket y ^ (4 * M))) ∂mu
            ∂((referenceLaw q h mu beta (m + 1) (m + 1) pins0).map (fun X => X i)) :=
          lintegral_mono fun x => hC x
      _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (κ * (jbracket x ^ (4 * M) + jbracket y ^ (4 * M))) ∂mu
            ∂(ENNReal.ofReal (1 + 2 * C1) • mu) := lintegral_mono' hdom le_rfl
      _ = ENNReal.ofReal (1 + 2 * C1) * ∫⁻ x, ∫⁻ y, ENNReal.ofReal
            (κ * (jbracket x ^ (4 * M) + jbracket y ^ (4 * M))) ∂mu ∂mu := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ENNReal.ofReal (1 + 2 * C1) * ENNReal.ofReal (2 * κ * Mom) := by
          gcongr
          exact s82p2_double_integral hjb (fun z => s82p2_jb_rpow_nonneg _ z) hκ0 hMom0
            (s82p2_jb_moment hd (4 * M) (by linarith) G c hG hc rho hρ hρG)
  -- conclusion
  refine hA1.trans ?_
  refine (mul_le_mul_of_nonneg_left hD bot_le).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul hK1, ← ENNReal.ofReal_mul hC0.le]
  congr 1
  rw [hκ]
  field_simp

end HRS.MS.S82P2
