import HRS.MS.MainRdPathAux11

/-!
# S.A.9, packet P3f: uniform tails of the transported empirical initial field

`sa9_Iq_tail`: for `t ∈ [0,T]` and `η > 0` there are `Lc` and `N₀` such that for all `N ≥ N₀`
`E ∑_{ℓ ≥ Lc} ⟨φ_ℓ, Iq_N^t⟩² ≤ η`.  Proof: assumption `(I2)` per `ℓ`, the weighted `H^{m_0}(ϖ)`-sum bound
(`sa9_varpi_sum_le`), the comparison of the tail function of the particle propagator with the limiting one
(`sa9_Gt_cmp`, through `AdjointStabilityInputRd`) and dominated convergence for the limiting tail function.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MP.RdInit
  HRS.MP.RdMart

variable {d : ℕ}

theorem sa9_hdiff_of_stab {S : WholeMainData d} {L : LimitCoeffsRd d} {Γ m₀ : ℕ} {Kst : ℝ}
    (hStab : AdjointStabilityInputRd S L (Γ + 2) (m₀ + 1) Γ Kst) {N : ℕ} (hN : 1 ≤ N)
    (hfin : coeffDiscrepancyRd S L Γ N ≠ ⊤) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (g : mhn_Hc d) :
    MemCb (m₀ + 1) (fun x => propagatorW (S.coeff N) 0 t (mhn_phi g) x - propagatorW (L.coeff S) 0 t (mhn_phi g) x) ∧
      cbNorm (m₀ + 1) (fun x => propagatorW (S.coeff N) 0 t (mhn_phi g) x -
        propagatorW (L.coeff S) 0 t (mhn_phi g) x) ≤
        (|Kst| * (coeffDiscrepancyRd S L Γ N).toReal) * HRS.Whole.sobolevNorm ((Γ + 2 : ℕ) : ℝ) (mhn_phi g) := by
  obtain ⟨-, -, hmem, hle⟩ := hStab N hN 0 t le_rfl ht.1 ht.2 (mhn_phi g) (mhn_isSobolevTest_phi _ g)
  refine ⟨hmem, ?_⟩
  set n := HRS.Whole.sobolevNorm ((Γ + 2 : ℕ) : ℝ) (mhn_phi g) with hn
  have hn0 : 0 ≤ n := Real.sqrt_nonneg _
  have hΔ0 : 0 ≤ (coeffDiscrepancyRd S L Γ N).toReal := ENNReal.toReal_nonneg
  have h1 : ENNReal.ofReal (Kst * n) ≤ ENNReal.ofReal (|Kst| * n) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) hn0)
  have hnn : 0 ≤ |Kst| * n := mul_nonneg (abs_nonneg _) hn0
  have h2 : ENNReal.ofReal (cbNorm (m₀ + 1) (fun x => propagatorW (S.coeff N) 0 t (mhn_phi g) x -
      propagatorW (L.coeff S) 0 t (mhn_phi g) x)) ≤ ENNReal.ofReal (|Kst| * n * (coeffDiscrepancyRd S L Γ N).toReal) := by
    refine hle.trans ?_
    calc ENNReal.ofReal (Kst * n) * coeffDiscrepancyRd S L Γ N
        ≤ ENNReal.ofReal (|Kst| * n) * coeffDiscrepancyRd S L Γ N := mul_le_mul' h1 le_rfl
      _ = ENNReal.ofReal (|Kst| * n) * ENNReal.ofReal (coeffDiscrepancyRd S L Γ N).toReal := by
          rw [ENNReal.ofReal_toReal hfin]
      _ = _ := (ENNReal.ofReal_mul hnn).symm
  have := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hnn hΔ0)).1 h2
  linarith

section Main

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {Γ : ℕ}

theorem sa9_Iq_tail (B : Sa9Bundle S R Γ) (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d ((Γ + 2 : ℕ) : ℝ),
      HasSum (fun n => (inner ℝ (mhn_rep ((Γ + 2 : ℕ) : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2))
    {m₀ : ℕ} {χ : Euc d → ℝ} {Cin : ℝ} {ε : ℕ → ℝ}
    (hinit : InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅))
    {Kadj Kst : ℝ} (hAdjP : AdjointDerivInput ((Γ + 2 : ℕ) : ℝ) (m₀ + 1) S.coeff S.T Kadj)
    (L : LimitCoeffsRd d) (hAdjL : AdjointInputOneD ((Γ + 2 : ℕ) : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj)
    (hStab : AdjointStabilityInputRd S L (Γ + 2) (m₀ + 1) Γ Kst)
    (hΔ : Tendsto (fun N => coeffDiscrepancyRd S L Γ N) atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {η : ℝ} (hη : 0 < η) :
    ∃ Lc N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
      ∫⁻ ζ, ∑' l, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h (l + Lc))) (B.Iq N t ζ)) ^ 2) ∂(R N).P ≤
        ENNReal.ofReal η := by
  classical
  have hχ := hinit.cutoff
  obtain ⟨Kc, hKc, hvs⟩ := sa9_varpi_sum_le hχ m₀
  set w : (Fin d → ℤ) → ℝ≥0∞ := fun z => ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) with hw
  set V0 : ℝ≥0∞ := volume (Metric.ball (0 : Euc d) 2) with hV0
  have hV0top : V0 ≠ ⊤ := measure_ball_lt_top.ne
  set Cw : ℝ≥0∞ := ∑' z, w z * (ENNReal.ofReal Kc * V0) with hCw
  have hCwtop : Cw ≠ ⊤ := by
    rw [hCw, ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top sa9_wsum_lt_top.ne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV0top)
  -- the bound for one `N` and one `Lc`
  have hA : ∀ N : ℕ, 1 ≤ N → coeffDiscrepancyRd S L Γ N ≠ ⊤ → ∀ Lc : ℕ,
      ∫⁻ ζ, ∑' l, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h (l + Lc))) (B.Iq N t ζ)) ^ 2) ∂(R N).P ≤
        ENNReal.ofReal (Cin ^ 2) * (2 * ∑' z, w z * (ENNReal.ofReal Kc *
            ∫⁻ x in Metric.ball (cellPt d z) 2, sa9_Gt h (L.coeff S) t m₀ Lc x) +
          2 * ENNReal.ofReal (sa9_Cdim d m₀ * ((|Kst| * (coeffDiscrepancyRd S L Γ N).toReal) ^ 2)) * Cw) := by
    intro N hN hfin Lc
    have hAdjN := hAdjP N hN
    set D : ℝ := |Kst| * (coeffDiscrepancyRd S L Γ N).toReal with hD
    have hdiff := sa9_hdiff_of_stab hStab hN hfin ht
    have hψ : ∀ l, ContDiff ℝ m₀ (propagatorW (S.coeff N) 0 t (mhn_phi (h (l + Lc)))) := fun l =>
      ((hAdjN 0 t le_rfl ht.1 ht.2 _ (mhn_isSobolevTest_phi _ _)).2.1).of_le (by exact_mod_cast Nat.le_succ m₀)
    -- one coordinate
    have hl : ∀ l, ∫⁻ ζ, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h (l + Lc))) (B.Iq N t ζ)) ^ 2) ∂(R N).P ≤
        ENNReal.ofReal (Cin ^ 2) * varpiNormE m₀ χ (propagatorW (S.coeff N) 0 t (mhn_phi (h (l + Lc)))) ^ 2 := by
      intro l
      set e := mhn_phi (h (l + Lc)) with he
      have hte : IsSobolevTest ((Γ + 2 : ℕ) : ℝ) e := mhn_isSobolevTest_phi _ _
      set ψ := propagatorW (S.coeff N) 0 t e with hψdef
      have hY := mri_Y0_prop hχ m₀ hAdjN ht.1 ht.2 hte
      have hAN := mri_AN_bounds S N
      have hA2 : ENNReal.ofReal (S.AN N ^ 2) ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [hAN.1, hAN.2])
      have e1 : ∫⁻ ζ, ENNReal.ofReal ((HNeg.pairing e (B.Iq N t ζ)) ^ 2) ∂(R N).P =
          ENNReal.ofReal (S.AN N ^ 2) * ∫⁻ ζ, ENNReal.ofReal ((S.κ N *
            (HRS.Whole.pair (HRS.Whole.empirical ((R N).X₀ ζ)) ψ - HRS.Whole.pair S.μ0 ψ)) ^ 2) ∂(R N).P := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr_ae ((B.hIqp N hN t ht e hte).mono fun ζ hζ => ?_)
        beta_reduce
        rw [hζ, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
      have hI2 := hinit.I2 N hN ψ hY
      rw [e1]
      calc ENNReal.ofReal (S.AN N ^ 2) * ∫⁻ ζ, ENNReal.ofReal ((S.κ N *
            (HRS.Whole.pair (HRS.Whole.empirical ((R N).X₀ ζ)) ψ - HRS.Whole.pair S.μ0 ψ)) ^ 2) ∂(R N).P
          ≤ 1 * ENNReal.ofReal (Cin ^ 2 * (varpiNormE m₀ χ ψ).toReal ^ 2) :=
            mul_le_mul' hA2 (le_trans le_self_add hI2)
        _ ≤ ENNReal.ofReal (Cin ^ 2) * varpiNormE m₀ χ ψ ^ 2 := by
            rw [one_mul, ENNReal.ofReal_mul (sq_nonneg _)]
            exact mul_le_mul' le_rfl (mri_ofReal_V_le _ _ _)
    have hmeas : ∀ l, Measurable fun ζ => ENNReal.ofReal ((HNeg.pairing (mhn_phi (h (l + Lc))) (B.Iq N t ζ)) ^ 2) :=
      fun l => ENNReal.measurable_ofReal.comp
        (((mhn_continuous_pairing (mhn_isSobolevTest_phi _ _)).measurable.comp (B.hIqm N hN t)).pow_const 2)
    obtain ⟨hvs1⟩ : Nonempty (∑' l, varpiNormE m₀ χ (propagatorW (S.coeff N) 0 t (mhn_phi (h (l + Lc)))) ^ 2 ≤
        ∑' z : Fin d → ℤ, w z * (ENNReal.ofReal Kc * ∫⁻ x in Metric.ball (cellPt d z) 2, sa9_Gt h (S.coeff N) t m₀ Lc x)) :=
      ⟨hvs _ hψ _ (sa9_Gt_meas hAdjN ht.1 ht.2 h Lc) (fun x => sa9_mriG_le h (S.coeff N) t m₀ Lc x)⟩
    have hcmp : ∀ x, sa9_Gt h (S.coeff N) t m₀ Lc x ≤ 2 * sa9_Gt h (L.coeff S) t m₀ Lc x +
        2 * ENNReal.ofReal (sa9_Cdim d m₀ * D ^ 2) := fun x =>
      sa9_Gt_cmp h hP hAdjN hAdjL ht.1 ht.2 hdiff Lc x
    have hcell : ∀ z : Fin d → ℤ, ∫⁻ x in Metric.ball (cellPt d z) 2, sa9_Gt h (S.coeff N) t m₀ Lc x ≤
        2 * (∫⁻ x in Metric.ball (cellPt d z) 2, sa9_Gt h (L.coeff S) t m₀ Lc x) +
          2 * ENNReal.ofReal (sa9_Cdim d m₀ * D ^ 2) * V0 := by
      intro z
      calc ∫⁻ x in Metric.ball (cellPt d z) 2, sa9_Gt h (S.coeff N) t m₀ Lc x
          ≤ ∫⁻ x in Metric.ball (cellPt d z) 2, (2 * sa9_Gt h (L.coeff S) t m₀ Lc x +
              2 * ENNReal.ofReal (sa9_Cdim d m₀ * D ^ 2)) := lintegral_mono hcmp
        _ = 2 * (∫⁻ x in Metric.ball (cellPt d z) 2, sa9_Gt h (L.coeff S) t m₀ Lc x) +
              2 * ENNReal.ofReal (sa9_Cdim d m₀ * D ^ 2) * V0 := by
            rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num),
              lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
              Measure.addHaar_ball_center]
    calc ∫⁻ ζ, ∑' l, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h (l + Lc))) (B.Iq N t ζ)) ^ 2) ∂(R N).P
        = ∑' l, ∫⁻ ζ, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h (l + Lc))) (B.Iq N t ζ)) ^ 2) ∂(R N).P :=
          lintegral_tsum fun l => (hmeas l).aemeasurable
      _ ≤ ∑' l, ENNReal.ofReal (Cin ^ 2) * varpiNormE m₀ χ (propagatorW (S.coeff N) 0 t (mhn_phi (h (l + Lc)))) ^ 2 :=
          ENNReal.tsum_le_tsum hl
      _ = ENNReal.ofReal (Cin ^ 2) * ∑' l, varpiNormE m₀ χ (propagatorW (S.coeff N) 0 t (mhn_phi (h (l + Lc)))) ^ 2 :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (Cin ^ 2) * ∑' z : Fin d → ℤ, w z * (ENNReal.ofReal Kc *
            (2 * (∫⁻ x in Metric.ball (cellPt d z) 2, sa9_Gt h (L.coeff S) t m₀ Lc x) +
              2 * ENNReal.ofReal (sa9_Cdim d m₀ * D ^ 2) * V0)) :=
          mul_le_mul' le_rfl (hvs1.trans (ENNReal.tsum_le_tsum fun z =>
            mul_le_mul' le_rfl (mul_le_mul' le_rfl (hcell z))))
      _ = ENNReal.ofReal (Cin ^ 2) * (2 * ∑' z, w z * (ENNReal.ofReal Kc *
            ∫⁻ x in Metric.ball (cellPt d z) 2, sa9_Gt h (L.coeff S) t m₀ Lc x) +
          2 * ENNReal.ofReal (sa9_Cdim d m₀ * D ^ 2) * Cw) := by
          congr 1
          have : ∀ z : Fin d → ℤ, w z * (ENNReal.ofReal Kc *
              (2 * (∫⁻ x in Metric.ball (cellPt d z) 2, sa9_Gt h (L.coeff S) t m₀ Lc x) +
                2 * ENNReal.ofReal (sa9_Cdim d m₀ * D ^ 2) * V0)) =
              2 * (w z * (ENNReal.ofReal Kc * ∫⁻ x in Metric.ball (cellPt d z) 2, sa9_Gt h (L.coeff S) t m₀ Lc x)) +
              2 * ENNReal.ofReal (sa9_Cdim d m₀ * D ^ 2) * (w z * (ENNReal.ofReal Kc * V0)) := fun z => by
                generalize w z = a
                generalize ENNReal.ofReal Kc = k
                generalize (∫⁻ x in Metric.ball (cellPt d z) 2, sa9_Gt h (L.coeff S) t m₀ Lc x) = I
                generalize ENNReal.ofReal (sa9_Cdim d m₀ * D ^ 2) = E
                generalize V0 = v
                ring
          rw [tsum_congr this, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  -- choice of `Lc`
  have hηpos : (0 : ℝ≥0∞) < ENNReal.ofReal (η / 2) := ENNReal.ofReal_pos.2 (by positivity)
  have hcell_t := sa9_cellsum_tendsto hAdjL h hP ht.1 ht.2 Kc
  have h1 : Tendsto (fun Lc => ENNReal.ofReal (Cin ^ 2) * (2 * ∑' z, w z * (ENNReal.ofReal Kc *
      ∫⁻ x in Metric.ball (cellPt d z) 2, sa9_Gt h (L.coeff S) t m₀ Lc x))) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul hcell_t (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)))
      (Or.inr (ENNReal.ofReal_ne_top (r := Cin ^ 2)))
    rw [mul_zero, mul_zero] at this
    exact this
  obtain ⟨Lc, hLc⟩ := (h1.eventually (gt_mem_nhds hηpos)).exists
  -- choice of `N₀`
  have hD : Tendsto (fun N => (|Kst| * (coeffDiscrepancyRd S L Γ N).toReal)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hΔ
    simpa using this.const_mul |Kst|
  have h2 : Tendsto (fun N => ENNReal.ofReal (Cin ^ 2) * (2 * ENNReal.ofReal (sa9_Cdim d m₀ *
      ((|Kst| * (coeffDiscrepancyRd S L Γ N).toReal) ^ 2)) * Cw)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun N => ENNReal.ofReal (sa9_Cdim d m₀ *
        ((|Kst| * (coeffDiscrepancyRd S L Γ N).toReal) ^ 2))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal ((hD.pow 2).const_mul (sa9_Cdim d m₀))
      simpa using this
    have := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul h3
      (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))) (Or.inr hCwtop)) (Or.inr (ENNReal.ofReal_ne_top (r := Cin ^ 2)))
    simpa using this
  have hfinev : ∀ᶠ N in atTop, coeffDiscrepancyRd S L Γ N ≠ ⊤ :=
    hΔ.eventually (ENNReal.isOpen_ne_top.mem_nhds ENNReal.zero_ne_top)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hfinev.and (h2.eventually (gt_mem_nhds hηpos)))
  refine ⟨Lc, N₀, fun N hN hN1 => ?_⟩
  obtain ⟨hfin, hsm⟩ := hN₀ N hN
  refine (hA N hN1 hfin Lc).trans ?_
  rw [mul_add]
  calc _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add hLc.le hsm.le
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end Main

end HRS.MS.MainRdPath
