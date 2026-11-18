import HRS.MS.MainRdPathAux15

/-!
# S.A.9, packet P3j: the bound for the tails of the stochastic convolution (one `N`, all parameters)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MP.RdInit
  HRS.MP.RdMart HRS.MP.RdRem HRS.MP.RdProp HRS.MS.MainRdField

variable {d : ℕ}

theorem sa9_hdiff_of_stab_r {S : WholeMainData d} {L : LimitCoeffsRd d} {Γ m₀ : ℕ} {Kst : ℝ}
    (hStab : AdjointStabilityInputRd S L (Γ + 2) (m₀ + 1) Γ Kst) {N : ℕ} (hN : 1 ≤ N)
    (hfin : coeffDiscrepancyRd S L Γ N ≠ ⊤) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t ≤ S.T)
    (g : mhn_Hc d) :
    MemCb (m₀ + 1) (fun x => propagatorW (S.coeff N) r t (mhn_phi g) x - propagatorW (L.coeff S) r t (mhn_phi g) x) ∧
      cbNorm (m₀ + 1) (fun x => propagatorW (S.coeff N) r t (mhn_phi g) x -
        propagatorW (L.coeff S) r t (mhn_phi g) x) ≤
        (|Kst| * (coeffDiscrepancyRd S L Γ N).toReal) * HRS.Whole.sobolevNorm ((Γ + 2 : ℕ) : ℝ) (mhn_phi g) := by
  obtain ⟨-, -, hmem, hle⟩ := hStab N hN r t hr hrt htT (mhn_phi g) (mhn_isSobolevTest_phi _ g)
  refine ⟨hmem, ?_⟩
  set n := HRS.Whole.sobolevNorm ((Γ + 2 : ℕ) : ℝ) (mhn_phi g) with hn
  have hn0 : 0 ≤ n := Real.sqrt_nonneg _
  have hΔ0 : 0 ≤ (coeffDiscrepancyRd S L Γ N).toReal := ENNReal.toReal_nonneg
  have h1 : ENNReal.ofReal (Kst * n) ≤ ENNReal.ofReal (|Kst| * n) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) hn0)
  have hnn : 0 ≤ |Kst| * n := mul_nonneg (abs_nonneg _) hn0
  have h2 : ENNReal.ofReal (cbNorm (m₀ + 1) (fun x => propagatorW (S.coeff N) r t (mhn_phi g) x -
      propagatorW (L.coeff S) r t (mhn_phi g) x)) ≤ ENNReal.ofReal (|Kst| * n * (coeffDiscrepancyRd S L Γ N).toReal) := by
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

theorem sa9_Mq_tail_bound (B : Sa9Bundle S R Γ) (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d ((Γ + 2 : ℕ) : ℝ),
      HasSum (fun n => (inner ℝ (mhn_rep ((Γ + 2 : ℕ) : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2))
    {m₀ : ℕ} (hm₀ : 1 ≤ m₀) {Kadj Kst : ℝ}
    (hAdjP : AdjointDerivInput ((Γ + 2 : ℕ) : ℝ) (m₀ + 1) S.coeff S.T Kadj)
    (L : LimitCoeffsRd d) (hAdjL : AdjointInputOneD ((Γ + 2 : ℕ) : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj)
    (hStab : AdjointStabilityInputRd S L (Γ + 2) (m₀ + 1) Γ Kst) {m₂ : ℝ}
    (hm₂ : PropagatedSecondMoment S R m₂) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T)
    {N : ℕ} (hN : 1 ≤ N) (hfin : coeffDiscrepancyRd S L Γ N ≠ ⊤) (Lc : ℕ)
    {Rr δ : ℝ} (hRr : 0 < Rr) (net : Finset (Euc d))
    (hnet : ∀ x : Euc d, ‖x‖ ≤ Rr → ∃ y ∈ net, ‖x - y‖ < δ) :
    ∫⁻ ζ, ∑' l, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h (l + Lc))) (B.Mq N t ζ)) ^ 2) ∂(R N).P ≤
      2 * (4 * ∑ j : Fin d, ∑ y ∈ net, (∫⁻ r in Set.Icc (0 : ℝ) t, sa9_Tm h (L.coeff S) t j Lc (r, y)) +
        ENNReal.ofReal t * ∑ _j : Fin d, (4 * ENNReal.ofReal (((d : ℝ) * d * |Kadj| * δ) ^ 2) +
          2 * ENNReal.ofReal ((|Kst| * (coeffDiscrepancyRd S L Γ N).toReal) ^ 2))) +
      2 * d * ENNReal.ofReal (Kadj ^ 2) * ENNReal.ofReal (2 / Rr ^ 2) * (ENNReal.ofReal t * ENNReal.ofReal m₂) := by
  classical
  have hN0 : 0 < N := hN
  have hT : 0 ≤ S.T := S.hT.le
  have hAdjN := hAdjP N hN
  set cN : ℝ := S.sigma N * Real.sqrt (2 * S.invβ N) / N with hcN
  have hcN2 : cN ^ 2 * N ≤ 2 := mrm_cN_sq S hN0
  set D : ℝ := |Kst| * (coeffDiscrepancyRd S L Γ N).toReal with hD
  set Eδ : ℝ≥0∞ := ENNReal.ofReal (((d : ℝ) * d * |Kadj| * δ) ^ 2) with hEδ
  set ED : ℝ≥0∞ := ENNReal.ofReal (D ^ 2) with hED
  set K2 : ℝ≥0∞ := ENNReal.ofReal (Kadj ^ 2) with hK2
  have hF := B.hfilt N hN
  have hXm := mrr_prog_meas (B.ℱ N) (R N).X hF.progressive hT
  rw [sa9_Mq_tail_eq B h hN hAdjN ht Lc]
  set a : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (cN ^ 2 * N) * ∑ j : Fin d,
    (4 * ∑ y ∈ net, sa9_Tm h (L.coeff S) t j Lc (r, y) + 4 * Eδ + 2 * ED) with ha
  set C0 : ℝ≥0∞ := 2 * d * K2 * ENNReal.ofReal (cN ^ 2 / Rr ^ 2) with hC0
  set b : ℝ → (R N).Ω → ℝ≥0∞ := fun r ζ => C0 * ∑ i : Fin N,
    ENNReal.ofReal (‖(R N).X (Real.toNNReal (mrrClamp S.T r)) ζ i‖ ^ 2) with hb
  have hpt : ∀ ζ, ∀ r ∈ Set.Icc (0 : ℝ) t, ∑ ia : Fin N × Fin d, ENNReal.ofReal (cN ^ 2) *
      sa9_Tm h (S.coeff N) t ia.2 Lc (r, (R N).X (Real.toNNReal (mrrClamp S.T r)) ζ ia.1) ≤ a r + b r ζ := by
    intro ζ r hr
    have := sa9_pt_bound hm₀ h hP hAdjN hAdjL ht.2 hr
      (hdiff := sa9_hdiff_of_stab_r hStab hN hfin hr.1 hr.2 ht.2) Lc hRr net hnet cN
      ((R N).X (Real.toNNReal (mrrClamp S.T r)) ζ)
    exact this
  have hTm_meas : ∀ j y, Measurable fun r : ℝ => sa9_Tm h (L.coeff S) t j Lc (r, y) := fun j y =>
    (sa9_Tm_meas h (L.coeff S) t j Lc).comp (measurable_id.prodMk measurable_const)
  have hamea : Measurable a := by
    refine Measurable.const_mul (Finset.measurable_sum _ fun j _ => ?_) _
    exact (((Finset.measurable_sum _ fun y _ => hTm_meas j y).const_mul 4).add_const _).add_const _
  -- the integral of `a`
  have hint : ∀ j : Fin d, ∫⁻ r in Set.Icc (0 : ℝ) t, (4 * ∑ y ∈ net, sa9_Tm h (L.coeff S) t j Lc (r, y) +
      4 * Eδ + 2 * ED) = 4 * ∑ y ∈ net, (∫⁻ r in Set.Icc (0 : ℝ) t, sa9_Tm h (L.coeff S) t j Lc (r, y)) +
        (4 * Eδ + 2 * ED) * ENNReal.ofReal t := by
    intro j
    have e : (fun r : ℝ => 4 * ∑ y ∈ net, sa9_Tm h (L.coeff S) t j Lc (r, y) + 4 * Eδ + 2 * ED) =
        fun r => 4 * ∑ y ∈ net, sa9_Tm h (L.coeff S) t j Lc (r, y) + (4 * Eδ + 2 * ED) := by
      funext r; ring
    rw [e, lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by simp),
      lintegral_finset_sum _ fun y _ => hTm_meas j y, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, Real.volume_Icc, sub_zero]
  have hfirst : ∫⁻ r in Set.Icc (0 : ℝ) t, a r ≤ 2 * (4 * ∑ j : Fin d, ∑ y ∈ net,
      (∫⁻ r in Set.Icc (0 : ℝ) t, sa9_Tm h (L.coeff S) t j Lc (r, y)) +
        ENNReal.ofReal t * ∑ _j : Fin d, (4 * Eδ + 2 * ED)) := by
    have h2 : ENNReal.ofReal (cN ^ 2 * N) ≤ 2 := by
      calc ENNReal.ofReal (cN ^ 2 * N) ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hcN2
        _ = 2 := by simp
    calc ∫⁻ r in Set.Icc (0 : ℝ) t, a r
        ≤ ∫⁻ r in Set.Icc (0 : ℝ) t, 2 * ∑ j : Fin d,
          (4 * ∑ y ∈ net, sa9_Tm h (L.coeff S) t j Lc (r, y) + 4 * Eδ + 2 * ED) :=
          lintegral_mono fun r => mul_le_mul' h2 le_rfl
      _ = 2 * ∑ j : Fin d, ∫⁻ r in Set.Icc (0 : ℝ) t, (4 * ∑ y ∈ net, sa9_Tm h (L.coeff S) t j Lc (r, y) +
          4 * Eδ + 2 * ED) := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_finset_sum]
          intro j _
          exact (((Finset.measurable_sum _ fun y _ => hTm_meas j y).const_mul 4).add_const _).add_const _
      _ = _ := by
          simp only [hint]
          congr 1
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
          ring
  -- the second moment part
  set K3 : ℝ≥0∞ := 2 * d * K2 * ENNReal.ofReal (2 / Rr ^ 2) with hK3
  have hK3top : K3 ≠ ⊤ := by
    simp only [hK3, hK2]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (by simp)) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  set G : ℝ → (R N).Ω → ℝ := fun r ζ =>
    secondMomentOf (HRS.Whole.empirical ((R N).X (Real.toNNReal (mrrClamp S.T r)) ζ)) with hG
  have hGm : Measurable fun p : ℝ × (R N).Ω => G p.1 p.2 := (mrm_measurable_secondMoment hN0).comp hXm
  have hbG : ∀ r ζ, b r ζ ≤ K3 * ENNReal.ofReal (G r ζ) := by
    intro r ζ
    set x := (R N).X (Real.toNNReal (mrrClamp S.T r)) ζ with hx
    have hsm := mrm_secondMoment_empirical hN0 x
    have hG0 : 0 ≤ G r ζ := mrm_secondMoment_nonneg x
    have hsum' : ∑ i, ‖x i‖ ^ 2 = N * G r ζ := by
      have : G r ζ = (N : ℝ)⁻¹ * ∑ i, ‖x i‖ ^ 2 := hsm
      rw [this]
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
      field_simp
    have hNG : 0 ≤ (N : ℝ) * G r ζ := by positivity
    calc b r ζ = 2 * d * K2 * (ENNReal.ofReal (cN ^ 2 / Rr ^ 2) * ENNReal.ofReal (N * G r ζ)) := by
          simp only [hb, hC0]
          rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _, hsum']
          ring
      _ = 2 * d * K2 * ENNReal.ofReal (cN ^ 2 * N / Rr ^ 2 * G r ζ) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 2; ring
      _ ≤ 2 * d * K2 * ENNReal.ofReal (2 / Rr ^ 2 * G r ζ) := by
          refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hG0))
          exact div_le_div_of_nonneg_right hcN2 (by positivity)
      _ = K3 * ENNReal.ofReal (G r ζ) := by
          rw [ENNReal.ofReal_mul (by positivity)]
          simp only [hK3]; ring
  have hmom : ∀ r ∈ Set.Icc (0 : ℝ) t, ∫⁻ ζ, ENNReal.ofReal (G r ζ) ∂(R N).P ≤ ENNReal.ofReal m₂ := by
    intro r hr
    have hrT : r ∈ Set.Icc (0 : ℝ) S.T := ⟨hr.1, hr.2.trans ht.2⟩
    refine le_trans (lintegral_mono fun ζ => ENNReal.ofReal_le_ofReal ?_) (hm₂ N hN r hrT)
    simp only [hG, mrrClamp_of_mem hrT]
    have := HRS.Whole.Q09A.secondMomentOf_nonneg (d := d) (HRS.Whole.withDensityReal (S.ρ N r))
    linarith
  have hsecond : ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) t, b r ζ) ∂(R N).P ≤ K3 * (ENNReal.ofReal t * ENNReal.ofReal m₂) := by
    calc ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) t, b r ζ) ∂(R N).P
        ≤ ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) t, K3 * ENNReal.ofReal (G r ζ)) ∂(R N).P :=
          lintegral_mono fun ζ => lintegral_mono fun r => hbG r ζ
      _ = K3 * ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal (G r ζ)) ∂(R N).P := by
          simp_rw [lintegral_const_mul' _ _ hK3top]
      _ ≤ K3 * (ENNReal.ofReal t * ENNReal.ofReal m₂) :=
          mul_le_mul' le_rfl (mrr_time_moment (R N).P G hGm (ENNReal.ofReal m₂) hmom)
  calc ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) t, ∑ ia : Fin N × Fin d, ENNReal.ofReal (cN ^ 2) *
        sa9_Tm h (S.coeff N) t ia.2 Lc (r, (R N).X (Real.toNNReal (mrrClamp S.T r)) ζ ia.1)) ∂(R N).P
      ≤ ∫⁻ ζ, ((∫⁻ r in Set.Icc (0 : ℝ) t, a r) + ∫⁻ r in Set.Icc (0 : ℝ) t, b r ζ) ∂(R N).P :=
        lintegral_mono fun ζ => ((setLIntegral_mono' measurableSet_Icc (hpt ζ)).trans
          (lintegral_add_left hamea _).le)
    _ = (∫⁻ r in Set.Icc (0 : ℝ) t, a r) + ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) t, b r ζ) ∂(R N).P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ _ := add_le_add hfirst hsecond

end Main

end HRS.MS.MainRdPath
