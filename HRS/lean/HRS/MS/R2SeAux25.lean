import HRS.MS.R2SeAux24

/-!
# S9.9 `r2_static_edgeworth`, packet 25: the expansion of `E[Y_u Y_v ψ(W_N)]`

Worker S99, namespace `S99`.  `s99_Mab`: for `u, v ∈ C_b^{J1}` and `ψ ∈ Bd 4`,
`E[Y_u Y_v ψ(W)] - E[Y_u Y_v] E[ψ(W)] = ∑_{l,q} κ_{u,l} κ_{v,q} E[∂_q∂_lψ(G)] + O(1/√N)`.
It combines `s99_E1b` (for `ψ` and for the constant `1`), the remainder bound `s99_Bq_bound`, the LLN `s99_T_L1`
and the per-`l` estimate `s99_Mab_l`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section Mab

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

set_option maxHeartbeats 2000000 in
theorem s99_Mab {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j => susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) γ (φ i) (φ j))) {u v : Euc d → ℝ} (hu : MemCb (J1 d) u)
    (hv : MemCb (J1 d) v) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ {ψ : SeqL2 → ℝ}, Bd 4 ψ →
      |(∫ X, s45_Yi N u (pair (S46.s46_nu d s a β γ N) u) X *
          (s45_Yi N v (pair (S46.s46_nu d s a β γ N) v) X *
            ψ (featureVec φ (S46.s46_nu d s a β γ N) X)) ∂(S46.s46_P d s a β γ N)) -
        (∫ X, s45_Yi N u (pair (S46.s46_nu d s a β γ N) u) X *
          s45_Yi N v (pair (S46.s46_nu d s a β γ N) v) X ∂(S46.s46_P d s a β γ N)) *
          (∫ X, ψ (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N)) -
        ∑' l, ∑' q, kap d s a β γ u φ l * kap d s a β γ v φ q * ∫ z, pd (pd ψ l) q z ∂G| ≤
        K / Real.sqrt N := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨K₂, hK₂, h2⟩ := s99_chi1 hd hs0 hsd ha hβ hγ hT
  obtain ⟨KB, hKB0, hKB⟩ := s99_Bq_bound hd hs0 hs ha hβ hγ hT hS
  obtain ⟨KT, hKT0, hTL2⟩ := s99_T_L2 hd hs0 hs ha hβ hγ hT hS
  obtain ⟨KY, hKY0, hY2⟩ := s99_Y_L2 hd hs0 hs ha hβ hγ hT hS
  obtain ⟨KM, hKM0, hMl⟩ := s99_Mab_l hd hs0 hs ha hβ hγ hT hS hφ F hG
  have hk0 : 1 ≤ k0 d := k0_ge_one d
  have hJ1 : 1 ≤ J1 d := by unfold J1; omega
  have hu0 : MemCb (k0 d) u := (HRS.MS.Tc5.tc5_cb_mono (J1_ge_k0 d |>.trans' (by omega)) hu).1
  obtain ⟨χ, hχ2, hwf, hgen⟩ := h2 u hu0
  set Bu : ℝ := K₂ * cbNorm (k0 d) u with hBudef
  have hBu0 : 0 ≤ Bu := by have := HRS.MS.Tc5.tc5_cb_nonneg (d := d) (k0 d) u; positivity
  set b : ℕ → ℝ := fun j => cbNorm (J1 d) (φ j) with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  set Sb : ℝ := ∑' m, b m with hSb
  have hSb0 : 0 ≤ Sb := tsum_nonneg hb0
  set cv := cbNorm (J1 d) v with hcvdef
  have hcv0 : 0 ≤ cv := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hvbd : ∀ x, |v x| ≤ cv := fun x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le hv x
    rwa [Real.norm_eq_abs] at this
  have hvc1 : ContDiff ℝ 1 v := hv.1.of_le (by exact_mod_cast hJ1)
  have hvm : Measurable v := hvc1.continuous.measurable
  have hDv : ∀ x, ‖fderiv ℝ v x‖ ≤ cv := fun x => s45_cb_deriv_le hJ1 hv x
  set cu := cbNorm (J1 d) u with hcudef
  have hcu0 : 0 ≤ cu := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hubd : ∀ x, |u x| ≤ cu := fun x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le hu x
    rwa [Real.norm_eq_abs] at this
  have huc1 : ContDiff ℝ 1 u := hu.1.of_le (by exact_mod_cast hJ1)
  have hum : Measurable u := huc1.continuous.measurable
  have hv1 : ContDiff ℝ 1 (gradient χ) := s45_contDiff_gradient hwf.smooth
  -- the mixed observable `w_{uv}`
  set wuv : Euc d → ℝ := fun x => γ⁻¹ * ⟪gradient χ x, gradient v x⟫ with hwuv
  set Cuv : ℝ := γ⁻¹ * Bu * cv with hCuv
  have hCuv0 : 0 ≤ Cuv := by positivity
  have hwuvbd : ∀ x, |wuv x| ≤ Cuv := by
    intro x
    simp only [hwuv, hCuv]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
    exact (mul_le_mul_of_nonneg_left (s99_inner_grad_le hwf.B1 hDv x) (inv_nonneg.2 hγ.le)).trans_eq
      (by ring)
  have hwuvc : Continuous wuv :=
    continuous_const.mul (hv1.continuous.inner (s45_gradient_continuous hvc1))
  have hwuvm : Measurable wuv := hwuvc.measurable
  obtain ⟨KT1, hKT1, hT1⟩ : ∃ KT1 : ℝ, 0 ≤ KT1 ∧ ∀ N : ℕ, 2 ≤ N → ∀ {B : ℝ}, 0 ≤ B → ∀ {w : Euc d → ℝ},
      Measurable w → (∀ x, |w x| ≤ B) →
      ∫ X, |pair (empirical X) w - pair (thermalMeasure d s a β) w| ∂(S46.s46_P d s a β γ N) ≤
        KT1 * B / Real.sqrt N :=
    ⟨KT, hKT0, fun N hN B hB w hw hwb => s99_T_L1 hT hS hKT0 hTL2 hN hB hw hwb⟩
  set K : ℝ := 2 * KB * Bu * KY * cv + KM * Bu * cv * Sb + 2 * KT1 * Cuv with hKdef
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, hK0, fun N hN ψ hψ => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
  haveI hν : IsProbabilityMeasure (S46.s46_nu d s a β γ N) := s99_nu_prob hN1
  set P := S46.s46_P d s a β γ N with hPdef
  set ν := S46.s46_nu d s a β γ N with hνdef
  set Yu : EucConfig d N → ℝ := fun X => s45_Yi N u (pair ν u) X with hYudef
  set Yv : EucConfig d N → ℝ := fun X => s45_Yi N v (pair ν v) X with hYvdef
  have hYvm : Measurable Yv :=
    measurable_const.mul ((s45_measurable_pair_empirical hN1 hvm).sub measurable_const)
  have hYvb : ∀ X, |Yv X| ≤ 2 * Real.sqrt N * cv := fun X => s99_Yi_bd hN1 hvbd X
  have hWc : Continuous (fun X : EucConfig d N => featureVec φ ν X) :=
    (s99_W_contDiff hN1 hJ1 hφ).continuous
  have hψ1 : Bd 1 ψ := hψ.of_le (by norm_num)
  have hψW_m : Measurable fun X : EucConfig d N => ψ (featureVec φ ν X) :=
    (hψ.1.continuous.comp hWc).measurable
  have hψW_b : ∀ X : EucConfig d N, |ψ (featureVec φ ν X)| ≤ 1 := fun X => hψ.abs_le _
  set Eψ : ℝ := ∫ X, ψ (featureVec φ ν X) ∂P with hEψ
  have hEψb : |Eψ| ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := fun X : EucConfig d N => ψ (featureVec φ ν X))
      (C := 1) (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hψW_b X)
    simpa [Real.norm_eq_abs] using this
  -- the two exact identities
  have hE1 := s99_E1b hd hs0 hsd ha hβ hγ hT hN (hS N hN) hJ1 hφ hv hu hwf hψ1
  have hE0 := s99_E1b hd hs0 hsd ha hβ hγ hT hN (hS N hN) hJ1 hφ hv hu hwf (s99_Bd_const 1)
  simp only [mul_one, s99_pd_const, mul_zero, integral_zero, tsum_zero, add_zero] at hE0
  -- the remainder `r`
  set r : EucConfig d N → ℝ := fun X => Real.sqrt N * s45_Rp (thermalMeasure d s a β) ν P
      (commutatorKernel d s (gradient χ)) X with hrdef
  have hsqrt : ∀ X : EucConfig d N, r X = -(Bq d s a β γ N χ X) / Real.sqrt N := fun X =>
    s99_sqrt_Rp hd hs0 hsd hT hN (hS N hN) hwf.smooth hwf.B2 X
  obtain ⟨hBi2, hB2, hBi, hB1⟩ := hKB N hN hwf.smooth hwf.B2
  have hBm : Measurable fun X : EucConfig d N => Bq d s a β γ N χ X := by
    unfold Bq
    exact measurable_const.mul ((HRS.MS.Wr.wr9_measurable_pairEnergy
      (HRS.MS.Comm.comm_meas (s := s) (gradient χ) hv1.continuous.measurable)).sub measurable_const)
  have hBL2 : MemLp (fun X : EucConfig d N => Bq d s a β γ N χ X) 2 P :=
    (memLp_two_iff_integrable_sq hBm.aestronglyMeasurable).2 hBi2
  have hYvL2 : MemLp Yv 2 P := s99_memLp_two_of_bdd hYvm hYvb
  have hYvsq : ∫ X, (Yv X) ^ 2 ∂P ≤ (KY * cv) ^ 2 := (hY2 N hN cv hcv0 v hvm hvbd).2
  -- Cauchy-Schwarz for the remainder
  have hRv : ∫ X, |r X| * |Yv X| ∂P ≤ KB * Bu * (KY * cv) / Real.sqrt N := by
    have hcs := s99_cs_bd hBL2 hYvL2 hB2 hYvsq (mul_nonneg hKB0 hBu0) (mul_nonneg hKY0 hcv0)
    have e : ∀ X : EucConfig d N, |r X| * |Yv X| = |Bq d s a β γ N χ X| * |Yv X| / Real.sqrt N := by
      intro X
      rw [hsqrt X, abs_div, abs_neg, abs_of_pos hsqN]; ring
    simp_rw [e]
    rw [integral_div]
    exact div_le_div_of_nonneg_right hcs hsqN.le
  have hrL2 : MemLp r 2 P := by
    have e : r = fun X => -(Real.sqrt N)⁻¹ * Bq d s a β γ N χ X := by
      funext X
      rw [hsqrt X]; ring
    rw [e]
    exact hBL2.const_mul _
  have hrY_int : Integrable (fun X : EucConfig d N => |r X| * |Yv X|) P := by
    have hfa : MemLp (fun X : EucConfig d N => |r X|) 2 P := hrL2.abs
    have hga : MemLp (fun X : EucConfig d N => |Yv X|) 2 P := hYvL2.abs
    exact hfa.integrable_mul hga
  have key : ∀ g : EucConfig d N → ℝ, (∀ X, |g X| ≤ 1) →
      |∫ X, r X * (Yv X * g X) ∂P| ≤ ∫ X, |r X| * |Yv X| ∂P := by
    intro g hg
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => norm_nonneg _) hrY_int
      (Filter.Eventually.of_forall fun X => ?_)
    show ‖r X * (Yv X * g X)‖ ≤ |r X| * |Yv X|
    rw [Real.norm_eq_abs, abs_mul (r X), abs_mul (Yv X)]
    calc |r X| * (|Yv X| * |g X|) ≤ |r X| * (|Yv X| * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hg X) (abs_nonneg _)) (abs_nonneg _)
      _ = |r X| * |Yv X| := by rw [mul_one]
  -- the mixed linear term
  have hTe : ∀ X : EucConfig d N, γ⁻¹ * pair (empirical X) (fun x => ⟪gradient χ x, gradient v x⟫) =
      pair (empirical X) wuv := fun X => (s99_pair_smul hN1 γ⁻¹ _ X).symm
  have hTm : Measurable fun X : EucConfig d N => pair (empirical X) wuv :=
    s45_measurable_pair_empirical hN1 hwuvm
  have hTbd : ∀ X : EucConfig d N, |pair (empirical X) wuv| ≤ Cuv := fun X =>
    s45_abs_pair_empirical_le hN1 hwuvbd X
  have hE1' : (∫ X, Yu X * (Yv X * ψ (featureVec φ ν X)) ∂P) =
      (∫ X, r X * (Yv X * ψ (featureVec φ ν X)) ∂P) +
        (∑' l, ∫ X, (γ⁻¹ * pair (empirical X) (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
          (Yv X * pd ψ l (featureVec φ ν X)) ∂P) +
        ∫ X, pair (empirical X) wuv * ψ (featureVec φ ν X) ∂P := by
    have := hE1
    simp_rw [hTe] at this
    exact this
  have hE0' : (∫ X, Yu X * Yv X ∂P) =
      (∫ X, r X * Yv X ∂P) + ∫ X, pair (empirical X) wuv ∂P := by
    have := hE0
    simp_rw [hTe] at this
    exact this
  -- the three pieces
  set RR1 : ℝ := ∫ X, r X * (Yv X * ψ (featureVec φ ν X)) ∂P with hRR1
  set RR0 : ℝ := ∫ X, r X * Yv X ∂P with hRR0
  set TT1 : ℝ := ∫ X, pair (empirical X) wuv * ψ (featureVec φ ν X) ∂P with hTT1
  set TT0 : ℝ := ∫ X, pair (empirical X) wuv ∂P with hTT0
  have hA1 : |RR1 - RR0 * Eψ| ≤ 2 * (KB * Bu * (KY * cv) / Real.sqrt N) := by
    have h1 : |RR1| ≤ ∫ X, |r X| * |Yv X| ∂P := key _ hψW_b
    have h0 : |RR0| ≤ ∫ X, |r X| * |Yv X| ∂P := by
      have := key (fun _ => (1 : ℝ)) (fun X => by simp)
      simpa [hRR0] using this
    calc |RR1 - RR0 * Eψ| ≤ |RR1| + |RR0| * |Eψ| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul]
      _ ≤ (KB * Bu * (KY * cv) / Real.sqrt N) + (KB * Bu * (KY * cv) / Real.sqrt N) * 1 := by
          refine add_le_add (h1.trans hRv) (mul_le_mul (h0.trans hRv) hEψb (abs_nonneg _) ?_)
          exact (abs_nonneg _).trans (h0.trans hRv)
      _ = _ := by ring
  have hA3 : |TT1 - TT0 * Eψ| ≤ 2 * (KT1 * Cuv / Real.sqrt N) := by
    set c0 : ℝ := pair (thermalMeasure d s a β) wuv with hc0
    have hTi : Integrable (fun X : EucConfig d N => pair (empirical X) wuv) P :=
      Integrable.of_bound hTm.aestronglyMeasurable Cuv (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact hTbd X)
    have hψi : Integrable (fun X : EucConfig d N => ψ (featureVec φ ν X)) P :=
      Integrable.of_bound hψW_m.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact hψW_b X)
    have hTψi : Integrable (fun X : EucConfig d N => pair (empirical X) wuv * ψ (featureVec φ ν X)) P :=
      Integrable.of_bound (hTm.mul hψW_m).aestronglyMeasurable (Cuv * 1)
        (Filter.Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hTbd X) (hψW_b X) (abs_nonneg _) hCuv0)
    have hid : TT1 - TT0 * Eψ = ∫ X, (pair (empirical X) wuv - c0) * (ψ (featureVec φ ν X) - Eψ) ∂P := by
      have e : (fun X : EucConfig d N => (pair (empirical X) wuv - c0) * (ψ (featureVec φ ν X) - Eψ)) =
          fun X => (pair (empirical X) wuv * ψ (featureVec φ ν X) -
            Eψ * pair (empirical X) wuv) - c0 * (ψ (featureVec φ ν X) - Eψ) := by
        funext X; ring
      have i1 : Integrable (fun X : EucConfig d N => pair (empirical X) wuv * ψ (featureVec φ ν X) -
          Eψ * pair (empirical X) wuv) P := hTψi.sub (hTi.const_mul Eψ)
      have i2 : Integrable (fun X : EucConfig d N => c0 * (ψ (featureVec φ ν X) - Eψ)) P :=
        (hψi.sub (integrable_const _)).const_mul c0
      have i3 : Integrable (fun X : EucConfig d N => Eψ * pair (empirical X) wuv) P := hTi.const_mul Eψ
      have i4 : Integrable (fun X : EucConfig d N => ψ (featureVec φ ν X) - Eψ) P :=
        hψi.sub (integrable_const _)
      rw [e, integral_sub i1 i2, integral_sub hTψi i3, integral_const_mul, integral_const_mul,
        integral_sub hψi (integrable_const _)]
      simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
      rw [← hEψ]
      simp only [hTT1, hTT0]
      ring
    rw [hid, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hL1 := hT1 N hN hCuv0 hwuvm hwuvbd
    have hint : Integrable (fun X : EucConfig d N => 2 * |pair (empirical X) wuv - c0|) P := by
      refine Integrable.of_bound ((hTm.sub measurable_const).abs.const_mul 2).aestronglyMeasurable
        (2 * (Cuv + |c0|)) (Filter.Eventually.of_forall fun X => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_two]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hTbd X) le_rfl)) (by norm_num)
    have := integral_mono_of_nonneg (μ := P)
      (f := fun X : EucConfig d N => ‖(pair (empirical X) wuv - c0) * (ψ (featureVec φ ν X) - Eψ)‖)
      (g := fun X => 2 * |pair (empirical X) wuv - c0|) (Filter.Eventually.of_forall fun X => norm_nonneg _)
      hint (Filter.Eventually.of_forall fun X => by
        beta_reduce
        rw [Real.norm_eq_abs, abs_mul]
        have h3 : |ψ (featureVec φ ν X) - Eψ| ≤ 2 :=
          (abs_sub _ _).trans (by linarith [hψW_b X, hEψb])
        calc |pair (empirical X) wuv - c0| * |ψ (featureVec φ ν X) - Eψ|
            ≤ |pair (empirical X) wuv - c0| * 2 := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
          _ = _ := mul_comm _ _)
    refine this.trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hL1 (by norm_num)
  -- the series
  set Gm : ℕ → ℕ → ℝ := fun l q => ∫ z, pd (pd ψ l) q z ∂G with hGm
  have hGb : ∀ l q, |Gm l q| ≤ 1 := fun l q => by
    have := norm_integral_le_of_norm_le_const (μ := G) (f := pd (pd ψ l) q) (C := 1)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact ((hψ.pd l).pd q).abs_le z)
    simpa [Real.norm_eq_abs, hGm] using this
  have hκb : ∀ l, |kap d s a β γ u φ l| ≤ cu * (F.K * b l) := fun l =>
    s99_kap_bd hd hs0 hs ha hβ hγ hT hS hφ F hum hubd l
  have hκv : ∀ q, |kap d s a β γ v φ q| ≤ cv * (F.K * b q) := fun q =>
    s99_kap_bd hd hs0 hs ha hβ hγ hT hS hφ F hvm hvbd q
  have hFK0 := F.hK
  have hSl_sum : ∀ l, Summable fun q => kap d s a β γ v φ q * Gm l q := fun l =>
    Summable.of_norm_bounded (hbs.mul_left (cv * F.K)) (fun q => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |kap d s a β γ v φ q| * |Gm l q| ≤ (cv * (F.K * b q)) * 1 :=
            mul_le_mul (hκv q) (hGb l q) (abs_nonneg _) (by have := hb0 q; positivity)
        _ = cv * F.K * b q := by ring)
  set Sl : ℕ → ℝ := fun l => ∑' q, kap d s a β γ v φ q * Gm l q with hSl
  have hSlb : ∀ l, |Sl l| ≤ cv * F.K * Sb := fun l => by
    have hg : HasSum (fun q => cv * F.K * b q) (cv * F.K * Sb) := hbs.hasSum.mul_left _
    have := tsum_of_norm_bounded hg (f := fun q => kap d s a β γ v φ q * Gm l q) (fun q => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |kap d s a β γ v φ q| * |Gm l q| ≤ (cv * (F.K * b q)) * 1 :=
            mul_le_mul (hκv q) (hGb l q) (abs_nonneg _) (by have := hb0 q; positivity)
        _ = cv * F.K * b q := by ring)
    rwa [Real.norm_eq_abs] at this
  have hMeq : (∑' l, ∑' q, kap d s a β γ u φ l * kap d s a β γ v φ q * Gm l q) =
      ∑' l, kap d s a β γ u φ l * Sl l := by
    refine tsum_congr fun l => ?_
    simp only [hSl]
    rw [← tsum_mul_left]
    refine tsum_congr fun q => ?_
    ring
  set Al : ℕ → ℝ := fun l => ∫ X, (γ⁻¹ * pair (empirical X) (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
      (Yv X * pd ψ l (featureVec φ ν X)) ∂P with hAl
  have hDφ : ∀ m x, ‖fderiv ℝ (φ m) x‖ ≤ b m := fun m x => s45_cb_deriv_le hJ1 (hφ.1 m) x
  have hAlb : ∀ l, ‖Al l‖ ≤ (γ⁻¹ * Bu * b l) * (2 * Real.sqrt N * cv) := fun l => by
    have := norm_integral_le_of_norm_le_const (μ := P) (C := (γ⁻¹ * Bu * b l) * (2 * Real.sqrt N * cv))
      (f := fun X : EucConfig d N => (γ⁻¹ * pair (empirical X) (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
        (Yv X * pd ψ l (featureVec φ ν X)))
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
        have h1 : |pair (empirical X) (fun x => ⟪gradient χ x, gradient (φ l) x⟫)| ≤ Bu * b l :=
          s45_abs_pair_empirical_le hN1 (fun x => s99_inner_grad_le hwf.B1 (hDφ l) x) X
        have h2 : |pd ψ l (featureVec φ ν X)| ≤ 1 := ((hψ.pd l).abs_le _)
        have hb' := hb0 l
        calc γ⁻¹ * |pair (empirical X) (fun x => ⟪gradient χ x, gradient (φ l) x⟫)| *
              (|Yv X| * |pd ψ l (featureVec φ ν X)|)
            ≤ (γ⁻¹ * (Bu * b l)) * ((2 * Real.sqrt N * cv) * 1) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hγ.le))
                (mul_le_mul (hYvb X) h2 (abs_nonneg _) (by positivity)) (by positivity) (by positivity)
          _ = _ := by ring)
    refine this.trans ?_
    simp
  have hAl_sum : Summable Al := Summable.of_norm_bounded
    (hbs.mul_left (γ⁻¹ * Bu * (2 * Real.sqrt N * cv))) (fun l => (hAlb l).trans (le_of_eq (by ring)))
  have hBl_sum : Summable fun l => kap d s a β γ u φ l * Sl l := Summable.of_norm_bounded
    (hbs.mul_left (cu * F.K * (cv * F.K * Sb))) (fun l => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |kap d s a β γ u φ l| * |Sl l| ≤ (cu * (F.K * b l)) * (cv * F.K * Sb) :=
            mul_le_mul (hκb l) (hSlb l) (abs_nonneg _) (by have := hb0 l; positivity)
        _ = cu * F.K * (cv * F.K * Sb) * b l := by ring)
  have hdl : ∀ l, ‖Al l - kap d s a β γ u φ l * Sl l‖ ≤ KM * Bu * cv * b l / Real.sqrt N := fun l => by
    rw [Real.norm_eq_abs]
    exact hMl N hN hu hv hwf hgen hψ l
  have hS2 : |(∑' l, Al l) - ∑' l, kap d s a β γ u φ l * Sl l| ≤ KM * Bu * cv * Sb / Real.sqrt N := by
    have hg : HasSum (fun l => KM * Bu * cv / Real.sqrt N * b l) (KM * Bu * cv / Real.sqrt N * Sb) :=
      hbs.hasSum.mul_left _
    have := tsum_of_norm_bounded hg (f := fun l => Al l - kap d s a β γ u φ l * Sl l) (fun l =>
      (hdl l).trans (le_of_eq (by ring)))
    rw [hAl_sum.tsum_sub hBl_sum] at this
    rw [← Real.norm_eq_abs]
    refine this.trans (le_of_eq ?_)
    ring
  -- assembly
  rw [hE1', hE0', hMeq]
  have hfin : (RR1 + (∑' l, Al l) + TT1) - (RR0 + TT0) * Eψ - ∑' l, kap d s a β γ u φ l * Sl l =
      (RR1 - RR0 * Eψ) + ((∑' l, Al l) - ∑' l, kap d s a β γ u φ l * Sl l) + (TT1 - TT0 * Eψ) := by
    ring
  show |(RR1 + (∑' l, Al l) + TT1) - (RR0 + TT0) * Eψ - ∑' l, kap d s a β γ u φ l * Sl l| ≤ K / Real.sqrt N
  rw [hfin]
  calc |(RR1 - RR0 * Eψ) + ((∑' l, Al l) - ∑' l, kap d s a β γ u φ l * Sl l) + (TT1 - TT0 * Eψ)|
      ≤ |RR1 - RR0 * Eψ| + |(∑' l, Al l) - ∑' l, kap d s a β γ u φ l * Sl l| + |TT1 - TT0 * Eψ| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * (KB * Bu * (KY * cv) / Real.sqrt N) + KM * Bu * cv * Sb / Real.sqrt N +
          2 * (KT1 * Cuv / Real.sqrt N) := add_le_add (add_le_add hA1 hS2) hA3
    _ = K / Real.sqrt N := by simp only [hKdef]; ring


end Mab

end S99

end
