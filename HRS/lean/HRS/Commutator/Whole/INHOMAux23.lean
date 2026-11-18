import HRS.Commutator.Whole.INHOMAux22

/-!
# CMX-INHOM auxiliary 23: the cross term `(4.crosslow)` and its bound
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma inhom_inner_eq (x y : Euc d) : inner ℝ x y = ∑ i, x i * y i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma inhom_conv_add (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {b₀ b₁ : Euc d → ℝ}
    (hb₀m : Measurable b₀) {M₀ : ℝ} (hM₀ : ∀ x, |b₀ x| ≤ M₀)
    (hb₁m : Measurable b₁) {M₁ : ℝ} (hM₁ : ∀ x, |b₁ x| ≤ M₁) (x : Euc d) :
    inhom_conv (ghiForce s) (fun y => b₀ y + b₁ y) x =
      inhom_conv (ghiForce s) b₀ x + inhom_conv (ghiForce s) b₁ x := by
  unfold inhom_conv
  rw [← integral_add (inhom_conv_integrable hd hs0 hsd hb₀m hM₀ x)
    (inhom_conv_integrable hd hs0 hsd hb₁m hM₁ x)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [add_smul]

/-- `(4.crosslow)`: `𝒞_{g_{>1}}(v,a) - 𝒞_{g_{>1}}(v,a₁) = 2 ⟨a₀ v, ∇g_{>1} * a₁⟩`. -/
theorem inhom_cross_identity (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    {v : Euc d → Euc d} {L : ℝ≥0} (hL : LipschitzWith L v)
    {φ φ₀ φ₁ : SchwartzMap (Euc d) ℂ} {a a₀ a₁ : Euc d → ℝ}
    (hφ : ∀ x, φ x = ((a x : ℝ) : ℂ)) (hφ₀ : ∀ x, φ₀ x = ((a₀ x : ℝ) : ℂ))
    (hφ₁ : ∀ x, φ₁ x = ((a₁ x : ℝ) : ℂ)) (ha₁ : ∀ x, a₁ x = a x - a₀ x)
    (hF₀ : ∀ ξ, 𝓕 (⇑φ₀) ξ = cmxFB_gL d (1 / 16) ξ * 𝓕 (⇑φ) ξ) :
    CcommFun (ghiForce s) v a - CcommFun (ghiForce s) v a₁ =
      2 * ∑ i : Fin d, ∫ x, a₀ x * v x i * inhom_conv (ghiForce s) a₁ x i := by
  obtain ⟨hac, hai, ⟨M, hM⟩, ha1, ha2⟩ := inhom_schw_props hφ
  obtain ⟨ha₀c, ha₀i, ⟨M₀, hM₀⟩, ha₀1, ha₀2⟩ := inhom_schw_props hφ₀
  obtain ⟨ha₁c, ha₁i, ⟨M₁, hM₁⟩, ha₁1, ha₁2⟩ := inhom_schw_props hφ₁
  have hvc : Continuous v := hL.continuous
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hvg : ∀ x, ‖v x‖ ≤ (‖v 0‖ + L) * (1 + ‖x‖) := by
    intro x
    have h1 : ‖v x‖ ≤ ‖v 0‖ + L * ‖x‖ := by
      have := hL.dist_le_mul x 0
      simp only [dist_eq_norm, sub_zero] at this
      calc ‖v x‖ = ‖(v x - v 0) + v 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖v x - v 0‖ + ‖v 0‖ := norm_add_le _ _
        _ ≤ L * ‖x‖ + ‖v 0‖ := by gcongr
        _ = ‖v 0‖ + L * ‖x‖ := by ring
    nlinarith [norm_nonneg x, norm_nonneg (v 0), mul_nonneg hL0 (norm_nonneg x)]
  have hodd := fun z : Euc d => inhom_ghi_odd (s := s) z
  have hHm := inhom_ghi_measurable hd hs0 hsd (d := d)
  have hH1 := inhom_ghi_L1 hd hs0 hsd (d := d) (s := s)
  have hp := inhom_pairing_L1 hHm hodd hH1 hvc hvg hac hai hM
  have hp1 := inhom_pairing_L1 hHm hodd hH1 hvc hvg ha₁c ha₁i hM₁
  have haeq : a = fun y => a₀ y + a₁ y := by funext y; rw [ha₁ y]; ring
  have hadd : ∀ x, inhom_conv (ghiForce s) a x = inhom_conv (ghiForce s) a₁ x := by
    intro x
    have h1 := inhom_conv_add hd hs0 hsd ha₀c.measurable hM₀ ha₁c.measurable hM₁ x
    rw [← haeq, inhom_conv_ghi_zero hd hs0 hsd hφ₀ hF₀ x, zero_add] at h1
    exact h1
  have hconv : ∀ x, inhom_conv (ghiForce s) a x = inhom_conv (ghiForce s) a₁ x := hadd
  rw [hp, hp1]
  simp_rw [hconv]
  -- components
  have hint : ∀ (b : Euc d → ℝ), Continuous b → Integrable (fun y : Euc d => (1 + ‖y‖) * |b y|) volume →
      ∀ i : Fin d, Integrable (fun x => b x * v x i * inhom_conv (ghiForce s) a₁ x i) volume := by
    intro b hbc hbi i
    obtain ⟨hhc, Mh, hMh⟩ := inhom_h_props hd hs0 hsd hφ₁ i
    refine inhom_int_aqh hbi hbc ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hvc)
      (Cq := ‖v 0‖ + L) (fun x => ?_) hhc hMh
    have := hvg x
    have h2 : |v x i| ≤ ‖v x‖ := by simpa using PiLp.norm_apply_le (v x) i
    exact h2.trans this
  have e1 : ∀ (b : Euc d → ℝ), Continuous b →
      Integrable (fun y : Euc d => (1 + ‖y‖) * |b y|) volume →
      ∫ x, b x * inner ℝ (v x) (inhom_conv (ghiForce s) a₁ x) =
        ∑ i : Fin d, ∫ x, b x * v x i * inhom_conv (ghiForce s) a₁ x i := by
    intro b hbc hbi
    have e : ∀ x, b x * inner ℝ (v x) (inhom_conv (ghiForce s) a₁ x) =
        ∑ i : Fin d, b x * v x i * inhom_conv (ghiForce s) a₁ x i := by
      intro x
      rw [inhom_inner_eq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [e]
    exact integral_finset_sum _ (fun i _ => hint b hbc hbi i)
  rw [e1 a hac hai, e1 a₁ ha₁c ha₁i, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 2
  funext i
  rw [← integral_sub (hint a hac hai i) (hint a₁ ha₁c ha₁i i)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ha₁ x]
  ring

/-- the bound for the cross term. -/
theorem inhom_cross (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ (φ φ₀ φ₁ : SchwartzMap (Euc d) ℂ) (a a₀ a₁ : Euc d → ℝ),
        (∀ x, φ x = ((a x : ℝ) : ℂ)) → (∀ x, φ₀ x = ((a₀ x : ℝ) : ℂ)) →
        (∀ x, φ₁ x = ((a₁ x : ℝ) : ℂ)) → (∀ x, a₁ x = a x - a₀ x) →
        (∀ x, a₀ x = Pleq (1 / 16) a x) →
        (∀ ξ, 𝓕 (⇑φ₀) ξ = cmxFB_gL d (1 / 16) ξ * 𝓕 (⇑φ) ξ) →
        (∀ ξ, 𝓕 (⇑φ₁) ξ = (1 - cmxFB_gL d (1 / 16) ξ) * 𝓕 (⇑φ) ξ) →
        ENNReal.ofReal |CcommFun (ghiForce s) v a - CcommFun (ghiForce s) v a₁| ≤
          ENNReal.ofReal (C * K) * inhom_Sob (-alphaE d s) φ := by
  obtain ⟨C, hC, hcomp⟩ := inhom_cross_comp hd hs0 hsd
  refine ⟨2 * d * C, by positivity, fun v K hv φ φ₀ φ₁ a a₀ a₁ hφ hφ₀ hφ₁ ha₁ ha₀ hF₀ hF₁ => ?_⟩
  have hK0 := inhom_subTransport_nonneg hv
  obtain ⟨L, F, hF0, hL, -, hK⟩ := id hv
  rw [inhom_cross_identity hd hs0 hsd hL hφ hφ₀ hφ₁ ha₁ hF₀]
  set S := inhom_Sob (-alphaE d s) φ with hS
  set I : Fin d → ℝ := fun i => ∫ x, a₀ x * v x i * inhom_conv (ghiForce s) a₁ x i with hI
  have hI' : ∀ i, ENNReal.ofReal |I i| ≤ ENNReal.ofReal (C * K) * S := fun i =>
    hcomp v K hv φ φ₀ φ₁ a a₀ a₁ hφ hφ₀ hφ₁ ha₀ hF₀ hF₁ i
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_mul (by norm_num)]
  have hsum : ENNReal.ofReal |∑ i, I i| ≤ ∑ i : Fin d, ENNReal.ofReal |I i| := by
    calc ENNReal.ofReal |∑ i, I i| ≤ ENNReal.ofReal (∑ i, |I i|) :=
          ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
      _ = _ := ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _
  calc ENNReal.ofReal 2 * ENNReal.ofReal |∑ i, I i|
      ≤ ENNReal.ofReal 2 * ∑ i : Fin d, ENNReal.ofReal |I i| := by gcongr
    _ ≤ ENNReal.ofReal 2 * ∑ _i : Fin d, (ENNReal.ofReal (C * K) * S) := by
        gcongr with i _
        exact hI' i
    _ = ENNReal.ofReal (2 * d * C * K) * S := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have : ENNReal.ofReal (2 * d * C * K) = ENNReal.ofReal 2 * (d : ℝ≥0∞) * ENNReal.ofReal (C * K) := by
          rw [show 2 * (d : ℝ) * C * K = (2 * d) * (C * K) by ring,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]
        rw [this]; ring

end HRS.Commutator.Whole
