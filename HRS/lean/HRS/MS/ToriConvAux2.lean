import HRS.MS.ToriConvAux1

/-!
# MS-TORI-DRIFTCONV, helper file 2: convergence of the cube operators to the whole-space operator (order 0)

`tcv_conv0`: if `g_L → g` locally uniformly, with uniform bounds on `g_L, Dg_L` and uniformly small tails of
`‖g_L(x - ·)‖` on the cube and of `‖g(x - ·)‖` on the whole space, then
`T^{Q_L}_{k_L} g_L → T^E_{k_E} g` uniformly on compacts.  The proof splits `Q_L` (resp. `ℝ^d`) into
`B_δ`, the annulus `B_R ∖ B_δ`, and the tail.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriConv

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.ToriCoefA HRS.MS.ToriCoefB

variable {d : ℕ}

theorem tcv_ind_norm_le {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (a : W) (z : Euc d) :
    ‖(tcb_N d).indicator (fun _ => a) z‖ ≤ ‖a‖ := by
  by_cases h : z ∈ tcb_N d
  · simp [h]
  · simp [h]

theorem tcv_ind_sub_le {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (a b : W) (z : Euc d) :
    ‖(tcb_N d).indicator (fun _ => a) z - (tcb_N d).indicator (fun _ => b) z‖ ≤ ‖a - b‖ := by
  by_cases h : z ∈ tcb_N d
  · simp [h]
  · simp [h]

theorem tcv_Q_sdiff_ball (d : ℕ) (L R : ℝ) :
    tcb_Q d L \ Metric.closedBall (0 : Euc d) R = tcb_Q d L ∩ {z : Euc d | R < ‖z‖} := by
  ext z
  simp only [mem_diff, mem_inter_iff, mem_setOf_eq, Metric.mem_closedBall, dist_zero_right, not_le]

theorem tcv_ball_subset_Q {L R : ℝ} (hR : 2 * R + 1 ≤ L) :
    Metric.closedBall (0 : Euc d) R ⊆ tcb_Q d L := by
  intro z hz i
  have h1 : ‖z‖ ≤ R := by simpa using hz
  have h2 : |z i| ≤ ‖z‖ := by
    have := PiLp.norm_apply_le z i
    rwa [Real.norm_eq_abs] at this
  have := abs_le.1 (h2.trans h1)
  have hR0 : 0 ≤ R := (norm_nonneg z).trans h1
  constructor <;> linarith [this.1, this.2]

theorem tcv_conv0 {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {s : ℝ} {kL : ℝ → Euc d → ℝ} {kE : Euc d → ℝ} {Kf Cn : ℝ} (hd : 1 ≤ d) (hsd : s < d)
    (hk : tcv_Kerns d s kL kE Kf Cn)
    (gL : ℝ → Euc d → W) (g : Euc d → W) (B0 B1 L₁ : ℝ)
    (hgLd : ∀ L : ℝ, L₁ ≤ L → Differentiable ℝ (gL L))
    (hgL0 : ∀ L : ℝ, L₁ ≤ L → ∀ y, ‖gL L y‖ ≤ B0)
    (hgL1 : ∀ L : ℝ, L₁ ≤ L → ∀ y, ‖fderiv ℝ (gL L) y‖ ≤ B1)
    (hgd : Differentiable ℝ g) (hg0 : ∀ y, ‖g y‖ ≤ B0) (hg1 : ∀ y, ‖fderiv ℝ g y‖ ≤ B1)
    (hgint : Integrable g)
    (hconv : ∀ K : Set (Euc d), IsCompact K → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ y ∈ K, ‖gL L y - g y‖ ≤ η)
    (htail : ∀ K : Set (Euc d), IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∃ L₂ : ℝ, ∀ L : ℝ, L₂ ≤ L → ∀ x ∈ K,
        (∫ z in tcb_Q d L ∩ {z : Euc d | R < ‖z‖}, ‖gL L (x - z)‖) ≤ ε ∧
        ∫ z in {z : Euc d | R < ‖z‖}, ‖g (x - z)‖ ≤ ε)
    (K : Set (Euc d)) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ x ∈ K,
      ‖tcb_T L (kL L) (gL L) x - tcv_TE kE g x‖ ≤ ε := by
  classical
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hg0 0)
  have hB1 : 0 ≤ B1 := (norm_nonneg _).trans (hg1 0)
  have hCn := hk.hCn
  have hKf := hk.hKf
  obtain ⟨RK, hRK⟩ := hK.isBounded.exists_norm_le
  have hε5 : 0 < ε / 5 := by positivity
  -- the radius `δ`
  have hden1 : 0 < 5 * (Cn * B1 + 1) := by nlinarith [mul_nonneg hCn hB1]
  have hε1 : 0 < ε / (5 * (Cn * B1 + 1)) := div_pos hε hden1
  obtain ⟨δ, hδ0, hδ4, hδJ⟩ := tcv_near_small hd hsd _ hε1
  have hJ0 : 0 ≤ ∫ z in Metric.closedBall (0 : Euc d) δ, ‖z‖ ^ (-s) :=
    setIntegral_nonneg measurableSet_closedBall fun z _ => Real.rpow_nonneg (norm_nonneg _) _
  have hnear_const : Cn * B1 * (∫ z in Metric.closedBall (0 : Euc d) δ, ‖z‖ ^ (-s)) ≤ ε / 5 := by
    have h1 := mul_le_mul_of_nonneg_left hδJ (mul_nonneg hCn hB1)
    have h2 : Cn * B1 * (ε / (5 * (Cn * B1 + 1))) ≤ (Cn * B1 + 1) * (ε / (5 * (Cn * B1 + 1))) := by
      nlinarith
    have h3 : (Cn * B1 + 1) * (ε / (5 * (Cn * B1 + 1))) = ε / 5 := by
      field_simp
    linarith
  -- the radius `R`
  have hden2 : 0 < 5 * (Kf + 1) := by nlinarith
  have hε2 : 0 < ε / (5 * (Kf + 1)) := div_pos hε hden2
  obtain ⟨R₀, hR₀⟩ := htail K hK _ hε2
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max R₀ 1 := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by rw [hR]; exact le_max_right _ _
  obtain ⟨L₂, hL₂⟩ := hR₀ R (by rw [hR]; exact le_max_left _ _)
  have hKfε : Kf * (ε / (5 * (Kf + 1))) ≤ ε / 5 := by
    have h2 : Kf * (ε / (5 * (Kf + 1))) ≤ (Kf + 1) * (ε / (5 * (Kf + 1))) := by nlinarith
    have h3 : (Kf + 1) * (ε / (5 * (Kf + 1))) = ε / 5 := by field_simp
    linarith
  -- the annulus constants
  obtain ⟨Cδ, hCδ⟩ := hk.awayE δ hδ0
  obtain ⟨Cδ', hCδ'⟩ : ∃ C : ℝ, C = max Cδ 0 := ⟨_, rfl⟩
  have hCδ'0 : 0 ≤ Cδ' := by rw [hCδ']; exact le_max_right _ _
  have hCδ'1 : ∀ z : Euc d, δ ≤ ‖z‖ → |kE z| ≤ Cδ' := fun z hz => by
    rw [hCδ']; exact (hCδ z hz).trans (le_max_left _ _)
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = volume.real (Metric.closedBall (0 : Euc d) R) := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := by rw [hV]; exact measureReal_nonneg
  have hden3 : 0 < 5 * (V * (2 * B0 + 2 * Cδ') + 1) := by
    nlinarith [mul_nonneg hV0 (by linarith : 0 ≤ 2 * B0 + 2 * Cδ')]
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / (5 * (V * (2 * B0 + 2 * Cδ') + 1)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact div_pos hε hden3
  have hann_const : (η * (2 * B0) + Cδ' * (2 * η)) * V ≤ ε / 5 := by
    have e1 : (η * (2 * B0) + Cδ' * (2 * η)) * V = (V * (2 * B0 + 2 * Cδ')) * η := by ring
    have h2 : (V * (2 * B0 + 2 * Cδ')) * η ≤ (V * (2 * B0 + 2 * Cδ') + 1) * η := by nlinarith
    have h3 : (V * (2 * B0 + 2 * Cδ') + 1) * η = ε / 5 := by
      rw [hη]; field_simp
    linarith
  obtain ⟨L₃, hL₃⟩ := hk.conv δ R η hδ0 hη0
  obtain ⟨L₄, hL₄⟩ := hconv (Metric.closedBall (0 : Euc d) (RK + R)) (isCompact_closedBall _ _) η hη0
  refine ⟨max (max L₁ 1) (max L₂ (max L₃ (max L₄ (2 * R + 1)))), ?_⟩
  intro L hL x hx
  have hLL1 : L₁ ≤ L := (le_max_left L₁ 1).trans ((le_max_left _ _).trans hL)
  have hL1' : 1 ≤ L := (le_max_right L₁ 1).trans ((le_max_left _ _).trans hL)
  have hLL2 : L₂ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLL3 : L₃ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hL))
  have hLL4 : L₄ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hL)))
  have hLL5 : 2 * R + 1 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hL)))
  have hBQ : Metric.closedBall (0 : Euc d) R ⊆ tcb_Q d L := tcv_ball_subset_Q hLL5
  have hmBR : MeasurableSet (Metric.closedBall (0 : Euc d) R) := measurableSet_closedBall
  have hmBδ : MeasurableSet (Metric.closedBall (0 : Euc d) δ) := measurableSet_closedBall
  have hδR : Metric.closedBall (0 : Euc d) δ ⊆ Metric.closedBall 0 R :=
    Metric.closedBall_subset_closedBall (by linarith)
  have hδball : Metric.closedBall (0 : Euc d) δ ⊆ Metric.ball 0 (1 / 2) :=
    Metric.closedBall_subset_ball (by linarith)
  obtain ⟨FL, hFL⟩ : ∃ FL : Euc d → W, FL = tcb_F (kL L) (gL L) x := ⟨_, rfl⟩
  obtain ⟨FE, hFE⟩ : ∃ FE : Euc d → W, FE = tcb_F kE g x := ⟨_, rfl⟩
  have hFLint : IntegrableOn FL (tcb_Q d L) volume := by
    rw [hFL]
    exact tcb_F_integrable (hk.kern L hL1') (gL L) (hgLd L hLL1) B0 B1 (hgL0 L hLL1)
      (hgL1 L hLL1) x
  have hFEint : Integrable FE := by
    rw [hFE]
    exact tcv_F_integrable_E hd hsd hk g hgd B1 hg1 hgint x
  -- decompositions
  have hTL : tcb_T L (kL L) (gL L) x = (∫ z in Metric.closedBall (0 : Euc d) δ, FL z) +
      (∫ z in Metric.closedBall (0 : Euc d) R \ Metric.closedBall (0 : Euc d) δ, FL z) +
      ∫ z in tcb_Q d L \ Metric.closedBall (0 : Euc d) R, FL z := by
    have e1 := integral_inter_add_sdiff (μ := volume) (f := FL) (s := tcb_Q d L) hmBR hFLint
    rw [inter_eq_right.2 hBQ] at e1
    have e2 := integral_inter_add_sdiff (μ := volume) (f := FL)
      (s := Metric.closedBall (0 : Euc d) R) hmBδ (hFLint.mono_set hBQ)
    rw [inter_eq_right.2 hδR] at e2
    have e0 : tcb_T L (kL L) (gL L) x = ∫ z in tcb_Q d L, FL z := by rw [hFL]; rfl
    rw [e0, ← e1, ← e2]
  have hTE : tcv_TE kE g x = (∫ z in Metric.closedBall (0 : Euc d) δ, FE z) +
      (∫ z in Metric.closedBall (0 : Euc d) R \ Metric.closedBall (0 : Euc d) δ, FE z) +
      ∫ z in (univ : Set (Euc d)) \ Metric.closedBall (0 : Euc d) R, FE z := by
    have e1 := integral_inter_add_sdiff (μ := volume) (f := FE) (s := (univ : Set (Euc d)))
      hmBR hFEint.integrableOn
    rw [univ_inter, setIntegral_univ] at e1
    have e2 := integral_inter_add_sdiff (μ := volume) (f := FE)
      (s := Metric.closedBall (0 : Euc d) R) hmBδ hFEint.integrableOn
    rw [inter_eq_right.2 hδR] at e2
    have e0 : tcv_TE kE g x = ∫ z, FE z := by rw [hFE]; rfl
    rw [e0, ← e1, ← e2]
  -- the near parts
  have hrp : Integrable (fun z : Euc d => Cn * B1 * ‖z‖ ^ (-s))
      (volume.restrict (Metric.closedBall (0 : Euc d) δ)) :=
    IntegrableOn.mono_set ((tcv_rpow_integrableOn hd hsd).const_mul (Cn * B1)) hδball
  have hnearL : ‖∫ z in Metric.closedBall (0 : Euc d) δ, FL z‖ ≤ ε / 5 := by
    refine (norm_integral_le_of_norm_le hrp ?_).trans ?_
    · refine ae_restrict_of_forall_mem hmBδ fun z hz => ?_
      have hz1 : ‖z‖ ≤ δ := by simpa using hz
      have h1 := tcv_F_near (kL L) (gL L) (hgLd L hLL1) B1 (hgL1 L hLL1) x z (hz1.trans hδ4)
      have h2 := hk.near L hL1' z (by linarith)
      rw [hFL]
      calc ‖tcb_F (kL L) (gL L) x z‖ ≤ |kL L z| * ‖z‖ * B1 := h1
        _ ≤ Cn * ‖z‖ ^ (-s) * B1 := mul_le_mul_of_nonneg_right h2 hB1
        _ = Cn * B1 * ‖z‖ ^ (-s) := by ring
    · rw [integral_const_mul]; exact hnear_const
  have hnearE : ‖∫ z in Metric.closedBall (0 : Euc d) δ, FE z‖ ≤ ε / 5 := by
    refine (norm_integral_le_of_norm_le hrp ?_).trans ?_
    · refine ae_restrict_of_forall_mem hmBδ fun z hz => ?_
      have hz1 : ‖z‖ ≤ δ := by simpa using hz
      have h1 := tcv_F_near kE g hgd B1 hg1 x z (hz1.trans hδ4)
      have h2 := hk.nearE z (by linarith)
      rw [hFE]
      calc ‖tcb_F kE g x z‖ ≤ |kE z| * ‖z‖ * B1 := h1
        _ ≤ Cn * ‖z‖ ^ (-s) * B1 := mul_le_mul_of_nonneg_right h2 hB1
        _ = Cn * B1 * ‖z‖ ^ (-s) := by ring
    · rw [integral_const_mul]; exact hnear_const
  -- the annulus
  have hann : ‖(∫ z in Metric.closedBall (0 : Euc d) R \ Metric.closedBall (0 : Euc d) δ, FL z) -
      ∫ z in Metric.closedBall (0 : Euc d) R \ Metric.closedBall (0 : Euc d) δ, FE z‖ ≤ ε / 5 := by
    have hi1 : IntegrableOn FL (Metric.closedBall (0 : Euc d) R \ Metric.closedBall (0 : Euc d) δ) :=
      (hFLint.mono_set hBQ).mono_set sdiff_subset
    have hi2 : IntegrableOn FE (Metric.closedBall (0 : Euc d) R \ Metric.closedBall (0 : Euc d) δ) :=
      hFEint.integrableOn
    rw [← integral_sub hi1 hi2]
    have hvol : volume (Metric.closedBall (0 : Euc d) R \ Metric.closedBall (0 : Euc d) δ) < ⊤ :=
      (measure_mono sdiff_subset).trans_lt measure_closedBall_lt_top
    have hbd := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (f := fun z => FL z - FE z) (C := η * (2 * B0) + Cδ' * (2 * η)) hvol (fun z hz => ?_)
    · refine hbd.trans ?_
      have hC0 : 0 ≤ η * (2 * B0) + Cδ' * (2 * η) := by positivity
      have hmono : volume.real (Metric.closedBall (0 : Euc d) R \ Metric.closedBall (0 : Euc d) δ) ≤ V := by
        rw [hV]
        exact measureReal_mono sdiff_subset (measure_closedBall_lt_top).ne
      calc (η * (2 * B0) + Cδ' * (2 * η)) *
            volume.real (Metric.closedBall (0 : Euc d) R \ Metric.closedBall (0 : Euc d) δ)
          ≤ (η * (2 * B0) + Cδ' * (2 * η)) * V := mul_le_mul_of_nonneg_left hmono hC0
        _ ≤ ε / 5 := hann_const
    · obtain ⟨hzR, hzδ⟩ := hz
      have hzR' : ‖z‖ ≤ R := by simpa using hzR
      have hzδ' : δ ≤ ‖z‖ := by
        have : δ < ‖z‖ := by simpa using hzδ
        exact this.le
      set aL : W := gL L (x - z) - (tcb_N d).indicator (fun _ => gL L x) z with haL
      set aE : W := g (x - z) - (tcb_N d).indicator (fun _ => g x) z with haE
      have heq : FL z - FE z = (kL L z - kE z) • aL + kE z • (aL - aE) := by
        rw [hFL, hFE]
        simp only [tcb_F, sub_smul, smul_sub, haL, haE]
        abel
      have hxK : x ∈ Metric.closedBall (0 : Euc d) (RK + R) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        have := hRK x hx
        linarith
      have hxzK : x - z ∈ Metric.closedBall (0 : Euc d) (RK + R) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        have := hRK x hx
        have := norm_sub_le x z
        linarith
      have hnaL : ‖aL‖ ≤ 2 * B0 := by
        refine (norm_sub_le _ _).trans ?_
        have h1 := hgL0 L hLL1 (x - z)
        have h2 := (tcv_ind_norm_le (gL L x) z).trans (hgL0 L hLL1 x)
        linarith
      have hdaL : ‖aL - aE‖ ≤ 2 * η := by
        have e : aL - aE = (gL L (x - z) - g (x - z)) -
            ((tcb_N d).indicator (fun _ => gL L x) z - (tcb_N d).indicator (fun _ => g x) z) := by
          rw [haL, haE]; abel
        rw [e]
        refine (norm_sub_le _ _).trans ?_
        have h1 := hL₄ L hLL4 (x - z) hxzK
        have h2 := (tcv_ind_sub_le (gL L x) (g x) z).trans (hL₄ L hLL4 x hxK)
        linarith
      have hk1 : |kL L z - kE z| ≤ η := hL₃ L hLL3 z hzδ' hzR'
      have hk2 : |kE z| ≤ Cδ' := hCδ'1 z hzδ'
      rw [heq]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have t1 : |kL L z - kE z| * ‖aL‖ ≤ η * (2 * B0) :=
        mul_le_mul hk1 hnaL (norm_nonneg _) hη0.le
      have t2 : |kE z| * ‖aL - aE‖ ≤ Cδ' * (2 * η) :=
        mul_le_mul hk2 hdaL (norm_nonneg _) hCδ'0
      linarith
  -- the tails
  have hmQ : MeasurableSet (tcb_Q d L) := tcb_measurableSet_Q L
  have htailL : ‖∫ z in tcb_Q d L \ Metric.closedBall (0 : Euc d) R, FL z‖ ≤ ε / 5 := by
    have hint2 : IntegrableOn (fun z => ‖gL L (x - z)‖) (tcb_Q d L) volume := by
      have : IsFiniteMeasure (volume.restrict (tcb_Q d L)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact tcb_measure_Q_lt_top L⟩
      refine Integrable.mono' (integrable_const B0)
        ((((hgLd L hLL1).continuous).comp (continuous_const.sub continuous_id)).norm.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => ?_)
      rw [norm_norm]; exact hgL0 L hLL1 _
    have hint2' : Integrable (fun z => Kf * ‖gL L (x - z)‖)
        (volume.restrict (tcb_Q d L \ Metric.closedBall (0 : Euc d) R)) :=
      (IntegrableOn.mono_set hint2 sdiff_subset).const_mul Kf
    refine (norm_integral_le_of_norm_le hint2' ?_).trans ?_
    · refine ae_restrict_of_forall_mem (hmQ.diff hmBR) fun z hz => ?_
      obtain ⟨hzQ, hzR⟩ := hz
      have hzR' : R < ‖z‖ := by simpa using hzR
      have hz4 : ¬ ‖z‖ ≤ 1 / 4 := by intro h; linarith
      rw [hFL, tcv_F_far _ _ x z hz4, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ((hk.kern L hL1').far z hzQ hz4) (norm_nonneg _)
    · rw [integral_const_mul, tcv_Q_sdiff_ball]
      have := (hL₂ L hLL2 x hx).1
      exact (mul_le_mul_of_nonneg_left this hKf).trans hKfε
  have htailE : ‖∫ z in (univ : Set (Euc d)) \ Metric.closedBall (0 : Euc d) R, FE z‖ ≤ ε / 5 := by
    have hint2' : Integrable (fun z => Kf * ‖g (x - z)‖)
        (volume.restrict ((univ : Set (Euc d)) \ Metric.closedBall (0 : Euc d) R)) :=
      ((hgint.comp_sub_left x).norm.const_mul Kf).integrableOn
    refine (norm_integral_le_of_norm_le hint2' ?_).trans ?_
    · refine ae_restrict_of_forall_mem (MeasurableSet.univ.diff hmBR) fun z hz => ?_
      obtain ⟨-, hzR⟩ := hz
      have hzR' : R < ‖z‖ := by simpa using hzR
      have hz4 : ¬ ‖z‖ ≤ 1 / 4 := by intro h; linarith
      rw [hFE, tcv_F_far _ _ x z hz4, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hk.farE z (not_le.1 hz4)) (norm_nonneg _)
    · rw [integral_const_mul]
      have e : (univ : Set (Euc d)) \ Metric.closedBall (0 : Euc d) R = {z : Euc d | R < ‖z‖} := by
        ext z
        simp only [mem_diff, mem_univ, true_and, Metric.mem_closedBall, dist_zero_right, not_le,
          mem_setOf_eq]
      rw [e]
      have := (hL₂ L hLL2 x hx).2
      exact (mul_le_mul_of_nonneg_left this hKf).trans hKfε
  rw [hTL, hTE]
  have e : ((∫ z in Metric.closedBall (0 : Euc d) δ, FL z) +
      (∫ z in Metric.closedBall (0 : Euc d) R \ Metric.closedBall (0 : Euc d) δ, FL z) +
      ∫ z in tcb_Q d L \ Metric.closedBall (0 : Euc d) R, FL z) -
      ((∫ z in Metric.closedBall (0 : Euc d) δ, FE z) +
      (∫ z in Metric.closedBall (0 : Euc d) R \ Metric.closedBall (0 : Euc d) δ, FE z) +
      ∫ z in (univ : Set (Euc d)) \ Metric.closedBall (0 : Euc d) R, FE z) =
      ((∫ z in Metric.closedBall (0 : Euc d) δ, FL z) - ∫ z in Metric.closedBall (0 : Euc d) δ, FE z) +
      ((∫ z in Metric.closedBall (0 : Euc d) R \ Metric.closedBall (0 : Euc d) δ, FL z) -
        ∫ z in Metric.closedBall (0 : Euc d) R \ Metric.closedBall (0 : Euc d) δ, FE z) +
      ((∫ z in tcb_Q d L \ Metric.closedBall (0 : Euc d) R, FL z) -
        ∫ z in (univ : Set (Euc d)) \ Metric.closedBall (0 : Euc d) R, FE z) := by abel
  rw [e]
  refine (norm_add₃_le).trans ?_
  have h1 := norm_sub_le (∫ z in Metric.closedBall (0 : Euc d) δ, FL z)
    (∫ z in Metric.closedBall (0 : Euc d) δ, FE z)
  have h3 := norm_sub_le (∫ z in tcb_Q d L \ Metric.closedBall (0 : Euc d) R, FL z)
    (∫ z in (univ : Set (Euc d)) \ Metric.closedBall (0 : Euc d) R, FE z)
  linarith

end HRS.MS.ToriConv
