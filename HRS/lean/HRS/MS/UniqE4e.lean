import HRS.MS.UniqE4d
import HRS.Commutator.Whole.LocalAuxSAMP1

/-!
# E4 of `UniqPlan.md`, part 5: the commutator estimates

* `e4_lip_local`, `e4_lip_global` : mean value bounds for a `C¹` function with decaying gradient.
* `e4_comm_abs_le_loc` : `|[η_ε, a]F (y)| ≤ ε L_y η_ε * |F| (y)` if `|a x - a y| ≤ ε L_y` for `|x - y| < ε`.
* `e4_kcd_near` : Young's inequality for `H = g * ∂_iψ` on `B̄(c, 2R)`, `supp ψ ⊆ B̄(c, R)`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE4

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3 HRS.MS.UniqE3 HRS.MS.UniqN0

variable {d : ℕ}

theorem e4_lip_global {A : ℝ} {ρ : Euc d → ℝ} (hρ : ContDiff ℝ 1 ρ) {κ : ℝ} (hκ : 0 ≤ κ)
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ A * (1 + ‖y‖) ^ (-κ)) (hA : 0 ≤ A) (x y : Euc d) :
    |ρ x - ρ y| ≤ A * ‖x - y‖ := by
  have hb : ∀ ξ ∈ (univ : Set (Euc d)), ‖fderiv ℝ ρ ξ‖ ≤ A := by
    intro ξ _
    refine (h1 ξ).trans ?_
    have : (1 + ‖ξ‖) ^ (-κ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg ξ]) (by linarith)
    calc A * (1 + ‖ξ‖) ^ (-κ) ≤ A * 1 := by gcongr
      _ = A := mul_one A
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := ρ) (s := univ) (C := A)
    (fun ξ _ => hρ.differentiable (by simp) ξ) hb convex_univ (mem_univ y) (mem_univ x)
  rw [Real.norm_eq_abs] at this
  exact this

theorem e4_lip_local {A : ℝ} {ρ : Euc d → ℝ} (hρ : ContDiff ℝ 1 ρ) {κ : ℝ} (hκ : 0 ≤ κ)
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ A * (1 + ‖y‖) ^ (-κ)) (hA : 0 ≤ A) (y x : Euc d)
    (hx : ‖x - y‖ < 1) :
    |ρ x - ρ y| ≤ (A * 2 ^ κ * (1 + ‖y‖) ^ (-κ)) * ‖x - y‖ := by
  have hb : ∀ ξ ∈ ball y 1, ‖fderiv ℝ ρ ξ‖ ≤ A * 2 ^ κ * (1 + ‖y‖) ^ (-κ) := by
    intro ξ hξ
    refine (h1 ξ).trans ?_
    have := n0_decay_pt (d := d) hκ 0 ξ y (by rwa [mem_ball, dist_comm] at hξ)
    simp only [sub_zero] at this
    calc A * (1 + ‖ξ‖) ^ (-κ) ≤ A * (2 ^ κ * (1 + ‖y‖) ^ (-κ)) := by gcongr
      _ = _ := by ring
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := ρ) (s := ball y 1)
    (C := A * 2 ^ κ * (1 + ‖y‖) ^ (-κ)) (fun ξ _ => hρ.differentiable (by simp) ξ) hb
    (convex_ball y 1) (mem_ball_self one_pos) (by rwa [mem_ball, dist_eq_norm])
  rw [Real.norm_eq_abs] at this
  exact this

/-- Pointwise commutator bound with a local Lipschitz constant. -/
theorem e4_comm_abs_le_loc {ε : ℝ} (hε : 0 < ε) {a F : Euc d → ℝ} (ha : Continuous a)
    (hF : LocallyIntegrable F volume) (y : Euc d) {Ly : ℝ}
    (hL : ∀ x : Euc d, ‖x - y‖ < ε → |a x - a y| ≤ ε * Ly) :
    |comm d ε a F y| ≤ ε * Ly * moll d ε (fun x => ‖F x‖) y := by
  have hG : LocallyIntegrable (fun x => ‖F x‖) volume := by
    rw [← locallyIntegrableOn_univ] at hF ⊢
    exact hF.norm
  have hint := (m3_kernel_integrable hε y hG).const_mul (ε * Ly)
  rw [m3_comm_eq_integral hε ha hF y, ← Real.norm_eq_abs]
  calc ‖∫ x, eta d ε (y - x) * (a x - a y) * F x‖
      ≤ ∫ x, (ε * Ly) * (eta d ε (y - x) * ‖F x‖) := by
        refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun x => ?_)
        by_cases hx : eta d ε (y - x) = 0
        · simp [hx]
        · have hmem : y - x ∈ Function.support (eta d ε) := Function.mem_support.2 hx
          have hball : ‖y - x‖ < ε := mem_ball_zero_iff.1 (eta_support hε hmem)
          have hxy : ‖x - y‖ < ε := by rw [norm_sub_rev]; exact hball
          have h1 := hL x hxy
          have he : 0 ≤ eta d ε (y - x) := eta_nonneg hε _
          have key : ‖eta d ε (y - x) * (a x - a y) * F x‖
              = eta d ε (y - x) * |a x - a y| * ‖F x‖ := by
            rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg he]
          rw [key]
          calc eta d ε (y - x) * |a x - a y| * ‖F x‖
              ≤ eta d ε (y - x) * (ε * Ly) * ‖F x‖ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 he) (norm_nonneg _)
            _ = (ε * Ly) * (eta d ε (y - x) * ‖F x‖) := by ring
    _ = ε * Ly * moll d ε (fun x => ‖F x‖) y := by
        rw [integral_const_mul]
        rfl

theorem e4_comm_continuous {ε : ℝ} (hε : 0 < ε) {a F : Euc d → ℝ} (ha : Continuous a)
    (hF : LocallyIntegrable F volume) : Continuous (HRS.MS.UniqM3.comm d ε a F) :=
  (e3_moll_continuous hε (hF.continuous_mul ha)).sub
    (ha.mul (e3_moll_continuous hε hF))

/-- `LocMass` of the mollification of `|F|` (`ε ≤ 1`). -/
theorem e4_locMass_moll_abs (d : ℕ) :
    ∃ N : ℕ, ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (B : ℝ), 0 ≤ B → ∀ (F : Euc d → ℝ), LocMass B F →
      LocMass (Real.sqrt N * B) (moll d ε (fun x => ‖F x‖)) := by
  obtain ⟨N, hN⟩ := moll_mass_le_const d 1
  refine ⟨N, fun ε hε hε1 B hB F hF => ?_⟩
  have hG : LocMass B (fun x => ‖F x‖) :=
    ⟨hF.1.norm, fun c' => by simpa only [enorm_norm] using hF.2 c'⟩
  refine ⟨(e3_moll_continuous hε hG.locallyIntegrable).aestronglyMeasurable, fun c => ?_⟩
  refine (hN ε hε hε1 B _ hG c).trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), ENNReal.ofReal_mul (Nat.cast_nonneg N),
    ENNReal.ofReal_natCast]

/-- Young's inequality for `H = g * ∂_iψ` on `B̄(c, 2R)` when `supp ψ ⊆ B̄(c, R)`. -/
theorem e4_kcd_near {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {R : ℝ} (hR : 0 ≤ R) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ (c0 : Euc d) (ψ : Euc d → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      Function.support ψ ⊆ closedBall c0 R →
      ∫⁻ y in closedBall c0 (2 * R), ‖kernelConvDeriv d s i ψ y‖ₑ ^ 2 ≤
        ENNReal.ofReal (G ^ 2) * ∫⁻ x, ‖D1 i ψ x‖ₑ ^ 2 := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  set a : Euc d → ℝ≥0∞ := (closedBall (0 : Euc d) (3 * R)).indicator
    (fun z => ‖rieszKernel d s z‖ₑ) with ha
  have hint : IntegrableOn (rieszKernel d s) (closedBall (0 : Euc d) (3 * R)) volume :=
    hl.integrableOn_isCompact (isCompact_closedBall _ _)
  have ham : Measurable a :=
    ((g_meas s).enorm).indicator measurableSet_closedBall
  have hfin : ∫⁻ z, a z ≠ ⊤ := by
    rw [ha, lintegral_indicator measurableSet_closedBall]
    exact hint.hasFiniteIntegral.ne
  set G : ℝ := (∫⁻ z, a z).toReal with hG
  refine ⟨G, ENNReal.toReal_nonneg, fun c0 ψ hψ hψc hsupp => ?_⟩
  have hb : Continuous (D1 i ψ) := e3_continuous_D1 hψ i
  have hbm : Measurable fun x => ‖D1 i ψ x‖ₑ := hb.measurable.enorm
  -- pointwise bound by the convolution
  have hpt : ∀ y ∈ closedBall c0 (2 * R), ‖kernelConvDeriv d s i ψ y‖ₑ ≤
      ∫⁻ z, a z * ‖D1 i ψ (y - z)‖ₑ := by
    intro y hy
    have h1 : ‖kernelConvDeriv d s i ψ y‖ₑ ≤
        ∫⁻ x, ‖rieszKernel d s (y - x) * D1 i ψ x‖ₑ := by
      unfold kernelConvDeriv
      exact enorm_integral_le_lintegral_enorm _
    refine h1.trans ?_
    have h2 : ∀ x, ‖rieszKernel d s (y - x) * D1 i ψ x‖ₑ = a (y - x) * ‖D1 i ψ x‖ₑ := by
      intro x
      by_cases hx : D1 i ψ x = 0
      · simp [hx]
      · have hxt : x ∈ tsupport ψ := by
          by_contra hn
          apply hx
          simp [D1, e3_fderiv_eq_zero_of_notMem hn]
        have hxc : x ∈ closedBall c0 R :=
          (closure_minimal hsupp isClosed_closedBall) hxt
        have hdist : ‖y - x‖ ≤ 3 * R := by
          have h3 : ‖y - c0‖ ≤ 2 * R := by simpa [dist_eq_norm] using hy
          have h4 : ‖x - c0‖ ≤ R := by simpa [dist_eq_norm] using hxc
          calc ‖y - x‖ = ‖(y - c0) - (x - c0)‖ := by congr 1; abel
            _ ≤ ‖y - c0‖ + ‖x - c0‖ := norm_sub_le _ _
            _ ≤ 3 * R := by linarith
        have : y - x ∈ closedBall (0 : Euc d) (3 * R) := by simpa using hdist
        rw [enorm_mul, ha]
        simp only [Set.indicator_of_mem this]
    simp_rw [h2]
    have := lintegral_sub_left_eq_self (μ := (volume : Measure (Euc d)))
      (fun z => a z * ‖D1 i ψ (y - z)‖ₑ) y
    simp only [sub_sub_cancel] at this
    exact this.le
  have hyoung := HRS.Commutator.Whole.SAMP1.young_lintegral (volume : Measure (Euc d)) ham hbm
    (p := 2) (by norm_num) hfin
  have hcv : Measurable fun y => ∫⁻ z, a z * ‖D1 i ψ (y - z)‖ₑ := by
    have : Measurable (fun q : Euc d × Euc d => a q.2 * ‖D1 i ψ (q.1 - q.2)‖ₑ) :=
      (ham.comp measurable_snd).mul
        ((hb.measurable.comp (measurable_fst.sub measurable_snd)).enorm)
    exact this.lintegral_prod_right'
  calc ∫⁻ y in closedBall c0 (2 * R), ‖kernelConvDeriv d s i ψ y‖ₑ ^ 2
      ≤ ∫⁻ y in closedBall c0 (2 * R), (∫⁻ z, a z * ‖D1 i ψ (y - z)‖ₑ) ^ 2 := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy
        exact pow_le_pow_left' (hpt y hy) 2
    _ ≤ ∫⁻ y, (∫⁻ z, a z * ‖D1 i ψ (y - z)‖ₑ) ^ 2 := setLIntegral_le_lintegral _ _
    _ = ∫⁻ y, (∫⁻ z, a z * ‖D1 i ψ (y - z)‖ₑ) ^ (2 : ℝ) := by
        simp_rw [ENNReal.rpow_two]
    _ ≤ (∫⁻ z, a z) ^ (2 : ℝ) * ∫⁻ x, ‖D1 i ψ x‖ₑ ^ (2 : ℝ) := hyoung
    _ = ENNReal.ofReal (G ^ 2) * ∫⁻ x, ‖D1 i ψ x‖ₑ ^ 2 := by
        simp_rw [ENNReal.rpow_two]
        rw [hG, ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin]

end HRS.MS.UniqE4
