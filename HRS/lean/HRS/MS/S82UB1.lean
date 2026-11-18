import HRS.MS.S82UA6
import HRS.MH.PairingRdP5
import HRS.MH.PairingRdP4

/-!
# S8.2 A01 (S82U): truncated forces `F_ε` and the cancellation convolution
For a Lipschitz probability density `ρ`, `F_ε(x) = ∫_{|x-z|>ε} ρ(z) ∇g(x-z) dz` is bounded uniformly
in `ε ≤ 1/4` and converges pointwise to `forceMean ρ`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T HRS.MH.PairingRd

/-- A Lipschitz probability density. -/
structure UForce (d : ℕ) (rho : Euc d → ℝ) (Λ : ℝ) : Prop where
  prob : HRS.Whole.IsProbDensity rho
  hΛ : 0 ≤ Λ
  lip : ∀ x z : Euc d, ‖z‖ ≤ 1 / 4 → |rho (x - z) - rho x| ≤ Λ * ‖z‖ ^ (1 : ℝ)

lemma u_conv_unif {d : ℕ} (hd : 2 ≤ d) {rho : Euc d → ℝ} {Λ : ℝ} (hF : UForce d rho Λ) :
    (∀ x, Integrable (convInt (rieszKernelGrad d (criticalS d)) rho x)) ∧
      ∃ K1 : ℝ, ∀ x, ∫ z, ‖convInt (rieszKernelGrad d (criticalS d)) rho x z‖ ≤ K1 := by
  have hs0 : 0 ≤ criticalS d := by unfold criticalS; positivity
  have hsd : criticalS d < d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set s := criticalS d with hsdef
  have hρm := hF.prob.measurable
  have hint : Integrable rho := integrable_of_integral_eq_one hF.prob.integral_one
  set J : Euc d → ℝ := Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
    (fun z => ‖z‖ ^ ((1 : ℝ) - s - 1)) with hJ
  have hJint : Integrable J := by
    rw [hJ, integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    have := HRS.MP.RdGen.rg_near_integrable (d := d) (by omega) (s := s + 1 - 1) (by linarith)
    refine this.congr_fun (fun z _ => ?_) Metric.isClosed_closedBall.measurableSet
    show ‖z‖ ^ (-(s + 1 - 1)) = ‖z‖ ^ ((1 : ℝ) - s - 1)
    congr 1; ring
  set σ : ℝ := max 1 s with hσ
  have hσ0 : 0 ≤ σ := (zero_le_one).trans (le_max_left _ _)
  let m : Euc d → Euc d → ℝ := fun x y => σ * (Λ * J (x - y) + 4 ^ (s + 1) * |rho y|)
  have hmint : ∀ x, Integrable (m x) := fun x => by
    have h1 : Integrable (fun y => J (x - y)) := hJint.comp_sub_left x
    exact (((h1.const_mul Λ).add (hint.abs.const_mul _))).const_mul σ
  have : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hbd : ∀ x, ∀ᵐ y ∂(volume : Measure (Euc d)), ‖convInt (rieszKernelGrad d s) rho x y‖ ≤ m x y := by
    intro x
    have hae : ∀ᵐ y ∂(volume : Measure (Euc d)), y ≠ x :=
      compl_mem_ae_iff.mpr (measure_singleton x)
    filter_upwards [hae] with y hy
    exact HRS.MH.PairingRdP.conv_integrand_bound_rd hs0 hF.hΛ hF.lip x y hy.symm
  have hmeas : ∀ x, AEStronglyMeasurable (convInt (rieszKernelGrad d s) rho x) volume := by
    intro x
    have hG := HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) s
    have hsub : Measurable (fun y : Euc d => x - y) := measurable_const.sub measurable_id
    refine Measurable.aestronglyMeasurable ?_
    refine Measurable.ite (measurableSet_le (measurable_norm.comp hsub) measurable_const) ?_ ?_
    · exact (hρm.sub measurable_const).smul (hG.comp hsub)
    · exact hρm.smul (hG.comp hsub)
  have hI : ∀ x, ∫ y, m x y = σ * (Λ * (∫ z, J z) + 4 ^ (s + 1) * ∫ y, |rho y|) := by
    intro x
    have h1 : Integrable (fun y => J (x - y)) := hJint.comp_sub_left x
    simp only [m]
    rw [integral_const_mul, integral_add (h1.const_mul Λ) (hint.abs.const_mul _), integral_const_mul,
      integral_const_mul, integral_sub_left_eq_self J volume x]
  refine ⟨fun x => Integrable.mono' (hmint x) (hmeas x) (hbd x),
    σ * (Λ * (∫ z, J z) + 4 ^ (s + 1) * ∫ y, |rho y|), fun x => ?_⟩
  rw [← hI x]
  exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hmint x) (hbd x)

/-- truncated force `F_ε`. -/
def uFe {d : ℕ} (ε : ℝ) (rho : Euc d → ℝ) (x : Euc d) : Euc d :=
  ∫ z, (if ε < ‖x - z‖ then rho z • rieszKernelGrad d (criticalS d) (x - z) else 0)

/-- Odd truncated annulus integrates to zero. -/
lemma u_annulus_zero {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (x : Euc d) :
    ∫ z : Euc d, (if ε < ‖x - z‖ ∧ ‖x - z‖ ≤ 1 / 4 then rieszKernelGrad d (criticalS d) (x - z) else 0)
      = 0 := by
  set g : Euc d → Euc d := fun w => if ε < ‖w‖ ∧ ‖w‖ ≤ 1 / 4 then rieszKernelGrad d (criticalS d) w else 0
    with hg
  have hodd : ∀ w, g (-w) = -g w := by
    intro w
    simp only [hg, norm_neg]
    split_ifs with h
    · by_cases hw : ε < ‖w‖
      · have hw0 : w ≠ 0 := fun e => by rw [e, norm_zero] at hw; linarith
        have := u_grad_odd (x := w) (y := 0) hw0
        simpa using this
      · exact absurd h.1 hw
    · simp
  have h1 : ∫ z : Euc d, g (x - z) = ∫ w, g w := integral_sub_left_eq_self g volume x
  have h2 : ∫ w, g (-w) = ∫ w, g w := integral_neg_eq_self g volume
  have h3 : ∫ w, g (-w) = -∫ w, g w := by
    simp only [hodd]; exact integral_neg _
  have h5 : ∫ w, g w = -∫ w, g w := h2.symm.trans h3
  have h6 : (2 : ℝ) • ∫ w, g w = 0 := by
    rw [two_smul]; nth_rewrite 1 [h5]; exact neg_add_cancel _
  have h4 : ∫ w, g w = 0 := (smul_eq_zero.1 h6).resolve_left (by norm_num)
  have : (fun z : Euc d => (if ε < ‖x - z‖ ∧ ‖x - z‖ ≤ 1 / 4 then rieszKernelGrad d (criticalS d) (x - z) else 0))
      = fun z => g (x - z) := rfl
  rw [this, h1, h4]

lemma u_G_norm_le {d : ℕ} {ε : ℝ} (hε : 0 < ε) {w : Euc d} (hw : ε < ‖w‖) :
    ‖rieszKernelGrad d (criticalS d) w‖ ≤ HRS.Whole.movtr_sigma (criticalS d) * ε ^ (-criticalS d - 1) := by
  have hs0 : 0 ≤ criticalS d := by unfold criticalS; positivity
  have hw0 : w ≠ 0 := fun e => by rw [e, norm_zero] at hw; linarith
  rw [HRS.Whole.movtr_rieszKernelGrad_norm (criticalS d) hs0 hw0]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hε hw.le (by linarith))
    (s82t_sigma_nonneg _ hs0)

lemma u_trunc_integrable {d : ℕ} {ε : ℝ} (hε : 0 < ε) {rho : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity rho)
    (x : Euc d) :
    Integrable (fun z => if ε < ‖x - z‖ then rho z • rieszKernelGrad d (criticalS d) (x - z) else 0) := by
  have hint : Integrable rho := integrable_of_integral_eq_one hρ.integral_one
  have hG := HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)
  have hsub : Measurable (fun y : Euc d => x - y) := measurable_const.sub measurable_id
  refine Integrable.mono' (hint.abs.const_mul (HRS.Whole.movtr_sigma (criticalS d) * ε ^ (-criticalS d - 1)))
    (Measurable.aestronglyMeasurable (Measurable.ite (measurableSet_lt measurable_const
      (measurable_norm.comp hsub)) (hρ.measurable.smul (hG.comp hsub)) measurable_const))
    (Eventually.of_forall fun z => ?_)
  by_cases h : ε < ‖x - z‖
  · rw [if_pos h, norm_smul, Real.norm_eq_abs]
    have := u_G_norm_le hε h
    have h0 : 0 ≤ |rho z| := abs_nonneg _
    calc |rho z| * ‖rieszKernelGrad d (criticalS d) (x - z)‖
        ≤ |rho z| * (HRS.Whole.movtr_sigma (criticalS d) * ε ^ (-criticalS d - 1)) :=
          mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  · rw [if_neg h, norm_zero]
    have := s82t_sigma_nonneg (criticalS d) (by unfold criticalS; positivity)
    positivity

lemma u_Fe_eq {d : ℕ} {ε : ℝ} (hε : 0 < ε) {rho : Euc d → ℝ} {Λ : ℝ} (hF : UForce d rho Λ)
    (x : Euc d) :
    uFe ε rho x = ∫ z, (if ε < ‖x - z‖ then convInt (rieszKernelGrad d (criticalS d)) rho x z else 0) := by
  have hint : Integrable rho := integrable_of_integral_eq_one hF.prob.integral_one
  set Gf := rieszKernelGrad d (criticalS d) with hGf
  have hG := HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)
  have hsub : Measurable (fun y : Euc d => x - y) := measurable_const.sub measurable_id
  -- the annulus piece
  have hann : Integrable (fun z : Euc d => (if ε < ‖x - z‖ ∧ ‖x - z‖ ≤ 1 / 4 then Gf (x - z) else 0)) := by
    have hind : Integrable (Set.indicator (Metric.closedBall x (1 / 4))
        (fun _ => HRS.Whole.movtr_sigma (criticalS d) * ε ^ (-criticalS d - 1))) := by
      rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
      exact integrableOn_const (by simp [measure_closedBall_lt_top.ne])
    refine Integrable.mono' hind ?_ (Eventually.of_forall fun z => ?_)
    · refine Measurable.aestronglyMeasurable (Measurable.ite ?_ (hG.comp hsub) measurable_const)
      exact (measurableSet_lt measurable_const (measurable_norm.comp hsub)).inter
        (measurableSet_le (measurable_norm.comp hsub) measurable_const)
    · by_cases h : ε < ‖x - z‖ ∧ ‖x - z‖ ≤ 1 / 4
      · rw [if_pos h]
        have hz : z ∈ Metric.closedBall x (1 / 4) := by
          rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]; exact h.2
        rw [Set.indicator_of_mem hz]
        exact u_G_norm_le hε h.1
      · rw [if_neg h, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => mul_nonneg (s82t_sigma_nonneg _
          (by unfold criticalS; positivity)) (Real.rpow_nonneg hε.le _)) z
  have hpt : (fun z => if ε < ‖x - z‖ then convInt Gf rho x z else 0) =
      fun z => (if ε < ‖x - z‖ then rho z • Gf (x - z) else 0) -
        rho x • (if ε < ‖x - z‖ ∧ ‖x - z‖ ≤ 1 / 4 then Gf (x - z) else 0) := by
    funext z
    unfold convInt
    by_cases h1 : ε < ‖x - z‖
    · by_cases h2 : ‖x - z‖ ≤ 1 / 4
      · simp only [if_pos h1, if_pos h2, if_pos (And.intro h1 h2), sub_smul]
      · simp only [if_pos h1, if_neg h2, if_neg (fun h : ε < ‖x - z‖ ∧ ‖x - z‖ ≤ 1 / 4 => h2 h.2),
          smul_zero, sub_zero]
    · simp only [if_neg h1, if_neg (fun h : ε < ‖x - z‖ ∧ ‖x - z‖ ≤ 1 / 4 => h1 h.1), smul_zero, sub_zero]
  have hsm : Integrable (fun z : Euc d => rho x • (if ε < ‖x - z‖ ∧ ‖x - z‖ ≤ 1 / 4 then Gf (x - z) else 0)) :=
    hann.smul (rho x)
  unfold uFe
  rw [hpt, integral_sub (u_trunc_integrable hε hF.prob x) hsm, integral_smul,
    u_annulus_zero hε.le x]
  simp

lemma u_Fe_bdd {d : ℕ} (hd : 2 ≤ d) {rho : Euc d → ℝ} {Λ : ℝ} (hF : UForce d rho Λ) :
    ∃ K1 : ℝ, ∀ ε : ℝ, 0 < ε → ∀ x, ‖uFe ε rho x‖ ≤ K1 := by
  obtain ⟨hint, K1, hK1⟩ := u_conv_unif hd hF
  refine ⟨K1, fun ε hε x => ?_⟩
  rw [u_Fe_eq hε hF x]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    (hint x).norm (Eventually.of_forall fun z => ?_)) (hK1 x)
  by_cases h : ε < ‖x - z‖ <;> simp [h]

lemma u_Fe_tendsto {d : ℕ} (hd : 2 ≤ d) {rho : Euc d → ℝ} {Λ : ℝ} (hF : UForce d rho Λ) (x : Euc d) :
    Tendsto (fun ε => uFe ε rho x) (𝓝[>] 0) (𝓝 (forceMean rho x)) := by
  obtain ⟨hint, -⟩ := u_conv_unif hd hF
  have : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hG := HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)
  have hsub : Measurable (fun y : Euc d => x - y) := measurable_const.sub measurable_id
  have hmeas : ∀ ε : ℝ, AEStronglyMeasurable (fun z => if ε < ‖x - z‖ then
      convInt (rieszKernelGrad d (criticalS d)) rho x z else 0) volume := by
    intro ε
    refine Measurable.aestronglyMeasurable (Measurable.ite (measurableSet_lt measurable_const
      (measurable_norm.comp hsub)) ?_ measurable_const)
    unfold convInt
    refine Measurable.ite (measurableSet_le (measurable_norm.comp hsub) measurable_const) ?_ ?_
    · exact (hF.prob.measurable.sub measurable_const).smul (hG.comp hsub)
    · exact hF.prob.measurable.smul (hG.comp hsub)
  have hlim : Tendsto (fun ε : ℝ => ∫ z, (if ε < ‖x - z‖ then
      convInt (rieszKernelGrad d (criticalS d)) rho x z else 0)) (𝓝[>] 0)
      (𝓝 (∫ z, convInt (rieszKernelGrad d (criticalS d)) rho x z)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖convInt (rieszKernelGrad d (criticalS d)) rho x z‖)
      (Eventually.of_forall hmeas) ?_ (hint x).norm ?_
    · refine Eventually.of_forall fun ε => Eventually.of_forall fun z => ?_
      by_cases h : ε < ‖x - z‖ <;> simp [h]
    · have hae : ∀ᵐ z ∂(volume : Measure (Euc d)), z ≠ x :=
        compl_mem_ae_iff.mpr (measure_singleton x)
      filter_upwards [hae] with z hz
      have hzpos : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hz.symm)
      have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ‖x - z‖ :=
        (eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hzpos))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [this] with ε hε
      simp [hε]
  refine hlim.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with ε hε
  exact (u_Fe_eq hε.1 hF x).symm

end HRS.MS.S82U
