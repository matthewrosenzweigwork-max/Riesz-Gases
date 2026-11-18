import HRS.MH.DualityRdC1a

/-!
# DualityRd packet C1b: the self-pairing identity (Lemma 3.1 (5),(6)) on `ℝ^d`

Port of `HRS.interactionPairing_withDensity_self` / `integral_nonlocalTerm_eq_neg`
(`HRS/Stochastic/Duality.lean:197`, `:1470`) and of the antisymmetry `MeanFieldPairing.antisym`
(`HRS/PDE/MeanFieldPairing.lean:130`).  No truncation is needed: the cancellation kernel
`(x,z) ↦ f(x) κ(z) (h(x-z) - 1_{|z|≤1/4} h(x))` is absolutely integrable on `ℝ^d × ℝ^d`
(majorant `HRS.MP.RdGen.rgMaj`), so Fubini applies, and the antisymmetry follows from the oddness of `κ`
and the substitutions `x ↦ x + z`, `z ↦ -z`.  Then `(5)` is `B = (X - N)/2` (C1a (2)) and `(6)` is `N = -X`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.DualityRd

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem dc1b_movtr_measurable {u : Euc d → ℝ} (hu : Continuous u) :
    Measurable (fun p : Euc d × Euc d => movtr_R u p.1 p.2) := by
  unfold movtr_R
  have h2 : Measurable (fun p : Euc d × Euc d => u (p.1 - p.2)) :=
    hu.measurable.comp (measurable_fst.sub measurable_snd)
  have h3 : Measurable (fun p : Euc d × Euc d => u p.1) := hu.measurable.comp measurable_fst
  exact Measurable.ite (measurableSet_le (measurable_norm.comp measurable_snd) measurable_const)
    (h2.sub h3) h2

theorem dc1b_rgMaj_nonneg {s σ b0 b1 : ℝ} (hσ : 0 ≤ σ) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (x z : Euc d) :
    0 ≤ HRS.MP.RdGen.rgMaj d s σ b0 b1 x z := by
  unfold HRS.MP.RdGen.rgMaj
  refine mul_nonneg hσ (add_nonneg (Set.indicator_nonneg
    (fun z _ => mul_nonneg hb1 (Real.rpow_nonneg (norm_nonneg _) _)) z) ?_)
  exact mul_nonneg (mul_nonneg (by positivity) hb0) (Real.rpow_nonneg (by positivity) _)

theorem dc1b_mul_bdd_int {ρ G : Euc d → ℝ} (hρint : Integrable ρ) (hρnn : ∀ x, 0 ≤ ρ x)
    (hρm : Measurable ρ) (hG : Measurable G) {B : ℝ} (hB : ∀ x, ‖G x‖ ≤ B) :
    Integrable (fun x => ρ x * G x) := by
  refine Integrable.mono' (hρint.mul_const B) (hρm.mul hG).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Real.norm_of_nonneg (hρnn x)]
  exact mul_le_mul_of_nonneg_left (hB x) (hρnn x)

/-- Joint integrability of the cancellation kernel `(x,z) ↦ f(x) κ(z) (g(x-z) - 1_{|z|≤1/4} g(x))`. -/
theorem dc1b_joint_int {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ} {σ : ℝ}
    (hκ : HRS.MP.RdGen.RgKer d s σ κ) {f g : Euc d → ℝ} {cf cg : ℝ} (hcf : 0 ≤ cf) (hcg : 0 ≤ cg)
    (hf : HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 cf f)
    (hg : HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 cg g) :
    Integrable (fun p : Euc d × Euc d => f p.1 * (κ p.2 * movtr_R g p.1 p.2)) (volume.prod volume) := by
  obtain ⟨hgd, hgc, hg0, hg1, -⟩ := dc1a_rgW_facts hcg hg
  obtain ⟨-, hfc, hf0, -, -⟩ := dc1a_rgW_facts hcf hf
  have hσ : 0 ≤ σ := hκ.sigma_nonneg
  have hκm : Measurable κ := hκ.meas
  have hmeas : Measurable (fun p : Euc d × Euc d => f p.1 * (κ p.2 * movtr_R g p.1 p.2)) :=
    (hfc.measurable.comp measurable_fst).mul ((hκm.comp measurable_snd).mul (dc1b_movtr_measurable hgc))
  have hfint : Integrable f :=
    Integrable.mono' ((HRS.MP.RdGen.rg_W_integrable hd).const_mul cf) hfc.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        have := hf0 y
        exact this)
  have hmaj : Measurable (fun p : Euc d × Euc d => HRS.MP.RdGen.rgMaj d s σ cg cg p.1 p.2) := by
    unfold HRS.MP.RdGen.rgMaj
    have hind : Measurable (fun p : Euc d × Euc d => Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
        (fun z : Euc d => cg * ‖z‖ ^ (-s)) p.2) :=
      (Measurable.indicator (measurable_const.mul (measurable_norm.pow_const _))
        Metric.isClosed_closedBall.measurableSet).comp measurable_snd
    have hpow : Measurable (fun p : Euc d × Euc d => (1 + ‖p.1 - p.2‖) ^ (-((d : ℝ) + 1))) :=
      (measurable_const.add (measurable_norm.comp (measurable_fst.sub measurable_snd))).pow_const _
    exact measurable_const.mul (hind.add (measurable_const.mul hpow))
  set G : Euc d × Euc d → ℝ := fun p => |f p.1| * HRS.MP.RdGen.rgMaj d s σ cg cg p.1 p.2 with hG
  have hGm : Measurable G :=
    ((continuous_abs.measurable).comp (hfc.measurable.comp measurable_fst)).mul hmaj
  have hGint : Integrable G (volume.prod volume) := by
    rw [integrable_prod_iff hGm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
    · exact (HRS.MP.RdGen.rg_maj_integrable hd hsd σ cg cg x).const_mul |f x|
    · have e : ∀ x, ∫ y, ‖G (x, y)‖ = |f x| * (σ * (cg * HRS.MP.RdGen.rgNear d s
          + 4 ^ (s + 1) * cg * HRS.MP.RdGen.rgW d)) := by
        intro x
        rw [← HRS.MP.RdGen.rg_integral_maj hd hsd σ cg cg x, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [hG]
        rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _)
          (dc1b_rgMaj_nonneg hσ hcg hcg x y))]
      refine (hfint.abs.mul_const (σ * (cg * HRS.MP.RdGen.rgNear d s
          + 4 ^ (s + 1) * cg * HRS.MP.RdGen.rgW d))).congr (Filter.Eventually.of_forall fun x => ?_)
      exact (e x).symm
  refine Integrable.mono' hGint hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  by_cases hz : p.2 = 0
  · have h0 : ‖f p.1 * (κ p.2 * movtr_R g p.1 p.2)‖ = 0 := by
      simp [movtr_R, hz]
    rw [h0]
    exact mul_nonneg (abs_nonneg _) (dc1b_rgMaj_nonneg hσ hcg hcg _ _)
  · have hnorm := HRS.MP.RdGen.rg_norm_le hs0 hκ hgd hcg hcg hg0 hg1 p.1 p.2 hz
    have e1 : ‖f p.1 * (κ p.2 * movtr_R g p.1 p.2)‖ =
        |f p.1| * ‖κ p.2 • HRS.MP.RdGen.rgR g p.1 p.2‖ := by
      rw [HRS.MP.RdGen.rg_movtr_R_eq, smul_eq_mul]
      simp only [norm_mul, Real.norm_eq_abs]
    rw [e1]
    exact mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)

/-- The Fubini step and the substitution `y = x - z` in the cancellation integral. -/
theorem dc1b_core {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ} {σ : ℝ}
    (hκ : HRS.MP.RdGen.RgKer d s σ κ) {f g : Euc d → ℝ} {cf cg : ℝ} (hcf : 0 ≤ cf) (hcg : 0 ≤ cg)
    (hf : HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 cf f)
    (hg : HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 cg g) :
    ∫ x, f x * ∫ z, κ z * movtr_R g x z =
      ∫ z, κ z * ((∫ x, f x * g (x - z)) - (if ‖z‖ ≤ 1 / 4 then (1 : ℝ) else 0) * (∫ x, f x * g x)) := by
  have hJ := dc1b_joint_int hd hs0 hsd hκ hcf hcg hf hg
  obtain ⟨-, hfc, hf0, -, -⟩ := dc1a_rgW_facts hcf hf
  obtain ⟨-, hgc, hg0, -, -⟩ := dc1a_rgW_facts hcg hg
  have hfint : Integrable f :=
    Integrable.mono' ((HRS.MP.RdGen.rg_W_integrable hd).const_mul cf) hfc.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hf0 y)
  have hfg : ∀ z : Euc d, Integrable (fun x => f x * g (x - z)) := fun z => by
    refine Integrable.mono' (hfint.norm.mul_const cg)
      (hfc.measurable.mul (hgc.measurable.comp (measurable_id.sub_const z))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (dc1a_rgW_facts hcg hg |>.2.2.2.2 _) (norm_nonneg _)
  have hfg0 : Integrable (fun x => f x * g x) := by simpa using hfg 0
  calc ∫ x, f x * ∫ z, κ z * movtr_R g x z
      = ∫ x, ∫ z, f x * (κ z * movtr_R g x z) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (integral_const_mul _ _).symm)
    _ = ∫ z, ∫ x, f x * (κ z * movtr_R g x z) := integral_integral_swap hJ
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        have hpt : ∀ x, f x * (κ z * movtr_R g x z) =
            κ z * (f x * g (x - z)) - (κ z * (if ‖z‖ ≤ 1 / 4 then (1 : ℝ) else 0)) * (f x * g x) := by
          intro x
          unfold movtr_R
          split_ifs <;> ring
        simp_rw [hpt]
        rw [integral_sub ((hfg z).const_mul _) (hfg0.const_mul _), integral_const_mul, integral_const_mul]
        ring

/-- Antisymmetry of the cancellation convolution with an odd kernel. -/
theorem dc1b_antisym {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ} {σ : ℝ}
    (hκ : HRS.MP.RdGen.RgKer d s σ κ) (hodd : ∀ z : Euc d, κ (-z) = -κ z)
    {f g : Euc d → ℝ} {cf cg : ℝ} (hcf : 0 ≤ cf) (hcg : 0 ≤ cg)
    (hf : HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 cf f)
    (hg : HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 cg g) :
    ∫ x, f x * ∫ z, κ z * movtr_R g x z = -∫ x, g x * ∫ z, κ z * movtr_R f x z := by
  have h1 := dc1b_core hd hs0 hsd hκ hcf hcg hf hg
  have h2 := dc1b_core hd hs0 hsd hκ hcg hcf hg hf
  rw [h1, h2]
  have hc : ∫ x, g x * f x = ∫ x, f x * g x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [hc]
  have hΦ : ∀ z : Euc d, ∫ x, f x * g (x - z) = ∫ x, g x * f (x - -z) := by
    intro z
    have hs : ∫ x, f (x + z) * g (x + z - z) = ∫ x, f x * g (x - z) :=
      integral_add_right_eq_self (μ := volume) (fun x => f x * g (x - z)) z
    rw [← hs]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [add_sub_cancel_right, sub_neg_eq_add]
    ring
  have hL : ∫ z, κ z * ((∫ x, f x * g (x - z)) - (if ‖z‖ ≤ 1 / 4 then (1 : ℝ) else 0) * (∫ x, f x * g x))
      = ∫ z, κ z * ((∫ x, g x * f (x - -z)) - (if ‖z‖ ≤ 1 / 4 then (1 : ℝ) else 0) * (∫ x, f x * g x)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [hΦ z])
  have hneg : ∫ z : Euc d, κ (-z) * ((∫ x, g x * f (x - -z)) - (if ‖-z‖ ≤ 1 / 4 then (1 : ℝ) else 0) * (∫ x, f x * g x))
      = ∫ z : Euc d, κ z * ((∫ x, g x * f (x - z)) - (if ‖z‖ ≤ 1 / 4 then (1 : ℝ) else 0) * (∫ x, f x * g x)) :=
    integral_neg_eq_self (μ := volume)
      (fun z : Euc d => κ z * ((∫ x, g x * f (x - z)) - (if ‖z‖ ≤ 1 / 4 then (1 : ℝ) else 0) * (∫ x, f x * g x)))
  have hpt : ∀ z : Euc d,
      κ (-z) * ((∫ x, g x * f (x - -z)) - (if ‖-z‖ ≤ 1 / 4 then (1 : ℝ) else 0) * (∫ x, f x * g x))
        = -(κ z * ((∫ x, g x * f (x - -z)) - (if ‖z‖ ≤ 1 / 4 then (1 : ℝ) else 0) * (∫ x, f x * g x))) := by
    intro z
    rw [hodd z, norm_neg]
    ring
  simp_rw [hpt] at hneg
  rw [integral_neg] at hneg
  rw [hL]
  linarith


theorem dc1b_int_mul_bdd {g G : Euc d → ℝ} (hg : Integrable g) (hGm : Measurable G) {B : ℝ}
    (hB : ∀ x, ‖G x‖ ≤ B) : Integrable (fun x => g x * G x) := by
  refine Integrable.mono' (hg.norm.mul_const B) (hg.aestronglyMeasurable.mul hGm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)

theorem dc1b_rgW_int (hd : 1 ≤ d) {u : Euc d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hu : HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 c u) : Integrable u := by
  obtain ⟨-, hcont, h0, -, -⟩ := dc1a_rgW_facts hc hu
  exact Integrable.mono' ((HRS.MP.RdGen.rg_W_integrable hd).const_mul c) hcont.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => h0 y)

theorem dc1b_conv_meas {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {u : Euc d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hu : HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 c u) (j : Fin d) :
    Measurable (fun x => (convGradConvW (rieszKernelGrad d s) u x) j) := by
  have e : (fun x => (convGradConvW (rieszKernelGrad d s) u x) j) =
      fun x => ∫ z, rieszKernelGrad d s z j * movtr_R u x z :=
    funext fun x => dc1a_force_eq hd hs0 hsd hc hu x j
  rw [e]
  exact (dc1a_meas_int (HRS.MP.RdGen.rgKerComp_ok hs0 j).meas (dc1a_rgW_facts hc hu).2.1).measurable

theorem self_pairing_rd_proof (D : WholeDyn d) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) {ρ : Euc d → ℝ}
    (hρ : RegSliceRd ρ) {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) :
    interactionPairingW D ψ (Whole.withDensityReal ρ) (Whole.withDensityReal ρ)
      = ∫ x, ρ x * inner ℝ (gradient ψ x)
          (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x)) ∧
    ∫ x, ρ x * nlTermRd D ρ ψ x
      = -∫ x, ρ x * inner ℝ (gradient ψ x)
          (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x)) := by
  obtain ⟨-, hA2, hA3, hA4⟩ := pairing_expansion_rd_proof D hd hs0 hsd hρ hψ
  obtain ⟨Cρ, hCρ0, hρW⟩ := dc1a_rho_rgW hd hρ
  have hP : Whole.IsProbDensity ρ := by unfold RegSliceRd at hρ; exact hρ.1
  have hρm : Measurable ρ := hP.measurable
  have hρnn : ∀ y, 0 ≤ ρ y := hP.nonneg
  have hρint : Integrable ρ := dc1b_rgW_int hd hCρ0 hρW
  choose cv hcv0 hvW using fun j : Fin d => dc1a_v_rgW hψ D.M j
  have hc2 : ∀ j : Fin d, 0 ≤ 2 ^ 1 * Cρ * cv j :=
    fun j => mul_nonneg (mul_nonneg (by norm_num) hCρ0) (hcv0 j)
  have hhW : ∀ j : Fin d, HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1
      (2 ^ 1 * Cρ * cv j) (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) :=
    fun j => dc1a_mul_rgW hCρ0 (hcv0 j) hρW (hvW j)
  have hκ : ∀ j : Fin d, HRS.MP.RdGen.RgKer d D.s (movtr_sigma D.s)
      (fun z => rieszKernelGrad d D.s z j) := fun j => HRS.MP.RdGen.rgKerComp_ok hs0 j
  have hκodd : ∀ j : Fin d, ∀ z : Euc d, rieszKernelGrad d D.s (-z) j = -(rieszKernelGrad d D.s z j) := by
    intro j z
    rw [HRS.Whole.Q09B.q09b_rkg_neg]
    simp
  choose Bc hBc0 hBc using fun j : Fin d => dc1a_force_bound' hd hs0 hsd hCρ0 hρW j
  choose Bh hBh0 hBh using fun j : Fin d => dc1a_force_bound' hd hs0 hsd (hc2 j) (hhW j) j
  -- the antisymmetry: each component of the `g`-force pairs with that of `ρ`
  have hstep : ∀ j : Fin d,
      ∫ x, ρ x * (convGradConvW (rieszKernelGrad d D.s)
          (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x) j
        = -∫ x, (ρ x * (Torus.matVec D.M.transpose (gradient ψ x)) j)
            * (convGradConvW (rieszKernelGrad d D.s) ρ x) j := by
    intro j
    have e1 : ∫ x, ρ x * (convGradConvW (rieszKernelGrad d D.s)
          (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x) j
        = ∫ x, ρ x * ∫ z, rieszKernelGrad d D.s z j *
            movtr_R (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x z :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [dc1a_force_eq hd hs0 hsd (hc2 j) (hhW j) x j])
    rw [e1, dc1b_antisym hd hs0 hsd (hκ j) (hκodd j) hCρ0 (hc2 j) hρW (hhW j)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [dc1a_force_eq hd hs0 hsd hCρ0 hρW x j]
  have hint_nl : ∀ j : Fin d, Integrable (fun x => ρ x * (convGradConvW (rieszKernelGrad d D.s)
          (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x) j) :=
    fun j => dc1b_mul_bdd_int hρint hρnn hρm
      (dc1b_conv_meas hd hs0 hsd (hc2 j) (hhW j) j) (hBh j)
  have hint_X : ∀ j : Fin d, Integrable (fun x => (ρ x * (Torus.matVec D.M.transpose (gradient ψ x)) j)
      * (convGradConvW (rieszKernelGrad d D.s) ρ x) j) :=
    fun j => dc1b_int_mul_bdd (dc1b_rgW_int hd (hc2 j) (hhW j))
      (dc1b_conv_meas hd hs0 hsd hCρ0 hρW j) (hBc j)
  have hsumX : ∑ j : Fin d, ∫ x, (ρ x * (Torus.matVec D.M.transpose (gradient ψ x)) j)
        * (convGradConvW (rieszKernelGrad d D.s) ρ x) j
      = ∫ x, ρ x * inner ℝ (gradient ψ x)
          (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x)) := by
    rw [← integral_finsetSum _ (fun j _ => hint_X j)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [dc1a_inner_matVec_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- (6) the nonlocal term is the negative of the pairing
  have hN1 : ∫ x, ρ x * nlTermRd D ρ ψ x = ∑ j : Fin d, ∫ x, ρ x * (convGradConvW (rieszKernelGrad d D.s)
          (fun y => ρ y * (Torus.matVec D.M.transpose (gradient ψ y)) j) x) j := by
    rw [← integral_finsetSum _ (fun j _ => hint_nl j)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    simp only [nlTermRd, Finset.mul_sum]
  have hN : ∫ x, ρ x * nlTermRd D ρ ψ x = -∫ x, ρ x * inner ℝ (gradient ψ x)
      (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x)) := by
    rw [hN1]
    simp only [hstep, Finset.sum_neg_distrib, neg_inj]
    exact hsumX
  -- (5) the self-pairing is `½ (X - N)`
  have hB : interactionPairingW D ψ (Whole.withDensityReal ρ) (Whole.withDensityReal ρ)
      = (1 / 2 : ℝ) * ((∫ x, ρ x * inner ℝ (gradient ψ x)
          (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x)))
        - ∫ x, ρ x * nlTermRd D ρ ψ x) := by
    have hc : ∫ x, (∫ y, (if x = y then (0 : ℝ) else
          inner ℝ (gradient ψ x - gradient ψ y) (Torus.matVec D.M (rieszKernelGrad d D.s (x - y))))
            ∂(Whole.withDensityReal ρ)) ∂(Whole.withDensityReal ρ)
        = ∫ x, (inner ℝ (gradient ψ x)
            (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x)) - nlTermRd D ρ ψ x)
            ∂(Whole.withDensityReal ρ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => hA2 x)
    unfold interactionPairingW
    rw [hc, dc1a_integral_withDensity hρm hρnn
      (fun x => inner ℝ (gradient ψ x) (Torus.matVec D.M (convGradConvW (rieszKernelGrad d D.s) ρ x))
        - nlTermRd D ρ ψ x)]
    congr 1
    simp only [mul_sub]
    exact integral_sub hA3 hA4
  refine ⟨?_, hN⟩
  rw [hB, hN]
  ring

end HRS.MH.DualityRd
