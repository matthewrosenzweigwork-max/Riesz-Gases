import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.Mov63Aux3
import HRS.MS.UniqC2c
import HRS.MS.S67NlBD14
import HRS.MS.S67NlBD26

/-!
# S6.7nl.48: joint order-zero continuity of the force and of the `J` source
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Route: both sources are `convGradConvW (rieszKernelGrad d s)` of a family `g_r` on `[0,T]`.  A family with
uniform decay `(1+|y|)^{-(d+1)}`, uniform Lipschitz bound and weak continuity in `r` has jointly
continuous convolution (`UniqC2.c2_joint`, `c2_rgT_cont`).  The families are `√ρ₀ v_r` (force) and
`ρ_r ∂_j f_r` (J); the uniform bounds come from `mn_force_bound` (Σ^m embedding) and the
Schwartz decay of `√ρ₀`, the pointwise time continuity of `v_r(y)` from the sup-norm bound
applied to `v_r - v_{r'}` together with the continuity of `r ↦ OscSpace.ofFun v_r`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

lemma s67bd48_rpow_le_one (y : Euc d) : (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

/-- joint continuity of the convolution from uniform decay / Lipschitz bounds and weak continuity -/
lemma s67bd48_conv_cont (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {T : ℝ}
    {g : ℝ → Euc d → ℝ} {b0 b1 : ℝ} (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hdiff : ∀ r ∈ Icc (0 : ℝ) T, Differentiable ℝ (g r))
    (h0 : ∀ r ∈ Icc (0 : ℝ) T, ∀ y, ‖g r y‖ ≤ b0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
    (h1 : ∀ r ∈ Icc (0 : ℝ) T, ∀ y, ‖fderiv ℝ (g r) y‖ ≤ b1)
    (hweak : ∀ ψ : Euc d → ℝ, Continuous ψ → HasCompactSupport ψ →
      ContinuousOn (fun r => ∫ x, ψ x * g r x) (Icc (0 : ℝ) T)) :
    ContinuousOn (fun p : ℝ × Euc d => convGradConvW (rieszKernelGrad d s) (g p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := by
  have hjoint := HRS.MS.UniqC2.c2_joint hb1 hweak hdiff h1
  apply HRS.MS.UniqC2.c2_vec_contOn
  intro i
  have hcomp := HRS.MS.UniqC2.c2_rgT_cont hd hs0 hsd
    (HRS.MP.RdGen.rgKerComp_ok (d := d) hs0 i) hb0 hb1 hdiff h0 h1 hjoint
  refine hcomp.congr fun p hp => ?_
  exact HRS.MP.RdGen.rg_force_comp hd hs0 hsd (hdiff p.1 hp.1) hb0 hb1 (h0 p.1 hp.1)
    (h1 p.1 hp.1) p.2 i

/-- weak continuity from pointwise continuity in `r` and a uniform bound -/
lemma s67bd48_weak {T : ℝ} {g : ℝ → Euc d → ℝ} {B : ℝ}
    (hgc : ∀ r ∈ Icc (0 : ℝ) T, Continuous (g r)) (hgb : ∀ r ∈ Icc (0 : ℝ) T, ∀ y, ‖g r y‖ ≤ B)
    (hgp : ∀ y, ContinuousOn (fun r => g r y) (Icc (0 : ℝ) T)) :
    ∀ ψ : Euc d → ℝ, Continuous ψ → HasCompactSupport ψ →
      ContinuousOn (fun r => ∫ x, ψ x * g r x) (Icc (0 : ℝ) T) := by
  intro ψ hψ hk
  have hI : Integrable (fun x => ‖ψ x‖ * B) volume :=
    (hψ.integrable_of_hasCompactSupport hk).norm.mul_const B
  refine continuousOn_of_dominated (bound := fun x => ‖ψ x‖ * B)
    (fun r hr => (hψ.mul (hgc r hr)).aestronglyMeasurable)
    (fun r hr => Filter.Eventually.of_forall fun x => ?_) hI
    (Filter.Eventually.of_forall fun x => continuousOn_const.mul (hgp x))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hgb r hr x) (norm_nonneg _)

lemma s67bd48_fderiv_mul_le {a b : Euc d → ℝ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    {Ma Mb Na Nb : ℝ} {y : Euc d} (hMa : |a y| ≤ Ma) (hMb : |b y| ≤ Mb)
    (hNa : ‖fderiv ℝ a y‖ ≤ Na) (hNb : ‖fderiv ℝ b y‖ ≤ Nb) :
    ‖fderiv ℝ (fun z => a z * b z) y‖ ≤ Ma * Nb + Mb * Na := by
  rw [fderiv_fun_mul (ha y) (hb y)]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hMa0 : 0 ≤ Ma := (abs_nonneg _).trans hMa
  have hMb0 : 0 ≤ Mb := (abs_nonneg _).trans hMb
  exact add_le_add (mul_le_mul hMa hNb (norm_nonneg _) hMa0) (mul_le_mul hMb hNa (norm_nonneg _) hMb0)

lemma s67bd48_fderiv_add_le {a b : Euc d → ℝ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    {Na Nb : ℝ} {y : Euc d} (hNa : ‖fderiv ℝ a y‖ ≤ Na) (hNb : ‖fderiv ℝ b y‖ ≤ Nb) :
    ‖fderiv ℝ (fun z => a z + b z) y‖ ≤ Na + Nb := by
  rw [fderiv_fun_add (ha y) (hb y)]
  exact (norm_add_le _ _).trans (add_le_add hNa hNb)

/-- sup bounds for a directional derivative of a `C²` function with bounded jets -/
lemma s67bd48_D_bounds {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) (i : Fin d) {B1 B2 : ℝ}
    (hB1 : ∀ y, ‖iteratedFDeriv ℝ 1 u y‖ ≤ B1) (hB2 : ∀ y, ‖iteratedFDeriv ℝ 2 u y‖ ≤ B2) :
    ContDiff ℝ 1 (s67bd_D i u) ∧ (∀ y, |s67bd_D i u y| ≤ B1) ∧
      ∀ y, ‖fderiv ℝ (s67bd_D i u) y‖ ≤ B2 := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (m := 1) (by norm_num)
  have hD1 : ContDiff ℝ 1 (s67bd_D i u) := by
    unfold s67bd_D
    exact hf1.clm_apply contDiff_const
  have he : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
  refine ⟨hD1, fun y => ?_, fun y => ?_⟩
  · have h1 := (fderiv ℝ u y).le_opNorm (EuclideanSpace.single i (1 : ℝ))
    rw [he, mul_one, ← norm_iteratedFDeriv_one] at h1
    unfold s67bd_D
    rw [← Real.norm_eq_abs]
    exact h1.trans (hB1 y)
  · have hc : HasFDerivAt (s67bd_D i u)
        ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)).comp
          (fderiv ℝ (fderiv ℝ u) y)) y :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)).hasFDerivAt.comp y
        ((hf1.differentiable one_ne_zero) y).hasFDerivAt
    rw [hc.fderiv]
    have hnorm : ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ B2 := by
      have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := u) (x := y) (n := 1)
      rw [norm_iteratedFDeriv_one] at this
      rw [this]
      exact hB2 y
    have hB20 : 0 ≤ B2 := (norm_nonneg (fderiv ℝ (fderiv ℝ u) y)).trans hnorm
    refine ContinuousLinearMap.opNorm_le_bound _ hB20 fun h => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    calc ‖(fderiv ℝ (fderiv ℝ u) y) h (EuclideanSpace.single i (1 : ℝ))‖
        ≤ ‖(fderiv ℝ (fderiv ℝ u) y) h‖ * ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ u) y‖ * ‖h‖) * 1 := by
          rw [he]
          exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) zero_le_one
      _ ≤ B2 * ‖h‖ := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

/-- time continuity of the directional derivative of the classical adjoint -/
lemma s67bd48_D_pt {C : WholeCoeff d} {T : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C T φ f) (j : Fin d) (y : Euc d) :
    ContinuousOn (fun t => s67bd_D j (f t) y) (Icc (0 : ℝ) T) := by
  have hc := hf.cont_c2 1 (by norm_num)
  have hmap : Continuous (fun t : Icc (0 : ℝ) T => ((t, y) : Icc (0 : ℝ) T × Euc d)) :=
    continuous_id.prodMk continuous_const
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) ℝ
    (fun _ => (EuclideanSpace.single j (1 : ℝ) : Euc d))).continuous.comp (hc.comp hmap)
  rw [continuousOn_iff_continuous_domRestrict]
  refine h2.congr fun t => ?_
  simp [s67bd_D, Set.domRestrict]

/-- Schwartz decay of `√ρ₀` and a bound on its derivative -/
lemma s67bd48_sqrt_bounds (H : Mov2dTh d s β q ρ₀) :
    ∃ S0 S1 : ℝ, 0 ≤ S0 ∧ 0 ≤ S1 ∧
      (∀ y, Real.sqrt (ρ₀ y) ≤ S0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) ∧
      (∀ y, ‖fderiv ℝ (fun x => Real.sqrt (ρ₀ x)) y‖ ≤ S1) := by
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  refine ⟨|2 ^ (d + 1) * (Finset.Iic ((d + 1, 1) : ℕ × ℕ)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψs|,
    |2 ^ (d + 1) * (Finset.Iic ((d + 1, 1) : ℕ × ℕ)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψs|, abs_nonneg _, abs_nonneg _, fun y => ?_,
    fun y => ?_⟩
  · have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((d + 1, 1) : ℕ × ℕ))
      (k := d + 1) (n := 0) le_rfl (by norm_num) ψs y
    rw [norm_iteratedFDeriv_zero] at h
    have hs : Real.sqrt (ρ₀ y) = ‖ψs y‖ := by
      rw [Real.norm_eq_abs, congrFun hψs y, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hP : 0 < (1 + ‖y‖) ^ (d + 1) := by positivity
    rw [Real.rpow_neg (by positivity), show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hP, hs]
    have := le_abs_self (2 ^ (d + 1) * (Finset.Iic ((d + 1, 1) : ℕ × ℕ)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψs)
    nlinarith [h]
  · have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((d + 1, 1) : ℕ × ℕ))
      (k := 0) (n := 1) (Nat.zero_le _) le_rfl ψs y
    rw [norm_iteratedFDeriv_one, pow_zero, one_mul] at h
    rw [← hψs]
    exact h.trans (le_abs_self _)

/-- `ρ_t = ρ₀ + √ρ₀ v_t` -/
lemma s67bd48_rho_eq (H : Mov2dTh d s β q ρ₀) (ρ : ℝ → Euc d → ℝ) (t : ℝ) (y : Euc d) :
    ρ t y = ρ₀ y + Real.sqrt (ρ₀ y) * movV ρ₀ ρ t y := by
  obtain ⟨-, hρpos⟩ := mov2d_rho_data H
  have : Real.sqrt (ρ₀ y) ≠ 0 := (Real.sqrt_pos.2 (hρpos y)).ne'
  simp only [movV]
  field_simp
  ring

/-- uniform `C¹` data and pointwise time continuity of `v_t` -/
lemma s67bd48_vdata (H : Mov2dTh d s β q ρ₀) (m : ℕ) (hm : (d : ℝ) / 2 + 7 < m) (R0 c0 : ℝ)
    (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hρ : MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ) (T : ℝ) :
    ∃ Mv : ℝ, 0 ≤ Mv ∧
      (∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 1 (movV ρ₀ ρ t) ∧ (∀ y, |movV ρ₀ ρ t y| ≤ Mv) ∧
        ∀ y, ‖fderiv ℝ (movV ρ₀ ρ t) y‖ ≤ Mv) ∧
      ∀ y, ContinuousOn (fun t => movV ρ₀ ρ t y) (Icc (0 : ℝ) T) := by
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  have hsqc : Continuous (fun x => Real.sqrt (ρ₀ x)) := by
    rw [← hψs]; exact ψs.continuous
  obtain ⟨C, hC0, hC⟩ := mn_force_bound H.hd H.hs0 H.hsd β q H.hβ H.hq ρ₀ H.hρ 0 m
    (by push_cast; linarith)
  have hvc : ∀ t ∈ Icc (0 : ℝ) T, Continuous (movV ρ₀ ρ t) := by
    intro t ht
    show Continuous (fun x => (ρ t x - ρ₀ x) / Real.sqrt (ρ₀ x))
    exact ((hρ.regular t ht.1).sub hρsm.continuous).div hsqc
      (fun x => (Real.sqrt_pos.2 (hρpos x)).ne')
  set Mo : ℝ := |R0| * Real.exp (|c0| * T) with hMo
  have hosc : ∀ t ∈ Icc (0 : ℝ) T, oscNorm (m : ℝ) (movV ρ₀ ρ t) ≤ Mo := by
    intro t ht
    refine (hρ.weighted t ht.1).2.trans ?_
    calc R0 * Real.exp (-c0 * t) ≤ |R0| * Real.exp (-c0 * t) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      _ ≤ |R0| * Real.exp (|c0| * T) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply Real.exp_le_exp.2
          calc -c0 * t ≤ |c0| * t := mul_le_mul_of_nonneg_right (neg_le_abs c0) ht.1
            _ ≤ |c0| * T := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _)
  have hMo0 : 0 ≤ Mo := by positivity
  refine ⟨C * Mo, by positivity, fun t ht => ?_, ?_⟩
  · obtain ⟨hc2, hb, -⟩ := hC (movV ρ₀ ρ t) (hvc t ht) (hρ.weighted t ht.1).1
    refine ⟨hc2.of_le (by norm_num), fun y => ?_, fun y => ?_⟩
    · have := hb 0 (by norm_num) y
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      exact this.trans (mul_le_mul_of_nonneg_left (hosc t ht) hC0)
    · have := hb 1 (by norm_num) y
      rw [norm_iteratedFDeriv_one] at this
      exact this.trans (mul_le_mul_of_nonneg_left (hosc t ht) hC0)
  · intro y
    have hcont : ContinuousOn (fun t => OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ t))
        (Icc (0 : ℝ) T) := hρ.cont.mono Icc_subset_Ici_self
    intro t0 ht0
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 (hcont t0 ht0) (ε / (C + 1))
      (by positivity)
    refine ⟨δ, hδ, fun t ht hdist => ?_⟩
    have hdd := hδ' ht hdist
    have hmt := (hρ.weighted t ht.1).1
    have hm0 := (hρ.weighted t0 ht0.1).1
    have hw := mov2d_memOsc_sub hmt hm0
    have hwc : Continuous (fun z => movV ρ₀ ρ t z - movV ρ₀ ρ t0 z) :=
      (hvc t ht).sub (hvc t0 ht0)
    obtain ⟨-, hb, -⟩ := hC _ hwc hw
    have h0 := hb 0 (by norm_num) y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h0
    have hn : oscNorm (m : ℝ) (fun z => movV ρ₀ ρ t z - movV ρ₀ ρ t0 z) =
        dist (OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ t))
          (OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ t0)) := by
      rw [dist_eq_norm, ← mov2d_ofFun_sub hmt hm0, OscSpace.norm_ofFun _ hw]
    rw [hn] at h0
    rw [Real.dist_eq]
    have hd0 := dist_nonneg (x := OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ t))
      (y := OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ t0))
    have hCpos : 0 < C + 1 := by linarith
    calc |movV ρ₀ ρ t y - movV ρ₀ ρ t0 y|
        ≤ C * dist (OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ t))
          (OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ t0)) := h0
      _ ≤ (C + 1) * dist (OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ t))
          (OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ t0)) := by nlinarith
      _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left hdd hCpos
      _ = ε := by field_simp

lemma s67bd48_force_cont (H : Mov2dTh d s β q ρ₀)
    (m : ℕ) (hm : (d : ℝ) / 2 + 7 < m) (R0 c0 : ℝ)
    (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hρ : MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ) (T : ℝ) :
    ContinuousOn (fun p : ℝ × Euc d => s67bd_F d s ρ₀ (movV ρ₀ ρ p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := by
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  have hsqsm : ContDiff ℝ ∞ (fun x => Real.sqrt (ρ₀ x)) := by
    rw [← hψs]; exact ψs.smooth _
  have hda : Differentiable ℝ (fun x => Real.sqrt (ρ₀ x)) := hsqsm.differentiable (by simp)
  obtain ⟨Mv, hMv0, hv, hvpt⟩ := s67bd48_vdata H m hm R0 c0 f0 ρ hρ T
  obtain ⟨S0, S1, hS0, hS1, hsd0, hsd1⟩ := s67bd48_sqrt_bounds H
  have hsq1 : ∀ y, |Real.sqrt (ρ₀ y)| ≤ S0 := fun y => by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (ρ₀ y) ≤ S0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := hsd0 y
      _ ≤ S0 * 1 := mul_le_mul_of_nonneg_left (s67bd48_rpow_le_one y) hS0
      _ = S0 := mul_one _
  have hdiff : ∀ t ∈ Icc (0 : ℝ) T,
      Differentiable ℝ (fun y => Real.sqrt (ρ₀ y) * movV ρ₀ ρ t y) := fun t ht =>
    hda.mul ((hv t ht).1.differentiable one_ne_zero)
  have h0 : ∀ t ∈ Icc (0 : ℝ) T, ∀ y, ‖Real.sqrt (ρ₀ y) * movV ρ₀ ρ t y‖ ≤
      (S0 * Mv) * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
    intro t ht y
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (ρ₀ y) * |movV ρ₀ ρ t y|
        ≤ (S0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) * Mv :=
          mul_le_mul (hsd0 y) ((hv t ht).2.1 y) (abs_nonneg _) (by positivity)
      _ = (S0 * Mv) * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by ring
  have h1 : ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
      ‖fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * movV ρ₀ ρ t y) y‖ ≤ S0 * Mv + Mv * S1 := by
    intro t ht y
    exact s67bd48_fderiv_mul_le hda ((hv t ht).1.differentiable one_ne_zero) (hsq1 y)
      ((hv t ht).2.1 y) (hsd1 y) ((hv t ht).2.2 y)
  have hbnd : ∀ t ∈ Icc (0 : ℝ) T, ∀ y, ‖Real.sqrt (ρ₀ y) * movV ρ₀ ρ t y‖ ≤ S0 * Mv := by
    intro t ht y
    calc _ ≤ (S0 * Mv) * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := h0 t ht y
      _ ≤ (S0 * Mv) * 1 :=
          mul_le_mul_of_nonneg_left (s67bd48_rpow_le_one y) (mul_nonneg hS0 hMv0)
      _ = S0 * Mv := mul_one _
  have hweak := s67bd48_weak (T := T) (g := fun t y => Real.sqrt (ρ₀ y) * movV ρ₀ ρ t y)
    (B := S0 * Mv) (fun t ht => hsqsm.continuous.mul (hv t ht).1.continuous) hbnd
    (fun y => continuousOn_const.mul (hvpt y))
  exact s67bd48_conv_cont (g := fun t y => Real.sqrt (ρ₀ y) * movV ρ₀ ρ t y) (by have := H.hd; omega)
    H.hs0 H.hsd (mul_nonneg hS0 hMv0) (add_nonneg (mul_nonneg hS0 hMv0) (mul_nonneg hMv0 hS1))
    hdiff h0 h1 hweak

lemma s67bd48_J_cont (H : Mov2dTh d s β q ρ₀)
    (m : ℕ) (hm : (d : ℝ) / 2 + 7 < m) (R0 c0 : ℝ)
    (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hρ : MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ)
    (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (hT : 0 ≤ T)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f) :
    ContinuousOn (fun p : ℝ × Euc d => s67J d s (ρ p.1) (f p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := by
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  have hsqsm : ContDiff ℝ ∞ (fun x => Real.sqrt (ρ₀ x)) := by
    rw [← hψs]; exact ψs.smooth _
  have hda : Differentiable ℝ (fun x => Real.sqrt (ρ₀ x)) := hsqsm.differentiable (by simp)
  obtain ⟨Mv, hMv0, hv, hvpt⟩ := s67bd48_vdata H m hm R0 c0 f0 ρ hρ T
  obtain ⟨S0, S1, hS0, hS1, hsd0, hsd1⟩ := s67bd48_sqrt_bounds H
  obtain ⟨B1, hB1⟩ := hf.bdd 1 (by norm_num)
  obtain ⟨B2, hB2⟩ := hf.bdd 2 (le_refl 2)
  have hsq1 : ∀ y, |Real.sqrt (ρ₀ y)| ≤ S0 := fun y => by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (ρ₀ y) ≤ S0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := hsd0 y
      _ ≤ S0 * 1 := mul_le_mul_of_nonneg_left (s67bd48_rpow_le_one y) hS0
      _ = S0 := mul_one _
  -- the derivative data
  have hDd : ∀ t ∈ Icc (0 : ℝ) T, ∀ j : Fin d, ContDiff ℝ 1 (s67bd_D j (f t)) ∧
      (∀ y, |s67bd_D j (f t) y| ≤ B1) ∧ ∀ y, ‖fderiv ℝ (s67bd_D j (f t)) y‖ ≤ B2 :=
    fun t ht j => s67bd48_D_bounds (hf.c2 t ht) j (fun y => hB1 t ht y) (fun y => hB2 t ht y)
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0 ⟨le_rfl, hT⟩ 0)
  obtain ⟨-, hρpos⟩ := mov2d_rho_data H
  set MP : ℝ := S0 * (S0 + Mv) with hMP
  set NP : ℝ := S0 * (S1 + Mv) + (S0 + Mv) * S1 with hNP
  have hMP0 : 0 ≤ MP := by positivity
  have hsv : ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
      |Real.sqrt (ρ₀ y) + movV ρ₀ ρ t y| ≤ S0 + Mv := fun t ht y =>
    (abs_add_le _ _).trans (add_le_add (hsq1 y) ((hv t ht).2.1 y))
  have hPb : ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
      ‖Real.sqrt (ρ₀ y) * (Real.sqrt (ρ₀ y) + movV ρ₀ ρ t y)‖ ≤
        MP * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
    intro t ht y
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (ρ₀ y) * |Real.sqrt (ρ₀ y) + movV ρ₀ ρ t y|
        ≤ (S0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) * (S0 + Mv) :=
          mul_le_mul (hsd0 y) (hsv t ht y) (abs_nonneg _) (by positivity)
      _ = MP * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by rw [hMP]; ring
  have hPb1 : ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
      |Real.sqrt (ρ₀ y) * (Real.sqrt (ρ₀ y) + movV ρ₀ ρ t y)| ≤ MP := by
    intro t ht y
    have := hPb t ht y
    rw [Real.norm_eq_abs] at this
    exact this.trans (by
      calc MP * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ MP * 1 :=
            mul_le_mul_of_nonneg_left (s67bd48_rpow_le_one y) hMP0
        _ = MP := mul_one _)
  have hvd : ∀ t ∈ Icc (0 : ℝ) T, Differentiable ℝ (movV ρ₀ ρ t) := fun t ht =>
    (hv t ht).1.differentiable one_ne_zero
  have hPdiff : ∀ t ∈ Icc (0 : ℝ) T,
      Differentiable ℝ (fun y => Real.sqrt (ρ₀ y) * (Real.sqrt (ρ₀ y) + movV ρ₀ ρ t y)) :=
    fun t ht => hda.mul (hda.add (hvd t ht))
  have hPN : ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
      ‖fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * (Real.sqrt (ρ₀ y) + movV ρ₀ ρ t y)) y‖ ≤ NP := by
    intro t ht y
    have hadd := s67bd48_fderiv_add_le (a := fun x => Real.sqrt (ρ₀ x)) (b := movV ρ₀ ρ t)
      hda (hvd t ht) (hsd1 y) ((hv t ht).2.2 y)
    exact s67bd48_fderiv_mul_le (a := fun x => Real.sqrt (ρ₀ x))
      (b := fun x => Real.sqrt (ρ₀ x) + movV ρ₀ ρ t x) hda (hda.add (hvd t ht))
      (hsq1 y) (hsv t ht y) (hsd1 y) hadd
  have hrho' : ∀ (j : Fin d) (t : ℝ) (y : Euc d), ρ t y * gradient (f t) y j =
      (Real.sqrt (ρ₀ y) * (Real.sqrt (ρ₀ y) + movV ρ₀ ρ t y)) * s67bd_D j (f t) y := by
    intro j t y
    have e : ρ₀ y + Real.sqrt (ρ₀ y) * movV ρ₀ ρ t y =
        Real.sqrt (ρ₀ y) * (Real.sqrt (ρ₀ y) + movV ρ₀ ρ t y) := by
      rw [mul_add, Real.mul_self_sqrt (hρpos y).le]
    rw [s67bd48_rho_eq H ρ t y, mov2d_grad_coord, e]
    rfl
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hconv : ∀ j : Fin d, ContinuousOn (fun p : ℝ × Euc d =>
      (convGradConvW (rieszKernelGrad d s) (fun y => ρ p.1 y * gradient (f p.1) y j) p.2) j)
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := by
    intro j
    have hbnd : ∀ t ∈ Icc (0 : ℝ) T, ∀ y,
        ‖(Real.sqrt (ρ₀ y) * (Real.sqrt (ρ₀ y) + movV ρ₀ ρ t y)) * s67bd_D j (f t) y‖ ≤
          MP * B1 := by
      intro t ht y
      rw [norm_mul, Real.norm_eq_abs (s67bd_D j (f t) y)]
      have := hPb1 t ht y
      rw [← Real.norm_eq_abs] at this
      exact mul_le_mul this ((hDd t ht j).2.1 y) (abs_nonneg _) hMP0
    have hweak := s67bd48_weak (T := T)
      (g := fun t y => (Real.sqrt (ρ₀ y) * (Real.sqrt (ρ₀ y) + movV ρ₀ ρ t y)) *
        s67bd_D j (f t) y) (B := MP * B1)
      (fun t ht => ((hPdiff t ht).continuous).mul
        ((hDd t ht j).1.continuous)) hbnd
      (fun y => (continuousOn_const.mul (continuousOn_const.add (hvpt y))).mul
        (s67bd48_D_pt hf j y))
    have hc := s67bd48_conv_cont (g := fun t y =>
        (Real.sqrt (ρ₀ y) * (Real.sqrt (ρ₀ y) + movV ρ₀ ρ t y)) * s67bd_D j (f t) y)
      hd1 H.hs0 H.hsd (b0 := MP * B1) (b1 := MP * B2 + B1 * NP) (mul_nonneg hMP0 hB10)
      (by
        have : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0 ⟨le_rfl, hT⟩ 0)
        have hNP0 : 0 ≤ NP := by positivity
        positivity)
      (fun t ht => (hPdiff t ht).mul ((hDd t ht j).1.differentiable one_ne_zero))
      (fun t ht y => by
        rw [norm_mul, Real.norm_eq_abs (s67bd_D j (f t) y)]
        calc ‖Real.sqrt (ρ₀ y) * (Real.sqrt (ρ₀ y) + movV ρ₀ ρ t y)‖ * |s67bd_D j (f t) y|
            ≤ (MP * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) * B1 :=
              mul_le_mul (hPb t ht y) ((hDd t ht j).2.1 y) (abs_nonneg _) (by positivity)
          _ = (MP * B1) * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by ring)
      (fun t ht y => by
        refine s67bd48_fderiv_mul_le (hPdiff t ht) ((hDd t ht j).1.differentiable one_ne_zero)
          (hPb1 t ht y) ((hDd t ht j).2.1 y) (hPN t ht y) ((hDd t ht j).2.2 y))
      hweak
    have hc' : ContinuousOn (fun p : ℝ × Euc d =>
        convGradConvW (rieszKernelGrad d s) (fun y => ρ p.1 y * gradient (f p.1) y j) p.2)
        (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := by
      refine hc.congr fun p _ => ?_
      rw [show (fun y => ρ p.1 y * gradient (f p.1) y j) = fun y =>
        (Real.sqrt (ρ₀ y) * (Real.sqrt (ρ₀ y) + movV ρ₀ ρ p.1 y)) * s67bd_D j (f p.1) y from
        funext (hrho' j p.1)]
    exact (EuclideanSpace.proj j).continuous.comp_continuousOn hc'
  exact continuousOn_finset_sum _ (fun j _ => hconv j)

theorem s67bd_source_joint_cont (H : Mov2dTh d s β q ρ₀)
    (m : ℕ) (hm : (d : ℝ) / 2 + 7 < m) (R0 c0 : ℝ)
    (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hρ : MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ)
    (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (hT : 0 ≤ T)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f) :
    ContinuousOn (fun p : ℝ × Euc d => s67bd_F d s ρ₀ (movV ρ₀ ρ p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) ∧
    ContinuousOn (fun p : ℝ × Euc d => s67J d s (ρ p.1) (f p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) :=
  ⟨s67bd48_force_cont H m hm R0 c0 f0 ρ hρ T,
    s67bd48_J_cont H m hm R0 c0 f0 ρ hρ T φ f hT hf⟩

end HRS.MS.BreakdownS67
