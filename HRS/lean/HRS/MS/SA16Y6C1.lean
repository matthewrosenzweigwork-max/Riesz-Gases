import HRS.MS.SA16Y5Rm1
import HRS.MS.SA16Y5Lc1
import HRS.MS.SA16Y6Tc2
import HRS.MS.SA16Y6Tc7

/-!
# S.A.16 (SA16Y6) C1: the critical-case (`s = d-1`) replacements of the `L^1`/HLS inputs of the order-one chain

* `sa16y6c_D0` (replaces `sa16y5_D0`, Dc1): `‖∂_i(ρ ⋆ (aψ))‖_p ≤ K‖ψ‖_p` for `a` bounded, by the Calderón-Zygmund bound for `R_i`.
* `sa16y6c_lamComm_bound` (replaces `sa16y5_lamComm_bound`, Lc1, `θ < 1`): the commutator `[Λ^1, μ]` is bounded on `L^p`
  (`lp_Lambda_commutator_low_cb2` at `θ = 1` with `ElemTruncBound` from `elemTruncBound_lin`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q HRS.MS.ToriCoefA

section C1
variable {d : ℕ}

lemma sa16y6c_fderiv_conv_R (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) {f : Euc d → ℝ} (hf : IsCcInfty f)
    (i : Fin d) (x : Euc d) :
    fderiv ℝ (convFun (rieszKernel d s) f) x (sa16z_e i) = -(HRS.CZ.Hls.hlsg_c s) * sa16y6_R d i f x := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hsd : s < d := by rw [hs]; linarith
  have hc := HRS.CZ.Hls.hlsg_c_pos hs0
  have e : convFun (rieszKernel d s) f = sa16r_cv (rieszKernel d s) f := by
    funext y; rw [sa16sp_convFun_eq]; rfl
  rw [e, sa16y5_cv_fderiv (rieszKernel_locallyIntegrable hs0 hsd) hf x _, sa16y6_R_eq hd hs hf i x]
  field_simp

theorem sa16y6c_D0 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s = (d : ℝ) - 1) {p : ℝ} (hp : 2 ≤ p)
    (hfar : (d : ℝ) < p * (s + 1)) {W : ℝ} (hW : 0 ≤ W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {a : Euc d → ℝ}, ContDiff ℝ ∞ a → sa16y5_Dec 1 W a →
      ∀ {ψ : Euc d → ℝ}, IsCcInfty ψ → ∀ i : Fin d,
        eLpNorm (fun x => fderiv ℝ (convFun (rieszKernel d s) (fun y => a y * ψ y)) x (sa16z_e i))
          (ENNReal.ofReal p) volume ≤ ENNReal.ofReal K * eLpNorm ψ (ENNReal.ofReal p) volume := by
  choose CR hCR0 hCR using fun i : Fin d => sa16y6_R_Lp hd hp i
  set CRm : ℝ := ∑ i, CR i with hCRm
  have hCRm0 : 0 ≤ CRm := Finset.sum_nonneg fun i _ => hCR0 i
  have hCRle : ∀ i, CR i ≤ CRm := fun i => Finset.single_le_sum (f := CR) (fun i _ => hCR0 i) (Finset.mem_univ i)
  have hcs : 0 ≤ HRS.CZ.Hls.hlsg_c s := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    exact (HRS.CZ.Hls.hlsg_c_pos hs0).le
  refine ⟨HRS.CZ.Hls.hlsg_c s * (CRm * W), mul_nonneg hcs (mul_nonneg hCRm0 hW), fun {a} ha hdec {ψ} hψ i => ?_⟩
  have hΞ : IsCcInfty (fun y => a y * ψ y) := ⟨ha.mul hψ.1, hψ.2.mul_left⟩
  have hab : ∀ y, |a y| ≤ W := by
    intro y
    have h := hdec 0 (by omega) y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    refine h.trans ?_
    have h1 : (1 + ‖y‖) ^ (-((d + 3 : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (neg_nonpos.2 (Nat.cast_nonneg _))
    nlinarith
  have hfun : (fun x => fderiv ℝ (convFun (rieszKernel d s) (fun y => a y * ψ y)) x (sa16z_e i)) =
      (-(HRS.CZ.Hls.hlsg_c s)) • sa16y6_R d i (fun y => a y * ψ y) := by
    funext x
    rw [sa16y6c_fderiv_conv_R hd hs1 hΞ i x]
    simp
  rw [hfun, eLpNorm_const_smul]
  have hn : ‖(-(HRS.CZ.Hls.hlsg_c s))‖ₑ = ENNReal.ofReal (HRS.CZ.Hls.hlsg_c s) := by
    rw [Real.enorm_eq_ofReal_abs, abs_neg, abs_of_nonneg hcs]
  rw [hn]
  have h1 := hCR i _ hΞ
  have h2 : eLpNorm (fun y => a y * ψ y) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal W * eLpNorm ψ (ENNReal.ofReal p) volume := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hΞ.1.continuous.aestronglyMeasurable) (Eventually.of_forall fun y => ?_) _
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hab y) (abs_nonneg _)
  calc ENNReal.ofReal (HRS.CZ.Hls.hlsg_c s) * eLpNorm (sa16y6_R d i fun y => a y * ψ y) (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (HRS.CZ.Hls.hlsg_c s) * (ENNReal.ofReal CRm * (ENNReal.ofReal W *
          eLpNorm ψ (ENNReal.ofReal p) volume)) :=
        mul_le_mul' le_rfl (h1.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hCRle i)) h2))
    _ = ENNReal.ofReal (HRS.CZ.Hls.hlsg_c s * (CRm * W)) * eLpNorm ψ (ENNReal.ofReal p) volume := by
        rw [ENNReal.ofReal_mul hcs, ENNReal.ofReal_mul hCRm0]
        ring

theorem sa16y6c_lamComm_bound (hd : 1 ≤ d) {p : ℝ} (hp : 2 ≤ p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {μ : Euc d → ℝ} {Λ : ℝ}, 0 ≤ Λ → ContDiff ℝ ∞ μ → sa16z_Cb 2 Λ μ →
      ∀ {w : Euc d → ℝ}, IsCcInfty w →
      eLpNorm (fun x => lamComm d 1 μ w x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (K * Λ) * eLpNorm w (ENNReal.ofReal p) volume := by
  obtain ⟨CR, -, hCR⟩ := HRS.CZ.PvAsm.elemTruncBound_lin hd (show 1 < p by linarith)
  obtain ⟨C, hC⟩ := HRS.CZ.ElemA.lp_Lambda_commutator_low_cb2 hd 1 p one_pos le_rfl hp (fun _ => ⟨CR, hCR⟩)
  refine ⟨max C 0 * 3, by positivity, fun {μ Λ} hΛ hμs hCb {w} hw => ?_⟩
  have hmem : HRS.MemCb 2 μ := sa16z_memCb hμs hCb
  have hcb := sa16z_cbNorm_le hCb
  set W : 𝓢(Euc d, ℝ) := sa16z_schw hw with hW
  have hWc : ⇑W = w := rfl
  have h := hC μ hmem W
  rw [hWc] at h
  refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have hcb0 : 0 ≤ HRS.cbNorm 2 μ := Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun z => norm_nonneg _
  have hcb3 : HRS.cbNorm 2 μ ≤ 3 * Λ := by
    have : (((2 : ℕ) : ℝ) + 1) = 3 := by norm_num
    rw [this] at hcb; exact hcb
  have h1 : C * HRS.cbNorm 2 μ ≤ max C 0 * HRS.cbNorm 2 μ := mul_le_mul_of_nonneg_right (le_max_left C 0) hcb0
  have h2 : max C 0 * HRS.cbNorm 2 μ ≤ max C 0 * (3 * Λ) := mul_le_mul_of_nonneg_left hcb3 (le_max_right C 0)
  linarith

end C1

end HRS.Whole.AppendixA.Phase2SA16R
