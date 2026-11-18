/-
# HRS.Equilibrium.Q84bAuxJ — packet Q84b: the canonical row is differentiable under the integral
-/
import HRS.Equilibrium.Q84bAuxI

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84b

variable {d : ℕ} {s : ℝ}

/-- `|ψ(x,y)| ≤ 2K(1 + r^{1-s})`. -/
theorem q84b_size_le (hs1 : 1 ≤ s) {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hPs : PsiSize s K ψ)
    {x y : Torus d} (hxy : x ≠ y) :
    |ψ x y| ≤ 2 * K * (1 + rTrunc x y ^ (1 - s)) := by
  have hK : 0 ≤ K := Q84a.q84a_K_nonneg hPs hxy
  have hr := PairCorrAux.rTrunc_pos hxy
  have hr1 := PairCorrAux.rTrunc_le_one x y
  have h := hPs.size x y hxy
  have hA : rTrunc x y ^ (2 - s) ≤ rTrunc x y ^ (1 - s) := by
    refine Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have hB : (if s = 2 then |Real.log (rTrunc x y)| else 0) ≤ rTrunc x y ^ (1 - s) := by
    split_ifs with h2
    · have h3 : |Real.log (rTrunc x y)| = Real.log (1 / rTrunc x y) := by
        rw [one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos hr.le hr1)]
      rw [h3]
      have h4 := Real.log_le_sub_one_of_pos (one_div_pos.2 hr)
      have h5 : rTrunc x y ^ (1 - s) = 1 / rTrunc x y := by
        rw [h2, show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one, one_div]
      rw [h5]; linarith
    · exact Real.rpow_nonneg hr.le _
  have hpos : 0 ≤ rTrunc x y ^ (1 - s) := Real.rpow_nonneg hr.le _
  calc |ψ x y| ≤ K * (1 + rTrunc x y ^ (2 - s) +
        if s = 2 then |Real.log (rTrunc x y)| else 0) := h
    _ ≤ K * (1 + rTrunc x y ^ (1 - s) + rTrunc x y ^ (1 - s)) :=
        mul_le_mul_of_nonneg_left (by linarith) hK
    _ ≤ 2 * K * (1 + rTrunc x y ^ (1 - s)) := by nlinarith

theorem q84b_ball_w_le (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (p : Torus d) {R : ℝ}
    (hR0 : 0 < R) (hR1 : R ≤ 1) :
    ∫ z, {z : Torus d | Torus.eucDist p z < R}.indicator (fun z => wEnv s p z) z ≤
      PairCorrAux.cdR d * ((1 / d + 1 / s) * R ^ s) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have h := PairCorrAux.radial_B1' hd hcrit p R hR0 hR1
  have hnn : 0 ≤ᵐ[volume] fun z : Torus d => {z : Torus d | Torus.eucDist p z < R}.indicator
      (fun z => wEnv s p z) z := Eventually.of_forall fun z => by
    simp only [Pi.zero_apply]
    refine Set.indicator_nonneg (fun z _ => ?_) z
    have := PairCorrAux.one_le_wEnv s p z; linarith
  have hmeas : AEStronglyMeasurable (fun z : Torus d => {z : Torus d | Torus.eucDist p z < R}.indicator
      (fun z => wEnv s p z) z) volume :=
    ((PairCorrAux.measurable_wEnv s p).indicator
      (measurableSet_lt (PairCorrAux.measurable_eucDist' p) measurable_const)).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
  have hpt : ∀ z : Torus d, ENNReal.ofReal ({z : Torus d | Torus.eucDist p z < R}.indicator
      (fun z => wEnv s p z) z) = {z : Torus d | Torus.eucDist p z < R}.indicator
      (fun z => ENNReal.ofReal (wEnv s p z)) z := by
    intro z
    by_cases hz : z ∈ {z : Torus d | Torus.eucDist p z < R}
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz]
  simp_rw [hpt]
  have hc := PairCorrAux.cdR_nonneg d
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h


/-- Mean value inequality for `ψ` itself (first order analogue of `q84a_grad_diff`). -/
theorem q84b_fun_diff {ψ : Torus d → Torus d → ℝ} {K : ℝ} (hψ : PsiSize s K ψ) (hs1 : 1 ≤ s)
    {a b c : Torus d} (hac : a ≠ c) (h : Torus.eucDist a b ≤ Torus.eucDist a c / 2) :
    |ψ a c - ψ b c| ≤ K * (1 + 2 ^ s * rTrunc a c ^ (-s)) * Torus.eucDist a b := by
  have hs : 0 < s := by linarith
  obtain ⟨w, hw, hwn⟩ := Q84a.q84a_exists_lift_dist a b
  have hmA : Torus.mk (Torus.rep a) = a := Torus.mk_rep a
  have hmC : Torus.mk (Torus.rep c) = c := Torus.mk_rep c
  set A : Euc d := Torus.rep a with hA
  set C : Euc d := Torus.rep c with hC
  set B : Euc d := A - w with hB
  have hmB : Torus.mk B = b := by
    rw [hB, Q84a.q84a_mk_sub, hmA, hw]; abel
  have hEpos : 0 < Torus.eucDist a c := by
    rcases (PairCorrAux.eucDist_nonneg' a c).lt_or_eq with h0 | h0
    · exact h0
    · exact absurd ((PairCorrAux.eucDist_eq_zero' a c).1 h0.symm) hac
  set E := Torus.eucDist a c with hE
  have hK : 0 ≤ K := Q84a.q84a_K_nonneg hψ hac
  set S : Set (Euc d × Euc d) := segment ℝ A B ×ˢ ({C} : Set (Euc d)) with hS
  have hSconv : Convex ℝ S := (convex_segment A B).prod (convex_singleton C)
  have hmem : ∀ p ∈ S, E / 2 ≤ Torus.eucDist (Torus.mk p.1) (Torus.mk p.2) := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hv' : v = C := hv
    show E / 2 ≤ Torus.eucDist (Torus.mk u) (Torus.mk v)
    rw [hv', hmC]
    have h1 := Q84a.q84a_seg_norm hu
    have h2 : B - A = -w := by rw [hB]; abel
    rw [h2, norm_neg, hwn] at h1
    have h3 : Torus.eucDist a (Torus.mk u) ≤ ‖u - A‖ := by
      have := Q84a.q84a_eucDist_mk_le A u
      rw [hmA, norm_sub_rev] at this
      exact this
    have h4 := PairCorrAux.eucDist_triangle a (Torus.mk u) c
    linarith
  have hoff : ∀ p ∈ S, p ∈ offDiag d := by
    intro p hp
    show Torus.mk p.1 ≠ Torus.mk p.2
    intro hEq
    have := hmem p hp
    have h0 : Torus.eucDist (Torus.mk p.1) (Torus.mk p.2) = 0 := by
      rw [hEq]; exact PairCorrAux.eucDist_self' _
    linarith
  have hxS : (A, C) ∈ S := ⟨left_mem_segment ℝ A B, rfl⟩
  have hyS : (B, C) ∈ S := ⟨right_mem_segment ℝ A B, rfl⟩
  have hf : ∀ p ∈ S, DifferentiableAt ℝ (lift2 ψ) p := by
    intro p hp
    exact (hψ.smooth.contDiffAt (Q84a.q84a_isOpen_offDiag.mem_nhds (hoff p hp))).differentiableAt
      (by simp)
  have hR : 0 < rTrunc a c := PairCorrAux.rTrunc_pos hac
  have hR1 := PairCorrAux.rTrunc_le_one a c
  have hbound : ∀ p ∈ S, ‖fderiv ℝ (lift2 ψ) p‖ ≤ K * (1 + 2 ^ s * rTrunc a c ^ (-s)) := by
    intro p hp
    refine (hψ.grad p (hoff p hp)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hK
    have hlow : rTrunc a c / 2 ≤ rTrunc (Torus.mk p.1) (Torus.mk p.2) := by
      unfold rTrunc
      refine le_min ?_ ?_
      · have := PairCorrAux.rTrunc_le_one a c
        unfold rTrunc at this
        linarith
      · have := PairCorrAux.rTrunc_le_dist a c
        unfold rTrunc at this
        have hm := hmem p hp
        linarith
    have hrpow : rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s) ≤ (rTrunc a c / 2) ^ (1 - s) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hlow (by linarith)
    have hval : (rTrunc a c / 2) ^ (1 - s) ≤ 2 ^ s * rTrunc a c ^ (-s) := by
      have e : (rTrunc a c / 2) ^ (1 - s) = rTrunc a c ^ (1 - s) * 2 ^ s / 2 := by
        rw [Real.div_rpow hR.le (by norm_num), Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
          Real.rpow_one]
        field_simp
      rw [e, Q84a.q84a_rpow_split hR s]
      have h2 : (0 : ℝ) < 2 ^ s := Real.rpow_pos_of_pos (by norm_num) s
      have h3 : 0 ≤ rTrunc a c ^ (-s) := Real.rpow_nonneg hR.le _
      have h4 : rTrunc a c * rTrunc a c ^ (-s) ≤ rTrunc a c ^ (-s) :=
        mul_le_of_le_one_left h3 hR1
      nlinarith [mul_le_mul_of_nonneg_right h4 h2.le]
    linarith
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (f := lift2 ψ) hf hbound hSconv hxS hyS
  have hnorm : ‖((B, C) : Euc d × Euc d) - (A, C)‖ = Torus.eucDist a b := by
    rw [Prod.mk_sub_mk, sub_self, Prod.norm_def]
    have h2 : B - A = -w := by rw [hB]; abel
    simp [h2, hwn, PairCorrAux.eucDist_nonneg' a b]
  rw [hnorm] at hmv
  have e1 : lift2 ψ (A, C) = ψ a c := by simp [lift2, hmA, hmC]
  have e2 : lift2 ψ (B, C) = ψ b c := by simp [lift2, hmB, hmC]
  rw [e1, e2] at hmv
  rw [abs_sub_comm]
  exact (Real.norm_eq_abs _ ▸ hmv)


theorem q84b_near_psi (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {K : ℝ} {ψ : Torus d → Torus d → ℝ}
    (hPs : PsiSize s K ψ) (p : Torus d) {R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1) :
    ∫ z, {z : Torus d | Torus.eucDist p z < R}.indicator (fun z => |ψ p z|) z ≤
      4 * |K| * R * (PairCorrAux.cdR d * ((1 / d + 1 / s) * R ^ s)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have hd0 : 0 < d := by omega
  set B : Set (Torus d) := {z : Torus d | Torus.eucDist p z < R} with hB
  have hBm : MeasurableSet B := measurableSet_lt (PairCorrAux.measurable_eucDist' p) measurable_const
  have hwi := q84b_w_integrable hd hcrit p
  have hgi : Integrable (B.indicator (fun z => 4 * |K| * R * wEnv s p z)) :=
    (hwi.const_mul (4 * |K| * R)).indicator hBm
  have hle : ∫ z, B.indicator (fun z => |ψ p z|) z ≤
      ∫ z, B.indicator (fun z => 4 * |K| * R * wEnv s p z) z := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun z => ?_) hgi ?_
    · simp only [Pi.zero_apply]
      exact Set.indicator_nonneg (fun z _ => abs_nonneg _) z
    · filter_upwards [q84b_ae_ne hd0 p] with z hz
      by_cases hzB : z ∈ B
      · rw [Set.indicator_of_mem hzB, Set.indicator_of_mem hzB]
        have hzp : p ≠ z := fun h => hz h.symm
        have h1 := q84b_size_le hs1 hPs hzp
        have hr := PairCorrAux.rTrunc_pos hzp
        have hr1 := PairCorrAux.rTrunc_le_one p z
        have hrR : rTrunc p z ≤ R := by
          have := PairCorrAux.rTrunc_le_dist p z
          have hz' : Torus.eucDist p z < R := hzB
          linarith
        have hRs : R ^ s ≤ R := by
          calc R ^ s ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hR0 hR1 hs1
            _ = R := Real.rpow_one R
        have hX : 0 ≤ rTrunc p z ^ (-s) := Real.rpow_nonneg hr.le _
        have hone : 1 ≤ R ^ s * rTrunc p z ^ (-s) := by
          have : R ^ (-s) ≤ rTrunc p z ^ (-s) := Real.rpow_le_rpow_of_nonpos hr hrR (by linarith)
          have h2 : R ^ s * R ^ (-s) = 1 := by
            rw [← Real.rpow_add hR0]; simp
          calc (1 : ℝ) = R ^ s * R ^ (-s) := h2.symm
            _ ≤ R ^ s * rTrunc p z ^ (-s) :=
              mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hR0.le _)
        have hu : 1 + rTrunc p z ^ (1 - s) ≤ 2 * R * rTrunc p z ^ (-s) := by
          rw [Q84a.q84a_rpow_split hr]
          have : rTrunc p z * rTrunc p z ^ (-s) ≤ R * rTrunc p z ^ (-s) :=
            mul_le_mul_of_nonneg_right hrR hX
          nlinarith [mul_le_mul_of_nonneg_right hRs hX]
        have hw : rTrunc p z ^ (-s) ≤ wEnv s p z := by unfold wEnv; linarith
        have hK : K ≤ |K| := le_abs_self K
        have hK0 : 0 ≤ |K| := abs_nonneg K
        have hRw : 0 ≤ R * rTrunc p z ^ (-s) := mul_nonneg hR0.le hX
        calc |ψ p z| ≤ 2 * K * (1 + rTrunc p z ^ (1 - s)) := h1
          _ ≤ 2 * |K| * (1 + rTrunc p z ^ (1 - s)) := by
            have : 0 ≤ 1 + rTrunc p z ^ (1 - s) := by
              have := Real.rpow_nonneg hr.le (1 - s); linarith
            nlinarith
          _ ≤ 2 * |K| * (2 * R * rTrunc p z ^ (-s)) :=
            mul_le_mul_of_nonneg_left hu (by positivity)
          _ ≤ 4 * |K| * R * wEnv s p z := by
            have := mul_le_mul_of_nonneg_left hw (mul_nonneg hK0 hR0.le)
            nlinarith
      · rw [Set.indicator_of_notMem hzB, Set.indicator_of_notMem hzB]
  refine hle.trans ?_
  rw [show (fun z => B.indicator (fun z => 4 * |K| * R * wEnv s p z) z) =
      fun z => (4 * |K| * R) * B.indicator (fun z => wEnv s p z) z from by
    funext z; by_cases hz : z ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (q84b_ball_w_le hd hcrit p hR0 hR1) (by positivity)


theorem q84b_slope_tendsto {ψ : Torus d → Torus d → ℝ} {K : ℝ} (hPs : PsiSize s K ψ)
    {x z : Torus d} (hxz : x ≠ z) (v : Euc d) :
    Tendsto (fun t : ℝ => t⁻¹ * (ψ (Torus.mk (Torus.rep x + t • v)) z - ψ x z)) (𝓝[≠] 0)
      (𝓝 (inner ℝ v (gradFst ψ x z))) := by
  have hp : ((Torus.rep x, Torus.rep z) : Euc d × Euc d) ∈ offDiag d := by
    show Torus.mk (Torus.rep x) ≠ Torus.mk (Torus.rep z)
    rw [Torus.mk_rep, Torus.mk_rep]; exact hxz
  have hd : DifferentiableAt ℝ (lift2 ψ) (Torus.rep x, Torus.rep z) :=
    (hPs.smooth.contDiffAt (Q84a.q84a_isOpen_offDiag.mem_nhds hp)).differentiableAt (by simp)
  have h1 : HasDerivAt (fun t : ℝ => Torus.rep x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (Torus.rep x)
  have hγ : HasDerivAt (fun t : ℝ => ((Torus.rep x + t • v, Torus.rep z) : Euc d × Euc d))
      (v, (0 : Euc d)) 0 := h1.prodMk (hasDerivAt_const 0 (Torus.rep z))
  have hd' : HasFDerivAt (lift2 ψ) (fderiv ℝ (lift2 ψ) (Torus.rep x, Torus.rep z))
      ((Torus.rep x + (0 : ℝ) • v, Torus.rep z)) := by
    simpa using hd.hasFDerivAt
  have hcomp := hd'.comp_hasDerivAt (0 : ℝ) hγ
  have hslope := (hasDerivAt_iff_tendsto_slope_zero.1 hcomp)
  have hval : fderiv ℝ (lift2 ψ) (Torus.rep x, Torus.rep z) (v, 0) = inner ℝ v (gradFst ψ x z) := by
    have e := Q84a.q84a_gradFst_eq hPs.smooth hp
    rw [Torus.mk_rep, Torus.mk_rep] at e
    rw [e, real_inner_comm, InnerProductSpace.toDual_symm_apply]
    simp
  rw [hval] at hslope
  refine hslope.congr fun t => ?_
  simp only [Function.comp, smul_eq_mul, zero_add, lift2]
  simp [Torus.mk_rep]

end HRS.Q84b
