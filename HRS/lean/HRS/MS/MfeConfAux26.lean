import HRS.MS.MfeConfAux25

/-!
# S.B.1, packet F3 (part 7): the one-body identity and the identity for `ċ`

For a trajectory `H : Sb1Tr3` and a regular admissible kernel `k` (`Sb1KerU`, `Sb1KerR`), at a fixed time `r ∈ [0,T]`, with
`u = u_V^r = mfeTransportW D ρ_r`, `J = ρ u`, `h(x,y) = ∇k(x-y)·(u(x) - u(y))`, `H(x) = ∫ ρ(y) h(x,y) dy`:

* `sb1_Gd_eq`: `Ġ(x) = ∫ A(ρ)(y) k(x-y) dy = ∫ ρ(y) ∇k(x-y)·u(y) dy` (integration by parts, `A = Div J`);
* `sb1_oneBody`: `H(x) = ∇G(x)·u(x) - Ġ(x)`;
* `sb1_cd_eq`: `∫ (A G + ρ Ġ) = -∫ ρ H` (symmetrisation by Fubini).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_vec_expand (v : Euc d) : v = ∑ k, v k • sb1e k := by
  simpa [sb1e] using ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v).symm

theorem sb1_clm_expand (L : Euc d →L[ℝ] ℝ) (v : Euc d) : L v = ∑ k, v k * L (sb1e k) := by
  conv_lhs => rw [sb1_vec_expand v]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

theorem sb1_rhoFu_eq (D : Whole.WholeDyn d) (h : Euc d → ℝ) (L : Euc d →L[ℝ] ℝ) (y : Euc d) :
    h y * L (Whole.mfeTransportW D h y) = ∑ kk, L (sb1e kk) * sb1J D h kk y := by
  rw [sb1_clm_expand L (Whole.mfeTransportW D h y), Finset.mul_sum]
  refine Finset.sum_congr rfl fun kk _ => ?_
  unfold sb1J
  ring

theorem sb1_fderiv_shift {k : Euc d → ℝ} {Lg : ℝ} (hR : Sb1KerR d k Lg) (x y : Euc d) :
    fderiv ℝ (fun y => k (x - y)) y = -(fderiv ℝ k (x - y)) := by
  have h1 : HasFDerivAt (fun y => k (x - y)) ((fderiv ℝ k (x - y)).comp (-ContinuousLinearMap.id ℝ (Euc d))) y :=
    (hR.diff (x - y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
  rw [h1.fderiv]
  ext v
  simp

section Static

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} {k : Euc d → ℝ} {Lg : ℝ}

theorem sb1_conv_phi (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hk : Sb1KerU d s k) {a : ℝ} (ha : 0 ≤ a)
    {φ : Euc d → ℝ} (hφ : Measurable φ) (hb : ∀ y, |φ y| ≤ a * sb1w ((d : ℝ) + 2) y) (x : Euc d) :
    Integrable (fun y => φ y * k (x - y)) ∧
      ∫ y, ‖φ y * k (x - y)‖ ≤ sb1CGd d s a * (1 + ‖x‖) := by
  obtain ⟨hψi, hψ1⟩ := sb1_psiA (d := d) hd (a := a)
  obtain ⟨hI, hIb⟩ := sb1_Om_conv hd hs0 hsd (ψ := fun y => a * sb1w ((d : ℝ) + 2) y)
    (fun y => mul_nonneg ha (sb1w_pos _ _).le) (measurable_const.mul (sb1w_meas _)) hψi
    (Cψ := a) (fun y => mul_le_of_le_one_right ha (sb1w_le_one (by positivity) y)) hψ1 x
  have hle : ∀ᵐ y : Euc d ∂volume, ‖φ y * k (x - y)‖ ≤ a * sb1w ((d : ℝ) + 2) y * sb1Om s (x - y) := by
    filter_upwards [sb1_ae_ne hd x] with y hy
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hb y) (sb1_k_abs_le hs0 hk (sub_ne_zero.2 (Ne.symm hy))) (abs_nonneg _)
      (mul_nonneg ha (sb1w_pos _ _).le)
  have hint : Integrable (fun y => φ y * k (x - y)) :=
    hI.mono' (hφ.mul (hk.meas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable hle
  refine ⟨hint, ?_⟩
  have h := integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg (φ y * k (x - y))) hI hle
  refine h.trans ?_
  have hl := sb1_log_le_norm x
  have hl0 := sb1_log_nonneg x
  have hn := norm_nonneg x
  have h1 : 0 ≤ ∫ y : Euc d, a * sb1w ((d : ℝ) + 2) y :=
    integral_nonneg fun y => mul_nonneg ha (sb1w_pos _ _).le
  have h2 : 0 ≤ ∫ y : Euc d, a * sb1w ((d : ℝ) + 2) y * ‖y‖ :=
    integral_nonneg fun y => mul_nonneg (mul_nonneg ha (sb1w_pos _ _).le) (norm_nonneg _)
  have h3 := sb1Isig_nonneg (d := d) (sb1sig s)
  unfold sb1CGd
  nlinarith [mul_le_mul_of_nonneg_right hl h1, mul_nonneg h3 ha, mul_nonneg h1 hn, mul_nonneg h2 hn,
    mul_nonneg (mul_nonneg h3 ha) hn]

theorem sb1_J_meas (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (kk : Fin d) :
    Continuous (sb1J D (ρ r) kk) :=
  (sb1_J_contDiff H.tr.V H.tr.hd H.tr.hs0 H.tr.hsd (H.tr.slice r hr) (H.pos r hr) kk).continuous

theorem sb1_dJ_cont (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (kk : Fin d) :
    Continuous (fun y => fderiv ℝ (sb1J D (ρ r) kk) y (sb1e kk)) :=
  ((sb1_J_contDiff H.tr.V H.tr.hd H.tr.hs0 H.tr.hsd (H.tr.slice r hr) (H.pos r hr) kk).continuous_fderiv
    (by norm_num)).clm_apply continuous_const

theorem sb1_fkJ_int (H : Sb1Tr3 D T C B C3 ρ) (hR : Sb1KerR d k Lg) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T)
    (kk : Fin d) (x : Euc d) :
    Integrable (fun y => fderiv ℝ k (x - y) (sb1e kk) * sb1J D (ρ r) kk y) := by
  have hw := sb1w_int H.tr.hd (p := (d : ℝ) + 2) (by linarith)
  have hLg := hR.Lg_nonneg
  have hCJ := H.CJ_nonneg
  refine (hw.const_mul (Lg * sb1CJ D B C C3)).mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact (((hR.cont_fderiv.comp (continuous_const.sub continuous_id)).clm_apply continuous_const).mul
      (sb1_J_meas H hr kk)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    have h1 : |fderiv ℝ k (x - y) (sb1e kk)| ≤ Lg := (sb1_apply_single_le _ kk).trans (hR.gbd _)
    have h2 := H.J_bound hr kk y
    calc |fderiv ℝ k (x - y) (sb1e kk)| * |sb1J D (ρ r) kk y| ≤ Lg * (sb1CJ D B C C3 * sb1w ((d : ℝ) + 2) y) :=
          mul_le_mul h1 h2 (abs_nonneg _) hLg
      _ = Lg * sb1CJ D B C C3 * sb1w ((d : ℝ) + 2) y := by ring

theorem sb1_ibp_kernel (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) (kk : Fin d) (x : Euc d) :
    ∫ y, k (x - y) * fderiv ℝ (sb1J D (ρ r) kk) y (sb1e kk) =
      ∫ y, fderiv ℝ k (x - y) (sb1e kk) * sb1J D (ρ r) kk y := by
  have hd := H.tr.hd
  have hJc := sb1_J_contDiff H.tr.V hd H.tr.hs0 H.tr.hsd (H.tr.slice r hr) (H.pos r hr) kk
  have hJd : Differentiable ℝ (sb1J D (ρ r) kk) := hJc.differentiable (by norm_num)
  have hCdJ := H.CdJ_nonneg
  have hCJ := H.CJ_nonneg
  have i1 : Integrable (fun y => k (x - y) * fderiv ℝ (sb1J D (ρ r) kk) y (sb1e kk)) := by
    have := (sb1_conv_phi hd H.tr.hs0 H.tr.hsd hk hCdJ (φ := fun y => fderiv ℝ (sb1J D (ρ r) kk) y (sb1e kk))
      (sb1_dJ_cont H hr kk).measurable (fun y => H.dJ_bound hr kk y) x).1
    simpa [mul_comm] using this
  have i2 : Integrable (fun y => k (x - y) * sb1J D (ρ r) kk y) := by
    have := (sb1_conv_phi hd H.tr.hs0 H.tr.hsd hk hCJ (φ := sb1J D (ρ r) kk)
      (sb1_J_meas H hr kk).measurable (fun y => H.J_bound hr kk y) x).1
    simpa [mul_comm] using this
  have i3 : Integrable (fun y => fderiv ℝ (fun y => k (x - y)) y (sb1e kk) * sb1J D (ρ r) kk y) := by
    have := (sb1_fkJ_int H hR hr kk x).neg
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [sb1_fderiv_shift hR x, ContinuousLinearMap.neg_apply, neg_mul, Pi.neg_apply]
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
    (f := fun y => k (x - y)) (g := sb1J D (ρ r) kk) (v := sb1e kk) i3 i1 i2
    (fun y _ => (hR.diff.comp (differentiable_const x |>.sub differentiable_id)) y) (fun y _ => hJd y)
  rw [key]
  simp only [sb1_fderiv_shift hR x, ContinuousLinearMap.neg_apply, neg_mul, integral_neg, neg_neg]

theorem sb1_rhoFu_int (H : Sb1Tr3 D T C B C3 ρ) (hR : Sb1KerR d k Lg) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T)
    (x : Euc d) : Integrable (fun y => ρ r y * fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) y)) := by
  have e : (fun y => ρ r y * fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) y)) =
      fun y => ∑ kk, fderiv ℝ k (x - y) (sb1e kk) * sb1J D (ρ r) kk y :=
    funext fun y => sb1_rhoFu_eq D (ρ r) (fderiv ℝ k (x - y)) y
  rw [e]
  exact integrable_finset_sum _ fun kk _ => sb1_fkJ_int H hR hr kk x

theorem sb1_Gd_eq (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) (x : Euc d) :
    sb1Gd D ρ k r x = ∫ y, ρ r y * fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) y) := by
  have hd := H.tr.hd
  have hCdJ := H.CdJ_nonneg
  unfold sb1Gd
  have e1 : ∀ y, sb1A D (ρ r) y * k (x - y) =
      ∑ kk, k (x - y) * fderiv ℝ (sb1J D (ρ r) kk) y (sb1e kk) := by
    intro y
    rw [sb1_A_eq_sumJ H.tr.V hd H.tr.hs0 H.tr.hsd (H.tr.slice r hr) (H.pos r hr) y, Finset.sum_mul]
    exact Finset.sum_congr rfl fun kk _ => mul_comm _ _
  have i1 : ∀ kk, Integrable (fun y => k (x - y) * fderiv ℝ (sb1J D (ρ r) kk) y (sb1e kk)) := by
    intro kk
    have := (sb1_conv_phi hd H.tr.hs0 H.tr.hsd hk hCdJ (φ := fun y => fderiv ℝ (sb1J D (ρ r) kk) y (sb1e kk))
      (sb1_dJ_cont H hr kk).measurable (fun y => H.dJ_bound hr kk y) x).1
    simpa [mul_comm] using this
  simp_rw [e1]
  rw [integral_finset_sum _ (fun kk _ => i1 kk)]
  have e2 : ∀ kk, ∫ y, k (x - y) * fderiv ℝ (sb1J D (ρ r) kk) y (sb1e kk) =
      ∫ y, fderiv ℝ k (x - y) (sb1e kk) * sb1J D (ρ r) kk y := fun kk => sb1_ibp_kernel H hk hR hr kk x
  simp_rw [e2]
  rw [← integral_finset_sum _ (fun kk _ => sb1_fkJ_int H hR hr kk x)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  exact (sb1_rhoFu_eq D (ρ r) (fderiv ℝ k (x - y)) y).symm

theorem sb1_oneBody (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) (x : Euc d) :
    sb1PG (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y)) (ρ r) x =
      fderiv ℝ (sb1G k (ρ r)) x (Whole.mfeTransportW D (ρ r) x) - sb1Gd D ρ k r x := by
  have R := H.rho H.tr.hd hr
  unfold sb1PG
  rw [sb1_fderiv_G_apply H.tr.hd H.tr.hs0 H.tr.hsd hk hR R x, sb1_Gd_eq H hk hR hr x]
  have ia : Integrable (fun y => ρ r y * fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x)) := by
    refine (R.integrable.const_mul (Lg * ‖Whole.mfeTransportW D (ρ r) x‖)).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact (R.dens.measurable.mul (((hR.cont_fderiv.comp (continuous_const.sub continuous_id)).clm_apply
        continuous_const).measurable)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (R.dens.nonneg y)]
      have h1 := (fderiv ℝ k (x - y)).le_opNorm (Whole.mfeTransportW D (ρ r) x)
      have h2 : ‖fderiv ℝ k (x - y)‖ * ‖Whole.mfeTransportW D (ρ r) x‖ ≤ Lg * ‖Whole.mfeTransportW D (ρ r) x‖ :=
        mul_le_mul_of_nonneg_right (hR.gbd _) (norm_nonneg _)
      rw [Real.norm_eq_abs] at h1
      nlinarith [R.dens.nonneg y]
  rw [← integral_sub ia (sb1_rhoFu_int H hR hr x)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [map_sub, mul_sub]


/-- the constants of the pointwise bounds of `A G` and `ρ Ġ` -/
theorem sb1_AG_pt (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x : Euc d) :
    |sb1A D (ρ r) x * sb1G k (ρ r) x| ≤
      sb1CA D B C C3 * (1 + sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)) * sb1w ((d : ℝ) + 1) x := by
  have hd := H.tr.hd
  have hCA := H.CA_nonneg
  have Rr := H.rho hd hr
  have hCGc0 := sb1CG_nonneg (d := d) (s := D.s) Rr
  have hG := sb1_G_abs_le hd H.tr.hs0 H.tr.hsd hk Rr x
  have hA := H.A_le hr x
  have e1 : sb1w ((d : ℝ) + 2) x * (1 + ‖x‖) = sb1w ((d : ℝ) + 1) x := by
    have := sb1w_succ ((d : ℝ) + 1) x
    rwa [show (d : ℝ) + 1 + 1 = (d : ℝ) + 2 by ring] at this
  have hw2 := (sb1w_pos ((d : ℝ) + 2) x).le
  have hn := norm_nonneg x
  have hl := sb1_log_le_norm x
  rw [abs_mul]
  refine (mul_le_mul hA (hG.trans (by nlinarith [sb1_log_nonneg x] : Real.log (1 + ‖x‖) +
    sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) ≤
      (1 + sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)) * (1 + ‖x‖))) (abs_nonneg _)
    (mul_nonneg hCA hw2)).trans ?_
  rw [← e1]
  nlinarith [mul_nonneg hCA hw2]

theorem sb1_rhoGd_pt (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x : Euc d) :
    |ρ r x * sb1Gd D ρ k r x| ≤ C3 * sb1CGd d D.s (sb1CA D B C C3) * sb1w ((d : ℝ) + 1) x := by
  have hd := H.tr.hd
  have hC3 := H.C3nn
  have hCGd0 : 0 ≤ sb1CGd d D.s (sb1CA D B C C3) := sb1CGd_nonneg D.s H.CA_nonneg
  obtain ⟨-, hGd⟩ := sb1_Gd_facts H hk hr x
  have hρ := H.rho_le hr x
  have hρ0 := H.pos r hr x
  have e1 : sb1w ((d : ℝ) + 2) x * (1 + ‖x‖) = sb1w ((d : ℝ) + 1) x := by
    have := sb1w_succ ((d : ℝ) + 1) x
    rwa [show (d : ℝ) + 1 + 1 = (d : ℝ) + 2 by ring] at this
  have e2 := sb1w_32 x
  have hw3 := (sb1w_pos ((d : ℝ) + 3) x).le
  have hn := norm_nonneg x
  rw [abs_mul, abs_of_pos hρ0]
  have := mul_le_mul hρ hGd (abs_nonneg _) (mul_nonneg hC3 hw3)
  refine this.trans ?_
  have e3 : C3 * sb1w ((d : ℝ) + 3) x * (sb1CGd d D.s (sb1CA D B C C3) * (1 + ‖x‖)) =
      C3 * sb1CGd d D.s (sb1CA D B C C3) * sb1w ((d : ℝ) + 2) x := by
    rw [← e2]; ring
  rw [e3]
  have hw12 : sb1w ((d : ℝ) + 2) x ≤ sb1w ((d : ℝ) + 1) x := by
    rw [← e1]; nlinarith [sb1w_pos ((d : ℝ) + 2) x]
  exact mul_le_mul_of_nonneg_left hw12 (mul_nonneg hC3 hCGd0)

theorem sb1_AG_int (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    Integrable (fun x => sb1A D (ρ r) x * sb1G k (ρ r) x) := by
  have Rr := H.rho H.tr.hd hr
  have hw1 := sb1w_int H.tr.hd (p := (d : ℝ) + 1) (by linarith)
  refine (hw1.const_mul (sb1CA D B C C3 * (1 + sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)))).mono'
    (((H.A_cont hr).measurable.mul (sb1_G_meas hk Rr))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact sb1_AG_pt H hk hr x

theorem sb1_rhoGd_int (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    Integrable (fun x => ρ r x * sb1Gd D ρ k r x) := by
  have hw1 := sb1w_int H.tr.hd (p := (d : ℝ) + 1) (by linarith)
  refine (hw1.const_mul (C3 * sb1CGd d D.s (sb1CA D B C C3))).mono'
    (((H.tr.cont hr).measurable.mul (sb1_Gd_meas H hk hr))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact sb1_rhoGd_pt H hk hr x

theorem sb1_rho_absw (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (y : Euc d) :
    |ρ r y| ≤ C3 * sb1w ((d : ℝ) + 2) y := by
  rw [abs_of_pos (H.pos r hr y)]
  refine (H.rho_le hr y).trans (mul_le_mul_of_nonneg_left ?_ H.C3nn)
  have e2 := sb1w_32 y
  have hn := norm_nonneg y
  rw [← e2]
  nlinarith [sb1w_pos ((d : ℝ) + 3) y]

/-- Fubini/symmetry step: `∫ A G = ∫ ρ Ġ` -/
theorem sb1_S1 (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) :
    ∫ x, sb1A D (ρ r) x * sb1G k (ρ r) x = ∫ x, ρ r x * sb1Gd D ρ k r x := by
  have hd := H.tr.hd
  have R := H.rho hd hr
  have hCA := H.CA_nonneg
  have hC3 := H.C3nn
  have hmeasF : Measurable (fun p : Euc d × Euc d => sb1A D (ρ r) p.1 * (ρ r p.2 * k (p.1 - p.2))) :=
    ((H.A_cont hr).measurable.comp measurable_fst).mul (((H.tr.cont hr).measurable.comp measurable_snd).mul
      (hk.meas.comp (measurable_fst.sub measurable_snd)))
  have hprod : Integrable (fun p : Euc d × Euc d => sb1A D (ρ r) p.1 * (ρ r p.2 * k (p.1 - p.2)))
      (volume.prod volume) := by
    rw [integrable_prod_iff hmeasF.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun x => by
      simpa using (sb1_rhoG_int hd H.tr.hs0 H.tr.hsd hk R x).const_mul (sb1A D (ρ r) x), ?_⟩
    have hw1 := sb1w_int hd (p := (d : ℝ) + 1) (by linarith)
    refine (hw1.const_mul (sb1CA D B C C3 * sb1CGd d D.s C3)).mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact (hmeasF.norm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Euc d)))).aestronglyMeasurable
    · have hconv := (sb1_conv_phi hd H.tr.hs0 H.tr.hsd hk H.C3nn (φ := ρ r) (H.tr.cont hr).measurable
        (fun y => sb1_rho_absw H hr y) x).2
      have hCGd0 : 0 ≤ sb1CGd d D.s C3 := sb1CGd_nonneg D.s hC3
      have e : ∫ y, ‖sb1A D (ρ r) x * (ρ r y * k (x - y))‖ = |sb1A D (ρ r) x| * ∫ y, ‖ρ r y * k (x - y)‖ := by
        simp_rw [norm_mul, Real.norm_eq_abs]
        rw [integral_const_mul]
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _), e]
      have hA := H.A_le hr x
      have e1 : sb1w ((d : ℝ) + 2) x * (1 + ‖x‖) = sb1w ((d : ℝ) + 1) x := by
        have := sb1w_succ ((d : ℝ) + 1) x
        rwa [show (d : ℝ) + 1 + 1 = (d : ℝ) + 2 by ring] at this
      have hw2 := (sb1w_pos ((d : ℝ) + 2) x).le
      calc |sb1A D (ρ r) x| * ∫ y, ‖ρ r y * k (x - y)‖
          ≤ (sb1CA D B C C3 * sb1w ((d : ℝ) + 2) x) * (sb1CGd d D.s C3 * (1 + ‖x‖)) :=
            mul_le_mul hA hconv (integral_nonneg fun y => norm_nonneg _) (mul_nonneg hCA hw2)
        _ = sb1CA D B C C3 * sb1CGd d D.s C3 * sb1w ((d : ℝ) + 1) x := by rw [← e1]; ring
  have h1 : ∫ x, sb1A D (ρ r) x * sb1G k (ρ r) x = ∫ x, ∫ y, sb1A D (ρ r) x * (ρ r y * k (x - y)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [sb1G]
    rw [integral_const_mul]
  have h2 := integral_integral_swap (f := fun x y => sb1A D (ρ r) x * (ρ r y * k (x - y))) hprod
  rw [h1, h2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [sb1Gd]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have : k (y - x) = k (x - y) := by rw [← neg_sub x y]; exact hR.even _
  show sb1A D (ρ r) x * (ρ r y * k (x - y)) = ρ r y * (sb1A D (ρ r) x * k (y - x))
  rw [this]
  ring


/-- the symmetrisation step: `∫ ρ Ġ = -½ ∫ ρ H` -/
theorem sb1_S2 (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) :
    ∫ x, ρ r x * sb1Gd D ρ k r x = -(1 / 2) * ∫ x, ρ r x *
      sb1PG (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y))
        (ρ r) x := by
  have hd := H.tr.hd
  have R := H.rho hd hr
  have hC3 := H.C3nn
  have hLg := hR.Lg_nonneg
  have hCJ := H.CJ_nonneg
  set u := Whole.mfeTransportW D (ρ r) with hu
  set Phi : Euc d → Euc d → ℝ := fun x y =>
    ρ r x * ∑ kk, fderiv ℝ k (x - y) (sb1e kk) * sb1J D (ρ r) kk y with hPhidef
  have hPhi_eq : ∀ x y, Phi x y = ρ r x * (ρ r y * fderiv ℝ k (x - y) (u y)) := fun x y => by
    simp only [hPhidef]
    rw [← sb1_rhoFu_eq D (ρ r) (fderiv ℝ k (x - y)) y]
  have hmeas : Measurable (fun p : Euc d × Euc d => Phi p.1 p.2) := by
    refine (((H.tr.cont hr).comp continuous_fst).mul (continuous_finset_sum _ fun kk _ =>
      ((hR.cont_fderiv.comp (continuous_fst.sub continuous_snd)).clm_apply continuous_const).mul
        ((sb1_J_meas H hr kk).comp continuous_snd))).measurable
  have hw := sb1w_int hd (p := (d : ℝ) + 2) (by linarith)
  have hPhi : Integrable (fun p : Euc d × Euc d => Phi p.1 p.2) (volume.prod volume) := by
    have hb := Integrable.mul_prod (hw.const_mul C3) (hw.const_mul ((d : ℝ) * (Lg * sb1CJ D B C C3)))
      (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
    refine hb.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    simp only [hPhidef]
    rw [abs_mul]
    have h1 := sb1_rho_absw H hr p.1
    have h2 : |∑ kk, fderiv ℝ k (p.1 - p.2) (sb1e kk) * sb1J D (ρ r) kk p.2| ≤
        (d : ℝ) * (Lg * sb1CJ D B C C3) * sb1w ((d : ℝ) + 2) p.2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ kk, |fderiv ℝ k (p.1 - p.2) (sb1e kk) * sb1J D (ρ r) kk p.2|
          ≤ ∑ _kk : Fin d, Lg * (sb1CJ D B C C3 * sb1w ((d : ℝ) + 2) p.2) := by
            refine Finset.sum_le_sum fun kk _ => ?_
            rw [abs_mul]
            exact mul_le_mul ((sb1_apply_single_le _ kk).trans (hR.gbd _)) (H.J_bound hr kk p.2)
              (abs_nonneg _) hLg
        _ = (d : ℝ) * (Lg * sb1CJ D B C C3) * sb1w ((d : ℝ) + 2) p.2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hC3 (sb1w_pos _ _).le)
  have hPhis : Integrable (fun p : Euc d × Euc d => Phi p.2 p.1) (volume.prod volume) := hPhi.swap
  have hodd : ∀ x y, ρ r x * (ρ r y * fderiv ℝ k (x - y) (u x)) = -Phi y x := by
    intro x y
    rw [hPhi_eq y x]
    have : fderiv ℝ k (y - x) (u x) = -(fderiv ℝ k (x - y) (u x)) := by
      rw [← neg_sub x y]; exact sb1_fderiv_odd hR.diff hR.even _ _
    rw [this]; ring
  have e1 : ∀ x, ρ r x * sb1Gd D ρ k r x = ∫ y, Phi x y := by
    intro x
    rw [sb1_Gd_eq H hk hR hr x, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => (hPhi_eq x y).symm)
  have e2 : ∀ x, ρ r x * sb1PG (fun x y => fderiv ℝ k (x - y) (u x - u y)) (ρ r) x =
      (-(∫ y, Phi y x)) - ∫ y, Phi x y := by
    intro x
    rw [sb1_oneBody H hk hR hr x, mul_sub, e1 x, sb1_fderiv_G_apply hd H.tr.hs0 H.tr.hsd hk hR R x (u x),
      ← integral_const_mul, ← integral_neg]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun y => hodd x y)
  have i1 : Integrable (fun x => -(∫ y, Phi y x)) := hPhis.integral_prod_left.neg
  have i2 : Integrable (fun x => ∫ y, Phi x y) := hPhi.integral_prod_left
  simp_rw [e2, e1]
  rw [integral_sub i1 i2, integral_neg]
  have hsw := integral_integral_swap (f := fun x y => Phi y x) hPhis
  rw [hsw]
  ring

theorem sb1_cd_eq (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) :
    ∫ x, (sb1A D (ρ r) x * sb1G k (ρ r) x + ρ r x * sb1Gd D ρ k r x) = -(∫ x, ρ r x *
      sb1PG (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y))
        (ρ r) x) := by
  rw [integral_add (sb1_AG_int H hk hr) (sb1_rhoGd_int H hk hr), sb1_S1 H hk hR hr, sb1_S2 H hk hR hr]
  ring

end Static

end HRS.MS.MfeConf
