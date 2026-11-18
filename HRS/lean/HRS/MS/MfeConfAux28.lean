import HRS.MS.MfeConfAux27

/-!
# S.B.1, packet F3 (part 9): integration by parts in one particle variable

`sb1_ibp_cfg`: for `E = e^{-βN En}` (regular admissible kernel `k`) and `J = ρ u_V`,
`∫ E ∏_{l≠i}ρ(x_l) ∂_kk J_kk(x_i) dX = βN ∫ E ∏_{l≠i}ρ(x_l) J_kk(x_i) ∂_{(i,kk)}En dX`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section IBP

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} {k : Euc d → ℝ} {Lg : ℝ}

theorem sb1_dG_bound (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) (kk : Fin d) (x : Euc d) :
    |fderiv ℝ (sb1G k (ρ r)) x (sb1e kk)| ≤ Lg := by
  have R := H.rho H.tr.hd hr
  rw [sb1_fderiv_G_apply H.tr.hd H.tr.hs0 H.tr.hsd hk hR R x]
  have hLg := hR.Lg_nonneg
  have hi : Integrable (fun y => ρ r y * fderiv ℝ k (x - y) (sb1e kk)) := by
    refine (R.integrable.const_mul Lg).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact (R.dens.measurable.mul (((hR.cont_fderiv.comp (continuous_const.sub continuous_id)).clm_apply
        continuous_const).measurable)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (R.dens.nonneg y)]
      have h1 : |fderiv ℝ k (x - y) (sb1e kk)| ≤ Lg := (sb1_apply_single_le _ kk).trans (hR.gbd _)
      nlinarith [R.dens.nonneg y]
  have h := norm_integral_le_of_norm_le (R.integrable.const_mul Lg) (f := fun y => ρ r y * fderiv ℝ k (x - y) (sb1e kk))
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (R.dens.nonneg y)]
      have h1 : |fderiv ℝ k (x - y) (sb1e kk)| ≤ Lg := (sb1_apply_single_le _ kk).trans (hR.gbd _)
      nlinarith [R.dens.nonneg y])
  rw [Real.norm_eq_abs, integral_const_mul, R.int_one] at h
  linarith

theorem sb1_dG_meas (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) (e : Euc d) : Measurable (fun x => fderiv ℝ (sb1G k (ρ r)) x e) := by
  have R := H.rho H.tr.hd hr
  have : (fun x => fderiv ℝ (sb1G k (ρ r)) x e) = fun x => ∫ y, ρ r y * (fun z => fderiv ℝ k z e) (x - y) :=
    funext fun x => sb1_fderiv_G_apply H.tr.hd H.tr.hs0 H.tr.hsd hk hR R x e
  rw [this]
  exact sb1_meas_conv (H.tr.cont hr).measurable (hR.cont_fderiv.clm_apply continuous_const).measurable

theorem sb1_dE_bound (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) (hN : 1 ≤ N) (i : Fin N) (kk : Fin d) (X : Whole.EucConfig d N) :
    |sb1dE k (sb1G k (ρ r)) N X i (sb1e kk)| ≤ 2 * Lg := by
  have hLg := hR.Lg_nonneg
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : |∑ j ∈ Finset.univ.erase i, fderiv ℝ k (X i - X j) (sb1e kk)| ≤ (N - 1 : ℝ) * Lg := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.univ.erase i, |fderiv ℝ k (X i - X j) (sb1e kk)| ≤ ∑ _j ∈ Finset.univ.erase i, Lg :=
          Finset.sum_le_sum fun j _ => (sb1_apply_single_le _ kk).trans (hR.gbd _)
      _ = (N - 1 : ℝ) * Lg := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
          simp [Nat.cast_sub hN]
  have h2 := sb1_dG_bound H hk hR hr kk (X i)
  unfold sb1dE
  have hN0 : (0 : ℝ) < N := by linarith
  have e1 : |(1 / (N : ℝ) ^ 2) * ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (X i - X j) (sb1e kk)| ≤ Lg := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc 1 / (N : ℝ) ^ 2 * |∑ j ∈ Finset.univ.erase i, fderiv ℝ k (X i - X j) (sb1e kk)|
        ≤ 1 / (N : ℝ) ^ 2 * ((N - 1 : ℝ) * Lg) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ Lg := by
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
          nlinarith [mul_nonneg hLg (by nlinarith [sq_nonneg ((N : ℝ) - 1)] : (0 : ℝ) ≤ (N : ℝ) ^ 2 - ((N : ℝ) - 1))]
  have e2 : |(1 / (N : ℝ)) * fderiv ℝ (sb1G k (ρ r)) (X i) (sb1e kk)| ≤ Lg := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc 1 / (N : ℝ) * |fderiv ℝ (sb1G k (ρ r)) (X i) (sb1e kk)| ≤ 1 / (N : ℝ) * Lg :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ Lg := by
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hN0]
          nlinarith [mul_nonneg hLg (sub_nonneg.2 hn)]
  calc _ ≤ |(1 / (N : ℝ) ^ 2) * ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (X i - X j) (sb1e kk)| +
        |(1 / (N : ℝ)) * fderiv ℝ (sb1G k (ρ r)) (X i) (sb1e kk)| := abs_sub _ _
    _ ≤ 2 * Lg := by linarith

theorem sb1_dE_meas (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) (i : Fin N) (e : Euc d) :
    Measurable (fun X : Whole.EucConfig d N => sb1dE k (sb1G k (ρ r)) N X i e) := by
  unfold sb1dE
  refine (Measurable.const_mul (Finset.measurable_sum _ fun j _ => ?_) _).sub
    (((sb1_dG_meas H hk hR hr e).comp (measurable_pi_apply i)).const_mul _)
  exact ((hR.cont_fderiv.clm_apply continuous_const).measurable).comp
    ((measurable_pi_apply i).sub (measurable_pi_apply j))

/-- the uniform bound of the Gibbs weight -/
def sb1Cw (d : ℕ) (s C3 β : ℝ) (N : ℕ) : ℝ :=
  Real.exp (β * N * (sb1CG d s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) +
    sb1kap s * (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)))

theorem sb1Cw_pos (d : ℕ) (s C3 β : ℝ) (N : ℕ) : 0 < sb1Cw d s C3 β N := Real.exp_pos _

theorem Sb1Tr3.E_le (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hN : 1 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (X : Whole.EucConfig d N) :
    Real.exp (-β * N * sb1En k (ρ r) X) ≤ sb1Cw d D.s C3 β N :=
  sb1_E_le H.tr.hd H.tr.hs0 H.tr.hsd hN hβ hk (H.rho H.tr.hd hr) X

theorem sb1_En_cont (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) : Continuous (sb1En k (ρ r) : Whole.EucConfig d N → ℝ) :=
  continuous_iff_continuousAt.2 fun X =>
    (sb1_hasFDerivAt_En H.tr.hd H.tr.hs0 H.tr.hsd hk hR (H.rho H.tr.hd hr) X).continuousAt

/-- term bound -/
theorem sb1_cfg_term_bound (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) {β : ℝ} (hβ : 0 ≤ β) (hN : 1 ≤ N) (i : Fin N) {φ : Euc d → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hφ : ∀ y, |φ y| ≤ a * sb1w ((d : ℝ) + 2) y) (X : Whole.EucConfig d N) :
    |Real.exp (-β * N * sb1En k (ρ r) X) * ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) * φ (X i))| ≤
      sb1Cw d D.s C3 β N * (a * C3 ^ (N - 1)) * ∏ l, sb1w ((d : ℝ) + 2) (X l) := by
  have h1 := sb1_cfg_bound H hr i ha hφ X
  have hP0 : 0 ≤ ∏ l ∈ Finset.univ.erase i, ρ r (X l) := Finset.prod_nonneg fun l _ => (H.pos r hr _).le
  rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_of_nonneg hP0]
  calc Real.exp (-β * N * sb1En k (ρ r) X) * ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) * |φ (X i)|)
      = Real.exp (-β * N * sb1En k (ρ r) X) * (|φ (X i)| * ∏ l ∈ Finset.univ.erase i, ρ r (X l)) := by ring
    _ ≤ sb1Cw d D.s C3 β N * (a * C3 ^ (N - 1) * ∏ l, sb1w ((d : ℝ) + 2) (X l)) :=
        mul_le_mul (H.E_le hk hN hβ hr X) h1 (mul_nonneg (abs_nonneg _) hP0) (sb1Cw_pos _ _ _ _ _).le
    _ = _ := by ring

theorem sb1_cfg_term_int (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) {β : ℝ} (hβ : 0 ≤ β) (hN : 1 ≤ N) (i : Fin N) {φ : Euc d → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hφc : Continuous φ) (hφ : ∀ y, |φ y| ≤ a * sb1w ((d : ℝ) + 2) y) :
    Integrable (fun X : Whole.EucConfig d N => Real.exp (-β * N * sb1En k (ρ r) X) *
      ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) * φ (X i))) := by
  have hEcont : Continuous (fun X : Whole.EucConfig d N => Real.exp (-β * N * sb1En k (ρ r) X)) :=
    Real.continuous_exp.comp (continuous_const.mul (sb1_En_cont H hk hR hr))
  have hPcont : Continuous (fun X : Whole.EucConfig d N => ∏ l ∈ Finset.univ.erase i, ρ r (X l)) :=
    continuous_finset_prod _ fun l _ => (H.tr.cont hr).comp (continuous_apply l)
  exact sb1_cfg_int_of_bound H.tr.hd (hEcont.mul (hPcont.mul (hφc.comp (continuous_apply i)))).aestronglyMeasurable
    (fun X => sb1_cfg_term_bound H hk hr hβ hN i ha hφ X)

theorem sb1_ibp_cfg (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) {β : ℝ} (hβ : 0 ≤ β) (hN : 1 ≤ N) (i : Fin N) (kk : Fin d) :
    ∫ X : Whole.EucConfig d N, Real.exp (-β * N * sb1En k (ρ r) X) *
        ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) * fderiv ℝ (sb1J D (ρ r) kk) (X i) (sb1e kk)) =
      β * N * ∫ X : Whole.EucConfig d N, Real.exp (-β * N * sb1En k (ρ r) X) *
        ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) * sb1J D (ρ r) kk (X i) *
          sb1dE k (sb1G k (ρ r)) N X i (sb1e kk)) := by
  have hd := H.tr.hd
  have R := H.rho hd hr
  have hLg := hR.Lg_nonneg
  have hCJ := H.CJ_nonneg
  have hCdJ := H.CdJ_nonneg
  have hC3 := H.C3nn
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hEn : ∀ X : Whole.EucConfig d N,
      HasFDerivAt (sb1En k (ρ r) : Whole.EucConfig d N → ℝ) (sb1dEn k (sb1G k (ρ r)) N X) X := fun X =>
    sb1_hasFDerivAt_En hd H.tr.hs0 H.tr.hsd hk hR R X
  have hEnc : Continuous (sb1En k (ρ r) : Whole.EucConfig d N → ℝ) :=
    continuous_iff_continuousAt.2 fun X => (hEn X).continuousAt
  have hEd : ∀ X : Whole.EucConfig d N,
      HasFDerivAt (fun X : Whole.EucConfig d N => Real.exp (-β * N * sb1En k (ρ r) X))
        (Real.exp (-β * N * sb1En k (ρ r) X) • ((-β * N) • sb1dEn k (sb1G k (ρ r)) N X)) X :=
    fun X => ((hEn X).const_mul (-β * N)).exp
  have hJc := sb1_J_contDiff H.tr.V hd H.tr.hs0 H.tr.hsd (H.tr.slice r hr) (H.pos r hr) kk
  have hJd : Differentiable ℝ (sb1J D (ρ r) kk) := hJc.differentiable (by norm_num)
  have hρd : Differentiable ℝ (ρ r) := (H.tr.slice r hr).decay.1.differentiable (by norm_num)
  have hJ' : ∀ X : Whole.EucConfig d N, HasFDerivAt (fun X : Whole.EucConfig d N => sb1J D (ρ r) kk (X i))
      ((fderiv ℝ (sb1J D (ρ r) kk) (X i)).comp (sb1pr d N i)) X := fun X => by
    have h1 : HasFDerivAt (sb1J D (ρ r) kk) (fderiv ℝ (sb1J D (ρ r) kk) (X i)) (sb1pr d N i X) :=
      (hJd (X i)).hasFDerivAt
    exact h1.comp X (sb1pr d N i).hasFDerivAt
  have hP : ∀ X : Whole.EucConfig d N,
      HasFDerivAt (fun X : Whole.EucConfig d N => ∏ l ∈ Finset.univ.erase i, ρ r (X l))
        (∑ l ∈ Finset.univ.erase i, (∏ j ∈ (Finset.univ.erase i).erase l, ρ r (X j)) •
          (fderiv ℝ (ρ r) (X l)).comp (sb1pr d N l)) X := fun X =>
    HasFDerivAt.finsetProd (u := Finset.univ.erase i) (g := fun l (X : Whole.EucConfig d N) => ρ r (X l))
      (fun l _ => (hρd (X l)).hasFDerivAt.comp X
        (sb1pr d N l).hasFDerivAt)
  have hg : ∀ X : Whole.EucConfig d N,
      HasFDerivAt (fun X : Whole.EucConfig d N => sb1J D (ρ r) kk (X i) * ∏ l ∈ Finset.univ.erase i, ρ r (X l))
        (sb1J D (ρ r) kk (X i) • (∑ l ∈ Finset.univ.erase i, (∏ j ∈ (Finset.univ.erase i).erase l, ρ r (X j)) •
          (fderiv ℝ (ρ r) (X l)).comp (sb1pr d N l)) +
          (∏ l ∈ Finset.univ.erase i, ρ r (X l)) •
            (fderiv ℝ (sb1J D (ρ r) kk) (X i)).comp (sb1pr d N i)) X :=
    fun X => (hJ' X).fun_mul (hP X)
  set v : Whole.EucConfig d N := Pi.single i (sb1e kk) with hv
  have hgv : ∀ X : Whole.EucConfig d N,
      fderiv ℝ (fun X : Whole.EucConfig d N => sb1J D (ρ r) kk (X i) * ∏ l ∈ Finset.univ.erase i, ρ r (X l)) X v =
        (∏ l ∈ Finset.univ.erase i, ρ r (X l)) * fderiv ℝ (sb1J D (ρ r) kk) (X i) (sb1e kk) := by
    intro X
    rw [(hg X).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul]
    have h0 : ∀ l ∈ Finset.univ.erase i, (sb1pr d N l) v = 0 := by
      intro l hl
      simp [sb1pr, hv, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hl)]
    have h1 : (sb1pr d N i) v = sb1e kk := by simp [sb1pr, hv]
    rw [h1, Finset.sum_eq_zero (fun l hl => by rw [h0 l hl]; simp), mul_zero, zero_add]
  have hfv : ∀ X : Whole.EucConfig d N,
      fderiv ℝ (fun X : Whole.EucConfig d N => Real.exp (-β * N * sb1En k (ρ r) X)) X v =
        Real.exp (-β * N * sb1En k (ρ r) X) * ((-β * N) * sb1dE k (sb1G k (ρ r)) N X i (sb1e kk)) := by
    intro X
    rw [(hEd X).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hv, sb1_dEn_single hR (sb1G k (ρ r)) X i (sb1e kk)]
  have hCJ' := sb1Cw_pos d D.s C3 β N
  have hJcont : Continuous (sb1J D (ρ r) kk) := hJc.continuous
  have hρcont : Continuous (ρ r) := H.tr.cont hr
  have hPcont : Continuous (fun X : Whole.EucConfig d N => ∏ l ∈ Finset.univ.erase i, ρ r (X l)) :=
    continuous_finset_prod _ fun l _ => hρcont.comp (continuous_apply l)
  have hgcont : Continuous (fun X : Whole.EucConfig d N =>
      sb1J D (ρ r) kk (X i) * ∏ l ∈ Finset.univ.erase i, ρ r (X l)) :=
    (hJcont.comp (continuous_apply i)).mul hPcont
  have hEcont : Continuous (fun X : Whole.EucConfig d N => Real.exp (-β * N * sb1En k (ρ r) X)) :=
    Real.continuous_exp.comp (continuous_const.mul hEnc)
  have hdEm := sb1_dE_meas H hk hR hr i (sb1e kk)
  -- integrability
  have hfg0 := sb1_cfg_term_int H hk hR hr hβ hN i hCJ hJcont (fun y => H.J_bound hr kk y)
  have hfg : Integrable (fun X : Whole.EucConfig d N => Real.exp (-β * N * sb1En k (ρ r) X) *
      (sb1J D (ρ r) kk (X i) * ∏ l ∈ Finset.univ.erase i, ρ r (X l))) :=
    hfg0.congr (Eventually.of_forall fun X => by simp only [mul_comm (sb1J D (ρ r) kk (X i))])
  have hfg' : Integrable (fun X : Whole.EucConfig d N => Real.exp (-β * N * sb1En k (ρ r) X) *
      fderiv ℝ (fun X : Whole.EucConfig d N => sb1J D (ρ r) kk (X i) * ∏ l ∈ Finset.univ.erase i, ρ r (X l)) X v) := by
    simp_rw [hgv]
    exact sb1_cfg_term_int H hk hR hr hβ hN i hCdJ (sb1_dJ_cont H hr kk) (fun y => H.dJ_bound hr kk y)
  have hf'g : Integrable (fun X : Whole.EucConfig d N =>
      fderiv ℝ (fun X : Whole.EucConfig d N => Real.exp (-β * N * sb1En k (ρ r) X)) X v *
        (sb1J D (ρ r) kk (X i) * ∏ l ∈ Finset.univ.erase i, ρ r (X l))) := by
    simp_rw [hfv]
    refine sb1_cfg_int_of_bound hd ((hEcont.measurable.mul (measurable_const.mul hdEm)).mul
      hgcont.measurable).aestronglyMeasurable (K := sb1Cw d D.s C3 β N * (β * N * (2 * Lg)) * (sb1CJ D B C C3 * C3 ^ (N - 1)))
      (fun X => ?_)
    have hP0 : 0 ≤ ∏ l ∈ Finset.univ.erase i, ρ r (X l) := Finset.prod_nonneg fun l _ => (H.pos r hr _).le
    have h1 := sb1_cfg_bound H hr i hCJ (fun y => H.J_bound hr kk y) X
    have h2 := sb1_dE_bound H hk hR hr hN i kk X
    have hβN : 0 ≤ β * N := by positivity
    have e : |Real.exp (-β * N * sb1En k (ρ r) X) * (-β * N * sb1dE k (sb1G k (ρ r)) N X i (sb1e kk)) *
        (sb1J D (ρ r) kk (X i) * ∏ l ∈ Finset.univ.erase i, ρ r (X l))| =
        Real.exp (-β * N * sb1En k (ρ r) X) * (β * N * |sb1dE k (sb1G k (ρ r)) N X i (sb1e kk)|) *
          (|sb1J D (ρ r) kk (X i)| * ∏ l ∈ Finset.univ.erase i, ρ r (X l)) := by
      simp only [abs_mul, abs_neg, abs_of_nonneg hβ, Nat.abs_cast, abs_of_nonneg hP0,
        abs_of_pos (Real.exp_pos _)]
    rw [e]
    calc Real.exp (-β * N * sb1En k (ρ r) X) * (β * N * |sb1dE k (sb1G k (ρ r)) N X i (sb1e kk)|) *
          (|sb1J D (ρ r) kk (X i)| * ∏ l ∈ Finset.univ.erase i, ρ r (X l))
        ≤ (sb1Cw d D.s C3 β N * (β * N * (2 * Lg))) *
            (sb1CJ D B C C3 * C3 ^ (N - 1) * ∏ l, sb1w ((d : ℝ) + 2) (X l)) := by
          refine mul_le_mul (mul_le_mul (H.E_le hk hN hβ hr X) (mul_le_mul_of_nonneg_left h2 hβN) (by positivity)
            hCJ'.le) h1 (mul_nonneg (abs_nonneg _) hP0) (by positivity)
      _ = _ := by ring
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Whole.EucConfig d N)))
    (f := fun X : Whole.EucConfig d N => Real.exp (-β * N * sb1En k (ρ r) X))
    (g := fun X : Whole.EucConfig d N => sb1J D (ρ r) kk (X i) * ∏ l ∈ Finset.univ.erase i, ρ r (X l)) (v := v)
    hf'g hfg' hfg (fun X _ => (hEd X).differentiableAt) (fun X _ => (hg X).differentiableAt)
  simp only [hgv, hfv] at key
  rw [key, ← integral_neg, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  ring

end IBP

end HRS.MS.MfeConf
