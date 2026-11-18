import HRS.MS.MfeConfAux29

/-!
# S.B.1, packet F3 (part 11): the derivative of the normaliser is `βN ∫ W pairEnergy`

`sb1_dK_eq`: for a regular admissible kernel `k` and `0 ≤ r ≤ T`
`∫ ∂_r W_r(X) dX = β N ∫ W_r(X) 𝖥_N^{h}(X, ρ_r) dX`, `h(x,y) = ∇k(x-y)·(u_V^r(x) - u_V^r(y))`,
by the integration by parts `sb1_ibp_cfg` in each variable, the one-body identity and the identity for `ċ`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_dE_expand (k G : Euc d → ℝ) (X : Whole.EucConfig d N) (i : Fin N) (v : Euc d) :
    sb1dE k G N X i v = ∑ kk, v kk * sb1dE k G N X i (sb1e kk) := by
  have hL : ∀ e, sb1dE k G N X i e = (((1 / (N : ℝ) ^ 2) • ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (X i - X j) -
      (1 / (N : ℝ)) • fderiv ℝ G (X i) : Euc d →L[ℝ] ℝ)) e := by
    intro e
    simp [sb1dE, ContinuousLinearMap.sum_apply]
  rw [hL v, sb1_clm_expand _ v]
  exact Finset.sum_congr rfl fun kk _ => by rw [hL (sb1e kk)]

theorem sb1_pair_alg {k : Euc d → ℝ} {Lg : ℝ} (hR : Sb1KerR d k Lg) (u : Euc d → Euc d)
    (G Gd PG : Euc d → ℝ) (cdot : ℝ) (hone : ∀ x, fderiv ℝ G x (u x) = PG x + Gd x)
    (X : Whole.EucConfig d N) (hN : 1 ≤ N) :
    ∑ i, sb1dE k G N X i (u (X i)) - (-(1 / (N : ℝ)) * ∑ a, Gd (X a) + (1 / 2) * cdot) =
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
          fderiv ℝ k (X i - X j) (u (X i) - u (X j)) - (1 / (N : ℝ)) * ∑ i, PG (X i) - (1 / 2) * cdot := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  set S1 : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (X i - X j) (u (X i)) with hS1
  have hS2 : ∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (X i - X j) (u (X j)) = -S1 := by
    rw [MP.SelfSimP4Impl.p4k_sum_swap (fun i j => fderiv ℝ k (X i - X j) (u (X j)))]
    rw [hS1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← neg_sub (X i) (X j)]
    exact sb1_fderiv_odd hR.diff hR.even _ _
  have hsym : ∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (X i - X j) (u (X i) - u (X j)) = 2 * S1 := by
    simp only [map_sub, Finset.sum_sub_distrib]
    rw [hS2, ← hS1]
    ring
  have hsum : ∑ i, sb1dE k G N X i (u (X i)) =
      (1 / (N : ℝ) ^ 2) * S1 - (1 / (N : ℝ)) * (∑ i, PG (X i) + ∑ i, Gd (X i)) := by
    unfold sb1dE
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp_rw [hone, Finset.sum_add_distrib]
    rw [hS1]
  rw [hsym, hsum]
  ring

section Dk

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} {k : Euc d → ℝ} {Lg : ℝ}

theorem sb1_cfg_term_int2 (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) {β : ℝ} (hβ : 0 ≤ β) (hN : 1 ≤ N) (i : Fin N) (kk : Fin d) :
    Integrable (fun X : Whole.EucConfig d N => Real.exp (-β * N * sb1En k (ρ r) X) *
      ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) * sb1J D (ρ r) kk (X i) *
        sb1dE k (sb1G k (ρ r)) N X i (sb1e kk))) := by
  have hd := H.tr.hd
  have hLg := hR.Lg_nonneg
  have hCJ := H.CJ_nonneg
  have hEc : Continuous (fun X : Whole.EucConfig d N => Real.exp (-β * N * sb1En k (ρ r) X)) :=
    Real.continuous_exp.comp (continuous_const.mul (sb1_En_cont H hk hR hr))
  have hPc : Continuous (fun X : Whole.EucConfig d N => ∏ l ∈ Finset.univ.erase i, ρ r (X l)) :=
    continuous_finset_prod _ fun l _ => (H.tr.cont hr).comp (continuous_apply l)
  have hJc := sb1_J_meas H hr kk
  refine sb1_cfg_int_of_bound hd (hEc.measurable.mul ((hPc.measurable.mul (hJc.measurable.comp
    (measurable_pi_apply i))).mul (sb1_dE_meas H hk hR hr i (sb1e kk)))).aestronglyMeasurable
    (K := sb1Cw d D.s C3 β N * (sb1CJ D B C C3 * C3 ^ (N - 1) * (2 * Lg))) (fun X => ?_)
  have h1 := sb1_cfg_term_bound H hk hr hβ hN i hCJ (fun y => H.J_bound hr kk y) X
  have h2 := sb1_dE_bound H hk hR hr hN i kk X
  have hP0 : 0 ≤ ∏ l ∈ Finset.univ.erase i, ρ r (X l) := Finset.prod_nonneg fun l _ => (H.pos r hr _).le
  have hBd : 0 ≤ ∏ l, sb1w ((d : ℝ) + 2) (X l) := Finset.prod_nonneg fun l _ => (sb1w_pos _ _).le
  calc _ = |Real.exp (-β * N * sb1En k (ρ r) X) * ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) * sb1J D (ρ r) kk (X i))| *
        |sb1dE k (sb1G k (ρ r)) N X i (sb1e kk)| := by rw [← abs_mul]; congr 1; ring
    _ ≤ (sb1Cw d D.s C3 β N * (sb1CJ D B C C3 * C3 ^ (N - 1)) * ∏ l, sb1w ((d : ℝ) + 2) (X l)) * (2 * Lg) :=
        mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    _ = _ := by ring

/-- the pointwise algebraic identity -/
theorem sb1_alg_pt (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) {β : ℝ} (hN : 1 ≤ N) (X : Whole.EucConfig d N) :
    sb1Wdot D ρ k β N r X - β * N * (sb1Wf k β N ρ r X *
      Whole.pairEnergy (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y))
        X (Whole.withDensityReal (ρ r))) =
    ∑ i, ∑ kk, (Real.exp (-β * N * sb1En k (ρ r) X) *
        ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) * fderiv ℝ (sb1J D (ρ r) kk) (X i) (sb1e kk)) -
      β * N * (Real.exp (-β * N * sb1En k (ρ r) X) * ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) *
        sb1J D (ρ r) kk (X i) * sb1dE k (sb1G k (ρ r)) N X i (sb1e kk)))) := by
  have hd := H.tr.hd
  have R := H.rho hd hr
  have hcd : sb1cdot D ρ k r = -(∫ x, ρ r x * sb1PG (fun x y => fderiv ℝ k (x - y)
      (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y)) (ρ r) x) := sb1_cd_eq H hk hR hr
  have hpe : Whole.pairEnergy (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x -
        Whole.mfeTransportW D (ρ r) y)) X (Whole.withDensityReal (ρ r)) =
      ∑ i, sb1dE k (sb1G k (ρ r)) N X i (Whole.mfeTransportW D (ρ r) (X i)) - sb1EnDot D ρ k N r X := by
    rw [sb1_pairEnergy_eq R.dens]
    beta_reduce
    have h1 := sb1_pair_alg hR (Whole.mfeTransportW D (ρ r)) (sb1G k (ρ r)) (sb1Gd D ρ k r)
      (sb1PG (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y)) (ρ r))
      (sb1cdot D ρ k r) (fun x => by have := sb1_oneBody H hk hR hr x; linarith) X hN
    unfold sb1EnDot
    rw [hcd] at h1 ⊢
    linarith
  have hA : ∀ i, ∑ kk, fderiv ℝ (sb1J D (ρ r) kk) (X i) (sb1e kk) = sb1A D (ρ r) (X i) := fun i =>
    (sb1_A_eq_sumJ H.tr.V hd H.tr.hs0 H.tr.hsd (H.tr.slice r hr) (H.pos r hr) (X i)).symm
  have hdE : ∀ i, ∑ kk, sb1J D (ρ r) kk (X i) * sb1dE k (sb1G k (ρ r)) N X i (sb1e kk) =
      ρ r (X i) * sb1dE k (sb1G k (ρ r)) N X i (Whole.mfeTransportW D (ρ r) (X i)) := by
    intro i
    rw [sb1_dE_expand k (sb1G k (ρ r)) X i (Whole.mfeTransportW D (ρ r) (X i)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun kk _ => ?_
    simp only [sb1J]
    ring
  have hPi : ∀ i, (∏ l ∈ Finset.univ.erase i, ρ r (X l)) * ρ r (X i) = ∏ l, ρ r (X l) := fun i => by
    rw [mul_comm]; exact Finset.mul_prod_erase Finset.univ (fun l => ρ r (X l)) (Finset.mem_univ i)
  have lhs1 : ∑ i, ∑ kk, Real.exp (-β * N * sb1En k (ρ r) X) *
      ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) * fderiv ℝ (sb1J D (ρ r) kk) (X i) (sb1e kk)) =
      (∑ i, sb1A D (ρ r) (X i) * ∏ l ∈ Finset.univ.erase i, ρ r (X l)) * Real.exp (-β * N * sb1En k (ρ r) X) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hA i]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun kk _ => ?_
    ring
  have lhs2 : ∑ i, ∑ kk, β * N * (Real.exp (-β * N * sb1En k (ρ r) X) *
      ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) * sb1J D (ρ r) kk (X i) *
        sb1dE k (sb1G k (ρ r)) N X i (sb1e kk))) =
      β * N * (Real.exp (-β * N * sb1En k (ρ r) X) * ((∏ l, ρ r (X l)) *
        ∑ i, sb1dE k (sb1G k (ρ r)) N X i (Whole.mfeTransportW D (ρ r) (X i)))) := by
    have this : ∀ i, ∑ kk, β * N * (Real.exp (-β * N * sb1En k (ρ r) X) *
        ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) * sb1J D (ρ r) kk (X i) *
          sb1dE k (sb1G k (ρ r)) N X i (sb1e kk))) =
        β * N * (Real.exp (-β * N * sb1En k (ρ r) X) * ((∏ l, ρ r (X l)) *
          sb1dE k (sb1G k (ρ r)) N X i (Whole.mfeTransportW D (ρ r) (X i)))) := by
      intro i
      rw [← hPi i, ← Finset.mul_sum]
      congr 1
      rw [← Finset.mul_sum]
      congr 1
      calc ∑ kk, (∏ l ∈ Finset.univ.erase i, ρ r (X l)) * sb1J D (ρ r) kk (X i) *
            sb1dE k (sb1G k (ρ r)) N X i (sb1e kk)
          = (∏ l ∈ Finset.univ.erase i, ρ r (X l)) * ∑ kk, sb1J D (ρ r) kk (X i) *
            sb1dE k (sb1G k (ρ r)) N X i (sb1e kk) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun kk _ => by ring
        _ = _ := by rw [hdE i]; ring
    simp only [this]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Finset.sum_sub_distrib]
  rw [lhs1, lhs2, hpe]
  unfold sb1Wdot sb1Wf
  ring

/-- the integrals of the two terms of `T_{i,kk}` agree -/
theorem sb1_T_int_zero (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) {β : ℝ} (hβ : 0 ≤ β) (hN : 1 ≤ N) (i : Fin N) (kk : Fin d) :
    ∫ X : Whole.EucConfig d N, (Real.exp (-β * N * sb1En k (ρ r) X) *
        ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) * fderiv ℝ (sb1J D (ρ r) kk) (X i) (sb1e kk)) -
      β * N * (Real.exp (-β * N * sb1En k (ρ r) X) * ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) *
        sb1J D (ρ r) kk (X i) * sb1dE k (sb1G k (ρ r)) N X i (sb1e kk)))) = 0 := by
  rw [integral_sub (sb1_cfg_term_int H hk hR hr hβ hN i H.CdJ_nonneg (sb1_dJ_cont H hr kk)
      (fun y => H.dJ_bound hr kk y)) ((sb1_cfg_term_int2 H hk hR hr hβ hN i kk).const_mul _),
    integral_const_mul, sb1_ibp_cfg H hk hR hr hβ hN i kk]
  ring

theorem sb1_dK_eq (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) {β : ℝ} (hβ : 0 ≤ β) (hN : 1 ≤ N) :
    ∫ X : Whole.EucConfig d N, sb1Wdot D ρ k β N r X = β * N * ∫ X : Whole.EucConfig d N, sb1Wf k β N ρ r X *
      Whole.pairEnergy (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y))
        X (Whole.withDensityReal (ρ r)) := by
  have hd := H.tr.hd
  have hBd : Integrable (fun X : Whole.EucConfig d N => ∏ l, sb1w ((d : ℝ) + 2) (X l)) volume :=
    Integrable.fintype_prod (fun _ => sb1w_int hd (p := (d : ℝ) + 2) (by linarith))
  have hW : Integrable (fun X : Whole.EucConfig d N => sb1Wdot D ρ k β N r X) :=
    sb1_cfg_int_of_bound hd (sb1_Wdot_meas H hk hR hr).aestronglyMeasurable
      (fun X => sb1_Wdot_bound H hk hβ hN hr X)
  have hT : ∀ i kk, Integrable (fun X : Whole.EucConfig d N => (Real.exp (-β * N * sb1En k (ρ r) X) *
        ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) * fderiv ℝ (sb1J D (ρ r) kk) (X i) (sb1e kk)) -
      β * N * (Real.exp (-β * N * sb1En k (ρ r) X) * ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) *
        sb1J D (ρ r) kk (X i) * sb1dE k (sb1G k (ρ r)) N X i (sb1e kk))))) := fun i kk =>
    (sb1_cfg_term_int H hk hR hr hβ hN i H.CdJ_nonneg (sb1_dJ_cont H hr kk) (fun y => H.dJ_bound hr kk y)).sub
      ((sb1_cfg_term_int2 H hk hR hr hβ hN i kk).const_mul _)
  have hTs : Integrable (fun X : Whole.EucConfig d N => ∑ i, ∑ kk, (Real.exp (-β * N * sb1En k (ρ r) X) *
        ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) * fderiv ℝ (sb1J D (ρ r) kk) (X i) (sb1e kk)) -
      β * N * (Real.exp (-β * N * sb1En k (ρ r) X) * ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) *
        sb1J D (ρ r) kk (X i) * sb1dE k (sb1G k (ρ r)) N X i (sb1e kk))))) :=
    integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun kk _ => hT i kk
  have hzero : ∫ X : Whole.EucConfig d N, ∑ i, ∑ kk, (Real.exp (-β * N * sb1En k (ρ r) X) *
        ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) * fderiv ℝ (sb1J D (ρ r) kk) (X i) (sb1e kk)) -
      β * N * (Real.exp (-β * N * sb1En k (ρ r) X) * ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) *
        sb1J D (ρ r) kk (X i) * sb1dE k (sb1G k (ρ r)) N X i (sb1e kk)))) = 0 := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun kk _ => hT i kk)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_finset_sum _ (fun kk _ => hT i kk)]
    exact Finset.sum_eq_zero fun kk _ => sb1_T_int_zero H hk hR hr hβ hN i kk
  have hid : ∀ X : Whole.EucConfig d N, β * N * (sb1Wf k β N ρ r X *
      Whole.pairEnergy (fun x y => fderiv ℝ k (x - y) (Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y))
        X (Whole.withDensityReal (ρ r))) = sb1Wdot D ρ k β N r X - ∑ i, ∑ kk, (Real.exp (-β * N * sb1En k (ρ r) X) *
        ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) * fderiv ℝ (sb1J D (ρ r) kk) (X i) (sb1e kk)) -
      β * N * (Real.exp (-β * N * sb1En k (ρ r) X) * ((∏ l ∈ Finset.univ.erase i, ρ r (X l)) *
        sb1J D (ρ r) kk (X i) * sb1dE k (sb1G k (ρ r)) N X i (sb1e kk)))) := fun X => by
    have := sb1_alg_pt H hk hR hr (β := β) hN X
    linarith
  rw [← integral_const_mul]
  simp_rw [hid]
  rw [integral_sub hW hTs, hzero, sub_zero]

end Dk

end HRS.MS.MfeConf
