import HRS.MS.MfeConfAux28

/-!
# S.B.1, packet F3 (part 10): differentiation of the normaliser `K_r = ∫ ∏ρ_r(x_i) e^{-βN En_r(X)} dX`

For a regular admissible kernel `k` and `0 < r < T`:
`sb1_hasDerivAt_K`: `K` is differentiable at `r` with derivative `∫ sb1Wdot` (differentiation under the integral; the
domination is `K_b ∏_l (1+|x_l|)^{-(d+2)}`, uniform in `r`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section KDeriv

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} {k : Euc d → ℝ} {Lg : ℝ}

/-- the unnormalised Gibbs density at time `r` -/
def sb1Wf (k : Euc d → ℝ) (β : ℝ) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (r : ℝ) (X : Whole.EucConfig d N) : ℝ :=
  (∏ i, ρ r (X i)) * Real.exp (-β * N * sb1En k (ρ r) X)

/-- `ċ_r = ∂_r c_r` -/
def sb1cdot (D : Whole.WholeDyn d) (ρ : ℝ → Euc d → ℝ) (k : Euc d → ℝ) (r : ℝ) : ℝ :=
  ∫ x, (sb1A D (ρ r) x * sb1G k (ρ r) x + ρ r x * sb1Gd D ρ k r x)

/-- `∂_r En_r(X)` -/
def sb1EnDot (D : Whole.WholeDyn d) (ρ : ℝ → Euc d → ℝ) (k : Euc d → ℝ) (N : ℕ) (r : ℝ)
    (X : Whole.EucConfig d N) : ℝ :=
  -(1 / (N : ℝ)) * ∑ a, sb1Gd D ρ k r (X a) + (1 / 2) * sb1cdot D ρ k r

/-- `∂_r W_r(X)` -/
def sb1Wdot (D : Whole.WholeDyn d) (ρ : ℝ → Euc d → ℝ) (k : Euc d → ℝ) (β : ℝ) (N : ℕ) (r : ℝ)
    (X : Whole.EucConfig d N) : ℝ :=
  (∑ i, sb1A D (ρ r) (X i) * ∏ l ∈ Finset.univ.erase i, ρ r (X l)) * Real.exp (-β * N * sb1En k (ρ r) X) +
    (∏ i, ρ r (X i)) * (Real.exp (-β * N * sb1En k (ρ r) X) * ((-β * N) * sb1EnDot D ρ k N r X))

theorem sb1_hasDerivAt_Wf (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T) (hk : Sb1KerU d D.s k) {β : ℝ}
    {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) T) (X : Whole.EucConfig d N) :
    HasDerivAt (fun r => sb1Wf k β N ρ r X) (sb1Wdot D ρ k β N r₀ X) r₀ := by
  have hprod : HasDerivAt (fun r => ∏ i, ρ r (X i))
      (∑ i, (∏ j ∈ Finset.univ.erase i, ρ r₀ (X j)) • sb1A D (ρ r₀) (X i)) r₀ :=
    HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin N))) (f := fun i r => ρ r (X i))
      (fun i _ => sb1_hasDerivAt H.tr hT hr₀ (X i))
  have hG : HasDerivAt (fun r => ∑ a, sb1G k (ρ r) (X a)) (∑ a, sb1Gd D ρ k r₀ (X a)) r₀ :=
    HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N))) (fun a _ => sb1_hasDerivAt_G H hT hk hr₀ (X a))
  have hc := sb1_hasDerivAt_c H hT hk hr₀
  have hEn : HasDerivAt (fun r => sb1En k (ρ r) X) (sb1EnDot D ρ k N r₀ X) r₀ := by
    have h : HasDerivAt (fun r => sb1En k (ρ r) X)
        (0 - (1 / (N : ℝ)) * ∑ a, sb1Gd D ρ k r₀ (X a) + (1 / 2) * (∫ x, (sb1A D (ρ r₀) x * sb1G k (ρ r₀) x +
          ρ r₀ x * sb1Gd D ρ k r₀ x))) r₀ :=
      ((hasDerivAt_const r₀ ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i - X j))).sub
        (hG.const_mul (1 / (N : ℝ)))).add (hc.const_mul (1 / 2))
    refine h.congr_deriv ?_
    unfold sb1EnDot sb1cdot
    ring
  have hE := ((hEn.const_mul (-β * N)).exp)
  have hs : ∑ i, (∏ j ∈ Finset.univ.erase i, ρ r₀ (X j)) • sb1A D (ρ r₀) (X i) =
      ∑ i, sb1A D (ρ r₀) (X i) * ∏ l ∈ Finset.univ.erase i, ρ r₀ (X l) :=
    Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
  have h2 : HasDerivAt (fun r => sb1Wf k β N ρ r X) (sb1Wdot D ρ k β N r₀ X) r₀ := by
    have := hprod.mul hE
    rw [hs] at this
    exact this
  exact h2

theorem sb1_cdot_bound (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    |sb1cdot D ρ k r| ≤ (sb1CA D B C C3 * (1 + sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)) +
      C3 * sb1CGd d D.s (sb1CA D B C C3)) * ∫ x : Euc d, sb1w ((d : ℝ) + 1) x := by
  have hd := H.tr.hd
  have hw1 := sb1w_int hd (p := (d : ℝ) + 1) (by linarith)
  have hint := (sb1_AG_int H hk hr).add (sb1_rhoGd_int H hk hr)
  have hb : Integrable (fun x : Euc d => (sb1CA D B C C3 * (1 + sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)) +
      C3 * sb1CGd d D.s (sb1CA D B C C3)) * sb1w ((d : ℝ) + 1) x) := hw1.const_mul _
  have h := norm_integral_le_of_norm_le hb (f := fun x => sb1A D (ρ r) x * sb1G k (ρ r) x + ρ r x * sb1Gd D ρ k r x)
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans ?_
      have := sb1_AG_pt H hk hr x
      have := sb1_rhoGd_pt H hk hr x
      nlinarith)
  rw [Real.norm_eq_abs, integral_const_mul] at h
  exact h


theorem sb1_prod_mul_le (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (a : Fin N)
    (X : Whole.EucConfig d N) :
    (∏ l, ρ r (X l)) * (1 + ‖X a‖) ≤ C3 ^ N * ∏ l, sb1w ((d : ℝ) + 2) (X l) := by
  have hC3 := H.C3nn
  have h1 : ρ r (X a) * (1 + ‖X a‖) ≤ C3 * sb1w ((d : ℝ) + 2) (X a) := by
    have := mul_le_mul_of_nonneg_right (H.rho_le hr (X a)) (by positivity : (0 : ℝ) ≤ 1 + ‖X a‖)
    have e := sb1w_32 (X a)
    calc ρ r (X a) * (1 + ‖X a‖) ≤ C3 * sb1w ((d : ℝ) + 3) (X a) * (1 + ‖X a‖) := this
      _ = C3 * sb1w ((d : ℝ) + 2) (X a) := by rw [mul_assoc, e]
  have h2 := sb1_prod_erase_le H hr a X
  have hP0 : 0 ≤ ∏ l ∈ Finset.univ.erase a, ρ r (X l) := Finset.prod_nonneg fun l _ => (H.pos r hr _).le
  have hCN : C3 ^ N = C3 * C3 ^ (N - 1) := by
    rw [← pow_succ']; congr 1; have := a.pos; omega
  calc (∏ l, ρ r (X l)) * (1 + ‖X a‖)
      = (ρ r (X a) * (1 + ‖X a‖)) * ∏ l ∈ Finset.univ.erase a, ρ r (X l) := by
        rw [← Finset.mul_prod_erase Finset.univ (fun l => ρ r (X l)) (Finset.mem_univ a)]; ring
    _ ≤ (C3 * sb1w ((d : ℝ) + 2) (X a)) * (C3 ^ (N - 1) * ∏ l ∈ Finset.univ.erase a, sb1w ((d : ℝ) + 2) (X l)) :=
        mul_le_mul h1 h2 hP0 (mul_nonneg hC3 (sb1w_pos _ _).le)
    _ = C3 ^ N * ∏ l, sb1w ((d : ℝ) + 2) (X l) := by
        rw [hCN, ← Finset.mul_prod_erase Finset.univ (fun l => sb1w ((d : ℝ) + 2) (X l)) (Finset.mem_univ a)]
        ring

/-- the bound of `ċ` -/
def sb1Cdot (d : ℕ) (D : Whole.WholeDyn d) (B C C3 : ℝ) : ℝ :=
  (sb1CA D B C C3 * (1 + sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)) +
      C3 * sb1CGd d D.s (sb1CA D B C C3)) * ∫ x : Euc d, sb1w ((d : ℝ) + 1) x

/-- the bound constant of `Wdot` -/
def sb1Kb (d : ℕ) (D : Whole.WholeDyn d) (B C C3 β : ℝ) (N : ℕ) : ℝ :=
  sb1Cw d D.s C3 β N * (N * sb1CA D B C C3 * C3 ^ (N - 1)) +
    sb1Cw d D.s C3 β N * (β * N * ((sb1CGd d D.s (sb1CA D B C C3) + (1 / 2) * sb1Cdot d D B C C3) * C3 ^ N))

theorem sb1_Wdot_bound (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) {β : ℝ} (hβ : 0 ≤ β) (hN : 1 ≤ N)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (X : Whole.EucConfig d N) :
    |sb1Wdot D ρ k β N r X| ≤ sb1Kb d D B C C3 β N * ∏ l, sb1w ((d : ℝ) + 2) (X l) := by
  have hd := H.tr.hd
  have hCA := H.CA_nonneg
  have hC3 := H.C3nn
  have hCw := sb1Cw_pos d D.s C3 β N
  have hCGd0 : 0 ≤ sb1CGd d D.s (sb1CA D B C C3) := sb1CGd_nonneg D.s hCA
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hBd0 : 0 ≤ ∏ l, sb1w ((d : ℝ) + 2) (X l) := Finset.prod_nonneg fun l _ => (sb1w_pos _ _).le
  have hE0 := Real.exp_pos (-β * N * sb1En k (ρ r) X)
  have hEle := H.E_le hk hN hβ hr X
  have hP0 : 0 ≤ ∏ i, ρ r (X i) := Finset.prod_nonneg fun l _ => (H.pos r hr _).le
  have hCdot0 : 0 ≤ sb1Cdot d D B C C3 := by
    have R := H.rho hd hr
    have h1 := sb1CG_nonneg (d := d) (s := D.s) R
    have h2 : 0 ≤ ∫ x : Euc d, sb1w ((d : ℝ) + 1) x := integral_nonneg fun x => (sb1w_pos _ _).le
    unfold sb1Cdot
    positivity
  -- part 1
  have p1 : |∑ i, sb1A D (ρ r) (X i) * ∏ l ∈ Finset.univ.erase i, ρ r (X l)| ≤
      N * (sb1CA D B C C3 * C3 ^ (N - 1) * (∏ l, sb1w ((d : ℝ) + 2) (X l))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |sb1A D (ρ r) (X i) * ∏ l ∈ Finset.univ.erase i, ρ r (X l)|
        = ∑ i, |sb1A D (ρ r) (X i)| * ∏ l ∈ Finset.univ.erase i, ρ r (X l) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg fun l _ => (H.pos r hr _).le)]
      _ ≤ ∑ _i : Fin N, (sb1CA D B C C3 * C3 ^ (N - 1) * (∏ l, sb1w ((d : ℝ) + 2) (X l))) :=
          Finset.sum_le_sum fun i _ => sb1_cfg_bound H hr i hCA (fun y => H.A_le hr y) X
      _ = N * (sb1CA D B C C3 * C3 ^ (N - 1) * (∏ l, sb1w ((d : ℝ) + 2) (X l))) := by simp
  -- part 2
  have hGd : ∀ a, |sb1Gd D ρ k r (X a)| ≤ sb1CGd d D.s (sb1CA D B C C3) * (1 + ‖X a‖) := fun a => by
    have := (sb1_Gd_facts H hk hr (X a)).2
    exact this
  have hcd := sb1_cdot_bound H hk hr
  have hEnDot : |sb1EnDot D ρ k N r X| ≤ (1 / (N : ℝ)) * ∑ a, sb1CGd d D.s (sb1CA D B C C3) * (1 + ‖X a‖) +
      (1 / 2) * sb1Cdot d D B C C3 := by
    unfold sb1EnDot
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_neg, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => hGd a))
        (by positivity)
    · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact mul_le_mul_of_nonneg_left hcd (by norm_num)
  have p2 : (∏ i, ρ r (X i)) * |sb1EnDot D ρ k N r X| ≤
      (sb1CGd d D.s (sb1CA D B C C3) + (1 / 2) * sb1Cdot d D B C C3) * C3 ^ N * (∏ l, sb1w ((d : ℝ) + 2) (X l)) := by
    have hPP := sb1_prod_le H hr X
    calc (∏ i, ρ r (X i)) * |sb1EnDot D ρ k N r X|
        ≤ (∏ i, ρ r (X i)) * ((1 / (N : ℝ)) * ∑ a, sb1CGd d D.s (sb1CA D B C C3) * (1 + ‖X a‖) +
            (1 / 2) * sb1Cdot d D B C C3) := mul_le_mul_of_nonneg_left hEnDot hP0
      _ = (1 / (N : ℝ)) * ∑ a, sb1CGd d D.s (sb1CA D B C C3) * ((∏ i, ρ r (X i)) * (1 + ‖X a‖)) +
            (1 / 2) * sb1Cdot d D B C C3 * (∏ i, ρ r (X i)) := by
          have hS : (∏ i, ρ r (X i)) * ∑ a, sb1CGd d D.s (sb1CA D B C C3) * (1 + ‖X a‖) =
              ∑ a, sb1CGd d D.s (sb1CA D B C C3) * ((∏ i, ρ r (X i)) * (1 + ‖X a‖)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun a _ => by ring
          rw [mul_add, show (∏ i, ρ r (X i)) * ((1 / (N : ℝ)) * ∑ a, sb1CGd d D.s (sb1CA D B C C3) * (1 + ‖X a‖)) =
            (1 / (N : ℝ)) * ((∏ i, ρ r (X i)) * ∑ a, sb1CGd d D.s (sb1CA D B C C3) * (1 + ‖X a‖)) by ring, hS]
          ring
      _ ≤ (1 / (N : ℝ)) * ∑ _a : Fin N, sb1CGd d D.s (sb1CA D B C C3) * (C3 ^ N * (∏ l, sb1w ((d : ℝ) + 2) (X l))) +
            (1 / 2) * sb1Cdot d D B C C3 * (C3 ^ N * (∏ l, sb1w ((d : ℝ) + 2) (X l))) := by
          refine add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ =>
            mul_le_mul_of_nonneg_left (sb1_prod_mul_le H hr a X) hCGd0) (by positivity)) ?_
          exact mul_le_mul_of_nonneg_left hPP (by positivity)
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hNne : (N : ℝ) ≠ 0 := hn0.ne'
          rw [← mul_assoc (1 / (N : ℝ)) (N : ℝ), one_div_mul_cancel hNne, one_mul]
          ring
  unfold sb1Wdot sb1Kb
  have hβN : 0 ≤ β * N := by positivity
  have q1 : |(∑ i, sb1A D (ρ r) (X i) * ∏ l ∈ Finset.univ.erase i, ρ r (X l)) *
      Real.exp (-β * N * sb1En k (ρ r) X)| ≤ sb1Cw d D.s C3 β N * (N * sb1CA D B C C3 * C3 ^ (N - 1)) * (∏ l, sb1w ((d : ℝ) + 2) (X l)) := by
    rw [abs_mul, abs_of_pos hE0]
    calc |∑ i, sb1A D (ρ r) (X i) * ∏ l ∈ Finset.univ.erase i, ρ r (X l)| * Real.exp (-β * N * sb1En k (ρ r) X)
        ≤ (N * (sb1CA D B C C3 * C3 ^ (N - 1) * (∏ l, sb1w ((d : ℝ) + 2) (X l)))) * sb1Cw d D.s C3 β N :=
          mul_le_mul p1 hEle hE0.le (by positivity)
      _ = _ := by ring
  have q2 : |(∏ i, ρ r (X i)) * (Real.exp (-β * N * sb1En k (ρ r) X) * ((-β * N) * sb1EnDot D ρ k N r X))| ≤
      sb1Cw d D.s C3 β N * (β * N * ((sb1CGd d D.s (sb1CA D B C C3) + (1 / 2) * sb1Cdot d D B C C3) * C3 ^ N)) * (∏ l, sb1w ((d : ℝ) + 2) (X l)) := by
    have habs : |(-β * (N : ℝ))| = β * N := by rw [abs_mul, abs_neg, abs_of_nonneg hβ, Nat.abs_cast]
    rw [abs_mul, abs_of_nonneg hP0, abs_mul, abs_of_pos hE0, abs_mul, habs]
    calc (∏ i, ρ r (X i)) * (Real.exp (-β * N * sb1En k (ρ r) X) * (β * N * |sb1EnDot D ρ k N r X|))
        = Real.exp (-β * N * sb1En k (ρ r) X) * (β * N) * ((∏ i, ρ r (X i)) * |sb1EnDot D ρ k N r X|) := by ring
      _ ≤ sb1Cw d D.s C3 β N * (β * N) *
            ((sb1CGd d D.s (sb1CA D B C C3) + (1 / 2) * sb1Cdot d D B C C3) * C3 ^ N * (∏ l, sb1w ((d : ℝ) + 2) (X l))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hEle hβN) p2 (by positivity) (by positivity)
      _ = _ := by ring
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ sb1Cw d D.s C3 β N * (N * sb1CA D B C C3 * C3 ^ (N - 1)) * (∏ l, sb1w ((d : ℝ) + 2) (X l)) +
        sb1Cw d D.s C3 β N * (β * N * ((sb1CGd d D.s (sb1CA D B C C3) + (1 / 2) * sb1Cdot d D B C C3) * C3 ^ N)) * (∏ l, sb1w ((d : ℝ) + 2) (X l)) :=
        add_le_add q1 q2
    _ = _ := by ring

theorem sb1_Wdot_meas (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {β : ℝ}
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    Measurable (fun X : Whole.EucConfig d N => sb1Wdot D ρ k β N r X) := by
  have hρc := H.tr.cont hr
  have hEc : Continuous (fun X : Whole.EucConfig d N => Real.exp (-β * N * sb1En k (ρ r) X)) :=
    Real.continuous_exp.comp (continuous_const.mul (sb1_En_cont H hk hR hr))
  have hPc : ∀ i : Fin N, Continuous (fun X : Whole.EucConfig d N => ∏ l ∈ Finset.univ.erase i, ρ r (X l)) :=
    fun i => continuous_finset_prod _ fun l _ => hρc.comp (continuous_apply l)
  have hEnDot : Measurable (fun X : Whole.EucConfig d N => sb1EnDot D ρ k N r X) := by
    unfold sb1EnDot
    exact (measurable_const.mul (Finset.measurable_sum _ fun a _ =>
      (sb1_Gd_meas H hk hr).comp (measurable_pi_apply a))).add measurable_const
  unfold sb1Wdot
  refine ((Finset.measurable_sum _ fun i _ => ?_).mul hEc.measurable).add
    ((continuous_finset_prod _ fun i _ => hρc.comp (continuous_apply i)).measurable.mul
      (hEc.measurable.mul (measurable_const.mul hEnDot)))
  exact ((H.A_cont hr).measurable.comp (measurable_pi_apply i)).mul (hPc i).measurable

theorem sb1_Wf_bound (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) {β : ℝ} (hβ : 0 ≤ β) (hN : 1 ≤ N)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (X : Whole.EucConfig d N) :
    |sb1Wf k β N ρ r X| ≤ sb1Cw d D.s C3 β N * C3 ^ N * ∏ l, sb1w ((d : ℝ) + 2) (X l) := by
  unfold sb1Wf
  have hE0 := Real.exp_pos (-β * N * sb1En k (ρ r) X)
  have hP0 : 0 ≤ ∏ i, ρ r (X i) := Finset.prod_nonneg fun l _ => (H.pos r hr _).le
  rw [abs_mul, abs_of_nonneg hP0, abs_of_pos hE0]
  calc (∏ i, ρ r (X i)) * Real.exp (-β * N * sb1En k (ρ r) X)
      ≤ (C3 ^ N * ∏ l, sb1w ((d : ℝ) + 2) (X l)) * sb1Cw d D.s C3 β N :=
        mul_le_mul (sb1_prod_le H hr X) (H.E_le hk hN hβ hr X) hE0.le
          (mul_nonneg (pow_nonneg H.C3nn _) (Finset.prod_nonneg fun l _ => (sb1w_pos _ _).le))
    _ = _ := by ring

theorem sb1_Wf_cont (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg) {β : ℝ}
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) : Continuous (fun X : Whole.EucConfig d N => sb1Wf k β N ρ r X) :=
  (continuous_finset_prod _ fun i _ => (H.tr.cont hr).comp (continuous_apply i)).mul
    (Real.continuous_exp.comp (continuous_const.mul (sb1_En_cont H hk hR hr)))

theorem sb1_hasDerivAt_K (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T) (hk : Sb1KerU d D.s k) (hR : Sb1KerR d k Lg)
    {β : ℝ} (hβ : 0 ≤ β) (hN : 1 ≤ N) {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => ∫ X : Whole.EucConfig d N, sb1Wf k β N ρ r X)
      (∫ X : Whole.EucConfig d N, sb1Wdot D ρ k β N r₀ X) r₀ := by
  have hd := H.tr.hd
  have hI : Set.Ioo (0 : ℝ) T ∈ 𝓝 r₀ := Ioo_mem_nhds hr₀.1 hr₀.2
  have hIcc : ∀ r ∈ Set.Ioo (0 : ℝ) T, r ∈ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1.le, hr.2.le⟩
  have hBd : Integrable (fun X : Whole.EucConfig d N => ∏ l, sb1w ((d : ℝ) + 2) (X l)) volume :=
    Integrable.fintype_prod (fun _ => sb1w_int hd (p := (d : ℝ) + 2) (by linarith))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Whole.EucConfig d N)))
    (F := fun r X => sb1Wf k β N ρ r X) (F' := fun r X => sb1Wdot D ρ k β N r X) (x₀ := r₀) (s := Set.Ioo 0 T)
    (bound := fun X => sb1Kb d D B C C3 β N * ∏ l, sb1w ((d : ℝ) + 2) (X l)) hI ?_ ?_ ?_ ?_ (hBd.const_mul _) ?_
  · exact key.2
  · filter_upwards [hI] with r hr
    exact (sb1_Wf_cont H hk hR (hIcc r hr)).aestronglyMeasurable
  · exact sb1_cfg_int_of_bound hd (sb1_Wf_cont H hk hR (hIcc r₀ hr₀)).aestronglyMeasurable
      (fun X => sb1_Wf_bound H hk hβ hN (hIcc r₀ hr₀) X)
  · exact (sb1_Wdot_meas H hk hR (hIcc r₀ hr₀)).aestronglyMeasurable
  · exact Eventually.of_forall fun X r hr => by
      rw [Real.norm_eq_abs]; exact sb1_Wdot_bound H hk hβ hN (hIcc r hr) X
  · exact Eventually.of_forall fun X r hr => sb1_hasDerivAt_Wf H hT hk hr X

end KDeriv

end HRS.MS.MfeConf
