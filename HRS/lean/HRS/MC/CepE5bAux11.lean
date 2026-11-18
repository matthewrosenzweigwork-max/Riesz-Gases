import HRS.MC.CepE5bAux6
import HRS.MC.CepE4

/-!
# Packet CEPE5B, auxiliary 11: deterministic facts about the envelope `Φ_n` used in the Itô argument

`G_n z = n (z - J_n z)`, `D Φ_n = ⟨G_n, ·⟩`, growth of `G_n` and `Φ_n`, the trace function `tr_n z = ∑_i D²Φ_n(e_i, e_i)`
is continuous with `0 ≤ tr_n ≤ n N`.
-/

open Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5b

open HRS.MC.Cepa
open HRS.MC.CepE4 (e4_rho e4_lip_growth)

variable {N : ℕ} {a : ℝ} {J : ℝ → Ch N → Ch N}

/-- The Yosida force. -/
def e5b_G (J : ℝ → Ch N → Ch N) (n : ℝ) (z : Ch N) : Ch N := n • (z - J n z)

/-- The Hessian trace of the envelope. -/
def e5b_tr (a : ℝ) (N : ℕ) (J : ℝ → Ch N → Ch N) (n : ℝ) (z : Ch N) : ℝ :=
  ∑ i : Fin N, fderiv ℝ (fderiv ℝ (e5b_Pn a N J n)) z (e5b_e i) (e5b_e i)

theorem e5b_rho_mem : e4_rho N ∈ cep_Alcove N := by
  have hN : ∀ k : Fin N, (0 : ℝ) < N := fun k => by
    have := k.2
    exact_mod_cast (by omega : 0 < N)
  constructor
  · intro k l hkl
    have hNp := hN k
    have : ((k : ℕ) : ℝ) < ((l : ℕ) : ℝ) := by exact_mod_cast hkl
    simp only [e4_rho]
    exact div_lt_div_of_pos_right this hNp
  · intro k l
    have hNp := hN k
    have h1 : ((l : ℕ) : ℝ) < N := by exact_mod_cast l.2
    have h2 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) / N := by positivity
    simp only [e4_rho]
    have : ((l : ℕ) : ℝ) / N < 1 := (div_lt_one hNp).2 h1
    linarith

theorem e5b_fderiv_apply (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (x v : Ch N) :
    fderiv ℝ (e5b_Pn a N J n) x v = inner ℝ (e5b_G J n x) v := by
  rw [e5b_fderiv_Pn ha hJ hn]
  rfl

theorem e5b_G_growth (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    ‖e5b_G J n z‖ ≤ ‖e5b_G J n 0‖ + n * ‖z‖ := by
  have h := e4_lip_growth (hJ.lip n hn) z
  rw [Real.coe_toNNReal _ hn.le] at h
  exact h

theorem e5b_G_cont (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) : Continuous (e5b_G J n) :=
  (hJ.lip n hn).continuous

theorem e5b_tr_nonneg (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    0 ≤ e5b_tr a N J n z :=
  Finset.sum_nonneg fun i _ => (e5b_hess_bounds ha hJ hn z (e5b_e i)).1

theorem e5b_tr_le (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    e5b_tr a N J n z ≤ n * N := by
  unfold e5b_tr
  calc _ ≤ ∑ _i : Fin N, n := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := (e5b_hess_bounds ha hJ hn z (e5b_e i)).2.1
        have hn1 : ‖(e5b_e i : Ch N)‖ = 1 := by simp [e5b_e]
        rw [hn1] at this
        simpa using this
    _ = n * N := by simp [mul_comm]

theorem e5b_tr_cont (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) :
    Continuous (e5b_tr a N J n) := by
  have h2 := e5b_contDiff_Pn ha hJ hn
  have h1 : ContDiff ℝ 1 (fderiv ℝ (e5b_Pn a N J n)) :=
    h2.fderiv_right (by norm_num)
  have hc : Continuous (fderiv ℝ (fderiv ℝ (e5b_Pn a N J n))) := h1.continuous_fderiv one_ne_zero
  unfold e5b_tr
  refine continuous_finset_sum _ fun i _ => ?_
  exact (hc.clm_apply continuous_const).clm_apply continuous_const

/-- Quadratic growth of the envelope. -/
theorem e5b_Pn_abs_le (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    |e5b_Pn a N J n z| ≤ ((a / N) * HRS.MC.CepE2.cepe2_npairs N * Real.log 2 +
      |cep_chamberPot a N (e4_rho N)| + n * ‖e4_rho N‖ ^ 2) + n * ‖z‖ ^ 2 := by
  have hlow := e5b_Pn_lower ha.le hJ hn z
  have hup := e5b_Pn_le ha.le hJ hn z (e5b_rho_mem (N := N))
  have h1 : ‖z - e4_rho N‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖e4_rho N‖ ^ 2 := by
    have h0 : ‖z - e4_rho N‖ ^ 2 ≤ (‖z‖ + ‖e4_rho N‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le z (e4_rho N)) 2
    nlinarith [sq_nonneg (‖z‖ - ‖e4_rho N‖)]
  have h2 : n / 2 * ‖z - e4_rho N‖ ^ 2 ≤ n * ‖z‖ ^ 2 + n * ‖e4_rho N‖ ^ 2 := by
    nlinarith
  have hc0 : 0 ≤ (a / N) * HRS.MC.CepE2.cepe2_npairs N * Real.log 2 := by
    have : 0 ≤ HRS.MC.CepE2.cepe2_npairs N := by unfold HRS.MC.CepE2.cepe2_npairs; positivity
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  have hz := sq_nonneg ‖z‖
  have hr := sq_nonneg ‖e4_rho N‖
  have hnz : 0 ≤ n * ‖z‖ ^ 2 := by positivity
  have hnr : 0 ≤ n * ‖e4_rho N‖ ^ 2 := by positivity
  have hab := abs_nonneg (cep_chamberPot a N (e4_rho N))
  rw [abs_le]
  constructor
  · linarith
  · have := le_abs_self (cep_chamberPot a N (e4_rho N))
    linarith

end HRS.MC.CepE5b
