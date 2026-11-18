import HRS.MC.D1TAux2

/-!
# Packet D1T, auxiliary file 3: the heat-damped function of `t`, its bounds and its limit.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators

namespace HRS.MC.D1T

open HRS

variable {d : ℕ}

/-- `G_ε(t) = ∑_{k ≠ 0} e^{-ε|k|²} ψ̂(tk)² cos(2π k·x)`. -/
def d1tG (ψ : Euc d → ℝ) (x : Torus d) (ε t : ℝ) : ℝ :=
  ∑' k : Lattice d, Real.exp (-ε * Lattice.enorm k ^ 2) * d1tB ψ t k * Torus.cosMode k x

theorem d1t_hat_bdd {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Euc d, fdlPsiHat ψ ξ ^ 2 ≤ C := by
  obtain ⟨C0, hC0, h⟩ := Per.per_psiHat_decay hψ 0
  refine ⟨C0 ^ 2, by positivity, fun ξ => ?_⟩
  have h1 : |fdlPsiHat ψ ξ| ≤ C0 := by simpa using h ξ
  calc fdlPsiHat ψ ξ ^ 2 = |fdlPsiHat ψ ξ| ^ 2 := (sq_abs _).symm
    _ ≤ C0 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2

theorem d1tB_le {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t k, d1tB ψ t k ≤ C := by
  obtain ⟨C, hC, h⟩ := d1t_hat_bdd hψ
  refine ⟨C, hC, fun t k => ?_⟩
  unfold d1tB
  split_ifs
  · exact hC
  · exact h _

theorem d1t_term_bound {ψ : Euc d → ℝ} (ε t : ℝ) (x : Torus d) (k : Lattice d) :
    |Real.exp (-ε * Lattice.enorm k ^ 2) * d1tB ψ t k * Torus.cosMode k x| ≤
      Real.exp (-ε * Lattice.enorm k ^ 2) * d1tB ψ t k := by
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (d1tB_nonneg ψ t k)]
  exact mul_le_of_le_one_right (mul_nonneg (Real.exp_pos _).le (d1tB_nonneg ψ t k))
    (abs_cosMode_le k x)

theorem d1t_term_summable {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {ε : ℝ} (hε : 0 < ε) (t : ℝ)
    (x : Torus d) :
    Summable fun k : Lattice d =>
      Real.exp (-ε * Lattice.enorm k ^ 2) * d1tB ψ t k * Torus.cosMode k x := by
  obtain ⟨C, hC0, hC⟩ := d1tB_le hψ
  refine Summable.of_norm_bounded ((summable_gauss_lattice d ε hε).mul_left C) fun k => ?_
  rw [Real.norm_eq_abs]
  refine (d1t_term_bound ε t x k).trans ?_
  rw [mul_comm C]
  gcongr
  exact hC t k

theorem d1tG_continuous {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {ε : ℝ} (hε : 0 < ε) (x : Torus d) :
    Continuous fun t => d1tG ψ x ε t := by
  obtain ⟨C, hC0, hC⟩ := d1tB_le hψ
  unfold d1tG
  refine continuous_tsum (u := fun k : Lattice d => C * Real.exp (-ε * Lattice.enorm k ^ 2))
    (fun k => ?_) ((summable_gauss_lattice d ε hε).mul_left C) (fun k t => ?_)
  · by_cases hk : k = 0
    · simp only [d1tB, hk, if_true]
      simp only [mul_zero, zero_mul]
      exact continuous_const
    · simp only [d1tB, hk, if_false]
      have : Continuous fun t : ℝ => fdlPsiHat ψ (t • Lattice.toEuc k) :=
        (D1F.d1f_hat_cont hψ).comp (continuous_id.smul continuous_const)
      fun_prop
  · rw [Real.norm_eq_abs]
    refine (d1t_term_bound ε t x k).trans ?_
    rw [mul_comm C]
    gcongr
    exact hC t k

theorem d1tG_tendsto {ψ : Euc d → ℝ} (hd : 1 ≤ d) (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t)
    (x : Torus d) :
    Tendsto (fun ε => d1tG ψ x ε t) (𝓝[>] 0) (𝓝 (Per.perQ ψ t x)) := by
  obtain ⟨K, -, hK⟩ := d1t_tail hψ
  have hlim : Tendsto (fun ε : ℝ => ∑' k : Lattice d,
      Real.exp (-ε * Lattice.enorm k ^ 2) * d1tB ψ t k * Torus.cosMode k x) (𝓝[>] (0 : ℝ))
      (𝓝 (∑' k : Lattice d, d1tB ψ t k * Torus.cosMode k x)) :=
    tendsto_tsum_of_dominated_convergence (bound := d1tB ψ t) (hK t ht).1 (fun k => ?_) ?_
  · rw [(d1t_inversion hd hψ ht x).tsum_eq] at hlim
    exact hlim
  · have hc : Continuous fun ε : ℝ => Real.exp (-ε * Lattice.enorm k ^ 2) * d1tB ψ t k * Torus.cosMode k x := by
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with ε hε k
    rw [Real.norm_eq_abs]
    refine (d1t_term_bound ε t x k).trans (mul_le_of_le_one_left (d1tB_nonneg ψ t k) ?_)
    exact Real.exp_le_one_iff.mpr (by have hε' : 0 < ε := hε; nlinarith [mul_nonneg hε'.le (sq_nonneg (Lattice.enorm k))])

end HRS.MC.D1T
