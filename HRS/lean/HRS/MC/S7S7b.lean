import HRS.MC.S7S7bAux13
import HRS.MC.S7S7bAux4

/-!
# Packet `s7_S7b_weighted_moments` (relocation of `HRS.MC.Sec7.s7_S7b_weighted_moments`)

Moments of the weighted statistics of Proposition 7.7, uniformly in `N >= 1` and the modes `k, l`:
* (i) `E |sqrt N (A_{N,kl} - E A_{N,kl})|^{2q} <= C (b_k b_l)^{2q}`: B7 (`sed_B7_lln`, homogeneous in the sup norm)
  for the bounded observable `w_{kl} = v_k . grad phi_l`, `||w_{kl}||_inf <= C b_k b_l`, plus the uniform mean bias
  (`s7b_Y_moment`);
* (ii) for `0 < gamma`: `E |B_{N,k}|^{2q} <= C b_k^{2q}` from the exponential pair estimate
  (`perturbed_pressure`, `N delta_N = 1`) with the envelope `|h_v| <= K (sum L_j)(g + c)` (`s7b_B_moment`);
* (iii) the mean bias `|E A_{N,kl} - mu(phi_l a_k)| <= C b_k b_l / N`, via the uniform bias
  `|E mu_N(w) - mu(w)| <= C sup|w| / N` (`s7b_bias_uniform`: Stein identity with the Poisson solution of `r_w` in
  `H^1`, `||h_v||_{L^2(mu x mu)} <= C ||v||_{H^1}` by the translation estimate, Holder transfer of the `L^2`
  energy bound).  Note that `v_k` is only controlled in `C^1` by `s7_ModeData`; the proof uses only `||w||_inf`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7b

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ}

theorem s7_S7b_weighted_moments_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (r : ℝ)
    (hr : r = 2 * (d : ℝ) + 6) {γ : ℝ} (hγ : 0 ≤ γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀) (q : ℕ) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ k l : NonzeroLattice d,
      (∫ X, |sed_Y (sed_Q d s N γ ρ) (sed_drift (v k) (s7_phi r l)) X| ^ (2 * q)
          ∂(sed_Q d s N γ ρ) ≤ C * (s7_b k * s7_b l) ^ (2 * q)) ∧
      (0 < γ → Integrable (fun X => |sed_B d s ρ γ (v k) X| ^ (2 * q)) (sed_Q d s N γ ρ) ∧
        ∫ X, |sed_B d s ρ γ (v k) X| ^ (2 * q) ∂(sed_Q d s N γ ρ) ≤ C * s7_b k ^ (2 * q)) ∧
      |∫ X, sed_A (v k) (s7_phi r l) X ∂(sed_Q d s N γ ρ) - s7_Cmode r ρ a l k| ≤
        C * s7_b k * s7_b l / N := by
  have hb : ∀ k j, Torus.cbNorm 1 (v k j) ≤ C₀ * s7_b k := hmode.bound_v
  have hbpos : ∀ k : NonzeroLattice d, 0 < s7_b k := fun k => by
    unfold s7_b; have := Torus.jp_pos k.1; positivity
  set Cd : ℝ := d * max C₀ 0 * (2 * Real.sqrt 2) with hCd
  have hCd0 : 0 ≤ Cd := by positivity
  -- the observable `w_{kl}`
  have hws : ∀ k l, Torus.IsSmooth (sed_drift (v k) (s7_phi r l)) := fun k l =>
    s7b_drift_smooth (hmode.smooth_v k) (HRS.MC.Sec7.S7a.s7a_phi_smooth r l)
  have hwb : ∀ k l x, |sed_drift (v k) (s7_phi r l) x| ≤ Cd * (s7_b k * s7_b l) := fun k l x =>
    s7b_drift_bound hr hmode.smooth_v hb k l x
  -- (i)
  obtain ⟨C1, hC1, h1⟩ := s7b_Y_moment hd hs0 hs hγ hρ q
  -- (iii)
  obtain ⟨Cu, hCu0, hCu⟩ := s7b_bias_uniform hd hs0 hs hγ hρ
  -- (ii)
  have h2 : ∃ C2 : ℝ, 0 ≤ C2 ∧ (0 < γ → ∀ N : ℕ, 1 ≤ N → ∀ k : NonzeroLattice d,
      Integrable (fun X => |sed_B d s ρ γ (v k) X| ^ (2 * q)) (sed_Q d s N γ ρ) ∧
        ∫ X, |sed_B d s ρ γ (v k) X| ^ (2 * q) ∂(sed_Q d s N γ ρ) ≤ C2 * s7_b k ^ (2 * q)) := by
    rcases hγ.eq_or_lt with h0 | hpos
    · exact ⟨0, le_rfl, fun h => absurd h (by rw [← h0]; exact lt_irrefl _)⟩
    · obtain ⟨K, M, hK0, hM0, hBm⟩ := s7b_B_moment hd hs0 hs hpos hρ q
      set C₀' : ℝ := max C₀ 1 with hC₀'
      have hC₀'pos : 0 < C₀' := lt_of_lt_of_le one_pos (le_max_right _ _)
      refine ⟨M * ((K + 1) * (d * C₀')) ^ (2 * q), by positivity, fun _ N hN k => ?_⟩
      have hLip : ∀ j : Fin d, HRS.KernelGrad.IsLipschitz (C₀' * s7_b k) (v k j) := by
        intro j x y
        have h := HRS.PDE.R2Aux.isLipschitz_of_cbNorm
          (HRS.Q66.q66_isCk_of_smooth (hmode.smooth_v k j) 1) x y
        refine h.trans ?_
        have : Torus.cbNorm 1 (v k j) ≤ C₀' * s7_b k :=
          (hb k j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hbpos k).le)
        exact mul_le_mul_of_nonneg_right this (HRS.KernelGrad.tdist_nonneg x y)
      have hsum : ∑ _j : Fin d, C₀' * s7_b k = d * (C₀' * s7_b k) := by simp
      have hΛ : 0 < (K + 1) * (d * (C₀' * s7_b k)) := by
        have : (0 : ℝ) < d := by
          have : (2 : ℝ) ≤ d := by exact_mod_cast hd
          linarith
        have := hbpos k
        positivity
      obtain ⟨hI, hB⟩ := hBm (v k) (fun _ => C₀' * s7_b k) (hmode.smooth_v k)
        (fun _ => (mul_pos hC₀'pos (hbpos k)).le) hLip ((K + 1) * (d * (C₀' * s7_b k))) hΛ
        (by
          rw [hsum]
          have : 0 ≤ d * (C₀' * s7_b k) := by have := hbpos k; positivity
          nlinarith) N hN
      refine ⟨hI, hB.trans ?_⟩
      have : ((K + 1) * (d * (C₀' * s7_b k))) ^ (2 * q) =
          ((K + 1) * (d * C₀')) ^ (2 * q) * s7_b k ^ (2 * q) := by
        rw [← mul_pow]; congr 1; ring
      rw [this]; ring_nf; exact le_rfl
  obtain ⟨C2, hC20, h2⟩ := h2
  refine ⟨max (max (C1 * Cd ^ (2 * q)) C2) (Cu * Cd), fun N hN k l => ⟨?_, ?_, ?_⟩⟩
  · -- (i)
    have h := h1 _ (Cd * (s7_b k * s7_b l)) (hws k l) (hwb k l) N hN
    refine h.trans ?_
    rw [mul_pow, ← mul_assoc]
    have : 0 ≤ (s7_b k * s7_b l) ^ (2 * q) := by
      have := hbpos k; have := hbpos l; positivity
    exact mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) this
  · -- (ii)
    intro hpos
    obtain ⟨hI, hB⟩ := h2 hpos N hN k
    refine ⟨hI, hB.trans ?_⟩
    have : 0 ≤ s7_b k ^ (2 * q) := by have := hbpos k; positivity
    exact mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _)) this
  · -- (iii)
    have hmean := s7b_drift_mean hd hs0 hs hγ hρ r hmode k l
    have h := hCu _ (Cd * (s7_b k * s7_b l)) (hws k l) (hwb k l) N hN
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN
    have e : ∫ X, sed_A (v k) (s7_phi r l) X ∂(sed_Q d s N γ ρ) =
        ∫ X, pair (empirical X) (sed_drift (v k) (s7_phi r l)) ∂(sed_Q d s N γ ρ) := rfl
    rw [e, ← hmean]
    refine h.trans ?_
    have hbb : 0 ≤ s7_b k * s7_b l := by have := hbpos k; have := hbpos l; positivity
    have hle : Cu * Cd ≤ max (max (C1 * Cd ^ (2 * q)) C2) (Cu * Cd) := le_max_right _ _
    calc Cu * (Cd * (s7_b k * s7_b l)) / N = ((Cu * Cd) * (s7_b k * s7_b l)) / N := by ring
      _ ≤ ((max (max (C1 * Cd ^ (2 * q)) C2) (Cu * Cd)) * (s7_b k * s7_b l)) / N := by
          apply div_le_div_of_nonneg_right _ hNp.le
          exact mul_le_mul_of_nonneg_right hle hbb
      _ = _ := by ring

end HRS.MC.Sec7.S7b

end
