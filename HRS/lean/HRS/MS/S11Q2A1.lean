import HRS.MS.S113Q2

/-!
# S11.3 Q-regularity (worker S11Q2), A1: dominated convergence for the Steklov regularization

Pointwise convergence and uniform bounds (for `k ≥ k₀`, `τ ∈ [0,T]`) of the two spatial integrals
`∫ N_k r_k^p` and `∫ q_k r_k^p log r_k` of the right-hand side `s113b_Gp` along the Steklov averages `q_k`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set intervalIntegral

namespace HRS.MS.S11Q2

open HRS.MS.S113X2B HRS.MS.S113X2C HRS.MS.S113Q

/-- Dominated convergence for `∫ w_k ψ(u/q_k)` with `u` supported in the compact `K`, `ψ 0 = 0`. -/
theorem s11q2_dct_ratio {n : ℕ} {K : Set (s113b_E n)} (hK : IsCompact K) {u : s113b_E n → ℝ}
    (hum : Measurable u) (hu0 : ∀ x, 0 ≤ u x) (huK : ∀ x, x ∉ K → u x = 0)
    {wk : ℕ → s113b_E n → ℝ} {w : s113b_E n → ℝ} {qk : ℕ → s113b_E n → ℝ} {q : s113b_E n → ℝ}
    {ψ : ℝ → ℝ} {W Z Cψ qmin : ℝ} {k0 : ℕ} (hwm : ∀ k, Measurable (wk k)) (hqm : ∀ k, Measurable (qk k))
    (hwb : ∀ k, k0 ≤ k → ∀ x ∈ K, |wk k x| ≤ W) (hqb : ∀ k, k0 ≤ k → ∀ x ∈ K, qmin ≤ qk k x)
    (hqmin : 0 < qmin) (hZ : ∀ k, k0 ≤ k → ∀ x ∈ K, u x / qk k x ≤ Z)
    (hψm : Measurable ψ) (hψ0 : ψ 0 = 0) (hψb : ∀ z ∈ Icc (0 : ℝ) Z, |ψ z| ≤ Cψ)
    (hψc : ∀ z : ℝ, 0 < z → ContinuousAt ψ z)
    (hwl : ∀ x, Tendsto (fun k => wk k x) atTop (𝓝 (w x)))
    (hql : ∀ x, Tendsto (fun k => qk k x) atTop (𝓝 (q x))) (hq : ∀ x, 0 < q x) :
    Tendsto (fun k => ∫ x, wk k x * ψ (u x / qk k x)) atTop (𝓝 (∫ x, w x * ψ (u x / q x))) ∧
      ∀ k, k0 ≤ k → |∫ x, wk k x * ψ (u x / qk k x)| ≤ (W * Cψ) * (volume K).toReal := by
  have key := s113q_dct_K hK (F := fun k x => wk k x * ψ (u x / qk k x)) (f := fun x => w x * ψ (u x / q x))
    (C := W * Cψ) (k0 := k0) (fun k => ((hwm k).mul (hψm.comp (hum.div (hqm k)))).aestronglyMeasurable) ?_ ?_
  · simpa only [Real.norm_eq_abs] using key
  · intro k hk x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
      have hqp : 0 < qk k x := lt_of_lt_of_le hqmin (hqb k hk x hx)
      have hr : u x / qk k x ∈ Icc (0 : ℝ) Z := ⟨div_nonneg (hu0 x) hqp.le, hZ k hk x hx⟩
      exact mul_le_mul (hwb k hk x hx) (hψb _ hr) (abs_nonneg _) ((abs_nonneg _).trans (hwb k hk x hx))
    · rw [indicator_of_notMem hx]
      simp [huK x hx, hψ0]
  · intro x
    rcases (hu0 x).eq_or_lt with h | h
    · simp [← h, hψ0]
    · have h1 : Tendsto (fun k => u x / qk k x) atTop (𝓝 (u x / q x)) :=
        tendsto_const_nhds.div (hql x) (hq x).ne'
      exact (hwl x).mul (((hψc _ (div_pos h (hq x))).tendsto).comp h1)

theorem s11q2_Nk_eq {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ} {T : ℝ} {u : ℝ → s113b_E n → ℝ}
    {K G : Set (s113b_E n)} {B : ℝ} (hD : s113q_Data ν b q T u K G B) {d1 : ℝ × s113b_E n → ℝ}
    {d2 : ℝ × s113b_E n → s113b_E n →L[ℝ] ℝ} {d3 : ℝ × s113b_E n → s113b_E n →L[ℝ] s113b_E n →L[ℝ] ℝ}
    (hd : s113q_C12Data (fun z : ℝ × s113b_E n => q z.1 z.2) d1 d2 d3) (k : ℕ) (τ : ℝ) (x : s113b_E n) :
    s113b_N ν b (s113q_qk q k) τ x = s113q_Nf ν b (s113q_S (s113q_eta k) (fun z : ℝ × s113b_E n => q z.1 z.2) (τ, x))
      (s113q_S (s113q_eta k) d1 (τ, x)) (s113q_S (s113q_eta k) d2 (τ, x)) (s113q_S (s113q_eta k) d3 (τ, x)) x :=
  s113q_N_eq hD.hb (hd.steklov_data (s113q_eta k)) τ x

theorem s11q2_Nk_tendsto {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ} {T : ℝ} {u : ℝ → s113b_E n → ℝ}
    {K G : Set (s113b_E n)} {B : ℝ} (hD : s113q_Data ν b q T u K G B) (τ : ℝ) (x : s113b_E n) :
    Tendsto (fun k => s113b_N ν b (s113q_qk q k) τ x) atTop (𝓝 (s113b_N ν b q τ x)) := by
  obtain ⟨d1, d2, d3, hd⟩ := hD.hq
  rw [s113q_N_eq hD.hb hd τ x]
  simp only [s11q2_Nk_eq hD hd]
  exact s113q_Nf_tendsto ν b x (s113q_S_tendsto_pt hd.cQ (τ, x)) (s113q_S_tendsto_pt hd.c1 (τ, x))
    (s113q_S_tendsto_pt (W := s113b_E n →L[ℝ] ℝ) hd.c2 (τ, x))
    (s113q_S_tendsto_pt (W := s113b_E n →L[ℝ] s113b_E n →L[ℝ] ℝ) hd.c3 (τ, x))

end HRS.MS.S11Q2

end
