import HRS.MS.SA16Y4Ct17

/-!
# S.A.16 (SA16Y4) Ct18: local strong continuity in `W^{m',p}`, `m' < m` (abstract form)

`sa16y4_cont_abstract`: if `G : ℝ → W^{m,p}` is bounded and weakly continuous on `[0,t]`, `θ ∈ C_c^∞`, then
`τ ↦ θ (wrep (G τ) - wrep (G τ₀))` is continuous at `τ₀` in `wNormE m' p` for every `m' < m` (Rellich-free route:
derivative gain at fixed mollification scale + weak-to-strong + localized multiplier bound).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution Phase2SA16Transfer

section Ct18
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y4_iota_norm (k : ℕ) : ‖sa16r_iota d k p‖ ≤ 1 :=
  (Classical.choose_spec (jet_restriction_and_finite_lift d k (k + 1) (Nat.le_succ k) p).1).1

theorem sa16y4_cont_abstract (m m' : ℕ) (hmm : m' < m) {θ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) {R₁ : ℝ} (hsupp : tsupport θ ⊆ Metric.closedBall 0 R₁)
    (G : ℝ → WmpSpace d m p) {t Kb : ℝ} (hbd : ∀ τ ∈ Icc (0 : ℝ) t, ‖G τ‖ ≤ Kb)
    (hw : ∀ ℓ : WmpSpace d m p →L[ℝ] ℝ, ContinuousOn (fun τ => ℓ (G τ)) (Icc (0 : ℝ) t))
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ Icc (0 : ℝ) t) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Icc (0 : ℝ) t, |τ - τ₀| < δ →
      wNormE m' p (fun x => θ x * (wrep d m p (G τ) x - wrep d m p (G τ₀) x)) ≤ ENNReal.ofReal ε := by
  obtain ⟨⟨Rs, hRs1, hRsw⟩, -⟩ := jet_restriction_and_finite_lift d (m' + 1) m (by omega) p
  obtain ⟨M, B', hB'0, hMs, hMb⟩ := sa16y4_Mop (p := p) m' hθ hθc hsupp
  have hKb0 : 0 ≤ Kb := (norm_nonneg _).trans (hbd τ₀ hτ₀)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (Fintype.card (WIndex d m') : ℝ) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ Nat.cast_nonneg _
  obtain ⟨C0, hC0def⟩ : ∃ C0 : ℝ, C0 = B' * c * (c * d) * (2 * Kb) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C0 := by rw [hC0def]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (C0 / (ε / 2))
  obtain ⟨R, -, hR⟩ := sa16y4_Rop (d := d) (p := p) m' n
  have hgain : C0 / ((n : ℝ) + 1) < ε / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    have h1 : C0 < ε / 2 * n := by rwa [div_lt_iff₀ (by positivity), mul_comm] at hn
    nlinarith
  obtain ⟨Zp, hZp⟩ : ∃ Zp : ℝ → WmpSpace d (m' + 1) p, ∀ τ, Zp τ = Rs (G τ - G τ₀) := ⟨_, fun _ => rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ → WmpSpace d m' p, ∀ τ, Z τ = sa16r_iota d m' p (Zp τ) := ⟨_, fun _ => rfl⟩
  have hbZp : ∀ τ ∈ Icc (0 : ℝ) t, ‖Zp τ‖ ≤ 2 * Kb := by
    intro τ hτ
    rw [hZp]
    calc ‖Rs (G τ - G τ₀)‖ ≤ ‖Rs‖ * ‖G τ - G τ₀‖ := Rs.le_opNorm _
      _ ≤ 1 * (Kb + Kb) := by
        refine mul_le_mul hRs1 ((norm_sub_le _ _).trans (add_le_add (hbd τ hτ) (hbd τ₀ hτ₀))) (norm_nonneg _) zero_le_one
      _ = 2 * Kb := by ring
  have hbZ : ∀ τ ∈ Icc (0 : ℝ) t, ‖Z τ‖ ≤ 2 * Kb := fun τ hτ => by
    rw [hZ]
    exact ((sa16r_iota d m' p).le_opNorm _).trans (by
      have := sa16y4_iota_norm (d := d) (p := p) m'
      nlinarith [norm_nonneg (Zp τ), hbZp τ hτ])
  have hBev : ∀ᶠ τ in 𝓝[Icc (0 : ℝ) t] τ₀, ‖Z τ‖ ≤ 2 * Kb :=
    eventually_nhdsWithin_of_forall hbZ
  have hwk : ∀ (κ : WIndex d m') {N : EuclideanSpace ℝ (Fin d) → ℝ} (hN : IsCcInfty N),
      Tendsto (fun τ => sa16y4_ellK m' κ hN (Z τ)) (𝓝[Icc (0 : ℝ) t] τ₀) (𝓝 0) := by
    intro κ N hN
    set ℓ : WmpSpace d m p →L[ℝ] ℝ := ((sa16y4_ellK (p := p) m' κ hN).comp (sa16r_iota d m' p)).comp Rs with hℓ
    have h1 : Tendsto (fun τ => ℓ (G τ) - ℓ (G τ₀)) (𝓝[Icc (0 : ℝ) t] τ₀) (𝓝 (ℓ (G τ₀) - ℓ (G τ₀))) :=
      (hw ℓ τ₀ hτ₀).tendsto.sub tendsto_const_nhds
    rw [sub_self] at h1
    refine h1.congr fun τ => ?_
    rw [hZ, hZp, ← map_sub]
    rfl
  have htend : Tendsto (fun τ => ∑ κ : WIndex d m', sa16y4_loc m' R₁ κ (R (Z τ))) (𝓝[Icc (0 : ℝ) t] τ₀) (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (WIndex d m')) (fun κ _ =>
      sa16y4_weak_strong m' n R hR κ R₁ (𝓝[Icc (0 : ℝ) t] τ₀) Z (2 * Kb) hBev (fun hN => hwk κ hN))
    simp only [Finset.sum_const_zero] at this
    exact this
  have hev : ∀ᶠ τ in 𝓝[Icc (0 : ℝ) t] τ₀, B' * ∑ κ : WIndex d m', sa16y4_loc m' R₁ κ (R (Z τ)) < ε / 2 := by
    have h0 : Tendsto (fun τ => B' * ∑ κ : WIndex d m', sa16y4_loc m' R₁ κ (R (Z τ))) (𝓝[Icc (0 : ℝ) t] τ₀) (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := B')).mul htend
    exact h0.eventually (gt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 hev
  refine ⟨δ, hδ, fun τ hτ hτδ => ?_⟩
  have hmem : τ ∈ Metric.ball τ₀ δ ∩ Icc (0 : ℝ) t := ⟨by rwa [Metric.mem_ball, Real.dist_eq], hτ⟩
  have hS := hδs hmem
  simp only [Set.mem_ofPred_eq] at hS
  have hMZ := sa16y4_MZ_le m' n R₁ M R hB'0 hMb hR (Zp τ)
  rw [← hZ] at hMZ
  have hfirst : B' * c * (c * d / ((n : ℝ) + 1) * ‖Zp τ‖) ≤ C0 / ((n : ℝ) + 1) := by
    rw [hC0def]
    have h1 : B' * c * (c * d / ((n : ℝ) + 1) * ‖Zp τ‖) ≤ B' * c * (c * d / ((n : ℝ) + 1) * (2 * Kb)) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hbZp τ hτ) (by positivity)) (by positivity)
    refine h1.trans (le_of_eq ?_)
    ring
  have hnorm : ‖M (Z τ)‖ ≤ ε := by
    rw [← hc] at hMZ
    linarith
  have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      wrep d m' p (M (Z τ)) x = θ x * (wrep d m p (G τ) x - wrep d m p (G τ₀) x) := by
    filter_upwards [sa16y4_M_wrep m' hθ hθc M hMs (Z τ), sa16r_iota_wrep (p := p) m' (Zp τ),
      hRsw (G τ - G τ₀), sa16y3_wrep_sub (G τ) (G τ₀)] with x h1 h2 h3 h4
    rw [h1, hZ, h2, hZp, h3, h4]
  calc wNormE m' p (fun x => θ x * (wrep d m p (G τ) x - wrep d m p (G τ₀) x))
      ≤ ENNReal.ofReal ‖M (Z τ)‖ := iInf₂_le (M (Z τ)) hae
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hnorm
end Ct18

end HRS.Whole.AppendixA.Phase2SA16R
