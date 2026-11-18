import HRS.MS.FlowB

/-!
# MS-FLOW-D: the `τ`-derivative of the inverse flow (S.A.32 (ii))

Direct difference-quotient proof; route in `FlowDPlan.md`.
-/

open Set Filter Topology
open HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

namespace HRS.MS.FlowD

variable {d : ℕ} {T : ℝ} {m : ℕ} {Λ : ℝ} {b : ℝ → Euc d → Euc d} {Ψ : ℝ → Euc d → Euc d}

theorem Λ_nonneg' (hT : 0 ≤ T) (hb : IsDriftBounds T m Λ b) : 0 ≤ Λ :=
  (FlowA.hyp_of_drift hT hb).Λ_nonneg

/-- The flow is Lipschitz in time, with constant `Λ(1+R)` when `‖Ψ_s u‖ ≤ R`. -/
theorem psi_time_lip (hT : 0 ≤ T) (hb : IsDriftBounds T m Λ b) (hΨ : IsNegDriftFlow T b Ψ)
    (u : Euc d) (R : ℝ) (hR : ∀ s ∈ Icc (0 : ℝ) T, ‖Ψ s u‖ ≤ R) :
    ∀ s ∈ Icc (0 : ℝ) T, ∀ s' ∈ Icc (0 : ℝ) T, ‖Ψ s' u - Ψ s u‖ ≤ Λ * (1 + R) * ‖s' - s‖ := by
  intro s hs s' hs'
  refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s => Ψ s u)
    (f' := fun s => -(b s (Ψ s u))) (s := Icc 0 T) (fun r hr => hΨ.eqn u r hr) (fun r hr => ?_)
    (convex_Icc 0 T) hs hs'
  rw [norm_neg]
  exact (hb.growth r hr (Ψ r u)).trans
    (mul_le_mul_of_nonneg_left (by linarith [hR r hr]) (Λ_nonneg' hT hb))

theorem psi_zero_bound (hΨ : IsNegDriftFlow T b Ψ) : ∃ M₀ : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ‖Ψ s 0‖ ≤ M₀ :=
  isCompact_Icc.exists_bound_of_continuousOn (FlowA.sol_of_flow hΨ 0).continuousOn

/-- Any inverse of `Ψ τ` has the Lipschitz constant `e^{Λτ}`. -/
theorem inv_lip (hT : 0 ≤ T) (hb : IsDriftBounds T m Λ b) (hΨ : IsNegDriftFlow T b Ψ)
    (Ψinv : ℝ → Euc d → Euc d)
    (hinv : ∀ τ ∈ Icc (0 : ℝ) T, (∀ x, Ψinv τ (Ψ τ x) = x) ∧ (∀ y, Ψ τ (Ψinv τ y) = y)) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ y y', ‖Ψinv τ y - Ψinv τ y'‖ ≤ Real.exp (Λ * τ) * ‖y - y'‖ := by
  intro τ hτ
  obtain ⟨Φ, hΦ1, hΦ2, hΦl⟩ := FlowA.flow_invertible hT hb hΨ τ hτ
  have e : ∀ y, Ψinv τ y = Φ y := fun y => by
    calc Ψinv τ y = Ψinv τ (Ψ τ (Φ y)) := by rw [hΦ2]
      _ = Φ y := (hinv τ hτ).1 _
  intro y y'
  rw [e, e]
  exact hΦl y y'

theorem inv_bound (hT : 0 ≤ T) (hb : IsDriftBounds T m Λ b) (hΨ : IsNegDriftFlow T b Ψ)
    (Ψinv : ℝ → Euc d → Euc d)
    (hinv : ∀ τ ∈ Icc (0 : ℝ) T, (∀ x, Ψinv τ (Ψ τ x) = x) ∧ (∀ y, Ψ τ (Ψinv τ y) = y))
    (x : Euc d) :
    ∃ R : ℝ, ∀ τ' ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ‖Ψ s (Ψinv τ' x)‖ ≤ R := by
  obtain ⟨M₀, hM₀⟩ := psi_zero_bound hΨ
  have hΛ := Λ_nonneg' hT hb
  set E := Real.exp (Λ * T) with hE
  have hexp : ∀ s ∈ Icc (0 : ℝ) T, Real.exp (Λ * s) ≤ E := fun s hs =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 hΛ)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  refine ⟨E * (E * (‖x‖ + M₀)) + M₀, fun τ' hτ' s hs => ?_⟩
  have hM0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0 ⟨le_rfl, hT⟩)
  have hu : ‖Ψinv τ' x‖ ≤ E * (‖x‖ + M₀) := by
    have h1 := inv_lip hT hb hΨ Ψinv hinv τ' hτ' x (Ψ τ' 0)
    rw [(hinv τ' hτ').1 0, sub_zero] at h1
    refine h1.trans ?_
    have h2 : ‖x - Ψ τ' 0‖ ≤ ‖x‖ + M₀ := (norm_sub_le _ _).trans (by linarith [hM₀ τ' hτ'])
    exact (mul_le_mul (hexp τ' hτ') h2 (norm_nonneg _) hE0)
  have h3 := FlowA.flow_lipschitz hT hb hΨ s hs (Ψinv τ' x) 0
  rw [sub_zero] at h3
  calc ‖Ψ s (Ψinv τ' x)‖ ≤ ‖Ψ s (Ψinv τ' x) - Ψ s 0‖ + ‖Ψ s 0‖ := norm_le_norm_sub_add _ _
    _ ≤ E * ‖Ψinv τ' x‖ + M₀ := by
        gcongr
        · exact h3.trans (mul_le_mul_of_nonneg_right (hexp s hs) (norm_nonneg _))
        · exact hM₀ s hs
    _ ≤ E * (E * (‖x‖ + M₀)) + M₀ := by gcongr

theorem inv_time_lip (hT : 0 ≤ T) (hb : IsDriftBounds T m Λ b) (hΨ : IsNegDriftFlow T b Ψ)
    (Ψinv : ℝ → Euc d → Euc d)
    (hinv : ∀ τ ∈ Icc (0 : ℝ) T, (∀ x, Ψinv τ (Ψ τ x) = x) ∧ (∀ y, Ψ τ (Ψinv τ y) = y))
    (x : Euc d) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Icc (0 : ℝ) T, ∀ τ' ∈ Icc (0 : ℝ) T,
      ‖Ψinv τ' x - Ψinv τ x‖ ≤ L * ‖τ' - τ‖ := by
  obtain ⟨R, hR⟩ := inv_bound hT hb hΨ Ψinv hinv x
  have hΛ := Λ_nonneg' hT hb
  have hR0 : 0 ≤ R := by
    refine (norm_nonneg _).trans (hR 0 ⟨le_rfl, hT⟩ 0 ⟨le_rfl, hT⟩)
  refine ⟨Real.exp (Λ * T) * (Λ * (1 + R)), by positivity, fun τ hτ τ' hτ' => ?_⟩
  set u := Ψinv τ' x with hu
  have hx : Ψ τ' u = x := (hinv τ' hτ').2 x
  have h1 : Ψinv τ x = Ψinv τ (Ψ τ' u) := by rw [hx]
  have h2 : u = Ψinv τ (Ψ τ u) := ((hinv τ hτ).1 u).symm
  have h3 := psi_time_lip hT hb hΨ u R (fun s hs => hR τ' hτ' s hs) τ hτ τ' hτ'
  calc ‖u - Ψinv τ x‖ = ‖Ψinv τ (Ψ τ u) - Ψinv τ (Ψ τ' u)‖ := by rw [← h1, ← h2]
    _ ≤ Real.exp (Λ * τ) * ‖Ψ τ u - Ψ τ' u‖ := inv_lip hT hb hΨ Ψinv hinv τ hτ _ _
    _ = Real.exp (Λ * τ) * ‖Ψ τ' u - Ψ τ u‖ := by rw [norm_sub_rev]
    _ ≤ Real.exp (Λ * T) * (Λ * (1 + R) * ‖τ' - τ‖) := by
        exact mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτ.2 hΛ)) h3
          (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

/-- The key estimate: `τ' ↦ Ψ_τ(Ψ_{τ'}^{-1} x)` has derivative `b^τ(x)` at `τ` within `[0,T]`. -/
theorem key_hasDeriv (hT : 0 ≤ T) (hb : IsDriftBounds T m Λ b) (hΨ : IsNegDriftFlow T b Ψ)
    (Ψinv : ℝ → Euc d → Euc d)
    (hinv : ∀ τ ∈ Icc (0 : ℝ) T, (∀ x, Ψinv τ (Ψ τ x) = x) ∧ (∀ y, Ψ τ (Ψinv τ y) = y))
    (x : Euc d) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun τ' => Ψ τ (Ψinv τ' x)) (b τ x) (Icc 0 T) τ := by
  obtain ⟨L, hL0, hL⟩ := inv_time_lip hT hb hΨ Ψinv hinv x
  have hu₀ : Ψ τ (Ψinv τ x) = x := (hinv τ hτ).2 x
  have hk : ContinuousOn (fun p : ℝ × Euc d => b p.1 (Ψ p.1 p.2)) (Icc (0 : ℝ) T ×ˢ univ) := by
    have h1 := FlowA.flow_continuous hT hb hΨ
    have h2 : ContinuousOn (fun p : ℝ × Euc d => (p.1, Ψ p.1 p.2)) (Icc (0 : ℝ) T ×ˢ univ) :=
      continuousOn_fst.prodMk h1
    exact hb.cont.comp h2 (fun p hp => ⟨hp.1, mem_univ _⟩)
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hkc := hk (τ, Ψinv τ x) ⟨hτ, mem_univ _⟩
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds] at hkc
  obtain ⟨δ, hδ, hδk⟩ := hkc ε hε
  have hpos : 0 < δ / (L + 1) := by positivity
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds τ hpos)] with τ' hτ' hball
  have hball' : |τ' - τ| < δ / (L + 1) := by simpa [Metric.mem_ball, Real.dist_eq] using hball
  have hmul : |τ' - τ| * (L + 1) < δ := by rwa [lt_div_iff₀ (by positivity)] at hball'
  set u := Ψinv τ' x with hu
  have hx : Ψ τ' u = x := (hinv τ' hτ').2 x
  have hdist : ‖u - Ψinv τ x‖ < δ := by
    have := hL τ hτ τ' hτ'
    rw [Real.norm_eq_abs] at this
    nlinarith [abs_nonneg (τ' - τ)]
  set c := b τ x with hc
  have hSsub : uIcc τ τ' ⊆ Icc (0 : ℝ) T := uIcc_subset_Icc hτ hτ'
  have hMVT : ‖(Ψ τ' u + τ' • c) - (Ψ τ u + τ • c)‖ ≤ ε * ‖τ' - τ‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s => Ψ s u + s • c)
      (f' := fun s => -(b s (Ψ s u)) + (1 : ℝ) • c) (s := uIcc τ τ') (fun s hs => ?_)
      (fun s hs => ?_) (convex_uIcc τ τ') left_mem_uIcc right_mem_uIcc
    · exact ((hΨ.eqn u s (hSsub hs)).mono hSsub).add ((hasDerivWithinAt_id s _).smul_const c)
    · have hs1 : |s - τ| ≤ |τ' - τ| := abs_sub_left_of_mem_uIcc hs
      have := hδk (x := (s, u)) ⟨hSsub hs, mem_univ _⟩ (by
        rw [Prod.dist_eq, max_lt_iff]
        refine ⟨?_, ?_⟩
        · rw [Real.dist_eq]
          nlinarith [abs_nonneg (τ' - τ)]
        · rw [dist_eq_norm]; exact hdist)
      dsimp only at this
      rw [dist_eq_norm, hu₀] at this
      have e : -(b s (Ψ s u)) + (1 : ℝ) • c = -(b s (Ψ s u) - c) := by rw [one_smul]; abel
      rw [e, norm_neg]
      exact this.le
  have e : Ψ τ u - Ψ τ (Ψinv τ x) - (τ' - τ) • c = -((Ψ τ' u + τ' • c) - (Ψ τ u + τ • c)) := by
    rw [hx, hu₀, sub_smul]; abel
  rw [e, norm_neg]
  exact hMVT

/-- Deliverable 1: `∂_τ Ψ_τ^{-1}(x) = ∇Ψ_τ^{-1}(x) b^τ(x)` within `[0,T]`. -/
theorem flow_inv_hasDerivWithinAt (hT : 0 ≤ T) (hb : IsDriftBounds T m Λ b)
    (hΨ : IsNegDriftFlow T b Ψ) (Ψinv : ℝ → Euc d → Euc d)
    (hinv : ∀ τ ∈ Icc (0 : ℝ) T, (∀ x, Ψinv τ (Ψ τ x) = x) ∧ (∀ y, Ψ τ (Ψinv τ y) = y)) :
    ∀ x : Euc d, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun τ' => Ψinv τ' x) (fderiv ℝ (Ψinv τ) x (b τ x)) (Icc 0 T) τ := by
  intro x τ hτ
  have hcd := (FlowB.flow_inv_contDiff hT hb hΨ τ hτ (Ψinv τ) (hinv τ hτ).1 (hinv τ hτ).2).1
  have hdiff : DifferentiableAt ℝ (Ψinv τ) x :=
    hcd.differentiable (by exact_mod_cast Nat.succ_ne_zero m) x
  have hl : HasFDerivAt (Ψinv τ) (fderiv ℝ (Ψinv τ) x) (Ψ τ (Ψinv τ x)) := by
    rw [(hinv τ hτ).2 x]; exact hdiff.hasFDerivAt
  have := hl.comp_hasDerivWithinAt τ (key_hasDeriv hT hb hΨ Ψinv hinv x hτ)
  exact this.congr (fun y _ => ((hinv τ hτ).1 _).symm) ((hinv τ hτ).1 _).symm

end HRS.MS.FlowD
