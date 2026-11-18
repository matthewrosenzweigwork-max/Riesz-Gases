import HRS.MS.UniqC3

/-!
# Packet C3, part 2: the advected weights `ς_c^τ = (advCutoff χ Ψ τ c)^2`

Values in `[0,1]`, `C^2` with bounded first and second derivatives, support in `B̄(Ψ_τ c, 2L)`, equal to
`1` on `B̄(Ψ_τ c, 1/L)`, transport equation `∂_τ ς = b · ∇ς` with jointly continuous right side, and the
partner cutoff `advCutoff χh`.  `L = e^{Cb t}`.
-/

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open HRS HRS.Whole

namespace HRS.MS.UniqC3

variable {d : ℕ}

/-- The weight `ς_c^τ(x) = (χ(Ψ_τ^{-1}(x) - c))^2`. -/
def varsigma (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (c x : Euc d) : ℝ :=
  advCutoff χ Ψ τ c x ^ 2

theorem varsigma_eq (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (c : Euc d) :
    varsigma χ Ψ τ c = fun x => (fun y => χ y ^ 2) (Function.invFun (Ψ τ) x - c) := rfl

section Weights

variable {m : ℕ} {Cb t : ℝ} {Ψ : ℝ → Euc d → Euc d} {χ : Euc d → ℝ}

/-- `χ ∈ [0,1]` gives `ς ∈ [0,1]`. -/
theorem varsigma_range (hχ : AppendixA.IsUlocCutoff χ) (τ : ℝ) (c x : Euc d) :
    0 ≤ varsigma χ Ψ τ c x ∧ varsigma χ Ψ τ c x ≤ 1 := by
  have h := hχ.2.2.2.1 (Function.invFun (Ψ τ) x - c)
  exact ⟨sq_nonneg _, pow_le_one₀ h.1 h.2⟩

/-- The weight is `C^2` (here `m ≥ 1`). -/
theorem varsigma_contDiff (hχ : AppendixA.IsUlocCutoff χ) (hm : 1 ≤ m)
    (hF : FlowFacts m Cb t Ψ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) (c : Euc d) :
    ContDiff ℝ 2 (varsigma χ Ψ τ c) := by
  have h1 : ContDiff ℝ ∞ (fun y : Euc d => χ y ^ 2) := hχ.1.pow 2 |> fun h => h
  have h2 : ContDiff ℝ 2 (fun y : Euc d => χ y ^ 2) := h1.of_le (by simp)
  have h3 : ContDiff ℝ 2 (fun x => Function.invFun (Ψ τ) x - c) :=
    ((hF.contDiff_inv τ hτ).of_le (by exact_mod_cast Nat.succ_le_succ hm)).sub contDiff_const
  exact h2.comp h3

/-- Generic support bound: if `g w ≠ 0 → ‖w‖ < r`, the support of `g (Ψ_τ^{-1} · - c)` lies in
`B̄(Ψ_τ c, r e^{Cb τ})`. -/
theorem tsupport_sub_closedBall (hF : FlowFacts m Cb t Ψ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t)
    (c : Euc d) (g : Euc d → ℝ) {r : ℝ} (hr : 0 ≤ r) (hg : ∀ w, g w ≠ 0 → ‖w‖ < r) :
    tsupport (fun x => g (Function.invFun (Ψ τ) x - c)) ⊆
      Metric.closedBall (Ψ τ c) (r * Real.exp (Cb * τ)) := by
  refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
  have hx' : g (Function.invFun (Ψ τ) x - c) ≠ 0 := hx
  have h1 := hg _ hx'
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h2 := hF.lip τ hτ (Function.invFun (Ψ τ) x) c
  rw [hF.inv_right τ hτ x] at h2
  calc ‖x - Ψ τ c‖ ≤ Real.exp (Cb * τ) * ‖Function.invFun (Ψ τ) x - c‖ := h2
    _ ≤ Real.exp (Cb * τ) * r := mul_le_mul_of_nonneg_left h1.le (Real.exp_pos _).le
    _ = r * Real.exp (Cb * τ) := mul_comm _ _

/-- Generic equality-to-one on a small ball. -/
theorem eq_one_of_mem_ball (hF : FlowFacts m Cb t Ψ) (hCb : 0 ≤ Cb) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) t) (c : Euc d) (g : Euc d → ℝ) {r : ℝ}
    (hg : ∀ w, ‖w‖ ≤ r → g w = 1) {x : Euc d}
    (hx : x ∈ Metric.closedBall (Ψ τ c) (r / Real.exp (Cb * t))) :
    g (Function.invFun (Ψ τ) x - c) = 1 := by
  apply hg
  have h1 := hF.lip_inv τ hτ x (Ψ τ c)
  rw [hF.inv_left τ hτ c] at h1
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  have hE : Real.exp (Cb * τ) ≤ Real.exp (Cb * t) := Real.exp_le_exp.2 (by nlinarith [hτ.2])
  have hEp := Real.exp_pos (Cb * t)
  calc ‖Function.invFun (Ψ τ) x - c‖ ≤ Real.exp (Cb * τ) * ‖x - Ψ τ c‖ := h1
    _ ≤ Real.exp (Cb * t) * (r / Real.exp (Cb * t)) := by
        gcongr
    _ = r := by field_simp

theorem uc3_le_cbNorm {f : Euc d → ℝ} {n j : ℕ} (hf : MemCb n f) (hj : j ≤ n) (x : Euc d) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ cbNorm n f := by
  refine (le_ciSup (hf.2 j hj) x).trans ?_
  unfold cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖)
    (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

/-- The square of an `IsUlocCutoff` is an `IsUlocCutoff`. -/
theorem uloc_sq (hχ : AppendixA.IsUlocCutoff χ) : AppendixA.IsUlocCutoff (fun y => χ y ^ 2) := by
  refine ⟨hχ.1.pow 2, ?_, ?_, fun x => ⟨sq_nonneg _, pow_le_one₀ (hχ.2.2.2.1 x).1 (hχ.2.2.2.1 x).2⟩,
    fun x hx => by simp [hχ.2.2.2.2 x hx]⟩
  · have e : (fun y => χ y ^ 2) = χ * χ := by funext y; simp [sq]
    rw [e]; exact hχ.2.1.mul_right
  · refine (closure_mono fun y hy => ?_).trans hχ.2.2.1
    exact fun h => hy (by simp [h])

/-- First and second derivative bounds of `ς`, uniform in `c` and `τ ∈ [0,t]` (from the `C_b^{m+1}`
bound of `FlowE.uloc_bilip_i_ii` applied to `χ^2`). -/
theorem uc3_deriv_bounds (m : ℕ) (hm : 1 ≤ m) (Cb t : ℝ) (ht : 0 < t) (χ χh : Euc d → ℝ)
    (hχ : AppendixA.IsUlocCutoff χ) (hχh : AppendixALemmas.IsCutoffRad 6 8 χh) :
    ∃ K : ℝ, 0 < K ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb t b → IsNegDriftFlow t b Ψ → ∀ τ ∈ Icc (0 : ℝ) t, ∀ c : Euc d,
        (∀ x, ‖fderiv ℝ (varsigma χ Ψ τ c) x‖ ≤ K) ∧
        (∀ x, ‖fderiv ℝ (fderiv ℝ (varsigma χ Ψ τ c)) x‖ ≤ K) := by
  obtain ⟨C, hC, hprop⟩ := HRS.MS.FlowE.uloc_bilip_i_ii m t Cb ht (fun y => χ y ^ 2) χh
    (uloc_sq hχ) hχh
  refine ⟨max 1 (C * Real.exp (C * m * t)), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro b Ψ hb hΨ τ hτ c
  obtain ⟨-, hex⟩ := hprop b (uc3_drift hb)
  obtain ⟨Ψinv, hΨinv⟩ := hex Ψ (uc3_flow hΨ)
  obtain ⟨⟨hi1, -⟩, hii⟩ := hΨinv τ hτ
  have hid : Ψinv τ = Function.invFun (Ψ τ) := funext fun y => by
    obtain ⟨x, rfl⟩ := (hΨ.bij τ hτ).2 y
    rw [hi1 x, Function.leftInverse_invFun (hΨ.bij τ hτ).1 x]
  obtain ⟨-, hmem, hcb⟩ := hii c
  rw [hid] at hmem hcb
  have hmem' : MemCb (m + 1) (varsigma χ Ψ τ c) := hmem
  have hcb' : cbNorm (m + 1) (varsigma χ Ψ τ c) ≤ C * Real.exp (C * m * t) :=
    hcb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
      have : (0 : ℝ) ≤ C * m := by positivity
      nlinarith [hτ.2])) hC.le)
  have hK := le_max_right 1 (C * Real.exp (C * m * t))
  have hcd : ContDiff ℝ 2 (varsigma χ Ψ τ c) := by
    refine hmem'.1.of_le ?_
    exact_mod_cast Nat.succ_le_succ hm
  constructor
  · intro x
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    exact (uc3_le_cbNorm hmem' (by omega) x).trans (hcb'.trans hK)
  · intro x
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ), norm_iteratedFDeriv_fderiv]
    exact (uc3_le_cbNorm hmem' (by omega) x).trans (hcb'.trans hK)

theorem varsigma_hasDerivWithinAt {b : ℝ → Euc d → Euc d} (ht : 0 ≤ t)
    (hb : IsAdvectingDrift m Cb t b) (hΨ : IsNegDriftFlow t b Ψ) (hχ : AppendixA.IsUlocCutoff χ)
    (c x : Euc d) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) :
    HasDerivWithinAt (fun τ' => varsigma χ Ψ τ' c x)
      (inner ℝ (b τ x) (gradient (varsigma χ Ψ τ c) x)) (Icc 0 t) τ :=
  HRS.MS.FlowD.flow_cutoff_hasDerivWithinAt ht (uc3_drift hb) (uc3_flow hΨ)
    (fun τ => Function.invFun (Ψ τ)) (uc3_hinv hΨ) (fun y => χ y ^ 2) (hχ.1.pow 2) c x τ hτ

theorem varsigma_fderiv_eq (hχ : AppendixA.IsUlocCutoff χ) (hm : 1 ≤ m)
    (hF : FlowFacts m Cb t Ψ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) (c x : Euc d) :
    fderiv ℝ (varsigma χ Ψ τ c) x = (fderiv ℝ (fun y : Euc d => χ y ^ 2)
      (Function.invFun (Ψ τ) x - c)).comp (fderiv ℝ (Function.invFun (Ψ τ)) x) := by
  have hχd : Differentiable ℝ (fun y : Euc d => χ y ^ 2) := (hχ.1.pow 2).differentiable (by simp)
  have hΦd : Differentiable ℝ (Function.invFun (Ψ τ)) :=
    (hF.contDiff_inv τ hτ).differentiable (by exact_mod_cast Nat.succ_ne_zero m)
  exact ((hχd _).hasFDerivAt.comp x ((hΦd x).hasFDerivAt.sub_const c)).fderiv

/-- Joint continuity of `ς`, of `∇ς` and of `b · ∇ς`. -/
theorem varsigma_cont {b : ℝ → Euc d → Euc d} (hb : IsAdvectingDrift m Cb t b)
    (hχ : AppendixA.IsUlocCutoff χ) (hm : 1 ≤ m) (hF : FlowFacts m Cb t Ψ) (c : Euc d) :
    ContinuousOn (fun p : ℝ × Euc d => varsigma χ Ψ p.1 c p.2) (Icc (0 : ℝ) t ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (varsigma χ Ψ p.1 c) p.2) (Icc (0 : ℝ) t ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × Euc d => inner ℝ (b p.1 p.2) (gradient (varsigma χ Ψ p.1 c) p.2))
      (Icc (0 : ℝ) t ×ˢ univ) := by
  have h1 : ContinuousOn (fun p : ℝ × Euc d => varsigma χ Ψ p.1 c p.2) (Icc (0 : ℝ) t ×ˢ univ) :=
    (hχ.1.pow 2).continuous.comp_continuousOn (hF.cont_inv.sub continuousOn_const)
  have hcf : Continuous (fderiv ℝ (fun y : Euc d => χ y ^ 2)) :=
    (hχ.1.pow 2).continuous_fderiv (by simp)
  have h2 : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (varsigma χ Ψ p.1 c) p.2)
      (Icc (0 : ℝ) t ×ˢ univ) := by
    have : ContinuousOn (fun p : ℝ × Euc d => (fderiv ℝ (fun y : Euc d => χ y ^ 2)
        (Function.invFun (Ψ p.1) p.2 - c)).comp (fderiv ℝ (Function.invFun (Ψ p.1)) p.2))
        (Icc (0 : ℝ) t ×ˢ univ) :=
      (hcf.comp_continuousOn (hF.cont_inv.sub continuousOn_const)).clm_comp hF.cont_fderiv_inv
    exact this.congr fun p hp => varsigma_fderiv_eq hχ hm hF hp.1 c p.2
  refine ⟨h1, h2, ?_⟩
  have h3 : ContinuousOn (fun p : ℝ × Euc d => gradient (varsigma χ Ψ p.1 c) p.2)
      (Icc (0 : ℝ) t ×ˢ univ) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn h2
  exact hb.cont.inner h3

end Weights

end HRS.MS.UniqC3
