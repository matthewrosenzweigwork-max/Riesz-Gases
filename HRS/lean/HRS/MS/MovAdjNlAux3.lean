import HRS.MS.MovAdjNlAux2

/-!
# S6.7 nonlinear row, package A, packet N1 (part 3): the Volterra identity `s67a_volterra`

Namespace `HRS.MS.MovAdjNl`, helpers `s67a_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

* `s67a_Tgen`: for `v₀` in the Schwartz core of `L²_0` there is `w₀ ∈ L²_0` with `(d/dτ) T(τ) v₀ = -T(σ) w₀` (right derivative at every `σ ≥ 0`).
* `s67a_k_bound`: the source `k(σ) = ∫ (R_{r+σ} f_{r+σ}) √ρ T(σ) v₀` is bounded on `(0,t-r)` (it is minus the derivative of the pairing, whose two
  terms are bounded: `a'` is dominated in `L²`, and `S T(σ) v₀ = T(σ) w₀`).
* `s67a_volterra`: **`∫ f_r √ρ v₀ = ∫ φ √ρ T(t-r) v₀ + ∫_0^{t-r} k(σ) dσ`**.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdjNl

open HRS HRS.Whole HRS.MH.DualityRd HRS.MS.MovLin HRS.MS.Mov63 HRS.MS.MovAdj

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s67a_Tgen (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {φ₀ : 𝓢R} {v₀ : MovL2Zero ρ} (hv : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v₀ x = φ₀ x) :
    ∃ w₀ : MovL2Zero ρ, ∀ σ : ℝ, 0 ≤ σ →
      HasDerivWithinAt (fun τ => ((mov2d_T H ψ0 hψ0 τ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))))
        (-((mov2d_T H ψ0 hψ0 σ w₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d)))) (Set.Ici σ) σ := by
  obtain ⟨w₀, -, hwd⟩ := mov2d_T_gen H ψ0 hψ0 φ₀ v₀ hv
  refine ⟨w₀, fun σ hσ => ?_⟩
  have h := (Submodule.subtypeL (MovL2Zero ρ)).hasFDerivAt.comp_hasDerivWithinAt σ (hwd σ hσ)
  exact h.congr_deriv (by simp)

theorem s67a_norm_toLp_le {F G : Euc d → ℝ} (hF : MemLp F 2 (volume : Measure (Euc d)))
    (hG : MemLp G 2 (volume : Measure (Euc d))) (h : ∀ x, |F x| ≤ G x) :
    ‖hF.toLp F‖ ≤ ‖hG.toLp G‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x h1 h2
  rw [h1, h2, Real.norm_eq_abs, Real.norm_eq_abs]
  exact (h x).trans (le_abs_self _)

set_option maxHeartbeats 1600000 in
theorem s67a_k_bound (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {ρt : ℝ → Euc d → ℝ} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρt) t φ f) (ht : 0 ≤ t)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) {φ₀ : 𝓢R} {v₀ : MovL2Zero ρ}
    (hv : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v₀ x = φ₀ x)
    (hgL : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d))) {w₀ : MovL2Zero ρ}
    (hw₀ : ∀ σ : ℝ, 0 ≤ σ →
      HasDerivWithinAt (fun τ => ((mov2d_T H ψ0 hψ0 τ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))))
        (-((mov2d_T H ψ0 hψ0 σ w₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d)))) (Set.Ici σ) σ)
    {BU Bw : ℝ}
    (hBU : ∀ τ ∈ Set.Icc (0 : ℝ) (t - r),
      ‖((mov2d_T H ψ0 hψ0 τ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d)))‖ ≤ BU)
    (hBw : ∀ τ ∈ Set.Icc (0 : ℝ) (t - r),
      ‖((mov2d_T H ψ0 hψ0 τ w₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d)))‖ ≤ Bw) :
    ∃ Bk : ℝ, ∀ σ ∈ Set.Ioo (0 : ℝ) (t - r),
      |∫ x, s67aR d s q β ρ ρt (r + σ) (f (r + σ)) x *
        (Real.sqrt (ρ x) * movFun (mov2d_T H ψ0 hψ0 σ v₀) x)| ≤ Bk := by
  obtain ⟨B0, hB00, hB0⟩ := s67_f_bdd hf
  obtain ⟨Bf, hBf0, hBgen, -⟩ := s67_time_lip hf
  have hGL : MemLp (fun x => Bf * ((1 + ‖x‖) * Real.sqrt (ρ x))) 2 (volume : Measure (Euc d)) :=
    (s67_memLp_G H).const_mul Bf
  have hAL : MemLp (fun x => B0 * Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := hgL.const_mul B0
  refine ⟨‖hAL.toLp (fun x => B0 * Real.sqrt (ρ x))‖ * Bw + ‖hGL.toLp _‖ * BU, fun σ hσ => ?_⟩
  have hσ0 : 0 ≤ σ := hσ.1.le
  have hσI : σ ∈ Set.Icc (0 : ℝ) (t - r) := ⟨hσ0, hσ.2.le⟩
  have hr1 : 0 < r + σ := by linarith [hr.1, hσ.1]
  have hr2 : r + σ < t := by linarith [hσ.2]
  have hr'mem : r + σ ∈ Set.Icc (0 : ℝ) t := ⟨hr1.le, hr2.le⟩
  obtain ⟨φ', hφ', w, hw, hwd⟩ := s67_T_deriv H ψ0 hψ0 hv hσ0
  obtain ⟨a', ha', ha'def, hAd⟩ := s67a_hdv H hf ht hr hgL hσ
  have hb : HasDerivWithinAt (fun τ => ((mov2d_T H ψ0 hψ0 τ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))))
      (-(w : Lp ℝ 2 (volume : Measure (Euc d)))) (Set.Ici σ) σ := by
    have h := (Submodule.subtypeL (MovL2Zero ρ)).hasFDerivAt.comp_hasDerivWithinAt σ hwd
    exact h.congr_deriv (by simp)
  have hpair := hAd.inner ℝ hb
  have hk := s67a_gdv H ψ0 hψ0 hf ht hr hv hgL hσ
  have hU := (uniqueDiffWithinAt_Ici σ)
  have hwe : (w : Lp ℝ 2 (volume : Measure (Euc d))) =
      ((mov2d_T H ψ0 hψ0 σ w₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) := by
    have := hU.eq_deriv _ hb (hw₀ σ hσ0)
    exact neg_injective this
  have hD := hU.eq_deriv _ hpair hk
  rw [← neg_neg (∫ x, s67aR d s q β ρ ρt (r + σ) (f (r + σ)) x *
      (Real.sqrt (ρ x) * movFun (mov2d_T H ψ0 hψ0 σ v₀) x)), ← hD, abs_neg]
  have hclσ : s67clamp r t σ = r + σ := s67clamp_eq hr1.le hr2.le
  have n1 : ‖(s67a_memLp hf ht r hgL σ).toLp (s67a f ρ r t σ)‖ ≤ ‖hAL.toLp (fun x => B0 * Real.sqrt (ρ x))‖ := by
    refine s67a_norm_toLp_le _ _ fun x => ?_
    unfold s67a
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (hB0 _ (s67clamp_mem ht σ) x) (Real.sqrt_nonneg _)
  have n2 : ‖ha'.toLp a'‖ ≤ ‖hGL.toLp (fun x => Bf * ((1 + ‖x‖) * Real.sqrt (ρ x)))‖ := by
    refine s67a_norm_toLp_le _ _ fun x => ?_
    rw [ha'def x, abs_mul, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc |generatorW ((quadraticGradientDyn d s q β).coeff ρt) (r + σ) (f (r + σ)) x| * Real.sqrt (ρ x)
        ≤ (Bf * (1 + ‖x‖)) * Real.sqrt (ρ x) :=
          mul_le_mul_of_nonneg_right (hBgen _ hr'mem x) (Real.sqrt_nonneg _)
      _ = Bf * ((1 + ‖x‖) * Real.sqrt (ρ x)) := by ring
  have n3 : ‖(w : Lp ℝ 2 (volume : Measure (Euc d)))‖ ≤ Bw := by rw [hwe]; exact hBw σ hσI
  have n4 := hBU σ hσI
  calc |inner ℝ ((s67a_memLp hf ht r hgL σ).toLp (s67a f ρ r t σ)) (-(w : Lp ℝ 2 (volume : Measure (Euc d)))) +
        inner ℝ (ha'.toLp a') ((mov2d_T H ψ0 hψ0 σ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d)))|
      ≤ |inner ℝ ((s67a_memLp hf ht r hgL σ).toLp (s67a f ρ r t σ)) (-(w : Lp ℝ 2 (volume : Measure (Euc d))))| +
        |inner ℝ (ha'.toLp a') ((mov2d_T H ψ0 hψ0 σ v₀ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d)))| :=
        abs_add_le _ _
    _ ≤ _ := by
        refine add_le_add ((abs_real_inner_le_norm _ _).trans ?_) ((abs_real_inner_le_norm _ _).trans ?_)
        · rw [norm_neg]
          exact mul_le_mul n1 n3 (norm_nonneg _) (norm_nonneg _)
        · exact mul_le_mul n2 n4 (norm_nonneg _) (norm_nonneg _)

end HRS.MS.MovAdjNl
