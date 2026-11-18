import HRS.MH.DualityRdB2Aux

/-!
# DualityRd packet B2: `mf_continuity` (continuity in time of the mean-field trajectory on `ℝ^d`)

Assembles the helpers of `DualityRdB2Aux.lean`: (i) `r ↦ ρ_r(x)` is continuous (uniform approximation by
`⟨ρ_r, η_n(x-·)⟩`), (ii) `(u,r) ↦ ⟨ρ_r, φ_u⟩` is jointly continuous (dominated convergence with the decay
majorant), (iii) `(a,r) ↦ mfGen D (f_a) (ρ_r)` is jointly continuous (the drift part by (ii), the interaction
part by a two-stage dominated convergence).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.DualityRd

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem mf_continuity_proof {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ}
    (h : MFData s Λ T ΛV G₀ D ρ) :
    (∀ x : Euc d, ContinuousOn (fun r => ρ r x) (Set.Icc (0 : ℝ) T)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : ℝ → Euc d → ℝ,
      ContinuousOn (Function.uncurry φ) (Set.Icc (0 : ℝ) t ×ˢ Set.univ) →
      (∃ K : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) t, ∀ x, |φ u x| ≤ K * (1 + ‖x‖)) →
      ContinuousOn (fun p : ℝ × ℝ => Whole.pair (Whole.withDensityReal (ρ p.2)) (φ p.1))
        (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ f ft : ℝ → Euc d → ℝ, IsC12TestRd t f ft →
      ContinuousOn (fun p : ℝ × ℝ => mfGen D (f p.1) (ρ p.2))
        (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t)) := by
  refine ⟨fun x => db2_rho_contOn h x, fun t ht φ hφc hφg => db2_pair_joint h ht φ hφc hφg,
    fun t ht f ft hf => ?_⟩
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hV2 : ContDiff ℝ 2 D.V := h.hV.1.of_le (by norm_num)
  -- the drift test function `φ_a = β⁻¹ Δf_a - ∇V · ∇f_a` is jointly continuous with linear growth
  have hφc : ContinuousOn (Function.uncurry (fun a x => D.invβ * Laplacian.laplacian (f a) x
      - inner ℝ (gradient D.V x) (gradient (f a) x))) (Set.Icc (0 : ℝ) t ×ˢ Set.univ) := by
    have h1 := db2_lap_joint hf
    have h2 := db2_grad_joint hf
    have h3 : ContinuousOn (fun p : ℝ × Euc d => gradient D.V p.2) (Set.Icc (0 : ℝ) t ×ˢ Set.univ) :=
      ((db1_gradient_continuous hV2).comp continuous_snd).continuousOn
    exact (continuousOn_const.mul h1).sub (h3.inner h2)
  have hφg : ∃ K : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) t, ∀ x : Euc d,
      |D.invβ * Laplacian.laplacian (f u) x - inner ℝ (gradient D.V x) (gradient (f u) x)|
        ≤ K * (1 + ‖x‖) := by
    obtain ⟨CL, hCL⟩ := db2_lap_unif hf
    obtain ⟨A, hA⟩ := db2_grad_unif hf
    refine ⟨|D.invβ| * |CL| + (|G₀| + |ΛV|) * |A|, fun u hu x => ?_⟩
    have hu0 : u ∈ Set.Icc (0 : ℝ) t := hu
    have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
    have hΔ : |Laplacian.laplacian (f u) x| ≤ |CL| := (hCL u hu0 x).trans (le_abs_self _)
    have hg : ‖gradient (f u) x‖ ≤ |A| := (hA u hu0 x).trans (le_abs_self _)
    have hVg := Q09B.q09b_gradV_bound (le_refl 2) h.hV x
    have hV0 : 0 ≤ G₀ + ΛV * ‖x‖ := (norm_nonneg _).trans hVg
    have hb1 : |D.invβ * Laplacian.laplacian (f u) x| ≤ |D.invβ| * |CL| * (1 + ‖x‖) := by
      rw [abs_mul]
      have e1 : |D.invβ| * |Laplacian.laplacian (f u) x| ≤ |D.invβ| * |CL| :=
        mul_le_mul_of_nonneg_left hΔ (abs_nonneg _)
      have e2 : |D.invβ| * |CL| ≤ |D.invβ| * |CL| * (1 + ‖x‖) :=
        le_mul_of_one_le_right (by positivity) (by linarith)
      linarith
    have hb2 : |inner ℝ (gradient D.V x) (gradient (f u) x)| ≤ (|G₀| + |ΛV|) * |A| * (1 + ‖x‖) := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      have e1 : ‖gradient D.V x‖ * ‖gradient (f u) x‖ ≤ (G₀ + ΛV * ‖x‖) * |A| :=
        mul_le_mul hVg hg (norm_nonneg _) hV0
      have e2 : G₀ + ΛV * ‖x‖ ≤ (|G₀| + |ΛV|) * (1 + ‖x‖) := by
        nlinarith [le_abs_self G₀, le_abs_self ΛV, abs_nonneg G₀, abs_nonneg ΛV,
          mul_nonneg (abs_nonneg G₀) hx0, mul_le_mul_of_nonneg_right (le_abs_self ΛV) hx0]
      have e3 : (G₀ + ΛV * ‖x‖) * |A| ≤ (|G₀| + |ΛV|) * (1 + ‖x‖) * |A| :=
        mul_le_mul_of_nonneg_right e2 (abs_nonneg _)
      nlinarith [e1, e3]
    calc |D.invβ * Laplacian.laplacian (f u) x - inner ℝ (gradient D.V x) (gradient (f u) x)|
        ≤ |D.invβ * Laplacian.laplacian (f u) x| + |inner ℝ (gradient D.V x) (gradient (f u) x)| :=
          abs_sub _ _
      _ ≤ |D.invβ| * |CL| * (1 + ‖x‖) + (|G₀| + |ΛV|) * |A| * (1 + ‖x‖) := add_le_add hb1 hb2
      _ = (|D.invβ| * |CL| + (|G₀| + |ΛV|) * |A|) * (1 + ‖x‖) := by ring
  -- (iii)
  have hcomb : ContinuousOn (fun p : ℝ × ℝ =>
      Whole.pair (Whole.withDensityReal (ρ p.2)) (fun x => D.invβ * Laplacian.laplacian (f p.1) x
        - inner ℝ (gradient D.V x) (gradient (f p.1) x))
      + (1 / 2 : ℝ) * ∫ x, ρ p.2 x * ∫ y, ρ p.2 y * pairKernelRd D (f p.1) x y)
      (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) :=
    (db2_pair_joint h ht (fun a x => D.invβ * Laplacian.laplacian (f a) x
      - inner ℝ (gradient D.V x) (gradient (f a) x)) hφc hφg).add
      (continuousOn_const.mul (db2_H_contOn h ht hf))
  refine ContinuousOn.congr hcomb (fun p hp => ?_)
  have hρp : Whole.IsProbDensity (ρ p.2) := h.hρ.density p.2 (hsub hp.2)
  rw [db1_mfGen_eq D hρp, Q09A.pair_withDensityReal hρp]

end HRS.MH.DualityRd
