import HRS.MS.SA12CompB3
import HRS.MS.SA12CompB3Z
import HRS.Whole.AppendixAAdjoint

/-!
# S.A.12 B4, part A: joint continuity of the density path

From the weak continuity of `r ↦ μ^r` and the uniform Lipschitz bound of the slices (the `C_b^{m+3}` part of
`CoeffHypRd`), `(r, x) ↦ μ^r(x)` is jointly continuous on `[0,T] × ℝ^d` (mollify at scale `δ`, weak continuity of the
mollified path, Lipschitz error `O(δ)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Companions

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem sa12z_lip_of_cb {r : ℕ} (hr : 1 ≤ r) {f : Euc d → ℝ} (hf : MemCb r f) (x y : Euc d) :
    |f x - f y| ≤ cbNorm r f * ‖x - y‖ := by
  have hdf : Differentiable ℝ f := hf.1.differentiable (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hr))
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := f) (C := cbNorm r f)
    (s := Set.univ) (x := y) (y := x) (fun z _ => hdf z) (fun z _ => ?_) convex_univ
    (Set.mem_univ _) (Set.mem_univ _)
  · simpa [Real.norm_eq_abs, norm_sub_rev] using h
  · rw [← norm_iteratedFDeriv_one]
    exact sa12z_norm_iteratedFDeriv_le_cbNorm hf hr z

theorem sa12z_cb_nonneg {r : ℕ} {f : Euc d → ℝ} (hf : MemCb r f) : 0 ≤ cbNorm r f := by
  unfold cbNorm
  exact Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

/-- Pointwise continuity in time of a weakly continuous path of uniformly Lipschitz functions. -/
theorem sa12z_density_time_cont {T L : ℝ} (hL : 0 ≤ L) {μ : ℝ → Euc d → ℝ}
    (hlip : ∀ r ∈ Icc (0 : ℝ) T, ∀ x y : Euc d, |μ r x - μ r y| ≤ L * ‖x - y‖)
    (hcont : ∀ r ∈ Icc (0 : ℝ) T, Continuous (μ r))
    (hint : ∀ r ∈ Icc (0 : ℝ) T, ∀ ψ : Euc d → ℝ, Continuous ψ → HasCompactSupport ψ →
      Integrable (fun y => ψ y * μ r y))
    (hweak : ∀ ψ : Euc d → ℝ, Continuous ψ → (∃ B, ∀ x, |ψ x| ≤ B) →
      ContinuousOn (fun r => ∫ x, ψ x * μ r x) (Icc (0 : ℝ) T))
    (hprob : ∀ r ∈ Icc (0 : ℝ) T, ∀ x, 0 ≤ μ r x) (x₀ : Euc d) :
    ContinuousOn (fun r => μ r x₀) (Icc (0 : ℝ) T) := by
  intro r₀ hr₀
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set ρ0 : ℝ := ε / (4 * (L + 1)) with hρ0
  have hρ0pos : 0 < ρ0 := by positivity
  let f : ContDiffBump (0 : Euc d) := ⟨ρ0 / 2, ρ0, half_pos hρ0pos, half_lt_self hρ0pos⟩
  set η : Euc d → ℝ := f.normed volume with hη
  have hηc : Continuous η := f.continuous_normed
  have hηs : HasCompactSupport η := f.hasCompactSupport_normed
  have hη0 : ∀ z, 0 ≤ η z := fun z => f.nonneg_normed z
  have hη1 : ∫ z, η z = 1 := f.integral_normed
  have hηint : Integrable η := f.integrable_normed
  have hηsupp : ∀ z, η z ≠ 0 → ‖z‖ < ρ0 := by
    intro z hz
    have : z ∈ Function.support η := hz
    rw [hη, ContDiffBump.support_normed_eq] at this
    simpa using this
  set ψ : Euc d → ℝ := fun y => η (x₀ - y) with hψ
  have hψc : Continuous ψ := hηc.comp (continuous_const.sub continuous_id)
  have hψs : HasCompactSupport ψ := by
    have := hηs.comp_homeomorph ((Homeomorph.neg (Euc d)).trans (Homeomorph.addLeft x₀))
    exact this
  obtain ⟨Bψ, hBψ⟩ : ∃ B, ∀ x, |ψ x| ≤ B := by
    obtain ⟨B, hB⟩ := hψc.bounded_above_of_compact_support hψs
    exact ⟨B, fun x => by simpa [Real.norm_eq_abs] using hB x⟩
  have hψ1 : ∫ y, ψ y = 1 := by
    rw [← hη1]
    exact integral_sub_left_eq_self η volume x₀
  -- the error of the mollified value
  have herr : ∀ r ∈ Icc (0 : ℝ) T, |(∫ y, ψ y * μ r y) - μ r x₀| ≤ L * ρ0 := by
    intro r hr
    have h1 : Integrable (fun y => ψ y * μ r y) := hint r hr ψ hψc hψs
    have h2 : Integrable (fun y => ψ y * μ r x₀) := (hψc.integrable_of_hasCompactSupport hψs).mul_const _
    have e : (∫ y, ψ y * μ r y) - μ r x₀ = ∫ y, ψ y * (μ r y - μ r x₀) := by
      have : ∫ y, ψ y * (μ r y - μ r x₀) = (∫ y, ψ y * μ r y) - ∫ y, ψ y * μ r x₀ := by
        simp_rw [mul_sub]
        exact integral_sub h1 h2
      rw [this, integral_mul_const, hψ1, one_mul]
    rw [e]
    have hb : ∀ y, ‖ψ y * (μ r y - μ r x₀)‖ ≤ ψ y * (L * ρ0) := by
      intro y
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hη0 _)]
      by_cases hy : η (x₀ - y) = 0
      · simp [hψ, hy]
      · have hn := hηsupp _ hy
        have hlip' := hlip r hr y x₀
        refine mul_le_mul_of_nonneg_left ?_ (hη0 _)
        rw [Real.norm_eq_abs]
        refine hlip'.trans (mul_le_mul_of_nonneg_left ?_ hL)
        rw [norm_sub_rev] at hn
        exact hn.le
    have hbint : Integrable (fun y => ψ y * (L * ρ0)) := (hψc.integrable_of_hasCompactSupport hψs).mul_const _
    calc |∫ y, ψ y * (μ r y - μ r x₀)| = ‖∫ y, ψ y * (μ r y - μ r x₀)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ y, ψ y * (L * ρ0) := norm_integral_le_of_norm_le hbint (Eventually.of_forall hb)
      _ = L * ρ0 := by rw [integral_mul_const, hψ1, one_mul]
  have hcJ := hweak ψ hψc ⟨Bψ, hBψ⟩ r₀ hr₀
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds] at hcJ
  obtain ⟨δ, hδ, hδ'⟩ := hcJ (ε / 4) (by positivity)
  refine ⟨δ, hδ, fun r hr hdist => ?_⟩
  have hJ := hδ' hr hdist
  rw [Real.dist_eq] at hJ ⊢
  have e1 := herr r hr
  have e2 := herr r₀ hr₀
  have hLρ : L * ρ0 ≤ ε / 4 := by
    rw [hρ0]
    have : L * (ε / (4 * (L + 1))) = ε / 4 * (L / (L + 1)) := by field_simp
    rw [this]
    have h3 : L / (L + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  have e1' : |μ r x₀ - ∫ y, ψ y * μ r y| ≤ L * ρ0 := by rw [abs_sub_comm]; exact e1
  have htri : |μ r x₀ - μ r₀ x₀| ≤ |μ r x₀ - ∫ y, ψ y * μ r y| +
      (|(∫ y, ψ y * μ r y) - ∫ y, ψ y * μ r₀ y| + |(∫ y, ψ y * μ r₀ y) - μ r₀ x₀|) := by
    calc |μ r x₀ - μ r₀ x₀| = |(μ r x₀ - ∫ y, ψ y * μ r y) + (((∫ y, ψ y * μ r y) - ∫ y, ψ y * μ r₀ y) +
          ((∫ y, ψ y * μ r₀ y) - μ r₀ x₀))| := by congr 1; ring
      _ ≤ _ := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
  linarith

/-- Joint continuity of the density path. -/
theorem sa12z_density_joint_cont {s : ℝ} {m : ℕ} {Λ T : ℝ} {μ : ℝ → Euc d → ℝ}
    (hμ : CoeffHypRd s m Λ T μ) :
    ContinuousOn (fun q : ℝ × Euc d => μ q.1 q.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  have hcb : ∀ r ∈ Icc (0 : ℝ) T, MemCb (m + 3) (μ r) ∧ cbNorm (m + 3) (μ r) ≤ Λ := by
    intro r hr
    obtain ⟨h1, -, h3⟩ := hμ.regular.1 r hr
    refine ⟨h1, ?_⟩
    have : 0 ≤ (weightedSupE (m + 3) ((d : ℝ) + 3) (μ r)).toReal := ENNReal.toReal_nonneg
    linarith
  set L : ℝ := max Λ 0 with hL
  have hL0 : 0 ≤ L := le_max_right _ _
  have hlip : ∀ r ∈ Icc (0 : ℝ) T, ∀ x y : Euc d, |μ r x - μ r y| ≤ L * ‖x - y‖ := by
    intro r hr x y
    refine (sa12z_lip_of_cb (r := m + 3) (by omega) (hcb r hr).1 x y).trans ?_
    exact mul_le_mul_of_nonneg_right ((hcb r hr).2.trans (le_max_left _ _)) (norm_nonneg _)
  have hcont : ∀ r ∈ Icc (0 : ℝ) T, Continuous (μ r) := fun r hr => (hcb r hr).1.1.continuous
  have hint : ∀ r ∈ Icc (0 : ℝ) T, ∀ ψ : Euc d → ℝ, Continuous ψ → HasCompactSupport ψ →
      Integrable (fun y => ψ y * μ r y) := fun r hr ψ hψ hψs =>
    (hψ.mul (hcont r hr)).integrable_of_hasCompactSupport hψs.mul_right
  have hweak := hμ.cont
  have hprob : ∀ r ∈ Icc (0 : ℝ) T, ∀ x, 0 ≤ μ r x := fun r hr x => (hμ.prob r hr).nonneg x
  have htime := fun x₀ => sa12z_density_time_cont hL0 hlip hcont hint hweak hprob x₀
  intro p hp
  obtain ⟨r₀, x₀⟩ := p
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := (Metric.continuousWithinAt_iff.1 (htime x₀ r₀ hp.1)) (ε / 2) (half_pos hε)
  refine ⟨min δ₁ (ε / (2 * (L + 1))), by positivity, ?_⟩
  rintro ⟨r, x⟩ ⟨hr, -⟩ hdist
  have hm : max (dist r r₀) (dist x x₀) < min δ₁ (ε / (2 * (L + 1))) := by rwa [Prod.dist_eq] at hdist
  have h1 : dist r r₀ < δ₁ := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hm) (min_le_left _ _)
  have h2 : dist x x₀ < ε / (2 * (L + 1)) :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hm) (min_le_right _ _)
  have ht := hδ₁' hr h1
  rw [Real.dist_eq] at ht ⊢
  have hx := hlip r hr x x₀
  rw [dist_eq_norm] at h2
  have hLx : L * ‖x - x₀‖ < ε / 2 := by
    have : L * ‖x - x₀‖ ≤ L * (ε / (2 * (L + 1))) := mul_le_mul_of_nonneg_left h2.le hL0
    have h4 : L * (ε / (2 * (L + 1))) = ε / 2 * (L / (L + 1)) := by field_simp
    have h3 : L / (L + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  calc |μ r x - μ r₀ x₀| = |(μ r x - μ r x₀) + (μ r x₀ - μ r₀ x₀)| := by congr 1; ring
    _ ≤ |μ r x - μ r x₀| + |μ r x₀ - μ r₀ x₀| := abs_add_le _ _
    _ < ε := by linarith

end HRS.MH.AdjointRd.Phase2SA12Companions
