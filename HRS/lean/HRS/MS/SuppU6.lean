import HRS.MS.SuppU6Aux8
import HRS.Whole.CriticalNoise

/-!
# Worker U6: proof of `HRS.Whole.adapted_charts` (frozen in `HRS/Whole/CriticalNoise.lean`)

Route.  Charts `F_x(u) = x + A_x u`, `A_x = 1 - γ(|x|²) x xᵀ` (radial scale `⟨x⟩⁻¹`, angular scale `1`),
with inverse `B_x = 1 + δ(|x|²) x xᵀ`, `‖B_x v‖² = ‖v‖² + ⟪x,v⟫²`, `det A_x = ⟨x⟩⁻¹`.
A maximal `1/16`-separated set `S` for the relation "`|x-y| ≥ ε` or `||x|²-|y|²| ≥ ε`" (Zorn) gives
centres; the cover property and the uniform volume count (`u6_count`) give a locally finite family
of bumps `ψ_k = ψ ∘ F_k⁻¹`, `Ψ = ∑ ψ_k² ≥ 1`, `χ_k = ψ_k G(Ψ)` with `G(t) = t^{-1/2}` on `[1,∞)`.
Uniform derivative bounds: the transition maps satisfy `‖B_k A_j‖ ≤ 2` for overlapping charts, and the
Faà di Bruno / Leibniz bounds of Mathlib give constants independent of `j`.
-/

noncomputable section

open MeasureTheory Metric

namespace HRS.Whole

open HRS.U6

variable {d : ℕ}

lemma u6_cube_norm_le {u : Euc d} (hu : u ∈ chartCube d) : ‖u‖ ≤ (d : ℝ) := by
  have h1 : ∀ i, ‖u.ofLp i‖ ^ 2 ≤ 1 / 4 := by
    intro i
    have := hu i
    rw [Real.norm_eq_abs, sq_abs]
    nlinarith [abs_nonneg (u.ofLp i), sq_abs (u.ofLp i)]
  have h2 : ‖u‖ ^ 2 ≤ (d : ℝ) / 4 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖u.ofLp i‖ ^ 2 ≤ ∑ _i : Fin d, (1 / 4 : ℝ) := Finset.sum_le_sum (fun i _ => h1 i)
      _ = (d : ℝ) / 4 := by simp [div_eq_inv_mul]; ring
  have h3 : (d : ℝ) / 4 ≤ (d : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ d := by exact_mod_cast h
      nlinarith
  exact le_of_sq_le_sq (h2.trans h3) (Nat.cast_nonneg d)

lemma u6_closedBall_subset_interior (d : ℕ) :
    Metric.closedBall (0 : Euc d) (1 / 4) ⊆ interior (chartCube d) := by
  have hopen : IsOpen {u : Euc d | ∀ i, |u.ofLp i| < 1 / 2} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt
      (continuous_abs.comp (EuclideanSpace.proj i).continuous) continuous_const)
  have hsub : {u : Euc d | ∀ i, |u.ofLp i| < 1 / 2} ⊆ chartCube d := fun u hu i => (hu i).le
  refine fun u hu => interior_maximal hsub hopen ?_
  intro i
  have h1 := PiLp.norm_apply_le u i
  rw [Real.norm_eq_abs] at h1
  rw [mem_closedBall, dist_zero_right] at hu
  linarith

lemma u6_density {q c C : ℝ} (hc : 0 < c) {ρ : Euc d → ℝ}
    (hρ : ∀ x, c * Real.exp (-q * ‖x‖ ^ 2 / 2) ≤ ρ x ∧ ρ x ≤ C * Real.exp (-q * ‖x‖ ^ 2 / 2))
    (hq : 0 < q) {M : ℝ} (x y : Euc d) (h : |‖y‖ ^ 2 - ‖x‖ ^ 2| ≤ M) :
    (c / C) * Real.exp (-q * M / 2) * ρ x ≤ ρ y ∧
      ρ y ≤ (C / c) * Real.exp (q * M / 2) * ρ x := by
  have hC : 0 < C := by
    have := hρ 0
    have h0 := Real.exp_pos (-q * ‖(0 : Euc d)‖ ^ 2 / 2)
    nlinarith [this.1, this.2]
  have hab := abs_le.mp h
  obtain ⟨hx1, hx2⟩ := hρ x
  obtain ⟨hy1, hy2⟩ := hρ y
  constructor
  · -- ρ y ≥ c e^{-q|y|²/2} ≥ c e^{-qM/2} e^{-q|x|²/2} ≥ (c/C) e^{-qM/2} ρ x
    have e1 : Real.exp (-q * M / 2) * Real.exp (-q * ‖x‖ ^ 2 / 2) ≤ Real.exp (-q * ‖y‖ ^ 2 / 2) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
    have e2 : (c / C) * Real.exp (-q * M / 2) * ρ x ≤ c * (Real.exp (-q * M / 2) *
        Real.exp (-q * ‖x‖ ^ 2 / 2)) := by
      have : (c / C) * ρ x ≤ c * Real.exp (-q * ‖x‖ ^ 2 / 2) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hC]
        nlinarith [hx2]
      have hE := Real.exp_pos (-q * M / 2)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left e1 hc.le]
  · have e1 : Real.exp (-q * ‖y‖ ^ 2 / 2) ≤ Real.exp (q * M / 2) * Real.exp (-q * ‖x‖ ^ 2 / 2) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
    have e2 : C * (Real.exp (q * M / 2) * Real.exp (-q * ‖x‖ ^ 2 / 2)) ≤
        (C / c) * Real.exp (q * M / 2) * ρ x := by
      have : C * Real.exp (-q * ‖x‖ ^ 2 / 2) ≤ (C / c) * ρ x := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hc]
        nlinarith [hx1]
      have hE := Real.exp_pos (q * M / 2)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left e1 hC.le]

theorem u6_adapted_charts_main : type_of% @HRS.Whole.adapted_charts := by
  intro d hd q c C hq hc ρ hρ
  obtain ⟨S, hS, hcov⟩ := u6_exists_net (d := d) (1 / 16) (by norm_num)
  have hcount : Countable S := by
    have hc' : S.PairwiseDisjoint (fun x : Euc d => {y | ‖u6Fi x y‖ < 1 / 128}) := by
      intro x hx x' hx' hne
      rw [Function.onFun, Set.disjoint_left]
      intro y hy hy'
      have h1 : u6F x (u6Fi x y) = u6F x' (u6Fi x' y) := by rw [u6F_Fi, u6F_Fi]
      exact u6_not_sep_of_overlap (ε := 1 / 16) (ρ := 1 / 128) (by norm_num) (by norm_num) h1
        (le_of_lt hy) (le_of_lt hy') (hS hx hx' hne)
    exact (Set.PairwiseDisjoint.countable_of_isOpen hc'
      (fun x _ => isOpen_lt (continuous_u6Fi x).norm continuous_const)
      (fun x _ => ⟨x, by simp [u6Fi]⟩)).to_subtype
  refine ⟨S, hcount, fun j => j.1, fun j => u6A j.1, u6chi S, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    refine ⟨u6chi_contDiff hS j, ?_⟩
    exact (u6chi_tsupport j).trans (Set.image_mono (u6_closedBall_subset_interior d))
  · exact fun x => u6chi_sum hS hcov x
  · exact ⟨1, fun j => opNorm_u6A_le j.1⟩
  · refine ⟨1, 1, one_pos, fun j => ?_⟩
    have h1 : |LinearMap.det (u6A j.1 : Euc d →ₗ[ℝ] Euc d)| = jbracket j.1 ^ (-1 : ℝ) := by
      rw [u6_det, Real.rpow_neg_one]
      show |1 / u6j j.1| = (u6j j.1)⁻¹
      have hp := u6j_pos j.1
      rw [abs_of_nonneg (by positivity), one_div]
    show 1 * jbracket j.1 ^ (-1 : ℝ) ≤ |LinearMap.det (u6A j.1 : Euc d →ₗ[ℝ] Euc d)| ∧
      |LinearMap.det (u6A j.1 : Euc d →ₗ[ℝ] Euc d)| ≤ 1 * jbracket j.1 ^ (-1 : ℝ)
    rw [h1, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  · intro l
    obtain ⟨Cl, hCl⟩ := u6_chart_deriv_bound hS l
    exact ⟨Cl, fun j u => hCl j u⟩
  · obtain ⟨K, hK⟩ := u6_count_sub (d := d) (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num) hS
      (d : ℝ) 0 (Nat.cast_nonneg d) le_rfl
    refine ⟨K, fun x => ?_⟩
    refine (hK x _ ?_).2
    rintro k ⟨u, hu, hux⟩
    refine ⟨u, 0, u6_cube_norm_le hu, by simp, ?_⟩
    simp only [u6F, map_zero, add_zero]
    exact hux
  · -- density comparison
    set R : ℝ := (d : ℝ) with hR
    set Mq : ℝ := 2 * R + R ^ 2 with hMq
    refine ⟨(c / C) * Real.exp (-q * Mq / 2), (C / c) * Real.exp (q * Mq / 2), ?_, fun j u hu => ?_⟩
    · have hC : 0 < C := by
        have := hρ 0
        have h0 := Real.exp_pos (-q * ‖(0 : Euc d)‖ ^ 2 / 2)
        nlinarith [this.1, this.2]
      positivity
    · have hb : |‖j.1 + u6A j.1 u‖ ^ 2 - ‖j.1‖ ^ 2| ≤ Mq := by
        have := abs_normsq_u6F j.1 u
        have hn := u6_cube_norm_le hu
        have h1 : 2 * ‖u‖ + ‖u‖ ^ 2 ≤ Mq := by
          rw [hMq, hR]; gcongr
        exact (this.trans h1)
      have hdens := u6_density hc hρ hq j.1 (j.1 + u6A j.1 u) hb
      have hdet : 0 ≤ |LinearMap.det (u6A j.1 : Euc d →ₗ[ℝ] Euc d)| := abs_nonneg _
      constructor
      · have := mul_le_mul_of_nonneg_right hdens.1 hdet
        simpa [mul_assoc] using this
      · have := mul_le_mul_of_nonneg_right hdens.2 hdet
        simpa [mul_assoc] using this
  · intro p hp
    have := u6_summable_jbracket hS hp
    exact this

end HRS.Whole

/-- Worker U6: the frozen statement `HRS.Whole.adapted_charts`. -/
theorem adapted_charts_proof : type_of% @HRS.Whole.adapted_charts :=
  HRS.Whole.u6_adapted_charts_main
