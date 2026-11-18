import HRS.Main.A9Aux30

/-!
# Packet A9, part 31: weak convergence from `d_{C²}`-closeness to a convergent sequence

`a9_weak_of_dc2`: on `H = NegSobolev d m`, if `smoothDist 2 (μ_n) (λ_n) → 0` and `λ_n → λ_∞` in law, then
`μ_n → λ_∞` in law.  Proof: bounded Lipschitz test functions `g` are approximated by `g ∘ P_E` (finite rank
projection, the error controlled by the cylinder tail tests `1 - exp(-θ ‖Q_E x‖²)`, which lie in a scaled
`C_b²` unit ball), and the finite-dimensional marginals converge by Lévy (`a9_fd_converges`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace BoundedContinuousFunction

namespace HRS.Main.A9

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.Main

variable {d : ℕ} {m : ℝ}

theorem a9_pt_bound (E : Finset (NonzeroLattice d)) {C L δ : ℝ} (hδ : 0 < δ) (hC0 : 0 ≤ C)
    (hL0 : 0 ≤ L) (g : NegSobolev d m → ℝ) (hC : ∀ x y, |g x - g y| ≤ C)
    (hL : ∀ x y, |g x - g y| ≤ L * ‖x - y‖) (x : NegSobolev d m) :
    |g x - g (x - a9QE m E x)| ≤ L * δ + 2 * C * a9psi (1 / δ ^ 2) (a9QE m E x) := by
  set r := ‖a9QE m E x‖ with hr
  have h1 := hL x (x - a9QE m E x)
  rw [sub_sub_cancel] at h1
  have hψ0 := a9psi_nonneg (1 / δ ^ 2) (by positivity) (a9QE m E x)
  rcases le_or_gt r δ with h | h
  · have : L * r ≤ L * δ := mul_le_mul_of_nonneg_left h hL0
    nlinarith [mul_nonneg hC0 hψ0]
  · have h2 := hC x (x - a9QE m E x)
    have hθ : 1 ≤ 1 / δ ^ 2 * r ^ 2 := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
      nlinarith
    have he : Real.exp (-(1 / δ ^ 2 * r ^ 2)) ≤ 1 / 2 := by
      have h3 : Real.exp (-(1 / δ ^ 2 * r ^ 2)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
      have h4 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
      have h5 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
      have h6 : (Real.exp 1)⁻¹ ≤ 1 / 2 := by
        rw [one_div]; exact inv_anti₀ (by norm_num) h5
      linarith
    have hψ : 1 / 2 ≤ a9psi (1 / δ ^ 2) (a9QE m E x) := by
      unfold a9psi; rw [← hr]; linarith
    have : 0 ≤ L * δ := by positivity
    nlinarith

theorem a9_int_pt (E : Finset (NonzeroLattice d)) {C L δ : ℝ} (hδ : 0 < δ) (hC0 : 0 ≤ C)
    (hL0 : 0 ≤ L) (g : NegSobolev d m → ℝ) (hgc : Continuous g) (hC : ∀ x y, |g x - g y| ≤ C)
    (hL : ∀ x y, |g x - g y| ≤ L * ‖x - y‖) (ν : Measure (NegSobolev d m))
    [IsProbabilityMeasure ν] :
    |∫ x, g x ∂ν - ∫ x, g (x - a9QE m E x) ∂ν| ≤
      L * δ + 2 * C * ∫ x, a9psi (1 / δ ^ 2) (a9QE m E x) ∂ν := by
  have hgb : ∀ x, |g x| ≤ |g 0| + C := fun x => by
    have := hC x 0
    have := abs_sub_abs_le_abs_sub (g x) (g 0)
    linarith
  have hg1 : Integrable g ν := Integrable.of_bound hgc.aestronglyMeasurable (|g 0| + C)
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hgb x)
  have hcQ : Continuous fun x : NegSobolev d m => x - a9QE m E x := continuous_id.sub (a9QE m E).continuous
  have hg2 : Integrable (fun x => g (x - a9QE m E x)) ν :=
    Integrable.of_bound (hgc.comp hcQ).aestronglyMeasurable (|g 0| + C)
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hgb _)
  have hθ : (0 : ℝ) ≤ 1 / δ ^ 2 := by positivity
  have hψc : Continuous fun x : NegSobolev d m => a9psi (1 / δ ^ 2) (a9QE m E x) := by
    unfold a9psi
    exact continuous_const.sub (Real.continuous_exp.comp
      (((continuous_const.mul ((a9QE m E).continuous.norm.pow 2))).neg))
  have hψ : Integrable (fun x => a9psi (1 / δ ^ 2) (a9QE m E x)) ν :=
    Integrable.of_bound hψc.aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (a9psi_nonneg _ hθ _)]
      exact a9psi_le_one _ hθ _)
  rw [← integral_sub hg1 hg2]
  refine (abs_integral_le_integral_abs).trans ?_
  have hmono : ∫ x, |g x - g (x - a9QE m E x)| ∂ν ≤
      ∫ x, (L * δ + 2 * C * a9psi (1 / δ ^ 2) (a9QE m E x)) ∂ν := by
    refine integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _) ?_ (ae_of_all _ fun x =>
      a9_pt_bound E hδ hC0 hL0 g hC hL x)
    exact (integrable_const _).add (hψ.const_mul _)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add (integrable_const _) (hψ.const_mul _), integral_const, integral_const_mul]
  simp

theorem a9_psiQ_continuous (E : Finset (NonzeroLattice d)) (θ : ℝ) :
    Continuous fun x : NegSobolev d m => a9psi θ (a9QE m E x) := by
  unfold a9psi
  exact continuous_const.sub (Real.continuous_exp.comp
    (((continuous_const.mul ((a9QE m E).continuous.norm.pow 2))).neg))

theorem a9_exists_small_tail (ν : Measure (NegSobolev d m)) [IsProbabilityMeasure ν] {θ η : ℝ}
    (hθ : 0 ≤ θ) (hη : 0 < η) :
    ∃ E : Finset (NonzeroLattice d), ∫ x, a9psi θ (a9QE m E x) ∂ν < η := by
  have h : Tendsto (fun E : Finset (NonzeroLattice d) => ∫ x, a9psi θ (a9QE m E x) ∂ν) atTop
      (𝓝 (∫ _x : NegSobolev d m, (0 : ℝ) ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
      (Eventually.of_forall fun E => (a9_psiQ_continuous E θ).aestronglyMeasurable)
      (Eventually.of_forall fun E => ae_of_all _ fun x => ?_) (integrable_const _)
      (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (a9psi_nonneg _ hθ _)]
      exact a9psi_le_one _ hθ _
    · have hcont : Continuous fun r : ℝ => 1 - Real.exp (-(θ * r ^ 2)) := by fun_prop
      have h0 := (hcont.tendsto 0).comp (a9QE_tendsto (m := m) x)
      have h1 : (1 : ℝ) - Real.exp (-(θ * (0 : ℝ) ^ 2)) = 0 := by simp
      rw [h1] at h0
      exact h0
  simp only [integral_zero] at h
  exact (h.eventually (gt_mem_nhds hη)).exists

theorem a9_lip_tendsto (μ lam : ℕ → Measure (NegSobolev d m)) (lam₀ : Measure (NegSobolev d m))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (lam n)]
    [IsProbabilityMeasure lam₀] (hlc : ConvergesInLaw lam lam₀)
    (hd : Tendsto (fun n => smoothDist 2 (μ n) (lam n)) atTop (𝓝 0))
    {g : NegSobolev d m → ℝ} {C : ℝ} (hC : ∀ x y, dist (g x) (g y) ≤ C) {L : ℝ≥0}
    (hL : LipschitzWith L g) :
    Tendsto (fun n => ∫ x, g x ∂(μ n)) atTop (𝓝 (∫ x, g x ∂lam₀)) := by
  have hC' : ∀ x y, |g x - g y| ≤ C := fun x y => by simpa [Real.dist_eq] using hC x y
  have hL' : ∀ x y, |g x - g y| ≤ (L : ℝ) * ‖x - y‖ := fun x y => by
    have := hL.dist_le_mul x y
    simpa [Real.dist_eq, dist_eq_norm] using this
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC' 0 0)
  have hL0 : (0 : ℝ) ≤ L := L.2
  rw [Metric.tendsto_nhds]
  intro ε hε
  set Lr : ℝ := (L : ℝ) with hLr
  have hC1 : 0 < C + 1 := by linarith
  have hL1 : 0 < Lr + 1 := by linarith
  set δ : ℝ := ε / (8 * (Lr + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  set η : ℝ := ε / (16 * (C + 1)) with hη
  have hη0 : 0 < η := by positivity
  set e : ℝ := ε / (12 * (C + 1)) with he
  have he0 : 0 < e := by positivity
  set θ : ℝ := 1 / δ ^ 2 with hθ
  have hθ0 : 0 < θ := by positivity
  obtain ⟨E, hE⟩ := a9_exists_small_tail lam₀ (m := m) hθ0.le hη0
  -- the tail test along `μ n`
  have hmem : (fun z => (1 / (3 * (1 + Real.sqrt θ + 6 * θ))) * a9psi θ (a9QE m E z)) ∈
      CbUnitBall (NegSobolev d m) 2 :=
    cbUnitBall_comp_clm (a9QE m E) (a9QE_opNorm_le E) (a9psi_mem_ball θ hθ0)
  have hcpos : 0 < 1 / (3 * (1 + Real.sqrt θ + 6 * θ)) := by
    have := Real.sqrt_nonneg θ; positivity
  have tψ := a9_tendsto_of_ball (f := fun x => a9psi θ (a9QE m E x)) (a9_psiQ_continuous E θ)
    (fun z => by rw [abs_of_nonneg (a9psi_nonneg _ hθ0.le _)]; exact a9psi_le_one _ hθ0.le _)
    hcpos hmem μ lam lam₀ hlc hd
  -- the finite-dimensional marginal
  let G : (ℝ^E.card) →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun y => g (embedCLM (fun a => a9unit m (a9kE E a)) y),
      hL.continuous.comp (embedCLM (fun a => a9unit m (a9kE E a))).continuous⟩ C
    (fun y z => by simpa [Real.dist_eq] using hC _ _)
  have tG := a9_fd_converges (a9TE m E) μ lam lam₀ hlc hd G
  have hGe : ∀ x, G (a9TE m E x) = g (x - a9QE m E x) := fun x => by
    rw [a9QE_apply, sub_sub_cancel]; rfl
  simp only [hGe] at tG
  have hε3 : 0 < ε / 3 := by positivity
  filter_upwards [tG.eventually (Metric.ball_mem_nhds _ hε3),
    tψ.eventually (gt_mem_nhds (lt_add_of_pos_right (∫ x, a9psi θ (a9QE m E x) ∂lam₀) he0))]
    with n hn1 hn2
  have hA := a9_int_pt E hδ0 hC0 hL0 g hL.continuous hC' hL' (μ n)
  have hB := a9_int_pt E hδ0 hC0 hL0 g hL.continuous hC' hL' lam₀
  rw [Real.dist_eq] at hn1
  rw [Real.dist_eq]
  set a := ∫ x, g x ∂(μ n)
  set b := ∫ x, g (x - a9QE m E x) ∂(μ n)
  set c := ∫ x, g (x - a9QE m E x) ∂lam₀
  set d' := ∫ x, g x ∂lam₀
  set Hμ := ∫ x, a9psi θ (a9QE m E x) ∂(μ n)
  set Hl := ∫ x, a9psi θ (a9QE m E x) ∂lam₀
  have h1 : |a - d'| ≤ |a - b| + |b - c| + |c - d'| := by
    have := abs_add_three (a - b) (b - c) (c - d')
    simpa using this
  have hB' : |c - d'| ≤ Lr * δ + 2 * C * Hl := by rw [abs_sub_comm]; exact hB
  have hLδ : Lr * δ ≤ ε / 8 := by
    rw [hδ, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hCη : C * η ≤ ε / 16 := by
    rw [hη, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hCe : C * e ≤ ε / 12 := by
    rw [he, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hμη : Hμ ≤ η + e := by linarith
  have m1 := mul_le_mul_of_nonneg_left hμη hC0
  have m2 := mul_le_mul_of_nonneg_left hE.le hC0
  rw [mul_add] at m1
  linarith

theorem a9_weak_of_dc2 (μ lam : ℕ → Measure (NegSobolev d m)) (lam₀ : Measure (NegSobolev d m))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (lam n)]
    [IsProbabilityMeasure lam₀] (hlc : ConvergesInLaw lam lam₀)
    (hd : Tendsto (fun n => smoothDist 2 (μ n) (lam n)) atTop (𝓝 0)) :
    ConvergesInLaw μ lam₀ := by
  intro f
  let ν : ℕ → ProbabilityMeasure (NegSobolev d m) := fun n => ⟨μ n, inferInstance⟩
  let ν₀ : ProbabilityMeasure (NegSobolev d m) := ⟨lam₀, inferInstance⟩
  have h : Tendsto ν atTop (𝓝 ν₀) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    intro g ⟨C, hC⟩ ⟨L, hL⟩
    exact a9_lip_tendsto μ lam lam₀ hlc hd hC hL
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h f

end HRS.Main.A9
