import HRS.MC.L5566Aux1

/-!
# Packet L5566, auxiliary 2: the lift is `C¹` off the integer lattice

`G(y)(cos(2π y_i) - 1) = F_i(y)` with `F_i = ∑ (a(k - e_i) - a(k)) cos(2π k·y)` a `C¹` series.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MC.L5566

open HRS

variable {d : ℕ}

lemma l5566_lift_eq (s c : ℝ) (y : Euc d) :
    Torus.lift (negSpectralKernel d s c) y =
      ∑' k : Lattice d, negSpectralCoeff d s c k * Real.cos (2 * Real.pi * Lattice.dot k y) := by
  simp [Torus.lift, negSpectralKernel, Torus.cosMode_mk]

/-- the difference series -/
def l5566_F (d : ℕ) (s c : ℝ) (i : Fin d) (y : Euc d) : ℝ :=
  ∑' k : Lattice d, (negSpectralCoeff d s c (k - Pi.single i (1 : ℤ)) - negSpectralCoeff d s c k) *
    Real.cos (2 * Real.pi * Lattice.dot k y)

lemma l5566_dot_add_single (k : Lattice d) (i : Fin d) (y : Euc d) :
    Lattice.dot (k + Pi.single i (1 : ℤ)) y = Lattice.dot k y + y i := by
  simp [Lattice.dot, add_mul, Finset.sum_add_distrib, Pi.single_apply]

lemma l5566_summable_a {s : ℝ} (hs : s < 0) (c : ℝ) (i : Fin d) (f : Lattice d → ℝ)
    (hf : ∀ k, |f k| ≤ 1) :
    Summable fun k : Lattice d => negSpectralCoeff d s c k * f k := by
  refine Summable.of_norm_bounded (summable_negSpectralCoeff d hs c).norm (fun k => ?_)
  rw [norm_mul]
  calc ‖negSpectralCoeff d s c k‖ * ‖f k‖ ≤ ‖negSpectralCoeff d s c k‖ * 1 := by
        gcongr; simpa using hf k
    _ = _ := mul_one _

lemma l5566_summable_u {s c : ℝ} (hs : s < 0) (hc : 0 < c) (i : Fin d) :
    Summable fun k : Lattice d =>
      |negSpectralCoeff d s c (k - Pi.single i (1 : ℤ)) - negSpectralCoeff d s c k| *
        (2 * Real.pi * Lattice.enorm k) := by
  have hg := (summable_negSpectralCoeff d hs c).mul_left
    (|s - d| * 2 ^ (1 - (s - d)) * (2 * Real.pi))
  refine Summable.of_norm_bounded_eventually hg ?_
  have hfin : {k : Lattice d | ¬ (2 ≤ Lattice.enorm k)}.Finite := by
    refine (Set.Finite.subset (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-2 : ℤ) 2)).finite_toSet ?_)
    intro k hk
    simp only [Set.mem_setOf_eq, not_le] at hk
    simp only [Finset.coe_sort_coe, Fintype.coe_piFinset, Set.mem_pi, Set.mem_univ, Finset.coe_Icc,
      Set.mem_Icc, forall_true_left]
    intro j
    have h1 : |(k j : ℝ)| ≤ Lattice.enorm k := by
      have := NegHess.abs_coord_le_enorm k j
      exact this
    have h2 : |(k j : ℝ)| < 2 := lt_of_le_of_lt h1 hk
    have h3 : |k j| < 2 := by exact_mod_cast h2
    constructor <;> linarith [abs_lt.mp h3]
  have : ∀ᶠ k : Lattice d in cofinite, 2 ≤ Lattice.enorm k := by
    rw [Filter.eventually_cofinite]; exact hfin
  filter_upwards [this] with k hk
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact l5566_b_bound hs hc i k hk

lemma l5566_F_differentiable {s c : ℝ} (hs : s < 0) (hc : 0 < c) (i : Fin d) :
    Differentiable ℝ (l5566_F d s c i) := by
  set b : Lattice d → ℝ := fun k =>
    negSpectralCoeff d s c (k - Pi.single i (1 : ℤ)) - negSpectralCoeff d s c k with hb
  have hu : Summable fun k : Lattice d => |b k| * (2 * Real.pi * Lattice.enorm k) :=
    l5566_summable_u hs hc i
  have hf : ∀ (k : Lattice d) (y : Euc d),
      HasFDerivAt (fun y : Euc d => b k * Real.cos (2 * Real.pi * Lattice.dot k y))
        ((b k * (-Real.sin (2 * Real.pi * Lattice.dot k y))) • Torus.freqFunctional k) y := by
    intro k y
    have h1 : HasFDerivAt (fun y : Euc d => Real.cos (Torus.freqFunctional k y))
        (-Real.sin (Torus.freqFunctional k y) • Torus.freqFunctional k) y :=
      (Real.hasDerivAt_cos _).comp_hasFDerivAt y (Torus.freqFunctional k).hasFDerivAt
    have h2 := h1.const_mul (b k)
    simp only [Torus.freqFunctional_apply] at h2
    convert h2 using 1
    rw [smul_smul]
  have hbd : ∀ (k : Lattice d) (y : Euc d),
      ‖(b k * (-Real.sin (2 * Real.pi * Lattice.dot k y))) • Torus.freqFunctional k‖ ≤
        |b k| * (2 * Real.pi * Lattice.enorm k) := by
    intro k y
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg]
    have hf := Torus.norm_freqFunctional_le k
    have hs1 := Real.abs_sin_le_one (2 * Real.pi * Lattice.dot k y)
    calc |b k| * |Real.sin (2 * Real.pi * Lattice.dot k y)| * ‖Torus.freqFunctional k‖
        ≤ |b k| * 1 * (2 * Real.pi * Lattice.enorm k) := by gcongr
      _ = _ := by ring
  exact differentiable_tsum hu hf hbd

lemma l5566_continuous_lift {s : ℝ} (hs : s < 0) (c : ℝ) :
    Continuous (Torus.lift (negSpectralKernel d s c)) := by
  have : Torus.lift (negSpectralKernel d s c) = fun y =>
      ∑' k : Lattice d, negSpectralCoeff d s c k * Real.cos (2 * Real.pi * Lattice.dot k y) :=
    funext (l5566_lift_eq s c)
  rw [this]
  refine continuous_tsum (u := fun k => ‖negSpectralCoeff d s c k‖)
    (fun k => ?_) (summable_negSpectralCoeff d hs c).norm (fun k y => ?_)
  · have : Continuous (fun y : Euc d => Lattice.dot k y) := by
      unfold Lattice.dot; fun_prop
    fun_prop
  · rw [norm_mul]
    calc ‖negSpectralCoeff d s c k‖ * ‖Real.cos (2 * Real.pi * Lattice.dot k y)‖
        ≤ ‖negSpectralCoeff d s c k‖ * 1 := by
          gcongr; simpa using Real.abs_cos_le_one _
      _ = _ := mul_one _

/-- the key identity -/
lemma l5566_identity {s : ℝ} (hs : s < 0) (c : ℝ) (i : Fin d) (y : Euc d) :
    Torus.lift (negSpectralKernel d s c) y * (Real.cos (2 * Real.pi * y i) - 1) =
      l5566_F d s c i y := by
  set a := negSpectralCoeff d s c with ha
  set e : Lattice d := Pi.single i (1 : ℤ) with he
  set θ : Lattice d → ℝ := fun k => 2 * Real.pi * Lattice.dot k y with hθ
  set φ : ℝ := 2 * Real.pi * y i with hφ
  have hG : Torus.lift (negSpectralKernel d s c) y = ∑' k, a k * Real.cos (θ k) :=
    l5566_lift_eq s c y
  have hcosb : ∀ k, |Real.cos (θ k)| ≤ 1 := fun k => Real.abs_cos_le_one _
  have hsinb : ∀ k, |Real.sin (θ k)| ≤ 1 := fun k => Real.abs_sin_le_one _
  have hsC : Summable fun k => a k * Real.cos (θ k) := l5566_summable_a hs c i _ hcosb
  have hsS : Summable fun k => a k * Real.sin (θ k) := l5566_summable_a hs c i _ hsinb
  -- the sine series vanishes
  have hS : ∑' k, a k * Real.sin (θ k) = 0 := by
    have h1 : ∑' k, a (-k) * Real.sin (θ (-k)) = ∑' k, a k * Real.sin (θ k) :=
      (Equiv.neg (Lattice d)).tsum_eq (fun k => a k * Real.sin (θ k))
    have h2 : ∀ k : Lattice d, a (-k) * Real.sin (θ (-k)) = -(a k * Real.sin (θ k)) := by
      intro k
      have : θ (-k) = -θ k := by
        simp only [hθ, Lattice.dot, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
        ring
      have hn : a (-k) = a k := l5566_coeff_neg s c k
      rw [this, Real.sin_neg, hn]; ring
    simp_rw [h2] at h1
    rw [tsum_neg] at h1
    linarith
  -- shift
  have hshift : ∑' k, a k * Real.cos (θ (k + e)) = ∑' k, a (k - e) * Real.cos (θ k) := by
    have := (Equiv.addRight e).tsum_eq (fun k => a (k - e) * Real.cos (θ k))
    simpa using this
  have hθe : ∀ k, θ (k + e) = θ k + φ := by
    intro k
    simp only [hθ, hφ, he, l5566_dot_add_single]; ring
  have hexp : ∀ k, a k * Real.cos (θ (k + e)) =
      Real.cos φ * (a k * Real.cos (θ k)) - Real.sin φ * (a k * Real.sin (θ k)) := by
    intro k
    rw [hθe, Real.cos_add]; ring
  simp_rw [hexp] at hshift
  rw [(hsC.mul_left _).tsum_sub (hsS.mul_left _), tsum_mul_left, tsum_mul_left, hS, ← hG] at hshift
  have hsh : Summable fun k => a (k - e) * Real.cos (θ k) := by
    have h0 : Summable fun k => a k * Real.cos (θ (k + e)) :=
      l5566_summable_a hs c i _ (fun k => Real.abs_cos_le_one _)
    have := (Equiv.addRight e).summable_iff (f := fun k => a (k - e) * Real.cos (θ k))
    refine this.mp ?_
    simpa [Function.comp_def] using h0
  have hF : l5566_F d s c i y = ∑' k, (a (k - e) * Real.cos (θ k) - a k * Real.cos (θ k)) := by
    unfold l5566_F
    exact tsum_congr (fun k => by simp only [ha, he, hθ]; ring)
  rw [hF, hsh.tsum_sub hsC, ← hshift, ← hG]
  ring

end HRS.MC.L5566
