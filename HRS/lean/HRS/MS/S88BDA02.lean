import HRS.MS.SuppU11Aux1
import HRS.Whole.CriticalNoise

/-!
# S8.8.A02: differentiated diagonal evolution and positive-time smoothing

`s88_diagonal_derivative`: for `ω_l ≥ lam > 0`, the diagonal semigroup `semiDiag om r z` of an `ℓ²` vector is
differentiable at every `t > 0` with `ℓ²`-derivative `(-ω_l e^{-tω_l} z_l)_l`, and for `t ≥ 1` both the value and the
derivative are bounded in `ℓ²` by `3 e^{-lam t} ‖z‖²`.  (The packet's variable `λ` is renamed `lam`, since `λ` is
the lambda-abstraction keyword in Lean 4.)
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S88Breakdown

open HRS HRS.Whole

/-- A bounded multiplier of an `ℓ²` vector stays square summable, with the expected bound. -/
lemma s88_mul_sq_summable (z : SeqL2) (g : ℕ → ℝ) {G : ℝ} (hg : ∀ l, |g l| ≤ G) :
    Summable (fun l => (g l * SeqL2.coord z l) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun l => sq_nonneg _) (fun l => ?_)
    ((u11_coord_summable z).mul_left (G ^ 2))
  rw [mul_pow]
  have : g l ^ 2 ≤ G ^ 2 := by
    rw [← sq_abs (g l)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hg l) 2
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

lemma s88_mul_exp_le (ω t : ℝ) (hω : 0 ≤ ω) (ht : 0 < t) :
    ω * Real.exp (-t * ω) ≤ 1 / t := by
  have h : t * ω + 1 ≤ Real.exp (t * ω) := Real.add_one_le_exp _
  rw [show -t * ω = -(t * ω) by ring, Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀
    (Real.exp_pos _) ht]
  nlinarith

lemma s88_exp_hasDerivAt (ω x : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s * ω)) (-ω * Real.exp (-x * ω)) x := by
  have h := (((hasDerivAt_id x).neg).mul_const ω).exp
  refine h.congr_deriv ?_
  simp
  ring

/-- Mean-value bound for the difference quotient of `s ↦ e^{-sω}` away from zero. -/
lemma s88_quot_bound (ω t h : ℝ) (hω : 0 ≤ ω) (ht : 0 < t) (hh : |h| ≤ t / 2) :
    |h⁻¹ * (Real.exp (-(t + h) * ω) - Real.exp (-t * ω))| ≤ 2 / t := by
  have hbd : ∀ x ∈ Set.Ici (t / 2), ‖-ω * Real.exp (-x * ω)‖ ≤ 2 / t := by
    intro x hx
    have hx' : t / 2 ≤ x := hx
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hω, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-x * ω) ≤ Real.exp (-(t / 2) * ω) :=
      Real.exp_le_exp.2 (by nlinarith)
    calc ω * Real.exp (-x * ω) ≤ ω * Real.exp (-(t / 2) * ω) := mul_le_mul_of_nonneg_left h1 hω
      _ ≤ 1 / (t / 2) := s88_mul_exp_le ω (t / 2) hω (by positivity)
      _ = 2 / t := by field_simp
  have hab := abs_le.1 hh
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => Real.exp (-s * ω)) (f' := fun x => -ω * Real.exp (-x * ω))
    (s := Set.Ici (t / 2)) (fun x _ => (s88_exp_hasDerivAt ω x).hasDerivWithinAt) hbd
    (convex_Ici _) (x := t) (y := t + h) (by show t / 2 ≤ t; linarith)
    (by show t / 2 ≤ t + h; linarith)
  simp only [Real.norm_eq_abs, add_sub_cancel_left] at key
  rcases eq_or_ne h 0 with h0 | h0
  · subst h0; simp; positivity
  · rw [abs_mul, abs_inv]
    have hp : 0 < |h| := abs_pos.2 h0
    calc |h|⁻¹ * |Real.exp (-(t + h) * ω) - Real.exp (-t * ω)| ≤ |h|⁻¹ * (2 / t * |h|) :=
          mul_le_mul_of_nonneg_left key (inv_nonneg.2 hp.le)
      _ = 2 / t := by field_simp

theorem s88_diagonal_derivative (om : ℕ → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hgap : ∀ l : ℕ, lam ≤ om l) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : SeqL2, ∃ v : ℝ → SeqL2,
      (∀ t : ℝ, 0 < t →
        HasDerivAt (fun r : ℝ => semiDiag om r z) (v t) t ∧
        ∀ l : ℕ, SeqL2.coord (v t) l =
          -om l * Real.exp (-t * om l) * SeqL2.coord z l) ∧
      ∀ t : ℝ, 1 ≤ t →
        ‖semiDiag om t z‖ ^ 2 + ‖v t‖ ^ 2 ≤
          D * Real.exp (-lam * t) * ‖z‖ ^ 2 := by
  have hom : ∀ l, 0 < om l := fun l => lt_of_lt_of_le hlam (hgap l)
  refine ⟨3, by norm_num, fun z => ?_⟩
  have hmemA : ∀ s : ℝ, 0 ≤ s → Memℓp (fun l => Real.exp (-s * om l) * SeqL2.coord z l) 2 :=
    fun s hs => u11_diag_memℓp om hom hs z
  have hB : ∀ s : ℝ, 0 < s → Summable (fun l => (-om l * Real.exp (-s * om l) *
      SeqL2.coord z l) ^ 2) := by
    intro s hs
    refine s88_mul_sq_summable z (fun l => -om l * Real.exp (-s * om l)) (G := 1 / s) (fun l => ?_)
    rw [neg_mul, abs_neg, abs_of_nonneg (mul_nonneg (hom l).le (Real.exp_pos _).le)]
    exact s88_mul_exp_le (om l) s (hom l).le hs
  have hmemB : ∀ s : ℝ, 0 < s → Memℓp (fun l => -om l * Real.exp (-s * om l) *
      SeqL2.coord z l) 2 := fun s hs => memℓp_two_iff.2 (hB s hs)
  have coordA : ∀ s : ℝ, 0 ≤ s → ∀ l, SeqL2.coord (semiDiag om s z) l =
      Real.exp (-s * om l) * SeqL2.coord z l := fun s hs l => by
    unfold semiDiag
    exact u11_coord_ofSeq (hmemA s hs) l
  refine ⟨fun t => SeqL2.ofSeq (fun l => -om l * Real.exp (-t * om l) * SeqL2.coord z l), ?_, ?_⟩
  · intro t ht
    have coordV : ∀ l, SeqL2.coord (SeqL2.ofSeq (fun l => -om l * Real.exp (-t * om l) *
        SeqL2.coord z l)) l = -om l * Real.exp (-t * om l) * SeqL2.coord z l :=
      fun l => u11_coord_ofSeq (hmemB t ht) l
    refine ⟨?_, coordV⟩
    set V := SeqL2.ofSeq (fun l => -om l * Real.exp (-t * om l) * SeqL2.coord z l) with hV
    set G : ℝ → ℕ → ℝ := fun h l => h⁻¹ * (Real.exp (-(t + h) * om l) - Real.exp (-t * om l)) +
      om l * Real.exp (-t * om l) with hG
    rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_iff_norm_sub_tendsto_zero]
    have hnorm : ∀ h : ℝ, |h| < t / 2 → ‖h⁻¹ • (semiDiag om (t + h) z - semiDiag om t z) - V‖ =
        Real.sqrt (∑' l, (G h l * SeqL2.coord z l) ^ 2) := by
      intro h hh
      have hab := abs_lt.1 hh
      have hpos : 0 ≤ t + h := by linarith
      have h1 := lp_two_norm_eq (show lp (fun _ : ℕ => ℝ) 2 from
        (h⁻¹ • (semiDiag om (t + h) z - semiDiag om t z) - V))
      have h2 : ‖h⁻¹ • (semiDiag om (t + h) z - semiDiag om t z) - V‖ = Real.sqrt (∑' l,
          SeqL2.coord (h⁻¹ • (semiDiag om (t + h) z - semiDiag om t z) - V) l ^ 2) := h1
      rw [h2]
      congr 1
      refine tsum_congr fun l => ?_
      have hc : SeqL2.coord (h⁻¹ • (semiDiag om (t + h) z - semiDiag om t z) - V) l =
          h⁻¹ * (SeqL2.coord (semiDiag om (t + h) z) l - SeqL2.coord (semiDiag om t z) l) -
            SeqL2.coord V l := rfl
      rw [hc, coordA _ hpos, coordA t ht.le, coordV]
      simp only [hG]
      ring
    have hlim : Tendsto (fun h : ℝ => ∑' l, (G h l * SeqL2.coord z l) ^ 2) (𝓝[≠] 0) (𝓝 0) := by
      have hab : ∀ l : ℕ, Tendsto (fun h : ℝ => (G h l * SeqL2.coord z l) ^ 2) (𝓝[≠] (0 : ℝ))
          (𝓝 0) := by
        intro l
        have hd := (hasDerivAt_iff_tendsto_slope_zero.1 (s88_exp_hasDerivAt (om l) t))
        have h0 : Tendsto (fun h : ℝ => G h l) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
          have := hd.add_const (om l * Real.exp (-t * om l))
          simp only [smul_eq_mul, neg_mul, neg_add_cancel] at this
          refine this.congr (fun h => ?_)
          simp only [hG, neg_mul]
        have := (h0.mul_const (SeqL2.coord z l)).pow 2
        simpa using this
      have hbd : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ∀ l : ℕ,
          ‖(G h l * SeqL2.coord z l) ^ 2‖ ≤ (3 / t) ^ 2 * SeqL2.coord z l ^ 2 := by
        have hev : ∀ᶠ h in 𝓝 (0 : ℝ), |h| < t / 2 := by
          have := Metric.ball_mem_nhds (0 : ℝ) (show 0 < t / 2 by positivity)
          filter_upwards [this] with h hh
          simpa [Real.dist_eq] using hh
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds hev] with h hh l
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
        have hq := s88_quot_bound (om l) t h (hom l).le ht hh.le
        have hm := s88_mul_exp_le (om l) t (hom l).le ht
        have hGb : |G h l| ≤ 3 / t := by
          simp only [hG]
          calc |h⁻¹ * (Real.exp (-(t + h) * om l) - Real.exp (-t * om l)) +
                om l * Real.exp (-t * om l)|
              ≤ |h⁻¹ * (Real.exp (-(t + h) * om l) - Real.exp (-t * om l))| +
                |om l * Real.exp (-t * om l)| := abs_add_le _ _
            _ ≤ 2 / t + 1 / t := by
                refine add_le_add hq ?_
                rw [abs_of_nonneg (mul_nonneg (hom l).le (Real.exp_pos _).le)]
                exact hm
            _ = 3 / t := by ring
        have : G h l ^ 2 ≤ (3 / t) ^ 2 := by
          rw [← sq_abs (G h l)]
          exact pow_le_pow_left₀ (abs_nonneg _) hGb 2
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[≠] (0 : ℝ))
        (f := fun (h : ℝ) (l : ℕ) => (G h l * SeqL2.coord z l) ^ 2) (g := fun _ => (0 : ℝ))
        (bound := fun l => (3 / t) ^ 2 * SeqL2.coord z l ^ 2)
        ((u11_coord_summable z).mul_left _) hab hbd
      simpa using this
    have hlim2 := (Real.continuous_sqrt.tendsto 0).comp hlim
    rw [Real.sqrt_zero] at hlim2
    refine hlim2.congr' ?_
    have hev : ∀ᶠ h in 𝓝 (0 : ℝ), |h| < t / 2 := by
      have := Metric.ball_mem_nhds (0 : ℝ) (show 0 < t / 2 by positivity)
      filter_upwards [this] with h hh
      simpa [Real.dist_eq] using hh
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hev] with h hh
    exact (hnorm h hh).symm
  · intro t ht
    have ht0 : 0 ≤ t := by linarith
    have ht1 : 0 < t := by linarith
    have coordV : ∀ l, SeqL2.coord (SeqL2.ofSeq (fun l => -om l * Real.exp (-t * om l) *
        SeqL2.coord z l)) l = -om l * Real.exp (-t * om l) * SeqL2.coord z l :=
      fun l => u11_coord_ofSeq (hmemB t ht1) l
    have hsA : Summable (fun l => (Real.exp (-t * om l) * SeqL2.coord z l) ^ 2) :=
      memℓp_two_iff.1 (hmemA t ht0)
    have nA : ‖semiDiag om t z‖ ^ 2 = ∑' l, (Real.exp (-t * om l) * SeqL2.coord z l) ^ 2 := by
      rw [← u11_norm_sq]
      refine tsum_congr fun l => ?_
      unfold semiDiag
      rw [u11_coord_ofSeq (hmemA t ht0)]
    have nB : ‖SeqL2.ofSeq (fun l => -om l * Real.exp (-t * om l) * SeqL2.coord z l)‖ ^ 2 =
        ∑' l, (-om l * Real.exp (-t * om l) * SeqL2.coord z l) ^ 2 := by
      rw [← u11_norm_sq]
      refine tsum_congr fun l => ?_
      rw [coordV]
    show ‖semiDiag om t z‖ ^ 2 + ‖SeqL2.ofSeq (fun l => -om l * Real.exp (-t * om l) *
        SeqL2.coord z l)‖ ^ 2 ≤ 3 * Real.exp (-lam * t) * ‖z‖ ^ 2
    rw [nA, nB, ← Summable.tsum_add hsA (hB t ht1), ← u11_norm_sq, ← tsum_mul_left]
    refine (hsA.add (hB t ht1)).tsum_le_tsum (fun l => ?_) ((u11_coord_summable z).mul_left _)
    have hω := hom l
    have hE := Real.exp_pos (-t * om l)
    have hE1 : Real.exp (-t * om l) ≤ Real.exp (-lam * t) :=
      Real.exp_le_exp.2 (by nlinarith [hgap l])
    have hq : Real.exp (-t * om l) * (1 + om l ^ 2) ≤ 3 := by
      have hq1 : 1 + om l ^ 2 ≤ 3 * Real.exp (om l) := by
        have := Real.quadratic_le_exp_of_nonneg hω.le
        nlinarith
      have hq2 : Real.exp (-t * om l) * Real.exp (om l) ≤ 1 := by
        rw [← Real.exp_add, Real.exp_le_one_iff]; nlinarith
      calc Real.exp (-t * om l) * (1 + om l ^ 2) ≤ Real.exp (-t * om l) * (3 * Real.exp (om l)) :=
            mul_le_mul_of_nonneg_left hq1 hE.le
        _ = 3 * (Real.exp (-t * om l) * Real.exp (om l)) := by ring
        _ ≤ 3 * 1 := by linarith
        _ = 3 := by ring
    have hkey : Real.exp (-t * om l) ^ 2 * (1 + om l ^ 2) ≤ 3 * Real.exp (-lam * t) := by
      calc Real.exp (-t * om l) ^ 2 * (1 + om l ^ 2) =
            Real.exp (-t * om l) * (Real.exp (-t * om l) * (1 + om l ^ 2)) := by ring
        _ ≤ Real.exp (-lam * t) * 3 :=
            mul_le_mul hE1 hq (mul_nonneg hE.le (by positivity)) (Real.exp_pos _).le
        _ = 3 * Real.exp (-lam * t) := by ring
    have e1 : (Real.exp (-t * om l) * SeqL2.coord z l) ^ 2 +
        (-om l * Real.exp (-t * om l) * SeqL2.coord z l) ^ 2 =
        Real.exp (-t * om l) ^ 2 * (1 + om l ^ 2) * SeqL2.coord z l ^ 2 := by ring
    rw [e1]
    have := mul_le_mul_of_nonneg_right hkey (sq_nonneg (SeqL2.coord z l))
    linarith

end HRS.MS.S88Breakdown
