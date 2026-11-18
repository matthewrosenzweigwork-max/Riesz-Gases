import Mathlib

/-!
# S55M, part 1: compactness and derivative convergence (pure analysis)

Infrastructure for the `t`-measurability `S55fMeas` (see `GoMeasAux3.lean`); helper names carry the prefix `s55m_`.

* `s55m_dl`: if `h_m : E → F` (finite dimensional `E`, `F`) are `C^{n+1}` with `‖D^j h_m‖ ≤ B` for `j ≤ n+1` and
  `h_m → h₀` pointwise, then `h₀` is `C^n` and `D^j h_m(x) → D^j h₀(x)` for `j ≤ n` and every `x` (the limit also
  satisfies the bounds, `s55m_dl_bound`).  Proof: Taylor's formula with the Lipschitz constant of the derivative and
  Bolzano-Weierstrass for the (bounded) sequence of derivatives; no Arzelà-Ascoli theorem is used.
* `s55m_ex`: extraction of a pointwise convergent subsequence from a family `f_n : ℝ → E → ℝ` which is uniformly
  bounded and equi-Lipschitz in `x`, and equi-Lipschitz in `r` with the weight `1 + ‖x‖` (a diagonal argument along
  a dense sequence of `ℝ × E`); the limit has the same bounds.
-/

noncomputable section

open Filter Topology Metric
open scoped ContDiff

namespace HRS.MS.Go

/-! ### First-order derivative convergence -/

section DL1
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

lemma s55m_taylor {g : E → F} {B : ℝ} (hB : 0 ≤ B) (hd : Differentiable ℝ g)
    (hl : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ B * ‖x - y‖) (x w : E) :
    ‖g (x + w) - g x - fderiv ℝ g x w‖ ≤ B * ‖w‖ ^ 2 := by
  set A : E →L[ℝ] F := fderiv ℝ g x with hA
  set k : E → F := fun y => g y - A y with hk
  have hkd : ∀ y, DifferentiableAt ℝ k y := fun y => (hd y).sub A.differentiableAt
  have hkf : ∀ y, fderiv ℝ k y = fderiv ℝ g y - A := fun y => by
    rw [hk]; exact ((hd y).hasFDerivAt.sub A.hasFDerivAt).fderiv
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := k) (C := B * ‖w‖)
    (s := closedBall x ‖w‖) (x := x) (y := x + w) (fun y _ => hkd y) (fun y hy => by
      rw [hkf]
      have h1 := hl y x
      have h2 : ‖y - x‖ ≤ ‖w‖ := by simpa [dist_eq_norm] using hy
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hB))
    (convex_closedBall _ _) (mem_closedBall_self (norm_nonneg _)) (by simp [dist_eq_norm])
  have e : k (x + w) - k x = g (x + w) - g x - A w := by
    simp only [hk, map_add]; abel
  rw [e] at h
  simpa [sq, mul_assoc] using h

lemma s55m_hasFDerivAt_of_taylor {h₀ : E → F} {x : E} {v : E →L[ℝ] F} {B : ℝ}
    (h : ∀ w, ‖h₀ (x + w) - h₀ x - v w‖ ≤ B * ‖w‖ ^ 2) : HasFDerivAt h₀ v x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hB : 0 < |B| + 1 := by positivity
  rw [Metric.eventually_nhds_iff]
  refine ⟨c / (|B| + 1), by positivity, fun w hw => ?_⟩
  rw [dist_zero_right] at hw
  calc ‖h₀ (x + w) - h₀ x - v w‖ ≤ B * ‖w‖ ^ 2 := h w
    _ ≤ |B| * ‖w‖ * ‖w‖ := by nlinarith [le_abs_self B, norm_nonneg w, sq_nonneg ‖w‖]
    _ ≤ (|B| + 1) * (c / (|B| + 1)) * ‖w‖ := by
        have : |B| * ‖w‖ ≤ (|B| + 1) * (c / (|B| + 1)) := by
          rw [mul_div_cancel₀ _ hB.ne']
          have : |B| * ‖w‖ ≤ |B| * (c / (|B| + 1)) := mul_le_mul_of_nonneg_left hw.le (abs_nonneg B)
          have h2 : |B| * (c / (|B| + 1)) ≤ c := by
            rw [mul_div_assoc', div_le_iff₀ hB]; nlinarith [abs_nonneg B]
          linarith
        exact mul_le_mul_of_nonneg_right this (norm_nonneg w)
    _ = c * ‖w‖ := by rw [mul_div_cancel₀ _ hB.ne']

/-- First-order convergence of derivatives: bounded, equi-Lipschitz derivatives and pointwise convergence. -/
theorem s55m_dl1 {B : ℝ} (hB : 0 ≤ B) {h : ℕ → E → F} {h₀ : E → F}
    (hd : ∀ m, Differentiable ℝ (h m)) (hb : ∀ m x, ‖fderiv ℝ (h m) x‖ ≤ B)
    (hl : ∀ m x y, ‖fderiv ℝ (h m) x - fderiv ℝ (h m) y‖ ≤ B * ‖x - y‖)
    (ht : ∀ x, Tendsto (fun m => h m x) atTop (𝓝 (h₀ x))) :
    Differentiable ℝ h₀ ∧ ∀ x, Tendsto (fun m => fderiv ℝ (h m) x) atTop (𝓝 (fderiv ℝ h₀ x)) := by
  have hcl : ∀ x (ns : ℕ → ℕ) (v : E →L[ℝ] F), Tendsto ns atTop atTop →
      Tendsto (fun i => fderiv ℝ (h (ns i)) x) atTop (𝓝 v) → HasFDerivAt h₀ v x := by
    intro x ns v hns hv
    refine s55m_hasFDerivAt_of_taylor (B := B) fun w => ?_
    have h1 : Tendsto (fun i => ‖h (ns i) (x + w) - h (ns i) x - fderiv ℝ (h (ns i)) x w‖) atTop
        (𝓝 ‖h₀ (x + w) - h₀ x - v w‖) := by
      refine (Tendsto.norm ?_)
      exact (((ht _).comp hns).sub ((ht _).comp hns)).sub
        ((ContinuousLinearMap.apply ℝ F w).continuous.tendsto v |>.comp hv)
    exact le_of_tendsto' h1 fun i => s55m_taylor hB (hd _) (hl _) x w
  have hex : ∀ x, ∃ v : E →L[ℝ] F, ∃ ns : ℕ → ℕ, StrictMono ns ∧
      Tendsto (fun i => fderiv ℝ (h (ns i)) x) atTop (𝓝 v) := by
    intro x
    obtain ⟨v, -, ns, hns, hv⟩ := tendsto_subseq_of_bounded (isBounded_closedBall (x := (0 : E →L[ℝ] F))
      (r := B)) (x := fun m => fderiv ℝ (h m) x) (fun m => by simpa using hb m x)
    exact ⟨v, ns, hns, hv⟩
  have hdiff : Differentiable ℝ h₀ := fun x => by
    obtain ⟨v, ns, hns, hv⟩ := hex x
    exact (hcl x ns v hns.tendsto_atTop hv).differentiableAt
  refine ⟨hdiff, fun x => ?_⟩
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨v, -, ms, hms, hv⟩ := tendsto_subseq_of_bounded (isBounded_closedBall (x := (0 : E →L[ℝ] F))
    (r := B)) (x := fun i => fderiv ℝ (h (ns i)) x) (fun i => by simpa using hb (ns i) x)
  refine ⟨ms, ?_⟩
  have := (hcl x (ns ∘ ms) v (hns.comp hms.tendsto_atTop) hv).fderiv
  rw [← this] at hv
  exact hv

end DL1

/-! ### Higher-order convergence -/

section DL
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem s55m_dl (n : ℕ) : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {B : ℝ} (hB : 0 ≤ B) {h : ℕ → E → F} {h₀ : E → F}
    (hc : ∀ m, ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (h m))
    (hb : ∀ m, ∀ j ≤ n + 1, ∀ x, ‖iteratedFDeriv ℝ j (h m) x‖ ≤ B)
    (ht : ∀ x, Tendsto (fun m => h m x) atTop (𝓝 (h₀ x))),
    ContDiff ℝ (n : WithTop ℕ∞) h₀ ∧ ∀ j ≤ n, ∀ x,
      Tendsto (fun m => iteratedFDeriv ℝ j (h m) x) atTop (𝓝 (iteratedFDeriv ℝ j h₀ x)) := by
  induction n with
  | zero =>
    intro F _ _ _ B hB h h₀ hc hb ht
    have hlip : ∀ x y, ‖h₀ x - h₀ y‖ ≤ B * ‖x - y‖ := by
      intro x y
      have h1 : ∀ m, ‖h m x - h m y‖ ≤ B * ‖x - y‖ := fun m => by
        have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := h m) (C := B) (s := Set.univ)
          (x := y) (y := x) (fun z _ => ((hc m).differentiable (by simp)) z) (fun z _ => by
            have := hb m 1 le_rfl z
            rwa [norm_iteratedFDeriv_one] at this) convex_univ (Set.mem_univ _) (Set.mem_univ _)
        simpa [mul_comm] using this
      exact le_of_tendsto' (((ht x).sub (ht y)).norm) h1
    have hcont : Continuous h₀ := by
      refine (LipschitzWith.of_dist_le_mul (K := ⟨B, hB⟩) fun x y => ?_).continuous
      rw [dist_eq_norm, dist_eq_norm]
      exact hlip x y
    refine ⟨by simpa using hcont, fun j hj x => ?_⟩
    obtain rfl : j = 0 := by omega
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp]
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.continuous.tendsto _).comp (ht x)
  | succ n ih =>
    intro F _ _ _ B hB h h₀ hc hb ht
    have hd : ∀ m, Differentiable ℝ (h m) := fun m => (hc m).differentiable (by simp)
    have hb1 : ∀ m x, ‖fderiv ℝ (h m) x‖ ≤ B := fun m x => by
      have := hb m 1 (by omega) x
      rwa [norm_iteratedFDeriv_one] at this
    have hl : ∀ m x y, ‖fderiv ℝ (h m) x - fderiv ℝ (h m) y‖ ≤ B * ‖x - y‖ := fun m x y => by
      have hcd : ContDiff ℝ 1 (fderiv ℝ (h m)) := (hc m).fderiv_right (by exact_mod_cast (by omega : 1 + 1 ≤ n + 1 + 1))
      have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fderiv ℝ (h m)) (C := B)
        (s := Set.univ) (x := y) (y := x) (fun z _ => hcd.differentiable (by simp) z) (fun z _ => by
          have := hb m 2 (by omega) z
          rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at this) convex_univ
          (Set.mem_univ _) (Set.mem_univ _)
      simpa [mul_comm] using this
    obtain ⟨hdiff, hder⟩ := s55m_dl1 hB hd hb1 hl ht
    have hcf : ∀ m, ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ (h m)) := fun m =>
      (hc m).fderiv_right (by push_cast; exact le_rfl)
    obtain ⟨ih1, ih2⟩ := ih (F := E →L[ℝ] F) hB (h := fun m => fderiv ℝ (h m)) (h₀ := fderiv ℝ h₀) hcf
      (fun m j hj x => by
        rw [norm_iteratedFDeriv_fderiv]; exact hb m (j + 1) (by omega) x) hder
    refine ⟨?_, fun j hj x => ?_⟩
    · have e : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [e, contDiff_succ_iff_fderiv]
      exact ⟨hdiff, by simp, by simpa using ih1⟩
    · rcases j with _ | j
      · simp only [iteratedFDeriv_zero_eq_comp, Function.comp]
        exact ((continuousMultilinearCurryFin0 ℝ E F).symm.continuous.tendsto _).comp (ht x)
      · have h3 := ih2 j (by omega) x
        have h4 := (((continuousMultilinearCurryRightEquiv' ℝ j E F).symm).continuous.tendsto _).comp h3
        simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp]
        exact h4

theorem s55m_dl_bound {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {B : ℝ} {h : ℕ → E → F} {h₀ : E → F}
    {j : ℕ} {x : E} (hb : ∀ m, ‖iteratedFDeriv ℝ j (h m) x‖ ≤ B)
    (ht : Tendsto (fun m => iteratedFDeriv ℝ j (h m) x) atTop (𝓝 (iteratedFDeriv ℝ j h₀ x))) :
    ‖iteratedFDeriv ℝ j h₀ x‖ ≤ B :=
  le_of_tendsto' ht.norm hb

end DL

/-! ### Extraction of a pointwise convergent subsequence -/

section EX
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]

theorem s55m_ex (f : ℕ → ℝ → E → ℝ) {B L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ n r x, |f n r x| ≤ B)
    (hr : ∀ n r r' x, |f n r x - f n r' x| ≤ L * (1 + ‖x‖) * |r - r'|)
    (hx : ∀ n r x x', |f n r x - f n r x'| ≤ L * ‖x - x'‖) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ g : ℝ → E → ℝ,
      (∀ r x, Tendsto (fun i => f (ns i) r x) atTop (𝓝 (g r x))) ∧
      (∀ r r' x, |g r x - g r' x| ≤ L * (1 + ‖x‖) * |r - r'|) ∧
      (∀ r x x', |g r x - g r x'| ≤ L * ‖x - x'‖) ∧ (∀ r x, |g r x| ≤ B) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb 0 0 0)
  obtain ⟨q, hq⟩ : ∃ q : ℕ → ℝ × E, DenseRange q :=
    ⟨TopologicalSpace.denseSeq (ℝ × E), TopologicalSpace.denseRange_denseSeq _⟩
  have hK : IsCompact (Set.pi Set.univ fun _ : ℕ => Set.Icc (-B) B) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨a, -, ns, hns, ha⟩ := hK.tendsto_subseq (x := fun n (i : ℕ) => f n (q i).1 (q i).2)
    (fun n i _ => abs_le.1 (hb n _ _))
  have hat : ∀ i, Tendsto (fun k => f (ns k) (q i).1 (q i).2) atTop (𝓝 (a i)) := fun i =>
    tendsto_pi_nhds.1 ha i
  have hcau : ∀ r x, CauchySeq fun k => f (ns k) r x := by
    intro r x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    set c : ℝ := L * (1 + ‖x‖) + L + 1 with hc
    have hc0 : 0 < c := by positivity
    obtain ⟨i, hi⟩ := hq.exists_dist_lt (r, x) (show 0 < ε / (4 * c) by positivity)
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, dist_eq_norm] at hi
    obtain ⟨hr1, hx1⟩ := hi
    have hmod : ∀ n, |f n r x - f n (q i).1 (q i).2| ≤ ε / 4 := by
      intro n
      have h1 := hr n r (q i).1 x
      have h2 := hx n (q i).1 x (q i).2
      have h3 : |f n r x - f n (q i).1 (q i).2| ≤
          |f n r x - f n (q i).1 x| + |f n (q i).1 x - f n (q i).1 (q i).2| := by
        have := abs_add_le (f n r x - f n (q i).1 x) (f n (q i).1 x - f n (q i).1 (q i).2)
        simpa using this
      have h2' : |f n (q i).1 x - f n (q i).1 (q i).2| ≤ L * ‖x - (q i).2‖ := h2
      have h4 : L * (1 + ‖x‖) * |r - (q i).1| ≤ ε / 4 * (L * (1 + ‖x‖) / c) := by
        calc L * (1 + ‖x‖) * |r - (q i).1| ≤ L * (1 + ‖x‖) * (ε / (4 * c)) :=
              mul_le_mul_of_nonneg_left hr1.le (by positivity)
          _ = ε / 4 * (L * (1 + ‖x‖) / c) := by field_simp
      have h5 : L * ‖x - (q i).2‖ ≤ ε / 4 * (L / c) := by
        calc L * ‖x - (q i).2‖ ≤ L * (ε / (4 * c)) := mul_le_mul_of_nonneg_left hx1.le hL
          _ = ε / 4 * (L / c) := by field_simp
      have h6 : L * (1 + ‖x‖) / c + L / c ≤ 1 := by
        rw [← add_div, div_le_one hc0]; rw [hc]; nlinarith [norm_nonneg x]
      have h7 : ε / 4 * (L * (1 + ‖x‖) / c) + ε / 4 * (L / c) ≤ ε / 4 := by
        rw [← mul_add]; nlinarith [h6]
      linarith
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hat i) (ε / 4) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [Real.dist_eq]
    have h1 := hN m hm
    have h2 := hN n hn
    rw [Real.dist_eq] at h1 h2
    have h3 := hmod (ns m)
    have h4 := hmod (ns n)
    rw [abs_lt] at h1 h2
    rw [abs_le] at h3 h4
    rw [abs_lt]
    constructor <;> linarith [h3.1, h3.2, h4.1, h4.2, h1.1, h1.2, h2.1, h2.2]
  refine ⟨ns, hns, fun r x => limUnder atTop fun k => f (ns k) r x, fun r x => (hcau r x).tendsto_limUnder,
    fun r r' x => ?_, fun r x x' => ?_, fun r x => ?_⟩
  · exact le_of_tendsto' (((hcau r x).tendsto_limUnder.sub (hcau r' x).tendsto_limUnder).abs)
      fun k => hr (ns k) r r' x
  · exact le_of_tendsto' (((hcau r x).tendsto_limUnder.sub (hcau r x').tendsto_limUnder).abs)
      fun k => hx (ns k) r x x'
  · exact le_of_tendsto' ((hcau r x).tendsto_limUnder.abs) fun k => hb (ns k) r x

end EX

end HRS.MS.Go
