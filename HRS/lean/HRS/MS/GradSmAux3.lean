import HRS.MS.GradSmAux2

/-!
# S6.7 packet S67B: gradient smoothing, part 3: a compactness lemma (qualitative regularity of limits)

* `s67b_aa`: Arzela-Ascoli (sequential form) for uniformly bounded, uniformly Lipschitz maps `ℝ^d → E`, `E` finite-dimensional;
* `s67b_lim`: if `f_n ∈ C^{N+1}`, `‖D^i f_n‖ ≤ K` for `i ≤ N+1` (uniformly in `n, x`) and `f_n → g` pointwise, then `g ∈ C^N`.

Used in `GradSmAux4` to prove the qualitative gain `F ∈ C_b^k ⇒ P_t F ∈ C^{k+1}` (`t > 0`).
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
open HRS

noncomputable section

namespace HRS.MS.GradSm

variable {d : ℕ}

theorem s67b_aa {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : ℝ) (hK : 0 ≤ K) (g : ℕ → Euc d → E) (hlip : ∀ n x y, ‖g n x - g n y‖ ≤ K * ‖x - y‖)
    (hb : ∀ n x, ‖g n x‖ ≤ K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ h : Euc d → E,
      TendstoLocallyUniformly (fun n => g (φ n)) h atTop := by
  have hcontf : ∀ f : Euc d → E, (∀ x y, ‖f x - f y‖ ≤ K * ‖x - y‖) → Continuous f := by
    intro f hf
    exact (LipschitzWith.of_dist_le_mul (K := ⟨K, hK⟩) (fun x y => by
      show dist (f x) (f y) ≤ K * dist x y
      rw [dist_eq_norm, dist_eq_norm]; exact hf x y)).continuous
  let T : Set (Euc d → E) :=
    {f | (∀ x, ‖f x‖ ≤ K) ∧ ∀ x y, ‖f x - f y‖ ≤ K * ‖x - y‖}
  have hTc : IsCompact T := by
    refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun x => isCompact_closedBall (0 : E) K)
      ?_ ?_
    · have h1 : IsClosed {f : Euc d → E | ∀ x, ‖f x‖ ≤ K} := by
        simp only [ofPred_forall]
        exact isClosed_iInter fun x => isClosed_le ((continuous_apply x).norm) continuous_const
      have h2 : IsClosed {f : Euc d → E | ∀ x y, ‖f x - f y‖ ≤ K * ‖x - y‖} := by
        simp only [ofPred_forall]
        exact isClosed_iInter fun x => isClosed_iInter fun y =>
          isClosed_le (((continuous_apply x).sub (continuous_apply y)).norm) continuous_const
      exact h1.inter h2
    · intro f hf x _
      simpa using hf.1 x
  let S : Set C(Euc d, E) := {f | (⇑f) ∈ T}
  have hS1 : IsCompact (ContinuousMap.toFun '' S) := by
    have : ContinuousMap.toFun '' S = T := by
      ext f
      constructor
      · rintro ⟨f', hf', rfl⟩
        exact hf'
      · intro hf
        exact ⟨⟨f, hcontf f hf.2⟩, hf, rfl⟩
    rw [this]; exact hTc
  have hS2 : Equicontinuous (fun f : S => (⇑f.1 : Euc d → E)) := by
    refine Metric.equicontinuous_of_continuity_modulus (fun r => K * r) ?_ _ (fun x y f => ?_)
    · have : Tendsto (fun r : ℝ => K * r) (𝓝 0) (𝓝 (K * 0)) := tendsto_const_nhds.mul tendsto_id
      simpa using this
    · simpa [dist_eq_norm] using f.2.2 x y
  have hSc : IsCompact S := ArzelaAscoli.isCompact_of_equicontinuous S hS1 hS2
  obtain ⟨a, -, φ, hφ, hT⟩ := hSc.tendsto_subseq
    (x := fun n => (⟨g n, hcontf _ (hlip n)⟩ : C(Euc d, E))) (fun n => ⟨hb n, hlip n⟩)
  refine ⟨φ, hφ, a, ?_⟩
  exact tendstoLocallyUniformly_iff_forall_isCompact.2
    (fun K' hK' => ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 hT K' hK')


theorem s67b_lip_of_fderiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Euc d → E} (hf : Differentiable ℝ f) {K : ℝ} (hK : ∀ x, ‖fderiv ℝ f x‖ ≤ K) (x y : Euc d) :
    ‖f x - f y‖ ≤ K * ‖x - y‖ := by
  have := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
    (f := f) (C := K) (fun z _ => hf z) (fun z _ => hK z) (mem_univ y) (mem_univ x)
  simpa using this

theorem s67b_lim (K : ℝ) (hK : 0 ≤ K) : ∀ (N : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : ℕ → Euc d → E) (g : Euc d → E),
    (∀ n, ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) (f n)) →
    (∀ n, ∀ i ≤ N + 1, ∀ x, ‖iteratedFDeriv ℝ i (f n) x‖ ≤ K) →
    (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) →
    ContDiff ℝ (N : WithTop ℕ∞) g := by
  intro N
  induction N with
  | zero =>
    intro E _ _ _ f g hc hb hlim
    have hl : ∀ x y, ‖g x - g y‖ ≤ K * ‖x - y‖ := by
      intro x y
      refine le_of_tendsto ((hlim x).sub (hlim y)).norm (Eventually.of_forall fun n => ?_)
      refine s67b_lip_of_fderiv ((hc n).differentiable (by simp)) (fun z => ?_) x y
      have := hb n 1 le_rfl z
      rwa [norm_iteratedFDeriv_one] at this
    have hcont : Continuous g := (LipschitzWith.of_dist_le_mul (K := ⟨K, hK⟩) (fun x y => by
      show dist (g x) (g y) ≤ K * dist x y
      rw [dist_eq_norm, dist_eq_norm]; exact hl x y)).continuous
    exact contDiff_zero.2 hcont
  | succ N ih =>
    intro E _ _ _ f g hc hb hlim
    have hDc : ∀ n, ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ (f n)) := fun n =>
      (contDiff_succ_iff_fderiv.1 (by exact_mod_cast hc n)).2.2
    have hDb : ∀ n, ∀ i ≤ N + 1, ∀ x, ‖iteratedFDeriv ℝ i (fderiv ℝ (f n)) x‖ ≤ K := by
      intro n i hi x
      rw [norm_iteratedFDeriv_fderiv]
      exact hb n (i + 1) (by omega) x
    have hD0 : ∀ n x, ‖fderiv ℝ (f n) x‖ ≤ K := by
      intro n x
      have := hb n 1 (by omega) x
      rwa [norm_iteratedFDeriv_one] at this
    have hDlip : ∀ n x y, ‖fderiv ℝ (f n) x - fderiv ℝ (f n) y‖ ≤ K * ‖x - y‖ := by
      intro n x y
      refine s67b_lip_of_fderiv ((hDc n).differentiable (by simp)) (fun z => ?_) x y
      have := hDb n 1 (by omega) z
      rwa [norm_iteratedFDeriv_one] at this
    obtain ⟨φ, hφ, h, hh⟩ := s67b_aa K hK (fun n => fderiv ℝ (f n)) hDlip hD0
    have hder : ∀ x, HasFDerivAt g (h x) x := fun x =>
      hasFDerivAt_of_tendstoLocallyUniformlyOn (f := fun n => f (φ n)) isOpen_univ
        (tendstoLocallyUniformlyOn_univ.2 hh)
        (fun n z _ => (((hc (φ n)).differentiable (by simp)) z).hasFDerivAt)
        (fun z _ => (hlim z).comp hφ.tendsto_atTop) (mem_univ x)
    have hIH : ContDiff ℝ (N : WithTop ℕ∞) h :=
      ih (fun n => fderiv ℝ (f (φ n))) h (fun n => hDc (φ n)) (fun n i hi x => hDb (φ n) i hi x)
        (fun x => (tendstoLocallyUniformlyOn_univ.2 hh).tendsto_at (mem_univ x))
    have hfd : fderiv ℝ g = h := funext fun x => (hder x).fderiv
    have hdiff : Differentiable ℝ g := fun x => (hder x).differentiableAt
    have e : ((N + 1 : ℕ) : WithTop ℕ∞) = (N : WithTop ℕ∞) + 1 := by norm_cast
    rw [e]
    refine contDiff_succ_iff_fderiv.2 ⟨hdiff, fun h' => by simp at h', ?_⟩
    rw [hfd]; exact hIH

end HRS.MS.GradSm
