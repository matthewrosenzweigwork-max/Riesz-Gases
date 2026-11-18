import HRS.MS.R26T8AP06r

/-!
# S8.2 Taylor split (T), step A: a C^k limit of C^k functions whose iterated derivatives extend continuously
`r26t8a_limit_taylor`: if `Φ w` is `C^k` for `w ≠ 0` and the iterated derivatives `iteratedFDeriv p (Φ w) Y` (`p ≤ k`) extend to
continuous functions `G p` of `(Y,w)` on all of `E × E`, then `Y ↦ G 0 (Y,0)` is `C^k` with `iteratedFDeriv p = G p (·,0)`.
(Uniform convergence of the derivatives as `w → 0` and `hasFDerivAt_of_tendstoUniformlyOnFilter`.)
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A

theorem r26t8a_limit_taylor {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (k : ℕ)
    (Φ : E → E → V) (hΦ : ∀ w, w ≠ 0 → ContDiff ℝ (k : WithTop ℕ∞) (Φ w))
    (G : (p : ℕ) → E × E → ContinuousMultilinearMap ℝ (fun _ : Fin p => E) V)
    (hGc : ∀ p ≤ k, Continuous (G p))
    (hGe : ∀ p ≤ k, ∀ Y w : E, w ≠ 0 → G p (Y, w) = iteratedFDeriv ℝ p (Φ w) Y) :
    ∃ f₀ : E → V, ContDiff ℝ (k : WithTop ℕ∞) f₀ ∧
      (∀ Y, f₀ Y = continuousMultilinearCurryFin0 ℝ E V (G 0 (Y, 0))) ∧
      ∀ p ≤ k, ∀ Y, iteratedFDeriv ℝ p f₀ Y = G p (Y, 0) := by
  haveI : NeBot (𝓝[≠] (0 : E)) := inferInstance
  have hTay : HasFTaylorSeriesUpTo (k : ℕ∞) (fun Y => continuousMultilinearCurryFin0 ℝ E V (G 0 (Y, 0)))
      (fun Y p => G p (Y, 0)) := by
    refine ⟨fun Y => ?_, fun m hm Y => ?_, fun m hm => ?_⟩
    · simp
    · have hmk : m < k := by exact_mod_cast hm
      -- the derivative of the approximants
      have hder : ∀ w : E, w ≠ 0 → ∀ y : E,
          HasFDerivAt (fun Y => G m (Y, w)) ((G (m + 1) (y, w)).curryLeft) y := by
        intro w hw y
        have hfun : (fun Y => G m (Y, w)) = iteratedFDeriv ℝ m (Φ w) :=
          funext fun Y => hGe m hmk.le Y w hw
        have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ m (Φ w)) y :=
          ((hΦ w hw).differentiable_iteratedFDeriv (by exact_mod_cast hmk)) y
        rw [hfun]
        have e : (G (m + 1) (y, w)).curryLeft = fderiv ℝ (iteratedFDeriv ℝ m (Φ w)) y := by
          rw [hGe (m + 1) hmk y w hw, iteratedFDeriv_succ_eq_comp_left]
          exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) V).apply_symm_apply _
        rw [e]
        exact hd.hasFDerivAt
      have hdist : ∀ a b : E × E, dist ((G (m + 1) a).curryLeft) ((G (m + 1) b).curryLeft) =
          dist (G (m + 1) a) (G (m + 1) b) := fun a b =>
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) V).dist_map _ _
      refine hasFDerivAt_of_tendstoUniformlyOnFilter (l := 𝓝[≠] (0 : E))
        (f := fun w Y => G m (Y, w)) (f' := fun w Y => (G (m + 1) (Y, w)).curryLeft)
        (g := fun Y => G m (Y, 0)) (g' := fun Y => (G (m + 1) (Y, 0)).curryLeft) ?_ ?_ ?_
      · rw [Metric.tendstoUniformlyOnFilter_iff]
        intro ε hε
        obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 ((hGc (m + 1) (by omega)).continuousAt (x := (Y, 0))) (ε / 2) (by positivity)
        have h1 : ∀ᶠ n : E × E in (𝓝[≠] (0 : E)) ×ˢ 𝓝 Y, dist n.2 Y < δ ∧ dist n.1 0 < δ := by
          have a : ∀ᶠ n : E × E in (𝓝[≠] (0 : E)) ×ˢ 𝓝 Y, dist n.1 0 < δ :=
            Filter.tendsto_fst.eventually (eventually_nhdsWithin_of_eventually_nhds
              (Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun y hy => hy⟩ : ∀ᶠ w in 𝓝 (0 : E), dist w 0 < δ))
          have b : ∀ᶠ n : E × E in (𝓝[≠] (0 : E)) ×ˢ 𝓝 Y, dist n.2 Y < δ :=
            Filter.tendsto_snd.eventually (Metric.ball_mem_nhds Y hδ)
          exact b.and a
        filter_upwards [h1] with n hn
        have e1 := hδ' (show dist ((n.2, n.1) : E × E) (Y, 0) < δ by
          rw [Prod.dist_eq]; exact max_lt hn.1 (by simpa using hn.2))
        have e2 := hδ' (show dist ((n.2, 0) : E × E) (Y, 0) < δ by
          rw [Prod.dist_eq]; exact max_lt hn.1 (by simpa using hδ))
        rw [hdist]
        calc dist (G (m + 1) (n.2, 0)) (G (m + 1) (n.2, n.1))
            ≤ dist (G (m + 1) (n.2, 0)) (G (m + 1) (Y, 0)) +
              dist (G (m + 1) (Y, 0)) (G (m + 1) (n.2, n.1)) := dist_triangle _ _ _
          _ < ε / 2 + ε / 2 := by
              refine add_lt_add e2 ?_
              rw [dist_comm]; exact e1
          _ = ε := by ring
      · exact (Filter.tendsto_fst.eventually (eventually_mem_nhdsWithin : ∀ᶠ w in 𝓝[≠] (0 : E), w ∈ ({0}ᶜ : Set E))).mono
          fun n hn => hder n.1 hn n.2
      · exact Filter.Eventually.of_forall fun y => ((hGc m hmk.le).comp
          (continuous_const.prodMk continuous_id)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · exact (hGc m (by exact_mod_cast hm)).comp (continuous_id.prodMk continuous_const)
  refine ⟨_, by exact_mod_cast hTay.contDiff, fun Y => rfl, fun p hp Y => ?_⟩
  exact (hTay.eq_iteratedFDeriv (m := p) (by exact_mod_cast hp) Y).symm

end HRS.MS.R26T8A
