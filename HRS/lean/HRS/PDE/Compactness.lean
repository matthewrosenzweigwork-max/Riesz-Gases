import Mathlib

/-!
# Coordinatewise compactness of uniformly Lipschitz families

Auxiliary file of the torus PDE layer (package ADJ-01).  The passage to the limit in the
Fourier–Galerkin scheme for Proposition 3.9 (`B:thm:adjoint-torus`, main manuscript
L1739–1757) extracts a subsequence of the Galerkin coefficient paths that converges uniformly on
`[0,t]` in every Fourier coordinate.  This is Arzelà–Ascoli for scalar functions combined with a
diagonal argument over the countable index set.
-/

noncomputable section

open Filter Topology Set

namespace HRS.PDE

/-- The ball of bounded, `L`-Lipschitz continuous functions on `[0,t]`. -/
def lipBall (t B L : ℝ) : Set C(Icc (0 : ℝ) t, ℂ) :=
  {g | (∀ x, ‖g x‖ ≤ B) ∧ ∀ x y, ‖g x - g y‖ ≤ L * dist x y}

lemma continuous_of_lip {X : Type*} [PseudoMetricSpace X] (h : X → ℂ) (L : ℝ)
    (hh : ∀ x y, ‖h x - h y‖ ≤ L * dist x y) : Continuous h := by
  refine (LipschitzWith.of_dist_le_mul (K := L.toNNReal) fun x y => ?_).continuous
  rw [dist_eq_norm]
  refine (hh x y).trans ?_
  exact mul_le_mul_of_nonneg_right (by simp) dist_nonneg

lemma isCompact_lipBall (t B L : ℝ) : IsCompact (lipBall t B L) := by
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · let T : Set (Icc (0 : ℝ) t → ℂ) :=
      {h | (∀ x, ‖h x‖ ≤ B) ∧ ∀ x y, ‖h x - h y‖ ≤ L * dist x y}
    have hT : IsCompact T := by
      refine IsCompact.of_isClosed_subset
        (isCompact_univ_pi fun x : Icc (0 : ℝ) t => isCompact_closedBall (0 : ℂ) B) ?_ ?_
      · have : T = (⋂ x, {h : Icc (0 : ℝ) t → ℂ | ‖h x‖ ≤ B}) ∩
            ⋂ x, ⋂ y, {h : Icc (0 : ℝ) t → ℂ | ‖h x - h y‖ ≤ L * dist x y} := by
          ext h; simp only [T, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
        rw [this]
        refine (isClosed_iInter fun x => ?_).inter
          (isClosed_iInter fun x => isClosed_iInter fun y => ?_)
        · exact isClosed_le ((continuous_apply x).norm) continuous_const
        · exact isClosed_le (((continuous_apply x).sub (continuous_apply y)).norm)
            continuous_const
      · intro h hh x _
        simpa using hh.1 x
    have : ContinuousMap.toFun '' lipBall t B L = T := by
      ext h
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact hg
      · intro hh
        exact ⟨⟨h, continuous_of_lip h L hh.2⟩, hh, rfl⟩
    rw [this]; exact hT
  · refine Metric.equicontinuous_of_continuity_modulus (fun d => L * d) ?_ _ ?_
    · have : Continuous fun d : ℝ => L * d := continuous_const.mul continuous_id
      simpa using this.tendsto 0
    · intro x y g
      rw [dist_eq_norm]
      exact g.2.2 x y

/-- Diagonal Arzelà–Ascoli: a sequence of coordinate families `f n : ℝ → ι → ℂ`, `ι` countable,
which is uniformly bounded and uniformly Lipschitz on `[0,t]` in each coordinate (bounds may
depend on the coordinate) has a subsequence converging uniformly on `[0,t]` in every coordinate. -/
theorem exists_subseq_tendstoUniformlyOn_coord {ι : Type*} [Countable ι]
    (f : ℕ → ℝ → ι → ℂ) (t : ℝ) (B L : ι → ℝ)
    (hB : ∀ n i, ∀ τ ∈ Icc 0 t, ‖f n τ i‖ ≤ B i)
    (hL : ∀ n i, ∀ τ ∈ Icc 0 t, ∀ σ ∈ Icc 0 t, ‖f n τ i - f n σ i‖ ≤ L i * |τ - σ|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ → ι → ℂ,
      ∀ i, TendstoUniformlyOn (fun n τ => f (φ n) τ i) (fun τ => g τ i) atTop (Icc 0 t) := by
  classical
  set F : ℕ → ι → C(Icc (0 : ℝ) t, ℂ) := fun n i =>
    ⟨fun x => f n x i, continuous_of_lip _ (L i) fun x y => hL n i x x.2 y y.2⟩ with hF
  have hmem : ∀ n, F n ∈ Set.pi univ (fun i => lipBall t (B i) (L i)) := by
    intro n i _
    refine ⟨fun x => hB n i x x.2, fun x y => ?_⟩
    simpa [hF, Subtype.dist_eq, Real.dist_eq] using hL n i x x.2 y y.2
  have hK : IsCompact (Set.pi univ (fun i => lipBall t (B i) (L i))) :=
    isCompact_univ_pi fun i => isCompact_lipBall t (B i) (L i)
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  refine ⟨φ, hφ, fun τ i => if h : τ ∈ Icc (0 : ℝ) t then a i ⟨τ, h⟩ else 0, fun i => ?_⟩
  have h1 := (ContinuousMap.tendsto_iff_tendstoUniformly.1 (tendsto_pi_nhds.1 hlim i))
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have h2 : TendstoUniformly (fun n (x : Icc (0 : ℝ) t) => f (φ n) x i) (fun x => a i x) atTop :=
    h1
  convert h2 using 1
  funext x
  simp only [Function.comp_apply]
  split_ifs with hx
  · rfl
  · exact absurd x.2 hx

end HRS.PDE
