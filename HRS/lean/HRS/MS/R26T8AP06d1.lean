import HRS.MS.R26T8AP00

/-!
# S8.2 local Newton layer, packet T8A.P06d (part 1): `C^n` extension across the diagonal from continuous extensions of all jets
`r26t8a_extend_C`: let `U = {(X,z) | z != 0}` and `f : E x E -> V` of class `C^n` on `U` such that each `iteratedFDeriv j f` (`j <= n`) restricted to `U`
has a continuous extension to `E x E`.  Then `f` is the restriction to `U` of a `C^n` function.  Proof by induction on `n` via
`hasFDerivWithinAt_closure_of_tendsto_fderiv` on the two opposite half-spaces `{+-<z,e> > 0}` (convex, open, inside `U`, closures cover `E x E`).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Set
open scoped ContDiff

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_halfspace_cover (e : Euc d) (he : e ≠ 0) :
    closure {w : Euc d × Euc d | 0 < inner ℝ w.2 e} ∪ closure {w : Euc d × Euc d | inner ℝ w.2 e < 0} = Set.univ := by
  ext w
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  rcases lt_trichotomy (inner ℝ w.2 e) 0 with h | h | h
  · exact Or.inr (subset_closure h)
  · left
    have hlim : Tendsto (fun t : ℝ => (w.1, w.2 + t • e)) (𝓝[>] 0) (𝓝 w) := by
      have : Tendsto (fun t : ℝ => (w.1, w.2 + t • e)) (𝓝 0) (𝓝 (w.1, w.2 + (0 : ℝ) • e)) :=
        (continuous_const.prodMk (continuous_const.add (continuous_id.smul continuous_const))).tendsto 0
      simp only [zero_smul, add_zero, Prod.mk.eta] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    show 0 < inner ℝ (w.2 + t • e) e
    rw [inner_add_left, inner_smul_left, h, zero_add]
    have : 0 < ‖e‖ ^ 2 := by positivity
    simp only [real_inner_self_eq_norm_sq, conj_trivial]
    exact mul_pos ht this
  · exact Or.inl (subset_closure h)

theorem r26t8a_extend_C (e : Euc d) (he : e ≠ 0) : ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Euc d × Euc d → V), ContDiffOn ℝ (n : WithTop ℕ∞) f {w | w.2 ≠ 0} →
    (∀ j ≤ n, ∃ g : Euc d × Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d × Euc d) V,
        Continuous g ∧ ∀ w : Euc d × Euc d, w.2 ≠ 0 → g w = iteratedFDeriv ℝ j f w) →
    ∃ f' : Euc d × Euc d → V, ContDiff ℝ (n : WithTop ℕ∞) f' ∧ ∀ w : Euc d × Euc d, w.2 ≠ 0 → f' w = f w := by
  intro n
  induction n with
  | zero =>
    intro V _ _ f hf hg
    obtain ⟨g, hgc, hgw⟩ := hg 0 le_rfl
    refine ⟨fun w => continuousMultilinearCurryFin0 ℝ (Euc d × Euc d) V (g w), ?_, fun w hw => ?_⟩
    · exact contDiff_zero.2 ((continuousMultilinearCurryFin0 ℝ (Euc d × Euc d) V).continuous.comp hgc)
    · show continuousMultilinearCurryFin0 ℝ (Euc d × Euc d) V (g w) = f w
      rw [hgw w hw, iteratedFDeriv_zero_eq_comp]
      simp
  | succ n ih =>
    intro V _ _ f hf hg
    set U : Set (Euc d × Euc d) := {w | w.2 ≠ 0} with hU
    have hUo : IsOpen U := isOpen_ne.preimage continuous_snd
    obtain ⟨g0, hg0c, hg0w⟩ := hg 0 (Nat.zero_le _)
    obtain ⟨g1, hg1c, hg1w⟩ := hg 1 (by omega)
    set f0 : Euc d × Euc d → V := fun w => continuousMultilinearCurryFin0 ℝ (Euc d × Euc d) V (g0 w) with hf0
    set G : Euc d × Euc d → (Euc d × Euc d →L[ℝ] V) :=
      fun w => continuousMultilinearCurryFin1 ℝ (Euc d × Euc d) V (g1 w) with hG
    have hf0c : Continuous f0 := (continuousMultilinearCurryFin0 ℝ (Euc d × Euc d) V).continuous.comp hg0c
    have hf0w : ∀ w ∈ U, f0 w = f w := fun w hw => by
      show continuousMultilinearCurryFin0 ℝ (Euc d × Euc d) V (g0 w) = f w
      rw [hg0w w hw, iteratedFDeriv_zero_eq_comp]; simp
    have hGc : Continuous G := (continuousMultilinearCurryFin1 ℝ (Euc d × Euc d) V).continuous.comp hg1c
    have hGw : ∀ w ∈ U, G w = fderiv ℝ f w := fun w hw => by
      show continuousMultilinearCurryFin1 ℝ (Euc d × Euc d) V (g1 w) = fderiv ℝ f w
      rw [hg1w w hw]
      refine ContinuousLinearMap.ext fun v => ?_
      simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    -- the two opposite half-spaces
    set Hp : Set (Euc d × Euc d) := {w | 0 < inner ℝ w.2 e} with hHp
    set Hm : Set (Euc d × Euc d) := {w | inner ℝ w.2 e < 0} with hHm
    have hHpo : IsOpen Hp := isOpen_lt continuous_const ((continuous_snd.inner continuous_const))
    have hHmo : IsOpen Hm := isOpen_lt ((continuous_snd.inner continuous_const)) continuous_const
    have hHpc : Convex ℝ Hp := by
      intro a ha b hb s t hs ht hst
      show 0 < inner ℝ (s • a + t • b).2 e
      simp only [Prod.smul_snd, Prod.fst_add, Prod.snd_add, inner_add_left, inner_smul_left, conj_trivial]
      have ha' : 0 < inner ℝ a.2 e := ha
      have hb' : 0 < inner ℝ b.2 e := hb
      rcases hs.eq_or_lt with h | h
      · subst h; have : t = 1 := by linarith
        subst this; simpa using hb'
      · nlinarith [mul_pos h ha', mul_nonneg ht hb'.le]
    have hHmc : Convex ℝ Hm := by
      intro a ha b hb s t hs ht hst
      show inner ℝ (s • a + t • b).2 e < 0
      simp only [Prod.smul_snd, Prod.fst_add, Prod.snd_add, inner_add_left, inner_smul_left, conj_trivial]
      have ha' : inner ℝ a.2 e < 0 := ha
      have hb' : inner ℝ b.2 e < 0 := hb
      rcases hs.eq_or_lt with h | h
      · subst h; have : t = 1 := by linarith
        subst this; simpa using hb'
      · nlinarith [mul_neg_of_pos_of_neg h ha', mul_nonpos_of_nonneg_of_nonpos ht hb'.le]
    have hHpU : Hp ⊆ U := fun w hw h0 => by
      have : inner ℝ w.2 e = 0 := by rw [show w.2 = 0 from h0]; simp
      exact absurd hw (by simp [hHp, this])
    have hHmU : Hm ⊆ U := fun w hw h0 => by
      have : inner ℝ w.2 e = 0 := by rw [show w.2 = 0 from h0]; simp
      exact absurd hw (by simp [hHm, this])
    have hcover := r26t8a_halfspace_cover e he
    have hfdiffU : DifferentiableOn ℝ f U := (hf.differentiableOn (by simp))
    have hhalf : ∀ (s : Set (Euc d × Euc d)), Convex ℝ s → IsOpen s → s ⊆ U → ∀ x,
        HasFDerivWithinAt f0 (G x) (closure s) x := by
      intro s hsc hso hsU x
      have hev : ∀ y ∈ s, f0 =ᶠ[𝓝 y] f := fun y hy => by
        filter_upwards [hUo.mem_nhds (hsU hy)] with w hw using hf0w w hw
      refine hasFDerivWithinAt_closure_of_tendsto_fderiv (fun y hy => ?_) hsc hso
        (fun y _ => hf0c.continuousWithinAt) ?_
      · exact ((hfdiffU y (hsU hy)).differentiableAt (hUo.mem_nhds (hsU hy))).congr_of_eventuallyEq (hev y hy)
          |>.differentiableWithinAt
      · refine ((hGc.tendsto x).mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        rw [(hev y hy).fderiv_eq, hGw y (hsU hy)]
    have hderiv : ∀ x, HasFDerivAt f0 (G x) x := fun x => by
      have := (hhalf Hp hHpc hHpo hHpU x).union (hhalf Hm hHmc hHmo hHmU x)
      rw [hcover, hasFDerivWithinAt_univ] at this
      exact this
    have hfd : fderiv ℝ f0 = G := funext fun x => (hderiv x).fderiv
    have hdense : Dense U := by
      rw [dense_iff_closure_eq]
      apply Set.eq_univ_of_univ_subset
      rw [← hcover]
      exact Set.union_subset (closure_mono hHpU) (closure_mono hHmU)
    set f1 : Euc d × Euc d → (Euc d × Euc d →L[ℝ] V) := fun w => fderiv ℝ f w with hf1def
    have hf1 : ContDiffOn ℝ (n : WithTop ℕ∞) f1 U :=
      hf.fderiv_of_isOpen hUo (by exact_mod_cast le_refl (n + 1))
    have hg1' : ∀ j ≤ n, ∃ g' : Euc d × Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d × Euc d)
        (Euc d × Euc d →L[ℝ] V), Continuous g' ∧ ∀ w : Euc d × Euc d, w.2 ≠ 0 → g' w = iteratedFDeriv ℝ j f1 w := by
      intro j hj
      obtain ⟨gj, hgjc, hgjw⟩ := hg (j + 1) (by omega)
      refine ⟨fun w => continuousMultilinearCurryRightEquiv' ℝ j (Euc d × Euc d) V (gj w),
        (continuousMultilinearCurryRightEquiv' ℝ j (Euc d × Euc d) V).continuous.comp hgjc, fun w hw => ?_⟩
      show continuousMultilinearCurryRightEquiv' ℝ j (Euc d × Euc d) V (gj w) = _
      rw [hgjw w hw, iteratedFDeriv_succ_eq_comp_right]
      simp [hf1def]
    obtain ⟨f1', hf1'd, hf1'w⟩ := ih f1 hf1 hg1'
    have hf1G : f1' = G :=
      Continuous.ext_on hdense hf1'd.continuous hGc (fun w hw => by rw [hf1'w w hw, hGw w hw])
    refine ⟨f0, ?_, hf0w⟩
    have hn : (n : WithTop ℕ∞) ≠ ⊤ := by exact_mod_cast WithTop.coe_ne_top
    have := (contDiff_succ_iff_fderiv (𝕜 := ℝ) (f := f0) (n := (n : WithTop ℕ∞))).2
      ⟨fun x => (hderiv x).differentiableAt, fun h => absurd h hn, by rw [hfd, ← hf1G]; exact hf1'd⟩
    exact_mod_cast this

end HRS.MS.R26T8A
