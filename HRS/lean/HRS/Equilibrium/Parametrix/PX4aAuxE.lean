import HRS.Equilibrium.Parametrix.PX4aAuxD

/-!
# Packet PX4a auxiliaries E: the shear `(X, z) ↦ (X + λ z, z)` and typed derivative bounds

The chart `(X, z)` (midpoint) and the left chart `(Y, w)` (`Y = X - z/2`) differ by the shear
`T_λ(Y, w) = (Y + λ w, w)`, `λ = 1/2`.  Typed derivative bounds are transported by `T_λ` with the
loss factor `(1 + |λ|)^c` (the tangential derivatives are free).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

/-- The shear `(X, z) ↦ (X + λ z, z)`. -/
def shearCLM (d : ℕ) (lam : ℝ) : Euc d × Euc d →L[ℝ] Euc d × Euc d :=
  ((ContinuousLinearMap.fst ℝ (Euc d) (Euc d)) + lam • (ContinuousLinearMap.snd ℝ (Euc d) (Euc d))).prod
    (ContinuousLinearMap.snd ℝ (Euc d) (Euc d))

lemma shearCLM_apply (lam : ℝ) (p : Euc d × Euc d) : shearCLM d lam p = (p.1 + lam • p.2, p.2) := rfl

theorem tb_dirD_shear {G : Euc d × Euc d → ℝ} {q : Euc d × Euc d} {a c : ℕ} {W₁ W₂ : ℝ}
    (hG : ContDiffAt ℝ ((a + c + 1 : ℕ) : WithTop ℕ∞) G q) (lam : ℝ) (e : Euc d)
    (h1 : TB G q (a + 1) c W₁) (h2 : TB G q a (c + 1) W₂) :
    TB (dirD (lam • e, e) G) q a c ((|lam| * W₁ + W₂) * ‖e‖) := by
  intro u v
  have hG1 : ContDiffAt ℝ ((a + c : ℕ) : WithTop ℕ∞) (dirD (e, (0 : Euc d)) G) q :=
    (hG.fderiv_right_succ (n := a + c)).clm_apply contDiffAt_const
  have hG2 : ContDiffAt ℝ ((a + c : ℕ) : WithTop ℕ∞) (dirD ((0 : Euc d), e) G) q :=
    (hG.fderiv_right_succ (n := a + c)).clm_apply contDiffAt_const
  have hsplit : dirD (lam • e, e) G =
      lam • dirD (e, (0 : Euc d)) G + dirD ((0 : Euc d), e) G := by
    funext p
    simp only [dirD, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : (lam • e, e) = lam • (e, (0 : Euc d)) + ((0 : Euc d), e) := by
      ext <;> simp
    rw [this, map_add, map_smul]
    rfl
  have hG1' : ContDiffAt ℝ ((a + c : ℕ) : WithTop ℕ∞) (lam • dirD (e, (0 : Euc d)) G) q :=
    ContDiffAt.const_smul lam hG1
  rw [hsplit, iteratedFDeriv_add_apply hG1' hG2, iteratedFDeriv_const_smul_apply hG1]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [iteratedFDeriv_dirD hG, iteratedFDeriv_dirD hG]
  have hp1 : 0 ≤ ∏ i, ‖u i‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hp2 : 0 ≤ ∏ j, ‖v j‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have T1 : |iteratedFDeriv ℝ (a + c + 1) G q (Fin.snoc (pat u v) (e, (0 : Euc d)))| ≤
      W₁ * ‖e‖ * (∏ i, ‖u i‖) * ∏ j, ‖v j‖ := by
    rw [← iteratedFDeriv_cons_eq_snoc hG]
    have := h1 (Fin.cons e u) v
    rw [pat_cons_left, iteratedFDeriv_cast, prod_norm_cons] at this
    linarith
  have T2 : |iteratedFDeriv ℝ (a + c + 1) G q (Fin.snoc (pat u v) ((0 : Euc d), e))| ≤
      W₂ * ‖e‖ * (∏ i, ‖u i‖) * ∏ j, ‖v j‖ := by
    have h2' := h2 u (Fin.snoc v e)
    rw [pat_snoc_right, prod_norm_snoc] at h2'
    refine h2'.trans (le_of_eq ?_)
    ring
  calc _ ≤ |lam| * |iteratedFDeriv ℝ (a + c + 1) G q (Fin.snoc (pat u v) (e, (0 : Euc d)))| +
        |iteratedFDeriv ℝ (a + c + 1) G q (Fin.snoc (pat u v) ((0 : Euc d), e))| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
    _ ≤ |lam| * (W₁ * ‖e‖ * (∏ i, ‖u i‖) * ∏ j, ‖v j‖) + W₂ * ‖e‖ * (∏ i, ‖u i‖) * ∏ j, ‖v j‖ :=
        add_le_add (mul_le_mul_of_nonneg_left T1 (abs_nonneg _)) T2
    _ = _ := by ring

lemma dirD_comp_shear {U : Set (Euc d × Euc d)} (hU : IsOpen U) {f : Euc d × Euc d → ℝ}
    (hf : ContDiffOn ℝ 1 f U) (lam : ℝ) (e : Euc d) {p : Euc d × Euc d}
    (hp : shearCLM d lam p ∈ U) :
    dirD ((0 : Euc d), e) (fun p' => f (shearCLM d lam p')) p =
      dirD (lam • e, e) f (shearCLM d lam p) := by
  have hd : DifferentiableAt ℝ f (shearCLM d lam p) :=
    (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp)
  have h2 : HasFDerivAt (fun p' => f (shearCLM d lam p')) ((fderiv ℝ f (shearCLM d lam p)).comp (shearCLM d lam)) p :=
    hd.hasFDerivAt.comp p (shearCLM d lam).hasFDerivAt
  unfold dirD
  rw [h2.fderiv]
  simp [shearCLM_apply]

set_option maxHeartbeats 1600000 in
/-- Typed derivative bounds are transported by the shear, with the loss `(1 + |λ|)^j`. -/
theorem tb_shear (lam : ℝ) {U : Set (Euc d × Euc d)} (hU : IsOpen U) :
    ∀ (j i : ℕ) (f : Euc d × Euc d → ℝ) (W : ℕ → ℝ), (∀ j', W j' ≤ W (j' + 1)) →
      ContDiffOn ℝ ((i + j : ℕ) : WithTop ℕ∞) f U → ∀ q : Euc d × Euc d, shearCLM d lam q ∈ U →
      (∀ i' j', i' + j' ≤ i + j → TB f (shearCLM d lam q) i' j' (W j')) →
      TB (fun p => f (shearCLM d lam p)) q i j ((1 + |lam|) ^ j * W j) := by
  intro j
  induction j with
  | zero =>
    intro i f W hW hf q hq hT u v
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    subst hv
    have h1 := iteratedFDeriv_comp_clm_of_open_n hU hf (shearCLM d lam) (x := q) hq
      (i := i + 0) le_rfl
    change |(iteratedFDeriv ℝ (i + 0) (f ∘ shearCLM d lam) q) _| ≤ _
    rw [h1]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have e : (fun l => shearCLM d lam (pat u (Fin.elim0 : Fin 0 → Euc d) l)) =
        pat u (Fin.elim0 : Fin 0 → Euc d) := by
      funext l
      unfold pat
      obtain ⟨l', rfl⟩ : ∃ l' : Fin i, l = Fin.castAdd 0 l' := ⟨⟨l.1, by have := l.2; omega⟩, by ext; simp⟩
      rw [Fin.append_left]
      simp [shearCLM_apply]
    rw [e]
    have := hT i 0 le_rfl u Fin.elim0
    simpa using this
  | succ j ih =>
    intro i f W hW hf q hq hT u v
    set e : Euc d := v (Fin.last j) with he
    set v' : Fin j → Euc d := Fin.init v with hv'
    have hv : v = Fin.snoc v' e := (Fin.snoc_init_self v).symm
    have hf1 : ContDiffOn ℝ (1 : WithTop ℕ∞) f U := by
      refine hf.of_le ?_
      exact_mod_cast (by omega : 1 ≤ i + (j + 1))
    have hfat : ContDiffAt ℝ ((i + j + 1 : ℕ) : WithTop ℕ∞) f (shearCLM d lam q) :=
      (hf.contDiffAt (hU.mem_nhds hq)).of_le (by exact_mod_cast (by omega : i + j + 1 ≤ i + (j + 1)))
    -- the composite is smooth near `q`
    have hcomp : ContDiffAt ℝ ((i + (j + 1) : ℕ) : WithTop ℕ∞) (fun p => f (shearCLM d lam p)) q :=
      (hf.contDiffAt (hU.mem_nhds hq)).comp q (shearCLM d lam).contDiff.contDiffAt
    have hcomp' : ContDiffAt ℝ ((i + j + 1 : ℕ) : WithTop ℕ∞) (fun p => f (shearCLM d lam p)) q :=
      hcomp.of_le (by exact_mod_cast (by omega : i + j + 1 ≤ i + (j + 1)))
    -- f' = dirD (λ e, e) f
    set f' : Euc d × Euc d → ℝ := dirD (lam • e, e) f with hf'
    have hf'sm : ContDiffOn ℝ ((i + j : ℕ) : WithTop ℕ∞) f' U :=
      contDiffOn_dirD hU (hf.of_le (by exact_mod_cast (by omega : i + j + 1 ≤ i + (j + 1)))) _
    have hq' : shearCLM d lam q ∈ U := hq
    -- bounds for f'
    have hT' : ∀ i' j', i' + j' ≤ i + j →
        TB f' (shearCLM d lam q) i' j' (((1 + |lam|) * W (j' + 1)) * ‖e‖) := by
      intro i' j' hij
      have hcd : ContDiffAt ℝ ((i' + j' + 1 : ℕ) : WithTop ℕ∞) f (shearCLM d lam q) :=
        (hf.contDiffAt (hU.mem_nhds hq)).of_le (by exact_mod_cast (by omega : i' + j' + 1 ≤ i + (j + 1)))
      have := tb_dirD_shear hcd lam e (hT (i' + 1) j' (by omega)) (hT i' (j' + 1) (by omega))
      refine fun u' v' => (this u' v').trans ?_
      have hP : 0 ≤ (∏ x, ‖u' x‖) * ∏ y, ‖v' y‖ :=
        mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      have hW0 : W j' ≤ W (j' + 1) := hW j'
      have h1 : (|lam| * W j' + W (j' + 1)) * ‖e‖ ≤ ((1 + |lam|) * W (j' + 1)) * ‖e‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have : |lam| * W j' ≤ |lam| * W (j' + 1) := mul_le_mul_of_nonneg_left hW0 (abs_nonneg _)
        nlinarith
      have h2 := mul_le_mul_of_nonneg_right h1 hP
      calc (|lam| * W j' + W (j' + 1)) * ‖e‖ * (∏ x, ‖u' x‖) * ∏ y, ‖v' y‖
          = (|lam| * W j' + W (j' + 1)) * ‖e‖ * ((∏ x, ‖u' x‖) * ∏ y, ‖v' y‖) := by ring
        _ ≤ _ := by
          have := h2
          calc _ ≤ ((1 + |lam|) * W (j' + 1)) * ‖e‖ * ((∏ x, ‖u' x‖) * ∏ y, ‖v' y‖) := this
            _ = _ := by ring
    have hWmono : ∀ j', ((1 + |lam|) * W (j' + 1)) * ‖e‖ ≤ ((1 + |lam|) * W (j' + 1 + 1)) * ‖e‖ := by
      intro j'
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hW _) (by positivity)) (norm_nonneg _)
    have IH := ih i f' (fun j' => ((1 + |lam|) * W (j' + 1)) * ‖e‖) hWmono hf'sm q hq' hT'
    -- the derivative of the composite
    have heq : dirD ((0 : Euc d), e) (fun p => f (shearCLM d lam p)) =ᶠ[𝓝 q]
        fun p => f' (shearCLM d lam p) := by
      have hU' : IsOpen ((shearCLM d lam) ⁻¹' U) := hU.preimage (shearCLM d lam).continuous
      filter_upwards [hU'.mem_nhds hq] with p hp
      exact dirD_comp_shear hU hf1 lam e hp
    have hpat : pat u v = (Fin.snoc (pat u v') ((0 : Euc d), e) : Fin (i + j + 1) → Euc d × Euc d) := by
      conv_lhs => rw [hv]
      exact pat_snoc_right u v' e
    have hstep : iteratedFDeriv ℝ (i + (j + 1)) (fun p => f (shearCLM d lam p)) q (pat u v) =
        iteratedFDeriv ℝ (i + j) (dirD ((0 : Euc d), e) (fun p => f (shearCLM d lam p))) q (pat u v') := by
      rw [hpat]; exact (iteratedFDeriv_dirD hcomp' ((0 : Euc d), e) (pat u v')).symm
    rw [hstep, (heq.iteratedFDeriv ℝ (i + j)).eq_of_nhds]
    have key := IH u v'
    rw [prod_norm_init v]
    simp only [hv', he] at key ⊢
    calc _ ≤ (1 + |lam|) ^ j * ((1 + |lam|) * W (j + 1) * ‖v (Fin.last j)‖) * (∏ i, ‖u i‖) *
          ∏ j_1, ‖Fin.init v j_1‖ := key
      _ = _ := by ring

end HRS.Parx

end
