import HRS.Equilibrium.Parametrix.PX1AuxMul

/-!
# Prop 4.13 parametrix, packet PX1: `x`-derivatives of conormal kernels

`conormal_partial_fst`: `∂_{x_j} = ½ ∂_{X_j} + ∂_{z_j}` in the chart `(X, z)`; the typed derivative
bounds of `F` of types `(a+1, c)` and `(a, c+1)` bound those of `∂_{x_j} F` of type `(a, c)`.  The
`X`-slot is moved to the front with the symmetry of iterated derivatives.
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx

variable {d : ℕ}

theorem pat_cons_left {a c : ℕ} (e : Euc d) (u : Fin a → Euc d) (v : Fin c → Euc d) :
    pat (Fin.cons e u : Fin (a + 1) → Euc d) v =
      (Fin.cons ((e, (0 : Euc d)) : Euc d × Euc d) (pat u v) : Fin (a + c + 1) → Euc d × Euc d) ∘
        Fin.cast (Nat.add_right_comm a 1 c) := by
  unfold pat
  have : (fun i => ((Fin.cons e u : Fin (a + 1) → Euc d) i, (0 : Euc d))) =
      (Fin.cons ((e, (0 : Euc d)) : Euc d × Euc d) (fun i => (u i, (0 : Euc d))) :
        Fin (a + 1) → Euc d × Euc d) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i <;> simp
  rw [this, Fin.append_cons]

theorem prod_norm_cons {a : ℕ} (e : Euc d) (u : Fin a → Euc d) :
    ∏ i, ‖(Fin.cons e u : Fin (a + 1) → Euc d) i‖ = ‖e‖ * ∏ i, ‖u i‖ := by
  rw [Fin.prod_univ_succ]
  simp

theorem tb_partial {G : Euc d × Euc d → ℝ} {q : Euc d × Euc d} {a c : ℕ} {W₁ W₂ : ℝ}
    (hG : ContDiffAt ℝ ((a + c + 1 : ℕ) : WithTop ℕ∞) G q) (e : Euc d) (he : ‖e‖ = 1)
    (h1 : TB G q (a + 1) c W₁) (h2 : TB G q a (c + 1) W₂) :
    TB (dirD (((1 / 2 : ℝ) • e), e) G) q a c ((1 / 2) * W₁ + W₂) := by
  intro u v
  have hG1 : ContDiffAt ℝ ((a + c : ℕ) : WithTop ℕ∞) (dirD (e, (0 : Euc d)) G) q :=
    (hG.fderiv_right_succ (n := a + c)).clm_apply contDiffAt_const
  have hG2 : ContDiffAt ℝ ((a + c : ℕ) : WithTop ℕ∞) (dirD ((0 : Euc d), e) G) q :=
    (hG.fderiv_right_succ (n := a + c)).clm_apply contDiffAt_const
  have hsplit : dirD (((1 / 2 : ℝ) • e), e) G =
      (1 / 2 : ℝ) • dirD (e, (0 : Euc d)) G + dirD ((0 : Euc d), e) G := by
    funext p
    simp only [dirD, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : (((1 / 2 : ℝ) • e), e) = (1 / 2 : ℝ) • (e, (0 : Euc d)) + ((0 : Euc d), e) := by
      ext <;> simp
    rw [this, map_add, map_smul]
    rfl
  have hG1' : ContDiffAt ℝ ((a + c : ℕ) : WithTop ℕ∞) ((1 / 2 : ℝ) • dirD (e, (0 : Euc d)) G) q :=
    ContDiffAt.const_smul (1 / 2 : ℝ) hG1
  rw [hsplit, iteratedFDeriv_add_apply hG1' hG2, iteratedFDeriv_const_smul_apply hG1]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [iteratedFDeriv_dirD hG, iteratedFDeriv_dirD hG]
  have hp1 : 0 ≤ ∏ i, ‖u i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hp2 : 0 ≤ ∏ j, ‖v j‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have T1 : |iteratedFDeriv ℝ (a + c + 1) G q (Fin.snoc (pat u v) (e, (0 : Euc d)))| ≤
      W₁ * (∏ i, ‖u i‖) * ∏ j, ‖v j‖ := by
    rw [← iteratedFDeriv_cons_eq_snoc hG]
    have := h1 (Fin.cons e u) v
    rw [pat_cons_left, iteratedFDeriv_cast, prod_norm_cons, he, one_mul] at this
    exact this
  have T2 : |iteratedFDeriv ℝ (a + c + 1) G q (Fin.snoc (pat u v) ((0 : Euc d), e))| ≤
      W₂ * (∏ i, ‖u i‖) * ∏ j, ‖v j‖ := by
    have := h2 u (Fin.snoc v e)
    rw [pat_snoc_right, prod_norm_snoc, he, mul_one] at this
    exact this
  calc _ ≤ |(1 / 2 : ℝ)| * |iteratedFDeriv ℝ (a + c + 1) G q (Fin.snoc (pat u v) (e, (0 : Euc d)))| +
        |iteratedFDeriv ℝ (a + c + 1) G q (Fin.snoc (pat u v) ((0 : Euc d), e))| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
    _ ≤ (1 / 2) * (W₁ * (∏ i, ‖u i‖) * ∏ j, ‖v j‖) + W₂ * (∏ i, ‖u i‖) * ∏ j, ‖v j‖ := by
        have : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_pos (by norm_num)
        rw [this]
        exact add_le_add (mul_le_mul_of_nonneg_left T1 (by norm_num)) T2
    _ = _ := by ring

section Geometry
variable {d : ℕ}

theorem mk_toEuc' (n : Lattice d) : Torus.mk (Lattice.toEuc n) = (0 : Torus d) := by
  funext i; simp [Torus.mk, Lattice.toEuc]

theorem mk_add' (x y : Euc d) : Torus.mk (x + y) = Torus.mk x + Torus.mk y := by
  funext i; simp [Torus.mk]

/-- The slice derivative `∂_{x_j} F (x, y)` of a kernel, in the lift: `fderiv (lift2 F) (e_j, 0)`. -/
theorem lift2_partial {F : Torus d → Torus d → ℝ} {m : ℕ}
    (hF : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 F) (offDiag d)) (hm : 1 ≤ m) (j : Fin d)
    {p : Euc d × Euc d} (hp : p ∈ offDiag d) :
    lift2 (fun x y => Torus.partialDeriv j (fun z => F z y) x) p =
      fderiv ℝ (lift2 F) p (EuclideanSpace.single j (1 : ℝ), 0) := by
  have hd : DifferentiableAt ℝ (lift2 F) p :=
    (hF.differentiableOn (by exact_mod_cast (by omega : m ≠ 0))).differentiableAt
      (isOpen_offDiag.mem_nhds hp)
  obtain ⟨n, hn⟩ := Torus.rep_mk p.1
  set g : Euc d → ℝ := fun x' => lift2 F (x', p.2) with hg
  have hper : ∀ x, g (x + Lattice.toEuc n) = g x := by
    intro x
    simp only [hg, lift2]
    rw [mk_add', mk_toEuc', add_zero]
  have h1 : fderiv ℝ g (p.1 + Lattice.toEuc n) = fderiv ℝ g p.1 := by
    have e : (fun x => g (x + Lattice.toEuc n)) = g := funext hper
    have := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := p.1) (Lattice.toEuc n)
    rw [e] at this
    exact this.symm
  have h2 : lift2 (fun x y => Torus.partialDeriv j (fun z => F z y) x) p =
      fderiv ℝ g (Torus.rep (Torus.mk p.1)) (EuclideanSpace.single j (1 : ℝ)) := by
    simp only [lift2, Torus.partialDeriv, Torus.lift, hg]
    rfl
  rw [h2, hn, h1]
  have := fderiv_slice_fst (G := lift2 F) (X := p.1) (z := p.2) hd (EuclideanSpace.single j (1 : ℝ))
  exact this

theorem toChart_partial {F : Torus d → Torus d → ℝ} {m : ℕ}
    (hF : ContDiffOn ℝ (m : WithTop ℕ∞) (lift2 F) (offDiag d)) (hm : 1 ≤ m) (j : Fin d)
    {q : Euc d × Euc d} (hq : q ∈ Uc d) :
    toChart (fun x y => Torus.partialDeriv j (fun z => F z y) x) q =
      fderiv ℝ (toChart F) q (((1 / 2 : ℝ) • EuclideanSpace.single j (1 : ℝ)), EuclideanSpace.single j (1 : ℝ)) := by
  have hTq : chartT d q ∈ offDiag d := hq
  have hd : DifferentiableAt ℝ (lift2 F) (chartT d q) :=
    (hF.differentiableOn (by exact_mod_cast (by omega : m ≠ 0))).differentiableAt
      (isOpen_offDiag.mem_nhds hTq)
  have h1 : toChart (fun x y => Torus.partialDeriv j (fun z => F z y) x) q =
      lift2 (fun x y => Torus.partialDeriv j (fun z => F z y) x) (chartT d q) := by
    rw [toChart_eq]; rfl
  rw [h1, lift2_partial hF hm j hTq]
  have h2 : HasFDerivAt (toChart F) ((fderiv ℝ (lift2 F) (chartT d q)).comp (chartT d)) q := by
    rw [toChart_eq]
    exact hd.hasFDerivAt.comp q (chartT d).hasFDerivAt
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  rw [chartT_apply]
  refine Prod.ext ?_ ?_
  · show EuclideanSpace.single j (1 : ℝ) = (1 / 2 : ℝ) • EuclideanSpace.single j (1 : ℝ) +
      (1 / 2 : ℝ) • EuclideanSpace.single j (1 : ℝ)
    rw [← add_smul]; norm_num
  · show (0 : Euc d) = (1 / 2 : ℝ) • EuclideanSpace.single j (1 : ℝ) -
      (1 / 2 : ℝ) • EuclideanSpace.single j (1 : ℝ)
    exact (sub_self _).symm

theorem tb_congr {f g : Euc d × Euc d → ℝ} {q : Euc d × Euc d} {a c : ℕ} {W : ℝ}
    (h : f =ᶠ[𝓝 q] g) (hT : TB g q a c W) : TB f q a c W := by
  intro u v
  rw [(h.iteratedFDeriv ℝ (a + c)).eq_of_nhds]
  exact hT u v

theorem norm_single_prod (j : Fin d) : ‖((EuclideanSpace.single j (1 : ℝ) : Euc d), (0 : Euc d))‖ = 1 := by
  rw [Prod.norm_def]
  simp

theorem conormal_partial_fst_aux {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : ConormalL σ b m B F) (hm : 1 ≤ m) (j : Fin d) :
    ConormalL (σ + 1) (fun c => max (b c) (b (c + 1))) (m - 1) (2 * B)
      (fun x y => Torus.partialDeriv j (fun z => F z y) x) where
  smooth := by
    have hfd : ContDiffOn ℝ ((m - 1 : ℕ) : WithTop ℕ∞)
        (fun p => fderiv ℝ (lift2 F) p (EuclideanSpace.single j (1 : ℝ), 0)) (offDiag d) :=
      (hF.smooth.fderiv_of_isOpen isOpen_offDiag (m := ((m - 1 : ℕ) : WithTop ℕ∞))
        (by exact_mod_cast (by omega : m - 1 + 1 ≤ m))).clm_apply contDiffOn_const
    exact hfd.congr (fun p hp => lift2_partial hF.smooth hm j hp)
  near := by
    intro a c hac X z hz hzr
    have hq : (X, z) ∈ Uc d := mem_Uc hz hzr
    set r := ‖z‖ with hr
    set L := 1 + |Real.log r| with hL
    have hr0 : 0 < r := norm_pos_iff.mpr hz
    have hr1 : r ≤ 1 := by unfold r0 at hzr; linarith
    have hL1 : 1 ≤ L := by linarith [abs_nonneg (Real.log r)]
    have hB : 0 ≤ B := by
      have h00 := hF.near 0 0 (Nat.zero_le _) X z hz hzr
      have h0 : 0 ≤ ‖mixedDeriv 0 0 (toChart F) X z‖ := ContinuousMultilinearMap.opNorm_nonneg _
      have hw : 0 < 1 + r ^ (-(σ + ((0 : ℕ) : ℝ))) * L ^ (b 0) := by positivity
      by_contra hneg
      rw [not_le] at hneg
      have := mul_neg_of_neg_of_pos hneg hw
      linarith
    set e : Euc d := EuclideanSpace.single j (1 : ℝ) with he
    have hne : ‖e‖ = 1 := by simp [he]
    have hs : ContDiffOn ℝ (((m - 1 : ℕ)) : WithTop ℕ∞)
        (lift2 (fun x y => Torus.partialDeriv j (fun z => F z y) x)) (offDiag d) := by
      have hfd : ContDiffOn ℝ ((m - 1 : ℕ) : WithTop ℕ∞)
          (fun p => fderiv ℝ (lift2 F) p (EuclideanSpace.single j (1 : ℝ), 0)) (offDiag d) :=
        (hF.smooth.fderiv_of_isOpen isOpen_offDiag (m := ((m - 1 : ℕ) : WithTop ℕ∞))
          (by exact_mod_cast (by omega : m - 1 + 1 ≤ m))).clm_apply contDiffOn_const
      exact hfd.congr (fun p hp => lift2_partial hF.smooth hm j hp)
    have hG'd : ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞)
        (toChart (fun x y => Torus.partialDeriv j (fun z => F z y) x)) (Uc d) :=
      (toChart_contDiffOn hs).of_le (by exact_mod_cast hac)
    have hGd : ∀ k ≤ m, ContDiffOn ℝ (k : WithTop ℕ∞) (toChart F) (Uc d) := fun k hk =>
      (toChart_contDiffOn hF.smooth).of_le (by exact_mod_cast hk)
    have hGat : ContDiffAt ℝ ((a + c + 1 : ℕ) : WithTop ℕ∞) (toChart F) (X, z) :=
      (hGd (a + c + 1) (by omega)).contDiffAt (isOpen_Uc.mem_nhds hq)
    have hev : toChart (fun x y => Torus.partialDeriv j (fun z => F z y) x) =ᶠ[𝓝 (X, z)]
        dirD (((1 / 2 : ℝ) • e), e) (toChart F) := by
      filter_upwards [isOpen_Uc.mem_nhds hq] with q' hq'
      exact toChart_partial hF.smooth hm j hq'
    set W₁ : ℝ := B * (1 + r ^ (-(σ + (c : ℝ))) * L ^ (b c)) with hW₁
    set W₂ : ℝ := B * (1 + r ^ (-(σ + ((c + 1 : ℕ) : ℝ))) * L ^ (b (c + 1))) with hW₂
    have hW₁0 : 0 ≤ W₁ := by simp only [hW₁]; positivity
    have hW₂0 : 0 ≤ W₂ := by simp only [hW₂]; positivity
    have T1 : TB (toChart F) (X, z) (a + 1) c W₁ :=
      tb_of_norm_le isOpen_Uc (hGd (a + 1 + c) (by omega)) hq
        (hF.near (a + 1) c (by omega) X z hz hzr)
    have T2 : TB (toChart F) (X, z) a (c + 1) W₂ :=
      tb_of_norm_le isOpen_Uc (hGd (a + (c + 1)) (by omega)) hq
        (hF.near a (c + 1) (by omega) X z hz hzr)
    have T := tb_congr hev (tb_partial hGat e hne T1 T2)
    have hnorm := norm_le_of_tb isOpen_Uc hG'd hq (by positivity) T
    refine hnorm.trans ?_
    -- comparison of the weights
    set Q := r ^ (-(σ + 1 + (c : ℝ))) * L ^ (max (b c) (b (c + 1))) with hQ
    have hQ0 : 0 ≤ Q := by simp only [hQ]; positivity
    have hP1 : r ^ (-(σ + (c : ℝ))) * L ^ (b c) ≤ Q := by
      have h1 : r ^ (-(σ + (c : ℝ))) ≤ r ^ (-(σ + 1 + (c : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
      have h2 : L ^ (b c) ≤ L ^ (max (b c) (b (c + 1))) := pow_le_pow_right₀ hL1 (le_max_left _ _)
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have hP2 : r ^ (-(σ + ((c + 1 : ℕ) : ℝ))) * L ^ (b (c + 1)) ≤ Q := by
      have h1 : r ^ (-(σ + ((c + 1 : ℕ) : ℝ))) = r ^ (-(σ + 1 + (c : ℝ))) := by
        congr 1; push_cast; ring
      have h2 : L ^ (b (c + 1)) ≤ L ^ (max (b c) (b (c + 1))) :=
        pow_le_pow_right₀ hL1 (le_max_right _ _)
      rw [h1]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    simp only [hW₁, hW₂]
    have : 0 ≤ B * (1 + Q) := mul_nonneg hB (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hP1 hB, mul_le_mul_of_nonneg_left hP2 hB]
  far := by
    intro k hk p hp hr
    have hB : 0 ≤ B := (norm_nonneg _).trans (hF.far 0 (Nat.zero_le _) p hp hr)
    have hat : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (lift2 F) p :=
      (hF.smooth.contDiffAt (isOpen_offDiag.mem_nhds hp)).of_le (by exact_mod_cast (by omega : k + 1 ≤ m))
    have hev : lift2 (fun x y => Torus.partialDeriv j (fun z => F z y) x) =ᶠ[𝓝 p]
        dirD (EuclideanSpace.single j (1 : ℝ), (0 : Euc d)) (lift2 F) := by
      filter_upwards [isOpen_offDiag.mem_nhds hp] with p' hp'
      exact lift2_partial hF.smooth hm j hp'
    rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
    refine (norm_iteratedFDeriv_dirD_le hat _).trans ?_
    rw [norm_single_prod, mul_one]
    have := hF.far (k + 1) (by omega) p hp hr
    linarith

end Geometry

end HRS.Parx

end
