import HRS.Equilibrium.Parametrix.PX2Aux

/-!
# Packet PX2b auxiliaries: calculus of the mixed derivatives `mixedDeriv`

* `iteratedFDeriv_inner`, `mixedDeriv_snoc_apply` (the recursion
  `mixedDeriv a (c+1) G (u, v ⧺ w) = mixedDeriv a c (∂_{(0,w)} G) (u, v)`),
* additivity,
* `norm_mixedDeriv_le`: `‖mixedDeriv a c G X z‖ ≤ ‖D^{a+c} G (X,z)‖`,
* `norm_mixedDeriv_mul_pureZ`: the Leibniz estimate for a product `Ā(X,z) κ(z)` with `κ` independent of
  `X` (the `X`-derivatives never hit `κ`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### Unit-ball criterion for norms of multilinear maps -/

theorem opNorm_le_of_unit_bound' {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => V) W) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ u : Fin n → V, (∀ j, ‖u j‖ ≤ 1) → ‖f u‖ ≤ M) : ‖f‖ ≤ M := by
  classical
  refine f.opNorm_le_bound hM fun m => ?_
  set u : Fin n → V := fun j => if m j = 0 then 0 else ‖m j‖⁻¹ • m j with hu
  have hu1 : ∀ j, ‖u j‖ ≤ 1 := by
    intro j
    by_cases hj : m j = 0
    · simp [hu, hj]
    · simp only [hu, hj, if_false, norm_smul, norm_inv, norm_norm]
      rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hj)]
  have hm : m = fun j => ‖m j‖ • u j := by
    funext j
    by_cases hj : m j = 0
    · simp [hu, hj]
    · simp only [hu, hj, if_false, smul_smul]
      rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hj), one_smul]
  have : f m = (∏ j, ‖m j‖) • f u := by
    conv_lhs => rw [hm]
    rw [f.map_smul_univ]
  rw [this, norm_smul, norm_prod]
  simp only [norm_norm]
  calc (∏ j, ‖m j‖) * ‖f u‖ ≤ (∏ j, ‖m j‖) * M := by
        gcongr
        exact h u hu1
    _ = M * ∏ j, ‖m j‖ := by ring

theorem norm_mixed_le_of_unit {a c : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin a => Euc d)
      (ContinuousMultilinearMap ℝ (fun _ : Fin c => Euc d) ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ (u : Fin a → Euc d) (v : Fin c → Euc d), (∀ j, ‖u j‖ ≤ 1) → (∀ j, ‖v j‖ ≤ 1) →
      |T u v| ≤ M) : ‖T‖ ≤ M := by
  refine opNorm_le_of_unit_bound' T hM fun u hu => ?_
  refine opNorm_le_of_unit_bound' (T u) hM fun v hv => ?_
  exact h u v hu hv

theorem abs_mixed_le {a c : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin a => Euc d)
      (ContinuousMultilinearMap ℝ (fun _ : Fin c => Euc d) ℝ))
    (u : Fin a → Euc d) (v : Fin c → Euc d) (hu : ∀ j, ‖u j‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1) :
    |T u v| ≤ ‖T‖ := by
  rw [← Real.norm_eq_abs]
  have h1 : ‖T u v‖ ≤ ‖T u‖ * ∏ j, ‖v j‖ := (T u).le_opNorm v
  have h2 : ‖T u‖ ≤ ‖T‖ * ∏ j, ‖u j‖ := T.le_opNorm u
  have h3 : ∏ j, ‖v j‖ ≤ 1 := Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => hv j)
  have h4 : ∏ j, ‖u j‖ ≤ 1 := Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => hu j)
  calc ‖T u v‖ ≤ ‖T u‖ * ∏ j, ‖v j‖ := h1
    _ ≤ ‖T u‖ * 1 := by gcongr
    _ = ‖T u‖ := mul_one _
    _ ≤ ‖T‖ * ∏ j, ‖u j‖ := h2
    _ ≤ ‖T‖ * 1 := by gcongr
    _ = ‖T‖ := mul_one _

/-! ### The inner derivative as a total derivative -/

theorem iteratedFDeriv_inner {G : Euc d × Euc d → ℝ} (hG : ContDiff ℝ ∞' G) (c : ℕ)
    (X z : Euc d) :
    iteratedFDeriv ℝ c (fun z' => G (X, z')) z =
      (iteratedFDeriv ℝ c G (X, z)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) := by
  have hfun : (fun z' : Euc d => G (X, z')) =
      (fun p : Euc d × Euc d => G (p + (X, 0))) ∘ (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) := by
    funext z'; simp
  have hcd : ContDiff ℝ ∞' (fun p : Euc d × Euc d => G (p + (X, 0))) :=
    hG.comp (contDiff_id.add contDiff_const)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ hcd z (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  simp

theorem contDiff_inner {G : Euc d × Euc d → ℝ} (hG : ContDiff ℝ ∞' G) (c : ℕ) (z : Euc d) :
    ContDiff ℝ ∞' (fun X' : Euc d => iteratedFDeriv ℝ c (fun z' => G (X', z')) z) := by
  have : (fun X' : Euc d => iteratedFDeriv ℝ c (fun z' => G (X', z')) z) =
      (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin c => ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin c => Euc d × Euc d) ℝ →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin c => Euc d) ℝ) ∘
        (iteratedFDeriv ℝ c G) ∘ (fun X' : Euc d => (X', z)) := by
    funext X'
    simp [iteratedFDeriv_inner hG c X' z]
  rw [this]
  refine (ContinuousLinearMap.contDiff _).comp ?_
  exact (hG.iteratedFDeriv_right (m := ∞') (i := c) (by simp)).comp
    (contDiff_id.prodMk contDiff_const)

theorem iteratedFDeriv_apply_ml {k : ℕ}
    {Ψ : Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin k => Euc d) ℝ} (hΨ : ContDiff ℝ ∞' Ψ)
    (a : ℕ) (X : Euc d) (u : Fin a → Euc d) (v : Fin k → Euc d) :
    (iteratedFDeriv ℝ a Ψ X u) v = iteratedFDeriv ℝ a (fun X' => Ψ X' v) X u := by
  have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euc d) ℝ v).iteratedFDeriv_comp_left
    (f := Ψ) (x := X) hΨ.contDiffAt (i := a) (by exact_mod_cast le_top)
  have h2 : ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euc d) ℝ v) ∘ Ψ) =
      fun X' => Ψ X' v := rfl
  rw [h2] at h
  rw [h]
  rfl

theorem fderiv_inner_apply {G : Euc d × Euc d → ℝ} (hG : ContDiff ℝ ∞' G) (X' z' w : Euc d) :
    fderiv ℝ (fun y : Euc d => G (X', y)) z' w = fderiv ℝ G (X', z') (0, w) := by
  have h1 : HasFDerivAt G (fderiv ℝ G (X', z')) (X', z') :=
    (hG.differentiable (by simp) (X', z')).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Euc d => (X', y))
      ((0 : Euc d →L[ℝ] Euc d).prod (ContinuousLinearMap.id ℝ (Euc d))) z' :=
    (hasFDerivAt_const X' z').prodMk (hasFDerivAt_id z')
  have h3 : HasFDerivAt (fun y : Euc d => G (X', y))
      ((fderiv ℝ G (X', z')).comp ((0 : Euc d →L[ℝ] Euc d).prod (ContinuousLinearMap.id ℝ (Euc d)))) z' :=
    h1.comp z' h2
  rw [h3.fderiv]
  simp

theorem contDiff_fderiv_apply {G : Euc d × Euc d → ℝ} (hG : ContDiff ℝ ∞' G) (w : Euc d × Euc d) :
    ContDiff ℝ ∞' (fun p => fderiv ℝ G p w) := by
  have h := hG.fderiv_right (m := ∞') (by simp)
  exact (ContinuousLinearMap.apply ℝ ℝ w).contDiff.comp h

theorem contDiff_fderiv_apply' {κ : Euc d → ℝ} (hκ : ContDiff ℝ ∞' κ) (w : Euc d) :
    ContDiff ℝ ∞' (fun y => fderiv ℝ κ y w) := by
  have h := hκ.fderiv_right (m := ∞') (by simp)
  exact (ContinuousLinearMap.apply ℝ ℝ w).contDiff.comp h

theorem mixedDeriv_snoc_apply {G : Euc d × Euc d → ℝ} (hG : ContDiff ℝ ∞' G) (a c : ℕ)
    (X z : Euc d) (u : Fin a → Euc d) (v : Fin c → Euc d) (w : Euc d) :
    mixedDeriv a (c + 1) G X z u (Fin.snoc v w) =
      mixedDeriv a c (fun p => fderiv ℝ G p (0, w)) X z u v := by
  have hG' : ContDiff ℝ ∞' (fun p => fderiv ℝ G p (0, w)) := contDiff_fderiv_apply hG _
  unfold mixedDeriv
  rw [iteratedFDeriv_apply_ml (contDiff_inner hG (c + 1) z) a X u (Fin.snoc v w),
    iteratedFDeriv_apply_ml (contDiff_inner hG' c z) a X u v]
  congr 2
  funext X'
  rw [iteratedFDeriv_succ_apply_right]
  simp only [Fin.init_snoc, Fin.snoc_last]
  have hgd : ContDiff ℝ ∞' (fun y : Euc d => G (X', y)) := hG.comp (contDiff_const.prodMk contDiff_id)
  have h2 := (ContinuousLinearMap.apply ℝ ℝ w).iteratedFDeriv_comp_left
    (f := fun y : Euc d => fderiv ℝ (fun y' : Euc d => G (X', y')) y) (x := z)
    ((hgd.fderiv_right (m := ∞') (by simp)).contDiffAt) (i := c) (by exact_mod_cast le_top)
  have h3 : ((ContinuousLinearMap.apply ℝ ℝ w) ∘ fun y : Euc d => fderiv ℝ (fun y' : Euc d => G (X', y')) y) =
      fun y => fderiv ℝ G (X', y) (0, w) := by
    funext y
    exact fderiv_inner_apply hG X' y w
  rw [h3] at h2
  rw [h2]
  rfl

theorem norm_mixedDeriv_zero (G : Euc d × Euc d → ℝ) (a : ℕ) (X z : Euc d) :
    ‖mixedDeriv a 0 G X z‖ = ‖iteratedFDeriv ℝ a (fun X' => G (X', z)) X‖ := by
  unfold mixedDeriv
  have h : (fun X' : Euc d => iteratedFDeriv ℝ 0 (fun z' => G (X', z')) z) =
      (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm ∘ (fun X' => G (X', z)) := by
    funext X'
    simp [iteratedFDeriv_zero_eq_comp]
  rw [h]
  exact LinearIsometryEquiv.norm_iteratedFDeriv_comp_left _ _ _ _

theorem norm_prodMk_zero_le (w : Euc d) (hw : ‖w‖ ≤ 1) : ‖((0 : Euc d), w)‖ ≤ 1 := by
  simp [Prod.norm_def, hw]

theorem norm_iteratedFDeriv_slice_fst_le {G : Euc d × Euc d → ℝ} (hG : ContDiff ℝ ∞' G) (a : ℕ)
    (X z : Euc d) :
    ‖iteratedFDeriv ℝ a (fun X' => G (X', z)) X‖ ≤ ‖iteratedFDeriv ℝ a G (X, z)‖ := by
  have hfun : (fun X' : Euc d => G (X', z)) =
      (fun p : Euc d × Euc d => G (p + (0, z))) ∘ (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) := by
    funext X'; simp
  have hcd : ContDiff ℝ ∞' (fun p : Euc d × Euc d => G (p + (0, z))) :=
    hG.comp (contDiff_id.add contDiff_const)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ hcd X (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ‖ContinuousLinearMap.inl ℝ (Euc d) (Euc d)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp [Prod.norm_def]
  have h2 : ∏ _j : Fin a, ‖ContinuousLinearMap.inl ℝ (Euc d) (Euc d)‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) h1
  have h3 : (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) X + (0, z) = (X, z) := by simp
  rw [ContinuousLinearMap.inl_apply] at *
  simp only [Prod.mk_add_mk, add_zero, zero_add]
  calc _ ≤ ‖iteratedFDeriv ℝ a G (X, z)‖ * 1 := by
        gcongr
    _ = _ := mul_one _

theorem norm_iteratedFDeriv_fderiv_apply_le {G : Euc d × Euc d → ℝ} (hG : ContDiff ℝ ∞' G)
    (w : Euc d × Euc d) (n : ℕ) (p : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ n (fun q => fderiv ℝ G q w) p‖ ≤ ‖w‖ * ‖iteratedFDeriv ℝ (n + 1) G p‖ := by
  have hc : ContDiffAt ℝ ∞' (fderiv ℝ G) p := (hG.fderiv_right (m := ∞') (by simp)).contDiffAt
  have h := norm_iteratedFDeriv_clm_apply_const (c := w) (n := n) hc (by exact_mod_cast le_top)
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h

theorem norm_mixedDeriv_le {G : Euc d × Euc d → ℝ} :
    ∀ (c : ℕ) (hG : ContDiff ℝ ∞' G) (a : ℕ) (X z : Euc d),
      ‖mixedDeriv a c G X z‖ ≤ ‖iteratedFDeriv ℝ (a + c) G (X, z)‖ := by
  intro c
  induction c generalizing G with
  | zero =>
    intro hG a X z
    rw [norm_mixedDeriv_zero]
    exact norm_iteratedFDeriv_slice_fst_le hG a X z
  | succ c ih =>
    intro hG a X z
    refine norm_mixed_le_of_unit _ (norm_nonneg _) fun u v hu hv => ?_
    set w := v (Fin.last c) with hw
    have hv' : v = Fin.snoc (Fin.init v) w := (Fin.snoc_init_self v).symm
    have hG' : ContDiff ℝ ∞' (fun p => fderiv ℝ G p (0, w)) := contDiff_fderiv_apply hG _
    have hw1 : ‖w‖ ≤ 1 := hv (Fin.last c)
    rw [hv', mixedDeriv_snoc_apply hG]
    have hinit : ∀ j, ‖Fin.init v j‖ ≤ 1 := fun j => hv _
    refine (abs_mixed_le _ u _ hu hinit).trans ?_
    refine (ih hG' a X z).trans ?_
    refine (norm_iteratedFDeriv_fderiv_apply_le hG (0, w) (a + c) (X, z)).trans ?_
    have := norm_prodMk_zero_le w hw1
    calc ‖((0 : Euc d), w)‖ * ‖iteratedFDeriv ℝ (a + c + 1) G (X, z)‖
        ≤ 1 * ‖iteratedFDeriv ℝ (a + c + 1) G (X, z)‖ := by gcongr
      _ = ‖iteratedFDeriv ℝ (a + (c + 1)) G (X, z)‖ := by rw [one_mul, add_assoc]

theorem px2_mixedDeriv_add {G₁ G₂ : Euc d × Euc d → ℝ} (h₁ : ContDiff ℝ ∞' G₁) (h₂ : ContDiff ℝ ∞' G₂)
    (a c : ℕ) (X z : Euc d) :
    mixedDeriv a c (fun p => G₁ p + G₂ p) X z = mixedDeriv a c G₁ X z + mixedDeriv a c G₂ X z := by
  unfold mixedDeriv
  have hin : ∀ X' : Euc d, iteratedFDeriv ℝ c (fun z' => G₁ (X', z') + G₂ (X', z')) z =
      iteratedFDeriv ℝ c (fun z' => G₁ (X', z')) z + iteratedFDeriv ℝ c (fun z' => G₂ (X', z')) z := by
    intro X'
    have e1 : ContDiffAt ℝ ∞' (fun z' : Euc d => G₁ (X', z')) z :=
      (h₁.comp (contDiff_const.prodMk contDiff_id)).contDiffAt
    have e2 : ContDiffAt ℝ ∞' (fun z' : Euc d => G₂ (X', z')) z :=
      (h₂.comp (contDiff_const.prodMk contDiff_id)).contDiffAt
    exact iteratedFDeriv_add_apply (e1.of_le (by exact_mod_cast le_top))
      (e2.of_le (by exact_mod_cast le_top))
  have hfun : (fun X' : Euc d => iteratedFDeriv ℝ c (fun z' => G₁ (X', z') + G₂ (X', z')) z) =
      (fun X' : Euc d => iteratedFDeriv ℝ c (fun z' => G₁ (X', z')) z) +
        (fun X' : Euc d => iteratedFDeriv ℝ c (fun z' => G₂ (X', z')) z) := by
    funext X'; exact hin X'
  rw [hfun]
  exact iteratedFDeriv_add_apply ((contDiff_inner h₁ c z).contDiffAt.of_le (by exact_mod_cast le_top))
    ((contDiff_inner h₂ c z).contDiffAt.of_le (by exact_mod_cast le_top))

theorem norm_mixedDeriv_succ_fderiv_le {G : Euc d × Euc d → ℝ} (hG : ContDiff ℝ ∞' G) (a c : ℕ)
    (X z : Euc d) {w : Euc d} (hw : ‖w‖ ≤ 1) :
    ‖mixedDeriv a c (fun p => fderiv ℝ G p (0, w)) X z‖ ≤ ‖mixedDeriv a (c + 1) G X z‖ := by
  refine norm_mixed_le_of_unit _ (norm_nonneg (mixedDeriv a (c + 1) G X z)) fun u v hu hv => ?_
  rw [← mixedDeriv_snoc_apply hG]
  refine abs_mixed_le _ u _ hu fun j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa using hw
  · simpa using hv i

theorem norm_iteratedFDeriv_fderiv_apply_le' {κ : Euc d → ℝ} (hκ : ContDiff ℝ ∞' κ) {w : Euc d}
    (hw : ‖w‖ ≤ 1) (n : ℕ) (z : Euc d) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ κ y w) z‖ ≤ ‖iteratedFDeriv ℝ (n + 1) κ z‖ := by
  have hc : ContDiffAt ℝ ∞' (fderiv ℝ κ) z := (hκ.fderiv_right (m := ∞') (by simp)).contDiffAt
  have h := norm_iteratedFDeriv_clm_apply_const (c := w) (n := n) hc (by exact_mod_cast le_top)
  rw [norm_iteratedFDeriv_fderiv] at h
  calc _ ≤ ‖w‖ * ‖iteratedFDeriv ℝ (n + 1) κ z‖ := h
    _ ≤ 1 * ‖iteratedFDeriv ℝ (n + 1) κ z‖ := by gcongr
    _ = _ := one_mul _

theorem fderiv_mul_pureZ {Ā : Euc d × Euc d → ℝ} {κ : Euc d → ℝ} (hĀ : ContDiff ℝ ∞' Ā)
    (hκ : ContDiff ℝ ∞' κ) (w : Euc d) :
    (fun p : Euc d × Euc d => fderiv ℝ (fun q : Euc d × Euc d => Ā q * κ q.2) p (0, w)) =
      fun p => (fderiv ℝ Ā p (0, w)) * κ p.2 + Ā p * (fderiv ℝ κ p.2 w) := by
  funext p
  have h1 : HasFDerivAt Ā (fderiv ℝ Ā p) p := (hĀ.differentiable (by simp) p).hasFDerivAt
  have h2 : HasFDerivAt (fun q : Euc d × Euc d => κ q.2)
      ((fderiv ℝ κ p.2).comp (ContinuousLinearMap.snd ℝ (Euc d) (Euc d))) p :=
    ((hκ.differentiable (by simp) p.2).hasFDerivAt).comp p (hasFDerivAt_snd)
  have h3 : HasFDerivAt (fun q : Euc d × Euc d => Ā q * κ q.2)
      (Ā p • ((fderiv ℝ κ p.2).comp (ContinuousLinearMap.snd ℝ (Euc d) (Euc d))) + κ p.2 • fderiv ℝ Ā p) p :=
    h1.mul h2
  rw [h3.fderiv]
  simp
  ring

theorem norm_mixedDeriv_mul_pureZ : ∀ (c : ℕ) (Ā : Euc d × Euc d → ℝ) (κ : Euc d → ℝ),
    ContDiff ℝ ∞' Ā → ContDiff ℝ ∞' κ → ∀ (a : ℕ) (X z : Euc d),
      ‖mixedDeriv a c (fun p => Ā p * κ p.2) X z‖ ≤
        ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ) * ‖mixedDeriv a i Ā X z‖ *
          ‖iteratedFDeriv ℝ (c - i) κ z‖ := by
  intro c
  induction c with
  | zero =>
    intro Ā κ hĀ hκ a X z
    have hrhs : ∑ i ∈ Finset.range (0 + 1), ((0 : ℕ).choose i : ℝ) * ‖mixedDeriv a i Ā X z‖ *
        ‖iteratedFDeriv ℝ (0 - i) κ z‖ = ‖mixedDeriv a 0 Ā X z‖ * ‖κ z‖ := by
      simp [norm_iteratedFDeriv_zero]
    rw [hrhs, norm_mixedDeriv_zero, norm_mixedDeriv_zero]
    have hfun : (fun X' : Euc d => Ā (X', z) * κ z) = fun X' => κ z • Ā (X', z) := by
      funext X'; simp [mul_comm]
    have hcd : ContDiffAt ℝ ∞' (fun X' : Euc d => Ā (X', z)) X :=
      (hĀ.comp (contDiff_id.prodMk contDiff_const)).contDiffAt
    simp only [hfun]
    rw [iteratedFDeriv_const_smul_apply' (hcd.of_le (by exact_mod_cast le_top)), norm_smul]
    rw [mul_comm]
  | succ c ih =>
    intro Ā κ hĀ hκ a X z
    set m : ℕ → ℝ := fun i => ‖mixedDeriv a i Ā X z‖ with hm
    set k : ℕ → ℝ := fun j => ‖iteratedFDeriv ℝ j κ z‖ with hk
    have hm0 : ∀ i, 0 ≤ m i := fun i => norm_nonneg (mixedDeriv a i Ā X z)
    have hk0 : ∀ j, 0 ≤ k j := fun j => norm_nonneg _
    set M : ℝ := ∑ i ∈ Finset.range (c + 1 + 1), ((c + 1).choose i : ℝ) * m i * k (c + 1 - i) with hM
    have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hm0 _)) (hk0 _)
    refine norm_mixed_le_of_unit _ hM0 fun u v hu hv => ?_
    set w := v (Fin.last c) with hw
    have hv' : v = Fin.snoc (Fin.init v) w := (Fin.snoc_init_self v).symm
    have hw1 : ‖w‖ ≤ 1 := hv (Fin.last c)
    have hinit : ∀ j, ‖Fin.init v j‖ ≤ 1 := fun j => hv _
    have hG : ContDiff ℝ ∞' (fun p : Euc d × Euc d => Ā p * κ p.2) :=
      hĀ.mul (hκ.comp contDiff_snd)
    rw [hv', mixedDeriv_snoc_apply hG, fderiv_mul_pureZ hĀ hκ w]
    refine (abs_mixed_le _ u _ hu hinit).trans ?_
    have hA' : ContDiff ℝ ∞' (fun p : Euc d × Euc d => fderiv ℝ Ā p (0, w)) :=
      contDiff_fderiv_apply hĀ _
    have hκ' : ContDiff ℝ ∞' (fun y : Euc d => fderiv ℝ κ y w) := contDiff_fderiv_apply' hκ w
    have hP1 : ContDiff ℝ ∞' (fun p : Euc d × Euc d => (fderiv ℝ Ā p (0, w)) * κ p.2) :=
      hA'.mul (hκ.comp contDiff_snd)
    have hP2 : ContDiff ℝ ∞' (fun p : Euc d × Euc d => Ā p * (fderiv ℝ κ p.2 w)) :=
      hĀ.mul (hκ'.comp contDiff_snd)
    rw [px2_mixedDeriv_add hP1 hP2]
    have hna := norm_add_le
      (mixedDeriv a c (fun p : Euc d × Euc d => (fderiv ℝ Ā p (0, w)) * κ p.2) X z)
      (mixedDeriv a c (fun p : Euc d × Euc d => Ā p * (fderiv ℝ κ p.2 w)) X z)
    refine hna.trans ?_
    have I1 := ih (fun p => fderiv ℝ Ā p (0, w)) κ hA' hκ a X z
    have I2 := ih Ā (fun y => fderiv ℝ κ y w) hĀ hκ' a X z
    have J1 : ∀ i, ‖mixedDeriv a i (fun p => fderiv ℝ Ā p (0, w)) X z‖ ≤ m (i + 1) := fun i =>
      norm_mixedDeriv_succ_fderiv_le hĀ a i X z hw1
    have J2 : ∀ j, ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ κ y w) z‖ ≤ k (j + 1) := fun j =>
      norm_iteratedFDeriv_fderiv_apply_le' hκ hw1 j z
    have S1 : ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ) *
        ‖mixedDeriv a i (fun p => fderiv ℝ Ā p (0, w)) X z‖ * ‖iteratedFDeriv ℝ (c - i) κ z‖ ≤
        ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ) * (m (i + 1) * k (c - i)) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (J1 i) le_rfl (hk0 _) (hm0 _)) (Nat.cast_nonneg _)
    have S2 : ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ) * ‖mixedDeriv a i Ā X z‖ *
        ‖iteratedFDeriv ℝ (c - i) (fun y => fderiv ℝ κ y w) z‖ ≤
        ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ) * (m i * k (c - i + 1)) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul le_rfl (J2 _) (norm_nonneg _) (hm0 _)) (Nat.cast_nonneg _)
    have hPascal := Finset.sum_choose_succ_mul (fun i j => m i * k j) c
    have hM' : M = ∑ i ∈ Finset.range (c + 1 + 1), ((c + 1).choose i : ℝ) * (m i * k (c + 1 - i)) := by
      rw [hM]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    have e2 : ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ) * (m i * k (c - i + 1)) =
        ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ) * (m i * k (c + 1 - i)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have : c - i + 1 = c + 1 - i := by have := Finset.mem_range.mp hi; omega
      rw [this]
    calc _ ≤ _ := add_le_add I1 I2
      _ ≤ _ := add_le_add S1 S2
      _ = M := by
          rw [hM', hPascal, e2]
          ring

end HRS.Parx

end
