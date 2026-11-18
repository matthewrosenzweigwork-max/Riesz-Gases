import HRS.MC.S7PIS2Cb
import HRS.Sections.Q17Aux7
import HRS.Main.Headline

/-!
# Packet E213O1: window restriction `winRestr`, its `C_b^5` composition bound, and `tensorPow'` (items B1, B2, D1)

* `winRestr a ha : 𝒳_{m,a+T} →L 𝒳_{m,T}`, `(winRestr a ha w)(t) = w(a+t)`, `‖winRestr a ha‖ ≤ 1`.
* the window objects of Section 7 / `Main` are `winRestr` of the corresponding horizon `a+T` objects, whenever the
  underlying process is continuous on `[0,a+T]` (`toPath`, `procWin`, `zetaWin`, `windowPath`, `windowZeta`, `pathOf`).
* `MemCb 5 (Φ ∘ winRestr a)` and `cbNorm 5 (Φ ∘ winRestr a) ≤ cbNorm 5 Φ`.
* `tensorPow' j P : TensorDual B j →L TensorDual B' j` for `P : B →L B'` (direction: a tensor on the BIG space
  `B = 𝒳_{a+T}` is sent to a tensor on the small space `B' = 𝒳_T`; `(P^{⊗j} u)(M) = u(M ∘ (P,…,P))`), with
  `‖tensorPow' j P u‖ ≤ ‖P‖^j ‖u‖`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7

namespace HRS.MC.E213O

set_option maxSynthPendingDepth 3

variable {d : ℕ}

/-! ### B1: the window restriction -/

theorem e213o_ext {m T : ℝ} {w v : PathSpace d m T} (h : ∀ t, w.at' t = v.at' t) : w = v :=
  ContinuousMap.ext h


/-- The point `a + t ∈ [0, a+T]` for `t ∈ [0,T]`, `a ≥ 0`. -/
def e213o_shift {a T : ℝ} (ha : 0 ≤ a) (t : Set.Icc (0 : ℝ) T) : Set.Icc (0 : ℝ) (a + T) :=
  ⟨a + t.1, by linarith [t.2.1], by linarith [t.2.2]⟩

theorem e213o_continuous_shift {a T : ℝ} (ha : 0 ≤ a) : Continuous (e213o_shift (a := a) (T := T) ha) := by
  unfold e213o_shift
  fun_prop

/-- Underlying linear map of `winRestr`. -/
def e213o_winRestrLM {m T : ℝ} (a : ℝ) (ha : 0 ≤ a) :
    PathSpace d m (a + T) →ₗ[ℝ] PathSpace d m T where
  toFun w := (show C(Set.Icc (0 : ℝ) (a + T), NegSobolev d m) from w).comp
    ⟨e213o_shift ha, e213o_continuous_shift ha⟩
  map_add' w w' := e213o_ext (fun t => rfl)
  map_smul' c w := e213o_ext (fun t => rfl)

/-- **(B1)** The window restriction `𝒳_{m,a+T} →L 𝒳_{m,T}`, `w ↦ (t ↦ w(a+t))`. -/
def winRestr {m T : ℝ} (a : ℝ) (ha : 0 ≤ a) : PathSpace d m (a + T) →L[ℝ] PathSpace d m T :=
  LinearMap.mkContinuous (e213o_winRestrLM a ha) 1 (fun w => by
    rw [one_mul]
    refine ContinuousMap.norm_le _ (norm_nonneg _) |>.2 (fun t => ?_)
    exact ContinuousMap.norm_coe_le_norm
      (show C(Set.Icc (0 : ℝ) (a + T), NegSobolev d m) from w) (e213o_shift ha t))

theorem winRestr_at' {m T : ℝ} (a : ℝ) (ha : 0 ≤ a) (w : PathSpace d m (a + T))
    (t : Set.Icc (0 : ℝ) T) : (winRestr a ha w).at' t = w.at' (e213o_shift ha t) := rfl

theorem winRestr_norm_le {m T : ℝ} (a : ℝ) (ha : 0 ≤ a) : ‖(winRestr (d := d) (m := m) (T := T) a ha)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- `pathAt (winRestr a w) t = pathAt w (a + t)` for `t ∈ [0,T]`. -/
theorem winRestr_pathAt {m T : ℝ} (a : ℝ) (ha : 0 ≤ a) (w : PathSpace d m (a + T)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) : pathAt (winRestr a ha w) t = pathAt w (a + t) := by
  have h2 : a + t ∈ Set.Icc (0 : ℝ) (a + T) := (e213o_shift ha ⟨t, ht⟩).2
  unfold pathAt
  rw [dif_pos ht, dif_pos h2]
  rfl

/-- The restriction is the identity on window shifts of continuous paths. -/
theorem winRestr_eq_of_forall {m T : ℝ} (a : ℝ) (ha : 0 ≤ a) (w : PathSpace d m (a + T))
    (v : PathSpace d m T) (h : ∀ t ∈ Set.Icc (0 : ℝ) T, pathAt v t = pathAt w (a + t)) :
    winRestr a ha w = v := by
  refine e213o_ext (fun t => ?_)
  have h3 : pathAt (winRestr a ha w) t.1 = pathAt v t.1 := (winRestr_pathAt a ha w t.2).trans (h t.1 t.2).symm
  unfold pathAt at h3
  rw [dif_pos t.2, dif_pos t.2] at h3
  exact h3

theorem e213o_pathOf_at' {m T : ℝ} (g : ℝ → NegSobolev d m) (hc : Continuous fun t : Set.Icc (0 : ℝ) T => g t)
    (s : Set.Icc (0 : ℝ) T) : (pathOf m T g).at' s = g s := by
  have hw : pathOf m T g = (⟨fun t => g t, hc⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
    unfold pathOf
    exact dif_pos hc
  rw [hw]
  rfl

theorem e213o_toPath_at' {Ω : Type*} {m T : ℝ} (Y : ℝ → Ω → NegSobolev d m) (ω : Ω)
    (hc : Continuous fun t : Set.Icc (0 : ℝ) T => Y t ω) (s : Set.Icc (0 : ℝ) T) :
    (toPath m T Y ω).at' s = Y s ω := by
  have hw : toPath m T Y ω = (⟨fun t => Y t ω, hc⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
    unfold toPath
    exact dif_pos hc
  rw [hw]
  rfl

/-- A path `g : ℝ → E_m` continuous on `[0,a+T]`: the window `pathOf m T (g(a+·))` is the restriction of
`pathOf m (a+T) g`. -/
theorem winRestr_pathOf {m T : ℝ} (a : ℝ) (ha : 0 ≤ a) (g : ℝ → NegSobolev d m)
    (hg : ContinuousOn g (Set.Icc 0 (a + T))) :
    pathOf m T (fun t => g (a + t)) = winRestr a ha (pathOf m (a + T) g) := by
  have hc : Continuous fun t : Set.Icc (0 : ℝ) (a + T) => g t := continuousOn_iff_continuous_domRestrict.1 hg
  have hc' : Continuous fun t : Set.Icc (0 : ℝ) T => g (a + t) :=
    hc.comp (e213o_continuous_shift (a := a) (T := T) ha)
  refine e213o_ext (fun t => ?_)
  rw [winRestr_at', e213o_pathOf_at' _ hc' t, e213o_pathOf_at' _ hc]
  rfl

/-- Same for `toPath` (the window of a process, `0` off the continuity set). -/
theorem winRestr_toPath {Ω : Type*} {m T : ℝ} (a : ℝ) (ha : 0 ≤ a) (Y : ℝ → Ω → NegSobolev d m) (ω : Ω)
    (hY : ContinuousOn (fun t => Y t ω) (Set.Icc 0 (a + T))) :
    toPath m T (fun t ω => Y (a + t) ω) ω = winRestr a ha (toPath m (a + T) Y ω) := by
  have hc : Continuous fun t : Set.Icc (0 : ℝ) (a + T) => Y t ω := continuousOn_iff_continuous_domRestrict.1 hY
  have hc' : Continuous fun t : Set.Icc (0 : ℝ) T => Y (a + t) ω :=
    hc.comp (e213o_continuous_shift (a := a) (T := T) ha)
  refine e213o_ext (fun t => ?_)
  rw [winRestr_at', e213o_toPath_at' _ ω hc' t, e213o_toPath_at' _ ω hc]
  rfl

/-- `procWin` is the restriction of the horizon-`a+T` window at `0`. -/
theorem winRestr_procWin {Ω : Type} {m T : ℝ} (a : ℝ) (ha : 0 ≤ a) (η : ℝ → Ω → NegSobolev d m) (ω : Ω)
    (hη : ContinuousOn (fun t => η t ω) (Set.Icc 0 (a + T))) :
    HRS.Sec7.procWin m T a η ω = winRestr a ha (HRS.Sec7.procWin m (a + T) 0 η ω) := by
  have h0 : (fun t ω => η (0 + t) ω) = η := by funext t ω; rw [zero_add]
  unfold HRS.Sec7.procWin
  rw [h0]
  exact winRestr_toPath (T := T) a ha η ω hη

/-- `zetaWin` is the restriction of the horizon-`a+T` window at `0`. -/
theorem winRestr_zetaWin {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (m T a : ℝ) (ha : 0 ≤ a) (P : Measure Ω)
    (X : NNReal → Ω → Config d N) (ω : Ω)
    (hζ : ContinuousOn (fun t => HRS.Sec7.zetaAt m P X t ω) (Set.Icc 0 (a + T))) :
    HRS.Sec7.zetaWin m T a P X ω = winRestr a ha (HRS.Sec7.zetaWin m (a + T) 0 P X ω) := by
  have h0 : (fun t ω => HRS.Sec7.zetaAt m P X (0 + t) ω) = (fun t ω => HRS.Sec7.zetaAt m P X t ω) := by
    funext t ω; rw [zero_add]
  unfold HRS.Sec7.zetaWin
  rw [h0]
  exact winRestr_toPath (T := T) a ha (fun t ω => HRS.Sec7.zetaAt m P X t ω) ω hζ

/-- `Main.windowPath` is the restriction of the horizon-`a+T` window at `0`. -/
theorem winRestr_windowPath {Ω : Type*} {m T : ℝ} (a : ℝ) (ha : 0 ≤ a) (Y : ℝ → Ω → NegSobolev d m) (ω : Ω)
    (hY : ContinuousOn (fun t => Y t ω) (Set.Icc 0 (a + T))) :
    Main.windowPath m T a Y ω = winRestr a ha (Main.windowPath m (a + T) 0 Y ω) := by
  have h0 : (fun t ω => Y (0 + t) ω) = Y := by funext t ω; rw [zero_add]
  show toPath m T (fun t ω => Y (a + t) ω) ω = winRestr a ha (toPath m (a + T) (fun t ω => Y (0 + t) ω) ω)
  rw [h0]
  exact winRestr_toPath (T := T) a ha Y ω hY

/-- `Main.windowZeta` is the restriction of the horizon-`a+T` window at `0`. -/
theorem winRestr_windowZeta {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (m T a : ℝ) (ha : 0 ≤ a) (P : Measure Ω)
    (X : NNReal → Ω → Config d N) (ω : Ω)
    (hζ : ContinuousOn (fun t : ℝ => zetaE m (P.map (X (Real.toNNReal t))) (X (Real.toNNReal t) ω))
      (Set.Icc 0 (a + T))) :
    Main.windowZeta m T a P X ω = winRestr a ha (Main.windowZeta m (a + T) 0 P X ω) := by
  have hc : Continuous fun t : Set.Icc (0 : ℝ) (a + T) =>
      zetaE m (P.map (X (Real.toNNReal t))) (X (Real.toNNReal t) ω) :=
    continuousOn_iff_continuous_domRestrict.1 hζ
  have hc' : Continuous fun t : Set.Icc (0 : ℝ) T =>
      zetaE m (P.map (X (Real.toNNReal (a + t)))) (X (Real.toNNReal (a + t)) ω) :=
    hζ.comp_continuous (f := fun t : Set.Icc (0 : ℝ) T => a + (t : ℝ)) (by fun_prop)
      (fun t => (e213o_shift ha t).2)
  have hc0 : Continuous fun t : Set.Icc (0 : ℝ) (a + T) =>
      zetaE m (P.map (X (Real.toNNReal (0 + t)))) (X (Real.toNNReal (0 + t)) ω) := by
    simpa only [zero_add] using hc
  have e1 : Main.windowZeta m T a P X ω = (⟨_, hc'⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
    unfold Main.windowZeta
    exact dif_pos hc'
  have e2 : Main.windowZeta m (a + T) 0 P X ω = (⟨_, hc0⟩ : C(Set.Icc (0 : ℝ) (a + T), NegSobolev d m)) := by
    unfold Main.windowZeta
    exact dif_pos hc0
  refine e213o_ext (fun t => ?_)
  rw [winRestr_at']
  have a1 : (Main.windowZeta m T a P X ω).at' t =
      zetaE m (P.map (X (Real.toNNReal (a + t)))) (X (Real.toNNReal (a + t)) ω) := by
    rw [e1]; rfl
  have a2 : (Main.windowZeta m (a + T) 0 P X ω).at' (e213o_shift ha t) =
      zetaE m (P.map (X (Real.toNNReal (0 + (a + t))))) (X (Real.toNNReal (0 + (a + t))) ω) := by
    rw [e2]; rfl
  rw [a1, a2, zero_add]

/-! ### B2: composition with `Φ` -/

/-- **(B2)** `MemCb 5 (Φ ∘ winRestr a)` and `cbNorm 5 (Φ ∘ winRestr a) ≤ cbNorm 5 Φ`. -/
theorem winRestr_memCb {m T : ℝ} (a : ℝ) (ha : 0 ≤ a) {Φ : PathSpace d m T → ℝ} (hΦ : MemCb 5 Φ) :
    MemCb 5 (fun w => Φ (winRestr a ha w)) ∧ cbNorm 5 (fun w => Φ (winRestr a ha w)) ≤ cbNorm 5 Φ := by
  obtain ⟨h1, -, h3⟩ := HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof (winRestr a ha) hΦ
  exact ⟨h1, h3 (winRestr_norm_le a ha)⟩

/-! ### D1: tensor power between different Banach spaces -/

section TensorPow

open HRS HRS.Sec7

variable {B B' B'' : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup B']
  [NormedSpace ℝ B'] [NormedAddCommGroup B''] [NormedSpace ℝ B'']

/-- **(D1)** The action `P^{⊗j}` of a bounded operator `P : B →L B'` between two different Banach spaces on the duals of
the bounded `j`-linear forms: `(P^{⊗j} u)(M) = u(M ∘ (P,…,P))`, sending a tensor on `B` to a tensor on `B'`. -/
def tensorPow' (j : ℕ) (P : B →L[ℝ] B') : TensorDual B j →L[ℝ] TensorDual B' j :=
  ContinuousLinearMap.precomp ℝ (ContinuousMultilinearMap.compContinuousLinearMapL (F := ℝ) (fun _ : Fin j => P))

theorem tensorPow'_apply (j : ℕ) (P : B →L[ℝ] B') (u : TensorDual B j) (M : B' [×j]→L[ℝ] ℝ) :
    tensorPow' j P u M = u (M.compContinuousLinearMap fun _ => P) := rfl

/-- On one space `tensorPow'` is `tensorPow`. -/
theorem tensorPow'_eq_tensorPow (j : ℕ) (P : B →L[ℝ] B) : tensorPow' j P = tensorPow j P := rfl

/-- **(D1)** `‖P^{⊗j} u‖ ≤ ‖P‖^j ‖u‖`. -/
theorem tensorPow'_norm_le (j : ℕ) (P : B →L[ℝ] B') (u : TensorDual B j) :
    ‖tensorPow' j P u‖ ≤ ‖P‖ ^ j * ‖u‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun M => ?_)
  rw [tensorPow'_apply]
  calc ‖u (M.compContinuousLinearMap fun _ => P)‖
      ≤ ‖u‖ * ‖M.compContinuousLinearMap fun _ => P‖ := u.le_opNorm _
    _ ≤ ‖u‖ * (‖M‖ * ∏ _i : Fin j, ‖P‖) :=
        mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) (norm_nonneg _)
    _ = ‖P‖ ^ j * ‖u‖ * ‖M‖ := by simp; ring

/-- Operator-norm form: `‖tensorPow' j P‖ ≤ ‖P‖^j`. -/
theorem tensorPow'_opNorm_le (j : ℕ) (P : B →L[ℝ] B') : ‖tensorPow' j P‖ ≤ ‖P‖ ^ j :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun u => tensorPow'_norm_le j P u)

theorem tensorPow'_opNorm_le_one (j : ℕ) (P : B →L[ℝ] B') (hP : ‖P‖ ≤ 1) : ‖tensorPow' j P‖ ≤ 1 :=
  (tensorPow'_opNorm_le j P).trans (pow_le_one₀ (norm_nonneg _) hP)

/-- On elementary tensors. -/
theorem tensorPow'_elem (j : ℕ) (P : B →L[ℝ] B') (v : Fin j → B) :
    tensorPow' j P (elemTensor v) = elemTensor (fun i => P (v i)) := rfl

/-- Functoriality. -/
theorem tensorPow'_comp (j : ℕ) (P : B →L[ℝ] B') (Q : B' →L[ℝ] B'') (u : TensorDual B j) :
    tensorPow' j (Q.comp P) u = tensorPow' j Q (tensorPow' j P u) := rfl

end TensorPow

/-- The window tensor power `(winRestr a)^{⊗j}` sends a tensor on `𝒳_{m,a+T}` to a tensor on `𝒳_{m,T}`, norm `≤ ‖u‖`. -/
theorem winRestr_tensorPow'_norm_le {m T : ℝ} (a : ℝ) (ha : 0 ≤ a) (j : ℕ)
    (u : TensorDual (PathSpace d m (a + T)) j) : ‖tensorPow' j (winRestr a ha) u‖ ≤ ‖u‖ := by
  refine (tensorPow'_norm_le j _ u).trans ?_
  calc _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) (winRestr_norm_le a ha)) (norm_nonneg _)
    _ = ‖u‖ := one_mul _

end HRS.MC.E213O

end
