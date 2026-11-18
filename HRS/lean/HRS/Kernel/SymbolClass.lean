import HRS.PDE.Toolbox.Kernel

/-!
# Symbol classes with uniform derivative bounds (packet Q39, Lemma C.2 infrastructure)

A function `G : V → E` belongs to the class `Symb τ B` when
`‖D^m G(ξ)‖ ≤ B m (1 + ‖ξ‖)^{-τ-m}` for all `m` and `ξ`.  We prove closure under products
(Leibniz) and the gain of one power of decay under a finite difference `ξ ↦ G(ξ - v) - G(ξ)` with
`‖v‖ ≤ 1`; the constants are explicit functions of `B` only, so uniform families stay uniform.
-/

noncomputable section

open Filter Topology
open scoped ContDiff BigOperators

namespace HRS
section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- the symbol class: `‖D^m G(ξ)‖ ≤ B m (1+‖ξ‖)^{-τ-m}` -/
def Symb (τ : ℝ) (B : ℕ → ℝ) (G : V → E) : Prop :=
  ∀ (m : ℕ) (ξ : V), ‖iteratedFDeriv ℝ m G ξ‖ ≤ B m * (1 + ‖ξ‖) ^ (-τ - (m : ℝ))

theorem Symb.B_nonneg {τ : ℝ} {B : ℕ → ℝ} {G : V → E} (h : Symb τ B G) (m : ℕ) : 0 ≤ B m := by
  have h0 := h m 0
  have hp : 0 < (1 + ‖(0 : V)‖) ^ (-τ - (m : ℝ)) := by
    apply Real.rpow_pos_of_pos; simp
  have := (norm_nonneg _).trans h0
  exact nonneg_of_mul_nonneg_left this hp

theorem Symb.mono_B {τ : ℝ} {B B' : ℕ → ℝ} {G : V → E} (h : Symb τ B G) (hB : ∀ m, B m ≤ B' m) :
    Symb τ B' G := fun m ξ =>
  (h m ξ).trans (mul_le_mul_of_nonneg_right (hB m) (Real.rpow_nonneg (by positivity) _))

/-- Peetre-type comparison of weights. -/
theorem peetre (a : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : |x - y| ≤ 1) :
    (1 + x) ^ (-a) ≤ 2 ^ |a| * (1 + y) ^ (-a) := by
  have h1 : 0 < 1 + x := by linarith
  have h2 : 0 < 1 + y := by linarith
  have hx1 : x ≤ y + 1 := by have := (abs_le.mp h).2; linarith
  have hy1 : y ≤ x + 1 := by have := (abs_le.mp h).1; linarith
  have hr1 : (1 + x) / (1 + y) ≤ 2 := by rw [div_le_iff₀ h2]; linarith
  have hr2 : 1 / 2 ≤ (1 + x) / (1 + y) := by rw [le_div_iff₀ h2]; linarith
  have hr0 : 0 < (1 + x) / (1 + y) := by positivity
  have hsplit : (1 + x) ^ (-a) = ((1 + x) / (1 + y)) ^ (-a) * (1 + y) ^ (-a) := by
    rw [← Real.mul_rpow hr0.le h2.le, div_mul_cancel₀ _ h2.ne']
  rw [hsplit]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg h2.le _)
  rcases le_total 0 (-a) with ha | ha
  · calc ((1 + x) / (1 + y)) ^ (-a) ≤ 2 ^ (-a) := Real.rpow_le_rpow hr0.le hr1 ha
      _ ≤ 2 ^ |a| := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        exact neg_le_abs a
  · have h3 : ((1 + x) / (1 + y)) ^ (-a) ≤ (1 / 2) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hr2 ha
    calc ((1 + x) / (1 + y)) ^ (-a) ≤ (1 / 2) ^ (-a) := h3
      _ = 2 ^ a := by
        rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg]
      _ ≤ 2 ^ |a| := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        exact le_abs_self a

/-- Leibniz closure under products (real-valued factors). -/
theorem Symb.mul {τ₁ τ₂ : ℝ} {B₁ B₂ : ℕ → ℝ} {A H : V → ℝ} (hA : ContDiff ℝ ∞ A)
    (hH : ContDiff ℝ ∞ H) (hSA : Symb τ₁ B₁ A) (hSH : Symb τ₂ B₂ H) :
    Symb (τ₁ + τ₂) (fun m => ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * B₁ i * B₂ (m - i))
      (fun ξ => A ξ * H ξ) := by
  intro m ξ
  have h := norm_iteratedFDeriv_mul_le hA hH ξ (n := m) (by exact_mod_cast le_top)
  refine h.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hw : (1 + ‖ξ‖) ^ (-(τ₁ + τ₂) - (m : ℝ)) =
      (1 + ‖ξ‖) ^ (-τ₁ - (i : ℝ)) * (1 + ‖ξ‖) ^ (-τ₂ - ((m - i : ℕ) : ℝ)) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    rw [Nat.cast_sub hi']; ring
  rw [hw]
  have hb1 := hSA i ξ
  have hb2 := hSH (m - i) ξ
  calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i A ξ‖ * ‖iteratedFDeriv ℝ (m - i) H ξ‖
      ≤ (m.choose i : ℝ) * (B₁ i * (1 + ‖ξ‖) ^ (-τ₁ - (i : ℝ))) *
        (B₂ (m - i) * (1 + ‖ξ‖) ^ (-τ₂ - ((m - i : ℕ) : ℝ))) := by
        have hc : (0 : ℝ) ≤ m.choose i := Nat.cast_nonneg _
        exact mul_le_mul (mul_le_mul_of_nonneg_left hb1 hc) hb2 (norm_nonneg _)
          (mul_nonneg hc (mul_nonneg (hSA.B_nonneg i) (Real.rpow_nonneg (by positivity) _)))
    _ = _ := by ring

/-- the elementary difference `ξ ↦ G(ξ - v) - G(ξ)` -/
theorem iteratedFDeriv_fdiff (v : V) {G : V → E} (hG : ContDiff ℝ ∞ G) (m : ℕ) (ξ : V) :
    iteratedFDeriv ℝ m (HRS.PDE.Kern.fdiff v G) ξ =
      iteratedFDeriv ℝ m G (ξ - v) - iteratedFDeriv ℝ m G ξ := by
  have : HRS.PDE.Kern.fdiff v G = (fun z => G (z - v)) - G := rfl
  rw [this, iteratedFDeriv_sub_apply, iteratedFDeriv_comp_sub]
  · exact ((hG.comp (contDiff_id.sub contDiff_const)).contDiffAt).of_le (by exact_mod_cast le_top)
  · exact hG.contDiffAt.of_le (by exact_mod_cast le_top)

/-- the constants after one difference -/
def Bstep (τ : ℝ) (B : ℕ → ℝ) : ℕ → ℝ := fun m => 2 ^ |(-τ - ((m + 1 : ℕ) : ℝ))| * B (m + 1)

/-- One finite difference gains one power of decay. -/
theorem Symb.fdiff {τ : ℝ} {B : ℕ → ℝ} {G : V → E} (hG : ContDiff ℝ ∞ G) (hS : Symb τ B G)
    {v : V} (hv : ‖v‖ ≤ 1) :
    Symb (τ + 1) (Bstep τ B) (HRS.PDE.Kern.fdiff v G) := by
  intro m ξ
  rw [iteratedFDeriv_fdiff v hG]
  have hd : Differentiable ℝ (iteratedFDeriv ℝ m G) :=
    hG.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top m)
  set a : ℝ := τ + ((m + 1 : ℕ) : ℝ) with ha
  have hB1 : 0 ≤ B (m + 1) := hS.B_nonneg (m + 1)
  have hbound : ∀ ζ ∈ Metric.closedBall ξ 1,
      ‖fderiv ℝ (iteratedFDeriv ℝ m G) ζ‖ ≤ B (m + 1) * (2 ^ |a| * (1 + ‖ξ‖) ^ (-a)) := by
    intro ζ hζ
    rw [norm_fderiv_iteratedFDeriv]
    refine (hS (m + 1) ζ).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hB1
    have hdist : |‖ζ‖ - ‖ξ‖| ≤ 1 := by
      have h1 : |‖ζ‖ - ‖ξ‖| ≤ ‖ζ - ξ‖ := abs_norm_sub_norm_le _ _
      have h2 : ‖ζ - ξ‖ ≤ 1 := by simpa [dist_eq_norm] using hζ
      linarith
    have := peetre a (norm_nonneg ζ) (norm_nonneg ξ) hdist
    have e : -τ - ((m + 1 : ℕ) : ℝ) = -a := by rw [ha]; ring
    rw [e]; exact this
  have hmem : ξ - v ∈ Metric.closedBall ξ 1 := by
    simpa [dist_eq_norm] using hv
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := iteratedFDeriv ℝ m G)
    (s := Metric.closedBall ξ 1) (C := B (m + 1) * (2 ^ |a| * (1 + ‖ξ‖) ^ (-a)))
    (fun y _ => hd y) hbound (convex_closedBall ξ 1) (Metric.mem_closedBall_self zero_le_one) hmem
  have h2 : ‖ξ - v - ξ‖ ≤ 1 := by simpa using hv
  have hC : 0 ≤ B (m + 1) * (2 ^ |a| * (1 + ‖ξ‖) ^ (-a)) := by positivity
  refine this.trans ?_
  have e : -(τ + 1) - (m : ℝ) = -a := by rw [ha]; push_cast; ring
  rw [e]
  unfold Bstep
  have e2 : -τ - ((m + 1 : ℕ) : ℝ) = -a := by rw [ha]; ring
  rw [e2, abs_neg]
  calc B (m + 1) * (2 ^ |a| * (1 + ‖ξ‖) ^ (-a)) * ‖ξ - v - ξ‖
      ≤ B (m + 1) * (2 ^ |a| * (1 + ‖ξ‖) ^ (-a)) * 1 := mul_le_mul_of_nonneg_left h2 hC
    _ = 2 ^ |a| * B (m + 1) * (1 + ‖ξ‖) ^ (-a) := by ring

/-- iterated constants -/
def BIter : ℕ → ℝ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, _, B => B
  | N + 1, τ, B => BIter N (τ + 1) (Bstep τ B)

/-- Iterating differences along a list of steps of norm `≤ 1`. -/
theorem Symb.fdiffs : ∀ (L : List V) {τ : ℝ} {B : ℕ → ℝ} {G : V → E}, ContDiff ℝ ∞ G →
    Symb τ B G → (∀ v ∈ L, ‖v‖ ≤ 1) →
    Symb (τ + L.length) (BIter L.length τ B) (HRS.PDE.Kern.fdiffs L G)
  | [], τ, B, G, _, hS, _ => by simpa [HRS.PDE.Kern.fdiffs, BIter] using hS
  | v :: L, τ, B, G, hG, hS, hL => by
    have h1 := Symb.fdiff hG hS (hL v (by simp))
    have h2 := Symb.fdiffs L (HRS.PDE.Kern.contDiff_fdiff v hG) h1 (fun w hw => hL w (by simp [hw]))
    have e : τ + (((v :: L).length : ℕ) : ℝ) = τ + 1 + (L.length : ℝ) := by
      simp only [List.length_cons]; push_cast; ring
    rw [e]
    simpa only [HRS.PDE.Kern.fdiffs, List.length_cons, BIter] using h2

/-- vanishing below a threshold survives differences -/
theorem fdiffs_eq_zero : ∀ (L : List V) {G : V → E} {R : ℝ}, (∀ ξ : V, ‖ξ‖ < R → G ξ = 0) →
    (∀ v ∈ L, ‖v‖ ≤ 1) → ∀ ξ : V, ‖ξ‖ < R - L.length → HRS.PDE.Kern.fdiffs L G ξ = 0
  | [], G, R, hG, _, ξ, hξ => by simpa [HRS.PDE.Kern.fdiffs] using hG ξ (by simpa using hξ)
  | v :: L, G, R, hG, hL, ξ, hξ => by
    simp only [HRS.PDE.Kern.fdiffs]
    refine fdiffs_eq_zero L (R := R - 1) ?_ (fun w hw => hL w (by simp [hw])) ξ ?_
    · intro η hη
      have hv := hL v (by simp)
      simp only [HRS.PDE.Kern.fdiff]
      rw [hG η (by linarith), hG (η - v) ?_, sub_zero]
      have := norm_sub_le η v
      linarith
    · simp only [List.length_cons] at hξ
      push_cast at hξ
      linarith


end General

section Homogeneity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem contDiffAt_rpow_norm (τ : ℝ) {ξ : V} (hξ : ξ ≠ 0) :
    ContDiffAt ℝ ∞ (fun x : V => ‖x‖ ^ τ) ξ :=
  (contDiffAt_norm ℝ hξ).rpow_const_of_ne (norm_ne_zero_iff.mpr hξ)

theorem contDiffOn_rpow_norm (τ : ℝ) : ContDiffOn ℝ ∞ (fun x : V => ‖x‖ ^ τ) {(0 : V)}ᶜ :=
  fun _ hx => (contDiffAt_rpow_norm τ hx).contDiffWithinAt

/-- homogeneity of the derivatives of `‖x‖^τ` -/
theorem iteratedFDeriv_rpow_norm_smul (τ : ℝ) {lam : ℝ} (hlam : 0 < lam) {ξ : V} (hξ : ξ ≠ 0)
    (m : ℕ) :
    iteratedFDeriv ℝ m (fun x : V => ‖x‖ ^ τ) (lam • ξ) =
      lam ^ (τ - m) • iteratedFDeriv ℝ m (fun x : V => ‖x‖ ^ τ) ξ := by
  set f : V → ℝ := fun x => ‖x‖ ^ τ with hf
  set e : V ≃L[ℝ] V := ContinuousLinearEquiv.smulLeft (Units.mk0 lam hlam.ne') with he
  have heapp : ∀ x, e x = lam • x := fun x => by simp [he]
  set s : Set V := {(0 : V)}ᶜ with hs
  have hso : IsOpen s := isOpen_compl_singleton
  have hes : e ⁻¹' s = s := by
    ext x
    simp only [Set.mem_preimage, hs, Set.mem_compl_iff, Set.mem_singleton_iff, heapp]
    rw [smul_eq_zero]; simp [hlam.ne']
  have hfe : f ∘ e = fun x => lam ^ τ * f x := by
    funext x
    simp only [Function.comp, heapp, hf, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
    rw [Real.mul_rpow hlam.le (norm_nonneg _)]
  have h1 := e.iteratedFDerivWithin_comp_right f hso.uniqueDiffOn (x := ξ)
    (by rw [heapp]; simpa [hs, hlam.ne'] using hξ) m
  rw [hes, iteratedFDerivWithin_of_isOpen m hso (by simpa [hs] using hξ), hfe,
    iteratedFDerivWithin_of_isOpen m hso (by rw [heapp]; simpa [hs, hlam.ne'] using hξ)] at h1
  have hcd : ContDiffAt ℝ m f ξ := (contDiffAt_rpow_norm τ hξ).of_le (by exact_mod_cast le_top)
  have h2 : iteratedFDeriv ℝ m (fun x => lam ^ τ * f x) ξ = lam ^ τ • iteratedFDeriv ℝ m f ξ :=
    iteratedFDeriv_const_smul_apply (a := lam ^ τ) hcd
  rw [h2, heapp] at h1
  have h3 : ((iteratedFDeriv ℝ m f (lam • ξ)).compContinuousLinearMap fun _ => (e : V →L[ℝ] V)) =
      lam ^ m • iteratedFDeriv ℝ m f (lam • ξ) := by
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, smul_apply]
    have : (fun i => (e : V →L[ℝ] V) (v i)) = fun i => lam • v i := by funext i; exact heapp (v i)
    rw [this, ContinuousMultilinearMap.map_smul_univ]
    simp
  rw [h3] at h1
  have hlm : (0 : ℝ) < lam ^ m := pow_pos hlam m
  have hrp : lam ^ (τ - m) = lam ^ τ * (lam ^ m)⁻¹ := by
    rw [Real.rpow_sub hlam, Real.rpow_natCast, div_eq_mul_inv]
  have h4 : iteratedFDeriv ℝ m f (lam • ξ) =
      (lam ^ m)⁻¹ • (lam ^ τ • iteratedFDeriv ℝ m f ξ) := by
    rw [h1, smul_smul, inv_mul_cancel₀ hlm.ne', one_smul]
  rw [h4, hrp, smul_smul, mul_comm]

/-- bound on the derivatives of `‖x‖^τ` away from the origin -/
theorem norm_iteratedFDeriv_rpow_norm_le (τ : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : V, ξ ≠ 0 →
      ‖iteratedFDeriv ℝ m (fun x : V => ‖x‖ ^ τ) ξ‖ ≤ C * ‖ξ‖ ^ (τ - m) := by
  set f : V → ℝ := fun x => ‖x‖ ^ τ with hf
  set s : Set V := {(0 : V)}ᶜ with hs
  have hso : IsOpen s := isOpen_compl_singleton
  have hcont : ContinuousOn (iteratedFDeriv ℝ m f) s := by
    have h1 := (contDiffOn_rpow_norm (V := V) τ).continuousOn_iteratedFDerivWithin (m := m)
      (by exact_mod_cast le_top) hso.uniqueDiffOn
    exact h1.congr (iteratedFDerivWithin_of_isOpen m hso).symm
  have hsph : Metric.sphere (0 : V) 1 ⊆ s := fun x hx => by
    simp only [hs, Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl; simp at hx
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : V) 1).exists_bound_of_continuousOn (hcont.mono hsph)
  refine ⟨max C 0, le_max_right _ _, fun ξ hξ => ?_⟩
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  set u : V := ‖ξ‖⁻¹ • ξ with hu
  have hu1 : u ∈ Metric.sphere (0 : V) 1 := by
    simp [hu, norm_smul, hn.ne']
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu1; simp at hu1
  have hξu : ξ = ‖ξ‖ • u := by
    simp [hu, smul_smul, hn.ne']
  have := iteratedFDeriv_rpow_norm_smul τ hn hu0 m
  rw [← hξu] at this
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn _), mul_comm]
  gcongr
  exact (hC u hu1).trans (le_max_left _ _)

end Homogeneity


section Cutoff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- hypotheses on a cutoff-type function `T`: constant on the unit ball and outside the ball of
radius `2` -/
structure CutHyp (T : V → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ T
  inner : ∃ c : ℝ, ∀ ζ : V, ‖ζ‖ ≤ 1 → T ζ = c
  outer : ∃ c : ℝ, ∀ ζ : V, 2 ≤ ‖ζ‖ → T ζ = c

theorem iteratedFDeriv_eq_zero_of_const {T : V → ℝ} {U : Set V} (hU : IsOpen U) (c : ℝ)
    (hT : ∀ ζ ∈ U, T ζ = c) {ζ : V} (hζ : ζ ∈ U) {m : ℕ} (hm : 1 ≤ m) :
    iteratedFDeriv ℝ m T ζ = 0 := by
  have h : T =ᶠ[𝓝 ζ] fun _ => c := by
    filter_upwards [hU.mem_nhds hζ] with x hx using hT x hx
  rw [(h.iteratedFDeriv ℝ m).self_of_nhds, iteratedFDeriv_const_of_ne (by omega)]
  rfl

theorem CutHyp.bound {T : V → ℝ} (h : CutHyp T) (m : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ : V, ‖iteratedFDeriv ℝ m T ζ‖ ≤ M := by
  obtain ⟨c2, hc2⟩ := h.outer
  have hc : Continuous (iteratedFDeriv ℝ m T) :=
    h.smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : V) 2).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max (max M0 |c2|) 0, le_max_right _ _, fun ζ => ?_⟩
  by_cases hζ : ‖ζ‖ ≤ 2
  · exact (hM0 ζ (by simpa using hζ)).trans ((le_max_left _ _).trans (le_max_left _ _))
  · push Not at hζ
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [norm_iteratedFDeriv_zero, hc2 ζ hζ.le, Real.norm_eq_abs]
      exact (le_max_right M0 |c2|).trans (le_max_left _ _)
    · rw [iteratedFDeriv_eq_zero_of_const (U := {x : V | 2 < ‖x‖}) (isOpen_lt continuous_const continuous_norm)
        c2 (fun x hx => hc2 x hx.le) hζ hm, norm_zero]
      exact le_max_right _ _

theorem CutHyp.deriv_eq_zero {T : V → ℝ} (h : CutHyp T) {m : ℕ} (hm : 1 ≤ m) {ζ : V}
    (hζ : ‖ζ‖ < 1 ∨ 2 < ‖ζ‖) : iteratedFDeriv ℝ m T ζ = 0 := by
  obtain ⟨c1, hc1⟩ := h.inner
  obtain ⟨c2, hc2⟩ := h.outer
  rcases hζ with hζ | hζ
  · exact iteratedFDeriv_eq_zero_of_const (U := {x : V | ‖x‖ < 1}) (isOpen_lt continuous_norm continuous_const)
      c1 (fun x hx => hc1 x (le_of_lt hx)) hζ hm
  · exact iteratedFDeriv_eq_zero_of_const (U := {x : V | 2 < ‖x‖}) (isOpen_lt continuous_const continuous_norm)
      c2 (fun x hx => hc2 x hx.le) hζ hm

/-- the scaled cutoff `T(λ ·)`, `0 < λ ≤ 1`, is a symbol of order `0` with bounds independent of `λ` -/
theorem CutHyp.symb {T : V → ℝ} (h : CutHyp T) :
    ∃ B : ℕ → ℝ, ∀ lam : ℝ, 0 < lam → lam ≤ 1 → Symb 0 B (fun ξ : V => T (lam • ξ)) := by
  choose M hM0 hM using fun m => h.bound m
  refine ⟨fun m => 4 ^ m * M m, fun lam hlam hlam1 m ξ => ?_⟩
  have hdn : iteratedFDeriv ℝ m (fun z => T (lam • z)) ξ = lam ^ m • iteratedFDeriv ℝ m T (lam • ξ) := by
    have := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := m) lam (f := T)
      (h.smooth.of_le (by exact_mod_cast le_top))
    exact congrFun this ξ
  rw [hdn, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos hlam]
  have hw : (0 : ℝ) ≤ (1 + ‖ξ‖) ^ (-(0 : ℝ) - (m : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hMm := hM0 m
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero, neg_zero, Real.rpow_zero, mul_one]
    exact hM 0 (lam • ξ)
  · by_cases hs : ‖lam • ξ‖ < 1 ∨ 2 < ‖lam • ξ‖
    · rw [h.deriv_eq_zero hm hs, norm_zero, mul_zero]
      positivity
    · push Not at hs
      have h1 : 1 ≤ lam * ‖ξ‖ := by
        have := hs.1; rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at this
      have hξ1 : 1 ≤ ‖ξ‖ := by nlinarith [norm_nonneg ξ]
      have hl : lam ≤ 4 * (1 + ‖ξ‖)⁻¹ := by
        have hpos : 0 < 1 + ‖ξ‖ := by positivity
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]
        have := hs.2
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at this
        nlinarith
      have hrw : (1 + ‖ξ‖) ^ (-(0 : ℝ) - (m : ℝ)) = ((1 + ‖ξ‖)⁻¹) ^ m := by
        rw [neg_zero, zero_sub, Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow]
      rw [hrw]
      calc lam ^ m * ‖iteratedFDeriv ℝ m T (lam • ξ)‖ ≤ (4 * (1 + ‖ξ‖)⁻¹) ^ m * M m := by
            gcongr
            exact hM m _
        _ = 4 ^ m * M m * ((1 + ‖ξ‖)⁻¹) ^ m := by rw [mul_pow]; ring

end Cutoff


section QClass

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem contDiff_Q (τ : ℝ) {T : V → ℝ} (hT : CutHyp T) (h0 : ∀ ζ : V, ‖ζ‖ ≤ 1 → T ζ = 0) :
    ContDiff ℝ ∞ (fun ξ : V => ‖ξ‖ ^ τ * T ((2 : ℝ) • ξ)) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst hξ
    have : (fun ξ : V => ‖ξ‖ ^ τ * T ((2 : ℝ) • ξ)) =ᶠ[𝓝 (0 : V)] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : V) (by norm_num : (0 : ℝ) < 1 / 2)] with η hη
      have : ‖η‖ < 1 / 2 := by simpa using hη
      rw [h0 _ (by rw [norm_smul]; norm_num; linarith), mul_zero]
    exact (contDiffAt_const).congr_of_eventuallyEq this
  · exact (contDiffAt_rpow_norm τ hξ).mul
      ((hT.smooth.comp (contDiff_id.const_smul (2 : ℝ))).contDiffAt)

/-- the smooth radial symbol `‖ξ‖^τ (1 - χ(2ξ))` of order `-τ` -/
theorem exists_symb_Q (τ : ℝ) {T : V → ℝ} (hT : CutHyp T) (h0 : ∀ ζ : V, ‖ζ‖ ≤ 1 → T ζ = 0)
    (h1 : ∀ ζ : V, 2 ≤ ‖ζ‖ → T ζ = 1) :
    ∃ B : ℕ → ℝ, Symb (-τ) B (fun ξ : V => ‖ξ‖ ^ τ * T ((2 : ℝ) • ξ)) := by
  set Q : V → ℝ := fun ξ => ‖ξ‖ ^ τ * T ((2 : ℝ) • ξ) with hQ
  have hQs : ContDiff ℝ ∞ Q := contDiff_Q τ hT h0
  have hcont : ∀ m : ℕ, Continuous (iteratedFDeriv ℝ m Q) := fun m =>
    hQs.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hball : ∀ m : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ : V, ‖ξ‖ ≤ 1 → ‖iteratedFDeriv ℝ m Q ξ‖ ≤ M := by
    intro m
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : V) 1).exists_bound_of_continuousOn (hcont m).continuousOn
    exact ⟨max M 0, le_max_right _ _, fun ξ hξ => (hM ξ (by simpa using hξ)).trans (le_max_left _ _)⟩
  choose M hM0 hM using hball
  choose C hC0 hC using fun m => norm_iteratedFDeriv_rpow_norm_le (V := V) τ m
  refine ⟨fun m => (M m + C m) * 2 ^ |τ - m|, fun m ξ => ?_⟩
  have hexp : -(-τ) - (m : ℝ) = τ - m := by ring
  rw [hexp]
  have hw : (0 : ℝ) < (1 + ‖ξ‖) ^ (τ - m) := Real.rpow_pos_of_pos (by positivity) _
  by_cases hξ : ‖ξ‖ ≤ 1
  · have hp := peetre (-(τ - m)) (x := 0) (y := ‖ξ‖) le_rfl (norm_nonneg ξ) (by
      rw [zero_sub, abs_neg, abs_of_nonneg (norm_nonneg ξ)]; exact hξ)
    rw [neg_neg, add_zero, Real.one_rpow, abs_neg] at hp
    calc ‖iteratedFDeriv ℝ m Q ξ‖ ≤ M m := hM m ξ hξ
      _ = M m * 1 := (mul_one _).symm
      _ ≤ M m * (2 ^ |τ - m| * (1 + ‖ξ‖) ^ (τ - m)) := mul_le_mul_of_nonneg_left hp (hM0 m)
      _ ≤ (M m + C m) * 2 ^ |τ - m| * (1 + ‖ξ‖) ^ (τ - m) := by
        have : 0 ≤ C m * (2 ^ |τ - m| * (1 + ‖ξ‖) ^ (τ - m)) := by positivity [hC0 m]
        nlinarith
  · push Not at hξ
    have hξ0 : ξ ≠ 0 := by intro h; rw [h, norm_zero] at hξ; linarith
    have heq : Q =ᶠ[𝓝 ξ] fun x : V => ‖x‖ ^ τ := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hξ] with η hη
      have hη' : 1 < ‖η‖ := hη
      simp only [hQ]
      rw [h1 _ (by rw [norm_smul]; norm_num; linarith), mul_one]
    rw [(heq.iteratedFDeriv ℝ m).self_of_nhds]
    have hp := peetre (-(τ - m)) (x := ‖ξ‖ - 1) (y := ‖ξ‖) (by linarith) (norm_nonneg ξ) (by
      rw [abs_of_nonpos (by linarith)]; linarith)
    rw [neg_neg, abs_neg, show 1 + (‖ξ‖ - 1) = ‖ξ‖ by ring] at hp
    calc ‖iteratedFDeriv ℝ m (fun x : V => ‖x‖ ^ τ) ξ‖ ≤ C m * ‖ξ‖ ^ (τ - m) := hC m ξ hξ0
      _ ≤ C m * (2 ^ |τ - m| * (1 + ‖ξ‖) ^ (τ - m)) := mul_le_mul_of_nonneg_left hp (hC0 m)
      _ ≤ (M m + C m) * 2 ^ |τ - m| * (1 + ‖ξ‖) ^ (τ - m) := by
        have : 0 ≤ M m * (2 ^ |τ - m| * (1 + ‖ξ‖) ^ (τ - m)) := by positivity [hM0 m]
        nlinarith

end QClass


section Poly

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem norm_iteratedFDeriv_succ_clm (ℓ : V →L[ℝ] ℝ) (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ (n + 1) ℓ x‖ = if n = 0 then ‖ℓ‖ else 0 := by
  have hf : fderiv ℝ ℓ = fun _ => ℓ := by
    funext y; exact ℓ.fderiv
  rw [← norm_iteratedFDeriv_fderiv, hf]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [iteratedFDeriv_const_of_ne hn.ne']; simp [hn.ne']

/-- the coefficients for a single linear form -/
def Bl : ℕ → ℝ := fun m => if m ≤ 1 then 1 else 0

theorem symb_inner (v : V) (hv : ‖v‖ ≤ 1) : Symb (-1) Bl (fun ξ : V => inner ℝ v ξ) := by
  intro m ξ
  have hw : 0 ≤ (1 + ‖ξ‖) ^ (-(-1 : ℝ) - (m : ℝ)) := Real.rpow_nonneg (by positivity) _
  rcases m with _ | m
  · simp only [norm_iteratedFDeriv_zero, Bl, Nat.zero_le, if_true, Nat.cast_zero, sub_zero, neg_neg,
      Real.rpow_one, one_mul]
    calc ‖inner ℝ v ξ‖ ≤ ‖v‖ * ‖ξ‖ := norm_inner_le_norm _ _
      _ ≤ 1 * ‖ξ‖ := by gcongr
      _ ≤ 1 + ‖ξ‖ := by linarith
  · have hℓ : (fun ξ : V => inner ℝ v ξ) = ⇑(innerSL ℝ v) := by funext y; simp
    rw [hℓ, norm_iteratedFDeriv_succ_clm]
    by_cases hm : m = 0
    · subst hm
      simp only [Bl, if_true, innerSL_apply_norm, zero_add, Nat.le_refl]
      norm_num
      exact hv
    · have : ¬ (m + 1 ≤ 1) := by omega
      simp [Bl, hm, this]

/-- the coefficients of a product of `n` linear forms -/
def BP : ℕ → (ℕ → ℝ)
  | 0 => fun m => if m = 0 then 1 else 0
  | n + 1 => fun m => ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bl i * BP n (m - i)

end Poly


section Poly2

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem contDiff_polyP : ∀ (n : ℕ) (v : Fin n → V), ContDiff ℝ ∞ (fun ξ : V => ∏ j, inner ℝ (v j) ξ)
  | 0, v => by simpa using contDiff_const
  | n + 1, v => by
    have h : (fun ξ : V => ∏ j, inner ℝ (v j) ξ) =
        fun ξ => inner ℝ (v 0) ξ * ∏ j : Fin n, inner ℝ (v j.succ) ξ := by
      funext ξ; rw [Fin.prod_univ_succ]
    rw [h]
    exact ((innerSL ℝ (v 0)).contDiff).mul (contDiff_polyP n (fun j => v j.succ))

theorem symb_polyP : ∀ (n : ℕ) (v : Fin n → V), (∀ j, ‖v j‖ ≤ 1) →
    Symb (-(n : ℝ)) (BP n) (fun ξ : V => ∏ j, inner ℝ (v j) ξ)
  | 0, v, _ => by
    intro m ξ
    simp only [Finset.univ_eq_empty, Finset.prod_empty, BP, Nat.cast_zero, neg_zero, zero_sub]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · rw [iteratedFDeriv_const_of_ne hm.ne']
      have : (1 + ‖ξ‖) ^ (-(m : ℝ)) ≥ 0 := Real.rpow_nonneg (by positivity) _
      simp [hm.ne']
  | n + 1, v, hv => by
    have h : (fun ξ : V => ∏ j, inner ℝ (v j) ξ) =
        fun ξ => inner ℝ (v 0) ξ * ∏ j : Fin n, inner ℝ (v j.succ) ξ := by
      funext ξ; rw [Fin.prod_univ_succ]
    rw [h]
    have := Symb.mul (innerSL ℝ (v 0)).contDiff (contDiff_polyP n (fun j => v j.succ))
      (symb_inner (v 0) (hv 0)) (symb_polyP n (fun j => v j.succ) (fun j => hv j.succ))
    have e : (-1 : ℝ) + -(n : ℝ) = -((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e] at this
    simpa [BP] using this

end Poly2


section Assembly

variable {d : ℕ}

/-- the high-frequency symbol `‖ξ‖^{s-d} χ(δξ)² ∏_j ⟨v_j, ξ⟩ (1 - χ(ρξ))`, written with the smooth
radial factor `Q(ξ) = ‖ξ‖^{s-d}(1 - χ(2ξ))` (equal to `‖ξ‖^{s-d}` on the support of the last factor) -/
def Gsym (d : ℕ) (s : ℝ) (χ : Euc d → ℝ) (δ ρ : ℝ) {n : ℕ} (v : Fin n → Euc d) (ξ : Euc d) : ℝ :=
  (‖ξ‖ ^ (s - d) * (1 - χ ((2 : ℝ) • ξ))) * χ (δ • ξ) ^ 2 * (∏ j, inner ℝ (v j) ξ) *
    (1 - χ (ρ • ξ))

variable {χ : Euc d → ℝ}

theorem cutHyp_one_sub (hs : ContDiff ℝ ∞ χ) (h1 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1)
    (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) : CutHyp (fun ζ : Euc d => 1 - χ ζ) :=
  ⟨contDiff_const.sub hs, ⟨0, fun ζ hζ => by simp [h1 ζ hζ]⟩, ⟨1, fun ζ hζ => by simp [h2 ζ hζ]⟩⟩

theorem cutHyp_sq (hs : ContDiff ℝ ∞ χ) (h1 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1)
    (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) : CutHyp (fun ζ : Euc d => χ ζ ^ 2) :=
  ⟨hs.pow 2, ⟨1, fun ζ hζ => by simp [h1 ζ hζ]⟩, ⟨0, fun ζ hζ => by simp [h2 ζ hζ]⟩⟩

theorem contDiff_Gsym (s : ℝ) (hs : ContDiff ℝ ∞ χ) (h1 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1)
    (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) (δ ρ : ℝ) {n : ℕ} (v : Fin n → Euc d) :
    ContDiff ℝ ∞ (Gsym d s χ δ ρ v) := by
  have hT1 := cutHyp_one_sub hs h1 h2
  have hQ := contDiff_Q (s - d) hT1 (fun ζ hζ => by simp [h1 ζ hζ])
  have hX : ContDiff ℝ ∞ (fun ξ : Euc d => χ (δ • ξ) ^ 2) :=
    (hs.comp (contDiff_id.const_smul δ)).pow 2
  have hW : ContDiff ℝ ∞ (fun ξ : Euc d => 1 - χ (ρ • ξ)) :=
    contDiff_const.sub (hs.comp (contDiff_id.const_smul ρ))
  exact ((hQ.mul hX).mul (contDiff_polyP n v)).mul hW

/-- uniform symbol bounds for `Gsym` -/
theorem Gsym_symb (s : ℝ) (hs : ContDiff ℝ ∞ χ) (h1 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1)
    (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) (n : ℕ) :
    ∃ B : ℕ → ℝ, ∀ δ ρ : ℝ, 0 < δ → δ ≤ 1 → 0 < ρ → ρ ≤ 1 → ∀ v : Fin n → Euc d,
      (∀ j, ‖v j‖ ≤ 1) → Symb (-(s - d + n)) B (Gsym d s χ δ ρ v) := by
  have hT1 := cutHyp_one_sub hs h1 h2
  have hT2 := cutHyp_sq hs h1 h2
  obtain ⟨BQ, hBQ⟩ := exists_symb_Q (s - d) hT1 (fun ζ hζ => by simp [h1 ζ hζ])
    (fun ζ hζ => by simp [h2 ζ hζ])
  obtain ⟨BX, hBX⟩ := hT2.symb
  obtain ⟨BW, hBW⟩ := hT1.symb
  set B1 : ℕ → ℝ := fun m => ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * BQ i * BX (m - i) with hB1
  set B2 : ℕ → ℝ := fun m => ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * B1 i * BP n (m - i) with hB2
  set B3 : ℕ → ℝ := fun m => ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * B2 i * BW (m - i) with hB3
  refine ⟨B3, fun δ ρ hδ hδ1 hρ hρ1 v hv => ?_⟩
  have hQ := contDiff_Q (s - d) hT1 (fun ζ hζ => by simp [h1 ζ hζ])
  have hX : ContDiff ℝ ∞ (fun ξ : Euc d => χ (δ • ξ) ^ 2) :=
    (hs.comp (contDiff_id.const_smul δ)).pow 2
  have hW : ContDiff ℝ ∞ (fun ξ : Euc d => 1 - χ (ρ • ξ)) :=
    contDiff_const.sub (hs.comp (contDiff_id.const_smul ρ))
  have s1 := Symb.mul hQ hX hBQ (hBX δ hδ hδ1)
  have s2 := Symb.mul (hQ.mul hX) (contDiff_polyP n v) s1 (symb_polyP n v hv)
  have s3 := Symb.mul ((hQ.mul hX).mul (contDiff_polyP n v)) hW s2 (hBW ρ hρ hρ1)
  have e : -(s - (d : ℝ)) + 0 + -(n : ℝ) + 0 = -(s - d + n) := by ring
  rw [e] at s3
  exact s3

theorem Gsym_eq_zero (s : ℝ) (h1 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1) (δ ρ : ℝ) (hρ : 0 < ρ)
    {n : ℕ} (v : Fin n → Euc d) (ξ : Euc d) (hξ : ‖ξ‖ < 1 / ρ) : Gsym d s χ δ ρ v ξ = 0 := by
  have : χ (ρ • ξ) = 1 := by
    apply h1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    rw [lt_div_iff₀ hρ] at hξ
    nlinarith
  simp [Gsym, this]

theorem Gsym_eq (s : ℝ) (h1 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1) (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0)
    (δ ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {n : ℕ} (v : Fin n → Euc d) (ξ : Euc d) :
    Gsym d s χ δ ρ v ξ =
      ‖ξ‖ ^ (s - d) * χ (δ • ξ) ^ 2 * (∏ j, inner ℝ (v j) ξ) * (1 - χ (ρ • ξ)) := by
  by_cases hχ : χ (ρ • ξ) = 1
  · simp [Gsym, hχ]
  · have hn : 1 < ρ * ‖ξ‖ := by
      by_contra hle
      push Not at hle
      apply hχ
      apply h1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      exact hle
    have hξ : 1 ≤ ‖ξ‖ := by nlinarith [norm_nonneg ξ]
    have : χ ((2 : ℝ) • ξ) = 0 := by
      apply h2
      rw [norm_smul]; norm_num; linarith
    simp [Gsym, this]

/-- the main symbol estimate: `N` coordinate differences of `Gsym` gain `N` powers of decay,
with a constant independent of `δ, ρ, v, i`. -/
theorem Gsym_fdiffs_bound (s : ℝ) (hs : ContDiff ℝ ∞ χ) (h1 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1)
    (h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0) (n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ ρ : ℝ, 0 < δ → δ ≤ 1 → 0 < ρ → ρ ≤ 1 → ∀ v : Fin n → Euc d,
      (∀ j, ‖v j‖ ≤ 1) → ∀ i : Fin d, ∀ ξ : Euc d,
        ‖HRS.PDE.Kern.fdiffs (List.replicate N (EuclideanSpace.single i (1 : ℝ)))
          (Gsym d s χ δ ρ v) ξ‖ ≤ C * (1 + ‖ξ‖) ^ (s - d + n - N) ∧
        (‖ξ‖ < 1 / ρ - N → HRS.PDE.Kern.fdiffs (List.replicate N (EuclideanSpace.single i (1 : ℝ)))
          (Gsym d s χ δ ρ v) ξ = 0) := by
  obtain ⟨B, hB⟩ := Gsym_symb s hs h1 h2 n
  refine ⟨|BIter N (-(s - d + n)) B 0|, abs_nonneg _, fun δ ρ hδ hδ1 hρ hρ1 v hv i ξ => ?_⟩
  have hL : ∀ w ∈ List.replicate N (EuclideanSpace.single i (1 : ℝ) : Euc d), ‖w‖ ≤ 1 := by
    intro w hw
    rw [List.eq_of_mem_replicate hw]
    simp
  have hsy := Symb.fdiffs (List.replicate N (EuclideanSpace.single i (1 : ℝ) : Euc d))
    (contDiff_Gsym s hs h1 h2 δ ρ v) (hB δ ρ hδ hδ1 hρ hρ1 v hv) hL
  refine ⟨?_, fun hξ => ?_⟩
  · have := hsy 0 ξ
    rw [norm_iteratedFDeriv_zero, List.length_replicate] at this
    have e : -(-(s - (d : ℝ) + n) + (N : ℝ)) - ((0 : ℕ) : ℝ) = s - d + n - N := by push_cast; ring
    rw [e] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by positivity) _)
  · refine fdiffs_eq_zero (List.replicate N (EuclideanSpace.single i (1 : ℝ) : Euc d))
      (fun η hη => Gsym_eq_zero s h1 δ ρ hρ v η hη) hL ξ ?_
    rwa [List.length_replicate]

end Assembly

end HRS
