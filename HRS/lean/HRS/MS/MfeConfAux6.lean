import HRS.MS.MfeConfAux5

/-!
# S.B.1, packet F1 (part 1): Landau-Kolmogorov type interpolation (sup-norm smallness of derivatives)

If `f` is `C³` on `ℝ^d` with `‖D²f‖ ≤ M₂`, `‖D³f‖ ≤ M₃` and `sup |f| ≤ δ`, then `‖Df‖ ≤ 2δ/h + M₂h` and
`‖D²f‖ ≤ 8δ/h² + 6M₃h` for every `h > 0` (mean value theorem along lines, polarisation for `D²`).  Used to turn the
`sup`-Lipschitz continuity in time of a mean-field trajectory into continuity of its first two derivatives.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MfeConf

variable {d : ℕ}

/-! ### One-dimensional lemmas -/

theorem sb1_lk1d_first {φ φ' φ'' : ℝ → ℝ} (h1 : ∀ t, HasDerivAt φ (φ' t) t)
    (h2 : ∀ t, HasDerivAt φ' (φ'' t) t) {δ M2 h : ℝ} (hh : 0 < h)
    (hφ : ∀ t ∈ Set.Icc 0 h, |φ t| ≤ δ) (hφ2 : ∀ t ∈ Set.Icc 0 h, |φ'' t| ≤ M2) :
    |φ' 0| ≤ 2 * δ / h + M2 * h := by
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope φ φ' hh
    (fun t _ => (h1 t).continuousAt.continuousWithinAt) (fun t _ => h1 t)
  have hξ0 : |φ' ξ| ≤ 2 * δ / h := by
    rw [hξe, sub_zero, abs_div, abs_of_pos hh, div_le_div_iff_of_pos_right hh]
    calc |φ h - φ 0| ≤ |φ h| + |φ 0| := abs_sub _ _
      _ ≤ δ + δ := add_le_add (hφ h ⟨hh.le, le_rfl⟩) (hφ 0 ⟨le_rfl, hh.le⟩)
      _ = 2 * δ := by ring
  have hM : ‖φ' ξ - φ' 0‖ ≤ M2 * ‖ξ - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ') (f' := φ'') (s := Set.Icc 0 h)
      (fun t _ => (h2 t).hasDerivWithinAt) (fun t ht => ?_) (convex_Icc 0 h)
      ⟨le_rfl, hh.le⟩ ⟨hξ.1.le, hξ.2.le⟩
    rw [Real.norm_eq_abs]; exact hφ2 t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_pos hξ.1] at hM
  have hM0 : 0 ≤ M2 := (abs_nonneg _).trans (hφ2 0 ⟨le_rfl, hh.le⟩)
  have : |φ' 0| ≤ |φ' ξ| + |φ' ξ - φ' 0| := by
    have := abs_sub (φ' ξ) (φ' 0)
    have e : φ' 0 = φ' ξ - (φ' ξ - φ' 0) := by ring
    calc |φ' 0| = |φ' ξ - (φ' ξ - φ' 0)| := by rw [← e]
      _ ≤ _ := abs_sub _ _
  nlinarith [hξ.2]

theorem sb1_lk1d_second {φ φ' φ'' φ''' : ℝ → ℝ} (h1 : ∀ t, HasDerivAt φ (φ' t) t)
    (h2 : ∀ t, HasDerivAt φ' (φ'' t) t) (h3 : ∀ t, HasDerivAt φ'' (φ''' t) t) {δ M3 h : ℝ}
    (hh : 0 < h) (hφ : ∀ t ∈ Set.Icc 0 (3 * h), |φ t| ≤ δ)
    (hφ3 : ∀ t ∈ Set.Icc 0 (3 * h), |φ''' t| ≤ M3) : |φ'' 0| ≤ 4 * δ / h ^ 2 + 3 * M3 * h := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hφ 0 ⟨le_rfl, by linarith⟩)
  -- a point `ξ₁ ∈ (0,h)` and `ξ₂ ∈ (2h,3h)` where `φ'` is small
  obtain ⟨ξ₁, hξ₁, he₁⟩ := exists_hasDerivAt_eq_slope φ φ' hh
    (fun t _ => (h1 t).continuousAt.continuousWithinAt) (fun t _ => h1 t)
  have hh2 : 2 * h < 3 * h := by linarith
  obtain ⟨ξ₂, hξ₂, he₂⟩ := exists_hasDerivAt_eq_slope φ φ' hh2
    (fun t _ => (h1 t).continuousAt.continuousWithinAt) (fun t _ => h1 t)
  have hsl : ∀ a b : ℝ, 0 ≤ a → b ≤ 3 * h → a < b → b - a = h → |(φ b - φ a) / (b - a)| ≤ 2 * δ / h := by
    intro a b ha hb hab hba
    rw [hba, abs_div, abs_of_pos hh, div_le_div_iff_of_pos_right hh]
    calc |φ b - φ a| ≤ |φ b| + |φ a| := abs_sub _ _
      _ ≤ δ + δ := add_le_add (hφ b ⟨by linarith, hb⟩) (hφ a ⟨ha, by linarith⟩)
      _ = 2 * δ := by ring
  have hs1 : |φ' ξ₁| ≤ 2 * δ / h := by
    rw [he₁]; exact hsl 0 h le_rfl (by linarith) hh (by ring)
  have hs2 : |φ' ξ₂| ≤ 2 * δ / h := by
    rw [he₂]; exact hsl (2 * h) (3 * h) (by linarith) le_rfl hh2 (by ring)
  have hξ12 : ξ₁ < ξ₂ := by linarith [hξ₁.2, hξ₂.1]
  obtain ⟨ζ, hζ, hζe⟩ := exists_hasDerivAt_eq_slope φ' φ'' hξ12
    (fun t _ => (h2 t).continuousAt.continuousWithinAt) (fun t _ => h2 t)
  have hgap : h < ξ₂ - ξ₁ := by linarith [hξ₁.2, hξ₂.1]
  have hζbd : |φ'' ζ| ≤ 4 * δ / h ^ 2 := by
    rw [hζe, abs_div, abs_of_pos (by linarith : 0 < ξ₂ - ξ₁)]
    calc |φ' ξ₂ - φ' ξ₁| / (ξ₂ - ξ₁) ≤ (4 * δ / h) / h := by
          have hnum : |φ' ξ₂ - φ' ξ₁| ≤ 4 * δ / h := by
            calc |φ' ξ₂ - φ' ξ₁| ≤ |φ' ξ₂| + |φ' ξ₁| := abs_sub _ _
              _ ≤ 2 * δ / h + 2 * δ / h := add_le_add hs2 hs1
              _ = 4 * δ / h := by ring
          calc |φ' ξ₂ - φ' ξ₁| / (ξ₂ - ξ₁) ≤ |φ' ξ₂ - φ' ξ₁| / h :=
                div_le_div_of_nonneg_left (abs_nonneg _) hh hgap.le
            _ ≤ _ := div_le_div_of_nonneg_right hnum hh.le
      _ = 4 * δ / h ^ 2 := by field_simp
  have hM : ‖φ'' ζ - φ'' 0‖ ≤ M3 * ‖ζ - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ'') (f' := φ''') (s := Set.Icc 0 (3 * h))
      (fun t _ => (h3 t).hasDerivWithinAt) (fun t ht => ?_) (convex_Icc 0 (3 * h))
      ⟨le_rfl, by linarith⟩ ⟨by linarith [hξ₁.1, hξ₁.2, hζ.1], by linarith [hξ₂.2, hζ.2]⟩
    rw [Real.norm_eq_abs]; exact hφ3 t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero,
    abs_of_pos (by linarith [hξ₁.1, hζ.1] : 0 < ζ)] at hM
  have hM3 : 0 ≤ M3 := (abs_nonneg _).trans (hφ3 0 ⟨le_rfl, by linarith⟩)
  have hζ3 : ζ < 3 * h := by linarith [hζ.2, hξ₂.2]
  have : |φ'' 0| ≤ |φ'' ζ| + |φ'' ζ - φ'' 0| := by
    have e : φ'' 0 = φ'' ζ - (φ'' ζ - φ'' 0) := by ring
    calc |φ'' 0| = |φ'' ζ - (φ'' ζ - φ'' 0)| := by rw [← e]
      _ ≤ _ := abs_sub _ _
  nlinarith [mul_le_mul_of_nonneg_left hζ3.le hM3]


/-! ### Lines in `ℝ^d` -/

theorem sb1_hasDerivAt_line {g : Euc d → ℝ} (x u : Euc d) (t : ℝ) (hg : DifferentiableAt ℝ g (x + t • u)) :
    HasDerivAt (fun s : ℝ => g (x + s • u)) (fderiv ℝ g (x + t • u) u) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • u) u t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_add x
  exact hg.hasFDerivAt.comp_hasDerivAt t h1

theorem sb1_hasDerivAt_line_clm {g : Euc d → (Euc d →L[ℝ] ℝ)} (x u w : Euc d) (t : ℝ)
    (hg : DifferentiableAt ℝ g (x + t • u)) :
    HasDerivAt (fun s : ℝ => g (x + s • u) w) (fderiv ℝ g (x + t • u) u w) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • u) u t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_add x
  have h2 := hg.hasFDerivAt.comp_hasDerivAt t h1
  have h3 := h2.clm_apply (hasDerivAt_const t w)
  simpa using h3

theorem sb1_norm_fderiv_fderiv (f : Euc d → ℝ) (y : Euc d) :
    ‖fderiv ℝ (fderiv ℝ f) y‖ = ‖iteratedFDeriv ℝ 2 f y‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

/-- first derivative: `‖Df‖ ≤ 2δ/h + M₂ h`. -/
theorem sb1_lk_first {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) {δ M2 h : ℝ} (hh : 0 < h)
    (hδ : ∀ x, |f x| ≤ δ) (hM2 : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ M2) (x : Euc d) :
    ‖fderiv ℝ f x‖ ≤ 2 * δ / h + M2 * h := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ x)
  have hM0 : 0 ≤ M2 := (norm_nonneg _).trans (hM2 x)
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hunit : ∀ u : Euc d, ‖u‖ = 1 → |fderiv ℝ f x u| ≤ 2 * δ / h + M2 * h := by
    intro u hu
    have hbd : ∀ t : ℝ, |fderiv ℝ (fderiv ℝ f) (x + t • u) u u| ≤ M2 := by
      intro t
      have := (fderiv ℝ (fderiv ℝ f) (x + t • u)).le_opNorm u
      have h2 := ((fderiv ℝ (fderiv ℝ f) (x + t • u)) u).le_opNorm u
      calc |fderiv ℝ (fderiv ℝ f) (x + t • u) u u|
          = ‖fderiv ℝ (fderiv ℝ f) (x + t • u) u u‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ (fderiv ℝ f) (x + t • u) u‖ * ‖u‖ := h2
        _ ≤ ‖fderiv ℝ (fderiv ℝ f) (x + t • u)‖ * ‖u‖ * ‖u‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ ≤ M2 := by
            rw [hu, mul_one, mul_one, sb1_norm_fderiv_fderiv]; exact hM2 _
    have key := sb1_lk1d_first (φ := fun s : ℝ => f (x + s • u))
      (φ' := fun s => fderiv ℝ f (x + s • u) u) (φ'' := fun s => fderiv ℝ (fderiv ℝ f) (x + s • u) u u)
      (fun t => sb1_hasDerivAt_line x u t (hf1 _)) (fun t => sb1_hasDerivAt_line_clm x u u t (hf2 _))
      hh (fun t _ => hδ _) (fun t _ => hbd t)
    simpa using key
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  by_cases hv : v = 0
  · simp [hv]
  · have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hu : ‖(‖v‖⁻¹) • v‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn.ne']
    have := hunit _ hu
    rw [map_smul, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 hvn)] at this
    rw [Real.norm_eq_abs]
    have h3 := mul_le_mul_of_nonneg_left this hvn.le
    rw [← mul_assoc, mul_inv_cancel₀ hvn.ne', one_mul] at h3
    linarith

/-- derivative of the `n`-th diagonal derivative along a line. -/
theorem sb1_hasDerivAt_iter {f : Euc d → ℝ} (n : ℕ) (hf : ContDiff ℝ (n + 1) f) (x u : Euc d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n f (x + s • u) (fun _ => u))
      (iteratedFDeriv ℝ (n + 1) f (x + t • u) (fun _ => u)) t := by
  have hG : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
  have h1 : HasDerivAt (fun s : ℝ => x + s • u) u t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_add x
  have h4 := ((hG (x + t • u)).hasFDerivAt).continuousMultilinear_apply_const (fun _ : Fin n => u)
  have h5 := h4.comp_hasDerivAt t h1
  have e : iteratedFDeriv ℝ (n + 1) f (x + t • u) (fun _ => u) =
      (fderiv ℝ (iteratedFDeriv ℝ n f) (x + t • u)).flipMultilinear (fun _ : Fin n => u) u := by
    rw [iteratedFDeriv_succ_apply_left]; rfl
  rw [e]
  exact h5

theorem sb1_iter_apply_le {f : Euc d → ℝ} (n : ℕ) (y u : Euc d) (hu : ‖u‖ = 1) :
    |iteratedFDeriv ℝ n f y (fun _ => u)| ≤ ‖iteratedFDeriv ℝ n f y‖ := by
  have := (iteratedFDeriv ℝ n f y).le_opNorm (fun _ : Fin n => u)
  simpa [hu] using this

/-- the diagonal second derivative along a unit line: `|D²f(x)(u,u)| ≤ 4δ/h² + 3 M₃ h`. -/
theorem sb1_lk_second_diag {f : Euc d → ℝ} (hf : ContDiff ℝ 3 f) {δ M3 h : ℝ} (hh : 0 < h)
    (hδ : ∀ x, |f x| ≤ δ) (hM3 : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ M3) (x u : Euc d) (hu : ‖u‖ = 1) :
    |iteratedFDeriv ℝ 2 f x (fun _ => u)| ≤ 4 * δ / h ^ 2 + 3 * M3 * h := by
  have key := sb1_lk1d_second (φ := fun s : ℝ => iteratedFDeriv ℝ 0 f (x + s • u) (fun _ => u))
    (φ' := fun s => iteratedFDeriv ℝ 1 f (x + s • u) (fun _ => u))
    (φ'' := fun s => iteratedFDeriv ℝ 2 f (x + s • u) (fun _ => u))
    (φ''' := fun s => iteratedFDeriv ℝ 3 f (x + s • u) (fun _ => u)) (M3 := M3) (δ := δ)
    (fun t => sb1_hasDerivAt_iter 0 (hf.of_le (by norm_num)) x u t)
    (fun t => sb1_hasDerivAt_iter 1 (hf.of_le (by norm_num)) x u t)
    (fun t => sb1_hasDerivAt_iter 2 hf x u t) hh
    (fun t _ => by
      have : iteratedFDeriv ℝ 0 f (x + t • u) (fun _ => u) = f (x + t • u) := iteratedFDeriv_zero_apply (fun _ => u)
      simp only [this]; exact hδ _)
    (fun t _ => (sb1_iter_apply_le 3 _ u hu).trans (hM3 _))
  simpa using key

/-- the second derivative operator: `‖D²f‖ ≤ 4δ/h² + 3 M₃ h` (polarisation of the diagonal bound). -/
theorem sb1_lk_second {f : Euc d → ℝ} (hf : ContDiff ℝ 3 f) {δ M3 h : ℝ} (hh : 0 < h)
    (hδ : ∀ x, |f x| ≤ δ) (hM3 : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ M3) (x : Euc d) :
    ‖iteratedFDeriv ℝ 2 f x‖ ≤ 4 * δ / h ^ 2 + 3 * M3 * h := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ x)
  have hM30 : 0 ≤ M3 := (norm_nonneg _).trans (hM3 x)
  set c : ℝ := 4 * δ / h ^ 2 + 3 * M3 * h with hc
  have hc0 : 0 ≤ c := by positivity
  have hsymm : ∀ v w : Euc d, fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v := by
    have := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]; norm_num)
    exact fun v w => this v w
  have hdiag : ∀ u : Euc d, |fderiv ℝ (fderiv ℝ f) x u u| ≤ c * ‖u‖ ^ 2 := by
    intro u
    by_cases hu : u = 0
    · simp [hu]
    · have hun : 0 < ‖u‖ := norm_pos_iff.2 hu
      have hu1 : ‖(‖u‖⁻¹) • u‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hun.ne']
      have := sb1_lk_second_diag hf hh hδ hM3 x _ hu1
      rw [iteratedFDeriv_two_apply] at this
      simp only [map_smul, smul_apply, smul_eq_mul, abs_mul,
        abs_of_pos (inv_pos.2 hun)] at this
      have h2 := mul_le_mul_of_nonneg_left this (sq_nonneg ‖u‖)
      have e : ‖u‖ ^ 2 * (‖u‖⁻¹ * (‖u‖⁻¹ * |fderiv ℝ (fderiv ℝ f) x u u|)) =
          |fderiv ℝ (fderiv ℝ f) x u u| := by field_simp
      rw [e] at h2
      linarith
  have hpol : ∀ v w : Euc d, |fderiv ℝ (fderiv ℝ f) x v w| ≤ c / 2 * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
    intro v w
    have e : fderiv ℝ (fderiv ℝ f) x v w = (fderiv ℝ (fderiv ℝ f) x (v + w) (v + w) -
        fderiv ℝ (fderiv ℝ f) x (v - w) (v - w)) / 4 := by
      simp only [map_add, map_sub, add_apply, sub_apply]
      rw [hsymm w v]; ring
    have h1 := hdiag (v + w)
    have h2 := hdiag (v - w)
    have hpar : ‖v + w‖ ^ 2 + ‖v - w‖ ^ 2 = 2 * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
      have := parallelogram_law_with_norm ℝ v w
      linarith
    rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    calc |fderiv ℝ (fderiv ℝ f) x (v + w) (v + w) - fderiv ℝ (fderiv ℝ f) x (v - w) (v - w)|
        ≤ _ := abs_sub _ _
      _ ≤ c * ‖v + w‖ ^ 2 + c * ‖v - w‖ ^ 2 := add_le_add h1 h2
      _ = c * (‖v + w‖ ^ 2 + ‖v - w‖ ^ 2) := by ring
      _ = c / 2 * (‖v‖ ^ 2 + ‖w‖ ^ 2) * 4 := by rw [hpar]; ring
  rw [← sb1_norm_fderiv_fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ hc0 fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [Real.norm_eq_abs]
  by_cases hv : v = 0
  · simp [hv]
  by_cases hw : w = 0
  · simp [hw]
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have := hpol ((‖v‖⁻¹) • v) ((‖w‖⁻¹) • w)
  have hv1 : ‖(‖v‖⁻¹) • v‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn.ne']
  have hw1 : ‖(‖w‖⁻¹) • w‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwn.ne']
  rw [hv1, hw1] at this
  simp only [map_smul, smul_apply, smul_eq_mul, abs_mul,
    abs_of_pos (inv_pos.2 hvn), abs_of_pos (inv_pos.2 hwn)] at this
  have h2 := mul_le_mul_of_nonneg_left this (mul_pos hvn hwn).le
  have e : ‖v‖ * ‖w‖ * (‖w‖⁻¹ * (‖v‖⁻¹ * |fderiv ℝ (fderiv ℝ f) x v w|)) = |fderiv ℝ (fderiv ℝ f) x v w| := by
    field_simp
  rw [e] at h2
  nlinarith

end HRS.MS.MfeConf
