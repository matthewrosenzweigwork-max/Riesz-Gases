import HRS.Commutator.Whole.XLIAux12

/-!
# X-LI part 13: dyadic projections on Schwartz functions and Fourier supports of products
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the cutoff as a complex symbol -/
def cutC (η : 𝔼) : ℂ := ((cut η : ℝ) : ℂ)

lemma cutC_contDiff : ContDiff ℝ ∞ (cutC : 𝔼 → ℂ) :=
  Complex.ofRealCLM.contDiff.comp cut_contDiff

lemma cutC_eq_zero_of_ge {η : 𝔼} (h : 2 ≤ ‖η‖) : cutC η = 0 := by
  unfold cutC; rw [cut_zero h]; simp

lemma cutC_eq_one_of_le {η : 𝔼} (h : ‖η‖ ≤ 1) : cutC η = 1 := by
  unfold cutC; rw [cut_one h]; simp

lemma cutC_cs : HasCompactSupport (cutC : 𝔼 → ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : 𝔼) 2) ?_
  intro η hη
  by_contra h
  exact hη (cutC_eq_zero_of_ge (by
    rw [mem_closedBall_zero_iff, not_le] at h; exact h.le))

lemma norm_cutC_le_one (η : 𝔼) : ‖cutC η‖ ≤ 1 := by
  unfold cutC
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [cut_nonneg η, cut_le_one η]

lemma rho_eq_cutC (η : 𝔼) : rho η = cutC η - cutC ((2 : ℝ) • η) := by
  unfold rho cutC; push_cast; ring

/-- `Δ_j f` as a Schwartz function -/
def Dm (j : ℤ) (f : SchwartzMap 𝔼 ℂ) : SchwartzMap 𝔼 ℂ :=
  mulS (fun ξ => rho (((2 : ℝ) ^ j)⁻¹ • ξ)) (temperate_symbol rho_contDiff rho_cs j) f

/-- `P_m f` (low-pass) as a Schwartz function -/
def Pm (m : ℤ) (f : SchwartzMap 𝔼 ℂ) : SchwartzMap 𝔼 ℂ :=
  mulS (fun ξ => cutC (((2 : ℝ) ^ m)⁻¹ • ξ)) (temperate_symbol cutC_contDiff cutC_cs m) f

lemma cv_rho_eq_Dm (j : ℤ) (f : SchwartzMap 𝔼 ℂ) : cv (symK rho j) ⇑f = ⇑(Dm j f) :=
  cv_symK_eq_mulS rho_contDiff rho_cs f j

lemma cv_cut_eq_Pm (m : ℤ) (f : SchwartzMap 𝔼 ℂ) : cv (symK cutC m) ⇑f = ⇑(Pm m f) :=
  cv_symK_eq_mulS cutC_contDiff cutC_cs f m

lemma fourier_Dm (j : ℤ) (f : SchwartzMap 𝔼 ℂ) (ξ : 𝔼) :
    𝓕 (⇑(Dm j f)) ξ = rho (((2 : ℝ) ^ j)⁻¹ • ξ) * 𝓕 (⇑f) ξ :=
  fourier_mulS _ _ f ξ

lemma fourier_Pm (m : ℤ) (f : SchwartzMap 𝔼 ℂ) (ξ : 𝔼) :
    𝓕 (⇑(Pm m f)) ξ = cutC (((2 : ℝ) ^ m)⁻¹ • ξ) * 𝓕 (⇑f) ξ :=
  fourier_mulS _ _ f ξ

lemma two_zpow_sub_one (m : ℤ) : (2 : ℝ) ^ (m - 1) = (2 : ℝ) ^ m / 2 := by
  rw [zpow_sub₀ (by norm_num)]; simp

lemma two_zpow_add_one (m : ℤ) : (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ m * 2 := by
  rw [zpow_add₀ (by norm_num)]; simp

lemma inv_two_zpow_sub_one (m : ℤ) : ((2 : ℝ) ^ (m - 1))⁻¹ = 2 * ((2 : ℝ) ^ m)⁻¹ := by
  rw [two_zpow_sub_one]; field_simp

/-- `P_m = P_{m-1} + Δ_m` -/
lemma Pm_succ (m : ℤ) (f : SchwartzMap 𝔼 ℂ) : Pm m f = Pm (m - 1) f + Dm m f := by
  have hT1 := temperate_symbol (d := d) cutC_contDiff cutC_cs (m - 1)
  have hT2 := temperate_symbol (d := d) rho_contDiff rho_cs m
  have hsym : (fun ξ : 𝔼 => cutC (((2 : ℝ) ^ m)⁻¹ • ξ)) =
      fun ξ : 𝔼 => cutC (((2 : ℝ) ^ (m - 1))⁻¹ • ξ) + rho (((2 : ℝ) ^ m)⁻¹ • ξ) := by
    funext ξ
    have h2 : (2 : ℝ) • (((2 : ℝ) ^ m)⁻¹ • ξ) = ((2 : ℝ) ^ (m - 1))⁻¹ • ξ := by
      rw [smul_smul, inv_two_zpow_sub_one]
    rw [rho_eq_cutC, h2]; ring
  calc Pm m f = mulS (fun ξ : 𝔼 => cutC (((2 : ℝ) ^ (m - 1))⁻¹ • ξ) + rho (((2 : ℝ) ^ m)⁻¹ • ξ))
        (hT1.add hT2) f := mulS_congr hsym _ _ f
    _ = Pm (m - 1) f + Dm m f := mulS_add _ _ hT1 hT2 (hT1.add hT2) f

/-! ### Fourier supports -/

/-- the Fourier transform of `u` is supported in the open annulus `a < |η| < b` -/
def FSupp (u : SchwartzMap 𝔼 ℂ) (a b : ℝ) : Prop :=
  ∀ η : 𝔼, 𝓕 (⇑u) η ≠ 0 → a < ‖η‖ ∧ ‖η‖ < b

lemma norm_smul_inv_zpow (j : ℤ) (ξ : 𝔼) : ‖((2 : ℝ) ^ j)⁻¹ • ξ‖ = ((2 : ℝ) ^ j)⁻¹ * ‖ξ‖ := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (zpow_pos (by norm_num) j).le)]

lemma rho_ne_zero_bounds {η : 𝔼} (h : rho η ≠ 0) : 1 / 2 < ‖η‖ ∧ ‖η‖ < 2 := by
  constructor
  · by_contra hc; exact h (rho_eq_zero_of_le (not_lt.1 hc))
  · by_contra hc; exact h (rho_eq_zero_of_ge (not_lt.1 hc))

lemma FSupp_Dm (j : ℤ) (f : SchwartzMap 𝔼 ℂ) : FSupp (Dm j f) ((2 : ℝ) ^ j / 2) ((2 : ℝ) ^ j * 2) := by
  intro η hη
  rw [fourier_Dm] at hη
  have h1 : rho (((2 : ℝ) ^ j)⁻¹ • η) ≠ 0 := left_ne_zero_of_mul hη
  obtain ⟨h2, h3⟩ := rho_ne_zero_bounds h1
  rw [norm_smul_inv_zpow] at h2 h3
  have hs : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  constructor
  · rw [← div_eq_inv_mul, lt_div_iff₀ hs] at h2; linarith
  · rw [← div_eq_inv_mul, div_lt_iff₀ hs] at h3; linarith

lemma FSupp_Pm (m : ℤ) (f : SchwartzMap 𝔼 ℂ) : FSupp (Pm m f) (-1) ((2 : ℝ) ^ m * 2) := by
  intro η hη
  rw [fourier_Pm] at hη
  have h1 : cutC (((2 : ℝ) ^ m)⁻¹ • η) ≠ 0 := left_ne_zero_of_mul hη
  have hs : 0 < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
  refine ⟨by linarith [norm_nonneg η], ?_⟩
  by_contra hc
  rw [not_lt] at hc
  apply h1
  apply cutC_eq_zero_of_ge
  rw [norm_smul_inv_zpow, ← div_eq_inv_mul, le_div_iff₀ hs]
  linarith

lemma FSupp_prod {u v : SchwartzMap 𝔼 ℂ} {a₁ b₁ a₂ b₂ : ℝ} (hu : FSupp u a₁ b₁) (hv : FSupp v a₂ b₂) :
    FSupp (prodS u v) (max (a₁ - b₂) (a₂ - b₁)) (b₁ + b₂) := by
  intro ξ hξ
  have e : (⇑(prodS u v)) = fun x => u x * v x := funext fun x => prodS_apply u v x
  rw [e, fourier_mul_eq] at hξ
  obtain ⟨η, hη⟩ : ∃ η, 𝓕 (⇑u) η * 𝓕 (⇑v) (ξ - η) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hξ (integral_eq_zero_of_ae (Eventually.of_forall fun η => hcon η))
  obtain ⟨h1, h2⟩ := hu η (left_ne_zero_of_mul hη)
  obtain ⟨h3, h4⟩ := hv (ξ - η) (right_ne_zero_of_mul hη)
  have t1 : ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ := by
    calc ‖ξ‖ = ‖η + (ξ - η)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have t2 : ‖η‖ ≤ ‖ξ‖ + ‖ξ - η‖ := by
    calc ‖η‖ = ‖ξ - (ξ - η)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have t3 : ‖ξ - η‖ ≤ ‖ξ‖ + ‖η‖ := norm_sub_le ξ η
  refine ⟨max_lt (by linarith) (by linarith), by linarith⟩

/-- the multiplier `τ` kills `w` if its support avoids the Fourier support of `w` -/
lemma mulS_FSupp_zero (τ : 𝔼 → ℂ) (hτ : τ.HasTemperateGrowth) (w : SchwartzMap 𝔼 ℂ) {a b : ℝ}
    (hw : FSupp w a b) (hτ0 : ∀ ξ : 𝔼, τ ξ ≠ 0 → ¬ (a < ‖ξ‖ ∧ ‖ξ‖ < b)) (x : 𝔼) :
    mulS τ hτ w x = 0 := by
  rw [mulS_apply]
  have : (fun ξ => τ ξ * 𝓕 (⇑w) ξ) = fun _ => 0 := by
    funext ξ
    by_cases h : τ ξ = 0
    · rw [h, zero_mul]
    · have : 𝓕 (⇑w) ξ = 0 := by
        by_contra hne
        exact hτ0 ξ h (hw ξ hne)
      rw [this, mul_zero]
  rw [this, Real.fourierInv_eq']
  simp

/-! ### Vanishing of the dyadic output pieces -/

lemma symR_ne_zero_bounds {s : ℝ} {k : ℤ} {ξ : 𝔼} (h : symR s k ξ ≠ 0) :
    (2 : ℝ) ^ k / 2 < ‖ξ‖ ∧ ‖ξ‖ < (2 : ℝ) ^ k * 2 := by
  have h1 : rho (((2 : ℝ) ^ k)⁻¹ • ξ) ≠ 0 := right_ne_zero_of_mul h
  obtain ⟨h2, h3⟩ := rho_ne_zero_bounds h1
  rw [norm_smul_inv_zpow] at h2 h3
  have hs : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  constructor
  · rw [← div_eq_inv_mul, lt_div_iff₀ hs] at h2; linarith
  · rw [← div_eq_inv_mul, div_lt_iff₀ hs] at h3; linarith

lemma symR_vanish {s : ℝ} (k : ℤ) (w : SchwartzMap 𝔼 ℂ) {a b : ℝ} (hw : FSupp w a b)
    (h : b ≤ (2 : ℝ) ^ k / 2 ∨ (2 : ℝ) ^ k * 2 ≤ a) (x : 𝔼) :
    mulS (symR s k) (symR_temperate s k) w x = 0 := by
  refine mulS_FSupp_zero _ _ w hw (fun ξ hξ hc => ?_) x
  obtain ⟨h1, h2⟩ := symR_ne_zero_bounds hξ
  rcases h with h | h
  · linarith [hc.2]
  · linarith [hc.1]

lemma two_zpow_add_three (m : ℤ) : (2 : ℝ) ^ (m + 3) = 8 * (2 : ℝ) ^ m := by
  rw [zpow_add₀ (by norm_num)]; norm_num; ring

lemma two_zpow_add_two (m : ℤ) : (2 : ℝ) ^ (m + 2) = 4 * (2 : ℝ) ^ m := by
  rw [zpow_add₀ (by norm_num)]; norm_num; ring

lemma two_zpow_add_five (m : ℤ) : (2 : ℝ) ^ (m + 5) = 32 * (2 : ℝ) ^ m := by
  rw [zpow_add₀ (by norm_num)]; norm_num; ring

lemma two_zpow_sub_three (m : ℤ) : (2 : ℝ) ^ (m - 3) = (2 : ℝ) ^ m / 8 := by
  rw [zpow_sub₀ (by norm_num)]; norm_num

lemma two_zpow_mono {a b : ℤ} (h : a ≤ b) : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
  zpow_le_zpow_right₀ (by norm_num) h

/-- class A: `Δ_m f · P_{m-3} g` has output frequencies only at `|k - m| ≤ 2` -/
lemma classA_vanish {s : ℝ} (m k : ℤ) (f g : SchwartzMap 𝔼 ℂ) (hk : m + 3 ≤ k ∨ k ≤ m - 3) (x : 𝔼) :
    mulS (symR s k) (symR_temperate s k) (prodS (Dm m f) (Pm (m - 3) g)) x = 0 := by
  have hs : 0 < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hP := FSupp_prod (FSupp_Dm m f) (FSupp_Pm (m - 3) g)
  refine symR_vanish k _ hP ?_ x
  rcases hk with hk | hk
  · left
    have := two_zpow_mono hk
    rw [two_zpow_add_three] at this
    rw [two_zpow_sub_three]
    linarith
  · right
    have := two_zpow_mono hk
    rw [two_zpow_sub_three] at this
    refine le_max_of_le_left ?_
    rw [two_zpow_sub_three]
    linarith

/-- class B: `P_{m-3} f · Δ_m g` -/
lemma classB_vanish {s : ℝ} (m k : ℤ) (f g : SchwartzMap 𝔼 ℂ) (hk : m + 3 ≤ k ∨ k ≤ m - 3) (x : 𝔼) :
    mulS (symR s k) (symR_temperate s k) (prodS (Pm (m - 3) f) (Dm m g)) x = 0 := by
  have hs : 0 < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hP := FSupp_prod (FSupp_Pm (m - 3) f) (FSupp_Dm m g)
  refine symR_vanish k _ hP ?_ x
  rcases hk with hk | hk
  · left
    have := two_zpow_mono hk
    rw [two_zpow_add_three] at this
    rw [two_zpow_sub_three]
    linarith
  · right
    have := two_zpow_mono hk
    rw [two_zpow_sub_three] at this
    refine le_max_of_le_right ?_
    rw [two_zpow_sub_three]
    linarith

/-- class C: `Δ_{l₁} f · Δ_{l₂} g` with `l₁, l₂ ≤ j` has output frequencies only at `k ≤ j + 2` -/
lemma classC_vanish {s : ℝ} (j k l₁ l₂ : ℤ) (h1 : l₁ ≤ j) (h2 : l₂ ≤ j) (f g : SchwartzMap 𝔼 ℂ)
    (hk : j + 3 ≤ k) (x : 𝔼) :
    mulS (symR s k) (symR_temperate s k) (prodS (Dm l₁ f) (Dm l₂ g)) x = 0 := by
  have hs : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hP := FSupp_prod (FSupp_Dm l₁ f) (FSupp_Dm l₂ g)
  refine symR_vanish k _ hP (Or.inl ?_) x
  have h3 := two_zpow_mono hk
  rw [two_zpow_add_three] at h3
  have h4 : (2 : ℝ) ^ l₁ ≤ (2 : ℝ) ^ j := two_zpow_mono h1
  have h5 : (2 : ℝ) ^ l₂ ≤ (2 : ℝ) ^ j := two_zpow_mono h2
  linarith

end HRS.Commutator.Whole.XLI
