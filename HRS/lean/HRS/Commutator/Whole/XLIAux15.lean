import HRS.Commutator.Whole.XLIAux14

/-!
# X-LI part 15: pointwise estimates of the dyadic output pieces of a product
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### Elementary properties of `CvP` -/

lemma CvP_mono (j : ℤ) {H H' : 𝔼 → ℝ≥0∞} (h : ∀ y, H y ≤ H' y) (x : 𝔼) :
    CvP j H x ≤ CvP j H' x :=
  lintegral_mono fun y => mul_le_mul_right (h _) _

lemma CvP_const_mul (j : ℤ) {a : ℝ≥0∞} (ha : a ≠ ⊤) (H : 𝔼 → ℝ≥0∞) (x : 𝔼) :
    CvP j (fun y => a * H y) x = a * CvP j H x := by
  unfold CvP
  have : ∀ y, Phi j y * (a * H (x - y)) = a * (Phi j y * H (x - y)) := fun y => by ring
  simp_rw [this]
  exact lintegral_const_mul' _ _ ha

lemma CvP_tsum (j : ℤ) {ι : Type*} [Countable ι] {H : ι → 𝔼 → ℝ≥0∞} (hH : ∀ i, Measurable (H i))
    (x : 𝔼) : CvP j (fun y => ∑' i, H i y) x = ∑' i, CvP j (H i) x := by
  unfold CvP
  simp_rw [← ENNReal.tsum_mul_left]
  rw [lintegral_tsum]
  intro i
  exact ((Phi_measurable j).mul ((hH i).comp (measurable_const.sub measurable_id))).aemeasurable

lemma CvP_add (j : ℤ) {H H' : 𝔼 → ℝ≥0∞} (hH : Measurable H) (hH' : Measurable H') (x : 𝔼) :
    CvP j (fun y => H y + H' y) x = CvP j H x + CvP j H' x := by
  unfold CvP
  simp_rw [mul_add]
  rw [lintegral_add_left]
  exact (Phi_measurable j).mul (hH.comp (measurable_const.sub measurable_id))

/-! ### Linearity of the multiplier in the Schwartz function -/

lemma mulS_add_phi (τ : 𝔼 → ℂ) (hτ : τ.HasTemperateGrowth) (φ ψ : SchwartzMap 𝔼 ℂ) :
    mulS τ hτ (φ + ψ) = mulS τ hτ φ + mulS τ hτ ψ := by
  unfold mulS
  rw [FourierAdd.fourier_add, map_add, FourierInvAdd.fourierInv_add]

lemma cv_dK_Ths_add (s : ℝ) {j : ℤ} (hj : -2 ≤ j) (φ ψ : SchwartzMap 𝔼 ℂ) (x : 𝔼) :
    cv (dK (Ths s : ℤ → 𝔼 → ℂ) j) ⇑(φ + ψ) x =
      cv (dK (Ths s : ℤ → 𝔼 → ℂ) j) ⇑φ x + cv (dK (Ths s : ℤ → 𝔼 → ℂ) j) ⇑ψ x := by
  rw [cv_dK_Ths_apply s hj, cv_dK_Ths_apply s hj, cv_dK_Ths_apply s hj, mulS_add_phi]
  simp only [SchwartzMap.add_apply]
  ring

/-! ### The Bessel pieces of a Schwartz function -/

section Pieces

variable (α : ℝ)

/-- the Bessel derivative `J^α f` as a Schwartz function -/
def Fm (f : SchwartzMap 𝔼 ℂ) : SchwartzMap 𝔼 ℂ := mulS (bsymX α) (bsymX_temperate α) f

/-- the Littlewood–Paley piece `Θ^{-α}_j ⋆ J^α f` (equal to `2^{jα} Δ_j f`) -/
def Fj (f : SchwartzMap 𝔼 ℂ) (j : ℤ) : 𝔼 → ℂ :=
  cv (dK (Ths (-α) : ℤ → 𝔼 → ℂ) j) ⇑(Fm α f)

lemma Fj_meas (f : SchwartzMap 𝔼 ℂ) (j : ℤ) : Measurable (Fj α f j) :=
  measurable_cv (dK_continuous (symFam_Ths (d := d) (-α)) j).measurable
    (Fm α f).continuous.measurable

/-- scale-`j` average of `|ψ|` -/
def Gc (ψ : SchwartzMap 𝔼 ℂ) (j : ℤ) : 𝔼 → ℝ≥0∞ := CvP j (fun z => ‖ψ z‖ₑ)

lemma Gc_meas (ψ : SchwartzMap 𝔼 ℂ) (j : ℤ) : Measurable (Gc ψ j) :=
  CvP_measurable j ψ.continuous.measurable.enorm

/-- the sum of four consecutive scale averages -/
def Gs (ψ : SchwartzMap 𝔼 ℂ) (m : ℤ) (y : 𝔼) : ℝ≥0∞ :=
  Gc ψ (m + -3) y + Gc ψ (m + -2) y + Gc ψ (m + -1) y + Gc ψ m y

lemma Gs_meas (ψ : SchwartzMap 𝔼 ℂ) (m : ℤ) : Measurable (Gs ψ m) :=
  (((Gc_meas ψ _).add (Gc_meas ψ _)).add (Gc_meas ψ _)).add (Gc_meas ψ _)

/-- the basic quantity: `CvP_k (|F_m| · Gs_m)` -/
def XX (φ ψ : SchwartzMap 𝔼 ℂ) (k m : ℤ) (x : 𝔼) : ℝ≥0∞ :=
  CvP k (fun y => ‖Fj α φ m y‖ₑ * Gs ψ m y) x

lemma enorm_Dm_eq {j : ℤ} (hj : -2 ≤ j) (f : SchwartzMap 𝔼 ℂ) (y : 𝔼) :
    ‖Dm j f y‖ₑ = ENNReal.ofReal (((2 : ℝ) ^ j) ^ (-α)) * ‖Fj α f j y‖ₑ := by
  have h := delta_eq_bessel α hj f y
  have e := congrFun (cv_rho_eq_Dm j f) y
  have hr : ‖((((2 : ℝ) ^ j) ^ (-α) : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (((2 : ℝ) ^ j) ^ (-α)) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg
      (Real.rpow_nonneg (zpow_pos (by norm_num) j).le _)]
  rw [← e, h, enorm_mul, hr]
  rfl

lemma enorm_Dm_le {A : ℝ≥0∞} {j : ℤ} (hA : DecK A j (symK (rho : 𝔼 → ℂ) j)) (g : SchwartzMap 𝔼 ℂ) (y : 𝔼) :
    ‖Dm j g y‖ₑ ≤ A * Gc g j y := by
  have e := congrFun (cv_rho_eq_Dm j g) y
  rw [← e]
  exact enorm_cv_le_CvP hA g.continuous.measurable y

lemma enorm_Pm_le {A : ℝ≥0∞} {j : ℤ} (hA : DecK A j (symK (cutC : 𝔼 → ℂ) j)) (g : SchwartzMap 𝔼 ℂ) (y : 𝔼) :
    ‖Pm j g y‖ₑ ≤ A * Gc g j y := by
  have e := congrFun (cv_cut_eq_Pm j g) y
  rw [← e]
  exact enorm_cv_le_CvP hA g.continuous.measurable y

/-- the bound for a product term -/
lemma term_bound {k : ℤ} {AΘ : ℝ≥0∞} (hdec : DecK AΘ k (dK (Ths α : ℤ → 𝔼 → ℂ) k))
    (u v : SchwartzMap 𝔼 ℂ) {a b : ℝ≥0∞} (H₁ H₂ : 𝔼 → ℝ≥0∞)
    (hu : ∀ y, ‖u y‖ₑ ≤ a * H₁ y) (hv : ∀ y, ‖v y‖ₑ ≤ b * H₂ y) (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (x : 𝔼) :
    ‖cv (dK (Ths α : ℤ → 𝔼 → ℂ) k) ⇑(prodS u v) x‖ₑ ≤
      AΘ * ((a * b) * CvP k (fun y => H₁ y * H₂ y) x) := by
  have h1 := enorm_cv_le_CvP hdec (prodS u v).continuous.measurable x
  refine h1.trans ?_
  refine mul_le_mul_right ?_ _
  have h2 : CvP k (fun y => ‖(prodS u v) y‖ₑ) x ≤ CvP k (fun y => (a * b) * (H₁ y * H₂ y)) x := by
    refine CvP_mono k (fun y => ?_) x
    rw [prodS_apply, enorm_mul]
    calc ‖u y‖ₑ * ‖v y‖ₑ ≤ (a * H₁ y) * (b * H₂ y) := mul_le_mul' (hu y) (hv y)
      _ = (a * b) * (H₁ y * H₂ y) := by ring
  refine h2.trans (le_of_eq ?_)
  exact CvP_const_mul k (ENNReal.mul_ne_top ha hb) _ x

end Pieces

end HRS.Commutator.Whole.XLI
