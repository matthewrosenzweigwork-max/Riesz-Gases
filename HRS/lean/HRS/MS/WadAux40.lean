import HRS.MS.WadAux39

/-!
# S8.3, packet D7 (Route A), part 5: the value `U_t φ = w_0 - μ(w_0) + μ(φ)` and its Lipschitz estimate

`s85_V ρβ w φ x = w_0(x) - μ(w_0) + μ(φ)`; `s85_V_bound`: the value depends Lipschitz-continuously on the datum
in the weighted sup norm (uniformly for horizons `t ∈ [0,T]`), for all frozen classical solutions.
`s85_Ucc` is the value of the `propagatorW`-chosen solution, `s85_Ucc_eq` identifies it with any classical
solution (uniqueness).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- `w_0(x) - μ(w_0) + μ(φ)`. -/
def s85_V (ρβ : Euc d → ℝ) (w : ℝ → Euc d → ℝ) (φ : Euc d → ℝ) (x : Euc d) : ℝ :=
  w 0 x - ∫ z, w 0 z ∂(HRS.Whole.withDensityReal ρβ) + HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) φ

/-- Test functions: `C_c^∞`. -/
def S85Cc (φ : Euc d → ℝ) : Prop := ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

theorem s85_int_bdd {μ : Measure (Euc d)} [IsFiniteMeasure μ] {f : Euc d → ℝ} (hf : Continuous f) {B : ℝ}
    (hb : ∀ x, |f x| ≤ B) : Integrable f μ :=
  Integrable.mono' (integrable_const B) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)

theorem s85_cl_int (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    {w : ℝ → Euc d → ℝ} (hw : IsClassicalAdjointW (critCoeff d a β ρβ) t φ w) :
    Integrable (w 0) (HRS.Whole.withDensityReal ρβ) ∧ Integrable φ (HRS.Whole.withDensityReal ρβ) := by
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hρ.1.1
  obtain ⟨B0, BG, hB0, hBG0, hb0, hbG, hwc, hGc⟩ := s85_cl_facts hd ha hβ hρ hw
  refine ⟨s85_int_bdd (hw.c2 0 ⟨le_rfl, ht⟩).continuous (hb0 0 ⟨le_rfl, ht⟩), ?_⟩
  have : φ = w t := hw.terminal.symm
  rw [this]
  exact s85_int_bdd (hw.c2 t ⟨ht, le_rfl⟩).continuous (hb0 t ⟨ht, le_rfl⟩)

/-- Abstract core of the Lipschitz estimate of the value. -/
theorem s85_V_core {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {K Φ M : ℝ} (hK0 : 0 ≤ K) (hΦ0 : 0 ≤ Φ)
    (hM : 0 ≤ M) (hjint : Integrable (fun z : Euc d => jbracket z ^ M) μ) {u₁ u₂ φ₁ φ₂ : Euc d → ℝ}
    (iu1 : Integrable u₁ μ) (iu2 : Integrable u₂ μ) (iφ1 : Integrable φ₁ μ) (iφ2 : Integrable φ₂ μ)
    (hb : ∀ y, |u₁ y - u₂ y| ≤ K * Φ * jbracket y ^ M) (hφb : ∀ y, |φ₁ y - φ₂ y| ≤ Φ * jbracket y ^ M)
    (x : Euc d) :
    |(u₁ x - ∫ z, u₁ z ∂μ + ∫ z, φ₁ z ∂μ) - (u₂ x - ∫ z, u₂ z ∂μ + ∫ z, φ₂ z ∂μ)| ≤
      (1 + K + K * (∫ z, jbracket z ^ M ∂μ) + ∫ z, jbracket z ^ M ∂μ) * Φ * jbracket x ^ M := by
  have hmM0 : 0 ≤ ∫ z, jbracket z ^ M ∂μ :=
    integral_nonneg fun z => Real.rpow_nonneg (s83_jb_pos z).le _
  set mM : ℝ := ∫ z, jbracket z ^ M ∂μ with hmM
  have hJ : 1 ≤ jbracket x ^ M := Real.one_le_rpow (s83_one_le_jb x) hM
  have hb1 : |∫ z, (u₁ z - u₂ z) ∂μ| ≤ K * Φ * mM := by
    have := s85_abs_integral_le (μ := μ) (h := fun z => u₁ z - u₂ z)
      (bd := fun z => K * Φ * jbracket z ^ M) (hjint.const_mul (K * Φ)) hb
    rwa [integral_const_mul] at this
  have hb2 : |∫ z, (φ₁ z - φ₂ z) ∂μ| ≤ Φ * mM := by
    have := s85_abs_integral_le (μ := μ) (h := fun z => φ₁ z - φ₂ z)
      (bd := fun z => Φ * jbracket z ^ M) (hjint.const_mul Φ) hφb
    rwa [integral_const_mul] at this
  have e1 : ∫ z, (u₁ z - u₂ z) ∂μ = ∫ z, u₁ z ∂μ - ∫ z, u₂ z ∂μ := integral_sub iu1 iu2
  have e2 : ∫ z, (φ₁ z - φ₂ z) ∂μ = ∫ z, φ₁ z ∂μ - ∫ z, φ₂ z ∂μ := integral_sub iφ1 iφ2
  have key : (u₁ x - ∫ z, u₁ z ∂μ + ∫ z, φ₁ z ∂μ) - (u₂ x - ∫ z, u₂ z ∂μ + ∫ z, φ₂ z ∂μ) =
      (u₁ x - u₂ x) + (-∫ z, (u₁ z - u₂ z) ∂μ) + ∫ z, (φ₁ z - φ₂ z) ∂μ := by
    rw [e1, e2]; ring
  rw [key]
  have habs := abs_add_three (u₁ x - u₂ x) (-∫ z, (u₁ z - u₂ z) ∂μ) (∫ z, (φ₁ z - φ₂ z) ∂μ)
  rw [abs_neg] at habs
  have hx := hb x
  have h5 : 0 ≤ K * Φ * mM := mul_nonneg (mul_nonneg hK0 hΦ0) hmM0
  have h6 : 0 ≤ Φ * mM := mul_nonneg hΦ0 hmM0
  have h8 : 0 ≤ K * Φ * mM * (jbracket x ^ M - 1) := mul_nonneg h5 (by linarith)
  have h9 : 0 ≤ Φ * mM * (jbracket x ^ M - 1) := mul_nonneg h6 (by linarith)
  have h10 : 0 ≤ Φ * jbracket x ^ M := mul_nonneg hΦ0 (by linarith)
  have fin : K * Φ * jbracket x ^ M + K * Φ * mM + Φ * mM ≤
      (1 + K + K * mM + mM) * Φ * jbracket x ^ M := by
    nlinarith [h8, h9, h10]
  linarith [habs, hx, hb1, hb2, fin]

/-- **Lipschitz dependence of the value on the datum.** -/
theorem s85_V_bound (hd : 2 ≤ d) {a β T M : ℝ} (ha : 0 < a) (hβ : 0 < β) (hT : 0 < T) (hM : 0 ≤ M)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t Φ : ℝ} {φ₁ φ₂ : Euc d → ℝ} {w₁ w₂ : ℝ → Euc d → ℝ}, 0 ≤ t → t ≤ T →
      IsClassicalAdjointW (critCoeff d a β ρβ) t φ₁ w₁ → IsClassicalAdjointW (critCoeff d a β ρβ) t φ₂ w₂ →
      Wt M Φ (fun y => φ₁ y - φ₂ y) → ∀ x : Euc d,
        |s85_V ρβ w₁ φ₁ x - s85_V ρβ w₂ φ₂ x| ≤ K * Φ * jbracket x ^ M := by
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hP
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  obtain ⟨K, hK0, hK⟩ := s85_apriori_sub_classical hd ha hβ hT hM hρ
  have hjint : Integrable (fun z : Euc d => jbracket z ^ M) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hg hM
  have hmM0 : 0 ≤ ∫ z, jbracket z ^ M ∂(HRS.Whole.withDensityReal ρβ) :=
    integral_nonneg fun z => Real.rpow_nonneg (s83_jb_pos z).le _
  refine ⟨1 + max K 1 + max K 1 * (∫ z, jbracket z ^ M ∂(HRS.Whole.withDensityReal ρβ)) +
    ∫ z, jbracket z ^ M ∂(HRS.Whole.withDensityReal ρβ), by positivity, ?_⟩
  intro t Φ φ₁ φ₂ w₁ w₂ ht htT h₁ h₂ hΦ x
  have hΦ0 : 0 ≤ Φ := hΦ.nonneg
  obtain ⟨i1, iφ1⟩ := s85_cl_int hd ha hβ hρ ht h₁
  obtain ⟨i2, iφ2⟩ := s85_cl_int hd ha hβ hρ ht h₂
  have hφb : ∀ y, |φ₁ y - φ₂ y| ≤ Φ * jbracket y ^ M := fun y => by
    have := hΦ y; rwa [Real.norm_eq_abs] at this
  have hJ1 : ∀ y : Euc d, 0 ≤ Φ * jbracket y ^ M := fun y =>
    mul_nonneg hΦ0 (Real.rpow_nonneg (s83_jb_pos y).le _)
  have hb : ∀ y, |w₁ 0 y - w₂ 0 y| ≤ max K 1 * Φ * jbracket y ^ M := by
    rcases ht.eq_or_lt with h0 | hpos
    · subst h0
      intro y
      rw [h₁.terminal, h₂.terminal]
      have := hφb y
      have h2 : Φ * jbracket y ^ M ≤ max K 1 * (Φ * jbracket y ^ M) :=
        le_mul_of_one_le_left (hJ1 y) (le_max_right _ _)
      calc |φ₁ y - φ₂ y| ≤ Φ * jbracket y ^ M := this
        _ ≤ max K 1 * (Φ * jbracket y ^ M) := h2
        _ = max K 1 * Φ * jbracket y ^ M := by ring
    · intro y
      refine (hK hpos htT h₁ h₂ hΦ 0 ⟨le_rfl, ht⟩ y).trans ?_
      have h2 : K * Φ * jbracket y ^ M ≤ max K 1 * Φ * jbracket y ^ M := by
        have : 0 ≤ Φ * jbracket y ^ M := hJ1 y
        nlinarith [le_max_left K 1]
      exact h2
  have key := s85_V_core (μ := HRS.Whole.withDensityReal ρβ) (le_trans zero_le_one (le_max_right K 1)) hΦ0 hM
    hjint i1 i2 iφ1 iφ2 hb hφb x
  exact key

theorem s85_exists_cl (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    (hφ : S85Cc φ) : ∃ w, IsClassicalAdjointW (critCoeff d a β ρβ) t φ w :=
  s84_exists_adjoint hd ha hβ hρ ht (hφ.2.toSchwartzMap hφ.1) ⟨ht, le_rfl⟩

/-- The value of the chosen classical solution. -/
def s85_Ucc (a β : ℝ) (ρβ : Euc d → ℝ) (t : ℝ) (φ : Euc d → ℝ) (x : Euc d) : ℝ :=
  s85_V ρβ (fun r => propagatorW (critCoeff d a β ρβ) r t φ) φ x

theorem s85_Ucc_eq (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    {w : ℝ → Euc d → ℝ} (hw : IsClassicalAdjointW (critCoeff d a β ρβ) t φ w) (x : Euc d) :
    s85_Ucc a β ρβ t φ x = s85_V ρβ w φ x := by
  have h := s85_propagator_eq hd ha hβ hρ ht hw (r := 0) ⟨le_rfl, ht⟩
  unfold s85_Ucc s85_V
  simp only [h]

/-- **Lipschitz dependence of `U_t` on `C_c^∞` data in the weighted sup norm.** -/
theorem s85_Ucc_bound (hd : 2 ≤ d) {a β T M : ℝ} (ha : 0 < a) (hβ : 0 < β) (hT : 0 < T) (hM : 0 ≤ M)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t Φ : ℝ} {φ₁ φ₂ : Euc d → ℝ}, 0 ≤ t → t ≤ T → S85Cc φ₁ → S85Cc φ₂ →
      Wt M Φ (fun y => φ₁ y - φ₂ y) → ∀ x : Euc d,
        |s85_Ucc a β ρβ t φ₁ x - s85_Ucc a β ρβ t φ₂ x| ≤ K * Φ * jbracket x ^ M := by
  obtain ⟨K, hK0, hK⟩ := s85_V_bound hd ha hβ hT hM hρ
  refine ⟨K, hK0, fun {t Φ φ₁ φ₂} ht htT h₁ h₂ hΦ x => ?_⟩
  obtain ⟨w₁, hw₁⟩ := s85_exists_cl hd ha hβ hρ ht h₁
  obtain ⟨w₂, hw₂⟩ := s85_exists_cl hd ha hβ hρ ht h₂
  rw [s85_Ucc_eq hd ha hβ hρ ht hw₁, s85_Ucc_eq hd ha hβ hρ ht hw₂]
  exact hK ht htT hw₁ hw₂ hΦ x

end HRS.MS.Wad
