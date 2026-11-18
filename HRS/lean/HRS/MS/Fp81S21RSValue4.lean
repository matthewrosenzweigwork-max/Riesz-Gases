import HRS.MS.Fp81S21RSValue3

/-! A consumer-facing interval family of measurable, integrable BV RS values. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators

namespace HRS.Fp81.S21

/-- The exact variation majorant from `fp81s21_rsOn_bv_bound`. -/
def fp81s21_rs_bv_variation_majorant
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Ω → ℝ → E →L[ℝ] ℝ) (F : Ω → ℝ → E)
    (q r : ℝ) (ω : Ω) : ℝ :=
  (⨆ τ : Icc q r, ‖A ω τ‖) *
    (eVariationOn (F ω) (Icc q r)).toReal

/-- One scalar BV Riemann--Stieltjes value family on all subintervals of `[0,T]`. -/
structure fp81s21_RSBVWindow
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) (T : ℝ)
    (A : Ω → ℝ → E →L[ℝ] ℝ) (F : Ω → ℝ → E) where
  value : ℝ → ℝ → Ω → ℝ
  majorant : ℝ → ℝ → Ω → ℝ
  value_isRS : ∀ q r, 0 ≤ q → q ≤ r → r ≤ T →
    ∀ᵐ ω ∂μ, fp81s21_IsRSOn q r
      (fun τ u v => A ω τ (F ω v - F ω u)) (value q r ω)
  value_aemeasurable : ∀ q r, 0 ≤ q → q ≤ r → r ≤ T →
    AEMeasurable (value q r) μ
  value_integrable : ∀ q r, 0 ≤ q → q ≤ r → r ≤ T →
    Integrable (value q r) μ
  majorant_integrable : ∀ q r, 0 ≤ q → q ≤ r → r ≤ T →
    Integrable (majorant q r) μ
  value_bound : ∀ q r, 0 ≤ q → q ≤ r → r ≤ T →
    ∀ᵐ ω ∂μ, |value q r ω| ≤ majorant q r ω
  value_zero : ∀ q, 0 ≤ q → q ≤ T →
    value q q =ᵐ[μ] fun _ => 0
  value_add : ∀ q s r, 0 ≤ q → q ≤ s → s ≤ r → r ≤ T →
    value q r =ᵐ[μ] fun ω => value q s ω + value s r ω

/-- A window RS interface bundles drift and covariance scalar RS families. -/
structure fp81s21_WindowRS
    {Ω ED EJ : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup ED] [NormedSpace ℝ ED] [CompleteSpace ED]
    [NormedAddCommGroup EJ] [NormedSpace ℝ EJ] [CompleteSpace EJ]
    (μ : Measure Ω) (T : ℝ)
    (Ad : Ω → ℝ → ED →L[ℝ] ℝ) (Fd : Ω → ℝ → ED)
    (Aj : Ω → ℝ → EJ →L[ℝ] ℝ) (Fj : Ω → ℝ → EJ) where
  T_nonneg : 0 ≤ T
  drift : fp81s21_RSBVWindow μ T Ad Fd
  covariance : fp81s21_RSBVWindow μ T Aj Fj

/-- Select one interval family using the staged measurable BV selection theorem. -/
noncomputable def fp81s21_rsbv_window_of_bv
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) (T : ℝ)
    (A : Ω → ℝ → E →L[ℝ] ℝ) (F : Ω → ℝ → E)
    (hS : ∀ q r, 0 ≤ q → q < r → r ≤ T →
      ∀ τ u v, Measurable (fun ω => A ω τ (F ω v - F ω u)))
    (hgood : ∀ q r, 0 ≤ q → q < r → r ≤ T →
      ∀ᵐ ω ∂μ, ContinuousOn (A ω) (Icc q r) ∧
        BoundedVariationOn (F ω) (Icc q r))
    (hmaj : ∀ q r, 0 ≤ q → q < r → r ≤ T →
      Integrable (fp81s21_rs_bv_variation_majorant A F q r) μ) :
    fp81s21_RSBVWindow μ T A F := by
  classical
  let val : ℝ → ℝ → Ω → ℝ := fun q r =>
    if h : 0 ≤ q ∧ q < r ∧ r ≤ T then
      Classical.choose
        (fp81s21_rs_bv_ae_integrable_selection μ h.2.1 (A := A) (F := F)
          (hS q r h.1 h.2.1 h.2.2)
          (hgood q r h.1 h.2.1 h.2.2)
          (hmaj q r h.1 h.2.1 h.2.2))
    else fun _ => 0
  let maj : ℝ → ℝ → Ω → ℝ := fun q r =>
    if h : 0 ≤ q ∧ q < r ∧ r ≤ T then
      fp81s21_rs_bv_variation_majorant A F q r
    else fun _ => 0
  have hspec : ∀ q r, 0 ≤ q → q ≤ r → r ≤ T →
      ∀ᵐ ω ∂μ, fp81s21_IsRSOn q r
        (fun τ u v => A ω τ (F ω v - F ω u)) (val q r ω) := by
    intro q r hq hqr hr
    by_cases hlt : q < r
    · let hvalid : 0 ≤ q ∧ q < r ∧ r ≤ T := ⟨hq, hlt, hr⟩
      let hsel := fp81s21_rs_bv_ae_integrable_selection μ hlt (A := A) (F := F)
        (hS q r hq hlt hr) (hgood q r hq hlt hr) (hmaj q r hq hlt hr)
      have hchoose := Classical.choose_spec hsel
      have hv : val q r = Classical.choose hsel := by simp [val, hvalid]
      rw [hv]
      exact hchoose.2.1
    · have heq : q = r := le_antisymm hqr (le_of_not_gt hlt)
      subst r
      have hfalse : ¬ (0 ≤ q ∧ q < q ∧ q ≤ T) := by
        rintro ⟨_, hqq, _⟩
        exact (lt_irrefl q hqq)
      have hv : val q q = fun _ => 0 := by simp [val, hfalse]
      rw [hv]
      filter_upwards [] with ω
      exact fp81s21_isRSOn_zero q
        (fun τ u v => A ω τ (F ω v - F ω u))
  have hmeas : ∀ q r, 0 ≤ q → q ≤ r → r ≤ T → AEMeasurable (val q r) μ := by
    intro q r hq hqr hr
    by_cases hlt : q < r
    · let hvalid : 0 ≤ q ∧ q < r ∧ r ≤ T := ⟨hq, hlt, hr⟩
      let hsel := fp81s21_rs_bv_ae_integrable_selection μ hlt (A := A) (F := F)
        (hS q r hq hlt hr) (hgood q r hq hlt hr) (hmaj q r hq hlt hr)
      have hchoose := Classical.choose_spec hsel
      have hv : val q r = Classical.choose hsel := by simp [val, hvalid]
      rw [hv]
      exact hchoose.1
    · have heq : q = r := le_antisymm hqr (le_of_not_gt hlt)
      subst r
      have hfalse : ¬ (0 ≤ q ∧ q < q ∧ q ≤ T) := by
        rintro ⟨_, hqq, _⟩
        exact (lt_irrefl q hqq)
      have hv : val q q = fun _ => 0 := by simp [val, hfalse]
      rw [hv]
      exact aemeasurable_const
  have hint : ∀ q r, 0 ≤ q → q ≤ r → r ≤ T → Integrable (val q r) μ := by
    intro q r hq hqr hr
    by_cases hlt : q < r
    · let hvalid : 0 ≤ q ∧ q < r ∧ r ≤ T := ⟨hq, hlt, hr⟩
      let hsel := fp81s21_rs_bv_ae_integrable_selection μ hlt (A := A) (F := F)
        (hS q r hq hlt hr) (hgood q r hq hlt hr) (hmaj q r hq hlt hr)
      have hchoose := Classical.choose_spec hsel
      have hv : val q r = Classical.choose hsel := by simp [val, hvalid]
      rw [hv]
      exact hchoose.2.2.1
    · have heq : q = r := le_antisymm hqr (le_of_not_gt hlt)
      subst r
      have hfalse : ¬ (0 ≤ q ∧ q < q ∧ q ≤ T) := by
        rintro ⟨_, hqq, _⟩
        exact (lt_irrefl q hqq)
      have hv : val q q = fun _ => 0 := by simp [val, hfalse]
      rw [hv]
      exact integrable_zero Ω ℝ μ
  have hmajint : ∀ q r, 0 ≤ q → q ≤ r → r ≤ T → Integrable (maj q r) μ := by
    intro q r hq hqr hr
    by_cases hlt : q < r
    · let hvalid : 0 ≤ q ∧ q < r ∧ r ≤ T := ⟨hq, hlt, hr⟩
      simpa [maj, hvalid] using hmaj q r hq hlt hr
    · have heq : q = r := le_antisymm hqr (le_of_not_gt hlt)
      subst r
      have hfalse : ¬ (0 ≤ q ∧ q < q ∧ q ≤ T) := by
        rintro ⟨_, hqq, _⟩
        exact (lt_irrefl q hqq)
      have hv : maj q q = fun _ => 0 := by simp [maj, hfalse]
      rw [hv]
      exact integrable_zero Ω ℝ μ
  have hbound : ∀ q r, 0 ≤ q → q ≤ r → r ≤ T →
      ∀ᵐ ω ∂μ, |val q r ω| ≤ maj q r ω := by
    intro q r hq hqr hr
    by_cases hlt : q < r
    · let hvalid : 0 ≤ q ∧ q < r ∧ r ≤ T := ⟨hq, hlt, hr⟩
      let hsel := fp81s21_rs_bv_ae_integrable_selection μ hlt (A := A) (F := F)
        (hS q r hq hlt hr) (hgood q r hq hlt hr) (hmaj q r hq hlt hr)
      have hchoose := Classical.choose_spec hsel
      have hv : val q r = Classical.choose hsel := by simp [val, hvalid]
      have hm : maj q r = fp81s21_rs_bv_variation_majorant A F q r := by
        simp [maj, hvalid]
      rw [hv, hm]
      filter_upwards [hgood q r hq hlt hr, hchoose.2.1] with ω hω hωRS
      exact fp81s21_rsOn_bv_bound hlt (F ω) (A ω) hω.2 hω.1 hωRS
    · have heq : q = r := le_antisymm hqr (le_of_not_gt hlt)
      subst r
      have hfalse : ¬ (0 ≤ q ∧ q < q ∧ q ≤ T) := by
        rintro ⟨_, hqq, _⟩
        exact (lt_irrefl q hqq)
      have hv : val q q = fun _ => 0 := by simp [val, hfalse]
      have hm : maj q q = fun _ => 0 := by simp [maj, hfalse]
      rw [hv, hm]
      filter_upwards [] with ω
      simp
  have hzero : ∀ q, 0 ≤ q → q ≤ T → val q q =ᵐ[μ] fun _ => 0 := by
    intro q hq hqT
    have hfalse : ¬ (0 ≤ q ∧ q < q ∧ q ≤ T) := by
      rintro ⟨_, hqq, _⟩
      exact (lt_irrefl q hqq)
    have hv : val q q = fun _ => 0 := by simp [val, hfalse]
    rw [hv]
  have hadd : ∀ q s r, 0 ≤ q → q ≤ s → s ≤ r → r ≤ T →
      val q r =ᵐ[μ] fun ω => val q s ω + val s r ω := by
    intro q s r hq hqs hsr hr
    exact fp81s21_rs_bv_split_ae_selection μ hqs hsr A F
      (val q r) (val q s) (val s r)
      (hspec q r hq (hqs.trans hsr) hr)
      (hspec q s hq hqs (hsr.trans hr))
      (hspec s r (le_trans hq hqs) hsr hr)
  exact {
    value := val
    majorant := maj
    value_isRS := hspec
    value_aemeasurable := hmeas
    value_integrable := hint
    majorant_integrable := hmajint
    value_bound := hbound
    value_zero := hzero
    value_add := hadd
  }

/-- Build the public drift/covariance interface from the generic BV hypotheses. -/
noncomputable def fp81s21_WindowRS_of_bv
    {Ω ED EJ : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup ED] [NormedSpace ℝ ED] [CompleteSpace ED]
    [NormedAddCommGroup EJ] [NormedSpace ℝ EJ] [CompleteSpace EJ]
    (μ : Measure Ω) (T : ℝ)
    (Ad : Ω → ℝ → ED →L[ℝ] ℝ) (Fd : Ω → ℝ → ED)
    (Aj : Ω → ℝ → EJ →L[ℝ] ℝ) (Fj : Ω → ℝ → EJ)
    (hT : 0 ≤ T)
    (hSd : ∀ q r, 0 ≤ q → q < r → r ≤ T →
      ∀ τ u v, Measurable (fun ω => Ad ω τ (Fd ω v - Fd ω u)))
    (hgd : ∀ q r, 0 ≤ q → q < r → r ≤ T →
      ∀ᵐ ω ∂μ, ContinuousOn (Ad ω) (Icc q r) ∧
        BoundedVariationOn (Fd ω) (Icc q r))
    (hmd : ∀ q r, 0 ≤ q → q < r → r ≤ T →
      Integrable (fp81s21_rs_bv_variation_majorant Ad Fd q r) μ)
    (hSj : ∀ q r, 0 ≤ q → q < r → r ≤ T →
      ∀ τ u v, Measurable (fun ω => Aj ω τ (Fj ω v - Fj ω u)))
    (hgj : ∀ q r, 0 ≤ q → q < r → r ≤ T →
      ∀ᵐ ω ∂μ, ContinuousOn (Aj ω) (Icc q r) ∧
        BoundedVariationOn (Fj ω) (Icc q r))
    (hmj : ∀ q r, 0 ≤ q → q < r → r ≤ T →
      Integrable (fp81s21_rs_bv_variation_majorant Aj Fj q r) μ) :
    fp81s21_WindowRS μ T Ad Fd Aj Fj :=
  ⟨hT,
    fp81s21_rsbv_window_of_bv μ T Ad Fd hSd hgd hmd,
    fp81s21_rsbv_window_of_bv μ T Aj Fj hSj hgj hmj⟩

#print axioms fp81s21_rsbv_window_of_bv
#print axioms fp81s21_WindowRS_of_bv

end HRS.Fp81.S21

end
