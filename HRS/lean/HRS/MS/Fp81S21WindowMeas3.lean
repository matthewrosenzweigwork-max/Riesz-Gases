import HRS.MS.Fp81S21WindowMeas2
import HRS.Uniform.KotTrace

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.FixEq

variable {d : ℕ}

/- Exact interfaces for the compressed measurable density:
def fp81s21_windowDm (C : WholeCoeff d) (m H a : ℝ)
    (z : ℝ → (Euc d → ℝ) → ℝ) (ha : 0 ≤ a) (hH : 0 ≤ H) (v : ℝ) :
    KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ

theorem fp81s21_windowDm_meas_entries
    (hd : 1 ≤ d) {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P Bpos : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} (hH : 0 < H) (ha : 0 ≤ a)
    (horb : R2OrbitSummable C m (a + H) r)
    (hterminal : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ α : MultiIndex d, ∀ x : Euc d,
      propagatorW C v v (oscTestFun m α) x = oscTestFun m α x)
    (hz : IsR2L1F r P (a + H) z) (hP : (d : ℝ) < 2 * P)
    (hm : R2JIntegrandMeas C m (a + H) z)
    (hPos : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 →
      ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fp81s21_window_feature C m H a v) x‖ ≤ Bpos)
    (u w : KSpace d m H) :
    Measurable (fun v => fp81s21_windowDm C m H a z ha (le_of_lt hH) v u w)

theorem fp81s21_windowDm_symm
    (hd : 1 ≤ d) {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} (hH : 0 < H) (ha : 0 ≤ a)
    (horb : R2OrbitSummable C m (a + H) r)
    (hz : IsR2L1F r P (a + H) z) (hP : (d : ℝ) < 2 * P)
    (hm : R2JIntegrandMeas C m (a + H) z) :
    ∀ v u w, fp81s21_windowDm C m H a z ha (le_of_lt hH) v u w =
      fp81s21_windowDm C m H a z ha (le_of_lt hH) v w u

theorem fp81s21_windowDm_good_spec
    (hd : 1 ≤ d) {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P Bpos : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} (hH : 0 < H) (ha : 0 ≤ a)
    (horb : R2OrbitSummable C m (a + H) r)
    (hterminal : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ α : MultiIndex d, ∀ x : Euc d,
      propagatorW C v v (oscTestFun m α) x = oscTestFun m α x)
    (hz : IsR2L1F r P (a + H) z) (hP : (d : ℝ) < 2 * P)
    (hm : R2JIntegrandMeas C m (a + H) z)
    (hPos : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 →
      ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fp81s21_window_feature C m H a v) x‖ ≤ Bpos) :
    ∃ G, S101Good C m (a + H) z G ∧
      ∀ v, fp81s21_windowDm C m H a z ha (le_of_lt hH) v =
        if v ∈ G then fp81s21_windowD C m H a z v else 0
-/

/-- Compress a full-history measurable form through the Hilbert adjoint of the
same bounded map used to compress the feature. -/
def fp81s21_windowDm (C : WholeCoeff d) (m H a : ℝ)
    (z : ℝ → (Euc d → ℝ) → ℝ) (ha : 0 ≤ a) (hH : 0 ≤ H) (v : ℝ) :
    KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ := by
  by_cases hv : v ∈ Icc (0 : ℝ) (a + H)
  · by_cases hle : v ≤ a
    · exact HRS.Uniform.Kot.formComp
        (ContinuousLinearMap.adjoint
          (fp81s21_windowCompressionMinus (d := d) (m := m) (a := a) (H := H) ha hH))
        (s101Dm C m (a + H) z v)
    · exact HRS.Uniform.Kot.formComp
        (ContinuousLinearMap.adjoint
          (fp81s21_windowCompressionPlus (d := d) (m := m) (a := a) (H := H) ha hH))
        (s101Dm C m (a + H) z v)
  · exact 0

private lemma fp81s21_windowDm_pullback
    {C : WholeCoeff d} {m H a v : ℝ} {r : ℕ} {P Bpos : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} (ha : 0 ≤ a) (hH : 0 < H)
    (hd : 1 ≤ d) (horb : R2OrbitSummable C m (a + H) r)
    (hterminal : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ α : MultiIndex d, ∀ x : Euc d,
      propagatorW C v v (oscTestFun m α) x = oscTestFun m α x)
    (hz : IsR2L1F r P (a + H) z) (hP : (d : ℝ) < 2 * P)
    (hm : R2JIntegrandMeas C m (a + H) z)
    (hv : v ∈ Icc (0 : ℝ) (a + H))
    (hPos : ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j (fp81s21_window_feature C m H a v) x‖ ≤ Bpos)
    (F : KSpace d m (a + H) →L[ℝ] KSpace d m H)
    (hfeature : ∀ x, fp81s21_window_feature C m H a v x =
      F (s101Gamma C m (a + H) v x)) :
    HRS.Uniform.Kot.formComp (ContinuousLinearMap.adjoint F)
        (s101D C m (a + H) z v) = fp81s21_windowD C m H a z v := by
  ext u w
  obtain ⟨c, hD⟩ := s101_data_of_horb hd horb
  let A : S101Adm C m (a + H) r P z := ⟨hd, hP, horb, hz.1, hm⟩
  have hGammaFull : Differentiable ℝ (fun x => s101Gamma C m (a + H) v x) :=
    s101_Gamma_diff A hv
  have htermv : ∀ α : MultiIndex d, ∀ x : Euc d,
      propagatorW C v v (oscTestFun m α) x = oscTestFun m α x :=
    fun α x => hterminal v hv α x
  have hreg := fp81s21_window_feature_contDiff_full_of_data
    hd hH a ha v hv hD htermv
  have hGammaWindow : Differentiable ℝ (fp81s21_window_feature C m H a v) :=
    hreg.1.differentiable (by exact_mod_cast Nat.succ_ne_zero r)
  have hu : ∀ x, inner ℝ (fp81s21_window_feature C m H a v x) u =
      inner ℝ (s101Gamma C m (a + H) v x) (ContinuousLinearMap.adjoint F u) := by
    intro x
    rw [hfeature x, ← ContinuousLinearMap.adjoint_inner_right]
  have hw : ∀ x, inner ℝ (fp81s21_window_feature C m H a v x) w =
      inner ℝ (s101Gamma C m (a + H) v x) (ContinuousLinearMap.adjoint F w) := by
    intro x
    rw [hfeature x, ← ContinuousLinearMap.adjoint_inner_right]
  let fu : Euc d → ℝ := fun x => inner ℝ (fp81s21_window_feature C m H a v x) u
  let fw : Euc d → ℝ := fun x => inner ℝ (fp81s21_window_feature C m H a v x) w
  let gu : Euc d → ℝ := fun x => inner ℝ (s101Gamma C m (a + H) v x)
    (ContinuousLinearMap.adjoint F u)
  let gw : Euc d → ℝ := fun x => inner ℝ (s101Gamma C m (a + H) v x)
    (ContinuousLinearMap.adjoint F w)
  have hfu : fu = gu := funext hu
  have hfw : fw = gw := funext hw
  have hFmWindow := s101_Fm_Rk_eq_inner hGammaWindow
    (u := u) (v := w) (f := fu) (f' := fw) (fun x => rfl) (fun x => rfl)
  have hFmFull := s101_Fm_Rk_eq_inner hGammaFull
    (u := ContinuousLinearMap.adjoint F u) (v := ContinuousLinearMap.adjoint F w)
    (f := gu) (f' := gw) (fun x => rfl) (fun x => rfl)
  have hFm : s101Fm (fp81s21_window_feature C m H a v) (s101Rk u w) =
      s101Fm (s101Gamma C m (a + H) v)
        (s101Rk (ContinuousLinearMap.adjoint F u) (ContinuousLinearMap.adjoint F w)) := by
    calc
      s101Fm (fp81s21_window_feature C m H a v) (s101Rk u w) =
          fun x => inner ℝ (gradient fu x) (gradient fw x) := hFmWindow
      _ = fun x => inner ℝ (gradient gu x) (gradient gw x) := by rw [hfu, hfw]
      _ = s101Fm (s101Gamma C m (a + H) v)
          (s101Rk (ContinuousLinearMap.adjoint F u) (ContinuousLinearMap.adjoint F w)) := hFmFull.symm
  have hwindow := fp81s21_windowD_data hd hH ha horb hterminal hz hP hv hPos
  simp only [HRS.Uniform.Kot.formComp_apply]
  rw [s101_D_apply A hv, hwindow.1, hFm]

theorem fp81s21_windowDm_meas_entries
    (hd : 1 ≤ d) {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P Bpos : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} (hH : 0 < H) (ha : 0 ≤ a)
    (horb : R2OrbitSummable C m (a + H) r)
    (hterminal : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ α : MultiIndex d, ∀ x : Euc d,
      propagatorW C v v (oscTestFun m α) x = oscTestFun m α x)
    (hz : IsR2L1F r P (a + H) z) (hP : (d : ℝ) < 2 * P)
    (hm : R2JIntegrandMeas C m (a + H) z)
    (hPos : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 →
      ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fp81s21_window_feature C m H a v) x‖ ≤ Bpos)
    (u w : KSpace d m H) :
    Measurable (fun v => fp81s21_windowDm C m H a z ha (le_of_lt hH) v u w) := by
  let A : S101Adm C m (a + H) r P z := ⟨hd, hP, horb, hz.1, hm⟩
  have hL : 0 ≤ a + H := by linarith
  have htr : S101Tr C m (a + H) z := s101_htr_of_L1F A hL hz
  have hTD := s101_Dm_isTraceDensity A hL htr
  have hminus0 : Measurable (fun v => s101Dm C m (a + H) z v
      (ContinuousLinearMap.adjoint
        (fp81s21_windowCompressionMinus (d := d) (m := m) (a := a) (H := H) ha (le_of_lt hH)) u)
      (ContinuousLinearMap.adjoint
        (fp81s21_windowCompressionMinus (d := d) (m := m) (a := a) (H := H) ha (le_of_lt hH)) w)) :=
    hTD.2.2.1 _ _
  have hplus0 : Measurable (fun v => s101Dm C m (a + H) z v
      (ContinuousLinearMap.adjoint
        (fp81s21_windowCompressionPlus (d := d) (m := m) (a := a) (H := H) ha (le_of_lt hH)) u)
      (ContinuousLinearMap.adjoint
        (fp81s21_windowCompressionPlus (d := d) (m := m) (a := a) (H := H) ha (le_of_lt hH)) w)) :=
    hTD.2.2.1 _ _
  have hminus : Measurable (fun v => HRS.Uniform.Kot.formComp
      (ContinuousLinearMap.adjoint
        (fp81s21_windowCompressionMinus (d := d) (m := m) (a := a) (H := H) ha (le_of_lt hH)))
      (s101Dm C m (a + H) z v) u w) := by
    simpa only [HRS.Uniform.Kot.formComp_apply] using hminus0
  have hplus : Measurable (fun v => HRS.Uniform.Kot.formComp
      (ContinuousLinearMap.adjoint
        (fp81s21_windowCompressionPlus (d := d) (m := m) (a := a) (H := H) ha (le_of_lt hH)))
      (s101Dm C m (a + H) z v) u w) := by
    simpa only [HRS.Uniform.Kot.formComp_apply] using hplus0
  have hscalar : Measurable (fun v => if v ∈ Icc (0 : ℝ) (a + H) then
    if v ≤ a then HRS.Uniform.Kot.formComp
        (ContinuousLinearMap.adjoint
          (fp81s21_windowCompressionMinus (d := d) (m := m) (a := a) (H := H) ha (le_of_lt hH)))
        (s101Dm C m (a + H) z v) u w
    else HRS.Uniform.Kot.formComp
        (ContinuousLinearMap.adjoint
          (fp81s21_windowCompressionPlus (d := d) (m := m) (a := a) (H := H) ha (le_of_lt hH)))
        (s101Dm C m (a + H) z v) u w else 0) :=
    Measurable.ite measurableSet_Icc
      (Measurable.ite measurableSet_Iic hminus hplus) measurable_const
  have hEq : (fun v => fp81s21_windowDm C m H a z ha (le_of_lt hH) v u w) =
      (fun v => if v ∈ Icc (0 : ℝ) (a + H) then
        if v ≤ a then HRS.Uniform.Kot.formComp
            (ContinuousLinearMap.adjoint
              (fp81s21_windowCompressionMinus (d := d) (m := m) (a := a) (H := H) ha (le_of_lt hH)))
            (s101Dm C m (a + H) z v) u w
        else HRS.Uniform.Kot.formComp
            (ContinuousLinearMap.adjoint
              (fp81s21_windowCompressionPlus (d := d) (m := m) (a := a) (H := H) ha (le_of_lt hH)))
            (s101Dm C m (a + H) z v) u w else 0) := by
    funext v
    by_cases hv : v ∈ Icc (0 : ℝ) (a + H)
    · by_cases hle : v ≤ a
      · simp [fp81s21_windowDm, hv, hle]
      · simp [fp81s21_windowDm, hv, hle]
    · simp [fp81s21_windowDm, hv]
  rw [hEq]
  exact hscalar

theorem fp81s21_windowDm_symm
    (hd : 1 ≤ d) {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} (hH : 0 < H) (ha : 0 ≤ a)
    (horb : R2OrbitSummable C m (a + H) r)
    (hz : IsR2L1F r P (a + H) z) (hP : (d : ℝ) < 2 * P)
    (hm : R2JIntegrandMeas C m (a + H) z) :
    ∀ v u w, fp81s21_windowDm C m H a z ha (le_of_lt hH) v u w =
      fp81s21_windowDm C m H a z ha (le_of_lt hH) v w u := by
  let A : S101Adm C m (a + H) r P z := ⟨hd, hP, horb, hz.1, hm⟩
  have hL : 0 ≤ a + H := by linarith
  have htr : S101Tr C m (a + H) z := s101_htr_of_L1F A hL hz
  have hTD := s101_Dm_isTraceDensity A hL htr
  intro v u w
  by_cases hv : v ∈ Icc (0 : ℝ) (a + H)
  · by_cases hle : v ≤ a
    · simp only [fp81s21_windowDm, dif_pos hv, dif_pos hle,
        HRS.Uniform.Kot.formComp_apply]
      exact hTD.1 v ((ContinuousLinearMap.adjoint
        (fp81s21_windowCompressionMinus (d := d) (m := m) (a := a) (H := H)
          ha (le_of_lt hH))) u)
        ((ContinuousLinearMap.adjoint
          (fp81s21_windowCompressionMinus (d := d) (m := m) (a := a) (H := H)
            ha (le_of_lt hH))) w)
    · simp only [fp81s21_windowDm, dif_pos hv, dif_neg hle,
        HRS.Uniform.Kot.formComp_apply]
      exact hTD.1 v ((ContinuousLinearMap.adjoint
        (fp81s21_windowCompressionPlus (d := d) (m := m) (a := a) (H := H)
          ha (le_of_lt hH))) u)
        ((ContinuousLinearMap.adjoint
          (fp81s21_windowCompressionPlus (d := d) (m := m) (a := a) (H := H)
            ha (le_of_lt hH))) w)
  · simp [fp81s21_windowDm, hv]

local instance fp81s21_decidable_of_classical (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem fp81s21_windowDm_good_spec
    (hd : 1 ≤ d) {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P Bpos : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} (hH : 0 < H) (ha : 0 ≤ a)
    (horb : R2OrbitSummable C m (a + H) r)
    (hterminal : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ α : MultiIndex d, ∀ x : Euc d,
      propagatorW C v v (oscTestFun m α) x = oscTestFun m α x)
    (hz : IsR2L1F r P (a + H) z) (hP : (d : ℝ) < 2 * P)
    (hm : R2JIntegrandMeas C m (a + H) z)
    (hPos : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 →
      ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (fp81s21_window_feature C m H a v) x‖ ≤ Bpos) :
    ∃ G, S101Good C m (a + H) z G ∧
      ∀ v, fp81s21_windowDm C m H a z ha (le_of_lt hH) v =
        if v ∈ G then fp81s21_windowD C m H a z v else 0 := by
  let A : S101Adm C m (a + H) r P z := ⟨hd, hP, horb, hz.1, hm⟩
  have hL : 0 ≤ a + H := by linarith
  obtain ⟨c, hD⟩ := s101_data_of_horb hd horb
  obtain ⟨G, hG, hDm⟩ := s101_Dm_spec A hL
  refine ⟨G, hG, fun v => ?_⟩
  by_cases hv : v ∈ Icc (0 : ℝ) (a + H)
  · by_cases hgood : v ∈ G
    · have hDmv : s101Dm C m (a + H) z v = s101D C m (a + H) z v := by
        rw [hDm v, if_pos hgood]
      by_cases hle : v ≤ a
      · have hfeature : ∀ x,
          fp81s21_window_feature C m H a v x =
            fp81s21_windowCompressionMinus (d := d) (m := m) (a := a) (H := H)
              ha (le_of_lt hH) (s101Gamma C m (a + H) v x) := by
          intro x
          simpa [hle] using fp81s21_window_feature_eq_compression ha (le_of_lt hH)
            hD hterminal hv x
        have hpull := fp81s21_windowDm_pullback ha hH hd horb hterminal hz hP hm hv
          (hPos v hv) (fp81s21_windowCompressionMinus (d := d) (m := m)
            (a := a) (H := H) ha (le_of_lt hH)) hfeature
        have hEq : fp81s21_windowDm C m H a z ha (le_of_lt hH) v =
            fp81s21_windowD C m H a z v := by
          simp only [fp81s21_windowDm, dif_pos hv, dif_pos hle]
          calc
            HRS.Uniform.Kot.formComp
                (ContinuousLinearMap.adjoint
                  (fp81s21_windowCompressionMinus (d := d) (m := m)
                    (a := a) (H := H) ha (le_of_lt hH)))
                (s101Dm C m (a + H) z v) =
              HRS.Uniform.Kot.formComp
                (ContinuousLinearMap.adjoint
                  (fp81s21_windowCompressionMinus (d := d) (m := m)
                    (a := a) (H := H) ha (le_of_lt hH)))
                (s101D C m (a + H) z v) := by rw [hDmv]
            _ = fp81s21_windowD C m H a z v := hpull
        rw [if_pos hgood]
        exact hEq
      · have hgt : a < v := lt_of_not_ge hle
        have hfeature : ∀ x,
          fp81s21_window_feature C m H a v x =
            fp81s21_windowCompressionPlus (d := d) (m := m) (a := a) (H := H)
              ha (le_of_lt hH) (s101Gamma C m (a + H) v x) := by
          intro x
          simpa [hle] using fp81s21_window_feature_eq_compression ha (le_of_lt hH)
            hD hterminal hv x
        have hpull := fp81s21_windowDm_pullback ha hH hd horb hterminal hz hP hm hv
          (hPos v hv) (fp81s21_windowCompressionPlus (d := d) (m := m)
            (a := a) (H := H) ha (le_of_lt hH)) hfeature
        have hEq : fp81s21_windowDm C m H a z ha (le_of_lt hH) v =
            fp81s21_windowD C m H a z v := by
          simp only [fp81s21_windowDm, dif_pos hv, dif_neg hle]
          calc
            HRS.Uniform.Kot.formComp
                (ContinuousLinearMap.adjoint
                  (fp81s21_windowCompressionPlus (d := d) (m := m)
                    (a := a) (H := H) ha (le_of_lt hH)))
                (s101Dm C m (a + H) z v) =
              HRS.Uniform.Kot.formComp
                (ContinuousLinearMap.adjoint
                  (fp81s21_windowCompressionPlus (d := d) (m := m)
                    (a := a) (H := H) ha (le_of_lt hH)))
                (s101D C m (a + H) z v) := by rw [hDmv]
            _ = fp81s21_windowD C m H a z v := hpull
        rw [if_pos hgood]
        exact hEq
    · have hDzero : s101Dm C m (a + H) z v = 0 := by
        rw [hDm v, if_neg hgood]
      rw [if_neg hgood]
      simp [fp81s21_windowDm, hv, hDzero, HRS.Uniform.Kot.formComp_zero]
  · have hnotG : v ∉ G := fun hmem => hv (hG.2.1 hmem)
    rw [if_neg hnotG]
    simp [fp81s21_windowDm, hv]

/- Exact interfaces for the history-time comparison and sharp trace estimate:
theorem fp81s21_windowDm_ae_eq_windowD
    (hd : 1 ≤ d) {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P Bpos : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} (hH : 0 < H) (ha : 0 ≤ a)
    (horb : R2OrbitSummable C m (a + H) r)
    (hterminal : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ α : MultiIndex d, ∀ x : Euc d,
      propagatorW C v v (oscTestFun m α) x = oscTestFun m α x)
    (hz : IsR2L1F r P (a + H) z) (hP : (d : ℝ) < 2 * P)
    (hm : R2JIntegrandMeas C m (a + H) z)
    (hPos : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 →
      ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fp81s21_window_feature C m H a v) x‖ ≤ Bpos) :
    ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) (a + H))),
      fp81s21_windowDm C m H a z ha (le_of_lt hH) v = fp81s21_windowD C m H a z v

theorem fp81s21_windowDm_trace_bound
    (hd : 1 ≤ d) {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P Bpos : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} (hH : 0 < H) (ha : 0 ≤ a)
    (horb : R2OrbitSummable C m (a + H) r)
    (hterminal : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ α : MultiIndex d, ∀ x : Euc d,
      propagatorW C v v (oscTestFun m α) x = oscTestFun m α x)
    (hz : IsR2L1F r P (a + H) z) (hP : (d : ℝ) < 2 * P)
    (hm : R2JIntegrandMeas C m (a + H) z)
    (hPos : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 →
      ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fp81s21_window_feature C m H a v) x‖ ≤ Bpos) :
    ∀ v ∈ Icc (0 : ℝ) (a + H),
      ENNReal.ofReal (HRS.traceNormForm
        (fp81s21_windowDm C m H a z ha (le_of_lt hH) v)) ≤
        ENNReal.ofReal |2 * C.ν| * dualNormE r P (z v) *
          ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r * Bpos ^ 2))
-/

theorem fp81s21_windowDm_ae_eq_windowD
    (hd : 1 ≤ d) {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P Bpos : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} (hH : 0 < H) (ha : 0 ≤ a)
    (horb : R2OrbitSummable C m (a + H) r)
    (hterminal : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ α : MultiIndex d, ∀ x : Euc d,
      propagatorW C v v (oscTestFun m α) x = oscTestFun m α x)
    (hz : IsR2L1F r P (a + H) z) (hP : (d : ℝ) < 2 * P)
    (hm : R2JIntegrandMeas C m (a + H) z)
    (hPos : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 →
      ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fp81s21_window_feature C m H a v) x‖ ≤ Bpos) :
    ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) (a + H))),
      fp81s21_windowDm C m H a z ha (le_of_lt hH) v = fp81s21_windowD C m H a z v := by
  obtain ⟨G, hG, hspec⟩ := fp81s21_windowDm_good_spec
    hd hH ha horb hterminal hz hP hm hPos
  have hGae : ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) (a + H))), v ∈ G := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have hnot : ∀ᵐ v ∂(volume : Measure ℝ), v ∉ Icc (0 : ℝ) (a + H) \ G :=
      measure_eq_zero_iff_ae_notMem.1 hG.2.2.1
    filter_upwards [hnot] with v hv hI
    by_contra hng
    exact hv ⟨hI, hng⟩
  filter_upwards [hGae] with v hv
  rw [hspec v]
  simp [hv]

theorem fp81s21_windowDm_trace_bound
    (hd : 1 ≤ d) {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P Bpos : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} (hH : 0 < H) (ha : 0 ≤ a)
    (horb : R2OrbitSummable C m (a + H) r)
    (hterminal : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ α : MultiIndex d, ∀ x : Euc d,
      propagatorW C v v (oscTestFun m α) x = oscTestFun m α x)
    (hz : IsR2L1F r P (a + H) z) (hP : (d : ℝ) < 2 * P)
    (hm : R2JIntegrandMeas C m (a + H) z)
    (hPos : ∀ v ∈ Icc (0 : ℝ) (a + H), ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 →
      ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fp81s21_window_feature C m H a v) x‖ ≤ Bpos) :
    ∀ v ∈ Icc (0 : ℝ) (a + H),
      ENNReal.ofReal (HRS.traceNormForm
        (fp81s21_windowDm C m H a z ha (le_of_lt hH) v)) ≤
        ENNReal.ofReal |2 * C.ν| * dualNormE r P (z v) *
          ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r * Bpos ^ 2)) := by
  obtain ⟨G, hG, hspec⟩ := fp81s21_windowDm_good_spec
    hd hH ha horb hterminal hz hP hm hPos
  intro v hv
  by_cases hgood : v ∈ G
  · rw [hspec v, if_pos hgood]
    exact (fp81s21_windowD_data hd hH ha horb hterminal hz hP hv (hPos v hv)).2.2.2
  · rw [hspec v, if_neg hgood]
    simp [HRS.traceNormForm]

#print axioms fp81s21_windowDm_meas_entries
#print axioms fp81s21_windowDm_symm
#print axioms fp81s21_windowDm_good_spec
#print axioms fp81s21_windowDm_ae_eq_windowD
#print axioms fp81s21_windowDm_trace_bound

end HRS.Fp81.S21

end

