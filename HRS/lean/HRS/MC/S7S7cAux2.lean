import HRS.MC.S7S7cAux1

/-!
# Packet `s7_S7c_hilbert_stein`, helper 2: calculus for `F` with bounded first/second derivatives

The finite-rank embedding `iota kappa : R^p -> E_r`, `y |-> sum_a y_a eps_{kappa a}`, the test functions
`psi_b(y) = DF(iota y)[eps_{kappa b}]` (`MemCb 1`) and their derivatives.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7c

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ}

/-- Local copy of `HRS.MC.Sec7.s7_C2b` (defined in the sorried spec file, which cannot be imported):
`f` has bounded derivatives of orders `1` and `2`.  Definitionally equal to the spec's definition. -/
def s7_C2b {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ 1 f x‖) ∧
    BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ 2 f x‖)

/-- Consequences of `s7_C2b`: operator-norm bounds on `DF` and `D^2 F`. -/
theorem s7c_C2b_facts {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ}
    (hF : s7_C2b F) :
    ContDiff ℝ 2 F ∧ ∃ M1 M2 : ℝ, 0 ≤ M1 ∧ 0 ≤ M2 ∧ (∀ x, ‖fderiv ℝ F x‖ ≤ M1) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ M2) := by
  obtain ⟨h2, ⟨M1, hM1⟩, ⟨M2, hM2⟩⟩ := hF
  refine ⟨h2, max M1 0, max M2 0, le_max_right _ _, le_max_right _ _, fun x => ?_, fun x => ?_⟩
  · have : ‖iteratedFDeriv ℝ 1 F x‖ ≤ M1 := hM1 ⟨x, rfl⟩
    rw [norm_iteratedFDeriv_one] at this
    exact this.trans (le_max_left _ _)
  · have h : ‖iteratedFDeriv ℝ 2 F x‖ ≤ M2 := hM2 ⟨x, rfl⟩
    have e : ‖fderiv ℝ (fderiv ℝ F) x‖ = ‖iteratedFDeriv ℝ 2 F x‖ := by
      rw [← norm_iteratedFDeriv_one (f := fderiv ℝ F), norm_iteratedFDeriv_fderiv]
    rw [e]
    exact h.trans (le_max_left _ _)

variable (r : ℝ)

/-- The finite-rank embedding `y |-> sum_a y_a eps_{kappa a}`. -/
def s7c_iota {p : ℕ} (κ : Fin p → NonzeroLattice d) : EuclideanSpace ℝ (Fin p) →L[ℝ] NegSobolev d r :=
  ∑ a : Fin p, (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).smulRight (s7_eps r (κ a))

theorem s7c_iota_apply {p : ℕ} (κ : Fin p → NonzeroLattice d) (y : EuclideanSpace ℝ (Fin p)) :
    s7c_iota r κ y = ∑ a, y a • s7_eps r (κ a) := by
  unfold s7c_iota
  simp

theorem s7c_iota_std {p : ℕ} (κ : Fin p → NonzeroLattice d) (c : Fin p) :
    s7c_iota r κ (stdVec c) = s7_eps r (κ c) := by
  rw [s7c_iota_apply]
  rw [Finset.sum_eq_single c]
  · simp [stdVec]
  · intro b _ hb
    simp [stdVec, PiLp.single_apply, hb]
  · simp

theorem s7c_norm_eps (k : NonzeroLattice d) : ‖s7_eps r k‖ = 1 := by
  unfold s7_eps
  exact lp.norm_single (by norm_num) k 1 |>.trans (by simp)

variable {r}

/-- `psi_b(y) = DF(iota y)[eps_{kappa b}]`. -/
def s7c_psi {p : ℕ} (F : NegSobolev d r → ℝ) (κ : Fin p → NonzeroLattice d) (b : Fin p)
    (y : EuclideanSpace ℝ (Fin p)) : ℝ :=
  fderiv ℝ F (s7c_iota r κ y) (s7_eps r (κ b))

theorem s7c_psi_hasFDerivAt {p : ℕ} {F : NegSobolev d r → ℝ} (hF2 : ContDiff ℝ 2 F)
    (κ : Fin p → NonzeroLattice d) (b : Fin p) (y : EuclideanSpace ℝ (Fin p)) :
    HasFDerivAt (s7c_psi F κ b)
      ((ContinuousLinearMap.apply ℝ ℝ (s7_eps r (κ b))).comp
        ((fderiv ℝ (fderiv ℝ F) (s7c_iota r κ y)).comp (s7c_iota r κ))) y := by
  have hd1 : Differentiable ℝ (fderiv ℝ F) :=
    (hF2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (s7c_iota r κ y)) (s7c_iota r κ y) :=
    (hd1 _).hasFDerivAt
  have h2 := h1.comp y (s7c_iota r κ).hasFDerivAt
  exact ((ContinuousLinearMap.apply ℝ ℝ (s7_eps r (κ b))).hasFDerivAt).comp y h2

theorem s7c_psi_fderiv {p : ℕ} {F : NegSobolev d r → ℝ} (hF2 : ContDiff ℝ 2 F)
    (κ : Fin p → NonzeroLattice d) (b c : Fin p) (y : EuclideanSpace ℝ (Fin p)) :
    fderiv ℝ (s7c_psi F κ b) y (stdVec c) =
      fderiv ℝ (fderiv ℝ F) (s7c_iota r κ y) (s7_eps r (κ c)) (s7_eps r (κ b)) := by
  rw [(s7c_psi_hasFDerivAt hF2 κ b y).fderiv]
  simp [s7c_iota_std]

theorem s7c_psi_memCb {p : ℕ} {F : NegSobolev d r → ℝ} (hF : s7_C2b F)
    (κ : Fin p → NonzeroLattice d) (b : Fin p) : MemCb 1 (s7c_psi F κ b) := by
  obtain ⟨hF2, M1, M2, hM1, hM2, h1, h2⟩ := s7c_C2b_facts hF
  refine ⟨?_, ?_⟩
  · have hd1 : ContDiff ℝ 1 (fderiv ℝ F) := hF2.fderiv_right (m := 1) (by norm_num)
    have : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin p) => fderiv ℝ F (s7c_iota r κ y)) :=
      hd1.comp (s7c_iota r κ).contDiff
    exact this.clm_apply contDiff_const
  · intro j hj
    interval_cases j
    · refine ⟨M1, ?_⟩
      rintro _ ⟨y, rfl⟩
      simp only [norm_iteratedFDeriv_zero, s7c_psi]
      calc ‖fderiv ℝ F (s7c_iota r κ y) (s7_eps r (κ b))‖
          ≤ ‖fderiv ℝ F (s7c_iota r κ y)‖ * ‖s7_eps r (κ b)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ M1 := by rw [s7c_norm_eps]; linarith [h1 (s7c_iota r κ y)]
    · refine ⟨M2 * ‖s7c_iota r κ‖, ?_⟩
      rintro _ ⟨y, rfl⟩
      simp only [norm_iteratedFDeriv_one]
      rw [(s7c_psi_hasFDerivAt hF2 κ b y).fderiv]
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
      calc ‖fderiv ℝ (fderiv ℝ F) (s7c_iota r κ y) (s7c_iota r κ u) (s7_eps r (κ b))‖
          ≤ ‖fderiv ℝ (fderiv ℝ F) (s7c_iota r κ y) (s7c_iota r κ u)‖ * ‖s7_eps r (κ b)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖fderiv ℝ (fderiv ℝ F) (s7c_iota r κ y)‖ * ‖s7c_iota r κ u‖) * 1 := by
            rw [s7c_norm_eps]
            gcongr
            exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ (M2 * (‖s7c_iota r κ‖ * ‖u‖)) := by
            rw [mul_one]
            gcongr
            · exact h2 _
            · exact ContinuousLinearMap.le_opNorm _ _
        _ = M2 * ‖s7c_iota r κ‖ * ‖u‖ := by ring

end HRS.MC.Sec7.S7c

end
