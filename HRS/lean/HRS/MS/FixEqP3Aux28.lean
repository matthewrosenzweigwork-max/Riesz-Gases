import HRS.MS.FixEqP3Aux27

/-!
# S5.7 `fixed_equation` (worker S57P), part 40: Hilbert-Schmidt Hölder constant of the kernel difference
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ} {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K KN : ℝ} {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} {ν νN : ℝ}
  {c cN : ℝ → Euc d → Euc d} {ρ ρN : ℝ → Euc d → ℝ} {A Λc νbar : ℝ} {m : ℝ} {J : ℕ}
  {Ca CaN Cd CdN Cp1 Cp2 Dt : ℝ}

/-- the Hölder constant `C_z` of the kernel difference -/
def s57pCz (T q qN τ CaN CdN Cp1 Cp2 Dt : ℝ) : ℝ :=
  ((Real.sqrt (2 * qN) - Real.sqrt (2 * q)) ^ 2 + 2 * q * τ) * (CdN ^ 2 * T ^ 2 + CaN ^ 2) +
    2 * q * Dt ^ 2 * (Cp2 ^ 2 * T ^ 2 + Cp1 ^ 2)

theorem s57p_sq3 {E : Type*} [NormedAddCommGroup E] (x1 x2 x3 y1 y2 y3 : E) :
    ‖(x1 + x2 + x3) - (y1 + y2 + y3)‖ ^ 2 ≤ 3 * (‖x1 - y1‖ ^ 2 + ‖x2 - y2‖ ^ 2 + ‖x3 - y3‖ ^ 2) := by
  have e : (x1 + x2 + x3) - (y1 + y2 + y3) = (x1 - y1) + (x2 - y2) + (x3 - y3) := by abel
  rw [e]
  have h := norm_add₃_le (a := x1 - y1) (b := x2 - y2) (c := x3 - y3)
  have h0 : 0 ≤ ‖(x1 - y1) + (x2 - y2) + (x3 - y3)‖ := norm_nonneg _
  nlinarith [norm_nonneg (x1 - y1), norm_nonneg (x2 - y2), norm_nonneg (x3 - y3),
    sq_nonneg (‖x1 - y1‖ - ‖x2 - y2‖), sq_nonneg (‖x2 - y2‖ - ‖x3 - y3‖), sq_nonneg (‖x1 - y1‖ - ‖x3 - y3‖)]

theorem S57pPairBd.kdiff_holder (P : S57pPairBd θ T n K KN s M Q ν νN c cN ρ ρN A Λc νbar m J Ca CaN Cd CdN Cp1 Cp2 Dt)
    (hT : 0 ≤ T) {q qN τ : ℝ} (hq : 0 ≤ q) (hqN : 0 ≤ qN) (hτ0 : 0 ≤ τ)
    (hτ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ x : Euc d, ENNReal.ofReal |ρN r x - ρ r x| ≤ ENNReal.ofReal τ)
    (α : MultiIndex d) {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (h2T : t₂ ≤ T) :
    ‖(s57pκ (fixedEqCoeff s M Q νN cN ρN) T qN ρN t₂ (oscTestFun m α) - s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t₂ (oscTestFun m α)) -
      (s57pκ (fixedEqCoeff s M Q νN cN ρN) T qN ρN t₁ (oscTestFun m α) - s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t₁ (oscTestFun m α))‖ ^ 2 ≤
      3 * (s57pCz T q qN τ CaN CdN Cp1 Cp2 Dt * oscEigenvalue d α ^ ((J : ℝ) - m)) * (t₂ - t₁) := by
  have ht1 : t₁ ∈ Set.Icc (0 : ℝ) T := ⟨h0, h12.trans h2T⟩
  have ht2 : t₂ ∈ Set.Icc (0 : ℝ) T := ⟨h0.trans h12, h2T⟩
  have hn : 1 ≤ n := by have := P.Fx.hn4; omega
  have K1 := s57p_w1_data P.FxN.fe hT hq hqN P.FxN.prob
  have K2 := s57p_w2_data P.Fx.fe P.FxN.fe hT hq P.Fx.prob P.FxN.prob hτ0 hτ
  have K3 := s57p_wdata P.Fx.fe hT hq P.Fx.prob
  rw [P.kdiff_decomp hT hq hqN hτ0 hτ α ht2, P.kdiff_decomp hT hq hqN hτ0 hτ α ht1]
  set L := oscEigenvalue d α ^ (((J : ℝ) - m) / 2) with hL
  have hL0 : 0 ≤ L := Real.rpow_nonneg (oscEigenvalue_pos α).le _
  have hLL : L ^ 2 = oscEigenvalue d α ^ ((J : ℝ) - m) := by rw [hL, rpow_half_sq _ _ (oscEv_pos α)]
  have p1 := s57p_el_holder_fam K1 P.hbdN α h0 h12 h2T hn
  have p2 := s57p_el_holder_fam K2 P.hbdN α h0 h12 h2T hn
  have p3 := s57p_el_holder K3 ((P.Adiff α ht2).1).aestronglyMeasurable ((P.Adiff α ht1).1).aestronglyMeasurable
    (s := t₁) (t := t₂) (Ba := Cp1 * L * Dt) (Bd := Cp2 * L * Dt) h12 (fun p _ => (P.Adiff α ht2).2 p)
    (fun p _ => (P.Adiff α ht1).2 p) (fun p hp => P.Hdiff α h0 h12 h2T p hp)
  refine (s57p_sq3 _ _ _ _ _ _).trans ?_
  have hu : 0 ≤ t₂ - t₁ := sub_nonneg.2 h12
  have huT : t₂ - t₁ ≤ T := by linarith [ht1.1, ht2.2]
  have h3 : (t₂ - t₁) ^ 2 * T ≤ T ^ 2 * (t₂ - t₁) := by nlinarith [mul_nonneg hu hT]
  have hW1 : 0 ≤ (Real.sqrt (2 * qN) - Real.sqrt (2 * q)) ^ 2 := sq_nonneg _
  have hW2 : 0 ≤ 2 * q * τ := by positivity
  have hW3 : 0 ≤ 2 * q := by positivity
  have gen : ∀ (W Cd' Ca' : ℝ), 0 ≤ W →
      W * ((Cd' * L) ^ 2 * (t₂ - t₁) ^ 2 * T + (Ca' * L) ^ 2 * (t₂ - t₁)) ≤
        W * (Cd' ^ 2 * T ^ 2 + Ca' ^ 2) * L ^ 2 * (t₂ - t₁) := by
    intro W Cd' Ca' hW
    have : (Cd' * L) ^ 2 * (t₂ - t₁) ^ 2 * T ≤ (Cd' * L) ^ 2 * (T ^ 2 * (t₂ - t₁)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    calc W * ((Cd' * L) ^ 2 * (t₂ - t₁) ^ 2 * T + (Ca' * L) ^ 2 * (t₂ - t₁))
        ≤ W * ((Cd' * L) ^ 2 * (T ^ 2 * (t₂ - t₁)) + (Ca' * L) ^ 2 * (t₂ - t₁)) :=
          mul_le_mul_of_nonneg_left (by linarith) hW
      _ = W * (Cd' ^ 2 * T ^ 2 + Ca' ^ 2) * L ^ 2 * (t₂ - t₁) := by ring
  have g1 := gen _ CdN CaN hW1
  have g2 := gen _ CdN CaN hW2
  have g3 : (2 * q) * ((Cp2 * L * Dt) ^ 2 * (t₂ - t₁) ^ 2 * T + (Cp1 * L * Dt) ^ 2 * (t₂ - t₁)) ≤
      2 * q * Dt ^ 2 * (Cp2 ^ 2 * T ^ 2 + Cp1 ^ 2) * L ^ 2 * (t₂ - t₁) := by
    have := gen (2 * q * Dt ^ 2) Cp2 Cp1 (by positivity)
    calc (2 * q) * ((Cp2 * L * Dt) ^ 2 * (t₂ - t₁) ^ 2 * T + (Cp1 * L * Dt) ^ 2 * (t₂ - t₁))
        = 2 * q * Dt ^ 2 * ((Cp2 * L) ^ 2 * (t₂ - t₁) ^ 2 * T + (Cp1 * L) ^ 2 * (t₂ - t₁)) := by ring
      _ ≤ _ := this
  rw [hLL] at g1 g2 g3
  have hz : s57pCz T q qN τ CaN CdN Cp1 Cp2 Dt * oscEigenvalue d α ^ ((J : ℝ) - m) * (t₂ - t₁) =
      (Real.sqrt (2 * qN) - Real.sqrt (2 * q)) ^ 2 * (CdN ^ 2 * T ^ 2 + CaN ^ 2) * oscEigenvalue d α ^ ((J : ℝ) - m) * (t₂ - t₁) +
      2 * q * τ * (CdN ^ 2 * T ^ 2 + CaN ^ 2) * oscEigenvalue d α ^ ((J : ℝ) - m) * (t₂ - t₁) +
      2 * q * Dt ^ 2 * (Cp2 ^ 2 * T ^ 2 + Cp1 ^ 2) * oscEigenvalue d α ^ ((J : ℝ) - m) * (t₂ - t₁) := by
    unfold s57pCz; ring
  linarith [p1.trans g1, p2.trans g2, p3.trans g3, hz]

end HRS.MS.FixEq
