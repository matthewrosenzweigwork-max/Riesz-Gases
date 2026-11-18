import HRS.MS.Fp81S21EmbedField5
import HRS.MS.Fp81S21WeightedRellich17

/-! Transfer the test-core finite net to the full primal image of the unit ball. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111
  HRS.MS.FixEq

/-- The primal inclusion maps its closed unit ball into a totally bounded
set. Dense strong-chart approximants are normalized before applying the
weighted Rellich test-core net, and each net center is retained as a chart
coordinate. -/
theorem fp81s21_embedField_primal_image_finiteNet
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : Finset r26t6_Coeff, ∀ x : r26t6_Coeff, ‖x‖ ≤ 1 →
      ∃ z ∈ t,
        dist (fp81s21_embedField_primal hP hPs E Es x) z < ε := by
  classical
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C, R, hC, hR, hrellich⟩ :=
    fp81s21_weightedRellich_unitBall_finiteWeakNet
      (d := d) (q := q) (P := Pw) hPs
  obtain ⟨ρ, hρ, χ, hχs, hχc, hχone, hχzero, hχB, t, hcenters, hcover⟩ :=
    hrellich δ hδ
  have hrep : ∀ z ∈ t, ∃ g : Euc d → ℝ,
      IsR2Test g ∧ weightedSobolevE (q + 2) Pw g ≤ 1 ∧
      z = r26t3_jet q (Pw + 2) (fun x => χ x * g x) ∧
      weightedSobolevE (q + 2) Pw (fun x => χ x * g x) ≤ ENNReal.ofReal R := by
    intro z hz
    exact hcenters z hz
  choose g hgtest hgenergy hjet hcutenergy using hrep
  let tCoeff : Finset r26t6_Coeff := t.attach.image fun a =>
    Es.encode (fun x => χ x * g a.1 a.2 x)
  refine ⟨tCoeff, ?_⟩
  intro x hx
  obtain ⟨f, hftest, hfenergy, hxf⟩ :=
    fp81s21_embedField_normalized_denseTest hP E x hx δ hδ
  obtain ⟨z, hz, hnet⟩ := hcover f hftest hfenergy
  let a : {z : HRS.MS.R26T3.JetSpace d q (Pw + 2) // z ∈ t} := ⟨z, hz⟩
  let v : Euc d → ℝ := fun y => χ y * g a.1 a.2 y
  have hvtest : IsR2Test v := by
    exact ⟨hχs.mul (hgtest z hz).1, hχc.mul_right⟩
  have hmem : Es.encode v ∈ tCoeff := by
    change Es.encode v ∈ t.attach.image (fun b =>
      Es.encode (fun x => χ x * g b.1 b.2 x))
    apply Finset.mem_image.mpr
    exact ⟨a, Finset.mem_attach _ _, rfl⟩
  let K := fp81s21_embedField_primal hP hPs E Es
  have hKnorm : ‖K‖ ≤ 1 := fp81s21_embedField_primal_norm_le hP hPs E Es
  have hcontract : dist (K x) (K (E.encode f)) ≤ dist x (E.encode f) := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    calc
      ‖K (x - E.encode f)‖ ≤ ‖K‖ * ‖x - E.encode f‖ := K.le_opNorm _
      _ ≤ 1 * ‖x - E.encode f‖ :=
        mul_le_mul_of_nonneg_right hKnorm (norm_nonneg _)
      _ = ‖x - E.encode f‖ := by rw [one_mul]
  have htarget : dist (K (E.encode f)) (Es.encode v) < δ := by
    rw [fp81s21_embedField_primal_apply_test hP hPs E Es f hftest]
    rw [fp81s21_embedField_chartJet_dist hPs Es f v hftest hvtest]
    rw [← hjet z hz]
    exact hnet
  refine ⟨Es.encode v, hmem, ?_⟩
  calc
    dist (K x) (Es.encode v) ≤
        dist (K x) (K (E.encode f)) + dist (K (E.encode f)) (Es.encode v) :=
      dist_triangle _ _ _
    _ < 2 * δ + δ := by linarith [hcontract, hxf, htarget]
    _ < ε := by dsimp [δ]; nlinarith

#print axioms HRS.Fp81.S21.fp81s21_embedField_primal_image_finiteNet

end HRS.Fp81.S21
