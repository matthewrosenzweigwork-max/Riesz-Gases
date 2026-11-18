import HRS.MS.Fp81S21EmbedField4
import HRS.MS.S21G2_W01

/-! Distance bridge and normalized dense tests for compactness. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111
  HRS.MS.FixEq

/-- The chart and weighted-jet distances agree on compact smooth tests. -/
theorem fp81s21_embedField_chartJet_dist
    {d q : ℕ} {Pw : ℝ}
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (f g : Euc d → ℝ) (hf : IsR2Test f) (hg : IsR2Test g) :
    dist (Es.encode f) (Es.encode g) =
      dist (r26t3_jet q (Pw + 2) f) (r26t3_jet q (Pw + 2) g) := by
  have hwf : IsR2WeightedTest q (Pw + 2) f :=
    weightedTestSubmodule_iff.1
      (weighted_test_of_compact_smooth (r := q) (Pw := Pw + 2) hPs hf)
  have hwg : IsR2WeightedTest q (Pw + 2) g :=
    weightedTestSubmodule_iff.1
      (weighted_test_of_compact_smooth (r := q) (Pw := Pw + 2) hPs hg)
  have hwd : IsR2WeightedTest q (Pw + 2) (f - g) :=
    weightedTestSubmodule_iff.1
      (weighted_test_of_compact_smooth (r := q) (Pw := Pw + 2) hPs
        ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩)
  have henc : Es.encode f - Es.encode g = Es.encode (f - g) := by
    simpa [fp81s21_embedField_weakTestEncode] using
      (map_sub (fp81s21_embedField_weakTestEncode hPs Es)
        (⟨f, hf⟩ : compactSmoothSubmodule d) ⟨g, hg⟩).symm
  have hjet : r26t3_jet q (Pw + 2) (f - g) =
      r26t3_jet q (Pw + 2) f - r26t3_jet q (Pw + 2) g := by
    simpa [sub_eq_add_neg] using
      (r26t3_jet_linear (Pw + 2) f g hwf hwg (-1))
  have hnorm := fp81s21_embedField_chartJet_norm hPs Es (f - g)
    ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩
  calc
    dist (Es.encode f) (Es.encode g) = ‖Es.encode f - Es.encode g‖ := dist_eq_norm _ _
    _ = ‖Es.encode (f - g)‖ := by rw [henc]
    _ = ‖r26t3_jet q (Pw + 2) (f - g)‖ := hnorm.1
    _ = ‖r26t3_jet q (Pw + 2) f - r26t3_jet q (Pw + 2) g‖ := by rw [hjet]
    _ = dist (r26t3_jet q (Pw + 2) f) (r26t3_jet q (Pw + 2) g) := (dist_eq_norm _ _).symm

/-- Every vector in the strong unit ball is approximated by a compact smooth
test whose strong weighted energy is at most one. The fixed rescaling keeps
the approximation inside the unit ball. -/
theorem fp81s21_embedField_normalized_denseTest
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (x : r26t6_Coeff) (hx : ‖x‖ ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : Euc d → ℝ, IsR2Test f ∧
      weightedSobolevE (q + 2) Pw f ≤ 1 ∧
      dist x (E.encode f) < 2 * δ := by
  have hdense : DenseRange
      (fun f : {f : Euc d → ℝ // IsR2Test f} => E.encode f) := by
    rw [DenseRange]
    exact E.dense
  obtain ⟨g, happrox⟩ := (Metric.denseRange_iff.1 hdense) x δ hδ
  have hdist : ‖x - E.encode g‖ < δ := by
    simpa [dist_eq_norm] using happrox
  have hnormg : ‖E.encode g‖ ≤ 1 + δ := by
    calc
      ‖E.encode g‖ = ‖x - (x - E.encode g)‖ := by congr 1 <;> abel
      _ ≤ ‖x‖ + ‖x - E.encode g‖ := norm_sub_le _ _
      _ ≤ 1 + δ := add_le_add hx hdist.le
  let c : ℝ := (1 + δ)⁻¹
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    rw [inv_le_one₀ (by linarith : (0 : ℝ) < 1 + δ)]
    linarith
  have hcprod : c * (1 + δ) = 1 := by
    dsimp [c]
    field_simp [show (1 + δ : ℝ) ≠ 0 by linarith]
  let g0 : compactSmoothSubmodule d := ⟨g, g.property⟩
  let f0 : compactSmoothSubmodule d := c • g0
  let f : Euc d → ℝ := f0
  have hf : IsR2Test f := f0.property
  have henc : E.encode f = c • E.encode g := by
    change fp81s21_embedField_strongTestEncode hP E f0 =
      c • fp81s21_embedField_strongTestEncode hP E g0
    exact map_smul (fp81s21_embedField_strongTestEncode hP E) c g0
  have hnormf : ‖E.encode f‖ ≤ 1 := by
    rw [henc, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    calc
      c * ‖E.encode g‖ ≤ c * (1 + δ) := mul_le_mul_of_nonneg_left hnormg hc0
      _ = 1 := hcprod
  have hwt : IsR2WeightedTest (q + 2) Pw f :=
    weightedTestSubmodule_iff.1
      (weighted_test_of_compact_smooth (r := q + 2) (Pw := Pw) hP hf)
  have henergyReal : (weightedSobolevE (q + 2) Pw f).toReal ≤ 1 := by
    rw [← E.norm f hwt]
    exact hnormf
  have henergy : weightedSobolevE (q + 2) Pw f ≤ 1 := by
    rw [← ENNReal.ofReal_toReal hwt.2.ne]
    simpa using ENNReal.ofReal_le_ofReal henergyReal
  have hcShrinkprod : (1 - c) * (1 + δ) = δ := by
    calc
      (1 - c) * (1 + δ) = 1 * (1 + δ) - c * (1 + δ) := by ring
      _ = (1 + δ) - 1 := by rw [hcprod, one_mul]
      _ = δ := by ring
  have hcShrink : dist (E.encode g) (c • E.encode g) ≤ δ := by
    rw [dist_eq_norm]
    have hdiff : E.encode g - c • E.encode g = (1 - c) • E.encode g := by module
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - c)]
    calc
      (1 - c) * ‖E.encode g‖ ≤ (1 - c) * (1 + δ) :=
        mul_le_mul_of_nonneg_left hnormg (by linarith)
      _ = δ := hcShrinkprod
  have hclose : dist x (E.encode f) < 2 * δ := by
    rw [henc]
    calc
      dist x (c • E.encode g) ≤ dist x (E.encode g) + dist (E.encode g) (c • E.encode g) :=
        dist_triangle _ _ _
      _ < δ + δ := by linarith [happrox, hcShrink]
      _ = 2 * δ := by ring
  exact ⟨f, hf, henergy, hclose⟩

#print axioms HRS.Fp81.S21.fp81s21_embedField_chartJet_dist
#print axioms HRS.Fp81.S21.fp81s21_embedField_normalized_denseTest

end HRS.Fp81.S21
