import HRS.MS.Fp81S21IidIndexed
import HRS.MS.Fp81S21QwinUniform
import HRS.MS.Fp81S21InitialIid
import HRS.MS.S21H2_S30C

set_option autoImplicit false
set_option maxHeartbeats 400000

/-!
# Zero-coupling cosine-family instance of the indexed iid core

The qwin producer supplies a common weighted feature envelope for every
nonnegative shift. Its squared envelope gives common norm and projection-tail
bounds, so the indexed Edgeworth threshold is selected before the shift.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS.Whole
open HRS.MS.R26T3
open S45

/-- Uniform indexed Edgeworth expansion for the actual initial cosine features
at zero coupling. The laws in the integral are the actual zero-coupling Gibbs
laws, and the threshold is common to every nonnegative shift. -/
theorem fp81s21_iid_indexed_qwin (p : Parameters) (hγ : p.γ = 0) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ G : {a : ℝ // 0 ≤ a} → Measure SeqL2,
          (∀ a, IsProbabilityMeasure (G a)) →
          (∀ a, IsCenteredGaussian (G a)) →
          (∀ a x y, covarianceBilin (G a) x y =
            covarianceBilin
              ((r26t3_mu R 0).map
                (s21h2_Y (r26t3_qwin R a.1) (r26t3_mu R 0))) x y) →
          ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ,
            ∀ N : ℕ, N₀ ≤ N → 2 ≤ N →
              ∀ a : {a : ℝ // 0 ≤ a},
                ∀ Φ : SeqL2 → ℝ, Φ ∈ CbUnitBall SeqL2 5 →
                  |Real.sqrt N *
                    ((∫ X, Φ (featureVec (r26t3_qwin R a.1)
                        (r26t3_marg R N) X) ∂(r26t3_Q R N)) -
                      ∫ z, Φ z ∂(G a)) -
                    (1 / 6) * ∫ z, ∫ x,
                      iteratedFDeriv ℝ 3 Φ z
                        ![s21h2_Y (r26t3_qwin R a.1) (r26t3_mu R 0) x,
                          s21h2_Y (r26t3_qwin R a.1) (r26t3_mu R 0) x,
                          s21h2_Y (r26t3_qwin R a.1) (r26t3_mu R 0) x]
                        ∂(r26t3_mu R 0) ∂(G a)| ≤ ε := by
  obtain ⟨δ0, hδ0, hδ0half, hwindow⟩ := fp81s21_qwin_uniform p
  refine ⟨δ0, hδ0, hδ0half, fun δ hδ hδle R G hGp hGg hcov => ?_⟩
  have hδhalf : δ ≤ 1 / 2 := le_trans hδle hδ0half
  set μ := r26t3_mu R 0
  have hdens := (r26t3_reference_data p δ hδ hδhalf R).2.2.1 0 le_rfl
  have hμprob : IsProbabilityMeasure μ := by
    dsimp [μ, r26t3_mu]
    exact s11iid_prob hdens.1.nonneg hdens.1.integral_one
  letI : IsProbabilityMeasure μ := hμprob
  letI : ∀ a : {a : ℝ // 0 ≤ a}, IsProbabilityMeasure (G a) := hGp
  obtain ⟨Cq, hCq, hqwin⟩ := hwindow δ hδ hδle R
  let q : {a : ℝ // 0 ≤ a} → ℕ → Euc p.d → ℝ :=
    fun a => r26t3_qwin R a.1
  let Y : {a : ℝ // 0 ≤ a} → Euc p.d → SeqL2 :=
    fun a x => s21h2_Y (q a) μ x
  have hq : ∀ a : {a : ℝ // 0 ≤ a},
      IsSummableFeatureFamily (r26t3_J p.d) (q a) := by
    intro a
    exact (hqwin a.1 a.2).1
  have hqbound : ∀ a : {a : ℝ // 0 ≤ a}, ∀ j,
      cbNorm (r26t3_J p.d) (q a j) ≤ Cq * r26t3_feature_weight p.d j := by
    intro a j
    exact (hqwin a.1 a.2).2 j
  have hweight0 : ∀ j, 0 ≤ r26t3_feature_weight p.d j := by
    intro j
    dsimp [r26t3_feature_weight]
    apply mul_nonneg
    · apply Real.rpow_nonneg
      positivity
    · exact Real.rpow_nonneg (oscEigenvalue_pos _).le _
  let w : ℕ → ℝ := fun j =>
    (2 * Cq * r26t3_feature_weight p.d j) ^ 2
  have hw : Summable w := by
    have hs := S45.s45_summable_sq hweight0 (fp81s21_qwin_weight_summable p)
    have hs' := hs.mul_left ((2 * Cq) ^ 2)
    convert hs' using 1 <;> ext j <;> simp [w, mul_pow, mul_assoc] <;> ring
  let C : ℝ := Real.sqrt (∑' j, w j)
  have hC : ∀ a : {a : ℝ // 0 ≤ a}, ∀ x, ‖Y a x‖ ≤ C := by
    intro a x
    change ‖s21h2_Y (q a) μ x‖ ≤ Real.sqrt (∑' j, w j)
    refine Real.le_sqrt_of_sq_le ?_
    rw [← u11_norm_sq]
    refine Summable.tsum_le_tsum (fun j => ?_) (u11_coord_summable _) hw
    rw [s21h2_coord (hq a) μ x j]
    have habs := s21h2_abs_le (hq a) μ x j
    have hb := hqbound a j
    have habs' :
        |q a j x - HRS.Whole.pair μ (q a j)| ≤
          2 * Cq * r26t3_feature_weight p.d j := by
      calc
        |q a j x - HRS.Whole.pair μ (q a j)| ≤
            2 * cbNorm (r26t3_J p.d) (q a j) := habs
        _ ≤ 2 * Cq * r26t3_feature_weight p.d j := by nlinarith
    calc
      (q a j x - HRS.Whole.pair μ (q a j)) ^ 2 =
          |q a j x - HRS.Whole.pair μ (q a j)| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * Cq * r26t3_feature_weight p.d j) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs' 2
      _ = w j := by rfl
  have hYc : ∀ a : {a : ℝ // 0 ≤ a}, Continuous (Y a) := by
    intro a
    exact s21h2_continuous (hq a) μ
  have hcent : ∀ a : {a : ℝ // 0 ≤ a}, ∫ x, Y a x ∂μ = 0 := by
    intro a
    exact s21h2_centered (hq a) μ
  have hYw : ∀ a : {a : ℝ // 0 ≤ a}, ∀ n x,
      (inner ℝ (S45.s45_seqBasis n) (Y a x)) ^ 2 ≤ w n := by
    intro a n x
    have habs := s21h2_abs_le (hq a) μ x n
    have hb := hqbound a n
    have habs' :
        |q a n x - HRS.Whole.pair μ (q a n)| ≤
          2 * Cq * r26t3_feature_weight p.d n := by
      calc
        |q a n x - HRS.Whole.pair μ (q a n)| ≤
            2 * cbNorm (r26t3_J p.d) (q a n) := habs
        _ ≤ 2 * Cq * r26t3_feature_weight p.d n := by nlinarith
    rw [s21h2_inner (hq a) μ]
    calc
      (q a n x - HRS.Whole.pair μ (q a n)) ^ 2 =
          |q a n x - HRS.Whole.pair μ (q a n)| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * Cq * r26t3_feature_weight p.d n) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs' 2
      _ = w n := by rfl
  have hcov' : ∀ a : {a : ℝ // 0 ≤ a}, ∀ x y,
      covarianceBilin (G a) x y = covarianceBilin (μ.map (Y a)) x y := by
    intro a x y
    simpa [Y, q, μ] using hcov a x y
  have hcore := fp81s21_iid_indexed_core μ S45.s45_seqBasis Y
    hYc C hC hcent w hw hYw G hGg hcov'
  have hQ : ∀ N, r26t3_Q R N = Measure.pi fun _ : Fin N => μ := by
    intro N
    simpa [μ] using fp81s21_initial_iid_Q hδ hδhalf R hγ N
  have hMarg : ∀ N, 1 ≤ N → r26t3_marg R N = μ := by
    intro N hN
    change HRS.Whole.firstMarginal (r26t3_Q R N) = μ
    rw [hQ N]
    exact s21h2_marg_pi N hN μ
  have hfeature : ∀ (a : {a : ℝ // 0 ≤ a}) (N : ℕ), 2 ≤ N →
      (fun X => featureVec (q a) (r26t3_marg R N) X) =
        fun X => HRS.StaticLimitAux.Ssum (Y a) N X := by
    intro a N hN
    funext X
    change featureVec (q a) (r26t3_marg R N) X =
      HRS.StaticLimitAux.Ssum (s21h2_Y (q a) μ) N X
    rw [hMarg N (by omega)]
    exact s21h2_W_eq (hq a) μ N (by omega) X
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hcore ε hε
  refine ⟨N₀, fun N hN0 hN2 a Φ hΦ => ?_⟩
  have h := hN₀ N hN0 (by omega) a Φ hΦ
  simpa [hQ N, hfeature a N hN2, Y, q, μ] using h

#print axioms fp81s21_iid_indexed_qwin

end HRS.Fp81.S21
