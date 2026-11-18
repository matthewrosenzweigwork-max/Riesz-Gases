import HRS.MS.Fp81S21CovBlockAPI3
import HRS.MS.Fp81S21CovSum4

/-!
# S2.1(iii), packet 16b: summed physical covariance block domination

This theorem sums the actual packet-15 `WindowCovarianceBlockContract` bounds.
The dual-norm measurability needed for the tsum/lintegral exchange is an
explicit restricted-measure hypothesis, as required by the packet-16 review
note. The interval's shared endpoints are assigned by the half-open source
partition proved in `CovSum4`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas
open HRS.MS.GenPath HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL
open HRS.MS.R2WinOrb HRS.MS.FixEq

/-- Sum the physical covariance block norms into one interval-local weighted
source integral. The constant is independent of the localization set and of
`z`; the source is finite by `IsR2L1F`. AEMeasurability of `dualNormE` on the
physical source interval is stated explicitly. -/
theorem fp81s21_window_covariance_blocks_tsum_weighted
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c • ψ) =
          propagatorW C u t φ + c • propagatorW C u t ψ)
    (I : Set ℝ) (hI : MeasurableSet I)
    (hblocks : ∀ k, fp81s21_WindowCovarianceBlockContract D hlin I k)
    (hdual : AEMeasurable (fun v => dualNormE r P (z v))
      (volume.restrict (Icc (0 : ℝ) (a + H)))) :
    (∑' k, ‖fp81s21_blockValue D I k‖ₑ ≤
      (ENNReal.ofReal ((3 + Real.sqrt H) ^ 2 * fp81s21_blockC0) *
        ENNReal.ofReal |2 * C.ν| *
        ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r *
          (fp81s21_windowCovBlockAmp d r H Cmix) ^ 2))) *
        (∫⁻ v in I ∩ Ioc (0 : ℝ) (a + H),
          dualNormE r P (z v) * ENNReal.ofReal
            (Real.exp (-2 * cdec * max (a - v) 0)))) ∧
      (∑' k, ‖fp81s21_blockValue D I k‖ₑ < ∞) ∧
      (∫⁻ v in I ∩ Ioc (0 : ℝ) (a + H),
        dualNormE r P (z v) * ENNReal.ofReal
          (Real.exp (-2 * cdec * max (a - v) 0)) < ∞) := by
  let T : Set ℝ := Icc (0 : ℝ) (a + H)
  let S : Set ℝ := I ∩ Ioc (0 : ℝ) (a + H)
  let w : ℝ → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (Real.exp (-2 * cdec * max (a - v) 0))
  let g : ℝ → ℝ≥0∞ := T.indicator
    (fun v => dualNormE r P (z v) * w v)
  let Bhalf : ℕ → Set ℝ := fun k =>
    Ioc (k : ℝ) ((k : ℝ) + 1) ∩ S
  let Bclosed : ℕ → Set ℝ := fun k =>
    fp81s21_windowLocalBlock a H k ∩ I
  let amp : ℝ := fp81s21_windowCovBlockAmp d r H Cmix
  let A : ℝ≥0∞ := ENNReal.ofReal |2 * C.ν|
  let B0 : ℝ := s57pC d r P * ((d : ℝ) * 2 ^ r * amp ^ 2)
  let B : ℝ≥0∞ := ENNReal.ofReal B0
  let K0 : ℝ≥0∞ := ENNReal.ofReal ((3 + Real.sqrt H) ^ 2 * fp81s21_blockC0)
  let Kfac : ℝ≥0∞ := A * B
  let K : ℝ≥0∞ := K0 * Kfac
  have hT : MeasurableSet T := measurableSet_Icc
  have hS : MeasurableSet S := hI.inter measurableSet_Ioc
  have hSpos : S ⊆ Ioi 0 := by
    intro v hv
    exact hv.2.1
  have hST : S ⊆ T := by
    intro v hv
    exact ⟨le_of_lt hv.2.1, hv.2.2⟩
  have hdualFinite : (∫⁻ v in T, dualNormE r P (z v)) < ∞ := by
    have hz := D.fp81s21_hz
    unfold IsR2L1F at hz
    exact hz.2.2
  have hwmeas : Measurable w := by
    fun_prop
  have hweighted : AEMeasurable
      (fun v => dualNormE r P (z v) * w v) (volume.restrict T) :=
    hdual.mul (hwmeas.aemeasurable.restrict)
  have hg : AEMeasurable g volume :=
    (aemeasurable_indicator_iff hT).2 hweighted
  have hwle : ∀ v, w v ≤ 1 := by
    intro v
    have hexp : Real.exp (-2 * cdec * max (a - v) 0) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hmax : 0 ≤ max (a - v) 0 := le_max_right _ _
      nlinarith [D.fp81s21_hcdec]
    calc
      w v ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hexp
      _ = 1 := by simp [w]
  have hsource : (∫⁻ v in S, g v) < ∞ := by
    have hmono : (∫⁻ v in S, g v) ≤ ∫⁻ v in T, dualNormE r P (z v) := by
      calc
        (∫⁻ v in S, g v) = ∫⁻ v, S.indicator g v ∂volume :=
          (lintegral_indicator hS g).symm
        _ ≤ ∫⁻ v, T.indicator (fun v => dualNormE r P (z v)) v ∂volume := by
          apply lintegral_mono
          intro v
          by_cases hv : v ∈ S
          · have hvT := hST hv
            have hmul : dualNormE r P (z v) * w v ≤ dualNormE r P (z v) := by
              calc
                _ = w v * dualNormE r P (z v) := mul_comm _ _
                _ ≤ 1 * dualNormE r P (z v) :=
                  mul_le_mul_left (hwle v) (dualNormE r P (z v))
                _ = _ := one_mul _
            simp [Set.indicator, hv, hvT, g, hmul]
          · simp [Set.indicator, hv]
        _ = ∫⁻ v in T, dualNormE r P (z v) :=
          lintegral_indicator hT _
    exact lt_of_le_of_lt hmono hdualFinite
  have hBhalf : ∀ k, MeasurableSet (Bhalf k) := by
    intro k
    exact measurableSet_Ioc.inter hS
  have hBclosed : ∀ k, MeasurableSet (Bclosed k) := by
    intro k
    exact (measurableSet_Icc.inter measurableSet_Icc).inter hI
  have hBsubset : ∀ k, Bhalf k ⊆ Bclosed k := by
    intro k v hv
    rcases hv with ⟨hvBlock, hvSource⟩
    rcases hvSource with ⟨hvI, hvT⟩
    change v ∈ Ioc (0 : ℝ) (a + H) at hvT
    change v ∈ fp81s21_windowLocalBlock a H k ∩ I
    exact ⟨⟨⟨le_of_lt hvBlock.1, hvBlock.2⟩,
      ⟨le_of_lt hvT.1, hvT.2⟩⟩, hvI⟩
  have hpartition :
      ∫⁻ v, ∑' k, (Bhalf k).indicator g v ∂volume = ∫⁻ v in S, g v := by
    simpa only [Bhalf] using fp81s21_lintegral_natUnitBlocks_eq g S hS hSpos
  have hB0 : 0 ≤ B0 := by
    dsimp [B0]
    exact mul_nonneg (s57pC_nonneg d r P) (by positivity)
  have hfactor : ∀ v,
      ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r *
          (amp ^ 2 * Real.exp (-2 * cdec * max (a - v) 0)))) =
        B * w v := by
    intro v
    have hreal : s57pC d r P * ((d : ℝ) * 2 ^ r *
        (amp ^ 2 * Real.exp (-2 * cdec * max (a - v) 0))) =
        B0 * Real.exp (-2 * cdec * max (a - v) 0) := by
      dsimp [B0]
      ring
    rw [hreal, ENNReal.ofReal_mul hB0]
  have hconstfinite : K < ∞ := by
    dsimp [K, Kfac, K0, A, B]
    apply ENNReal.mul_lt_top
    · exact ENNReal.ofReal_lt_top
    · apply ENNReal.mul_lt_top <;> exact ENNReal.ofReal_lt_top
  have hblock : ∀ k,
      ‖fp81s21_blockValue D I k‖ₑ ≤ K * (∫⁻ v in Bhalf k, g v) := by
    intro k
    have hClosedT : ∀ v ∈ Bclosed k, v ∈ T := by
      intro v hv
      have hw : v ∈ fp81s21_windowLocalBlock a H k := hv.1
      change v ∈ Icc (k : ℝ) ((k : ℝ) + 1) ∩ T at hw
      exact hw.2
    have hmem : ∀ v, v ≠ (k : ℝ) → v ≠ 0 →
        (v ∈ Bhalf k ↔ v ∈ Bclosed k) := by
      intro v hvk hv0
      constructor
      · rintro ⟨⟨hlo, hhi⟩, ⟨hvI, ⟨hTlo, hThi⟩⟩⟩
        exact ⟨⟨⟨hlo.le, hhi⟩, ⟨le_of_lt hTlo, hThi⟩⟩, hvI⟩
      · rintro ⟨⟨⟨hlo, hhi⟩, ⟨hTlo, hThi⟩⟩, hvI⟩
        have hlo' : (k : ℝ) < v := lt_of_le_of_ne hlo hvk.symm
        have hTlo' : 0 < v := lt_of_le_of_ne hTlo hv0.symm
        exact ⟨⟨hlo', hhi⟩, ⟨hvI, ⟨hTlo', hThi⟩⟩⟩
    have hnotk : ∀ᵐ v ∂volume, v ≠ (k : ℝ) := by
      rw [ae_iff]
      simpa using (measure_singleton (k : ℝ))
    have hnot0 : ∀ᵐ v ∂volume, v ≠ (0 : ℝ) := by
      rw [ae_iff]
      simpa using (measure_singleton (0 : ℝ))
    have hindicator :
        (Bhalf k).indicator g =ᵐ[volume] (Bclosed k).indicator g := by
      filter_upwards [hnotk, hnot0] with v hvk hv0
      have hvEq := hmem v hvk hv0
      by_cases hv : v ∈ Bhalf k
      · have hv' := hvEq.mp hv
        simp [Set.indicator, hv, hv']
      · have hv' : v ∉ Bclosed k := fun h => hv (hvEq.mpr h)
        simp [Set.indicator, hv, hv']
    have hClosedSource :
        (∫⁻ v in Bclosed k, g v) = (∫⁻ v in Bhalf k, g v) := by
      calc
        (∫⁻ v in Bclosed k, g v) =
            ∫⁻ v, (Bclosed k).indicator g v ∂volume :=
              (lintegral_indicator (hBclosed k) g).symm
        _ = ∫⁻ v, (Bhalf k).indicator g v ∂volume :=
              lintegral_congr_ae hindicator.symm
        _ = ∫⁻ v in Bhalf k, g v := lintegral_indicator (hBhalf k) g
    have hphys :
        (∫⁻ v in Bclosed k,
          A * dualNormE r P (z v) *
            ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r *
              (amp ^ 2 * Real.exp (-2 * cdec * max (a - v) 0))))) =
          Kfac * (∫⁻ v in Bclosed k, g v) := by
      calc
        _ = ∫⁻ v in Bclosed k, Kfac * g v := by
          apply setLIntegral_congr_fun (hBclosed k)
          intro v hv
          have hvT := hClosedT v hv
          change A * dualNormE r P (z v) *
              ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r *
                (amp ^ 2 * Real.exp (-2 * cdec * max (a - v) 0)))) =
            Kfac * g v
          simp only [g, Set.indicator_of_mem hvT]
          rw [hfactor v]
          dsimp [Kfac]
          ac_rfl
        _ = Kfac * (∫⁻ v in Bclosed k, g v) :=
          lintegral_const_mul'' Kfac (hg.restrict)
    have hmain := (hblocks k).weighted_bound
    calc
      ‖fp81s21_blockValue D I k‖ₑ ≤
          K0 * (∫⁻ v in Bclosed k,
            A * dualNormE r P (z v) *
              ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r *
                (amp ^ 2 * Real.exp (-2 * cdec * max (a - v) 0))))) := by
        simpa [K0, A, amp, Bclosed, fp81s21_windowCovBlockAmp] using hmain
      _ = K * (∫⁻ v in Bhalf k, g v) := by
        rw [hphys, hClosedSource]
        dsimp [K]
        ac_rfl
  have hsum := fp81s21_tsum_norm_le_integral_of_blockwise
    (x := fun k => fp81s21_blockValue D I k) (f := g) (B := Bhalf)
    (S := S) (K := K) hconstfinite hg hBhalf hblock hpartition.le hsource
  have hsourceEq : (∫⁻ v in S, g v) =
      ∫⁻ v in S, dualNormE r P (z v) * w v := by
    apply setLIntegral_congr_fun hS
    intro v hv
    simp [g, hST hv]
  refine ⟨?_, hsum.2, ?_⟩
  · calc
      (∑' k, ‖fp81s21_blockValue D I k‖ₑ) ≤
          K * (∫⁻ v in S, g v) := hsum.1
      _ = (ENNReal.ofReal ((3 + Real.sqrt H) ^ 2 * fp81s21_blockC0) *
          ENNReal.ofReal |2 * C.ν| *
            ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r * amp ^ 2))) *
          (∫⁻ v in S, dualNormE r P (z v) *
            ENNReal.ofReal (Real.exp (-2 * cdec * max (a - v) 0))) := by
        rw [hsourceEq]
        dsimp [K, Kfac, K0, A, B, B0, w]
        ac_rfl
  · rw [← hsourceEq]
    exact hsource

#print axioms fp81s21_window_covariance_blocks_tsum_weighted

end HRS.Fp81.S21

end
