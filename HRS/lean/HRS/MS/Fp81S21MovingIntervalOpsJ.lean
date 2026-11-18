import HRS.MS.Fp81S21MovingIntervalOpsD
import HRS.MS.Fp81S21WindowFeature4
import HRS.MS.Fp81S21CovBlockAPI2
import HRS.MS.Fp81S21WindowCovId
import HRS.MS.Fp81S21CovMeasure

/-! Uniform moving window-orbit input and coefficient interval operators. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp
open HRS.MS.R2WinOrb HRS.MS.R2WinOrbNL HRS.MS.R2WinErr
open HRS.MS.ProClosureS111 HRS.MS.S111K2 HRS.MS.S111K4J01

/-- The common all-time moving orbit estimates supply the window-orbit input
with a single square-summable amplitude, independently of the window start. -/
theorem fp81s21_moving_window_orbit_input
    (p : Parameters) {δ Co co : ℝ} (R : Trajectory p δ)
    (hclaims : S103nOrbitClaims p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁) :
    Summable (fun α : MultiIndex p.d => (|Co| * s103_b p.d α) ^ 2) ∧
      S111k2WindowOrbitInput (r26t3_coeff R) (wholeSpaceIndex p.d) co
        (r26t6_coreOrder p.d) (fun α => |Co| * s103_b p.d α) := by
  have hsq : Summable (fun α : MultiIndex p.d => (|Co| * s103_b p.d α) ^ 2) := by
    have hs := (stationary_weight_square_summable
      (by have := p.hd; omega : 1 ≤ p.d)).mul_left (|Co| ^ 2)
    convert hs using 1 <;> ext α <;> simp [mul_pow]
  refine ⟨hsq, ?_⟩
  refine {
    nonneg := fun α => mul_nonneg (abs_nonneg _) (s103_b_nonneg α)
    classical := ?_
    grad := ?_
    terminal_derivative := ?_
    orbit := fun H hH => fp81s21_covLocal_orbit_summable p R hH hclaims hterm
    linear := ?_ }
  · intro α t ht
    have hH : 0 ≤ t + 1 := by linarith
    have horb := s104b_orbit_of_termRegGen hterm R.admissible R.resulting α (t + 1) hH
    exact ⟨horb.ex0 t ⟨ht, by linarith⟩, horb.ex1 t ⟨ht, by linarith⟩⟩
  · intro α t ht
    have hraw := hclaims R.ε R.ψ R.ρ R.admissible R.resulting α t ht
    have hm : Co * s103_b p.d α ≤ |Co| * s103_b p.d α :=
      mul_le_mul_of_nonneg_right (le_abs_self Co) (s103_b_nonneg α)
    constructor
    · exact r2OrbitGrad_order_mono (by unfold r26t6_coreOrder; omega)
        (s103_orbitGrad_mono hraw.2.1 hm)
    · exact r2OrbitGrad_order_mono (by unfold r26t6_coreOrder; omega)
        (s103_orbitGrad_mono hraw.2.2.2.1 hm)
  · intro α v t hv hvt x
    have hH : 0 < t + 1 := by linarith
    have h := fp81s21_moving_terminal_derivative_within p R hH hterm α v
      ⟨hv, by linarith⟩ t ⟨hvt, by linarith⟩ (by linarith) x
    apply h.mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      show Iio (t + 1) ∈ 𝓝[Ici v] t from
        nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))] with z hz1 hz2
    exact ⟨hz1, hz2.le⟩
  · intro v t hv hvt φ ψ c hφ hψ
    exact fp81s21_S102Lin p R t v t hv hvt le_rfl φ ψ c hφ hψ

/-- Uniform interval operators for the moving trajectory coefficient. The
radius is chosen before the trajectory, and both constants before the start. -/
theorem fp81s21_moving_interval_operators (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ E : r26t6_WeightedChart p.d (r26t6_coreOrder p.d) (r26t6_coreWeight p.d),
      ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ a : ℝ, 0 ≤ a →
        Nonempty (r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K) := by
  obtain ⟨δc, Co, co, hδc, hδch, hco, hcommon⟩ := fp81s21_common_radius p
  obtain ⟨δs, hδs, hδsh, hstd⟩ := fp81s21_moving_std p
  refine ⟨min δc δs, lt_min hδc hδs, (min_le_left _ _).trans hδch, ?_⟩
  intro δ hδ hδle R E
  have hδc' := hδle.trans (min_le_left δc δs)
  have hδs' := hδle.trans (min_le_right δc δs)
  obtain ⟨hclaims, -, hterm, -⟩ := hcommon δ hδ hδc' R.ρβ R.thermal
  obtain ⟨hsq, hW⟩ := fp81s21_moving_window_orbit_input p R hclaims hterm
  let b : MultiIndex p.d → ℝ := fun α => |Co| * s103_b p.d α
  let S : ℝ := ∑' α, b α ^ 2
  have hS : 0 ≤ S := tsum_nonneg fun _ => sq_nonneg _
  have hPw : (p.d : ℝ) / 2 + 1 < r26t6_coreWeight p.d := by
    unfold r26t6_coreWeight
    linarith [(Nat.cast_nonneg p.d : (0 : ℝ) ≤ p.d)]
  have hr : (p.d : ℝ) / 2 + 2 < r26t6_coreOrder p.d := by
    unfold r26t6_coreOrder
    push_cast
    linarith [(Nat.cast_nonneg p.d : (0 : ℝ) ≤ p.d)]
  obtain ⟨K, hK, hO⟩ := k4_coefficient_interval_operators p.d (r26t6_coreOrder p.d)
    p.hd p.T (r26t6_coreWeight p.d) S co p.hT hPw hr hS hco
  refine ⟨co, K, hco, hK, ?_⟩
  intro a ha
  obtain ⟨c, hc⟩ := hstd δ hδ hδs' R a ha
  have hP : (p.d : ℝ) < 2 * r26t6_coreWeight p.d := by linarith
  have hH : 0 < a + p.T := by linarith [p.hT]
  have hchart := fp81s21_moving_charted_orbits p R hH hc hP E
  obtain ⟨O⟩ := hO (nativeChartOfFrozen E) (r26t3_coeff R) b hsq le_rfl hW a ha hchart
  exact ⟨frozenIntervalOfNative E O⟩

/-- The covariance map has the packet-16 window value for its own
L¹ coefficient representative, including the physical noise factor once. -/
theorem fp81s21_interval_covariance_window_value
    {d r : ℕ} {Pw T a c K : ℝ} {C : WholeCoeff d}
    {E : r26t6_WeightedChart d r Pw}
    (O : r26t6_IntervalOperators E C T a c K)
    (q : r26t6_TimeCoeff (a + T)) {v w : ℝ}
    (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w ≤ a + T) :
    fp81s21_IsWindowJValue C (wholeSpaceIndex d) T a
      (r26t6_coefficientField E q) (Ioc v w)
      ((O.covariance v w q : projTensor (R2X d T) 2) : TensorDual (R2X d T) 2) := by
  refine ⟨(O.covariance v w q).property, ?_⟩
  intro ta tb φ ψ l₁ l₂ hφ hψ hta htb hl₁ hl₂
  have h := O.covariance_coordinate q v w hv hvw hw
    ⟨ta, hta⟩ ⟨tb, htb⟩ φ ψ l₁ l₂ hφ hψ
  apply h
  · intro z
    simpa [r2PathAt, hta] using hl₁ z
  · intro z
    simpa [r2PathAt, htb] using hl₂ z

/-- An interval map agrees with the packet-16 measure when the chosen
L¹ representative agrees with the physical field on the tested products. -/
theorem fp81s21_interval_covariance_eq_physical
    {d r : ℕ} {Pw T a c K Cmix cdec : ℝ} {C : WholeCoeff d}
    {E : r26t6_WeightedChart d r Pw}
    (O : r26t6_IntervalOperators E C T a c K)
    (q : r26t6_TimeCoeff (a + T))
    {z : ℝ → (Euc d → ℝ) → ℝ}
    (D : fp81s21_WindowLocalInput C (wholeSpaceIndex d) T a r Pw z Cmix cdec)
    {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w ≤ a + T)
    (hphysical : fp81s21_IsWindowJValue C (wholeSpaceIndex d) T a z (Ioc v w)
      ((fp81s21_window_covariance_measure D v w : projTensor (R2X d T) 2) :
        TensorDual (R2X d T) 2))
    (hrep : ∀ ta tb : ℝ, ∀ φ ψ : Euc d → ℝ,
      IsR2DualCombo (wholeSpaceIndex d) φ → IsR2DualCombo (wholeSpaceIndex d) ψ →
      ta ∈ Icc (0 : ℝ) T → tb ∈ Icc (0 : ℝ) T →
      ∀ᵐ s ∂volume.restrict (Ioc v w ∩ Icc 0 (min (a + ta) (a + tb))),
        r26t6_coefficientField E q s (fun x => inner ℝ
          (gradient (propagatorW C s (a + ta) φ) x)
          (gradient (propagatorW C s (a + tb) ψ) x)) =
        z s (fun x => inner ℝ (gradient (propagatorW C s (a + ta) φ) x)
          (gradient (propagatorW C s (a + tb) ψ) x))) :
    O.covariance v w q = fp81s21_window_covariance_measure D v w := by
  have hO := fp81s21_interval_covariance_window_value O q hv hvw hw
  have hO' : fp81s21_IsWindowJValue C (wholeSpaceIndex d) T a z (Ioc v w)
      ((O.covariance v w q : projTensor (R2X d T) 2) : TensorDual (R2X d T) 2) := by
    refine ⟨hO.1, ?_⟩
    intro ta tb φ ψ l₁ l₂ hφ hψ hta htb hl₁ hl₂
    have hcoord := hO.2 ta tb φ ψ l₁ l₂ hφ hψ hta htb hl₁ hl₂
    rw [hcoord]
    congr 1
    exact integral_congr_ae (hrep ta tb φ ψ hφ hψ hta htb)
  apply Subtype.ext
  exact fp81s21_window_J_unique C D.fp81s21_hH z (Ioc v w) hO' hphysical

#print axioms fp81s21_interval_covariance_eq_physical
#print axioms fp81s21_interval_covariance_window_value
#print axioms fp81s21_moving_window_orbit_input
#print axioms fp81s21_moving_interval_operators
end HRS.Fp81.S21
end
