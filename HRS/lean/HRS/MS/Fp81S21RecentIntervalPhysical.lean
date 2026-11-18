import HRS.MS.Fp81S21AvgPackageRetained
import HRS.MS.Fp81S21MovingIntervalOpsJ
import HRS.MS.Fp81S21VarCarrier
import HRS.MS.Fp81S21WickApprox39
import HRS.MS.Fp81S21GaussianFieldsRetained
import HRS.MS.Fp81S21JointT

/-! Origin-zero history identification for the recent interval operators.
The covariance lemma below retains its supplied history and proves all interval
identities on one probability-good set. The two-law physical assembly additionally
needs the selected centered quadratic histories and their spatial zero mass.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp

local instance fp81s21_recentInterval_history_measurable (H : ℝ) :
    MeasurableSpace (fp81s21_L2History H) := borel _
local instance fp81s21_recentInterval_history_borel (H : ℝ) :
    BorelSpace (fp81s21_L2History H) := ⟨rfl⟩

/-- The precise one-law interval obligation. `z` and `B` are the physical
covariance and drift fields; `zTest` records the original compact-test field
of the continuous linear version. The origin-zero and translated histories
represent the SAME `qη,qB`. Identities hold simultaneously for all recent
subintervals, hence also for every clipped cumulative interval.

This is a specification, not an existence theorem or an added hypothesis
of the proposed final export. -/
def fp81s21_RecentIntervalLaw
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (qη qB : ℝ → Ω → r26t6_Coeff)
    (z B zTest : ℝ → Ω → (Euc p.d → ℝ) → ℝ)
    (Mη MB a L c K : ℝ) (ha : 0 ≤ a) (hL : 0 < L)
    (O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K) : Prop :=
  let b := max (a - L) 0
  let H := L + p.T
  let hH : 0 < H := add_pos hL p.hT
  let hQ : 0 ≤ a + p.T := add_nonneg ha p.hT.le
  ∃ Uη0 UB0 : Ω → fp81s21_L2History (a + p.T),
  ∃ Uη UB : Ω → fp81s21_L2History H,
  ∃ X : Ω → fp81s21_SmoothCH H,
    fp81s21_TimeL2Rep P qη Mη 0 (a + p.T) Uη0 ∧
    fp81s21_TimeL2Rep P qB MB 0 (a + p.T) UB0 ∧
    fp81s21_TimeL2Rep P qη Mη b H Uη ∧
    fp81s21_TimeL2Rep P qB MB b H UB ∧
    Measurable X ∧ MemLp X 2 P ∧
    Uη =ᵐ[P] (fun ω => fp81s21_smoothPathToL2 H hH (X ω)) ∧
    (∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) H, ∀ f : Euc p.d → ℝ,
      IsR2Test f → fp81s21_chartAction E (X ω t) f = zTest (b + t) ω f) ∧
    (∀ᵐ ω ∂P, ∀ v w : ℝ, b ≤ v → v ≤ w → w ≤ a + p.T →
      let Vη0 := fp81s21_timeL2L1 (a + p.T) hQ (Uη0 ω)
      let VB0 := fp81s21_timeL2L1 (a + p.T) hQ (UB0 ω)
      let Vη := fp81s21_recentShift p a ha L hL
        (fp81s21_timeL2L1 H hH.le (Uη ω))
      let VB := fp81s21_recentShift p a ha L hL
        (fp81s21_timeL2L1 H hH.le (UB ω))
      O.drift v w VB = O.drift v w VB0 ∧
      O.drift v w VB0 = fp81s21_weightedDrift_windowInc ha le_rfl
        (r26t3_coeff R) (fun s f => B s ω f) v w ∧
      O.covariance v w Vη = O.covariance v w Vη0 ∧
      fp81s21_IsWindowJValue (r26t3_coeff R) (wholeSpaceIndex p.d) p.T a
        (fun s f => z s ω f) (Ioc v w)
        ((O.covariance v w Vη0 : projTensor (R2X p.d p.T) 2) :
          TensorDual (R2X p.d p.T) 2))

/-- Exact proposed two-law target, with no physical-identification premise.
The retained V2-N linear representative is `qN`; V2-G uses `canon.q`.
`S` retains the packet-31 quadratic selectors and their actual T/W payload.
`c,K` and the operator family precede `L,N,A,G,a`; the radius precedes the trajectory and both
window parameters. Only the field moment bound `M2` may depend on `L`.

The covariance is raw empirical/canonical linear, while the drift is exactly
centered quadratic. The Gaussian fields on weighted tests are canonical chart
actions, not the generally unavailable weighted extension of raw OscDual.eval.
This unit does not assert prediction, BV moments, or a joint W₂ profile. -/
def fp81s21_RecentIntervalPhysicalSpec (p : Parameters) : Prop :=
  ∃ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
  ∃ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
  ∃ ε εN εG εB : ℕ → ℝ,
    (∀ m, 0 ≤ ε m) ∧ Tendsto ε atTop (𝓝 0) ∧
    (∀ m, 0 ≤ εN m) ∧ Tendsto εN atTop (𝓝 0) ∧
    (∀ m, 0 ≤ εG m) ∧ Tendsto εG atTop (𝓝 0) ∧
    (∀ m, 0 ≤ εB m) ∧ Tendsto εB atTop (𝓝 0) ∧
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧
    ∃ O : (a : ℝ) → (ha : 0 ≤ a) →
      r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K,
    ∃ MUG : ℝ, 0 ≤ MUG ∧
    ∃ canon : fp81s21_gaussian_V2_G_canonicalFamily p Es E R MUG ε,
    ∃ S : fp81s21_Physical31 p R Es E εN εG εB,
    ∀ L : ℝ, (hL : 0 < L) → ∃ M2 : ℝ, 0 ≤ M2 ∧
    ∀ N : ℕ, (hN : 2 ≤ N) → ∀ A : Particle R N,
    ∃ qN : ℝ → A.Ω → r26t6_Coeff,
      fp81s21_MomentRep E A.P (fp81s21_particleEmpField R N A) qN M2 ∧
      ∀ G : GaussianRealization R, ∀ a : ℝ, (ha : 0 ≤ a) →
        fp81s21_RecentIntervalLaw p R A.P E qN
          (fun s ω => fp81s21_particle_embedField p Es E (S.qsBN N hN A s ω))
          (fp81s21_particleEmpField R N A) (fp81s21_particleQuadField R N A)
          (fp81s21_particleEmpField R N A) M2 S.MN a L c K ha hL (O a ha) ∧
        fp81s21_RecentIntervalLaw p R G.P E
          (fp81s21_gaussian_embedFamily p Es E (canon.q G))
          (S.gaussian.quadratic.qe G)
          (fun s ω f => fp81s21_chartAction E
            (fp81s21_gaussian_embedFamily p Es E (canon.q G) s ω) f)
          (fun s ω f => fp81s21_chartAction E (S.gaussian.quadratic.qe G s ω) f)
          (fun s ω f => OscDual.eval (G.Z s ω) f)
          MUG (S.gaussian.quadratic.Kstar ^ 4 * S.gaussian.quadratic.B / 2)
          a L c K ha hL (O a ha)

/-!
EXACT LEAN HEADER:
```lean
theorem fp81s21_recent_interval_physical (p : Parameters) :
    fp81s21_RecentIntervalPhysicalSpec p
```
Both specifications above are definitions. Expanding them gives the
full header; no unspecified predicate or physical-agreement assumption occurs.
The origin-zero horizon is `a+p.T`; the recent translated horizon is `L+p.T`.
Using origin-zero histories of length `L+p.T` without the shift would evaluate
`q s` instead of `q (b+s)` and is not the intended recent interval statement.
-/

/-- One probability-good set identifies every interval covariance of the
supplied origin-zero history with its canonical physical chart field. -/
theorem fp81s21_interval_history_covariance_chart
    {d r : ℕ} {Pw a T c K M : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (P : Measure Ω) (q : ℝ → Ω → r26t6_Coeff) (hH : 0 ≤ a + T)
    (O : r26t6_IntervalOperators E C T a c K)
    (U : Ω → fp81s21_L2History (a + T))
    (hU : fp81s21_TimeL2Rep P q M 0 (a + T) U) :
    ∀ᵐ ω ∂P, ∀ v w : ℝ, 0 ≤ v → v ≤ w → w ≤ a + T →
      fp81s21_IsWindowJValue C (wholeSpaceIndex d) T a
        (fun s f => fp81s21_chartAction E (q s ω) f) (Ioc v w)
        ((O.covariance v w (fp81s21_timeL2L1 (a + T) hH (U ω)) :
          projTensor (R2X d T) 2) : TensorDual (R2X d T) 2) := by
  filter_upwards [hU.2.2.2] with ω hω
  let V := fp81s21_timeL2L1 (a + T) hH (U ω)
  have hrep : V =ᵐ[volume.restrict (Icc (0 : ℝ) (a + T))]
      fun s => q s ω := by
    simpa only [zero_add] using
      (fp81s21_timeL2L1_ae (a + T) hH (U ω)).trans hω.2
  intro v w hv hvw hw
  have hvalue := fp81s21_interval_covariance_window_value O V hv hvw hw
  refine ⟨hvalue.1, ?_⟩
  intro ta tb φ ψ l₁ l₂ hφ hψ hta htb hl₁ hl₂
  rw [hvalue.2 ta tb φ ψ l₁ l₂ hφ hψ hta htb hl₁ hl₂]
  congr 1
  apply integral_congr_ae
  have hsub : Ioc v w ∩ Icc (0 : ℝ) (min (a + ta) (a + tb)) ⊆
      Icc (0 : ℝ) (a + T) := by
    intro s hs
    exact ⟨hv.trans hs.1.1.le, hs.1.2.trans hw⟩
  have hrep' := hrep.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  filter_upwards [hrep'] with s hs
  change inner ℝ (V s) (E.encode _) = inner ℝ (q s ω) (E.encode _)
  rw [hs]

/-- Two coefficient histories for the same field agree after recent translation
on the entire retained absolute-time interval, on one probability-good set. -/
theorem fp81s21_recent_history_agreement
    (p : Parameters) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (q : ℝ → Ω → r26t6_Coeff) (M a L : ℝ)
    (ha : 0 ≤ a) (hL : 0 < L)
    (U0 : Ω → fp81s21_L2History (a + p.T))
    (U : Ω → fp81s21_L2History (L + p.T))
    (hU0 : fp81s21_TimeL2Rep P q M 0 (a + p.T) U0)
    (hU : fp81s21_TimeL2Rep P q M (max (a - L) 0) (L + p.T) U) :
    ∀ᵐ ω ∂P,
      fp81s21_recentShift p a ha L hL
        (fp81s21_timeL2L1 (L + p.T) (add_pos hL p.hT).le (U ω))
        =ᵐ[volume.restrict (Icc (max (a - L) 0) (a + p.T))]
      fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (U0 ω) := by
  let b := max (a - L) 0
  have hb : 0 ≤ b := le_max_right _ _
  have hAH : a + p.T ≤ b + (L + p.T) := by
    have := le_max_left (a - L) 0
    dsimp [b]
    linarith
  have hsub : Icc b (a + p.T) ⊆ Icc (0 : ℝ) (a + p.T) :=
    Icc_subset_Icc_left hb
  filter_upwards [hU0.2.2.2, hU.2.2.2] with ω h0 h
  let V := fp81s21_timeL2L1 (L + p.T) (add_pos hL p.hT).le (U ω)
  let V0 := fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (U0 ω)
  have hv : V =ᵐ[volume.restrict (Icc (0 : ℝ) (L + p.T))]
      fun s => q (b + s) ω :=
    (fp81s21_timeL2L1_ae _ _ _).trans h.2
  have hv0 : V0 =ᵐ[volume.restrict (Icc (0 : ℝ) (a + p.T))]
      fun s => q s ω := by
    simpa only [zero_add] using (fp81s21_timeL2L1_ae _ _ _).trans h0.2
  have hvbase := (ae_restrict_iff' measurableSet_Icc).1 hv
  have mp : MeasurePreserving (fun t : ℝ => t - b) volume volume := by
    simpa [sub_eq_add_neg] using measurePreserving_add_right volume (-b)
  have htrans0 : ∀ᵐ t ∂volume, t - b ∈ Icc (0 : ℝ) (L + p.T) →
      V (t - b) = q (b + (t - b)) ω := mp.quasiMeasurePreserving.ae hvbase
  have htrans := htrans0.filter_mono (ae_mono (Measure.restrict_le_self (s := Icc b (a + p.T))))
  have hout := (fp81s21_recentShift_repr_Icc p a ha L hL V).filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hzero := hv0.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  filter_upwards [hout, hzero, htrans, ae_restrict_mem measurableSet_Icc]
    with t ho hz ht hm
  have hmem : t - b ∈ Icc (0 : ℝ) (L + p.T) := by
    constructor <;> linarith [hm.1, hm.2]
  have he := ht hmem
  have hab : b + (t - b) = t := by ring
  rw [hab] at he
  change _ = (Icc b (a + p.T)).indicator (fun t => V (t - b)) t at ho
  rw [Set.indicator_of_mem hm] at ho
  exact ho.trans (he.trans hz.symm)

/-- The norm estimates make both interval maps local in their coefficient
history; no zero-mass premise is needed for this locality statement. -/
theorem fp81s21_interval_operators_congr
    {d r : ℕ} {Pw a T c K v w : ℝ}
    {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    (O : r26t6_IntervalOperators E C T a c K)
    (q q' : r26t6_TimeCoeff (a + T))
    (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w ≤ a + T)
    (heq : q =ᵐ[volume.restrict (Ioc v w)] q') :
    O.drift v w q = O.drift v w q' ∧
    O.covariance v w q = O.covariance v w q' := by
  have hsub : Ioc v w ⊆ Icc (0 : ℝ) (a + T) := fun s hs =>
    ⟨hv.trans hs.1.le, hs.2.trans hw⟩
  have hcoe := (Lp.coeFn_sub q q').filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hz : (q - q' : r26t6_TimeCoeff (a + T)) =ᵐ[
      volume.restrict (Ioc v w)] (fun _ => 0) := by
    filter_upwards [hcoe, heq] with s hs he
    simpa only [Pi.sub_apply, he, sub_self] using hs
  constructor
  · apply sub_eq_zero.mp
    rw [← map_sub]
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have hn := O.drift_norm v w hv hvw hw (q - q')
    have hi : (∫ s in Ioc v w,
        HRS.MS.S111K2.s111k2_age c a s * ‖(q - q') s‖) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hz] with s hs
      rw [hs, norm_zero, mul_zero]
      rfl
    simpa only [hi, mul_zero] using hn
  · apply sub_eq_zero.mp
    rw [← map_sub]
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have hn := O.covariance_norm v w hv hvw hw (q - q')
    have hi : (∫ s in Ioc v w,
        HRS.MS.S111K2.s111k2_age c a s ^ 2 * ‖(q - q') s‖) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hz] with s hs
      rw [hs, norm_zero, mul_zero]
      rfl
    simpa only [hi, mul_zero] using hn

/-- Spatial cancellation passes to the origin-zero L¹ history of the SAME
selected quadratic family. -/
theorem fp81s21_recent_quadratic_history_zero_mass
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    {ε : ℕ → ℝ} (S : fp81s21_QuadraticPhysical31 p R Es E ε)
    (G : GaussianRealization R) (H : ℝ) (hH : 0 ≤ H)
    (U : G.Ω → fp81s21_L2History H)
    (hU : fp81s21_TimeL2Rep G.P (S.qe G) (S.Kstar ^ 4 * S.B / 2) 0 H U) :
    ∀ᵐ ω ∂G.P, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) H),
      inner ℝ (fp81s21_timeL2L1 H hH (U ω) s) (E.encode (fun _ => 1)) = 0 := by
  filter_upwards [hU.2.2.2,
    fp81s21_quadraticPhysical31_zero_mass p R Es E S G H hH] with ω hω hz
  have he := (fp81s21_timeL2L1_ae H hH (U ω)).trans hω.2
  filter_upwards [he, hz] with s hs hs0
  simpa only [hs, zero_add, fp81s21_chartAction] using hs0


private theorem fp81s21_recent_TimeRep_core
    {d r : ℕ} {Pw M a H : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {E : r26t6_WeightedChart d r Pw} {P : Measure Ω}
    {Q : ℝ → Ω → (Euc d → ℝ) → ℝ} {q : ℝ → Ω → r26t6_Coeff}
    {U : Ω → fp81s21_L2History H} (h : fp81s21_TimeRep E P Q q M a H U) :
    fp81s21_TimeL2Rep P q M a H U := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  filter_upwards [h.2.2.2] with ω hω
  exact ⟨hω.1, hω.2.mono (fun _ hs => hs.1)⟩

private theorem fp81s21_recent_TimeRep_chart
    {d r : ℕ} {Pw M a H : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart d r Pw) {P : Measure Ω}
    {q : ℝ → Ω → r26t6_Coeff} {U : Ω → fp81s21_L2History H}
    (h : fp81s21_TimeL2Rep P q M a H U) :
    fp81s21_TimeRep E P (fun s ω f => fp81s21_chartAction E (q s ω) f)
      q M a H U := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  filter_upwards [h.2.2.2] with ω hω
  refine ⟨hω.1, ?_⟩
  filter_upwards [hω.2] with s hs
  exact ⟨hs, fun f _ => congrArg (fun z => fp81s21_chartAction E z f) hs⟩

private theorem fp81s21_recent_combo_memCb
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {coef : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) coef hH)
    {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) H) (hs : s ∈ Icc (0 : ℝ) t)
    {φ : Euc p.d → ℝ} (hφ : IsR2DualCombo (wholeSpaceIndex p.d) φ) :
    MemCb (2 * p.d + 9) (propagatorW (r26t3_coeff R) s t φ) := by
  obtain ⟨S, coeff, rfl⟩ := hφ
  rw [s102_prop_sum (fp81s21_S102Lin p R H) hs.1 hs.2 ht.2 S coeff]
  have hb : ∀ α : MultiIndex p.d, MemCb (2 * p.d + 9)
      (propagatorW (r26t3_coeff R) s t (oscTestFun (wholeSpaceIndex p.d) α)) := by
    intro α
    have hsH : s ∈ Icc (0 : ℝ) H := ⟨hs.1, hs.2.trans ht.2⟩
    have hst : t ∈ Icc s H := ⟨hs.2, ht.2⟩
    refine ⟨?_, ?_⟩
    · have heq : 2 * p.d + 9 = (2 * p.d + 8) + 1 := by omega
      rw [heq]
      exact hstd.hD.smoothU α s hsH t hst
    · intro j hj
      refine ⟨coef α, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hstd.hD.bddU α s hsH t hst j (by omega) x
  induction S using Finset.induction_on with
  | empty =>
      change MemCb (2 * p.d + 9) (0 : Euc p.d → ℝ)
      simpa using HRS.MS.ProClosureS111.chart_memCb_smul (0 : ℝ) (hb 0)
  | @insert α S hα ih =>
      have hh := HRS.MS.ProClosureS111.chart_memCb_sub
        (HRS.MS.ProClosureS111.chart_memCb_smul (coeff α) (hb α))
        (HRS.MS.ProClosureS111.chart_memCb_smul (-1 : ℝ) ih)
      convert hh using 1
      funext x
      simp [Finset.sum_insert, hα, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]

private theorem fp81s21_recent_origin_physical
    (p : Parameters) {δ a c K Mη MB : ℝ} (R : Trajectory p δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (ha : 0 ≤ a)
    (O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K)
    {coef : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (a + p.T) (2 * p.d + 8) coef (add_pos_of_nonneg_of_pos ha p.hT))
    (qη qB : ℝ → Ω → r26t6_Coeff)
    (z B : ℝ → Ω → (Euc p.d → ℝ) → ℝ)
    (Uη UB : Ω → fp81s21_L2History (a + p.T))
    (hη : fp81s21_TimeRep E P z qη Mη 0 (a + p.T) Uη)
    (hB : fp81s21_TimeRep E P B qB MB 0 (a + p.T) UB)
    (Mb : Ω → ℝ → ℝ)
    (hDrift : ∀ᵐ ω ∂P, S102Drift (r26t3_coeff R) (wholeSpaceIndex p.d)
      (a + p.T) (2 * p.d + 8) ((p.d : ℝ) + 2) (fun s f => B s ω f) (Mb ω))
    (hzero : ∀ᵐ ω ∂P, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (a + p.T)),
      B s ω (fun _ => 1) = 0) :
    ∀ᵐ ω ∂P, ∀ v w : ℝ, 0 ≤ v → v ≤ w → w ≤ a + p.T →
      O.drift v w (fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (UB ω)) =
        fp81s21_weightedDrift_windowInc ha le_rfl (r26t3_coeff R)
          (fun s f => B s ω f) v w ∧
      fp81s21_IsWindowJValue (r26t3_coeff R) (wholeSpaceIndex p.d) p.T a
        (fun s f => z s ω f) (Ioc v w)
        ((O.covariance v w
          (fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (Uη ω)) :
            projTensor (R2X p.d p.T) 2) : TensorDual (R2X p.d p.T) 2) := by
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    linarith [Nat.cast_nonneg p.d (α := ℝ)]
  filter_upwards [hη.2.2.2, hB.2.2.2, hDrift, hzero] with ω hηω hBω hd hz
  let Vη := fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (Uη ω)
  let VB := fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (UB ω)
  have hb : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (a + p.T)),
      ∀ f, IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f →
        r26t6_coefficientField E VB s f = B s ω f := by
    filter_upwards [fp81s21_timeL2L1_ae _ _ (UB ω), hBω.2] with s he hs
    intro f hf
    change inner ℝ (VB s) (E.encode f) = B s ω f
    change VB s = (UB ω) s at he
    rw [he]
    simpa only [fp81s21_chartAction, zero_add] using hs.2 f hf
  have hη' : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (a + p.T)),
      ∀ f, IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f →
        r26t6_coefficientField E Vη s f = z s ω f := by
    filter_upwards [fp81s21_timeL2L1_ae _ _ (Uη ω), hηω.2] with s he hs
    intro f hf
    change inner ℝ (Vη s) (E.encode f) = z s ω f
    change Vη s = (Uη ω) s at he
    rw [he]
    simpa only [fp81s21_chartAction, zero_add] using hs.2 f hf
  have hq0 : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (a + p.T)),
      inner ℝ (VB s) (E.encode (fun _ => 1)) = 0 := by
    filter_upwards [hb, hz] with s hs hs0
    exact (hs _ (HRS.MS.ProClosureS111.constant_isWeightedTest hP 1)).trans hs0
  intro v w hv hvw hw
  constructor
  · apply fp81s21_interval_drift_eq_physical O VB ha p.hT.le hP hstd.hD
      (fp81s21_S102Lin p R (a + p.T)) hd hq0 hv hvw hw
    intro τ α
    have hsub : Ioc v (min w (a + ↑τ)) ⊆ Icc (0 : ℝ) (a + p.T) := by
      intro s hs
      exact ⟨hv.trans hs.1.le, (hs.2.trans (min_le_left _ _)).trans hw⟩
    filter_upwards [hb.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)),
      ae_restrict_mem measurableSet_Ioc] with s hs hm
    apply hs
    exact (s102_orbit_test hP hstd.hD (hsub hm)
      ⟨hm.2.trans (min_le_right _ _), by linarith [τ.property.2]⟩ α).1
  · have hvalue := fp81s21_interval_covariance_window_value O Vη hv hvw hw
    refine ⟨hvalue.1, ?_⟩
    intro ta tb φ ψ l₁ l₂ hφ hψ hta htb hl₁ hl₂
    rw [hvalue.2 ta tb φ ψ l₁ l₂ hφ hψ hta htb hl₁ hl₂]
    congr 1
    apply integral_congr_ae
    have hsub : Ioc v w ∩ Icc (0 : ℝ) (min (a + ta) (a + tb)) ⊆
        Icc (0 : ℝ) (a + p.T) := fun s hs => ⟨hv.trans hs.1.1.le, hs.1.2.trans hw⟩
    filter_upwards [hη'.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)),
      ae_restrict_mem (measurableSet_Ioc.inter measurableSet_Icc)] with s hs hm
    apply hs
    apply HRS.MS.ProClosureS111.chart_weighted_of_memCb hP
    apply HRS.MS.ProClosureS111.chart_memCb_gradient_inner
    · exact fp81s21_recent_combo_memCb p R (add_pos_of_nonneg_of_pos ha p.hT) hstd
        ⟨add_nonneg ha hta.1, by linarith [hta.2]⟩
        ⟨hm.2.1, hm.2.2.trans (min_le_left _ _)⟩ hφ
    · exact fp81s21_recent_combo_memCb p R (add_pos_of_nonneg_of_pos ha p.hT) hstd
        ⟨add_nonneg ha htb.1, by linarith [htb.2]⟩
        ⟨hm.2.1, hm.2.2.trans (min_le_right _ _)⟩ hψ

private theorem fp81s21_recent_chart_drift_data
    {d r : ℕ} {Pw H : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart d r Pw) (C : WholeCoeff d)
    (P : Measure Ω) (q : ℝ → Ω → r26t6_Coeff)
    {M : ℝ} (U : Ω → fp81s21_L2History H)
    (hU : fp81s21_TimeL2Rep P q M 0 H U)
    (hchart : r26t6_ChartedOrbits E C (wholeSpaceIndex d) H) :
    ∀ᵐ ω ∂P, S102Drift C (wholeSpaceIndex d) H r Pw
      (fun s f => fp81s21_chartAction E (q s ω) f) (fun s => ‖q s ω‖) := by
  filter_upwards [hU.2.2.2] with ω hω
  refine {
    hZ := fun u _ => fp81s21_chartAction_S102Z E (q u ω)
    hM := fun u _ f hf => fp81s21_chartAction_weighted_bound E (q u ω) f hf
    Mb_nonneg := fun _ => norm_nonneg _
    Mb_int := ?_
    meas := ?_ }
  · change Integrable (fun s => ‖q s ω‖) (volume.restrict (Icc (0 : ℝ) H))
    simpa only [zero_add] using (hω.1.integrable one_le_two).norm
  · intro t ht α
    have hsm : AEStronglyMeasurable (fun s => q s ω)
        (volume.restrict (Icc (0 : ℝ) H)) := by
      simpa only [zero_add] using hω.1.aestronglyMeasurable
    have hsm' := hsm.mono_ac (Measure.absolutelyContinuous_of_le
      (Measure.restrict_mono (Icc_subset_Icc_right ht.2) le_rfl))
    exact hsm'.inner (hchart.2 t ht _ (s102_isDualCombo α))

private theorem fp81s21_recent_law_assemble
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (qη qB : ℝ → Ω → r26t6_Coeff)
    (z B zTest : ℝ → Ω → (Euc p.d → ℝ) → ℝ)
    (Mη MB a L c K : ℝ) (ha : 0 ≤ a) (hL : 0 < L)
    (O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K)
    (Uη0 UB0 : Ω → fp81s21_L2History (a + p.T))
    (Uη UB : Ω → fp81s21_L2History (L + p.T))
    (X : Ω → fp81s21_SmoothCH (L + p.T))
    (hη0 : fp81s21_TimeL2Rep P qη Mη 0 (a + p.T) Uη0)
    (hB0 : fp81s21_TimeL2Rep P qB MB 0 (a + p.T) UB0)
    (hη : fp81s21_TimeL2Rep P qη Mη (max (a - L) 0) (L + p.T) Uη)
    (hB : fp81s21_TimeL2Rep P qB MB (max (a - L) 0) (L + p.T) UB)
    (hXm : Measurable X) (hX : MemLp X 2 P)
    (heq : Uη =ᵐ[P] fun ω => fp81s21_smoothPathToL2 (L + p.T) (add_pos hL p.hT) (X ω))
    (hTest : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (L + p.T), ∀ f : Euc p.d → ℝ,
      IsR2Test f → fp81s21_chartAction E (X ω t) f = zTest (max (a - L) 0 + t) ω f)
    (hphys : ∀ᵐ ω ∂P, ∀ v w : ℝ, 0 ≤ v → v ≤ w → w ≤ a + p.T →
      O.drift v w (fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (UB0 ω)) =
        fp81s21_weightedDrift_windowInc ha le_rfl (r26t3_coeff R) (fun s f => B s ω f) v w ∧
      fp81s21_IsWindowJValue (r26t3_coeff R) (wholeSpaceIndex p.d) p.T a
        (fun s f => z s ω f) (Ioc v w)
        ((O.covariance v w (fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (Uη0 ω)) :
          projTensor (R2X p.d p.T) 2) : TensorDual (R2X p.d p.T) 2)) :
    fp81s21_RecentIntervalLaw p R P E qη qB z B zTest Mη MB a L c K ha hL O := by
  refine ⟨Uη0, UB0, Uη, UB, X, hη0, hB0, hη, hB, hXm, hX, heq, hTest, ?_⟩
  filter_upwards [hphys, fp81s21_recent_history_agreement p P qη Mη a L ha hL Uη0 Uη hη0 hη,
    fp81s21_recent_history_agreement p P qB MB a L ha hL UB0 UB hB0 hB] with ω hp hηω hBω
  intro v w hv hvw hw
  have hv0 : 0 ≤ v := (le_max_right _ _).trans hv
  have hsub : Ioc v w ⊆ Icc (max (a - L) 0) (a + p.T) :=
    fun s hs => ⟨hv.trans hs.1.le, hs.2.trans hw⟩
  have heη := fp81s21_interval_operators_congr O _ _ hv0 hvw hw
    (hηω.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
  have heB := fp81s21_interval_operators_congr O _ _ hv0 hvw hw
    (hBω.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
  exact ⟨heB.1, (hp v w hv0 hvw hw).1, heη.2, (hp v w hv0 hvw hw).2⟩

/-- Both retained laws have the physical packet-14/16 interval corrections,
with their radius and interval-operator constants chosen before the window. -/
theorem fp81s21_recent_interval_physical (p : Parameters) :
    fp81s21_RecentIntervalPhysicalSpec p := by
  obtain ⟨Es, E, ε, hε, hεlim, δA, hδA, hδAh, hAvg⟩ :=
    fp81s21_physical_avgPackage_retained p
  obtain ⟨εN, εG, εB, hεN, hεNlim, hεG, hεGlim, hεB, hεBlim,
    δS, hδS, hδSh, hSel⟩ := fp81s21_physical31_exists p Es E
  obtain ⟨δO, hδO, hδOh, hOps⟩ := fp81s21_moving_interval_operators p
  obtain ⟨δI, hδI, hδIh, hInputs⟩ := fp81s21_moving_inputs_all p
  refine ⟨Es, E, ε, εN, εG, εB, hε, hεlim, hεN, hεNlim,
    hεG, hεGlim, hεB, hεBlim, min δA (min δS (min δO δI)),
    lt_min hδA (lt_min hδS (lt_min hδO hδI)),
    (min_le_left _ _).trans hδAh, ?_⟩
  intro δ hδ hδle R
  have hA := hδle.trans (min_le_left δA _)
  have hS := hδle.trans ((min_le_right δA _).trans (min_le_left δS _))
  have hOI := hδle.trans ((min_le_right δA _).trans (min_le_right δS _))
  obtain ⟨c, K, hc, hK, hO⟩ := hOps δ hδ (hOI.trans (min_le_left _ _)) R E
  let O := fun a ha => Classical.choice (hO a ha)
  obtain ⟨MUG, hMUG, canon, hForH⟩ := hAvg δ hδ hA R
  obtain ⟨S⟩ := hSel δ hδ hS R
  refine ⟨c, K, hc, hK, O, MUG, hMUG, canon, S, ?_⟩
  intro L hL
  have hH : 0 < L + p.T := add_pos hL p.hT
  obtain ⟨M2, hM2, Savg, err, herr, herrlim, hSavg, hForN⟩ := hForH (L + p.T) hH
  refine ⟨M2, hM2, ?_⟩
  intro N hN A
  obtain ⟨qN, hqN, hForG⟩ := hForN N hN A
  refine ⟨qN, hqN, ?_⟩
  intro G a ha
  let b := max (a - L) 0
  have hb : 0 ≤ b := le_max_right _ _
  have hQ : 0 < a + p.T := add_pos_of_nonneg_of_pos ha p.hT
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    linarith [Nat.cast_nonneg p.d (α := ℝ)]
  obtain ⟨coef, hstd, hphys⟩ :=
    hInputs δ hδ (hOI.trans (min_le_right _ _)) R a ha
  obtain ⟨XN, UN, XG, UG, hXN, hXNmem, hUNm, hUN, hUNeq, hNTest,
    hXG, hXGmem, hUGm, hUG, hUGeq, hGTest, hApprox⟩ := hForG G b hb
  obtain ⟨UN0, hUN0⟩ := fp81s21_MomentRep_time_section E A.P
    (fp81s21_particleEmpField R N A) qN M2 0 (a + p.T) hqN le_rfl hQ.le
  obtain ⟨VN0, BN0, hVN0, hBN0, hNtail0⟩ :=
    (S.particle N hN A).2.2.2.2.2.2 0 le_rfl (a + p.T) hQ
  obtain ⟨VN, BN, hVN, hBN, hNtail⟩ :=
    (S.particle N hN A).2.2.2.2.2.2 b hb (L + p.T) hH
  have hrepN := (S.particle N hN A).2.2.2.2.1
  have heN := fp81s21_MomentRep_TimeL2Rep_eq_ae hP E A.P
    (fp81s21_particleEmpField R N A) qN _ M2 S.MN 0 (a + p.T) UN0 VN0
    hqN.1 hrepN.1 le_rfl hqN hrepN hUN0 (fp81s21_recent_TimeRep_core hVN0)
  have hUNweighted : fp81s21_TimeRep E A.P (fp81s21_particleEmpField R N A)
      qN M2 0 (a + p.T) UN0 := by
    refine ⟨hUN0.1, hUN0.2.1, hUN0.2.2.1, ?_⟩
    filter_upwards [hUN0.2.2.2, hVN0.2.2.2, heN] with ω hω hVω he
    refine ⟨hω.1, ?_⟩
    filter_upwards [hω.2, hVω.2] with s hs ht
    refine ⟨hs, ?_⟩
    intro f hf
    rw [he]
    exact ht.2 f hf
  obtain ⟨Mb, hMb, hMbint⟩ := fp81s21_moving_M1 p R hQ hN A hstd
    (by push_cast; linarith [Nat.cast_nonneg p.d (α := ℝ)]) (hphys N hN A)
  have hNzero : ∀ᵐ ω ∂A.P, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (a + p.T)),
      fp81s21_particleQuadField R N A s ω (fun _ => 1) = 0 := by
    filter_upwards with ω
    filter_upwards with s
    simp [fp81s21_particleQuadField, r2QuadField, gradient, commutatorKernel, pairEnergy]
  have hNP := fp81s21_recent_origin_physical p R A.P E ha (O a ha) hstd
    qN _ (fp81s21_particleEmpField R N A) (fp81s21_particleQuadField R N A)
    UN0 BN0 hUNweighted hBN0 Mb hMb hNzero
  have hGNrep := (canon.payload G).coefficients.weak_momentRep
  obtain ⟨UG0, hUG0⟩ := fp81s21_MomentRep_time_section E G.P
    (fun s ω f => OscDual.eval (G.Z s ω) f)
    (fp81s21_gaussian_embedFamily p Es E (canon.q G)) MUG 0 (a + p.T)
    hGNrep le_rfl hQ.le
  obtain ⟨BG0, hBG0, hBGweighted0, hBGtail0⟩ :=
    (S.gaussian.quadratic.payload G).2.2.2.2.2.2.2 0 le_rfl (a + p.T) hQ
  obtain ⟨BG, hBG, hBGweighted, hBGtail⟩ :=
    (S.gaussian.quadratic.payload G).2.2.2.2.2.2.2 b hb (L + p.T) hH
  have hchart := fp81s21_moving_charted_orbits p R hQ hstd hP E
  have hGdrift := fp81s21_recent_chart_drift_data E (r26t3_coeff R) G.P
    (S.gaussian.quadratic.qe G) BG0 hBG0 hchart
  have hGzero := fp81s21_quadraticPhysical31_zero_mass p R Es E
    S.gaussian.quadratic G (a + p.T) hQ.le
  have hGP := fp81s21_recent_origin_physical p R G.P E ha (O a ha) hstd
    _ _ _ _ UG0 BG0 (fp81s21_recent_TimeRep_chart E hUG0)
    hBGweighted0 _ hGdrift hGzero
  constructor
  · exact fp81s21_recent_law_assemble p R A.P E qN _ _ _ _
      M2 S.MN a L c K ha hL (O a ha) UN0 BN0 UN BN XN
      hUN0 (fp81s21_recent_TimeRep_core hBN0) hUN
      (fp81s21_recent_TimeRep_core hBN) hXN hXNmem hUNeq hNTest hNP
  · exact fp81s21_recent_law_assemble p R G.P E _ _ _ _ _
      MUG (S.gaussian.quadratic.Kstar ^ 4 * S.gaussian.quadratic.B / 2)
      a L c K ha hL (O a ha) UG0 BG0 UG BG XG hUG0 hBG0 hUG hBG
      hXG hXGmem hUGeq hGTest hGP

end HRS.Fp81.S21
end

#print axioms HRS.Fp81.S21.fp81s21_interval_history_covariance_chart
#print axioms HRS.Fp81.S21.fp81s21_physical_avgPackage_retained
#print axioms HRS.Fp81.S21.fp81s21_moving_interval_operators

#print axioms HRS.Fp81.S21.fp81s21_RecentIntervalLaw
#print axioms HRS.Fp81.S21.fp81s21_RecentIntervalPhysicalSpec

#print axioms HRS.Fp81.S21.fp81s21_recent_history_agreement
#print axioms HRS.Fp81.S21.fp81s21_interval_operators_congr
#print axioms HRS.Fp81.S21.fp81s21_recent_quadratic_history_zero_mass

#print axioms HRS.Fp81.S21.fp81s21_recent_interval_physical
