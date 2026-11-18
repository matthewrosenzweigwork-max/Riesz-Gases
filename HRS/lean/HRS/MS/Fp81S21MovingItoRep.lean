import HRS.MS.Fp81S21MovingM1
import HRS.MS.Fp81S21MovingDuality2

/-!
# HRS S2.1(iii), packet 8.5: moving-coordinate Itô representation

The stationary statements being generalized are these (all names are in
`HRS.MS.R2Interp`; the full hypotheses and definitions are recorded at the
indicated source declarations):

* Aux94: `s102_PhicE` and `s102_PhicE_form` (`R2InterpAux94:19,47`):
  coordinate `i` of the Euclidean noise coefficient is
  `(√N * (√(2ν)/N)) * s102_Ig (s102_orb C m hT L i)
    (s102_tk hT L i) X u ζ k`, and on `u ≥ 0` it equals `s102_Phic`.
* Aux95: `s102_PhicE_locL2` (`R2InterpAux95:22`): from `S102Std` and
  progressivity of `ofNNRealTime X`, this `s102_PhicE` is
  `IsProgressiveLocL2E P ℱ`.
* Aux96: `s102_bdc` and `s102_bdc_prog_int`
  (`R2InterpAux96:36,42`): with the fixed reference `μ`,
  `bdc_i u ζ = if 0 ≤ u then - (√N)⁻¹ * s102_hh C m τ α
    (fun v => r2QuadField sQ μ P X v ζ) i u else 0`; under the stationary
  `IsRound2Density` and fixed-reference time-marginal `HasR2ActualDensity`
  hypotheses, it is progressive and a.e. locally integrable.
* Aux97: `s102_obs_y0` (`R2InterpAux97:18`): the initial predicted-path
  observation equals `s102_zf P X ζ 0 (s102_orb ... 0)` coordinatewise.
* Aux98: `s102_bdE` and `s102_bdE_locL1` (`R2InterpAux98:39,47`): Euclidean
  assembly of `bdc`, progressive and locally L¹ under those same fixed-density
  hypotheses.
* Aux99: `s102_bd_integral_coord` and `s102_bdc_integral`
  (`R2InterpAux99:18,27`): projection commutes with the drift integral, and
  the coordinate integral through time `u ≥ 0` truncates at `min u τᵢ`.
* Aux100: `s102_loc_coord` (`R2InterpAux100:20`): for a.e. `ζ`, simultaneously
  for every real `u`, the coordinate of `localItoIntegralE Φc` is the scalar
  Itô integral with the factor `√N * (√(2ν)/N)`, and that scalar integral
  stopped at `τᵢ` equals its value at `min u τᵢ`.
* Aux101: `s102_itoRep` (`R2InterpAux101:20`) produces the `S102ItoRep`
  contract from a stationary thermal density, `S102Std`, fixed-reference
  actual-density bounds, and particle moments on `[0,T]`.
* Aux61 defines that contract (`R2InterpAux61:22`): locally integrable
  progressive `bd`, locally square-integrable progressive `Φc`, initial
  observation measurability, pointwise formulas for `bd` and `Φc`, and a
  simultaneous a.e.-in-`ζ`, all-`u ∈ [0,T]` observation identity with
  `itoProcess`.

The moving statements in this packet use `C = r26t3_coeff R`,
`m = wholeSpaceIndex p.d`, `H` as the observation horizon, and replace every
drift reference at time `v` by `r26t3_mu R v`. The moving drift coordinate and
its Euclidean assembly below have the exact integral identities; subsequent
files prove local L¹, retain the existing `s102_PhicE` noise coefficient and
its local L² estimate, prove the stopped coordinate result and initial
measurability, then construct the moving Itô representation. In that final
contract `F : FilteredParticle A` supplies `F.ℱ`, `F.Wc`, and `F.X` for all
stochastic integration and adapted initial data. `A.X` remains the observed
path; P00's single event `∀ᵐ ω, ∀ t : ℝ≥0, F.X t ω = A.X t ω` transports the
observation identity and the moving M1 drift bound. No stationary density is
assumed: the fixed-density local-L¹ argument of Aux96/Aux98 is replaced by
moving M1 and this P00 transport.

The scope adjustment is that local integrability is needed only for the
stopped drift on `[0,H]`; the new coordinate is set to zero outside that
interval. This preserves all nonnegative-time `s102_hh` coordinate formulas,
since each observation time lies in `[0,H]`, and makes the process locally L¹
on every real compact interval without requiring physical inputs beyond `H`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- The stopped drift coordinate with the reference law evaluated at the
integration time. It is supported on the physical observation horizon. -/
def fp81s21_moving_bdc
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    (L : ℕ) (sQ : ℝ) {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig p.d N)
    (i : Fin (s102_q p.d L)) (u : ℝ) (ζ : Ω) : ℝ :=
  if u ∈ Icc (0 : ℝ) H then
    -(Real.sqrt N)⁻¹ * s102_hh (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (s102_tauk hH L) (s102_alk L)
      (fun v => r2QuadField sQ (r26t3_mu R v) P X v ζ) i u
  else 0

/-- Euclidean assembly of the moving drift coordinates. -/
def fp81s21_moving_bdE
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    (L : ℕ) (sQ : ℝ) {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig p.d N) :
    ℝ → Ω → EuclideanSpace ℝ (Fin (s102_q p.d L)) :=
  fun u ζ => (EuclideanSpace.equiv (Fin (s102_q p.d L)) ℝ).symm
    (fun i => fp81s21_moving_bdc p R hH L sQ P X i u ζ)

theorem fp81s21_moving_bdc_form
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    (L : ℕ) (sQ : ℝ) {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig p.d N)
    (i : Fin (s102_q p.d L)) (u : ℝ) (ζ : Ω) (hu : 0 ≤ u) :
    fp81s21_moving_bdc p R hH L sQ P X i u ζ =
      -(Real.sqrt N)⁻¹ * s102_hh (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
        (s102_tauk hH L) (s102_alk L)
        (fun v => r2QuadField sQ (r26t3_mu R v) P X v ζ) i u := by
  classical
  by_cases huH : u ∈ Icc (0 : ℝ) H
  · simp [fp81s21_moving_bdc, huH]
  · have hnot : ¬ u ≤ H := by
      intro hu'
      exact huH ⟨hu, hu'⟩
    have hstop : ¬ u ∈ Iic (s102_tauk hH L i : ℝ) := by
      intro hui
      apply hnot
      exact hui.trans (s102_tauk hH L i).2.2
    unfold fp81s21_moving_bdc
    rw [if_neg huH]
    unfold s102_hh
    rw [Set.indicator_of_notMem hstop]
    simp

theorem fp81s21_moving_bd_integral_coord
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    (L : ℕ) (sQ : ℝ) {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig p.d N)
    (ζ : Ω) (u : ℝ)
    (hint : ∀ i, IntegrableOn
      (fun s => fp81s21_moving_bdc p R hH L sQ P X i s ζ) (Icc 0 u))
    (i : Fin (s102_q p.d L)) :
    (∫ s in Icc 0 u, fp81s21_moving_bdE p R hH L sQ P X s ζ) i =
      ∫ s in Icc 0 u, fp81s21_moving_bdc p R hH L sQ P X i s ζ := by
  have hI : IntegrableOn
      (fun s => fp81s21_moving_bdE p R hH L sQ P X s ζ) (Icc 0 u) :=
    s102_integrableOn_E _ hint
  have hproj := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hI
  exact hproj.symm

theorem fp81s21_moving_bdc_integral
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    (L : ℕ) (sQ : ℝ) {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig p.d N)
    (ζ : Ω) {u : ℝ} (hu : 0 ≤ u) (i : Fin (s102_q p.d L)) :
    ∫ s in Icc 0 u, fp81s21_moving_bdc p R hH L sQ P X i s ζ =
      ∫ s in Icc 0 (min u (s102_tk hH L i)),
        (-(Real.sqrt N)⁻¹ * r2QuadField sQ (r26t3_mu R s) P X s ζ
          (s102_orb (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) hH L i s)) := by
  have h1 : ∀ s ∈ Icc (0 : ℝ) u,
      fp81s21_moving_bdc p R hH L sQ P X i s ζ =
        (Iic (s102_tk hH L i)).indicator
          (fun s => -(Real.sqrt N)⁻¹ * r2QuadField sQ (r26t3_mu R s)
            P X s ζ (s102_orb (r26t3_coeff R)
              (wholeSpaceIndex p.d : ℝ) hH L i s)) s := by
    intro s hs
    by_cases hst : s ≤ s102_tk hH L i
    · have hsH : s ∈ Icc (0 : ℝ) H :=
        ⟨hs.1, hst.trans (s102_tauk hH L i).2.2⟩
      have hsTau : s ∈ Iic (s102_tauk hH L i : ℝ) := by
        simpa [s102_tk] using hst
      unfold fp81s21_moving_bdc
      rw [if_pos hsH]
      unfold s102_hh
      rw [Set.indicator_of_mem hsTau]
      rw [Set.indicator_of_mem (show s ∈ Iic (s102_tk hH L i) from hst)]
      simp [s102_orb, s102_tk]
    · have hsTau : s ∉ Iic (s102_tauk hH L i : ℝ) := by
        intro hsTau
        exact hst (by simpa [s102_tk] using hsTau)
      have hsTk : s ∉ Iic (s102_tk hH L i) := fun hsTk => hst hsTk
      unfold fp81s21_moving_bdc
      by_cases hsH : s ∈ Icc (0 : ℝ) H
      · rw [if_pos hsH]
        unfold s102_hh
        rw [Set.indicator_of_notMem hsTau]
        rw [Set.indicator_of_notMem hsTk]
        simp
      · rw [if_neg hsH]
        rw [Set.indicator_of_notMem hsTk]
  have hset : Icc (0 : ℝ) u ∩ Iic (s102_tk hH L i) =
      Icc 0 (min u (s102_tk hH L i)) := by
    ext s
    simp only [mem_inter_iff, mem_Icc, mem_Iic, le_min_iff]
    tauto
  rw [setIntegral_congr_fun measurableSet_Icc h1,
    setIntegral_indicator measurableSet_Iic, hset]

#print axioms HRS.Fp81.S21.fp81s21_moving_bdc_form
#print axioms HRS.Fp81.S21.fp81s21_moving_bd_integral_coord
#print axioms HRS.Fp81.S21.fp81s21_moving_bdc_integral

end HRS.Fp81.S21

end
