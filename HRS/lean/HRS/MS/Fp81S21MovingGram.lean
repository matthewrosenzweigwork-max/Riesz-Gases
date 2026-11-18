import HRS.MS.Fp81S21MovingInputs
import HRS.MS.R2InterpAux56

/-!
# HRS S2.1(iii): moving Gram integrability, PSD rates, and the heat wrapper

The generic covariance and heat arguments only require integrability of the cut-off Gram
entries, continuity and positive semidefiniteness of the rate on an observation-free piece,
and the covariance increment identity.  This file supplies those inputs from `Fp81MovingStd`,
whose density and Gram hypotheses are timewise and moving.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.CovMeas HRS.MS.R2Interp
open HRS.MC.Sec7.PI

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ}
  {c : MultiIndex d → ℝ} {hT : 0 < T}

/-- The moving Gram entries give the exact cut-off integrability interface
`S102GramInt` used by the generic covariance increment theorem. -/
theorem fp81s21_moving_gramInt
    (hs : Fp81MovingStd C m T r c hT) (L : ℕ) :
    S102GramInt C m hT L := by
  intro i j
  have hμT : min (s102_tk hT L i) (s102_tk hT L j) ≤ T :=
    (min_le_left _ _).trans (s102_tauk hT L i).2.2
  have hcont := hs.hGram L i j
  have hI : IntegrableOn
      (fun u => s102_gram C m hT L u i j)
      (Icc 0 (min (s102_tk hT L i) (s102_tk hT L j))) :=
    hcont.integrableOn_Icc
  have hfun : (fun u => if u ≤ min (s102_tk hT L i) (s102_tk hT L j) then
      s102_gram C m hT L u i j else 0) =
      (Iic (min (s102_tk hT L i) (s102_tk hT L j))).indicator
        (fun u => s102_gram C m hT L u i j) := by
    funext u
    simp [indicator]
  rw [hfun, IntegrableOn, integrable_indicator_iff measurableSet_Iic,
    IntegrableOn, Measure.restrict_restrict measurableSet_Iic]
  refine hI.mono_set ?_
  intro u hu
  exact ⟨hu.2.1, hu.1⟩

/-- Moving Gram integrability implies the rate-entry integrability consumed by
`s102_obsCov_cont` and the generic covariance increment argument. -/
theorem fp81s21_moving_rateM_integrableOn
    (hs : Fp81MovingStd C m T r c hT) (L : ℕ)
    (i j : Fin (s102_q d L)) :
    IntegrableOn (fun u => s102_rateM C m hT L u i j) (Icc 0 T) := by
  exact s102_rateM_integrableOn hT L (fp81s21_moving_gramInt hs L) i j

/-- At each time, the moving covariance rate is positive semidefinite. -/
theorem fp81s21_moving_rateM_psd
    (hs : Fp81MovingStd C m T r c hT) (L : ℕ) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) T) :
    (s102_rateM C m hT L u).PosSemidef := by
  exact s102_rateM_psd hs.hD hT L hu (hs.hint u hu) (hs.hnn u hu) hs.hν

/-- The frozen rate on an observation-free time piece is positive semidefinite,
using the moving timewise density hypotheses. -/
theorem fp81s21_moving_Ar_psd
    (hs : Fp81MovingStd C m T r c hT) (L : ℕ)
    {a b v : ℝ} (hv : v ∈ Icc a b) (ha : 0 ≤ a) (hb : b ≤ T) :
    (s102_Ar C m hT L b v).PosSemidef := by
  have hvT : v ∈ Icc (0 : ℝ) T := ⟨ha.trans hv.1, hv.2.trans hb⟩
  have hR := fp81s21_moving_rateM_psd hs L hvT
  set D : Matrix (Fin (s102_q d L)) (Fin (s102_q d L)) ℝ :=
    Matrix.diagonal fun i => if b ≤ s102_tk hT L i then (1 : ℝ) else 0 with hD
  have hDH : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    ext i j
    simp [Matrix.diagonal]
  have hcong := hR.conjTranspose_mul_mul_same D
  rw [hDH] at hcong
  convert hcong using 1
  ext i j
  simp only [s102_Ar, s102_rateM, hD, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.of_apply]
  by_cases hi : b ≤ s102_tk hT L i <;>
    by_cases hj : b ≤ s102_tk hT L j
  · have hm : b ≤ min (s102_tk hT L i) (s102_tk hT L j) := le_min hi hj
    rw [if_pos hm, if_pos (hv.2.trans hm)]
    simp [hi, hj]
  · have hm : ¬ b ≤ min (s102_tk hT L i) (s102_tk hT L j) :=
      fun h => hj (h.trans (min_le_right _ _))
    simp [hi, hj, hm]
  · have hm : ¬ b ≤ min (s102_tk hT L i) (s102_tk hT L j) :=
      fun h => hi (h.trans (min_le_left _ _))
    simp [hi, hj, hm]
  · have hm : ¬ b ≤ min (s102_tk hT L i) (s102_tk hT L j) :=
      fun h => hi (h.trans (min_le_left _ _))
    simp [hi, hj, hm]

/-- Moving-density version of the `c12` heat wrapper.  Its proof supplies the
continuous PSD piece rate, the terminal covariance positivity, and the covariance
increment identity required by the generic `s7_PIH_heat_c12_proof'` theorem. -/
theorem fp81s21_moving_c12
    {p : HRS.MS.R26T3.Parameters} {δ : ℝ}
    (R : HRS.MS.R26T3.Trajectory p δ)
    {m T : ℝ} {r : ℕ} {c : MultiIndex p.d → ℝ} {hT : 0 < T}
    (hs : Fp81MovingStd (r26t3_coeff R) m T r c hT) (L : ℕ)
    (γ : ℝ → Measure (OscPath p.d m T))
    (hγ : ∀ u ∈ Icc (0 : ℝ) T,
      IsR2FutureGaussian (r26t3_coeff R) m T u (γ u))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hno : ∀ i : Fin (s102_q p.d L),
      ¬ (a < s102_tk hT L i ∧ s102_tk hT L i < b))
    {G : EuclideanSpace ℝ (Fin (s102_q p.d L)) → ℝ} (hG4 : MemCb 4 G) :
    ∃ f : ℝ → EuclideanSpace ℝ (Fin (s102_q p.d L)) → ℝ,
      HRS.IsC12On T Set.univ f ∧
      (∀ z ∈ Icc a b,
        f z = gaussHeat
          (s102_obsCov (r26t3_coeff R) m (s102_tauk hT L) (s102_alk L)) G z) ∧
      ∀ z ∈ Ioc a b, ∀ x,
        derivWithin (fun s => f s x) (Icc 0 T) z =
          -(1 / 2) * ∑ i, ∑ j,
            s102_rateM (r26t3_coeff R) m hT L z i j *
              iteratedFDeriv ℝ 2
                (gaussHeat
                  (s102_obsCov (r26t3_coeff R) m (s102_tauk hT L)
                    (s102_alk L)) G z) x
                ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] := by
  have hGi := fp81s21_moving_gramInt hs L
  have hbT : b ∈ Icc (0 : ℝ) T := ⟨ha.trans hab, hb⟩
  obtain ⟨f, hf, hfeq, hfd⟩ :=
    HRS.MC.Sec7.S7PIH.s7_PIH_heat_c12_proof'
      (q := s102_q p.d L) a b T ha hab hb hT
      (s102_Ar (r26t3_coeff R) m hT L b)
      (s102_obsCov (r26t3_coeff R) m (s102_tauk hT L) (s102_alk L))
      (fun i j => by
        by_cases h : b ≤ min (s102_tk hT L i) (s102_tk hT L j)
        · have hsub : Icc a b ⊆
              Icc 0 (min (s102_tk hT L i) (s102_tk hT L j)) :=
            Icc_subset_Icc ha h
          have hcont := (hs.hGram L i j).mono hsub
          refine (hcont.const_mul (2 * (r26t3_coeff R).ν)).congr
            (fun z _ => ?_)
          simp only [s102_Ar, Matrix.of_apply, if_pos h]
        · simp only [s102_Ar, Matrix.of_apply, if_neg h, mul_zero]
          exact continuousOn_const)
      (fun z hz => fp81s21_moving_Ar_psd hs L hz ha hb)
      (s102_obs_law (r26t3_coeff R) (hγ b hbT)
        (s102_tauk hT L) (s102_alk L)).1
      (fun u hu i j => by
        have hcov := s102_obsCov_eq_rate hT L hGi
          (ha.trans hu.1) hu.2 hb i j
        rw [hcov]
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioc fun z hz => ?_
        have har := s102_Ar_eq_rate (C := r26t3_coeff R) (m := m)
          hT L (a := a) (b := b) (v := z)
          ⟨hu.1.trans_lt hz.1, hz.2⟩ hno
        rw [har])
      G hG4
  refine ⟨f, hf, hfeq, fun z hz x => ?_⟩
  rw [hfd z ⟨hz.1.le, hz.2⟩ x]
  have har := s102_Ar_eq_rate (C := r26t3_coeff R) (m := m)
    hT L (a := a) (b := b) (v := z) hz hno
  rw [har]

#print axioms HRS.Fp81.S21.fp81s21_moving_gramInt
#print axioms HRS.Fp81.S21.fp81s21_moving_rateM_integrableOn
#print axioms HRS.Fp81.S21.fp81s21_moving_rateM_psd
#print axioms HRS.Fp81.S21.fp81s21_moving_Ar_psd
#print axioms HRS.Fp81.S21.fp81s21_moving_c12

end HRS.Fp81.S21

end
