import HRS.MS.Fp81S21ResponseWindow
import HRS.MS.Fp81S21Uniform2
import HRS.MS.R2ObsAux4
import HRS.MS.R2ObsAux7
import HRS.MS.S104bOrb1
import HRS.MS.R2WinOrbAux13

/-!
# S2.1(iii): high order response-window coordinate bounds

This file extracts the high order orbit bound before applying the response
estimate.  The first result is a uniform square-summable envelope for the
response coordinates, for every configuration point and every physical time.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.CovMeas
open HRS.MS.R2WinOrb HRS.MS.R2WinOrbNL HRS.MS.R2WinErr

variable {p : Parameters} {δ : ℝ}

theorem fp81s21_response_mode_bound_of_orbits
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) {Co co : ℝ}
    (hclaims : S103nOrbitClaims p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), 0 ≤ t → ∀ α : MultiIndex p.d, ∀ x : Euc p.d,
      |r26t3_a R (propagatorW (r26t3_coeff R) 0 t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x| ≤
      C * (|Co| * s103_b p.d α) := by
  obtain ⟨C, hC0, hresp⟩ := fp81s21_response_smooth hδ hδh R hγ
  refine ⟨C, hC0, fun t ht α x => ?_⟩
  let Cf : WholeCoeff p.d := r26t3_coeff R
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let A : ℝ := |Co| * s103_b p.d α
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (abs_nonneg Co) (s103_b_nonneg α)
  have hmono : Co * s103_b p.d α ≤ A := by
    dsimp [A]
    exact mul_le_mul_of_nonneg_right (le_abs_self Co) (s103_b_nonneg α)
  have htIcc : t ∈ Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have horb : S104nOrbit Cf φ t :=
    s104b_orbit_of_termRegGen hterm R.admissible R.resulting α t ht
  obtain ⟨f, hf⟩ := horb.ex0 t htIcc
  have hcanonical := HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩
  have hraw := hclaims R.ε R.ψ R.ρ R.admissible R.resulting α t ht
  have hsup := HRS.MS.R2WinOrb.s103_orbitSup_mono hraw.1 hmono
  have hU := hsup (fun z => propagatorW Cf z t φ) hcanonical 0 ⟨le_rfl, ht⟩
  have hderiv := HRS.MS.R2WinOrb.s103_cb_of_E hA0 hU.2
  have hmemK : MemCb (4 * p.d + 42) (propagatorW Cf 0 t φ) := by
    refine ⟨hU.1, ?_⟩
    intro j hj
    refine ⟨A, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hderiv j hj y
  have hcbK : cbNorm (4 * p.d + 42) (propagatorW Cf 0 t φ) ≤ A := by
    apply (ENNReal.ofReal_le_ofReal_iff hA0).1
    rw [← HRS.MS.R2WinOrb.s103_cbE_eq hmemK]
    exact hU.2
  have hmemJ : MemCb (r26t3_J p.d) (propagatorW Cf 0 t φ) :=
    HRS.MS.R2Obs.s910_memCb_mono (by
      dsimp [r26t3_J]
      omega) hmemK
  have hcbJ : cbNorm (r26t3_J p.d) (propagatorW Cf 0 t φ) ≤ A :=
    (HRS.MS.R2Obs.s910_cbNorm_mono (by
      dsimp [r26t3_J]
      omega) (propagatorW Cf 0 t φ)).trans hcbK
  obtain ⟨haMem, haNorm, -, -⟩ := hresp (propagatorW Cf 0 t φ) hmemJ
  have habs : |r26t3_a R (propagatorW Cf 0 t φ) x| ≤
      cbNorm (r26t3_k p.d + 2) (r26t3_a R (propagatorW Cf 0 t φ)) := by
    have h0 := HRS.MS.R2Obs.s910_norm_iter_le_cb haMem (j := 0) (by omega) x
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using h0
  calc
    |r26t3_a R (propagatorW Cf 0 t φ) x| ≤
        cbNorm (r26t3_k p.d + 2) (r26t3_a R (propagatorW Cf 0 t φ)) := habs
    _ ≤ C * cbNorm (r26t3_J p.d) (propagatorW Cf 0 t φ) := haNorm
    _ ≤ C * A := mul_le_mul_of_nonneg_left hcbJ hC0
    _ = C * (|Co| * s103_b p.d α) := by rfl

theorem fp81s21_response_modes_memℓp_of_orbits
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) {Co co : ℝ}
    (hclaims : S103nOrbitClaims p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    (b : ℝ) (hb : 0 ≤ b) (t : Icc (0 : ℝ) p.T) (x : Euc p.d) :
    Memℓp (fun α : MultiIndex p.d =>
      r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x) 2 := by
  obtain ⟨C, hC0, hmode⟩ := fp81s21_response_mode_bound_of_orbits
    hδ hδh R hγ hclaims hterm
  let A : ℝ := C * |Co|
  have hA0 : 0 ≤ A := mul_nonneg hC0 (abs_nonneg Co)
  have hsq : Summable (fun α : MultiIndex p.d =>
      (A * s103_b p.d α) ^ 2) := by
    have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
    have hbase := HRS.MS.ProClosureS111.stationary_weight_square_summable
      hd1
    have hscaled := hbase.mul_left (A ^ 2)
    convert hscaled using 1
    ext α
    dsimp [A]
    ring
  apply HRS.MS.CovMeas.s101_memℓp_of_bound hsq
  intro α
  have htime : 0 ≤ b + (t : ℝ) := by linarith [hb, t.2.1]
  have hbound := hmode (b + (t : ℝ)) htime α x
  simpa [A, mul_assoc, mul_left_comm, mul_comm] using hbound

/-- For the actual preparation, response coordinates along every shifted
physical window form an ℓ² sequence at every point and time.  The common
radius is selected before the trajectory, shift, time, and point. -/
theorem fp81s21_response_coordinates_memℓp (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ),
        0 < p.γ → ∀ b : ℝ, 0 ≤ b → ∀ t : Icc (0 : ℝ) p.T, ∀ x : Euc p.d,
          Memℓp (fun α : MultiIndex p.d =>
            r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x) 2 := by
  obtain ⟨δ0, Co, co, hδ0, hδhalf, hco, hcommon⟩ := fp81s21_common_radius p
  refine ⟨δ0, hδ0, hδhalf, fun δ hδ hδle R hγ b hb t x => ?_⟩
  obtain ⟨hclaims, -, hterm, -⟩ := hcommon δ hδ hδle R.ρβ R.thermal
  have hδh : δ ≤ 1 / 2 := hδle.trans hδhalf
  exact fp81s21_response_modes_memℓp_of_orbits hδ hδh R hγ hclaims hterm b hb t x

#print axioms fp81s21_response_coordinates_memℓp
#print axioms fp81s21_response_mode_bound_of_orbits
#print axioms fp81s21_response_modes_memℓp_of_orbits

end HRS.Fp81.S21

end
