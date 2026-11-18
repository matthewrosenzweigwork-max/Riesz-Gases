import HRS.MS.Fp81S21WindowOrbitDecay

/-!
# HRS S2.1(iii), SOL40 packet 15b: observation-window orbit estimates

This file specializes the all-time moving orbit estimates to terminal times
`a + t'`.  Since `t' ≥ 0`, the exponential tail is controlled by the distance
from the observation start `a`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.R2WinErr

/-- Convert an all-time `R2OrbitGrad` estimate into an observation-window estimate.
The later terminal time improves the exponent from `t - v` to `max (a - v) 0`. -/
private theorem fp81s21_orbitGrad_observation_window_bound
    {d k : ℕ} {C : WholeCoeff d} {a t' v A c : ℝ} {φ : Euc d → ℝ}
    (hA : 0 ≤ A) (hc : 0 < c) (ht' : 0 ≤ t')
    (hv : v ∈ Set.Icc (0 : ℝ) (a + t'))
    (hOrbit : R2OrbitGrad C k (a + t') φ A c)
    (f : ℝ → Euc d → ℝ)
    (hf : IsClassicalAdjointW C (a + t') φ f) :
    ContDiff ℝ k (fun x => gradient (f v) x) ∧
      cbNormVecE k (fun x => gradient (f v) x) ≤
        ENNReal.ofReal (A * Real.exp (-c * max (a - v) 0)) := by
  have hmax : max (a - v) 0 ≤ a + t' - v := by
    apply max_le
    · linarith
    · linarith [hv.2]
  have hexp : Real.exp (-c * (a + t' - v)) ≤
      Real.exp (-c * max (a - v) 0) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hmax (by linarith)
  have hscale : A * Real.exp (-c * (a + t' - v)) ≤
      A * Real.exp (-c * max (a - v) 0) :=
    mul_le_mul_of_nonneg_left hexp hA
  obtain ⟨hcont, hbound⟩ := hOrbit f hf v hv
  refine ⟨hcont, ?_⟩
  calc
    cbNormVecE k (fun x => gradient (f v) x) ≤
        ENNReal.ofReal (A * Real.exp (-c * (a + t' - v))) := hbound
    _ ≤ ENNReal.ofReal (A * Real.exp (-c * max (a - v) 0)) :=
      ENNReal.ofReal_le_ofReal hscale

/-- The positive weighted amplitude for the whole oscillator family on an
observation window. -/
def fp81s21_window_Bpos (d : ℕ) (Cs0 cdec a v : ℝ) : ℝ :=
  Cs0 * Real.sqrt (∑' α : MultiIndex d, (s104_b d α) ^ 2) *
    Real.exp (-cdec * max (a - v) 0)

/-- Square summability of `s104_b` gives the exact ℓ² amplitude carried by
`fp81s21_window_Bpos`. -/
theorem fp81s21_window_orbit_amplitude_sq_sum
    {d : ℕ} (Cs0 cdec a v : ℝ) (hCs0 : 0 ≤ Cs0)
    (hsum : Summable (s104_b d)) :
    0 ≤ fp81s21_window_Bpos d Cs0 cdec a v ∧
      Summable (fun α : MultiIndex d =>
        (Cs0 * s104_b d α * Real.exp (-cdec * max (a - v) 0)) ^ 2) ∧
      (∑' α : MultiIndex d,
        (Cs0 * s104_b d α * Real.exp (-cdec * max (a - v) 0)) ^ 2) =
        (fp81s21_window_Bpos d Cs0 cdec a v) ^ 2 := by
  let q : ℝ := Cs0 * Real.exp (-cdec * max (a - v) 0)
  have hsq : Summable (fun α : MultiIndex d => (s104_b d α) ^ 2) :=
    HRS.MS.R2GenInit.s105_b_sq_summable hsum
  refine ⟨?_, ?_, ?_⟩
  · dsimp [fp81s21_window_Bpos]
    positivity
  · have hmul := hsq.mul_left (q ^ 2)
    refine hmul.congr fun α => ?_
    dsimp [q]
    ring
  · calc
      (∑' α : MultiIndex d,
          (Cs0 * s104_b d α * Real.exp (-cdec * max (a - v) 0)) ^ 2) =
        ∑' α : MultiIndex d, q ^ 2 * (s104_b d α) ^ 2 := by
          apply tsum_congr
          intro α
          dsimp [q]
          ring
      _ = q ^ 2 * ∑' α : MultiIndex d, (s104_b d α) ^ 2 := tsum_mul_left
      _ = (fp81s21_window_Bpos d Cs0 cdec a v) ^ 2 := by
          dsimp [fp81s21_window_Bpos, q]
          have hsum0 : 0 ≤ ∑' α : MultiIndex d, (s104_b d α) ^ 2 :=
            tsum_nonneg fun α => sq_nonneg (s104_b d α)
          simp only [mul_pow, Real.sq_sqrt hsum0]
          ring

/-- Common moving-orbit decay on every observation window of length `p.T`,
for both the terminal test and its generator terminal derivative. -/
theorem fp81s21_moving_observation_window_orbit_decay (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ Cs0 cdec : ℝ, 0 ≤ Cs0 ∧ 0 < cdec ∧ Summable (s104_b p.d) ∧
          Summable (fun α : MultiIndex p.d => (s104_b p.d α) ^ 2) ∧
          ∀ a : ℝ, 0 ≤ a → ∀ t' : ℝ, t' ∈ Set.Icc (0 : ℝ) p.T →
            ∀ v : ℝ, v ∈ Set.Icc (0 : ℝ) (a + t') →
              ∀ α : MultiIndex p.d,
                (∀ f : ℝ → Euc p.d → ℝ,
                  IsClassicalAdjointW (r26t3_coeff R) (a + t')
                    (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α) f →
                  ContDiff ℝ ((4 * p.d + 42 : ℕ) : WithTop ℕ∞)
                    (fun x => gradient (f v) x) ∧
                  cbNormVecE (4 * p.d + 42)
                    (fun x => gradient (f v) x) ≤
                    ENNReal.ofReal (Cs0 * s104_b p.d α *
                      Real.exp (-cdec * max (a - v) 0))) ∧
                (∀ f : ℝ → Euc p.d → ℝ,
                  IsClassicalAdjointW (r26t3_coeff R) (a + t')
                    (generatorW (r26t3_coeff R) (a + t')
                      (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α)) f →
                  ContDiff ℝ ((4 * p.d + 42 : ℕ) : WithTop ℕ∞)
                    (fun x => gradient (f v) x) ∧
                  cbNormVecE (4 * p.d + 42)
                    (fun x => gradient (f v) x) ≤
                    ENNReal.ofReal (Cs0 * s104_b p.d α *
                      Real.exp (-cdec * max (a - v) 0))) := by
  obtain ⟨δ0, hδ0, hδ0half, hdecay⟩ :=
    fp81s21_moving_orbit_gradient_decay p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨Cs0, cdec, hCs0, hcdec, hsum, hgrad⟩ :=
    hdecay δ hδ hδle R
  have hsumSq : Summable (fun α : MultiIndex p.d => (s104_b p.d α) ^ 2) :=
    HRS.MS.R2GenInit.s105_b_sq_summable hsum
  refine ⟨Cs0, cdec, hCs0, hcdec, hsum, hsumSq, ?_⟩
  intro a ha t' ht v hv α
  have hterminal : 0 ≤ a + t' := by linarith [ha, ht.1]
  have hA : 0 ≤ Cs0 * s104_b p.d α :=
    mul_nonneg hCs0 (s104_b_nonneg α)
  have hgradPhi : R2OrbitGrad (r26t3_coeff R) (4 * p.d + 42)
      (a + t') (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α)
      (Cs0 * s104_b p.d α) cdec := (hgrad α).1 (a + t') hterminal
  have hgradGen : R2OrbitGrad (r26t3_coeff R) (4 * p.d + 42)
      (a + t')
      (generatorW (r26t3_coeff R) (a + t')
        (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α))
      (Cs0 * s104_b p.d α) cdec := (hgrad α).2 (a + t') hterminal
  refine ⟨?_, ?_⟩
  · intro f hf
    simpa only [r26t3_coeff] using
      fp81s21_orbitGrad_observation_window_bound hA hcdec ht.1 hv
        hgradPhi f hf
  · intro f hf
    simpa only [r26t3_coeff] using
      fp81s21_orbitGrad_observation_window_bound hA hcdec ht.1 hv
        hgradGen f hf

#print axioms fp81s21_orbitGrad_observation_window_bound
#print axioms fp81s21_window_orbit_amplitude_sq_sum
#print axioms fp81s21_moving_observation_window_orbit_decay

end HRS.Fp81.S21

end
