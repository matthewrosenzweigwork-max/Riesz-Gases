import HRS.MS.Fp81S21PredMap5
import HRS.MS.GoMeasAux1
import HRS.MS.MovAdjAux7
import HRS.MS.FcauTie
import HRS.MS.FixEqP1Aux1

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas HRS.MS.Go HRS.MS.FixEq
  HRS.MS.MovAdj

/-- Uniform spatial regularity and bounds turn source-time continuity of the
propagator into convergence in the weighted Sobolev energy. -/
theorem fp81s21_prop_source_norm_tendsto
    {d r : ℕ} {Pw q B : ℝ} {C : WholeCoeff d} {f : Euc d → ℝ}
    (hP : (d : ℝ) < 2 * Pw) (hB : 0 ≤ B)
    (hreg : ∀ u ∈ Icc (0 : ℝ) q,
      ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (propagatorW C u q f))
    (hbound : ∀ u ∈ Icc (0 : ℝ) q, ∀ j ≤ r + 1, ∀ x,
      ‖iteratedFDeriv ℝ j (propagatorW C u q f) x‖ ≤ B)
    (us : ℕ → Icc (0 : ℝ) q) (u : Icc (0 : ℝ) q)
    (hus : Tendsto us atTop (𝓝 u)) :
    Tendsto (fun n => (weightedSobolevE r Pw
      (fun x => propagatorW C u q f x - propagatorW C (us n) q f x)).toReal)
      atTop (𝓝 0) := by
  by_cases hex : ∃ F, IsClassicalAdjointW C q f F
  · let F₀ : Euc d → ℝ := propagatorW C (u : ℝ) q f
    let Fₙ : ℕ → Euc d → ℝ := fun n => propagatorW C (us n : ℝ) q f
    have hpoint : ∀ x, Tendsto (fun n => Fₙ n x) atTop (𝓝 (F₀ x)) := by
      intro x
      have hcontOn : ContinuousOn (fun v : ℝ => propagatorW C v q f x) (Icc (0 : ℝ) q) :=
        s67_cont_time (HRS.MS.Fcau.propagatorW_isClassical hex) x
      have hcont : Continuous (fun v : Icc (0 : ℝ) q => propagatorW C (v : ℝ) q f x) := by
        have hh := hcontOn.domRestrict
        have heq : (Icc (0 : ℝ) q).domRestrict
            (fun v : ℝ => propagatorW C v q f x) =
            fun v : Icc (0 : ℝ) q => propagatorW C (v : ℝ) q f x := by
          funext v
          rfl
        rw [heq] at hh
        exact hh
      exact (hcont.tendsto u).comp hus
    have hdl := s55m_dl r hB (h := Fₙ) (h₀ := F₀)
      (fun n => hreg (us n : ℝ) (us n).property)
      (fun n j hj x => hbound (us n : ℝ) (us n).property j hj x)
      hpoint
    have hF₀ : ContDiff ℝ r F₀ := hdl.1
    have hFₙ : ∀ n, ContDiff ℝ r (Fₙ n) := by
      intro n
      exact (hreg (us n : ℝ) (us n).property).of_le (by exact_mod_cast Nat.le_succ r)
    have hlim : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x,
        Tendsto (fun n => partialDeriv i (Fₙ n) x) atTop (𝓝 (partialDeriv i F₀ x)) := by
      intro j hj i x
      let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
        (fun l : Fin j => EuclideanSpace.single (i l) (1 : ℝ))
      have hev := (ev.continuous.tendsto _).comp (hdl.2 j hj x)
      simpa [Function.comp_def, partialDeriv, ev] using hev
    have hfb : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i F₀ x| ≤ B := by
      intro j hj i x
      exact (s57p_abs_partialDeriv_le i F₀ x).trans
        (hbound (u : ℝ) u.property j (by omega) x)
    have hgb : ∀ n, ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x,
        |partialDeriv i (Fₙ n) x| ≤ B := by
      intro n j hj i x
      exact (s57p_abs_partialDeriv_le i (Fₙ n) x).trans
        (hbound (us n : ℝ) (us n).property j (by omega) x)
    have hS := (s57p_S_tendsto (d := d) (P := Pw) (r := r) hP F₀ Fₙ B
      hF₀ hFₙ hfb hgb hlim).2
    have hE : Tendsto (fun n => weightedSobolevE r Pw (fun x => F₀ x - Fₙ n x))
        atTop (𝓝 0) := by
      have hcr : Continuous fun a : ℝ≥0∞ => a ^ (1 / 2 : ℝ) := ENNReal.continuous_rpow_const
      have hsqrt := (hcr.tendsto 0).comp hS
      simpa only [Function.comp_def, s57p_E_eq,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hsqrt
    have hreal := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hE
    simpa [Function.comp_def, F₀, Fₙ, ENNReal.toReal_zero] using hreal
  · have hzero : ∀ v x, propagatorW C v q f x = 0 := by
      intro v x
      simp [propagatorW, hex]
    have heq : (fun n => (weightedSobolevE r Pw
        (fun x => propagatorW C u q f x - propagatorW C (us n) q f x)).toReal) =
        fun _ => (0 : ℝ) := by
      funext n
      simp [weightedSobolevE, partialDeriv, hzero]
    rw [heq]
    exact tendsto_const_nhds

#print axioms HRS.Fp81.S21.fp81s21_prop_source_norm_tendsto

end HRS.Fp81.S21
