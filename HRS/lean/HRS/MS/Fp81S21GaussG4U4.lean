import HRS.MS.Fp81S21WindowFeature4
import HRS.MS.S104bNL6
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Terminal-generator integrability for the oscillator modes. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.Fp81.S21
open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL HRS.MS.S53

/-- A terminal orbit has continuous scalar and gradient generator paths,
so both are integrable on every later compact time interval. -/
theorem fp81s21_g4_orbit_integrable
    {d : ℕ} {C : WholeCoeff d} {f : Euc d → ℝ} {T r v w : ℝ}
    (horb : S104nOrbit C f T) (hr : 0 ≤ r) (hrv : r ≤ v)
    (hvw : v ≤ w) (hwT : w ≤ T) (x : Euc d) :
    IntegrableOn (fun q => propagatorW C r q (generatorW C q f) x) (Icc v w) ∧
    IntegrableOn (fun q => gradient (propagatorW C r q (generatorW C q f)) x) (Icc v w) := by
  let G : ℝ → Euc d → ℝ := fun τ =>
    propagatorW C r (r + τ) (generatorW C (r + τ) f)
  have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr, hrv.trans (hvw.trans hwT)⟩
  have hG : ∀ τ ∈ Icc (0 : ℝ) (T - r), MemCb 2 (G τ) :=
    fun τ hτ => horb.cb1 hrT hτ
  obtain ⟨G2, hG2, hd12⟩ := horb.diff12 r hrT
  have hc : S53Cont (T - r) G := s53_cont_of_diff hG hG2 hd12
  have hscalar : ContinuousOn (fun τ => G τ x) (Icc (0 : ℝ) (T - r)) := by
    intro τ hτ
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨η, hη, hh⟩ := hc τ hτ (ε / 2) (by positivity)
    refine ⟨η, hη, fun τ' hτ' hdist => ?_⟩
    have h := hh τ' hτ' (by simpa [Real.dist_eq] using hdist) 0 (by norm_num) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    rw [Real.dist_eq]
    linarith
  have hgrad : ContinuousOn (fun τ => gradient (G τ) x) (Icc (0 : ℝ) (T - r)) := by
    have h : Continuous (fun τ : ℝ => gradient (G (s53_clamp (T - r) τ)) x) :=
      (s53_grad_continuous (by linarith : 0 ≤ T - r) hG hc).comp
        (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => x)))
    refine h.continuousOn.congr ?_
    intro τ hτ
    simp only [Function.comp_def]
    rw [s53_clamp_of_mem hτ]
  have hmap : MapsTo (fun q : ℝ => q - r) (Icc v w) (Icc (0 : ℝ) (T - r)) := by
    intro q hq
    constructor <;> linarith [hq.1, hq.2]
  have hshift : ContinuousOn (fun q : ℝ => q - r) (Icc v w) :=
    continuousOn_id.sub continuousOn_const
  constructor
  · have h := (hscalar.comp hshift hmap).integrableOn_Icc (μ := volume)
    simpa [Function.comp_def, G, add_sub_cancel] using h
  · have h := (hgrad.comp hshift hmap).integrableOn_Icc (μ := volume)
    simpa [Function.comp_def, G, add_sub_cancel] using h

/-- Both Duhamel integrands are integrable for every physical oscillator mode,
with one radius chosen before the mode and times. -/
theorem fp81s21_g4_mode_integrable (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ α : MultiIndex p.d, ∀ r v w : ℝ, 0 ≤ r → r ≤ v → v ≤ w →
          ∀ x : Euc p.d,
          IntegrableOn (fun q => r26t3_U R r q
            (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x)
            (Icc v w) ∧
          IntegrableOn (fun q => gradient (r26t3_U R r q
            (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x)
            (Icc v w) := by
  obtain ⟨δ0, Co, co, hδ0, hhalf, hco, hcommon⟩ := fp81s21_common_radius p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R α r v w hr hrv hvw x
  obtain ⟨_, _, hterm, _⟩ := hcommon δ hδ hδle R.ρβ R.thermal
  have hw : 0 ≤ w := hr.trans (hrv.trans hvw)
  have horb := s104b_orbit_of_termRegGen hterm R.admissible R.resulting α w hw
  simpa [r26t3_U, r26t3_coeff] using fp81s21_g4_orbit_integrable horb hr hrv hvw le_rfl x

#print axioms fp81s21_g4_orbit_integrable
#print axioms fp81s21_g4_mode_integrable
end HRS.Fp81.S21
end
