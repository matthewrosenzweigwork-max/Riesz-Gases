import HRS.MS.Fp81S21WindowFeature10
import HRS.MS.Fp81S21WindowOrbitDecay2
import HRS.MS.Fp81S21WindowFeature5

/-!
# S2.1 packet 15c: coordinatewise positive window bounds

The modewise window decay is applied to both the oscillator terminal input and
its generator terminal input.  The latter is identified with `s101Dt` only on
the strict active interval, leaving the diagonal endpoint in the zero branch.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.CovMeas HRS.MS.Go HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

variable {d : ℕ}

/-- The two moving-orbit estimates from wR33, with their constants fixed
before the observation window variables. -/
def fp81s21_WindowOrbitDecay {δ : ℝ} (p : Parameters) (R : Trajectory p δ)
    (Cs0 cdec : ℝ) : Prop :=
  ∀ a : ℝ, 0 ≤ a → ∀ t' : ℝ, t' ∈ Icc (0 : ℝ) p.T →
    ∀ v : ℝ, v ∈ Icc (0 : ℝ) (a + t') → ∀ α : MultiIndex p.d,
      (∀ f : ℝ → Euc p.d → ℝ,
        IsClassicalAdjointW (r26t3_coeff R) (a + t')
          (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α) f →
        ContDiff ℝ ((4 * p.d + 42 : ℕ) : WithTop ℕ∞)
          (fun x => gradient (f v) x) ∧
        cbNormVecE (4 * p.d + 42) (fun x => gradient (f v) x) ≤
          ENNReal.ofReal (Cs0 * s104_b p.d α *
            Real.exp (-cdec * max (a - v) 0))) ∧
      (∀ f : ℝ → Euc p.d → ℝ,
        IsClassicalAdjointW (r26t3_coeff R) (a + t')
          (generatorW (r26t3_coeff R) (a + t')
            (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α)) f →
        ContDiff ℝ ((4 * p.d + 42 : ℕ) : WithTop ℕ∞)
          (fun x => gradient (f v) x) ∧
        cbNormVecE (4 * p.d + 42) (fun x => gradient (f v) x) ≤
          ENNReal.ofReal (Cs0 * s104_b p.d α *
            Real.exp (-cdec * max (a - v) 0)))

/-- The three scalar coordinate families of the observation-window feature
inherit the positive-order moving decay.  The common multiplier is chosen
before `a`, `v`, `t`, and `x`; it dominates both the wR33 amplitude and the
unpropagated oscillator-test envelope. -/
theorem fp81s21_window_coordinate_pos_bounds
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    {Cs0 cdec : ℝ} (hCs0 : 0 ≤ Cs0) (hcdec : 0 < cdec)
    (hdecay : fp81s21_WindowOrbitDecay p R Cs0 cdec) :
    ∃ Cmix : ℝ, 0 ≤ Cmix ∧ Cs0 ≤ Cmix ∧
      ∀ a : ℝ, 0 ≤ a → ∀ v : ℝ, v ∈ Icc (0 : ℝ) (a + p.T) →
      ∀ α : MultiIndex p.d,
        (∀ j : ℕ, 1 ≤ j → j ≤ 2 * p.d + 9 → ∀ x : Euc p.d,
          ‖iteratedFDeriv ℝ j
            (fun x => if v ≤ a then
              propagatorW (r26t3_coeff R) v a
                (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α) x
              else oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α x) x‖ ≤
              Cmix * s104_b p.d α * Real.exp (-cdec * max (a - v) 0)) ∧
        (∀ t' : ℝ, t' ∈ Icc (0 : ℝ) p.T →
          ∀ j : ℕ, 1 ≤ j → j ≤ 2 * p.d + 9 → ∀ x : Euc p.d,
            ‖iteratedFDeriv ℝ j
              (fun x => if v < a + t' then
                s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                  (a + p.T) v (a + t') α x else 0) x‖ ≤
                Cmix * s104_b p.d α * Real.exp (-cdec * max (a - v) 0)) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ 2 * p.d + 9 → ∀ x : Euc p.d,
          ‖iteratedFDeriv ℝ j
            (fun x => if a < v then
              oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α x else 0) x‖ ≤
              Cmix * s104_b p.d α * Real.exp (-cdec * max (a - v) 0)) := by
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  obtain ⟨Kφ, hKφ, hphi⟩ := fp81s21_window_test_pos_envelope (d := p.d) hd1
  let Cmix : ℝ := max Cs0 Kφ
  have hmix0 : 0 ≤ Cmix := le_trans hCs0 (le_max_left _ _)
  have hCs : Cs0 ≤ Cmix := le_max_left _ _
  have hKφ : Kφ ≤ Cmix := le_max_right _ _
  refine ⟨Cmix, hmix0, hCs, ?_⟩
  intro a ha v hv α
  let C : WholeCoeff p.d := r26t3_coeff R
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let k : ℕ := 2 * p.d + 9
  have hphys : 0 ≤ a + p.T := by linarith [ha, p.hT.le]
  have horb : S104nOrbit C φ (a + p.T) := by
    exact s104b_orbit_of_termRegGen hterm R.admissible R.resulting α
      (a + p.T) hphys
  have hphi' : ∀ j : ℕ, j ≤ 4 * p.d + 42 → ∀ x,
      ‖iteratedFDeriv ℝ j φ x‖ ≤ Kφ * s104_b p.d α := by
    intro j hj x
    have hj' : j ≤ 4 * p.d + 42 := hj
    simpa [φ] using hphi α j hj' x
  have hA0 : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ x : Euc p.d,
      ‖iteratedFDeriv ℝ j
        (fun x => if v ≤ a then propagatorW C v a φ x else φ x) x‖ ≤
          Cmix * s104_b p.d α * Real.exp (-cdec * max (a - v) 0) := by
    intro j hj1 hjk x
    by_cases hva : v ≤ a
    · have hvA : v ∈ Icc (0 : ℝ) a := ⟨hv.1, hva⟩
      have haT : a ∈ Icc (0 : ℝ) (a + p.T) := by constructor <;> linarith [p.hT.le]
      obtain ⟨f, hf⟩ := horb.ex0 a haT
      have hex : ∃ f : ℝ → Euc p.d → ℝ,
          IsClassicalAdjointW C a φ f := ⟨f, by simpa [C, φ] using hf⟩
      have ht0 : (0 : ℝ) ∈ Icc (0 : ℝ) p.T := ⟨le_rfl, p.hT.le⟩
      have hdecayA : ∀ f : ℝ → Euc p.d → ℝ,
          IsClassicalAdjointW C a φ f →
          ContDiff ℝ ((4 * p.d + 42 : ℕ) : WithTop ℕ∞)
              (fun y => gradient (f v) y) ∧
            cbNormVecE (4 * p.d + 42)
              (fun y => gradient (f v) y) ≤
                ENNReal.ofReal (Cs0 * s104_b p.d α *
                  Real.exp (-cdec * max (a - v) 0)) := by
        intro f hf
        have hvA' : v ∈ Icc (0 : ℝ) (a + 0) := by simpa using hvA
        have h := (hdecay a ha 0 ht0 v hvA' α).1 f (by
          simpa only [add_zero] using hf)
        simpa only [add_zero] using h
      have hX : 0 ≤ Cs0 * s104_b p.d α *
          Real.exp (-cdec * max (a - v) 0) :=
        mul_nonneg (mul_nonneg hCs0 (s104_b_nonneg α)) (Real.exp_pos _).le
      have hscalar := fp81s21_scalar_orbit_pos_of_gradient_decay
        (C := C) (T := a) (v := v) (X := Cs0 * s104_b p.d α *
          Real.exp (-cdec * max (a - v) 0)) (ψ := φ)
        (K := 4 * p.d + 42) (k := j) hex hvA hdecayA hX hj1 (by omega)
      have hfac : 0 ≤ s104_b p.d α *
          Real.exp (-cdec * max (a - v) 0) :=
        mul_nonneg (s104_b_nonneg α) (Real.exp_pos _).le
      have hscale : Cs0 * s104_b p.d α *
          Real.exp (-cdec * max (a - v) 0) ≤
          Cmix * s104_b p.d α * Real.exp (-cdec * max (a - v) 0) := by
        calc
          _ = Cs0 * (s104_b p.d α *
              Real.exp (-cdec * max (a - v) 0)) := by ring
          _ ≤ Cmix * (s104_b p.d α *
              Real.exp (-cdec * max (a - v) 0)) :=
            mul_le_mul_of_nonneg_right hCs hfac
          _ = _ := by ring
      simpa [hva, C, φ] using (hscalar x).trans hscale
    · have hav : a < v := lt_of_not_ge hva
      have hjφ : j ≤ 4 * p.d + 42 := by omega
      have hbase := hphi' j hjφ x
      have hmax : max (a - v) 0 = 0 := max_eq_right (by linarith)
      have hscale : Kφ * s104_b p.d α ≤ Cmix * s104_b p.d α :=
        mul_le_mul_of_nonneg_right hKφ (s104_b_nonneg α)
      simpa [hva, C, φ, hmax] using hbase.trans (by simpa using hscale)
  have hAprime : ∀ t' : ℝ, t' ∈ Icc (0 : ℝ) p.T →
      ∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ x : Euc p.d,
        ‖iteratedFDeriv ℝ j
          (fun x => if v < a + t' then
            s101Dt C (wholeSpaceIndex p.d : ℝ) (a + p.T) v (a + t') α x
            else 0) x‖ ≤
          Cmix * s104_b p.d α * Real.exp (-cdec * max (a - v) 0) := by
    intro t' ht' j hj1 hjk x
    by_cases hvt : v < a + t'
    · have hv' : v ∈ Icc (0 : ℝ) (a + t') := ⟨hv.1, hvt.le⟩
      have htT : a + t' ∈ Icc (0 : ℝ) (a + p.T) := by
        constructor <;> linarith [ht'.1, ht'.2, ha]
      obtain ⟨f, hf⟩ := horb.ex1 (a + t') htT
      let ψg : Euc p.d → ℝ := generatorW C (a + t') φ
      have hex : ∃ f : ℝ → Euc p.d → ℝ,
          IsClassicalAdjointW C (a + t') ψg f := ⟨f, by simpa [C, ψg, φ] using hf⟩
      have hOrbit : ∀ f : ℝ → Euc p.d → ℝ,
          IsClassicalAdjointW C (a + t') ψg f →
          ContDiff ℝ ((4 * p.d + 42 : ℕ) : WithTop ℕ∞)
              (fun y => gradient (f v) y) ∧
            cbNormVecE (4 * p.d + 42)
              (fun y => gradient (f v) y) ≤
                ENNReal.ofReal (Cs0 * s104_b p.d α *
                  Real.exp (-cdec * max (a - v) 0)) := by
        intro f hf
        simpa [C, ψg, φ] using (hdecay a ha t' ht' v hv' α).2 f hf
      have hX : 0 ≤ Cs0 * s104_b p.d α *
          Real.exp (-cdec * max (a - v) 0) :=
        mul_nonneg (mul_nonneg hCs0 (s104_b_nonneg α)) (Real.exp_pos _).le
      have hscalar := fp81s21_scalar_orbit_pos_of_gradient_decay
        (C := C) (T := a + t') (v := v)
        (X := Cs0 * s104_b p.d α * Real.exp (-cdec * max (a - v) 0))
        (ψ := ψg) (K := 4 * p.d + 42) (k := j) hex hv' hOrbit hX hj1 (by omega)
      have hvEnd : v < a + p.T := by linarith [hvt, ht'.2]
      have hvH : v ∈ Icc (0 : ℝ) (a + p.T) := ⟨hv.1, hv.2⟩
      have htphys : a + t' ∈ Icc v (a + p.T) := ⟨hvt.le, by linarith [ht'.2]⟩
      have hident := fp81s21_window_s101Dt_eq_generator p R p.hT ha hvH hvEnd
        hterm (a + t') htphys α
      have hfac : 0 ≤ s104_b p.d α *
          Real.exp (-cdec * max (a - v) 0) :=
        mul_nonneg (s104_b_nonneg α) (Real.exp_pos _).le
      have hscale : Cs0 * s104_b p.d α *
          Real.exp (-cdec * max (a - v) 0) ≤
          Cmix * s104_b p.d α * Real.exp (-cdec * max (a - v) 0) := by
        calc
          _ = Cs0 * (s104_b p.d α *
              Real.exp (-cdec * max (a - v) 0)) := by ring
          _ ≤ Cmix * (s104_b p.d α *
              Real.exp (-cdec * max (a - v) 0)) :=
            mul_le_mul_of_nonneg_right hCs hfac
          _ = _ := by ring
      have hscalar' := (hscalar x).trans hscale
      have hfun : (fun y : Euc p.d => if v < a + t' then
          s101Dt C (wholeSpaceIndex p.d : ℝ) (a + p.T) v (a + t') α y else 0) =
          fun y => propagatorW C v (a + t') ψg y := by
        funext y
        simp [hvt, hident y, C, ψg, φ]
      rw [hfun]
      exact hscalar'
    · simp only [hvt, if_false]
      rw [s55f_iter_zero]
      exact mul_nonneg (mul_nonneg hmix0 (s104_b_nonneg α)) (Real.exp_pos _).le
  have hB : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ x : Euc p.d,
      ‖iteratedFDeriv ℝ j
        (fun x => if a < v then φ x else 0) x‖ ≤
          Cmix * s104_b p.d α * Real.exp (-cdec * max (a - v) 0) := by
    intro j hj1 hjk x
    by_cases hav : a < v
    · have hjφ : j ≤ 4 * p.d + 42 := by omega
      have hbase := hphi' j hjφ x
      have hmax : max (a - v) 0 = 0 := max_eq_right (by linarith)
      have hscale : Kφ * s104_b p.d α ≤ Cmix * s104_b p.d α :=
        mul_le_mul_of_nonneg_right hKφ (s104_b_nonneg α)
      simpa [hav, φ, hmax] using hbase.trans (by simpa using hscale)
    · simp only [hav, if_false]
      rw [s55f_iter_zero]
      exact mul_nonneg (mul_nonneg hmix0 (s104_b_nonneg α)) (Real.exp_pos _).le
  simpa only [k] using And.intro hA0 (And.intro hAprime hB)

#print axioms fp81s21_window_coordinate_pos_bounds

end HRS.Fp81.S21

end
