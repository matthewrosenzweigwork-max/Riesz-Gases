import HRS.MS.Fp81S21WeightedDrift
import HRS.MS.ProClosureS111WindowRestriction
import HRS.MS.ProClosureS111ChartSections
import HRS.MS.R2InterpAux19
import HRS.MS.Fp81S21MovingStd

/-!
# HRS S2.1(iii), SOL26 packet 14: shifted weighted drift variation

The stationary contracts that determine the moving packet's types are stated
first. The covariance theorem is finite-horizon and requires both
`IsR2L1F` and `R2JIntegrandMeas`; this drift packet does not construct that
covariance path.

```lean
def IsR2L1F (r : ℕ) (Pw T : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) : Prop :=
  (∀ u ∈ Set.Icc (0 : ℝ) T, (∀ f g, IsR2WeightedTest r Pw f → IsR2WeightedTest r Pw g →
      z u (f + g) = z u f + z u g) ∧
    (∀ (c : ℝ) f, IsR2WeightedTest r Pw f → z u (c • f) = c * z u f) ∧
    ∃ M : ℝ, ∀ f, IsR2WeightedTest r Pw f →
      |z u f| ≤ M * (weightedSobolevE r Pw f).toReal) ∧
  (∀ f, IsR2WeightedTest r Pw f → Measurable fun u => z u f) ∧
  ∫⁻ u in Set.Icc (0 : ℝ) T, dualNormE r Pw (z u) < ⊤

def R2JIntegrandMeas (C : WholeCoeff d) (m T : ℝ)
    (z : ℝ → (Euc d → ℝ) → ℝ) : Prop :=
  ∀ (ta tb : ℝ) (φa φb : Euc d → ℝ), IsR2DualCombo m φa → IsR2DualCombo m φb →
    ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
    AEMeasurable (fun u => z u (fun x =>
      inner ℝ (gradient (propagatorW C u ta φa) x)
        (gradient (propagatorW C u tb φb) x)))
      (volume.restrict (Set.Icc (0 : ℝ) (min ta tb)))

def IsR2JValue (C : WholeCoeff d) (m T : ℝ)
    (z : ℝ → (Euc d → ℝ) → ℝ) (I : Set ℝ)
    (J : TensorDual (OscPath d m T) 2) : Prop :=
  J ∈ projTensor (OscPath d m T) 2 ∧
  ∀ (ta tb : ℝ) (φa φb : Euc d → ℝ)
      (l₁ l₂ : StrongDual ℝ (OscPath d m T)),
    IsR2DualCombo m φa → IsR2DualCombo m φb →
    ta ∈ Set.Icc (0 : ℝ) T → tb ∈ Set.Icc (0 : ℝ) T →
    (∀ w, l₁ w = OscDual.eval (r2PathAt w ta) φa) →
    (∀ w, l₂ w = OscDual.eval (r2PathAt w tb) φb) →
    J ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]) =
      2 * C.ν * ∫ u in I ∩ Set.Icc (0 : ℝ) (min ta tb), z u (fun x =>
        inner ℝ (gradient (propagatorW C u ta φa) x)
          (gradient (propagatorW C u tb φb) x))

def R2OrbitGrad (C : WholeCoeff d) (k : ℕ) (t : ℝ)
    (φ : Euc d → ℝ) (A c : ℝ) : Prop :=
  ∀ f : ℝ → Euc d → ℝ, IsClassicalAdjointW C t φ f →
    ∀ r ∈ Set.Icc (0 : ℝ) t,
      ContDiff ℝ k (fun x => gradient (f r) x) ∧
      cbNormVecE k (fun x => gradient (f r) x) ≤
        ENNReal.ofReal (A * Real.exp (-c * (t - r)))

theorem r2_covariance_measure (hd : 2 ≤ d) (C : WholeCoeff d)
    (m T : ℝ) (hT : 0 < T) (r : ℕ) (Pw : ℝ)
    (hP : (d : ℝ) / 2 < Pw) (horb : R2OrbitSummable C m T r)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T →
      ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c • ψ) =
          propagatorW C u t φ + c • propagatorW C u t ψ) :
    ∃ (K : ℝ)
      (Jm : (ℝ → (Euc d → ℝ) → ℝ) → ℝ → ℝ →
        projTensor (OscPath d m T) 2),
      (∀ z z', IsR2L1F r Pw T z → IsR2L1F r Pw T z' →
        R2JIntegrandMeas C m T z → R2JIntegrandMeas C m T z' →
        ∀ a a', Jm (z + z') a a' = Jm z a a' + Jm z' a a') ∧
      (∀ (c : ℝ) z, IsR2L1F r Pw T z → R2JIntegrandMeas C m T z →
        ∀ a a', Jm (c • z) a a' = c • Jm z a a') ∧
      ∀ z, IsR2L1F r Pw T z → R2JIntegrandMeas C m T z →
        (∀ a b c, 0 ≤ a → a ≤ b → b ≤ c → c ≤ T →
          Jm z a c = Jm z a b + Jm z b c) ∧
        (∀ a, Jm z a a = 0) ∧
        ContinuousOn (fun u => Jm z 0 u) (Set.Icc 0 T) ∧
        eVariationOn (fun u => Jm z 0 u) (Set.Icc 0 T) ≤
          ENNReal.ofReal K * ∫⁻ u in Set.Icc (0 : ℝ) T, dualNormE r Pw (z u) ∧
        ∀ a a', 0 ≤ a → a ≤ a' → a' ≤ T →
          IsR2JValue C m T z (Set.Ioc a a') (Jm z a a')

structure S102Drift (C : WholeCoeff d) (m T : ℝ) (r : ℕ) (Pw : ℝ)
    (b : ℝ → (Euc d → ℝ) → ℝ) (Mb : ℝ → ℝ) : Prop where
  hZ : ∀ u ∈ Icc (0 : ℝ) T, S102Z r Pw (b u)
  hM : ∀ u ∈ Icc (0 : ℝ) T, ∀ f, IsR2WeightedTest r Pw f →
    |b u f| ≤ Mb u * (weightedSobolevE r Pw f).toReal
  Mb_nonneg : ∀ u, 0 ≤ Mb u
  Mb_int : IntegrableOn Mb (Icc 0 T)
  meas : ∀ t ∈ Icc (0 : ℝ) T, ∀ α : MultiIndex d,
    AEStronglyMeasurable
      (fun u => b u (propagatorW C u t (oscTestFun m α)))
      (volume.restrict (Icc 0 t))

theorem s102_Vprop_coord (hP : (d : ℝ) < 2 * Pw)
    (hD : S101Data C m T r c) (hz : S102Z r Pw z)
    (hlin : S102Lin C m T) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T)
    {t : ℝ} (ht : t ∈ Icc u T) (α : MultiIndex d) :
    OscDual.coord (r2Vprop C m t u z) α =
      z (propagatorW C u t (oscTestFun m α))

theorem s102_driftInc_norm_le (hP : (d : ℝ) < 2 * Pw)
    (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) (hT : 0 ≤ T)
    {a a' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') (ha'T : a' ≤ T) :
    ‖r2DriftInc C m T b a a'‖ ≤
      s102_KV d r Pw c * ∫ u in Ioc a a', Mb u

theorem s102_drift_bv (hP : (d : ℝ) < 2 * Pw)
    (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) (hT : 0 ≤ T) :
    BoundedVariationOn (fun s => r2DriftInc C m T b 0 s) (Icc 0 T) ∧
      r2DriftInc C m T b 0 0 = 0
```

The packet-38 drift producer consumes the following interval-local statement.
Here `Dcum v` is the full-history drift through source time `v`, restricted
to the observation window `[a,a+T]`.  The constant `K` and the decay rate `c`
are chosen before `a`, `T`, `H`, the field `b`, and the source interval.

```lean
let Dcum : ℝ → OscPath d m T := fun v =>
  HRS.MS.ProClosureS111.physicalWindowRestriction ha hwin
    (r2DriftInc C m H b 0 v)

∀ q r', 0 ≤ q → q ≤ r' → r' ≤ H →
  eVariationOn Dcum (Set.Icc q r') ≤
    ENNReal.ofReal K * ∫⁻ v in Set.Ioc q r',
      ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) *
        dualNormE r Pw (b v)
```

This is a variation bound in the source variable, not a variation density in
the terminal-path parameter.  The matching remote-tail scalar contract is
the same bound on `[0,(a-L)₊]`; since `max (a-v) 0 ≥ L` there, the weighted
integral gives the exponential remote factor after the packet-4 first-moment
bound.  The pointwise action theorem below is the reusable analytic input.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R2Interp HRS.MS.R2WinOrb HRS.MS.FixEq HRS.MS.R26T3

/-- The cumulative drift increment, transported to the physical window. -/
def fp81s21_weightedDrift_windowCum {d : ℕ} {m T H a : ℝ}
    (ha : 0 ≤ a) (hwin : a + T ≤ H) (C : WholeCoeff d)
    (b : ℝ → (Euc d → ℝ) → ℝ) (v : ℝ) : OscPath d m T :=
  HRS.MS.ProClosureS111.physicalWindowRestriction ha hwin
    (r2DriftInc C m H b 0 v)

/-- A source-time interval drift increment, transported to the physical
observation window. -/
def fp81s21_weightedDrift_windowInc {d : ℕ} {m T H a : ℝ}
    (ha : 0 ≤ a) (hwin : a + T ≤ H) (C : WholeCoeff d)
    (b : ℝ → (Euc d → ℝ) → ℝ) (q r' : ℝ) : OscPath d m T :=
  HRS.MS.ProClosureS111.physicalWindowRestriction ha hwin
    (r2DriftInc C m H b q r')

/-- The moving drift acts on the centered adjoint orbit with a decaying
weighted-Sobolev bound, and therefore with the actual `dualNormE` norm of the
drift functional.  The supremum orbit bound is used only to place the centered
function in the bounded-derivative core used by `s57p_dual_bound`; it does not
enter the resulting constant. -/
theorem fp81s21_weightedDrift_action_le
    {d k r : ℕ} {C : WholeCoeff d} {m H s u A c P : ℝ}
    {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    {b : ℝ → (Euc d → ℝ) → ℝ} {Mb : ℝ → ℝ}
    (hP : (d : ℝ) < 2 * (P - 1)) (hA : 0 ≤ A)
    (hSup : R2OrbitSup C k s φ A)
    (hGrad : R2OrbitGrad C k s φ A c)
    (hf : IsClassicalAdjointW C s φ f)
    (hu : u ∈ Icc (0 : ℝ) s) (hsH : s ≤ H) (hr : r ≤ k + 1)
    (hb : HRS.MS.R2Interp.S102Drift C m H r P b Mb)
    (hshift : b u (propagatorW C u s φ) =
      b u (fun x => propagatorW C u s φ x - propagatorW C u s φ 0)) :
    |b u (propagatorW C u s φ)| ≤
      (dualNormE r P (b u)).toReal *
        (s57pC d r (P - 1) * (A * Real.exp (-c * (s - u)))) := by
  have huH : u ∈ Icc (0 : ℝ) H := ⟨hu.1, hu.2.trans hsH⟩
  have hprop : IsClassicalAdjointW C s φ (fun v => propagatorW C v s φ) :=
    s102_propagator_classical ⟨f, hf⟩
  let g : Euc d → ℝ := fun x => propagatorW C u s φ x - propagatorW C u s φ 0
  let B : ℝ := A * Real.exp (-c * (s - u))
  have hB : 0 ≤ B := mul_nonneg hA (Real.exp_pos _).le
  obtain ⟨hGradSmooth, hGradBound⟩ := hGrad (fun v => propagatorW C v s φ) hprop u hu
  have hSmooth : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (propagatorW C u s φ) :=
    HRS.MS.R2WinOrb.s103_fderiv_contDiff
      ((hprop.c2 u hu).differentiable (by norm_num)) hGradSmooth
  have hJets := HRS.MS.R2WinOrbNL.s103c_jets_of_cb hB hSmooth hGradBound
  obtain ⟨_, hSupBound⟩ := hSup (fun v => propagatorW C v s φ) hprop u hu
  have hZeroJets := HRS.MS.R2WinOrb.s103_cb_of_E hA hSupBound
  have hgSmooth : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g := by
    dsimp [g]
    exact hSmooth.sub contDiff_const
  have hM0 : ∀ x, ‖g x‖ ≤ 2 * A := by
    intro x
    dsimp [g]
    calc ‖propagatorW C u s φ x - propagatorW C u s φ 0‖ ≤
        ‖propagatorW C u s φ x‖ + ‖propagatorW C u s φ 0‖ := norm_sub_le _ _
      _ ≤ A + A := by
        have hx := hZeroJets 0 (Nat.zero_le _) x
        have h0 := hZeroJets 0 (Nat.zero_le _) 0
        simpa using add_le_add hx h0
      _ = 2 * A := by ring
  have hDerivBound : ∀ j ≤ r, ∀ x,
      ‖iteratedFDeriv ℝ j g x‖ ≤ max (2 * A) B := by
    intro j hj x
    by_cases hj0 : j = 0
    · subst j
      simpa [iteratedFDeriv_zero_apply] using
        (hM0 x).trans (le_max_left _ _)
    · have hsub : iteratedFDeriv ℝ j g x = iteratedFDeriv ℝ j (propagatorW C u s φ) x := by
        dsimp [g]
        rw [show (fun y => propagatorW C u s φ y - propagatorW C u s φ 0) =
            (propagatorW C u s φ) - fun _ => propagatorW C u s φ 0 by rfl,
          iteratedFDeriv_sub_apply
            (hSmooth.of_le (by exact_mod_cast (le_trans hj hr))).contDiffAt
            contDiff_const.contDiffAt,
          iteratedFDeriv_const_of_ne hj0, Pi.zero_apply, sub_zero]
      calc ‖iteratedFDeriv ℝ j g x‖
          = ‖iteratedFDeriv ℝ j (propagatorW C u s φ) x‖ := by rw [hsub]
        _ ≤ B := hJets j (by omega) (le_trans hj hr) x
        _ ≤ max (2 * A) B := le_max_right _ _
  have hCTest := fp81s21_weightedDrift_centered_test
    (m := m) (T := H) (t := s) (u := u) hP hA hGrad hprop hu hr
  have hPfull : (d : ℝ) < 2 * P := by linarith
  have hz := hb.hZ u huH
  have hη : IsBoundedLinearOnE r P (b u) := by
    refine ⟨?_, ?_⟩
    · intro f₁ f₂ hf₁ hf₁E hf₂ hf₂E c₀
      have ht₁ : IsR2WeightedTest r P f₁ := ⟨hf₁, hf₁E⟩
      have ht₂ : IsR2WeightedTest r P f₂ := ⟨hf₂, hf₂E⟩
      exact ⟨hz.add f₁ f₂ ht₁ ht₂, hz.smul c₀ f₁ ht₁⟩
    · exact ⟨Mb u, fun q hq hqE => hb.hM u huH q ⟨hq, hqE⟩⟩
  have hdual := HRS.MS.R2Interp.s102_dualNormE_le
    (d := d) (r := r) (Pw := P) (z := b u)
    (hb.Mb_nonneg u) (hb.hM u huH)
  have hdualTop : dualNormE r P (b u) < ⊤ :=
    lt_of_le_of_lt hdual ENNReal.ofReal_lt_top
  have hEtop : weightedSobolevE r P g < ⊤ := hCTest.1.2
  have hdualAction := HRS.MS.FixEq.s57p_dual_bound hPfull hη
    (hgSmooth.of_le (by exact_mod_cast hr))
    hDerivBound
  have hreal : |b u g| ≤
      (dualNormE r P (b u)).toReal * (weightedSobolevE r P g).toReal := by
    have hreal' := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hdualTop.ne hEtop.ne) hdualAction
    rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul] at hreal'
    exact hreal'
  have hAbs : |b u (propagatorW C u s φ)| = |b u g| := by
    calc |b u (propagatorW C u s φ)| =
          |b u (fun x => propagatorW C u s φ x - propagatorW C u s φ 0)| :=
            congrArg abs hshift
      _ = |b u g| := by simp [g]
  calc |b u (propagatorW C u s φ)| = |b u g| := hAbs
    _ ≤ (dualNormE r P (b u)).toReal *
        (weightedSobolevE r P g).toReal := hreal
    _ ≤ (dualNormE r P (b u)).toReal *
        (s57pC d r (P - 1) * B) :=
          mul_le_mul_of_nonneg_left hCTest.2 ENNReal.toReal_nonneg
    _ = (dualNormE r P (b u)).toReal *
        (s57pC d r (P - 1) * (A * Real.exp (-c * (s - u)))) := by dsimp [B]

/-- Weighted norm bound for the transported drift density.  The orbit envelope
is square summable, so the coordinatewise positive-derivative decay gives the
same exponential weight in the full oscillator dual norm. -/
theorem fp81s21_weightedDrift_density_norm_le
    {d k r : ℕ} {C : WholeCoeff d} {m H a s u A c P : ℝ}
    {coef : MultiIndex d → ℝ} {b : ℝ → (Euc d → ℝ) → ℝ} {Mb : ℝ → ℝ}
    (hd1 : 1 ≤ d) (hP : (d : ℝ) < 2 * (P - 1))
    (hA : 0 ≤ A) (hc : 0 < c)
    (hr : r ≤ k + 1)
    (hD : HRS.MS.CovMeas.S101Data C m H r coef) (hlin : S102Lin C m H)
    (hb : S102Drift C m H r P b Mb)
    (hOrbit : ∀ α : MultiIndex d,
      R2OrbitSup C k s (oscTestFun m α) (A * s103_b d α) ∧
      R2OrbitGrad C k s (oscTestFun m α) (A * s103_b d α) c)
    (hsol : ∀ α : MultiIndex d, ∃ f : ℝ → Euc d → ℝ,
      IsClassicalAdjointW C s (oscTestFun m α) f)
    (hu : u ∈ Icc (0 : ℝ) H) (hus : u ≤ s) (hsH : s ≤ H) (haS : a ≤ s)
    (hshift : ∀ φ : Euc d → ℝ,
      b u (propagatorW C u s φ) =
        b u (fun x => propagatorW C u s φ x - propagatorW C u s φ 0)) :
    ‖s102_w C m b u s‖ ≤
      (s57pC d r (P - 1) * A *
        Real.sqrt (∑' α : MultiIndex d, s103_b d α ^ 2)) *
        (Real.exp (-c * max (a - u) 0) * (dualNormE r P (b u)).toReal) := by
  have hPfull : (d : ℝ) < 2 * P := by linarith
  have hhsq := HRS.MS.ProClosureS111.stationary_weight_square_summable hd1
  have hgap : max (a - u) 0 ≤ s - u := max_le (by linarith) (by linarith [hus])
  have hdecay : Real.exp (-c * (s - u)) ≤ Real.exp (-c * max (a - u) 0) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hgap (by linarith)
  let w : ℝ := Real.exp (-c * max (a - u) 0)
  let M : ℝ := (dualNormE r P (b u)).toReal *
    (s57pC d r (P - 1) * (A * w))
  have hw : 0 ≤ w := (Real.exp_pos _).le
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg ENNReal.toReal_nonneg
      (mul_nonneg (s57pC_nonneg d r (P - 1)) (mul_nonneg hA hw))
  have hcoord : ∀ α : MultiIndex d,
      |OscDual.coord (s102_w C m b u s) α| ≤ M * s103_b d α := by
    intro α
    have hcoordEq := s102_Vprop_coord hPfull hD (hb.hZ u hu) hlin hu
      ⟨hus, hsH⟩ α
    obtain ⟨fα, hfα⟩ := hsol α
    obtain ⟨hsupα, hgradα⟩ := hOrbit α
    have hAmp : 0 ≤ A * s103_b d α := mul_nonneg hA (s103_b_nonneg α)
    have hact := fp81s21_weightedDrift_action_le
      (m := m) (H := H) (s := s) (u := u) (b := b) (Mb := Mb)
      hP hAmp hsupα hgradα hfα ⟨hu.1, hus⟩ hsH hr hb (hshift (oscTestFun m α))
    have hact' : |b u (propagatorW C u s (oscTestFun m α))| ≤
        (dualNormE r P (b u)).toReal *
          (s57pC d r (P - 1) *
            (A * s103_b d α * Real.exp (-c * (s - u)))) := by
      simpa [mul_assoc] using hact
    change |OscDual.coord (r2Vprop C m s u (b u)) α| ≤ M * s103_b d α
    rw [hcoordEq]
    calc |b u (propagatorW C u s (oscTestFun m α))|
        ≤ (dualNormE r P (b u)).toReal *
          (s57pC d r (P - 1) *
            (A * s103_b d α * Real.exp (-c * (s - u)))) := hact'
      _ ≤ (dualNormE r P (b u)).toReal *
          (s57pC d r (P - 1) * (A * s103_b d α * w)) := by
            have hC0 : 0 ≤ s57pC d r (P - 1) := s57pC_nonneg d r (P - 1)
            apply mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hdecay
                  (mul_nonneg hA (s103_b_nonneg α))) hC0)
              ENNReal.toReal_nonneg
      _ = M * s103_b d α := by
            dsimp [M, w]
            ring
  have hMsum : Summable (fun α : MultiIndex d => (M * s103_b d α) ^ 2) := by
    have h := hhsq.mul_left (M ^ 2)
    refine h.congr fun α => ?_
    ring
  have hcoordSum :
      ∑' α : MultiIndex d, (OscDual.coord (s102_w C m b u s) α) ^ 2 ≤
        ∑' α : MultiIndex d, (M * s103_b d α) ^ 2 :=
    Summable.tsum_le_tsum (fun α => by
      have h := hcoord α
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2)
      (OscDual.coord_sq_summable' _) hMsum
  have hsumEq :
      ∑' α : MultiIndex d, (M * s103_b d α) ^ 2 =
        M ^ 2 * (∑' α : MultiIndex d, s103_b d α ^ 2) := by
    simp_rw [mul_pow]
    rw [tsum_mul_left]
  rw [OscDual.norm_eq_coord]
  calc Real.sqrt (∑' α : MultiIndex d,
        (OscDual.coord (s102_w C m b u s) α) ^ 2)
      ≤ Real.sqrt (∑' α : MultiIndex d, (M * s103_b d α) ^ 2) :=
        Real.sqrt_le_sqrt hcoordSum
    _ = M * Real.sqrt (∑' α : MultiIndex d, s103_b d α ^ 2) := by
        rw [hsumEq, Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]
    _ = (s57pC d r (P - 1) * A *
          Real.sqrt (∑' α : MultiIndex d, s103_b d α ^ 2)) *
        (Real.exp (-c * max (a - u) 0) *
          (dualNormE r P (b u)).toReal) := by
        dsimp [M, w]
        ring

/-- The transported interval increment is controlled by the decaying integral
of the drift's actual weighted dual norm. -/
theorem fp81s21_weightedDrift_windowInc_norm_le
    {d k r : ℕ} {C : WholeCoeff d} {m H T a A c P : ℝ}
    {coef : MultiIndex d → ℝ} {b : ℝ → (Euc d → ℝ) → ℝ} {Mb : ℝ → ℝ}
    {q r' : ℝ}
    (hd1 : 1 ≤ d) (hP : (d : ℝ) < 2 * (P - 1))
    (hA : 0 ≤ A) (hc : 0 < c) (hr : r ≤ k + 1)
    (hD : HRS.MS.CovMeas.S101Data C m H r coef) (hlin : S102Lin C m H)
    (hb : S102Drift C m H r P b Mb)
    (hOrbit : ∀ s ∈ Icc (0 : ℝ) H, ∀ α : MultiIndex d,
      R2OrbitSup C k s (oscTestFun m α) (A * s103_b d α) ∧
      R2OrbitGrad C k s (oscTestFun m α) (A * s103_b d α) c)
    (hsol : ∀ s ∈ Icc (0 : ℝ) H, ∀ α : MultiIndex d,
      ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW C s (oscTestFun m α) f)
    (ha : 0 ≤ a) (hT : 0 ≤ T) (hwin : a + T ≤ H)
    (hq : 0 ≤ q) (hqr : q ≤ r') (hr'H : r' ≤ H)
    (hshift : ∀ v ∈ Icc (0 : ℝ) H, ∀ s ∈ Icc v H, ∀ φ : Euc d → ℝ,
      b v (propagatorW C v s φ) =
        b v (fun x => propagatorW C v s φ x - propagatorW C v s φ 0)) :
    ‖fp81s21_weightedDrift_windowInc (m := m) ha hwin C b q r'‖ ≤
      (s57pC d r (P - 1) * A *
        Real.sqrt (∑' α : MultiIndex d, s103_b d α ^ 2)) *
        (∫⁻ v in Ioc q r',
          ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) *
            dualNormE r P (b v)).toReal := by
  let K : ℝ := s57pC d r (P - 1) * A *
    Real.sqrt (∑' α : MultiIndex d, s103_b d α ^ 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (s57pC_nonneg d r (P - 1)) hA)
      (Real.sqrt_nonneg _)
  have hH0 : 0 ≤ H := by linarith
  have hPfull : (d : ℝ) < 2 * P := by linarith
  have hJtop : (∫⁻ v in Ioc q r',
      ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) * dualNormE r P (b v)) < ⊤ := by
    have hsub : Ioc q r' ⊆ Icc (0 : ℝ) H := fun v hv =>
      ⟨hq.trans hv.1.le, hv.2.trans hr'H⟩
    have hbd : ∀ v ∈ Ioc q r',
        ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) * dualNormE r P (b v) ≤
          ENNReal.ofReal (Mb v) := by
      intro v hv
      have hvH := hsub hv
      have hdual := s102_dualNormE_le (r := r) (Pw := P)
        (hb.Mb_nonneg v) (hb.hM v hvH)
      have hw : ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) ≤ 1 := by
        apply ENNReal.ofReal_le_one.2
        apply Real.exp_le_one_iff.mpr
        have hmax : 0 ≤ max (a - v) 0 := le_max_right _ _
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hmax
      calc ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) * dualNormE r P (b v)
          ≤ 1 * dualNormE r P (b v) := by gcongr
        _ = dualNormE r P (b v) := one_mul _
        _ ≤ ENNReal.ofReal (Mb v) := hdual
    have hmb' : (∫⁻ v in Icc (0 : ℝ) H, ENNReal.ofReal (Mb v)) < ⊤ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hb.Mb_int
        ((ae_restrict_mem measurableSet_Icc).mono fun v hv => hb.Mb_nonneg v)]
      exact ENNReal.ofReal_lt_top
    have hle : (∫⁻ v in Ioc q r',
        ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) * dualNormE r P (b v)) ≤
        ∫⁻ v in Icc (0 : ℝ) H, ENNReal.ofReal (Mb v) := by
      calc _ ≤ ∫⁻ v in Ioc q r', ENNReal.ofReal (Mb v) :=
            lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioc).mono fun v hv => hbd v hv)
        _ ≤ _ := lintegral_mono_set hsub
    exact lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top hmb'.ne hle)
  have hnorm : ‖fp81s21_weightedDrift_windowInc (m := m) ha hwin C b q r'‖ ≤
      K * (∫⁻ v in Ioc q r',
        ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) *
          dualNormE r P (b v)).toReal := by
    refine (ContinuousMap.norm_le _ (mul_nonneg hK (ENNReal.toReal_nonneg (a :=
      ∫⁻ v in Ioc q r', ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) *
        dualNormE r P (b v))))).2 ?_
    intro τ
    let s : ℝ := a + (τ : ℝ)
    have hs : s ∈ Icc (0 : ℝ) H := by
      refine ⟨?_, ?_⟩
      · dsimp [s]; exact add_nonneg ha τ.property.1
      · dsimp [s]; linarith [τ.property.2]
    have htime := HRS.MS.ProClosureS111.physicalWindowRestriction_apply
      ha hwin (r2DriftInc C m H b q r') τ
    have hpath := s102_driftInc_at hPfull hD hlin hb hH0 hq
      (le_trans hq hqr) (t := s) hs
    have htimeval : HRS.MS.ProClosureS111.physicalWindowTime ha hwin τ =
        (⟨s, hs⟩ : Icc (0 : ℝ) H) := by
      apply Subtype.ext
      rfl
    rw [s102_r2PathAt_of_mem _ hs] at hpath
    change ‖OscPath.at' (HRS.MS.ProClosureS111.physicalWindowRestriction ha hwin
      (r2DriftInc C m H b q r')) τ‖ ≤ _
    rw [htime, htimeval, hpath]
    change ‖s102_g C m b q r' s‖ ≤ _
    unfold s102_g
    have hS : Ioc q (min r' s) ⊆ Icc (0 : ℝ) H := fun v hv =>
      ⟨hq.trans hv.1.le, (hv.2.trans (min_le_right _ _)).trans hs.2⟩
    have hnormENN : ENNReal.ofReal ‖∫ v in Ioc q (min r' s),
        s102_w C m b v s‖ ≤ ENNReal.ofReal K *
          (∫⁻ v in Ioc q r',
            ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) *
              dualNormE r P (b v)) := by
      calc ENNReal.ofReal ‖∫ v in Ioc q (min r' s), s102_w C m b v s‖
          = ‖∫ v in Ioc q (min r' s), s102_w C m b v s‖ₑ :=
            ofReal_norm_eq_enorm _
        _ ≤ ∫⁻ v in Ioc q (min r' s), ‖s102_w C m b v s‖ₑ :=
          enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ v in Ioc q (min r' s),
          ENNReal.ofReal K *
            (ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) *
              dualNormE r P (b v)) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
          have hvH := hS hv
          have hdualtop : dualNormE r P (b v) < ⊤ := by
            exact lt_of_le_of_lt (s102_dualNormE_le (hb.Mb_nonneg v)
              (hb.hM v hvH)) ENNReal.ofReal_lt_top
          have hweight : 0 ≤ Real.exp (-c * max (a - v) 0) :=
            (Real.exp_pos _).le
          have hshiftv := hshift v hvH s ⟨hv.2.trans (min_le_right _ _), hs.2⟩
          have hvs : v ≤ s := hv.2.trans (min_le_right _ _)
          have has : a ≤ s := by dsimp [s]; linarith [τ.property.1]
          have hact := fp81s21_weightedDrift_density_norm_le
            (m := m) (H := H) (a := a) (s := s) (u := v) (A := A) (c := c)
            (P := P) (b := b) (Mb := Mb) hd1 hP hA hc hr hD hlin hb
            (hOrbit s hs) (hsol s hs) hvH hvs hs.2 has hshiftv
          have hact' : ‖s102_w C m b v s‖ ≤ K *
              (Real.exp (-c * max (a - v) 0) *
                (dualNormE r P (b v)).toReal) := by
            simpa [s102_w, r2Vprop, K, mul_assoc, mul_left_comm, mul_comm] using hact
          have hreal := ENNReal.ofReal_le_ofReal hact'
          have hmul : ENNReal.ofReal
              (K * (Real.exp (-c * max (a - v) 0) *
                (dualNormE r P (b v)).toReal)) =
              ENNReal.ofReal K *
                (ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) *
                  dualNormE r P (b v)) := by
            rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_mul hweight,
              ENNReal.ofReal_toReal hdualtop.ne]
          rw [← ofReal_norm_eq_enorm (s102_w C m b v s)]
          rw [hmul] at hreal
          exact hreal
        _ = ENNReal.ofReal K * (∫⁻ v in Ioc q (min r' s),
          ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) *
            dualNormE r P (b v)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal K * (∫⁻ v in Ioc q r',
          ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) *
            dualNormE r P (b v)) := by
          gcongr
          exact min_le_left _ _
    have hnormReal : ‖s102_g C m b q r' s‖ ≤
        K * (∫⁻ v in Ioc q r',
          ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) *
            dualNormE r P (b v)).toReal := by
      have hKtop : ENNReal.ofReal K ≠ ⊤ := ENNReal.ofReal_ne_top
      have htop := ENNReal.mul_ne_top hKtop hJtop.ne
      have hreal := ENNReal.toReal_mono htop hnormENN
      rw [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hK] at hreal
      exact hreal
    simpa [K, s102_g] using hnormReal
  simpa [K] using hnorm

/-- The cumulative moving drift has interval-local scalar variation bounded by
the decaying propagator weight times the actual dual norm of its source.  The
orbit amplitude `A` and decay rate `c` precede the horizon and window binders,
so the resulting constant is uniform in both. -/
theorem fp81s21_weightedDrift_variation_le
    {d k r : ℕ} {C : WholeCoeff d} {m A c P H T a : ℝ}
    {coef : MultiIndex d → ℝ} {b : ℝ → (Euc d → ℝ) → ℝ} {Mb : ℝ → ℝ}
    {q r' : ℝ}
    (hd1 : 1 ≤ d) (hP : (d : ℝ) < 2 * (P - 1))
    (hA : 0 ≤ A) (hc : 0 < c) (hr : r ≤ k + 1)
    (hD : HRS.MS.CovMeas.S101Data C m H r coef) (hlin : S102Lin C m H)
    (hb : S102Drift C m H r P b Mb)
    (hOrbit : ∀ s ∈ Icc (0 : ℝ) H, ∀ α : MultiIndex d,
      R2OrbitSup C k s (oscTestFun m α) (A * s103_b d α) ∧
      R2OrbitGrad C k s (oscTestFun m α) (A * s103_b d α) c)
    (hsol : ∀ s ∈ Icc (0 : ℝ) H, ∀ α : MultiIndex d,
      ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW C s (oscTestFun m α) f)
    (ha : 0 ≤ a) (hT : 0 ≤ T) (hwin : a + T ≤ H)
    (hq : 0 ≤ q) (hqr : q ≤ r') (hr'H : r' ≤ H)
    (hshift : ∀ v ∈ Icc (0 : ℝ) H, ∀ s ∈ Icc v H, ∀ φ : Euc d → ℝ,
      b v (propagatorW C v s φ) =
        b v (fun x => propagatorW C v s φ x - propagatorW C v s φ 0)) :
    eVariationOn (fp81s21_weightedDrift_windowCum (m := m) ha hwin C b)
      (Icc q r') ≤
        ENNReal.ofReal (s57pC d r (P - 1) * A *
          Real.sqrt (∑' α : MultiIndex d, s103_b d α ^ 2)) *
          (∫⁻ v in Ioc q r',
            ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) *
              dualNormE r P (b v)) := by
  let K : ℝ := s57pC d r (P - 1) * A *
    Real.sqrt (∑' α : MultiIndex d, s103_b d α ^ 2)
  let F : ℝ → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) * dualNormE r P (b v)
  let J : ℝ → ℝ≥0∞ := fun t => ∫⁻ v in Ioc q t, F v
  let Φ : ℝ → ℝ := fun t => K * (J t).toReal
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (s57pC_nonneg d r (P - 1)) hA)
      (Real.sqrt_nonneg _)
  have hH0 : 0 ≤ H := by linarith
  have hPfull : (d : ℝ) < 2 * P := by linarith
  have hJtop : J r' < ⊤ := by
    have hsub : Ioc q r' ⊆ Icc (0 : ℝ) H := fun v hv =>
      ⟨hq.trans hv.1.le, hv.2.trans hr'H⟩
    have hbd : ∀ v ∈ Ioc q r', F v ≤ ENNReal.ofReal (Mb v) := by
      intro v hv
      have hvH := hsub hv
      have hdual := s102_dualNormE_le (r := r) (Pw := P)
        (hb.Mb_nonneg v) (hb.hM v hvH)
      have hw : ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) ≤ 1 := by
        apply ENNReal.ofReal_le_one.2
        apply Real.exp_le_one_iff.mpr
        have hmax : 0 ≤ max (a - v) 0 := le_max_right _ _
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hmax
      dsimp [F]
      calc ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) * dualNormE r P (b v)
          ≤ 1 * dualNormE r P (b v) := by gcongr
        _ = dualNormE r P (b v) := one_mul _
        _ ≤ ENNReal.ofReal (Mb v) := hdual
    have hmb' : (∫⁻ v in Icc (0 : ℝ) H, ENNReal.ofReal (Mb v)) < ⊤ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hb.Mb_int
        ((ae_restrict_mem measurableSet_Icc).mono fun v hv => hb.Mb_nonneg v)]
      exact ENNReal.ofReal_lt_top
    have hle : J r' ≤ ∫⁻ v in Icc (0 : ℝ) H, ENNReal.ofReal (Mb v) := by
      dsimp [J]
      calc ∫⁻ v in Ioc q r', F v ≤ ∫⁻ v in Ioc q r', ENNReal.ofReal (Mb v) :=
            lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioc).mono fun v hv => hbd v hv)
        _ ≤ _ := lintegral_mono_set hsub
    exact lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top hmb'.ne hle)
  have hJfinite : ∀ t ∈ Icc q r', J t < ⊤ := by
    intro t ht
    have hle : J t ≤ J r' := by
      dsimp [J]
      exact lintegral_mono_set (Ioc_subset_Ioc_right ht.2)
    exact lt_of_le_of_lt hle hJtop
  have hJxyfinite : ∀ x y, x ∈ Icc q r' → y ∈ Icc q r' → x ≤ y →
      (∫⁻ v in Ioc x y, F v) < ⊤ := by
    intro x y hx hy hxy
    have hle : (∫⁻ v in Ioc x y, F v) ≤ J r' := by
      dsimp [J]
      apply lintegral_mono_set
      intro v hv
      exact ⟨lt_of_le_of_lt hx.1 hv.1, hv.2.trans hy.2⟩
    exact lt_of_le_of_lt hle hJtop
  have hJadd {x y : ℝ} (hx : x ∈ Icc q r') (hy : y ∈ Icc q r') (hxy : x ≤ y) :
      J y = J x + ∫⁻ v in Ioc x y, F v := by
    dsimp [J]
    rw [← lintegral_union measurableSet_Ioc
      (Set.disjoint_left.2 fun v hv hv' => (not_lt_of_ge hv.2) hv'.1),
      Set.Ioc_union_Ioc_eq_Ioc hx.1 hxy]
  have hΦmono : MonotoneOn Φ (Icc q r') := by
    intro x hx y hy hxy
    dsimp [Φ]
    apply mul_le_mul_of_nonneg_left _ hK
    exact ENNReal.toReal_mono (hJfinite y hy).ne
      (lintegral_mono_set (Ioc_subset_Ioc_right hxy))
  have hΦdiff {x y : ℝ} (hx : x ∈ Icc q r') (hy : y ∈ Icc q r') (hxy : x ≤ y) :
      Φ y - Φ x = K * (∫⁻ v in Ioc x y, F v).toReal := by
    have hsplit := hJadd hx hy hxy
    dsimp [Φ] at ⊢
    rw [hsplit, ENNReal.toReal_add (hJfinite x hx).ne (hJxyfinite x y hx hy hxy).ne]
    ring
  let Dcum : ℝ → OscPath d m T := fun v =>
    fp81s21_weightedDrift_windowCum ha hwin C b v
  have hDadd {x y : ℝ} (hx : x ∈ Icc q r') (hxy : x ≤ y) :
      Dcum y = Dcum x + fp81s21_weightedDrift_windowInc ha hwin C b x y := by
    have hadd := s102_driftInc_add hPfull hD hlin hb hH0
      (a := 0) (a' := x) (a'' := y) le_rfl (le_trans hq hx.1) hxy
    have hpath := congrArg (HRS.MS.ProClosureS111.physicalWindowRestriction ha hwin)
      hadd.symm
    simpa [Dcum, fp81s21_weightedDrift_windowCum,
      fp81s21_weightedDrift_windowInc] using hpath
  have hincbound {x y : ℝ} (hx : x ∈ Icc q r') (hy : y ∈ Icc q r') (hxy : x ≤ y) :
      ‖Dcum y - Dcum x‖ ≤ Φ y - Φ x := by
    have hpath := hDadd hx hxy
    have hsub : Dcum y - Dcum x =
        fp81s21_weightedDrift_windowInc ha hwin C b x y := by rw [hpath]; abel
    rw [hsub, hΦdiff hx hy hxy]
    exact fp81s21_weightedDrift_windowInc_norm_le
      (m := m) (A := A) (c := c) (P := P) (q := x) (r' := y)
      hd1 hP hA hc hr hD hlin hb hOrbit hsol ha hT hwin
      (le_trans hq hx.1) hxy (le_trans hy.2 hr'H) hshift
  unfold eVariationOn
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  have hstep : ∀ i, edist (Dcum (u (i + 1))) (Dcum (u i)) ≤
      ENNReal.ofReal (Φ (u (i + 1)) - Φ (u i)) := by
    intro i
    rw [edist_dist, dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal
      (hincbound (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
  calc ∑ i ∈ Finset.range n, edist (Dcum (u (i + 1))) (Dcum (u i))
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (Φ (u (i + 1)) - Φ (u i)) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, (Φ (u (i + 1)) - Φ (u i))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _
        exact sub_nonneg.2 (hΦmono (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (Φ (u n) - Φ (u 0)) := by
        rw [Finset.sum_range_sub (fun i => Φ (u i))]
    _ ≤ ENNReal.ofReal (Φ r' - Φ q) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hr'mem : r' ∈ Icc q r' := ⟨hqr, le_rfl⟩
        have hqmem : q ∈ Icc q r' := ⟨le_rfl, hqr⟩
        have h1 := hΦmono (hus n) hr'mem (hus n).2
        have h2 := hΦmono hqmem (hus 0) (hus 0).1
        linarith
    _ = ENNReal.ofReal K * J r' := by
        have hΦq : Φ q = 0 := by simp [Φ, J]
        rw [hΦq, sub_zero]
        dsimp [Φ]
        rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_toReal hJtop.ne]

/-- The moving centered quadratic field annihilates additive constants because
its commutator kernel depends only on the gradient of the test. -/
theorem fp81s21_moving_r2QuadField_sub_const
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (u : ℝ) (ζ : A.Ω) (f : Euc p.d → ℝ) :
    fp81s21_moving_r2QuadField R A u ζ (fun x => f x - f 0) =
      fp81s21_moving_r2QuadField R A u ζ f := by
  unfold fp81s21_moving_r2QuadField HRS.Whole.r2QuadField
  rw [HRS.MS.ProClosureS111.commutator_gradient_sub_const p.s (f 0) f]

/-- The interval-local weighted variation bound for the actual moving
quadratic drift.  The amplitude and decay rate are returned after `R`, before
all particle, time, and interval data.  The orbit claim is all-time; at the
remote-tail consumer's horizon `H = a + T`, the moving standard-data producer
supplies `S101Data` and classical adjoints. -/
theorem fp81s21_moving_weightedDrift_variation_le
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (horbit : ∃ Co co : ℝ, 0 < co ∧
      HRS.MS.R2WinOrbNL.S103nOrbitClaims
        p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co) :
    ∃ Co co : ℝ, 0 < co ∧
      ∀ {N : ℕ} (part : Particle R N) (ζ : part.Ω)
        {H T a : ℝ} (hH : 0 < H)
        {coef : MultiIndex p.d → ℝ} {Mb : ℝ → ℝ}
        (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
          (2 * p.d + 8) coef hH)
        (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H)
        (hb : S102Drift (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
          (2 * p.d + 8) ((p.d : ℝ) + 2)
          (fun u f => fp81s21_moving_r2QuadField R part u ζ f) Mb)
        {q r' : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (hwin : a + T ≤ H)
        (hq : 0 ≤ q) (hqr : q ≤ r') (hr'H : r' ≤ H),
        eVariationOn (fp81s21_weightedDrift_windowCum
          (m := wholeSpaceIndex p.d) ha hwin (r26t3_coeff R)
          (fun u f => fp81s21_moving_r2QuadField R part u ζ f)) (Icc q r') ≤
          ENNReal.ofReal (s57pC p.d (2 * p.d + 8) (((p.d : ℝ) + 2) - 1) *
            |Co| * Real.sqrt (∑' α : MultiIndex p.d, s103_b p.d α ^ 2)) *
            (∫⁻ v in Ioc q r',
              ENNReal.ofReal (Real.exp (-co * max (a - v) 0)) *
                dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
                  (fun f => fp81s21_moving_r2QuadField R part v ζ f)) := by
  obtain ⟨Co, co, hco, hclaims⟩ := horbit
  refine ⟨Co, co, hco, ?_⟩
  intro N part ζ H T a hH coef Mb hstd hlin hb q r' ha hT hwin hq hqr hr'H
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := wholeSpaceIndex p.d
  let P : ℝ := (p.d : ℝ) + 2
  let k : ℕ := 4 * p.d + 42
  let r : ℕ := 2 * p.d + 8
  let b : ℝ → (Euc p.d → ℝ) → ℝ :=
    fun u f => fp81s21_moving_r2QuadField R part u ζ f
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hP : (p.d : ℝ) < 2 * (P - 1) := by dsimp [P]; nlinarith
  have hr : r ≤ k + 1 := by dsimp [r, k]; omega
  have hOrbit : ∀ s ∈ Icc (0 : ℝ) H, ∀ α : MultiIndex p.d,
      R2OrbitSup C k s (oscTestFun m α) (|Co| * s103_b p.d α) ∧
      R2OrbitGrad C k s (oscTestFun m α) (|Co| * s103_b p.d α) co := by
    intro s hs α
    have hraw := hclaims R.ε R.ψ R.ρ R.admissible R.resulting α s hs.1
    have hAα : 0 ≤ s103_b p.d α := s103_b_nonneg α
    have hmono : Co * s103_b p.d α ≤ |Co| * s103_b p.d α :=
      mul_le_mul_of_nonneg_right (le_abs_self Co) hAα
    have hsup := HRS.MS.R2WinOrb.s103_orbitSup_mono hraw.1 hmono
    have hgrad := HRS.MS.R2WinOrb.s103_orbitGrad_mono hraw.2.1 hmono
    simpa [C, m, k, wholeSpaceIndex, HRS.MS.R26T3.r26t3_coeff] using And.intro hsup hgrad
  have hsol : ∀ s ∈ Icc (0 : ℝ) H, ∀ α : MultiIndex p.d,
      ∃ f : ℝ → Euc p.d → ℝ, IsClassicalAdjointW C s (oscTestFun m α) f := by
    intro s hs α
    obtain ⟨f, hf⟩ := hstd.hcls α s hs
    exact ⟨f, by simpa [C, m] using hf⟩
  have hshift : ∀ v ∈ Icc (0 : ℝ) H, ∀ s ∈ Icc v H, ∀ φ : Euc p.d → ℝ,
      b v (propagatorW C v s φ) =
        b v (fun x => propagatorW C v s φ x - propagatorW C v s φ 0) := by
    intro v hv s hs φ
    change fp81s21_moving_r2QuadField R part v ζ (propagatorW C v s φ) =
      fp81s21_moving_r2QuadField R part v ζ
        (fun x => propagatorW C v s φ x - propagatorW C v s φ 0)
    exact (fp81s21_moving_r2QuadField_sub_const p R part v ζ
      (propagatorW C v s φ)).symm
  simpa [C, m, P, k, r, b, s103_b] using
    (fp81s21_weightedDrift_variation_le
      (C := C) (m := m) (A := |Co|) (c := co) (P := P) (H := H) (T := T) (a := a)
      (coef := coef) (b := b) (Mb := Mb) (q := q) (r' := r')
      (k := k) (r := r) hd1 hP (abs_nonneg Co) hco hr hstd.hD hlin hb
      hOrbit hsol ha hT hwin hq hqr hr'H hshift)

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_weightedDrift_action_le
#print axioms HRS.Fp81.S21.fp81s21_weightedDrift_density_norm_le
#print axioms HRS.Fp81.S21.fp81s21_moving_r2QuadField_sub_const
#print axioms HRS.Fp81.S21.fp81s21_weightedDrift_windowInc_norm_le
#print axioms HRS.Fp81.S21.fp81s21_weightedDrift_variation_le
#print axioms HRS.Fp81.S21.fp81s21_moving_weightedDrift_variation_le
