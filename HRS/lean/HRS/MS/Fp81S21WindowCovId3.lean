import HRS.MS.Fp81S21WindowCovId2
import HRS.MS.Fp81S21CovClose3
import HRS.MS.Fp81S21MovingHeat5

/-! Simultaneous identification against the specified interval map. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MC.E213O

/-- Each full-horizon increment equals the specified window interval value
under restriction. The original interval contract, including its local
variation bound and projective symmetry, is retained. -/
theorem fp81s21_window_covariance_interval_identification
    {d : ℕ} {C : WholeCoeff d} {m T a : ℝ} {r : ℕ} {P : ℝ}
    {z z' : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec c : ℝ}
    (hT : 0 < T) (ha : 0 ≤ a)
    (D : fp81s21_WindowLocalInput C m T a r P z Cmix cdec)
    (D' : fp81s21_WindowLocalInput C m T a r P z' Cmix cdec)
    (Dsum : fp81s21_WindowLocalInput C m T a r P (z + z') Cmix cdec)
    (Dsmul : fp81s21_WindowLocalInput C m T a r P (c • z) Cmix cdec)
    (K : ℝ) (Fj : ℝ → projTensor (OscPath d m (a + T)) 2)
    (hfull : ∀ q s, 0 ≤ q → q ≤ s → s ≤ a + T →
      IsR2JValue C m (a + T) z (Ioc q s)
        (((Fj s - Fj q : projTensor (OscPath d m (a + T)) 2) :
          TensorDual (OscPath d m (a + T)) 2)))
    (hwindow : ∀ q s, 0 ≤ q → q ≤ s → s ≤ a + T →
      fp81s21_covariance_interval_contract D D' Dsum Dsmul K q s) :
    ∀ q s, 0 ≤ q → q ≤ s → s ≤ a + T →
      tensorPow' 2 (HRS.MS.ProClosureS111.physicalWindowRestriction
        (d := d) (m := m) (T := T) (H := a + T) ha le_rfl)
        (((Fj s - Fj q : projTensor (OscPath d m (a + T)) 2) :
          TensorDual (OscPath d m (a + T)) 2)) =
          ((fp81s21_window_covariance_measure D q s : projTensor (OscPath d m T) 2) :
            TensorDual (OscPath d m T) 2) ∧
      fp81s21_covariance_interval_contract D D' Dsum Dsmul K q s := by
  intro q s hq hqs hs
  have hw := hwindow q s hq hqs hs
  refine ⟨?_, hw⟩
  apply fp81s21_restrict_eq_windowJValue C hT ha z (Ioc q s)
    (hfull q s hq hqs hs)
  exact hw.2.2.2.2.2.2.2.1


/-- The second heat derivative pairs with the transported covariance exactly
as the full-history derivative pairs with the original tensor. -/
theorem fp81s21_window_covariance_heat_pairing
    (p : Parameters) (a : ℝ) (ha : 0 ≤ a)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : ∀ H v, IsProbabilityMeasure (future H v))
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ) (τ : ℝ)
    (y : OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (J : TensorDual (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2) :
    let W := HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := a + p.T) ha le_rfl
    tensorPow' 2 W J (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ τ) (W y)) =
      J (iteratedFDeriv ℝ 2 (r2HeatFn (future (a + p.T))
        (fun w => Φ (W w)) τ) y) := by
  dsimp only
  rw [tensorPow'_apply]
  rw [fp81s21_initialHeat_pullback_iteratedFDeriv future hfuture a ha Φ hΦ τ 2
    (by norm_num) y]

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_window_covariance_interval_identification
#print axioms HRS.Fp81.S21.fp81s21_window_covariance_heat_pairing
