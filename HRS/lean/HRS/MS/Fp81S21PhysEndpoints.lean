import HRS.MS.Fp81S21CenteredShort
import HRS.MS.Fp81S21ShiftedMildAssembly2
import HRS.MS.R2InterpAux75

/-! The physical terminal endpoint of the full-history prediction. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- At the final time the full prediction restricts to the actual centered
particle window. The sample event also excludes both path fallbacks. -/
theorem fp81s21_physical_terminal_endpoint
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (hN : 2 ≤ N) (A : Particle R N) (a : ℝ) (ha : 0 ≤ a) :
    (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
      (H := a + p.T) ha le_rfl
      (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d) (a + p.T)
        A.P A.X ω (a + p.T))) =ᵐ[A.P] r26t3_zetapath A a := by
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  let H : ℝ := a + p.T
  have hNpos : 0 < N := by omega
  have hd1 : 1 ≤ p.d := le_trans (by decide : 1 ≤ 2) p.hd
  have hm : (p.d : ℝ) < m := by
    dsimp [m, wholeSpaceIndex]
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    push_cast
    linarith
  have hstrong := A.strong H
  have hζcont := HRS.Whole.s21e_zeta_cont_time hd1 hNpos hm A.P A.X
    hstrong.adapted hstrong.cont
  let Y : ℝ → A.Ω → OscDual p.d m := fun t ω => fp81s21_particleZeta p R A t ω
  filter_upwards [hζcont] with ω hω
  have hcLong : Continuous fun τ : Icc (0 : ℝ) H => Y (0 + (τ : ℝ)) ω :=
    hω.comp (continuous_const.add continuous_subtype_val)
  have hcShort : Continuous fun τ : Icc (0 : ℝ) p.T => Y (a + (τ : ℝ)) ω :=
    hω.comp (continuous_const.add continuous_subtype_val)
  have hlong : zetaPathW m H 0 A.P A.X ω =
      (⟨fun τ : Icc (0 : ℝ) H => Y (0 + (τ : ℝ)) ω, hcLong⟩ : OscPath p.d m H) := by
    change windowPathOf m H 0 (fun t => Y t ω) = _
    unfold windowPathOf
    exact dif_pos hcLong
  have hshort : zetaPathW m p.T a A.P A.X ω =
      (⟨fun τ : Icc (0 : ℝ) p.T => Y (a + (τ : ℝ)) ω, hcShort⟩ : OscPath p.d m p.T) := by
    change windowPathOf m p.T a (fun t => Y t ω) = _
    unfold windowPathOf
    exact dif_pos hcShort
  change HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := m) (T := p.T) (H := H) ha le_rfl
      (s102_Y (r26t3_coeff R) m H A.P A.X ω H) = zetaPathW m p.T a A.P A.X ω
  rw [s102_hE1]
  apply ContinuousMap.ext
  intro τ
  change OscPath.at' (HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := m) (T := p.T) (H := H) ha le_rfl
      (zetaPathW m H 0 A.P A.X ω)) τ =
    OscPath.at' (zetaPathW m p.T a A.P A.X ω) τ
  rw [HRS.MS.ProClosureS111.physicalWindowRestriction_apply, hlong, hshort]
  change Y (0 + (a + (τ : ℝ))) ω = Y (a + (τ : ℝ)) ω
  simp only [zero_add]

/-- The terminal expectation is the expectation of the centered particle window. -/
theorem fp81s21_physical_terminal_expectation
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (hN : 2 ≤ N) (A : Particle R N) (a : ℝ) (ha : 0 ≤ a)
    (Φ : Window p → ℝ) :
    (∫ ω, Φ (HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
      (H := a + p.T) ha le_rfl
      (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d) (a + p.T)
        A.P A.X ω (a + p.T))) ∂A.P) =
      ∫ ω, Φ (r26t3_zetapath A a ω) ∂A.P := by
  apply integral_congr_ae
  filter_upwards [fp81s21_physical_terminal_endpoint p R hN A a ha] with ω hω
  rw [hω]

#print axioms HRS.Fp81.S21.fp81s21_physical_terminal_endpoint
#print axioms HRS.Fp81.S21.fp81s21_physical_terminal_expectation
end HRS.Fp81.S21
end
