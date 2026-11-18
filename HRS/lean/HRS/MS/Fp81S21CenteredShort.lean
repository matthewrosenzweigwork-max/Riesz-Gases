import HRS.MS.Fp81S21CenteredAdapter3

/-!
# S2.1(iii): identify the recent restrictions with the short windows

For each fixed window start, the long and short paths agree after restriction
on a full-measure continuity event.  The event excludes the zero fallback
branches of both window constructions.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3

/-- Restricting the long exactly centered particle window gives the short
window at the same physical times, almost surely. -/
theorem fp81s21_particle_short_window_identity
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (hN : 2 ≤ N) (A : Particle R N) (L a₀ : ℝ)
    (hL : 0 < L) (ha₀ : 0 ≤ a₀) :
    (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction
        (fp81s21_recent_geometry ha₀ hL p.hT).1
        (fp81s21_recent_geometry ha₀ hL p.hT).2
        (zetaPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) (L + p.T)
          (max (a₀ - L) 0) A.P A.X ω))
      =ᵐ[A.P] zetaPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) p.T a₀ A.P A.X := by
  let m : ℝ := ((wholeSpaceIndex p.d : ℕ) : ℝ)
  let H : ℝ := L + p.T
  let b : ℝ := max (a₀ - L) 0
  let u : ℝ := a₀ - b
  have hH : 0 < H := by dsimp [H]; linarith [p.hT, hL]
  have hb : 0 ≤ b := by dsimp [b]; exact le_max_right _ _
  have hgeo := fp81s21_recent_geometry ha₀ hL p.hT
  have hu : 0 ≤ u := by simpa [u, b] using hgeo.1
  have huH : u + p.T ≤ H := by simpa [u, b, H] using hgeo.2
  have hbu : b + u = a₀ := by dsimp [u]; ring
  have hshortEnd : a₀ + p.T ≤ b + H := by
    rw [← hbu]
    dsimp [H]
    linarith [huH]
  have hNpos : 0 < N := by omega
  have hd1 : 1 ≤ p.d := Nat.le_trans (by decide : 1 ≤ 2) p.hd
  have hm : (p.d : ℝ) < m := by
    dsimp [m, wholeSpaceIndex]
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    push_cast
    linarith
  have hstrong := A.strong (b + H)
  have hζcont := HRS.Whole.s21e_zeta_cont_time hd1 hNpos hm A.P A.X
    hstrong.adapted hstrong.cont
  let Y : ℝ → A.Ω → OscDual p.d m := fun t ω =>
    zetaB m (A.P.map (A.X (Real.toNNReal t))) (A.X (Real.toNNReal t) ω)
  filter_upwards [hζcont] with ω hω
  have hcLong : Continuous fun τ : Set.Icc (0 : ℝ) H => Y (b + (τ : ℝ)) ω :=
    hω.comp (continuous_const.add continuous_subtype_val)
  have hcShort : Continuous fun τ : Set.Icc (0 : ℝ) p.T => Y (a₀ + (τ : ℝ)) ω :=
    hω.comp (continuous_const.add continuous_subtype_val)
  have hlong : zetaPathW m H b A.P A.X ω =
      (⟨fun τ : Set.Icc (0 : ℝ) H => Y (b + (τ : ℝ)) ω, hcLong⟩ : OscPath p.d m H) := by
    change windowPathOf m H b (fun t => Y t ω) = _
    unfold windowPathOf
    exact dif_pos hcLong
  have hshort : zetaPathW m p.T a₀ A.P A.X ω =
      (⟨fun τ : Set.Icc (0 : ℝ) p.T => Y (a₀ + (τ : ℝ)) ω, hcShort⟩ : OscPath p.d m p.T) := by
    change windowPathOf m p.T a₀ (fun t => Y t ω) = _
    unfold windowPathOf
    exact dif_pos hcShort
  apply ContinuousMap.ext
  intro τ
  change OscPath.at'
      (HRS.MS.ProClosureS111.physicalWindowRestriction hu huH
        (zetaPathW m H b A.P A.X ω)) τ =
    OscPath.at' (zetaPathW m p.T a₀ A.P A.X ω) τ
  rw [HRS.MS.ProClosureS111.physicalWindowRestriction_apply, hlong, hshort]
  change Y (b + (u + (τ : ℝ))) ω = Y (a₀ + (τ : ℝ)) ω
  rw [← add_assoc, hbu]

/-- Restricting the long Gaussian evolution window gives the short window at
the same physical times, almost surely. -/
theorem fp81s21_gaussian_short_window_identity
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (G : GaussianRealization R) (L a₀ : ℝ)
    (hL : 0 < L) (ha₀ : 0 ≤ a₀) :
    (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction
        (fp81s21_recent_geometry ha₀ hL p.hT).1
        (fp81s21_recent_geometry ha₀ hL p.hT).2
        (processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) (L + p.T)
          (max (a₀ - L) 0) G.Z ω))
      =ᵐ[G.P] processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) p.T a₀ G.Z := by
  let m : ℝ := ((wholeSpaceIndex p.d : ℕ) : ℝ)
  let H : ℝ := L + p.T
  let b : ℝ := max (a₀ - L) 0
  let u : ℝ := a₀ - b
  let C := r26t3_coeff R
  let C₀ := HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
  have hH : 0 < H := by dsimp [H]; linarith [p.hT, hL]
  have hb : 0 ≤ b := by dsimp [b]; exact le_max_right _ _
  have hgeo := fp81s21_recent_geometry ha₀ hL p.hT
  have hu : 0 ≤ u := by simpa [u, b] using hgeo.1
  have huH : u + p.T ≤ H := by simpa [u, b, H] using hgeo.2
  have hbu : b + u = a₀ := by dsimp [u]; ring
  have hshortEnd : a₀ + p.T ≤ b + H := by
    rw [← hbu]
    dsimp [H]
    linarith [huH]
  have hHorizon : 0 ≤ b + H := by linarith [hb, hH.le]
  have hZ := G.evolution (b + H)
  obtain ⟨_, hLongEval⟩ := HRS.MS.S111BD.s111_shifted_window_aemeas
    p.d G.P C m p.β⁻¹ H b (b + H) C₀ G.Z hZ hH.le hb le_rfl
  obtain ⟨_, hShortEval⟩ := HRS.MS.S111BD.s111_shifted_window_aemeas
    p.d G.P C m p.β⁻¹ p.T a₀ (b + H) C₀ G.Z hZ p.hT.le ha₀ hshortEnd
  filter_upwards [hLongEval, hShortEval] with ω hLong hShort
  apply ContinuousMap.ext
  intro τ
  change OscPath.at'
      (HRS.MS.ProClosureS111.physicalWindowRestriction hu huH
        (processWindow m H b G.Z ω)) τ =
    OscPath.at' (processWindow m p.T a₀ G.Z ω) τ
  rw [HRS.MS.ProClosureS111.physicalWindowRestriction_apply,
    hLong (HRS.MS.ProClosureS111.physicalWindowTime hu huH τ), hShort τ]
  change G.Z (b + (u + (τ : ℝ))) ω = G.Z (a₀ + (τ : ℝ)) ω
  rw [← add_assoc, hbu]

#print axioms fp81s21_particle_short_window_identity
#print axioms fp81s21_gaussian_short_window_identity

end HRS.Fp81.S21

end
