import HRS.MS.Fp81S21PredictionParticle2
import HRS.MS.Fp81S21RemotePhysical

/-! Particle prediction compatibility between the recent and full horizons.
No new prediction, future, or RS record is selected. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas
open HRS.MS.ProClosureS111

private theorem fp81s21_recentRS_particle_formula
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (T : ℝ)
    (c : MultiIndex p.d → ℝ) (hD : S101Data (r26t3_coeff R) (m p) T (r p) c)
    (hmom : ∀ u ∈ I T, Integrable (fun x : Euc p.d => jbracket x ^ (Pw p))
      (HRS.Whole.meanEmpirical (A.P.map (A.X u.toNNReal)))) :
    ∀ᵐ ω ∂A.P, ∀ u ∈ I T, ∀ t ∈ I T,
      r2PathAt (s102_Y (r26t3_coeff R) (m p) T A.P A.X ω u) t =
        if t ≤ u then zetaB (m p) (A.P.map (A.X t.toNNReal)) (A.X t.toNNReal ω)
        else r2Vprop (r26t3_coeff R) (m p) t u (s102_zf A.P A.X ω u) := by
  have hN0 : 0 < N := by omega
  have hd : 1 ≤ p.d := by have := p.hd; omega
  have hPw : 0 ≤ Pw p := by dsimp [Pw]; positivity
  have hr : (p.d : ℝ) / 2 < (r p : ℝ) := by
    dsimp [r]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) p.d]
  have hdim : (p.d : ℝ) < 2 * Pw p := by
    dsimp [Pw]; nlinarith [Nat.cast_nonneg (α := ℝ) p.d]
  have hm : (p.d : ℝ) < m p := by
    dsimp [m, wholeSpaceIndex]; push_cast; nlinarith [p.hd]
  have hlin := fp81s21_S102Lin p R T
  have hXm : ∀ t, Measurable (A.X t) := (A.strong T).adapted
  filter_upwards [s102_zeta_cont hm hN0 A.P A.X hXm (A.strong T).cont] with ω hc
  let w : OscPath p.d (m p) T := zetaPathW (m p) T 0 A.P A.X ω
  have hwat : ∀ t ∈ I T, r2PathAt w t =
      zetaB (m p) (A.P.map (A.X t.toNNReal)) (A.X t.toNNReal ω) := by
    intro t ht
    exact s102_windowPathOf_at hc.continuousOn ht
  intro u hu t ht
  have hz := s102_Z_zf hd hPw hr hN0 A.P A.X u (hmom u hu) ω
  have hmatch : r2Vprop (r26t3_coeff R) (m p) u u (s102_zf A.P A.X ω u) =
      r2PathAt w u := by
    apply s102_ext
    intro α
    have hterm := (s102_propagator_classical
      (fp81s21_adjoint_of_hermite_combo p R (s102_isDualCombo α) hu.1)).terminal
    rw [s102_Vprop_coord hdim hD hz hlin hu ⟨le_rfl, hu.2⟩ α, hterm,
      hwat u hu, s102_coord_zetaB hm hN0 A.P A.X hXm u ω α]
  change r2PathAt (r2Predicted (r26t3_coeff R) w (s102_zf A.P A.X ω) u) t = _
  rw [s102_predicted_at hdim hD hlin w _ hu hz hmatch ht, hwat t ht]

/-- The packet-33 particle prediction agrees simultaneously, on the actual
recent interval, with the supplied packet-20 prediction restricted to the
observation window. The two orbit-data inputs are the two actual horizons;
weighted moments are needed only through the longer horizon. -/
theorem fp81s21_recentRS_particle_prediction_restrict
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ} (hN : 2 ≤ N)
    (A : Particle R N) (F : FilteredParticle A) (L : ℝ) (hL : 0 < L)
    (a : ℝ) (ha : 0 ≤ a) (D : fp81s21_finproj_shared_data p R a A F)
    (c : MultiIndex p.d → ℝ)
    (hDs : S101Data (r26t3_coeff R) (m p) (a + p.T) (r p) c)
    (hDl : S101Data (r26t3_coeff R) (m p)
      (max (a - L) 0 + (L + p.T)) (r p) c)
    (hmom : ∀ u ∈ I (max (a - L) 0 + (L + p.T)),
      Integrable (fun x : Euc p.d => jbracket x ^ (Pw p))
        (HRS.Whole.meanEmpirical (A.P.map (A.X u.toNNReal))))
    (Y : A.Ω → YH p (L + p.T)) (hY : NId p R A L a Y) :
    ∀ᵐ ω ∂A.P, ∀ v : I (L + p.T), (v : ℝ) ≤ a - max (a - L) 0 + p.T →
      Y ω v = physicalWindowRestriction (d := p.d) (m := m p)
        (T := p.T) (H := a + p.T) ha le_rfl
        (D.Yh ω (max (a - L) 0 + (v : ℝ))) := by
  let b := max (a - L) 0
  have hg := recent_geometry L a hL ha
  have hb : 0 ≤ b := hg.1
  have hlong : a + p.T ≤ b + (L + p.T) := by
    dsimp [b]; linarith [hg.2.2.1]
  have hshort : ∀ u ∈ I (a + p.T), u ∈ I (b + (L + p.T)) :=
    fun u hu => ⟨hu.1, hu.2.trans hlong⟩
  have hs := fp81s21_recentRS_particle_formula p R hN A (a + p.T) c hDs
    (fun u hu => hmom u (hshort u hu))
  have hl := fp81s21_recentRS_particle_formula p R hN A (b + (L + p.T)) c hDl hmom
  filter_upwards [hY, D.Yh_ae, hs, hl] with ω hy hd hsω hlω
  intro v hv
  have hu : b + (v : ℝ) ∈ I (a + p.T) :=
    ⟨add_nonneg hb v.property.1, by dsimp [b] at *; linarith⟩
  apply ContinuousMap.ext
  intro τ
  have ht : a + (τ : ℝ) ∈ I (a + p.T) :=
    ⟨add_nonneg ha τ.property.1, by linarith [τ.property.2]⟩
  have hy' := hy v τ
  change OscPath.at' (Y ω v) τ = OscPath.at'
    (physicalWindowRestriction (d := p.d) (m := m p) (T := p.T)
      (H := a + p.T) ha le_rfl (D.Yh ω (b + (v : ℝ)))) τ
  rw [physicalWindowRestriction_apply, hd _ hu]
  change OscPath.at' (Y ω v) τ =
    OscPath.at' (s102_Y (r26t3_coeff R) (m p) (a + p.T) A.P A.X ω
      (b + (v : ℝ))) ⟨a + (τ : ℝ), ht⟩
  rw [← s102_r2PathAt_of_mem _ ht]
  change OscPath.at' (Y ω v) τ =
    r2PathAt (s102_Y (r26t3_coeff R) (m p) (b + (L + p.T)) A.P A.X ω
      (b + min (v : ℝ) (a - b + p.T))) (a + (τ : ℝ)) at hy'
  rw [min_eq_left hv] at hy'
  rw [hy', hlω _ (hshort _ hu) _ (hshort _ ht), hsω _ hu _ ht]

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_recentRS_particle_prediction_restrict
end
