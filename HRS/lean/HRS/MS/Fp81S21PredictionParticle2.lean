import HRS.MS.Fp81S21PredictionParticle

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas

local instance fp81s21_particle2_CH_measSpace (H : ℝ) :
    MeasurableSpace (CH H) := borel _
local instance fp81s21_particle2_CH_borelSpace (H : ℝ) :
    BorelSpace (CH H) := ⟨rfl⟩
local instance fp81s21_particle2_YH_measSpace (p : Parameters) (H : ℝ) :
    MeasurableSpace (YH p H) := borel _
local instance fp81s21_particle2_YH_borelSpace (p : Parameters) (H : ℝ) :
    BorelSpace (YH p H) := ⟨rfl⟩

/-- The physical prediction of the exactly centered particle field is the
clipped restriction of the standard particle prediction. -/
theorem fp81s21_particle_prediction_id
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (E : r26t6_WeightedChart p.d (r p) (Pw p))
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a)
    (c : MultiIndex p.d → ℝ)
    (hD : S101Data (r26t3_coeff R) (m p)
      (max (a - L) 0 + (L + p.T)) (r p) c)
    (P : CH (L + p.T) →L[ℝ] YH p (L + p.T))
    (hP : PSpec p R E L a P) (X : A.Ω → CH (L + p.T))
    (hX : CD E A.P (fp81s21_particleEmpField R N A)
      (max (a - L) 0) (L + p.T) X)
    (hmom : ∀ u ∈ I (max (a - L) 0 + (L + p.T)),
      Integrable (fun x : Euc p.d => jbracket x ^ (Pw p))
        (HRS.Whole.meanEmpirical (A.P.map (A.X u.toNNReal)))) :
    NId p R A L a (fun ω => P (cen A.P X ω)) := by
  let H : ℝ := L + p.T
  let b : ℝ := max (a - L) 0
  let θ : ℝ := a - b
  let T0 : ℝ := b + H
  have hg := recent_geometry L a hL ha
  have hb : 0 ≤ b := hg.1
  have hθ : 0 ≤ θ := hg.2.1
  have hθL : θ ≤ L := hg.2.2.1
  have hsum : b + θ = a := hg.2.2.2
  have hH : 0 < H := by dsimp [H]; linarith [p.hT]
  have hT : 0 < T0 := by dsimp [T0]; linarith
  have hd : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hN0 : 0 < N := by omega
  have hPw : 0 ≤ Pw p := by dsimp [Pw]; positivity
  have hr : (p.d : ℝ) / 2 < (r p : ℝ) := by
    dsimp [r]
    push_cast
    nlinarith [show (0 : ℝ) ≤ p.d by positivity]
  have hdim : (p.d : ℝ) < 2 * Pw p := by
    dsimp [Pw]
    nlinarith [show (0 : ℝ) ≤ p.d by positivity]
  have hm : (p.d : ℝ) < m p := by
    dsimp [m, wholeSpaceIndex]
    push_cast
    nlinarith [p.hd]
  have hlin : S102Lin (r26t3_coeff R) (m p) T0 :=
    fp81s21_S102Lin p R T0
  have hXm : ∀ t, Measurable (A.X t) := (A.strong T0).adapted
  have hcz := s102_zeta_cont hm hN0 A.P A.X hXm (A.strong T0).cont
  have hZ : ∀ ω : A.Ω, ∀ u ∈ I T0, S102Z (r p) (Pw p) (s102_zf A.P A.X ω u) :=
    fun ω u hu => s102_Z_zf hd hPw hr hN0 A.P A.X u (hmom u hu) ω
  have hterm : ∀ t ∈ I T0, ∀ α : MultiIndex p.d,
      propagatorW (r26t3_coeff R) t t (oscTestFun (m p) α) = oscTestFun (m p) α := by
    intro t ht α
    exact (s102_propagator_classical
      (fp81s21_adjoint_of_hermite_combo p R (s102_isDualCombo α) ht.1)).terminal
  filter_upwards [fp81s21_particle_centered_zf p R hN A E b H hb X hX, hcz] with ω hω hc
  let w : OscPath p.d (m p) T0 := zetaPathW (m p) T0 0 A.P A.X ω
  have hwat : ∀ t ∈ I T0, r2PathAt w t =
      zetaB (m p) (A.P.map (A.X t.toNNReal)) (A.X t.toNNReal ω) := by
    intro t ht
    exact s102_windowPathOf_at hc.continuousOn ht
  have hmatch : ∀ t ∈ I T0,
      r2Vprop (r26t3_coeff R) (m p) t t (s102_zf A.P A.X ω t) = r2PathAt w t := by
    intro t ht
    apply s102_ext
    intro α
    rw [s102_Vprop_coord hdim hD (hZ ω t ht) hlin ht ⟨le_rfl, ht.2⟩ α,
      hterm t ht α, hwat t ht, s102_coord_zetaB hm hN0 A.P A.X hXm t ω α]
  change ∀ v : I H, ∀ τ : I p.T, _
  intro v τ
  let s : ℝ := min (v : ℝ) (θ + (τ : ℝ))
  let u : ℝ := b + min (v : ℝ) (θ + p.T)
  let t : ℝ := a + (τ : ℝ)
  have hs : s ∈ I H := by
    constructor
    · exact le_min v.2.1 (by linarith [τ.2.1])
    · exact (min_le_left _ _).trans v.2.2
  have hu : u ∈ I T0 := by
    dsimp [u, T0]
    constructor
    · have hm0 : 0 ≤ min (v : ℝ) (θ + p.T) :=
        le_min v.2.1 (by linarith [p.hT])
      linarith
    · have := min_le_left (v : ℝ) (θ + p.T)
      linarith [v.2.2]
  have ht : t ∈ I T0 := by
    dsimp [t, T0, H]
    constructor <;> linarith [τ.2.1, τ.2.2]
  have hbs : b + s ∈ I T0 := by
    dsimp [T0]
    constructor <;> linarith [hs.1, hs.2]
  have hst : b + s ≤ t := by
    have := min_le_right (v : ℝ) (θ + (τ : ℝ))
    dsimp [s, t] at *
    linarith
  have hphys : r2Vprop (r26t3_coeff R) (m p) t (b + s)
      (fp81s21_chartAction E (cen A.P X ω ⟨s, hs⟩)) =
      r2Vprop (r26t3_coeff R) (m p) t (b + s) (s102_zf A.P A.X ω (b + s)) := by
    exact fp81s21_chartVprop_physical hdim hD hlin E _ _ (hZ ω _ hbs)
      (hω ⟨s, hs⟩) hbs ⟨hst, ht.2⟩
  have hspec := hP (cen A.P X ω) v τ hs
  have hpred := s102_predicted_at hdim hD hlin w (s102_zf A.P A.X ω)
    hu (hZ ω u hu) (hmatch u hu) ht
  change OscPath.at' (P (cen A.P X ω) v) τ =
    r2PathAt (r2Predicted (r26t3_coeff R) w (s102_zf A.P A.X ω) u) t
  rw [hspec, hphys, hpred]
  by_cases htu : t ≤ u
  · have hts : b + s = t := by
      have hle : θ + (τ : ℝ) ≤ (v : ℝ) := by
        have hmin := min_le_left (v : ℝ) (θ + p.T)
        dsimp [t, u] at htu
        linarith
      dsimp [s, t]
      rw [min_eq_right hle]
      linarith
    rw [if_pos htu, hts]
    exact hmatch t ht
  · have hv : (v : ℝ) ≤ θ + (τ : ℝ) := by
      by_contra hn
      have hm' : θ + (τ : ℝ) ≤ min (v : ℝ) (θ + p.T) :=
        le_min (le_of_lt (not_le.mp hn)) (by linarith [τ.2.2])
      dsimp [t, u] at htu
      exact htu (by linarith)
    have hv' : (v : ℝ) ≤ θ + p.T := by linarith [τ.2.2]
    have hsu : b + s = u := by simp [s, u, min_eq_left hv, min_eq_left hv']
    rw [if_neg htu, hsu]

#print axioms HRS.Fp81.S21.fp81s21_particle_prediction_id

end HRS.Fp81.S21
