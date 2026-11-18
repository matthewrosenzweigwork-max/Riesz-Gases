import HRS.MS.R2InterpAux91
import HRS.MS.R2InterpAux54

/-!
# S10.2 (worker S10R), part 92 (packet M3d): the observations of the predicted path along the particle system
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

theorem s102_Z_zf (hd : 1 ≤ d) (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 < r) {N : ℕ} (hN : 0 < N) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) (u : ℝ)
    (hmom : Integrable (fun x : Euc d => jbracket x ^ Pw) (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))))
    (ζ : Ω) : S102Z r Pw (s102_zf P X ζ u) :=
  s102_Z_fluct hd hP0 r hr hN (X u.toNNReal ζ) _ hmom (Real.sqrt N)

theorem s102_obs_Y (hs : S102Std C m T r c) (hP : (d : ℝ) < 2 * Pw) (hlin : S102Lin C m T) (hT : 0 < T)
    (hd : 1 ≤ d) (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 < r) (hm : (d : ℝ) < m) {N : ℕ} (hN : 0 < N) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → EucConfig d N)
    (hXm : ∀ t, Measurable (X t))
    (hmom : ∀ u ∈ Icc (0 : ℝ) T, Integrable (fun x : Euc d => jbracket x ^ Pw)
      (HRS.Whole.meanEmpirical (P.map (X u.toNNReal)))) (L : ℕ) (ζ : Ω)
    (hcz : Continuous fun u : ℝ => zetaB m (P.map (X u.toNNReal)) (X u.toNNReal ζ)) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) T) (i : Fin (s102_q d L)) :
    s102_obs (s102_tauk hT L) (s102_alk L) (s102_Y C m T P X ζ u) i =
      s102_zf P X ζ (min u (s102_tk hT L i))
        (propagatorW C (min u (s102_tk hT L i)) (s102_tk hT L i) (oscTestFun m (s102_alk L i))) := by
  classical
  have hti : s102_tk hT L i ∈ Icc (0 : ℝ) T := (s102_tauk hT L i).2
  set w : OscPath d m T := zetaPathW m T 0 P X ζ with hw
  have hwat : ∀ t ∈ Icc (0 : ℝ) T, r2PathAt w t = zetaB m (P.map (X t.toNNReal)) (X t.toNNReal ζ) := by
    intro t ht
    exact s102_windowPathOf_at (f := fun t : ℝ => zetaB m (P.map (X t.toNNReal)) (X t.toNNReal ζ))
      hcz.continuousOn ht
  have hzu := s102_Z_zf hd hP0 hr hN P X u (hmom u hu) ζ
  have hterm : ∀ t ∈ Icc (0 : ℝ) T, ∀ α : MultiIndex d, propagatorW C t t (oscTestFun m α) = oscTestFun m α :=
    fun t ht α => (s102_propagator_classical (hs.hcls α t ht)).terminal
  have hmatch : r2Vprop C m u u (s102_zf P X ζ u) = r2PathAt w u := by
    apply s102_ext
    intro α
    rw [s102_Vprop_coord hP hs.hD hzu hlin hu ⟨le_rfl, hu.2⟩ α, hterm u hu α, hwat u hu,
      s102_coord_zetaB hm hN P X hXm u ζ α]
  have hpred := s102_predicted_at hP hs.hD hlin w (s102_zf P X ζ) hu hzu hmatch hti
  show OscDual.coord (OscPath.at' (r2Predicted C w (s102_zf P X ζ) u) (s102_tauk hT L i)) (s102_alk L i) = _
  have hat : OscPath.at' (r2Predicted C w (s102_zf P X ζ) u) (s102_tauk hT L i) =
      r2PathAt (r2Predicted C w (s102_zf P X ζ) u) (s102_tk hT L i) :=
    (s102_r2PathAt_of_mem _ hti).symm
  rw [hat, hpred]
  by_cases hle : s102_tk hT L i ≤ u
  · rw [if_pos hle, min_eq_right hle, hwat _ hti, s102_coord_zetaB hm hN P X hXm _ ζ, hterm _ hti]
  · rw [if_neg hle, min_eq_left (not_le.1 hle).le,
      s102_Vprop_coord hP hs.hD hzu hlin hu ⟨(not_le.1 hle).le, hti.2⟩ (s102_alk L i)]

end HRS.MS.R2Interp

end
