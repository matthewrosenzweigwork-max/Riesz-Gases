import HRS.MS.Fp81S21MovingItoRep4

/-!
# HRS S2.1(iii), packet 8.5: moving initial observations

These helpers use only the moving S101 data, moving classical adjoints, the
linear propagator premise supplied by interpolation consumers, and the P00
full-time indistinguishability event. They do not construct stationary S102
data.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp
open HRS.MS.CovMeas

private theorem fp81s21_moving_filtered_moment
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    (hphys : Fp81MovingPhysicalInputs R hN A H) :
    ∀ u ∈ Icc (0 : ℝ) H,
      Integrable (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 2))
        (HRS.Whole.meanEmpirical (A.P.map (F.X u.toNNReal))) := by
  obtain ⟨C₀, hC₀⟩ := hphys.particle_moment
  intro u hu
  have hmap : A.P.map (F.X u.toNNReal) = A.P.map (A.X u.toNNReal) :=
    Measure.map_congr (F.indist.mono fun ω hω => hω u.toNNReal)
  rw [hmap]
  exact (hC₀ u hu).1

private theorem fp81s21_moving_obs_y0_coord
    {d : ℕ} {C : WholeCoeff d} {m H : ℝ} {r : ℕ}
    {c : MultiIndex d → ℝ} {Pw : ℝ}
    (hD : S101Data C m H r c) (hP : (d : ℝ) < 2 * Pw)
    (hlin : S102Lin C m H) (hH : 0 < H) (hd : 1 ≤ d)
    (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 < r)
    {N : ℕ} (hN : 0 < N) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N)
    (hmom : Integrable (fun x : Euc d => jbracket x ^ Pw)
      (HRS.Whole.meanEmpirical (P.map (X 0))))
    (L : ℕ) (ζ : Ω) (i : Fin (s102_q d L)) :
    s102_obs (s102_tauk hH L) (s102_alk L)
      (s102_y0 C m H P X ζ) i =
        s102_zf P X ζ 0 (s102_orb C m hH L i 0) := by
  have hz : S102Z r Pw (s102_zf P X ζ 0) :=
    s102_Z_zf hd hP0 hr hN P X 0 (by simpa using hmom) ζ
  have hy : s102_y0 C m H P X ζ = r2InitProp C m H (s102_zf P X ζ 0) := by
    unfold s102_y0 s102_zf
    simp only [Real.toNNReal_zero]
  rw [hy, s102_obs_apply, ← s102_r2PathAt_of_mem _ (s102_tauk hH L i).2,
    s102_initProp_at hP hD hlin hz hH.le (s102_tauk hH L i).2]
  simpa [s102_orb, s102_tk] using
    s102_Vprop_coord hP hD hz hlin ⟨le_rfl, hH.le⟩
      ⟨(s102_tauk hH L i).2.1, (s102_tauk hH L i).2.2⟩ _

private theorem fp81s21_moving_obs_Y_coord
    {d : ℕ} {C : WholeCoeff d} {m H : ℝ} {r : ℕ}
    {c : MultiIndex d → ℝ} {Pw : ℝ}
    (hD : S101Data C m H r c)
    (hcls : ∀ (α : MultiIndex d) (t : ℝ), t ∈ Icc (0 : ℝ) H →
      ∃ f, IsClassicalAdjointW C t (oscTestFun m α) f)
    (hP : (d : ℝ) < 2 * Pw) (hlin : S102Lin C m H) (hH : 0 < H)
    (hd : 1 ≤ d) (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 < r)
    (hm : (d : ℝ) < m) {N : ℕ} (hN : 0 < N) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N)
    (hXm : ∀ t, Measurable (X t))
    (hmom : ∀ u ∈ Icc (0 : ℝ) H,
      Integrable (fun x : Euc d => jbracket x ^ Pw)
        (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))))
    (L : ℕ) (ζ : Ω)
    (hcz : Continuous fun u : ℝ =>
      zetaB m (P.map (X u.toNNReal)) (X u.toNNReal ζ))
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) H) (i : Fin (s102_q d L)) :
    s102_obs (s102_tauk hH L) (s102_alk L) (s102_Y C m H P X ζ u) i =
      s102_zf P X ζ (min u (s102_tk hH L i))
        (propagatorW C (min u (s102_tk hH L i))
          (s102_tk hH L i) (oscTestFun m (s102_alk L i))) := by
  classical
  have hti : s102_tk hH L i ∈ Icc (0 : ℝ) H := (s102_tauk hH L i).2
  set w : OscPath d m H := zetaPathW m H 0 P X ζ
  have hwat : ∀ t ∈ Icc (0 : ℝ) H,
      r2PathAt w t = zetaB m (P.map (X t.toNNReal)) (X t.toNNReal ζ) := by
    intro t ht
    exact s102_windowPathOf_at (f := fun t : ℝ =>
      zetaB m (P.map (X t.toNNReal)) (X t.toNNReal ζ)) hcz.continuousOn ht
  have hzu := s102_Z_zf hd hP0 hr hN P X u (hmom u hu) ζ
  have hterm : ∀ t ∈ Icc (0 : ℝ) H, ∀ α : MultiIndex d,
      propagatorW C t t (oscTestFun m α) = oscTestFun m α :=
    fun t ht α => (s102_propagator_classical (hcls α t ht)).terminal
  have hmatch : r2Vprop C m u u (s102_zf P X ζ u) = r2PathAt w u := by
    apply s102_ext
    intro α
    rw [s102_Vprop_coord hP hD hzu hlin hu ⟨le_rfl, hu.2⟩ α,
      hterm u hu, hwat u hu, s102_coord_zetaB hm hN P X hXm u ζ α]
  have hpred := s102_predicted_at hP hD hlin w (s102_zf P X ζ) hu hzu hmatch hti
  show OscDual.coord
      (OscPath.at' (r2Predicted C w (s102_zf P X ζ) u) (s102_tauk hH L i))
      (s102_alk L i) = _
  have hat : OscPath.at' (r2Predicted C w (s102_zf P X ζ) u)
      (s102_tauk hH L i) =
        r2PathAt (r2Predicted C w (s102_zf P X ζ) u) (s102_tk hH L i) :=
    (s102_r2PathAt_of_mem _ hti).symm
  rw [hat, hpred]
  by_cases hle : s102_tk hH L i ≤ u
  · rw [if_pos hle, min_eq_right hle, hwat _ hti,
      s102_coord_zetaB hm hN P X hXm _ ζ, hterm _ hti]
  · rw [if_neg hle, min_eq_left (not_le.1 hle).le,
      s102_Vprop_coord hP hD hzu hlin hu
        ⟨(not_le.1 hle).le, hti.2⟩ (s102_alk L i)]

private theorem fp81s21_moving_zf_indist
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (F : FilteredParticle A)
    {ζ : A.Ω} (hζ : ∀ t : ℝ≥0, F.X t ζ = A.X t ζ)
    (hInd : ∀ᵐ ω ∂A.P, ∀ t : ℝ≥0, F.X t ω = A.X t ω)
    (u : ℝ) (f : Euc p.d → ℝ) :
    s102_zf A.P F.X ζ u f = s102_zf A.P A.X ζ u f := by
  have hmap : A.P.map (F.X u.toNNReal) = A.P.map (A.X u.toNNReal) :=
    Measure.map_congr (hInd.mono fun ω hω => hω u.toNNReal)
  rw [s102_zf, hζ u.toNNReal, hmap]
  rfl

/-- Initial observation measurability for the moving filtered realization.
The proof narrows Aux97 to `S101Data` and moving adjoints; no stationary
`S102Std` density fields are used. -/
theorem fp81s21_moving_initial_obs_meas
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {r : ℕ} {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) H r c hH)
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H)
    (hr : (p.d : ℝ) / 2 + 2 < r)
    (hphys : Fp81MovingPhysicalInputs R hN A H)
    (L : ℕ) :
    ∀ t : ℝ, Measurable[F.ℱ t] (fun ζ =>
      s102_obs (s102_tauk hH L) (s102_alk L)
        (s102_y0 (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H A.P F.X ζ)) := by
  classical
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := wholeSpaceIndex p.d
  let Pw : ℝ := (p.d : ℝ) + 2
  have hN0 : 0 < N := by omega
  have hd1 : 1 ≤ p.d := Nat.le_trans (by decide) p.hd
  have hdcast : (0 : ℝ) ≤ (p.d : ℝ) := Nat.cast_nonneg _
  have hP : (p.d : ℝ) < 2 * Pw := by dsimp [Pw]; nlinarith [hdcast]
  have hP0 : 0 ≤ Pw := by dsimp [Pw]; linarith [hdcast]
  have hm : (p.d : ℝ) < m := by
    change (p.d : ℝ) < (wholeSpaceIndex p.d : ℝ)
    exact_mod_cast (show p.d < wholeSpaceIndex p.d by
      unfold wholeSpaceIndex
      omega)
  have hrr : (p.d : ℝ) / 2 < (r : ℝ) := by linarith [hr]
  have hmom := fp81s21_moving_filtered_moment p R hH hN A F hphys
  have hXm : ∀ t, Measurable (F.X t) := (F.strong H).adapted
  intro t
  have hle : F.ℱ 0 ≤ F.ℱ t := by
    rcases le_total 0 t with h | h
    · exact F.ℱ.mono h
    · exact le_of_eq (F.negative t h).symm
  have hfun : (fun ζ => s102_obs (s102_tauk hH L) (s102_alk L)
      (s102_y0 C m H A.P F.X ζ)) =
      fun ζ => (EuclideanSpace.equiv (Fin (s102_q p.d L)) ℝ).symm
        (fun i => s102_zf A.P F.X ζ 0 (s102_orb C m hH L i 0)) := by
    funext ζ
    ext i
    exact fp81s21_moving_obs_y0_coord hstd.hD hP hlin hH hd1 hP0
      hrr hN0 A.P F.X
      (by simpa using hmom 0 ⟨le_rfl, hH.le⟩)
      L ζ i
  rw [hfun]
  refine (EuclideanSpace.equiv (Fin (s102_q p.d L)) ℝ).symm.continuous.measurable.comp
    ((@measurable_pi_iff _ _ _ (F.ℱ t) _).2 fun i => ?_)
  have htobs : s102_tk hH L i ∈ Icc (0 : ℝ) H := (s102_tauk hH L i).2
  have hf : IsClassicalAdjointW C (s102_tk hH L i)
      (oscTestFun m (s102_alk L i)) (s102_orb C m hH L i) :=
    s102_propagator_classical (hstd.hcls (s102_alk L i) _ htobs)
  have hg : Measurable (s102_orb C m hH L i 0) :=
    ((hf.c2 0 ⟨le_rfl, htobs.1⟩).continuous.measurable)
  have h0 : Measurable[F.ℱ 0] (F.X 0) := F.filtered.adapted 0
  have h1 : Measurable[F.ℱ 0] (fun ζ =>
      HRS.Whole.pair (HRS.Whole.empirical (F.X 0 ζ))
        (s102_orb C m hH L i 0)) :=
    @Measurable.comp _ _ _ (F.ℱ 0) _ _ _ _ (s102_pairEmp_meas hN0 hg) h0
  have h2 : Measurable[F.ℱ t] (fun ζ =>
      s102_zf A.P F.X ζ 0 (s102_orb C m hH L i 0)) := by
    have htmp := ((h1.mono hle le_rfl).sub (@measurable_const _ _ _ (F.ℱ t)
      (HRS.Whole.pair (HRS.Whole.meanEmpirical (A.P.map (F.X 0)))
        (s102_orb C m hH L i 0)))).const_mul (Real.sqrt N)
    simpa [s102_zf, Real.toNNReal_zero] using htmp
  exact h2

#print axioms HRS.Fp81.S21.fp81s21_moving_initial_obs_meas

end HRS.Fp81.S21

end
