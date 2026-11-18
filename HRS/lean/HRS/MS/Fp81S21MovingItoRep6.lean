import HRS.MS.Fp81S21MovingItoRep5

/-!
# HRS S2.1(iii), packet 8.5: moving `S102ItoRep`

The stationary statements generalized here are:

* `R2InterpAux61.s102_PhicE` / `s102_PhicE_form`: the Euclidean noise
  coefficient and, for `u ≥ 0`, its coordinate is `s102_Phic`.
* `R2InterpAux96.s102_bdc` / `s102_bdc_prog_int`: for fixed `μ`,
  `bdc_i u ζ = if 0 ≤ u then -(√N)⁻¹ * s102_hh C m τ α
    (fun v => r2QuadField sQ μ P X v ζ) i u else 0`, with the stated
  stationary density assumptions yielding progressive local integrability.
* `R2InterpAux98.s102_bdE` / `s102_bdE_locL1`: Euclidean assembly of those
  coordinates and its progressive local-L¹ bound.
* `R2InterpAux97.s102_obs_y0`, `R2InterpAux92.s102_obs_Y`, and
  `R2InterpAux99.s102_bd_integral_coord` / `s102_bdc_integral`: the initial
  and predicted observation identities and drift integral identities.
* `R2InterpAux100.s102_loc_coord`: the scalar-coordinate identity for the
  local Euclidean Itô integral and stopping at `min u τᵢ`.
* `R2InterpAux101.s102_itoRep`: the producer of the `R2InterpAux61`
  `S102ItoRep` contract.

That stationary contract has witnesses `bd` and `Φc` satisfying, in order,
`IsProgressiveLocL1`, `IsProgressiveLocL2E`, initial-observation filtration
measurability, the nonnegative-time formula
`bd u ζ i = -(√N)⁻¹ * s102_hh C m τ α
  (fun v => r2QuadField sQ μ P X v ζ) i u`, the nonnegative-time formula
`Φc u ζ k i = s102_Phic C m hT L X u ζ k i`, and
`∀ᵐ ζ, ∀ u ∈ [0,T], obs(Y X ζ u) = itoProcess(... obs(y0 X ζ)) bd Φc u ζ`.

The moving statement below replaces the fixed `μ` by `r26t3_mu R v` at the
integration time `v`. It uses `A.X` for the observation path in `Y`, and
`F.X`, `F.ℱ`, and `F.Wc` for the initial adapted data and all stochastic
integration. P00's event `∀ᵐ ω, ∀ t, F.X t ω = A.X t ω` transports the
observation identity and the M1-controlled moving drift. No stationary
density hypothesis is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas

private theorem fp81s21_moving_obs_y0_coord_final
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

private theorem fp81s21_moving_obs_Y_coord_final
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

private theorem fp81s21_moving_zf_indist_final
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

private theorem fp81s21_moving_filtered_moment_final
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    (hphys : Fp81MovingPhysicalInputs R hN A H) :
    ∀ u ∈ Icc (0 : ℝ) H,
      Integrable (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 2))
        (HRS.Whole.meanEmpirical (A.P.map (F.X u.toNNReal))) := by
  obtain ⟨Cm, hCm⟩ := hphys.particle_moment
  intro u hu
  have hmap : A.P.map (F.X u.toNNReal) = A.P.map (A.X u.toNNReal) :=
    Measure.map_congr (F.indist.mono fun ω hω => hω u.toNNReal)
  rw [hmap]
  exact (hCm u hu).1

/-- Moving-reference generalization of `HRS.MS.R2Interp.S102ItoRep`.
The observed path remains `A.X`; the adapted initial observation and the
stochastic integrals use the P00 filtered realization `F.X`. -/
def fp81s21_moving_S102ItoRep
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    (L : ℕ) {N : ℕ} (A : Particle R N) (F : FilteredParticle A) : Prop :=
  ∃ (bd : ℝ → A.Ω → EuclideanSpace ℝ (Fin (s102_q p.d L)))
    (Φc : ℝ → A.Ω → (Fin N × Fin p.d) → EuclideanSpace ℝ (Fin (s102_q p.d L))),
    IsProgressiveLocL1 A.P F.ℱ bd ∧
    IsProgressiveLocL2E A.P F.ℱ Φc ∧
    (∀ t : ℝ, Measurable[F.ℱ t] (fun ζ =>
      s102_obs (s102_tauk hH L) (s102_alk L)
        (s102_y0 (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H A.P F.X ζ))) ∧
    (∀ u ζ i, 0 ≤ u →
      bd u ζ i = -(Real.sqrt N)⁻¹ * s102_hh (r26t3_coeff R)
        (wholeSpaceIndex p.d : ℝ) (s102_tauk hH L) (s102_alk L)
        (fun v => r2QuadField p.s (r26t3_mu R v) A.P F.X v ζ) i u) ∧
    (∀ u ζ k i, 0 ≤ u →
      Φc u ζ k i = s102_Phic (r26t3_coeff R)
        (wholeSpaceIndex p.d : ℝ) hH L F.X u ζ k i) ∧
    ∀ᵐ ζ ∂A.P, ∀ u ∈ Icc (0 : ℝ) H,
      s102_obs (s102_tauk hH L) (s102_alk L)
        (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H A.P A.X ζ u) =
      itoProcess A.P F.ℱ F.Wc
        (fun ω => s102_obs (s102_tauk hH L) (s102_alk L)
          (s102_y0 (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H A.P F.X ω))
        bd Φc u ζ

/-- Assemble the moving progressive drift/noise coordinates, stopping, and
observation identities into the moving `S102ItoRep` contract. -/
theorem fp81s21_moving_itoRep
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {r : ℕ} {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) H r c hH)
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H)
    (hr : (p.d : ℝ) / 2 + 2 < r)
    (hphys : Fp81MovingPhysicalInputs R hN A H)
    (L : ℕ) : fp81s21_moving_S102ItoRep p R hH L A F := by
  classical
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := wholeSpaceIndex p.d
  let bd : ℝ → A.Ω → EuclideanSpace ℝ (Fin (s102_q p.d L)) :=
    fp81s21_moving_bdE p R hH L p.s A.P F.X
  let Φc : ℝ → A.Ω → (Fin N × Fin p.d) →
      EuclideanSpace ℝ (Fin (s102_q p.d L)) :=
    s102_PhicE C m hH L F.X
  have hbd := fp81s21_moving_bdE_locL1 p R hH hN A F hstd hr hphys L
  have hPhi := fp81s21_moving_PhicE_locL2 p R hH L A.P F.X
    F.filtered.progressive hstd
  have hN0 : 0 < N := by omega
  have hd1 : 1 ≤ p.d := Nat.le_trans (by decide) p.hd
  have hdcast : (0 : ℝ) ≤ (p.d : ℝ) := Nat.cast_nonneg _
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by linarith
  have hP0 : 0 ≤ (p.d : ℝ) + 2 := by linarith
  have hm : (p.d : ℝ) < m := by
    change (p.d : ℝ) < (wholeSpaceIndex p.d : ℝ)
    exact_mod_cast (show p.d < wholeSpaceIndex p.d by
      unfold wholeSpaceIndex
      omega)
  have hrr : (p.d : ℝ) / 2 < (r : ℝ) := by linarith [hr]
  have hmomA : ∀ u ∈ Icc (0 : ℝ) H,
      Integrable (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 2))
        (HRS.Whole.meanEmpirical (A.P.map (A.X u.toNNReal))) := by
    obtain ⟨Cm, hCm⟩ := hphys.particle_moment
    intro u hu
    exact (hCm u hu).1
  have hmomF := fp81s21_moving_filtered_moment_final p R hH hN A F hphys
  have hXmA : ∀ t, Measurable (A.X t) := (A.strong H).adapted
  have hcontz := s102_zeta_cont hm hN0 A.P A.X hXmA (A.strong H).cont
  have hinitial := fp81s21_moving_initial_obs_meas p R hH hN A F
    hstd hlin hr hphys L
  refine ⟨bd, Φc, ?_, ?_, hinitial, ?_, ?_, ?_⟩
  · simpa [bd] using hbd
  · simpa [Φc] using hPhi
  · intro u ζ i hu
    change fp81s21_moving_bdc p R hH L p.s A.P F.X i u ζ = _
    exact fp81s21_moving_bdc_form p R hH L p.s A.P F.X i u ζ hu
  · intro u ζ k i hu
    exact s102_PhicE_form C m hH L F.X u hu ζ k i
  · have horb : ∀ i : Fin (s102_q p.d L), ∀ᵐ ζ ∂A.P,
      ∀ τ ∈ Icc (0 : ℝ) (s102_tk hH L i),
        s102_zf A.P F.X ζ τ (s102_orb C m hH L i τ) =
          s102_zf A.P F.X ζ 0 (s102_orb C m hH L i 0) +
            (Real.sqrt N * (Real.sqrt (2 * p.β⁻¹) / N)) *
              itoIntegral A.P F.ℱ F.Wc
                (s102_Ig (s102_orb C m hH L i)
                  (s102_tk hH L i) F.X) τ ζ +
            ∫ s in Icc (0 : ℝ) τ,
              (-(Real.sqrt N)⁻¹ * r2QuadField p.s (r26t3_mu R s)
                A.P F.X s ζ (s102_orb C m hH L i s)) := by
      intro i
      exact fp81s21_moving_orbit_zeta p R hδ hδh hH hN A F hphys
        (s102_tauk hH L i).2 (s102_alk L i)
    have hloc : ∀ i : Fin (s102_q p.d L), ∀ᵐ ζ ∂A.P,
      ∀ u : ℝ,
        (localItoIntegralE A.P F.ℱ F.Wc Φc u ζ).ofLp i =
          (Real.sqrt N *
            (Real.sqrt (2 * (r26t3_coeff R).ν) / N)) *
            itoIntegral A.P F.ℱ F.Wc
              (s102_Ig (s102_orb C m hH L i)
                (s102_tk hH L i) F.X) u ζ ∧
        itoIntegral A.P F.ℱ F.Wc
          (s102_Ig (s102_orb C m hH L i)
            (s102_tk hH L i) F.X) u ζ =
          itoIntegral A.P F.ℱ F.Wc
            (s102_Ig (s102_orb C m hH L i)
              (s102_tk hH L i) F.X)
            (min u (s102_tk hH L i)) ζ := by
      intro i
      simpa [Φc, C, m] using
        fp81s21_moving_loc_coord p R hH L A.P F.filtered.brownian
          F.X F.filtered.progressive hstd i
    filter_upwards [hcontz, ae_all_iff.2 horb, ae_all_iff.2 hloc,
      hbd.int H, F.indist] with ζ hc ho hl hbdInt hInd
    have hζ : ∀ t : ℝ≥0, F.X t ζ = A.X t ζ := hInd
    have hbdcoord : ∀ u ∈ Icc (0 : ℝ) H,
        ∀ i : Fin (s102_q p.d L),
          IntegrableOn
            (fun s => fp81s21_moving_bdc p R hH L p.s A.P F.X i s ζ)
            (Icc (0 : ℝ) u) := by
      intro u hu i
      have hsub : Icc (0 : ℝ) u ⊆ Icc (0 : ℝ) H :=
        Icc_subset_Icc le_rfl hu.2
      have hproj := (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp
        (hbdInt.mono_set hsub)
      refine IntegrableOn.congr_fun hproj (fun s hs => ?_) measurableSet_Icc
      simp [bd, fp81s21_moving_bdE]
    intro u hu
    have hτi : ∀ i : Fin (s102_q p.d L),
        min u (s102_tk hH L i) ∈ Icc (0 : ℝ) (s102_tk hH L i) := by
      intro i
      exact ⟨le_min hu.1 (s102_tauk hH L i).2.1,
        min_le_right _ _⟩
    ext i
    have e0 := fp81s21_moving_obs_Y_coord_final hstd.hD hstd.hcls
      hP hlin hH hd1 hP0 hrr hm hN0 A.P A.X hXmA hmomA L ζ hc hu i
    have ez := fp81s21_moving_zf_indist_final p R A F hζ F.indist
      (min u (s102_tk hH L i))
      (propagatorW C (min u (s102_tk hH L i))
        (s102_tk hH L i) (oscTestFun m (s102_alk L i)))
    have e1 := ho i _ (hτi i)
    have e2 := fp81s21_moving_obs_y0_coord_final hstd.hD hP hlin hH
      hd1 hP0 hrr hN0 A.P F.X
      (by simpa using hmomF 0 ⟨le_rfl, hH.le⟩) L ζ i
    have e3 := fp81s21_moving_bd_integral_coord p R hH L p.s A.P F.X
      ζ u (hbdcoord u hu) i
    have e3' := fp81s21_moving_bdc_integral p R hH L p.s A.P F.X
      ζ hu.1 i
    obtain ⟨e4, e5⟩ := hl i u
    have e1' : s102_zf A.P F.X ζ (min u (s102_tk hH L i))
        (s102_orb C m hH L i (min u (s102_tk hH L i))) =
      s102_zf A.P F.X ζ 0 (s102_orb C m hH L i 0) +
        (Real.sqrt N * (Real.sqrt (2 * p.β⁻¹) / N)) *
          itoIntegral A.P F.ℱ F.Wc
            (s102_Ig (s102_orb C m hH L i)
              (s102_tk hH L i) F.X)
            (min u (s102_tk hH L i)) ζ +
        ∫ s in Icc (0 : ℝ) (min u (s102_tk hH L i)),
          (-(Real.sqrt N)⁻¹ * r2QuadField p.s (r26t3_mu R s)
            A.P F.X s ζ (s102_orb C m hH L i s)) := by
      simpa [s102_orb, s102_tk] using e1
    change (s102_obs (s102_tauk hH L) (s102_alk L)
        (s102_Y C m H A.P A.X ζ u)).ofLp i =
      ((s102_obs (s102_tauk hH L) (s102_alk L)
          (s102_y0 C m H A.P F.X ζ)) +
        (∫ s in Icc (0 : ℝ) u, bd s ζ) +
        localItoIntegralE A.P F.ℱ F.Wc Φc u ζ).ofLp i
    rw [PiLp.add_apply, PiLp.add_apply, e0, ez.symm, e2, e3, e3', e4, e5]
    refine e1'.trans ?_
    have hν : (r26t3_coeff R).ν = p.β⁻¹ := rfl
    rw [hν]
    ring

#print axioms HRS.Fp81.S21.fp81s21_moving_itoRep

end HRS.Fp81.S21

end
