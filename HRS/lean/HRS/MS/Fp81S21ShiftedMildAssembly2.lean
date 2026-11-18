import HRS.MS.Fp81S21ShiftedMildAssembly
import HRS.MS.Fp81S21ShiftedMild
import HRS.MS.Fp81S21NoisePath6

/-! Transfer of the shifted mild equation to rational local times for A.X. -/
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Set

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp
open HRS.MP.RdRem
open scoped NNReal

/-- The actual centered particle coordinate, expanded from the compiled
`zetaB` definition. -/
def fp81s21_particleZeta
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (t : ℝ) (ω : A.Ω) :
    OscDual p.d (wholeSpaceIndex p.d : ℝ) :=
  zetaB (wholeSpaceIndex p.d : ℝ)
    (A.P.map (A.X t.toNNReal)) (A.X t.toNNReal ω)

/-- The initial centered coordinate propagated from the window start to the
terminal time. -/
def fp81s21_shiftedModeInitial
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (α : MultiIndex p.d) (b t : ℝ) (ω : A.Ω) : ℝ :=
  s102_zf A.P A.X ω b
    (propagatorW (r26t3_coeff R) b t
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α))

/-- Evaluation of the reconstructed path at a rational local time. -/
def fp81s21_shiftedNoiseValue
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) {H : ℝ}
    (hH : 0 ≤ H) (G : A.Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H)
    (ω : A.Ω) (u : ℝ) :
    OscDual p.d (wholeSpaceIndex p.d : ℝ) :=
  OscPath.at' (G ω) ⟨mrrClamp H u, mrrClamp_mem hH u⟩

/-- Indistinguishable coupled particle paths have the same centered
configuration functional at every fixed time, on the same sample event. -/
theorem fp81s21_s102_zf_indist
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (F : FilteredParticle A)
    {ω : A.Ω} (hω : ∀ t : ℝ≥0, F.X t ω = A.X t ω)
    (u : ℝ) (f : Euc p.d → ℝ) :
    s102_zf A.P F.X ω u f = s102_zf A.P A.X ω u f := by
  have hmap : A.P.map (F.X u.toNNReal) = A.P.map (A.X u.toNNReal) :=
    Measure.map_congr (F.indist.mono fun ω' hω' => hω' u.toNNReal)
  rw [s102_zf, hω u.toNNReal, hmap]
  rfl

/-- On the same indistinguishability event, the moving quadratic field is
unchanged when the filtered path is replaced by the particle path. -/
theorem fp81s21_quadField_indist
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (F : FilteredParticle A)
    {ω : A.Ω} (hω : ∀ t : ℝ≥0, F.X t ω = A.X t ω)
    (u : ℝ) (f : Euc p.d → ℝ) :
    r2QuadField p.s (r26t3_mu R u) A.P F.X u ω f =
      r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f := by
  unfold r2QuadField
  have hInt : (fun ω' => pairEnergy
      (commutatorKernel p.d p.s (fun x => gradient f x))
      (F.X u.toNNReal ω') (r26t3_mu R u)) =ᵐ[A.P]
      (fun ω' => pairEnergy
        (commutatorKernel p.d p.s (fun x => gradient f x))
        (A.X u.toNNReal ω') (r26t3_mu R u)) := by
    filter_upwards [F.indist] with ω' hω'
    rw [hω' u.toNNReal]
  rw [hω u.toNNReal, integral_congr_ae hInt]

/-- At every rational local time, the centered coordinate minus the
reconstructed noise equals the initial propagated coordinate minus the
inverse-square-root shifted drift. The event is simultaneous in modes and
rational local times. -/
theorem fp81s21_shifted_mild_coord_rational
    (p : Parameters) {δ b H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hb : 0 ≤ b) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    (hphys : Fp81MovingPhysicalInputs R hN A (b + H))
    (G : A.Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H)
    (hNoise : fp81s21_NoiseMatch p R A F hH b G)
    (hsource : ∀ᵐ ω ∂A.P, ∀ α : MultiIndex p.d, ∀ a t : ℝ,
      0 ≤ a → a ≤ t → t ≤ b + H →
      IntervalIntegrable
        (fun v => fp81s21_window_mode_source_field p R A α v t ω) volume a t) :
    ∀ᵐ ω ∂A.P, ∀ α : MultiIndex p.d, ∀ q : ℚ,
      (hq : (q : ℝ) ∈ Icc (0 : ℝ) H) →
      OscDual.coord
          (fp81s21_particleZeta p R A (b + (q : ℝ)) ω -
            fp81s21_shiftedNoiseValue p R A hH.le G ω (q : ℝ)) α =
        fp81s21_shiftedModeInitial p R A α b (b + (q : ℝ)) ω -
          (Real.sqrt (N : ℝ))⁻¹ *
            fp81s21_shiftedModeDrift p R A α b (b + (q : ℝ)) ω := by
  apply ae_all_iff.2
  intro α
  apply ae_all_iff.2
  intro q
  by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) H
  · have ht : b + (q : ℝ) ∈ Icc b (b + H) := by
      constructor
      · linarith [hq.1]
      · linarith [hq.2]
    filter_upwards
      [fp81s21_shifted_mild_identity p R hδ hδh hb hH hN A F
        hphys ht α,
       hNoise, hsource, F.indist] with ω hm hn hs hInd
    intro _
    have hω : ∀ t : ℝ≥0, F.X t ω = A.X t ω := hInd
    have hMild := hm
    have hsrc0t : IntervalIntegrable
        (fun v => fp81s21_window_mode_source_field p R A α v
          (b + (q : ℝ)) ω) volume 0 (b + (q : ℝ)) :=
      hs α 0 (b + (q : ℝ)) (by norm_num) (by linarith [hb, hq.1]) ht.2
    have hsrc0b : IntervalIntegrable
        (fun v => fp81s21_window_mode_source_field p R A α v
          (b + (q : ℝ)) ω) volume 0 b := by
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le hb).2
      apply ((intervalIntegrable_iff_integrableOn_Icc_of_le
        (by linarith [hb, hq.1])).1 hsrc0t).mono_set
      exact Icc_subset_Icc le_rfl ht.1
    have hsrcbt : IntervalIntegrable
        (fun v => fp81s21_window_mode_source_field p R A α v
          (b + (q : ℝ)) ω) volume b (b + (q : ℝ)) :=
      hs α b (b + (q : ℝ)) hb ht.1 ht.2
    have hsub := fp81s21_shifted_mode_drift_subtraction
      p R A α hb ht.1 ω hsrc0b hsrcbt
    have hIt : (∫ v in Icc (0 : ℝ) (b + (q : ℝ)),
        (-(Real.sqrt (N : ℝ))⁻¹ *
          r2QuadField p.s (r26t3_mu R v) A.P F.X v ω
            (propagatorW (r26t3_coeff R) v (b + (q : ℝ))
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α)))) =
      ∫ v in Icc (0 : ℝ) (b + (q : ℝ)),
        (-(Real.sqrt (N : ℝ))⁻¹ *
          fp81s21_window_mode_source_field p R A α v
            (b + (q : ℝ)) ω) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      change -(Real.sqrt (N : ℝ))⁻¹ *
          r2QuadField p.s (r26t3_mu R v) A.P F.X v ω
            (propagatorW (r26t3_coeff R) v (b + (q : ℝ))
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) =
        -(Real.sqrt (N : ℝ))⁻¹ *
          r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
            (propagatorW (r26t3_coeff R) v (b + (q : ℝ))
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α))
      rw [fp81s21_quadField_indist p R A F hω v
        (propagatorW (r26t3_coeff R) v (b + (q : ℝ))
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α))]
    have hIb : (∫ v in Icc (0 : ℝ) b,
        (-(Real.sqrt (N : ℝ))⁻¹ *
          r2QuadField p.s (r26t3_mu R v) A.P F.X v ω
            (propagatorW (r26t3_coeff R) v (b + (q : ℝ))
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α)))) =
      ∫ v in Icc (0 : ℝ) b,
        (-(Real.sqrt (N : ℝ))⁻¹ *
          fp81s21_window_mode_source_field p R A α v
            (b + (q : ℝ)) ω) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      change -(Real.sqrt (N : ℝ))⁻¹ *
          r2QuadField p.s (r26t3_mu R v) A.P F.X v ω
            (propagatorW (r26t3_coeff R) v (b + (q : ℝ))
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) =
        -(Real.sqrt (N : ℝ))⁻¹ *
          r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
            (propagatorW (r26t3_coeff R) v (b + (q : ℝ))
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α))
      rw [fp81s21_quadField_indist p R A F hω v
        (propagatorW (r26t3_coeff R) v (b + (q : ℝ))
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α))]
    have hmild' :
        s102_zf A.P A.X ω (b + (q : ℝ))
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α) =
          fp81s21_shiftedModeInitial p R A α b (b + (q : ℝ)) ω +
            fp81s21_shiftedNoiseDiff p R A F b (b + (q : ℝ)) α ω +
            (-(Real.sqrt (N : ℝ))⁻¹ *
              fp81s21_shiftedModeDrift p R A α b (b + (q : ℝ)) ω) := by
      rw [fp81s21_s102_zf_indist p R A F hω
        (b + (q : ℝ)) (oscTestFun (wholeSpaceIndex p.d : ℝ) α),
        fp81s21_s102_zf_indist p R A F hω b
          (propagatorW (r26t3_coeff R) b (b + (q : ℝ))
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)),
        hIt, hIb, hsub] at hMild
      simpa [fp81s21_shiftedModeInitial] using hMild
    have hNpos : 0 < N := by omega
    have hTpos : 0 < b + H := by linarith
    have hXmeas : ∀ t : ℝ≥0, Measurable (A.X t) :=
      (A.strong (b + H)).adapted
    have hmindex : (p.d : ℝ) < (wholeSpaceIndex p.d : ℝ) := by
      exact_mod_cast (show p.d < wholeSpaceIndex p.d by
        unfold wholeSpaceIndex
        omega)
    have hcoord := HRS.MS.R2Interp.s102_coord_zetaB hmindex hNpos
      A.P A.X hXmeas (b + (q : ℝ)) ω α
    have hNoiseCoord :
        OscDual.coord
          (fp81s21_shiftedNoiseValue p R A hH.le G ω (q : ℝ)) α =
          fp81s21_shiftedNoiseDiff p R A F b
            (b + (q : ℝ)) α ω := by
      have hn' := hn α q
      simpa [fp81s21_shiftedNoiseValue, HRS.MP.RdRem.mrrClamp_of_mem hq] using hn'
    have hcoordSub :
        OscDual.coord
          (fp81s21_particleZeta p R A (b + (q : ℝ)) ω -
            fp81s21_shiftedNoiseValue p R A hH.le G ω (q : ℝ)) α =
          OscDual.coord (fp81s21_particleZeta p R A (b + (q : ℝ)) ω) α -
            OscDual.coord
              (fp81s21_shiftedNoiseValue p R A hH.le G ω (q : ℝ)) α := by
      rw [sub_eq_add_neg, OscDual.coord_add, ← neg_one_smul ℝ
        (fp81s21_shiftedNoiseValue p R A hH.le G ω (q : ℝ)),
        OscDual.coord_smul]
      ring
    calc
      OscDual.coord
          (fp81s21_particleZeta p R A (b + (q : ℝ)) ω -
            fp81s21_shiftedNoiseValue p R A hH.le G ω (q : ℝ)) α =
          OscDual.coord (fp81s21_particleZeta p R A (b + (q : ℝ)) ω) α -
            OscDual.coord
              (fp81s21_shiftedNoiseValue p R A hH.le G ω (q : ℝ)) α := hcoordSub
      _ = fp81s21_shiftedModeInitial p R A α b (b + (q : ℝ)) ω -
            (Real.sqrt (N : ℝ))⁻¹ *
              fp81s21_shiftedModeDrift p R A α b (b + (q : ℝ)) ω := by
        rw [fp81s21_particleZeta, hcoord, hNoiseCoord, hmild']
        dsimp [fp81s21_shiftedModeInitial]
        ring
  · exact Filter.Eventually.of_forall fun ω hbad => False.elim (hq hbad)

#print axioms HRS.Fp81.S21.fp81s21_s102_zf_indist
#print axioms HRS.Fp81.S21.fp81s21_quadField_indist
#print axioms HRS.Fp81.S21.fp81s21_shifted_mild_coord_rational

end HRS.Fp81.S21

end
