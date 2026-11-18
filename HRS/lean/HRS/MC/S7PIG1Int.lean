import HRS.MC.S7PIDSAsm

/-!
# Packet piG, part G2 (helper): integrability of the integrand of `IsJValue`

For `zr : ℝ → E_r` measurable, bounded by `M` on `[0,T]`, and smooth `φ_a, φ_b`, the integrand
`u ↦ z^u(∇U^{u,t_a}φ_a · ∇U^{u,t_b}φ_b)` (`z^u = ofSeq m (fourierCoeff (zr u))`) is integrable on
`(0,T] ∩ [0, t_a ∧ t_b]`.  It is the sum of the series of `s7_PID_expansion_proof`, with the measurability and the
bounds of `S7PIDSMain.lean` (re-done here for the single interval `(0,T]`, because `s7_PID_series_proof` does not
expose the integrability).  This is what gives the additivity of `a ↦ ∫_{(0,a] ∩ …}` needed for `s7_PIG_J_measure`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIG1

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
set_option maxSynthPendingDepth 3 in
theorem S7PIG1_integrand_integrable (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (zr : ℝ → NegSobolev d r) (hzr : Measurable zr)
    (M : ℝ) (hM : ∀ u ∈ Set.Icc (0 : ℝ) T, ‖zr u‖ ≤ M) (ta tb : ℝ) (hta : ta ∈ Set.Icc (0 : ℝ) T)
    (htb : tb ∈ Set.Icc (0 : ℝ) T) (φa φb : Torus d → ℝ) (hφa : Torus.IsSmooth φa) (hφb : Torus.IsSmooth φb) :
    IntegrableOn (fun u => NegSobolev.eval
        (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) : NegSobolev d m)
        (fun x => inner ℝ (Torus.grad (propagator R.D R.ρ u ta φa) x)
          (Torus.grad (propagator R.D R.ρ u tb φb) x)))
      (Set.Ioc (0 : ℝ) T ∩ Set.Icc 0 (min ta tb)) := by
  classical
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hrm : r ≤ m := by rw [hr]; linarith
  obtain ⟨Cg, hCg0, hCg⟩ := HRS.MC.Sec7.S7PIDR.s7_PID_gradprod_proof (d := d) r hr0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT.le⟩)
  obtain ⟨S, hSdef⟩ : ∃ S : Set ℝ, S = Set.Ioc (0 : ℝ) T ∩ Set.Icc 0 (min ta tb) := ⟨_, rfl⟩
  rw [← hSdef]
  have hSm : MeasurableSet S := by rw [hSdef]; exact measurableSet_Ioc.inter measurableSet_Icc
  have hSsub : S ⊆ Set.Ioc 0 T := by rw [hSdef]; exact Set.inter_subset_left
  have hSa : ∀ u ∈ S, u ≤ ta := fun u hu => by
    rw [hSdef] at hu; exact hu.2.2.trans (min_le_left _ _)
  have hSb : ∀ u ∈ S, u ≤ tb := fun u hu => by
    rw [hSdef] at hu; exact hu.2.2.trans (min_le_right _ _)
  have hSu : ∀ u ∈ S, u ∈ Set.Icc (0 : ℝ) T := fun u hu => ⟨(hSsub hu).1.le, (hSsub hu).2⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, r + d + 2 ≤ N := ⟨⌈r + d + 2⌉₊, Nat.le_ceil _⟩
  obtain ⟨Aa, hAa0, hAa⟩ := HRS.MC.Sec7.S7PIDM.s7_PID_mode_decay_proof R m hm T hT φa hφa N
  obtain ⟨Ab, hAb0, hAb⟩ := HRS.MC.Sec7.S7PIDM.s7_PID_mode_decay_proof R m hm T hT φb hφb N
  obtain ⟨h, hhdef⟩ : ∃ h : NonzeroLattice d → ℝ, ∀ k, h k = Lattice.jp k.1 ^ (-((N : ℝ) - r - 1)) :=
    ⟨fun k => Lattice.jp k.1 ^ (-((N : ℝ) - r - 1)), fun _ => rfl⟩
  have hh0 : ∀ k, 0 ≤ h k := fun k => by rw [hhdef]; exact Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hhs : Summable h := by
    have hs := summable_jp_rpow (d := d) (((N : ℝ) - r - 1) / 2) (by linarith)
    refine hs.congr fun k => ?_
    rw [hhdef]
    congr 1
    ring
  have hhh : Summable fun pr : NonzeroLattice d × NonzeroLattice d => h pr.1 * h pr.2 :=
    Summable.mul_of_nonneg hhs hhs (fun k => hh0 k) (fun k => hh0 k)
  obtain ⟨F, hFdef⟩ : ∃ F : NonzeroLattice d × NonzeroLattice d → ℝ → ℝ, ∀ pr u, F pr u =
      NegSobolev.eval (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k))
          (gradProd pr.1 pr.2) *
        NegSobolev.eval (Vprop R.D R.ρ m ta u (modeVec m pr.1)) φa *
        NegSobolev.eval (Vprop R.D R.ρ m tb u (modeVec m pr.2)) φb :=
    ⟨fun pr u => NegSobolev.eval (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k))
          (gradProd pr.1 pr.2) *
        NegSobolev.eval (Vprop R.D R.ρ m ta u (modeVec m pr.1)) φa *
        NegSobolev.eval (Vprop R.D R.ρ m tb u (modeVec m pr.2)) φb, fun _ _ => rfl⟩
  have hFm : ∀ pr, AEStronglyMeasurable (F pr) (volume.restrict S) := by
    intro pr
    obtain ⟨hmemS, -⟩ := hCg pr.1 pr.2
    have e : F pr = fun u => NegSobolev.eval
        (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k)) (gradProd pr.1 pr.2) *
        NegSobolev.eval (Vprop R.D R.ρ m ta u (modeVec m pr.1)) φa *
        NegSobolev.eval (Vprop R.D R.ρ m tb u (modeVec m pr.2)) φb := funext (hFdef pr)
    rw [e]
    exact ((S7PIDS.S7PIDS_meas_eval hrm hmemS hzr).aestronglyMeasurable.mul
      (S7PIDS.S7PIDS_meas_V R m hm T hT hφa hta pr.1 hSm hSsub hSa)).mul
      (S7PIDS.S7PIDS_meas_V R m hm T hT hφb htb pr.2 hSm hSsub hSb)
  have hFb : ∀ pr, ∀ u ∈ S, ‖F pr u‖ ≤ (M * Cg * Aa * Ab) * (h pr.1 * h pr.2) := by
    intro pr u hu
    obtain ⟨hmemS, hnormS⟩ := hCg pr.1 pr.2
    have hu0 : 0 ≤ u := (hSu u hu).1
    have h1 := S7PIDS.S7PIDS_bound_eval hrm hmemS hnormS (hM u (hSu u hu))
    have h2 := hAa u ta hu0 (hSa u hu) hta.2 pr.1
    have h3 := hAb u tb hu0 (hSb u hu) htb.2 pr.2
    have e1 : Lattice.jp pr.1.1 ^ (r + 1) * Lattice.jp pr.1.1 ^ (-(N : ℝ)) = h pr.1 := by
      rw [← Real.rpow_add (Torus.jp_pos _), hhdef]; congr 1; ring
    have e2 : Lattice.jp pr.2.1 ^ (r + 1) * Lattice.jp pr.2.1 ^ (-(N : ℝ)) = h pr.2 := by
      rw [← Real.rpow_add (Torus.jp_pos _), hhdef]; congr 1; ring
    have hj1 : 0 ≤ Lattice.jp pr.1.1 ^ (-(N : ℝ)) := Real.rpow_nonneg (Torus.jp_pos _).le _
    have hj2 : 0 ≤ Lattice.jp pr.2.1 ^ (-(N : ℝ)) := Real.rpow_nonneg (Torus.jp_pos _).le _
    have hp1 : 0 ≤ Lattice.jp pr.1.1 ^ (r + 1) := Real.rpow_nonneg (Torus.jp_pos _).le _
    have hp2 : 0 ≤ Lattice.jp pr.2.1 ^ (r + 1) := Real.rpow_nonneg (Torus.jp_pos _).le _
    rw [hFdef, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    calc _ ≤ (M * (Cg * Lattice.jp pr.1.1 ^ (r + 1) * Lattice.jp pr.2.1 ^ (r + 1))) *
          (Aa * Lattice.jp pr.1.1 ^ (-(N : ℝ))) * (Ab * Lattice.jp pr.2.1 ^ (-(N : ℝ))) :=
          mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _)
            (mul_nonneg hM0 (mul_nonneg (mul_nonneg hCg0 hp1) hp2))) h3 (abs_nonneg _)
            (mul_nonneg (mul_nonneg hM0 (mul_nonneg (mul_nonneg hCg0 hp1) hp2))
              (mul_nonneg hAa0 hj1))
      _ = (M * Cg * Aa * Ab) * ((Lattice.jp pr.1.1 ^ (r + 1) * Lattice.jp pr.1.1 ^ (-(N : ℝ))) *
          (Lattice.jp pr.2.1 ^ (r + 1) * Lattice.jp pr.2.1 ^ (-(N : ℝ)))) := by ring
      _ = (M * Cg * Aa * Ab) * (h pr.1 * h pr.2) := by rw [e1, e2]
  -- the series
  have hHas : ∀ u ∈ S, HasSum (fun pr => F pr u)
      (NegSobolev.eval (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) : NegSobolev d m)
        (fun x => inner ℝ (Torus.grad (propagator R.D R.ρ u ta φa) x)
          (Torus.grad (propagator R.D R.ρ u tb φb) x))) := by
    intro u hu
    have hz : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) *
        NegSobolev.fourierCoeff
          (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) : NegSobolev d m) k) 2 := by
      refine (Torus.memℓp_two_iff _).2 ?_
      refine (HRS.MC.Sec7.PIE.pie_coeff_summable (zr u)).congr fun k => ?_
      rw [S7PIDS.S7PIDS_fc_embed hrm (zr u) k]
    have := HRS.MC.Sec7.S7PIDE.s7_PID_expansion_proof R r hr m hm T hT φa φb hφa hφb u ta tb
      (hSu u hu).1 (hSa u hu) (hSb u hu) hta.2 htb.2 _ hz
    simpa only [hFdef] using this
  have hfm : AEStronglyMeasurable (fun u => NegSobolev.eval
        (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) : NegSobolev d m)
        (fun x => inner ℝ (Torus.grad (propagator R.D R.ρ u ta φa) x)
          (Torus.grad (propagator R.D R.ρ u tb φb) x))) (volume.restrict S) := by
    refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset (NonzeroLattice d × NonzeroLattice d)))
      (f := fun s u => ∑ pr ∈ s, F pr u) (fun s => Finset.aestronglyMeasurable_fun_sum s (fun pr _ => hFm pr)) ?_
    exact (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun u hu => hHas u hu)
  have : IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    refine lt_of_le_of_lt (measure_mono hSsub) ?_
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  refine Integrable.mono' (integrable_const (∑' pr : NonzeroLattice d × NonzeroLattice d,
    (M * Cg * Aa * Ab) * (h pr.1 * h pr.2))) hfm ?_
  refine (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun u hu => ?_)
  exact (hHas u hu).norm_le_of_bounded (hhh.mul_left (M * Cg * Aa * Ab)).hasSum (fun pr => hFb pr u hu)

end HRS.MC.Sec7.S7PIG1

end
