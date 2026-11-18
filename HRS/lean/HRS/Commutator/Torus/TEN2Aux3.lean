import HRS.Commutator.Torus.TEN2Aux1

/-!
# Torus energy layer (packet T-EN2), helper part 3: the periodisation versus the centred representative

Prefix `ten2_`.  (i) `∫_𝕋 H(centeredRep x) ≤ ∫_{ℝ^d} H` for `H ≥ 0`; (ii) the pointwise bound
`perio f_η (x) ≤ f_η(centeredRep x) + K₁ η^{2d+4-s}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

theorem ten2_toEuc_zero : Lattice.toEuc (0 : Lattice d) = 0 := by
  ext i; simp [Lattice.toEuc]

theorem ten2_toEuc_sub (m n : Lattice d) :
    Lattice.toEuc (m - n) = Lattice.toEuc m - Lattice.toEuc n := by
  ext i; simp [Lattice.toEuc]

theorem ten2_cr_measurable : Measurable (KernelGrad.centeredRep : Torus d → Euc d) := by
  have h : ∀ i : Fin d, Measurable fun z : Torus d =>
      (if (Torus.rep z) i ≤ 1 / 2 then (Torus.rep z) i else (Torus.rep z) i - 1) := by
    intro i
    have hr : Measurable fun z : Torus d => (Torus.rep z) i := (tpos_measurable_coord i).comp tpos_measurable_rep
    exact Measurable.ite (measurableSet_le hr measurable_const) hr (hr.sub_const 1)
  have h2 : Measurable fun z : Torus d => (fun i : Fin d =>
      (if (Torus.rep z) i ≤ 1 / 2 then (Torus.rep z) i else (Torus.rep z) i - 1)) :=
    Measurable.of_eval h
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp h2

/-- Unfolding the periodisation: `∫_𝕋 H(centeredRep x) ≤ ∫_{ℝ^d} H`. -/
theorem ten2_lintegral_cr_le (H : Euc d → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ x : Torus d, H (KernelGrad.centeredRep x) ≤ ∫⁻ y : Euc d, H y := by
  have h1 : ∀ x : Torus d, H (KernelGrad.centeredRep x) ≤
      ∑' m : Lattice d, H (Torus.rep x + Lattice.toEuc m) := by
    intro x
    obtain ⟨m, hm⟩ := tpos_centeredRep_eq x
    rw [hm]
    exact ENNReal.le_tsum (f := fun m : Lattice d => H (Torus.rep x + Lattice.toEuc m)) m
  have h2 : ∀ y : Euc d, ∑' m : Lattice d, H (Torus.rep (Torus.mk y) + Lattice.toEuc m) =
      ∑' m : Lattice d, H (y + Lattice.toEuc m) := by
    intro y
    obtain ⟨n, hn⟩ := Torus.rep_mk y
    rw [hn]
    calc ∑' m : Lattice d, H (y + Lattice.toEuc n + Lattice.toEuc m)
        = ∑' m : Lattice d, H (y + Lattice.toEuc (n + m)) :=
          tsum_congr fun m => by rw [ten_toEuc_add, add_assoc]
      _ = ∑' m : Lattice d, H (y + Lattice.toEuc m) :=
          (Equiv.addLeft n).tsum_eq (fun m : Lattice d => H (y + Lattice.toEuc m))
  have hmeas : Measurable fun x : Torus d => ∑' m : Lattice d, H (Torus.rep x + Lattice.toEuc m) :=
    Measurable.tsum fun m => hH.comp (tpos_measurable_rep.add_const _)
  calc ∫⁻ x : Torus d, H (KernelGrad.centeredRep x)
      ≤ ∫⁻ x : Torus d, ∑' m : Lattice d, H (Torus.rep x + Lattice.toEuc m) := lintegral_mono h1
    _ = ∫⁻ y in tposCell0 d, ∑' m : Lattice d, H (Torus.rep (Torus.mk y) + Lattice.toEuc m) :=
        tpos_torus_lintegral (fun x => ∑' m : Lattice d, H (Torus.rep x + Lattice.toEuc m))
    _ = ∫⁻ y in tposCell0 d, ∑' m : Lattice d, H (y + Lattice.toEuc m) := by
        refine lintegral_congr fun y => h2 y
    _ = ∑' m : Lattice d, ∫⁻ y in tposCell0 d, H (y + Lattice.toEuc m) := by
        rw [lintegral_tsum]
        intro m
        exact (hH.comp (measurable_id.add_const _)).aemeasurable
    _ = ∫⁻ y : Euc d, H y := (tpos_lintegral_unfold H).symm

/-- For `c` in the cube `[-1/2,1/2]^d` and `m ≠ 0`: `‖m‖ ≤ 2√d ‖c + m‖`. -/
theorem ten2_norm_le_of_cube {c : Euc d} (hc : ∀ i, |c i| ≤ 1 / 2) {m : Lattice d} (hm : m ≠ 0) :
    ‖Lattice.toEuc m‖ ≤ 2 * Real.sqrt d * ‖c + Lattice.toEuc m‖ := by
  set N := ‖c + Lattice.toEuc m‖ with hN
  have hcoord : ∀ i, |c i + (m i : ℝ)| ≤ N := by
    intro i
    have := PiLp.norm_apply_le (c + Lattice.toEuc m) i
    simpa [hN, Lattice.toEuc] using this
  obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (funext h)
  have hj1 : (1 : ℝ) ≤ |(m j : ℝ)| := by
    have : (1 : ℤ) ≤ |m j| := Int.one_le_abs hj
    exact_mod_cast this
  have hNhalf : 1 / 2 ≤ N := by
    have h1 : |(m j : ℝ)| ≤ |c j + (m j : ℝ)| + |c j| := by
      calc |(m j : ℝ)| = |(c j + (m j : ℝ)) - c j| := by ring_nf
        _ ≤ |c j + (m j : ℝ)| + |c j| := abs_sub _ _
    have := hcoord j
    have := hc j
    linarith
  have hcoord2 : ∀ i, |(m i : ℝ)| ≤ 2 * N := by
    intro i
    have h1 : |(m i : ℝ)| ≤ |c i + (m i : ℝ)| + |c i| := by
      calc |(m i : ℝ)| = |(c i + (m i : ℝ)) - c i| := by ring_nf
        _ ≤ |c i + (m i : ℝ)| + |c i| := abs_sub _ _
    have := hcoord i
    have := hc i
    linarith
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖(Lattice.toEuc m) i‖ ^ 2 ≤ (d : ℝ) * (2 * N) ^ 2 := by
    calc ∑ i, ‖(Lattice.toEuc m) i‖ ^ 2 ≤ ∑ _i : Fin d, (2 * N) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h0 : 0 ≤ ‖(Lattice.toEuc m) i‖ := norm_nonneg _
          have h3 : ‖(Lattice.toEuc m) i‖ ≤ 2 * N := by
            simpa [Lattice.toEuc, Real.norm_eq_abs] using hcoord2 i
          exact pow_le_pow_left₀ h0 h3 2
      _ = (d : ℝ) * (2 * N) ^ 2 := by simp
  calc Real.sqrt (∑ i, ‖(Lattice.toEuc m) i‖ ^ 2) ≤ Real.sqrt ((d : ℝ) * (2 * N) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = 2 * Real.sqrt d * N := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (by linarith)]
        ring

end HRS.Commutator.TorusNote
