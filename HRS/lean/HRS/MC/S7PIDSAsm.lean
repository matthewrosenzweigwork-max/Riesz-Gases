import HRS.MC.S7PIDSMain
import HRS.MC.S7PIDEMain

/-!
# Packet PI-D, sub-packet S (part 3): the final assembly `s7_PI_D_J_exists_assembly`

Statement copied verbatim from `HRS/MC/S7PIDPlan.lean` (= `HRS.MC.Sec7.s7_PI_D_J_exists`).  `IsJValue` is the membership in
`projTensor` and the norm bound of `s7_PID_series_proof`, together with the evaluation formula, which is the series form
of `s7_PID_series_proof` with each integrand summed by `s7_PID_expansion_proof` (with `z = z^u`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDS

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

/-- **s7_PI_D_J_exists_assembly_proof**: proof of `HRS.MC.Sec7.PIDPlan.s7_PI_D_J_exists_assembly` (statement verbatim). -/
theorem s7_PI_D_J_exists_assembly_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, ∀ (zr : ℝ → NegSobolev d r), Measurable zr → ∀ M : ℝ, (∀ u ∈ Set.Icc (0 : ℝ) T, ‖zr u‖ ≤ M) →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T →
      ∃ J : TensorDual (PathSpace d m T) 2,
        IsJValue R.D R.ρ m T (fun u => NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k))
          (Set.Ioc a b) J ∧ ‖J‖ ≤ C * M * (b - a) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hrm : r ≤ m := by rw [hr]; linarith
  obtain ⟨C, hC⟩ := s7_PID_series_proof R r hr m hm T hT
  refine ⟨C, fun zr hzr M hM a b ha hab hbT => ?_⟩
  obtain ⟨J, hJm, hJn, hJe⟩ := hC zr hzr M hM a b ha hab hbT
  refine ⟨J, ⟨hJm, ?_⟩, hJn⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  have h := hJe ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  unfold prodForm at h
  rw [h]
  congr 1
  refine setIntegral_congr_fun (measurableSet_Ioc.inter measurableSet_Icc) fun u hu => ?_
  beta_reduce
  have hu0 : 0 ≤ u := hu.2.1
  have hua : u ≤ ta := hu.2.2.trans (min_le_left _ _)
  have hub : u ≤ tb := hu.2.2.trans (min_le_right _ _)
  have hz : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) *
      NegSobolev.fourierCoeff
        (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) : NegSobolev d m) k) 2 := by
    refine (Torus.memℓp_two_iff _).2 ?_
    refine (HRS.MC.Sec7.PIE.pie_coeff_summable (zr u)).congr fun k => ?_
    rw [S7PIDS_fc_embed hrm (zr u) k]
  exact (HRS.MC.Sec7.S7PIDE.s7_PID_expansion_proof R r hr m hm T hT φa φb hφa hφb u ta tb hu0 hua hub
    hta.2 htb.2 _ hz).tsum_eq

end HRS.MC.Sec7.S7PIDS

end
