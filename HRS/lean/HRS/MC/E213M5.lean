import HRS.MC.E213M4
import HRS.MC.S7PIDEMain

/-!
# Packet E213M5: translation-uniform PI-D (Theorem 2.13), the final family-quantified assembly

`s7_PI_D_J_exists_assembly_proof` with the constant `C` chosen before the shift `b ≥ 0`, for the density path
`fun t => R.ρ (b + t)` at the fixed horizon `G`.  (The original assembly statement has the same shape; only `∀ b ≥ 0`
and the shifted density are new.)  Proof: `E213M.e213m_series` and the expansion formula on `E213F.shift R b hb`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213M

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.S7PIDS

variable {d : ℕ}

theorem e213_PID_unif (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) :
    ∃ C : ℝ, ∀ b : ℝ, 0 ≤ b → ∀ (zr : ℝ → NegSobolev d r), Measurable zr → ∀ M : ℝ,
      (∀ u ∈ Set.Icc (0 : ℝ) G, ‖zr u‖ ≤ M) →
      ∀ a a' : ℝ, 0 ≤ a → a ≤ a' → a' ≤ G →
      ∃ J : TensorDual (PathSpace d m G) 2,
        IsJValue R.D (fun t => R.ρ (b + t)) m G
          (fun u => NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k))
          (Set.Ioc a a') J ∧ ‖J‖ ≤ C * M * (a' - a) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hrm : r ≤ m := by rw [hr]; linarith
  obtain ⟨C, hC⟩ := e213m_series R r hr m hm G hG
  refine ⟨C, fun b hb zr hzr M hM a a' ha haa' ha'G => ?_⟩
  obtain ⟨J, hJm, hJn, hJe⟩ := hC b hb zr hzr M hM a a' ha haa' ha'G
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
  exact (HRS.MC.Sec7.S7PIDE.s7_PID_expansion_proof (HRS.MC.E213F.shift R b hb) r hr m hm G hG φa φb hφa hφb
    u ta tb hu0 hua hub hta.2 htb.2 _ hz).tsum_eq

end HRS.MC.E213M

end
