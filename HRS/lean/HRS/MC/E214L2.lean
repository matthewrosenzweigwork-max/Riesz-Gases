import HRS.MC.E214PD
import HRS.MC.E214L1
import HRS.MC.E214G6
import HRS.MC.E214FDecay
import HRS.MC.L2C6c
import HRS.MC.QRPMarg
import HRS.MC.QRPGaussEr

/-!
# Packet E214L, part 2: `pair_fixed_time`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214L

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan

variable {d : ℕ}

section PairEstimates

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}
variable {sd : StatDatum S β₀ m hE}

theorem pair_fixed_time_proof (pg : PairGD sd) (p : ℝ) (hp : 1 ≤ p) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      eLpNorm (fun ω => ‖pg.η t ω - pg.ηs t ω‖) (ENNReal.ofReal p) pg.P ≤ ENNReal.ofReal (C * Real.exp (-c * t)) := by
  set R := regime S β₀ hE with hR
  obtain ⟨C₀, c, hc, hD⟩ := HRS.MC.L2C6c.l2c6c_proof R (rLvl d) rfl
  obtain ⟨Cg, hCg, hG⟩ := HRS.MC.QRSpec.GaussEr.qrs_gauss_er_proof p hp
  have hr1 : (d : ℝ) < 2 * (rLvl d) := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    show (d : ℝ) < 2 * (2 * (d : ℝ) + 6)
    linarith
  have hsum : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(2 * (rLvl d))) :=
    summable_jp_rpow (d := d) (rLvl d) hr1
  set Ssum : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (rLvl d))) with hSsum
  have hS0 : 0 ≤ Ssum := tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _
  set A : ℝ := max C₀ 1 with hA
  have hA1 : 1 ≤ A := le_max_right _ _
  refine ⟨Cg * Real.sqrt (A * Ssum) + 1, c / 2, by positivity, by positivity, ?_⟩
  intro t ht
  obtain ⟨hY, hYs, hind, hη, hηs, hN⟩ := pg.pair
  have hmarg := (HRS.MC.QRSpec.Marg.qrs_gauss_marginals_proof R (rLvl d) rfl pg.P pg.Y₀ pg.Ys₀ pg.η pg.ηs
    hY hYs hind hη hηs hN t ht).2.2
  have hmeas : Measurable (fun ω => pg.η t ω - pg.ηs t ω) :=
    ((hη 0).meas t).sub ((hηs 0).meas t)
  have hmom : ∀ k : NonzeroLattice d,
      ∫ ω, NegSobolev.fourierCoeff (pg.η t ω - pg.ηs t ω) k ^ 2 ∂pg.P ≤ A * Real.exp (-c * t) := by
    intro k
    have h1 : ∀ ω, NegSobolev.fourierCoeff (pg.η t ω - pg.ηs t ω) k =
        NegSobolev.eval (pg.η t ω) (Torus.realMode k) - NegSobolev.eval (pg.ηs t ω) (Torus.realMode k) := by
      intro ω
      rw [← HRS.MC.E214F.eval_realMode, HRS.MC.E214F.eval_realMode_sub]
    simp_rw [h1]
    refine ((hD pg.P pg.Y₀ pg.Ys₀ pg.η pg.ηs hY hYs hind hη hηs hN t ht _
      (HRS.FieldSingAux.isSmooth_realMode k)).2).trans ?_
    rw [HRS.MC.E214F.l2NormSq_realMode, mul_one]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  have hnn : ∀ k : NonzeroLattice d, 0 ≤ ∫ ω, NegSobolev.fourierCoeff (pg.η t ω - pg.ηs t ω) k ^ 2 ∂pg.P :=
    fun k => integral_nonneg fun ω => sq_nonneg _
  have hterm : ∀ k : NonzeroLattice d,
      Lattice.jp k.1 ^ (-(2 * (rLvl d))) * ∫ ω, NegSobolev.fourierCoeff (pg.η t ω - pg.ηs t ω) k ^ 2 ∂pg.P ≤
        (A * Real.exp (-c * t)) * Lattice.jp k.1 ^ (-(2 * (rLvl d))) := fun k => by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hmom k) (Real.rpow_nonneg (Torus.jp_pos k.1).le _)
  have hsum2 : Summable fun k : NonzeroLattice d =>
      Lattice.jp k.1 ^ (-(2 * (rLvl d))) * ∫ ω, NegSobolev.fourierCoeff (pg.η t ω - pg.ηs t ω) k ^ 2 ∂pg.P :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos k.1).le _) (hnn k)) hterm
      (hsum.mul_left _)
  have htsum : ∑' k : NonzeroLattice d,
      Lattice.jp k.1 ^ (-(2 * (rLvl d))) * ∫ ω, NegSobolev.fourierCoeff (pg.η t ω - pg.ηs t ω) k ^ 2 ∂pg.P ≤
        (A * Real.exp (-c * t)) * Ssum := by
    calc _ ≤ ∑' k : NonzeroLattice d, (A * Real.exp (-c * t)) * Lattice.jp k.1 ^ (-(2 * (rLvl d))) :=
          hsum2.tsum_le_tsum hterm (hsum.mul_left _)
      _ = _ := by rw [tsum_mul_left]
  have hneg : (-2 * rLvl d : ℝ) = -(2 * rLvl d) := by ring
  have key := hG d (rLvl d) pg.P (fun ω => pg.η t ω - pg.ηs t ω) hmeas hmarg (by rw [hneg]; exact hsum2)
  rw [hneg] at key
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsq : Real.sqrt (∑' k : NonzeroLattice d,
      Lattice.jp k.1 ^ (-(2 * (rLvl d))) * ∫ ω, NegSobolev.fourierCoeff (pg.η t ω - pg.ηs t ω) k ^ 2 ∂pg.P) ≤
      Real.sqrt (A * Ssum) * Real.exp (-(c / 2) * t) := by
    refine (Real.sqrt_le_sqrt htsum).trans ?_
    rw [show (A * Real.exp (-c * t)) * Ssum = (A * Ssum) * Real.exp (-c * t) by ring,
      Real.sqrt_mul (by positivity)]
    refine le_of_eq ?_
    congr 1
    have h2 : Real.exp (-c * t) = Real.exp (-(c / 2) * t) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h2, Real.sqrt_sq (Real.exp_pos _).le]
  have hexp : 0 < Real.exp (-(c / 2) * t) := Real.exp_pos _
  calc Cg * Real.sqrt _ ≤ Cg * (Real.sqrt (A * Ssum) * Real.exp (-(c / 2) * t)) :=
        mul_le_mul_of_nonneg_left hsq hCg.le
    _ ≤ (Cg * Real.sqrt (A * Ssum) + 1) * Real.exp (-(c / 2) * t) := by
        nlinarith [Real.sqrt_nonneg (A * Ssum), hexp]

end PairEstimates

end HRS.MC.E214L

end
