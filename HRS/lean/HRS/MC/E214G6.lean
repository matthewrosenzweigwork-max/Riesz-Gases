import HRS.MC.E214G5
import HRS.MC.E214G2
import HRS.MC.E214G1
import HRS.MC.L2C6c
import HRS.Equilibrium.FieldSingAux

/-!
# E214G6: the sorry-free path-supremum estimate for a coupled pair

`p4_pair_proof`: there is a coupled pair (the one of `exists_coupled_pair_inc_proof`) such that, for every horizon
`T > 0` and exponent `p ≥ 2`, the path supremum of `η - ηs` over `[a, a+T]` has `p`-th moment bounded by
`(C e^{-κ a})^p`, uniformly in `a ≥ 0`. The pair does not depend on `T`, `p`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214G

open HRS HRS.Sec7

variable {d : ℕ}

/-- Continuity on every `[0,n]` gives continuity on `[0,∞)` almost surely. -/
theorem ae_continuousOn_Ici_of_nat' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {E : Type*}
    [TopologicalSpace E] (f : ℝ → Ω → E)
    (h : ∀ n : ℕ, ∀ᵐ ω ∂P, ContinuousOn (fun t => f t ω) (Icc 0 (n : ℝ))) :
    ∀ᵐ ω ∂P, ContinuousOn (fun t => f t ω) (Ici 0) := by
  have h' : ∀ᵐ ω ∂P, ∀ n : ℕ, ContinuousOn (fun t => f t ω) (Icc 0 (n : ℝ)) :=
    ae_all_iff.2 h
  filter_upwards [h'] with ω hω
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_gt (t + 1)
  have hmem : Icc (0 : ℝ) n ∈ 𝓝[Ici 0] t := by
    rw [mem_nhdsWithin]
    exact ⟨Iio (n : ℝ), isOpen_Iio, by simp only [mem_Iio]; linarith,
      fun x hx => ⟨hx.2, (mem_Iio.1 hx.1).le⟩⟩
  exact ((hω n).continuousWithinAt ⟨ht, by simp only [mem_Ici] at ht; linarith⟩).mono_of_mem_nhdsWithin hmem

theorem p4_pair_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Y₀ Ys₀ : Ω → NegSobolev d r) (η ηs : ℝ → Ω → NegSobolev d r),
      IsCoupledPair R r P Y₀ Ys₀ η ηs ∧
      ∀ {T : ℝ}, 0 < T → ∀ {p : ℝ}, 2 ≤ p →
        ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ a : ℝ, 0 ≤ a →
          ∫⁻ ω, (⨆ t ∈ Icc (0 : ℝ) T, ‖η (a + t) ω - ηs (a + t) ω‖ₑ) ^ p ∂P ≤
            ENNReal.ofReal ((C * Real.exp (-κ * a)) ^ p) := by
  obtain ⟨Ω, mΩ, P, hP, Y₀, Ys₀, η, ηs, hpair, B, hB, hI⟩ := exists_coupled_pair_inc_proof R r hr
  refine ⟨Ω, mΩ, P, hP, Y₀, Ys₀, η, ηs, hpair, ?_⟩
  intro T hT p hp
  obtain ⟨C₀, c, hc, hD⟩ := HRS.MC.L2C6c.l2c6c_proof R r hr
  have hr1 : (d : ℝ) < 2 * r := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    rw [hr]; linarith
  have hsum : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r) := by
    have := summable_jp_rpow (d := d) (r / 2) (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      rw [hr]; linarith)
    refine this.congr fun k => ?_
    rw [show -(2 * (r / 2)) = -r by ring]
  have hjp1 : ∀ k : NonzeroLattice d, 1 ≤ Lattice.jp k.1 := fun k => by
    unfold Lattice.jp
    have : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * Lattice.enorm k.1 ^ 2 := by positivity
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  have hwAB : ∀ k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * r)) ≤ Lattice.jp k.1 ^ (-r) := fun k =>
    Real.rpow_le_rpow_of_exponent_le (hjp1 k) (by linarith)
  obtain ⟨C, κ, hC, hκ, hmain⟩ := p4_of_inputs_gen (d := d) (r := r) (A := max C₀ 1) (c := c) (B := B)
    (γ := 1 / 2) hr1 (fun k => Lattice.jp k.1 ^ (-r)) (fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _)
    hsum hwAB (by norm_num) (lt_max_of_lt_right one_pos) hc hB hT hp
  refine ⟨C, κ, hC, hκ, ?_⟩
  obtain ⟨-, -, -, hη, hηs, -⟩ := id hpair
  have hsm : ∀ k : NonzeroLattice d, Torus.IsSmooth (Torus.realMode k) :=
    HRS.FieldSingAux.isSmooth_realMode
  refine hmain P (fun t ω => η t ω - ηs t ω) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t; exact ((hη 0).meas t).sub ((hηs 0).meas t)
  · refine ae_continuousOn_Ici_of_nat' P _ fun n => ?_
    filter_upwards [(hη n).cont, (hηs n).cont] with ω h1 h2 using h1.sub h2
  · intro t ht k
    rw [show (∫ ω, NegSobolev.eval ((η t ω - ηs t ω)) (Torus.realMode k) ^ 2 ∂P) =
      ∫ ω, (NegSobolev.eval (η t ω) (Torus.realMode k) - NegSobolev.eval (ηs t ω) (Torus.realMode k)) ^ 2 ∂P from
      integral_congr_ae (ae_of_all _ fun ω => by simp only [HRS.MC.E214F.eval_realMode_sub])]
    obtain ⟨hY, hYs, hind, hS, hS', hN⟩ := hpair
    refine ((hD P Y₀ Ys₀ η ηs hY hYs hind hη hηs hN t ht _ (hsm k)).2).trans ?_
    rw [HRS.MC.E214F.l2NormSq_realMode, mul_one]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · exact fun s t hs ht h1 k => hI s t hs ht h1 k
  · exact fun t ht k => (pair_gaussian_proof R r P Y₀ Ys₀ η ηs hpair 0 t le_rfl ht k).1
  · exact fun t ht k => (pair_gaussian_proof R r P Y₀ Ys₀ η ηs hpair 0 t le_rfl ht k).2.1
  · exact fun s t hs ht k => (pair_gaussian_proof R r P Y₀ Ys₀ η ηs hpair s t hs ht k).2.2.1
  · exact fun s t hs ht k => (pair_gaussian_proof R r P Y₀ Ys₀ η ηs hpair s t hs ht k).2.2.2

end HRS.MC.E214G

end
