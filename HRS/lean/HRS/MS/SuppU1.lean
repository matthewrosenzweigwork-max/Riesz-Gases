import HRS.Whole.Round2
import HRS.MS.SuppU1Aux9

/-!
# U1: proof of the supplement lemma S9.1 `HRS.Whole.round2_approximation`

Route (S L6826-6834): cut-off, mollification by a bump on `ℝ^d × ℝ^d` (the envelope constant comes from the
average of `W_s` over a small ball), Stone-Weierstrass for the finite-rank kernels (cut off again), symmetrisation;
the exponents `r_j ↑ d/s` handle all `r` at once.  The generic analysis is in `SuppU1Aux1`-`SuppU1Aux9`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.U1

variable {d : ℕ}

lemma u1_isProb {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) : IsProbabilityMeasure (withDensityReal ρ) := by
  have hint : Integrable ρ :=
    Integrable.of_integral_ne_zero (by rw [hρ.integral_one]; exact one_ne_zero)
  refine ⟨?_⟩
  unfold withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hρ.nonneg),
    hρ.integral_one]
  simp

lemma u1_le_smul {ρ : Euc d → ℝ} {M : ℝ} (hM : ∀ x, ρ x ≤ M) :
    withDensityReal ρ ≤ ENNReal.ofReal M • (volume : Measure (Euc d)) := by
  refine Measure.le_iff.2 fun s hs => ?_
  unfold withDensityReal
  rw [withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ x in s, ENNReal.ofReal (ρ x) ∂volume
      ≤ ∫⁻ x in s, ENNReal.ofReal M ∂volume := lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hM x)
    _ = ENNReal.ofReal M * volume s := by rw [setLIntegral_const, mul_comm]

lemma u1_rseq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) :
    ∃ rs : ℕ → ℝ, (∀ j, 1 ≤ rs j) ∧ (∀ j, rs j * s < (d : ℝ)) ∧
      ∀ r : ℝ, 1 ≤ r → r * s < (d : ℝ) → ∃ J : ℕ, ∀ j, J ≤ j → r ≤ rs j := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  by_cases h0 : s = 0
  · refine ⟨fun j => (j : ℝ) + 1, fun j => by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)],
      fun j => by rw [h0]; linarith, fun r _ _ => ?_⟩
    obtain ⟨J, hJ⟩ := exists_nat_ge r
    refine ⟨J, fun j hj => ?_⟩
    have : (J : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
    have hD : 2 < (d : ℝ) / s := by rw [lt_div_iff₀ hs']; linarith
    refine ⟨fun j => (d : ℝ) / s * (1 - 1 / ((j : ℝ) + 2)), ?_, ?_, ?_⟩
    · intro j
      have hq : 1 / ((j : ℝ) + 2) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)])
      have : (d : ℝ) / s * (1 / 2) ≤ (d : ℝ) / s * (1 - 1 / ((j : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    · intro j
      have hq : 0 < 1 / ((j : ℝ) + 2) := by positivity
      have : (d : ℝ) / s * (1 - 1 / ((j : ℝ) + 2)) * s = (d : ℝ) * (1 - 1 / ((j : ℝ) + 2)) := by
        field_simp
      rw [this]; nlinarith
    · intro r hr1 hrs
      have hδ : 0 < ((d : ℝ) - r * s) / d := by apply div_pos <;> linarith
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
      refine ⟨N, fun j hj => ?_⟩
      have hj' : (N : ℝ) ≤ j := by exact_mod_cast hj
      have hq : 1 / ((j : ℝ) + 2) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h2 : 1 / ((j : ℝ) + 2) < ((d : ℝ) - r * s) / d := lt_of_le_of_lt hq hN
      have h3 : (d : ℝ) * (1 / ((j : ℝ) + 2)) < (d : ℝ) - r * s := by
        have := (lt_div_iff₀ (by linarith : (0:ℝ) < d)).mp (by linarith [h2] : 1 / ((j : ℝ) + 2) < _)
        linarith
      have h4 : r * s ≤ (d : ℝ) * (1 - 1 / ((j : ℝ) + 2)) := by nlinarith
      have : (d : ℝ) / s * (1 - 1 / ((j : ℝ) + 2)) = (d : ℝ) * (1 - 1 / ((j : ℝ) + 2)) / s := by
        field_simp
      show r ≤ (d : ℝ) / s * (1 - 1 / ((j : ℝ) + 2))
      rw [this, le_div_iff₀ hs']
      exact h4

theorem round2_approximation_proof : type_of% @HRS.Whole.round2_approximation := by
  intro d hd s hs0 hs
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hfr : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  have hsd : s < (Module.finrank ℝ (Euc d) : ℝ) := by rw [hfr]; linarith
  obtain ⟨C, hC0, hCap⟩ := u1_approx (volume : Measure (Euc d)) hs0 hsd
  refine ⟨C, fun M L ρ hρ B h hh => ?_⟩
  haveI : IsProbabilityMeasure (withDensityReal ρ) := u1_isProb hρ.prob
  have hle := u1_le_smul (d := d) hρ.bdd
  have hV : ∀ z : Euc d, u1Vs s ‖z‖ = 1 + rieszWeight s z := fun z => rfl
  -- `B ≥ 0`
  haveI : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfr]; omega)
  obtain ⟨x0, y0, hxy0⟩ := exists_pair_ne (Euc d)
  have hB0 : 0 ≤ B := by
    have h1 := hh.bound x0 y0 hxy0
    have h2 : 0 < 1 + rieszWeight s (x0 - y0) := by
      rw [← hV]; linarith [u1Vs_ge_one (s := s) (norm_nonneg (x0 - y0))]
    have := (abs_nonneg (h x0 y0)).trans h1
    exact (mul_nonneg_iff_of_pos_right h2).mp this
  rcases hB0.eq_or_lt with hB | hBpos
  · -- `B = 0`: the kernel vanishes a.e.
    subst hB
    refine ⟨fun _ _ _ => 0, ?_⟩
    refine ⟨fun j => ⟨0, fun _ _ => 0, fun _ _ => 0, ⟨fun _ _ => rfl, fun a => a.elim0,
      fun a => a.elim0⟩, by funext x y; simp [r2FiniteRankKernel]⟩, fun j x y hxy => by simp, ?_⟩
    intro r hr hrs
    have hμ'μ : withDensityReal ρ ≪ (volume : Measure (Euc d)) :=
      Measure.absolutelyContinuous_of_le_smul hle
    have hPν : (withDensityReal ρ).prod (withDensityReal ρ) ≪ (volume : Measure (Euc d)).prod volume :=
      Measure.AbsolutelyContinuous.prod hμ'μ hμ'μ
    have hoff : ∀ᵐ q ∂((withDensityReal ρ).prod (withDensityReal ρ)), q.1 ≠ q.2 :=
      hPν.ae_le (u1_ae_offdiag (volume : Measure (Euc d)) (by rw [hfr]; omega))
    have hz : eLpNorm (fun p : Euc d × Euc d => (fun _ _ => (0 : ℝ)) p.1 p.2 - h p.1 p.2)
        (ENNReal.ofReal r) ((withDensityReal ρ).prod (withDensityReal ρ)) = 0 := by
      rw [← eLpNorm_zero (p := ENNReal.ofReal r) (μ := (withDensityReal ρ).prod (withDensityReal ρ))
        (ε := ℝ)]
      refine eLpNorm_congr_ae ?_
      filter_upwards [hoff] with q hq
      have := hh.bound q.1 q.2 hq
      have h0 : h q.1 q.2 = 0 := by
        have h1 : |h q.1 q.2| ≤ 0 := by simpa using this
        exact abs_nonpos_iff.mp h1
      simp [h0]
    simp only [hz]
    exact tendsto_const_nhds
  · obtain ⟨rs, hrs1, hrs2, hrs3⟩ := u1_rseq hd hs0 hs
    have hex : ∀ j : ℕ, ∃ (m : ℕ) (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ),
        (∀ a b, c a b = c b a) ∧ (∀ a, ContDiff ℝ ∞ (u a)) ∧ (∀ a, HasCompactSupport (u a)) ∧
        (∀ x y, x ≠ y → |∑ a, ∑ b, c a b * u a x * u b y| ≤ C * B * u1Vs s ‖x - y‖) ∧
        eLpNorm (fun p : Euc d × Euc d => (∑ a, ∑ b, c a b * u a p.1 * u b p.2) - h p.1 p.2)
          (ENNReal.ofReal (rs j)) ((withDensityReal ρ).prod (withDensityReal ρ))
            ≤ ENNReal.ofReal (1 / ((j : ℝ) + 1)) := fun j =>
      hCap M (withDensityReal ρ) hle B hBpos h hh.measurable hh.symm
        (fun x y hxy => by rw [hV]; exact hh.bound x y hxy) (rs j) (hrs1 j)
        (by rw [hfr]; exact hrs2 j) (1 / ((j : ℝ) + 1)) (by positivity)
    choose m c u hcs hsm hcp henv hL using hex
    refine ⟨fun j => r2FiniteRankKernel (c j) (u j), ?_, ?_, ?_⟩
    · intro j
      exact ⟨m j, c j, u j, ⟨hcs j, hsm j, hcp j⟩, rfl⟩
    · intro j x y hxy
      have := henv j x y hxy
      rw [hV] at this
      exact this
    · intro r hr hrs
      obtain ⟨J, hJ⟩ := hrs3 r hr hrs
      have hup : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
        have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        simpa using this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
        (Eventually.of_forall fun j => zero_le) ?_
      filter_upwards [eventually_ge_atTop J] with j hj
      refine le_trans ?_ (hL j)
      exact eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (hJ j hj))

end HRS.Whole.U1
