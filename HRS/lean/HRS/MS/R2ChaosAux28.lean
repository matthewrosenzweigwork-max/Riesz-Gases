import HRS.MS.R2ChaosAux27

/-!
# HRS.MS.R2ChaosAux28 -- R1: time-dependent finite-rank approximants of a jointly measurable kernel family

Packet S94 (R1, part 4), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_R1`: for a jointly measurable family `h_t` of `IsBoundedPairKernel s B` kernels (`t ∈ [0,T]`) there are finite-rank
kernels `r2FiniteRankKernel (Cm m t) (u m)` with fixed tests `u m` and Borel bounded symmetric coefficients `Cm m ·`, which for
EVERY `t ∈ [0,T]` form an `IsRound2Approx s C₁ B μ (h t)` (the constant `C₁` of S9.1 does not depend on `t`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

section R1

variable {s T : ℝ}

theorem s94_R1 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {M L B : ℝ} {ρ : Euc d → ℝ}
    (hρ : IsRound2Density d s M L ρ) (hT : 0 < T) {h : ℝ → Euc d → Euc d → ℝ}
    (hmeas : Measurable fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2)
    (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsBoundedPairKernel s B (h t)) :
    ∃ (C₁ : ℝ) (n : ℕ → ℕ) (u : ∀ m, Fin (n m) → Euc d → ℝ) (Cm : ∀ m, ℝ → Fin (n m) → Fin (n m) → ℝ),
      (∀ m a, IsR2Test (u m a)) ∧ (∀ m a b, Measurable fun t => Cm m t a b) ∧
      (∀ m, ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ t a b, |Cm m t a b| ≤ K0) ∧ (∀ m t a b, Cm m t a b = Cm m t b a) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, IsRound2Approx s C₁ B (Whole.withDensityReal ρ) (h t)
        (fun m => r2FiniteRankKernel (Cm m t) (u m)) := by
  classical
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨C₁, hC₁⟩ := HRS.Whole.U1.round2_approximation_proof hd s hs0 hs
  obtain ⟨τ, kk, hτ, hkkm, hkkle, hsel⟩ := s94_select (μ := Whole.withDensityReal ρ) hT hmeas
    (fun t ht => s94_env_memLp hd hs0 hs hρ (hker t ht))
  have hex : ∀ n, ∃ hj : ℕ → Euc d → Euc d → ℝ,
      IsRound2Approx s C₁ B (Whole.withDensityReal ρ) (h (τ n)) hj :=
    fun n => hC₁ M L ρ hρ B _ (hker (τ n) (hτ n))
  choose hj hA using hex
  obtain ⟨rs, hrs1, hrs2, hrs3⟩ := HRS.Whole.U1.u1_rseq hd hs0 hs
  have hJ : ∀ n m, ∃ J : ℕ, eLpNorm (fun q : Euc d × Euc d => hj n J q.1 q.2 - h (τ n) q.1 q.2)
      (ENNReal.ofReal (rs m)) ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ))
        ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
    intro n m
    have := (hA n).converges (rs m) (hrs1 m) (hrs2 m)
    have h2 := (ENNReal.tendsto_nhds_zero.1 this) (ENNReal.ofReal (1 / ((m : ℝ) + 1)))
      (ENNReal.ofReal_pos.2 (by positivity))
    exact h2.exists
  choose J hJ using hJ
  have hfr : ∀ n m, ∃ (k : ℕ) (c : Fin k → Fin k → ℝ) (u : Fin k → Euc d → ℝ),
      IsR2FiniteRankData c u ∧ hj n (J n m) = r2FiniteRankKernel c u :=
    fun n m => (hA n).finiteRank (J n m)
  choose sz c u hdat heq using hfr
  have hcat : ∀ m, ∃ (N : ℕ) (u' : Fin N → Euc d → ℝ) (c' : Fin (m + 1) → Fin N → Fin N → ℝ),
      (∀ a, IsR2Test (u' a)) ∧ (∀ n a b, c' n a b = c' n b a) ∧
      ∀ (n : Fin (m + 1)) x y, r2FiniteRankKernel (c' n) u' x y =
        r2FiniteRankKernel (c n.1 m) (u n.1 m) x y :=
    fun m => s94_concat (K := m + 1) (fun n => sz n.1 m) (fun n => c n.1 m) (fun n => u n.1 m)
      (fun n => (hdat n.1 m).symm) (fun n a => ⟨(hdat n.1 m).smooth a, (hdat n.1 m).compactSupport a⟩)
  choose N u' c' hu' hc'sym hc'ker using hcat
  let c'' : ∀ m, ℕ → Fin (N m) → Fin (N m) → ℝ := fun m n a b =>
    if hn : n < m + 1 then c' m ⟨n, hn⟩ a b else 0
  let Cm : ∀ m, ℝ → Fin (N m) → Fin (N m) → ℝ := fun m t a b => c'' m (kk m t) a b
  have hlt : ∀ m t, kk m t < m + 1 := fun m t => Nat.lt_succ_of_le (hkkle m t)
  have hC : ∀ m t, Cm m t = c' m ⟨kk m t, hlt m t⟩ := by
    intro m t; funext a b
    simp only [Cm, c'', dif_pos (hlt m t)]
  have hK : ∀ m t x y, r2FiniteRankKernel (Cm m t) (u' m) x y = hj (kk m t) (J (kk m t) m) x y := by
    intro m t x y
    rw [hC, hc'ker, ← heq]
  refine ⟨C₁, N, u', Cm, hu', ?_, ?_, ?_, ?_⟩
  · intro m a b
    exact (measurable_from_nat (f := fun n => c'' m n a b)).comp (hkkm m)
  · intro m
    refine ⟨∑ n : Fin (m + 1), ∑ a, ∑ b, |c' m n a b|, Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _, fun t a b => ?_⟩
    rw [show Cm m t a b = c' m ⟨kk m t, hlt m t⟩ a b from by rw [hC]]
    have h1 : |c' m ⟨kk m t, hlt m t⟩ a b| ≤ ∑ b', |c' m ⟨kk m t, hlt m t⟩ a b'| :=
      Finset.single_le_sum (f := fun b' => |c' m ⟨kk m t, hlt m t⟩ a b'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ b)
    have h2 : ∑ b', |c' m ⟨kk m t, hlt m t⟩ a b'| ≤ ∑ a', ∑ b', |c' m ⟨kk m t, hlt m t⟩ a' b'| :=
      Finset.single_le_sum (f := fun a' => ∑ b', |c' m ⟨kk m t, hlt m t⟩ a' b'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    have h3 : ∑ a', ∑ b', |c' m ⟨kk m t, hlt m t⟩ a' b'| ≤ ∑ n : Fin (m + 1), ∑ a', ∑ b', |c' m n a' b'| :=
      Finset.single_le_sum (f := fun n : Fin (m + 1) => ∑ a', ∑ b', |c' m n a' b'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ (⟨kk m t, hlt m t⟩ : Fin (m + 1)))
    exact h1.trans (h2.trans h3)
  · intro m t a b
    rw [show Cm m t a b = c' m ⟨kk m t, hlt m t⟩ a b from by rw [hC],
      show Cm m t b a = c' m ⟨kk m t, hlt m t⟩ b a from by rw [hC]]
    exact hc'sym m _ a b
  · intro t ht
    have hjmeas : ∀ n j, Measurable fun q : Euc d × Euc d => hj n j q.1 q.2 := by
      intro n j
      obtain ⟨k, c0, u0, hd0, he⟩ := (hA n).finiteRank j
      rw [he]
      exact s94_finiteRank_measurable (fun a => ⟨hd0.smooth a, hd0.compactSupport a⟩)
    refine ⟨fun m => ⟨N m, Cm m t, u' m, ⟨fun a b => ?_, fun a => (hu' m a).1, fun a => (hu' m a).2⟩, rfl⟩,
      fun m x y hxy => ?_, fun r hr hrs' => ?_⟩
    · rw [hC]; exact hc'sym m _ a b
    · rw [hK]; exact (hA (kk m t)).envelope (J (kk m t) m) x y hxy
    · set g : ℕ → Euc d → Euc d → ℝ := fun m => h (τ (kk m t)) with hg
      have hgB : ∀ m, IsBoundedPairKernel s B (g m) := fun m => hker (τ (kk m t)) (hτ _)
      have hup := s94_kernel_upgrade hd hs0 hs hρ (hker t ht) hgB (hsel t ht) hr hrs'
      obtain ⟨J0, hJ0⟩ := hrs3 r hr hrs'
      have hE1 : ∀ m, J0 ≤ m → eLpNorm (fun q : Euc d × Euc d => hj (kk m t) (J (kk m t) m) q.1 q.2 -
          h (τ (kk m t)) q.1 q.2) (ENNReal.ofReal r)
          ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
        intro m hm
        exact le_trans (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (hJ0 m hm)))
          (hJ (kk m t) m)
      have hup2 : Tendsto (fun m : ℕ => ENNReal.ofReal (1 / ((m : ℝ) + 1)) +
          eLpNorm (fun q : Euc d × Euc d => g m q.1 q.2 - h t q.1 q.2) (ENNReal.ofReal r)
            ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ))) atTop (𝓝 0) := by
        have h0 : Tendsto (fun m : ℕ => ENNReal.ofReal (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
          have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
          simpa using this
        simpa using h0.add hup
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup2
        (Eventually.of_forall fun m => bot_le) ?_
      refine Filter.eventually_atTop.2 ⟨J0, fun m hm => ?_⟩
      have hsplit : (fun q : Euc d × Euc d => r2FiniteRankKernel (Cm m t) (u' m) q.1 q.2 - h t q.1 q.2) =
          (fun q : Euc d × Euc d => hj (kk m t) (J (kk m t) m) q.1 q.2 - h (τ (kk m t)) q.1 q.2) +
          (fun q : Euc d × Euc d => g m q.1 q.2 - h t q.1 q.2) := by
        funext q
        simp only [Pi.add_apply, hK, hg]
        ring
      show eLpNorm (fun q : Euc d × Euc d => r2FiniteRankKernel (Cm m t) (u' m) q.1 q.2 - h t q.1 q.2)
        (ENNReal.ofReal r) _ ≤ _
      rw [hsplit]
      refine (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hr)).trans ?_
      exact add_le_add (hE1 m hm) le_rfl

end R1

end HRS.MS.R2Chaos
