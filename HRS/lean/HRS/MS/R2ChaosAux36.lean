import HRS.MS.R2ChaosAux35

/-!
# HRS.MS.R2ChaosAux36 -- the quadratic process is a.s. in `L²(dt)` also for `N = 0, 1`

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

For `N = 0` the process vanishes; for `N = 1` the pair energy has no pair sum and equals `-H(x_1) + ½ ∫ H dμ` (`H(x) = ∫ h(x,y) dμ(y)`),
bounded by `2 c B` uniformly (`wr14a_Hc_bound`).  Together with `s94_quad_ae_memLp` (`N ≥ 2`) this gives the hypothesis `hae`
of `s94_part_ii` for every `N`.
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

section Small

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ}

theorem s94_pE_one_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hρ : IsRound2Density d s M L ρ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {B : ℝ}, 0 ≤ B → ∀ {k : Euc d → Euc d → ℝ}, IsBoundedPairKernel s B k →
      ∀ Z : EucConfig d 1, |pairEnergy k Z (Whole.withDensityReal ρ)| ≤ 2 * (c * B) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < (d : ℝ) := by linarith
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  have hle : Whole.withDensityReal ρ ≤ ENNReal.ofReal 1 • Whole.withDensityReal ρ := by simp
  obtain ⟨c, hc0, hc⟩ := HRS.MS.Wr.wr14a_Hc_bound (d := d) (by omega) hs0 hsd M
  refine ⟨c, hc0, fun {B} hB {k} hk Z => ?_⟩
  have hH : ∀ x, |HRS.MS.Wr.wr14a_Hc k (Whole.withDensityReal ρ) x| ≤ c * 1 * B := fun x =>
    hc hρ.prob hρ.bdd hle zero_le_one hB (fun x y hxy => hk.bound x y hxy) x
  have hI : |∫ x, HRS.MS.Wr.wr14a_Hc k (Whole.withDensityReal ρ) x ∂(Whole.withDensityReal ρ)| ≤ c * 1 * B := by
    have := norm_integral_le_of_norm_le_const (μ := Whole.withDensityReal ρ)
      (f := HRS.MS.Wr.wr14a_Hc k (Whole.withDensityReal ρ)) (C := c * 1 * B)
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hH x)
    simpa [Real.norm_eq_abs] using this
  have e : pairEnergy k Z (Whole.withDensityReal ρ) = -(HRS.MS.Wr.wr14a_Hc k (Whole.withDensityReal ρ) (Z 0)) +
      (1 / 2) * ∫ x, HRS.MS.Wr.wr14a_Hc k (Whole.withDensityReal ρ) x ∂(Whole.withDensityReal ρ) := by
    simp [pairEnergy, HRS.MS.Wr.wr14a_Hc]
  rw [e]
  have h1 := hH (Z 0)
  have h2 : |(1 / 2 : ℝ) * ∫ x, HRS.MS.Wr.wr14a_Hc k (Whole.withDensityReal ρ) x ∂(Whole.withDensityReal ρ)| ≤
      c * 1 * B := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have : 0 ≤ c * 1 * B := by positivity
    linarith
  calc _ ≤ |-(HRS.MS.Wr.wr14a_Hc k (Whole.withDensityReal ρ) (Z 0))| +
        |(1 / 2 : ℝ) * ∫ x, HRS.MS.Wr.wr14a_Hc k (Whole.withDensityReal ρ) x ∂(Whole.withDensityReal ρ)| :=
        abs_add_le _ _
    _ ≤ _ := by rw [abs_neg]; linarith

end Small

section SmallAll

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

/-- The hypothesis `hae` of `s94_part_ii`: for every `N`, the quadratic process is a.s. in `L²(dt)`. -/
theorem s94_quad_ae_memLp_all (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) (hT : 0 < T) {B : ℝ}
    {h : ℝ → Euc d → Euc d → ℝ} (hmeas : Measurable fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2)
    (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsBoundedPairKernel s B (h t)) (N : ℕ) :
    ∀ᵐ ζ ∂(P N), MemLp (fun t => r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · refine ae_of_all _ fun ζ => ?_
    interval_cases N
    · have : (fun t => r2QuadFluct (Whole.withDensityReal ρ) h (P 0) (X 0) t ζ) = fun _ => 0 := by
        funext t; simp [r2QuadFluct]
      rw [this]
      exact MemLp.zero
    · haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
      have hB : 0 ≤ B := s94_B_nonneg hd (hker 0 ⟨le_rfl, hT.le⟩)
      obtain ⟨c, hc0, hc⟩ := s94_pE_one_bound hd hs0 hs hρ
      have hQ := s94_quad_measurable (μ := Whole.withDensityReal ρ) (P := P 1) hmeas (X 1) (hset.measX 1)
      have hQt : Measurable (fun t : ℝ => r2QuadFluct (Whole.withDensityReal ρ) h (P 1) (X 1) t ζ) :=
        Measurable.comp (g := fun q : ℝ × Ω 1 => r2QuadFluct (Whole.withDensityReal ρ) h (P 1) (X 1) q.1 q.2)
          (f := fun t : ℝ => (t, ζ)) hQ (measurable_id.prodMk measurable_const)
      refine s94_memLp_of_bdd (T := T) (K := 4 * (c * B)) hQt fun t ht => ?_
      have h1 := hc hB (hker t ht) (X 1 t.toNNReal ζ)
      have h2 : |∫ ζ', pairEnergy (h t) (X 1 t.toNNReal ζ') (Whole.withDensityReal ρ) ∂(P 1)| ≤ 2 * (c * B) := by
        have := norm_integral_le_of_norm_le_const (μ := P 1)
          (f := fun ζ' => pairEnergy (h t) (X 1 t.toNNReal ζ') (Whole.withDensityReal ρ)) (C := 2 * (c * B))
          (ae_of_all _ fun ζ' => by simpa [Real.norm_eq_abs] using hc hB (hker t ht) (X 1 t.toNNReal ζ'))
        simpa [Real.norm_eq_abs] using this
      show |r2QuadFluct (Whole.withDensityReal ρ) h (P 1) (X 1) t ζ| ≤ 4 * (c * B)
      unfold r2QuadFluct
      rw [Nat.cast_one, one_mul]
      calc _ ≤ |pairEnergy (h t) (X 1 t.toNNReal ζ) (Whole.withDensityReal ρ)| +
          |∫ ζ', pairEnergy (h t) (X 1 t.toNNReal ζ') (Whole.withDensityReal ρ) ∂(P 1)| := abs_sub _ _
        _ ≤ _ := by linarith
  · exact s94_quad_ae_memLp hd hs0 hs hb hp hρ hset (B' := B) (kf := h) hmeas hker hN

end SmallAll

end HRS.MS.R2Chaos
