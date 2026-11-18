import HRS.Main.GFB3Aux11

/-!
# Packet GFB3, part 12: `gf_pair_identification` (with the measurability hypothesis `hZm` that the statement lacks)

The packet statement `gf_pair_identification` has no measurability hypothesis on `Zt`; since `IsStochConv` is a statement about the
(lower) Lebesgue integral `∫⁻ ‖Z - R_π‖²`, it holds for `Z₀ + 1_A v` with `A` a non-measurable set of full outer measure and `v ∈ E_m`
with `⟨v, φ⟩ ≠ 0`, whereas the conclusion fails on `A`.  So the statement is false as written; here it is proved with the extra hypothesis
`hZm : AEMeasurable (fun ω => NegSobolev.eval (Zt ω) φ) P`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS HRS.Uniform HRS.Uniform.Q54c

variable {d : ℕ}

lemma gfb3_Xi_bound (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N)
    {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ} {n : ℕ} (hn : 1 ≤ n) {ε' δ' : ℝ}
    (huc : ∀ r ∈ Set.Icc 0 t, ∀ s ∈ Set.Icc 0 t, |r - s| < δ' → ∀ (x : Torus d) (j : Fin d),
      |Torus.partialDeriv j (f r) x - Torus.partialDeriv j (f s) x| < ε')
    (hstep : t / n < δ') :
    sqIntegralOn P (fun s ω => (fun k => ∑ i : Fin n, restrictFun
        (gfb3_eta S N X (f (gfb3_part t n i.castSucc)))
        (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) Set.univ s ω k) +
      ((-(sigN S N)) • empiricalNoiseIntegrand (S.dynM M N) t f X s ω)) t ≤
      ENNReal.ofReal t * (((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((noiseScale S N / N) ^ 2 * ε' ^ 2)) := by
  unfold sqIntegralOn
  have hpt : ∀ ω : Ω, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
      ∑ k : Fin N × Fin d, ‖((fun k => ∑ i : Fin n, restrictFun
        (gfb3_eta S N X (f (gfb3_part t n i.castSucc)))
        (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) Set.univ s ω k) +
        ((-(sigN S N)) • empiricalNoiseIntegrand (S.dynM M N) t f X s ω)) k‖ₑ ^ 2 ≤
      ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((noiseScale S N / N) ^ 2 * ε' ^ 2) := by
    intro ω
    have h0 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), s ≠ 0 := by
      refine ae_restrict_of_ae ?_
      have := (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)
      filter_upwards [this] with s hs using hs
    filter_upwards [ae_restrict_mem measurableSet_Icc, h0] with s hs hs0
    have hs' : s ∈ Set.Ioc 0 t := ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2⟩
    calc ∑ k : Fin N × Fin d, ‖((fun k => ∑ i : Fin n, restrictFun
          (gfb3_eta S N X (f (gfb3_part t n i.castSucc)))
          (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) Set.univ s ω k) +
          ((-(sigN S N)) • empiricalNoiseIntegrand (S.dynM M N) t f X s ω)) k‖ₑ ^ 2
        ≤ ∑ _k : Fin N × Fin d, ENNReal.ofReal ((noiseScale S N / N) ^ 2 * ε' ^ 2) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have h1 := gfb3_Xi_pointwise S M N X ht (f := f) (ft := ft) hn huc hstep hs' ω k
          have h2 : ‖((fun k => ∑ i : Fin n, restrictFun
              (gfb3_eta S N X (f (gfb3_part t n i.castSucc)))
              (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) Set.univ s ω k) +
              ((-(sigN S N)) • empiricalNoiseIntegrand (S.dynM M N) t f X s ω)) k‖ₑ =
              ENNReal.ofReal |(∑ i : Fin n, restrictFun
        (gfb3_eta S N X (f (gfb3_part t n i.castSucc)))
        (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) Set.univ s ω k) +
      (-(sigN S N)) * empiricalNoiseIntegrand (S.dynM M N) t f X s ω k| := by
            rw [Real.enorm_eq_ofReal_abs]; rfl
          rw [h2, ← ENNReal.ofReal_pow (abs_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          calc _ ≤ (|noiseScale S N / N| * ε') ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
            _ = _ := by rw [mul_pow, sq_abs]
      _ = _ := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  calc ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t, ∑ k : Fin N × Fin d, ‖((fun k => ∑ i : Fin n, restrictFun
        (gfb3_eta S N X (f (gfb3_part t n i.castSucc)))
        (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) Set.univ s ω k) +
        ((-(sigN S N)) • empiricalNoiseIntegrand (S.dynM M N) t f X s ω)) k‖ₑ ^ 2) ∂P
      ≤ ∫⁻ _ω, (∫⁻ _s in Set.Icc (0 : ℝ) t,
          ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((noiseScale S N / N) ^ 2 * ε' ^ 2)) ∂P :=
        lintegral_mono fun ω => lintegral_mono_ae (hpt ω)
    _ = _ := by
        simp [lintegral_const, Real.volume_Icc, mul_comm, mul_left_comm]

end HRS.GF
