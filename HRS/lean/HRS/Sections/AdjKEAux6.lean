import HRS.Sections.AdjKEAux5

/-!
# ADJKE part 6: identification of the stochastic convolution by pairing (`adjk` version of `gf_pair_identification`)

If `Z_t` is the `L²`-limit of the Riemann sums of `∫ V^{t,r} dM_r` (`IsStochConv`) and `⟨Z_t, e_k⟩` is measurable, then
a.s. `⟨Z_t, e_k⟩ = √N ∫_0^t ∂_jU^{r,t}e_k(x_i(r)) dW'` (the empirical martingale with the time-dependent test `U^{·,t}e_k`).
This is `GF.gfb3_pair_identification_aem` outside `GeneralSetup`: `M` is any process with the smooth pairing property of B0,
`Vev` any dual evolution on `E_m`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q54c

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

open Classical in
lemma adjke_Xi_pointwise (D : DynData d) (N : ℕ) (c0 : ℝ) (hc0 : c0 = Real.sqrt N * Real.sqrt (2 * D.invβ))
    {Ω : Type*} (X : ℝ≥0 → Ω → Config d N) {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ} {n : ℕ}
    (hn : 1 ≤ n) {ε' δ' : ℝ}
    (huc : ∀ r ∈ Set.Icc 0 t, ∀ s ∈ Set.Icc 0 t, |r - s| < δ' → ∀ (x : Torus d) (j : Fin d),
      |Torus.partialDeriv j (f r) x - Torus.partialDeriv j (f s) x| < ε')
    (hstep : t / n < δ') {s : ℝ} (hs : s ∈ Set.Ioc 0 t) (ω : Ω) (k : Fin N × Fin d) :
    |(∑ i : Fin n, restrictFun (adjkeEta (c0 / N) X (f (gfb3_part t n i.castSucc)))
        (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) Set.univ s ω k) +
      (-(Real.sqrt N)) * empiricalNoiseIntegrand D t f X s ω k| ≤ |c0 / N| * ε' := by
  obtain ⟨i₀, hi₀⟩ := gfb3_part_cover ht hn hs
  have hsum : (∑ i : Fin n, restrictFun (adjkeEta (c0 / N) X (f (gfb3_part t n i.castSucc)))
        (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) Set.univ s ω k) =
      adjkeEta (c0 / N) X (f (gfb3_part t n i₀.castSucc)) s ω k := by
    rw [Finset.sum_eq_single i₀]
    · unfold restrictFun
      rw [if_pos ⟨trivial, hi₀⟩]
    · intro j _ hj
      unfold restrictFun
      rw [if_neg (fun h => gfb3_part_disjoint ht (Ne.symm hj) hi₀ h.2)]
      rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  have hE : empiricalNoiseIntegrand D t f X s ω k =
      (Real.sqrt (2 * D.invβ) / N) *
        Torus.partialDeriv k.2 (f s) (X (Real.toNNReal s) ω k.1) := by
    unfold empiricalNoiseIntegrand
    rw [if_pos ⟨hs.1.le, hs.2⟩, HRS.Commutator.StressAux.grad_apply]
  rw [hsum, hE]
  have hkey : adjkeEta (c0 / N) X (f (gfb3_part t n i₀.castSucc)) s ω k +
      (-(Real.sqrt N)) * ((Real.sqrt (2 * D.invβ) / N) *
        Torus.partialDeriv k.2 (f s) (X (Real.toNNReal s) ω k.1)) =
      (c0 / N) * (Torus.partialDeriv k.2 (f (gfb3_part t n i₀.castSucc))
          (X (Real.toNNReal s) ω k.1) -
        Torus.partialDeriv k.2 (f s) (X (Real.toNNReal s) ω k.1)) := by
    unfold adjkeEta
    rw [hc0]
    ring
  rw [hkey, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hab := gfb3_part_step (t := t) hn i₀
  have h0 : gfb3_part t n i₀.castSucc ∈ Set.Icc 0 t :=
    ⟨gfb3_part_nonneg ht _, gfb3_part_le ht hn _⟩
  refine (huc _ h0 s ⟨hs.1.le, hs.2⟩ ?_ _ _).le
  rw [abs_sub_comm, abs_of_nonneg (by linarith [hi₀.1])]
  linarith [hi₀.2]

lemma adjke_Xi_bound (D : DynData d) (N : ℕ) (c0 : ℝ) (hc0 : c0 = Real.sqrt N * Real.sqrt (2 * D.invβ))
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Config d N)
    {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ} {n : ℕ} (hn : 1 ≤ n) {ε' δ' : ℝ}
    (huc : ∀ r ∈ Set.Icc 0 t, ∀ s ∈ Set.Icc 0 t, |r - s| < δ' → ∀ (x : Torus d) (j : Fin d),
      |Torus.partialDeriv j (f r) x - Torus.partialDeriv j (f s) x| < ε')
    (hstep : t / n < δ') :
    sqIntegralOn P (fun s ω => (fun k => ∑ i : Fin n, restrictFun
        (adjkeEta (c0 / N) X (f (gfb3_part t n i.castSucc)))
        (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) Set.univ s ω k) +
      ((-(Real.sqrt N)) • empiricalNoiseIntegrand D t f X s ω)) t ≤
      ENNReal.ofReal t * (((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((c0 / N) ^ 2 * ε' ^ 2)) := by
  unfold sqIntegralOn
  have hpt : ∀ ω : Ω, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
      ∑ k : Fin N × Fin d, ‖((fun k => ∑ i : Fin n, restrictFun
        (adjkeEta (c0 / N) X (f (gfb3_part t n i.castSucc)))
        (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) Set.univ s ω k) +
        ((-(Real.sqrt N)) • empiricalNoiseIntegrand D t f X s ω)) k‖ₑ ^ 2 ≤
      ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((c0 / N) ^ 2 * ε' ^ 2) := by
    intro ω
    have h0 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), s ≠ 0 := by
      refine ae_restrict_of_ae ?_
      have := (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)
      filter_upwards [this] with s hs using hs
    filter_upwards [ae_restrict_mem measurableSet_Icc, h0] with s hs hs0
    have hs' : s ∈ Set.Ioc 0 t := ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2⟩
    calc ∑ k : Fin N × Fin d, ‖((fun k => ∑ i : Fin n, restrictFun
          (adjkeEta (c0 / N) X (f (gfb3_part t n i.castSucc)))
          (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) Set.univ s ω k) +
          ((-(Real.sqrt N)) • empiricalNoiseIntegrand D t f X s ω)) k‖ₑ ^ 2
        ≤ ∑ _k : Fin N × Fin d, ENNReal.ofReal ((c0 / N) ^ 2 * ε' ^ 2) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have h1 := adjke_Xi_pointwise D N c0 hc0 X ht (f := f) (ft := ft) hn huc hstep hs' ω k
          have h2 : ‖((fun k => ∑ i : Fin n, restrictFun
              (adjkeEta (c0 / N) X (f (gfb3_part t n i.castSucc)))
              (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) Set.univ s ω k) +
              ((-(Real.sqrt N)) • empiricalNoiseIntegrand D t f X s ω)) k‖ₑ =
              ENNReal.ofReal |(∑ i : Fin n, restrictFun
        (adjkeEta (c0 / N) X (f (gfb3_part t n i.castSucc)))
        (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) Set.univ s ω k) +
      (-(Real.sqrt N)) * empiricalNoiseIntegrand D t f X s ω k| := by
            rw [Real.enorm_eq_ofReal_abs]; rfl
          rw [h2, ← ENNReal.ofReal_pow (abs_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          calc _ ≤ (|c0 / N| * ε') ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
            _ = _ := by rw [mul_pow, sq_abs]
      _ = _ := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  calc ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t, ∑ k : Fin N × Fin d, ‖((fun k => ∑ i : Fin n, restrictFun
        (adjkeEta (c0 / N) X (f (gfb3_part t n i.castSucc)))
        (gfb3_part t n i.castSucc) (gfb3_part t n i.succ) Set.univ s ω k) +
        ((-(Real.sqrt N)) • empiricalNoiseIntegrand D t f X s ω)) k‖ₑ ^ 2) ∂P
      ≤ ∫⁻ _ω, (∫⁻ _s in Set.Icc (0 : ℝ) t,
          ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((c0 / N) ^ 2 * ε' ^ 2)) ∂P :=
        lintegral_mono fun ω => lintegral_mono_ae (hpt ω)
    _ = _ := by
        simp [lintegral_const, Real.volume_Icc, mul_comm, mul_left_comm]

lemma adjke_abs_eval_le {m : ℝ} (F : NegSobolev d m) {φ : Torus d → ℝ} (hφ : MemSobolev m φ) :
    |NegSobolev.eval F φ| ≤ ‖F‖ * sobolevNorm m φ := by
  rw [eval_lpFun F hφ]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (norm_lpFun_le m φ) (norm_nonneg _))

end HRS.AdjK
