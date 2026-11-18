import HRS.Uniform.RelativeCoupling

/-!
# Q48a, part 1: the abstract representation data on the whole half-line (horizon `⊤`)

`⊤`-copy of `HRS/Prob/MRepAux5.lean` and `HRS/Prob/MRepAux6.lean` (the data `ARData`, the noise factorisation `vz`, the
approximability of the Brownian integrands) with the cut-off `r ≤ T` removed: the covariation densities are integrable
locally (`∫ r in Icc 0 t` for every `t`), not on one fixed window.
-/

noncomputable section

open HRS HRS.MRep
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q48a

section AR
open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]

/-- The data of the abstract representation theorem on the whole half-line. -/
structure ARTop (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (e : HilbertBasis ι ℝ H)
    (Mt : ℝ → Ω → H) (Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ) (S : ℝ → Ω → H →L[ℝ] H)
    (W : ℝ≥0 → Ω → ι → ℝ) : Prop where
  complete : IsCompleteFiltration P ℱ
  cont : ∀ ω, Continuous fun t => Mt t ω
  adapted : ∀ t, Measurable[ℱ t] (Mt t)
  zero : ∀ t ≤ 0, ∀ ω, Mt t ω = 0
  sq : ∀ t x, MemLp (fun ω => inner ℝ (Mt t ω) x) 2 P
  mart : ∀ x, Martingale (fun t ω => inner ℝ (Mt t ω) x) ℱ P
  cov : ∀ x y, Martingale (fun t ω => inner ℝ (Mt t ω) x * inner ℝ (Mt t ω) y -
    ∫ r in Set.Icc 0 t, Ct r ω x y) ℱ P
  wiener : IsCylindricalBrownian P ℱ W
  cross : ∀ x j, Martingale (fun t ω => inner ℝ (Mt t ω) x * ofNNRealTime W t ω j) ℱ P
  trace : ∀ r ω, IsTraceClassCov (Ct r ω)
  sqrt : ∀ r ω, IsSqrtOfForm (S r ω) (Ct r ω)
  Cprog : ∀ x y, IsProgressive ℱ (fun r ω => Ct r ω x y)
  Sprog : ∀ x y, IsProgressive ℱ (fun r ω => inner ℝ (S r ω x) y)
  Cint : ∀ᵐ ω ∂P, ∀ i j (t : ℝ), IntegrableOn (fun r => Ct r ω (e i) (e j)) (Set.Icc 0 t)
  Ctr : ∀ t : ℝ, ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (∑' i, Ct r ω (e i) (e i))) ∂P ≠ ∞

/-- The factorisation of the covariation densities through `K = ℓ²(H × H)`. -/
def vzT (e : HilbertBasis ι ℝ H) (S : ℝ → Ω → H →L[ℝ] H) :
    ℝ → Ω → ι ⊕ ι → WithLp 2 (H × H) :=
  fun r ω a => Sum.elim (fun i => WithLp.toLp 2 (S r ω (e i), (0 : H)))
    (fun j => WithLp.toLp 2 ((0 : H), e j)) a

lemma inner_vzT_ll (e : HilbertBasis ι ℝ H) (S : ℝ → Ω → H →L[ℝ] H) (r : ℝ) (ω : Ω)
    (i j : ι) : inner ℝ (vzT e S r ω (Sum.inl i)) (vzT e S r ω (Sum.inl j)) =
      inner ℝ (S r ω (e i)) (S r ω (e j)) := by
  simp [vzT, WithLp.prod_inner_apply]

lemma inner_vzT_rr (e : HilbertBasis ι ℝ H) (S : ℝ → Ω → H →L[ℝ] H) (r : ℝ) (ω : Ω)
    (i j : ι) : inner ℝ (vzT e S r ω (Sum.inr i)) (vzT e S r ω (Sum.inr j)) =
      if i = j then 1 else 0 := by
  simp only [vzT, Sum.elim_inr, WithLp.prod_inner_apply, inner_zero_left, zero_add]
  exact orthonormal_iff_ite.1 e.orthonormal i j

lemma inner_vzT_lr (e : HilbertBasis ι ℝ H) (S : ℝ → Ω → H →L[ℝ] H) (r : ℝ) (ω : Ω)
    (i j : ι) : inner ℝ (vzT e S r ω (Sum.inl i)) (vzT e S r ω (Sum.inr j)) = 0 := by
  simp [vzT, WithLp.prod_inner_apply]

lemma inner_vzT_rl (e : HilbertBasis ι ℝ H) (S : ℝ → Ω → H →L[ℝ] H) (r : ℝ) (ω : Ω)
    (i j : ι) : inner ℝ (vzT e S r ω (Sum.inr j)) (vzT e S r ω (Sum.inl i)) = 0 := by
  rw [real_inner_comm]; exact inner_vzT_lr e S r ω i j

section NoiseK

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {e : HilbertBasis ι ℝ H}
  {Mt : ℝ → Ω → H} {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ} {S : ℝ → Ω → H →L[ℝ] H}
  {W : ℝ≥0 → Ω → ι → ℝ}

lemma ARTop.measurable_S_apply (hA : ARTop P ℱ e Mt Ct S W) (x : H) :
    Measurable fun p : ℝ × Ω => S p.1 p.2 x := by
  refine measurable_of_inner_basis e (fun j => ?_)
  have : (fun p : ℝ × Ω => inner ℝ (e j) (S p.1 p.2 x)) = fun p => inner ℝ (S p.1 p.2 x) (e j) := by
    funext p; exact real_inner_comm _ _
  rw [this]
  exact isProgressive_measurable_uncurry (hA.Sprog x (e j))

lemma ARTop.measurable_vz (hA : ARTop P ℱ e Mt Ct S W) (a : ι ⊕ ι) :
    Measurable fun p : ℝ × Ω => vzT e S p.1 p.2 a := by
  rcases a with i | j
  · exact (WithLp.measurable_toLp 2 (H × H)).comp ((hA.measurable_S_apply (e i)).prodMk measurable_const)
  · exact measurable_const

theorem ARTop.isNoiseK (hA : ARTop P ℱ e Mt Ct S W) :
    IsNoiseK P ℱ (Nz e Mt W) (vzT e S) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hA.measurable_vz⟩
  · intro a
    rcases a with i | j
    · exact hA.mart (e i)
    · exact hA.wiener.martingale_coord j
  · intro ω a
    rcases a with i | j
    · exact (hA.cont ω).inner continuous_const
    · exact (hA.wiener {j} |>.cont ω |> fun h => (continuous_apply (⟨j, by simp⟩ :
        ({j} : Finset ι))).comp h |> fun h' => h'.comp continuous_real_toNNReal)
  · intro t a
    rcases a with i | j
    · exact hA.sq t (e i)
    · exact (hA.wiener {j}).memLp_two_coord_real t ⟨j, by simp⟩
  · intro a b
    exact meas_inner (hA.measurable_vz a) (hA.measurable_vz b)
  · -- Qint
    filter_upwards [hA.Cint] with ω hω a b t
    rcases a with i | j <;> rcases b with i' | j'
    · have e1 : (fun r => inner ℝ (vzT e S r ω (Sum.inl i)) (vzT e S r ω (Sum.inl i'))) =
          fun r => Ct r ω (e i) (e i') := by
        funext r
        rw [inner_vzT_ll, (hA.sqrt r ω).sq]
      rw [e1]
      exact hω i i' t
    · simp only [inner_vzT_lr, integrableOn_zero]
    · simp only [inner_vzT_rl, integrableOn_zero]
    · simp only [inner_vzT_rr]
      exact integrableOn_const (by simp)
  · -- cov
    intro a b
    rcases a with i | j <;> rcases b with i' | j'
    · have e2 : (fun t ω => Nz e Mt W t ω (Sum.inl i) * Nz e Mt W t ω (Sum.inl i') -
          ∫ r in Set.Icc 0 t, inner ℝ (vzT e S r ω (Sum.inl i)) (vzT e S r ω (Sum.inl i'))) =
          fun t ω => inner ℝ (Mt t ω) (e i) * inner ℝ (Mt t ω) (e i') -
          ∫ r in Set.Icc 0 t, Ct r ω (e i) (e i') := by
        funext t ω
        simp only [Nz, Sum.elim_inl]
        congr 1
        exact setIntegral_congr_fun measurableSet_Icc fun r _ => by
          rw [inner_vzT_ll, (hA.sqrt r ω).sq]
      rw [e2]
      exact hA.cov _ _
    · have e2 : (fun t ω => Nz e Mt W t ω (Sum.inl i) * Nz e Mt W t ω (Sum.inr j') -
          ∫ r in Set.Icc 0 t, inner ℝ (vzT e S r ω (Sum.inl i)) (vzT e S r ω (Sum.inr j'))) =
          fun t ω => inner ℝ (Mt t ω) (e i) * ofNNRealTime W t ω j' := by
        funext t ω
        simp only [Nz, Sum.elim_inl, Sum.elim_inr, inner_vzT_lr, integral_zero, sub_zero]
      rw [e2]
      exact hA.cross _ _
    · have e2 : (fun t ω => Nz e Mt W t ω (Sum.inr j) * Nz e Mt W t ω (Sum.inl i') -
          ∫ r in Set.Icc 0 t, inner ℝ (vzT e S r ω (Sum.inr j)) (vzT e S r ω (Sum.inl i'))) =
          fun t ω => inner ℝ (Mt t ω) (e i') * ofNNRealTime W t ω j := by
        funext t ω
        simp only [Nz, Sum.elim_inl, Sum.elim_inr, inner_vzT_rl, integral_zero, sub_zero]
        ring
      rw [e2]
      exact hA.cross _ _
    · have e2 : (fun t ω => Nz e Mt W t ω (Sum.inr j) * Nz e Mt W t ω (Sum.inr j') -
          ∫ r in Set.Icc 0 t, inner ℝ (vzT e S r ω (Sum.inr j)) (vzT e S r ω (Sum.inr j'))) =
          fun t ω => ofNNRealTime W t ω j * ofNNRealTime W t ω j' -
            if j = j' then max t 0 else 0 := by
        funext t ω
        simp only [Nz, Sum.elim_inr, inner_vzT_rr]
        by_cases h : j = j'
        · simp [h, Real.volume_real_Icc]
        · simp [h]
      rw [e2]
      exact hA.wiener.martingale_mul_sub j j'

end NoiseK

end AR

/-! ### Approximability of the Brownian integrands -/

section Gk
open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]

section Defs

/-- The limiting integrand of the `k`-th Brownian coordinate. -/
def GkT (e : HilbertBasis ι ℝ H) (Q : ℝ → Ω → H →L[ℝ] H) (k : ι) :
    ℝ → Ω → WithLp 2 (H × H) :=
  fun r ω => WithLp.toLp 2 (Q r ω (e k), e k - Q r ω (e k))

/-- The regularised integrand. -/
def GnT (e : HilbertBasis ι ℝ H) (S : ℝ → Ω → H →L[ℝ] H) (n : ℕ) (k : ι) :
    ℝ → Ω → WithLp 2 (H × H) :=
  fun r ω => WithLp.toLp 2 (e k - epsn n • resolvent (S r ω) n (e k),
    epsn n • resolvent (S r ω) n (e k))

/-- The second component of the regularised integrand. -/
def psinT (e : HilbertBasis ι ℝ H) (S : ℝ → Ω → H →L[ℝ] H) (n : ℕ) (k : ι) :
    ℝ → Ω → H :=
  fun r ω => epsn n • resolvent (S r ω) n (e k)

/-- The coefficients of the regularised integrand in the noise coordinates. -/
def ThnT (e : HilbertBasis ι ℝ H) (S : ℝ → Ω → H →L[ℝ] H) (n : ℕ) (k : ι) :
    ℝ → Ω → ι ⊕ ι → ℝ :=
  fun r ω a => Sum.elim (fun i => inner ℝ (e i) (resolvent (S r ω) n (e k)))
    (fun j => inner ℝ (e j) (psinT e S n k r ω)) a

/-- The finite-coordinate truncation. -/
def GFT (e : HilbertBasis ι ℝ H) (S : ℝ → Ω → H →L[ℝ] H) (n : ℕ) (k : ι) (F : Finset ι) :
    ℝ → Ω → WithLp 2 (H × H) :=
  fun r ω => ∑ a : ↥(F.disjSum F), ThnT e S n k r ω a.1 • vzT e S r ω a.1

lemma GFT_eq (e : HilbertBasis ι ℝ H) (S : ℝ → Ω → H →L[ℝ] H) (n : ℕ) (k : ι) (F : Finset ι)
    (r : ℝ) (ω : Ω) :
    GFT e S n k F r ω = WithLp.toLp 2
      (S r ω (∑ i ∈ F, inner ℝ (e i) (resolvent (S r ω) n (e k)) • e i),
        ∑ j ∈ F, inner ℝ (e j) (psinT e S n k r ω) • e j) := by
  unfold GFT
  rw [Finset.sum_coe_sort (F.disjSum F) (fun a => ThnT e S n k r ω a • vzT e S r ω a),
    Finset.sum_disjSum]
  apply WithLp.ofLp_injective
  simp [ThnT, vzT, Prod.ext_iff, map_sum, Prod.fst_sum, Prod.snd_sum]

end Defs

section StageF

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {e : HilbertBasis ι ℝ H}
  {Mt : ℝ → Ω → H} {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ} {S : ℝ → Ω → H →L[ℝ] H}
  {W : ℝ≥0 → Ω → ι → ℝ}

/-- The dominating function `√tr`. -/
def dST (e : HilbertBasis ι ℝ H) (Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ) : ℝ × Ω → ℝ :=
  fun p => Real.sqrt (trf e Ct p)

lemma ARTop.norm_S_le (hA : ARTop P ℱ e Mt Ct S W) (r : ℝ) (ω : Ω) (x : H) :
    ‖S r ω x‖ ≤ Real.sqrt (trf e Ct (r, ω)) * ‖x‖ := by
  obtain ⟨Tr, hT, hb⟩ := (hA.trace r ω).hasSum_basis e
  have h1 : ‖S r ω x‖ ^ 2 ≤ Tr * ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, (hA.sqrt r ω).sq x x]
    exact hb x
  have h2 : trf e Ct (r, ω) = Tr := hT.tsum_eq
  have hTr0 : 0 ≤ Tr := hT.nonneg (fun i => (hA.trace r ω).nonneg _)
  rw [h2]
  calc ‖S r ω x‖ = Real.sqrt (‖S r ω x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (Tr * ‖x‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt Tr * ‖x‖ := by rw [Real.sqrt_mul hTr0, Real.sqrt_sq (norm_nonneg _)]

lemma ARTop.measurable_trf (hA : ARTop P ℱ e Mt Ct S W) : Measurable (trf e Ct) :=
  Measurable.tsum fun i => isProgressive_measurable_uncurry (hA.Cprog (e i) (e i))

lemma ARTop.measurable_dS (hA : ARTop P ℱ e Mt Ct S W) : Measurable (dST e Ct) := by
  unfold dST
  exact hA.measurable_trf.sqrt

lemma ARTop.eLpNorm_dS (hA : ARTop P ℱ e Mt Ct S W) (t : ℝ) :
    eLpNorm (dST e Ct) 2 (tsm P t) ≠ ∞ := by
  have hm := hA.measurable_dS
  have h1 : eLpNorm (dST e Ct) 2 (tsm P t) ^ 2 = ∫⁻ p, ‖dST e Ct p‖ₑ ^ 2 ∂(tsm P t) :=
    (HRS.lintegral_enorm_sq_eq_eLpNorm_sq hm.aestronglyMeasurable).symm
  have h2 : ∀ p, ‖dST e Ct p‖ₑ ^ 2 = ENNReal.ofReal (trf e Ct p) := by
    intro p
    have hnn : 0 ≤ trf e Ct p := tsum_nonneg fun i => (hA.trace p.1 p.2).nonneg _
    simp only [dST]
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_of_nonneg
      (Real.sqrt_nonneg _), Real.sq_sqrt hnn]
  have h3 : ∫⁻ p, ‖dST e Ct p‖ₑ ^ 2 ∂(tsm P t) ≠ ∞ := by
    simp_rw [h2]
    unfold tsm
    have hmeas : Measurable fun p : ℝ × Ω => ENNReal.ofReal (trf e Ct p) :=
      ENNReal.measurable_ofReal.comp hA.measurable_trf
    rw [lintegral_prod_symm' _ hmeas]
    exact hA.Ctr t
  intro htop
  rw [htop] at h1
  simp at h1
  exact h3 h1.symm

end StageF

section ApproxGn

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {e : HilbertBasis ι ℝ H}
  {Mt : ℝ → Ω → H} {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ} {S : ℝ → Ω → H →L[ℝ] H}
  {W : ℝ≥0 → Ω → ι → ℝ}

lemma ARTop.psd (hA : ARTop P ℱ e Mt Ct S W) (r : ℝ) (ω : Ω) :
    HilbertCLTAux.IsPSDOp (S r ω) := ⟨(hA.sqrt r ω).symm, (hA.sqrt r ω).nonneg⟩

lemma ARTop.measurable_resolvent_inner (hA : ARTop P ℱ e Mt Ct S W) (n : ℕ) (x y : H) :
    Measurable fun p : ℝ × Ω => inner ℝ (resolvent (S p.1 p.2) n x) y :=
  isProgressive_measurable_uncurry
    (isProgressive_resolvent e Ct hA.trace S hA.sqrt hA.Cprog hA.Sprog n x y)

lemma ARTop.measurable_resolvent (hA : ARTop P ℱ e Mt Ct S W) (n : ℕ) (x : H) :
    Measurable fun p : ℝ × Ω => resolvent (S p.1 p.2) n x := by
  refine measurable_of_inner_basis e (fun j => ?_)
  have : (fun p : ℝ × Ω => inner ℝ (e j) (resolvent (S p.1 p.2) n x)) =
      fun p => inner ℝ (resolvent (S p.1 p.2) n x) (e j) := by
    funext p; exact real_inner_comm _ _
  rw [this]
  exact hA.measurable_resolvent_inner n x (e j)

lemma ARTop.measurable_Gn (hA : ARTop P ℱ e Mt Ct S W) (n : ℕ) (k : ι) :
    Measurable fun p : ℝ × Ω => GnT e S n k p.1 p.2 := by
  unfold GnT
  have h1 := (hA.measurable_resolvent n (e k)).const_smul (epsn n)
  exact (WithLp.measurable_toLp 2 (H × H)).comp (Measurable.prodMk (measurable_const.sub h1) h1)

lemma ARTop.measurable_psin (hA : ARTop P ℱ e Mt Ct S W) (n : ℕ) (k : ι) :
    Measurable fun p : ℝ × Ω => psinT e S n k p.1 p.2 := by
  unfold psinT
  exact (hA.measurable_resolvent n (e k)).const_smul (epsn n)

lemma ARTop.measurable_Thn (hA : ARTop P ℱ e Mt Ct S W) (n : ℕ) (k : ι) (a : ι ⊕ ι) :
    Measurable fun p : ℝ × Ω => ThnT e S n k p.1 p.2 a := by
  rcases a with i | j
  · simp only [ThnT, Sum.elim_inl]
    have : (fun p : ℝ × Ω => inner ℝ (e i) (resolvent (S p.1 p.2) n (e k))) =
        fun p => inner ℝ (resolvent (S p.1 p.2) n (e k)) (e i) := by
      funext p; exact real_inner_comm _ _
    rw [this]
    exact hA.measurable_resolvent_inner n (e k) (e i)
  · simp only [ThnT, Sum.elim_inr]
    exact meas_inner measurable_const (hA.measurable_psin n k)

lemma ARTop.norm_psin_le (hA : ARTop P ℱ e Mt Ct S W) (n : ℕ) (k : ι) (r : ℝ) (ω : Ω) :
    ‖psinT e S n k r ω‖ ≤ 2 := by
  unfold psinT
  have h2 : epsn n • resolvent (S r ω) n (e k) = e k - S r ω (resolvent (S r ω) n (e k)) :=
    eq_sub_of_add_eq' (resolvent_right (hA.psd r ω) n (e k))
  rw [h2]
  calc ‖e k - S r ω (resolvent (S r ω) n (e k))‖ ≤ ‖e k‖ + ‖S r ω (resolvent (S r ω) n (e k))‖ :=
        norm_sub_le _ _
    _ ≤ 1 + 1 := by
        gcongr
        · exact (e.orthonormal.norm_eq_one k).le
        · calc _ ≤ ‖e k‖ := norm_S_resolvent_le (hA.psd r ω) n (e k)
            _ = 1 := e.orthonormal.norm_eq_one k
    _ = 2 := by norm_num

theorem ARTop.approx_Gn (hA : ARTop P ℱ e Mt Ct S W) (n : ℕ) (k : ι) :
    Approx P ℱ (vzT e S) (GnT e S n k) := by
  classical
  have hN := hA.isNoiseK
  obtain ⟨F, hF⟩ := Filter.exists_seq_tendsto (Filter.atTop : Filter (Finset ι))
  refine Approx.of_limit (Gs := fun m => GFT e S n k (F m)) (fun m => ?_) (fun N => ?_)
  · -- each truncation is approximable
    have := approx_of_bounded (P := P) (ℱ := ℱ) hA.complete hN ((F m).disjSum (F m))
      (fun r ω (a : ↥((F m).disjSum (F m))) => ThnT e S n k r ω a.1) (C := 2 * ((n : ℝ) + 1) + 2)
      ?_ (by positivity) ?_
    · exact this
    · -- progressive
      intro i
      letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
      refine measurable_pi_iff.2 fun a => ?_
      rcases a with ⟨a, ha⟩
      rcases a with i' | j
      · simp only [ThnT, Sum.elim_inl]
        have : (fun z : Set.Iic i × Ω => inner ℝ (e i') (resolvent (S z.1 z.2) n (e k))) =
            fun z => inner ℝ (resolvent (S z.1 z.2) n (e k)) (e i') := by
          funext z; exact real_inner_comm _ _
        rw [this]
        exact (isProgressive_resolvent e Ct hA.trace S hA.sqrt hA.Cprog hA.Sprog n (e k) (e i')) i
      · simp only [ThnT, Sum.elim_inr, psinT]
        have : (fun z : Set.Iic i × Ω => inner ℝ (e j) (epsn n • resolvent (S z.1 z.2) n (e k))) =
            fun z => epsn n * inner ℝ (resolvent (S z.1 z.2) n (e k)) (e j) := by
          funext z; rw [real_inner_smul_right, real_inner_comm]
        rw [this]
        exact (isProgressive_resolvent e Ct hA.trace S hA.sqrt hA.Cprog hA.Sprog n (e k) (e j) i).const_mul _
    · -- bounded
      intro r ω a
      rcases a with ⟨a, ha⟩
      rcases a with i' | j
      · simp only [ThnT, Sum.elim_inl]
        calc |inner ℝ (e i') (resolvent (S r ω) n (e k))| ≤ ‖e i'‖ * ‖resolvent (S r ω) n (e k)‖ :=
              abs_real_inner_le_norm _ _
          _ ≤ 1 * (2 * ((n : ℝ) + 1) * ‖e k‖) := by
              gcongr
              · exact (e.orthonormal.norm_eq_one i').le
              · exact norm_resolvent_le (hA.psd r ω) n (e k)
          _ ≤ 2 * ((n : ℝ) + 1) + 2 := by
              rw [e.orthonormal.norm_eq_one k]; linarith
      · simp only [ThnT, Sum.elim_inr]
        calc |inner ℝ (e j) (psinT e S n k r ω)| ≤ ‖e j‖ * ‖psinT e S n k r ω‖ :=
              abs_real_inner_le_norm _ _
          _ ≤ 1 * 2 := by
              gcongr
              · exact (e.orthonormal.norm_eq_one j).le
              · exact hA.norm_psin_le n k r ω
          _ ≤ 2 * ((n : ℝ) + 1) + 2 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · -- convergence of the truncations
    set d : ℝ × Ω → ℝ := fun p => 2 * ((n : ℝ) + 1) * dST e Ct p + 2 with hd
    have hdm : Measurable d := (measurable_const.mul hA.measurable_dS).add measurable_const
    have hdL2 : eLpNorm d 2 (tsm P N) ≠ ∞ := by
      have h1 : eLpNorm ((2 * ((n : ℝ) + 1)) • dST e Ct) 2 (tsm P N) ≠ ∞ := by
        rw [eLpNorm_const_smul]
        exact ENNReal.mul_ne_top enorm_ne_top (hA.eLpNorm_dS N)
      have h2 : eLpNorm (fun _ : ℝ × Ω => (2 : ℝ)) 2 (tsm P N) ≠ ∞ :=
        (memLp_const (2 : ℝ)).eLpNorm_ne_top
      have h3 : d = ((2 * ((n : ℝ) + 1)) • dST e Ct) + (fun _ => (2 : ℝ)) := by
        funext p; simp [hd]
      rw [h3]
      exact ne_of_lt (lt_of_le_of_lt (eLpNorm_add_le (by norm_num))
        (ENNReal.add_lt_top.2 ⟨h1.lt_top, h2.lt_top⟩))
    refine tendsto_eLpNorm_of_dominated (μ := tsm P N) (f := fun m p => GFT e S n k (F m) p.1 p.2)
      (g := fun p => GnT e S n k p.1 p.2) (d := d) (fun m => ?_) (hA.measurable_Gn n k) hdm hdL2
      (fun m => Eventually.of_forall fun p => ?_) (Eventually.of_forall fun p => ?_)
    · unfold GFT
      exact Finset.measurable_sum _ fun a _ => (hA.measurable_Thn n k a.1).smul
        (hA.measurable_vz a.1)
    · -- domination
      obtain ⟨r, ω⟩ := p
      simp only []
      rw [GFT_eq]
      have hRk := resolvent_right (hA.psd r ω) n (e k)
      have hg : ‖resolvent (S r ω) n (e k)‖ ≤ 2 * ((n : ℝ) + 1) := by
        have := norm_resolvent_le (hA.psd r ω) n (e k)
        rwa [e.orthonormal.norm_eq_one k, mul_one] at this
      have hGn : GnT e S n k r ω = WithLp.toLp 2
          (S r ω (resolvent (S r ω) n (e k)), psinT e S n k r ω) := by
        unfold GnT psinT
        rw [eq_sub_of_add_eq hRk]
      rw [hGn]
      refine (norm_toLp_sub_le _ _ _ _).trans ?_
      have hψ := norm_sub_proj_le e (psinT e S n k r ω) (F m)
      have hψ2 := hA.norm_psin_le n k r ω
      have hdS : ‖S r ω (∑ i ∈ F m, inner ℝ (e i) (resolvent (S r ω) n (e k)) • e i) -
          S r ω (resolvent (S r ω) n (e k))‖ ≤ 2 * ((n : ℝ) + 1) * dST e Ct (r, ω) := by
        simp only [dST]
        rw [← map_sub]
        calc _ ≤ Real.sqrt (trf e Ct (r, ω)) * ‖(∑ i ∈ F m, inner ℝ (e i)
              (resolvent (S r ω) n (e k)) • e i) - resolvent (S r ω) n (e k)‖ :=
              hA.norm_S_le r ω _
          _ ≤ Real.sqrt (trf e Ct (r, ω)) * (2 * ((n : ℝ) + 1)) := by
              gcongr
              rw [norm_sub_rev]
              exact (norm_sub_proj_le e _ (F m)).trans hg
          _ = _ := by ring
      calc _ ≤ 2 * ((n : ℝ) + 1) * dST e Ct (r, ω) + 2 :=
            add_le_add hdS (by rw [norm_sub_rev]; exact hψ.trans hψ2)
        _ = d (r, ω) := by simp only [hd]
    · -- pointwise limit
      obtain ⟨r, ω⟩ := p
      simp only []
      have hRk := resolvent_right (hA.psd r ω) n (e k)
      have hlim1 : Tendsto (fun m => S r ω (∑ i ∈ F m, inner ℝ (e i)
          (resolvent (S r ω) n (e k)) • e i)) atTop
          (𝓝 (e k - epsn n • resolvent (S r ω) n (e k))) := by
        have := ((S r ω).continuous.tendsto _).comp
          (tendsto_proj e (resolvent (S r ω) n (e k)) hF)
        rwa [eq_sub_of_add_eq hRk] at this
      have hlim2 : Tendsto (fun m => ∑ j ∈ F m, inner ℝ (e j) (psinT e S n k r ω) • e j) atTop
          (𝓝 (psinT e S n k r ω)) := tendsto_proj e _ hF
      have := ((WithLp.prod_continuous_toLp 2 H H).tendsto _).comp (hlim1.prodMk_nhds hlim2)
      have hGn : GnT e S n k r ω = WithLp.toLp 2 (e k -
          epsn n • resolvent (S r ω) n (e k), psinT e S n k r ω) := by
        unfold GnT psinT; rfl
      rw [hGn]
      simp only [GFT_eq]
      exact this

end ApproxGn

section ApproxGk

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {e : HilbertBasis ι ℝ H}
  {Mt : ℝ → Ω → H} {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ} {S : ℝ → Ω → H →L[ℝ] H}
  {W : ℝ≥0 → Ω → ι → ℝ}

lemma norm_Q_leT (hA : ARTop P ℱ e Mt Ct S W) {Q : ℝ → Ω → H →L[ℝ] H}
    (hQlim : ∀ r ω x, Tendsto (fun n => S r ω (resolvent (S r ω) n x)) atTop (𝓝 (Q r ω x)))
    (r : ℝ) (ω : Ω) (x : H) : ‖Q r ω x‖ ≤ ‖x‖ :=
  le_of_tendsto' (hQlim r ω x).norm (fun n => norm_S_resolvent_le (hA.psd r ω) n x)

lemma measurable_Q_applyT (hA : ARTop P ℱ e Mt Ct S W) {Q : ℝ → Ω → H →L[ℝ] H}
    (hQprog : ∀ x y, IsProgressive ℱ (fun r ω => inner ℝ (Q r ω x) y)) (x : H) :
    Measurable fun p : ℝ × Ω => Q p.1 p.2 x := by
  refine measurable_of_inner_basis e (fun j => ?_)
  have : (fun p : ℝ × Ω => inner ℝ (e j) (Q p.1 p.2 x)) = fun p => inner ℝ (Q p.1 p.2 x) (e j) := by
    funext p; exact real_inner_comm _ _
  rw [this]
  exact isProgressive_measurable_uncurry (hQprog x (e j))

theorem ARTop.approx_Gk (hA : ARTop P ℱ e Mt Ct S W) {Q : ℝ → Ω → H →L[ℝ] H}
    (hQlim : ∀ r ω x, Tendsto (fun n => S r ω (resolvent (S r ω) n x)) atTop (𝓝 (Q r ω x)))
    (hQprog : ∀ x y, IsProgressive ℱ (fun r ω => inner ℝ (Q r ω x) y)) (k : ι) :
    Approx P ℱ (vzT e S) (GkT e Q k) := by
  have hGk : Measurable fun p : ℝ × Ω => GkT e Q k p.1 p.2 := by
    unfold GkT
    have h1 := measurable_Q_applyT hA hQprog (e k)
    exact (WithLp.measurable_toLp 2 (H × H)).comp (Measurable.prodMk h1 (measurable_const.sub h1))
  refine Approx.of_limit (Gs := fun n => GnT e S n k) (fun n => hA.approx_Gn n k) (fun N => ?_)
  refine tendsto_eLpNorm_of_dominated (μ := tsm P N) (f := fun n p => GnT e S n k p.1 p.2)
    (g := fun p => GkT e Q k p.1 p.2) (d := fun _ => (6 : ℝ)) (fun n => hA.measurable_Gn n k) hGk
    measurable_const (memLp_const (6 : ℝ)).eLpNorm_ne_top
    (fun n => Eventually.of_forall fun p => ?_) (Eventually.of_forall fun p => ?_)
  · obtain ⟨r, ω⟩ := p
    simp only []
    refine (norm_toLp_sub_le _ _ _ _).trans ?_
    have hRk := resolvent_right (hA.psd r ω) n (e k)
    have h1 : ‖e k - epsn n • resolvent (S r ω) n (e k)‖ ≤ 1 := by
      rw [← eq_sub_of_add_eq hRk]
      calc _ ≤ ‖e k‖ := norm_S_resolvent_le (hA.psd r ω) n (e k)
        _ = 1 := e.orthonormal.norm_eq_one k
    have h2 : ‖Q r ω (e k)‖ ≤ 1 := (norm_Q_leT hA hQlim r ω (e k)).trans
      (e.orthonormal.norm_eq_one k).le
    have h3 : ‖epsn n • resolvent (S r ω) n (e k)‖ ≤ 2 := by
      have := hA.norm_psin_le n k r ω
      simpa [psinT] using this
    have h4 : ‖e k - Q r ω (e k)‖ ≤ 2 := by
      calc _ ≤ ‖e k‖ + ‖Q r ω (e k)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by rw [e.orthonormal.norm_eq_one k]; linarith
        _ = 2 := by norm_num
    calc _ ≤ (‖e k - epsn n • resolvent (S r ω) n (e k)‖ + ‖Q r ω (e k)‖) +
          (‖epsn n • resolvent (S r ω) n (e k)‖ + ‖e k - Q r ω (e k)‖) := by
          gcongr <;> exact norm_sub_le _ _
      _ ≤ 6 := by linarith
  · obtain ⟨r, ω⟩ := p
    simp only []
    unfold GnT GkT
    have hRk : ∀ n, e k - epsn n • resolvent (S r ω) n (e k) =
        S r ω (resolvent (S r ω) n (e k)) := fun n => by
      rw [eq_sub_of_add_eq (resolvent_right (hA.psd r ω) n (e k))]
    have hRk' : ∀ n, epsn n • resolvent (S r ω) n (e k) =
        e k - S r ω (resolvent (S r ω) n (e k)) := fun n =>
      eq_sub_of_add_eq' (resolvent_right (hA.psd r ω) n (e k))
    have h1 := hQlim r ω (e k)
    have h2 : Tendsto (fun n => epsn n • resolvent (S r ω) n (e k)) atTop
        (𝓝 (e k - Q r ω (e k))) := by
      simp_rw [hRk']
      exact tendsto_const_nhds.sub h1
    have h1' : Tendsto (fun n => e k - epsn n • resolvent (S r ω) n (e k)) atTop
        (𝓝 (Q r ω (e k))) := by
      simp_rw [hRk]; exact h1
    exact ((WithLp.prod_continuous_toLp 2 H H).tendsto _).comp (h1'.prodMk_nhds h2)

end ApproxGk

end Gk

end HRS.Uniform.Q48a
