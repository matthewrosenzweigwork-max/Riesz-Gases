import HRS.Uniform.Q48aAux2

/-!
# Q48a, part 3: martingale representation on the whole half-line (horizon `⊤`)

`⊤`-copy of `HRS/Prob/MRepAux12.lean` (sections `Ct`, `Reg2`) and `HRS/Prob/MRepAux14.lean`: for a continuous `L²`
Hilbert martingale `M` with covariation density `Sg` on every window `[0,S]` (`hM : ∀ S ≥ 0, ...`) there is an
enlargement (product with independent Wiener coordinates) carrying a cylindrical Brownian motion `B` independent of
`𝒢` and an integrand `Φ` (Hilbert-Schmidt on every window, `Φ_r Φ_r^* = Sg_r` for all `r ≥ 0`) with `M̃ = ∫ Φ dB`
a modification of `M∘π`.
-/

noncomputable section

open HRS HRS.MRep
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q48a

section Ct

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]

/-- All windows: for every `S ≥ 0` the covariation hypotheses on `[0,S]`. -/
abbrev AllWin (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (M : ℝ → Ω → H)
    (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)) : Prop :=
  ∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P ℱ S M Sg

lemma allwin_traceClass {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : AllWin P ℱ M Sg) : ∀ᵐ ω ∂P, ∀ σ : ℝ, 0 ≤ σ → IsTraceClassCov (Sg σ ω) := by
  have h : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ σ ∈ Set.Icc (0 : ℝ) n, IsTraceClassCov (Sg σ ω) :=
    fun n => (hM n (Nat.cast_nonneg n)).sigma_traceClass
  rw [← ae_all_iff] at h
  filter_upwards [h] with ω hω σ hσ
  obtain ⟨n, hn⟩ := exists_nat_ge σ
  exact hω n σ ⟨hσ, hn⟩

lemma allwin_entry_int {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : AllWin P ℱ M Sg) :
    ∀ᵐ ω ∂P, ∀ (x y : H) (t : ℝ), IntegrableOn (fun σ => Sg σ ω x y) (Set.Icc 0 t) := by
  have h : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ x y : H, IntegrableOn (fun σ => Sg σ ω x y) (Set.Icc 0 (n : ℝ)) :=
    fun n => (hM n (Nat.cast_nonneg n)).sigma_entry_int
  rw [← ae_all_iff] at h
  filter_upwards [h] with ω hω x y t
  obtain ⟨n, hn⟩ := exists_nat_ge t
  exact (hω n x y).mono_set (Set.Icc_subset_Icc le_rfl hn)

theorem exists_CtTop {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : AllWin P ℱ M Sg) (e : HilbertBasis ι ℝ H) :
    ∃ Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ,
      (∀ r ω, IsTraceClassCov (Ct r ω)) ∧ (∀ x y, IsProgressive ℱ (fun r ω => Ct r ω x y)) ∧
      (∀ r : ℝ, 0 ≤ r → ∀ᵐ ω ∂P, Ct r ω = Sg r ω) ∧
      (∀ᵐ ω ∂P, ∀ᵐ r ∂(volume.restrict (Set.Ici (0 : ℝ))), Ct r ω = Sg r ω) ∧
      (∀ᵐ ω ∂P, ∀ i j (t : ℝ), IntegrableOn (fun r => Ct r ω (e i) (e j)) (Set.Icc 0 t)) ∧
      (∀ t : ℝ, ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (∑' i, Ct r ω (e i) (e i))) ∂P ≠ ∞) := by
  classical
  have hM0 := hM 0 le_rfl
  have htc := allwin_traceClass hM
  have hex : ∀ i j, ∃ Z : ℝ → Ω → ℝ, IsProgressive ℱ Z ∧
      ∀ t, Z t =ᵐ[P] (fun ω => Sg t ω (e i) (e j)) := fun i j =>
    exists_progressive_modification (P := P) (Y := fun t ω => Sg t ω (e i) (e j))
      (hM0.sigma_meas _ _) (fun t => hM0.sigma_adapted t _ _)
  choose Z hZp hZ using hex
  set Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ := fun r ω => matForm e (fun i j => Z i j r ω) with hCt
  have h1 : ∀ r ω, IsTraceClassCov (Ct r ω) := fun r ω => by
    by_cases hg : GoodMat (fun i j => Z i j r ω)
    · exact isTraceClassCov_matForm hg
    · simp only [hCt, matForm_of_not hg]
      exact isTraceClassCov_zero
  have h2 : ∀ x y, IsProgressive ℱ (fun r ω => Ct r ω x y) := fun x y i => by
    letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
    exact measurable_matForm_apply e (α := Set.Iic i × Ω)
      (a := fun a b p => Z a b p.1 p.2) (fun a b => hZp a b i) x y
  have h3 : ∀ r : ℝ, 0 ≤ r → ∀ᵐ ω ∂P, Ct r ω = Sg r ω := by
    intro r hr
    have h1 : ∀ᵐ ω ∂P, ∀ i j, Z i j r ω = Sg r ω (e i) (e j) :=
      ae_all_iff.2 fun i => ae_all_iff.2 fun j => hZ i j r
    filter_upwards [h1, htc] with ω h1 h2
    have : (fun i j => Z i j r ω) = fun i j => Sg r ω (e i) (e j) := by
      funext i j; exact h1 i j
    show matForm e (fun i j => Z i j r ω) = Sg r ω
    rw [this]
    exact matForm_matrix e (h2 r hr)
  have hCtm : ∀ i j, Measurable fun p : ℝ × Ω => Ct p.1 p.2 (e i) (e j) := fun i j =>
    isProgressive_measurable_uncurry (h2 (e i) (e j))
  have hSm : ∀ i j, Measurable fun p : ℝ × Ω => Sg p.1 p.2 (e i) (e j) := fun i j =>
    hM0.sigma_meas _ _
  set Eset : Set (ℝ × Ω) := {p | ∃ i j, Ct p.1 p.2 (e i) (e j) ≠ Sg p.1 p.2 (e i) (e j)} with hE
  have hEm : MeasurableSet Eset := by
    have : Eset = ⋃ i, ⋃ j, {p : ℝ × Ω | Ct p.1 p.2 (e i) (e j) ≠ Sg p.1 p.2 (e i) (e j)} := by
      ext p; simp [hE]
    rw [this]
    exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
      (measurableSet_eq_fun (hCtm i j) (hSm i j)).compl
  have hsec : ∀ r ∈ Set.Ici (0 : ℝ), P (Prod.mk r ⁻¹' Eset) = 0 := by
    intro r hr
    have := h3 r hr
    rw [ae_iff] at this
    refine measure_mono_null (fun ω hω => ?_) this
    obtain ⟨i, j, hij⟩ := hω
    intro heq
    exact hij (by rw [heq])
  have hprod : ((volume.restrict (Set.Ici (0 : ℝ))).prod P) Eset = 0 := by
    rw [Measure.measure_prod_null hEm]
    filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
    exact hsec r hr
  have hae1 : ∀ᵐ p ∂((volume.restrict (Set.Ici (0 : ℝ))).prod P), p ∉ Eset := by
    rw [ae_iff]; simpa using hprod
  have hae2 : ∀ᵐ r ∂(volume.restrict (Set.Ici (0 : ℝ))), ∀ᵐ ω ∂P, (r, ω) ∉ Eset :=
    Measure.ae_ae_of_ae_prod hae1
  have hae3 : ∀ᵐ ω ∂P, ∀ᵐ r ∂(volume.restrict (Set.Ici (0 : ℝ))), (r, ω) ∉ Eset :=
    (Measure.ae_ae_comm (μ := volume.restrict (Set.Ici (0 : ℝ))) (ν := P)
      (p := fun r ω => (r, ω) ∉ Eset) hEm.compl).1 hae2
  have h4 : ∀ᵐ ω ∂P, ∀ᵐ r ∂(volume.restrict (Set.Ici (0 : ℝ))), Ct r ω = Sg r ω := by
    filter_upwards [hae3] with ω hω
    filter_upwards [hω] with r hr
    refine form_ext_basis e fun i j => ?_
    by_contra hne
    exact hr ⟨i, j, hne⟩
  refine ⟨Ct, h1, h2, h3, h4, ?_, ?_⟩
  · filter_upwards [allwin_entry_int hM, h4] with ω hω h4ω i j t
    have h5 : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) t)), Ct r ω = Sg r ω :=
      ae_restrict_of_ae_restrict_of_subset Set.Icc_subset_Ici_self h4ω
    exact (hω (e i) (e j) t).congr_fun_ae
      (h5.mono fun r hr => (congrArg (fun C => C (e i) (e j)) hr).symm)
  · intro t
    by_cases ht : 0 ≤ t
    · have hMt := hM t ht
      have hb : ∀ᵐ ω ∂P, ∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (∑' i, Ct r ω (e i) (e i)) ≤
          ENNReal.ofReal (∫ σ in Set.Icc 0 t, traceNormForm (Sg σ ω)) := by
        filter_upwards [hMt.sigma_traceClass, hMt.sigma_pathint, h4] with ω htc hpath h4ω
        rw [ofReal_integral_eq_lintegral_ofReal hpath
          (Eventually.of_forall fun σ => traceNormForm_nonneg _)]
        refine lintegral_mono_ae ?_
        have h5 : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) t)), Ct r ω = Sg r ω :=
          ae_restrict_of_ae_restrict_of_subset Set.Icc_subset_Ici_self h4ω
        filter_upwards [h5, ae_restrict_mem measurableSet_Icc] with r hr hrI
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hr]
        exact tsum_diag_le_traceNormForm e (htc r hrI)
      refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hb)
      exact hMt.sigma_int.lintegral_lt_top.ne
    · push Not at ht
      simp [Set.Icc_eq_empty (not_le.2 ht)]

end Ct

section Reg

open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]

/-- The regularised martingale on the half-line. -/
def regMT (N : Set Ω) (M : ℝ → Ω → H) : ℝ → Ω → H :=
  fun t ω => if ω ∈ N then 0 else M (max 0 t) ω

lemma allwin_good {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : AllWin P ℱ M Sg) :
    ∀ᵐ ω ∂P, M 0 ω = 0 ∧ ContinuousOn (fun τ => M τ ω) (Set.Ici 0) := by
  have h : ∀ n : ℕ, ∀ᵐ ω ∂P, M 0 ω = 0 ∧ ContinuousOn (fun τ => M τ ω) (Set.Icc 0 (n : ℝ)) :=
    fun n => (hM n (Nat.cast_nonneg n)).zero.and (hM n (Nat.cast_nonneg n)).cont
  have h := ae_all_iff.2 h
  filter_upwards [h, (hM 0 le_rfl).zero] with ω hω h0
  refine ⟨h0, fun t ht => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_ge (t + 1)
  have hI : ContinuousOn (fun τ => M τ ω) (Set.Icc 0 (n : ℝ)) := (hω n).2
  have hnhds : Set.Icc 0 (n : ℝ) ∈ 𝓝[Set.Ici 0] t := by
    refine mem_nhdsWithin.2 ⟨Set.Iio (n : ℝ), isOpen_Iio, by simp only [Set.mem_Iio]; linarith, ?_⟩
    intro y hy
    exact ⟨hy.2, hy.1.le⟩
  exact (hI t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin hnhds

lemma regMT_cont {N : Set Ω} {M : ℝ → Ω → H}
    (hN : ∀ ω, ω ∉ N → M 0 ω = 0 ∧ ContinuousOn (fun τ => M τ ω) (Set.Ici 0)) (ω : Ω) :
    Continuous fun t => regMT N M t ω := by
  by_cases hω : ω ∈ N
  · simp only [regMT, hω, if_true]; exact continuous_const
  · simp only [regMT, hω, if_false]
    exact (hN ω hω).2.comp_continuous (continuous_const.max continuous_id)
      (fun t => Set.mem_Ici.2 (le_max_left _ _))

lemma regMT_zero {N : Set Ω} {M : ℝ → Ω → H}
    (hN : ∀ ω, ω ∉ N → M 0 ω = 0 ∧ ContinuousOn (fun τ => M τ ω) (Set.Ici 0)) {t : ℝ}
    (ht : t ≤ 0) (ω : Ω) : regMT N M t ω = 0 := by
  by_cases hω : ω ∈ N
  · simp [regMT, hω]
  · simp only [regMT, hω, if_false, max_eq_left ht]
    exact (hN ω hω).1

lemma regMT_of_mem {N : Set Ω} {M : ℝ → Ω → H} {t : ℝ} (ht : 0 ≤ t) {ω : Ω}
    (hω : ω ∉ N) : regMT N M t ω = M t ω := by
  simp only [regMT, hω, if_false, max_eq_right ht]

lemma regMT_adapted {N : Set Ω} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : AllWin P ℱ M Sg) (e : HilbertBasis ι ℝ H)
    (hN : ∀ ω, ω ∉ N → M 0 ω = 0 ∧ ContinuousOn (fun τ => M τ ω) (Set.Ici 0))
    (hNm : MeasurableSet N) (hN0 : P N = 0) (t : ℝ) :
    Measurable[augFiltration P ℱ t] (regMT N M t) := by
  by_cases ht : t ≤ 0
  · have : regMT N M t = fun _ => 0 := funext fun ω => regMT_zero hN ht ω
    rw [this]; exact measurable_const
  · push Not at ht
    have hNa : MeasurableSet[augFiltration P ℱ t] N := augFiltration_isComplete ℱ t N hNm hN0
    have hM' : Measurable[augFiltration P ℱ t] (M t) :=
      (measurable_M_adapted (hM 0 le_rfl) e t).mono le_sup_left le_rfl
    have : regMT N M t = fun ω => if ω ∈ N then 0 else M t ω := by
      funext ω; simp only [regMT, max_eq_right ht.le]
    rw [this]
    exact Measurable.ite hNa measurable_const hM'

lemma regMT_ae {N : Set Ω} (hN0 : P N = 0) {M : ℝ → Ω → H} (t : ℝ) :
    ∀ᵐ ω ∂P, regMT N M t ω = M (max 0 t) ω := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
  simp [regMT, hω]

lemma regMT_sq {N : Set Ω} (hN0 : P N = 0) {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : AllWin P ℱ M Sg) (t : ℝ) (x : H) :
    MemLp (fun ω => inner ℝ (regMT N M t ω) x) 2 P := by
  have h := ((hM (max 0 t) (le_max_left _ _)).sq_int (max 0 t)
    ⟨le_max_left _ _, le_rfl⟩).inner_const (𝕜 := ℝ) x
  refine h.ae_eq ?_
  filter_upwards [regMT_ae (P := P) hN0 (M := M) t] with ω hω
  rw [hω]

lemma regMT_mart {N : Set Ω} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : AllWin P ℱ M Sg) (e : HilbertBasis ι ℝ H)
    (hN : ∀ ω, ω ∉ N → M 0 ω = 0 ∧ ContinuousOn (fun τ => M τ ω) (Set.Ici 0))
    (hNm : MeasurableSet N) (hN0 : P N = 0) (x : H) :
    Martingale (fun t ω => inner ℝ (regMT N M t ω) x) (augFiltration P ℱ) P := by
  have hX := martingale_aug ((hM 0 le_rfl).martingale x)
  refine martingale_congr_complete (augFiltration_isComplete ℱ) hX (fun t => ?_) (fun t => ?_)
  · have h := (regMT_adapted hM e hN hNm hN0 t).mono (augFiltration P ℱ |>.le t) le_rfl
    exact h.inner measurable_const
  · by_cases ht : 0 ≤ t
    · filter_upwards [regMT_ae (P := P) hN0 (M := M) t] with ω hω
      show inner ℝ (M t ω) x = inner ℝ (regMT N M t ω) x
      rw [hω, max_eq_right ht]
    · push Not at ht
      filter_upwards [M_nonpos_ae (hM 0 le_rfl) ht.le x] with ω hω
      show inner ℝ (M t ω) x = inner ℝ (regMT N M t ω) x
      rw [regMT_zero hN ht.le, inner_zero_left, hω]

lemma regMT_cov {N : Set Ω} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : AllWin P ℱ M Sg) (e : HilbertBasis ι ℝ H)
    (hN : ∀ ω, ω ∉ N → M 0 ω = 0 ∧ ContinuousOn (fun τ => M τ ω) (Set.Ici 0))
    (hNm : MeasurableSet N) (hN0 : P N = 0) {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ}
    (hCprog : ∀ x y, IsProgressive ℱ (fun r ω => Ct r ω x y))
    (h4 : ∀ᵐ ω ∂P, ∀ᵐ r ∂(volume.restrict (Set.Ici (0 : ℝ))), Ct r ω = Sg r ω) (x y : H) :
    Martingale (fun t ω => inner ℝ (regMT N M t ω) x * inner ℝ (regMT N M t ω) y -
      ∫ r in Set.Icc 0 t, Ct r ω x y) (augFiltration P ℱ) P := by
  have hX := martingale_aug ((hM 0 le_rfl).covariation x y)
  refine martingale_congr_complete (augFiltration_isComplete ℱ) hX (fun t => ?_) (fun t => ?_)
  · have h := (regMT_adapted hM e hN hNm hN0 t).mono (augFiltration P ℱ |>.le t) le_rfl
    refine (h.inner measurable_const).mul (h.inner measurable_const) |>.sub ?_
    refine HRS.MRep.measurable_setIntegral_Icc (g := fun r ω => Ct r ω x y) ?_ t
    exact isProgressive_measurable_uncurry (hCprog x y)
  · by_cases ht : 0 ≤ t
    · filter_upwards [regMT_ae (P := P) hN0 (M := M) t, h4] with ω hω h4ω
      show inner ℝ (M t ω) x * inner ℝ (M t ω) y -
          ∫ σ in Set.Icc 0 t, Sg σ ω x y =
        inner ℝ (regMT N M t ω) x * inner ℝ (regMT N M t ω) y -
          ∫ r in Set.Icc 0 t, Ct r ω x y
      rw [hω, max_eq_right ht]
      congr 1
      have h5 : ∀ᵐ r ∂(volume.restrict (Set.Icc 0 t)), Ct r ω = Sg r ω :=
        ae_restrict_of_ae_restrict_of_subset Set.Icc_subset_Ici_self h4ω
      refine (integral_congr_ae ?_).symm
      filter_upwards [h5] with r hr
      rw [hr]
    · push Not at ht
      filter_upwards [M_nonpos_ae (hM 0 le_rfl) ht.le x, M_nonpos_ae (hM 0 le_rfl) ht.le y] with ω hx hy
      show inner ℝ (M t ω) x * inner ℝ (M t ω) y -
          ∫ σ in Set.Icc 0 t, Sg σ ω x y =
        inner ℝ (regMT N M t ω) x * inner ℝ (regMT N M t ω) y -
          ∫ r in Set.Icc 0 t, Ct r ω x y
      rw [regMT_zero hN ht.le, inner_zero_left, hx, hy, Set.Icc_eq_empty (not_le.2 ht)]
      simp

end Reg

/-! ### Assembly -/

section Assembly

open Classical

universe u

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- Martingale representation on the whole half-line, on an enlargement. -/
theorem martingale_representation_top {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (𝒢 : InitialSigma ℱ)
    (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
    (hM : ∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P ℱ S M Sg) :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (π : Ω' → Ω) (_ : MeasurePreserving π P' P) (ℱ' : Filtration ℝ mΩ')
      (ι : Type u) (_ : Countable ι) (B : ℝ≥0 → Ω' → ι → ℝ) (Φ : ℝ → Ω' → ι → H) (M' : ℝ → Ω' → H),
      (∀ τ, (ℱ τ).comap π ≤ ℱ' τ) ∧
      IsCylindricalBrownian P' ℱ' B ∧
      Indep (𝒢.1.comap π) (cylindricalPathSigma B) P' ∧
      (∀ S : ℝ, IsHSIntegrand P' ℱ' S Φ) ∧
      (∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P' ℱ' S
        (fun τ ω' => M τ (π ω')) (fun r ω' => Sg r (π ω'))) ∧
      IsHilbertItoIntegral P' ℱ' B Φ M' ∧
      (∀ᵐ ω' ∂P', ∀ τ : ℝ, 0 ≤ τ → M' τ ω' = M τ (π ω')) ∧
      (∀ r : ℝ, 0 ≤ r → ∀ᵐ ω' ∂P', hsCovForm (Φ r ω') = Sg r (π ω')) ∧
      (∀ᵐ ω' ∂P', ∀ᵐ r ∂(volume.restrict (Set.Ici (0 : ℝ))), hsCovForm (Φ r ω') = Sg r (π ω')) := by
  obtain ⟨ι, hι, e, -⟩ := exists_hilbertBasis_ulift.{_, u} (H := H)
  -- the exceptional null set
  have hbad : P {ω | ¬ (M 0 ω = 0 ∧ ContinuousOn (fun τ => M τ ω) (Set.Ici 0))} = 0 :=
    ae_iff.1 (allwin_good hM)
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hbad
  have hN : ∀ ω, ω ∉ N → M 0 ω = 0 ∧ ContinuousOn (fun τ => M τ ω) (Set.Ici 0) := by
    intro ω hω
    by_contra h
    exact hω (hsub h)
  obtain ⟨Ct, hCt1, hCt2, hCt3, hCt4, hCt5, hCt6⟩ := exists_CtTop hM e
  obtain ⟨S, hS1, hS2⟩ := exists_progressive_sqrt e Ct hCt1 hCt2
  -- the enlargement
  set ℱb : Filtration ℝ mΩ := augFiltration P ℱ with hℱb
  set P' : Measure (Ω × (ι → WienerSeq)) := P.prod (wMeasure ι) with hP'
  set ℱ' := prodFiltration P (wMeasure ι) ℱb (wFiltration ι) with hℱ'
  have hπp : MeasurePreserving (Prod.fst : Ω × (ι → WienerSeq) → Ω) P' P := measurePreserving_fst
  have hπm : ∀ s, Measurable[ℱ' s, ℱb s] (Prod.fst : Ω × (ι → WienerSeq) → Ω) := fun s =>
    Measurable.of_comap_le (le_sup_of_le_left le_sup_left)
  have hcomap : ∀ τ, (ℱ τ).comap (Prod.fst : Ω × (ι → WienerSeq) → Ω) ≤ ℱ' τ := fun τ =>
    (MeasurableSpace.comap_mono (le_sup_left : ℱ τ ≤ ℱb τ)).trans
      (le_sup_of_le_left le_sup_left)
  have hℱbℱ : ∀ t, ℱ t ≤ ℱb t := fun t => le_sup_left
  set Mt : ℝ → Ω → H := regMT N M with hMt
  have hCprog' : ∀ x y, IsProgressive ℱb (fun r ω => Ct r ω x y) := fun x y =>
    IsProgressive.mono_filtration hℱbℱ (hCt2 x y)
  have hSprog' : ∀ x y, IsProgressive ℱb (fun r ω => inner ℝ (S r ω x) y) := fun x y =>
    IsProgressive.mono_filtration hℱbℱ (hS2 x y)
  have hGm : ∀ t : ℝ, Measurable fun ω : Ω => ∫⁻ r in Set.Icc 0 t,
      ENNReal.ofReal (∑' i, Ct r ω (e i) (e i)) := by
    intro t
    have hf : Measurable fun p : ℝ × Ω => ENNReal.ofReal (∑' i, Ct p.1 p.2 (e i) (e i)) :=
      ENNReal.measurable_ofReal.comp
        (Measurable.tsum fun i => isProgressive_measurable_uncurry (hCt2 (e i) (e i)))
    exact (hf.comp measurable_swap).lintegral_prod_right' (ν := volume.restrict (Set.Icc 0 t))
  have hA : ARTop P' ℱ' e (fun t ω' => Mt t ω'.1) (fun r ω' => Ct r ω'.1)
      (fun r ω' => S r ω'.1) (fun t ω' j => wienerPath t (ω'.2 j)) :=
    { complete := prodFiltration_complete P ℱb
      cont := fun ω' => regMT_cont hN ω'.1
      adapted := fun t => (regMT_adapted hM e hN hNm hN0 t).comp (hπm t)
      zero := fun t ht ω' => regMT_zero hN ht ω'.1
      sq := fun t x => (regMT_sq hN0 hM t x).comp_measurePreserving hπp
      mart := fun x => martingale_fst (regMT_mart hM e hN hNm hN0 x)
      cov := fun x y => martingale_fst (regMT_cov hM e hN hNm hN0 hCt2 hCt4 x y)
      wiener := isCylindricalBrownian_wiener_prod ℱb
      cross := fun x j => martingale_fst_mul_wiener (regMT_mart hM e hN hNm hN0 x) j
      trace := fun r ω' => hCt1 r ω'.1
      sqrt := fun r ω' => hS1 r ω'.1
      Cprog := fun x y => isProgressive_comp_π hπm (hCprog' x y)
      Sprog := fun x y => isProgressive_comp_π hπm (hSprog' x y)
      Cint := hπp.quasiMeasurePreserving.ae hCt5
      Ctr := fun t => by
        show ∫⁻ ω', (fun ω => ∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (∑' i, Ct r ω (e i) (e i))) ω'.1
          ∂P' ≠ ∞
        rw [hπp.lintegral_comp (hGm t)]
        exact hCt6 t }
  obtain ⟨B, hB, hItoB⟩ := hA.representation
  have hle0 : 𝒢.1.comap (Prod.fst : Ω × (ι → WienerSeq) → Ω) ≤ ℱ' 0 :=
    (MeasurableSpace.comap_mono 𝒢.2).trans (hcomap 0)
  have hqmp := hπp.quasiMeasurePreserving
  have hMImm : ∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P' ℱ' S
      (fun τ ω' => M τ ω'.1) (fun r ω' => Sg r ω'.1) := fun S hS =>
    { martingale := fun x => martingale_fst (martingale_aug ((hM S hS).martingale x))
      zero := hqmp.ae (hM S hS).zero
      cont := hqmp.ae (hM S hS).cont
      sq_int := fun τ hτ => ((hM S hS).sq_int τ hτ).comp_measurePreserving hπp
      sigma_meas := fun x y => ((hM S hS).sigma_meas x y).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      sigma_adapted := fun σ x y => ((hM S hS).sigma_adapted σ x y).comp
        (Measurable.of_comap_le (hcomap σ))
      sigma_traceClass := hqmp.ae (hM S hS).sigma_traceClass
      sigma_int := MeasureTheory.Integrable.comp_fst (hM S hS).sigma_int (wMeasure ι)
      sigma_pathint := hqmp.ae (hM S hS).sigma_pathint
      sigma_entry_int := hqmp.ae (hM S hS).sigma_entry_int
      covariation := fun x y => martingale_fst (martingale_aug ((hM S hS).covariation x y)) }
  refine ⟨Ω × (ι → WienerSeq), inferInstance, P', inferInstance, Prod.fst, hπp, ℱ', ι, hι, B,
    PhiRT e (fun r ω' => S r ω'.1), (fun t ω' => Mt t ω'.1), hcomap, hB,
    indep_of_indep_of_le_left (indep_zero_cylPath hB) hle0, fun S' => hA.isHSIntegrand S',
    hMImm, hItoB, ?_, ?_, ?_⟩
  · filter_upwards [hqmp.ae (measure_eq_zero_iff_ae_notMem.1 hN0)] with ω' hω' τ hτ
    exact regMT_of_mem hτ hω'
  · intro r hr
    filter_upwards [hqmp.ae (hCt3 r hr)] with ω' h
    rw [hA.hsCovForm_PhiR r ω']
    exact h
  · filter_upwards [hqmp.ae hCt4] with ω' hω'
    filter_upwards [hω'] with r hr
    rw [hA.hsCovForm_PhiR r ω']
    exact hr

end Assembly

end HRS.Uniform.Q48a
