import HRS.Prob.MRepAux1

/-!
# MREP, part 2: the stochastic integral as an `L²` limit of elementary integrals

`Q_{αβ}(r,ω) = ⟨v_α(r,ω), v_β(r,ω)⟩_K` (a factorisation through a Hilbert space `K`).  An integrand
`G : ℝ → Ω → K` is *approximable* if it is an `L²_loc` limit of the processes `hat Ψ = ∑_k Ψ^k v_{a k}`
of elementary integrands.  For such `G` the integral exists, and the isometry, the compensated products and the
cross-covariations with test martingales pass to the limit.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MRep

section Closure

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*}
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K]

/-- `hat Ψ = ∑_k Ψ^k v_{k}`. -/
def hat (v : ℝ → Ω → A → K) (F : Finset A) (Ψ : SimpleIntegrand ℱ F) : ℝ → Ω → K :=
  fun r ω => ∑ k : F, Ψ.toFun r ω k • v r ω k.1

/-- The elementary integral over a finite set of coordinates. -/
def eInt (N : ℝ → Ω → A → ℝ) (F : Finset A) (Ψ : SimpleIntegrand ℱ F) : ℝ → Ω → ℝ :=
  nInt N (fun k : F => k.1) Ψ

/-- The weighted `L²` size over `[0,s]`. -/
def qn (P : Measure Ω) (s : ℝ) (G : ℝ → Ω → K) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ r in Set.Icc 0 s, ‖G r ω‖ₑ ^ 2) ∂P

lemma inner_hat (v : ℝ → Ω → A → K) {F F' : Finset A} (Ψ : SimpleIntegrand ℱ F)
    (Ψ' : SimpleIntegrand ℱ F') (r : ℝ) (ω : Ω) :
    inner ℝ (hat v F Ψ r ω) (hat v F' Ψ' r ω) = ∑ k : F, ∑ l : F',
      Ψ.toFun r ω k * Ψ'.toFun r ω l * inner ℝ (v r ω k.1) (v r ω l.1) := by
  simp only [hat, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- A noise whose covariation densities factor through a Hilbert space `K`. -/
structure IsNoiseK (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (N : ℝ → Ω → A → ℝ)
    (v : ℝ → Ω → A → K) : Prop where
  noise : IsNoise P ℱ N (fun r ω α β => inner ℝ (v r ω α) (v r ω β))
  vmeas : ∀ α, Measurable fun p : ℝ × Ω => v p.1 p.2 α

variable {N : ℝ → Ω → A → ℝ} {v : ℝ → Ω → A → K}

lemma IsNoiseK.compensator_eq (hN : IsNoiseK P ℱ N v) {F F' : Finset A}
    (Ψ : SimpleIntegrand ℱ F) (Ψ' : SimpleIntegrand ℱ F') (s : ℝ) (ω : Ω) :
    ∫ r in Set.Icc 0 s, ∑ k : F, ∑ l : F', Ψ.toFun r ω k * Ψ'.toFun r ω l *
      inner ℝ (v r ω k.1) (v r ω l.1) = ∫ r in Set.Icc 0 s, inner ℝ (hat v F Ψ r ω) (hat v F' Ψ' r ω) :=
  setIntegral_congr_fun measurableSet_Icc fun r _ => (inner_hat v Ψ Ψ' r ω).symm

theorem IsNoiseK.integrable_compensator (hℱ : IsCompleteFiltration P ℱ) (hN : IsNoiseK P ℱ N v)
    {F F' : Finset A} (Ψ : SimpleIntegrand ℱ F) (Ψ' : SimpleIntegrand ℱ F') (s : ℝ) :
    Integrable (fun ω => ∫ r in Set.Icc 0 s, inner ℝ (hat v F Ψ r ω) (hat v F' Ψ' r ω)) P := by
  have hX := martingale_nInt_mul_nInt hℱ hN.noise (fun k : F => k.1) (fun l : F' => l.1) Ψ Ψ'
  have hI : Integrable (fun ω => eInt N F Ψ s ω * eInt N F' Ψ' s ω) P :=
    (memLp_nInt hN.noise.sq _ Ψ s).integrable_mul (memLp_nInt hN.noise.sq _ Ψ' s)
  have := hI.sub (hX.integrable s)
  refine this.congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.sub_apply]
  rw [← hN.compensator_eq Ψ Ψ' s ω]
  simp only [eInt]
  ring

/-- Polarised isometry for elementary integrals. -/
theorem IsNoiseK.integral_eInt_mul (hℱ : IsCompleteFiltration P ℱ) (hN : IsNoiseK P ℱ N v)
    {F F' : Finset A} (Ψ : SimpleIntegrand ℱ F) (Ψ' : SimpleIntegrand ℱ F') (s : ℝ) :
    ∫ ω, eInt N F Ψ s ω * eInt N F' Ψ' s ω ∂P =
      ∫ ω, (∫ r in Set.Icc 0 s, inner ℝ (hat v F Ψ r ω) (hat v F' Ψ' r ω)) ∂P := by
  have hX := martingale_nInt_mul_nInt hℱ hN.noise (fun k : F => k.1) (fun l : F' => l.1) Ψ Ψ'
  have hE := HRS.SimpleIntegrand.martingale_integral_eq_zero_time hX s
  have h0 : ∫ ω, (nInt N (fun k : F => k.1) Ψ 0 ω * nInt N (fun l : F' => l.1) Ψ' 0 ω -
      ∫ r in Set.Icc 0 0, ∑ k : F, ∑ l : F', Ψ.toFun r ω k * Ψ'.toFun r ω l *
        inner ℝ (v r ω k.1) (v r ω l.1)) ∂P = 0 := by
    simp [nInt_of_nonpos N _ Ψ le_rfl, nInt_of_nonpos N _ Ψ' le_rfl]
  have hI : Integrable (fun ω => nInt N (fun k : F => k.1) Ψ s ω *
      nInt N (fun l : F' => l.1) Ψ' s ω) P :=
    (memLp_nInt hN.noise.sq _ Ψ s).integrable_mul (memLp_nInt hN.noise.sq _ Ψ' s)
  have hC := hN.integrable_compensator hℱ Ψ Ψ' s
  simp only [eInt]
  have hC' : Integrable (fun ω => ∫ r in Set.Icc 0 s, ∑ k : F, ∑ l : F',
      Ψ.toFun r ω k * Ψ'.toFun r ω l * inner ℝ (v r ω k.1) (v r ω l.1)) P :=
    hC.congr (ae_of_all _ fun ω => (hN.compensator_eq Ψ Ψ' s ω).symm)
  simp only [h0] at hE
  rw [integral_sub hI hC'] at hE
  have hE' := sub_eq_zero.1 hE
  rw [hE']
  exact integral_congr_ae (ae_of_all _ fun ω => hN.compensator_eq Ψ Ψ' s ω)

theorem IsNoiseK.ae_integrableOn_inner_hat (hN : IsNoiseK P ℱ N v) {F F' : Finset A}
    (Ψ : SimpleIntegrand ℱ F) (Ψ' : SimpleIntegrand ℱ F') :
    ∀ᵐ ω ∂P, ∀ t, IntegrableOn (fun r => inner ℝ (hat v F Ψ r ω) (hat v F' Ψ' r ω))
      (Set.Icc 0 t) := by
  obtain ⟨C, hC⟩ := HRS.SimpleIntegrand.toFun_bdd Ψ
  obtain ⟨C', hC'⟩ := HRS.SimpleIntegrand.toFun_bdd Ψ'
  filter_upwards [hN.noise.Qint] with ω hω t
  simp_rw [inner_hat]
  refine integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => ?_
  have h1 := hω k.1 l.1 t
  refine h1.bdd_mul (c := C * C') ?_ (ae_of_all _ fun r => ?_)
  · have m1 : Measurable fun r : ℝ => Ψ.toFun r ω k :=
      ((measurable_pi_apply k).comp Ψ.measurable_toFun_joint).comp
        (measurable_id.prodMk measurable_const)
    have m2 : Measurable fun r : ℝ => Ψ'.toFun r ω l :=
      ((measurable_pi_apply l).comp Ψ'.measurable_toFun_joint).comp
        (measurable_id.prodMk measurable_const)
    exact (m1.mul m2).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hC r ω k) (hC' r ω l) (abs_nonneg _) ((abs_nonneg _).trans (hC r ω k))

lemma integral_comb3 {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f g h : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    ∫ x, (f x - 2 * g x + h x) ∂μ = ∫ x, f x ∂μ - 2 * ∫ x, g x ∂μ + ∫ x, h x ∂μ := by
  rw [integral_add (f := fun x => f x - 2 * g x) (g := h) (hf.sub (hg.const_mul 2)) hh,
    integral_sub hf (hg.const_mul 2), integral_const_mul]

lemma enorm_sq_eq_ofReal_norm (x : K) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- The isometry for differences of elementary integrals. -/
theorem IsNoiseK.lintegral_eInt_sub_sq (hℱ : IsCompleteFiltration P ℱ) (hN : IsNoiseK P ℱ N v)
    {F F' : Finset A} (Ψ : SimpleIntegrand ℱ F) (Ψ' : SimpleIntegrand ℱ F') (s : ℝ) :
    ∫⁻ ω, ‖eInt N F Ψ s ω - eInt N F' Ψ' s ω‖ₑ ^ 2 ∂P =
      qn P s (fun r ω => hat v F Ψ r ω - hat v F' Ψ' r ω) := by
  have hI : MemLp (eInt N F Ψ s) 2 P := memLp_nInt hN.noise.sq _ Ψ s
  have hI' : MemLp (eInt N F' Ψ' s) 2 P := memLp_nInt hN.noise.sq _ Ψ' s
  have hL : ∫⁻ ω, ‖eInt N F Ψ s ω - eInt N F' Ψ' s ω‖ₑ ^ 2 ∂P =
      ENNReal.ofReal (∫ ω, (eInt N F Ψ s ω - eInt N F' Ψ' s ω) ^ 2 ∂P) := by
    have hsq : Integrable (fun ω => (eInt N F Ψ s ω - eInt N F' Ψ' s ω) ^ 2) P :=
      (hI.sub hI').integrable_sq
    rw [ofReal_integral_eq_lintegral_ofReal hsq (ae_of_all _ fun ω => sq_nonneg _)]
    exact lintegral_congr fun ω => HRS.SimpleIntegrand.enorm_sq_eq' _
  have c11 := hN.integrable_compensator hℱ Ψ Ψ s
  have c12 := hN.integrable_compensator hℱ Ψ Ψ' s
  have c22 := hN.integrable_compensator hℱ Ψ' Ψ' s
  have hae := (hN.ae_integrableOn_inner_hat Ψ Ψ).and ((hN.ae_integrableOn_inner_hat Ψ Ψ').and
    (hN.ae_integrableOn_inner_hat Ψ' Ψ'))
  -- the inner integrals
  set D : Ω → ℝ := fun ω => ∫ r in Set.Icc 0 s, ‖hat v F Ψ r ω - hat v F' Ψ' r ω‖ ^ 2 with hD
  have hDe : ∀ᵐ ω ∂P, D ω = (∫ r in Set.Icc 0 s, inner ℝ (hat v F Ψ r ω) (hat v F Ψ r ω)) -
      2 * (∫ r in Set.Icc 0 s, inner ℝ (hat v F Ψ r ω) (hat v F' Ψ' r ω)) +
      ∫ r in Set.Icc 0 s, inner ℝ (hat v F' Ψ' r ω) (hat v F' Ψ' r ω) := by
    filter_upwards [hae] with ω hω
    obtain ⟨h1, h2, h3⟩ := hω
    have e : ∀ r, ‖hat v F Ψ r ω - hat v F' Ψ' r ω‖ ^ 2 =
        inner ℝ (hat v F Ψ r ω) (hat v F Ψ r ω) - 2 * inner ℝ (hat v F Ψ r ω) (hat v F' Ψ' r ω) +
        inner ℝ (hat v F' Ψ' r ω) (hat v F' Ψ' r ω) := by
      intro r
      rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] <;> ring
    simp only [hD, e]
    exact integral_comb3 (h1 s) (h2 s) (h3 s)
  have hDint : Integrable D P := by
    have := (c11.sub (c12.const_mul 2)).add c22
    exact this.congr (hDe.mono fun ω hω => by simp [hω])
  have hDnn : ∀ ω, 0 ≤ D ω := fun ω => integral_nonneg fun r => sq_nonneg _
  have hq : qn P s (fun r ω => hat v F Ψ r ω - hat v F' Ψ' r ω) = ENNReal.ofReal (∫ ω, D ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hDint (ae_of_all _ hDnn)]
    unfold qn
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    obtain ⟨h1, h2, h3⟩ := hω
    have hint : IntegrableOn (fun r => ‖hat v F Ψ r ω - hat v F' Ψ' r ω‖ ^ 2) (Set.Icc 0 s) := by
      have e : ∀ r, ‖hat v F Ψ r ω - hat v F' Ψ' r ω‖ ^ 2 =
          inner ℝ (hat v F Ψ r ω) (hat v F Ψ r ω) - 2 * inner ℝ (hat v F Ψ r ω) (hat v F' Ψ' r ω) +
          inner ℝ (hat v F' Ψ' r ω) (hat v F' Ψ' r ω) := by
        intro r
        rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] <;> ring
      simp only [e]
      exact ((h1 s).sub ((h2 s).const_mul 2)).add (h3 s)
    rw [hD]
    simp only []
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun r => sq_nonneg _)]
    exact lintegral_congr fun r => enorm_sq_eq_ofReal_norm _
  rw [hL, hq]
  congr 1
  have e1 := hN.integral_eInt_mul hℱ Ψ Ψ s
  have e2 := hN.integral_eInt_mul hℱ Ψ Ψ' s
  have e3 := hN.integral_eInt_mul hℱ Ψ' Ψ' s
  have hIsq := (hI.integrable_sq)
  have hIsq' := (hI'.integrable_sq)
  have hII := hI.integrable_mul hI'
  have : ∫ ω, D ω ∂P = ∫ ω, ((∫ r in Set.Icc 0 s, inner ℝ (hat v F Ψ r ω) (hat v F Ψ r ω)) -
      2 * (∫ r in Set.Icc 0 s, inner ℝ (hat v F Ψ r ω) (hat v F' Ψ' r ω)) +
      ∫ r in Set.Icc 0 s, inner ℝ (hat v F' Ψ' r ω) (hat v F' Ψ' r ω)) ∂P :=
    integral_congr_ae hDe
  rw [this, integral_comb3 c11 c12 c22, ← e1, ← e2, ← e3]
  have : ∫ ω, (eInt N F Ψ s ω - eInt N F' Ψ' s ω) ^ 2 ∂P =
      ∫ ω, (eInt N F Ψ s ω * eInt N F Ψ s ω - 2 * (eInt N F Ψ s ω * eInt N F' Ψ' s ω) +
        eInt N F' Ψ' s ω * eInt N F' Ψ' s ω) ∂P := by
    refine integral_congr_ae (ae_of_all _ fun ω => by ring)
  rw [this]
  exact integral_comb3 (f := fun ω => eInt N F Ψ s ω * eInt N F Ψ s ω)
    (g := fun ω => eInt N F Ψ s ω * eInt N F' Ψ' s ω)
    (h := fun ω => eInt N F' Ψ' s ω * eInt N F' Ψ' s ω)
    (hI.integrable_mul hI) hII (hI'.integrable_mul hI')

/-- The product measure on `[0,s] × Ω`. -/
def tsm (P : Measure Ω) (s : ℝ) : Measure (ℝ × Ω) := (volume.restrict (Set.Icc 0 s)).prod P

instance (P : Measure Ω) [IsProbabilityMeasure P] (s : ℝ) : IsFiniteMeasure (tsm P s) := by
  unfold tsm; infer_instance

lemma tsm_mono {s s' : ℝ} (h : s ≤ s') : tsm P s ≤ tsm P s' := by
  unfold tsm
  exact Measure.prod_mono (Measure.restrict_mono (Set.Icc_subset_Icc_right h) le_rfl) le_rfl

lemma qn_eq {G : ℝ → Ω → K} (hG : Measurable fun p : ℝ × Ω => G p.1 p.2) (s : ℝ) :
    qn P s G = eLpNorm (fun p : ℝ × Ω => G p.1 p.2) 2 (tsm P s) ^ 2 := by
  rw [← HRS.lintegral_enorm_sq_eq_eLpNorm_sq hG.aestronglyMeasurable]
  unfold qn tsm
  rw [lintegral_prod_symm' _ (by fun_prop : Measurable fun p : ℝ × Ω => ‖G p.1 p.2‖ₑ ^ 2)]

lemma measurable_hat (hN : IsNoiseK P ℱ N v) (F : Finset A) (Ψ : SimpleIntegrand ℱ F) :
    Measurable fun p : ℝ × Ω => hat v F Ψ p.1 p.2 := by
  unfold hat
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (((measurable_pi_apply k).comp Ψ.measurable_toFun_joint)).smul (hN.vmeas k.1)

/-- Approximability of an integrand by elementary ones. -/
def Approx (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (v : ℝ → Ω → A → K) (G : ℝ → Ω → K) : Prop :=
  ∀ (n : ℕ) (ε : ℝ≥0∞), 0 < ε → ∃ (F : Finset A) (Ψ : SimpleIntegrand ℱ F),
    eLpNorm (fun p : ℝ × Ω => hat v F Ψ p.1 p.2 - G p.1 p.2) 2 (tsm P n) < ε

/-- A fast approximating sequence. -/
structure ApproxSeq (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (v : ℝ → Ω → A → K)
    (G : ℝ → Ω → K) where
  F : ℕ → Finset A
  Ψ : ∀ m, SimpleIntegrand ℱ (F m)
  rate : ∀ m : ℕ, eLpNorm (fun p : ℝ × Ω => hat v (F m) (Ψ m) p.1 p.2 - G p.1 p.2) 2 (tsm P m) ≤
    (2⁻¹ : ℝ≥0∞) ^ (2 * m + 3)

lemma Approx.exists_seq {G : ℝ → Ω → K} (h : Approx P ℱ v G) : Nonempty (ApproxSeq P ℱ v G) := by
  have : ∀ m : ℕ, ∃ (F : Finset A) (Ψ : SimpleIntegrand ℱ F),
      eLpNorm (fun p : ℝ × Ω => hat v F Ψ p.1 p.2 - G p.1 p.2) 2 (tsm P m) ≤
        (2⁻¹ : ℝ≥0∞) ^ (2 * m + 3) := by
    intro m
    have h2 : (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ (2 * m + 3) :=
      ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _
    obtain ⟨F, Ψ, hFΨ⟩ := h m _ h2
    exact ⟨F, Ψ, hFΨ.le⟩
  choose F Ψ hrate using this
  exact ⟨⟨F, Ψ, hrate⟩⟩

theorem martingale_of_L1_limit {X : ℕ → ℝ → Ω → ℝ} {W : ℝ → Ω → ℝ}
    (hX : ∀ m, Martingale (X m) ℱ P) (hW : ∀ t, StronglyMeasurable[ℱ t] (W t))
    (hWi : ∀ t, Integrable (W t) P)
    (hlim : ∀ t, Tendsto (fun m => ∫⁻ ω, ‖X m t ω - W t ω‖ₑ ∂P) atTop (𝓝 0)) :
    Martingale W ℱ P := by
  refine ⟨hW, fun s t hst => ?_⟩
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hWi t)
    (fun A _ _ => (hWi s).integrableOn) (fun A hA _ => ?_) (hW s).aestronglyMeasurable
  have h1 := tendsto_setIntegral_of_L1 (W s) (hWi s).aestronglyMeasurable (Eventually.of_forall fun m => (hX m).integrable s)
    (hlim s) A
  have h2 := tendsto_setIntegral_of_L1 (W t) (hWi t).aestronglyMeasurable (Eventually.of_forall fun m => (hX m).integrable t)
    (hlim t) A
  have h3 : ∀ m, ∫ ω in A, X m s ω ∂P = ∫ ω in A, X m t ω ∂P := fun m =>
    (hX m).setIntegral_eq hst hA
  simp only [h3] at h1
  exact tendsto_nhds_unique h1 h2

/-- The integral of an approximable integrand, along a fast approximating sequence. -/
structure IsIntOf (N : ℝ → Ω → A → ℝ) {v : ℝ → Ω → A → K} {G : ℝ → Ω → K}
    (seq : ApproxSeq P ℱ v G) (Y : ℝ → Ω → ℝ) : Prop where
  cont : ∀ ω, Continuous fun t => Y t ω
  zero : ∀ t ≤ 0, ∀ ω, Y t ω = 0
  adapted : ∀ t, Measurable[ℱ t] (Y t)
  tendsto : ∀ t, Tendsto (fun m => ∫⁻ ω, ‖eInt N (seq.F m) (seq.Ψ m) t ω - Y t ω‖ₑ ^ 2 ∂P)
    atTop (𝓝 0)

lemma ApproxSeq.hat_sub_le {G : ℝ → Ω → K} (seq : ApproxSeq P ℱ v G) {m n : ℕ} {t : ℝ}
    (htm : t ≤ m) (htn : t ≤ n) :
    eLpNorm (fun p : ℝ × Ω => hat v (seq.F m) (seq.Ψ m) p.1 p.2 - hat v (seq.F n) (seq.Ψ n) p.1 p.2)
      2 (tsm P t) ≤ (2⁻¹ : ℝ≥0∞) ^ (2 * m + 3) + (2⁻¹ : ℝ≥0∞) ^ (2 * n + 3) := by
  have e : (fun p : ℝ × Ω => hat v (seq.F m) (seq.Ψ m) p.1 p.2 - hat v (seq.F n) (seq.Ψ n) p.1 p.2) =
      (fun p : ℝ × Ω => hat v (seq.F m) (seq.Ψ m) p.1 p.2 - G p.1 p.2) +
      (fun p : ℝ × Ω => G p.1 p.2 - hat v (seq.F n) (seq.Ψ n) p.1 p.2) := by
    funext p; simp
  rw [e]
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  refine add_le_add ?_ ?_
  · exact (eLpNorm_mono_measure _ (tsm_mono (P := P) htm)).trans (seq.rate m)
  · calc eLpNorm (fun p : ℝ × Ω => G p.1 p.2 - hat v (seq.F n) (seq.Ψ n) p.1 p.2) 2 (tsm P t)
        ≤ eLpNorm (fun p : ℝ × Ω => G p.1 p.2 - hat v (seq.F n) (seq.Ψ n) p.1 p.2) 2 (tsm P n) :=
          eLpNorm_mono_measure _ (tsm_mono (P := P) htn)
      _ = eLpNorm (fun p : ℝ × Ω => hat v (seq.F n) (seq.Ψ n) p.1 p.2 - G p.1 p.2) 2 (tsm P n) :=
          eLpNorm_sub_comm _ _ _ _
      _ ≤ _ := seq.rate n

lemma pow_inv_two_aux (k : ℕ) : (2 : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ (k + 1) = (2⁻¹ : ℝ≥0∞) ^ k := by
  rw [pow_succ, ← mul_assoc, mul_comm (2 : ℝ≥0∞), mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofNat_ne_top, mul_one]

lemma ApproxSeq.sq_diff_le (hℱ : IsCompleteFiltration P ℱ) (hN : IsNoiseK P ℱ N v)
    {G : ℝ → Ω → K} (hG : Measurable fun p : ℝ × Ω => G p.1 p.2) (seq : ApproxSeq P ℱ v G)
    {m n : ℕ} {t : ℝ} (htm : t ≤ m) (htn : t ≤ n) :
    ∫⁻ ω, ‖eInt N (seq.F m) (seq.Ψ m) t ω - eInt N (seq.F n) (seq.Ψ n) t ω‖ₑ ^ 2 ∂P ≤
      ((2⁻¹ : ℝ≥0∞) ^ (2 * m + 3) + (2⁻¹ : ℝ≥0∞) ^ (2 * n + 3)) ^ 2 := by
  rw [hN.lintegral_eInt_sub_sq hℱ, qn_eq ((measurable_hat hN _ _).sub (measurable_hat hN _ _))]
  exact pow_le_pow_left' (seq.hat_sub_le htm htn) 2

/-- Existence of the integral along an approximating sequence. -/
theorem exists_isIntOf (hℱ : IsCompleteFiltration P ℱ) (hN : IsNoiseK P ℱ N v)
    {G : ℝ → Ω → K} (hG : Measurable fun p : ℝ × Ω => G p.1 p.2) (seq : ApproxSeq P ℱ v G) :
    ∃ Y : ℝ → Ω → ℝ, IsIntOf N seq Y := by
  set I : ℕ → ℝ → Ω → ℝ := fun m => eInt N (seq.F m) (seq.Ψ m) with hI
  have hIm : ∀ m, Martingale (I m) ℱ P := fun m => martingale_nInt hN.noise.mart _ (seq.Ψ m)
  have hI2 : ∀ m t, MemLp (I m t) 2 P := fun m t => memLp_nInt hN.noise.sq _ (seq.Ψ m) t
  have hIc : ∀ m ω, Continuous fun t => I m t ω := fun m ω =>
    continuous_nInt hN.noise.cont _ (seq.Ψ m) ω
  have hIz : ∀ m t, t ≤ 0 → ∀ ω, I m t ω = 0 := fun m t ht ω => nInt_of_nonpos _ _ (seq.Ψ m) ht ω
  have hIa : ∀ m t, Measurable[ℱ t] (I m t) := fun m t => ((hIm m).stronglyAdapted t).measurable
  have hIme : ∀ m t, Measurable (I m t) := fun m t => (hIa m t).mono (ℱ.le t) le_rfl
  set a : ℝ≥0∞ := 2⁻¹ with ha
  have ha1 : a ≤ 1 := by simp [ha]
  have hb : ∀ n N : ℕ, N ≤ n → ∫⁻ ω, ‖I (n + 1) (N : ℝ) ω - I n (N : ℝ) ω‖ₑ ^ 2 ∂P ≤ a ^ (3 * n) := by
    intro n N hNn
    have h1 := seq.sq_diff_le hℱ hN hG (m := n + 1) (n := n) (t := (N : ℝ))
      (by exact_mod_cast hNn.trans (Nat.le_succ n)) (by exact_mod_cast hNn)
    refine h1.trans ?_
    have h2 : a ^ (2 * (n + 1) + 3) + a ^ (2 * n + 3) ≤ a ^ (2 * n + 2) := by
      calc a ^ (2 * (n + 1) + 3) + a ^ (2 * n + 3) ≤ a ^ (2 * n + 3) + a ^ (2 * n + 3) :=
            add_le_add_left (pow_le_pow_right_of_le_one' ha1 (by omega)) _
        _ = 2 * a ^ (2 * n + 3) := (two_mul _).symm
        _ = a ^ (2 * n + 2) := pow_inv_two_aux (2 * n + 2)
    calc (a ^ (2 * (n + 1) + 3) + a ^ (2 * n + 3)) ^ 2 ≤ (a ^ (2 * n + 2)) ^ 2 :=
          pow_le_pow_left' h2 2
      _ = a ^ (4 * n + 4) := by rw [← pow_mul]; ring_nf
      _ ≤ a ^ (3 * n) := pow_le_pow_right_of_le_one' ha1 (by omega)
  have hfast := ae_fast_of_martingales (fun n t ω => I (n + 1) t ω - I n t ω)
    (fun n => (hIm (n + 1)).sub (hIm n)) (fun n t => (hI2 (n + 1) t).sub (hI2 n t))
    (fun n ω => (hIc (n + 1) ω).sub (hIc n ω)) hb
  have hfast' : ∀ᵐ ω ∂P, ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t ∈ Set.Icc (0 : ℝ) N,
      |I (n + 1) t ω - I n t ω| ≤ (2⁻¹ : ℝ) ^ n := hfast
  obtain ⟨Y, hYc, hYz, hYa, hYlim⟩ := exists_continuous_adapted_limit hℱ I hIc hIz hIa hfast'
  refine ⟨Y, hYc, hYz, hYa, fun t => ?_⟩
  have hYm : Measurable (Y t) := (hYa t).mono (ℱ.le t) le_rfl
  -- bound for each large `m` by Fatou
  have hbound : ∀ m : ℕ, t ≤ m → ∫⁻ ω, ‖I m t ω - Y t ω‖ₑ ^ 2 ∂P ≤ a ^ (4 * m + 4) := by
    intro m htm
    have hfat : ∫⁻ ω, ‖I m t ω - Y t ω‖ₑ ^ 2 ∂P ≤
        liminf (fun n => ∫⁻ ω, ‖I m t ω - I n t ω‖ₑ ^ 2 ∂P) atTop := by
      calc ∫⁻ ω, ‖I m t ω - Y t ω‖ₑ ^ 2 ∂P
          = ∫⁻ ω, liminf (fun n => ‖I m t ω - I n t ω‖ₑ ^ 2) atTop ∂P := by
            refine lintegral_congr_ae ?_
            filter_upwards [hYlim] with ω hω
            have h1 : Tendsto (fun n => ‖I m t ω - I n t ω‖ₑ ^ 2) atTop (𝓝 (‖I m t ω - Y t ω‖ₑ ^ 2)) :=
              ((ENNReal.continuous_pow 2).tendsto _).comp
                ((continuous_enorm.tendsto _).comp (tendsto_const_nhds.sub (hω t)))
            exact h1.liminf_eq.symm
        _ ≤ _ := lintegral_liminf_le fun n =>
            (((hIme m t).sub (hIme n t)).enorm.pow_const 2)
    refine hfat.trans ?_
    have hev : ∀ᶠ n in atTop, ∫⁻ ω, ‖I m t ω - I n t ω‖ₑ ^ 2 ∂P ≤ a ^ (4 * m + 4) := by
      filter_upwards [eventually_ge_atTop m] with n hn
      have h1 := seq.sq_diff_le hℱ hN hG (m := m) (n := n) (t := t) htm
        (htm.trans (by exact_mod_cast hn))
      refine h1.trans ?_
      have h2 : a ^ (2 * m + 3) + a ^ (2 * n + 3) ≤ a ^ (2 * m + 2) := by
        calc a ^ (2 * m + 3) + a ^ (2 * n + 3) ≤ a ^ (2 * m + 3) + a ^ (2 * m + 3) :=
              add_le_add_right (pow_le_pow_right_of_le_one' ha1 (by omega)) _
          _ = 2 * a ^ (2 * m + 3) := (two_mul _).symm
          _ = a ^ (2 * m + 2) := pow_inv_two_aux (2 * m + 2)
      calc (a ^ (2 * m + 3) + a ^ (2 * n + 3)) ^ 2 ≤ (a ^ (2 * m + 2)) ^ 2 := pow_le_pow_left' h2 2
        _ = a ^ (4 * m + 4) := by rw [← pow_mul]; ring_nf
    exact (liminf_le_liminf hev).trans_eq (liminf_const _)
  have hlim0 : Tendsto (fun m : ℕ => a ^ (4 * m + 4)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => a ^ k) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by simp [ha])
    exact h1.comp (tendsto_atTop_mono (fun m : ℕ => (by omega : m ≤ 4 * m + 4)) tendsto_id)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim0
    (Eventually.of_forall fun m => bot_le) ?_
  filter_upwards [eventually_ge_atTop ⌈t⌉₊] with m hm
  exact hbound m ((Nat.le_ceil t).trans (by exact_mod_cast hm))

section Limits

variable {α : Type*} {mα : MeasurableSpace α}

lemma eLpNorm_one_inner_le {μ : Measure α} (f g : α → K) :
    eLpNorm (fun x => inner ℝ (f x) (g x)) 1 μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
  have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm_of_pos (μ := μ) (f := f) (g := g)
    (p := 2) (q := 2) (r := 1) (fun x y => inner ℝ x y) 1 (by fun_prop)
    (ae_of_all _ fun x => by
      rw [← NNReal.coe_le_coe]
      simpa using (norm_inner_le_norm (𝕜 := ℝ) (f x) (g x))) (by norm_num)
  simpa using this

lemma eLpNorm_one_mul_le {μ : Measure α} (f g : α → ℝ) :
    eLpNorm (fun x => f x * g x) 1 μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
  have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm_of_pos (μ := μ) (f := f) (g := g)
    (p := 2) (q := 2) (r := 1) (fun x y => x * y) 1 (by fun_prop)
    (ae_of_all _ fun x => by simp [nnnorm_mul]) (by norm_num)
  simpa using this

end Limits

theorem measurable_of_ae_tendsto_complete (hℱ : IsCompleteFiltration P ℱ) (t : ℝ)
    {f : ℕ → Ω → ℝ} (hf : ∀ n, Measurable[ℱ t] (f n)) {W : Ω → ℝ} (hW : Measurable W)
    (h : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (W ω))) : Measurable[ℱ t] W := by
  obtain ⟨C, hCm, hC0, hCG⟩ : ∃ C : Set Ω, MeasurableSet C ∧ P Cᶜ = 0 ∧
      ∀ ω ∈ C, Tendsto (fun n => f n ω) atTop (𝓝 (W ω)) := by
    refine ⟨(toMeasurable P {ω | ¬ Tendsto (fun n => f n ω) atTop (𝓝 (W ω))})ᶜ,
      (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 h
    · intro ω hω
      by_contra hcon
      exact hω (subset_toMeasurable _ _ hcon)
  have hCt : MeasurableSet[ℱ t] C := by
    have := hℱ t Cᶜ hCm.compl hC0
    simpa using this.compl
  have hf' : ∀ n, Measurable[ℱ t] (C.indicator (f n)) := fun n => (hf n).indicator hCt
  have h1 : Measurable[ℱ t] (C.indicator W) := by
    refine @measurable_of_tendsto_metrizable Ω ℝ (ℱ t) _ _ _ _ _ _ hf' ?_
    rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ C
    · simpa [Set.indicator_of_mem hω] using hCG ω hω
    · simp [hω]
  refine hℱ.measurable_of_ae_eq_aux t h1 hW ?_
  filter_upwards [(ae_iff.2 hC0 : ∀ᵐ ω ∂P, ω ∈ C)] with ω hω
  simp [hω]

theorem martingale_of_L1_limit' (hℱ : IsCompleteFiltration P ℱ) {X : ℕ → ℝ → Ω → ℝ}
    {W : ℝ → Ω → ℝ} (hX : ∀ m, Martingale (X m) ℱ P) (hW : ∀ t, Measurable (W t))
    (hlim : ∀ t, Tendsto (fun m => ∫⁻ ω, ‖X m t ω - W t ω‖ₑ ∂P) atTop (𝓝 0)) :
    Martingale W ℱ P := by
  have hWi : ∀ t, Integrable (W t) P := by
    intro t
    obtain ⟨m, hm⟩ := ((tendsto_order.1 (hlim t)).2 1 one_pos).exists
    have h1 : Integrable (fun ω => W t ω - X m t ω) P := by
      refine ⟨((hW t).sub ((hX m).stronglyAdapted t |>.measurable.mono (ℱ.le t) le_rfl)).aestronglyMeasurable,
        ?_⟩
      have : ∫⁻ ω, ‖W t ω - X m t ω‖ₑ ∂P = ∫⁻ ω, ‖X m t ω - W t ω‖ₑ ∂P := by
        refine lintegral_congr fun ω => ?_
        rw [← enorm_neg, neg_sub]
      rw [HasFiniteIntegral, this]
      exact hm.trans ENNReal.one_lt_top
    exact (h1.add ((hX m).integrable t)).congr (ae_of_all _ fun ω => by simp)
  have hXm : ∀ m t, Measurable (X m t) := fun m t =>
    ((hX m).stronglyAdapted t).measurable.mono (ℱ.le t) le_rfl
  refine martingale_of_L1_limit hX (fun t => ?_) hWi hlim
  have hmeas : TendstoInMeasure P (fun m => X m t) atTop (W t) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero ?_
    refine (hlim t).congr (fun m => ?_)
    rw [eLpNorm_one_eq_lintegral_enorm]
    · rfl
    · exact ((hXm m t).sub (hW t)).aestronglyMeasurable
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  exact (measurable_of_ae_tendsto_complete hℱ t (f := fun n => X (ns n) t)
    (fun n => ((hX (ns n)).stronglyAdapted t).measurable) (hW t) hae).stronglyMeasurable

section Pairing

lemma meas_inner {α : Type*} [MeasurableSpace α] {f g : α → K} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun x => inner ℝ (f x) (g x) :=
  Measurable.inner (𝕜 := ℝ) hf hg

lemma tendsto_eLpNorm_pair {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {a b : ℕ → α → K} {a₀ b₀ : α → K}
    (hb₀ : eLpNorm b₀ 2 μ ≠ ∞)
    (h1 : Tendsto (fun m => eLpNorm (a m - a₀) 2 μ) atTop (𝓝 0))
    (h2 : Tendsto (fun m => eLpNorm (b m - b₀) 2 μ) atTop (𝓝 0))
    (ha₀ : eLpNorm a₀ 2 μ ≠ ∞) :
    Tendsto (fun m => eLpNorm (fun x => inner ℝ (a m x) (b m x) - inner ℝ (a₀ x) (b₀ x)) 1 μ)
      atTop (𝓝 0) := by
  have hbound : ∀ m, eLpNorm (fun x => inner ℝ (a m x) (b m x) - inner ℝ (a₀ x) (b₀ x)) 1 μ ≤
      eLpNorm (a m - a₀) 2 μ * (eLpNorm (b m - b₀) 2 μ + eLpNorm b₀ 2 μ) +
        eLpNorm a₀ 2 μ * eLpNorm (b m - b₀) 2 μ := by
    intro m
    have e : (fun x => inner ℝ (a m x) (b m x) - inner ℝ (a₀ x) (b₀ x)) =
        (fun x => inner ℝ ((a m - a₀) x) (b m x)) + (fun x => inner ℝ (a₀ x) ((b m - b₀) x)) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply, inner_sub_left, inner_sub_right]
      ring
    rw [e]
    refine (eLpNorm_add_le (by norm_num)).trans (add_le_add ?_ ?_)
    · refine (eLpNorm_one_inner_le (μ := μ) (a m - a₀) (b m)).trans ?_
      refine mul_le_mul_right ?_ _
      have : b m = (b m - b₀) + b₀ := by simp
      calc eLpNorm (b m) 2 μ = eLpNorm ((b m - b₀) + b₀) 2 μ := by rw [← this]
        _ ≤ _ := eLpNorm_add_le (by norm_num)
    · exact eLpNorm_one_inner_le (μ := μ) a₀ (b m - b₀)
  have hlim : Tendsto (fun m => eLpNorm (a m - a₀) 2 μ * (eLpNorm (b m - b₀) 2 μ + eLpNorm b₀ 2 μ) +
        eLpNorm a₀ 2 μ * eLpNorm (b m - b₀) 2 μ) atTop (𝓝 0) := by
    have t1 : Tendsto (fun m => eLpNorm (b m - b₀) 2 μ + eLpNorm b₀ 2 μ) atTop
        (𝓝 (0 + eLpNorm b₀ 2 μ)) := h2.add tendsto_const_nhds
    have t2 := ENNReal.Tendsto.mul h1 (Or.inr (by simpa using hb₀)) t1 (Or.inr (by simp))
    have t3 := ENNReal.Tendsto.const_mul h2 (Or.inr ha₀) (a := eLpNorm a₀ 2 μ)
    simpa using t2.add t3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun m => bot_le) hbound

theorem tendsto_lintegral_compensator {a b : ℕ → ℝ → Ω → K} {a₀ b₀ : ℝ → Ω → K} (t : ℝ)
    (ha : ∀ m, Measurable fun p : ℝ × Ω => a m p.1 p.2)
    (hb : ∀ m, Measurable fun p : ℝ × Ω => b m p.1 p.2)
    (ha₀ : Measurable fun p : ℝ × Ω => a₀ p.1 p.2) (hb₀ : Measurable fun p : ℝ × Ω => b₀ p.1 p.2)
    (hfa : ∀ m, eLpNorm (fun p : ℝ × Ω => a m p.1 p.2) 2 (tsm P t) ≠ ∞)
    (hfb : ∀ m, eLpNorm (fun p : ℝ × Ω => b m p.1 p.2) 2 (tsm P t) ≠ ∞)
    (hfa₀ : eLpNorm (fun p : ℝ × Ω => a₀ p.1 p.2) 2 (tsm P t) ≠ ∞)
    (hfb₀ : eLpNorm (fun p : ℝ × Ω => b₀ p.1 p.2) 2 (tsm P t) ≠ ∞)
    (h1 : Tendsto (fun m => eLpNorm (fun p : ℝ × Ω => a m p.1 p.2 - a₀ p.1 p.2) 2 (tsm P t))
      atTop (𝓝 0))
    (h2 : Tendsto (fun m => eLpNorm (fun p : ℝ × Ω => b m p.1 p.2 - b₀ p.1 p.2) 2 (tsm P t))
      atTop (𝓝 0)) :
    Tendsto (fun m => ∫⁻ ω, ‖(∫ r in Set.Icc 0 t, inner ℝ (a m r ω) (b m r ω)) -
      ∫ r in Set.Icc 0 t, inner ℝ (a₀ r ω) (b₀ r ω)‖ₑ ∂P) atTop (𝓝 0) := by
  have hconv := tendsto_eLpNorm_pair (μ := tsm P t) (a := fun (m : ℕ) (p : ℝ × Ω) => a m p.1 p.2)
    (b := fun (m : ℕ) (p : ℝ × Ω) => b m p.1 p.2) (a₀ := fun p : ℝ × Ω => a₀ p.1 p.2)
    (b₀ := fun p : ℝ × Ω => b₀ p.1 p.2) hfb₀ h1 h2 hfa₀
  have hint : ∀ {a' b' : ℝ → Ω → K}, (Measurable fun p : ℝ × Ω => a' p.1 p.2) →
      (Measurable fun p : ℝ × Ω => b' p.1 p.2) →
      eLpNorm (fun p : ℝ × Ω => a' p.1 p.2) 2 (tsm P t) ≠ ∞ →
      eLpNorm (fun p : ℝ × Ω => b' p.1 p.2) 2 (tsm P t) ≠ ∞ →
      Integrable (fun p : ℝ × Ω => inner ℝ (a' p.1 p.2) (b' p.1 p.2)) (tsm P t) := by
    intro a' b' ha' hb' hfa' hfb'
    have hm : AEStronglyMeasurable (fun p : ℝ × Ω => inner ℝ (a' p.1 p.2) (b' p.1 p.2))
        (tsm P t) := (meas_inner ha' hb').aestronglyMeasurable
    refine ⟨hm, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have := lt_of_le_of_lt (eLpNorm_one_inner_le (μ := tsm P t)
      (fun p : ℝ × Ω => a' p.1 p.2) (fun p : ℝ × Ω => b' p.1 p.2))
      (ENNReal.mul_lt_top hfa'.lt_top hfb'.lt_top)
    rwa [eLpNorm_one_eq_lintegral_enorm hm] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv (fun m => bot_le)
    (fun m => ?_)
  have hm := hint (ha m) (hb m) (hfa m) (hfb m)
  have h0 := hint ha₀ hb₀ hfa₀ hfb₀
  have hae := (hm.prod_left_ae).and (h0.prod_left_ae)
  calc ∫⁻ ω, ‖(∫ r in Set.Icc 0 t, inner ℝ (a m r ω) (b m r ω)) -
        ∫ r in Set.Icc 0 t, inner ℝ (a₀ r ω) (b₀ r ω)‖ₑ ∂P
      ≤ ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ‖inner ℝ (a m r ω) (b m r ω) -
          inner ℝ (a₀ r ω) (b₀ r ω)‖ₑ) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with ω ⟨e1, e2⟩
        rw [← integral_sub e1 e2]
        exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ p, ‖inner ℝ (a m p.1 p.2) (b m p.1 p.2) - inner ℝ (a₀ p.1 p.2) (b₀ p.1 p.2)‖ₑ ∂(tsm P t) := by
        unfold tsm
        rw [lintegral_prod_symm' _ (by
          exact ((meas_inner (ha m) (hb m)).sub (meas_inner ha₀ hb₀)).enorm)]
    _ = eLpNorm (fun p : ℝ × Ω => inner ℝ (a m p.1 p.2) (b m p.1 p.2) -
          inner ℝ (a₀ p.1 p.2) (b₀ p.1 p.2)) 1 (tsm P t) := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        exact ((meas_inner (ha m) (hb m)).sub (meas_inner ha₀ hb₀)).aestronglyMeasurable

end Pairing

lemma tendsto_of_tendsto_sq {x : ℕ → ℝ≥0∞} (h : Tendsto (fun m => x m ^ 2) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) := by
  have h1 := ((ENNReal.continuous_rpow_const (y := (2⁻¹ : ℝ))).tendsto 0).comp h
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h1
  refine h1.congr (fun m => ?_)
  simp only [Function.comp_apply]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

lemma zeroSimple_hat (v : ℝ → Ω → A → K) (F : Finset A) (r : ℝ) (ω : Ω) :
    hat v F (zeroSimple ℱ : SimpleIntegrand ℱ F) r ω = 0 := by
  simp [hat, SimpleIntegrand.toFun, zeroSimple]

lemma zeroSimple_eInt (N : ℝ → Ω → A → ℝ) (F : Finset A) (t : ℝ) (ω : Ω) :
    eInt N F (zeroSimple ℱ : SimpleIntegrand ℱ F) t ω = 0 := by
  simp [eInt, nInt, zeroSimple]

theorem eLpNorm_hat_lt_top (hℱ : IsCompleteFiltration P ℱ) (hN : IsNoiseK P ℱ N v) (F : Finset A)
    (Ψ : SimpleIntegrand ℱ F) (t : ℝ) :
    eLpNorm (fun p : ℝ × Ω => hat v F Ψ p.1 p.2) 2 (tsm P t) < ∞ := by
  have h := hN.lintegral_eInt_sub_sq hℱ Ψ (zeroSimple ℱ : SimpleIntegrand ℱ F) t
  simp only [zeroSimple_eInt, sub_zero, zeroSimple_hat] at h
  have hm := measurable_hat hN F Ψ
  have h2 : qn P t (hat v F Ψ) = eLpNorm (fun p : ℝ × Ω => hat v F Ψ p.1 p.2) 2 (tsm P t) ^ 2 :=
    qn_eq hm t
  have h3 : ∫⁻ ω, ‖eInt N F Ψ t ω‖ₑ ^ 2 ∂P < ∞ :=
    HRS.lintegral_enorm_sq_lt_top (memLp_nInt hN.noise.sq _ Ψ t)
  rw [h, h2] at h3
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon] at h3
  simp at h3

lemma ApproxSeq.tendsto_eLpNorm {G : ℝ → Ω → K} (seq : ApproxSeq P ℱ v G) (t : ℝ) :
    Tendsto (fun m => eLpNorm (fun p : ℝ × Ω => hat v (seq.F m) (seq.Ψ m) p.1 p.2 - G p.1 p.2) 2
      (tsm P t)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun m : ℕ => (2⁻¹ : ℝ≥0∞) ^ (2 * m + 3)) atTop (𝓝 0) :=
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by simp)).comp
      (tendsto_atTop_mono (fun m : ℕ => (by omega : m ≤ 2 * m + 3)) tendsto_id)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun m => bot_le) ?_
  filter_upwards [eventually_ge_atTop ⌈t⌉₊] with m hm
  have htm : t ≤ m := (Nat.le_ceil t).trans (by exact_mod_cast hm)
  exact (eLpNorm_mono_measure _ (tsm_mono (P := P) htm)).trans (seq.rate m)

lemma ApproxSeq.eLpNorm_G_ne_top (hℱ : IsCompleteFiltration P ℱ) (hN : IsNoiseK P ℱ N v)
    {G : ℝ → Ω → K} (seq : ApproxSeq P ℱ v G) (t : ℝ) :
    eLpNorm (fun p : ℝ × Ω => G p.1 p.2) 2 (tsm P t) ≠ ∞ := by
  obtain ⟨m, hm⟩ := ((tendsto_order.1 (seq.tendsto_eLpNorm t)).2 1 one_pos).exists
  have h1 := eLpNorm_hat_lt_top hℱ hN (seq.F m) (seq.Ψ m) t
  have e : (fun p : ℝ × Ω => G p.1 p.2) =
      (fun p : ℝ × Ω => hat v (seq.F m) (seq.Ψ m) p.1 p.2) -
        (fun p : ℝ × Ω => hat v (seq.F m) (seq.Ψ m) p.1 p.2 - G p.1 p.2) := by
    funext p; simp
  rw [e]
  refine ne_of_lt (lt_of_le_of_lt (eLpNorm_sub_le (by norm_num)) ?_)
  exact ENNReal.add_lt_top.2 ⟨h1, hm.trans ENNReal.one_lt_top⟩

section IntProps

variable {G : ℝ → Ω → K} {seq : ApproxSeq P ℱ v G} {Y : ℝ → Ω → ℝ}

lemma measurable_eInt (hN : IsNoiseK P ℱ N v) (F : Finset A) (Ψ : SimpleIntegrand ℱ F) (t : ℝ) :
    Measurable (eInt N F Ψ t) :=
  ((martingale_nInt hN.noise.mart (fun k : F => k.1) Ψ).stronglyAdapted t).measurable.mono
    (ℱ.le t) le_rfl

lemma IsIntOf.measurable (hY : IsIntOf N seq Y) (t : ℝ) : Measurable (Y t) :=
  (hY.adapted t).mono (ℱ.le t) le_rfl

lemma IsIntOf.sq_eq (hN : IsNoiseK P ℱ N v) (hY : IsIntOf N seq Y) (t : ℝ) (m : ℕ) :
    ∫⁻ ω, ‖eInt N (seq.F m) (seq.Ψ m) t ω - Y t ω‖ₑ ^ 2 ∂P =
      eLpNorm (fun ω => eInt N (seq.F m) (seq.Ψ m) t ω - Y t ω) 2 P ^ 2 :=
  HRS.lintegral_enorm_sq_eq_eLpNorm_sq
    ((measurable_eInt hN _ _ t).sub (hY.measurable t)).aestronglyMeasurable

lemma IsIntOf.tendsto_eLpNorm (hN : IsNoiseK P ℱ N v) (hY : IsIntOf N seq Y) (t : ℝ) :
    Tendsto (fun m => eLpNorm (fun ω => eInt N (seq.F m) (seq.Ψ m) t ω - Y t ω) 2 P) atTop
      (𝓝 0) :=
  tendsto_of_tendsto_sq ((hY.tendsto t).congr (fun m => hY.sq_eq hN t m))

lemma IsIntOf.memLp (hN : IsNoiseK P ℱ N v) (hY : IsIntOf N seq Y) (t : ℝ) :
    MemLp (Y t) 2 P := by
  obtain ⟨m, hm⟩ := ((tendsto_order.1 (hY.tendsto_eLpNorm hN t)).2 1 one_pos).exists
  have hI : MemLp (eInt N (seq.F m) (seq.Ψ m) t) 2 P := memLp_nInt hN.noise.sq _ (seq.Ψ m) t
  have e : Y t = (eInt N (seq.F m) (seq.Ψ m) t) -
      (fun ω => eInt N (seq.F m) (seq.Ψ m) t ω - Y t ω) := by funext ω; simp
  show eLpNorm (Y t) 2 P < ∞
  rw [e]
  exact lt_of_le_of_lt (eLpNorm_sub_le (by norm_num))
    (ENNReal.add_lt_top.2 ⟨hI, hm.trans ENNReal.one_lt_top⟩)

lemma IsIntOf.tendsto_lintegral_one (hN : IsNoiseK P ℱ N v) (hY : IsIntOf N seq Y) (t : ℝ) :
    Tendsto (fun m => ∫⁻ ω, ‖eInt N (seq.F m) (seq.Ψ m) t ω - Y t ω‖ₑ ∂P) atTop (𝓝 0) := by
  have h := hY.tendsto_eLpNorm hN t
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun m => bot_le)
    (fun m => ?_)
  have h1 := eLpNorm_le_eLpNorm_of_exponent_le (μ := P)
    (f := fun ω => eInt N (seq.F m) (seq.Ψ m) t ω - Y t ω) (p := 1) (q := 2) (by norm_num)
  have h2 := eLpNorm_one_eq_lintegral_enorm (μ := P)
    (f := fun ω => eInt N (seq.F m) (seq.Ψ m) t ω - Y t ω)
    ((measurable_eInt hN (seq.F m) (seq.Ψ m) t).sub (hY.measurable t)).aestronglyMeasurable
  exact h2.symm.le.trans h1

theorem IsIntOf.martingale (hℱ : IsCompleteFiltration P ℱ) (hN : IsNoiseK P ℱ N v)
    (hY : IsIntOf N seq Y) : Martingale Y ℱ P :=
  martingale_of_L1_limit' hℱ (X := fun m => eInt N (seq.F m) (seq.Ψ m))
    (fun m => martingale_nInt hN.noise.mart _ (seq.Ψ m)) (fun t => hY.measurable t)
    (fun t => hY.tendsto_lintegral_one hN t)

end IntProps

section BracketProps

variable {G : ℝ → Ω → K} {seq : ApproxSeq P ℱ v G} {Y : ℝ → Ω → ℝ}

/-- Real-valued version of `tendsto_eLpNorm_pair`. -/
lemma tendsto_eLpNorm_mul_pair {a b : ℕ → Ω → ℝ} {a₀ b₀ : Ω → ℝ}
    (hb₀ : eLpNorm b₀ 2 P ≠ ∞) (ha₀ : eLpNorm a₀ 2 P ≠ ∞)
    (h1 : Tendsto (fun m => eLpNorm (a m - a₀) 2 P) atTop (𝓝 0))
    (h2 : Tendsto (fun m => eLpNorm (b m - b₀) 2 P) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (fun ω => a m ω * b m ω - a₀ ω * b₀ ω) 1 P) atTop (𝓝 0) := by
  have h := tendsto_eLpNorm_pair (K := ℝ) (μ := P) (a := a) (b := b) (a₀ := a₀) (b₀ := b₀)
    hb₀ h1 h2 ha₀
  refine h.congr (fun m => ?_)
  congr 1
  funext ω
  simp [mul_comm]

/-- Passage to the limit in compensated products. -/
theorem martingale_of_product_limit (hℱ : IsCompleteFiltration P ℱ)
    {A B : ℕ → ℝ → Ω → ℝ} {A₀ B₀ : ℝ → Ω → ℝ} {a b : ℕ → ℝ → Ω → K} {a₀ b₀ : ℝ → Ω → K}
    (hX : ∀ m, Martingale (fun t ω => A m t ω * B m t ω -
      ∫ r in Set.Icc 0 t, inner ℝ (a m r ω) (b m r ω)) ℱ P)
    (hAm : ∀ m t, Measurable (A m t)) (hBm : ∀ m t, Measurable (B m t))
    (hA₀ : ∀ t, Measurable (A₀ t)) (hB₀ : ∀ t, Measurable (B₀ t))
    (hAf : ∀ t, eLpNorm (A₀ t) 2 P ≠ ∞) (hBf : ∀ t, eLpNorm (B₀ t) 2 P ≠ ∞)
    (hA : ∀ t, Tendsto (fun m => eLpNorm (A m t - A₀ t) 2 P) atTop (𝓝 0))
    (hB : ∀ t, Tendsto (fun m => eLpNorm (B m t - B₀ t) 2 P) atTop (𝓝 0))
    (ha : ∀ m, Measurable fun p : ℝ × Ω => a m p.1 p.2)
    (hb : ∀ m, Measurable fun p : ℝ × Ω => b m p.1 p.2)
    (ha₀ : Measurable fun p : ℝ × Ω => a₀ p.1 p.2) (hb₀ : Measurable fun p : ℝ × Ω => b₀ p.1 p.2)
    (hfa : ∀ m t, eLpNorm (fun p : ℝ × Ω => a m p.1 p.2) 2 (tsm P t) ≠ ∞)
    (hfb : ∀ m t, eLpNorm (fun p : ℝ × Ω => b m p.1 p.2) 2 (tsm P t) ≠ ∞)
    (hfa₀ : ∀ t, eLpNorm (fun p : ℝ × Ω => a₀ p.1 p.2) 2 (tsm P t) ≠ ∞)
    (hfb₀ : ∀ t, eLpNorm (fun p : ℝ × Ω => b₀ p.1 p.2) 2 (tsm P t) ≠ ∞)
    (h1 : ∀ t, Tendsto (fun m => eLpNorm (fun p : ℝ × Ω => a m p.1 p.2 - a₀ p.1 p.2) 2 (tsm P t))
      atTop (𝓝 0))
    (h2 : ∀ t, Tendsto (fun m => eLpNorm (fun p : ℝ × Ω => b m p.1 p.2 - b₀ p.1 p.2) 2 (tsm P t))
      atTop (𝓝 0)) :
    Martingale (fun t ω => A₀ t ω * B₀ t ω - ∫ r in Set.Icc 0 t, inner ℝ (a₀ r ω) (b₀ r ω)) ℱ P := by
  refine martingale_of_L1_limit' hℱ hX (fun t => ?_) (fun t => ?_)
  · exact ((hA₀ t).mul (hB₀ t)).sub (measurable_setIntegral_Icc (g := fun r ω => inner ℝ (a₀ r ω) (b₀ r ω))
      (meas_inner ha₀ hb₀) t)
  · -- the two error terms
    have hAB := tendsto_eLpNorm_mul_pair (P := P) (a := fun m => A m t) (b := fun m => B m t)
      (a₀ := A₀ t) (b₀ := B₀ t) (hBf t) (hAf t) (hA t) (hB t)
    have hcomp := tendsto_lintegral_compensator (P := P) (a := a) (b := b) (a₀ := a₀) (b₀ := b₀) t
      ha hb ha₀ hb₀ (fun m => hfa m t) (fun m => hfb m t) (hfa₀ t) (hfb₀ t) (h1 t) (h2 t)
    have hsum := hAB.add hcomp
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun m => bot_le)
      (fun m => ?_)
    have mAB : Measurable fun ω => A m t ω * B m t ω - A₀ t ω * B₀ t ω :=
      ((hAm m t).mul (hBm m t)).sub ((hA₀ t).mul (hB₀ t))
    have mC : Measurable fun ω => (∫ r in Set.Icc 0 t, inner ℝ (a m r ω) (b m r ω)) -
        ∫ r in Set.Icc 0 t, inner ℝ (a₀ r ω) (b₀ r ω) :=
      (measurable_setIntegral_Icc (g := fun r ω => inner ℝ (a m r ω) (b m r ω))
        (meas_inner (ha m) (hb m)) t).sub
        (measurable_setIntegral_Icc (g := fun r ω => inner ℝ (a₀ r ω) (b₀ r ω))
          (meas_inner ha₀ hb₀) t)
    have e1 : ∫⁻ ω, ‖A m t ω * B m t ω - A₀ t ω * B₀ t ω‖ₑ ∂P =
        eLpNorm (fun ω => A m t ω * B m t ω - A₀ t ω * B₀ t ω) 1 P := by
      rw [eLpNorm_one_eq_lintegral_enorm mAB.aestronglyMeasurable]
    calc ∫⁻ ω, ‖(A m t ω * B m t ω - ∫ r in Set.Icc 0 t, inner ℝ (a m r ω) (b m r ω)) -
          (A₀ t ω * B₀ t ω - ∫ r in Set.Icc 0 t, inner ℝ (a₀ r ω) (b₀ r ω))‖ₑ ∂P
        ≤ ∫⁻ ω, (‖A m t ω * B m t ω - A₀ t ω * B₀ t ω‖ₑ +
            ‖(∫ r in Set.Icc 0 t, inner ℝ (a m r ω) (b m r ω)) -
              ∫ r in Set.Icc 0 t, inner ℝ (a₀ r ω) (b₀ r ω)‖ₑ) ∂P := by
          refine lintegral_mono fun ω => ?_
          have : (A m t ω * B m t ω - ∫ r in Set.Icc 0 t, inner ℝ (a m r ω) (b m r ω)) -
              (A₀ t ω * B₀ t ω - ∫ r in Set.Icc 0 t, inner ℝ (a₀ r ω) (b₀ r ω)) =
              (A m t ω * B m t ω - A₀ t ω * B₀ t ω) -
              ((∫ r in Set.Icc 0 t, inner ℝ (a m r ω) (b m r ω)) -
                ∫ r in Set.Icc 0 t, inner ℝ (a₀ r ω) (b₀ r ω)) := by ring
          rw [this]
          exact enorm_sub_le
      _ = ∫⁻ ω, ‖A m t ω * B m t ω - A₀ t ω * B₀ t ω‖ₑ ∂P +
          ∫⁻ ω, ‖(∫ r in Set.Icc 0 t, inner ℝ (a m r ω) (b m r ω)) -
            ∫ r in Set.Icc 0 t, inner ℝ (a₀ r ω) (b₀ r ω)‖ₑ ∂P :=
          lintegral_add_left mAB.enorm _
      _ = _ := by rw [e1]

/-- Compensated product of two integrals. -/
theorem IsIntOf.bracket (hℱ : IsCompleteFiltration P ℱ) (hN : IsNoiseK P ℱ N v)
    {G G' : ℝ → Ω → K} (hG : Measurable fun p : ℝ × Ω => G p.1 p.2)
    (hG' : Measurable fun p : ℝ × Ω => G' p.1 p.2)
    {seq : ApproxSeq P ℱ v G} {seq' : ApproxSeq P ℱ v G'} {Y Y' : ℝ → Ω → ℝ}
    (hY : IsIntOf N seq Y) (hY' : IsIntOf N seq' Y') :
    Martingale (fun t ω => Y t ω * Y' t ω - ∫ r in Set.Icc 0 t, inner ℝ (G r ω) (G' r ω)) ℱ P := by
  have hX : ∀ m, Martingale (fun t ω => eInt N (seq.F m) (seq.Ψ m) t ω *
      eInt N (seq'.F m) (seq'.Ψ m) t ω -
      ∫ r in Set.Icc 0 t, inner ℝ (hat v (seq.F m) (seq.Ψ m) r ω) (hat v (seq'.F m) (seq'.Ψ m) r ω))
      ℱ P := by
    intro m
    have h := martingale_nInt_mul_nInt hℱ hN.noise (fun k : seq.F m => k.1)
      (fun l : seq'.F m => l.1) (seq.Ψ m) (seq'.Ψ m)
    have e : (fun t ω => eInt N (seq.F m) (seq.Ψ m) t ω * eInt N (seq'.F m) (seq'.Ψ m) t ω -
        ∫ r in Set.Icc 0 t, inner ℝ (hat v (seq.F m) (seq.Ψ m) r ω)
          (hat v (seq'.F m) (seq'.Ψ m) r ω)) =
        (fun s ω => nInt N (fun k : seq.F m => k.1) (seq.Ψ m) s ω *
          nInt N (fun l : seq'.F m => l.1) (seq'.Ψ m) s ω -
        ∫ r in Set.Icc 0 s, ∑ k : seq.F m, ∑ l : seq'.F m, (seq.Ψ m).toFun r ω k *
          (seq'.Ψ m).toFun r ω l * inner ℝ (v r ω k.1) (v r ω l.1)) := by
      funext t ω
      simp only [eInt]
      rw [← hN.compensator_eq]
    rw [e]; exact h
  exact martingale_of_product_limit hℱ hX (fun m t => measurable_eInt hN _ _ t)
    (fun m t => measurable_eInt hN _ _ t) (fun t => hY.measurable t) (fun t => hY'.measurable t)
    (fun t => (hY.memLp hN t).eLpNorm_ne_top) (fun t => (hY'.memLp hN t).eLpNorm_ne_top)
    (fun t => hY.tendsto_eLpNorm hN t) (fun t => hY'.tendsto_eLpNorm hN t)
    (fun m => measurable_hat hN _ _) (fun m => measurable_hat hN _ _) hG hG'
    (fun m t => (eLpNorm_hat_lt_top hℱ hN _ _ t).ne) (fun m t => (eLpNorm_hat_lt_top hℱ hN _ _ t).ne)
    (fun t => seq.eLpNorm_G_ne_top hℱ hN t) (fun t => seq'.eLpNorm_G_ne_top hℱ hN t)
    (fun t => seq.tendsto_eLpNorm t) (fun t => seq'.tendsto_eLpNorm t)

/-- Cross covariation of an integral with a test martingale. -/
theorem IsIntOf.cross (hℱ : IsCompleteFiltration P ℱ) (hN : IsNoiseK P ℱ N v)
    {G : ℝ → Ω → K} (hG : Measurable fun p : ℝ × Ω => G p.1 p.2) {seq : ApproxSeq P ℱ v G}
    {Y : ℝ → Ω → ℝ} (hY : IsIntOf N seq Y)
    {V : ℝ → Ω → ℝ} (hV : Martingale V ℱ P) (hV2 : ∀ t, MemLp (V t) 2 P)
    {w : ℝ → Ω → K} (hw : Measurable fun p : ℝ × Ω => w p.1 p.2)
    (hw2 : ∀ t, eLpNorm (fun p : ℝ × Ω => w p.1 p.2) 2 (tsm P t) ≠ ∞)
    (hwi : ∀ᵐ ω ∂P, ∀ (α : A) (t : ℝ), IntegrableOn (fun r => inner ℝ (v r ω α) (w r ω))
      (Set.Icc 0 t))
    (hVw : ∀ α, Martingale (fun t ω => N t ω α * V t ω -
      ∫ r in Set.Icc 0 t, inner ℝ (v r ω α) (w r ω)) ℱ P) :
    Martingale (fun t ω => Y t ω * V t ω - ∫ r in Set.Icc 0 t, inner ℝ (G r ω) (w r ω)) ℱ P := by
  have hX : ∀ m, Martingale (fun t ω => eInt N (seq.F m) (seq.Ψ m) t ω * V t ω -
      ∫ r in Set.Icc 0 t, inner ℝ (hat v (seq.F m) (seq.Ψ m) r ω) (w r ω)) ℱ P := by
    intro m
    have h := martingale_nInt_mul hℱ hN.noise.mart hN.noise.sq (fun k : seq.F m => k.1)
      (seq.Ψ m) hV hV2 (q := fun k r ω => inner ℝ (v r ω k.1) (w r ω))
      (fun k => meas_inner (hN.vmeas k.1 |>.comp measurable_id) (by exact hw))
      (by filter_upwards [hwi] with ω hω k t using hω k.1 t)
      (fun k => hVw k.1)
    have e : (fun t ω => eInt N (seq.F m) (seq.Ψ m) t ω * V t ω -
        ∫ r in Set.Icc 0 t, inner ℝ (hat v (seq.F m) (seq.Ψ m) r ω) (w r ω)) =
        (fun s ω => nInt N (fun k : seq.F m => k.1) (seq.Ψ m) s ω * V s ω -
        ∫ r in Set.Icc 0 s, ∑ k : seq.F m, (seq.Ψ m).toFun r ω k *
          inner ℝ (v r ω k.1) (w r ω)) := by
      funext t ω
      simp only [eInt]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun r => ?_)
      simp only [hat, sum_inner, real_inner_smul_left]
    rw [e]; exact h
  exact martingale_of_product_limit hℱ hX (fun m t => measurable_eInt hN _ _ t)
    (fun m t => ((hV.stronglyAdapted t).measurable.mono (ℱ.le t) le_rfl))
    (fun t => hY.measurable t) (fun t => ((hV.stronglyAdapted t).measurable.mono (ℱ.le t) le_rfl))
    (fun t => (hY.memLp hN t).eLpNorm_ne_top) (fun t => (hV2 t).eLpNorm_ne_top)
    (fun t => hY.tendsto_eLpNorm hN t)
    (fun t => by simpa using tendsto_const_nhds (x := (0 : ℝ≥0∞)))
    (fun m => measurable_hat hN _ _) (fun m => hw) hG hw
    (fun m t => (eLpNorm_hat_lt_top hℱ hN _ _ t).ne) (fun m t => hw2 t)
    (fun t => seq.eLpNorm_G_ne_top hℱ hN t) hw2
    (fun t => seq.tendsto_eLpNorm t)
    (fun t => by simpa using tendsto_const_nhds (x := (0 : ℝ≥0∞)))

end BracketProps

end Closure

end HRS.MRep
