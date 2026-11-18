import HRS.Whole.AppendixALemmas2
import HRS.MP.PropIncr
import HRS.MP.KernIncr
import HRS.Main.A9Final
import HRS.Main.A8PAux13
import HRS.Stochastic.BDG

/-!
# Packet MPMART (stage 1): the fourth moment of the thermal stochastic convolution (S.A.24, torus)

The first conjunct of `HRS.Whole.AppendixALemmas.path_martingale_modulus_torus`:
`E‖𝕄_N^t - 𝕄_N^s‖⁴_{H_q} ≤ C|t-s|²`, `q = qT d = ℓ + d + 2` with `ℓ = mStar d + 3`.

Route.  For each mode `k` the pairing `⟨e_k, 𝕄^t - 𝕄^{s'}⟩` is `σ` times an Itô integral
(`IsStochConvT`, linearity of `itoIntegral`, the integrand of `M^{s'}` vanishes after `s'`); BDG (`p = 4`)
and the sup bounds `sup_x|∇U^{r,t}e_k| ≤ C jp_k^ℓ`, `sup_x|∇(U^{r,t}-U^{r,s'})e_k| ≤ C|t-s'| jp_k^ℓ`
(Sobolev embedding `H^{ℓ-2} ⊂ C¹` and `HRS.MP.PropIncr.mpi_main`) give
`E|⟨e_k, ·⟩|⁴ ≲ jp_k^{4ℓ}|t-s'|²`.  Summing over `k` with the weights `jp_k^{-2q}` uses a weighted
Cauchy–Schwarz in `ℝ≥0∞` and `Σ_k jp_k^{-3d-7} < ∞`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MP.MartMod

open HRS HRS.PDE HRS.Whole.AppendixALemmas HRS.MP.KernIncr

variable {d : ℕ}

/-! ### Stage 1: deterministic sup bounds at the level `ℓ = m2 + 2` -/

theorem mmm_pde (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m2 : ℕ)
    (hm : mStar d ≤ m2 + 2) (hm2 : (d : ℝ) / 2 + 1 < m2) (Rg : Regime)
    (ν₀ MB Λ T VB νbar : ℝ) :
    ∃ C₂ C₃ : ℝ, 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ ∀ (D : DynData d) (μ : ℝ → Torus d → ℝ),
      AdjointData s (m2 + 2) Rg MB Λ VB D ν₀ T μ → D.invβ ≤ νbar → ∀ (j : Fin d) (x : Torus d),
      (∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
        |Torus.grad (propagator D μ r t φ) x j| ≤ C₂ * sobolevNorm (((m2 + 2 : ℕ)) : ℝ) φ) ∧
      (∀ r s' t : ℝ, 0 ≤ r → r ≤ s' → s' ≤ t → t ≤ T → ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
        |Torus.grad (propagator D μ r t φ) x j - Torus.grad (propagator D μ r s' φ) x j| ≤
          C₃ * |t - s'| * sobolevNorm (((m2 + 2 : ℕ)) : ℝ) φ) := by
  obtain ⟨K, hK1, hKf⟩ := mpk_prop_facts hd s hs0 hsd (m2 + 2) hm Rg MB Λ VB ν₀ T
  have hq1 : (d : ℝ) / 2 + 1 < (((m2 + 2 : ℕ)) : ℝ) := by
    push_cast; linarith
  obtain ⟨Cs1, hCs1, hgq⟩ := mpk_grad_sup_le (d := d) (m2 + 2) hq1
  obtain ⟨Cs2, hCs2, hgg⟩ := mpk_grad_sup_le (d := d) m2 hm2
  obtain ⟨C1, hC1⟩ := PropIncr.mpi_main hd s hs0 hsd m2 hm Rg MB Λ VB νbar ν₀ T
  refine ⟨Cs1 * K, Cs2 * |C1|, by positivity, by positivity, ?_⟩
  intro D μ hA hν j x
  refine ⟨?_, ?_⟩
  · intro r t hr hrt htT φ hφ
    obtain ⟨hck, hmem, hn⟩ := hKf D μ hA r t hr hrt htT φ hφ
    refine (mpk_abs_grad_le _ x j).trans ((hgq _ hmem (mpk_isCk_one hck) x).trans ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hn hCs1
  · intro r s' t hr hrs hst htT φ hφ
    obtain ⟨hckt, hmemt, -⟩ := hKf D μ hA r t hr (hrs.trans hst) htT φ hφ
    obtain ⟨hcks, hmems, -⟩ := hKf D μ hA r s' hr hrs (hst.trans htT) φ hφ
    have hφS : MemSobolev (((m2 + 2 : ℕ)) : ℝ) φ := MFSemigroup.memSobolev_of_isSmooth hφ _
    have hφc : Continuous φ := mpk_cont_of_smooth hφ
    obtain ⟨hmemd, hnd⟩ := hC1 D μ hA hν r s' t hr hrs hst htT φ hφS hφc
    have hfe : (fun y => propagator D μ r t φ y - propagator D μ r s' φ y) =
        fun y => 1 * propagator D μ r t φ y + (-1) * propagator D μ r s' φ y := by
      funext y; ring
    have hck1 : Torus.IsCk 1 (fun y => propagator D μ r t φ y - propagator D μ r s' φ y) := by
      rw [hfe]
      exact mpk_isCk_comb (mpk_isCk_one hckt) (mpk_isCk_one hcks) 1 (-1)
    have hg := mpk_grad_comb (mpk_isCk_one hckt) (mpk_isCk_one hcks) 1 (-1) x j
    have hdiff : Torus.grad (propagator D μ r t φ) x j - Torus.grad (propagator D μ r s' φ) x j =
        Torus.grad (fun y => propagator D μ r t φ y - propagator D μ r s' φ y) x j := by
      rw [hfe, hg]; ring
    rw [hdiff]
    refine (mpk_abs_grad_le _ x j).trans ((hgg _ hmemd hck1 x).trans ?_)
    have h0 : 0 ≤ |t - s'| * sobolevNorm (((m2 + 2 : ℕ)) : ℝ) φ :=
      mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
    calc Cs2 * sobolevNorm (m2 : ℝ)
          (fun y => propagator D μ r t φ y - propagator D μ r s' φ y)
        ≤ Cs2 * (C1 * |t - s'| * sobolevNorm (((m2 + 2 : ℕ)) : ℝ) φ) :=
          mul_le_mul_of_nonneg_left hnd hCs2
      _ ≤ Cs2 * (|C1| * (|t - s'| * sobolevNorm (((m2 + 2 : ℕ)) : ℝ) φ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCs2
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ = Cs2 * |C1| * |t - s'| * sobolevNorm (((m2 + 2 : ℕ)) : ℝ) φ := by ring

/-- the Sobolev norm of a real Fourier mode -/
theorem mmm_sobolevNorm_realMode (m : ℝ) (k : NonzeroLattice d) :
    sobolevNorm m (Torus.realMode k : Torus d → ℝ) = Lattice.jp k.1 ^ m := by
  have h := mpk_sobolevNorm_trigPoly m {k} (fun _ => 1)
  have e : FieldSingAux.trigPoly ({k} : Finset (NonzeroLattice d)) (fun _ => (1 : ℝ)) =
      (Torus.realMode k : Torus d → ℝ) := by
    funext x; simp [FieldSingAux.trigPoly]
  rw [e] at h
  rw [h]
  simp only [Finset.sum_singleton, one_pow, mul_one]
  rw [← Torus.jp_rpow_sq]
  exact Real.sqrt_sq (Real.rpow_nonneg (Torus.jp_pos k.1).le _)

theorem mmm_eval_realMode {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.eval F (Torus.realMode k : Torus d → ℝ) = NegSobolev.fourierCoeff F k := by
  have h := mpk_eval_trigPoly F {k} (fun _ => (1 : ℝ))
  have e : FieldSingAux.trigPoly ({k} : Finset (NonzeroLattice d)) (fun _ => (1 : ℝ)) =
      (Torus.realMode k : Torus d → ℝ) := by
    funext x; simp [FieldSingAux.trigPoly]
  rw [e] at h
  rw [h]; simp

/-! ### Stage 2: progressivity of the noise integrand -/

theorem mmm_c12_congr {t : ℝ} {f g ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft)
    (h : ∀ r ∈ Set.Icc 0 t, f r = g r) : IsC12Test t g ft where
  c2 := fun r hr => by rw [← h r hr]; exact hf.c2 r hr
  cont_c2 := fun j hj => by
    refine (hf.cont_c2 j hj).congr fun p => ?_
    rw [h p.1.1 p.1.2]
  time_deriv := fun x r hr => by
    refine (hf.time_deriv x r hr).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with r' hr'
    rw [h r' ⟨hr'.1.le, hr'.2.le⟩]
  cont_time_deriv := hf.cont_time_deriv

theorem mmm_c12_prop (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : mStar d ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ)
    (μ : ℝ → Torus d → ℝ) (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ ft : ℝ → Torus d → ℝ, IsC12Test t (fun r => propagator D μ r t φ) ft := by
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    have hm3 := ClassicalPart.one_le_of_mStar hm
    have hV1 : Torus.IsCk 1 D.V :=
      ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ m + 3)) hA.hV.1
    have hμ1 : Torus.IsCk 1 (μ 0) :=
      ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))
        (hA.hμ.smooth 0 ⟨le_rfl, hA.hT.le⟩)
    have hφ2 : Torus.IsCk 2 φ := MFSemigroup.isCk_nat_of_isSmooth hφ 2
    have hcls := PropIncr.mpi_isClassical_zero D (ClassicalAux.convKernelFacts hd D) hV1 μ hμ1 hφ2
    refine ⟨_, mmm_c12_congr hcls.isC12Test fun r hr => ?_⟩
    have hr0 : r = 0 := le_antisymm hr.2 hr.1
    subst hr0
    exact (PropIncr.mpi_propagator_zero D (ClassicalAux.convKernelFacts hd D) hV1 μ hμ1 hφ2).symm
  · have htI : t ∈ Set.Ioc (0 : ℝ) T := ⟨hpos, ht.2⟩
    obtain ⟨C, Cs, hC, hCs, hmain⟩ := adjoint_torus_classical hd s hs0 hsd m hm R MB Λ VB
    obtain ⟨hcls, hpe, -⟩ := hmain D ν₀ T μ hA t htI φ (mpk_cont_of_smooth hφ)
      (MFSemigroup.memSobolev_of_isSmooth hφ _)
    exact ⟨_, mmm_c12_congr hcls.isC12Test fun r hr => (hpe r hr).symm⟩


/-! ### Stage 3: BDG for the difference of two martingales with a common stopping structure -/

theorem mmm_enorm_pow {n : ℕ} (hn : Even n) (σ : ℝ) : ‖σ‖ₑ ^ n = ENNReal.ofReal (σ ^ n) := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, hn.pow_abs]

theorem mmm_ofReal_norm_sq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) :=
  mmm_enorm_pow (by decide) x

section Stoch

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι] {P : Measure Ω}
  [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ} {Φ Φ' : ℝ → Ω → ι → ℝ}

/-- an integrand vanishing after `b` has an integral that is constant after `b` -/
theorem mmm_ito_stop (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ) (b : ℝ)
    (hz : ∀ r, b < r → ∀ ω k, Φ r ω k = 0) :
    ∀ᵐ ω ∂P, ∀ t, itoIntegral P ℱ W Φ t ω = itoIntegral P ℱ W Φ (min t b) ω := by
  have h := itoIntegral_stopIntegrand hW hΦ (τ := fun _ => (b : WithTop ℝ)) (isStoppingTime_const ℱ b)
  have e : stopIntegrand Φ (fun _ => (b : WithTop ℝ)) = Φ := by
    funext r ω
    by_cases hr : r ≤ b
    · have : ω ∈ {ω : Ω | (r : WithTop ℝ) ≤ (fun _ : Ω => (b : WithTop ℝ)) ω} := by
        simpa using hr
      simp only [stopIntegrand, Set.indicator_of_mem this]
    · funext k
      have : ω ∉ {ω : Ω | (r : WithTop ℝ) ≤ (fun _ : Ω => (b : WithTop ℝ)) ω} := by
        simpa using hr
      simp only [stopIntegrand, Set.indicator_of_notMem this, Pi.zero_apply]
      exact (hz r (not_le.1 hr) ω k).symm
  rw [e] at h
  filter_upwards [h] with ω hω t
  rw [hω t]
  exact stoppedProcess_apply_coe (M := itoIntegral P ℱ W Φ) (σ := fun _ => (b : WithTop ℝ))
    (ω := ω) (c := b) rfl t

theorem mmm_bdg_diff (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ)
    (hΦ' : IsProgressiveL2 P ℱ Φ') {b t : ℝ} (hb : b ≤ t) (ht : 0 ≤ t)
    (hz : ∀ r, b < r → ∀ ω k, Φ' r ω k = 0) :
    ∫⁻ ω, ‖itoIntegral P ℱ W Φ t ω - itoIntegral P ℱ W Φ' b ω‖ₑ ^ 4 ∂P ≤
      bdgConstFour * ∫⁻ ω, (∫⁻ s in Set.Icc 0 t, ∑ k, ‖Φ s ω k - Φ' s ω k‖ₑ ^ 2) ^ 2 ∂P := by
  have hΨ := isProgressiveL2_sub hΦ hΦ'
  have h1 := mmm_ito_stop hW hΦ' b hz
  have h2 := itoIntegral_sub hW hΦ hΦ'
  refine le_trans (lintegral_mono_ae ?_) (bdg_four hW hΨ ht)
  filter_upwards [h1, h2] with ω hω1 hω2
  refine pow_le_pow_left' ?_ 4
  have e : itoIntegral P ℱ W Φ t ω - itoIntegral P ℱ W Φ' b ω =
      itoIntegral P ℱ W (fun s ω k => Φ s ω k - Φ' s ω k) t ω := by
    rw [hω2 t, hω1 t, min_eq_right hb]
  rw [e]
  exact le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) t) =>
    ‖itoIntegral P ℱ W (fun s ω k => Φ s ω k - Φ' s ω k) u ω‖ₑ) t ⟨ht, le_rfl⟩

end Stoch


/-! ### Stage 4: the square integral of the noise integrands -/

variable {Ω : Type*}

/-- the quantity `N d c_N²`, `c_N = √(2β⁻¹)/N` -/
def mmmNu (N d : ℕ) (b : ℝ) : ℝ := (N : ℝ) * d * (Real.sqrt (2 * b) / N) ^ 2

theorem mmmNu_nonneg (N d : ℕ) (b : ℝ) : 0 ≤ mmmNu N d b := by
  unfold mmmNu; positivity

theorem mmm_pt (c B x : ℝ) (hx : |x| ≤ B) : ‖c * x‖ₑ ^ 2 ≤ ENNReal.ofReal (c ^ 2 * B ^ 2) := by
  rw [mmm_ofReal_norm_sq]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg c)
  have := pow_le_pow_left₀ (abs_nonneg x) hx 2
  rwa [sq_abs] at this

theorem mmm_sum_le {N d : ℕ} (g : Fin N × Fin d → ℝ≥0∞) (a : ℝ≥0∞) (h : ∀ k, g k ≤ a) :
    ∑ k, g k ≤ ENNReal.ofReal ((N : ℝ) * d) * a := by
  have := Finset.sum_le_card_nsmul Finset.univ g a (fun k _ => h k)
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul] at this
  rw [← ENNReal.ofReal_natCast, Nat.cast_mul] at this
  exact this

theorem mmm_noise_pt {N : ℕ} (D : DynData d) (X : ℝ≥0 → Ω → Config d N)
    (f : ℝ → Torus d → ℝ) (t : ℝ) (B : ℝ) (hB : ∀ r ∈ Set.Icc 0 t, ∀ x j, |Torus.grad (f r) x j| ≤ B)
    (s : ℝ) (hs : s ∈ Set.Icc 0 t) (ω : Ω) :
    ∑ k : Fin N × Fin d, ‖empiricalNoiseIntegrand D t f X s ω k‖ₑ ^ 2 ≤
      ENNReal.ofReal (mmmNu N d D.invβ * B ^ 2) := by
  refine (mmm_sum_le _ (ENNReal.ofReal ((Real.sqrt (2 * D.invβ) / N) ^ 2 * B ^ 2)) fun k => ?_).trans
    (le_of_eq ?_)
  · simp only [empiricalNoiseIntegrand, if_pos hs]
    exact mmm_pt _ _ _ (hB s hs _ _)
  · rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold mmmNu; ring


theorem mmm_sum_nu {N d : ℕ} (b : ℝ) (g : Fin N × Fin d → ℝ) (B : ℝ) (h : ∀ k, |g k| ≤ B) :
    ∑ k, ‖(Real.sqrt (2 * b) / N) * g k‖ₑ ^ 2 ≤ ENNReal.ofReal (mmmNu N d b * B ^ 2) := by
  refine (mmm_sum_le _ (ENNReal.ofReal ((Real.sqrt (2 * b) / N) ^ 2 * B ^ 2)) fun k => ?_).trans
    (le_of_eq ?_)
  · exact mmm_pt _ _ _ (h k)
  · rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold mmmNu; ring

theorem mmm_sqint_single {N : ℕ} (D : DynData d) (X : ℝ≥0 → Ω → Config d N)
    (f : ℝ → Torus d → ℝ) {t : ℝ} (ht : 0 ≤ t) (B : ℝ)
    (hB : ∀ r ∈ Set.Icc 0 t, ∀ x j, |Torus.grad (f r) x j| ≤ B) (ω : Ω) :
    ∫⁻ s in Set.Icc 0 t, ∑ k : Fin N × Fin d, ‖empiricalNoiseIntegrand D t f X s ω k‖ₑ ^ 2 ≤
      ENNReal.ofReal (mmmNu N d D.invβ * (t * B ^ 2)) := by
  calc ∫⁻ s in Set.Icc 0 t, ∑ k : Fin N × Fin d, ‖empiricalNoiseIntegrand D t f X s ω k‖ₑ ^ 2
      ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (mmmNu N d D.invβ * B ^ 2) :=
        setLIntegral_mono' measurableSet_Icc fun s hs => mmm_noise_pt D X f t B hB s hs ω
    _ = ENNReal.ofReal (mmmNu N d D.invβ * B ^ 2) * ENNReal.ofReal (t - 0) := by
        rw [setLIntegral_const, Real.volume_Icc]
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by have := mmmNu_nonneg N d D.invβ; positivity)]
        congr 1; ring

theorem mmm_sqint_diff {N : ℕ} (D : DynData d) (X : ℝ≥0 → Ω → Config d N)
    (f f' : ℝ → Torus d → ℝ) {s' t : ℝ} (hs' : 0 ≤ s') (hst : s' ≤ t) (B₁ B₂ : ℝ)
    (hB₁ : ∀ r ∈ Set.Icc 0 t, ∀ x j, |Torus.grad (f r) x j| ≤ B₁)
    (hB₂ : ∀ r ∈ Set.Icc 0 s', ∀ x j, |Torus.grad (f r) x j - Torus.grad (f' r) x j| ≤ B₂)
    (ω : Ω) :
    ∫⁻ s in Set.Icc 0 t, ∑ k : Fin N × Fin d,
        ‖empiricalNoiseIntegrand D t f X s ω k - empiricalNoiseIntegrand D s' f' X s ω k‖ₑ ^ 2 ≤
      ENNReal.ofReal (mmmNu N d D.invβ * (s' * B₂ ^ 2 + (t - s') * B₁ ^ 2)) := by
  have hν := mmmNu_nonneg N d D.invβ
  have hsplit : Set.Icc (0 : ℝ) t = Set.Icc 0 s' ∪ Set.Ioc s' t :=
    (Set.Icc_union_Ioc_eq_Icc hs' hst).symm
  have hdisj : Disjoint (Set.Icc (0 : ℝ) s') (Set.Ioc s' t) :=
    Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx'.1)
  rw [hsplit, lintegral_union measurableSet_Ioc hdisj]
  have h1 : ∫⁻ s in Set.Icc (0 : ℝ) s', ∑ k : Fin N × Fin d,
        ‖empiricalNoiseIntegrand D t f X s ω k - empiricalNoiseIntegrand D s' f' X s ω k‖ₑ ^ 2 ≤
      ENNReal.ofReal (mmmNu N d D.invβ * B₂ ^ 2) * ENNReal.ofReal (s' - 0) := by
    rw [← Real.volume_Icc, ← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
    have hst' : s ∈ Set.Icc (0 : ℝ) t := ⟨hs.1, hs.2.trans hst⟩
    have e : ∀ k : Fin N × Fin d, empiricalNoiseIntegrand D t f X s ω k -
        empiricalNoiseIntegrand D s' f' X s ω k =
        (Real.sqrt (2 * D.invβ) / N) * (Torus.grad (f s) (X (Real.toNNReal s) ω k.1) k.2 -
          Torus.grad (f' s) (X (Real.toNNReal s) ω k.1) k.2) := by
      intro k
      simp only [empiricalNoiseIntegrand, if_pos hst', if_pos hs]
      ring
    simp only [e]
    exact mmm_sum_nu D.invβ _ B₂ fun k => hB₂ s hs _ _
  have h2 : ∫⁻ s in Set.Ioc s' t, ∑ k : Fin N × Fin d,
        ‖empiricalNoiseIntegrand D t f X s ω k - empiricalNoiseIntegrand D s' f' X s ω k‖ₑ ^ 2 ≤
      ENNReal.ofReal (mmmNu N d D.invβ * B₁ ^ 2) * ENNReal.ofReal (t - s') := by
    rw [← Real.volume_Ioc, ← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
    have hst' : s ∈ Set.Icc (0 : ℝ) t := ⟨hs'.trans hs.1.le, hs.2⟩
    have hns : s ∉ Set.Icc (0 : ℝ) s' := fun h => absurd h.2 (not_le.2 hs.1)
    have e : ∀ k : Fin N × Fin d, empiricalNoiseIntegrand D t f X s ω k -
        empiricalNoiseIntegrand D s' f' X s ω k =
        (Real.sqrt (2 * D.invβ) / N) * Torus.grad (f s) (X (Real.toNNReal s) ω k.1) k.2 := by
      intro k
      simp only [empiricalNoiseIntegrand, if_pos hst', if_neg hns, sub_zero]
    simp only [e]
    exact mmm_sum_nu D.invβ _ B₁ fun k => hB₁ s hst' _ _
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by have := sub_nonneg.2 hs'; positivity)
      (by have := sub_nonneg.2 hst; positivity)]
  congr 1; ring


/-! ### Stage 5: the moments of one martingale mode -/

section Mode

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
  {N : ℕ} {W' : ℝ≥0 → Ω → Fin N × Fin d → ℝ}

/-- fourth moment of the difference of two empirical martingale modes -/
theorem mmm_mode_fourth (hW : IsBrownianFiltration P ℱ W') (D : DynData d)
    (X : ℝ≥0 → Ω → Config d N) {f f' : ℝ → Torus d → ℝ} {s' t : ℝ} (hs' : 0 ≤ s') (hst : s' ≤ t)
    (hΦ : IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D t f X))
    (hΦ' : IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D s' f' X)) (B₁ B₂ : ℝ)
    (hB₁ : ∀ r ∈ Set.Icc 0 t, ∀ x j, |Torus.grad (f r) x j| ≤ B₁)
    (hB₂ : ∀ r ∈ Set.Icc 0 s', ∀ x j, |Torus.grad (f r) x j - Torus.grad (f' r) x j| ≤ B₂)
    (σ : ℝ) :
    ∫⁻ ζ, ‖σ * empiricalMartingale P ℱ W' D t f X t ζ -
        σ * empiricalMartingale P ℱ W' D s' f' X s' ζ‖ₑ ^ 4 ∂P ≤
      ENNReal.ofReal (σ ^ 4 * (512 / 27 : ℝ) ^ 2 *
        (mmmNu N d D.invβ * (s' * B₂ ^ 2 + (t - s') * B₁ ^ 2)) ^ 2) := by
  have ht : 0 ≤ t := hs'.trans hst
  have hz : ∀ r, s' < r → ∀ ω k, empiricalNoiseIntegrand D s' f' X r ω k = 0 := by
    intro r hr ω k
    simp [empiricalNoiseIntegrand, Set.mem_Icc, not_le.2 hr]
  have hν := mmmNu_nonneg N d D.invβ
  have hb : 0 ≤ s' * B₂ ^ 2 + (t - s') * B₁ ^ 2 := by
    have := sub_nonneg.2 hst; positivity
  calc ∫⁻ ζ, ‖σ * empiricalMartingale P ℱ W' D t f X t ζ -
        σ * empiricalMartingale P ℱ W' D s' f' X s' ζ‖ₑ ^ 4 ∂P
      = ∫⁻ ζ, ENNReal.ofReal (σ ^ 4) * ‖empiricalMartingale P ℱ W' D t f X t ζ -
        empiricalMartingale P ℱ W' D s' f' X s' ζ‖ₑ ^ 4 ∂P := by
        refine lintegral_congr fun ζ => ?_
        rw [← mul_sub, enorm_mul, mul_pow, mmm_enorm_pow (by decide)]
    _ = ENNReal.ofReal (σ ^ 4) * ∫⁻ ζ, ‖empiricalMartingale P ℱ W' D t f X t ζ -
        empiricalMartingale P ℱ W' D s' f' X s' ζ‖ₑ ^ 4 ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (σ ^ 4) * (bdgConstFour * ∫⁻ ζ, (∫⁻ s in Set.Icc 0 t, ∑ k,
          ‖empiricalNoiseIntegrand D t f X s ζ k - empiricalNoiseIntegrand D s' f' X s ζ k‖ₑ ^ 2) ^ 2
          ∂P) := by
        refine mul_le_mul' le_rfl ?_
        exact mmm_bdg_diff hW hΦ hΦ' hst ht hz
    _ ≤ ENNReal.ofReal (σ ^ 4) * (bdgConstFour * ∫⁻ ζ, (ENNReal.ofReal (mmmNu N d D.invβ *
          (s' * B₂ ^ 2 + (t - s') * B₁ ^ 2))) ^ 2 ∂P) := by
        refine mul_le_mul' le_rfl (mul_le_mul' le_rfl (lintegral_mono fun ζ => ?_))
        exact pow_le_pow_left' (mmm_sqint_diff D X f f' hs' hst B₁ B₂ hB₁ hB₂ ζ) 2
    _ = _ := by
        rw [lintegral_const, measure_univ, mul_one, bdgConstFour, ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-- second moment of one empirical martingale mode -/
theorem mmm_mode_second (hW : IsBrownianFiltration P ℱ W') (D : DynData d)
    (X : ℝ≥0 → Ω → Config d N) {f : ℝ → Torus d → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hΦ : IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D t f X)) (B : ℝ)
    (hB : ∀ r ∈ Set.Icc 0 t, ∀ x j, |Torus.grad (f r) x j| ≤ B) (σ : ℝ) :
    ∫⁻ ζ, ‖σ * empiricalMartingale P ℱ W' D t f X t ζ‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (σ ^ 2 * (mmmNu N d D.invβ * (t * B ^ 2))) := by
  have hν := mmmNu_nonneg N d D.invβ
  calc ∫⁻ ζ, ‖σ * empiricalMartingale P ℱ W' D t f X t ζ‖ₑ ^ 2 ∂P
      = ∫⁻ ζ, ENNReal.ofReal (σ ^ 2) * ‖empiricalMartingale P ℱ W' D t f X t ζ‖ₑ ^ 2 ∂P := by
        refine lintegral_congr fun ζ => ?_
        rw [enorm_mul, mul_pow, mmm_enorm_pow (by decide)]
    _ = ENNReal.ofReal (σ ^ 2) * ∫⁻ ζ, ‖empiricalMartingale P ℱ W' D t f X t ζ‖ₑ ^ 2 ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (σ ^ 2) * sqIntegralOn P (empiricalNoiseIntegrand D t f X) t := by
        rw [empiricalMartingale, lintegral_itoIntegral_sq hW hΦ]
    _ ≤ ENNReal.ofReal (σ ^ 2) * ∫⁻ ζ, ENNReal.ofReal (mmmNu N d D.invβ * (t * B ^ 2)) ∂P := by
        refine mul_le_mul' le_rfl (lintegral_mono fun ζ => ?_)
        exact mmm_sqint_single D X f ht B hB ζ
    _ = _ := by
        rw [lintegral_const, measure_univ, mul_one, ← ENNReal.ofReal_mul (by positivity)]

end Mode


/-! ### Stage 6: summation over the Fourier modes -/

theorem mmm_cs_fin {ι : Type*} (S : Finset ι) (a b : ι → ℝ≥0∞) :
    (∑ k ∈ S, a k * b k) ^ 2 ≤ (∑ k ∈ S, a k ^ 2) * ∑ k ∈ S, b k ^ 2 := by
  have h := ENNReal.inner_le_Lp_mul_Lq S a b Real.HolderConjugate.two_two
  have e : ∀ x : ℝ≥0∞, (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc (∑ k ∈ S, a k * b k) ^ 2 ≤ ((∑ k ∈ S, a k ^ (2:ℝ)) ^ ((1 : ℝ) / 2) *
        (∑ k ∈ S, b k ^ (2:ℝ)) ^ ((1 : ℝ) / 2)) ^ 2 := pow_le_pow_left' h 2
    _ = _ := by
      rw [mul_pow, e, e]
      simp only [ENNReal.rpow_two]

/-- Cauchy-Schwarz for `ℝ≥0∞`-valued series -/
theorem mmm_cs_tsum {ι : Type*} (a b : ι → ℝ≥0∞) :
    (∑' k, a k * b k) ^ 2 ≤ (∑' k, a k ^ 2) * ∑' k, b k ^ 2 := by
  rw [ENNReal.tsum_eq_iSup_sum]
  have hmono : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun x y h => pow_le_pow_left' h 2
  have := Monotone.map_iSup_of_continuousAt (f := fun x : ℝ≥0∞ => x ^ 2)
    (g := fun s : Finset ι => ∑ k ∈ s, a k * b k) (ENNReal.continuous_pow 2).continuousAt hmono
    (by simp)
  rw [this]
  refine iSup_le fun S => ?_
  exact (mmm_cs_fin S a b).trans (mul_le_mul' (ENNReal.sum_le_tsum S) (ENNReal.sum_le_tsum S))

theorem mmm_weight (ℓ q : ℝ) (hq : q = ℓ + d + 2) (k : NonzeroLattice d) :
    (Lattice.jp k.1 ^ (-(2 * q)) / Lattice.jp k.1 ^ (-(((d : ℝ) + 1) / 2))) ^ 2 *
        Lattice.jp k.1 ^ (4 * ℓ) = Lattice.jp k.1 ^ (-(3 * (d : ℝ) + 7)) := by
  have hj := Torus.jp_pos k.1
  rw [← Real.rpow_sub hj, Torus.jp_rpow_sq, ← Real.rpow_add hj]
  congr 1
  subst hq; ring

theorem mmm_summable_jp1 : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-((d : ℝ) + 1)) := by
  have := summable_jp_rpow (d := d) (((d : ℝ) + 1) / 2) (by linarith)
  convert this using 2; ring_nf

theorem mmm_summable_jp2 :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(3 * (d : ℝ) + 7)) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have := summable_jp_rpow (d := d) ((3 * (d : ℝ) + 7) / 2) (by linarith)
  convert this using 2; ring_nf

section Sum

variable {mΩ : MeasurableSpace Ω}

/-- the weighted sum over Fourier modes: if each mode has fourth moment `≲ jp_k^{4ℓ}`, then the
`H^{-q}`-norm, `q = ℓ + d + 2`, has finite fourth moment. -/
theorem mmm_sum_fourth (P : Measure Ω) [IsProbabilityMeasure P] (ℓ q : ℝ) (hq : q = ℓ + d + 2)
    (F : Ω → NegSobolev d q) (hF : Measurable F) (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hmode : ∀ k : NonzeroLattice d, ∫⁻ ζ, ‖NegSobolev.fourierCoeff (F ζ) k‖ₑ ^ 4 ∂P ≤
      ENNReal.ofReal (A * Lattice.jp k.1 ^ (4 * ℓ) * δ)) :
    ∫⁻ ζ, ‖F ζ‖ₑ ^ 4 ∂P ≤ ENNReal.ofReal
      ((∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-((d : ℝ) + 1))) *
        (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(3 * (d : ℝ) + 7))) * (A * δ)) := by
  classical
  set μ : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-(((d : ℝ) + 1) / 2)) with hμ
  have hμpos : ∀ k, 0 < μ k := fun k => Real.rpow_pos_of_pos (Torus.jp_pos k.1) _
  have hμsq : ∀ k, μ k ^ 2 = Lattice.jp k.1 ^ (-((d : ℝ) + 1)) := by
    intro k; rw [hμ]; simp only; rw [Torus.jp_rpow_sq]; congr 1; ring
  set w : NonzeroLattice d → ℝ := fun k =>
    (Lattice.jp k.1 ^ (-(2 * q)) / μ k) ^ 2 with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => sq_nonneg _
  have hwk : ∀ k, w k * Lattice.jp k.1 ^ (4 * ℓ) = Lattice.jp k.1 ^ (-(3 * (d : ℝ) + 7)) :=
    fun k => mmm_weight ℓ q hq k
  have hΔ : ∀ k, Measurable fun ζ => NegSobolev.fourierCoeff (F ζ) k := fun k =>
    ((FieldSingAux.coordCLM q k).continuous.measurable).comp hF
  -- the coordinates
  have hcoord : ∀ ζ k, NegSobolev.coord (F ζ) k =
      Lattice.jp k.1 ^ (-q) * NegSobolev.fourierCoeff (F ζ) k := by
    intro ζ k
    unfold NegSobolev.fourierCoeff
    rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
    simp
  have h1 : ∀ ζ, ‖F ζ‖ₑ ^ 4 = (∑' k, ENNReal.ofReal (NegSobolev.coord (F ζ) k ^ 2)) ^ 2 := by
    intro ζ
    obtain ⟨hs, hn⟩ := NegSobolev.coord_sq (F ζ)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hs, ← hn,
      ← ENNReal.ofReal_pow (sq_nonneg _), ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
    congr 1; ring
  have h2 : ∀ ζ k, ENNReal.ofReal (NegSobolev.coord (F ζ) k ^ 2) =
      ENNReal.ofReal (μ k) * ENNReal.ofReal (NegSobolev.coord (F ζ) k ^ 2 / μ k) := by
    intro ζ k
    rw [← ENNReal.ofReal_mul (hμpos k).le]
    congr 1; field_simp [(hμpos k).ne']
  have h3 : ∀ ζ k, ENNReal.ofReal (NegSobolev.coord (F ζ) k ^ 2 / μ k) ^ 2 =
      ENNReal.ofReal (w k) * ‖NegSobolev.fourierCoeff (F ζ) k‖ₑ ^ 4 := by
    intro ζ k
    rw [← ENNReal.ofReal_pow (div_nonneg (sq_nonneg _) (hμpos k).le),
      mmm_enorm_pow (by decide), ← ENNReal.ofReal_mul (hw0 k)]
    congr 1
    rw [hcoord, hw, mul_pow, Torus.jp_rpow_sq]
    have : (Lattice.jp k.1 ^ (2 * -q) * NegSobolev.fourierCoeff (F ζ) k ^ 2 / μ k) ^ 2 =
        (Lattice.jp k.1 ^ (-(2 * q)) / μ k) ^ 2 * NegSobolev.fourierCoeff (F ζ) k ^ 4 := by
      rw [show 2 * -q = -(2 * q) by ring]
      ring
    exact this
  have hLam : ∑' k, ENNReal.ofReal (μ k) ^ 2 =
      ENNReal.ofReal (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-((d : ℝ) + 1))) := by
    rw [ENNReal.ofReal_tsum_of_nonneg
      (f := fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-((d : ℝ) + 1)))
      (fun k => (Real.rpow_pos_of_pos (Torus.jp_pos k.1) _).le) mmm_summable_jp1]
    refine tsum_congr fun k => ?_
    rw [← ENNReal.ofReal_pow (hμpos k).le, hμsq]
  calc ∫⁻ ζ, ‖F ζ‖ₑ ^ 4 ∂P
      = ∫⁻ ζ, (∑' k, ENNReal.ofReal (μ k) *
          ENNReal.ofReal (NegSobolev.coord (F ζ) k ^ 2 / μ k)) ^ 2 ∂P := by
        refine lintegral_congr fun ζ => ?_
        rw [h1]
        simp only [h2]
    _ ≤ ∫⁻ ζ, ((∑' k, ENNReal.ofReal (μ k) ^ 2) *
          ∑' k, ENNReal.ofReal (NegSobolev.coord (F ζ) k ^ 2 / μ k) ^ 2) ∂P :=
        lintegral_mono fun ζ => mmm_cs_tsum _ _
    _ = (∑' k, ENNReal.ofReal (μ k) ^ 2) *
          ∫⁻ ζ, ∑' k, ENNReal.ofReal (NegSobolev.coord (F ζ) k ^ 2 / μ k) ^ 2 ∂P := by
        refine lintegral_const_mul' _ _ ?_
        rw [hLam]; exact ENNReal.ofReal_ne_top
    _ = (∑' k, ENNReal.ofReal (μ k) ^ 2) *
          ∑' k, ∫⁻ ζ, ENNReal.ofReal (w k) * ‖NegSobolev.fourierCoeff (F ζ) k‖ₑ ^ 4 ∂P := by
        congr 1
        calc ∫⁻ ζ, ∑' k, ENNReal.ofReal (NegSobolev.coord (F ζ) k ^ 2 / μ k) ^ 2 ∂P
            = ∫⁻ ζ, ∑' k, ENNReal.ofReal (w k) * ‖NegSobolev.fourierCoeff (F ζ) k‖ₑ ^ 4 ∂P :=
              lintegral_congr fun ζ => tsum_congr fun k => h3 ζ k
          _ = _ := lintegral_tsum (f := fun k ζ =>
              ENNReal.ofReal (w k) * ‖NegSobolev.fourierCoeff (F ζ) k‖ₑ ^ 4) fun k =>
              (measurable_const.mul ((hΔ k).enorm.pow_const 4)).aemeasurable
    _ ≤ ENNReal.ofReal (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-((d : ℝ) + 1))) *
          ∑' k : NonzeroLattice d, ENNReal.ofReal (A * δ * Lattice.jp k.1 ^ (-(3 * (d : ℝ) + 7))) := by
        rw [hLam]
        refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun k => ?_)
        rw [lintegral_const_mul _ ((hΔ k).enorm.pow_const 4)]
        calc ENNReal.ofReal (w k) * ∫⁻ ζ, ‖NegSobolev.fourierCoeff (F ζ) k‖ₑ ^ 4 ∂P
            ≤ ENNReal.ofReal (w k) * ENNReal.ofReal (A * Lattice.jp k.1 ^ (4 * ℓ) * δ) :=
              mul_le_mul' le_rfl (hmode k)
          _ = ENNReal.ofReal (w k * (A * Lattice.jp k.1 ^ (4 * ℓ) * δ)) :=
              (ENNReal.ofReal_mul (hw0 k)).symm
          _ = _ := by
              congr 1
              rw [← hwk k]; ring
    _ = _ := by
        have h0 : ∀ k : NonzeroLattice d,
            0 ≤ A * δ * Lattice.jp k.1 ^ (-(3 * (d : ℝ) + 7)) := fun k =>
          mul_nonneg (mul_nonneg hA hδ) (Real.rpow_pos_of_pos (Torus.jp_pos k.1) _).le
        have hsum2 : Summable fun k : NonzeroLattice d =>
            A * δ * Lattice.jp k.1 ^ (-(3 * (d : ℝ) + 7)) :=
          (mmm_summable_jp2 (d := d)).mul_left (A * δ)
        have hLam0 : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-((d : ℝ) + 1)) :=
          tsum_nonneg fun k => (Real.rpow_pos_of_pos (Torus.jp_pos k.1) _).le
        rw [← ENNReal.ofReal_tsum_of_nonneg h0 hsum2, ← ENNReal.ofReal_mul hLam0, tsum_mul_left]
        congr 1
        ring

end Sum


/-! ### Stage 7: the per-`N` moment lemmas -/

theorem mmm_sigma_nu (N d : ℕ) (hN : 1 ≤ N) (σ b : ℝ) (hb : 0 ≤ b) (h : σ ^ 2 * b / N ≤ 1) :
    σ ^ 2 * mmmNu N d b ≤ 2 * d := by
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have e : σ ^ 2 * mmmNu N d b = 2 * d * (σ ^ 2 * b / N) := by
    unfold mmmNu
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [e]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

theorem mmm_real_bound (σ ν u C₂ C₃ T s' t : ℝ) (d : ℝ) (hd : 0 ≤ d) (hσν : σ ^ 2 * ν ≤ 2 * d)
    (hν : 0 ≤ ν) (hs' : 0 ≤ s') (hst : s' ≤ t) (htT : t ≤ T) :
    σ ^ 4 * (512 / 27 : ℝ) ^ 2 *
        (ν * (s' * (C₃ * |t - s'| * u) ^ 2 + (t - s') * (C₂ * u) ^ 2)) ^ 2 ≤
      ((512 / 27 : ℝ) ^ 2 * (4 * d ^ 2 * (T ^ 2 * C₃ ^ 2 + C₂ ^ 2) ^ 2)) * u ^ 4 * |t - s'| ^ 2 := by
  have hδ : 0 ≤ t - s' := sub_nonneg.2 hst
  rw [abs_of_nonneg hδ]
  set δ := t - s' with hδdef
  have hδT : δ ≤ T := by linarith
  have hsT : s' ≤ T := by linarith
  have hT : 0 ≤ T := by linarith
  have h1 : s' * δ ≤ T * T := mul_le_mul hsT hδT hδ hT
  have h2 : s' * δ ^ 2 ≤ T ^ 2 * δ := by
    have : s' * δ ^ 2 = (s' * δ) * δ := by ring
    rw [this]
    nlinarith
  set X : ℝ := s' * (C₃ * δ * u) ^ 2 + δ * (C₂ * u) ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  have hXle : X ≤ u ^ 2 * δ * (T ^ 2 * C₃ ^ 2 + C₂ ^ 2) := by
    have e : X = u ^ 2 * (C₃ ^ 2 * (s' * δ ^ 2) + C₂ ^ 2 * δ) := by rw [hX]; ring
    rw [e]
    have : C₃ ^ 2 * (s' * δ ^ 2) ≤ C₃ ^ 2 * (T ^ 2 * δ) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
    nlinarith
  have h3 : σ ^ 2 * ν * X ≤ 2 * d * (u ^ 2 * δ * (T ^ 2 * C₃ ^ 2 + C₂ ^ 2)) := by
    calc σ ^ 2 * ν * X ≤ 2 * d * X := mul_le_mul_of_nonneg_right hσν hX0
      _ ≤ _ := mul_le_mul_of_nonneg_left hXle (by positivity)
  have h4 : (σ ^ 2 * ν * X) ^ 2 ≤ (2 * d * (u ^ 2 * δ * (T ^ 2 * C₃ ^ 2 + C₂ ^ 2))) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  have e1 : σ ^ 4 * (512 / 27 : ℝ) ^ 2 * (ν * X) ^ 2 = (512 / 27 : ℝ) ^ 2 * (σ ^ 2 * ν * X) ^ 2 := by
    ring
  rw [e1]
  calc (512 / 27 : ℝ) ^ 2 * (σ ^ 2 * ν * X) ^ 2
      ≤ (512 / 27 : ℝ) ^ 2 * (2 * d * (u ^ 2 * δ * (T ^ 2 * C₃ ^ 2 + C₂ ^ 2))) ^ 2 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

theorem mmm_cast (d : ℕ) : ((qT d : ℕ) : ℝ) = ((mStar d + 1 + 2 : ℕ) : ℝ) + d + 2 := by
  unfold qT Main.gammaIdx
  push_cast
  ring

theorem mmm_ell_bounds (d : ℕ) : mStar d ≤ mStar d + 1 + 2 ∧ (d : ℝ) / 2 + 1 < ((mStar d + 1 : ℕ) : ℝ) := by
  refine ⟨by omega, ?_⟩
  unfold mStar
  push_cast
  have := Nat.lt_floor_add_one ((d : ℝ) / 2)
  linarith

theorem mmm_level_le (d : ℕ) : mStar d + 1 + 2 ≤ qT d := by
  unfold qT Main.gammaIdx; omega

/-- **(b) per-mode second moment**, one fixed `N`: for a smooth test `φ`,
`E|σ · M_N^t[U^{·,t}φ]|² ≤ C ‖φ‖²_{H^{ℓ}}`, `ℓ = mStar d + 3`, with `C` independent of `N`, `t`, `φ`.
Hypotheses: the adjoint data at level `ℓ`, `β⁻¹ ≤ νbar`, `σ² β⁻¹/N ≤ 1` (`q_N ≤ 1`), a Brownian filtration
and a progressive `X`. -/
theorem mmm_second_moment_N (s : ℝ) (Rg : Regime) (ν₀ MB Λ T VB νbar : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) {N : ℕ} (_ : 1 ≤ N)
      (W' : ℝ≥0 → Ω → Fin N × Fin d → ℝ) (X : ℝ≥0 → Ω → Config d N) (D : DynData d)
      (ρ : ℝ → Torus d → ℝ) (σ : ℝ),
      AdjointData s (mStar d + 1 + 2) Rg MB Λ VB D ν₀ T ρ → D.invβ ≤ νbar →
      σ ^ 2 * D.invβ / N ≤ 1 → IsBrownianFiltration P ℱ W' → IsProgressive ℱ (ofNNRealTime X) →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
        ∫⁻ ζ, ‖σ * empiricalMartingale P ℱ W' D t (fun r => propagator D ρ r t φ) X t ζ‖ₑ ^ 2 ∂P ≤
          ENNReal.ofReal (C * sobolevNorm (((mStar d + 1 + 2 : ℕ)) : ℝ) φ ^ 2) := by
  by_cases hcase : 1 ≤ d ∧ 0 ≤ s ∧ s < d
  · obtain ⟨hd, hs0, hsd⟩ := hcase
    obtain ⟨hm, hm2⟩ := mmm_ell_bounds d
    obtain ⟨C₂, C₃, hC₂, hC₃, hP⟩ := mmm_pde hd s hs0 hsd (mStar d + 1) hm hm2 Rg ν₀ MB Λ T VB νbar
    refine ⟨2 * d * max T 0 * C₂ ^ 2, by positivity, ?_⟩
    intro Ω mΩ P _ ℱ N hN W' X D ρ σ hA hν hσ hW hX t ht φ hφ
    obtain ⟨ft, hft⟩ := mmm_c12_prop hd s hs0 hsd (mStar d + 1 + 2) hm Rg MB Λ VB D ν₀ T ρ hA ht hφ
    have hΦ := isProgressiveL2_empiricalNoiseIntegrand (P := P) hX ht.1 (D := D) hft
    have hB : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x j, |Torus.grad (propagator D ρ r t φ) x j| ≤
        C₂ * sobolevNorm (((mStar d + 1 + 2 : ℕ)) : ℝ) φ :=
      fun r hr x j => (hP D ρ hA hν j x).1 r t hr.1 hr.2 ht.2 φ hφ
    refine (mmm_mode_second hW D X ht.1 hΦ _ hB σ).trans (ENNReal.ofReal_le_ofReal ?_)
    have hb : 0 ≤ D.invβ := D.hβ
    have h1 := mmm_sigma_nu N d hN σ D.invβ hb hσ
    have hν0 := mmmNu_nonneg N d D.invβ
    have e : σ ^ 2 * (mmmNu N d D.invβ * (t * (C₂ * sobolevNorm (((mStar d + 1 + 2 : ℕ)) : ℝ) φ) ^ 2)) =
        (σ ^ 2 * mmmNu N d D.invβ) * (t * (C₂ * sobolevNorm (((mStar d + 1 + 2 : ℕ)) : ℝ) φ) ^ 2) := by
      ring
    rw [e]
    have htm : t ≤ max T 0 := ht.2.trans (le_max_left _ _)
    have hY : 0 ≤ (C₂ * sobolevNorm (((mStar d + 1 + 2 : ℕ)) : ℝ) φ) ^ 2 := sq_nonneg _
    calc (σ ^ 2 * mmmNu N d D.invβ) * (t * (C₂ * sobolevNorm (((mStar d + 1 + 2 : ℕ)) : ℝ) φ) ^ 2)
        ≤ (2 * d) * (max T 0 * (C₂ * sobolevNorm (((mStar d + 1 + 2 : ℕ)) : ℝ) φ) ^ 2) := by
          refine mul_le_mul h1 (mul_le_mul_of_nonneg_right htm hY) (mul_nonneg ht.1 hY) (by positivity)
      _ = _ := by ring
  · refine ⟨0, le_rfl, ?_⟩
    intro Ω mΩ P _ ℱ N hN W' X D ρ σ hA
    exfalso
    apply hcase
    have h0 := D.hs0
    have h1 := D.hsd
    have hs := hA.hs
    rw [hs] at h0 h1
    refine ⟨?_, h0, h1⟩
    have : (0 : ℝ) < d := lt_of_le_of_lt h0 h1
    exact_mod_cast this


theorem mmm_fc_sub {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (F - G) k = NegSobolev.fourierCoeff F k - NegSobolev.fourierCoeff G k := by
  have hc : NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k := rfl
  unfold NegSobolev.fourierCoeff
  rw [hc, mul_sub]

/-- **(a) per-`N` fourth moment**: `E‖𝕄^t - 𝕄^{s'}‖⁴_{H_q} ≤ C|t-s'|²`, `q = qT d`, for one fixed `N ≥ 1`
and any `M` with `IsStochConvT` (hypotheses only on this `N`; `C` is independent of `N`, `M`, `Ω`). -/
theorem mmm_fourth_moment_N (s : ℝ) (Rg : Regime) (ν₀ MB Λ T VB νbar : ℝ) :
    ∃ C : ℝ, ∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) {N : ℕ} (_ : 1 ≤ N)
      (W' : ℝ≥0 → Ω → Fin N × Fin d → ℝ) (X : ℝ≥0 → Ω → Config d N) (D : DynData d)
      (ρ : ℝ → Torus d → ℝ) (σ : ℝ),
      AdjointData s (mStar d + 1 + 2) Rg MB Λ VB D ν₀ T ρ → D.invβ ≤ νbar →
      σ ^ 2 * D.invβ / N ≤ 1 → IsBrownianFiltration P ℱ W' → IsProgressive ℱ (ofNNRealTime X) →
      ∀ M : ℝ → Ω → NegSobolev d ((qT d : ℕ) : ℝ),
        IsStochConvT P ℱ W' D ρ σ ((qT d : ℕ) : ℝ) T X M →
        ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ζ, ‖M t ζ - M s' ζ‖ₑ ^ 4 ∂P ≤ ENNReal.ofReal (C * |t - s'| ^ 2) := by
  by_cases hcase : 1 ≤ d ∧ 0 ≤ s ∧ s < d
  · obtain ⟨hd, hs0, hsd⟩ := hcase
    obtain ⟨hm, hm2⟩ := mmm_ell_bounds d
    obtain ⟨C₂, C₃, hC₂, hC₃, hP⟩ := mmm_pde hd s hs0 hsd (mStar d + 1) hm hm2 Rg ν₀ MB Λ T VB νbar
    set K : ℝ := T ^ 2 * C₃ ^ 2 + C₂ ^ 2 with hK
    set A : ℝ := (512 / 27 : ℝ) ^ 2 * (4 * (d : ℝ) ^ 2 * K ^ 2) with hA
    have hA0 : 0 ≤ A := by positivity
    set Lam : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-((d : ℝ) + 1)) with hLam
    set Sm : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(3 * (d : ℝ) + 7)) with hSm
    refine ⟨Lam * Sm * A, ?_⟩
    intro Ω mΩ P _ ℱ N hN W' X D ρ σ hAd hν hσ hW hX M hM
    have hb : 0 ≤ D.invβ := D.hβ
    have hσν := mmm_sigma_nu N d hN σ D.invβ hb hσ
    have hν0 := mmmNu_nonneg N d D.invβ
    set ℓ : ℝ := ((mStar d + 1 + 2 : ℕ) : ℝ) with hℓ
    have core : ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T, s' ≤ t →
        ∫⁻ ζ, ‖M t ζ - M s' ζ‖ₑ ^ 4 ∂P ≤ ENNReal.ofReal (Lam * Sm * A * |t - s'| ^ 2) := by
      intro s' hs' t ht hst
      have hmeasF : Measurable fun ζ => M t ζ - M s' ζ := (hM.1 t).sub (hM.1 s')
      have hmode : ∀ k : NonzeroLattice d, ∫⁻ ζ, ‖NegSobolev.fourierCoeff (M t ζ - M s' ζ) k‖ₑ ^ 4 ∂P ≤
          ENNReal.ofReal (A * Lattice.jp k.1 ^ (4 * ℓ) * |t - s'| ^ 2) := by
        intro k
        have hsm := mpk_test_realMode (d := d) k
        have h1 := hM.2 t ht _ hsm.1 hsm.2
        have h2 := hM.2 s' hs' _ hsm.1 hsm.2
        have hae : ∀ᵐ ζ ∂P, NegSobolev.fourierCoeff (M t ζ - M s' ζ) k =
            σ * empiricalMartingale P ℱ W' D t (fun r => propagator D ρ r t (Torus.realMode k)) X t ζ -
            σ * empiricalMartingale P ℱ W' D s' (fun r => propagator D ρ r s' (Torus.realMode k)) X s' ζ := by
          filter_upwards [h1, h2] with ζ e1 e2
          rw [mmm_fc_sub, ← mmm_eval_realMode, ← mmm_eval_realMode, e1, e2]
        obtain ⟨ft, hft⟩ := mmm_c12_prop hd s hs0 hsd (mStar d + 1 + 2) hm Rg MB Λ VB D ν₀ T ρ hAd
          ht hsm.1
        obtain ⟨ft', hft'⟩ := mmm_c12_prop hd s hs0 hsd (mStar d + 1 + 2) hm Rg MB Λ VB D ν₀ T ρ hAd
          hs' hsm.1
        have hΦ := isProgressiveL2_empiricalNoiseIntegrand (P := P) hX ht.1 (D := D) hft
        have hΦ' := isProgressiveL2_empiricalNoiseIntegrand (P := P) hX hs'.1 (D := D) hft'
        have hnorm := mmm_sobolevNorm_realMode (d := d) ℓ k
        have hB₁ : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x j,
            |Torus.grad (propagator D ρ r t (Torus.realMode k)) x j| ≤ C₂ * Lattice.jp k.1 ^ ℓ := by
          intro r hr x j
          have := (hP D ρ hAd hν j x).1 r t hr.1 hr.2 ht.2 _ hsm.1
          rwa [hnorm] at this
        have hB₂ : ∀ r ∈ Set.Icc (0 : ℝ) s', ∀ x j,
            |Torus.grad (propagator D ρ r t (Torus.realMode k)) x j -
              Torus.grad (propagator D ρ r s' (Torus.realMode k)) x j| ≤
              C₃ * |t - s'| * Lattice.jp k.1 ^ ℓ := by
          intro r hr x j
          have := (hP D ρ hAd hν j x).2 r s' t hr.1 hr.2 hst ht.2 _ hsm.1
          rwa [hnorm] at this
        calc ∫⁻ ζ, ‖NegSobolev.fourierCoeff (M t ζ - M s' ζ) k‖ₑ ^ 4 ∂P
            = ∫⁻ ζ, ‖σ * empiricalMartingale P ℱ W' D t (fun r => propagator D ρ r t (Torus.realMode k)) X t ζ -
            σ * empiricalMartingale P ℱ W' D s' (fun r => propagator D ρ r s' (Torus.realMode k)) X s' ζ‖ₑ ^ 4
              ∂P := lintegral_congr_ae (hae.mono fun ζ h => by simp only [h])
          _ ≤ ENNReal.ofReal (σ ^ 4 * (512 / 27 : ℝ) ^ 2 *
              (mmmNu N d D.invβ * (s' * (C₃ * |t - s'| * Lattice.jp k.1 ^ ℓ) ^ 2 +
                (t - s') * (C₂ * Lattice.jp k.1 ^ ℓ) ^ 2)) ^ 2) :=
              mmm_mode_fourth hW D X hs'.1 hst hΦ hΦ' _ _ hB₁ hB₂ σ
          _ ≤ ENNReal.ofReal (A * Lattice.jp k.1 ^ (4 * ℓ) * |t - s'| ^ 2) := by
              refine ENNReal.ofReal_le_ofReal ?_
              have hu4 : Lattice.jp k.1 ^ (4 * ℓ) = (Lattice.jp k.1 ^ ℓ) ^ 4 := by
                rw [show 4 * ℓ = ℓ * ((4 : ℕ) : ℝ) by push_cast; ring,
                  Real.rpow_mul_natCast (Torus.jp_pos k.1).le]
              rw [hu4]
              exact mmm_real_bound σ (mmmNu N d D.invβ) (Lattice.jp k.1 ^ ℓ) C₂ C₃ T s' t d
                (Nat.cast_nonneg d) hσν hν0 hs'.1 hst ht.2
      have hq : ((qT d : ℕ) : ℝ) = ℓ + d + 2 := mmm_cast d
      have hs := mmm_sum_fourth P ℓ ((qT d : ℕ) : ℝ) hq (fun ζ => M t ζ - M s' ζ) hmeasF A
        (|t - s'| ^ 2) hA0 (sq_nonneg _) hmode
      refine hs.trans (le_of_eq ?_)
      congr 1; ring
    intro s' hs' t ht
    rcases le_total s' t with h | h
    · exact core s' hs' t ht h
    · have := core t ht s' hs' h
      rw [abs_sub_comm] at this
      refine le_trans (le_of_eq ?_) this
      exact lintegral_congr fun ζ => by rw [enorm_sub_rev]
  · refine ⟨0, ?_⟩
    intro Ω mΩ P _ ℱ N hN W' X D ρ σ hA
    exfalso
    apply hcase
    have h0 := D.hs0
    have h1 := D.hsd
    have hs := hA.hs
    rw [hs] at h0 h1
    refine ⟨?_, h0, h1⟩
    have : (0 : ℝ) < d := lt_of_le_of_lt h0 h1
    exact_mod_cast this


/-- **(b') per-mode form** of `mmm_second_moment_N`: for the Fourier mode `e_k`,
`E|σ · M_N^t[U^{·,t}e_k]|² ≤ C jp_k^{2ℓ}`, `ℓ = mStar d + 3`. -/
theorem mmm_second_moment_mode (s : ℝ) (Rg : Regime) (ν₀ MB Λ T VB νbar : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) {N : ℕ} (_ : 1 ≤ N)
      (W' : ℝ≥0 → Ω → Fin N × Fin d → ℝ) (X : ℝ≥0 → Ω → Config d N) (D : DynData d)
      (ρ : ℝ → Torus d → ℝ) (σ : ℝ),
      AdjointData s (mStar d + 1 + 2) Rg MB Λ VB D ν₀ T ρ → D.invβ ≤ νbar →
      σ ^ 2 * D.invβ / N ≤ 1 → IsBrownianFiltration P ℱ W' → IsProgressive ℱ (ofNNRealTime X) →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : NonzeroLattice d,
        ∫⁻ ζ, ‖σ * empiricalMartingale P ℱ W' D t
            (fun r => propagator D ρ r t (Torus.realMode k)) X t ζ‖ₑ ^ 2 ∂P ≤
          ENNReal.ofReal (C * Lattice.jp k.1 ^ (2 * ((mStar d + 1 + 2 : ℕ) : ℝ))) := by
  obtain ⟨C, hC0, hC⟩ := mmm_second_moment_N (d := d) s Rg ν₀ MB Λ T VB νbar
  refine ⟨C, hC0, ?_⟩
  intro Ω mΩ P _ ℱ N hN W' X D ρ σ hA hν hσ hW hX t ht k
  have hsm := mpk_test_realMode (d := d) k
  refine (hC P ℱ hN W' X D ρ σ hA hν hσ hW hX t ht _ hsm.1).trans (le_of_eq ?_)
  rw [mmm_sobolevNorm_realMode, Torus.jp_rpow_sq]

/-- the weights `jp_k^{-2q} · jp_k^{2ℓ}` of `Σ_k w_k E|M^t[e_k]|²` are summable (`q = qT d`,
`ℓ = mStar d + 3`). -/
theorem mmm_weighted_summable :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(2 * ((qT d : ℕ) : ℝ))) *
      Lattice.jp k.1 ^ (2 * ((mStar d + 1 + 2 : ℕ) : ℝ)) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h := summable_jp_rpow (d := d) ((d : ℝ) + 2) (by linarith)
  refine h.congr fun k => ?_
  rw [← Real.rpow_add (Torus.jp_pos k.1), mmm_cast]
  congr 1; ring

/-! ### The theorem -/

theorem path_martingale_modulus_torus_moment (s : ℝ) (Rg : PDE.Regime)
    (ν₀ MB Λ T VB C₀ Cc νbar : ℝ) :
    ∃ C : ℝ, ∀ (S : Main.MainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      ∀ (R : ∀ N, Main.Realization d N) (𝔈 : ℕ → ℝ),
        Main.TorusStanding S R Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) C₀ Cc 𝔈 →
        ∀ (ℱ : ∀ N, Filtration ℝ (R N).mΩ) (W' : ∀ N, ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ),
        (∀ N : ℕ, 1 ≤ N → IsFilteredSolution (R N).P (ℱ N) (W' N) (R N).W (R N).X) →
        ∀ (Mq : ∀ N, ℝ → (R N).Ω → NegSobolev d ((qT d : ℕ) : ℝ)),
        (∀ N : ℕ, 1 ≤ N → IsStochConvT (R N).P (ℱ N) (W' N) (S.dyn N) (S.ρ N) (S.sigma N)
          ((qT d : ℕ) : ℝ) T (R N).X (Mq N)) →
        (∀ N : ℕ, 1 ≤ N → ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ζ, ‖Mq N t ζ - Mq N s' ζ‖ₑ ^ 4 ∂(R N).P ≤ ENNReal.ofReal (C * |t - s'| ^ 2)) := by
  obtain ⟨C, hC⟩ := mmm_fourth_moment_N (d := d) s Rg ν₀ MB Λ T VB νbar
  refine ⟨C, ?_⟩
  intro S hs hT hν R 𝔈 hS ℱ W' hF Mq hM N hN s' hs' t ht
  have hq : PDE.mStar d ≤ Main.gammaIdx d + 2 := by unfold Main.gammaIdx; omega
  have hA0 := HRS.Main.A9.a9_adjointData hq hS hN
  rw [hs, hT] at hA0
  have hA : AdjointData s (mStar d + 1 + 2) Rg MB Λ VB (S.dyn N) ν₀ T (S.ρ N) :=
    StabAux.adjointData_mono (by unfold Main.gammaIdx; omega) hA0
  have hσ : S.sigma N ^ 2 * (S.dyn N).invβ / N ≤ 1 := by
    have h1 := (HRS.Main.A8P.a8p_q_bounds S hN).2
    rw [HRS.Main.A8P.a8p_q_eq] at h1
    exact h1
  exact hC (R N).P (ℱ N) hN (W' N) (R N).X (S.dyn N) (S.ρ N) (S.sigma N) hA (hν N) hσ
    (hF N hN).brownian (hF N hN).progressive (Mq N) (hM N hN) s' hs' t ht

end HRS.MP.MartMod
