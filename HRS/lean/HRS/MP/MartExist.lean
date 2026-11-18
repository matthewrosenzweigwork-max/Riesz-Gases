import HRS.MP.MartModulus
import HRS.Uniform.Q54cAux11

/-!
# Packet MPMEX: existence of the `H^{-q_T}`-valued thermal stochastic convolution (`IsStochConvT`)

For one `N ≥ 1` the pairings `Y_φ = σ M^t[U^{·,t}φ]` form an a.s. linear family of `L²(P)`
random variables with `‖Y_φ‖²_{L²} ≤ C ‖φ‖²_{H^ℓ}` (`mmm_second_moment_N`).  The Fourier coordinates
`c_k = Y_{e_k}` therefore satisfy `Σ_k jp_k^{-2q} c_k² < ∞` a.s. (`q = q_T`), define an `H^{-q}`-valued
random variable `M`, and `eval M φ = Y_φ` a.s. for every smooth mean-zero `φ` (the partial sums of
`Σ_k c_k φ_k` converge in `L²` to `Y_φ` and a.s. to `eval M φ`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MP.MartExist

open HRS HRS.PDE HRS.Whole.AppendixALemmas HRS.MP.KernIncr HRS.MP.MartMod

variable {d : ℕ}

/-! ### Stage 1: deterministic facts -/

/-- the tail of the Sobolev norm of `φ - φ_T` tends to `0` along finite truncations. -/
theorem mex_tail (m : ℝ) {φ : Torus d → ℝ} (hφ : MPKTest φ) :
    Tendsto (fun T : Finset (NonzeroLattice d) => sobolevNorm m
      (fun x => 1 * φ x + (-1) * FieldSingAux.trigPoly T (Torus.funRealCoeff φ) x) ^ 2)
      atTop (𝓝 0) := by
  classical
  have hS := (A33.a33_memSob m hφ.1).2
  set w : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2
    with hw
  have hcontφ : Continuous φ := mpk_cont_of_smooth hφ.1
  have hcomb : ∀ T : Finset (NonzeroLattice d),
      MPKTest (fun x => 1 * φ x + (-1) * FieldSingAux.trigPoly T (Torus.funRealCoeff φ) x) :=
    fun T => mpk_test_comb hφ (mpk_test_trigPoly T _) 1 (-1)
  have hnorm : ∀ T : Finset (NonzeroLattice d),
      sobolevNorm m (fun x => 1 * φ x + (-1) * FieldSingAux.trigPoly T (Torus.funRealCoeff φ) x) ^ 2 =
        ∑' k, (if k ∈ T then 0 else w k) := by
    intro T
    unfold sobolevNorm
    rw [(hcomb T).2, zero_pow two_ne_zero, zero_add]
    have h0 : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) *
        Torus.funRealCoeff (fun x => 1 * φ x + (-1) * FieldSingAux.trigPoly T
          (Torus.funRealCoeff φ) x) k ^ 2 :=
      tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos k.1).le _) (sq_nonneg _)
    rw [Real.sq_sqrt h0]
    refine tsum_congr fun k => ?_
    rw [A33.a33_funRealCoeff_lin hcontφ (PDE.ClassicalAux.continuous_of_isCk
      (PDE.ClassicalAux.isCk_of_le (by exact_mod_cast le_top) (FieldSingAux.isSmooth_trigPoly T _)))
      1 (-1) k, FieldSingAux.funRealCoeff_trigPoly]
    by_cases hk : k ∈ T
    · simp [hk]
    · simp [hk, hw]
  simp_rw [hnorm]
  have e : ∀ T : Finset (NonzeroLattice d),
      ∑' k, (if k ∈ T then 0 else w k) = (∑' k, w k) - ∑ k ∈ T, w k := by
    intro T
    have hsF : Summable (fun k => if k ∈ T then w k else 0) :=
      summable_of_ne_finset_zero (s := T) fun k hk => by simp [hk]
    have : (fun k => if k ∈ T then (0 : ℝ) else w k) =
        fun k => w k - (if k ∈ T then w k else 0) := by
      funext k; split_ifs <;> simp
    have hind : ∑' k, (if k ∈ T then w k else 0) = ∑ k ∈ T, w k := by
      rw [tsum_eq_sum (s := T) (fun k hk => by simp [hk])]
      exact Finset.sum_congr rfl fun k hk => by simp [hk]
    rw [this, hS.tsum_sub hsF, hind]
  simp_rw [e]
  have h2 : Tendsto (fun T : Finset (NonzeroLattice d) => (∑' k, w k) - ∑ k ∈ T, w k) atTop
      (𝓝 ((∑' k, w k) - ∑' k, w k)) := tendsto_const_nhds.sub hS.hasSum
  simpa using h2

/-- the weighted AM-GM bound for the products `c_k φ_k`. -/
theorem mex_amgm (j : ℝ) (hj : 0 < j) (q c b : ℝ) :
    |c * b| ≤ (j ^ (-(2 * q)) * c ^ 2 + j ^ (2 * q) * b ^ 2) / 2 := by
  have hA : 0 < j ^ (2 * q) := Real.rpow_pos_of_pos hj _
  have e : j ^ (-(2 * q)) = (j ^ (2 * q))⁻¹ := Real.rpow_neg hj.le _
  rw [e]
  set A := j ^ (2 * q) with hAdef
  rw [abs_mul]
  have h1 : 2 * (|c| * |b|) ≤ A⁻¹ * c ^ 2 + A * b ^ 2 := by
    have h2 : 0 ≤ A⁻¹ * (|c| - A * |b|) ^ 2 := mul_nonneg (inv_nonneg.2 hA.le) (sq_nonneg _)
    have h3 : A⁻¹ * (|c| - A * |b|) ^ 2 =
        A⁻¹ * c ^ 2 + A * b ^ 2 - 2 * (|c| * |b|) := by
      have hc : c ^ 2 = |c| ^ 2 := (sq_abs c).symm
      have hb : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
      rw [hc, hb]
      field_simp
      ring
    linarith
  linarith

/-! ### Stage 2: a.s. linear, `L²`-bounded families of random variables -/

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω]

/-- the finite trigonometric polynomials are mapped to the corresponding finite combinations -/
theorem mex_trig_ae {P : Measure Ω} (Y : (Torus d → ℝ) → Ω → ℝ)
    (hlin : ∀ φ ψ : Torus d → ℝ, MPKTest φ → MPKTest ψ → ∀ α β : ℝ,
      Y (fun x => α * φ x + β * ψ x) =ᵐ[P] fun ζ => α * Y φ ζ + β * Y ψ ζ)
    (S : Finset (NonzeroLattice d)) (b : NonzeroLattice d → ℝ) :
    Y (FieldSingAux.trigPoly S b) =ᵐ[P] fun ζ => ∑ k ∈ S, Y (Torus.realMode k) ζ * b k := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have e : FieldSingAux.trigPoly (∅ : Finset (NonzeroLattice d)) b =
        fun x => (0 : ℝ) * (fun _ : Torus d => (0 : ℝ)) x + (0 : ℝ) * (fun _ : Torus d => (0 : ℝ)) x := by
      funext x; simp [FieldSingAux.trigPoly]
    rw [e]
    filter_upwards [hlin _ _ mpk_test_zero mpk_test_zero 0 0] with ζ h
    simpa using h
  | insert k S hk ih =>
    have e : FieldSingAux.trigPoly (insert k S) b =
        fun x => b k * Torus.realMode k x + 1 * FieldSingAux.trigPoly S b x := by
      funext x; simp [FieldSingAux.trigPoly, Finset.sum_insert hk]
    rw [e]
    filter_upwards [hlin _ _ (mpk_test_realMode k) (mpk_test_trigPoly S b) (b k) 1, ih] with ζ h h2
    rw [h, h2, Finset.sum_insert hk]
    ring

/-- an element of `H^{-q}` with prescribed coordinates `c k` on the set where the weighted series
converges. -/
theorem mex_construct (q : ℝ) (c : NonzeroLattice d → Ω → ℝ)
    (hc : ∀ k, Measurable (c k)) :
    ∃ M : Ω → NegSobolev d q, Measurable M ∧ ∀ ζ : Ω,
      (∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * q)) * c k ζ ^ 2) < ⊤) →
        ∀ k, NegSobolev.fourierCoeff (M ζ) k = c k ζ := by
  classical
  set w : Ω → ℝ≥0∞ := fun ζ =>
    ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * q)) * c k ζ ^ 2) with hwdef
  have hw : Measurable w := by
    refine Measurable.tsum fun k => ENNReal.measurable_ofReal.comp ?_
    exact measurable_const.mul ((hc k).pow_const 2)
  set G : Set Ω := {ζ | w ζ < ⊤} with hGdef
  have hG : MeasurableSet G := measurableSet_lt hw measurable_const
  have hmem : ∀ ζ ∈ G,
      Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-q) * c k ζ) 2 := by
    intro ζ hζ
    rw [Torus.memℓp_two_iff]
    have hs := ENNReal.summable_toReal (f := fun k : NonzeroLattice d =>
      ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * q)) * c k ζ ^ 2)) hζ.ne
    refine hs.congr fun k => ?_
    have h0 : 0 ≤ Lattice.jp k.1 ^ (-(2 * q)) * c k ζ ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (Torus.jp_pos k.1).le _) (sq_nonneg _)
    rw [ENNReal.toReal_ofReal h0, mul_pow, Torus.jp_rpow_sq]
    ring_nf
  refine ⟨fun ζ => if ζ ∈ G then NegSobolev.ofSeq q (fun k => c k ζ) else 0, ?_, ?_⟩
  · refine HRS.Uniform.Q54c.measurable_of_coord fun k => ?_
    have e : (fun ζ => NegSobolev.coord ((if ζ ∈ G then NegSobolev.ofSeq q (fun k => c k ζ) else 0 :
        NegSobolev d q)) k) = G.indicator (fun ζ => Lattice.jp k.1 ^ (-q) * c k ζ) := by
      funext ζ
      by_cases h : ζ ∈ G
      · simp only [h, ite_true, Set.indicator_of_mem]
        exact NegSobolev.coord_ofSeq_of_mem _ (hmem ζ h) k
      · simp only [h, ite_false, Set.indicator_of_notMem, not_false_eq_true]
        rfl
    rw [e]
    exact (measurable_const.mul (hc k)).indicator hG
  · intro ζ hζ k
    have h : ζ ∈ G := hζ
    simp only [h, ite_true]
    unfold NegSobolev.fourierCoeff
    rw [NegSobolev.coord_ofSeq_of_mem _ (hmem ζ h) k, ← mul_assoc,
      ← Real.rpow_add (Torus.jp_pos k.1)]
    simp

/-- **Abstract existence**: an a.s. linear family `φ ↦ Y φ` of measurable `L²` random variables with
`E|Y φ|² ≤ C ‖φ‖²_{H^ℓ}` on the smooth mean-zero tests is represented by an `H^{-q}`-valued random
variable, provided `Σ_k jp_k^{-2q + 2ℓ} < ∞`. -/
theorem mex_abstract (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : (Torus d → ℝ) → Ω → ℝ) (C ℓ q : ℝ) (hC0 : 0 ≤ C)
    (hmeas : ∀ φ : Torus d → ℝ, MPKTest φ → Measurable (Y φ))
    (hbd : ∀ φ : Torus d → ℝ, MPKTest φ →
      ∫⁻ ζ, ‖Y φ ζ‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (C * sobolevNorm ℓ φ ^ 2))
    (hlin : ∀ φ ψ : Torus d → ℝ, MPKTest φ → MPKTest ψ → ∀ α β : ℝ,
      Y (fun x => α * φ x + β * ψ x) =ᵐ[P] fun ζ => α * Y φ ζ + β * Y ψ ζ)
    (hsum : Summable fun k : NonzeroLattice d =>
      Lattice.jp k.1 ^ (-(2 * q)) * Lattice.jp k.1 ^ (2 * ℓ)) :
    ∃ M : Ω → NegSobolev d q, Measurable M ∧
      ∀ φ : Torus d → ℝ, MPKTest φ → ∀ᵐ ζ ∂P, NegSobolev.eval (M ζ) φ = Y φ ζ := by
  classical
  set c : NonzeroLattice d → Ω → ℝ := fun k => Y (Torus.realMode k) with hcdef
  have hc : ∀ k, Measurable (c k) := fun k => hmeas _ (mpk_test_realMode k)
  have hck : ∀ k, ∫⁻ ζ, ‖c k ζ‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (C * Lattice.jp k.1 ^ (2 * ℓ)) := by
    intro k
    have := hbd _ (mpk_test_realMode k)
    rwa [mmm_sobolevNorm_realMode, Torus.jp_rpow_sq] at this
  set wf : Ω → ℝ≥0∞ := fun ζ =>
    ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * q)) * c k ζ ^ 2) with hwf
  have hwm : Measurable wf := by
    refine Measurable.tsum fun k => ENNReal.measurable_ofReal.comp ?_
    exact measurable_const.mul ((hc k).pow_const 2)
  have hlint : ∫⁻ ζ, wf ζ ∂P ≠ ⊤ := by
    have h1 : ∫⁻ ζ, wf ζ ∂P = ∑' k : NonzeroLattice d, ∫⁻ ζ,
        ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * q)) * c k ζ ^ 2) ∂P := by
      refine lintegral_tsum fun k => ?_
      exact (ENNReal.measurable_ofReal.comp
        (measurable_const.mul ((hc k).pow_const 2))).aemeasurable
    have h2 : ∀ k : NonzeroLattice d, ∫⁻ ζ,
        ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * q)) * c k ζ ^ 2) ∂P ≤
          ENNReal.ofReal (C * (Lattice.jp k.1 ^ (-(2 * q)) * Lattice.jp k.1 ^ (2 * ℓ))) := by
      intro k
      have ha : 0 ≤ Lattice.jp k.1 ^ (-(2 * q)) := Real.rpow_nonneg (Torus.jp_pos k.1).le _
      have e : ∀ ζ, ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * q)) * c k ζ ^ 2) =
          ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * q))) * ‖c k ζ‖ₑ ^ 2 := by
        intro ζ
        rw [ENNReal.ofReal_mul ha, mmm_ofReal_norm_sq]
      simp_rw [e]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * q))) * ∫⁻ ζ, ‖c k ζ‖ₑ ^ 2 ∂P
          ≤ ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * q))) *
            ENNReal.ofReal (C * Lattice.jp k.1 ^ (2 * ℓ)) := by gcongr; exact hck k
        _ = _ := by
          rw [← ENNReal.ofReal_mul ha]
          congr 1; ring
    have h3 : Summable fun k : NonzeroLattice d =>
        C * (Lattice.jp k.1 ^ (-(2 * q)) * Lattice.jp k.1 ^ (2 * ℓ)) := hsum.mul_left C
    have h4 : ∀ k : NonzeroLattice d,
        0 ≤ C * (Lattice.jp k.1 ^ (-(2 * q)) * Lattice.jp k.1 ^ (2 * ℓ)) := fun k =>
      mul_nonneg hC0 (mul_nonneg (Real.rpow_nonneg (Torus.jp_pos k.1).le _)
        (Real.rpow_nonneg (Torus.jp_pos k.1).le _))
    rw [h1]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum h2)
    rw [← ENNReal.ofReal_tsum_of_nonneg h4 h3]
    exact ENNReal.ofReal_ne_top
  have hfin : ∀ᵐ ζ ∂P, wf ζ < ⊤ := ae_lt_top hwm hlint
  obtain ⟨M, hM, hMc⟩ := mex_construct q c hc
  refine ⟨M, hM, fun φ hφ => ?_⟩
  set b : NonzeroLattice d → ℝ := Torus.funRealCoeff φ with hb
  have hsT := mex_trig_ae (P := P) Y hlin
  have hdiff : ∀ T : Finset (NonzeroLattice d), ∀ᵐ ζ ∂P,
      Y φ ζ - ∑ k ∈ T, c k ζ * b k =
        Y (fun x => 1 * φ x + (-1) * FieldSingAux.trigPoly T b x) ζ := by
    intro T
    filter_upwards [hlin φ _ hφ (mpk_test_trigPoly T b) 1 (-1), hsT T b] with ζ h h2
    rw [h, h2]
    ring
  -- `L²` convergence of the partial sums to `Y φ`
  have hL2 : Tendsto (fun T : Finset (NonzeroLattice d) =>
      eLpNorm ((fun ζ => ∑ k ∈ T, c k ζ * b k) - Y φ) 2 P) atTop (𝓝 0) := by
    have hτ := mex_tail ℓ hφ
    have hτ' : Tendsto (fun T : Finset (NonzeroLattice d) => ENNReal.ofReal (C *
        sobolevNorm ℓ (fun x => 1 * φ x + (-1) * FieldSingAux.trigPoly T b x) ^ 2))
        atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (hτ.const_mul C)
      simpa using this
    have hup : Tendsto (fun T : Finset (NonzeroLattice d) => (ENNReal.ofReal (C *
        sobolevNorm ℓ (fun x => 1 * φ x + (-1) * FieldSingAux.trigPoly T b x) ^ 2)) ^ (1 / (2 : ℝ)))
        atTop (𝓝 0) := by
      have h0 : (0 : ℝ≥0∞) ^ (1 / (2 : ℝ)) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hτ'
      rwa [h0] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun T => bot_le)
      (fun T => ?_)
    have hT : MPKTest (fun x => 1 * φ x + (-1) * FieldSingAux.trigPoly T b x) :=
      mpk_test_comb hφ (mpk_test_trigPoly T b) 1 (-1)
    have hmT : AEStronglyMeasurable ((fun ζ => ∑ k ∈ T, c k ζ * b k) - Y φ) P :=
      ((Finset.measurable_sum _ fun k _ => (hc k).mul_const (b k)).sub (hmeas φ hφ)).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hmT]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    have e2 : ∀ ζ, ‖((fun ζ => ∑ k ∈ T, c k ζ * b k) - Y φ) ζ‖ₑ ^ (ENNReal.toReal 2) =
        ‖Y φ ζ - ∑ k ∈ T, c k ζ * b k‖ₑ ^ 2 := by
      intro ζ
      simp only [Pi.sub_apply, ENNReal.toReal_ofNat]
      rw [enorm_sub_rev]
      exact ENNReal.rpow_two _
    simp_rw [e2]
    calc ∫⁻ ζ, ‖Y φ ζ - ∑ k ∈ T, c k ζ * b k‖ₑ ^ 2 ∂P
        = ∫⁻ ζ, ‖Y (fun x => 1 * φ x + (-1) * FieldSingAux.trigPoly T b x) ζ‖ₑ ^ 2 ∂P :=
          lintegral_congr_ae ((hdiff T).mono fun ζ h => by simp only [h])
      _ ≤ _ := hbd _ hT
  have hconv : TendstoInMeasure P (fun T : Finset (NonzeroLattice d) => fun ζ => ∑ k ∈ T, c k ζ * b k)
      atTop (Y φ) := tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hL2
  obtain ⟨ns, hns, hae⟩ := hconv.exists_seq_tendsto_ae'
  have hbs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * q) * b k ^ 2 :=
    (A33.a33_memSob q hφ.1).2
  filter_upwards [hae, hfin] with ζ h1 h2
  have hs1 := ENNReal.summable_toReal (f := fun k : NonzeroLattice d =>
      ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * q)) * c k ζ ^ 2)) h2.ne
  have hs2 : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(2 * q)) * c k ζ ^ 2 :=
    hs1.congr fun k => ENNReal.toReal_ofReal (mul_nonneg
      (Real.rpow_nonneg (Torus.jp_pos k.1).le _) (sq_nonneg _))
  have hs3 : Summable fun k : NonzeroLattice d => c k ζ * b k :=
    Summable.of_norm_bounded (((hs2.add hbs).div_const 2)) fun k => by
      rw [Real.norm_eq_abs]
      exact mex_amgm _ (Torus.jp_pos k.1) q _ _
  have hev : NegSobolev.eval (M ζ) φ = ∑' k, c k ζ * b k := by
    unfold NegSobolev.eval
    exact tsum_congr fun k => by rw [hMc ζ h2 k]
  have h3 : Tendsto (fun T : Finset (NonzeroLattice d) => ∑ k ∈ T, c k ζ * b k) atTop
      (𝓝 (NegSobolev.eval (M ζ) φ)) := by
    rw [hev]; exact hs3.hasSum
  exact tendsto_nhds_unique (h3.comp hns) h1

/-! ### Stage 3: the stochastic input for one `N` -/

section PerN

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ}

/-- Linearity of the thermal pairing in the test function (a.s.), for `t ∈ [0,T]`. -/
theorem mex_lin (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → Fin N × Fin d → ℝ) (X : ℝ≥0 → Ω → Config d N) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (σ T : ℝ) (hW : IsBrownianFiltration P ℱ W')
    (hX : IsProgressive ℱ (ofNNRealTime X)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hft : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      ∃ ft : ℝ → Torus d → ℝ, IsC12Test t (fun r => propagator D ρ r t φ) ft)
    (hlinG : ∀ (j : Fin d) (x : Torus d), ∀ r : ℝ, 0 ≤ r → r ≤ t → ∀ φ ψ : Torus d → ℝ, ∀ α β : ℝ,
        Torus.IsSmooth φ → Torus.IsSmooth ψ →
        Torus.grad (propagator D ρ r t (fun y => α * φ y + β * ψ y)) x j =
          α * Torus.grad (propagator D ρ r t φ) x j + β * Torus.grad (propagator D ρ r t ψ) x j)
    {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) (α β : ℝ) :
    (fun ζ => σ * empiricalMartingale P ℱ W' D t
        (fun r => propagator D ρ r t (fun x => α * φ x + β * ψ x)) X t ζ) =ᵐ[P]
      fun ζ => α * (σ * empiricalMartingale P ℱ W' D t (fun r => propagator D ρ r t φ) X t ζ) +
        β * (σ * empiricalMartingale P ℱ W' D t (fun r => propagator D ρ r t ψ) X t ζ) := by
  obtain ⟨ftφ, hftφ⟩ := hft φ hφ
  obtain ⟨ftψ, hftψ⟩ := hft ψ hψ
  have hΦφ := isProgressiveL2_empiricalNoiseIntegrand (P := P) hX ht.1 (D := D) hftφ
  have hΦψ := isProgressiveL2_empiricalNoiseIntegrand (P := P) hX ht.1 (D := D) hftψ
  set Φφ := empiricalNoiseIntegrand D t (fun r => propagator D ρ r t φ) X with hΦφdef
  set Φψ := empiricalNoiseIntegrand D t (fun r => propagator D ρ r t ψ) X with hΦψdef
  have hcomb : empiricalNoiseIntegrand D t
      (fun r => propagator D ρ r t (fun x => α * φ x + β * ψ x)) X =
      fun s ω => α • Φφ s ω + β • Φψ s ω := by
    funext s ω k
    by_cases hs : s ∈ Set.Icc (0 : ℝ) t
    · simp only [hΦφdef, hΦψdef, empiricalNoiseIntegrand, hs, ite_true, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      rw [hlinG k.2 _ s hs.1 hs.2 φ ψ α β hφ hψ]
      ring
    · simp [hΦφdef, hΦψdef, empiricalNoiseIntegrand, hs]
  have h1 := isItoIntegral_itoIntegral hW (hΦφ.smul α)
  have h2 := isItoIntegral_itoIntegral hW (hΦψ.smul β)
  have h3 := isItoIntegral_itoIntegral hW ((hΦφ.smul α).add (hΦψ.smul β))
  have hadd := IsItoIntegral.ae_eq_add hW (hΦφ.smul α) (hΦψ.smul β) h1 h2 h3 t
  have hs1 := IsItoIntegral.ae_eq_smul hW hΦφ (isItoIntegral_itoIntegral hW hΦφ) α h1 t
  have hs2 := IsItoIntegral.ae_eq_smul hW hΦψ (isItoIntegral_itoIntegral hW hΦψ) β h2 t
  unfold empiricalMartingale
  rw [hcomb]
  filter_upwards [hadd, hs1, hs2] with ζ ha h1' h2'
  rw [ha, h1', h2']
  ring

/-- Existence of the thermal stochastic convolution for one fixed `N ≥ 1`. -/
theorem mex_per_N {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (hN : 1 ≤ N)
    (W' : ℝ≥0 → Ω → Fin N × Fin d → ℝ) (X : ℝ≥0 → Ω → Config d N) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (σ : ℝ) (s : ℝ) (Rg : Regime) (ν₀ MB Λ T VB νbar : ℝ)
    (hA : AdjointData s (qT d) Rg MB Λ VB D ν₀ T ρ) (hν : D.invβ ≤ νbar)
    (hσ : σ ^ 2 * D.invβ / N ≤ 1) (hW : IsBrownianFiltration P ℱ W')
    (hX : IsProgressive ℱ (ofNNRealTime X)) :
    ∃ M : ℝ → Ω → NegSobolev d ((qT d : ℕ) : ℝ),
      IsStochConvT P ℱ W' D ρ σ ((qT d : ℕ) : ℝ) T X M := by
  have h0 := D.hs0
  have h1 := D.hsd
  have hs := hA.hs
  rw [hs] at h0 h1
  have hd : 1 ≤ d := by
    have : (0 : ℝ) < d := lt_of_le_of_lt h0 h1
    exact_mod_cast this
  obtain ⟨C, hC0, hC⟩ := mmm_second_moment_N (d := d) s Rg ν₀ MB Λ T VB νbar
  obtain ⟨C₂, C₃, -, -, hP⟩ := mpk_pde hd s h0 h1 Rg ν₀ MB Λ T VB νbar
  have hA' : AdjointData s (mStar d + 1 + 2) Rg MB Λ VB D ν₀ T ρ :=
    StabAux.adjointData_mono (by unfold qT Main.gammaIdx; omega) hA
  have key : ∀ t : ℝ, ∃ F : Ω → NegSobolev d ((qT d : ℕ) : ℝ), Measurable F ∧
      (t ∈ Set.Icc (0 : ℝ) T → ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → Torus.mean φ = 0 →
        ∀ᵐ ζ ∂P, NegSobolev.eval (F ζ) φ =
          σ * empiricalMartingale P ℱ W' D t (fun r => propagator D ρ r t φ) X t ζ) := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · have hft : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
          ∃ ft : ℝ → Torus d → ℝ, IsC12Test t (fun r => propagator D ρ r t φ) ft :=
        fun φ hφ => mmm_c12_prop hd s h0 h1 (mStar d + 1 + 2) (mmm_ell_bounds d).1 Rg MB Λ VB D ν₀ T ρ
          hA' ht hφ
      obtain ⟨M, hM, hMe⟩ := mex_abstract (d := d) P
        (fun φ ζ => σ * empiricalMartingale P ℱ W' D t (fun r => propagator D ρ r t φ) X t ζ)
        C ((mStar d + 1 + 2 : ℕ) : ℝ) ((qT d : ℕ) : ℝ) hC0
        (fun φ _ => (measurable_const.mul
          (((adapted_itoIntegral P ℱ W' _ t).mono (ℱ.le t) le_rfl))))
        (fun φ hφ => hC P ℱ hN W' X D ρ σ hA' hν hσ hW hX t ht φ hφ.1)
        (fun φ ψ hφ hψ α β => mex_lin P ℱ W' X D ρ σ T hW hX ht hft
          (fun j x r hr hrt φ ψ α β hφ hψ => (hP D ρ hA hν j x).2.2 r t hr hrt ht.2 φ ψ α β hφ hψ)
          hφ.1 hψ.1 α β)
        mmm_weighted_summable
      exact ⟨M, hM, fun _ φ hφ hmean => hMe φ ⟨hφ, hmean⟩⟩
    · exact ⟨fun _ => 0, measurable_const, fun h => absurd h ht⟩
  choose F hFm hFe using key
  exact ⟨F, hFm, fun t ht φ hφ hmean => hFe t ht φ hφ hmean⟩

end PerN

end Abstract

/-! ### The theorem -/

theorem mex_Mq_exists {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ} {𝔈 : ℕ → ℝ} (S : Main.MainData d)
    (R : ∀ N, Main.Realization d N)
    (hS : Main.TorusStanding S R Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) C₀ Cc 𝔈)
    (ℱ : ∀ N, Filtration ℝ (R N).mΩ) (W' : ∀ N, ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ)
    (hF : ∀ N : ℕ, 1 ≤ N → IsFilteredSolution (R N).P (ℱ N) (W' N) (R N).W (R N).X) :
    ∃ Mq : ∀ N, ℝ → (R N).Ω → NegSobolev d ((qT d : ℕ) : ℝ), ∀ N : ℕ, 1 ≤ N →
      IsStochConvT (R N).P (ℱ N) (W' N) (S.dyn N) (S.ρ N) (S.sigma N) ((qT d : ℕ) : ℝ) S.T (R N).X
        (Mq N) := by
  obtain ⟨νbar, hνb⟩ := S.invβ_bdd
  have hq : PDE.mStar d ≤ Main.gammaIdx d + 2 := by unfold Main.gammaIdx; omega
  have key : ∀ N : ℕ, ∃ M : ℝ → (R N).Ω → NegSobolev d ((qT d : ℕ) : ℝ), 1 ≤ N →
      IsStochConvT (R N).P (ℱ N) (W' N) (S.dyn N) (S.ρ N) (S.sigma N) ((qT d : ℕ) : ℝ) S.T (R N).X M := by
    intro N
    by_cases hN : 1 ≤ N
    · have hA : AdjointData S.s (qT d) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) :=
        HRS.Main.A9.a9_adjointData hq hS hN
      have hσ : S.sigma N ^ 2 * (S.dyn N).invβ / N ≤ 1 := by
        have h1 := (HRS.Main.A8P.a8p_q_bounds S hN).2
        rw [HRS.Main.A8P.a8p_q_eq] at h1
        exact h1
      obtain ⟨M, hM⟩ := mex_per_N (R N).P (ℱ N) hN (W' N) (R N).X (S.dyn N) (S.ρ N) (S.sigma N)
        S.s Rg ν₀ MB Λ S.T VB νbar hA (hνb N) hσ (hF N hN).brownian (hF N hN).progressive
      exact ⟨M, fun _ => hM⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hN⟩
  choose Mq hMq using key
  exact ⟨Mq, fun N hN => hMq N hN⟩

end HRS.MP.MartExist
