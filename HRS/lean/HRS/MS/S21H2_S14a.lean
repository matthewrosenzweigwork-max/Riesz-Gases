import HRS.MS.S21H2_S14aD5

/-!
# S21H2, packet R26-T3.S14a: spectral expansion of the centered physical interaction kernel

`r26t3_kernel_spectral` (contract verbatim up to the binder name `lam` for `λ`).  Route: the `KRep` operator `K` at the actual `μ₀` restricted to the centered classes
`V` is symmetric, nonnegative, and compact (Hilbert-Schmidt bound `‖K‖²_HS ≤ ‖c‖²` through the identity `K U = ∫ c(·,y) U(y)`); `V` is infinite dimensional; the eigenbasis
`(e_k, λ_k)` of `K|_V` gives all clauses.  `∑ λ_k² = ‖c‖²` by Parseval in the second variable for a.e. slice `c(x,·) ∈ L²_0(μ)` and `∫ e_k² = 1`; the partial sums converge by
Pythagoras in `L²(μ⊗μ)` (`s21h2_pyth`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole.Q34 HRS.MS.S111X2

theorem r26t3_kernel_spectral {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) :
    ∃ (lam : ℕ → ℝ) (e : ℕ → Euc p.d → ℝ),
      (∀ j, 0 ≤ lam j ∧ HRS.Whole.MemL2Zero (r26t3_mu R 0) (e j)) ∧
      (∀ i j, ∫ x, e i x * e j x ∂(r26t3_mu R 0) = if i = j then 1 else 0) ∧
      Summable (fun j => lam j ^ 2) ∧
      Tendsto (fun n => eLpNorm (fun z : Euc p.d × Euc p.d =>
        HRS.Whole.r2CenterKernel (r26t3_mu R 0) (fun x y => HRS.Whole.rieszKernel p.d p.s (x - y)) z.1 z.2 -
          ∑ j ∈ Finset.range n, lam j * e j z.1 * e j z.2) 2
        ((r26t3_mu R 0).prod (r26t3_mu R 0))) atTop (𝓝 0) ∧
      (∀ f : Euc p.d → ℝ, HRS.Whole.MemL2Zero (r26t3_mu R 0) f →
        (∀ j, ∫ x, f x * e j x ∂(r26t3_mu R 0) = 0) → f =ᵐ[r26t3_mu R 0] 0) := by
  haveI := s21h2_mu_prob hδ hδh R
  set μ := r26t3_mu R 0 with hμ
  have hk := (r26t3_interaction_hs hδ hδh R).1
  obtain ⟨Mg, K, hK⟩ := s21h2_krep_init hδ hδh R
  obtain ⟨b, lam, hlam, heig⟩ := s21h2_eigen_exists hK hk (s21h2_not_fin hδ hδh R)
  set c := HRS.Whole.r2CenterKernel μ (fun a b => HRS.Whole.rieszKernel p.d p.s (a - b)) with hc
  have hcm : MemLp (fun z : Euc p.d × Euc p.d => c z.1 z.2) 2 (μ.prod μ) :=
    s21h2_c_memLp μ (k := fun a b => HRS.Whole.rieszKernel p.d p.s (a - b)) hk
  set e : ℕ → Euc p.d → ℝ := fun k x => ((b k : s21h2_V μ) : Lp ℝ 2 μ) x with he
  have hem : ∀ k, MemLp (e k) 2 μ := fun k => Lp.memLp _
  have hmem : ∀ k, inner ℝ (one2 μ) ((b k : s21h2_V μ) : Lp ℝ 2 μ) = 0 := fun k => s21h2_mem_V.1 (b k).2
  have hmean : ∀ k, ∫ x, e k x ∂μ = 0 := fun k => s21h2_mean_zero (hmem k)
  have hon : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0 := by
    intro i j
    have h1 := orthonormal_iff_ite.1 b.orthonormal i j
    have h2 : inner ℝ ((b i : s21h2_V μ) : Lp ℝ 2 μ) ((b j : s21h2_V μ) : Lp ℝ 2 μ) =
        if i = j then 1 else 0 := by rw [← h1]; rfl
    rw [lp_inner] at h2
    exact h2
  have hKe : ∀ k, ∀ᵐ x ∂μ, ∫ y, c x y * e k y ∂μ = lam k * e k x := by
    intro k
    have h1 := s21h2_KC hK hk ((b k : s21h2_V μ) : Lp ℝ 2 μ) (hmem k)
    have h2 := Lp.coeFn_smul (lam k) ((b k : s21h2_V μ) : Lp ℝ 2 μ)
    filter_upwards [h1, h2] with x hx1 hx2
    calc ∫ y, c x y * e k y ∂μ = (K ((b k : s21h2_V μ) : Lp ℝ 2 μ)) x := hx1.symm
      _ = (lam k • ((b k : s21h2_V μ) : Lp ℝ 2 μ)) x := by rw [heig k]
      _ = lam k * e k x := hx2
  have hnu : Integrable (fun z : Euc p.d × Euc p.d => c z.1 z.2 ^ 2) (μ.prod μ) := hcm.integrable_sq
  have hv : Orthonormal ℝ (fun k => ((b k : s21h2_V μ) : Lp ℝ 2 μ)) :=
    b.orthonormal.comp_linearIsometry (s21h2_V μ).subtypeₗᵢ
  have hsum : Summable fun k => lam k ^ 2 := by
    refine summable_of_sum_le (c := ∫ z : Euc p.d × Euc p.d, c z.1 z.2 ^ 2 ∂(μ.prod μ))
      (fun _ => sq_nonneg _) fun s => ?_
    have h := s21h2_hs_bound hK hk (fun k => ((b k : s21h2_V μ) : Lp ℝ 2 μ)) hv hmem s
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [heig k, norm_smul, hv.norm_eq_one k, mul_one, Real.norm_eq_abs, sq_abs]
  have hKall : ∀ᵐ x ∂μ, ∀ k, ∫ y, c x y * e k y ∂μ = lam k * e k x := ae_all_iff.2 hKe
  have hPars : ∀ᵐ x ∂μ, HasSum (fun k => (lam k * e k x) ^ 2) (∫ y, c x y ^ 2 ∂μ) := by
    filter_upwards [s21h2_c_slice μ (k := fun a b => HRS.Whole.rieszKernel p.d p.s (a - b)) hk, hKall]
      with x hx hxK
    set F : Lp ℝ 2 μ := hx.1.toLp (fun y => c x y) with hF
    have hFa : (F : Euc p.d → ℝ) =ᵐ[μ] fun y => c x y := hx.1.coeFn_toLp
    have hFV : F ∈ s21h2_V μ := by
      rw [s21h2_mem_V, inner_one2, integral_congr_ae hFa]; exact hx.2
    have h1 : ∀ k, inner ℝ (⟨F, hFV⟩ : s21h2_V μ) (b k) = lam k * e k x := fun k => by
      show inner ℝ F ((b k : s21h2_V μ) : Lp ℝ 2 μ) = _
      rw [lp_inner, ← hxK k]
      refine integral_congr_ae ?_
      filter_upwards [hFa] with y hy
      rw [hy]
    have h2 : inner ℝ (⟨F, hFV⟩ : s21h2_V μ) ⟨F, hFV⟩ = ∫ y, c x y ^ 2 ∂μ := by
      show inner ℝ F F = _
      rw [real_inner_self_eq_norm_sq]
      exact (integral_sq_eq hFa.symm).symm
    have h := b.hasSum_inner_mul_inner (⟨F, hFV⟩ : s21h2_V μ) ⟨F, hFV⟩
    rw [h2] at h
    have e3 : (fun k => inner ℝ (⟨F, hFV⟩ : s21h2_V μ) (b k) * inner ℝ (b k) (⟨F, hFV⟩ : s21h2_V μ)) =
        fun k => (lam k * e k x) ^ 2 := by
      funext k
      rw [real_inner_comm (⟨F, hFV⟩ : s21h2_V μ) (b k), h1 k]; ring
    rw [e3] at h
    exact h
  have hSig : ∫ z : Euc p.d × Euc p.d, c z.1 z.2 ^ 2 ∂(μ.prod μ) = ∑' k, lam k ^ 2 := by
    rw [integral_prod _ hnu]
    have hF_int : ∀ k, Integrable (fun x => (lam k * e k x) ^ 2) μ := fun k => by
      have := ((hem k).integrable_sq).const_mul (lam k ^ 2)
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only [mul_pow]
    have hint_k : ∀ k, ∫ x, (lam k * e k x) ^ 2 ∂μ = lam k ^ 2 := fun k => by
      have : ∀ x, (lam k * e k x) ^ 2 = lam k ^ 2 * (e k x * e k x) := fun x => by ring
      simp_rw [this]
      rw [integral_const_mul, hon k k]; simp
    have hF_sum : Summable fun k => ∫ x, ‖(lam k * e k x) ^ 2‖ ∂μ := by
      have : ∀ k, ∫ x, ‖(lam k * e k x) ^ 2‖ ∂μ = lam k ^ 2 := fun k => by
        simp_rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hint_k k
      simp_rw [this]; exact hsum
    calc ∫ x, ∫ y, c x y ^ 2 ∂μ ∂μ = ∫ x, ∑' k, (lam k * e k x) ^ 2 ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hPars] with x hx
          exact hx.tsum_eq.symm
      _ = ∑' k, ∫ x, (lam k * e k x) ^ 2 ∂μ := (integral_tsum_of_summable_integral_norm hF_int hF_sum).symm
      _ = ∑' k, lam k ^ 2 := tsum_congr hint_k
  have hCΦ : ∀ k, ∫ z : Euc p.d × Euc p.d, c z.1 z.2 * (e k z.1 * e k z.2) ∂(μ.prod μ) = lam k := by
    intro k
    have hint := (s21g2_k11b_B_bound hcm (hem k) (hem k)).1
    rw [integral_prod _ hint]
    have h1 : ∀ᵐ x ∂μ, ∫ y, c x y * (e k x * e k y) ∂μ = lam k * (e k x * e k x) := by
      filter_upwards [hKe k] with x hx
      have : ∀ y, c x y * (e k x * e k y) = e k x * (c x y * e k y) := fun y => by ring
      simp_rw [this]; rw [integral_const_mul, hx]; ring
    simp only
    rw [integral_congr_ae h1, integral_const_mul, hon k k]; simp
  have hT : ∀ k, MemLp (fun z : Euc p.d × Euc p.d => e k z.1 * e k z.2) 2 (μ.prod μ) := fun k =>
    (s21g2_k11b_tensor_memLp (hem k) (hem k)).1
  set P : ℕ → Lp ℝ 2 (μ.prod μ) := fun k => (hT k).toLp (fun z => e k z.1 * e k z.2) with hPdef
  have hP : Orthonormal ℝ P := by
    rw [orthonormal_iff_ite]
    intro i j
    show inner ℝ ((hT i).toLp _) ((hT j).toLp _) = _
    rw [s21h2_L2_inner]
    have : ∀ z : Euc p.d × Euc p.d, (e i z.1 * e i z.2) * (e j z.1 * e j z.2) =
        (e i z.1 * e j z.1) * (e i z.2 * e j z.2) := fun z => by ring
    simp_rw [this]
    rw [integral_prod_mul (fun x => e i x * e j x) (fun y => e i y * e j y), hon i j]
    split_ifs <;> simp
  have hCP : ∀ k, inner ℝ (hcm.toLp (fun z : Euc p.d × Euc p.d => c z.1 z.2)) (P k) = lam k := by
    intro k
    show inner ℝ (hcm.toLp _) ((hT k).toLp _) = _
    rw [s21h2_L2_inner]; exact hCΦ k
  have hpy := s21h2_pyth (C := fun z : Euc p.d × Euc p.d => c z.1 z.2) hcm hP lam hCP hsum hSig
  have hG : ∀ n, MemLp (fun z : Euc p.d × Euc p.d =>
      c z.1 z.2 - ∑ j ∈ Finset.range n, lam j * e j z.1 * e j z.2) 2 (μ.prod μ) := by
    intro n
    refine hcm.sub (memLp_finsetSum _ fun j _ => ?_)
    have e1 : (fun z : Euc p.d × Euc p.d => lam j * e j z.1 * e j z.2) =
        fun z => lam j * (e j z.1 * e j z.2) := by funext z; ring
    rw [e1]; exact (hT j).const_mul (lam j)
  have h5 : ∀ᵐ z ∂(μ.prod μ), ∀ k, (P k : Euc p.d × Euc p.d → ℝ) z = e k z.1 * e k z.2 :=
    ae_all_iff.2 fun k => (hT k).coeFn_toLp
  have htoLp : ∀ n, (hG n).toLp _ = hcm.toLp (fun z : Euc p.d × Euc p.d => c z.1 z.2) -
      ∑ k ∈ Finset.range n, lam k • P k := by
    intro n
    refine Lp.ext ?_
    have h1 := (hG n).coeFn_toLp
    have h2 := Lp.coeFn_sub (hcm.toLp (fun z : Euc p.d × Euc p.d => c z.1 z.2))
      (∑ k ∈ Finset.range n, lam k • P k)
    have h3 := hcm.coeFn_toLp
    have h4 := s21h2_coeFn_finsum lam P (Finset.range n)
    filter_upwards [h1, h2, h3, h4, h5] with z hz1 hz2 hz3 hz4 hz5
    rw [hz1, hz2, Pi.sub_apply, hz3, hz4]
    simp only [hz5]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlim : Tendsto (fun n => eLpNorm (fun z : Euc p.d × Euc p.d =>
      c z.1 z.2 - ∑ j ∈ Finset.range n, lam j * e j z.1 * e j z.2) 2 (μ.prod μ)) atTop (𝓝 0) := by
    have hE : ∀ n, eLpNorm (fun z : Euc p.d × Euc p.d =>
        c z.1 z.2 - ∑ j ∈ Finset.range n, lam j * e j z.1 * e j z.2) 2 (μ.prod μ) =
        ENNReal.ofReal ‖hcm.toLp (fun z : Euc p.d × Euc p.d => c z.1 z.2) -
          ∑ k ∈ Finset.range n, lam k • P k‖ := fun n => by
      rw [ofReal_norm, ← htoLp n, Lp.enorm_toLp]
    simp_rw [hE]
    simpa using ENNReal.tendsto_ofReal hpy
  refine ⟨lam, e, fun j => ⟨hlam j, hem j, hmean j⟩, hon, hsum, hlim, ?_⟩
  intro f hf hfe
  set F : Lp ℝ 2 μ := hf.1.toLp f with hF
  have hFa : (F : Euc p.d → ℝ) =ᵐ[μ] f := hf.1.coeFn_toLp
  have hFV : F ∈ s21h2_V μ := by
    rw [s21h2_mem_V, inner_one2, integral_congr_ae hFa]; exact hf.2
  have h0 : b.repr ⟨F, hFV⟩ = 0 := by
    refine lp.ext (funext fun j => ?_)
    rw [HilbertBasis.repr_apply_apply]
    show inner ℝ ((b j : s21h2_V μ) : Lp ℝ 2 μ) F = 0
    rw [lp_inner]
    refine Eq.trans (integral_congr_ae ?_) (hfe j)
    filter_upwards [hFa] with x hx
    rw [hx]; ring
  have hW : (⟨F, hFV⟩ : s21h2_V μ) = 0 := b.repr.injective (by rw [h0, map_zero])
  have hF0 : F = 0 := congrArg Subtype.val hW
  filter_upwards [hFa, Lp.coeFn_zero ℝ 2 μ] with x hx1 hx2
  rw [← hx1, hF0, hx2]

end HRS.MS.R26T3
