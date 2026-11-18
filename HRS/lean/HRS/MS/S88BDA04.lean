import HRS.MS.S88BDA03

/-!
# S8.8.A04: complete bounded synthesis and exact dual-coefficient reconstruction

`s88_synthesis_reconstruction`: from the finite synthesis bound `‖∑ r_i e_i‖² ≤ K ∑ r_i²` there is a bounded
synthesis operator `S : ℓ² → L²(μ)`, `‖S‖ ≤ √K`, with `β⟨S z, R e_l⟩ = z_l`; every centered `f ∈ L²(μ)` is
reconstructed a.e. as `S z` from its dual coefficients `z_l = β⟨f, R e_l⟩` (Bessel + spectral completeness).

Construction: `A f = (⟨e_l, f⟩)_l : L² → ℓ²` is bounded by `√K` (this is the finite bound, dualized); `S = A†`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators InnerProductSpace

namespace HRS.MS.S88Breakdown

open HRS HRS.Whole

lemma s88_seq_ext (z z' : SeqL2) (h : ∀ l, SeqL2.coord z l = SeqL2.coord z' l) : z = z' :=
  lp.ext (funext h)

lemma s88_inner_seq (z w : SeqL2) :
    inner ℝ z w = ∑' l, SeqL2.coord z l * SeqL2.coord w l := by
  have := lp.inner_eq_tsum (𝕜 := ℝ) (G := fun _ : ℕ => ℝ) (show lp (fun _ : ℕ => ℝ) 2 from z) (show lp (fun _ : ℕ => ℝ) 2 from w)
  refine this.trans (tsum_congr fun l => ?_)
  simp [SeqL2.coord, mul_comm]

section Core

variable {d : ℕ} {ρ : Euc d → ℝ} {M s : ℝ}
variable [IsProbabilityMeasure (HRS.Whole.withDensityReal ρ)]

theorem s88_synth_core (h : Q34.Q34Hyp d s ρ M) {β : ℝ} (hβ : 0 < β) (e : ℕ → Euc d → ℝ)
    (he : ∀ l, MemL2Zero (HRS.Whole.withDensityReal ρ) (e l))
    (horth : ∀ l j, β * HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ) (e l)
      (HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (e j)) =
        if l = j then 1 else 0)
    (hcomp : ∀ f : Euc d → ℝ, MemL2Zero (HRS.Whole.withDensityReal ρ) f →
      (∀ l, HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ) f
        (HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (e l)) = 0) →
      f =ᵐ[HRS.Whole.withDensityReal ρ] 0)
    (K : ℝ) (hK : 0 ≤ K)
    (hfinite : ∀ (p : ℕ) (r : Fin p → ℝ),
      (∫ x, (∑ i : Fin p, r i * e (i : ℕ) x) ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ≤
        K * ∑ i : Fin p, (r i) ^ 2) :
    ∃ S : SeqL2 →L[ℝ] Lp ℝ 2 (HRS.Whole.withDensityReal ρ), ‖S‖ ≤ Real.sqrt K ∧
      (∀ z : SeqL2, MemL2Zero (HRS.Whole.withDensityReal ρ) (fun x => S z x)) ∧
      (∀ (z : SeqL2) (l : ℕ),
        β * HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ) (fun x => S z x)
          (HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (e l)) =
            SeqL2.coord z l) ∧
      ∀ f : Euc d → ℝ, MemL2Zero (HRS.Whole.withDensityReal ρ) f →
        ∃ z : SeqL2,
          (∀ l : ℕ, SeqL2.coord z l =
            β * HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ) f
              (HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (e l))) ∧
          ‖z‖ ^ 2 ≤ β * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ) ∧
          (fun x => S z x) =ᵐ[HRS.Whole.withDensityReal ρ] f := by
  set ν := HRS.Whole.withDensityReal ρ with hν
  have hRm : ∀ ψ, MemL2Zero ν ψ →
      MemL2Zero ν (HRS.Whole.responseInverse (rieszKernel d s) ν β ψ) :=
    fun ψ hψ => (u11_resp_isResponse h hβ hψ).1
  set Y : ℕ → Lp ℝ 2 ν := fun l => (hRm _ (he l)).1.toLp
    (HRS.Whole.responseInverse (rieszKernel d s) ν β (e l)) with hYdef
  set E : ℕ → Lp ℝ 2 ν := fun l => (he l).1.toLp (e l) with hEdef
  have hYae : ∀ l, HRS.Whole.responseInverse (rieszKernel d s) ν β (e l) =ᵐ[ν] (Y l : Euc d → ℝ) :=
    fun l => (MemLp.coeFn_toLp (hRm _ (he l)).1).symm
  have hEae : ∀ l, e l =ᵐ[ν] (E l : Euc d → ℝ) := fun l => (MemLp.coeFn_toLp (he l).1).symm
  have hinE : ∀ l j, inner ℝ (E l) (Y j) =
      HRS.Whole.l2Inner ν (e l) (HRS.Whole.responseInverse (rieszKernel d s) ν β (e j)) :=
    fun l j => (Q34.l2Inner_eq (hEae l) (hYae j)).symm
  have hbio : ∀ l j, β * inner ℝ (E l) (Y j) = if l = j then 1 else 0 := by
    intro l j; rw [hinE, horth]
  -- step 1: norm of a finite synthesis
  have hnormsq : ∀ (p : ℕ) (r : Fin p → ℝ),
      ‖∑ i : Fin p, r i • E (i : ℕ)‖ ^ 2 = ∫ x, (∑ i : Fin p, r i * e (i : ℕ) x) ^ 2 ∂ν := by
    intro p r
    have hae : (fun x => ∑ i : Fin p, r i * e (i : ℕ) x) =ᵐ[ν]
        ((∑ i : Fin p, r i • E (i : ℕ) : Lp ℝ 2 ν) : Euc d → ℝ) := by
      have h1 := s88_ae_sum (ν := ν) (Finset.univ : Finset (Fin p)) (fun i => E (i : ℕ)) r
      have h2 : ∀ᵐ x ∂ν, ∀ i : Fin p, (E (i : ℕ) : Euc d → ℝ) x = e (i : ℕ) x :=
        ae_all_iff.2 fun i => MemLp.coeFn_toLp (he (i : ℕ)).1
      filter_upwards [h1, h2] with x hx1 hx2
      rw [hx1]
      exact Finset.sum_congr rfl fun i _ => by rw [hx2 i]
    exact (Q34.integral_sq_eq hae).symm
  -- step 2: the dualized finite bound
  have hbessel : ∀ (f : Lp ℝ 2 ν) (n : ℕ),
      ∑ l ∈ Finset.range n, (inner ℝ (E l) f) ^ 2 ≤ K * ‖f‖ ^ 2 := by
    intro f n
    rw [Finset.sum_range]
    set r : Fin n → ℝ := fun i => inner ℝ (E (i : ℕ)) f with hr
    set Fs : Lp ℝ 2 ν := ∑ i : Fin n, r i • E (i : ℕ) with hFs
    set t : ℝ := ∑ i : Fin n, (inner ℝ (E (i : ℕ)) f) ^ 2 with ht
    have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => sq_nonneg _
    have h1 : t = inner ℝ Fs f := by
      rw [hFs, sum_inner, ht]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_left, hr]
      ring
    have h2 : ‖Fs‖ ^ 2 ≤ K * t := by
      rw [hFs, hnormsq n r]
      have := hfinite n r
      simpa [hr, ht] using this
    have h3 : t ≤ ‖Fs‖ * ‖f‖ := by
      rw [h1]; exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)
    have h4 : t ^ 2 ≤ K * t * ‖f‖ ^ 2 := by
      calc t ^ 2 ≤ (‖Fs‖ * ‖f‖) ^ 2 := pow_le_pow_left₀ ht0 h3 2
        _ = ‖Fs‖ ^ 2 * ‖f‖ ^ 2 := by ring
        _ ≤ K * t * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    rcases ht0.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · have : t * t ≤ t * (K * ‖f‖ ^ 2) := by nlinarith
      exact le_of_mul_le_mul_left this hpos
  have hmem : ∀ f : Lp ℝ 2 ν, Memℓp (fun l => inner ℝ (E l) f) 2 := by
    intro f
    refine memℓp_two_iff.2 (summable_of_sum_range_le (fun l => sq_nonneg _) (hbessel f))
  have hnorm_ofSeq : ∀ f : Lp ℝ 2 ν,
      ‖SeqL2.ofSeq (fun l => inner ℝ (E l) f)‖ ≤ Real.sqrt K * ‖f‖ := by
    intro f
    have hsq : ‖SeqL2.ofSeq (fun l => inner ℝ (E l) f)‖ ^ 2 ≤ K * ‖f‖ ^ 2 := by
      have e1 : ∑' l, SeqL2.coord (SeqL2.ofSeq (fun l => inner ℝ (E l) f)) l ^ 2 =
          ∑' l, (inner ℝ (E l) f) ^ 2 :=
        tsum_congr fun l => by rw [u11_coord_ofSeq (hmem f) l]
      rw [← u11_norm_sq, e1]
      exact Real.tsum_le_of_sum_range_le (fun l => sq_nonneg _) (hbessel f)
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, Real.sq_sqrt hK]
    exact hsq
  -- step 3: the analysis operator `A : L² → ℓ²` and its adjoint `S`
  let A0 : Lp ℝ 2 ν →ₗ[ℝ] SeqL2 :=
    { toFun := fun f => SeqL2.ofSeq (fun l => inner ℝ (E l) f)
      map_add' := fun f g => by
        refine s88_seq_ext _ _ fun l => ?_
        change SeqL2.coord _ l = SeqL2.coord _ l + SeqL2.coord _ l
        rw [u11_coord_ofSeq (hmem (f + g)) l, u11_coord_ofSeq (hmem f) l,
          u11_coord_ofSeq (hmem g) l, inner_add_right]
      map_smul' := fun c f => by
        refine s88_seq_ext _ _ fun l => ?_
        change SeqL2.coord _ l = c * SeqL2.coord _ l
        rw [u11_coord_ofSeq (hmem (c • f)) l, u11_coord_ofSeq (hmem f) l, real_inner_smul_right] }
  let A : Lp ℝ 2 ν →L[ℝ] SeqL2 := A0.mkContinuous (Real.sqrt K) (fun f => hnorm_ofSeq f)
  have hA : ∀ f l, SeqL2.coord (A f) l = inner ℝ (E l) f := fun f l =>
    u11_coord_ofSeq (hmem f) l
  have hAnorm : ‖A‖ ≤ Real.sqrt K := LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _
  set S : SeqL2 →L[ℝ] Lp ℝ 2 ν := ContinuousLinearMap.adjoint A with hSdef
  have hSnorm : ‖S‖ ≤ Real.sqrt K := by
    rw [hSdef, LinearIsometryEquiv.norm_map]; exact hAnorm
  have hSA : ∀ (z : SeqL2) (f : Lp ℝ 2 ν),
      inner ℝ (S z) f = ∑' l, SeqL2.coord z l * inner ℝ (E l) f := by
    intro z f
    rw [hSdef, ContinuousLinearMap.adjoint_inner_left, s88_inner_seq]
    exact tsum_congr fun l => by rw [hA]
  have hYS : ∀ (z : SeqL2) (l : ℕ), β * inner ℝ (S z) (Y l) = SeqL2.coord z l := by
    intro z l
    rw [← real_inner_smul_right, hSA]
    rw [tsum_eq_single l]
    · rw [real_inner_smul_right, hbio l l]
      simp
    · intro j hj
      rw [real_inner_smul_right, hbio j l]
      simp [hj]
  have hcent : ∀ z : SeqL2, MemL2Zero ν (fun x => S z x) := by
    intro z
    refine ⟨Lp.memLp (S z), ?_⟩
    have h1 : ∫ x, (S z) x ∂ν = inner ℝ (Q34.one2 ν) (S z) := (Q34.inner_one2 (S z)).symm
    rw [h1, real_inner_comm, hSA]
    refine (tsum_congr fun l => ?_).trans tsum_zero
    have : inner ℝ (E l) (Q34.one2 ν) = 0 := by
      rw [real_inner_comm, Q34.inner_one2]
      exact (integral_congr_ae (MemLp.coeFn_toLp (he l).1)).trans (he l).2
    rw [this, mul_zero]
  have hSY : ∀ (z : SeqL2) (l : ℕ), β * HRS.Whole.l2Inner ν (fun x => S z x)
      (HRS.Whole.responseInverse (rieszKernel d s) ν β (e l)) = SeqL2.coord z l := by
    intro z l
    rw [Q34.l2Inner_eq (Filter.EventuallyEq.refl _ _) (hYae l), hYS]
  refine ⟨S, hSnorm, hcent, hSY, fun f hf => ?_⟩
  -- step 4: reconstruction of a centered function
  set F : Lp ℝ 2 ν := hf.1.toLp f with hF
  have hFae : f =ᵐ[ν] (F : Euc d → ℝ) := (MemLp.coeFn_toLp hf.1).symm
  set zc : ℕ → ℝ := fun l => β * HRS.Whole.l2Inner ν f
    (HRS.Whole.responseInverse (rieszKernel d s) ν β (e l)) with hzc
  have hbes : ∀ T : Finset ℕ, ∑ l ∈ T, zc l ^ 2 ≤ β * ∫ x, f x ^ 2 ∂ν :=
    fun T => u11_bessel_model h hβ e he horth hf T
  have hzmem : Memℓp zc 2 :=
    memℓp_two_iff.2 (summable_of_sum_le (fun l => sq_nonneg _) hbes)
  have hcoord : ∀ l, SeqL2.coord (SeqL2.ofSeq zc) l = zc l := fun l => u11_coord_ofSeq hzmem l
  refine ⟨SeqL2.ofSeq zc, hcoord, ?_, ?_⟩
  · have e1 : ∑' l, SeqL2.coord (SeqL2.ofSeq zc) l ^ 2 = ∑' l, zc l ^ 2 :=
      tsum_congr fun l => by rw [hcoord]
    rw [← u11_norm_sq, e1]
    exact Real.tsum_le_of_sum_le (fun l => sq_nonneg _) hbes
  · set z := SeqL2.ofSeq zc with hz
    have hSzae : ∀ᵐ x ∂ν, (S z) x = (S z) x := Filter.Eventually.of_forall fun _ => rfl
    have hg0 : MemL2Zero ν (fun x => f x - S z x) := by
      refine ⟨hf.1.sub (Lp.memLp (S z)), ?_⟩
      rw [integral_sub (hf.1.integrable one_le_two) ((Lp.memLp (S z)).integrable one_le_two),
        hf.2, (hcent z).2]
      simp
    have hgae : (fun x => f x - S z x) =ᵐ[ν] ((F - S z : Lp ℝ 2 ν) : Euc d → ℝ) := by
      filter_upwards [hFae, Lp.coeFn_sub F (S z)] with x h1 h2
      rw [h2, Pi.sub_apply, h1]
    have hcz : ∀ l, HRS.Whole.l2Inner ν (fun x => f x - S z x)
        (HRS.Whole.responseInverse (rieszKernel d s) ν β (e l)) = 0 := by
      intro l
      rw [Q34.l2Inner_eq hgae (hYae l), inner_sub_left]
      have h1 : β * inner ℝ F (Y l) = zc l := by
        rw [hzc]; simp only; rw [Q34.l2Inner_eq hFae (hYae l)]
      have h2 := hYS z l
      rw [hcoord] at h2
      have : β * (inner ℝ F (Y l) - inner ℝ (S z) (Y l)) = 0 := by rw [mul_sub, h1, h2]; ring
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 hβ.ne'
      · exact h0
    have hzero := hcomp _ hg0 hcz
    filter_upwards [hzero] with x hx
    have : f x - S z x = 0 := hx
    linarith

end Core

theorem s88_synthesis_reconstruction {d : ℕ} (hd : 2 ≤ d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (ρ : Euc d → ℝ)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ)
    (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ) (hdata : IsSpectralData d β ρ e om)
    (K : ℝ) (hK : 0 ≤ K)
    (hfinite : ∀ (p : ℕ) (r : Fin p → ℝ),
      (∫ x, (∑ i : Fin p, r i * e (i : ℕ) x) ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ≤
        K * ∑ i : Fin p, (r i) ^ 2) :
    ∃ S : SeqL2 →L[ℝ] Lp ℝ 2 (HRS.Whole.withDensityReal ρ), ‖S‖ ≤ Real.sqrt K ∧
      (∀ z : SeqL2, MemL2Zero (HRS.Whole.withDensityReal ρ) (fun x => S z x)) ∧
      (∀ (z : SeqL2) (l : ℕ),
        β * HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ) (fun x => S z x)
          (HRS.Whole.responseInverse (rieszKernel d ((d : ℝ) / 2)) (HRS.Whole.withDensityReal ρ) β
            (e l)) = SeqL2.coord z l) ∧
      ∀ f : Euc d → ℝ, MemL2Zero (HRS.Whole.withDensityReal ρ) f →
        ∃ z : SeqL2,
          (∀ l : ℕ, SeqL2.coord z l =
            β * HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ) f
              (HRS.Whole.responseInverse (rieszKernel d ((d : ℝ) / 2))
                (HRS.Whole.withDensityReal ρ) β (e l))) ∧
          ‖z‖ ^ 2 ≤ β * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ) ∧
          (fun x => S z x) =ᵐ[HRS.Whole.withDensityReal ρ] f := by
  have hprob : HRS.Whole.IsProbDensity ρ := hρ.1.1
  obtain ⟨M, hM⟩ := u11_rho_le hd ha hβ hρ
  have := Q34.isProbabilityMeasure_nu hprob
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hQ : Q34.Q34Hyp d ((d : ℝ) / 2) ρ M :=
    ⟨by omega, by positivity, by linarith, hprob, hM⟩
  exact s88_synth_core hQ hβ e hdata.centered hdata.orth hdata.complete K hK hfinite

end HRS.MS.S88Breakdown
