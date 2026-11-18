import HRS.MS.S88BDA04
import HRS.MS.S111X2Aux5
import HRS.MS.S81w2Gram

/-!
# S8.1 (worker S81W2): the spectral form of the susceptibility covariance

For the critical thermal reference `μ = ρ dx` and any `IsSpectralData` `(e_l, ω_l)` (S8.7), with
`z_f(l) = β ⟨P_μ f, R e_l⟩` the dual coefficients of the centered part of `f ∈ L²(μ)`:

`s81w2_susc_spectral : C_{β,μ}(f, g) = β⁻¹ Σ_l z_f(l) z_g(l)`  (the series is summable).

Route: the bounded synthesis `S` of S8.8 A04 (`S z = Σ z_l e_l`, `β⟨S z, R e_l⟩ = z_l`, `S z_f = P_μ f`), the resolvent
`B = (I+βK)⁻¹` (S111X2 `KRep`), `S e_l = e_l` by spectral completeness, `⟨e_k, B e_l⟩ = β⁻¹ δ_{kl}` (`orth`), and the abstract
Gram identity `s81w2_gram`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators InnerProductSpace

namespace HRS.Whole.S81W2

open HRS HRS.Whole HRS.Whole.Q34 HRS.MS.S111X2 HRS.MS.S88Breakdown

variable {d : ℕ}

/-- The dual coefficient `z_f(l) = β ⟨P_μ f, R e_l⟩` of the centered part of `f`. -/
def s81w2_coef (d : ℕ) (β : ℝ) (ρ : Euc d → ℝ) (e : ℕ → Euc d → ℝ) (f : Euc d → ℝ) (l : ℕ) : ℝ :=
  β * l2Inner (withDensityReal ρ) (projMean (withDensityReal ρ) f)
    (responseInverse (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρ) β (e l))

set_option maxHeartbeats 1600000 in
theorem s81w2_susc_spectral (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) {e : ℕ → Euc d → ℝ} {om : ℕ → ℝ}
    (hdata : IsSpectralData d β ρ e om) {f g : Euc d → ℝ}
    (hf : MemLp f 2 (withDensityReal ρ)) (hg : MemLp g 2 (withDensityReal ρ)) :
    Summable (fun l => s81w2_coef d β ρ e f l * s81w2_coef d β ρ e g l) ∧
      susceptibilityCov (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρ) β f g =
        β⁻¹ * ∑' l, s81w2_coef d β ρ e f l * s81w2_coef d β ρ e g l := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hprobρ : IsProbDensity ρ := hρ.1.1
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProbabilityMeasure_nu hprobρ
  set μ := withDensityReal ρ with hμ
  -- the operator `K`
  obtain ⟨M₀, c, S0, hc, hTc⟩ := HRS.MS.TransOp.s611_tcref_of_thermal hd hs0 hsd ha hβ hρ
  obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref (by omega) hs0 hsd hc hTc
  have hθ : 0 ≤ β := hβ.le
  -- the synthesis operator
  obtain ⟨Kf, hKf, hfin⟩ := s88_finite_synthesis_bound hd a β ha hβ ρ hρ e om hdata
  obtain ⟨S, -, hSz, hSc, hSrec⟩ := s88_synthesis_reconstruction hd a β ha hβ ρ hρ e om hdata Kf hKf hfin
  -- the resolvent as a continuous linear map
  let B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    LinearMap.mkContinuous
      { toFun := s111x2_Res hK.posOp hθ
        map_add' := s111x2_Res_add hK.posOp hθ
        map_smul' := fun c x => s111x2_Res_smul hK.posOp hθ c x } 1
      (fun x => by simpa using (s111x2_Res_bounds hK.posOp hθ x).2.2)
  have hBapp : ∀ x, B x = s111x2_Res hK.posOp hθ x := fun x => rfl
  have hee : ∀ l, MemLp (e l) 2 μ := fun l => (hdata.centered l).1
  have hePc : ∀ l, projMean μ (e l) = e l := by
    intro l; funext x
    show e l x - ∫ y, e l y ∂μ = e l x
    rw [(hdata.centered l).2]; ring
  have hcl : ∀ l, ((s111x2_cl (hee l) : Lp ℝ 2 μ) : Euc d → ℝ) =ᵐ[μ] e l := by
    intro l
    have := s111x2_cl_ae (hee l)
    rw [hePc] at this
    exact this.symm
  have hRI : ∀ k, responseInverse (rieszKernel d ((d : ℝ) / 2)) μ β (e k) =ᵐ[μ]
      ((s111x2_Res hK.posOp hθ (s111x2_cl (hee k)) : Lp ℝ 2 μ) : Euc d → ℝ) :=
    fun k => s111x2_responseInverse_ae hK hθ (hee k)
  have hcoordsingle : ∀ l k : ℕ, SeqL2.coord (lp.single (E := fun _ : ℕ => ℝ) 2 l (1 : ℝ)) k =
      if l = k then 1 else 0 := by
    intro l k
    simp only [SeqL2.coord, lp.single_apply, Pi.single_apply]
    by_cases h : k = l
    · subst h; simp
    · simp [h, Ne.symm h]
  -- `⟨e_l, R e_k⟩ = β⁻¹ δ`
  have horth : ∀ l k, l2Inner μ (e l) (responseInverse (rieszKernel d ((d : ℝ) / 2)) μ β (e k)) =
      β⁻¹ * (if l = k then 1 else 0) := by
    intro l k
    have := hdata.orth l k
    field_simp
    linarith
  -- `S e_l = e_l`
  have hSe : ∀ l, ((S (lp.single (E := fun _ : ℕ => ℝ) 2 l (1 : ℝ)) : Lp ℝ 2 μ) : Euc d → ℝ) =ᵐ[μ] e l := by
    intro l
    set Sl := S (lp.single (E := fun _ : ℕ => ℝ) 2 l (1 : ℝ)) with hSl
    have hD : ((Sl - s111x2_cl (hee l) : Lp ℝ 2 μ) : Euc d → ℝ) =ᵐ[μ] 0 := by
      refine hdata.complete _ ⟨Lp.memLp _, ?_⟩ ?_
      · have h1 := (hSz (lp.single (E := fun _ : ℕ => ℝ) 2 l (1 : ℝ))).2
        have h2 := (hSz (lp.single (E := fun _ : ℕ => ℝ) 2 l (1 : ℝ))).1
        have h3 : ∫ x, ((s111x2_cl (hee l) : Lp ℝ 2 μ) : Euc d → ℝ) x ∂μ = 0 := by
          rw [integral_congr_ae (hcl l)]; exact (hdata.centered l).2
        have e1 : ∫ x, ((Sl - s111x2_cl (hee l) : Lp ℝ 2 μ) : Euc d → ℝ) x ∂μ =
            ∫ x, ((Sl : Lp ℝ 2 μ) : Euc d → ℝ) x ∂μ -
              ∫ x, ((s111x2_cl (hee l) : Lp ℝ 2 μ) : Euc d → ℝ) x ∂μ := by
          rw [integral_congr_ae (Lp.coeFn_sub Sl (s111x2_cl (hee l)))]
          exact integral_sub (h2.integrable (by norm_num)) ((Lp.memLp _).integrable (by norm_num))
        rw [e1, h3]; simpa using h1
      · intro k
        rw [l2Inner_eq (Filter.EventuallyEq.refl _ _) (hRI k)]
        rw [inner_sub_left]
        have e1 : inner ℝ Sl (s111x2_Res hK.posOp hθ (s111x2_cl (hee k))) = β⁻¹ * (if l = k then 1 else 0) := by
          rw [← l2Inner_eq (Filter.EventuallyEq.refl _ _) (hRI k)]
          have := hSc (lp.single (E := fun _ : ℕ => ℝ) 2 l (1 : ℝ)) k
          rw [hcoordsingle] at this
          field_simp
          linarith
        have e2 : inner ℝ (s111x2_cl (hee l)) (s111x2_Res hK.posOp hθ (s111x2_cl (hee k))) =
            β⁻¹ * (if l = k then 1 else 0) := by
          rw [← l2Inner_eq (hcl l).symm (hRI k)]
          exact horth l k
        rw [e1, e2]; ring
    have h1 : ((Sl : Lp ℝ 2 μ) : Euc d → ℝ) =ᵐ[μ] ((s111x2_cl (hee l) : Lp ℝ 2 μ) : Euc d → ℝ) := by
      filter_upwards [Lp.coeFn_sub Sl (s111x2_cl (hee l)), hD] with x h1 h2
      rw [h1, Pi.sub_apply] at h2
      exact sub_eq_zero.1 h2
    exact h1.trans (hcl l)
  have hSeq : ∀ l, S (lp.single (E := fun _ : ℕ => ℝ) 2 l (1 : ℝ)) = s111x2_cl (hee l) := by
    intro l
    refine Lp.ext ?_
    exact (hSe l).trans (hcl l).symm
  have hB : ∀ k l : ℕ, inner ℝ (S (lp.single (E := fun _ : ℕ => ℝ) 2 k (1 : ℝ)))
      (B (S (lp.single (E := fun _ : ℕ => ℝ) 2 l (1 : ℝ)))) = if k = l then β⁻¹ else 0 := by
    intro k l
    rw [hSeq k, hSeq l, hBapp, ← s111x2_susc_eq hK hθ (hee k) (hee l)]
    unfold susceptibilityCov
    rw [hePc, horth]
    split_ifs <;> simp
  -- the coefficient vectors
  have hz : ∀ {h : Euc d → ℝ} (hh : MemLp h 2 μ), ∃ z : SeqL2,
      (∀ l, SeqL2.coord z l = s81w2_coef d β ρ e h l) ∧
        s111x2_cl hh = S z := by
    intro h hh
    obtain ⟨z, hz1, -, hz3⟩ := hSrec (projMean μ h) (s111x2_memL2Zero_projMean hh)
    refine ⟨z, fun l => hz1 l, ?_⟩
    refine Lp.ext ?_
    exact (s111x2_cl_ae hh).symm.trans hz3.symm
  obtain ⟨zf, hzf, hclf⟩ := hz hf
  obtain ⟨zg, hzg, hclg⟩ := hz hg
  have hgram := s81w2_gram (S : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] Lp ℝ 2 μ) B β⁻¹ hB
    (zf : lp (fun _ : ℕ => ℝ) 2) (zg : lp (fun _ : ℕ => ℝ) 2)
  have hsum : HasSum (fun l => s81w2_coef d β ρ e f l * s81w2_coef d β ρ e g l)
      (inner ℝ (zf : lp (fun _ : ℕ => ℝ) 2) (zg : lp (fun _ : ℕ => ℝ) 2)) := by
    have := lp.hasSum_inner (𝕜 := ℝ) (zf : lp (fun _ : ℕ => ℝ) 2) (zg : lp (fun _ : ℕ => ℝ) 2)
    have hfun : (fun l => s81w2_coef d β ρ e f l * s81w2_coef d β ρ e g l) =
        fun i => inner ℝ (SeqL2.coord zf i) (SeqL2.coord zg i) := by
      funext l
      have h1 := hzf l
      have h2 := hzg l
      rw [← h1, ← h2]
      simp [mul_comm]
    rw [hfun]
    exact this
  refine ⟨hsum.summable, ?_⟩
  rw [hsum.tsum_eq, s111x2_susc_eq hK hθ hf hg, hclf, hclg, ← hBapp]
  exact hgram

end HRS.Whole.S81W2
