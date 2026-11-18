import HRS.MS.S81w2Susc

/-!
# S8.1 (worker S81W2): the synthesis operator of a spectral datum as a Hilbert sum

`s81w2_synth`: for any `IsSpectralData` `(e_l, ω_l)` of the critical thermal reference there is a bounded linear map
`S : ℓ² → L²(μ)` with `S z = Σ_l z_l e_l` (an `L²(μ)`-convergent series, `HasSum`), centered values, and
`S z_f = P_μ f` for the dual coefficients `z_f(l) = β⟨P_μ f, R e_l⟩` of every centered class (S8.8 A04, with `S e_l = e_l`).
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators InnerProductSpace

namespace HRS.Whole.S81W2

open HRS HRS.Whole HRS.Whole.Q34 HRS.MS.S111X2 HRS.MS.S88Breakdown

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem s81w2_synth (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) {e : ℕ → Euc d → ℝ} {om : ℕ → ℝ}
    (hdata : IsSpectralData d β ρ e om) :
    ∃ S : SeqL2 →L[ℝ] Lp ℝ 2 (withDensityReal ρ),
      (∀ z : SeqL2, HasSum (fun l => SeqL2.coord z l • (((hdata.centered l).1).toLp (e l) :
          Lp ℝ 2 (withDensityReal ρ))) (S z)) ∧
      (∀ z : SeqL2, MemL2Zero (withDensityReal ρ) (fun x => (S z : Lp ℝ 2 (withDensityReal ρ)) x)) ∧
      ∀ f : Euc d → ℝ, MemL2Zero (withDensityReal ρ) f →
        ∃ z : SeqL2, (∀ l, SeqL2.coord z l = s81w2_coef d β ρ e f l) ∧
          (fun x => (S z : Lp ℝ 2 (withDensityReal ρ)) x) =ᵐ[withDensityReal ρ] f := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hprobρ : IsProbDensity ρ := hρ.1.1
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProbabilityMeasure_nu hprobρ
  set μ := withDensityReal ρ with hμ
  obtain ⟨M₀, c, S0, hc, hTc⟩ := HRS.MS.TransOp.s611_tcref_of_thermal hd hs0 hsd ha hβ hρ
  obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref (by omega) hs0 hsd hc hTc
  have hθ : 0 ≤ β := hβ.le
  obtain ⟨Kf, hKf, hfin⟩ := s88_finite_synthesis_bound hd a β ha hβ ρ hρ e om hdata
  obtain ⟨S, -, hSz, hSc, hSrec⟩ := s88_synthesis_reconstruction hd a β ha hβ ρ hρ e om hdata Kf hKf hfin
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
  refine ⟨S, ?_, hSz, fun f hf => ?_⟩
  · intro z
    let zl : lp (fun _ : ℕ => ℝ) 2 := z
    let S' : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] Lp ℝ 2 μ := S
    have hz : HasSum (fun l => lp.single (E := fun _ : ℕ => ℝ) 2 l (zl l)) zl :=
      lp.hasSum_single (by simp) zl
    have h1 := hz.mapL (S : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] Lp ℝ 2 μ)
    have hel : ∀ l, (((hdata.centered l).1).toLp (e l) : Lp ℝ 2 μ) = s111x2_cl (hee l) := fun l =>
      Lp.ext ((MemLp.coeFn_toLp (hee l)).trans (hcl l).symm)
    have hfun : (fun l => SeqL2.coord z l • (((hdata.centered l).1).toLp (e l) : Lp ℝ 2 μ)) =
        fun l => (S : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] Lp ℝ 2 μ)
          (lp.single (E := fun _ : ℕ => ℝ) 2 l (zl l)) := by
      funext l
      have e1 : lp.single (E := fun _ : ℕ => ℝ) 2 l (zl l) =
          zl l • lp.single (E := fun _ : ℕ => ℝ) 2 l (1 : ℝ) := by
        rw [← lp.single_smul]; simp
      rw [e1]
      show _ = S' (zl l • lp.single (E := fun _ : ℕ => ℝ) 2 l (1 : ℝ))
      rw [S'.map_smul]
      have := hSeq l
      show _ = zl l • S (lp.single (E := fun _ : ℕ => ℝ) 2 l (1 : ℝ))
      rw [this, hel l]
      rfl
    rw [hfun]
    exact h1
  · obtain ⟨z, hz1, -, hz3⟩ := hSrec f hf
    have hpm : projMean μ f = f := by
      funext x
      show f x - ∫ y, f y ∂μ = f x
      rw [hf.2]; ring
    exact ⟨z, fun l => by rw [hz1 l]; unfold s81w2_coef; rw [show projMean (withDensityReal ρ) f = f from hpm], hz3⟩

end HRS.Whole.S81W2
