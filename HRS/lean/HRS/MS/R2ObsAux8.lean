import HRS.MS.R2ObsAux7

/-!
# S9.10 path row, packet 8: the path objects are images under `J`

Worker S910, namespace `HRS.MS.R2Obs`.  With the features `ψ_n = c f_{σ n}`, `c = c_J`:

* `s910_ell_path`: the coordinate `(t,α)` of `J (ℓ_x^H)` is `a_{U^{0,t}φ_α}(x)`, i.e. `J ℓ_x^H` is the path `ℓ_x^0`;
* `s910_field_path`: the coordinate `(t,α)` of `J (W_N^H)` is `√N(μ_N - Eμ_N)(U^{0,t}φ_α)`, i.e. `J W_N^H` is the initial path.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

noncomputable section

namespace HRS.MS.R2Obs

open S99 S45 HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s910_hsum_fiber {f : ℕ × MultiIndex d → Euc d → ℝ} (hsum : Summable fun q => cbNorm (J1 d) (f q))
    (α : MultiIndex d) : Summable fun n : ℕ => cbNorm (J1 d) (f (n, α)) :=
  hsum.comp_injective (i := fun n : ℕ => ((n, α) : ℕ × MultiIndex d)) (fun a b hab => by simpa using hab)

section Paths

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a) (hβ : 0 < β)
  (hγ : 0 < γ) {T : ℝ} (hT : 0 < T) {f : ℕ × MultiIndex d → Euc d → ℝ}
  (hf : ∀ q, MemCb (J1 d) (f q)) (hsum : Summable fun q => cbNorm (J1 d) (f q))
  {U : MultiIndex d → ℝ → Euc d → ℝ}
  (hU : ∀ (α : MultiIndex d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T → ∀ x : Euc d,
    HasSum (fun n => s11p_kap n * r2CosBasis T n t * f (n, α) x) (U α t x))
  (σ : ℕ ≃ ℕ × MultiIndex d) (M : ℝ)

include hd hs0 hs ha hβ hγ hT hf hsum hU

theorem s910_ell_path (E : Env d s a β γ (fun n x => s11p_cJ T * f (σ n) x)) (x : Euc d)
    (t : Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    OscDual.coord (OscPath.at' (s11p_J hT M (r2EllH (s11p_basis σ) (fun n x => s11p_cJ T * f (σ n) x)
      (rieszKernel d s) (thermalMeasure d s a β) γ x)) t) α = aRep d s a β γ (U α t) x := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  rw [s910_J_coord_series hT M _ (fun q => aRep d s a β γ (f q) x)
    (fun q => s910_ell_coord hd hs0 hs ha hβ hγ hf σ E x q) t α]
  have h := (s910_resp_series hd hs0 hsd ha hβ hγ (f := fun n => f (n, α)) (fun n => hf _)
    (s910_hsum_fiber hsum α) (fun n => s11p_kap n * r2CosBasis T n t) (B := Real.sqrt (2 / T))
    (fun n => s910_term_bound hT n t) (g := U α t) (fun x => hU α t t.2 x)).2 x
  exact h.tsum_eq

theorem s910_field_path {N : ℕ} (hN : 1 ≤ N) (P : Measure (EucConfig d N)) [IsProbabilityMeasure P]
    (hex : HRS.Whole.IsExchangeable P) (hφ : IsSummableFeatureFamily (J1 d) (fun n x => s11p_cJ T * f (σ n) x))
    (X : EucConfig d N) (t : Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    OscDual.coord (OscPath.at' (s11p_J hT M (r2FieldH (s11p_basis σ) (fun n x => s11p_cJ T * f (σ n) x) P X))
      t) α = Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (U α t) - HRS.Whole.pair (HRS.Whole.meanEmpirical P) (U α t)) := by
  haveI : IsProbabilityMeasure (HRS.Whole.firstMarginal P) := s99_nu_prob hN
  have hme : HRS.Whole.meanEmpirical P = HRS.Whole.firstMarginal P :=
    HRS.Whole.meanEmpirical_eq_firstMarginal P hex hN
  haveI hm2 : IsProbabilityMeasure (HRS.Whole.meanEmpirical P) := HRS.Whole.meanEmpirical_isProbabilityMeasure P hN
  haveI hm1 : IsProbabilityMeasure (HRS.Whole.empirical X) := HRS.Whole.empirical_isProbabilityMeasure hN X
  have hmℓ := s45_feature_memℓp hN hφ (ν := HRS.Whole.firstMarginal P) X
  have hz : ∀ q : ℕ × MultiIndex d, (r2FieldH (s11p_basis σ) (fun n x => s11p_cJ T * f (σ n) x) P X).c q =
      s11p_cJ T * (Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (f q) - HRS.Whole.pair (HRS.Whole.meanEmpirical P) (f q))) := by
    intro q
    obtain ⟨n, rfl⟩ := σ.surjective q
    rw [s910_field_eq hN (s11p_basis σ) hφ P hex X, s910_coord_symm]
    unfold featureVec
    rw [s45_coord_ofSeq hmℓ n, ← hme]
    simp only [Equiv.symm_apply_apply, HRS.Whole.pair]
    rw [integral_const_mul, integral_const_mul]
    ring
  rw [s910_J_coord_series hT M _ (fun q => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (f q) -
    HRS.Whole.pair (HRS.Whole.meanEmpirical P) (f q))) hz t α]
  have hU' : S11pSeries (s910_data hf hsum) T U := fun α t ht x => hU α t ht x
  have h1 := s11p_mu_series (HRS.Whole.empirical X) hT hU' α t t.2
  have h2 := s11p_mu_series (HRS.Whole.meanEmpirical P) hT hU' α t t.2
  have h3 := (h1.sub h2).mul_left (Real.sqrt N)
  have e : (fun n : ℕ => Real.sqrt N * (s11p_kap n * r2CosBasis T n t * ∫ y, (s910_data hf hsum).f (n, α) y ∂(HRS.Whole.empirical X) -
      s11p_kap n * r2CosBasis T n t * ∫ y, (s910_data hf hsum).f (n, α) y ∂(HRS.Whole.meanEmpirical P))) =
      fun n => s11p_kap n * r2CosBasis T n t * (Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (f (n, α)) -
        HRS.Whole.pair (HRS.Whole.meanEmpirical P) (f (n, α)))) := funext fun n => by
    simp only [HRS.Whole.pair]
    show Real.sqrt N * (s11p_kap n * r2CosBasis T n t * ∫ y, f (n, α) y ∂(HRS.Whole.empirical X) -
      s11p_kap n * r2CosBasis T n t * ∫ y, f (n, α) y ∂(HRS.Whole.meanEmpirical P)) = _
    ring
  rw [e] at h3
  rw [h3.tsum_eq]
  simp only [HRS.Whole.pair]

end Paths

end HRS.MS.R2Obs

end
