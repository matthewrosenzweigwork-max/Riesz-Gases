import HRS.Main.A1014Aux8

/-!
# Packet A1014, part 9: the four term bounds of `a1014_core_abs` for `p = 1` and `p = 2`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A1014

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.A33 HRS.PDE HRS.Main HRS.Main.A8P HRS.Main.A9 HRS.GF HRS.Uniform

variable {d : ℕ}

section Gauss2

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- Second moment of one coordinate of the Gaussian field. -/
theorem a1014_gauss_coord_sq (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (k : NonzeroLattice d)
    {νG : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hνG : IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG) :
    ∫⁻ F, ENNReal.ofReal (NegSobolev.coord F k ^ 2) ∂νG ≤
      ENNReal.ofReal (2 * S.qN N * t * (d * (Ca * a8pK Λ₁ t (a9phi d k))) ^ 2) := by
  obtain ⟨hprob, hcg, hcov⟩ := hνG
  haveI := hprob
  haveI : IsGaussian νG := hcg.1
  have hL : MemLp (fun F : NegSobolev d (gammaIdx d : ℝ) => NegSobolev.coord F k) 2 νG := by
    have e : (fun F : NegSobolev d (gammaIdx d : ℝ) => NegSobolev.coord F k) =
        fun F => innerSL ℝ (a9unit (gammaIdx d : ℝ) k) F := by
      funext F; rw [innerSL_apply_apply, a9unit_inner]
    rw [e]
    exact IsGaussian.memLp_dual νG (innerSL ℝ (a9unit (gammaIdx d : ℝ) k)) 2 (by simp)
  have hvar : ∫ F, NegSobolev.coord F k ^ 2 ∂νG = noiseCovariance (S.dyn N) (S.ρ N) (S.qN N) t
      (a9phi d k) (a9phi d k) := by
    rw [← hcov _ _ (a9phi_smooth k) (a9phi_smooth k)]
    refine integral_congr_ae (Eventually.of_forall fun F => ?_)
    simp only [a9_eval_phi, sq]
  have hle := (a9_noiseCov_le hspec hCa hS hN ht (a9phi_cont k) (a9phi_mem _ k)).2
  have hint : Integrable (fun F : NegSobolev d (gammaIdx d : ℝ) => NegSobolev.coord F k ^ 2) νG :=
    hL.integrable_sq
  have e : ENNReal.ofReal (∫ F, NegSobolev.coord F k ^ 2 ∂νG) =
      ∫⁻ F, ENNReal.ofReal (NegSobolev.coord F k ^ 2) ∂νG :=
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun F => sq_nonneg _)
  rw [← e]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hvar]; exact hle

/-- The `L²` Gaussian tail: `(E ‖y - ι c y‖²)^{1/2} ≤ ∑_{j ∉ range k} (2 q t (d Ca K_j)²)^{1/2}`. -/
theorem a1014_gauss_tail2 (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {q : ℕ} {k : Fin q → NonzeroLattice d}
    (hk : Function.Injective k)
    {νG : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hνG : IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG) :
    (∫⁻ y, ENNReal.ofReal (‖y - embedCLM (fun a => a9unit (gammaIdx d : ℝ) (k a))
        (hmCoordCLM (fun a => a9unit (gammaIdx d : ℝ) (k a)) y)‖ ^ (2 : ℝ)) ∂νG) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (∑' j, if j ∈ Set.range k then 0 else
        Real.sqrt (2 * S.qN N * t * (d * (Ca * a9K d Λ₁ t j)) ^ 2)) := by
  classical
  have hprob := hνG.1
  haveI := hprob
  have hq := (a8p_q_bounds S hN).1
  have ht0 : 0 ≤ t := ht.1
  have hCd : 0 ≤ (d : ℝ) * Ca := mul_nonneg (Nat.cast_nonneg d) hCa
  set gm : NonzeroLattice d → ℝ := fun j =>
    Real.sqrt (2 * S.qN N * t * (d * (Ca * a9K d Λ₁ t j)) ^ 2) with hgm
  have hgm_eq : ∀ j, gm j = Real.sqrt (2 * S.qN N * t) * ((d : ℝ) * Ca) * a9K d Λ₁ t j := by
    intro j
    simp only [hgm]
    have e : (d : ℝ) * (Ca * a9K d Λ₁ t j) = ((d : ℝ) * Ca) * a9K d Λ₁ t j := by ring
    rw [e, a9_sqrt_form (by positivity) (a9K_nonneg _ _ j) hCd]
    ring
  have hgm0 : ∀ j, 0 ≤ gm j := fun j => Real.sqrt_nonneg _
  set b : NonzeroLattice d → ℝ := fun j => if j ∈ Set.range k then 0 else gm j with hb
  have hb0 : ∀ j, 0 ≤ b j := fun j => by simp only [hb]; split_ifs <;> simp [hgm0]
  have hbs : Summable b := by
    have h1 : Summable gm := by
      have := (a9K_summable (d := d) Λ₁ t).mul_left (Real.sqrt (2 * S.qN N * t) * ((d : ℝ) * Ca))
      refine this.congr fun j => ?_
      rw [hgm_eq]
    refine Summable.of_nonneg_of_le hb0 (fun j => ?_) h1
    simp only [hb]; split_ifs
    · exact hgm0 j
    · exact le_rfl
  have hQm : Measurable fun y : NegSobolev d (gammaIdx d : ℝ) => y - embedCLM
      (fun a => a9unit (gammaIdx d : ℝ) (k a)) (hmCoordCLM (fun a => a9unit (gammaIdx d : ℝ) (k a)) y) :=
    measurable_id.sub ((embedCLM _).continuous.measurable.comp (hmCoordCLM _).continuous.measurable)
  have key := a1014_lintegral_sq_norm_le νG _ hQm.aemeasurable b hb0 hbs fun j => ?_
  · exact key
  by_cases hj : j ∈ Set.range k
  · obtain ⟨a, rfl⟩ := hj
    have : ∀ y : NegSobolev d (gammaIdx d : ℝ), NegSobolev.coord (y - embedCLM
        (fun a => a9unit (gammaIdx d : ℝ) (k a)) (hmCoordCLM (fun a => a9unit (gammaIdx d : ℝ) (k a) ) y))
        (k a) = 0 := fun y => by
      rw [a9_coord_sub_embed_mem hk, a9_coordCLM_apply]; ring
    simp [this, hb]
  · have : ∀ y : NegSobolev d (gammaIdx d : ℝ), NegSobolev.coord (y - embedCLM
        (fun a => a9unit (gammaIdx d : ℝ) (k a)) (hmCoordCLM (fun a => a9unit (gammaIdx d : ℝ) (k a)) y))
        j = NegSobolev.coord y j := fun y => a9_coord_sub_embed_nmem y _ j hj
    simp only [this, hb, if_neg hj]
    refine (a1014_gauss_coord_sq hspec hCa hS hN ht j hνG).trans (le_of_eq ?_)
    congr 1
    simp only [hgm]
    rw [Real.sq_sqrt (by positivity)]
    rfl

end Gauss2

end HRS.Main.A1014
