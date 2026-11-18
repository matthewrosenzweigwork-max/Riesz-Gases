import HRS.Main.A9Aux10

/-!
# Packet A9, part 11: the Gaussian side: law of finitely many coordinates, tail of the Gaussian field
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.A33 HRS.PDE HRS.Main.A8P HRS.GF HRS.Uniform

variable {d : ℕ}

/-- `K_j = e^{|Λ₁| t} ‖φ_j‖_{H^{m_*}}`. -/
def a9K (d : ℕ) (Λ₁ t : ℝ) (j : NonzeroLattice d) : ℝ := a8pK Λ₁ t (a9phi d j)

theorem a9K_nonneg (Λ₁ t : ℝ) (j : NonzeroLattice d) : 0 ≤ a9K d Λ₁ t j := a8pK_nonneg _ _ _

theorem a9K_summable (Λ₁ t : ℝ) : Summable (a9K d Λ₁ t) := by
  have h := (a9_summable_modes (d := d)).mul_left (Real.exp (|Λ₁| * t))
  refine h.congr fun j => ?_
  unfold a9K a8pK
  rw [a9phi_sobolevNorm_mStar]

theorem a9_sqrt_form {A K C : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hC : 0 ≤ C) :
    Real.sqrt (A * (C * K) ^ 2) = Real.sqrt A * (C * K) := by
  rw [Real.sqrt_mul hA, Real.sqrt_sq (mul_nonneg hC hK)]

section GaussSide

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

theorem a9_surrogateCov_noise (D : DynData d) (ρ : ℝ → Torus d → ℝ) (qq t : ℝ) {q : ℕ}
    (φ : Fin q → Torus d → ℝ) :
    surrogateCov D ρ qq (fun _ : Fin q => t) φ =
      Matrix.of fun a b => noiseCovariance D ρ qq t (φ a) (φ b) := by
  ext a b
  simp [surrogateCov, noiseCovariance]

theorem a9_integratedCov_eq (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) {q : ℕ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ) :
    integratedCov S.T (a8pSb S N (fun _ : Fin q => t) φ) =
      Matrix.of fun a b => noiseCovariance (S.dyn N) (S.ρ N) (S.qN N) t (φ a) (φ b) := by
  have hsc := a8p_surrogateCov_eq (S.dyn N) (S.ρ N) (S.qN N) S.T (fun _ : Fin q => t) φ
    (fun _ => ht.2) (fun r => S.ρ N (Q54c.clampT S.T r)) (fun r hr => by rw [Q54c.clampT_of_mem hr])
  have hq := a8p_q_eq S N
  rw [← a9_surrogateCov_noise, hsc]
  unfold a8pSb
  rw [hq]
  rfl

/-- The law of the coordinates `(G_{k_a})_a` of the Gaussian field. -/
theorem a9_gauss_law (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {q : ℕ} (k : Fin q → NonzeroLattice d)
    {νG : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hνG : IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG) :
    νG.map (hmCoordCLM (fun a => a9unit (gammaIdx d : ℝ) (k a))) =
      multivariateGaussian 0 (integratedCov S.T
        (a8pSb S N (fun _ : Fin q => t) (fun a => a9phi d (k a)))) := by
  obtain ⟨hprob, hcg, hcov⟩ := hνG
  haveI := hprob
  rw [a9_gauss_coord hcg, a9_integratedCov_eq hS hN ht]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [← hcov _ _ (a9phi_smooth (k i)) (a9phi_smooth (k j))]
  refine integral_congr_ae (Eventually.of_forall fun F => ?_)
  simp only [a9unit_inner, a9_eval_phi]

/-- The Gaussian tail `E‖G - ι_Λ P_Λ G‖ ≤ ∑_{j ∉ Λ} E|G_j|`. -/
theorem a9_gauss_tail (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {q : ℕ} {k : Fin q → NonzeroLattice d}
    (hk : Function.Injective k)
    {νG : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hνG : IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG) :
    ∫⁻ y, ENNReal.ofReal ‖y - embedCLM (fun a => a9unit (gammaIdx d : ℝ) (k a))
        (hmCoordCLM (fun a => a9unit (gammaIdx d : ℝ) (k a)) y)‖ ∂νG ≤
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
  refine (a9_lintegral_norm_le νG _ hQm.aemeasurable b hb0 hbs fun j => ?_)
  by_cases hj : j ∈ Set.range k
  · obtain ⟨a, rfl⟩ := hj
    have : ∀ y : NegSobolev d (gammaIdx d : ℝ), NegSobolev.coord (y - embedCLM
        (fun a => a9unit (gammaIdx d : ℝ) (k a)) (hmCoordCLM (fun a => a9unit (gammaIdx d : ℝ) (k a)) y))
        (k a) = 0 := fun y => by
      rw [a9_coord_sub_embed_mem hk, a9_coordCLM_apply]; ring
    simp [this, hb]
  · have : ∀ y : NegSobolev d (gammaIdx d : ℝ), NegSobolev.coord (y - embedCLM
        (fun a => a9unit (gammaIdx d : ℝ) (k a)) (hmCoordCLM (fun a => a9unit (gammaIdx d : ℝ) (k a)) y))
        j = NegSobolev.coord y j := fun y => a9_coord_sub_embed_nmem y _ j hj
    simp only [this, hb, if_neg hj]
    exact a9_gauss_coord_moment hspec hCa hS hN ht j hνG

end GaussSide

end HRS.Main.A9
