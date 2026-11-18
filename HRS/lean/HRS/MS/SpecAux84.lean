import HRS.MS.SpecAux83

/-!
# S8L: weighted integration by parts in coordinates (S8.7, block L)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_pair_coord` (the pairing `⟨∇f, ∇g⟩ = Σ ∂_i f ∂_i g`) and `s8p_hibp`:
for `ρ ∈ C¹` with `∇ρ = -ρ ∇W`, `s ∈ C²`, `Ψ ∈ C¹` with compact support,
`∫ ρ ⟨∇s, ∇Ψ⟩ = ∫ ρ (L_W s) Ψ`, `L_W = -Δ + ⟨∇W, ∇·⟩` (the hypothesis `hibp` of `s8p_en_of_sub`).
-/

noncomputable section

open MeasureTheory Real Filter Topology

namespace HRS.MS.Spec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ V)

/-- Pairing in coordinates. -/
theorem s8p_pair_coord (f g : V → ℝ) (x : V) :
    s8p_pair f g x = ∑ i, fderiv ℝ f x (b i) * fderiv ℝ g x (b i) := by
  unfold s8p_pair s8p_grad
  have h := b.sum_repr' ((InnerProductSpace.toDual ℝ V).symm (fderiv ℝ g x))
  conv_lhs => rw [← h]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 1
  have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := b i) (y := fderiv ℝ g x)
  rw [← this, real_inner_comm]


/-- Weighted integration by parts against compactly supported test functions. -/
theorem s8p_hibp {ρ W s Ψ : V → ℝ} (hρ : ContDiff ℝ 1 ρ) (hρd : ∀ x, fderiv ℝ ρ x = -(ρ x) • fderiv ℝ W x)
    (hW : ContDiff ℝ 1 W) (hs : ContDiff ℝ 2 s) (hΨ : ContDiff ℝ 1 Ψ) (hcs : HasCompactSupport Ψ) :
    ∫ x, ρ x * s8p_pair s Ψ x = ∫ x, ρ x * (s8p_Lw b W s x * Ψ x) := by
  have hDs : ∀ i, ContDiff ℝ 1 (fun x => fderiv ℝ s x (b i)) := fun i =>
    (hs.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hf : ∀ i, ContDiff ℝ 1 (fun x => ρ x * fderiv ℝ s x (b i)) := fun i => hρ.mul (hDs i)
  have hdΨ : HasCompactSupport (fderiv ℝ Ψ) := hcs.fderiv ℝ
  have hcsΨ : ∀ F : V → ℝ, Continuous F → Integrable (fun x => F x * Ψ x) := fun F hF =>
    (hF.mul hΨ.continuous).integrable_of_hasCompactSupport (hcs.mul_left)
  have hcsdΨ : ∀ F : V → ℝ, Continuous F → ∀ i, Integrable (fun x => F x * fderiv ℝ Ψ x (b i)) := fun F hF i =>
    (hF.mul ((hΨ.continuous_fderiv (by norm_num)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (by
        refine HasCompactSupport.intro hdΨ (fun x hx => ?_)
        simp [image_eq_zero_of_notMem_tsupport hx])
  have key : ∀ i, ∫ x, ρ x * (fderiv ℝ s x (b i) * fderiv ℝ Ψ x (b i)) =
      ∫ x, ρ x * ((fderiv ℝ W x (b i) * fderiv ℝ s x (b i) - fderiv ℝ (fderiv ℝ s) x (b i) (b i)) * Ψ x) := fun i => by
    have hI := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure V))
      (f := fun x => ρ x * fderiv ℝ s x (b i)) (g := Ψ) (v := b i)
      (by
        refine (hcsΨ (fun x => fderiv ℝ (fun x => ρ x * fderiv ℝ s x (b i)) x (b i)) ?_).congr
          (Filter.Eventually.of_forall fun x => rfl)
        exact ((hf i).continuous_fderiv (by norm_num)).clm_apply continuous_const)
      ((hcsdΨ _ (hρ.continuous.mul (hDs i).continuous) i).congr (Filter.Eventually.of_forall fun x => rfl))
      (hcsΨ _ (hρ.continuous.mul (hDs i).continuous))
      (fun x _ => ((hf i).differentiable (by norm_num)) x) (fun x _ => (hΨ.differentiable (by norm_num)) x)
    have hd : ∀ x, fderiv ℝ (fun x => ρ x * fderiv ℝ s x (b i)) x (b i) =
        ρ x * (fderiv ℝ (fderiv ℝ s) x (b i) (b i) - fderiv ℝ W x (b i) * fderiv ℝ s x (b i)) := fun x => by
      have h1 : DifferentiableAt ℝ ρ x := (hρ.differentiable (by norm_num)) x
      have h2 := ((hDs i).differentiable (by norm_num)) x
      have e : fderiv ℝ (fun x => ρ x * fderiv ℝ s x (b i)) x = ρ x • fderiv ℝ (fun x => fderiv ℝ s x (b i)) x +
          (fderiv ℝ s x (b i)) • fderiv ℝ ρ x := (h1.hasFDerivAt.mul h2.hasFDerivAt).fderiv
      rw [e]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hρd x, s8p_fderiv_apply hs (b i) (b i) x]
      simp
      ring
    simp only [hd] at hI
    calc ∫ x, ρ x * (fderiv ℝ s x (b i) * fderiv ℝ Ψ x (b i))
        = ∫ x, (ρ x * fderiv ℝ s x (b i)) * fderiv ℝ Ψ x (b i) := integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = _ := hI.trans (by
        rw [← integral_neg]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only; ring)
  have hsum : ∀ x, ρ x * s8p_pair s Ψ x = ∑ i, ρ x * (fderiv ℝ s x (b i) * fderiv ℝ Ψ x (b i)) := fun x => by
    rw [s8p_pair_coord b, Finset.mul_sum]
  have hsum2 : ∀ x, ρ x * (s8p_Lw b W s x * Ψ x) =
      ∑ i, ρ x * ((fderiv ℝ W x (b i) * fderiv ℝ s x (b i) - fderiv ℝ (fderiv ℝ s) x (b i) (b i)) * Ψ x) := fun x => by
    simp only [s8p_Lw, s8p_lap]
    rw [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_sub_distrib]
    ring
  simp_rw [hsum, hsum2]
  rw [integral_finset_sum _ (fun i _ => ?_), integral_finset_sum _ (fun i _ => ?_)]
  · exact Finset.sum_congr rfl fun i _ => key i
  · have := hcsΨ (fun x => ρ x * (fderiv ℝ W x (b i) * fderiv ℝ s x (b i) - fderiv ℝ (fderiv ℝ s) x (b i) (b i))) (by
      have h2 : Continuous fun x => fderiv ℝ (fderiv ℝ s) x (b i) (b i) :=
        (((hs.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
      exact hρ.continuous.mul ((((hW.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul (hDs i).continuous).sub h2))
    exact this.congr (Filter.Eventually.of_forall fun x => by ring)
  · have := hcsdΨ (fun x => ρ x * fderiv ℝ s x (b i)) (hρ.continuous.mul (hDs i).continuous) i
    exact this.congr (Filter.Eventually.of_forall fun x => by ring)

end HRS.MS.Spec
