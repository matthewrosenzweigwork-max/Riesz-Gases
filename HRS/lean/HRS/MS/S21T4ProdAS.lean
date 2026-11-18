import HRS.MS.S21T4ProdAR

/-! Physical S13 singular product joint CLT in uncentered pair-energy normalization. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole
variable {d : ℕ}

theorem s21t4_physical_singular_joint_one_space
    (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (M L : ℝ) (ρ : Euc d → ℝ) (hρ : IsRound2Density d s M L ρ)
    [IsProbabilityMeasure (HRS.Whole.withDensityReal ρ)]
    (I : ProductGaussian (HRS.Whole.withDensityReal ρ))
    {n : ℕ} (f : Fin n → Euc d → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (HRS.Whole.withDensityReal ρ))
    (B : ℝ) (h : Euc d → Euc d → ℝ) (hh : IsBoundedPairKernel s B h) :
    ∃ Q : I.Ω → ℝ, MemLp Q 2 I.P ∧
      TendstoInDistribution
        (fun N (X : EucConfig d N) =>
          ((fun i => Real.sqrt N *
            (HRS.Whole.pair (HRS.Whole.empirical X) (f i) -
              HRS.Whole.pair (HRS.Whole.withDensityReal ρ) (f i))),
           (N : ℝ) * pairEnergy h X (HRS.Whole.withDensityReal ρ))) atTop
        (fun ω : I.Ω => ((fun i => I.η (f i) ω),
          (1 / 2 : ℝ) * Q ω -
            (1 / 2) * ∫ x, ∫ y, h x y
              ∂(HRS.Whole.withDensityReal ρ)
              ∂(HRS.Whole.withDensityReal ρ)))
        (fun N => Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ) I.P := by
  letI := I.mΩ
  letI := I.prob
  obtain ⟨Q, hQ, hclt⟩ :=
    s21t4_physical_singular_centered_joint_clt hd s hs0 hs M L ρ hρ I f hf B h hh
  let b : ℝ := (1 / 2) * ∫ x, ∫ y, h x y
    ∂(HRS.Whole.withDensityReal ρ)
    ∂(HRS.Whole.withDensityReal ρ)
  let F : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ :=
    fun z => (z.1, z.2 - b)
  have hF : Continuous F :=
    continuous_fst.prodMk (continuous_snd.sub continuous_const)
  have hc := hclt.continuous_comp hF
  refine ⟨Q, hQ, ?_⟩
  convert hc using 1
  · funext N X
    apply Prod.ext
    · rfl
    · simp only [F, b, Function.comp_def, sub_add_cancel, add_sub_cancel_right]
  · funext ω
    apply Prod.ext
    · rfl
    · rfl

end HRS.MS.R26T3
