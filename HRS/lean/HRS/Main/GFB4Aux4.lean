import HRS.Main.GFB4Aux3

/-!
# GFB4, part 4: `gfb4_vec_gaussian`, the joint Gaussian law of `L²`-limits of Itô sums
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.GF

open HRS HRS.Uniform.Q54c HRS.Uniform.Q07c

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {G : ℝ → Ω → H} {C : ℝ → H →L[ℝ] H →L[ℝ] ℝ} {T : ℝ}

theorem gfb4_vec_gaussian (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0) (hT : 0 < T)
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc 0 T) (ys : Fin p → ℝ → H) {B : ℝ}
    (hB : ∀ a, ∀ σ ∈ Set.Icc 0 (ts a), ‖ys a σ‖ ≤ B)
    (hw : ∀ a, ∀ x : H, ContinuousOn (fun σ => inner ℝ (ys a σ) x) (Set.Icc 0 (ts a)))
    (X : Ω → EuclideanSpace ℝ (Fin p)) (hXm : Measurable X)
    (hL2 : ∀ a, Tendsto (fun N => ∫⁻ ω, ‖X ω a - isum (fun σ => G σ ω) (ys a) T (ts a) N‖ₑ ^ 2 ∂P)
      atTop (𝓝 0)) :
    P.map X = multivariateGaussian 0 (Matrix.of fun a b =>
      ∫ σ in Set.Icc 0 (min (ts a) (ts b)), C σ (ys a σ) (ys b σ)) := by
  classical
  have hT0 : 0 ≤ T := hT.le
  set yc : Fin p → ℝ → H := fun a => clampPath (ys a) (ts a) with hyc
  have hcc : ∀ a, Continuous fun σ : ℝ => max 0 (min σ (ts a)) := fun a =>
    continuous_const.max (continuous_id.min continuous_const)
  have hcmem : ∀ a σ, max 0 (min σ (ts a)) ∈ Set.Icc 0 (ts a) := fun a σ =>
    ⟨le_max_left _ _, max_le (hts a).1 (min_le_right _ _)⟩
  have hycy : ∀ a, ∀ σ ∈ Set.Icc 0 (ts a), yc a σ = ys a σ := by
    intro a σ hσ
    simp only [hyc, clampPath]
    rw [min_eq_left hσ.2, max_eq_right hσ.1]
  have hycB : ∀ a σ, ‖yc a σ‖ ≤ B := fun a σ => hB a _ (hcmem a σ)
  have hycw : ∀ a x, Continuous fun σ => inner ℝ (yc a σ) x := fun a x =>
    (hw a x).comp_continuous (hcc a) (hcmem a)
  have hycm : ∀ a, Measurable (yc a) := fun a => gfb4_measurable_of_weak fun x => (hycw a x).measurable
  have hsame : ∀ a ω N, isum (fun σ => G σ ω) (ys a) T (ts a) N =
      isum (fun σ => G σ ω) (yc a) T (ts a) N := fun a ω N =>
    (isum_clamp (fun σ => G σ ω) (ys a) hT0 (hts a).1 N).symm
  set XN : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun N ω =>
    WithLp.toLp 2 fun a => isum (fun σ => G σ ω) (ys a) T (ts a) N with hXN
  have hXNm : ∀ N, Measurable (XN N) := by
    intro N
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp ?_
    exact measurable_pi_iff.2 fun a => measurable_isum hG (ys a) (ts a) N
  obtain ⟨ω₀, hω₀tc, hω₀path⟩ : ∃ ω₀ : Ω, (∀ σ ∈ Set.Icc 0 T, IsTraceClassCov (C σ)) ∧
      IntegrableOn (fun σ => traceNormForm (C σ)) (Set.Icc 0 T) := by
    obtain ⟨ω, h1, h3⟩ := (hG.sigma_traceClass.and hG.sigma_pathint).exists
    exact ⟨ω, h1, h3⟩
  have hCm : ∀ u v : H, Measurable fun σ => C σ u v := fun u v =>
    (hG.sigma_meas u v).comp (measurable_id.prodMk (measurable_const (a := ω₀)))
  have hcov : ∀ a b, Tendsto (fun N : ℕ => ∫ ω, isum (fun σ => G σ ω) (ys a) T (ts a) N *
      isum (fun σ => G σ ω) (ys b) T (ts b) N ∂P) atTop
      (𝓝 (∫ σ in Set.Icc 0 (min (ts a) (ts b)), C σ (ys a σ) (ys b σ))) := by
    intro a b
    have hlim' := gfb4_cov_sum_tendsto (T := T) (ta := ts a) (tb := ts b) hT (hts a) (hts b)
      (hycm a) (hycm b) (hycB a) (hycB b) (hycw a) (hycw b) (C := C) (c := fun σ => traceNormForm (C σ))
      hω₀tc (fun σ => traceNormForm_nonneg _)
      (fun σ hσ u v => abs_apply_le_tn (hω₀tc σ hσ) u v) hω₀path hCm
    have e1 : (fun N : ℕ => ∫ ω, isum (fun σ => G σ ω) (ys a) T (ts a) N *
        isum (fun σ => G σ ω) (ys b) T (ts b) N ∂P) = fun N => ∑ i ∈ Finset.range (N + 1),
          ∫ σ in Set.Ioc (gridPt T N i) (gridPt T N (i + 1)) ∩ Set.Iic (min (ts a) (ts b)),
            C σ (yc a (min (gridPt T N i) (ts a))) (yc b (min (gridPt T N i) (ts b))) := by
      funext N
      simp_rw [hsame]
      exact isum_cov hG hT0 (hts a) (hts b) (yc a) (yc b) N
    rw [e1]
    have e2 : ∫ σ in Set.Icc 0 (min (ts a) (ts b)), C σ (yc a σ) (yc b σ) =
        ∫ σ in Set.Icc 0 (min (ts a) (ts b)), C σ (ys a σ) (ys b σ) :=
      setIntegral_congr_fun measurableSet_Icc fun σ hσ => by
        rw [hycy a σ ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩, hycy b σ ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩]
    rw [← e2]
    exact hlim'
  set S : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b =>
    ∫ σ in Set.Icc 0 (min (ts a) (ts b)), C σ (ys a σ) (ys b σ) with hS
  set Zx : ℕ → EuclideanSpace ℝ (Fin p) → Ω → ℝ := fun N x ω =>
    ∑ a, x a * isum (fun σ => G σ ω) (ys a) T (ts a) N with hZx
  set QN : ℕ → EuclideanSpace ℝ (Fin p) → ℝ := fun N x => ∫ ω, (Zx N x ω) ^ 2 ∂P with hQN
  have hZm : ∀ N x, Measurable (Zx N x) := fun N x =>
    Finset.measurable_sum _ fun a _ => (measurable_isum hG (ys a) (ts a) N).const_mul _
  have hinner : ∀ N x ω, inner ℝ (XN N ω) x = Zx N x ω := by
    intro N x ω
    simp only [hXN, hZx, PiLp.inner_apply, WithLp.ofLp_toLp]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [mul_comm]
  have hchar : ∀ N x, charFun (P.map (XN N)) x = Complex.exp (-(QN N x : ℂ) / 2) := by
    intro N x
    obtain ⟨v, hv⟩ := isum_comb_law hG hGc hGz hT0 ts hts ys N (fun a => x a)
    exact charFun_vec_of_gauss (hZm N x) v hv (XN N) (hXNm N) x (hinner N x)
  have hL2' : ∀ N a, MemLp (fun ω => isum (fun σ => G σ ω) (ys a) T (ts a) N) 2 P :=
    fun N a => isum_memLp hG hT0 (hts a) (ys a) N
  have hQexp : ∀ N x, QN N x = ∑ a, ∑ b, x a * x b *
      ∫ ω, isum (fun σ => G σ ω) (ys a) T (ts a) N * isum (fun σ => G σ ω) (ys b) T (ts b) N ∂P := by
    intro N x
    simp only [hQN, hZx, sq, Finset.sum_mul_sum]
    have hi : ∀ a b, Integrable (fun ω => x a * isum (fun σ => G σ ω) (ys a) T (ts a) N *
        (x b * isum (fun σ => G σ ω) (ys b) T (ts b) N)) P := by
      intro a b
      have := ((hL2' N a).const_mul (x a)).integrable_mul ((hL2' N b).const_mul (x b))
      exact this
    rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun b _ => hi a b)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ (fun b _ => hi a b)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only []
    ring
  have hQ : ∀ x : EuclideanSpace ℝ (Fin p), Tendsto (fun N => QN N x) atTop (𝓝 (x ⬝ᵥ S *ᵥ x)) := by
    intro x
    simp_rw [hQexp]
    have : x ⬝ᵥ S *ᵥ x = ∑ a, ∑ b, x a * x b * S a b := by
      simp only [dotProduct, Matrix.mulVec, hS, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [this]
    refine tendsto_finset_sum _ fun a _ => tendsto_finset_sum _ fun b _ => ?_
    exact (hcov a b).const_mul _
  obtain ⟨ns, hns, hae⟩ := gfb4_subseq_ae P hXNm hXm hL2
  have hchar_lim : ∀ x, charFun (P.map X) x = Complex.exp (-((x ⬝ᵥ S *ᵥ x : ℝ) : ℂ) / 2) := fun x =>
    gfb4_charFun_limit_ae P (fun k => hXNm (ns k)) hXm hae (fun x => x ⬝ᵥ S *ᵥ x)
      (fun k x => QN (ns k) x) (fun x => (hQ x).comp hns.tendsto_atTop) (fun k x => hchar (ns k) x) x
  have hSsymm : ∀ a b, S a b = S b a := by
    intro a b
    simp only [hS, Matrix.of_apply]
    rw [min_comm]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    exact C_symm hG ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans (hts b).2)⟩ _ _
  have hPSD : S.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · ext a b
      simp [Matrix.conjTranspose_apply, hSsymm a b]
    · have := ge_of_tendsto (hQ (WithLp.toLp 2 x)) (Filter.Eventually.of_forall fun N =>
        integral_nonneg fun ω => sq_nonneg _)
      simpa using this
  exact eq_multivariateGaussian P hXm hPSD hchar_lim

end HRS.GF
