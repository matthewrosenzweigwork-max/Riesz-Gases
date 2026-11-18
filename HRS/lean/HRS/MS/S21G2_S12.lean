import HRS.MS.S21G2_S12F

/-!
# S21G2 S12 -- finite-rank joint product central limit theorem (R26-T3.S12)

Contract with ONE repair: the skeleton does not elaborate (`TendstoInDistribution .. G` needs `IsProbabilityMeasure G`); the minimal fix is the extra
existential `∃ (_ : IsProbabilityMeasure G)` (a Gaussian measure is a probability measure anyway).  Route: replace `f_i` by measurable versions; the Gaussian field of S11a gives `G`; vector CLT
(part B) for the i.i.d. coordinates of `infinitePi μ`; LLN in probability for the diagonal term; Slutsky (Mathlib) and the closed
formula of part E (J08); transfer to the product measures (part A), a.e. replacement `f̂ → f`, index shift.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3

theorem r26t3_product_finite_rank {d n m : ℕ} (μ : Measure (HRS.Euc d)) [IsProbabilityMeasure μ]
    (f : Fin n → HRS.Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (c : Fin m → Fin m → ℝ) (u : Fin m → HRS.Euc d → ℝ) (hu : HRS.Whole.IsR2FiniteRankData c u) :
    ∃ (G : Measure ((Fin n → ℝ) × (Fin m → ℝ))) (_ : IsProbabilityMeasure G), HRS.IsCenteredGaussian G ∧
      (∀ L M : ((Fin n → ℝ) × (Fin m → ℝ)) →L[ℝ] ℝ,
        ∫ z, L z * M z ∂G = ∫ x,
          L (fun i => HRS.Whole.projMean μ (f i) x, fun j => HRS.Whole.projMean μ (u j) x) *
          M (fun i => HRS.Whole.projMean μ (f i) x, fun j => HRS.Whole.projMean μ (u j) x) ∂μ) ∧
      TendstoInDistribution
        (fun N (X : HRS.Whole.EucConfig d N) =>
          (fun i => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (f i) - HRS.Whole.pair μ (f i)),
           (N : ℝ) * HRS.Whole.pairEnergy (HRS.Whole.r2FiniteRankKernel c u) X μ)) atTop
        (fun z => (z.1, (1 / 2) * ∑ i, ∑ j, c i j * (z.2 i * z.2 j - HRS.Whole.pair μ (fun x => u i x * u j x))))
        (fun N => Measure.pi fun _ : Fin N => μ) G := by
  classical
  set fh : Fin n → HRS.Euc d → ℝ := fun i => (hf i).aestronglyMeasurable.mk (f i) with hfh
  have hfhm : ∀ i, Measurable (fh i) := fun i => (hf i).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfae : ∀ i, f i =ᵐ[μ] fh i := fun i => (hf i).aestronglyMeasurable.ae_eq_mk
  have hfh2 : ∀ i, MemLp (fh i) 2 μ := fun i => (memLp_congr_ae (hfae i)).1 (hf i)
  have huT : ∀ i, HRS.Whole.IsR2Test (u i) := fun i => ⟨hu.smooth i, hu.compactSupport i⟩
  have hu2 : ∀ i, MemLp (u i) 2 μ := fun i =>
    (huT i).1.continuous.memLp_of_hasCompactSupport (huT i).2
  set g : Fin (n + m) → HRS.Euc d → ℝ := Fin.append fh u with hgdef
  have hg : ∀ k, MemLp (g k) 2 μ := fun k => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa [hgdef] using hfh2 i
    · simpa [hgdef] using hu2 j
  have hgm : ∀ k, Measurable (g k) := fun k => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa [hgdef] using hfhm i
    · simpa [hgdef] using (huT j).1.continuous.measurable
  obtain ⟨Ω', _, P', _, Zv, hZm, hGv, hZl, hCov⟩ := s21g2_s12_gauss_field μ g hg
  set ψ : HRS.Euc d → EuclideanSpace ℝ (Fin (n + m)) :=
    fun x => WithLp.toLp 2 (fun k => HRS.Whole.projMean μ (g k) x) with hψdef
  have hpmm : ∀ k, Measurable (HRS.Whole.projMean μ (g k)) := fun k => (hgm k).sub measurable_const
  have hψ : Measurable ψ :=
    (PiLp.continuous_toLp 2 (fun _ : Fin (n + m) => ℝ)).measurable.comp (measurable_pi_iff.2 hpmm)
  have hpm2 : ∀ k, MemLp (HRS.Whole.projMean μ (g k)) 2 μ := fun k => (hg k).sub (memLp_const _)
  have hpm0 : ∀ k, ∫ x, HRS.Whole.projMean μ (g k) x ∂μ = 0 := fun k => by
    unfold HRS.Whole.projMean HRS.Whole.pair
    rw [integral_sub ((hg k).integrable one_le_two) (integrable_const _)]; simp
  set ZE : Ω' → EuclideanSpace ℝ (Fin (n + m)) := fun ω => WithLp.toLp 2 (Zv ω) with hZEdef
  have hZEm : Measurable ZE :=
    (PiLp.continuous_toLp 2 (fun _ : Fin (n + m) => ℝ)).measurable.comp hZm
  have hGE : HRS.IsCenteredGaussian (P'.map ZE) := by
    let T : (Fin (n + m) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + m)) :=
      (EuclideanSpace.equiv (Fin (n + m)) ℝ).symm.toContinuousLinearMap
    have hmapeq : P'.map ZE = (P'.map Zv).map T := by
      rw [Measure.map_map T.continuous.measurable hZm]; rfl
    rw [hmapeq]
    exact s21g2_s12_cg_map hGv T
  have hcovE : ∀ t : EuclideanSpace ℝ (Fin (n + m)), ∫ ω, ⟪ZE ω, t⟫ ^ 2 ∂P' = ∫ x, ⟪ψ x, t⟫ ^ 2 ∂μ := by
    intro t
    have e1 : ∀ ω, ⟪ZE ω, t⟫ = ∑ k, t k * Zv ω k := fun ω => by
      simp [hZEdef, PiLp.inner_apply, mul_comm]
    have e2 : ∀ x, ⟪ψ x, t⟫ = ∑ k, t k * HRS.Whole.projMean μ (g k) x := fun x => by
      simp [hψdef, PiLp.inner_apply, mul_comm]
    simp_rw [sq, e1, e2]
    exact hCov (fun k => t k) (fun k => t k)
  have hvclt := s21g2_s12_vclt μ hψ (fun k => hpm2 k) hpm0 hZEm.aemeasurable hGE hcovE
  -- the limit law
  set Tv := s21g2_s12_Tv n m with hTv
  have hGeq : (P'.map Zv).map Tv = P'.map (fun ω => Tv (Zv ω)) :=
    Measure.map_map Tv.continuous.measurable hZm
  have hcgG : HRS.IsCenteredGaussian ((P'.map Zv).map Tv) := s21g2_s12_cg_map hGv Tv
  haveI hprobG : IsProbabilityMeasure ((P'.map Zv).map Tv) := by
    have := hcgG.1; infer_instance
  have hpmae : ∀ᵐ x ∂μ, ∀ i, HRS.Whole.projMean μ (f i) x = HRS.Whole.projMean μ (fh i) x := by
    rw [ae_all_iff]
    intro i
    filter_upwards [hfae i] with x hx
    have hp : HRS.Whole.pair μ (f i) = HRS.Whole.pair μ (fh i) := integral_congr_ae (hfae i)
    simp only [HRS.Whole.projMean, hx, hp]
  have hcovG : ∀ L M : ((Fin n → ℝ) × (Fin m → ℝ)) →L[ℝ] ℝ,
      ∫ z, L z * M z ∂((P'.map Zv).map Tv) = ∫ x,
        L (fun i => HRS.Whole.projMean μ (f i) x, fun j => HRS.Whole.projMean μ (u j) x) *
        M (fun i => HRS.Whole.projMean μ (f i) x, fun j => HRS.Whole.projMean μ (u j) x) ∂μ := by
    intro L M
    obtain ⟨α, hα⟩ := s21g2_s12_lin_expand L
    obtain ⟨β, hβ⟩ := s21g2_s12_lin_expand M
    rw [← hTv] at hα hβ
    rw [hGeq, integral_map (φ := fun ω => Tv (Zv ω)) (f := fun z => L z * M z)
      (Tv.continuous.measurable.comp hZm).aemeasurable
      ((L.continuous.mul M.continuous).aestronglyMeasurable)]
    simp_rw [hα, hβ]
    rw [hCov α β]
    refine integral_congr_ae ?_
    filter_upwards [hpmae] with x hx
    have hw : (fun i => HRS.Whole.projMean μ (f i) x, fun j => HRS.Whole.projMean μ (u j) x) =
        Tv (fun k => HRS.Whole.projMean μ (g k) x) := by
      refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
      · simp [hTv, s21g2_s12_Tv_apply, hgdef, hx i]
      · simp [hTv, s21g2_s12_Tv_apply, hgdef]
    rw [hw, hα, hβ]
  refine ⟨(P'.map Zv).map Tv, hprobG, hcgG, hcovG, ?_⟩
  set Te : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] (Fin n → ℝ) × (Fin m → ℝ) :=
    Tv.comp (EuclideanSpace.equiv (Fin (n + m)) ℝ).toContinuousLinearMap with hTe
  have hTeapp : ∀ w : EuclideanSpace ℝ (Fin (n + m)), Te w =
      (fun i : Fin n => w (Fin.castAdd m i), fun j : Fin m => w (Fin.natAdd n j)) := fun w => rfl
  have hX := hvclt.continuous_comp (g := Te) Te.continuous
  -- the diagonal term and its law of large numbers
  set dg : HRS.Euc d → ℝ := fun x => HRS.Whole.r2FiniteRankKernel c u x x with hdg
  have hdgc : Continuous dg := by
    simp only [hdg, HRS.Whole.r2FiniteRankKernel]
    exact continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
      ((continuous_const.mul (huT a).1.continuous).mul (huT b).1.continuous)
  have hdgi : Integrable dg μ := by
    have : dg = fun x => ∑ a, ∑ b, c a b * (u a x * u b x) := funext fun x => by
      simp only [hdg, HRS.Whole.r2FiniteRankKernel]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      ((hu2 a).integrable_mul (hu2 b)).const_mul _
  have hI : ∀ a b, Integrable (fun x => c a b * (u a x * u b x)) μ := fun a b =>
    ((hu2 a).integrable_mul (hu2 b)).const_mul _
  have hc0 : ∫ x, dg x ∂μ = ∑ a, ∑ b, c a b * HRS.Whole.pair μ (fun x => u a x * u b x) := by
    have : ∀ x, dg x = ∑ a, ∑ b, c a b * (u a x * u b x) := fun x => by
      simp only [hdg, HRS.Whole.r2FiniteRankKernel]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    simp_rw [this]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hI a b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => hI a b]
    exact Finset.sum_congr rfl fun b _ => by rw [integral_const_mul]; rfl
  have hlln := s21g2_s12_lln μ hdgc.measurable hdgi
  set gm : ((Fin n → ℝ) × (Fin m → ℝ)) × ℝ → (Fin n → ℝ) × ℝ := fun p =>
    (p.1.1, (1 / 2) * ∑ i, ∑ j, c i j * p.1.2 i * p.1.2 j - (1 / 2) * p.2) with hgm
  have hgmc : Continuous gm := by
    refine Continuous.prodMk (continuous_fst.comp continuous_fst) ?_
    refine Continuous.sub (continuous_const.mul (continuous_finset_sum _ fun i _ =>
      continuous_finset_sum _ fun j _ => ?_)) (continuous_const.mul continuous_snd)
    exact (continuous_const.mul ((continuous_apply i).comp (continuous_snd.comp continuous_fst))).mul
      ((continuous_apply j).comp (continuous_snd.comp continuous_fst))
  have hYm : ∀ N : ℕ, AEMeasurable (fun ω : ℕ → HRS.Euc d => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, dg (ω k))
      (Measure.infinitePi fun _ : ℕ => μ) := fun N =>
    ((Finset.measurable_sum _ fun k _ => hdgc.measurable.comp (measurable_pi_apply k)).const_mul _).aemeasurable
  have hS := hX.continuous_comp_prodMk_of_tendstoInMeasure_const (g := gm) hgmc hlln hYm
  have hS1 := s21g2_s12_shift_in hS
  have hcomp : ∀ (M : ℕ) (ω : ℕ → HRS.Euc d) (k0 : Fin (n + m)),
      ((Real.sqrt M)⁻¹ • ∑ k ∈ Finset.range M, ψ (ω k)) k0 =
        (Real.sqrt M)⁻¹ * ∑ k : Fin M, HRS.Whole.projMean μ (g k0) (ω k) := fun M ω k0 => by
    rw [Fin.sum_univ_eq_sum_range (fun k => HRS.Whole.projMean μ (g k0) (ω k)) M]
    simp [hψdef, WithLp.ofLp_sum, Finset.sum_apply]
  have hS2 : TendstoInDistribution (fun (N : ℕ) (ω : ℕ → HRS.Euc d) =>
      s21g2_s12_Fhat μ fh c u (N + 1) (s21g2_s12_restr (N + 1) ω)) atTop
      (fun ω => gm (Te (ZE ω), ∫ x, dg x ∂μ)) (fun _ => Measure.infinitePi fun _ : ℕ => μ) P' := by
    refine TendstoInDistribution.congr (fun N => ae_of_all _ fun ω => ?_) (ae_of_all _ fun _ => rfl) hS1
    show gm (Te ((Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ • ∑ k ∈ Finset.range (N + 1), ψ (ω k)),
        ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.range (N + 1), dg (ω k)) =
      s21g2_s12_Fhat μ fh c u (N + 1) (s21g2_s12_restr (N + 1) ω)
    rw [s21g2_s12_Fhat_formula (Nat.succ_pos N) μ (fun i => (hfh2 i).integrable one_le_two) hu.symm huT]
    have hgl : ∀ i : Fin n, g (Fin.castAdd m i) = fh i := fun i => by simp [hgdef]
    have hgr : ∀ j : Fin m, g (Fin.natAdd n j) = u j := fun j => by simp [hgdef]
    have h1 : ∀ i : Fin n, (Te ((Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ • ∑ k ∈ Finset.range (N + 1), ψ (ω k))).1 i =
        (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ * ∑ k : Fin (N + 1), HRS.Whole.projMean μ (fh i) (ω k) := fun i => by
      rw [hTeapp]; simp only; rw [hcomp, hgl]
    have h2 : ∀ j : Fin m, (Te ((Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ • ∑ k ∈ Finset.range (N + 1), ψ (ω k))).2 j =
        (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ * ∑ k : Fin (N + 1), HRS.Whole.projMean μ (u j) (ω k) := fun j => by
      rw [hTeapp]; simp only; rw [hcomp, hgr]
    refine Prod.ext (funext fun i => (h1 i)) ?_
    simp only [hgm, h2, hdg, s21g2_s12_restr]
    rw [Fin.sum_univ_eq_sum_range (fun k => HRS.Whole.r2FiniteRankKernel c u (ω k) (ω k)) (N + 1)]
  have hT1 := s21g2_s12_transfer μ (fun N => N + 1) (fun N => s21g2_s12_Fhat μ fh c u (N + 1))
    (fun N => (s21g2_s12_Fhat_measurable (Nat.succ_pos N) μ hfhm
      (fun i => (hfh2 i).integrable one_le_two) hu.symm huT).aemeasurable) hS2
  have hT2 : TendstoInDistribution (fun N => s21g2_s12_Fhat μ f c u (N + 1)) atTop
      (fun ω => gm (Te (ZE ω), ∫ x, dg x ∂μ)) (fun N => Measure.pi fun _ : Fin (N + 1) => μ) P' := by
    refine TendstoInDistribution.congr (fun N => ?_) (ae_of_all _ fun _ => rfl) hT1
    have hae : ∀ᵐ X ∂(Measure.pi fun _ : Fin (N + 1) => μ), ∀ (i : Fin n) (k : Fin (N + 1)), f i (X k) = fh i (X k) := by
      rw [ae_all_iff]; intro i
      rw [ae_all_iff]; intro k
      exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin (N + 1) => μ) k).ae (hfae i)
    filter_upwards [hae] with X hX
    refine Prod.ext (funext fun i => ?_) rfl
    show HRS.Whole.r2EmpDistr μ X (fh i) = HRS.Whole.r2EmpDistr μ X (f i)
    unfold HRS.Whole.r2EmpDistr
    rw [s21g2_s12_pair_emp, s21g2_s12_pair_emp]
    simp only [hX i]
    rw [show HRS.Whole.pair μ (f i) = HRS.Whole.pair μ (fh i) from integral_congr_ae (hfae i)]
  have h0 : AEMeasurable (s21g2_s12_Fhat μ f c u 0) (Measure.pi fun _ : Fin 0 => μ) :=
    (Subsingleton.measurable).aemeasurable
  have hT3 := s21g2_s12_shift_out (Ω := fun N => Fin N → HRS.Euc d) (P := fun N => Measure.pi fun _ : Fin N => μ)
    (F := fun N => s21g2_s12_Fhat μ f c u N) h0 hT2
  set Φ : ((Fin n → ℝ) × (Fin m → ℝ)) → (Fin n → ℝ) × ℝ := fun z =>
    (z.1, (1 / 2) * ∑ i, ∑ j, c i j * (z.2 i * z.2 j - HRS.Whole.pair μ (fun x => u i x * u j x))) with hΦdef
  have hΦm : Measurable Φ := by
    refine Measurable.prodMk measurable_fst ?_
    refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
    exact measurable_const.mul (((measurable_pi_apply i).comp measurable_snd).mul
      ((measurable_pi_apply j).comp measurable_snd) |>.sub measurable_const)
  have hlimeq : (fun ω => gm (Te (ZE ω), ∫ x, dg x ∂μ)) = fun ω => Φ (Tv (Zv ω)) := by
    funext ω
    refine Prod.ext rfl ?_
    show (1 / 2) * ∑ i, ∑ j, c i j * (Tv (Zv ω)).2 i * (Tv (Zv ω)).2 j - (1 / 2) * ∫ x, dg x ∂μ =
      (1 / 2) * ∑ i, ∑ j, c i j * ((Tv (Zv ω)).2 i * (Tv (Zv ω)).2 j -
        HRS.Whole.pair μ (fun x => u i x * u j x))
    have : ∀ i j, c i j * ((Tv (Zv ω)).2 i * (Tv (Zv ω)).2 j - HRS.Whole.pair μ (fun x => u i x * u j x)) =
        c i j * (Tv (Zv ω)).2 i * (Tv (Zv ω)).2 j - c i j * HRS.Whole.pair μ (fun x => u i x * u j x) :=
      fun i j => by ring
    simp_rw [this, Finset.sum_sub_distrib]
    rw [hc0]; ring
  rw [hlimeq] at hT3
  exact s21g2_s12_retarget (Z := fun ω => Tv (Zv ω)) (Tv.continuous.measurable.comp hZm).aemeasurable hΦm
    ((P'.map Zv).map Tv) hGeq hT3

end HRS.MS.R26T3
