import HRS.MS.S81w2Grad

/-!
# S8.1 (worker S81W2): `s81w2_grad_closure` (see `S81w2Grad`)
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators ContDiff InnerProductSpace

namespace HRS.Whole.S81W2

open HRS HRS.Whole HRS.MS.S88Breakdown HRS.MS.MovDec

variable {d : ℕ}

theorem s81w2_projMean_idem {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {f : Euc d → ℝ}
    (hf : MemLp f 2 μ) : projMean μ (projMean μ f) = projMean μ f := by
  funext x
  have h1 : Integrable f μ := hf.integrable (by norm_num)
  show (f x - pair μ f) - ∫ y, (f y - pair μ f) ∂μ = f x - pair μ f
  rw [integral_sub h1 (integrable_const _), integral_const]
  simp [pair]

theorem s81w2_mul_exp_le {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) :
    x * Real.exp (-t * x) ^ 2 ≤ 1 / (2 * t) := by
  have h1 : Real.exp (-t * x) ^ 2 = Real.exp (-(2 * t * x)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h2 := Real.add_one_le_exp (2 * t * x)
  have h3 : 0 < Real.exp (-(2 * t * x)) := Real.exp_pos _
  have h4 : Real.exp (2 * t * x) * Real.exp (-(2 * t * x)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [h1, le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right (show 2 * t * x ≤ Real.exp (2 * t * x) by linarith) h3.le]

section Main

variable {a β : ℝ} {ρ : Euc d → ℝ} {e : ℕ → Euc d → ℝ} {om : ℕ → ℝ} {m : ℝ}

set_option maxHeartbeats 3200000 in
theorem s81w2_grad_closure (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) (hm : (wholeSpaceIndex d : ℝ) ≤ m)
    (hdata : IsSpectralData d β ρ e om) (hcoef : S81W2Coef d a β ρ e om m)
    (α : MultiIndex d) {t : ℝ} (ht : 0 < t) :
    Summable (fun l => om l * (Real.exp (-t * om l) * u11Coef d β ρ e m α l) ^ 2) ∧
    ∀ L : ℕ, Integrable (fun x => ‖gradient (s88Orbit (critCoeff d a β ρ) m t α) x -
        ∑ l ∈ Finset.range L, (Real.exp (-t * om l) * u11Coef d β ρ e m α l) • gradient (e l) x‖ ^ 2)
          (withDensityReal ρ) ∧
      ∫ x, ‖gradient (s88Orbit (critCoeff d a β ρ) m t α) x -
        ∑ l ∈ Finset.range L, (Real.exp (-t * om l) * u11Coef d β ρ e m α l) • gradient (e l) x‖ ^ 2
          ∂(withDensityReal ρ) =
        ∑' l, om (l + L) * (Real.exp (-t * om (l + L)) * u11Coef d β ρ e m α (l + L)) ^ 2 := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  obtain ⟨hρ', -, -⟩ := mov2e_thermal hd hs0 hsd hβ ha hρ
  have hpos : ∀ x, 0 < ρ x := hρ'.pos
  have hρs : ContDiff ℝ ∞ ρ := hρ'.data.smooth
  haveI : IsProbabilityMeasure (withDensityReal ρ) := Q34.isProbabilityMeasure_nu hρ'.prob
  set μ := withDensityReal ρ with hμ
  have hreg := s88_regular_orbit hd a β ha hβ m hm ρ hρ
  obtain ⟨S, hSsum, hSz, hSrec⟩ := s81w2_synth hd ha hβ hρ hdata
  set c : ℕ → ℝ := fun l => Real.exp (-t * om l) * u11Coef d β ρ e m α l with hc
  -- coefficient vectors
  have hz : ∀ s : ℝ, 0 ≤ s → ∃ z : SeqL2,
      (∀ l, SeqL2.coord z l = Real.exp (-s * om l) * u11Coef d β ρ e m α l) ∧
      (fun x => (S z : Lp ℝ 2 μ) x) =ᵐ[μ] projMean μ (s88Orbit (critCoeff d a β ρ) m s α) := by
    intro s hs
    have hfm : MemLp (s88Orbit (critCoeff d a β ρ) m s α) 2 μ :=
      s81w2_memLp_of_memCb (hreg.memCb α s hs)
    obtain ⟨z, hz1, hz2⟩ := hSrec _ (HRS.MS.S111X2.s111x2_memL2Zero_projMean hfm)
    refine ⟨z, fun l => ?_, hz2⟩
    rw [hz1 l, ← hcoef α s hs l]
    unfold s81w2_coef
    rw [show projMean (withDensityReal ρ) (projMean (withDensityReal ρ)
      (s88Orbit (critCoeff d a β ρ) m s α)) = projMean (withDensityReal ρ)
      (s88Orbit (critCoeff d a β ρ) m s α) from s81w2_projMean_idem hfm]
  -- summability
  have hsa : Summable (fun l => (u11Coef d β ρ e m α l) ^ 2) := by
    obtain ⟨z0, hz0, -⟩ := hz 0 le_rfl
    have := lp.summable_inner (𝕜 := ℝ) (z0 : lp (fun _ : ℕ => ℝ) 2) (z0 : lp (fun _ : ℕ => ℝ) 2)
    refine this.congr fun l => ?_
    have h1 := hz0 l
    simp only [neg_zero, zero_mul, Real.exp_zero, one_mul] at h1
    show inner ℝ (SeqL2.coord z0 l) (SeqL2.coord z0 l) = _
    rw [h1]; simp [sq]
  have hsumom : Summable (fun l => om l * c l ^ 2) := by
    refine Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_) (hsa.mul_left (1 / (2 * t)))
    · exact mul_nonneg (hdata.pos l).le (sq_nonneg _)
    · simp only [hc, mul_pow]
      have := s81w2_mul_exp_le ht (hdata.pos l).le
      calc om l * (Real.exp (-t * om l) ^ 2 * u11Coef d β ρ e m α l ^ 2)
          = (om l * Real.exp (-t * om l) ^ 2) * u11Coef d β ρ e m α l ^ 2 := by ring
        _ ≤ 1 / (2 * t) * u11Coef d β ρ e m α l ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
  -- the vector family
  have hgm : ∀ l, MemLp (fun x => gradient (e l) x) 2 μ := fun l =>
    s81w2_grad_memLp (hdata.smooth l) (hdata.grad_int l l)
  set g : ℕ → Lp (Euc d) 2 μ := fun l => (hgm l).toLp (fun x => gradient (e l) x) with hgdef
  have hg : ∀ l k, inner ℝ (g l) (g k) = if l = k then om l else 0 := by
    intro l k
    rw [L2.inner_def]
    have : ∫ x, inner ℝ ((g l : Lp (Euc d) 2 μ) x) ((g k : Lp (Euc d) 2 μ) x) ∂μ =
        ∫ x, inner ℝ (gradient (e l) x) (gradient (e k) x) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [(hgm l).coeFn_toLp, (hgm k).coeFn_toLp] with x h1 h2
      rw [h1, h2]
    rw [this]
    exact hdata.grad_orth l k
  obtain ⟨Ĝ, hGsum, htail⟩ := s81w2_orth_sum g om (fun l => hdata.pos l) hg c hsumom
  -- the orbit at time `t`
  obtain ⟨zt, hztc, hztS⟩ := hz t ht.le
  set f := s88Orbit (critCoeff d a β ρ) m t α with hf
  have hfC := hreg.memCb α t ht.le
  have hf2 : ContDiff ℝ 2 f := hfC.1
  have hfm : MemLp f 2 μ := s81w2_memLp_of_memCb hfC
  set h : Euc d → ℝ := projMean μ f with hh
  have hh1 : ContDiff ℝ 1 h := (hf2.of_le (by norm_num)).sub contDiff_const
  have hhm : MemLp h 2 μ := hfm.sub (memLp_const _)
  have hDh : ∀ x v, fderiv ℝ h x v = fderiv ℝ f x v := fun x v => by
    show fderiv ℝ (fun y => f y - pair μ f) x v = _
    rw [fderiv_sub_const]
  -- scalar partial sums
  have hep : ∀ l, MemLp (e l) 2 μ := fun l => (hdata.centered l).1
  set F : ℕ → Euc d → ℝ := fun L x => ∑ l ∈ Finset.range L, c l • e l x with hFdef
  have hsc := fun L => s81w2_partial (μ := μ) e hep c L
  have hFm : ∀ L, MemLp (F L) 2 μ := fun L => (hsc L).choose
  have hFs : ∀ L, ContDiff ℝ 1 (F L) := by
    intro L
    refine ContDiff.sum fun l _ => ?_
    have h1 : ContDiff ℝ 1 (e l) := (hdata.smooth l).of_le (by exact_mod_cast le_top)
    exact h1.const_smul (c l)
  have hconvF : Tendsto (fun L => (hFm L).toLp (F L)) atTop (𝓝 (hhm.toLp h)) := by
    have h1 := (hSsum zt).tendsto_sum_nat
    have hS : S zt = hhm.toLp h := Lp.ext (hztS.trans hhm.coeFn_toLp.symm)
    have hseq : (fun L => (hFm L).toLp (F L)) = fun L => ∑ l ∈ Finset.range L,
        SeqL2.coord zt l • (((hdata.centered l).1).toLp (e l) : Lp ℝ 2 μ) := by
      funext L
      rw [(hsc L).choose_spec]
      exact Finset.sum_congr rfl fun l _ => by rw [hztc l]
    rw [hseq, ← hS]
    exact h1
  -- vector partial sums
  have hgs := fun L => s81w2_partial (E := Euc d) (μ := μ) (fun l x => gradient (e l) x) hgm c L
  set Gp : ℕ → Euc d → Euc d := fun L x => ∑ l ∈ Finset.range L, c l • gradient (e l) x with hGpdef
  have hGpm : ∀ L, MemLp (Gp L) 2 μ := fun L => (hgs L).choose
  have hGpeq : ∀ L, (hGpm L).toLp (Gp L) = ∑ l ∈ Finset.range L, c l • g l := fun L =>
    (hgs L).choose_spec
  -- the directional identification
  have hdir : ∀ v : Euc d, ∀ᵐ x ∂μ, (ContinuousLinearMap.compLpL 2 μ (innerSL ℝ v) Ĝ : Lp ℝ 2 μ) x =
      fderiv ℝ f x v := by
    intro v
    set Φ : Lp (Euc d) 2 μ →L[ℝ] Lp ℝ 2 μ := ContinuousLinearMap.compLpL 2 μ (innerSL ℝ v) with hΦ
    have hDF : ∀ L x, fderiv ℝ (F L) x v = inner ℝ v (Gp L x) := by
      intro L x
      have hdiff : ∀ l ∈ Finset.range L, DifferentiableAt ℝ (fun y => c l • e l y) x := fun l _ =>
        (((hdata.smooth l).differentiable (by simp)).differentiableAt).const_smul (c l)
      have h1 : fderiv ℝ (F L) x = ∑ l ∈ Finset.range L, c l • fderiv ℝ (e l) x := by
        simp only [hFdef]
        rw [fderiv_fun_sum hdiff]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [fderiv_fun_const_smul (((hdata.smooth l).differentiable (by simp)).differentiableAt)]
      rw [h1]
      simp only [hGpdef, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, inner_sum,
        inner_smul_right, s81w2_inner_gradient, smul_eq_mul]
    have hDm : ∀ L, MemLp (fun x => fderiv ℝ (F L) x v) 2 μ := by
      intro L
      have := (innerSL ℝ v).comp_memLp' (hGpm L)
      exact MemLp.ae_eq (Filter.Eventually.of_forall fun x => by simp [hDF L x]) this
    have hGm : MemLp (fun x => (Φ Ĝ : Lp ℝ 2 μ) x) 2 μ := Lp.memLp _
    have hDhm : MemLp (fun x => fderiv ℝ h x v) 2 μ := by
      obtain ⟨B, hB⟩ := hfC.2 1 (by norm_num)
      have hcont : Continuous fun x => fderiv ℝ h x v :=
        (hh1.continuous_fderiv (by norm_num)).clm_apply continuous_const
      refine MemLp.of_bound hcont.aestronglyMeasurable (B * ‖v‖) (Filter.Eventually.of_forall fun x => ?_)
      have h1 : ‖fderiv ℝ f x‖ ≤ B := by
        have := hB ⟨x, rfl⟩
        simpa using this
      rw [hDh]
      calc ‖fderiv ℝ f x v‖ ≤ ‖fderiv ℝ f x‖ * ‖v‖ := (fderiv ℝ f x).le_opNorm v
        _ ≤ B * ‖v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have hconvD : Tendsto (fun L => (hDm L).toLp (fun x => fderiv ℝ (F L) x v)) atTop
        (𝓝 (hGm.toLp (fun x => (Φ Ĝ : Lp ℝ 2 μ) x))) := by
      have hseq : (fun L => (hDm L).toLp (fun x => fderiv ℝ (F L) x v)) =
          fun L => Φ (∑ l ∈ Finset.range L, c l • g l) := by
        funext L
        refine Lp.ext ?_
        have hT : ((hGpm L).toLp (Gp L) : Lp (Euc d) 2 μ) = ∑ l ∈ Finset.range L, c l • g l :=
          hGpeq L
        filter_upwards [(hDm L).coeFn_toLp,
          ContinuousLinearMap.coeFn_compLpL (innerSL ℝ v) (∑ l ∈ Finset.range L, c l • g l),
          (hGpm L).coeFn_toLp] with x h1 h2 h3
        rw [h1, hΦ, h2, ← hT, h3, hDF L x]
        simp
      rw [hseq, Lp.toLp_coeFn]
      exact (Φ.continuous.tendsto Ĝ).comp hGsum.tendsto_sum_nat
    have hw := s81w2_weak_ident hρs hpos F hFs hFm hh1 hhm v hDm hGm hDhm hconvF hconvD
    filter_upwards [hw] with x hx
    rw [hx, hDh]
  -- `Ĝ = ∇ f`
  have hGeq : (fun x => (Ĝ : Lp (Euc d) 2 μ) x) =ᵐ[μ] fun x => gradient f x := by
    have hall : ∀ᵐ x ∂μ, ∀ i : Fin d, inner ℝ (EuclideanSpace.single i (1 : ℝ)) ((Ĝ : Lp (Euc d) 2 μ) x) =
        inner ℝ (EuclideanSpace.single i (1 : ℝ)) (gradient f x) := by
      rw [ae_all_iff]
      intro i
      filter_upwards [hdir (EuclideanSpace.single i (1 : ℝ)),
        ContinuousLinearMap.coeFn_compLpL (innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) Ĝ] with x h1 h2
      rw [s81w2_inner_gradient, ← h1, h2]
      simp
    filter_upwards [hall] with x hx
    ext i
    have := hx i
    rw [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left] at this
    simpa using this
  -- the tails
  refine ⟨hsumom, fun L => ?_⟩
  have hu : ((Ĝ - ∑ l ∈ Finset.range L, c l • g l : Lp (Euc d) 2 μ) : Euc d → Euc d) =ᵐ[μ]
      fun x => gradient f x - Gp L x := by
    have hT : ((hGpm L).toLp (Gp L) : Lp (Euc d) 2 μ) = ∑ l ∈ Finset.range L, c l • g l := hGpeq L
    filter_upwards [Lp.coeFn_sub Ĝ (∑ l ∈ Finset.range L, c l • g l), hGeq, (hGpm L).coeFn_toLp] with
      x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, ← hT, h3]
  set U : Lp (Euc d) 2 μ := Ĝ - ∑ l ∈ Finset.range L, c l • g l with hU
  have hint : Integrable (fun x => ‖(U : Euc d → Euc d) x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable U)).1 (Lp.memLp U)
  have hnorm : ‖U‖ ^ 2 = ∫ x, ‖(U : Euc d → Euc d) x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact real_inner_self_eq_norm_sq _
  refine ⟨hint.congr (by filter_upwards [hu] with x hx; rw [hx]), ?_⟩
  rw [← htail L, hnorm]
  refine integral_congr_ae ?_
  filter_upwards [hu] with x hx
  rw [hx]

end Main

end HRS.Whole.S81W2
