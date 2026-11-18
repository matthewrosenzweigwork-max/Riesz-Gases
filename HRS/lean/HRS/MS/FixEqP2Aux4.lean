import HRS.MS.FixEqP2Aux3

/-!
# S5.7 `fixed_equation` (worker S57P), part 7: linearity of the generator of `fixedEqCoeff` and commutation with integrals

`S57pLin C T`: `generatorW C τ` is additive on bounded `C^3` functions (`sub`) and commutes with `u`-integrals of families
bounded in `C^4` with jets continuous in `u` (`comm`).  For `fixedEqCoeff` this is the linearity of the local part and Fubini
for the cancellation-convention convolution of the nonlocal part.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go

variable {d : ℕ}

/-- linearity facts of a generator -/
structure S57pLin (C : WholeCoeff d) (T : ℝ) : Prop where
  sub : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ (B : ℝ) (u₁ u₂ : Euc d → ℝ), ContDiff ℝ 3 u₁ → ContDiff ℝ 3 u₂ →
    (∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i u₁ x‖ ≤ B) → (∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i u₂ x‖ ≤ B) → ∀ x,
    generatorW C τ (fun y => u₁ y - u₂ y) x = generatorW C τ u₁ x - generatorW C τ u₂ x
  comm : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ (a b B : ℝ), 0 ≤ B → a ≤ b → ∀ F : ℝ → Euc d → ℝ,
    (∀ u ∈ Set.Ioc a b, ContDiff ℝ 4 (F u) ∧ ∀ i ≤ 4, ∀ y, ‖iteratedFDeriv ℝ i (F u) y‖ ≤ B) →
    (∀ i ≤ 3, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (F p.1) p.2) (Set.Ioc a b ×ˢ Set.univ)) → ∀ x,
    generatorW C τ (fun y => ∫ u in a..b, F u y) x = ∫ u in a..b, generatorW C τ (F u) x

theorem s57p_conv_eq (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c : ℝ} (hc : 0 ≤ c)
    {f : Euc d → ℝ} (hf : RgDecay 2 (fun _ => c) f) (x : Euc d) (j : Fin d) :
    (convGradConvW (rieszKernelGrad d s) f x) j = rgT (fun z => (rieszKernelGrad d s z) j) f x := by
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨h2, h0, h1, -⟩ := rg_decay_parts (n := 2) le_rfl (a := fun _ => c) (fun _ => hc) hf
  exact rg_force_comp hd hs0 hsd (h2.differentiable (by norm_num)) hc hc h0 (fun y => (h1 y).trans (by
      calc c * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ c * 1 := mul_le_mul_of_nonneg_left (hw y) hc
        _ = c := mul_one _)) x j

theorem s57p_rgT_sub (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ} {σ : ℝ}
    (hκ : RgKer d s σ κ) {c : ℝ} (hc : 0 ≤ c) {f₁ f₂ : Euc d → ℝ} (h₁ : RgDecay 2 (fun _ => c) f₁)
    (h₂ : RgDecay 2 (fun _ => c) f₂) (x : Euc d) :
    rgT κ (fun y => f₁ y - f₂ y) x = rgT κ f₁ x - rgT κ f₂ x := by
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have parts : ∀ {f : Euc d → ℝ}, RgDecay 2 (fun _ => c) f → Differentiable ℝ f ∧
      (∀ y, ‖f y‖ ≤ c * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) ∧ (∀ y, ‖fderiv ℝ f y‖ ≤ c) := by
    intro f hf
    obtain ⟨h2, h0, h1, -⟩ := rg_decay_parts (n := 2) le_rfl (a := fun _ => c) (fun _ => hc) hf
    exact ⟨h2.differentiable (by norm_num), h0, fun y => (h1 y).trans (by
      calc c * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ c * 1 := mul_le_mul_of_nonneg_left (hw y) hc
        _ = c := mul_one _)⟩
  obtain ⟨d1, a1, b1⟩ := parts h₁
  obtain ⟨d2, a2, b2⟩ := parts h₂
  have i1 := rg_integrable hd hs0 hsd hκ d1 hc hc a1 b1 x
  have i2 := rg_integrable hd hs0 hsd hκ d2 hc hc a2 b2 x
  unfold rgT
  rw [← integral_sub i1 i2]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [rgR]
  split_ifs <;> simp <;> ring

theorem s57p_lin_sub {s : ℝ} (M Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} {c : ℝ → Euc d → Euc d}
    {ρ : ℝ → Euc d → ℝ} {T : ℝ} (hD : S57pFeData s Q ν c ρ T) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T)
    {B : ℝ} {u₁ u₂ : Euc d → ℝ} (h₁ : ContDiff ℝ 3 u₁) (h₂ : ContDiff ℝ 3 u₂)
    (b₁ : ∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i u₁ x‖ ≤ B) (b₂ : ∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i u₂ x‖ ≤ B)
    (x : Euc d) :
    generatorW (fixedEqCoeff s M Q ν c ρ) τ (fun y => u₁ y - u₂ y) x =
      generatorW (fixedEqCoeff s M Q ν c ρ) τ u₁ x - generatorW (fixedEqCoeff s M Q ν c ρ) τ u₂ x := by
  obtain ⟨A, hA, hdec, -⟩ := hD.rho
  have hMB := s55f_matBound M
  have hMB0 : 0 ≤ ∑ i, ∑ j, |M i j| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (b₁ 0 (by norm_num) 0)
  have hρ2 : RgDecay 2 (fun _ => A) (ρ τ) := rg_decay_mono (by norm_num) (hdec τ hτ)
  have h1' : ContDiff ℝ 1 u₁ := h₁.of_le (by norm_num)
  have h2' : ContDiff ℝ 1 u₂ := h₂.of_le (by norm_num)
  have hdiffc : ContDiff ℝ 3 (fun y => u₁ y - u₂ y) := h₁.sub h₂
  have hdb : ∀ i ≤ 3, ∀ y, ‖iteratedFDeriv ℝ i (fun y => u₁ y - u₂ y) y‖ ≤ B + B := by
    intro i hi y
    have e : iteratedFDeriv ℝ i (fun y => u₁ y - u₂ y) y = iteratedFDeriv ℝ i u₁ y - iteratedFDeriv ℝ i u₂ y :=
      iteratedFDeriv_sub_apply ((h₁.of_le (by exact_mod_cast hi)).contDiffAt) ((h₂.of_le (by exact_mod_cast hi)).contDiffAt)
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add (b₁ i hi y) (b₂ i hi y))
  show ν * Laplacian.laplacian (fun y => u₁ y - u₂ y) x +
      inner ℝ (-(Torus.matVec Q x) + c τ x) (gradient (fun y => u₁ y - u₂ y) x) -
      ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ τ y * (Torus.matVec M.transpose (gradient (fun y => u₁ y - u₂ y) y)) j) x) j =
    (ν * Laplacian.laplacian u₁ x + inner ℝ (-(Torus.matVec Q x) + c τ x) (gradient u₁ x) -
      ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ τ y * (Torus.matVec M.transpose (gradient u₁ y)) j) x) j) -
    (ν * Laplacian.laplacian u₂ x + inner ℝ (-(Torus.matVec Q x) + c τ x) (gradient u₂ x) -
      ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ τ y * (Torus.matVec M.transpose (gradient u₂ y)) j) x) j)
  have hlap : Laplacian.laplacian (fun y => u₁ y - u₂ y) x =
      Laplacian.laplacian u₁ x - Laplacian.laplacian u₂ x :=
    ((h₁.of_le (by norm_num : ((2 : ℕ) : WithTop ℕ∞) ≤ 3)).contDiffAt (x := x)).laplacian_sub
      ((h₂.of_le (by norm_num : ((2 : ℕ) : WithTop ℕ∞) ≤ 3)).contDiffAt (x := x))
  have hgr : ∀ y, gradient (fun y => u₁ y - u₂ y) y = gradient u₁ y - gradient u₂ y := fun y =>
    HRS.MS.Fcau.fcau_gradient_sub h1' h2' y
  have hnl : ∀ j : Fin d, (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ τ y * (Torus.matVec M.transpose (gradient (fun y => u₁ y - u₂ y) y)) j) x) j =
      (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ τ y * (Torus.matVec M.transpose (gradient u₁ y)) j) x) j -
      (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ τ y * (Torus.matVec M.transpose (gradient u₂ y)) j) x) j := by
    intro j
    have hc0 : 0 ≤ 2 ^ 2 * A * ((d : ℝ) * (∑ i, ∑ j, |M i j|) * (B + B)) := by positivity
    have hd1 : RgDecay 2 (fun _ => 2 ^ 2 * A * ((d : ℝ) * (∑ i, ∑ j, |M i j|) * (B + B)))
        (fun y => ρ τ y * (Torus.matVec M.transpose (gradient u₁ y)) j) :=
      s55m_nl_decay hMB hMB0 hA (by positivity) hρ2 h₁ (fun n hn x => (b₁ n hn x).trans (by linarith)) j
    have hd2 : RgDecay 2 (fun _ => 2 ^ 2 * A * ((d : ℝ) * (∑ i, ∑ j, |M i j|) * (B + B)))
        (fun y => ρ τ y * (Torus.matVec M.transpose (gradient u₂ y)) j) :=
      s55m_nl_decay hMB hMB0 hA (by positivity) hρ2 h₂ (fun n hn x => (b₂ n hn x).trans (by linarith)) j
    have hd3 : RgDecay 2 (fun _ => 2 ^ 2 * A * ((d : ℝ) * (∑ i, ∑ j, |M i j|) * (B + B)))
        (fun y => ρ τ y * (Torus.matVec M.transpose (gradient (fun y => u₁ y - u₂ y) y)) j) :=
      s55m_nl_decay hMB hMB0 hA (by positivity) hρ2 hdiffc hdb j
    rw [s57p_conv_eq hD.hd hD.hs0 hD.hsd hc0 hd3, s57p_conv_eq hD.hd hD.hs0 hD.hsd hc0 hd1,
      s57p_conv_eq hD.hd hD.hs0 hD.hsd hc0 hd2]
    have hfun : (fun y => ρ τ y * (Torus.matVec M.transpose (gradient (fun y => u₁ y - u₂ y) y)) j) =
        fun y => ρ τ y * (Torus.matVec M.transpose (gradient u₁ y)) j -
          ρ τ y * (Torus.matVec M.transpose (gradient u₂ y)) j := by
      funext y
      rw [hgr y]
      simp only [Torus.matVec, map_sub, PiLp.sub_apply]; ring
    rw [hfun]
    exact s57p_rgT_sub hD.hd hD.hs0 hD.hsd (rgKerComp_ok hD.hs0 j) hc0 hd1 hd2 x
  rw [hlap, hgr x, inner_sub_right, Finset.sum_congr rfl fun j _ => hnl j, Finset.sum_sub_distrib]
  ring

/-! ### Commutation with integrals -/

theorem s57p_jet_integrable {a b B : ℝ} {F : ℝ → Euc d → ℝ} (j : ℕ)
    (hF : ∀ u ∈ Set.Ioc a b, ∀ y, ‖iteratedFDeriv ℝ j (F u) y‖ ≤ B)
    (hc : ∀ y, ContinuousOn (fun u => iteratedFDeriv ℝ j (F u) y) (Set.Ioc a b)) (y : Euc d) :
    Integrable (fun u => iteratedFDeriv ℝ j (F u) y) (volume.restrict (Set.Ioc a b)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := ⟨by simp⟩
  refine (integrable_const B).mono' ((hc y).aestronglyMeasurable measurableSet_Ioc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact hF u hu y

/-- the gradient as a continuous linear map of the first jet -/
def s57pLg (d : ℕ) : (Euc d [×1]→L[ℝ] ℝ) →L[ℝ] Euc d :=
  ∑ i : Fin d, (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) ℝ
    (fun _ => EuclideanSpace.single i (1 : ℝ))).smulRight (EuclideanSpace.single i (1 : ℝ))

theorem s57p_gradient_eq_Lg (f : Euc d → ℝ) (x : Euc d) :
    gradient f x = s57pLg d (iteratedFDeriv ℝ 1 f x) := by
  ext j
  simp only [s57pLg, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousMultilinearMap.apply_apply, PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul]
  rw [movtr_gradient_apply]
  rw [Finset.sum_eq_single j]
  · simp [iteratedFDeriv_one_apply]
  · intro i _ hij
    simp [EuclideanSpace.single_apply, hij.symm]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- the Laplacian as a continuous linear map of the second jet -/
def s57pLl (d : ℕ) : (Euc d [×2]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin d, ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ
    ![(EuclideanSpace.basisFun (Fin d) ℝ) i, (EuclideanSpace.basisFun (Fin d) ℝ) i]

theorem s57p_laplacian_eq_Ll (f : Euc d → ℝ) (x : Euc d) :
    Laplacian.laplacian f x = s57pLl d (iteratedFDeriv ℝ 2 f x) := by
  have := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := f)
    (EuclideanSpace.basisFun (Fin d) ℝ)) x
  simpa [s57pLl] using this

/-- jets that are continuous in the parameter for each point and Lipschitz in the point (uniformly) are jointly continuous -/
theorem s57p_jets_jointCont {S : Set ℝ} {B : ℝ} {F : ℝ → Euc d → ℝ} (i : ℕ)
    (hF : ∀ u ∈ S, ContDiff ℝ (i + 1 : ℕ) (F u) ∧ ∀ y, ‖iteratedFDeriv ℝ (i + 1) (F u) y‖ ≤ B)
    (hc : ∀ y, ContinuousOn (fun u => iteratedFDeriv ℝ i (F u) y) S) :
    ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (F p.1) p.2) (S ×ˢ Set.univ) := by
  intro p hp
  have hp1 : p.1 ∈ S := hp.1
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hB0 : 0 ≤ B := by
    have := (hF p.1 hp1).2 0
    exact le_trans (norm_nonneg _) this
  have h1 := (hc p.2 p.1 hp1)
  rw [ContinuousWithinAt, Metric.tendsto_nhds] at h1
  have e1 := h1 (ε / 2) (by positivity)
  have hδ : 0 < ε / (2 * (B + 1)) := by positivity
  have e2 : ∀ᶠ q in 𝓝[S ×ˢ Set.univ] p, dist q.2 p.2 < ε / (2 * (B + 1)) :=
    (tendsto_nhdsWithin_of_tendsto_nhds ((continuous_snd.tendsto p))).eventually (Metric.ball_mem_nhds _ hδ)
  have e3 : ∀ᶠ q in 𝓝[S ×ˢ Set.univ] p, q.1 ∈ S ∧ dist (iteratedFDeriv ℝ i (F q.1) p.2)
      (iteratedFDeriv ℝ i (F p.1) p.2) < ε / 2 := by
    have : Tendsto (fun q : ℝ × Euc d => q.1) (𝓝[S ×ˢ Set.univ] p) (𝓝[S] p.1) := by
      refine tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto p).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with q hq using hq.1
    filter_upwards [this.eventually e1, self_mem_nhdsWithin] with q hq1 hq2
    exact ⟨hq2.1, hq1⟩
  filter_upwards [e2, e3] with q hq2 hq3
  obtain ⟨hq1, hq3⟩ := hq3
  have hlip : ‖iteratedFDeriv ℝ i (F q.1) q.2 - iteratedFDeriv ℝ i (F q.1) p.2‖ ≤ B * ‖q.2 - p.2‖ := by
    have hd : Differentiable ℝ (iteratedFDeriv ℝ i (F q.1)) :=
      (hF q.1 hq1).1.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self i)
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := iteratedFDeriv ℝ i (F q.1)) (C := B)
      (s := Set.univ) (x := p.2) (y := q.2) (fun z _ => hd z) (fun z _ => by
        rw [norm_fderiv_iteratedFDeriv]; exact (hF q.1 hq1).2 z) convex_univ (Set.mem_univ _) (Set.mem_univ _)
  rw [dist_eq_norm] at hq3 ⊢
  have hq2' : ‖q.2 - p.2‖ < ε / (2 * (B + 1)) := by rwa [dist_eq_norm] at hq2
  calc ‖iteratedFDeriv ℝ i (F q.1) q.2 - iteratedFDeriv ℝ i (F p.1) p.2‖
      = ‖(iteratedFDeriv ℝ i (F q.1) q.2 - iteratedFDeriv ℝ i (F q.1) p.2) +
        (iteratedFDeriv ℝ i (F q.1) p.2 - iteratedFDeriv ℝ i (F p.1) p.2)‖ := by congr 1; abel
    _ ≤ B * ‖q.2 - p.2‖ + ε / 2 := (norm_add_le _ _).trans (add_le_add hlip hq3.le)
    _ < ε / 2 + ε / 2 := by
        have : B * ‖q.2 - p.2‖ < ε / 2 := by
          calc B * ‖q.2 - p.2‖ ≤ (B + 1) * ‖q.2 - p.2‖ := by nlinarith [norm_nonneg (q.2 - p.2)]
            _ < (B + 1) * (ε / (2 * (B + 1))) := mul_lt_mul_of_pos_left hq2' (by positivity)
            _ = ε / 2 := by field_simp
        linarith
    _ = ε := by ring

theorem s57p_decay_parts {c : ℝ} (hc : 0 ≤ c) {f : Euc d → ℝ} (hf : RgDecay 2 (fun _ => c) f) :
    Differentiable ℝ f ∧ (∀ y, ‖f y‖ ≤ c * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) ∧ (∀ y, ‖fderiv ℝ f y‖ ≤ c) := by
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨h2, h0, h1, -⟩ := rg_decay_parts (n := 2) le_rfl (a := fun _ => c) (fun _ => hc) hf
  exact ⟨h2.differentiable (by norm_num), h0, fun y => (h1 y).trans (by
    calc c * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ c * 1 := mul_le_mul_of_nonneg_left (hw y) hc
      _ = c := mul_one _)⟩

/-- Fubini for the cancellation-convention convolution -/
theorem s57p_rgT_integral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ} {σ : ℝ}
    (hκ : RgKer d s σ κ) {c : ℝ} (hc : 0 ≤ c) {a b : ℝ} (hab : a ≤ b) {K : ℝ → Euc d → ℝ}
    (hK : ∀ u ∈ Set.Ioc a b, RgDecay 2 (fun _ => c) (K u))
    (hKc : ContinuousOn (fun p : ℝ × Euc d => K p.1 p.2) (Set.Ioc a b ×ˢ Set.univ))
    {Kz : Euc d → ℝ} (hKz : ∀ y, Kz y = ∫ u in a..b, K u y) (x : Euc d) :
    Integrable (fun u => rgT κ (K u) x) (volume.restrict (Set.Ioc a b)) ∧
    rgT κ Kz x = ∫ u in a..b, rgT κ (K u) x := by
  simp only [intervalIntegral.integral_of_le hab] at hKz ⊢
  set μ : Measure ℝ := volume.restrict (Set.Ioc a b) with hμ
  haveI : IsFiniteMeasure μ := ⟨by simp [hμ]⟩
  have hae : ∀ᵐ u ∂μ, u ∈ Set.Ioc a b := by rw [hμ]; exact ae_restrict_mem measurableSet_Ioc
  -- the integrand
  set f : Euc d → ℝ → ℝ := fun z u => κ z • rgR (K u) x z with hf
  have hfsplit : ∀ z u, f z u = κ z * (K u (x - z) - (if ‖z‖ ≤ 1 / 4 then K u x else 0)) := by
    intro z u
    simp only [hf, rgR]
    split_ifs <;> simp [smul_eq_mul]
  have hKbound : ∀ u ∈ Set.Ioc a b, ∀ y, |K u y| ≤ c := by
    intro u hu y
    obtain ⟨-, h0, -⟩ := s57p_decay_parts hc (hK u hu)
    have hw : (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have := h0 y
    rw [Real.norm_eq_abs] at this
    exact this.trans (by nlinarith)
  have hKu_c : ∀ y, ContinuousOn (fun u => K u y) (Set.Ioc a b) := by
    intro y
    have : ContinuousOn (fun u : ℝ => ((u, y) : ℝ × Euc d)) (Set.Ioc a b) :=
      (continuous_id.prodMk continuous_const).continuousOn
    exact hKc.comp this (fun u hu => ⟨hu, Set.mem_univ _⟩)
  have hKu_int : ∀ y, Integrable (fun u => K u y) μ := by
    intro y
    refine (integrable_const c).mono' ((hKu_c y).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [hae] with u hu
    rw [Real.norm_eq_abs]; exact hKbound u hu y
  -- pointwise identity
  have hpt : ∀ z, ∫ u, f z u ∂μ = κ z • rgR Kz x z := by
    intro z
    have e1 : rgR Kz x z = ∫ u, rgR (K u) x z ∂μ := by
      simp only [rgR]
      split_ifs
      · rw [hKz, hKz, integral_sub (hKu_int _) (hKu_int _)]
      · rw [hKz]
    rw [e1, ← integral_smul]
  -- measurability on the product
  have hprod : (volume : Measure (Euc d)).prod μ = ((volume : Measure (Euc d)).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ Set.Ioc a b) := by
    rw [hμ, ← Measure.prod_restrict, Measure.restrict_univ]
  have hG1 : AEStronglyMeasurable (fun p : Euc d × ℝ => K p.2 (x - p.1)) ((volume : Measure (Euc d)).prod μ) := by
    rw [hprod]
    refine ContinuousOn.aestronglyMeasurable ?_ (MeasurableSet.univ.prod measurableSet_Ioc)
    have : ContinuousOn (fun p : Euc d × ℝ => ((p.2, x - p.1) : ℝ × Euc d)) (Set.univ ×ˢ Set.Ioc a b) :=
      ((continuous_snd.prodMk (continuous_const.sub continuous_fst))).continuousOn
    exact hKc.comp this (fun p hp => ⟨hp.2, Set.mem_univ _⟩)
  have hG2 : AEStronglyMeasurable (fun p : Euc d × ℝ => (if ‖p.1‖ ≤ 1 / 4 then K p.2 x else 0))
      ((volume : Measure (Euc d)).prod μ) := by
    have hG : AEStronglyMeasurable (fun p : Euc d × ℝ => K p.2 x) ((volume : Measure (Euc d)).prod μ) := by
      rw [hprod]
      refine ContinuousOn.aestronglyMeasurable ?_ (MeasurableSet.univ.prod measurableSet_Ioc)
      exact (hKu_c x).comp continuous_snd.continuousOn (fun p hp => hp.2)
    have : (fun p : Euc d × ℝ => (if ‖p.1‖ ≤ 1 / 4 then K p.2 x else 0)) =
        Set.indicator {p : Euc d × ℝ | ‖p.1‖ ≤ 1 / 4} (fun p => K p.2 x) := by
      funext p; simp [Set.indicator_apply]
    rw [this]
    exact hG.indicator (measurableSet_le continuous_fst.norm.measurable measurable_const)
  have hκm : AEStronglyMeasurable (fun p : Euc d × ℝ => κ p.1) ((volume : Measure (Euc d)).prod μ) :=
    (hκ.meas.comp measurable_fst).aestronglyMeasurable
  have hfm : AEStronglyMeasurable (Function.uncurry f) ((volume : Measure (Euc d)).prod μ) := by
    have : Function.uncurry f = fun p : Euc d × ℝ => κ p.1 * (K p.2 (x - p.1) - (if ‖p.1‖ ≤ 1 / 4 then K p.2 x else 0)) := by
      funext p; exact hfsplit p.1 p.2
    rw [this]
    exact hκm.mul (hG1.sub hG2)
  -- integrability on the product
  have hmaj_int := rg_maj_integrable hd hsd σ c c x
  have hfint : Integrable (Function.uncurry f) ((volume : Measure (Euc d)).prod μ) := by
    rw [integrable_prod_iff hfm]
    have hbd : ∀ᵐ z : Euc d, ∀ u ∈ Set.Ioc a b, ‖f z u‖ ≤ rgMaj d s σ c c x z := by
      filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz u hu
      obtain ⟨hdf, h0, h1⟩ := s57p_decay_parts hc (hK u hu)
      exact rg_norm_le hs0 hκ hdf hc hc h0 h1 x z hz
    have hfu_meas : ∀ z, AEStronglyMeasurable (fun u => f z u) μ := by
      intro z
      have : (fun u => f z u) = fun u => κ z * (K u (x - z) - (if ‖z‖ ≤ 1 / 4 then K u x else 0)) :=
        funext (hfsplit z)
      rw [this]
      refine aestronglyMeasurable_const.mul ((hKu_c _).aestronglyMeasurable measurableSet_Ioc |>.sub ?_)
      split_ifs
      · exact (hKu_c x).aestronglyMeasurable measurableSet_Ioc
      · exact aestronglyMeasurable_const
    refine ⟨?_, ?_⟩
    · filter_upwards [hbd] with z hz
      refine (integrable_const (rgMaj d s σ c c x z)).mono' (hfu_meas z) ?_
      filter_upwards [hae] with u hu using hz u hu
    · refine ((hmaj_int.mul_const (μ.real Set.univ)).mono' ?_ ?_)
      · exact hfm.norm.integral_prod_right'
      · filter_upwards [hbd] with z hz
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun u => norm_nonneg _)]
        have hI : Integrable (fun u => ‖f z u‖) μ := by
          refine (integrable_const (rgMaj d s σ c c x z)).mono' (hfu_meas z).norm ?_
          filter_upwards [hae] with u hu
          rw [norm_norm]; exact hz u hu
        calc ∫ u, ‖f z u‖ ∂μ ≤ ∫ u, rgMaj d s σ c c x z ∂μ := by
              refine integral_mono_ae hI (integrable_const _) ?_
              filter_upwards [hae] with u hu using hz u hu
          _ = rgMaj d s σ c c x z * μ.real Set.univ := by simp [mul_comm]
  have hsw := integral_integral_swap (μ := (volume : Measure (Euc d))) (ν := μ) hfint
  unfold rgT
  refine ⟨hfint.integral_prod_right, ?_⟩
  calc ∫ z, κ z • rgR Kz x z = ∫ z, ∫ u, f z u ∂μ := by simp_rw [hpt]
    _ = ∫ u, ∫ z, f z u ∂volume ∂μ := hsw
    _ = ∫ u, ∫ z, κ z • rgR (K u) x z ∂volume ∂μ := rfl

theorem s57p_lin_comm {s : ℝ} (M Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} {c : ℝ → Euc d → Euc d}
    {ρ : ℝ → Euc d → ℝ} {T : ℝ} (hD : S57pFeData s Q ν c ρ T) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T)
    {a b B : ℝ} (hB0 : 0 ≤ B) (hab : a ≤ b) {F : ℝ → Euc d → ℝ}
    (hF : ∀ u ∈ Set.Ioc a b, ContDiff ℝ 4 (F u) ∧ ∀ i ≤ 4, ∀ y, ‖iteratedFDeriv ℝ i (F u) y‖ ≤ B)
    (hjc : ∀ i ≤ 3, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (F p.1) p.2) (Set.Ioc a b ×ˢ Set.univ))
    (x : Euc d) :
    generatorW (fixedEqCoeff s M Q ν c ρ) τ (fun y => ∫ u in a..b, F u y) x =
      ∫ u in a..b, generatorW (fixedEqCoeff s M Q ν c ρ) τ (F u) x := by
  have hcu : ∀ i ≤ 3, ∀ y, ContinuousOn (fun u => iteratedFDeriv ℝ i (F u) y) (Set.Ioc a b) := fun i hi y =>
    (hjc i hi).comp (continuous_id.prodMk continuous_const).continuousOn (fun u hu => ⟨hu, Set.mem_univ _⟩)
  obtain ⟨hZ3, hjet⟩ := s57p_param_jets 3 hab (B := B) (F := F)
    (fun u hu => ⟨by exact_mod_cast (hF u hu).1, fun j hj => (hF u hu).2 j (by omega)⟩) hcu
  obtain ⟨A, hA, hdec, -⟩ := hD.rho
  have hMB := s55f_matBound M
  have hMB0 : 0 ≤ ∑ i, ∑ j, |M i j| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hρ2 : RgDecay 2 (fun _ => A) (ρ τ) := rg_decay_mono (by norm_num) (hdec τ hτ)
  set Zf : Euc d → ℝ := fun y => ∫ u in a..b, F u y with hZf
  simp only [intervalIntegral.integral_of_le hab] at hjet
  set μ : Measure ℝ := volume.restrict (Set.Ioc a b) with hμ
  haveI : IsFiniteMeasure μ := ⟨by simp [hμ]⟩
  have hae : ∀ᵐ u ∂μ, u ∈ Set.Ioc a b := by rw [hμ]; exact ae_restrict_mem measurableSet_Ioc
  have hbd : ∀ u ∈ Set.Ioc a b, ∀ i ≤ 3, ∀ y, ‖iteratedFDeriv ℝ i (F u) y‖ ≤ B :=
    fun u hu i hi y => (hF u hu).2 i (by omega) y
  have hint : ∀ i ≤ 3, ∀ y, Integrable (fun u => iteratedFDeriv ℝ i (F u) y) μ := fun i hi y =>
    s57p_jet_integrable i (fun u hu y' => hbd u hu i hi y') (hcu i hi) y
  -- bounds of the integral
  have hbZ : ∀ i ≤ 3, ∀ y, ‖iteratedFDeriv ℝ i Zf y‖ ≤ B * (b - a) := by
    intro i hi y
    rw [hjet i hi y]
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc a b)
      (f := fun u => iteratedFDeriv ℝ i (F u) y) (C := B) (by simp) (fun u hu => hbd u hu i hi y)
    simpa [Real.volume_real_Ioc_of_le hab, mul_comm] using this
  set Bs : ℝ := max B (B * (b - a)) with hBs
  have hBs0 : 0 ≤ Bs := le_max_of_le_left hB0
  have hbdS : ∀ u ∈ Set.Ioc a b, ∀ i ≤ 3, ∀ y, ‖iteratedFDeriv ℝ i (F u) y‖ ≤ Bs :=
    fun u hu i hi y => (hbd u hu i hi y).trans (le_max_left _ _)
  have hbZS : ∀ i ≤ 3, ∀ y, ‖iteratedFDeriv ℝ i Zf y‖ ≤ Bs := fun i hi y => (hbZ i hi y).trans (le_max_right _ _)
  -- Laplacian and gradient
  have hΔ : ∀ y, Laplacian.laplacian Zf y = ∫ u, Laplacian.laplacian (F u) y ∂μ := by
    intro y
    rw [s57p_laplacian_eq_Ll, hjet 2 (by norm_num) y, ← (s57pLl d).integral_comp_comm (hint 2 (by norm_num) y)]
    exact integral_congr_ae (Eventually.of_forall fun u => (s57p_laplacian_eq_Ll _ _).symm)
  have hgr : ∀ y, gradient Zf y = ∫ u, gradient (F u) y ∂μ := by
    intro y
    rw [s57p_gradient_eq_Lg, hjet 1 (by norm_num) y, ← (s57pLg d).integral_comp_comm (hint 1 (by norm_num) y)]
    exact integral_congr_ae (Eventually.of_forall fun u => (s57p_gradient_eq_Lg _ _).symm)
  have hΔint : Integrable (fun u => Laplacian.laplacian (F u) x) μ := by
    have := (s57pLl d).integrable_comp (hint 2 (by norm_num) x)
    exact this.congr (Eventually.of_forall fun u => (s57p_laplacian_eq_Ll _ _).symm)
  have hgint : ∀ y, Integrable (fun u => gradient (F u) y) μ := by
    intro y
    have := (s57pLg d).integrable_comp (hint 1 (by norm_num) y)
    exact this.congr (Eventually.of_forall fun u => (s57p_gradient_eq_Lg _ _).symm)
  set v : Euc d := -(Torus.matVec Q x) + c τ x with hv
  have hinner : Integrable (fun u => inner ℝ v (gradient (F u) x)) μ := by
    have := (innerSL ℝ v).integrable_comp (hgint x)
    exact this
  -- the nonlocal terms
  have hnl : ∀ j : Fin d, Integrable (fun u => (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ τ y * (Torus.matVec M.transpose (gradient (F u) y)) j) x) j) μ ∧
      (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ τ y * (Torus.matVec M.transpose (gradient Zf y)) j) x) j =
      ∫ u, (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ τ y * (Torus.matVec M.transpose (gradient (F u) y)) j) x) j ∂μ := by
    intro j
    set Λ : Euc d →L[ℝ] ℝ := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).comp
      (Matrix.toEuclideanLin M.transpose).toContinuousLinearMap with hΛ
    have hΛe : ∀ w : Euc d, (Torus.matVec M.transpose w) j = Λ w := fun w => by simp [hΛ, Torus.matVec]
    set c' : ℝ := 2 ^ 2 * A * ((d : ℝ) * (∑ i, ∑ j, |M i j|) * Bs) with hc'
    have hc'0 : 0 ≤ c' := by positivity
    set K : ℝ → Euc d → ℝ := fun u y => ρ τ y * (Torus.matVec M.transpose (gradient (F u) y)) j with hK
    set Kz : Euc d → ℝ := fun y => ρ τ y * (Torus.matVec M.transpose (gradient Zf y)) j with hKz
    have hKz' : ∀ y, Kz y = ∫ u in a..b, K u y := by
      intro y
      rw [intervalIntegral.integral_of_le hab]
      simp only [hKz, hK, hΛe, hgr y]
      rw [integral_const_mul, ← Λ.integral_comp_comm (hgint y)]
    have hKdec : ∀ u ∈ Set.Ioc a b, RgDecay 2 (fun _ => c') (K u) := fun u hu =>
      s55m_nl_decay hMB hMB0 hA hBs0 hρ2 ((hF u hu).1.of_le (by norm_num)) (hbdS u hu) j
    have hKc : ContinuousOn (fun p : ℝ × Euc d => K p.1 p.2) (Set.Ioc a b ×ˢ Set.univ) := by
      have e : (fun p : ℝ × Euc d => K p.1 p.2) = fun p => ρ τ p.2 * Λ (s57pLg d (iteratedFDeriv ℝ 1 (F p.1) p.2)) := by
        funext p; simp only [hK, hΛe, s57p_gradient_eq_Lg]
      rw [e]
      exact (hρ2.1.continuous.comp continuous_snd).continuousOn.mul
        ((Λ.comp (s57pLg d)).continuous.comp_continuousOn (hjc 1 (by norm_num)))
    obtain ⟨hI, heq⟩ := s57p_rgT_integral hD.hd hD.hs0 hD.hsd (rgKerComp_ok hD.hs0 j) hc'0 hab hKdec hKc hKz' x
    have hZdec : RgDecay 2 (fun _ => c') Kz :=
      s55m_nl_decay hMB hMB0 hA hBs0 hρ2 hZ3 hbZS j
    have ee : ∀ u ∈ Set.Ioc a b, (convGradConvW (rieszKernelGrad d s) (K u) x) j =
        rgT (fun z => (rieszKernelGrad d s z) j) (K u) x := fun u hu =>
      s57p_conv_eq hD.hd hD.hs0 hD.hsd hc'0 (hKdec u hu) x j
    refine ⟨?_, ?_⟩
    · refine hI.congr ?_
      filter_upwards [hae] with u hu
      exact (ee u hu).symm
    · rw [s57p_conv_eq hD.hd hD.hs0 hD.hsd hc'0 hZdec x j, heq, intervalIntegral.integral_of_le hab]
      exact setIntegral_congr_fun measurableSet_Ioc (fun u hu => (ee u hu).symm)
  have hsumint : Integrable (fun u => ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ τ y * (Torus.matVec M.transpose (gradient (F u) y)) j) x) j) μ :=
    integrable_finset_sum _ fun j _ => (hnl j).1
  have hAint : Integrable (fun u => ν * Laplacian.laplacian (F u) x + inner ℝ v (gradient (F u) x)) μ :=
    (hΔint.const_mul ν).add hinner
  show ν * Laplacian.laplacian Zf x + inner ℝ v (gradient Zf x) - ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ τ y * (Torus.matVec M.transpose (gradient Zf y)) j) x) j =
    ∫ u in a..b, (ν * Laplacian.laplacian (F u) x + inner ℝ v (gradient (F u) x) - ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ τ y * (Torus.matVec M.transpose (gradient (F u) y)) j) x) j)
  rw [intervalIntegral.integral_of_le hab, integral_sub hAint hsumint, integral_add (hΔint.const_mul ν) hinner,
    integral_const_mul, integral_inner (hgint x) v, integral_finset_sum _ (fun j _ => (hnl j).1), ← hΔ x, ← hgr x]
  congr 1
  exact Finset.sum_congr rfl fun j _ => (hnl j).2

theorem s57p_lin_inst {s : ℝ} (M Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} {c : ℝ → Euc d → Euc d}
    {ρ : ℝ → Euc d → ℝ} {T : ℝ} (hD : S57pFeData s Q ν c ρ T) :
    S57pLin (fixedEqCoeff s M Q ν c ρ) T :=
  ⟨fun τ hτ B u₁ u₂ h₁ h₂ b₁ b₂ x => s57p_lin_sub M Q hD hτ h₁ h₂ b₁ b₂ x,
    fun τ hτ a b B hB hab F hF hjc x => s57p_lin_comm M Q hD hτ hB hab hF hjc x⟩

theorem s57p_gen_inst {s : ℝ} (M Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} {c : ℝ → Euc d → Euc d}
    {ρ : ℝ → Euc d → ℝ} {T : ℝ} (hD : S57pFeData s Q ν c ρ T) :
    S57pGen (fixedEqCoeff s M Q ν c ρ) T :=
  ⟨s57p_gen_rgW M Q hD, fun hB _ _ hτ hτ₀ hτt _ _ hu hu₀ h1 x h2 =>
    s57p_gen_tendsto M Q hD hB hτ hτ₀ hτt hu hu₀ h1 x h2⟩

end HRS.MS.FixEq
