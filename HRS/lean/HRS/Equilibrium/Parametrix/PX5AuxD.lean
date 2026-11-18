import HRS.Equilibrium.Parametrix.PX5AuxC

/-!
# Prop 4.13 parametrix, packet PX5: linearity in `f`

`Hsource`, `parxR_j`, `parxPsi_L`, `diagExt R_L` are linear in the smooth test function `f`.
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

theorem px5_isSmooth_comb {f f' : Torus d → ℝ} (hf : Torus.IsSmooth f) (hf' : Torus.IsSmooth f')
    (a b : ℝ) : Torus.IsSmooth (a • f + b • f') := by
  unfold Torus.IsSmooth Torus.IsCk at *
  have e : Torus.lift (a • f + b • f') = a • Torus.lift f + b • Torus.lift f' := rfl
  rw [e]
  exact (hf.const_smul a).add (hf'.const_smul b)

theorem px5_grad_comb {f f' : Torus d → ℝ} (hf : Torus.IsSmooth f) (hf' : Torus.IsSmooth f')
    (a b : ℝ) (x : Torus d) :
    Torus.grad (a • f + b • f') x = a • Torus.grad f x + b • Torus.grad f' x := by
  unfold Torus.grad
  have e : Torus.lift (a • f + b • f') = a • Torus.lift f + b • Torus.lift f' := rfl
  have hf1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) := hf
  have hf2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f') := hf'
  have h1 : DifferentiableAt ℝ (Torus.lift f) (Torus.rep x) :=
    (hf1.differentiable (by simp)) _
  have h2 : DifferentiableAt ℝ (Torus.lift f') (Torus.rep x) :=
    (hf2.differentiable (by simp)) _
  rw [e]
  have h3 : fderiv ℝ (a • Torus.lift f + b • Torus.lift f') (Torus.rep x) =
      a • fderiv ℝ (Torus.lift f) (Torus.rep x) + b • fderiv ℝ (Torus.lift f') (Torus.rep x) := by
    rw [fderiv_add (h1.const_smul a) (h2.const_smul b), fderiv_const_smul h1, fderiv_const_smul h2]
  unfold gradient
  rw [h3]
  simp

theorem px5_hTransport_comb {f f' : Torus d → ℝ} (hf : Torus.IsSmooth f) (hf' : Torus.IsSmooth f')
    (s a b : ℝ) (x y : Torus d) :
    hTransport d s (a • f + b • f') x y = a * hTransport d s f x y + b * hTransport d s f' x y := by
  unfold hTransport
  rw [px5_grad_comb hf hf' a b x, px5_grad_comb hf hf' a b y]
  have : a • Torus.grad f x + b • Torus.grad f' x - (a • Torus.grad f y + b • Torus.grad f' y) =
      a • (Torus.grad f x - Torus.grad f y) + b • (Torus.grad f' x - Torus.grad f' y) := by
    module
  rw [this, inner_add_left, inner_smul_left, inner_smul_left]
  simp

theorem px5_integrable_of_smooth (hρ : SmoothPosDensity ρ) {g : Torus d → ℝ} (hg : Torus.IsSmooth g) :
    Integrable g (withDensityReal ρ) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hc : Continuous g := Torus.continuous_of_continuous_lift (by
    have : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift g) := hg
    exact this.continuous)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

theorem px5_hsource_comb (H : ParxHyp d s V β ρ) {f f' : Torus d → ℝ} (hf : Torus.IsSmooth f)
    (hf' : Torus.IsSmooth f') (a b : ℝ) (x y : Torus d) :
    Hsource d s ρ (a • f + b • f') x y = a * Hsource d s ρ f x y + b * Hsource d s ρ f' x y := by
  have hd := H.two_le
  have hs0 := px5_s_pos H
  have hsd := H.s_lt
  have hρ := H.rho_smooth
  have hfab := px5_isSmooth_comb hf hf' a b
  have hC := hTransport_conormal px5_conormalAdd hd hs0 hsd
  obtain ⟨Cr, -, hCr⟩ := row_data hd hsd hρ hC 0
  have hrf := hCr f hf
  have hrf' := hCr f' hf'
  have i1 := hTransport_row_integrable hd hs0.le hsd hρ hf
  have i2 := hTransport_row_integrable hd hs0.le hsd hρ hf'
  have r1 : ∀ x, ∫ y', hTransport d s (a • f + b • f') x y' ∂(withDensityReal ρ) =
      a * ∫ y', hTransport d s f x y' ∂(withDensityReal ρ) +
        b * ∫ y', hTransport d s f' x y' ∂(withDensityReal ρ) := by
    intro x
    simp_rw [px5_hTransport_comb hf hf' s a b x]
    rw [integral_add ((i1 x).const_mul a) ((i2 x).const_mul b), integral_const_mul, integral_const_mul]
  rw [hsource_eq hsd hfab, hsource_eq hsd hf, hsource_eq hsd hf', r1 x, r1 y, px5_hTransport_comb hf hf' s a b x y]
  have r2 : ∫ x', (∫ y', hTransport d s (a • f + b • f') x' y' ∂(withDensityReal ρ)) ∂(withDensityReal ρ) =
      a * ∫ x', (∫ y', hTransport d s f x' y' ∂(withDensityReal ρ)) ∂(withDensityReal ρ) +
        b * ∫ x', (∫ y', hTransport d s f' x' y' ∂(withDensityReal ρ)) ∂(withDensityReal ρ) := by
    simp_rw [r1]
    rw [integral_add ((px5_integrable_of_smooth hρ (g := fun x' => ∫ y', hTransport d s f x' y' ∂(withDensityReal ρ)) hrf.1).const_mul a)
      ((px5_integrable_of_smooth hρ (g := fun x' => ∫ y', hTransport d s f' x' y' ∂(withDensityReal ρ)) hrf'.1).const_mul b),
      integral_const_mul, integral_const_mul]
  rw [r2]
  ring

theorem px5_neBot_torus (hd : 0 < d) (x : Torus d) : (𝓝[≠] x).NeBot := by
  set p : Euc d := Torus.rep x with hp
  have hx : Torus.mk p = x := Torus.mk_rep x
  set S' : Set (Euc d) := {v | Torus.mk v ≠ Torus.mk p} with hS'
  have hmk := isOpenQuotientMap_mk (d := d)
  have hmkc : Continuous (Torus.mk : Euc d → Torus d) := hmk.continuous
  have h1 : Filter.map Torus.mk (𝓝[S'] p) ≤ 𝓝[≠] x := by
    rw [nhdsWithin, nhdsWithin]
    refine (Filter.map_inf_le).trans (inf_le_inf ?_ ?_)
    · show Filter.map Torus.mk (𝓝 p) ≤ 𝓝 x
      rw [← hx]; exact hmkc.continuousAt
    · rw [Filter.map_principal]
      refine Filter.principal_mono.2 ?_
      rintro _ ⟨v, hv, rfl⟩
      rw [← hx]; exact hv
  have hne : (𝓝[S'] p).NeBot := neBot_punctured_torus hd p p
  have : (Filter.map Torus.mk (𝓝[S'] p)).NeBot := hne.map _
  exact Filter.NeBot.mono this h1

theorem px5_diagExt_tendsto (hd : 2 ≤ d) {J : ℕ} {σ : ℝ} {b : ℕ} (hσ : σ + ((J : ℝ) + 1) < 0)
    {B : ℝ} (hB : 0 ≤ B) {F : Torus d → Torus d → ℝ} (hF : Conormal σ b (J + 1) B F) (x : Torus d) :
    Tendsto (fun y' => F x y') (𝓝[≠] x) (𝓝 (diagExt F x x)) := by
  obtain ⟨C, -, hC⟩ := conormal_extend hd J σ b hσ
  obtain ⟨h1, -, h3⟩ := hC B F hB hF
  have hc := px5_cont_slice2 h1 x
  have ht : Tendsto (fun y' => diagExt F x y') (𝓝[≠] x) (𝓝 (diagExt F x x)) :=
    (hc.tendsto x).mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y' hy'
  exact h3 x y' (fun h => hy' h.symm)

theorem px5_R_comb (H : ParxHyp d s V β ρ) (J : ℕ) {f f' : Torus d → ℝ} (hf : Torus.IsSmooth f)
    (hf' : Torus.IsSmooth f') (a b : ℝ) :
    ∀ j ≤ parxL d J, parxR d s V β ρ (a • f + b • f') j =
      fun x y => a * parxR d s V β ρ f j x y + b * parxR d s V β ρ f' j x y := by
  have hfab := px5_isSmooth_comb hf hf' a b
  obtain ⟨CN, hCN0, hCN⟩ := px5_N_class H J
  intro j
  induction j with
  | zero =>
    intro _
    funext x y
    by_cases hxy : x = y
    · subst hxy; simp [parxR, offZero]
    · simp only [parxR, offZero, hxy, ite_false]
      exact px5_hsource_comb H hf hf' a b x y
  | succ j ih =>
    intro hj
    have hjL : j < parxL d J := by omega
    have ih' := ih (by omega)
    obtain ⟨C1, hC10, hC1⟩ := parxR_conormal H (px5m d J) j (by unfold px5m; omega)
    have hσ : s - (j : ℝ) / 2 < d := by
      have : (0 : ℝ) ≤ (j : ℝ) / 2 := by positivity
      linarith [H.s_lt]
    obtain ⟨h1f, -, -⟩ := hC1 f hf
    obtain ⟨h1f', -, -⟩ := hC1 f' hf'
    have hnl := newton_linear H hσ h1f h1f' a b
    have hgl := gen_linear H (px5_crit_lt H) (b := 1) (m := J + 3) (by omega)
      (hCN f hf j hjL) (hCN f' hf' j hjL) a b
    funext x y
    show defectOp d s V β ρ (parxR d s V β ρ (a • f + b • f') j) x y = _
    rw [ih']
    unfold defectOp
    by_cases hxy : x = y
    · simp [hxy, parxR, defectOp]
    · simp only [hxy, ite_false]
      rw [hnl]
      obtain ⟨g1, g2, -⟩ := hgl x y hxy
      show _ + genFst d s V β ρ (fun x y => a * newtonOp d β ρ (parxR d s V β ρ f j) x y +
          b * newtonOp d β ρ (parxR d s V β ρ f' j) x y) x y + genSnd d s V β ρ
          (fun x y => a * newtonOp d β ρ (parxR d s V β ρ f j) x y +
          b * newtonOp d β ρ (parxR d s V β ρ f' j) x y) x y = _
      rw [g1, g2]
      simp only [parxR, defectOp, hxy, ite_false]
      ring

theorem px5_linear_psi (H : ParxHyp d s V β ρ) (J : ℕ) {f f' : Torus d → ℝ} (hf : Torus.IsSmooth f)
    (hf' : Torus.IsSmooth f') (a b : ℝ) :
    parxPsi d s V β ρ (a • f + b • f') (parxL d J) =
      fun x y => a * parxPsi d s V β ρ f (parxL d J) x y + b * parxPsi d s V β ρ f' (parxL d J) x y := by
  funext x y
  unfold parxPsi
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjL := Finset.mem_range.mp hj
  obtain ⟨C1, hC10, hC1⟩ := parxR_conormal H (px5m d J) j (by unfold px5m; omega)
  have hσ : s - (j : ℝ) / 2 < d := by
    have : (0 : ℝ) ≤ (j : ℝ) / 2 := by positivity
    linarith [H.s_lt]
  obtain ⟨h1f, -, -⟩ := hC1 f hf
  obtain ⟨h1f', -, -⟩ := hC1 f' hf'
  have hnl := newton_linear H hσ h1f h1f' a b
  rw [px5_R_comb H J hf hf' a b j (by omega), hnl]

theorem px5_R_class (H : ParxHyp d s V β ρ) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Conormal (s - (parxL d J : ℝ) / 2) 0 (J + 1) (C * posSeminorm (px5m d J + 2) f)
        (parxR d s V β ρ f (parxL d J)) := by
  have hL : 2 * parxL d J ≤ px5m d J := by unfold px5m; omega
  obtain ⟨C, hC0, hC⟩ := parxR_conormal H (px5m d J) (parxL d J) hL
  have e : px5m d J - 2 * parxL d J = J + 1 := by unfold px5m; omega
  refine ⟨C, hC0, fun f hf => ?_⟩
  have := (hC f hf).1
  rw [e] at this
  exact this

theorem px5_linear_R (H : ParxHyp d s V β ρ) (J : ℕ) {f f' : Torus d → ℝ} (hf : Torus.IsSmooth f)
    (hf' : Torus.IsSmooth f') (a b : ℝ) :
    diagExt (parxR d s V β ρ (a • f + b • f') (parxL d J)) =
      fun x y => a * diagExt (parxR d s V β ρ f (parxL d J)) x y +
        b * diagExt (parxR d s V β ρ f' (parxL d J)) x y := by
  have hσ : s - (parxL d J : ℝ) / 2 + ((J : ℝ) + 1) < 0 := by
    have hc : (parxL d J : ℝ) = 2 * J + d + 6 := by unfold parxL; push_cast; ring
    rw [hc, H.crit]; linarith
  obtain ⟨C, hC0, hC⟩ := px5_R_class H J
  have hB0 : ∀ g : Torus d → ℝ, 0 ≤ C * posSeminorm (px5m d J + 2) g :=
    fun g => mul_nonneg hC0 (posSeminorm_nonneg' _ _)
  have hcomb := px5_R_comb H J hf hf' a b (parxL d J) le_rfl
  funext x y
  by_cases hxy : x = y
  · subst hxy
    have t1 := px5_diagExt_tendsto H.two_le hσ (hB0 f) (hC f hf) x
    have t2 := px5_diagExt_tendsto H.two_le hσ (hB0 f') (hC f' hf') x
    have hNe := px5_neBot_torus (by have := H.two_le; omega) x
    have t3 := (t1.const_mul a).add (t2.const_mul b)
    have e : diagExt (parxR d s V β ρ (a • f + b • f') (parxL d J)) x x =
        limUnder (𝓝[≠] x) (fun y' => a * parxR d s V β ρ f (parxL d J) x y' +
          b * parxR d s V β ρ f' (parxL d J) x y') := by
      simp only [diagExt, if_true, hcomb]
    rw [e]
    exact t3.limUnder_eq
  · simp only [diagExt, hxy, ite_false, hcomb]

end HRS.Parx

end
