import HRS.Main.ThermLin2St3

/-!
# THERMLIN2, packet St, part 4: D3 `tl2_stationary_fdd`

The finite-dimensional laws of `Z̃^t = W^{t,0} ξ + ∫_0^t W^{t,r} dĜ_r`.  Uses `tl2_xi_law`-type hypotheses only through
the arguments (`γ`, `hγ`); the Lyapunov identity is the proof `tl2_lyapunov_proof` (D2), not the plan statement.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.ThermLin.Plan2

open HRS HRS.PDE HRS.PDE.MFSemigroup HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c HRS.Uniform.Q07c

variable {d : ℕ}

/-- The entries of the covariance matrix of the noise part, via `t25p_cov_eq`. -/
theorem tl2St_B_entry (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m)
    {T' K : ℝ} (hT' : 0 < T') (hK : 0 ≤ K)
    (Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hWd : IsDualEvolution S.dyn (fun _ => ρβ) m Wev)
    (hWb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Wev t r‖ ≤ K)
    {φa φb : Torus d → ℝ} (hφa : Torus.IsSmooth φa) (hφb : Torus.IsSmooth φb) {ta tb : ℝ}
    (hta : ta ∈ Set.Icc (0 : ℝ) T') (htb : tb ∈ Set.Icc (0 : ℝ) T') :
    ∫ σ in Set.Icc 0 (min ta tb),
      tl2CbDens S ρβ m T' σ
        (pullbackVec (HRS.Uniform.Comp28.plainData Wev) ta σ (gfb4_ell m φa))
        (pullbackVec (HRS.Uniform.Comp28.plainData Wev) tb σ (gfb4_ell m φb)) =
    2 * S.β⁻¹ * ∫ σ in Set.Icc 0 (min ta tb), ∫ x,
      inner ℝ (Torus.grad (propagator S.dyn (fun _ => ρβ) σ ta φa) x)
        (Torus.grad (propagator S.dyn (fun _ => ρβ) σ tb φb) x) * ρβ x := by
  have htr := HRS.ThermLin.thermlin_stationary_traj S h
  have hm2 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hq0 : 0 ≤ S.β⁻¹ := inv_nonneg.2 S.hβ.le
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
  exact t25p_cov_eq S.hd htr hm2 hT' hWd hK hWb hq0 hta htb hσ hφa hφb

/-- Core of D3: given the law of the noise vector and its independence of `ξ`, the law of the vector
`(eval (W ξ + Zb) φ_a)_a` is the stationary Gaussian law. -/
theorem tl2St_fdd_core (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m)
    {T' K : ℝ} (hT' : 0 < T') (hK : 0 ≤ K)
    (Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hWd : IsDualEvolution S.dyn (fun _ => ρβ) m Wev)
    (hWb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Wev t r‖ ≤ K)
    {Ω₃ : Type} [mΩ₃ : MeasurableSpace Ω₃] (P₃ : Measure Ω₃) [IsProbabilityMeasure P₃]
    (γ : Measure (NegSobolev d m))
    (hγ : IsCenteredGaussianWithCov m γ (susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β))
    (ξ : Ω₃ → NegSobolev d m) (hξ : Measurable ξ) (hξlaw : P₃.map ξ = γ)
    (Zb : ℝ → Ω₃ → NegSobolev d m) (hZbm : ∀ t, Measurable (Zb t))
    {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T')
    (hφ : ∀ a, Torus.IsSmooth (φ a))
    (hBpsd : (Matrix.of fun a b => ∫ σ in Set.Icc 0 (min (ts a) (ts b)),
      tl2CbDens S ρβ m T' σ
        (pullbackVec (HRS.Uniform.Comp28.plainData Wev) (ts a) σ (gfb4_ell m (φ a)))
        (pullbackVec (HRS.Uniform.Comp28.plainData Wev) (ts b) σ (gfb4_ell m (φ b)))).PosSemidef)
    (hXlaw : P₃.map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Zb (ts a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun a b => ∫ σ in Set.Icc 0 (min (ts a) (ts b)),
      tl2CbDens S ρβ m T' σ
        (pullbackVec (HRS.Uniform.Comp28.plainData Wev) (ts a) σ (gfb4_ell m (φ a)))
        (pullbackVec (HRS.Uniform.Comp28.plainData Wev) (ts b) σ (gfb4_ell m (φ b)))))
    (hindX : IndepFun (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Zb (ts a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p))) ξ P₃) :
    P₃.map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Wev (ts a) 0 (ξ ω) + Zb (ts a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (PDE.stationaryLagCov d S.s S.β S.dyn ρβ ts φ) := by
  have hmem : ∀ a, MemSobolev m (φ a) := fun a => HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ a) m
  have hUs : ∀ a, Torus.IsSmooth (tl2Ub S ρβ 0 (ts a) (φ a)) := fun a =>
    tl2Ly_smooth S h (hφ a) le_rfl (hts a).1
  set X : Ω₃ → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a => NegSobolev.eval (Zb (ts a) ω) (φ a)
    with hX
  set Lm : NegSobolev d m → EuclideanSpace ℝ (Fin p) := fun z =>
    WithLp.toLp 2 fun a => NegSobolev.eval z (tl2Ub S ρβ 0 (ts a) (φ a)) with hLm
  have hUmem : ∀ a, MemSobolev m (tl2Ub S ρβ 0 (ts a) (φ a)) := fun a =>
    HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hUs a) m
  have hLmm : Measurable Lm :=
    measurable_toLp_eval fun a => (continuous_eval_const (hUmem a)).measurable
  have hXm : Measurable X := measurable_toLp_eval fun a =>
    (continuous_eval_const (hmem a)).measurable.comp (hZbm _)
  set Bm : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b =>
    ∫ σ in Set.Icc 0 (min (ts a) (ts b)),
      tl2CbDens S ρβ m T' σ
        (pullbackVec (HRS.Uniform.Comp28.plainData Wev) (ts a) σ (gfb4_ell m (φ a)))
        (pullbackVec (HRS.Uniform.Comp28.plainData Wev) (ts b) σ (gfb4_ell m (φ b))) with hBm
  have hindXA : IndepFun X (Lm ∘ ξ) P₃ := hindX.comp measurable_id hLmm
  obtain ⟨hSpsd, hSchar⟩ := tl2St_xi_charFun (susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β)
    γ hγ (fun a => tl2Ub S ρβ 0 (ts a) (φ a)) hUs P₃ ξ hξ hξlaw
  have hlaw := tl2St_law_add P₃ X (Lm ∘ ξ) hXm (hLmm.comp hξ) hindXA hBpsd hSpsd hXlaw hSchar
  have hvec : (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Wev (ts a) 0 (ξ ω) + Zb (ts a) ω) (φ a) :
      EuclideanSpace ℝ (Fin p))) = fun ω => X ω + (Lm ∘ ξ) ω := by
    funext ω
    ext a
    have hadd : NegSobolev.eval (Wev (ts a) 0 (ξ ω) + Zb (ts a) ω) (φ a) =
        NegSobolev.eval (Wev (ts a) 0 (ξ ω)) (φ a) + NegSobolev.eval (Zb (ts a) ω) (φ a) := by
      rw [← gfb4_ell_apply (hmem a), map_add, gfb4_ell_apply (hmem a), gfb4_ell_apply (hmem a)]
    have hd0 := hWd 0 (ts a) le_rfl (hts a).1 (ξ ω) (φ a) (hφ a)
    simp only [hX, hLm, Function.comp, PiLp.add_apply, hadd, hd0]
    change _ = _ + NegSobolev.eval (ξ ω) (propagator S.dyn (fun _ => ρβ) 0 (ts a) (φ a))
    ring
  rw [hvec, hlaw]
  congr 1
  ext a b
  have hBab : Bm a b = 2 * S.β⁻¹ * ∫ σ in Set.Icc 0 (min (ts a) (ts b)), ∫ x,
      inner ℝ (Torus.grad (propagator S.dyn (fun _ => ρβ) σ (ts a) (φ a)) x)
        (Torus.grad (propagator S.dyn (fun _ => ρβ) σ (ts b) (φ b)) x) * ρβ x := by
    simp only [hBm, Matrix.of_apply]
    exact tl2St_B_entry S h m hm hT' hK Wev hWd hWb (hφ a) (hφ b) (hts a) (hts b)
  simp only [Matrix.add_apply, Matrix.of_apply, PDE.stationaryLagCov]
  rw [add_comm, hBab]
  split_ifs with hab
  · rw [min_eq_left hab]
    exact tl2St_entry_le S h (hφ a) (hφ b) (hts a).1 hab
  · have hba : ts b ≤ ts a := (not_le.1 hab).le
    rw [min_eq_right hba]
    exact tl2St_entry_gt S h (hφ a) (hφ b) (hts b).1 hba

/-- D3 proof. -/
theorem tl2_stationary_fdd_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m)
    {T' K : ℝ} (hT' : 0 < T') (hK : 0 ≤ K)
    (Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hWd : IsDualEvolution S.dyn (fun _ => ρβ) m Wev) (hWp : IsPlainEvolution Wev T')
    (hWb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Wev t r‖ ≤ K)
    {Ω₃ : Type} [mΩ₃ : MeasurableSpace Ω₃] (P₃ : Measure Ω₃) [IsProbabilityMeasure P₃] {ℱ₃ : Filtration ℝ mΩ₃}
    (γ : Measure (NegSobolev d m))
    (hγ : IsCenteredGaussianWithCov m γ (susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β))
    (ξ : Ω₃ → NegSobolev d m) (hξ : Measurable ξ) (hξlaw : P₃.map ξ = γ)
    (Ĝ : ℝ → Ω₃ → NegSobolev d m)
    (hĜ : IsHilbertMartingaleWithCovariation P₃ ℱ₃ T' Ĝ (fun r _ => tl2CbDens S ρβ m T' r))
    (hĜc : ∀ ω, Continuous fun s => Ĝ s ω) (hĜz : ∀ ω, Ĝ 0 ω = 0)
    (hind : Indep (MeasurableSpace.comap ξ inferInstance)
      (⨆ τ ∈ Set.Icc (0 : ℝ) T', MeasurableSpace.comap (Ĝ τ) inferInstance) P₃)
    (Zb : ℝ → Ω₃ → NegSobolev d m)
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P₃ Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Ĝ 0 t (Zb t))
    (hZbm : ∀ t, Measurable (Zb t)) :
    ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ), (∀ a, ts a ∈ Set.Icc (0 : ℝ) T') →
      (∀ a, Torus.IsSmooth (φ a)) →
      P₃.map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Wev (ts a) 0 (ξ ω) + Zb (ts a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (PDE.stationaryLagCov d S.s S.β S.dyn ρβ ts φ) := by
  intro p ts φ hts hφ
  have hmem : ∀ a, MemSobolev m (φ a) := fun a => HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ a) m
  have hVc : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => Wev p.1 p.2 y)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T'} := hWp.2.2
  have hXlaw := t25p_Zb_gaussian hK hT' Wev hVc hWb P₃ Ĝ _ hĜ hĜc hĜz Zb hZb hZbm ts hts φ hmem
  have hBpsd : (Matrix.of fun a b => ∫ σ in Set.Icc 0 (min (ts a) (ts b)),
      tl2CbDens S ρβ m T' σ
        (pullbackVec (HRS.Uniform.Comp28.plainData Wev) (ts a) σ (gfb4_ell m (φ a)))
        (pullbackVec (HRS.Uniform.Comp28.plainData Wev) (ts b) σ (gfb4_ell m (φ b)))).PosSemidef := by
    refine tl2St_cov_psd (B := K * ∑ b, ‖gfb4_ell m (φ b)‖) hĜ hĜc hĜz hT' ts hts
      (fun a σ => pullbackVec (HRS.Uniform.Comp28.plainData Wev) (ts a) σ (gfb4_ell m (φ a))) ?_ ?_
    · intro a σ hσ
      have h1 := t25p_norm_pullback_le Wev hWb hK hσ.1 hσ.2 (hts a).2 (gfb4_ell m (φ a))
      refine h1.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hK
      exact Finset.single_le_sum (f := fun b => ‖gfb4_ell m (φ b)‖) (fun b _ => norm_nonneg _)
        (Finset.mem_univ a)
    · intro a x
      exact t25p_pullback_weak Wev hVc (hts a) _ x
  have hindX : IndepFun (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Zb (ts a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p))) ξ P₃ :=
    t25p_indep_pairing hT' Wev P₃ Ĝ Ĝ _ hĜ (fun τ _ => measurable_of_isHM hĜ τ)
      (fun τ _ => Filter.EventuallyEq.rfl) Zb hZb hZbm ξ hind ts hts φ hmem
  exact tl2St_fdd_core S h m hm hT' hK Wev hWd hWb P₃ γ hγ ξ hξ hξlaw Zb hZbm ts φ hts hφ hBpsd hXlaw hindX

example := (@tl2_stationary_fdd_proof : type_of% @tl2_stationary_fdd)

end HRS.ThermLin.Plan2
