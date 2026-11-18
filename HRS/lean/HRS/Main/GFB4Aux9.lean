import HRS.Main.GFB4Aux8

/-!
# GFB4, part 9: equality of the finite-dimensional laws of `Y` and of `V(·,0) j X₀' + Z̄`
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.GF

open HRS HRS.Uniform HRS.Uniform.Q54c HRS.Uniform.Q45 HRS.Uniform.Q07c

variable {d : ℕ}

theorem gfb4_fdd (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (m K : ℝ) (hm : (S.γ : ℝ) ≤ m)
    (EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m)) (hEV : GFEvo S M N m K EV)
    {Ω Ω' : Type} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (ℱ'' : Filtration ℝ mΩ') (X₀' : Ω' → NegSobolev d (S.γ : ℝ)) (hX₀' : Measurable X₀')
    (G G0 : ℝ → Ω' → NegSobolev d (S.γ : ℝ))
    (hG : IsHilbertMartingaleWithCovariation P' ℱ'' S.T G
      (fun r _ => covDensT (S.γ : ℝ) (qN S N) S.T (S.ρ N) r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0)
    (hG0m : ∀ τ ∈ Set.Icc (0 : ℝ) S.T, Measurable (G0 τ))
    (hGG : ∀ τ ∈ Set.Icc (0 : ℝ) S.T, G τ =ᵐ[P'] G0 τ)
    (hGind : Indep (MeasurableSpace.comap X₀' inferInstance)
      (⨆ τ ∈ Set.Icc (0 : ℝ) S.T, MeasurableSpace.comap (G0 τ) inferInstance) P')
    (Zb : ℝ → Ω' → NegSobolev d m)
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) S.T, IsStochConv P' EV.VE EV.j G 0 t (Zb t))
    (hZbm : ∀ t, Measurable (Zb t))
    (Y₀ : Ω → NegSobolev d m) (hY₀ : Measurable Y₀) (hlaw : P.map Y₀ = P'.map (fun ω' => EV.j (X₀' ω')))
    (Y : ℝ → Ω → NegSobolev d m)
    (hY : IsLinearFluctuationSolution P (S.dynM M N) (S.ρ N) m (qN S N) S.T Y₀ Y) :
    ∀ (p : ℕ) (ts : Fin p → ℝ) (ks : Fin p → NonzeroLattice d), (∀ a, ts a ∈ Set.Icc 0 S.T) →
      P.map (fun ω a => NegSobolev.coord (Y (ts a) ω) (ks a)) =
        P'.map (fun ω' a => NegSobolev.coord (EV.VE (ts a) 0 (EV.j (X₀' ω')) + Zb (ts a) ω') (ks a)) := by
  intro p ts ks hts
  have hT0 : 0 < S.T := S.hT
  set φ : Fin p → Torus d → ℝ := fun a => Torus.realMode (ks a) with hφdef
  have hφ : ∀ a, Torus.IsSmooth (φ a) := fun a => HRS.Uniform.Q48b.q48b_isSmooth_realMode (ks a)
  have hmemφ : ∀ a, MemSobolev m (φ a) := fun a =>
    HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ a) m
  have hmemU : ∀ a, MemSobolev m (propagator (S.dynM M N) (S.ρ N) 0 (ts a) (φ a)) := fun a =>
    (hEV.adjoint 0 (ts a) le_rfl (hts a).1 (hts a).2 (φ a) (gfb4_isCk2_of_smooth (hφ a)) (hmemφ a)).2.1
  set W : NegSobolev d m → EuclideanSpace ℝ (Fin p) :=
    fun z => WithLp.toLp 2 fun a => NegSobolev.eval z (propagator (S.dynM M N) (S.ρ N) 0 (ts a) (φ a))
    with hWdef
  have hW : Measurable W := measurable_toLp_eval fun a => (continuous_eval_const (hmemU a)).measurable
  set Sy : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b =>
    2 * qN S N * ∫ r in Set.Icc 0 (min (ts a) (ts b)), ∫ x,
      inner ℝ (Torus.grad (propagator (S.dynM M N) (S.ρ N) r (ts a) (φ a)) x)
        (Torus.grad (propagator (S.dynM M N) (S.ρ N) r (ts b) (φ b)) x) * S.ρ N r x with hSy
  set Gy : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
    NegSobolev.eval (Y (ts a) ω) (φ a) -
      NegSobolev.eval (Y₀ ω) (propagator (S.dynM M N) (S.ρ N) 0 (ts a) (φ a)) with hGy
  obtain ⟨hindY, hlawY⟩ := hY.gaussian_part p ts φ hts hφ
  -- the Gaussian part on `Ω'`
  set Y₀' : Ω' → NegSobolev d m := fun ω' => EV.j (X₀' ω') with hY₀'
  have hY₀'m : Measurable Y₀' := EV.j.continuous.measurable.comp hX₀'
  set G' : Ω' → EuclideanSpace ℝ (Fin p) := fun ω' =>
    WithLp.toLp 2 fun a => NegSobolev.eval (Zb (ts a) ω') (φ a) with hG'
  have hlawG' := gfb4_Zb_gaussian hT0 EV hEV.maxHyp P' G _ hG hGc hGz Zb hZb hZbm ts hts φ hmemφ
  have hSS : (Matrix.of fun a b => ∫ σ in Set.Icc 0 (min (ts a) (ts b)),
      covDensT (S.γ : ℝ) (qN S N) S.T (S.ρ N) σ
        (pullbackVec EV (ts a) σ (gfb4_ell m (φ a))) (pullbackVec EV (ts b) σ (gfb4_ell m (φ b)))) = Sy := by
    ext a b
    simp only [hSy, Matrix.of_apply]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    have := gfb4_cov_eq S M hMF N hm EV hEV (hts a) (hts b) hσ (hφ a) (hφ b)
    rw [this]
  have hind' : IndepFun G' Y₀' P' := by
    refine gfb4_indep_pairing hT0 EV hEV.maxHyp P' G G0 _ hG hG0m hGG Zb hZb hZbm Y₀' ?_ ts hts φ hmemφ
    refine indep_of_indep_of_le_left hGind ?_
    rw [show Y₀' = EV.j ∘ X₀' from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono EV.j.continuous.measurable.comap_le
  have hmeas_eval : ∀ (a : Fin p) (z : NegSobolev d m → ℝ), True := fun _ _ => trivial
  have hGym : Measurable Gy := by
    refine measurable_toLp_eval fun a => ?_
    exact ((continuous_eval_const (hmemφ a)).measurable.comp (hY.meas _)).sub
      ((continuous_eval_const (hmemU a)).measurable.comp hY₀)
  have hG'm : Measurable G' := measurable_toLp_eval fun a =>
    (continuous_eval_const (hmemφ a)).measurable.comp (hZbm _)
  have hlawG : P.map Gy = P'.map G' := by
    have h1 : P.map Gy = multivariateGaussian 0 Sy := hlawY
    rw [h1, ← hSS]
    exact hlawG'.symm
  -- the vectors
  set V : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
    NegSobolev.eval (Y (ts a) ω) (φ a) with hV
  set V' : Ω' → EuclideanSpace ℝ (Fin p) := fun ω' => WithLp.toLp 2 fun a =>
    NegSobolev.eval (EV.VE (ts a) 0 (EV.j (X₀' ω')) + Zb (ts a) ω') (φ a) with hV'
  have hVV : P.map V = P'.map V' := by
    refine map_eq_of_decomp P P' Gy Y₀ G' Y₀' W hW hGym hY₀ hG'm hY₀'m hindY hind' hlawG
      (by rw [← hlaw]) V V' (fun ω => ?_) (fun ω' => ?_)
    · ext a
      simp [hV, hGy, hWdef]
    · ext a
      have hadd : NegSobolev.eval (EV.VE (ts a) 0 (EV.j (X₀' ω')) + Zb (ts a) ω') (φ a) =
          NegSobolev.eval (EV.VE (ts a) 0 (EV.j (X₀' ω'))) (φ a) + NegSobolev.eval (Zb (ts a) ω') (φ a) := by
        rw [← gfb4_ell_apply (hmemφ a), map_add, gfb4_ell_apply (hmemφ a), gfb4_ell_apply (hmemφ a)]
      have hdual := hEV.dual 0 (ts a) le_rfl (hts a).1 (hts a).2 (EV.j (X₀' ω')) (φ a) (hφ a)
      simp only [hV', hG', hWdef, hY₀', PiLp.add_apply, WithLp.ofLp_toLp, hadd, hdual]
      ring
  -- the coordinates
  set Sc : EuclideanSpace ℝ (Fin p) → (Fin p → ℝ) :=
    fun v a => Lattice.jp (ks a).1 ^ (-m) * v a with hSc
  have hScm : Measurable Sc := by
    refine measurable_pi_iff.2 fun a => ?_
    exact (measurable_pi_apply a |>.comp (PiLp.continuous_ofLp 2 (fun _ : Fin p => ℝ)).measurable).const_mul _
  have e1 : (fun ω a => NegSobolev.coord (Y (ts a) ω) (ks a)) = Sc ∘ V := by
    funext ω a
    simp only [Function.comp, hSc, hV]
    rw [coord_eq_eval]
  have e2 : (fun ω' a => NegSobolev.coord (EV.VE (ts a) 0 (EV.j (X₀' ω')) + Zb (ts a) ω') (ks a)) = Sc ∘ V' := by
    funext ω' a
    simp only [Function.comp, hSc, hV']
    rw [coord_eq_eval]
  have hVm : Measurable V := measurable_toLp_eval fun a =>
    (continuous_eval_const (hmemφ a)).measurable.comp (hY.meas _)
  have hVm' : Measurable V' := measurable_toLp_eval fun a =>
    (continuous_eval_const (hmemφ a)).measurable.comp
      (((EV.VE (ts a) 0).continuous.comp EV.j.continuous).measurable.comp hX₀' |>.add (hZbm _))
  rw [e1, e2, ← Measure.map_map hScm hVm, ← Measure.map_map hScm hVm', hVV]

end HRS.GF
