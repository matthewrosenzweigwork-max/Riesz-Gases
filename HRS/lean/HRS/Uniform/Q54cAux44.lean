import HRS.Uniform.Q54cAux43

/-!
# Q54c, part 44: `Y` and `Ŷ` have the same finite-dimensional coordinate laws
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

namespace PdeSetup

variable {P : PdeSetup d} {D : DynData d} {ν₀ : ℝ} {μ : ℝ → Torus d → ℝ}

theorem Data.fdd_eq (h : P.Data D ν₀ μ) (hn2 : (d : ℝ) / 2 + 2 < (P.n : ℝ)) {q : ℝ} (hq : 0 ≤ q)
    (hT : 0 < P.T) {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] {mΩ' : MeasurableSpace Ω'}
    (PΩ : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure PΩ] [IsProbabilityMeasure P']
    (A : ℝ) (η₀ : Ω → NegSobolev d ((P.n : ℝ) + 2)) (hη₀ : Measurable η₀)
    (Y : ℝ → Ω → NegSobolev d ((P.n : ℝ) + 4))
    (hY : IsLinearFluctuationSolution PΩ D μ ((P.n : ℝ) + 4) q P.T
      (fun ω => A • NegSobolev.embed ((P.n : ℝ) + 4) (η₀ ω)) Y)
    (η' : Ω' → NegSobolev d ((P.n : ℝ) + 2)) (hη' : Measurable η')
    (hlaw : P'.map η' = PΩ.map η₀) {ℱ' : Filtration ℝ mΩ'}
    (G : ℝ → Ω' → NegSobolev d (P.n : ℝ))
    (hG : IsHilbertMartingaleWithCovariation P' ℱ' P.T G (fun r _ => covDens (P.n : ℝ) q P.T μ r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0) (hGm : ∀ τ, Measurable (G τ))
    (hind : Indep (MeasurableSpace.comap η' inferInstance)
      (⨆ τ ∈ {τ : ℝ | 0 ≤ τ ∧ τ ≤ P.T}, MeasurableSpace.comap (G τ) inferInstance) P') :
    ∀ (p : ℕ) (ts : Fin p → ℝ) (ks : Fin p → NonzeroLattice d), (∀ a, ts a ∈ Set.Icc 0 P.T) →
      PΩ.map (fun ω a => NegSobolev.coord (Y (ts a) ω) (ks a)) =
        P'.map (fun ω a => NegSobolev.coord ((P.pd D μ).Yproc P.T A η' G (ts a) ω) (ks a)) := by
  intro p ts ks hts
  have hspec := h.spec_pd
  set φ : Fin p → Torus d → ℝ := fun a => Torus.realMode (ks a) with hφdef
  have hφ : ∀ a, Torus.IsSmooth (φ a) := fun a => HRS.Uniform.Q48b.q48b_isSmooth_realMode (ks a)
  have hlev : (P.n : ℝ) + 4 ≤ P.lev := by rw [lev_eq]
  -- the common map `W`
  set W : NegSobolev d ((P.n : ℝ) + 4) → EuclideanSpace ℝ (Fin p) :=
    fun z => WithLp.toLp 2 fun a => NegSobolev.eval z (propagator D μ 0 (ts a) (φ a)) with hWdef
  have hmemU : ∀ a, MemSobolev ((P.n : ℝ) + 4) (propagator D μ 0 (ts a) (φ a)) := fun a =>
    h.memSob_prop (hts a) (hφ a) ⟨le_rfl, (hts a).1⟩ hlev
  have hW : Measurable W := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp (measurable_pi_iff.2 fun a => ?_)
    exact (continuous_eval_const (hmemU a)).measurable
  set Y₀ : Ω → NegSobolev d ((P.n : ℝ) + 4) :=
    fun ω => A • NegSobolev.embed ((P.n : ℝ) + 4) (η₀ ω) with hY₀
  set Y₀' : Ω' → NegSobolev d ((P.n : ℝ) + 4) :=
    fun ω => A • NegSobolev.embed ((P.n : ℝ) + 4) (η' ω) with hY₀'
  set Sy : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b =>
    2 * q * ∫ r in Set.Icc 0 (min (ts a) (ts b)), ∫ x,
      inner ℝ (Torus.grad (propagator D μ r (ts a) (φ a)) x)
        (Torus.grad (propagator D μ r (ts b) (φ b)) x) * μ r x with hSy
  set Gy : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
      NegSobolev.eval (Y (ts a) ω) (φ a) - NegSobolev.eval (Y₀ ω) (propagator D μ 0 (ts a) (φ a)) with hGy
  have hg : IndepFun Gy Y₀ PΩ ∧ law PΩ Gy = multivariateGaussian 0 Sy :=
    hY.gaussian_part p ts φ hts hφ
  obtain ⟨hindY, hlawY⟩ := hg
  -- the decomposition on `Ω'`
  have hw : ∀ t ∈ Set.Icc 0 P.T, ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ → ∀ z : NegSobolev d ((P.n : ℝ) + 2),
      inner ℝ z ((P.pd D μ).w t ψ) = NegSobolev.eval z (propagator D μ 0 t ψ) :=
    fun t ht ψ hψ z => h.hw ht hψ z
  obtain ⟨hind', hlaw'⟩ := Yproc_gaussian_part (PD := P.pd D μ) hspec hG hGc hGz hT A hη' hind
    (fun t ψ => propagator D μ 0 t ψ) hw ts hts φ hφ
  set Sy' : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun i j =>
    ∫ σ in Set.Icc 0 (min (ts i) (ts j)), covDens (P.n : ℝ) q P.T μ σ ((P.pd D μ).y (ts i) (φ i) σ)
      ((P.pd D μ).y (ts j) (φ j) σ) with hSy'
  have hSS : Sy = Sy' := by
    ext a b
    simp only [hSy, hSy', Matrix.of_apply]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    exact (h.cov_integrand_eq hn2 hq (hts a) (hts b) (hφ a) (hφ b) hσ).symm
  -- measurability
  have hYm : ∀ t, Measurable (Y t) := hY.meas
  have hY₀m : Measurable Y₀ := (measurable_Asmul_embed (a := (P.n : ℝ)) A).comp hη₀
  have hY₀m' : Measurable Y₀' := (measurable_Asmul_embed (a := (P.n : ℝ)) A).comp hη'
  have hmemφ : ∀ a, MemSobolev ((P.n : ℝ) + 4) (φ a) := fun a =>
    HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ a) _
  have hGym : Measurable Gy := by
    refine measurable_toLp_eval fun a => ?_
    exact ((continuous_eval_const (hmemφ a)).measurable.comp (hYm _)).sub
      ((continuous_eval_const (hmemU a)).measurable.comp hY₀m)
  have hYpm : ∀ t, Measurable ((P.pd D μ).Yproc P.T A η' G t) := fun t =>
    Yproc_measurable hspec hGm hGc hGz A hη' t
  set G' : Ω' → EuclideanSpace ℝ (Fin p) := procVec (P.pd D μ) P.T A η' G
    (fun t ψ => propagator D μ 0 t ψ) ts φ with hG'
  have hG'm : Measurable G' := by
    refine measurable_toLp_eval fun a => ?_
    exact ((continuous_eval_const (hmemφ a)).measurable.comp (hYpm _)).sub
      ((continuous_eval_const (hmemU a)).measurable.comp hY₀m')
  have hlawY₀ : PΩ.map Y₀ = P'.map Y₀' := by
    have e1 : Y₀ = (fun z : NegSobolev d ((P.n : ℝ) + 2) => A • NegSobolev.embed ((P.n : ℝ) + 4) z) ∘ η₀ := rfl
    have e2 : Y₀' = (fun z : NegSobolev d ((P.n : ℝ) + 2) => A • NegSobolev.embed ((P.n : ℝ) + 4) z) ∘ η' := rfl
    rw [e1, e2, ← Measure.map_map (measurable_Asmul_embed (a := (P.n : ℝ)) A) hη₀,
      ← Measure.map_map (measurable_Asmul_embed (a := (P.n : ℝ)) A) hη', hlaw]
  have hlawG : PΩ.map Gy = P'.map G' := by
    have h1 : PΩ.map Gy = multivariateGaussian 0 Sy := hlawY
    rw [h1, hSS]
    exact hlaw'.symm
  -- the vectors
  set V : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
    NegSobolev.eval (Y (ts a) ω) (φ a) with hV
  set V' : Ω' → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
    NegSobolev.eval ((P.pd D μ).Yproc P.T A η' G (ts a) ω) (φ a) with hV'
  have hVV : PΩ.map V = P'.map V' := by
    refine map_eq_of_decomp PΩ P' Gy Y₀ G' Y₀' W hW hGym hY₀m hG'm hY₀m' hindY hind' hlawG hlawY₀
      V V' (fun ω => ?_) (fun ω => ?_)
    · ext a; simp [hV, hGy, hWdef]
    · ext a; simp [hV', hG', procVec, hWdef, hY₀']
  -- the coordinates
  set Sc : EuclideanSpace ℝ (Fin p) → (Fin p → ℝ) :=
    fun v a => Lattice.jp (ks a).1 ^ (-((P.n : ℝ) + 4)) * v a with hSc
  have hScm : Measurable Sc := by
    refine measurable_pi_iff.2 fun a => ?_
    exact (measurable_pi_apply a |>.comp (PiLp.continuous_ofLp 2 (fun _ : Fin p => ℝ)).measurable).const_mul _
  have e1 : (fun ω a => NegSobolev.coord (Y (ts a) ω) (ks a)) = Sc ∘ V := by
    funext ω a
    simp only [Function.comp, hSc, hV]
    rw [coord_eq_eval]
  have e2 : (fun ω a => NegSobolev.coord ((P.pd D μ).Yproc P.T A η' G (ts a) ω) (ks a)) = Sc ∘ V' := by
    funext ω a
    simp only [Function.comp, hSc, hV']
    rw [coord_eq_eval]
  have hVm : Measurable V := measurable_toLp_eval fun a =>
    (continuous_eval_const (hmemφ a)).measurable.comp (hYm _)
  have hVm' : Measurable V' := measurable_toLp_eval fun a =>
    (continuous_eval_const (hmemφ a)).measurable.comp (hYpm _)
  rw [e1, e2, ← Measure.map_map hScm hVm, ← Measure.map_map hScm hVm', hVV]

end PdeSetup

end HRS.Uniform.Q54c
