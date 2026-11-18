import HRS.MS.R2InterpAux78

/-!
# S10.2 (worker S102), part 79 (packet M3): integrability of the covariance densities `hh2` along the particle paths

For a configuration path continuous in time, `u ↦ η_N^u(∇U^{u,τ_i}φ_i·∇U^{u,τ_j}φ_j)` is continuous on `[0, τ_i ∧ τ_j]`; hence `hh2` is integrable on `[0,T]`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}

theorem s102_grad_jointCont {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f)
    (a : Fin d) : Continuous fun p : Icc (0 : ℝ) t × Euc d => gradient (f p.1) p.2 a := by
  have hc := hf.cont_c2 1 (by norm_num)
  have := (HRS.MC.Sec7.S7PIL.S7PIL_ev (fun _ : Fin 1 => (EuclideanSpace.single a (1 : ℝ) : Euc d))).continuous.comp hc
  refine this.congr fun p => ?_
  simp [HRS.MC.Sec7.S7PIL.S7PIL_ev_apply, iteratedFDeriv_one_apply, s102_gradient_apply]

theorem s102_hh2_integrable (hs : S102Std C m T r c) (hT : 0 < T) (L : ℕ) {N : ℕ} (hN : 0 < N) (μ : Measure (Euc d))
    (hμ : ∀ u ∈ Icc (0 : ℝ) T, ∀ g : Euc d → ℝ, HRS.Whole.pair μ g = ∫ x, g x * C.ρ u x)
    {Ω : Type} (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) (hX : ∀ i, Continuous fun t : ℝ≥0 => X t ζ i)
    (i j : Fin (s102_q d L)) :
    IntegrableOn (s102_hh2 C m (s102_tauk hT L) (s102_alk L) (s102_etaf μ X ζ) i j) (Icc 0 T) := by
  classical
  set mn : ℝ := min (s102_tk hT L i) (s102_tk hT L j) with hmn
  have hmnT : mn ≤ T := (min_le_left _ _).trans (s102_tauk hT L i).2.2
  have hmn0 : 0 ≤ mn := le_min (s102_tauk hT L i).2.1 (s102_tauk hT L j).2.1
  have hi : s102_tk hT L i ∈ Icc (0 : ℝ) T := (s102_tauk hT L i).2
  have hj : s102_tk hT L j ∈ Icc (0 : ℝ) T := (s102_tauk hT L j).2
  have hF1 := s102_propagator_classical (hs.hcls (s102_alk L i) _ hi)
  have hF2 := s102_propagator_classical (hs.hcls (s102_alk L j) _ hj)
  have hsub1 : Icc 0 mn ⊆ Icc 0 (s102_tk hT L i) := Icc_subset_Icc le_rfl (min_le_left _ _)
  have hsub2 : Icc 0 mn ⊆ Icc 0 (s102_tk hT L j) := Icc_subset_Icc le_rfl (min_le_right _ _)
  -- continuity of `u ↦ g(u, X^k_u)`
  have hk : ∀ k : Fin N, ContinuousOn (fun u : ℝ =>
      inner ℝ (gradient (propagatorW C u (s102_tk hT L i) (oscTestFun m (s102_alk L i))) (X u.toNNReal ζ k))
        (gradient (propagatorW C u (s102_tk hT L j) (oscTestFun m (s102_alk L j))) (X u.toNNReal ζ k))) (Icc 0 mn) := by
    intro k
    rw [continuousOn_iff_continuous_restrict]
    have hpath : Continuous fun u : Icc (0 : ℝ) mn => X (u : ℝ).toNNReal ζ k :=
      (hX k).comp (continuous_real_toNNReal.comp continuous_subtype_val)
    simp_rw [s102_inner_eq_sum]
    refine continuous_finsetSum _ fun a _ => ?_
    have h1 := s102_grad_jointCont hF1 a
    have h2 := s102_grad_jointCont hF2 a
    have p1 : Continuous fun u : Icc (0 : ℝ) mn => ((⟨u.1, hsub1 u.2⟩ : Icc (0 : ℝ) (s102_tk hT L i)), X (u : ℝ).toNNReal ζ k) :=
      (continuous_subtype_val.subtype_mk _).prodMk hpath
    have p2 : Continuous fun u : Icc (0 : ℝ) mn => ((⟨u.1, hsub2 u.2⟩ : Icc (0 : ℝ) (s102_tk hT L j)), X (u : ℝ).toNNReal ζ k) :=
      (continuous_subtype_val.subtype_mk _).prodMk hpath
    exact (h1.comp p1).mul (h2.comp p2)
  have hgram := s102_gram_cont hT L hs.hcls (C.ρ 0) hs.hint hs.hstat i j
  have hcont : ContinuousOn (fun u : ℝ => s102_etaf μ X ζ u (fun x =>
      inner ℝ (gradient (propagatorW C u (s102_tk hT L i) (oscTestFun m (s102_alk L i))) x)
        (gradient (propagatorW C u (s102_tk hT L j) (oscTestFun m (s102_alk L j))) x))) (Icc 0 mn) := by
    have hfun : ∀ u ∈ Icc 0 mn, s102_etaf μ X ζ u (fun x =>
        inner ℝ (gradient (propagatorW C u (s102_tk hT L i) (oscTestFun m (s102_alk L i))) x)
          (gradient (propagatorW C u (s102_tk hT L j) (oscTestFun m (s102_alk L j))) x)) =
        Real.sqrt N * ((N : ℝ)⁻¹ * ∑ k : Fin N, inner ℝ
          (gradient (propagatorW C u (s102_tk hT L i) (oscTestFun m (s102_alk L i))) (X u.toNNReal ζ k))
          (gradient (propagatorW C u (s102_tk hT L j) (oscTestFun m (s102_alk L j))) (X u.toNNReal ζ k)) -
          s102_gram C m hT L u i j) := by
      intro u hu
      have huT : u ∈ Icc (0 : ℝ) T := ⟨hu.1, hu.2.trans hmnT⟩
      unfold s102_etaf
      rw [HRS.Whole.pair_empirical hN, hμ u huT]
      rfl
    refine ContinuousOn.congr ?_ hfun
    refine continuousOn_const.mul (ContinuousOn.sub ?_ hgram)
    exact continuousOn_const.mul (continuousOn_finsetSum _ fun k _ => hk k)
  have hI : IntegrableOn (fun u => s102_etaf μ X ζ u (fun x =>
      inner ℝ (gradient (propagatorW C u (s102_tk hT L i) (oscTestFun m (s102_alk L i))) x)
        (gradient (propagatorW C u (s102_tk hT L j) (oscTestFun m (s102_alk L j))) x))) (Icc 0 mn) :=
    hcont.integrableOn_Icc
  unfold s102_hh2
  refine (integrable_indicator_iff measurableSet_Iic).2 ?_
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Iic]
  refine hI.mono_set ?_
  intro u hu
  exact ⟨hu.2.1, hu.1⟩

end HRS.MS.R2Interp

end
