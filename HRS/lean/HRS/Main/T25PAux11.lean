import HRS.Main.T25PAux10

/-!
# T25P, part 11: law identification of the linear process `Y` at level `m` (port of `GFB4Aux8-10` to a plain evolution)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q54c HRS.Uniform.Q07c HRS.Uniform.Q45 HRS.AdjK

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem t25p_pullback_eq_lpFun (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr.dyn ρ m Vev)
    {K : ℝ} (hK : 0 ≤ K) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (hKb : ‖Vev t r‖ ≤ K)
    {φ : Torus d → ℝ} (hφs : Torus.IsSmooth φ) :
    pullbackVec (HRS.Uniform.Comp28.plainData Vev) t r (gfb4_ell m φ) =
      lpFun m (propagator htr.dyn ρ r t φ) := by
  have hφm : MemSobolev m φ := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφs m
  have hmemU := t25p_memSobolev_propagator hd htr hdual hK hr hrt hKb hφs
  refine ext_inner_right ℝ fun x => ?_
  rw [pullback_inner]
  simp only [HRS.Uniform.Comp28.plainData_VE, HRS.Uniform.Comp28.plainData_j, ContinuousLinearMap.id_apply]
  rw [gfb4_ell_apply hφm, hdual r t hr hrt x φ hφs, eval_lpFun x hmemU, real_inner_comm]

theorem t25p_cov_eq (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m) {T' : ℝ} (hT' : 0 < T')
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr.dyn ρ m Vev)
    {K : ℝ} (hK : 0 ≤ K) (hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Vev t r‖ ≤ K)
    {q : ℝ} (hq : 0 ≤ q) {ta tb σ : ℝ} (hta : ta ∈ Set.Icc 0 T') (htb : tb ∈ Set.Icc 0 T')
    (hσ : σ ∈ Set.Icc 0 (min ta tb)) {φa φb : Torus d → ℝ} (hφa : Torus.IsSmooth φa)
    (hφb : Torus.IsSmooth φb) :
    covDensT m q T' ρ σ
      (pullbackVec (HRS.Uniform.Comp28.plainData Vev) ta σ (gfb4_ell m φa))
      (pullbackVec (HRS.Uniform.Comp28.plainData Vev) tb σ (gfb4_ell m φb)) =
    2 * q * ∫ x, inner ℝ (Torus.grad (propagator htr.dyn ρ σ ta φa) x)
      (Torus.grad (propagator htr.dyn ρ σ tb φb) x) * ρ σ x := by
  have hd1 : 1 ≤ d := by omega
  have hσa : σ ∈ Set.Icc 0 ta := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have hσb : σ ∈ Set.Icc 0 tb := ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
  have hσT : σ ∈ Set.Icc 0 T' := ⟨hσ.1, hσa.2.trans hta.2⟩
  simp only [covDensT, if_pos hσT]
  rw [t25p_pullback_eq_lpFun hd htr hdual hK hσ.1 hσa.2 (hKb σ ta hσ.1 hσa.2 hta.2) hφa,
    t25p_pullback_eq_lpFun hd htr hdual hK hσ.1 hσb.2 (hKb σ tb hσ.1 hσb.2 htb.2) hφb]
  have hjc := Q40b.q40b_jointCont hd1 htr T'
  have hMF := Q40b.q40b_meanField hd1 htr hT'
  have hρc : Continuous (ρ σ) :=
    hjc.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hσT, Set.mem_univ _⟩)
  have hρ0 := (hMF.density σ hσT).nonneg
  have hprop : ∀ {t : ℝ}, t ∈ Set.Icc 0 T' → σ ∈ Set.Icc 0 t → ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      MemSobolev m (propagator htr.dyn ρ σ t φ) ∧
      Continuous (propagator htr.dyn ρ σ t φ) ∧
      Torus.IsCk 1 (propagator htr.dyn ρ σ t φ) := by
    intro t ht hσt φ hφ
    have hck := adjkd_propagator_ck2 htr.dyn ρ hσt.1 hσt.2 φ
    refine ⟨t25p_memSobolev_propagator hd htr hdual hK hσt.1 hσt.2 (hKb σ t hσt.1 hσt.2 ht.2) hφ,
      Torus.continuous_of_continuous_lift hck.continuous, ?_⟩
    exact ContDiff.of_le hck (by norm_num)
  obtain ⟨ha1, ha2, ha3⟩ := hprop hta hσa φa hφa
  obtain ⟨hb1, hb2, hb3⟩ := hprop htb hσb φb hφb
  exact covForm_lpFun hm hq hρc hρ0 ha1 ha2 ha3 hb1 hb2 hb3

theorem t25p_fdd (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m) {T' : ℝ} (hT' : 0 < T')
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr.dyn ρ m Vev)
    (hplain : IsPlainEvolution Vev T') {K : ℝ} (hK : 0 ≤ K)
    (hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Vev t r‖ ≤ K)
    {Ω Ω' : Type} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (ℱ'' : Filtration ℝ mΩ') (X₀' : Ω' → NegSobolev d m) (hX₀' : Measurable X₀')
    (G G0 : ℝ → Ω' → NegSobolev d m)
    (hG : IsHilbertMartingaleWithCovariation P' ℱ'' T' G (fun r _ => covDensT m β⁻¹ T' ρ r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0)
    (hG0m : ∀ τ ∈ Set.Icc (0 : ℝ) T', Measurable (G0 τ))
    (hGG : ∀ τ ∈ Set.Icc (0 : ℝ) T', G τ =ᵐ[P'] G0 τ)
    (hGind : Indep (MeasurableSpace.comap X₀' inferInstance)
      (⨆ τ ∈ Set.Icc (0 : ℝ) T', MeasurableSpace.comap (G0 τ) inferInstance) P')
    (Zb : ℝ → Ω' → NegSobolev d m)
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P' Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zb t))
    (hZbm : ∀ t, Measurable (Zb t))
    (Y₀ : Ω → NegSobolev d m) (hY₀ : Measurable Y₀) (hlaw : P.map Y₀ = P'.map X₀')
    (Y : ℝ → Ω → NegSobolev d m)
    (hY : IsLinearFluctuationSolution P htr.dyn ρ m β⁻¹ T' Y₀ Y) :
    ∀ (p : ℕ) (ts : Fin p → ℝ) (ks : Fin p → NonzeroLattice d), (∀ a, ts a ∈ Set.Icc 0 T') →
      P.map (fun ω a => NegSobolev.coord (Y (ts a) ω) (ks a)) =
        P'.map (fun ω' a => NegSobolev.coord (Vev (ts a) 0 (X₀' ω') + Zb (ts a) ω') (ks a)) := by
  intro p ts ks hts
  have hq0 : 0 ≤ β⁻¹ := inv_nonneg.2 htr.hβ.le
  have hVc : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 y)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T'} := hplain.2.2
  set φ : Fin p → Torus d → ℝ := fun a => Torus.realMode (ks a) with hφdef
  have hφ : ∀ a, Torus.IsSmooth (φ a) := fun a => HRS.Uniform.Q48b.q48b_isSmooth_realMode (ks a)
  have hmemφ : ∀ a, MemSobolev m (φ a) := fun a =>
    HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ a) m
  have hmemU : ∀ a, MemSobolev m (propagator htr.dyn ρ 0 (ts a) (φ a)) := fun a =>
    t25p_memSobolev_propagator hd htr hdual hK le_rfl (hts a).1 (hKb 0 (ts a) le_rfl (hts a).1 (hts a).2) (hφ a)
  set W : NegSobolev d m → EuclideanSpace ℝ (Fin p) :=
    fun z => WithLp.toLp 2 fun a => NegSobolev.eval z (propagator htr.dyn ρ 0 (ts a) (φ a))
    with hWdef
  have hW : Measurable W := measurable_toLp_eval fun a => (continuous_eval_const (hmemU a)).measurable
  set Sy : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b =>
    2 * β⁻¹ * ∫ r in Set.Icc 0 (min (ts a) (ts b)), ∫ x,
      inner ℝ (Torus.grad (propagator htr.dyn ρ r (ts a) (φ a)) x)
        (Torus.grad (propagator htr.dyn ρ r (ts b) (φ b)) x) * ρ r x with hSy
  set Gy : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
    NegSobolev.eval (Y (ts a) ω) (φ a) -
      NegSobolev.eval (Y₀ ω) (propagator htr.dyn ρ 0 (ts a) (φ a)) with hGy
  obtain ⟨hindY, hlawY⟩ := hY.gaussian_part p ts φ hts hφ
  -- the Gaussian part on `Ω'`
  set G' : Ω' → EuclideanSpace ℝ (Fin p) := fun ω' =>
    WithLp.toLp 2 fun a => NegSobolev.eval (Zb (ts a) ω') (φ a) with hG'
  have hlawG' := t25p_Zb_gaussian hK hT' Vev hVc hKb P' G _ hG hGc hGz Zb hZb hZbm ts hts φ hmemφ
  have hSS : (Matrix.of fun a b => ∫ σ in Set.Icc 0 (min (ts a) (ts b)),
      covDensT m β⁻¹ T' ρ σ
        (pullbackVec (HRS.Uniform.Comp28.plainData Vev) (ts a) σ (gfb4_ell m (φ a)))
        (pullbackVec (HRS.Uniform.Comp28.plainData Vev) (ts b) σ (gfb4_ell m (φ b)))) = Sy := by
    ext a b
    simp only [hSy, Matrix.of_apply]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    have := t25p_cov_eq hd htr hm hT' hdual hK hKb hq0 (hts a) (hts b) hσ (hφ a) (hφ b)
    rw [this]
  have hind' : IndepFun G' X₀' P' := by
    refine t25p_indep_pairing hT' Vev P' G G0 _ hG hG0m hGG Zb hZb hZbm X₀' hGind ts hts φ hmemφ
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
  set Vv : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
    NegSobolev.eval (Y (ts a) ω) (φ a) with hVv
  set V' : Ω' → EuclideanSpace ℝ (Fin p) := fun ω' => WithLp.toLp 2 fun a =>
    NegSobolev.eval (Vev (ts a) 0 (X₀' ω') + Zb (ts a) ω') (φ a) with hV'
  have hVV : P.map Vv = P'.map V' := by
    refine map_eq_of_decomp P P' Gy Y₀ G' X₀' W hW hGym hY₀ hG'm hX₀' hindY hind' hlawG hlaw
      Vv V' (fun ω => ?_) (fun ω' => ?_)
    · ext a
      simp [hVv, hGy, hWdef]
    · ext a
      have hadd : NegSobolev.eval (Vev (ts a) 0 (X₀' ω') + Zb (ts a) ω') (φ a) =
          NegSobolev.eval (Vev (ts a) 0 (X₀' ω')) (φ a) + NegSobolev.eval (Zb (ts a) ω') (φ a) := by
        rw [← gfb4_ell_apply (hmemφ a), map_add, gfb4_ell_apply (hmemφ a), gfb4_ell_apply (hmemφ a)]
      have hd0 := hdual 0 (ts a) le_rfl (hts a).1 (X₀' ω') (φ a) (hφ a)
      simp only [hV', hG', hWdef, PiLp.add_apply, WithLp.ofLp_toLp, hadd, hd0]
      ring
  -- the coordinates
  set Sc : EuclideanSpace ℝ (Fin p) → (Fin p → ℝ) :=
    fun v a => Lattice.jp (ks a).1 ^ (-m) * v a with hSc
  have hScm : Measurable Sc := by
    refine measurable_pi_iff.2 fun a => ?_
    exact (measurable_pi_apply a |>.comp (PiLp.continuous_ofLp 2 (fun _ : Fin p => ℝ)).measurable).const_mul _
  have e1 : (fun ω a => NegSobolev.coord (Y (ts a) ω) (ks a)) = Sc ∘ Vv := by
    funext ω a
    simp only [Function.comp, hSc, hVv]
    rw [coord_eq_eval]
  have e2 : (fun ω' a => NegSobolev.coord (Vev (ts a) 0 (X₀' ω') + Zb (ts a) ω') (ks a)) = Sc ∘ V' := by
    funext ω' a
    simp only [Function.comp, hSc, hV']
    rw [coord_eq_eval]
  have hVm : Measurable Vv := measurable_toLp_eval fun a =>
    (continuous_eval_const (hmemφ a)).measurable.comp (hY.meas _)
  have hVm' : Measurable V' := measurable_toLp_eval fun a =>
    (continuous_eval_const (hmemφ a)).measurable.comp
      ((((Vev (ts a) 0).continuous).measurable.comp hX₀').add (hZbm _))
  rw [e1, e2, ← Measure.map_map hScm hVm, ← Measure.map_map hScm hVm', hVV]

theorem t25p_law_ident (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m) {T' : ℝ} (hT' : 0 < T')
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr.dyn ρ m Vev)
    (hplain : IsPlainEvolution Vev T') {K : ℝ} (hK : 0 ≤ K)
    (hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Vev t r‖ ≤ K)
    {Ω Ω' : Type} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (ℱ' : Filtration ℝ mΩ') (X₀' : Ω' → NegSobolev d m) (hX₀' : Measurable X₀')
    (G : ℝ → Ω' → NegSobolev d m)
    (hG : IsHilbertMartingaleWithCovariation P' ℱ' T' G (fun r _ => covDensT m β⁻¹ T' ρ r))
    (hGind : Indep (MeasurableSpace.comap X₀' inferInstance)
      (⨆ τ ∈ Set.Icc (0 : ℝ) T', MeasurableSpace.comap (G τ) inferInstance) P')
    (Zb : ℝ → Ω' → NegSobolev d m)
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P' Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zb t))
    (hZbc : ∀ᵐ ω ∂P', ContinuousOn (fun t => Zb t ω) (Set.Icc 0 T')) (hZbm : ∀ t, Measurable (Zb t))
    (Y₀ : Ω → NegSobolev d m) (hY₀ : Measurable Y₀) (hlaw : P.map Y₀ = P'.map X₀')
    (Y : ℝ → Ω → NegSobolev d m)
    (hY : IsLinearFluctuationSolution P htr.dyn ρ m β⁻¹ T' Y₀ Y) :
    law P (toPath m T' Y) =
      law P' (windowPath 0 T' (fun t ω' => Vev t 0 (X₀' ω') + Zb t ω')) := by
  have hCd0 : ∀ σ, σ ∉ Set.Icc 0 T' → covDensT m β⁻¹ T' ρ σ = 0 := by
    intro σ hσ
    simp [covDensT, hσ]
  obtain ⟨G', hG', hGc, hGz, hGG⟩ := gfb4_modify P' ℱ' hT'.le G
    (fun r => covDensT m β⁻¹ T' ρ r) hCd0 hG
  have hZb' : ∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P' Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G' 0 t (Zb t) :=
    fun t ht => gfb4_isStochConv_congr P' Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) ht.1
      (fun τ hτ => hGG τ ⟨hτ.1, hτ.2.trans ht.2⟩) (hZb t ht)
  have hG0m : ∀ τ ∈ Set.Icc (0 : ℝ) T', Measurable (G τ) := fun τ _ => measurable_of_isHM hG τ
  have hfdd := t25p_fdd hd htr hm hT' hdual hplain hK hKb P P' (gfb4_aug P' ℱ') X₀' hX₀' G' G hG' hGc hGz
    hG0m hGG hGind Zb hZb' hZbm Y₀ hY₀ hlaw Y hY
  have hmY := hY.meas
  have hmXb : ∀ t, Measurable (fun ω' => Vev t 0 (X₀' ω') + Zb t ω') := fun t =>
    (((Vev t 0).continuous).measurable.comp hX₀').add (hZbm t)
  have hcXb : ∀ᵐ ω' ∂P', ContinuousOn (fun t => Vev t 0 (X₀' ω') + Zb t ω') (Set.Icc 0 T') := by
    filter_upwards [hZbc] with ω' hω'
    exact (HRS.Uniform.Comp28.continuousOn_V_zero Vev hplain.2.2 (X₀' ω')).add hω'
  have key := Q54c.toPath_law_eq (m := m) (T := T') hT'.le P P' Y
    (fun t ω' => Vev t 0 (X₀' ω') + Zb t ω') hmY hmXb hY.cont hcXb hfdd
  rw [key]
  congr 1
  funext ω'
  exact toPath_eq_windowPath m T' _ ω'

end HRS.T25P
