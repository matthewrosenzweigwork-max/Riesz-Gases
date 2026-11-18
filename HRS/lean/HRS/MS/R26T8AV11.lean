import HRS.MS.R26T8AV09
import HRS.MS.R26T8AV10
import HRS.MS.R26T8AV11a

/-!
# S8.2 observed-time layer, packet T8A.V11: maximal inequality for the reversed compact martingale

On `C([0,T];E)` put `Ψ_t γ = F(γ_t) - F(γ_0) - ∫_0^t LF(γ_r) dr` and `S γ = sup_{t ≤ T} |Ψ_t γ|`.  Since `LF` is measurable
and bounded (`r26t8a_v11a_LF`), `t ↦ Ψ_t γ` is continuous for every `γ`, so `S` equals a countable supremum and is Borel.
The forward process `M t = Ψ_t (Y)` and the reversed one `Mrev t = Ψ_t (Yrev)` are functionals of the two window path
representatives of V09, which have the same law; the bound is then V10 for the forward process.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

theorem r26t8a_v11_prim_cont (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ r, |g r| ≤ C) :
    Continuous fun t : ℝ => ∫ r in Set.Icc 0 t, g r := by
  have hint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => by
    refine (Measure.integrableOn_of_bounded (M := C) (by simp) hg.aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => ?_)).intervalIntegrable
    · rw [Real.norm_eq_abs]; exact hC r
  have h1 : Continuous fun b : ℝ => ∫ x in (0 : ℝ)..b, g x := intervalIntegral.continuous_primitive hint 0
  have h2 : Continuous fun t : ℝ => ∫ x in (0 : ℝ)..(max t 0), g x :=
    h1.comp (continuous_id.max continuous_const)
  have : (fun t : ℝ => ∫ r in Set.Icc 0 t, g r) = fun t : ℝ => ∫ x in (0 : ℝ)..(max t 0), g x := by
    funext t
    by_cases ht : 0 ≤ t
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht, max_eq_left ht]
    · push_neg at ht
      rw [Set.Icc_eq_empty (not_le.2 ht), max_eq_right ht.le]
      simp
  rw [this]
  exact h2

theorem r26t8a_reversed_compact_maximal (d N : ℕ) (hd : 2≤d) (hN : 2≤N)
    (a beta : ℝ) (ha : 0<a) (hbeta : 0<beta)
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N) (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X)
    (hrev : r26t8a_ReversibleWindows P X)
    (F : EucConfig d N → ℝ) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hFs : tsupport F⊆(eucCollisionSet d N)ᶜ) (u T : ℝ) (hu : 0≤u) (hT : 0<T) :
    let LF := particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F
    let Mrev := fun t w => F (X (u+T-t).toNNReal w)-F (X (u+T).toNNReal w)-
      ∫ r in Set.Icc 0 t, LF (X (u+T-r).toNNReal w)
    AEMeasurable (fun w => ⨆ t : Set.Icc (0:ℝ) T, ‖Mrev t w‖ₑ) P ∧
    r26t8a_scalarSupSq P T Mrev ≤ ENNReal.ofReal (8*T/beta)*
      ∫⁻ x, ∑ i, ‖HRS.MS.Phase2S82.configGrad F x i‖ₑ^2 ∂canonicalP d N a beta := by
  intro LF Mrev
  classical
  obtain ⟨hLFm, CLF, hCLF⟩ := r26t8a_v11a_LF d N (criticalS d) a beta F hF hFc hFs
  have hmeasX : ∀ t, AEMeasurable (X t) P := fun t => ((hX.solution (t : ℝ)).adapted t).aemeasurable
  have hcX : ∀ᵐ w ∂P, Continuous fun t => X t w := by
    filter_upwards [(hX.solution 1).cont] with w hw
    exact continuous_pi hw
  obtain ⟨Y, Yrev, hYm, hYrm, hlaw, hae⟩ := r26t8a_window_path_law P X hmeasX hcX hrev u T hu hT.le
  have hV10 := r26t8a_compact_martingale d N hd hN a beta ha hbeta P X0 W X hX F hF hFc hFs u T hu hT
  obtain ⟨hV10m, hV10b⟩ := hV10
  -- the functional on path space
  let pr : ℝ → Set.Icc (0 : ℝ) T := Set.projIcc 0 T hT.le
  have hprc : Continuous pr := continuous_projIcc
  let Psi : ℝ → C(Set.Icc (0 : ℝ) T, EucConfig d N) → ℝ := fun t γ =>
    F (γ (pr t)) - F (γ (pr 0)) - ∫ r in Set.Icc 0 t, LF (γ (pr r))
  have hgam : ∀ γ : C(Set.Icc (0 : ℝ) T, EucConfig d N), Measurable fun r : ℝ => LF (γ (pr r)) :=
    fun γ => hLFm.comp (γ.continuous.comp hprc).measurable
  have hPsic : ∀ γ, Continuous fun t => Psi t γ := fun γ => by
    have h1 : Continuous fun t : ℝ => F (γ (pr t)) := hF.continuous.comp (γ.continuous.comp hprc)
    have h2 := r26t8a_v11_prim_cont (fun r => LF (γ (pr r))) (hgam γ) CLF (fun r => hCLF _)
    exact (h1.sub continuous_const).sub h2
  obtain ⟨D, hDc, hDs, hDd⟩ := TopologicalSpace.exists_countable_dense_subset (Set.Icc (0 : ℝ) T)
  let S : C(Set.Icc (0 : ℝ) T, EucConfig d N) → ℝ≥0∞ := fun γ => ⨆ q ∈ D, ‖Psi q γ‖ₑ
  have hS : ∀ γ, S γ = ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Psi t γ‖ₑ := fun γ =>
    (iSup_Icc_enorm_eq_of_dense (hPsic γ) hDs hDd).symm
  have hPsim : ∀ t, Measurable (Psi t) := by
    intro t
    have hev : ∀ x : Set.Icc (0 : ℝ) T, Measurable fun γ : C(Set.Icc (0 : ℝ) T, EucConfig d N) => γ x :=
      fun x => (continuous_eval_const x).measurable
    have hH : Measurable fun p : C(Set.Icc (0 : ℝ) T, EucConfig d N) × ℝ => LF (p.1 (pr p.2)) :=
      hLFm.comp (continuous_eval.comp
        (continuous_fst.prodMk (hprc.comp continuous_snd))).measurable
    have hI : Measurable fun γ : C(Set.Icc (0 : ℝ) T, EucConfig d N) =>
        ∫ r in Set.Icc 0 t, LF (γ (pr r)) :=
      (hH.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Icc 0 t))).measurable
    exact (((hF.continuous.measurable.comp (hev _)).sub
      (hF.continuous.measurable.comp (hev _))).sub hI)
  have hSm : Measurable S := Measurable.biSup D hDc fun q _ => (hPsim q).enorm
  -- identification of the two processes with the path functionals
  have hsupeq : ∀ (Z : ℝ → Omega → ℝ) (γ : Omega → C(Set.Icc (0 : ℝ) T, EucConfig d N)),
      (∀ᵐ w ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Z t w = Psi t (γ w)) →
      ∀ᵐ w ∂P, (⨆ t : Set.Icc (0 : ℝ) T, ‖Z t w‖ₑ) = S (γ w) := by
    intro Z γ h
    filter_upwards [h] with w hw
    rw [hS, iSup_subtype' (p := fun t => t ∈ Set.Icc (0 : ℝ) T)
      (f := fun t _ => ‖Psi t (γ w)‖ₑ)]
    exact iSup_congr fun t => by rw [hw t t.2]
  have hprt : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) T), pr t = ⟨t, ht⟩ := fun t ht =>
    Set.projIcc_of_mem hT.le ht
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  have hY1 : ∀ᵐ w ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      F (X (u + t).toNNReal w) - F (X u.toNNReal w) -
        ∫ r in Set.Icc 0 t, LF (X (u + r).toNNReal w) = Psi t (Y w) := by
    filter_upwards [hae] with w hw t ht
    have e1 : Y w (pr t) = X (u + t).toNNReal w := by
      rw [hprt t ht]; exact (hw ⟨t, ht⟩).1
    have e0 : Y w (pr 0) = X u.toNNReal w := by
      rw [hprt 0 h0]; simpa using (hw ⟨0, h0⟩).1
    have hint : ∫ r in Set.Icc 0 t, LF (X (u + r).toNNReal w) =
        ∫ r in Set.Icc 0 t, LF (Y w (pr r)) := by
      refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      have hr' : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
      show LF (X (u + r).toNNReal w) = LF (Y w (pr r))
      rw [hprt r hr']
      exact congrArg LF (hw ⟨r, hr'⟩).1.symm
    show _ = F (Y w (pr t)) - F (Y w (pr 0)) - ∫ r in Set.Icc 0 t, LF (Y w (pr r))
    rw [e1, e0, hint]
  have hY2 : ∀ᵐ w ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Mrev t w = Psi t (Yrev w) := by
    filter_upwards [hae] with w hw t ht
    have e1 : Yrev w (pr t) = X (u + T - t).toNNReal w := by
      rw [hprt t ht]; exact (hw ⟨t, ht⟩).2
    have e0 : Yrev w (pr 0) = X (u + T).toNNReal w := by
      rw [hprt 0 h0]; simpa using (hw ⟨0, h0⟩).2
    have hint : ∫ r in Set.Icc 0 t, LF (X (u + T - r).toNNReal w) =
        ∫ r in Set.Icc 0 t, LF (Yrev w (pr r)) := by
      refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      have hr' : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
      show LF (X (u + T - r).toNNReal w) = LF (Yrev w (pr r))
      rw [hprt r hr']
      exact congrArg LF (hw ⟨r, hr'⟩).2.symm
    show F (X (u + T - t).toNNReal w) - F (X (u + T).toNNReal w) -
        ∫ r in Set.Icc 0 t, LF (X (u + T - r).toNNReal w) =
      F (Yrev w (pr t)) - F (Yrev w (pr 0)) - ∫ r in Set.Icc 0 t, LF (Yrev w (pr r))
    rw [e1, e0, hint]
  have hsF := hsupeq (fun t w => F (X (u + t).toNNReal w) - F (X u.toNNReal w) -
    ∫ r in Set.Icc 0 t, LF (X (u + r).toNNReal w)) Y hY1
  have hsR := hsupeq Mrev Yrev hY2
  refine ⟨((hSm.comp hYrm).aemeasurable).congr (hsR.mono fun w h => h.symm), ?_⟩
  unfold r26t8a_scalarSupSq at hV10b ⊢
  calc ∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) T, ‖Mrev t w‖ₑ) ^ 2 ∂P
      = ∫⁻ w, (S (Yrev w)) ^ 2 ∂P := lintegral_congr_ae (hsR.mono fun w h => by simp only [h])
    _ = ∫⁻ γ, (S γ) ^ 2 ∂(P.map Yrev) := (lintegral_map (hSm.pow_const 2) hYrm).symm
    _ = ∫⁻ γ, (S γ) ^ 2 ∂(P.map Y) := by rw [hlaw]
    _ = ∫⁻ w, (S (Y w)) ^ 2 ∂P := lintegral_map (hSm.pow_const 2) hYm
    _ = ∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) T, ‖F (X (u + (t : ℝ)).toNNReal w) - F (X u.toNNReal w) -
          ∫ r in Set.Icc (0 : ℝ) (t : ℝ), LF (X (u + r).toNNReal w)‖ₑ) ^ 2 ∂P :=
        lintegral_congr_ae (hsF.mono fun w h => by simp only [h])
    _ ≤ _ := hV10b

end HRS.MS.R26T8A

end
