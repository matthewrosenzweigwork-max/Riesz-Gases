import HRS.MD.EQLawPath4

/-!
# Packet EQ-LAW (chunk D): `eq_path_stationary_proof`

Relocated proof of `HRS.MD.EQ29.eq_path_stationary` (frozen with its `sorry` in `HRS/MD/EQ29Spec.lean`; the tie
`HRS/MD/EQLawPathTie.lean` checks that the statements agree).

Route (the repaired route of `EQ29Plan.md`, without Yamada-Watanabe and without Doob-Dynkin):
1. For a stationary Gibbs flow `(X, W)` on the horizon `u + T` the pair `J = (X_u, path of W_{u+·} - W_u)` takes values in the
   canonical space `Σ = Config × C(ℝ≥0, ℝ^{N×d})`; its law is `ℙ_{N,β} ⊗ 𝒲`, where `𝒲` is the law of the path of any Brownian
   filtration (STAT gives `law X_u = ℙ_{N,β}`; `X_u` is `ℱ_u`-measurable hence independent of the shifted Brownian path;
   the path law is the same for every Brownian filtration by the finite-dimensional distributions).  (`EQLawPath1`, `EQLawPath3`)
2. `particle_wellposed` on `(Σ, ℙ_{N,β} ⊗ 𝒲)` gives ONE strong solution `Xσ` of the canonical problem (`T + 1 > 0`).
3. The shifted flow `s ↦ X_{u+s}` is a strong solution on `(Ω, P)` (`eqlaw_isStrongSolution_shift`), and so is `Xσ ∘ J`
   (`eqlaw_isStrongSolution_comp`); pathwise uniqueness on `(Ω, P)` gives `X_{u+s} = Xσ_s ∘ J` a.s. (`eqlaw_flow_compare`).
4. `windowZeta` is therefore a.s. `Γ ∘ J` with the single functional `Γ` of `Xσ` (the centre is `ℙ_{N,β}` by STAT;
   `ζ_N` is continuous in the configuration, so `Γ` is a.e. measurable, `EQLawZeta`), and both laws equal `(ℙ_{N,β} ⊗ 𝒲).map Γ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace MD

namespace EQLawPath

open HRS.LZ HRS.Uniform HRS.Main HRS.MD.EQLawFlow

variable {d : ℕ}

theorem eq_path_stationary_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (m : ℝ) (hm : (d : ℝ) / 2 < m)
    (T : ℝ) (hT : 0 ≤ T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (u : ℝ) (hu : 0 ≤ u) (hX : IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X₀' : Ω' → Config d N) (W' : ℝ≥0 → Ω' → (Fin N → Euc d)) (X' : ℝ≥0 → Ω' → Config d N)
    (a : ℝ) (ha : 0 ≤ a) (hX' : IsStationaryGibbsFlow P' s hs0 hsd V β hβ (a + T) X₀' W' X') :
    law P (Main.windowZeta m T u P X) = law P' (Main.windowZeta m T a P' X') := by
  classical
  haveI : BorelSpace (Torus d) := Pi.borelSpace
  haveI : BorelSpace (Config d N) := Pi.borelSpace
  set G : Measure (Config d N) := canonicalGibbs (periodicRiesz d s) V N β with hG
  haveI hGp : IsProbabilityMeasure G := eqlaw_gibbs_prob hd hs0 hsd hV hβ (by omega)
  set D : DynData d := PDE.mfData d s hs0 hsd V β hβ with hD
  have hV2 : Torus.IsCk 2 D.V :=
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV).of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hM : Torus.SymNonpos D.M := eqlaw_symNonpos_neg_one
  have hb : IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z) :=
    liftedDrift_locLipschitz D (kernelLocal_of_two_le hd D.hs0 D.hsd).smoothOffZero hV2
  have hm' : (d : ℝ) < 2 * m := by linarith
  have hstr : IsStrongSolution P D (u + T) X₀ W X := by
    rcases hX.flow.flow with ⟨h, _⟩ | ⟨h1, _⟩
    · exact h
    · exfalso; omega
  have hstr' : IsStrongSolution P' D (a + T) X₀' W' X' := by
    rcases hX'.flow.flow with ⟨h, _⟩ | ⟨h1, _⟩
    · exact h
    · exfalso; omega
  have hstat : ∀ t : ℝ≥0, (t : ℝ) ≤ u + T → P.map (X t) = G :=
    Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ (u + T) hN P X₀ W X hX
  have hstat' : ∀ t : ℝ≥0, (t : ℝ) ≤ a + T → P'.map (X' t) = G :=
    Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ (a + T) hN P' X₀' W' X' hX'
  have hu' : ((Real.toNNReal u : ℝ≥0) : ℝ) = u := Real.coe_toNNReal u hu
  have ha' : ((Real.toNNReal a : ℝ≥0) : ℝ) = a := Real.coe_toNNReal a ha
  obtain ⟨ℱ1, W1, hBF1, hJ1, hmap1, hdrv1⟩ :=
    eqlaw_flow_canon hd hs0 hsd V hV hβ hN P hX (Real.toNNReal u) (by rw [hu']; linarith)
  obtain ⟨ℱ2, W2, hBF2, hJ2, hmap2, hdrv2⟩ :=
    eqlaw_flow_canon hd hs0 hsd V hV hβ hN P' hX' (Real.toNNReal a) (by rw [ha']; linarith)
  have hLL : P'.map (bfPath hBF2) = P.map (bfPath hBF1) := bf_path_law_eq hBF2 hBF1
  rw [hLL] at hmap2
  haveI : IsProbabilityMeasure (P.map (bfPath hBF1)) := inferInstance
  set Q : Measure (Sig d N) := G.prod (P.map (bfPath hBF1)) with hQ
  -- the canonical solution
  have hdist : ∀ᵐ σ ∂Q, σ.1 ∉ collisionSet d N := by
    have hmp : MeasurePreserving (Prod.fst : Sig d N → Config d N) Q G :=
      ⟨measurable_fst, by rw [hQ, Measure.map_fst_prod, measure_univ, one_smul]⟩
    exact hmp.quasiMeasurePreserving.ae (eqlaw_gibbs_ae_not_collision hd s V β N)
  have hBrQ : IsVectorBrownian Q (sigW d N) := by
    have := eqlaw_isVectorBrownian_map (P := P) _ hJ1 measurable_sigW continuous_sigW
      (isVectorBrownian_of_isBrownianFiltration P ℱ1 W1 hBF1)
    rw [hmap1] at this
    exact this
  have hwpath : Measurable fun (c : WSp d N) (t : ℝ≥0) (i : Fin N) =>
      (WithLp.toLp 2 fun j => c t (i, j) : Euc d) :=
    measurable_pi_iff.2 fun t => measurable_pi_iff.2 fun i => (WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.2 fun j => (measurable_pi_apply (i, j)).comp
        (ContinuousMap.measurable_eval t))
  have hindQ : IndepFun Prod.fst (fun σ : Sig d N => fun t => sigW d N t σ) Q :=
    indepFun_prod (μ := G) (ν := P.map (bfPath hBF1)) (X := id)
      (Y := fun (c : WSp d N) (t : ℝ≥0) (i : Fin N) => (WithLp.toLp 2 fun j => c t (i, j) : Euc d))
      measurable_id hwpath
  obtain ⟨⟨Xσ, hXσ⟩, -⟩ := particle_wellposed_proof Q D hd hN hM hV2 Prod.fst measurable_fst hdist
    (sigW d N) hBrQ hindQ (T + 1) (by linarith)
  have hXσ' : IsStrongSolution Q D T Prod.fst (sigW d N) Xσ :=
    eqlaw_isStrongSolution_mono (by linarith) hXσ
  -- comparison
  have hc1 := eqlaw_flow_compare hb P (Real.toNNReal u) (by rw [hu']; exact hstr) hBF1 hdrv1 hJ1
    hmap1 hXσ'
  have hc2 := eqlaw_flow_compare hb P' (Real.toNNReal a) (by rw [ha']; exact hstr') hBF2 hdrv2 hJ2
    hmap2 hXσ'
  have hw1 := eqlaw_window_eq (s := s) (V := V) (β := β) m T hu P G hstat hc1
  have hw2 := eqlaw_window_eq (s := s) (V := V) (β := β) m T ha P' G hstat' hc2
  -- the functional
  set Γ : Sig d N → PathSpace d m T := fun σ =>
    eqlaw_pathOf d m T (fun t : Set.Icc (0 : ℝ) T => zetaE m G (Xσ (Real.toNNReal t) σ)) with hΓ
  have hΓm : AEMeasurable Γ Q := by
    refine eqlaw_aemeasurable_pathOf Q T _ (fun t => ?_) ?_
    · exact (eqlaw_continuous_zetaE hm' (by omega) G).measurable.comp (hXσ'.adapted _)
    · filter_upwards [hXσ'.cont] with σ hσ
      have : Continuous fun t : ℝ≥0 => Xσ t σ := continuous_pi hσ
      exact ((eqlaw_continuous_zetaE hm' (by omega) G).comp this).comp
        (continuous_real_toNNReal.comp continuous_subtype_val)
  have e1 : law P (Main.windowZeta m T u P X) = Q.map Γ := by
    calc law P (Main.windowZeta m T u P X)
        = P.map (fun ω => Γ ((X (Real.toNNReal u) ω, bfPath hBF1 ω) : Sig d N)) :=
          Measure.map_congr hw1
      _ = (P.map (fun ω => ((X (Real.toNNReal u) ω, bfPath hBF1 ω) : Sig d N))).map Γ :=
          (AEMeasurable.map_map_of_aemeasurable (show AEMeasurable Γ (P.map _) by rw [hmap1]; exact hΓm)
            hJ1.aemeasurable).symm
      _ = Q.map Γ := by rw [hmap1]
  have e2 : law P' (Main.windowZeta m T a P' X') = Q.map Γ := by
    calc law P' (Main.windowZeta m T a P' X')
        = P'.map (fun ω => Γ ((X' (Real.toNNReal a) ω, bfPath hBF2 ω) : Sig d N)) :=
          Measure.map_congr hw2
      _ = (P'.map (fun ω => ((X' (Real.toNNReal a) ω, bfPath hBF2 ω) : Sig d N))).map Γ :=
          (AEMeasurable.map_map_of_aemeasurable (show AEMeasurable Γ (P'.map _) by rw [hmap2]; exact hΓm)
            hJ2.aemeasurable).symm
      _ = Q.map Γ := by rw [hmap2]
  rw [e1, e2]

end EQLawPath

end MD

end HRS
