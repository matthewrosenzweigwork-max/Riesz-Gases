import HRS.MS.FixEqP3Aux17

/-!
# S5.7 `fixed_equation` (worker S57P), part 30: the linear fluctuation solution of one family on `Ω × Ω₂`

`s57p_fam_solution`: `Y_t(ζ₁,ζ₂) = s57pI (η₀ ζ₁) t + X_t(ζ₂)` is a solution of the linear fluctuation equation
(`IsLinearFluctuationSolutionW`) on `(Ω × Ω₂, P ⊗ Q)` with initial field `a η₀ ∘ fst`, as soon as `X` is a noise field with the
Gaussian pairings of `s57p_fam_noise`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ} {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K : ℝ} {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ}
  {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ} {A Λc νbar : ℝ} {m : ℝ} {J : ℕ} {Ca Cd : ℝ}

theorem s57p_continuousOn_of_lip {E : Type*} [PseudoMetricSpace E] {f : ℝ → E} {S : Set ℝ} {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) ≤ L * |x - y|) : ContinuousOn f S := by
  refine (LipschitzOnWith.of_dist_le_mul (K := L.toNNReal) fun x hx y hy => ?_).continuousOn
  rw [Real.coe_toNNReal _ hL, Real.dist_eq]
  exact h x hx y hy

theorem s57p_fam_solution (hθ : IsUlCutoff θ) (hd : 1 ≤ d) (hP : (d : ℝ) < 2 * (((d : ℝ) + 3) / 2))
    (Fx : S57pFx θ T n K s M Q ν c ρ A Λc νbar)
    (hbd : S57pOrbBd (fixedEqCoeff s M Q ν c ρ) T n m J Ca Cd) (hCa : 0 ≤ Ca) (hCd : 0 ≤ Cd) {Cj : ℝ} (hCj : 0 ≤ Cj)
    (hjets : ∀ α : MultiIndex d, ContDiff ℝ ∞ (oscTestFun m α) ∧ ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x,
      ‖iteratedFDeriv ℝ l (oscTestFun m α) x‖ ≤ Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))
    (hJ : 3 * (n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) + 9 ≤ J) (hm : (J : ℝ) + d < m) (a q : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (η₀ : Ω → (Euc d → ℝ) → ℝ)
    (hη₀m : Measurable η₀) (hη₀ : ∀ᵐ ζ ∂P, IsBoundedLinearOnE n (((d : ℝ) + 3) / 2) (η₀ ζ))
    (hdual : ∀ᵐ ζ ∂P, dualNormE n (((d : ℝ) + 3) / 2) (η₀ ζ) < ⊤)
    {Ω₀ : Type} [MeasurableSpace Ω₀] (Qm : Measure Ω₀) [IsProbabilityMeasure Qm] {X : ℝ → Ω₀ → OscDual d m}
    (hXm : ∀ t, Measurable (X t)) (hXc : ∀ w, ContinuousOn (fun t => X t w) (Set.Icc 0 T))
    (hXlaw : ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ), (∀ a, ts a ∈ Set.Icc (0 : ℝ) T) →
        (∀ a, IsOscTest m (φ a)) →
        Qm.map (fun w => (WithLp.toLp 2 (fun a => OscDual.eval (X (ts a) w) (φ a)) : EuclideanSpace ℝ (Fin p))) =
          multivariateGaussian 0 (Matrix.of fun a b =>
            noiseCovW (fixedEqCoeff s M Q ν c ρ) q (ts a) (ts b) (φ a) (φ b))) :
    IsLinearFluctuationSolutionW (P.prod Qm) (fixedEqCoeff s M Q ν c ρ) m q T (fun ζ f => a * η₀ ζ.1 f)
      (fun t ζ => s57pI (fixedEqCoeff s M Q ν c ρ) m a (η₀ ζ.1) t + X t ζ.2) := by
  set C := fixedEqCoeff s M Q ν c ρ with hC
  have hsumJ := s57p_summable_J hd hm
  have hgood : ∀ᵐ ζ ∂P, IsBoundedLinearOnE n (((d : ℝ) + 3) / 2) (η₀ ζ) ∧
      dualNormE n (((d : ℝ) + 3) / 2) (η₀ ζ) < ⊤ := by
    filter_upwards [hη₀, hdual] with ζ h1 h2; exact ⟨h1, h2⟩
  have hgood2 : ∀ᵐ ζ ∂(P.prod Qm), IsBoundedLinearOnE n (((d : ℝ) + 3) / 2) (η₀ ζ.1) ∧
      dualNormE n (((d : ℝ) + 3) / 2) (η₀ ζ.1) < ⊤ := Measure.quasiMeasurePreserving_fst.ae hgood
  have hcoordm : ∀ t α, Measurable fun ζ : Ω × Ω₀ => a * η₀ ζ.1 (propagatorW C 0 t (oscTestFun m α)) := fun t α =>
    measurable_const.mul ((measurable_pi_iff.1 hη₀m _).comp measurable_fst)
  refine ⟨?_, fun t => ?_, fun p ts φ hts hφ => ?_⟩
  · filter_upwards [hgood2] with ζ hζ
    have hL := s57p_init_lip hP hζ.1 hζ.2 hbd hCa hCd a hsumJ
    refine ContinuousOn.add ?_ ((hXc ζ.2))
    refine s57p_continuousOn_of_lip (L := |a| * s57pD d n (((d : ℝ) + 3) / 2) (η₀ ζ.1) * Cd *
        Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m))) (by
          have := s57pD_nonneg d n (((d : ℝ) + 3) / 2) (η₀ ζ.1); positivity) (fun x hx y hy => ?_)
    rw [dist_eq_norm]
    exact hL.2 y hy x hx |>.trans (by rw [abs_sub_comm])
  · exact (s57p_measurable_ellVec (m := m) _ (fun α => hcoordm t α)).add (hXm t |>.comp measurable_snd)
  · -- the Gaussian part
    have hG : ∀ᵐ ζ ∂(P.prod Qm), (WithLp.toLp 2 (fun a' => OscDual.eval (s57pI C m a (η₀ ζ.1) (ts a') + X (ts a') ζ.2) (φ a') -
        a * η₀ ζ.1 (propagatorW C 0 (ts a') (φ a'))) : EuclideanSpace ℝ (Fin p)) =
        WithLp.toLp 2 (fun a' => OscDual.eval (X (ts a') ζ.2) (φ a')) := by
      filter_upwards [hgood2] with ζ hζ
      congr 1
      funext a'
      rw [s57p_eval_add (hφ a').2, s57p_init_eval hθ hd hP hζ.1 hζ.2 Fx hbd hCa hCd hCj hjets hJ hm a (hφ a') (hts a')]
      ring
    have hmeasG' : Measurable fun w => (WithLp.toLp 2 (fun a' => OscDual.eval (X (ts a') w) (φ a')) : EuclideanSpace ℝ (Fin p)) :=
      (WithLp.measurable_toLp 2 (Fin p → ℝ)).comp (measurable_pi_iff.2 fun a' =>
        (s57p_eval_cont (hφ a').2).measurable.comp (hXm (ts a')))
    refine ⟨?_, ?_⟩
    · have hind := (indepFun_prod (μ := P) (ν := Qm) (X := fun ζ => (fun f => a * η₀ ζ f)) (Y := fun w =>
        (WithLp.toLp 2 (fun a' => OscDual.eval (X (ts a') w) (φ a')) : EuclideanSpace ℝ (Fin p)))
        (measurable_pi_iff.2 fun f => measurable_const.mul (measurable_pi_iff.1 hη₀m f)) hmeasG').symm
      have hG' : (fun z : Ω × Ω₀ => (WithLp.toLp 2 (fun a' => OscDual.eval (X (ts a') z.2) (φ a')) : EuclideanSpace ℝ (Fin p))) =ᵐ[P.prod Qm]
          fun ζ => (WithLp.toLp 2 (fun a' => OscDual.eval (s57pI C m a (η₀ ζ.1) (ts a') + X (ts a') ζ.2) (φ a') -
            a * η₀ ζ.1 (propagatorW C 0 (ts a') (φ a'))) : EuclideanSpace ℝ (Fin p)) := by
        filter_upwards [hG] with ζ hζ; exact hζ.symm
      exact hind.congr hG' (Filter.EventuallyEq.refl _ _)
    · have e : law (P.prod Qm) (fun ζ => (WithLp.toLp 2 (fun a' => OscDual.eval (s57pI C m a (η₀ ζ.1) (ts a') + X (ts a') ζ.2) (φ a') -
          a * η₀ ζ.1 (propagatorW C 0 (ts a') (φ a'))) : EuclideanSpace ℝ (Fin p))) =
          Qm.map (fun w => (WithLp.toLp 2 (fun a' => OscDual.eval (X (ts a') w) (φ a')) : EuclideanSpace ℝ (Fin p))) := by
        unfold law
        rw [Measure.map_congr hG, ← Function.comp_def (fun w => (WithLp.toLp 2 (fun a' => OscDual.eval (X (ts a') w) (φ a')) : EuclideanSpace ℝ (Fin p))) Prod.snd,
          ← Measure.map_map hmeasG' measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
      rw [e]
      exact hXlaw p ts φ hts hφ

end HRS.MS.FixEq
