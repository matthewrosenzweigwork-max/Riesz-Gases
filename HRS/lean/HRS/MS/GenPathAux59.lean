import HRS.MS.GenPathAux58

/-!
# S5.6 packet P10a: the hypotheses packets (trace moment, remainder moment) as `Prop`s; helper facts
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MP.RdRem HRS.Whole.AppendixA HRS.MS.S52

variable {d : ℕ}

/-- The conclusion of `s56_trace_moment` for a fixed `b` and constant `C`. -/
def S56TraceHyp (b : WholeBounds d) (C : ℝ) : Prop :=
  ∀ S : WholeSetup b, ∀ N : ℕ, 2 ≤ N → ∀ q : ℝ, 0 ≤ q → ∀ M₂ : ℝ, 0 ≤ M₂ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℝ≥0 → Ω → EucConfig d N),
      (∀ᵐ ζ ∂P, ∀ t ∈ Set.Icc (0 : ℝ) b.T, Function.Injective (X (Real.toNNReal t) ζ)) →
      AEMeasurable (fun p : Ω × ℝ => rieszModulatedEnergy d b.s (X (Real.toNNReal p.2) p.1)
        (HRS.Whole.withDensityReal (S.ρ N p.2)) + HRS.oN d b.s b.C₀ N)
        (P.prod (volume.restrict (Set.Icc 0 b.T))) →
      AEMeasurable (fun p : Ω × ℝ => secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal p.2) p.1)))
        (P.prod (volume.restrict (Set.Icc 0 b.T))) →
      (∀ t ∈ Set.Icc (0 : ℝ) b.T,
        ∫⁻ ζ, ENNReal.ofReal (secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal t) ζ))) ∂P ≤
          ENNReal.ofReal M₂ ∧
        ENNReal.ofReal (secondMomentOf (HRS.Whole.withDensityReal (S.ρ N t))) ≤ ENNReal.ofReal M₂) →
      S.energyMomentE N 1 P X ≠ ⊤ →
      ∀ (B₁ : ℝ → Ω → KSpace d b.m b.T →L[ℝ] KSpace d b.m b.T →L[ℝ] ℝ)
        (B₂ : ℝ → KSpace d b.m b.T →L[ℝ] KSpace d b.m b.T →L[ℝ] ℝ),
      (∀ r ∈ Set.Icc (0 : ℝ) b.T, ∀ ζ u v, B₁ r ζ u v = featureForm b.m b.T q
        (fun a => gradFeature (S.coeff N) b.m b.T a r) (HRS.Whole.empirical (X (Real.toNNReal r) ζ)) u v) →
      (∀ r ∈ Set.Icc (0 : ℝ) b.T, ∀ u v, B₂ r u v = featureForm b.m b.T q
        (fun a => gradFeature (S.coeff N) b.m b.T a r) (HRS.Whole.withDensityReal (S.ρ N r)) u v) →
      ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) b.T, ENNReal.ofReal (HRS.traceNormForm (B₁ r ζ - B₂ r))) ∂P ≤
        ENNReal.ofReal (C * q * generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N)

/-- The conclusion of `s56_rem_moment` for a fixed `b`, constant `C` and exponent `p`. -/
def S56RemHyp (b : WholeBounds d) (C p : ℝ) : Prop :=
  ∀ S : WholeSetup b, ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ) (X : ℝ≥0 → Ω → EucConfig d N), IsProgressive ℱ (ofNNRealTime X) →
      (∀ᵐ ζ ∂P, ∀ r ∈ Set.Icc (0 : ℝ) b.T, Function.Injective (X (Real.toNNReal r) ζ)) →
      (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) b.T, l2NormE (fun α : MultiIndex d =>
          S.σ N * ∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N)
            (propagatorW (S.coeff N) r t (oscTestFun b.m α)) (X (Real.toNNReal r) ζ) (S.ρ N r))) ^ p ∂P) ^
          (1 / p) ≤
        ENNReal.ofReal (C * S.σ N) * S.energyMomentE N p P X

theorem s56_trace_moment' (b₀ : WholeBounds d) (hb : b₀.Valid) :
    ∃ C₀min : ℝ, ∀ b : WholeBounds d, b = { b₀ with C₀ := b.C₀ } → C₀min ≤ b.C₀ →
      ∃ C : ℝ, 0 ≤ C ∧ S56TraceHyp b C := s56_trace_moment b₀ hb

theorem s56_rem_moment' (b₀ : WholeBounds d) (hb : b₀.Valid) (p : ℝ) (hp : p = 1 ∨ p = 2) :
    ∃ C₀min : ℝ, ∀ b : WholeBounds d, b = { b₀ with C₀ := b.C₀ } → C₀min ≤ b.C₀ →
      ∃ C : ℝ, 0 ≤ C ∧ S56RemHyp b (C) p := s56_rem_moment b₀ hb p hp

theorem s56_hS (b : WholeBounds d) (S : WholeSetup b) (N : ℕ) :
    ∀ r ∈ Set.Icc (0 : ℝ) b.T, IsFiniteMeasure (HRS.Whole.withDensityReal (S.ρ N r)) := fun r hr => by
  have := HRS.MS.Thm.cb_withDensityReal_isProb ((S.mf N).density r hr)
  infer_instance

theorem s56_q_nonneg (b : WholeBounds d) (S : WholeSetup b) (N : ℕ) (hN : 1 ≤ N) : 0 ≤ S.q N := by
  have hσ : 0 ≤ S.σ N := by
    unfold WholeSetup.σ sigmaScale
    have := S.hκ N
    have := (S.hinvβ N).1
    split_ifs
    · exact (S.hκ N).le
    · exact le_min (S.hκ N).le (Real.sqrt_nonneg _)
  unfold WholeSetup.q qScale
  have hinv : 0 ≤ S.invβ N := (S.hinvβ N).1
  split_ifs
  · exact le_rfl
  · have : (0 : ℝ) < N := by exact_mod_cast hN
    show 0 ≤ S.σ N ^ 2 * S.invβ N / N
    positivity

theorem s56_wpo_congr {m T : ℝ} {f f' : ℝ → OscDual d m} (h : ∀ t ∈ Set.Icc (0 : ℝ) T, f t = f' t) :
    windowPathOf m T 0 f = windowPathOf m T 0 f' := by
  unfold windowPathOf
  have h' : ∀ t : Set.Icc (0 : ℝ) T, f (0 + (t : ℝ)) = f' (0 + (t : ℝ)) := fun t => by simpa using h t t.2
  have hfun : (fun t : Set.Icc (0 : ℝ) T => f (0 + (t : ℝ))) = (fun t : Set.Icc (0 : ℝ) T => f' (0 + (t : ℝ))) :=
    funext h'
  exact HRS.GF.dite_continuousMap_congr _ _ hfun

theorem s56_window_recon_ae (b : WholeBounds d) (hT : 0 ≤ b.T) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G G' : ℝ → Ω → KSpace d b.m b.T) (s : ℕ → Set.Icc (0 : ℝ) b.T) (hs : DenseRange s)
    (hGc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => G t ζ) (Set.Icc 0 b.T))
    (hG'c : ∀ ζ, Continuous fun t => G' t ζ)
    (hae : ∀ τ ∈ Set.Icc (0 : ℝ) b.T, G τ =ᵐ[P] G' τ) (cp : Ω → OscPath d b.m b.T) :
    (fun ζ => windowPathOf b.m b.T 0 (fun t => s56Ext hT (cp ζ) t + reconstructPath b.m b.T G ζ t)) =ᵐ[P]
    (fun ζ => windowPathOf b.m b.T 0 (fun t => s56Ext hT (cp ζ) t + reconstructPath b.m b.T G' ζ t)) := by
  have hT' : b.T ∈ Set.Icc (0 : ℝ) b.T := ⟨hT, le_rfl⟩
  have h1 : ∀ᵐ ζ ∂P, ∀ n : ℕ, G (s n) ζ = G' (s n) ζ := ae_all_iff.2 fun n => hae _ (s n).2
  filter_upwards [h1, hae _ hT', hGc] with ζ hn hT'' hc
  refine s56_wpo_congr fun t ht => ?_
  congr 1
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) b.T => reconstructPath b.m b.T G ζ t :=
    HRS.MS.U9.u9_continuous_recon hT G ζ hc
  have hcont' : Continuous fun t : Set.Icc (0 : ℝ) b.T => reconstructPath b.m b.T G' ζ t :=
    HRS.MS.U9.u9_continuous_recon hT G' ζ (hG'c ζ).continuousOn
  have heq : (fun t : Set.Icc (0 : ℝ) b.T => reconstructPath b.m b.T G ζ t) =
      fun t : Set.Icc (0 : ℝ) b.T => reconstructPath b.m b.T G' ζ t := by
    refine hs.equalizer hcont hcont' (funext fun n => ?_)
    show reconstructPath b.m b.T G ζ (s n) = reconstructPath b.m b.T G' ζ (s n)
    unfold reconstructPath
    rw [hT'', hn n]
  exact congrFun heq ⟨t, ht⟩

theorem s56_indepFun_vec (b : WholeBounds d) {Ω₂ : Type*} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂)
    (s : ℕ → Set.Icc (0 : ℝ) b.T) (G : ℝ → Ω₂ → KSpace d b.m b.T) (c'' : Ω₂ → (ℕ × MultiIndex d → ℝ))
    (hind : Indep (MeasurableSpace.comap c'' inferInstance)
      (⨆ τ ∈ Set.Icc (0 : ℝ) b.T, MeasurableSpace.comap (G τ) inferInstance) P₂)
    {p : ℕ} (f : Fin p → ℕ × MultiIndex d) :
    IndepFun (fun ζ => (WithLp.toLp 2 fun a => s56FArr b s G ζ (f a) : EuclideanSpace ℝ (Fin p)))
      (fun ζ => (WithLp.toLp 2 fun a => c'' ζ (f a) : EuclideanSpace ℝ (Fin p))) P₂ := by
  set m : MeasurableSpace Ω₂ := ⨆ τ ∈ Set.Icc (0 : ℝ) b.T, MeasurableSpace.comap (G τ) inferInstance with hm
  have hle : ∀ t ∈ Set.Icc (0 : ℝ) b.T, MeasurableSpace.comap (G t) inferInstance ≤ m := fun t ht =>
    le_iSup₂ (f := fun τ (_ : τ ∈ Set.Icc (0 : ℝ) b.T) => MeasurableSpace.comap (G τ) inferInstance) t ht
  have hG : ∀ t ∈ Set.Icc (0 : ℝ) b.T, @Measurable Ω₂ (KSpace d b.m b.T) m _ (G t) := fun t ht =>
    Measurable.of_comap_le (hle t ht)
  have hΦ : @Measurable Ω₂ (Fin p → ℝ) m _ (fun ζ (a : Fin p) => s56FArr b s G ζ (f a)) := by
    refine @measurable_pi_iff Ω₂ (Fin p) (fun _ => ℝ) m _ _ |>.2 fun a => ?_
    exact @Measurable.comp Ω₂ (KSpace d b.m b.T) ℝ m _ _
      (fun x : KSpace d b.m b.T => inner ℝ x (s52y1 b.m b.T (s (f a).1) (f a).2)) (G (s (f a).1))
      (continuous_id.inner continuous_const).measurable (hG _ (s (f a).1).2)
  have hWF : @Measurable Ω₂ (EuclideanSpace ℝ (Fin p)) m _
      (fun ζ => (WithLp.toLp 2 fun a => s56FArr b s G ζ (f a) : EuclideanSpace ℝ (Fin p))) :=
    @Measurable.comp Ω₂ (Fin p → ℝ) (EuclideanSpace ℝ (Fin p)) m _ _
      (fun v : Fin p → ℝ => (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin p)))
      (fun ζ (a : Fin p) => s56FArr b s G ζ (f a))
      (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable hΦ
  have hWc : @Measurable Ω₂ (EuclideanSpace ℝ (Fin p)) (MeasurableSpace.comap c'' inferInstance) _
      (fun ζ => (WithLp.toLp 2 fun a => c'' ζ (f a) : EuclideanSpace ℝ (Fin p))) :=
    @Measurable.comp Ω₂ (ℕ × MultiIndex d → ℝ) (EuclideanSpace ℝ (Fin p)) (MeasurableSpace.comap c'' inferInstance) _ _
      (fun c : ℕ × MultiIndex d → ℝ => (WithLp.toLp 2 fun a => c (f a) : EuclideanSpace ℝ (Fin p))) c''
      ((PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
        (measurable_pi_iff.2 fun a => measurable_pi_apply (f a))) (comap_measurable c'')
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind.symm hWF.comap_le) hWc.comap_le

/-- The conclusion of `s56_compare` for fixed constants. -/
def S56CompareHyp (m T Cs Cw1 Cw2 : ℝ) : Prop :=
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (k0 : Ω → KSpace d m T), Measurable[ℱ 0] k0 →
      ∀ (M : ℝ → Ω → KSpace d m T) (Sg : ℝ → Ω → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)),
      IsHilbertMartingaleWithCovariation P ℱ T M Sg → (∀ t, Measurable (M t)) →
      ∀ (G : ℝ → Ω → KSpace d m T) (Cb : ℝ → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)),
      IsDetCovDensity T Cb → IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Cb r) →
      (∀ t, Measurable (G t)) →
      ∀ (Sd : ℝ → Ω → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)) (cost : ℝ → Ω → ℝ),
      IsHilbertMartingaleWithCovariation P ℱ T (fun τ ζ => M (min τ T) ζ - G (min τ T) ζ)
        (fun r ζ => if r ≤ T then Sd r ζ else 0) →
      (∀ᵐ ζ ∂P, ∀ r : ℝ, 0 ≤ r → r ≤ T → traceNormForm (Sd r ζ) ≤ cost r ζ) →
      (∀ᵐ ζ ∂P, ContinuousOn (fun t => M t ζ) (Set.Icc 0 T)) → (∀ᵐ ζ ∂P, M 0 ζ = 0) →
      (∀ᵐ ζ ∂P, ContinuousOn (fun t => G t ζ) (Set.Icc 0 T)) → (∀ᵐ ζ ∂P, G 0 ζ = 0) →
      ∀ (R : ℝ → Ω → OscDual d m), (∀ᵐ ζ ∂P, ContinuousOn (fun t => R t ζ) (Set.Icc 0 T)) →
      (∀ t, Measurable (R t)) → ∀ (Ξ Yc : Ω → OscPath d m T),
      AEMeasurable Ξ P → AEMeasurable Yc P →
      AEMeasurable (fun ζ => windowPathOf m T 0 (fun t => (k0 ζ).evalA t + reconstructPath m T G ζ t)) P →
      (∀ᵐ ζ ∂P, Ξ ζ = windowPathOf m T 0
        (fun t => (k0 ζ).evalA t + reconstructPath m T M ζ t + R t ζ)) →
      (ENNReal.ofReal (smoothDist 2 (law P Ξ) (law P Yc)) ≤
        ENNReal.ofReal Cs * ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal (traceNormForm (Sg r ζ - Cb r))) ∂P +
        ∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ∂P +
        ∫⁻ ζ, ‖windowPathOf m T 0 (fun t => (k0 ζ).evalA t + reconstructPath m T G ζ t) - Yc ζ‖ₑ ∂P) ∧
      (wassersteinE 1 (law P Ξ) (law P Yc) ≤
        ENNReal.ofReal Cw1 * (∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ζ)) ∂P) ^ (1 / 2 : ℝ) +
        (∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ^ (1 : ℝ) ∂P) ^ (1 / (1 : ℝ)) +
        (∫⁻ ζ, ENNReal.ofReal (‖windowPathOf m T 0 (fun t => (k0 ζ).evalA t + reconstructPath m T G ζ t) -
          Yc ζ‖ ^ (1 : ℝ)) ∂P) ^ (1 / (1 : ℝ))) ∧
      (wassersteinE 2 (law P Ξ) (law P Yc) ≤
        ENNReal.ofReal Cw2 * (∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ζ)) ∂P) ^ (1 / 2 : ℝ) +
        (∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) +
        (∫⁻ ζ, ENNReal.ofReal (‖windowPathOf m T 0 (fun t => (k0 ζ).evalA t + reconstructPath m T G ζ t) -
          Yc ζ‖ ^ (2 : ℝ)) ∂P) ^ (1 / (2 : ℝ)))

theorem s56_compare' (m T : ℝ) (hT : 0 ≤ T) :
    ∃ Cs Cw1 Cw2 : ℝ, 0 ≤ Cs ∧ 0 ≤ Cw1 ∧ 0 ≤ Cw2 ∧ S56CompareHyp (d := d) m T Cs Cw1 Cw2 :=
  s56_compare m T hT

end HRS.MS.GenPath
