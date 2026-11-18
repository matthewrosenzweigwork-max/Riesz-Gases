import HRS.MS.SpecAux58

/-!
# S8R: `IsHSIntegrand` for the empirical integrand of the stationary realization (S8.7, packet C3)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  For a stationary realization (`P.map (X t) = Q`, the canonical Gibbs law with the
static bundle `S45.S45Static`) with progressive coordinates, and `J = ∫ Fq dμ < ∞`:

* `s8p_marg_lintegral`: `∫⁻ G(X_t^i) dP ≤ C_s ∫⁻ G dμ`;
* `s8p_isHSIntegrand`: `IsHSIntegrand P ℱ T Φ` for every `T`, for
  `Φ r z (i,a) = √(2/(Nβ)) • s8p_Gv (X_{r}^i z) a`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s8p_fm_le {N : ℕ} {s a β Cs : ℝ} (hS : S45.S45Static d s a β Cs N) :
    HRS.Whole.firstMarginal (s8p_QN d s a β N) ≤ ENNReal.ofReal Cs • thermalMeasure d s a β := by
  obtain ⟨φ, hφm, hφeq, hφb, hφ2, hφn⟩ := hS.marg
  rw [hφeq]
  refine (withDensity_mono (g := fun _ => ENNReal.ofReal Cs)
    (Filter.Eventually.of_forall fun x => ?_)).trans (le_of_eq ?_)
  · exact ENNReal.ofReal_le_ofReal (hφb x).2
  · rw [withDensity_const]

theorem s8p_measurable_of_progressive {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}
    {β : Type*} [MeasurableSpace β] {f : ℝ → Ω → β} (hf : IsProgressive ℱ f) (r : ℝ) :
    Measurable (f r) := by
  have h := hf r
  have hg : Measurable[ℱ r, Subtype.instMeasurableSpace.prod (ℱ r)]
      (fun z : Ω => ((⟨r, Set.mem_Iic.2 le_rfl⟩ : Set.Iic r), z)) :=
    @Measurable.prodMk Ω (ℱ r) (Set.Iic r) Ω Subtype.instMeasurableSpace (ℱ r) _ _ measurable_const
      measurable_id
  exact (h.comp hg).mono (ℱ.le r) le_rfl

theorem s8p_marg_lintegral {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} (hN : 0 < N)
    {s a β Cs : ℝ} (hS : S45.S45Static d s a β Cs N) {Y : Ω → EucConfig d N} (hYm : Measurable Y)
    (hlaw : P.map Y = s8p_QN d s a β N) (i : Fin N) {G : Euc d → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ z, G (Y z i) ∂P ≤ ENNReal.ofReal Cs * ∫⁻ x, G x ∂(thermalMeasure d s a β) := by
  have hev : Measurable fun X : EucConfig d N => X i := measurable_pi_apply i
  have h1 : P.map (fun z => Y z i) = HRS.Whole.firstMarginal (s8p_QN d s a β N) := by
    calc P.map (fun z => Y z i) = (P.map Y).map (fun X : EucConfig d N => X i) :=
          (Measure.map_map hev hYm).symm
      _ = (s8p_QN d s a β N).map (fun X : EucConfig d N => X i) := by rw [hlaw]
      _ = _ := s8p_map_eval hN hS.exch i
  have h2 : ∫⁻ z, G (Y z i) ∂P = ∫⁻ x, G x ∂(P.map (fun z => Y z i)) :=
    (lintegral_map hG (g := fun z => Y z i) (hev.comp hYm)).symm
  rw [h2, h1]
  calc _ ≤ ∫⁻ x, G x ∂(ENNReal.ofReal Cs • thermalMeasure d s a β) := lintegral_mono' (s8p_fm_le hS) le_rfl
    _ = _ := lintegral_smul_measure _ _

theorem s8p_measurable_config {Ω : Type} {mΩ : MeasurableSpace Ω} {N : ℕ} {ℱ : Filtration ℝ mΩ}
    {X : ℝ≥0 → Ω → EucConfig d N}
    (hprog : ∀ i : Fin N, IsProgressive ℱ (fun r z => X (Real.toNNReal r) z i)) (r : ℝ) :
    Measurable (X (Real.toNNReal r)) :=
  measurable_pi_iff.2 fun i => s8p_measurable_of_progressive (hprog i) r

theorem s8p_isHSIntegrand {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) {s a β Cs : ℝ} (hS : S45.S45Static d s a β Cs N) (hβ : 0 < β)
    {om : ℕ → ℝ} {e : ℕ → Euc d → ℝ} (he : ∀ l, ContDiff ℝ ∞ (e l)) {τ : ℝ}
    (hJ : ∫⁻ x, s8p_Fq om e τ x ∂(thermalMeasure d s a β) < ⊤)
    (X : ℝ≥0 → Ω → EucConfig d N) (hlaw : ∀ t, P.map (X t) = s8p_QN d s a β N)
    (ℱ : Filtration ℝ mΩ)
    (hprog : ∀ i : Fin N, IsProgressive ℱ (fun r z => X (Real.toNNReal r) z i)) (T : ℝ) :
    IsHSIntegrand P ℱ T (fun r z (ia : Fin N × Fin d) =>
      Real.sqrt (2 / (N * β)) • s8p_Gv om e τ (X (Real.toNNReal r) z ia.1) ia.2) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨fun ia => ?_, fun r z => (hasSum_fintype _).summable, ?_⟩
  · exact isProgressive_comp_measurable (hprog ia.1)
      (g := fun x : Euc d => Real.sqrt (2 / (N * β)) • s8p_Gv om e τ x ia.2)
      ((s8p_measurable_Gv he τ ia.2).const_smul (Real.sqrt (2 / (N * β))))
  · unfold hsSqIntegralOn
    set c := ENNReal.ofReal (2 / (N * β)) with hc
    set J := ∫⁻ x, s8p_Fq om e τ x ∂(thermalMeasure d s a β) with hJdef
    set H : ℝ → Ω → ℝ≥0∞ := fun r z => c * ∑ i, s8p_Fq om e τ (X (Real.toNNReal r) z i) with hH
    have hpt : ∀ r z, ∑' k : Fin N × Fin d, ‖Real.sqrt (2 / (N * β)) •
        s8p_Gv om e τ (X (Real.toNNReal r) z k.1) k.2‖ₑ ^ 2 ≤ H r z := fun r z =>
      s8p_Phi_enorm_sum_le hN hβ om e τ (X (Real.toNNReal r) z)
    have hFm := s8p_measurable_Fq om he τ
    have hHm : Measurable (fun q : Ω × ℝ => H q.2 q.1) := by
      refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
      have := HRS.MRep.isProgressive_measurable_uncurry (ℱ := ℱ) (hprog i)
      exact hFm.comp (this.comp measurable_swap)
    calc ∫⁻ z, (∫⁻ r in Set.Icc 0 T, ∑' k : Fin N × Fin d, ‖Real.sqrt (2 / (N * β)) •
          s8p_Gv om e τ (X (Real.toNNReal r) z k.1) k.2‖ₑ ^ 2) ∂P
        ≤ ∫⁻ z, (∫⁻ r in Set.Icc 0 T, H r z) ∂P := by
          refine lintegral_mono fun z => ?_
          exact lintegral_mono fun r => hpt r z
      _ = ∫⁻ r in Set.Icc 0 T, (∫⁻ z, H r z ∂P) := by
          refine lintegral_lintegral_swap ?_
          exact hHm.aemeasurable
      _ ≤ ∫⁻ r in Set.Icc 0 T, c * (N * (ENNReal.ofReal Cs * J)) := by
          refine lintegral_mono fun r => ?_
          have hXm := s8p_measurable_config hprog r
          simp only [hH]
          have hterm : ∀ i : Fin N, Measurable fun z => s8p_Fq om e τ (X (Real.toNNReal r) z i) :=
            fun i => hFm.comp ((measurable_pi_apply i).comp hXm)
          rw [lintegral_const_mul (f := fun z => ∑ i : Fin N, s8p_Fq om e τ (X (Real.toNNReal r) z i))
              c (Finset.measurable_sum _ fun i _ => hterm i),
            lintegral_finsetSum _ fun i _ => hterm i]
          refine mul_le_mul_right ?_ _
          calc ∑ i : Fin N, ∫⁻ z, s8p_Fq om e τ (X (Real.toNNReal r) z i) ∂P
              ≤ ∑ i : Fin N, ENNReal.ofReal Cs * J := Finset.sum_le_sum fun i _ =>
                s8p_marg_lintegral hN hS hXm (hlaw _) i hFm
            _ = N * (ENNReal.ofReal Cs * J) := by
                simp [Finset.sum_const, nsmul_eq_mul]
      _ < ⊤ := by
          rw [setLIntegral_const, Real.volume_Icc]
          refine ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top
          refine ENNReal.mul_lt_top (by simp [hc]) (ENNReal.mul_lt_top (by simp) ?_)
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ

end HRS.MS.Spec
