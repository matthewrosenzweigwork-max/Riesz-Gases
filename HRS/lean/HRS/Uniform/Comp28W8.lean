import HRS.Uniform.Comp28W7

/-!
# COMP-28, Wasserstein part, W8: a stochastic convolution is a measurable functional of the integrator's path
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.Uniform.Q07c HRS.Uniform.Q48d

section Funct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- The Riemann-sum functional of a path along a partition. -/
def rsFun (V : ℝ → ℝ → H →L[ℝ] H) {T : ℝ} (hT : 0 ≤ T) (t : ℝ) {n : ℕ} (r : Fin (n + 1) → ℝ)
    (y : PathSp T H) : H :=
  ∑ i : Fin n, V t (r i.castSucc)
    (pcm y (Set.projIcc 0 T hT (r i.succ)) - pcm y (Set.projIcc 0 T hT (r i.castSucc)))

lemma continuous_rsFun (V : ℝ → ℝ → H →L[ℝ] H) {T : ℝ} (hT : 0 ≤ T) (t : ℝ) {n : ℕ}
    (r : Fin (n + 1) → ℝ) : Continuous (rsFun V hT t r) := by
  unfold rsFun
  refine continuous_finset_sum _ fun i _ => ?_
  refine (V t (r i.castSucc)).continuous.comp (Continuous.sub ?_ ?_)
  · have : Continuous fun y : C(Set.Icc (0 : ℝ) T, H) => y (Set.projIcc 0 T hT (r i.succ)) :=
      continuous_eval_const _
    exact this
  · have : Continuous fun y : C(Set.Icc (0 : ℝ) T, H) => y (Set.projIcc 0 T hT (r i.castSucc)) :=
      continuous_eval_const _
    exact this

lemma rsFun_windowPath (V : ℝ → ℝ → H →L[ℝ] H) {T : ℝ} (hT : 0 ≤ T) (t : ℝ) {n : ℕ}
    (r : Fin (n + 1) → ℝ) (hr : ∀ i, r i ∈ Set.Icc 0 T) {G : ℝ → Ω → H}
    (hGc : ∀ ω, Continuous fun s => G s ω) (ω : Ω) :
    rsFun V hT t r (windowPath 0 T G ω) =
      riemannSum V (ContinuousLinearMap.id ℝ H) G t r ω := by
  unfold rsFun riemannSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pcm_windowPath G (hGc ω).continuousOn, pcm_windowPath G (hGc ω).continuousOn,
    Set.projIcc_of_mem hT (hr _), Set.projIcc_of_mem hT (hr _)]
  rfl

/-- A stochastic convolution at a fixed time is (a.s.) a measurable functional of the integrator's path. -/
theorem exists_funct {T : ℝ} (hT : 0 ≤ T) {V : ℝ → ℝ → H →L[ℝ] H} {G : ℝ → Ω → H}
    (hGm : ∀ t, Measurable (G t)) (hGc : ∀ ω, Continuous fun s => G s ω) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) {Zt : Ω → H} (hZm : Measurable Zt)
    (hZ : IsStochConv P V (ContinuousLinearMap.id ℝ H) G 0 t Zt) :
    ∃ f : PathSp T H → H, Measurable f ∧ Zt =ᵐ[P] fun ω => f (windowPath 0 T G ω) := by
  classical
  have hDm : ∀ τ ∈ Set.Icc (0 : ℝ) t, AEStronglyMeasurable (G τ) P := fun τ _ =>
    (hGm τ).aestronglyMeasurable
  have hSC := (isStochConv_iff hZm.aestronglyMeasurable hDm).1 hZ
  have hpart : ∀ k : ℕ, ∃ (n : ℕ) (r : Fin (n + 1) → ℝ), r 0 = 0 ∧ r (Fin.last n) = t ∧ Monotone r ∧
      ∀ i : Fin n, r i.succ - r i.castSucc < 1 / ((k : ℝ) + 1) := fun k =>
    exists_part ht.1 (by positivity)
  choose n r h0 hl hm hmesh using hpart
  have hr : ∀ k i, r k i ∈ Set.Icc (0 : ℝ) T := fun k i => by
    have := mem_Icc_of_part (h0 k) (hl k) (hm k) i
    exact ⟨this.1, this.2.trans ht.2⟩
  set Rk : ℕ → Ω → H := fun k ω => riemannSum V (ContinuousLinearMap.id ℝ H) G t (r k) ω with hRk
  have hRkm : ∀ k, Measurable (Rk k) := by
    intro k
    simp only [hRk]
    simp_rw [riemannSum_id]
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (V t (r k i.castSucc)).continuous.measurable.comp ((hGm _).sub (hGm _))
  have hconv : Tendsto (fun k => eLpNorm (Rk k - Zt) 2 P) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨ε', hε'0, hpos, hε'⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have hε'pos : 0 < ε' := ENNReal.ofReal_pos.1 hpos
    obtain ⟨δ, hδ, hδ'⟩ := hSC ε' hε'pos
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine Filter.eventually_atTop.2 ⟨N, fun k hk => ?_⟩
    have hmesh' : ∀ i : Fin (n k), r k i.succ - r k i.castSucc < δ := fun i =>
      (hmesh k i).trans_le (by
        refine le_trans ?_ hN.le
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1))
    have := hδ' (n k) (r k) (h0 k) (hl k) (hm k) hmesh'
    rw [eLpNorm_sub_comm]
    exact (this.trans hε').le
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm (μ := P) (f := Rk) (g := Zt) (p := 2)
    (by norm_num) hconv
  obtain ⟨ns, hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  refine ⟨fun y => limUnder atTop (fun i => rsFun V hT t (r (ns i)) y), ?_, ?_⟩
  · exact (StronglyMeasurable.limUnder (fun i => (continuous_rsFun V hT t (r (ns i))).stronglyMeasurable)).measurable
  · filter_upwards [hae] with ω hω
    have : Tendsto (fun i => rsFun V hT t (r (ns i)) (windowPath 0 T G ω)) atTop (𝓝 (Zt ω)) := by
      refine hω.congr fun i => ?_
      simp only [hRk]
      rw [rsFun_windowPath V hT t (r (ns i)) (hr (ns i)) hGc ω]
    exact this.limUnder_eq.symm

/-- The stochastic convolution, as a path, is (a.s.) a measurable functional of the integrator's path. -/
theorem exists_path_funct {T : ℝ} (hT : 0 ≤ T) {V : ℝ → ℝ → H →L[ℝ] H} {G : ℝ → Ω → H}
    (hGm : ∀ t, Measurable (G t)) (hGc : ∀ ω, Continuous fun s => G s ω) {Zb : ℝ → Ω → H}
    (hZm : ∀ t, Measurable (Zb t)) (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 T))
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P V (ContinuousLinearMap.id ℝ H) G 0 t (Zb t)) :
    ∃ h : PathSp T H → PathSp T H, Measurable h ∧
      ∀ᵐ ω ∂P, windowPath 0 T Zb ω = h (windowPath 0 T G ω) := by
  classical
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  set s : ℕ → Set.Icc (0 : ℝ) T := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) T) with hsdef
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  have hemb := measurableEmbedding_pathEvals (H := H) T s hs
  obtain ⟨g, hgm, hg⟩ := hemb.exists_measurable_extend (g := id) measurable_id (fun _ => ⟨0⟩)
  have hf : ∀ n, ∃ f : PathSp T H → H, Measurable f ∧
      Zb (s n : ℝ) =ᵐ[P] fun ω => f (windowPath 0 T G ω) := fun n =>
    exists_funct hT hGm hGc (s n).2 (hZm _) (hZ _ (s n).2)
  choose f hfm hfae using hf
  refine ⟨fun y => g (fun n => f n y), hgm.comp (measurable_pi_iff.2 hfm), ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ n, Zb (s n : ℝ) ω = f n (windowPath 0 T G ω) := ae_all_iff.2 hfae
  filter_upwards [hall, hZc] with ω h1 h2
  have e1 := congrFun hg (windowPath 0 T Zb ω)
  simp only [Function.comp, id] at e1
  rw [← e1, pathEvals_windowPath s Zb h2]
  congr 1
  funext n
  exact h1 n

end Funct

end HRS.Uniform.Comp28
