import HRS.MS.WsPrepQ4

/-!
# S21S packet M5: the reconstructed Gaussian path of the moving window: independence from the initial array and finite-dimensional laws

`s21mPath0`: the initial path `K_b = A(k₀)(·)`, `k₀ = s105K0`, of the window started at `b` (the transported initial particle field).
`s21m_recon_indep`: the window reconstruction of a Gaussian martingale `G` with covariation density `s21mDb` is independent of any `ξ` independent of `σ(G_τ)`.
`s21m_recon_fdd`: the finite-dimensional laws of the reconstructed window path are the centered Gaussians with covariance `noiseCovW` at `(b+t, b+t')`
(moving analogue of `s21_recon_indep`, `s21_recon_fdd`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S21m

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem HRS.MH.DualityRd HRS.MS.R2GenInit
  HRS.Uniform.Q54c HRS.GF

variable {d : ℕ}

/-- The initial path `t ↦ A(k_0)(t)` of the window started at `b`. -/
def s21mPath0 (C : WholeCoeff d) (m T b σ : ℝ) (hT : 0 ≤ T) (ρ0 : Euc d → ℝ) {N : ℕ} {Ω : Type*}
    (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) : OscPath d m T :=
  s56EvalPath hT (s105K0 C m T b σ ρ0 X ζ)

theorem s21m_FArr_range {s a β T b : ℝ} {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) (hb : 0 ≤ b)
    (q : ℝ) (hq : 0 ≤ q)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {G : ℝ → Ω → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T}
    (hG : IsHilbertMartingaleWithCovariation P ℱ (b + T) G (fun r _ =>
      s21mDb _ hS.hF hS.hpAll q hq r))
    (s' : ℕ → Set.Icc (0 : ℝ) T) :
    ∀ᵐ ζ ∂P, s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G ζ = fun i =>
      OscDual.coord (reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => G (b + τ) ζ) ζ (s' i.1)) i.2 := by
  have : ∀ i : ℕ × MultiIndex d, ∀ᵐ ζ ∂P,
      OscDual.coord (reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => G (b + τ) ζ) ζ (s' i.1)) i.2 =
        inner ℝ (G (b + s' i.1) ζ) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (s' i.1) i.2) := fun i =>
    s21m_recon_coord_eq hS hb q hq hG (s' i.1).2 i.2
  filter_upwards [ae_all_iff.2 this] with ζ hζ
  funext i
  exact (hζ i).symm

theorem s21m_recon_indep {s a β T b : ℝ} {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) (hb : 0 ≤ b)
    (hT : 0 < T) (q : ℝ) (hq : 0 ≤ q) {Ω₂ : Type} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂)
    [IsProbabilityMeasure P₂] {ℱ₂ : Filtration ℝ ‹MeasurableSpace Ω₂›}
    {G : ℝ → Ω₂ → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T}
    (hG : IsHilbertMartingaleWithCovariation P₂ ℱ₂ (b + T) G (fun r _ => s21mDb _ hS.hF hS.hpAll q hq r))
    (hGm : ∀ t, Measurable (G t)) {E' : Type} [mE : MeasurableSpace E'] (ξ : Ω₂ → E')
    (hind : Indep (MeasurableSpace.comap ξ mE)
      (⨆ τ ∈ Set.Icc (0 : ℝ) (b + T), MeasurableSpace.comap (G τ) inferInstance) P₂) :
    IndepFun ξ (fun ζ => windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0
      (fun t => reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => G (b + τ) ζ) ζ t)) P₂ := by
  have hT0 : 0 ≤ T := hT.le
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT0⟩⟩
  set s' : ℕ → Set.Icc (0 : ℝ) T := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) T) with hsdef
  have hs : DenseRange s' := TopologicalSpace.denseRange_denseSeq _
  have hemb := s56_measurableEmbedding_pathCoords (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T s' hs
  obtain ⟨g, hgm, hg⟩ := hemb.exists_measurable_extend (g := id) measurable_id (fun _ => ⟨0⟩)
  set m : MeasurableSpace Ω₂ := ⨆ τ ∈ Set.Icc (0 : ℝ) (b + T), MeasurableSpace.comap (G τ) inferInstance with hm
  have hle : ∀ t ∈ Set.Icc (0 : ℝ) (b + T), MeasurableSpace.comap (G t) inferInstance ≤ m := fun t ht =>
    le_iSup₂ (f := fun τ (_ : τ ∈ Set.Icc (0 : ℝ) (b + T)) => MeasurableSpace.comap (G τ) inferInstance) t ht
  have hG' : ∀ t ∈ Set.Icc (0 : ℝ) (b + T), @Measurable Ω₂ (KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T) m _ (G t) :=
    fun t ht => Measurable.of_comap_le (hle t ht)
  have hArr : @Measurable Ω₂ (ℕ × MultiIndex d → ℝ) m _ (s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G) := by
    refine @measurable_pi_iff Ω₂ (ℕ × MultiIndex d) (fun _ => ℝ) m _ _ |>.2 fun i => ?_
    exact @Measurable.comp Ω₂ (KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T) ℝ m _ _
      (fun x : KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T => inner ℝ x (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (s' i.1) i.2))
      (G (b + s' i.1)) (continuous_id.inner continuous_const).measurable
      (hG' _ ⟨by linarith [(s' i.1).2.1], by linarith [(s' i.1).2.2]⟩)
  have hgA : @Measurable Ω₂ (OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T) m _
      (fun ζ => g (s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G ζ)) :=
    @Measurable.comp Ω₂ (ℕ × MultiIndex d → ℝ) (OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T) m _ _ g
      (s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G) hgm hArr
  have hae : (fun ζ => windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0
      (fun t => reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => G (b + τ) ζ) ζ t)) =ᵐ[P₂]
      fun ζ => g (s105FArr ((wholeSpaceIndex d : ℕ) : ℝ) T b s' G ζ) := by
    filter_upwards [s21m_FArr_range hS hb q hq hG s', hG.cont] with ζ h1 hc
    have hshift : ContinuousOn (fun τ => G (b + τ) ζ) (Set.Icc 0 T) :=
      hc.comp (by fun_prop) (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hrc : ContinuousOn (fun t => reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
        (fun τ ζ => G (b + τ) ζ) ζ t) (Set.Icc 0 T) :=
      continuousOn_iff_continuous_domRestrict.2 (HRS.MS.U9.u9_continuous_recon hT0 _ ζ hshift)
    have h2 := s56_pathCoords_windowPathOf (d := d) (m := ((wholeSpaceIndex d : ℕ) : ℝ)) (T := T) s'
      (fun t ζ => reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => G (b + τ) ζ) ζ t) hrc
    rw [h1, ← h2]
    exact (congrFun hg _).symm
  refine IndepFun.congr ?_ Filter.EventuallyEq.rfl hae.symm
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right hind hgA.comap_le

theorem s21m_recon_fdd {s a β T b : ℝ} {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) (hb : 0 ≤ b)
    (hT : 0 < T) (q : ℝ) (hq : 0 ≤ q) {Ω₂ : Type} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂)
    [IsProbabilityMeasure P₂] {ℱ₂ : Filtration ℝ ‹MeasurableSpace Ω₂›}
    {G : ℝ → Ω₂ → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T}
    (hG : IsHilbertMartingaleWithCovariation P₂ ℱ₂ (b + T) G (fun r _ => s21mDb _ hS.hF hS.hpAll q hq r))
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d) :
    P₂.map (fun ζ => (WithLp.toLp 2 fun i : Fin p => OscDual.coord (OscPath.at'
        (windowPathOf ((wholeSpaceIndex d : ℕ) : ℝ) T 0 (fun t => reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
          (fun τ ζ => G (b + τ) ζ) ζ t)) ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun (i j : Fin p) => noiseCovW ((quadraticGradientDyn d s a β).coeff ρ) q
        (b + ts i) (b + ts j) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i))
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j))) := by
  classical
  have hT0 : 0 ≤ T := hT.le
  have hτ : 0 ≤ b + T := by linarith
  obtain ⟨G', hG', hG'c, hG'z, hGG'⟩ := gfb4_modify P₂ ℱ₂ hτ G (s21mDb _ hS.hF hS.hpAll q hq)
    (fun σ hσ => s21mDb_zero _ hS.hF hS.hpAll q hq hσ) hG
  have hG'm : ∀ t, Measurable (G' t) := fun t => HRS.Uniform.Q07c.measurable_of_isHM hG' t
  have h := s21m_Gb_fdd hS hb hT q hq hG' hG'c hG'z hG'm ts hts αs
  rw [← h]
  refine Measure.map_congr ?_
  have h1 : ∀ a : Fin p, ∀ᵐ ζ ∂P₂, OscDual.coord (reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
      (fun τ ζ => G (b + τ) ζ) ζ (ts a)) (αs a) =
      inner ℝ (G (b + ts a) ζ) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (ts a) (αs a)) := fun a =>
    s21m_recon_coord_eq hS hb q hq hG (hts a) (αs a)
  have h2 : ∀ a : Fin p, ∀ᵐ ζ ∂P₂, G (b + ts a) ζ = G' (b + ts a) ζ := fun a =>
    (hGG' _ ⟨by linarith [(hts a).1], by linarith [(hts a).2]⟩).symm
  filter_upwards [ae_all_iff.2 h1, ae_all_iff.2 h2, hG.cont] with ζ e1 e2 hc
  have hshift : ContinuousOn (fun τ => G (b + τ) ζ) (Set.Icc 0 T) :=
    hc.comp (by fun_prop) (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hrc : ContinuousOn (fun t => reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T
      (fun τ ζ => G (b + τ) ζ) ζ t) (Set.Icc 0 T) :=
    continuousOn_iff_continuous_domRestrict.2 (HRS.MS.U9.u9_continuous_recon hT0 _ ζ hshift)
  ext a
  simp only
  have := s56_wpo_apply (m := ((wholeSpaceIndex d : ℕ) : ℝ)) (T := T)
    (f := fun t => reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => G (b + τ) ζ) ζ t) hrc
    ⟨ts a, hts a⟩
  unfold OscPath.at'
  rw [this]
  show OscDual.coord (reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => G (b + τ) ζ) ζ (ts a)) (αs a) = _
  rw [e1 a, e2 a]

end HRS.MS.S21m
