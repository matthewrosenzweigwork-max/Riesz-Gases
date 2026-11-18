import HRS.MC.E213U16h
import HRS.Uniform.Q54cAux1

/-!
# Packet e213u16, file i: sub-sigma-algebras and measurability transfer through countable coordinates
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10

variable {d : ℕ}

section Coords

/-- A map into a Polish space whose countably many separating continuous coordinates are a.e. equal to
`m`-measurable real functions is a.e. equal to an `m`-measurable map. -/
theorem u16_meas_of_coords {Ω X : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} (m : MeasurableSpace Ω)
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [PolishSpace X] [Nonempty X]
    {J : Type*} [Countable J] (ℓ : J → X → ℝ) (hc : ∀ j, Continuous (ℓ j))
    (hinj : Function.Injective (fun x j => ℓ j x)) {W : Ω → X}
    (h : ∀ j, ∃ g : Ω → ℝ, Measurable[m] g ∧ ∀ᵐ ω ∂μ, ℓ j (W ω) = g ω) :
    ∃ W' : Ω → X, Measurable[m] W' ∧ W =ᵐ[μ] W' := by
  have emb : MeasurableEmbedding (fun x j => ℓ j x) :=
    (measurable_pi_iff.2 fun j => (hc j).measurable).measurableEmbedding hinj
  obtain ⟨g, hg, hgc⟩ := emb.exists_measurable_extend (g := id) measurable_id
    (fun _ => ⟨Classical.arbitrary X⟩)
  choose G hGm hGae using h
  have hΨ : Measurable[m] (fun ω j => G j ω) := by
    refine @measurable_pi_iff Ω J (fun _ => ℝ) m _ _ |>.2 fun j => hGm j
  refine ⟨fun ω => g (fun j => G j ω), @Measurable.comp _ _ _ m _ _ _ _ hg hΨ, ?_⟩
  have hall : ∀ᵐ ω ∂μ, ∀ j, ℓ j (W ω) = G j ω := ae_all_iff.2 hGae
  filter_upwards [hall] with ω hω
  have h2 := congrFun hgc (W ω)
  simp only [Function.comp, id] at h2
  rw [← h2]
  congr 1
  funext j
  exact hω j

end Coords


section Sig

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- The past sigma-algebra `σ(η^s(ψ) : s ≤ τ, ψ smooth)`. -/
def pastSig (τ : ℝ) : MeasurableSpace gd.Ω₀ :=
  MeasurableSpace.comap (fun ω p => Xs gd τ p ω) MeasurableSpace.pi

/-- The future sigma-algebra `σ(η^t(ψ) - η^τ(U^{τ,t}ψ) : τ < t ≤ H, ψ smooth)`. -/
def futSig (τ H : ℝ) : MeasurableSpace gd.Ω₀ :=
  MeasurableSpace.comap (fun ω q => Ys gd τ H q ω) MeasurableSpace.pi

theorem pastSig_le {H τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) : pastSig gd τ ≤ gd.mΩ₀ := by
  refine Measurable.comap_le ?_
  exact measurable_pi_iff.2 fun p => (u16_isSC_Xs gd hτ p).measurable

theorem futSig_le {H τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) : futSig gd τ H ≤ gd.mΩ₀ := by
  refine Measurable.comap_le ?_
  exact measurable_pi_iff.2 fun p => (u16_isSC_Ys gd hτ p).measurable

theorem pastSig_meas_Xs (τ : ℝ) (p : Set.Icc (0 : ℝ) τ × SmoothFn d) : Measurable[pastSig gd τ] (Xs gd τ p) :=
  @Measurable.comp _ _ _ (pastSig gd τ) _ _ _ _ (measurable_pi_apply p)
    (comap_measurable (fun ω p => Xs gd τ p ω))

theorem futSig_meas_Ys (τ H : ℝ) (p : Set.Ioc τ H × SmoothFn d) : Measurable[futSig gd τ H] (Ys gd τ H p) :=
  @Measurable.comp _ _ _ (futSig gd τ H) _ _ _ _ (measurable_pi_apply p)
    (comap_measurable (fun ω q => Ys gd τ H q ω))

theorem u16_indep_sig {H τ : ℝ} (hH : 0 < H) (hτ : τ ∈ Set.Icc (0 : ℝ) H) :
    Indep (pastSig gd τ) (futSig gd τ H) gd.P₀ :=
  (IndepFun_iff_Indep _ _ _).1 (u16_indep gd hH hτ)

theorem u16_indepFun_of_sig {H τ : ℝ} (hH : 0 < H) (hτ : τ ∈ Set.Icc (0 : ℝ) H) {V W : Type*}
    [MeasurableSpace V] [MeasurableSpace W] {v : gd.Ω₀ → V} {γ : gd.Ω₀ → W}
    (hv : ∃ v', Measurable[pastSig gd τ] v' ∧ v =ᵐ[gd.P₀] v')
    (hγ : ∃ γ', Measurable[futSig gd τ H] γ' ∧ γ =ᵐ[gd.P₀] γ') : IndepFun v γ gd.P₀ := by
  obtain ⟨v', hv', hvv⟩ := hv
  obtain ⟨γ', hγ', hγγ⟩ := hγ
  have h : IndepFun v' γ' gd.P₀ := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left (u16_indep_sig gd hH hτ) hv'.comap_le)
      hγ'.comap_le
  exact h.congr hvv.symm hγγ.symm

end Sig


section CoordLemmas

/-- `coord F k = ⟨k⟩^{-r} · eval F (e_k)`. -/
theorem u16_coord_eq {r : ℝ} (F : NegSobolev d r) (k : NonzeroLattice d) :
    NegSobolev.coord F k = Lattice.jp k.1 ^ (-r) * NegSobolev.eval F (Torus.realMode k) := by
  rw [HRS.MD.EQGaussWindow.eqgw_eval_realMode]
  unfold NegSobolev.fourierCoeff
  rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos _)]
  simp

/-- Measurability transfer for `NegSobolev`-valued maps via the pairings with smooth tests. -/
theorem u16_neg_meas {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} (m : MeasurableSpace Ω) {r : ℝ}
    {F : Ω → NegSobolev d r}
    (h : ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
      ∃ g : Ω → ℝ, Measurable[m] g ∧ ∀ᵐ ω ∂μ, NegSobolev.eval (F ω) ψ = g ω) :
    ∃ F' : Ω → NegSobolev d r, Measurable[m] F' ∧ F =ᵐ[μ] F' := by
  letI : MeasurableSpace Ω := m0
  refine u16_meas_of_coords (μ := μ) (J := NonzeroLattice d) m (fun k F => NegSobolev.coord F k)
    (fun k => HRS.Uniform.Q54c.continuous_coord r k) ?_ ?_
  · intro F G hFG
    have : (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) = (show lp (fun _ : NonzeroLattice d => ℝ) 2 from G) :=
      lp.ext (funext fun k => congrFun hFG k)
    exact this
  · intro k
    obtain ⟨g, hg, hae⟩ := h _ (HRS.MD.EQGaussWindow.eqgw_isSmooth_realMode k)
    refine ⟨fun ω => Lattice.jp k.1 ^ (-r) * g ω, hg.const_mul _, ?_⟩
    filter_upwards [hae] with ω hω
    rw [u16_coord_eq, hω]

/-- Measurability transfer for path-valued maps via the pairings with smooth tests. -/
theorem u16_path_meas {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} (m : MeasurableSpace Ω) {r H : ℝ}
    (hH : 0 < H) {W : Ω → PathSpace d r H}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) H, ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
      ∃ g : Ω → ℝ, Measurable[m] g ∧ ∀ᵐ ω ∂μ, NegSobolev.eval (pathAt (W ω) t) ψ = g ω) :
    ∃ W' : Ω → PathSpace d r H, Measurable[m] W' ∧ W =ᵐ[μ] W' := by
  letI : MeasurableSpace Ω := m0
  haveI : Nonempty (Set.Icc (0 : ℝ) H) := ⟨⟨0, le_rfl, hH.le⟩⟩
  set s : ℕ → Set.Icc (0 : ℝ) H := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) H) with hsdef
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  refine u16_meas_of_coords (μ := μ) (J := ℕ × NonzeroLattice d) m (fun i w => HRS.Uniform.Q54c.pathCoords (d := d) r H s w i)
    (fun i => ?_) ?_ ?_
  · have h1 : Continuous fun w : PathSpace d r H => PathSpace.at' w (s i.1) :=
      (continuous_eval_const (s i.1) : Continuous fun w : C(Set.Icc (0 : ℝ) H, NegSobolev d r) => w (s i.1))
    exact (HRS.Uniform.Q54c.continuous_coord r i.2).comp h1
  · intro w w' hw
    exact HRS.Uniform.Q54c.pathCoords_injective r H s hs (funext fun i => congrFun hw i)
  · rintro ⟨n, k⟩
    obtain ⟨g, hg, hae⟩ := h (s n) (s n).2 _ (HRS.MD.EQGaussWindow.eqgw_isSmooth_realMode k)
    refine ⟨fun ω => Lattice.jp k.1 ^ (-r) * g ω, hg.const_mul _, ?_⟩
    filter_upwards [hae] with ω hω
    simp only [HRS.Uniform.Q54c.pathCoords]
    rw [u16_coord_eq, ← hω, HRS.MC.E213U4.u4_pathAt_coe]

end CoordLemmas

end HRS.MC.E213U16

end
