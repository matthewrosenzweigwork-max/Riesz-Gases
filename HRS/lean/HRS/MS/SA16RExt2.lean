import HRS.MS.SA16RExt1
import HRS.MS.SA16TransferT8
import HRS.MS.SA16TransferFamilyDefs

/-!
# S.A.16 (SA16R) Ext2: operators on `WmpSpace` from operators on smooth jets

`sa16r_S d k p`: smooth functions that are the zeroth component of an element of `WmpSpace d k p`;
`sa16r_J`: the linear lift `sa16r_S d k p →ₗ WmpSpace d k p` (unique by `wmp_zero_injective`), with dense range.
`sa16r_extend`: a linear map `𝓛 : sa16r_S d k p →ₗ sa16r_S d l p` with `‖J_l (𝓛 f)‖ ≤ c ‖J_k f‖` extends uniquely to
a continuous linear map `WmpSpace d k p →L WmpSpace d l p` of norm `≤ c`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Ext2
variable (d k l : ℕ) (p : ℝ) [Fact (2 ≤ p)]

lemma sa16r_wrep_add (G H : WmpSpace d k p) :
    wrep d k p (G + H) =ᵐ[volume] fun x => wrep d k p G x + wrep d k p H x := by
  filter_upwards [Lp.coeFn_add (G : WLp d k p) (H : WLp d k p)] with x hx
  simp only [wrep]
  exact (by rw [show ((G + H : WmpSpace d k p) : WLp d k p) = (G : WLp d k p) + H from rfl, hx]; rfl)

lemma sa16r_wrep_smul (c : ℝ) (G : WmpSpace d k p) :
    wrep d k p (c • G) =ᵐ[volume] fun x => c * wrep d k p G x := by
  filter_upwards [Lp.coeFn_smul c (G : WLp d k p)] with x hx
  simp only [wrep]
  exact (by rw [show ((c • G : WmpSpace d k p) : WLp d k p) = c • (G : WLp d k p) from rfl, hx]; rfl)

lemma sa16r_wrep_zero : wrep d k p (0 : WmpSpace d k p) =ᵐ[volume] fun _ => 0 := by
  filter_upwards [Lp.coeFn_zero (WIndex d k → ℝ) (ENNReal.ofReal p) (volume : Measure (Euc d))] with x hx
  simp only [wrep]
  exact (by rw [show (((0 : WmpSpace d k p)) : WLp d k p) = 0 from rfl, hx]; rfl)

lemma sa16r_wrep_inj (G H : WmpSpace d k p) (h : wrep d k p G =ᵐ[volume] wrep d k p H) : G = H :=
  wmp_zero_injective d k p G H h

/-- smooth functions with a lift to `WmpSpace d k p` -/
def sa16r_S : Submodule ℝ (Euc d → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ ∃ G : WmpSpace d k p, wrep d k p G =ᵐ[volume] f}
  add_mem' := by
    rintro f g ⟨hf, G, hG⟩ ⟨hg, H, hH⟩
    refine ⟨hf.add hg, G + H, ?_⟩
    filter_upwards [sa16r_wrep_add d k p G H, hG, hH] with x h1 h2 h3
    simp [h1, h2, h3]
  zero_mem' := ⟨contDiff_const, 0, by
    filter_upwards [sa16r_wrep_zero d k p] with x hx
    simp [hx]⟩
  smul_mem' := by
    rintro c f ⟨hf, G, hG⟩
    refine ⟨hf.const_smul c, c • G, ?_⟩
    filter_upwards [sa16r_wrep_smul d k p c G, hG] with x h1 h2
    simp [h1, h2]

/-- the lift of a smooth function in `sa16r_S` -/
def sa16r_Jfun (f : sa16r_S d k p) : WmpSpace d k p := Classical.choose f.2.2

lemma sa16r_Jfun_spec (f : sa16r_S d k p) : wrep d k p (sa16r_Jfun d k p f) =ᵐ[volume] f.1 :=
  Classical.choose_spec f.2.2

def sa16r_J : sa16r_S d k p →ₗ[ℝ] WmpSpace d k p where
  toFun := sa16r_Jfun d k p
  map_add' f g := by
    refine sa16r_wrep_inj d k p _ _ ?_
    filter_upwards [sa16r_Jfun_spec d k p (f + g), sa16r_wrep_add d k p (sa16r_Jfun d k p f)
      (sa16r_Jfun d k p g), sa16r_Jfun_spec d k p f, sa16r_Jfun_spec d k p g] with x h1 h2 h3 h4
    rw [h2, h3, h4]
    simpa using h1
  map_smul' c f := by
    refine sa16r_wrep_inj d k p _ _ ?_
    filter_upwards [sa16r_Jfun_spec d k p (c • f), sa16r_wrep_smul d k p c (sa16r_Jfun d k p f),
      sa16r_Jfun_spec d k p f] with x h1 h2 h3
    simp only [RingHom.id_apply]
    rw [h2, h3]
    simpa using h1

lemma sa16r_J_spec (f : sa16r_S d k p) : wrep d k p (sa16r_J d k p f) =ᵐ[volume] f.1 :=
  sa16r_Jfun_spec d k p f

lemma sa16r_J_dense : DenseRange (sa16r_J d k p) := by
  intro G
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  show (G : WLp d k p) ∈ closure (Subtype.val '' Set.range (sa16r_J d k p))
  set N : Submodule ℝ (WLp d k p) :=
    (LinearMap.range (sa16r_J d k p)).map (WmpSpace d k p).subtype with hN
  have hspan : Submodule.span ℝ {F : WLp d k p | ∃ φ : Euc d → ℝ, IsCcInfty φ ∧
      (F : Euc d → (WIndex d k → ℝ)) =ᵐ[volume] wJet k φ} ≤ N := by
    rw [Submodule.span_le]
    rintro F ⟨φ, hφ, hF⟩
    have hFmem : F ∈ WmpSpace d k p := by
      unfold WmpSpace
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ, hφ, hF⟩)
    have hz : wrep d k p ⟨F, hFmem⟩ =ᵐ[volume] φ := by
      filter_upwards [hF] with x hx
      show ((F : Euc d → (WIndex d k → ℝ)) x) (wZero d k) = φ x
      rw [hx]
      simp only [wJet, wZero, partialDeriv]
      exact iteratedFDeriv_zero_apply _
    have hφS : φ ∈ sa16r_S d k p := ⟨hφ.1, ⟨F, hFmem⟩, hz⟩
    refine ⟨sa16r_J d k p ⟨φ, hφS⟩, ⟨⟨φ, hφS⟩, rfl⟩, ?_⟩
    have : sa16r_J d k p ⟨φ, hφS⟩ = ⟨F, hFmem⟩ := by
      refine sa16r_wrep_inj d k p _ _ ?_
      filter_upwards [sa16r_J_spec d k p ⟨φ, hφS⟩, hz] with x h1 h2
      rw [h1, h2]
    rw [this]; rfl
  have h1 : (G : WLp d k p) ∈ (Submodule.span ℝ {F : WLp d k p | ∃ φ : Euc d → ℝ, IsCcInfty φ ∧
      (F : Euc d → (WIndex d k → ℝ)) =ᵐ[volume] wJet k φ}).topologicalClosure := G.2
  have h2 := Submodule.topologicalClosure_mono hspan h1
  have h3 : ((N : Set (WLp d k p))) = Subtype.val '' Set.range (sa16r_J d k p) := by
    rw [hN, Submodule.map_coe, LinearMap.coe_range]
    rfl
  have h2' : (G : WLp d k p) ∈ closure ((N : Set (WLp d k p))) := h2
  rw [← h3]
  exact h2'

/-- **Extension principle.** -/
theorem sa16r_extend (𝓛 : sa16r_S d k p →ₗ[ℝ] sa16r_S d l p) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ f, ‖sa16r_J d l p (𝓛 f)‖ ≤ c * ‖sa16r_J d k p f‖) :
    ∃ T : WmpSpace d k p →L[ℝ] WmpSpace d l p, ‖T‖ ≤ c ∧
      (∀ f, T (sa16r_J d k p f) = sa16r_J d l p (𝓛 f)) ∧
      ∀ T' : WmpSpace d k p →L[ℝ] WmpSpace d l p,
        (∀ f, T' (sa16r_J d k p f) = sa16r_J d l p (𝓛 f)) → T' = T :=
  sa16r_ext_abstract (sa16r_J d k p) (sa16r_J_dense d k p) ((sa16r_J d l p).comp 𝓛) hc hb

/-- `G` with smooth zeroth component `f` is `J f` -/
lemma sa16r_eq_J (G : WmpSpace d k p) (f : sa16r_S d k p) (h : wrep d k p G =ᵐ[volume] f.1) :
    G = sa16r_J d k p f := by
  refine sa16r_wrep_inj d k p _ _ ?_
  filter_upwards [h, sa16r_J_spec d k p f] with x h1 h2
  rw [h1, h2]

end Ext2

end HRS.Whole.AppendixA.Phase2SA16R
