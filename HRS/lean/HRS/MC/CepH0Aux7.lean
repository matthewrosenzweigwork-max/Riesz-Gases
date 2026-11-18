import HRS.Appendix.CepaFlow

/-!
# Packet CEPH0, auxiliary 7: locality of the Fisher functional and gluing of test fields
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepH0

open HRS

variable {d N : ℕ}

/-- The integrand of the variational formula of `fisherInfo`. -/
def h0F (D : DynData d) (ζ : Config d N → (Fin N → Euc d)) (X : Config d N) : ℝ :=
  -2 * configDiv ζ X
    + 2 * D.invβ⁻¹ * fderiv ℝ (fun Z : Fin N → Euc d => totalPotential D (fun i => Torus.mk (Z i)))
        (fun i => Torus.rep (X i)) (ζ X)
    - ∑ i, ‖ζ X i‖ ^ 2

theorem h0_fisherInfo_eq (D : DynData d) (P : Measure (Config d N)) :
    fisherInfo D N P = ⨆ (ζ : Config d N → (Fin N → Euc d)) (_ : IsFisherTestField ζ),
      ENNReal.ofReal (∫ X, h0F D ζ X ∂P) := rfl

theorem h0_continuous_mkN : Continuous (fun Z : Fin N → Euc d => fun i => Torus.mk (Z i)) :=
  continuous_pi fun i => Torus.continuous_mk.comp (continuous_apply i)

theorem h0F_congr_of_eq_on (D : DynData d) {ζ ζ' : Config d N → (Fin N → Euc d)}
    {U : Set (Config d N)} (hU : IsOpen U) (h : ∀ X ∈ U, ζ X = ζ' X) {X : Config d N}
    (hX : X ∈ U) : h0F D ζ X = h0F D ζ' X := by
  have hζ : ζ X = ζ' X := h X hX
  have hmk : (fun i => Torus.mk (Torus.rep (X i))) = X := funext fun i => Torus.mk_rep _
  have hdiv : configDiv ζ X = configDiv ζ' X := by
    unfold configDiv
    refine Finset.sum_congr rfl fun k _ => ?_
    have hev : (fun Z : Fin N → Euc d => (ζ (fun i => Torus.mk (Z i)) k.1) k.2)
        =ᶠ[𝓝 (fun i => Torus.rep (X i))] (fun Z : Fin N → Euc d => (ζ' (fun i => Torus.mk (Z i)) k.1) k.2) := by
      have hmem : (fun i => Torus.rep (X i)) ∈
          (fun Z : Fin N → Euc d => (fun i => Torus.mk (Z i))) ⁻¹' U := by
        show (fun i => Torus.mk (Torus.rep (X i))) ∈ U
        rw [hmk]; exact hX
      filter_upwards [(hU.preimage h0_continuous_mkN).mem_nhds hmem] with Z hZ
      rw [h _ hZ]
    rw [hev.fderiv_eq]
  unfold h0F
  rw [hdiv, hζ]

theorem h0_piece_smooth {n : WithTop ℕ∞} (S : Set (Config d N)) (hSo : IsOpen S) (K : Set (Config d N))
    (hK : IsClosed K) (ζc : Config d N → (Fin N → Euc d))
    (hsm : ContDiff ℝ n (fun Y : Fin N → Euc d => ζc (fun i => Torus.mk (Y i))))
    (hsupp : ∀ X, X ∉ K → ζc X = 0)
    (hKS : ∀ X ∈ K, X ∉ S → ∃ S' : Set (Config d N), IsOpen S' ∧ X ∈ S' ∧ Disjoint S' S) :
    ContDiff ℝ n (fun Y : Fin N → Euc d => S.indicator ζc (fun i => Torus.mk (Y i))) := by
  rw [contDiff_iff_contDiffAt]
  intro Y
  by_cases hY : (fun i => Torus.mk (Y i)) ∈ S
  · refine (hsm.contDiffAt (x := Y)).congr_of_eventuallyEq ?_
    filter_upwards [(hSo.preimage h0_continuous_mkN).mem_nhds hY] with Z hZ
    exact Set.indicator_of_mem (s := S) hZ ζc
  · have hz : (fun Z : Fin N → Euc d => S.indicator ζc (fun i => Torus.mk (Z i)))
        =ᶠ[𝓝 Y] fun _ => (0 : Fin N → Euc d) := by
      by_cases hYK : (fun i => Torus.mk (Y i)) ∈ K
      · obtain ⟨S', hS'o, hYS', hS'd⟩ := hKS _ hYK hY
        filter_upwards [(hS'o.preimage h0_continuous_mkN).mem_nhds hYS'] with Z hZ
        exact Set.indicator_of_notMem (fun hm => Set.disjoint_left.mp hS'd hZ hm) _
      · filter_upwards [(hK.isOpen_compl.preimage h0_continuous_mkN).mem_nhds hYK] with Z hZ
        by_cases hm : (fun i => Torus.mk (Z i)) ∈ S
        · rw [Set.indicator_of_mem hm]; exact hsupp _ hZ
        · exact Set.indicator_of_notMem hm _
    exact (contDiffAt_const : ContDiffAt ℝ n (fun _ : Fin N → Euc d => (0 : Fin N → Euc d)) Y).congr_of_eventuallyEq hz

theorem h0_glue {ι : Type*} [Fintype ι] (C : ι → Set (Config d N)) (hCo : ∀ c, IsOpen (C c))
    (hCd : Pairwise fun c c' => Disjoint (C c) (C c'))
    (hCc : (⋃ c, C c) = (collisionSet d N)ᶜ)
    (ζs : ι → Config d N → (Fin N → Euc d)) (hζ : ∀ c, IsFisherTestField (ζs c)) :
    IsFisherTestField (fun X => ∑ c, (C c).indicator (ζs c) X) ∧
      ∀ c, ∀ X ∈ C c, (∑ c', (C c').indicator (ζs c') X) = ζs c X := by
  classical
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine ContDiff.sum fun c _ => ?_
    obtain ⟨K, hKc, hKd, hKs⟩ := (hζ c).support
    refine h0_piece_smooth (C c) (hCo c) K hKc.isClosed (ζs c) (hζ c).smooth hKs ?_
    intro X hXK hXC
    have hXn : X ∉ collisionSet d N := fun h => Set.disjoint_left.mp hKd hXK h
    have : X ∈ ⋃ c, C c := by rw [hCc]; exact hXn
    obtain ⟨c', hc'⟩ := Set.mem_iUnion.mp this
    have hne : c' ≠ c := fun h => hXC (h ▸ hc')
    exact ⟨C c', hCo c', hc', hCd hne⟩
  · choose K hKc hKd hKs using fun c => (hζ c).support
    refine ⟨⋃ c, K c, isCompact_iUnion hKc, ?_, ?_⟩
    · rw [Set.disjoint_iUnion_left]; exact hKd
    · intro X hX
      refine Finset.sum_eq_zero fun c _ => ?_
      have : X ∉ K c := fun h => hX (Set.mem_iUnion.mpr ⟨c, h⟩)
      by_cases hm : X ∈ C c
      · rw [Set.indicator_of_mem hm]; exact hKs c X this
      · exact Set.indicator_of_notMem hm _
  · intro c X hX
    rw [Finset.sum_eq_single c]
    · exact Set.indicator_of_mem hX _
    · intro c' _ hc'
      exact Set.indicator_of_notMem (fun h => Set.disjoint_left.mp (hCd hc') h hX) _
    · simp

end HRS.MC.CepH0
