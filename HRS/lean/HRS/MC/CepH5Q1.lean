import HRS.Appendix.CepaFlow
import HRS.Kernel.D1
import HRS.Torus.Sobolev

/-!
# Packet CEPH5FISH, part 1: periodic lifts and continuity of the Fisher test integrand

Facts about the covering map `mkN : (Fin N → Euc 1) → Config 1 N`: it is an open quotient map, `fderiv` of a
function of the form `P ∘ mkN` is invariant under lattice shifts, so the test integrand of `fisherInfo`
(evaluated at the representative `rep X`) equals its value at any lift.  For `V ∈ C¹` the integrand is a
continuous function on the compact space `Config 1 N`.
-/

noncomputable section

namespace HRS.MC.CepH5Pf

open HRS MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {N : ℕ}

/-- the covering map -/
abbrev q1mk (N : ℕ) (y : Fin N → Euc 1) : Config 1 N := fun i => Torus.mk (y i)

lemma q1mk_cont : Continuous (q1mk N) :=
  continuous_pi fun i => Torus.continuous_mk.comp (continuous_apply i)

lemma q1_mk_open : IsOpenMap (Torus.mk : Euc 1 → Torus 1) := by
  have h1 : IsOpenMap (Pi.map (fun _ : Fin 1 => (fun a : ℝ => (a : UnitAddCircle)))) :=
    IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe) (by simp [Filter.cofinite_eq_bot])
  exact h1.comp (PiLp.homeomorph 2 (fun _ : Fin 1 => ℝ)).isOpenMap

lemma q1mk_open : IsOpenMap (q1mk N) := by
  have := IsOpenMap.piMap (f := fun _ : Fin N => (Torus.mk : Euc 1 → Torus 1)) (fun _ => q1_mk_open)
    (by simp [Filter.cofinite_eq_bot])
  exact this

lemma q1mk_surj : Function.Surjective (q1mk N) :=
  fun x => ⟨fun i => Torus.rep (x i), funext fun i => Torus.mk_rep (x i)⟩

lemma q1mk_quot : Topology.IsQuotientMap (q1mk N) :=
  q1mk_open.isQuotientMap q1mk_cont q1mk_surj

/-- lattice vectors in `(ℝ¹)^N` -/
def Q1Lat (ℓ : Fin N → Euc 1) : Prop := ∀ i j, ∃ n : ℤ, ℓ i j = n

lemma q1mk_add_lat {Y ℓ : Fin N → Euc 1} (h : Q1Lat ℓ) : q1mk N (Y + ℓ) = q1mk N Y := by
  funext i
  have : Torus.mk (Y i + ℓ i) = Torus.mk (Y i) := by
    funext j
    obtain ⟨n, hn⟩ := h i j
    simp only [Torus.mk, PiLp.add_apply, hn]
    rw [AddCircle.coe_add]
    have : ((n : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]; exact ⟨n, by simp⟩
    rw [this, add_zero]
  simpa [q1mk] using this


lemma q1_rep_lat (Y : Fin N → Euc 1) :
    ∃ ℓ : Fin N → Euc 1, Q1Lat ℓ ∧ (fun i => Torus.rep (q1mk N Y i)) = Y + ℓ := by
  have h : ∀ i, ∃ n : Lattice 1, Torus.rep (Torus.mk (Y i)) = Y i + Lattice.toEuc n :=
    fun i => Torus.rep_mk (Y i)
  choose n hn using h
  refine ⟨fun i => Lattice.toEuc (n i), fun i j => ⟨n i j, by simp [Lattice.toEuc]⟩, ?_⟩
  funext i
  simpa [q1mk] using hn i

lemma q1_fderiv_lat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Config 1 N → E)
    {Y ℓ : Fin N → Euc 1} (h : Q1Lat ℓ) :
    fderiv ℝ (fun Z => P (q1mk N Z)) (Y + ℓ) = fderiv ℝ (fun Z => P (q1mk N Z)) Y := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext Z
  rw [q1mk_add_lat h]

lemma q1_fderiv_rep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Config 1 N → E)
    (Y : Fin N → Euc 1) :
    fderiv ℝ (fun Z => P (q1mk N Z)) (fun i => Torus.rep (q1mk N Y i)) =
      fderiv ℝ (fun Z => P (q1mk N Z)) Y := by
  obtain ⟨ℓ, hℓ, he⟩ := q1_rep_lat Y
  rw [he]; exact q1_fderiv_lat P hℓ

/-- the integrand of `fisherInfo` -/
def q1F (D : DynData 1) (ζ : Config 1 N → (Fin N → Euc 1)) (X : Config 1 N) : ℝ :=
  -2 * configDiv ζ X
        + 2 * D.invβ⁻¹ * fderiv ℝ (fun Z : Fin N → Euc 1 => totalPotential D (fun i => Torus.mk (Z i)))
            (fun i => Torus.rep (X i)) (ζ X)
        - ∑ i, ‖ζ X i‖ ^ 2

/-- the integrand expressed on the lift -/
def q1G (D : DynData 1) (ζ : Config 1 N → (Fin N → Euc 1)) (Y : Fin N → Euc 1) : ℝ :=
  -2 * (∑ k : Fin N × Fin 1, fderiv ℝ (fun Z : Fin N → Euc 1 => (ζ (q1mk N Z) k.1) k.2) Y
      (configBasis 1 N k))
    + 2 * D.invβ⁻¹ * fderiv ℝ (fun Z : Fin N → Euc 1 => totalPotential D (q1mk N Z)) Y (ζ (q1mk N Y))
    - ∑ i, ‖ζ (q1mk N Y) i‖ ^ 2

lemma q1F_mk (D : DynData 1) (ζ : Config 1 N → (Fin N → Euc 1)) (Y : Fin N → Euc 1) :
    q1F D ζ (q1mk N Y) = q1G D ζ Y := by
  unfold q1F q1G configDiv
  have h1 := q1_fderiv_rep (fun X => totalPotential D X) Y
  have h2 : ∀ k : Fin N × Fin 1, fderiv ℝ (fun Z : Fin N → Euc 1 => (ζ (q1mk N Z) k.1) k.2)
      (fun i => Torus.rep (q1mk N Y i)) = fderiv ℝ (fun Z : Fin N → Euc 1 => (ζ (q1mk N Z) k.1) k.2) Y :=
    fun k => q1_fderiv_rep (fun X => (ζ X k.1) k.2) Y
  rw [h1]
  simp only [h2]

end HRS.MC.CepH5Pf
