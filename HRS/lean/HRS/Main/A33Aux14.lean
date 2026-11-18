import Mathlib
import HRS.Main.A33Aux13

/-!
# Packet A33, helper 14: existence of the limit process
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A33

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

lemma a33_eval_realMode {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.eval F (Torus.realMode k) = NegSobolev.fourierCoeff F k := by
  classical
  unfold NegSobolev.eval
  rw [tsum_eq_single k]
  · unfold Torus.funRealCoeff
    rw [Torus.realMode_orthonormal k k]
    simp
  · intro l hl
    unfold Torus.funRealCoeff
    rw [Torus.realMode_orthonormal l k, if_neg hl]
    simp

lemma a33_ofSeq_fourierCoeff {m : ℝ} (F : NegSobolev d m) :
    NegSobolev.ofSeq m (NegSobolev.fourierCoeff F) = F := by
  have h1 : ∀ k : NonzeroLattice d, Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff F k =
      NegSobolev.coord F k := by
    intro k
    unfold NegSobolev.fourierCoeff
    rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
    simp
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) *
      NegSobolev.fourierCoeff F k) 2 := by
    have : (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff F k) =
        fun k => NegSobolev.coord F k := funext h1
    rw [this]
    exact (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F).2
  have e := NegSobolev.ofSeq_of_mem (m := m) (NegSobolev.fourierCoeff F) hmem
  refine (show (NegSobolev.ofSeq m (NegSobolev.fourierCoeff F) :
      lp (fun _ : NonzeroLattice d => ℝ) 2) = (F : lp (fun _ : NonzeroLattice d => ℝ) 2) from ?_)
  rw [e]
  exact Subtype.ext (funext fun k => by
    show Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff F k = NegSobolev.coord F k
    exact h1 k)

lemma a33_eval_add_left {m : ℝ} (F F' : NegSobolev d m) {ψ : Torus d → ℝ} (hψ : A33WS m ψ) :
    NegSobolev.eval (F + F') ψ = NegSobolev.eval F ψ + NegSobolev.eval F' ψ := by
  unfold NegSobolev.eval
  rw [← Summable.tsum_add (a33_summable_eval' F hψ) (a33_summable_eval' F' hψ)]
  refine tsum_congr fun k => ?_
  have : NegSobolev.fourierCoeff (F + F') k =
      NegSobolev.fourierCoeff F k + NegSobolev.fourierCoeff F' k := by
    unfold NegSobolev.fourierCoeff NegSobolev.coord
    rw [← mul_add]; rfl
  rw [this]; ring

namespace A33Setup

variable (S : A33Setup d)

theorem transport_zero (F : NegSobolev d (S.J : ℝ)) : a33_transport S 0 F = F := by
  have : (fun k : NonzeroLattice d => NegSobolev.eval F (propagator S.D S.ρ 0 0 (Torus.realMode k))) =
      NegSobolev.fourierCoeff F := by
    funext k
    have := S.U_zero (HRS.FieldSingAux.isSmooth_realMode k)
    simp only [A33Setup.U] at this
    rw [this, a33_eval_realMode]
  unfold a33_transport
  rw [this, a33_ofSeq_fourierCoeff]

theorem vec_zero (q : ℝ) (ψ : Torus d → ℝ) : a33_vec S q 0 ψ = 0 := by
  have hg : a33_g S.D S.ρ q 0 ψ = 0 := by
    funext p; unfold a33_g; simp
  have h : MemLp (a33_g S.D S.ρ q 0 ψ) 2 (a33_nu d S.T S.ρ) := by rw [hg]; exact MemLp.zero
  unfold a33_vec
  rw [dif_pos h]
  refine Lp.ext ?_
  filter_upwards [MemLp.coeFn_toLp h, Lp.coeFn_zero (Euc d) 2 (a33_nu d S.T S.ρ)] with p h1 h2
  rw [h1, h2, hg]

end A33Setup

section Existence

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

theorem a33_Gfield_zero_ae (S : A33Setup d) (q : ℝ)
    (W : Lp (Euc d) 2 (a33_nu d S.T S.ρ) → Ω → ℝ) [IsProbabilityMeasure P] (hI : A33Iso P W) :
    ∀ᵐ ω ∂P, a33_Gfield S q W 0 ω = 0 := by
  have hW0 : W 0 =ᵐ[P] fun _ => 0 := by
    have := hI.lin 0 0 0 0
    simpa using this
  have hall : ∀ᵐ ω ∂P, ∀ k : NonzeroLattice d, a33_X S q W 0 k ω = 0 := by
    refine ae_all_iff.2 fun k => ?_
    filter_upwards [hW0] with ω h
    unfold a33_X
    rw [S.vec_zero q, h]
  filter_upwards [hall] with ω hω
  unfold a33_Gfield
  have : (fun k : NonzeroLattice d => a33_X S q W 0 k ω) = fun _ => 0 := funext hω
  have h0 : NegSobolev.fourierCoeff (0 : NegSobolev d (S.J : ℝ)) = fun _ => 0 := by
    funext k
    unfold NegSobolev.fourierCoeff NegSobolev.coord
    have h00 : (show lp (fun _ : NonzeroLattice d => ℝ) 2 from (0 : NegSobolev d (S.J : ℝ))) k = 0 :=
      rfl
    rw [h00, mul_zero]
  rw [this, ← h0, a33_ofSeq_fourierCoeff]

end Existence

end HRS.A33
