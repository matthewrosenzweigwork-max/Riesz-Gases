import HRS.MC.S7PIDEMat
import HRS.MC.S7PIEMeas

/-!
# Packet PI-D, sub-packet K (part 3): the semigroup law for `V` on a mode vector

`V^{t,c'} (p₀ • V^{c',u} e_k) = p₀ • V^{t,u} e_k` for `0 < u ≤ c' < t ≤ T`.  Route: in coordinates `V^{t,u} e_k` is the sequence
`i ↦ T^{u,t}_{k i}` (matrix of the propagator), the row series of `S7PIDEMat` (`S7PIDE_hasSum_row`) and the propagator
semigroup give `T^{u,t}_{k i} = ∑_j T^{u,c'}_{k j} T^{c',t}_{j i}`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDK

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIDE HRS.MC.Sec7.S7PIDM

variable {d : ℕ}

theorem S7PIDK_ofSeq_smul (m p₀ : ℝ) (a : NonzeroLattice d → ℝ)
    (ha : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * a k) 2) :
    NegSobolev.ofSeq m (fun k => p₀ * a k) = p₀ • NegSobolev.ofSeq m a := by
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * (p₀ * a k)) 2 := by
    have h := ha.const_smul p₀
    convert h using 1
    funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  refine pie_ext _ _ fun k => ?_
  rw [NegSobolev.coord_ofSeq_of_mem _ hmem k]
  have : NegSobolev.coord (p₀ • NegSobolev.ofSeq m a) k = p₀ * NegSobolev.coord (NegSobolev.ofSeq m a) k := rfl
  rw [this, NegSobolev.coord_ofSeq_of_mem _ ha k]
  ring

/-- the semigroup law for `V` on a mode vector -/
theorem S7PIDK_V_semigroup (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    {u c' t : ℝ} (hu : 0 < u) (huc : u ≤ c') (hct : c' < t) (htT : t ≤ T) (p₀ : ℝ) (k : NonzeroLattice d) :
    Vprop R.D R.ρ m t c' (p₀ • Vprop R.D R.ρ m c' u (modeVec m k)) =
      p₀ • Vprop R.D R.ρ m t u (modeVec m k) := by
  set L : ℕ := max (PDE.mStar d) ⌊m⌋₊ with hLdef
  have hL : PDE.mStar d ≤ L := le_max_left _ _
  have hLm : ⌊m⌋₊ ≤ L := le_max_right _ _
  have H := S7PIDM.S7PIDM_pie R T hT L hL
  have hm0 : 0 ≤ m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hn1 : 1 ≤ ⌊m⌋₊ := by
    apply Nat.le_floor
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    push_cast
    linarith
  have hnm : ((⌊m⌋₊ : ℕ) : ℝ) ≤ m := Nat.floor_le hm0
  have hL1 : 1 ≤ L := hn1.trans hLm
  have hc'0 : 0 < c' := lt_of_lt_of_le hu huc
  have hc'T : c' ≤ T := hct.le.trans htT
  have ht0 : 0 < t := hc'0.trans hct
  -- row memberships
  have hmemUC : Memℓp (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-m) *
      Torus.funRealCoeff (propagator R.D R.ρ u c' (Torus.realMode j)) k) 2 :=
    S7PIDE_row_mem H ⌊m⌋₊ hn1 hLm m hnm ⟨hc'0, hc'T⟩ ⟨hu.le, huc⟩ k
  have hmemUT : Memℓp (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-m) *
      Torus.funRealCoeff (propagator R.D R.ρ u t (Torus.realMode j)) k) 2 :=
    S7PIDE_row_mem H ⌊m⌋₊ hn1 hLm m hnm ⟨ht0, htT⟩ ⟨hu.le, huc.trans hct.le⟩ k
  -- the Fourier coefficients of `V^{c',u} e_k`
  have hfc : ∀ j : NonzeroLattice d, NegSobolev.fourierCoeff (Vprop R.D R.ρ m c' u (modeVec m k)) j =
      Torus.funRealCoeff (propagator R.D R.ρ u c' (Torus.realMode j)) k := by
    intro j
    rw [S7PIDM_Vprop_eq]
    unfold NegSobolev.fourierCoeff
    rw [NegSobolev.coord_ofSeq_of_mem _ hmemUC j, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos j.1)]
    simp
  -- the matrix semigroup identity
  have hmat : ∀ i : NonzeroLattice d,
      HasSum (fun j : NonzeroLattice d =>
        Torus.funRealCoeff (propagator R.D R.ρ u c' (Torus.realMode j)) k *
          Torus.funRealCoeff (propagator R.D R.ρ c' t (Torus.realMode i)) j)
        (Torus.funRealCoeff (propagator R.D R.ρ u t (Torus.realMode i)) k) := by
    intro i
    have hdom : HRS.A33.Dom L (propagator R.D R.ρ c' t (Torus.realMode i)) :=
      S7PIDE_dom H hc'0.le hct.le htT (pieDom_realMode L i)
    have hrow := S7PIDE_hasSum_row H hL1 ⟨hc'0, hc'T⟩ ⟨hu.le, huc⟩ hdom k
    have hsg : propagator R.D R.ρ u t (Torus.realMode i) =
        propagator R.D R.ρ u c' (propagator R.D R.ρ c' t (Torus.realMode i)) :=
      pie_prop_semigroup H ⟨ht0, htT⟩ (pieDom_realMode L i) hu.le huc hct
    rw [hsg]
    exact hrow
  have hV : Vprop R.D R.ρ m t c' (p₀ • Vprop R.D R.ρ m c' u (modeVec m k)) =
      NegSobolev.ofSeq m (fun i => p₀ * Torus.funRealCoeff (propagator R.D R.ρ u t (Torus.realMode i)) k) := by
    generalize hG : Vprop R.D R.ρ m c' u (modeVec m k) = G at hfc ⊢
    show NegSobolev.ofSeq m (fun i => NegSobolev.eval (p₀ • G) (propagator R.D R.ρ c' t (Torus.realMode i))) = _
    congr 1
    funext i
    have e1 : NegSobolev.eval (p₀ • G) (propagator R.D R.ρ c' t (Torus.realMode i)) =
        p₀ * NegSobolev.eval G (propagator R.D R.ρ c' t (Torus.realMode i)) := by
      unfold NegSobolev.eval NegSobolev.fourierCoeff
      rw [← tsum_mul_left]
      refine tsum_congr fun j => ?_
      have : NegSobolev.coord (p₀ • G) j = p₀ * NegSobolev.coord G j := rfl
      rw [this]; ring
    rw [e1]
    congr 1
    unfold NegSobolev.eval
    rw [← (hmat i).tsum_eq]
    exact tsum_congr fun j => by rw [hfc j]
  rw [hV, S7PIDM_Vprop_eq]
  exact S7PIDK_ofSeq_smul m p₀ _ hmemUT

end HRS.MC.Sec7.S7PIDK

end
