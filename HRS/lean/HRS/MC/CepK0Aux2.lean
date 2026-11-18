import HRS.Stochastic.SelectedLawFKE

/-!
# Packet CEPK0 (aux 2): lattice and chamber helpers for the uniqueness externals

Helpers for `cep_U1_lift_const_proof` and `cep_U1b_chamber_unique_proof` (`HRS/MC/CepK0.lean`).
Only `HRS.Stochastic.SelectedLawFKE` (for `IsLatticeVec`) and `HRS.CyclicallyOrdered` are used.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepK0

open HRS

/-- Strict cyclic order of a lift (`d = 1`).  Same body as `HRS.MC.Cepa.cep_StrictlyOrdered`
(`HRS/MC/CepaSpec.lean`); duplicated so that this packet does not import the spec file. -/
def cep_StrictlyOrdered {N : ℕ} (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) : Prop :=
  (∀ k k' : Fin N, k < k' → y (π k) 0 < y (π k') 0) ∧
    ∀ k k' : Fin N, y (π k') 0 < y (π k) 0 + 1

/-- Real core of the chamber identification: two points `x` (strictly ordered, gap in `(0,1)`) and
their shifted versions `x + v`, with `v` integer-differing in the pair, and cyclic-order bounds on the
shifted `z + v`, give the pair bounds on `z`. -/
theorem cep_U1b_pair_real (xa xb za zb va vb : ℝ) (hx : 0 < xb - xa) (hx1 : xb - xa < 1)
    (hm : ∃ m : ℤ, vb - va = m) (hW1 : xb + vb - (xa + va) < 1) (hW2 : xa + va - (xb + vb) < 1)
    (hU1 : (zb + vb) - (za + va) ≤ 1) (hU2 : (za + va) - (zb + vb) ≤ 1)
    (hcase : (xa + va < xb + vb ∧ za + va ≤ zb + vb) ∨ (xb + vb < xa + va ∧ zb + vb ≤ za + va)) :
    0 ≤ zb - za ∧ zb - za ≤ 1 := by
  obtain ⟨m, hm⟩ := hm
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have a1 : (-1 : ℝ) < m := by linarith
    have a2 : (m : ℝ) < 1 := by linarith
    have b1 : (-1 : ℤ) < m := by exact_mod_cast a1
    have b2 : m < 1 := by exact_mod_cast a2
    have hm0 : m = 0 := by omega
    rw [hm0] at hm
    push_cast at hm
    constructor <;> linarith
  · have a1 : (m : ℝ) < 0 := by linarith
    have a2 : (-2 : ℝ) < m := by linarith
    have b1 : m < 0 := by exact_mod_cast a1
    have b2 : (-2 : ℤ) < m := by exact_mod_cast a2
    have hm1 : m = -1 := by omega
    rw [hm1] at hm
    push_cast at hm
    constructor <;> linarith

/-- Two torus-equal points differ, coordinatewise, by an integer. -/
theorem cep_U1_torus_int {d : ℕ} {x x' : Euc d} (h : Torus.mk x = Torus.mk x') (j : Fin d) :
    ∃ n : ℤ, (x' - x) j = n := by
  have h1 := congrFun h j
  simp only [Torus.mk] at h1
  have h2 : (((x' - x) j : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [PiLp.sub_apply, AddCircle.coe_sub, h1, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h2
  exact ⟨n, by rw [← hn]; simp⟩

/-- A continuous real function on `[0,T]` with integer values is constant there. -/
theorem cep_U1_const_of_int {g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hc : ContinuousOn g (Icc 0 T))
    (hint : ∀ s ∈ Icc (0:ℝ) T, ∃ n : ℤ, g s = n) : ∀ s ∈ Icc (0:ℝ) T, g s = g 0 := by
  intro s hs
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) T := ⟨le_rfl, hT⟩
  obtain ⟨n0, hn0⟩ := hint 0 h0
  obtain ⟨ns, hns⟩ := hint s hs
  have hcs : ContinuousOn g (Icc 0 s) := hc.mono (Icc_subset_Icc le_rfl hs.2)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hlt' : ns < n0 := by
      have : (ns : ℝ) < n0 := by rw [← hns, ← hn0]; exact hlt
      exact_mod_cast this
    have hle' : (ns : ℝ) + 1 ≤ n0 := by exact_mod_cast hlt'
    have hle : g s ≤ g 0 - 1 / 2 := by linarith
    obtain ⟨r, hr, hgr⟩ :=
      intermediate_value_Icc' hs.1 hcs (show g 0 - 1 / 2 ∈ Icc (g s) (g 0) from ⟨hle, by linarith⟩)
    obtain ⟨m, hm⟩ := hint r ⟨hr.1, hr.2.trans hs.2⟩
    have h2 : (2 * m : ℝ) = 2 * n0 - 1 := by linarith
    have h3 : 2 * m = 2 * n0 - 1 := by exact_mod_cast h2
    omega
  · have hgt' : n0 < ns := by
      have : (n0 : ℝ) < ns := by rw [← hns, ← hn0]; exact hlt
      exact_mod_cast this
    have hle' : (n0 : ℝ) + 1 ≤ ns := by exact_mod_cast hgt'
    have hle : g 0 + 1 / 2 ≤ g s := by linarith
    obtain ⟨r, hr, hgr⟩ :=
      intermediate_value_Icc hs.1 hcs (show g 0 + 1 / 2 ∈ Icc (g 0) (g s) from ⟨by linarith, hle⟩)
    obtain ⟨m, hm⟩ := hint r ⟨hr.1, hr.2.trans hs.2⟩
    have h2 : (2 * m : ℝ) = 2 * n0 + 1 := by linarith
    have h3 : 2 * m = 2 * n0 + 1 := by exact_mod_cast h2
    omega

/-- Integer coordinates make a lattice vector (`IsLatticeVec`). -/
theorem cep_U1_isLattice_of_int {d N : ℕ} {v : Fin N → Euc d} (h : ∀ i j, ∃ n : ℤ, v i j = n) :
    IsLatticeVec v := by
  choose nn hnn using h
  intro i
  refine ⟨fun j => nn i j, ?_⟩
  ext j
  simp [Lattice.toEuc, hnn]

end HRS.MC.CepK0
