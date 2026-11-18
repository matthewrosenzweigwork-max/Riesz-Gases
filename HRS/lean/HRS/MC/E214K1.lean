import HRS.MC.E214PD
import HRS.Uniform.Q48bAux5
import HRS.Uniform.Q48bAux2
import HRS.Main.ThermLinAux8
import HRS.Main.ThermLinAux7
import HRS.Uniform.Q54Aux10
import HRS.Main.A9Aux5
import HRS.MC.E213D
import HRS.PDE.MeanFieldSemigroup
import HRS.Uniform.Q48eAux2
import HRS.PDE.WellPosed

/-!
# Packet E214K, part 1: weighted duality bound for a difference of two dual evolutions, and time homogeneity

* `wbound_of_duality2`: a variant of `Q48b.q48b_wbound_of_duality` in which the dual-side test function is replaced
  by an abstract coefficient sequence `χ T c` (no `projMean` of the dual test function is needed);
* `frozen_shift`: time homogeneity of the frozen propagator `U^β_{u,t} φ = U^β_{0,t-u} φ` on smooth tests (copy of
  `ThermLin.Plan2.tl2_frozen_shift_proof`, whose file contains `sorry`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214K

open HRS HRS.PDE HRS.Uniform HRS.Uniform.Q48b

variable {d : ℕ}

/-- Variant of `q48b_wbound_of_duality`: the dual side is the abstract coefficient sequence `χ T c`. -/
theorem wbound_of_duality2 {m a : ℝ} (V : NegSobolev d m →L[ℝ] NegSobolev d m)
    (χ : Finset (NonzeroLattice d) → (NonzeroLattice d → ℝ) → NonzeroLattice d → ℝ)
    (hdual : ∀ (S T : Finset (NonzeroLattice d)) (ζ c : NonzeroLattice d → ℝ),
      NegSobolev.eval (V (q48bFin m S ζ)) (q48bTest T c) = ∑ k ∈ S, ζ k * χ T c k)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hdec : ∀ (S T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ),
      ∑ k ∈ S, q48bW k ^ (2 * a) * χ T c k ^ 2 ≤ M ^ 2 * ∑ l ∈ T, q48bW l ^ (2 * a) * c l ^ 2) :
    ∀ S T : Finset (NonzeroLattice d), WBound q48bW (q48bMat m V) S T a M := by
  intro S T ζ
  set Y : NonzeroLattice d → ℝ := fun l => ∑ k ∈ S, q48bMat m V l k * ζ k with hY
  set c : NonzeroLattice d → ℝ := fun l => q48bW l ^ (-2 * a) * Y l with hc
  set φ := q48bTest T c with hφ
  set z := q48bFin m S ζ with hz
  set X : ℝ := ∑ l ∈ T, q48bW l ^ (-2 * a) * Y l ^ 2 with hX
  set Nz : ℝ := ∑ k ∈ S, q48bW k ^ (-2 * a) * ζ k ^ 2 with hNz
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun l _ =>
    mul_nonneg (Real.rpow_nonneg (q48bW_pos l).le _) (sq_nonneg _)
  have hNz0 : 0 ≤ Nz := Finset.sum_nonneg fun l _ =>
    mul_nonneg (Real.rpow_nonneg (q48bW_pos l).le _) (sq_nonneg _)
  show X ≤ M ^ 2 * Nz
  have h1 : NegSobolev.eval (V z) φ = X := by
    rw [hφ, q48b_eval_test]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hz, q48bFin_V]
    simp only [hc, hY]
    have : (∑ k ∈ S, q48bMat m V l k * ζ k) = Y l := rfl
    rw [this]
    ring
  have h2 : NegSobolev.eval (V z) φ = ∑ k ∈ S, ζ k * χ T c k := hdual S T ζ c
  have hcs : (∑ k ∈ S, ζ k * χ T c k) ^ 2 ≤ Nz *
      ∑ k ∈ S, q48bW k ^ (2 * a) * χ T c k ^ 2 := by
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq S (fun k => q48bW k ^ (-a) * ζ k)
      (fun k => q48bW k ^ a * χ T c k)
    have e1 : ∀ k, (q48bW k ^ (-a) * ζ k) * (q48bW k ^ a * χ T c k) = ζ k * χ T c k := by
      intro k
      have := q48b_rpow_neg_mul (q48bW_pos k) a
      calc _ = (q48bW k ^ (-a) * q48bW k ^ a) * (ζ k * χ T c k) := by ring
        _ = _ := by rw [this, one_mul]
    have e2 : ∀ k, (q48bW k ^ (-a) * ζ k) ^ 2 = q48bW k ^ (-2 * a) * ζ k ^ 2 := by
      intro k
      rw [mul_pow, q48b_rpow_sq (q48bW_pos k)]; congr 2; ring
    have e3 : ∀ k, (q48bW k ^ a * χ T c k) ^ 2 = q48bW k ^ (2 * a) * χ T c k ^ 2 := by
      intro k
      rw [mul_pow, q48b_rpow_sq (q48bW_pos k)]
    simp_rw [e1, e2, e3] at hcs0
    exact hcs0
  have hTc : ∑ l ∈ T, q48bW l ^ (2 * a) * c l ^ 2 = X := by
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [hc]
    have hw := q48bW_pos l
    have h2' : (q48bW l ^ (-2 * a)) ^ 2 = q48bW l ^ (-2 * a) * q48bW l ^ (-2 * a) := sq _
    have h3 : q48bW l ^ (2 * a) * q48bW l ^ (-2 * a) = 1 := by
      rw [← Real.rpow_add hw]; simp
    calc q48bW l ^ (2 * a) * (q48bW l ^ (-2 * a) * Y l) ^ 2
        = (q48bW l ^ (2 * a) * q48bW l ^ (-2 * a)) * (q48bW l ^ (-2 * a) * Y l ^ 2) := by ring
      _ = _ := by rw [h3, one_mul]
  have hd := hdec S T c
  rw [hTc] at hd
  have hE : X = ∑ k ∈ S, ζ k * χ T c k := by rw [← h1, h2]
  have hfin : X ^ 2 ≤ (M ^ 2 * Nz) * X := by
    have hh2 : (∑ k ∈ S, ζ k * χ T c k) ^ 2 ≤ Nz * (M ^ 2 * X) :=
      hcs.trans (mul_le_mul_of_nonneg_left hd hNz0)
    rw [← hE] at hh2
    calc X ^ 2 ≤ Nz * (M ^ 2 * X) := hh2
      _ = (M ^ 2 * Nz) * X := by ring
  rcases eq_or_lt_of_le hX0 with h0 | hpos
  · rw [← h0]; positivity
  · have h5 : X * X ≤ (M ^ 2 * Nz) * X := by simpa [sq] using hfin
    exact le_of_mul_le_mul_right h5 hpos

/-! ### Time homogeneity of the frozen propagator (copy of `ThermLin2Dy1`, whose imports contain `sorry`) -/

/-- Time shift of a classical adjoint solution along a constant coefficient path. -/
theorem shift_sol {D : DynData d} {ρβ : Torus d → ℝ} {t u : ℝ} (hu : 0 ≤ u) (hut : u < t)
    {φ : Torus d → ℝ} {f : ℝ → Torus d → ℝ}
    (hf : IsClassicalAdjointSolution D (fun _ => ρβ) t φ f) :
    IsClassicalAdjointSolution D (fun _ => ρβ) (t - u) φ (fun r => f (r + u)) := by
  have hmem : ∀ r ∈ Set.Icc (0 : ℝ) (t - u), r + u ∈ Set.Icc (0 : ℝ) t := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  let ι : Set.Icc (0 : ℝ) (t - u) → Set.Icc (0 : ℝ) t := fun r => ⟨r.1 + u, hmem r.1 r.2⟩
  have hι : Continuous ι :=
    Continuous.subtype_mk (continuous_subtype_val.add continuous_const) _
  refine ⟨fun r hr => hf.c2 _ (hmem r hr), fun j hj => ?_, ?_, fun x r hr => ?_, ?_⟩
  · have hc : Continuous (fun p : Set.Icc (0 : ℝ) (t - u) × Euc d => (ι p.1, p.2)) :=
      (hι.comp continuous_fst).prodMk continuous_snd
    have := (hf.cont_c2 j hj).comp hc
    exact this
  · show f (t - u + u) = φ
    rw [sub_add_cancel]; exact hf.terminal
  · have h1 := hf.time_deriv x (r + u) ⟨by linarith [hr.1], by linarith [hr.2]⟩
    exact HasDerivAt.comp_add_const r u h1
  · have hc : Continuous (fun p : Set.Icc (0 : ℝ) (t - u) × Torus d => (ι p.1, p.2)) :=
      (hι.comp continuous_fst).prodMk continuous_snd
    have := hf.cont_time_deriv.comp hc
    exact this

/-- Time homogeneity of the frozen propagator for continuous data in `H^{m_*}` and `u < t`. -/
theorem shift_gen (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {φ : Torus d → ℝ} (hφc : Continuous φ)
    (hφS : MemSobolev (PDE.mStar d : ℝ) φ) {u t : ℝ} (hu : 0 ≤ u) (hlt : u < t) :
    propagator S.dyn (fun _ => ρβ) u t φ = propagator S.dyn (fun _ => ρβ) 0 (t - u) φ := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hprob : IsProbDensity ρβ := h.1
  have ht : 0 < t := lt_of_le_of_lt hu hlt
  have htu : 0 < t - u := sub_pos.2 hlt
  obtain ⟨R, MB, Λ, VB, hA⟩ :=
    PDE.MFSemigroup.adjointData_frozen S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ hprob hsm hpos (PDE.mStar d)
  obtain ⟨C, Cs, -, -, hmain⟩ :=
    PDE.adjoint_torus_classical hd1 S.s S.hs0 S.hsd (PDE.mStar d) le_rfl R MB Λ VB
  obtain ⟨hcls, hpe, -⟩ := hmain S.dyn 0 t (fun _ => ρβ) (hA 0 t ht) t ⟨ht, le_rfl⟩ φ hφc hφS
  have hsh := shift_sol (ρβ := ρβ) hu hlt hcls
  have hE : ∃ g, IsClassicalAdjointSolution S.dyn (fun _ => ρβ) (t - u) φ g := ⟨_, hsh⟩
  have htu' : t - u ∈ Set.Ioc (0 : ℝ) (t - u) := ⟨htu, le_rfl⟩
  show propagator S.dyn (fun _ => ρβ) u t φ = propagator S.dyn (fun _ => ρβ) 0 (t - u) φ
  rw [hpe u ⟨hu, hlt.le⟩]
  unfold propagator
  rw [dif_pos hE]
  have huniq := PDE.classical_adjoint_unique hd1 S.s S.hs0 S.hsd (PDE.mStar d)
    (by have := PDE.ClassicalPart.three_le_mStar d; omega) R MB Λ VB S.dyn 0 (t - u) (fun _ => ρβ)
    (hA 0 (t - u) htu) (t - u) htu' φ _ _ hE.choose_spec hsh 0 ⟨le_rfl, htu.le⟩
  rw [huniq]
  simp only [zero_add]

/-- Time homogeneity of the frozen propagator on smooth tests, `U^β_{u,t} φ = U^β_{0,t-u} φ` for `0 ≤ u ≤ t`. -/
theorem frozen_shift (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) :
    propagator S.dyn (fun _ => ρβ) u t φ = propagator S.dyn (fun _ => ρβ) 0 (t - u) φ := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hprob : IsProbDensity ρβ := h.1
  rcases hut.eq_or_lt with heq | hlt
  · subst heq
    have e1 := Uniform.Q48e.frozen_self_pos hd1 S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ hprob hsm hpos φ hφ u hu
    have e2 := Uniform.Q48e.frozen_self_pos hd1 S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ hprob hsm hpos φ hφ 0 le_rfl
    rw [sub_self]
    exact e1.trans e2.symm
  · exact shift_gen S h (PDE.MFAux.continuous_of_isCk (PDE.MFSemigroup.isCk_nat_of_isSmooth hφ 1))
      (PDE.MFSemigroup.memSobolev_of_isSmooth hφ _) hu hlt

end HRS.MC.E214K

end
