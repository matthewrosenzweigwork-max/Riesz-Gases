import HRS.Main.GFEVMAux1

/-!
# Packet GFEVM, part 2: functional-analytic helpers

* `gfm_norm_le_of_eval`: the norm of `w ∈ E_m` is bounded by `B` as soon as `|⟨w, φ⟩| ≤ B ‖φ‖_{H^m}` on trigonometric polynomials;
* `gfm_denseRange_embed`: `E_γ ↪ E_{γ+2}` has dense range;
* `gfm_continuousOn_of_dense`: strong continuity of a bounded family from a dense set.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

theorem gfm_memSobolev_mono {m m' : ℝ} {φ : Torus d → ℝ} (hφ : MemSobolev m φ) (h : m' ≤ m) :
    MemSobolev m' φ :=
  memSobolev_of_memHs m' φ hφ.1 ((hsNormSq_coeffOf m φ hφ).1.mono h)

theorem gfm_sobolevNorm_phiOf (m : ℝ) (c : NonzeroLattice d →₀ ℝ) :
    sobolevNorm m (phiOf m c) = ‖eFin d c‖ := by
  unfold phiOf
  rw [q48bTest_sobolevNorm, norm_eFin]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  have hj := Torus.jp_pos l.1
  show Lattice.jp l.1 ^ (2 * m) * (c l / Lattice.jp l.1 ^ m) ^ 2 = c l ^ 2
  rw [div_pow, Torus.jp_rpow_sq]
  field_simp

theorem gfm_memSobolev_phiOf (m : ℝ) (c : NonzeroLattice d →₀ ℝ) : MemSobolev m (phiOf m c) :=
  MFSemigroup.memSobolev_of_isSmooth (phiOf_smooth m c) m

theorem gfm_lpOf_phiOf (m : ℝ) (c : NonzeroLattice d →₀ ℝ) :
    lpOf m (gfm_memSobolev_phiOf m c) = (show NegSobolev d m from eFin d c) := by
  refine gfev_ext fun k => ?_
  rw [coord_lpOf]
  show Lattice.jp k.1 ^ m * Torus.funRealCoeff (phiOf m c) k = (eFin d c) k
  rw [eFin_apply]
  unfold phiOf
  rw [q48bTest_coeff]
  have hne : Lattice.jp k.1 ^ m ≠ 0 := (Real.rpow_pos_of_pos (Torus.jp_pos _) _).ne'
  by_cases hk : k ∈ c.support
  · rw [if_pos hk]
    field_simp
  · rw [if_neg hk]
    simp [Finsupp.notMem_support_iff.1 hk]

theorem gfm_norm_le_of_eval {m : ℝ} (w : NegSobolev d m) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ c : NonzeroLattice d →₀ ℝ, |NegSobolev.eval w (phiOf m c)| ≤ B * ‖eFin d c‖) :
    ‖w‖ ≤ B := by
  have hdense : DenseRange (fun c : NonzeroLattice d →₀ ℝ => (show NegSobolev d m from eFin d c)) :=
    denseRange_eFin d
  have hclosed : IsClosed {y : NegSobolev d m | |inner ℝ w y| ≤ B * ‖y‖} :=
    isClosed_le (continuous_const.inner continuous_id |>.abs) (continuous_const.mul continuous_norm)
  have hall : ∀ y : NegSobolev d m, |inner ℝ w y| ≤ B * ‖y‖ := by
    intro y
    have hsub : Set.range (fun c : NonzeroLattice d →₀ ℝ => (show NegSobolev d m from eFin d c)) ⊆
        {y : NegSobolev d m | |inner ℝ w y| ≤ B * ‖y‖} := by
      rintro _ ⟨c, rfl⟩
      show |inner ℝ w (show NegSobolev d m from eFin d c)| ≤ B * ‖(show NegSobolev d m from eFin d c)‖
      have := h c
      rw [eval_eq_inner m w (gfm_memSobolev_phiOf m c), gfm_lpOf_phiOf m c] at this
      exact this
    have := hclosed.closure_subset_iff.2 hsub
    rw [hdense.closure_eq] at this
    exact this (Set.mem_univ y)
  have h1 := hall w
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at h1
  by_cases h0 : ‖w‖ = 0
  · rw [h0]; exact hB
  · have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

theorem gfm_denseRange_embed (γ : ℝ) :
    DenseRange (NegSobolev.embed (γ + 2) : NegSobolev d γ → NegSobolev d (γ + 2)) := by
  classical
  have hdense : DenseRange (fun c : NonzeroLattice d →₀ ℝ => (show NegSobolev d (γ + 2) from eFin d c)) :=
    denseRange_eFin d
  refine Dense.mono ?_ hdense
  rintro _ ⟨c, rfl⟩
  refine ⟨(show NegSobolev d γ from
    eFin d (secFin (fun k => Lattice.jp k.1 ^ ((γ + 2) - γ) * c k) c.support)), ?_⟩
  refine gfev_ext fun k => ?_
  rw [gfev_coord_embed (by linarith : γ ≤ γ + 2)]
  have hj := Torus.jp_pos k.1
  show Lattice.jp k.1 ^ (-(γ + 2)) * (Lattice.jp k.1 ^ γ *
    (eFin d (secFin (fun k => Lattice.jp k.1 ^ ((γ + 2) - γ) * c k) c.support)) k) = (eFin d c) k
  rw [eFin_apply, eFin_apply, secFin_apply]
  by_cases hk : k ∈ c.support
  · rw [if_pos hk, ← mul_assoc, ← Real.rpow_add hj, ← mul_assoc, ← Real.rpow_add hj]
    have : (-(γ + 2) + γ) + ((γ + 2) - γ) = 0 := by ring
    rw [this]
    simp
  · rw [if_neg hk]
    simp [Finsupp.notMem_support_iff.1 hk]

theorem gfm_continuousOn_of_dense {X : Type*} [PseudoMetricSpace X] {S : Set X} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Vf : X → E →L[ℝ] F} (M : ℝ) (hb : ∀ x ∈ S, ‖Vf x‖ ≤ M) {Dn : Set E} (hD : Dense Dn)
    (hc : ∀ y ∈ Dn, ContinuousOn (fun x => Vf x y) S) (y : E) :
    ContinuousOn (fun x => Vf x y) S := by
  rw [Metric.continuousOn_iff]
  intro b hbS ε hε
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hb b hbS)
  have hη : 0 < ε / (3 * (M + 1)) := by positivity
  obtain ⟨y', hy'D, hy'⟩ := hD.exists_dist_lt y hη
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousOn_iff.1 (hc y' hy'D) b hbS (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun a haS hab => ?_⟩
  have h1 : dist (Vf a y) (Vf a y') ≤ ε / 3 := by
    rw [dist_eq_norm, ← map_sub]
    calc ‖Vf a (y - y')‖ ≤ ‖Vf a‖ * ‖y - y'‖ := (Vf a).le_opNorm _
      _ ≤ M * (ε / (3 * (M + 1))) := by
          rw [← dist_eq_norm]
          exact mul_le_mul (hb a haS) hy'.le dist_nonneg hM0
      _ ≤ ε / 3 := by
          rw [show M * (ε / (3 * (M + 1))) = ε / 3 * (M / (M + 1)) by field_simp]
          have : M / (M + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          nlinarith [hε]
  have h3 : dist (Vf b y') (Vf b y) ≤ ε / 3 := by
    rw [dist_eq_norm, ← map_sub]
    calc ‖Vf b (y' - y)‖ ≤ ‖Vf b‖ * ‖y' - y‖ := (Vf b).le_opNorm _
      _ ≤ M * (ε / (3 * (M + 1))) := by
          rw [← dist_eq_norm, dist_comm]
          exact mul_le_mul (hb b hbS) hy'.le dist_nonneg hM0
      _ ≤ ε / 3 := by
          rw [show M * (ε / (3 * (M + 1))) = ε / 3 * (M / (M + 1)) by field_simp]
          have : M / (M + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          nlinarith [hε]
  have h2 := hδ' a haS hab
  calc dist (Vf a y) (Vf b y) ≤ dist (Vf a y) (Vf a y') + dist (Vf a y') (Vf b y') + dist (Vf b y') (Vf b y) :=
        dist_triangle4 _ _ _ _
    _ < ε := by linarith

end HRS.GF
