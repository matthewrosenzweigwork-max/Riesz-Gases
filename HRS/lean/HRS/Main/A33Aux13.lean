import Mathlib
import HRS.Main.A33Aux12

/-!
# Packet A33, helper 13: the transported initial field `V^{t,0} F`
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A33

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

/-- The transported field `⟨e_k, V^{t,0}F⟩ = F(U^{0,t} e_k)` (as `HRS.Main.transportField`). -/
def a33_transport (S : A33Setup d) (t : ℝ) (F : NegSobolev d (S.J : ℝ)) :
    NegSobolev d (S.J : ℝ) :=
  NegSobolev.ofSeq (S.J : ℝ) fun k => NegSobolev.eval F (propagator S.D S.ρ 0 t (Torus.realMode k))

namespace A33Setup

variable (S : A33Setup d)

theorem ell_tr {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) (F : NegSobolev d (S.J : ℝ)) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) (e : ℕ ≃ NonzeroLattice d) (n : ℕ) :
    S.ell t F (a33_tr φ e n) =
      ∑ i ∈ Finset.range n, Torus.funRealCoeff φ (e i) * S.ell t F (Torus.realMode (e i)) := by
  induction n with
  | zero =>
    have h0 : a33_tr φ e 0 = fun _ => (0 : ℝ) := by
      funext y; simp [a33_tr]
    rw [h0, S.ell_const ht F 0]; simp
  | succ n ih =>
    have h1 : a33_tr φ e (n + 1) = fun y => 1 * a33_tr φ e n y +
        Torus.funRealCoeff φ (e n) * Torus.realMode (e n) y := by
      funext y; simp [a33_tr, Finset.sum_range_succ]
    rw [h1, S.ell_lin ht F (a33_tr_smooth φ e n) (HRS.FieldSingAux.isSmooth_realMode (e n)) 1
      (Torus.funRealCoeff φ (e n)), ih, Finset.sum_range_succ]
    ring

theorem ell_split {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) (F : NegSobolev d (S.J : ℝ)) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) (e : ℕ ≃ NonzeroLattice d) (n : ℕ) :
    S.ell t F φ = S.ell t F (a33_res φ e n) +
      ∑ i ∈ Finset.range n, Torus.funRealCoeff φ (e i) * S.ell t F (Torus.realMode (e i)) := by
  have hm : Torus.IsSmooth (fun x => 1 * (fun _ : Torus d => Torus.mean φ) x + 1 * a33_tr φ e n x) := by
    unfold Torus.IsSmooth Torus.IsCk
    have h1 := a33_tr_smooth φ e n
    unfold Torus.IsSmooth Torus.IsCk at h1
    exact (contDiff_const.mul contDiff_const).add (contDiff_const.mul h1)
  have hφe : φ = fun x => 1 * a33_res φ e n x + 1 *
      (fun x => 1 * (fun _ : Torus d => Torus.mean φ) x + 1 * a33_tr φ e n x) x := by
    funext x; simp [a33_res]
  conv_lhs => rw [hφe]
  rw [S.ell_lin ht F (a33_res_smooth hφ e n) hm 1 1,
    S.ell_lin ht F (a33_isSmooth_const _) (a33_tr_smooth φ e n) 1 1, S.ell_const ht F,
    S.ell_tr ht F hφ e n]
  ring

theorem ell_bound {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : NegSobolev d (S.J : ℝ)) {ψ : Torus d → ℝ}, Torus.IsSmooth ψ →
      |S.ell t F ψ| ≤ ‖F‖ * (K * sobolevNorm (S.J : ℝ) ψ) := by
  obtain ⟨K, hK0, hK⟩ := S.U_bound
  refine ⟨K, hK0, fun F ψ hψ => ?_⟩
  obtain ⟨hm, hb⟩ := hK ht hψ
  unfold ell
  refine (a33_abs_eval_le F (a33_ws_of_memSobolev hm)).trans ?_
  exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

theorem transport_memℓp {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) (F : NegSobolev d (S.J : ℝ)) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(S.J : ℝ)) *
      NegSobolev.eval F (propagator S.D S.ρ 0 t (Torus.realMode k))) 2 := by
  classical
  rw [Torus.memℓp_two_iff]
  obtain ⟨K, hK0, hK⟩ := S.ell_bound ht
  set a : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-(S.J : ℝ)) *
    NegSobolev.eval F (propagator S.D S.ρ 0 t (Torus.realMode k)) with ha
  have hell : ∀ k, S.ell t F (Torus.realMode k) = Lattice.jp k.1 ^ (S.J : ℝ) * a k := by
    intro k
    have hj := Torus.jp_pos k.1
    simp only [ha, ell]
    rw [← mul_assoc, ← Real.rpow_add hj]
    simp
  refine summable_of_sum_le (c := (‖F‖ * K) ^ 2) (fun k => sq_nonneg _) (fun s => ?_)
  set c : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-(S.J : ℝ)) * a k with hc
  set A : ℝ := ∑ k ∈ s, a k ^ 2 with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hpoly : S.ell t F (HRS.FieldSingAux.trigPoly s c) = A := by
    rw [S.ell_trigPoly ht F s c, hA]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hell k, hc]
    have hj := Torus.jp_pos k.1
    simp only
    rw [show Lattice.jp k.1 ^ (-(S.J : ℝ)) * a k * (Lattice.jp k.1 ^ (S.J : ℝ) * a k) =
      (Lattice.jp k.1 ^ (-(S.J : ℝ)) * Lattice.jp k.1 ^ (S.J : ℝ)) * a k ^ 2 by ring,
      ← Real.rpow_add hj]
    simp
  have hsob : sobolevNorm (S.J : ℝ) (HRS.FieldSingAux.trigPoly s c) = Real.sqrt A := by
    unfold sobolevNorm
    rw [HRS.FieldSingAux.mean_trigPoly]
    congr 1
    have : ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * (S.J : ℝ)) *
        Torus.funRealCoeff (HRS.FieldSingAux.trigPoly s c) k ^ 2 = A := by
      simp_rw [HRS.FieldSingAux.funRealCoeff_trigPoly]
      rw [tsum_eq_sum (s := s)]
      · refine Finset.sum_congr rfl fun k hk => ?_
        rw [if_pos hk, hc]
        have hj := Torus.jp_pos k.1
        simp only
        rw [mul_pow, ← Real.rpow_natCast (Lattice.jp k.1 ^ (-(S.J : ℝ))) 2, ← Real.rpow_mul hj.le,
          ← mul_assoc, ← Real.rpow_add hj]
        have : (2 * (S.J : ℝ) + -(S.J : ℝ) * ((2 : ℕ) : ℝ)) = 0 := by push_cast; ring
        rw [this]; simp
      · intro k hk; simp [hk]
    rw [this]; simp
  have hb := hK F (HRS.FieldSingAux.isSmooth_trigPoly s c)
  rw [hpoly, hsob] at hb
  have hb' : A ≤ ‖F‖ * K * Real.sqrt A := by
    calc A = |A| := (abs_of_nonneg hA0).symm
      _ ≤ _ := hb
      _ = _ := by ring
  by_cases h0 : A = 0
  · rw [h0]; positivity
  · have hpos : 0 < Real.sqrt A := Real.sqrt_pos.2 (lt_of_le_of_ne hA0 (Ne.symm h0))
    have h1 : Real.sqrt A ≤ ‖F‖ * K := by
      by_contra hcon
      push_neg at hcon
      have := mul_lt_mul_of_pos_right hcon hpos
      have h2 : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA0
      nlinarith
    calc A = Real.sqrt A * Real.sqrt A := (Real.mul_self_sqrt hA0).symm
      _ ≤ (‖F‖ * K) * (‖F‖ * K) := mul_self_le_mul_self hpos.le h1
      _ = _ := by ring

theorem eval_transport {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) (e : ℕ ≃ NonzeroLattice d)
    (F : NegSobolev d (S.J : ℝ)) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    NegSobolev.eval (a33_transport S t F) φ = NegSobolev.eval F (S.U t φ) := by
  have hmem := S.transport_memℓp ht F
  have hfc : ∀ k, NegSobolev.fourierCoeff (a33_transport S t F) k =
      S.ell t F (Torus.realMode k) := fun k =>
    HRS.Q41.q41_fourierCoeff_ofSeq (m := (S.J : ℝ)) hmem k
  have h1 := a33_eval_tendsto e (a33_transport S t F) hφ
  simp_rw [hfc] at h1
  -- the other limit
  obtain ⟨K, hK0, hK⟩ := S.ell_bound ht
  have h2 : Tendsto (fun n => S.ell t F (a33_res φ e n)) atTop (𝓝 0) := by
    have h3 := (a33_trunc_sob hφ e (S.J : ℝ)).2
    have h4 : Tendsto (fun n => ‖F‖ * (K * sobolevNorm (S.J : ℝ) (a33_res φ e n))) atTop (𝓝 0) := by
      simpa using (h3.const_mul K).const_mul ‖F‖
    refine squeeze_zero_norm (fun n => ?_) h4
    rw [Real.norm_eq_abs]
    exact hK F (a33_res_smooth hφ e n)
  have h5 : Tendsto (fun n => S.ell t F (a33_res φ e n) +
      ∑ i ∈ Finset.range n, Torus.funRealCoeff φ (e i) * S.ell t F (Torus.realMode (e i)))
      atTop (𝓝 (0 + NegSobolev.eval (a33_transport S t F) φ)) := by
    refine h2.add ?_
    refine h1.congr fun n => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h6 : (fun n => S.ell t F (a33_res φ e n) +
      ∑ i ∈ Finset.range n, Torus.funRealCoeff φ (e i) * S.ell t F (Torus.realMode (e i))) =
      fun _ => S.ell t F φ := by
    funext n; rw [S.ell_split ht F hφ e n]
  rw [h6] at h5
  have := tendsto_nhds_unique h5 tendsto_const_nhds
  unfold ell at this
  rw [zero_add] at this
  exact this

theorem transport_measurable {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) (e : ℕ ≃ NonzeroLattice d) :
    Measurable (a33_transport S t : NegSobolev d (S.J : ℝ) → NegSobolev d (S.J : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := S.U_bound
  exact HRS.Q41.q41_measurable_ofSeq (m := (S.J : ℝ)) e e.surjective
    (fun k F => NegSobolev.eval F (propagator S.D S.ρ 0 t (Torus.realMode k)))
    (fun k => a33_eval_measurable e (a33_ws_of_memSobolev
      (hK ht (HRS.FieldSingAux.isSmooth_realMode k)).1))

end A33Setup

end HRS.A33
