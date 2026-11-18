import HRS.MC.S7PIDKMain
import HRS.MC.S7PIDTKer
import HRS.Main.GFB4Aux6

/-!
# Packet PI-D, sub-packet S (part 1): auxiliary lemmas for the series form of `J` (D7)

* `S7PIDS_pq`: the splitting `A = p * q` with `p = √|A|`, `q = sgn(A) √|A|` (measurable, bounded by `√B`);
* `S7PIDS_fc_embed`, `S7PIDS_eval_embed`: `z^u = ofSeq m (fourierCoeff (zr u))` has the Fourier coefficients of
  `zr u ∈ E_r` and pairs with test functions as `zr u`;
* `S7PIDS_meas_eval`, `S7PIDS_bound_eval`: measurability of `u ↦ z^u(ψ)` and the bound `|z^u(ψ)| ≤ M ‖ψ‖_{H^r}`;
* `S7PIDS_meas_V`: measurability of `u ↦ (V^{t,u} e_k)(φ)` on a measurable subset of `(0,T]` where `u ≤ t`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDS

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

/-- `A = p q` with `p = √|A|`, `q = sgn(A) √|A|`. -/
theorem S7PIDS_pq {A : ℝ → ℝ} (hA : Measurable A) {B : ℝ} (hB : ∀ u, |A u| ≤ B) :
    ∃ p q : ℝ → ℝ, Measurable p ∧ Measurable q ∧ (∀ u, |p u| ≤ Real.sqrt B) ∧
      (∀ u, |q u| ≤ Real.sqrt B) ∧ ∀ u, p u * q u = A u := by
  refine ⟨fun u => Real.sqrt |A u|, fun u => (if 0 ≤ A u then (1 : ℝ) else -1) * Real.sqrt |A u|,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact Real.continuous_sqrt.measurable.comp hA.abs
  · refine Measurable.mul ?_ (Real.continuous_sqrt.measurable.comp hA.abs)
    exact Measurable.ite (measurableSet_le measurable_const hA) measurable_const measurable_const
  · intro u
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hB u)
  · intro u
    have h1 : |(if 0 ≤ A u then (1 : ℝ) else -1)| = 1 := by split_ifs <;> simp
    rw [abs_mul, h1, one_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hB u)
  · intro u
    have hs : Real.sqrt |A u| * Real.sqrt |A u| = |A u| := Real.mul_self_sqrt (abs_nonneg _)
    by_cases h : 0 ≤ A u
    · simp only [if_pos h, one_mul]
      rw [hs, abs_of_nonneg h]
    · have h' : A u < 0 := not_le.1 h
      simp only [if_neg h]
      calc Real.sqrt |A u| * (-1 * Real.sqrt |A u|) = -(Real.sqrt |A u| * Real.sqrt |A u|) := by ring
        _ = -|A u| := by rw [hs]
        _ = A u := by rw [abs_of_neg h']; ring

theorem S7PIDS_memℓp_embed {r m : ℝ} (hrm : r ≤ m) (F : NegSobolev d r) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff F k) 2 := by
  have hcoord : ∀ k : NonzeroLattice d,
      |Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff F k| ≤ |NegSobolev.coord F k| := by
    intro k
    have hj := Torus.jp_pos k.1
    have : Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff F k =
        Lattice.jp k.1 ^ (r - m) * NegSobolev.coord F k := by
      unfold NegSobolev.fourierCoeff
      rw [← mul_assoc, ← Real.rpow_add hj]
      ring_nf
    rw [this, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hj _)]
    have h1 : Lattice.jp k.1 ^ (r - m) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (Torus.jp_ge_one _) (by linarith)
    exact mul_le_of_le_one_left (abs_nonneg _) h1
  obtain ⟨h3, -⟩ := NegSobolev.coord_sq F
  rw [Torus.memℓp_two_iff]
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) h3
  calc _ = |Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff F k| ^ 2 := (sq_abs _).symm
    _ ≤ |NegSobolev.coord F k| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hcoord k) 2
    _ = _ := sq_abs _

theorem S7PIDS_fc_embed {r m : ℝ} (hrm : r ≤ m) (F : NegSobolev d r) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (NegSobolev.ofSeq m (fun j => NegSobolev.fourierCoeff F j) : NegSobolev d m) k =
      NegSobolev.fourierCoeff F k := by
  have hmem := S7PIDS_memℓp_embed hrm F
  have hj := Torus.jp_pos k.1
  have e : NegSobolev.fourierCoeff
      (NegSobolev.ofSeq m (fun j => NegSobolev.fourierCoeff F j) : NegSobolev d m) k =
      Lattice.jp k.1 ^ m * NegSobolev.coord
        (NegSobolev.ofSeq m (fun j => NegSobolev.fourierCoeff F j) : NegSobolev d m) k := rfl
  rw [e, NegSobolev.coord_ofSeq_of_mem _ hmem k, ← mul_assoc, ← Real.rpow_add hj]
  simp

theorem S7PIDS_eval_embed {r m : ℝ} (hrm : r ≤ m) (F : NegSobolev d r) (ψ : Torus d → ℝ) :
    NegSobolev.eval
      (NegSobolev.ofSeq m (fun j => NegSobolev.fourierCoeff F j) : NegSobolev d m) ψ =
      NegSobolev.eval F ψ := by
  unfold NegSobolev.eval
  exact tsum_congr fun k => by rw [S7PIDS_fc_embed hrm F k]

theorem S7PIDS_meas_eval {r m : ℝ} (hrm : r ≤ m) {ψ : Torus d → ℝ} (hψ : MemSobolev r ψ)
    {zr : ℝ → NegSobolev d r} (hzr : Measurable zr) :
    Measurable fun u => NegSobolev.eval
      (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) : NegSobolev d m) ψ := by
  have h : (fun u => NegSobolev.eval
      (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) : NegSobolev d m) ψ) =
      fun u => HRS.GF.gfb4_ell r ψ (zr u) := by
    funext u
    rw [S7PIDS_eval_embed hrm (zr u) ψ, HRS.GF.gfb4_ell_apply hψ]
  rw [h]
  exact (HRS.GF.gfb4_ell r ψ).continuous.measurable.comp hzr

theorem S7PIDS_bound_eval {r m : ℝ} (hrm : r ≤ m) {ψ : Torus d → ℝ} (hψ : MemSobolev r ψ) {Cψ : ℝ}
    (hC : sobolevNorm r ψ ≤ Cψ) {F : NegSobolev d r} {M : ℝ} (hF : ‖F‖ ≤ M) :
    |NegSobolev.eval
      (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff F k) : NegSobolev d m) ψ| ≤ M * Cψ := by
  rw [S7PIDS_eval_embed hrm F ψ]
  refine (NegSobolev.abs_eval_le F ψ hψ.2).trans ?_
  have h1 : Real.sqrt (∑' k : NonzeroLattice d,
      Lattice.jp k.1 ^ (2 * r) * Torus.funRealCoeff ψ k ^ 2) ≤ sobolevNorm r ψ := by
    unfold sobolevNorm
    exact Real.sqrt_le_sqrt (by linarith [sq_nonneg (Torus.mean ψ)])
  exact mul_le_mul hF (h1.trans hC) (Real.sqrt_nonneg _) ((norm_nonneg _).trans hF)

/-- Measurability of `u ↦ (V^{t,u} e_k)(φ)` on a measurable `S ⊆ (0,T]` with `u ≤ t` on `S`. -/
theorem S7PIDS_meas_V (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (k : NonzeroLattice d) {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioc 0 T)
    (hSt : ∀ u ∈ S, u ≤ t) :
    AEStronglyMeasurable (fun u => NegSobolev.eval (Vprop R.D R.ρ m t u (modeVec m k)) φ)
      (volume.restrict S) := by
  obtain ⟨Cb, -, hker⟩ := HRS.MC.Sec7.S7PIDT.S7PIDT_ker R m hm T hT
  have h1 := (hker 0 T le_rfl hT.le le_rfl (modeVec m k) t ht.1 ht.2).1
  have hcont : Continuous fun x : NegSobolev d m => NegSobolev.eval x φ := by
    refine continuous_iff_continuousAt.2 fun x₀ => ?_
    exact HRS.MC.Sec7.S7PIDK.S7PIDK_eval_tendsto (HRS.MC.Sec7.S7PIDK.S7PIDK_summable_smooth m hφ)
      (tendsto_id (x := 𝓝 x₀))
  have h2 := hcont.comp_aestronglyMeasurable h1
  have h3 := h2.mono_measure (Measure.restrict_mono hSsub le_rfl)
  refine h3.congr ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun u hu => ?_))
  simp only [Function.comp, causalVec, if_pos (hSt u hu)]

end HRS.MC.Sec7.S7PIDS

end
