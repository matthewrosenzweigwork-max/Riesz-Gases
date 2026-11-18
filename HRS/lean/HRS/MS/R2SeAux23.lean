import HRS.MS.R2SeAux22

/-!
# S9.9 `r2_static_edgeworth`, packet 23: Cauchy-Schwarz and the per-`l` estimate of the quadratic term

Worker S99, namespace `S99`.

* `s99_cs`: `∫ |f| |g| ≤ (∫ f²)^{1/2} (∫ g²)^{1/2}`;
* `s99_Bd_const`: constants lie in every `Bd n`;
* `s99_kap_bd`: `|κ_{w,m}| ≤ ‖w‖_∞ K b_m`;
* `s99_Mab_l`: the `l`-th term of the expansion of `E[Y_u Y_v ψ(W_N)]`, `ψ ∈ Bd 4`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s99_cs {α : Type*} [MeasurableSpace α] {P : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ∫ x, |f x| * |g x| ∂P ≤ Real.sqrt (∫ x, f x ^ 2 ∂P) * Real.sqrt (∫ x, g x ^ 2 ∂P) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) Real.HolderConjugate.two_two
    (f := fun x => |f x|) (g := fun x => |g x|) (Filter.Eventually.of_forall fun x => abs_nonneg _)
    (Filter.Eventually.of_forall fun x => abs_nonneg _) (by rw [ENNReal.ofReal_ofNat]; exact hf.abs) (by rw [ENNReal.ofReal_ofNat]; exact hg.abs)
  have e1 : ∫ a, |f a| ^ (2 : ℝ) ∂P = ∫ a, f a ^ 2 ∂P := by
    congr 1; funext a; rw [Real.rpow_two, sq_abs]
  have e2 : ∫ a, |g a| ^ (2 : ℝ) ∂P = ∫ a, g a ^ 2 ∂P := by
    congr 1; funext a; rw [Real.rpow_two, sq_abs]
  rw [e1, e2] at h
  simpa [Real.sqrt_eq_rpow] using h

/-- Cauchy-Schwarz with square-integral bounds. -/
theorem s99_cs_bd {α : Type*} [MeasurableSpace α] {P : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) {A B : ℝ} (hA : ∫ x, f x ^ 2 ∂P ≤ A ^ 2)
    (hB : ∫ x, g x ^ 2 ∂P ≤ B ^ 2) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) :
    ∫ x, |f x| * |g x| ∂P ≤ A * B := by
  refine (s99_cs hf hg).trans ?_
  refine mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) hA0
  · exact (Real.sqrt_le_sqrt hA).trans_eq (Real.sqrt_sq hA0)
  · exact (Real.sqrt_le_sqrt hB).trans_eq (Real.sqrt_sq hB0)

theorem s99_Bd_const (n : ℕ) : Bd n (fun _ : SeqL2 => (1 : ℝ)) := by
  refine ⟨contDiff_const, fun i _ z => ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [iteratedFDeriv_const_of_ne (by omega)]; simp

theorem s99_pd_const (l : ℕ) (z : SeqL2) : pd (fun _ : SeqL2 => (1 : ℝ)) l z = 0 := by
  simp [pd]

theorem s99_memLp_two_of_bdd {α : Type*} [MeasurableSpace α] {P : Measure α} [IsFiniteMeasure P]
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : MemLp f 2 P :=
  MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

section Mab

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

theorem s99_kap_bd {w : Euc d → ℝ} {cw : ℝ} (hwm : Measurable w) (hwbd : ∀ x, |w x| ≤ cw) (m : ℕ) :
    |kap d s a β γ w φ m| ≤ cw * (F.K * cbNorm (J1 d) (φ m)) := by
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have hcw0 : 0 ≤ cw := (abs_nonneg _).trans (hwbd 0)
  have ham : ∀ x, |aRep d s a β γ (φ m) x| ≤ F.K * cbNorm (J1 d) (φ m) := fun x => by
    have h1 := s99_norm_iter_le_cb (F.amem m) (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
    exact h1.trans (F.anorm m)
  have := norm_integral_le_of_norm_le_const (μ := thermalMeasure d s a β)
    (f := fun x => w x * aRep d s a β γ (φ m) x) (C := cw * (F.K * cbNorm (J1 d) (φ m)))
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hwbd x) (ham x) (abs_nonneg _) hcw0)
  simpa [Real.norm_eq_abs, kap] using this

end Mab

end S99

end
