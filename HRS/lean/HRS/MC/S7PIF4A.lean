import HRS.MC.S7PIS1Eval
import HRS.MC.S7PIS1Path2
import HRS.MC.S7PIEMeas
import HRS.MC.S7PIF1Brk
import HRS.MC.RegSet
import HRS.Main.A33Aux14

/-!
# Packet piF4, part A: evaluation functionals, the measurability and the bound of `r ↦ eval (B r) (U^{r,τ} φ)`

* `S7PIF4_rho_smooth`: `R.ρ t` is smooth for `t ≥ 0`;
* `S7PIF4_evalCLM`: `F ↦ eval F ψ` is a continuous linear functional on `E_m` (for `ψ` with weighted summable coefficients);
* `S7PIF4_core`: the uniform bound of `V^{t,u}` and its joint continuity in `(u, F)` (from PI-E);
* `S7PIF4_eval_prop_bound`, `S7PIF4_eval_prop_aesm`: `|eval F (U^{r,τ} φ)| ≤ C ‖F‖` and a.e. strong measurability of
  `a ↦ eval (B a) (U^{rr a,τ} φ)` for a.e. strongly measurable `B` (through `S1`, `eval (V^{τ,r} F) φ = eval F (U^{r,τ} φ)`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF4

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIS1

variable {d : ℕ}

/-- `R.ρ t` is smooth for `t ≥ 0`. -/
theorem S7PIF4_rho_smooth (R : Regime d) {t : ℝ} (ht : 0 ≤ t) : Torus.IsSmooth (R.ρ t) := by
  choose Λ hΛ using HRS.MC.RegSet.reg_proof R
  unfold Torus.IsSmooth Torus.IsCk
  have : ∀ n : ℕ, ContDiff ℝ n (Torus.lift (R.ρ t)) := fun n => (hΛ n t t ⟨ht, le_rfl⟩).1
  exact contDiff_infty.2 this

/-- `F ↦ eval F ψ` is a continuous linear functional on `E_m`. -/
def S7PIF4_evalCLM (m : ℝ) {ψ : Torus d → ℝ} (hψ : A33WS m ψ) : NegSobolev d m →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun F => NegSobolev.eval F ψ
      map_add' := fun F G => a33_eval_add_left F G hψ
      map_smul' := fun c F => by simpa using HRS.MC.Sec7.S7PIF1.S7PIF1_eval_smul c F ψ }
    (Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff ψ k ^ 2))
    (fun F => by
      have := NegSobolev.abs_eval_le F ψ hψ
      rw [Real.norm_eq_abs, mul_comm]
      exact this)

theorem S7PIF4_evalCLM_apply (m : ℝ) {ψ : Torus d → ℝ} (hψ : A33WS m ψ) (F : NegSobolev d m) :
    S7PIF4_evalCLM m hψ F = NegSobolev.eval F ψ := rfl

theorem S7PIF4_eval_sub (m : ℝ) {ψ : Torus d → ℝ} (hψ : A33WS m ψ) (F G : NegSobolev d m) :
    NegSobolev.eval (F - G) ψ = NegSobolev.eval F ψ - NegSobolev.eval G ψ :=
  map_sub (S7PIF4_evalCLM m hψ) F G

theorem S7PIF4_eval_zero_fun (m : ℝ) (F : NegSobolev d m) :
    NegSobolev.eval F (0 : Torus d → ℝ) = 0 := by
  exact HRS.A33.a33_eval_const F (0 : ℝ)

/-- The uniform bound of `V^{t,u}` on `E_m` and its joint continuity in `(u, F)` on `[0,t]`. -/
theorem S7PIF4_core (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ CV : ℝ, 0 ≤ CV ∧
      (∀ t ∈ Set.Ioc 0 T, ∀ u ∈ Set.Icc 0 t, ∀ F : NegSobolev d m, ‖Vprop R.D R.ρ m t u F‖ ≤ CV * ‖F‖) ∧
      (∀ t ∈ Set.Ioc 0 T,
        Continuous fun p : Set.Icc (0 : ℝ) t × NegSobolev d m => Vprop R.D R.ρ m t p.1.1 p.2) := by
  obtain ⟨J, k, hk, hJ, hm0, hm1, H⟩ := S7PIS1_data R m hm T hT
  have P : PIEData J R.D R.ρ T m (k + 1) :=
    ⟨H, by omega, by omega, by push_cast; linarith, by push_cast; linarith⟩
  obtain ⟨CV, hCV0, hCV⟩ := pie_Vbound H m (k + 1) (by omega) (by omega) (by push_cast; linarith)
    (by push_cast; linarith)
  exact ⟨CV, hCV0, hCV, fun t ht => pie_V_jointCont P ht⟩

/-- a.e. strong measurability of `a ↦ V^{τ,rr a}(B a)` -/
theorem S7PIF4_V_aesm_gen {m : ℝ} {D : DynData d} {ρ : ℝ → Torus d → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hjc : Continuous fun p : Set.Icc (0 : ℝ) τ × NegSobolev d m => Vprop D ρ m τ p.1.1 p.2)
    {α : Type*} [MeasurableSpace α] {ν : Measure α} {rr : α → ℝ} {B : α → NegSobolev d m}
    (hr : Measurable rr) (hB : AEStronglyMeasurable B ν) (hrτ : ∀ᵐ a ∂ν, rr a ∈ Set.Icc (0 : ℝ) τ) :
    AEStronglyMeasurable (fun a => Vprop D ρ m τ (rr a) (B a)) ν := by
  have hproj : Continuous (fun p : ℝ × NegSobolev d m => (Set.projIcc 0 τ hτ p.1, p.2)) :=
    (continuous_projIcc.comp continuous_fst).prodMk continuous_snd
  have hΦ : Continuous (fun p : ℝ × NegSobolev d m => Vprop D ρ m τ (Set.projIcc 0 τ hτ p.1).1 p.2) := by
    have h : Continuous ((fun p : Set.Icc (0 : ℝ) τ × NegSobolev d m => Vprop D ρ m τ p.1.1 p.2) ∘
        (fun p : ℝ × NegSobolev d m => (Set.projIcc 0 τ hτ p.1, p.2))) := Continuous.comp hjc hproj
    exact h
  have hg : AEStronglyMeasurable (fun a => (rr a, B a)) ν := hr.aestronglyMeasurable.prodMk hB
  refine (hΦ.comp_aestronglyMeasurable hg).congr ?_
  filter_upwards [hrτ] with a ha
  show Vprop D ρ m τ (Set.projIcc 0 τ hτ (rr a)).1 (B a) = _
  rw [Set.projIcc_of_mem _ ha]

/-- `|eval F (U^{r,τ} φ)| ≤ C ‖F‖` uniformly in `0 ≤ r ≤ τ ≤ T`. -/
theorem S7PIF4_eval_prop_bound (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Ioc 0 T, ∀ r ∈ Set.Icc 0 τ, ∀ F : NegSobolev d m,
      |NegSobolev.eval F (propagator R.D R.ρ r τ φ)| ≤ C * ‖F‖ := by
  obtain ⟨CV, hCV0, hCV, -⟩ := S7PIF4_core R m hm T hT
  have hws : A33WS m φ := a33_ws_smooth m hφ
  set ℓ := S7PIF4_evalCLM m hws
  refine ⟨CV * ‖ℓ‖, mul_nonneg hCV0 (norm_nonneg _), fun τ hτ r hr F => ?_⟩
  have hV := HRS.MC.Sec7.S7PIS1.s7_PIS_V_eval_proof R m hm T hT r τ hr.1 hr.2 hτ.2 F φ hφ
  rw [← hV]
  have h1 : |NegSobolev.eval (Vprop R.D R.ρ m τ r F) φ| ≤ ‖ℓ‖ * ‖Vprop R.D R.ρ m τ r F‖ := by
    have := ℓ.le_opNorm (Vprop R.D R.ρ m τ r F)
    rwa [Real.norm_eq_abs] at this
  calc _ ≤ ‖ℓ‖ * ‖Vprop R.D R.ρ m τ r F‖ := h1
    _ ≤ ‖ℓ‖ * (CV * ‖F‖) := mul_le_mul_of_nonneg_left (hCV τ hτ r hr F) (norm_nonneg _)
    _ = _ := by ring

/-- a.e. strong measurability of `a ↦ eval (B a) (U^{rr a,τ} φ)` -/
theorem S7PIF4_eval_prop_aesm (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {τ : ℝ} (hτ : τ ∈ Set.Ioc 0 T)
    {α : Type*} [MeasurableSpace α] {ν : Measure α} {rr : α → ℝ} {B : α → NegSobolev d m}
    (hr : Measurable rr) (hB : AEStronglyMeasurable B ν) (hrτ : ∀ᵐ a ∂ν, rr a ∈ Set.Icc (0 : ℝ) τ) :
    AEStronglyMeasurable (fun a => NegSobolev.eval (B a) (propagator R.D R.ρ (rr a) τ φ)) ν := by
  obtain ⟨CV, hCV0, hCV, hjc⟩ := S7PIF4_core R m hm T hT
  have hws : A33WS m φ := a33_ws_smooth m hφ
  have hV := S7PIF4_V_aesm_gen (D := R.D) (ρ := R.ρ) hτ.1.le (hjc τ hτ) hr hB hrτ
  have h2 := (S7PIF4_evalCLM m hws).continuous.comp_aestronglyMeasurable hV
  refine h2.congr ?_
  filter_upwards [hrτ] with a ha
  show S7PIF4_evalCLM m hws (Vprop R.D R.ρ m τ (rr a) (B a)) = _
  rw [S7PIF4_evalCLM_apply]
  exact HRS.MC.Sec7.S7PIS1.s7_PIS_V_eval_proof R m hm T hT (rr a) τ ha.1 ha.2 hτ.2 (B a) φ hφ

end HRS.MC.Sec7.S7PIF4

end
