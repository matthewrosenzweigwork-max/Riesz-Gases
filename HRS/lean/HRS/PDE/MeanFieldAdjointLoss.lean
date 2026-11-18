import HRS.PDE.MeanFieldDefs
import HRS.PDE.MeanFieldProductB
import HRS.PDE.MeanFieldAprioriParaproduct
import HRS.PDE.ClassicalPart
import HRS.PDE.EnergySymbol
import HRS.PDE.GalerkinLimit

/-!
# Loss and perturbation bounds for the forward generator (package MF-01, packet P11c)

See `HRS/PDE/MeanFieldAdjointPlan.md`, packet P11c.  Coefficient-level (Sobolev `H^m`) bounds:

* `exists_forwardGen_loss`: `𝓛_ρ - νΔ` loses `a = aExp d s` derivatives;
* `exists_forwardGen_diff`: `‖(𝓛_{ρ₁} - 𝓛_{ρ₂})F‖_{H^{i-a}} ≤ C ‖ρ₁ - ρ₂‖_{H^r} ‖F‖_{H^i}`;
* `exists_centerCoeff_bound`: centering at the `μβ`-mean is bounded on `H^i`.

The common definitions `aExp`, `meanCoeff`, `centerCoeff` of the plan (§1, "Common definitions")
are repeated here verbatim, because this packet does not depend on P11a.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFAdjoint

variable {d : ℕ}

/-! ### Common definitions (repeated from the plan) -/

/-- The derivative gain `a = max(1, θ)`, `θ = s + 2 - d` (TeX: `max(1,θ) < a < 2`; here the
endpoint value, which suffices because the frozen coefficients are smooth). -/
def aExp (d : ℕ) (s : ℝ) : ℝ := max 1 (thetaOrder d s)

theorem aExp_spec (s : ℝ) (hsd : s < d) :
    1 ≤ aExp d s ∧ aExp d s < 2 ∧ thetaOrder d s ≤ aExp d s := by
  refine ⟨le_max_left _ _, ?_, le_max_right _ _⟩
  refine max_lt (by norm_num) ?_
  unfold thetaOrder
  linarith

/-- The `μβ`-mean of `toFun c` in coefficients: `∑_k ρ̂β(-k) c(k)`. -/
def meanCoeff (ρβ : Torus d → ℝ) (c : Coeff d) : ℝ := (hsInner 0 (coeffOf ρβ) c).re

/-- Centering at the coefficient level. -/
def centerCoeff (ρβ : Torus d → ℝ) (c : Coeff d) : Coeff d :=
  c - (meanCoeff ρβ c : ℂ) • deltaCoeff 0

/-! ### Generic Sobolev tools -/

theorem hsNormSq_eq_tsum_sq' (a : ℝ) (x : Coeff d) :
    hsNormSq a x = ∑' k, (sobWeight (a / 2) k * ‖x k‖) ^ 2 := by
  unfold hsNormSq
  exact tsum_congr fun k => by rw [mul_pow, MFProduct.sobWeight_half_sq]

theorem summable_sq_of_memHs' {a : ℝ} {x : Coeff d} (hx : MemHs a x) :
    Summable fun k => (sobWeight (a / 2) k * ‖x k‖) ^ 2 :=
  hx.congr fun k => by rw [mul_pow, MFProduct.sobWeight_half_sq]

theorem hsNorm_nonneg' (m : ℝ) (c : Coeff d) : 0 ≤ hsNorm m c := Real.sqrt_nonneg _

/-- Multiplier bound: if `‖e k‖ ≤ C ⟨k⟩^γ ‖c k‖` then `‖e‖_{H^{m-γ}} ≤ C ‖c‖_{H^m}`. -/
theorem hs_mult {m γ C : ℝ} (hC : 0 ≤ C) {c e : Coeff d} (hc : MemHs m c)
    (h : ∀ k, ‖e k‖ ≤ C * Lattice.jp k ^ γ * ‖c k‖) :
    MemHs (m - γ) e ∧ hsNorm (m - γ) e ≤ C * hsNorm m c := by
  have hpt : ∀ k, sobWeight (m - γ) k * ‖e k‖ ^ 2 ≤ C ^ 2 * (sobWeight m k * ‖c k‖ ^ 2) := by
    intro k
    have hw : sobWeight m k = sobWeight (m - γ) k * sobWeight γ k := by
      rw [← sobWeight_add]; congr 1; ring
    have hg : sobWeight γ k = (Lattice.jp k ^ γ) ^ 2 := by
      rw [sobWeight_eq_jp, Torus.jp_rpow_sq]
    have hw0 : 0 ≤ sobWeight (m - γ) k := MFProduct.sobWeight_nonneg _ k
    have h1 : ‖e k‖ ^ 2 ≤ (C * Lattice.jp k ^ γ * ‖c k‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (h k) 2
    calc sobWeight (m - γ) k * ‖e k‖ ^ 2
        ≤ sobWeight (m - γ) k * (C * Lattice.jp k ^ γ * ‖c k‖) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 hw0
      _ = C ^ 2 * (sobWeight m k * ‖c k‖ ^ 2) := by rw [hw, hg]; ring
  have hsum : MemHs (m - γ) e :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (sq_nonneg _)) hpt (hc.mul_left _)
  refine ⟨hsum, ?_⟩
  have hle : hsNormSq (m - γ) e ≤ C ^ 2 * hsNormSq m c := by
    unfold hsNormSq
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hpt hsum (hc.mul_left _)
  unfold hsNorm
  calc Real.sqrt (hsNormSq (m - γ) e) ≤ Real.sqrt (C ^ 2 * hsNormSq m c) :=
        Real.sqrt_le_sqrt hle
    _ = C * Real.sqrt (hsNormSq m c) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC]

/-- Triangle inequality in `H^a`. -/
theorem hs_add_le (a : ℝ) {x y : Coeff d} (hx : MemHs a x) (hy : MemHs a y) :
    MemHs a (fun k => x k + y k) ∧
      hsNorm a (fun k => x k + y k) ≤ hsNorm a x + hsNorm a y := by
  have hxy : MemHs a (fun k => x k + y k) := (ProdAux.hsNormSq_add_le a hx hy).1
  refine ⟨hxy, ?_⟩
  set p : Lattice d → ℝ := fun k => sobWeight (a / 2) k * ‖x k‖ with hp
  set q : Lattice d → ℝ := fun k => sobWeight (a / 2) k * ‖y k‖ with hq
  have hp0 : ∀ k, 0 ≤ p k := fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (norm_nonneg _)
  have hq0 : ∀ k, 0 ≤ q k := fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (norm_nonneg _)
  have hp2 : Summable fun k => p k ^ 2 := summable_sq_of_memHs' hx
  have hq2 : Summable fun k => q k ^ 2 := summable_sq_of_memHs' hy
  obtain ⟨hpq, hcs⟩ := Torus.cs_tsum p q hp0 hq0 hp2 hq2
  have hle : ∀ k, (sobWeight (a / 2) k * ‖x k + y k‖) ^ 2 ≤ (p k + q k) ^ 2 := by
    intro k
    have h1 : ‖x k + y k‖ ≤ ‖x k‖ + ‖y k‖ := norm_add_le _ _
    have h2 := MFProduct.sobWeight_nonneg (d := d) (a / 2) k
    have : sobWeight (a / 2) k * ‖x k + y k‖ ≤ p k + q k := by
      simp only [hp, hq]; nlinarith
    exact pow_le_pow_left₀ (mul_nonneg h2 (norm_nonneg _)) this 2
  have hsum2 : Summable fun k => (p k + q k) ^ 2 :=
    (hp2.add hq2).add (hpq.mul_left 2) |>.congr fun k => by ring
  have hmain : hsNormSq a (fun k => x k + y k) ≤ (hsNorm a x + hsNorm a y) ^ 2 := by
    rw [hsNormSq_eq_tsum_sq']
    have hS : Summable fun k => (sobWeight (a / 2) k * ‖x k + y k‖) ^ 2 :=
      summable_sq_of_memHs' hxy
    calc ∑' k, (sobWeight (a / 2) k * ‖x k + y k‖) ^ 2 ≤ ∑' k, (p k + q k) ^ 2 :=
          hS.tsum_le_tsum hle hsum2
      _ = ∑' k, p k ^ 2 + 2 * ∑' k, p k * q k + ∑' k, q k ^ 2 := by
          have e : ∀ k, (p k + q k) ^ 2 = (p k ^ 2 + q k ^ 2) + 2 * (p k * q k) :=
            fun k => by ring
          simp_rw [e]
          rw [(hp2.add hq2).tsum_add (hpq.mul_left 2), hp2.tsum_add hq2, tsum_mul_left]
          ring
      _ ≤ (hsNorm a x + hsNorm a y) ^ 2 := by
          have hA : hsNorm a x = Real.sqrt (∑' k, p k ^ 2) := by
            unfold hsNorm; rw [hsNormSq_eq_tsum_sq']
          have hB : hsNorm a y = Real.sqrt (∑' k, q k ^ 2) := by
            unfold hsNorm; rw [hsNormSq_eq_tsum_sq']
          have sA : Real.sqrt (∑' k, p k ^ 2) ^ 2 = ∑' k, p k ^ 2 :=
            Real.sq_sqrt (tsum_nonneg fun k => sq_nonneg (p k))
          have sB : Real.sqrt (∑' k, q k ^ 2) ^ 2 = ∑' k, q k ^ 2 :=
            Real.sq_sqrt (tsum_nonneg fun k => sq_nonneg (q k))
          rw [hA, hB]
          nlinarith [hcs]
  unfold hsNorm
  calc Real.sqrt (hsNormSq a fun k => x k + y k) ≤ Real.sqrt ((hsNorm a x + hsNorm a y) ^ 2) :=
        Real.sqrt_le_sqrt hmain
    _ = hsNorm a x + hsNorm a y :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Finite sums in `H^a`. -/
theorem hs_sum_le {ι : Type*} (a : ℝ) (S : Finset ι) (x : ι → Coeff d)
    (hx : ∀ j ∈ S, MemHs a (x j)) :
    MemHs a (fun k => ∑ j ∈ S, x j k) ∧
      hsNorm a (fun k => ∑ j ∈ S, x j k) ≤ ∑ j ∈ S, hsNorm a (x j) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨?_, ?_⟩
    · unfold MemHs; simp
    · unfold hsNorm hsNormSq; simp
  | insert j S hj ih =>
    have ih' := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    have hxj := hx j (Finset.mem_insert_self _ _)
    simp only [Finset.sum_insert hj]
    obtain ⟨h1, h2⟩ := hs_add_le a hxj ih'.1
    exact ⟨h1, h2.trans (by linarith [ih'.2])⟩


/-- Lowering the index: `‖c‖_{H^{m-γ}} ≤ ‖c‖_{H^m}` for `γ ≥ 0`. -/
theorem hs_lower {m γ : ℝ} (hγ : 0 ≤ γ) {c : Coeff d} (hc : MemHs m c) :
    MemHs (m - γ) c ∧ hsNorm (m - γ) c ≤ hsNorm m c := by
  have := hs_mult (m := m) (γ := γ) (C := 1) zero_le_one hc (e := c) (fun k => by
    have h1 : (1 : ℝ) ≤ Lattice.jp k ^ γ := Real.one_le_rpow (Torus.jp_ge_one k) hγ
    have h2 := norm_nonneg (c k)
    nlinarith)
  simpa using this

/-- Negation in `H^m`. -/
theorem hs_neg {m : ℝ} {c : Coeff d} (hc : MemHs m c) :
    MemHs m (fun k => -c k) ∧ hsNorm m (fun k => -c k) ≤ hsNorm m c := by
  have := hs_mult (m := m) (γ := 0) (C := 1) zero_le_one hc (e := fun k => -c k) (fun k => by
    simp)
  simpa using this

theorem hs_zero_of_nonneg {m : ℝ} (hm : 0 ≤ m) {c : Coeff d} (hc : MemHs m c) : MemHs 0 c := by
  have := (hs_lower hm hc).1
  simpa using this

/-- `∂_j` loses one derivative. -/
theorem hs_deriv {i : ℝ} {F : Coeff d} (hF : MemHs i F) (j : Fin d) :
    MemHs (i - 1) (derivCoeff j F) ∧ hsNorm (i - 1) (derivCoeff j F) ≤ hsNorm i F := by
  have := hs_mult (m := i) (γ := 1) (C := 1) zero_le_one hF (e := derivCoeff j F) (fun k => by
    rw [Real.rpow_one, one_mul]; exact ClassicalPart.norm_derivCoeff_le j F k)
  simpa using this

theorem rad_le_jp (k : Lattice d) : rad k ≤ Lattice.jp k := by
  unfold Lattice.jp
  exact Real.le_sqrt_of_sq_le (rad_sq_le k)

/-- The symbol of `∇g ⋆` is bounded by `⟨k⟩^γ` for every `γ ≥ a - 1` (`a = aExp d s`). -/
theorem norm_gradRieszCoeff_le_jp {s : ℝ} (hsd : s < d) (i : Fin d) (c : Coeff d) (k : Lattice d)
    {γ : ℝ} (hγ : aExp d s - 1 ≤ γ) :
    ‖gradRieszCoeff d s i c k‖ ≤ |rieszConst d s| * Lattice.jp k ^ γ * ‖c k‖ := by
  have ha := (aExp_spec s hsd).1
  have hjp1 := Torus.jp_ge_one k
  have hγ0 : 0 ≤ γ := by linarith
  have hone : (1 : ℝ) ≤ Lattice.jp k ^ γ := Real.one_le_rpow hjp1 hγ0
  by_cases hk : k = 0
  · subst hk
    simp only [gradRieszCoeff, derivCoeff]
    simp
    positivity
  · have hθ : s - (d : ℝ) + 1 ≤ γ := by
      have := (aExp_spec s hsd).2.2
      unfold thetaOrder at this
      linarith
    have heq : gradRieszCoeff d s i c k =
        ((2 * Real.pi * Complex.I * (k i : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) * c k := by
      simp only [gradRieszCoeff, derivCoeff, rieszMult]; ring
    rw [heq, norm_mul]
    have hsym := norm_symS_le s i k hk
    have hrad : rad k ^ (s - (d : ℝ) + 1) ≤ Lattice.jp k ^ γ := by
      by_cases he : 0 ≤ s - (d : ℝ) + 1
      · calc rad k ^ (s - (d : ℝ) + 1) ≤ Lattice.jp k ^ (s - (d : ℝ) + 1) :=
              Real.rpow_le_rpow (rad_nonneg k) (rad_le_jp k) he
          _ ≤ Lattice.jp k ^ γ := Real.rpow_le_rpow_of_exponent_le hjp1 hθ
      · push Not at he
        exact (Real.rpow_le_one_of_one_le_of_nonpos (one_le_rad k hk) he.le).trans hone
    calc _ ≤ (|rieszConst d s| * Lattice.jp k ^ γ) * ‖c k‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact hsym.trans (mul_le_mul_of_nonneg_left hrad (abs_nonneg _))
      _ = _ := by ring

theorem hs_gradRiesz {s : ℝ} (hsd : s < d) {γ : ℝ} (hγ : aExp d s - 1 ≤ γ) {m : ℝ} {c : Coeff d}
    (hc : MemHs m c) (i : Fin d) :
    MemHs (m - γ) (gradRieszCoeff d s i c) ∧
      hsNorm (m - γ) (gradRieszCoeff d s i c) ≤ |rieszConst d s| * hsNorm m c :=
  hs_mult (abs_nonneg _) hc (fun k => norm_gradRieszCoeff_le_jp hsd i c k hγ)

/-! ### The transport and nonlocal sums -/

/-- The transport term `∑_j b_j ∂_j F`. -/
def transSum (b : Fin d → Coeff d) (F : Coeff d) : Coeff d :=
  fun k => ∑ j, mulCoeff (b j) (derivCoeff j F) k

/-- The nonlocal sum `∑_j ∂_j-component of ∇g ⋆ (w ∂_j F)`: `∑_j (∇g ⋆)_j (w ∂_jF)`. -/
def nlSum (s : ℝ) (w F : Coeff d) : Coeff d :=
  fun k => ∑ j, gradRieszCoeff d s j (mulCoeff w (derivCoeff j F)) k

theorem transSum_bound (i r : ℝ) (hi : 1 ≤ i) (hr : (d : ℝ) / 2 + i < r) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ (b : Fin d → Coeff d) (F : Coeff d), (∀ j, MemHs (r - 1) (b j)) →
      MemHs i F → MemHs (i - 1) (transSum b F) ∧
        hsNorm (i - 1) (transSum b F) ≤ Cp * (∑ j, hsNorm (r - 1) (b j)) * hsNorm i F := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  obtain ⟨Cp, hCp, hP⟩ := MFProduct.exists_product_bound (d := d) (r - 1) (i - 1) (i - 1)
    (by linarith) (by linarith) le_rfl (by linarith)
  refine ⟨Cp, hCp, fun b F hb hF => ?_⟩
  have hj : ∀ j ∈ Finset.univ, MemHs (i - 1) (mulCoeff (b j) (derivCoeff j F)) :=
    fun j _ => (hP (b j) (derivCoeff j F) (hb j) (hs_deriv hF j).1).1
  obtain ⟨h1, h2⟩ := hs_sum_le (i - 1) Finset.univ (fun j => mulCoeff (b j) (derivCoeff j F)) hj
  refine ⟨h1, h2.trans ?_⟩
  calc ∑ j, hsNorm (i - 1) (mulCoeff (b j) (derivCoeff j F))
      ≤ ∑ j, Cp * hsNorm (r - 1) (b j) * hsNorm i F := by
        refine Finset.sum_le_sum fun j _ => ?_
        have := (hP (b j) (derivCoeff j F) (hb j) (hs_deriv hF j).1).2
        refine this.trans ?_
        refine mul_le_mul_of_nonneg_left (hs_deriv hF j).2 ?_
        exact mul_nonneg hCp (hsNorm_nonneg' _ _)
    _ = Cp * (∑ j, hsNorm (r - 1) (b j)) * hsNorm i F := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem nlSum_bound {s : ℝ} (hsd : s < d) (i r : ℝ) (hi : 1 ≤ i) (hr : (d : ℝ) / 2 + i < r) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ (w F : Coeff d), MemHs r w → MemHs i F →
      MemHs (i - aExp d s) (nlSum s w F) ∧
        hsNorm (i - aExp d s) (nlSum s w F) ≤ Cn * hsNorm r w * hsNorm i F := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  obtain ⟨Cp, hCp, hP⟩ := MFProduct.exists_product_bound (d := d) r (i - 1) (i - 1)
    (by linarith) (by linarith) le_rfl (by linarith)
  set A : ℝ := |rieszConst d s| with hA
  refine ⟨d * (A * Cp), by positivity, fun w F hw hF => ?_⟩
  have hidx : i - 1 - (aExp d s - 1) = i - aExp d s := by ring
  have hj : ∀ j ∈ Finset.univ, MemHs (i - aExp d s)
      (gradRieszCoeff d s j (mulCoeff w (derivCoeff j F))) := fun j _ => by
    have := (hs_gradRiesz hsd (le_refl (aExp d s - 1)) (hP w (derivCoeff j F) hw
      (hs_deriv hF j).1).1 j).1
    rwa [hidx] at this
  obtain ⟨h1, h2⟩ := hs_sum_le (i - aExp d s) Finset.univ
    (fun j => gradRieszCoeff d s j (mulCoeff w (derivCoeff j F))) hj
  refine ⟨h1, h2.trans ?_⟩
  have hterm : ∀ j : Fin d, hsNorm (i - aExp d s)
      (gradRieszCoeff d s j (mulCoeff w (derivCoeff j F))) ≤ A * (Cp * hsNorm r w * hsNorm i F) := by
    intro j
    have hm := (hP w (derivCoeff j F) hw (hs_deriv hF j).1)
    have := (hs_gradRiesz hsd (le_refl (aExp d s - 1)) hm.1 j).2
    rw [hidx] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
    refine hm.2.trans ?_
    exact mul_le_mul_of_nonneg_left (hs_deriv hF j).2 (mul_nonneg hCp (hsNorm_nonneg' _ _))
  calc ∑ j, hsNorm (i - aExp d s) (gradRieszCoeff d s j (mulCoeff w (derivCoeff j F)))
      ≤ ∑ _j : Fin d, A * (Cp * hsNorm r w * hsNorm i F) := Finset.sum_le_sum fun j _ => hterm j
    _ = d * (A * Cp) * hsNorm r w * hsNorm i F := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring


/-! ### Decomposition of `forwardGen` for `M = -1` -/

theorem driftCoeff_eq (D : DynData d) (hM : D.M = -1) (ρ : Torus d → ℝ) (j : Fin d) :
    driftCoeff D ρ j = fun k =>
      (-(gradRieszCoeff d D.s j (coeffOf ρ) k)) + (-(derivCoeff j (coeffOf D.V) k)) := by
  funext k
  simp only [driftCoeff, hM, Matrix.neg_apply, Matrix.one_apply]
  simp [apply_ite Complex.ofReal, ite_mul, Finset.sum_ite_eq]
  ring

theorem nonlocalCoeff_eq (D : DynData d) (hM : D.M = -1) (ρ : Torus d → ℝ) (F : Coeff d) :
    nonlocalCoeff D ρ F = fun k => -(nlSum D.s (coeffOf ρ) F k) := by
  funext k
  simp only [nonlocalCoeff, nlSum, hM, Matrix.neg_apply, Matrix.one_apply]
  rw [Finset.sum_comm]
  simp [apply_ite Complex.ofReal, ite_mul, Finset.sum_ite_eq]

theorem forwardGen_sub_lap (D : DynData d) (hM : D.M = -1) (ρ : Torus d → ℝ) (F : Coeff d) :
    (forwardGen D ρ F - fun k => ((D.invβ : ℝ) : ℂ) * laplaceCoeff F k) = fun k =>
      transSum (fun j k => (-(gradRieszCoeff d D.s j (coeffOf ρ) k)) +
        (-(derivCoeff j (coeffOf D.V) k))) F k + nlSum D.s (coeffOf ρ) F k := by
  funext k
  have h1 : transportCoeff D ρ F k = transSum (fun j k => (-(gradRieszCoeff d D.s j (coeffOf ρ) k)) +
        (-(derivCoeff j (coeffOf D.V) k))) F k := by
    simp only [transportCoeff, transSum, driftCoeff_eq D hM]
  have h2 := congrFun (nonlocalCoeff_eq D hM ρ F) k
  simp only [Pi.sub_apply, forwardGen, h1, h2]
  ring


/-! ### Bounds for the drift coefficients and linearity in the density -/

theorem drift_bound0 {s : ℝ} (hsd : s < d) {r : ℝ} {w : Coeff d} (hw : MemHs r w) (j : Fin d) :
    MemHs (r - 1) (fun k => -(gradRieszCoeff d s j w k)) ∧
      hsNorm (r - 1) (fun k => -(gradRieszCoeff d s j w k)) ≤ |rieszConst d s| * hsNorm r w :=
  hs_mult (m := r) (γ := 1) (C := |rieszConst d s|) (abs_nonneg _) hw
    (e := fun k => -(gradRieszCoeff d s j w k)) (fun k => by
      rw [norm_neg]
      exact norm_gradRieszCoeff_le_jp hsd j w k (by have := (aExp_spec s hsd).2.1; linarith))

theorem drift_bound {s : ℝ} (hsd : s < d) {r : ℝ} {w v : Coeff d} (hw : MemHs r w) (hv : MemHs r v)
    (j : Fin d) :
    MemHs (r - 1) (fun k => (-(gradRieszCoeff d s j w k)) + (-(derivCoeff j v k))) ∧
      hsNorm (r - 1) (fun k => (-(gradRieszCoeff d s j w k)) + (-(derivCoeff j v k))) ≤
        |rieszConst d s| * hsNorm r w + hsNorm r v := by
  obtain ⟨h1, h1'⟩ := drift_bound0 hsd hw j
  have h2 := hs_mult (m := r) (γ := 1) (C := 1) zero_le_one hv
    (e := fun k => -(derivCoeff j v k)) (fun k => by
      rw [norm_neg, Real.rpow_one, one_mul]; exact ClassicalPart.norm_derivCoeff_le j v k)
  obtain ⟨h3, h3'⟩ := hs_add_le (r - 1) h1 h2.1
  refine ⟨h3, h3'.trans ?_⟩
  have := h2.2
  linarith

theorem mulCoeff_sub_left {a₁ a₂ c : Coeff d} (h1 : MemHs 0 a₁) (h2 : MemHs 0 a₂) (hc : MemHs 0 c)
    (k : Lattice d) :
    mulCoeff (fun k => a₁ k - a₂ k) c k = mulCoeff a₁ c k - mulCoeff a₂ c k := by
  unfold mulCoeff
  rw [← Summable.tsum_sub (summable_mulCoeff a₁ c h1 hc k) (summable_mulCoeff a₂ c h2 hc k)]
  exact tsum_congr fun j => by ring

theorem transSum_sub {b₁ b₂ bd : Fin d → Coeff d} {F : Coeff d}
    (h1 : ∀ j, MemHs 0 (b₁ j)) (h2 : ∀ j, MemHs 0 (b₂ j)) (hG : ∀ j, MemHs 0 (derivCoeff j F))
    (hbd : ∀ j k, bd j k = b₁ j k - b₂ j k) (k : Lattice d) :
    transSum bd F k = transSum b₁ F k - transSum b₂ F k := by
  unfold transSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : bd j = fun k => b₁ j k - b₂ j k := funext (hbd j)
  rw [this]
  exact mulCoeff_sub_left (h1 j) (h2 j) (hG j) k

theorem nlSum_sub {s : ℝ} {w₁ w₂ F : Coeff d} (h1 : MemHs 0 w₁) (h2 : MemHs 0 w₂)
    (hG : ∀ j, MemHs 0 (derivCoeff j F)) (k : Lattice d) :
    nlSum s (fun k => w₁ k - w₂ k) F k = nlSum s w₁ F k - nlSum s w₂ F k := by
  unfold nlSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : mulCoeff (fun k => w₁ k - w₂ k) (derivCoeff j F) =
      fun k => mulCoeff w₁ (derivCoeff j F) k - mulCoeff w₂ (derivCoeff j F) k :=
    funext (mulCoeff_sub_left h1 h2 (hG j))
  rw [this]
  simp only [gradRieszCoeff, derivCoeff, rieszMult]
  ring

theorem norm_mulCoeff_sub_le {a₁ a₂ ad c : Coeff d} (hbd : ∀ k, ad k = a₁ k - a₂ k)
    (had : MemHs 0 ad) (hc : MemHs 0 c) (k : Lattice d) :
    ‖mulCoeff a₁ c k - mulCoeff a₂ c k‖ ≤ ‖mulCoeff ad c k‖ := by
  have hsd' := summable_mulCoeff ad c had hc k
  have hrel : ∀ l, a₂ (k - l) * c l = a₁ (k - l) * c l - ad (k - l) * c l := fun l => by
    rw [hbd]; ring
  by_cases h : Summable fun l => a₁ (k - l) * c l
  · have h2 : Summable fun l => a₂ (k - l) * c l :=
      (h.sub hsd').congr fun l => (hrel l).symm
    apply le_of_eq
    congr 1
    unfold mulCoeff
    rw [← Summable.tsum_sub h h2]
    refine tsum_congr fun l => ?_
    rw [hrel]; ring
  · have h2 : ¬ Summable fun l => a₂ (k - l) * c l := fun h2 => by
      apply h
      refine (h2.add hsd').congr fun l => ?_
      rw [hrel]; ring
    unfold mulCoeff
    rw [tsum_eq_zero_of_not_summable h, tsum_eq_zero_of_not_summable h2]
    simp

/-! ### The main bounds -/

set_option linter.unusedVariables false in
/-- The lower-order part `𝓛 - νΔ` loses `a = aExp d s` derivatives
(`eq:periodic-B-regularity`, Sobolev form). -/
theorem exists_forwardGen_loss (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (i r : ℝ)
    (hi : 1 ≤ i) (hr : (d : ℝ) / 2 + i < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : DynData d), D.s = s → D.M = -1 →
      ∀ ρ : Torus d → ℝ, Continuous ρ → MemHs r (coeffOf ρ) → MemHs r (coeffOf D.V) →
      ∀ F : Coeff d, MemHs i F →
        MemHs (i - aExp d s)
          (forwardGen D ρ F - fun k => ((D.invβ : ℝ) : ℂ) * laplaceCoeff F k) ∧
        hsNorm (i - aExp d s)
            (forwardGen D ρ F - fun k => ((D.invβ : ℝ) : ℂ) * laplaceCoeff F k) ≤
          C * (hsNorm r (coeffOf ρ) + hsNorm r (coeffOf D.V)) * hsNorm i F := by
  obtain ⟨Cp, hCp, hT⟩ := transSum_bound (d := d) i r hi hr
  obtain ⟨Cn, hCn, hN⟩ := nlSum_bound (d := d) hsd i r hi hr
  set A : ℝ := |rieszConst d s| with hA
  have hA0 : 0 ≤ A := abs_nonneg _
  refine ⟨Cp * (d * (A + 1)) + Cn, by positivity, ?_⟩
  intro D hs hM ρ _ hρ hV F hF
  have hdec := forwardGen_sub_lap D hM ρ F
  rw [hs] at hdec
  rw [hdec]
  have hb := fun j => drift_bound hsd hρ hV j
  obtain ⟨hT1, hT2⟩ := hT _ F (fun j => (hb j).1) hF
  have hidx : i - 1 - (aExp d s - 1) = i - aExp d s := by ring
  have ha1 := (aExp_spec s hsd).1
  obtain ⟨hT3, hT4⟩ := hs_lower (γ := aExp d s - 1) (by linarith) hT1
  rw [hidx] at hT3 hT4
  obtain ⟨hN1, hN2⟩ := hN (coeffOf ρ) F hρ hF
  obtain ⟨hS1, hS2⟩ := hs_add_le (i - aExp d s) hT3 hN1
  refine ⟨hS1, hS2.trans ?_⟩
  set P := hsNorm r (coeffOf ρ) with hP
  set Q := hsNorm r (coeffOf D.V) with hQ
  set N := hsNorm i F with hNdef
  have hP0 : 0 ≤ P := hsNorm_nonneg' _ _
  have hQ0 : 0 ≤ Q := hsNorm_nonneg' _ _
  have hN0 : 0 ≤ N := hsNorm_nonneg' _ _
  have hsum : ∑ j : Fin d, hsNorm (r - 1) (fun k => (-(gradRieszCoeff d s j (coeffOf ρ) k)) +
      (-(derivCoeff j (coeffOf D.V) k))) ≤ d * (A * P + Q) := by
    calc _ ≤ ∑ _j : Fin d, (A * P + Q) := Finset.sum_le_sum fun j _ => (hb j).2
      _ = d * (A * P + Q) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 : hsNorm (i - aExp d s) (transSum (fun j k => (-(gradRieszCoeff d s j (coeffOf ρ) k)) +
      (-(derivCoeff j (coeffOf D.V) k))) F) ≤ Cp * (d * (A * P + Q)) * N := by
    refine hT4.trans ?_
    refine (hT2.trans ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hCp) hN0
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hkey : (Cp * (d * (A + 1)) + Cn) * (P + Q) * N -
      (Cp * (d * (A * P + Q)) * N + Cn * P * N) = N * (Cp * d * (A * Q + P) + Cn * Q) := by
    ring
  have hpos : 0 ≤ N * (Cp * d * (A * Q + P) + Cn * Q) := by positivity
  linarith

set_option linter.unusedVariables false in
/-- `C:eq:perturbation`: `‖(𝓛_{ρ₁} - 𝓛_{ρ₂})F‖_{H^{i-a}} ≤ C ‖ρ₁ - ρ₂‖_{H^r} ‖F‖_{H^i}`. -/
theorem exists_forwardGen_diff (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (i r : ℝ)
    (hi : 1 ≤ i) (hr : (d : ℝ) / 2 + i < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : DynData d), D.s = s → D.M = -1 →
      ∀ ρ₁ ρ₂ : Torus d → ℝ, Continuous ρ₁ → Continuous ρ₂ → MemHs r (coeffOf ρ₁) →
      MemHs r (coeffOf ρ₂) → ∀ F : Coeff d, MemHs i F →
        MemHs (i - aExp d s) (forwardGen D ρ₁ F - forwardGen D ρ₂ F) ∧
        hsNorm (i - aExp d s) (forwardGen D ρ₁ F - forwardGen D ρ₂ F) ≤
          C * hsNorm r (coeffOf ρ₁ - coeffOf ρ₂) * hsNorm i F := by
  obtain ⟨Cn, hCn, hN⟩ := nlSum_bound (d := d) hsd i r hi hr
  have hd0' : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  obtain ⟨Cq, hCq, hP⟩ := MFProduct.exists_product_bound (d := d) (r - 1) (i - 1) (i - 1)
    (by linarith) (by linarith) le_rfl (by linarith)
  set A : ℝ := |rieszConst d s| with hA
  have hA0 : 0 ≤ A := abs_nonneg _
  refine ⟨Cq * (d * A) + Cn, by positivity, ?_⟩
  intro D hs hM ρ₁ ρ₂ _ _ h1 h2 F hF
  have hr1 : 0 ≤ r - 1 := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  set w : Coeff d := fun k => coeffOf ρ₁ k - coeffOf ρ₂ k with hwdef
  have hwmem : MemHs r w ∧ hsNorm r w ≤ hsNorm r (coeffOf ρ₁) + hsNorm r (coeffOf ρ₂) := by
    obtain ⟨hn, hn'⟩ := hs_neg h2
    obtain ⟨ha, ha'⟩ := hs_add_le r h1 hn
    refine ⟨ha, ?_⟩
    exact ha'.trans (by linarith)
  have hwe : hsNorm r (coeffOf ρ₁ - coeffOf ρ₂) = hsNorm r w := rfl
  rw [hwe]
  -- the decomposition
  have hd1 := forwardGen_sub_lap D hM ρ₁ F
  have hd2 := forwardGen_sub_lap D hM ρ₂ F
  rw [hs] at hd1 hd2
  have hG0 : ∀ j, MemHs 0 (derivCoeff j F) := fun j =>
    hs_zero_of_nonneg (by linarith) (hs_deriv hF j).1
  have h10 : MemHs 0 (coeffOf ρ₁) := hs_zero_of_nonneg (by linarith) h1
  have h20 : MemHs 0 (coeffOf ρ₂) := hs_zero_of_nonneg (by linarith) h2
  set bd : Fin d → Coeff d := fun j k => -(gradRieszCoeff d s j w k) with hbd
  set b₁ : Fin d → Coeff d := fun j k => (-(gradRieszCoeff d s j (coeffOf ρ₁) k)) +
    (-(derivCoeff j (coeffOf D.V) k)) with hb₁
  set b₂ : Fin d → Coeff d := fun j k => (-(gradRieszCoeff d s j (coeffOf ρ₂) k)) +
    (-(derivCoeff j (coeffOf D.V) k)) with hb₂
  have hbdeq : ∀ j k, bd j k = b₁ j k - b₂ j k := by
    intro j k
    simp only [hbd, hb₁, hb₂, hwdef, gradRieszCoeff, derivCoeff, rieszMult]
    ring
  have hbd0 : ∀ j, MemHs 0 (bd j) := fun j =>
    hs_zero_of_nonneg hr1 (drift_bound0 hsd hwmem.1 j).1
  -- per-term bound with junk values
  set u : Fin d → Coeff d := fun j k =>
    mulCoeff (b₁ j) (derivCoeff j F) k - mulCoeff (b₂ j) (derivCoeff j F) k with hu
  have hupt : ∀ j k, ‖u j k‖ ≤ ‖mulCoeff (bd j) (derivCoeff j F) k‖ := by
    intro j k
    simp only [hu]
    exact norm_mulCoeff_sub_le (hbdeq j) (hbd0 j) (hG0 j) k
  have hprod := fun j => hP (bd j) (derivCoeff j F) (drift_bound0 hsd hwmem.1 j).1 (hs_deriv hF j).1
  have huj : ∀ j, MemHs (i - 1) (u j) ∧ hsNorm (i - 1) (u j) ≤
      Cq * (|rieszConst d s| * hsNorm r w) * hsNorm i F := by
    intro j
    have h := hs_mult (m := i - 1) (γ := 0) (C := 1) zero_le_one (hprod j).1 (e := u j)
      (fun k => by rw [Real.rpow_zero]; simpa using hupt j k)
    refine ⟨by simpa using h.1, ?_⟩
    have h' : hsNorm (i - 1) (u j) ≤ hsNorm (i - 1) (mulCoeff (bd j) (derivCoeff j F)) := by
      simpa using h.2
    refine h'.trans ((hprod j).2.trans ?_)
    have hn := (drift_bound0 hsd hwmem.1 j).2
    have hdn := (hs_deriv hF j).2
    refine mul_le_mul (mul_le_mul_of_nonneg_left hn hCq) hdn (hsNorm_nonneg' _ _) ?_
    exact mul_nonneg hCq (mul_nonneg (abs_nonneg _) (hsNorm_nonneg' _ _))
  have hLHS : (forwardGen D ρ₁ F - forwardGen D ρ₂ F) = fun k =>
      (∑ j, u j k) + nlSum s w F k := by
    funext k
    have e1 := congrFun hd1 k
    have e2 := congrFun hd2 k
    simp only [Pi.sub_apply] at e1 e2 ⊢
    have e3 : nlSum s w F k = nlSum s (coeffOf ρ₁) F k - nlSum s (coeffOf ρ₂) F k :=
      nlSum_sub h10 h20 hG0 k
    have e4 : (∑ j, u j k) = transSum b₁ F k - transSum b₂ F k := by
      simp only [hu, transSum]
      exact Finset.sum_sub_distrib _ _
    linear_combination e1 - e2 - e3 - e4
  rw [hLHS]

  obtain ⟨hs1, hs2⟩ := hs_sum_le (i - 1) Finset.univ u (fun j _ => (huj j).1)
  have hidx : i - 1 - (aExp d s - 1) = i - aExp d s := by ring
  have ha1 := (aExp_spec s hsd).1
  obtain ⟨hs3, hs4⟩ := hs_lower (γ := aExp d s - 1) (by linarith) hs1
  rw [hidx] at hs3 hs4
  obtain ⟨hN1, hN2⟩ := hN w F hwmem.1 hF
  obtain ⟨hS1, hS2⟩ := hs_add_le (i - aExp d s) hs3 hN1
  refine ⟨hS1, hS2.trans ?_⟩
  set W := hsNorm r w with hW
  set N := hsNorm i F with hNdef
  have hW0 : 0 ≤ W := hsNorm_nonneg' _ _
  have hN0 : 0 ≤ N := hsNorm_nonneg' _ _
  have hsum : ∑ j, hsNorm (i - 1) (u j) ≤ d * (Cq * (A * W) * N) := by
    calc _ ≤ ∑ _j : Fin d, Cq * (A * W) * N := Finset.sum_le_sum fun j _ => (huj j).2
      _ = d * (Cq * (A * W) * N) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hkey : (Cq * (d * A) + Cn) * W * N = d * (Cq * (A * W) * N) + Cn * W * N := by ring
  linarith


/-! ### Centering -/

/-- Parseval for a bounded probability density: `‖ρ̂‖²_{H⁰} ≤ Λ₀`. -/
theorem memHs_zero_coeffOf_le {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hc : Continuous ρ)
    {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) : MemHs 0 (coeffOf ρ) ∧ hsNormSq 0 (coeffOf ρ) ≤ Λ := by
  have hcF : Continuous (fun x => (ρ x : ℂ)) := Complex.continuous_ofReal.comp hc
  have hF : MemLp (fun x => (ρ x : ℂ)) 2 volume :=
    hcF.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hP := hasSum_parseval _ _ hF hF
  have hterm : ∀ n : Lattice d, conj (Torus.funFourierCoeff (fun x => (ρ x : ℂ)) n) *
      Torus.funFourierCoeff (fun x => (ρ x : ℂ)) n = ((‖coeffOf ρ n‖ ^ 2 : ℝ) : ℂ) := by
    intro n
    have : Torus.funFourierCoeff (fun x => (ρ x : ℂ)) n = coeffOf ρ n := rfl
    rw [this, Complex.conj_mul']
    push_cast; ring
  have hint : ∀ t, conj ((ρ t : ℂ)) * (ρ t : ℂ) = ((ρ t * ρ t : ℝ) : ℂ) := by
    intro t; simp
  simp_rw [hterm, hint] at hP
  rw [integral_complex_ofReal] at hP
  have hP' : HasSum (fun n : Lattice d => ‖coeffOf ρ n‖ ^ 2) (∫ t, ρ t * ρ t) :=
    Complex.hasSum_ofReal.mp hP
  have hsum : MemHs 0 (coeffOf ρ) := by
    unfold MemHs; simp_rw [sobWeight_zero, one_mul]; exact hP'.summable
  refine ⟨hsum, ?_⟩
  unfold hsNormSq
  simp_rw [sobWeight_zero, one_mul]
  rw [hP'.tsum_eq]
  have hi1 : Integrable (fun t => ρ t * ρ t) := (hc.mul hc).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun t => Λ * ρ t) :=
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul Λ
  calc ∫ t, ρ t * ρ t ≤ ∫ t, Λ * ρ t :=
        integral_mono hi1 hi2 fun t => mul_le_mul_of_nonneg_right (hΛ t) (hρ.nonneg t)
    _ = Λ := by rw [integral_const_mul, hρ.integral_one, mul_one]

/-- `|meanCoeff ρβ c| ≤ ‖ρ̂β‖_{H⁰} ‖c‖_{H⁰}`. -/
theorem abs_meanCoeff_le (ρ : Torus d → ℝ) {c : Coeff d} (hρ : MemHs 0 (coeffOf ρ))
    (hc : MemHs 0 c) : |meanCoeff ρ c| ≤ hsNorm 0 (coeffOf ρ) * hsNorm 0 c := by
  have hρ2 : Summable fun k => (‖coeffOf ρ k‖) ^ 2 := (memHs_zero_iff _).mp hρ
  have hc2 : Summable fun k => (‖c k‖) ^ 2 := (memHs_zero_iff _).mp hc
  obtain ⟨hs, hle⟩ := Torus.cs_tsum (fun k => ‖coeffOf ρ k‖) (fun k => ‖c k‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hρ2 hc2
  have hnorm : ∀ k, ‖((sobWeight 0 k : ℝ) : ℂ) * (coeffOf ρ k * conj (c k))‖ =
      ‖coeffOf ρ k‖ * ‖c k‖ := by
    intro k
    rw [sobWeight_zero]; simp
  have hsN : Summable fun k => ‖((sobWeight 0 k : ℝ) : ℂ) * (coeffOf ρ k * conj (c k))‖ :=
    hs.congr fun k => (hnorm k).symm
  unfold meanCoeff hsInner
  calc |(∑' k, ((sobWeight 0 k : ℝ) : ℂ) * (coeffOf ρ k * conj (c k))).re|
      ≤ ‖∑' k, ((sobWeight 0 k : ℝ) : ℂ) * (coeffOf ρ k * conj (c k))‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ∑' k, ‖((sobWeight 0 k : ℝ) : ℂ) * (coeffOf ρ k * conj (c k))‖ :=
        norm_tsum_le_tsum_norm hsN
    _ = ∑' k, ‖coeffOf ρ k‖ * ‖c k‖ := tsum_congr hnorm
    _ ≤ Real.sqrt (∑' k, ‖coeffOf ρ k‖ ^ 2) * Real.sqrt (∑' k, ‖c k‖ ^ 2) := hle
    _ = hsNorm 0 (coeffOf ρ) * hsNorm 0 c := by
        unfold hsNorm hsNormSq
        simp_rw [sobWeight_zero, one_mul]

theorem memHs_deltaCoeff (m : ℝ) : MemHs m (deltaCoeff (0 : Lattice d)) := by
  unfold MemHs
  refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
  have : k ≠ 0 := by simpa using hk
  simp [deltaCoeff, this]

theorem hsNorm_deltaCoeff_zero (m : ℝ) : hsNorm m (deltaCoeff (0 : Lattice d)) = 1 := by
  rw [hsNorm_deltaCoeff]
  have : Lattice.enorm (0 : Lattice d) = 0 := by
    unfold Lattice.enorm Lattice.toEuc
    have : (WithLp.toLp 2 fun i : Fin d => (((0 : Lattice d) i : ℤ) : ℝ)) = (0 : Euc d) := by
      ext i; simp
    rw [this, norm_zero]
  rw [this]; simp

/-- Sobolev-type bound for `hsNorm` of a centered coefficient family (`Q` is bounded on `H^i`). -/
theorem exists_centerCoeff_bound (i : ℝ) (hi : 0 ≤ i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρβ : Torus d → ℝ), IsProbDensity ρβ → Continuous ρβ → ∀ Λ₀ : ℝ,
      (∀ x, ρβ x ≤ Λ₀) → ∀ c : Coeff d, MemHs i c →
        MemHs i (centerCoeff ρβ c) ∧ hsNorm i (centerCoeff ρβ c) ≤ C * (1 + Λ₀) * hsNorm i c := by
  refine ⟨2, by norm_num, fun ρβ hρ hc Λ₀ hΛ c hci => ?_⟩
  have hΛ0 : 0 ≤ Λ₀ := (hρ.nonneg 0).trans (hΛ 0)
  obtain ⟨hρ0, hρΛ⟩ := memHs_zero_coeffOf_le hρ hc hΛ
  have hc0 : MemHs 0 c := by
    have := (hs_lower hi hci).1
    simpa using this
  have hc0n : hsNorm 0 c ≤ hsNorm i c := by
    have := (hs_lower hi hci).2
    simpa using this
  have hm := abs_meanCoeff_le ρβ hρ0 hc0
  have hρn : hsNorm 0 (coeffOf ρβ) ≤ Real.sqrt Λ₀ := by
    unfold hsNorm
    exact Real.sqrt_le_sqrt hρΛ
  have hmabs : |meanCoeff ρβ c| ≤ Real.sqrt Λ₀ * hsNorm i c :=
    hm.trans (mul_le_mul hρn hc0n (hsNorm_nonneg' _ _) (Real.sqrt_nonneg _))
  set m : ℝ := meanCoeff ρβ c with hmdef
  have hy := hs_mult (m := i) (γ := 0) (C := |m|) (abs_nonneg _) (memHs_deltaCoeff (d := d) i)
    (e := fun k => -((m : ℂ) * deltaCoeff (0 : Lattice d) k)) (fun k => by
      rw [Real.rpow_zero, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]; simp)
  have hcen : centerCoeff ρβ c = fun k => c k + -((m : ℂ) * deltaCoeff (0 : Lattice d) k) := by
    funext k
    simp [centerCoeff, sub_eq_add_neg, hmdef]
  rw [hcen]
  obtain ⟨hA, hA'⟩ := hs_add_le i hci (by simpa using hy.1)
  refine ⟨hA, hA'.trans ?_⟩
  have hy2 : hsNorm i (fun k => -((m : ℂ) * deltaCoeff (0 : Lattice d) k)) ≤ |m| := by
    have := hy.2
    rw [hsNorm_deltaCoeff_zero] at this
    simpa using this
  have ht : Real.sqrt Λ₀ ≤ 1 + 2 * Λ₀ := by
    have h1 := Real.sq_sqrt hΛ0
    nlinarith [Real.sqrt_nonneg Λ₀, sq_nonneg (Real.sqrt Λ₀ - 1)]
  have hN0 := hsNorm_nonneg' i c
  nlinarith [mul_le_mul_of_nonneg_right ht hN0]

end HRS.PDE.MFAdjoint
