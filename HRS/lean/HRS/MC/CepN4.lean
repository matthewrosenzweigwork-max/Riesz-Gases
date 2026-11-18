import Mathlib
import HRS.MC.CepN4Aux4
import HRS.MC.CepK1
import HRS.MC.CepC0
import HRS.Stochastic.Particle

/-!
# Packet CEPN4: gap dynamics while the leading pair is isolated

`cep_N4_gap_dynamics_proof`: with `G = Y_{π 1} - Y_{π 0}` the integrated particle equation gives
`G_t - G_s = ∫_s^t (b_{π1} - b_{π0})(Y_u) du + √(2 invβ) (ΔW_{π1} - ΔW_{π0})`, and K1 turns
`b_{π1} - b_{π0}` into `(2a/N)/G + E(Y_u)` with `E` the explicit remainder of `CepN4Aux2`, bounded by `C` on
`r`-isolated configurations with gap in `(0, 1/4)`; `c = max (-C) (min C E)` (clamped, so `|c| ≤ C` everywhere),
and `c u` is `ℱ u`-measurable because `Y u` is and `π` is `ℱ 0`-measurable.
The vocabulary `cep_i0, cep_i1, cep_PairIsolated, cep_StrictlyOrdered` is duplicated from
`HRS/MC/CepaSpec.lean` (same bodies).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepN4

open HRS

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

def cep_i0 (hN : 2 ≤ N) : Fin N := ⟨0, by omega⟩

def cep_i1 (hN : 2 ≤ N) : Fin N := ⟨1, by omega⟩

def cep_PairIsolated (hN : 2 ≤ N) (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) (r : ℝ) : Prop :=
  ∀ k : Fin N, k ≠ π (cep_i0 hN) → k ≠ π (cep_i1 hN) → ∀ m : ℤ,
    r ≤ |y k 0 - y (π (cep_i0 hN)) 0 - m| ∧ r ≤ |y k 0 - y (π (cep_i1 hN)) 0 - m|

def cep_StrictlyOrdered {N : ℕ} (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) : Prop :=
  (∀ k k' : Fin N, k < k' → y (π k) 0 < y (π k') 0) ∧
    ∀ k k' : Fin N, y (π k') 0 < y (π k) 0 + 1

lemma cepn4_i0_ne_i1 (hN : 2 ≤ N) : cep_i0 hN ≠ cep_i1 hN := by
  intro h
  have := congrArg Fin.val h
  simp [cep_i0, cep_i1] at this

/-- Clamp. -/
lemma cepn4_clamp_abs (C x : ℝ) (hC : 0 ≤ C) : |max (-C) (min C x)| ≤ C := by
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma cepn4_clamp_eq {C x : ℝ} (h : |x| ≤ C) : max (-C) (min C x) = x := by
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

theorem cep_N4_gap_dynamics_proof [IsProbabilityMeasure P] (hN : 2 ≤ N) {D : DynData 1} (hs : D.s = 0) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : HRS.MC.CepC0.cep_IsC11 D.V)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → Fin N → Euc 1} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → Fin N → Euc 1}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) {π : Ω → Equiv.Perm (Fin N)}
    (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ}) {r : ℝ} (hr : 0 < r) :
    ∃ (C : ℝ) (c : ℝ → Ω → ℝ), 0 ≤ C ∧ (∀ u ω, |c u ω| ≤ C) ∧ (∀ u, 0 ≤ u → Measurable[ℱ u] (c u)) ∧
      ∀ᵐ ω ∂P, ∀ s t : ℝ, 0 ≤ s → s ≤ t →
        (∀ u ∈ Set.Icc s t, ((u : ℝ) : WithTop ℝ) < τ ω ∧ cep_StrictlyOrdered (π ω) (Y u ω) ∧
          cep_PairIsolated hN (π ω) (Y u ω) r ∧
          0 < Y u ω (π ω (cep_i1 hN)) 0 - Y u ω (π ω (cep_i0 hN)) 0 ∧ Y u ω (π ω (cep_i1 hN)) 0 - Y u ω (π ω (cep_i0 hN)) 0 < 1 / 4) →
        (Y t ω (π ω (cep_i1 hN)) 0 - Y t ω (π ω (cep_i0 hN)) 0) - (Y s ω (π ω (cep_i1 hN)) 0 - Y s ω (π ω (cep_i0 hN)) 0) =
          (∫ u in s..t, ((2 * a / N) / (Y u ω (π ω (cep_i1 hN)) 0 - Y u ω (π ω (cep_i0 hN)) 0) + c u ω))
            + 2 * Real.sqrt D.invβ *
              (((W' (Real.toNNReal t) ω (π ω (cep_i1 hN), 0) - W' (Real.toNNReal t) ω (π ω (cep_i0 hN), 0)) -
                (W' (Real.toNNReal s) ω (π ω (cep_i1 hN), 0) - W' (Real.toNNReal s) ω (π ω (cep_i0 hN), 0))) / Real.sqrt 2) := by
  obtain ⟨ρ, hρsm, hρper, hρodd, hρK⟩ := HRS.MC.CepK1.cep_K1_force_decomp_proof
  obtain ⟨Bρ, hBρ0, hBρ⟩ := cepn4_periodic_bound hρsm.continuous hρper
  obtain ⟨BH, hBH0, hBH⟩ := cepn4_H_bound
  obtain ⟨BV, hBV0, hBV⟩ := cepn4_gV_bound hV.1
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  set Cb : ℝ := (2 * a / N) * (BH + Bρ) + 2 * a * (Real.pi / (2 * r) + Bρ) + 2 * BV with hCb
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  let f : Equiv.Perm (Fin N) → (Fin N → Euc 1) → ℝ := fun σ y =>
    max (-Cb) (min Cb (cepn4_E a ρ D.V y (σ (cep_i0 hN)) (σ (cep_i1 hN))))
  have hfm : ∀ σ, Measurable (f σ) := fun σ =>
    measurable_const.max (measurable_const.min
      (cepn4_E_measurable a hρsm.continuous hV.1 _ _))
  refine ⟨Cb, fun u ω => f (π ω) (Y u ω), hCb0, fun u ω => cepn4_clamp_abs _ _ hCb0, ?_, ?_⟩
  · intro u hu
    have hYm : Measurable[ℱ u] (Y u) := hsol.sol.adapted u
    show Measurable[ℱ u] (fun ω => f (π ω) (Y u ω))
    have heq : (fun ω => f (π ω) (Y u ω)) =
        fun ω => ∑ σ : Equiv.Perm (Fin N), if π ω = σ then f σ (Y u ω) else 0 := by
      funext ω
      simp [Finset.sum_ite_eq]
    rw [heq]
    refine Finset.measurable_sum _ fun σ _ => ?_
    refine Measurable.ite (ℱ.mono (show (0 : ℝ) ≤ u from hu) _ (hπ σ)) ((hfm σ).comp hYm)
      measurable_const
  · filter_upwards [hsol.sol.eq] with ω hω
    intro s t hs0 hst hcond
    have ht0 : 0 ≤ t := le_trans hs0 hst
    have hsmem : s ∈ Set.Icc s t := ⟨le_rfl, hst⟩
    have htmem : t ∈ Set.Icc s t := ⟨hst, le_rfl⟩
    obtain ⟨hIt, hEt⟩ := hω t ht0 (hcond t htmem).1
    obtain ⟨hIs, hEs⟩ := hω s hs0 (hcond s hsmem).1
    have hne : π ω (cep_i0 hN) ≠ π ω (cep_i1 hN) := (π ω).injective.ne (cepn4_i0_ne_i1 hN)
    set i0 := π ω (cep_i0 hN) with hi0
    set i1 := π ω (cep_i1 hN) with hi1
    let Λ : (Fin N → Euc 1) →L[ℝ] ℝ :=
      (EuclideanSpace.proj (0 : Fin 1) ∘L ContinuousLinearMap.proj i1) -
        (EuclideanSpace.proj (0 : Fin 1) ∘L ContinuousLinearMap.proj i0)
    have hΛ : ∀ y : Fin N → Euc 1, Λ y = y i1 0 - y i0 0 := fun y => rfl
    set g : ℝ → ℝ := fun u => Λ (liftedDrift D (Y u ω)) with hg
    have hgI : IntegrableOn g (Set.Icc 0 t) := Λ.integrable_comp hIt
    have hEt' : Y t ω = Y₀ ω + (∫ u in Set.Icc 0 t, liftedDrift D (Y u ω)) +
        ∑ ij, W' (Real.toNNReal t) ω ij • liftedNoise D ij := hEt
    have hEs' : Y s ω = Y₀ ω + (∫ u in Set.Icc 0 s, liftedDrift D (Y u ω)) +
        ∑ ij, W' (Real.toNNReal s) ω ij • liftedNoise D ij := hEs
    rw [sum_liftedNoise] at hEt' hEs'
    have hlt : Λ (Y t ω) = Λ (Y₀ ω) + (∫ u in Set.Icc 0 t, g u) +
        Real.sqrt (2 * D.invβ) * (W' (Real.toNNReal t) ω (i1, 0) - W' (Real.toNNReal t) ω (i0, 0)) := by
      rw [hEt', map_add, map_add, ← Λ.integral_comp_comm hIt]
      simp [hΛ, ofCoords, hg]
      ring
    have hls : Λ (Y s ω) = Λ (Y₀ ω) + (∫ u in Set.Icc 0 s, g u) +
        Real.sqrt (2 * D.invβ) * (W' (Real.toNNReal s) ω (i1, 0) - W' (Real.toNNReal s) ω (i0, 0)) := by
      rw [hEs', map_add, map_add, ← Λ.integral_comp_comm hIs]
      simp [hΛ, ofCoords, hg]
      ring
    have hIcc : ∀ x : ℝ, 0 ≤ x → ∫ u in Set.Icc 0 x, g u = ∫ u in (0 : ℝ)..x, g u := fun x hx => by
      rw [intervalIntegral.integral_of_le hx, integral_Icc_eq_integral_Ioc]
    have hII_t : IntervalIntegrable g volume 0 t := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0]; exact hgI
    have hII_s : IntervalIntegrable g volume 0 s := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hs0]
      exact hgI.mono_set (Set.Icc_subset_Icc_right hst)
    have hsub : ∫ u in s..t, g u = (∫ u in Set.Icc 0 t, g u) - ∫ u in Set.Icc 0 s, g u := by
      rw [hIcc t ht0, hIcc s hs0, intervalIntegral.integral_interval_sub_left hII_t hII_s]
    have hint : ∫ u in s..t, g u =
        ∫ u in s..t, ((2 * a / N) / (Y u ω i1 0 - Y u ω i0 0) + f (π ω) (Y u ω)) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le hst] at hu
      obtain ⟨hlt', -, hiso, hG0, hG1⟩ := hcond u hu
      have hu0 : 0 ≤ u := le_trans hs0 hu.1
      have hfree := hsol.mem ω u hu0 hlt'
      have hdr : g u = cepn4_bdrift a ρ D.V (Y u ω) i1 - cepn4_bdrift a ρ D.V (Y u ω) i0 := by
        simp only [hg, hΛ]
        rw [cepn4_drift_comp hs hM hρK hfree i1, cepn4_drift_comp hs hM hρK hfree i0]
      have hbd := cepn4_E_bound ha hρodd hBρ hBρ0 hBH hBV hr hNpos (y := Y u ω) hne hiso hG0 hG1
      have hf : f (π ω) (Y u ω) = cepn4_E a ρ D.V (Y u ω) i0 i1 :=
        cepn4_clamp_eq hbd
      simp only [hf, hdr, cepn4_E]
      ring
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hsq : Real.sqrt (2 * D.invβ) = Real.sqrt 2 * Real.sqrt D.invβ :=
      Real.sqrt_mul (by norm_num) _
    have hs2ne : Real.sqrt 2 ≠ 0 := by positivity
    show (Y t ω i1 0 - Y t ω i0 0) - (Y s ω i1 0 - Y s ω i0 0) =
      (∫ u in s..t, ((2 * a / N) / (Y u ω i1 0 - Y u ω i0 0) + f (π ω) (Y u ω))) + _
    rw [← hint, hsub]
    have e1 := hlt
    have e2 := hls
    rw [hΛ] at e1 e2
    rw [hsq] at e1 e2
    calc _ = (Λ (Y t ω)) - Λ (Y s ω) := by rw [hΛ, hΛ]
      _ = _ := by
        rw [hlt, hls, hsq]
        have : ∀ X : ℝ, 2 * Real.sqrt D.invβ * (X / Real.sqrt 2) = Real.sqrt 2 * Real.sqrt D.invβ * X := by
          intro X
          calc 2 * Real.sqrt D.invβ * (X / Real.sqrt 2)
              = (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt D.invβ * (X / Real.sqrt 2) := by rw [hs2]
            _ = Real.sqrt 2 * Real.sqrt D.invβ * X := by field_simp
        rw [this]
        ring

end HRS.MC.CepN4
