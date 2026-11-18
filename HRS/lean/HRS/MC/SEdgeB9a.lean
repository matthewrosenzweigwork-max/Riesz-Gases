import HRS.MC.SEdgeVocab
import HRS.MC.SEdgeB3
import HRS.MC.SEdgeB4a
import HRS.MC.SEdgeB4b
import HRS.Equilibrium.QuadraticLimit.Assembly

/-!
# Packet B9a: `quadratic_limit` with linearly growing test functions (relocation of
`sed_B9a_quadratic_limit_lin`)

Route: (1) the proof of `HRS.quadratic_limit_proof` is re-run (its last lines are copied) to export the
measurability of `G, Qv, Lin`; (2) the `L^{3/2}` bound of the centred energy `B_N` under the Gibbs law
(the proof of `sed_B4b_energy_proof`, for a general envelope kernel `h`); (3) `Qv in L^1` by truncation and the
bounded-continuous convergence; (4) truncation of the linearly growing test function.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B9a

open HRS.Sec7
open HRS.MC.SEdge

section L32

variable {d : ℕ}

/-- The centred scaled energy `B_N = N (mE(h) - E_Q mE(h))`. -/
def b9a_Bn (D : HRS.Q08.Q08Data d) (N : ℕ) (X : Config d N) : ℝ :=
  (N : ℝ) * (modulatedEnergy D.h X D.μ - ∫ Y, modulatedEnergy D.h Y D.μ ∂(D.Gibbs N))

/-- `L^{3/2}` bound of `B_N` under the Gibbs law, uniform in `N` (proof of `sed_B4b_energy_proof` for a
general envelope kernel). -/
theorem b9a_L32 (D : HRS.Q08.Q08Data d) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      Integrable (fun X : Config d N => |b9a_Bn D N X| ^ (3 / 2 : ℝ)) (D.Gibbs N) ∧
      ∫ X, |b9a_Bn D N X| ^ (3 / 2 : ℝ) ∂(D.Gibbs N) ≤ C := by
  haveI hP : IsProbabilityMeasure D.μ := HRS.Q08.q08_isProb_μ D
  have hk : Integrable (fun z : Torus d × Torus d => D.h z.1 z.2 ^ 2) (D.μ.prod D.μ) :=
    HRS.Q08.q08gl_h_sq_int D
  set J : ℝ := ∫ x, ∫ y, D.h x y ∂D.μ ∂D.μ with hJ
  set K : ℝ := 3 * ∫ x, ∫ y, D.h x y ^ 2 ∂D.μ ∂D.μ with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (by norm_num) (integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _)
  obtain ⟨C43, hC43, T43⟩ := HRS.MC.SEdge.B4a.sed_B4a_transfer_proof D.hd D.hs0 D.hs D.hβ.le D.hρ
    (r := 4 / 3) (by norm_num)
  obtain ⟨C2, hC2, T2⟩ := HRS.MC.SEdge.B4a.sed_B4a_transfer_proof D.hd D.hs0 D.hs D.hβ.le D.hρ
    (r := 2) (by norm_num)
  set A : ℝ := C2 * K ^ (1 / 2 : ℝ) with hAdef
  have hA0 : 0 ≤ A := mul_nonneg hC2 (Real.rpow_nonneg hK0 _)
  set A' : ℝ := C43 * (2 * K + 2 * A ^ 2) ^ (1 / (4 / 3 : ℝ)) with hA'def
  have hA'0 : 0 ≤ A' := mul_nonneg hC43 (Real.rpow_nonneg (by positivity) _)
  refine ⟨A', fun N hN => ?_⟩
  haveI hG : IsProbabilityMeasure (D.Gibbs N) := HRS.Q08.q08_gibbs_isProb D N hN
  haveI hPP : IsProbabilityMeasure (D.prodLaw N) := by
    unfold HRS.Q08.Q08Data.prodLaw; infer_instance
  set Y : Config d N → ℝ := fun X => (N : ℝ) * modulatedEnergy D.h X D.μ + (1 / 2) * J with hYdef
  have hYm : Measurable Y :=
    (measurable_const.mul (HRS.Q08.q08_measurable_energy D N)).add measurable_const
  have hYL : MemLp Y 2 (D.prodLaw N) := HRS.Q08.q08gl_Z_memLp D.μ D.h D.hmeas hk D.hsymm N hN
  have hYint : ∫ X, Y X ^ 2 ∂(D.prodLaw N) ≤ 3 * ∫ x, ∫ y, D.h x y ^ 2 ∂D.μ ∂D.μ :=
    HRS.Q08.q08_energy_L2 D.μ D.h D.hmeas D.hsymm hk N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hYsq : ∫⁻ X, ENNReal.ofReal (Y X ^ 2) ∂(D.prodLaw N) ≤ ENNReal.ofReal K := by
    rw [← ofReal_integral_eq_lintegral_ofReal hYL.integrable_sq
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hYint
  have hA : ∫⁻ X, ENNReal.ofReal |Y X| ∂(D.Gibbs N) ≤ ENNReal.ofReal A := by
    have h1 : ∫⁻ X, ENNReal.ofReal |Y X| ∂(D.Gibbs N) ≤ ENNReal.ofReal C2 *
        (∫⁻ X, (ENNReal.ofReal |Y X|) ^ (2 : ℝ) ∂(D.prodLaw N)) ^ (1 / (2 : ℝ)) :=
      T2 N hN (fun X => ENNReal.ofReal |Y X|) hYm.abs.ennreal_ofReal
    have h2 : ∫⁻ X, (ENNReal.ofReal |Y X|) ^ (2 : ℝ) ∂(D.prodLaw N)
        = ∫⁻ X, ENNReal.ofReal (Y X ^ 2) ∂(D.prodLaw N) := by
      refine lintegral_congr fun X => ?_
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two, sq_abs]
    rw [h2] at h1
    refine h1.trans ?_
    calc ENNReal.ofReal C2 * (∫⁻ X, ENNReal.ofReal (Y X ^ 2) ∂(D.prodLaw N)) ^ (1 / (2 : ℝ))
        ≤ ENNReal.ofReal C2 * (ENNReal.ofReal K) ^ (1 / (2 : ℝ)) := by gcongr
      _ = ENNReal.ofReal A := by
        rw [hAdef, ENNReal.ofReal_mul hC2, ENNReal.ofReal_rpow_of_nonneg hK0 (by norm_num)]
  have hGY : Integrable Y (D.Gibbs N) := by
    refine ⟨hYm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact lt_of_le_of_lt hA ENNReal.ofReal_lt_top
  have hYabs : ∫ X, |Y X| ∂(D.Gibbs N) ≤ A := by
    have := ofReal_integral_eq_lintegral_ofReal hGY.abs
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    rw [← this] at hA
    exact (ENNReal.ofReal_le_ofReal_iff hA0).1 hA
  set c : ℝ := ∫ X, Y X ∂(D.Gibbs N) with hc
  have hcA : |c| ≤ A := (abs_integral_le_integral_abs).trans hYabs
  have hNmE : ∀ X, (N : ℝ) * modulatedEnergy D.h X D.μ = Y X - J / 2 := by
    intro X
    simp only [hYdef]
    ring
  have hint2 : ∫ X, (N : ℝ) * modulatedEnergy D.h X D.μ ∂(D.Gibbs N) = c - J / 2 := by
    simp_rw [hNmE]
    rw [integral_sub hGY (integrable_const _)]
    simp [hc]
  have hB : ∀ X, b9a_Bn D N X = Y X - c := by
    intro X
    unfold b9a_Bn
    have h3 : ∫ Z, modulatedEnergy D.h Z D.μ ∂(D.Gibbs N) = (N : ℝ)⁻¹ * (c - J / 2) := by
      rw [← hint2, integral_const_mul]
      field_simp
    rw [h3, mul_sub, hNmE X]
    field_simp
    ring
  have hsq : ∫⁻ X, ENNReal.ofReal ((Y X - c) ^ 2) ∂(D.prodLaw N) ≤
      ENNReal.ofReal (2 * K + 2 * A ^ 2) := by
    have hi : Integrable (fun X => (Y X - c) ^ 2) (D.prodLaw N) := by
      have := (hYL.sub (memLp_const c)).integrable_sq
      simpa using this
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hdom : Integrable (fun X => 2 * Y X ^ 2 + 2 * c ^ 2) (D.prodLaw N) :=
      (hYL.integrable_sq.const_mul 2).add (integrable_const _)
    calc ∫ X, (Y X - c) ^ 2 ∂(D.prodLaw N)
        ≤ ∫ X, (2 * Y X ^ 2 + 2 * c ^ 2) ∂(D.prodLaw N) :=
          integral_mono hi hdom (fun X => by nlinarith [sq_nonneg (Y X + c)])
      _ = 2 * ∫ X, Y X ^ 2 ∂(D.prodLaw N) + 2 * c ^ 2 := by
          rw [integral_add (hYL.integrable_sq.const_mul 2) (integrable_const _),
            integral_const_mul]
          simp
      _ ≤ 2 * K + 2 * A ^ 2 := by
          have : c ^ 2 ≤ A ^ 2 := by
            rw [← sq_abs c]
            exact pow_le_pow_left₀ (abs_nonneg _) hcA 2
          have := hYint
          nlinarith
  have hf : Measurable (fun X => ENNReal.ofReal (|Y X - c| ^ (3 / 2 : ℝ))) :=
    ((hYm.sub_const c).abs.pow_const _).ennreal_ofReal
  have h1 : ∫⁻ X, ENNReal.ofReal (|Y X - c| ^ (3 / 2 : ℝ)) ∂(D.Gibbs N) ≤ ENNReal.ofReal C43 *
      (∫⁻ X, (ENNReal.ofReal (|Y X - c| ^ (3 / 2 : ℝ))) ^ (4 / 3 : ℝ) ∂(D.prodLaw N)) ^
        (1 / (4 / 3 : ℝ)) :=
    T43 N hN _ hf
  have h2 : ∫⁻ X, (ENNReal.ofReal (|Y X - c| ^ (3 / 2 : ℝ))) ^ (4 / 3 : ℝ) ∂(D.prodLaw N) =
      ∫⁻ X, ENNReal.ofReal ((Y X - c) ^ 2) ∂(D.prodLaw N) := by
    refine lintegral_congr fun X => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (by norm_num),
      ← Real.rpow_mul (abs_nonneg _)]
    have : (3 / 2 : ℝ) * (4 / 3) = (2 : ℕ) := by norm_num
    rw [this, Real.rpow_natCast, sq_abs]
  rw [h2] at h1
  have h3 : ∫⁻ X, ENNReal.ofReal (|Y X - c| ^ (3 / 2 : ℝ)) ∂(D.Gibbs N) ≤ ENNReal.ofReal A' := by
    refine h1.trans ?_
    calc ENNReal.ofReal C43 * (∫⁻ X, ENNReal.ofReal ((Y X - c) ^ 2) ∂(D.prodLaw N)) ^
          (1 / (4 / 3 : ℝ))
        ≤ ENNReal.ofReal C43 * (ENNReal.ofReal (2 * K + 2 * A ^ 2)) ^ (1 / (4 / 3 : ℝ)) := by
          gcongr
      _ = ENNReal.ofReal A' := by
          rw [hA'def, ENNReal.ofReal_mul hC43,
            ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  have hint3 : Integrable (fun X => |Y X - c| ^ (3 / 2 : ℝ)) (D.Gibbs N) := by
    refine ⟨((hYm.sub_const c).abs.pow_const _).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have : ∀ X, ‖|Y X - c| ^ (3 / 2 : ℝ)‖ₑ = ENNReal.ofReal (|Y X - c| ^ (3 / 2 : ℝ)) := fun X => by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    simp_rw [this]
    exact lt_of_le_of_lt h3 ENNReal.ofReal_lt_top
  have h4 : ∫ X, |Y X - c| ^ (3 / 2 : ℝ) ∂(D.Gibbs N) =
      (∫⁻ X, ENNReal.ofReal (|Y X - c| ^ (3 / 2 : ℝ)) ∂(D.Gibbs N)).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun X => Real.rpow_nonneg (abs_nonneg _) _)
      ((hYm.sub_const c).abs.pow_const _).aestronglyMeasurable
  simp_rw [hB]
  exact ⟨hint3, by rw [h4]; exact ENNReal.toReal_le_of_le_ofReal hA'0 h3⟩

end L32


section Core

variable {d : ℕ} {s : ℝ}

/-- The `Q08Data` bundle of the hypotheses of `quadratic_limit`. -/
def b9a_D (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, z ≠ 0 → 1 ≤ periodicRiesz d s z + c) (B : ℝ) (h : Torus d → Torus d → ℝ)
    (hmeas : Measurable (Function.uncurry h)) (hsymm : ∀ x y, h x y = h y x)
    (hB : ∀ x y, x ≠ y → |h x y| ≤ B * (periodicRiesz d s (x - y) + c))
    (e : ℕ → Torus d → ℝ) (he : IsONBL2Zero (withDensityReal ρ) e)
    (p : ℕ) (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Measurable (φ a) ∧ ∃ M, ∀ x, |φ a x| ≤ M) :
    HRS.Q08.Q08Data d :=
  ⟨s, β, ρ, c, B, h, e, p, φ, hd, hs0, hs, hβ, hρ, hc, hmeas, hsymm, hB, he, hφ⟩

open HRS.Q08 in
/-- The proof of `HRS.quadratic_limit_proof`, with the measurability of `G, Qv, Lin` exported. -/
theorem b9a_core (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, z ≠ 0 → 1 ≤ periodicRiesz d s z + c) (B : ℝ) (h : Torus d → Torus d → ℝ)
    (hmeas : Measurable (Function.uncurry h)) (hsymm : ∀ x y, h x y = h y x)
    (hB : ∀ x y, x ≠ y → |h x y| ≤ B * (periodicRiesz d s (x - y) + c))
    (e : ℕ → Torus d → ℝ) (he : IsONBL2Zero (withDensityReal ρ) e)
    (p : ℕ) (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Measurable (φ a) ∧ ∃ M, ∀ x, |φ a x| ≤ M) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (G : ℕ → Ω → ℝ) (Qv : Ω → ℝ) (Lin : Fin p → Ω → ℝ),
      sed_QLData d s β ρ h e φ P G Qv Lin ∧
      ∀ F : ℝ × (Fin p → ℝ) → ℝ, Continuous F → (∃ M, ∀ z, |F z| ≤ M) →
        Tendsto (fun N : ℕ => ∫ X, F (HRS.Q08.q08Stat
          (b9a_D hd hs0 hs hβ hρ c hc B h hmeas hsymm hB e he p φ hφ) N X)
          ∂(sed_Q d s N β ρ)) atTop (𝓝 (∫ ω, F (Qv ω, fun a => Lin a ω) ∂P)) := by
  let D : Q08Data d := b9a_D hd hs0 hs hβ hρ c hc B h hmeas hsymm hB e he p φ hφ
  obtain ⟨hCs, hCp, hCle, hCres⟩ := q08_Cmat_spec D
  obtain ⟨hHs, hHsum⟩ := q08_Hmat_spec D
  have hC : q08_IsCov D.Cmat := ⟨hCs, hCp, hCle⟩
  obtain ⟨Ω, mΩ, P, hP, G, Q, Lin, hGm, hQm, hLm, hlaw, hLin, hQ⟩ :=
    q08_chaos_exists D.Cmat D.Hmat D.coef hC hHs hHsum (q08_coef_summable D)
  refine ⟨Ω, mΩ, P, hP, G, Q, Lin, ⟨hGm, hQm, hLm, hlaw, hLin, hQ⟩, ?_⟩
  intro F hFc hFb
  have hT0 : Measurable (fun ω => (Q ω, fun a => Lin a ω)) :=
    hQm.prodMk (measurable_pi_iff.2 fun a => hLm a)
  let lam : Measure (ℝ × (Fin D.p → ℝ)) := P.map (fun ω => (Q ω, fun a => Lin a ω))
  have : IsProbabilityMeasure lam := (Measure.isProbabilityMeasure_map_iff hT0.aemeasurable).2 hP
  have hint : ∀ F' : ℝ × (Fin D.p → ℝ) → ℝ, Continuous F' →
      ∫ z, F' z ∂lam = ∫ ω, F' (Q ω, fun a => Lin a ω) ∂P := fun F' hF' =>
    integral_map hT0.aemeasurable hF'.aestronglyMeasurable
  have hlip : ∀ F' : ℝ × (Fin D.p → ℝ) → ℝ, (∃ M, ∀ z, |F' z| ≤ M) → (∃ K : ℝ≥0, LipschitzWith K F') →
      Tendsto (fun N => ∫ X, F' (q08Stat D N X) ∂(D.Gibbs N)) atTop (𝓝 (∫ z, F' z ∂lam)) := by
    intro F' hb hl
    obtain ⟨M, hM⟩ := hb
    obtain ⟨K, hK⟩ := hl
    rw [hint F' hK.continuous]
    have A : Tendsto (fun L => q08FiniteChaos D L F') atTop
        (𝓝 (∫ ω, F' (Q ω, fun a => Lin a ω) ∂P)) :=
      q08_finiteChaos_tendsto P D.Cmat D.Hmat D.coef G Q Lin hGm hQm hLm hlaw hLin hQ F' M hM K hK
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨L1, hL1⟩ := Metric.tendsto_atTop.1 A (ε / 2) (by linarith)
    obtain ⟨L0, hL0⟩ := q08_gibbs_approx D F' ⟨M, hM⟩ ⟨K, hK⟩ (ε / 2) (by linarith)
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hL0 (max L0 L1) (le_max_left _ _))
    refine ⟨N0, fun N hN => ?_⟩
    have h1 := hN0 N hN
    have h2 := hL1 (max L0 L1) (le_max_right _ _)
    rw [Real.dist_eq] at h2 ⊢
    calc |∫ X, F' (q08Stat D N X) ∂(D.Gibbs N) - ∫ ω, F' (Q ω, fun a => Lin a ω) ∂P|
        ≤ |∫ X, F' (q08Stat D N X) ∂(D.Gibbs N) - q08FiniteChaos D (max L0 L1) F'| +
          |q08FiniteChaos D (max L0 L1) F' - ∫ ω, F' (Q ω, fun a => Lin a ω) ∂P| :=
          abs_sub_le _ _ _
      _ < ε := by linarith
  have main := q08_upgrade (X := fun N => Config d N) (fun N => D.Gibbs N)
    (fun N hN => q08_gibbs_isProb D N hN) (fun N => q08Stat D N) (q08_measurable_stat D) lam hlip
    F hFc hFb
  rw [hint F hFc] at main
  exact main

end Core


section Trunc

/-- Integrability from a uniform bound on the truncated absolute moments. -/
theorem b9a_integrable_of_trunc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Q : Ω → ℝ} (hQ : Measurable Q) (C : ℝ)
    (h : ∀ n : ℕ, ∫ ω, min |Q ω| n ∂P ≤ C) : Integrable Q P := by
  have hm : ∀ n : ℕ, Measurable (fun ω => min |Q ω| (n : ℝ)) := fun n =>
    hQ.abs.min measurable_const
  have hg : ∀ n : ℕ, Measurable (fun ω => ENNReal.ofReal (min |Q ω| (n : ℝ))) := fun n =>
    (hm n).ennreal_ofReal
  have hnn : ∀ (n : ℕ) ω, 0 ≤ min |Q ω| (n : ℝ) := fun n ω =>
    le_min (abs_nonneg _) (Nat.cast_nonneg n)
  have hint : ∀ n : ℕ, Integrable (fun ω => min |Q ω| (n : ℝ)) P := fun n =>
    Integrable.of_bound (hm n).aestronglyMeasurable (n : ℝ) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn n ω)]
      exact min_le_right _ _)
  refine ⟨hQ.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hmono : Monotone (fun (n : ℕ) ω => ENNReal.ofReal (min |Q ω| (n : ℝ))) :=
    fun n m hnm ω => ENNReal.ofReal_le_ofReal (min_le_min le_rfl (Nat.cast_le.2 hnm))
  have hsup : ∀ ω, ⨆ n : ℕ, ENNReal.ofReal (min |Q ω| (n : ℝ)) = ‖Q ω‖ₑ := by
    intro ω
    rw [Real.enorm_eq_ofReal_abs]
    refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
    obtain ⟨n, hn⟩ := exists_nat_ge |Q ω|
    refine le_iSup_of_le n ?_
    rw [min_eq_left hn]
  have : ∫⁻ ω, ‖Q ω‖ₑ ∂P = ⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal (min |Q ω| (n : ℝ)) ∂P := by
    rw [← lintegral_iSup hg hmono]
    exact lintegral_congr fun ω => (hsup ω).symm
  rw [this]
  refine lt_of_le_of_lt (iSup_le fun n => ?_) (ENNReal.ofReal_lt_top (r := C))
  rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (ae_of_all _ fun ω => hnn n ω)]
  exact ENNReal.ofReal_le_ofReal (h n)

/-- The clamp to `[-K, K]`. -/
def b9a_cl (K b : ℝ) : ℝ := max (-K) (min b K)

theorem b9a_cl_of_abs_le {K b : ℝ} (h : |b| ≤ K) : b9a_cl K b = b := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  unfold b9a_cl
  rw [min_eq_left h2, max_eq_right h1]

theorem b9a_abs_cl_le_K {K : ℝ} (hK : 0 ≤ K) (b : ℝ) : |b9a_cl K b| ≤ K := by
  unfold b9a_cl
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem b9a_abs_cl_le {K : ℝ} (hK : 0 ≤ K) (b : ℝ) : |b9a_cl K b| ≤ |b| := by
  unfold b9a_cl
  rw [abs_le]
  constructor
  · refine le_trans ?_ (le_max_right _ _)
    refine le_min ?_ ?_
    · linarith [neg_abs_le b]
    · linarith [abs_nonneg b]
  · refine max_le (by linarith [abs_nonneg b]) ?_
    exact (min_le_left _ _).trans (le_abs_self b)

theorem b9a_continuous_cl (K : ℝ) : Continuous (b9a_cl K) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem b9a_rpow_32 {t : ℝ} (ht : 0 ≤ t) : t ^ (3 / 2 : ℝ) = t * Real.sqrt t := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add' ht (by norm_num), Real.rpow_one]

/-- Pointwise truncation error of a linearly growing function. -/
theorem b9a_trunc_pt {p : ℕ} {F : ℝ × (Fin p → ℝ) → ℝ} {M : ℝ}
    (hF : ∀ b z, |F (b, z)| ≤ M * (1 + |b|)) {K : ℝ} (hK : 1 ≤ K) (b : ℝ) (z : Fin p → ℝ) :
    |F (b, z) - F (b9a_cl K b, z)| ≤ 4 * M * (Real.sqrt K)⁻¹ * |b| ^ (3 / 2 : ℝ) := by
  have hM : 0 ≤ M := by
    have := hF 0 0
    simp at this
    exact (abs_nonneg _).trans this
  have hK0 : 0 < K := by linarith
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK0
  have hrhs : 0 ≤ 4 * M * (Real.sqrt K)⁻¹ * |b| ^ (3 / 2 : ℝ) := by positivity
  by_cases hb : |b| ≤ K
  · rw [b9a_cl_of_abs_le hb, sub_self, abs_zero]
    exact hrhs
  · push_neg at hb
    have h1 := hF b z
    have h2 := hF (b9a_cl K b) z
    have h3 := b9a_abs_cl_le_K hK0.le b
    have hb1 : 1 ≤ |b| := by linarith
    have h4 : |F (b, z) - F (b9a_cl K b, z)| ≤ 4 * M * |b| := by
      calc |F (b, z) - F (b9a_cl K b, z)| ≤ |F (b, z)| + |F (b9a_cl K b, z)| := abs_sub _ _
        _ ≤ M * (1 + |b|) + M * (1 + K) := by
          refine add_le_add h1 (h2.trans ?_)
          exact mul_le_mul_of_nonneg_left (by linarith) hM
        _ ≤ 4 * M * |b| := by nlinarith
    refine h4.trans ?_
    rw [b9a_rpow_32 (abs_nonneg b)]
    have h5 : Real.sqrt K ≤ Real.sqrt |b| := Real.sqrt_le_sqrt hb.le
    have h6 : |b| ≤ (Real.sqrt K)⁻¹ * (|b| * Real.sqrt |b|) := by
      rw [← mul_assoc, mul_comm (Real.sqrt K)⁻¹, mul_assoc]
      have : 1 ≤ (Real.sqrt K)⁻¹ * Real.sqrt |b| := by
        rw [← div_eq_inv_mul, le_div_iff₀ hsK]; linarith
      nlinarith [abs_nonneg b]
    calc 4 * M * |b| ≤ 4 * M * ((Real.sqrt K)⁻¹ * (|b| * Real.sqrt |b|)) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = 4 * M * (Real.sqrt K)⁻¹ * (|b| * Real.sqrt |b|) := by ring

end Trunc


theorem b9a_le_one_add {t : ℝ} (ht : 0 ≤ t) : t ≤ 1 + t ^ (3 / 2 : ℝ) := by
  rw [b9a_rpow_32 ht]
  by_cases h1 : t ≤ 1
  · nlinarith [Real.sqrt_nonneg t]
  · push_neg at h1
    have : 1 ≤ Real.sqrt t := Real.one_le_sqrt.2 h1.le
    nlinarith [Real.sqrt_nonneg t]

section Main

variable {d : ℕ} {s : ℝ}

open HRS.Q08 in
theorem sed_B9a_quadratic_limit_lin_proof (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ}
    (hβ : 0 < β) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, z ≠ 0 → 1 ≤ periodicRiesz d s z + c) (B : ℝ) (h : Torus d → Torus d → ℝ)
    (hmeas : Measurable (Function.uncurry h)) (hsymm : ∀ x y, h x y = h y x)
    (hB : ∀ x y, x ≠ y → |h x y| ≤ B * (periodicRiesz d s (x - y) + c))
    (e : ℕ → Torus d → ℝ) (he : IsONBL2Zero (withDensityReal ρ) e)
    (p : ℕ) (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Measurable (φ a) ∧ ∃ M, ∀ x, |φ a x| ≤ M) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (G : ℕ → Ω → ℝ) (Qv : Ω → ℝ) (Lin : Fin p → Ω → ℝ),
      sed_QLData d s β ρ h e φ P G Qv Lin ∧ Integrable Qv P ∧
      ∀ F : ℝ × (Fin p → ℝ) → ℝ, Continuous F → (∃ M, ∀ b z, |F (b, z)| ≤ M * (1 + |b|)) →
        Tendsto (fun N : ℕ => ∫ X, F ((N : ℝ) * (modulatedEnergy h X (withDensityReal ρ) -
              ∫ Y, modulatedEnergy h Y (withDensityReal ρ) ∂(sed_Q d s N β ρ)),
            fun a => Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, φ a (X i) -
              pair (firstMarginal (sed_Q d s N β ρ)) (φ a))) ∂(sed_Q d s N β ρ)) atTop
          (𝓝 (∫ ω, F (Qv ω, fun a => Lin a ω) ∂P)) := by
  obtain ⟨Ω, mΩ, P, hP, G, Qv, Lin, hdata, hbdd⟩ :=
    b9a_core hd hs0 hs hβ hρ c hc B h hmeas hsymm hB e he p φ hφ
  have hQm : Measurable Qv := hdata.2.1
  have hLm : ∀ a, Measurable (Lin a) := hdata.2.2.1
  set D : Q08Data d := b9a_D hd hs0 hs hβ hρ c hc B h hmeas hsymm hB e he p φ hφ with hDdef
  obtain ⟨CL, hCL⟩ := b9a_L32 D
  have hQprob : ∀ N : ℕ, 1 ≤ N → IsProbabilityMeasure (sed_Q d s N β ρ) := fun N hN =>
    q08_gibbs_isProb D N hN
  have hstatm : ∀ N : ℕ, Measurable (q08Stat D N) := q08_measurable_stat D
  have hBm : ∀ N : ℕ, Measurable (b9a_Bn D N) := fun N =>
    measurable_const.mul ((q08_measurable_energy D N).sub measurable_const)
  have hT0 : Measurable (fun ω => (Qv ω, fun a => Lin a ω)) :=
    hQm.prodMk (measurable_pi_iff.2 fun a => hLm a)
  -- integrability of linearly growing functions of the statistic under the Gibbs law
  have hintG : ∀ (Gf : ℝ × (Fin p → ℝ) → ℝ), Continuous Gf → ∀ M : ℝ,
      (∀ b z, |Gf (b, z)| ≤ M * (1 + |b|)) → ∀ N : ℕ, 1 ≤ N →
      Integrable (fun X : Config d N => Gf (q08Stat D N X)) (sed_Q d s N β ρ) := by
    intro Gf hGc M hGM N hN
    haveI : IsProbabilityMeasure (D.Gibbs N) := q08_gibbs_isProb D N hN
    obtain ⟨hI, -⟩ := hCL N hN
    have hM0 : 0 ≤ M := by
      have := hGM 0 0
      simp at this
      exact (abs_nonneg _).trans this
    refine Integrable.mono' (((integrable_const (2 : ℝ)).add hI).const_mul M)
      (hGc.measurable.comp (hstatm N)).aestronglyMeasurable (ae_of_all _ fun X => ?_)
    rw [Real.norm_eq_abs]
    refine (hGM _ _).trans ?_
    show M * (1 + |b9a_Bn D N X|) ≤ M * (2 + |b9a_Bn D N X| ^ (3 / 2 : ℝ))
    exact mul_le_mul_of_nonneg_left
      (by linarith [b9a_le_one_add (abs_nonneg (b9a_Bn D N X))]) hM0
  -- Qv is integrable
  have hQvint : Integrable Qv P := by
    refine b9a_integrable_of_trunc P hQm (1 + CL) fun n => ?_
    have hFc : Continuous (fun q : ℝ × (Fin p → ℝ) => min |q.1| (n : ℝ)) :=
      (continuous_fst.abs).min continuous_const
    have hFb : ∃ M, ∀ q : ℝ × (Fin p → ℝ), |min |q.1| (n : ℝ)| ≤ M := ⟨n, fun q => by
      rw [abs_of_nonneg (le_min (abs_nonneg _) (Nat.cast_nonneg n))]
      exact min_le_right _ _⟩
    have hlim := hbdd _ hFc hFb
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨1, fun N hN => ?_⟩)
    haveI := hQprob N hN
    haveI : IsProbabilityMeasure (D.Gibbs N) := q08_gibbs_isProb D N hN
    obtain ⟨hI, hC⟩ := hCL N hN
    have hmeasF : Measurable (fun X : Config d N => min |b9a_Bn D N X| (n : ℝ)) :=
      (hBm N).abs.min measurable_const
    have hi1 : Integrable (fun X : Config d N => min |b9a_Bn D N X| (n : ℝ)) (D.Gibbs N) :=
      Integrable.of_bound hmeasF.aestronglyMeasurable (n : ℝ) (ae_of_all _ fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg _) (Nat.cast_nonneg n))]
        exact min_le_right _ _)
    calc ∫ X, min |b9a_Bn D N X| (n : ℝ) ∂(D.Gibbs N)
        ≤ ∫ X, (1 + |b9a_Bn D N X| ^ (3 / 2 : ℝ)) ∂(D.Gibbs N) :=
          integral_mono hi1 ((integrable_const (1 : ℝ)).add hI) (fun X =>
            (min_le_left _ _).trans (b9a_le_one_add (abs_nonneg _)))
      _ = 1 + ∫ X, |b9a_Bn D N X| ^ (3 / 2 : ℝ) ∂(D.Gibbs N) := by
          rw [integral_add (integrable_const _) hI]
          simp
      _ ≤ 1 + CL := by linarith
  refine ⟨Ω, mΩ, P, hP, G, Qv, Lin, hdata, hQvint, ?_⟩
  have key : ∀ F : ℝ × (Fin p → ℝ) → ℝ, Continuous F →
      (∃ M, ∀ b z, |F (b, z)| ≤ M * (1 + |b|)) →
      Tendsto (fun N : ℕ => ∫ X, F (q08Stat D N X) ∂(sed_Q d s N β ρ)) atTop
        (𝓝 (∫ ω, F (Qv ω, fun a => Lin a ω) ∂P)) := by
    intro F hFc hFM
    obtain ⟨M, hM⟩ := hFM
    have hM0 : 0 ≤ M := by
      have := hM 0 0
      simp at this
      exact (abs_nonneg _).trans this
    -- the truncated functions
    obtain ⟨Fn, hFn⟩ : ∃ Fn : ℕ → ℝ × (Fin p → ℝ) → ℝ,
        ∀ n q, Fn n q = F (b9a_cl n q.1, q.2) := ⟨fun n q => F (b9a_cl n q.1, q.2), fun _ _ => rfl⟩
    have hFnc : ∀ n, Continuous (Fn n) := fun n => by
      have : Fn n = fun q => F (b9a_cl n q.1, q.2) := funext (hFn n)
      rw [this]
      exact hFc.comp (((b9a_continuous_cl n).comp continuous_fst).prodMk continuous_snd)
    have hFnM : ∀ n b z, |Fn n (b, z)| ≤ M * (1 + |b|) := fun n b z => by
      rw [hFn]
      exact (hM (b9a_cl n b) z).trans (mul_le_mul_of_nonneg_left
        (by linarith [b9a_abs_cl_le (Nat.cast_nonneg (α := ℝ) n) b]) hM0)
    have hFnb : ∀ n : ℕ, ∃ M', ∀ q, |Fn n q| ≤ M' := fun n =>
      ⟨M * (1 + n), fun q => by
        rw [hFn]
        exact (hM (b9a_cl n q.1) q.2).trans (mul_le_mul_of_nonneg_left
          (by linarith [b9a_abs_cl_le_K (Nat.cast_nonneg (α := ℝ) n) q.1]) hM0)⟩
    -- limit side: dominated convergence
    have hLlim : Tendsto (fun n : ℕ => ∫ ω, Fn n (Qv ω, fun a => Lin a ω) ∂P) atTop
        (𝓝 (∫ ω, F (Qv ω, fun a => Lin a ω) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun ω => M * (1 + |Qv ω|))
        (fun n => ((hFnc n).measurable.comp hT0).aestronglyMeasurable)
        (((integrable_const (1 : ℝ)).add hQvint.abs).const_mul M)
        (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
      · rw [Real.norm_eq_abs]
        exact hFnM n _ _
      · refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨⌈|Qv ω|⌉₊, fun n hn => ?_⟩)
        have : |Qv ω| ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.2 hn)
        show F (Qv ω, fun a => Lin a ω) = Fn n (Qv ω, fun a => Lin a ω)
        rw [hFn, b9a_cl_of_abs_le this]
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n0, hn0⟩ := Metric.tendsto_atTop.1 hLlim (ε / 3) (by positivity)
    have e2 : Tendsto (fun n : ℕ => 4 * M * |CL| * (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
        tendsto_natCast_atTop_atTop)).const_mul (4 * M * |CL|)
      simpa using this
    obtain ⟨n1, hn1⟩ := Metric.tendsto_atTop.1 e2 (ε / 3) (by positivity)
    obtain ⟨n, hn0', hn1', hn1''⟩ : ∃ n : ℕ, n0 ≤ n ∧ n1 ≤ n ∧ 1 ≤ n :=
      ⟨max (max n0 n1) 1, (le_max_left _ _).trans (le_max_left _ _),
        (le_max_right _ _).trans (le_max_left _ _), le_max_right _ _⟩
    have a3 := hn0 n hn0'
    rw [Real.dist_eq] at a3
    have a4 : 4 * M * |CL| * (Real.sqrt n)⁻¹ < ε / 3 := by
      have := hn1 n hn1'
      rw [Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans_lt this
    obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 (hbdd (Fn n) (hFnc n) (hFnb n)) (ε / 3)
      (by positivity)
    refine ⟨max N0 1, fun N hN => ?_⟩
    have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
    have hN0' : N0 ≤ N := (le_max_left _ _).trans hN
    have a2 := hN0 N hN0'
    rw [Real.dist_eq] at a2
    haveI := hQprob N hN1
    haveI : IsProbabilityMeasure (D.Gibbs N) := q08_gibbs_isProb D N hN1
    obtain ⟨hI, hC⟩ := hCL N hN1
    have hK : (1 : ℝ) ≤ n := by exact_mod_cast hn1''
    have hsn : 0 ≤ (Real.sqrt n)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    have a1 : |∫ X, F (q08Stat D N X) ∂(sed_Q d s N β ρ) -
        ∫ X, Fn n (q08Stat D N X) ∂(sed_Q d s N β ρ)| ≤ 4 * M * |CL| * (Real.sqrt n)⁻¹ := by
      rw [← integral_sub (hintG F hFc M hM N hN1) (hintG (Fn n) (hFnc n) M (hFnM n) N hN1),
        ← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le
        (g := fun X => 4 * M * (Real.sqrt n)⁻¹ * |b9a_Bn D N X| ^ (3 / 2 : ℝ))
        (hI.const_mul _) (ae_of_all _ fun X => ?_)).trans ?_
      · rw [Real.norm_eq_abs]
        show |F ((q08Stat D N X).1, (q08Stat D N X).2) -
          Fn n ((q08Stat D N X).1, (q08Stat D N X).2)| ≤ _
        rw [hFn]
        exact b9a_trunc_pt hM hK (q08Stat D N X).1 (q08Stat D N X).2
      · rw [integral_const_mul]
        calc 4 * M * (Real.sqrt n)⁻¹ * ∫ X, |b9a_Bn D N X| ^ (3 / 2 : ℝ) ∂(D.Gibbs N)
            ≤ 4 * M * (Real.sqrt n)⁻¹ * CL :=
              mul_le_mul_of_nonneg_left hC (by positivity)
          _ ≤ 4 * M * (Real.sqrt n)⁻¹ * |CL| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
          _ = 4 * M * |CL| * (Real.sqrt n)⁻¹ := by ring
    rw [Real.dist_eq]
    calc |∫ X, F (q08Stat D N X) ∂(sed_Q d s N β ρ) - ∫ ω, F (Qv ω, fun a => Lin a ω) ∂P|
        ≤ |∫ X, F (q08Stat D N X) ∂(sed_Q d s N β ρ) -
            ∫ X, Fn n (q08Stat D N X) ∂(sed_Q d s N β ρ)| +
          |∫ X, Fn n (q08Stat D N X) ∂(sed_Q d s N β ρ) -
            ∫ ω, Fn n (Qv ω, fun a => Lin a ω) ∂P| +
          |∫ ω, Fn n (Qv ω, fun a => Lin a ω) ∂P - ∫ ω, F (Qv ω, fun a => Lin a ω) ∂P| := by
          have := abs_sub_le (∫ X, F (q08Stat D N X) ∂(sed_Q d s N β ρ))
            (∫ X, Fn n (q08Stat D N X) ∂(sed_Q d s N β ρ))
            (∫ ω, F (Qv ω, fun a => Lin a ω) ∂P)
          have := abs_sub_le (∫ X, Fn n (q08Stat D N X) ∂(sed_Q d s N β ρ))
            (∫ ω, Fn n (Qv ω, fun a => Lin a ω) ∂P) (∫ ω, F (Qv ω, fun a => Lin a ω) ∂P)
          linarith
      _ < ε := by linarith
  exact key

end Main

end HRS.MC.SEdge.B9a

