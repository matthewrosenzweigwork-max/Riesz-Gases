import HRS.PDE.MeanFieldAprioriPhi
import HRS.PDE.MeanFieldAprioriPositive
import HRS.PDE.MeanFieldAprioriUpper
import HRS.PDE.MeanFieldAprioriSobolev

/-!
# A priori bounds for the finite-regularity mean-field equation, packet AP6a
(free energy and dissipation; package MF-01, plan `MeanFieldAprioriPlan.md`, amendment §2.5)

* `freeEnergy`, `dissipation`;
* `hasDerivAt_freeEnergy` : `d/dt F(ρ^t) = -D(ρ^t)` where `ρ^t ≥ δ > 0` (time-local, on `[0,T]`);
* `integral_dissipation_le` : `∫_0^T D ≤ F(ρ⁰) + ‖V‖_∞` for a positive mass-one solution on `[0,T]`.

AP6b (`exists_sup_sub_mean_le`, `exists_lower_of_small_dissipation`, `exists_inf_bound`) is
appended at the end of this file (Sections 6-9).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace HRS.PDE.MFApriori

variable {d : ℕ}

/-- Free energy `F(ρ) = ν ∫ ρ log ρ + ∫ V ρ + ½ ∑ ĝ(k)|ρ̂(k)|²`, **verbatim** from the packet.

**Parsing problem (reported to the orchestrator).**  In Lean/Mathlib the body of `∫ x, f x` is
parsed at precedence 60, so it swallows the following `+`: as printed here the definition is
`ν * ∫ x, (ρ log ρ + ∫ y, (V ρ + ½ ∑ ĝ|ρ̂|²))`, i.e. `ν * (∫ ρ log ρ + ∫ V ρ + ½ ∑ ĝ|ρ̂|²)`
(the torus has total mass one).  This is `ν` times the intended free energy in the last two terms, so
`hasDerivAt_freeEnergy` / `integral_dissipation_le` are *false* for it when `ν ≠ 1`.  The intended
functional is `freeEnergy'` below, for which both statements are proved. -/
def freeEnergy (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (ν : ℝ) (c : Coeff d) : ℝ :=
  ν * ∫ x, toFun c x * Real.log (toFun c x) + ∫ x, V x * toFun c x +
    (1 / 2 : ℝ) * (∑' k, (rieszCoeff d s k : ℂ) * ‖c k‖ ^ 2).re

/-- The intended free energy (corrected parenthesisation of `freeEnergy`):
`F(ρ) = ν ∫ ρ log ρ + ∫ V ρ + ½ ∑ ĝ(k)|ρ̂(k)|²`. -/
def freeEnergy' (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (ν : ℝ) (c : Coeff d) : ℝ :=
  ν * (∫ x, toFun c x * Real.log (toFun c x)) + (∫ x, V x * toFun c x) +
    (1 / 2 : ℝ) * (∑' k, (rieszCoeff d s k : ℂ) * ‖c k‖ ^ 2).re

/-- Dissipation `D(ρ) = ∫ |ν∇ρ + ρ∇W|² / ρ`. -/
def dissipation (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (ν : ℝ) (c : Coeff d) : ℝ :=
  ∫ x, ‖ν • Torus.grad (toFun c) x + toFun c x • Torus.grad (Wpot d s V c) x‖ ^ 2 / toFun c x

/-! ### Section 1: integration by parts against `W = V + g ⋆ ρ` -/

theorem continuous_toFun_mfRhs (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk 2 V)
    (hVK : MemHs K (coeffOf V)) (ν : ℝ) (c : Coeff d) (hc : MemHs K c) (hreal : IsRealCoeff c) :
    Continuous (toFun (mfRhsCoeff d s V ν c)) := by
  obtain ⟨C₂, -, hC₂⟩ := exists_mfPath_isCk (d := d) 2 K (by simpa using hK)
  have hρ2 : Torus.IsCk 2 (toFun c) := (hC₂ c hc hreal).1
  have hρ1 : Torus.IsCk 1 (toFun c) := hρ2.of_le (by norm_num)
  have hW2 := isCk_two_Wpot hd s hs0 hsd K hK V hV c hc hreal
  have hP1 : ∀ j, Torus.IsCk 1 (fun y => toFun c y * Torus.partialDeriv j (Wpot d s V c) y) :=
    fun j => MFAux.isCk_mul_partialDeriv _ _ hρ1 hW2 j
  have hpP : ∀ j, Continuous (Torus.partialDeriv j
      (fun y => toFun c y * Torus.partialDeriv j (Wpot d s V c) y)) :=
    fun j => continuous_partialDeriv j _ (hP1 j)
  have hpp : ∀ j, Continuous (Torus.partialDeriv j (Torus.partialDeriv j (toFun c))) := fun j =>
    continuous_partialDeriv j _ (isCk_one_partialDeriv j _ hρ2)
  have e : toFun (mfRhsCoeff d s V ν c) = fun x =>
      ν * ∑ j, Torus.partialDeriv j (Torus.partialDeriv j (toFun c)) x +
        ∑ j, Torus.partialDeriv j
          (fun y => toFun c y * Torus.partialDeriv j (Wpot d s V c) y) x := by
    funext x
    rw [toFun_mfRhsCoeff_eq' hd s hs0 hsd K hK V hV hVK ν c hc hreal x,
      laplacian_eq_sum _ hρ2 x]
  rw [e]
  exact (continuous_const.mul (continuous_finsetSum _ fun j _ => hpp j)).add
    (continuous_finsetSum _ fun j _ => hpP j)

/-- `∫ W (νΔρ + Div(ρ∇W)) = -ν ∫ ∇ρ·∇W - ∫ ρ |∇W|²`. -/
theorem integral_Wpot_mul_rhs (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk 2 V)
    (hVK : MemHs K (coeffOf V)) (ν : ℝ) (c : Coeff d) (hc : MemHs K c) (hreal : IsRealCoeff c) :
    ∫ x, Wpot d s V c x * toFun (mfRhsCoeff d s V ν c) x =
      -ν * (∫ x, inner ℝ (Torus.grad (toFun c) x) (Torus.grad (Wpot d s V c) x)) -
        ∫ x, toFun c x * ‖Torus.grad (Wpot d s V c) x‖ ^ 2 := by
  obtain ⟨C₂, -, hC₂⟩ := exists_mfPath_isCk (d := d) 2 K (by simpa using hK)
  have hρ2 : Torus.IsCk 2 (toFun c) := (hC₂ c hc hreal).1
  have hρ1 : Torus.IsCk 1 (toFun c) := hρ2.of_le (by norm_num)
  have hW2 := isCk_two_Wpot hd s hs0 hsd K hK V hV c hc hreal
  have hW1 : Torus.IsCk 1 (Wpot d s V c) := hW2.of_le (by norm_num)
  set ρ := toFun c with hρdef
  set W := Wpot d s V c with hWdef
  have hρc : Continuous ρ := continuous_of_isCk' hρ1 le_rfl
  have hWc : Continuous W := continuous_of_isCk' hW1 le_rfl
  have hpρ : ∀ j, Continuous (Torus.partialDeriv j ρ) := fun j => continuous_partialDeriv j _ hρ1
  have hpW : ∀ j, Continuous (Torus.partialDeriv j W) := fun j => continuous_partialDeriv j _ hW1
  have hpρ1 : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j ρ) := fun j => isCk_one_partialDeriv j _ hρ2
  have hP1 : ∀ j, Torus.IsCk 1 (fun y => ρ y * Torus.partialDeriv j W y) := fun j =>
    MFAux.isCk_mul_partialDeriv _ _ hρ1 hW2 j
  have hpP : ∀ j, Continuous (Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y)) :=
    fun j => continuous_partialDeriv j _ (hP1 j)
  have hpp : ∀ j, Continuous (Torus.partialDeriv j (Torus.partialDeriv j ρ)) := fun j =>
    continuous_partialDeriv j _ (hpρ1 j)
  have hlap : ∀ x, Torus.laplacian ρ x = ∑ j, Torus.partialDeriv j (Torus.partialDeriv j ρ) x :=
    fun x => laplacian_eq_sum _ hρ2 x
  have hF : ∀ x, toFun (mfRhsCoeff d s V ν c) x =
      ν * ∑ j, Torus.partialDeriv j (Torus.partialDeriv j ρ) x +
      ∑ j, Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x := by
    intro x
    rw [toFun_mfRhsCoeff_eq' hd s hs0 hsd K hK V hV hVK ν c hc hreal x, hlap x]
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable f := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ibp1 : ∀ j, ∫ x, W x * Torus.partialDeriv j (Torus.partialDeriv j ρ) x =
      -∫ x, Torus.partialDeriv j ρ x * Torus.partialDeriv j W x := by
    intro j
    have := integral_partialDeriv_mul j (Torus.partialDeriv j ρ) W (hpρ1 j) hW1
    have e1 : ∀ x, W x * Torus.partialDeriv j (Torus.partialDeriv j ρ) x =
        Torus.partialDeriv j (Torus.partialDeriv j ρ) x * W x := fun x => mul_comm _ _
    simp_rw [e1, this]
  have ibp2 : ∀ j, ∫ x, W x * Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x =
      -∫ x, ρ x * (Torus.partialDeriv j W x) ^ 2 := by
    intro j
    have := integral_partialDeriv_mul j (fun y => ρ y * Torus.partialDeriv j W y) W (hP1 j) hW1
    have e1 : ∀ x, W x * Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x =
        Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x * W x :=
      fun x => mul_comm _ _
    simp_rw [e1, this]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only; ring
  calc ∫ x, W x * toFun (mfRhsCoeff d s V ν c) x
      = ∫ x, (ν * (∑ j, W x * Torus.partialDeriv j (Torus.partialDeriv j ρ) x) +
          ∑ j, W x * Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hF, mul_add, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ν * (∑ j, ∫ x, W x * Torus.partialDeriv j (Torus.partialDeriv j ρ) x) +
          ∑ j, ∫ x, W x * Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x := by
        have c1 : ∀ j, Continuous fun x => W x * Torus.partialDeriv j (Torus.partialDeriv j ρ) x :=
          fun j => hWc.mul (hpp j)
        have c2 : ∀ j, Continuous fun x => W x *
            Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x :=
          fun j => hWc.mul (hpP j)
        have i1 : Integrable fun x => ν * (∑ j, W x * Torus.partialDeriv j (Torus.partialDeriv j ρ) x) :=
          hint _ (continuous_const.mul (continuous_finsetSum _ fun j _ => c1 j))
        have i2 : Integrable fun x => ∑ j, W x *
            Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x :=
          hint _ (continuous_finsetSum _ fun j _ => c2 j)
        rw [integral_add i1 i2, integral_const_mul, integral_finsetSum _ (fun j _ => hint _ (c1 j)),
          integral_finsetSum _ (fun j _ => hint _ (c2 j))]
    _ = _ := by
        have e1 : ∫ x, inner ℝ (Torus.grad ρ x) (Torus.grad W x) =
            ∑ j, ∫ x, Torus.partialDeriv j ρ x * Torus.partialDeriv j W x := by
          simp_rw [inner_grad_grad]
          exact integral_finsetSum _ (fun j _ => hint _ ((hpρ j).mul (hpW j)))
        have e2 : ∫ x, ρ x * ‖Torus.grad W x‖ ^ 2 =
            ∑ j, ∫ x, ρ x * (Torus.partialDeriv j W x) ^ 2 := by
          simp_rw [norm_grad_sq, Finset.mul_sum]
          exact integral_finsetSum _ (fun j _ => hint _ (hρc.mul ((hpW j).pow 2)))
        rw [e1, e2]
        simp_rw [ibp1, ibp2]
        simp only [Finset.sum_neg_distrib, Finset.mul_sum, mul_neg, neg_mul]
        rw [sub_eq_add_neg]

/-! ### Section 2: the derivative of the free energy -/

/-- `Φ(r) = r log r`. -/
theorem mulLog_facts :
    (∀ r : ℝ, 0 < r → deriv (fun r : ℝ => r * Real.log r) r = Real.log r + 1) ∧
    (∀ r : ℝ, 0 < r → deriv (deriv (fun r : ℝ => r * Real.log r)) r = r⁻¹) := by
  have h1 : ∀ r : ℝ, r ≠ 0 → deriv (fun r : ℝ => r * Real.log r) r = Real.log r + 1 :=
    fun r hr => Real.deriv_mul_log hr
  refine ⟨fun r hr => h1 r hr.ne', fun r hr => ?_⟩
  have hev : deriv (fun r : ℝ => r * Real.log r) =ᶠ[𝓝 r] fun r => Real.log r + 1 := by
    filter_upwards [Ioi_mem_nhds hr] with y hy using h1 y (ne_of_gt hy)
  rw [hev.deriv_eq]
  simp [Real.deriv_log]

theorem contDiffOn_mulLog (δ : ℝ) (hδ : 0 < δ) :
    ContDiffOn ℝ 2 (fun r : ℝ => r * Real.log r) (Ioi (δ / 2)) := by
  refine contDiffOn_id.mul ?_
  refine Real.contDiffOn_log.mono ?_
  intro y hy
  have : 0 < y := lt_trans (by linarith) hy
  simpa using this.ne'

theorem interaction_re_eq (s : ℝ) (c : Coeff d) :
    (∑' k, (rieszCoeff d s k : ℂ) * ‖c k‖ ^ 2).re = ∑' k, rieszCoeff d s k * ‖c k‖ ^ 2 := by
  have : (∑' k, (rieszCoeff d s k : ℂ) * ‖c k‖ ^ 2) =
      ((∑' k, rieszCoeff d s k * ‖c k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun k => ?_
    simp
  rw [this, Complex.ofReal_re]

theorem continuous_norm_grad_sq {u : Torus d → ℝ} (hu : Torus.IsCk 1 u) :
    Continuous fun x => ‖Torus.grad u x‖ ^ 2 := by
  simp_rw [norm_grad_sq]
  exact continuous_finsetSum _ fun j _ => (continuous_partialDeriv j _ hu).pow 2

theorem continuous_inner_grad {u w : Torus d → ℝ} (hu : Torus.IsCk 1 u) (hw : Torus.IsCk 1 w) :
    Continuous fun x => inner ℝ (Torus.grad u x) (Torus.grad w x) := by
  simp_rw [inner_grad_grad]
  exact continuous_finsetSum _ fun j _ =>
    (continuous_partialDeriv j _ hu).mul (continuous_partialDeriv j _ hw)

theorem hasDerivAt_freeEnergy' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolRealOn d s V ν K ρ₀ ρc T) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hbT : b ≤ T) (δ : ℝ) (hδ : 0 < δ)
    (hpos : ∀ t ∈ Set.Icc a b, ∀ x, δ ≤ mfPath ρc t x) {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    HasDerivAt (fun τ => freeEnergy' d s V ν (ρc τ)) (-dissipation d s V ν (ρc t)) t := by
  have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
  have htT : t < T := lt_of_lt_of_le ht.2 hbT
  have htI : t ∈ Icc 0 T := ⟨ht0.le, htT.le⟩
  have hK2 : (d : ℝ) / 2 + 2 < (K : ℝ) := hK
  have hV2 : Torus.IsCk 2 V := hV.of_le (by exact_mod_cast (by omega : 2 ≤ K + 2))
  have hVK : MemHs (K : ℝ) (coeffOf V) := Aux.memHs_of_isCk_nat K V hV
  have hcm : MemHs (K : ℝ) (ρc t) := H.sol.cont.1 t htI
  have hcr : IsRealCoeff (ρc t) := H.real t htI
  -- the three derivatives
  have D1 := hasDerivAt_integral_comp hd s hs0 hsd K hK V ρ₀ hV ν ρc H
    (fun r : ℝ => r * Real.log r) (Ioi (δ / 2)) isOpen_Ioi (contDiffOn_mulLog δ hδ) ha hab hbT
    (fun τ hτ x => by
      show δ / 2 < mfPath ρc τ x
      linarith [hpos τ hτ x]) ht
  have D2 := hasDerivAt_integral_V hd s hs0 hsd K hK V ρ₀ hV ν ρc H ⟨ht0, htT⟩
  have D3 := hasDerivAt_interaction hd s hs0 hsd K hK V ρ₀ hV ν ρc H ⟨ht0, htT⟩
  have Dsum := ((D1.const_mul ν).add D2).add D3
  -- evaluate the derivative
  suffices key : -dissipation d s V ν (ρc t) =
      ν * (∫ x, deriv (fun r : ℝ => r * Real.log r) (mfPath ρc t x) *
        toFun (mfRhsCoeff d s V ν (ρc t)) x) +
      (∫ x, V x * toFun (mfRhsCoeff d s V ν (ρc t)) x) +
      ∫ x, riesz d s (ρc t) x * toFun (mfRhsCoeff d s V ν (ρc t)) x by
    rw [key]; exact Dsum
  have hRc : Continuous (toFun (mfRhsCoeff d s V ν (ρc t))) :=
    continuous_toFun_mfRhs hd s hs0 hsd K hK2 V hV2 hVK ν (ρc t) hcm hcr
  have hA := integral_deriv_mul_rhs' hd s hs0 hsd K hK2 V hV2 hVK ν (ρc t) hcm hcr
    (fun r : ℝ => r * Real.log r) (Ioi (δ / 2)) isOpen_Ioi (contDiffOn_mulLog δ hδ)
    (fun x => by
      show δ / 2 < mfPath ρc t x
      linarith [hpos t ⟨ht.1.le, ht.2.le⟩ x])
  have hBC := integral_Wpot_mul_rhs hd s hs0 hsd K hK2 V hV2 hVK ν (ρc t) hcm hcr
  set c := ρc t with hcdef
  set ρ := toFun c with hρdef
  set W := Wpot d s V c with hWdef
  have hρpos : ∀ x, δ ≤ ρ x := fun x => hpos t ⟨ht.1.le, ht.2.le⟩ x
  have hρpos' : ∀ x, 0 < ρ x := fun x => lt_of_lt_of_le hδ (hρpos x)
  obtain ⟨C₂, -, hC₂⟩ := exists_mfPath_isCk (d := d) 2 K (by simpa using hK)
  have hρ2 : Torus.IsCk 2 ρ := (hC₂ c hcm hcr).1
  have hρ1 : Torus.IsCk 1 ρ := hρ2.of_le (by norm_num)
  have hW2 := isCk_two_Wpot hd s hs0 hsd K hK2 V hV2 c hcm hcr
  have hW1 : Torus.IsCk 1 W := hW2.of_le (by norm_num)
  have hρc : Continuous ρ := continuous_of_isCk' hρ1 le_rfl
  have hWc : Continuous W := continuous_of_isCk' hW1 le_rfl
  have hV1 : Torus.IsCk 1 V := hV2.of_le (by norm_num)
  have hVc : Continuous V := continuous_of_isCk' hV1 le_rfl
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable f := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hrieszc : Continuous (riesz d s c) := by
    have : riesz d s c = fun x => W x - V x := by
      funext x; simp [hWdef, Wpot]
    rw [this]; exact hWc.sub hVc
  -- A: derivative of the entropy
  obtain ⟨hΦ1, hΦ2⟩ := mulLog_facts
  have hA' : ∫ x, deriv (fun r : ℝ => r * Real.log r) (mfPath ρc t x) *
        toFun (mfRhsCoeff d s V ν (ρc t)) x =
      -ν * (∫ x, (ρ x)⁻¹ * ‖Torus.grad ρ x‖ ^ 2) -
        ∫ x, inner ℝ (Torus.grad ρ x) (Torus.grad W x) := by
    have e1 : ∀ x, deriv (fun r : ℝ => r * Real.log r) (mfPath ρc t x) = Real.log (ρ x) + 1 :=
      fun x => hΦ1 _ (hρpos' x)
    have e2 : ∀ x, deriv (deriv (fun r : ℝ => r * Real.log r)) (ρ x) = (ρ x)⁻¹ :=
      fun x => hΦ2 _ (hρpos' x)
    have hA2 := hA
    simp_rw [e2] at hA2
    have e3 : ∀ x, deriv (fun r : ℝ => r * Real.log r) (ρ x) = Real.log (ρ x) + 1 :=
      fun x => hΦ1 _ (hρpos' x)
    simp_rw [e3] at hA2
    simp_rw [e1]
    rw [hA2]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have := (hρpos' x).ne'
    simp only; field_simp
  have hBC' : (∫ x, V x * toFun (mfRhsCoeff d s V ν (ρc t)) x) +
      ∫ x, riesz d s (ρc t) x * toFun (mfRhsCoeff d s V ν (ρc t)) x =
      ∫ x, W x * toFun (mfRhsCoeff d s V ν c) x := by
    rw [← integral_add (f := fun x => V x * toFun (mfRhsCoeff d s V ν (ρc t)) x)
      (g := fun x => riesz d s (ρc t) x * toFun (mfRhsCoeff d s V ν (ρc t)) x)
      (hint _ (hVc.mul hRc)) (hint _ (hrieszc.mul hRc))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hWdef, Wpot]; ring
  -- the dissipation
  have hDeq : ∀ x, ‖ν • Torus.grad ρ x + ρ x • Torus.grad W x‖ ^ 2 / ρ x =
      ν ^ 2 * ((ρ x)⁻¹ * ‖Torus.grad ρ x‖ ^ 2) +
        2 * ν * inner ℝ (Torus.grad ρ x) (Torus.grad W x) + ρ x * ‖Torus.grad W x‖ ^ 2 := by
    intro x
    have hne := (hρpos' x).ne'
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
    field_simp
  have c1 : Continuous fun x => (ρ x)⁻¹ * ‖Torus.grad ρ x‖ ^ 2 :=
    (hρc.inv₀ fun x => (hρpos' x).ne').mul (continuous_norm_grad_sq hρ1)
  have c2 : Continuous fun x => inner ℝ (Torus.grad ρ x) (Torus.grad W x) :=
    continuous_inner_grad hρ1 hW1
  have c3 : Continuous fun x => ρ x * ‖Torus.grad W x‖ ^ 2 :=
    hρc.mul (continuous_norm_grad_sq hW1)
  have hD : dissipation d s V ν c = ν ^ 2 * (∫ x, (ρ x)⁻¹ * ‖Torus.grad ρ x‖ ^ 2) +
      2 * ν * (∫ x, inner ℝ (Torus.grad ρ x) (Torus.grad W x)) +
      ∫ x, ρ x * ‖Torus.grad W x‖ ^ 2 := by
    have h0 : dissipation d s V ν c = ∫ x, (ν ^ 2 * ((ρ x)⁻¹ * ‖Torus.grad ρ x‖ ^ 2) +
        2 * ν * inner ℝ (Torus.grad ρ x) (Torus.grad W x) + ρ x * ‖Torus.grad W x‖ ^ 2) := by
      unfold dissipation
      exact integral_congr_ae (Eventually.of_forall hDeq)
    have i1 : Integrable fun x => ν ^ 2 * ((ρ x)⁻¹ * ‖Torus.grad ρ x‖ ^ 2) := (hint _ c1).const_mul _
    have i2 : Integrable fun x => 2 * ν * inner ℝ (Torus.grad ρ x) (Torus.grad W x) :=
      (hint _ c2).const_mul _
    have i3 : Integrable fun x => ρ x * ‖Torus.grad W x‖ ^ 2 := hint _ c3
    have i12 : Integrable fun x => ν ^ 2 * ((ρ x)⁻¹ * ‖Torus.grad ρ x‖ ^ 2) +
        2 * ν * inner ℝ (Torus.grad ρ x) (Torus.grad W x) := i1.add i2
    rw [h0, integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul]
  have hBC2 := hBC'
  rw [hBC] at hBC2
  rw [hD, hA']
  linear_combination (-1 : ℝ) * hBC2
/-! ### Section 3: lower bound and continuity of the free energy -/

theorem coeffOf_zero_eq_integral' (φ : Torus d → ℝ) : coeffOf φ 0 = ((∫ x, φ x : ℝ) : ℂ) := by
  unfold coeffOf
  rw [funFourierCoeff_eq_int, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [UnitAddTorus.mFourier_zero]

/-- For a real mass-one `H^K` coefficient sequence, `∫ toFun c = 1`. -/
theorem integral_toFun_eq_one (K : ℝ) (hK : (d : ℝ) / 2 < K) (c : Coeff d) (hc : MemHs K c)
    (hreal : IsRealCoeff c) (h0 : c 0 = 1) : ∫ x, toFun c x = 1 := by
  have hs : Summable fun k => ‖c k‖ := summable_norm_of_memHs K hK c hc
  have h1 := coeffOf_zero_eq_integral' (toFun c)
  rw [coeffOf_toFun c hreal hs, h0] at h1
  exact_mod_cast h1.symm

theorem interaction_nonneg (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (c : Coeff d) :
    0 ≤ (∑' k, (rieszCoeff d s k : ℂ) * ‖c k‖ ^ 2).re := by
  rw [interaction_re_eq]
  exact tsum_nonneg fun k => mul_nonneg (rieszCoeff_nonneg hd hs0 hsd k) (sq_nonneg _)

/-- The free energy of a positive mass-one density is `≥ -‖V‖_∞` (`ν ≥ 0`). -/
theorem freeEnergy'_ge (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 < K) (V : Torus d → ℝ) (hVc : Continuous V) (ν : ℝ) (hν : 0 ≤ ν)
    (c : Coeff d) (hc : MemHs K c) (hreal : IsRealCoeff c) (hpos : ∀ x, 0 < toFun c x)
    (h0 : c 0 = 1) : -Torus.supNorm V ≤ freeEnergy' d s V ν c := by
  have hs : Summable fun k => ‖c k‖ := summable_norm_of_memHs K hK c hc
  have hρc : Continuous (toFun c) := HRS.PDE.MFProduct.continuous_toFun c hs
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable f := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmass := integral_toFun_eq_one K hK c hc hreal h0
  -- entropy
  have hent : 0 ≤ ∫ x, toFun c x * Real.log (toFun c x) := by
    have h1 : ∀ x, toFun c x - 1 ≤ toFun c x * Real.log (toFun c x) := fun x => by
      have := Real.one_sub_inv_le_log_of_pos (hpos x)
      have h2 := mul_le_mul_of_nonneg_left this (hpos x).le
      have h3 : toFun c x * (1 - (toFun c x)⁻¹) = toFun c x - 1 := by
        rw [mul_sub, mul_one, mul_inv_cancel₀ (hpos x).ne']
      linarith
    have hmono : ∫ x, (toFun c x - 1) ≤ ∫ x, toFun c x * Real.log (toFun c x) :=
      integral_mono (hint _ (hρc.sub continuous_const))
        (hint _ (hρc.mul (hρc.log fun x => (hpos x).ne')))
        h1
    have hz : ∫ x, (toFun c x - 1) = 0 := by
      rw [integral_sub (hint _ hρc) (integrable_const _), hmass]
      simp
    linarith
  -- potential
  have hpot : -Torus.supNorm V ≤ ∫ x, V x * toFun c x := by
    have hmono : ∫ x, (-Torus.supNorm V) * toFun c x ≤ ∫ x, V x * toFun c x := by
      refine integral_mono (hint _ (continuous_const.mul hρc)) (hint _ (hVc.mul hρc)) fun x => ?_
      have := norm_le_supNorm hVc x
      rw [Real.norm_eq_abs] at this
      have h1 : -Torus.supNorm V ≤ V x := by linarith [neg_abs_le (V x)]
      exact mul_le_mul_of_nonneg_right h1 (hpos x).le
    rw [integral_const_mul, hmass] at hmono
    linarith
  have hint0 := interaction_nonneg hd s hs0 hsd c
  unfold freeEnergy'
  nlinarith [mul_nonneg hν hent]
/-- Continuity of the interaction energy along a path continuous into `H^K`, `K > d/2`. -/
theorem continuousOn_interaction (s : ℝ) (hsd : s < d) (K : ℝ) (hK : (d : ℝ) / 2 < K)
    (ρc : ℝ → Coeff d) (T : ℝ) (h : ContinuousInHsOn K ρc (Icc 0 T)) :
    ContinuousOn (fun τ => (1 / 2 : ℝ) * (∑' k, (rieszCoeff d s k : ℂ) * ‖ρc τ k‖ ^ 2).re)
      (Icc 0 T) := by
  obtain ⟨B, hB⟩ := exists_bound_of_continuousInHsOn_Icc K ρc T h
  set Rc : ℝ := |rieszConst d s| with hRc
  have hus : Summable fun k : Lattice d => Rc * (B ^ 2 * sobWeight (-K) k) :=
    ((summable_sobWeight_neg K hK).mul_left (B ^ 2)).mul_left Rc
  simp_rw [interaction_re_eq]
  refine continuousOn_const.mul ?_
  refine continuousOn_tsum (u := fun k : Lattice d => Rc * (B ^ 2 * sobWeight (-K) k))
    (fun k => ?_) hus (fun k τ hτ => ?_)
  · exact continuousOn_const.mul ((Aux.continuousOn_mode h k).norm.pow 2)
  · have hw : 0 < sobWeight K k := sobWeight_pos _ k
    have h1 : ‖ρc τ k‖ * Real.sqrt (sobWeight K k) ≤ B :=
      (Aux.norm_coeff_mul_sqrt_le K (h.1 τ hτ) k).trans (hB τ hτ)
    have h0 : 0 ≤ ‖ρc τ k‖ * Real.sqrt (sobWeight K k) := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    have h2 : ‖ρc τ k‖ ^ 2 * sobWeight K k ≤ B ^ 2 := by
      have := pow_le_pow_left₀ h0 h1 2
      rw [mul_pow, Real.sq_sqrt hw.le] at this
      exact this
    have hneg : sobWeight (-K) k = (sobWeight K k)⁻¹ := by
      unfold sobWeight
      rw [Real.rpow_neg (by positivity)]
    have h3 : ‖ρc τ k‖ ^ 2 ≤ B ^ 2 * sobWeight (-K) k := by
      rw [hneg, ← div_eq_mul_inv, le_div_iff₀ hw]
      exact h2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖ρc τ k‖)]
    exact mul_le_mul (abs_rieszCoeff_leU hsd k) h3 (sq_nonneg _) (abs_nonneg _)

/-- Continuity of the free energy along a real solution on `[0,T]` with positive density. -/
theorem continuousOn_freeEnergy' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolRealOn d s V ν K ρ₀ ρc T) :
    ContinuousOn (fun τ => freeEnergy' d s V ν (ρc τ)) (Icc 0 T) := by
  obtain ⟨h1, -⟩ := continuousOn_mfPath_prod_on hd s hs0 hsd K hK V ρ₀ hV ν ρc H
  have hV1 : Torus.IsCk 1 V := hV.of_le (by exact_mod_cast (by omega : 1 ≤ K + 2))
  have hVc : Continuous V := continuous_of_isCk' hV1 le_rfl
  have hk : IsCompact (univ : Set (Torus d)) := isCompact_univ
  have A : ContinuousOn (fun τ => ∫ x, mfPath ρc τ x * Real.log (mfPath ρc τ x)) (Icc 0 T) := by
    refine continuousOn_integral_of_compact_support (f := fun τ x => mfPath ρc τ x *
      Real.log (mfPath ρc τ x)) hk ?_ (fun p x _ hx => absurd (mem_univ x) hx)
    exact Real.continuous_mul_log.comp_continuousOn h1
  have B : ContinuousOn (fun τ => ∫ x, V x * mfPath ρc τ x) (Icc 0 T) := by
    refine continuousOn_integral_of_compact_support (f := fun τ x => V x * mfPath ρc τ x) hk ?_
      (fun p x _ hx => absurd (mem_univ x) hx)
    exact (hVc.comp_continuousOn continuous_snd.continuousOn).mul h1
  have C := continuousOn_interaction s hsd K (by linarith) ρc T H.sol.cont
  exact (A.const_smul ν |>.add B |>.add C : _)
/-! ### Section 4: the integrated dissipation bound -/

/-- Integrated dissipation bound for the intended free energy `freeEnergy'`:
`∫_0^T D ≤ F(ρ⁰) + ‖V‖_∞`, for a positive mass-one real solution on `[0,T]`. -/
theorem integral_dissipation_le' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (hν : 0 < ν) (ρc : ℝ → Coeff d) {T : ℝ} (hT : 0 ≤ T) (H : MFSolRealOn d s V ν K ρ₀ ρc T)
    (hpos : ∀ t ∈ Set.Icc 0 T, ∀ x, 0 < mfPath ρc t x) (hmass : ∀ t ∈ Set.Icc 0 T, ρc t 0 = 1) :
    ∫ t in (0 : ℝ)..T, dissipation d s V ν (ρc t) ≤
      freeEnergy' d s V ν (ρc 0) + Torus.supNorm V := by
  have hV1 : Torus.IsCk 1 V := hV.of_le (by exact_mod_cast (by omega : 1 ≤ K + 2))
  have hVc : Continuous V := continuous_of_isCk' hV1 le_rfl
  have hKd : (d : ℝ) / 2 < (K : ℝ) := by linarith
  have lower : ∀ t ∈ Icc 0 T, -Torus.supNorm V ≤ freeEnergy' d s V ν (ρc t) := fun t ht =>
    freeEnergy'_ge hd s hs0 hsd K hKd V hVc ν hν.le (ρc t) (H.sol.cont.1 t ht) (H.real t ht)
      (hpos t ht) (hmass t ht)
  rcases hT.eq_or_lt with rfl | hT'
  · have := lower 0 ⟨le_rfl, le_rfl⟩
    simp only [intervalIntegral.integral_same]
    linarith
  · obtain ⟨h1, -⟩ := continuousOn_mfPath_prod_on hd s hs0 hsd K hK V ρ₀ hV ν ρc H
    have hcpt : IsCompact (Icc 0 T ×ˢ (univ : Set (Torus d))) := isCompact_Icc.prod isCompact_univ
    obtain ⟨δ, hδ, hδle⟩ := hcpt.exists_forall_le' (a := 0) h1
      (fun p hp => hpos p.1 hp.1 p.2)
    have hposδ : ∀ t ∈ Icc 0 T, ∀ x, δ ≤ mfPath ρc t x := fun t ht x =>
      hδle (t, x) ⟨ht, mem_univ _⟩
    have hcont : ContinuousOn (fun τ => -freeEnergy' d s V ν (ρc τ)) (uIcc 0 T) := by
      rw [uIcc_of_le hT]
      exact (continuousOn_freeEnergy' hd s hs0 hsd K hK V ρ₀ hV ν ρc H).neg
    have hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt (fun τ => -freeEnergy' d s V ν (ρc τ))
        (dissipation d s V ν (ρc t)) t := fun t ht => by
      have := (hasDerivAt_freeEnergy' hd s hs0 hsd K hK V ρ₀ hV ν ρc H le_rfl hT' le_rfl δ hδ
        hposδ ht).fun_neg
      rwa [neg_neg] at this
    have hD0 : ∀ t ∈ Ioo 0 T, 0 ≤ dissipation d s V ν (ρc t) := fun t ht =>
      integral_nonneg fun x => div_nonneg (sq_nonneg _) (hpos t ⟨ht.1.le, ht.2.le⟩ x).le
    have hint : IntervalIntegrable (fun t => dissipation d s V ν (ρc t)) volume 0 T :=
      intervalIntegral.intervalIntegrable_deriv_of_nonneg hcont
        (by rw [min_eq_left hT, max_eq_right hT]; exact hderiv) (by
          rw [min_eq_left hT, max_eq_right hT]; exact hD0)
    have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT
      (hcont.mono (by rw [uIcc_of_le hT])) (fun x hx => (hderiv x hx).hasDerivWithinAt) hint
    have hlowT := lower T ⟨hT, le_rfl⟩
    rw [key]
    linarith
/-! ### Section 5: relation between the verbatim `freeEnergy` and the intended `freeEnergy'` -/

/-- The verbatim `freeEnergy` (whose first integral swallows the two following summands) is
`ν * (∫ ρ log ρ + ∫ V ρ + ½ ∑ ĝ|ρ̂|²)`, for `ρ̂ ∈ H^K`, `K > d/2`, `V` continuous. -/
theorem freeEnergy_eq_mul (s : ℝ) (K : ℝ) (hK : (d : ℝ) / 2 < K) (V : Torus d → ℝ)
    (hVc : Continuous V) (ν : ℝ) (c : Coeff d) (hc : MemHs K c) :
    freeEnergy d s V ν c = ν * ((∫ x, toFun c x * Real.log (toFun c x)) + (∫ x, V x * toFun c x) +
      (1 / 2 : ℝ) * (∑' k, (rieszCoeff d s k : ℂ) * ‖c k‖ ^ 2).re) := by
  have hs : Summable fun k => ‖c k‖ := summable_norm_of_memHs K hK c hc
  have hρc : Continuous (toFun c) := HRS.PDE.MFProduct.continuous_toFun c hs
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable f := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i1 : Integrable fun x => V x * toFun c x := hint _ (hVc.mul hρc)
  have i0 : Integrable fun x => toFun c x * Real.log (toFun c x) :=
    hint _ (Real.continuous_mul_log.comp hρc)
  set S0 : ℝ := (1 / 2 : ℝ) * (∑' k, (rieszCoeff d s k : ℂ) * ‖c k‖ ^ 2).re with hS0
  have e2 : (∫ y, (V y * toFun c y + S0)) = (∫ y, V y * toFun c y) + S0 := by
    rw [integral_add i1 (integrable_const _)]
    simp
  have e1 : (∫ x, (toFun c x * Real.log (toFun c x) + (∫ y, (V y * toFun c y + S0)))) =
      (∫ x, toFun c x * Real.log (toFun c x)) + ((∫ y, V y * toFun c y) + S0) := by
    rw [e2, integral_add i0 (integrable_const _)]
    simp
  show ν * (∫ x, (toFun c x * Real.log (toFun c x) + (∫ y, (V y * toFun c y + S0)))) = _
  rw [e1]
  ring

/-! ### Note on the packet statements

The packet statements `hasDerivAt_freeEnergy` and `integral_dissipation_le` are stated for the
verbatim `freeEnergy`, which is mis-parsed (see its docstring and `freeEnergy_eq_mul`), and are
false for it when `ν ≠ 1`.  They are proved here for the intended functional as
`hasDerivAt_freeEnergy'` and `integral_dissipation_le'` (statements otherwise exactly the amended
ones).  If `freeEnergy` is re-defined with the parentheses of `freeEnergy'`, the packet names are
`hasDerivAt_freeEnergy := hasDerivAt_freeEnergy'` etc. -/

/-! ========================= AP6b goes below ========================= -/
-- (the namespace `HRS.PDE.MFApriori` and the `noncomputable section` are deliberately left open
-- at the end of this file; AP6b appends its declarations here and then `end HRS.PDE.MFApriori`)

/-! ### Section 6 (AP6b): sup-norm control by the `L²` oscillation (box lemma) -/

/-- The coordinate distance on the torus is the absolute value of the centred representative. -/
theorem norm_coord_eq_abs_centeredRep (z : Torus d) (i : Fin d) :
    ‖z i‖ = |Torus.centeredRep z i| := by
  have h := congrFun (R2Aux.mk_centeredRep z) i
  have hc := Kern.abs_centeredRep_le z i
  have : ‖((Torus.centeredRep z i : ℝ) : UnitAddCircle)‖ = |Torus.centeredRep z i| := by
    rw [AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero]
    simpa using hc
  rw [← this, ← h]
  rfl

/-- Lipschitz bound on coordinate boxes. -/
theorem abs_sub_le_of_coord_le {u : Torus d → ℝ} (hu : Torus.IsCk 1 u) {L : ℝ}
    (hL : Torus.cbNorm 1 u ≤ L) (x y : Torus d) {r : ℝ} (h : ∀ i, ‖x i - y i‖ ≤ r) :
    |u x - u y| ≤ L * (d * r) := by
  have h1 := R2Aux.isLipschitz_of_cbNorm hu x y
  have h2 : Torus.tdist x y ≤ d * r := by
    unfold Torus.tdist
    refine (norm_euc_le_sum _).trans ?_
    calc ∑ j, |(Torus.centeredRep (x - y)).ofLp j| = ∑ j : Fin d, ‖(x - y) j‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_coord_eq_abs_centeredRep]
      _ ≤ ∑ _j : Fin d, r := Finset.sum_le_sum fun j _ => h j
      _ = d * r := by simp
  have h3 : 0 ≤ Torus.cbNorm 1 u := R2Aux.cbNorm_nonneg' 1 u
  calc |u x - u y| ≤ Torus.cbNorm 1 u * Torus.tdist x y := h1
    _ ≤ L * (d * r) := mul_le_mul hL h2 (norm_nonneg _) (h3.trans hL)

/-- The volume of a coordinate box of radius `r ≤ 1/2`. -/
theorem volume_box (x₀ : Torus d) {r : ℝ} (hr : r ≤ 1 / 2) :
    volume {x : Torus d | ∀ i, ‖x i - x₀ i‖ ≤ r} = ENNReal.ofReal (2 * r) ^ d := by
  have e : {x : Torus d | ∀ i, ‖x i - x₀ i‖ ≤ r} =
      Set.pi Set.univ (fun i => Metric.closedBall (x₀ i) r) := by
    ext x
    simp [Set.mem_pi, dist_eq_norm]
  rw [e, volume_pi, Measure.pi_pi]
  have : ∀ i : Fin d, volume (Metric.closedBall (x₀ i) r) = ENNReal.ofReal (2 * r) := by
    intro i
    rw [AddCircle.volume_closedBall (1 : ℝ) r, min_eq_right (by linarith)]
  simp_rw [this]
  simp

theorem measurableSet_box (x₀ : Torus d) (r : ℝ) :
    MeasurableSet {x : Torus d | ∀ i, ‖x i - x₀ i‖ ≤ r} := by
  have e : {x : Torus d | ∀ i, ‖x i - x₀ i‖ ≤ r} =
      Set.pi Set.univ (fun i => Metric.closedBall (x₀ i) r) := by
    ext x
    simp [Set.mem_pi, dist_eq_norm]
  rw [e]
  exact MeasurableSet.univ_pi fun i => Metric.isClosed_closedBall.measurableSet

theorem box_le_integral {u : Torus d → ℝ} (hu : Continuous u) (m : ℝ) (x₀ : Torus d) {r a : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (ha : 0 ≤ a)
    (hB : ∀ x : Torus d, (∀ i, ‖x i - x₀ i‖ ≤ r) → a ≤ |u x - m|) :
    a ^ 2 * (2 * r) ^ d ≤ ∫ x, (u x - m) ^ 2 := by
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable f := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc : Continuous fun x => (u x - m) ^ 2 := (hu.sub continuous_const).pow 2
  set B : Set (Torus d) := {x : Torus d | ∀ i, ‖x i - x₀ i‖ ≤ r} with hBdef
  have hBm : MeasurableSet B := measurableSet_box x₀ r
  have h1 : ∫ x in B, (u x - m) ^ 2 ≤ ∫ x, (u x - m) ^ 2 :=
    setIntegral_le_integral (hint _ hc) (Eventually.of_forall fun x => sq_nonneg _)
  have h2 : ∫ x in B, a ^ 2 ≤ ∫ x in B, (u x - m) ^ 2 := by
    refine setIntegral_mono_on (integrableOn_const (measure_ne_top _ _))
      (hint _ hc).integrableOn hBm fun x hx => ?_
    have := hB x hx
    calc a ^ 2 ≤ |u x - m| ^ 2 := pow_le_pow_left₀ ha this 2
      _ = (u x - m) ^ 2 := sq_abs _
  have h3 : ∫ x in B, a ^ 2 = a ^ 2 * (2 * r) ^ d := by
    rw [setIntegral_const, smul_eq_mul, Measure.real, hBdef, volume_box x₀ hr, mul_comm]
    congr 1
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith)]
  linarith

theorem exists_sup_sub_mean_le (hd : 1 ≤ d) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Torus d → ℝ, Torus.IsCk 1 u → Torus.cbNorm 1 u ≤ L →
      ∀ η : ℝ, 0 ≤ η → (∫ x, (u x - ∫ y, u y) ^ 2) ≤ η ^ 2 →
        ∀ x, |u x - ∫ y, u y| ≤ C * (η + η ^ (2 / ((d : ℝ) + 2))) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by linarith
  set L' : ℝ := L + 1 with hL'
  have hL'pos : 0 < L' := by linarith
  set D : ℝ := (d : ℝ) with hD
  set p : ℝ := 2 / ((d : ℝ) + 2) with hp
  set C₁ : ℝ := (4 * (L' * D) ^ d) ^ (1 / ((d : ℝ) + 2)) with hC₁
  have hC₁0 : 0 ≤ C₁ := Real.rpow_nonneg (by positivity) _
  refine ⟨max C₁ 2, le_trans hC₁0 (le_max_left _ _), ?_⟩
  intro u hu hcb η hη hint x₀
  set m := ∫ y, u y with hm
  have huc : Continuous u := continuous_of_isCk' hu le_rfl
  have hpow : 0 ≤ η ^ p := Real.rpow_nonneg hη _
  have hRHS : 0 ≤ max C₁ 2 * (η + η ^ p) :=
    mul_nonneg (hC₁0.trans (le_max_left _ _)) (add_nonneg hη hpow)
  by_cases hδ : |u x₀ - m| = 0
  · rw [hδ]; exact hRHS
  have hδpos : 0 < |u x₀ - m| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hδ)
  set δ := |u x₀ - m| with hδdef
  set r₁ : ℝ := δ / (2 * L' * D) with hr₁def
  have hr₁ : 0 < r₁ := by positivity
  set r := min r₁ (1 / 2) with hrdef
  have hr0 : 0 < r := lt_min hr₁ (by norm_num)
  have hr12 : r ≤ 1 / 2 := min_le_right _ _
  have hBox : ∀ x : Torus d, (∀ i, ‖x i - x₀ i‖ ≤ r) → δ / 2 ≤ |u x - m| := by
    intro x hx
    have h1 := abs_sub_le_of_coord_le hu hcb x x₀ hx
    have h2 : L * (D * r) ≤ δ / 2 := by
      calc L * (D * r) ≤ L' * (D * r₁) := by
            apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left (min_le_left _ _) hdpos.le)
              (by positivity) hL'pos.le
        _ = δ / 2 := by rw [hr₁def]; field_simp
    have h3 : δ ≤ |u x - m| + |u x - u x₀| := by
      have : u x₀ - m = (u x - m) - (u x - u x₀) := by ring
      rw [hδdef, this]
      exact abs_sub _ _
    linarith
  have hkey := box_le_integral huc m x₀ hr0.le hr12 (by positivity : 0 ≤ δ / 2) hBox
  have hkey2 : (δ / 2) ^ 2 * (2 * r) ^ d ≤ η ^ 2 := hkey.trans hint
  have hfinal : δ ≤ C₁ * η ^ p → δ ≤ max C₁ 2 * (η + η ^ p) := by
    intro h
    calc δ ≤ C₁ * η ^ p := h
      _ ≤ max C₁ 2 * η ^ p := mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
      _ ≤ max C₁ 2 * (η + η ^ p) :=
          mul_le_mul_of_nonneg_left (by linarith) (hC₁0.trans (le_max_left _ _))
  by_cases hcase : r₁ ≤ 1 / 2
  · have hrr : r = r₁ := min_eq_left hcase
    have h2r : 2 * r = δ / (L' * D) := by rw [hrr, hr₁def]; field_simp
    have hpoly : δ ^ (d + 2) ≤ 4 * (L' * D) ^ d * η ^ 2 := by
      have e : (δ / 2) ^ 2 * (2 * r) ^ d = δ ^ (d + 2) / (4 * (L' * D) ^ d) := by
        rw [h2r]
        simp only [div_pow, pow_add]
        field_simp
        ring
      rw [e, div_le_iff₀ (by positivity)] at hkey2
      linarith
    apply hfinal
    have hexp : (0 : ℝ) ≤ 1 / ((d : ℝ) + 2) := by positivity
    have e1 : δ = (δ ^ (d + 2)) ^ (1 / ((d : ℝ) + 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδpos.le]
      have : ((d + 2 : ℕ) : ℝ) * (1 / ((d : ℝ) + 2)) = 1 := by
        push_cast; field_simp
      rw [this, Real.rpow_one]
    have e2 : (η ^ 2) ^ (1 / ((d : ℝ) + 2)) = η ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hη, hp]
      congr 1
      push_cast
      ring
    calc δ = (δ ^ (d + 2)) ^ (1 / ((d : ℝ) + 2)) := e1
      _ ≤ (4 * (L' * D) ^ d * η ^ 2) ^ (1 / ((d : ℝ) + 2)) :=
          Real.rpow_le_rpow (by positivity) hpoly hexp
      _ = C₁ * η ^ p := by
          rw [Real.mul_rpow (by positivity) (by positivity), e2]
  · push Not at hcase
    have hrr : r = 1 / 2 := min_eq_right hcase.le
    rw [hrr] at hkey2
    have : (δ / 2) ^ 2 ≤ η ^ 2 := by
      have h := hkey2
      norm_num at h
      exact h
    have hle : δ / 2 ≤ η := by
      by_contra hcon
      push Not at hcon
      nlinarith
    calc δ ≤ 2 * η := by linarith
      _ ≤ max C₁ 2 * η := mul_le_mul_of_nonneg_right (le_max_right _ _) hη
      _ ≤ max C₁ 2 * (η + η ^ p) :=
          mul_le_mul_of_nonneg_left (by linarith) (hC₁0.trans (le_max_left _ _))

/-! ### Section 7 (AP6b): the Poincaré inequality on the torus -/

theorem memHs_zero_coeffOf_continuous {g : Torus d → ℝ} (hg : Continuous g) :
    MemHs 0 (coeffOf g) := by
  have hm : MemLp (fun x => (g x : ℂ)) 2 volume :=
    memLp_two_of_continuous (Complex.continuous_ofReal.comp hg)
  exact (hsNormSq_zero_coeffOfC _ hm).1

/-- Poincaré inequality `‖u - ū‖₂² ≤ (4π²)⁻¹ ‖∇u‖₂²` for `C¹` functions on the torus. -/
theorem poincare_sq {u : Torus d → ℝ} (hu : Torus.IsCk 1 u) :
    ∫ x, (u x - ∫ y, u y) ^ 2 ≤ (4 * Real.pi ^ 2)⁻¹ * ∫ x, ‖Torus.grad u x‖ ^ 2 := by
  have huc : Continuous u := continuous_of_isCk' hu le_rfl
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable f := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set m : ℝ := ∫ y, u y with hm
  -- ∫ (u - m)² = ∫ u² - m²
  have h1 : ∫ x, (u x - m) ^ 2 = (∫ x, u x ^ 2) - m ^ 2 := by
    have e : ∀ x, (u x - m) ^ 2 = u x ^ 2 - 2 * m * u x + m ^ 2 := fun x => by ring
    have i1 : Integrable fun x => u x ^ 2 := hint _ (huc.pow 2)
    have i2 : Integrable fun x => 2 * m * u x := (hint _ huc).const_mul _
    simp_rw [e]
    rw [integral_add (f := fun x => u x ^ 2 - 2 * m * u x) (g := fun _ => m ^ 2) (i1.sub i2)
      (integrable_const _), integral_sub i1 i2, integral_const_mul]
    simp [hm]
    ring
  -- Parseval
  have hP : ∫ x, u x ^ 2 = ∑' k, ‖coeffOf u k‖ ^ 2 := by
    rw [← parseval_real huc, hsNormSq_zero]
  have hSum : Summable fun k => ‖coeffOf u k‖ ^ 2 :=
    (memHs_zero_iffC _).1 (memHs_zero_coeffOf_continuous huc)
  have h0 : ‖coeffOf u 0‖ ^ 2 = m ^ 2 := by
    rw [coeffOf_zero_eq_integral', Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h2 : (∫ x, u x ^ 2) - m ^ 2 =
      ∑' k, (if k = (0 : Lattice d) then 0 else ‖coeffOf u k‖ ^ 2) := by
    rw [hP, hSum.tsum_eq_add_tsum_ite 0, h0]
    simp only [add_sub_cancel_left]
  -- gradient side
  obtain ⟨hmem, -⟩ := memHs_one_coeffOf u hu
  have hS1 : Summable fun k => sobWeight 1 k * ‖coeffOf u k‖ ^ 2 := hmem
  have hterm : ∀ k : Lattice d, ‖((2 * Real.pi * Lattice.enorm k : ℝ) : ℂ) * coeffOf u k‖ ^ 2 =
      (2 * Real.pi * Lattice.enorm k) ^ 2 * ‖coeffOf u k‖ ^ 2 := by
    intro k
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hSg : Summable fun k : Lattice d =>
      ‖((2 * Real.pi * Lattice.enorm k : ℝ) : ℂ) * coeffOf u k‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hS1
    rw [hterm]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    unfold sobWeight
    rw [Real.rpow_one]
    nlinarith [sq_nonneg Real.pi]
  have hG := grad_parseval hu
  rw [hsNormSq_zero] at hG
  rw [h1, h2, ← hG]
  have hSg' : Summable fun k : Lattice d =>
      (4 * Real.pi ^ 2)⁻¹ * ‖((2 * Real.pi * Lattice.enorm k : ℝ) : ℂ) * coeffOf u k‖ ^ 2 :=
    hSg.mul_left _
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) ?_ hSg'
  · by_cases hk : k = 0
    · rw [ite_eq_left_iff.mpr (fun h => absurd hk h)]; positivity
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hk), hterm]
      have h1k := one_le_enorm k hk
      have hpi : 0 < Real.pi := Real.pi_pos
      have : (4 * Real.pi ^ 2)⁻¹ * ((2 * Real.pi * Lattice.enorm k) ^ 2 * ‖coeffOf u k‖ ^ 2) =
          Lattice.enorm k ^ 2 * ‖coeffOf u k‖ ^ 2 := by
        field_simp
        norm_num
      rw [this]
      exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ h1k)
  · refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hSum
    · split_ifs <;> positivity
    · split_ifs <;> simp

/-! ### Section 8 (AP6b): the small-dissipation lemma -/

/-- A real coefficient sequence whose function is somewhere positive is absolutely summable
(otherwise the `tsum` defining `toFun` is the junk value `0`). -/
theorem summable_norm_of_toFun_pos (c : Coeff d) (x : Torus d) (hx : 0 < toFun c x) :
    Summable fun k => ‖c k‖ := by
  by_contra hns
  have hns' : ¬ Summable fun k => c k * Torus.mode k x := by
    intro hs
    apply hns
    have := (summable_norm_iff.mpr hs)
    simpa [norm_mul, Torus.norm_mode] using this
  have : toFun c x = 0 := by
    unfold toFun series
    rw [tsum_eq_zero_of_not_summable hns']
    simp
  linarith

theorem integral_toFun_eq_one_of_pos (c : Coeff d) (hreal : IsRealCoeff c) (h0 : c 0 = 1)
    (hpos : ∀ x, 0 < toFun c x) : ∫ x, toFun c x = 1 := by
  have hs : Summable fun k => ‖c k‖ := summable_norm_of_toFun_pos c 0 (hpos 0)
  have h1 := coeffOf_zero_eq_integral' (toFun c)
  rw [coeffOf_toFun c hreal hs, h0] at h1
  exact_mod_cast h1.symm

theorem isCk1_mul {f g : Torus d → ℝ} (hf : Torus.IsCk 1 f) (hg : Torus.IsCk 1 g) :
    Torus.IsCk 1 (fun x => f x * g x) := hf.mul hg

theorem isCk1_const_mul {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) (c : ℝ) :
    Torus.IsCk 1 (fun x => c * f x) := contDiff_const.mul hf

theorem isCk1_exp {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) :
    Torus.IsCk 1 (fun x => Real.exp (f x)) := Real.contDiff_exp.comp hf

theorem partialDeriv_const_mul_of_isCk1 (j : Fin d) {f : Torus d → ℝ} (hf : Torus.IsCk 1 f)
    (c : ℝ) (x : Torus d) :
    Torus.partialDeriv j (fun y => c * f y) x = c * Torus.partialDeriv j f x := by
  unfold Torus.partialDeriv
  have e : Torus.lift (fun y => c * f y) = fun y => c * Torus.lift f y := rfl
  rw [e, fderiv_const_mul ((hf.differentiable one_ne_zero) _)]
  simp

theorem partialDeriv_exp_of_isCk1 (j : Fin d) {f : Torus d → ℝ} (hf : Torus.IsCk 1 f)
    (x : Torus d) :
    Torus.partialDeriv j (fun y => Real.exp (f y)) x =
      Real.exp (f x) * Torus.partialDeriv j f x := by
  unfold Torus.partialDeriv
  have e : Torus.lift (fun y => Real.exp (f y)) = fun y => Real.exp (Torus.lift f y) := rfl
  rw [e, fderiv_exp ((hf.differentiable one_ne_zero) _)]
  simp [Torus.lift, Torus.mk_rep]

/-- Gradient of `ρ e^{ν⁻¹ W}`. -/
theorem grad_mul_exp {ρ W : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) (hW : Torus.IsCk 1 W) (ν : ℝ)
    (x : Torus d) :
    Torus.grad (fun y => ρ y * Real.exp (ν⁻¹ * W y)) x =
      Real.exp (ν⁻¹ * W x) • (Torus.grad ρ x + (ν⁻¹ * ρ x) • Torus.grad W x) := by
  have hE : Torus.IsCk 1 (fun y => Real.exp (ν⁻¹ * W y)) := isCk1_exp (isCk1_const_mul hW ν⁻¹)
  ext j
  simp only [MFAux.grad_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  rw [MFAux.partialDeriv_mul j ρ _ hρ hE, partialDeriv_exp_of_isCk1 j (isCk1_const_mul hW ν⁻¹),
    partialDeriv_const_mul_of_isCk1 j hW]
  ring

theorem isCk_mul_exp {ρ W : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) (hW : Torus.IsCk 1 W) (ν : ℝ) :
    Torus.IsCk 1 (fun y => ρ y * Real.exp (ν⁻¹ * W y)) :=
  isCk1_mul hρ (isCk1_exp (isCk1_const_mul hW ν⁻¹))

theorem norm_fderiv_lift_eq (φ : Torus d → ℝ) (y : Euc d) :
    ‖fderiv ℝ (Torus.lift φ) y‖ = ‖Torus.grad φ (Torus.mk y)‖ := by
  have h := congrFun (lift_grad φ) y
  have h2 : Torus.lift (Torus.grad φ) y = Torus.grad φ (Torus.mk y) := rfl
  rw [h2] at h
  rw [h]
  show ‖fderiv ℝ (Torus.lift φ) y‖ = ‖(InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (Torus.lift φ) y)‖
  rw [LinearIsometryEquiv.norm_map]

theorem cbNorm_one_le {u : Torus d → ℝ} {B0 B1 : ℝ} (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (h0 : ∀ x, |u x| ≤ B0) (h1 : ∀ x, ‖Torus.grad u x‖ ≤ B1) : Torus.cbNorm 1 u ≤ B0 + B1 := by
  unfold Torus.cbNorm
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  refine add_le_add (Real.iSup_le (fun y => ?_) hB0) (Real.iSup_le (fun y => ?_) hB1)
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact h0 _
  · rw [norm_iteratedFDeriv_one, norm_fderiv_lift_eq]
    exact h1 _

theorem continuous_dissipation_integrand {ρ W : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ)
    (hW : Torus.IsCk 1 W) (hpos : ∀ x, 0 < ρ x) (ν : ℝ) :
    Continuous fun x => ‖ν • Torus.grad ρ x + ρ x • Torus.grad W x‖ ^ 2 / ρ x := by
  have hρc : Continuous ρ := continuous_of_isCk' hρ le_rfl
  have e : ∀ x, ‖ν • Torus.grad ρ x + ρ x • Torus.grad W x‖ ^ 2 =
      ∑ j, (ν * Torus.partialDeriv j ρ x + ρ x * Torus.partialDeriv j W x) ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    simp [MFAux.grad_apply]
  simp_rw [e]
  refine Continuous.div ?_ hρc fun x => (hpos x).ne'
  exact continuous_finsetSum _ fun j _ =>
    (((continuous_partialDeriv j _ hρ).const_mul ν).add
      (hρc.mul (continuous_partialDeriv j _ hW))).pow 2

theorem exists_eta_small (C a p : ℝ) (ha : 0 < a) (hp : 0 < p) :
    ∃ η : ℝ, 0 < η ∧ C * (η + η ^ p) < a := by
  have hcont : ContinuousAt (fun η : ℝ => C * (η + η ^ p)) 0 := by
    have h1 : ContinuousAt (fun η : ℝ => η ^ p) 0 := Real.continuousAt_rpow_const _ _ (Or.inr hp.le)
    exact continuousAt_const.mul (continuousAt_id.add h1)
  have h0 : C * ((0 : ℝ) + (0 : ℝ) ^ p) = 0 := by simp [Real.zero_rpow hp.ne']
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hcont a ha
  refine ⟨δ / 2, by positivity, ?_⟩
  have := hδ' (x := δ / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
  rw [Real.dist_eq, h0, sub_zero] at this
  exact (le_abs_self _).trans_lt this

theorem exists_lower_of_small_dissipation (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (νm νp M W₀ L₁ L₂ : ℝ) (hνm : 0 < νm) (hνν : νm ≤ νp) :
    ∃ ε₀ κ : ℝ, 0 < ε₀ ∧ 0 < κ ∧ ∀ ν ∈ Set.Icc νm νp, ∀ c : Coeff d, IsRealCoeff c →
      MemHs 2 c → Torus.IsCk 1 (toFun c) → Torus.IsCk 1 (Wpot d s V c) → (∀ x, 0 < toFun c x) →
      (∀ x, toFun c x ≤ M) → c 0 = 1 → (∀ x, |Wpot d s V c x| ≤ W₀) →
      (∀ x, ‖Torus.grad (toFun c) x‖ ≤ L₁) → (∀ x, ‖Torus.grad (Wpot d s V c) x‖ ≤ L₂) →
      dissipation d s V ν c ≤ ε₀ → ∀ x, κ ≤ toFun c x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set M' : ℝ := max M 0 with hM'
  set W' : ℝ := max W₀ 0 with hW'
  set L₁' : ℝ := max L₁ 0 with hL₁'
  set L₂' : ℝ := max L₂ 0 with hL₂'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hW'0 : 0 ≤ W' := le_max_right _ _
  have hL₁'0 : 0 ≤ L₁' := le_max_right _ _
  have hL₂'0 : 0 ≤ L₂' := le_max_right _ _
  set a₀ : ℝ := Real.exp (-(W' / νm)) with ha₀
  set E₀ : ℝ := Real.exp (W' / νm) with hE₀
  have ha₀pos : 0 < a₀ := Real.exp_pos _
  have hE₀pos : 0 < E₀ := Real.exp_pos _
  set B0 : ℝ := M' * E₀ with hB0
  set B1 : ℝ := E₀ * (L₁' + νm⁻¹ * M' * L₂') with hB1
  have hB0nn : 0 ≤ B0 := by positivity
  have hB1nn : 0 ≤ B1 := by positivity
  obtain ⟨C, hC0, hC⟩ := exists_sup_sub_mean_le hd (B0 + B1) (by positivity)
  set p : ℝ := 2 / ((d : ℝ) + 2) with hp
  have hp0 : 0 < p := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    positivity
  obtain ⟨η₁, hη₁, hη₁C⟩ := exists_eta_small C (a₀ / 2) p (by positivity) hp0
  set A₁ : ℝ := E₀ ^ 2 * (νm⁻¹) ^ 2 * M' with hA₁
  have hA₁0 : 0 ≤ A₁ := by positivity
  refine ⟨4 * Real.pi ^ 2 * η₁ ^ 2 / (A₁ + 1), a₀ * a₀ / 2, by positivity, by positivity, ?_⟩
  intro ν hν c hreal hmem hρ1 hW1 hpos hM hc0 hW hL1 hL2 hD
  have hν0 : 0 < ν := lt_of_lt_of_le hνm hν.1
  have hνinv : ν⁻¹ ≤ νm⁻¹ := inv_anti₀ hνm hν.1
  have hνinv0 : 0 ≤ ν⁻¹ := inv_nonneg.2 hν0.le
  set ρ : Torus d → ℝ := toFun c with hρdef
  set W : Torus d → ℝ := Wpot d s V c with hWdef
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable f := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hρc : Continuous ρ := continuous_of_isCk' hρ1 le_rfl
  have hmass : ∫ x, ρ x = 1 := integral_toFun_eq_one_of_pos c hreal hc0 hpos
  -- the auxiliary function `u = ρ e^{W/ν}`
  set u : Torus d → ℝ := fun y => ρ y * Real.exp (ν⁻¹ * W y) with hudef
  have hu1 : Torus.IsCk 1 u := isCk_mul_exp hρ1 hW1 ν
  have huc : Continuous u := continuous_of_isCk' hu1 le_rfl
  -- exponent bounds
  have hexp_le : ∀ x, ν⁻¹ * W x ≤ W' / νm := by
    intro x
    have h1 : W x ≤ W' := (le_abs_self _).trans ((hW x).trans (le_max_left _ _))
    calc ν⁻¹ * W x ≤ ν⁻¹ * W' := mul_le_mul_of_nonneg_left h1 hνinv0
      _ ≤ νm⁻¹ * W' := mul_le_mul_of_nonneg_right hνinv hW'0
      _ = W' / νm := by rw [div_eq_inv_mul]
  have hexp_ge : ∀ x, -(W' / νm) ≤ ν⁻¹ * W x := by
    intro x
    have h1 : -W' ≤ W x := by
      have := (abs_le.1 ((hW x).trans (le_max_left W₀ 0))).1
      linarith
    calc -(W' / νm) = νm⁻¹ * (-W') := by rw [div_eq_inv_mul]; ring
      _ ≤ ν⁻¹ * (-W') := mul_le_mul_of_nonpos_right hνinv (by linarith)
      _ ≤ ν⁻¹ * W x := mul_le_mul_of_nonneg_left h1 hνinv0
  have hE_le : ∀ x, Real.exp (ν⁻¹ * W x) ≤ E₀ := fun x => Real.exp_le_exp.2 (hexp_le x)
  have hE_ge : ∀ x, a₀ ≤ Real.exp (ν⁻¹ * W x) := fun x => Real.exp_le_exp.2 (hexp_ge x)
  have hρM : ∀ x, ρ x ≤ M' := fun x => (hM x).trans (le_max_left _ _)
  -- pointwise bounds on `u` and its gradient
  have hu_abs : ∀ x, |u x| ≤ B0 := by
    intro x
    rw [abs_of_pos (mul_pos (hpos x) (Real.exp_pos _))]
    exact mul_le_mul (hρM x) (hE_le x) (Real.exp_pos _).le hM'0
  have hgrad_u : ∀ x, Torus.grad u x =
      Real.exp (ν⁻¹ * W x) • (Torus.grad ρ x + (ν⁻¹ * ρ x) • Torus.grad W x) :=
    fun x => grad_mul_exp hρ1 hW1 ν x
  have hgrad_le : ∀ x, ‖Torus.grad u x‖ ≤ B1 := by
    intro x
    rw [hgrad_u, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (hE_le x) ?_ (norm_nonneg _) hE₀pos.le
    calc ‖Torus.grad ρ x + (ν⁻¹ * ρ x) • Torus.grad W x‖
        ≤ ‖Torus.grad ρ x‖ + ‖(ν⁻¹ * ρ x) • Torus.grad W x‖ := norm_add_le _ _
      _ ≤ L₁' + νm⁻¹ * M' * L₂' := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hνinv0 (hpos x).le)]
          refine add_le_add ((hL1 x).trans (le_max_left _ _)) ?_
          exact mul_le_mul (mul_le_mul hνinv (hρM x) (hpos x).le (inv_nonneg.2 hνm.le))
            ((hL2 x).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
  have hcb : Torus.cbNorm 1 u ≤ B0 + B1 := cbNorm_one_le hB0nn hB1nn hu_abs hgrad_le
  -- gradient of `u` against the dissipation integrand
  have hgrad_sq : ∀ x, ‖Torus.grad u x‖ ^ 2 ≤
      A₁ * (‖ν • Torus.grad ρ x + ρ x • Torus.grad W x‖ ^ 2 / ρ x) := by
    intro x
    have hJ : ν • Torus.grad ρ x + ρ x • Torus.grad W x =
        ν • (Torus.grad ρ x + (ν⁻¹ * ρ x) • Torus.grad W x) := by
      rw [smul_add, smul_smul, ← mul_assoc, mul_inv_cancel₀ hν0.ne', one_mul]
    have hn : ‖Torus.grad u x‖ = Real.exp (ν⁻¹ * W x) * ν⁻¹ *
        ‖ν • Torus.grad ρ x + ρ x • Torus.grad W x‖ := by
      rw [hJ, norm_smul, Real.norm_eq_abs, abs_of_pos hν0, hgrad_u, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      field_simp
    have hρx := hpos x
    set J : ℝ := ‖ν • Torus.grad ρ x + ρ x • Torus.grad W x‖ with hJdef
    have h1 : J ^ 2 ≤ M' * (J ^ 2 / ρ x) := by
      rw [← mul_div_assoc, le_div_iff₀ hρx]
      calc J ^ 2 * ρ x = ρ x * J ^ 2 := mul_comm _ _
        _ ≤ M' * J ^ 2 := mul_le_mul_of_nonneg_right (hρM x) (sq_nonneg _)
    have h2 : (Real.exp (ν⁻¹ * W x) * ν⁻¹) ^ 2 ≤ E₀ ^ 2 * (νm⁻¹) ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul (hE_le x) hνinv hνinv0 hE₀pos.le) 2
    rw [hn, mul_pow]
    calc (Real.exp (ν⁻¹ * W x) * ν⁻¹) ^ 2 * J ^ 2
        ≤ (E₀ ^ 2 * (νm⁻¹) ^ 2) * (M' * (J ^ 2 / ρ x)) :=
          mul_le_mul h2 h1 (sq_nonneg _) (by positivity)
      _ = A₁ * (J ^ 2 / ρ x) := by rw [hA₁]; ring
  -- the integrated gradient bound
  have hDint : Continuous fun x => ‖ν • Torus.grad ρ x + ρ x • Torus.grad W x‖ ^ 2 / ρ x :=
    continuous_dissipation_integrand hρ1 hW1 hpos ν
  have hΓ : ∫ x, ‖Torus.grad u x‖ ^ 2 ≤ A₁ * dissipation d s V ν c := by
    unfold dissipation
    rw [← integral_const_mul]
    exact integral_mono (hint _ (continuous_norm_grad_sq hu1)) ((hint _ hDint).const_mul _)
      hgrad_sq
  set ε₀ : ℝ := 4 * Real.pi ^ 2 * η₁ ^ 2 / (A₁ + 1) with hε₀
  have hε₀pos : 0 < ε₀ := by positivity
  have hPoin : ∫ x, (u x - ∫ y, u y) ^ 2 ≤ η₁ ^ 2 := by
    refine (poincare_sq hu1).trans ?_
    have h1 : ∫ x, ‖Torus.grad u x‖ ^ 2 ≤ A₁ * ε₀ :=
      hΓ.trans (mul_le_mul_of_nonneg_left hD hA₁0)
    have h2 : A₁ * ε₀ ≤ 4 * Real.pi ^ 2 * η₁ ^ 2 := by
      rw [hε₀, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2)
        (sq_nonneg η₁)) hA₁0]
    calc (4 * Real.pi ^ 2)⁻¹ * ∫ x, ‖Torus.grad u x‖ ^ 2
        ≤ (4 * Real.pi ^ 2)⁻¹ * (4 * Real.pi ^ 2 * η₁ ^ 2) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = η₁ ^ 2 := by field_simp
  -- lower bound for the mean of `u`
  have hmean : a₀ ≤ ∫ y, u y := by
    have : ∫ y, a₀ * ρ y ≤ ∫ y, u y :=
      integral_mono ((hint _ hρc).const_mul _) (hint _ huc) fun x =>
        by
          have := mul_le_mul_of_nonneg_left (hE_ge x) (hpos x).le
          simp only [hudef]
          linarith
    rw [integral_const_mul, hmass] at this
    linarith
  intro x
  have hosc := hC u hu1 hcb η₁ hη₁.le hPoin x
  have hlt : |u x - ∫ y, u y| < a₀ / 2 := lt_of_le_of_lt hosc hη₁C
  have hux : a₀ / 2 ≤ u x := by
    have := (abs_lt.1 hlt).1
    linarith
  have hρx : ρ x = u x * Real.exp (-(ν⁻¹ * W x)) := by
    simp only [hudef]
    rw [mul_assoc, ← Real.exp_add]
    simp
  have hexp2 : a₀ ≤ Real.exp (-(ν⁻¹ * W x)) := by
    refine Real.exp_le_exp.2 ?_
    have := hexp_le x
    linarith
  show a₀ * a₀ / 2 ≤ ρ x
  rw [hρx]
  nlinarith

/-! ### Section 9 (AP6b): the uniform lower bound -/

theorem norm_grad_le_cbNorm {φ : Torus d → ℝ} (hφ : Torus.IsCk 1 φ) (x : Torus d) :
    ‖Torus.grad φ x‖ ≤ Torus.cbNorm 1 φ := by
  have h := norm_fderiv_lift_eq φ (Torus.rep x)
  rw [Torus.mk_rep] at h
  rw [← h]
  exact R2Aux.norm_fderiv_le_cbNorm hφ _

/-- The dissipation is interval integrable on `[0,T]` when the density stays above `δ > 0`. -/
theorem intervalIntegrable_dissipation (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) {T : ℝ} (hT : 0 ≤ T) (H : MFSolRealOn d s V ν K ρ₀ ρc T) (δ : ℝ)
    (hδ : 0 < δ) (hposδ : ∀ t ∈ Set.Icc 0 T, ∀ x, δ ≤ mfPath ρc t x) :
    IntervalIntegrable (fun t => dissipation d s V ν (ρc t)) volume 0 T := by
  rcases hT.eq_or_lt with rfl | hT'
  · exact IntervalIntegrable.refl
  · have hcont : ContinuousOn (fun τ => -freeEnergy' d s V ν (ρc τ)) (uIcc 0 T) := by
      rw [uIcc_of_le hT]
      exact (continuousOn_freeEnergy' hd s hs0 hsd K hK V ρ₀ hV ν ρc H).neg
    have hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt (fun τ => -freeEnergy' d s V ν (ρc τ))
        (dissipation d s V ν (ρc t)) t := fun t ht => by
      have := (hasDerivAt_freeEnergy' hd s hs0 hsd K hK V ρ₀ hV ν ρc H le_rfl hT' le_rfl δ hδ
        hposδ ht).fun_neg
      rwa [neg_neg] at this
    have hD0 : ∀ t ∈ Ioo 0 T, 0 ≤ dissipation d s V ν (ρc t) := fun t ht =>
      integral_nonneg fun x => div_nonneg (sq_nonneg _)
        (lt_of_lt_of_le hδ (hposδ t ⟨ht.1.le, ht.2.le⟩ x)).le
    exact intervalIntegral.intervalIntegrable_deriv_of_nonneg hcont
      (by rw [min_eq_left hT, max_eq_right hT]; exact hderiv) (by
        rw [min_eq_left hT, max_eq_right hT]; exact hD0)

theorem exists_inf_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (νm νp : ℝ)
    (hνm : 0 < νm) (hνν : νm ≤ νp) (ρ₀ : Torus d → ℝ) (hρ₀ : IsProbDensity ρ₀)
    (hρ₀H : MemSobolev K ρ₀) (hpos : ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ ρ₀ x) :
    ∃ c : ℝ, 0 < c ∧ ∀ ν ∈ Set.Icc νm νp, ∀ (T : ℝ) (ρc : ℝ → Coeff d),
      MFSolRealOn d s V ν K ρ₀ ρc T → ∀ t ∈ Set.Icc 0 T, ∀ x, c ≤ mfPath ρc t x := by
  have hV2 : Torus.IsCk 2 V := hV.of_le (by exact_mod_cast (by omega : 2 ≤ K + 2))
  have hKd : (d : ℝ) / 2 < (K : ℝ) := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hK2 : (2 : ℝ) ≤ K := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hpos' := hpos
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_sup_bound hd s hs0 hsd K hK V hV νm νp hνm hνν ρ₀ hρ₀ hρ₀H hpos
  obtain ⟨CK, hCK0, hCK⟩ := exists_hK_bound hd s hs0 hsd K hK V hV νm νp hνm hνν ρ₀ hρ₀H Λ
  obtain ⟨CW, hCW0, hCW⟩ := exists_Wpot_bounds hd s hs0 hsd (K : ℝ) hK V hV2
  obtain ⟨C1, hC10, hC1⟩ := exists_mfPath_isCk (d := d) 1 (K : ℝ)
    (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      push_cast
      linarith)
  set G : ℝ := CW * (1 + CK) with hG
  have hGnn : 0 ≤ G := by positivity
  set L₁ : ℝ := C1 * CK with hL₁
  obtain ⟨ε₀, κ, hε₀, hκ, hlow⟩ :=
    exists_lower_of_small_dissipation hd s hs0 hsd V νm νp Λ G L₁ G hνm hνν
  obtain ⟨c₀, hc₀, hc₀ρ⟩ := hpos
  -- the energy constant
  set c0 : Coeff d := coeffOf ρ₀ with hc0def
  set a : ℝ := ∫ x, toFun c0 x * Real.log (toFun c0 x) with ha
  set b : ℝ := (∫ x, V x * toFun c0 x) +
    (1 / 2 : ℝ) * (∑' k, (rieszCoeff d s k : ℂ) * ‖c0 k‖ ^ 2).re with hb
  have hsupnn : 0 ≤ Torus.supNorm V := Real.iSup_nonneg fun _ => norm_nonneg _
  set E : ℝ := νp * |a| + |b| + Torus.supNorm V with hE
  have hνp : 0 < νp := lt_of_lt_of_le hνm hνν
  have hE0 : 0 ≤ E := by positivity
  have hEbound : ∀ ν ∈ Set.Icc νm νp, freeEnergy' d s V ν c0 + Torus.supNorm V ≤ E := by
    intro ν hν
    have e : freeEnergy' d s V ν c0 = ν * a + b := by
      unfold freeEnergy'
      rw [ha, hb]
      ring
    rw [e]
    have h1 : ν * a ≤ νp * |a| :=
      (mul_le_mul_of_nonneg_right hν.2 (abs_nonneg a) |>.trans' (mul_le_mul_of_nonneg_left
        (le_abs_self a) (lt_of_lt_of_le hνm hν.1).le))
    have h2 : b ≤ |b| := le_abs_self b
    rw [hE]
    linarith
  set τ : ℝ := E / ε₀ + 1 with hτ
  have hτ1 : 1 ≤ τ := by
    have : 0 ≤ E / ε₀ := div_nonneg hE0 hε₀.le
    linarith
  refine ⟨min κ c₀ * Real.exp (-(G * τ)), by positivity, ?_⟩
  intro ν hν T ρc H t ht x
  have hν0 : 0 < ν := lt_of_lt_of_le hνm hν.1
  have hupper : ∀ t ∈ Set.Icc 0 T, ∀ x, |mfPath ρc t x| ≤ Λ := fun t ht x => by
    have := hΛ ν hν T ρc H t ht x
    rw [abs_of_nonneg this.1]
    exact this.2
  have hnorm := hCK ν hν T ρc H hupper
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) T, MemHs (K : ℝ) (ρc t) := H.sol.cont.1
  obtain ⟨δ, hδ, hδle⟩ :=
    exists_pos_on_Icc hd s hs0 hsd K hK V ρ₀ hV ν hν0 ρc H hρ₀H hpos'
  have hposT : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < mfPath ρc t x := fun t ht x =>
    lt_of_lt_of_le hδ (hδle t ht x)
  have hmass : ∀ t ∈ Set.Icc (0 : ℝ) T, ρc t 0 = 1 := by
    intro t ht
    rw [coeff_zero_eq_on hd s V ρ₀ ν K ρc H.sol ht, coeffOf_zero_eq_integral', hρ₀.integral_one]
    simp
  have hWb : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      |Torus.laplacian (Wpot d s V (ρc t)) x| ≤ G ∧ ‖Torus.grad (Wpot d s V (ρc t)) x‖ ≤ G ∧
        |Wpot d s V (ρc t) x| ≤ G := by
    intro t ht x
    obtain ⟨h1, h2, h3⟩ := hCW (ρc t) (hmem t ht) (H.real t ht) x
    have hle : CW * (1 + hsNorm (K : ℝ) (ρc t)) ≤ G :=
      mul_le_mul_of_nonneg_left (by linarith [hnorm t ht]) hCW0
    exact ⟨h1.trans hle, h2.trans hle, h3.trans hle⟩
  have hLap : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, -G ≤ Torus.laplacian (Wpot d s V (ρc t)) x :=
    fun t ht x => (abs_le.1 (hWb t ht x).1).1
  -- a good time has a uniform lower bound
  have hgood : ∀ t' ∈ Set.Icc (0 : ℝ) T, dissipation d s V ν (ρc t') ≤ ε₀ →
      ∀ x, κ ≤ mfPath ρc t' x := by
    intro t' ht' hD
    have hc := hmem t' ht'
    have hreal := H.real t' ht'
    obtain ⟨hρ1, hcb⟩ := hC1 (ρc t') hc hreal
    have hW2 := isCk_two_Wpot hd s hs0 hsd (K : ℝ) hK V hV2 (ρc t') hc hreal
    refine hlow ν hν (ρc t') hreal (Aux.memHs_mono hK2 hc) hρ1 (hW2.of_le (by norm_num))
      (fun x => hposT t' ht' x) (fun x => (hΛ ν hν T ρc H t' ht' x).2) (hmass t' ht')
      (fun x => (hWb t' ht' x).2.2) (fun x => ?_) (fun x => (hWb t' ht' x).2.1) hD
    exact (norm_grad_le_cbNorm hρ1 x).trans (hcb.trans
      (by rw [hL₁]; exact mul_le_mul_of_nonneg_left (hnorm t' ht') hC10))
  have hD0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ dissipation d s V ν (ρc t) := fun t ht =>
    integral_nonneg fun x => div_nonneg (sq_nonneg _) (hposT t ht x).le
  -- existence of a good time in every window of length `τ`
  have hgoodtime : ∀ t ∈ Set.Icc (0 : ℝ) T, τ ≤ t →
      ∃ t' ∈ Set.Icc (t - τ) t, dissipation d s V ν (ρc t') ≤ ε₀ := by
    intro t ht hτt
    by_contra hcon
    push Not at hcon
    have ht0 : 0 ≤ t := ht.1
    have Hm := H.mono ht.2
    have hsub : ∀ t' ∈ Set.Icc (0 : ℝ) t, t' ∈ Set.Icc (0 : ℝ) T := fun t' ht' =>
      ⟨ht'.1, ht'.2.trans ht.2⟩
    have hint := intervalIntegrable_dissipation hd s hs0 hsd K hK V ρ₀ hV ν ρc ht0 Hm δ hδ
      (fun t' ht' => hδle t' (hsub t' ht'))
    have hIle := integral_dissipation_le' hd s hs0 hsd K hK V ρ₀ hV ν hν0 ρc ht0 Hm
      (fun t' ht' x => hposT t' (hsub t' ht') x) (fun t' ht' => hmass t' (hsub t' ht'))
    have hF : freeEnergy' d s V ν (ρc 0) + Torus.supNorm V ≤ E := by
      rw [H.sol.init]
      exact hEbound ν hν
    have hint1 : IntervalIntegrable (fun t => dissipation d s V ν (ρc t)) volume 0 (t - τ) :=
      hint.mono_set (by
        rw [uIcc_of_le ht0, uIcc_of_le (by linarith)]
        exact Icc_subset_Icc le_rfl (by linarith))
    have hint2 : IntervalIntegrable (fun t => dissipation d s V ν (ρc t)) volume (t - τ) t :=
      hint.mono_set (by
        rw [uIcc_of_le ht0, uIcc_of_le (by linarith)]
        exact Icc_subset_Icc (by linarith) le_rfl)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    have h1 : 0 ≤ ∫ t' in (0 : ℝ)..(t - τ), dissipation d s V ν (ρc t') :=
      intervalIntegral.integral_nonneg (by linarith)
        (fun t' ht' => hD0 t' (hsub t' ⟨ht'.1, by linarith [ht'.2]⟩))
    have h2 : (t - (t - τ)) • ε₀ ≤ ∫ t' in (t - τ)..t, dissipation d s V ν (ρc t') := by
      rw [← intervalIntegral.integral_const]
      exact intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hint2
        (fun t' ht' => (hcon t' ht').le)
    have h3 : ε₀ * τ = E + ε₀ := by
      rw [hτ]
      field_simp
    simp only [smul_eq_mul, sub_sub_cancel] at h2
    linarith
  -- conclusion
  have hKd' : (d : ℝ) / 2 < (K : ℝ) := hKd
  by_cases hτt : τ ≤ t
  · obtain ⟨t', ht', hDt'⟩ := hgoodtime t ht hτt
    have ht'T : t' ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [ht'.1], ht'.2.trans ht.2⟩
    have hκ' := hgood t' ht'T hDt'
    have Hs := H.shift hKd' ht'T
    have key := lower_bound_of_laplacian_ge hd s hs0 hsd K hK V (mfPath ρc t') hV ν hν0
      (fun τ' => ρc (t' + τ')) Hs κ hκ (fun y => by simpa [mfPath] using hκ' y) G hGnn
      (fun u hu y => by
        have := hLap (t' + u) ⟨by linarith [hu.1, ht'T.1], by linarith [hu.2, ht'T.2]⟩ y
        exact this) (t - t') ⟨by linarith [ht'.2], by linarith [ht.2]⟩ x
    have e : mfPath (fun τ' => ρc (t' + τ')) (t - t') x = mfPath ρc t x := by
      simp [mfPath]
    rw [e] at key
    refine le_trans ?_ key
    have : min κ c₀ ≤ κ := min_le_left _ _
    calc min κ c₀ * Real.exp (-(G * τ)) ≤ κ * Real.exp (-G * (t - t')) := by
          refine mul_le_mul this (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hκ.le
          nlinarith [ht'.1]
      _ = κ * Real.exp (-G * (t - t')) := rfl
  · push Not at hτt
    have hρ0 := le_mfPath_zero hKd' hρ₀H hc₀ρ H.sol.init
    have key := lower_bound_of_laplacian_ge hd s hs0 hsd K hK V ρ₀ hV ν hν0 ρc H c₀ hc₀ hρ0 G hGnn
      hLap t ht x
    refine le_trans ?_ key
    have : min κ c₀ ≤ c₀ := min_le_right _ _
    refine mul_le_mul this (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hc₀.le
    nlinarith [ht.1]

end HRS.PDE.MFApriori
