import HRS.MH.CommSuperDefs
import HRS.MH.CommSuperCS8
import HRS.Commutator.Whole.ApproxAux2
import HRS.Commutator.Whole.ApproxAux3
import HRS.Commutator.Whole.Bridge

/-!
# CS9: removing the compact support (`truncation_limit`)

Truncate-and-renormalise: `ρ_m = c_m⁻¹ ρ 1_{‖x‖ ≤ m, |ρ| ≤ m}` (`cmxSA_rhom`), `c_m → 1`, `ρ_m ≤ c_m⁻¹ Λ`,
`|ρ_m| ≤ 2ρ` eventually.  `CompactCase` applies to each `ρ_m`; both sides converge by dominated convergence
(`cmxSA_pairGen_tendsto`), transferred to the Euclidean objects by `rieszEnergy_eq` and `commN_eq`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MH.CommSuper

variable {d N : ℕ} {s : ℝ}

open HRS.Commutator.Whole (cmxSA_trunc cmxSA_S cmxSA_c cmxSA_rhom cmxSA_rhom_bdd cmxSA_trunc_abs_le
  cmxSA_trunc_zero cmxSA_c_eventually cmxSA_rhom_tendsto cmxSA_rhom_dom cmxSA_c_tendsto
  cmxSA_pairGen_tendsto cmxSA_kern_measurable cmxSA_commKer_measurable kernGrad kern commKer
  modEnergy commA rieszScale rieszEnergy_eq commN_eq)

theorem cs9_trunc_nonneg {ρ : Euc d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (m : ℕ) (x : Euc d) :
    0 ≤ cmxSA_trunc ρ m x := by
  unfold cmxSA_trunc
  by_cases hx : x ∈ cmxSA_S ρ m
  · rw [Set.indicator_of_mem hx]; exact hρ0 x
  · rw [Set.indicator_of_notMem hx]

theorem cs9_rhom_nonneg {ρ : Euc d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) {m : ℕ}
    (hc : 1 / 2 ≤ cmxSA_c ρ m) (x : Euc d) : 0 ≤ cmxSA_rhom ρ d m x := by
  unfold cmxSA_rhom
  rw [if_pos hc]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.2 (by linarith)) (cs9_trunc_nonneg hρ0 m x)

theorem cs9_rhom_le {ρ : Euc d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) {m : ℕ}
    (hc : 1 / 2 ≤ cmxSA_c ρ m) (x : Euc d) : cmxSA_rhom ρ d m x ≤ (cmxSA_c ρ m)⁻¹ * Λ := by
  unfold cmxSA_rhom
  rw [if_pos hc]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hcpos : 0 < cmxSA_c ρ m := by linarith
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hcpos.le)
  have h1 := cmxSA_trunc_abs_le ρ m x
  rw [abs_of_nonneg (hρ0 x)] at h1
  exact le_trans (le_trans (le_abs_self _) h1) (hΛ x)

theorem cs9_rhom_zero {ρ : Euc d → ℝ} {m : ℕ} (hc : 1 / 2 ≤ cmxSA_c ρ m) {x : Euc d}
    (hx : (m : ℝ) < ‖x‖) : cmxSA_rhom ρ d m x = 0 := by
  unfold cmxSA_rhom
  rw [if_pos hc]
  simp [cmxSA_trunc_zero ρ m x hx]

theorem cs9_oN_cont {C₀ Λ : ℝ} (hΛ : 0 < Λ) (N : ℕ) (hN : 1 ≤ N) :
    ContinuousAt (fun Λ' : ℝ => oNΛ d s C₀ Λ' N) Λ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  unfold oNΛ
  refine ContinuousAt.add ?_ ?_
  · by_cases hs : s = 0
    · simp only [if_pos hs]
      exact ((continuousAt_const.mul continuousAt_id).log (mul_pos hNpos hΛ).ne').div_const _
    · simp only [if_neg hs]
      exact continuousAt_const
  · exact (continuousAt_const.mul (Real.continuousAt_rpow_const Λ (s / d) (Or.inl hΛ.ne'))).mul
      continuousAt_const

/-- **CS9** (size M).  Removing the compact support: `CompactCase` ⇒ the full estimate. -/
theorem truncation_limit_proof (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {C₀ C : ℝ}
    (hc : CompactCase d s C₀ C) (L : ℝ) :
    ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N → ∀ ρ : Euc d → ℝ, Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      (s = 0 → Whole.HasLogMoment (Whole.withDensityReal ρ) L) →
      ∀ X : Whole.EucConfig d N, Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), Whole.HasLipBoundW v K →
        |Whole.commN d s v X (Whole.withDensityReal ρ)| ≤
          C * K * (Whole.rieszModulatedEnergy d s X (Whole.withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  intro Λ hΛ1 N hN ρ hρ hρΛ hlog X hX v K hvK
  unfold CompactCase at hc
  obtain ⟨_, _, hcc⟩ := hc
  have hΛpos : 0 < Λ := by linarith
  have hρ0 := hρ.nonneg
  have hρmeas := hρ.measurable
  have hρint : Integrable ρ := cs8_integrable hρ
  have hmass := hρ.integral_one
  obtain ⟨hEI, hCI, -⟩ := bdd_integrable_proof hd hs0 hsd hρ hρΛ hlog X hX v K hvK
  have hvK' := hvK
  obtain ⟨Lv, hLv, -⟩ := hvK'
  have hvmeas : Measurable v := hLv.continuous.measurable
  have hmeas : ∀ m, Measurable (cmxSA_rhom ρ d m) := fun m => (cmxSA_rhom_bdd hd hρmeas m).measurable
  have hpt : ∀ x, Tendsto (fun m => cmxSA_rhom ρ d m x) atTop (𝓝 (ρ x)) :=
    cmxSA_rhom_tendsto hρmeas hρint hmass
  have hdom : ∀ᶠ m in atTop, ∀ x, |cmxSA_rhom ρ d m x| ≤ 2 * |ρ x| :=
    cmxSA_rhom_dom hρmeas hρint hmass
  have hkE : Measurable (fun q : Euc d × Euc d => kern s (q.1 - q.2)) :=
    (cmxSA_kern_measurable s).comp (measurable_fst.sub measurable_snd)
  have hPE := cmxSA_pairGen_tendsto (fun x y => kern s (x - y)) hkE X ρ hEI.1 hEI.2
    (fun m => cmxSA_rhom ρ d m) hmeas hpt hdom
  have hPC := cmxSA_pairGen_tendsto (commKer (kernGrad s) v) (cmxSA_commKer_measurable s hvmeas) X ρ
    hCI.1 hCI.2 (fun m => cmxSA_rhom ρ d m) hmeas hpt hdom
  have hev : ∀ᶠ m in atTop, 1 / 2 ≤ cmxSA_c ρ m := cmxSA_c_eventually hρmeas hρint hmass
  have hpm : ∀ᶠ m in atTop, Whole.IsProbDensity (cmxSA_rhom ρ d m) := by
    filter_upwards [hev] with m hm
    exact ⟨cs9_rhom_nonneg hρ0 hm, hmeas m, (cmxSA_rhom_bdd hd hρmeas m).mass⟩
  -- the masses and the bound Λ_m
  have hcT : Tendsto (cmxSA_c ρ) atTop (𝓝 1) := cmxSA_c_tendsto hρmeas hρint hmass
  have hΛT : Tendsto (fun m => max ((cmxSA_c ρ m)⁻¹ * Λ) 1) atTop (𝓝 Λ) := by
    have h1 : Tendsto (fun m => (cmxSA_c ρ m)⁻¹ * Λ) atTop (𝓝 (1⁻¹ * Λ)) :=
      (hcT.inv₀ one_ne_zero).mul_const Λ
    have h2 := h1.max (tendsto_const_nhds (x := (1 : ℝ)))
    have h3 : max (1⁻¹ * Λ) 1 = Λ := by
      rw [inv_one, one_mul]
      exact max_eq_left hΛ1
    rw [h3] at h2
    exact h2
  have hcont : ContinuousAt (fun Λ' : ℝ => oNΛ d s C₀ Λ' N) Λ := cs9_oN_cont hΛpos N (by omega)
  have hOT := hcont.tendsto.comp hΛT
  -- convergence of the two sides
  have hCN : Tendsto (fun m => Whole.commN d s v X (Whole.withDensityReal (cmxSA_rhom ρ d m)))
      atTop (𝓝 (Whole.commN d s v X (Whole.withDensityReal ρ))) := by
    rw [commN_eq ρ hρ X hX v]
    refine ((hPC.const_mul (rieszScale s)).congr' ?_)
    filter_upwards [hpm] with m hm
    exact (commN_eq _ hm X hX v).symm
  have hME : Tendsto (fun m => modEnergy s X (cmxSA_rhom ρ d m)) atTop (𝓝 (modEnergy s X ρ)) := by
    unfold modEnergy
    exact hPE.const_mul (1 / 2)
  have hFE : Tendsto (fun m => Whole.rieszModulatedEnergy d s X (Whole.withDensityReal (cmxSA_rhom ρ d m)))
      atTop (𝓝 (Whole.rieszModulatedEnergy d s X (Whole.withDensityReal ρ))) := by
    rw [rieszEnergy_eq ρ hρ X]
    refine ((hME.const_mul (rieszScale s)).congr' ?_)
    filter_upwards [hpm] with m hm
    exact (rieszEnergy_eq _ hm X).symm
  have hLHS := hCN.abs
  have hRHS := ((hFE.add hOT).const_mul (C * K))
  refine le_of_tendsto_of_tendsto hLHS hRHS ?_
  filter_upwards [hev, hpm] with m hm hpm_m
  -- the CompactCase bound for ρ_m
  have hXi : ∀ i, ‖X i‖ ≤ (m : ℝ) + ∑ j, ‖X j‖ := by
    intro i
    have h1 : ‖X i‖ ≤ ∑ j, ‖X j‖ := Finset.single_le_sum (fun j _ => norm_nonneg (X j))
      (Finset.mem_univ i)
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hsupp : ∀ x : Euc d, ((m : ℝ) + ∑ j, ‖X j‖) < ‖x‖ → cmxSA_rhom ρ d m x = 0 := by
    intro x hx
    have h1 : ∑ j, ‖X j‖ ≥ 0 := Finset.sum_nonneg (fun j _ => norm_nonneg (X j))
    exact cs9_rhom_zero hm (by linarith)
  have hbd := hcc (max ((cmxSA_c ρ m)⁻¹ * Λ) 1) (le_max_right _ _) N hN (cmxSA_rhom ρ d m) hpm_m
    (fun x => (cs9_rhom_le hρ0 hρΛ hm x).trans (le_max_left _ _))
    ((m : ℝ) + ∑ j, ‖X j‖) hsupp X hX hXi v K hvK
  exact hbd

end HRS.MH.CommSuper
