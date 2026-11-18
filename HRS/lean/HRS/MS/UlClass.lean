import HRS.MS.UlClassAux2
import HRS.MS.LcUniqAux2

/-!
# UL-5 (S5.1 infrastructure, supplement foundation packet): classical evolution, existence and uniqueness

Not a manuscript row.  Helper lemmas carry the prefix `ul5_`.

* `ou_duhamel_classical` (the plan's `IsLocalBackwardSolutionWithSource`, written out): for a uniformly
  strongly continuous family `w : [0,T] → UlClosure k θ` and `V τ = ∫_0^τ P_{τ-σ} ulPert (w σ) dσ`
  (`ulD`), every `V τ` lies in `UlClosure k θ` (hence is `C_b^4`), `V 0 = 0`, and for `τ ∈ (0,T)`, all `x`,
  `∂_τ V τ x = ν ΔV τ x + ⟨-Qx, ∇V τ x⟩ + ulPert (w τ) x` (the inhomogeneous OU equation with source
  `S_τ = ulPert (w τ)`; the "source form" of `IsLocalBackwardSolution`).
* `ul_evolution_exists`: for `4 + d/2 < k` there is `C` such that for every `t ∈ [0,T]` and every
  `f ∈ UlClosure k θ` there is an `IsUlBackwardEvolution` of the generator of `fixedViscosityCoeff` with
  `‖u r‖_{H^k_ul} ≤ C ‖f‖_{H^k_ul}` (`u r = w (t - r)`, `w` the mild solution of `ul_mild_exists`).
* `ul_evolution_unique`: two evolutions with the same terminal datum agree on `[0,t]`.  Every evolution
  is mild (`ul5_mild_of_evolution`): with `w τ = u (t - τ)`, `V` the Duhamel integral of
  `ulPert (w ·)`, the difference `u r - P_{t-r} f - V (t-r)` is a bounded classical solution of the
  homogeneous OU equation with terminal datum `0`, hence `0` by `lc_unique` (not `uloc_uniqueness_proof`).
  The mild uniqueness `ul_mild_unique` of UL-4 then gives uniqueness.

Adjustment of the plan statements (documented, harmless): the data index is `4 + d/2 < k` (as in the UL-4
packet), `ρ` is Schwartz as `∃ ψ : SchwartzMap, ⇑ψ = ρ`; the statements are for every `t ∈ [0,T]`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.Ul
open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UlocMW
open HRS.MS.Lc HRS.MD.EQLawPath

variable {d : ℕ}

section Class
variable {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ρ : Euc d → ℝ} {c : Euc d → Euc d} {ν : ℝ} {k : ℕ}
  {θ : Euc d → ℝ}

/-- unfolding of the generator of `fixedViscosityCoeff` at any time -/
theorem ul5_gen_fixed (s : ℝ) (M Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (c : Euc d → Euc d)
    (ρ : Euc d → ℝ) (r : ℝ) (φ : Euc d → ℝ) (x : Euc d) :
    generatorW (fixedViscosityCoeff s M Q ν c ρ) r φ x = ul5A Q ν φ x + ulPert s M ρ c φ x := by
  have e : generatorW (fixedViscosityCoeff s M Q ν c ρ) r φ x =
      generatorW (fixedViscosityCoeff s M Q ν c ρ) 0 φ x := rfl
  rw [e, generatorW_fixed]
  unfold ul5A ulPert
  rw [inner_neg_left]
  ring

/-- time reversal of a strongly continuous family -/
theorem ul5_reg_flip {t : ℝ} {u : ℝ → Euc d → ℝ} (hu : UlReg k θ t u) :
    UlReg k θ t (fun τ => u (t - τ)) := by
  have hflip : ∀ r ∈ Icc (0 : ℝ) t, t - r ∈ Icc (0 : ℝ) t := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  refine ⟨fun r hr => hu.mem _ (hflip r hr), fun r₀ h0 ε hε => ?_⟩
  obtain ⟨δ, hδ, h⟩ := hu.cont (t - r₀) (hflip r₀ h0) ε hε
  refine ⟨δ, hδ, fun r hr hd => h (t - r) (hflip r hr) ?_⟩
  rw [show t - r - (t - r₀) = -(r - r₀) by ring, abs_neg]
  exact hd

theorem ul5_flip_cont {t : ℝ} {a : ℝ → Euc d → ℝ}
    (h : Continuous (fun p : Icc (0 : ℝ) t × Euc d => a p.1 p.2)) :
    Continuous (fun p : Icc (0 : ℝ) t × Euc d => a (t - p.1) p.2) :=
  h.comp (Continuous.prodMk (Continuous.subtype_mk (continuous_const.sub
    (continuous_subtype_val.comp continuous_fst))
    (fun p => ⟨sub_nonneg.2 p.1.2.2, sub_le_self t p.1.2.1⟩)) continuous_snd)

/-- **`ou_duhamel_classical`.**  The Duhamel integral of a uniformly strongly continuous closure-valued
source is a classical solution of the inhomogeneous OU equation `∂_τ V = L_0 V + S_τ`, `V 0 = 0`,
`S_τ = ulPert (w τ)`, `L_0 = νΔ + ⟨-Qx, ∇·⟩`. -/
theorem ou_duhamel_classical (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) {T : ℝ}
    {w : ℝ → Euc d → ℝ} (hw : UlUReg k θ T w) :
    (∀ τ ∈ Icc (0 : ℝ) T, UlClosure k θ (fun y => ulD Q ν s M ρ c w τ τ y)) ∧
    (∀ y, ulD Q ν s M ρ c w 0 0 y = 0) ∧
    ∀ τ ∈ Ioo (0 : ℝ) T, ∀ x : Euc d,
      HasDerivAt (fun τ' => ulD Q ν s M ρ c w τ' τ' x)
        (ν * Laplacian.laplacian (fun y => ulD Q ν s M ρ c w τ τ y) x +
          inner ℝ (-(Torus.matVec Q x)) (gradient (fun y => ulD Q ν s M ρ c w τ τ y) x) +
          ulPert s M ρ c (w τ) x) τ :=
  ⟨fun τ hτ => (ul4b_adm H Q T w hw).mem τ hτ, fun y => by simp [ulD],
    fun τ hτ x => ul5_V_hasDerivAt H Q hw hτ x⟩

/-- the mild solution is differentiable in time, with derivative `L_0 w + ulPert w` -/
theorem ul5_w_deriv (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) {T : ℝ}
    {f : Euc d → ℝ} {w : ℝ → Euc d → ℝ} (hw : UlUReg k θ T w) (hf : UlClosure k θ f)
    (hmild : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x, w τ x = ouSg Q ν τ f x +
      ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (ulPert s M ρ c (w σ)) x)
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) T) (x : Euc d) :
    HasDerivAt (fun τ' => w τ' x) (ul5A Q ν (w τ) x + ulPert s M ρ c (w τ) x) τ := by
  obtain ⟨C, hC, hcb⟩ := ulClosure_cb k 2 H.hk2 θ H.hθ
  obtain ⟨hfcb, -⟩ := hcb f hf
  have hP := ou_forward_hasDerivAt Q H.hν.le hfcb.1 (M := cbNorm 2 f)
    (fun i hi y => ul3_cb_apply hfcb hi y) hτ.1 x
  have hV := ul5_V_hasDerivAt H Q hw hτ x
  have hsum := hP.add hV
  have hev : (fun τ' => w τ' x) =ᶠ[𝓝 τ] fun τ' =>
      ouSg Q ν τ' f x + ulD Q ν s M ρ c w τ' τ' x := by
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with τ' h'
    exact hmild τ' ⟨h'.1.le, h'.2.le⟩ x
  have hmem : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le⟩
  have hwτ : w τ = fun y => ouSg Q ν τ f y + ulD Q ν s M ρ c w τ τ y :=
    funext fun y => hmild τ hmem y
  have hC2a : ContDiff ℝ 2 (ouSg Q ν τ f) := ouSg_contDiff_two Q ν τ k θ H.hθ H.hk2 hf
  have hC2b : ContDiff ℝ 2 (fun y => ulD Q ν s M ρ c w τ τ y) :=
    ((ul4b_adm H Q T w hw).mem τ hmem).1
  have hA : ul5A Q ν (w τ) x = ul5A Q ν (ouSg Q ν τ f) x +
      ul5A Q ν (fun y => ulD Q ν s M ρ c w τ τ y) x := by
    rw [hwτ]; exact ul5_A_add Q ν hC2a hC2b x
  rw [hA]
  refine (hsum.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [ul5A]
  ring

/-- **Existence of the classical evolution from the mild solution.** -/
theorem ul5_evolution_of_mild (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) {t : ℝ}
    (ht : 0 ≤ t) {f : Euc d → ℝ} {w : ℝ → Euc d → ℝ} (hw : UlReg k θ t w)
    (hmild : ∀ τ ∈ Icc (0 : ℝ) t, ∀ x, w τ x = ouSg Q ν τ f x +
      ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (ulPert s M ρ c (w σ)) x) :
    IsUlBackwardEvolution θ k (fixedViscosityCoeff s M Q ν c ρ) t f (fun r => w (t - r)) := by
  have hwU : UlUReg k θ t w := ul4b_unif_of_reg H.hθ hw
  have hf0 : w 0 = f := by
    funext x
    rw [hmild 0 ⟨le_rfl, ht⟩ x]
    simp [ouSg_zero Q H.hν.le]
  have hfc : UlClosure k θ f := by
    rw [← hf0]; exact hw.mem 0 ⟨le_rfl, ht⟩
  have hureg : UlReg k θ t (fun r => w (t - r)) := ul5_reg_flip hw
  have huU : UlUReg k θ t (fun r => w (t - r)) := ul4b_unif_of_reg H.hθ hureg
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hureg.mem, hureg.cont⟩
  · exact fun r hr => (hureg.mem r hr).1
  · intro j hj
    obtain ⟨B, hB0, hB⟩ := ul5_ureg_bdd H.hθ hureg (j := 4) H.hk
    exact ⟨B, fun r hr x => (ul3_cb_apply (hB r hr).1 (hj.trans (by norm_num)) x).trans
      (hB r hr).2⟩
  · intro j hj
    exact ul5_ureg_joint H.hθ huU (j := 4) H.hk (i := j) (hj.trans (by norm_num))
  · show w (t - t) = f
    rw [sub_self]; exact hf0
  · intro x r hr
    have hτ : t - r ∈ Ioo (0 : ℝ) t := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have hd := ul5_w_deriv H Q hwU hfc hmild hτ x
    have hc := hd.scomp r ((hasDerivAt_id r).const_sub t)
    refine hc.congr_deriv ?_
    rw [ul5_gen_fixed]
    simp
  · have e : (fun p : Icc (0 : ℝ) t × Euc d => generatorW (fixedViscosityCoeff s M Q ν c ρ) p.1
        (w (t - p.1)) p.2) = fun p => ul5A Q ν (w (t - p.1)) p.2 +
          ulPert s M ρ c (w (t - p.1)) p.2 := by
      funext p; exact ul5_gen_fixed s M Q ν c ρ p.1 _ p.2
    show Continuous (fun p : Icc (0 : ℝ) t × Euc d => generatorW (fixedViscosityCoeff s M Q ν c ρ) p.1
        (w (t - p.1)) p.2)
    rw [e]
    exact (ul5_A_joint Q ν H.hθ (a := fun r => w (t - r)) huU H.hk2).add
      (ul5_pert_joint H (a := fun r => w (t - r)) huU)
  · obtain ⟨B, hB0, hB⟩ := ul5_ureg_bdd H.hθ hureg (j := 4) H.hk
    obtain ⟨Cp, hCp0, hpcb⟩ := ul4_pert_cb H.hs0 H.hsd M ρ H.hρ H.hc
    obtain ⟨K, hK0, hK⟩ := ul5_matVec_le Q
    refine ⟨|ν| * (d * B) + Cp * B + B * K, fun r hr x => ?_⟩
    rw [ul5_gen_fixed]
    have h1 : ‖iteratedFDeriv ℝ 1 (w (t - r)) x‖ ≤ B :=
      (ul3_cb_apply (hB r hr).1 (by norm_num) x).trans (hB r hr).2
    have h2 : ‖iteratedFDeriv ℝ 2 (w (t - r)) x‖ ≤ B :=
      (ul3_cb_apply (hB r hr).1 (by norm_num) x).trans (hB r hr).2
    have hA := ul5_A_bound Q ν x h1 h2
    have hp : |ulPert s M ρ c (w (t - r)) x| ≤ Cp * B :=
      ((hpcb _ (hB r hr).1).2 x).trans (mul_le_mul_of_nonneg_left (hB r hr).2 hCp0)
    have hQ : B * ‖Torus.matVec Q x‖ ≤ B * K * ‖x‖ := by
      calc B * ‖Torus.matVec Q x‖ ≤ B * (K * ‖x‖) := mul_le_mul_of_nonneg_left (hK x) hB0
        _ = B * K * ‖x‖ := by ring
    have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
    have hν0 : 0 ≤ |ν| * (d * B) := by positivity
    have hCB : 0 ≤ Cp * B := by positivity
    have hBK : 0 ≤ B * K := by positivity
    calc |ul5A Q ν (w (t - r)) x + ulPert s M ρ c (w (t - r)) x|
        ≤ |ul5A Q ν (w (t - r)) x| + |ulPert s M ρ c (w (t - r)) x| := abs_add_le _ _
      _ ≤ |ν| * (d * B) + B * ‖Torus.matVec Q x‖ + Cp * B := add_le_add hA hp
      _ ≤ (|ν| * (d * B) + Cp * B + B * K) * (1 + ‖x‖) := by
        nlinarith [mul_nonneg hν0 hx0, mul_nonneg hCB hx0]

end Class

/-- **`ul_evolution_exists`.**  `0 ≤ s < d`, `4 + d/2 < k`, `T ≥ 0`, `ν > 0`, `ρ` Schwartz, `c` smooth with bounded
derivatives: there is `C` such that for every `t ∈ [0,T]` and `f ∈ UlClosure k θ` there is a backward evolution
`u` (`IsUlBackwardEvolution`) with terminal time `t` and datum `f`, and `‖u r‖_{H^k_ul} ≤ C ‖f‖_{H^k_ul}`
for `r ∈ [0,t]`. -/
theorem ul_evolution_exists {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ)
    (k : ℕ) (hk : (4 : ℝ) + (d : ℝ) / 2 < k) (T ν : ℝ) (hT : 0 ≤ T) (hν : 0 < ν)
    (Q M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ)
    (c : Euc d → Euc d) (hc : IsSmoothBounded c) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ f : Euc d → ℝ, UlClosure k θ f →
      ∃ u : ℝ → Euc d → ℝ, IsUlBackwardEvolution θ k (fixedViscosityCoeff s M Q ν c ρ) t f u ∧
        ∀ r ∈ Icc (0 : ℝ) t, ulNormE k θ (u r) ≤ ENNReal.ofReal C * ulNormE k θ f := by
  have H : UlHyp s M ρ c ν k θ := ⟨hs0, hsd, hρ, hc, hν, hk, hθ⟩
  obtain ⟨C, hC⟩ := ul_mild_exists hs0 hsd θ hθ k hk T ν hT hν Q M ρ hρ c hc
  refine ⟨C, fun t ht f hf => ?_⟩
  obtain ⟨w, hmem, hcont, hmild⟩ := hC f hf
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc le_rfl ht.2
  have hw : UlReg k θ t w :=
    ⟨fun τ hτ => (hmem τ (hsub hτ)).1, fun τ₀ h0 ε hε => by
      obtain ⟨δ, hδ, h⟩ := hcont τ₀ (hsub h0) ε hε
      exact ⟨δ, hδ, fun τ hτ hd => h τ (hsub hτ) hd⟩⟩
  refine ⟨fun r => w (t - r), ul5_evolution_of_mild H Q ht.1 hw (fun τ hτ x => hmild τ (hsub hτ) x),
    fun r hr => (hmem (t - r) (hsub ⟨sub_nonneg.2 hr.2, sub_le_self t hr.1⟩)).2⟩

section Uniq
variable {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ρ : Euc d → ℝ} {c : Euc d → Euc d} {ν : ℝ} {k : ℕ}
  {θ : Euc d → ℝ}

/-- **Every classical evolution is mild** (via `lc_unique` for the homogeneous OU equation). -/
theorem ul5_mild_of_evolution (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) {t : ℝ}
    (ht : 0 ≤ t) {f : Euc d → ℝ} {u : ℝ → Euc d → ℝ}
    (hev : IsUlBackwardEvolution θ k (fixedViscosityCoeff s M Q ν c ρ) t f u) :
    ∀ τ ∈ Icc (0 : ℝ) t, ∀ x, u (t - τ) x = ouSg Q ν τ f x +
      ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (ulPert s M ρ c (u (t - σ))) x := by
  have hureg : UlReg k θ t u := ⟨hev.mem, hev.cont⟩
  have huU : UlUReg k θ t u := ul4b_unif_of_reg H.hθ hureg
  set w : ℝ → Euc d → ℝ := fun τ => u (t - τ) with hwdef
  have hw : UlReg k θ t w := ul5_reg_flip hureg
  have hwU : UlUReg k θ t w := ul4b_unif_of_reg H.hθ hw
  have hwr : ∀ r, w (t - r) = u r := fun r => by simp only [hwdef, sub_sub_cancel]
  have hflip : ∀ r ∈ Icc (0 : ℝ) t, t - r ∈ Icc (0 : ℝ) t := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hterm := hev.classicalSol.terminal
  have hfc : UlClosure k θ f := by
    have := hev.mem t ⟨ht, le_rfl⟩
    rwa [hterm] at this
  obtain ⟨Cf, hCf, hcbf⟩ := ulClosure_cb k 2 H.hk2 θ H.hθ
  obtain ⟨hfcb, -⟩ := hcbf f hfc
  have hV : UlUReg k θ t (fun τ y => ulD Q ν s M ρ c w τ τ y) := ul4b_adm H Q t w hwU
  have hP : UlUReg k θ t (fun σ => ouSg Q ν σ f) := ul4_P_ureg Q H.hν k θ H.hθ H.hk2 hfc
  set zt : ℝ → Euc d → ℝ := fun r x =>
    u r x - ouSg Q ν (t - r) f x - ulD Q ν s M ρ c w (t - r) (t - r) x with hzt
  have hsol : IsLocalBackwardSolution (fun _ => ν) (fun _ x => -(Torus.matVec Q x)) t
      (fun _ => (0 : ℝ)) zt := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      exact ((hev.mem r hr).1.sub (ouSg_contDiff_two Q ν (t - r) k θ H.hθ H.hk2 hfc)).sub
        (hV.mem (t - r) (hflip r hr)).1
    · obtain ⟨B1, hB1⟩ := ul5_val_bdd H.hθ hureg H.hk0
      obtain ⟨Bf, hBf⟩ := ul3C_bdd_of_cb hfcb
      obtain ⟨B2, hB2⟩ := ul5_val_bdd H.hθ hV.toReg H.hk0
      refine ⟨B1 + Bf + B2, fun r hr x => ?_⟩
      have h1 := hB1 r hr x
      have h2 : |ouSg Q ν (t - r) f x| ≤ Bf := ul4_ouSg_abs_le Q ν _ hBf x
      have h3 := hB2 (t - r) (hflip r hr) x
      calc |u r x - ouSg Q ν (t - r) f x - ulD Q ν s M ρ c w (t - r) (t - r) x|
          ≤ |u r x - ouSg Q ν (t - r) f x| + |ulD Q ν s M ρ c w (t - r) (t - r) x| := abs_sub _ _
        _ ≤ |u r x| + |ouSg Q ν (t - r) f x| + |ulD Q ν s M ρ c w (t - r) (t - r) x| :=
            by have := abs_sub (u r x) (ouSg Q ν (t - r) f x); linarith
        _ ≤ B1 + Bf + B2 := add_le_add (add_le_add h1 h2) h3
    · exact ((ul5_ureg_val H.hθ huU H.hk0).sub (ul5_flip_cont (ul5_ureg_val H.hθ hP H.hk0))).sub
        (ul5_flip_cont (ul5_ureg_val H.hθ hV H.hk0))
    · funext x
      show u t x - ouSg Q ν (t - t) f x - ulD Q ν s M ρ c w (t - t) (t - t) x = 0
      rw [sub_self, hterm, ouSg_zero Q H.hν.le]
      simp [ulD]
    · intro x r hr
      have hτ : t - r ∈ Ioo (0 : ℝ) t := ⟨by linarith [hr.2], by linarith [hr.1]⟩
      have d1 := hev.classicalSol.time_deriv x r hr
      have d2 : HasDerivAt (fun r' => ouSg Q ν (t - r') f x)
          (-(ul5A Q ν (ouSg Q ν (t - r) f) x)) r := by
        have h := ou_forward_hasDerivAt Q H.hν.le hfcb.1 (M := cbNorm 2 f)
          (fun i hi y => ul3_cb_apply hfcb hi y) hτ.1 x
        refine (h.scomp r ((hasDerivAt_id r).const_sub t)).congr_deriv ?_
        simp [ul5A]
      have d3 : HasDerivAt (fun r' => ulD Q ν s M ρ c w (t - r') (t - r') x)
          (-(ul5A Q ν (fun y => ulD Q ν s M ρ c w (t - r) (t - r) y) x +
            ulPert s M ρ c (w (t - r)) x)) r := by
        have h := ul5_V_hasDerivAt H Q hwU hτ x
        refine (h.scomp r ((hasDerivAt_id r).const_sub t)).congr_deriv ?_
        simp
      have hd := (d1.sub d2).sub d3
      refine hd.congr_deriv ?_
      have hu2 : ContDiff ℝ 2 (u r) := (hev.mem r ⟨hr.1.le, hr.2.le⟩).1
      have hP2 : ContDiff ℝ 2 (ouSg Q ν (t - r) f) :=
        ouSg_contDiff_two Q ν (t - r) k θ H.hθ H.hk2 hfc
      have hV2 : ContDiff ℝ 2 (fun y => ulD Q ν s M ρ c w (t - r) (t - r) y) :=
        (hV.mem (t - r) ⟨hτ.1.le, hτ.2.le⟩).1
      have e1 := ul5_A_sub Q ν (hu2.sub hP2) hV2 x
      have e2 := ul5_A_sub Q ν hu2 hP2 x
      have hzr : ul5A Q ν (zt r) x = ul5A Q ν (u r) x - ul5A Q ν (ouSg Q ν (t - r) f) x -
          ul5A Q ν (fun y => ulD Q ν s M ρ c w (t - r) (t - r) y) x := by
        rw [← e2]; exact e1
      show _ = -(ul5A Q ν (zt r) x)
      rw [hzr, ul5_gen_fixed, hwr]
      ring
  have hzero : IsLocalBackwardSolution (fun _ => ν) (fun _ x => -(Torus.matVec Q x)) t
      (fun _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) := by
    refine ⟨fun _ _ => contDiff_const, ⟨0, fun _ _ _ => by simp⟩, continuous_const, rfl, ?_⟩
    intro x r hr
    simp only [InnerProductSpace.laplacian_const, gradient_fun_const]
    simpa using hasDerivAt_const r (0 : ℝ)
  have hbb : ∀ r ∈ Icc (0 : ℝ) t, ∀ x : Euc d, -(Torus.matVec Q x) =
      -Torus.matVec Q x - (fun _ : ℝ => (0 : Euc d)) r + (fun (_ : ℝ) (_ : Euc d) => (0 : Euc d)) r x :=
    fun r _ x => by simp
  have hsol' := ul2_solution_congr (b' := fun r x => -Torus.matVec Q x - (fun _ : ℝ => (0 : Euc d)) r +
    (fun (_ : ℝ) (_ : Euc d) => (0 : Euc d)) r x) ht hbb (fun r _ => rfl) hsol
  have hzero' := ul2_solution_congr (b' := fun r x => -Torus.matVec Q x - (fun _ : ℝ => (0 : Euc d)) r +
    (fun (_ : ℝ) (_ : Euc d) => (0 : Euc d)) r x) ht hbb (fun r _ => rfl) hzero
  have key := lc_unique (Q := Q) (c := fun _ => (0 : Euc d)) (B := fun _ _ => (0 : Euc d))
    (ν := fun _ => ν) (νstar := ν) (Λc := 0) (ΛB := 0) ht (fun r _ => ⟨H.hν.le, le_rfl⟩)
    (fun r _ => by simp) (fun r _ x => by simp) hsol' hzero'
  intro τ hτ x
  have h0 := key (t - τ) (hflip τ hτ) x
  simp only [hzt, sub_sub_cancel] at h0
  have : u (t - τ) x = w τ x := rfl
  rw [this]
  show w τ x = _
  have h1 : w τ x - ouSg Q ν τ f x - ulD Q ν s M ρ c w τ τ x = 0 := h0
  have h2 : ulD Q ν s M ρ c w τ τ x = ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ)
      (ulPert s M ρ c (w σ)) x := rfl
  linarith

end Uniq

/-- **`ul_evolution_unique`.**  Two backward evolutions with the same terminal datum agree on `[0,t]`. -/
theorem ul_evolution_unique {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ)
    (k : ℕ) (hk : (4 : ℝ) + (d : ℝ) / 2 < k) (ν : ℝ) (hν : 0 < ν)
    (Q M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ)
    (c : Euc d → Euc d) (hc : IsSmoothBounded c) {t : ℝ} (ht : 0 ≤ t) {f : Euc d → ℝ}
    {u u' : ℝ → Euc d → ℝ}
    (hu : IsUlBackwardEvolution θ k (fixedViscosityCoeff s M Q ν c ρ) t f u)
    (hu' : IsUlBackwardEvolution θ k (fixedViscosityCoeff s M Q ν c ρ) t f u') :
    ∀ r ∈ Icc (0 : ℝ) t, u r = u' r := by
  have H : UlHyp s M ρ c ν k θ := ⟨hs0, hsd, hρ, hc, hν, hk, hθ⟩
  have m1 := ul5_mild_of_evolution H Q ht hu
  have m2 := ul5_mild_of_evolution H Q ht hu'
  have h1 : UlReg k θ t (fun τ => u (t - τ)) := ul5_reg_flip ⟨hu.mem, hu.cont⟩
  have h2 : UlReg k θ t (fun τ => u' (t - τ)) := ul5_reg_flip ⟨hu'.mem, hu'.cont⟩
  have key := ul_mild_unique hs0 hsd θ hθ k hk t ν hν Q M ρ hρ c hc f (fun τ => u (t - τ))
    (fun τ => u' (t - τ)) h1.mem h2.mem h1.cont h2.cont m1 m2
  intro r hr
  have := key (t - r) ⟨sub_nonneg.2 hr.2, sub_le_self t hr.1⟩
  simpa only [sub_sub_cancel] using this

end HRS.MS.Ul
