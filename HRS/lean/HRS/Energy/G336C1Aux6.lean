import HRS.Energy.G336C1Aux5

/-!
# G336C1, helper file 6: integral Grönwall and the deterministic zero-temperature bound

(1) `g336c1_gronwall_int`: if `φ` is continuous on `[0,T]` and `φ t ≤ φ 0 + κ ∫_0^t φ` there, then
`φ t ≤ φ 0 e^{κ t}` (through `le_gronwallBound_of_liminf_deriv_right_le`).
(2) `g336c1_det_gronwall`: along the deterministic path, from the limit identity, the sign of the microscopic term
and the commutator/coercivity bounds, `φ(t) ≤ e^{(C/2) T Λ'} φ(0)` with `φ = F + o_N`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem g336c1_gronwall_int {φ : ℝ → ℝ} {T κ : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ)
    (hφ : ContinuousOn φ (Set.Icc 0 T))
    (hineq : ∀ t ∈ Set.Icc 0 T, φ t ≤ φ 0 + κ * ∫ r in (0 : ℝ)..t, φ r) :
    ∀ t ∈ Set.Icc 0 T, φ t ≤ φ 0 * Real.exp (κ * t) := by
  set cl : ℝ → ℝ := fun r => max 0 (min r T) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hclm : ∀ r, cl r ∈ Set.Icc (0 : ℝ) T := fun r => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hcle : ∀ r ∈ Set.Icc (0 : ℝ) T, cl r = r := fun r hr => by
    simp only [hcl]; rw [min_eq_left hr.2]; exact max_eq_right hr.1
  set φt : ℝ → ℝ := fun r => φ (cl r) with hφt
  have hφtc : Continuous φt := hφ.comp_continuous hclc hclm
  set G : ℝ → ℝ := fun t => φ 0 + κ * ∫ r in (0 : ℝ)..t, φt r with hG
  have hGd : ∀ x, HasDerivAt G (κ * φt x) x := fun x => by
    have := (hφtc.integral_hasStrictDerivAt 0 x).hasDerivAt
    exact (this.const_mul κ).const_add (φ 0)
  have hGφ : ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ G t := by
    intro t ht
    have := hineq t ht
    have e : ∫ r in (0 : ℝ)..t, φt r = ∫ r in (0 : ℝ)..t, φ r := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Set.uIcc_of_le ht.1] at hr
      simp only [hφt]
      rw [hcle r ⟨hr.1, hr.2.trans ht.2⟩]
    simp only [hG]
    rw [e]
    exact this
  have key := le_gronwallBound_of_liminf_deriv_right_le (f := G) (f' := fun x => κ * φt x)
    (δ := φ 0) (K := κ) (ε := 0) (a := 0) (b := T)
    (fun x _ => (hGd x).continuousAt.continuousWithinAt)
    (fun x _ r hr => (hGd x).hasDerivWithinAt.liminf_right_slope_le hr)
    (by simp [hG]) (fun x hx => by
      have h1 : φt x = φ x := by simp only [hφt]; rw [hcle x ⟨hx.1, hx.2.le⟩]
      have h2 := hGφ x ⟨hx.1, hx.2.le⟩
      rw [h1]
      nlinarith)
  intro t ht
  have := key t ht
  rw [gronwallBound_ε0, sub_zero] at this
  exact (hGφ t ht).trans this

theorem g336c1_det_gronwall (hd : 1 ≤ d) (D : DynData d) (hinvβ : D.invβ = 0)
    (hS : Torus.SymNonpos D.M) (hN : 2 ≤ N) (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 ≤ T)
    {ρ : ℝ → Torus d → ℝ} {Λ : ℝ} (hmf : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF 3 Λ T ρ)
    {Λ' : ℝ} (hΛ' : ∀ r ∈ Set.Icc 0 T, HasTransportBound d D.s (meanFieldDrift D (ρ r)) Λ')
    {Y : ℝ≥0 → Fin N → Euc d} (hp : G336C1Path D T Y) {C₀ C : ℝ} (hC : 0 < C)
    (hφ0 : ∀ r ∈ Set.Icc 0 T,
      0 ≤ rieszEnergy d D.s (g336c1_x Y r) (withDensityReal (ρ r)) + oNΛ d D.s C₀ Λ N)
    (hcomm : ∀ r ∈ Set.Icc 0 T,
      |commQuantity d D.s (meanFieldDrift D (ρ r)) (g336c1_x Y r) (withDensityReal (ρ r))| ≤
        C * Λ' * (rieszEnergy d D.s (g336c1_x Y r) (withDensityReal (ρ r)) + oNΛ d D.s C₀ Λ N)) :
    ∀ t ∈ Set.Icc 0 T,
      rieszEnergy d D.s (g336c1_x Y t) (withDensityReal (ρ t)) + oNΛ d D.s C₀ Λ N ≤
        Real.exp (C / 2 * T * Λ') *
          (rieszEnergy d D.s (g336c1_x Y 0) (withDensityReal (ρ 0)) + oNΛ d D.s C₀ Λ N) := by
  have h0T : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hΛ'0 : 0 ≤ Λ' := (hΛ' 0 h0T).nonneg
  have hLip : ∀ r ∈ Set.Icc 0 T, IsLipschitzVF Λ' (meanFieldDrift D (ρ r)) := by
    intro r hr x y
    obtain ⟨L, F, hL, hF, hlip, -, hK⟩ := hΛ' r hr
    have hLK : L ≤ Λ' := by split_ifs at hK <;> linarith
    exact (hlip x y).trans (mul_le_mul_of_nonneg_right hLK (KernelGrad.tdist_nonneg _ _))
  obtain ⟨B, hmeas, hbd, hid⟩ := g336c1_limit_identity hd D hinvβ hN hV hT hmf hreg hΛ'0 hLip hp
  set f : ℝ → ℝ := g336c1_f D ρ Y with hf
  set φ : ℝ → ℝ := fun r => rieszEnergy d D.s (g336c1_x Y r) (withDensityReal (ρ r)) +
    oNΛ d D.s C₀ Λ N with hφ
  have hfint : IntegrableOn f (Set.Icc 0 T) :=
    Integrable.of_bound hmeas B ((ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun r hr => by rw [Real.norm_eq_abs]; exact hbd r hr))
  have hφid : ∀ t ∈ Set.Icc (0 : ℝ) T, φ t = φ 0 + ∫ r in (0 : ℝ)..t, f r := by
    intro t ht
    have := hid t ht
    rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc, ← this]
    simp only [hφ]; ring
  have hφc : ContinuousOn φ (Set.Icc 0 T) := by
    have h1 : ContinuousOn (fun x => ∫ r in (0 : ℝ)..x, f r) (Set.uIcc 0 T) :=
      intervalIntegral.continuousOn_primitive_interval (by rwa [Set.uIcc_of_le hT])
    rw [Set.uIcc_of_le hT] at h1
    exact ((continuousOn_const.add h1)).congr fun t ht => hφid t ht
  set κ : ℝ := C / 2 * Λ' with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hfle : ∀ r ∈ Set.Icc (0 : ℝ) T, f r ≤ κ * φ r := by
    intro r hr
    have h1 := hcomm r hr
    have h2 := g336c1_microG_nonpos hS (ρ r) (g336c1_x Y r)
    simp only [hf, g336c1_f, hκ, hφ]
    have h3 := le_abs_self (commQuantity d D.s (meanFieldDrift D (ρ r)) (g336c1_x Y r) (withDensityReal (ρ r)))
    nlinarith
  have hineq : ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ φ 0 + κ * ∫ r in (0 : ℝ)..t, φ r := by
    intro t ht
    rw [hφid t ht]
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right ht.2
    have hfi : IntegrableOn f (Set.Icc 0 t) := hfint.mono_set hsub
    have hφi : IntegrableOn φ (Set.Icc 0 t) := (hφc.mono hsub).integrableOn_Icc
    have h1 : ∫ r in Set.Icc 0 t, f r ≤ ∫ r in Set.Icc 0 t, κ * φ r :=
      setIntegral_mono_on hfi (hφi.const_mul κ) measurableSet_Icc (fun r hr => hfle r (hsub hr))
    rw [integral_const_mul] at h1
    have e1 : ∫ r in (0 : ℝ)..t, f r = ∫ r in Set.Icc 0 t, f r := by
      rw [intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc]
    have e2 : ∫ r in (0 : ℝ)..t, φ r = ∫ r in Set.Icc 0 t, φ r := by
      rw [intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc]
    rw [e1, e2]
    linarith
  intro t ht
  have h1 := g336c1_gronwall_int hT hκ0 hφc hineq t ht
  have h2 : Real.exp (κ * t) ≤ Real.exp (C / 2 * T * Λ') := by
    apply Real.exp_le_exp.2
    simp only [hκ]
    have : C / 2 * Λ' * t ≤ C / 2 * Λ' * T := mul_le_mul_of_nonneg_left ht.2 (by positivity)
    linarith
  have h3 := hφ0 0 h0T
  calc φ t ≤ φ 0 * Real.exp (κ * t) := h1
    _ ≤ φ 0 * Real.exp (C / 2 * T * Λ') := mul_le_mul_of_nonneg_left h2 h3
    _ = _ := by simp only [hφ]; ring

end HRS
