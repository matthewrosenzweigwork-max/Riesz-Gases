import HRS.MC.SEdgeB2a
import HRS.MC.Sec7Vocab
import HRS.Equilibrium.QuadraticLimit.GibbsAuxG
import HRS.Equilibrium.QuadraticLimit.Features
import HRS.Equilibrium.LocalDivMain
import HRS.Equilibrium.FieldSingAux

/-!
# FC-G, part 2: the difference kernel and the `L^2` bound of its energy under the product law

* `hTransport` of a smooth test is a symmetric measurable kernel with envelope `B_h (g + c)`;
* finite-rank smooth kernels are symmetric and measurable;
* `E_{mu^N} |N F_N^k|^2 <= 7 iint k^2` (`q08_energy_L2` plus the centring).
Packet prefix `fcg`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.FCG

open HRS HRS.Sec7

variable {d : ℕ}

theorem fcg_hT_eq {s : ℝ} {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    hTransport d s φ = Q66.q66_hv d s (fun j => Torus.partialDeriv j φ) := by
  funext x y
  rw [HRS.LocalDivAux.hTransport_eq s φ hφ]
  rfl

theorem fcg_hT_meas_symm {s : ℝ} (hsd : s < d) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Measurable (Function.uncurry (hTransport d s φ)) ∧ ∀ x y, hTransport d s φ x y = hTransport d s φ y x := by
  rw [fcg_hT_eq hφ]
  exact ⟨Q66.q66_hv_measurable hsd fun j => HRS.StaticLimitAux.continuous_of_smooth
    (HRS.LocalDivAux.isSmooth_partialDeriv hφ j), Q66.q66_hv_symm hsd _⟩

theorem fcg_hT_env (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {c : ℝ}
    (hc : EnvelopeConst (d := d) s c) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ Bh : ℝ, 0 ≤ Bh ∧ ∀ x y : Torus d, x ≠ y →
      |hTransport d s φ x y| ≤ Bh * (periodicRiesz d s (x - y) + c) := by
  obtain ⟨B', c', hc', hB'⟩ := HRS.MC.SEdge.B2a.b2a_main hd hs0 hs
    (v := fun j => Torus.partialDeriv j φ) fun j => HRS.LocalDivAux.isSmooth_partialDeriv hφ j
  refine ⟨max B' 0 * (1 + |c' - c|), by positivity, fun x y hxy => ?_⟩
  have hg : 1 ≤ periodicRiesz d s (x - y) + c := hc _ (sub_ne_zero.2 hxy)
  have hg' : 1 ≤ periodicRiesz d s (x - y) + c' := hc' _ (sub_ne_zero.2 hxy)
  have h1 : periodicRiesz d s (x - y) + c' ≤ (1 + |c' - c|) * (periodicRiesz d s (x - y) + c) := by
    have := le_abs_self (c' - c)
    nlinarith [abs_nonneg (c' - c)]
  rw [fcg_hT_eq hφ]
  calc |Q66.q66_hv d s (fun j => Torus.partialDeriv j φ) x y|
      ≤ B' * (periodicRiesz d s (x - y) + c') := hB' x y hxy
    _ ≤ max B' 0 * (periodicRiesz d s (x - y) + c') :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    _ ≤ max B' 0 * ((1 + |c' - c|) * (periodicRiesz d s (x - y) + c)) :=
        mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
    _ = _ := by ring

theorem fcg_finrank_meas_symm {h : Torus d → Torus d → ℝ} (hh : s7_IsFiniteRankSmooth h) :
    Measurable (Function.uncurry h) ∧ ∀ x y, h x y = h y x := by
  obtain ⟨n, f, c, hf, hc, hk⟩ := hh
  have hfc : ∀ i, Continuous (f i) := fun i => HRS.StaticLimitAux.continuous_of_smooth (hf i)
  refine ⟨?_, fun x y => ?_⟩
  · have e : Function.uncurry h = fun p : Torus d × Torus d =>
        ∑ i, ∑ j, c i j * f i p.1 * f j p.2 := by
      funext p; exact hk p.1 p.2
    rw [e]
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact (measurable_const.mul ((hfc i).measurable.comp measurable_fst)).mul
      ((hfc j).measurable.comp measurable_snd)
  · rw [hk x y, hk y x, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hc i j]; ring

/-- The difference kernel `h_L - h` : measurable, symmetric, with envelope. -/
theorem fcg_diff_kernel {s : ℝ} (hsd : s < (d : ℝ)) {c : ℝ}
    (hc : EnvelopeConst (d := d) s c) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {B Bh : ℝ}
    (hBh : ∀ x y : Torus d, x ≠ y → |hTransport d s φ x y| ≤ Bh * (periodicRiesz d s (x - y) + c))
    {hL : Torus d → Torus d → ℝ} (hLd : s7_IsFiniteRankSmooth hL)
    (hLB : ∀ x y, x ≠ y → |hL x y| ≤ B * (periodicRiesz d s (x - y) + c)) :
    Measurable (Function.uncurry fun x y => hL x y - hTransport d s φ x y) ∧
      (∀ x y, hL x y - hTransport d s φ x y = hL y x - hTransport d s φ y x) ∧
      ∀ x y, x ≠ y → |hL x y - hTransport d s φ x y| ≤
        (max B 0 + Bh) * (periodicRiesz d s (x - y) + c) := by
  obtain ⟨hm1, hs1⟩ := fcg_finrank_meas_symm hLd
  obtain ⟨hm2, hs2⟩ := fcg_hT_meas_symm hsd hφ
  refine ⟨hm1.sub hm2, fun x y => by rw [hs1 x y, hs2 x y], fun x y hxy => ?_⟩
  have hg : 1 ≤ periodicRiesz d s (x - y) + c := hc _ (sub_ne_zero.2 hxy)
  calc |hL x y - hTransport d s φ x y| ≤ |hL x y| + |hTransport d s φ x y| := abs_sub _ _
    _ ≤ B * (periodicRiesz d s (x - y) + c) + Bh * (periodicRiesz d s (x - y) + c) :=
        add_le_add (hLB x y hxy) (hBh x y hxy)
    _ ≤ max B 0 * (periodicRiesz d s (x - y) + c) + Bh * (periodicRiesz d s (x - y) + c) := by
        gcongr
        exact le_max_left _ _
    _ = _ := by ring

/-- `(∫ f)^2 ≤ ∫ f^2` for a probability measure. -/
theorem fcg_sq_integral_le {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    {f : α → ℝ} (hf : MemLp f 2 ν) : (∫ x, f x ∂ν) ^ 2 ≤ ∫ x, f x ^ 2 ∂ν := by
  have h := variance_eq_sub hf
  have h2 := variance_nonneg f ν
  simp only [Pi.pow_apply] at h
  linarith

/-- **`L^2` bound of the energy under the product law.** -/
theorem fcg_L2 (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {k : Torus d → Torus d → ℝ}
    (hm : Measurable (Function.uncurry k)) (hs : ∀ x y, k x y = k y x)
    (hk : Integrable (fun z : Torus d × Torus d => k z.1 z.2 ^ 2) (μ.prod μ)) (N : ℕ) (hN : 1 ≤ N) :
    Measurable (fun X : Config d N => (N : ℝ) * modulatedEnergy k X μ) ∧
    ∫⁻ X : Config d N, ENNReal.ofReal (|(N : ℝ) * modulatedEnergy k X μ| ^ (2 : ℕ))
        ∂(Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal (7 * ∫ z : Torus d × Torus d, k z.1 z.2 ^ 2 ∂(μ.prod μ)) := by
  set S : ℝ := ∫ z : Torus d × Torus d, k z.1 z.2 ^ 2 ∂(μ.prod μ) with hS
  have hS0 : 0 ≤ S := integral_nonneg fun z => sq_nonneg _
  set J : ℝ := ∫ x, ∫ y, k x y ∂μ ∂μ with hJ
  set π : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hπ
  -- the centred energy
  have hYmem : MemLp (HRS.Q08.q08e_Z μ k : Config d N → ℝ) 2 π :=
    HRS.Q08.q08gl_Z_memLp μ k hm hk hs N hN
  have hYeq : ∀ X : Config d N, HRS.Q08.q08e_Z μ k X = (N : ℝ) * modulatedEnergy k X μ + (1 / 2) * J :=
    fun X => rfl
  have hYsq := HRS.Q08.q08_energy_L2 μ k hm hs hk N hN
  have hZmem : MemLp (fun X : Config d N => (N : ℝ) * modulatedEnergy k X μ) 2 π := by
    have := hYmem.sub (memLp_const ((1 / 2) * J))
    refine this.ae_eq (Filter.Eventually.of_forall fun X => ?_)
    simp only [Pi.sub_apply, hYeq]; ring
  -- measurability
  have hmeas : Measurable (fun X : Config d N => (N : ℝ) * modulatedEnergy k X μ) := by
    have ha : Measurable (HRS.Q08.q08e_a μ k) := HRS.Q08.q08e_a_meas' μ k hm hk
    unfold modulatedEnergy
    refine measurable_const.mul ((Measurable.sub ?_ ?_).add measurable_const)
    · refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
      exact (hm.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) :
        Measurable fun X : Config d N => Function.uncurry k (X i, X j))
    · refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
      exact ha.comp (measurable_pi_apply i)
  refine ⟨hmeas, ?_⟩
  -- `J^2 ≤ S`
  have hfmem : MemLp (fun z : Torus d × Torus d => k z.1 z.2) 2 (μ.prod μ) := by
    refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hk
  have hJeq : J = ∫ z : Torus d × Torus d, k z.1 z.2 ∂(μ.prod μ) := by
    rw [hJ, integral_prod _ (hfmem.integrable one_le_two)]
  have hJsq : J ^ 2 ≤ S := by
    rw [hJeq]; exact fcg_sq_integral_le (μ.prod μ) hfmem
  -- pointwise bound and integration
  set Zf : Config d N → ℝ := fun X => (N : ℝ) * modulatedEnergy k X μ with hZf
  have hZi : Integrable (fun X => Zf X ^ 2) π := hZmem.integrable_sq
  have hYi : Integrable (fun X => HRS.Q08.q08e_Z μ k X ^ 2) π := hYmem.integrable_sq
  have hpt : ∀ X, Zf X ^ 2 ≤ 2 * HRS.Q08.q08e_Z μ k X ^ 2 + J ^ 2 / 2 := fun X => by
    have : Zf X = HRS.Q08.q08e_Z μ k X - (1 / 2) * J := by rw [hYeq X]; simp only [hZf]; ring
    rw [this]; nlinarith [sq_nonneg (HRS.Q08.q08e_Z μ k X + (1 / 2) * J)]
  have hint : ∫ X, Zf X ^ 2 ∂π ≤ 7 * S := by
    calc ∫ X, Zf X ^ 2 ∂π ≤ ∫ X, (2 * HRS.Q08.q08e_Z μ k X ^ 2 + J ^ 2 / 2) ∂π :=
          integral_mono hZi ((hYi.const_mul 2).add (integrable_const _)) hpt
      _ = 2 * ∫ X, HRS.Q08.q08e_Z μ k X ^ 2 ∂π + J ^ 2 / 2 := by
          rw [integral_add (hYi.const_mul 2) (integrable_const _), integral_const_mul]
          simp
      _ ≤ 2 * (3 * S) + S / 2 := by
          have h1 : ∫ X, HRS.Q08.q08e_Z μ k X ^ 2 ∂π ≤ 3 * S := by
            have hS' : ∫ x, ∫ y, k x y ^ 2 ∂μ ∂μ = S := by rw [hS, integral_prod _ hk]
            have := hYsq
            rw [hS'] at this
            exact this
          linarith
      _ ≤ 7 * S := by linarith
  have hconv : ∫⁻ X, ENNReal.ofReal (|Zf X| ^ (2 : ℕ)) ∂π = ENNReal.ofReal (∫ X, Zf X ^ 2 ∂π) := by
    rw [ofReal_integral_eq_lintegral_ofReal hZi (Filter.Eventually.of_forall fun X => sq_nonneg _)]
    refine lintegral_congr fun X => ?_
    rw [sq_abs]
  show ∫⁻ X, ENNReal.ofReal (|Zf X| ^ (2 : ℕ)) ∂π ≤ _
  rw [hconv]
  exact ENNReal.ofReal_le_ofReal hint

end HRS.MC.Sec7.FCG

end
