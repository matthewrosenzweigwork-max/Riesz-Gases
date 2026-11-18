import HRS.Sections.Sec7Fields
import HRS.Energy.Commutator.AbsConv
import HRS.Dynamics.InitialData
import HRS.Kernel.D1

/-!
# Packet WCI: the Wick coefficients do not see the density (`l2cs_wickCoeff_indep`)

Route.  Write `h = hTransport d s f`, `m = withDensityReal ρ`, `e_k = realMode k`.  Then
`canonicalCenter m h x y = h x y - a(x) - b(y) + c` with `a(x) = ∫ h(x,·) dm`, `b(y) = ∫ h(·,y) dm` and a
constant `c`.  The Lebesgue integrals of `e_k` and `e_l` vanish, so every term except `∫∫ h e_k(x) e_l(y)`
drops out, and `wickCoeff m h k l = ∫ e_k(x) (∫ h(x,y) e_l(y) dy) dx` does not mention `m`.
Integrability: `|h(x,y)| ≤ K(|x-y|^{-s} + 1)` (the commutator bound with the Lipschitz constant of `∇f`,
`s < d`), and `m ≤ B · dx` transports the bounds to `a` and `b`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace MC

namespace WCI

open HRS.Sec7

variable {d : ℕ}

/-- The integrable majorant `z ↦ K (‖z‖^{-s} + 1)` of the pair kernel. -/
def wciG (s K : ℝ) (z : Torus d) : ℝ := K * (‖z‖ ^ (-s) + 1)

theorem wciG_nonneg {s K : ℝ} (hK : 0 ≤ K) (z : Torus d) : 0 ≤ wciG s K z :=
  mul_nonneg hK (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one)

theorem wciG_integrable {s : ℝ} (hd : 0 < d) (hsd : s < d) (K : ℝ) :
    Integrable (wciG (d := d) s K) volume :=
  ((HRS.KernelGrad.integrable_norm_rpow_neg hd hsd).add (integrable_const 1)).const_mul K

theorem wci_realMode_continuous (k : NonzeroLattice d) : Continuous (Torus.realMode k) := by
  unfold Torus.realMode
  split_ifs
  · exact continuous_const.mul (Torus.continuous_cosMode k.1)
  · exact continuous_const.mul (Complex.continuous_im.comp (Torus.continuous_mode k.1))

theorem wci_grad_lip {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    ∃ L : ℝ, 0 ≤ L ∧ HRS.IsLipschitzVF L (Torus.grad f) := by
  obtain ⟨L, hL0, hL⟩ := HRS.LatticeEnergyAux.lipschitz_a (HRS.KernelD1Aux.isSmooth_grad hf)
  exact ⟨L, hL0, fun x y => hL x y⟩

/-- Pointwise majorant of the pair kernel `h_f = hTransport d s f` for a smooth `f`. -/
theorem wci_hT_bound {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : Torus d, ‖hTransport d s f x y‖ ≤ wciG s K (x - y) := by
  have hd : 1 ≤ d := by
    have h0 : (0 : ℝ) < d := by linarith
    have h1 : 0 < d := by exact_mod_cast h0
    exact h1
  obtain ⟨L, hL0, hLip⟩ := wci_grad_lip hf
  obtain ⟨C, hC0, hC⟩ := HRS.Commutator.commKernel_bound hd hs0 hsd
  refine ⟨C * L, mul_nonneg hC0 hL0, fun x y => ?_⟩
  rw [Real.norm_eq_abs]
  unfold wciG
  by_cases hxy : x = y
  · subst hxy
    have h0 : hTransport d s f x x = 0 := by unfold hTransport; simp
    rw [h0, abs_zero]
    exact mul_nonneg (mul_nonneg hC0 hL0) (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one)
  · have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have h1 := hC L (Torus.grad f) hL0 hLip x y hxy
    have hT : hTransport d s f x y = HRS.commKernel (periodicRieszGrad d s) (Torus.grad f) x y := by
      unfold HRS.commKernel hTransport
      rw [if_neg hxy]
    rw [hT]
    have h2 : HRS.KernelGrad.tdist x y ^ (-s) ≤ ‖x - y‖ ^ (-s) := by
      rw [HRS.KernelGrad.tdist_eq_sub_zero]
      exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hz) (HRS.KernelGrad.norm_le_tdist _)
        (by linarith)
    calc |HRS.commKernel (periodicRieszGrad d s) (Torus.grad f) x y|
        ≤ C * L * (HRS.KernelGrad.tdist x y ^ (-s) + 1) := h1
      _ ≤ C * L * (‖x - y‖ ^ (-s) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC0 hL0)

theorem wci_hT_measurable {s : ℝ} (hsd : s < d) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    Measurable (fun p : Torus d × Torus d => hTransport d s f p.1 p.2) := by
  obtain ⟨L, hL0, hLip⟩ := wci_grad_lip hf
  have hc : Continuous (Torus.grad f) := HRS.Commutator.IsLipschitzVF.continuous hL0 hLip
  have hc' := hc.measurable
  show Measurable (fun p : Torus d × Torus d =>
    inner ℝ (Torus.grad f p.1 - Torus.grad f p.2) (periodicRieszGrad d s (p.1 - p.2)))
  exact Measurable.inner ((hc'.comp measurable_fst).sub (hc'.comp measurable_snd))
    ((HRS.KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd))

/-- Core identity: for any finite measure `m` whose integrals of `Lebesgue`-integrable functions are
dominated by `B` times the Lebesgue integral, the Wick coefficient of the `m`-centred kernel equals the
uncentred double integral. -/
theorem wci_core {s K B : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hK : 0 ≤ K) (hB0 : 0 ≤ B)
    {m : Measure (Torus d)} [IsFiniteMeasure m]
    (hmI : ∀ g : Torus d → ℝ, Integrable g volume → Integrable g m)
    (hmB : ∀ g : Torus d → ℝ, (∀ y, 0 ≤ g y) → Integrable g volume → ∫ y, g y ∂m ≤ B * ∫ y, g y)
    {h : Torus d → Torus d → ℝ} (hhm : Measurable (fun p : Torus d × Torus d => h p.1 p.2))
    (hhb : ∀ x y, ‖h x y‖ ≤ wciG s K (x - y)) (k l : NonzeroLattice d) :
    ∫ x, ∫ y, canonicalCenter m h x y * Torus.realMode k x * Torus.realMode l y =
      ∫ x, Torus.realMode k x * ∫ y, h x y * Torus.realMode l y := by
  have hd : 0 < d := by
    have h0 : (0 : ℝ) < d := by linarith
    exact_mod_cast h0
  set I : ℝ := ∫ z, wciG s K z with hIdef
  have hI0 : 0 ≤ I := integral_nonneg fun z => wciG_nonneg hK z
  have hGi : Integrable (wciG (d := d) s K) volume := wciG_integrable hd hsd K
  have hGx : ∀ x : Torus d, Integrable (fun y => wciG s K (x - y)) volume :=
    fun x => hGi.comp_sub_left x
  have hGy : ∀ y : Torus d, Integrable (fun x => wciG s K (x - y)) volume :=
    fun y => hGi.comp_sub_right y
  have hIx : ∀ x : Torus d, ∫ y, wciG s K (x - y) = I :=
    fun x => integral_sub_left_eq_self (wciG s K) volume x
  have hIy : ∀ y : Torus d, ∫ x, wciG s K (x - y) = I :=
    fun y => integral_sub_right_eq_self (wciG s K) y
  have hkc : Continuous (Torus.realMode k) := wci_realMode_continuous k
  have hlc : Continuous (Torus.realMode l) := wci_realMode_continuous l
  have hke : ∀ x, ‖Torus.realMode k x‖ ≤ Real.sqrt 2 := fun x => by
    rw [Real.norm_eq_abs]; exact Torus.abs_realMode_le k x
  have hle : ∀ y, ‖Torus.realMode l y‖ ≤ Real.sqrt 2 := fun y => by
    rw [Real.norm_eq_abs]; exact Torus.abs_realMode_le l y
  have hkint : Integrable (Torus.realMode k) volume :=
    hkc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlint : Integrable (Torus.realMode l) volume :=
    hlc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hslice : ∀ x : Torus d, Measurable (fun y => h x y) :=
    fun x => hhm.comp (measurable_const.prodMk measurable_id)
  -- the `y`-integrand `h(x,y) e_l(y)` is dominated by `√2 K(|x-y|^{-s}+1)`
  have hE : ∀ x y, ‖h x y * Torus.realMode l y‖ ≤ Real.sqrt 2 * wciG s K (x - y) := fun x y => by
    rw [norm_mul, mul_comm (Real.sqrt 2)]
    exact mul_le_mul (hhb x y) (hle y) (norm_nonneg _) (wciG_nonneg hK _)
  have hEint : ∀ x, Integrable (fun y => h x y * Torus.realMode l y) volume := fun x =>
    Integrable.mono' ((hGx x).const_mul (Real.sqrt 2))
      ((hslice x).mul hlc.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hE x y)
  -- `x ↦ ∫ h(x,y) e_l(y) dy` is measurable and bounded
  have hPm : Measurable (fun x => ∫ y, h x y * Torus.realMode l y) := by
    have hS : StronglyMeasurable (fun p : Torus d × Torus d => h p.1 p.2 * Torus.realMode l p.2) :=
      (hhm.mul (hlc.measurable.comp measurable_snd)).stronglyMeasurable
    exact (hS.integral_prod_right' (ν := volume)).measurable
  have hPb : ∀ x, ‖∫ y, h x y * Torus.realMode l y‖ ≤ Real.sqrt 2 * I := fun x => by
    have h1 := norm_integral_le_of_norm_le (f := fun y => h x y * Torus.realMode l y)
      ((hGx x).const_mul (Real.sqrt 2)) (Filter.Eventually.of_forall fun y => hE x y)
    rw [integral_const_mul, hIx x] at h1
    exact h1
  -- `y ↦ ∫ h(x,y) dm(x)` is measurable and bounded (uses `m ≤ B dx`)
  have hbb : ∀ y, ‖∫ x, h x y ∂m‖ ≤ B * I := fun y => by
    have h1 := norm_integral_le_of_norm_le (f := fun x => h x y)
      (g := fun x => wciG s K (x - y)) (hmI _ (hGy y)) (Filter.Eventually.of_forall fun x => hhb x y)
    have h2 := hmB (fun x => wciG s K (x - y)) (fun x => wciG_nonneg hK _) (hGy y)
    rw [hIy y] at h2
    exact h1.trans h2
  have hbm : Measurable (fun y => ∫ x, h x y ∂m) := by
    have hS : StronglyMeasurable (fun p : Torus d × Torus d => h p.1 p.2) :=
      hhm.stronglyMeasurable
    exact (hS.integral_prod_left' (μ := m)).measurable
  have hJint : Integrable (fun y => (∫ x, h x y ∂m) * Torus.realMode l y) volume := by
    refine Integrable.mono' (integrable_const (B * I * Real.sqrt 2))
      (hbm.mul hlc.measurable).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul]
    exact mul_le_mul (hbb y) (hle y) (norm_nonneg _) (mul_nonneg hB0 hI0)
  -- inner integral: the centring terms vanish against `e_l`
  have hinner : ∀ x : Torus d,
      ∫ y, canonicalCenter m h x y * Torus.realMode k x * Torus.realMode l y =
        Torus.realMode k x * (∫ y, h x y * Torus.realMode l y) -
          Torus.realMode k x * ∫ y, (∫ x', h x' y ∂m) * Torus.realMode l y := by
    intro x
    have hfun : (fun y => canonicalCenter m h x y * Torus.realMode k x * Torus.realMode l y) =
        fun y => ((Torus.realMode k x * (h x y * Torus.realMode l y) -
            Torus.realMode k x * ((∫ x', h x' y ∂m) * Torus.realMode l y)) -
          ((∫ y', h x y' ∂m) * Torus.realMode k x) * Torus.realMode l y) +
          ((∫ x', ∫ y', h x' y' ∂m ∂m) * Torus.realMode k x) * Torus.realMode l y := by
      funext y
      unfold canonicalCenter
      ring
    rw [hfun]
    have i1 : Integrable (fun y => Torus.realMode k x * (h x y * Torus.realMode l y)) volume :=
      (hEint x).const_mul _
    have i2 : Integrable
        (fun y => Torus.realMode k x * ((∫ x', h x' y ∂m) * Torus.realMode l y)) volume :=
      hJint.const_mul _
    have i3 : Integrable
        (fun y => ((∫ y', h x y' ∂m) * Torus.realMode k x) * Torus.realMode l y) volume :=
      hlint.const_mul _
    have i4 : Integrable
        (fun y => ((∫ x', ∫ y', h x' y' ∂m ∂m) * Torus.realMode k x) * Torus.realMode l y) volume :=
      hlint.const_mul _
    have j12 : Integrable (fun y => Torus.realMode k x * (h x y * Torus.realMode l y) -
        Torus.realMode k x * ((∫ x', h x' y ∂m) * Torus.realMode l y)) volume := i1.sub i2
    have j123 : Integrable (fun y => (Torus.realMode k x * (h x y * Torus.realMode l y) -
        Torus.realMode k x * ((∫ x', h x' y ∂m) * Torus.realMode l y)) -
        ((∫ y', h x y' ∂m) * Torus.realMode k x) * Torus.realMode l y) volume := j12.sub i3
    rw [integral_add j123 i4, integral_sub j12 i3, integral_sub i1 i2]
    simp only [integral_const_mul, Torus.integral_realMode l, mul_zero, sub_zero, add_zero]
  -- outer integral
  have hPint : Integrable
      (fun x => Torus.realMode k x * ∫ y, h x y * Torus.realMode l y) volume := by
    refine Integrable.mono' (integrable_const (Real.sqrt 2 * (Real.sqrt 2 * I)))
      (hkc.measurable.mul hPm).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul (hke x) (hPb x) (norm_nonneg _) (Real.sqrt_nonneg _)
  have hJc : Integrable
      (fun x => Torus.realMode k x * ∫ y, (∫ x', h x' y ∂m) * Torus.realMode l y) volume :=
    hkint.mul_const _
  simp only [hinner]
  rw [integral_sub hPint hJc, integral_mul_const, Torus.integral_realMode k, zero_mul, sub_zero]

theorem wci_wick_eq {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {f : Torus d → ℝ} (hf : Torus.IsSmooth f)
    {ρ : Torus d → ℝ} {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) (k l : NonzeroLattice d) :
    wickCoeff (withDensityReal ρ) (hTransport d s f) k l =
      ∫ x, Torus.realMode k x * ∫ y, hTransport d s f x y * Torus.realMode l y := by
  obtain ⟨K, hK0, hK⟩ := wci_hT_bound hs0 hsd hf
  have hB0 : 0 ≤ max Λ 0 := le_max_right _ _
  have hΛB : ∀ x, ρ x ≤ max Λ 0 := fun x => (hΛ x).trans (le_max_left _ _)
  haveI := HRS.Commutator.absConv_isFiniteMeasure hΛB
  unfold wickCoeff
  exact wci_core hs0 hsd hK0 hB0 (fun g hg => HRS.Commutator.absConv_integrable_mu hΛB hg)
    (fun g hg0 hg => HRS.Commutator.absConv_integral_mu_le hΛB hB0 hg0 hg)
    (wci_hT_measurable hsd hf) hK k l

/-- (Packet WCI, `l2cs_wickCoeff_indep`.)  The Wick coefficients `ĥ°_{kl} = ∬ h°(x,y)e_k(x)e_l(y)dxdy` of the
`μ`-centred pair kernel do NOT depend on `μ`, for `h = h_{∇f}` (`hTransport`), `0 ≤ s < d`, because the centring
subtracts functions of one variable only and the modes have Lebesgue mean zero.  Hence, in the formalisation,
`IsWickQuadraticField s P η μ B` does not depend on `μ`, and the 'Wick-centring mismatch of `ρ^t` vs `ρ_β`' recorded in
`PROOF_QUEUE.md` (2026-10-17 entry, item (4)) disappears: the matrices `A^k(ρ^t)` and `A^k(ρ_β)` of `QRelAux1.lean` are the
same matrix.  Route: expand `canonicalCenter`; `∫ (∫ h x y' ∂μ) e_k x e_l y dy = (∫h x y'∂μ e_k x)·∫ e_l = 0`
(`Torus.integral_realMode`); integrability of `h_{∇f}(x,·)` w.r.t. `μ` and of the products from `|h_{∇f}(x,y)| ≤
C|x-y|^{-s}` near the diagonal, bounded `ρ`.  The diagonal is a null set (junk value of `periodicRieszGrad` at `0`).
Size ~150 lines. -/
theorem wci_proof (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (ρ ρ' : Torus d → ℝ)
    (hρ : IsProbDensity ρ) (hρ' : IsProbDensity ρ') (Mρ : ℝ) (hMρ : ∀ x, ρ x ≤ Mρ) (hMρ' : ∀ x, ρ' x ≤ Mρ)
    (f : Torus d → ℝ) (hf : Torus.IsSmooth f)
    (k l : NonzeroLattice d) :
    wickCoeff (withDensityReal ρ) (hTransport d s f) k l =
      wickCoeff (withDensityReal ρ') (hTransport d s f) k l := by
  rw [wci_wick_eq hs0 hsd hf hMρ k l, wci_wick_eq hs0 hsd hf hMρ' k l]

end WCI

end MC

end HRS

end
