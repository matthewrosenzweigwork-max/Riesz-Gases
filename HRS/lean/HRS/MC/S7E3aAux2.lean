import HRS.MC.S7E3aAux1

/-!
# Packets `s7_E3a/b`, file 2: the tail of the convolution operator along an orthonormal family

For `g in L^1`, even, and `rho <= Lambda`: for every `eta > 0` there is `N` such that for every finite
combination `w = sum_{i<L} x_i e_i` with `x_i = 0` for `i < N`,
`||Phi_g w||_{L^2(mu)} <= eta ||x||`.  (Compactness of the kernel operator `K_mu`, in the form needed.)
Route: split `g = clamp_n g + (g - clamp_n g)`; the bounded part is controlled by Bessel's inequality and
the tail of a convergent series (`e3_bounded_tail`), the remainder by the Schur bound `memLp_Phi`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.Sec7.E3Aux2

open HRS HRS.Sec7 HRS.MC.Sec7.E3Aux1

variable {d : ℕ} {ρ : Torus d → ℝ}

theorem e3_wnorm_sq [IsProbabilityMeasure (withDensityReal ρ)] {e : ℕ → Torus d → ℝ}
    (he : IsONBL2Zero (withDensityReal ρ) e) (L : ℕ) (x : ℕ → ℝ) :
    ∫ y, (∑ i ∈ Finset.range L, x i * e i y) ^ 2 ∂(withDensityReal ρ) =
      ∑ i ∈ Finset.range L, x i ^ 2 := by
  have hint : ∀ i j, Integrable (fun y => e i y * e j y) (withDensityReal ρ) :=
    fun i j => (he.memLp i).integrable_mul (he.memLp j)
  have h1 : ∀ y, (∑ i ∈ Finset.range L, x i * e i y) ^ 2 =
      ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, (x i * x j) * (e i y * e j y) := by
    intro y
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [h1]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
  have : ∀ j, ∫ y, (x i * x j) * (e i y * e j y) ∂(withDensityReal ρ) =
      (x i * x j) * (if i = j then 1 else 0) := by
    intro j
    rw [integral_const_mul]
    congr 1
    exact he.orthonormal i j
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  rw [if_pos (Finset.mem_range.1 hi)]
  ring

theorem e3_kt [IsProbabilityMeasure (withDensityReal ρ)] {e : ℕ → Torus d → ℝ}
    (he : IsONBL2Zero (withDensityReal ρ) e) {g : Torus d → ℝ} {Λ : ℝ}
    (H : PDE.MFLinear.KS g ρ Λ) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ (L : ℕ) (x : ℕ → ℝ), (∀ i, i < N → x i = 0) →
      eLpNorm (PDE.MFLinear.Phi g ρ (fun y => ∑ i ∈ Finset.range L, x i * e i y)) 2
          (withDensityReal ρ) ≤ ENNReal.ofReal (η * Real.sqrt (∑ i ∈ Finset.range L, x i ^ 2)) := by
  set μ := withDensityReal ρ with hμ
  have hΛ : 0 ≤ Λ := le_trans (H.prob.nonneg 0) (H.bd 0)
  -- the clamp level
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal Λ * ∫⁻ z, ‖g z - e3Clamp (n : ℝ) g z‖ₑ) atTop
      (𝓝 (ENNReal.ofReal Λ * 0)) :=
    ENNReal.Tendsto.const_mul (e3Clamp_tendsto H.int) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hlim
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (η / 2) := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).2 _ hpos).exists
  set M : ℝ := (n : ℝ) with hMdef
  have hM : 0 ≤ M := Nat.cast_nonneg n
  set gM : Torus d → ℝ := e3Clamp M g with hgM
  have HgM : PDE.MFLinear.KS gM ρ Λ :=
    ⟨(integrable_const M).mono' (e3Clamp_aesm H.int.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => by
          simpa [Real.norm_eq_abs] using e3Clamp_abs_le hM g z),
      fun z => e3Clamp_even H.even z, H.prob, H.bd⟩
  have Hk : PDE.MFLinear.KS (fun z => g z - gM z) ρ Λ :=
    ⟨H.int.sub HgM.int, fun z => by simp only [hgM, e3Clamp_even H.even, H.even], H.prob, H.bd⟩
  obtain ⟨N, hN⟩ := e3_bounded_tail he HgM hM (fun z => e3Clamp_abs_le hM g z)
    (δ := (η / 2) ^ 2) (by positivity)
  refine ⟨N, fun L x hx => ?_⟩
  set X2 := ∑ i ∈ Finset.range L, x i ^ 2 with hX2
  have hX2nn : 0 ≤ X2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  set w : Torus d → ℝ := fun y => ∑ i ∈ Finset.range L, x i * e i y with hw_def
  have hw : MemLp w 2 μ := by
    have := memLp_finsetSum' (Finset.range L) (fun i _ => (he.memLp i).const_mul (x i))
    refine this.ae_eq (Filter.Eventually.of_forall fun y => ?_)
    simp [hw_def]
  have hwi : Integrable w μ := hw.integrable one_le_two
  -- splitting
  have hsplit : PDE.MFLinear.Phi g ρ w =ᵐ[μ] fun a => PDE.MFLinear.Phi gM ρ w a +
      PDE.MFLinear.Phi (fun z => g z - gM z) ρ w a := by
    filter_upwards [PDE.MFLinear.ae_integrable_slice HgM hwi,
      PDE.MFLinear.ae_integrable_slice Hk hwi] with a h1 h2
    unfold PDE.MFLinear.Phi
    rw [← integral_add h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  obtain ⟨hF1m, -⟩ := PDE.MFLinear.memLp_Phi HgM hw
  obtain ⟨hF2m, hF2⟩ := PDE.MFLinear.memLp_Phi Hk hw
  -- the norm of `w`
  have hwsq : (eLpNorm w 2 μ).toReal ^ 2 = X2 := by
    rw [E0b.e0b_sq_eq hw]; exact e3_wnorm_sq he L x
  have hwn : eLpNorm w 2 μ = ENNReal.ofReal (Real.sqrt X2) := by
    rw [← ENNReal.ofReal_toReal hw.eLpNorm_ne_top]
    congr 1
    rw [← Real.sqrt_sq ENNReal.toReal_nonneg, hwsq]
  -- bounded part
  have hb1 : eLpNorm (PDE.MFLinear.Phi gM ρ w) 2 μ ≤ ENNReal.ofReal (η / 2 * Real.sqrt X2) := by
    have h1 := hN L x hx
    have h2 : (eLpNorm (PDE.MFLinear.Phi gM ρ w) 2 μ).toReal ^ 2 ≤ (η / 2) ^ 2 * X2 := by
      rw [E0b.e0b_sq_eq hF1m]; exact h1
    rw [← ENNReal.ofReal_toReal hF1m.eLpNorm_ne_top]
    refine ENNReal.ofReal_le_ofReal ?_
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [mul_pow, Real.sq_sqrt hX2nn]
    exact h2
  -- remainder
  have hb2 : eLpNorm (PDE.MFLinear.Phi (fun z => g z - gM z) ρ w) 2 μ ≤
      ENNReal.ofReal (η / 2 * Real.sqrt X2) := by
    refine hF2.trans ?_
    rw [hwn, ENNReal.ofReal_mul (by linarith)]
    refine mul_le_mul_left ?_ _
    exact hn.le
  calc eLpNorm (PDE.MFLinear.Phi g ρ w) 2 μ
      = eLpNorm (fun a => PDE.MFLinear.Phi gM ρ w a +
          PDE.MFLinear.Phi (fun z => g z - gM z) ρ w a) 2 μ := eLpNorm_congr_ae hsplit
    _ ≤ eLpNorm (PDE.MFLinear.Phi gM ρ w) 2 μ +
          eLpNorm (PDE.MFLinear.Phi (fun z => g z - gM z) ρ w) 2 μ :=
        eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (η / 2 * Real.sqrt X2) + ENNReal.ofReal (η / 2 * Real.sqrt X2) :=
        add_le_add hb1 hb2
    _ = ENNReal.ofReal (η * Real.sqrt X2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end HRS.MC.Sec7.E3Aux2

end
