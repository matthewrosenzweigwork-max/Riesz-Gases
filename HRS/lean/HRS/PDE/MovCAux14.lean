import HRS.PDE.MovCAux13

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movc_comm_tendsto (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) {r : ℝ}
    (hr : r ∈ Set.Icc 0 T) {X : Config d N} (hX : X ∉ collisionSet d N) :
    Tendsto (fun n => movT_commReg D N (M n) (ρ r) X) atTop
        (𝓝 (movT_commAt D N (ρ r) X)) ∧
      Tendsto (fun n => ∫ Y, movT_commReg D N (M n) (ρ r) Y
          ∂(movT_Q (b15c_gReg d D.s (M n)) D N ρ r)) atTop
        (𝓝 (∫ Y, movT_commAt D N (ρ r) Y ∂(movT_Q (periodicRiesz d D.s) D N ρ r))) := by
  have hd : 1 ≤ d := b15_one_le_d D
  have hρ : IsProbDensity (ρ r) := h.mf.density r hr
  have hcont : Continuous (ρ r) := b15_continuous_of_isCk (h.ck r hr)
  haveI hμ : IsProbabilityMeasure (withDensityReal (ρ r)) := isProb_withDensityReal hρ
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 h.pos_temp
  have hN1 : 1 ≤ N := by omega
  obtain ⟨Bg, hBg⟩ := b15_periodicRiesz_lower D
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d D.s z + (Bg + 1) := fun z _ => by
    have := hBg z; linarith
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_abs_bound hcont
  have hρΛ : ∀ x, ρ r x ≤ Mρ := fun x => (le_abs_self _).trans (hMρ x)
  obtain ⟨hgR, -⟩ := rowOK_g_h hd D.s D.hs0 D.hsd (Bg + 1) hw 0 hMρ0 hρΛ
    (h := fun _ _ => 0) measurable_const (fun x y => by simp)
  have hFm : Measurable (fun X : Config d N => modulatedEnergyKernel (periodicRiesz d D.s) X
      (withDensityReal (ρ r))) := measurable_modulatedEnergy hgR
  have hFnm : ∀ n, Measurable (fun X : Config d N => modulatedEnergyKernel (b15c_gReg d D.s (M n)) X
      (withDensityReal (ρ r))) := fun n =>
    measurable_modulatedEnergyKernel (movc_gReg_measurable hd D.hs0 D.hsd (M n)) _
  obtain ⟨c, hc⟩ := movc_energy_lower hd D.hs0 D.hsd hN1 hρ hcont (N := N)
  have hae := Repulsive.ae_notMem_collisionSet hd (rfl : withDensityReal (ρ r) = withDensityReal (ρ r)) hρ N
  have hlim : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => withDensityReal (ρ r)),
      Tendsto (fun n => modulatedEnergyKernel (b15c_gReg d D.s (M n)) X (withDensityReal (ρ r))) atTop
        (𝓝 (modulatedEnergyKernel (periodicRiesz d D.s) X (withDensityReal (ρ r)))) :=
    hae.mono fun X hX => movc_energy_tendsto hd D.hs0 D.hsd hρ hcont hM hM0 hX
  -- the kernels
  obtain ⟨W, hWi, hWm, hW0, hdomM, hdomk⟩ := movc_kernel_dom h hr
  have hdom : ∀ n x y, |commKernel (Torus.grad (b15c_gReg d D.s (M n))) (movT_uReg D (M n) (ρ r)) x y|
      ≤ W (x - y) := fun n => hdomM (M n) (hM0 n)
  have hm : ∀ n, Measurable (Function.uncurry
      (commKernel (Torus.grad (b15c_gReg d D.s (M n))) (movT_uReg D (M n) (ρ r)))) :=
    fun n => (movc_kernel_meas h hr (M n)).1
  have hmk := (movc_kernel_meas h hr 0).2
  have hconv : ∀ x y, x ≠ y → Tendsto (fun n => commKernel (Torus.grad (b15c_gReg d D.s (M n)))
      (movT_uReg D (M n) (ρ r)) x y) atTop
      (𝓝 (commKernel (periodicRieszGrad d D.s) (mfeTransport D (ρ r)) x y)) :=
    fun x y hxy => movc_kernel_conv h hr hM hM0 x y hxy
  have hEt : ∀ X : Config d N, X ∉ collisionSet d N → Tendsto (fun n =>
      modulatedEnergy (commKernel (Torus.grad (b15c_gReg d D.s (M n))) (movT_uReg D (M n) (ρ r))) X
        (withDensityReal (ρ r))) atTop
      (𝓝 (modulatedEnergy (commKernel (periodicRieszGrad d D.s) (mfeTransport D (ρ r))) X
        (withDensityReal (ρ r)))) := fun X hX =>
    movc_modEnergy_tendsto hd hMρ0 hρΛ hρ hWi hm hdom hconv hX
  refine ⟨hEt X hX, ?_⟩
  -- expectation
  have hrowM : ∀ n, RowOK (withDensityReal (ρ r))
      (commKernel (Torus.grad (b15c_gReg d D.s (M n))) (movT_uReg D (M n) (ρ r))) := fun n =>
    (rowOK_of_dom hMρ0 hρΛ hWi (hm n) (hdom n)).1
  have hrowk : RowOK (withDensityReal (ρ r))
      (commKernel (periodicRieszGrad d D.s) (mfeTransport D (ρ r))) :=
    (rowOK_of_dom hMρ0 hρΛ hWi hmk hdomk).1
  have hEm : ∀ n, Measurable (fun X : Config d N => modulatedEnergy
      (commKernel (Torus.grad (b15c_gReg d D.s (M n))) (movT_uReg D (M n) (ρ r))) X
        (withDensityReal (ρ r))) := fun n => measurable_modulatedEnergy (hrowM n)
  have hEkm : Measurable (fun X : Config d N => modulatedEnergy
      (commKernel (periodicRieszGrad d D.s) (mfeTransport D (ρ r))) X (withDensityReal (ρ r))) :=
    measurable_modulatedEnergy hrowk
  have hH := movc_Emax_integrable (N := N) hMρ0 hρΛ hρ hWi hW0 hWm
  have hbd : ∀ (n : ℕ) (X : Config d N), |modulatedEnergy
      (commKernel (Torus.grad (b15c_gReg d D.s (M n))) (movT_uReg D (M n) (ρ r))) X
        (withDensityReal (ρ r))| ≤ movc_Emax W X (withDensityReal (ρ r)) := fun n X =>
    movc_modEnergy_abs_le hMρ0 hρΛ hρ hWi hW0 hWm (hm n) (hdom n) X
  have hlimφ := hae.mono fun X hX => hEt X hX
  unfold movT_Q modulatedGibbs gibbsNormalizer
  unfold movT_commReg movT_commAt
  have ha0 : -D.invβ⁻¹ * N ≤ 0 := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
  exact movc_gibbs_tendsto2 (Measure.pi fun _ : Fin N => withDensityReal (ρ r))
    (-D.invβ⁻¹ * N) ha0
    (fun n X => modulatedEnergyKernel (b15c_gReg d D.s (M n)) X (withDensityReal (ρ r)))
    (fun X => modulatedEnergyKernel (periodicRiesz d D.s) X (withDensityReal (ρ r)))
    hFnm hFm c (fun n X => hc (M n) (hM0 n) X) hlim
    (fun n X => modulatedEnergy
      (commKernel (Torus.grad (b15c_gReg d D.s (M n))) (movT_uReg D (M n) (ρ r))) X
        (withDensityReal (ρ r)))
    (fun X => modulatedEnergy (commKernel (periodicRieszGrad d D.s) (mfeTransport D (ρ r))) X
      (withDensityReal (ρ r)))
    hEm hEkm (fun X => movc_Emax W X (withDensityReal (ρ r))) hH hbd hlimφ

end HRS
