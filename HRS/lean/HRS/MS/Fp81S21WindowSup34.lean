import HRS.MS.Fp81S21WindowSup33

/-! Joint measurability of a frozen-source raw commutator orbit. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.S53 HRS.MS.R2Interp

/-- A clamped `S53Cont` test family and a measurable particle configuration
produce a jointly measurable raw scaled commutator. -/
theorem fp81s21_frozen_raw_s53_joint_meas
    {d N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {σ T : ℝ} {ρ : Euc d → ℝ} (hT : 0 ≤ T)
    (hρ : HRS.Whole.IsProbDensity ρ)
    (G : ℝ → Euc d → ℝ)
    (hG : ∀ τ ∈ Icc (0 : ℝ) T, MemCb 2 (G τ)) (hc : S53Cont T G)
    (X : Ω → EucConfig d N) (hX : Measurable X) :
    Measurable (fun z : ℝ × Ω => (N : ℝ) / 2 *
      s53_Dk σ ρ (G (s53_clamp T z.1)) (X z.2)) := by
  let V : ℝ → Euc d → Euc d := fun t x => gradient (G (s53_clamp T t)) x
  have hV : Measurable (Function.uncurry V) := s53_grad_measurable hT hG hc
  let k : ℝ → Euc d → Euc d → ℝ := fun t => commutatorKernel d σ (V t)
  have hk : Measurable (fun q : ℝ × Euc d × Euc d => k q.1 q.2.1 q.2.2) := by
    have hVx : Measurable (fun q : ℝ × Euc d × Euc d => V q.1 q.2.1) :=
      hV.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have hVy : Measurable (fun q : ℝ × Euc d × Euc d => V q.1 q.2.2) :=
      hV.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    have hgrad : Measurable (fun q : ℝ × Euc d × Euc d =>
        rieszKernelGrad d σ (q.2.1 - q.2.2)) :=
      (movtr_rieszKernelGrad_measurable (d := d) σ).comp
        ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))
    change Measurable (fun q : ℝ × Euc d × Euc d =>
      inner ℝ (V q.1 q.2.1 - V q.1 q.2.2) (rieszKernelGrad d σ (q.2.1 - q.2.2)))
    exact (hVx.sub hVy).inner hgrad
  let ρ' : ℝ → Euc d → ℝ := fun _ => ρ
  have hρ' : Measurable (fun q : ℝ × Euc d => ρ' q.1 q.2) := hρ.measurable.comp measurable_snd
  let F : ℝ × EucConfig d N → ℝ := fun z =>
    pairEnergy (k z.1) z.2 (HRS.Whole.withDensityReal (ρ' z.1))
  have hF : Measurable F := fp81s21_param_pairEnergy_joint_meas hρ' (fun _ => hρ.nonneg) hk
  let Y : ℝ × Ω → EucConfig d N := fun z => X z.2
  have hY : Measurable Y := hX.comp measurable_snd
  have hraw : Measurable (fun z : ℝ × Ω => (N : ℝ) * F (z.1, Y z)) :=
    measurable_const.mul (fp81s21_param_comp_meas F Y hF hY)
  convert hraw using 1
  funext z
  dsimp [F, Y, k, V, ρ']
  rw [fp81s21_pairEnergy_eq_half_s53_Dk]
  ring

#print axioms fp81s21_frozen_raw_s53_joint_meas
end HRS.Fp81.S21
end
