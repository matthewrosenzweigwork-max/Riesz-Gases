import HRS.Equilibrium.Parametrix.PX1AuxDeriv
import HRS.Equilibrium.Parametrix.PX1AuxTop

/-!
# Prop 4.13 parametrix, packet PX1: the chart and the linear operations on conormal classes

The chart map `chartT (X, z) = (X + z/2, X - z/2)`, `toChart F = lift2 F ∘ chartT`, the chart
domain `Uc` (an open set on which `toChart F` is as smooth as `lift2 F` is off the diagonal), and
sums and real multiples of conormal kernels.
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx

variable {d : ℕ}

/-- The chart map `(X, z) ↦ (X + z/2, X - z/2)`. -/
def chartT (d : ℕ) : Euc d × Euc d →L[ℝ] Euc d × Euc d :=
  (ContinuousLinearMap.fst ℝ (Euc d) (Euc d) + (1 / 2 : ℝ) • ContinuousLinearMap.snd ℝ (Euc d) (Euc d)).prod
    (ContinuousLinearMap.fst ℝ (Euc d) (Euc d) - (1 / 2 : ℝ) • ContinuousLinearMap.snd ℝ (Euc d) (Euc d))

theorem chartT_apply (p : Euc d × Euc d) :
    chartT d p = (p.1 + (1 / 2 : ℝ) • p.2, p.1 - (1 / 2 : ℝ) • p.2) := by
  simp [chartT]

theorem toChart_eq (F : Torus d → Torus d → ℝ) : toChart F = lift2 F ∘ chartT d := by
  funext p
  simp [toChart, lift2, chartT_apply]

/-- The chart domain: the points whose image under the chart is off the diagonal. -/
def Uc (d : ℕ) : Set (Euc d × Euc d) := chartT d ⁻¹' offDiag d

theorem isOpen_Uc : IsOpen (Uc d) := isOpen_offDiag.preimage (chartT d).continuous

theorem toChart_contDiffOn {F : Torus d → Torus d → ℝ} {m : WithTop ℕ∞}
    (hs : ContDiffOn ℝ m (lift2 F) (offDiag d)) : ContDiffOn ℝ m (toChart F) (Uc d) := by
  rw [toChart_eq]
  exact hs.comp (chartT d).contDiff.contDiffOn (fun p hp => hp)

theorem mk_eq_zero_imp {z : Euc d} (h : Torus.mk z = 0) : ∀ i, ∃ n : ℤ, z i = n := by
  intro i
  have := congrFun h i
  simp only [Torus.mk, Pi.zero_apply] at this
  rw [AddCircle.coe_eq_zero_iff] at this
  obtain ⟨n, hn⟩ := this
  exact ⟨n, by simpa using hn.symm⟩

theorem mk_sub_eq_zero {a b : Euc d} (h : Torus.mk a = Torus.mk b) : Torus.mk (a - b) = 0 := by
  funext i
  have := congrFun h i
  simp only [Torus.mk, Pi.zero_apply] at this ⊢
  rw [PiLp.sub_apply, AddCircle.coe_sub]
  exact sub_eq_zero.mpr this

theorem mem_Uc {X z : Euc d} (hz : z ≠ 0) (hzr : ‖z‖ < r0) : (X, z) ∈ Uc d := by
  show Torus.mk (X + (1 / 2 : ℝ) • z) ≠ Torus.mk (X - (1 / 2 : ℝ) • z)
  intro h
  apply hz
  have h1 : Torus.mk z = 0 := by
    have e : z = (X + (1 / 2 : ℝ) • z) - (X - (1 / 2 : ℝ) • z) := by module
    rw [e]
    exact mk_sub_eq_zero h
  have h2 := mk_eq_zero_imp h1
  ext i
  obtain ⟨n, hn⟩ := h2 i
  have hi : |z i| ≤ ‖z‖ := by
    have := PiLp.norm_apply_le z i
    simpa using this
  have hr : ‖z‖ < 1 := by unfold r0 at hzr; linarith
  have : n = 0 := by
    have h3 : |(n : ℝ)| < 1 := by rw [← hn]; exact lt_of_le_of_lt hi hr
    have : |n| < 1 := by exact_mod_cast h3
    exact abs_lt.mp this |> fun h => by omega
  simp [hn, this]

theorem mixedDeriv_add {U : Set (Euc d × Euc d)} (hU : IsOpen U) {a c : ℕ}
    {G₁ G₂ : Euc d × Euc d → ℝ} (h₁ : ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞) G₁ U)
    (h₂ : ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞) G₂ U) {X z : Euc d} (hz : (X, z) ∈ U) :
    mixedDeriv a c (fun p => G₁ p + G₂ p) X z = mixedDeriv a c G₁ X z + mixedDeriv a c G₂ X z := by
  ext u v
  simp only [add_apply]
  rw [mixedDeriv_apply hU (h₁.add h₂) hz, mixedDeriv_apply hU h₁ hz, mixedDeriv_apply hU h₂ hz]
  have := iteratedFDeriv_add_apply (i := a + c) (h₁.contDiffAt (hU.mem_nhds hz))
    (h₂.contDiffAt (hU.mem_nhds hz))
  have e : (fun p => G₁ p + G₂ p) = G₁ + G₂ := rfl
  rw [e, this]
  simp

theorem mixedDeriv_smul {U : Set (Euc d × Euc d)} (hU : IsOpen U) {a c : ℕ}
    {G : Euc d × Euc d → ℝ} (r : ℝ) (h : ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞) G U)
    {X z : Euc d} (hz : (X, z) ∈ U) :
    mixedDeriv a c (fun p => r * G p) X z = r • mixedDeriv a c G X z := by
  ext u v
  simp only [smul_apply]
  have hh : ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞) (fun p => r * G p) U := h.const_smul r
  rw [mixedDeriv_apply hU hh hz, mixedDeriv_apply hU h hz]
  have := iteratedFDeriv_const_smul_apply (a := r) (i := a + c) (h.contDiffAt (hU.mem_nhds hz))
  have e : (fun p => r * G p) = r • G := rfl
  rw [e, this]
  simp

theorem norm_nested_le_of {a c : ℕ} {M : ContinuousMultilinearMap ℝ (fun _ : Fin a => Euc d)
    (ContinuousMultilinearMap ℝ (fun _ : Fin c => Euc d) ℝ)} {W : ℝ} (hW : 0 ≤ W)
    (h : ∀ (u : Fin a → Euc d) (v : Fin c → Euc d),
      |M u v| ≤ W * (∏ i, ‖u i‖) * ∏ j, ‖v j‖) : ‖M‖ ≤ W := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by simpa using hW) fun u => ?_
  have hp : 0 ≤ ∏ i, ‖u i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [Real.norm_eq_abs]
  simpa [mul_assoc] using h u v

theorem le_norm_nested {a c : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin a => Euc d)
    (ContinuousMultilinearMap ℝ (fun _ : Fin c => Euc d) ℝ)) (u : Fin a → Euc d)
    (v : Fin c → Euc d) : |M u v| ≤ ‖M‖ * (∏ i, ‖u i‖) * ∏ j, ‖v j‖ := by
  rw [← Real.norm_eq_abs]
  calc ‖M u v‖ ≤ ‖M u‖ * ∏ j, ‖v j‖ := (M u).le_opNorm v
    _ ≤ (‖M‖ * ∏ i, ‖u i‖) * ∏ j, ‖v j‖ :=
        mul_le_mul_of_nonneg_right (M.le_opNorm u) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ = _ := by ring

theorem conormalL_add {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B B' : ℝ} {F G : Torus d → Torus d → ℝ}
    (hF : ConormalL σ b m B F) (hG : ConormalL σ b m B' G) :
    ConormalL σ b m (B + B') (fun x y => F x y + G x y) where
  smooth := hF.smooth.add hG.smooth
  near := by
    intro a c hac X z hz hzr
    have hq : (X, z) ∈ Uc d := mem_Uc hz hzr
    have h1 : ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞) (toChart F) (Uc d) :=
      (toChart_contDiffOn hF.smooth).of_le (by exact_mod_cast hac)
    have h2 : ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞) (toChart G) (Uc d) :=
      (toChart_contDiffOn hG.smooth).of_le (by exact_mod_cast hac)
    have e : toChart (fun x y => F x y + G x y) = fun p => toChart F p + toChart G p := rfl
    rw [e, mixedDeriv_add isOpen_Uc h1 h2 hq]
    refine (norm_add_le (mixedDeriv a c (toChart F) X z) (mixedDeriv a c (toChart G) X z)).trans ?_
    have := hF.near a c hac X z hz hzr
    have := hG.near a c hac X z hz hzr
    linarith
  far := by
    intro k hk p hp hr
    have hF' := hF.far k hk p hp hr
    have hG' := hG.far k hk p hp hr
    have e : lift2 (fun x y => F x y + G x y) = lift2 F + lift2 G := rfl
    rw [e, iteratedFDeriv_add_apply ((hF.smooth.contDiffAt (isOpen_offDiag.mem_nhds hp)).of_le
      (by exact_mod_cast hk)) ((hG.smooth.contDiffAt (isOpen_offDiag.mem_nhds hp)).of_le
      (by exact_mod_cast hk))]
    exact (norm_add_le _ _).trans (by linarith)

theorem conormalL_smul {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : ConormalL σ b m B F) (a : ℝ) : ConormalL σ b m (|a| * B) (fun x y => a * F x y) where
  smooth := hF.smooth.const_smul a
  near := by
    intro i c hac X z hz hzr
    have hq : (X, z) ∈ Uc d := mem_Uc hz hzr
    have h1 : ContDiffOn ℝ ((i + c : ℕ) : WithTop ℕ∞) (toChart F) (Uc d) :=
      (toChart_contDiffOn hF.smooth).of_le (by exact_mod_cast hac)
    have e : toChart (fun x y => a * F x y) = fun p => a * toChart F p := rfl
    rw [e]
    have hnear := hF.near i c hac X z hz hzr
    set w := B * (1 + ‖z‖ ^ (-(σ + c)) * (1 + |Real.log ‖z‖|) ^ b c) with hw
    have hw0 : 0 ≤ w := (ContinuousMultilinearMap.opNorm_nonneg _).trans hnear
    have : |a| * w = |a| * B * (1 + ‖z‖ ^ (-(σ + c)) * (1 + |Real.log ‖z‖|) ^ b c) := by
      rw [hw]; ring
    rw [← this]
    refine norm_nested_le_of (mul_nonneg (abs_nonneg a) hw0) ?_
    intro u v
    rw [mixedDeriv_smul isOpen_Uc a h1 hq]
    simp only [smul_apply, smul_eq_mul, abs_mul]
    have h2 := le_norm_nested (mixedDeriv i c (toChart F) X z) u v
    have h3 : ‖mixedDeriv i c (toChart F) X z‖ * (∏ i, ‖u i‖) * ∏ j, ‖v j‖ ≤
        w * (∏ i, ‖u i‖) * ∏ j, ‖v j‖ := by
      have hp1 : 0 ≤ ∏ i, ‖u i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
      have hp2 : 0 ≤ ∏ j, ‖v j‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnear hp1) hp2
    calc |a| * |mixedDeriv i c (toChart F) X z u v| ≤ |a| * (w * (∏ i, ‖u i‖) * ∏ j, ‖v j‖) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) (abs_nonneg a)
      _ = _ := by ring
  far := by
    intro k hk p hp hr
    have hF' := hF.far k hk p hp hr
    have e : lift2 (fun x y => a * F x y) = a • lift2 F := rfl
    rw [e, iteratedFDeriv_const_smul_apply ((hF.smooth.contDiffAt (isOpen_offDiag.mem_nhds hp)).of_le
      (by exact_mod_cast hk)), norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hF' (abs_nonneg a)

end HRS.Parx

end
