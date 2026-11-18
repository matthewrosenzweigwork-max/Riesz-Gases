import HRS.PDE.MeanFieldSchauderB
import HRS.Kernel.GradReg

/-!
# Regularity of the thermal density in the remaining range (package MF-01, packet P4b)

`thermal_memSobolev_general` is `MFInputs.thermal_memSobolev` for every `s < d`: for `s < d/2 + 1`
it is `MFThermalReg.thermal_memSobolev_of_lt`; for `s ≥ d/2 + 1` (which forces `d ≥ 3`) the
Lipschitz/Moser bootstrap does not reach `H^{> d/2}`, and we instead climb in the Hölder scale:
the Riesz kernel satisfies `|g| ≲ ‖z‖^{-p}`, `|∇g| ≲ ‖z‖^{-p-1}` for some `p < d`, so convolution
gains a fixed positive amount of Hölder regularity (`MFSchauder`), `exp` and products preserve the
Hölder classes (`MFHolder`), and `ρ = exp(-β V - β g ⋆ ρ + c)` is therefore `C^{K+1}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.PDE.MFThermalRegB

variable {d : ℕ}

open HRS.PDE.MFSchauder HRS.PDE.MFHolder

/-- Every point of the torus is `boxPt y` for a `y` in the box `(-1/2, 1/2]^d`. -/
theorem exists_box (z : Torus d) : ∃ y ∈ KernelAux.Box d, KernelAux.boxPt y = z := by
  refine ⟨fun i => ((AddCircle.equivIoc (1 : ℝ) (-1 / 2) (z i) : Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)) : ℝ),
    fun i => ?_, ?_⟩
  · exact (AddCircle.equivIoc (1 : ℝ) (-1 / 2) (z i)).2
  · funext i
    simp [KernelAux.boxPt]

/-- The kernel bundle for the Riesz kernel, with the (weaker) exponent `p = (s + d)/2`. -/
theorem kb_riesz (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (F : MFInputs.MFKernelFacts d s) :
    ∃ C : ℝ, KB d (periodicRiesz d s) (periodicRieszGrad d s) ((s + d) / 2) C := by
  obtain ⟨C1, C2, hC1, hC2, hbd⟩ := KernelAux.periodicRiesz_box_bound (d := d) (s := s) hd hs0 hsd
  obtain ⟨CG, hG⟩ := KernelGrad.goodKernel_periodicRieszGrad hd hs0 hsd
  have hd0 : 0 < d := by omega
  have hp0 : 0 ≤ (s + d) / 2 := by positivity
  refine ⟨max (C1 + C2) (2 * CG), ⟨hd0, hp0, by linarith, le_max_of_le_left (by positivity),
    F.integrable, hG.meas, fun z hz => ?_, fun z hz => ?_, fun x hx =>
      KernelGrad.periodicRieszGrad_hasGradientAt hd hs0 hsd hx x rfl⟩⟩
  · obtain ⟨y, hyB, rfl⟩ := exists_box z
    have hy0 : y ≠ 0 := fun h => hz (by rw [h]; rfl)
    have hyn : ‖KernelAux.boxPt y‖ = ‖y‖ := KernelGrad.norm_boxPt hyB
    rw [hyn]
    have hpos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hle : ‖y‖ ≤ 1 / 2 := KernelAux.Box_norm_le hyB
    have h1 := hbd y hyB hy0
    have h2 : (1 : ℝ) ≤ ‖y‖ ^ (-((s + d) / 2)) := by
      have : (1 : ℝ) ≤ ‖y‖⁻¹ := by rw [le_inv_comm₀ one_pos hpos]; linarith
      calc (1 : ℝ) ≤ ‖y‖⁻¹ ^ ((s + d) / 2) := Real.one_le_rpow this hp0
        _ = ‖y‖ ^ (-((s + d) / 2)) := by rw [Real.rpow_neg hpos.le, Real.inv_rpow hpos.le]
    have h3 : 0 ≤ ‖y‖ ^ (-((s + d) / 2)) := Real.rpow_nonneg hpos.le _
    calc |periodicRiesz d s (KernelAux.boxPt y)| ≤ C1 * ‖y‖ ^ (-((s + d) / 2)) + C2 := h1
      _ ≤ (C1 + C2) * ‖y‖ ^ (-((s + d) / 2)) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) h3
  · have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hle : ‖z‖ ≤ 1 / 2 := MFHolder.norm_torus_le_half z
    have h1 := hG.bound_norm z hz
    have h2 : (1 : ℝ) ≤ ‖z‖ ^ (-s - 1) := by
      have : (1 : ℝ) ≤ ‖z‖⁻¹ := by rw [le_inv_comm₀ one_pos hzn]; linarith
      calc (1 : ℝ) ≤ ‖z‖⁻¹ ^ (s + 1) := Real.one_le_rpow this (by linarith)
        _ = ‖z‖ ^ (-s - 1) := by
            rw [show -s - 1 = -(s + 1) by ring, Real.rpow_neg hzn.le, Real.inv_rpow hzn.le]
    have h3 : ‖z‖ ^ (-s - 1) ≤ ‖z‖ ^ (-((s + d) / 2) - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hzn (by linarith) (by linarith)
    have h4 : 0 ≤ ‖z‖ ^ (-((s + d) / 2) - 1) := Real.rpow_nonneg hzn.le _
    have hCG : 0 ≤ CG := hG.hC0
    calc ‖periodicRieszGrad d s z‖ ≤ CG * (‖z‖ ^ (-s - 1) + 1) := h1
      _ ≤ CG * (2 * ‖z‖ ^ (-((s + d) / 2) - 1)) := by
          apply mul_le_mul_of_nonneg_left _ hCG
          linarith
      _ = (2 * CG) * ‖z‖ ^ (-((s + d) / 2) - 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) h4


/-- A continuous function is `C^{0,0}`. -/
theorem hol0_zero_of_continuous {f : Torus d → ℝ} (hf : Continuous f) : Hol0 0 f := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨hf, 2 * max B 0, fun x y => ?_⟩
  have h1 := hB x (Set.mem_univ x)
  have h2 := hB y (Set.mem_univ y)
  rw [Real.norm_eq_abs] at h1 h2
  rw [Real.rpow_zero, mul_one]
  have := le_max_left B 0
  have := le_max_right B 0
  calc |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
    _ ≤ 2 * max B 0 := by linarith

section Step

variable {g : Torus d → ℝ} {G : Torus d → Euc d} {p C θ : ℝ}

/-- Regularity of `V` in the Hölder scale. -/
theorem hc_V {N : ℕ} {V : Torus d → ℝ} (hV : Torus.IsCk ((N + 1 : ℕ) : WithTop ℕ∞) V)
    {m : ℕ} (hm : m ≤ N) {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) : HC m γ V :=
  HC.le m N h0 h1 hm (HC.of_isCk N hV h0 h1)

/-- The right-hand side of the thermal equation preserves `HC`. -/
theorem hc_rhs {m : ℕ} {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) {V u : Torus d → ℝ} (hV : HC m γ V)
    (hu : HC m γ u) (β c : ℝ) :
    HC m γ (fun x => Real.exp (-β * V x + -β * u x + c)) :=
  HC.exp m h0 h1 (HC.add m h0 h1 (HC.add m h0 h1 (HC.const_mul m hV (-β))
    (HC.const_mul m hu (-β))) (HC.const m γ c))

/-- One step of the climb without crossing an integer. -/
theorem step_stay (K : KB d g G (d - θ) C) (hθ0 : 0 < θ) {N : ℕ}
    {V : Torus d → ℝ} (hV : Torus.IsCk ((N + 1 : ℕ) : WithTop ℕ∞) V) {β c : ℝ} {ρ : Torus d → ℝ}
    (hρe : ∀ x, ρ x = Real.exp (-β * V x + -β * convFun g ρ x + c)) {m : ℕ} (hm : m ≤ N)
    {a : ℝ} (ha0 : 0 ≤ a) (hae : a + θ / 2 ≤ 1) (H : HC m a ρ) : HC m (a + θ / 2) ρ := by
  have hc : HC m (a + θ / 2) (convFun g ρ) :=
    K.conv_HC m ha0 (by linarith) hae (by rw [sub_sub_cancel]; linarith) H
  have hρ : ρ = fun x => Real.exp (-β * V x + -β * convFun g ρ x + c) := funext hρe
  rw [hρ]
  exact hc_rhs (by linarith) hae (hc_V hV hm (by linarith) hae) hc β c

/-- One step of the climb crossing an integer. -/
theorem step_cross (K : KB d g G (d - θ) C) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2) {N : ℕ}
    {V : Torus d → ℝ} (hV : Torus.IsCk ((N + 1 : ℕ) : WithTop ℕ∞) V) {β c : ℝ} {ρ : Torus d → ℝ}
    (hρe : ∀ x, ρ x = Real.exp (-β * V x + -β * convFun g ρ x + c)) {m : ℕ} (hm : m + 1 ≤ N)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hae : 1 < a + θ / 2) (H : HC m a ρ) :
    HC (m + 1) (a + θ / 2 - 1) ρ := by
  have hc : HC (m + 1) (a + θ / 2 - 1) (convFun g ρ) :=
    K.cross_HC m ha0 ha1 (by rw [sub_sub_cancel]; linarith) (by linarith) (by linarith)
      (by rw [sub_sub_cancel]; linarith) H
  have hρ : ρ = fun x => Real.exp (-β * V x + -β * convFun g ρ x + c) := funext hρe
  rw [hρ]
  exact hc_rhs (by linarith) (by linarith) (hc_V hV hm (by linarith) (by linarith)) hc β c

/-- The climb: after finitely many steps `ρ ∈ C^{N,a}`. -/
theorem climb_aux (K : KB d g G (d - θ) C) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2) {N : ℕ}
    {V : Torus d → ℝ} (hV : Torus.IsCk ((N + 1 : ℕ) : WithTop ℕ∞) V) {β c : ℝ} {ρ : Torus d → ℝ}
    (hρc : Continuous ρ)
    (hρe : ∀ x, ρ x = Real.exp (-β * V x + -β * convFun g ρ x + c)) :
    ∀ n : ℕ, ∃ (m : ℕ) (a : ℝ), m ≤ N ∧ 0 ≤ a ∧ a ≤ 1 ∧ HC m a ρ ∧
      (m = N ∨ (n : ℝ) * (θ / 2) ≤ m + a)
  | 0 => ⟨0, 0, Nat.zero_le _, le_rfl, zero_le_one, hol0_zero_of_continuous hρc,
      Or.inr (by simp)⟩
  | n + 1 => by
    obtain ⟨m, a, hmN, ha0, ha1, H, hm⟩ := climb_aux K hθ0 hθ1 hV hρc hρe n
    rcases hm with rfl | hm
    · exact ⟨m, a, hmN, ha0, ha1, H, Or.inl rfl⟩
    · rcases hmN.lt_or_eq with hlt | rfl
      · by_cases hae : a + θ / 2 ≤ 1
        · refine ⟨m, a + θ / 2, hmN, by linarith, hae,
            step_stay K hθ0 hV hρe hmN ha0 hae H, Or.inr ?_⟩
          push_cast
          linarith
        · rw [not_le] at hae
          refine ⟨m + 1, a + θ / 2 - 1, hlt, by linarith, by linarith,
            step_cross K hθ0 hθ1 hV hρe hlt ha0 ha1 hae H, Or.inr ?_⟩
          push_cast
          linarith
      · exact ⟨m, a, le_rfl, ha0, ha1, H, Or.inl rfl⟩

/-- `ρ ∈ C^N`. -/
theorem climb (K : KB d g G (d - θ) C) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2) {N : ℕ}
    {V : Torus d → ℝ} (hV : Torus.IsCk ((N + 1 : ℕ) : WithTop ℕ∞) V) {β c : ℝ} {ρ : Torus d → ℝ}
    (hρc : Continuous ρ)
    (hρe : ∀ x, ρ x = Real.exp (-β * V x + -β * convFun g ρ x + c)) :
    Torus.IsCk (N : WithTop ℕ∞) ρ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (((N : ℝ) + 2) / (θ / 2))
  obtain ⟨m, a, hmN, ha0, ha1, H, hm⟩ := climb_aux K hθ0 hθ1 hV hρc hρe n
  rcases hm with rfl | hm
  · exact H.isCk
  · exfalso
    have hθ2 : 0 < θ / 2 := by positivity
    have h1 : (N : ℝ) + 2 < n * (θ / 2) := by
      rwa [div_lt_iff₀ hθ2] at hn
    have h2 : (m : ℝ) ≤ N := by exact_mod_cast hmN
    linarith

end Step

/-- The regularity theorem, for a given kernel-fact bundle. -/
theorem thermal_memSobolev_of_facts (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hc : Continuous ρ) (hp : ∀ x, 0 < ρ x)
    (F : MFInputs.MFKernelFacts d s) :
    MemSobolev K ρ := by
  by_cases hs : s < (d : ℝ) / 2 + 1
  · exact MFThermalReg.thermal_memSobolev_of_lt hd s hs0 hsd F hs K V hV β hβ ρ hρ hc hp
  · have hd2 : 2 ≤ d := by
      by_contra h
      have : d = 1 := by omega
      subst this
      push_cast at hs hsd
      linarith
    have hV' : Torus.IsCk ((K + 1 : ℕ) : WithTop ℕ∞) V := by
      refine (show Torus.IsCk ((K + 2 : ℕ) : WithTop ℕ∞) V by exact_mod_cast hV).of_le ?_
      exact_mod_cast Nat.le_succ _
    obtain ⟨c, hlog⟩ := MFThermal.log_thermal hρ hp
    have hρe : ∀ x, ρ x = Real.exp (-β * V x + -β * convFun (periodicRiesz d s) ρ x + c) := by
      intro x
      rw [← Real.exp_log (hp x), hlog x]
      congr 1; ring
    obtain ⟨C, KC⟩ := kb_riesz hd2 hs0 hsd F
    set θ : ℝ := min (((d : ℝ) - s) / 2) (1 / 2) with hθ
    have hθ0 : 0 < θ := lt_min (by linarith) (by norm_num)
    have hθ1 : θ ≤ 1 / 2 := min_le_right _ _
    have hθ2 : θ ≤ ((d : ℝ) - s) / 2 := min_le_left _ _
    have K' : KB d (periodicRiesz d s) (periodicRieszGrad d s) (d - θ) C :=
      KC.mono (by linarith) (by linarith)
    have hCk : Torus.IsCk (K : WithTop ℕ∞) ρ := climb K' hθ0 hθ1 hV' hc hρe
    exact memSobolev_of_memHs (K : ℝ) ρ (MFProduct.memLp_two_real hc)
      (MFThermalReg.memHs_of_isCk K ρ hCk)

/-- `thermal_memSobolev_general`: exactly the statement of `MFInputs.thermal_memSobolev`
(finite regularity of a continuous positive thermal density, every `s < d`). -/
theorem thermal_memSobolev_general (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hc : Continuous ρ) (hp : ∀ x, 0 < ρ x) :
    MemSobolev K ρ := by
  have F : MFInputs.MFKernelFacts d s := by
    rcases Nat.lt_or_ge d 2 with h | h
    · exact MFInputs.mfKernelFacts_one (by omega) s hs0 hsd
    · exact MFInputs.mfKernelFacts_of_two h s hs0 hsd
  exact thermal_memSobolev_of_facts hd s hs0 hsd K V hV β hβ ρ hρ hc hp F

end HRS.PDE.MFThermalRegB
