import HRS.MS.ProClosureS111OscillatorCb
import HRS.MS.S104eC5C
import HRS.MS.S104eC5F
import HRS.MS.S104eFinal
import HRS.MS.S21F_D00
import HRS.MS.R2WinOrbTRD11

/-!
# S2.1(iii): oscillator data for the S104e Volterra construction

The weighted estimates below extend the Schwartz estimate `s103_weighted` by
Hermite truncation.  The arbitrary-test Sobolev estimate controls convergence
of the derivatives of those truncations.  The generalized Volterra entry point
records the datum actually consumed by the Picard and classical-regularity
steps, rather than specializing that datum to a Hermite function.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovLin HRS.MS.R2WinOrbNL HRS.MS.Ul
open HRS.MS.S104e.C HRS.MS.R26T3

variable {d : ℕ}

private theorem fp81s21_weighted_osc_derivatives :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (φ : Euc d → ℝ),
      IsOscTest ((wholeSpaceIndex d : ℕ) : ℝ) φ →
      ∀ i ≤ 4, ∀ x : Euc d,
        (1 + ‖x‖) ^ 3 * ‖iteratedFDeriv ℝ i φ x‖ ≤
          K * oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) φ := by
  have hCwAll : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : SchwartzMap (Euc d) ℝ) (x : Euc d),
        (1 + ‖x‖) ^ 3 * ‖iteratedFDeriv ℝ j f x‖ ≤
          C * oscNorm ((3 + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f :=
    HRS.MS.R2WinOrb.s103_weighted (d := d) 3
  choose Cw hCw0 hCw using hCwAll
  have hindex_floor :
      ((⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤ 4 + (d : ℝ) / 2 :=
    Nat.floor_le (by positivity)
  let q : ℕ := 3 + ⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1
  have hqle : q ≤ wholeSpaceIndex d := by
    have hqR : (q : ℝ) ≤ (wholeSpaceIndex d : ℝ) := by
      dsimp [q, wholeSpaceIndex]
      push_cast
      linarith [hindex_floor]
    exact_mod_cast hqR
  have hn : (4 : ℝ) + (d : ℝ) / 2 < ((d + 10 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hm' : (d : ℝ) <
      (((wholeSpaceIndex d : ℕ) : ℝ) - ((d + 10 : ℕ) : ℝ)) / 2 := by
    rw [wholeSpaceIndex]
    push_cast
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith [hd0]
  obtain ⟨Ce, hCe0, hCe⟩ :=
    HRS.MS.ProClosureS111.oscillator_derivative_norm_bound
      (d := d) (m := ((wholeSpaceIndex d : ℕ) : ℝ)) 4 (d + 10) hn hm'
  let K : ℝ := ∑ i ∈ Finset.range 5, Cw i
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Finset.sum_nonneg fun i hi => hCw0 i
  have hqosc : ∀ (φ : Euc d → ℝ),
      IsOscTest ((wholeSpaceIndex d : ℕ) : ℝ) φ → MemOsc (q : ℝ) φ := by
    intro φ hφ
    exact (HRS.MS.MovOsc.mo_mono (r := (q : ℝ))
      (r' := ((wholeSpaceIndex d : ℕ) : ℝ)) (by exact_mod_cast hqle) hφ.2).1
  have hqnorm : ∀ (φ : Euc d → ℝ),
      IsOscTest ((wholeSpaceIndex d : ℕ) : ℝ) φ →
      oscNorm (q : ℝ) φ ≤ oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) φ := by
    intro φ hφ
    exact (HRS.MS.MovOsc.mo_mono (r := (q : ℝ))
      (r' := ((wholeSpaceIndex d : ℕ) : ℝ)) (by exact_mod_cast hqle) hφ.2).2
  refine ⟨K, hK0, ?_⟩
  intro φ hφ i hi x
  let g : ℕ → Euc d → ℝ := fun n => HRS.MS.MovOsc.mo_pSum φ n
  have hpartial : ∀ n, (1 + ‖x‖) ^ 3 *
      ‖iteratedFDeriv ℝ i (g n) x‖ ≤
      K * oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) φ := by
    intro n
    obtain ⟨f, hf⟩ := HRS.MS.Mov63.mn_pSum_schwartz φ n
    have hbase := hCw i f x
    let qi : ℕ := 3 + ⌊(i : ℝ) + (d : ℝ) / 2⌋₊ + 1
    have hfloor : ⌊(i : ℝ) + (d : ℝ) / 2⌋₊ ≤
        ⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ :=
      Nat.floor_le_floor (by gcongr; exact_mod_cast hi)
    have hqile : qi ≤ q := by dsimp [qi, q]; omega
    have hqiOsc : MemOsc (qi : ℝ) φ :=
      (HRS.MS.MovOsc.mo_mono (r := (qi : ℝ)) (r' := (q : ℝ))
        (by exact_mod_cast hqile) (hqosc φ hφ)).1
    have hqSum : MemOsc (q : ℝ) (g n) := by
      dsimp [g]
      exact (HRS.MS.MovOsc.mo_pSum_oscNorm_le (r := (q : ℝ))
        (hqosc φ hφ) n).1
    have hqitoq := HRS.MS.MovOsc.mo_mono (r := (qi : ℝ)) (r' := (q : ℝ))
      (by exact_mod_cast hqile) hqSum
    have hqip : MemOsc (qi : ℝ) (g n) := hqitoq.1
    have hqimon : oscNorm (qi : ℝ) (g n) ≤ oscNorm (q : ℝ) (g n) := hqitoq.2
    have hbase' : (1 + ‖x‖) ^ 3 *
        ‖iteratedFDeriv ℝ i (g n) x‖ ≤ Cw i * oscNorm (q : ℝ) (g n) := by
      calc
        _ ≤ Cw i * oscNorm (qi : ℝ) (g n) := by simpa [g, hf, qi] using hbase
        _ ≤ _ := mul_le_mul_of_nonneg_left hqimon (hCw0 i)
    have hsumNorm : oscNorm (q : ℝ) (g n) ≤ oscNorm (q : ℝ) φ := by
      dsimp [g]
      exact (HRS.MS.MovOsc.mo_pSum_oscNorm_le (r := (q : ℝ))
        (hqosc φ hφ) n).2
    have hconst : Cw i ≤ K := by
      dsimp [K]
      exact Finset.single_le_sum (f := Cw)
        (fun j hj => hCw0 j) (Finset.mem_range.2 (by omega : i < 5))
    calc
      (1 + ‖x‖) ^ 3 * ‖iteratedFDeriv ℝ i (g n) x‖ ≤
          Cw i * oscNorm (q : ℝ) (g n) := by
            exact hbase'
      _ ≤ K * oscNorm (q : ℝ) (g n) :=
        mul_le_mul_of_nonneg_right hconst (Real.sqrt_nonneg _)
      _ ≤ K * oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) φ :=
        mul_le_mul_of_nonneg_left (hsumNorm.trans (hqnorm φ hφ)) hK0
  have htail : Tendsto (fun n : ℕ => oscNorm ((wholeSpaceIndex d : ℕ) : ℝ)
      (fun y => φ y - g n y)) atTop (𝓝 0) :=
    HRS.MS.MovOsc.mo_hsum_tail _ hφ.2
  have hSmoothg : ∀ n, ContDiff ℝ ∞ (g n) := by
    intro n
    obtain ⟨f, hf⟩ := HRS.MS.Mov63.mn_pSum_schwartz φ n
    change ContDiff ℝ ∞ (HRS.MS.MovOsc.mo_pSum φ n)
    rw [← hf]
    exact f.smooth (⊤ : ℕ∞)
  have htestDiff : ∀ n, IsOscTest ((wholeSpaceIndex d : ℕ) : ℝ)
      (fun y => φ y - g n y) := by
    intro n
    constructor
    · exact hφ.1.sub (hSmoothg n)
    · exact HRS.MS.MovLin.mov2d_memOsc_sub hφ.2
        (HRS.MS.MovOsc.mo_pSum_oscNorm_le
          (r := ((wholeSpaceIndex d : ℕ) : ℝ)) hφ.2 n).1
  have hderivConv : Tendsto (fun n : ℕ => iteratedFDeriv ℝ i (g n) x)
      atTop (𝓝 (iteratedFDeriv ℝ i φ x)) := by
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    have herr : ∀ n, ‖iteratedFDeriv ℝ i (g n) x -
        iteratedFDeriv ℝ i φ x‖ ≤ Ce *
          oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) (fun y => φ y - g n y) := by
      intro n
      have hb := hCe φ hφ i hi x
      have hd := hCe (fun y => φ y - g n y) (htestDiff n) i hi x
      have hsub : iteratedFDeriv ℝ i (fun y => φ y - g n y) x =
          iteratedFDeriv ℝ i φ x - iteratedFDeriv ℝ i (g n) x := by
        have heq : (fun y => φ y - g n y) = φ - g n := rfl
        have hitop : ((i : ℕ∞) : WithTop ℕ∞) ≤
            ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
        rw [heq]
        rw [iteratedFDeriv_sub_apply
          (hφ.1.of_le hitop).contDiffAt
          ((hSmoothg n).of_le hitop).contDiffAt]
      rw [hsub] at hd
      simpa [norm_sub_rev] using hd
    have hupper : Tendsto (fun n : ℕ => Ce *
        oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) (fun y => φ y - g n y)) atTop (𝓝 0) := by
      simpa using htail.const_mul Ce
    have hnorm : Tendsto (fun n : ℕ =>
        ‖iteratedFDeriv ℝ i (g n) x - iteratedFDeriv ℝ i φ x‖) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => herr n) hupper
    simpa using hnorm
  have hnormConv : Tendsto (fun n : ℕ => ‖iteratedFDeriv ℝ i (g n) x‖)
      atTop (𝓝 ‖iteratedFDeriv ℝ i φ x‖) :=
    continuous_norm.continuousAt.tendsto.comp hderivConv
  have hweightedConv : Tendsto (fun n : ℕ =>
      (1 + ‖x‖) ^ 3 * ‖iteratedFDeriv ℝ i (g n) x‖) atTop
      (𝓝 ((1 + ‖x‖) ^ 3 * ‖iteratedFDeriv ℝ i φ x‖)) :=
    (tendsto_const_nhds.mul hnormConv)
  have hclosed : IsClosed {z : ℝ | z ≤
      K * oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) φ} := isClosed_Iic
  exact hclosed.mem_of_tendsto hweightedConv (Filter.Eventually.of_forall hpartial)

/-- Every oscillator test at the fixed whole-space index supplies the S104e
Picard datum. The constant `B` is chosen before the test and may depend on its
oscillator norm. -/
theorem fp81s21_datum_of_osc
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    {φ : Euc d → ℝ}
    (hφ : IsOscTest ((wholeSpaceIndex d : ℕ) : ℝ) φ) :
    ∃ B : ℝ, HolB 2 η B φ ∧ VanB 3 φ ∧ Bd 2 B φ := by
  obtain ⟨K, hK0, hK⟩ := fp81s21_weighted_osc_derivatives (d := d)
  let M : ℝ := K * oscNorm ((wholeSpaceIndex d : ℕ) : ℝ) φ
  have hM0 : 0 ≤ M := mul_nonneg hK0 (Real.sqrt_nonneg _)
  have hsy : SyN 3 4 M φ := by
    have h4top : ((4 : ℕ∞) : WithTop ℕ∞) ≤
        ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
    refine ⟨hφ.1.of_le h4top, ?_⟩
    intro i hi x
    rw [mul_comm]
    exact hK φ hφ i hi x
  have hbd4 : Bd 4 M φ := hsy.bd
  have hvan : VanB 3 φ :=
    HRS.MS.S104e.C.c5_vanB_of_decay
      (fun i hi x => hsy.2 i (by omega) x) (by norm_num)
  have hhol : HolB 2 η (2 * M) φ :=
    HRS.MS.S104e.C.holB_of_bd hη0 hη1 hbd4
  refine ⟨2 * M, hhol, hvan, ?_⟩
  exact hbd4.mono_N (by omega) |>.mono_A (by linarith)

/-- The Volterra construction only needs its Picard datum. This is `c5_exists`
with its Hermite-specific `c5_datum` call replaced by the supplied datum; the
remaining Picard and classical-regularity steps are unchanged. -/
theorem fp81s21_exists_of_picard_datum
    (s a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (ρ : ℝ → Euc d → ℝ) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    {φ : Euc d → ℝ}
    (hdatum : ∃ B : ℝ, HolB 2 η B φ ∧ VanB 3 φ ∧ Bd 2 B φ)
    {t : ℝ} (ht : 0 ≤ t)
    (hyp : VolHyp d 2 η (t + 1) (ouSg (ouQ d a) β⁻¹)
      (fun v f => s103bQ d s (ρ v) f)) :
    ∃ f : ℝ → Euc d → ℝ,
      IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t φ f := by
  obtain ⟨B, hψH, hψV, hψB⟩ := hdatum
  obtain ⟨C3, hC30, hex⟩ := c3_volterra_exists 2 η (t + 1) hη0 hη1
    (by linarith) _ _ hyp
  obtain ⟨w, hwH, hwt, hwc, hwm, hwV, hwTC⟩ :=
    hex t ⟨ht, by linarith⟩ B _ hψH hψV
  set Bw := C3 * B
  have hw2 : ∀ r ∈ Icc (0 : ℝ) t, Bd 2 Bw (w r) := fun r hr =>
    ⟨(hwH r hr).1.1.of_le (by exact_mod_cast (by omega : 2 ≤ 2 + 1)),
      fun i hi x => (hwH r hr).1.2 i (by omega) x⟩
  have hmem : ∀ v ∈ Icc (0 : ℝ) t, v ∈ Icc (0 : ℝ) (t + 1) := fun v hv =>
    ⟨hv.1, by linarith [hv.2]⟩
  have hg2 : ∀ r ∈ Icc (0 : ℝ) t,
      Bd 2 (hyp.CA * Bw) (s103bQ d s (ρ r) (w r)) := fun r hr =>
    hyp.A_bd r (hmem r hr) Bw (w r) (hwH r hr)
  have hTCg := hyp.A_tc t ⟨ht, by linarith⟩ Bw w hwH hwTC
  refine ⟨w, c4_classical s a β ha hβ ρ ht hψB hw2
    (fun i hi => hwc i (by omega)) hwt (fun r hr => rfl) hg2
    (fun r₀ hr₀ ε hε => ?_) (fun r hr x => ?_)⟩
  · obtain ⟨δ, hδ, h⟩ := hTCg 0 (Nat.zero_le _) ε hε
    exact ⟨δ, hδ, fun r hr hd y => c5_norm0_le (h r hr r₀ hr₀ hd y)⟩
  · exact hwm r hr x

/-- Classical adjoints exist for every oscillator test along every resulting
common-radius trajectory, for every nonnegative terminal time. -/
theorem fp81s21_adjoint_of_osc_test
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {φ : Euc p.d → ℝ}
    (hφ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) φ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ f : ℝ → Euc p.d → ℝ,
      IsClassicalAdjointW (r26t3_coeff R) t φ f := by
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith [p.hs]
  let η : ℝ := (max 0 (p.s - p.d + 1) + 1) / 2
  have hmax : max 0 (p.s - p.d + 1) < 1 :=
    max_lt (by norm_num) (by linarith)
  have hη0 : max 0 (p.s - p.d + 1) < η := by
    dsimp [η]
    linarith
  have hη1 : η < 1 := by
    dsimp [η]
    linarith
  have hηp : 0 < η := lt_of_le_of_lt (le_max_left _ _) hη0
  have hPfields := HRS.MS.S104e.C.c1_P_fields
    (d := p.d) p.a p.β⁻¹ p.ha (inv_pos.2 p.hβ) hηp hη1 2 (t + 1)
  obtain ⟨CP, hCP1, hP1, hP2, hP3, hP4, hP5, hP6, hP7⟩ := hPfields
  have hP : Nonempty (C5PHyp p.d p.a p.β⁻¹ 2 η (t + 1)) := by
    exact ⟨⟨CP, hCP1, hP1, hP2, hP3, hP4, hP5, hP6, hP7⟩⟩
  have hAjc := HRS.MS.S104e.C.c5_Ajc p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.resulting hη0 hη1 (t + 1)
  obtain ⟨hyp⟩ := HRS.MS.S104e.C.c5_volHyp p.hd p.hs0 hsd p.hβ
    δ p.c₁ p.C₁ R.thermal R.resulting p.ha hη0 hη1 (by linarith) hP hAjc
  have hdatum := fp81s21_datum_of_osc (d := p.d) hηp hη1.le hφ
  have hadj := fp81s21_exists_of_picard_datum
    (d := p.d) p.s p.a p.β p.ha p.hβ R.ρ hηp hη1 hdatum ht hyp
  simpa [r26t3_coeff] using hadj

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_datum_of_osc
#print axioms HRS.Fp81.S21.fp81s21_exists_of_picard_datum
#print axioms HRS.Fp81.S21.fp81s21_adjoint_of_osc_test

end
