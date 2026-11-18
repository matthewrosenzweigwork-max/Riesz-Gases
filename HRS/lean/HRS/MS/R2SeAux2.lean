import HRS.MS.R2SeAux1

/-!
# S9.9 `r2_static_edgeworth`, packet 2: screened correctors of high regularity

Worker S99, namespace `S99`.  `s99_chi` is the proof of S9.8 (`HRS.MS.S98.s98_core` / `r2_screened_proof`) with the corrector `χ`
(`∇χ = γ v`) exported instead of existentially hidden: for `φ ∈ C_b^J` (`J > k + 1 + d/2`) there is `χ ∈ C^{k+1}` with
`‖D^{j+1}χ‖_∞ ≤ K ‖φ‖_{C_b^J}` for `j ≤ k`, `L_μ χ = γ a` pointwise where `a = responseRepW φ` (the continuous representative of the
response, `IsResponse`), `a ∈ C_b^k` with `‖a‖_{C_b^k} ≤ K ‖φ‖_{C_b^J}`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace S99

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

/-- **S9.8 with exported corrector** (generic assembly). -/
theorem s99_core (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ) (hk : 1 ≤ k)
    (a β γ : ℝ) (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ) (P : (Euc d → ℝ) → Prop)
    (nf : (Euc d → ℝ) → ℝ) (hnf : ∀ φ, P φ → 0 ≤ nf φ) (hPc : ∀ φ, P φ → Continuous φ)
    (hres : ∃ N0 : ℕ, ∀ M₀ c S : ℝ, 0 < c → ∃ C5 : ℝ, 0 ≤ C5 ∧
      ∀ ρ : Euc d → ℝ, HRS.MS.TcDefs.TcRef d ρ M₀ c S N0 → ∀ γ' : ℝ, 0 < γ' → γ' ≤ γ →
        ∀ φ : Euc d → ℝ, P φ →
          ∃ r₀ r : Euc d → ℝ, MemL2Zero (withDensityReal ρ) r₀ ∧
            (∀ᵐ x ∂(withDensityReal ρ),
              r₀ x + γ' * Kop (rieszKernel d s) (withDensityReal ρ) r₀ x =
                γ' * projMean (withDensityReal ρ) φ x) ∧
            MemCb (k + 1) r ∧ cbNorm (k + 1) r ≤ C5 * nf φ ∧
            r =ᵐ[withDensityReal ρ] r₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Euc d → ℝ, P φ → ∃ χ : Euc d → ℝ,
      ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) χ ∧
      (∀ x, ∀ j ≤ k, ‖iteratedFDeriv ℝ (j + 1) χ x‖ ≤ C * nf φ) ∧
      (∀ x, thermalGen d s a β χ x =
        γ * responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ φ x) ∧
      IsResponse (rieszKernel d s) (thermalMeasure d s a β) γ φ
        (responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ φ) ∧
      MemCb k (responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ φ) ∧
      cbNorm k (responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ φ) ≤ C * nf φ := by
  obtain ⟨N0, hN0⟩ := hres
  obtain ⟨c, M₀, m₂, hc, hM₀, hS, hMb⟩ := HRS.MS.Tc6.tc6_unif hd hs0 hsd (am := a) (ap := a)
    (βm := β) (βp := β) ha hβ le_rfl le_rfl
  obtain ⟨S, hS0, hSρ⟩ := hS N0
  obtain ⟨Mb, hMb0, hMbρ⟩ := hMb (k + 1)
  obtain ⟨C5, hC5, hC5ρ⟩ := hN0 M₀ c S hc
  have hqm : 0 < a * β := mul_pos ha hβ
  obtain ⟨C1, Cm, hP⟩ := HRS.MS.Tc1.tc1_poisson_thermal hd (a * β) (a * β) Mb m₂ hqm (k + 1)
    (by omega)
  refine ⟨(|Cm| + γ⁻¹) * C5, by positivity, fun φ hφ => ?_⟩
  have hTc := hSρ a β le_rfl le_rfl le_rfl le_rfl
  have hdr := hMbρ a β le_rfl le_rfl le_rfl le_rfl
  obtain ⟨r₀, r, hr₀, hae, hr, hbd, hrr⟩ := hC5ρ _ hTc γ hγ le_rfl φ hφ
  have hprob : IsProbabilityMeasure (withDensityReal (thermalDensity d s a β)) :=
    HRS.MS.TcF.tc4_isProb hTc.prob
  have hri : Integrable r (withDensityReal (thermalDensity d s a β)) :=
    (HRS.MS.Tc5.tc5_memLp_of_cb hr).integrable one_le_two
  have hr0 : ∫ x, r x ∂(withDensityReal (thermalDensity d s a β)) = 0 :=
    (integral_congr_ae hrr).trans hr₀.2
  obtain ⟨χ, hχc, -, -, hgen, -, -, hder⟩ :=
    hP s a β hs0 hsd ha hβ le_rfl le_rfl hdr r hr hri hr0
  have hrc : Continuous r := hr.1.continuous
  have hX0 : 0 ≤ cbNorm (k + 1) r := HRS.MS.Tc5.tc5_cb_nonneg _ r
  obtain ⟨hrep, hrespW⟩ := HRS.MS.S98.s98_resp_rep (d := d) (by omega) hs0 hsd hc hTc hγ (hPc φ hφ) hrc
    (B := cbNorm (k + 1) r) (fun x => by
      have := HRS.MS.Tc5.tc5_cb_sup_le hr x
      rwa [Real.norm_eq_abs] at this) hr₀ hae hrr
  have hrepf : responseRepW (rieszKernel d s) (withDensityReal (thermalDensity d s a β)) γ φ =
      fun x => γ⁻¹ * r x := funext hrep
  have hμ : thermalMeasure d s a β = withDensityReal (thermalDensity d s a β) := rfl
  have hnf := hnf φ hφ
  have hXn : cbNorm (k + 1) r ≤ C5 * nf φ := hbd
  refine ⟨χ, hχc, ?_, ?_, ?_, ?_, ?_⟩
  · intro x j hj
    have h1 : ‖iteratedFDeriv ℝ (j + 1) χ x‖ ≤ ∑ i : Fin (k + 1), ‖iteratedFDeriv ℝ ((i : ℕ) + 1) χ x‖ :=
      Finset.single_le_sum (f := fun i : Fin (k + 1) => ‖iteratedFDeriv ℝ ((i : ℕ) + 1) χ x‖)
        (fun i _ => norm_nonneg _) (Finset.mem_univ (⟨j, by omega⟩ : Fin (k + 1)))
    have h2 := (h1.trans (hder fun _ => x)).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hX0)
    calc ‖iteratedFDeriv ℝ (j + 1) χ x‖ ≤ |Cm| * cbNorm (k + 1) r := h2
      _ ≤ |Cm| * (C5 * nf φ) := mul_le_mul_of_nonneg_left hXn (abs_nonneg _)
      _ ≤ (|Cm| + γ⁻¹) * C5 * nf φ := by
          have : 0 ≤ γ⁻¹ * (C5 * nf φ) := by positivity
          nlinarith
  · intro x
    rw [hμ, hrepf]
    simp only
    rw [hgen x]
    field_simp
  · rw [hμ]; exact hrespW
  · rw [hμ, hrepf]
    exact (HRS.MS.Tc5.tc5_cb_smul γ⁻¹ (HRS.MS.Tc5.tc5_cb_mono (Nat.le_succ k) hr).1).1
  · rw [hμ, hrepf]
    have := (HRS.MS.Tc5.tc5_cb_smul γ⁻¹ (HRS.MS.Tc5.tc5_cb_mono (Nat.le_succ k) hr).1).2
    rw [abs_of_nonneg (inv_nonneg.2 hγ.le)] at this
    have h3 := this.trans (mul_le_mul_of_nonneg_left (HRS.MS.Tc5.tc5_cb_mono (Nat.le_succ k) hr).2
        (inv_nonneg.2 hγ.le))
    calc cbNorm k (fun x => γ⁻¹ * r x) ≤ γ⁻¹ * cbNorm (k + 1) r := h3
      _ ≤ γ⁻¹ * (C5 * nf φ) := mul_le_mul_of_nonneg_left hXn (inv_nonneg.2 hγ.le)
      _ ≤ (|Cm| + γ⁻¹) * C5 * nf φ := by
          have : 0 ≤ |Cm| * (C5 * nf φ) := by positivity
          nlinarith

/-- **The corrector at order `k`, `C_b^J` data.** -/
theorem s99_chi (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ) (hk : 1 ≤ k)
    (a β γ : ℝ) (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ) (J : ℕ)
    (hJ : (k : ℝ) + 1 + (d : ℝ) / 2 < J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Euc d → ℝ, MemCb J φ → ∃ χ : Euc d → ℝ,
      ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) χ ∧
      (∀ x, ∀ j ≤ k, ‖iteratedFDeriv ℝ (j + 1) χ x‖ ≤ C * cbNorm J φ) ∧
      (∀ x, thermalGen d s a β χ x =
        γ * responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ φ x) ∧
      IsResponse (rieszKernel d s) (thermalMeasure d s a β) γ φ
        (responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ φ) ∧
      MemCb k (responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ φ) ∧
      cbNorm k (responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ φ) ≤ C * cbNorm J φ := by
  have hd2 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hα : 0 < (d : ℝ) - s := by
    have : (s : ℝ) < d := hsd
    linarith
  set m : ℕ := k + 1 with hm
  have hmJ : m ≤ J := by
    have : ((m : ℕ) : ℝ) ≤ J := by
      rw [hm]; push_cast; linarith
    exact_mod_cast this
  set M : ℕ := ⌈((m : ℝ) + d / 2) / ((d : ℝ) - s)⌉₊ + 1 with hM
  have hMs : (m : ℝ) + d / 2 < M * ((d : ℝ) - s) := HRS.MS.Tc5.tc5_M_spec hsd m
  set N0 : ℕ := m + ⌈(M : ℝ) * ((d : ℝ) - s) + d⌉₊ + 1 with hN0
  have hmN : m ≤ N0 := by omega
  have hN : (M : ℝ) * ((d : ℝ) - s) + d < N0 := by
    have h1 := Nat.le_ceil ((M : ℝ) * ((d : ℝ) - s) + d)
    have : ((⌈(M : ℝ) * ((d : ℝ) - s) + d⌉₊ : ℕ) : ℝ) + 1 ≤ N0 := by
      rw [hN0]; push_cast; have : (0 : ℝ) ≤ m := by positivity
      linarith
    linarith
  exact s99_core hd hs0 hsd k hk a β γ ha hβ hγ (MemCb J) (cbNorm J)
    (fun φ _ => HRS.MS.Tc5.tc5_cb_nonneg J φ) (fun φ hφ => hφ.1.continuous)
    ⟨N0, fun M₀ c S hc => HRS.MS.Tc5.tc5_resolvent_rep (d := d) hs0 hsd m J M hmJ hMs γ M₀ c S hc N0 hmN hN
      |>.imp fun C hC => hC⟩

/-! ### Feature data and the norm of `⟨v, ∇ψ⟩` -/

theorem s99_norm_iter_le_cb {k : ℕ} {Φ : Euc d → ℝ} (hΦ : MemCb k Φ) {j : ℕ} (hj : j ≤ k) (x : Euc d) :
    ‖iteratedFDeriv ℝ j Φ x‖ ≤ cbNorm k Φ := by
  have h1 := le_ciSup (hΦ.2 j hj) x
  have h2 : (⨆ z : Euc d, ‖iteratedFDeriv ℝ j Φ z‖) ≤ cbNorm k Φ := by
    unfold cbNorm
    exact Finset.single_le_sum (f := fun i => ⨆ z : Euc d, ‖iteratedFDeriv ℝ i Φ z‖)
      (fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  exact h1.trans h2

/-- `⟨v, ∇ψ⟩ ∈ C_b^{J'}` with a Leibniz bound. -/
theorem s99_inner_cb {J' : ℕ} {v : Euc d → Euc d} (hv : ContDiff ℝ J' v) {Bv : ℝ}
    (hBv : ∀ x, ∀ i ≤ J', ‖iteratedFDeriv ℝ i v x‖ ≤ Bv) {ψ : Euc d → ℝ} (hψ : MemCb (J' + 1) ψ) :
    MemCb J' (fun x => inner ℝ (v x) (gradient ψ x)) ∧
      cbNorm J' (fun x => inner ℝ (v x) (gradient ψ x)) ≤
        ((J' : ℝ) + 1) * 2 ^ J' * Bv * cbNorm (J' + 1) ψ := by
  have hBv0 : 0 ≤ Bv := (norm_nonneg _).trans (hBv 0 0 (Nat.zero_le _))
  have hcb0 : 0 ≤ cbNorm (J' + 1) ψ := HRS.MS.Tc5.tc5_cb_nonneg _ ψ
  have hg : ContDiff ℝ J' (fun y => gradient ψ y) := by
    have := HRS.MS.S98.s98_gL_contDiff (k := J') (χ := ψ) hψ.1 1
    simpa using this
  have hI : ContDiff ℝ J' (fun x => inner ℝ (v x) (gradient ψ x)) := hv.inner ℝ hg
  have hder : ∀ x, ∀ n ≤ J', ‖iteratedFDeriv ℝ n (fun x => inner ℝ (v x) (gradient ψ x)) x‖ ≤
      2 ^ J' * Bv * cbNorm (J' + 1) ψ := by
    intro x n hn
    have h1 := (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear_of_le_one
      (f := v) (g := fun y => gradient ψ y) (N := (J' : ℕ∞ω)) hv hg x (n := n) (by exact_mod_cast hn)
      (by simpa using (norm_innerSL_le (𝕜 := ℝ) (E := Euc d)))
    have e : (fun y => (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (v y) (gradient ψ y)) =
        fun y => inner ℝ (v y) (gradient ψ y) := by
      funext y; simp [innerSL_apply_apply]
    rw [e] at h1
    refine h1.trans ?_
    calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i v x‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y => gradient ψ y) x‖
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (Bv * cbNorm (J' + 1) ψ) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have h2 := hBv x i (hi'.trans hn)
          have h3 : ‖iteratedFDeriv ℝ (n - i) (fun y => gradient ψ y) x‖ ≤ cbNorm (J' + 1) ψ := by
            have := HRS.MS.S98.s98_gL_iter (k := J') (χ := ψ) hψ.1 1 (j := n - i) (by omega) x
            simp only [one_smul, abs_one, one_mul] at this
            exact this.trans (s99_norm_iter_le_cb hψ (by omega) x)
          have h0 : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
          calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i v x‖ * ‖iteratedFDeriv ℝ (n - i) (fun y => gradient ψ y) x‖
              ≤ (n.choose i : ℝ) * Bv * cbNorm (J' + 1) ψ := by
                refine mul_le_mul (mul_le_mul_of_nonneg_left h2 h0) h3 (norm_nonneg _) (by positivity)
            _ = (n.choose i : ℝ) * (Bv * cbNorm (J' + 1) ψ) := by ring
      _ = 2 ^ n * (Bv * cbNorm (J' + 1) ψ) := by
          rw [← Finset.sum_mul]
          have : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
            exact_mod_cast Nat.sum_range_choose n
          rw [this]
      _ ≤ 2 ^ J' * (Bv * cbNorm (J' + 1) ψ) := by
          gcongr
          · norm_num
      _ = 2 ^ J' * Bv * cbNorm (J' + 1) ψ := by ring
  refine ⟨⟨hI, fun j hj => ⟨2 ^ J' * Bv * cbNorm (J' + 1) ψ, ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hder x j hj
  · unfold cbNorm
    calc ∑ j ∈ Finset.range (J' + 1), ⨆ x : Euc d,
          ‖iteratedFDeriv ℝ j (fun x => inner ℝ (v x) (gradient ψ x)) x‖
        ≤ ∑ _j ∈ Finset.range (J' + 1), 2 ^ J' * Bv * cbNorm (J' + 1) ψ := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact ciSup_le fun x => hder x j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      _ = ((J' : ℝ) + 1) * 2 ^ J' * Bv * cbNorm (J' + 1) ψ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- The corrector data give `S46Feat` (the input of the Stein identity of S4.6). -/
theorem s99_feat_S46 {s a β γ C c BU : ℝ} (hT : S45.ThermalData d s a β C c BU) (hγ : 0 < γ)
    {k : ℕ} (hk : 1 ≤ k) {φ χ : Euc d → ℝ} {B : ℝ}
    (hχ : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) χ)
    (hder : ∀ x, ∀ j ≤ k, ‖iteratedFDeriv ℝ (j + 1) χ x‖ ≤ B)
    (hgen : ∀ x, thermalGen d s a β χ x =
      γ * responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ φ x)
    (hresp : IsResponse (rieszKernel d s) (thermalMeasure d s a β) γ φ
      (responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ φ))
    (hmem : MemCb k (responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ φ)) :
    S46.S46Feat d s a β γ φ χ B := by
  haveI : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  set μ := thermalMeasure d s a β with hμ
  set aφ := responseRepW (rieszKernel d s) μ γ φ with haφ
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by exact_mod_cast (by omega : 2 ≤ k + 1))
  have hgenf : thermalGen d s a β χ = fun x => γ * aφ x := funext hgen
  refine ⟨hχ2, fun x => ?_, fun x => ?_, ?_, ?_⟩
  · rw [S45.s45_norm_gradient, ← norm_iteratedFDeriv_one]
    exact hder x 0 (Nat.zero_le _)
  · exact (S45.s45_norm_fderiv_gradient hχ2 x).trans (hder x 1 hk)
  · filter_upwards [hresp.2] with x hx
    unfold susceptibilityOp
    rw [hgenf, HRS.MS.S98.s98_kop_smul]
    have : γ⁻¹ * (γ * aφ x) + γ * Kop (rieszKernel d s) μ aφ x = aφ x + γ * Kop (rieszKernel d s) μ aφ x := by
      field_simp
    rw [this]; exact hx
  · rw [hgenf]
    exact (HRS.MS.Tc5.tc5_memLp_of_cb hmem).const_mul γ

end S99

end
