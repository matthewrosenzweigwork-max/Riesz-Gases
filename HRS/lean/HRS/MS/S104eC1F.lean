import HRS.MS.S104eC1A
import HRS.MS.S104eC1E

/-!
# S104E route C, packet C1 (part F): `c1_ou_gain` (Hölder gain `h^{-(1+η)/2}`)

Interpolation of `‖D^{j+1}P_h f‖ ≤ K B h^{-1/2}` and the Lipschitz bound `K B h^{-1} ‖z‖` (for `‖z‖ ≤ s₀ h^{1/2}`)
into the `η`-Hölder bound `K' B h^{-(1+η)/2} ‖z‖^η`.
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace HRS.MS.S104e.C
open HRS HRS.Whole HRS.MS.Wad HRS.MS.R2WinOrbNL HRS.MS.Ul
variable {d : ℕ}

theorem s104c1_interp {K B s0 q t η D : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hs0 : 0 < s0) (hq : 0 < q)
    (ht : 0 ≤ t) (hη0 : 0 < η) (hη1 : η < 1) (hD1 : D ≤ 2 * K * B * q⁻¹)
    (hD2 : t ≤ s0 * q → D ≤ K * B * (q * q)⁻¹ * t) :
    D ≤ K * (s0 ^ (1 - η) + 2 * s0 ^ (-η)) * B * q ^ (-(1 + η)) * t ^ η := by
  have hqe : q ^ (-(1 + η)) = q ^ (-(1 : ℝ)) * q ^ (-η) := by
    rw [← Real.rpow_add hq]; congr 1; ring
  have hqe2 : q ^ (-(1 + η)) = (q * q)⁻¹ * q ^ (1 - η) := by
    have : q ^ (-(1 + η)) = q ^ (-(2 : ℝ)) * q ^ (1 - η) := by
      rw [← Real.rpow_add hq]; congr 1; ring
    rw [this, Real.rpow_neg hq.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_two]
  have hq1 : q ^ (-(1 : ℝ)) = q⁻¹ := by rw [Real.rpow_neg hq.le, Real.rpow_one]
  have hpos : 0 ≤ K * B * q ^ (-(1 + η)) * t ^ η := by positivity
  by_cases hc : t ≤ s0 * q
  · refine (hD2 hc).trans ?_
    have h1 : t ≤ t ^ η * (s0 ^ (1 - η) * q ^ (1 - η)) := by
      rcases ht.eq_or_lt with h0 | h0
      · rw [← h0, Real.zero_rpow hη0.ne']; simp
      · have : t = t ^ η * t ^ (1 - η) := by
          rw [← Real.rpow_add h0]; simp
        calc t = t ^ η * t ^ (1 - η) := this
          _ ≤ t ^ η * (s0 * q) ^ (1 - η) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht hc (by linarith)) (by positivity)
          _ = _ := by rw [Real.mul_rpow hs0.le hq.le]
    calc K * B * (q * q)⁻¹ * t ≤ K * B * (q * q)⁻¹ * (t ^ η * (s0 ^ (1 - η) * q ^ (1 - η))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = K * s0 ^ (1 - η) * B * ((q * q)⁻¹ * q ^ (1 - η)) * t ^ η := by ring
      _ = K * s0 ^ (1 - η) * B * q ^ (-(1 + η)) * t ^ η := by rw [hqe2]
      _ ≤ K * (s0 ^ (1 - η) + 2 * s0 ^ (-η)) * B * q ^ (-(1 + η)) * t ^ η := by
          have : 0 ≤ K * (2 * s0 ^ (-η)) * B * q ^ (-(1 + η)) * t ^ η := by positivity
          nlinarith
  · push Not at hc
    refine hD1.trans ?_
    have hr : 1 ≤ (t / (s0 * q)) ^ η :=
      Real.one_le_rpow ((one_le_div (by positivity)).2 hc.le) hη0.le
    have ht0 : 0 < t := lt_of_le_of_lt (by positivity) hc
    have e : (t / (s0 * q)) ^ η = t ^ η * (s0 ^ (-η) * q ^ (-η)) := by
      rw [Real.div_rpow ht (by positivity), Real.mul_rpow hs0.le hq.le, Real.rpow_neg hs0.le,
        Real.rpow_neg hq.le]; field_simp
    calc 2 * K * B * q⁻¹ ≤ 2 * K * B * q⁻¹ * (t / (s0 * q)) ^ η := by
          have : 0 ≤ 2 * K * B * q⁻¹ := by positivity
          nlinarith
      _ = 2 * K * s0 ^ (-η) * B * (q ^ (-(1 : ℝ)) * q ^ (-η)) * t ^ η := by
          rw [e, hq1]; ring
      _ = 2 * K * s0 ^ (-η) * B * q ^ (-(1 + η)) * t ^ η := by rw [hqe]
      _ ≤ K * (s0 ^ (1 - η) + 2 * s0 ^ (-η)) * B * q ^ (-(1 + η)) * t ^ η := by
          have : 0 ≤ K * s0 ^ (1 - η) * B * q ^ (-(1 + η)) * t ^ η := by positivity
          nlinarith

theorem s104c1_rpow_h {h η : ℝ} (hh : 0 < h) : (Real.sqrt h) ^ (-(1 + η)) = h ^ (-((1 + η) / 2)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hh.le]; congr 1; ring

theorem s104c1_sqrt_inv {h η : ℝ} (hh : 0 < h) (hη : 0 ≤ η) :
    (Real.sqrt h)⁻¹ ≤ 1 + h ^ (-((1 + η) / 2)) := by
  have hq : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hp : 0 ≤ h ^ (-((1 + η) / 2)) := Real.rpow_nonneg hh.le _
  by_cases h1 : h ≤ 1
  · have : (Real.sqrt h)⁻¹ ≤ h ^ (-((1 + η) / 2)) := by
      rw [← s104c1_rpow_h hh]
      have hq1 : Real.sqrt h ≤ 1 := Real.sqrt_le_one.2 h1
      calc (Real.sqrt h)⁻¹ = (Real.sqrt h) ^ (-(1 : ℝ)) := by rw [Real.rpow_neg hq.le, Real.rpow_one]
        _ ≤ (Real.sqrt h) ^ (-(1 + η)) := Real.rpow_le_rpow_of_exponent_ge hq hq1 (by linarith)
    linarith
  · push Not at h1
    have : (Real.sqrt h)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hq]; exact Real.one_le_sqrt.2 h1.le
    linarith

/-- Gain of `1 + η` derivatives at cost `h^{-(1+η)/2}`. -/
theorem c1_ou_gain (a ν : ℝ) (ha : 0 < a) (hν : 0 < ν) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (j : ℕ)
    (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ H → ∀ (B : ℝ) (f : Euc d → ℝ), Bd j B f →
      HolB j η (C * (1 + h ^ (-((1 + η) / 2))) * B) (ouSg (ouQ d a) ν h f) := by
  obtain ⟨K, s0, hK, hs0, hcore⟩ := s104c1_gain_core (d := d) a ν (max H 1) ha hν
  set c : ℝ := K * (s0 ^ (1 - η) + 2 * s0 ^ (-η)) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨max (max 1 K) c, le_max_of_le_left (le_max_of_le_left zero_le_one), fun h hh hH B f hf => ?_⟩
  have hB : 0 ≤ B := hf.nonneg
  have hfc : Continuous f := hf.1.continuous
  have hOP := s104c1_ouSg (d := d) ha hν.le hh.le hfc
  rw [hOP]
  obtain ⟨hC, hb1, hb2⟩ := hcore j hf hh (hH.trans (le_max_left _ _))
  have hst : Bd j B (s83_P a ν h f) := by
    have := s104c1_stab a ν ha hν j hh.le hf
    rwa [hOP] at this
  set Cc : ℝ := max (max 1 K) c with hCc
  have hCc1 : 1 ≤ Cc := le_max_of_le_left (le_max_left _ _)
  have hCcK : K ≤ Cc := le_max_of_le_left (le_max_right _ _)
  have hCcc : c ≤ Cc := le_max_right _ _
  set q : ℝ := Real.sqrt h with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 hh
  set p : ℝ := h ^ (-((1 + η) / 2)) with hp
  have hp0 : 0 ≤ p := Real.rpow_nonneg hh.le _
  have hsi : q⁻¹ ≤ 1 + p := s104c1_sqrt_inv hh hη0.le
  have hCp : 0 ≤ Cc * (1 + p) := by positivity
  have hhq : q * q = h := Real.mul_self_sqrt hh.le
  refine ⟨⟨hC, fun i hi x => ?_⟩, fun x z => ?_⟩
  · rcases Nat.lt_or_ge i (j + 1) with hi' | hi'
    · refine (hst.2 i (by omega) x).trans ?_
      nlinarith [mul_nonneg hB hp0]
    · have hij : i = j + 1 := le_antisymm hi hi'
      subst hij
      refine (hb1 x).trans ?_
      calc K * B * q⁻¹ ≤ Cc * B * (1 + p) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hCcK hB) hsi (by positivity) (by positivity)
        _ = Cc * (1 + p) * B := by ring
  · set D : ℝ := ‖iteratedFDeriv ℝ (j + 1) (s83_P a ν h f) (x + z) -
      iteratedFDeriv ℝ (j + 1) (s83_P a ν h f) x‖ with hD
    have hD1 : D ≤ 2 * K * B * q⁻¹ := by
      refine (norm_sub_le _ _).trans ?_
      have h1 := hb1 (x + z)
      have h2 := hb1 x
      calc _ ≤ K * B * q⁻¹ + K * B * q⁻¹ := add_le_add h1 h2
        _ = 2 * K * B * q⁻¹ := by ring
    have hD2 : ‖z‖ ≤ s0 * q → D ≤ K * B * (q * q)⁻¹ * ‖z‖ := fun hz => by
      have := hb2 x (x + z) (by rwa [add_sub_cancel_left])
      rw [add_sub_cancel_left] at this
      rw [hhq]; exact this
    have key := s104c1_interp (K := K) (B := B) (s0 := s0) (q := q) (t := ‖z‖) (η := η) (D := D) hK hB hs0
      hq0 (norm_nonneg _) hη0 hη1 hD1 hD2
    refine key.trans ?_
    rw [hq, s104c1_rpow_h hh, ← hp]
    have : 0 ≤ B * p * ‖z‖ ^ η := by positivity
    calc K * (s0 ^ (1 - η) + 2 * s0 ^ (-η)) * B * p * ‖z‖ ^ η = c * (B * p * ‖z‖ ^ η) := by rw [hc]; ring
      _ ≤ Cc * (B * p * ‖z‖ ^ η) := mul_le_mul_of_nonneg_right hCcc this
      _ ≤ Cc * (1 + p) * B * ‖z‖ ^ η := by
          have : 0 ≤ Cc * B * ‖z‖ ^ η := by positivity
          nlinarith

end HRS.MS.S104e.C
