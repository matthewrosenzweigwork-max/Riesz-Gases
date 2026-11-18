import HRS.MC.E214FKC
import HRS.MC.E214FGauss

/-!
# E214F-Assemble: P4 from coordinate estimates (abstract reduction)

`sup_moment_of_coordinates`: an a.s. continuous process `X` in `E_m = NegSobolev d m` whose coordinates are
centred Gaussians with (i) fixed-time decay `E ξ_k(t)² ≤ A e^{-ct} wA_k` and (ii) increments
`E (ξ_k(t) - ξ_k(s))² ≤ B |t-s|^γ wB_k` (`wA, wB` summable) satisfies, for every `p ≥ 2` and window `T`,
`E sup_{t∈[0,T]} ‖X(a+t)‖^p ≤ (C e^{-κ a})^p` for all `a ≥ 0`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.E214F

variable {d : ℕ} {m : ℝ}

theorem coord_sub' (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k := rfl

/-- Increment moments of order `P` from the coordinate estimates (interpolating decay and smallness). -/
theorem increment_moment {A0 B0 c γ : ℝ} (hA0 : 0 < A0) (hB0 : 0 < B0) (hc : 0 < c) (hγ : 0 < γ)
    {P : ℝ} (hP : 2 ≤ P) (wA wB : NonzeroLattice d → ℝ)
    (hwA0 : ∀ k, 0 ≤ wA k) (hwB0 : ∀ k, 0 ≤ wB k) (hwA : Summable wA) (hwB : Summable wB) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℝ → Ω → NegSobolev d m)
      (hdec : ∀ t, 0 ≤ t → ∀ k, ∫ ω, NegSobolev.coord (X t ω) k ^ 2 ∂μ ≤ A0 * Real.exp (-c * t) * wA k)
      (hinc : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ k,
        ∫ ω, (NegSobolev.coord (X t ω) k - NegSobolev.coord (X s ω) k) ^ 2 ∂μ ≤
          B0 * |t - s| ^ γ * wB k)
      (hG : ∀ t, 0 ≤ t → ∀ k, HasGaussianLaw (fun ω => NegSobolev.coord (X t ω) k) μ)
      (hGi : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ k, HasGaussianLaw
        (fun ω => NegSobolev.coord (X t ω) k - NegSobolev.coord (X s ω) k) μ)
      (hGi0 : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ k,
        ∫ ω, (NegSobolev.coord (X t ω) k - NegSobolev.coord (X s ω) k) ∂μ = 0)
      (a s t : ℝ), 0 ≤ a → a ≤ s → a ≤ t →
      ∫⁻ ω, ‖X t ω - X s ω‖ₑ ^ P ∂μ ≤
        ENNReal.ofReal (C0 * Real.exp (-c * a * P / 4) * |t - s| ^ (γ * P / 4)) := by
  obtain ⟨Cg, hCg, hmain⟩ := lintegral_norm_rpow_le (d := d) (m := m) hP
  set W : ℝ := ∑' k, (wA k + wB k) with hW
  have hW0 : 0 ≤ W := tsum_nonneg fun k => add_nonneg (hwA0 k) (hwB0 k)
  have hsumW : Summable fun k => wA k + wB k := hwA.add hwB
  have hP0 : 0 < P := by linarith
  refine ⟨(Cg + 1) * (A0 * B0) ^ (P / 4) * (W + 1) ^ (P / 2), by positivity, ?_⟩
  intro Ω _ μ _ X hdec hinc hG hGi hGi0 a s t ha has hat
  have hs0 : 0 ≤ s := ha.trans has
  have ht0 : 0 ≤ t := ha.trans hat
  set Q : ℝ := Real.sqrt (A0 * B0) * Real.exp (-c * a / 2) * |t - s| ^ (γ / 2) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hbd : ∀ k, ∫ ω, NegSobolev.coord ((X t ω - X s ω)) k ^ 2 ∂μ ≤ Q * (wA k + wB k) := by
    intro k
    simp_rw [coord_sub']
    set E := ∫ ω, (NegSobolev.coord (X t ω) k - NegSobolev.coord (X s ω) k) ^ 2 ∂μ with hE
    have hE0 : 0 ≤ E := integral_nonneg fun ω => sq_nonneg _
    have hy : E ≤ B0 * |t - s| ^ γ * wB k := hinc s t hs0 ht0 k
    have hx : E ≤ 4 * (A0 * Real.exp (-c * a) * wA k) := by
      have hft := (hG t ht0 k).memLp_two
      have hfs := (hG s hs0 k).memLp_two
      have i1 := hft.integrable_sq
      have i2 := hfs.integrable_sq
      calc E ≤ ∫ ω, (2 * NegSobolev.coord (X t ω) k ^ 2 + 2 * NegSobolev.coord (X s ω) k ^ 2) ∂μ := by
            refine integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
              ((i1.const_mul 2).add (i2.const_mul 2)) (ae_of_all _ fun ω => ?_)
            nlinarith [sq_nonneg (NegSobolev.coord (X t ω) k + NegSobolev.coord (X s ω) k)]
        _ = 2 * ∫ ω, NegSobolev.coord (X t ω) k ^ 2 ∂μ + 2 * ∫ ω, NegSobolev.coord (X s ω) k ^ 2 ∂μ := by
            rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul]
        _ ≤ 4 * (A0 * Real.exp (-c * a) * wA k) := by
            have e1 := hdec t ht0 k
            have e2 := hdec s hs0 k
            have x1 : Real.exp (-c * t) ≤ Real.exp (-c * a) := Real.exp_le_exp.2 (by nlinarith)
            have x2 : Real.exp (-c * s) ≤ Real.exp (-c * a) := Real.exp_le_exp.2 (by nlinarith)
            have y1 : A0 * Real.exp (-c * t) * wA k ≤ A0 * Real.exp (-c * a) * wA k := by
              gcongr; exact hwA0 k
            have y2 : A0 * Real.exp (-c * s) * wA k ≤ A0 * Real.exp (-c * a) * wA k := by
              gcongr; exact hwA0 k
            linarith
    have hxy : E * E ≤ (4 * (A0 * Real.exp (-c * a) * wA k)) * (B0 * |t - s| ^ γ * wB k) :=
      mul_le_mul hx hy hE0 (by have := hwA0 k; positivity)
    have hQsq : Q ^ 2 = A0 * B0 * Real.exp (-c * a) * |t - s| ^ γ := by
      rw [hQ, mul_pow, mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul,
        ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      push_cast
      rw [show 2 * (-c * a / 2) = -c * a by ring, show γ / 2 * 2 = γ by ring]
    have hab : 4 * wA k * wB k ≤ (wA k + wB k) ^ 2 := by nlinarith [sq_nonneg (wA k - wB k)]
    have hR : E * E ≤ (Q * (wA k + wB k)) * (Q * (wA k + wB k)) := by
      refine hxy.trans ?_
      have : (4 * (A0 * Real.exp (-c * a) * wA k)) * (B0 * |t - s| ^ γ * wB k) =
          Q ^ 2 * (4 * wA k * wB k) := by rw [hQsq]; ring
      rw [this]
      nlinarith [sq_nonneg Q, mul_le_mul_of_nonneg_left hab (sq_nonneg Q)]
    have hRn : 0 ≤ Q * (wA k + wB k) := mul_nonneg hQ0 (add_nonneg (hwA0 k) (hwB0 k))
    nlinarith
  have hbd0 : ∀ k, 0 ≤ Q * (wA k + wB k) := fun k => mul_nonneg hQ0 (add_nonneg (hwA0 k) (hwB0 k))
  have h := hmain μ (fun ω => X t ω - X s ω) (fun k => Q * (wA k + wB k)) hbd0
    (hsumW.mul_left Q) (fun k => by simpa [coord_sub'] using hGi s t hs0 ht0 k)
    (fun k => by simpa [coord_sub'] using hGi0 s t hs0 ht0 k) hbd
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [tsum_mul_left, ← hW, Real.mul_rpow hQ0 hW0]
  have hQP : Q ^ (P / 2) = (A0 * B0) ^ (P / 4) * Real.exp (-c * a * P / 4) * |t - s| ^ (γ * P / 4) := by
    have f1 : Real.sqrt (A0 * B0) ^ (P / 2) = (A0 * B0) ^ (P / 4) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
      congr 1; ring
    have f2 : Real.exp (-c * a / 2) ^ (P / 2) = Real.exp (-c * a * P / 4) := by
      rw [← Real.exp_mul]; congr 1; ring
    have f3 : (|t - s| ^ (γ / 2)) ^ (P / 2) = |t - s| ^ (γ * P / 4) := by
      rw [← Real.rpow_mul (abs_nonneg _)]
      congr 1; ring
    rw [hQ, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      f1, f2, f3]
  rw [hQP]
  have hW1 : W ^ (P / 2) ≤ (W + 1) ^ (P / 2) :=
    Real.rpow_le_rpow hW0 (by linarith) (by positivity)
  have hpos : 0 ≤ (A0 * B0) ^ (P / 4) * Real.exp (-c * a * P / 4) * |t - s| ^ (γ * P / 4) := by positivity
  calc Cg * ((A0 * B0) ^ (P / 4) * Real.exp (-c * a * P / 4) * |t - s| ^ (γ * P / 4) * W ^ (P / 2))
      ≤ (Cg + 1) * ((A0 * B0) ^ (P / 4) * Real.exp (-c * a * P / 4) * |t - s| ^ (γ * P / 4) * (W + 1) ^ (P / 2)) := by
        gcongr
        linarith
    _ = _ := by ring

/-- **P4 from coordinate estimates.**  An a.s. continuous process in `E_m` whose coordinates are centred
Gaussian, with coordinate decay `E ξ_k(t)² ≤ A0 e^{-ct} wA_k` and coordinate increments
`E (ξ_k(t)-ξ_k(s))² ≤ B0 |t-s|^γ wB_k`, satisfies `E sup_{t∈[0,T]} ‖X(a+t)‖^p ≤ (C e^{-κ a})^p`. -/
theorem sup_moment_of_coordinates {A0 B0 c γ : ℝ} (hA0 : 0 < A0) (hB0 : 0 < B0) (hc : 0 < c)
    (hγ : 0 < γ) (wA wB : NonzeroLattice d → ℝ)
    (hwA0 : ∀ k, 0 ≤ wA k) (hwB0 : ∀ k, 0 ≤ wB k) (hwA : Summable wA) (hwB : Summable wB)
    {T : ℝ} (hT : 0 < T) {p : ℝ} (hp : 2 ≤ p) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℝ → Ω → NegSobolev d m) (hXm : ∀ t, Measurable (X t))
      (hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Ici 0))
      (hdec : ∀ t, 0 ≤ t → ∀ k, ∫ ω, NegSobolev.coord (X t ω) k ^ 2 ∂μ ≤ A0 * Real.exp (-c * t) * wA k)
      (hinc : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ k,
        ∫ ω, (NegSobolev.coord (X t ω) k - NegSobolev.coord (X s ω) k) ^ 2 ∂μ ≤
          B0 * |t - s| ^ γ * wB k)
      (hG : ∀ t, 0 ≤ t → ∀ k, HasGaussianLaw (fun ω => NegSobolev.coord (X t ω) k) μ)
      (hG0 : ∀ t, 0 ≤ t → ∀ k, ∫ ω, NegSobolev.coord (X t ω) k ∂μ = 0)
      (hGi : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ k, HasGaussianLaw
        (fun ω => NegSobolev.coord (X t ω) k - NegSobolev.coord (X s ω) k) μ)
      (hGi0 : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ k,
        ∫ ω, (NegSobolev.coord (X t ω) k - NegSobolev.coord (X s ω) k) ∂μ = 0)
      (a : ℝ), 0 ≤ a →
      ∫⁻ ω, (⨆ t ∈ Icc (0 : ℝ) T, ‖X (a + t) ω‖ₑ) ^ p ∂μ ≤
        ENNReal.ofReal ((C * Real.exp (-κ * a)) ^ p) := by
  set P : ℝ := max (2 * p) (4 / γ + 1) with hPdef
  have hP2 : 2 * p ≤ P := le_max_left _ _
  have hP4 : 4 / γ + 1 ≤ P := le_max_right _ _
  have hP : 2 ≤ P := by linarith
  have hp0 : 0 < p := by linarith
  have hpP : p < P := by linarith
  set β : ℝ := γ * P / 4 - 1 with hβdef
  have hβ : 0 < β := by
    have : 4 / γ < P := by linarith
    rw [div_lt_iff₀ hγ] at this
    rw [hβdef]; linarith
  obtain ⟨C0, hC0, hinc_mom⟩ := increment_moment (d := d) (m := m) hA0 hB0 hc hγ hP wA wB hwA0 hwB0 hwA hwB
  obtain ⟨C1, hC1, hkc⟩ := kc_sup_moment (E := NegSobolev d m) hp0 hpP hβ
  obtain ⟨Cg, hCg, hnorm⟩ := lintegral_norm_rpow_le (d := d) (m := m) hp
  set WA : ℝ := ∑' k, wA k with hWA
  have hWA0 : 0 ≤ WA := tsum_nonneg hwA0
  set K1 : ℝ := C1 * (C0 * T ^ (1 + β)) ^ (p / P) with hK1
  set K2 : ℝ := Cg * (A0 * WA) ^ (p / 2) with hK2
  have hK1n : 0 ≤ K1 := by positivity
  have hK2n : 0 ≤ K2 := by positivity
  set Cf : ℝ := (2 ^ (p - 1) * (K1 + K2) + 1) ^ (1 / p) with hCf
  have hbase : 0 < 2 ^ (p - 1) * (K1 + K2) + 1 := by positivity
  refine ⟨Cf, c / 4, Real.rpow_pos_of_pos hbase _, by positivity, ?_⟩
  intro Ω _ μ _ X hXm hcont hdec hinc hG hG0 hGi hGi0 a ha
  -- the shifted process on [0,T]
  set Y : ℝ → Ω → NegSobolev d m := fun t => X (a + t) with hY
  have hYm : ∀ t, Measurable (Y t) := fun t => hXm _
  have hYc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => Y t ω) (Icc 0 T) := by
    filter_upwards [hcont] with ω hω
    exact hω.comp (continuousOn_const.add continuousOn_id) (fun t ht => by
      simp only [mem_Ici]; linarith [ht.1])
  have hexp : ∀ x : ℝ, Real.exp x ^ (p / P) = Real.exp (x * (p / P)) := fun x => (Real.exp_mul x _).symm
  have hmomY : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖Y t ζ - Y s ζ‖ₑ ^ P ∂μ ≤
        ENNReal.ofReal ((C0 * Real.exp (-c * a * P / 4)) * |t - s| ^ (1 + β)) := by
    intro s hs t ht
    have := hinc_mom μ X hdec hinc hG hGi hGi0 a (a + s) (a + t) ha (by linarith [hs.1])
      (by linarith [ht.1])
    have e : |a + t - (a + s)| = |t - s| := by congr 1; ring
    rw [e] at this
    have e2 : γ * P / 4 = 1 + β := by rw [hβdef]; ring
    rw [e2] at this
    exact this
  have hsup := hkc μ Y hYm hT (mul_pos hC0 (Real.exp_pos _)) hmomY hYc
  have hY0 : Y 0 = X a := by simp [hY]
  rw [hY0] at hsup
  -- the initial term
  have hinit : ∫⁻ ω, ‖X a ω‖ₑ ^ p ∂μ ≤ ENNReal.ofReal (K2 * Real.exp (-c * a * p / 2)) := by
    have hw0 : ∀ k, 0 ≤ A0 * Real.exp (-c * a) * wA k := fun k => by
      have := hwA0 k; positivity
    have h := hnorm μ (X a) (fun k => A0 * Real.exp (-c * a) * wA k) hw0 (hwA.mul_left _)
      (hG a ha) (hG0 a ha) (fun k => by simpa using hdec a ha k)
    refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [tsum_mul_left, ← hWA, hK2]
    have : Real.exp (-c * a) ^ (p / 2) = Real.exp (-c * a * p / 2) := by
      rw [← Real.exp_mul]; congr 1; ring
    rw [show A0 * Real.exp (-c * a) * WA = Real.exp (-c * a) * (A0 * WA) by ring,
      Real.mul_rpow (Real.exp_pos _).le (by positivity), this]
    ring
  have hsup' : ∫⁻ ω, (⨆ t ∈ Icc (0 : ℝ) T, ‖Y t ω - X a ω‖ₑ) ^ p ∂μ ≤
      ENNReal.ofReal (K1 * Real.exp (-c * a * p / 4)) := by
    refine hsup.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hK1, show C0 * Real.exp (-c * a * P / 4) * T ^ (1 + β) =
        Real.exp (-c * a * P / 4) * (C0 * T ^ (1 + β)) by ring,
      Real.mul_rpow (Real.exp_pos _).le (by positivity)]
    have : Real.exp (-c * a * P / 4) ^ (p / P) = Real.exp (-c * a * p / 4) := by
      rw [← Real.exp_mul]; congr 1; field_simp
    rw [this]; ring
  -- combination
  have hS : AEMeasurable (fun ω => (⨆ t ∈ Icc (0 : ℝ) T, ‖Y t ω - X a ω‖ₑ) ^ p) μ :=
    (HRS.Uniform.Q48d.aemeasurable_supIcc (f := fun t ζ => Y t ζ - X a ζ) hT.le
      (fun t _ => ((hYm t).sub (hXm a)).aestronglyMeasurable)
      (by filter_upwards [hYc] with ζ hζ using hζ.sub continuousOn_const)).pow_const _
  have hpt : ∀ ω, (⨆ t ∈ Icc (0 : ℝ) T, ‖X (a + t) ω‖ₑ) ^ p ≤
      ENNReal.ofReal (2 ^ (p - 1)) * ((⨆ t ∈ Icc (0 : ℝ) T, ‖Y t ω - X a ω‖ₑ) ^ p + ‖X a ω‖ₑ ^ p) := by
    intro ω
    have h1 : (⨆ t ∈ Icc (0 : ℝ) T, ‖X (a + t) ω‖ₑ) ≤
        (⨆ t ∈ Icc (0 : ℝ) T, ‖Y t ω - X a ω‖ₑ) + ‖X a ω‖ₑ := by
      refine iSup₂_le fun t ht => ?_
      calc ‖X (a + t) ω‖ₑ = ‖(Y t ω - X a ω) + X a ω‖ₑ := by simp [hY]
        _ ≤ ‖Y t ω - X a ω‖ₑ + ‖X a ω‖ₑ := enorm_add_le _ _
        _ ≤ _ := by
          gcongr
          exact le_iSup₂ (f := fun t (_ : t ∈ Icc (0 : ℝ) T) => ‖Y t ω - X a ω‖ₑ) t ht
    calc (⨆ t ∈ Icc (0 : ℝ) T, ‖X (a + t) ω‖ₑ) ^ p
        ≤ ((⨆ t ∈ Icc (0 : ℝ) T, ‖Y t ω - X a ω‖ₑ) + ‖X a ω‖ₑ) ^ p :=
          ENNReal.rpow_le_rpow h1 (by linarith)
      _ ≤ 2 ^ (p - 1) * ((⨆ t ∈ Icc (0 : ℝ) T, ‖Y t ω - X a ω‖ₑ) ^ p + ‖X a ω‖ₑ ^ p) :=
          ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by linarith)
      _ = _ := by
          have : ENNReal.ofReal (2 ^ (p - 1)) = 2 ^ (p - 1) := by
            rw [← ENNReal.ofReal_rpow_of_pos (by norm_num)]; simp
          rw [this]
  calc ∫⁻ ω, (⨆ t ∈ Icc (0 : ℝ) T, ‖X (a + t) ω‖ₑ) ^ p ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (2 ^ (p - 1)) *
        ((⨆ t ∈ Icc (0 : ℝ) T, ‖Y t ω - X a ω‖ₑ) ^ p + ‖X a ω‖ₑ ^ p) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal (2 ^ (p - 1)) * (∫⁻ ω, (⨆ t ∈ Icc (0 : ℝ) T, ‖Y t ω - X a ω‖ₑ) ^ p ∂μ +
          ∫⁻ ω, ‖X a ω‖ₑ ^ p ∂μ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hS]
    _ ≤ ENNReal.ofReal (2 ^ (p - 1)) * (ENNReal.ofReal (K1 * Real.exp (-c * a * p / 4)) +
          ENNReal.ofReal (K2 * Real.exp (-c * a * p / 2))) := by gcongr
    _ = ENNReal.ofReal (2 ^ (p - 1) * (K1 * Real.exp (-c * a * p / 4) + K2 * Real.exp (-c * a * p / 2))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ((Cf * Real.exp (-(c / 4) * a)) ^ p) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.mul_rpow (Real.rpow_nonneg hbase.le _) (Real.exp_pos _).le,
          ← Real.rpow_mul hbase.le, one_div_mul_cancel hp0.ne', Real.rpow_one, ← Real.exp_mul]
        have e1 : Real.exp (-c * a * p / 2) ≤ Real.exp (-c * a * p / 4) :=
          Real.exp_le_exp.2 (by nlinarith [mul_nonneg hc.le (mul_nonneg ha hp0.le)])
        have e2 : -(c / 4) * a * p = -c * a * p / 4 := by ring
        rw [e2]
        have : 2 ^ (p - 1) * (K1 * Real.exp (-c * a * p / 4) + K2 * Real.exp (-c * a * p / 2)) ≤
            2 ^ (p - 1) * ((K1 + K2) * Real.exp (-c * a * p / 4)) := by
          gcongr
          nlinarith [mul_le_mul_of_nonneg_left e1 hK2n]
        refine this.trans ?_
        nlinarith [Real.exp_pos (-c * a * p / 4)]



end HRS.MC.E214F

end
