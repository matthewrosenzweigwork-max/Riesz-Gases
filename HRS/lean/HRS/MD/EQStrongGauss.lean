import HRS.MD.EQStrongGaussMode
import HRS.MD.EQ29Vocab
import HRS.Stochastic.LyonsZhengSpec

/-!
# EQ-STRONG, Gaussian clause: `E sup_{t ∈ ratTimes 0 T} ‖Z^t‖²_{E_q} ≤ C`

Coordinatewise dyadic chaining (`chain_scalar`) for the Gaussian coordinates `⟨Z^t, e_k⟩`, then summation
over `k` with the weights `⟨k⟩^{-2q}`: `sup_t ∑_k ≤ ∑_k sup_t`.  The constant is uniform in `β ≥ β_m` and in the
thermal density.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MD.EQStrong

open HRS HRS.Q41 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear HRS.PDE.MFPair HRS.LZ HRS.MD.EQ29

variable {d : ℕ}

theorem eqstrong_jp_sq' (k : NonzeroLattice d) (q : ℝ) :
    Lattice.jp k.1 ^ (-2 * q) * Lattice.jp k.1 ^ 2 = Lattice.jp k.1 ^ (-(2 * (q - 1))) := by
  have hj : 0 < Lattice.jp k.1 := Torus.jp_pos _
  rw [← Real.rpow_natCast, ← Real.rpow_add hj]
  congr 1
  push_cast
  ring

theorem eqstrong_inc_const {x y Cc jp δ e : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (he : 0 ≤ e)
    (hjp : 0 ≤ jp) (hδ : 0 ≤ δ) :
    e * (2 * x * Cc ^ 2 * jp ^ 2 * δ) ^ 2 ≤ (e * (2 * y * Cc ^ 2) ^ 2 + 1) * jp ^ 4 * δ ^ 2 := by
  have h1 : (2 * x * Cc ^ 2) ^ 2 ≤ (2 * y * Cc ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by gcongr) 2
  calc e * (2 * x * Cc ^ 2 * jp ^ 2 * δ) ^ 2 = (e * (2 * x * Cc ^ 2) ^ 2) * (jp ^ 4 * δ ^ 2) := by
        ring
    _ ≤ (e * (2 * y * Cc ^ 2) ^ 2 + 1) * (jp ^ 4 * δ ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left h1 he]
    _ = _ := by ring

theorem eqstrong_gauss_clause (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm : ℝ) (hβm : 0 < βm) (m q : ℝ)
    (hq : (d : ℝ) / 2 + 1 < q) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (hβ : βm ≤ β) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' s β hs0 hsd (hβm.trans_le hβ) V ρβ m Z →
        ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, coordEnergy q (fun k => NegSobolev.fourierCoeff (Z t ω) k) ∂P' ≤
          ENNReal.ofReal C := by
  classical
  obtain ⟨Cc, hCc⟩ := Torus.cbNorm_realMode_le (d := d) 1
  obtain ⟨K, hK, hchain⟩ := chain_scalar
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hq1 : (d : ℝ) < 2 * q := by linarith
  have hq2 : (d : ℝ) < 2 * (q - 1) := by linarith
  have hS1 := summable_jp_rpow (d := d) q hq1
  have hS2 := summable_jp_rpow (d := d) (q - 1) hq2
  have hjp0 : ∀ (k : NonzeroLattice d) (e : ℝ), 0 ≤ Lattice.jp k.1 ^ e := fun k e =>
    Real.rpow_nonneg (Torus.jp_pos _).le _
  set S1 : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * q)) with hS1def
  set S2 : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (q - 1))) with hS2def
  have hS1nn : 0 ≤ S1 := tsum_nonneg fun k => hjp0 k _
  have hS2nn : 0 ≤ S2 := tsum_nonneg fun k => hjp0 k _
  set Bc : ℝ := 48 * Real.exp (1 / 2) * (2 * βm⁻¹ * Cc ^ 2) ^ 2 + 1 with hBcdef
  have hBc : 0 < Bc := by positivity
  have hsBc : 0 < Real.sqrt Bc := Real.sqrt_pos.2 hBc
  refine ⟨16 * S1 + K * Real.sqrt Bc * T * S2 + 1, by positivity, ?_⟩
  intro β hβ ρβ hρ Ω' _ P' _ Z hZ
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ
  obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ0 hV hρ
  obtain ⟨c₀, Λ₀, H⟩ := frozenHyp_of_smooth s hs0 hsd β hβ0 V hV ρβ hρ hsm hpos
    (2 * mStar d + 4)
  have hβinv : β⁻¹ ≤ βm⁻¹ := inv_anti₀ hβm hβ
  -- the coordinate bound
  have hmode : ∀ k : NonzeroLattice d,
      ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * q) *
          NegSobolev.fourierCoeff (Z t ω) k ^ 2) ∂P' ≤
        ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * q) *
          (16 + K * Real.sqrt Bc * T * Lattice.jp k.1 ^ 2)) := by
    intro k
    have hjp : 0 < Lattice.jp k.1 := Torus.jp_pos _
    have hcoef : Continuous (fun F : NegSobolev d m => NegSobolev.fourierCoeff F k) := by
      unfold NegSobolev.fourierCoeff
      exact continuous_const.mul (q38b_continuous_coord k)
    set g : ℝ → Ω' → ℝ := fun t ω => NegSobolev.fourierCoeff (Z t ω) k with hg
    have hgm : ∀ t, Measurable (g t) := fun t => hcoef.measurable.comp (hZ.meas t)
    set Bk : ℝ := Bc * Lattice.jp k.1 ^ 4 with hBk
    have hBk0 : 0 < Bk := by positivity
    have hinc : ∀ s' t', s' ∈ Set.Icc 0 T → t' ∈ Set.Icc 0 T →
        ∫⁻ ω, ENNReal.ofReal ((g t' ω - g s' ω) ^ 4) ∂P' ≤
          ENNReal.ofReal (Bk * (t' - s') ^ 2) := by
      intro s' t' hs' ht'
      have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
          ∫⁻ ω, ENNReal.ofReal ((g b ω - g a ω) ^ 4) ∂P' ≤
            ENNReal.ofReal (Bk * (b - a) ^ 2) := by
        intro a b ha hab
        refine (eqstrong_inc4 hd hs0 hsd hβ0 hV hρ H hZ hCc k ha hab).trans
          (ENNReal.ofReal_le_ofReal ?_)
        have := eqstrong_inc_const (x := β⁻¹) (y := βm⁻¹) (Cc := Cc) (jp := Lattice.jp k.1)
          (δ := b - a) (e := 48 * Real.exp (1 / 2)) (inv_nonneg.2 hβ0.le) hβinv (by positivity)
          hjp.le (by linarith)
        calc _ ≤ _ := this
          _ = _ := by rw [hBk, hBcdef]
      rcases le_total s' t' with h | h
      · exact key s' t' hs'.1 h
      · have := key t' s' ht'.1 h
        have e1 : ∀ ω, (g t' ω - g s' ω) ^ 4 = (g s' ω - g t' ω) ^ 4 := fun ω => by ring
        simp_rw [e1]
        rw [show (t' - s') ^ 2 = (s' - t') ^ 2 by ring]
        exact this
    have hcont : ∀ᵐ ω ∂P', ContinuousOn (fun t => g t ω) (Set.Icc 0 T) := by
      filter_upwards [hZ.cont] with ω hω
      exact (hcoef.comp_continuousOn hω).mono Set.Icc_subset_Ici_self
    have hU : ratTimes 0 T ⊆ Set.Icc 0 T := fun t ht => by simpa using ht.1
    have hch := hchain P' g hgm hT hBk0 hinc hcont (ratTimes 0 T) hU
    have h0 := eqstrong_zero_moment hd hs0 hsd hβ0 hV hρ hZ k
    have hsqrt : Real.sqrt Bk = Real.sqrt Bc * Lattice.jp k.1 ^ 2 := by
      rw [hBk, Real.sqrt_mul hBc.le, show Lattice.jp k.1 ^ 4 = (Lattice.jp k.1 ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    have hw0 : 0 ≤ Lattice.jp k.1 ^ (-2 * q) := hjp0 k _
    have hpt : ∀ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * q) *
          NegSobolev.fourierCoeff (Z t ω) k ^ 2) =
        ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * q)) *
          ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal (g t ω ^ 2) := by
      intro ω
      simp only [ENNReal.mul_iSup]
      refine iSup_congr fun t => iSup_congr fun ht => ?_
      rw [ENNReal.ofReal_mul hw0]
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * q)) *
          ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal (g t ω ^ 2) ∂P'
        ≤ ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * q)) *
            ENNReal.ofReal (16 + K * Real.sqrt Bc * T * Lattice.jp k.1 ^ 2) := by
          gcongr
          calc ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal (g t ω ^ 2) ∂P'
              ≤ 2 * ∫⁻ ω, ENNReal.ofReal (g 0 ω ^ 2) ∂P' +
                  ENNReal.ofReal (K * Real.sqrt Bk * T) := hch
            _ ≤ 2 * ENNReal.ofReal 8 +
                  ENNReal.ofReal (K * Real.sqrt Bc * T * Lattice.jp k.1 ^ 2) := by
                refine add_le_add (by gcongr) (le_of_eq ?_)
                rw [hsqrt]
                congr 1
                ring
            _ = ENNReal.ofReal (16 + K * Real.sqrt Bc * T * Lattice.jp k.1 ^ 2) := by
                rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
                  ← ENNReal.ofReal_add (by norm_num) (by positivity)]
                congr 1
                norm_num
      _ = _ := by rw [← ENNReal.ofReal_mul hw0]
  -- assemble
  have hcount : (ratTimes 0 T).Countable :=
    (Set.countable_range ((↑) : ℚ → ℝ)).mono fun t ht => by
      obtain ⟨q', hq'⟩ := ht.2
      exact ⟨q', hq'⟩
  have hmeas : ∀ k : NonzeroLattice d, Measurable fun ω => ⨆ t ∈ ratTimes 0 T,
      ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * q) * NegSobolev.fourierCoeff (Z t ω) k ^ 2) := by
    intro k
    have hcoef : Continuous (fun F : NegSobolev d m => NegSobolev.fourierCoeff F k) := by
      unfold NegSobolev.fourierCoeff
      exact continuous_const.mul (q38b_continuous_coord k)
    refine Measurable.biSup _ hcount fun t _ => ?_
    exact ((((hcoef.measurable.comp (hZ.meas t)).pow_const 2).const_mul _)).ennreal_ofReal
  have hsum : ∀ ω, ⨆ t ∈ ratTimes 0 T, coordEnergy q (fun k => NegSobolev.fourierCoeff (Z t ω) k) ≤
      ∑' k : NonzeroLattice d, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * q) *
        NegSobolev.fourierCoeff (Z t ω) k ^ 2) := by
    intro ω
    refine iSup₂_le fun t ht => ?_
    unfold coordEnergy
    exact ENNReal.tsum_le_tsum fun k => le_iSup₂ (f := fun t (_ : t ∈ ratTimes 0 T) =>
      ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * q) * NegSobolev.fourierCoeff (Z t ω) k ^ 2)) t ht
  have e1 : ∀ k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * q) = Lattice.jp k.1 ^ (-(2 * q)) := by
    intro k; rw [neg_mul]
  have hterm : ∀ k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * q) *
      (16 + K * Real.sqrt Bc * T * Lattice.jp k.1 ^ 2) =
      16 * Lattice.jp k.1 ^ (-(2 * q)) +
        K * Real.sqrt Bc * T * Lattice.jp k.1 ^ (-(2 * (q - 1))) := by
    intro k
    rw [← eqstrong_jp_sq' k q, e1 k]
    ring
  have hsumm : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-2 * q) *
      (16 + K * Real.sqrt Bc * T * Lattice.jp k.1 ^ 2) := by
    simp_rw [hterm]
    exact (hS1.mul_left 16).add (hS2.mul_left _)
  calc ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, coordEnergy q (fun k => NegSobolev.fourierCoeff (Z t ω) k) ∂P'
      ≤ ∫⁻ ω, ∑' k : NonzeroLattice d, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
          (Lattice.jp k.1 ^ (-2 * q) * NegSobolev.fourierCoeff (Z t ω) k ^ 2) ∂P' :=
        lintegral_mono hsum
    _ = ∑' k : NonzeroLattice d, ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
          (Lattice.jp k.1 ^ (-2 * q) * NegSobolev.fourierCoeff (Z t ω) k ^ 2) ∂P' :=
        lintegral_tsum fun k => (hmeas k).aemeasurable
    _ ≤ ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * q) *
          (16 + K * Real.sqrt Bc * T * Lattice.jp k.1 ^ 2)) := ENNReal.tsum_le_tsum hmode
    _ = ENNReal.ofReal (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * q) *
          (16 + K * Real.sqrt Bc * T * Lattice.jp k.1 ^ 2)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (hjp0 k _) (by positivity)) hsumm).symm
    _ ≤ ENNReal.ofReal (16 * S1 + K * Real.sqrt Bc * T * S2 + 1) := by
        apply ENNReal.ofReal_le_ofReal
        simp_rw [hterm]
        rw [Summable.tsum_add (hS1.mul_left 16) (hS2.mul_left _), tsum_mul_left, tsum_mul_left]
        linarith

end HRS.MD.EQStrong
