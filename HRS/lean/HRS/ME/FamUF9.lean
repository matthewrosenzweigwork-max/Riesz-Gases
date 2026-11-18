import HRS.ME.FamUF9A
import HRS.ME.CritUnifDefs

/-!
# Chunk E, packet F9b/F9c (namespace `HRS.ME.FamU`): V-uniform decay of the Fourier coefficients and `UnifDecay`

Originals (copied with the convention of `docs/MAIN_E_FAMU_PLAN.md`; `Bf : ℕ → ℝ` is fixed data, `V` is a bound variable):
* `HRS.ME.Crit.fourier_decay_unif` (`HRS/ME/CritUnifDecay.lean:35`) becomes `fourier_decay_unifV`. The fixed data are
  `d hd s hs0 hsd βm βp hβm hββ p Bf`; the constants `C, c` are chosen before `V`, `β`, `ρβ`.
  The frozen data come from `HRS.ME.EVU.eqevo_thermal_unifV` with `Bv := Bf (K+2)` (level `J + mStar d`, `K` as in the
  original), the generator constant from `equilibriumGen_sobolev_unifV` (F9a) with the same `Bf`.
  The remaining constants `C0, c0` and `CJ, cJ` are those of `exists_frozen_l2_decay` and `exists_frozen_hj_decay'`,
  which depend only on `c₀, Λ₀`.
* New family definition `UnifDecayFam d hs0 hsd βm βp hβm Bf` (body of `HRS.ME.Crit.UnifDecay`,
  `HRS/ME/CritUnifDefs.lean:34`, verbatim with `∀ V, IsSmooth V → (∀ j, cbNorm j V ≤ Bf j) → …`), with
  `UnifDecayFam.specialize`, and `unif_decayV` (the statement at `p = 9 d + 82`, `s = d/2`, from `fourier_decay_unifV`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.FamU

open HRS

variable {d : ℕ}

/-- **F9b (V-uniform copy of `fourier_decay_unif`).** The constants `C, c` are chosen before `V`, `β`, `ρβ`. -/
theorem fourier_decay_unifV (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (p : ℕ) (Bf : ℕ → ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ V : Torus d → ℝ, Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
      ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
      ∀ (m : ℝ) (j : NonzeroLattice d) (v : ℝ), 0 ≤ v →
        Summable (fun l : NonzeroLattice d => Lattice.jp l.1 ^ p *
          (|Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
              (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l| +
            |Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹
              (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
                (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x))) l|)) ∧
        ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ p *
          (|Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
              (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l| +
            |Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹
              (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
                (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x))) l|) ≤
          C * Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ)) * Real.exp (-c * v) := by
  have hd1 : 1 ≤ d := by omega
  -- indices: `n = p + ⌊d/2⌋ + 1`, `N = n + 2`, `J = 2N`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = p + d / 2 + 1 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = n + 2 := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = 2 * N := ⟨_, rfl⟩
  have hdn : (d : ℝ) < 2 * ((d / 2 : ℕ) : ℝ) + 2 := by
    have : d < 2 * (d / 2) + 2 := by omega
    exact_mod_cast this
  have hnR : (n : ℝ) = p + ((d / 2 : ℕ) : ℝ) + 1 := by rw [hn]; push_cast; ring
  have hNR : (N : ℝ) = n + 2 := by rw [hN]; push_cast; ring
  have hJR : (J : ℝ) = 2 * N := by rw [hJ]; push_cast; ring
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hq0 : (0 : ℝ) ≤ ((d / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hdn0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hnlt : (d : ℝ) / 2 + p < n := by rw [hnR]; linarith
  have hNlt : (d : ℝ) / 2 + p < N := by rw [hNR]; linarith
  have hJlt : (d : ℝ) / 2 + 4 < J := by rw [hJR, hNR, hnR]; linarith
  have hN1 : N + 1 ≤ p + d + 3 := by omega
  -- uniform frozen data at the top level `J + mStar d`, and the index bound for the Sobolev norm of `ρβ`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 2 * (J + PDE.mStar d) + 6 * d + 30 := ⟨_, rfl⟩
  obtain ⟨Λ₀, c₀, lam, Lam, B, hc₀, hlam, hB0, hU⟩ :=
    HRS.ME.EVU.eqevo_thermal_unifV hd s βm βp hs0 hsd hβm hββ (Bf (K + 2)) (J + PDE.mStar d) K (by omega)
  have hK2 : (K : ℝ) = 2 * ((J + PDE.mStar d : ℕ) : ℝ) + 6 * (d : ℝ) + 30 := by
    rw [hK]; push_cast; ring
  have hKidx : (d : ℝ) / 2 + ((n : ℝ) + 2) + 1 ≤ (K : ℝ) := by
    have hm0 : (0 : ℝ) ≤ (PDE.mStar d : ℝ) := Nat.cast_nonneg _
    have hJm : ((J + PDE.mStar d : ℕ) : ℝ) = (J : ℝ) + (PDE.mStar d : ℝ) := by push_cast; ring
    rw [hK2, hJm]
    linarith
  -- the constants of the frozen decay lemmas, with `νm = βp⁻¹`, `νp = βm⁻¹` and the uniform `c₀, Λ₀`
  obtain ⟨C0, c0, hC0, hc0, hL2⟩ :=
    PDE.MFAdjoint.exists_frozen_l2_decay hd1 s βp⁻¹ βm⁻¹ c₀ Λ₀
  obtain ⟨CJ, cJ, hCJ, hcJ, hJdec⟩ :=
    PDE.MFAdjoint.exists_frozen_hj_decay' hd1 s J hJlt βp⁻¹ βm⁻¹ c₀ Λ₀
  -- the uniform generator bound (`Lam` is replaced by `max Lam 0` to get a nonnegative bound)
  obtain ⟨Cg, hCg, hgen⟩ := equilibriumGen_sobolev_unifV hd1 s hs0 hsd n (max Lam 0) (Real.sqrt B) (βm⁻¹)
    (le_max_right _ _) (Real.sqrt_nonneg _) (inv_nonneg.2 hβm.le) Bf
  obtain ⟨Kn, hKn, hcoefn⟩ := fb_coeff_exists p n hnlt
  obtain ⟨KN, hKN, hcoefN⟩ := fb_coeff_exists p N hNlt
  -- the constants of the final bound
  set KQ : ℝ := Real.sqrt (C0 * CJ) * (Real.sqrt 2 + 1) with hKQ
  have hKQ0 : 0 ≤ KQ := mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hKN' : 0 ≤ KN + Kn * Cg := add_nonneg hKN (mul_nonneg hKn hCg)
  refine ⟨(KN + Kn * Cg) * KQ + 1, (c0 + cJ) / 2, by nlinarith [mul_nonneg hKN' hKQ0],
    by positivity, ?_⟩
  intro V hV hbV β hβ ρβ hρβ hρS hpos m j v hv
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  -- the uniform frozen data of this `V` at the level `J + mStar d`
  have hUV := hU V hV (hbV (K + 2))
  have H₂ := (hUV β hβ ρβ hρβ).1
  -- the uniform frozen data at the level `mStar d + 5` (from the level `J + mStar d` by monotonicity)
  have H₁ := PDE.MFAdjoint.FrozenHyp.mono (by omega : PDE.mStar d + 5 ≤ J + PDE.mStar d) H₂
  have hMρ : ∀ x, ρβ x ≤ max Lam 0 := fun x => ((hUV β hβ ρβ hρβ).2.1 x).2.trans (le_max_left _ _)
  have hHρ : PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) ≤ Real.sqrt B := by
    have hMem : PDE.MemHs (K : ℝ) (PDE.coeffOf ρβ) := PDE.MFSemigroup.memHs_of_isSmooth hρS _
    have hmono := (fourierTailA_hs_mono (c := PDE.coeffOf ρβ) hKidx hMem).2
    have hsq : PDE.hsNorm (K : ℝ) (PDE.coeffOf ρβ) ≤ Real.sqrt B :=
      Real.sqrt_le_sqrt ((hUV β hβ ρβ hρβ).2.2)
    exact hmono.trans hsq
  have hβi : |β⁻¹| ≤ βm⁻¹ := by
    rw [abs_of_pos (inv_pos.2 hβ0)]
    exact inv_anti₀ hβm hβ.1
  have hgenβ := hgen V hV hbV β hβ0 ρβ hρβ hρS hpos hMρ hHρ hβi
  have hprob : IsProbDensity ρβ := hρβ.1
  have hρc : Continuous ρβ :=
    Torus.continuous_of_continuous_lift (φ := ρβ) (PDE.MFPair.isCk_of_smooth_ps hρS 0).continuous
  have hjp1 : ∀ k : Lattice d, 1 ≤ Lattice.jp k := fun k => by
    unfold Lattice.jp
    have : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  set cj : ℝ := Lattice.jp j.1 ^ (-m) with hcj
  have hcj0 : 0 ≤ cj := Real.rpow_nonneg (Torus.jp_pos _).le _
  set φ : Torus d → ℝ := fun x => cj * Torus.realMode j x with hφ
  have hφs : Torus.IsSmooth φ := fb_mode_smooth cj j
  have hφc : Continuous φ := (fb_memSob_of_smooth hφs 0).1
  set g : Torus d → ℝ := PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ0) ρβ v φ with hg
  have hgs : Torus.IsSmooth g := fb_S_smooth hd1 s hs0 hsd β hβ0 V hV ρβ hρβ hρS hpos φ hφs v hv
  have hgc : Continuous g := (fb_memSob_of_smooth hgs 0).1
  have hg0 : MemSobolev 0 g := by simpa using (fb_memSob_of_smooth hgs 0).2
  have hgN : MemSobolev (N : ℝ) g := (fb_memSob_of_smooth hgs N).2
  have hgJ : MemSobolev (J : ℝ) g := (fb_memSob_of_smooth hgs J).2
  have hgJ2 : MemSobolev (2 * (N : ℝ)) g := by rw [← hJR]; exact hgJ
  -- decay of the H^0 and H^J norms of `g = U_v φ`
  have hmemPsi : MemSobolev ((PDE.mStar d : ℝ) + 2) φ := fb_memSobolev_mode _ _ j
  have hA0 : sobolevNorm 0 g ≤ C0 * Real.exp (-c0 * v) *
      sobolevNorm 2 (projMean (withDensityReal ρβ) φ) :=
    hL2 β V ρβ H₁ φ hφc hmemPsi v hv
  have hAJ0 : sobolevNorm (J : ℝ) g ≤ CJ * Real.exp (-cJ * v) *
      sobolevNorm (J : ℝ) (projMean (withDensityReal ρβ) φ) :=
    (hJdec β V ρβ H₂ φ hφc (fb_memSobolev_mode _ _ j) v hv).2
  have hP2 : sobolevNorm 2 (projMean (withDensityReal ρβ) φ) ≤
      cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ)) :=
    fb_projMean_mode ρβ hprob hρc 2 cj hcj0 j
  have hPJ : sobolevNorm (J : ℝ) (projMean (withDensityReal ρβ) φ) ≤
      cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ)) :=
    fb_projMean_mode ρβ hprob hρc (J : ℝ) cj hcj0 j
  have hE0 : 0 ≤ C0 * Real.exp (-c0 * v) := mul_nonneg hC0.le (Real.exp_pos _).le
  have hEJ : 0 ≤ CJ * Real.exp (-cJ * v) := mul_nonneg hCJ.le (Real.exp_pos _).le
  have hA0' : sobolevNorm 0 g ≤ (C0 * Real.exp (-c0 * v)) * (cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ))) :=
    hA0.trans (mul_le_mul_of_nonneg_left hP2 hE0)
  have hAJ' : sobolevNorm (J : ℝ) g ≤ (CJ * Real.exp (-cJ * v)) * (cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ))) :=
    hAJ0.trans (mul_le_mul_of_nonneg_left hPJ hEJ)
  -- midpoint interpolation `‖g‖_N² ≤ ‖g‖_0 ‖g‖_{2N}`
  have hI := fb_interp (N : ℝ) (Nat.cast_nonneg N) hg0 hgJ2
  rw [← hJR] at hI
  have hX0 : 0 ≤ sobolevNorm (N : ℝ) g := Real.sqrt_nonneg _
  have hA0nn : 0 ≤ sobolevNorm 0 g := Real.sqrt_nonneg _
  have hAJnn : 0 ≤ sobolevNorm (J : ℝ) g := Real.sqrt_nonneg _
  have ha1 : 1 ≤ Lattice.jp j.1 ^ (2 : ℝ) := Real.one_le_rpow (hjp1 j.1) (by norm_num)
  have hb1 : 1 ≤ Lattice.jp j.1 ^ (J : ℝ) := Real.one_le_rpow (hjp1 j.1) (by positivity)
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  -- the squared bound
  have hP0nn : 0 ≤ (C0 * Real.exp (-c0 * v)) * (cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ))) :=
    mul_nonneg hE0 (mul_nonneg hcj0 (add_nonneg hs2 (Real.rpow_nonneg (Torus.jp_pos _).le _)))
  have hPJnn : 0 ≤ (CJ * Real.exp (-cJ * v)) * (cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ))) :=
    mul_nonneg hEJ (mul_nonneg hcj0 (add_nonneg hs2 (Real.rpow_nonneg (Torus.jp_pos _).le _)))
  have hprod := mul_le_mul hA0' hAJ' hAJnn hP0nn
  have hsqa : Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ) ≤ (Real.sqrt 2 + 1) * Lattice.jp j.1 ^ (2 : ℝ) := by
    have e : (Real.sqrt 2 + 1) * Lattice.jp j.1 ^ (2 : ℝ) - (Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ)) =
        Real.sqrt 2 * (Lattice.jp j.1 ^ (2 : ℝ) - 1) := by ring
    linarith [mul_nonneg hs2 (sub_nonneg.mpr ha1)]
  have hsqb : Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ) ≤ (Real.sqrt 2 + 1) * Lattice.jp j.1 ^ (J : ℝ) := by
    have e : (Real.sqrt 2 + 1) * Lattice.jp j.1 ^ (J : ℝ) - (Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ)) =
        Real.sqrt 2 * (Lattice.jp j.1 ^ (J : ℝ) - 1) := by ring
    linarith [mul_nonneg hs2 (sub_nonneg.mpr hb1)]
  have hBound : (C0 * Real.exp (-c0 * v)) * (cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ))) *
      ((CJ * Real.exp (-cJ * v)) * (cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ)))) ≤
      C0 * CJ * (Real.sqrt 2 + 1) ^ 2 * (Real.exp (-c0 * v) * Real.exp (-cJ * v)) * cj ^ 2 *
        (Lattice.jp j.1 ^ (2 : ℝ) * Lattice.jp j.1 ^ (J : ℝ)) := by
    have hm1 : (Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ)) * (Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ)) ≤
        (Real.sqrt 2 + 1) ^ 2 * (Lattice.jp j.1 ^ (2 : ℝ) * Lattice.jp j.1 ^ (J : ℝ)) := by
      have h1 := mul_le_mul hsqa hsqb (add_nonneg hs2 (Real.rpow_nonneg (Torus.jp_pos _).le _))
        (mul_nonneg (add_nonneg hs2 zero_le_one) (Real.rpow_nonneg (Torus.jp_pos _).le _))
      calc _ ≤ _ := h1
        _ = _ := by ring
    have hpos0 : 0 ≤ (C0 * Real.exp (-c0 * v)) * (CJ * Real.exp (-cJ * v)) * cj ^ 2 :=
      mul_nonneg (mul_nonneg hE0 hEJ) (sq_nonneg _)
    have e : (C0 * Real.exp (-c0 * v)) * (cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ))) *
        ((CJ * Real.exp (-cJ * v)) * (cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ)))) =
        (C0 * Real.exp (-c0 * v)) * (CJ * Real.exp (-cJ * v)) * cj ^ 2 *
          ((Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ)) * (Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ))) := by ring
    rw [e]
    have e2 : C0 * CJ * (Real.sqrt 2 + 1) ^ 2 * (Real.exp (-c0 * v) * Real.exp (-cJ * v)) * cj ^ 2 *
        (Lattice.jp j.1 ^ (2 : ℝ) * Lattice.jp j.1 ^ (J : ℝ)) =
        (C0 * Real.exp (-c0 * v)) * (CJ * Real.exp (-cJ * v)) * cj ^ 2 *
          ((Real.sqrt 2 + 1) ^ 2 * (Lattice.jp j.1 ^ (2 : ℝ) * Lattice.jp j.1 ^ (J : ℝ))) := by ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left hm1 hpos0
  -- the target bound `Q`
  set cQ : ℝ := (c0 + cJ) / 2 with hcQ
  set Q : ℝ := KQ * Real.exp (-cQ * v) * cj * Lattice.jp j.1 ^ ((N : ℝ) + 1) with hQdef
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg hKQ0 (Real.exp_pos _).le) hcj0)
      (Real.rpow_nonneg (Torus.jp_pos _).le _)
  have hQ2 : Q ^ 2 = C0 * CJ * (Real.sqrt 2 + 1) ^ 2 * (Real.exp (-c0 * v) * Real.exp (-cJ * v)) * cj ^ 2 *
      (Lattice.jp j.1 ^ (2 : ℝ) * Lattice.jp j.1 ^ (J : ℝ)) := by
    have hK2' : KQ ^ 2 = C0 * CJ * (Real.sqrt 2 + 1) ^ 2 := by
      rw [hKQ, mul_pow, Real.sq_sqrt (mul_nonneg hC0.le hCJ.le)]
    have hE : Real.exp (-cQ * v) ^ 2 = Real.exp (-c0 * v) * Real.exp (-cJ * v) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; rw [hcQ]; ring
    have hJp : (Lattice.jp j.1 ^ ((N : ℝ) + 1)) ^ 2 = Lattice.jp j.1 ^ (2 : ℝ) * Lattice.jp j.1 ^ (J : ℝ) := by
      rw [Torus.jp_rpow_sq, show 2 * ((N : ℝ) + 1) = 2 + (J : ℝ) by rw [hJR]; ring,
        Real.rpow_add (Torus.jp_pos _)]
    rw [hQdef, mul_pow, mul_pow, mul_pow, hK2', hE, hJp]
  have hX2Q : sobolevNorm (N : ℝ) g ≤ Q := by
    calc sobolevNorm (N : ℝ) g = Real.sqrt (sobolevNorm (N : ℝ) g ^ 2) := (Real.sqrt_sq hX0).symm
      _ ≤ Real.sqrt (Q ^ 2) := Real.sqrt_le_sqrt (by rw [hQ2]; exact hI.trans (hprod.trans hBound))
      _ = Q := Real.sqrt_sq hQ0
  -- coefficient sums of `g` and of `A g`
  have hAg := fb_gen_memSobolev hd1 s hs0 hsd β hβ0 V hV ρβ hρβ hρS hpos n g hgs
  have hgI : Integrable g := hgc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hAgI : Integrable (PDE.equilibriumGen d s ρβ β⁻¹ g) := hAg.1.integrable one_le_two
  obtain ⟨s1, t1⟩ := hcoefN g hgI hgN
  obtain ⟨s2, t2⟩ := hcoefn (PDE.equilibriumGen d s ρβ β⁻¹ g) hAgI hAg
  have hgen' : sobolevNorm (n : ℝ) (PDE.equilibriumGen d s ρβ β⁻¹ g) ≤ Cg * sobolevNorm (N : ℝ) g := by
    rw [hNR]; exact hgenβ g hgs
  have hsplit : ∀ l : NonzeroLattice d,
      Lattice.jp l.1 ^ p * (|Torus.funRealCoeff g l| +
          |Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹ g) l|) =
        Lattice.jp l.1 ^ p * |Torus.funRealCoeff g l| +
          Lattice.jp l.1 ^ p * |Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹ g) l| :=
    fun l => mul_add _ _ _
  simp only [hsplit]
  refine ⟨s1.add s2, ?_⟩
  rw [s1.tsum_add s2]
  have hTn : 0 ≤ Real.exp (-cQ * v) * Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ)) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (Torus.jp_pos _).le _)
  have hcjN : cj * Lattice.jp j.1 ^ ((N : ℝ) + 1) ≤ Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ)) := by
    rw [hcj, ← Real.rpow_add (Torus.jp_pos _)]
    have hN1R : (N : ℝ) + 1 ≤ ((p + d + 3 : ℕ) : ℝ) := by exact_mod_cast hN1
    exact Real.rpow_le_rpow_of_exponent_le (hjp1 j.1) (by linarith)
  have hQle : Q ≤ KQ * (Real.exp (-cQ * v) * Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ))) := by
    rw [hQdef]
    calc KQ * Real.exp (-cQ * v) * cj * Lattice.jp j.1 ^ ((N : ℝ) + 1)
        = KQ * Real.exp (-cQ * v) * (cj * Lattice.jp j.1 ^ ((N : ℝ) + 1)) := by ring
      _ ≤ KQ * Real.exp (-cQ * v) * Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hcjN (mul_nonneg hKQ0 (Real.exp_pos _).le)
      _ = _ := by ring
  have hfin : (KN + Kn * Cg) * Q ≤
      ((KN + Kn * Cg) * KQ + 1) * (Real.exp (-cQ * v) * Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ))) := by
    calc (KN + Kn * Cg) * Q ≤ (KN + Kn * Cg) * (KQ * (Real.exp (-cQ * v) *
          Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ)))) := mul_le_mul_of_nonneg_left hQle hKN'
      _ = ((KN + Kn * Cg) * KQ) * (Real.exp (-cQ * v) * Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ))) := by
          ring
      _ ≤ ((KN + Kn * Cg) * KQ + 1) * (Real.exp (-cQ * v) *
          Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (by linarith [mul_nonneg hKN' hKQ0]) hTn
  have hsumX : KN * sobolevNorm (N : ℝ) g + Kn * sobolevNorm (n : ℝ) (PDE.equilibriumGen d s ρβ β⁻¹ g) ≤
      (KN + Kn * Cg) * sobolevNorm (N : ℝ) g := by
    have h3 : Kn * sobolevNorm (n : ℝ) (PDE.equilibriumGen d s ρβ β⁻¹ g) ≤ Kn * (Cg * sobolevNorm (N : ℝ) g) :=
      mul_le_mul_of_nonneg_left hgen' hKn
    have h4 : (KN + Kn * Cg) * sobolevNorm (N : ℝ) g = KN * sobolevNorm (N : ℝ) g +
        Kn * (Cg * sobolevNorm (N : ℝ) g) := by ring
    linarith
  calc _ ≤ KN * sobolevNorm (N : ℝ) g + Kn * sobolevNorm (n : ℝ) (PDE.equilibriumGen d s ρβ β⁻¹ g) :=
        add_le_add t1 t2
    _ ≤ (KN + Kn * Cg) * sobolevNorm (N : ℝ) g := hsumX
    _ ≤ (KN + Kn * Cg) * Q := mul_le_mul_of_nonneg_left hX2Q hKN'
    _ ≤ ((KN + Kn * Cg) * KQ + 1) * (Real.exp (-cQ * v) *
          Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ))) := hfin
    _ = ((KN + Kn * Cg) * KQ + 1) * Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ)) *
          Real.exp (-cQ * v) := by ring

/-- **F9c.** The family version of `HRS.ME.Crit.UnifDecay` (`HRS/ME/CritUnifDefs.lean:34`): the body is the
original with `∀ V, IsSmooth V → (∀ j, cbNorm j V ≤ Bf j) → …` in front; `C, c` are chosen before `V`. -/
def UnifDecayFam (d : ℕ) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (βm βp : ℝ) (hβm : 0 < βm)
    (Bf : ℕ → ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ V : Torus d → ℝ, Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
    ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
    IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
    ∀ (m : ℝ) (j : NonzeroLattice d) (v : ℝ), 0 ≤ v →
      Summable (fun l : NonzeroLattice d => Lattice.jp l.1 ^ (9 * d + 82) *
        (|Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
            (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l| +
          |Torus.funRealCoeff (PDE.equilibriumGen d ((d : ℝ) / 2) ρβ β⁻¹
            (PDE.equilibriumSemigroup (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
              (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x))) l|)) ∧
      ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (9 * d + 82) *
        (|Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
            (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l| +
          |Torus.funRealCoeff (PDE.equilibriumGen d ((d : ℝ) / 2) ρβ β⁻¹
            (PDE.equilibriumSemigroup (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) ρβ v
              (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x))) l|) ≤
        C * Lattice.jp j.1 ^ (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ)) * Real.exp (-c * v)

/-- **F9c (`UnifDecayFam` specialized).** A family and one smooth `V` with `cbNorm j V ≤ Bf j` give the fixed-`V`
`HRS.ME.Crit.UnifDecay`. -/
theorem UnifDecayFam.specialize {d : ℕ} {hs0 : 0 ≤ (d : ℝ) / 2} {hsd : (d : ℝ) / 2 < d} {βm βp : ℝ}
    {hβm : 0 < βm} {Bf : ℕ → ℝ} (h : UnifDecayFam d hs0 hsd βm βp hβm Bf) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) (hb : ∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) :
    HRS.ME.Crit.UnifDecay d hs0 hsd V βm βp hβm := by
  obtain ⟨C, c, hC, hc, h⟩ := h
  exact ⟨C, c, hC, hc, fun β hβ ρβ hρβ hρS hpos => h V hV hb β hβ ρβ hρβ hρS hpos⟩

/-- **F9c (`unif_decay` family).** `UnifDecayFam` at `p = 9 d + 82`, `s = d/2`, from `fourier_decay_unifV`. -/
theorem unif_decayV (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (βm βp : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (Bf : ℕ → ℝ) :
    UnifDecayFam d hs0 hsd βm βp hβm Bf :=
  fourier_decay_unifV hd ((d : ℝ) / 2) hs0 hsd βm βp hβm hββ (9 * d + 82) Bf

end HRS.ME.FamU
