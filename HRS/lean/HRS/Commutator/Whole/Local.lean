import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.LocalAuxFC
import HRS.Commutator.Whole.LocalAuxFC2
import HRS.Commutator.Whole.LocalAuxKR3
import HRS.Commutator.Whole.LocalAuxSAMP18
import HRS.Commutator.Whole.Positive
import HRS.Commutator.Whole.LocalAuxSAMP2Bessel
import HRS.Commutator.Whole.LocalAuxSAMP2Fin

/-!
# Sub-Coulomb commutator on `ℝ^d`: Fourier truncation and local supremum estimates (Section 3)

Source `[N]`: Section 3 (L376-512).  Lemma 3.1 `lem:kernelremainder` (L409-424), Lemma 3.2
`lem:sampling` (L429-499), the fractional Leibniz consequence `(3.product)` (L501-512).
Packets `CMX-FC` (cutoff facts), `CMX-KR` (Lemma 3.1), `CMX-SAMP` (Lemma 3.2), `CMX-PROD` (3.product).

Standing assumptions `d ≥ 3`, `0 ≤ s < d-2`; exponents `α = (d-s)/2`, `p₁ = 2d/(d-s-2)`,
`p₂ = 2d/(s+2)` (`alphaE`, `p1E`, `p2E`; relations `(1.relations)` L170-174).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- The transport data used in Lemma 3.2: `v` is `L`-Lipschitz and `w` represents `|∇|^α v`
componentwise (`IsFracDerivRep`) with `‖|w|‖_{L^{p₁}} ≤ F`.  (`HasFracTransportBound` is the
existential packaging: `∃ L F w, HasFracData … ∧ L + F ≤ K`.) -/
structure HasFracData (d : ℕ) (s : ℝ) (v : Euc d → Euc d) (L : ℝ≥0) (w : Euc d → Euc d) (F : ℝ) :
    Prop where
  lip : LipschitzWith L v
  rep : ∀ i, IsFracDerivRep (alphaE d s) (fun x => v x i) (fun x => w x i)
  norm : eLpNorm (fun x => ‖w x‖) (ENNReal.ofReal (p1E d s)) volume ≤ ENNReal.ofReal F

/-! ### The Fourier cutoff: kernel facts (`[N] L379-393`) -/

/-- `[N] L393`: `ψ = 𝓕⁻χ` is a real, even Schwartz function with `∫ ψ = χ(0) = 1`, and
`ψ_L(x) = L^d ψ(Lx)`; `χ` has the properties of `[N] L379`. -/
theorem chi_psi_props (hd : 1 ≤ d) :
    (∀ ξ : Euc d, 0 ≤ chi ξ ∧ chi ξ ≤ 1) ∧ (∀ ξ : Euc d, ‖ξ‖ ≤ 1 → chi ξ = 1) ∧
      (∀ ξ : Euc d, 2 ≤ ‖ξ‖ → chi ξ = 0) ∧ (∀ ξ : Euc d, chi (-ξ) = chi ξ) ∧
      ContDiff ℝ ∞ (chi : Euc d → ℝ) ∧
      (∀ L : ℝ, 0 < L → ∃ Ω : SchwartzMap (Euc d) ℂ, ∀ x, Ω x = ((psiL L x : ℝ) : ℂ)) ∧
      (∀ (L : ℝ) (x : Euc d), psiL L (-x) = psiL L x) ∧
      (∀ L : ℝ, 0 < L → ∫ x : Euc d, psiL L x = 1) := by
  refine ⟨fun ξ => ⟨cmxFB_chi_nonneg ξ, cmxFB_chi_le_one ξ⟩, fun ξ h => cmxFB_chi_one h,
    fun ξ h => cmxFB_chi_zero h, cmxFB_chi_neg, cmxFB_chi_contDiff, fun L hL => ?_,
    cmxFB_psiL_neg, fun L hL => cmxFB_integral_psiL hL⟩
  exact ⟨cmxFB_Om L hL, cmxFB_Om_apply hL⟩

/-- `[N] L393` ("This kernel is smooth and even. Its gradient and all derivatives of its gradient
are bounded, and `∇g_{≤1}(0) = 0`"): `∇g_{≤1} = ψ * ∇g` is smooth, odd, vanishes at `0`, and all its
derivatives are bounded.  (Used for the smoothness of `u = ∇g_{≤1}*ν` and `(5.highidentity)`.) -/
theorem gloForce_props (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ContDiff ℝ ∞ (gloForce s : Euc d → Euc d) ∧ gloForce s (0 : Euc d) = 0 ∧
      (∀ x : Euc d, gloForce s (-x) = -gloForce s x) ∧
      ∀ k : ℕ, ∃ B : ℝ, ∀ x : Euc d, ‖iteratedFDeriv ℝ k (gloForce s) x‖ ≤ B := by
  have hK := cmxFB_kerOK hd hs0 hsd
  have hOdd := cmxFB_gloForce_neg (s := s) (d := d)
  refine ⟨?_, ?_, hOdd, ?_⟩
  · rw [cmxFB_gloForce_eq, contDiff_infty]
    exact fun n => cmxFB_Phi_contDiff hK n _ _
  · have h := hOdd 0
    rw [neg_zero] at h
    have h2 : gloForce s (0 : Euc d) + gloForce s (0 : Euc d) = 0 := by
      nth_rewrite 1 [h]; exact neg_add_cancel _
    have h3 : (2 : ℝ) • gloForce s (0 : Euc d) = 0 := by rw [two_smul]; exact h2
    exact (smul_eq_zero.1 h3).resolve_left (by norm_num)
  · intro k
    rw [cmxFB_gloForce_eq]
    exact cmxFB_Phi_iter_bdd hK k _ _

/-- `[N] L393`/(4.pairing): `P_{≤L}` of a function of at most linear growth has Fourier support in
`B̄(0,2L)` (the Fourier transform of `P_{≤L}f` is `χ(ξ/L) f̂`, `supp χ ⊂ B(0,2)`); here for
Lipschitz scalar `f` and for `L^p` functions. -/
theorem Pleq_fourierSupp (hd : 1 ≤ d) (L : ℝ) (hL : 0 < L) (f : Euc d → ℝ) (C : ℝ)
    (hf : ∀ x, |f x| ≤ C * (1 + ‖x‖)) (hm : Measurable f) :
    FourierSuppIn (2 * L) (Pleq L f) := fun φ hφ =>
  cmxFB_Pleq_supp L hL f C hf hm φ (by
    simpa [Metric.closedBall] using hφ)

/-! ### Lemma 3.1 -/

/-- Lemma 3.1 `lem:kernelremainder` (`[N] L409-415`), first assertion `(3.kernelremainder)`
(L411): `|x||∇g_{>1}(x)| ≲ f_1(x)` for `x ≠ 0`. -/
theorem kernel_remainder (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Euc d, x ≠ 0 → ‖x‖ * ‖ghiForce s x‖ ≤ C * fTrunc s 1 x := by
  obtain ⟨c0, C0, hc0, hC0, hcmp⟩ := fcomparison (d := d) (s := s) hd hs0 hsd
  obtain ⟨Cf, hCf⟩ := cmxMY_ghi_far hd hs0 hsd (2 * d + 5)
  have hK := cmxFB_kerOK hd hs0 hsd
  obtain ⟨B, hB⟩ := cmxFB_Phi_bdd hK (cmxFB_B0 d) (cmxFB_Om (d := d) 1 one_pos)
  have hglo : ∀ x : Euc d, ‖gloForce s x‖ ≤ |B| := fun x => by
    rw [cmxFB_gloForce_eq]; exact (hB x).trans (le_abs_self B)
  refine ⟨(|Cf| + 1 + |B| + 1) / c0, by positivity, fun x hx => ?_⟩
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨h1, h2, h3⟩ := hcmp x hx
  by_cases hx1 : ‖x‖ ≤ 1
  · -- near field
    have hnear : ‖x‖ * ‖ghiForce s x‖ ≤ ‖x‖ ^ (-s) + |B| * ‖x‖ := by
      have hg : ‖ghiForce s x‖ ≤ ‖x‖ ^ (-(s + 1)) + |B| := by
        calc ‖ghiForce s x‖ = ‖kernGrad s x - gloForce s x‖ := rfl
          _ ≤ ‖kernGrad s x‖ + ‖gloForce s x‖ := norm_sub_le _ _
          _ ≤ ‖x‖ ^ (-(s + 1)) + |B| := add_le_add (cmxFB_kernGrad_norm_le hs0 x) (hglo x)
      calc ‖x‖ * ‖ghiForce s x‖ ≤ ‖x‖ * (‖x‖ ^ (-(s + 1)) + |B|) :=
            mul_le_mul_of_nonneg_left hg hxn.le
        _ = ‖x‖ ^ (-s) + |B| * ‖x‖ := by
            rw [mul_add, show -s = 1 + -(s + 1) by ring, Real.rpow_add hxn, Real.rpow_one]
            ring
    by_cases hs : s = 0
    · have hlow := (h2 hs hx1).1
      have hlog : 1 ≤ 1 + |Real.log ‖x‖| := by linarith [abs_nonneg (Real.log ‖x‖)]
      have hf : c0 ≤ fTrunc s 1 x := by nlinarith
      have hone : ‖x‖ ^ (-s) = 1 := by rw [hs]; simp
      rw [hone] at hnear
      have hB0 : |B| * ‖x‖ ≤ |B| := by
        calc |B| * ‖x‖ ≤ |B| * 1 := by gcongr
          _ = |B| := mul_one _
      calc ‖x‖ * ‖ghiForce s x‖ ≤ 1 + |B| := by linarith
        _ ≤ (|Cf| + 1 + |B| + 1) := by linarith [abs_nonneg Cf]
        _ = ((|Cf| + 1 + |B| + 1) / c0) * c0 := by field_simp
        _ ≤ ((|Cf| + 1 + |B| + 1) / c0) * fTrunc s 1 x := by gcongr
    · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      have hlow := (h1 hs' hx1).1
      have hone : 1 ≤ ‖x‖ ^ (-s) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hxn hx1 (by linarith)
      have hB0 : |B| * ‖x‖ ≤ |B| * ‖x‖ ^ (-s) := by
        calc |B| * ‖x‖ ≤ |B| * 1 := by gcongr
          _ ≤ |B| * ‖x‖ ^ (-s) := by gcongr
      have hp : 0 < ‖x‖ ^ (-s) := Real.rpow_pos_of_pos hxn _
      calc ‖x‖ * ‖ghiForce s x‖ ≤ (1 + |B|) * ‖x‖ ^ (-s) := by linarith
        _ ≤ (|Cf| + 1 + |B| + 1) * ‖x‖ ^ (-s) :=
            mul_le_mul_of_nonneg_right (by linarith [abs_nonneg Cf, abs_nonneg B]) hp.le
        _ = ((|Cf| + 1 + |B| + 1) / c0) * (c0 * ‖x‖ ^ (-s)) := by field_simp
        _ ≤ ((|Cf| + 1 + |B| + 1) / c0) * fTrunc s 1 x := by gcongr
  · -- far field
    have hx1' : 1 ≤ ‖x‖ := (not_le.1 hx1).le
    have hlow := (h3 hx1').1
    have hfar := hCf x hx1'
    have hp : 0 < ‖x‖ ^ (-(2 * (d : ℝ) + 4)) := Real.rpow_pos_of_pos hxn _
    have e : ‖x‖ * ‖x‖ ^ (-((2 * d + 5 : ℕ) : ℝ)) = ‖x‖ ^ (-(2 * (d : ℝ) + 4)) := by
      rw [show -(2 * (d : ℝ) + 4) = 1 + -((2 * d + 5 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_add hxn, Real.rpow_one]
    calc ‖x‖ * ‖ghiForce s x‖ ≤ ‖x‖ * (Cf * ‖x‖ ^ (-((2 * d + 5 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hfar hxn.le
      _ = Cf * ‖x‖ ^ (-(2 * (d : ℝ) + 4)) := by rw [← e]; ring
      _ ≤ |Cf| * ‖x‖ ^ (-(2 * (d : ℝ) + 4)) := by gcongr; exact le_abs_self _
      _ ≤ (|Cf| + 1 + |B| + 1) * ‖x‖ ^ (-(2 * (d : ℝ) + 4)) := by
          gcongr; linarith [abs_nonneg B]
      _ = ((|Cf| + 1 + |B| + 1) / c0) * (c0 * ‖x‖ ^ (-(2 * (d : ℝ) + 4))) := by field_simp
      _ ≤ ((|Cf| + 1 + |B| + 1) / c0) * fTrunc s 1 x := by gcongr

/-- Lemma 3.1, "Consequently" (`[N] L414`): `|x||∇g_{>1}(x)|` belongs to `L¹ ∩ L^{p'}` for
`p > d/(d-s)` (`p'` the Hölder conjugate `q`, `p⁻¹ + q⁻¹ = 1`; `q = 1` is `p = ∞`). -/
theorem kernel_remainder_Lp (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    MemLp (fun x : Euc d => ‖x‖ * ‖ghiForce s x‖) 1 volume ∧
      ∀ p q : ℝ≥0∞, ENNReal.ofReal ((d : ℝ) / (d - s)) < p → p⁻¹ + q⁻¹ = 1 →
        MemLp (fun x : Euc d => ‖x‖ * ‖ghiForce s x‖) q volume := by
  obtain ⟨C, hC0, hC⟩ := kernel_remainder (d := d) (s := s) hd hs0 hsd
  have hmeas : AEStronglyMeasurable (fun x : Euc d => ‖x‖ * ‖ghiForce s x‖) volume := by
    have h1 : Measurable (ghiForce s : Euc d → Euc d) :=
      (cmxSA_kernGrad_measurable s).sub (cmxMY_gloForce_continuous hd hs0 hsd).measurable
    exact (measurable_norm.mul h1.norm).aestronglyMeasurable
  have hle : ∀ᵐ x : Euc d, ‖‖x‖ * ‖ghiForce s x‖‖ ≤ C * fTrunc s 1 x := by
    filter_upwards [ae_ne_zero_euc (d := d) (by omega)] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact hC x hx
  have key : ∀ q : ℝ≥0∞, MemLp (fTrunc s 1 : Euc d → ℝ) q volume →
      MemLp (fun x : Euc d => ‖x‖ * ‖ghiForce s x‖) q volume := fun q hq =>
    (hq.const_mul C).mono' hmeas hle
  refine ⟨key 1 (fTrunc_Lq hd hs0 hsd ⊤ 1 (by simp) (by simp)), fun p q hp hpq => ?_⟩
  exact key q (fTrunc_Lq hd hs0 hsd p q hp hpq)

/-! ### Lemma 3.2 -/

/-- `(3.zhigh)` first estimate (`[N] L432`, proof L455): `C(v_{≤1}) ≲ C(v)`; i.e. `v_{≤1} = ψ * v`
has `‖∇v_{≤1}‖_∞ ≤ ‖ψ‖_{L¹}‖∇v‖_∞` and `|∇|^α v_{≤1} = ψ * |∇|^α v` (Young). -/
theorem vlo_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      SubTransport d s (Pleq 1 v) (C * K) :=
  SAMP1.vlo_core hd hs0 hsd

/-- `(3.zhigh)` second estimate (`[N] L433-434`, proof L455-460: Mikhlin multipliers
`(3.high-multipliers)`, here via kernel bounds + Young): `‖⟨∇⟩^α v_{>1}‖_{L^{p₁}} + ‖v_{>1}‖_{L^{p₁}}
≲ ‖|∇|^α v‖_{L^{p₁}}`, `v_{>1} = P_{>1}v`.  (`⟨∇⟩^α v_{>1}` is represented by `W`,
`IsBesselRep`.) -/
theorem vhi_Lp (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (L : ℝ≥0) (w : Euc d → Euc d) (F : ℝ),
      HasFracData d s v L w F →
      ∃ W : Euc d → Euc d,
        (∀ i, IsBesselRep (alphaE d s) (fun x => Pgt 1 v x i) (fun x => W x i)) ∧
        eLpNorm (fun x => ‖W x‖) (ENNReal.ofReal (p1E d s)) volume +
            eLpNorm (fun x => ‖Pgt 1 v x‖) (ENNReal.ofReal (p1E d s)) volume ≤
          ENNReal.ofReal (C * F) := by
  obtain ⟨C, hC, h⟩ := SAMP1.vhi_Lp_core hd hs0 hsd
  exact ⟨C, hC, fun v L w F hF => h v L w F hF.lip hF.rep hF.norm⟩

/-- `(3.high-continuous)` (`[N] L461-464`): `v_{>1}(x) = ∫ ψ(y)(v(x) - v(x-y)) dy` is bounded and
continuous with `‖v_{>1}‖_∞ ≲ ‖∇v‖_∞`, so its point values are unambiguous. -/
theorem vhi_bounded (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (L : ℝ≥0), LipschitzWith L v →
      Continuous (Pgt 1 v) ∧
      (∀ x, Pgt 1 v x = ∫ y, psiL 1 y • (v x - v (x - y))) ∧
      ∀ x, ‖Pgt 1 v x‖ ≤ C * L := by
  obtain ⟨C, hC, h⟩ := SAMP1.vhi_bounded_core d
  exact ⟨C, hC, fun v L hL => h v L hL⟩

/-- `(3.zsample)` (`[N] L437-440`, proof L466-484: kernel bounds `(3.K-bounds)`, `(3.cube-kernel)`,
`(3.cube-convolution)`, Hölder and Young for sequences; only `α > d/p₁` is used):
`(∑_j sup_{Q_j} |v_{>1}|^{p₁})^{1/p₁} ≲ ‖|∇|^α v‖_{L^{p₁}}`. -/
theorem vhi_cube_sampling (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (L : ℝ≥0) (w : Euc d → Euc d) (F : ℝ),
      HasFracData d s v L w F →
        cubeSupNorm (p1E d s) (Pgt 1 v) ≤ ENNReal.ofReal (C * F) := by
  obtain ⟨C, hC, h⟩ := SAMP1.vhi_cube_core hd hs0 hsd
  exact ⟨C, hC, fun v L w F hF => h v L w F hF.lip hF.rep hF.norm⟩

/-- `(3.usample)` (`[N] L441-446`, proof L486): for `u ∈ L^{p₂}` with Fourier support in `B(0,2)`
(componentwise) and `u` continuous (the point values of the `L^{p₂}` class must be meaningful; `u = Ω*u` is
smooth anyway), `‖⟨∇⟩^α u‖_{L^{p₂}} + (∑_j sup_{Q_j}|u|^{p₂})^{1/p₂} ≲ ‖u‖_{L^{p₂}}`
(`u = Ω * u` for a Schwartz `Ω` with `Ω̂ = 1` on `B̄(0,2)`). -/
theorem usample (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Euc d → Euc d, Continuous u →
      MemLp (fun x => ‖u x‖) (ENNReal.ofReal (p2E d s)) volume →
      (∀ i, FourierSuppIn 2 (fun x => u x i)) →
      ∃ U : Euc d → Euc d,
        (∀ i, IsBesselRep (alphaE d s) (fun x => u x i) (fun x => U x i)) ∧
        eLpNorm (fun x => ‖U x‖) (ENNReal.ofReal (p2E d s)) volume +
            cubeSupNorm (p2E d s) u ≤
          ENNReal.ofReal C * eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal (p2E d s)) volume := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 1 < p2E d s := by
    unfold p2E
    rw [lt_div_iff₀ (by linarith)]
    linarith
  exact HRS.Commutator.Whole.SAMP2.usample_core (d := d) (by omega) (alphaE d s) hp

/-- `(3.potentialSobolev)` (`[N] L447-451`, proof L488-498: `0 < α-1 < d/2`, `1/p₂ = 1/2 - (α-1)/d`,
homogeneous Sobolev inequality, Plancherel and the Riesz multiplier): for a compactly supported finite
measure or Schwartz density `σ` (of mass zero when `s = 0`),
`‖∇g_{≤1} * σ‖_{L^{p₂}} ≲ ‖P_{≤4}σ‖_{Ḣ^{-α}}`. -/
theorem potentialSobolev (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : SMeas d, IsAdmissible σ → (s = 0 → σ.mass = 0) →
      eLpNorm (fun x => ‖σ.convForce (gloForce s) x‖) (ENNReal.ofReal (p2E d s)) volume ≤
        ENNReal.ofReal C * (homSqE (-alphaE d s) (lowFreq 4 σ.fourier)) ^ ((1 : ℝ) / 2) := by
  obtain ⟨C, hC, h⟩ := HRS.Commutator.Whole.SAMP2.potential_core (d := d) (s := s) hd hs0 hsd
  exact ⟨C, hC, fun σ hσ _ => h σ hσ⟩

/-- `(3.product)` (`[N] L507-512`, "Applying `(3.leibniz)` componentwise and using Lemma 3.2"):
for `u ∈ L^{p₂}` with Fourier support in `B(0,2)`,
`‖v_{>1} · u‖_{H^α} ≲ ‖|∇|^α v‖_{L^{p₁}} ‖u‖_{L^{p₂}}`.  The conclusion includes that
`v_{>1}·u ∈ L²` (so that `fourierL2` is the Plancherel transform).  `u` is assumed a.e. strongly measurable
(2026-10-15 repair, ISSUES §I: without it the statement is false — `FourierSuppIn` is vacuous and `MemLp ‖u‖` does not
force measurability of `u`; the source's `u ∈ L^{p₂}` means a measurable function). -/
theorem product_estimate (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (L : ℝ≥0) (w : Euc d → Euc d) (F : ℝ),
      HasFracData d s v L w F → ∀ u : Euc d → Euc d, AEStronglyMeasurable u volume →
      MemLp (fun x => ‖u x‖) (ENNReal.ofReal (p2E d s)) volume →
      (∀ i, FourierSuppIn 2 (fun x => u x i)) →
        MemLp (fun x => inner ℝ (Pgt 1 v x) (u x)) 2 volume ∧
        (sobSqE (alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 (fun x => inner ℝ (Pgt 1 v x) (u x)))) ^
            ((1 : ℝ) / 2) ≤
          ENNReal.ofReal (C * F) *
            eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal (p2E d s)) volume := by
  sorry

end HRS.Commutator.Whole
