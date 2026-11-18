import HRS.Energy.Commutator.Basic
import HRS.Energy.Commutator.SliceAux

/-!
# Route S, packet S1: the resolvent ("Stieltjes") slices of the Riesz kernel

For `d - 2 ≤ s < d` put `β = (d-s)/2 ∈ (0,1]`.  The Fourier symbol `|k|^{-2β}` is the Stieltjes
mixture of the *screened Coulomb* symbols `(l + 4π²|k|²)^{-1}`:
`(4π²|k|²)^{-β} = (sin πβ/π) ∫_0^∞ l^{-β} (l + 4π²|k|²)^{-1} dl`  (`0 < β < 1`), and for `β = 1` the
mixture degenerates to the single slice `l = 0` (Coulomb).  Equivalently (and this is the form that
reuses the repository's heat subordination `periodicRiesz_eq_integral_one`): the Laplace transform in
the heat time, `∫_0^∞ l^{-β} e^{-lt} dl = Γ(1-β) t^{β-1}`.

**This replaces the Caffarelli-Silvestre extension** `T^d × ℝ` with weight `|z|^{s+1-d}` of `[RS]`,
`[CdCRS]`: every slice is a *local, non-degenerate* operator `l - Δ` on `T^d`, for which the
Serfaty smearing/stress-tensor argument is classical (Newton's theorem for `l - Δ` with compactly
supported radial charges, see `Smear.lean`).  The slice parameter `l` plays the role of the
extension variable `z`; the identities `L g = c δ`, `g * δ^{(η)} = min(g, g(η))`, the stress-energy
tensor and the energy identity `[RS] (2.19)` all hold slice by slice and are integrated against
`l^{-β} dl` at the end.  No weighted (`A_2`) elliptic theory, no Bessel `K_ν`.

Notation: `sliceG d l` is the *mean-free* slice kernel `∑_{k≠0} e^{2πik·x}/(l + 4π²|k|²)`
(for `l = 0`: the periodic Green function of `-Δ`); `sliceGfull = sliceG + 1/l` is the periodic
Green function of `l - Δ` (`l > 0`), equal to `∑_m Γ_l(|x+m|)` with the Euclidean Yukawa profile
`Γ_l` (`yukawa`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator

variable {d : ℕ} {s l : ℝ}

/-- The Euclidean Yukawa (screened Newton) profile `Γ_l(r) = ∫_0^∞ e^{-lt} (4πt)^{-d/2} e^{-r²/4t} dt`,
the fundamental solution of `l - Δ` on `ℝ^d` (`d ≥ 1`, `l > 0`; also `l = 0`, `d ≥ 3`). -/
def yukawa (d : ℕ) (l r : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (4 * t)))

/-- The mean-free slice kernel `𝒢_l(x) = ∫_0^∞ e^{-lt} ∑_{k≠0} e^{-4π² t |k|²} cos(2πk·x) dt
= ∑_{k≠0} cos(2πk·x)/(l + 4π²|k|²)` (`x ≠ 0`; the heat time `4π² t` is the repository's `u` in
`psiFn`).  For `l = 0` this is the periodic Green function of `-Δ`. -/
def sliceG (d : ℕ) (l : ℝ) (x : Torus d) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * psiFn x (4 * Real.pi ^ 2 * t)

/-- The periodic Green function of `l - Δ` (`l > 0`) including the zero mode `1/l`.
(For `l = 0` Lean's `1/0 = 0` makes this the mean-free Green function, which is what is wanted.) -/
def sliceGfull (d : ℕ) (l : ℝ) (x : Torus d) : ℝ := sliceG d l x + 1 / l

/-- The force of the slice, `∇ 𝒢_l` (smooth for `x ≠ 0`; value at `0` irrelevant). -/
def sliceGrad (d : ℕ) (l : ℝ) (x : Torus d) : Euc d := Torus.grad (sliceG d l) x

/-- **S1.1 (Stieltjes/Laplace representation of the kernel).**  For `d - 2 < s < d` (`β < 1`):
`g = c ∫_0^∞ l^{-β} 𝒢_l dl` off the origin, with `c = subA d s (4π²)^β / Γ(1-β) > 0`.
*Proof.*  `periodicRiesz_eq_integral_one`: `g(x) = A ∫_0^∞ u^{β-1} Ψ(x,u) du`; substitute `u = 4π²t`,
insert `∫_0^∞ l^{-β} e^{-lt} dl = Γ(1-β) t^{β-1}` and apply Fubini; the absolute integrand
`l^{-β} e^{-lt} |Ψ(x,4π²t)|` is integrable for `x ≠ 0` because `|Ψ(x,u)| ≤ M e^{-u}` (`psi_bound`)
and `u^{β-1}` is integrable at `0` (`integrableOn_psi`).  (~200 lines.) -/
theorem stieltjes_kernel (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Torus d, x ≠ 0 →
      periodicRiesz d s x = c * ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * sliceG d l x := by
  have hβ1 : bexp d s < 1 := by unfold bexp; linarith
  have hG : 0 < Real.Gamma (1 - bexp d s) := Real.Gamma_pos_of_pos (by linarith)
  refine ⟨KernelAux.subA d s * ((4 * Real.pi ^ 2) ^ bexp d s / Real.Gamma (1 - bexp d s)),
    mul_pos (CoercAux.subA_pos_one hd hs0 hsd) (by positivity), fun x hx => ?_⟩
  have hi := KernelAux.integrableOn_psi hsd x hx
  have hc := psi_continuousOn x
  have hb : bexp d s - 1 = ((d : ℝ) - s) / 2 - 1 := rfl
  rw [CoercAux.periodicRiesz_eq_integral_one hd hs0 hsd x hx, ← hb]
  rw [(SliceAux.bridge hβ1 hc (by rwa [hb])).2, mul_assoc]
  rfl

/-- **S1.1' (Coulomb case `s = d-2`, `β = 1`, `d ≥ 2`).**  A single slice, `l = 0`:
`g = c · 𝒢_0` off the origin (`c = 4π² subA d (d-2)`).  (For `d = 2` this is the logarithm.) -/
theorem coulomb_kernel (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Torus d, x ≠ 0 →
      periodicRiesz d ((d : ℝ) - 2) x = c * sliceG d 0 x := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : (d : ℝ) - 2 < d := by linarith
  refine ⟨4 * Real.pi ^ 2 * KernelAux.subA d ((d : ℝ) - 2),
    mul_pos (by positivity) (CoercAux.subA_pos_one hd1 hs0 hsd), fun x hx => ?_⟩
  have hi := KernelAux.integrableOn_psi hsd x hx
  have hb : (((d : ℝ) - ((d : ℝ) - 2)) / 2 - 1) = 0 := by ring
  rw [hb] at hi
  simp only [Real.rpow_zero, one_mul] at hi
  obtain ⟨-, he⟩ := SliceAux.scale_integral (β := 1) (b := 4 * Real.pi ^ 2) (by positivity)
    (H := fun u => psiFn x u) (by simpa using hi)
  rw [CoercAux.periodicRiesz_eq_integral_one hd1 hs0 hsd x hx, hb]
  simp only [Real.rpow_zero, one_mul, sub_self] at he ⊢
  rw [he, Real.rpow_one]
  unfold sliceG
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul]
  ring

/-- The force of the slice, componentwise: `∂_j 𝒢_l(x) = ∫_0^∞ e^{-lt} ∂_jΨ(x,4π²t) dt`. -/
theorem sliceGrad_eq (hl : 0 ≤ l) {x : Torus d} (hx : x ≠ 0) :
    sliceGrad d l x = WithLp.toLp 2 (fun j => ∫ t in Ioi (0 : ℝ),
      Real.exp (-l * t) * KernelAux.psiG j x (4 * Real.pi ^ 2 * t)) := by
  have hr : Torus.mk (Torus.rep x) = x := Torus.mk_rep x
  have h := SliceAux.hasFDerivAt_slice (d := d) hl (y0 := Torus.rep x) (by rw [hr]; exact hx)
  rw [hr] at h
  have h2 : HasGradientAt (Torus.lift (sliceG d l)) (WithLp.toLp 2 (fun j => ∫ t in Ioi (0 : ℝ),
      Real.exp (-l * t) * KernelAux.psiG j x (4 * Real.pi ^ 2 * t))) (Torus.rep x) := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have h' : HasFDerivAt (Torus.lift (sliceG d l)) (∑ j, (∫ t in Ioi (0 : ℝ),
        Real.exp (-l * t) * KernelAux.psiG j x (4 * Real.pi ^ 2 * t)) •
          (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)) (Torus.rep x) := h
    convert h' using 1
    ext v
    simp [PiLp.inner_apply, mul_comm]
  exact h2.gradient

/-- **S1.2 (gradient of the representation).**  Same constant `c` as in S1.1 (differentiation under
the integral sign: `∫ l^{-β} ∫ e^{-lt} |∇Ψ(x,4π²t)| dt dl = Γ(1-β) ∫ t^{β-1}|∇Ψ| dt < ∞`, locally
uniformly in `x ≠ 0`, `heat_comp_bound` / `psiG_bound_unif`). -/
theorem stieltjes_grad (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Torus d, x ≠ 0 →
      periodicRieszGrad d s x = c • ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) • sliceGrad d l x := by
  have hβ1 : bexp d s < 1 := by unfold bexp; linarith
  have hβ0 : 0 < bexp d s := by unfold bexp; linarith
  have hG : 0 < Real.Gamma (1 - bexp d s) := Real.Gamma_pos_of_pos (by linarith)
  refine ⟨KernelAux.subA d s * ((4 * Real.pi ^ 2) ^ bexp d s / Real.Gamma (1 - bexp d s)),
    mul_pos (CoercAux.subA_pos_one hd hs0 hsd) (by positivity), fun x hx => ?_⟩
  have hb : bexp d s - 1 = ((d : ℝ) - s) / 2 - 1 := rfl
  obtain ⟨xe, rfl, hxe⟩ := KernelGrad.exists_mk_box x
  have hne : xe ≠ 0 := SliceAux.mk_ne_zero_ne_zero hx
  -- the bridge for each component
  have hbr : ∀ j : Fin d,
      IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * ∫ t in Ioi (0 : ℝ),
        Real.exp (-l * t) * KernelAux.psiG j (Torus.mk xe) (4 * Real.pi ^ 2 * t)) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), u ^ (bexp d s - 1) * KernelAux.psiG j (Torus.mk xe) u =
        ((4 * Real.pi ^ 2) ^ bexp d s / Real.Gamma (1 - bexp d s)) *
          ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * ∫ t in Ioi (0 : ℝ),
            Real.exp (-l * t) * KernelAux.psiG j (Torus.mk xe) (4 * Real.pi ^ 2 * t) := fun j =>
    SliceAux.bridge hβ1 (KernelAux.psiG_continuousOn j _)
      (SliceAux.integrableOn_psiG hβ0 j hx)
  have hF : ∀ l ∈ Ioi (0 : ℝ), l ^ (-bexp d s) • sliceGrad d l (Torus.mk xe) =
      WithLp.toLp 2 (fun j => l ^ (-bexp d s) * ∫ t in Ioi (0 : ℝ),
        Real.exp (-l * t) * KernelAux.psiG j (Torus.mk xe) (4 * Real.pi ^ 2 * t)) := by
    intro l hl
    rw [sliceGrad_eq (le_of_lt hl) hx]
    ext j
    simp
  rw [setIntegral_congr_fun measurableSet_Ioi hF, KernelAux.periodicRieszGrad_eq hsd xe hxe hne]
  ext j
  have h2 := eval_integral_piLp (μ := volume.restrict (Ioi (0 : ℝ))) (q := 2) (E := fun _ : Fin d => ℝ)
    (f := fun l : ℝ => (WithLp.toLp 2 (fun j => l ^ (-bexp d s) * ∫ t in Ioi (0 : ℝ),
        Real.exp (-l * t) * KernelAux.psiG j (Torus.mk xe) (4 * Real.pi ^ 2 * t)) : Euc d))
    (fun j => (hbr j).1) j
  simp only [PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul] at h2 ⊢
  rw [h2]
  show KernelAux.subA d s * ∫ t in Ioi (0 : ℝ), t ^ (((d : ℝ) - s) / 2 - 1) *
      KernelAux.psiG j (Torus.mk xe) t = _
  rw [← hb, (hbr j).2]
  ring

/-- A Lipschitz field is continuous. -/
theorem lipschitzVF_continuous {L : ℝ} {v : Torus d → Euc d} (hL : 0 ≤ L) (hv : IsLipschitzVF L v) :
    Continuous v := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun y => L * KernelGrad.tdist y x) (𝓝 x) (𝓝 (L * KernelGrad.tdist x x)) :=
    ((CoercAux.continuous_tdist_left x).const_mul L).tendsto x
  have h2 : KernelGrad.tdist x x = 0 := CoercAux.tdist_self x
  rw [h2, mul_zero] at h1
  exact squeeze_zero (fun y => norm_nonneg _) (fun y => hv y x) h1

/-- **S1.3 (Fubini for the commutator quantity).**  The commutator quantity is the Stieltjes
mixture of the slice commutator quantities (all integrals absolutely convergent; the pair sums are
finite sums and the `μ`-integrals are dominated by `Λ ∫ tdist^{-s}`). -/
theorem commQuantity_stieltjes (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (X : Config d N) (ρ : Torus d → ℝ), IsProbDensity ρ →
      ∀ Λ : ℝ, (∀ x, ρ x ≤ Λ) → X ∉ collisionSet d N →
      ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v →
        commQuantity d s v X (withDensityReal ρ) =
          c * ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) *
            offDiagPairing (commKernel (sliceGrad d l) v) X (withDensityReal ρ) := by
  obtain ⟨c, hc, hgrad⟩ := stieltjes_grad hd hs0 hs hsd
  obtain ⟨C, hC0, hC⟩ := SliceAux.slice_abs_bound hs0 hs hsd
  refine ⟨c, hc, fun N X ρ hρ Λ hΛ hX L v hL hv => ?_⟩
  have hd0 : 0 < d := hd
  have hβ : bexp d s = ((d : ℝ) - s) / 2 := rfl
  set μ := withDensityReal ρ with hμ
  have : SFinite μ := by rw [hμ]; unfold withDensityReal; infer_instance
  have hvc : Continuous v := lipschitzVF_continuous hL hv
  have hvm : Measurable v := hvc.measurable
  -- the slice kernels
  set kS : ℝ → Torus d → Torus d → ℝ := fun l => commKernel (SliceAux.sgv l) v with hkS
  have hmeas : Measurable fun p : ℝ × (Torus d × Torus d) => kS p.1 p.2.1 p.2.2 := by
    simp only [hkS, commKernel]
    refine Measurable.ite (measurableSet_eq_fun measurable_snd.fst measurable_snd.snd)
      measurable_const ?_
    refine Measurable.inner ?_ ?_
    · exact (hvm.comp measurable_snd.fst).sub (hvm.comp measurable_snd.snd)
    · exact SliceAux.measurable_sgv.comp (measurable_fst.prodMk (measurable_snd.fst.sub measurable_snd.snd))
  have htd : ∀ x y : Torus d, KernelGrad.tdist x y = KernelGrad.tdist (x - y) 0 := by
    intro x y; simp [KernelGrad.tdist]
  -- pointwise domination
  have hkb : ∀ (l : ℝ) (x y : Torus d), |kS l x y| ≤
      L * KernelGrad.tdist x y * ∑ j, |SliceAux.sgc j l (x - y)| := by
    intro l x y
    simp only [hkS, commKernel]
    split_ifs with hxy
    · simp only [abs_zero]
      have := KernelGrad.tdist_nonneg x y
      have h2 : 0 ≤ ∑ j, |SliceAux.sgc j l (x - y)| := Finset.sum_nonneg fun j _ => abs_nonneg _
      positivity
    · calc |inner ℝ (v x - v y) (SliceAux.sgv l (x - y))|
          ≤ ‖v x - v y‖ * ‖SliceAux.sgv l (x - y)‖ := abs_real_inner_le_norm _ _
        _ ≤ (L * KernelGrad.tdist x y) * ∑ j, |SliceAux.sgc j l (x - y)| :=
            mul_le_mul (hv x y) (SliceAux.norm_sgv_le l (x - y)) (norm_nonneg _)
              (mul_nonneg hL (KernelGrad.tdist_nonneg x y))
  have hkS_diag : ∀ l x, kS l x x = 0 := by
    intro l x; simp [hkS, commKernel]
  -- integrable majorant for x ≠ y
  have hmaj : ∀ x y : Torus d, x ≠ y →
      IntegrableOn (fun l : ℝ => L * KernelGrad.tdist x y *
        ∑ j, l ^ (-(((d : ℝ) - s) / 2)) * |SliceAux.sgc j l (x - y)|) (Ioi 0) := by
    intro x y hxy
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have : IntegrableOn (fun l : ℝ => ∑ j, l ^ (-(((d : ℝ) - s) / 2)) * |SliceAux.sgc j l (x - y)|)
        (Ioi 0) := integrable_finsetSum _ fun j _ => (hC j _ hz).1
    exact this.const_mul _
  have hkm : ∀ x y : Torus d, Measurable fun l : ℝ => kS l x y := fun x y => by
    have := hmeas.comp (measurable_id.prodMk (measurable_const : Measurable fun _ : ℝ => (x, y)))
    exact this
  -- (h1) integrability of each slice
  have h1 : ∀ x y : Torus d,
      IntegrableOn (fun l : ℝ => l ^ (-(((d : ℝ) - s) / 2)) * kS l x y) (Ioi 0) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp only [hkS_diag, mul_zero]
      exact integrableOn_zero
    · refine Integrable.mono' (hmaj x y hxy) ?_ ?_
      · exact ((measurable_id.pow_const _).mul (hkm x y)).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun l hl => ?_)
        have hl' : (0:ℝ) < l := hl
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hl' _)]
        have := hkb l x y
        calc l ^ (-(((d : ℝ) - s) / 2)) * |kS l x y|
            ≤ l ^ (-(((d : ℝ) - s) / 2)) * (L * KernelGrad.tdist x y * ∑ j, |SliceAux.sgc j l (x - y)|) :=
              mul_le_mul_of_nonneg_left this (Real.rpow_pos_of_pos hl' _).le
          _ = _ := by rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
                      exact Finset.sum_congr rfl fun j _ => by ring
  -- the domination function
  set Θ : Torus d → ℝ := fun z => L * d * C * (KernelGrad.tdist z 0 ^ (-s) + d) with hΘ
  have hΘ0 : ∀ z, 0 ≤ Θ z := fun z => by
    have := Real.rpow_nonneg (KernelGrad.tdist_nonneg z 0) (-s)
    simp only [hΘ]; positivity
  have h2 : ∀ x y : Torus d,
      ∫ l in Ioi (0 : ℝ), ‖l ^ (-(((d : ℝ) - s) / 2)) * kS l x y‖ ≤ Θ (x - y) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp only [hkS_diag, mul_zero, norm_zero, integral_zero, sub_self]
      exact hΘ0 _
    · have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
      have ht : 0 < KernelGrad.tdist (x - y) 0 := by
        rw [KernelGrad.tdist_zero_right]
        refine norm_pos_iff.mpr fun h => hz ?_
        rw [← KernelGrad.mk_centeredRep (x - y), h]
        funext i; simp [Torus.mk]
      have hle : ∫ l in Ioi (0 : ℝ), ‖l ^ (-(((d : ℝ) - s) / 2)) * kS l x y‖ ≤
          ∫ l in Ioi (0 : ℝ), L * KernelGrad.tdist x y *
            ∑ j, l ^ (-(((d : ℝ) - s) / 2)) * |SliceAux.sgc j l (x - y)| := by
        refine setIntegral_mono_on ?_ (hmaj x y hxy) measurableSet_Ioi fun l hl => ?_
        · exact (h1 x y).norm
        · have hl' : (0:ℝ) < l := hl
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hl' _)]
          have := hkb l x y
          calc l ^ (-(((d : ℝ) - s) / 2)) * |kS l x y|
              ≤ l ^ (-(((d : ℝ) - s) / 2)) * (L * KernelGrad.tdist x y * ∑ j, |SliceAux.sgc j l (x - y)|) :=
                mul_le_mul_of_nonneg_left this (Real.rpow_pos_of_pos hl' _).le
            _ = _ := by rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
                        exact Finset.sum_congr rfl fun j _ => by ring
      refine hle.trans ?_
      rw [integral_const_mul, integral_finsetSum _ fun j _ => (hC j _ hz).1]
      have hsum : ∑ j : Fin d, ∫ l in Ioi (0 : ℝ), l ^ (-(((d : ℝ) - s) / 2)) * |SliceAux.sgc j l (x - y)| ≤
          ∑ j : Fin d, C * (KernelGrad.tdist (x - y) 0 ^ (-s - 1) + 1) :=
        Finset.sum_le_sum fun j _ => (hC j _ hz).2
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      rw [htd x y]
      set t := KernelGrad.tdist (x - y) 0 with htdef
      have htd' : t ≤ d := SliceAux.tdist_le_dim _
      have e : t * (t ^ (-s - 1) + 1) = t ^ (-s) + t := by
        have : t ^ (-s) = t ^ (-s - 1) * t := by
          rw [← Real.rpow_add_one ht.ne']; ring_nf
        rw [this]; ring
      have hLt : 0 ≤ L * t := mul_nonneg hL ht.le
      calc L * t * ∑ j : Fin d, ∫ l in Ioi (0 : ℝ), l ^ (-(((d : ℝ) - s) / 2)) * |SliceAux.sgc j l (x - y)|
          ≤ L * t * ((d : ℝ) * (C * (t ^ (-s - 1) + 1))) := by gcongr
        _ = L * d * C * (t * (t ^ (-s - 1) + 1)) := by ring
        _ = L * d * C * (t ^ (-s) + t) := by rw [e]
        _ ≤ Θ (x - y) := by
          simp only [hΘ]
          have : 0 ≤ L * (d : ℝ) * C := by positivity
          gcongr
  -- measurability / integrability of `Θ`
  have hΘm : Measurable Θ := by
    simp only [hΘ]
    exact measurable_const.mul
      (((CoercAux.continuous_tdist_zero.measurable).pow_const _).add measurable_const)
  have hΘi : Integrable Θ := by
    simp only [hΘ]
    exact ((SliceAux.integrable_tdist_rpow hd0 hs0 hsd).add (integrable_const (d : ℝ))).const_mul _
  have hΘ1 : ∀ x, Integrable (fun y => Θ (x - y)) μ :=
    fun x => CoercAux.integrable_conv_density hΛ hΘm hΘi x
  have hΘ2 := SliceAux.integrable_conv_prod hΛ hΘm hΘi
  -- the identity `∇g = c ∫ l^{-β} ∇𝒢_l` componentwise
  have hcomp : ∀ z : Torus d, z ≠ 0 → ∀ j : Fin d, periodicRieszGrad d s z j =
      c * ∫ l in Ioi (0 : ℝ), l ^ (-(((d : ℝ) - s) / 2)) * SliceAux.sgc j l z := by
    intro z hz j
    have hF : ∀ l ∈ Ioi (0 : ℝ), l ^ (-bexp d s) • sliceGrad d l z =
        WithLp.toLp 2 (fun j => l ^ (-(((d : ℝ) - s) / 2)) * SliceAux.sgc j l z) := by
      intro l hl
      rw [sliceGrad_eq (le_of_lt hl) hz]
      ext j
      simp [SliceAux.sgc, bexp]
    have h := congrArg (fun w : Euc d => w j) (hgrad z hz)
    simp only [PiLp.smul_apply, smul_eq_mul] at h
    rw [setIntegral_congr_fun measurableSet_Ioi hF] at h
    have h2 := eval_integral_piLp (μ := volume.restrict (Ioi (0 : ℝ))) (q := 2)
      (E := fun _ : Fin d => ℝ)
      (f := fun l : ℝ => (WithLp.toLp 2 (fun j => l ^ (-(((d : ℝ) - s) / 2)) * SliceAux.sgc j l z) : Euc d))
      (fun j => SliceAux.sgc_integrable hs0 hs hsd j hz) j
    simp only [PiLp.toLp_apply] at h2
    rw [h2] at h
    exact h
  have hin : ∀ a w : Euc d, inner ℝ a w = ∑ j, a j * w j := by
    intro a w; simp [PiLp.inner_apply, mul_comm]
  have h1' : ∀ x y : Torus d, commKernel (periodicRieszGrad d s) v x y =
      c * ∫ l in Ioi (0 : ℝ), l ^ (-(((d : ℝ) - s) / 2)) * kS l x y := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp [hkS_diag, commKernel]
    · have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
      have e1 : ∀ l : ℝ, l ^ (-(((d : ℝ) - s) / 2)) * kS l x y =
          ∑ j, (v x - v y) j * (l ^ (-(((d : ℝ) - s) / 2)) * SliceAux.sgc j l (x - y)) := by
        intro l
        simp only [hkS, commKernel, hxy, if_false, hin, SliceAux.sgv, PiLp.toLp_apply]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      simp only [e1]
      rw [integral_finsetSum _ fun j _ => (SliceAux.sgc_integrable hs0 hs hsd j hz).const_mul _,
        Finset.mul_sum]
      simp only [commKernel, hxy, if_false, hin]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, hcomp _ hz j]
      ring
  have key := SliceAux.offDiag_stieltjes (β := ((d : ℝ) - s) / 2) (c := c) kS
    (commKernel (periodicRieszGrad d s) v) X μ hmeas h1 h1' Θ h2 hΘ1 hΘ2
  have hcongr : ∀ l ∈ Ioi (0 : ℝ), offDiagPairing (commKernel (sliceGrad d l) v) X μ =
      offDiagPairing (kS l) X μ := by
    intro l hl
    congr 1
    funext x y
    simp only [hkS, commKernel]
    split_ifs with hxy
    · rfl
    · rw [sliceGrad_eq (le_of_lt hl) (sub_ne_zero.mpr hxy)]
      rfl
  show offDiagPairing (commKernel (periodicRieszGrad d s) v) X μ = _
  rw [key]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun l hl => ?_
  simp only [bexp]
  rw [hcongr l hl]

/-- **S1.4 (periodisation of the Yukawa profile).**  For `l > 0` and `y ∈ (-1/2,1/2]^d`, `y ≠ 0`:
`𝒢_l(y) + 1/l = ∑_{m ∈ ℤ^d} Γ_l(|y - m|)` (the Poisson-summed heat kernel,
`KernelAux.theta_images`, then `∫_0^∞ e^{-lt} (heat kernel) dt = Γ_l`, Tonelli on positive terms). -/
theorem sliceGfull_periodization (hl : 0 < l) {y : Fin d → ℝ} (hy : y ∈ KernelAux.Box d) (hy0 : y ≠ 0) :
    sliceGfull d l (KernelAux.boxPt y) =
      ∑' m : Lattice d, yukawa d l ‖(WithLp.toLp 2 (fun i => y i - (m i : ℝ)) : Euc d)‖ := by
  have h := SliceAux.periodization_aux hl hy hy0
  unfold sliceGfull sliceG
  rw [add_comm]
  exact h

/-- **S1.5 (profile facts).**  `Γ_l` is positive, strictly decreasing and smooth on `(0,∞)`, solves
`(r^{d-1} Γ')' = l r^{d-1} Γ` there, and has the Newton flux `-r^{d-1} Γ'(r) → 1/|S^{d-1}|` as
`r → 0` (`|S^{d-1}| = 2π^{d/2}/Γ(d/2)`); the Gaussian integral makes all of this elementary
(`(∂_t - Δ) heat kernel = 0`, `∫_0^∞ e^{-lt} ∂_t p_t dt = l Γ_l` for `r > 0`). -/
theorem yukawa_ode (hd : 1 ≤ d) (hl : 0 < l) :
    (∀ r : ℝ, 0 < r → 0 < yukawa d l r) ∧
    (∀ r r' : ℝ, 0 < r → r < r' → yukawa d l r' < yukawa d l r) ∧
    (∀ r : ℝ, 0 < r → deriv (fun r => r ^ (d - 1) * deriv (yukawa d l) r) r =
        l * r ^ (d - 1) * yukawa d l r) ∧
    Tendsto (fun r : ℝ => -(r ^ (d - 1) * deriv (yukawa d l) r)) (𝓝[>] 0)
      (𝓝 (Real.Gamma ((d : ℝ) / 2) / (2 * Real.pi ^ ((d : ℝ) / 2)))) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hd1 : 1 ≤ n + 1 := hd
  have hder : ∀ r : ℝ, 0 < r → deriv (yukawa (n + 1) l) r =
      ∫ t in Ioi (0 : ℝ), -(r / (2 * t)) * (Real.exp (-l * t) * SliceAux.gprof (n + 1) t r) :=
    fun r hr => (SliceAux.hasDerivAt_yk hd1 hl hr).2.deriv
  refine ⟨fun r hr => SliceAux.yk_pos hd1 hl hr, fun r r' hr hrr' => ?_, fun r hr => ?_, ?_⟩
  · exact SliceAux.yk_strictAnti hd1 hl hr (lt_trans hr hrr') hrr'
  · have hfl : ∀ r' : ℝ, 0 < r' → r' ^ n * deriv (yukawa (n + 1) l) r' =
        ∫ t in Ioi (0 : ℝ), r' ^ n * (-(r' / (2 * t)) * (Real.exp (-l * t) *
          SliceAux.gprof (n + 1) t r')) := by
      intro r' hr'
      rw [hder r' hr', ← integral_const_mul]
    have hD := (SliceAux.hasDerivAt_flux n hl hr).2
    have heq : (fun r' : ℝ => r' ^ n * deriv (yukawa (n + 1) l) r') =ᶠ[𝓝 r]
        fun r' => ∫ t in Ioi (0 : ℝ), r' ^ n * (-(r' / (2 * t)) * (Real.exp (-l * t) *
          SliceAux.gprof (n + 1) t r')) := by
      filter_upwards [Ioi_mem_nhds hr] with r' hr'
      exact hfl r' hr'
    have hD' := hD.congr_of_eventuallyEq heq
    simp only [Nat.add_sub_cancel]
    rw [hD'.deriv, SliceAux.flux_identity n hl hr]
    rfl
  · simp only [Nat.add_sub_cancel]
    refine (SliceAux.flux_limit n hl).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) < r := hr
    rw [hder r hr', ← integral_const_mul, ← integral_neg]
    congr 1
    funext t
    ring

/-- **S1.6 (Euclidean Stieltjes identity: the profile of the truncation).**  For `d-2 < s < d`:
`∫_0^∞ l^{-β} (Γ_l(r) - Γ_l(η)) dl = c' (selfScale(r) - selfScale(η))` for all `r, η > 0`, with
the same `c'` for all `r, η` (Mellin scaling `Γ_l(r) = l^{(d-2)/2} Γ_1(√l r)`; for `s > 0` the two
terms converge separately and give `c' (r^{-s} - η^{-s})`, for `s = 0` (`d = 1`) only the
difference converges and gives `c' log(η/r)`).  This is the identity `g_η = min(g, g(η))` of
`[RS] (2.5)` seen at `z = 0`. -/
theorem yukawa_stieltjes (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ r η : ℝ, 0 < r → 0 < η →
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * (yukawa d l r - yukawa d l η) =
        c' * (selfScale d s r - selfScale d s η) := by
  obtain ⟨c', hc', h⟩ := SliceAux.yuk_stieltjes_aux hd hs0 hs hsd
  refine ⟨c', hc', fun r η hr hη => ?_⟩
  have := h r η hr hη
  unfold selfScale
  split_ifs at this ⊢ with h0
  · rw [show -Real.log r - -Real.log η = -Real.log r + Real.log η by ring]
    exact this
  · exact this

end HRS.Commutator
