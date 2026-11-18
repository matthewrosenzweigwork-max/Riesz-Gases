import HRS.Main.A8PAux3
import HRS.Sections.DynConvAux1

/-!
# Packet A8P, part 4: the transport seminorm `‖Mᵀ∇ψ‖_*` of an `H^{m_*}` test (torus HLS)

`a8p_transport_bound`: for `ψ ∈ C² ∩ H^{m_*}` and any matrix with `|M_{ij}| ≤ MB`,
`HasTransportBound d s (Mᵀ∇ψ) (c_T ‖ψ‖_{H^{m_*}})` with `c_T = c_T(d, MB)`.
The fractional part is the Hardy-Littlewood-Sobolev embedding on the torus (`hls_T`), as in `dynconv_fracDeriv_scalar`,
but with an `H^{m_*}` hypothesis (`m_* ≥ d/2 + 5/2`) instead of a `C^n` one.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

/-- Uniform operator bound for matrices with bounded entries. -/
theorem a8p_matVec_bound {MB : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : PDE.MatBound MB M) (v : Euc d) :
    ‖Torus.matVec M v‖ ≤ ((d : ℝ) * d * MB) * ‖v‖ := by
  have hMB : 0 ≤ MB ∨ d = 0 := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exact Or.inr h
    · exact Or.inl ((abs_nonneg _).trans (hM ⟨0, h⟩ ⟨0, h⟩))
  have hcoord : ∀ i, (Torus.matVec M v) i = ∑ j, M i j * v j := by
    intro i
    simp [Torus.matVec, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  have h1 : ‖Torus.matVec M v‖ ≤ ∑ i, |(Torus.matVec M v) i| := by
    have := HRS.Commutator.Whole.cmxHLS_norm_toLp_le (d := d) (fun i => (Torus.matVec M v) i)
    simpa using this
  refine h1.trans ?_
  have h2 : ∀ i, |(Torus.matVec M v) i| ≤ ∑ _j : Fin d, MB * ‖v‖ := by
    intro i
    rw [hcoord i]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (hM i j) (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v j)
      (abs_nonneg _) ((abs_nonneg _).trans (hM i j))
  refine (Finset.sum_le_sum fun i _ => h2 i).trans (le_of_eq ?_)
  simp [Finset.sum_const]
  ring


/-- Scalar fractional derivative of order `(d+1)/2` in `L^{2d/(d-1)}` from an `ℓ²` bound on `(2π|k|)^{(d+2)/2} v̂(k)`
(`d ≥ 3`; Hardy-Littlewood-Sobolev on the torus). -/
theorem a8p_fracDeriv_scalar (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : Torus d → ℝ) (A : ℝ), 0 ≤ A → Integrable v →
      (Summable fun k : Lattice d => ((2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2)) *
        ‖Torus.fcoef v k‖ ^ 2) →
      (∑' k : Lattice d, ((2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2)) * ‖Torus.fcoef v k‖ ^ 2 ≤ A ^ 2) →
      ∃ w : Torus d → ℝ, MemLp w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ∧
        (∀ k : Lattice d, Torus.fcoef w k =
          (((2 * Real.pi * Lattice.enorm k) ^ (((d : ℝ) + 1) / 2) : ℝ) : ℂ) * Torus.fcoef v k) ∧
        eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ≤ ENNReal.ofReal (C * A) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hp1, hpq, hqt, hσ, hrel⟩ := dynconv_hls_exps hd
  obtain ⟨Ch, hChpos, hCh⟩ := HRS.Commutator.TorusNote.hls_T hd1 (1 / 2 : ℝ) 2
    (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) hp1 hpq hqt hσ hrel
  refine ⟨Ch, hChpos.le, fun v A hA hv hsum hbound => ?_⟩
  set c : PDE.Coeff d := fun k =>
    (((2 * Real.pi * Lattice.enorm k) ^ (((d : ℝ) + 2) / 2) : ℝ) : ℂ) * Torus.fcoef v k with hc
  have hcsq : ∀ k, ‖c k‖ ^ 2 = ((2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2)) * ‖Torus.fcoef v k‖ ^ 2 := by
    intro k
    have hx : 0 ≤ 2 * Real.pi * Lattice.enorm k := by
      have : 0 ≤ Lattice.enorm k := norm_nonneg _
      positivity
    simp only [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    rw [abs_of_nonneg (Real.rpow_nonneg hx _), ← Real.rpow_natCast, ← Real.rpow_mul hx]
    congr 2
    push_cast; ring
  have hsumc : Summable fun k => ‖c k‖ ^ 2 := hsum.congr fun k => (hcsq k).symm
  have hc0 : PDE.MemHs 0 c := (PDE.memHs_zero_iff c).2 hsumc
  have hreal : PDE.IsRealCoeff c := by
    intro k
    simp only [hc]
    rw [map_mul, Complex.conj_ofReal, HRS.enorm_neg, gfb2_fcoef_neg v k]
  obtain ⟨f, hf2, hfc, hfn⟩ := dynconv_exists_real_L2 c hc0 hreal
  have hf0 : Torus.fcoef f 0 = 0 := by
    rw [hfc 0]
    have : Lattice.enorm (0 : Lattice d) = 0 := by
      unfold Lattice.enorm
      have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
      rw [this, norm_zero]
    simp [hc, this, Real.zero_rpow (show ((d : ℝ) + 2) / 2 ≠ 0 by positivity)]
  obtain ⟨h, hh2, hh0, hhk, hhn⟩ := hCh f hf2 hf0
  refine ⟨h, hh2, fun k => ?_, ?_⟩
  · by_cases hk : k = 0
    · subst hk
      have : Lattice.enorm (0 : Lattice d) = 0 := by
        unfold Lattice.enorm
        have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
        rw [this, norm_zero]
      rw [hh0]
      simp [this, Real.zero_rpow (show ((d : ℝ) + 1) / 2 ≠ 0 by positivity)]
    · rw [hhk k hk, hfc k]
      simp only [hc]
      have hten : 0 < 2 * Real.pi * Lattice.enorm k := by
        have := HRS.one_le_enorm k hk
        positivity
      rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hten]
      congr 3
      ring
  · refine hhn.trans ?_
    have hS' : Real.sqrt (∑' k, ‖c k‖ ^ 2) ≤ A := by
      refine Real.sqrt_le_iff.2 ⟨hA, ?_⟩
      calc ∑' k, ‖c k‖ ^ 2 = ∑' k : Lattice d, ((2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2)) *
            ‖Torus.fcoef v k‖ ^ 2 := tsum_congr hcsq
        _ ≤ A ^ 2 := hbound
    calc ENNReal.ofReal Ch * eLpNorm f 2 volume
        ≤ ENNReal.ofReal Ch * ENNReal.ofReal (Real.sqrt (∑' k, ‖c k‖ ^ 2)) :=
          mul_le_mul_right hfn _
      _ ≤ ENNReal.ofReal Ch * ENNReal.ofReal A :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal hS') _
      _ = ENNReal.ofReal (Ch * A) := by rw [← ENNReal.ofReal_mul hChpos.le]


/-- The `ℓ²` bound on `(2π|k|)^{(d+2)/2} · \widehat{∂_c ψ}(k)` by the `H^m` norm. -/
theorem a8p_dir_sum {m : ℝ} (hm : (d : ℝ) + 4 ≤ 2 * m) {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ)
    (hMem : MemSobolev m ψ) (c : Euc d) :
    (Summable fun k : Lattice d => ((2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2)) *
        ‖Torus.fcoef (KernelGrad.dirTor ψ c) k‖ ^ 2) ∧
    ∑' k : Lattice d, ((2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2)) *
        ‖Torus.fcoef (KernelGrad.dirTor ψ c) k‖ ^ 2 ≤ (‖c‖ * sobolevNorm m ψ) ^ 2 := by
  classical
  have hint : Integrable ψ := hMem.1.integrable one_le_two
  obtain ⟨hs2, he⟩ := Torus.weighted_fcoef_sq (2 * m) hint hMem.2
  set F : Lattice d → ℝ := fun k => ((2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2)) *
    ‖Torus.fcoef (KernelGrad.dirTor ψ c) k‖ ^ 2 with hF
  have hF0 : F 0 = 0 := by
    have : Lattice.enorm (0 : Lattice d) = 0 := by
      unfold Lattice.enorm
      have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
      rw [this, norm_zero]
    simp [hF, this, Real.zero_rpow (show (d : ℝ) + 2 ≠ 0 by positivity)]
  have hFle : ∀ k : NonzeroLattice d, F k.1 ≤ ‖c‖ ^ 2 * (Lattice.jp k.1 ^ (2 * m) * ‖Torus.fcoef ψ k.1‖ ^ 2) := by
    intro k
    set E := Lattice.enorm k.1 with hE
    set J := Lattice.jp k.1 with hJ
    have hE0 : 0 ≤ E := norm_nonneg _
    have hA0 : 0 ≤ 2 * Real.pi * E := by positivity
    have hAJ : 2 * Real.pi * E ≤ J := Torus.two_pi_enorm_le_jp k.1
    have hJ1 : 1 ≤ J := Torus.jp_ge_one k.1
    have hcoef : ‖Torus.fcoef (KernelGrad.dirTor ψ c) k.1‖ =
        2 * Real.pi * |Lattice.dot k.1 c| * ‖Torus.fcoef ψ k.1‖ := by
      rw [gfb2_fcoef_dirTor hψ c k.1]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, Complex.norm_ofNat, mul_one]
      rw [abs_of_pos Real.pi_pos]
    have hdot := Torus.abs_dot_le k.1 c
    have h1 : ‖Torus.fcoef (KernelGrad.dirTor ψ c) k.1‖ ≤
        (2 * Real.pi * E) * ‖c‖ * ‖Torus.fcoef ψ k.1‖ := by
      rw [hcoef]
      calc 2 * Real.pi * |Lattice.dot k.1 c| * ‖Torus.fcoef ψ k.1‖
          ≤ 2 * Real.pi * (E * ‖c‖) * ‖Torus.fcoef ψ k.1‖ := by gcongr
        _ = _ := by ring
    have h2 : ‖Torus.fcoef (KernelGrad.dirTor ψ c) k.1‖ ^ 2 ≤
        ((2 * Real.pi * E) * ‖c‖ * ‖Torus.fcoef ψ k.1‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (2 * Real.pi * E) ^ ((d : ℝ) + 2) * (2 * Real.pi * E) ^ 2 ≤ J ^ (2 * m) := by
      have e1 : (2 * Real.pi * E) ^ ((d : ℝ) + 2) * (2 * Real.pi * E) ^ 2 =
          (2 * Real.pi * E) ^ ((d : ℝ) + 4) := by
        rw [← Real.rpow_natCast (2 * Real.pi * E) 2, ← Real.rpow_add' hA0 (by positivity)]
        congr 1; push_cast; ring
      rw [e1]
      calc (2 * Real.pi * E) ^ ((d : ℝ) + 4) ≤ J ^ ((d : ℝ) + 4) :=
            Real.rpow_le_rpow hA0 hAJ (by positivity)
        _ ≤ J ^ (2 * m) := Real.rpow_le_rpow_of_exponent_le hJ1 hm
    calc F k.1 = (2 * Real.pi * E) ^ ((d : ℝ) + 2) * ‖Torus.fcoef (KernelGrad.dirTor ψ c) k.1‖ ^ 2 := rfl
      _ ≤ (2 * Real.pi * E) ^ ((d : ℝ) + 2) * ((2 * Real.pi * E) * ‖c‖ * ‖Torus.fcoef ψ k.1‖) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hA0 _)
      _ = ((2 * Real.pi * E) ^ ((d : ℝ) + 2) * (2 * Real.pi * E) ^ 2) * (‖c‖ ^ 2 * ‖Torus.fcoef ψ k.1‖ ^ 2) := by
          ring
      _ ≤ J ^ (2 * m) * (‖c‖ ^ 2 * ‖Torus.fcoef ψ k.1‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = _ := by ring
  have hsumG : Summable fun k : NonzeroLattice d =>
      ‖c‖ ^ 2 * (Lattice.jp k.1 ^ (2 * m) * ‖Torus.fcoef ψ k.1‖ ^ 2) := hs2.mul_left _
  have hsF : Summable fun k : NonzeroLattice d => F k.1 :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (by
      have : 0 ≤ Lattice.enorm k.1 := norm_nonneg _
      positivity) _) (sq_nonneg _)) hFle hsumG
  refine ⟨(Torus.summable_lattice_iff F).2 hsF, ?_⟩
  rw [Torus.tsum_lattice F ((Torus.summable_lattice_iff F).2 hsF), hF0, zero_add]
  calc ∑' k : NonzeroLattice d, F k.1
      ≤ ∑' k : NonzeroLattice d, ‖c‖ ^ 2 * (Lattice.jp k.1 ^ (2 * m) * ‖Torus.fcoef ψ k.1‖ ^ 2) :=
        hsF.tsum_le_tsum hFle hsumG
    _ = ‖c‖ ^ 2 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * ‖Torus.fcoef ψ k.1‖ ^ 2 := by
        rw [tsum_mul_left]
    _ = ‖c‖ ^ 2 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff ψ k ^ 2 := by
        rw [he]
    _ ≤ ‖c‖ ^ 2 * sobolevNorm m ψ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        unfold sobolevNorm
        rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (tsum_nonneg fun k => mul_nonneg
          (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)))]
        nlinarith [sq_nonneg (Torus.mean ψ)]
    _ = _ := by ring


theorem a8p_mStar_gt (d : ℕ) : (d : ℝ) / 2 + 2 < (PDE.mStar d : ℝ) := by
  unfold PDE.mStar
  push_cast
  have := Nat.lt_floor_add_one ((d : ℝ) / 2)
  linarith

/-- The transport seminorm `‖Mᵀ∇ψ‖_*` of an `H^{m_*}` test, uniformly for `|M_{ij}| ≤ MB`. -/
theorem a8p_transport_bound (hd : 1 ≤ d) (MB s : ℝ) (hs0 : 0 ≤ s) :
    ∃ cT : ℝ, 0 ≤ cT ∧ ∀ (M : Matrix (Fin d) (Fin d) ℝ), PDE.MatBound MB M →
      ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → MemSobolev (PDE.mStar d : ℝ) ψ →
        HasTransportBound d s (gfb2_v M ψ) (cT * sobolevNorm (PDE.mStar d : ℝ) ψ) := by
  classical
  have hmst := a8p_mStar_gt d
  have hm2 : (d : ℝ) + 4 ≤ 2 * (PDE.mStar d : ℝ) := by linarith
  have hmi : (d : ℝ) / 2 + ((2 : ℕ) : ℝ) < (PDE.mStar d : ℝ) := by push_cast; linarith
  obtain ⟨Cemb, hCemb⟩ := cbNorm_le_sobolevNorm 2 (PDE.mStar d : ℝ) hmi
  obtain ⟨Cs, hCs0, hCs⟩ : ∃ Cs : ℝ, 0 ≤ Cs ∧ (3 ≤ d → ∀ (v : Torus d → ℝ) (A : ℝ), 0 ≤ A → Integrable v →
      (Summable fun k : Lattice d => ((2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2)) *
        ‖Torus.fcoef v k‖ ^ 2) →
      (∑' k : Lattice d, ((2 * Real.pi * Lattice.enorm k) ^ ((d : ℝ) + 2)) * ‖Torus.fcoef v k‖ ^ 2 ≤ A ^ 2) →
      ∃ w : Torus d → ℝ, MemLp w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ∧
        (∀ k : Lattice d, Torus.fcoef w k =
          (((2 * Real.pi * Lattice.enorm k) ^ (((d : ℝ) + 1) / 2) : ℝ) : ℂ) * Torus.fcoef v k) ∧
        eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ≤ ENNReal.ofReal (Cs * A)) := by
    by_cases hd3 : 3 ≤ d
    · obtain ⟨C, hC0, hC⟩ := a8p_fracDeriv_scalar hd3
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hd3⟩
  set cM : ℝ := (d : ℝ) * d * |MB| with hcM
  have hcM0 : 0 ≤ cM := by positivity
  refine ⟨cM * max Cemb 0 + d * Cs * cM, by positivity, fun M hM ψ hψ hMem => ?_⟩
  have hMB' : PDE.MatBound |MB| M := fun i j => (hM i j).trans (le_abs_self _)
  have hcMv : ∀ v : Euc d, ‖Torus.matVec M v‖ ≤ cM * ‖v‖ := fun v => a8p_matVec_bound hMB' v
  have hsob0 : 0 ≤ sobolevNorm (PDE.mStar d : ℝ) ψ := Real.sqrt_nonneg _
  have hcb : Torus.cbNorm 2 ψ ≤ max Cemb 0 * sobolevNorm (PDE.mStar d : ℝ) ψ :=
    (hCemb ψ hMem hψ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hsob0)
  have hcb0 := gfb2_cbNorm_nonneg ψ 2
  refine ⟨cM * Torus.cbNorm 2 ψ, d * Cs * (cM * sobolevNorm (PDE.mStar d : ℝ) ψ),
    mul_nonneg hcM0 hcb0, by positivity, gfb2_lipschitzVF hψ M hcM0 hcMv, fun hs => ?_, ?_⟩
  · have hd3 : 3 ≤ d := by
      by_contra h
      push Not at h
      have : (d : ℝ) ≤ 2 := by exact_mod_cast (by omega : d ≤ 2)
      linarith
    have hex : ∀ j : Fin d, ∃ w : Torus d → ℝ,
        MemLp w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ∧
          (∀ k : Lattice d, Torus.fcoef w k =
            (((2 * Real.pi * Lattice.enorm k) ^ (((d : ℝ) + 1) / 2) : ℝ) : ℂ) *
              Torus.fcoef (fun x => gfb2_v M ψ x j) k) ∧
          eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume ≤
            ENNReal.ofReal (Cs * (cM * sobolevNorm (PDE.mStar d : ℝ) ψ)) := fun j => by
      set cj : Euc d := Torus.matVec M (EuclideanSpace.single j (1 : ℝ)) with hcj
      have hcjn : ‖cj‖ ≤ cM := by
        have := hcMv (EuclideanSpace.single j (1 : ℝ))
        simpa using this
      obtain ⟨hsm, hbd⟩ := a8p_dir_sum hm2 hψ hMem cj
      have hA0 : 0 ≤ cM * sobolevNorm (PDE.mStar d : ℝ) ψ := mul_nonneg hcM0 hsob0
      have hAle : ‖cj‖ * sobolevNorm (PDE.mStar d : ℝ) ψ ≤ cM * sobolevNorm (PDE.mStar d : ℝ) ψ :=
        mul_le_mul_of_nonneg_right hcjn hsob0
      have hsq : (‖cj‖ * sobolevNorm (PDE.mStar d : ℝ) ψ) ^ 2 ≤ (cM * sobolevNorm (PDE.mStar d : ℝ) ψ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hAle 2
      have hfun : (fun x => gfb2_v M ψ x j) = KernelGrad.dirTor ψ cj := gfb2_v_apply_eq M ψ j
      have hvint : Integrable (KernelGrad.dirTor ψ cj) := by
        have hcont : Continuous (KernelGrad.dirTor ψ cj) := by
          have h1 : Torus.IsCk 1 (KernelGrad.dirTor ψ cj) := by
            have h2' : Torus.IsCk ((1 + 1 : ℕ) : WithTop ℕ∞) ψ := by exact_mod_cast hψ
            exact_mod_cast KernelGrad.isCk_dirTor h2' cj
          exact Q54c.isCk_continuous h1
        exact hcont.integrable_of_hasCompactSupport (by simpa using HasCompactSupport.of_compactSpace _)
      obtain ⟨w, hw, hwf, hwn⟩ := hCs hd3 (KernelGrad.dirTor ψ cj) _ hA0 hvint hsm (hbd.trans hsq)
      exact ⟨w, hw, fun k => by rw [hfun]; exact hwf k, hwn⟩
    choose h hmem hcoef hhn using hex
    obtain ⟨hp1, hpq, hqt, -, -⟩ := dynconv_hls_exps hd3
    refine ⟨fun x => WithLp.toLp 2 (fun j => h j x), ?_, ?_⟩
    · intro j k
      have hfun : (fun x => (WithLp.toLp 2 (fun j => h j x) : Euc d) j) = h j := by
        funext x; simp
      rw [hfun]
      exact hcoef j k
    · have hwm : AEStronglyMeasurable (fun x => (WithLp.toLp 2 (fun j => h j x) : Euc d)) volume := by
        refine AEMeasurable.aestronglyMeasurable ?_
        exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp_aemeasurable
          (aemeasurable_pi_iff.2 fun j => (hmem j).aemeasurable)
      have hle : ∀ x, ‖(WithLp.toLp 2 (fun j => h j x) : Euc d)‖ ≤
          ‖(∑ j : Fin d, fun x => ‖h j x‖) x‖ := by
        intro x
        have h1 := HRS.Commutator.Whole.cmxHLS_norm_toLp_le (d := d) (fun j => h j x)
        refine h1.trans (le_of_eq ?_)
        rw [Finset.sum_apply, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)]
        simp [Real.norm_eq_abs]
      calc eLpNorm (fun x => (WithLp.toLp 2 (fun j => h j x) : Euc d))
            (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume
          ≤ eLpNorm (∑ j : Fin d, fun x => ‖h j x‖) (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume :=
            eLpNorm_mono hwm hle
        _ ≤ ∑ j : Fin d, eLpNorm (fun x => ‖h j x‖) (ENNReal.ofReal (2 * d / ((d : ℝ) - 1))) volume :=
            eLpNorm_sum_le (hp1.trans hpq).le
        _ ≤ ∑ _j : Fin d, ENNReal.ofReal (Cs * (cM * sobolevNorm (PDE.mStar d : ℝ) ψ)) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [eLpNorm_norm _ (hmem j).aestronglyMeasurable]
            exact hhn j
        _ = ENNReal.ofReal (d * (Cs * (cM * sobolevNorm (PDE.mStar d : ℝ) ψ))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal (d * Cs * (cM * sobolevNorm (PDE.mStar d : ℝ) ψ)) := by
            congr 1; ring
  · split_ifs with hs
    · nlinarith [mul_le_mul_of_nonneg_left hcb hcM0, mul_nonneg hcM0 hsob0, mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hCs0) (mul_nonneg hcM0 hsob0)]
    · nlinarith [mul_le_mul_of_nonneg_left hcb hcM0, mul_nonneg hcM0 hsob0, mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hCs0) (mul_nonneg hcM0 hsob0)]

end HRS.Main.A8P
