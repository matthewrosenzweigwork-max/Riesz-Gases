import HRS.MS.WadAux154

/-!
# S8.3, packet S8G-6: weighted decay of all jets of the tensor pairing

`s8g_Phi_decay`: for `M > 0`, `hT : S8gOp M T (n+1) A`, a section `s` and a functional `m`, the pair function `Φ_s = s8g_Phi hT hs m`
satisfies `S8gPD M n Φ_s` (smooth, all jets of order `≤ n` weighted-decaying at infinity).  Proof: the weighted jet sup-norm of
`Φ_s - Φ_{s'}` is `≲ sup‖s - s'‖` (`s8g_Phi_bound`, linearity in `s`), separated sections `s'` give finite sums of products of one-body
functions (`s8g_pd_mul`), and `s8g_sec_approx` approximates `s`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8g_dec_mono {M : ℝ} {n m : ℕ} (h : n ≤ m) {u : Euc d → ℝ} (hu : S8gDec M m u) : S8gDec M n u :=
  ⟨hu.1.of_le (by exact_mod_cast h), fun i hi => hu.2 i (hi.trans h)⟩

theorem s8g_sum_apply {ι : Type} (t : Finset ι) (f : ι → S8gV d) (x : Euc d) :
    (∑ i ∈ t, f i) x = ∑ i ∈ t, f i x := by
  classical
  induction t using Finset.induction_on with
  | empty => rfl
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, s8g_add_apply, ih]

/-- The separated section `x' ↦ Σ_i φ_i(x') b_i`. -/
def s8g_sepSec {ι : Type} [Fintype ι] (φ b : ι → S8gV d) (x' : Euc d) : S8gV d := ∑ i, φ i x' • b i

theorem s8g_sepSec_sec {ι : Type} [Fintype ι] (φ b : ι → S8gV d) :
    S8gSec (s8g_sepSec φ b) (∑ i, ‖φ i‖ * ‖b i‖) := by
  refine ⟨?_, fun x' => ?_, ?_⟩
  · exact continuous_finset_sum _ fun i _ => ((s8g_cont (φ i)).smul continuous_const)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using s8g_norm_apply_le (φ i) x') (norm_nonneg _)
  · have : Tendsto (fun x' => ∑ i, |φ i x'| * ‖b i‖) (cocompact (Euc d)) (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset ι) (fun i _ => by
        have h0 := (s8g_zero_at_infty (φ i)).abs.mul_const ‖b i‖
        simpa using h0)
      simpa using this
    refine squeeze_zero (fun x' => norm_nonneg _) (fun x' => ?_) this
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]

theorem s8g_psi_sep {ι : Type} [Fintype ι] (φ b : ι → S8gV d) (ξ : S8gV d →L[ℝ] ℝ) :
    s8g_psi (s8g_sepSec_sec φ b) ξ = ∑ i, ξ (b i) • φ i := by
  refine s8g_ext fun x' => ?_
  rw [s8g_psi_apply, s8g_sum_apply]
  simp only [s8g_sepSec, map_sum, map_smul, s8g_smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem s8g_Phi_sep {M : ℝ} {T : (Euc d → ℝ) → Euc d → ℝ} {J : ℕ} {A : ℝ} (hT : S8gOp M T J A) {ι : Type}
    [Fintype ι] (φ b : ι → S8gV d) (m : S8gV d →L[ℝ] ℝ) (z : Euc d × Euc d) :
    s8g_Phi hT (s8g_sepSec_sec φ b) m z =
      ∑ i, ((s8g_ell hT z.1 + m) (φ i)) * (s8g_ell hT z.2 (b i)) := by
  unfold s8g_Phi
  rw [s8g_psi_sep]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem s8g_Phi_sub {M : ℝ} {T : (Euc d → ℝ) → Euc d → ℝ} {J : ℕ} {A : ℝ} (hT : S8gOp M T J A)
    {s s' : Euc d → S8gV d} {N0 N1 N2 : ℝ} (hs : S8gSec s N0) (hs' : S8gSec s' N1)
    (hss' : S8gSec (fun x' => s x' - s' x') N2) (m : S8gV d →L[ℝ] ℝ) (z : Euc d × Euc d) :
    s8g_Phi hT hss' m z = s8g_Phi hT hs m z - s8g_Phi hT hs' m z := by
  unfold s8g_Phi
  rw [← map_sub]
  congr 1
  refine s8g_ext fun x' => ?_
  simp [s8g_psi_apply]
  rfl

theorem s8g_Phi_decay {M : ℝ} (hM : 0 < M) {T : (Euc d → ℝ) → Euc d → ℝ} {n : ℕ} {A : ℝ}
    (hT : S8gOp M T (n + 1) A) {s : Euc d → S8gV d} {N0 : ℝ} (hs : S8gSec s N0) (m : S8gV d →L[ℝ] ℝ) :
    S8gPD M n (s8g_Phi hT hs m) := by
  classical
  refine s8g_pd_of_approx (s8g_Phi_contDiff hT hs m) fun ε hε => ?_
  set c : ℝ := ((d : ℝ) + 1) ^ (n + 1) with hc
  have hA := hT.nonneg
  have hc0 : 0 ≤ c := by positivity
  set Kc : ℝ := 2 ^ n * ((c * A + ‖m‖) * (c * A)) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set ε' : ℝ := ε / (Kc + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨ι, hι, φ, b, hφb⟩ := s8g_sec_approx hs.cont hs.decay hε'0
  have hsec' := s8g_sepSec_sec φ b
  have hdiff : S8gSec (fun x' => s x' - s8g_sepSec φ b x') ε' := by
    refine ⟨hs.cont.sub hsec'.cont, hφb, ?_⟩
    have := hs.decay.add hsec'.decay
    rw [add_zero] at this
    exact squeeze_zero (fun x' => norm_nonneg _) (fun x' => norm_sub_le _ _) this
  refine ⟨s8g_Phi hT hsec' m, ?_, fun k hk z => ?_⟩
  · -- the separated pairing is a finite sum of products of one-body functions
    have hfun : s8g_Phi hT hsec' m = fun z => ∑ i, (fun x => (s8g_ell hT x + m) (φ i)) z.1 *
        (fun y => s8g_ell hT y (b i)) z.2 := funext fun z => s8g_Phi_sep hT φ b m z
    rw [hfun]
    refine s8g_pd_sum _ fun i _ => s8g_pd_mul (u := fun x => (s8g_ell hT x + m) (φ i))
      (v := fun y => s8g_ell hT y (b i)) ?_ ?_
    · have h1 : S8gDec M n (fun x => T (s8g_ι M (φ i)) x) :=
        s8g_dec_mono (Nat.le_succ n) (s8g_dec_of_memCMj (hT.mem _ (s8g_ι_memCM M (φ i))))
      have := s8g_dec_add_const hM h1 (m (φ i))
      exact this
    · exact s8g_dec_mono (Nat.le_succ n) (s8g_dec_of_memCMj (hT.mem _ (s8g_ι_memCM M (b i))))
  · have hk' : (k : WithTop ℕ∞) ≤ n := by exact_mod_cast hk
    have hn : (n : WithTop ℕ∞) ≤ n := le_rfl
    have hsub : s8g_Phi hT hdiff m = fun z => s8g_Phi hT hs m z - s8g_Phi hT hsec' m z :=
      funext fun z => s8g_Phi_sub hT hs hsec' hdiff m z
    have e : iteratedFDeriv ℝ k (s8g_Phi hT hdiff m) z =
        iteratedFDeriv ℝ k (s8g_Phi hT hs m) z - iteratedFDeriv ℝ k (s8g_Phi hT hsec' m) z := by
      rw [hsub]
      have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := k) (x := z)
        ((s8g_Phi_contDiff hT hs m).of_le hk').contDiffAt ((s8g_Phi_contDiff hT hsec' m).of_le hk').contDiffAt
      exact this
    rw [← e]
    have hb := s8g_Phi_bound hM.le hT hdiff m hk z
    refine hb.trans ?_
    have hjj : 0 ≤ jbracket z.1 ^ M * jbracket z.2 ^ M :=
      mul_nonneg (Real.rpow_nonneg (s83_jb_pos z.1).le _) (Real.rpow_nonneg (s83_jb_pos z.2).le _)
    refine mul_le_mul_of_nonneg_right ?_ hjj
    have h2k : (2 : ℝ) ^ k ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hk
    have hq : 0 ≤ (c * A + ‖m‖) * ε' * (c * A) := by positivity
    calc (2 : ℝ) ^ k * ((c * A + ‖m‖) * ε' * (c * A)) ≤ 2 ^ n * ((c * A + ‖m‖) * ε' * (c * A)) :=
          mul_le_mul_of_nonneg_right h2k hq
      _ = Kc * ε' := by rw [hKc]; ring
      _ = Kc * ε / (Kc + 1) := by rw [hε']; ring
      _ ≤ ε := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith

end HRS.MS.Wad
