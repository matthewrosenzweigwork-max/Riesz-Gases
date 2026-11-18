import HRS.MS.FeatDecAux9
import HRS.Whole.CriticalNoise

/-!
# S8.5 `feature_decay`, part 10 (S85 packet): weighted bounds of the `𝒦`-valued feature

* `s85_mulw`: multiplication by `⟨x⟩^p` preserves bounded `C^n` classes of weighted symbols;
* `s85_unweight`: the converse Leibniz bound for `𝒦`-valued maps;
* `s85_features_weighted`: from coordinatewise weighted bounds (`‖D^j u_α(x)‖ ≤ c_α ⟨x⟩^{-(p+j)}`) the feature
  `Γ_{r,a} = gradFeature` is genuinely in `𝒦` (`IsKFeature`), `C^n`, and `⟨x⟩^p ‖D^jΓ(x)‖ ≤ C_f`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S85

open HRS HRS.Whole HRS.MS.Go

variable {d : ℕ}

theorem s85_jb_pos (x : Euc d) : 0 < jbracket x := u2_jb_pos x

theorem s85_jb_one_le (x : Euc d) : 1 ≤ jbracket x := HRS.MS.Adj.ad1_one_le_jb x

theorem s85_mulw (n : ℕ) (p : ℝ) : ∃ Kw : ℝ, 0 ≤ Kw ∧ ∀ (u : Euc d → ℝ) (A : ℝ), 0 ≤ A →
    ContDiff ℝ (n : WithTop ℕ∞) u →
    (∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤ A * jbracket x ^ (-(p + (j : ℝ)))) →
    ContDiff ℝ (n : WithTop ℕ∞) (fun x => jbracket x ^ p * u x) ∧
    ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun x => jbracket x ^ p * u x) x‖ ≤ Kw * A := by
  have hsym := s85_jb_sym (d := d) n
  choose! Cw hCw0 hCw using fun l (hl : l ≤ n) => hsym l hl p
  set Kw : ℝ := ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Cw i with hKw
  have hCwn : ∀ i ∈ Finset.range (n + 1), 0 ≤ Cw i := fun i hi =>
    hCw0 i (by have := Finset.mem_range.1 hi; omega)
  have hKw0 : 0 ≤ Kw := Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun i hi =>
    mul_nonneg (by positivity) (hCwn i (Finset.mem_range.2 (by
      have := Finset.mem_range.1 hi; have := Finset.mem_range.1 hj; omega)))
  refine ⟨Kw, hKw0, fun u A hA hu hb => ⟨(s85_jbpow_contDiff p |>.of_le (by exact_mod_cast le_top)).mul hu,
    fun j hj x => ?_⟩⟩
  have hw : ContDiff ℝ (n : WithTop ℕ∞) (fun x : Euc d => jbracket x ^ p) :=
    (s85_jbpow_contDiff p).of_le (by exact_mod_cast le_top)
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := fun x : Euc d => jbracket x ^ p) (g := u)
    (N := (n : WithTop ℕ∞)) hw hu x (n := j) (by exact_mod_cast hj)
  refine hmul.trans ?_
  have hjb := s85_jb_pos x
  have hjb1 := s85_jb_one_le x
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun x : Euc d => jbracket x ^ p) x‖ *
        ‖iteratedFDeriv ℝ (j - i) u x‖ ≤ (j.choose i : ℝ) * Cw i * A := by
    intro i hi
    have hi' : i ≤ j := by have := Finset.mem_range.1 hi; omega
    have h1 := hCw i (by omega) x
    have h2 := hb (j - i) (by omega) x
    have hpe : jbracket x ^ (p - (i : ℝ)) * jbracket x ^ (-(p + ((j - i : ℕ) : ℝ))) ≤ 1 := by
      rw [← Real.rpow_add hjb]
      apply Real.rpow_le_one_of_one_le_of_nonpos hjb1
      have : ((j - i : ℕ) : ℝ) = (j : ℝ) - i := by rw [Nat.cast_sub hi']
      rw [this]
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have hC : 0 ≤ Cw i := hCw0 i (by omega)
    calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun x : Euc d => jbracket x ^ p) x‖ *
          ‖iteratedFDeriv ℝ (j - i) u x‖
        ≤ (j.choose i : ℝ) * (Cw i * jbracket x ^ (p - (i : ℝ))) *
            (A * jbracket x ^ (-(p + ((j - i : ℕ) : ℝ)))) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (norm_nonneg _)
            (by positivity)
      _ = (j.choose i : ℝ) * Cw i * A *
            (jbracket x ^ (p - (i : ℝ)) * jbracket x ^ (-(p + ((j - i : ℕ) : ℝ)))) := by ring
      _ ≤ (j.choose i : ℝ) * Cw i * A * 1 :=
          mul_le_mul_of_nonneg_left hpe (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hA
  have hjn : j ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have hcn : ∀ j' ∈ Finset.range (n + 1), 0 ≤ ∑ i ∈ Finset.range (j' + 1), (j'.choose i : ℝ) * Cw i :=
    fun j' hj' => Finset.sum_nonneg fun i hi => mul_nonneg (by positivity)
      (hCwn i (Finset.mem_range.2 (by
        have := Finset.mem_range.1 hi; have := Finset.mem_range.1 hj'; omega)))
  exact Finset.single_le_sum (f := fun j' => ∑ i ∈ Finset.range (j' + 1), (j'.choose i : ℝ) * Cw i)
    hcn hjn

theorem s85_unweight {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (p : ℝ) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ (G : Euc d → E) (B : ℝ), ContDiff ℝ (n : WithTop ℕ∞) G →
      (∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun x => jbracket x ^ p • G x) x‖ ≤ B) →
      ∀ j ≤ n, ∀ x, jbracket x ^ p * ‖iteratedFDeriv ℝ j G x‖ ≤ K' * B := by
  have hsym := s85_jb_sym (d := d) n
  choose! Cw hCw0 hCw using fun l (hl : l ≤ n) => hsym l hl (-p)
  set K' : ℝ := ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Cw i with hK'
  have hCwn : ∀ i ∈ Finset.range (n + 1), 0 ≤ Cw i := fun i hi =>
    hCw0 i (by have := Finset.mem_range.1 hi; omega)
  have hK'0 : 0 ≤ K' := Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun i hi =>
    mul_nonneg (by positivity) (hCwn i (Finset.mem_range.2 (by
      have := Finset.mem_range.1 hi; have := Finset.mem_range.1 hj; omega)))
  refine ⟨K', hK'0, fun G B hG hB j hj x => ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) x)
  have hw : ContDiff ℝ (n : WithTop ℕ∞) (fun x : Euc d => jbracket x ^ (-p)) :=
    (s85_jbpow_contDiff (-p)).of_le (by exact_mod_cast le_top)
  have hwG : ContDiff ℝ (n : WithTop ℕ∞) (fun x : Euc d => jbracket x ^ p • G x) :=
    ((s85_jbpow_contDiff p).of_le (by exact_mod_cast le_top)).smul hG
  have hGe : G = fun x => jbracket x ^ (-p) • (jbracket x ^ p • G x) := by
    funext y
    rw [smul_smul, ← Real.rpow_add (s85_jb_pos y)]
    simp
  have hsm := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (f := fun x : Euc d => jbracket x ^ (-p))
    (g := fun x => jbracket x ^ p • G x) (N := (n : WithTop ℕ∞)) hw hwG x (n := j)
    (by exact_mod_cast hj)
  rw [hGe]
  have hjb := s85_jb_pos x
  have hjb1 := s85_jb_one_le x
  have hterm : ∀ i ∈ Finset.range (j + 1),
      jbracket x ^ p * ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun x : Euc d => jbracket x ^ (-p)) x‖ *
        ‖iteratedFDeriv ℝ (j - i) (fun x => jbracket x ^ p • G x) x‖) ≤ (j.choose i : ℝ) * Cw i * B := by
    intro i hi
    have hi' : i ≤ j := by have := Finset.mem_range.1 hi; omega
    have h1 := hCw i (by omega) x
    have h2 := hB (j - i) (by omega) x
    have hpe : jbracket x ^ p * jbracket x ^ (-p - (i : ℝ)) ≤ 1 := by
      rw [← Real.rpow_add hjb]
      apply Real.rpow_le_one_of_one_le_of_nonpos hjb1
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    have hC : 0 ≤ Cw i := hCw0 i (by omega)
    calc jbracket x ^ p * ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun x : Euc d => jbracket x ^ (-p)) x‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun x => jbracket x ^ p • G x) x‖)
        ≤ jbracket x ^ p * ((j.choose i : ℝ) * (Cw i * jbracket x ^ (-p - (i : ℝ))) * B) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (norm_nonneg _)
            (by positivity)
      _ = (j.choose i : ℝ) * Cw i * B * (jbracket x ^ p * jbracket x ^ (-p - (i : ℝ))) := by ring
      _ ≤ (j.choose i : ℝ) * Cw i * B * 1 := mul_le_mul_of_nonneg_left hpe (by positivity)
      _ = _ := by ring
  calc jbracket x ^ p * ‖iteratedFDeriv ℝ j (fun x => jbracket x ^ (-p) • (jbracket x ^ p • G x)) x‖
      ≤ jbracket x ^ p * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x : Euc d => jbracket x ^ (-p)) x‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun x => jbracket x ^ p • G x) x‖ :=
        mul_le_mul_of_nonneg_left hsm (by positivity)
    _ = ∑ i ∈ Finset.range (j + 1), jbracket x ^ p * ((j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x : Euc d => jbracket x ^ (-p)) x‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun x => jbracket x ^ p • G x) x‖) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Cw i * B := Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Cw i) * B := by rw [Finset.sum_mul]
    _ ≤ K' * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB0
        have hjn : j ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
        have hcn : ∀ j' ∈ Finset.range (n + 1),
            0 ≤ ∑ i ∈ Finset.range (j' + 1), (j'.choose i : ℝ) * Cw i :=
          fun j' hj' => Finset.sum_nonneg fun i hi => mul_nonneg (by positivity)
            (hCwn i (Finset.mem_range.2 (by
              have := Finset.mem_range.1 hi; have := Finset.mem_range.1 hj'; omega)))
        exact Finset.single_le_sum
          (f := fun j' => ∑ i ∈ Finset.range (j' + 1), (j'.choose i : ℝ) * Cw i) hcn hjn

end HRS.MS.S85
