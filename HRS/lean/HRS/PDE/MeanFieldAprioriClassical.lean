import HRS.PDE.MeanFieldDefs
import HRS.PDE.MeanFieldProduct
import HRS.PDE.MeanFieldProductB
import HRS.PDE.MeanFieldSemigroup
import HRS.PDE.EnergySymbol

/-!
# A priori bounds for the finite-regularity mean-field equation, packet AP1a
(classical facts for `IsMFSolutionHK` solutions; package MF-01, plan `MeanFieldAprioriPlan.md`)

Imports only `MeanFieldDefs` and project modules that do not depend on `MeanFieldInputs`.
Section 0 contains verbatim copies (renamed into `MFApriori.Aux`) of the elementary `H^m` calculus of
`MeanFieldLocal.lean` (which cannot be imported here).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace HRS.PDE.MFApriori
namespace Aux

variable {d : ℕ}

/-- The nonlinear part `Div(ρ ∇(V + g⋆ρ))` of `mfRhsCoeff`. -/
noncomputable def nlCoeff (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (ρc : Coeff d) : Coeff d :=
  fun k => ∑ j : Fin d, derivCoeff j
    (mulCoeff ρc (fun k' => derivCoeff j (coeffOf V) k' + gradRieszCoeff d s j ρc k')) k

theorem mfRhsCoeff_eq (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (invβ : ℝ) (ρc : Coeff d) (k : Lattice d) :
    mfRhsCoeff d s V invβ ρc k = (invβ : ℂ) * laplaceCoeff ρc k + nlCoeff d s V ρc k := rfl


/-- A Fourier multiplier with `sobWeight b k ‖m k‖² ≤ B²` maps `H^a → H^{a+b}` with norm `≤ B`. -/
theorem hs_mult (m : Lattice d → ℂ) (a b B : ℝ) (hB : 0 ≤ B)
    (hm : ∀ k, sobWeight b k * ‖m k‖ ^ 2 ≤ B ^ 2) (c : Coeff d) (hc : MemHs a c) :
    MemHs (a + b) (fun k => m k * c k) ∧
      hsNorm (a + b) (fun k => m k * c k) ≤ B * hsNorm a c := by
  have hle : ∀ k, sobWeight (a + b) k * ‖m k * c k‖ ^ 2 ≤ B ^ 2 * (sobWeight a k * ‖c k‖ ^ 2) := by
    intro k
    rw [norm_mul, mul_pow, ← HRS.PDE.MFProduct.sobWeight_mul a b k]
    have h0 := HRS.PDE.MFProduct.sobWeight_nonneg a k
    have h1 : 0 ≤ ‖c k‖ ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left (hm k) (mul_nonneg h0 h1)]
  have hsum : Summable fun k => B ^ 2 * (sobWeight a k * ‖c k‖ ^ 2) := hc.mul_left _
  have hmem : MemHs (a + b) (fun k => m k * c k) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (HRS.PDE.MFProduct.sobWeight_nonneg _ k) (sq_nonneg _))
      hle hsum
  refine ⟨hmem, ?_⟩
  unfold hsNorm hsNormSq
  calc Real.sqrt (∑' k, sobWeight (a + b) k * ‖m k * c k‖ ^ 2)
      ≤ Real.sqrt (B ^ 2 * ∑' k, sobWeight a k * ‖c k‖ ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [← tsum_mul_left]
        exact hmem.tsum_le_tsum hle hsum
    _ = B * Real.sqrt (∑' k, sobWeight a k * ‖c k‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB]


/-! ### Elementary `H^m` calculus -/

theorem hsNorm_nonneg (m : ℝ) (c : Coeff d) : 0 ≤ hsNorm m c := Real.sqrt_nonneg _

theorem memHs_mono {m n : ℝ} (hmn : m ≤ n) {c : Coeff d} (hc : MemHs n c) : MemHs m c := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (HRS.PDE.MFProduct.sobWeight_nonneg m k) (sq_nonneg _)) (fun k => ?_) hc
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  unfold sobWeight
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (Real.pi * Lattice.enorm k)]) hmn

theorem memHs_zero_coeff (m : ℝ) : MemHs m (0 : Coeff d) := by
  simp [MemHs]

theorem hsNorm_zero_coeff (m : ℝ) : hsNorm m (0 : Coeff d) = 0 := by
  simp [hsNorm, hsNormSq]

theorem sobWeight_half_sq' (m : ℝ) (k : Lattice d) (x : ℂ) :
    sobWeight m k * ‖x‖ ^ 2 = (sobWeight (m / 2) k * ‖x‖) ^ 2 := by
  rw [mul_pow, HRS.PDE.MFProduct.sobWeight_half_sq]

theorem hsNorm_eq_sqrt (m : ℝ) (c : Coeff d) :
    hsNorm m c = Real.sqrt (∑' k, (sobWeight (m / 2) k * ‖c k‖) ^ 2) := by
  unfold hsNorm hsNormSq
  congr 1; exact tsum_congr fun k => sobWeight_half_sq' m k _

/-- Triangle inequality in `H^m`. -/
theorem memHs_add_le (m : ℝ) {f g : Coeff d} (hf : MemHs m f) (hg : MemHs m g) :
    MemHs m (f + g) ∧ hsNorm m (f + g) ≤ hsNorm m f + hsNorm m g := by
  set P : Lattice d → ℝ := fun k => sobWeight (m / 2) k * ‖f k‖ with hP
  set Q : Lattice d → ℝ := fun k => sobWeight (m / 2) k * ‖g k‖ with hQ
  have hP0 : ∀ k, 0 ≤ P k := fun k => mul_nonneg (HRS.PDE.MFProduct.sobWeight_nonneg _ k) (norm_nonneg _)
  have hQ0 : ∀ k, 0 ≤ Q k := fun k => mul_nonneg (HRS.PDE.MFProduct.sobWeight_nonneg _ k) (norm_nonneg _)
  have hP2 : Summable fun k => P k ^ 2 := hf.congr fun k => sobWeight_half_sq' m k _
  have hQ2 : Summable fun k => Q k ^ 2 := hg.congr fun k => sobWeight_half_sq' m k _
  obtain ⟨hs, hle⟩ := HRS.PDE.MFProduct.minkowski_sq P Q hP0 hQ0 hP2 hQ2
  have hpt : ∀ k, sobWeight m k * ‖(f + g) k‖ ^ 2 ≤ (P k + Q k) ^ 2 := by
    intro k
    rw [sobWeight_half_sq']
    have : sobWeight (m / 2) k * ‖(f + g) k‖ ≤ P k + Q k := by
      have h := norm_add_le (f k) (g k)
      have hw := HRS.PDE.MFProduct.sobWeight_nonneg (m / 2) k
      calc sobWeight (m / 2) k * ‖(f + g) k‖ ≤ sobWeight (m / 2) k * (‖f k‖ + ‖g k‖) :=
            mul_le_mul_of_nonneg_left h hw
        _ = _ := by simp only [hP, hQ]; ring
    exact pow_le_pow_left₀ (mul_nonneg (HRS.PDE.MFProduct.sobWeight_nonneg _ k) (norm_nonneg _)) this 2
  have hmem : MemHs m (f + g) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (HRS.PDE.MFProduct.sobWeight_nonneg _ k) (sq_nonneg _))
      hpt hs
  refine ⟨hmem, ?_⟩
  rw [hsNorm_eq_sqrt, hsNorm_eq_sqrt m f, hsNorm_eq_sqrt m g]
  refine le_trans (Real.sqrt_le_sqrt ?_) hle
  refine Summable.tsum_le_tsum (fun k => ?_) ?_ hs
  · rw [← sobWeight_half_sq']; exact hpt k
  · exact hmem.congr fun k => sobWeight_half_sq' m k _

theorem memHs_neg {m : ℝ} {f : Coeff d} (hf : MemHs m f) : MemHs m (-f) := by
  simpa [MemHs] using hf

theorem memHs_sub_aux {m : ℝ} {f g : Coeff d} (hf : MemHs m f) (hg : MemHs m g) :
    MemHs m (f - g) := by
  rw [sub_eq_add_neg]; exact (memHs_add_le m hf (memHs_neg hg)).1

/-- Triangle inequality for finite sums. -/
theorem memHs_finsum_le {ι : Type*} (m : ℝ) (S : Finset ι) (F : ι → Coeff d)
    (hF : ∀ i ∈ S, MemHs m (F i)) :
    MemHs m (fun k => ∑ i ∈ S, F i k) ∧
      hsNorm m (fun k => ∑ i ∈ S, F i k) ≤ ∑ i ∈ S, hsNorm m (F i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨memHs_zero_coeff m, le_of_eq (hsNorm_zero_coeff m)⟩
  | insert a S ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have h := memHs_add_le m (hF a (Finset.mem_insert_self a S)) ih1
    simp only [Finset.sum_insert ha]
    exact ⟨h.1, h.2.trans (by linarith)⟩

/-! ### Multiplication: linearity -/

theorem mulCoeff_diff_aux {a a' c c' : Coeff d} (ha : MemHs 0 a) (ha' : MemHs 0 a')
    (hc : MemHs 0 c) (hc' : MemHs 0 c') :
    mulCoeff a c - mulCoeff a' c' = mulCoeff (a - a') c + mulCoeff a' (c - c') := by
  funext k
  have h1 : Summable fun j => (a (k - j) - a' (k - j)) * c j :=
    summable_mulCoeff (a - a') c (memHs_sub_aux ha ha') hc k
  have h2 : Summable fun j => a' (k - j) * (c j - c' j) :=
    summable_mulCoeff a' (c - c') ha' (memHs_sub_aux hc hc') k
  have h3 := summable_mulCoeff a c ha hc k
  have h4 := summable_mulCoeff a' c' ha' hc' k
  simp only [mulCoeff, Pi.sub_apply, Pi.add_apply]
  rw [← h3.tsum_sub h4, ← h1.tsum_add h2]
  refine tsum_congr fun j => ?_
  ring

/-! ### Derivative and Riesz-gradient multipliers -/

/-- `∂_j : H^m → H^{m-1}` is a contraction. -/
theorem hs_deriv (j : Fin d) (m : ℝ) (c : Coeff d) (hc : MemHs m c) :
    MemHs (m + -1) (derivCoeff j c) ∧ hsNorm (m + -1) (derivCoeff j c) ≤ hsNorm m c := by
  have := hs_mult (fun k : Lattice d => (2 * Real.pi * Complex.I * (k j : ℂ))) m (-1) 1
    zero_le_one (fun k => ?_) c hc
  · rw [one_mul] at this
    exact this
  · have hW : 0 < sobWeight 1 k := sobWeight_pos 1 k
    have h1 : ‖(2 * Real.pi * Complex.I * (k j : ℂ))‖ = |2 * Real.pi * (k j : ℝ)| := by
      simp [Complex.norm_I, abs_of_pos Real.pi_pos, abs_mul]
    rw [h1]
    have h2 := abs_two_pi_le_rad k j
    have h3 := rad_sq_le k
    have h4 : |2 * Real.pi * (k j : ℝ)| ^ 2 ≤ sobWeight 1 k := by
      have : |2 * Real.pi * (k j : ℝ)| ^ 2 ≤ rad k ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h2 2
      unfold sobWeight; rw [Real.rpow_one]; linarith
    have h5 : sobWeight (-1) k = (sobWeight 1 k)⁻¹ := by
      unfold sobWeight; rw [Real.rpow_neg_one, Real.rpow_one]
    rw [h5, one_pow]
    calc (sobWeight 1 k)⁻¹ * |2 * Real.pi * (k j : ℝ)| ^ 2 ≤ (sobWeight 1 k)⁻¹ * sobWeight 1 k :=
          mul_le_mul_of_nonneg_left h4 (inv_nonneg.mpr hW.le)
      _ = 1 := inv_mul_cancel₀ hW.ne'

/-- `∂_i g * : H^m → H^{m + δ' - 1}` for `δ' ≤ min (d - s) 1`. -/
theorem hs_gradRiesz (s : ℝ) (i : Fin d) (m δ' : ℝ) (h1 : δ' ≤ 1) (h2 : δ' ≤ (d : ℝ) - s)
    (c : Coeff d) (hc : MemHs m c) :
    MemHs (m + (δ' - 1)) (gradRieszCoeff d s i c) ∧
      hsNorm (m + (δ' - 1)) (gradRieszCoeff d s i c) ≤ |rieszConst d s| * hsNorm m c := by
  have := hs_mult (fun k : Lattice d =>
      (2 * Real.pi * Complex.I * (k i : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) m (δ' - 1)
    |rieszConst d s| (abs_nonneg _) (fun k => ?_) c hc
  · have e : (fun k : Lattice d => (2 * Real.pi * Complex.I * (k i : ℂ)) *
        ((rieszCoeff d s k : ℝ) : ℂ) * c k) = gradRieszCoeff d s i c := by
      funext k; simp [gradRieszCoeff, derivCoeff, rieszMult, mul_assoc]
    rwa [e] at this
  · by_cases hk : k = 0
    · subst hk
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, zero_mul, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      positivity
    · have hr : 1 ≤ rad k := one_le_rad k hk
      have hr0 : 0 < rad k := by linarith
      have hn := norm_symS_le s i k hk
      set e : ℝ := s - (d : ℝ) + 1 with he
      set W : ℝ := 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 with hW
      have hW1 : 1 ≤ W := by nlinarith [sq_nonneg (Real.pi * Lattice.enorm k)]
      have hrr : rad k * rad k ≤ W := by
        have := rad_sq_le k
        nlinarith
      have hrr1 : 1 ≤ rad k * rad k := by nlinarith
      have key : sobWeight (δ' - 1) k * (rad k ^ e * rad k ^ e) ≤ 1 := by
        rw [← Real.mul_rpow hr0.le hr0.le]
        have hWb : sobWeight (δ' - 1) k = W ^ (δ' - 1) := rfl
        rw [hWb]
        rcases le_or_gt 0 e with he0 | he0
        · have h6 : (rad k * rad k) ^ e ≤ W ^ e :=
            Real.rpow_le_rpow (by positivity) hrr he0
          calc W ^ (δ' - 1) * (rad k * rad k) ^ e
              ≤ W ^ (δ' - 1) * W ^ e :=
                mul_le_mul_of_nonneg_left h6 (Real.rpow_nonneg (by linarith) _)
            _ = W ^ ((δ' - 1) + e) := (Real.rpow_add (by linarith) _ _).symm
            _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by rw [he]; linarith)
        · have h6 : (rad k * rad k) ^ e ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos hrr1 he0.le
          have h7 : W ^ (δ' - 1) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
          calc W ^ (δ' - 1) * (rad k * rad k) ^ e
              ≤ 1 * 1 := mul_le_mul h7 h6 (Real.rpow_nonneg (by positivity) _)
                (by norm_num)
            _ = 1 := by norm_num
      have hsq : ‖(2 * Real.pi * Complex.I * (k i : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)‖ ^ 2 ≤
          |rieszConst d s| ^ 2 * (rad k ^ e * rad k ^ e) := by
        calc _ ≤ (|rieszConst d s| * rad k ^ e) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hn 2
          _ = _ := by ring
      calc sobWeight (δ' - 1) k * ‖(2 * Real.pi * Complex.I * (k i : ℂ)) *
            ((rieszCoeff d s k : ℝ) : ℂ)‖ ^ 2
          ≤ sobWeight (δ' - 1) k * (|rieszConst d s| ^ 2 * (rad k ^ e * rad k ^ e)) :=
            mul_le_mul_of_nonneg_left hsq (HRS.PDE.MFProduct.sobWeight_nonneg _ k)
        _ = |rieszConst d s| ^ 2 * (sobWeight (δ' - 1) k * (rad k ^ e * rad k ^ e)) := by ring
        _ ≤ |rieszConst d s| ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left key (sq_nonneg _)
        _ = _ := mul_one _

/-! ### The bilinear estimate -/

theorem gradRieszCoeff_sub_aux (s : ℝ) (i : Fin d) (c₁ c₂ : Coeff d) :
    gradRieszCoeff d s i (c₁ - c₂) = gradRieszCoeff d s i c₁ - gradRieszCoeff d s i c₂ := by
  funext k
  simp only [gradRieszCoeff, rieszMult, derivCoeff, Pi.sub_apply]
  ring

theorem derivCoeff_sub_aux (j : Fin d) (a b : Coeff d) :
    derivCoeff j (a - b) = derivCoeff j a - derivCoeff j b := by
  funext k
  simp only [derivCoeff, Pi.sub_apply]
  ring

/-- **Corrected bilinear estimate.**  The plan's `exists_nl_lipschitz` (with the right-hand side
`C (‖ρ‖ + ‖ρ'‖) ‖ρ - ρ'‖` and `V ∈ C²`) is false as stated: the part `∑_j ∂_j(ρ ∂_jV)` of `nlCoeff`
is linear in `ρ`, so for `ρ = 0`, `ρ' = ε δ_k` the left side is of order `ε` while the right side is of
order `ε²` as soon as `V` is not constant; moreover `V ∈ C²` does not put `∂_jV` in `H^{K-1+δ'}`
for large `K`.  Here the right side is `C (1 + ‖ρ‖ + ‖ρ'‖) ‖ρ - ρ'‖` and `V` is assumed to satisfy
`V̂ ∈ H^{K+δ'}` (e.g. `V ∈ C^{K+2}` with `K` an integer, `δ' < 1`). -/
theorem exists_nl_lipschitz' (_hd : 1 ≤ d) (s : ℝ) (_hs0 : 0 ≤ s) (_hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 1 < K) (V : Torus d → ℝ) (δ' : ℝ) (hδ0 : 0 ≤ δ')
    (hδ : δ' < min ((d : ℝ) - s) 1) (hV : MemHs (K + δ') (coeffOf V)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρc ρc' : Coeff d, MemHs K ρc → MemHs K ρc' →
      MemHs (K - 2 + δ') (nlCoeff d s V ρc - nlCoeff d s V ρc') ∧
      hsNorm (K - 2 + δ') (nlCoeff d s V ρc - nlCoeff d s V ρc') ≤
        C * (1 + hsNorm K ρc + hsNorm K ρc') * hsNorm K (ρc - ρc') := by
  have hδ1 : δ' < (d : ℝ) - s := lt_of_lt_of_le hδ (min_le_left _ _)
  have hδ2 : δ' < 1 := lt_of_lt_of_le hδ (min_le_right _ _)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set c0 : ℝ := K - 1 + δ' with hc0
  have hc00 : 0 ≤ c0 := by rw [hc0]; linarith
  have hc0K : c0 ≤ K := by rw [hc0]; linarith
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨P, hP0, hP⟩ := HRS.PDE.MFProduct.exists_product_bound (d := d) K c0 c0 hc00 hc0K le_rfl (by linarith)
  -- the potential part
  have hv : ∀ j : Fin d, MemHs c0 (derivCoeff j (coeffOf V)) := by
    intro j
    have := (hs_deriv j (K + δ') (coeffOf V) hV).1
    rwa [show K + δ' + -1 = c0 by rw [hc0]; ring] at this
  set Mv : ℝ := ∑ j : Fin d, hsNorm c0 (derivCoeff j (coeffOf V)) with hMv
  have hMv0 : 0 ≤ Mv := Finset.sum_nonneg fun j _ => hsNorm_nonneg _ _
  set Cg : ℝ := |rieszConst d s| with hCg
  -- the interaction part
  have hG : ∀ (j : Fin d) (ρ : Coeff d), MemHs K ρ →
      MemHs c0 (gradRieszCoeff d s j ρ) ∧ hsNorm c0 (gradRieszCoeff d s j ρ) ≤ Cg * hsNorm K ρ := by
    intro j ρ hρ
    have := hs_gradRiesz s j K δ' hδ2.le hδ1.le ρ hρ
    rwa [show K + (δ' - 1) = c0 by rw [hc0]; ring] at this
  refine ⟨P * (Mv + d * Cg), by positivity, fun ρ ρ' hρ hρ' => ?_⟩
  have hΔ : MemHs K (ρ - ρ') := memHs_sub_aux hρ hρ'
  set Δ : Coeff d := ρ - ρ' with hΔdef
  have hρ0 : MemHs 0 ρ := memHs_mono hK0 hρ
  have hρ'0 : MemHs 0 ρ' := memHs_mono hK0 hρ'
  -- per-mode estimates
  have hmode : ∀ j : Fin d,
      MemHs (K - 2 + δ') (derivCoeff j (mulCoeff ρ (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ) -
          mulCoeff ρ' (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ'))) ∧
        hsNorm (K - 2 + δ') (derivCoeff j (mulCoeff ρ (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ) -
          mulCoeff ρ' (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ'))) ≤
        P * hsNorm K Δ * (hsNorm c0 (derivCoeff j (coeffOf V)) + Cg * hsNorm K ρ) +
          P * hsNorm K ρ' * (Cg * hsNorm K Δ) := by
    intro j
    obtain ⟨hGρ, hGρn⟩ := hG j ρ hρ
    obtain ⟨hGρ', -⟩ := hG j ρ' hρ'
    obtain ⟨hGΔ, hGΔn⟩ := hG j Δ hΔ
    have hvj := hv j
    obtain ⟨hw, hwn⟩ := memHs_add_le c0 hvj hGρ
    have hw' := (memHs_add_le c0 hvj hGρ').1
    have hid : mulCoeff ρ (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ) -
        mulCoeff ρ' (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ') =
        mulCoeff Δ (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ) +
          mulCoeff ρ' (gradRieszCoeff d s j Δ) := by
      rw [mulCoeff_diff_aux hρ0 hρ'0 (memHs_mono hc00 hw) (memHs_mono hc00 hw')]
      congr 2
      rw [hΔdef, gradRieszCoeff_sub_aux]
      abel
    rw [hid]
    obtain ⟨hA, hAn⟩ := hP Δ _ hΔ hw
    obtain ⟨hB, hBn⟩ := hP ρ' _ hρ' hGΔ
    obtain ⟨hE, hEn⟩ := memHs_add_le c0 hA hB
    obtain ⟨hF, hFn⟩ := hs_deriv j c0 _ hE
    rw [show c0 + -1 = K - 2 + δ' by rw [hc0]; ring] at hF hFn
    refine ⟨hF, hFn.trans (hEn.trans ?_)⟩
    have h1 : P * hsNorm K Δ * hsNorm c0 (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ) ≤
        P * hsNorm K Δ * (hsNorm c0 (derivCoeff j (coeffOf V)) + Cg * hsNorm K ρ) :=
      mul_le_mul_of_nonneg_left (hwn.trans (by linarith)) (by positivity [hsNorm_nonneg K Δ])
    have h2 : P * hsNorm K ρ' * hsNorm c0 (gradRieszCoeff d s j Δ) ≤
        P * hsNorm K ρ' * (Cg * hsNorm K Δ) :=
      mul_le_mul_of_nonneg_left hGΔn (by positivity [hsNorm_nonneg K ρ'])
    linarith
  -- assemble
  have hsum : nlCoeff d s V ρ - nlCoeff d s V ρ' = fun k => ∑ j : Fin d, derivCoeff j
      (mulCoeff ρ (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ) -
        mulCoeff ρ' (derivCoeff j (coeffOf V) + gradRieszCoeff d s j ρ')) k := by
    funext k
    simp only [nlCoeff, Pi.sub_apply, ← Finset.sum_sub_distrib, derivCoeff_sub_aux]
    rfl
  rw [hsum]
  obtain ⟨h1, h2⟩ := memHs_finsum_le (K - 2 + δ') Finset.univ _ (fun j _ => (hmode j).1)
  refine ⟨h1, h2.trans ?_⟩
  refine (Finset.sum_le_sum fun j _ => (hmode j).2).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have e1 : ∑ j : Fin d, (hsNorm c0 (derivCoeff j (coeffOf V)) + Cg * hsNorm K ρ) =
      Mv + d * (Cg * hsNorm K ρ) := by
    rw [Finset.sum_add_distrib, hMv]
    simp
  rw [e1]
  have hx := hsNorm_nonneg K ρ
  have hy := hsNorm_nonneg K ρ'
  have hz := hsNorm_nonneg K Δ
  have hCg0 : 0 ≤ Cg := abs_nonneg _
  have hdC : 0 ≤ (d : ℝ) * Cg := by positivity
  have hPz : 0 ≤ P * hsNorm K Δ := mul_nonneg hP0 hz
  nlinarith [mul_nonneg hPz (mul_nonneg hMv0 hx), mul_nonneg hPz (mul_nonneg hMv0 hy),
    mul_nonneg hPz hdC]

/-! ### Variation of constants for a scalar linear ODE with integrable forcing -/

theorem norm_coeff_mul_sqrt_le (m : ℝ) {c : Coeff d} (hc : MemHs m c) (k : Lattice d) :
    ‖c k‖ * Real.sqrt (sobWeight m k) ≤ hsNorm m c := by
  have h1 : sobWeight m k * ‖c k‖ ^ 2 ≤ hsNormSq m c := hc.le_tsum k fun j _ =>
    mul_nonneg (HRS.PDE.MFProduct.sobWeight_nonneg m j) (sq_nonneg _)
  calc ‖c k‖ * Real.sqrt (sobWeight m k)
      = Real.sqrt (sobWeight m k * ‖c k‖ ^ 2) := by
        rw [Real.sqrt_mul (HRS.PDE.MFProduct.sobWeight_nonneg m k), Real.sqrt_sq (norm_nonneg _), mul_comm]
    _ ≤ hsNorm m c := Real.sqrt_le_sqrt h1

/-- Modewise continuity of a path continuous into `H^m`. -/
theorem continuousOn_mode {m : ℝ} {ρc : ℝ → Coeff d} {S : Set ℝ} (h : ContinuousInHsOn m ρc S)
    (k : Lattice d) : ContinuousOn (fun t => ρc t k) S := by
  intro τ0 hτ0
  have hw : 0 < Real.sqrt (sobWeight m k) := Real.sqrt_pos.mpr (sobWeight_pos m k)
  have hT := h.2 τ0 hτ0
  have hbd : ∀ τ ∈ S, ‖ρc τ k - ρc τ0 k‖ ≤ hsNorm m (ρc τ - ρc τ0) / Real.sqrt (sobWeight m k) := by
    intro τ hτ
    rw [le_div_iff₀ hw]
    exact norm_coeff_mul_sqrt_le m (memHs_sub_aux (h.1 τ hτ) (h.1 τ0 hτ0)) k
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall hbd) ?_
  simpa using hT.div_const (Real.sqrt (sobWeight m k))

/-- Minkowski: `‖∫ F‖_{H^m} ≤ ∫ ‖F‖_{H^m}` for a coefficientwise interval integral of a family of
`H^m` sequences with integrable modes and integrable `H^m` norm. -/
theorem hsNorm_intervalIntegral_le (m : ℝ) (F : ℝ → Coeff d) {a b : ℝ} (hab : a ≤ b)
    (hmem : ∀ σ ∈ Set.Icc a b, MemHs m (F σ))
    (hmode : ∀ k, IntervalIntegrable (fun σ => F σ k) volume a b)
    (hnorm : IntervalIntegrable (fun σ => hsNorm m (F σ)) volume a b) :
    MemHs m (fun k => ∫ σ in a..b, F σ k) ∧
      hsNorm m (fun k => ∫ σ in a..b, F σ k) ≤ ∫ σ in a..b, hsNorm m (F σ) := by
  set A : Lattice d → ℂ := fun k => ∫ σ in a..b, F σ k with hA
  set B : ℝ := ∫ σ in a..b, hsNorm m (F σ) with hB
  have hB0 : 0 ≤ B := intervalIntegral.integral_nonneg hab fun σ _ => hsNorm_nonneg _ _
  have hw0 : ∀ k : Lattice d, 0 ≤ sobWeight m k := fun k => HRS.PDE.MFProduct.sobWeight_nonneg m k
  have key : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight m k * ‖A k‖ ^ 2 ≤ B ^ 2 := by
    intro S
    set N : ℝ := ∑ k ∈ S, sobWeight m k * ‖A k‖ ^ 2 with hN
    have hN0 : 0 ≤ N := Finset.sum_nonneg fun k _ => mul_nonneg (hw0 k) (sq_nonneg _)
    rcases hN0.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    set H : ℝ → ℂ := fun σ => ∑ k ∈ S, ((sobWeight m k : ℝ) : ℂ) * conj (A k) * F σ k with hH
    have hHint : IntervalIntegrable H volume a b := by
      have := IntervalIntegrable.sum S fun k _ =>
        (hmode k).const_mul (((sobWeight m k : ℝ) : ℂ) * conj (A k))
      convert this using 1
      funext σ
      simp [hH, Finset.sum_apply, mul_assoc]
    have hI : ∫ σ in a..b, H σ = (N : ℂ) := by
      simp only [hH]
      rw [intervalIntegral.integral_finsetSum fun k _ => (hmode k).const_mul _]
      simp_rw [intervalIntegral.integral_const_mul]
      simp only [hN]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      have : (conj (A k)) * A k = ((‖A k‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hA]
      simp only at this ⊢
      rw [mul_assoc, this]
      push_cast; ring
    have hpt : ∀ σ ∈ Set.Icc a b, ‖H σ‖ ≤ Real.sqrt N * hsNorm m (F σ) := by
      intro σ hσ
      have h1 : ‖H σ‖ ≤ ∑ k ∈ S, (Real.sqrt (sobWeight m k) * ‖A k‖) *
          (Real.sqrt (sobWeight m k) * ‖F σ k‖) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => le_of_eq ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 k),
          RCLike.norm_conj]
        have := Real.mul_self_sqrt (hw0 k)
        linear_combination (-(‖A k‖ * ‖F σ k‖)) * this
      refine h1.trans ((Real.sum_mul_le_sqrt_mul_sqrt S _ _).trans ?_)
      refine mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      · refine le_of_eq (congrArg Real.sqrt (Finset.sum_congr rfl fun k _ => ?_))
        rw [mul_pow, Real.sq_sqrt (hw0 k)]
      · unfold hsNorm hsNormSq
        refine Real.sqrt_le_sqrt ?_
        have hs := hmem σ hσ
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
          (hs.sum_le_tsum S fun k _ => mul_nonneg (hw0 k) (sq_nonneg _))
        rw [mul_pow, Real.sq_sqrt (hw0 k)]
    have h2 : N ≤ Real.sqrt N * B := by
      calc N = ‖(N : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN0]
        _ = ‖∫ σ in a..b, H σ‖ := by rw [hI]
        _ ≤ ∫ σ in a..b, ‖H σ‖ := intervalIntegral.norm_integral_le_integral_norm hab
        _ ≤ ∫ σ in a..b, Real.sqrt N * hsNorm m (F σ) :=
            intervalIntegral.integral_mono_on hab hHint.norm (hnorm.const_mul _) hpt
        _ = Real.sqrt N * B := intervalIntegral.integral_const_mul _ _
    have h3 : Real.sqrt N ≤ B := by
      have hs := Real.sqrt_pos.mpr hpos
      have : Real.sqrt N * Real.sqrt N ≤ Real.sqrt N * B := by
        rwa [Real.mul_self_sqrt hN0]
      exact le_of_mul_le_mul_left this hs
    calc N = Real.sqrt N ^ 2 := (Real.sq_sqrt hN0).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h3 2
  have hnn : 0 ≤ fun k : Lattice d => sobWeight m k * ‖A k‖ ^ 2 := fun k => mul_nonneg (hw0 k) (sq_nonneg _)
  have hsum : MemHs m A := summable_of_sum_le hnn key
  refine ⟨hsum, ?_⟩
  unfold hsNorm hsNormSq
  exact Real.sqrt_le_iff.mpr ⟨hB0, Real.tsum_le_of_sum_le hnn key⟩

/-- Minkowski for a path continuous into `H^m`. -/
theorem hsNorm_intervalIntegral_le_of_cont (m : ℝ) (F : ℝ → Coeff d) {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousInHsOn m F (Set.Icc a b)) :
    MemHs m (fun k => ∫ σ in a..b, F σ k) ∧
      hsNorm m (fun k => ∫ σ in a..b, F σ k) ≤ ∫ σ in a..b, hsNorm m (F σ) := by
  refine hsNorm_intervalIntegral_le m F hab hF.1 (fun k => ?_) ?_
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]; exact continuousOn_mode hF k
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    intro σ0 hσ0
    have hT := hF.2 σ0 hσ0
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_nhdsWithin_of_forall fun σ hσ => ?_) hT
    have h1 := memHs_add_le m (hF.1 σ0 hσ0) (memHs_sub_aux (hF.1 σ hσ) (hF.1 σ0 hσ0))
    have h2 := memHs_add_le m (hF.1 σ hσ) (memHs_sub_aux (hF.1 σ0 hσ0) (hF.1 σ hσ))
    have e1 : F σ0 + (F σ - F σ0) = F σ := by abel
    have e2 : F σ + (F σ0 - F σ) = F σ0 := by abel
    have e3 : hsNorm m (F σ0 - F σ) = hsNorm m (F σ - F σ0) := by
      unfold hsNorm hsNormSq
      simp only [Pi.sub_apply, norm_sub_rev (F σ0 _)]
    rw [e1] at h1
    rw [e2, e3] at h2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h2.2, h1.2]


/-! ### Section 1: further elementary `H^m` facts -/

theorem memHs_sub {m : ℝ} {f g : Coeff d} (hf : MemHs m f) (hg : MemHs m g) :
    MemHs m (f - g) := memHs_sub_aux hf hg

/-- `‖c‖_{H^m} ≤ ‖c'‖_{H^m} + ‖c - c'‖_{H^m}`. -/
theorem hsNorm_le_add_sub (m : ℝ) {f g : Coeff d} (hf : MemHs m f) (hg : MemHs m g) :
    hsNorm m f ≤ hsNorm m g + hsNorm m (f - g) := by
  have h := memHs_add_le m hg (memHs_sub hf hg)
  have e : g + (f - g) = f := by abel
  rw [e] at h
  exact h.2

theorem hsNorm_neg (m : ℝ) (c : Coeff d) : hsNorm m (-c) = hsNorm m c := by
  unfold hsNorm hsNormSq
  simp only [Pi.neg_apply, norm_neg]

theorem hsNorm_sub_comm (m : ℝ) (f g : Coeff d) : hsNorm m (f - g) = hsNorm m (g - f) := by
  unfold hsNorm hsNormSq
  simp only [Pi.sub_apply, norm_sub_rev (f _)]

theorem abs_hsNorm_sub_le (m : ℝ) {f g : Coeff d} (hf : MemHs m f) (hg : MemHs m g) :
    |hsNorm m f - hsNorm m g| ≤ hsNorm m (f - g) := by
  have h1 := hsNorm_le_add_sub m hf hg
  have h2 := hsNorm_le_add_sub m hg hf
  rw [hsNorm_sub_comm m g f] at h2
  rw [abs_le]; constructor <;> linarith

theorem sobWeight_zero_aux (k : Lattice d) : sobWeight 0 k = 1 := by simp [sobWeight]

/-- Scalar multiplication by a real constant. -/
theorem hs_const_mul (m : ℝ) (a : ℝ) (c : Coeff d) (hc : MemHs m c) :
    MemHs m (fun k => (a : ℂ) * c k) ∧ hsNorm m (fun k => (a : ℂ) * c k) ≤ |a| * hsNorm m c := by
  have := hs_mult (fun _ : Lattice d => (a : ℂ)) m 0 |a| (abs_nonneg a) (fun k => by
    rw [sobWeight_zero_aux, one_mul, Complex.norm_real, Real.norm_eq_abs]) c hc
  simpa using this

theorem laplace_bound (K : ℝ) (c : Coeff d) (hc : MemHs K c) (ν : ℝ) :
    MemHs (K - 2) (fun k => (ν : ℂ) * laplaceCoeff c k) ∧
      hsNorm (K - 2) (fun k => (ν : ℂ) * laplaceCoeff c k) ≤ |ν| * hsNorm K c := by
  have := hs_mult (fun k : Lattice d => (ν : ℂ) * (-((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ)))
    K (-2) |ν| (abs_nonneg ν) (fun k => ?_) c hc
  · have e : (fun k => (ν : ℂ) * (-((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ)) * c k) =
        fun k => (ν : ℂ) * laplaceCoeff c k := by
      funext k; simp only [laplaceCoeff]; ring
    rw [e] at this
    simpa [sub_eq_add_neg] using this
  · set L : ℝ := 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 with hL
    have hL0 : 0 ≤ L := by positivity
    have hw : sobWeight (-2) k = ((1 + L) ^ 2)⁻¹ := by
      unfold sobWeight
      rw [← hL, show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg (by linarith), Real.rpow_natCast]
    rw [hw, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hL0]
    have : L ^ 2 ≤ (1 + L) ^ 2 := by nlinarith
    have hp : 0 < (1 + L) ^ 2 := by positivity
    calc ((1 + L) ^ 2)⁻¹ * (|ν| * L) ^ 2 = |ν| ^ 2 * (L ^ 2 / (1 + L) ^ 2) := by
          field_simp
      _ ≤ |ν| ^ 2 * 1 := by
          gcongr
          rw [div_le_one hp]; exact this
      _ = |ν| ^ 2 := mul_one _


/-! ### Section 2: the right-hand side `mfRhsCoeff` -/

theorem nlCoeff_zero (s : ℝ) (V : Torus d → ℝ) : nlCoeff d s V 0 = 0 := by
  funext k
  simp [nlCoeff, mulCoeff, derivCoeff]

theorem mfRhsCoeff_split (s : ℝ) (V : Torus d → ℝ) (ν : ℝ) (c : Coeff d) :
    mfRhsCoeff d s V ν c = (fun k => (ν : ℂ) * laplaceCoeff c k) + nlCoeff d s V c := rfl

theorem mfRhsCoeff_zero (s : ℝ) (V : Torus d → ℝ) (ν : ℝ) : mfRhsCoeff d s V ν 0 = 0 := by
  funext k
  simp [mfRhsCoeff_split, nlCoeff_zero, laplaceCoeff]

/-- Shared estimate: the difference of right-hand sides. -/
theorem rhs_diff (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 1 < K) (V : Torus d → ℝ) (hVK : MemHs K (coeffOf V)) (ν : ℝ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ a b : Coeff d, MemHs K a → MemHs K b →
      MemHs (K - 2) (mfRhsCoeff d s V ν a - mfRhsCoeff d s V ν b) ∧
      hsNorm (K - 2) (mfRhsCoeff d s V ν a - mfRhsCoeff d s V ν b) ≤
        (|ν| + C₀ * (1 + hsNorm K a + hsNorm K b)) * hsNorm K (a - b) := by
  have hd' : 0 < min ((d : ℝ) - s) 1 := lt_min (by have := hsd; linarith) one_pos
  obtain ⟨C₀, hC₀, hC⟩ := exists_nl_lipschitz' hd s hs0 hsd K hK V 0 le_rfl hd'
    (by rw [add_zero]; exact hVK)
  refine ⟨C₀, hC₀, fun a b ha hb => ?_⟩
  obtain ⟨h1, h2⟩ := hC a b ha hb
  rw [add_zero] at h1 h2
  have hab : MemHs K (a - b) := memHs_sub ha hb
  obtain ⟨h3, h4⟩ := laplace_bound K (a - b) hab ν
  have e : mfRhsCoeff d s V ν a - mfRhsCoeff d s V ν b =
      (fun k => (ν : ℂ) * laplaceCoeff (a - b) k) + (nlCoeff d s V a - nlCoeff d s V b) := by
    funext k
    simp only [mfRhsCoeff_split, Pi.add_apply, Pi.sub_apply, laplaceCoeff]
    ring
  rw [e]
  obtain ⟨h5, h6⟩ := memHs_add_le (K - 2) h3 h1
  refine ⟨h5, h6.trans ?_⟩
  have hz := hsNorm_nonneg K (a - b)
  nlinarith [h4, h2]

theorem memHs_of_isCk_nat (K : ℕ) (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) :
    MemHs (K : ℝ) (coeffOf V) := by
  have := HRS.PDE.MFSemigroup.memHs_nat_of_isCk (K + 2) V hV
  exact memHs_mono (by push_cast; linarith) this

/-- The norm of a continuous path is continuous. -/
theorem continuousWithinAt_hsNorm {m : ℝ} {F : ℝ → Coeff d} {S : Set ℝ}
    (h : ContinuousInHsOn m F S) {τ0 : ℝ} (hτ0 : τ0 ∈ S) :
    ContinuousWithinAt (fun τ => hsNorm m (F τ)) S τ0 := by
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall fun τ hτ => ?_) (h.2 τ0 hτ0)
  rw [Real.norm_eq_abs]
  exact abs_hsNorm_sub_le m (h.1 τ hτ) (h.1 τ0 hτ0)

theorem uIcc_subset_Ici_zero {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : Set.uIcc a b ⊆ Set.Ici 0 := by
  intro x hx
  rw [Set.mem_uIcc] at hx
  rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact le_trans ha h1
  · exact le_trans hb h1

/-! ### Section 4: pointwise values of `toFun`, Minkowski for oriented integrals -/

theorem exists_l1_le (m : ℝ) (hm : (d : ℝ) / 2 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : Coeff d, MemHs m c →
      (Summable fun k => ‖c k‖) ∧ ∑' k, ‖c k‖ ≤ C * hsNorm m c := by
  obtain ⟨C, hC0, hC⟩ := HRS.PDE.MFProduct.exists_wienerW_le_hsNorm (d := d) m 0 le_rfl
    (by linarith)
  refine ⟨C, hC0, fun c hc => ?_⟩
  obtain ⟨h1, h2⟩ := hC c hc
  have e : ∀ k : Lattice d, sobWeight ((0 : ℝ) / 2) k = 1 := fun k => by simp [sobWeight]
  simp only [e, one_mul] at h1
  unfold HRS.PDE.MFProduct.wienerNormW at h2
  simp only [e, one_mul] at h2
  exact ⟨h1, h2⟩

/-- `toFun` is linear on `ℓ¹` sequences. -/
theorem toFun_lin (c c' e : Coeff d) (a : ℝ) (hc : Summable fun k => ‖c k‖)
    (hc' : Summable fun k => ‖c' k‖) (he : Summable fun k => ‖e k‖) (x : Torus d) :
    toFun (fun k => (a : ℂ) * (c k - c' k) - e k) x = a * (toFun c x - toFun c' x) - toFun e x := by
  have h1 := summable_series_terms c hc x
  have h2 := summable_series_terms c' hc' x
  have h3 := summable_series_terms e he x
  have : series (fun k => (a : ℂ) * (c k - c' k) - e k) x =
      a * (series c x - series c' x) - series e x := by
    unfold series
    rw [← h1.tsum_sub h2, ← tsum_mul_left, ← ((h1.sub h2).mul_left (a : ℂ)).tsum_sub h3]
    exact tsum_congr fun k => by ring
  unfold toFun
  rw [this]
  simp [Complex.sub_re, Complex.re_ofReal_mul]

theorem toFun_sub (c c' : Coeff d) (hc : Summable fun k => ‖c k‖)
    (hc' : Summable fun k => ‖c' k‖) (x : Torus d) :
    toFun (c - c') x = toFun c x - toFun c' x := by
  have h := toFun_lin c c' 0 1 hc hc' (by simpa using (summable_zero : Summable fun _ : Lattice d => (0:ℝ))) x
  simpa [toFun, series] using h

theorem continuousInHsOn_sub_const {m : ℝ} {F : ℝ → Coeff d} {S : Set ℝ}
    (h : ContinuousInHsOn m F S) (c : Coeff d) (hc : MemHs m c) :
    ContinuousInHsOn m (fun σ => F σ - c) S := by
  refine ⟨fun τ hτ => memHs_sub (h.1 τ hτ) hc, fun τ0 hτ0 => ?_⟩
  refine (h.2 τ0 hτ0).congr' (Eventually.of_forall fun τ => ?_)
  have : F τ - c - (F τ0 - c) = F τ - F τ0 := by abel
  simp only [this]

/-- Oriented Minkowski. -/
theorem hsNorm_integral_le (m : ℝ) (G : ℝ → Coeff d) (t y η : ℝ)
    (hG : ContinuousInHsOn m G (Set.uIcc t y)) (hη : ∀ σ ∈ Set.uIcc t y, hsNorm m (G σ) ≤ η) :
    MemHs m (fun k => ∫ σ in t..y, G σ k) ∧
      hsNorm m (fun k => ∫ σ in t..y, G σ k) ≤ |y - t| * η := by
  have key : ∀ a b : ℝ, a ≤ b → ContinuousInHsOn m G (Set.Icc a b) → (∀ σ ∈ Set.Icc a b, hsNorm m (G σ) ≤ η) →
      MemHs m (fun k => ∫ σ in a..b, G σ k) ∧
        hsNorm m (fun k => ∫ σ in a..b, G σ k) ≤ |b - a| * η := by
    intro a b hab hGc hηc
    obtain ⟨h1, h2⟩ := hsNorm_intervalIntegral_le_of_cont m G hab hGc
    refine ⟨h1, h2.trans ?_⟩
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (f := fun σ => hsNorm m (G σ)) (C := η) (fun σ hσ => by
        rw [Set.uIoc_of_le hab] at hσ
        rw [Real.norm_eq_abs, abs_of_nonneg (hsNorm_nonneg _ _)]
        exact hηc σ (Set.Ioc_subset_Icc_self hσ))
    refine (le_abs_self _).trans (this.trans ?_)
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    linarith
  rcases le_total t y with hty | hty
  · rw [Set.uIcc_of_le hty] at hG hη
    exact key t y hty hG hη
  · rw [Set.uIcc_of_ge hty] at hG hη
    obtain ⟨h1, h2⟩ := key y t hty hG hη
    have e : (fun k => ∫ σ in t..y, G σ k) = -(fun k => ∫ σ in y..t, G σ k) := by
      funext k
      simp [intervalIntegral.integral_symm y t]
    rw [e]
    refine ⟨by simpa [MemHs] using h1, ?_⟩
    rw [hsNorm_neg, abs_sub_comm]
    exact h2

end Aux

variable {d : ℕ}
open Aux

theorem exists_rhs_lipschitz (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 1 < K) (V : Torus d → ℝ) (hVK : MemHs K (coeffOf V)) (ν : ℝ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : Coeff d, MemHs K a → MemHs K b → hsNorm K a ≤ R → hsNorm K b ≤ R →
      MemHs (K - 2) (mfRhsCoeff d s V ν a - mfRhsCoeff d s V ν b) ∧
      hsNorm (K - 2) (mfRhsCoeff d s V ν a - mfRhsCoeff d s V ν b) ≤ C * hsNorm K (a - b) := by
  obtain ⟨C₀, hC₀, hC⟩ := rhs_diff hd s hs0 hsd K hK V hVK ν
  refine ⟨|ν| + C₀ * (1 + max R 0 + max R 0), by positivity, fun a b ha hb haR hbR => ?_⟩
  obtain ⟨h1, h2⟩ := hC a b ha hb
  refine ⟨h1, h2.trans ?_⟩
  have hz := hsNorm_nonneg K (a - b)
  have hR := le_max_left R 0
  gcongr
  · linarith
  · linarith

theorem exists_rhs_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 1 < K) (V : Torus d → ℝ) (hVK : MemHs K (coeffOf V)) (ν : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : Coeff d, MemHs K a →
      MemHs (K - 2) (mfRhsCoeff d s V ν a) ∧
      hsNorm (K - 2) (mfRhsCoeff d s V ν a) ≤ C * (1 + hsNorm K a) * (|ν| + 1 + hsNorm K a) := by
  obtain ⟨C₀, hC₀, hC⟩ := rhs_diff hd s hs0 hsd K hK V hVK ν
  refine ⟨1 + C₀, by positivity, fun a ha => ?_⟩
  have h0 : MemHs K (0 : Coeff d) := memHs_zero_coeff K
  obtain ⟨h1, h2⟩ := hC a 0 ha h0
  rw [mfRhsCoeff_zero, sub_zero, sub_zero, hsNorm_zero_coeff] at h2
  rw [mfRhsCoeff_zero, sub_zero] at h1
  refine ⟨h1, h2.trans ?_⟩
  have hx := hsNorm_nonneg K a
  have hn := abs_nonneg ν
  nlinarith [mul_nonneg hC₀ hx, mul_nonneg hC₀ hn, mul_nonneg (mul_nonneg hC₀ hx) hx,
    mul_nonneg (mul_nonneg hC₀ hx) hn, mul_nonneg hx hn, mul_nonneg hx hx]

theorem rhs_continuousInHsOn (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 1 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) (H : IsMFSolutionHK d s V ν K ρ₀ ρc) :
    ContinuousInHsOn ((K : ℝ) - 2) (fun σ => mfRhsCoeff d s V ν (ρc σ)) (Set.Ici 0) := by
  have hVK := memHs_of_isCk_nat K V hV
  obtain ⟨Cb, hCb0, hCb⟩ := exists_rhs_bound hd s hs0 hsd K hK V hVK ν
  refine ⟨fun τ hτ => (hCb _ (H.cont.1 τ hτ)).1, fun τ0 hτ0 => ?_⟩
  set R : ℝ := hsNorm K (ρc τ0) + 1 with hR
  obtain ⟨C, hC0, hC⟩ := exists_rhs_lipschitz hd s hs0 hsd K hK V hVK ν R
  have hT := H.cont.2 τ0 hτ0
  have hev : ∀ᶠ τ in 𝓝[Set.Ici 0] τ0, hsNorm K (ρc τ - ρc τ0) < 1 :=
    hT.eventually (gt_mem_nhds one_pos)
  have hmem : ∀ᶠ τ in 𝓝[Set.Ici 0] τ0, τ ∈ Set.Ici (0 : ℝ) := self_mem_nhdsWithin
  have hbound : ∀ᶠ τ in 𝓝[Set.Ici 0] τ0, hsNorm (K - 2 : ℝ) (mfRhsCoeff d s V ν (ρc τ) -
      mfRhsCoeff d s V ν (ρc τ0)) ≤ C * hsNorm K (ρc τ - ρc τ0) := by
    filter_upwards [hev, hmem] with τ hτ hτm
    have h1 := hsNorm_le_add_sub K (H.cont.1 τ hτm) (H.cont.1 τ0 hτ0)
    exact (hC _ _ (H.cont.1 τ hτm) (H.cont.1 τ0 hτ0) (by rw [hR]; linarith) (by rw [hR]; linarith)).2
  have hlim : Tendsto (fun τ => C * hsNorm K (ρc τ - ρc τ0)) (𝓝[Set.Ici 0] τ0) (𝓝 0) := by
    simpa using hT.const_mul C
  exact squeeze_zero' (Eventually.of_forall fun τ => hsNorm_nonneg _ _) hbound hlim

theorem exists_bound_of_continuousInHsOn (m : ℝ) (F : ℝ → Coeff d) (T : ℝ)
    (h : ContinuousInHsOn m F (Set.Ici 0)) :
    ∃ B : ℝ, ∀ t ∈ Set.Icc 0 T, hsNorm m (F t) ≤ B := by
  have hc : ContinuousOn (fun τ => hsNorm m (F τ)) (Set.Icc 0 T) := fun τ hτ =>
    (continuousWithinAt_hsNorm h (Set.mem_Ici.mpr hτ.1)).mono Set.Icc_subset_Ici_self
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨B, fun t ht => (le_abs_self _).trans (by simpa using hB t ht)⟩

/-! ### Section 3: modewise differentiability, mass conservation -/


theorem rhs_mode_continuousOn (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 1 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) (H : IsMFSolutionHK d s V ν K ρ₀ ρc) (k : Lattice d) :
    ContinuousOn (fun σ => mfRhsCoeff d s V ν (ρc σ) k) (Set.Ici 0) :=
  Aux.continuousOn_mode (rhs_continuousInHsOn hd s hs0 hsd K hK V ρ₀ hV ν ρc H) k

theorem coeff_sub_eq_integral (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 1 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) (H : IsMFSolutionHK d s V ν K ρ₀ ρc) (k : Lattice d) {t y : ℝ}
    (ht : 0 ≤ t) (hy : 0 ≤ y) :
    ρc y k - ρc t k = ∫ σ in t..y, mfRhsCoeff d s V ν (ρc σ) k := by
  have hc := rhs_mode_continuousOn hd s hs0 hsd K hK V ρ₀ hV ν ρc H k
  have hi : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      IntervalIntegrable (fun σ => mfRhsCoeff d s V ν (ρc σ) k) volume a b := fun a b ha hb =>
    (hc.mono (Aux.uIcc_subset_Ici_zero ha hb)).intervalIntegrable
  rw [H.eq k y hy, H.eq k t ht, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hi 0 y le_rfl hy) (hi 0 t le_rfl ht)]

theorem hasDerivAt_coeff (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 1 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) (H : IsMFSolutionHK d s V ν K ρ₀ ρc) (k : Lattice d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun τ => ρc τ k) (mfRhsCoeff d s V ν (ρc t) k) t := by
  have hc := rhs_mode_continuousOn hd s hs0 hsd K hK V ρ₀ hV ν ρc H k
  have hco : ContinuousOn (fun σ => mfRhsCoeff d s V ν (ρc σ) k) (Set.Ioi 0) :=
    hc.mono Set.Ioi_subset_Ici_self
  have hat : Set.Ioi (0 : ℝ) ∈ 𝓝 t := Ioi_mem_nhds ht
  have hint : IntervalIntegrable (fun σ => mfRhsCoeff d s V ν (ρc σ) k) volume 0 t :=
    (hc.mono (Aux.uIcc_subset_Ici_zero le_rfl ht.le)).intervalIntegrable
  have h1 := intervalIntegral.integral_hasDerivAt_right hint
    (hco.stronglyMeasurableAtFilter isOpen_Ioi t ht) (hco.continuousAt hat)
  have h2 := h1.const_add (coeffOf ρ₀ k)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [hat] with τ hτ
  exact H.eq k τ (le_of_lt hτ)

theorem coeff_zero_eq (hd : 1 ≤ d) (s : ℝ) (V ρ₀ : Torus d → ℝ) (ν K : ℝ) (ρc : ℝ → Coeff d)
    (H : IsMFSolutionHK d s V ν K ρ₀ ρc) {t : ℝ} (ht : 0 ≤ t) : ρc t 0 = coeffOf ρ₀ 0 := by
  have h0 : ∀ σ, mfRhsCoeff d s V ν (ρc σ) 0 = 0 := by
    intro σ
    have hn : Lattice.enorm (0 : Lattice d) = 0 := by
      simp [Lattice.enorm, Lattice.toEuc]; rfl
    simp [mfRhsCoeff, laplaceCoeff, derivCoeff, hn]
  rw [H.eq 0 t ht]
  simp only [h0]
  simp

theorem exists_mfPath_isCk (j : ℕ) (K : ℝ) (hK : (d : ℝ) / 2 + j < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : Coeff d, MemHs K c → IsRealCoeff c →
      Torus.IsCk j (toFun c) ∧ Torus.cbNorm j (toFun c) ≤ C * hsNorm K c := by
  obtain ⟨C, hC⟩ := toFun_isCk_le (d := d) j K hK
  refine ⟨max C 0, le_max_right _ _, fun c hc hr => ?_⟩
  obtain ⟨h1, h2⟩ := hC c hc hr
  exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Aux.hsNorm_nonneg _ _))⟩

/-! ### Section 5: pointwise time derivative of the density -/

/-- A solution with real coefficients (reality is derived from uniqueness in AP7). -/
structure MFSolReal (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (ν K : ℝ) (ρ₀ : Torus d → ℝ)
    (ρc : ℝ → Coeff d) : Prop where
  sol : IsMFSolutionHK d s V ν K ρ₀ ρc
  real : ∀ t, 0 ≤ t → IsRealCoeff (ρc t)

/-- The interaction potential `g ⋆ ρ` as a function, from the coefficients. -/
def riesz (d : ℕ) (s : ℝ) (c : Coeff d) : Torus d → ℝ := toFun (rieszMult d s c)

/-- The full potential `W = V + g ⋆ ρ`. -/
def Wpot (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (c : Coeff d) : Torus d → ℝ :=
  fun x => V x + riesz d s c x

/-- `Δ(g ⋆ ρ)` as a coefficient multiplier `-4π²|k|² ĝ(k)`. -/
def laplaceRieszCoeff (d : ℕ) (s : ℝ) (c : Coeff d) : Coeff d := laplaceCoeff (rieszMult d s c)

theorem hasDerivAt_mfPath (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) (H : MFSolReal d s V ν K ρ₀ ρc) (x : Torus d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun τ => mfPath ρc τ x) (toFun (mfRhsCoeff d s V ν (ρc t)) x) t := by
  have hK1 : (d : ℝ) / 2 + 1 < K := by linarith
  have hr := rhs_continuousInHsOn hd s hs0 hsd K hK1 V ρ₀ hV ν ρc H.sol
  set m : ℝ := (K : ℝ) - 2 with hm
  have hmd : (d : ℝ) / 2 < m := by rw [hm]; linarith
  have hKd : (d : ℝ) / 2 < K := by linarith
  obtain ⟨Cℓ, hCℓ0, hCℓ⟩ := exists_l1_le m hmd
  have hsumK : ∀ τ, 0 ≤ τ → Summable fun k => ‖ρc τ k‖ := fun τ hτ =>
    summable_norm_of_memHs K hKd _ (H.sol.cont.1 τ hτ)
  have hsumr : ∀ τ, 0 ≤ τ → Summable fun k => ‖mfRhsCoeff d s V ν (ρc τ) k‖ := fun τ hτ =>
    (hCℓ _ (hr.1 τ hτ)).1
  rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set η : ℝ := ε / (Cℓ + 1) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨δ0, hδ0, hδ0'⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hr.2 t (Set.mem_Ici.mpr ht.le)) η hη0
  refine ⟨min δ0 t, lt_min hδ0 ht, fun y hyt hyd => ?_⟩
  have hyt' : y ≠ t := hyt
  have hy1 : |y - t| < δ0 := by
    have := lt_of_lt_of_le hyd (min_le_left _ _); rwa [Real.dist_eq] at this
  have hy2 : |y - t| < t := by
    have := lt_of_lt_of_le hyd (min_le_right _ _); rwa [Real.dist_eq] at this
  have hy0 : 0 < y := by
    have := (abs_lt.mp hy2).1; linarith
  have hsub : y - t ≠ 0 := sub_ne_zero.mpr hyt'
  set G : ℝ → Coeff d := fun σ => mfRhsCoeff d s V ν (ρc σ) - mfRhsCoeff d s V ν (ρc t) with hG
  have hsubI : Set.uIcc t y ⊆ Set.Ici 0 := Aux.uIcc_subset_Ici_zero ht.le hy0.le
  have hGc : ContinuousInHsOn m G (Set.uIcc t y) := by
    have h := continuousInHsOn_sub_const hr _ (hr.1 t (Set.mem_Ici.mpr ht.le))
    exact ⟨fun τ hτ => h.1 τ (hsubI hτ), fun τ0 hτ0 => (h.2 τ0 (hsubI hτ0)).mono_left
      (nhdsWithin_mono _ hsubI)⟩
  have hGη : ∀ σ ∈ Set.uIcc t y, hsNorm m (G σ) ≤ η := by
    intro σ hσ
    have hσ0 := hsubI hσ
    have hdist : dist σ t < δ0 := by
      rw [Real.dist_eq]
      refine lt_of_le_of_lt ?_ hy1
      rw [Set.mem_uIcc] at hσ
      rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
    have := hδ0' hσ0 hdist
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNorm_nonneg _ _)] at this
    exact this.le
  obtain ⟨hM1, hM2⟩ := hsNorm_integral_le m G t y η hGc hGη
  -- the difference quotient as a coefficient sequence
  set a : ℝ := (y - t)⁻¹ with ha
  set D : Coeff d := fun k => (a : ℂ) * (ρc y k - ρc t k) - mfRhsCoeff d s V ν (ρc t) k with hD
  have hDeq : D = fun k => (a : ℂ) * (∫ σ in t..y, G σ k) := by
    funext k
    have hcont := rhs_mode_continuousOn hd s hs0 hsd K hK1 V ρ₀ hV ν ρc H.sol k
    have hint : IntervalIntegrable (fun σ => mfRhsCoeff d s V ν (ρc σ) k) volume t y :=
      (hcont.mono hsubI).intervalIntegrable
    have hGk : ∫ σ in t..y, G σ k = (∫ σ in t..y, mfRhsCoeff d s V ν (ρc σ) k) -
        (y - t) * mfRhsCoeff d s V ν (ρc t) k := by
      simp only [hG, Pi.sub_apply]
      rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const]
      simp
    rw [hGk, ← coeff_sub_eq_integral hd s hs0 hsd K hK1 V ρ₀ hV ν ρc H.sol k ht.le hy0.le]
    simp only [hD, ha]
    have hc : ((y : ℂ) - (t : ℂ)) ≠ 0 := by exact_mod_cast hsub
    push_cast
    field_simp
  have hDmem : MemHs m D ∧ hsNorm m D ≤ |a| * (|y - t| * η) := by
    rw [hDeq]
    obtain ⟨h1, h2⟩ := hs_const_mul m a _ hM1
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left hM2 (abs_nonneg _))⟩
  have hDb : |a| * (|y - t| * η) = η := by
    rw [ha, abs_inv, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hsub), one_mul]
  -- pointwise value
  have hval : toFun D x = (toFun (ρc y) x - toFun (ρc t) x) / (y - t) -
      toFun (mfRhsCoeff d s V ν (ρc t)) x := by
    have := toFun_lin (ρc y) (ρc t) (mfRhsCoeff d s V ν (ρc t)) a (hsumK y hy0.le)
      (hsumK t ht.le) (hsumr t ht.le) x
    simp only [hD]
    rw [this, ha]
    ring
  obtain ⟨hl1, hl2⟩ := hCℓ D hDmem.1
  have hbound : |toFun D x| ≤ Cℓ * η := by
    refine (HRS.PDE.MFProduct.abs_toFun_le D hl1 x).trans (hl2.trans ?_)
    exact mul_le_mul_of_nonneg_left (hDmem.2.trans (le_of_eq hDb)) hCℓ0
  rw [Real.dist_eq, slope_def_field]
  have : mfPath ρc y x = toFun (ρc y) x := rfl
  have h2 : mfPath ρc t x = toFun (ρc t) x := rfl
  rw [this, h2, ← hval]
  refine lt_of_le_of_lt hbound ?_
  rw [hη]
  have : Cℓ * (ε / (Cℓ + 1)) = ε * (Cℓ / (Cℓ + 1)) := by ring
  rw [this]
  have : Cℓ / (Cℓ + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  nlinarith

/-! ### Section 6: joint continuity -/

theorem continuousOn_toFun_prod (m : ℝ) (hm : (d : ℝ) / 2 < m) (F : ℝ → Coeff d)
    (h : ContinuousInHsOn m F (Set.Ici 0)) :
    ContinuousOn (fun p : ℝ × Torus d => toFun (F p.1) p.2) (Set.Ici 0 ×ˢ Set.univ) := by
  obtain ⟨Cℓ, hCℓ0, hCℓ⟩ := exists_l1_le m hm
  rintro ⟨t0, x0⟩ ⟨ht0, -⟩
  have ht0' : t0 ∈ Set.Ici (0 : ℝ) := ht0
  have hsum : ∀ τ ∈ Set.Ici (0 : ℝ), Summable fun k => ‖F τ k‖ := fun τ hτ => (hCℓ _ (h.1 τ hτ)).1
  rw [ContinuousWithinAt, nhdsWithin_prod_eq, nhdsWithin_univ, tendsto_iff_dist_tendsto_zero]
  have hA : Tendsto (fun p : ℝ × Torus d => Cℓ * hsNorm m (F p.1 - F t0))
      (𝓝[Set.Ici 0] t0 ×ˢ 𝓝 x0) (𝓝 0) := by
    have := (h.2 t0 ht0').const_mul Cℓ
    rw [mul_zero] at this
    exact this.comp (tendsto_fst : Tendsto (fun p : ℝ × Torus d => p.1)
      (𝓝[Set.Ici 0] t0 ×ˢ 𝓝 x0) (𝓝[Set.Ici 0] t0))
  have hcont := continuous_toFun (F t0) (hsum t0 ht0')
  have hB : Tendsto (fun p : ℝ × Torus d => dist (toFun (F t0) p.2) (toFun (F t0) x0))
      (𝓝[Set.Ici 0] t0 ×ˢ 𝓝 x0) (𝓝 0) := by
    have h1 : Tendsto (fun x : Torus d => dist (toFun (F t0) x) (toFun (F t0) x0)) (𝓝 x0) (𝓝 0) := by
      have := (hcont.tendsto x0).dist tendsto_const_nhds (b := toFun (F t0) x0)
      simpa using this
    exact h1.comp (tendsto_snd : Tendsto (fun p : ℝ × Torus d => p.2)
      (𝓝[Set.Ici 0] t0 ×ˢ 𝓝 x0) (𝓝 x0))
  have hev : ∀ᶠ p in (𝓝[Set.Ici 0] t0 ×ˢ 𝓝 x0 : Filter (ℝ × Torus d)), p.1 ∈ Set.Ici (0 : ℝ) :=
    (tendsto_fst (f := (𝓝[Set.Ici 0] t0 : Filter ℝ)) (g := (𝓝 x0 : Filter (Torus d)))).eventually
      self_mem_nhdsWithin
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ (hA.add hB |>.trans_eq (by simp))
  filter_upwards [hev] with p hp
  refine (dist_triangle _ (toFun (F t0) p.2) _).trans (add_le_add ?_ le_rfl)
  rw [Real.dist_eq, ← toFun_sub _ _ (hsum _ hp) (hsum t0 ht0')]
  refine (HRS.PDE.MFProduct.abs_toFun_le _ (hCℓ _ (memHs_sub (h.1 _ hp) (h.1 t0 ht0'))).1 _).trans ?_
  exact (hCℓ _ (memHs_sub (h.1 _ hp) (h.1 t0 ht0'))).2

theorem continuousOn_mfPath_prod (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) (H : MFSolReal d s V ν K ρ₀ ρc) :
    ContinuousOn (fun p : ℝ × Torus d => mfPath ρc p.1 p.2) (Set.Ici 0 ×ˢ Set.univ) ∧
    ContinuousOn (fun p : ℝ × Torus d => toFun (mfRhsCoeff d s V ν (ρc p.1)) p.2)
      (Set.Ici 0 ×ˢ Set.univ) := by
  refine ⟨continuousOn_toFun_prod K (by linarith) ρc H.sol.cont,
    continuousOn_toFun_prod ((K : ℝ) - 2) (by linarith) _
      (rhs_continuousInHsOn hd s hs0 hsd K (by linarith) V ρ₀ hV ν ρc H.sol)⟩

/-! ### Section 7: regularity of the potential and the classical form of the right-hand side -/

theorem isRealCoeff_rieszMult (s : ℝ) (c : Coeff d) (hc : IsRealCoeff c) :
    IsRealCoeff (rieszMult d s c) := by
  intro k
  simp only [rieszMult, rieszCoeff_neg, hc k, map_mul, Complex.conj_ofReal]

theorem isRealCoeff_derivCoeff (j : Fin d) (c : Coeff d) (hc : IsRealCoeff c) :
    IsRealCoeff (derivCoeff j c) := by
  intro k
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  simp only [derivCoeff, Pi.neg_apply, hc k, map_mul, h2, Complex.conj_ofReal, Complex.conj_I,
    map_intCast]
  push_cast
  ring

theorem isRealCoeff_laplaceCoeff (c : Coeff d) (hc : IsRealCoeff c) :
    IsRealCoeff (laplaceCoeff c) := by
  intro k
  simp only [laplaceCoeff, enorm_neg', hc k, map_mul, map_neg, Complex.conj_ofReal]

/-- `ĝ *` maps `H^K` to `H^K`. -/
theorem hs_rieszMult (s : ℝ) (hsd : s < d) (K : ℝ) (c : Coeff d) (hc : MemHs K c) :
    MemHs K (rieszMult d s c) ∧ hsNorm K (rieszMult d s c) ≤ |rieszConst d s| * hsNorm K c := by
  have := hs_mult (fun k : Lattice d => ((rieszCoeff d s k : ℝ) : ℂ)) K 0 |rieszConst d s|
    (abs_nonneg _) (fun k => by
      rw [sobWeight_zero_aux, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_rieszCoeff_leU hsd k) 2) c hc
  rw [add_zero] at this
  exact this

/-- `Δ(ĝ *) : H^K → H^{K-2}`. -/
theorem hs_laplaceRiesz (s : ℝ) (hsd : s < d) (K : ℝ) (c : Coeff d) (hc : MemHs K c) :
    MemHs (K - 2) (laplaceRieszCoeff d s c) ∧
      hsNorm (K - 2) (laplaceRieszCoeff d s c) ≤ |rieszConst d s| * hsNorm K c := by
  have := hs_mult (fun k : Lattice d =>
      (-((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) K (-2)
    |rieszConst d s| (abs_nonneg _) (fun k => ?_) c hc
  · have e : (fun k : Lattice d => (-((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ)) *
        ((rieszCoeff d s k : ℝ) : ℂ) * c k) = laplaceRieszCoeff d s c := by
      funext k; simp only [laplaceRieszCoeff, laplaceCoeff, rieszMult]; ring
    rw [e] at this
    simpa [sub_eq_add_neg] using this
  · set L : ℝ := 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 with hL
    have hL0 : 0 ≤ L := by positivity
    have hw : sobWeight (-2) k = ((1 + L) ^ 2)⁻¹ := by
      unfold sobWeight
      rw [← hL, show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg (by linarith), Real.rpow_natCast]
    rw [hw, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hL0]
    have hg := abs_rieszCoeff_leU hsd k
    have : L ^ 2 ≤ (1 + L) ^ 2 := by nlinarith
    have hp : 0 < (1 + L) ^ 2 := by positivity
    calc ((1 + L) ^ 2)⁻¹ * (L * |rieszCoeff d s k|) ^ 2
        = (L ^ 2 / (1 + L) ^ 2) * |rieszCoeff d s k| ^ 2 := by field_simp
      _ ≤ 1 * |rieszConst d s| ^ 2 := by
          gcongr
          · rw [div_le_one hp]; exact this
      _ = _ := one_mul _

theorem partialDeriv_toFun (j : Fin d) (e : Coeff d) (M : ℝ) (he : MemHs M e) (hreal : IsRealCoeff e)
    (hM : (d : ℝ) / 2 + 1 < M) :
    Torus.partialDeriv j (toFun e) = toFun (derivCoeff j e) := by
  obtain ⟨C, -, hC⟩ := exists_mfPath_isCk (d := d) 1 M (by simpa using hM)
  have h1 : Torus.IsCk 1 (toFun e) := by simpa using (hC e he hreal).1
  have hs : Summable fun k => ‖e k‖ := summable_norm_of_memHs M (by linarith) e he
  have hde : MemHs (M + -1) (derivCoeff j e) := (hs_deriv j M e he).1
  have hs' : Summable fun k => ‖derivCoeff j e k‖ :=
    summable_norm_of_memHs (M + -1) (by linarith) _ hde
  have hreal' := isRealCoeff_derivCoeff j e hreal
  refine MFAux.eq_of_funFourierCoeff_eq (continuous_partialDeriv j _ h1)
    (HRS.PDE.MFProduct.continuous_toFun _ hs') (fun k => ?_)
  have e1 : coeffOf (Torus.partialDeriv j (toFun e)) = derivCoeff j e := by
    rw [coeffOf_partialDeriv j _ h1, coeffOf_toFun e hreal hs]
  have e2 : coeffOf (toFun (derivCoeff j e)) = derivCoeff j e := coeffOf_toFun _ hreal' hs'
  exact (congrFun e1 k).trans (congrFun e2 k).symm

theorem laplacian_toFun (e : Coeff d) (M : ℝ) (he : MemHs M e) (hreal : IsRealCoeff e)
    (hM : (d : ℝ) / 2 + 2 < M) :
    Torus.laplacian (toFun e) = toFun (laplaceCoeff e) := by
  obtain ⟨C, -, hC⟩ := exists_mfPath_isCk (d := d) 2 M (by simpa using hM)
  have h2 : Torus.IsCk 2 (toFun e) := by simpa using (hC e he hreal).1
  have hs : Summable fun k => ‖e k‖ := summable_norm_of_memHs M (by linarith) e he
  have hde : MemHs (M - 2) (laplaceCoeff e) := by
    have := (laplace_bound M e he 1).1
    simpa using this
  have hs' : Summable fun k => ‖laplaceCoeff e k‖ :=
    summable_norm_of_memHs (M - 2) (by linarith) _ hde
  have hreal' := isRealCoeff_laplaceCoeff e hreal
  have hcont : Continuous (Torus.laplacian (toFun e)) := by
    have : Torus.laplacian (toFun e) = fun x => ∑ j, Torus.partialDeriv j (Torus.partialDeriv j (toFun e)) x := by
      funext x; exact laplacian_eq_sum _ h2 x
    rw [this]
    exact continuous_finsetSum _ fun j _ =>
      continuous_partialDeriv j _ (isCk_one_partialDeriv j _ h2)
  refine MFAux.eq_of_funFourierCoeff_eq hcont (HRS.PDE.MFProduct.continuous_toFun _ hs') (fun k => ?_)
  have e1 : coeffOf (Torus.laplacian (toFun e)) = laplaceCoeff e := by
    rw [coeffOf_laplacian _ h2, coeffOf_toFun e hreal hs]
  have e2 : coeffOf (toFun (laplaceCoeff e)) = laplaceCoeff e := coeffOf_toFun _ hreal' hs'
  exact (congrFun e1 k).trans (congrFun e2 k).symm

theorem riesz_isCk (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) (K : ℝ)
    (hK : (d : ℝ) / 2 + j < K) (c : Coeff d) (hc : MemHs K c) (hreal : IsRealCoeff c) :
    Torus.IsCk j (riesz d s c) ∧
      (2 ≤ j → ∀ x, Torus.laplacian (riesz d s c) x = toFun (laplaceRieszCoeff d s c) x) := by
  obtain ⟨C, -, hC⟩ := exists_mfPath_isCk (d := d) j K hK
  have hmem := (hs_rieszMult s hsd K c hc).1
  have hrr := isRealCoeff_rieszMult s c hreal
  refine ⟨(hC _ hmem hrr).1, fun hj x => ?_⟩
  have hK2 : (d : ℝ) / 2 + 2 < K := by
    have : (2 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have := laplacian_toFun _ K hmem hrr hK2
  exact congrFun this x

theorem partialDeriv_add (j : Fin d) (f g : Torus d → ℝ) (hf : Torus.IsCk 1 f) (hg : Torus.IsCk 1 g)
    (x : Torus d) :
    Torus.partialDeriv j (fun y => f y + g y) x = Torus.partialDeriv j f x + Torus.partialDeriv j g x := by
  have e1 : Torus.lift (fun y => f y + g y) = fun y => Torus.lift f y + Torus.lift g y := rfl
  unfold Torus.partialDeriv
  rw [e1, fderiv_fun_add ((hf.differentiable one_ne_zero) _) ((hg.differentiable one_ne_zero) _)]
  simp

theorem coeffOf_add (f g : Torus d → ℝ) (hf : Continuous f) (hg : Continuous g) (k : Lattice d) :
    coeffOf (fun x => f x + g x) k = coeffOf f k + coeffOf g k := by
  have := MFAux.coeffOf_sum (Finset.univ : Finset (Fin 2)) (fun i => if i = 0 then f else g)
    (fun i => by split_ifs <;> assumption) k
  simpa [Fin.sum_univ_two] using this

theorem coeffOf_const_mul (a : ℝ) (f : Torus d → ℝ) (k : Lattice d) :
    coeffOf (fun x => a * f x) k = a * coeffOf f k := by
  unfold coeffOf
  simp only [funFourierCoeff_eq_int, Complex.ofReal_mul]
  have : ∀ x : Torus d, UnitAddTorus.mFourier (-k) x * ((a : ℂ) * (f x : ℂ)) =
      (a : ℂ) * (UnitAddTorus.mFourier (-k) x * (f x : ℂ)) := fun x => by ring
  simp_rw [this]
  exact integral_const_mul _ _

theorem isCk_add {j : ℕ} (f g : Torus d → ℝ) (hf : Torus.IsCk j f) (hg : Torus.IsCk j g) :
    Torus.IsCk j (fun y => f y + g y) := hf.add hg

/-- The classical form of the right-hand side. **Corrected variant** of the plan statement
`toFun_mfRhsCoeff_eq`, which is false when `V` is merely `C²`: the extra hypothesis
`hVK : MemHs K (coeffOf V)` is needed (and available in all applications, `V ∈ C^{K+2}`). -/
theorem toFun_mfRhsCoeff_eq' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk 2 V)
    (hVK : MemHs K (coeffOf V)) (ν : ℝ)
    (c : Coeff d) (hc : MemHs K c) (hreal : IsRealCoeff c) (x : Torus d) :
    toFun (mfRhsCoeff d s V ν c) x =
      ν * Torus.laplacian (toFun c) x +
        ∑ j, Torus.partialDeriv j (fun y => toFun c y * Torus.partialDeriv j (Wpot d s V c) y) x := by
  have hK1 : (d : ℝ) / 2 + 1 < K := by linarith
  have hKd : (d : ℝ) / 2 < K := by linarith
  have hsc : Summable fun k => ‖c k‖ := summable_norm_of_memHs K hKd c hc
  obtain ⟨C₂, -, hC₂⟩ := exists_mfPath_isCk (d := d) 2 K (by simpa using hK)
  have hρ2 : Torus.IsCk 2 (toFun c) := (hC₂ c hc hreal).1
  have hρ1 : Torus.IsCk 1 (toFun c) := hρ2.of_le (by norm_num)
  have hmem := (hs_rieszMult s hsd K c hc).1
  have hrr := isRealCoeff_rieszMult s c hreal
  have hR2 : Torus.IsCk 2 (riesz d s c) := (riesz_isCk hd s hs0 hsd 2 K (by simpa using hK) c hc hreal).1
  have hR1 : Torus.IsCk 1 (riesz d s c) := hR2.of_le (by norm_num)
  have hV1 : Torus.IsCk 1 V := hV.of_le (by norm_num)
  have hW2 : Torus.IsCk 2 (Wpot d s V c) := isCk_add V _ hV hR2
  have hcoR : coeffOf (riesz d s c) = rieszMult d s c := by
    have hs' : Summable fun k => ‖rieszMult d s c k‖ := summable_norm_of_memHs K hKd _ hmem
    exact coeffOf_toFun _ hrr hs'
  have hcoρ : coeffOf (toFun c) = c := coeffOf_toFun c hreal hsc
  -- coefficients of ∂_j W
  have hdW : ∀ j : Fin d, coeffOf (Torus.partialDeriv j (Wpot d s V c)) =
      fun k' => derivCoeff j (coeffOf V) k' + gradRieszCoeff d s j c k' := by
    intro j
    funext k
    have e : Torus.partialDeriv j (Wpot d s V c) =
        fun y => Torus.partialDeriv j V y + Torus.partialDeriv j (riesz d s c) y := by
      funext y; exact partialDeriv_add j V _ hV1 hR1 y
    rw [e, coeffOf_add _ _ (continuous_partialDeriv j _ hV1) (continuous_partialDeriv j _ hR1),
      coeffOf_partialDeriv j V hV1, coeffOf_partialDeriv j _ hR1, hcoR]
    rfl
  have hPj : ∀ j : Fin d, Torus.IsCk 1 (fun y => toFun c y * Torus.partialDeriv j (Wpot d s V c) y) :=
    fun j => MFAux.isCk_mul_partialDeriv _ _ hρ1 hW2 j
  have hcoP : ∀ j : Fin d, coeffOf (Torus.partialDeriv j
      (fun y => toFun c y * Torus.partialDeriv j (Wpot d s V c) y)) =
      derivCoeff j (mulCoeff c (fun k' => derivCoeff j (coeffOf V) k' + gradRieszCoeff d s j c k')) := by
    intro j
    rw [coeffOf_partialDeriv j _ (hPj j),
      coeffOf_mul (toFun c) (Torus.partialDeriv j (Wpot d s V c))
        (HRS.PDE.MFProduct.memLp_two_real (MFAux.continuous_of_isCk hρ1))
        (HRS.PDE.MFProduct.memLp_two_real (MFAux.continuous_of_isCk (isCk_one_partialDeriv j _ hW2))),
      hcoρ, hdW j]
  -- the function F
  set F : Torus d → ℝ := fun y => ν * Torus.laplacian (toFun c) y +
    ∑ j, Torus.partialDeriv j (fun y => toFun c y * Torus.partialDeriv j (Wpot d s V c) y) y with hF
  have hlapc : Continuous (Torus.laplacian (toFun c)) := by
    have : Torus.laplacian (toFun c) = fun x => ∑ j, Torus.partialDeriv j (Torus.partialDeriv j (toFun c)) x := by
      funext x; exact laplacian_eq_sum _ hρ2 x
    rw [this]
    exact continuous_finsetSum _ fun j _ =>
      continuous_partialDeriv j _ (isCk_one_partialDeriv j _ hρ2)
  have hc1 : Continuous fun y => ν * Torus.laplacian (toFun c) y := continuous_const.mul hlapc
  have hc2 : Continuous fun y => ∑ j, Torus.partialDeriv j
      (fun y => toFun c y * Torus.partialDeriv j (Wpot d s V c) y) y :=
    continuous_finsetSum _ fun j _ => continuous_partialDeriv j _ (hPj j)
  have hFc : Continuous F := hc1.add hc2
  have hcoF : coeffOf F = mfRhsCoeff d s V ν c := by
    funext k
    rw [hF, coeffOf_add _ _ hc1 hc2,
      coeffOf_const_mul, MFAux.coeffOf_sum Finset.univ _ (fun j => continuous_partialDeriv j _ (hPj j)),
      coeffOf_laplacian _ hρ2, hcoρ]
    simp only [hcoP]
    rfl
  obtain ⟨Cb, -, hCb⟩ := exists_rhs_bound hd s hs0 hsd K hK1 V hVK ν
  have hsF : Summable fun k => ‖coeffOf F k‖ := by
    rw [hcoF]
    exact summable_norm_of_memHs (K - 2) (by linarith) _ (hCb c hc).1
  have := toFun_coeffOf F hFc hsF
  rw [hcoF] at this
  exact congrFun this x

theorem laplacian_add (f g : Torus d → ℝ) (hf : Torus.IsCk 2 f) (hg : Torus.IsCk 2 g) (x : Torus d) :
    Torus.laplacian (fun y => f y + g y) x = Torus.laplacian f x + Torus.laplacian g x := by
  have hfg : Torus.IsCk 2 (fun y => f y + g y) := isCk_add f g hf hg
  rw [laplacian_eq_sum _ hfg, laplacian_eq_sum _ hf, laplacian_eq_sum _ hg, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : Torus.partialDeriv j (fun y => f y + g y) =
      fun y => Torus.partialDeriv j f y + Torus.partialDeriv j g y := by
    funext y
    exact partialDeriv_add j f g (hf.of_le (by norm_num)) (hg.of_le (by norm_num)) y
  rw [e]
  exact partialDeriv_add j _ _ (isCk_one_partialDeriv j f hf) (isCk_one_partialDeriv j g hg) x

theorem norm_euc_le_sum (v : Euc d) : ‖v‖ ≤ ∑ j, |v j| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg fun j _ => abs_nonneg _, ?_⟩
  calc ∑ j, ‖v j‖ ^ 2 = ∑ j, |v j| ^ 2 := by simp
    _ ≤ (∑ j, |v j|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => abs_nonneg _

theorem exists_abs_le_of_continuous (f : Torus d → ℝ) (hf : Continuous f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f x| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  have := hB x (Set.mem_univ x)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem exists_Wpot_bounds (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk 2 V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : Coeff d, MemHs K c → IsRealCoeff c → ∀ x,
      |Torus.laplacian (Wpot d s V c) x| ≤ C * (1 + hsNorm K c) ∧
      ‖Torus.grad (Wpot d s V c) x‖ ≤ C * (1 + hsNorm K c) ∧
      |Wpot d s V c x| ≤ C * (1 + hsNorm K c) := by
  have hV1 : Torus.IsCk 1 V := hV.of_le (by norm_num)
  obtain ⟨A0, hA0, hA0'⟩ := exists_abs_le_of_continuous V (MFAux.continuous_of_isCk hV1)
  have hA1 : ∀ j : Fin d, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |Torus.partialDeriv j V x| ≤ B := fun j =>
    exists_abs_le_of_continuous _ (continuous_partialDeriv j _ hV1)
  choose A1 hA1n hA1b using hA1
  have hlapc : Continuous (Torus.laplacian V) := by
    have : Torus.laplacian V = fun x => ∑ j, Torus.partialDeriv j (Torus.partialDeriv j V) x := by
      funext x; exact laplacian_eq_sum _ hV x
    rw [this]
    exact continuous_finsetSum _ fun j _ => continuous_partialDeriv j _ (isCk_one_partialDeriv j _ hV)
  obtain ⟨A2, hA2, hA2'⟩ := exists_abs_le_of_continuous _ hlapc
  obtain ⟨Cl0, hCl0, hCl0'⟩ := exists_l1_le (d := d) K (by linarith)
  obtain ⟨Cl1, hCl1, hCl1'⟩ := exists_l1_le (d := d) (K + -1) (by linarith)
  obtain ⟨Cl2, hCl2, hCl2'⟩ := exists_l1_le (d := d) (K - 2) (by linarith)
  set rc : ℝ := |rieszConst d s| with hrc
  set Asum : ℝ := ∑ j, A1 j with hAsum
  have hAsum0 : 0 ≤ Asum := Finset.sum_nonneg fun j _ => hA1n j
  set C : ℝ := A0 + A2 + Asum + (Cl0 + d * Cl1 + Cl2) * rc with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, hC0, fun c hc hreal x => ?_⟩
  have hx := hsNorm_nonneg K c
  have hmem := hs_rieszMult s hsd K c hc
  have hrr := isRealCoeff_rieszMult s c hreal
  have hR2 : Torus.IsCk 2 (riesz d s c) :=
    (riesz_isCk hd s hs0 hsd 2 K (by simpa using hK) c hc hreal).1
  have hR1 : Torus.IsCk 1 (riesz d s c) := hR2.of_le (by norm_num)
  -- the three bounds on the potential `g ⋆ ρ`
  have b0 : |riesz d s c x| ≤ Cl0 * rc * hsNorm K c := by
    obtain ⟨h1, h2⟩ := hCl0' _ hmem.1
    refine (HRS.PDE.MFProduct.abs_toFun_le _ h1 x).trans (h2.trans ?_)
    calc Cl0 * hsNorm K (rieszMult d s c) ≤ Cl0 * (rc * hsNorm K c) :=
          mul_le_mul_of_nonneg_left hmem.2 hCl0
      _ = _ := by ring
  have b1 : ∀ j : Fin d, |Torus.partialDeriv j (riesz d s c) x| ≤ Cl1 * rc * hsNorm K c := by
    intro j
    have hp := partialDeriv_toFun j _ K hmem.1 hrr (by linarith)
    have hd1 := hs_deriv j K _ hmem.1
    obtain ⟨h1, h2⟩ := hCl1' _ hd1.1
    show |Torus.partialDeriv j (toFun (rieszMult d s c)) x| ≤ _
    rw [hp]
    refine (HRS.PDE.MFProduct.abs_toFun_le _ h1 x).trans (h2.trans ?_)
    calc Cl1 * hsNorm (K + -1) (derivCoeff j (rieszMult d s c)) ≤ Cl1 * (rc * hsNorm K c) :=
          mul_le_mul_of_nonneg_left (hd1.2.trans hmem.2) hCl1
      _ = _ := by ring
  have b2 : |Torus.laplacian (riesz d s c) x| ≤ Cl2 * rc * hsNorm K c := by
    have hl := (riesz_isCk hd s hs0 hsd 2 K (by simpa using hK) c hc hreal).2 le_rfl x
    rw [hl]
    obtain ⟨hm, hn⟩ := hs_laplaceRiesz s hsd K c hc
    obtain ⟨h1, h2⟩ := hCl2' _ hm
    refine (HRS.PDE.MFProduct.abs_toFun_le _ h1 x).trans (h2.trans ?_)
    calc Cl2 * hsNorm (K - 2) (laplaceRieszCoeff d s c) ≤ Cl2 * (rc * hsNorm K c) :=
          mul_le_mul_of_nonneg_left hn hCl2
      _ = _ := by ring
  have hrc0 : 0 ≤ rc := abs_nonneg _
  have hdn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨?_, ?_, ?_⟩
  · show |Torus.laplacian (fun y => V y + riesz d s c y) x| ≤ _
    rw [laplacian_add V _ hV hR2]
    have := abs_add_le (Torus.laplacian V x) (Torus.laplacian (riesz d s c) x)
    have h3 := hA2' x
    have h4 : 0 ≤ Cl0 * rc := by positivity
    have h5 : 0 ≤ Cl1 * rc := by positivity
    have h6 : 0 ≤ Cl2 * rc := by positivity
    nlinarith [mul_nonneg h4 hx, mul_nonneg h5 hx, mul_nonneg h6 hx, mul_nonneg (mul_nonneg hdn h5) hx]
  · have hg : ‖Torus.grad (Wpot d s V c) x‖ ≤ ∑ j, |Torus.partialDeriv j (Wpot d s V c) x| := by
      refine (norm_euc_le_sum _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
      rw [MFAux.grad_apply]
    refine hg.trans ?_
    have hj : ∀ j : Fin d, |Torus.partialDeriv j (Wpot d s V c) x| ≤ A1 j + Cl1 * rc * hsNorm K c := by
      intro j
      show |Torus.partialDeriv j (fun y => V y + riesz d s c y) x| ≤ _
      rw [partialDeriv_add j V _ hV1 hR1]
      exact (abs_add_le _ _).trans (add_le_add (hA1b j x) (b1 j))
    refine (Finset.sum_le_sum fun j _ => hj j).trans ?_
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h4 : 0 ≤ Cl0 * rc := by positivity
    have h5 : 0 ≤ Cl1 * rc := by positivity
    have h6 : 0 ≤ Cl2 * rc := by positivity
    nlinarith [mul_nonneg h4 hx, mul_nonneg h5 hx, mul_nonneg h6 hx, mul_nonneg (mul_nonneg hdn h5) hx]
  · show |V x + riesz d s c x| ≤ _
    have := abs_add_le (V x) (riesz d s c x)
    have h3 := hA0' x
    have h4 : 0 ≤ Cl0 * rc := by positivity
    have h5 : 0 ≤ Cl1 * rc := by positivity
    have h6 : 0 ≤ Cl2 * rc := by positivity
    nlinarith [mul_nonneg h4 hx, mul_nonneg h5 hx, mul_nonneg h6 hx, mul_nonneg (mul_nonneg hdn h5) hx]
end HRS.PDE.MFApriori
