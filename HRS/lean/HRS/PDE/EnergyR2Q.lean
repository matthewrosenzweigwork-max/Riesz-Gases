import HRS.PDE.EnergyR2Fn
import HRS.PDE.GStructure
import HRS.PDE.EnergyR2Kernel

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.R2Aux

variable {d : ℕ}

abbrev PIdx (d : ℕ) := Fin d ⊕ (Fin d × Fin d)

def pvec : PIdx d → Euc d
  | Sum.inl i => EuclideanSpace.single i 1
  | Sum.inr p => EuclideanSpace.single p.1 1 + EuclideanSpace.single p.2 1

def pcoef (q : Euc d) : PIdx d → ℝ
  | Sum.inl i => -(q i * ∑ j, q j)
  | Sum.inr p => q p.1 * q p.2 / 2

theorem inner_single_toEuc (i : Fin d) (k : Lattice d) :
    inner ℝ (EuclideanSpace.single i (1 : ℝ)) (Lattice.toEuc k) = (k i : ℝ) := by
  simp [inner_toEuc_eq]

theorem inner_single_add_toEuc (i j : Fin d) (k : Lattice d) :
    inner ℝ (EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j (1 : ℝ)) (Lattice.toEuc k) =
      (k i : ℝ) + (k j : ℝ) := by
  rw [inner_add_left, inner_single_toEuc, inner_single_toEuc]

theorem poly_identity (q u : Fin d → ℝ) (c g : ℝ) :
    (c * ∑ i, q i * u i) ^ 2 * g =
      ∑ i, -(q i * ∑ j, q j) * ((c * u i) ^ 2 * g) +
        ∑ i, ∑ j, q i * q j / 2 * ((c * (u i + u j)) ^ 2 * g) := by
  have h1 : ∀ i, -(q i * ∑ j, q j) * ((c * u i) ^ 2 * g) =
      ∑ j, (-(q i * q j) * ((c * u i) ^ 2 * g)) := by
    intro i
    rw [← Finset.sum_mul, Finset.sum_neg_distrib, ← Finset.mul_sum]
  simp_rw [h1]
  have h2 : (c * ∑ i, q i * u i) ^ 2 * g = ∑ i, ∑ j, c ^ 2 * g * (q i * q j * (u i * u j)) := by
    rw [mul_pow, sq (∑ i, q i * u i), Finset.sum_mul_sum]
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h2, ← Finset.sum_add_distrib]
  have h3 : ∑ i, ∑ j, c ^ 2 * g * (q i * q j * (u j ^ 2 - u i ^ 2) / 2) = 0 := by
    have : ∑ i, ∑ j, c ^ 2 * g * (q i * q j * (u j ^ 2 - u i ^ 2) / 2) =
        -∑ i, ∑ j, c ^ 2 * g * (q i * q j * (u j ^ 2 - u i ^ 2) / 2) := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    linarith
  have h4 : ∑ i, (∑ j, ((-(q i * q j) * ((c * u i) ^ 2 * g)) +
        q i * q j / 2 * ((c * (u i + u j)) ^ 2 * g))) =
      ∑ i, ∑ j, (c ^ 2 * g * (q i * q j * (u i * u j)) +
        c ^ 2 * g * (q i * q j * (u j ^ 2 - u i ^ 2) / 2)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h5 : ∑ i, (∑ j, (-(q i * q j) * ((c * u i) ^ 2 * g)) +
        ∑ j, q i * q j / 2 * ((c * (u i + u j)) ^ 2 * g)) =
      ∑ i, (∑ j, ((-(q i * q j) * ((c * u i) ^ 2 * g)) +
        q i * q j / 2 * ((c * (u i + u j)) ^ 2 * g))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_add_distrib]
  rw [h5, h4]
  simp only [Finset.sum_add_distrib]
  rw [h3, add_zero]

theorem symbolK_polarize (s : ℝ) (q : Euc d) (k : Lattice d) :
    symbolK d s q k = ∑ ι, pcoef q ι * symbolK d s (pvec ι) k := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [pcoef, pvec, symbolK]
  simp only [inner_single_toEuc, inner_single_add_toEuc]
  rw [inner_toEuc_eq]
  exact poly_identity (fun i => q i) (fun i => (k i : ℝ)) (2 * Real.pi) (rieszCoeff d s k)


theorem abs_pcoef_le (hd : 1 ≤ d) (q : Euc d) (hq : ‖q‖ ≤ 1) (ι : PIdx d) :
    |pcoef q ι| ≤ d := by
  have hqi : ∀ i, |q i| ≤ 1 := fun i => by
    have := PiLp.norm_apply_le q i
    rw [Real.norm_eq_abs] at this
    linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rcases ι with i | p
  · simp only [pcoef, abs_neg, abs_mul]
    have h1 : |∑ j, q j| ≤ d := by
      calc |∑ j, q j| ≤ ∑ j, |q j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin d, (1 : ℝ) := Finset.sum_le_sum fun j _ => hqi j
        _ = d := by simp
    calc |q i| * |∑ j, q j| ≤ 1 * d :=
          mul_le_mul (hqi i) h1 (abs_nonneg _) zero_le_one
      _ = d := one_mul _
  · simp only [pcoef, abs_div, abs_mul]
    have := mul_le_mul (hqi p.1) (hqi p.2) (abs_nonneg _) zero_le_one
    rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith

theorem symbolForm_polarize (s : ℝ) (q : Euc d) (u v : Torus d → ℝ)
    (hsum : ∀ ι : PIdx d, Summable fun k => ((symbolK d s (pvec ι) k : ℝ) : ℂ) *
      (coeffOf u k * conj (coeffOf v k))) :
    symbolForm (symbolK d s q) u v =
      ∑ ι, pcoef q ι * symbolForm (symbolK d s (pvec ι)) u v := by
  unfold symbolForm bilinForm
  have e : ∀ k, ((symbolK d s q k : ℝ) : ℂ) * (coeffOf u k * conj (coeffOf v k)) =
      ∑ ι, ((pcoef q ι : ℝ) : ℂ) * (((symbolK d s (pvec ι) k : ℝ) : ℂ) *
        (coeffOf u k * conj (coeffOf v k))) := by
    intro k
    rw [symbolK_polarize s q k]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun ι _ => by ring
  simp_rw [e]
  rw [Summable.tsum_finsetSum (fun ι _ => (hsum ι).mul_left _), Complex.re_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [tsum_mul_left, Complex.re_ofReal_mul]


/-- Lemma C.3(iii) (weighted symmetrisation), uniformly over unit-ball directions `q`
(polarisation of the finitely many symbols `𝔪_{e_i}`, `𝔪_{e_i+e_j}`). -/
theorem weighted_uniform (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ C : ℝ, ∀ (q : Euc d), ‖q‖ ≤ 1 → ∀ (L La Lm Lw : ℝ) (a w : Torus d → ℝ),
      (∀ x, 0 ≤ a x) → IsC11 L a → Torus.IsLipschitz La a →
      Torus.IsLipschitz Lm (fun x => Real.sqrt (a x)) → Torus.IsLipschitz Lw w →
      MemSobolev (thetaOrder d s / 2) w →
      |symbolForm (symbolK d s q) (fun x => a x * w x) w -
        symbolForm (symbolK d s q) (fun x => Real.sqrt (a x) * w x)
          (fun x => Real.sqrt (a x) * w x)| ≤
        C * (Lm ^ 2 + Torus.supNorm (fun x => Real.sqrt (a x)) ^ 2) * l2NormSq w := by
  have hθ0 : 0 < thetaOrder d s := by unfold thetaOrder; linarith
  have hθ2 : thetaOrder d s < 2 := by unfold thetaOrder; have : (s : ℝ) < d := hsd; linarith
  have hd1 : 1 ≤ d := hd
  have hH : ∀ ι : PIdx d, IsHomogSymbol (thetaOrder d s) (symbolK d s (pvec ι)) :=
    fun ι => symbolK_isHomogSymbol hd s hs0 hs1 hsd _
  have hK : ∀ ι : PIdx d, ∃ 𝔨 : Torus d → ℝ, IsLevyKernel (thetaOrder d s) (symbolK d s (pvec ι)) 𝔨 :=
    fun ι => quadratic_toolbox_kernel hd _ hθ0 hθ2 _ (hH ι)
  choose 𝔨 h𝔨 using hK
  have hW : ∀ ι : PIdx d, ∃ C : ℝ, ∀ (L La Lm Lw : ℝ) (a w : Torus d → ℝ), (∀ x, 0 ≤ a x) →
      IsC11 L a → Torus.IsLipschitz La a → Torus.IsLipschitz Lm (fun x => Real.sqrt (a x)) →
      Torus.IsLipschitz Lw w →
      |symbolForm (symbolK d s (pvec ι)) (fun x => a x * w x) w -
        symbolForm (symbolK d s (pvec ι)) (fun x => Real.sqrt (a x) * w x)
          (fun x => Real.sqrt (a x) * w x)| ≤
        C * (Lm ^ 2 + Torus.supNorm (fun x => Real.sqrt (a x)) ^ 2) * l2NormSq w := by
    intro ι
    obtain ⟨C, hC⟩ := quadratic_toolbox_weighted hd _ hθ0 hθ2 _ (hH ι) (𝔨 ι) (h𝔨 ι)
    refine ⟨C, fun L La Lm Lw a w ha hC11 hLa hLm hLw => ?_⟩
    obtain ⟨-, -, h3⟩ := hC L La Lm Lw a w ha hC11 hLa hLm hLw
    exact h3
  choose CC hCC using hW
  have hB : ∀ ι : PIdx d, ∃ C : ℝ, ∀ u v : Torus d → ℝ, MemSobolev (thetaOrder d s / 2) u →
      MemSobolev (thetaOrder d s / 2) v →
      Summable fun k => ((symbolK d s (pvec ι) k : ℝ) : ℂ) * (coeffOf u k * conj (coeffOf v k)) := by
    intro ι
    obtain ⟨C, hC⟩ := quadratic_toolbox_basic _ hθ0 hθ2 _ (hH ι)
    exact ⟨C, fun u v hu hv => (hC u v hu hv).2.2.1⟩
  choose CB hCB using hB
  obtain ⟨CP, hCP⟩ := product_toolbox_frac (d := d) hd1 (thetaOrder d s / 2) (by linarith)
    (by linarith)
  refine ⟨d * ∑ ι, |CC ι|, fun q hq L La Lm Lw a w ha hC11 hLa hLm hLw hw => ?_⟩
  have hu : MemSobolev (thetaOrder d s / 2) (fun x => a x * w x) := (hCP La a hLa w hw).1
  have hv : MemSobolev (thetaOrder d s / 2) (fun x => Real.sqrt (a x) * w x) :=
    (hCP Lm _ hLm w hw).1
  rw [symbolForm_polarize s q _ _ (fun ι => hCB ι _ _ hu hw),
    symbolForm_polarize s q _ _ (fun ι => hCB ι _ _ hv hv), ← Finset.sum_sub_distrib]
  have hR : 0 ≤ (Lm ^ 2 + Torus.supNorm (fun x => Real.sqrt (a x)) ^ 2) * l2NormSq w := by
    refine mul_nonneg (by positivity) ?_
    unfold l2NormSq
    exact integral_nonneg fun x => sq_nonneg _
  calc |∑ ι, (pcoef q ι * symbolForm (symbolK d s (pvec ι)) (fun x => a x * w x) w -
        pcoef q ι * symbolForm (symbolK d s (pvec ι)) (fun x => Real.sqrt (a x) * w x)
          (fun x => Real.sqrt (a x) * w x))|
      ≤ ∑ ι, |pcoef q ι * (symbolForm (symbolK d s (pvec ι)) (fun x => a x * w x) w -
        symbolForm (symbolK d s (pvec ι)) (fun x => Real.sqrt (a x) * w x)
          (fun x => Real.sqrt (a x) * w x))| := by
        refine Finset.abs_sum_le_sum_abs _ _ |>.trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun ι _ => ?_
        rw [mul_sub]
    _ ≤ ∑ ι, (d : ℝ) * (|CC ι| * ((Lm ^ 2 + Torus.supNorm (fun x => Real.sqrt (a x)) ^ 2) *
          l2NormSq w)) := by
        refine Finset.sum_le_sum fun ι _ => ?_
        rw [abs_mul]
        refine mul_le_mul (abs_pcoef_le hd1 q hq ι) ?_ (abs_nonneg _) (Nat.cast_nonneg d)
        refine (hCC ι L La Lm Lw a w ha hC11 hLa hLm hLw).trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_abs_self _) hR
    _ = _ := by
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        ring


theorem sqrt_isLipschitz {a : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L) (ha : ∀ x, 0 ≤ a x)
    (hC11 : IsC11 L a) :
    Torus.IsLipschitz (Real.sqrt (L / 2)) (fun x => Real.sqrt (a x)) := by
  have h := HRS.sqrt_lipschitz (E := Euc d) (Torus.lift a) hC11.1 (fun y => ha _) L hL hC11.2
  have h2 := isLipschitz_of_lipschitzWith (a := fun x => Real.sqrt (a x)) h
  rwa [Real.coe_toNNReal _ (Real.sqrt_nonneg _)] at h2

theorem supNorm_sqrt_sq_le {a : Torus d → ℝ} {A : ℝ} (ha : ∀ x, 0 ≤ a x) (hA : ∀ x, a x ≤ A) :
    Torus.supNorm (fun x => Real.sqrt (a x)) ^ 2 ≤ A := by
  have hA0 : 0 ≤ A := (ha 0).trans (hA 0)
  have h : Torus.supNorm (fun x => Real.sqrt (a x)) ≤ Real.sqrt A := by
    refine Real.iSup_le (fun x => ?_) (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hA x)
  calc _ ≤ Real.sqrt A ^ 2 := pow_le_pow_left₀ (Real.iSup_nonneg fun _ => norm_nonneg _) h 2
    _ = A := Real.sq_sqrt hA0

/-- Lemma C.3(iii) in the form used below: `a` a nonnegative `C^{1,1}` function with
`0 ≤ a ≤ A`, `w` a `C¹` function in `H^{θ/2}`. -/
theorem weighted_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Euc d), ‖q‖ ≤ 1 → ∀ (L A : ℝ) (a w : Torus d → ℝ), 0 ≤ L →
      (∀ x, 0 ≤ a x) → (∀ x, a x ≤ A) → IsC11 L a → Torus.IsCk 1 w →
      MemSobolev (thetaOrder d s / 2) w →
      |symbolForm (symbolK d s q) (fun x => a x * w x) w -
        symbolForm (symbolK d s q) (fun x => Real.sqrt (a x) * w x)
          (fun x => Real.sqrt (a x) * w x)| ≤ C * (L / 2 + A) * l2NormSq w := by
  obtain ⟨C, hC⟩ := weighted_uniform hd s hs0 hs1 hsd
  refine ⟨|C|, abs_nonneg _, fun q hq L A a w hL ha hA hC11 hw1 hw => ?_⟩
  have hLa := isLipschitz_of_cbNorm hC11.1
  have hLm := sqrt_isLipschitz hL ha hC11
  have hLw := isLipschitz_of_cbNorm hw1
  refine (hC q hq _ _ _ _ a w ha hC11 hLa hLm hLw hw).trans ?_
  have h1 : Real.sqrt (L / 2) ^ 2 = L / 2 := Real.sq_sqrt (by positivity)
  have h2 := supNorm_sqrt_sq_le ha hA
  have hl2 : 0 ≤ l2NormSq w := by
    unfold l2NormSq
    exact integral_nonneg fun x => sq_nonneg _
  rw [h1]
  have h3 : 0 ≤ L / 2 + Torus.supNorm (fun x => Real.sqrt (a x)) ^ 2 := by positivity
  calc C * (L / 2 + Torus.supNorm (fun x => Real.sqrt (a x)) ^ 2) * l2NormSq w
      ≤ |C| * (L / 2 + Torus.supNorm (fun x => Real.sqrt (a x)) ^ 2) * l2NormSq w := by
        gcongr
        exact le_abs_self _
    _ ≤ |C| * (L / 2 + A) * l2NormSq w := by
        gcongr


theorem continuous_of_isLipschitz {a : Torus d → ℝ} {L : ℝ} (h : Torus.IsLipschitz L a) :
    Continuous a := (ProdAux.prodHyp_of_lipschitz h).cont

/-- Lemma C.4 together with the kernel fact `rieszGrad_pairing_symmetrized`, in Fourier form:
the pairing `Re ∑_k conj(ŵ(k)) (2πi k_i ĝ(k)) (a ŵ)^(k)` is bounded by `C ‖a‖_{C^{0,1}} ‖w‖²`. -/
theorem sameFunction_bound (hd : 1 ≤ d) (s : ℝ) (hsd : s < d) (hK : R2KernelFacts d s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin d) (La A : ℝ) (a : Torus d → ℝ), Torus.IsLipschitz La a →
      (∀ x, |a x| ≤ A) → ∀ (n : ℕ) (w : Coeff d), IsRealCoeff w → IsTrigPoly n w →
      |(∑ k ∈ boxFin d n, conj (w k) * (((2 * Real.pi * Complex.I * (k i : ℂ)) *
          ((rieszCoeff d s k : ℝ) : ℂ)) * mulCoeff (coeffOf a) w k)).re| ≤
        C * (A + |La| * Real.sqrt d) * hsNormSq 0 w := by
  obtain ⟨C4, hC4⟩ := periodic_same_function hd s hsd
  obtain ⟨C1, hC1⟩ := hK.bound
  have hodd := periodicRieszGrad_neg (d := d) (s := s) hsd
  have hsm := hK.smooth
  refine ⟨|C4| * max C1 0, by positivity, fun i La A a ha hA n w hw hwt => ?_⟩
  set v : Euc d := EuclideanSpace.single i (1 : ℝ) with hv
  set wf := toFun w with hwf
  have hcw : coeffOf wf = w := coeffOf_toFun_trig hw hwt
  have hw1 : Torus.IsCk 1 wf := isCk_toFun_trig hw hwt 1
  have hwcont : Continuous wf := continuous_toFun_trig hw hwt
  have hacont : Continuous a := continuous_of_isLipschitz ha
  have hP := hK.pairing v La a ha n wf hw1 (by rw [hcw]; exact hwt)
  -- the Fourier side as a box sum
  have hcoef : coeffOf (fun x => a x * wf x) = mulCoeff (coeffOf a) w := by
    rw [coeffOf_mul a wf (memLp_of_continuous_real hacont) (memLp_of_continuous_real hwcont), hcw]
  rw [hcoef, hcw] at hP
  have hbox : (∑' k, ((2 * Real.pi * Complex.I * (inner ℝ v (Lattice.toEuc k) : ℂ)) *
        ((rieszCoeff d s k : ℝ) : ℂ)) * (mulCoeff (coeffOf a) w k * conj (w k))).re =
      (∑ k ∈ boxFin d n, conj (w k) * (((2 * Real.pi * Complex.I * (k i : ℂ)) *
          ((rieszCoeff d s k : ℝ) : ℂ)) * mulCoeff (coeffOf a) w k)).re := by
    congr 1
    rw [tsum_eq_sum (s := boxFin d n)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [hv, inner_single_toEuc]
      push_cast
      ring
    · intro k hk
      rw [eq_zero_of_isTrigPoly hwt hk]; simp
  rw [← hbox, hP]
  -- Lemma C.4
  set κ : Torus d → ℝ := fun z => inner ℝ v (periodicRieszGrad d s z) with hκ
  have hκodd : ∀ z, κ (-z) = -κ z := fun z => by simp [hκ, hodd z]
  have hκsm : Torus.IsSmoothOffZero κ := by
    unfold Torus.IsSmoothOffZero at hsm ⊢
    have : Torus.lift κ = fun x => (innerSL ℝ v) (Torus.lift (periodicRieszGrad d s) x) := rfl
    rw [this]
    exact (innerSL ℝ v).contDiff.comp_contDiffOn hsm
  have hκb : ∀ z : Torus d, z ≠ 0 → |κ z| ≤ max C1 0 * (1 + Torus.tdist z 0 ^ (-s - 1)) := by
    intro z hz
    have h1 := hC1 z hz
    have h2 : |κ z| ≤ ‖periodicRieszGrad d s z‖ := by
      have := abs_real_inner_le_norm v (periodicRieszGrad d s z)
      have hvn : ‖v‖ = 1 := by simp [hv, PiLp.norm_single]
      rw [hvn, one_mul] at this
      exact this
    have h3 : 0 ≤ Torus.tdist z 0 ^ (-s - 1) := Real.rpow_nonneg (norm_nonneg _) _
    calc |κ z| ≤ C1 * (Torus.tdist z 0 ^ (-s - 1) + 1) := h2.trans h1
      _ ≤ max C1 0 * (Torus.tdist z 0 ^ (-s - 1) + 1) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
      _ = _ := by ring
  have hwL2 : MemLp wf 2 volume := memLp_of_continuous_real hwcont
  obtain ⟨-, -, -, h4⟩ := hC4 κ (max C1 0) hκodd hκsm hκb La a wf ha hwL2
  have hl2 : l2NormSq wf = hsNormSq 0 w := by
    rw [l2NormSq_eq_hsNormSq hwcont, hcw]
  rw [hl2] at h4
  refine h4.trans ?_
  have hc01 := c01Norm_le ha hA
  have hn0 : 0 ≤ hsNormSq 0 w := hsNormSq_nonnegE 0 w
  have hK0 : 0 ≤ max C1 0 := le_max_right _ _
  calc C4 * max C1 0 * Torus.c01Norm a * hsNormSq 0 w
      ≤ |C4| * max C1 0 * (A + |La| * Real.sqrt d) * hsNormSq 0 w := by
        have hc0 : 0 ≤ Torus.c01Norm a := by
          unfold Torus.c01Norm
          refine add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _) ?_
          exact Real.iSup_nonneg fun p => by positivity
        gcongr
        · exact le_abs_self _
    _ = _ := by ring

end HRS.PDE.R2Aux
