import HRS.Torus.Sobolev

/-!
# S8.6 `finite_noise`: the Hilbert-valued weighted Bessel inequality (Pro FR01) (S86b)

For a `C^r` function `G : ℝ^d → K` into a real inner product space, `ℤ^d`-periodic, and an orthonormal family `b`
of `K`, the scalar Fourier coefficients `c_n(k)` of `y ↦ ⟨b n, G y⟩` satisfy, for every finite set `F` of indices,
`∑_{n∈F} ∑_k (1+|k|²)^r |c_n(k)|² ≤ ∑_{l ≤ r} C(r,l) d^l B_l²`,  `B_l = sup_y ‖D^l G(y)‖`.
Route: scalar Parseval for the coordinate derivatives `D^l G_n (e_{m_1},…,e_{m_l})`, Bessel in `K`, and the identity
`∑_m ∏_s k_{m_s}² = |k|^{2l}`; only finite sums over `n` are used.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS HRS.Torus

variable {d : ℕ}

theorem s86_parseval (φ : Torus d → ℝ) (hφ : Continuous φ) :
    HasSum (fun k : Lattice d => ‖fcoef φ k‖ ^ 2) (∫ x, φ x ^ 2) := by
  have hI : Integrable φ := hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hM : MemLp φ 2 volume := hφ.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := hasSum_sq_coeff hM
  convert h using 2 with n
  exact (norm_sq_coeff hI n)

theorem s86_dot_single (k : Lattice d) (i : Fin d) :
    Lattice.dot k (EuclideanSpace.single i (1 : ℝ)) = (k i : ℝ) := by
  classical
  unfold Lattice.dot
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem s86_sum_tuple (k : Lattice d) (l : ℕ) :
    ∑ m : Fin l → Fin d, ∏ s, ((k (m s) : ℝ)) ^ 2 = (Lattice.enorm k ^ 2) ^ l := by
  have h1 : Lattice.enorm k ^ 2 = ∑ i : Fin d, ((k i : ℝ)) ^ 2 := by
    unfold Lattice.enorm Lattice.toEuc
    rw [EuclideanSpace.norm_sq_eq]
    simp
  rw [h1]
  symm
  calc (∑ i : Fin d, ((k i : ℝ)) ^ 2) ^ l = ∏ _s : Fin l, ∑ i : Fin d, ((k i : ℝ)) ^ 2 := by simp
    _ = ∑ p ∈ Fintype.piFinset (fun _ : Fin l => (Finset.univ : Finset (Fin d))),
          ∏ s, ((k (p s) : ℝ)) ^ 2 :=
        Finset.prod_univ_sum (fun _ : Fin l => (Finset.univ : Finset (Fin d)))
          (fun (_ : Fin l) (j : Fin d) => ((k j : ℝ)) ^ 2)
    _ = ∑ m : Fin l → Fin d, ∏ s, ((k (m s) : ℝ)) ^ 2 := by rw [Fintype.piFinset_univ]

theorem s86_fcoef_deriv_norm_sq {G : Euc d → ℝ} (hG : Per G) {n : ℕ} (hd : ContDiff ℝ n G)
    (k : Lattice d) {l : ℕ} (hl : l ≤ n) (m : Fin l → Fin d) :
    ‖fcoef (descend (fun y => iteratedFDeriv ℝ l G y
        (fun s => EuclideanSpace.single (m s) (1 : ℝ)))) k‖ ^ 2 =
      (2 * Real.pi) ^ (2 * l) * (∏ s, ((k (m s) : ℝ)) ^ 2) * ‖fcoef (descend G) k‖ ^ 2 := by
  rw [fcoef_iteratedFDeriv hG hd k l hl]
  simp only [s86_dot_single]
  rw [norm_mul, norm_mul, norm_pow, norm_prod]
  have h2 : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by simp [Complex.norm_I]
  rw [h2]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [mul_pow, mul_pow, ← pow_mul]
  have e : (∏ x, |((k (m x) : ℤ) : ℝ)|) ^ 2 = ∏ x, ((k (m x) : ℝ)) ^ 2 := by
    rw [← Finset.prod_pow]; simp only [sq_abs]
  rw [e, mul_comm l 2]

theorem s86_vector_bessel (r : ℕ) {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {ι : Type*} (b : ι → K) (hb : Orthonormal ℝ b) (G : Euc d → K)
    (hper : ∀ (y : Euc d) (n : Lattice d), G (y + Lattice.toEuc n) = G y) (hG : ContDiff ℝ r G)
    (B : ℕ → ℝ) (hB : ∀ l ≤ r, ∀ y, ‖iteratedFDeriv ℝ l G y‖ ≤ B l) (F : Finset ι) :
    (∀ n ∈ F, Summable fun k : Lattice d => (1 + Lattice.enorm k ^ 2) ^ r *
        ‖fcoef (descend fun y => ⟪b n, G y⟫) k‖ ^ 2) ∧
    ∑ n ∈ F, ∑' k : Lattice d, (1 + Lattice.enorm k ^ 2) ^ r *
        ‖fcoef (descend fun y => ⟪b n, G y⟫) k‖ ^ 2 ≤
      ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ) * (d : ℝ) ^ l * B l ^ 2 := by
  classical
  set Gn : ι → Euc d → ℝ := fun n y => ⟪b n, G y⟫ with hGn
  have hGnper : ∀ n, Per (Gn n) := fun n y k => by simp only [hGn, hper y k]
  have hGnd : ∀ n, ContDiff ℝ r (Gn n) := fun n =>
    (innerSL ℝ (b n)).contDiff.comp hG
  -- the coordinate derivatives
  set ψ : ι → (l : ℕ) → (Fin l → Fin d) → Euc d → ℝ := fun n l m y =>
    iteratedFDeriv ℝ l (Gn n) y (fun s => EuclideanSpace.single (m s) (1 : ℝ)) with hψ
  have hψeq : ∀ n l, l ≤ r → ∀ m y, ψ n l m y =
      ⟪b n, iteratedFDeriv ℝ l G y (fun s => EuclideanSpace.single (m s) (1 : ℝ))⟫ := by
    intro n l hl m y
    have h := ContinuousLinearMap.iteratedFDeriv_comp_left (innerSL ℝ (b n)) (hG.contDiffAt (x := y))
      (i := l) (by exact_mod_cast hl)
    simp only [hψ, hGn]
    have : (fun y => ⟪b n, G y⟫) = (innerSL ℝ (b n)) ∘ G := by
      funext y; simp
    rw [this, h]
    simp
  have hψper : ∀ n l m, Per (ψ n l m) := fun n l m =>
    (hGnper n).iteratedFDeriv_apply _
  have hψcont : ∀ n l, l ≤ r → ∀ m, Continuous (ψ n l m) := fun n l hl m =>
    continuous_iteratedFDeriv_apply (hGnd n) hl _
  have hψc' : ∀ n l, l ≤ r → ∀ m, Continuous (descend (ψ n l m)) := fun n l hl m =>
    continuous_descend (hψper n l m) (hψcont n l hl m)
  -- pointwise Bessel bound
  have hbessel : ∀ l, l ≤ r → ∀ (m : Fin l → Fin d) (y : Euc d),
      ∑ n ∈ F, ψ n l m y ^ 2 ≤ B l ^ 2 := by
    intro l hl m y
    have h1 := hb.sum_inner_products_le (iteratedFDeriv ℝ l G y
      (fun s => EuclideanSpace.single (m s) (1 : ℝ))) (s := F)
    have h2 : ‖iteratedFDeriv ℝ l G y (fun s => EuclideanSpace.single (m s) (1 : ℝ))‖ ≤ B l := by
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
      have : ∏ s, ‖(EuclideanSpace.single (m s) (1 : ℝ) : Euc d)‖ = 1 := by simp
      rw [this, mul_one]
      exact hB l hl y
    have h3 : 0 ≤ ‖iteratedFDeriv ℝ l G y
        (fun s => EuclideanSpace.single (m s) (1 : ℝ))‖ := norm_nonneg _
    calc ∑ n ∈ F, ψ n l m y ^ 2
        = ∑ n ∈ F, ‖⟪b n, iteratedFDeriv ℝ l G y
            (fun s => EuclideanSpace.single (m s) (1 : ℝ))⟫‖ ^ 2 := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hψeq n l hl m y, Real.norm_eq_abs, sq_abs]
      _ ≤ ‖iteratedFDeriv ℝ l G y (fun s => EuclideanSpace.single (m s) (1 : ℝ))‖ ^ 2 := h1
      _ ≤ B l ^ 2 := pow_le_pow_left₀ h3 h2 2
  -- Parseval
  have hpars : ∀ n l, l ≤ r → ∀ m, HasSum (fun k : Lattice d => ‖fcoef (descend (ψ n l m)) k‖ ^ 2)
      (∫ x, descend (ψ n l m) x ^ 2) := fun n l hl m => s86_parseval _ (hψc' n l hl m)
  have hint : ∀ l, l ≤ r → ∀ m : Fin l → Fin d,
      ∑ n ∈ F, ∫ x : Torus d, descend (ψ n l m) x ^ 2 ≤ B l ^ 2 := by
    intro l hl m
    rw [← integral_finsetSum]
    · have : ∫ x : Torus d, ∑ n ∈ F, descend (ψ n l m) x ^ 2 ≤ ∫ _x : Torus d, B l ^ 2 := by
        refine integral_mono ?_ (integrable_const _) fun x => ?_
        · exact integrable_finsetSum _ fun n _ => (((hψc' n l hl m).pow 2).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
        · simp only [descend]
          exact hbessel l hl m _
      simpa using this
    · intro n _
      exact ((hψc' n l hl m).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- the pointwise (in k) majorant
  set c : ι → Lattice d → ℝ := fun n k => ‖fcoef (descend (Gn n)) k‖ ^ 2 with hc
  have hmaj : ∀ n k, (1 + Lattice.enorm k ^ 2) ^ r * c n k ≤
      ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ) *
        ∑ m : Fin l → Fin d, ‖fcoef (descend (ψ n l m)) k‖ ^ 2 := by
    intro n k
    have hexp : (1 + Lattice.enorm k ^ 2) ^ r = ∑ l ∈ Finset.range (r + 1),
        (Lattice.enorm k ^ 2) ^ l * (r.choose l : ℝ) := by
      rw [add_comm, add_pow]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp
    rw [hexp, Finset.sum_mul]
    refine Finset.sum_le_sum fun l hl => ?_
    have hlr : l ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hs : ∑ m : Fin l → Fin d, ‖fcoef (descend (ψ n l m)) k‖ ^ 2 =
        (2 * Real.pi) ^ (2 * l) * (Lattice.enorm k ^ 2) ^ l * c n k := by
      have : ∀ m : Fin l → Fin d, ‖fcoef (descend (ψ n l m)) k‖ ^ 2 =
          (2 * Real.pi) ^ (2 * l) * (∏ s, ((k (m s) : ℝ)) ^ 2) * c n k := fun m =>
        s86_fcoef_deriv_norm_sq (hGnper n) (hGnd n) k hlr m
      simp_rw [this]
      rw [← Finset.sum_mul, ← Finset.mul_sum, s86_sum_tuple]
    rw [hs]
    have h2pi : (1 : ℝ) ≤ (2 * Real.pi) ^ (2 * l) :=
      one_le_pow₀ (by nlinarith [Real.pi_gt_three])
    have hc0 : 0 ≤ c n k := sq_nonneg _
    have he0 : 0 ≤ (Lattice.enorm k ^ 2) ^ l := by positivity
    have hch : (0 : ℝ) ≤ (r.choose l : ℝ) := Nat.cast_nonneg _
    calc (Lattice.enorm k ^ 2) ^ l * (r.choose l : ℝ) * c n k
        = (r.choose l : ℝ) * ((Lattice.enorm k ^ 2) ^ l * c n k) := by ring
      _ ≤ (r.choose l : ℝ) * ((2 * Real.pi) ^ (2 * l) * (Lattice.enorm k ^ 2) ^ l * c n k) := by
          refine mul_le_mul_of_nonneg_left ?_ hch
          nlinarith [mul_nonneg he0 hc0]
  have hnn : ∀ n k, 0 ≤ (1 + Lattice.enorm k ^ 2) ^ r * c n k := fun n k => by
    have : 0 ≤ c n k := sq_nonneg _
    positivity
  have hmajS : ∀ n, Summable fun k : Lattice d => ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ) *
        ∑ m : Fin l → Fin d, ‖fcoef (descend (ψ n l m)) k‖ ^ 2 := by
    intro n
    refine summable_sum fun l hl => ?_
    have hlr : l ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    exact (summable_sum fun m _ => (hpars n l hlr m).summable).mul_left _
  have hsum : ∀ n, Summable fun k : Lattice d => (1 + Lattice.enorm k ^ 2) ^ r * c n k := fun n =>
    Summable.of_nonneg_of_le (hnn n) (hmaj n) (hmajS n)
  refine ⟨fun n _ => hsum n, ?_⟩
  calc ∑ n ∈ F, ∑' k : Lattice d, (1 + Lattice.enorm k ^ 2) ^ r * c n k
      ≤ ∑ n ∈ F, ∑' k : Lattice d, ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ) *
          ∑ m : Fin l → Fin d, ‖fcoef (descend (ψ n l m)) k‖ ^ 2 :=
        Finset.sum_le_sum fun n _ => (hsum n).tsum_le_tsum (hmaj n) (hmajS n)
    _ = ∑ n ∈ F, ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ) *
          ∑ m : Fin l → Fin d, ∫ x, descend (ψ n l m) x ^ 2 := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Summable.tsum_finsetSum fun l hl => ?_]
        · refine Finset.sum_congr rfl fun l hl => ?_
          have hlr : l ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
          rw [tsum_mul_left, Summable.tsum_finsetSum fun m _ => (hpars n l hlr m).summable]
          congr 1
          exact Finset.sum_congr rfl fun m _ => (hpars n l hlr m).tsum_eq
        · have hlr : l ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
          exact (summable_sum fun m _ => (hpars n l hlr m).summable).mul_left _
    _ = ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ) *
          ∑ m : Fin l → Fin d, ∑ n ∈ F, ∫ x, descend (ψ n l m) x ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ) * ∑ _m : Fin l → Fin d, B l ^ 2 := by
        refine Finset.sum_le_sum fun l hl => ?_
        have hlr : l ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum fun m _ => hint l hlr m
    _ = ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ) * (d : ℝ) ^ l * B l ^ 2 := by
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring

end HRS.MS.FinNoise
