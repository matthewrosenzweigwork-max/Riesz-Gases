import HRS.Uniform.Q54Aux6

/-!
# Q54, part 7: the energy form of the forward generator on trigonometric polynomials at a real index (E2)

`gen_form_trig`: for `ν ≥ ν₀ > 0`, `Re ⟨𝓛v, v⟩_{H^a} ≤ C ‖v‖²_{H^a} - (ν₀/2) ‖v‖²_{H^{a+1}}`
(TeX P:eq:energy, L2561-2564: the Schur bound on transport and interaction, absorbed by the diffusion because their order
`θ' = max(1, s+2-d)` is `< 2`).
-/

noncomputable section

open Finset

namespace HRS.Uniform.Q54

open HRS HRS.PDE

variable {d : ℕ}

theorem rpow_le_eps_mul_add {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, 0 ≤ x → x ^ q ≤ ε * x + c := by
  set M : ℝ := (1 / ε) ^ (1 / (1 - q)) with hM
  have hM0 : 0 < M := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨M ^ q, Real.rpow_nonneg hM0.le _, fun x hx => ?_⟩
  rcases le_or_gt x M with h | h
  · have : x ^ q ≤ M ^ q := Real.rpow_le_rpow hx h hq0
    have : 0 ≤ ε * x := by positivity
    linarith
  · have hx0 : 0 < x := lt_trans hM0 h
    have h1 : x ^ (q - 1) ≤ M ^ (q - 1) :=
      Real.rpow_le_rpow_of_nonpos hM0 h.le (by linarith)
    have h2 : M ^ (q - 1) = ε := by
      rw [hM, ← Real.rpow_mul (by positivity)]
      have : 1 / (1 - q) * (q - 1) = -1 := by
        have : (1 - q) ≠ 0 := by linarith
        field_simp
        ring
      rw [this, Real.rpow_neg_one]
      simp
    have h3 : x ^ q = x * x ^ (q - 1) := by
      have := Real.rpow_add_one hx0.ne' (q - 1)
      rw [sub_add_cancel] at this
      rw [this, mul_comm]
    rw [h3]
    have : x * x ^ (q - 1) ≤ x * ε := by rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hx0.le
    have : 0 ≤ M ^ q := Real.rpow_nonneg hM0.le _
    nlinarith

theorem gen_form_trig (s : ℝ) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB) (hBμ : 0 ≤ Bμ)
    (hBV : 0 ≤ BV) (a : ℝ) (hK : (d : ℝ) + |a| + 4 ≤ K) (ν₀ : ℝ) (hν₀ : 0 < ν₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : DynData d) (μ : Torus d → ℝ), GenHyp d s K MB Bμ BV D μ → ν₀ ≤ D.invβ →
      ∀ (n : ℕ) (v : Coeff d), IsTrigPoly n v →
        (hsInner a (forwardGen D μ v) v).re ≤ C * hsNormSq a v - (ν₀ / 2) * hsNormSq (a + 1) v := by
  obtain ⟨A, hA0, hAbd⟩ := genEntry_bound s hsd K MB Bμ BV hMB hBμ hBV
  set e : ℝ := max (s - d + 1) 0 with he
  have he0 : 0 ≤ e := le_max_right _ _
  have he1 : e < 1 := max_lt (by linarith) one_pos
  obtain ⟨C₂, hC₂, hE2⟩ := weighted_E2 (d := d) a (1 + e) (K - 1 - e) A hA0 (by linarith)
    (by
      have : |a - (1 + e) / 2| ≤ |a| + 1 := by
        calc |a - (1 + e) / 2| ≤ |a| + |(1 + e) / 2| := abs_sub _ _
          _ ≤ |a| + 1 := by
            have : |(1 + e) / 2| ≤ 1 := by
              rw [abs_of_nonneg (by linarith)]; linarith
            linarith
      linarith)
  set ε : ℝ := ν₀ / (2 * (C₂ + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨c, hc0, hc⟩ := rpow_le_eps_mul_add (q := (1 + e) / 2) (by linarith) (by linarith) hε0
  refine ⟨ν₀ + C₂ * c, by positivity, fun D μ h hν n v hv => ?_⟩
  have hM := hAbd D μ h
  have key := hE2 (genEntry D μ) hM v (boxFin d n)
  -- notation
  set N : ℝ := hsNormSq a v with hN
  set HL : ℝ := ∑ k ∈ boxFin d n, sobWeight a k * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ‖v k‖ ^ 2 with hHL
  have hHL0 : 0 ≤ HL := Finset.sum_nonneg fun k _ => by
    have := sobWeight_nonnegE a k
    positivity
  have hN' : N = ∑ k ∈ boxFin d n, sobWeight a k * ‖v k‖ ^ 2 := hsNormSq_trig hv a
  have hH1 : hsNormSq (a + 1) v = N + HL := by
    rw [hsNormSq_trig hv, hN', hHL, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sobWeight_one_add]; ring
  -- the pairing is a finite sum
  have hpair : hsInner a (forwardGen D μ v) v =
      ∑ k ∈ boxFin d n, ((sobWeight a k : ℝ) : ℂ) * (forwardGen D μ v k * (starRingEnd ℂ) (v k)) := by
    unfold hsInner
    refine tsum_eq_sum fun k hk => ?_
    rw [eq_zero_of_isTrigPoly hv hk]; simp
  have hre : (hsInner a (forwardGen D μ v) v).re ≤
      -(D.invβ * HL) + ∑ k ∈ boxFin d n, ∑ l ∈ boxFin d n,
        Lattice.jp k ^ (2 * a) * ‖genEntry D μ k l‖ * ‖v k‖ * ‖v l‖ := by
    rw [hpair, Complex.re_sum, hHL, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [forwardGen_trig_eq D μ v hv k]
    set Tk : ℂ := ∑ l ∈ boxFin d n, genEntry D μ k l * v l with hTk
    have hlap : ((D.invβ : ℝ) : ℂ) * laplaceCoeff v k * (starRingEnd ℂ) (v k) =
        ((-(D.invβ * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ‖v k‖ ^ 2) : ℝ) : ℂ) := by
      unfold laplaceCoeff
      have : v k * (starRingEnd ℂ) (v k) = ((‖v k‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc ((D.invβ : ℝ) : ℂ) * (-((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ) * v k) *
            (starRingEnd ℂ) (v k)
          = -(((D.invβ : ℝ) : ℂ) * ((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ)) *
            (v k * (starRingEnd ℂ) (v k)) := by ring
        _ = _ := by rw [this]; push_cast; try ring
    have hw := sobWeight_nonnegE a k
    have hsplit : ((sobWeight a k : ℝ) : ℂ) * ((((D.invβ : ℝ) : ℂ) * laplaceCoeff v k + Tk) *
        (starRingEnd ℂ) (v k)) = ((sobWeight a k : ℝ) : ℂ) *
          ((((D.invβ : ℝ) : ℂ) * laplaceCoeff v k * (starRingEnd ℂ) (v k)) + Tk * (starRingEnd ℂ) (v k)) := by
      ring
    rw [hsplit, hlap, mul_add, Complex.add_re]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
    have h2 : (((sobWeight a k : ℝ) : ℂ) * (Tk * (starRingEnd ℂ) (v k))).re ≤
        ∑ l ∈ boxFin d n, Lattice.jp k ^ (2 * a) * ‖genEntry D μ k l‖ * ‖v k‖ * ‖v l‖ := by
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw, norm_mul,
        Complex.norm_conj]
      have : ‖Tk‖ ≤ ∑ l ∈ boxFin d n, ‖genEntry D μ k l‖ * ‖v l‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul]
      calc sobWeight a k * (‖Tk‖ * ‖v k‖)
          ≤ sobWeight a k * ((∑ l ∈ boxFin d n, ‖genEntry D μ k l‖ * ‖v l‖) * ‖v k‖) := by
            gcongr
        _ = ∑ l ∈ boxFin d n, Lattice.jp k ^ (2 * a) * ‖genEntry D μ k l‖ * ‖v k‖ * ‖v l‖ := by
            rw [Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [sobWeight_eq_jp]; ring
    have h3 : sobWeight a k * (-(D.invβ * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ‖v k‖ ^ 2)) =
        -(D.invβ * (sobWeight a k * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ‖v k‖ ^ 2)) := by ring
    rw [h3]
    linarith
  -- absorption
  have habs : ∑ k ∈ boxFin d n, Lattice.jp k ^ (2 * a + (1 + e)) * ‖v k‖ ^ 2 ≤
      ε * (N + HL) + c * N := by
    have hpt : ∀ k, Lattice.jp k ^ (2 * a + (1 + e)) * ‖v k‖ ^ 2 ≤
        ε * (sobWeight a k * (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ‖v k‖ ^ 2) +
          c * (sobWeight a k * ‖v k‖ ^ 2) := by
      intro k
      have hjp := Torus.jp_pos k
      have h1 := hc (Lattice.jp k ^ 2) (by positivity)
      have h2 : (Lattice.jp k ^ 2) ^ ((1 + e) / 2) = Lattice.jp k ^ (1 + e) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hjp.le]
        congr 1; push_cast; ring
      rw [h2, jp_sq'] at h1
      have h3 : Lattice.jp k ^ (2 * a + (1 + e)) = sobWeight a k * Lattice.jp k ^ (1 + e) := by
        rw [sobWeight_eq_jp, Real.rpow_add hjp]
      rw [h3]
      have hw := sobWeight_nonnegE a k
      have hv2 : 0 ≤ ‖v k‖ ^ 2 := sq_nonneg _
      calc sobWeight a k * Lattice.jp k ^ (1 + e) * ‖v k‖ ^ 2
          = (sobWeight a k * ‖v k‖ ^ 2) * Lattice.jp k ^ (1 + e) := by ring
        _ ≤ (sobWeight a k * ‖v k‖ ^ 2) * (ε * (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) + c) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := by ring
    have e1 : ∑ k ∈ boxFin d n, sobWeight a k * (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ‖v k‖ ^ 2 =
        N + HL := by
      rw [hN', hHL, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    refine (Finset.sum_le_sum fun k _ => hpt k).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e1, ← hN']
  -- conclusion
  have hC2ε : C₂ * ε ≤ ν₀ / 2 := by
    rw [hε]
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hNnn : 0 ≤ N := hsNormSq_nonnegE a v
  calc (hsInner a (forwardGen D μ v) v).re
      ≤ -(D.invβ * HL) + ∑ k ∈ boxFin d n, ∑ l ∈ boxFin d n,
        Lattice.jp k ^ (2 * a) * ‖genEntry D μ k l‖ * ‖v k‖ * ‖v l‖ := hre
    _ ≤ -(D.invβ * HL) + C₂ * (ε * (N + HL) + c * N) := by
        refine add_le_add le_rfl (key.trans (mul_le_mul_of_nonneg_left habs hC₂))
    _ ≤ (ν₀ + C₂ * c) * N - (ν₀ / 2) * (N + HL) := by
        have h1 : ν₀ * HL ≤ D.invβ * HL := mul_le_mul_of_nonneg_right hν hHL0
        have h2 : C₂ * ε * (N + HL) ≤ ν₀ / 2 * (N + HL) :=
          mul_le_mul_of_nonneg_right hC2ε (by linarith)
        nlinarith
    _ = _ := by rw [hH1]

end HRS.Uniform.Q54
