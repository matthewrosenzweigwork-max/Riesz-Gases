import HRS.MC.QRVocab
import HRS.MC.QRPHdAux13
import HRS.MC.QRPHdAux12

/-!
# Packet HD (`qrs_hd_commutator_tail_proof`)

Proof plan (all steps formalised in `QRPHdAux1 .. QRPHdAux13`).

1. *Density-free coefficients* (`WCI.wci_wick_eq`): `A_{ab} = wickCoeff (ρ dx) h_{∇e_κ} a b = ∫ e_a(x) ∫ h(x,y) e_b(y) dy dx`
   for every bounded `ρ`.
2. *Fourier coefficients of the Riesz force* (`hdF_coeff`, Aux3): `∫ e_{-c} ∂_i g = 2πi c_i ĝ(c)` by dominated convergence
   from the heat regularisations (`integral_mode_heat_component`).  With `H_λ(x,y) = ∑_i 2πiλ_i (e_λ(x)-e_λ(y)) ∂_ig(x-y)`:
   `∫_x e_α ∫_y H_λ e_β = 1_{α+λ+β=0} K(λ,β)`, `K(λ,β) = (2πi)² λ·(q(β) - q(λ+β))`, `q(c) = ĝ(c) c`.
3. *Band structure* (Aux4-5, 9-10): `e_a = ∑_± c_± e_{±a}` (`realMode_cplx`), `∇e_κ = ∑_± c_± 2πi(±κ) e_{±κ}`, hence
   `A_{ab}` is a sum of 8 terms supported on `σa + εκ + τb = 0`, and
   `A_{ab}² ≤ 8 ∑_{σ,ε,τ} 1[b = φ(a)] (4π²|κ|)² D(σa, εκ)²`,  `D(α,λ) = ‖q α - q(α+λ)‖`.
4. *Bounds on `D`* (Aux2): `D(α,λ) ≤ C|λ||α|^{s-d}` for `|α| ≥ 2|λ|` (mean value inequality for `x ↦ |x|^{s-d}x`);
   crude bound `‖q c‖ = κ₀ |c|^{s-d+1}` otherwise.
5. *Lattice sums* (Aux1, 6-8, 12): `∑_{|α|_∞>L} D² ≲ |λ|² L^{-(d-2s)}` for `L ≥ 2|λ|`; `∑_α D² ≲ |λ|^{1+2s}` always; hence
   `∑_{α outside the cube (or α+λ outside)} D² ≲ |λ|^{d+1} L^{-(d-2s)}` for all `L ≥ 1` (for `L < 2|λ|` use the total mass).
6. *Assembly* (Aux11, 13): sum over pairs `(a,b) ∉ F×F`, using that `b = φ(a)` is determined by `a`, and the cube `⊂ F`.
   Result: `tailHS ≤ 64 (4π²|κ|)² C |κ|^{d+1} L^{-(d-2s)} ≤ C' ⟨κ⟩^{d+3} L^{-(d-2s)}`, and `L = 0` (`F = ∅`) from the total mass.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace MC

namespace QRSpec

namespace Hd

open HRS.Sec7

variable {d : ℕ}

theorem hd_enorm_le_jp (k : Lattice d) : Lattice.enorm k ≤ Lattice.jp k := HRS.enorm_le_jp k

theorem hd_rpow_enorm_le_jp (k : Lattice d) (e : ℝ) (he : 0 ≤ e) :
    Lattice.enorm k ^ e ≤ Lattice.jp k ^ e :=
  Real.rpow_le_rpow (hd_enorm_nonneg k) (hd_enorm_le_jp k) he

theorem hd_tailHS_eq (A : NonzeroLattice d → NonzeroLattice d → ℝ) (F : Finset (NonzeroLattice d)) :
    tailHS A F = ∑' p : NonzeroLattice d × NonzeroLattice d,
      (if p.1 ∈ F ∧ p.2 ∈ F then (0 : ℝ) else A p.1 p.2 ^ 2) := by
  unfold tailHS
  refine tsum_congr fun p => ?_
  by_cases h : p.1 ∈ F ∧ p.2 ∈ F <;> simp [h]

/-- (Packet HD, `qrs_hd_commutator_tail`.)  See the specification in `HRS.MC.QRSpec`. -/
theorem qrs_hd_commutator_tail_proof (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) / 2) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : Torus d → ℝ, IsProbDensity ρ → ∀ Mρ : ℝ, (∀ x, ρ x ≤ Mρ) →
      ∀ (k : NonzeroLattice d) (L : ℕ), 1 ≤ L →
        (Summable fun p : NonzeroLattice d × NonzeroLattice d =>
          wickCoeff (withDensityReal ρ) (hTransport d s (Torus.realMode k)) p.1 p.2 ^ 2) ∧
        tailHS (wickCoeff (withDensityReal ρ) (hTransport d s (Torus.realMode k))) ∅ ≤
          C * Lattice.jp k.1 ^ ((d : ℝ) + 3) ∧
        ∀ F : Finset (NonzeroLattice d), (∀ a : NonzeroLattice d, (∀ i, |a.1 i| ≤ (L : ℤ)) → a ∈ F) →
          tailHS (wickCoeff (withDensityReal ρ) (hTransport d s (Torus.realMode k))) F ≤
            C * Lattice.jp k.1 ^ ((d : ℝ) + 3) * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) := by
  have hsd2 : 2 * s < d := by linarith
  have hs1 : s + 1 < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨CB, hCB0, hB⟩ := hd_totalB hd hs0 hsd2
  obtain ⟨CO, hCO0, hO⟩ := hd_outBound hd hs0 hsd2
  set P := 64 * (4 * Real.pi ^ 2) ^ 2 with hP
  have hP0 : 0 < P := by positivity
  refine ⟨P * (CB + CO) + 1, by positivity, fun ρ _ Mρ hM κ L hL => ?_⟩
  classical
  set el := Lattice.enorm κ.1 with hel
  have hel1 : 1 ≤ el := hd_enorm_ge_one κ.2
  have hel0 : 0 < el := by linarith
  have hjp : el ≤ Lattice.jp κ.1 := hd_enorm_le_jp κ.1
  have hjp0 : 0 < Lattice.jp κ.1 := lt_of_lt_of_le hel0 hjp
  have hen : ∀ ε : Bool, Lattice.enorm (hdsg ε • κ.1) = el := fun ε => hd_enorm_smul_sg ε κ.1
  have hnz : ∀ ε : Bool, hdsg ε • κ.1 ≠ 0 := by
    intro ε h
    have := hen ε
    rw [h] at this
    have h0 : Lattice.enorm (0 : Lattice d) = 0 := by rw [hd_enorm_def, hd_toEuc_zero, norm_zero]
    linarith
  have hd3 : el ^ ((d : ℝ) + 3) ≤ Lattice.jp κ.1 ^ ((d : ℝ) + 3) := hd_rpow_enorm_le_jp κ.1 _ (by positivity)
  have hp : 0 < (d : ℝ) - 2 * s := by linarith
  -- the exponent bookkeeping
  have hK : (4 * Real.pi ^ 2 * el) ^ 2 = (4 * Real.pi ^ 2) ^ 2 * el ^ 2 := by ring
  have hpow : el ^ 2 * el ^ ((d : ℝ) + 1) = el ^ ((d : ℝ) + 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hel0]; congr 1; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · -- summability of the squared coefficients (F = ∅)
    have h := (hd_tail_gen hd hs0 hs1 (ρ := ρ) (Λ := Mρ) hM κ (fun _ => False)
      (fun _ _ => Iff.rfl) ∅ (fun a ha => ha.elim) (B := CB * el ^ (1 + 2 * s)) (fun ε => by
        have := hB (hdsg ε • κ.1) (hnz ε)
        rw [hen ε] at this
        have e : hdOut d s (hdsg ε • κ.1) (fun _ => False) = fun α => hdD d s (hdsg ε • κ.1) α ^ 2 := by
          funext α; simp [hdOut]
        rw [e]
        exact this)).1
    simpa using h
  · have h := (hd_tail_gen hd hs0 hs1 (ρ := ρ) (Λ := Mρ) hM κ (fun _ => False)
      (fun _ _ => Iff.rfl) ∅ (fun a ha => ha.elim) (B := CB * el ^ (1 + 2 * s)) (fun ε => by
        have := hB (hdsg ε • κ.1) (hnz ε)
        rw [hen ε] at this
        have e : hdOut d s (hdsg ε • κ.1) (fun _ => False) = fun α => hdD d s (hdsg ε • κ.1) α ^ 2 := by
          funext α; simp [hdOut]
        rw [e]
        exact this)).2
    rw [hd_tailHS_eq]
    refine h.trans ?_
    have e1 : el ^ 2 * el ^ (1 + 2 * s) ≤ Lattice.jp κ.1 ^ ((d : ℝ) + 3) := by
      refine le_trans ?_ hd3
      rw [← Real.rpow_natCast, ← Real.rpow_add hel0]
      exact Real.rpow_le_rpow_of_exponent_le hel1 (by push_cast; linarith)
    calc 64 * (4 * Real.pi ^ 2 * el) ^ 2 * (CB * el ^ (1 + 2 * s))
        = P * CB * (el ^ 2 * el ^ (1 + 2 * s)) := by rw [hK, hP]; ring
      _ ≤ P * CB * Lattice.jp κ.1 ^ ((d : ℝ) + 3) := mul_le_mul_of_nonneg_left e1 (by positivity)
      _ ≤ (P * (CB + CO) + 1) * Lattice.jp κ.1 ^ ((d : ℝ) + 3) := by
          have : 0 ≤ Lattice.jp κ.1 ^ ((d : ℝ) + 3) := Real.rpow_nonneg hjp0.le _
          have h2 : P * CB ≤ P * (CB + CO) + 1 := by nlinarith
          exact mul_le_mul_of_nonneg_right h2 this
  · intro F hF
    have h := (hd_tail_gen hd hs0 hs1 (ρ := ρ) (Λ := Mρ) hM κ (hdCu L)
      (fun σ x => hdCu_smul L σ x) F hF
      (B := CO * el ^ ((d : ℝ) + 1) * (L : ℝ) ^ (-((d : ℝ) - 2 * s))) (fun ε => by
        have := hO (hdsg ε • κ.1) (hnz ε) L hL
        rw [hen ε] at this
        exact this)).2
    rw [hd_tailHS_eq]
    refine h.trans ?_
    have hLp : 0 ≤ (L : ℝ) ^ (-((d : ℝ) - 2 * s)) := Real.rpow_nonneg (by positivity) _
    calc 64 * (4 * Real.pi ^ 2 * el) ^ 2 * (CO * el ^ ((d : ℝ) + 1) * (L : ℝ) ^ (-((d : ℝ) - 2 * s)))
        = P * CO * (el ^ 2 * el ^ ((d : ℝ) + 1)) * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) := by rw [hK, hP]; ring
      _ = P * CO * el ^ ((d : ℝ) + 3) * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) := by rw [hpow]
      _ ≤ P * CO * Lattice.jp κ.1 ^ ((d : ℝ) + 3) * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) := by
          gcongr
      _ ≤ (P * (CB + CO) + 1) * Lattice.jp κ.1 ^ ((d : ℝ) + 3) * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) := by
          have : 0 ≤ Lattice.jp κ.1 ^ ((d : ℝ) + 3) * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) :=
            mul_nonneg (Real.rpow_nonneg hjp0.le _) hLp
          have h2 : P * CO ≤ P * (CB + CO) + 1 := by nlinarith
          calc _ = (P * CO) * (Lattice.jp κ.1 ^ ((d : ℝ) + 3) * (L : ℝ) ^ (-((d : ℝ) - 2 * s))) := by ring
            _ ≤ (P * (CB + CO) + 1) * (Lattice.jp κ.1 ^ ((d : ℝ) + 3) * (L : ℝ) ^ (-((d : ℝ) - 2 * s))) :=
                mul_le_mul_of_nonneg_right h2 this
            _ = _ := by ring

end Hd

end QRSpec

end MC

end HRS

end
