import HRS.Sections.Sec4
import HRS.Equilibrium.PairCorrection

/-!
# Chunk E, row 4.17: the forcing statistic (definition only)

`forcingStat f X = (√N/2) (D_N(h_f; ν) - E_{ℙ_{N,β}} D_N(h_f; ν))(X)` with `D_N = quadStat`, `h_f = hTransport f`
the transport kernel and `ν = ρβ dx`: the right-hand side of the normal form
(`HRS.Critical.normal_form`, left-hand side), as a function of the configuration.  Along a stationary Gibbs flow
it equals `centeredCommutatorForcing` (`HRS.ME.forcing_eq_forcingStat`).
-/

noncomputable section

namespace HRS.ME

open HRS

/-- `(√N/2) · centered (canonicalGibbs) quadStat (hTransport f)`. -/
def forcingStat {d : ℕ} (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρβ : Torus d → ℝ) {N : ℕ} (f : Torus d → ℝ)
    (X : Config d N) : ℝ :=
  Real.sqrt N / 2 * centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
    (quadStat (hTransport d s f) (withDensityReal ρβ)) X

end HRS.ME

end
