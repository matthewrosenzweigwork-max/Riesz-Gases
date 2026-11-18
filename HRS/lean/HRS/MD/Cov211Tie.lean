import HRS.MD.Cov211
import HRS.Main.HeadlineEquilibrium

/-!
Tie: `HRS.MD.Cov211.covariance_obstruction_proof` has the type of the frozen statement
`HRS.Main.covariance_obstruction` (Prop. 2.11).  The definitions `rateLaw`, `rateGaussian` of the
proof file are copies (same body) of `HRS.Main.rateLaw`, `HRS.Main.rateGaussian`; this file imports
the spec module (which still contains `sorry`s), the proof files do not.
-/

example := (@HRS.MD.Cov211.covariance_obstruction_proof : type_of% @HRS.Main.covariance_obstruction)
