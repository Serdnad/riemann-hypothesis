import Development.AbelianVarietyTheory.Definitions.Divisors.SeminormBallFamily
open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr.DigitSums

theorem mono {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (hB : IsBallFam Λ B) {r r' : ℝ} (h : r ≤ r') {x : G} (hx : x ∈ B r) : x ∈ B r' :=
  hB.mono h hx

end GlobalTheory.VolBr.DigitSums
