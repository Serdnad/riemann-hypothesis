import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialClosedPointsOfOriginClosedFibre
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

theorem divConstClosedPts_of_divConstOrigin :
    GlobalTheory.VertUnits.DivConstOrigin → GlobalTheory.VertUnits.DivConstClosedPts := by
  intro hKO T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hne
  exact GlobalTheory.LocAcyc.Translate.polynomialClaim_of_origin (fun T O _ _ _ => DivConst T O)
    hKO T O hT P φ hφ hsh hPm hne

end GlobalTheory.VertUnits
