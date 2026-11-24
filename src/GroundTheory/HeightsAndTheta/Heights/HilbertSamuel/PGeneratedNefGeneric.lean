module

import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreDim
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedNefGeneric
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedRestrict
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedProductNonneg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem GeneratedNefGeneric.eq_natCast_of_add_one_eq (d : ℕ) (x : WithBot ℕ∞)
    (hform : x + 1 = ((d : ℕ) : WithBot ℕ∞) + 1) : x = d := by
  apply GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq <;> assumption

theorem GeneratedNefGeneric.isProjVarF_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {W : Ideal (MRing ι)} {d : ℕ} (hW : IsArithVar W (d + 1)) :
    IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) d := by
  apply _root_.GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar <;> assumption

theorem GeneratedNefGeneric.proof (hG : GenOnFibres.Statement) (hR : GeneratedRestrict.Statement)
    (hN : GeneratedProductNonneg.Statement) : GeneratedNefGeneric.Statement := by
  intro K _ ι _ Ω _ _ y D a q w _ hw hgen W hW hPW
  classical
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  have hQ : KH.GeneratedV ℚ (KH.genIdeal y) a := (hG K ι Ω y a q w hw hgen).1
  have hWQ : KH.GeneratedV ℚ (W.map (MvPolynomial.map (Int.castRingHom ℚ))) a :=
    hR ℚ K ι _ _ a (Ideal.map_mono hPW) hQ
  have hV : IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) 1 :=
    GeneratedNefGeneric.isProjVarF_map (d := 1) hW
  have h := hN ℚ K ι (fun V _ L => NumbersDVR.intNum ℚ V L) _ 1 (fun _ => a)
    (NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι) hV (fun _ => hWQ)
  unfold genDeg
  convert h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
