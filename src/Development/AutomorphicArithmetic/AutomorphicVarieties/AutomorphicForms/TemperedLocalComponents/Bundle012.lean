module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolvableEquivalenceOfBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Deplete
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.KerDiff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.CentChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.CuspZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.EigOfLow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.HolTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PNewform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

open NumberField UpperTheory.V.Af

theorem UpperTheory.V.Af.solDescent :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.SolDescent := by
  intro H F₀ F M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF hsol hplus hM l _ ι n hn r μ hr hirr hμ hs ⟨c, P, hc, hP⟩
  have hM' : IsCMField M := hM.resolve_left fun h => by
    obtain ⟨v⟩ : Nonempty (InfinitePlace M) := inferInstance
    exact (InfinitePlace.not_isReal_iff_isComplex.2 ((isTotallyComplex_of_algebra F M).isComplex v)) (h.isReal v)
  exact Z.Bc.solC H H.cyc F M Ω hsol hF hM' l ι n hn r hr hirr ⟨F₀, _, _, _, _, inferInstance, inferInstance, hplus.1, μ, c, P, hμ, hs, hc, hP⟩
end

section

theorem UpperTheory.V.Af.repNewform :
    UpperTheory.V.Published.RepNewform := by
  have hVolMap : UpperTheory.V.Af.Rs.VolMap := UpperTheory.V.Af.Rs.volMap
  have hStripFub : UpperTheory.V.Af.Rs.StripFub := UpperTheory.V.Af.Rs.stripFub hVolMap
  have hStripIm : UpperTheory.V.Af.Rs.StripIm := UpperTheory.V.Af.Rs.stripIm hVolMap
  have hFdFin : UpperTheory.V.Af.Rs.FdFin := UpperTheory.V.Af.Rs.fdFin hStripIm hVolMap
  have hFdNull : UpperTheory.V.Af.Rs.FdNull := UpperTheory.V.Af.Rs.fdNull hVolMap
  have hFdPos : UpperTheory.V.Af.Rs.FdPos := UpperTheory.V.Af.Rs.fdPos hVolMap
  have hStripInt : UpperTheory.V.Af.Rs.StripInt := UpperTheory.V.Af.Rs.stripInt hStripIm
  have hFdCount : UpperTheory.V.Af.Rs.FdCount := UpperTheory.V.Af.Rs.fdCount hFdNull
  have hUnfM : UpperTheory.V.Af.Rs.UnfM := UpperTheory.V.Af.Rs.unfM hFdFin hFdCount
  have hRowBij : UpperTheory.V.Af.Rs.RowBij := UpperTheory.V.Af.Rs.rowBij
  have hRowRep : UpperTheory.V.Af.Rs.RowRep := UpperTheory.V.Af.Rs.rowRep
  have hUnfold : UpperTheory.V.Af.Rs.Unfold := UpperTheory.V.Af.Rs.unfold hFdFin hUnfM hRowBij
  have hGcdSum : UpperTheory.V.Af.Rs.GcdSum := UpperTheory.V.Af.Rs.gcdSum
  have hKerBd : UpperTheory.V.Af.Rs.KerBd := UpperTheory.V.Af.Rs.kerBd
  have hKerLow : UpperTheory.V.Af.Rs.KerLow := UpperTheory.V.Af.Rs.kerLow
  have hKerDiff : UpperTheory.V.Af.Rs.KerDiff := UpperTheory.V.Af.Rs.kerDiff
  have hWTop : UpperTheory.V.Af.Rs.WTop := UpperTheory.V.Af.Rs.wTop
  have hZDiff : UpperTheory.V.Af.Rs.ZDiff := UpperTheory.V.Af.Rs.zDiff hKerBd hKerDiff hWTop
  have hZLow : UpperTheory.V.Af.Rs.ZLow := UpperTheory.V.Af.Rs.zLow hKerBd hKerLow hWTop
  have hZInt : UpperTheory.V.Af.Rs.ZInt := UpperTheory.V.Af.Rs.zInt hFdFin hKerBd hWTop
  have hSwap : UpperTheory.V.Af.Rs.Swap := UpperTheory.V.Af.Rs.swap hFdFin hKerBd hWTop
  have hTBdd : UpperTheory.V.Af.Rs.TBdd := UpperTheory.V.Af.Rs.tBdd hFdFin hZDiff hZInt
  have hTTop : UpperTheory.V.Af.Rs.TTop := UpperTheory.V.Af.Rs.tTop hFdFin hFdPos hWTop hZDiff hZLow hZInt
  have hClsEx : UpperTheory.V.Af.Rs.ClsEx := UpperTheory.V.Af.Rs.clsEx hRowBij
  have hClsProp : UpperTheory.V.Af.Rs.ClsProp := UpperTheory.V.Af.Rs.clsProp hRowRep
  have hLBd : UpperTheory.V.Af.Rs.LBd := UpperTheory.V.Af.Rs.lBd
  have hNicePet : UpperTheory.V.Af.Rs.NicePet := UpperTheory.V.Af.Rs.nicePet
  have hPetChar : UpperTheory.V.Af.Rs.PetChar := UpperTheory.V.Af.Rs.petChar
  have hPars : UpperTheory.V.Af.Rs.Pars := UpperTheory.V.Af.Rs.pars
  have hMelSum : UpperTheory.V.Af.Rs.MelSum := UpperTheory.V.Af.Rs.melSum
  have hRankSum : UpperTheory.V.Af.Rs.RankSum := UpperTheory.V.Af.Rs.rankSum hStripFub hStripInt hNicePet hPars hMelSum
  have hRankin : UpperTheory.V.Af.Rs.Rankin := UpperTheory.V.Af.Rs.rankin hStripFub hStripInt hNicePet hPars hRankSum
  have hArFact : UpperTheory.V.Af.Rs.ArFact := UpperTheory.V.Af.Rs.arFact
  have hArSum : UpperTheory.V.Af.Rs.ArSum := UpperTheory.V.Af.Rs.arSum
  have hCmp : UpperTheory.V.Af.Rs.Cmp := UpperTheory.V.Af.Rs.cmp hRankSum hRankin hArFact hArSum
  have hDeplete : UpperTheory.V.Af.Rs.Deplete := UpperTheory.V.Af.Rs.deplete
  have hSl2Two : UpperTheory.V.Af.Rn.Sl2Two := UpperTheory.V.Af.Rn.sl2Two
  have hLowTwo : UpperTheory.V.Af.Rn.LowTwo := UpperTheory.V.Af.Rn.lowTwo hSl2Two
  have hHolTwo : UpperTheory.V.Af.Rn.HolTwo := UpperTheory.V.Af.Rn.holTwo hLowTwo
  have hNoLow : UpperTheory.V.Af.Rn.NoLow := UpperTheory.V.Af.Rn.noLow UpperTheory.V.Af.Rn.centChar
  have hSatHerm : UpperTheory.V.Af.Rn.SatHerm := UpperTheory.V.Af.Rn.satHerm
  have hHermOf : UpperTheory.V.Af.Rn.HermOf := UpperTheory.V.Af.Rn.hermOf
  have hEigOfLow : UpperTheory.V.Af.Rn.EigOfLow := UpperTheory.V.Af.Rn.eigOfLow UpperTheory.V.Af.Rn.centChar
  have hUnitTw : UpperTheory.V.Af.Rn.UnitTw := UpperTheory.V.Af.Rn.unitTw
  have hEvPl : UpperTheory.V.Af.Rn.EvPl := UpperTheory.V.Af.Rn.evPl
  have hNewHerm : UpperTheory.V.Af.Rn.NewHerm := UpperTheory.V.Af.Rn.newHerm UpperTheory.V.Af.newformRep hUnitTw hHermOf hSatHerm
  have hPolyInj : UpperTheory.V.Af.Rn.PolyInj := UpperTheory.V.Af.Rn.polyInj
  have hTEq : UpperTheory.V.Af.Rs.TEq := UpperTheory.V.Af.Rs.tEq hRowBij hStripInt hUnfold hGcdSum hKerBd hSwap hLBd
  have hCore : UpperTheory.V.Af.Rs.Core := UpperTheory.V.Af.Rs.core hTBdd hTTop hClsEx hClsProp hTEq hLBd hNicePet hPetChar hCmp
  have hCharEq2 : UpperTheory.V.Af.Rs.CharEq2 := UpperTheory.V.Af.Rs.charEq2 hCore hDeplete
  exact UpperTheory.V.Af.Rn.repNewform_of
    (UpperTheory.V.Af.Rn.newAE_of hUnitTw hHermOf (UpperTheory.V.Af.Rn.holAll_of UpperTheory.V.Br.holVec hHolTwo hNoLow) hEigOfLow hSatHerm hEvPl hNewHerm
      UpperTheory.V.Br.minNew hCharEq2)
    hEvPl hPolyInj (fun w => (UpperTheory.V.Af.Nf.places w).1.pos) UpperTheory.V.Af.newformRep UpperTheory.V.Af.strongMultOneReal
end
