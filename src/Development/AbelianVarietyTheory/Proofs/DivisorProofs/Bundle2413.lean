module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle589
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle379
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle286
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle420
public import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrI
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupJetsChart
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle069
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle082
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle272
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle616
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.IncomingBounds.Bundle001
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
open Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

namespace GlobalTheory.BigTop.Fun.IntTie

theorem gBig_dep {Q : GP} (h : GBig @Q) :
    GBig fun {D} {T} {Lc} {sc} G μ₀ C x b => 1 ≤ sc.cDep ∧ sc.cDep ≤ C ∧ @Q D T Lc sc G μ₀ C x b := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨max CF0 1, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  exact ⟨max C0 CF, x0, fun C hC D large₂ he hx hR T Lc μ hL G =>
    ⟨le_of_max_le_right hCF, le_of_max_le_right hC, h C (le_of_max_le_left hC) D large₂ he hx hR T Lc μ hL G⟩⟩

theorem gBig_and {Q Q' : GP} (h : GBig @Q) (h' : GBig @Q') :
    GBig fun {D} {T} {Lc} {sc} G μ₀ C x b => @Q D T Lc sc G μ₀ C x b ∧ @Q' D T Lc sc G μ₀ C x b := by
  obtain ⟨a, h⟩ := h
  obtain ⟨a', h'⟩ := h'
  refine ⟨max a a', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h'⟩ := h' ε CF (le_of_max_le_right hCF)
  exact ⟨max C0 C1, max x0 x1, fun C hC D large₂ he hx hR T Lc μ hL G =>
    ⟨h C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ hL G,
     h' C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ hL G⟩⟩

theorem integralNormBound_mono {K : Type} [Field K] [NumberField K] {ι : Type} {dl : Formalism.PairingDivisionLocalBalance.Pl K → ℝ} {zA zA' : ι → K}
    {B B' : ℝ} (h : NonArchimedeanDefectBound dl zA zA' B) (hB : B ≤ B') : NonArchimedeanDefectBound dl zA zA' B' :=
  ⟨h.1, fun F => (h.2.1 F).trans hB, h.2.2⟩

end GlobalTheory.BigTop.Fun.IntTie

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

theorem _root_.GlobalTheory.T.isPolynomialFockThetaVector_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ P : PolF D WW.rank A.rank, IsFockVec W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) := by
  first | exact @GlobalTheory.BottomIPData.isFockVec_bottom | exact GlobalTheory.BottomIPData.isFockVec_bottom | (intros; apply GlobalTheory.BottomIPData.isFockVec_bottom <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2 Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigTop.Fun

theorem sqRatio_mem_of {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T)
    (W : G.Weil) (S : GridChoice W Set.univ) (ρ : RealMatch W) (c : Fin D.R.m → Fin D.R.m → T → ℂ)
    (hstd : IsStdChar D W.ψ (-1)) (hN : NumbersIn D.what₂.embLL S μ₀)
    (hC : ∀ i j t, SquareNonzero W S.B ρ t i j ∧ c i j t ≠ 0) (hK : ∀ i j t, IsSquareConst W S.B ρ t i j (c i j t))
    (hLN : ∀ i j : Fin D.R.m, (∀ t, ∃ Λ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ ∧
      ∀ s : ℤ, 1 - (GlobalTheory.SqTop.e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → Λ s ≠ 0))
    (hTX : ∀ i j : Fin D.R.m, ∃ (A A' WW : HSp D) (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X ∧ X.IsConst W.ψ W.θ c0)
    (hTW : ∀ (i j : Fin D.R.m) (t : T) (c c₀ : ℂ) (A A' WW : HSp D) (X : Tri T A A' WW)
      (c0 : T → ℂ) (Λ Λ₀ : ℂ → ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c → SquareNonzero W S.B ρ μ₀ i j →
      IsSquareConst W S.B ρ μ₀ i j c₀ → IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 → GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ →
      GlobalTheory.CMVal.IsHeckeL (nuH G μ₀ i j) Λ₀ → ∃ u : Fin (pp D j + qq D j) → ℂ,
        (∀ k, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (u k) 1) ∧
        ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧
          c / c₀ * ∏ k ∈ range (qq D j), Λ (eTop D i j + k + 1 : ℕ) / Λ₀ (eTop D i j + k + 1 : ℕ) =
            D.what₂.embLL ζ * (∏ k, u k) * (c0 t / c0 μ₀) *
              ∏ k ∈ range (pp D j), Λ (eTop D i j + qq D j - k : ℕ) / Λ₀ (eTop D i j + qq D j - k : ℕ))
    (hBF : ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X →
      ∃ lam : T → ℂ, GlobalTheory.ConstRatio.Factor X W.ψ W.θ lam)
    (i j : Fin D.R.m) (t : T) : c i j t / c i j μ₀ ∈ Set.range D.what₂.embLL := by
  have hF : ∀ z : ℂ, z ∈ Set.range D.what₂.embLL ↔ z ∈ D.what₂.embLL.fieldRange := fun z => Iff.rfl

  obtain ⟨A₀, A₀', WW₀, X₀, -, hX₀, -⟩ := hTX i j
  obtain ⟨A, A', WW, X, hX, hS⟩ := hN.bottom i j ⟨A₀, A₀', WW₀, X₀, hX₀⟩
  obtain ⟨lam, hlam⟩ := hBF i j A A' WW X hX
  have hI := hX.is
  have hi' : ∀ t P g, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P g) X.fd' X.m' := fun t P g =>
    (GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D W.ψ false A' WW _ _ (X.ω' t) X.m' X.fd' _ (hI.weil' t) (GlobalTheory.ConstRatio.posDef_of_std hX.std')
      hI.meas'.1 hI.meas'.2 (GlobalTheory.Chain.InnerSteps.theta_pureTensorO hI.isVac.1 hI.isVac.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
        (GlobalTheory.ConstRatio.theta_f hI t).2 P)).1 g
  have hr := hS.rationalSums (fun t P g => hlam.2.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1 t P g) hi'
  have hrat := GlobalTheory.ConstRatio.ratIn_of_definite hI (GlobalTheory.ConstRatio.posDef_of_std hX.std) (GlobalTheory.ConstRatio.posDef_of_std hX.std')
    (GlobalTheory.ConstRatio.posDef_of_std hX.stdW) hlam hr μ₀
  haveI : Nonempty T := ⟨μ₀⟩
  have hcst : X.IsConst W.ψ W.θ lam := hlam.isConst

  obtain ⟨Λ, hΛ, hΛne⟩ := hLN i j t
  obtain ⟨Λ₀, hΛ₀, hΛ₀ne⟩ := hLN i j μ₀
  obtain ⟨u, hu, ζ, -, heq⟩ := hTW i j t (c i j t) (c i j μ₀) A A' WW X lam Λ Λ₀ (hC i j t).1 (hK i j t) (hC i j μ₀).1
    (hK i j μ₀) hX hcst hΛ hΛ₀
  rw [hF]
  obtain ⟨hn1, -, -, hn4, -, -, -, hn8, hn9⟩ := Model.tower_numbers (D := D) i j
  have hne : ∀ L : ℂ → ℂ, (∀ s : ℤ, 1 - (e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → L s ≠ 0) →
      ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D i j → L (n : ℂ) ≠ 0 := fun L h n h1 h2 => by
    have := h n (by omega) (by exact_mod_cast h2)
    simpa using this
  have hs : ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D i j →
      Λ (n : ℂ) / Λ₀ (n : ℂ) ∈ D.what₂.embLL.fieldRange ∧ Λ (n : ℂ) / Λ₀ (n : ℂ) ≠ 0 := fun n h1 h2 =>
    ⟨(hF _).1 (hN.ratios i j t Λ Λ₀ hΛ hΛ₀ n h1 (by omega) (hne Λ₀ hΛ₀ne n h1 h2)),
      div_ne_zero (hne Λ hΛne n h1 h2) (hne Λ₀ hΛ₀ne n h1 h2)⟩
  have hP1 : ∀ k ∈ range (qq D j), Λ ((eTop D i j + k + 1 : ℕ) : ℂ) / Λ₀ ((eTop D i j + k + 1 : ℕ) : ℂ) ∈
      D.what₂.embLL.fieldRange ∧ Λ ((eTop D i j + k + 1 : ℕ) : ℂ) / Λ₀ ((eTop D i j + k + 1 : ℕ) : ℂ) ≠ 0 := fun k hk =>
    hs _ (by omega) (by have := mem_range.1 hk; omega)
  have hP2 : ∀ k ∈ range (pp D j), Λ ((eTop D i j + qq D j - k : ℕ) : ℂ) / Λ₀ ((eTop D i j + qq D j - k : ℕ) : ℂ) ∈
      D.what₂.embLL.fieldRange := fun k hk =>
    (hs _ (by have := mem_range.1 hk; omega) (by omega)).1
  have hU : (∏ k, u k) ∈ D.what₂.embLL.fieldRange := prod_mem fun k _ => by
    obtain ⟨b, g, g', -, -, h⟩ := hu k
    rw [h, mul_one]
    exact RingHom.mem_fieldRange.2 ⟨_, rfl⟩
  have hl : lam t / lam μ₀ ∈ D.what₂.embLL.fieldRange := by
    obtain ⟨-, y, hy⟩ := hrat t
    exact RingHom.mem_fieldRange.2 ⟨_, hy⟩
  rw [eq_div_of_mul_eq (prod_ne_zero_iff.2 fun k hk => (hP1 k hk).2) heq]
  exact div_mem (mul_mem (mul_mem (mul_mem (RingHom.mem_fieldRange.2 ⟨ζ, rfl⟩) hU) hl) (prod_mem hP2))
    (prod_mem fun k hk => (hP1 k hk).1)


end GlobalTheory.BigTop.Fun

end
end

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
open GlobalTheory.CharRealise
open Formalism.DivisionValues

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)



theorem splitPartFace_baseLevel_indices_eq (i : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (p.S false).Iw i p.P.A3.A.μ0 w = ((p.R.toRealDat.toCx (F2 p)).data (F2 p).cr false).Iw i p.P.A3.A.μ0 w := by
  show ((p.R.toCx3 p.F).data p.F.cr false).Iw i _ w = _
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl



theorem splitPartFace_baseLevel_jw_eq (i : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    jw ((lv (p.F.fc (p.R.toCx3 p.F).zs) false).HT i p.P.A3.A.μ0) w ((lv (p.F.fc (p.R.toCx3 p.F).zs) false).Tl i p.P.A3.A.μ0) =
      jw ((lv ((F2 p).fc (p.R.toRealDat.toCx (F2 p)).zs) false).HT i p.P.A3.A.μ0) w
        ((lv ((F2 p).fc (p.R.toRealDat.toCx (F2 p)).zs) false).Tl i p.P.A3.A.μ0) := by
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl



theorem w1_of_inW1_split_part (C CH : ℝ) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (h : p.R.toRealDat.NonzeroIndexPlace (F2 p) w) :
    (p.R.toCx3 p.F).W1 p.F.cr (p.N C CH) w := by
  obtain ⟨w', hw', i, h⟩ := h
  refine ⟨i, ?_⟩
  rcases hw' with rfl | rfl
  · rcases h with h | h | h | h | h
    · exact Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h)
    · exact Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h))
    · exact Or.inr (Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_jw_eq p i _) h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rcases h with h | h | h | h | h
    · exact Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h))
    · rw [ValuationRepresentative.conjPl_conjPl] at h
      exact Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_indices_eq p i _) h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl (ne_of_eq_of_ne (splitPartFace_baseLevel_jw_eq p i _) h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · rw [ValuationRepresentative.conjPl_conjPl] at h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem tupTw_of_w1Row : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D)
    (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz),
    SingleIndexPlacesAreTwisted p → p.R.toRealDat.tup_tw (F2 p) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p h w hw
  exact h w (w1_of_inW1_split_part p 0 0 w hw)

end GlobalTheory.BigOn

end
end

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
open GlobalTheory.CharRealise

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)



theorem iw_split_eq (j : Fin D.R.m) (t : p.P.A3.fam3.base3.Tup) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (p.S false).Iw j t w = (S2 p).Iw j t w := by
  show ((p.R.toCx3 p.F).data p.F.cr false).Iw j t w = _
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl



theorem d_split_eq : (p.S false).D = (S2 p).D := by
  show ((p.R.toCx3 p.F).data p.F.cr false).D = _
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl



theorem onWith_of_split : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), ∀ (C CH : ℝ) (err : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ), ONwith (S2 p) ((R2 p).num (F2 p) C CH) err → ONwith (p.S false) (p.N C CH) err ∧ (p.S false).D = (S2 p).D := by
  intro D L hT Gi Gl Kc Y cX ex Csz p C CH err h
  obtain ⟨h1, h2, h3⟩ := h
  have eD := d_split_eq p
  refine ⟨⟨fun w hw => ?_, fun w hw j => h2 w hw j, fun j => h3 j⟩, eD⟩
  have := h1 w hw
  simp only [iw_split_eq p, eD]
  exact this

end GlobalTheory.BigOn

end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem indefinitePoint_splitPartContent_eq_forcedContent (p : PtAt ex Csz) (C CH : ℝ) :
    Formalism.L2.Indef.Tree.DepthCond.ContentEqualsDatumContent ((R2 p).num (F2 p) C CH) (GlobalTheory.RunDepth.numOf D L) (fun j : Fin D.R.m => (j : ℕ) + 1) := by
  intro w j
  rw [numOf_Fj_eq_ofRecord D L p.Del p.h0 p.hDel p.hh0]
  rfl

end Comparison₂

end GlobalTheory.BigOn
end
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimesOnto

theorem prime_eq_plGw_or_conj : ∀ (D : D7) (k : Fin 2) (P : Ideal (𝓞 D.host.E)), P.IsPrime → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P →
    ∃ v : D.nd.PlG k, P = (D.naut.plGw k v).asIdeal ∨
      P = (D.naut.plGw k v).asIdeal.map
        ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E) :
          𝓞 D.host.E →+* 𝓞 D.host.E) := by
  intro D k P hP hg
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hg
    have h0 : ((D.host.g k : ℕ) : 𝓞 D.host.E) = ((0 : ℕ) : 𝓞 D.host.E) := by simpa using hg
    have := Nat.cast_injective h0
    exact (D.host.g_prime k).ne_zero this
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hP, hne⟩
  have hw : w ∈ Formalism.BasicNotions.placesOver D.host.E (D.host.g k) := hg
  obtain ⟨v, hv | hv⟩ := GlobalTheory.TypePlacesExhaust.eq_plGw_or_isConjPl D k w hw
  · exact ⟨v, Or.inl (congrArg HeightOneSpectrum.asIdeal hv)⟩
  · refine ⟨v, Or.inr ?_⟩
    set c : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
      RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv with hc
    rw [Ideal.map_comap_of_equiv]
    ext y
    rw [Ideal.mem_comap]
    have key : (y : D.host.E) = D.host.conj ((c.symm y : 𝓞 D.host.E) : D.host.E) := by
      rw [← GlobalTheory.HeightCounting.FormsStep.complexConj_eq_hostConj]
      have : c (c.symm y) = y := c.apply_symm_apply y
      rw [← congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) this]
      rfl
    exact ((hv (c.symm y) y key).symm.trans Iff.rfl)
end GlobalTheory.TypePrimesOnto
end

section

open NumberField IsLocalRing Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralChartCover

theorem cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y), ∃ (T' : CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)), Function.Injective φ ∧ φ.Finite ∧ UpFBr.GeoJ T'.V t'.G (𝓞 E) (fun a => t'.act.act a) (chD C3.ch) (fun i => MvPowerSeries.map φ (C3.FT i)) (fun a i => MvPowerSeries.map φ (C3.actT a i)) := by
  intro E _ _ _ H Dw lv Xo c inst hstar T io y C3
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starRing_ext_of_star inst H.starRing hstar
  letI := H.starRing
  letI := io.toAlgebra
  obtain ⟨T', φ, t', m, hi, hf, ⟨P⟩⟩ := GlobalTheory.ChartCharacters.exists_finite_ext_pelUnif Xo T C3.I.G C3.I.t' C3.I.m2 _ C3.I.m1
  obtain ⟨F', x', act', hF, hA, hx, ha⟩ := GlobalTheory.integralChart_baseChange E H Dw lv Xo c T io y C3 T' φ t' m
  exact ⟨T', φ, t', hi, hf, P.D, P.A, P.U.toUnifPre, F', x', _, t'.act.toRingAct, P.oD, P.oA, act', hF, funext hA, fun _ => rfl, hx, P.lin, ha⟩

end GlobalTheory.IntegralChartCover
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaShift

open GlobalTheory.ThetaProjEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem smul_apply_of_eq {H W : Type} [AddCommGroup W] [Module ℂ W] (c : ℂ) (hc : c ≠ 0) (f : H → W) (h : H) (w : W)
    (hw : f h = c⁻¹ • w) : (c • f) h = w := by
  rw [Pi.smul_apply, hw, smul_inv_smul₀ hc]

theorem pt_shift (R : RealDat D A Ks) (hM : R.IsModels) (hP : R.IsThP) (i : Fin D.R.m) (t : T0)
    (κ : GA D (Vc D i)) (κ' : GA D (Wc D i)) (hκ : κ ∈ GfC (Vc D i)) (hκ' : κ' ∈ GfC (Wc D i)) (a : ℂ)
    (hv : R.ωP i t (κ, κ') (R.vP i t) = a • R.vP i t) :
    ∀ P, R.ωP i t (κ, κ') (R.ptP i t P) = a • R.ptP i t P :=
  GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hM.inf (hP.ωP i t) _ _ _ _ _
    (hP.pt_theta i t) κ hκ κ' hκ' a hv

theorem thF_shift_of_eigen (R : RealDat D A Ks) (hM : R.IsModels) (hP : R.IsThP) (i : Fin D.R.m) (t : T0)
    (g0 : G0 R.Pg D.R.r)
    (κ : GA D (Vc D i)) (κ' : GA D (Wc D i)) (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ)
    (y y' : (R.HV i t).H) (c : ℂ) (hc0 : c ≠ 0)
    (hpt : ∀ P, R.ωP i t (κ, κ') (R.ptP i t P) = c⁻¹ • R.ptP i t P)
    (hy : ∀ h, (c • R.extV i t y') h = R.extV i t y (h * κ))
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : GA D (Wc D i)) :
    R.thF i t y' (fun ρ => v ρ) x = R.thF i t y (fun ρ => v ρ) (x * κ') := by
  refine (hP.thF i t).elim fun thP hPF => ?_
  have hker := fun P => GlobalTheory.thetaKO_rat_left_and_eigen_right R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) (hP.ωP i t)
    (R.ptP i t P) (hP.pt_theta i t P)
  have hm := thetaLift_shift hPF.1 (GQ (Vc D i)) κ κ' c hc0
    (integral_shift (Vc D i) (R.βV i) (R.datVt i t) g0 κ hκ (R.νV i t) (hM.νV i t).1.1 (R.fdV i t)
      (hM.νV i t).2)
    (fun P γ hγ g h => by
      have := (hker P).1 γ hγ 1 (GQ (Wc D i)).one_mem h g
      rwa [one_mul] at this)
    (fun P g h => (hker P).2 κ κ' c⁻¹ (hpt P) h g)
    ((R.extV i t).rangeRestrict y) ((R.extV i t).rangeRestrict y')
    (extV_left R hM.HV i t y)
    hy
    (PiTensorProduct.tprod ℂ v) x
  exact (congrFun (hPF.2 y' v) x).trans (hm.trans (congrFun (hPF.2 y v) (x * κ')).symm)

theorem thF_shift_of_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ y y' : (R.HV i t).H, (∀ h, R.extV i t y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : GA D (Wc D i)), R.thF i t y' (fun ρ => v ρ) x = R.thF i t y (fun ρ => v ρ) (x * κ') := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hlev hM hP i t g0 κ κ' hκ hκ' y y' hy v x
  have hc0 := levChi_ne_zero (V := Vc D i) (β := R.βV i) (flagL (R.datVt i t)) κ
  exact thF_shift_of_eigen R hM hP i t g0 κ κ' hκ y y' (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ) hc0
    (pt_shift R hM hP i t κ κ' hκ.1 hκ'.1 _ (GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hlev hM.inf hP.ωP hP.vP i t g0 κ κ' hκ hκ'))
    (fun h => smul_apply_of_eq _ hc0 _ h _ (hy h)) v x

end GlobalTheory.ThetaShift

end
end
