module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsBaseChangePolarisedDatum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Formalism.LocalToGlobal.Columns.RecPerFF
public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
import Lean.Exception
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle179
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle354
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1929
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1931
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstantsJets_baseChange_polarisedDatum : ∀ (R K : Type) [CommRing R] [Field K] (f : R →+* K) (x : KeyIn R) (x' : KeyIn K) (φ : x'.P.A.left ⟶ x.P.A.left), KeyAtMap x' x f φ → ∀ (g : ℕ) (hg : x.P.g = g) (hg' : x'.P.g = g) (m : ℕ) (I : Type) (pt : I → (baseOver (Sp R) ⟶ x.P.A)) (pt' : I → (baseOver (Sp K) ⟶ x'.P.A)) (ϑ : I → R) (J : I → Fin g → R), (∀ i, (pt' i).left ≫ φ = spMap f ≫ (pt i).left) → ThJet x hg m pt ϑ J → ThJet x' hg' m pt' (fun i => f (ϑ i)) (fun i j => f (J i j)) := by
  first | exact @GlobalTheory.MBLow.thJet_of_keyAtMap | exact GlobalTheory.MBLow.thJet_of_keyAtMap | (intros; apply GlobalTheory.MBLow.thJet_of_keyAtMap <;> assumption)
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColEvNorm

open _root_.Formalism.L2.Col in
theorem rowCast_injective {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
    {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (e : Pr.vGs = SG') (A : LevFam X.E X.K (R.N R.m - 1) Pr.vGs)
    (Λ' : LevFam X.E X.K (R.N R.m - 1) SG') (hΛ : Λ' = e ▸ A) :
    Function.Injective (rowCast W e A Λ' hΛ) := by
  subst hΛ
  subst e
  intro F G h
  exact h

open _root_.Formalism.L2.Col in
theorem zOfRow_injective {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S)
    (hQ : QE sel (mu : Formalism.L2.DIV.Chr X.F X.E X.K) = ∅) (P : LevFam X.E X.K R.r Pr.vGs) (σ₀ : X.K →+* ℂ)
    (hM : (rowGSD W (rowTyG Ch P).inv).Ok) :
    Function.Injective (zOfRow W Ch sel mu hQ P σ₀ hM) := by
  intro F G h
  apply rowCast_injective W (rcol_rowSG_eq sel mu hQ) (rowTyG Ch P).inv _ (rowTy_inv_cast Ch sel mu hQ P)
  apply ((rowGSD W (rowTyG Ch P).inv).hB hM).repr.injective
  ext a
  exact σ₀.injective (congrFun h a)

end GlobalTheory.ColEvNorm

namespace GlobalTheory.ColEvNorm


open _root_.Formalism.L2.Col in
theorem ipAt_le_of_ties {Xf : Fields} [_root_.NumberField.IsTotallyComplex Xf.K]
    (Pr : Primes Xf) (Rk : Ranks) (W : Wts Xf Pr.Word Rk) (Ch : Chars Xf Pr Rk.m)
    (sel : HeightOneSpectrum (𝓞 Xf.F) → HeightOneSpectrum (𝓞 Xf.E)) {Sg : Set ℕ} (hX : Xf.Ok)
    (Lv : LevFam Xf.E Xf.K Rk.r Pr.vGs) (Xg : Finset (G0 Xf.E Pr.vGs Rk.r → Xf.K)) (v0 : InfinitePlace Xf.K)
    (TU : Finset (Formalism.L2.DIV.Tup Xf.F Xf.E Xf.K Sg))
    (xiVal : Formalism.L2.DIV.Tup Xf.F Xf.E Xf.K Sg → HeightOneSpectrum (𝓞 Xf.E) → Xf.Kˣ)
    (trIv : Fin Rk.m → (LevOffI ∅ Pr.vGs ∅ × List ℕ → Xf.K) → LevOffI ∅ Pr.vGs ∅ × List ℕ → Xf.K)
    {Gp : Type} [grp : Group Gp] [fin : Fintype Gp] {Pl0 I0 Tt : Type} {m : ℕ}
    (A3 : FamIn3 Xf.K Gp Pl0 I0 (List ℕ) Tt m) (Ps : Subgroup Gp) (ψs : Ps →* Xf.Kˣ) (Zs : DefSub A3.fam3.amb3)
    (mu : A3.fam3.base3.Tup → Formalism.L2.DIV.Tup Xf.F Xf.E Xf.K Sg) (hP : ∀ t, (mtildeGSD W Ch sel (mu t) Lv).Ok)
    (gEq : Gp = G0 Xf.E Pr.vGs Rk.r) (hgrp : HEq grp (Pi.group : Group (G0 Xf.E Pr.vGs Rk.r)))
    (hm3 : Rk.m = m) (plEq : Pl0 = LevOff ∅ Pr.vGs ∅) (i0Eq : I0 = LevOffI ∅ Pr.vGs ∅) (tEq : Tt = TupF TU)
    (famEq : HEq A3 (colIn3 W Ch sel hX v0 TU Xg ∅ xiVal trIv))
    (muTie : ∀ t, mu t = (cast tEq t).1) (ok1 : A3.fam3.Ok3 1)
    (hps1 : HEq Ps Lv.grp) (hps2 : HEq ψs Lv.chr)
    (X0 : InfinitePlace Xf.K → Matrix (Fin ((A3.side3 Ps ψs Zs).nV A3.fam3.base3.μ0))
      (Fin ((A3.side3 Ps ψs Zs).nV A3.fam3.base3.μ0)) ℂ)
    (hX0 : GlobalTheory.ColRows.IsFrames (A3.side3 Ps ψs Zs) X0) (v : InfinitePlace Xf.K)
    (F : Fin ((A3.side3 Ps ψs Zs).nV A3.fam3.base3.μ0) → Xf.K)
    (F' : (mtildeKGSD W Ch sel (mu A3.fam3.base3.μ0)).EqFun)
    (hm : F'.1 ∈ (mtildeGSD W Ch sel (mu A3.fam3.base3.μ0) Lv).EqFun)
    (hres : HEq ((mtildeKGSD W Ch sel (mu A3.fam3.base3.μ0)).res (mtildeKOk W Ch sel (mu A3.fam3.base3.μ0) hX) F')
      ((A3.A.fam.R A3.fam3.base3.μ0).S.basis.equivFun.symm
        (((A3.A.fam.R A3.fam3.base3.μ0).S.cutE (A3.A.fam.R A3.fam3.base3.μ0).r
          (lvlIdem (A3.A.fam.lvl Ps ψs).P (A3.A.fam.lvl Ps ψs).ψ)).mulVec
          (((A3.A.fam.R A3.fam3.base3.μ0).S.lvlPr (A3.A.fam.R A3.fam3.base3.μ0).r (A3.A.fam.lvl Ps ψs).P
            (A3.A.fam.lvl Ps ψs).ψ * (A3.A.fam.R A3.fam3.base3.μ0).vE (A3.A.fam.lvl Ps ψs)).mulVec F)))) :
    ((mtildeGSD W Ch sel (mu A3.fam3.base3.μ0) Lv).ipAt (hP A3.fam3.base3.μ0) v F'.1 F'.1).re ≤
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun Xf.K (Fin ((A3.side3 Ps ψs Zs).nV A3.fam3.base3.μ0))) X0 v F ^ 2 := by
  subst gEq
  have hg : grp = (Pi.group : Group (G0 Xf.E Pr.vGs Rk.r)) := eq_of_heq hgrp
  subst hg
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    let g' ← g.withContext do
      let lctx ← Lean.getLCtx
      let some fe := lctx.findFromUserName? `famEq | throwError "famEq"
      let some fi := lctx.findFromUserName? `fin | throwError "fin"
      let t ← Lean.instantiateMVars fe.type
      let ty ← Lean.Meta.whnf (← Lean.Meta.inferType t.appArg!)
      let inst := ty.getAppArgs[6]!
      let pf ← Lean.Meta.mkAppM ``Subsingleton.elim #[fi.toExpr, inst]
      let (_, g') ← g.note `hfin pf
      pure g'
    Lean.Elab.Tactic.replaceMainGoal [g']
  subst hfin
  subst hm3
  subst plEq
  subst i0Eq
  subst tEq
  have hA := eq_of_heq famEq
  subst hA
  have hp1 := eq_of_heq hps1
  subst hp1
  have hp2 := eq_of_heq hps2
  subst hp2
  have hmuE : mu = fun t => t.1 := funext muTie
  subst hmuE
  exact GlobalTheory.T.classSum_le_frameNorm_sq_good_part Xf Pr Rk W Ch sel Sg hX v0 TU Xg ∅ xiVal trIv Lv Zs _ (hP _) ok1 F F' hm hres v X0
    (hX0 v).1 (hX0 v).2

end GlobalTheory.ColEvNorm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RamTwist

theorem unramAt_of_div {D : D7} {ε : AF D.host.F} {a b c : (AE D)ˣ →* Circle}
    (h : GlobalTheory.WeilParts.UnramAt ε (a * b / c)) (ha : GlobalTheory.WeilParts.UnramAt ε a) (hc : GlobalTheory.WeilParts.UnramAt ε c) :
    GlobalTheory.WeilParts.UnramAt ε b := by
  intro x h1 h2 h3
  have e := h x h1 h2 h3
  rw [MonoidHom.div_apply, MonoidHom.mul_apply, ha x h1 h2 h3, hc x h1 h2 h3, one_mul, div_one] at e
  exact e

theorem not_overP_g {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ G.pl.S0) (PP : HeightOneSpectrum (𝓞 D.host.E))
    (hPP : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v) (k : Fin 2) : ¬ Formalism.L2.Host.OverP D.host (D.host.g k) PP := by
  intro h
  have hk : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    subst hPP
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal
    rw [map_natCast]
    exact h
  refine hv (G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_)))
  fin_cases k
  · exact Or.inl hk
  · exact Or.inr (Or.inl hk)

end GlobalTheory.RamTwist


open GlobalTheory.RamTwist in
theorem GlobalTheory.SqTop.not_unramAt_twist : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → ∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v → ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  intro D T Lc sc G μ₀ hμ t v e he hv PP hPP hPv i j hU
  have hmi1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have hmi2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hchi : GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i)) :=
    GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (G.ch.chi_eq _ hmi1 hmi2) v e he fun P hP =>
      G.ch.unr _ hmi1 hmi2 P (hP ▸ hv)
  have hmu : GlobalTheory.WeilParts.UnramAt e (Lc.mu0 ((j : ℕ) + 1)) :=
    GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hμ.mu0 j) v e he fun P hP =>
      (Lc.C.isMu0 j).unr P (not_overP_g G hv P hP)
  have hxi : GlobalTheory.WeilParts.UnramAt e (Lc.xi t) := by
    refine unramAt_of_div (a := Lc.mu0 ((j : ℕ) + 1)) (c := G.ch.chi (D.R.m - i)) ?_ hmu hchi
    exact hU
  have h1 := GlobalTheory.UnrOverPlace.unrAt_of_unramAt D (Lc.xi t) v e he hxi PP hPv
  exact (hμ.Q_ram t PP).2 (Or.inl hPP) ((GlobalTheory.LFun.unrAt_iff_of_chrEq (hμ.xi t) PP).1 h1)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RamifiedIdeleBasePlace

theorem ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ →
    ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v = G.pl.v0 →
      ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  intro D T Lc sc G μ₀ hL t v e he hv i j hU
  subst hv
  have hw : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0 := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have h1 := GlobalTheory.UnrOverPlace.unrAt_of_unramAt D _ G.pl.v0 e he hU _ hw
  exact GlobalTheory.RowTest.squareNuHeckeCharacter_not_unramified_at_chosenPlace hL G t i j
    ((GlobalTheory.LFun.unrAt_iff_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL) _).1 h1)

end GlobalTheory.RamifiedIdeleBasePlace
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GridUnr

theorem chi_eta_unramAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → ∀ i : Fin D.R.m, GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i)) ∧ GlobalTheory.WeilParts.UnramAt e Lc.eta := by
  intro D T Lc sc G μ₀ hμ t v e he hv i
  have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  refine ⟨GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (G.ch.chi_eq _ h1 h2) v e he fun P hP => ?_,
    GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hμ.eta v e he fun P _ => Lc.C.isEta.unr P⟩
  exact G.ch.unr _ h1 h2 P (by rw [hP]; exact hv)

end GlobalTheory.GridUnr
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotTripleUnr

theorem unramAt_mul {D : D7} {ε : AF D.host.F} {χ₁ χ₂ : (AE D)ˣ →* Circle}
    (h₁ : GlobalTheory.WeilParts.UnramAt ε χ₁) (h₂ : GlobalTheory.WeilParts.UnramAt ε χ₂) : GlobalTheory.WeilParts.UnramAt ε (χ₁ * χ₂) := by
  intro x hx h1 h2
  rw [MonoidHom.mul_apply, h₁ x hx h1 h2, h₂ x hx h1 h2, one_mul]

theorem under_eq_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top
    fun a ha => ?_)
  obtain ⟨c', h1, h2⟩ := h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha
  have hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F) :=
    (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c' := RingOfIntegers.ext (h2.trans hfix).symm
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal
  rwa [e]

theorem unramAt_mu : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → (∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → ∀ j : Fin D.R.m, GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1)) := by
  intro D T Lc sc G μ₀ hL t v e he hv hQ j
  have hmu : Lc.mu t (j + 1) = Lc.mu0 ((j : ℕ) + 1) * Lc.xi t := rfl
  rw [hmu]
  refine unramAt_mul ?_ ?_
  · refine GlobalTheory.UnramOver.unramAt_of_unrAt D _ (Lc.C.mu0 j) (hL.mu0 j) v e he fun P hP => ?_
    refine (Lc.C.isMu0 j).unr P fun k hk => hv ?_
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
      rw [← hP]
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal
      rw [map_natCast]
      exact hk
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl hk'
    · exact Or.inr (Or.inl hk')
  · refine GlobalTheory.UnramOver.unramAt_of_unrAt D _ (Lc.xiH t) (hL.xi t) v e he fun P hP => ?_
    by_contra hn
    rcases (hL.Q_ram t P).1 hn with hq | ⟨P', hq, hc⟩
    · exact hQ P hq hP
    · exact hQ P' hq ((under_eq_of_isConjPl hc).trans hP)

end GlobalTheory.BotTripleUnr

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelCompatibilities_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), ColIn.JetsIn I → I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → (t.cst (I.rec7 l Z).what₂.mu0).sharp = true → GlobalTheory.ColRows.KerTies t W Del h0 := by
  first | exact @GlobalTheory.ColRows.kerTies_of_stdKer | exact GlobalTheory.ColRows.kerTies_of_stdKer | (intros; apply GlobalTheory.ColRows.kerTies_of_stdKer <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lineBundleFamily_agreeing_smallExtension_tangent : ∀ (S : Scheme.{0}) [IsAffine S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : Over S) (M : LB (A ⊗ U).left), Fam A M → Inj A M → TanLift A M → ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → e ≠ 0 → ∀ (s : Sp C ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N → ∀ u' : Over.mk s ⟶ U, Same A N M (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))) (ptMap s (Ideal.Quotient.mk (Ideal.span {e})) ≫ u') → ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u := by
  first | exact @GlobalTheory.DualOpen.exists_same_of_smallExt | exact GlobalTheory.DualOpen.exists_same_of_smallExt | (intros; apply GlobalTheory.DualOpen.exists_same_of_smallExt <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.lieSheaf_semiAbelian_semiNeg_of_isAlgClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → SemiNeg k (Lie G) := by
  first | exact @GlobalTheory.Nef.semiNeg_lie_of_isAlgClosed | exact GlobalTheory.Nef.semiNeg_lie_of_isAlgClosed | (intros; apply GlobalTheory.Nef.semiNeg_lie_of_isAlgClosed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyScalarNe

theorem polAVSectionInverseImage_ne_zero {K : Type} [Field K] (P : PolAV (Sp K)) (T : Over (Sp K)) (t₀ : T.left) (s : P.L.Sec)
    (hs : ∃ p, p ∈ nonzeroLocus s) (t : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) (h : IsPolAVSectionInverseImage P T s t) :
    t ≠ 0 := by
  rintro rfl
  obtain ⟨z, hz⟩ := hs
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz
  have hpb : IsPullback (fst T P.A).left (snd T P.A).left T.hom P.A.hom := by
    rw [Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback _ _
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨y, -, hy⟩ := Scheme.exists_preimage_of_isPullback hpb t₀ z (Subsingleton.elim _ _)
  have hle : (LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => k) ≤ (snd T P.A).left ⁻¹ᵁ P.L.U k :=
    LB.wchart_le P.L _ (fun _ : Fin 1 => k) 0
  have hyU : y ∈ (LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => k) := by
    show y ∈ LB.wchart P.L _ _
    refine Set.mem_iInter.2 fun _ => ?_
    show (snd T P.A).left y ∈ (P.L.U k : Set P.A.left)
    rw [hy]; exact hk
  subst hy
  have e := congrArg (gs (𝟙 _) y _) (h k hle)
  rw [gs_appLE _ _ _ hle (𝟙 _) y hyU, Category.id_comp, gs_stalkMap (snd T P.A).left y _ hk] at e
  have u' := u.map ((snd T P.A).left.stalkMap y).hom
  rw [← e] at u'
  have h0 : gs (𝟙 _) y ((LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => k)) ((0 : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)).f (fun _ => k)) = 0 := by
    have z0 : (0 : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)).f (fun _ => k) = 0 := rfl
    rw [z0, gs_eq _ y _ hyU, map_zero, map_zero]
  rw [h0] at u'
  exact not_isUnit_zero u'

end GlobalTheory.KeyScalarNe

theorem GlobalTheory.KeyScalarNe.scalar_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V))
    (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre), GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C →
    ∀ (N : NumD C) (ν : NumOf D.toPre C N) (th : GlobalTheory.UT.SecA x.P C 1) (ϑ : Fam D.toPre C 1) (c : C),
      IsPolAVSectionInverseImage x.P (TFK (R := V) C) x.th th → U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) → c ≠ 0 := by
  intro V _ _ _ _ _ D x G _ _ _ U w₀ hw C _ _ _ _ _ _ _ N ν th ϑ c hon hex hv
  rintro rfl
  rw [zero_smul] at hv
  have h0 : ν.FamV (0 : Fam D.toPre C 1) 0 := by
    have := GlobalTheory.WeilValues.famV_smul ν hv 0
    rwa [zero_smul, zero_smul] at this
  have hϑ : ϑ = 0 := GlobalTheory.Ex.FamVal.famV_inj ν hv h0
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF GlobalTheory.allSixLaws.1.globalFns U C (k := 1) le_rfl w₀ hw.1
  have ht : th = 0 := by
    have h1 := (he th ϑ).1 hex
    rw [hϑ] at h1
    exact e.map_eq_zero_iff.1 h1
  obtain ⟨z, -, hz⟩ := x.th_ne (IsLocalRing.closedPoint _)
  exact GlobalTheory.KeyScalarNe.polAVSectionInverseImage_ne_zero x.P (TFK (R := V) C) (IsLocalRing.closedPoint C) x.th ⟨z, hz⟩ th hon ht
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_thetaConstantsJets_localDomain : ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (x : KeyIn W) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → IsUnit (m : W) → ∀ (I : Type) (pt : I → (baseOver (Sp W) ⟶ x.P.A)), (∀ i, pt i ^ (m ^ 2) = 1) → ∃ ϑ J, ThJet x hg m pt ϑ J := by
  first | exact @GlobalTheory.MBLow.exists_thJet_local | exact GlobalTheory.MBLow.exists_thJet_local | (intros; apply GlobalTheory.MBLow.exists_thJet_local <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.exists_normalised_multiplicationPullback_function : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ (m : ℕ) (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ), FnT u 1 th f → ∃ (α : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![(snd (baseOver (Sp ℂ)) x.P.A).left, (snd (baseOver (Sp ℂ)) x.P.A ^ m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (s₁ : LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp ℂ)))), α.IsGen ∧ LB.Gen.Corr x.P.L _ _ _ _ (LB.pullGen x.P.L _ _ α (ptSecT x.P.A 1).left) (rigT x.P.A x.P.L x.rig (baseOver (Sp ℂ)) (((m ^ 2 : ℕ) : ℤ) - 1)) ∧ IsTwistPull x.P.A x.P.L (mulT x.P.A (baseOver (Sp ℂ)) m) (snd (baseOver (Sp ℂ)) x.P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧ FnT u (m ^ 2) s₁ fun z => f ((m : ℂ) • z) := by
  first | exact @GlobalTheory.MBLow.Cl.exists_normalised_mulPull_fnT | exact GlobalTheory.MBLow.Cl.exists_normalised_mulPull_fnT | (intros; apply GlobalTheory.MBLow.Cl.exists_normalised_mulPull_fnT <;> assumption)
end
