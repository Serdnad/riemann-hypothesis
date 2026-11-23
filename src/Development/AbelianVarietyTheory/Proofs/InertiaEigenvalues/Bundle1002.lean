module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle987
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyExtAnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle027
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.XiIntCore.xi_int_core : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h, Y.Z.ρ.IsDatum i j b s h 0 → ∃ u : ℂ, u ≠ 0 ∧ ∀ P ∈ (Y.Z.ρ.B i j b).valSpace, ∀ F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) → ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a, ∃ (n : ℕ) (o : Fin n → D.ntw.O i) (m : Fin n → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧ (((D.ntw.l i : ℕ) : ℂ) ^ c * u) • Y.Z.ρ.xi i j b D.nexp Q M h P a = ∑ k, Y.Z.ρ.eO i b (o k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
  intro hAR hSR hSI D X E Y hF hFP i hi j b s h hd
  obtain ⟨u, hu, hA⟩ := GlobalTheory.T.universal_series_coefficients_integral_core_forms hAR hSR hSI D X E Y hF hFP hF.split i hi j b s h hd
  refine ⟨u, hu, fun P hP F hPF => ?_⟩
  obtain ⟨c, hc⟩ := hA P hP F hPF
  refine ⟨c, fun Q M hQ hs a => ?_⟩
  obtain ⟨la, hla, n, o, ψ, hψ, he⟩ := hc Q M hQ hs a (X.geo.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ X.core.toCore.good_σ₀)
  obtain ⟨n', o', m, hm, he'⟩ := GlobalTheory.XiIntCore.supLattice_comb_of_baseInt hAR hSR hSI D X E Y hF hFP i hi j b _ la hla n o ψ hψ
  exact ⟨n', o', m, hm, he.trans he'⟩
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatBundles

theorem ratHyp {D : D7} (X : RealSide D) {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (hF : FieldOk X)
    (hP : ∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) {i : D.ntw.Tw} (hi : D.ntw.NonzeroIndexPlace i)
    (j : Fin D.R.m) : GlobalTheory.BigOn.Exp.RatHyp X.core X.R X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O i j (X.space_eq j) :=
  have hC := X.char
  { size := X.size
    host := X.host
    std := X.std j
    laws := X.geo.fw.laws
    core := ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩
    unif := X.unif
    fw := ⟨X.geo.fw⟩
    tieIn := ⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩
    io := GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
    guard := X.guard
    fin := X.finT
    pins := X.geo.pins j
    phase := by
      convert X.geo.phase j X.unif using 2
      rename_i k
      rw [X.phs k]
      simp
    frame := hP j _
    galois := hF.galois
    small := ⟨hF.vals, hF.ray, hF.roots⟩
    inUse := hi
    low := Y.low i }

theorem levelOf {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D} (Y : SerSide X E) : Y.Z.ρ.LevelOf D.nexp :=
  ⟨fun i j b => (Y.Z.tie i j b).U_eq, fun i j b => (Y.Z.tie i j b).psiU_eq⟩

theorem rat_of_split (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hS : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat) {D : D7} (X : RealSide D) {E : IntegralHeckeForms.XD D}
    (Y : SerSide X E) (hF : FieldOk X) (hsp : D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK)
    (hP : ∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) {i : D.ntw.Tw} (hi : D.ntw.NonzeroIndexPlace i)
    (j : Fin D.R.m) (b : Bool) : RatRow Y.YS X.geo.v₀ Y.Z.good i j b :=
  GlobalTheory.T.thetaSeries_base_twisted_universal_rational hA hA.rayClassFieldSt (GlobalTheory.SerStd.seriesRatS_of hS) D X.Γ X.Pl0 X.I0 X.T X.A3 X.core X.R X.cG Y.S Y.YS
    X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O Y.Z.ρ Y.Z.good i j b (X.space_eq j) Y.Z.pin (levelOf Y) hsp (ratHyp X Y hF hP hi j)

theorem rat_bundles : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b :=
  fun hA hS _ X _ Y hF hP _ hi j b => rat_of_split hA hS X Y hF hF.split hP hi j b

end GlobalTheory.RatBundles
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)


theorem _root_.GlobalTheory.T.classSums_conjugate_twists_conjugate_expansions : ∀ (D : D7) (X : RealSide D) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → ∀ ψ ψ' : Twist D Circle, ψ.Good → ψ'.Good → B.admitted ψ.Q →
  GlobalTheory.BigOn.Exp.TwConj.HasTuples X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j B ψ ψ' →
  ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (cc : VsV D j ℂ →ₗ[ℂ] (X.R.cV j).W) (κ : ℂ), IsLow X j u → ExtC X.R.toRealDat j (inC (X.geo.O j).c') (X.geo.O j).c0' cc → κ ≠ 0 →
  ∀ τ : ℂ ≃+* ℂ, FixBase X.core X.R.toRealDat j τ → FixDat B τ → ConjChar τ ψ ψ' → ∀ ω ω' : PairRep (Vc D j) (Wc D j), B.IsWeil ψ.chi ω → B.IsWeil ψ'.chi ω' →
  ∃ ζ : ℂ, IsRoot1 ζ ∧ ∀ (I : Type) [Fintype I] (rep : I → GA D (Vc D j)), (∀ a, rep a ∈ GfC (Vc D j)) → ∀ F F' : Amb D j,
    ConjAt (X.R.ioP j (PiTensorProduct.tprod ℂ u) ∘ₗ cc) κ τ F F' →
    ConjFun (X.geo.O j) (X.geo.κ j) τ ζ (κ • B.classSum ω ψ rep F) (κ • B.classSum ω' ψ' rep F') := by
  first | exact @GlobalTheory.PlaceClassSum.classSum_conj_place | exact GlobalTheory.PlaceClassSum.classSum_conj_place | (intros; apply GlobalTheory.PlaceClassSum.classSum_conj_place <;> assumption)
end
