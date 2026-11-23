module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle356
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle433
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle421
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle200
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle420
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftVAlgebraMapMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle424
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle103
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorProductIrreducibleCountableDimen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle433
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx

theorem triIs_congr {D : D7} {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ ψ' : AddChar (AF D.host.F) ℂ} {θ θ' : InfFam D}
    {α α' β β' : T → ((AE D)ˣ →* Circle)} {ν ν' : T → Formalism.L2.Host.HChar D.host.E} {S S' : T → Finset (Pl D.host.E)}
    (h : X.Is ψ θ α β ν S) (e1 : ψ' = ψ) (e2 : θ' = θ) (e3 : ∀ t, α' t = α t) (e4 : ∀ t, β' t = β t) (e5 : ∀ t, ν' t = ν t)
    (e6 : ∀ t, S' t = S t) : X.Is ψ' θ' α' β' ν' S' := by
  obtain rfl := e1
  obtain rfl := e2
  obtain rfl := funext e3
  obtain rfl := funext e4
  obtain rfl := funext e5
  obtain rfl := funext e6
  exact h



theorem trBot_holds : TrBot := by
  intro X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι hA M σ hB
  obtain ⟨hl, hg, hw, -⟩ := hA
  have pre := hl.pre
  cases X with | mk B C Wr V Sg N Gj =>
  cases X' with | mk B' C' Wr' V' Sg' N' Gj' =>
  cases B
  cases B'
  dsimp only at pre
  subst pre
  let DX := GlobalTheory.Mem.Stages.toD7 ⟨_, C, Wr, V, Sg, N, Gj⟩
  let DX' := GlobalTheory.Mem.Stages.toD7 ⟨_, C', Wr', V', Sg', N', Gj'⟩
  obtain ⟨f, f', hff, hC, hC'⟩ := hl.C
  obtain rfl : f' = f := eq_of_heq hff
  have hψ : W'.ψ = (by with_unfolding_all exact (W.ψ :)) := eq_of_heq hw.ψ
  have hθ : W'.θ = (by with_unfolding_all exact (W.θ :)) := eq_of_heq hw.θ
  have hxiH : ∀ t, L'.xiH t = (by with_unfolding_all exact ((L.xiH (ι t)) :)) := fun t => eq_of_heq (hl.xi t)
  have hQ : ∀ t, L'.Q t = (by with_unfolding_all exact ((L.Q (ι t)) :)) := fun t => eq_of_heq (hl.Q t)
  have hchi : G'.ch.chi = (by with_unfolding_all exact (G.ch.chi :)) := eq_of_heq hg.chi
  have hchiH : G'.ch.chiH = (by with_unfolding_all exact (G.ch.chiH :)) := eq_of_heq hg.chiH
  have hv0 : G'.pl.v0 = (by with_unfolding_all exact (G.pl.v0 :)) := eq_of_heq hg.v0
  have hwp : G'.pl.w = (by with_unfolding_all exact (G.pl.w :)) := eq_of_heq hg.w
  have hCmu : ∀ j, L'.C.mu0 j = (by with_unfolding_all exact ((L.C.mu0 j) :)) := fun j => by
    have a : L.C.mu0 j = f'.mu0 j := by rw [hC]; rfl
    have b : L'.C.mu0 j = f'.mu0 j := by rw [hC']; rfl
    exact b.trans ((by with_unfolding_all exact (a.symm :)))
  have hCeta : L'.C.eta = (by with_unfolding_all exact (L.C.eta :)) := by
    have a : L.C.eta = f'.eta := by rw [hC]; rfl
    have b : L'.C.eta = f'.eta := by rw [hC']; rfl
    exact b.trans ((by with_unfolding_all exact (a.symm :)))
  have hmu0 : ∀ j : Fin DX'.R.m, L'.mu0 (↑j + 1) = (by with_unfolding_all exact ((L.mu0 (↑j + 1)) :)) := fun j => by
    have h1 : ChrEq ((by with_unfolding_all exact ((L.mu0 (↑j + 1)) :))) (L'.C.mu0 j) := by rw [hCmu j]; exact (by with_unfolding_all exact ((hl.is.mu0 j) :))
    exact (GlobalTheory.ChrEqUnique.chrEq_unique DX').2.1 _ _ _ (hl.is'.mu0 j) h1
  have heta : L'.eta = (by with_unfolding_all exact (L.eta :)) := by
    have h1 : ChrEq ((by with_unfolding_all exact (L.eta :))) L'.C.eta := by rw [hCeta]; exact (by with_unfolding_all exact (hl.is.eta :))
    exact (GlobalTheory.ChrEqUnique.chrEq_unique DX').2.1 _ _ _ hl.is'.eta h1
  have hxi : ∀ t, L'.xi t = (by with_unfolding_all exact ((L.xi (ι t)) :)) := fun t => by
    have h1 : ChrEq ((by with_unfolding_all exact ((L.xi (ι t)) :))) (L'.xiH t) := by rw [hxiH t]; exact (by with_unfolding_all exact ((hl.is.xi (ι t)) :))
    exact (GlobalTheory.ChrEqUnique.chrEq_unique DX').2.1 _ _ _ (hl.is'.xi t) h1

  have thImp : ∀ ψ S T f, @IsThetaFunO DX ψ S T f → @IsThetaFunO DX' ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (f :))) :=
    fun ψ S T f h => ⟨(by with_unfolding_all exact (h.quasi :)), (by with_unfolding_all exact (h.level :)), (by with_unfolding_all exact (h.cont :)), (by with_unfolding_all exact (h.smooth :))⟩
  have thImp' : ∀ ψ S T f, @IsThetaFunO DX' ψ S T f → @IsThetaFunO DX ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (f :))) :=
    fun ψ S T f h => ⟨(by with_unfolding_all exact (h.quasi :)), (by with_unfolding_all exact (h.level :)), (by with_unfolding_all exact (h.cont :)), (by with_unfolding_all exact (h.smooth :))⟩
  have thEq : @IsThetaFunO DX' = fun ψ S T f => @IsThetaFunO DX ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (f :))) := by
    funext ψ S T f
    exact propext ⟨fun h => (by with_unfolding_all exact ((thImp' _ _ _ _ h) :)), fun h => (by with_unfolding_all exact ((thImp _ _ _ _ h) :))⟩
  have wImp : ∀ ψ S T x1 x2 ω, @IsWeilDatumO DX ψ S T x1 x2 ω →
      @IsWeilDatumO DX' ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (x1 :))) ((by with_unfolding_all exact (x2 :))) ((by with_unfolding_all exact (ω :))) := fun ψ S T x1 x2 ω h =>
    { std := (by with_unfolding_all exact (h.std :))
      hecS := (by with_unfolding_all exact (h.hecS :))
      hecT := (by with_unfolding_all exact (h.hecT :))
      resS := (by with_unfolding_all exact (h.resS :))
      resT := (by with_unfolding_all exact (h.resT :))
      om_pres := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_pres :))
      om_heis := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_heis :))
      om_aut := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_aut :))
      om_cont := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_cont :))
      om_unit := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_unit :))
      om_split := by rewrite [thEq]; exact (by with_unfolding_all exact (h.om_split :)) }
  have vacImp : ∀ ψ θ S T sS sT LS LT f, @IsVacO DX ψ θ S T sS sT LS LT f →
      @IsVacO DX' ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (θ :))) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) ((by with_unfolding_all exact (sS :))) ((by with_unfolding_all exact (sT :))) ((by with_unfolding_all exact (LS :))) ((by with_unfolding_all exact (LT :))) ((by with_unfolding_all exact (f :))) :=
    fun ψ θ S T sS sT LS LT f h => by
      unfold IsVacO
      rewrite [thEq]
      exact ⟨(by with_unfolding_all exact (h.1 :)), (by with_unfolding_all exact (h.2.inf :)), (by with_unfolding_all exact (h.2.theta :)), (by with_unfolding_all exact (h.2.lat :)), (by with_unfolding_all exact (h.2.fock :)), (by with_unfolding_all exact (h.2.norm :))⟩
  have pmImp : ∀ m n ψ B hs e Λ c f₀ T, @IsPlaceModel DX m n ψ B hs e Λ c f₀ T →
      @IsPlaceModel DX' m n ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (B :))) ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (e :))) ((by with_unfolding_all exact (Λ :))) c ((by with_unfolding_all exact (f₀ :))) ((by with_unfolding_all exact (T :))) :=
    fun m n ψ B hs e Λ c f₀ T h => ⟨(by with_unfolding_all exact (h.trans :)), (by with_unfolding_all exact (h.modul :)), (by with_unfolding_all exact (h.vac :))⟩
  have pmImp' : ∀ m n ψ B hs e Λ c f₀ T, @IsPlaceModel DX' m n ψ B hs e Λ c f₀ T →
      @IsPlaceModel DX m n ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (B :))) ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (e :))) ((by with_unfolding_all exact (Λ :))) c ((by with_unfolding_all exact (f₀ :))) ((by with_unfolding_all exact (T :))) :=
    fun m n ψ B hs e Λ c f₀ T h => ⟨(by with_unfolding_all exact (h.trans :)), (by with_unfolding_all exact (h.modul :)), (by with_unfolding_all exact (h.vac :))⟩
  have pmEq : @IsPlaceModel DX' = fun m n ψ B hs e Λ c f₀ T =>
      @IsPlaceModel DX m n ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (B :))) ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (e :))) ((by with_unfolding_all exact (Λ :))) c ((by with_unfolding_all exact (f₀ :))) ((by with_unfolding_all exact (T :))) := by
    funext m n ψ B hs e Λ c f₀ T
    exact propext ⟨fun h => (by with_unfolding_all exact ((pmImp' _ _ _ _ _ _ _ _ _ _ h) :)), fun h => (by with_unfolding_all exact ((pmImp _ _ _ _ _ _ _ _ _ _ h) :))⟩
  intro i j
  obtain ⟨A, A', WW, Y, hb, hsum⟩ := hB i j
  have hmu : ∀ t, L'.mu t (↑j + 1) = (by with_unfolding_all exact ((L.mu (ι t) (↑j + 1)) :)) := fun t => by
    show L'.mu0 (↑j + 1) * L'.xi t = _
    rw [hmu0 j, hxi t]
    exact (by with_unfolding_all exact ((Eq.refl (L.mu (ι t) (↑j + 1))) :))
  have hnu : ∀ t, SqNum.nuH G' t i j = (by with_unfolding_all exact ((SqNum.nuH G (ι t) i j) :)) := fun t => by
    show L'.C.mu0 j * L'.xiH t / G'.ch.chiH (DX'.R.m - ↑i) = _
    rw [hCmu j, hxiH t, hchiH]
    exact (by with_unfolding_all exact ((Eq.refl (SqNum.nuH G (ι t) i j)) :))
  have hloc : ∀ t, locPl G' t = (by with_unfolding_all exact ((locPl G (ι t)) :)) := fun t => by
    unfold locPl GlobalTheory.ChiGrid.Places.W0 GlobalTheory.ChiGrid.Places.S0
    rw [hQ t, hv0, hwp]
    exact (by with_unfolding_all exact ((Eq.refl (locPl G (ι t))) :))
  refine ⟨A, A', WW,
    ⟨⟨(by with_unfolding_all exact (Y.rA.Λ :)), (by with_unfolding_all exact (Y.rA.β :)), (by with_unfolding_all exact (Y.rA.s :)), (by with_unfolding_all exact (Y.rA.B :))⟩, ⟨(by with_unfolding_all exact (Y.rA'.Λ :)), (by with_unfolding_all exact (Y.rA'.β :)), (by with_unfolding_all exact (Y.rA'.s :)), (by with_unfolding_all exact (Y.rA'.B :))⟩,
      ⟨(by with_unfolding_all exact (Y.rW.Λ :)), (by with_unfolding_all exact (Y.rW.β :)), (by with_unfolding_all exact (Y.rW.s :)), (by with_unfolding_all exact (Y.rW.B :))⟩, fun t => (by with_unfolding_all exact ((Y.ω (ι t)) :)), fun t => (by with_unfolding_all exact ((Y.ω' (ι t)) :)), (by with_unfolding_all exact (Y.vac :)),
      (by with_unfolding_all exact (Y.vac' :)), fun t => (by with_unfolding_all exact ((Y.e (ι t)) :)), fun t => (by with_unfolding_all exact ((Y.c (ι t)) :)), fun t => (by with_unfolding_all exact ((Y.f (ι t)) :)), fun t => (by with_unfolding_all exact ((Y.f' (ι t)) :)),
      (by with_unfolding_all exact (Y.m :)), (by with_unfolding_all exact (Y.fd :)), (by with_unfolding_all exact (Y.m' :)), (by with_unfolding_all exact (Y.fd' :))⟩, ⟨(by with_unfolding_all exact (hb.rank :)), (by with_unfolding_all exact (hb.rank' :)), (by with_unfolding_all exact (hb.std :)), (by with_unfolding_all exact (hb.std' :)), (by with_unfolding_all exact (hb.stdW :)), ?_⟩, ?_⟩
  · have e3 : ∀ t, L'.mu t (↑j + 1) * L'.eta ^ (rankV DX' i j % 2) =
        (by with_unfolding_all exact ((L.mu (ι t) (↑j + 1) * L.eta ^ (rankV DX i j % 2)) :)) := fun t => by
      rw [hmu t, heta]
      exact (by with_unfolding_all exact ((Eq.refl (L.mu (ι t) (↑j + 1) * L.eta ^ (rankV DX i j % 2))) :))
    have e4 : ∀ _ : T', G'.ch.chi (DX'.R.m - ↑i) * L'.eta ^ (rankV DX' i j % 2) =
        (by with_unfolding_all exact ((G.ch.chi (DX.R.m - ↑i) * L.eta ^ (rankV DX i j % 2)) :)) := fun _ => by
      rw [hchi, heta]
      exact (by with_unfolding_all exact ((Eq.refl (G.ch.chi (DX.R.m - ↑i) * L.eta ^ (rankV DX i j % 2))) :))
    refine triIs_congr ?_ hψ hθ e3 e4 hnu hloc
    exact ⟨(by with_unfolding_all exact (hb.is.rank :)), (by with_unfolding_all exact (hb.is.rigA :)), (by with_unfolding_all exact (hb.is.rigA' :)), (by with_unfolding_all exact (hb.is.rigW :)),
      fun t => by unfold GlobalTheory.Grid.IsWeil; exact (by with_unfolding_all exact ((wImp _ _ _ _ _ _ (hb.is.weil (ι t))) :)),
      fun t => by unfold GlobalTheory.Grid.IsWeil; exact (by with_unfolding_all exact ((wImp _ _ _ _ _ _ (hb.is.weil' (ι t))) :)),
      (by with_unfolding_all exact ((vacImp _ _ _ _ _ _ _ _ _ hb.is.isVac) :)), (by with_unfolding_all exact ((vacImp _ _ _ _ _ _ _ _ _ hb.is.isVac') :)),
      fun t => (by with_unfolding_all exact ((hb.is.idem (ι t)) :)), fun t => (by with_unfolding_all exact ((hb.is.expo (ι t)) :)),
      fun t => by unfold IsThetaAt; rewrite [pmEq]; exact (by with_unfolding_all exact ((hb.is.fst (ι t)) :)),
      fun t => by unfold IsThetaAt; rewrite [pmEq]; exact (by with_unfolding_all exact ((hb.is.snd (ι t)) :)),
      (by with_unfolding_all exact (hb.is.meas :)), (by with_unfolding_all exact (hb.is.meas' :))⟩
  · obtain ⟨Ω, Ω', h0, h0', H⟩ := hsum
    refine ⟨Ω, Ω', h0, h0', fun t h hh => ?_⟩
    rw [hψ, hθ]
    have H3 := H (ι t) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (hh :)))
    exact (by with_unfolding_all exact (H3 :))

end GlobalTheory.RowEx

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols Separates rowForm)

noncomputable section

namespace GlobalTheory.RowEx

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}



theorem inj_of_sep_conv {ch : Choice R} (hM : R.IsModels) (hsep : Separates R ch.W ch.M ch.w ch.ρ ch.ξ)
    (hconv : ∀ a u, ConvK ch a u) (u : R.HE.H) (hu : ∀ a, psiK ch a u = 0) : u = 0 := by
  by_contra h0
  have hmem : R.HE.e u ∈ R.EEat R.triv := hM.HE.2.1 ▸ LinearMap.mem_range_self _ u
  have hne : R.HE.e u ≠ 0 := fun h => h0 (hM.HE.1 (h.trans (map_zero _).symm))
  obtain ⟨Ψ, hΨ, Φ, -, hf⟩ := hsep _ hmem hne
  apply hf
  rw [← span_col_eq_cols ch Φ] at hΨ
  have key : ∀ x ∈ Submodule.span ℂ (ch.col '' {a | ch.Phi a = Φ}),
      BplusConv ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ch.ξ x)
          (thetaChi ch.W ch.M ch.ρ Φ (rowForm R ch.w (R.HE.e u))) ∧
        Bplus ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ch.ξ x)
          (thetaChi ch.W ch.M ch.ρ Φ (rowForm R ch.w (R.HE.e u))) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have ha' : ch.Phi a = Φ := ha
      have h1 : FConv ch.W ch.M ch.ρ ch.ξ (ch.col a) (ch.Phi a) (ch.form u) := hconv a u
      have h2 : fPsiPhi ch.W ch.M ch.ρ ch.ξ (ch.col a) (ch.Phi a) (ch.form u) = 0 := hu a
      rw [ha'] at h1 h2
      exact ⟨h1.2, h2⟩
    | zero =>
      rw [LinearMap.map_zero (pairVec (coefPlus ch.G ch.W.θ) ch.ξ)]; exact bplusConv_zero ch.W ch.M _
    | add x y _ _ hx hy =>
      rw [LinearMap.map_add (pairVec (coefPlus ch.G ch.W.θ) ch.ξ) x y]
      obtain ⟨hc, he⟩ := bplusConv_add ch.W ch.M hx.1 hy.1
      exact ⟨hc, by rw [he, hx.2, hy.2, add_zero]⟩
    | smul c x _ hx =>
      rw [LinearMap.map_smul (pairVec (coefPlus ch.G ch.W.θ) ch.ξ) c x]
      obtain ⟨hc, he⟩ := bplusConv_smul ch.W ch.M c hx.1
      exact ⟨hc, by rw [he, hx.2, mul_zero]⟩
  exact (key Ψ hΨ).2



theorem isEx_of_separates (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate) (hL : LinB) (hB : BaseEx) : IsEx := by
  obtain ⟨C1, hL⟩ := hL
  obtain ⟨C2, hB⟩ := hB
  refine ⟨max 6510 (max C1 C2), fun ε CF hCF => ?_⟩
  obtain ⟨x1, hS⟩ := hS ε CF (le_of_max_le_left hCF)
  obtain ⟨x2, hL⟩ := hL ε CF (le_trans (le_max_left _ _) (le_of_max_le_right hCF))
  obtain ⟨x3, hB⟩ := hB ε CF (le_trans (le_max_right _ _) (le_of_max_le_right hCF))
  refine ⟨max x1 (max x2 x3), fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hset G W hW S₀ => ?_⟩
  have hx1 : x1 ≤ large₂.sc.x := le_of_max_le_left hx
  have hx2 : x2 ≤ large₂.sc.x := le_trans (le_max_left _ _) (le_of_max_le_right hx)
  have hx3 : x3 ≤ large₂.sc.x := le_trans (le_max_right _ _) (le_of_max_le_right hx)
  obtain ⟨M, ρ, ξ, cv, rm, S, rp, n, e, c, hS0, hbase⟩ := hB D large₂ hε hx3 Γ Pl0 T A Ks R F hset G W hW S₀
  obtain ⟨ρ', ξ', hsep⟩ := hS D large₂ hε hx1 hset.size hset.eser Γ Pl0 T A Ks R hset.core.lev hset.grp G W hbase.weil M
    hbase.vol _ hbase.w_ne
  have hconv := hL D large₂ hε hx2 Γ Pl0 T A Ks R F hset _ rfl (hbase.withReal ρ' ξ')
  exact ⟨M, ρ', ξ', cv, rm, S, rp, n, e, c, hS0,
    hbase.is_withReal (inj_of_sep_conv hset.core.models hsep hconv)⟩

end GlobalTheory.RowEx

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin




theorem _root_.GlobalTheory.T.adeleIdempotent_smul_mem_latticeCompletionAtPlace : ∀ (D : D7) (S : HSp D) (𝔞 : Set D.host.E) (L : GlobalTheory.FinPl.Lat S) (v : GlobalTheory.FinPl.Pl D) (z : Fin S.rank → AE D), z ∈ GlobalTheory.FinPl.latMul S 𝔞 L (fun _ => True) → GlobalTheory.FinPlLoc.idem D (· = v) • z ∈ GlobalTheory.FinPl.latMul S 𝔞 L (· = v) := by
  first | exact @GlobalTheory.FinPlLoc.idem_smul_mem_latMul_at | exact GlobalTheory.FinPlLoc.idem_smul_mem_latMul_at | (intros; apply GlobalTheory.FinPlLoc.idem_smul_mem_latMul_at <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin




theorem _root_.GlobalTheory.T.adeleIdempotent_mul_integral_of_unit_factor : ∀ (D : D7) (v : GlobalTheory.FinPl.Pl D) (u : 𝓞 D.host.F), u ∉ v.asIdeal → ∀ z : AE D, GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((u : D.host.F) : D.host.E) * z ∈ intAt D (· = v) → GlobalTheory.FinPlLoc.idem D (· = v) * z ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.UnitAtPl.idem_mul_mem_of_unit | exact GlobalTheory.UnitAtPl.idem_mul_mem_of_unit | (intros; apply GlobalTheory.UnitAtPl.idem_mul_mem_of_unit <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


theorem _root_.GlobalTheory.T.orthogonalSummandProjection_mem_lattice_of_splits : ∀ {D : D7} {S A B : HSp D} (o : OrthDec S A B) {L : Lat S} {LA : Lat A} {LB : Lat B}, (∀ z : Fin B.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV B LB (· = v)) → z ∈ LB) → (∀ v, OrthAt o L LA LB v) → ∀ t ∈ L, o.qB *ᵥ t ∈ LB := by
  first | exact @GlobalTheory.FinPl.projB_mem_of_orthAt | exact GlobalTheory.FinPl.projB_mem_of_orthAt | (intros; apply GlobalTheory.FinPl.projB_mem_of_orthAt <;> assumption)
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


theorem _root_.GlobalTheory.T.wittCoreEmbedding_mulVec_mem_lattice_of_splits : ∀ {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}, (∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L) → (∀ v, MonoAt d L L₀ v) → ∀ y ∈ L₀, d.i₀ *ᵥ y ∈ L := by
  first | exact @GlobalTheory.WittCoreLat.i₀_mulVec_mem | exact GlobalTheory.WittCoreLat.i₀_mulVec_mem | (intros; apply GlobalTheory.WittCoreLat.i₀_mulVec_mem <;> assumption)
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


theorem _root_.GlobalTheory.T.q0_mulVec_mem_of_splits : ∀ {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}, (∀ z : Fin S₀.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S₀ L₀ (· = v)) → z ∈ L₀) → (∀ v, MonoAt d L L₀ v) → ∀ t ∈ L, d.q0 *ᵥ t ∈ L₀ := by
  first | exact @GlobalTheory.FinPl.CoreProj.wittCoreProjection_mem_lattice_of_splits | exact GlobalTheory.FinPl.CoreProj.wittCoreProjection_mem_lattice_of_splits | (intros; apply GlobalTheory.FinPl.CoreProj.wittCoreProjection_mem_lattice_of_splits <;> assumption)
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitConj

theorem conj_to_sq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ W v, ∃ s ∈ GlobalTheory.InertDbl.ParD σ W v, s * n * s⁻¹ = n * n := by
  intro F E _ _ _ _ _ σ B hB d W v hsplit h2 n hn
  obtain ⟨a, b, c, hq, hσa, hc, hb⟩ := GlobalTheory.T.exists_integral_generator_splitPlace_cmExtension F E σ B hB v hsplit
  obtain ⟨Eid, E1, E2, E3, E4⟩ := GlobalTheory.SplitConj.exists_adelic_idem σ W v a b c hq hσa hc hb
  obtain ⟨s, hs, hd, ha⟩ := GlobalTheory.T.exists_integralSiegelParabolic_of_conjugateIdempotent F E σ B hB d W v h2 Eid E1 E2 E3 E4
  refine ⟨s, hs, GlobalTheory.SplitConj.conj_eq_sq n hn s _ _ (GlobalTheory.LatVac.liftV v 1 - 1) ?_ ?_ hd ha⟩
  · rw [map_sub (evFin F v), GlobalTheory.LatVac.evFin_liftV, map_one (evFin F v), sub_self]
  · have h2' : (2 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) * ((⅟2 : AF F) • Eid) = Eid := by
      rw [Algebra.smul_def, ← mul_assoc, show (2 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) 2 from (map_ofNat _ 2).symm,
        ← map_mul, mul_invOf_self, map_one, one_mul]
    rw [map_sub (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), map_one (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), ← E2]
    linear_combination h2'

end GlobalTheory.SplitConj
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.antidiagonalUnipotent_conj_siegel_square_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, GlobalTheory.InertDbl.inlD σ G.V' k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.V' v ∪ GlobalTheory.InertDbl.NabD σ G.V' v) := by
  first | exact @GlobalTheory.SplitDblGenLeft.inlD_mem_closure_left | exact GlobalTheory.SplitDblGenLeft.inlD_mem_closure_left | (intros; apply GlobalTheory.SplitDblGenLeft.inlD_mem_closure_left <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.scalarSq_smul_matrix_supported_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, GlobalTheory.InertDbl.inlD σ G.W k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) := by
  first | exact @GlobalTheory.SplitDblGen.inlD_mem_closure_split | exact GlobalTheory.SplitDblGen.inlD_mem_closure_split | (intros; apply GlobalTheory.SplitDblGen.inlD_mem_closure_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.restrictedTensorProduct_irreducible_countable_dimension : ∀ {ι : Type} [DecidableEq ι] (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (s : ∀ i, N i),
    {i | s i = 0}.Finite → (∀ i, Module.rank ℂ (N i) ≤ Cardinal.aleph0) → (∀ i, Nontrivial (N i)) →
    ∀ Sv : ∀ i, Set (Module.End ℂ (N i)),
    (∀ i, ∀ Q : Submodule ℂ (N i), (∀ a ∈ Sv i, ∀ x ∈ Q, a x ∈ Q) → Q = ⊥ ∨ Q = ⊤) →
    ∀ Op : ∀ i, Module.End ℂ (N i) → Module.End ℂ (GlobalTheory.SmallThetaModules.RTens s),
    (∀ i, ∀ a ∈ Sv i, ∀ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ →
      Op i a (GlobalTheory.SmallThetaModules.pureT s ξ) = GlobalTheory.SmallThetaModules.pureT s (Function.update ξ i (a (ξ i)))) →
    ∀ Q : Submodule ℂ (GlobalTheory.SmallThetaModules.RTens s), (∀ i, ∀ a ∈ Sv i, ∀ x ∈ Q, Op i a x ∈ Q) → Q = ⊥ ∨ Q = ⊤ := by
  first | exact @GlobalTheory.rtens_irreducible | exact GlobalTheory.rtens_irreducible | (intros; apply GlobalTheory.rtens_irreducible <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.R3.DatCopy

noncomputable section

namespace GlobalTheory.Twist

set_option backward.isDefEq.lazyProjDelta false in
set_option backward.isDefEq.lazyWhnfCore false in
theorem multEq_rowTest_of_copy :
    ∀ (B : Base) (C : Cols B) (a b : Late B C) (px : PreX B.toPre) (I : ColIn B px)
      (hX : B.fields.Ok) (Tw : TwDat B) (Wt : Set B.places.Pl) (s : SameGrp a b)
      (z : Dat a.st I hX Tw Wt),
      let z' := GlobalTheory.Mem.R3.DatCopy.copy b s z
      (GlobalTheory.CuspMult.MultEq z'.R.toRealDat → GlobalTheory.CuspMult.MultEq z.R.toRealDat) ∧
        (Formalism.IndefR.Rat.RowTest (z'.R.toCx3 z'.F) →
          Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) := by
  intro B C a b px I hX Tw Wt s z
  have e := twice_eq b (iK := z.alg) z.R
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 := multEq_tr (a := b) a (iK := alg b z.alg) (R := real b z.R.toRealDat)
      (by with_unfolding_all exact h)
    rw [e]
    with_unfolding_all exact h2
  · have h2 := rowTest_tr (a := b) a (iK := alg b z.alg) (R := real3 b z.R) (F := face3 b z.F)
      (by with_unfolding_all exact h)
    rw [e]
    with_unfolding_all exact h2

end GlobalTheory.Twist

end
end
