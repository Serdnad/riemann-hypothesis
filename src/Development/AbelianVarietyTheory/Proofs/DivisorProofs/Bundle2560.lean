module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfFlatPullbackReduction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle971
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle973
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2552
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem abelianSchemeLifts_of_hodgeDeRham (hC : CrystallineSmoothLift) (hH : AbelianHodgeDeRham) :
    AbelianSchemeLifts := by
  intro R _ _ I hI R₀ _ π hπ hk g A₀ _ A' _ i' h' hA hg
  haveI : IsNoetherianRing R₀ := isNoetherianRing_of_surjective R R₀ π hπ
  obtain ⟨-, -, -, -, -, -, hA₀, hg₀⟩ := GlobalTheory.T.abelianLift_reduction_standard_facts hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  have hG : Good A₀.hom := GlobalTheory.T.goodForSquareZeroLiftClassification_of_abelianScheme hC hH R₀ A₀ g hA₀ hg₀
  have hR : RhoBC hI hk A₀.hom := GlobalTheory.T.abelianScheme_crystal_reduces_to_deRham_sqZero hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨ad1, ad2, ad3⟩ := GlobalTheory.T.admissible_deRhamHomology_summands_crystal hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨S', ⟨P'⟩⟩ := GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk A₀.left A₀.hom A'.left A'.hom i' h'.1 hA.smooth
  obtain ⟨hF', hc'⟩ := GlobalTheory.T.abelian_scheme_presented_by_system hC hH R R₀ I hI π hπ hk g A₀ A' i' h' hA hg S' P'
  have core1 := GlobalTheory.T.squareZeroLiftSystem_filtration_direct_summand R R₀ I hI π hπ hk A₀.left A₀.hom hG hR S' hF' hc'
  have ksup := GlobalTheory.T.mem_liftSystemFiltration_sup_iff_hodgeFiltration R R₀ I hI π hπ hk A₀.left A₀.hom S' hR hF'
  have fil : ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left) (h : IsPullback i A₀.hom X.hom (spMap π)), Smooth X.hom →
      ∀ S : Sys I π A₀.hom, S.Presents X.hom i → schemeFil (divided₂ hI) A₀ X i h.w =
        ((S.K hI).comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator := fun X i h hX S P ↦
    congrArg Submodule.dualAnnihilator
      (GlobalTheory.T.primitiveCrystalHodgeLiftClasses_eq_comap_sys hC R R₀ I hI π hπ hk A₀ hA₀.proper hA₀.geomConnected X i h hX S P)
  refine ⟨⟨fun X i h hX ↦ ?_, fun F hF ↦ ?_⟩, fun X Y i j h k hX hY e ↦ ?_⟩
  · obtain ⟨S, ⟨P⟩⟩ := GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk A₀.left A₀.hom X.left X.hom i h hX
    obtain ⟨hc, hs⟩ := core1 S
    obtain ⟨F, hF, e⟩ := ad1 (S.K hI) hc fun c ↦ by rw [hs]; exact ksup c
    exact ⟨F, hF, (fil X i h hX S P).trans e⟩
  · obtain ⟨K, hc, hs, e⟩ := ad2 F hF
    obtain ⟨S, rfl⟩ := GlobalTheory.T.exists_squareZeroLiftSystem_of_summand_reduction R R₀ I hI π hπ hk A₀.left A₀.hom hG hR S' hF' hc' K hc
      (Submodule.ext fun c ↦ (hs c).trans (ksup c).symm)
    obtain ⟨X, s, i, h1, h2, ⟨P⟩⟩ := GlobalTheory.T.exists_scheme_presenting_squareZeroSmoothLiftSystem R R₀ I hI π hπ hk A₀.left A₀.hom S
    obtain ⟨h, hX⟩ := GlobalTheory.T.isSmoothLift_of_squareZeroLiftSystemPresents R R₀ I hI π hπ hk A₀.left A₀.hom S X s i h1 h2 P
    exact ⟨Over.mk s, i, h, hX, (fil (Over.mk s) i h hX S P).trans e⟩
  · obtain ⟨S, ⟨P⟩⟩ := GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk A₀.left A₀.hom X.left X.hom i h hX
    obtain ⟨T, ⟨Q⟩⟩ := GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk A₀.left A₀.hom Y.left Y.hom j k hY
    have hK : T.K hI = S.K hI := ad3 _ _ (core1 T).1 (core1 S).1
      ((fil Y j k hY T Q).symm.trans (e.symm.trans (fil X i h hX S P)))
    have hT : T.Full hI := (GlobalTheory.T.squareZeroLiftSystem_filtration_inf_eq_and_full R R₀ I hI π hπ hk A₀.left A₀.hom hG.const S' T).2 hF'
    obtain ⟨f, hf, hij⟩ := GlobalTheory.T.exists_morphism_liftSystemPresents_of_hom R R₀ I hI π hπ hk A₀.left A₀.hom T S X.left X.hom i Y.left Y.hom j h Q P
      (GlobalTheory.T.exists_squareZeroLiftSystem_hom_of_filtration_eq R R₀ I hI π hπ hk A₀.left A₀.hom hG hR T S hT hK)
    haveI := hX
    have hn : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk]; exact hI⟩
    haveI : IsIso (Over.homMk f hf : X ⟶ Y) :=
      GlobalTheory.NilThickIso.isIso_of_flat_of_isIso_reduction R R₀ π hπ hn X Y A₀ A₀ i j h k inferInstance
        (Over.homMk f hf) (𝟙 A₀) (by simpa using hij) inferInstance
    exact ⟨asIso (Over.homMk f hf : X ⟶ Y), hij⟩

end GlobalTheory.LiftSys
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

theorem _root_.GlobalTheory.T.exists_innerProductFormula_data_definite_bottom : GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → A.SigOK → ∀ t : T,
  ∃ (χA χB : (AE D)ˣ →* Circle) (sA : RealMat (GlobalTheory.Grid.neg A)) (sB : RealMat WW) (cA : CptF (GlobalTheory.Grid.neg A))
    (a : GL (Fin (GlobalTheory.Grid.neg A).rank) (AE D)) (νW : Measure (WO (GlobalTheory.Grid.neg A) WW)) (𝓕W : Set (WO (GlobalTheory.Grid.neg A) WW))
    (LA : Lat (GlobalTheory.Grid.neg A)) (LB : Lat WW) (Sf : Finset (FinPl D)) (par : GlobalTheory.LFun.Fam D.host.E) (κ : ℂ) (P : PolF D WW.rank A.rank),
    Pair W.ψ W.θ (GlobalTheory.Grid.neg A) WW χA χB sA sB A'.rank cA a ((X.ω t).toSgn true) νW 𝓕W ∧ wittIndex WW = 0 ∧
    IsFockVec W.ψ W.θ (GlobalTheory.Grid.neg A) WW sA sB (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) ∧ Unram W.ψ (GlobalTheory.Grid.neg A) WW χB LA LB Sf (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) ∧
    (fun _ => (1 : ℂ)) ∈ A0 W.θ (GlobalTheory.Grid.neg A) cA ∧
    GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram LA (Sf : Set (FinPl D)) (fun _ => (1 : ℂ)) par ∧
    SphFun (GlobalTheory.Grid.neg A) LA Sf (fun _ => (1 : ℂ)) ∧ κ ≠ 0 ∧
    GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) ≠ 0 ∧
    (∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ →
      HolValueAt (fun s => GlobalTheory.LFun.LSD D Sf par χB (s + 1 / 2)) ((A'.rank : ℂ) / 2)
        (κ * GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) *
          ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s)) ∧
    ∀ m : Measure (GA D (GlobalTheory.Grid.neg A)), m.IsHaarMeasure →
      (∃ s₁ : ℝ, s₁ < (A'.rank : ℝ) / 2 ∧ IntegrableOn
        (integrand ((X.ω t).toSgn true) m νW 𝓕W LA a (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (fun _ => 1) (fun _ => 1) s₁) (openOff (GlobalTheory.Grid.neg A) LA Sf) m) ∧
      ∫ g in openOff (GlobalTheory.Grid.neg A) LA Sf, wcoef ((X.ω t).toSgn true) νW 𝓕W (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) g * rcoef m (fun _ => 1) (fun _ => 1) g ∂m ≠ 0 := by
  first | exact @GlobalTheory.BottomIPData.data_exists | exact GlobalTheory.BottomIPData.data_exists | (intros; apply GlobalTheory.BottomIPData.data_exists <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.GoodLat.Obj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Arith Formalism.IndefR.FWT

theorem nV_pos (D : D7) : 0 < D.R.nV := by
  have := D.R.three_m_lt_t
  rw [Ranks.nV]
  omega

theorem fullLat {D : D7} (T : Core D) (hT : LawsM T) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) (hn : 0 < w.n) :
    FullLat (T.cuspA j (wtA w) w.n) (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)) fun la => isVal_valSet la :=
  (GlobalTheory.IndefiniteRowSideFullHecke.SupremumLattice.supIn_full_iff _ _ _).1
    (GlobalTheory.SupFull.fullAt_of_pins D T hT.pins j hj (hT.unf j hj _ T.good_σ₀) w hn)

section Real

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem latFull (T : CoreJ D) (hT : LawsJ T) {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} (hκ : KapIs κ) :
    LatFull T κ := fun i =>
  fullLat T.toCore hT.toLawsM (inR i) (κ i) (by rw [(hκ i (D.eTau.symm 1)).2.2]; exact nV_pos D)

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem mkFull_of_tie (t : FWTie T R κ v₀) (i : Fin D.R.m) : (R.FW i).MKFull :=
  GlobalTheory.GoodLat.mkFull_of_tie t (latFull T t.laws t.kap) i

theorem mLat_of_tie (t : FWTie T R κ v₀) (F : Face D A) (b : Bool) : (R.toCx F).MLat b :=
  GlobalTheory.GoodLat.mLat_of_tie t (latFull T t.laws t.kap) F b

end Real

end GlobalTheory.GoodLat.Obj
end
end
