module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLaws
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFETranslateFeTranslate
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle540
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle054
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle017
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle674
public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle677
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SquareSectionWeightZero

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), ∃ (σ : H0 U.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) ∧ ¬ ∀ j, (f 0).f j = 0 := by
  intro R _ _ _ _ G _ _ _ D A U
  obtain ⟨h1, h2, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨E, hE⟩ := GlobalTheory.FamFree.exists_fam_support (F := FractionRing R) h1.globalFns h2.secTwist
    D.tau_bimult (k := 2) (by norm_num) (0 : D.toPre.X)
  have hE0 : ¬ ∀ j, (E.s 0).f j = 0 := (hE 0).2 ⟨0, by simp⟩
  obtain ⟨s, hs, -⟩ := (U.expand 2 (by norm_num)).2 E
  obtain ⟨r, hr, σ, f, -, hf, hexp⟩ := hs
  refine ⟨σ, f, hexp, fun h0 => hE0 ?_⟩
  have key := (GlobalTheory.ConstFam.secScal_iff_resF D.toPre (FractionRing R) (E.s 0) (f 0) r).1 (hf 0)
  have hf0 : (f 0 : GlobalTheory.ConstFam.SecBMod D.toPre 2 0) = 0 := ReciprocityTheory.ChartRestriction.G.DVR.SecOps.sec_ext h0
  rw [hf0] at key
  erw [map_zero] at key
  have hr' : GlobalTheory.ConstFam.toF (R := R) (FractionRing R) r ≠ 0 := by
    intro h
    apply hr
    have hinj : Function.Injective (GlobalTheory.ConstFam.toF (R := R) (FractionRing R)) :=
      (algebraMap (FractionRing R) (FractionRing R)).injective.comp (IsFractionRing.injective R _)
    exact hinj (h.trans (map_zero _).symm)
  let t : GlobalTheory.ConstFam.SecFMod D.toPre (FractionRing R) 2 0 := E.s 0
  have k2 : GlobalTheory.ConstFam.toF (R := R) (FractionRing R) r • t = 0 := key.symm
  have e0 : t = 0 := by rw [← inv_smul_smul₀ hr' t, k2, smul_zero]
  intro j
  exact congrArg (fun q : GlobalTheory.ConstFam.SecFMod D.toPre (FractionRing R) 2 0 => LB.Sec.f q j) e0

end GlobalTheory.SquareSectionWeightZero
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.UnifCoordPull

theorem exists_unif_psiCoord : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN R → IsCN V → ∀ ψ : R →+* V, IsLocalHom ψ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (W : Set (Sp R)), IsOpen W → (∀ y, PsiUnitOn D.toPre y W) → (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ W → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap ψ) β → IsAbelianScheme ((Over.pullback (jK V)).obj G') → Rigidified ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → Out.Sym ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → RelAmple ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → KTriv ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → ∃ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (ε : D'.toPre.X ≃+ D.toPre.X), LBIso (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) (U'.LG.L.pull (pullback.fst G'.hom (jK V))) ∧ ∀ y r, PsiCoord D.toPre (ε y) r → ∃ u : Vˣ, PsiCoord D'.toPre y (u * ψ r) := by
  intro R _ _ _ V _ _ _ hR hV ψ hψl G _ _ hG D A U W hWo hψ hker G' _ _ β hpb hab hrig hsym hamp hkt
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.firstFiveLaws
  have aR := admissibleBase_of_completeNormalLocalCharZero hR
  have aV := admissibleBase_of_completeNormalLocalCharZero hV
  have hI : (maximalIdeal R).map ψ ≤ maximalIdeal V :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff ψ a).2 ha
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hpb (isGrpPullback_pullback G (spMap ψ))
  subst hbc

  have := hG.smooth
  have := hG.geomConnected
  have : ConnectedSpace (Sp R) := inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have hgA := GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
  have hgK := (isGrpPullback_pullback G' (jK V)).comp hpb
  have dA : d = A.g := H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgA.1 hd)
    A.smoothDim (eSec A.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)))
  have hdK : SmoothOfRelativeDimension A.g ((Over.pullback (jK V)).obj G').hom :=
    dA ▸ (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgK.1 hd
  have he := GlobalTheory.PolBaseChange.eSec_comm hpb
  let A' : PolAV (Sp (FractionRing V)) :=
    { A := (Over.pullback (jK V)).obj G'
      isAb := hab
      g := A.g
      smoothDim := hdK
      L := U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G.hom (spMap ψ))
      isLB := pull_isLB U.LG.isLB _
      rigid := hrig
      sym := hsym
      ample := hamp
      ktriv := hkt }
  have eAm : IsMonHom (Iso.refl A'.A).hom := show IsMonHom (𝟙 A'.A) from inferInstance
  have wA : ∃ wA : LB.Iso (A'.L.pull (Iso.refl A'.A).hom.left)
      (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ψ))), wA.IsGen := by
    have k : LBIso (A'.L.pull (𝟙 _)) (U.LG.L.pull (𝟙 _ ≫ pullback.fst G'.hom (jK V) ≫ bc.hom.left ≫
        pullback.fst G.hom (specOf ψ))) :=
      ⟨GlobalTheory.Proof.TautologicalModel.taut U.LG.L _ (𝟙 _), GlobalTheory.Proof.TautologicalModel.taut_isGen U.LG.isLB _ _⟩
    rw [Category.id_comp] at k
    exact k
  let L' : RigLB G' := ⟨U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (spMap ψ)),
    rigPullOf (G' := G') (G := G) (bc.hom.left ≫ pullback.fst G.hom (spMap ψ)) (spMap ψ) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _,
    GlobalTheory.Proof.TautologicalModel.rigPullOf_isGen (G' := G') (G := G) (bc.hom.left ≫ pullback.fst G.hom (spMap ψ)) (spMap ψ) he U.LG.L U.LG.rig U.LG.rigGen⟩
  obtain ⟨wL, gL, rL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap ψ) G G' _ he U.LG L'
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U.LG.isLB _))
  have hgen : (specOf ψ).base (genericPoint (Spec (CommRingCat.of V))) ∈ (⟨W, hWo⟩ : (Sp R).Opens) := by
    have : (specOf ψ).base (genericPoint (Spec (CommRingCat.of V))) =
        (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext rfl
    rw [this]; exact hker
  obtain ⟨D', hD, U', hLG, -, -⟩ := h4.unifBaseChange R V _ _ aR aV ψ hI D A G hG U ⟨W, hWo⟩
    (GlobalTheory.PelCoordPull.nonempty_psiOn D.toPre ⟨W, hWo⟩ ⟨_, hker⟩ hψ) hgen G' bc mbc A' rfl (Iso.refl _) eAm wA
    L' wL he gL rL
  refine ⟨D', A', U', hD.xe, ?_, fun y r hr => GlobalTheory.PelCoordPull.psiCoord_pull hD y r hr⟩
  rw [hLG]
  exact LBIso.symm ⟨GlobalTheory.Proof.TautologicalModel.taut U.LG.L _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen U.LG.isLB _ _⟩

end GlobalTheory.UnifCoordPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqTransport


open ReciprocityTheory.ChartRestriction.G.DVR in
theorem exists_transport_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen → ∀ (σ : H0 U.LG.L 2), ∃ (σ' : H0 U'.LG.L 2) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') := by
  intro R _ _ _ hCN G _ _ _ D D' A A' U U' wL hwL σ
  have hR := TorRef.admissibleBase_of_completeNormalLocalCharZero hCN
  haveI : IsNoetherianRing R := hR.1
  have hL := linComb_isLB U.LG.L U.LG.isLB (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)
  have hL' := linComb_isLB U'.LG.L U'.LG.isLB (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)
  let σ' : H0 U'.LG.L 2 := secOfIso σ hwL hL' hL
  obtain ⟨s, hs⟩ := exists_sec U'.LG.isLB (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R))
    (ε' := fun _ => ((2 : ℕ) : ℤ)) (fun _ _ h => by simp only [Category.comp_id])
    (H1.SectionArithmetic.pullSec σ' (pullback.fst G.hom (jK R)))
  obtain ⟨E, hsE, -⟩ := (U'.expand 2 (by norm_num)).1 s
  obtain ⟨f', hf', -⟩ := IntegralExpansionLocal.main R (maximalIdeal R) le_rfl D' A' G U'.toUnifPre 2 σ' s
    (SectionScalarValuation.secScal_of_sval U'.LG.isLB fun y J hJ =>
      ((hs _ _ y J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ y hJ)).symm) E hsE
  refine ⟨σ', f', hf', fun Z r z J J' hJ hJ' => ?_⟩
  have hm : r z ∈ (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)).U (fun _ => J' r) ⊓
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)).U (fun _ => J r) :=
    ⟨Set.mem_iInter.2 fun _ => hJ' r, Set.mem_iInter.2 fun _ => hJ r⟩
  have e := gs_secOfIso_eq wL σ hwL hL' hL (fun _ => J' r) (fun _ => J r) r z hm
  rw [sval_of σ r z J (fun _ => J r) (fun _ => by rw [Category.comp_id]),
    sval_of σ' r z J' (fun _ => J' r) (fun _ => by rw [Category.comp_id])]
  show _ = (gm r z _ (wL.s ((fun _ => J r), (fun _ => J' r)))).val * _
  have e' : gs r z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J' r) (σ'.f fun _ => J' r) =
      ((gm r z _ (wL.s ((fun _ => J r), (fun _ => J' r))))⁻¹).val *
        gs r z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J r) (σ.f fun _ => J r) := e
  rw [e', ← _root_.mul_assoc, ← Units.val_mul, _root_.mul_inv_cancel, Units.val_one, _root_.one_mul]

end GlobalTheory.SqTransport
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqCube

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.LamBiext

section Transport

variable {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']

theorem transport (hG : GlobalFnsSt) (hA' : IsAbelianScheme A') (Φ : A' ⟶ A) [IsMonHom Φ]
    {M : LB A.left} {M' : LB A'.left} (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (M.pull Φ.left)) (hw : w.IsGen)
    (c : LB.Gen (LB.LinComb M (thφ A (x3 A)) thε)) (c' : LB.Gen (LB.LinComb M' (thφ A' (x3 A')) thε))
    (hc : c.IsGen) (hc' : c'.IsGen)
    (n : ∀ (y : (𝟙_ (Over S)).left) J, Good M y J →
      val c (lift (1 : 𝟙_ (Over S) ⟶ A) (lift 1 1)).left y J = 1)
    (n' : ∀ (y : (𝟙_ (Over S)).left) J, Good M' y J →
      val c' (lift (1 : 𝟙_ (Over S) ⟶ A') (lift 1 1)).left y J = 1)
    {T : Over S} {z : T.left} {J J'} (hJ : Good M z J) (hJ' : Good M' z J') (x x' y : T ⟶ A') :
    val c (lift (x ≫ Φ) (lift (x' ≫ Φ) (y ≫ Φ))).left z J =
      (∏ I : thK.{0}, gw w ((lift x (lift x' y)).left ≫ thφ A' (x3 A') I) z
        (J (((lift x (lift x' y)).left ≫ thφ A' (x3 A') I) ≫ Φ.left))
        (J' ((lift x (lift x' y)).left ≫ thφ A' (x3 A') I)) ^ thε I) * val c' (lift x (lift x' y)).left z J' := by
  let m3 : G3 A' ⟶ G3 A := lift (x3 A' 0 ≫ Φ) (lift (x3 A' 1 ≫ Φ) (x3 A' 2 ≫ Φ))
  let β : (G3 A' ⟶ A') →* (G3 A' ⟶ A) := MonoidHom.mk' (· ≫ Φ) fun a b => MonObj.mul_comp a b Φ
  have hx : ∀ i, m3 ≫ x3 A i = x3 A' i ≫ Φ := fun i => by fin_cases i <;> simp [m3, x3]
  have comm : ∀ I : thK.{0}, m3.left ≫ thφ A (x3 A) I = thφ A' (x3 A') I ≫ Φ.left := fun I => by
    have e : m3 ≫ psum A (x3 A) I.down = psum A' (x3 A') I.down ≫ Φ :=
      (psum_hom (Geo.Tor.preHom m3) (x3 A) I.down).trans ((congrArg (fun q => psum A q I.down) (funext hx)).trans
        (psum_hom β (x3 A') I.down).symm)
    exact congrArg (fun q => q.left) e
  have q : ∀ {T : Over S} (a b d : T ⟶ A'),
      (lift a (lift b d)).left ≫ m3.left = (lift (a ≫ Φ) (lift (b ≫ Φ) (d ≫ Φ))).left := fun a b d => by
    rw [← Over.comp_left]; congr 1; simp [m3, x3]
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hM hM' c' hc'
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 A').left) (z : Z) J J', Good M z J → Good M' z J' →
      val t r z J = (∏ I : thK.{0}, gw w (r ≫ thφ A' (x3 A') I) z
        (J ((r ≫ thφ A' (x3 A') I) ≫ Φ.left)) (J' (r ≫ thφ A' (x3 A') I)) ^ thε I) * val c' r z J' :=
    fun Z r z J J' hJ hJ' => by
      refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans
        (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
      rw [Category.assoc]
  let e : 𝟙_ (Over S) ⟶ G3 A' := lift 1 (lift 1 1)
  have sj : Function.Surjective ((snd A' (A' ⊗ A')).left ≫ (snd A' A').left ≫ A'.hom).appTop.hom :=
    surj_comp (surj_snd hG hA' _) (surj_comp (surj_snd hG hA' _) (hG _ _ hA').2)
  have he : e.left ≫ (snd A' (A' ⊗ A')).left ≫ (snd A' A').left ≫ A'.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := gen_unique' hM (φ := fun I => m3.left ≫ thφ A (x3 A) I) (ε := thε)
    (fun V _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ thε I) (comm I).symm)
    _ e.left he sj (pullGen_isGen _ _ _ _ hc m3.left) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over S)).left ⟶ A'.left => exists_chart hM' (χ y)
      have p := prod_cub (1 : 𝟙_ (Over S) ⟶ A') 1 1 (fun q => gw w q y (I (q ≫ Φ.left)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine Eq.trans ?_ ((hv' _ e.left y I I' hI hI').trans (congrArg₂ (· * ·) p (n' y I' hI'))).symm
      rw [val_pull hI, q, MonObj.one_comp, n y I hI]
      simp) _ (lift x (lift x' y)).left z J hJ
  rw [val_pull hJ, q] at key
  exact key.trans (hv' _ _ z J J' hJ hJ')

end Transport

section Chart

variable {X Y : Scheme.{0}} {L : LB X}

theorem good_sq {y : Y} {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) :
    Good (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)) y (fun q _ => J q) :=
  fun ψ => Set.mem_iInter.2 fun _ => by simpa using hJ ψ

theorem adj_sq (hL : L.IsLB) {y : Y} {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) (χ : Y ⟶ X) :
    adj (fun _ : Fin 1 => 𝟙 X) (fun _ => (2 : ℤ)) y (fun q _ => J q) J χ = 1 := by
  have m := hJ.mem (fun _ : Fin 1 => 𝟙 X) χ
  simp only [Category.comp_id] at m
  unfold adj
  simp only [Category.comp_id]
  exact trF_self hL _ _ χ y m

end Chart

section Square

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem sq_formEq : FormEq (Sum.elim (thφ G (x3 G)) (thφ G (x3 G))) (Sum.elim thε thε)
    (flatφ (fun _ : Fin 1 => 𝟙 G.left) (thφ G (x3 G))) (flatε (fun _ : Fin 1 => (2 : ℤ)) thε) := fun U _ h => by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun I _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, flatφ, flatε, Category.comp_id]
  rw [zpow_mul, zpow_two]

theorem exists_sqCube {L : RigLB G} (c : CubicalStr G L) :
    ∃ u : LB.Gen (LB.LinComb (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (thφ G (x3 G)) thε),
      u.IsGen ∧ (∀ {T : Over S} (y : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L y J →
        ∀ (JP : (T.left ⟶ G.left) → Fin 1 → L.L.ι), Good (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) y JP →
        ∀ a b d : T ⟶ G, val u (lift a (lift b d)).left y JP =
          (∏ I : thK.{0}, adj (fun _ : Fin 1 => 𝟙 G.left) (fun _ => 2) y JP J ((lift a (lift b d)).left ≫ thφ G (x3 G) I) ^ thε I) *
            cubV c y J a b d ^ 2) ∧
      ∀ (y : (𝟙_ (Over S)).left) JP, Good (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) y JP →
        val u (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left y JP = 1 := by
  obtain ⟨s, hs, hv⟩ := exists_gen L.isLB sq_formEq (LB.mulGen L.L (thφ G (x3 G)) thε (thφ G (x3 G)) thε c.t c.t)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ c.isGen c.isGen)
  have F : ∀ {T : Over S} (y : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L y J →
        ∀ (JP : (T.left ⟶ G.left) → Fin 1 → L.L.ι), Good (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) y JP →
        ∀ a b d : T ⟶ G, val (nest L.L _ _ _ _ s) (lift a (lift b d)).left y JP =
          (∏ I : thK.{0}, adj (fun _ : Fin 1 => 𝟙 G.left) (fun _ => 2) y JP J ((lift a (lift b d)).left ≫ thφ G (x3 G) I) ^ thε I) *
            cubV c y J a b d ^ 2 := fun y J hJ JP hJP a b d => by
    rw [val_nest hs _ hJP hJ, hv _ _ y J hJ]
    exact congrArg _ ((val_mul hJ _ _ _).trans (sq _).symm)
  refine ⟨nest L.L _ _ _ _ s, nest_isGen hs, F, fun y JP hJP => ?_⟩
  choose J hJ using fun χ : (𝟙_ (Over S)).left ⟶ G.left => exists_chart L.isLB (χ y)
  change ((𝟙_ (Over S)).left ⟶ G.left) → Fin 1 → L.L.ι at JP
  set_option backward.isDefEq.respectTransparency false in
  have hcub : cubV c y J (1 : 𝟙_ (Over S) ⟶ G) 1 1 = 1 :=
    by
      have h := val_corr hJ (c.face 0) (lift (1 : 𝟙_ (Over S) ⟶ G) 1).left
      rw [val_one, val_pull hJ _ _ _, ← Over.comp_left] at h
      convert h using 1 <;> simp [cubV, faceMap, x2, pzero, Hom.one_def]
  rw [F y J hJ JP hJP]
  rw [prod_cub, hcub]
  simp

end Square

end GlobalTheory.SqCube

theorem GlobalTheory.cube_sq_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → ∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2 := by
  intro R _ _ _ _ D D' Φ w hw hΦ T z J J' hJ hJ' Ω hΩ a b c
  subst hΩ
  obtain ⟨u, hu, hvu, nu⟩ := GlobalTheory.SqCube.exists_sqCube D.toPre.cub
  obtain ⟨u', hu', hvu', nu'⟩ := GlobalTheory.SqCube.exists_sqCube D'.toPre.cub
  have key := GlobalTheory.SqCube.transport GlobalTheory.globalFns_holds D'.toPre.P.isAb Φ.hom
    (DVR.linComb_isLB _ D.toPre.P.isLB _ _) (DVR.linComb_isLB _ D'.toPre.P.isLB _ _) w hw u u' hu hu' nu nu'
    (GlobalTheory.SqCube.good_sq hJ) (GlobalTheory.SqCube.good_sq hJ') a b c
  rw [hvu z J hJ _ (GlobalTheory.SqCube.good_sq hJ), hvu' z J' hJ' _ (GlobalTheory.SqCube.good_sq hJ')] at key
  simp only [GlobalTheory.SqCube.adj_sq D.toPre.P.isLB hJ, GlobalTheory.SqCube.adj_sq D'.toPre.P.isLB hJ', one_zpow,
    Finset.prod_const_one, _root_.one_mul] at key
  refine key.trans ?_
  rw [prod_cub a b c (fun q => gw w q z (fun _ => J (q ≫ Φ.hom.left)) (fun _ => J' q))]
  rfl
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR in

theorem expansion_sums_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ (σ : H0 U.LG.L 2) (σ' : H0 U'.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') → (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') → ∀ e : ℕ, ∃ S : Finset D'.toPre.X, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → (∀ α' ∉ S, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J = 0) ∧ (∀ α' ∉ S, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' = 0) ∧ ∑ α' ∈ S, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (xe α')) r z J).val = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left)).val * ∑ α' ∈ S, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val := by
  intro R _ _ _ _ G _ _ _ D D' A A' U U' Φ w wL _ _ _ hlev xe _ σ σ' f f' hE hE' hσ e
  classical
  obtain ⟨S₁, hS₁⟩ := expandsAt_val U.toUnifPre e 2 σ f (hE e)
  obtain ⟨S₂, hS₂⟩ := expandsAt_val U'.toUnifPre e 2 σ' f' (hE' e)
  refine ⟨S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂, fun Z r z J J' hJ hJ' => ?_⟩
  obtain ⟨A₁, B₁⟩ := hS₁ Z r z J hJ
  obtain ⟨A₂, B₂⟩ := hS₂ Z r z J' hJ'
  have z₁ : ∀ α' ∉ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J = 0 := by
    intro α' hα
    refine A₁ _ fun hc => hα (Finset.mem_union_left _ (Finset.mem_map.2 ⟨xe α', hc, xe.symm_apply_apply α'⟩))
  have z₂ : ∀ α' ∉ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f' α') (r ≫ (U'.gt e).pG.left) z J' = 0 := by
    intro α' hα
    exact A₂ _ fun hc => hα (Finset.mem_union_right _ hc)
  refine ⟨z₁, z₂, ?_⟩

  have E₁ : ∑ α' ∈ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (xe α')) r z J).val =
      ∑ α ∈ S₁, sval (f α) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t α) r z J).val := by
    rw [← Finset.sum_subset (Finset.subset_union_left) (fun α' _ hα => by
      rw [A₁ (xe α') fun hc => hα (Finset.mem_map.2 ⟨xe α', hc, xe.symm_apply_apply α'⟩), zero_mul]),
      Finset.sum_map]
    refine Finset.sum_congr rfl fun α _ => ?_
    have h₀ : xe (xe.symm.toEquiv.toEmbedding α) = α := xe.apply_symm_apply α
    rw [h₀]
  have E₂ : ∑ α' ∈ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val =
      ∑ α' ∈ S₂, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val :=
    (Finset.sum_subset (Finset.subset_union_right) (fun α' _ hα => by rw [A₂ α' hα, zero_mul])).symm
  rw [E₁, E₂]
  obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((fstG (maximalIdeal R) e G).left (r z))
  obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG (maximalIdeal R) e G).left (r z))
  rw [← B₁ jL hL, ← B₂ jL' hL']
  obtain ⟨J₀, hJ₀, k₀⟩ := exists_good U.LG.L U.LG.isLB z (fun _ : PUnit => r ≫ (fstG (maximalIdeal R) e G).left)
    (fun _ => jL) (fun _ _ _ => rfl) (fun _ => hL)
  obtain ⟨J₀', hJ₀', k₀'⟩ := exists_good U'.LG.L U'.LG.isLB z (fun _ : PUnit => r ≫ (fstG (maximalIdeal R) e G).left)
    (fun _ => jL') (fun _ _ _ => rfl) (fun _ => hL')
  have c₀ : J₀ (r ≫ (fstG (maximalIdeal R) e G).left) = jL := k₀ PUnit.unit
  have c₀' : J₀' (r ≫ (fstG (maximalIdeal R) e G).left) = jL' := k₀' PUnit.unit
  have hS : sv U.toUnifPre 2 σ (r ≫ (fstG (maximalIdeal R) e G).left) z jL =
      (gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')).val *
        sv U'.toUnifPre 2 σ' (r ≫ (fstG (maximalIdeal R) e G).left) z jL' := by
    have H := hσ Z (r ≫ (fstG (maximalIdeal R) e G).left) z J₀ J₀' hJ₀ hJ₀'
    rw [sval_of σ _ z J₀ (fun _ => jL) (fun _ => by rw [Category.comp_id]; exact c₀),
      sval_of σ' _ z J₀' (fun _ => jL') (fun _ => by rw [Category.comp_id]; exact c₀'), c₀, c₀'] at H
    exact H
  have W : gw w (r ≫ (U'.gt e).pG.left) z (fun _ => J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left)) *
        wv U'.toUnifPre e r z (J' (r ≫ (U'.gt e).pG.left)) jL' ^ 2 =
      wv U.toUnifPre e r z (J (r ≫ (U.gt e).pG.left)) jL ^ 2 *
        gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL') :=
    (hlev e).2 Z r z (J (r ≫ (U.gt e).pG.left)) (J' (r ≫ (U'.gt e).pG.left)) jL jL' (hJ _) (hJ' _) hL hL'
  have hO : ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left) =
      gw w (r ≫ (U'.gt e).pG.left) z (fun _ => J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left)) := by
    show gw w (r ≫ (U'.gt e).pG.left) z (fun _ => J ((r ≫ (U'.gt e).pG.left) ≫ Φ.hom.left))
      (fun _ => J' (r ≫ (U'.gt e).pG.left)) = _
    rw [Category.assoc, (hlev e).1]
  rw [hS, hO, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, W]

end GlobalTheory
end

section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.trace_bounded_of_aeval_monic_eq_zero : ∀ (p : Polynomial ℤ), p.Monic → ∀ n : ℕ, ∃ K : ℝ, ∀ M : Matrix (Fin n) (Fin n) ℤ, Polynomial.aeval M p = 0 → ((M.trace : ℤ) : ℝ) ≤ K := by
  first | exact @GlobalTheory.RedTh.trace_le_of_aeval_monic_eq_zero | exact GlobalTheory.RedTh.trace_le_of_aeval_monic_eq_zero | (intros; apply GlobalTheory.RedTh.trace_le_of_aeval_monic_eq_zero <;> assumption)
end

section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.siegelUnipotent_inverse_entries_bounded : ∀ n : ℕ, ∃ c : ℝ, ∀ u : Matrix (Fin n) (Fin n) ℝ, (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (∀ i j, i < j → |u i j| ≤ 1 / 2) → ∃ v : Matrix (Fin n) (Fin n) ℝ, v * u = 1 ∧ u * v = 1 ∧ (∀ i j, j < i → v i j = 0) ∧ ∀ i j, |v i j| ≤ c := by
  first | exact @GlobalTheory.siegel_unipotent_inv_bounded | exact GlobalTheory.siegel_unipotent_inv_bounded | (intros; apply GlobalTheory.siegel_unipotent_inv_bounded <;> assumption)
end
