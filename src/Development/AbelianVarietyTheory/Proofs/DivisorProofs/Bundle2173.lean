module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle992

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistKerSurj

theorem exists_point_geom : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (K : Type) [Field K] [IsAlgClosed K] (ξ : Sp K ⟶ S) (M : LB (A ⊗ Over.mk ξ).left), Fam A M → ∃ a : Over.mk ξ ⟶ A, Same A (abelian₂ A L) M a (𝟙 _) := by
  intro S A _ hA L hL hAmp K _ _ ξ M hM
  obtain ⟨A', _, φ, hφ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A ξ
  have := hA
  have : IsProper A.hom := IsAbelianScheme.proper
  have hA' : IsAbelianScheme A' := by
    have : IsCommMonObj A := hA.comm
    have hc : IsCommMonObj A' := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hφ.2 T x y (pushPt hφ.1.w x) (pushPt hφ.1.w y) rfl rfl,
        ← hφ.2 T y x (pushPt hφ.1.w y) (pushPt hφ.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hφ.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hφ.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hφ.1 hA.geomConnected⟩
  have := hA'
  have : IsCommMonObj A := IsAbelianScheme.comm
  have : IsCommMonObj A' := IsAbelianScheme.comm
  have hL' : (L.pull φ).IsLB := pull_isLB hL φ
  have hAmp' : Out.RelAmple A' (L.pull φ) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hAmp hφ.1
  have hs : 𝟙 (Sp K) ≫ ξ = ξ := Category.id_comp ξ
  have hN' : Fam A' (M.pull (BaseChange.toBase hφ hs)) := BaseChange.fam_toBase hφ hs hM
  obtain ⟨a', ha'⟩ := GlobalTheory.T.additiveLineBundle_eq_mumfordLambda_of_ample_algClosed K A' hA' (L.pull φ) hL' hAmp' _ hN'
  refine ⟨GlobalTheory.AbDual.pushP hφ hs a', ?_⟩

  obtain hsq := GlobalTheory.LamPull.exists_isSquare (G := A) (G' := A') (f := ξ) (φ := φ) hφ.1.w
  have hLam : (abelian₂ A L).IsLB := FullSiegel.isLB_lam hL
  have hLam' : (abelian₂ A' (L.pull φ)).IsLB := FullSiegel.isLB_lam hL'
  have eLam := (GlobalTheory.LamPull.lbIso_lam_pull hφ hL hL' (GlobalTheory.lbIso_self hL') hsq).symm
  have h0 := (same_iff hN'.isLB hLam' _ _).mp ha'
  have e1 : evc hN'.isLB (fst A' (𝟙_ (Over (Sp K)))) (snd A' (𝟙_ (Over (Sp K))) ≫ 𝟙 _) =
      GlobalTheory.CechPic.pull (BaseChange.toBase hφ hs) (evc hM.isLB (fst A (Over.mk ξ)) (snd A (Over.mk ξ) ≫ 𝟙 _)) := by
    simp only [GlobalTheory.AbDual.evc]
    rw [show lift (fst A' (𝟙_ (Over (Sp K)))) (snd A' (𝟙_ (Over (Sp K))) ≫ 𝟙 _) = 𝟙 _ by simp,
      show lift (fst A (Over.mk ξ)) (snd A (Over.mk ξ) ≫ 𝟙 _) = 𝟙 _ by simp,
      Over.id_left, Over.id_left, GlobalTheory.CechPic.pull_id]
    exact (GlobalTheory.CechPic.pull_id _).trans (GlobalTheory.CechPic.cls_pull hM.isLB _ hN'.isLB)
  rw [same_iff hLam hM.isLB]
  rw [BaseChange.pull_inj_iff (BaseChange.toBase hφ hs) (BaseChange.ofBase hφ hs)
    (BaseChange.ofBase_toBase hφ hs), ← e1]
  unfold BaseChange.toBase
  rw [pull_evc]
  refine Eq.trans (GlobalTheory.AbDual.evc_eq (f := φ) (g := φ) hsq.1 hsq.2 hLam hLam' eLam
      (s := (A' ⊗ 𝟙_ (Over (Sp K))).hom) (s₀ := (A' ⊗ 𝟙_ (Over (Sp K))).hom ≫ ξ)
      (fst A' (𝟙_ (Over (Sp K)))) (snd A' (𝟙_ (Over (Sp K))) ≫ a') _ _ ?_ ?_).symm h0.symm
  · rw [Over.comp_left, GlobalTheory.AbDual.lift_left_fst]; rfl
  · simp only [Over.comp_left]
    rw [← Category.assoc, GlobalTheory.AbDual.lift_left_snd]
    simp [GlobalTheory.AbDual.pushP]

theorem surjective_twist_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → Surjective (h ≫ snd A T).left := by
  intro R _ _ A _ hA L hL hAmp T _ _ N hN H h _ hiff
  refine ⟨fun x => ?_⟩

  let Ω := AlgebraicClosure (T.left.residueField x)
  let p : Sp Ω ⟶ T.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField x) Ω)) ≫ T.left.fromSpecResidueField x
  let tpt : Over.mk (p ≫ T.hom) ⟶ T := Over.homMk p rfl
  have hMf := Fam.ev hN tpt
  obtain ⟨a, ha⟩ := exists_point_geom (Sp R) A hA L hL hAmp Ω (p ≫ T.hom) _ hMf
  have hs : Same A (abelian₂ A L) N a tpt := by
    rw [same_iff (FullSiegel.isLB_lam hL) hN.isLB]
    rw [same_iff (FullSiegel.isLB_lam hL) hMf.isLB] at ha
    rw [ha, GlobalTheory.AbDual.evc_ev hN.isLB]
    simp
  obtain ⟨z, hz⟩ := (hiff (Over.mk (p ≫ T.hom)) a tpt).mp hs
  have e : z.left ≫ (h ≫ snd A T).left = p := by
    rw [← Over.comp_left, ← Category.assoc, hz, lift_snd]
    rfl
  let q : Sp Ω := IsLocalRing.closedPoint Ω
  refine ⟨z.left.base q, ?_⟩
  have e2 : (h ≫ snd A T).left.base (z.left.base q) = p.base q :=
    (Scheme.Hom.comp_apply z.left (h ≫ snd A T).left q).symm.trans
      (congrArg (fun f : Sp Ω ⟶ T.left => f.base q) e)
  exact e2.trans ((Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _))

end GlobalTheory.TwistKerSurj
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilVacChar

variable {D : D7}

theorem hecke_mul_inv {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') :
    IsHeckeChar D (χ * χ'⁻¹) := by
  refine ⟨?_, fun x => ?_⟩
  · change Continuous fun a => χ a * (χ' a)⁻¹
    exact h.1.mul h'.1.inv
  · change χ _ * (χ' _)⁻¹ = 1
    rw [h.2 x, h'.2 x, inv_one, mul_one]

theorem resEta_mul_inv {χ χ' : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (h' : ResEta D χ' n) :
    ResEta D (χ * χ'⁻¹) 0 := by
  refine ⟨h.1, fun η hη a => ?_⟩
  change χ _ * (χ' _)⁻¹ = _
  rw [h.2 η hη a, h'.2 η hη a, mul_inv_cancel, pow_zero]

theorem mul_mul_inv_cancel (χ χ' : (AE D)ˣ →* Circle) : χ' * (χ * χ'⁻¹) = χ := by
  refine MonoidHom.ext fun a => ?_
  change χ' a * (χ a * (χ' a)⁻¹) = χ a
  rw [mul_comm (χ a), mul_inv_cancel_left]

theorem vacuum_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))) (η : (AE D)ˣ →* Circle), IsEtaTilde D η → IsWeilDatumO ψ S T χS χT om → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sS τ * compAt θ τ (Formalism.L2.Theta.mt S g) = compAt θ τ (Formalism.L2.Theta.mt S g) * sS τ) → (∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * sT τ) → ∀ x y, IsDetRoot S g x → IsDetRoot T h y → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → om (g, h) f = (((((χT * (η ^ T.rank)⁻¹) x)⁻¹ * (χS * (η ^ S.rank)⁻¹) y : Circle) : ℂ) * ∏ τ, detPlus (sS τ) (sT τ) (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt T h))) • f := by
  intro D ψ hψ S T θ hθ χS χT om η hη hom sS sT hS hT g hg h hh cS cT x y hx hy f hf hv
  obtain ⟨om₀, h₀, -, hvac⟩ := GlobalTheory.T.exists_weilDatum_powers_unramifiedEtaTilde D ψ hψ S T θ hθ _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) η hη
  obtain ⟨om', h', htw⟩ := GlobalTheory.T.exists_weilDatum_twist_heckeCharacters D ψ hψ S T _ _ (χS * (η ^ S.rank)⁻¹) (χT * (η ^ T.rank)⁻¹) om₀ h₀
    (hecke_mul_inv hom.hecS h₀.hecS) (hecke_mul_inv hom.hecT h₀.hecT)
    (resEta_mul_inv hom.resS h₀.resS) (resEta_mul_inv hom.resT h₀.resT)
  rw [mul_mul_inv_cancel, mul_mul_inv_cancel] at h'
  rw [GlobalTheory.T.weilDatum_unique_on_thetaFunctions D ψ hψ S T χS χT om om' hom h' (g, h) f hf, htw g h x y hx hy, LinearMap.smul_apply,
    hvac sS sT hS hT g hg h hh cS cT f hf hv, smul_smul]

end GlobalTheory.WeilVacChar

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.span_thetaTranslates_torsion_eq_top : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (m : ℕ), Odd m → 3 ≤ m →
    ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) →
    ∀ (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K)))), IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th →
    ∀ (U : I → ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))
      (t : I → LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))),
    (∀ i, SymLift x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (pt i) (U i) ∧ Tr x.P x.rig m th (U i) (t i)) →
    Submodule.span K (Set.range fun i =>
      (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i) : EA x.P (𝟙 (Sp K)) (m ^ 2))) = ⊤ := by
  first | exact @GlobalTheory.TSpan.span_eq_top | exact GlobalTheory.TSpan.span_eq_top | (intros; apply GlobalTheory.TSpan.span_eq_top <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaTranslateTerms_jets_bounded : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ q, N.Int q → ∀ (m : ℕ), Odd m → ∀ (p : N.QT (m ^ 2)) (s : Fam D.toPre C (m ^ 2)) (f : N.X → N.A → C), ν.FamV s f → IsEvFam N m p f → ∀ (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∃ b : ℝ, ∀ α, ‖(jc ν s gm α).fst / ν.rg ^ (m ^ 2)‖ ≤ b * Real.exp (-(q α / (m : ℝ) ^ 2)) ∧ ‖(jc ν s gm α).snd / ν.rg ^ (m ^ 2)‖ ≤ b * Real.exp (-(q α / (m : ℝ) ^ 2)) := by
  first | exact @GlobalTheory.MBLow.jc_bound | exact GlobalTheory.MBLow.jc_bound | (intros; apply GlobalTheory.MBLow.jc_bound <;> assumption)
end

section

noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem exists_isFockMapD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C →
    ∃ Φ, IsFockMapD ψ τ d A C Φ := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C hCM hψ hFr
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ α β κ ψ JA JB d hψ
  have hDf : ∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
      fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
        (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x :=
    fun u hu f x => (hD u hu f).2 x
  obtain ⟨hadd, hsm, hcom⟩ := GlobalTheory.T.archHeisenbergDerivative_additive_commutator σ JA JB d D hDf
  have hex := fun c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose uOf huOf using fun c => (hex c).exists
  have huniq : ∀ c u, At (evI F) u → (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → u = uOf c :=
    fun c u hu hw => (hex c).unique ⟨hu, hw⟩ (huOf c)
  have hAt_add : ∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → At (evI F) (u + u') :=
    fun u u' hu hu' z hz => by rw [smul_add, hu z hz, hu' z hz, add_zero]
  have hAt_smul : ∀ (r : ℝ) (u : Matrix α β (AE F E)), At (evI F) u → At (evI F) (realAd F r • u) :=
    fun r u hu z hz => by rw [smul_comm, hu z hz, smul_zero]
  let H : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ (SInf F κ) :=
    fun c => (D (uOf c)).toLinearMap
  have hHadd : ∀ c c', H (c + c') = H c + H c' := by
    intro c c'
    have e : uOf (c + c') = uOf c + uOf c' := by
      symm
      refine huniq _ _ (hAt_add _ _ (huOf c).1 (huOf c').1) fun w => ?_
      rw [Matrix.map_add _ (map_add _), (huOf c).2 w, (huOf c').2 w]
      simp [Matrix.mul_add, Matrix.add_mul]
    ext1 f
    simp only [H, e, hadd _ _ (huOf c).1 (huOf c').1]
    rfl
  have hHsmul : ∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c := by
    intro r c
    have e : uOf ((r : ℂ) • c) = realAd F r • uOf c := by
      symm
      refine huniq _ _ (hAt_smul r _ (huOf c).1) fun w => ?_
      rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (huOf c).2 w]
      simp [Matrix.mul_smul, Matrix.smul_mul]
    ext1 f
    simp only [H, e, hsm _ r (huOf c).1]
    rfl
  have hHcomm : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1 := by
    intro c c'
    ext1 f
    have h1 := hcom _ _ (huOf c).1 (huOf c').1 f
    rw [GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames σ τ JA JB a b A C hCM hFr _ _ c c' (huOf c).1 (huOf c').1 (huOf c).2 (huOf c').2] at h1
    simp only [H, LinearMap.sub_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
      Module.End.one_apply]
    rw [h1]
    congr 1
    push_cast
    ring
  obtain ⟨f₀, hf₀, hv⟩ := GlobalTheory.T.exists_gaussianVacuum_frames_placeSignatures σ τ JA JB d a b A C D hCM hFr hDf
  have hHvac : ∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0 := fun w a b =>
    hv w a b _ _ (huOf _).1 (huOf _).1 (huOf _).2 (huOf _).2
  obtain ⟨Φ, hinj, hint⟩ := GlobalTheory.T.fockMap_of_canonicalCommutation_placewise_signature H hHadd hHsmul hHcomm f₀ hf₀ hHvac
  refine ⟨Φ, hinj, fun u hu c hc T => ?_⟩
  rw [hint, huniq c u hu hc]
  exact (hD _ (huOf c).1 (Φ T)).1

end GlobalTheory.HoweD

end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.setLIntegral_flagCellFibreDensity_eq_base : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (δ : V d → ℝ) (O K : Set (V d)), IsOpen O → MeasurableSet K → K ⊆ O → ContinuousOn δ O → (∀ τ i j, ContinuousOn (fun v => G v τ i j) O) → (∀ v ∈ O, ∀ τ, (G v τ).PosDef) → ∫⁻ w in bsL ε ⁻¹' K, ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w)) = ∫⁻ v in K, ENNReal.ofReal (δ v) := by
  first | exact @GlobalTheory.FlagCell2.setLIntegral_fibDens | exact GlobalTheory.FlagCell2.setLIntegral_fibDens | (intros; apply GlobalTheory.FlagCell2.setLIntegral_fibDens <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.exists_unipotentFrameCoords_of_mem_isotropicUnipotentRadical : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ u ∈ unipRad σ J C, ∃ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c ∧ c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0 := by
  first | exact @GlobalTheory.SphEis.exists_crd_of_mem_unipRad | exact GlobalTheory.SphEis.exists_crd_of_mem_unipRad | (intros; apply GlobalTheory.SphEis.exists_crd_of_mem_unipRad <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.leviSection_commute_of_fixes_isotropicColumns : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ α, ∀ x ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), lv α * x = x * lv α := by
  first | exact @GlobalTheory.SphEis.lv_comm_of_fix_cols | exact GlobalTheory.SphEis.lv_comm_of_fix_cols | (intros; apply GlobalTheory.SphEis.lv_comm_of_fix_cols <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem mem_ratPts_of_crd_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (u : GAd σ J) (b₀ : Matrix (Fin j) (Fin m) E) (c₀ : Matrix (Fin j) (Fin j) E), Crd σ J C D Z J₀ u (adMat F b₀) (adMat F c₀) → u ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF u b₀ c₀ h
  have hmul : ∀ {a b c : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin b) (Fin c) E),
      adMat F (X * Y) = adMat F X * adMat F Y := fun X Y => by
    unfold adMat
    exact Matrix.map_mul (L := X) (M := Y) (f := (inclR (F := F) (AF F) : E →+* _))
  have hadd : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) E),
      adMat F (X + Y) = adMat F X + adMat F Y := fun X Y => by
    ext i k; simp [adMat]
  have hsub : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) E),
      adMat F (X - Y) = adMat F X - adMat F Y := fun X Y => by
    ext i k; simp [adMat]
  refine GlobalTheory.T.mem_unitaryRationalPoints_of_frameImages_rational F E σ n J j m C D Z J₀ hF u C
    (D - Z * (J₀⁻¹ * cT (σ : E →+* E) b₀) + C * c₀) (Z + C * b₀) h.onC ?_ ?_
  · rw [h.onZ, hadd, hmul]
  · rw [h.onD, hadd, hsub, hmul, hmul, hmul]
    rfl

end GlobalTheory.SphEis
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.unipotentRadical_coordinates_groupLaw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ (u u' : GAd σ J) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (b' : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c' : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c → (Crd σ J C D Z J₀ u' b' c' → Crd σ J C D Z J₀ (u * u') (b + b') (c + c' - b * plus σ J₀ b')) ∧ (Crd σ J C D Z J₀ u' b c → u = u') ∧ ∀ α, Crd σ J C D Z J₀ (lv α * u * (lv α)⁻¹) (α.1 * b) (α.1 * c * cT (sigR (AF F) σ) α.1) := by
  first | exact @GlobalTheory.SphEis.crd_law | exact GlobalTheory.SphEis.crd_law | (intros; apply GlobalTheory.SphEis.crd_law <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2

theorem pt_bsL_fb {n d : ℕ} {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (w : V n) : pt ε (bsL ε w) (fb ε w) = w := by
  ext a
  obtain ⟨x, rfl⟩ := ε.symm.surjective a
  rcases x with b | j <;> simp [pt, bsL_apply, fb]

theorem cellMap_image_eq : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m), IsOpen (cellSet E E' φ f hf c A u) ∧ Set.InjOn (cellMap ε f hf c u) (cellSet E E' φ f hf c A u) ∧ ∀ T : Set (CxPts X.str σ), T ⊆ c.e.source → (∀ x ∈ T, A ∈ E.S (under x)) → cellMap ε f hf c u '' (ptMap σ f hf ⁻¹' T ∩ cellSet E E' φ f hf c A u) = bsL ε ⁻¹' (c.e '' T) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u hgen n ε
  have hO := GlobalTheory.T.isOpen_flagBundleCell_and_coords_regular F X Y ι m E E' φ f hR A u
  have hP := GlobalTheory.T.flag_cell_points_existsUnique_unitriangular F X Y ι m E E' φ f hR A u hgen
  have hval : ∀ y : CxPts Y.str σ, InCell E E' φ f A u (under y) → ∀ j,
      ratVal (u j) y = (ratOf Y).val y.1 (u j) :=
    fun y hy j => ratVal_eq_val_ratOf y (mem_O_ratOf.2 (hO.2 _ hy j))
  refine ⟨?_, ?_, ?_⟩
  · let W : Y.X.Opens := ⟨{y | InCell E E' φ f A u y}, hO.1⟩
    have e : cellSet E E' φ f hf c A u = ptsIn Y.str σ W ∩ ptMap σ f hf ⁻¹' c.e.source := by
      ext y
      simp only [cellSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, mem_ptsIn]
      rfl
    rw [e]
    exact (isOpen_ptsIn W).inter (c.e.open_source.preimage (Points.PtsOver.continuous_map f hf _))
  · intro y hy y' hy' h
    have h1 := congrArg (bsL ε) h
    have h2 := congrArg (fb ε) h
    simp only [cellMap, bsL_pt, fb_pt] at h1 h2
    have hx : ptMap σ f hf y = ptMap σ f hf y' := c.e.injOn hy.2 hy'.2 h1
    have hA : A ∈ E.S ((ptMap σ f hf y).1 (IsLocalRing.closedPoint ℂ)) := hy.1.1
    apply Subtype.ext
    exact (hP ℂ (ptMap σ f hf y).1 hA (fun j => ratVal (u j) y)).unique
      ⟨rfl, hy.1, fun j => (hval y hy.1 j).symm⟩
      ⟨congrArg Subtype.val hx.symm, hy'.1, fun j => (hval y' hy'.1 j).symm.trans (congrFun h2 j).symm⟩
  · intro S hS hA
    ext w
    constructor
    · rintro ⟨y, ⟨hyS, -⟩, rfl⟩
      exact ⟨ptMap σ f hf y, hyS, by simp only [cellMap, bsL_pt]⟩
    · rintro ⟨x, hxS, hxw⟩
      obtain ⟨p, ⟨hpf, hpc, hpv⟩, -⟩ := hP ℂ x.1 (hA x hxS) (fb ε w)
      have hps : p ≫ Y.str = spMap σ := by rw [← hf, ← Category.assoc, hpf, x.2]
      let y : CxPts Y.str σ := ⟨p, hps⟩
      have hyx : ptMap σ f hf y = x := Subtype.ext hpf
      refine ⟨y, ⟨by rw [Set.mem_preimage, hyx]; exact hxS, hpc, by rw [hyx]; exact hS hxS⟩, ?_⟩
      have hv : (fun j => ratVal (u j) y) = fb ε w := funext fun j => (hval y hpc j).trans (hpv j)
      simp only [cellMap, hyx, hxw, hv]
      exact pt_bsL_fb ε w

end GlobalTheory.FlagCell2
end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj


theorem _root_.GlobalTheory.T.exists_unit_smul_of_central_parabolicLevi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∀ g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, (∀ k ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, g * k = k * g) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J g).1 * adMat F X = (l : AF F ⊗[F] E) • adMat F X := by
  first | exact @GlobalTheory.CentralLevi.exists_unit_smul_of_central | exact GlobalTheory.CentralLevi.exists_unit_smul_of_central | (intros; apply GlobalTheory.CentralLevi.exists_unit_smul_of_central <;> assumption)
end
