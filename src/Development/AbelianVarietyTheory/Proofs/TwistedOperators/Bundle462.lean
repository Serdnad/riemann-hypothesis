module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle429
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle410
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle042
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefIntegralEq
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle428
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfSymplZeroRight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupHalfCharactersSeparate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.RingTheory.DualNumber
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.signedUnitaryGroup_compat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (V : HSp D), SgnLaw θ ε V := by
  first | exact @GlobalTheory.SgnIdent.sgnLaw_holds | exact GlobalTheory.SgnIdent.sgnLaw_holds | (intros; apply GlobalTheory.SgnIdent.sgnLaw_holds <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.hermitianAdjoint_laws_standardCharacter : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, AdjLaw ψ S T := by
  first | exact @GlobalTheory.AdjLawPf.adjLaw | exact GlobalTheory.AdjLawPf.adjLaw | (intros; apply GlobalTheory.AdjLawPf.adjLaw <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.gaussian_conjMonomial_moment_eq_taylor_coefficient : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ G : VCx ι a b → ℂ, Differentiable ℂ G → (∃ M : ℝ, ∀ z, ‖G z‖ ≤ M * Real.exp (gq c z / 2)) → ∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z) : ℂ) * G z = ((∏ τ, (Real.pi / c τ) ^ (a * b) : ℝ) : ℂ) * ((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ) : ℂ) * derivAt0 G m := by
  first | exact @GlobalTheory.FockMoment.gaussMoment | exact GlobalTheory.FockMoment.gaussMoment | (intros; apply GlobalTheory.FockMoment.gaussMoment <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch


theorem _root_.GlobalTheory.T.zetaIdentity_transport_localFieldIso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (k' : Type) [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [MeasurableSpace k'] [BorelSpace k'] (j : k ≃+* k'), IsLocIso j → ∀ (a : ℕ) (A' : Type) [Fintype A'] [DecidableEq A'] (C : Type) [Fintype C] [DecidableEq C] (σ : Fin a ⊕ A' ≃ C)
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (μ' : Measure (GL A' k')) [μ'.IsHaarMeasure] (ϖ : kˣ) (ϖ' : k'ˣ), IsUnif ϖ → IsUnif ϖ' →
    ∀ (ν β : kˣ →* ℂˣ) (ν' β' : k'ˣ →* ℂˣ), (∀ x, ν x = ν' (Units.map (j : k →* k') x)) →
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (Ξ : Matrix (Fin a) C k' → ℂ) (Ψ : Matrix A' C k' → ℂ),
      bigP (haarVol (KO k' (Fin a))) ϖ' σ ν' β' Ξ = smallP μ' σ ν' (ν' * β') Ψ →
      bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun X => Ξ (X.map j)) = smallP μ σ ν (ν * β) fun Y => lam * Ψ (Y.map j) := by
  first | exact @GlobalTheory.FlipMatch.FieldTransport.zeta_identity_transport | exact GlobalTheory.FlipMatch.FieldTransport.zeta_identity_transport | (intros; apply GlobalTheory.FlipMatch.FieldTransport.zeta_identity_transport <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

noncomputable section

namespace GlobalTheory.RigIsoDescent

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A}

theorem exists_isRigIso_of_gen {Y : Scheme.{0}} {x x' : Y ⟶ S} {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left}
    {k : ℤ} (hΨ : IsPointed A Ψ) (t : LB.Gen (isoLB A L Ψ k)) (ht : t.IsGen) : ∃ β, IsRigIso A L Ψ k β := by
  obtain ⟨β, hβ, hc⟩ := DVR.exists_normalized_to L.isLB _ _ t ht (fst (Over.mk x) A).left
    (ptSecT A (1 : Over.mk x ⟶ A)).left ThetaReal.NormMul.ptSec_fst _ _
    (LB.mulGen L.L (Y := Y) _ _ _ _ (rigT A L.L L.rig (Over.mk x) k) (rigT A L.L L.rig (Over.mk x') (-1)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (ThetaReal.NormMul.rigT_isGen L.rigGen _) (ThetaReal.NormMul.rigT_isGen L.rigGen _))
    (by
      rw [DVR.fsum_sumElim, DVR.fsum, DVR.fsum, DVR.fsum, Fin.sum_univ_two, Fin.sum_univ_one, Fin.sum_univ_one]
      refine congrArg₂ (· + ·) (congrArg (Finsupp.single · k) ThetaReal.NormMul.ptSec_snd)
        (congrArg (Finsupp.single · (-1 : ℤ)) ?_)
      refine (Category.assoc _ _ _).symm.trans ?_
      rw [hΨ.2]
      exact ThetaReal.NormMul.ptSec_snd)
  exact ⟨β, hΨ, hβ, hc⟩

theorem exists_gen_of_field (hA : IsAbelianScheme A) {K K' : Type} [Field K] [Field K'] (φ : K →+* K')
    {x x' : Sp K ⟶ S} {w w' : Sp K' ⟶ S} {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left}
    {Ψ' : (Over.mk w ⊗ A).left ⟶ (Over.mk w' ⊗ A).left} {k : ℤ} (hw : w = spMap φ ≫ x)
    (π : (Over.mk w ⊗ A).left ⟶ (Over.mk x ⊗ A).left)
    (h₁ : π ≫ (fst (Over.mk x) A).left = (fst (Over.mk w) A).left ≫ spMap φ)
    (h₂ : π ≫ (snd (Over.mk x) A).left = (snd (Over.mk w) A).left)
    (h₃ : π ≫ Ψ ≫ (snd (Over.mk x') A).left = Ψ' ≫ (snd (Over.mk w') A).left)
    (t : LB.Gen (isoLB A L Ψ' k)) (ht : t.IsGen) : ∃ u : LB.Gen (isoLB A L Ψ k), u.IsGen := by
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  let p : (Over.mk x ⊗ A).left ⟶ Sp K := (fst (Over.mk x) A).left
  have H₀ : IsPullback (snd (Over.mk x) A).left p A.hom x := (IsPullback.of_hasPullback x A.hom).flip
  have H₁ : IsPullback (snd (Over.mk w) A).left (fst (Over.mk w) A).left A.hom w :=
    (IsPullback.of_hasPullback w A.hom).flip
  have : IsProper p := MorphismProperty.of_isPullback (P := @IsProper) H₀ inferInstance
  have : GeometricallyIntegral p := MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H₀ inferInstance
  have H : IsPullback π (fst (Over.mk w) A).left p (spMap φ) :=
    IsPullback.of_right (by rw [h₂, ← hw]; exact H₁) h₁ H₀
  obtain ⟨c, hc⟩ := gen_chartPull (chartPullOut L.L (isoφ A Ψ) ![k, -1] π (isoφ A Ψ') fun i => by
    fin_cases i
    exacts [h₂.symm, h₃.symm]) t ht
  exact FieldTriv.exists_gen_of_isPullback φ p π _ H (LB.isLB_linComb L.isLB _ _) c hc

end General

theorem eSec_fst {B B' : Scheme.{0}} (u : B' ⟶ B) (A : Over B) [GrpObj A] :
    eSec ((Over.pullback u).obj A) ≫ pullback.fst A.hom u = u ≫ eSec A := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem ptSec_swap {K : Type} [CommRing K] (x : Sp K ⟶ Xo.X) :
    (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ (swap x).hom = eSec (Fib Xo x) := by
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (swap_hom_fst x)).trans
      (ThetaReal.NormMul.ptSec_snd.trans (eSec_fst x _).symm))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (swap_hom_snd x)).trans
      (ThetaReal.NormMul.ptSec_fst.trans (Over.w η[Fib Xo x]).symm))

theorem isPointed_of_isMonHom {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x')
    (hf : IsMonHom f) : IsPointed Xo.univ.t.G (conj x x' f.left) := by
  refine ⟨(over_iff _).2 (Over.w f), ?_⟩
  have e : eSec (Fib Xo x) ≫ f.left = eSec (Fib Xo x') := congrArg (fun q => q.left) hf.one_hom
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (ptSec_swap x)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans ?_)))
  exact (Iso.comp_inv_eq _).2 (ptSec_swap x').symm

theorem exists_isRigIso_of_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') (k : ℤ), IsBC φ f g → IsMonHom f → (∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj w w' g.left) k β) → ∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) k β := by
  rintro E _ _ _ H Dw l Xo K L _ _ φ x x' w w' f g k ⟨hw, hw', hbc⟩ hf ⟨β, -, hβ, -⟩
  have mk : ∀ {y : Sp K ⟶ Xo.X} {v : Sp L ⟶ Xo.X}, v = spMap φ ≫ y →
      ∃ π : pullback Xo.univ.t.G.hom v ⟶ pullback Xo.univ.t.G.hom y,
        π ≫ pullback.fst _ _ = pullback.fst _ _ ∧ π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ := fun h =>
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap φ) (by rw [Category.assoc, ← h, pullback.condition]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨π, a₁, a₂⟩ := mk hw
  obtain ⟨π', b₁, b₂⟩ := mk hw'
  have e := hbc π π' a₁ a₂ b₁ b₂
  have hp := isPointed_of_isMonHom f hf
  obtain ⟨u, hu⟩ := exists_gen_of_field (L := Xo.univ.t.PP) (Ψ := conj x x' f.left) (UnivPol.pol Xo).isAb φ hw
    ((swap w).hom ≫ π ≫ (swap x).inv)
    (by rw [Category.assoc, Category.assoc, swap_inv_fst, a₂, swap_hom_snd_assoc])
    (by rw [Category.assoc, Category.assoc, swap_inv_snd, a₁, swap_hom_fst])
    (by
      simp only [conj_apply, Category.assoc, Iso.inv_hom_id_assoc, swap_inv_snd]
      rw [← reassoc_of% e, b₁]) β hβ
  exact exists_isRigIso_of_gen hp u hu

end GlobalTheory.RigIsoDescent
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.LieImageBC

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem epi_of_local {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (d : A →+* B)
    [IsLocalHom d] (hd : Function.Injective d) : Epi (spMap d) := by
  refine ⟨fun {X} a b h => ?_⟩
  obtain ⟨⟨x, f, hf⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm.surjective a
  obtain ⟨⟨y, g, hg⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm.surjective b
  have h1 : IsLocalHom (f ≫ CommRingCat.ofHom d).hom := by
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp d f.hom
  have h2 : IsLocalHom (g ≫ CommRingCat.ofHom d).hom := by
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp d g.hom
  have h3 : (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨x, _, h1⟩ =
      (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨y, _, h2⟩ := by
    simpa [SpecToEquivOfLocalRing] using h
  have h4 := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.injective h3
  obtain rfl : x = y := congrArg Sigma.fst h4
  have h5 : f ≫ CommRingCat.ofHom d = g ≫ CommRingCat.ofHom d :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj h4).2)
  obtain rfl : f = g := by
    ext s
    exact hd (congrArg (fun k => k.hom s) h5)
  rfl

theorem epi_dualMap {K L : Type} [Field K] [Field L] (φ : K →+* L) : Epi (spMap (dualMap φ)) := by
  have : IsLocalHom (dualMap φ) := ⟨fun a ha => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero] at ha ⊢
    intro h
    exact ha (by simp [dualMap, h])⟩
  refine epi_of_local _ fun a b h => ?_
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  ext
  · exact φ.injective (by simpa [dualMap] using h1)
  · exact φ.injective (by simpa [dualMap] using h2)

theorem dual_eps {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    spMap (dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (dualMap ψ) := by
  rw [sp_comp, sp_comp]
  congr 1
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap ψ := by
  rw [sp_comp, sp_comp]
  congr 1
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem isLieImageH_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') (p : ℕ) (v u : Sp (DualNumber K) ⟶ Xo.univ.t.G.left), IsBC φ f g → IsTanAt x v → (IsLieImageH p f.left v u ↔ IsLieImageH p g.left (spMap (dualMap φ) ≫ v) (spMap (dualMap φ) ≫ u)) := by
  intro E _ _ _ H Dw l Xo K L _ _ φ x x' w w' f g p v u hbc hv
  obtain ⟨rfl, rfl, hbc⟩ := hbc
  let π : pullback Xo.univ.t.G.hom (spMap φ ≫ x) ⟶ pullback Xo.univ.t.G.hom x :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap φ) (by rw [pullback.condition, Category.assoc])
  let π' : pullback Xo.univ.t.G.hom (spMap φ ≫ x') ⟶ pullback Xo.univ.t.G.hom x' :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap φ) (by rw [pullback.condition, Category.assoc])
  have hπ1 : π ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hπ2 : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ := pullback.lift_snd _ _ _
  have hπ1' : π' ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hπ2' : π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ := pullback.lift_snd _ _ _
  have hc := hbc π π' hπ1 hπ2 hπ1' hπ2'
  generalize hF : (f.left : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x') = F at hc ⊢
  generalize hG : (g.left : pullback Xo.univ.t.G.hom (spMap φ ≫ x) ⟶ pullback Xo.univ.t.G.hom (spMap φ ≫ x')) = G
    at hc ⊢
  have key : ∀ (a : Sp (DualNumber K) ⟶ pullback Xo.univ.t.G.hom x)
      (b : Sp (DualNumber L) ⟶ pullback Xo.univ.t.G.hom (spMap φ ≫ x)),
      a ≫ pullback.fst _ _ = v → a ≫ pullback.snd _ _ = spMap (algebraMap K (DualNumber K)) →
      b ≫ pullback.fst _ _ = spMap (dualMap φ) ≫ v → b ≫ pullback.snd _ _ = spMap (algebraMap L (DualNumber L)) →
      spMap (dualMap φ) ≫ spMap (epsMul ((p : K)⁻¹)) ≫ a ≫ F ≫ pullback.fst _ _ =
        spMap (epsMul ((p : L)⁻¹)) ≫ b ≫ G ≫ pullback.fst _ _ := by
    intro a b ha1 ha2 hb1 hb2
    have hab : b ≫ π = spMap (dualMap φ) ≫ a := by
      apply pullback.hom_ext
      · rw [Category.assoc, hπ1, hb1, Category.assoc, ha1]
      · rw [Category.assoc, hπ2, ← Category.assoc, hb2, Category.assoc, ha2, dual_alg]
    have hGF : G ≫ pullback.fst _ _ = π ≫ F ≫ pullback.fst _ _ := by
      rw [← hπ1', ← Category.assoc, hc, Category.assoc]
    rw [hGF, ← Category.assoc b, hab, ← Category.assoc, dual_eps, map_inv₀, map_natCast]
    simp only [Category.assoc]
  constructor
  · rintro ⟨a, ha1, ha2, rfl⟩
    refine ⟨pullback.lift (spMap (dualMap φ) ≫ v) (spMap (algebraMap L (DualNumber L))) ?_,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
      key a _ ha1 ha2 (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)⟩
    rw [Category.assoc, hv.1, ← Category.assoc, dual_alg, Category.assoc]
  · rintro ⟨b, hb1, hb2, hu⟩
    refine ⟨pullback.lift v (spMap (algebraMap K (DualNumber K))) hv.1,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
    have := epi_dualMap φ
    rw [← cancel_epi (spMap (dualMap φ)), hu]
    exact (key _ b (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hb1 hb2).symm

end GlobalTheory.LieImageBC
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {K : Type} [CommRing K]

theorem conj_pullback_map (x : Sp K ⟶ Xo.X) (g : Xo.univ.t.G ⟶ Xo.univ.t.G) :
    conj x x ((Over.pullback x).map g).left =
      (lift (fst (Over.mk x) Xo.univ.t.G) (snd (Over.mk x) Xo.univ.t.G ≫ g)).left := by
  refine gx_ext ?_ ?_
  · rw [lift_l_fst]
    exact (over_iff _).2 (pullback.lift_snd _ _ _)
  · rw [lift_l_snd, conj_apply, Category.assoc, Category.assoc, swap_inv_snd, Over.comp_left, ← swap_hom_fst,
      Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)

theorem conj_comp_left {x x' x'' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo x' ⟶ Fib Xo x'') :
    conj x x'' (f ≫ g).left = conj x x' f.left ≫ conj x' x'' g.left := by
  simp only [conj_apply, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Over.comp_left]
  simp only [Category.assoc]

theorem conj_id_pow (x : Sp K ⟶ Xo.X) (n : ℕ) :
    conj x x (𝟙 (Fib Xo x) ^ n).left = (mulT Xo.univ.t.G (Over.mk x) n).left := by
  have e : (Over.pullback x).map (𝟙 Xo.univ.t.G ^ n) = 𝟙 (Fib Xo x) ^ n := by
    have := map_pow (Over.pullback x).homMonoidHom (𝟙 Xo.univ.t.G) n
    rw [← (Over.pullback x).map_id]
    exact this
  rw [← e, conj_pullback_map, MonObj.comp_pow, Category.comp_id, mulT]

theorem conj_id_inv (x : Sp K ⟶ Xo.X) :
    conj x x (𝟙 (Fib Xo x))⁻¹.left = (negT Xo.univ.t.G (Over.mk x)).left := by
  have e : (Over.pullback x).map (𝟙 Xo.univ.t.G)⁻¹ = (𝟙 (Fib Xo x))⁻¹ := by
    rw [Functor.map_inv', CategoryTheory.Functor.map_id]
  rw [← e, conj_pullback_map, GrpObj.comp_inv, Category.comp_id, negT]
  rfl

theorem negT_comm_conj {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') [IsMonHom f] :
    (negT Xo.univ.t.G (Over.mk x)).left ≫ conj x x' f.left =
      conj x x' f.left ≫ (negT Xo.univ.t.G (Over.mk x')).left := by
  rw [← conj_id_inv, ← conj_id_inv, ← conj_comp_left, ← conj_comp_left, GrpObj.inv_comp, GrpObj.comp_inv,
    Category.id_comp, Category.comp_id]

theorem pow_eq_one_of_mem_transKer_conj {x x' : Sp K ⟶ Xo.X} {f : Fib Xo x ⟶ Fib Xo x'} {f' : Fib Xo x' ⟶ Fib Xo x}
    {n : ℕ} (h : f ≫ f' = 𝟙 _ ^ n) {c : Over.mk x ⟶ Xo.univ.t.G} (hc : c ∈ transKer Xo.univ.t.G (conj x x' f.left)) :
    c ^ n = 1 := by
  rw [← mem_transKer_mulT, mem_transKer, ← conj_id_pow, ← h, conj_comp_left, ← Category.assoc, mem_transKer.1 hc]

theorem thetaTrace_isTranslSum (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x x' : Sp K ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x')
    (f' : Fib Xo x' ⟶ Fib Xo x) (p : ℕ) (s : LB.Sec (PPx x)) (s₀ s' : LB.Sec (PPx x')) (a : K)
    (hf : IsPair (p ^ 2) f f') (hs' : ∀ i, s'.f i = scal x' a i * s₀.f i)
    (h : IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) p s s') :
    ∃ t, IsPullOf p f a s₀ t ∧ IsTranslSum p s t := by
  obtain ⟨β, s₁, t, n, U, F, hβ, hs, ht, hr, hU, hF, hsum⟩ := h
  have := hf.1
  refine ⟨t, ⟨β, s', hβ, hs', ht⟩, n, F, fun i => ?_, hsum⟩
  have hk : (U i).pt ^ (p ^ 2) = 1 := pow_eq_one_of_mem_transKer_conj hf.2.2.1 (hU i).1
  obtain ⟨α₀, α, h₁, h₂, h₃, h₄⟩ := hs
  exact ⟨_, (U i).pt, α₀, α, s₁, U i, rfl, hk, h₁, h₂, h₃, h₄,
    (hU i).symLift hβ.2.1 Xo.univ.t.sym (negT_comm_conj f) hk, hF i⟩

end GlobalTheory.HkIntegral
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem isProper_of_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (F : G.G ⟶ G'.G) (N : ℕ), Ext m₁ m₂ n₁ n₂ f F → f' ≫ f = 𝟙 _ ^ N → 0 < N → IsProper G.G.hom → IsProper G'.G.hom := by
  intro E _ _ _ H Dw l Xo T x x' G G' t t' m₁ m₂ n₁ n₂ f f' F N ⟨ψ, _, hψ, hc⟩ hN hpos hG
  have hU : IsAbelianScheme Xo.univ.t.G :=
    ⟨Xo.univ.t.semi.comm, Xo.univ.t.semi.smooth, Xo.univ.proper, Xo.univ.t.semi.geomConnected⟩
  have hA : IsAbelianScheme (Fib Xo x') := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback x' _ hU
  have hB : IsAbelianScheme G.G := ⟨G.semi.comm, G.semi.smooth, hG, G.semi.geomConnected⟩
  have hch : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
  have hu : IsUnit (N : Γ(Sp T.Fr, ⊤)) := by
    have h0 : IsUnit (N : T.Fr) := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hpos.ne')
    have := h0.map (Scheme.ΓSpecIso (CommRingCat.of T.Fr)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨-, -, -, hs⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective _ (Fib Xo x') N hA hu
  have hl : f'.left ≫ f.left = (𝟙 (Fib Xo x') ^ N).left := congrArg (·.left) hN
  have hf : Function.Surjective f.left := by
    intro y
    obtain ⟨z, hz⟩ := hs.1 y
    refine ⟨f'.left z, ?_⟩
    rw [← Scheme.Hom.comp_apply, hl, hz]
  have p₁ : IsPullback m₁.φ t.G.hom Xo.univ.t.G.hom x := m₁.cart.1
  have q₁ : IsPullback n₁.φ t'.G.hom Xo.univ.t.G.hom x' := n₁.cart.1
  have q₂ : IsPullback n₂.φ t'.G.hom G'.G.hom (spMap (algebraMap T.V T.Fr)) := n₂.cart.1
  have hsq := hc p₁.isoPullback.hom q₁.isoPullback.hom (by simp) (by simp) (by simp) (by simp)
  have hψs : Function.Surjective ψ.left := by
    intro y
    obtain ⟨z, hz⟩ := hf (q₁.isoPullback.hom y)
    obtain ⟨w, rfl⟩ := (inferInstance : Surjective p₁.isoPullback.hom).1 z
    refine ⟨w, q₁.isoPullback.hom.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
    exact hz
  refine (GlobalTheory.isAbelianScheme_of_generically_surjective T.V T.Fr G.G G'.G hB G'.semi F ?_).proper
  rintro y ⟨s, hs⟩
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback q₂ y s hs.symm
  obtain ⟨w, rfl⟩ := hψs z
  refine ⟨m₂.φ w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hψ, Scheme.Hom.comp_apply, hz]

end GlobalTheory.HkIntegral
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integrable_thetaMatrixCoeff_isotropic_rational : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Integrable (fun y => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) μ := by
  first | exact @GlobalTheory.IsoMean.integrable_coef | exact GlobalTheory.IsoMean.integrable_coef | (intros; apply GlobalTheory.IsoMean.integrable_coef <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_open_subgroup_half_characters_separate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (e : AE D), IsSplitIdem D e → ∀ U : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (U : Set (halfMx (cA D e) W.rank r)) → ∃ L : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (L : Set (halfMx (cA D e) W.rank r)) ∧ L ≤ U ∧ ∀ x, x ∉ L → ∃ a : halfMx e W.rank r, (∀ l ∈ L, ψ (halfSympl W (a : Mx D W.rank r) (l : Mx D W.rank r)) = 1) ∧ ψ (halfSympl W (a : Mx D W.rank r) (x : Mx D W.rank r)) ≠ 1 := by
  first | exact @GlobalTheory.HalfSeparate.exists_open_separated | exact GlobalTheory.HalfSeparate.exists_open_separated | (intros; apply GlobalTheory.HalfSeparate.exists_open_separated <;> assumption)
end
