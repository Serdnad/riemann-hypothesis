module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle262
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle286
public import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle027
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle125
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsomPhi

open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (gam centMeas orbCls torEmb)

theorem tor_mul_comm {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k] (a b : Tor P k) : a * b = b * a := by
  apply Subtype.ext
  show a.1 * b.1 = b.1 * a.1
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem map_isHaar_rightInv {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k] [TopologicalSpace k] {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [MeasurableSpace (Tor P k)] [BorelSpace (Tor P k)]
    [IsTopologicalGroup (Tor P k)] (e : Tor P k ≃ₜ* H) (dt : Measure (Tor P k)) [dt.IsHaarMeasure] :
    (dt.map e).IsHaarMeasure ∧ (dt.map e).IsMulRightInvariant := by
  haveI h1 : (dt.map e).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map dt e.toMulEquiv e.continuous e.symm.continuous
  refine ⟨h1, ⟨fun g => ?_⟩⟩
  have hc : (fun x : H => x * g) = fun x => g * x := funext fun x => by
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, tor_mul_comm]
  rw [hc]
  exact map_mul_left_eq_self _ g



open GlobalTheory.Orb in
theorem phi_map : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (P : PPol D.sp.cm.sig r) (v : HeightOneSpectrum (𝓞 D.host.F)) (j : GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), IsLatticeConj (frameLat V) (frameLat V') j → ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v)) (dt : Measure (Tor P (Fv D.host.F v))) (f : GLoc D.sp.cm.sig V.gram v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → PhiOK (J := V.gram) μ dt f → PhiOK (J := V'.gram) (μ.map j) dt (f ∘ j.symm) → Phi (J := V'.gram) (μ.map j) dt (f ∘ j.symm) = Phi (J := V.gram) μ dt f := by
  intro D V V' r P v j hj μ dt f hμ hdt hok hok'
  have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  obtain ⟨hX, hmv⟩ := GlobalTheory.T.unitaryTorusEllipticElements_of_localLatticeIsometry _ _ D.sp.cm.sig hcm r V.rank V'.rank P V.gram V'.gram (frameLat V) (frameLat V')
    v j hj
  unfold Phi
  rw [← finsum_comp_equiv (Equiv.subtypeEquivRight (fun c => by rw [hX]))]
  refine finsum_congr fun q => ?_
  obtain ⟨c, h2⟩ := q
  obtain ⟨x, φ, hc, h⟩ := id h2
  subst hc
  obtain ⟨φ'', h'', hγ, ht⟩ := hmv x φ h
  obtain ⟨e, he, hme⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure _ _ D.sp.cm.sig hcm r V.rank P V.gram (isHermND_gram V) (Fv D.host.F v) x φ h
  obtain ⟨e'', he'', hme''⟩ :=
    GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure _ _ D.sp.cm.sig hcm r V'.rank P V'.gram (isHermND_gram V') (Fv D.host.F v) x φ'' h''
  haveI := hμ
  haveI := hdt
  obtain ⟨i1, i2⟩ := map_isHaar_rightInv P (Fv D.host.F v) e dt
  haveI : (centMeas h dt).IsHaarMeasure := by rw [hme dt]; exact i1
  haveI : (centMeas h dt).IsMulRightInvariant := by rw [hme dt]; exact i2
  have v1 := (hok.2 x φ h).orbInt_eq
  have v2 := (hok'.2 x φ'' h'').orbInt_eq
  have hm : centMeas h'' dt = (centMeas h dt).map (centEquiv j (gam h) hγ.symm) := by
    rw [hme'', hme dt, Measure.map_map (map_continuous (centEquiv j (gam h) hγ.symm)).measurable (map_continuous e).measurable]
    congr 1
    funext t
    apply Subtype.ext
    rw [he'', ht, ← he]
    rfl
  calc orbCls (J := V'.gram) (μ.map j) dt (f ∘ j.symm) ((Equiv.subtypeEquivRight (fun c => by rw [hX])) ⟨QuotientGroup.mk x, h2⟩)
      = orbInt (μ.map j) (gam h'') (centMeas h'' dt) (f ∘ j.symm) := v2.symm
    _ = orbInt (μ.map j) (gam h'') ((centMeas h dt).map (centEquiv j (gam h) hγ.symm)) (f ∘ j.symm) := by rw [hm]
    _ = orbInt μ (gam h) (centMeas h dt) ((f ∘ j.symm) ∘ j) := (hasOrbInt_map j hγ.symm (f ∘ j.symm) 0).2
    _ = orbInt μ (gam h) (centMeas h dt) f := by
      congr 1
      ext g
      simp
    _ = orbCls (J := V.gram) μ dt f ⟨QuotientGroup.mk x, h2⟩ := v1

end GlobalTheory.IsomPhi
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.MumfordLocalComplex
open GlobalTheory.CechPic GlobalTheory.StabFlat GlobalTheory.PrimitiveOverValuationRing

theorem exists_ideal_complex_cech (hG : GlobalFnsSt) {V : Type} [CommRing V] (B : Over (Spec (CommRingCat.of V)))
    [GrpObj B] [IsCommMonObj B] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {g : ℕ}
    (hg : SmoothOfRelativeDimension g B.hom)
    {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen)
    (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen) {H : Over (Spec (CommRingCat.of V))} (j : H ⟶ B)
    (hH : ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ B), (∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) ↔
        ∃ y : T ⟶ H, y ≫ j = x)
    (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (a : Spec (CommRingCat.of A) ⟶ B.left)
    (K₀ : Type) [Field K₀] (g₀ : A →+* K₀) (hg₀ : IsLocalHom g₀)
    (h₀ : ∃ y : Spec (CommRingCat.of K₀) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom g₀) ≫ a) :
    ∃ (I : Ideal A) (C : CochainComplex (ModuleCat.{0} A) ℕ), (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) ∧
      (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧
      Nonempty ((Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] A ⧸ I) ∧
      (∀ p : Ideal A, p.IsPrime → ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p ∧
        ∀ i, (¬ I ≤ p ∨ g < i) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) ∧
      (∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R),
        (∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) ↔
          I ≤ RingHom.ker φ) ∧
      ∀ (K : Type) [Field K] (φ : A →+* K),
        (∃ y : Spec (CommRingCat.of K) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) →
        ∀ (X' : Scheme.{0}) (π' : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)),
        IsPullback π' f' B.hom (Spec.map (CommRingCat.ofHom φ) ≫ a ≫ B.hom) →
        ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X'.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ →
        ∀ i, Nonempty ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology i ≃ₗ[K]
          (cechLB f' (LB.triv X') D).homology i) := by
  let t := a ≫ B.hom
  obtain ⟨F, hF, hΛ, hcl⟩ := exists_family hL hO hΘ hu t (Over.homMk a rfl)
  let B' := (Over.pullback t).obj B
  have hB' : IsAbelianScheme B' := TLinPf.isAb_pullback t B hB
  have hpb : IsPullback (pullback.fst B.hom t) B'.hom B.hom t := IsPullback.of_hasPullback _ _
  have hp' : IsProjBy B'.hom := isProjBy_baseChange hp hpb
  have hg' : SmoothOfRelativeDimension g B'.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hpb hg
  have test : ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R) (X' : Scheme.{0}) (π : X' ⟶ B'.left)
      (f' : X' ⟶ Spec (CommRingCat.of R)), IsPullback π f' B'.hom (Spec.map (CommRingCat.ofHom φ)) →
      (Triv (F.pull π) ↔
        ∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) := by
    intro R _ _ φ X' π f' h
    let T : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ t)
    let x : T ⟶ B := Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ a) (Category.assoc _ _ _)
    have hM : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB :=
      LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
    have q : IsPullback f' (π ≫ pullback.fst B.hom t) T.hom B.hom := (h.paste_horiz hpb).flip
    let W : Over (Spec (CommRingCat.of V)) := Over.mk (f' ≫ T.hom)
    let e : W ⟶ T ⊗ B := Over.homMk q.isoPullback.hom (by
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ T.hom = f' ≫ T.hom
      rw [IsPullback.isoPullback_hom_fst_assoc])
    have : IsIso e.left := inferInstanceAs (IsIso q.isoPullback.hom)
    have c₁ : CechPic.pull π (cls F hF) = CechPic.pull e.left (cls _ hM) := by
      rw [cls_eq_dcl hL hO, pull_dcl]
      refine hcl W π _ _ ?_ q.isoPullback_hom_snd
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ a =
        π ≫ B'.hom ≫ a
      rw [IsPullback.isoPullback_hom_fst_assoc, h.w_assoc]
    refine (cls_eq_zero_iff (pull_isLB hF π)).symm.trans ?_
    rw [cls_pull hF, c₁, pull_iso_eq_zero]
    refine ((loc_triv_iff (R := R) (fst T B).left hM).symm.trans (hH T x)).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact ⟨y.left, congrArg (·.left) hy⟩
    · rintro ⟨y, hy⟩
      refine ⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩
      rw [← Over.w j, ← Category.assoc, hy]
      exact Category.assoc _ _ _
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj A _ B'.hom hB'.smooth hp' F hF
  have := hB'.proper
  have := hB'.geomConnected
  have q₀ := IsPullback.of_hasPullback B'.hom (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨I, ⟨eI⟩, hI⟩ := GlobalTheory.UU.SecCyclic.cyclic_ideal A _ B'.hom F hF P inferInstance inferInstance K₀ g₀ hg₀ _ _ _
    q₀ (CubeOpen.bijective_appTop hG B' hB' q₀) ((test K₀ g₀ _ _ _ q₀).2 h₀)
  obtain ⟨C, c₁, c₂, ⟨eC⟩, c₃, c₄⟩ := GlobalTheory.T.exists_free_complex_primitive_lineBundle_cech_fibres A B' hB' hp' g hg' F hF hΛ P
  refine ⟨I, C, c₁, c₂, ⟨eC.trans eI⟩, fun p _ => ?_, fun R _ _ φ =>
    (test R φ _ _ _ (IsPullback.of_hasPullback _ _)).symm.trans (hI R φ _ _ _ (IsPullback.of_hasPullback _ _)), ?_⟩
  · let K := AlgebraicClosure p.ResidueField
    let φ : A →+* K := (algebraMap p.ResidueField K).comp (algebraMap A p.ResidueField)
    have hk : RingHom.ker φ = p := by
      rw [RingHom.ker_comp_of_injective _ (algebraMap p.ResidueField K).injective, Ideal.ker_algebraMap_residueField]
    refine ⟨K, inferInstance, φ, hk, fun i hi => c₃ K φ _ _ _ (IsPullback.of_hasPullback _ _) i ?_⟩
    rcases hi with hi | hi
    · exact Or.inr fun ht => hi (hk ▸ (hI K φ _ _ _ (IsPullback.of_hasPullback _ _)).1 ht)
    · exact Or.inl hi
  · intro K _ φ hy X' π' f' hX κ _ _ D hD hc i
    let π : X' ⟶ B'.left := pullback.lift π' (f' ≫ Spec.map (CommRingCat.ofHom φ)) (by
      simp only [Category.assoc]
      exact hX.w)
    have hπ : IsPullback π f' B'.hom (Spec.map (CommRingCat.ofHom φ)) := by
      refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hpb
      rw [pullback.lift_fst]
      exact hX
    have ht : Triv (F.pull π) := (test K φ X' π f' hπ).2 hy
    obtain ⟨w, hw⟩ := (CechPic.iso_triv_iff (F.pull π)).2 ht
    obtain ⟨e⟩ := c₄ K φ X' π f' hπ κ D hD hc i
    exact ⟨e.trans (HomologicalComplex.homologyMapIso
      (cechLBCongr f' D (LB.isLB_triv X') (pull_isLB hF π) w hw) i).symm.toLinearEquiv⟩

end GlobalTheory.MumfordLocalComplex

namespace GlobalTheory.MumfordLocalComplex

theorem exists_ideal_free_complex_at_origin : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), L.IsLB → IsProjBy A.hom → (∃ t : LB.Gen (Theta A L), t.IsGen) → IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → (∀ (T : Over (Sp K)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∃ (J : Ideal (A.left.presheaf.stalk x₀)) (C : CochainComplex (ModuleCat.{0} (A.left.presheaf.stalk x₀)) ℕ) (φ : A.left.presheaf.stalk x₀ →+* K), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) ∧ RingHom.ker φ = IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀) ∧ (∀ i, Module.Free (A.left.presheaf.stalk x₀) (C.X i) ∧ Module.Finite (A.left.presheaf.stalk x₀) (C.X i)) ∧ (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧ Nonempty ((Module.Dual (A.left.presheaf.stalk x₀) (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A.left.presheaf.stalk x₀] (A.left.presheaf.stalk x₀ ⧸ J)) ∧ (∀ p : PrimeSpectrum (A.left.presheaf.stalk x₀), ∃ (K' : Type) (_ : Field K') (φ' : A.left.presheaf.stalk x₀ →+* K'), RingHom.ker φ' = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀) ∨ g < i) → (((ModuleCat.extendScalars φ').mapHomologicalComplex _).obj C).ExactAt i) ∧ ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ i, Nonempty (((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology i) ≃ₗ[K] (cechLB A.hom (LB.triv A.left) D).homology i) := by
  intro K _ _ A _ g hA hg L H _ j hL hp hΘ _ hjc hfin hH x₀ hx₀
  have := hA.comm
  have := hA.smooth
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨hO, hu, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ A L hL
  let ηK : Sp K ⟶ A.left := (η[A]).left
  have hηK : ηK ≫ A.hom = 𝟙 _ := Over.w η[A]
  obtain ⟨e, rfl⟩ := hx₀
  obtain rfl : e = IsLocalRing.closedPoint K := @Subsingleton.elim (Sp K) inferInstance _ _
  let φ : A.left.presheaf.stalk (ηK (IsLocalRing.closedPoint K)) →+* K := (Scheme.stalkClosedPointTo ηK).hom
  have hφl : IsLocalHom φ := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo ηK).hom)
  have hφa : Spec.map (CommRingCat.ofHom φ) ≫ A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) = ηK :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk ηK
  have h1 : (1 : 𝟙_ (Over (Sp K)) ⟶ A) = η[A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  obtain ⟨z, hz⟩ := (hH (𝟙_ _) η[A]).1 (h1 ▸ memKL_one hL (𝟙_ (Over (Sp K))))
  have hy : ∃ y : Spec (CommRingCat.of K) ⟶ H.left,
      y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) :=
    ⟨z.left, by rw [hφa]; exact congrArg (·.left) hz⟩
  haveI hN : IsNoetherianRing (A.left.presheaf.stalk (ηK (IsLocalRing.closedPoint K))) := inferInstance
  obtain ⟨I, C, c₁, c₂, eC, c₃, hI, c₅⟩ := @exists_ideal_complex_cech globalFns_holds _ _ A _ _ hA hp g hg L _ hL hO hΘ hu H j
    (fun T x => (hK _ rfl T x).symm.trans (hH T x)) (A.left.presheaf.stalk (ηK (IsLocalRing.closedPoint K))) _ hN _
    (A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K))) K _ φ hφl hy
  refine ⟨I, C, φ, fun R' _ ψ => GlobalTheory.T.local_ring_points_ideal_criterion _ A.left H.left _ j.left hjc I hI R' ψ, ?_, c₁, c₂, eC,
    fun p => ?_, ?_⟩
  · exact ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le (RingHom.ker_ne_top φ) fun x hx => by
      simpa [IsLocalRing.maximalIdeal_eq_bot] using map_nonunit φ x hx).symm
  · obtain ⟨K', _, φ', hk, hex⟩ := c₃ p.asIdeal p.isPrime
    refine ⟨K', inferInstance, φ', hk, fun i hi => hex i (hi.imp_left fun hne hIp => hne ?_)⟩
    obtain ⟨y, hy'⟩ := (hI K' φ').2 (hk ▸ hIp)
    let q := Spec.map (CommRingCat.ofHom φ') (IsLocalRing.closedPoint K')
    have hq : q.asIdeal = RingHom.ker φ' := by
      show Ideal.comap φ' (IsLocalRing.maximalIdeal K') = _
      rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
    have e : j.left (y (IsLocalRing.closedPoint K')) =
        A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) q :=
      congrArg (fun f => f (IsLocalRing.closedPoint K')) hy'
    have hc : IsClosed ({j.left (y (IsLocalRing.closedPoint K'))} : Set A.left) := by
      have := j.left.isClosedEmbedding.isClosedMap _
        (GlobalTheory.StabFlat.isClosed_of_isFinite H.hom (y (IsLocalRing.closedPoint K')) (Subsingleton.elim _ (IsLocalRing.closedPoint K)))
      rwa [Set.image_singleton] at this
    have hs : A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) q ⤳ ηK (IsLocalRing.closedPoint K) := by
      have : A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) q ∈
          Set.range (A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K))) := ⟨q, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have e' : ηK (IsLocalRing.closedPoint K) = A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) q :=
      (hs.mem_closed hc e.symm).trans e
    have hq' : q = IsLocalRing.closedPoint _ := (A.left.fromSpecStalk _).isEmbedding.injective
      (e'.symm.trans Scheme.fromSpecStalk_closedPoint.symm)
    rw [← hk, ← hq, hq']
    rfl
  · intro κ _ _ D hD hc i
    have hsq : IsPullback (𝟙 A.left) A.hom A.hom
        (Spec.map (CommRingCat.ofHom φ) ≫ A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) ≫ A.hom) := by
      rw [← Category.assoc, hφa, hηK]
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    exact c₅ K φ hy A.left (𝟙 _) A.hom hsq κ D hD hc i

end GlobalTheory.MumfordLocalComplex
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
open Formalism.UG (cT)
open scoped TensorProduct Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BlockForms.LeviLoc

section Lin

variable (R : Type) [CommRing R] {l d n : ℕ}

variable {R}

theorem map_formula {T : Type} [CommRing T] (p : R →+* T) (s : R →+* R) (X Y : Matrix (Fin n) (Fin d) R)
    (X' Y' : Matrix (Fin d) (Fin n) R) (P Q : Matrix (Fin d) (Fin d) R) (hQ : Q.map (p.comp s) = 1) :
    (1 + X * (P - 1) * Y' + Y * (cT s Q - 1) * X').map p = 1 + X.map p * (P.map p - 1) * Y'.map p := by
  have h1 : (cT s Q).map p = 1 := by
    rw [← Matrix.transpose_one, ← hQ]; rfl
  rw [Matrix.map_add _ (map_add p), Matrix.map_add _ (map_add p), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
    Matrix.map_mul, Matrix.map_sub _ (map_sub p), Matrix.map_sub _ (map_sub p), h1,
    Matrix.map_one _ (map_zero p) (map_one p), Matrix.map_one _ (map_zero p) (map_one p)]
  simp

end Lin

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
  {C : GL (Fin n) E} {l d : ℕ}


end Frame

section Adele

theorem gl_entry {R : Type} [CommRing R] {d : ℕ} {x y : GL (Fin d) R} (h : x = y) (a b : Fin d) : x.1 a b = y.1 a b := by
  rw [h]

open GlobalTheory.LFun GlobalTheory.CuspRep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem compFin_eq (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    compFin F E u z = Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E) (finTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

omit [NumberField E] in
theorem compFin_sigR (σ : E →ₐ[F] E) (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    compFin F E u (sigR _ σ z) = sigR _ σ (compFin F E u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]


theorem compFin_eq_zero (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E)
    (hz : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = u → pLoc E w (finAdEquiv F E (finTens F E z)) = 0) :
    compFin F E u z = 0 := by
  have h1 : ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E)) * finTens F E z = 0 := by
    refine (finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun w => ?_)
    rw [map_mul, map_zero]
    change pLoc E w (_ * _) = pLoc E w 0
    rw [map_mul, map_zero]
    by_cases hw : w.under (𝓞 F) = u
    · rw [hz w hw, mul_zero]
    · have e : pLoc E w (finAdEquiv F E ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E))) = 0 := by
        refine Eq.trans (b := toCompl (rfl : w.under (𝓞 F) = _) _)
          (finAdEquiv_apply rfl ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E))) ?_
        rw [Algebra.TensorProduct.map_tmul, evalV_singleFin_ne hw, TensorProduct.zero_tmul, map_zero]
      rw [e, zero_mul]
  have h2 := congrArg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E)) h1
  rwa [map_mul, map_zero, Algebra.TensorProduct.map_tmul, evalV_singleFin_self, map_one,
    ← Algebra.TensorProduct.one_def, one_mul, ← compFin_eq] at h2



variable {Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E} {j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E}
  (hΦ : ∀ z, Φ z = (j (infTens F E z), finAdEquiv F E (finTens F E z))) {d : ℕ}
include hΦ

theorem fin_symm (a : Ad E) : finAdEquiv F E (finTens F E (Φ.symm a)) = pFin E a :=
  (congrArg Prod.snd (hΦ (Φ.symm a))).symm.trans (congrArg (pFin E) (Φ.apply_symm_apply a))

end Adele


end GlobalTheory.BlockForms.LeviLoc

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.WeilAddLeft

theorem pow_comp_hom {S : Scheme.{0}} {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem unitOn_mul {R : Type} [CommRing R] (u v : Rˣ) : unitOn (u * v) = unitOn u * unitOn v :=
  map_mul (Units.map _) u v

theorem weilEq_mul_left : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f₁ f₂ g : A.t.G ⟶ B.t.G), IsMonHom f₁ → IsMonHom f₂ →
    IsMonHom g → ∀ r₁ r₂ : 𝓞 E,
    WeilEq B.t.PP.L f₁ g A.t.PP.L (A.t.act.act r₁) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f₂ g A.t.PP.L (A.t.act.act r₂) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L (f₁ * f₂) g A.t.PP.L (A.t.act.act (r₁ + r₂)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ σ₁ A B f₁ f₂ g hf₁ hf₂ hg r₁ r₂ h₁ h₂ n x y c hn hx hy
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  haveI : IsCommMonObj B.pol.A := B.pol.isAb.comm
  haveI : IsCommMonObj A.pol.A := A.pol.isAb.comm
  have tor : ∀ (f : A.t.G ⟶ B.t.G), IsMonHom f → ((x ≫ f) ^ n = 1) := fun f hf => by
    rw [← pow_comp_hom, hx, one_comp]
  have tory : (y ≫ g) ^ n = 1 := by rw [← pow_comp_hom, hy, one_comp]
  obtain ⟨c₁, hc₁⟩ := TorsionGenerators.exists_weilIs hL B.pol (σ₁.comp (algebraMap (𝓞 K) K)) (tor f₁ hf₁) tory
  obtain ⟨c₂, hc₂⟩ := TorsionGenerators.exists_weilIs hL B.pol (σ₁.comp (algebraMap (𝓞 K) K)) (tor f₂ hf₂) tory
  have a₁ := (h₁ n x y c₁ hn hx hy).1 hc₁
  have a₂ := (h₂ n x y c₂ hn hx hy).1 hc₂
  have hB := weilIs_mul_left hL.globalFns _ B.pol n _ _ _ _ _ _ hc₁ hc₂
  have hA := weilIs_mul_left hL.globalFns _ A.pol n _ _ _ _ _ _ a₁ a₂
  rw [← MonObj.comp_mul] at hB hA
  rw [← A.t.act.add] at hA
  rw [← unitOn_mul] at hB hA
  constructor
  · intro h
    obtain rfl := weilIs_unique_fieldPoint _ _ _ B.t.PP.isLB _ _ _ _ _ _ _ h hB
    exact hA
  · intro h
    obtain rfl := weilIs_unique_fieldPoint _ _ _ A.t.PP.isLB _ _ _ _ _ _ _ h hA
    exact hB

end GlobalTheory.CM.WeilAddLeft
end
end
