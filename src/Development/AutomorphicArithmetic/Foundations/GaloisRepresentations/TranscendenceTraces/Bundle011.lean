module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle393
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.ptEx_of :
    PtEx := by
  intro X s
  let Ω : Type := AlgebraicClosure (X.residueField s)
  let y : gp Ω ⟶ Spec (X.residueField s) :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField s) Ω))
  refine ⟨Ω, inferInstance, inferInstance, y ≫ X.fromSpecResidueField s, ?_⟩
  rw [pt_comp]
  exact Scheme.fromSpecResidueField_apply s (pt y)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtPt_of :
    WtExt → PtCommon → WtPt := by
  intro hE hC Z S p _ w hw Ω Ω' _ _ _ _ z z' h
  obtain ⟨L, _, _, a, a', ha⟩ := hC Z Ω Ω' z z' h
  rw [← hE p w hw Ω L z a, ← hE p w hw Ω' L z' a', ha]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.corrGraphQ_of :
    TrIdQ → WtLin → CorrGraphQ := by
  intro hT hW S Y f d
  refine ⟨⟨S, 𝟙 S, f, Wt.const S d, inferInstance, hW.2.2 (𝟙 S) d⟩, ?_, ?_, ?_⟩
  · intro B bY
    simp
  · intro Ω _ _ x y
    constructor
    · intro h
      have hs : {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y} = {x} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Category.comp_id]
        constructor
        · exact fun hz => hz.1
        · rintro rfl
          exact ⟨rfl, h⟩
      change ∑ᶠ z ∈ {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y}, Wt.const S d Ω z = d
      rw [hs, finsum_mem_singleton]
      rfl
    · intro h
      have hs : {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y} = ∅ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Category.comp_id]
        rintro ⟨rfl, h'⟩
        exact h h'
      change ∑ᶠ z ∈ {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y}, Wt.const S d Ω z = 0
      rw [hs, finsum_mem_empty]
  · intro l _ n i hl
    change (trHQ l (𝟙 S) (Wt.const S d) n i).comp (pullHQ l (sch.map f) n i) = _
    rw [hT l n i S d hl, LinearMap.smul_comp, LinearMap.id_comp]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.isolateSpec_of :
    IsolateSpec := by
  intro R B _ _ _ _ z
  let z' : PrimeSpectrum B := z
  haveI : z'.asIdeal.IsPrime := z'.isPrime
  haveI : Algebra.QuasiFiniteAt R z'.asIdeal := inferInstance
  obtain ⟨R', _, _, hEt, P, _, _, e, he, P', hP', hlo, hq, heP, -, -, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (z'.asIdeal.under R) z'.asIdeal
  have pb := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R R' B)).flip
  refine ⟨⟨Spec (CommRingCat.of R'), Spec (CommRingCat.of (TensorProduct R R' B)), _, _, _, pb⟩,
    ((PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum (TensorProduct R R' B))) :
      Set (PrimeSpectrum (TensorProduct R R' B))),
    (⟨P', hP'⟩ : PrimeSpectrum (TensorProduct R R' B)), ?_, ?_, ?_, ?_, ?_⟩
  · exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hEt)
  · exact PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  · exact heP
  · apply PrimeSpectrum.ext
    exact hq
  · intro v' hv' hr
    have h1 : (v' : PrimeSpectrum (TensorProduct R R' B)).asIdeal.LiesOver P := by
      constructor
      have h2 : Ideal.comap (algebraMap R' (TensorProduct R R' B))
          (v' : PrimeSpectrum (TensorProduct R R' B)).asIdeal =
          Ideal.comap (algebraMap R' (TensorProduct R R' B)) P' :=
        congrArg PrimeSpectrum.asIdeal hr
      rw [Ideal.under, h2]
      exact hlo.over
    apply PrimeSpectrum.ext
    exact huniq _ (PrimeSpectrum.isPrime _) h1 hv'
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private lemma exists_pow_mem_of_fixed (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Normal K L] (q : ℕ) [ExpChar K q] (x : L) (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) :
    ∃ n, x ^ q ^ n ∈ (algebraMap K L).range := by
  classical
  rw [← mem_perfectClosure_iff_pow_mem q, mem_perfectClosure_iff_natSepDegree_eq_one]
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hspl : ((minpoly K x).map (algebraMap K L)).Splits := Normal.splits inferInstance x
  rw [Polynomial.natSepDegree_eq_of_splits _ hspl, Finset.card_eq_one]
  refine ⟨x, ?_⟩
  ext y
  simp only [Multiset.mem_toFinset, Polynomial.mem_aroots, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hy⟩
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' hint.isAlgebraic hy
    rw [← hσ, hx σ]
  · intro h
    rw [h]
    exact ⟨minpoly.ne_zero hint, minpoly.aeval K x⟩

private lemma fixed_pow_mem (A L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
    [Normal (FractionRing A) L] (q : ℕ) [ExpChar (FractionRing A) q] (b : integralClosure A L)
    (hb : ∀ g : integralClosure A L ≃ₐ[A] integralClosure A L, g b = b) :
    ∃ (n : ℕ) (a : A), b ^ q ^ n = algebraMap A (integralClosure A L) a := by
  have hx : ∀ σ : L ≃ₐ[FractionRing A] L, σ (b : L) = b := fun σ => by
    have h := algebraMap_galRestrict_apply A (K := FractionRing A) (L := L)
      (B := integralClosure A L) σ b
    rw [hb] at h
    exact h.symm
  obtain ⟨n, k, hk⟩ := exists_pow_mem_of_fixed (FractionRing A) L q (b : L) hx
  have hint : IsIntegral A (algebraMap (FractionRing A) L k) := by
    rw [hk]
    exact (b ^ q ^ n).2
  have hk' : IsIntegral A k :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom A (FractionRing A) L)
      (algebraMap (FractionRing A) L).injective).mp hint
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hk'
  refine ⟨n, a, Subtype.ext ?_⟩
  rw [SubmonoidClass.coe_pow, ← hk, ← ha, ← IsScalarTower.algebraMap_apply]
  rfl

private lemma eq_of_fixed (A L Ω : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
    [Normal (FractionRing A) L] [Field Ω] (φ φ' : integralClosure A L →+* Ω)
    (h : φ.comp (algebraMap A _) = φ'.comp (algebraMap A _)) (b : integralClosure A L)
    (hb : ∀ g : integralClosure A L ≃ₐ[A] integralClosure A L, g b = b) : φ b = φ' b := by
  obtain ⟨q, hq⟩ := ExpChar.exists (FractionRing A)
  obtain ⟨n, a, ha⟩ := fixed_pow_mem A L q b hb
  have h1 : φ b ^ q ^ n = φ' b ^ q ^ n := by
    rw [← map_pow, ← map_pow, ha]
    exact congrArg (fun f : A →+* Ω => f a) h
  cases hq with
  | zero => simpa using h1
  | prime hp =>
    have hA : (q : A) = 0 := by
      apply IsFractionRing.injective A (FractionRing A)
      rw [map_natCast, map_zero, CharP.cast_eq_zero]
    have hΩ : (q : Ω) = 0 := by
      have := congrArg (fun f : A →+* Ω => f q) h
      simp only [RingHom.comp_apply, map_natCast] at this
      rw [← map_natCast (φ.comp (algebraMap A _)) q, hA, map_zero]
    haveI : CharP Ω q := (CharP.charP_iff_prime_eq_zero hp).mpr hΩ
    haveI : ExpChar Ω q := ExpChar.prime hp
    exact iterateFrobenius_inj Ω q n h1

theorem UpperTheory.Gal.TranscendenceTraces.galTrans_of : InvTrans → GalTrans := by
  intro hInv A L Ω _ _ _ _ _ _ _ _ _ _ φ φ' h
  let G := integralClosure A L ≃ₐ[A] integralClosure A L
  haveI : Finite G :=
    Finite.of_equiv _ (galRestrict A (FractionRing A) L (integralClosure A L)).toEquiv
  let A' := FixedPoints.subring (integralClosure A L) G
  haveI : SMulCommClass G A' (integralClosure A L) := ⟨fun g a b => by
    change g • ((a : integralClosure A L) * b) = (a : integralClosure A L) * (g • b)
    rw [smul_mul', show g • (a : integralClosure A L) = a from a.2 g]⟩
  haveI : Algebra.IsInvariant A' (integralClosure A L) G := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  obtain ⟨g, hg⟩ := hInv A' (integralClosure A L) G Ω φ φ' (by
    ext a
    exact eq_of_fixed A L Ω φ φ' h a fun g => a.2 g)
  exact ⟨g, hg⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.imageOne_of :
    ImageOne := by
  intro Z P S k b _ _ _
  have hk : IsFinite k := IsFinite.of_comp k b
  have ht : IsFinite k.toImage := by
    have : IsFinite (k.toImage ≫ k.imageι) := by rw [k.toImage_imageι]; exact hk
    exact IsFinite.of_comp k.toImage k.imageι
  have hs : Surjective k.toImage :=
     surjective_of_isDominant_of_isClosed_range k.toImage k.toImage.isClosedMap.isClosed_range
  have e : k.toImage ≫ (k.imageι ≫ b) = k ≫ b := k.toImage_imageι_assoc b
  have huc : UniversallyClosed (k.imageι ≫ b) := by
    have : UniversallyClosed (k.toImage ≫ (k.imageι ≫ b)) := by rw [e]; infer_instance
    exact UniversallyClosed.of_comp_surjective k.toImage _
  have hqf : LocallyQuasiFinite (k.imageι ≫ b) := by
    refine .of_finite_preimage_singleton _ fun s => ?_
    refine (((k ≫ b).finite_preimage_singleton s).image k.toImage).subset ?_
    intro y hy
    obtain ⟨x, rfl⟩ := k.toImage.surjective y
    refine ⟨x, ?_, rfl⟩
    have : (k ≫ b) x = (k.imageι ≫ b) (k.toImage x) := by
      rw [← e, Scheme.Hom.comp_apply]
    exact this.trans hy
  have : IsProper (k.imageι ≫ b) := ⟨⟩
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, ht⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped TensorProduct

namespace UpperTheory.Gal.TranscendenceTraces

private noncomputable def pushIso (A B O : Type) [CommRing A] [CommRing B] [CommRing O] [Algebra A B] [Algebra A O] :
    (Under.pushout (CommRingCat.ofHom (algebraMap A B))).obj (Under.mk (CommRingCat.ofHom (algebraMap A O))) ≅
      Under.mk (CommRingCat.ofHom (algebraMap B (B ⊗[A] O))) :=
  Under.isoMk (CommRingCat.isPushout_tensorProduct A B O).flip.isoPushout.symm
    ((CommRingCat.isPushout_tensorProduct A B O).flip.inr_isoPushout_inv)

private def algOf {B C T : Type} [CommRing B] [CommRing C] [CommRing T] [Algebra B C] [Algebra B T]
    (f : Under.mk (CommRingCat.ofHom (algebraMap B C)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap B T))) : C →ₐ[B] T :=
  { f.right.hom with
    commutes' := fun b => by
      have := congr($(Under.w f).hom b)
      simpa using this }

private def underOf {B C T : Type} [CommRing B] [CommRing C] [CommRing T] [Algebra B C] [Algebra B T]
    (f : C →ₐ[B] T) : Under.mk (CommRingCat.ofHom (algebraMap B C)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap B T)) :=
  Under.homMk (CommRingCat.ofHom f.toRingHom) (by ext b; exact f.commutes b)

end UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.indDesc_of :
    IndDesc := by
  intro A O B C _ _ _ _ _ _ _ _ hO ⟨g⟩
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, hD⟩ := GlobalTheory.T.exists_filtered_colimit_of_etale_of_indEt A O hO
  let F := Under.pushout (CommRingCat.ofHom (algebraMap A B))
  have hFc := isColimitOfPreserves F hc
  have : IsFinitelyPresentable.{0} (Under.mk (CommRingCat.ofHom (algebraMap B C))) :=
    CommRingCat.isFinitelyPresentable_under _ _
      (show (algebraMap B C).FinitePresentation from
        (RingHom.finitePresentation_algebraMap (A := B) (B := C)).mpr inferInstance)
  obtain ⟨j, q, -⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hFc
    (underOf g ≫ (pushIso A B O).inv)
  let E : Type := (D.obj j).right
  letI : Algebra A E := (D.obj j).hom.hom.toAlgebra
  refine ⟨E, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact RingHom.etale_algebraMap.mp (hD j)
  · refine ⟨{ (ι.app j).right.hom with commutes' := fun a => ?_ }⟩
    have := congr($(Under.w (ι.app j)).hom a)
    exact this
  · exact ⟨algOf (q ≫ (pushIso A B E).hom)⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.locFinSec_of :
    CoverOne → LocFinGeo → LocFinSec := by
  intro hC hG R _ F G f V U r _ b hb
  obtain ⟨W, π, a, hE, hS, ha⟩ := hC R f V b hb
  haveI := hE
  haveI := hS
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ (hG π r) ?_
  rintro U' g ⟨s, hs⟩ V' k r' hk
  refine ⟨Sec.res (pullback.lift k r' hk ≫ s) a, ?_⟩
  rw [map_res, ha, res_res]
  congr 1
  rw [Category.assoc, hs, pullback.lift_fst]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem res_zsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℤ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := by
  simp

private theorem sec_eq_of_isEmpty {R : Type} [CommRing R] {F : Shv R} (W : Scheme.{0}) [IsEmpty W] (a b : Sec F W) : a = b :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue R F W).1 a b (GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.2.2 W _)

theorem UpperTheory.Gal.TranscendenceTraces.funSec_of :
    FunSec := by
  intro q _ i U ζ φ hφ
  let V : ℤ → U.Opens := fun n => ⟨{x | φ x = n}, hφ.isOpen_fiber n⟩
  have hmem : ∀ (n : ℤ) (v : (V n : Scheme)), φ ((V n).ι v) = n := by
    intro n v
    have h1 : (V n).ι v ∈ Set.range (V n).ι := ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι] at h1
    exact h1
  have hcov : ∀ u : U, ∃ n, ∃ v, (V n).ι v = u := by
    intro u
    refine ⟨φ u, ?_⟩
    have h1 : u ∈ Set.range (V (φ u)).ι := by
      rw [Scheme.Opens.range_ι]
      exact rfl
    exact h1
  obtain ⟨y, hy⟩ := (GlobalTheory.T.etaleSheafSections_sep_glue_of_surjective_family (ZMod q) (tw q i) U ℤ (fun n => (V n : Scheme)) (fun n => (V n).ι)
    (fun n => inferInstance) hcov).2 (fun n => n • Sec.res (V n).ι (twGen i ζ)) (by
      intro n m
      by_cases h : n = m
      · subst h
        rw [res_zsmul, res_zsmul, res_res, res_res, pullback.condition]
      · haveI : IsEmpty ↥(pullback (V n).ι (V m).ι) := by
          refine ⟨fun p => h ?_⟩
          have e1 := hmem n (pullback.fst (V n).ι (V m).ι p)
          have e2 := hmem m (pullback.snd (V n).ι (V m).ι p)
          have hc : (V n).ι (pullback.fst (V n).ι (V m).ι p) =
              (V m).ι (pullback.snd (V n).ι (V m).ι p) :=
            congrArg (fun f : pullback (V n).ι (V m).ι ⟶ U => f p) pullback.condition
          rw [hc] at e1
          exact e1.symm.trans e2
        exact sec_eq_of_isEmpty _ _ _)
  refine ⟨y, ?_⟩
  intro Ω _ _ x
  have hr : Set.range x ⊆ Set.range (V (φ (pt x))).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    show φ (x s) = φ (pt x)
    rw [pt_eq]
  obtain ⟨k, hk⟩ : ∃ k, k ≫ (V (φ (pt x))).ι = x := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  calc Sec.res x y = Sec.res (k ≫ (V (φ (pt x))).ι) y := by rw [hk]
    _ = Sec.res k ((φ (pt x)) • Sec.res (V (φ (pt x))).ι (twGen i ζ)) := by
        rw [← res_res, hy]
    _ = φ (pt x) • Sec.res x (twGen i ζ) := by rw [res_zsmul, res_res, hk]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces.RepresentationImage

variable {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}

private theorem img_zero (τ : Fam p I J) (n : ℤ) :
    τ.IsImage (0 : Cochain ((chains R').obj (sch.obj Z)) I n) (0 : Cochain ((chains R).obj (sch.obj S)) J n) := by
  intro k s h A
  have h1 := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj S) (I := J) (n := n)).1 0 0 k s h A.U A.u).2.2.1
  have h2 := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R' (E := sch.obj Z) (I := I) (n := n)).1 0 0 k s h A.V A.v).2.2.1
  exact h1.trans ((map_zero ((τ.deg s).app A)).symm.trans (congrArg ((τ.deg s).app A) h2.symm))

private theorem img_add (τ : Fam p I J) {n : ℤ} {a a' : Cochain ((chains R').obj (sch.obj Z)) I n}
    {b b' : Cochain ((chains R).obj (sch.obj S)) J n} (h : τ.IsImage a b) (h' : τ.IsImage a' b') :
    τ.IsImage (a + a') (b + b') := by
  intro k s hs A
  rw [((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 b b' k s hs A.U A.u).1, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R').1 a a' k s hs A.V A.v).1, map_add (f := _),
    h k s hs A, h' k s hs A]

private noncomputable def imgc (hI : ImgBasic) (τ : Fam p I J) {n : ℤ}
    (α : Cocycle ((chains R').obj (sch.obj Z)) I n) : Cocycle ((chains R).obj (sch.obj S)) J n :=
  Cocycle.mk ((hI R' R τ n).1 α.1).exists.choose (n + 1) rfl (by
    have h := (hI R' R τ n).2 (n + 1) rfl _ _ ((hI R' R τ n).1 α.1).exists.choose_spec
    rw [Cocycle.δ_eq_zero] at h
    exact ((hI R' R τ (n + 1)).1 0).unique h (img_zero τ (n + 1)))

private theorem imgc_spec (hI : ImgBasic) (τ : Fam p I J) {n : ℤ}
    (α : Cocycle ((chains R').obj (sch.obj Z)) I n) : τ.IsImage α.1 (imgc hI τ α).1 :=
  ((hI R' R τ n).1 α.1).exists.choose_spec

private theorem imgc_eq (hI : ImgBasic) (τ : Fam p I J) {n : ℤ}
    (α : Cocycle ((chains R').obj (sch.obj Z)) I n) (β : Cocycle ((chains R).obj (sch.obj S)) J n)
    (h : τ.IsImage α.1 β.1) : imgc hI τ α = β :=
  Cocycle.ext (((hI R' R τ n).1 α.1).unique (imgc_spec hI τ α) h)

private noncomputable def opMap (hI : ImgBasic) (τ : Fam p I J) (n : ℤ) :
    CohomologyClass ((chains R').obj (sch.obj Z)) I n →+ CohomologyClass ((chains R).obj (sch.obj S)) J n :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (fun α => CohomologyClass.mk (imgc hI τ α)) (fun α α' => by
      rw [← CohomologyClass.mk_add]; congr 1
      exact imgc_eq hI τ _ _ (img_add τ (imgc_spec hI τ α) (imgc_spec hI τ α'))))
    (by
      rintro ⟨a, ha⟩ ⟨n', hn', a', rfl⟩
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      obtain ⟨b, hb, -⟩ := (hI R' R τ n').1 a'
      exact ⟨n', hn', b, ((hI R' R τ n).1 _).unique ((hI R' R τ n').2 n hn' _ _ hb) (imgc_spec hI τ ⟨_, ha⟩)⟩)

private theorem op_spec (hI : ImgBasic) (τ : Fam p I J) (n : ℤ)
    (α : Cocycle ((chains R').obj (sch.obj Z)) I n) (β : Cocycle ((chains R).obj (sch.obj S)) J n)
    (h : τ.IsImage α.1 β.1) : τ.op n (CohomologyClass.mk α) = CohomologyClass.mk β :=
  pick_spec (P := fun c : CohomologyClass ((chains R').obj (sch.obj Z)) I n →+
      CohomologyClass ((chains R).obj (sch.obj S)) J n =>
    ∀ (α : Cocycle _ I n) (β : Cocycle _ J n), τ.IsImage α.1 β.1 →
      c (CohomologyClass.mk α) = CohomologyClass.mk β)
    ⟨opMap hI τ n, fun α β h => congrArg CohomologyClass.mk (imgc_eq hI τ α β h)⟩ α β h

end UpperTheory.Gal.TranscendenceTraces.RepresentationImage

open UpperTheory.Gal.TranscendenceTraces.RepresentationImage in
theorem UpperTheory.Gal.TranscendenceTraces.rpOp_of :
    ImgBasic → RpOp := by
  intro hI Z S p R' R _ _ I J τ n x a hx
  obtain ⟨α, rfl, rfl⟩ := hx
  exact ⟨imgc hI τ α, (op_spec hI τ n α _ (imgc_spec hI τ α)).symm, imgc_spec hI τ α 0 n (by simp) (Sq.self p)⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.locFinGeo_of :
    LocFinAff → LocFinGeo := by
  intro hA W V U π r _ _ _
  rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U (fun V' g ↦ ∃ s, s ≫ π = pullback.fst r g)]
  swap
  · rintro V' W' g k ⟨s, hs⟩
    refine ⟨pullback.lift (pullback.fst r (k ≫ g)) (pullback.snd r (k ≫ g) ≫ k)
      (by simp [pullback.condition]) ≫ s, ?_⟩
    rw [Category.assoc, hs, pullback.lift_fst]
  intro x
  obtain ⟨y, hy⟩ := U.affineCover.covers x
  set ι := U.affineCover.f (U.affineCover.idx x) with hι
  obtain ⟨U', g, hU', hg, ⟨z, hz⟩, s, hs⟩ :=
    hA (pullback.snd π (pullback.fst r ι)) (pullback.snd r ι) y
  refine ⟨U', g ≫ ι, hU', inferInstance, ⟨z, by simp [hz, hy]⟩, ?_⟩
  let φ : pullback r (g ≫ ι) ⟶ pullback (pullback.snd r ι) g :=
    pullback.lift (pullback.lift (pullback.fst r (g ≫ ι)) (pullback.snd r (g ≫ ι) ≫ g)
      (by rw [Category.assoc, ← pullback.condition]))
      (pullback.snd r (g ≫ ι)) (pullback.lift_snd _ _ _)
  refine ⟨φ ≫ s ≫ pullback.fst π (pullback.fst r ι), ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc s, hs]
  dsimp only [φ]
  rw [← Category.assoc, pullback.lift_fst, pullback.lift_fst]
end
