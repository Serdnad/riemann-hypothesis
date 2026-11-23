module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle005
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.Xgn.IntegralPointExtension

theorem exists_lift {A B : CommRingCat.{0}} (ψ : A ⟶ B) [IsDomain A] [ValuationRing A] (hB : IsField B)
    (hf : letI := ψ.hom.toAlgebra; IsFractionRing A B) {Y S : Scheme.{0}} (sY : Y ⟶ S) [IsProper sY]
    (φ : Spec B ⟶ Y) (t : Spec A ⟶ S) (h : φ ≫ sY = Spec.map ψ ≫ t) :
    ∃ m : Spec A ⟶ Y, Spec.map ψ ≫ m = φ ∧ m ≫ sY = t := by
  letI : Algebra A B := ψ.hom.toAlgebra
  letI : Field B := hB.toField
  have hv : ValuativeCriterion.Existence sY :=
    (IsProper.eq_valuativeCriterion ▸ (inferInstance : IsProper sY) :
      (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) sY).1.1.1.existence
  let S : ValuativeCommSq sY :=
    { R := A, K := B, i₁ := φ, i₂ := t, commSq := ⟨h⟩ }
  obtain ⟨⟨l⟩⟩ := hv S
  exact ⟨l.l, l.fac_left, l.fac_right⟩

theorem extend_functionField {X Y S : Scheme.{0}} [IsIntegral X] [Y.IsSeparated]
    (hv : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (φ : Spec X.functionField ⟶ Y) (h : φ ≫ sY = X.fromSpecStalk _ ≫ sX) :
    ∃ g : X ⟶ Y, X.fromSpecStalk (genericPoint X) ≫ g = φ := by
  classical
  have hs : ∀ x : X, genericPoint X ⤳ x := fun x => (genericPoint_spec X).specializes trivial
  have hlift : ∀ x : X, ∃ m : Spec (X.presheaf.stalk x) ⟶ Y,
      Spec.map (X.presheaf.stalkSpecializes (hs x)) ≫ m = φ ∧ m ≫ sY = X.fromSpecStalk x ≫ sX := by
    intro x
    haveI := hv x
    letI : Algebra (X.presheaf.stalk x) X.functionField :=
      (X.presheaf.stalkSpecializes (hs x)).hom.toAlgebra
    have hfr : IsFractionRing (X.presheaf.stalk x) X.functionField := by
      convert (inferInstance : IsFractionRing (X.presheaf.stalk x) X.functionField) using 1
    refine exists_lift (A := X.presheaf.stalk x) (B := X.functionField)
      (X.presheaf.stalkSpecializes (hs x)) (Field.toIsField _) hfr sY φ (X.fromSpecStalk x ≫ sX) ?_
    rw [h, ← Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  choose m hm1 hm2 using hlift
  let r0 := Scheme.PartialMap.ofFromSpecStalk sX sY (x := genericPoint X) φ h
  have hr0 := Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY (x := genericPoint X) φ h
  have hdom : ∀ x : X, x ∈ r0.toRationalMap.domain := by
    intro x
    let gx := Scheme.PartialMap.ofFromSpecStalk sX sY (m x) (hm2 x)
    have hx : x ∈ gx.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY (m x) (hm2 x)
    have hg : genericPoint X ∈ gx.domain := (hs x).mem_open gx.domain.2 hx
    have key : gx.fromSpecStalkOfMem hg = φ := by
      have e1 : gx.domain.fromSpecStalkOfMem (genericPoint X) hg =
          Spec.map (X.presheaf.stalkSpecializes (hs x)) ≫ gx.domain.fromSpecStalkOfMem x hx := by
        rw [← cancel_mono gx.domain.ι]
        simp [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      have e2 := Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY (m x) (hm2 x)
      change gx.domain.fromSpecStalkOfMem (genericPoint X) hg ≫ gx.hom = φ
      rw [e1, Category.assoc]
      change _ ≫ gx.fromSpecStalkOfMem hx = φ
      rw [e2, hm1]
    rw [Scheme.RationalMap.mem_domain]
    refine ⟨gx, hx, Scheme.PartialMap.toRationalMap_eq_iff.mpr ?_⟩
    refine Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq (x := genericPoint X) gx r0 hg hr0 ?_
    rw [key, Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
  let P := r0.toRationalMap.toPartialMap
  have htop : (⊤ : X.Opens) = P.domain := by
    refine (top_le_iff.mp ?_).symm
    intro x _
    exact hdom x
  refine ⟨X.topIso.inv ≫ (X.isoOfEq htop).hom ≫ P.hom, ?_⟩
  have hP : P.toRationalMap = r0.toRationalMap := Scheme.RationalMap.toRationalMap_toPartialMap _
  have hgP : genericPoint X ∈ P.domain := hdom _
  have hPeq : P.fromSpecStalkOfMem hgP = φ := by
    have e4 : P.fromFunctionField = r0.fromFunctionField := by
      rw [← Scheme.RationalMap.fromFunctionField_toRationalMap, hP,
        Scheme.RationalMap.fromFunctionField_toRationalMap]
    exact e4.trans (Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY (x := genericPoint X) φ h)
  have e3 : X.fromSpecStalk (genericPoint X) ≫ X.topIso.inv ≫ (X.isoOfEq htop).hom =
      P.domain.fromSpecStalkOfMem (genericPoint X) hgP := by
    rw [← cancel_mono P.domain.ι]
    simp [Scheme.Opens.fromSpecStalkOfMem_ι]
  rw [← hPeq]
  change _ = P.domain.fromSpecStalkOfMem (genericPoint X) hgP ≫ P.hom
  rw [← e3]
  simp only [Category.assoc]

private theorem valuationRing_localization_atPrime_dedekind (R : Type) [CommRing R] [IsDedekindDomain R] (p : Ideal R) [p.IsPrime] :
    ValuationRing (Localization.AtPrime p) := by
  by_cases h0 : p = ⊥
  · subst h0
    have hF : IsFractionRing R (Localization.AtPrime (⊥ : Ideal R)) := by
      have h1 := Localization.isLocalization (M := (⊥ : Ideal R).primeCompl)
      unfold IsFractionRing
      convert h1 using 1
      exact Ideal.primeCompl_bot.symm
    letI : Field (Localization.AtPrime (⊥ : Ideal R)) := IsFractionRing.toField R
    rw [ValuationRing.iff_dvd_total]
    refine ⟨fun a b => ?_⟩
    by_cases ha : a = 0
    · right; rw [ha]; exact dvd_zero b
    · left; exact ⟨a⁻¹ * b, by rw [← _root_.mul_assoc, mul_inv_cancel₀ ha, _root_.one_mul]⟩
  · haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h0 (Localization.AtPrime p)
    infer_instance

theorem stalk_valuationRing (R : Type) [CommRing R] [IsDedekindDomain R] (x : Sp R) :
    ValuationRing ((Sp R).presheaf.stalk x) := by
  haveI : (PrimeSpectrum.asIdeal (R := R) x).IsPrime := PrimeSpectrum.isPrime (R := R) x
  have e := (Spec.stalkIso (CommRingCat.of R) x).commRingCatIsoToRingEquiv
  have hL := valuationRing_localization_atPrime_dedekind R (PrimeSpectrum.asIdeal (R := R) x)
  rw [ValuationRing.iff_dvd_total] at hL ⊢
  refine ⟨fun a b => (hL.total (e a) (e b)).imp (fun h => ?_) (fun h => ?_)⟩
  · simpa using map_dvd e.symm h
  · simpa using map_dvd e.symm h

theorem extend_dedekind (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {Y S : Scheme.{0}} [Y.IsSeparated] (sX : Sp R ⟶ S) (sY : Y ⟶ S) [IsProper sY] (y : Sp K ⟶ Y)
    (h : y ≫ sY = spMap (algebraMap R K) ≫ sX) : ∃ g : Sp R ⟶ Y, spMap (algebraMap R K) ≫ g = y := by
  classical
  haveI : IsDomain (CommRingCat.of R) := inferInstanceAs (IsDomain R)
  letI : Algebra (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField :=
    instAlgebraCarrierFunctionFieldSpec (CommRingCat.of R)
  haveI : IsFractionRing (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of R)
  let eK : (Spec (CommRingCat.of R)).functionField ≃ₐ[CommRingCat.of R] K :=
    IsLocalization.algEquiv (nonZeroDivisors (CommRingCat.of R)) _ K
  have hfs : (Sp R).fromSpecStalk (genericPoint (Sp R)) =
      Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField)) := by
    rw [Spec.fromSpecStalk_eq']
    rfl
  have hc1 : CommRingCat.ofHom (algebraMap R K) ≫
      CommRingCat.ofHom (eK.symm : K →+* (Spec (CommRingCat.of R)).functionField) =
      CommRingCat.ofHom (algebraMap (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField) := by
    ext r
    simp [eK]
  have hc2 : CommRingCat.ofHom (algebraMap (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField) ≫
      CommRingCat.ofHom (eK : (Spec (CommRingCat.of R)).functionField →+* K) =
      CommRingCat.ofHom (algebraMap R K) := by
    ext r
    simp [eK]
  have hc3 : CommRingCat.ofHom (eK.symm : K →+* (Spec (CommRingCat.of R)).functionField) ≫
      CommRingCat.ofHom (eK : (Spec (CommRingCat.of R)).functionField →+* K) = 𝟙 _ := by
    ext r
    simp
  have k1 : Spec.map (CommRingCat.ofHom (eK.symm : K →+* (Spec (CommRingCat.of R)).functionField)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K)) =
      Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of R) (Spec (CommRingCat.of R)).functionField)) := by
    rw [← hc1, Spec.map_comp]
  have k3 : Spec.map (CommRingCat.ofHom (eK : (Spec (CommRingCat.of R)).functionField →+* K)) ≫
      Spec.map (CommRingCat.ofHom (eK.symm : K →+* (Spec (CommRingCat.of R)).functionField)) =
      𝟙 (Spec (CommRingCat.of K)) := by
    rw [← Spec.map_id, ← hc3, Spec.map_comp]
  let φ : Spec (Spec (CommRingCat.of R)).functionField ⟶ Y :=
    Spec.map (CommRingCat.ofHom (eK.symm : K →+* (Spec (CommRingCat.of R)).functionField)) ≫ y
  have h' : φ ≫ sY = (Sp R).fromSpecStalk _ ≫ sX := by
    show (Spec.map _ ≫ y) ≫ sY = _
    rw [Category.assoc, h, spMap, hfs, ← Category.assoc]
    exact congrArg (· ≫ sX) k1
  obtain ⟨g, hg⟩ := extend_functionField (X := Sp R) (stalk_valuationRing R) sX sY φ h'
  refine ⟨g, ?_⟩
  have e1 : spMap (algebraMap R K) =
      Spec.map (CommRingCat.ofHom (eK : (Spec (CommRingCat.of R)).functionField →+* K)) ≫
        (Sp R).fromSpecStalk (genericPoint (Sp R)) := by
    rw [hfs, spMap, ← Spec.map_comp, hc2]
  rw [e1, Category.assoc, hg]
  show Spec.map _ ≫ Spec.map _ ≫ y = y
  rw [← Category.assoc]
  exact (congrArg (· ≫ y) k3).trans (Category.id_comp y)

end PositivityTheory.Xgn.IntegralPointExtension

theorem PositivityTheory.Xgn.integral_point_extends_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (_ : FiniteDimensional ℚ c.F) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (F : Type) [Field F] [NumberField F] (f : c.F →+* F) (y : Sp F ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap f → ∃ yt : Sp (𝓞 F) ⟶ Y.X, spMap (algebraMap (𝓞 F) F) ≫ yt = y ≫ Y.j := by
  intro E _ _ _ H D l Xo c _ Y F _ _ f y hy
  obtain ⟨N, i, hi, hs⟩ := Y.proj
  haveI : IsProper Y.s := by
    rw [← hs]
    haveI := isProper_str (𝓞 c.F) N
    infer_instance
  haveI : Y.X.IsSeparated := by
    refine ⟨?_⟩
    have e : terminal.from Y.X = Y.s ≫ terminal.from _ := terminal.hom_ext _ _
    rw [e]
    infer_instance
  refine PositivityTheory.Xgn.IntegralPointExtension.extend_dedekind (𝓞 F) F
    (spMap (RingOfIntegers.mapRingHom f)) Y.s (y ≫ Y.j) ?_
  have hj : Y.j ≫ Y.s = pullback.snd Xo.s _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    simp only [Model.j, Category.assoc, pullback.condition]
    rw [← Category.assoc, Y.jQ_over]
  rw [Category.assoc, hj, ← Category.assoc, hy]
  simp only [spMap, ← Spec.map_comp]
  congr 1
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_fam_constr

open ReciprocityTheory.ChartRestriction.G.Geo (exists_pow_mul_mem_chartRing div_mem_chartRing)

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} {x : (Σ k, ι k) → Ω}
variable {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]

theorem mono {Γ : (∀ k, ι k) → AddSubgroup V} (h : IsLatFamily o x Γ) {s t : ∀ k, ι k}
    (ht : mseg x t ≠ 0) {v : V} {m m' : ℕ} (hm : m ≤ m') (hv : (mseg x s / mseg x t) ^ m • v ∈ Γ t) :
    (mseg x s / mseg x t) ^ m' • v ∈ Γ t := by
  rw [← Nat.sub_add_cancel hm, pow_add, mul_smul]
  exact h.1 t ht _ (pow_mem (div_mem_chartRing (mseg x) t s) _) _ hv

theorem fam_sub (U : Submodule Ω V) : IsLatFamily o x (fun _ => U.toAddSubgroup) :=
  ⟨fun _ _ a _ _ hv => U.smul_mem a hv, fun _ _ _ _ _ hv => ⟨0, U.smul_mem _ hv⟩⟩

theorem fam_top : IsLatFamily o x (fun _ => (⊤ : AddSubgroup V)) :=
  ⟨fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => ⟨0, trivial⟩⟩

theorem fam_bot : IsLatFamily o x (fun _ => (⊥ : AddSubgroup V)) := fam_sub ⊥

theorem fam_sup {A B : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x (fun c => A c ⊔ B c) := by
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
    rw [smul_add]
    exact AddSubgroup.add_mem_sup (hA.1 s hs a ha y hy) (hB.1 s hs a ha z hz)
  · obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
    obtain ⟨m, hm⟩ := hA.2 s t hs ht y hy
    obtain ⟨m', hm'⟩ := hB.2 s t hs ht z hz
    refine ⟨m + m', ?_⟩
    rw [smul_add]
    exact AddSubgroup.add_mem_sup (mono hA ht (Nat.le_add_right _ _) hm)
      (mono hB ht (Nat.le_add_left _ _) hm')

theorem fam_inf {A B : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x (fun c => A c ⊓ B c) := by
  refine ⟨fun s hs a ha v hv => ⟨hA.1 s hs a ha v hv.1, hB.1 s hs a ha v hv.2⟩,
    fun s t hs ht v hv => ?_⟩
  obtain ⟨m, hm⟩ := hA.2 s t hs ht v hv.1
  obtain ⟨m', hm'⟩ := hB.2 s t hs ht v hv.2
  exact ⟨m + m', mono hA ht (Nat.le_add_right _ _) hm, mono hB ht (Nat.le_add_left _ _) hm'⟩

theorem fam_map {A : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (f : V →+ V₁)
    (hf : ∀ (a : Ω) v, f (a • v) = a • f v) : IsLatFamily o x (fun c => (A c).map f) := by
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨_, hA.1 s hs a ha y hy, hf a y⟩
  · obtain ⟨y, hy, rfl⟩ := hv
    obtain ⟨m, hm⟩ := hA.2 s t hs ht y hy
    exact ⟨m, _, hm, hf _ y⟩

theorem fam_comap {A : (∀ k, ι k) → AddSubgroup V₁} (hA : IsLatFamily o x A) (f : V →+ V₁)
    (hf : ∀ (a : Ω) v, f (a • v) = a • f v) : IsLatFamily o x (fun c => (A c).comap f) := by
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · rw [AddSubgroup.mem_comap, hf]
    exact hA.1 s hs a ha _ hv
  · obtain ⟨m, hm⟩ := hA.2 s t hs ht _ hv
    exact ⟨m, by rw [AddSubgroup.mem_comap, hf]; exact hm⟩

theorem fam_prod {A : (∀ k, ι k) → AddSubgroup V} {B : (∀ k, ι k) → AddSubgroup V₁}
    (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x (fun c => (A c).prod (B c)) := by
  refine ⟨fun s hs a ha v hv => ⟨hA.1 s hs a ha _ hv.1, hB.1 s hs a ha _ hv.2⟩,
    fun s t hs ht v hv => ?_⟩
  obtain ⟨m, hm⟩ := hA.2 s t hs ht _ hv.1
  obtain ⟨m', hm'⟩ := hB.2 s t hs ht _ hv.2
  exact ⟨m + m', mono hA ht (Nat.le_add_right _ _) hm, mono hB ht (Nat.le_add_left _ _) hm'⟩

theorem mem_stdLat (R : Subalgebra o Ω) {J : Type} (v : J → Ω) : v ∈ stdLat R J ↔ ∀ j, v j ∈ R :=
  ⟨fun h j => h j trivial, fun h j _ => h j⟩

theorem fam_std (J : Type) [Fintype J] :
    IsLatFamily o x (fun c => stdLat (chartRing o (mseg x) c) J) := by
  refine ⟨fun s _ a ha v hv => ?_, fun s t hs _ v hv => ?_⟩
  · rw [mem_stdLat] at hv ⊢
    exact fun j => mul_mem ha (hv j)
  · rw [mem_stdLat] at hv
    choose m hm using fun j => exists_pow_mul_mem_chartRing (mseg x) s t hs (hv j)
    refine ⟨∑ q, m q, (mem_stdLat _ _).2 fun q => ?_⟩
    have hle : m q ≤ ∑ q, m q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    rw [Pi.smul_apply, smul_eq_mul, ← Nat.sub_add_cancel hle, pow_add, mul_assoc]
    exact mul_mem (pow_mem (div_mem_chartRing (mseg x) t s) _) (hm q)

theorem mem_dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (w : Fin m → Ω) :
    w ∈ dotDual R L ↔ ∀ v ∈ L, v ⬝ᵥ w ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

def FG (R : Subalgebra o Ω) (L : AddSubgroup V) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (g : I → V), (∀ i, g i ∈ L) ∧
    ∀ e ∈ L, ∃ a : I → Ω, (∀ i, a i ∈ R) ∧ ∑ i, a i • g i = e

theorem fg_of_locFree {R : Subalgebra o Ω} {r : ℕ} {L : AddSubgroup V} (h : LocFree R r L) :
    FG R L := by
  let L' : Submodule R V := { L with smul_mem' := fun a e he => h.1 a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L') (r := r) h
  exact ⟨_, inferInstance, fun i => v i, fun i => (v i).2,
    fun e he => ⟨fun i => φ i e, fun i => hφ i e he, hv e⟩⟩

theorem fg_comap {R : Subalgebra o Ω} {L : AddSubgroup V₁} (h : FG R L) (f : V →ₗ[Ω] V₁)
    (hf : Function.Injective f) (hS : Summand L (LinearMap.range f)) :
    FG R (L.comap f.toAddMonoidHom) := by
  obtain ⟨I, hI, g, hg, hL⟩ := h
  obtain ⟨ρ, h1, h2, h3⟩ := hS
  choose y hy using fun i => h1 (g i)
  refine ⟨I, hI, y, fun i => ?_, fun e he => ?_⟩
  · change f (y i) ∈ L
    rw [hy]
    exact h3 _ (hg i)
  · obtain ⟨a, ha, hs⟩ := hL (f e) he
    refine ⟨a, ha, hf ?_⟩
    rw [← h2 (f e) ⟨e, rfl⟩, ← hs]

    simp only [map_sum, map_smul, hy]

theorem fam_dual {m : ℕ} {A : (∀ k, ι k) → AddSubgroup (Fin m → Ω)} (hA : IsLatFamily o x A)
    (hfg : ∀ c, mseg x c ≠ 0 → FG (chartRing o (mseg x) c) (A c)) :
    IsLatFamily o x (fun c => dotDual (chartRing o (mseg x) c) (A c)) := by
  refine ⟨fun s _ a ha w hw => ?_, fun s t hs ht w hw => ?_⟩
  · rw [mem_dotDual] at hw ⊢
    intro v hv
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_mem ha (hw v hv)
  · rw [mem_dotDual] at hw
    obtain ⟨I, hI, g, hg, hL⟩ := hfg t ht
    have key : ∀ i, ∃ k : ℕ, (mseg x s / mseg x t) ^ k * (g i ⬝ᵥ w) ∈ chartRing o (mseg x) t := by
      intro i
      obtain ⟨k, hk⟩ := hA.2 t s ht hs _ (hg i)
      obtain ⟨k', hk'⟩ := exists_pow_mul_mem_chartRing (mseg x) s t hs (hw _ hk)
      refine ⟨k', ?_⟩
      have hu : (mseg x s / mseg x t) ^ k * (mseg x t / mseg x s) ^ k = 1 := by
        rw [← mul_pow, div_mul_div_comm, mul_comm (mseg x s), div_self (mul_ne_zero ht hs), one_pow]
      rw [smul_dotProduct, smul_eq_mul] at hk'
      have : (mseg x s / mseg x t) ^ k' * (g i ⬝ᵥ w) = (mseg x s / mseg x t) ^ k *
          ((mseg x s / mseg x t) ^ k' * ((mseg x t / mseg x s) ^ k * (g i ⬝ᵥ w))) := by
        linear_combination (-(mseg x s / mseg x t) ^ k' * (g i ⬝ᵥ w)) * hu
      rw [this]
      exact mul_mem (pow_mem (div_mem_chartRing (mseg x) t s) _) hk'
    choose k hk using key
    refine ⟨∑ q, k q, (mem_dotDual _ _ _).2 fun v hv => ?_⟩
    obtain ⟨a, ha, rfl⟩ := hL v hv
    rw [sum_dotProduct]
    refine sum_mem fun q _ => ?_
    have hle : k q ≤ ∑ q, k q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← Nat.sub_add_cancel hle, pow_add,
      mul_assoc]
    exact mul_mem (ha q) (mul_mem (pow_mem (div_mem_chartRing (mseg x) t s) _) (hk q))

theorem linMap_inj {F : Type} [Zero F] [One F] (n : ℕ) (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) :
    Function.Injective (linMap n χ) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro l hl
  funext j
  have := congrFun hl (Pi.single j 1)
  rw [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Finset.sum_eq_single j] at this
  · simpa [h1] using this
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi, h0]
  · simp

end PositivityTheory.Xgn.A_fam_constr

open PositivityTheory.Xgn.A_fam_constr in
theorem PositivityTheory.Xgn.t_fam_constr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → IsLatFamily O x (fun c => (D c).l1 (chartRing O (mseg x) c) p) ∧ ∀ τ, IsLatFamily O x (fun c => (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ (∀ i, IsLatFamily O x (fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) ∧ IsLatFamily O x (fun c => (D c).stepGraph τ (fun a => algebraMap O Ω (χ τ a)) i)) ∧ (∀ i, IsLatFamily O x (fun c => (D c).kk τ i)) ∧ IsLatFamily O x (fun c => dotDual (chartRing O (mseg x) c) ((D c).lie τ)) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → IsLatFamily O x (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ IsLatFamily O x (fun c => (D c).imH (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a)))) := by
  classical
  intro O _ _ _ Ω _ _ K _ _ ι _ x _ F _ _ _ n Sg _ r s p _ w χ φ D hD
  have hl1 : IsLatFamily O x (fun c => (D c).l1 (chartRing O (mseg x) c) p) :=
    fam_sup hD.famM (fam_map (fam_std _) _ fun a v => smul_comm _ _ _)
  refine ⟨hl1, fun τ => ?_⟩
  obtain ⟨hlie, -, -, -, -, hDel, hTh⟩ := hD.fam τ
  have haf : IsLatFamily O x
      (fun c => (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) :=
    fam_comap hl1 _ fun a v => (linMap n (fun a => algebraMap O Ω (χ τ a))).map_smul a v
  refine ⟨haf, fun i => ⟨?_, ?_⟩, fun i => ?_, ?_, fun hG => ?_⟩
  · exact fam_comap (fam_sup hD.famM (fam_sub _)) _
      fun a v => (LinearMap.toSpanSingleton Ω _ _).map_smul a v
  · exact fam_comap (fam_sup hTh (fam_prod (fam_sub _) fam_bot)) _
      fun a v => Prod.ext ((LinearMap.toSpanSingleton Ω _ _).map_smul a v.1) rfl
  · exact fam_map (fam_inf hTh (fam_prod (fam_sub _) fam_top)) _ fun a v => rfl
  · exact fam_dual hlie fun c hc => fg_of_locFree ((hD.base c hc).free τ).1
  · have hh : IsLatFamily O x
        (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) := by
      refine fam_dual haf fun c hc => fg_comap (fg_of_locFree (hG c hc).l1) _
        (linMap_inj n _ ?_ ?_) ((hG c hc).lin τ)
      · simp [(hD.char.2.2.2.2 τ).1]
      · simp [(hD.char.2.2.2.2 τ).2]
    exact ⟨hh, fam_map (fam_inf hDel (fam_prod hh fam_top)) _ fun a v => rfl⟩
end
