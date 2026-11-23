module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Mathlib.Algebra.DualNumber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle039
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle239
public import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Algebra.CharP.Reduced
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.Ord.RootBuild

variable {p : ℕ} [hp : Fact p.Prime] {X Y : Scheme.{0}} [IsReduced X]

private theorem pow_inj (h : (p : Γ(X, ⊤)) = 0) (U : X.Opens) {a b : Γ(X, U)} (e : a ^ p = b ^ p) :
    a = b := by
  have hU := GlobalTheory.SS.FrobField.cast_zero h U
  have hs := map_sub (GlobalTheory.SS.FrobField.powHom Γ(X, U) p 1 hp.out hU) a b
  have e2 : (a - b) ^ p = 0 := by
    simpa [GlobalTheory.SS.FrobField.powHom, e] using hs
  exact sub_eq_zero.mp (IsReduced.eq_zero _ ⟨p, e2⟩)

variable (ψ : X ⟶ Y)
  (H : ∀ (U : Y.Opens) (s : Γ(Y, U)), ∃ r : Γ(X, ψ ⁻¹ᵁ U), r ^ p = ψ.app U s)

private def rt (U : Y.Opens) (s : Γ(Y, U)) : Γ(X, ψ ⁻¹ᵁ U) := (H U s).choose

private theorem rt_pow (U : Y.Opens) (s : Γ(Y, U)) : rt ψ H U s ^ p = ψ.app U s := (H U s).choose_spec

private def rtHom (h : (p : Γ(X, ⊤)) = 0) (U : Y.Opens) : Γ(Y, U) →+* Γ(X, ψ ⁻¹ᵁ U) where
  toFun := rt ψ H U
  map_one' := pow_inj h _ (by rw [rt_pow, map_one, one_pow])
  map_mul' a b := pow_inj h _ (by rw [mul_pow, rt_pow, rt_pow, rt_pow, map_mul])
  map_zero' := pow_inj h _ (by rw [rt_pow, map_zero, zero_pow hp.out.ne_zero])
  map_add' a b := pow_inj h _ (by
    have hU := GlobalTheory.SS.FrobField.cast_zero h (ψ ⁻¹ᵁ U)
    have := map_add (GlobalTheory.SS.FrobField.powHom Γ(X, ψ ⁻¹ᵁ U) p 1 hp.out hU) (rt ψ H U a) (rt ψ H U b)
    have e : (rt ψ H U a + rt ψ H U b) ^ p = rt ψ H U a ^ p + rt ψ H U b ^ p := by
      simpa [GlobalTheory.SS.FrobField.powHom] using this
    rw [e, rt_pow, rt_pow, rt_pow, map_add (f := _)])

private def rootPre (h : (p : Γ(X, ⊤)) = 0) : X.toPresheafedSpace.Hom Y.toPresheafedSpace where
  base := ψ.base
  c := { app := fun U => CommRingCat.ofHom (rtHom ψ H h U.unop)
         naturality := fun U V i => by
           ext s
           refine pow_inj h _ ?_
           have e := congrArg (fun φ => φ.hom s) (ψ.naturality i)
           show (rt ψ H V.unop ((Y.presheaf.map i).hom s)) ^ p =
             ((X.presheaf.map ((TopologicalSpace.Opens.map ψ.base).map i.unop).op).hom (rt ψ H U.unop s)) ^ p
           rw [rt_pow, ← map_pow, rt_pow]
           exact e }

private def rootMor (h : (p : Γ(X, ⊤)) = 0) : X ⟶ Y :=
  ⟨⟨rootPre ψ H h, fun x => ⟨fun a ha => by
    obtain ⟨U, hU, s, rfl⟩ := Y.presheaf.exists_germ_eq (x := ψ.base x) a
    have e := PresheafedSpace.stalkMap_germ_apply (rootPre ψ H h) U x hU s
    erw [e] at ha
    have ha' : IsUnit ((X.presheaf.germ (ψ ⁻¹ᵁ U) x hU).hom (rt ψ H U s)) := ha
    have e2 : (X.presheaf.germ (ψ ⁻¹ᵁ U) x hU).hom (ψ.app U s) =
        (X.presheaf.germ (ψ ⁻¹ᵁ U) x hU).hom (rt ψ H U s) ^ p := by
      rw [← rt_pow ψ H U s, map_pow]
    have hu : IsUnit ((X.presheaf.germ (ψ ⁻¹ᵁ U) x hU).hom (ψ.app U s)) := e2 ▸ ha'.pow p
    have e3 := Scheme.Hom.germ_stalkMap_apply ψ U x hU s
    rw [← e3] at hu
    exact isUnit_of_map_unit (ψ.stalkMap x).hom _ hu⟩⟩⟩

private theorem frob_rootMor (h : (p : Γ(X, ⊤)) = 0) : GlobalTheory.VB.frob X p h ≫ rootMor ψ H h = ψ := by
  refine Scheme.Hom.ext rfl ?_
  intro U
  erw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  ext s
  have e := GlobalTheory.VB.frob_app p h (rootMor ψ H h ⁻¹ᵁ U) (rt ψ H U s)
  refine Eq.trans ?_ (rt_pow ψ H U s)
  exact e

end UpperTheory.Gal.Ord.RootBuild

theorem UpperTheory.Gal.Ord.root0 :
    ∀ (p : ℕ) [Fact p.Prime] (X Y : Scheme.{0}) [IsReduced X] (h : (p : Γ(X, ⊤)) = 0) (ψ : X ⟶ Y),
      (∀ (U : Y.Opens) (s : Γ(Y, U)), ∃ r : Γ(X, ψ ⁻¹ᵁ U), r ^ p = ψ.app U s) → ∃ ψ' : X ⟶ Y, GlobalTheory.VB.frob X p h ≫ ψ' = ψ :=
  fun _ _ _ _ _ h ψ H => ⟨UpperTheory.Gal.Ord.RootBuild.rootMor ψ H h, UpperTheory.Gal.Ord.RootBuild.frob_rootMor ψ H h⟩

end
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem exists_functional_ne_zero_projective {B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
    [Module.Projective B M] {m : M} (hm : m ≠ 0) : ∃ l : M →ₗ[B] B, l m ≠ 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective B M)
  by_contra hall
  push_neg at hall
  apply hm
  have h0 : s m = 0 := by
    ext a
    simpa using hall (Finsupp.lapply a ∘ₗ s)
  have := LinearMap.congr_fun hs m
  simpa [h0] using this.symm

private theorem exists_point_nonvanishing_reduced (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] [IsReduced B] {c : B} (hc : c ≠ 0) :
    ∃ x : B →ₐ[k] k, x c ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.NonvanishingPoint.exists_point_nonvanishing_reduced k B hc

theorem UpperTheory.Gal.Ord.dz1 :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B] [Module.Projective B Ω[B⁄k]] (r : B),
      (∀ v : B →ₐ[k] DualNumber k, TrivSqZeroExt.snd (v r) = 0) → KaehlerDifferential.D k B r = 0 := by
  intro k _ _ B _ _ _ _ _ r hv
  by_contra hne
  obtain ⟨l, hl⟩ := exists_functional_ne_zero_projective (B := B) hne
  obtain ⟨x, hx⟩ := exists_point_nonvanishing_reduced k B hl
  let d : B →ₗ[k] k := x.toLinearMap ∘ₗ (l.restrictScalars k) ∘ₗ (KaehlerDifferential.D k B).toLinearMap
  have hd : ∀ b, d b = x (l (KaehlerDifferential.D k B b)) := fun _ => rfl
  let f : B →ₗ[k] DualNumber k :=
    Algebra.linearMap k (DualNumber k) ∘ₗ x.toLinearMap + TrivSqZeroExt.inrHom k k ∘ₗ d
  have hal : ∀ c : k, algebraMap k (DualNumber k) c = TrivSqZeroExt.inl c := fun _ => rfl
  have hfst : ∀ b, TrivSqZeroExt.fst (f b) = x b := fun b => by simp [f, hal]
  have hsnd : ∀ b, TrivSqZeroExt.snd (f b) = d b := fun b => by simp [f, hal]
  let v : B →ₐ[k] DualNumber k := AlgHom.ofLinearMap f
    (by
      apply TrivSqZeroExt.ext
      · simp [hfst]
      · simp [hsnd, hd])
    (by
      intro a b
      apply TrivSqZeroExt.ext
      · simp [hfst]
      · simp [hfst, hsnd, hd, Derivation.leibniz, mul_comm, add_comm])
  apply hx
  have := hv v
  simpa [v, hsnd, hd] using this
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

private theorem radical_quot (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (m : Ideal R) [m.IsMaximal] : (m.map (algebraMap R B)).IsRadical := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : _root_.IsReduced ((R ⧸ m) ⊗[R] B) := GlobalTheory.T.isReduced_of_smooth_over_field' (R ⧸ m) _
  have e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B m
  haveI : _root_.IsReduced (B ⧸ m.map (algebraMap R B)) :=
    isReduced_of_injective e.toRingEquiv.toRingHom e.injective
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr this

private theorem radical_loc (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (M : Submonoid B)
    [IsLocalization M A] (I : Ideal B) (hI : I.IsRadical) : (I.map (algebraMap B A)).IsRadical := by
  intro a ⟨n, hn⟩
  have hn' : a ^ (n + 1) ∈ I.map (algebraMap B A) := by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ hn
  obtain ⟨b, u, rfl⟩ := IsLocalization.exists_mk'_eq M a
  obtain ⟨⟨i, t⟩, ht⟩ := (IsLocalization.mem_map_algebraMap_iff M A).mp hn'
  have hu : IsLocalization.mk' A b u * algebraMap B A u = algebraMap B A b := IsLocalization.mk'_spec A b u
  have e1 : algebraMap B A (b ^ (n + 1) * t) = algebraMap B A (i * u ^ (n + 1)) := by
    simp only [map_mul, map_pow]
    rw [← ht, ← hu]
    ring
  obtain ⟨d, hd⟩ := IsLocalization.exists_of_eq (M := M) e1
  have hy : (d : B) * t * b ∈ I := by
    apply hI
    refine ⟨n + 1, ?_⟩
    have e2 : ((d : B) * t * b) ^ (n + 1) = ((d : B) * t) ^ n * ((d : B) * (b ^ (n + 1) * t)) := by ring
    rw [e2, hd]
    exact I.mul_mem_left _ (I.mul_mem_left _ (I.mul_mem_right _ i.2))
  refine (IsLocalization.mem_map_algebraMap_iff M A).mpr
    ⟨⟨⟨_, hy⟩, u * d * t⟩, ?_⟩
  simp only [Submonoid.coe_mul, map_mul]
  rw [← hu]
  ring

private theorem radical_stalk (R : Type) [CommRing R] (m : Ideal R) [m.IsMaximal] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of R)) [Smooth s] (z : X) (r : CommRingCat.of R ⟶ X.presheaf.stalk z)
    (hr : Spec.map r = X.fromSpecStalk z ≫ s) : (m.map r.hom).IsRadical := by
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (x := z) (U := ⊤) trivial
  have hsm : Smooth (hU.fromSpec ≫ s) := inferInstance
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (hU.fromSpec ≫ s)
  have hρs : ρ.hom.Smooth := by
    rw [← hρ] at hsm
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm
  have e : r = ρ ≫ X.presheaf.germ U z hzU := by
    apply Spec.map_injective
    rw [hr, Spec.map_comp, hρ, ← hU.fromSpecStalk_eq_fromSpecStalk hzU]
    simp [IsAffineOpen.fromSpecStalk]
  letI := ρ.hom.toAlgebra
  haveI : Algebra.Smooth R Γ(X, U) := hρs
  have h1 := radical_quot R Γ(X, U) m
  letI : Algebra Γ(X, U) (X.presheaf.stalk z) := (X.presheaf.germ U z hzU).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨z, hzU⟩
  have h2 := radical_loc Γ(X, U) (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl _ h1
  rw [Ideal.map_map] at h2
  rw [e]
  exact h2

private theorem kills_max (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of R)) [Smooth s] (z : X)
    (hmax : ∀ z' : X, s.base z' = IsLocalRing.closedPoint R → z' ⤳ z → z' = z)
    (T : Type) [CommRing T] (φ : X.presheaf.stalk z ⟶ CommRingCat.of T) (c : R →+* T)
    (h : Spec.map φ ≫ X.fromSpecStalk z ≫ s = Spec.map (CommRingCat.ofHom c))
    (hc : ∀ x ∈ IsLocalRing.maximalIdeal R, c x = 0) :
    ∀ x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z), φ.hom x = 0 := by
  obtain ⟨r, hr⟩ := Spec.map_surjective (X.fromSpecStalk z ≫ s)
  have hrc : r ≫ φ = CommRingCat.ofHom c := by
    apply Spec.map_injective
    rw [Spec.map_comp, hr, h]
  have hrad := radical_stalk R (IsLocalRing.maximalIdeal R) X s z r hr
  have hprime : ∀ P : Ideal (X.presheaf.stalk z), P.IsPrime →
      (IsLocalRing.maximalIdeal R).map r.hom ≤ P → P = IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    intro P hP hJ
    let y : Spec (X.presheaf.stalk z) := ⟨P, hP⟩
    have h1 : X.fromSpecStalk z y ⤳ z := by
      have : X.fromSpecStalk z y ∈ Set.range (X.fromSpecStalk z) := ⟨y, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have h2 : s.base (X.fromSpecStalk z y) = IsLocalRing.closedPoint R := by
      have e : s.base (X.fromSpecStalk z y) = (Spec.map r).base y := by rw [hr]; rfl
      rw [e]
      apply PrimeSpectrum.ext
      have hle : IsLocalRing.maximalIdeal R ≤ P.comap r.hom := Ideal.map_le_iff_le_comap.mp hJ
      exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.comap r.hom).ne_top hle).symm
    have h3 := hmax _ h2 h1
    have h4 : y = IsLocalRing.closedPoint (X.presheaf.stalk z) :=
      (X.fromSpecStalk z).isEmbedding.injective (h3.trans Scheme.fromSpecStalk_closedPoint.symm)
    exact congrArg PrimeSpectrum.asIdeal h4
  intro x hx
  have hxJ : x ∈ (IsLocalRing.maximalIdeal R).map r.hom := by
    apply hrad
    rw [Ideal.radical_eq_sInf]
    refine Ideal.mem_sInf.mpr fun {P} hP => ?_
    rw [hprime P hP.2 hP.1]
    exact hx
  have hker : (IsLocalRing.maximalIdeal R).map r.hom ≤ RingHom.ker φ.hom := by
    refine Ideal.map_le_iff_le_comap.mpr fun y hy => ?_
    have e : φ.hom (r.hom y) = c y := congrArg (fun f => f.hom y) hrc
    exact (RingHom.mem_ker).mpr (e.trans (hc y hy))
  exact hker hxJ

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.gen :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) [Smooth s] (z : X), s.base z = IsLocalRing.closedPoint R →
      (∀ z' : X, s.base z' = IsLocalRing.closedPoint R → z' ⤳ z → z' = z) → ∀ (T : Type) [CommRing T] [IsLocalRing T] (v : Sp T ⟶ X) (c : R →+* T),
      v.base (IsLocalRing.closedPoint T) = z → v ≫ s = spMap c → (∀ x ∈ IsLocalRing.maximalIdeal R, c x = 0) →
      ∃ τ : X.residueField z →+* T, spMap τ ≫ X.fromSpecResidueField z = v := by
  intro R _ _ _ X s _ z _ hmax T _ _ v c hv hvs hc
  subst hv
  have hφ : Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v) ≫ X.fromSpecStalk _ = v :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of T) v
  have hk := kills_max R X s _ hmax T (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v) c
    (by rw [← Category.assoc, hφ]; exact hvs) hc
  refine ⟨Ideal.Quotient.lift _ (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v).hom hk, ?_⟩
  have e : X.residue _ ≫ CommRingCat.ofHom (Ideal.Quotient.lift _ (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v).hom hk) =
      Scheme.stalkClosedPointTo (R := CommRingCat.of T) v := by
    ext x
    rfl
  show Spec.map _ ≫ Spec.map (X.residue _) ≫ X.fromSpecStalk _ = v
  rw [← Spec.map_comp_assoc]
  exact (congrArg (fun g => Spec.map g ≫ X.fromSpecStalk _) e).trans hφ
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private lemma rootGlue_uniq {R : Type*} [CommRing R] [IsReduced R] {p : ℕ} (hp : p.Prime)
    (h : (p : R) = 0) {a b : R} (hab : a ^ p = b ^ p) : a = b := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim a b
  · haveI : CharP R p := (CharP.charP_iff_prime_eq_zero hp).mpr h
    haveI : Fact p.Prime := ⟨hp⟩
    apply frobenius_inj R p
    simpa [frobenius_def] using hab

theorem UpperTheory.Gal.Ord.rootGlue :
    ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsReduced X], (p : Γ(X, ⊤)) = 0 → ∀ (U : X.Opens) (s : Γ(X, U)),
      (∀ (V : X.Opens) (hV : V ≤ U), IsAffineOpen V → ∃ r : Γ(X, V), r ^ p = X.presheaf.map (homOfLE hV).op s) → ∃ r : Γ(X, U), r ^ p = s := by
  intro p _ X _ hp U s hloc
  have hpr : p.Prime := Fact.out
  have hpV : ∀ V : X.Opens, (p : Γ(X, V)) = 0 := by
    intro V
    have h0 := congrArg (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) hp
    rwa [map_natCast, map_zero] at h0
  let Idx := {V : X.Opens // V ≤ U ∧ IsAffineOpen V}
  choose r hr using fun i : Idx => hloc i.1 i.2.1 i.2.2
  have hcover : U ≤ ⨆ i : Idx, i.1 := by
    intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVU, hV⟩, hxV⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.obj (fun i : Idx => i.1) r := by
    intro i j
    apply rootGlue_uniq hpr (hpV _)
    change (X.presheaf.map _ (r i)) ^ p = (X.presheaf.map _ (r j)) ^ p
    rw [← map_pow, ← map_pow, hr i, hr j, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  obtain ⟨t, ht, -⟩ : ∃! t : Γ(X, U), ∀ i : Idx, X.presheaf.map (homOfLE i.2.1).op t = r i :=
    X.sheaf.existsUnique_gluing' (fun i : Idx => i.1) U (fun i => homOfLE i.2.1) hcover r hcomp
  refine ⟨t, ?_⟩
  have key : ∀ i : Idx,
      X.presheaf.map (homOfLE i.2.1).op (t ^ p) = X.presheaf.map (homOfLE i.2.1).op s := by
    intro i
    rw [map_pow, ht i, hr i]
  exact X.sheaf.eq_of_locally_eq' (fun i : Idx => i.1) U (fun i => homOfLE i.2.1) hcover _ _ key
end
