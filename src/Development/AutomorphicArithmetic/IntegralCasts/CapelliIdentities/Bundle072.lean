module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle066
public import Mathlib.RingTheory.WittVector.Compare
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormSubgroupOpen
import Mathlib.Algebra.CharP.Subring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.Identities
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

section

open MvPolynomial in
private theorem UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_extension {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (R S : Type) [CommRing R] [Nontrivial R] [Algebra ℂ R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
    (π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R) (hπ : Function.Surjective π) (hJ : RingHom.ker π = J)
    (hinj : Function.Injective (algebraMap R S))
    (hfrac : ∀ s : S, ∃ a b : R, b ≠ 0 ∧ algebraMap R S b * s = algebraMap R S a) :
    Nonempty (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) := by
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := S)
  let φ : MvPolynomial (Fin n ⊕ Fin m) ℂ →+* S :=
    eval₂Hom ((algebraMap R S).comp (algebraMap ℂ R))
      (Sum.elim (fun i => algebraMap R S (π (X i))) s)
  have hcomp : φ.comp (rename Sum.inl :
      MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom
      = (algebraMap R S).comp π.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h : π (C r) = algebraMap ℂ R r := π.commutes r
      simp [φ, h]
    · intro i
      simp [φ]
  have hren : ∀ q, φ (rename Sum.inl q) = algebraMap R S (π q) := fun q =>
    RingHom.congr_fun hcomp q
  have hY : ∀ i, φ (X (Sum.inr i)) = s i := fun i => by simp [φ]
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : y ∈ Submodule.span R (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hy
    choose p hp using fun i => hπ (c i)
    refine ⟨∑ i, rename Sum.inl (p i) * X (Sum.inr i), ?_⟩

    simp only [map_sum, map_mul, hren, hY, hp, Algebra.smul_def]
  refine ⟨⟨m, RingHom.ker φ, RingHom.ker_isPrime _,
    IsIntegrallyClosed.of_equiv (RingHom.quotientKerEquivOfSurjective hsurj).symm, ?_, ?_, ?_⟩⟩
  · ext q
    rw [Ideal.mem_comap, RingHom.mem_ker, hren, ← hJ, RingHom.mem_ker,
      map_eq_zero_iff _ hinj]
  · intro i
    obtain ⟨Q, hQ, hQ0⟩ : IsIntegral R (s i) := Algebra.IsIntegral.isIntegral _
    obtain ⟨P, hP, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
      (f := π.toRingHom) (Polynomial.mem_lifts_of_surjective hπ Q) hQ
    refine ⟨P, hPm, ?_⟩
    rw [RingHom.mem_ker, Polynomial.hom_eval₂, hcomp, hY, ← Polynomial.eval₂_map, hP, hQ0]
  · intro i
    obtain ⟨a, b, hb, hab⟩ := hfrac (s i)
    obtain ⟨a, rfl⟩ := hπ a
    obtain ⟨b, rfl⟩ := hπ b
    refine ⟨a, b, ?_, ?_⟩
    · rw [← hJ, RingHom.mem_ker]
      exact hb
    · rw [RingHom.mem_ker, map_sub, map_mul, hren, hren, hY, hab, sub_self]

theorem UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_presentation :
    ∀ {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (R : Type) [inst : CommRing R] [IsDomain R] [inst_2 : Algebra ℂ R]
    (π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R),
    Function.Surjective (⇑π : MvPolynomial (Fin n) ℂ → R) →
      RingHom.ker π = J →
        Nonempty
          (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalModel
            J) := by
  intro n J R _ _ _ π hπ hJ
  haveI : Algebra.FiniteType ℂ R := Algebra.FiniteType.of_surjective π hπ
  haveI : Module.Finite R (integralClosure R (FractionRing R)) := UpperTheory.integralClosure_finite ℂ R (FractionRing R)
  haveI : IsIntegrallyClosed (integralClosure R (FractionRing R)) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
  refine UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_extension J R
    (integralClosure R (FractionRing R)) π hπ hJ ?_ ?_
  · intro x y hxy
    exact IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val hxy)
  · intro s
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) (s : FractionRing R)
    refine ⟨a, b, nonZeroDivisors.coe_ne_zero b, Subtype.ext ?_⟩
    rw [mul_comm] at hab
    exact hab
end

section

noncomputable def UpperTheory.Reformulated.B.RestrictAutomorphism.zlW :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → (R : Type) → [inst_1 : CommRing R] → [CharP R l] → ℤ_[l] →+* WittVector l R :=
    fun (l : ℕ) [Fact (Nat.Prime l)] (R : Type) [CommRing R] [CharP R l] ↦
      (WittVector.map (ZMod.castHom (dvd_refl l) R)).comp (WittVector.equiv l).symm.toRingHom

namespace UpperTheory.Reformulated.B.RestrictAutomorphism

private theorem hom_unique {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    (φ ψ : ℤ_[p] →+* WittVector p R) : φ = ψ := by
  ext1 x
  rw [← sub_eq_zero]
  ext i
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (i + 1) x)
  have hx : x = y * (p : ℤ_[p]) ^ (i + 1) + (x.appr (i + 1) : ℤ_[p]) := by
    rw [hy]; ring
  have h : φ x - ψ x = (φ y - ψ y) * (p : WittVector p R) ^ (i + 1) := by
    conv_lhs => rw [hx]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [h, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self i), WittVector.zero_coeff]

private theorem pow_pow_mul {p : ℕ} {R : Type} [CommRing R] {y : R} {m : ℕ}
    (h : y ^ p ^ m = y) (n : ℕ) : y ^ p ^ (m * n) = y := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

private def algPart (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p] : Subring R where
  carrier := {y | ∃ m : ℕ, 0 < m ∧ y ^ p ^ m = y}
  one_mem' := ⟨1, one_pos, one_pow _⟩
  zero_mem' := ⟨1, one_pos, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)⟩
  mul_mem' := by
    rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [mul_pow, pow_pow_mul ha, mul_comm m n, pow_pow_mul hb]
  add_mem' := by
    rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [add_pow_char_pow, pow_pow_mul ha, mul_comm m n, pow_pow_mul hb]
  neg_mem' := by
    rintro a ⟨m, hm, ha⟩
    refine ⟨m, hm, ?_⟩
    have h := map_neg (iterateFrobenius R p m) a
    rwa [iterateFrobenius_def, iterateFrobenius_def, ha] at h

private theorem map_mem_algPart {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    (σ : R ≃+* R) {y : R} (hy : y ∈ algPart p R) : σ y ∈ algPart p R := by
  obtain ⟨m, hm, h⟩ := hy
  exact ⟨m, hm, by rw [← map_pow, h]⟩

private def restrictAut (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    (σ : R ≃+* R) : algPart p R ≃+* algPart p R where
  toFun y := ⟨σ y, map_mem_algPart σ y.2⟩
  invFun y := ⟨σ.symm y, map_mem_algPart σ.symm y.2⟩
  left_inv y := Subtype.ext (σ.symm_apply_apply _)
  right_inv y := Subtype.ext (σ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul σ (a : R) b)
  map_add' a b := Subtype.ext (map_add σ (a : R) b)

private def restrictHom (p : ℕ) [Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R]
    [CharP R p] (ρ : G →* R ≃+* R) : G →* algPart p R ≃+* algPart p R where
  toFun g := restrictAut p (ρ g)
  map_one' := by
    ext y
    show ρ 1 (y : R) = y
    rw [map_one]; rfl
  map_mul' g h := by
    ext y
    show ρ (g * h) (y : R) = ρ g (ρ h y)
    rw [map_mul]; rfl

end UpperTheory.Reformulated.B.RestrictAutomorphism

theorem UpperTheory.Reformulated.B.RestrictAutomorphism.exists_alg :
    ∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {G : Type} [inst : Group G] {R : Type} [inst_1 : CommRing R] (ρ : G →* R ≃+* R)
      [inst_2 : TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [inst_6 : CharP R p],
      (∀ (y : R) (m : ℕ), (0 : ℕ) < m → y ^ p ^ m = y → ∀ᶠ (g : G) in nhds (1 : G), ((ρ : G → R ≃+* R) g : R → R) y = y) →
        ∀ {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]),
          Continuous (⇑M : G → Matrix (Fin r) (Fin r) ℤ_[p]) →
            (∀ (g : G),
                (∀ (m : ℕ), (0 : ℕ) < m → ∀ (y : R), y ^ p ^ m = y → ((ρ : G → R ≃+* R) g : R → R) y = y) →
                  (M : G → Matrix (Fin r) (Fin r) ℤ_[p]) g = (1 : Matrix (Fin r) (Fin r) ℤ_[p])) →
              ∃ (W : Matrix (Fin r) (Fin r) (WittVector p R)),
                IsUnit W.det ∧
                  (∀ (g : G),
                      ((M : G → Matrix (Fin r) (Fin r) ℤ_[p]) g).map (⇑(UpperTheory.Reformulated.B.RestrictAutomorphism.zlW p R) : ℤ_[p] → WittVector p R) *
                          W.map (⇑(WittVector.map ((ρ : G → R ≃+* R) g).toRingHom) : WittVector p R → WittVector p R) =
                        W) ∧
                    ∀ (i j : Fin r) (n : ℕ), ∃ (m : ℕ), (0 : ℕ) < m ∧ (W i j).coeff n ^ p ^ m = (W i j).coeff n := by
  intro p hp G _ R _ ρ _ _ _ _ _ hopen r M hM hker
  haveI : CharP (algPart p R) p := inferInstance
  obtain ⟨V, hV, hVeq⟩ := UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.exists_alg (p := p) (restrictHom p ρ)
    (fun y m hm hy => (hopen y m hm (by simpa using congrArg Subtype.val hy)).mono
      fun g hg => Subtype.ext hg)
    M hM
    (fun g hg => hker g fun m hm y hy =>
      congrArg Subtype.val (hg m hm ⟨y, m, hm, hy⟩ (Subtype.ext (by simpa using hy))))
  let ι : WittVector p (algPart p R) →+* WittVector p R := WittVector.map (algPart p R).subtype
  refine ⟨V.map ι, ?_, fun g => ?_, fun i j n => ?_⟩
  · have h := hV.map ι
    rwa [RingHom.map_det] at h
  · have h := congrArg (fun A => A.map ι) (hVeq g (restrictHom p ρ g).toRingHom fun _ _ _ _ => rfl)
    have h1 : (M g).map (zlW p R) =
        ((M g).map (UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.zlW p (algPart p R))).map ι := by
      rw [hom_unique (zlW p R) (ι.comp (UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.zlW p (algPart p R))),
        RingHom.coe_comp, Matrix.map_map]
    have h2 : (V.map ι).map (WittVector.map (ρ g).toRingHom) =
        (V.map (WittVector.map (restrictHom p ρ g).toRingHom)).map ι := by
      ext i j n
      simp only [Matrix.map_apply, ι, WittVector.map_coeff]
      rfl
    rw [h1, h2, ← Matrix.map_mul]
    exact h
  · simp only [Matrix.map_apply, ι, WittVector.map_coeff]
    exact ((V i j).coeff n).2
end

section

open AlgebraicGeometry CategoryTheory in
private lemma UpperTheory.Reformulated.B.RangeExtension.ext_aux {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    {A B : CommRingCat.{0}} (i : A ⟶ B) (hi : Function.Injective i.hom)
    (a b : Spec A ⟶ X) (ha : ∀ z, a z ∈ U) (hb : ∀ z, b z ∈ U)
    (h : Spec.map i ≫ a = Spec.map i ≫ b) : a = b := by
  have : IsAffine U.toScheme := hU
  have hr : ∀ c : Spec A ⟶ X, (∀ z, c z ∈ U) → Set.range c ⊆ Set.range U.ι := by
    intro c hc
    rintro _ ⟨z, rfl⟩
    simpa using hc z
  let a' := IsOpenImmersion.lift U.ι a (hr a ha)
  let b' := IsOpenImmersion.lift U.ι b (hr b hb)
  have ha' : a' ≫ U.ι = a := IsOpenImmersion.lift_fac _ _ _
  have hb' : b' ≫ U.ι = b := IsOpenImmersion.lift_fac _ _ _
  have h' : Spec.map i ≫ a' = Spec.map i ≫ b' := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, ha', hb', h]
  let s := Spec.preimage (a' ≫ U.toScheme.isoSpec.hom)
  let t := Spec.preimage (b' ≫ U.toScheme.isoSpec.hom)
  have hs : Spec.map s = a' ≫ U.toScheme.isoSpec.hom := Spec.map_preimage _
  have ht : Spec.map t = b' ≫ U.toScheme.isoSpec.hom := Spec.map_preimage _
  have h2 : s ≫ i = t ≫ i := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hs, ht, ← Category.assoc, ← Category.assoc, h']
  have hm : Mono i := ConcreteCategory.mono_of_injective i hi
  have h3 : s = t := (cancel_mono i).1 h2
  have h4 : a' = b' := by
    rw [← cancel_mono U.toScheme.isoSpec.hom, ← hs, ← ht, h3]
  rw [← ha', ← hb', h4]

open AlgebraicGeometry CategoryTheory in
private lemma UpperTheory.Reformulated.B.RangeExtension.finiteRing_sq_sub_mul_sq_eq_of_card {X : Scheme.{0}} {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {U : X.Opens}
    (hU : IsAffineOpen U) {R : Type} [CommRing R] (φ : R →+* Ω)
    (x : Spec (CommRingCat.of R) ⟶ X) (hx : Spec.map (CommRingCat.ofHom φ) ≫ x = ξ)
    (hxU : ∀ z, x z ∈ U) (p : X) (hp : ξ (IsLocalRing.closedPoint Ω) ⤳ p) (hpU : p ∈ U)
    (hinj : Function.Injective
      (X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ).hom)
    (hreg : ∀ a, φ a ∈ (X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ).hom.range) :
    p ∈ Set.range x := by
  have hi1 : Spec.map (X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ) ≫
      X.fromSpecStalk p = ξ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  generalize X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ = i at hinj hreg hi1
  let e : X.presheaf.stalk p ≃+* i.hom.range :=
    RingEquiv.ofBijective i.hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of R ⟶ X.presheaf.stalk p, g ≫ i = CommRingCat.ofHom φ := by
    refine ⟨CommRingCat.ofHom (e.symm.toRingHom.comp (φ.codRestrict i.hom.range hreg)), ?_⟩
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict i.hom.range hreg a))
  have hi2 : Spec.map i ≫ Spec.map g ≫ x = ξ := by
    rw [← Spec.map_comp_assoc, hg]
    exact hx
  have key : Spec.map g ≫ x = X.fromSpecStalk p := by
    refine UpperTheory.Reformulated.B.RangeExtension.ext_aux hU i hinj _ _ ?_ ?_ (hi2.trans hi1.symm)
    · intro z
      simpa using hxU _
    · intro z
      have hz : X.fromSpecStalk p z ∈ Set.range (X.fromSpecStalk p) := ⟨z, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hz
      exact Specializes.mem_open hz U.2 hpU
  have hmem : p ∈ Set.range (X.fromSpecStalk p) := ⟨_, Scheme.fromSpecStalk_closedPoint⟩
  rw [← key] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨Spec.map g z, by rw [← Scheme.Hom.comp_apply]; exact hz⟩

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar in
theorem UpperTheory.Reformulated.B.RangeExtension.mem_range
    {X : Scheme} {Ω : Type} [inst : Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} :
    IsCptGen ξ → ∀ {U : X.Opens}, IsAffineOpen U →
      ∀ {R : Type} [inst_1 : CommRing R] (φ : R →+* Ω) (x : Spec (@CommRingCat.of R inst_1) ⟶ X),
        Spec.map (CommRingCat.ofHom φ) ≫ x = ξ →
        (∀ z, x z ∈ U) → ∀ q : Cpt ξ, q.1 ∈ U →
        (∀ a : R, φ a ∈ regAt ξ q) → q.1 ∈ Set.range x := by
  intro hξ U hU R _ φ x hx hxU q hqU hreg
  exact UpperTheory.Reformulated.B.RangeExtension.finiteRing_sq_sub_mul_sq_eq_of_card
    hU φ x hx hxU q.1 q.2 hqU (hξ.inj q) hreg
end

section

private theorem UpperTheory.Reformulated.B.Uc15.exists_nsmul_integral {E : Type} [Field E] [NumberField E]
    (a : E) : ∃ M : ℕ, M ≠ 0 ∧ ∃ b : NumberField.RingOfIntegers E, (b : E) = (M : E) * a := by
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  have h2 : IsIntegral ℤ (y • (y • a)) := hint.smul y
  refine ⟨(y * y).natAbs, Int.natAbs_ne_zero.mpr (mul_ne_zero hy hy), ⟨y • (y • a), h2⟩, ?_⟩
  have h3 : (((y * y).natAbs : ℕ) : E) = ((y * y : ℤ) : E) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg y)]
  rw [h3]
  change y • (y • a) = _
  rw [smul_smul, zsmul_eq_mul]

theorem UpperTheory.Reformulated.B.Uc15.exists_nsmul_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ}
      (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (u : Fin r → E), ∃ (N : ℕ), N ≠ (0 : ℕ) ∧ N • u ∈ X.Λ := by
  intro E _ _ _ r X u
  have hu : u ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by
    rw [X.Λ_span]; exact Submodule.mem_top
  induction hu using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_nsmul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_nsmul]; exact X.Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, hM, hx⟩ := hx
    obtain ⟨N, hN, hy⟩ := hy
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    rw [nsmul_add]
    refine X.Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx N
    · rw [mul_smul]; exact nsmul_mem hy M
  | smul a x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, b, hb⟩ := UpperTheory.Reformulated.B.Uc15.exists_nsmul_integral a
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have h : (M * N) • a • x = b • (N • x) := by
      funext i
      change (M * N) • (a * x i) = (b : E) * (N • x i)
      rw [hb, nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rw [h]
    exact X.Λ.smul_mem b hx
end

section

theorem UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ}
      (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (w : Fin r → E),
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • w ∈ X.Λ := by
  intro E _ _ _ r X w
  have hw : w ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by
    rw [X.Λ_span]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact X.Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine X.Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact X.Λ.smul_mem b hax
    · rw [mul_smul]; exact X.Λ.smul_mem a hby
  | smul t x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) t
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap (NumberField.RingOfIntegers E) E q ≠ 0 := by
      simpa using hq0
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have key : (a * q) • ((algebraMap (NumberField.RingOfIntegers E) E p /
        algebraMap (NumberField.RingOfIntegers E) E q) • x) = p • (a • x) := by
      ext i
      simp only [Pi.smul_apply]
      simp only [Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply]
      field_simp
    rw [key]
    exact X.Λ.smul_mem p hax
end

section

theorem UpperTheory.Reformulated.B.Ga5b.exists_nat_smul_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] {N : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E N) (v : Fin N → E),
    ∃ (n : ℕ),
      (0 : ℕ) < n ∧
        (↑n : E) • v ∈
          X.Λ := by
  intro E _ _ _ N X v
  refine Submodule.span_induction (fun x hx => ⟨1, one_pos, by simpa using hx⟩) ⟨1, one_pos, by simp⟩
    ?_ ?_ (X.Λ_span ▸ Submodule.mem_top : v ∈ Submodule.span E (X.Λ : Set (Fin N → E)))
  · rintro x y - - ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_pos ha hb, ?_⟩
    convert X.Λ.add_mem (nsmul_mem hx b) (nsmul_mem hy a) using 1
    ext i; simp; ring
  · rintro c x - ⟨a, ha, hx⟩
    obtain ⟨m, s, hm, hs⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (.of_finite ℚ c)).exists_nsmul_eq (NumberField.RingOfIntegers E)
    refine ⟨m * a, mul_pos (Nat.pos_of_ne_zero hm) ha, ?_⟩
    convert X.Λ.smul_mem s hx using 1
    rw [← algebraMap_smul E s, ← hs]; ext i; simp; ring
end
