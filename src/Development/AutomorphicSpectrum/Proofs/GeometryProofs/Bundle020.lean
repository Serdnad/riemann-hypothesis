module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.Tan

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieEx

section Alg

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (ε : B →ₐ[R] R)

def augPart (f : B) : RingHom.ker ε :=
  ⟨f - algebraMap R B (ε f), by simp [RingHom.mem_ker]⟩

theorem augPart_coe (f : B) : ((augPart ε f : RingHom.ker ε) : B) = f - algebraMap R B (ε f) := rfl

theorem augPart_of_mem (f : RingHom.ker ε) : augPart ε f.1 = f := by
  apply Subtype.ext
  rw [augPart_coe, RingHom.mem_ker.mp f.2, map_zero, sub_zero]

theorem augPart_add (f g : B) : augPart ε (f + g) = augPart ε f + augPart ε g := by
  apply Subtype.ext
  simp only [Submodule.coe_add, augPart_coe, map_add (f := _)]
  abel

theorem augPart_smul (r : R) (f : B) : (RingHom.ker ε).toCotangent (augPart ε (r • f)) =
    r • (RingHom.ker ε).toCotangent (augPart ε f) := by
  have h : augPart ε (r • f) = algebraMap R B r • augPart ε f := by
    apply Subtype.ext
    have hr : algebraMap R R r = r := rfl
    simp only [Submodule.coe_smul, augPart_coe, smul_eq_mul, Algebra.smul_def, map_mul,
      AlgHom.commutes, hr]
    ring
  rw [h, map_smul, algebraMap_smul]

theorem augPart_mul (f g : B) : (RingHom.ker ε).toCotangent (augPart ε (f * g)) =
    (ε f) • (RingHom.ker ε).toCotangent (augPart ε g) + (ε g) • (RingHom.ker ε).toCotangent (augPart ε f) := by
  have hab : ((augPart ε f : B) * (augPart ε g : B)) ∈ RingHom.ker ε :=
    Ideal.mul_mem_left _ _ (augPart ε g).2
  have hdec : augPart ε (f * g) =
      ⟨(augPart ε f : B) * (augPart ε g : B), hab⟩ + algebraMap R B (ε f) • augPart ε g +
        algebraMap R B (ε g) • augPart ε f := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul, augPart_coe, smul_eq_mul, map_mul]
    ring
  have h0 : (RingHom.ker ε).toCotangent ⟨(augPart ε f : B) * (augPart ε g : B), hab⟩ = 0 := by
    rw [Ideal.toCotangent_eq_zero, pow_two]
    exact Ideal.mul_mem_mul (augPart ε f).2 (augPart ε g).2
  rw [hdec, map_add (f := _), map_add (f := _), h0, zero_add, map_smul, map_smul, algebraMap_smul, algebraMap_smul]

variable {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

def derRing (ψ : (RingHom.ker ε).Cotangent →ₗ[R] V) : B →ₐ[R] TrivSqZeroExt R V :=
  AlgHom.ofLinearMap
    { toFun := fun f => TrivSqZeroExt.inl (ε f) + TrivSqZeroExt.inr (ψ ((RingHom.ker ε).toCotangent (augPart ε f)))
      map_add' := fun f g => by
        rw [augPart_add, map_add (f := _), map_add (f := _), map_add (f := _)]
        ext <;> simp <;> abel
      map_smul' := fun r f => by
        rw [augPart_smul, map_smul]
        ext <;> simp }
    (by
      have : augPart ε (1 : B) = 0 := by
        apply Subtype.ext
        simp [augPart_coe]
      simp [this])
    (fun f g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [augPart_mul, map_add (f := _), map_smul, map_smul]
      ext <;> simp [add_comm])

theorem derRing_apply (ψ : (RingHom.ker ε).Cotangent →ₗ[R] V) (f : B) : derRing ε ψ f =
    TrivSqZeroExt.inl (ε f) + TrivSqZeroExt.inr (ψ ((RingHom.ker ε).toCotangent (augPart ε f))) := rfl

theorem derRing_of_mem (ψ : (RingHom.ker ε).Cotangent →ₗ[R] V) (f : RingHom.ker ε) :
    derRing ε ψ f.1 = TrivSqZeroExt.inr (ψ ((RingHom.ker ε).toCotangent f)) := by
  rw [derRing_apply, augPart_of_mem, RingHom.mem_ker.mp f.2]
  simp

theorem derRing_injective {ψ ψ' : (RingHom.ker ε).Cotangent →ₗ[R] V} (h : derRing ε ψ = derRing ε ψ') : ψ = ψ' := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker ε) x
  have hy := congrArg TrivSqZeroExt.snd (DFunLike.congr_fun h y.1)
  simpa [derRing_of_mem] using hy

end Alg

section Op
variable (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V]

abbrev opMod : Module Rᵐᵒᵖ V := Module.compHom V ((RingHom.id R).fromOpposite fun _ _ => mul_comm _ _)

theorem opCentral : @IsCentralScalar R V _ (opMod R V).toSMul := by
  exact @IsCentralScalar.mk R V _ (opMod R V).toSMul (fun _ _ => rfl)
end Op

section Red
variable {R : Type} [CommRing R] (I : Ideal R)

def kap : TrivSqZeroExt R (R ⧸ I) →ₐ[R] DualNumber (R ⧸ I) where
  toFun a := TrivSqZeroExt.inl (Ideal.Quotient.mk I a.fst) + TrivSqZeroExt.inr a.snd
  map_one' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_zero' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' a b := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [TrivSqZeroExt.snd_mul, Algebra.smul_def, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
  commutes' r := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem kap_inr (q : R ⧸ I) : kap I (TrivSqZeroExt.inr q) = TrivSqZeroExt.inr q := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [kap]

theorem kap_algebraMap (r : R) : kap I (algebraMap R _ r) = algebraMap (R ⧸ I) (DualNumber (R ⧸ I)) (Ideal.Quotient.mk I r) := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [kap, TrivSqZeroExt.algebraMap_eq_inl']

theorem kap_map (a : DualNumber R) : kap I (TrivSqZeroExt.map (Ideal.Quotient.mkₐ R I).toLinearMap a) =
    dualMap (Ideal.Quotient.mk I) a := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [kap, dualMap]
end Red

section Rel

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]
  {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

abbrev ev1 (Γ : QFGroup R T) : Γ.btOrder ⊤ →ₐ[R] R := evalAt (Γ.btOrder ⊤) 1

def TanRel (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} {x : Spec (CommRingCat.of R) ⟶ S} (i : Γ.G.left ⟶ G.left)
    (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))) (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V) (v : ob x V ⟶ G) : Prop :=
  ∃ y : Spec (CommRingCat.of (TrivSqZeroExt R V)) ⟶ Γ.G.left,
    y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) ∧
    y ≫ j = Spec.map (CommRingCat.ofHom (derRing (ev1 Γ) ψ).toRingHom) ∧
    y ≫ i = v.left

end Rel

end GlobalTheory.CompanionTheory.Ar.BT.Tan
end
end

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.SecAlg

theorem locFree_and_extend : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (Q : Type) (reg : Q → Subring Ω) (r : ℕ) (Λ : Q → AddSubgroup (Fin r → Ω)), (∀ q, IsLocalRing (reg q)) → (∀ q, ∀ a ∈ R, a ∈ reg q) → (∀ P : Ideal R, P.IsPrime → ∃ q, ∀ s : R, s ∉ P ↔ ((s : Ω) ≠ 0 ∧ (s : Ω)⁻¹ ∈ reg q)) → (∀ q, ∀ a ∈ reg q, ∃ s ∈ R, s ≠ 0 ∧ s⁻¹ ∈ reg q ∧ s * a ∈ R) → (∀ q, ∃ g ∈ R, g ≠ 0 ∧ g⁻¹ ∈ reg q ∧ ∃ f : Fin r → (Fin r → Ω), LinearIndependent Ω f ∧ ∀ q', g⁻¹ ∈ reg q' → ∀ e, e ∈ Λ q' ↔ ∃ a : Fin r → Ω, (∀ i, a i ∈ reg q') ∧ e = ∑ i, a i • f i) → LocFree R r (⨅ q, Λ q) ∧ ∀ g ∈ R, ∀ e : Fin r → Ω, (∀ q, g ≠ 0 → g⁻¹ ∈ reg q → e ∈ Λ q) → ∃ n : ℕ, g ^ n • e ∈ ⨅ q, Λ q :=
  @PositivityTheory.Xgn.lattice_section_algebra

end GlobalTheory.CompanionTheory.Ar.Num.SecAlg
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem valAt_scalar {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}} (π : X ⟶ Spec (CommRingCat.of A))
    (x : Spec (CommRingCat.of B) ⟶ X) (φ : A →+* B) (hw : x ≫ π = Spec.map (CommRingCat.ofHom φ))
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (hU : U ≤ π ⁻¹ᵁ ⊤) (b : A) :
    valAt x U h (π.appLE ⊤ U hU ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b)) = φ b := by
  have h1 := Scheme.Hom.appLE_comp_appLE x π ⊤ U ⊤ hU h
  have h0 : ∀ (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (e : ⊤ ≤ q ⁻¹ᵁ ⊤),
      q = Spec.map (CommRingCat.ofHom φ) →
      q.appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ := by
    rintro q e rfl
    have : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e = (Spec.map (CommRingCat.ofHom φ)).appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [this]
    exact Scheme.ΓSpecIso_naturality _
  have h2 : (π.appLE ⊤ U hU ≫ x.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ := by
    rw [h1]
    exact h0 _ _ hw
  have h3 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b)) h2
  simpa [valAt] using h3

theorem QFGroup.regularAt_scalar_mul (Γ : QFGroup R T) {f : T → FractionRing R} {g : Γ.G.left} (b : R)
    (H : Γ.RegularAt f g) : Γ.RegularAt (fun t => algebraMap R (FractionRing R) b * f t) g := by
  obtain ⟨U, hg, s, hs⟩ := H
  obtain ⟨π, hπ⟩ : ∃ π : Γ.G.left ⟶ Spec (CommRingCat.of R), π = Γ.G.hom := ⟨_, rfl⟩
  have hU : U ≤ π ⁻¹ᵁ ⊤ := fun _ _ => trivial
  refine ⟨U, hg, π.appLE ⊤ U hU ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * s, fun t h => ?_⟩
  have hw : (Γ.pt t).left ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
    rw [hπ]; exact Over.w (Γ.pt t)
  have h1 := valAt_scalar π (Γ.pt t).left (algebraMap R (FractionRing R)) hw U h hU b
  have h2 := hs t h
  show _ = algebraMap R (FractionRing R) b * f t
  rw [← h1, ← h2]
  simp [valAt, map_mul]

theorem QFGroup.compactSpace (Γ : QFGroup R T) : CompactSpace Γ.G.left := by
  obtain ⟨π, hπ⟩ : ∃ π : Γ.G.left ⟶ Spec (CommRingCat.of R), π = Γ.G.hom := ⟨_, rfl⟩
  have : QuasiCompact π := hπ ▸ Γ.quasiCompact
  exact QuasiCompact.compactSpace_of_compactSpace π

theorem QFGroup.exists_denom [Finite T] (Γ : QFGroup R T) (f : T → FractionRing R) :
    ∃ d : R, d ≠ 0 ∧ ∀ g, Γ.RegularAt (fun t => algebraMap R (FractionRing R) d * f t) g := by
  classical
  have := Γ.compactSpace
  have key : ∀ g : Γ.G.left, ∃ d : R, d ≠ 0 ∧ ∃ U : Γ.G.left.Opens, g ∈ U ∧
      ∀ g' ∈ U, Γ.RegularAt (fun t => algebraMap R (FractionRing R) d * f t) g' := by
    intro g
    have hreg : ∃ d : R, d ≠ 0 ∧ Γ.RegularAt (fun t => algebraMap R (FractionRing R) d * f t) g :=
      RegDenom.exists_denom_regularAt R T Γ f g
    obtain ⟨d, hd, U, hg, s, hs⟩ := hreg
    exact ⟨d, hd, U, hg, fun g' hg' => ⟨U, hg', s, hs⟩⟩
  choose d hd U hgU hU using key
  obtain ⟨F, hF⟩ := CompactSpace.elim_nhds_subcover (fun g => (U g : Set Γ.G.left))
    (fun g => (U g).isOpen.mem_nhds (hgU g))
  refine ⟨∏ x ∈ F, d x, Finset.prod_ne_zero_iff.2 fun x _ => hd x, fun g => ?_⟩
  have hg : g ∈ ⋃ x ∈ F, (U x : Set Γ.G.left) := by rw [hF]; trivial
  simp only [Set.mem_iUnion] at hg
  obtain ⟨x, hx, hgx⟩ := hg
  have h1 := Γ.regularAt_scalar_mul (∏ y ∈ F.erase x, d y) (hU x g hgx)
  have h2 : (∏ y ∈ F, d y) = (∏ y ∈ F.erase x, d y) * d x := (Finset.prod_erase_mul F d hx).symm
  rw [h2]
  simpa [map_mul, _root_.mul_assoc] using h1

end GlobalTheory.CompanionTheory.Ar.BT


open Classical in
theorem GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T]
    (Γ : QFGroup R T), ∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤ := by
  classical
  intro R _ _ T _ _ Γ
  have := Fintype.ofFinite T
  let δ : T → T → R := fun s h => if h = s then 1 else 0
  choose e he hreg using fun s : T =>
    Γ.exists_denom (fun h => algebraMap R (FractionRing R) (δ s h))
  have hmem : ∀ s, (∏ x, e x) • δ s ∈ Γ.btOrder ⊤ := by
    intro s
    refine Algebra.subset_adjoin ?_
    intro t g _
    have h1 := Γ.regularAt_scalar_mul (∏ y ∈ Finset.univ.erase (t⁻¹ * s), e y) (hreg (t⁻¹ * s) g)
    have h2 : (∏ y, e y) = (∏ y ∈ Finset.univ.erase (t⁻¹ * s), e y) * e (t⁻¹ * s) :=
      (Finset.prod_erase_mul _ e (Finset.mem_univ _)).symm
    have h3 : (fun h => algebraMap R (FractionRing R) (((∏ x, e x) • δ s) (t * h))) =
        fun h => algebraMap R (FractionRing R) (∏ y ∈ Finset.univ.erase (t⁻¹ * s), e y) *
          (algebraMap R (FractionRing R) (e (t⁻¹ * s)) *
            algebraMap R (FractionRing R) (δ (t⁻¹ * s) h)) := by
      funext h
      have h4 : δ s (t * h) = δ (t⁻¹ * s) h := by
        have : t * h = s ↔ h = t⁻¹ * s := by
          constructor
          · rintro rfl; simp
          · rintro rfl; simp
        simp [δ, this]
      rw [Pi.smul_apply, h4, h2, smul_eq_mul, map_mul, map_mul, _root_.mul_assoc]
    rw [h3]
    exact h1
  refine ⟨∏ x, e x, Finset.prod_ne_zero_iff.2 fun x _ => he x, fun f => ?_⟩
  have hf : (∏ x, e x) • f = ∑ s, f s • ((∏ x, e x) • δ s) := by
    funext h
    simp [δ, Finset.sum_apply, _root_.mul_comm]
  rw [hf]
  exact Subalgebra.sum_mem _ fun s _ => Subalgebra.smul_mem _ (hmem s) _
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.exists_denominator_regular : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (f : T → FractionRing R) (g : Γ.G.left), ∃ d : R, d ≠ 0 ∧ Γ.RegularAt (fun t => algebraMap R _ d * f t) g := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.RegDenom.exists_denom_regularAt
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_stalk_fraction_of_generic : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (p : Cpt ξ) (a : Ω), ∃ b c : X.presheaf.stalk p.1, genMap ξ p c ≠ 0 ∧ a * genMap ξ p c = genMap ξ p b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_frac_genMap | exact GlobalTheory.CompanionTheory.Ar.exists_frac_genMap | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_frac_genMap <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.germ_genPt_injective_range_regAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (U : X.Opens) (h : genPt ξ ∈ U), (∀ q : X, q ∈ U → genPt ξ ⤳ q) → Function.Injective (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom ∧ ∀ a : Ω, a ∈ (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom.range ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.regAt_sections | exact GlobalTheory.CompanionTheory.Ar.regAt_sections | (intros; apply GlobalTheory.CompanionTheory.Ar.regAt_sections <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_point_localization_prime : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (p : Cpt ξ) (I : Ideal (regAt ξ p)), I.IsPrime → ∃ q : Cpt ξ, q.1 ⤳ p.1 ∧ ∀ a : Ω, a ∈ regAt ξ q ↔ ∃ s : regAt ξ p, s ∉ I ∧ (s : Ω) * a ∈ regAt ξ p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.regAt_prime_generisation | exact GlobalTheory.CompanionTheory.Ar.regAt_prime_generisation | (intros; apply GlobalTheory.CompanionTheory.Ar.regAt_prime_generisation <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.regular_at_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G) (t : T), toUnit (genPt R) ≫ σ = Γ.pt t → ∀ (f : T → FractionRing R) (g : Γ.G.left), Γ.RegularAt f (((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left g) → Γ.RegularAt (fun h => f (t * h)) g := by
  exact @QFGroup.regularAt_translate
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.torus_point_over_fraction_field : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (Ω : Type) [Field Ω] (k : FractionRing R →+* Ω) (y : Spec (CommRingCat.of Ω) ⟶ Γ.G.left), y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (k.comp (algebraMap R (FractionRing R)))) → ∃ t, y = Spec.map (CommRingCat.ofHom k) ≫ (Γ.pt t).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_eq_comp_pt | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_eq_comp_pt | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_eq_comp_pt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.quasi_finite_group_finite : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T), Finite T := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.finite_of_qfGroup | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.finite_of_qfGroup | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.finite_of_qfGroup <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.regular_at_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ.RegularAt f (F g') → Γ'.RegularAt (fun t => κ (f t)) g' := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF κ hκ f g' ⟨U, hU, s, hs⟩
  refine ⟨F ⁻¹ᵁ U, hU, (F.app U).hom s, fun t h => ?_⟩
  have e := genericPoint_baseChange R T Γ R' Γ' F hF κ hκ t
  let x := (Γ.pt t).left
  let φ := Spec.map (CommRingCat.ofHom κ)
  have hcomp : ⊤ ≤ ((Γ'.pt t).left ≫ F) ⁻¹ᵁ U := h
  have hmap : ⊤ ≤ (φ ≫ x) ⁻¹ᵁ U := e ▸ hcomp
  have hx : ⊤ ≤ x ⁻¹ᵁ U := fun z _ => by
    have hz : z = φ (IsLocalRing.closedPoint (FractionRing R')) :=
      Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    rw [hz]
    exact hmap (by trivial)
  have valAt_eq {y y' : Spec (CommRingCat.of (FractionRing R')) ⟶ Γ.G.left}
      (hy : ⊤ ≤ y ⁻¹ᵁ U) (hy' : ⊤ ≤ y' ⁻¹ᵁ U) (eq : y = y') :
      valAt y U hy s = valAt y' U hy' s := by
    subst y'
    rfl
  have happ : (φ ≫ x).appLE U ⊤ hmap = x.appLE U ⊤ hx ≫ φ.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE φ x U ⊤ ⊤ hx le_top]
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE φ]
    rfl
  calc
    _ = valAt ((Γ'.pt t).left ≫ F) U hcomp s := by
      simp only [valAt, Scheme.Hom.comp_appLE]
      rfl
    _ = valAt (φ ≫ x) U hmap s := valAt_eq hcomp hmap e
    _ = κ (valAt x U hx s) := by
      simp only [valAt, happ]
      exact congrArg (fun z => z.hom ((x.appLE U ⊤ hx).hom s))
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom κ))
    _ = κ (f t) := congrArg κ (hs t hx)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.base_change_points_compat : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ t, (Γ'.pt t).left ≫ F = Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.genericPoint_baseChange
end
