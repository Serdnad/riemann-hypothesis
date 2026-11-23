module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1823
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1829
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle371
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaTildeHeckeCharSplitMulSignOfNormFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianPoincareSeriesThetaVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1826
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1827
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma
theorem unitLat_selfDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ q : UL n w, IsLat K.O K.E (unitLat e B ψ q) ∧ ∀ y, y ∈ unitLat e B ψ q ↔ ∀ z ∈ unitLat e B ψ q, B.herm x y z ∈ (algebraMap K.O K.E).range := GlobalTheory.T.unitaryLattice_isLattice_selfDual_hermitianModel
theorem unitLat_stable_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (γ : UL n w), (∀ y, ψ (B.g * y) = ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ q : UL n w, ((∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔ q⁻¹ * γ * q ∈ KL n w) := GlobalTheory.T.unitLattice_stable_iff_conj_integral
theorem unitLat_eq_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ q q' : UL n w, unitLat e B ψ q = unitLat e B ψ q' ↔ q⁻¹ * q' ∈ KL n w := GlobalTheory.T.unitaryLattice_eq_iff_inv_mul_integral
theorem exists_unitLat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ L : Submodule K.O B.A, IsLat K.O K.E L → (∀ y, y ∈ L ↔ ∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) → ∃ q : UL n w, unitLat e B ψ q = L := GlobalTheory.T.self_dual_lattice_standard_hermitian
theorem exists_torus_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∃ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, ∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y := GlobalTheory.T.localUnitaryCentralizer_equiv_normOneTorus
theorem cptPart_iff_intUnits : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∀ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, (∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ t : twCent (MonoidHom.id (UL n w)) γ, ((t : UL n w) ∈ cptPart (twCent (MonoidHom.id (UL n w)) γ) ↔ ((τ t : B.Aˣ)) ∈ intUnits K.O B.A) := GlobalTheory.T.compactPart_centralizer_iff_integralUnits_of_model
theorem twOrb_unit : ∀ (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G), twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id G) γ : Set G) (K : Set G), if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then (((twCent (MonoidHom.id G) γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) γ)) : ℕ) : ℂ) else 0 := GlobalTheory.T.orbitalIntegral_indicator_eq_finsum_relIndex
theorem relIndex_transport : ∀ (G H : Type) [Group G] [Group H] (T : Subgroup G) (S : Subgroup H) (τ : T ≃* S) (A₁ A₂ : Subgroup G) (B₁ B₂ : Subgroup H), A₁ ≤ T → A₂ ≤ T → (∀ t : T, (t : G) ∈ A₁ ↔ ((τ t : S) : H) ∈ B₁) → (∀ t : T, (t : G) ∈ A₂ ↔ ((τ t : S) : H) ∈ B₂) → A₁.relIndex A₂ = (B₁ ⊓ S).relIndex (B₂ ⊓ S) := GlobalTheory.T.relIndex_eq_relIndex_inf_of_mulEquiv_subgroup
end GlobalTheory.InertUnitOrb

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma

theorem mem_mulLat_unit {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (L : Submodule O A) (a : Aˣ) (y : A) :
    y ∈ mulLat O (a : A) L ↔ ((a⁻¹ : Aˣ) : A) * y ∈ L := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [← mul_assoc] using hz
  · intro h
    exact ⟨((a⁻¹ : Aˣ) : A) * y, h, by simp [← mul_assoc]⟩

theorem mem_stabLat_iff : ∀ (O : Type) [CommRing O] (A : Type) [CommRing A] [Algebra O A] (L : Submodule O A) (u : Aˣ), u ∈ stabLat O L ↔ mulLat O (u : A) L = L := by
  intro O _ A _ _ L u
  constructor
  · intro h
    have h' : ∀ y, y ∈ L ↔ (u : A) * y ∈ L := h
    ext y
    rw [mem_mulLat_unit, h', ← mul_assoc, Units.mul_inv, one_mul]
  · intro h y
    have hy := mem_mulLat_unit L u ((u : A) * y)
    rw [h, ← mul_assoc, Units.inv_mul, one_mul] at hy
    exact hy.symm

theorem unitLat_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (t q : UL n w) (a : B.Aˣ), (∀ y, ψ ((a : B.A) * y) = ((((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → unitLat e B ψ (t * q) = mulLat K.O (a : B.A) (unitLat e B ψ q) := by
  intro E _ _ _ hE w hw K e he hint n B ψ t q a ha
  have hmap : ∀ (g h : UL n w), ((((g * h : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) =
      (((g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm *
        (((h : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm := by
    intro g h
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact Matrix.map_mul (f := (e.symm : w.adicCompletion E →+* K.E))
  have hinv : ∀ y, ((((t⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y =
      ψ (((a⁻¹ : B.Aˣ) : B.A) * y) := by
    intro y
    have h1 : ψ y = ((((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ
        ψ (((a⁻¹ : B.Aˣ) : B.A) * y) := by
      rw [← ha, ← mul_assoc, Units.mul_inv, one_mul]
    rw [h1, Matrix.mulVec_mulVec, ← hmap, inv_mul_cancel]
    simp
  have key : ∀ (r : UL n w) (z : B.A), z ∈ unitLat e B ψ r ↔
      ∀ i, (((((r⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ z) i ∈
        (algebraMap K.O K.E).range := fun r z => Iff.rfl
  ext y
  rw [key, _root_.mul_inv_rev, hmap, ← Matrix.mulVec_mulVec, hinv, ← key, mem_mulLat_unit]

end GlobalTheory.InertUnitOrb

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma

theorem mulLat_one' {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (L : Submodule O A) :
    mulLat O (1 : A) L = L := by
  simp [mulLat]

theorem mulLat_mul' {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (a b : A) (L : Submodule O A) :
    mulLat O (a * b) L = mulLat O a (mulLat O b L) := by
  rw [mulLat, mulLat, mulLat, LinearMap.mulLeft_mul, Submodule.map_comp]

theorem orbRel_equivalence {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (G : Subgroup Aˣ)
    (X : Set (Submodule O A)) :
    Equivalence (fun L M : X => ∃ t ∈ G, (M : Submodule O A) = mulLat O (t : A) (L : Submodule O A)) := by
  constructor
  · intro L
    exact ⟨1, G.one_mem, by simp [mulLat_one']⟩
  · rintro L M ⟨t, ht, h⟩
    refine ⟨t⁻¹, G.inv_mem ht, ?_⟩
    rw [h, ← mulLat_mul', Units.inv_mul, mulLat_one']
  · rintro L M N ⟨t, ht, h⟩ ⟨s, hs, h'⟩
    refine ⟨s * t, G.mul_mem hs ht, ?_⟩
    rw [h', h, Units.val_mul, mulLat_mul']

theorem ratCast_finsum' {α : Type} (f : α → ℚ) : ((∑ᶠ i, f i : ℚ) : ℂ) = ∑ᶠ i, ((f i : ℚ) : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact AddMonoidHom.map_finsum (Rat.castHom ℂ).toAddMonoidHom h
  · rw [finsum_of_infinite_support h, finsum_of_infinite_support]
    · simp
    · have : Function.support (fun i => ((f i : ℚ) : ℂ)) = Function.support f := by
        ext i; simp
      rwa [this]

theorem finsum_ite_subtype' {α M : Type} [AddCommMonoid M] (p : α → Prop) [DecidablePred p] (f : α → M) :
    ∑ᶠ i, (if p i then f i else 0) = ∑ᶠ i : Subtype p, f i := by
  rw [finsum_subtype_eq_finsum_cond]
  exact finsum_congr fun i => finsum_eq_if.symm

theorem orb_eq_N : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (γ : UL n w) (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B (γ.1.val.map e.symm) x ψ → twOrb (MonoidHom.id _) (KL n w) γ ((KL n w : Set (UL n w)).indicator 1) = ((B.N x : ℚ) : ℂ) := by
  intro E _ _ _ hE w hw K e he hint n B hsep γ x ψ hM
  obtain ⟨hx, hg, hh⟩ := hM
  obtain ⟨τ, hτ⟩ := exists_torus_equiv E hE w hw K e he hint n B ψ x γ ⟨hx, hg, hh⟩ hsep
  have hcpt := cptPart_iff_intUnits E hE w hw K e he hint n B ψ x γ ⟨hx, hg, hh⟩ hsep τ hτ
  have hS1 := unitLat_selfDual E hE w hw K e he hint n B ψ x hx hh
  have hS1b := unitLat_stable_iff E hE w hw K e he hint n B ψ γ hg
  have hS2 := unitLat_eq_iff E hE w hw K e he hint n B ψ
  have hS3 := exists_unitLat_eq E hE w hw K e he hint n B ψ x hx hh
  have hS6 : ∀ (t : twCent (MonoidHom.id (UL n w)) γ) (q : UL n w),
      unitLat e B ψ ((t : UL n w) * q) = mulLat K.O ((τ t : B.Aˣ) : B.A) (unitLat e B ψ q) :=
    fun t q => unitLat_mul E hE w hw K e he hint n B ψ t q (τ t) (hτ t)
  have hcomm : ∀ s t : twCent (MonoidHom.id (UL n w)) γ, (s : UL n w) * t = t * s := by
    intro s t
    have h1 : τ (s * t) = τ (t * s) := by rw [map_mul, map_mul, mul_comm]
    have := congrArg Subtype.val (τ.injective h1)
    simpa using this
  have hX : ∀ q : UL n w, q⁻¹ * γ * q ∈ KL n w → unitLat e B ψ q ∈ B.X x := fun q hq =>
    ⟨(hS1 q).1, (hS1b q).2 hq, (hS1 q).2⟩
  have hrel : ∀ L M : B.X x, (Quot.mk _ L : Orb K.O B.T (B.X x)) = Quot.mk _ M →
      ∃ t ∈ B.T, (M : Submodule K.O B.A) = mulLat K.O (t : B.A) L := fun L M h =>
    (orbRel_equivalence B.T (B.X x)).eqvGen_iff.mp (Quot.eqvGen_exact h)
  have hcle : cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ twCent (MonoidHom.id (UL n w)) γ :=
    (Subgroup.closure_le _).mpr fun s hs => hs.1
  have hconj : ∀ (Q s : UL n w), s ∈ (KL n w).map (MulAut.conj Q).toMonoidHom ↔ Q⁻¹ * s * Q ∈ KL n w := by
    intro Q s
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rw [twOrb_unit]
  unfold InvAlg.N orbSum
  rw [ratCast_finsum']
  rw [finsum_ite_subtype']
  let φ : {q : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) γ : Set (UL n w)) (KL n w : Set (UL n w)) //
      (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ KL n w} → Orb K.O B.T (B.X x) :=
    fun q => Quot.mk _ ⟨unitLat e B ψ (Quotient.out q.1), hX _ q.2⟩
  refine finsum_eq_of_bijective φ ⟨?_, ?_⟩ ?_
  · rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
    obtain ⟨a, ha, hQ⟩ := hrel _ _ h
    set t := τ.symm ⟨a, ha⟩
    have hta : ((τ t : B.Aˣ) : B.A) = a := by simp [t]
    rw [← hta, ← hS6, hS2] at hQ
    apply Subtype.ext
    show q = q'
    rw [← DoubleCoset.out_eq' q, ← DoubleCoset.out_eq' q', DoubleCoset.eq]
    exact ⟨t, t.2, _, (KL n w).inv_mem hQ, by group⟩
  · intro o
    set R := Quot.out o
    obtain ⟨q0, hq0⟩ := hS3 R.1 R.2.1 R.2.2.2
    have hq0K : q0⁻¹ * γ * q0 ∈ KL n w := (hS1b q0).1 (hq0 ▸ R.2.2.1)
    obtain ⟨h, hh, k, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id (UL n w)) γ) (KL n w) q0
    have hhγ : h * γ = γ * h := hh
    have hP : (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) γ) (KL n w) q0))⁻¹ * γ *
        Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) γ) (KL n w) q0) ∈ KL n w := by
      rw [hout]
      have : (h * q0 * k)⁻¹ * γ * (h * q0 * k) = k⁻¹ * (q0⁻¹ * γ * q0) * k := by
        calc (h * q0 * k)⁻¹ * γ * (h * q0 * k) = k⁻¹ * q0⁻¹ * (h⁻¹ * (γ * h)) * q0 * k := by group
          _ = k⁻¹ * (q0⁻¹ * γ * q0) * k := by rw [← hhγ]; group
      rw [this]
      exact (KL n w).mul_mem ((KL n w).mul_mem ((KL n w).inv_mem hk) hq0K) hk
    refine ⟨⟨_, hP⟩, ?_⟩
    show Quot.mk _ _ = o
    rw [← Quot.out_eq o]
    refine (Quot.sound ?_).symm
    refine ⟨τ ⟨h, hh⟩, (τ ⟨h, hh⟩).2, ?_⟩
    show unitLat e B ψ _ = mulLat K.O _ R.1
    rw [hout, ← hq0, ← hS6]
    exact ((hS2 _ _).2 (by simpa [mul_assoc] using hk)).symm
  · rintro ⟨q, hq⟩
    set R := Quot.out (φ ⟨q, hq⟩)
    have hR : (Quot.mk _ R : Orb K.O B.T (B.X x)) = φ ⟨q, hq⟩ := Quot.out_eq _
    obtain ⟨a, ha, hRa⟩ := hrel _ _ hR.symm
    set t := τ.symm ⟨a, ha⟩
    have hta : ((τ t : B.Aˣ) : B.A) = a := by simp [t]
    rw [← hta, ← hS6] at hRa
    simp only [one_mul, Rat.cast_natCast]
    congr 1
    refine relIndex_transport (UL n w) B.Aˣ _ B.T τ _ _ (stabLat K.O R.1) (intUnits K.O B.A) inf_le_left hcle ?_ hcpt
    intro s
    rw [mem_stabLat_iff, hRa, ← hS6, hS2, Subgroup.mem_inf, hconj]
    simp only [SetLike.coe_mem, true_and]
    have : ((s : UL n w) * ((t : UL n w) * Quotient.out q))⁻¹ * ((t : UL n w) * Quotient.out q) =
        ((Quotient.out q)⁻¹ * s * Quotient.out q)⁻¹ := by
      rw [← mul_assoc (s : UL n w), hcomm s t]
      group
    rw [this]
    exact inv_mem_iff.symm

end GlobalTheory.InertUnitOrb
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.enveloping_representation_injective : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (R : RealPoints θ V), Function.Injective (envRepAll R) := by
  first | exact @GlobalTheory.CentralOps.envRepAll_injective | exact GlobalTheory.CentralOps.envRepAll_injective | (intros; apply GlobalTheory.CentralOps.envRepAll_injective <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj

variable {D : D7}

def gfcToGf (V : HSp D) : GfC V →* Bridge.Gf V := (finHom V).rangeRestrict.comp (GfC V).subtype

theorem gfcToGf_surjective (V : HSp D) : Function.Surjective (gfcToGf V) := by
  rintro ⟨_, h, rfl⟩
  obtain ⟨k, hk, e⟩ := GlobalTheory.VolHeckeCompare.exists_finite_part V h
  exact ⟨⟨k, hk⟩, Subtype.ext e⟩

theorem bc_swapAE_injective (n : ℕ) :
    Function.Injective (Formalism.UG.bc (Lev.swapAE D) : GL (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) →* _) := by
  intro a b e
  apply Units.ext
  have h := congrArg Units.val e
  exact Matrix.map_injective (f := Lev.swapAE D) (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h

theorem finG_injective (V : HSp D) : Function.Injective (finG V) := by
  intro a b e
  have e' : finHom V a.1 = finHom V b.1 := bc_swapAE_injective V.rank e
  have h1 : finHom V (a.1⁻¹ * b.1) = 1 := by rw [map_mul, map_inv, e', inv_mul_cancel]
  have := GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V (mul_mem (inv_mem a.2) b.2) h1
  exact Subtype.ext (inv_mul_eq_one.1 this)

def finLev (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Subgroup (Bridge.Gf V) :=
  (K.comap (Formalism.UG.bc (Lev.swapAE D))).comap (Bridge.Gf V).subtype

theorem mem_finLev_iff (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (g : GfC V) :
    gfcToGf V g ∈ finLev V K ↔ g ∈ K.comap (finG V) := Iff.rfl

theorem isOpenLev_finLev (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (hK : IsCO V K) :
    GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev V (finLev V K) := by
  have e : (((finLev V K).comap (finHom V).rangeRestrict : Subgroup (GA D V)) : Set (GA D V)) =
      ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev
  rw [e]
  exact hK.1

theorem finite_finCl (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hV : ∀ τ, (gramAt D V τ).PosDef) (hK : IsCO V K) : Finite (FinCl V K) := by
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover V hV (finLev V K) (isOpenLev_finLev V K hK)
  choose x hx using fun a => gfcToGf_surjective V (c a)
  refine Finite.of_surjective (fun a : Fin m => (DoubleCoset.mk (ratFin V) (K.comap (finG V)) (x a) : FinCl V K)) ?_
  intro q
  rw [← DoubleCoset.out_eq' q]
  set y := Quotient.out q
  obtain ⟨a, γ, k, e⟩ := hc (gfcToGf V y)
  obtain ⟨z, hz⟩ := gfcToGf_surjective V (Bridge.ratF V γ)
  refine ⟨a, (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨z, ?_, (x a)⁻¹ * z⁻¹ * y, ?_, by group⟩⟩
  · have hz' : finHom V z.1 = finHom V γ.1 := congrArg Subtype.val hz
    refine ⟨γ.1, γ.2, ?_⟩
    show Formalism.UG.bc (Lev.swapAE D) (finHom V γ.1) = Formalism.UG.bc (Lev.swapAE D) (finHom V z.1)
    rw [hz']
  · refine (mem_finLev_iff V K _).1 ?_
    have h1 : gfcToGf V ((x a)⁻¹ * z⁻¹ * y) = (gfcToGf V (x a))⁻¹ * (gfcToGf V z)⁻¹ * gfcToGf V y := by
      simp only [map_mul, map_inv]
    have h2 : (gfcToGf V (x a))⁻¹ * (gfcToGf V z)⁻¹ * gfcToGf V y = (k : Bridge.Gf V) := by
      simp only [hx a, hz, e]; group
    exact (congrArg (· ∈ finLev V K) (h1.trans h2)).mpr k.2

theorem continuous_finHom (V : HSp D) : Continuous (finHom V) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  exact (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ

theorem gamOrd_ne_zero (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hV : ∀ τ, (gramAt D V τ).PosDef) (hK : IsCO V K) (x : GfC V) : gamOrd V K x ≠ 0 := by
  set C : Set (Af D.host.F ⊗[D.host.F] D.host.E) :=
    ⋃ p : Fin V.rank × Fin V.rank, (fun g : GA D V => (finHom V g).1 p.1 p.2) '' (Lev.levA V K : Set (GA D V)) with hCdef
  have hC : IsCompact C := isCompact_iUnion fun p =>
    hK.2.image ((Units.continuous_val.comp (continuous_finHom V)).matrix_elem p.1 p.2)
  have hCJ : ∀ k ∈ finLev V K, ∀ i j, (k : Bridge.Gf V).1.1 i j ∈ C := by
    intro k hk i j
    obtain ⟨g, rfl⟩ := gfcToGf_surjective V k
    exact Set.mem_iUnion.2 ⟨(i, j), g.1, ⟨g.2, (mem_finLev_iff V K g).1 hk⟩, rfl⟩
  have hs := GlobalTheory.RepsObj.finite_stab V hV (finLev V K) hC hCJ (gfcToGf V x)
  have hq : ∀ γ : ratFin V, ∃ q : GQ V, Lev.finE V q.1 = finG V γ.1 := fun γ => by
    obtain ⟨q, hq, e⟩ := Subgroup.mem_map.1 γ.2
    exact ⟨⟨q, hq⟩, e⟩
  choose q hq using hq
  have hfin : Finite {γ : ratFin V // finG V (x⁻¹ * γ * x) ∈ K} := by
    refine Finite.of_injective (β := Bridge.stab (Bridge.ratF V) (finLev V K) (gfcToGf V x))
      (fun γ => ⟨q γ.1, ?_⟩) ?_
    · have e0 : Bridge.ratF V (q γ.1) = gfcToGf V γ.1.1 :=
        Subtype.ext (bc_swapAE_injective V.rank (hq γ.1))
      have e1 : (MulAut.conj (gfcToGf V x)⁻¹) (Bridge.ratF V (q γ.1)) = gfcToGf V (x⁻¹ * γ.1.1 * x) := by
        simp only [e0, map_mul, map_inv, MulAut.conj_inv_apply]
      show (MulAut.conj (gfcToGf V x)⁻¹) (Bridge.ratF V (q γ.1)) ∈ finLev V K
      exact (congrArg (· ∈ finLev V K) e1).mpr ((mem_finLev_iff V K _).2 γ.2)
    · intro γ γ' e
      have e1 : Lev.finE V (q γ.1).1 = Lev.finE V (q γ'.1).1 := by
        have := congrArg (fun s : Bridge.stab (Bridge.ratF V) (finLev V K) (gfcToGf V x) => Lev.finE V s.1.1) e
        exact this
      rw [hq, hq] at e1
      exact Subtype.ext (Subtype.ext (finG_injective V e1))
  refine Nat.card_ne_zero.2 ⟨⟨⟨1, one_mem _⟩, ?_⟩, hfin⟩
  simp only [mul_one, inv_mul_cancel, map_one]
  exact one_mem K

theorem finite_finCl_and_gamOrd : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))),
    (∀ φ : D.host.E →+* ℂ, (V.gram.map φ).PosDef) → IsCO V K → Finite (FinCl V K) ∧ ∀ x, gamOrd V K x ≠ 0 :=
  fun V K hV hK => ⟨finite_finCl V K (fun τ => hV (tauE _ τ)) hK, gamOrd_ne_zero V K (fun τ => hV (tauE _ τ)) hK⟩

end GlobalTheory.FunObj
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_lattice_selfDual_fg_full_index : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → SelfDual (gamQ ψ S T) (latQ S T ΛS ΛT) ∧ (latQ S T ΛS ΛT).toAddSubgroup.FG ∧ (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • x ∈ latQ S T ΛS ΛT) ∧ ∀ (g : GA D S) (h : GA D T) (a : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (b : Matrix (Fin T.rank) (Fin T.rank) D.host.E), Formalism.L2.Theta.mt S g = a.map (incA D) → Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D) → idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h))) = (latQ S T ΛS ΛT).toAddSubgroup.relIndex ((latQ S T ΛS ΛT).toAddSubgroup.comap (sandw b a).toAddMonoidHom) := by
  first | exact @GlobalTheory.RatLattice.latQ_selfDual_fg_full_index | exact GlobalTheory.RatLattice.latQ_selfDual_fg_full_index | (intros; apply GlobalTheory.RatLattice.latQ_selfDual_fg_full_index <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_gaussian_real_isometry_no_fixed : ∀ (D : D7) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ ε : ℂ, ∀ (a a' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (b b' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, a τ * a' τ = 1 ∧ b τ * b' τ = 1 ∧ (a τ)ᴴ * gramAt D S τ * a τ = gramAt D S τ ∧ (b τ)ᴴ * gramAt D T τ * b τ = gramAt D T τ ∧ sS τ * a τ = a τ * sS τ ∧ sT τ * b τ = b τ * sT τ ∧ (b τ ⊗ₖ (a τ)ᵀ - 1).det ≠ 0) → Integrable (gaussR S T sS sT a b) volume ∧ ∃ r : ℝ, 0 < r ∧ (∫ v, gaussR S T sS sT a b v) * ∏ τ, (b τ ⊗ₖ (a τ)ᵀ - 1).det = r * ε * ∏ τ, ((b τ ⊗ₖ (a τ)ᵀ).det * detPlus (sS τ) (sT τ) (a' τ) (b' τ)) := by
  first | exact @GlobalTheory.RatAut.RealInt.integral_gaussR | exact GlobalTheory.RatAut.RealInt.integral_gaussR | (intros; apply GlobalTheory.RatAut.RealInt.integral_gaussR <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.etaTildeHeckeChar_split_mul_sign_of_norm_formula : ∀ (D : D7) (η : (AE D)ˣ →* Circle), IsEtaTilde D η → ∀ (lam : ℕ →* ℂ), GoodNorm (GlobalTheory.FinWeil.sgO D) lam → (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) → ∀ ε, IsHalfIdem D ε → ∀ (x : D.host.E) (k : ℕ), x ≠ 0 → (k : ℚ) = |Algebra.norm ℚ x| → ∀ y : (AE D)ˣ, (y : AE D) = (ε + cA D ε) * incA D x + (1 - (ε + cA D ε)) → ∃ r : ℝ, 0 < r ∧ (η y : ℂ) * lam k * ∏ τ, tauE D τ x = r := by
  first | exact @GlobalTheory.EtaProduct.eta_split_mul_lam_pos | exact GlobalTheory.EtaProduct.eta_split_mul_lam_pos | (intros; apply GlobalTheory.EtaProduct.eta_split_mul_lam_pos <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gaussian_poincare_series_theta_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 → ∀ a : RW T S, ∃ hf : IsThetaFunO ψ S T (serO ψ θ σ S T sS sT ΛS ΛT w a), Fixes (opF hψ.1 S T w) (latF S T ΛS ΛT) (⟨serO ψ θ σ S T sS sT ΛS ΛT w a, hf⟩ : thetaSub ψ S T) ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (serO ψ θ σ S T sS sT ΛS ΛT w a) := by
  first | exact @GlobalTheory.GaussSeriesVacuum.series_theta_vacuum | exact GlobalTheory.GaussSeriesVacuum.series_theta_vacuum | (intros; apply GlobalTheory.GaussSeriesVacuum.series_theta_vacuum <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.sesquilinearDetOrdSignOnKernel_conj_GL : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K), (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (Q : K[X]) (a k : GL (Fin n) K), sgnOn σ 1 Q (k⁻¹ * a * k).val = sgnOn σ (cT σ (k⁻¹).val * (k⁻¹).val) Q a.val := by
  first | exact @GlobalTheory.UnitaryClasses.SgnConj.sgnOn_conj | exact GlobalTheory.UnitaryClasses.SgnConj.sgnOn_conj | (intros; apply GlobalTheory.UnitaryClasses.SgnConj.sgnOn_conj <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.gramKernelSign_nonsplit_baseChange_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (H A : Matrix (Fin n) (Fin n) E), (-1 : ℂ) ^ ordL (gramOn (cj w) (H.map (algebraMap E (w.adicCompletion E))) (LinearMap.ker (Matrix.toLin' (A.map (algebraMap E (w.adicCompletion E)))))).det = (-1) ^ ordL (algebraMap E (w.adicCompletion E) (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H (LinearMap.ker (Matrix.toLin' A))).det) := by
  first | exact @GlobalTheory.UnitaryClasses.BaseChangeSign.main | exact GlobalTheory.UnitaryClasses.BaseChangeSign.main | (intros; apply GlobalTheory.UnitaryClasses.BaseChangeSign.main <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.gram_det_hermitian_totally_positive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (V : Submodule E (Fin n → E)), (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det ≠ 0 ∧ ∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det = r := by
  first | exact @GlobalTheory.UnitaryClasses.gramOn_one_det_totallyPositive | exact GlobalTheory.UnitaryClasses.gramOn_one_det_totallyPositive | (intros; apply GlobalTheory.UnitaryClasses.gramOn_one_det_totallyPositive <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.exists_openSubgroups_schroedinger_fix_standardChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
      ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        ∀ x ∈ L₁, ∀ y ∈ L₂, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x, GlobalTheory.WeilCont.adeleJoin D.host.F 0 y) Φ = Φ := by
  first | exact @GlobalTheory.SchrFixNbhd.schr_fix_nbhd | exact GlobalTheory.SchrFixNbhd.schr_fix_nbhd | (intros; apply GlobalTheory.SchrFixNbhd.schr_fix_nbhd <;> assumption)
end
