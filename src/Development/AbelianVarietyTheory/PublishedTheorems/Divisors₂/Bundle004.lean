module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
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
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.UpperBounds.SingleMemIntVec

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ChowHt

section Mult

variable {R : Type} [CommRing R]

def localLength (J Q : Ideal R) [Q.IsPrime] : ℕ∞ :=
  Module.length (Localization.AtPrime Q)
    (Localization.AtPrime Q ⧸ J.map (algebraMap R (Localization.AtPrime Q)))

theorem localLength_ne_top [IsNoetherianRing R] {J Q : Ideal R} [Q.IsPrime]
    (h : Q ∈ J.minimalPrimes) : localLength J Q ≠ ⊤ := by
  have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (A := Localization.AtPrime Q) Q J h
  rw [Localization.AtPrime.map_eq_maximalIdeal] at hrad
  have hmin : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∈
      (J.map (algebraMap R (Localization.AtPrime Q))).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hrad, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  haveI := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hmin
  rw [localLength, Module.length_eq_of_surjective
    (R := Localization.AtPrime Q ⧸ J.map (algebraMap R (Localization.AtPrime Q)))
    Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

end Mult

variable {k : Type} [Field k] {N : ℕ}


open Classical in
def projCycle (J : Ideal (MvPolynomial (Fin N) k)) : Ideal (MvPolynomial (Fin N) k) →₀ ℕ :=
  Finsupp.ofSupportFinite
    (fun Q => if h : Q ∈ projComponents J then
      (haveI : Q.IsPrime := h.1.1.1; localLength J Q).toNat else 0)
    ((finite_projComponents J).subset fun Q hQ => by
      by_contra h
      exact hQ (dif_neg h))

theorem cast_projCycle_apply {J Q : Ideal (MvPolynomial (Fin N) k)} [Q.IsPrime]
    (h : Q ∈ projComponents J) : (projCycle J Q : ℕ∞) = localLength J Q := by
  rw [projCycle, Finsupp.ofSupportFinite_coe]
  simp only [dif_pos h]
  exact ENat.coe_toNat (localLength_ne_top h.1)

theorem projCycle_apply_of_notMem {J Q : Ideal (MvPolynomial (Fin N) k)}
    (h : Q ∉ projComponents J) : projCycle J Q = 0 := by
  rw [projCycle, Finsupp.ofSupportFinite_coe]
  exact dif_neg h

def hyperplaneForm (u : Fin N → k) : MvPolynomial (Fin N) k := ∑ j, C (u j) * X j

def hyperplaneSection (P : Ideal (MvPolynomial (Fin N) k)) (u : Fin N → k) :
    Ideal (MvPolynomial (Fin N) k) →₀ ℕ :=
  projCycle (P ⊔ Ideal.span {hyperplaneForm u})

def fixFirstBlock {B : ℕ} (u : Fin N → k) (f : MvPolynomial (Fin (B + 1) × Fin N) k) :
    MvPolynomial (Fin B × Fin N) k :=
  aeval (fun p : Fin (B + 1) × Fin N =>
    (Fin.cons (fun j => C (u j)) (fun b j => X (b, j)) :
      Fin (B + 1) → Fin N → MvPolynomial (Fin B × Fin N) k) p.1 p.2) f

end GlobalTheory.ChowHt

namespace GlobalTheory.Published

open GlobalTheory.ChowHt

def ChowFormExists : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (N D : ℕ) (I : Ideal (MvPolynomial (Fin N) k)),
    I.IsHomogeneous (homogeneousSubmodule (Fin N) k) →
    (I.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) :
      MvPolynomial (Fin N) k →+* MvPolynomial (Fin N) (AlgebraicClosure k))).IsPrime →
    ringKrullDim (MvPolynomial (Fin N) k ⧸ I) = (D + 1 : ℕ) →
    ∃ f : MvPolynomial (Fin (D + 1) × Fin N) k, IsChowForm I D (hilbertDegree I) f ∧
      ∀ g : MvPolynomial (Fin (D + 1) × Fin N) k, IsChowForm I D (hilbertDegree I) g →
        ∃ c : k, c ≠ 0 ∧ g = C c * f

def ChowFormIntExists : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (N e : ℕ) (P : Ideal (MvPolynomial (Fin N) k)),
    P.IsHomogeneous (homogeneousSubmodule (Fin N) k) → P.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) k ⧸ P) = (e + 1 : ℕ) →
    ∃ f : MvPolynomial (Fin (e + 1) × Fin N) k, IsChowFormInt P e (hilbertDegree P) f ∧
      ∀ g : MvPolynomial (Fin (e + 1) × Fin N) k, IsChowFormInt P e (hilbertDegree P) g →
        ∃ c : k, c ≠ 0 ∧ g = C c * f

def ChowFormHyperplaneSection : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (N e : ℕ) (P : Ideal (MvPolynomial (Fin N) k)),
    P.IsHomogeneous (homogeneousSubmodule (Fin N) k) → P.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) k ⧸ P) = (e + 1 + 1 : ℕ) →
    ∀ u : Fin N → k, hyperplaneForm u ∉ P →
    ∀ (dl : ℕ) (f : MvPolynomial (Fin (e + 1 + 1) × Fin N) k), IsChowFormInt P (e + 1) dl f →
    ∀ (d : Ideal (MvPolynomial (Fin N) k) → ℕ)
      (g : Ideal (MvPolynomial (Fin N) k) → MvPolynomial (Fin (e + 1) × Fin N) k),
      (∀ Q ∈ (hyperplaneSection P u).support, IsChowFormInt Q e (d Q) (g Q)) →
      ∃ c : k, c ≠ 0 ∧
        fixFirstBlock u f = C c * (hyperplaneSection P u).prod (fun Q m => g Q ^ m)

theorem chowFormExists_iff : ChowFormExists ↔
    ∀ (k : Type) [Field k] [CharZero k] (N D : ℕ) (I : Ideal (MvPolynomial (Fin N) k)),
      I.IsHomogeneous (homogeneousSubmodule (Fin N) k) →
      (I.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) :
        MvPolynomial (Fin N) k →+* MvPolynomial (Fin N) (AlgebraicClosure k))).IsPrime →
      ringKrullDim (MvPolynomial (Fin N) k ⧸ I) = (D + 1 : ℕ) →
      ∃ f : MvPolynomial (Fin (D + 1) × Fin N) k, IsChowForm I D (hilbertDegree I) f := by
  refine ⟨fun h k _ _ N D I h1 h2 h3 => (h k N D I h1 h2 h3).imp fun _ => And.left,
    fun h k _ _ N D I h1 h2 h3 => ?_⟩
  obtain ⟨f, hf⟩ := h k N D I h1 h2 h3
  exact ⟨f, hf, fun g hg => (hf.isChowFormInt.unique hg.isChowFormInt).2⟩

theorem chowFormIntExists_iff : ChowFormIntExists ↔
    ∀ (k : Type) [Field k] [CharZero k] (N e : ℕ) (P : Ideal (MvPolynomial (Fin N) k)),
      P.IsHomogeneous (homogeneousSubmodule (Fin N) k) → P.IsPrime →
      ringKrullDim (MvPolynomial (Fin N) k ⧸ P) = (e + 1 : ℕ) →
      ∃ f : MvPolynomial (Fin (e + 1) × Fin N) k, IsChowFormInt P e (hilbertDegree P) f := by
  refine ⟨fun h k _ _ N D I h1 h2 h3 => (h k N D I h1 h2 h3).imp fun _ => And.left,
    fun h k _ _ N D I h1 h2 h3 => ?_⟩
  obtain ⟨f, hf⟩ := h k N D I h1 h2 h3
  exact ⟨f, hf, fun g hg => (hf.unique hg).2⟩

end GlobalTheory.Published
end
end

section

noncomputable section

open CategoryTheory Ideal
open scoped TensorProduct

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup

def hodgeTateSubspace {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O] (C : Type) [Field C]
    [Algebra O C] (G : PDivGroup p O) : Submodule C (C ⊗[O] (O ⊗[ℤ_[p]] G.Tate)) :=
  LinearMap.ker (G.hodgeTateLinear.baseChange C)

def PDivisibleGroupsOverOC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] [Algebra ℤ_[p] O],
      (∀ (G H : PDivGroup p O) (f : G.Tate →ₗ[ℤ_[p]] H.Tate),
        (∀ x ∈ hodgeTateSubspace C G, (f.baseChange O).baseChange C x ∈ hodgeTateSubspace C H) →
          ∃! φ : G ⟶ H, tateMap G H O φ = f) ∧
      ∀ (h : ℕ) (W : Submodule C (C ⊗[O] (O ⊗[ℤ_[p]] (Fin h → ℤ_[p])))),
        ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])),
          ∀ x, x ∈ hodgeTateSubspace C G ↔ (e.toLinearMap.baseChange O).baseChange C x ∈ W

end GlobalTheory.Published
end
end

section

noncomputable section

open CategoryTheory Ideal
open scoped TensorProduct

namespace GlobalTheory.Published

open GlobalTheory.PDivGroup

def ScholzeWeinsteinB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] [Algebra ℤ_[p] O],
      (∀ (G H : PDivGroup p O) (f : G.Tate →ₗ[ℤ_[p]] H.Tate),
        (∀ x, G.hodgeTateLinear x = 0 → H.hodgeTateLinear (f.baseChange O x) = 0) →
          ∃! φ : G ⟶ H, tateMap G H O φ = f) ∧
      ∀ (h : ℕ) (W : Submodule O (O ⊗[ℤ_[p]] (Fin h → ℤ_[p]))),
        (∀ (c : O) (x : O ⊗[ℤ_[p]] (Fin h → ℤ_[p])), c ≠ 0 → c • x ∈ W → x ∈ W) →
          ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])),
            ∀ x, G.hodgeTateLinear x = 0 ↔ e.toLinearMap.baseChange O x ∈ W

end GlobalTheory.Published
end
end

section

noncomputable section

namespace GlobalTheory.SUVol.TamModel

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.UCls.Model GlobalTheory.SUVol
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Up.Definite
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem sEquiv_refl (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (M : ℕ) (g) : SEquiv G L M g g :=
  ⟨1, by rw [SUVol.ratM_one]; exact ⟨(isKM_one _ G L M).1, det_one⟩, 1, isKM_one _ G L M, det_one, by
    rw [SUVol.ratM_one]; simp⟩

theorem sEquiv_trans {G : Matrix (Fin r) (Fin r) E} {L : Set (Fin r → E)} {M : ℕ} {a b d}
    (h : SEquiv G L M a b) (h' : SEquiv G L M b d) : SEquiv G L M a d := by
  obtain ⟨γ, hγ, k, hk, hd, rfl⟩ := h
  obtain ⟨γ', hγ', k', hk', hd', rfl⟩ := h'
  exact ⟨γ' * γ, by
    rw [SUVol.ratM_mul]; exact ⟨isUA_mul _ G hγ'.1 hγ.1, by rw [det_mul, hγ'.2, hγ.2, one_mul]⟩,
    k * k', isKM_mul _ G L M hk hk', by rw [det_mul, hd, hd', one_mul], by
    rw [SUVol.ratM_mul]; simp only [Matrix.mul_assoc]⟩

theorem sEquiv_symm {G : Matrix (Fin r) (Fin r) E} {L : Set (Fin r → E)} {M : ℕ} {a b}
    (h : SEquiv G L M a b) : SEquiv G L M b a := by
  obtain ⟨γ, hγ, k, hk, hkd, rfl⟩ := h
  have hd1 : γ.det = 1 := by
    have h1 := hγ.2
    rw [ratM_det] at h1
    exact one_tmul_injective (F := maximalRealSubfield E) h1
  have hd : IsUnit γ.det := hd1 ▸ isUnit_one
  have hi : ratM (maximalRealSubfield E) γ⁻¹ * ratM (maximalRealSubfield E) γ = 1 := by
    rw [← SUVol.ratM_mul, nonsing_inv_mul γ hd, SUVol.ratM_one]
  refine ⟨γ⁻¹, ⟨by rw [← inv_eq_left_inv hi]; exact isUA_inv _ G hγ.1, ?_⟩, k⁻¹, isKM_inv _ G L M hk, ?_, ?_⟩
  · have := congrArg det hi
    rwa [det_mul, hγ.2, mul_one, det_one] at this
  · have := congrArg det (nonsing_inv_mul k hk.1.1)
    rwa [det_mul, hkd, mul_one, det_one] at this
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv k hk.1.1, Matrix.mul_one, ← Matrix.mul_assoc, hi,
      Matrix.one_mul]

theorem exists_sReps (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (M : ℕ) :
    ∃ (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), Nonempty J ∧ IsSReps G L M s := by
  let S : Setoid {g // IsSA G g} :=
    ⟨fun a b => SEquiv G L M a.1 b.1, fun a => sEquiv_refl G L M a.1, sEquiv_symm, sEquiv_trans⟩
  refine ⟨Quotient S, fun q => q.out.1, ⟨Quotient.mk S ⟨1, (isKM_one _ G L M).1, det_one⟩⟩, fun q => q.out.2,
    fun i j h => ?_, fun g hg => ⟨Quotient.mk S ⟨g, hg⟩, Quotient.mk_out (s := S) ⟨g, hg⟩⟩⟩
  rw [← i.out_eq, ← j.out_eq]
  exact Quotient.sound h



end GlobalTheory.SUVol.TamModel
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Published

namespace FormalAlgebraisation

def Morphisms : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom →
      IsSeparated Z.hom → LocallyOfFiniteType Z.hom → QuasiCompact Z.hom →
    ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left),
      (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) →
    ∀ f : ∀ e, (Y e).left ⟶ Z.left,
      (∀ e, f e ≫ Z.hom = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ f (e + 1) = f e) →
      ∃! g : X ⟶ Z, ∀ e, b e ≫ g.left = f e

def Schemes : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left),
      (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) →
      (∀ e, IsProper (Y e).hom) →
    ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → (∀ e, LBIso (N e) ((N (e + 1)).pull (β e))) →
      RelAmple (Y 0) (N 0) →
      ∃ (X : Over (Spec (CommRingCat.of R))) (M : LB X.left) (b : ∀ e, (Y e).left ⟶ X.left),
        IsProper X.hom ∧ M.IsLB ∧ RelAmple X M ∧
        (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧
        ∀ e, LBIso (N e) (M.pull (b e))

end FormalAlgebraisation

def FormalAlgebraisation : Prop :=
  FormalAlgebraisation.Morphisms ∧ FormalAlgebraisation.Schemes

namespace FormalAlgebraisation

variable {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}

theorem Morphisms.existsUnique_thick (H : Morphisms) (hI : IsAdicComplete I R)
    (X Z : Over (Spec (CommRingCat.of R))) [hX : IsProper X.hom] [hZ : IsProper Z.hom]
    (f : ∀ e, (thickObj R I e X).left ⟶ Z.left)
    (hf : ∀ e, f e ≫ Z.hom = pullback.fst X.hom (thick R I e) ≫ X.hom)
    (hc : ∀ e, thickMap R I e X ≫ f (e + 1) = f e) :
    ∃! g : X ⟶ Z, ∀ e, pullback.fst X.hom (thick R I e) ≫ g.left = f e :=
  H R I hI X Z hX inferInstance inferInstance inferInstance (fun e => thickObj R I e X)
    (fun e => thickMap R I e X) (fun e => pullback.fst X.hom (thick R I e))
    (fun _ => IsPullback.of_hasPullback _ _)
    (fun _ => (pullback.lift_fst _ _ _).trans (Category.comp_id _)) f
    (fun e => (hf e).trans pullback.condition) hc

theorem Morphisms.hom_ext (H : Morphisms) (hI : IsAdicComplete I R)
    {X Z : Over (Spec (CommRingCat.of R))} [IsProper X.hom] [IsProper Z.hom] {g g' : X ⟶ Z}
    (h : ∀ e, pullback.fst X.hom (thick R I e) ≫ g.left = pullback.fst X.hom (thick R I e) ≫ g'.left) :
    g = g' :=
  (H.existsUnique_thick hI X Z (fun e => pullback.fst X.hom (thick R I e) ≫ g'.left)
    (fun e => by rw [Category.assoc, Over.w])
    (fun e => by
      rw [← Category.assoc]
      exact congrArg (· ≫ g'.left) ((pullback.lift_fst _ _ _).trans (Category.comp_id _)))).unique
    h (fun _ => rfl)

theorem Morphisms.exists_iso (H : Morphisms) (hI : IsAdicComplete I R)
    {X X' : Over (Spec (CommRingCat.of R))} [hX : IsProper X.hom] [hX' : IsProper X'.hom]
    {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {b : ∀ e, (Y e).left ⟶ X.left}
    {b' : ∀ e, (Y e).left ⟶ X'.left}
    (hb : ∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) (hβ : ∀ e, β e ≫ b (e + 1) = b e)
    (hb' : ∀ e, IsPullback (b' e) (Y e).hom X'.hom (thick R I e))
    (hβ' : ∀ e, β e ≫ b' (e + 1) = b' e) :
    ∃ g : X ≅ X', (∀ e, b e ≫ g.hom.left = b' e) ∧
      ∀ g' : X ⟶ X', (∀ e, b e ≫ g'.left = b' e) → g' = g.hom := by
  obtain ⟨g, hg, hu⟩ := H R I hI X X' hX inferInstance inferInstance inferInstance Y β b hb hβ b'
    (fun e => (hb' e).w) hβ'
  obtain ⟨k, hk, -⟩ := H R I hI X' X hX' inferInstance inferInstance inferInstance Y β b' hb' hβ' b
    (fun e => (hb e).w) hβ
  refine ⟨⟨g, k, ?_, ?_⟩, hg, hu⟩
  · exact (H R I hI X X hX inferInstance inferInstance inferInstance Y β b hb hβ b
      (fun e => (hb e).w) hβ).unique
      (fun e => by rw [Over.comp_left, ← Category.assoc, hg, hk]) (fun e => Category.comp_id _)
  · exact (H R I hI X' X' hX' inferInstance inferInstance inferInstance Y β b' hb' hβ' b'
      (fun e => (hb' e).w) hβ').unique
      (fun e => by rw [Over.comp_left, ← Category.assoc, hk, hg]) (fun e => Category.comp_id _)

end FormalAlgebraisation

end GlobalTheory.Published
end
end
