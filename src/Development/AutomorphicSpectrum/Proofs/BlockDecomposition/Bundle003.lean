module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.Topology.Algebra.Group.ContinuousInv
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.FFNorm

theorem exists_conj_mul_eq : ∀ (κ : Type) [Field κ] [Finite κ] (τ : κ →+* κ), (∀ x, τ (τ x) = x) →
    (∃ x, τ x ≠ x) → ∀ c : κ, τ c = c → ∃ s : κ, τ s * s = c := by
  intro κ _ _ τ hinv hne c hc
  classical
  let F : Subfield κ := RingHom.eqLocusField τ (RingHom.id κ)
  have hF : ∀ y : F, τ (y : κ) = y := fun y => y.2
  let σ : κ ≃ₐ[F] κ := AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom τ τ
      (RingHom.ext hinv) (RingHom.ext hinv)) (fun y => hF y)
  have hσ : ∀ x, σ x = τ x := fun x => rfl
  have hσ1 : σ ≠ 1 := by
    obtain ⟨x, hx⟩ := hne
    intro h
    exact hx (by rw [← hσ, h]; rfl)
  have hall : ∀ ρ : κ ≃ₐ[F] κ, ρ = 1 ∨ ρ = σ := by
    have hfix : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : σ x = x := hx ⟨σ, Subgroup.mem_zpowers σ⟩
      exact IntermediateField.mem_bot.2 ⟨⟨x, this⟩, rfl⟩
    have htop : Subgroup.zpowers σ = ⊤ := by
      rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ), hfix]
      exact IntermediateField.fixingSubgroup_bot
    intro ρ
    have hρ : ρ ∈ Subgroup.zpowers σ := htop ▸ Subgroup.mem_top ρ
    have hsq : σ ^ 2 = 1 := by
      ext x
      simp [pow_two, hσ, hinv]
    obtain ⟨n, rfl⟩ := hρ
    rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
    · left; simp [zpow_mul, hsq]
    · right; simp [zpow_add, zpow_mul, hsq]
  have huniv : (Finset.univ : Finset (κ ≃ₐ[F] κ)) = {1, σ} := by
    ext ρ
    simpa using hall ρ
  obtain ⟨a, ha⟩ := FiniteField.norm_surjective F κ (⟨c, hc⟩ : F)
  refine ⟨a, ?_⟩
  have h := Algebra.norm_eq_prod_automorphisms F a
  rw [huniv, Finset.prod_pair hσ1.symm, ha] at h
  have h2 : algebraMap F κ (⟨c, hc⟩ : F) = c := rfl
  rw [h2] at h
  simpa [hσ, mul_comm] using h.symm

end GlobalTheory.CompanionTheory.FFNorm
end

section

namespace GlobalTheory.CompanionTheory.ProdQuotient

theorem support_mul_out_finite (G₁ G₂ : Type) [Group G₁] [Group G₂] (K₁ : Subgroup G₁)
    (K₂ : Subgroup G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ)
    (h₁ : (Function.support fun q : G₁ ⧸ K₁ => f₁ q.out).Finite)
    (h₂ : (Function.support fun q : G₂ ⧸ K₂ => f₂ q.out).Finite)
    (i₁ : ∀ k ∈ K₁, ∀ g, f₁ (g * k) = f₁ g) (i₂ : ∀ k ∈ K₂, ∀ g, f₂ (g * k) = f₂ g) :
    (Function.support fun q : (G₁ × G₂) ⧸ K₁.prod K₂ => f₁ q.out.1 * f₂ q.out.2).Finite := by
  let φ : (G₁ × G₂) ⧸ K₁.prod K₂ → (G₁ ⧸ K₁) × (G₂ ⧸ K₂) :=
    fun q => ((q.out.1 : G₁ ⧸ K₁), (q.out.2 : G₂ ⧸ K₂))
  have hinj : Function.Injective φ := by
    intro a b hab
    have e₁ : ((a.out.1 : G₁ ⧸ K₁)) = (b.out.1 : G₁ ⧸ K₁) := congrArg Prod.fst hab
    have e₂ : ((a.out.2 : G₂ ⧸ K₂)) = (b.out.2 : G₂ ⧸ K₂) := congrArg Prod.snd hab
    rw [QuotientGroup.eq] at e₁ e₂
    have key : ((a.out : G₁ × G₂) : (G₁ × G₂) ⧸ K₁.prod K₂) = (b.out : G₁ × G₂) := by
      rw [QuotientGroup.eq]
      exact Subgroup.mem_prod.mpr ⟨e₁, e₂⟩
    simpa using key
  have inv₁ : ∀ g : G₁, f₁ (g : G₁ ⧸ K₁).out = f₁ g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₁ g
    rw [hk]
    exact i₁ k k.2 g
  have inv₂ : ∀ g : G₂, f₂ (g : G₂ ⧸ K₂).out = f₂ g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₂ g
    rw [hk]
    exact i₂ k k.2 g
  refine ((h₁.prod h₂).preimage hinj.injOn).subset ?_
  intro q hq
  have hq' : f₁ q.out.1 * f₂ q.out.2 ≠ 0 := hq
  refine ⟨?_, ?_⟩
  · change f₁ (q.out.1 : G₁ ⧸ K₁).out ≠ 0
    rw [inv₁]
    exact left_ne_zero_of_mul hq'
  · change f₂ (q.out.2 : G₂ ⧸ K₂).out ≠ 0
    rw [inv₂]
    exact right_ne_zero_of_mul hq'

end GlobalTheory.CompanionTheory.ProdQuotient
end

section

open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.TopGroup

theorem homeomorph_prod_of_closed_complements :
    ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
      [T2Space Q] [SecondCountableTopology Q] (N M : Subgroup Q),
      IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) →
      (∀ x, x ∈ N → x ∈ M → x = 1) →
      ∃ Φ : (N × M) ≃ₜ Q, ∀ p, Φ p = (p.1 : Q) * (p.2 : Q) := by
  intro Q _ _ _ _ _ _ N M hN hM hprod hint
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace M := hM.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N :=
    TopologicalSpace.Subtype.secondCountableTopology (N : Set Q)
  haveI : SecondCountableTopology M :=
    TopologicalSpace.Subtype.secondCountableTopology (M : Set Q)
  haveI : SigmaCompactSpace (N × M) := sigmaCompactSpace_of_locallyCompact_secondCountable
  letI act : MulAction (N × M) Q :=
    { smul := fun p q => (p.1 : Q) * q * (p.2 : Q)⁻¹
      one_smul := fun q => by
        change ((1 : N) : Q) * q * ((1 : M) : Q)⁻¹ = q
        simp
      mul_smul := fun p r q => by
        change ((p.1 * r.1 : N) : Q) * q * ((p.2 * r.2 : M) : Q)⁻¹ =
          (p.1 : Q) * ((r.1 : Q) * q * (r.2 : Q)⁻¹) * (p.2 : Q)⁻¹
        simp [mul_assoc] }
  have hsmul : ∀ (p : N × M) (q : Q), p • q = (p.1 : Q) * q * (p.2 : Q)⁻¹ := fun _ _ => rfl
  haveI : ContinuousSMul (N × M) Q := ⟨by
    have : (fun x : (N × M) × Q => x.1 • x.2) =
        fun x : (N × M) × Q => ((x.1.1 : Q)) * x.2 * ((x.1.2 : Q))⁻¹ := rfl
    rw [this]
    fun_prop⟩
  haveI : MulAction.IsPretransitive (N × M) Q := ⟨fun x y => by
    obtain ⟨n₁, hn₁, m₁, hm₁, rfl⟩ := hprod x
    obtain ⟨n₂, hn₂, m₂, hm₂, rfl⟩ := hprod y
    refine ⟨(⟨n₂ * n₁⁻¹, N.mul_mem hn₂ (N.inv_mem hn₁)⟩,
      ⟨m₂⁻¹ * m₁, M.mul_mem (M.inv_mem hm₂) hm₁⟩), ?_⟩
    rw [hsmul]
    simp [mul_assoc]⟩
  have hopen₀ : IsOpenMap (fun g : N × M => g • (1 : Q)) := isOpenMap_smul_of_sigmaCompact (1 : Q)
  let e : (N × M) ≃ₜ (N × M) := (Homeomorph.refl N).prodCongr (Homeomorph.inv M)
  let f : N × M → Q := fun p => (p.1 : Q) * (p.2 : Q)
  have hf : f = (fun g : N × M => g • (1 : Q)) ∘ e := by
    funext p
    change (p.1 : Q) * (p.2 : Q) = ((e p).1 : Q) * 1 * (((e p).2 : M) : Q)⁻¹
    simp [e]
  have hopen : IsOpenMap f := by
    rw [hf]
    exact hopen₀.comp e.isOpenMap
  have hcont : Continuous f := by fun_prop
  have hinj : Function.Injective f := by
    rintro ⟨⟨n₁, hn₁⟩, ⟨m₁, hm₁⟩⟩ ⟨⟨n₂, hn₂⟩, ⟨m₂, hm₂⟩⟩ h
    have h' : n₁ * m₁ = n₂ * m₂ := h
    have h1 : n₂⁻¹ * n₁ = m₂ * m₁⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, h']
    have h2 : n₂⁻¹ * n₁ = 1 :=
      hint _ (N.mul_mem (N.inv_mem hn₂) hn₁) (h1 ▸ M.mul_mem hm₂ (M.inv_mem hm₁))
    have h3 : n₁ = n₂ := by
      rw [inv_mul_eq_one] at h2
      exact h2.symm
    have h4 : m₁ = m₂ := by
      subst h3
      exact mul_left_cancel h'
    subst h3
    subst h4
    rfl
  have hsurj : Function.Surjective f := fun q => by
    obtain ⟨n, hn, m, hm, rfl⟩ := hprod q
    exact ⟨(⟨n, hn⟩, ⟨m, hm⟩), rfl⟩
  exact ⟨(Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen,
    fun _ => rfl⟩

end GlobalTheory.CompanionTheory.TopGroup
end

section

open Matrix
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.Topology

theorem isCompact_addSubgroup_sup : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A B : AddSubgroup X), IsCompact (A : Set X) → IsCompact (B : Set X) → IsCompact ((A ⊔ B : AddSubgroup X) : Set X) := by
  intro X _ _ _ A B hA hB
  have h : ((A ⊔ B : AddSubgroup X) : Set X) = (A : Set X) + (B : Set X) := by
    ext x
    simp only [SetLike.mem_coe, AddSubgroup.mem_sup, Set.mem_add]
  rw [h]
  exact hA.add hB

end GlobalTheory.CompanionTheory.Topology
end

section

namespace GlobalTheory.CompanionTheory.Counting

theorem card_eq_card_ker_mul_card_range (R A B : Type) [Ring R] [AddCommGroup A] [Module R A] [Finite A]
    [AddCommGroup B] [Module R B] (f : A →ₗ[R] B) :
    Nat.card A = Nat.card ↥(LinearMap.ker f) * Nat.card ↥(LinearMap.range f) := by
  have h1 : Nat.card (A ⧸ LinearMap.ker f) = Nat.card ↥(LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have h2 : Nat.card A = Nat.card (A ⧸ (LinearMap.ker f).toAddSubgroup) * Nat.card (LinearMap.ker f).toAddSubgroup :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h3 : Nat.card (A ⧸ (LinearMap.ker f).toAddSubgroup) = Nat.card (A ⧸ LinearMap.ker f) := rfl
  have h4 : Nat.card (LinearMap.ker f).toAddSubgroup = Nat.card ↥(LinearMap.ker f) := rfl
  rw [h2, h3, h4, h1, Nat.mul_comm]

end GlobalTheory.CompanionTheory.Counting
end

section

namespace GlobalTheory.CompanionTheory.Counting

theorem card_comap_eq_card_ker_mul_card_range_inf :
    ∀ (R A X : Type) [Ring R] [AddCommGroup A] [Module R A] [Finite A] [AddCommGroup X]
      [Module R X] (f : A →ₗ[R] X) (U : Submodule R X),
      Nat.card ↥(U.comap f) = Nat.card ↥(LinearMap.ker f) * Nat.card ↥(LinearMap.range f ⊓ U) := by
  intro R A X _ _ _ _ _ _ f U
  have hker : LinearMap.ker (f.domRestrict (U.comap f)) ≃ LinearMap.ker f :=
    { toFun := fun x => ⟨x.1.1, LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp x.2)⟩
      invFun := fun y => ⟨⟨y.1, by
          rw [Submodule.mem_comap, LinearMap.mem_ker.mp y.2]
          exact U.zero_mem⟩, LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp y.2)⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  have hrange : LinearMap.range (f.domRestrict (U.comap f)) = LinearMap.range f ⊓ U := by
    rw [LinearMap.range_domRestrict, Submodule.map_comap_eq]
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (f.domRestrict (U.comap f))),
    Nat.card_congr hker, Nat.card_congr (f.domRestrict (U.comap f)).quotKerEquivRange.toEquiv,
    hrange]

end GlobalTheory.CompanionTheory.Counting
end

section

noncomputable section

open Matrix Finset

namespace GlobalTheory.CompanionTheory.RealCount.Tope

variable {n : ℕ}

abbrev LP (n : ℕ) := AddMonoidAlgebra ℂ (Fin n → ℤ)

def chr (z : Fin n → ℂˣ) : Multiplicative (Fin n → ℤ) →* ℂ where
  toFun μ := ∏ a, ((z a ^ (Multiplicative.toAdd μ a) : ℂˣ) : ℂ)
  map_one' := by simp
  map_mul' μ ν := by
    simp only [toAdd_mul, Pi.add_apply, _root_.zpow_add, Units.val_mul, Finset.prod_mul_distrib]

def evL (z : Fin n → ℂˣ) : LP n →ₐ[ℂ] ℂ := AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ) (chr z)

def altL (m : Fin n → ℤ) : LP n :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • AddMonoidAlgebra.single (fun i => m (σ i)) (1 : ℂ)

def delZ (n : ℕ) : Fin n → ℤ := fun j => ((n - 1 - (j : ℕ) : ℕ) : ℤ)

def pPL (n : ℕ) : LP n :=
  ∏ a : Fin n, ∏ b : Fin n, (1 + AddMonoidAlgebra.single (Pi.single a 1 - Pi.single b 1 : Fin n → ℤ) (1 : ℂ))

def frL (n : ℕ) : LP n →ₐ[ℂ] LP n :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (2 • AddMonoidHom.id (Fin n → ℤ))

def cPoly (s : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) : LP n :=
  ∑ μ ∈ s, AddMonoidAlgebra.single μ (c μ)

end GlobalTheory.CompanionTheory.RealCount.Tope
end
end

section

namespace GlobalTheory.CompanionTheory.SemistableSpecial

open MvPolynomial

theorem isRadical_prod_X {k σ : Type} [CommRing k] [IsDomain k] [UniqueFactorizationMonoid k]
    (s : Finset σ) : IsRadical (∏ i ∈ s, (X i : MvPolynomial σ k)) := by
  classical
  have key : ∀ (t : Finset σ) (y : MvPolynomial σ k),
      (∀ i ∈ t, (X i : MvPolynomial σ k) ∣ y) → (∏ i ∈ t, (X i : MvPolynomial σ k)) ∣ y := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro y _; simp
    | @insert a t ha ih =>
      intro y hy
      obtain ⟨z, rfl⟩ := hy a (Finset.mem_insert_self a t)
      rw [Finset.prod_insert ha]
      refine mul_dvd_mul_left _ (ih z ?_)
      intro i hi
      have hXi : Prime (X i : MvPolynomial σ k) := MvPolynomial.X_prime
      rcases hXi.dvd_or_dvd (hy i (Finset.mem_insert_of_mem hi)) with h | h
      · exfalso
        rw [MvPolynomial.X_dvd_X] at h
        exact ha (h ▸ hi)
      · exact h
  intro n y hy
  apply key
  intro i hi
  have hXi : Prime (X i : MvPolynomial σ k) := MvPolynomial.X_prime
  exact hXi.dvd_of_dvd_pow
    (dvd_trans (Finset.dvd_prod_of_mem (fun j => (X j : MvPolynomial σ k)) hi) hy)

theorem isRadical_span_sup {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {σ : Type} (s : Finset σ) :
    (Ideal.span {(∏ i ∈ s, (X i : MvPolynomial σ O)) - C ϖ} ⊔
      Ideal.span {(C ϖ : MvPolynomial σ O)}).IsRadical := by
  classical
  set P : MvPolynomial σ O := ∏ i ∈ s, X i with hP
  set φ : MvPolynomial σ O →+* MvPolynomial σ (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hφ
  have hker : RingHom.ker φ = Ideal.span {C ϖ} := by
    rw [hφ, MvPolynomial.ker_map, IsLocalRing.ker_residue,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hφP : φ P = ∏ i ∈ s, (X i : MvPolynomial σ (IsLocalRing.ResidueField O)) := by
    rw [hP, hφ, map_prod]
    simp only [MvPolynomial.map_X]
  have hCϖ : φ (C ϖ) = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self _
  have hPmem : P ∈ Ideal.span {P - C ϖ} ⊔ Ideal.span {(C ϖ : MvPolynomial σ O)} := by
    have h := Ideal.add_mem (Ideal.span {P - C ϖ} ⊔ Ideal.span {(C ϖ : MvPolynomial σ O)})
      (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (P - C ϖ)))
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (C ϖ : MvPolynomial σ O)))
    rwa [sub_add_cancel] at h
  have hmem : ∀ x, x ∈ Ideal.span {P - C ϖ} ⊔ Ideal.span {(C ϖ : MvPolynomial σ O)} ↔
      φ P ∣ φ x := by
    intro x
    constructor
    · intro hx
      have hle : Ideal.span {P - C ϖ} ⊔ Ideal.span {(C ϖ : MvPolynomial σ O)} ≤
          Ideal.comap φ (Ideal.span {φ P}) := by
        refine sup_le ?_ ?_
        · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
            map_sub, hCϖ, sub_zero]
          exact Ideal.mem_span_singleton_self _
        · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hCϖ]
          exact Ideal.zero_mem _
      exact Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp (hle hx))
    · rintro ⟨g, hg⟩
      obtain ⟨g', rfl⟩ := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective g
      have hdiff : x - P * g' ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker, map_sub, map_mul, hg, hφ]
        exact sub_self _
      rw [hker] at hdiff
      have hx : x = (x - P * g') + P * g' := by ring
      rw [hx]
      exact Ideal.add_mem _ (Ideal.mem_sup_right hdiff) (Ideal.mul_mem_right _ _ hPmem)
  unfold Ideal.IsRadical
  intro x hx
  rw [Ideal.mem_radical_iff] at hx
  obtain ⟨n, hn⟩ := hx
  rw [hmem] at hn
  rw [hmem]
  rw [map_pow, hφP] at hn
  rw [hφP]
  exact isRadical_prod_X s n (φ x) hn

theorem special_fibre_isReduced : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O), Irreducible ϖ → ∀ (m r : ℕ), 1 ≤ r → r ≤ m →
    IsReduced ((MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) ⧸ Ideal.span {algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) ϖ}) := by
  intro O _ _ _ ϖ hϖ m r _ _
  set J : Ideal (MvPolynomial (Fin m) O) := Ideal.span {(∏ i ∈ Finset.univ.filter
    (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ} with hJ
  have e : Ideal.span {algebraMap O (MvPolynomial (Fin m) O ⧸ J) ϖ} =
      Ideal.map (Ideal.Quotient.mk J) (Ideal.span {(MvPolynomial.C ϖ : MvPolynomial (Fin m) O)}) := by
    rw [Ideal.map_span, Set.image_singleton, ← Ideal.Quotient.mk_algebraMap,
      MvPolynomial.algebraMap_eq]
  rw [e]
  have : IsReduced (MvPolynomial (Fin m) O ⧸
      (J ⊔ Ideal.span {(MvPolynomial.C ϖ : MvPolynomial (Fin m) O)})) := by
    rw [← Ideal.isRadical_iff_quotient_reduced]
    exact isRadical_span_sup hϖ (Finset.univ.filter (fun i : Fin m => (i : ℕ) < r))
  exact isReduced_of_injective
    (DoubleQuot.quotQuotEquivQuotSup J (Ideal.span {(MvPolynomial.C ϖ : MvPolynomial (Fin m) O)}))
    (RingEquiv.injective _)

end GlobalTheory.CompanionTheory.SemistableSpecial
end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Dblock

theorem integral_norm_sq_le_toReal_lintegral_enorm_sq {α : Type} [MeasurableSpace α] (μ : Measure α) (f : α → ℂ) :
    ∫ x, ‖f x‖ ^ 2 ∂μ ≤ (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ).toReal := by
  by_cases h : Integrable (fun x => ‖f x‖ ^ 2) μ
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => by positivity) h.aestronglyMeasurable]
    apply le_of_eq
    congr 1
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  · rw [integral_undef h]
    exact ENNReal.toReal_nonneg

end GlobalTheory.CompanionTheory.Dblock
end
