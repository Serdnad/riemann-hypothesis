module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle067
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle083
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle084
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle077
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle088
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle090
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle089
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeries
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
public import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Prime
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Polynomial

namespace GlobalTheory

theorem etale_of_separable_charpoly_mulLeft (E A : Type) [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (h : (LinearMap.mulLeft E g).charpoly.Separable) :
    Algebra.Etale E A := by
  have hd := GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable (LinearMap.mulLeft E g) h
  have h2 : minpoly E (LinearMap.mulLeft E g) = minpoly E g :=
    minpoly.algHom_eq (Algebra.lmul E A) (Algebra.lmul_injective) g
  have hint : IsIntegral E g := Algebra.IsIntegral.isIntegral g
  have hm : (minpoly E g).Monic := minpoly.monic hint
  have hd' : minpoly E g ∣ (LinearMap.mulLeft E g).charpoly := by
    rw [← h2]; exact LinearMap.minpoly_dvd_charpoly _
  rw [h2] at hd
  have heq : minpoly E g = (LinearMap.mulLeft E g).charpoly :=
    eq_of_monic_of_associated hm (LinearMap.charpoly_monic _) (associated_of_dvd_dvd hd' hd)
  have hsep : (minpoly E g).Separable := heq ▸ h
  have hdeg : (minpoly E g).natDegree = Module.finrank E A := by
    rw [heq, LinearMap.charpoly_natDegree]
  haveI : Module.Finite E (AdjoinRoot (minpoly E g)) := hm.finite_adjoinRoot
  let φ : AdjoinRoot (minpoly E g) →ₐ[E] A := AdjoinRoot.liftAlgHom (minpoly E g) (Algebra.ofId E A) g (minpoly.aeval E g)
  have hli : LinearIndependent E fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ) :=
    linearIndependent_pow g
  let b := basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp [hdeg])
  have hsurj : Function.Surjective φ.toLinearMap := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨AdjoinRoot.root (minpoly E g) ^ (i : ℕ), ?_⟩
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank', AlgHom.toLinearMap_apply, map_pow]
    congr 1
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have hfr : Module.finrank E (AdjoinRoot (minpoly E g)) = Module.finrank E A := by
    rw [(AdjoinRoot.powerBasis' hm).finrank]; simpa using hdeg
  have hinj : Function.Injective φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).2 hsurj
  let e : AdjoinRoot (minpoly E g) ≃ₐ[E] A := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hu : IsUnit (AdjoinRoot.mk (minpoly E g) (minpoly E g).derivative) := by
    obtain ⟨a, c, hac⟩ := hsep
    have := congrArg (AdjoinRoot.mk (minpoly E g)) hac
    rw [map_add (f := _), map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one] at this
    exact isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact this⟩
  have := GlobalTheory.etale_adjoinRoot_of_isUnit_derivative hm hu
  exact Algebra.Etale.of_equiv e

end GlobalTheory
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.integralClosure_fg_dvr_of_separable_charpoly : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  first | exact @GlobalTheory.IntClosureSep.integralClosure_fg_of_separable_charpoly | exact GlobalTheory.IntClosureSep.integralClosure_fg_of_separable_charpoly | (intros; apply GlobalTheory.IntClosureSep.integralClosure_fg_of_separable_charpoly <;> assumption)
end

section

open scoped BigOperators

theorem _root_.GlobalTheory.T.brauerNesbitt_exists_equiv_of_charpoly_eq' : ∀ {k Γ V W : Type} [Field k] [Monoid Γ] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W] (ρ : Representation k Γ V) (σ : Representation k Γ W), ρ.IsSemisimpleRepresentation → σ.IsSemisimpleRepresentation → (∀ a : MonoidAlgebra k Γ, LinearMap.charpoly (ρ.asAlgebraHom a) = LinearMap.charpoly (σ.asAlgebraHom a)) → ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  first | exact @GlobalTheory.CharpolyIso.exists_equiv_of_charpoly_eq' | exact GlobalTheory.CharpolyIso.exists_equiv_of_charpoly_eq' | (intros; apply GlobalTheory.CharpolyIso.exists_equiv_of_charpoly_eq' <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

theorem _root_.GlobalTheory.T.det_commutator_map_eq_charpoly_resultant : ∀ (E : Type) [Field E] (V₁ V₂ : Type) [AddCommGroup V₁] [Module E V₁] [FiniteDimensional E V₁] [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂] (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂), LinearMap.det (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) = resultant f₁.charpoly f₂.charpoly := by
  first | exact @GlobalTheory.DetAdResultant.det_ad_eq_resultant | exact GlobalTheory.DetAdResultant.det_ad_eq_resultant | (intros; apply GlobalTheory.DetAdResultant.det_ad_eq_resultant <;> assumption)
end

section

open MvPolynomial

namespace GlobalTheory.HTCPoly

theorem prod_zpow_eq {ι G : Type} [CommGroup G] (u : G) (s : Finset ι) (a : ι → ℤ) :
    ∏ i ∈ s, u ^ a i = u ^ ∑ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add]

variable {C n : Type} [Field C] [Fintype n] [DecidableEq n]

def wt (k : n → ℤ) (m : (n × n) →₀ ℕ) : ℤ := ∑ i : n × n, (m i : ℤ) * k i.2

theorem unit_prod (k : n → ℤ) (u : Cˣ) (m : (n × n) →₀ ℕ) :
    ∏ i : n × n, ((u ^ k i.2 : Cˣ) : C) ^ (m i) = ((u ^ wt k m : Cˣ) : C) := by
  have h : ∏ i : n × n, (u ^ k i.2) ^ (m i) = u ^ wt k m := by
    rw [wt, ← prod_zpow_eq]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  rw [← h, Units.coe_prod]
  simp [Units.val_pow_eq_pow_val]

theorem eval_eq_sum {σ : Type} [Fintype σ] (x : σ → C) (p : MvPolynomial σ C)
    (s : Finset (σ →₀ ℕ)) (hs : p.support ⊆ s) :
    eval x p = ∑ m ∈ s, AddMonoidAlgebra.coeff p m * ∏ i, x i ^ m i := by
  rw [eval_eq']
  refine Finset.sum_subset hs fun m _ hm => ?_
  have : AddMonoidAlgebra.coeff p m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  rw [this, zero_mul]

theorem eval_mul_diag (k : n → ℤ) (u : Cˣ) (y : Matrix n n C) (p : MvPolynomial (n × n) C)
    (s : Finset ((n × n) →₀ ℕ)) (hs : p.support ⊆ s) :
    eval (fun ij => (y * Matrix.diagonal (fun j => ((u ^ k j : Cˣ) : C))) ij.1 ij.2) p
      = ∑ m ∈ s, ((u ^ wt k m : Cˣ) : C) * AddMonoidAlgebra.coeff p m * ∏ i : n × n, y i.1 i.2 ^ m i := by
  rw [eval_eq_sum _ _ s hs]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp_rw [Matrix.mul_diagonal, mul_pow, Finset.prod_mul_distrib, unit_prod]
  ring

variable {Γ : Type} [Group Γ] [MulSemiringAction Γ C]

def vanJ (ρ : Γ →* Matrix.GeneralLinearGroup n C) (P : Matrix n n C) :
    Submodule C (((n × n) →₀ ℕ) →₀ C) where
  carrier := {φ | ∀ γ, eval (fun ij : n × n => ((ρ γ : Matrix n n C) * P) ij.1 ij.2)
      (AddMonoidAlgebra.ofCoeff φ : MvPolynomial (n × n) C) = 0}
  add_mem' := by
    intro a b ha hb γ
    simp only [Set.mem_setOf_eq] at *
    rw [show (AddMonoidAlgebra.ofCoeff (a + b) : MvPolynomial (n × n) C) =
      AddMonoidAlgebra.ofCoeff a + AddMonoidAlgebra.ofCoeff b by simp, map_add (f := _), ha γ, hb γ, add_zero]
  zero_mem' := by
    intro γ
    simp
  smul_mem' := by
    intro c a ha γ
    simp only [Set.mem_setOf_eq] at *
    rw [show (AddMonoidAlgebra.ofCoeff (c • a) : MvPolynomial (n × n) C) =
      c • AddMonoidAlgebra.ofCoeff a by simp, smul_eval, ha γ, mul_zero]

end GlobalTheory.HTCPoly

namespace GlobalTheory.HTCPoly
variable {C n : Type} [Field C] [Fintype n] [DecidableEq n]
variable {Γ : Type} [Group Γ] [MulSemiringAction Γ C]

theorem mem_vanJ (ρ : Γ →* Matrix.GeneralLinearGroup n C) (P : Matrix n n C)
    (φ : ((n × n) →₀ ℕ) →₀ C) :
    φ ∈ vanJ ρ P ↔ ∀ γ, eval (fun ij : n × n => ((ρ γ : Matrix n n C) * P) ij.1 ij.2)
      (AddMonoidAlgebra.ofCoeff φ : MvPolynomial (n × n) C) = 0 := Iff.rfl

theorem vanJ_stable (χ : Γ →* Cˣ) (ρ : Γ →* Matrix.GeneralLinearGroup n C)
    (hfix : ∀ (g γ : Γ) (i j : n), g • (ρ γ : Matrix n n C) i j = (ρ γ : Matrix n n C) i j)
    (P : Matrix n n C) (k : n → ℤ)
    (hP : ∀ g : Γ, (ρ g : Matrix n n C) * P.map (fun a => g • a) =
      P * Matrix.diagonal (fun i => ((χ g ^ k i : Cˣ) : C))) :
    ∀ g : Γ, ∀ φ ∈ vanJ ρ P, ∃ ψ ∈ vanJ ρ P,
      ∀ m, ψ m = ((χ g ^ wt k m : Cˣ) : C) * (g • φ m) := by
  intro g φ hφ
  refine ⟨Finsupp.onFinset φ.support (fun m => ((χ g ^ wt k m : Cˣ) : C) * (g • φ m)) ?_, ?_,
    fun m => Finsupp.onFinset_apply⟩
  · intro m hm
    rw [Finsupp.mem_support_iff]
    intro h0
    apply hm
    rw [h0, smul_zero, mul_zero]
  · rw [mem_vanJ] at hφ ⊢
    intro γ
    set σg := MulSemiringAction.toRingHom Γ C g
    set p : MvPolynomial (n × n) C := AddMonoidAlgebra.ofCoeff φ
    have hfix' : (ρ (γ * g) : Matrix n n C).map σg = ρ (γ * g) := by
      ext i j
      exact hfix g (γ * g) i j
    have key : (ρ γ : Matrix n n C) * P * Matrix.diagonal (fun j => ((χ g ^ k j : Cˣ) : C)) =
        ((ρ (γ * g) : Matrix n n C) * P).map σg := by
      calc (ρ γ : Matrix n n C) * P * Matrix.diagonal (fun j => ((χ g ^ k j : Cˣ) : C))
          = (ρ γ : Matrix n n C) * (P * Matrix.diagonal (fun j => ((χ g ^ k j : Cˣ) : C))) :=
            Matrix.mul_assoc _ _ _
        _ = (ρ γ : Matrix n n C) * ((ρ g : Matrix n n C) * P.map (fun a => g • a)) := by rw [hP g]
        _ = ((ρ (γ * g) : Matrix n n C) * P).map σg := by
            rw [Matrix.map_mul, hfix', map_mul, Units.val_mul, Matrix.mul_assoc]
            rfl
    have e1 : eval (fun ij : n × n => ((ρ γ : Matrix n n C) * P) ij.1 ij.2)
        (AddMonoidAlgebra.ofCoeff (Finsupp.onFinset φ.support
          (fun m => ((χ g ^ wt k m : Cˣ) : C) * (g • φ m)) (by
            intro m hm
            rw [Finsupp.mem_support_iff]
            intro h0
            apply hm
            rw [h0, smul_zero, mul_zero])) : MvPolynomial (n × n) C)
        = ∑ m ∈ φ.support, ((χ g ^ wt k m : Cˣ) : C) * AddMonoidAlgebra.coeff (map σg p) m *
            ∏ i : n × n, ((ρ γ : Matrix n n C) * P) i.1 i.2 ^ m i := by
      refine (eval_eq_sum _ _ φ.support ?_).trans ?_
      · intro m hm
        rw [MvPolynomial.mem_support_iff] at hm
        rw [Finsupp.mem_support_iff]
        intro h0
        apply hm
        show ((χ g ^ wt k m : Cˣ) : C) * (g • φ m) = 0
        rw [h0, smul_zero, mul_zero]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [coeff_map]
      rfl
    rw [e1, ← eval_mul_diag k (χ g) _ (map σg p) φ.support (MvPolynomial.support_map_subset _ _), key]
    have h2 := eval₂_comp_left σg (RingHom.id C)
      (fun ij : n × n => ((ρ (γ * g) : Matrix n n C) * P) ij.1 ij.2) p
    rw [RingHom.comp_id] at h2
    rw [eval_map]
    calc eval₂ σg (fun ij : n × n => (((ρ (γ * g) : Matrix n n C) * P).map σg) ij.1 ij.2) p
        = σg (eval₂ (RingHom.id C) (fun ij : n × n => ((ρ (γ * g) : Matrix n n C) * P) ij.1 ij.2) p) :=
          h2.symm
      _ = 0 := by
          rw [show eval₂ (RingHom.id C) (fun ij : n × n => ((ρ (γ * g) : Matrix n n C) * P) ij.1 ij.2) p
            = eval (fun ij : n × n => ((ρ (γ * g) : Matrix n n C) * P) ij.1 ij.2) p from rfl, hφ (γ * g),
            map_zero]

end GlobalTheory.HTCPoly

namespace GlobalTheory.HTCPoly

theorem vanish_at_cocharacter : ∀ {C Γ n : Type} [Field C] [Group Γ] [MulSemiringAction Γ C] [Fintype n] [DecidableEq n] (χ : Γ →* Cˣ), (∀ m : ℤ, m ≠ 0 → ∀ a : C, (∀ g : Γ, g • a = ((χ g ^ m : Cˣ) : C) * a) → a = 0) → ∀ (ρ : Γ →* Matrix.GeneralLinearGroup n C), (∀ (g γ : Γ) (i j : n), g • (ρ γ : Matrix n n C) i j = (ρ γ : Matrix n n C) i j) → ∀ (P : Matrix.GeneralLinearGroup n C) (k : n → ℤ), (∀ g : Γ, (ρ g : Matrix n n C) * (P : Matrix n n C).map (fun a => g • a) = (P : Matrix n n C) * Matrix.diagonal (fun i => ((χ g ^ k i : Cˣ) : C))) → ∀ f : MvPolynomial (n × n) C, (∀ γ : Γ, MvPolynomial.eval (fun ij => (ρ γ : Matrix n n C) ij.1 ij.2) f = 0) → ∀ t : Cˣ, MvPolynomial.eval (fun ij => ((P : Matrix n n C) * Matrix.diagonal (fun i => ((t ^ k i : Cˣ) : C)) * ((P⁻¹ : Matrix.GeneralLinearGroup n C) : Matrix n n C)) ij.1 ij.2) f = 0 := by
  intro C Γ n _ _ _ _ _ χ hT ρ hfix P k hP f hf t
  set Pm : Matrix n n C := (P : Matrix n n C) with hPm
  set Qm : Matrix n n C := ((P⁻¹ : Matrix.GeneralLinearGroup n C) : Matrix n n C) with hQm
  have hPQ : Pm * Qm = 1 := by
    rw [hPm, hQm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  let q : n × n → MvPolynomial (n × n) C := fun ij => ∑ l, X (ij.1, l) * MvPolynomial.C (Qm l ij.2)
  have hφ : ∀ y : Matrix n n C, eval (fun ij : n × n => y ij.1 ij.2) (aeval q f) =
      eval (fun ij : n × n => (y * Qm) ij.1 ij.2) f := by
    intro y
    show aeval (fun ij : n × n => y ij.1 ij.2) (aeval q f) =
      aeval (fun ij : n × n => (y * Qm) ij.1 ij.2) f
    rw [← AlgHom.comp_apply, comp_aeval]
    refine congrArg (fun F : n × n → C => aeval F f) (funext fun ij => ?_)
    simp [q, Matrix.mul_apply]
  set p : MvPolynomial (n × n) C := aeval q f with hp
  have hpJ : AddMonoidAlgebra.coeff p ∈ vanJ ρ Pm := by
    rw [mem_vanJ]
    intro γ
    show eval _ p = 0
    rw [hφ, Matrix.mul_assoc, hPQ, Matrix.mul_one]
    exact hf γ
  have hgr := GlobalTheory.T.filter_weight_mem_of_tate_graded_stable χ hT (wt k) (vanJ ρ Pm) (vanJ_stable χ ρ hfix Pm k hP) _ hpJ
  have hzero : ∀ d : ℤ, eval (fun ij : n × n => Pm ij.1 ij.2)
      (AddMonoidAlgebra.ofCoeff ((AddMonoidAlgebra.coeff p).filter (fun m => wt k m = d)) :
        MvPolynomial (n × n) C) = 0 := by
    intro d
    have h1 := (mem_vanJ ρ Pm _).mp (hgr d) 1
    rwa [map_one, Units.val_one, Matrix.one_mul] at h1
  rw [← hφ (Pm * Matrix.diagonal (fun i => ((t ^ k i : Cˣ) : C)))]
  rw [eval_mul_diag k t Pm p p.support subset_rfl]
  rw [← Finset.sum_fiberwise_of_maps_to (t := p.support.image (wt k)) (g := wt k)
    (fun m hm => Finset.mem_image_of_mem _ hm)]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [← mul_zero ((t ^ d : Cˣ) : C), ← hzero d,
    eval_eq_sum _ _ (p.support.filter (fun m => wt k m = d)) ?_, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_filter] at hm
    have hc : AddMonoidAlgebra.coeff (AddMonoidAlgebra.ofCoeff ((AddMonoidAlgebra.coeff p).filter
        (fun m => wt k m = d)) : MvPolynomial (n × n) C) m = AddMonoidAlgebra.coeff p m :=
      Finsupp.filter_apply_pos _ _ hm.2
    rw [hc, hm.2]
    ring
  · intro m hm
    rw [MvPolynomial.mem_support_iff] at hm
    rw [Finset.mem_filter, MvPolynomial.mem_support_iff]
    by_contra hne
    apply hm
    show (Finsupp.filter (fun m => wt k m = d) (AddMonoidAlgebra.coeff p)) m = 0
    by_cases hw : wt k m = d
    · rw [Finsupp.filter_apply_pos (fun m => wt k m = d) _ hw]
      by_contra h
      exact hne ⟨h, hw⟩
    · exact Finsupp.filter_apply_neg _ _ hw

end GlobalTheory.HTCPoly
end

section

open NumberField IsDedekindDomain
open scoped Classical

namespace GlobalTheory

open NumberField IsDedekindDomain in
open scoped Classical in
private lemma exists_prime_liesOver_absNorm_eq_pow (K : Type) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) :
    ∃ q : ℕ, q.Prime ∧ P.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) ∧
      ∃ f : ℕ, Ideal.absNorm P.asIdeal = q ^ f := by
  set I : Ideal ℤ := P.asIdeal.under ℤ with hI
  have hN : (Ideal.absNorm P.asIdeal : ℤ) ∈ I := by
    rw [hI, Ideal.mem_comap]
    simpa using Ideal.absNorm_mem P.asIdeal
  have hN0 : (Ideal.absNorm P.asIdeal : ℤ) ≠ 0 := by
    have := _root_.GlobalTheory.Mem.RayPrimes.two_le_absNorm P
    omega
  have hIbot : I ≠ ⊥ := fun h => hN0 (by simpa [h] using hN)
  have hprime := Submodule.IsPrincipal.prime_generator_of_isPrime I hIbot
  set g := Submodule.IsPrincipal.generator I
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hprime, ?_, ?_⟩
  · refine ⟨?_⟩
    rw [Int.span_natAbs, Ideal.span_singleton_generator]
  · have hpr : Prime ((g.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact hprime.abs
    haveI : P.asIdeal.LiesOver (Ideal.span {((g.natAbs : ℕ) : ℤ)}) :=
      ⟨by rw [Int.span_natAbs, Ideal.span_singleton_generator]⟩
    exact ⟨_, (Ideal.absNorm_eq_pow_inertiaDeg P.asIdeal hpr).trans (by rw [Int.natAbs_natCast])⟩


open NumberField IsDedekindDomain in
open scoped Classical in
theorem _root_.GlobalTheory.summable_inv_absNorm_of_not_prime :
    ∀ (K : Type) [Field K] [NumberField K],
      Summable fun P : {P : HeightOneSpectrum (𝓞 K) // ¬ (Ideal.absNorm P.asIdeal).Prime} =>
        ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹ := by
  intro K _ _
  choose q hq hlies f hf using exists_prime_liesOver_absNorm_eq_pow K
  set d := Module.finrank ℚ K
  have hfib : ∀ (T : Finset {P : HeightOneSpectrum (𝓞 K) // ¬ (Ideal.absNorm P.asIdeal).Prime})
      (r : ℕ), (T.filter fun P => q P.1 = r).card ≤ d := by
    intro T r
    by_cases hr : ∃ P ∈ T, q P.1 = r
    · obtain ⟨P₀, -, rfl⟩ := hr
      have hspan : Ideal.span {((q P₀.1 : ℕ) : ℤ)} ≠ ⊥ := by
        simpa using (hq P₀.1).ne_zero
      haveI hsp : (Ideal.span {((q P₀.1 : ℕ) : ℤ)}).IsPrime :=
        (Ideal.span_singleton_prime (by simpa using (hq P₀.1).ne_zero)).mpr
          (Nat.prime_iff_prime_int.mp (hq P₀.1))
      haveI : (Ideal.span {((q P₀.1 : ℕ) : ℤ)}).IsMaximal := hsp.isMaximal hspan
      calc (T.filter fun P => q P.1 = q P₀.1).card
          ≤ (IsDedekindDomain.primesOverFinset (Ideal.span {((q P₀.1 : ℕ) : ℤ)}) (𝓞 K)).card := by
            refine Finset.card_le_card_of_injOn (fun P => P.1.asIdeal) ?_ ?_
            · intro P hP
              rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hspan]
              have hPq := (Finset.mem_filter.mp hP).2
              haveI := hlies P.1
              exact ⟨P.1.isPrime, by rw [← hPq]; infer_instance⟩
            · intro P _ P' _ h
              exact Subtype.ext (HeightOneSpectrum.ext h)
        _ ≤ d := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hspan
    · push_neg at hr
      rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr hr)]
      exact Nat.zero_le _
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
  refine summable_of_sum_le (c := d * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) (fun P => by positivity) ?_
  intro T
  have hle : ∀ P ∈ T, ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹ ≤ 1 / ((q P.1 : ℕ) : ℝ) ^ 2 := by
    intro P _
    have h2 := _root_.GlobalTheory.Mem.RayPrimes.two_le_absNorm P.1
    have hf2 : 2 ≤ f P.1 := by
      rcases Nat.lt_or_ge (f P.1) 2 with h | h
      · interval_cases hfP : f P.1
        · rw [hf P.1, hfP] at h2; simp at h2
        · exact absurd (by rw [hf P.1, hfP, pow_one]; exact hq P.1) P.2
      · exact h
    rw [one_div]
    apply inv_anti₀ (by have := (hq P.1).pos; positivity)
    rw [hf P.1]
    exact_mod_cast Nat.pow_le_pow_right (hq P.1).pos hf2
  calc ∑ P ∈ T, ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹
      ≤ ∑ P ∈ T, 1 / ((q P.1 : ℕ) : ℝ) ^ 2 := Finset.sum_le_sum hle
    _ = ∑ r ∈ T.image (fun P => q P.1), ∑ P ∈ T with q P.1 = r, 1 / ((q P.1 : ℕ) : ℝ) ^ 2 :=
        (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem _ hP) _).symm
    _ = ∑ r ∈ T.image (fun P => q P.1),
          ((T.filter fun P => q P.1 = r).card : ℝ) * (1 / (r : ℝ) ^ 2) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2]), Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ ∑ r ∈ T.image (fun P => q P.1), (d : ℝ) * (1 / (r : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun r _ => ?_
        gcongr
        exact_mod_cast hfib T r
    _ = d * ∑ r ∈ T.image (fun P => q P.1), 1 / (r : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ d * ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
        gcongr
        exact hsum.sum_le_tsum _ (fun n _ => by positivity)

end GlobalTheory
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.isLocallyConstant_orbit_of_inv_pow_character' : ∀ {p : ℕ} {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ),
    (∀ N : ℕ, IsLocallyConstant (fun g : G => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O))) →
    ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ (m : M) (N : ℕ), (p : O) ^ N • m = 0 →
    IsLocallyConstant (fun g => ρ g m) := by
  first | exact @GlobalTheory.ShapeNeg.isLocallyConstant_orbit_of_inv_pow_character | exact GlobalTheory.ShapeNeg.isLocallyConstant_orbit_of_inv_pow_character | (intros; apply GlobalTheory.ShapeNeg.isLocallyConstant_orbit_of_inv_pow_character <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finiteLength_lattice_projection_quotient : ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (L : Submodule O V) (G B : Submodule K V), L.FG → Disjoint G B → Module.length O (↥(G.restrictScalars O ⊓ (L ⊔ B.restrictScalars O)) ⧸ (L ⊓ G.restrictScalars O).comap (G.restrictScalars O ⊓ (L ⊔ B.restrictScalars O)).subtype) ≠ ⊤ ∨ ¬ (Submodule.span K (L : Set V) = ⊤ ∧ G ⊔ B = ⊤) := by
  first | exact @GlobalTheory.finiteLength_projection_quotient | exact GlobalTheory.finiteLength_projection_quotient | (intros; apply GlobalTheory.finiteLength_projection_quotient <;> assumption)
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.finite_residueField_of_compact_isAdic_dvr : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O], IsAdic (IsLocalRing.maximalIdeal O) →
    Finite (IsLocalRing.ResidueField O) := by
  first | exact @GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic | exact GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic | (intros; apply GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic <;> assumption)
end
