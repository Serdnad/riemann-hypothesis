module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Formalism.CyclotomicNorms.StatementT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle005
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle277
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle250
public import Formalism.LocalRingCardinality.Params
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
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012

@[expose] public section

section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.PrimeLabOrbit

variable {g : ℕ} [hg : Fact g.Prime]

theorem aeval_pow_frob {K : Type} [Field K] [Algebra (ZMod g) K] (n : ℕ) (Q : (ZMod g)[X]) (y : K) :
    aeval (y ^ g ^ n) Q = (aeval y Q) ^ g ^ n := by
  haveI : CharP K g := (Algebra.charP_iff (ZMod g) K g).1 (ZMod.charP g)
  haveI : ExpChar K g := ExpChar.prime hg.out
  rw [← iterateFrobenius_def g n y, ← iterateFrobenius_def g n (aeval y Q), aeval_def, aeval_def, hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

theorem frob_injective {K : Type} [Field K] [Algebra (ZMod g) K] (n : ℕ) :
    Function.Injective (fun y : K => y ^ g ^ n) := by
  haveI : CharP K g := (Algebra.charP_iff (ZMod g) K g).1 (ZMod.charP g)
  haveI : ExpChar K g := ExpChar.prime hg.out
  intro a b h
  apply (iterateFrobenius K g n).injective
  simpa only [iterateFrobenius_def] using h

theorem card_le_of_gen_fixed {L : Type} [Field L] [Algebra (ZMod g) L] [Fintype L] {k : ℕ} (hk : 0 < k) {x : L}
    (hgen : ∀ y : L, ∃ Q : (ZMod g)[X], aeval x Q = y) (hx : x ^ g ^ k = x) : Fintype.card L ≤ g ^ k := by
  have hq : 1 < g ^ k := Nat.one_lt_pow hk.ne' hg.out.one_lt
  set f : L[X] := X ^ (g ^ k) - X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero hq
  have hfix : ∀ y : L, y ^ g ^ k = y := by
    intro y
    obtain ⟨Q, rfl⟩ := hgen y
    rw [← aeval_pow_frob, hx]
  have hsub : (Finset.univ : Finset L) ⊆ f.roots.toFinset := by
    intro y _
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, hf, eval_sub, eval_pow, eval_X, hfix y, sub_self]
  calc Fintype.card L = (Finset.univ : Finset L).card := Finset.card_univ.symm
    _ ≤ f.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := card_roots' f
    _ = g ^ k := Polynomial.natDegree_X_pow_sub_X (R := L) hq

section adjoin

variable {d : ℕ} {P : (ZMod g)[X]} (hP : IsPrimeLab d P)
include hP

theorem finrank_adjoin : haveI := Fact.mk hP.2.1; Module.finrank (ZMod g) (AdjoinRoot P) = d := by
  haveI := Fact.mk hP.2.1
  rw [(AdjoinRoot.powerBasis hP.1.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hP.2.2.2]

theorem adjoin_gen : ∀ y : AdjoinRoot P, ∃ Q : (ZMod g)[X], aeval (AdjoinRoot.root P) Q = y := by
  intro y
  obtain ⟨Q, rfl⟩ := AdjoinRoot.mk_surjective y
  exact ⟨Q, AdjoinRoot.aeval_eq Q⟩

theorem le_of_dvd {k : ℕ} (hk : 0 < k) (hdvd : P ∣ X ^ (g ^ k) - X) : d ≤ k := by
  haveI := Fact.mk hP.2.1
  haveI : Module.Finite (ZMod g) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.1.ne_zero).finite
  haveI : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod g)
  letI : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot P) = g ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, finrank_adjoin hP]
  have hx : (AdjoinRoot.root P) ^ g ^ k = AdjoinRoot.root P := by
    obtain ⟨R, hR⟩ := hdvd
    have h0 : aeval (AdjoinRoot.root P) (X ^ (g ^ k) - X : (ZMod g)[X]) = 0 := by
      rw [hR, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
    rw [map_sub, map_pow, aeval_X, sub_eq_zero] at h0
    exact h0
  have := card_le_of_gen_fixed (L := AdjoinRoot P) (x := AdjoinRoot.root P) hk (adjoin_gen hP) hx
  rw [hcard] at this
  exact (Nat.pow_le_pow_iff_right hg.out.one_lt).1 this

end adjoin

variable {K : Type} [Field K] [Algebra (ZMod g) K]

theorem exists_unit_root {d : ℕ} (hd : 0 < d) (hK : Module.finrank (ZMod g) K = d) {P : (ZMod g)[X]}
    (hP : IsPrimeLab d P) : ∃ u : Kˣ, aeval (u : K) P = 0 := by
  haveI := Fact.mk hP.2.1
  haveI : Module.Finite (ZMod g) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.1.ne_zero).finite
  haveI : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod g)
  letI : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hd)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite _
  have hc : Fintype.card (AdjoinRoot P) = Fintype.card K := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), Module.card_eq_pow_finrank (K := ZMod g) (V := K),
      finrank_adjoin hP, hK]
  let φ := FiniteField.algEquivOfCardEq g hc
  have hr : aeval (φ (AdjoinRoot.root P)) P = 0 := by
    rw [show φ (AdjoinRoot.root P) = φ.toAlgHom (AdjoinRoot.root P) from rfl, aeval_algHom_apply,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  have hne : φ (AdjoinRoot.root P) ≠ 0 := by
    intro h0
    rw [h0, aeval_def, eval₂_at_zero] at hr
    exact hP.2.2.1 ((algebraMap (ZMod g) K).injective (hr.trans (map_zero _).symm))
  exact ⟨Units.mk0 _ hne, hr⟩

theorem orbit_regular {d : ℕ} {P : (ZMod g)[X]} (hP : IsPrimeLab d P) {u : K} (hu : aeval u P = 0) :
    ∀ i j, i < d → j < d → u ^ g ^ i = u ^ g ^ j → i = j := by
  have key : ∀ i j, i < j → j < d → u ^ g ^ i = u ^ g ^ j → False := by
    intro i j hij hj h
    have hk : 0 < j - i := Nat.sub_pos_of_lt hij
    have hfix : u ^ g ^ (j - i) = u := by
      apply frob_injective (g := g) (K := K) i
      simp only
      rw [h, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
    have hmin : P = minpoly (ZMod g) u := minpoly.eq_of_irreducible_of_monic hP.2.1 hu hP.1
    have hdvd : P ∣ X ^ (g ^ (j - i)) - X := by
      rw [hmin]
      apply minpoly.dvd
      rw [map_sub, map_pow, aeval_X, hfix, sub_self]
    have := le_of_dvd hP hk hdvd
    omega
  intro i j hi hj h
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (key i j hij hj h).elim
  · exact hij
  · exact (key j i hij hi h.symm).elim

theorem primeLab_to_regularChar : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K],
    Module.finrank (ZMod g) K = d → ∃ c : (ZMod g)[X] → (Kˣ →* ℂˣ), (∀ P, IsPrimeLab d P → IsRegularChar g d (c P)) ∧
      ∀ P P', IsPrimeLab d P → IsPrimeLab d P' → (∃ i < d, c P' = c P ^ g ^ i) → P = P' := by
  intro g _ d hd K _ _ hK
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hd)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  let e : Kˣ ≃* (Kˣ →* ℂˣ) := (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Kˣ ℂ).some.symm
  let c : (ZMod g)[X] → (Kˣ →* ℂˣ) := fun P =>
    if h : ∃ u : Kˣ, aeval (u : K) P = 0 then e h.choose else 1
  have hc : ∀ P, IsPrimeLab d P → ∃ u : Kˣ, aeval (u : K) P = 0 ∧ c P = e u := by
    intro P hP
    have h := exists_unit_root hd hK hP
    exact ⟨h.choose, h.choose_spec, dif_pos h⟩
  refine ⟨c, fun P hP => ?_, fun P P' hP hP' ⟨i, hi, h⟩ => ?_⟩
  · obtain ⟨u, hu, hcu⟩ := hc P hP
    intro i j hi hj h
    rw [hcu, ← map_pow, ← map_pow] at h
    have h' := congrArg Units.val (e.injective h)
    simp only [Units.val_pow_eq_pow_val] at h'
    exact orbit_regular hP hu i j hi hj h'
  · obtain ⟨u, hu, hcu⟩ := hc P hP
    obtain ⟨u', hu', hcu'⟩ := hc P' hP'
    rw [hcu, hcu', ← map_pow] at h
    have h' := congrArg Units.val (e.injective h)
    simp only [Units.val_pow_eq_pow_val] at h'
    have hr : aeval (u' : K) P = 0 := by rw [h', aeval_pow_frob, hu, zero_pow (pow_ne_zero _ (Fact.out : g.Prime).ne_zero)]
    rw [minpoly.eq_of_irreducible_of_monic hP.2.1 hr hP.1, minpoly.eq_of_irreducible_of_monic hP'.2.1 hu' hP'.1]

end GlobalTheory.PrimeLabOrbit

end
end

section

noncomputable section

namespace GlobalTheory.SmGL.DepthZero

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.StepData ValuativeRel
open scoped TensorProduct

section Tensor

variable {α : Type} [Fintype α] [dec : DecidableEq α] {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

def contract (φ : ∀ a, X a →ₗ[ℂ] ℂ) (a : α) : (⨂[ℂ] b, X b) →ₗ[ℂ] X a := GlobalTheory.MultilinearContraction.contract φ a

theorem contract_tprod (φ : ∀ a, X a →ₗ[ℂ] ℂ) (a : α) (x : ∀ b, X b) :
    contract φ a (PiTensorProduct.tprod ℂ x) = (∏ b ∈ Finset.univ.erase a, φ b (x b)) • x a :=
  GlobalTheory.MultilinearContraction.contract_tprod φ a x

theorem exists_contract_ne_zero {w : ⨂[ℂ] b, X b} (hw : w ≠ 0) (a : α) :
    ∃ φ : ∀ a, X a →ₗ[ℂ] ℂ, contract φ a w ≠ 0 := by
  let b := fun i => Module.Free.chooseBasis ℂ (X i)
  let B := Basis.piTensorProduct b
  obtain ⟨p, hp⟩ : ∃ p, B.repr w p ≠ 0 := by
    by_contra! h
    exact hw (B.repr.injective (by ext p; simp [h p]))
  refine ⟨fun i => (b i).coord (p i), fun h => hp ?_⟩
  have key : (b a).coord (p a) ∘ₗ contract (fun i => (b i).coord (p i)) a = B.coord p := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, contract_tprod, map_smul,
      Module.Basis.coord_apply, B, Basis.piTensorProduct_repr_tprod_apply, smul_eq_mul]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
  have := congrArg (fun L => L w) key
  simp only [LinearMap.comp_apply, h, map_zero, Module.Basis.coord_apply] at this
  exact this.symm

theorem contract_piTensor {Γ : α → Type} [∀ a, Group (Γ a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (φ : ∀ a, X a →ₗ[ℂ] ℂ) (a : α) (g : Γ a) (w : ⨂[ℂ] b, X b) :
    contract φ a (piTensor ρ (Pi.mulSingle a g) w) = ρ a g (contract φ a w) := by
  induction w using PiTensorProduct.induction_on with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | smul_tprod c x =>
    simp only [map_smul, piTensor_tprod, contract_tprod, Pi.mulSingle_eq_same]
    congr 2
    exact Finset.prod_congr rfl fun b hb => by
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hb)]; simp

end Tensor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem isCompact_KOne₁ : IsCompact (KOne k n : Set (GL n k)) :=
  SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ isOpen_KOne) KOne_le_KO

theorem conj_mem_KOne₁ {w g : GL n k} (hw : w ∈ KO k n) (hg : g ∈ KOne k n) : w⁻¹ * g * w ∈ KOne k n := by
  refine mem_KOne.2 ?_
  have : (w⁻¹ * g * w).val - 1 = (w⁻¹).val * (g.val - 1) * w.val := by
    simp [mul_sub, sub_mul]
  rw [this]
  exact ((mem_KO.1 hw).2.mul_maxM (mem_KOne.1 hg)).mul_intM (mem_KO.1 hw).1

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

theorem leviEmb_mem_KOne₁ (e : (Σ a, m a) ≃ n) {g : Levi k m} (hg : ∀ a, g a ∈ KOne k (m a)) :
    leviEmb k e g ∈ KOne k n := by
  refine mem_KOne.2 fun i j => ?_
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h
    have := mem_KOne.1 (hg a) i j
    simpa [Matrix.sub_apply, Matrix.one_apply] using this
  · have h' : e ⟨a, i⟩ ≠ e ⟨b, j⟩ := fun h' => h (congrArg Sigma.fst (e.injective h'))
    simp [Matrix.sub_apply, leviEmb_apply_ne k e g h, Matrix.one_apply_ne h']

theorem deltaHalf_eq_one {g : Levi k m} (hg : ∀ a, g a ∈ KOne k (m a)) : deltaHalf k m g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => tame_det_of_mem_KOne (fun x hx => isUnram_absPow k _ x ?_) (hg a)
  simpa using Valuation.map_one_add_of_lt _ hx

theorem exists_fixed_of_parInd (e : (Σ a, m a) ≃ n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k m) W) {f : IndSp e ρ} (hf : f ∈ fixed (parInd e ρ) (KOne k n)) (h0 : f ≠ 0) :
    ∃ w : W, w ≠ 0 ∧ ∀ g : Levi k m, (∀ a, g a ∈ KOne k (m a)) → ρ g w = w := by
  obtain ⟨x, hx⟩ : ∃ x, f.1.1 x ≠ 0 := by
    by_contra! h
    exact h0 (Subtype.ext (Subtype.ext (funext h)))
  obtain ⟨p, c, hc, rfl⟩ := MultiIrr.exists_parab_mul e x
  refine ⟨f.1.1 c, fun h => hx (by rw [parInd_law, h]; simp), fun g hg => ?_⟩
  have h1 := parInd_law e ρ f ⟨_, leviEmb_mem_parab k e g⟩ c
  rw [leviProj_leviEmb, deltaHalf_eq_one hg, Units.val_one, one_smul] at h1
  have h2 := hf ⟨_, conj_mem_KOne₁ hc (leviEmb_mem_KOne₁ e hg)⟩
  have h3 := congrArg (fun F : IndSp e ρ => F.1.1 c) h2
  simp only [parInd_apply, MonoidHom.one_apply, Units.val_one, one_smul] at h3
  rw [← h1, ← h3]
  group

theorem fixed_of_isSubquotient (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL n k) V} (h : IsSubquotient π (multiProd e σ))
    (hv : ∃ v ∈ fixed π (KOne k n), v ≠ 0) (a : α) : ∃ v ∈ fixed (σ a) (KOne k (m a)), v ≠ 0 := by
  obtain ⟨S, F, hF⟩ := h
  obtain ⟨v, hv, hv0⟩ := hv
  obtain ⟨u, rfl⟩ := hF v
  have hS : IsSmooth S.toRepresentation := fun y => by
    have := isSmooth_parInd e (piTensor σ) y.1
    convert this using 3 with g
    exact Subtype.ext_iff
  obtain ⟨y, hy, hyu⟩ := IwahoriOnto.exists_fixed_map_eq hS isCompact_KOne₁ F.toLinearMap u fun g hg => by
    have h1 := hv ⟨g, hg⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1
    exact (F.isIntertwining _ _ g u).trans h1
  have hy0 : y.1 ≠ 0 := fun h => hv0 (by
    have : y = 0 := Subtype.ext h
    rw [this, map_zero] at hyu
    exact hyu.symm)
  obtain ⟨w, hw0, hw⟩ := exists_fixed_of_parInd e (piTensor σ) (f := y.1)
    (fun g => congrArg Subtype.val (hy g)) hy0
  obtain ⟨φ, hφ⟩ := exists_contract_ne_zero hw0 a
  refine ⟨_, fun g => ?_, hφ⟩
  rw [← contract_piTensor, hw _ fun b => ?_]
  · simp
  · by_cases hb : b = a
    · subst hb; simp
    · rw [Pi.mulSingle_eq_of_ne hb]; exact one_mem _

end GlobalTheory.SmGL.DepthZero

namespace GlobalTheory.SmGL

open GlobalTheory.PRep GlobalTheory.SplitRead

theorem depthZeroSupport : GlobalTheory.Published.DepthZeroSupport := by
  intro k _ _ _ _ n π s d σ h hv a
  obtain ⟨-, -, e, he⟩ := h
  exact DepthZero.fixed_of_isSubquotient e (fun a => (σ a).π) he hv a

end GlobalTheory.SmGL

end
end

section

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.TameRed

theorem part_spec {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x : G} (hx : IsOfFinOrder x) :
    ∃ a M : ℕ, M ≠ 0 ∧ M.Coprime l ∧ Formalism.CyclotomicNorms.primeToPart l x ^ M = 1 ∧
      Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ a) = x ^ (l ^ a) := by
  have hn : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  set a := (orderOf x).factorization l with ha
  set M := orderOf x / l ^ a with hM
  have hmul : l ^ a * M = orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hcop : M.Coprime l := (Nat.coprime_ordCompl hl hn).symm
  have hM0 : M ≠ 0 := (Nat.ordCompl_pos l hn).ne'
  haveI : NeZero M := ⟨hM0⟩
  set u := (((l ^ a : ℕ) : ZMod M)⁻¹).val with hu
  have hz : Formalism.CyclotomicNorms.primeToPart l x = x ^ (l ^ a * u) := rfl
  have hone : (x ^ (l ^ a)) ^ M = 1 := by rw [← pow_mul, hmul, pow_orderOf_eq_one]
  have hmod : l ^ a * u ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, hu, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ (Nat.Coprime.pow_left a hcop.symm)
  refine ⟨a, M, hM0, hcop, ?_, ?_⟩
  · rw [hz, pow_mul, ← pow_mul _ u, mul_comm u, pow_mul, hone, one_pow]
  · rw [hz, ← pow_mul, mul_comm, pow_mul]
    have := pow_eq_pow_of_modEq hmod hone
    rwa [pow_one] at this

theorem eq_of_map_eq {O k : Type} [CommRing O] [IsDomain O] [Field k] (f : O →+* k) {M : ℕ} (hM : (M : k) ≠ 0)
    {x y : O} (hx : x ^ M = 1) (hy : y ^ M = 1) (h : f x = f y) : x = y := by
  first
  | (rename_i h_2 h_3 h_4; revert O k h_2 h_3 h_4 f M hM x y hx hy h; exact @_root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main)
  | exact @_root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main
  | exact _root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main
  | (apply _root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main ..)

end GlobalTheory.TameRed
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_tilt_root_of_unity_approx_ratio : ∀ (l : ℕ) [Fact l.Prime] (y y' : Formalism.Per.Fl l), y' ≠ 0 → ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖ = ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ → ∃ (ζ : Formalism.Per.Fl l) (o : ℕ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧ ‖(((y - ζ * y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ < ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
  first | exact @GlobalTheory.TiltRootApprox.exists_root_approx | exact GlobalTheory.TiltRootApprox.exists_root_approx | (intros; apply GlobalTheory.TiltRootApprox.exists_root_approx <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

theorem GlobalTheory.PMon.galois_inv_period_matrix : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]) (M : GL n ℂ_[l]), (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) * (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) → ∀ g : ↥(GK K), ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]) * (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) := by
  intro l _ n _ _ K ρ M h g
  set σ := Formalism.Per.σC (g : GQ l) with hσ
  have h1 : (M : Matrix n n ℂ_[l]).map σ * ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map σ = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have h2 := h g
  set R := (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l])
  have h3 : R = (M : Matrix n n ℂ_[l]) * ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map σ := by
    calc R = R * ((M : Matrix n n ℂ_[l]).map σ * ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]).map σ) := by rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h2]
  rw [h3, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory.AxLemma

theorem ax_lemma_matrix : ∀ (l : ℕ) [Fact l.Prime] , ∃ c : ℝ, 0 < c ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (H : Subgroup ↥(GK K)) (Y : Matrix n n ℂ_[l]) (r : ℝ), 0 < r → (∀ g ∈ H, ∀ i j, ‖(Y.map (Formalism.Per.σC (g : GQ l)) - Y) i j‖ ≤ r) → ∃ Z : Matrix n n ℂ_[l], (∀ g ∈ H, Z.map (Formalism.Per.σC (g : GQ l)) = Z) ∧ ∀ i j, ‖(Y - Z) i j‖ ≤ c * r := by
  intro l _
  obtain ⟨c, hc, hax⟩ := ax_lemma_complete l
  refine ⟨c, hc, fun n _ _ K H Y r hr hY => ?_⟩
  have hent : ∀ i j, ∃ z : Om l, (∀ g ∈ H.map (GK K).subtype, g z = z) ∧
      ‖Y i j - (z : ℂ_[l])‖ ≤ c * r := by
    intro i j
    refine hax (H.map (GK K).subtype) (Y i j) r hr ?_
    rintro g' ⟨g, hg, rfl⟩
    have := hY g hg i j
    simpa [Matrix.sub_apply, Matrix.map_apply] using this
  choose z hz hzY using hent
  refine ⟨Matrix.of fun i j => (z i j : ℂ_[l]), ?_, ?_⟩
  · intro g hg
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [GlobalTheory.RingBasics.σC_coe]
    congr 1
    exact hz i j _ ⟨g, hg, rfl⟩
  · intro i j
    simpa [Matrix.sub_apply, Matrix.of_apply] using hzY i j

end GlobalTheory.AxLemma
end

section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.Jumps

theorem odd_rank (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩

theorem map_round_cast (S : Multiset ℂ) (h : ∀ z ∈ S, ∃ n : ℤ, z = (n : ℂ)) :
    (S.map fun z => ⌊z.re⌋).map (fun n : ℤ => (n : ℂ)) = S := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id S]
  refine Multiset.map_congr rfl fun z hz => ?_
  obtain ⟨n, rfl⟩ := h z hz
  simp

end GlobalTheory.TripleGal.Jumps
end
