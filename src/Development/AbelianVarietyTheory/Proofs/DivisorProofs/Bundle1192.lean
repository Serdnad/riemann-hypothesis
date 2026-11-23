module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BadPlacesGoodCoefficients
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem GlobalTheory.HolDS.raisingSpan_stable : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ L : Submodule ℂ V, KStab ε E L → (∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ L, E b a x = 0) → ∀ (a b : Fin n), ∀ y ∈ Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x}, E a b y ∈ Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} := by
  intro n ε V _ _ E hG L hK hL
  set S := Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} with hS
  have gen : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) → ∀ x ∈ L,
      (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x ∈ S :=
    fun l hl x hx => Submodule.subset_span ⟨l, hl, x, hx, rfl⟩
  have pre : ∀ c d, ε c = true → ε d = false → ∀ y ∈ S, E c d y ∈ S := by
    intro c d hc hd y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, hl, x, hx, rfl⟩ := hz
      have h1 := gen ((c, d) :: l) (by
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨hc, hd⟩
        · exact hl p hp) x hx
      simpa only [List.map_cons, List.prod_cons, Module.End.mul_apply] using h1
    | zero => rw [map_zero]; exact S.zero_mem
    | add u v _ _ hu hv => rw [map_add (f := _)]; exact S.add_mem hu hv
    | smul r u _ hu => rw [map_smul]; exact S.smul_mem r hu
  have main : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) → ∀ x ∈ L,
      ∀ a b, E a b ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod x) ∈ S := by
    intro l
    induction l with
    | nil =>
      intro _ x hx a b
      simp only [List.map_nil, List.prod_nil, Module.End.one_apply]
      cases ha : ε a <;> cases hb : ε b
      · have h1 := gen [] (by simp) _ (hK a b (ha.trans hb.symm) x hx)
        simpa only [List.map_nil, List.prod_nil, Module.End.one_apply] using h1
      · rw [hL b a hb ha x hx]; exact S.zero_mem
      · have h1 := gen [(a, b)] (by simp [ha, hb]) x hx
        simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using h1
      · have h1 := gen [] (by simp) _ (hK a b (ha.trans hb.symm) x hx)
        simpa only [List.map_nil, List.prod_nil, Module.End.one_apply] using h1
    | cons q l ih =>
      obtain ⟨c, d⟩ := q
      intro hl x hx a b
      have hl' : ∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false := fun p hp => hl p (List.mem_cons_of_mem _ hp)
      have hcd : ε c = true ∧ ε d = false := hl (c, d) (by simp)
      have ih' := ih hl' x hx
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      set z := (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x
      have key : E a b (E c d z) = E c d (E a b z) +
          ((if b = c then E a d else 0) - (if d = a then E c b else 0)) z := by
        rw [← hG a b c d, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]; abel
      rw [key, LinearMap.sub_apply]
      refine S.add_mem (pre c d hcd.1 hcd.2 _ (ih' a b)) (S.sub_mem ?_ ?_)
      · split_ifs
        · exact ih' a d
        · rw [LinearMap.zero_apply]; exact S.zero_mem
      · split_ifs
        · exact ih' c b
        · rw [LinearMap.zero_apply]; exact S.zero_mem
  intro a b y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hl, x, hx, rfl⟩ := hz
    exact main l hl x hx a b
  | zero => rw [map_zero]; exact S.zero_mem
  | add u v _ _ hu hv => rw [map_add (f := _)]; exact S.add_mem hu hv
  | smul r u _ hu => rw [map_smul]; exact S.smul_mem r hu
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_kHighest_real_of_finiteDimensional : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), KRel ε E → KUnit ε E → ∀ N : Submodule ℂ V, FiniteDimensional ℂ N → KStab ε E N → N ≠ ⊥ → ∃ (μ : Fin n → ℝ) (w : V), w ∈ N ∧ w ≠ 0 ∧ KHighest ε E μ w := by
  intro n ε V _ _ E hR hU N hfd hS hN
  classical
  haveI : FiniteDimensional ℂ N := hfd
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 hN
  have hcomm : ∀ k i j, ε i = ε j → E k k * E i j - E i j * E k k =
      ((if k = i then (1 : ℂ) else 0) - (if j = k then 1 else 0)) • E i j := by
    intro k i j h
    rw [hR k k i j rfl h]
    by_cases h1 : k = i <;> by_cases h2 : j = k
    · subst h1; subst h2; simp
    · subst h1; simp [h2]
    · subst h2; simp [h1]
    · simp [h1, h2]
  let H : Module.End ℂ V := ∑ k : Fin n, ((k : ℕ) : ℂ) • E k k
  have hH : ∀ i j, ε i = ε j → H * E i j = E i j * H + (((i : ℕ) : ℂ) - (j : ℕ)) • E i j := by
    intro i j hij
    rw [← sub_eq_iff_eq_add', Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, hcomm _ _ _ hij, smul_smul, ← Finset.sum_smul]
    simp [mul_sub]
  have hHN : ∀ v ∈ N, H v ∈ N := by
    intro v hv
    simp only [H, LinearMap.sum_apply, LinearMap.smul_apply]
    exact N.sum_mem fun k _ => N.smul_mem _ (hS k k rfl v hv)
  let HN : Module.End ℂ N := H.restrict hHN
  let D : Fin n → Module.End ℂ N := fun k => (E k k).restrict (fun v hv => hS k k rfl v hv)
  obtain ⟨l, hl, hmin⟩ := Set.exists_min_image {c | HN.HasEigenvalue c} Complex.re
    (Module.End.finite_hasEigenvalue HN) (Module.End.exists_eigenvalue HN)
  have hDc : ∀ i j, D i * D j = D j * D i := by
    intro i j
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h := LinearMap.congr_fun (hcomm i j j rfl) (x : V)
    have h' : ((if i = j then (1 : ℂ) else 0) - (if j = i then 1 else 0)) = 0 := by
      by_cases h1 : i = j
      · subst h1; simp
      · simp [h1, Ne.symm h1]
    rw [h', zero_smul, LinearMap.zero_apply, LinearMap.sub_apply, sub_eq_zero] at h
    simpa [D, LinearMap.restrict_apply] using h
  obtain ⟨v, hv, hv0, ν, hν⟩ := GlobalTheory.AlgInfChar.exists_joint_eigenvector D hDc (HN.eigenspace l) hl
    (fun k u hu => by
      rw [Module.End.mem_eigenspace_iff] at hu ⊢
      apply Subtype.ext
      have h1 := LinearMap.congr_fun (hH k k rfl) (u : V)
      have h2 : H (u : V) = l • (u : V) := congrArg Subtype.val hu
      simp only [sub_self, zero_smul, add_zero, Module.End.mul_apply] at h1
      simp only [HN, D, LinearMap.restrict_apply, SetLike.val_smul]
      rw [h1, h2, map_smul])
  rw [Module.End.mem_eigenspace_iff] at hv
  have hHv : H (v : V) = l • (v : V) := congrArg Subtype.val hv
  have hEv : ∀ a, E a a (v : V) = ν a • (v : V) := fun a => congrArg Subtype.val (hν a)
  have hv0' : (v : V) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hreal : ∀ a, (((ν a).re : ℝ) : ℂ) = ν a := by
    intro a
    have h := hU a a rfl (v : V) (v : V)
    rw [hEv, inner_smul_left, inner_smul_right] at h
    have hne : ⟪(v : V), (v : V)⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0'
    exact Complex.conj_eq_iff_re.1 (mul_right_cancel₀ hne h)
  refine ⟨fun a => (ν a).re, v, v.2, hv0', fun a => by rw [hEv, hreal], fun a b hab he => ?_⟩
  by_contra h0
  let u : N := ⟨E a b v, hS a b he v v.2⟩
  have hu0 : u ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hHu : HN u = (l + (((a : ℕ) : ℂ) - (b : ℕ))) • u := by
    apply Subtype.ext
    have h1 := LinearMap.congr_fun (hH a b he) (v : V)
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at h1
    simp only [HN, u, LinearMap.restrict_apply, SetLike.val_smul]
    rw [h1, hHv, map_smul, add_smul]
  have h2 := hmin _ (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hHu, hu0⟩)
  have hab' : (a : ℕ) < b := hab
  simp at h2
  exact absurd hab' (not_lt.2 (by exact_mod_cast h2))

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameGram

theorem form_mem_span {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (T : Set (Fin n → R))
    (hT : ∀ x ∈ T, ∀ y ∈ T, ∑ i, ∑ j, σ (x i) * J i j * y j ∈ S) :
    ∀ x ∈ Submodule.span S T, ∀ y ∈ Submodule.span S T, ∑ i, ∑ j, σ (x i) * J i j * y j ∈ S := by
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact hT x hx y hy
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      exact S.add_mem ha hb
    | smul c a _ ha =>
      have : ∑ i, ∑ j, σ (x i) * J i j * (c • a) j = (c : R) * ∑ i, ∑ j, σ (x i) * J i j * a j := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        show _ * ((c : R) * a j) = _
        ring
      rw [this]; exact S.mul_mem c.2 ha
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
    exact S.add_mem ha hb
  | smul c a _ ha =>
    have : ∑ i, ∑ j, σ ((c • a) i) * J i j * y j = σ (c : R) * ∑ i, ∑ j, σ (a i) * J i j * y j := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      show σ ((c : R) * a i) * _ * _ = _
      rw [map_mul]; ring
    rw [this]; exact S.mul_mem (hσ _ c.2) ha

theorem exists_unit {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n m : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (β : GL (Fin n) R) (H : Set (Fin n → R))
    (hβ : ∀ x, x ∈ H ↔ ∀ i, (β⁻¹).1.mulVec x i ∈ S)
    (hH : ∀ x ∈ H, ∀ y ∈ H, ∑ i, ∑ j, σ (x i) * J i j * y j ∈ S)
    (s s' : Fin m → Fin n → R) (hs : ∀ i, s i ∈ H) (hs' : ∀ i, s' i ∈ H)
    (hd : ∀ a j, ∑ i, s i a * ∑ k, σ (s' i k) * J k j = if a = j then 1 else 0) :
    ∃ G : GL (Fin n) S, S.subtype.mapMatrix G.1 = (β.1.map σ)ᵀ * J * β.1 := by
  have hcol : ∀ j, (fun i => β.1 i j) ∈ H := by
    intro j
    rw [hβ]
    intro k
    have : (β⁻¹).1.mulVec (fun i => β.1 i j) k = ((β⁻¹).1 * β.1) k j := rfl
    rw [this, Units.inv_mul, Matrix.one_apply]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  have a1 : ∀ i j, ((β.1.map σ)ᵀ * J * β.1) i j ∈ S := by
    intro i j
    have := hH _ (hcol i) _ (hcol j)
    rw [Finset.sum_comm] at this
    simpa only [Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply] using this
  let P : Matrix (Fin n) (Fin m) R := Matrix.of fun a i => s i a
  let P' : Matrix (Fin n) (Fin m) R := Matrix.of fun a i => s' i a
  have hP : P * ((P'.map σ)ᵀ * J) = 1 := by
    ext a j
    rw [Matrix.one_apply, ← hd]
    rfl
  have a2 : ∀ i j, (((β⁻¹).1 * P) * (((β⁻¹).1 * P').map σ)ᵀ) i j ∈ S := by
    intro i j
    rw [Matrix.mul_apply]
    exact S.sum_mem fun k _ => S.mul_mem ((hβ _).1 (hs k) i) (hσ _ ((hβ _).1 (hs' k) j))
  have hinv : (((β⁻¹).1 * P) * (((β⁻¹).1 * P').map σ)ᵀ) * ((β.1.map σ)ᵀ * J * β.1) = 1 := by
    have e : (((β⁻¹).1 * P').map σ)ᵀ * (β.1.map σ)ᵀ = (P'.map σ)ᵀ := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    calc _ = (β⁻¹).1 * (P * (((((β⁻¹).1 * P').map σ)ᵀ * (β.1.map σ)ᵀ) * J)) * β.1 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e, hP, Matrix.mul_one, Units.inv_mul]
  let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, a1 i j⟩
  let M' : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, a2 i j⟩
  have hM : S.subtype.mapMatrix M = (β.1.map σ)ᵀ * J * β.1 := rfl
  have hM' : S.subtype.mapMatrix M' = ((β⁻¹).1 * P) * (((β⁻¹).1 * P').map σ)ᵀ := rfl
  have inj : Function.Injective (S.subtype.mapMatrix (m := Fin n)) := by
    intro A B h
    ext i j
    exact congrFun (congrFun h i) j
  have p2 : M' * M = 1 := inj (by rw [map_mul, map_one, hM, hM', hinv])
  exact ⟨⟨M, M', mul_eq_one_comm.1 p2, p2⟩, hM⟩

theorem exists_unit_adelic {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : ℕ}
    (c : E → E) (σ : E ⊗[F] Formalism.L2.Herm.Af F →+* E ⊗[F] Formalism.L2.Herm.Af F)
    (hσ : ∀ s ∈ Formalism.L2.Herm.intAf F E, σ s ∈ Formalism.L2.Herm.intAf F E)
    (hσι : ∀ x, σ (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) x) = Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (c x))
    (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hβ : IsFrame β Λ) (hΛ : ∀ y ∈ Λ, ∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, c (x i) * J i j * y j)
    (s s' : Fin m → Fin n → E) (hs : ∀ i, s i ∈ Λ ∧ s' i ∈ Λ)
    (hd : ∀ a j, ∑ i, s i a * ∑ k, c (s' i k) * J k j = if a = j then 1 else 0) :
    ∃ G : GL (Fin n) (Formalism.L2.Herm.intAf F E), (intGL F E n G).val =
      Formalism.UG.cT σ β.1 * J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) * β.1 := by
  let ι : E →+* E ⊗[F] Formalism.L2.Herm.Af F := Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)
  replace hσι : ∀ x, σ (ι x) = ι (c x) := hσι
  have hmem : ∀ x ∈ Λ, (fun i => ι (x i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := fun x hx =>
    Submodule.subset_span ⟨x, hx, rfl⟩
  refine exists_unit (Formalism.L2.Herm.intAf F E) σ hσ (J.map ι) β
    (Formalism.L2.Herm.hatL (F := F) Λ) hβ ?_ (fun i a => ι (s i a)) (fun i a => ι (s' i a))
    (fun i => hmem _ (hs i).1) (fun i => hmem _ (hs i).2) ?_
  · refine form_mem_span _ σ hσ _ _ ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨b, hb⟩ := hΛ y hy x hx
    have : ∑ i, ∑ j, σ (ι (x i)) * (J.map ι) i j * ι (y j) = ι b := by
      rw [hb]

      simp only [map_sum, RingHom.map_mul, hσι, Matrix.map_apply]
    show ∑ i, ∑ j, σ (ι (x i)) * (J.map ι) i j * ι (y j) ∈ _
    rw [this]
    exact (oToS F E b).2
  · intro a j
    have := congrArg ι (hd a j)

    simp only [map_sum, RingHom.map_mul, ← hσι, apply_ite ι, RingHom.map_one, RingHom.map_zero] at this
    exact this

theorem gram_unimodular : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∃ G : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), (intGL D.host.F D.host.E V.rank G).val = BadPlacesGoodCoefficients.gramIn V β := by
  intro D V β Λ N hB
  have hsd := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D V β Λ N ⟨1, by rw [pow_one]; exact hB⟩
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D V Λ hsd
  exact exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (fun _ => GlobalTheory.LevSplit.sigR_int)
    (fun _ => rfl) V.gram β Λ hB.1 (fun y hy => (hsd.2 y).1 hy) s s' hs hd

end GlobalTheory.FrameGram
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaConjChar

open Formalism.L2.Host Formalism.L2.JoinChr

section General

variable {E : Type} [Field E] [NumberField E]

theorem val_unif (P : HeightOneSpectrum (𝓞 E)) : P.valuation E ((unif P : Eˣ) : E) = WithZero.exp (-1 : ℤ) :=
  (P.valuedAdicCompletion_eq_valuation' _).symm.trans (unif_spec P)

theorem exists_unit_part (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    ∃ u : Eˣ, P.valuation E (u : E) = 1 ∧ k = unif P ^ ordF P k * u := by
  refine ⟨(unif P ^ ordF P k)⁻¹ * k, ?_, by rw [mul_inv_cancel_left]⟩
  have h0 : P.valuation E (k : E) ≠ 0 := (Valuation.ne_zero_iff _).2 k.ne_zero
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, val_unif,
    ← WithZero.exp_zsmul, ← WithZero.exp_neg, ordF]
  conv_lhs => rw [← WithZero.exp_log h0, WithZero.log_exp, ← WithZero.exp_add]
  simp

theorem twVal_half (χ : HChar E) (P : HeightOneSpectrum (𝓞 E)) (h : ∀ u : Eˣ, P.valuation E (u : E) = 1 → χ.locK P u = 1)
    (k : Eˣ) : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal χ (1 / 2) P k =
      (((χ.locK P (unif P) : ℂˣ) : ℂ) * (((Real.sqrt (Nat.card (kP P) : ℝ))⁻¹ : ℝ) : ℂ)) ^ ordF P k := by
  obtain ⟨u, hu, hk⟩ := exists_unit_part P k
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal
  generalize ordF P k = n at hk ⊢
  rw [hk, map_mul, h u hu, mul_one, map_zpow, Units.val_zpow_eq_zpow_val, mul_zpow]
  congr 1
  have hN : (0 : ℝ) ≤ (Nat.card (kP P) : ℕ) := Nat.cast_nonneg _
  rw [show Ideal.absNorm P.asIdeal = Nat.card (kP P) from Ideal.absNorm_eq_natCard _, ← Complex.ofReal_zpow, Real.sqrt_eq_rpow,
    ← Real.rpow_neg hN, ← Real.rpow_intCast, ← Real.rpow_mul hN, Complex.ofReal_cpow hN]
  push_cast
  congr 1
  ring

end General

theorem locK_eq_one {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (hc : ChrEq c χ) (hu : UnramEverywhere D c)
    (P : Pl D.host.E) (u : D.host.Eˣ) (h : P.valuation D.host.E (u : D.host.E) = 1) : χ.locK P u = 1 := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, hP, hQ⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have key : ∀ k : D.host.E, P.valuation D.host.E k = 1 → finPart D (locE D e k) ∈ intAE D := by
    intro k hk
    rw [h2]
    intro Q
    have h4 : ι (finPart D (incA D k)) = algebraMap D.host.E _ k := h1 k
    have h5 : ι (finPart D (locE D e k)) = 1 + ι (finPart D e) * (ι (finPart D (incA D k)) - 1) :=
      GlobalTheory.HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _
    rw [h5, h4]
    change Valued.v (1 + ι (finPart D e) Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) k - 1)) ≤ 1
    by_cases hQP : Q = P
    · subst hQP
      rw [hP, one_mul, add_sub_cancel]
      exact ((Q.valuedAdicCompletion_eq_valuation' k).trans hk).le
    · rw [hQ Q hQP, zero_mul, add_zero, map_one]
  have hinv : (((locU he.1 u)⁻¹ : (AE D)ˣ) : AE D) = locE D e ((u⁻¹ : D.host.Eˣ) : D.host.E) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [locU_val, locE_mul_locE he.1]
    simp [locE]
  have h6 := hu (locU he.1 u) (by
    rw [locU_val, locE, RingHom.map_add (f := _), RingHom.map_one, RingHom.map_mul, hinf, zero_mul, add_zero])
    (key _ h) (by
      rw [hinv]
      refine key _ ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one])
  have h7 := hc.2 P e he u (locU he.1 u) rfl
  rw [h6] at h7
  exact Units.ext h7.symm

end GlobalTheory.EtaConjChar
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.ThetaFiresOfMult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring GlobalTheory.IndefiniteRowSideFullHecke.ThetaMultiplicity

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem exists_isThetaMult_of_firesAt {R : RealDat D A Ks} {i : Fin D.R.m} {t : T}
    (h : ∀ x, FiresAt R i t x) : ∃ y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A)), IsThetaMult R i t y :=
  GlobalTheory.ThetaFiresLinear.exists_linear_lift (lowT (R.MW i (sg0 D A))) (R.Wall i (sg0 D A)) (R.νV i t) (R.fdV i t)
    (kernel R i t) (R.ptP i t) (GlobalTheory.ThetaFiresLinear.kernelL R i t)
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i t))
    (fun _ _ _ => rfl) (fun _ => rfl) (R.ioP i) (R.extV i t) h

end GlobalTheory.ThetaFiresOfMult

end
end

section

noncomputable section

namespace GlobalTheory.IndLine

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

def KEqOn (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (V : Submodule ℂ P) (T : P →ₗ[ℂ] P) : Prop :=
  ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → p f ∈ V →
    ∀ g ∈ M.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) g g₁ → T (p f) = p g →
      T (p f₁) = p g₁

end GlobalTheory.IndLine
end
end
