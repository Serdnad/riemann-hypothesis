module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle063
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle064
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

noncomputable section

namespace GlobalTheory.EigenPoint

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

section Alg

variable {Γ : Type} [Group Γ] {K : Type} [Field K]

theorem charpoly_smul [CharZero K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K} (hc : c ≠ 0) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

theorem twGL_val {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL _ K) : Matrix (Fin a) (Fin a) K) =
      (χ g : K) • ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K) := by
  show algebraMap K (Matrix (Fin a) (Fin a) K) (χ g : K) * ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K) = _
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem isInv_twGL {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (W : Submodule K (Fin a → K)) :
    IsInv (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) W ↔ IsInv ρ W := by
  constructor
  · intro h g v hv
    have := W.smul_mem ((χ g : K)⁻¹) (h g v hv)
    rwa [twGL_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
  · intro h g v hv
    rw [twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem ss_twGL {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (h : IsSSRep ρ) :
    IsSSRep (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) := fun W hW => by
  obtain ⟨W', hW', hc⟩ := h W ((isInv_twGL ρ χ W).1 hW)
  exact ⟨W', (isInv_twGL ρ χ W').2 hW', hc⟩

end Alg

theorem ms_one {s : Multiset ℕ} (h : s.sum = 1) (h1 : ∀ a ∈ s, 1 ≤ a) : s = {1} := by
  have hne : s ≠ 0 := by rintro rfl; simp at h
  have hc := Multiset.card_nsmul_le_sum h1
  have hp := Multiset.card_pos.2 hne
  rw [smul_eq_mul, mul_one, h] at hc
  have hc1 : Multiset.card s = 1 := by omega
  obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 hc1
  simp only [Multiset.sum_singleton] at h
  rw [h]

theorem sum_split {M : Type} [AddCommMonoid M] {n m : ℕ} (h : n = m + 1) (f : Fin n → M) :
    ∑ k, f k = ∑ k : Fin m, f (Fin.cast h.symm k.castSucc) + f (Fin.cast h.symm (Fin.last m)) := by
  subst h
  simp [Fin.sum_univ_castSucc]

theorem prod_flatMap' {α M : Type} [CommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.prod_append, ih]

theorem prod_flat {M : Type} [CommMonoid M] (n : ℕ) (d : Fin n → ℕ) (f : Fin n → ℕ → M) :
    (((List.finRange n).map fun k => ((List.range (d k)).map (f k)).prod)).prod =
      ∏ k, ∏ a ∈ Finset.range (d k), f k a := by
  rw [Fin.prod_univ_def]
  congr 1

variable (D : D7) (i : D.nd.Loc)

def eU : G D.host.E D.nd.Om →* (Qbar (D.nd.l i))ˣ :=
  (Units.map (iotaOQ D.nd D.naut i).toMonoidHom).comp (Formalism.MainNotions.N.Glob.epsO D.nd i)

def cU : G D.host.E D.nd.Om →* (Qbar (D.nd.l i))ˣ :=
  (Units.map (iotaOQ D.nd D.naut i).toMonoidHom).comp (D.nd.chi i 1)

theorem eU_pow (g : G D.host.E D.nd.Om) (a : ℕ) :
    ((((eU D i)⁻¹ ^ a) g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) = (epsQ D i g)⁻¹ ^ a := by
  rw [MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  rfl

def twList (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))) :
    List (Σ m : ℕ, G D.host.E D.nd.Om →* GL (Fin m) (Qbar (D.nd.l i))) :=
  (List.finRange Pa.length).flatMap fun k =>
    (List.range (Pa.get k).d).map fun a => ⟨(Pa.get k).a, Formalism.MainNotions.SumRepresentations.At.twGL (R k) ((eU D i)⁻¹ ^ a)⟩

theorem mem_twList {Pa : List (Part D.naut.CG)}
    {R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))}
    {p : Σ m : ℕ, G D.host.E D.nd.Om →* GL (Fin m) (Qbar (D.nd.l i))} (hp : p ∈ twList D i Pa R) :
    ∃ k : Fin Pa.length, ∃ a < (Pa.get k).d,
      p = ⟨(Pa.get k).a, Formalism.MainNotions.SumRepresentations.At.twGL (R k) ((eU D i)⁻¹ ^ a)⟩ := by
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hk
  exact ⟨k, a, List.mem_range.1 ha, rfl⟩

theorem twList_cp (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i)))
    (g : G D.host.E D.nd.Om) :
    ((twList D i Pa R).map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) (Qbar (D.nd.l i))).charpoly).prod =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))).charpoly).scaleRoots
          ((epsQ D i g)⁻¹ ^ a) := by
  rw [twList, List.map_flatMap, prod_flatMap']
  simp only [List.map_map, Function.comp_def]
  rw [prod_flat]
  refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun a _ => ?_
  rw [twGL_val, charpoly_smul _ (Units.ne_zero _), eU_pow]

theorem mapRep_val {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL _ _) : Matrix (Fin a) (Fin a) B) = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) A).map f := rfl

theorem eig_map (r : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)) (v : Fin D.R.nV → Kf D.nd i)
    (hv0 : v ≠ 0) (hv : ∀ g, ((mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) r g : GL _ _) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i)).mulVec v =
          algebraMap (D.nd.O i) (Kf D.nd i) (chi1 D.nd i g) • v) :
    ∃ w : Fin D.R.nV → Qbar (D.nd.l i), w ≠ 0 ∧ ∀ g,
      ((mapRep (iotaOQ D.nd D.naut i) r g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).mulVec w =
        ((cU D i g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) • w := by
  refine ⟨fun j => D.naut.iotaQ i (v j), fun h => hv0 (funext fun j => ?_), fun g => funext fun j => ?_⟩
  · have := congrFun h j
    exact (D.naut.iotaQ i).injective (by simpa using this)
  · have e1 := congrArg (D.naut.iotaQ i) (congrFun (hv g) j)
    rw [RingHom.map_mulVec, mapRep_val] at e1
    rw [mapRep_val]
    refine e1.trans ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, smul_eq_mul]
    rfl

end GlobalTheory.EigenPoint
end
end

section

noncomputable section

namespace GlobalTheory.SSListPf

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial GlobalTheory.StringRepresentationDecomposition
open scoped Matrix

variable {Γ : Type} [Group Γ] {K : Type} [Field K]

def AInv {V : Type} [AddCommGroup V] [Module K V] (ρ : Γ →* Module.End K V) (W : Submodule K V) : Prop :=
  ∀ g, ∀ v ∈ W, ρ g v ∈ W

def resEnd {V : Type} [AddCommGroup V] [Module K V] (ρ : Γ →* Module.End K V) (U : Submodule K V)
    (hU : AInv ρ U) : Γ →* Module.End K U where
  toFun g := (ρ g).restrict (hU g)
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp [LinearMap.restrict_apply]
  map_mul' g h := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp [LinearMap.restrict_apply, Module.End.mul_apply]

def quoEnd {V : Type} [AddCommGroup V] [Module K V] (ρ : Γ →* Module.End K V) (U : Submodule K V)
    (hU : AInv ρ U) : Γ →* Module.End K (V ⧸ U) where
  toFun g := U.mapQ U (ρ g) (hU g)
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    simp
  map_mul' g h := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    simp [Module.End.mul_apply]

def matRep {V : Type} [AddCommGroup V] [Module K V] {m : ℕ} (ρ : Γ →* Module.End K V)
    (b : Module.Basis (Fin m) K V) : Γ →* GL (Fin m) K :=
  MonoidHom.toHomUnits
    (((LinearMap.toMatrixAlgEquiv b : Module.End K V ≃ₐ[K] Matrix (Fin m) (Fin m) K) :
      Module.End K V →* Matrix (Fin m) (Fin m) K).comp ρ)

theorem matRep_val {V : Type} [AddCommGroup V] [Module K V] {m : ℕ} (ρ : Γ →* Module.End K V)
    (b : Module.Basis (Fin m) K V) (g : Γ) :
    ((matRep ρ b g : GL _ _) : Matrix (Fin m) (Fin m) K) = LinearMap.toMatrix b b (ρ g) := by
  simp only [matRep, MonoidHom.coe_toHomUnits, MonoidHom.comp_apply, MonoidHom.coe_coe]
  rfl

theorem matRep_mulVec {V : Type} [AddCommGroup V] [Module K V] {m : ℕ} (ρ : Γ →* Module.End K V)
    (b : Module.Basis (Fin m) K V) (g : Γ) (y : V) :
    ((matRep ρ b g : GL _ _) : Matrix (Fin m) (Fin m) K) *ᵥ b.equivFun y = b.equivFun (ρ g y) := by
  rw [matRep_val, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
  exact LinearMap.toMatrix_mulVec_repr b b (ρ g) y

theorem charpoly_matRep {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {m : ℕ}
    (ρ : Γ →* Module.End K V) (b : Module.Basis (Fin m) K V) (g : Γ) :
    ((matRep ρ b g : GL _ _) : Matrix (Fin m) (Fin m) K).charpoly = (ρ g).charpoly := by
  rw [matRep_val, LinearMap.charpoly_toMatrix]

theorem charpoly_res_quot {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (e : Module.End K V) (W : Submodule K V) (he : ∀ x ∈ W, e x ∈ W) :
    e.charpoly = (e.restrict he).charpoly * (W.mapQ W e he).charpoly := by
  let bW := Module.finBasis K W
  let bQ := Module.finBasis K (V ⧸ W)
  let b := Module.Basis.sumQuot bW bQ
  let A := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K (V ⧸ W))) K := Matrix.of fun i l ↦
    (b.repr (e (b (Sum.inr l)))) (Sum.inl i)
  let D := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  suffices h : LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by
    rw [← LinearMap.charpoly_toMatrix e b, h, Matrix.charpoly_fromBlocks_zero₂₁,
      LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k0 =>
      simp only [b, Module.Basis.sumQuot_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
      apply Module.Basis.sumQuot_repr_inl_of_mem
    | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k0 =>
      suffices W.mkQ (e (bW k0)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact he _ (Submodule.coe_mem (bW k0))
    | inr l =>
      simp only [LinearMap.toMatrix_apply, Module.Basis.sumQuot_repr_inr,
        Matrix.fromBlocks_apply₂₂, b, D]
      rw [← Module.Basis.sumQuot_inr bW bQ l, W.mapQ_apply]
      simp

def Split {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Γ →* Module.End K V) : Prop :=
  ∃ L : List (Σ m : ℕ, Γ →* GL (Fin m) K), (∀ p ∈ L, 1 ≤ p.1 ∧ IsIrrSub p.2 ⊤) ∧
    ∀ g, (ρ g).charpoly = (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod

theorem split_zero {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Γ →* Module.End K V) (hV : Module.finrank K V = 0) : Split ρ := by
  refine ⟨[], fun p hp => absurd hp List.not_mem_nil, fun g => ?_⟩
  rw [List.map_nil, List.prod_nil]
  exact Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
    (by rw [LinearMap.charpoly_natDegree, hV])

theorem split_irr {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Γ →* Module.End K V) (hV : 0 < Module.finrank K V)
    (hirr : ∀ W : Submodule K V, AInv ρ W → W = ⊥ ∨ W = ⊤) : Split ρ := by
  let b := Module.finBasis K V
  refine ⟨[⟨Module.finrank K V, matRep ρ b⟩], fun p hp => ?_, fun g => ?_⟩
  · rw [List.mem_singleton] at hp
    subst hp
    refine ⟨hV, ?_, fun _ _ _ => Submodule.mem_top, fun W' _ hW' => ?_⟩
    · intro h0
      have h1 : (fun _ => (1 : K)) ∈ (⊤ : Submodule K (Fin (Module.finrank K V) → K)) := Submodule.mem_top
      rw [h0, Submodule.mem_bot] at h1
      have h2 := congrFun h1 ⟨0, hV⟩
      simp at h2
    · have h1 : AInv ρ (W'.comap (b.equivFun : V →ₗ[K] (Fin (Module.finrank K V) → K))) := by
        intro g y hy
        show b.equivFun (ρ g y) ∈ W'
        rw [← matRep_mulVec]
        exact hW' g _ hy
      have h2 : (W'.comap (b.equivFun : V →ₗ[K] (Fin (Module.finrank K V) → K))).map
          (b.equivFun : V →ₗ[K] (Fin (Module.finrank K V) → K)) = W' :=
        Submodule.map_comap_eq_of_surjective b.equivFun.surjective W'
      rcases hirr _ h1 with h3 | h3
      · left
        rw [← h2, h3, Submodule.map_bot]
      · right
        rw [← h2, h3, Submodule.map_top, LinearMap.range_eq_top.mpr b.equivFun.surjective]
  · rw [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact (charpoly_matRep ρ b g).symm

theorem split_step {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Γ →* Module.End K V) (W : Submodule K V) (hW : AInv ρ W)
    (h1 : Split (resEnd ρ W hW)) (h2 : Split (quoEnd ρ W hW)) : Split ρ := by
  refine ⟨h1.choose ++ h2.choose, fun p hp => ?_, fun g => ?_⟩
  · rcases List.mem_append.mp hp with h | h
    · exact h1.choose_spec.1 p h
    · exact h2.choose_spec.1 p h
  · rw [List.map_append, List.prod_append, ← h1.choose_spec.2 g, ← h2.choose_spec.2 g]
    exact charpoly_res_quot (ρ g) W (hW g)

theorem split_all (d : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    Module.finrank K V = d → ∀ ρ : Γ →* Module.End K V, Split ρ := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V _ _ _ hV ρ
  by_cases hex : ∃ W : Submodule K V, AInv ρ W ∧ W ≠ ⊥ ∧ W ≠ ⊤
  · have hW : AInv ρ hex.choose := hex.choose_spec.1
    have hb : hex.choose ≠ ⊥ := hex.choose_spec.2.1
    have ht : hex.choose ≠ ⊤ := hex.choose_spec.2.2
    have hlt : Module.finrank K hex.choose < d := by
      rw [← hV]; exact Submodule.finrank_lt ht
    have hpos : 0 < Module.finrank K hex.choose :=
      Nat.pos_of_ne_zero fun h => hb (Submodule.finrank_eq_zero.mp h)
    have hq : Module.finrank K (V ⧸ hex.choose) + Module.finrank K hex.choose = d := by
      rw [← hV]; exact Submodule.finrank_quotient_add_finrank _
    exact split_step ρ hex.choose hW (ih _ hlt hex.choose rfl (resEnd ρ hex.choose hW))
      (ih _ (by omega) (V ⧸ hex.choose) rfl (quoEnd ρ hex.choose hW))
  · push_neg at hex
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exact split_zero ρ (hV.trans h0)
    · refine split_irr ρ (hV ▸ h0) fun W hW => ?_
      by_cases hb : W = ⊥
      · exact Or.inl hb
      · exact Or.inr (hex W hW hb)

end SSListPf

open Formalism.MainNotions.N Polynomial GlobalTheory.StringRepresentationDecomposition

theorem ssList_holds : SSList := by
  intro k _ Γ _ n ρ
  let ρE : Γ →* Module.End k (Fin n → k) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)) :
      Matrix (Fin n) (Fin n) k →* Module.End k (Fin n → k)).comp ((Units.coeHom _).comp ρ)
  have hρg : ∀ g, ρE g = Matrix.toLin' ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) k) := fun g => rfl
  have h := SSListPf.split_all n (Fin n → k) (by simp) ρE
  refine ⟨h.choose, h.choose_spec.1, fun g => ?_⟩
  rw [← h.choose_spec.2 g, hρg, Matrix.charpoly_toLin']

end GlobalTheory
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.SplitRead

open Formalism.MainNotions.SumRepresentations.At

theorem charpoly_fin_one {k : Type} [CommRing k] (M : Matrix (Fin 1) (Fin 1) k) :
    M.charpoly = X - C (M 0 0) := by
  simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def blockShift (R : Ranks) : ℝ := ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2

theorem blockChar_integral (hAut : TieAut N A) (hMu : MuInt N A) (i : N.Loc) (τ : H.E →+* ℂ) (z : ℂ)
    (hz : z ∈ A.infG (A.tw (A.muC i) A.etaTinv) τ) : ∃ k : ℤ, z + ((blockShift R : ℝ) : ℂ) = (k : ℂ) := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  obtain ⟨c, hc⟩ : ∃ c : ℕ, R.r = 2 * c + 1 := ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have hs : ((blockShift R : ℝ) : ℂ) = -(c : ℂ) - 1 / 2 := by
    have : blockShift R = -(c : ℝ) - 1 / 2 := by
      simp only [blockShift, Ranks.nV, hc]
      push_cast
      ring
    rw [this]
    push_cast
    ring
  obtain ⟨h1, h3⟩ := hAut.2.1 τ
  rcases h1 with h1 | h1
  · have he : A.infG A.etaTinv τ = {-(1 / 2)} := by rw [h3, h1]; simp
    rw [A.infG_tw _ _ _ _ he, Multiset.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨m, rfl⟩ := hMu i τ y hy
    exact ⟨m - c - 1, by rw [hs]; push_cast; ring⟩
  · have he : A.infG A.etaTinv τ = {1 / 2} := by rw [h3, h1]; simp
    rw [A.infG_tw _ _ _ _ he, Multiset.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨m, rfl⟩ := hMu i τ y hy
    exact ⟨m - c, by rw [hs]; push_cast; ring⟩

theorem finite_placesOver (l : ℕ) (hl : l ≠ 0) : (placesOver H.E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 H.E)} ≠ 0 := by
    simpa using hl
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv

theorem blockChar_eq (h5 : JacquetShalikaStrongMultOne N A) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin 1) (Qbar (N.l i)))
    (hρ : ContQ N i ρ)
    (hwd : ∀ w, w ∉ placesOver H.E (N.l i) →
      A.wdOf i ρ w = A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w) (blockShift R))
    (g : G H.E N.Om) :
    ((ρ g : GL (Fin 1) (Qbar (N.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (N.l i))) 0 0 =
      iotaOQ N A i (chi1 N i g) := by
  have hl : N.l i ≠ 0 := (Fact.out : (N.l i).Prime).ne_zero
  have hfin : (placesOver H.E (N.l i) ∪ ((N.S i : Set _) ∪ (N.Q i : Set _))).Finite :=
    (finite_placesOver (H := H) _ hl).union ((N.S i).finite_toSet.union (N.Q i).finite_toSet)
  have hd := h5.2.2.1 _ hfin
  have hc1 : Continuous fun g : G H.E N.Om =>
      ((ρ g : GL (Fin 1) (Qbar (N.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (N.l i))) 0 0 :=
    (continuous_apply_apply 0 0).comp hρ
  have hc2 : Continuous fun g : G H.E N.Om => iotaOQ N A i (chi1 N i g) :=
    (GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data N A i).comp (N.chi_cont i 1)
  refine congrFun (Continuous.ext_on (dense_iff_closure_eq.2 hd) hc1 hc2 ?_) g
  rintro σ ⟨w, hw, hsp, B, hB, hσ⟩
  simp only [Set.mem_union, Finset.mem_coe, not_or] at hw
  obtain ⟨hwl, hwS, hwQ⟩ := hw
  have hso : SplitOut N i w := ⟨hsp, hwl, hwS, hwQ⟩
  obtain ⟨hu, hf⟩ := A.chi_mu i w hso
  have hun : A.unr (A.wdOf i ρ w) := by
    rw [hwd w hwl]; exact (A.unr_tw _ _).2 hu
  have e := A.wdOf_frob i ρ w hwl hρ hun B σ hB hσ
  rw [hwd w hwl, show blockShift R = ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 from rfl, hf B σ hB hσ,
    charpoly_fin_one] at e
  simp only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C] at e
  have e2 := C_injective (sub_right_injective e)
  exact (A.iotaQC i).injective e2

end GlobalTheory.SplitRead
end
end

section

open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

theorem _root_.GlobalTheory.T.endSpanned_of_isIrrSub_of_isAlgClosed' : ∀ {Γ E : Type} [Group Γ] [Field E] [IsAlgClosed E] {a : ℕ} (σ : Γ →* GL (Fin a) E) (U : Submodule E (Fin a → E)), IsIrrSub σ U → EndSpanned σ U := by
  first | exact @GlobalTheory.SplitField.endSpanned_of_isIrrSub_of_isAlgClosed | exact GlobalTheory.SplitField.endSpanned_of_isIrrSub_of_isAlgClosed | (intros; apply GlobalTheory.SplitField.endSpanned_of_isIrrSub_of_isAlgClosed <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.exists_ideleClassGroupHom_open_kernel : ∀ (E : Type) [Field E] [NumberField E], ∃ cl : Ideles E →* ClassGroup (𝓞 E), IsOpen (cl.ker : Set (Ideles E)) ∧ (diagUnits E).range ⊔ infConn E ≤ cl.ker ∧ (∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnitAt v x → cl (localIdele E v x) = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnifAt v x → cl (localIdele E v x) = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  first | exact @GlobalTheory.exists_ideleClassHom | exact GlobalTheory.exists_ideleClassHom | (intros; apply GlobalTheory.exists_ideleClassHom <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.splitEx_every_datum : ∀ D : D7, Formalism.L2.SplitEx D := by
  first | exact @GlobalTheory.SplitConjPlace.splitEx_all | exact GlobalTheory.SplitConjPlace.splitEx_all | (intros; apply GlobalTheory.SplitConjPlace.splitEx_all <;> assumption)
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.exists_irreducible_constituents_charpoly_product : SSList := by
  first | exact @GlobalTheory.ssList_holds | exact GlobalTheory.ssList_holds | (intros; apply GlobalTheory.ssList_holds <;> assumption)

end
end
