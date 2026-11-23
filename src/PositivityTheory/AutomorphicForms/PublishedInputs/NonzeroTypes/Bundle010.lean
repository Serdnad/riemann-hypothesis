module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle413
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle003
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle006

@[expose] public section

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.Subquotient₂

variable {F H V : Type} [Field F] [Group H] [AddCommGroup V] [Module F V]

theorem wellFoundedGT_of_finiteLength {ρ : Representation F H V} (h : HasFiniteLength ρ) :
    WellFoundedGT (Subrepresentation ρ) := by
  have hN := (isFiniteLength_iff_isNoetherian_isArtinian.mp h).1
  have := isNoetherian_iff'.mp hN
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).strictMono.wellFoundedGT

theorem wellFoundedLT_of_finiteLength {ρ : Representation F H V} (h : HasFiniteLength ρ) :
    WellFoundedLT (Subrepresentation ρ) := by
  have hA := (isFiniteLength_iff_isNoetherian_isArtinian.mp h).2
  have : WellFoundedLT (Submodule (MonoidAlgebra F H) ρ.asModule) := hA
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).strictMono.wellFoundedLT

theorem exists_covBy {ρ : Representation F H V} (h : HasFiniteLength ρ) {y : V} (hy : y ≠ 0) :
    ∃ S T : Subrepresentation ρ, T ⋖ S ∧ y ∈ S.toSubmodule ∧ y ∉ T.toSubmodule := by
  have := wellFoundedGT_of_finiteLength h
  have := wellFoundedLT_of_finiteLength h
  obtain ⟨T, hT, hmax⟩ := wellFounded_gt.has_min {T : Subrepresentation ρ | y ∉ T.toSubmodule}
    ⟨⊥, fun h' => hy ((Submodule.mem_bot F).1 h')⟩
  have hTtop : T ≠ ⊤ := by
    rintro rfl
    exact hT trivial
  obtain ⟨S, hS, hmin⟩ := wellFounded_lt.has_min {S : Subrepresentation ρ | T < S}
    ⟨⊤, lt_top_iff_ne_top.2 hTtop⟩
  refine ⟨S, T, ⟨hS, fun U hTU hUS => hmin U hTU hUS⟩, ?_, hT⟩
  by_contra hyS
  exact hmax S hyS hS

end UpperTheory.TNZ.Grp.Subquotient₂

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_subq {n : ℕ} (G : Grp k n) : G.SubquotientProp := by
  intro W _ _ ρ hs hfl hη
  obtain ⟨y, hy, hyη⟩ := hη
  obtain ⟨S, T, hcov, hyS, hyT⟩ := Subquotient₂.exists_covBy hfl hy
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hsq : IsSubquotient (subQuot S T) ρ := ⟨S, p, Submodule.mkQ_surjective _⟩
  refine ⟨_, inferInstance, inferInstance, subQuot S T, hsq.isSmooth hs, isIrreducible_subQuot hcov, hsq,
    Submodule.Quotient.mk ⟨y, hyS⟩, ?_, fun m hm => ?_⟩
  · rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hyT
  · show Submodule.Quotient.mk (S.toRepresentation m ⟨y, hyS⟩) = _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (hyη m hm)

end UpperTheory.TNZ.Grp
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

namespace JacquetFiniteLength₂

variable {n : ℕ} (G : Grp k n)

theorem hasFiniteLength_jacU (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hπ : IsSmooth π) (hfl : HasFiniteLength π) :
    HasFiniteLength (jacU G.e π) :=
  (GlobalTheory.JacquetBlocks.hasFiniteLength_twist_iff (jacU G.e π) (deltaHalf k _)⁻¹).1
    ((hBZ k).2.1 _ _ _ G.e V π hπ hfl)

end JacquetFiniteLength₂

theorem step_jacFin {n : ℕ} (G : Grp k n) : G.JacquetModuleFiniteProp := by
  intro L V _ _ π hπ hirr
  exact ⟨isSmooth_jacU G.e hπ,
    JacquetFiniteLength₂.hasFiniteLength_jacU G L.loc.bz π hπ (hasFiniteLength_of_isIrreducible hirr)⟩

end Grp

end UpperTheory.TNZ
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct
open Module

namespace UpperTheory.TNZ.Grp.Tensor₂

section Contr

variable {ι : Type} [Fintype ι] [hd : DecidableEq ι] {Y : ι → Type} [∀ b, AddCommGroup (Y b)]
  [∀ b, Module ℂ (Y b)]

theorem prod_update (a : ι) (φ : ∀ b, Module.Dual ℂ (Y b)) (x : ∀ b, Y b) (i : ι) (hi : i ≠ a) (w : Y i) :
    ∏ b ∈ Finset.univ.erase a, φ b (Function.update x i w b) =
      φ i w * ∏ b ∈ (Finset.univ.erase a).erase i, φ b (x b) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]

theorem prod_update_self (a : ι) (φ : ∀ b, Module.Dual ℂ (Y b)) (x : ∀ b, Y b) (w : Y a) :
    ∏ b ∈ Finset.univ.erase a, φ b (Function.update x a w b) = ∏ b ∈ Finset.univ.erase a, φ b (x b) :=
  Finset.prod_congr rfl fun b hb => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]

def contrML (a : ι) (φ : ∀ b, Module.Dual ℂ (Y b)) : (∀ b, Y b) →ₘₗ[ℂ] Y a where
  toFun x := (∏ b ∈ Finset.univ.erase a, φ b (x b)) • x a
  map_update_add' := by
    intro inst x i u v
    obtain rfl : inst = hd := Subsingleton.elim _ _
    by_cases h : i = a
    · subst h
      simp only [prod_update_self, Function.update_self, smul_add]
    · simp only [prod_update a φ x i h, Function.update_of_ne (Ne.symm h), map_add (f := _), add_mul, add_smul]
  map_update_smul' := by
    intro inst x i c u
    obtain rfl : inst = hd := Subsingleton.elim _ _
    simp only [RingHom.id_apply]
    by_cases h : i = a
    · subst h
      simp only [prod_update_self, Function.update_self]
      rw [smul_comm]
    · simp only [prod_update a φ x i h, Function.update_of_ne (Ne.symm h), map_smul, smul_eq_mul]
      rw [mul_assoc, mul_smul]

def contr (a : ι) (φ : ∀ b, Module.Dual ℂ (Y b)) : (⨂[ℂ] b, Y b) →ₗ[ℂ] Y a :=
  PiTensorProduct.lift (contrML a φ)

theorem contr_tprod (a : ι) (φ : ∀ b, Module.Dual ℂ (Y b)) (x : ∀ b, Y b) :
    contr a φ (PiTensorProduct.tprod ℂ x) = (∏ b ∈ Finset.univ.erase a, φ b (x b)) • x a := by
  rw [contr, PiTensorProduct.lift.tprod]
  rfl

theorem exists_factor_vec {Γ : ι → Type} [∀ b, Group (Γ b)] (ρ : ∀ b, Representation ℂ (Γ b) (Y b)) (a : ι)
    (y : ⨂[ℂ] b, Y b) (hy : y ≠ 0) (S : Set (Γ a)) (c : Γ a → ℂ)
    (h : ∀ g ∈ S, piTensor ρ (Pi.mulSingle a g) y = c g • y) :
    ∃ v : Y a, v ≠ 0 ∧ ∀ g ∈ S, ρ a g v = c g • v := by
  let bs := fun b => Module.Basis.ofVectorSpace ℂ (Y b)
  let B := Basis.piTensorProduct bs
  obtain ⟨p, hp⟩ : ∃ p, B.repr y p ≠ 0 := by
    by_contra H
    simp only [not_exists, not_not] at H
    refine hy (B.repr.injective ?_)
    ext p
    rw [H p, map_zero, Finsupp.zero_apply]
  let φ : ∀ b, Module.Dual ℂ (Y b) := fun b => (bs b).coord (p b)
  have key : ∀ z, (bs a).coord (p a) (contr a φ z) = B.repr z p := by
    intro z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      simp only [map_smul, contr_tprod, B, Basis.piTensorProduct_repr_tprod_apply, Finsupp.smul_apply,
        smul_eq_mul, Basis.coord_apply, φ]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
      ring
    | add z w hz hw => rw [map_add (f := _), map_add (f := _), hz, hw, map_add (f := _), Finsupp.add_apply]
  have hequiv : ∀ g z, contr a φ (piTensor ρ (Pi.mulSingle a g) z) = ρ a g (contr a φ z) := by
    intro g z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      have hpr : ∏ b ∈ Finset.univ.erase a, φ b (ρ b (Pi.mulSingle a g b) (x b)) =
          ∏ b ∈ Finset.univ.erase a, φ b (x b) := by
        refine Finset.prod_congr rfl fun b hb => ?_
        rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hb), map_one, Module.End.one_apply]
      simp only [map_smul, piTensor_tprod, contr_tprod, Pi.mulSingle_eq_same, hpr]
    | add z w hz hw => simp only [map_add (f := _), hz, hw]
  refine ⟨contr a φ y, fun h0 => hp ?_, fun g hg => ?_⟩
  · rw [← key, h0, map_zero]
  · rw [← hequiv, h g hg, map_smul]

end Contr

end UpperTheory.TNZ.Grp.Tensor₂

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_tensor {n : ℕ} (G : Grp k n) : G.TensorProductProp := by
  intro hN X _ _ σ hs hirr hη
  obtain ⟨y, hy0, hy⟩ := hη
  obtain ⟨s, ⟨E⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hN.loc.bz k (Fin G.s)
    (fun a => Fin (G.d a)) { V := X, ρ := σ, smooth := hs, irr := hirr }
  refine ⟨fun a => (s a).V, fun a => inferInstance, fun a => inferInstance, fun a => (s a).ρ,
    fun a => (s a).smooth, fun a => (s a).irr, fun a => ?_, ⟨E⟩⟩
  have hE : ∀ m, E (σ m y) = piTensor (fun b => (s b).ρ) m (E y) := fun m =>
    LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' m) y
  have hEy : E y ≠ 0 := (map_ne_zero_iff E (EquivLike.injective E)).2 hy0
  have hK : ∀ g ∈ (KO k (Fin (G.d a)) : Set (GL (Fin (G.d a)) k)),
      piTensor (fun b => (s b).ρ) (Pi.mulSingle a g) (E y) =
        ((G.μ a (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • E y := by
    intro g hg
    have hm : (Pi.mulSingle a g : Levi k fun b : Fin G.s => Fin (G.d b)) ∈
        leviK k (m := fun b : Fin G.s => Fin (G.d b)) := by
      rw [leviK, Subgroup.mem_pi]
      intro b _
      by_cases hb : b = a
      · subst hb
        rw [Pi.mulSingle_eq_same]
        exact hg
      · rw [Pi.mulSingle_eq_of_ne hb]
        exact one_mem _
    rw [← hE, hy _ hm, map_smul]
    congr 1
    rw [eta, Finset.prod_eq_single a]
    · rw [Pi.mulSingle_eq_same]
    · intro b _ hb
      rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one, Units.val_one]
    · intro h
      exact absurd (Finset.mem_univ a) h
  exact Tensor₂.exists_factor_vec (fun b => (s b).ρ) a (E y) hEy _ _ hK

end UpperTheory.TNZ.Grp
end
end

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def SpecialLatticeProp : Prop :=
  ∀ (Γ V : Type) [Group Γ] [AddCommGroup V] [Module ℂ V] (I : Representation ℂ Γ V) (d : Subrepresentation I → ℕ),
    Monotone d → (∀ X Y, d (X ⊔ Y) + d (X ⊓ Y) = d X + d Y) → d ⊤ ≤ 1 →
    ∀ (A B : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
      (α : Representation ℂ Γ A) (β : Representation ℂ Γ B), α.IsIrreducible → β.IsIrreducible →
      (∃ X Y : Subrepresentation I, X ≤ Y ∧ d X < d Y ∧ Nonempty ((subQuot Y X).Equiv α)) →
      (∃ X Y : Subrepresentation I, X ≤ Y ∧ d X < d Y ∧ Nonempty ((subQuot Y X).Equiv β)) →
      Nonempty (α.Equiv β)

namespace Grp

variable {n : ℕ} (G : Grp k n)

def etaSp {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) W) :
    Submodule ℂ W :=
  ⨅ (m : Levi k fun a : Fin G.s => Fin (G.d a)) (_ : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a))),
    LinearMap.ker (ρ m - G.eta m • LinearMap.id)

def SphericalVectorUniqueness : Prop :=
  SpecialLatticeProp →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (I : Representation ℂ (GL (Fin n) k) V), IsSmooth I →
    FiniteDimensional ℂ ↥(G.etaSp (jacU G.e I)) → Module.finrank ℂ ↥(G.etaSp (jacU G.e I)) ≤ 1 →
    ∀ (A B : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
      (α : Representation ℂ (GL (Fin n) k) A) (β : Representation ℂ (GL (Fin n) k) B),
      α.IsIrreducible → β.IsIrreducible → IsSubquotient α I → IsSubquotient β I →
      G.HasEtaVec (jacU G.e α) → G.HasEtaVec (jacU G.e β) → Nonempty (α.Equiv β)

def SpecialLiftProp : Prop :=
  ∀ (W X : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) W)
    (σ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) X),
    IsSmooth ρ → IsSubquotient σ ρ → G.HasEtaVec σ → G.HasEtaVec ρ

def SpecialCountProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ c : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (c i)) → (∀ i, res (c i) = res (G.chi i)) →
    FiniteDimensional ℂ ↥(G.etaSp (jacU G.e (prinSeries c))) ∧
      Module.finrank ℂ ↥(G.etaSp (jacU G.e (prinSeries c))) ≤ 1

def twD {Y : Fin G.s → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)) (a : Fin G.s) :
    Representation ℂ (GL (Fin (G.d a)) k) (Y a) :=
  twist (τ a) (detChar (Fin (G.d a)) (absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))))

def cOf (ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ) (i : Fin n) : kˣ →* ℂˣ :=
  ν (G.e.symm i).1 (G.e.symm i).2 * absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) (G.e.symm i).1 : ℂ) / 2))

def NonzeroBasicTwistOfSpecialForm : Prop :=
  ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a))
    (a : Fin G.s), IsSmooth (τ a) → (τ a).IsIrreducible → HasDetVec (τ a) (G.μ a) →
    IsSmooth (G.twD τ a) ∧ (G.twD τ a).IsIrreducible ∧ HasDetVec (G.twD τ a) (G.μ a)

def SpecialRestrictionProp : Prop :=
  ∀ ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ, (∀ a j, res (ν a j) = res (G.μ a)) → ∀ i, res (G.cOf ν i) = res (G.chi i)

def SpecialRepresentationEtaProp : Prop :=
  G.SpecialLiftProp →
  ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
    (∀ a, IsSmooth (τ a)) → (∀ a, HasDetVec (τ a) (G.μ a)) →
    G.HasEtaVec (jacU G.e (multiProd G.e (G.twD τ)))

def SpecialOrderProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → ∀ c : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (c i)) →
    ∀ σ : Equiv.Perm (Fin n), IsSubquotient π (prinSeries (fun i => c (σ i))) → IsSubquotient π (prinSeries c)

def SpecialRepresentationSubProp : Prop :=
  SpecialOrderProp (k := k) (n := n) → GlobalTheory.Mem.LiteralAutomorphy.LitN →
  ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
    (∀ a, IsSmooth (τ a)) → (∀ a, (τ a).IsIrreducible) →
    ∀ ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ, (∀ a j, IsSmoothChar (ν a j)) →
    (∀ a, IsCuspSupport (τ a) (fun _ : Fin (G.d a) => 1) (fun j => detRep (Fin 1) (ν a j))) →
    (multiProd G.e (G.twD τ)).IsIrreducible →
    IsSubquotient (multiProd G.e (G.twD τ)) (prinSeries (G.cOf ν))

def SpecialSupportProp : Prop :=
  SpecialOrderProp (k := k) (n := n) → GlobalTheory.Mem.LiteralAutomorphy.LitN →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible →
    ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
      (∀ a, IsSmooth (τ a)) → (∀ a, (τ a).IsIrreducible) →
      ∀ ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ, (∀ a j, IsSmoothChar (ν a j)) →
      (∀ a, IsCuspSupport (τ a) (fun _ : Fin (G.d a) => 1) (fun j => detRep (Fin 1) (ν a j))) →
      IsSubquotient (piTensor τ) (jacU G.e π) → IsSubquotient π (prinSeries (G.cOf ν))

def NonzeroTopOfSpecialForm : Prop :=
  SpecialLatticeProp → G.SphericalVectorUniqueness → G.SpecialCountProp → G.SpecialLiftProp → G.NonzeroBasicTwistOfSpecialForm → G.SpecialRestrictionProp → G.SpecialRepresentationEtaProp →
    SpecialOrderProp (k := k) (n := n) → G.SpecialRepresentationSubProp → G.SpecialSupportProp → CuspidalSupportProp → ProductIrreducibleProp → TensorProductVectors →
    G.SupportOfProductProp

end Grp

end UpperTheory.TNZ
end
end

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

variable {n : ℕ} (G : Grp k n)

theorem jacProd_of (hjF : G.JacquetModuleFiniteProp) (hsub : G.SubquotientProp) (hten : G.TensorProductProp) (hsupp : G.SupportOfProductProp) :
    G.JacquetProductProp := by
  intro L V _ _ π hs hirr hy
  obtain ⟨hsm, hfl⟩ := hjF L V π hs hirr
  obtain ⟨X, _, _, σ, hσs, hσi, hsq, hση⟩ := hsub _ (jacU G.e π) hsm hfl hy
  obtain ⟨Y, _, _, τ, hτs, hτi, hτd, ⟨eqv⟩⟩ := hten L X σ hσs hσi hση
  refine hsupp L V π hs hirr Y τ hτs hτi hτd ?_
  obtain ⟨S, f, hf⟩ := hsq
  exact ⟨S, (eqv.toIntertwiningMap).comp f, eqv.toLinearEquiv.surjective.comp hf⟩

end Grp

def CSteps : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Grp.CompactConductorBasicProp (k := k) ∧ Grp.UniformizerProp (k := k) ∧ Grp.ExistsGroupElementProp (k := k) ∧ ∀ (n : ℕ) (G : Grp k n),
    G.CompactConductorBoundProp ∧ G.JacquetOneProp ∧ G.JacquetMultiplicativeProp ∧ G.JacquetInverseProp ∧ G.CompactOpenKernelProp ∧ G.ModulusOnUnitsProp ∧ G.ModulusMultiplicativeProp ∧
    G.LambdaMultiplicativeProp ∧ G.LambdaBasicProp ∧ G.LambdaUnipotentProp ∧ G.IwahoriDecompositionProp ∧ G.FixedSubspaceStableProp ∧ G.FixedSubspaceFiniteProp ∧ G.NonzeroLeviEigenvectorExists ∧
    G.ParabolicJacquetProp ∧ G.AnnihilationProp ∧ G.NonIntegralProp ∧ G.TorusCentreEigenProp ∧ G.TorusPowerProp ∧ G.JacquetKernelProp ∧ G.TorusCentreInjectiveProp ∧
    G.JacquetImageProp ∧ G.JacquetModuleFiniteProp ∧ G.SubquotientProp ∧ G.TensorProductProp ∧ G.SupportOfProductProp


open UpperTheory.NonzeroTypeTheory in
theorem need_CMain (hC : CSteps) (hlL : LeviSubgroupRestriction) (L : GlobalTheory.Mem.LiteralAutomorphy.LitN) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ρ.IsIrreducible →
    (∃ x : V, x ≠ 0 ∧ ∀ g ∈ G.JSet, ρ g x = G.lam g • x) → IsTwSphProd ρ G.d G.hd G.μ := by
  intro k _ _ _ _ n G V _ _ ρ hs hi hx
  obtain ⟨hcb, hun, -, hG⟩ := hC k
  obtain ⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, hlU, hiw, -, -, -, hPJ, hkill, hni, hTE, hTp, hjK, hTI,
    hjI, hjF, hsub, hten, hsupp⟩ := hG n G
  exact G.cMain hcb hccB hJone hJmul hJinv hKC hΔU hΔM hlM hlB hlU hiw hPJ hkill hni hTE hTp hjK hTI hun hlL hjI
    (G.jacProd_of hjF hsub hten hsupp) L V ρ hs hi hx


open UpperTheory.NonzeroTypeTheory in
theorem need_CProps (hC : CSteps) : Need_CProps := by
  intro k _ _ _ _ n G
  obtain ⟨hcb, -, -, hG⟩ := hC k
  obtain ⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, -, -, hV0s, hV0f, hv0, -⟩ := hG n G
  have hK := hKC hccB G.lev
  have hlB' := hlB hccB
  have hlM' := hlM hcb hΔU hΔM hccB
  obtain ⟨h1, h2, h3⟩ := hv0 hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC
  refine ⟨fun g hg => hg.1, hJone.1, fun g hg g' hg' => ⟨hJmul hcb hccB g hg g' hg', hlM' g hg g' hg'⟩, hJinv hcb hccB,
    fun g _ => hlB'.2.1 g, hK.2.2.1, ?_, hK.2.2.2.2 le_rfl, hlB'.2.2, fun φ hφ k' => hV0s hccB hKC k' φ hφ, hV0f hccB hKC, h1, h2, h3⟩
  rw [← hK.1]
  exact (KCg k n G.lev).one_mem


open UpperTheory.NonzeroTypeTheory in
theorem need_Grp (hC : CSteps) : Need_Grp := by
  intro k _ _ _ _ n μ hμ
  obtain ⟨-, -, hex, -⟩ := hC k
  obtain ⟨G, σ, h⟩ := hex n μ hμ
  exact ⟨G, σ, fun i => (h i).symm⟩

end UpperTheory.TNZ
end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

namespace DistinctCharacterUnits

theorem exists_unit_ne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {μ ν : kˣ →* ℂˣ} (hne : res μ ≠ res ν) : ∃ u : 𝒪[k]ˣ, μ (unitIncl k u) ≠ ν (unitIncl k u) := by
  by_contra hh
  push Not at hh
  exact hne (MonoidHom.ext hh)

end DistinctCharacterUnits

theorem distinctOnInertia_holds : DistinctOnUnitsDistinctOnInertia := by
  intro hA E Ω _ _ _ _ _ A w h a ha n G b c hbc
  obtain ⟨u, hu⟩ := DistinctCharacterUnits.exists_unit_ne (G.dist b c hbc)
  obtain ⟨t, ht⟩ := (hA E Ω A w h a ha).2 (unitIncl _ u) (valuation_eq_one_iff.mpr ⟨u, rfl⟩)
  exact ⟨t, by rw [ht]; exact hu⟩

end UpperTheory.NonzeroTypeTheory
end
end
