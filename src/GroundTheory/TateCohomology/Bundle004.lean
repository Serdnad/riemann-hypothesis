module

public import GroundTheory.TateCohomology.Bundle001
public import GroundTheory.TateCohomology.HerbrandAbstract
public import GroundTheory.TateCohomology.Bundle002
public import GroundTheory.TateCohomology.CupProduct
public import Mathlib.Tactic.Continuity
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import GroundTheory.TateCohomology.Bundle003
public import GroundTheory.TateCohomology.TateLow
public import GroundTheory.TateCohomology.InducedNorm
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
public import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

universe u

open CategoryTheory

theorem natCard_kerModRange_eq_relIndex {A : Type*} [AddCommGroup A] (f g : A →+ A) :
    Nat.card (KerModRange f g) = g.range.relIndex f.ker :=
  rfl

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]


omit [Fintype G] in
theorem ker_repSubOne (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    (repSubOne A σ).ker = A.ρ.invariants.toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, repSubOne_apply, sub_eq_zero, Submodule.mem_toAddSubgroup,
    Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ σ hσ]

theorem range_repSubOne (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    (repSubOne A σ).range = (Representation.Coinvariants.ker A.ρ).toAddSubgroup := by
  rw [Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ σ hσ]
  ext x
  rw [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  rfl

theorem ker_repNorm (A : Rep.{u} R G) :
    (repNorm A).ker = (LinearMap.ker A.ρ.norm).toAddSubgroup :=
  rfl

theorem range_repNorm (A : Rep.{u} R G) :
    (repNorm A).range = (LinearMap.range A.ρ.norm).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  rfl

theorem natCard_tateCohomology_zero (A : Rep.{u} R G) {σ : G}
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology A 0) = Nat.card (KerModRange (repSubOne A σ) (repNorm A)) := by
  rw [natCard_kerModRange_eq_relIndex, ker_repSubOne A hσ, range_repNorm]
  exact Nat.card_congr ((tateCohomologyZeroIso (R := R) (G := G)).app A).toLinearEquiv.toEquiv

theorem natCard_tateCohomology_neg_one (A : Rep.{u} R G) {σ : G}
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology A (-1)) = Nat.card (KerModRange (repNorm A) (repSubOne A σ)) := by
  rw [natCard_kerModRange_eq_relIndex, ker_repNorm, range_repSubOne A hσ]
  exact Nat.card_congr ((tateCohomologyNegOneIso (R := R) (G := G)).app A).toLinearEquiv.toEquiv

end GroundTheory.GroupCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep
open scoped MonoidAlgebra

universe u

section Def

variable {k G : Type u} [CommRing k] [Group G]

def CohTrivial (A : Rep.{u} k G) : Prop :=
  ∀ (S : Subgroup G) [Fintype S], TateAcyclic (res S.subtype A)

theorem CohTrivial.of_retract {M N : Rep.{u} k G} (i : M ⟶ N) (r : N ⟶ M) (h : i ≫ r = 𝟙 M)
    (hN : CohTrivial N) : CohTrivial M := fun S _ =>
  (hN S).of_retract ((resFunctor S.subtype).map i) ((resFunctor S.subtype).map r)
    (by rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id])

theorem CohTrivial.of_iso {M N : Rep.{u} k G} (e : M ≅ N) (hN : CohTrivial N) : CohTrivial M :=
  hN.of_retract e.hom e.inv e.hom_inv_id

end Def

section Norm

variable {k G : Type u} [CommRing k] [Group G]

theorem sum_eq_sum_quotient_sum [Fintype G] (S : Subgroup G) [Fintype S] [Fintype (G ⧸ S)]
    {β : Type*} [AddCommMonoid β] (f : G → β) :
    ∑ g : G, f g = ∑ c : G ⧸ S, ∑ s : S, f (c.out * s) := by
  let e : (G ⧸ S) × S ≃ G :=
    { toFun := fun x => x.1.out * x.2
      invFun := fun g => ((g : G ⧸ S), cosetPart S g)
      left_inv := fun x => by
        obtain ⟨c, s⟩ := x
        ext
        · exact mk_out_mul S c s
        · simp only [cosetPart_out_mul]
      right_inv := fun g => out_mul_cosetPart S g }
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm

variable {V : Type*} [AddCommGroup V] [Module k V]

theorem exists_sum_eq_subgroup [Fintype G] (ρ : Representation k G V) (φ : V →ₗ[k] V)
    (hφ : ∀ v, ∑ g : G, ρ g (φ (ρ g⁻¹ v)) = v) (S : Subgroup G) [Fintype S] :
    ∃ ψ : V →ₗ[k] V, ∀ v, ∑ s : S, ρ s (ψ (ρ (s⁻¹ : S) v)) = v := by
  classical
  refine ⟨∑ c : G ⧸ S, ρ c.out⁻¹ ∘ₗ φ ∘ₗ ρ c.out, fun v => ?_⟩
  conv_rhs => rw [← hφ v]
  rw [← Fintype.sum_equiv (Equiv.inv G) (fun h => ρ h⁻¹ (φ (ρ h v))) _ (fun h => by simp),
    sum_eq_sum_quotient_sum S, Finset.sum_comm]
  refine Fintype.sum_equiv (Equiv.inv S) _ _ fun s => ?_

  simp [map_sum, LinearMap.sum_apply, map_mul, mul_inv_rev, Module.End.mul_apply]

theorem cohTrivial_of_sum_eq [Fintype G] (M : Rep.{u} k G) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) : CohTrivial M := fun S _ => by
  obtain ⟨ψ, hψ⟩ := exists_sum_eq_subgroup M.ρ φ hφ S
  exact tateAcyclic_of_sum_eq (res S.subtype M) ψ hψ

variable [Fintype G]

theorem cohTrivial_coind_bot (B : Rep.{u} k (⊥ : Subgroup G)) :
    CohTrivial (coind (⊥ : Subgroup G).subtype B) :=
  cohTrivial_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)

theorem cohTrivial_ind_bot (B : Rep.{u} k (⊥ : Subgroup G)) :
    CohTrivial (ind (⊥ : Subgroup G).subtype B) := by
  classical
  exact (cohTrivial_coind_bot B).of_iso (indCoindIso B)

theorem exists_sum_eq_of_basis (M : Rep.{u} k G) {ι : Type*}
    (b : Module.Basis ι k[G] M.ρ.asModule) :
    ∃ φ : M.V →ₗ[k] M.V, ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m := by
  let φ : M.V →ₗ[k] M.V := M.ρ.asModuleEquiv.toLinearMap ∘ₗ
    (b.repr.symm.toLinearMap.restrictScalars k) ∘ₗ Finsupp.mapRange.linearMap coeffOneProj ∘ₗ
    (b.repr.toLinearMap.restrictScalars k) ∘ₗ M.ρ.asModuleEquiv.symm.toLinearMap
  refine ⟨φ, fun m => ?_⟩
  apply M.ρ.asModuleEquiv.symm.injective
  apply b.repr.injective

  simp only [map_sum, φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars,
  Representation.asModuleEquiv_symm_map_rho, map_smul, LinearEquiv.symm_apply_apply,
  LinearEquiv.apply_symm_apply]
  generalize b.repr (M.ρ.asModuleEquiv.symm m) = c
  ext i : 1
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, coeffOneProj_apply, smul_eq_mul,
    MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.single_mul_single,
    mul_one, one_mul, inv_inv]
  conv_rhs => rw [← MonoidAlgebra.sum_coeff_single (c i)]
  exact (Finsupp.sum_fintype _ _ (by simp)).symm

theorem cohTrivial_of_free (M : Rep.{u} k G) [Module.Free k[G] M.ρ.asModule] : CohTrivial M := by
  obtain ⟨φ, hφ⟩ := exists_sum_eq_of_basis M (Module.Free.chooseBasis k[G] M.ρ.asModule)
  exact cohTrivial_of_sum_eq M φ hφ

theorem cohTrivial_free (α : Type u) : CohTrivial (free k G α) := by
  have := Representation.free_asModule_free k G α
  exact cohTrivial_of_free _

end Norm

section ShortExact

variable {k G : Type u} [CommRing k] [Group G]

theorem TateAcyclic.of_shortExact_X₃ [Fintype G] {S : ShortComplex (Rep.{u} k G)}
    (hS : S.ShortExact) (h₂ : TateAcyclic S.X₂) (h₃ : TateAcyclic S.X₃) : TateAcyclic S.X₁ :=
  fun n => by
    have e := @asIso _ _ _ _ (TateCohomology.δ hS (n - 1)) (isIso_δ_of_tateAcyclic hS h₂ (n - 1))
    have h := (h₃ (n - 1)).of_iso e.symm
    rwa [sub_add_cancel] at h

theorem TateAcyclic.of_shortExact_X₁ [Fintype G] {S : ShortComplex (Rep.{u} k G)}
    (hS : S.ShortExact) (h₂ : TateAcyclic S.X₂) (h₁ : TateAcyclic S.X₁) : TateAcyclic S.X₃ :=
  fun n => (h₁ (n + 1)).of_iso
    (@asIso _ _ _ _ (TateCohomology.δ hS n) (isIso_δ_of_tateAcyclic hS h₂ n))

theorem CohTrivial.of_shortExact_X₃ {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (h₂ : CohTrivial S.X₂) (h₃ : CohTrivial S.X₃) : CohTrivial S.X₁ := by
  intro H _
  have hS' : (S.map (resFunctor H.subtype)).ShortExact := (shortExact_res H.subtype).2 hS
  have a : TateAcyclic (S.map (resFunctor H.subtype)).X₂ := by
    rw [ShortComplex.map_X₂]; exact h₂ H
  have b : TateAcyclic (S.map (resFunctor H.subtype)).X₃ := by
    rw [ShortComplex.map_X₃]; exact h₃ H
  have c := TateAcyclic.of_shortExact_X₃ hS' a b
  rw [ShortComplex.map_X₁] at c
  exact c

theorem CohTrivial.of_shortExact_X₁ {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (h₂ : CohTrivial S.X₂) (h₁ : CohTrivial S.X₁) : CohTrivial S.X₃ := by
  intro H _
  have hS' : (S.map (resFunctor H.subtype)).ShortExact := (shortExact_res H.subtype).2 hS
  have a : TateAcyclic (S.map (resFunctor H.subtype)).X₂ := by
    rw [ShortComplex.map_X₂]; exact h₂ H
  have b : TateAcyclic (S.map (resFunctor H.subtype)).X₁ := by
    rw [ShortComplex.map_X₁]; exact h₁ H
  have c := TateAcyclic.of_shortExact_X₁ hS' a b
  rw [ShortComplex.map_X₃] at c
  exact c

end ShortExact

section Rat

variable {G : Type} [Group G]

end Rat

end GroundTheory.GroupCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

section UniquelyDivisible

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem tateAcyclic_of_bijective_nsmul (M : Rep.{u} k G)
    (h : Function.Bijective fun m : M => Fintype.card G • m) : TateAcyclic M := by
  let f : M.V →ₗ[k] M.V := Fintype.card G • LinearMap.id
  have hf : ∀ m : M, f m = Fintype.card G • m := fun m => rfl
  have hb : Function.Bijective f := by
    have : (f : M → M) = fun m : M => Fintype.card G • m := funext hf
    rw [this]; exact h
  let e := LinearEquiv.ofBijective f hb
  have he : ∀ m : M, Fintype.card G • e.symm m = m := fun m => by
    rw [← hf]; exact e.apply_symm_apply m
  have hc : ∀ (g : G) (x : M), M.ρ g (e.symm x) = e.symm (M.ρ g x) := by
    intro g x
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    change f (M.ρ g (e.symm x)) = M.ρ g x
    rw [hf, ← map_nsmul, he]
  refine tateAcyclic_of_sum_eq M e.symm.toLinearMap fun m => ?_
  have hg : ∀ g : G, M.ρ g (e.symm.toLinearMap (M.ρ g⁻¹ m)) = e.symm m := fun g => by
    rw [LinearEquiv.coe_coe, hc, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  rw [Finset.sum_congr rfl fun g _ => hg g, Finset.sum_const, Finset.card_univ, he]

theorem isZero_groupCohomology_of_bijective_nsmul (M : Rep.{u} k G)
    (h : Function.Bijective fun m : M => Fintype.card G • m) (n : ℕ) [NeZero n] :
    IsZero (groupCohomology M n) :=
  (tateAcyclic_of_bijective_nsmul M h n).of_iso
    ((TateCohomology.isoGroupCohomology (R := k) (G := G) n).app M).symm

end UniquelyDivisible

section Rat

variable {G : Type} [Group G] [Fintype G]

theorem bijective_nsmul_of_module_rat {V : Type*} [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (hn : n ≠ 0) : Function.Bijective fun v : V => n • v := by
  have : (fun v : V => n • v) = LinearEquiv.smulOfUnit (M := V)
      (IsUnit.unit (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn) : IsUnit (n : ℚ))) := by
    funext v
    change _ = IsUnit.unit (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn) : IsUnit (n : ℚ)) • v
    rw [Units.smul_def, IsUnit.unit_spec, Nat.cast_smul_eq_nsmul]
  rw [this]
  exact LinearEquiv.bijective _

theorem isZero_groupCohomology_trivial_rat (n : ℕ) [NeZero n] :
    IsZero (groupCohomology (Rep.trivial ℤ G ℚ) n) :=
  isZero_groupCohomology_of_bijective_nsmul _
    (bijective_nsmul_of_module_rat (V := ℚ) Fintype.card_ne_zero) n

end Rat

end GroundTheory.GroupCoh
end

section

set_option maxSynthPendingDepth 1

noncomputable section

universe u

open CategoryTheory MonoidalCategory TensorProduct groupCohomology Rep

namespace GroundTheory.GroupCoh

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

theorem partialProd_comp {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {m : ℕ}
    (x : Fin m → M) (i : Fin (m + 1)) :
    Fin.partialProd (f ∘ x) i = f (Fin.partialProd x i) := by
  simp [Fin.partialProd, ← List.map_ofFn, ← List.map_take, map_list_prod]

variable (f : G →* H) {A₁ A₂ : Rep k H} {B₁ B₂ : Rep k G} {p q n : ℕ}

def resTensorHom (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) : res f (A₁ ⊗ A₂) ⟶ B₁ ⊗ B₂ :=
  ConcreteCategory.ofHom (C := Rep k G)
    { toLinearMap := TensorProduct.map φ₁.hom.toLinearMap φ₂.hom.toLinearMap
      isIntertwining' := fun g => TensorProduct.ext' fun a b => by
        change φ₁.hom (A₁.ρ (f g) a) ⊗ₜ[k] φ₂.hom (A₂.ρ (f g) b) =
          B₁.ρ g (φ₁.hom a) ⊗ₜ[k] B₂.ρ g (φ₂.hom b)
        rw [← Rep.hom_comm_apply φ₁, ← Rep.hom_comm_apply φ₂]
        rfl }

theorem resTensorHom_tmul (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (a : A₁) (b : A₂) :
    (resTensorHom f φ₁ φ₂).hom (a ⊗ₜ[k] b : (A₁ ⊗ A₂ : Rep k H)) = φ₁.hom a ⊗ₜ[k] φ₂.hom b :=
  rfl

theorem resTensorHom_cupCochain (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (h : p + q = n)
    (x : (Fin p → H) → A₁) (y : (Fin q → H) → A₂) (g : Fin n → G) :
    (resTensorHom f φ₁ φ₂).hom (cupCochain h x y (f ∘ g)) =
      cupCochain h (fun v => φ₁.hom (x (f ∘ v))) (fun v => φ₂.hom (y (f ∘ v))) g := by
  rw [cupCochain_apply, resTensorHom_tmul, cupCochain_apply, partialProd_comp]
  exact congrArg _ (Rep.hom_comm_apply φ₂ _ _)

theorem map_π_apply' {A : Rep k H} {B : Rep k G} (φ : res f A ⟶ B) (z : cocycles A n) :
    map f φ n (π A n z) = π B n (cocyclesMap f φ n z) := by
  change (π A n ≫ map f φ n).hom z = (cocyclesMap f φ n ≫ π B n).hom z
  rw [π_map]

theorem iCocycles_cocyclesMap' {A : Rep k H} {B : Rep k G} (φ : res f A ⟶ B)
    (z : cocycles A n) :
    iCocycles B n (cocyclesMap f φ n z) = fun g => φ.hom (iCocycles A n z (f ∘ g)) := by
  change (cocyclesMap f φ n ≫ iCocycles B n).hom z = _
  rw [HomologicalComplex.cyclesMap_i]
  rfl

theorem map_resTensorHom_cupH (φ₁ : res f A₁ ⟶ B₁) (φ₂ : res f A₂ ⟶ B₂) (h : p + q = n)
    (a : groupCohomology A₁ p) (b : groupCohomology A₂ q) :
    map f (resTensorHom f φ₁ φ₂) n (cupH h a b) = cupH h (map f φ₁ p a) (map f φ₂ q b) := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  have key : cocyclesMap (A := A₁ ⊗ A₂) f (resTensorHom f φ₁ φ₂) n (cupCocycles h z w) =
      cupCocycles h (cocyclesMap f φ₁ p z) (cocyclesMap f φ₂ q w) := by
    refine cocycles_ext ?_
    rw [iCocycles_cocyclesMap', iCocycles_cupCocycles, iCocycles_cupCocycles,
      iCocycles_cocyclesMap', iCocycles_cocyclesMap']
    funext g
    exact resTensorHom_cupCochain f φ₁ φ₂ h _ _ g
  rw [cupH_π, map_π_apply', map_π_apply', map_π_apply', cupH_π, key]

end GroundTheory.GroupCoh
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

theorem norm_apply_of_mem_invariants (A : Rep.{u} R G) {a : A} (ha : a ∈ A.ρ.invariants) :
    A.ρ.norm a = Fintype.card G • a := by
  rw [Representation.mem_invariants] at ha
  simp [Representation.norm, LinearMap.sum_apply, ha]

theorem card_smul_tateCohomology_zero (A : Rep.{u} R G) (x : tateCohomology A 0) :
    Fintype.card G • x = 0 := by
  let e := ((tateCohomologyZeroIso (R := R) (G := G)).app A).toLinearEquiv
  apply e.injective
  rw [map_nsmul, map_zero]
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (normRangeInvariants A) (e x)
  rw [← hy]
  have h : (Submodule.Quotient.mk (Fintype.card G • y) :
      A.ρ.invariants ⧸ normRangeInvariants A) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero, mem_normRangeInvariants_iff]
    exact ⟨y, by rw [norm_apply_of_mem_invariants A y.2]; rfl⟩
  rw [Submodule.Quotient.mk_smul] at h
  exact h

private theorem card_smul_succ {n : ℤ}
    (h : ∀ (A : Rep.{u} R G) (x : tateCohomology A n), Fintype.card G • x = 0)
    (A : Rep.{u} R G) (x : tateCohomology A (n + 1)) : Fintype.card G • x = 0 := by
  let e := (coindShiftIso A n).toLinearEquiv
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [← map_nsmul, h, map_zero]

private theorem card_smul_pred {n : ℤ}
    (h : ∀ (A : Rep.{u} R G) (x : tateCohomology A (n + 1)), Fintype.card G • x = 0)
    (A : Rep.{u} R G) (x : tateCohomology A n) : Fintype.card G • x = 0 := by
  let e := (indShiftIso A n).toLinearEquiv
  apply e.injective
  rw [map_nsmul, map_zero, h]

theorem card_smul_tateCohomology (A : Rep.{u} R G) (n : ℤ) (x : tateCohomology A n) :
    Fintype.card G • x = 0 := by
  induction n using Int.induction_on generalizing A with
  | zero => exact card_smul_tateCohomology_zero A x
  | succ n ih => exact card_smul_succ (fun A x => ih A x) A x
  | pred n ih =>
    refine card_smul_pred ?_ A x
    rw [sub_add_cancel]
    exact ih

end GroundTheory.GroupCoh
end
