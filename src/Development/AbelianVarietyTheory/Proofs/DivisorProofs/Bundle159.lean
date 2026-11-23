module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularMapCAppendMapLinForm
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle034
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
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
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Unramified.LocalRing

@[expose] public section

section

open MvPolynomial TensorProduct

noncomputable section

namespace GlobalTheory.GenericForm

variable (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] (N : ℕ)

def polyEquiv : MvPolynomial (Fin N) k ⊗[k] A ≃+* MvPolynomial (Unit × Fin N) A :=
  ((Algebra.TensorProduct.comm k (MvPolynomial (Fin N) k) A).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv k A).toRingEquiv).trans
    (renameEquiv A (Equiv.punitProd (Fin N)).symm).toRingEquiv

theorem polyEquiv_X_tmul (i : Fin N) (x : A) :
    polyEquiv k A N (X i ⊗ₜ x) = C x * X ((), i) := by
  simp [polyEquiv, smul_eq_C_mul]

theorem polyEquiv_one_tmul (x : A) : polyEquiv k A N (1 ⊗ₜ x) = C x := by
  simp [polyEquiv, smul_eq_C_mul]

variable {k A N}

def genForm (a : Fin N → A) : MvPolynomial (Fin N) k ⊗[k] A := ∑ i, X i ⊗ₜ a i

theorem polyEquiv_genForm (a : Fin N → A) :
    polyEquiv k A N (genForm (k := k) a) = linForm a () := by

  simp [genForm, linForm, map_sum, polyEquiv_X_tmul]

theorem isDomain_tensor : IsDomain (MvPolynomial (Fin N) k ⊗[k] A) :=
  Function.Injective.isDomain (polyEquiv k A N).toRingHom
    (polyEquiv k A N).injective

theorem genForm_ne_zero (a : Fin N → A) {j : Fin N} (hu : IsUnit (a j)) :
    genForm (k := k) a ≠ 0 := by
  intro h
  have h1 := congrArg (polyEquiv k A N) h
  rw [polyEquiv_genForm, map_zero, ← linFormEquiv_X_of_mem (ι := Unit) a hu (Set.mem_univ ())] at h1
  exact X_ne_zero _ ((linFormEquiv a Set.univ j hu).injective (h1.trans (map_zero _).symm))

theorem map_span_genForm (a : Fin N → A) :
    (Ideal.span {genForm (k := k) a}).map (polyEquiv k A N) = Ideal.span {linForm a ()} := by
  rw [Ideal.map_span, Set.image_singleton, polyEquiv_genForm]

theorem isPrime_span_genForm (a : Fin N → A) {j : Fin N} (hu : IsUnit (a j)) :
    (Ideal.span {genForm (k := k) a}).IsPrime := by
  have hp : (Ideal.span {linForm a ()}).IsPrime := by
    have := isPrime_span_linForm (ι := Unit) a hu Set.univ
    rwa [Set.image_univ, Set.range_unique] at this
  have : Ideal.span {genForm (k := k) a} =
      (Ideal.span {linForm a ()}).map (polyEquiv k A N).symm := by
    rw [Ideal.map_span, Set.image_singleton, ← polyEquiv_genForm (k := k) a, RingEquiv.symm_apply_apply]
  rw [this]
  exact Ideal.map_isPrime_of_equiv _

theorem eq_zero_of_one_tmul_mem (a : Fin N → A) {j : Fin N} (hu : IsUnit (a j)) {x : A}
    (hx : (1 : MvPolynomial (Fin N) k) ⊗ₜ[k] x ∈ Ideal.span {genForm (k := k) a}) : x = 0 := by
  have h1 := Ideal.mem_map_of_mem (polyEquiv k A N) hx
  rw [map_span_genForm, polyEquiv_one_tmul] at h1
  have h2 : C x ∈ RingHom.ker (linFormElim a hu (Set.univ : Set Unit)) := by
    rw [ker_linFormElim, Set.image_univ, Set.range_unique]
    exact h1
  rw [RingHom.mem_ker, algHom_C, algebraMap_eq, C_eq_zero] at h2
  exact h2

theorem span_genericForm_isPrime_or_eq_top :
    ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] (N : ℕ) (a : Fin N → A)
      (j : Fin N), IsUnit (a j) → ∀ t : FractionRing (MvPolynomial (Fin N) k) ⊗[k] A,
      t = ∑ i, algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k))
        (MvPolynomial.X i) ⊗ₜ[k] a i →
      t ≠ 0 ∧ (Ideal.span {t} = ⊤ ∨ (Ideal.span {t}).IsPrime ∧
        ∀ x : A, (1 : FractionRing (MvPolynomial (Fin N) k)) ⊗ₜ[k] x ∈ Ideal.span {t} → x = 0) := by
  intro k A _ _ _ _ N a j hu t ht
  let P := MvPolynomial (Fin N) k
  let K := FractionRing P
  let B := P ⊗[k] A
  haveI : IsDomain B := isDomain_tensor
  let φ : B →ₐ[k] K ⊗[k] A :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P K) (AlgHom.id k A)
  letI : Algebra B (K ⊗[k] A) := φ.toRingHom.toAlgebra
  have hφ : ∀ x, algebraMap B (K ⊗[k] A) x = φ x := fun _ => rfl
  haveI : IsScalarTower P B (K ⊗[k] A) := by
    refine IsScalarTower.of_algebraMap_eq fun p => ?_
    rw [hφ]
    simp [φ, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have H : (algebraMap B (K ⊗[k] A)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
    ext x
    change φ (1 ⊗ₜ[k] x) = 1 ⊗ₜ[k] x
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  let M : Submonoid B := Algebra.algebraMapSubmonoid B (nonZeroDivisors P)
  haveI hL : IsLocalization M (K ⊗[k] A) :=
    IsLocalization.tensorProduct_tensorProduct k A (nonZeroDivisors P) K H
  have hkA : Function.Injective (algebraMap k A) := (algebraMap k A).injective
  have hM : M ≤ nonZeroDivisors B := by
    rintro _ ⟨p, hp, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero hp ?_
    refine Algebra.TensorProduct.includeLeft_injective (R := k) (S := k) (A := P) (B := A) hkA ?_
    rw [map_zero]
    exact h
  have hinj : Function.Injective (algebraMap B (K ⊗[k] A)) := IsLocalization.injective _ hM
  have ht0 : t = algebraMap B (K ⊗[k] A) (genForm (k := k) a) := by

    rw [ht, hφ, genForm, map_sum]
    rfl
  have hspan : Ideal.span {t} = (Ideal.span {genForm (k := k) a}).map (algebraMap B (K ⊗[k] A)) := by
    rw [Ideal.map_span, Set.image_singleton, ht0]
  refine ⟨?_, ?_⟩
  · rw [ht0]
    exact fun h => genForm_ne_zero (k := k) a hu (hinj (h.trans (map_zero _).symm))
  haveI hQ := isPrime_span_genForm (k := k) a hu
  by_cases hd : Disjoint (M : Set B) (Ideal.span {genForm (k := k) a} : Set B)
  · right
    refine ⟨?_, fun x hx => ?_⟩
    · rw [hspan]
      exact IsLocalization.isPrime_of_isPrime_disjoint M (K ⊗[k] A) _ hQ hd
    · have h1 : (1 : K) ⊗ₜ[k] x = algebraMap B (K ⊗[k] A) ((1 : P) ⊗ₜ[k] x) := by
        rw [hφ, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      rw [h1, hspan] at hx
      have h2 := IsLocalization.under_map_of_isPrime_disjoint M (K ⊗[k] A) hQ hd
      have h3 : (1 : P) ⊗ₜ[k] x ∈ ((Ideal.span {genForm (k := k) a}).map
          (algebraMap B (K ⊗[k] A))).under B := hx
      rw [h2] at h3
      exact eq_zero_of_one_tmul_mem a hu h3
  · left
    obtain ⟨m, hmM, hmQ⟩ := Set.not_disjoint_iff.1 hd
    rw [hspan]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hmQ)
      (IsLocalization.map_units (K ⊗[k] A) (⟨m, hmM⟩ : M))

end GlobalTheory.GenericForm
end
end

section

open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf

namespace GlobalTheory.OrbitUnfold

theorem finite_support_pairTerm :
    ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ),
      (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) →
      (∀ y : Y, (Function.support (F y)).Finite) →
      {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite →
      (Function.support (fun o : MulAction.orbitRel.Quotient Γ (Y × ConjSelf Γ) =>
        pairTerm F (Quotient.out o))).Finite := by
  intro Γ Y _ _ F hF hfin hS
  refine (hS.biUnion (t := fun o' =>
      (fun γ : Γ => (Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (Quotient.out o', of γ))) ''
        Function.support (F (Quotient.out o'))) (fun o' _ => (hfin _).image _)).subset ?_
  intro o ho
  have hne : F (Quotient.out o).1 (val (Quotient.out o).2) ≠ 0 := by
    intro h
    apply ho
    simp [pairTerm, h]
  set p := Quotient.out o with hp
  set o' : MulAction.orbitRel.Quotient Γ Y := Quotient.mk (MulAction.orbitRel Γ Y) p.1 with ho'
  obtain ⟨η, hη⟩ := Quotient.exact (Quotient.out_eq o')
  change η • p.1 = Quotient.out o' at hη
  have hval : F (Quotient.out o') (η * val p.2 * η⁻¹) ≠ 0 := by
    rw [← hη, hF]; exact hne
  refine Set.mem_biUnion (x := o') ⟨_, hval⟩ ⟨η * val p.2 * η⁻¹, hval, ?_⟩
  have hsm : (η • p : Y × ConjSelf Γ) = (Quotient.out o', of (η * val p.2 * η⁻¹)) := by
    rw [Prod.smul_def, hη]; rfl
  show Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (Quotient.out o', of (η * val p.2 * η⁻¹)) = o
  rw [← hsm]
  calc Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) (η • p)
      = Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) p :=
        Quotient.sound ⟨η, rfl⟩
    _ = o := by rw [hp]; exact Quotient.out_eq o

end GlobalTheory.OrbitUnfold
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem firstAndFinite_mono (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    {F G : Finset A} (h : F ⊆ G) : firstAndFinite R A k F ≤ firstAndFinite R A k G := by
  unfold firstAndFinite
  apply Algebra.adjoin_mono
  apply Set.union_subset_union_right
  apply Set.iUnion_mono
  intro i
  exact Set.image_mono (by exact_mod_cast h)

theorem tprod_eq_prod_singleAlgHom (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    (f : Fin (k + 1) → A) :
    PiTensorProduct.tprod R f = ∏ i, PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) i (f i) := by
  classical
  simp only [PiTensorProduct.singleAlgHom_apply]
  have := map_prod (PiTensorProduct.tprodMonoidHom R (A := fun _ : Fin (k + 1) => A))
    (fun u => MonoidHom.mulSingle (fun _ : Fin (k + 1) => A) u (f u)) Finset.univ
  refine Eq.trans ?_ this
  simp only [MonoidHom.mulSingle_apply]
  rw [Finset.univ_prod_mulSingle]
  rfl

theorem exists_finset_mem_firstAndFinite (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    (x : PiTensorProduct R (fun _ : Fin (k + 1) => A)) : ∃ F : Finset A, x ∈ firstAndFinite R A k F := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine ⟨Finset.univ.image f, ?_⟩
    refine Subalgebra.smul_mem _ ?_ r
    rw [tprod_eq_prod_singleAlgHom]
    refine Subalgebra.prod_mem _ fun i _ => ?_
    apply Algebra.subset_adjoin
    refine Or.inr (Set.mem_iUnion.2 ⟨i, f i, by simp, rfl⟩)
  | add x y hx hy =>
    obtain ⟨F, hF⟩ := hx
    obtain ⟨G, hG⟩ := hy
    exact ⟨F ∪ G, Subalgebra.add_mem _ (firstAndFinite_mono R A k Finset.subset_union_left hF)
      (firstAndFinite_mono R A k Finset.subset_union_right hG)⟩

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem firstAndFinite_fg_over_first : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A), ∃ F' : Finset (firstAndFinite R A k F), Algebra.adjoin R (Set.range (firstIncl R A k F) ∪ (F' : Set (firstAndFinite R A k F))) = ⊤ := by
  intro R A _ _ _ k F
  classical
  set S := firstAndFinite R A k F with hS
  let g : Fin (k + 1) × F → S := fun p =>
    ⟨PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) p.1 p.2.1,
      Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.2 ⟨p.1, p.2.1, p.2.2, rfl⟩))⟩
  refine ⟨Finset.univ.image g, ?_⟩
  apply Subalgebra.map_injective (f := S.val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  conv_rhs => rw [hS, firstAndFinite]
  congr 1
  rw [Set.image_union]
  congr 1
  · ext x
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
  · ext x
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_image, Set.mem_range,
      Set.mem_iUnion, Finset.mem_coe]
    constructor
    · rintro ⟨_, ⟨⟨i, a, ha⟩, rfl⟩, rfl⟩
      exact ⟨i, a, ha, rfl⟩
    · rintro ⟨i, a, ha, rfl⟩
      exact ⟨g (i, ⟨a, ha⟩), ⟨(i, ⟨a, ha⟩), rfl⟩, rfl⟩

end GlobalTheory.EtC
end

section

open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.trans_isLocalHom_injective (R : Type) [CommRing R] [IsLocalRing R] (i j : EtNbhd R)
    (h : i ≤ j) : IsLocalHom (EtNbhd.trans h) ∧ Function.Injective (EtNbhd.trans h) := by
  have hloc : IsLocalHom (EtNbhd.trans h) := by
    unfold EtNbhd.trans
    exact Localization.isLocalHom_localRingHom _ _ _ _
  refine ⟨hloc, ?_⟩
  set f : i.A →ₐ[R] j.A := h.choose with hfdef
  letI : Algebra i.A j.A := (f : i.A →+* j.A).toAlgebra
  haveI : IsScalarTower R i.A j.A := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  haveI : Algebra.Etale i.A j.A := Algebra.Etale.of_restrictScalars R i.A j.A
  have hflat : (f : i.A →+* j.A).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hB : (EtNbhd.trans h).Flat := RingHom.Flat.localRingHom hflat j.q i.q _
  letI : Algebra i.B j.B := (EtNbhd.trans h).toAlgebra
  haveI : Module.Flat i.B j.B := RingHom.flat_algebraMap_iff.mp hB
  haveI : IsLocalHom (algebraMap i.B j.B) := hloc
  haveI hff : Module.FaithfullyFlat i.B j.B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact RingHom.FaithfullyFlat.injective hff

end GlobalTheory.Henselisation
end

section

open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation.EtNbhd

instance isLocalHom_algebraMap_B {R : Type} [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    IsLocalHom (algebraMap R i.B) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hm : a ∈ maximalIdeal R := hna
  have hq : algebraMap R i.A a ∈ i.q := by
    show i.pt (algebraMap R i.A a) = 0
    rw [AlgHom.commutes]
    exact (residue_eq_zero_iff a).2 hm
  have : algebraMap R i.B a ∈ maximalIdeal i.B := by
    rw [IsScalarTower.algebraMap_apply R i.A i.B]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff i.B i.q _).2 hq
  exact this ha

theorem maximalIdeal_B_eq_map (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    maximalIdeal i.B = (maximalIdeal R).map (algebraMap R i.B) :=
  Algebra.FormallyUnramified.map_maximalIdeal.symm

end GlobalTheory.Henselisation.EtNbhd
end

section

open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.exists_sub_mem_maximalIdeal :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (b : i.B),
      ∃ r : R, b - algebraMap R i.B r ∈ maximalIdeal i.B := by
  intro R _ _ i b
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective i.q.primeCompl b
  obtain ⟨r₁, hr₁⟩ := residue_surjective (i.pt a)
  obtain ⟨r₂, hr₂⟩ := residue_surjective (i.pt (s : i.A))
  have hs : i.pt (s : i.A) ≠ 0 := by
    intro h
    exact s.2 (show (s : i.A) ∈ RingHom.ker i.pt from h)
  have hu : IsUnit r₂ := by
    by_contra hn
    apply hs
    rw [← hr₂]
    exact (residue_eq_zero_iff r₂).2 hn
  obtain ⟨u, rfl⟩ := hu
  refine ⟨r₁ * ((u⁻¹ : Rˣ) : R), ?_⟩
  have key : IsLocalization.mk' i.B a s - algebraMap R i.B (r₁ * ((u⁻¹ : Rˣ) : R)) =
      IsLocalization.mk' i.B (a - (s : i.A) * algebraMap R i.A (r₁ * ((u⁻¹ : Rˣ) : R))) s := by
    rw [IsLocalization.eq_mk'_iff_mul_eq, sub_mul, IsLocalization.mk'_spec,
      (algebraMap i.A i.B).map_sub, (algebraMap i.A i.B).map_mul,
      ← IsScalarTower.algebraMap_apply R i.A i.B]
    ring
  rw [key, IsLocalization.AtPrime.mk'_mem_maximal_iff (S := i.B) (I := i.q)]
  show _ ∈ RingHom.ker i.pt
  rw [RingHom.mem_ker, map_sub, map_mul, AlgHom.commutes, ← hr₁, ← hr₂]
  rw [show algebraMap R (ResidueField R) = residue R from rfl, ← map_mul, ← map_sub]
  rw [residue_eq_zero_iff]
  have : r₁ - (u : R) * (r₁ * ((u⁻¹ : Rˣ) : R)) = 0 := by
    rw [mul_left_comm, Units.mul_inv, mul_one, sub_self]
  rw [this]
  exact zero_mem _

end GlobalTheory.Henselisation
end

section

open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.base_le_all {R : Type} [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    EtNbhd.base ≤ i := by
  refine ⟨Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (R := R) (S₁ := i.A) Fin.elim0) ?_, ?_⟩
  · intro a ha
    have hcomp : (MvPolynomial.aeval (R := R) (S₁ := i.A) Fin.elim0) =
        (Algebra.ofId R i.A).comp (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toAlgHom :=
      MvPolynomial.algHom_ext fun x => x.elim0
    have ha' : (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toAlgHom a = 0 := ha
    exact (DFunLike.congr_fun hcomp a).trans ((congrArg (Algebra.ofId R i.A) ha').trans (map_zero _))
  · exact Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun x => x.elim0)

theorem Hens.of_algebraMap (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (r : R) :
    Hens.of i (algebraMap R i.B r) = algebraMap R (Hens R) r := by
  have h := EtNbhd.base_le_all i
  change Hens.of i (algebraMap R i.B r) = Hens.of EtNbhd.base (algebraMap R EtNbhd.base.B r)
  have e : Hens.of EtNbhd.base (algebraMap R EtNbhd.base.B r) =
      Hens.of i (EtNbhd.trans h (algebraMap R EtNbhd.base.B r)) :=
    (Ring.DirectLimit.of_f (G := fun i : EtNbhd R => i.B) (f := fun _ _ h => ⇑(EtNbhd.trans h)) h _).symm
  rw [e]
  congr 1
  rw [IsScalarTower.algebraMap_apply R (EtNbhd.base (R := R)).A (EtNbhd.base (R := R)).B r, EtNbhd.trans,
    Localization.localRingHom_to_map, RingHom.coe_coe, AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply R i.A i.B r]

end GlobalTheory.Henselisation
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.FerrandPush

theorem res_eq_app_comp {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]
    (U : Y₀.Opens) :
    res i U = i.app (upOpen i U) ≫
      Y₀.presheaf.map (eqToHom (preimage_upOpen i U).symm).op := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  rfl

theorem res_surjective_nilpotent_ker : ∀ {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i], (∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i.app U).hom)) → ∀ U : Y₀.Opens, IsAffineOpen (GlobalTheory.FerrandPush.upOpen i U) → Function.Surjective (GlobalTheory.FerrandPush.res i U).hom ∧ IsNilpotent (RingHom.ker (GlobalTheory.FerrandPush.res i U).hom) := by
  intro Y₀ Y₁ i _ _ hnil U hU
  have e := res_eq_app_comp i U
  set g := Y₀.presheaf.map (eqToHom (preimage_upOpen i U).symm).op with hg
  haveI : IsIso g := by rw [hg]; infer_instance
  have hgb : Function.Bijective g.hom :=
    ConcreteCategory.bijective_of_isIso g
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [CommRingCat.hom_comp]
    exact hgb.2.comp (i.app_surjective _ hU)
  · rw [CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hgb.1]
    exact hnil _ hU

end GlobalTheory.FerrandPush
end
