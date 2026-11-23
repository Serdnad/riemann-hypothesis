module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
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
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

@[expose] public section

section

open TensorProduct

namespace GlobalTheory

theorem ker_counitAlgHom_baseChange_field (O B κ : Type) [CommRing O] [CommRing B] [Bialgebra O B]
    [Field κ] [Algebra O κ] :
    RingHom.ker (Bialgebra.counitAlgHom κ (κ ⊗[O] B)) =
      Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[O] κ ⊗[O] B)
        (RingHom.ker (Bialgebra.counitAlgHom O B)) := by
  have hs : Function.Surjective (Bialgebra.counitAlgHom O B) := fun c =>
    ⟨algebraMap O B c, by simp⟩
  rw [← Algebra.TensorProduct.lTensor_ker _ hs]
  have key : ∀ x : κ ⊗[O] B, Bialgebra.counitAlgHom κ (κ ⊗[O] B) x =
      Algebra.TensorProduct.rid O κ κ
        (Algebra.TensorProduct.map (AlgHom.id O κ) (Bialgebra.counitAlgHom O B) x) := by
    intro x
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul c b => simp [TensorProduct.counit_tmul]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, key, map_eq_zero_iff _ (AlgEquiv.injective _)]

theorem hopf_order_formula_fibre :
    (∀ (k A B : Type) [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A), Module.finrank k A = Module.finrank k (A ⧸ Ideal.map (f : B →ₐ[k] A) (RingHom.ker (Bialgebra.counitAlgHom k B))) * Module.finrank k (LinearMap.range (f : B →ₐ[k] A).toLinearMap)) → ∀ (O A B κ : Type) [CommRing O] [CommRing A] [CommRing B] [HopfAlgebra O A] [HopfAlgebra O B] [Module.Finite O A] [Field κ] [Algebra O κ] (f : B →ₐc[O] A), Module.finrank κ (TensorProduct O κ A) = Module.finrank κ (TensorProduct O κ (A ⧸ Ideal.map (f : B →ₐ[O] A) (RingHom.ker (Bialgebra.counitAlgHom O B)))) * Module.finrank κ (LinearMap.range ((f : B →ₐ[O] A).toLinearMap.baseChange κ)) := by
  intro H O A B κ _ _ _ _ _ _ _ _ f
  have h := H κ (κ ⊗[O] A) (κ ⊗[O] B) (Bialgebra.TensorProduct.map (BialgHom.id κ κ) f)
  have hI : Ideal.map ((Bialgebra.TensorProduct.map (BialgHom.id κ κ) f :
        κ ⊗[O] B →ₐc[κ] κ ⊗[O] A) : κ ⊗[O] B →ₐ[κ] κ ⊗[O] A)
        (RingHom.ker (Bialgebra.counitAlgHom κ (κ ⊗[O] B))) =
      Ideal.map (Algebra.TensorProduct.includeRight : A →ₐ[O] κ ⊗[O] A)
        (Ideal.map (f : B →ₐ[O] A) (RingHom.ker (Bialgebra.counitAlgHom O B))) := by
    rw [ker_counitAlgHom_baseChange_field]
    refine (Ideal.map_map
      ((Algebra.TensorProduct.includeRight : B →ₐ[O] κ ⊗[O] B) : B →+* κ ⊗[O] B)
      ((((Bialgebra.TensorProduct.map (BialgHom.id κ κ) f :
        κ ⊗[O] B →ₐc[κ] κ ⊗[O] A) : κ ⊗[O] B →ₐ[κ] κ ⊗[O] A)) : κ ⊗[O] B →+* κ ⊗[O] A)).trans ?_
    refine Eq.trans ?_ (Ideal.map_map ((f : B →ₐ[O] A) : B →+* A)
      ((Algebra.TensorProduct.includeRight : A →ₐ[O] κ ⊗[O] A) : A →+* κ ⊗[O] A)).symm
    congr 1
  have hL : ((Bialgebra.TensorProduct.map (BialgHom.id κ κ) f :
        κ ⊗[O] B →ₐc[κ] κ ⊗[O] A) : κ ⊗[O] B →ₐ[κ] κ ⊗[O] A).toLinearMap =
      (f : B →ₐ[O] A).toLinearMap.baseChange κ := by
    ext b
    simp
  rw [hI, hL] at h
  rw [h, (Algebra.TensorProduct.tensorQuotientEquiv (R := O) κ A κ
    (Ideal.map (f : B →ₐ[O] A) (RingHom.ker (Bialgebra.counitAlgHom O B)))).toLinearEquiv.finrank_eq]

end GlobalTheory
end

section

open Filter Topology

namespace GlobalTheory

theorem finrank_le_card_values : ∀ (C V Γ : Type) [Field C] [AddCommGroup V] [Module C V] [LinearOrder Γ] (ν : V → Γ), (∀ (c : C) (u : V), c ≠ 0 → ν (c • u) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u < ν v → u + v ≠ 0 ∧ ν (u + v) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u = ν v → ∃ c : C, u - c • v = 0 ∨ ν u < ν (u - c • v)) → ∀ (F : Submodule C V) [Module.Finite C F], ∃ f : Fin (Module.finrank C F) → V, (∀ i, f i ∈ F ∧ f i ≠ 0) ∧ Function.Injective (fun i => ν (f i)) := by
  intro C V Γ _ _ _ _ ν _h1 _h2 h3 F _
  classical
  set S : Set Γ := ν '' {u | u ∈ F ∧ u ≠ 0} with hS
  have hg : ∀ s ∈ S, ∃ u, (u ∈ F ∧ u ≠ 0) ∧ ν u = s := fun s hs => hs
  choose! g hgF hgν using hg
  suffices hcard : ∃ e : Fin (Module.finrank C F) → Γ, Function.Injective e ∧ ∀ i, e i ∈ S by
    obtain ⟨e, he, heS⟩ := hcard
    refine ⟨fun i => g (e i), fun i => hgF _ (heS i), ?_⟩
    intro i j hij
    simp only at hij
    rw [hgν _ (heS i), hgν _ (heS j)] at hij
    exact he hij
  by_cases hfin : S.Finite
  · have key : ∀ n : ℕ, ∀ u, u ∈ F → u ≠ 0 →
        (hfin.toFinset.filter (fun s => ν u < s)).card = n →
        u ∈ Submodule.span C (g '' S) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
      intro u huF hu0 hn
      have huS : ν u ∈ S := ⟨u, ⟨huF, hu0⟩, rfl⟩
      obtain ⟨hgF', hg0⟩ := hgF _ huS
      obtain ⟨c, hc⟩ := h3 u (g (ν u)) hu0 hg0 (hgν _ huS).symm
      have hgmem : g (ν u) ∈ Submodule.span C (g '' S) := Submodule.subset_span ⟨ν u, huS, rfl⟩
      have hdec : u = (u - c • g (ν u)) + c • g (ν u) := (sub_add_cancel _ _).symm
      rw [hdec]
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hgmem)
      rcases hc with hc | hc
      · rw [hc]; exact Submodule.zero_mem _
      · by_cases hw0 : u - c • g (ν u) = 0
        · rw [hw0]; exact Submodule.zero_mem _
        · have hwF : u - c • g (ν u) ∈ F := F.sub_mem huF (F.smul_mem c hgF')
          refine ih _ ?_ _ hwF hw0 rfl
          rw [← hn]
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨ν (u - c • g (ν u)), ?_, ?_⟩
            · rw [Finset.mem_filter, Set.Finite.mem_toFinset]
              exact ⟨⟨_, ⟨hwF, hw0⟩, rfl⟩, hc⟩
            · rw [Finset.mem_filter]
              exact fun h => lt_irrefl _ h.2
          · intro s hs
            rw [Finset.mem_filter] at hs ⊢
            exact ⟨hs.1, lt_trans hc hs.2⟩
    have hle : F ≤ Submodule.span C (g '' S) := by
      intro u huF
      by_cases hu0 : u = 0
      · rw [hu0]; exact Submodule.zero_mem _
      · exact key _ u huF hu0 rfl
    have himg : g '' S = ((hfin.toFinset.image g : Finset V) : Set V) := by
      ext x; simp
    have hdim : Module.finrank C F ≤ hfin.toFinset.card := by
      rw [himg] at hle
      calc Module.finrank C F ≤ Module.finrank C (Submodule.span C ((hfin.toFinset.image g : Finset V) : Set V)) :=
            Submodule.finrank_mono hle
        _ ≤ (hfin.toFinset.image g).card := finrank_span_finset_le_card _
        _ ≤ hfin.toFinset.card := Finset.card_image_le
    let emb : Fin (Module.finrank C F) ↪ hfin.toFinset :=
      (Fin.castLEEmb hdim).trans hfin.toFinset.equivFin.symm.toEmbedding
    refine ⟨fun i => (emb i : Γ), ?_, ?_⟩
    · intro i j hij
      exact emb.injective (Subtype.ext hij)
    · intro i
      exact (Set.Finite.mem_toFinset hfin).1 (emb i).2
  · let emb : ℕ ↪ S := Set.Infinite.natEmbedding S hfin
    refine ⟨fun i => (emb i : Γ), ?_, fun i => (emb i).2⟩
    intro i j hij
    exact Fin.ext (emb.injective (Subtype.ext hij))

end GlobalTheory
end

section

namespace GlobalTheory

open TensorProduct


open TensorProduct in
open TensorProduct in
theorem _root_.GlobalTheory.subsingleton_of_residueField_fibres (O Q : Type) [CommRing O]
    [AddCommGroup Q] [Module O Q] [Module.Finite O Q]
    (h : ∀ q : PrimeSpectrum O, Subsingleton (q.asIdeal.ResidueField ⊗[O] Q)) :
    Subsingleton Q := by
  rw [← Module.support_eq_empty_iff (R := O), Set.eq_empty_iff_forall_notMem]
  intro q hq
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hq
  exact not_nontrivial_iff_subsingleton.mpr (h q) hq

open TensorProduct in
open TensorProduct in
theorem _root_.GlobalTheory.surjective_of_fibre_rank (O M N : Type) [CommRing O] [AddCommGroup M]
    [Module O M] [AddCommGroup N] [Module O N] [Module.Finite O N] (f : M →ₗ[O] N)
    (h : ∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField
      (LinearMap.range (f.baseChange q.asIdeal.ResidueField)) =
      Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
  refine _root_.GlobalTheory.subsingleton_of_residueField_fibres O _ fun q => ?_
  have htop : LinearMap.range (f.baseChange q.asIdeal.ResidueField) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (h q)
  have hex := lTensor_exact q.asIdeal.ResidueField (LinearMap.exact_map_mkQ_range f)
    (Submodule.mkQ_surjective _)
  refine ⟨fun y y' => ?_⟩
  suffices ∀ y : q.asIdeal.ResidueField ⊗[O] (N ⧸ LinearMap.range f), y = 0 by
    rw [this y, this y']
  intro y
  obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective q.asIdeal.ResidueField
    (Submodule.mkQ_surjective (LinearMap.range f)) y
  have hx : x ∈ LinearMap.range (f.baseChange q.asIdeal.ResidueField) := htop ▸ Submodule.mem_top
  obtain ⟨z, rfl⟩ := hx
  rw [LinearMap.baseChange_eq_ltensor]
  exact hex.apply_apply_eq_zero z

theorem injective_of_fibre_rank (O M N : Type) [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] [Module.Finite O N] (f : M →ₗ[O] N)
    [Module.Finite O M] [Module.Projective O N] (hf : Function.Surjective f)
    (h : ∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField
      (TensorProduct O q.asIdeal.ResidueField M) =
      Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) :
    Function.Injective f := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf

  have hsurj : Function.Surjective s := by
    apply surjective_of_fibre_rank O N M s
    intro q
    have hinj : Function.Injective (s.baseChange q.asIdeal.ResidueField) := by
      apply Function.LeftInverse.injective (g := f.baseChange q.asIdeal.ResidueField)
      intro x
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hs]
      simp
    rw [LinearMap.finrank_range_of_inj hinj, h q]
  intro a b hab
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  have hx : f (s x) = x := LinearMap.congr_fun hs x
  have hy : f (s y) = y := LinearMap.congr_fun hs y
  rw [hx, hy] at hab
  rw [hab]

theorem surjective_injective_of_fibre_rank :
    ∀ (O M N : Type) [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] [Module.Finite O N] (f : M →ₗ[O] N), ((∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField (LinearMap.range (f.baseChange q.asIdeal.ResidueField)) = Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) → Function.Surjective f) ∧ (Module.Finite O M → Module.Projective O N → Function.Surjective f → (∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField M) = Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) → Function.Injective f) := by
  intro O M N _ _ _ _ _ _ f
  exact ⟨surjective_of_fibre_rank O M N f,
    fun _ _ hf h => injective_of_fibre_rank O M N f hf h⟩

end GlobalTheory
end

section

open scoped TensorProduct
universe u

namespace GlobalTheory

theorem weightSpace_iff_idempotent_fixed : ∀ (k : Type) [Field k] (C : Type) [CommRing C] (M : Type u) [AddCommGroup M] [Module k M] [Module (k ⊗[ℤ] C) M] [IsScalarTower k (k ⊗[ℤ] C) M] [FiniteDimensional k M] (χ : C →+* k) (e : k ⊗[ℤ] C), IsIdempotentElem e → (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) e = 1 → (∀ a, (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) a = 0 → IsNilpotent (e * a)) → ∀ m : M, m ∈ (⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c)) ↔ e • m = m := by
  intro k _ C _ M _ _ _ _ _ χ e he he1 hnil m
  set φ : k ⊗[ℤ] C →ₐ[k] k := Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) with hφ
  have hφt : ∀ (x : k) (c : C), φ (x ⊗ₜ[ℤ] c) = x * χ c := by
    intro x c
    simp [hφ]
  let ρ : k ⊗[ℤ] C →ₐ[k] Module.End k M := Algebra.lsmul k k M
  let T : C → k ⊗[ℤ] C := fun c => (1 : k) ⊗ₜ[ℤ] c - algebraMap k (k ⊗[ℤ] C) (χ c)
  have hφT : ∀ c, φ (T c) = 0 := by
    intro c
    simp [T, hφt, AlgHom.commutes]
  have hρT : ∀ c, ρ (T c) = DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c) - χ c • (1 : Module.End k M) := by
    intro c
    simp only [T]
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    rfl
  constructor
  · intro hm
    set X := ⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c) with hX
    have hstab : ∀ (a : k ⊗[ℤ] C) (x : M), x ∈ X → a • x ∈ X := by
      intro a x hx
      rw [hX, Submodule.mem_iInf] at hx ⊢
      intro c
      have hc : Commute (ρ ((1 : k) ⊗ₜ[ℤ] c)) (ρ a) := (Commute.all _ _).map ρ
      exact Module.End.mapsTo_maxGenEigenspace_of_comm hc (χ c) (hx c)
    let X' : Submodule (k ⊗[ℤ] C) M :=
      { carrier := X
        add_mem' := fun ha hb => X.add_mem ha hb
        zero_mem' := X.zero_mem
        smul_mem' := fun a x hx => hstab a x hx }
    let ρX : k ⊗[ℤ] C →ₐ[k] Module.End k X' := Algebra.lsmul k k X'
    have hT : ∀ c, IsNilpotent (ρX (T c)) := by
      intro c
      refine ⟨Module.End.maxGenEigenspaceIndex (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c), ?_⟩
      ext ⟨x, hx⟩
      have hx' : x ∈ Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c) :=
        (Submodule.mem_iInf _).1 hx c
      rw [Module.End.maxGenEigenspace_eq, Module.End.mem_genEigenspace_nat] at hx'
      rw [← hρT, ← map_pow] at hx'
      rw [LinearMap.mem_ker] at hx'
      rw [← map_pow, LinearMap.zero_apply]
      exact hx'
    have hall : ∀ a, IsNilpotent (ρX (a - algebraMap k (k ⊗[ℤ] C) (φ a))) := by
      intro a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul x c =>
        have : x ⊗ₜ[ℤ] c - algebraMap k (k ⊗[ℤ] C) (φ (x ⊗ₜ[ℤ] c)) = x • T c := by
          simp only [T, hφt, smul_sub, Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
            Algebra.TensorProduct.tmul_mul_tmul]
          rw [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
          simp
        rw [this, map_smul]
        exact (hT c).smul x
      | add a b ha hb =>
        have : a + b - algebraMap k (k ⊗[ℤ] C) (φ (a + b)) =
            (a - algebraMap k (k ⊗[ℤ] C) (φ a)) + (b - algebraMap k (k ⊗[ℤ] C) (φ b)) := by
          rw [map_add (f := _), map_add (f := _)]; abel
        rw [this, map_add (f := _)]
        exact Commute.isNilpotent_add ((Commute.all _ _).map ρX) ha hb
    have h1e : IsNilpotent (ρX (1 - e)) := by
      have := hall (1 - e)
      rwa [show φ (1 - e) = 0 by rw [map_sub, map_one, he1, sub_self], map_zero, sub_zero] at this
    have hid : IsIdempotentElem (ρX (1 - e)) := he.one_sub.map ρX
    have h0 := hid.eq_zero_of_isNilpotent h1e
    have := congrArg (fun f => (f ⟨m, hm⟩ : X')) h0
    simp only [LinearMap.zero_apply] at this
    have := congrArg Subtype.val this
    change (1 - e) • m = 0 at this
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  · intro hm
    rw [Submodule.mem_iInf]
    intro c
    rw [Module.End.mem_maxGenEigenspace]
    obtain ⟨n, hn⟩ := hnil (T c) (hφT c)
    refine ⟨n, ?_⟩
    have hen : ∀ j : ℕ, e ^ j • m = m := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, mul_smul, hm, ih]
    rw [← hρT, ← map_pow]
    change T c ^ n • m = 0
    rw [← hen n, smul_smul, mul_comm, ← mul_pow, hn, zero_smul]

end GlobalTheory
end

section

namespace GlobalTheory.MultiplierOrders

theorem exists_nsmul_mem_span {C : Type} [AddCommGroup C] [Module ℚ C] (S : Set C) (x : C)
    (hx : x ∈ Submodule.span ℚ S) : ∃ m : ℕ, 0 < m ∧ m • x ∈ Submodule.span ℤ S := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by rw [one_smul]; exact Submodule.subset_span hy⟩
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm, hy⟩ := hy
    obtain ⟨n, hn, hz⟩ := hz
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]
      exact nsmul_mem hy n
    · rw [mul_smul]
      exact nsmul_mem hz m
  | smul q y _ hy =>
    obtain ⟨m, hm, hy⟩ := hy
    refine ⟨m * q.den, Nat.mul_pos hm q.den_pos, ?_⟩
    have h : (m * q.den) • q • y = q.num • m • y := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ m, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, smul_smul]
      congr 1
      push_cast
      rw [mul_assoc, Rat.den_mul_eq_num, mul_comm]
    rw [h]
    exact Submodule.smul_mem _ _ hy

def multipliers {C : Type} [Ring C] (L : Submodule ℤ C) : Subring C where
  carrier := {x | ∀ y ∈ L, x * y ∈ L}
  mul_mem' := fun {a b} ha hb y hy => by
    rw [mul_assoc]; exact ha _ (hb y hy)
  one_mem' := fun y hy => by rw [one_mul]; exact hy
  add_mem' := fun {a b} ha hb y hy => by
    rw [add_mul]; exact L.add_mem (ha y hy) (hb y hy)
  zero_mem' := fun y _ => by rw [zero_mul]; exact L.zero_mem
  neg_mem' := fun {a} ha y hy => by
    rw [neg_mul]; exact L.neg_mem (ha y hy)

theorem exists_order (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] :
    ∃ OB : Subring C, Module.Finite ℤ OB ∧ ∀ b : C, ∃ m : ℕ, 0 < m ∧ (m : C) * b ∈ OB := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℚ) (M := C)
  have key : ∀ x : C, ∃ m : ℕ, 0 < m ∧ m • x ∈ Submodule.span ℤ (S : Set C) := fun x =>
    exists_nsmul_mem_span _ x (by rw [hS]; exact Submodule.mem_top)
  set L : Submodule ℤ C := Submodule.span ℤ (S : Set C) with hL
  haveI : Module.Finite ℤ L := Module.Finite.iff_fg.mpr ⟨S, rfl⟩
  refine ⟨multipliers L, ?_, ?_⟩
  · obtain ⟨m, hm, h1⟩ := key 1
    let f : multipliers L →+ L :=
      { toFun := fun x => ⟨x.1 * (m • (1 : C)), x.2 _ h1⟩
        map_zero' := Subtype.ext (by simp)
        map_add' := fun a b => Subtype.ext (by simp [add_mul]) }
    refine Module.Finite.of_injective f.toIntLinearMap ?_
    intro a b hab
    have h : a.1 * (m • (1 : C)) = b.1 * (m • (1 : C)) := congrArg Subtype.val hab
    rw [mul_smul_comm, mul_smul_comm, mul_one, mul_one, ← Nat.cast_smul_eq_nsmul ℚ,
      ← Nat.cast_smul_eq_nsmul ℚ] at h
    have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    exact Subtype.ext (smul_right_injective C hm' h)
  · intro b
    choose n hn hmem using fun s : C => key (b * s)
    refine ⟨∏ s ∈ S, n s, Finset.prod_pos fun s _ => hn s, ?_⟩
    intro y hy
    induction hy using Submodule.span_induction with
    | mem s hs =>
      have hs' : s ∈ S := hs
      rw [mul_assoc, ← nsmul_eq_mul, ← Finset.prod_erase_mul S n hs', mul_smul]
      exact nsmul_mem (hmem s) _
    | zero => rw [mul_zero]; exact L.zero_mem
    | add y z _ _ hy hz => rw [mul_add]; exact L.add_mem hy hz
    | smul k y _ hy => rw [mul_smul_comm]; exact L.smul_mem k hy

end GlobalTheory.MultiplierOrders
end

section

namespace GlobalTheory.IntertwiningOperators

open Polynomial

theorem intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C)
    (p : K[X]) : aeval B p * C = C * aeval A p := by
  induction p using Polynomial.induction_on with
  | C c =>
    simp only [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial n c ih =>
    rw [pow_succ, ← mul_assoc, map_mul (aeval B) (Polynomial.C c * X ^ n) X,
      map_mul (aeval A) (Polynomial.C c * X ^ n) X, aeval_X, aeval_X, Matrix.mul_assoc, ← h,
      ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

theorem main : ∀ {K : Type} [inst : Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K),
    IsCoprime (Matrix.charpoly A) (Matrix.charpoly B) → C * A = B * C →
      C = (0 : Matrix (Fin b) (Fin a) K) := by
  intro K _ a b A B C hcop h
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : aeval B u * aeval B (Matrix.charpoly A) = 1 := by
    have := congrArg (aeval B) huv
    rw [map_add (f := _), map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero, map_one] at this
    exact this
  have h2 : aeval B (Matrix.charpoly A) * C = 0 := by
    rw [intertwine A B C h, Matrix.aeval_self_charpoly, Matrix.mul_zero]
  calc C = (aeval B u * aeval B (Matrix.charpoly A)) * C := by rw [h1, Matrix.one_mul]
    _ = 0 := by rw [Matrix.mul_assoc, h2, Matrix.mul_zero]

end GlobalTheory.IntertwiningOperators
end
