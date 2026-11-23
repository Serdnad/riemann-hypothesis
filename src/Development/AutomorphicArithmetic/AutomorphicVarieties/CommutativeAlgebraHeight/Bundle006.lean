module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem base_change_residue_surjective (O' R T : Type) [CommRing O'] [IsLocalRing O'] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [CommRing T] [Algebra O' T] [Algebra R T]
    [Module.Finite R T] (φ : T →+* ResidueField O') (hφ : ∀ a, φ (algebraMap O' T a) = residue O' a)
    (hm : ∀ r ∈ maximalIdeal R, φ (algebraMap R T r) = 0)
    (hs : ∀ x : T, ∃ a : O', x - algebraMap O' T a ∈ (maximalIdeal R).map (algebraMap R T)) :
    IsCO O' T := by
  have hJ : (maximalIdeal R).map (algebraMap R T) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.jacobson, Submodule.mem_sInf]
    rintro P ⟨-, hP⟩
    have h1 : Ideal.comap (algebraMap R T) P = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) P)
    rw [← Ideal.mem_comap, h1]
    exact hr
  haveI : Nontrivial T := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h2 := congrArg φ h
    rw [map_zero, map_one] at h2
    exact zero_ne_one h2
  have key : ∀ (u y : T), IsUnit u → y ∈ Ideal.jacobson (⊥ : Ideal T) → IsUnit (u + y) := by
    intro u y hu hy
    obtain ⟨v, rfl⟩ := hu
    have h3 := (Ideal.mem_jacobson_bot.mp hy) ↑v⁻¹
    have e : (v : T) + y = v * (y * ↑v⁻¹ + 1) := by
      rw [mul_add, mul_one, mul_comm y, ← mul_assoc, Units.mul_inv, one_mul, add_comm]
    rw [e]
    exact v.isUnit.mul h3
  haveI : IsLocalRing T := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
    obtain ⟨a, ha⟩ := hs x
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
    · left
      have h4 := key _ _ (h.map (algebraMap O' T)) (hJ ha)
      rwa [add_sub_cancel] at h4
    · right
      have h4 := key _ _ (h.map (algebraMap O' T)) (hJ (neg_mem ha))
      convert h4 using 1
      rw [map_sub, map_one]
      ring
  have hR : IsCL R R := by
    refine ⟨inferInstance, inferInstance, ?_, ?_⟩
    · rw [Algebra.algebraMap_self]
      infer_instance
    · infer_instance
  have hT : IsCL R T := cl_fin R R T hR
  haveI : IsNoetherianRing T := hT.noeth
  refine ⟨hT.complete, ?_, ?_⟩
  · refine ⟨fun a ha => ?_⟩
    have h5 := ha.map φ
    rw [hφ] at h5
    exact (IsLocalRing.residue_ne_zero_iff_isUnit a).mp h5.ne_zero
  · intro x
    obtain ⟨a, ha⟩ := hs x
    refine ⟨a, ?_⟩
    have h6 : (maximalIdeal R).map (algebraMap R T) ≤ maximalIdeal T := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h7 := hu.map φ
      rw [hm r hr] at h7
      exact not_isUnit_zero h7
    exact h6 ha

theorem UpperTheory.V.CA.cl_bc :
    ∀ (O O' R : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [Module.Finite O O'] [IsLocalHom (algebraMap O O')] [CommRing R] [Algebra O R] [IsCO O R], IsCO O' (TensorProduct O O' R) := by
  intro O O' R _ _ _ _ _ _ _ _ _ _
  letI : Algebra R (TensorProduct O O' R) := Algebra.TensorProduct.rightAlgebra
  have hR : ∀ r : R, algebraMap R (TensorProduct O O' R) r = 1 ⊗ₜ r := fun r => rfl
  have hL : ∀ x : O', algebraMap O' (TensorProduct O O' R) x = x ⊗ₜ 1 := fun x => rfl
  haveI : Module.Finite R (TensorProduct O O' R) := by
    let c := Algebra.TensorProduct.comm O R O'
    let e : TensorProduct O R O' →ₗ[R] TensorProduct O O' R :=
      { toFun := c
        map_add' := map_add c
        map_smul' := fun r y => by
          rw [Algebra.smul_def, Algebra.smul_def, map_mul]
          congr 1 }
    exact Module.Finite.of_surjective e c.surjective
  haveI : IsNoetherianRing R := inferInstance
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  let f : O' →ₐ[O] ResidueField O' := IsScalarTower.toAlgHom O O' (ResidueField O')
  let g : R →ₐ[O] ResidueField O' :=
    (IsScalarTower.toAlgHom O (ResidueField O) (ResidueField O')).comp (res O R)
  let φ : TensorProduct O O' R →+* ResidueField O' := (Algebra.TensorProduct.productMap f g).toRingHom
  refine base_change_residue_surjective O' R (TensorProduct O O' R) φ ?_ ?_ ?_
  · intro a
    simp [φ, f, g]
  · intro r hr
    have h1 : res O R r = 0 := (res_eq_zero_iff O R r).mpr hr
    show Algebra.TensorProduct.productMap f g (algebraMap R (TensorProduct O O' R) r) = 0
    rw [hR, Algebra.TensorProduct.productMap_apply_tmul]
    simp [g, h1]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul o r =>
      obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) r
      refine ⟨algebraMap O O' c * o, ?_⟩
      have e2 : o ⊗ₜ[O] r - algebraMap O' (TensorProduct O O' R) (algebraMap O O' c * o) =
          algebraMap O' (TensorProduct O O' R) o * algebraMap R (TensorProduct O O' R) (r - algebraMap O R c) := by
        rw [hR, hL, hL, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_sub,
          ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
      rw [e2]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hc)
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, ?_⟩
      have e3 : x + y - algebraMap O' (TensorProduct O O' R) (a + b) =
          (x - algebraMap O' (TensorProduct O O' R) a) + (y - algebraMap O' (TensorProduct O O' R) b) := by
        rw [map_add (f := _)]
        ring
      rw [e3]
      exact add_mem ha hb
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private lemma mem_pow_iff (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (x : AdicCompletion (maximalIdeal L) L) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n ↔
      AdicCompletion.eval (maximalIdeal L) L n x = 0 := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem L,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal L).fg_of_isNoetherianRing]
  rfl

private lemma strict_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (a : L) (h : algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n) : a ∈ maximalIdeal L ^ n := by
  rw [mem_pow_iff, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h
  have h' : Submodule.Quotient.mk (p := (maximalIdeal L ^ n • ⊤ : Submodule L L)) a = 0 := by
    simpa [AdicCompletion.eval] using h
  rw [Submodule.Quotient.mk_eq_zero] at h'
  simpa using h'

private lemma dense_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (b : AdicCompletion (maximalIdeal L) L) :
    ∃ a : L, b - algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal L) L n b)
  refine ⟨a, ?_⟩
  rw [mem_pow_iff, map_sub, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, sub_eq_zero, ← ha]
  simp [AdicCompletion.eval]

theorem UpperTheory.V.CA.cpl_is :
    ∀ (C : Type) [CommRing C] [IsNoetherianRing C] (x : Ideal C) [x.IsMaximal], ∃ _ : IsLocalRing (Cpl x), IsCplAt x (Cpl x) := by
  intro C _ _ x hx
  refine ⟨inferInstance, ?_⟩
  have hL : ∀ (n : ℕ) (a : Localization.AtPrime x),
      a ∈ maximalIdeal (Localization.AtPrime x) ^ n →
      algebraMap (Localization.AtPrime x) (Cpl x) a ∈ maximalIdeal (Cpl x) ^ n := by
    intro n a ha
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  refine
    { noeth := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
      complete := inferInstance
      comap_pow := fun n => ?_
      dense := fun n r => ?_ }
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [IsScalarTower.algebraMap_eq C (Localization.AtPrime x) (Cpl x), ← Ideal.comap_comap]
    have e : Ideal.comap (algebraMap (Localization.AtPrime x) (Cpl x)) (maximalIdeal (Cpl x) ^ n) =
        maximalIdeal (Localization.AtPrime x) ^ n := by
      ext a
      exact ⟨strict_loc _ n a, hL n a⟩
    rw [e, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    refine IsLocalization.under_map_of_isPrimary_disjoint x.primeCompl (Localization.AtPrime x) ?_ ?_
    · apply Ideal.isPrimary_of_isMaximal_radical
      rw [Ideal.radical_pow _ hn.ne', (inferInstance : x.IsPrime).radical]
      infer_instance
    · exact Set.disjoint_left.mpr fun s hs hs' => hs (Ideal.pow_le_self hn.ne' hs')
  · obtain ⟨a, ha⟩ := dense_loc _ n r
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective x.primeCompl a
    have hsx : Ideal.span {(s : C)} ⊔ x = ⊤ := by
      rw [sup_comm]
      have hm : (s : C) ∈ x ⊔ Ideal.span {(s : C)} :=
        Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
      refine hx.out.2 _ (lt_of_le_of_ne le_sup_left fun e => s.2 ?_)
      rwa [← e] at hm
    have h1 : (1 : C) ∈ Ideal.span {(s : C)} ⊔ x ^ n := by
      rw [Ideal.sup_pow_eq_top hsx]
      trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    refine ⟨c * t, ?_⟩
    have key : IsLocalization.mk' (Localization.AtPrime x) c s - algebraMap C _ (c * t) =
        IsLocalization.mk' (Localization.AtPrime x) c s * algebraMap C _ z := by
      have hs := IsLocalization.mk'_spec (Localization.AtPrime x) c s
      have hz' : z = 1 - t * s := by
        rw [← hyz]
        ring
      rw [hz', map_sub, map_one, map_mul, map_mul, ← hs]
      ring
    have hmem : IsLocalization.mk' (Localization.AtPrime x) c s - algebraMap C _ (c * t) ∈
        maximalIdeal (Localization.AtPrime x) ^ n := by
      rw [key, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hz)
    have hsum := Ideal.add_mem _ ha (hL n _ hmem)
    rw [map_sub, ← IsScalarTower.algebraMap_apply C (Localization.AtPrime x) (Cpl x)] at hsum
    convert hsum using 1
    ring
end

section

noncomputable section

open IsLocalRing TensorProduct Polynomial UpperTheory.V.W UpperTheory.V.Alg

namespace UpperTheory.V.CA

def Z1 {G k : Type} [Group G] [TopologicalSpace G] [Field k] (χ ψ : G →* kˣ) : Submodule k (G → k) where
  carrier := {a | IsLocallyConstant a ∧ ∀ g h, a (g * h) = χ g * a h + a g * ψ h}
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun g h => by simp only [Pi.add_apply, ha.2, hb.2]; ring⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun g h => by simp⟩
  smul_mem' c a ha := ⟨ha.1.comp fun x => c * x, fun g h => by simp only [Pi.smul_apply, smul_eq_mul, ha.2]; ring⟩

structure MultFree {n : ℕ} {G k : Type} [Group G] [TopologicalSpace G] [Field k] (χ : Fin n → G →* kˣ) (h : ℕ) :
    Prop where
  isOpen : ∀ i, IsOpen ((χ i).ker : Set G)
  inj : Function.Injective χ
  fin : ∀ i j, i ≠ j → Module.Finite k (Z1 (χ i) (χ j)) ∧ Module.finrank k (Z1 (χ i) (χ j)) ≤ h

def finBound (n h : ℕ) : ℕ := n + ∑ p ∈ Finset.range n, (n ^ 2 * h) ^ p

structure IsGMA {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : Fin n → E) : Prop where
  ch : D.IsCH
  idem : CompleteOrthogonalIdempotents e
  rank : ∀ i, D.D A[X] (1 + X ⊗ₜ e i) = 1 + X

structure IsDef (O : Type) [CommRing O] [IsLocalRing O] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    (Dbar : GDet n (ResidueField O) G) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (D : GDet n R G) : Prop where
  cont : D.IsCont (maximalIdeal R)
  red : D.map (res O R : R →+* ResidueField O) = Dbar

structure IsUnivDet (O : Type) [CommRing O] [IsLocalRing O] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    (Dbar : GDet n (ResidueField O) G) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (D : GDet n R G) : Prop where
  isDef : IsDef O Dbar D
  univ : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (D' : GDet n R' G), IsDef O Dbar D' →
    ∃! f : R →ₐ[O] R', D.map (f : R →+* R') = D'

end UpperTheory.V.CA
end
end

section

open IsLocalRing

theorem UpperTheory.V.CA.g_dimcpl :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
      ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R := by
  intro R _ _ _
  haveI := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion R (maximalIdeal R)
  have hm := AdicCompletion.maximalIdeal_eq_map (R := R)
  haveI : (maximalIdeal (AdicCompletion (maximalIdeal R) R)).LiesOver (maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal.isMaximal R).eq_of_le Ideal.IsPrime.ne_top'
      (Ideal.map_le_iff_le_comap.mp hm.ge)⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R)
    (maximalIdeal (AdicCompletion (maximalIdeal R) R))
  rw [← hm, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h]
end
