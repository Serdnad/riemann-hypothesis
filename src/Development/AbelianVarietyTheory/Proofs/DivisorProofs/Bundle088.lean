module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Localization.Module

@[expose] public section

section

open IsLocalRing



namespace GlobalTheory

open Polynomial TensorProduct

namespace KummerRootTensor

variable {E : Type} [CommRing E] (B : Type) [CommRing B] [Algebra E B]

theorem aeval_root_map (Q : E[X]) :
    Polynomial.aeval (AdjoinRoot.root (Q.map (algebraMap E B))) Q = 0 := by
  rw [← Polynomial.aeval_map_algebraMap B, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

theorem aeval_one_tmul_root (Q : E[X]) :
    Polynomial.aeval ((1 : B) ⊗ₜ[E] AdjoinRoot.root Q) (Q.map (algebraMap E B)) = 0 := by
  have h : (1 : B) ⊗ₜ[E] AdjoinRoot.root Q =
      (Algebra.TensorProduct.includeRight : AdjoinRoot Q →ₐ[E] B ⊗[E] AdjoinRoot Q)
        (AdjoinRoot.root Q) := rfl
  rw [Polynomial.aeval_map_algebraMap, h, Polynomial.aeval_algHom_apply, AdjoinRoot.aeval_eq,
    AdjoinRoot.mk_self, map_zero]

noncomputable def toMap (Q : E[X]) : AdjoinRoot Q →ₐ[E] AdjoinRoot (Q.map (algebraMap E B)) :=
  AdjoinRoot.liftAlgHom Q (Algebra.ofId E _) (AdjoinRoot.root (Q.map (algebraMap E B)))
    (aeval_root_map B Q)

noncomputable def fromMap (Q : E[X]) :
    AdjoinRoot (Q.map (algebraMap E B)) →ₐ[B] B ⊗[E] AdjoinRoot Q :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId B _) ((1 : B) ⊗ₜ[E] AdjoinRoot.root Q)
    (aeval_one_tmul_root B Q)

theorem toMap_root (Q : E[X]) :
    toMap B Q (AdjoinRoot.root Q) = AdjoinRoot.root (Q.map (algebraMap E B)) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem fromMap_root (Q : E[X]) :
    fromMap B Q (AdjoinRoot.root (Q.map (algebraMap E B))) = (1 : B) ⊗ₜ[E] AdjoinRoot.root Q :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

noncomputable def toTensorMap (Q : E[X]) :
    B ⊗[E] AdjoinRoot Q →ₐ[B] AdjoinRoot (Q.map (algebraMap E B)) :=
  Algebra.TensorProduct.lift (Algebra.ofId B _) (toMap B Q) (fun _ _ => Commute.all _ _)

theorem toTensorMap_one_tmul_root (Q : E[X]) :
    toTensorMap B Q ((1 : B) ⊗ₜ[E] AdjoinRoot.root Q) = AdjoinRoot.root (Q.map (algebraMap E B)) := by
  rw [toTensorMap, Algebra.TensorProduct.lift_tmul, map_one, one_mul, toMap_root]

noncomputable def tensorEquiv (Q : E[X]) :
    B ⊗[E] AdjoinRoot Q ≃ₐ[B] AdjoinRoot (Q.map (algebraMap E B)) :=
  AlgEquiv.ofAlgHom (toTensorMap B Q) (fromMap B Q)
    (by
      apply AdjoinRoot.algHom_ext
      show toTensorMap B Q (fromMap B Q (AdjoinRoot.root _)) = _
      rw [fromMap_root, toTensorMap_one_tmul_root]; rfl)
    (by
      apply Algebra.TensorProduct.ext
      · exact Subsingleton.elim _ _
      · apply AdjoinRoot.algHom_ext
        show fromMap B Q (toTensorMap B Q ((1 : B) ⊗ₜ[E] AdjoinRoot.root Q)) = _
        rw [toTensorMap_one_tmul_root, fromMap_root]; rfl)

end KummerRootTensor

theorem kummer_uniformiser_tensor_isReduced : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    IsReduced (TensorProduct S D L) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ hφ hπ he
  obtain ⟨φ⟩ := hφ
  set f : S[X] := X ^ e - C π with hf
  have hinj : Function.Injective (algebraMap S L) := by
    rw [IsScalarTower.algebraMap_eq S K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective S K)
  have hπ' : algebraMap S L π ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  have he' : (e : L) ≠ 0 := by
    have := he.map (algebraMap S L)
    rw [map_natCast] at this
    exact this.ne_zero
  have hmap : f.map (algebraMap S L) = X ^ e - C (algebraMap S L π) := by
    simp [hf, Polynomial.map_sub, Polynomial.map_pow]
  have hsep : (f.map (algebraMap S L)).Separable := by
    rw [hmap]; exact separable_X_pow_sub_C _ he' hπ'
  have hred : IsReduced (AdjoinRoot (f.map (algebraMap S L))) :=
    (Ideal.isRadical_iff_quotient_reduced _).1
      (isRadical_iff_span_singleton.1 hsep.squarefree.isRadical)
  let ψ : TensorProduct S D L ≃ₐ[S] AdjoinRoot (f.map (algebraMap S L)) :=
    (Algebra.TensorProduct.comm S D L).trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl φ).trans
        ((KummerRootTensor.tensorEquiv L f).restrictScalars S))
  exact isReduced_of_injective ψ.toRingHom ψ.injective

end GlobalTheory
end

section

namespace GlobalTheory

open Subgroup

namespace UnfoldSemidirect

theorem mem_map_conj_iff {G : Type} [Group G] (K : Subgroup G) (g p : G) :
    p ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * p * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

end UnfoldSemidirect


open UnfoldSemidirect in
theorem relIndex_unfold_semidirect : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ (q : M) (X : N), (TP ⊓ KP.map (MulAut.conj (s q * u X)).toMonoidHom).relIndex CP = (TM ⊓ KM.map (MulAut.conj q).toMonoidHom).relIndex CM * (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) := by
  intro P M N _ _ _ s π u hsec hu hker KP KM L hsK hπK huK TM CM TP CP hCT hTP hCP hcond q X
  have hπu : ∀ Y, π (u Y) = 1 := fun Y => (hker _).2 ⟨Y, rfl⟩
  have hsinj : Function.Injective s := fun a b h => by
    have := congrArg π h
    rwa [hsec, hsec] at this
  have key : ∀ r : M, (s q * u X)⁻¹ * s (q * r * q⁻¹) * (s q * u X) = (u X)⁻¹ * s r * u X := by
    intro r; simp only [map_mul, map_inv]; group
  have hπc : ∀ r : M, π ((u X)⁻¹ * s r * u X) = r := by
    intro r; simp [map_mul, map_inv, hπu, hsec]
  have hCP' : CP = CM.map s := by
    ext p; rw [hCP p, Subgroup.mem_map]
  have hH : TP ⊓ KP.map (MulAut.conj (s q * u X)).toMonoidHom
      = ((TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓
          KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).map
          (MulAut.conj q).toMonoidHom).map s := by
    ext p
    rw [Subgroup.mem_inf, mem_map_conj_iff, hTP p, Subgroup.mem_map]
    simp only [mem_map_conj_iff, Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.coe_comp,
      Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hk⟩
      have hk' : (u X)⁻¹ * s (q⁻¹ * t * q) * u X ∈ KP := by
        rw [← key]; simpa [mul_assoc] using hk
      refine ⟨t, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
      · simpa [mul_assoc] using ht
      · have h1 := hπK _ hk'
        rwa [hπc] at h1
      · simpa using hk'
    · rintro ⟨t, ⟨⟨hr1, hr2⟩, hr3⟩, rfl⟩
      refine ⟨⟨t, by simpa [mul_assoc] using hr1, rfl⟩, ?_⟩
      have := key (q⁻¹ * t * q)
      have e : q * (q⁻¹ * t * q) * q⁻¹ = t := by group
      rw [e] at this
      rw [this]; exact hr3
  have hSq : TM ⊓ KM.map (MulAut.conj q).toMonoidHom
      = (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM).map (MulAut.conj q).toMonoidHom := by
    ext p
    simp only [Subgroup.mem_inf, mem_map_conj_iff, inv_inv]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by simpa [mul_assoc] using h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by simpa [mul_assoc] using h1, h2⟩
  have hle1 : (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓
          KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).map (MulAut.conj q).toMonoidHom
        ≤ (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM).map (MulAut.conj q).toMonoidHom :=
    Subgroup.map_mono inf_le_left
  have hle2 : (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM).map (MulAut.conj q).toMonoidHom ≤ CM := by
    rw [← hSq]; exact hcond q
  rw [hH, hCP', Subgroup.relIndex_map_map_of_injective _ _ hsinj,
    ← Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj q).injective, ← hSq, mul_comm]

end GlobalTheory
end

section

namespace GlobalTheory.FibreEquivalence

noncomputable def fibreEquiv {H : Type} [Group H] (D C : Subgroup H) (h : D ≤ C) (z : H ⧸ C) :
    { y : H ⧸ D // Subgroup.quotientMapOfLE h y = z } ≃ C ⧸ D.subgroupOf C :=
  have key : ∀ y : H ⧸ D,
      (Subgroup.quotientEquivProdOfLE h y).1 = Subgroup.quotientMapOfLE h y := by
    intro y
    induction y using QuotientGroup.induction_on
    rfl
  { toFun := fun y => (Subgroup.quotientEquivProdOfLE h y.1).2
    invFun := fun b => ⟨(Subgroup.quotientEquivProdOfLE h).symm (z, b), by
      rw [← key, Equiv.apply_symm_apply]⟩
    left_inv := fun y => by
      apply Subtype.ext
      change (Subgroup.quotientEquivProdOfLE h).symm
        (z, (Subgroup.quotientEquivProdOfLE h y.1).2) = y.1
      rw [Equiv.symm_apply_eq]
      exact Prod.ext (by rw [key]; exact y.2.symm) rfl
    right_inv := fun b => by
      change (Subgroup.quotientEquivProdOfLE h
        ((Subgroup.quotientEquivProdOfLE h).symm (z, b))).2 = b
      rw [Equiv.apply_symm_apply] }

theorem fibre_finite_card : ∀ {H : Type} [inst : Group H] (D C : Subgroup H) (h : D ≤ C), Subgroup.relIndex D C ≠ (0 : ℕ) → ∀ (z : H ⧸ C), Finite { y : H ⧸ D // Subgroup.quotientMapOfLE h y = z } ∧ Nat.card { y : H ⧸ D // Subgroup.quotientMapOfLE h y = z } = Subgroup.relIndex D C := by
  intro H _ D C h hD z
  have hcard : Nat.card { y : H ⧸ D // Subgroup.quotientMapOfLE h y = z } = Subgroup.relIndex D C := by
    rw [Nat.card_congr (fibreEquiv D C h z)]
    rfl
  exact ⟨Nat.finite_of_card_ne_zero (by rw [hcard]; exact hD), hcard⟩

end GlobalTheory.FibreEquivalence
end

section

namespace GlobalTheory.DoubleCosetWeight

open Subgroup

theorem inf_map_conj_mul_eq {G : Type} [Group G] (T K : Subgroup G) {t k : G}
    (ht : t ∈ T) (hk : k ∈ K) (q : G) :
    T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom =
      (T ⊓ K.map (MulAut.conj q).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
  ext x
  simp only [mem_inf, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hxT, y, hy, rfl⟩
    refine ⟨q * (k * y * k⁻¹) * q⁻¹, ⟨?_, k * y * k⁻¹, K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk), rfl⟩, ?_⟩
    · have : q * (k * y * k⁻¹) * q⁻¹ = t⁻¹ * (t * q * k * y * (t * q * k)⁻¹) * t := by group
      rw [this]; exact T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
    · group
  · rintro ⟨z, ⟨hzT, y, hy, rfl⟩, rfl⟩
    refine ⟨T.mul_mem (T.mul_mem ht hzT) (T.inv_mem ht), k⁻¹ * y * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hy) hk, ?_⟩
    group

def gen {G : Type} [Group G] (T K : Subgroup G) : Subgroup G :=
  ⨆ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom

theorem gen_map_le {G : Type} [Group G] (T K : Subgroup G) {t : G} (ht : t ∈ T) :
    (gen T K).map (MulAut.conj t).toMonoidHom ≤ gen T K := by
  rw [map_le_iff_le_comap]
  refine iSup_le fun q => ?_
  intro x hx
  rw [mem_comap]
  have h1 : (MulAut.conj t).toMonoidHom x ∈ T ⊓ K.map (MulAut.conj (t * q * 1)).toMonoidHom := by
    rw [inf_map_conj_mul_eq T K ht K.one_mem q]
    exact mem_map_of_mem _ hx
  exact (le_iSup (fun q : G => T ⊓ K.map (MulAut.conj q).toMonoidHom) (t * q * 1)) h1

theorem gen_map_eq {G : Type} [Group G] (T K : Subgroup G) {t : G} (ht : t ∈ T) :
    (gen T K).map (MulAut.conj t).toMonoidHom = gen T K := by
  refine le_antisymm (gen_map_le T K ht) fun x hx => ?_
  have : (MulAut.conj t⁻¹).toMonoidHom x ∈ gen T K :=
    gen_map_le T K (T.inv_mem ht) (mem_map_of_mem _ hx)
  refine ⟨_, this, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

theorem relIndex_eq {G : Type} [Group G] (T C K : Subgroup G)
    (hC : ∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) :
    ∀ t ∈ T, ∀ k ∈ K, ∀ q : G,
      (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C =
        (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C := by
  intro t ht k hk q
  have hN : gen T K ≤ C := iSup_le hC
  have hA : ∀ p : G, T ⊓ K.map (MulAut.conj p).toMonoidHom ≤ gen T K := fun p =>
    le_iSup (fun q : G => T ⊓ K.map (MulAut.conj q).toMonoidHom) p
  have e1 := relIndex_mul_relIndex _ _ _ (hA (t * q * k)) hN
  have e2 := relIndex_mul_relIndex _ _ _ (hA q) hN
  rw [← e1, ← e2, inf_map_conj_mul_eq T K ht hk q]
  congr 1
  conv_lhs => rw [← gen_map_eq T K ht]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj t).injective

end GlobalTheory.DoubleCosetWeight

theorem GlobalTheory.doubleCoset_relIndex_const : ∀ (G : Type) [Group G] (T C K : Subgroup G), (∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) → ∀ t ∈ T, ∀ k ∈ K, ∀ q : G, (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C = (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C :=
  fun G _ T C K hC => GlobalTheory.DoubleCosetWeight.relIndex_eq T C K hC
end

section

namespace GlobalTheory

theorem unitsMod_away_of_unique_prime (B D : Type) [CommRing B] [CommRing D] [Algebra B D]
    (f : B) (P : Ideal B) (Q : Ideal D) (g : D)
    (hQP : Q.comap (algebraMap B D) = P)
    (huniq : ∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q) :
    ∀ s : B, s ∉ P → ∃ t : Localization.Away g,
      algebraMap B (Localization.Away g) s * t - 1 ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
  intro s hs
  set A := Localization.Away g
  by_cases hI : Ideal.span {algebraMap B A s, algebraMap B A f} = ⊤
  · have h1 : (1 : A) ∈ Ideal.span {algebraMap B A s, algebraMap B A f} := by
      rw [hI]; exact Submodule.mem_top
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp h1
    refine ⟨a, ?_⟩
    have : algebraMap B A s * a - 1 = (-b) * algebraMap B A f := by
      rw [← hab]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · exfalso
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hI
    have hMp : (M.comap (algebraMap D A)).IsPrime := Ideal.comap_isPrime _ _
    have hf : algebraMap B D f ∈ M.comap (algebraMap D A) := by
      rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact hIM (Ideal.subset_span (by simp))
    have hg : g ∉ M.comap (algebraMap D A) := by
      intro hgM
      rw [Ideal.mem_comap] at hgM
      exact hM.ne_top (Ideal.eq_top_of_isUnit_mem _ hgM
        (IsLocalization.Away.algebraMap_isUnit g))
    have hEq := huniq _ hMp hf hg
    apply hs
    rw [← hQP, Ideal.mem_comap, ← hEq, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact hIM (Ideal.subset_span (by simp))

end GlobalTheory
end

section

namespace GlobalTheory

theorem residue_surj_localizationAway : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (P : Ideal B), P.IsMaximal → ∀ (Q : Ideal D) (g : D), g ∉ Q → Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) → ∀ a : Localization.Away g, ∃ b : B, a - algebraMap B (Localization.Away g) b ∈ Q.map (algebraMap D (Localization.Away g)) := by
  intro B D _ _ _ P hP Q g hg hQP hsurj a
  obtain ⟨⟨d, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) a
  obtain ⟨n, hn⟩ := s.2
  obtain ⟨bd, hbd⟩ := hsurj d
  obtain ⟨bg, hbg⟩ := hsurj g
  have hbgP : bg ∉ P := by
    intro h
    rw [← hQP, Ideal.mem_comap] at h
    exact hg (by simpa using Q.add_mem hbg h)
  obtain ⟨c, i, hi, hci⟩ := hP.exists_inv hbgP
  have hcg : algebraMap B D c * g - 1 ∈ Q := by
    have hiQ : algebraMap B D i ∈ Q := by rw [← hQP] at hi; exact hi
    have e : algebraMap B D c * g - 1 = algebraMap B D c * (g - algebraMap B D bg) - algebraMap B D i := by
      have := congrArg (algebraMap B D) hci
      simp only [map_add (f := _), map_mul, map_one] at this
      linear_combination this
    rw [e]
    exact Q.sub_mem (Q.mul_mem_left _ hbg) hiQ
  refine ⟨bd * c ^ n, ?_⟩
  have key : d - algebraMap B D (bd * c ^ n) * (s : D) ∈ Q := by
    rw [← hn]
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hcg hbd ⊢
    simp only [map_sub, map_mul, map_pow, map_one, sub_eq_zero] at hcg hbd ⊢
    rw [hbd, mul_assoc, ← mul_pow, hcg, one_pow, mul_one]
  set L := Localization.Away g
  have hspec : algebraMap D L (s : D) * IsLocalization.mk' L (1 : D) s = 1 := by
    rw [IsLocalization.mk'_spec', map_one]
  have e : IsLocalization.mk' L d s - algebraMap B L (bd * c ^ n)
      = algebraMap D L (d - algebraMap B D (bd * c ^ n) * (s : D)) * IsLocalization.mk' L (1 : D) s := by
    rw [IsScalarTower.algebraMap_apply B D L, IsLocalization.mk'_eq_mul_mk'_one, map_sub, map_mul (algebraMap D L)]
    linear_combination (algebraMap D L (algebraMap B D (bd * c ^ n))) * hspec
  rw [e]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ key)

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.BalRank

variable {O : Type} [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X]

def balBil : Submodule ℤ (LinearMap.BilinForm ℤ X) where
  carrier := {β | ∀ (a : O) y z, β (a • y) z = β y (bar a • z)}
  add_mem' := by
    rintro β β' h k a y z
    simp only [LinearMap.add_apply, h a y z, k a y z]
  zero_mem' := by simp
  smul_mem' := by
    rintro n β h a y z
    simp only [LinearMap.smul_apply, h a y z]

variable {bar X}

end GlobalTheory.BalRank
end
end

section

namespace GlobalTheory

theorem linIndep_intBilinForm_charZero_comb_eq_zero
    {X : Type} [AddCommGroup X] {m : ℕ} (gam : Fin m → LinearMap.BilinForm ℤ X)
    (k : Type) [Field k] [CharZero k] (a : Fin m → k) :
    LinearIndependent ℤ gam → (∀ y z, ∑ i, a i * (gam i y z : k) = 0) → a = 0 := by
  intro hli hsum

  let L : LinearMap.BilinForm ℤ X →ₗ[ℤ] (X → X → ℚ) :=
    { toFun := fun B y z => ((B y z : ℤ) : ℚ)
      map_add' := by intro B C; funext y z; simp
      map_smul' := by intro n B; funext y z; simp }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro B hB
    ext y z
    have := congrFun (congrFun hB y) z
    simpa [L] using this
  have hZ : LinearIndependent ℤ (L ∘ gam) := hli.map' L hker
  have hQ : LinearIndependent ℚ (L ∘ gam) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hZ
  funext j
  by_contra hj
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero ℚ (V := k) hj
  have hrel : ∑ i, ℓ (a i) • (L ∘ gam) i = 0 := by
    funext y z
    have h0 := congrArg ℓ (hsum y z)

    rw [map_sum, map_zero] at h0
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, Pi.zero_apply, smul_eq_mul, L,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (a i), ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  have := (Fintype.linearIndependent_iff.mp hQ) _ hrel j
  exact hℓ this

end GlobalTheory
end
