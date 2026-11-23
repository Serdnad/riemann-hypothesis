module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.lattice_normal_form_coordinates

open GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect

variable {F : Type} [Field F] {n c : ℕ}

theorem eN_eq_zero {N i : ℕ} (h : N ≤ i) : Loc.eN F N i = 0 := by
  funext l
  unfold Loc.eN
  have := l.2
  rw [if_neg (by omega)]
  rfl

theorem sum_eN_apply (g : Fin c → F) (l : Fin (n + c)) :
    (∑ i : Fin c, g i • Loc.eN F (n + c) (n + i.1)) l = if h : l.1 < n then 0 else g ⟨l.1 - n, by omega⟩ := by
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Loc.eN, smul_eq_mul]
  split_ifs with h
  · exact Finset.sum_eq_zero fun i _ => by rw [if_neg (by omega), mul_zero]
  · rw [Finset.sum_eq_single ⟨l.1 - n, by omega⟩]
    · rw [if_pos (by simp; omega), mul_one]
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro hl
      exact hb (Fin.ext (by simp; omega))
    · simp

theorem decomp (v : Fin (n + c) → F) :
    v = Loc.inX F n c (fun a => v (Fin.castAdd c a)) +
      ∑ i : Fin c, v (Fin.natAdd n i) • Loc.eN F (n + c) (n + i.1) := by
  funext l
  rw [Pi.add_apply, inX_apply, sum_eN_apply]
  split_ifs with h
  · rw [add_zero]
    rfl
  · rw [zero_add]
    congr 1
    exact Fin.ext (by simp; omega)

theorem isFrame : IsFrame (LinearMap.range (Loc.inX F n c)) (fun i : Fin c => Loc.eN F (n + c) (n + i.1)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrFun hg (Fin.natAdd n i)
    rw [sum_eN_apply, dite_eq_right (by simp)] at this
    simpa using this
  · rw [Submodule.disjoint_def]
    rintro _ ⟨x, rfl⟩ hv
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hv
    funext l
    have h1 := congrFun hg l
    rw [sum_eN_apply] at h1
    by_cases h : l.1 < n
    · rw [dite_eq_left h] at h1
      exact h1.symm
    · rw [inX_apply, dite_eq_right h]
      rfl
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [decomp v]
    exact Submodule.add_mem_sup ⟨_, rfl⟩
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem flag_le (i : Fin c) :
    flag (LinearMap.range (Loc.inX F n c)) (fun i : Fin c => Loc.eN F (n + c) (n + i.1)) i ≤ Loc.Ufl F n c i.1 := by
  refine sup_le ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨x, rfl⟩
    exact inX_mem_Ufl _ x
  · rintro _ ⟨l, hl, rfl⟩
    have : l.1 < i.1 := hl
    exact eN_mem_Ufl (by omega)

theorem R1cond_of {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)}
    (h1 : ∀ x, r (Loc.inX F n c x) ∈ Loc.Ufl F n c 0)
    (h2 : ∀ i : Fin c, i.1 = 0 → r (Loc.eN F (n + c) (n + i.1)) = Loc.eN F (n + c) (n + i.1))
    (h3 : ∀ i : Fin c, r (Loc.eN F (n + c) (n + i.1)) - Loc.eN F (n + c) (n + i.1) ∈ Loc.Ufl F n c i.1) :
    Loc.R1cond F n c r := by
  refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
  · rw [decomp v, map_add (f := _), map_sum]
    refine add_mem (Ufl_mono (Nat.zero_le i) (h1 _)) (Submodule.sum_mem _ fun j _ => ?_)
    by_cases hj : j.1 < i
    · rw [map_smul]
      refine Submodule.smul_mem _ _ ?_
      have := add_mem (Ufl_mono hj.le (h3 j)) (eN_mem_Ufl (F := F) (n := n) (c := c) (i := i) (s := n + j.1) (by omega))
      rwa [sub_add_cancel] at this
    · rw [mem_Ufl.1 hv (Fin.natAdd n j) (by simp; omega), zero_smul, map_zero]
      exact zero_mem _
  · rcases Nat.eq_zero_or_pos c with hc | hc
    · rw [eN_eq_zero (by omega), map_zero]
    · exact h2 ⟨0, hc⟩ rfl
  · by_cases hi : i < c
    · exact h3 ⟨i, hi⟩
    · rw [eN_eq_zero (by omega), map_zero, sub_zero]
      exact zero_mem _

theorem R1cond_inv {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)} (hr : Loc.R1cond F n c r) :
    Loc.R1cond F n c r⁻¹ := by
  have key : ∀ i, ∀ v ∈ Loc.Ufl F n c i, r⁻¹ v ∈ Loc.Ufl F n c i := by
    intro i v hv
    have hle : (Loc.Ufl F n c i).map r.toLinearMap ≤ Loc.Ufl F n c i := by
      rintro _ ⟨w, hw, rfl⟩
      exact hr.1 i w hw
    have heq := Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq r _)
    rw [← heq] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have : r⁻¹ (r.toLinearMap w) = w := r.symm_apply_apply w
    rwa [this]
  refine ⟨key, ?_, fun i => ?_⟩
  · show r.symm _ = _
    rw [LinearEquiv.symm_apply_eq, hr.2.1]
  · have h := neg_mem (key i _ (hr.2.2 i))
    have e : r⁻¹ (r (Loc.eN F (n + c) (n + i))) = Loc.eN F (n + c) (n + i) := r.symm_apply_apply _
    rwa [map_sub, e, neg_sub] at h

theorem mem_unipotentRadical_of_isSemidirect {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)}
    (hr : IsSemidirect (LinearMap.range (Loc.inX F n c)) (fun i : Fin c => Loc.eN F (n + c) (n + i.1)) r) :
    r ∈ Loc.R1 F n c := by
  obtain ⟨γ, g, u, hg, hu, rfl⟩ := hr
  have h1 : Loc.R1cond F n c g := by
    refine R1cond_of (fun x => ?_) (fun i _ => hg.2 i) (fun i => ?_)
    · have := hg.1 ⟨Loc.inX F n c x, x, rfl⟩
      obtain ⟨y, hy⟩ := (γ ⟨Loc.inX F n c x, x, rfl⟩).2
      rw [show g (Loc.inX F n c x) = Loc.inX F n c y from this.trans hy.symm]
      exact inX_mem_Ufl 0 y
    · rw [show g (Loc.eN F (n + c) (n + i.1)) = Loc.eN F (n + c) (n + i.1) from hg.2 i, sub_self]
      exact zero_mem _
  have h2 : Loc.R1cond F n c u := by
    refine R1cond_of (fun x => ?_) hu.2.1 (fun i => flag_le i (hu.2.2 i))
    rw [hu.1 _ ⟨x, rfl⟩]
    exact inX_mem_Ufl 0 x
  exact ⟨h1.mul h2, R1cond_inv (h1.mul h2)⟩

theorem isLattice_map {O : Type} [CommRing O] [Algebra O F] {V W : Type} [AddCommGroup V] [Module F V] [Module O V]
    [IsScalarTower O F V] [AddCommGroup W] [Module F W] [Module O W] [IsScalarTower O F W] (φ : V ≃ₗ[F] W)
    (L : Submodule O V) (hL : Submodule.IsLattice F L) :
    Submodule.IsLattice F (L.map (φ.toLinearMap.restrictScalars O)) := by
  refine ⟨hL.fg.map _, ?_⟩
  have h : ((L.map (φ.toLinearMap.restrictScalars O) : Submodule O W) : Set W) = φ.toLinearMap '' (L : Set V) := rfl
  intro s hs hli
  have hs' : φ.symm '' s ⊆ (L : Set V) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := h ▸ hs hy
    simpa using hz
  have hi : LinearIndepOn O id (φ.symm '' s) := by
    apply (linearIndepOn_id_imageₛ_iff (f := φ.symm.toLinearMap.restrictScalars O) φ.symm.injective.injOn).2
    exact hli
  have hf := hL.linearIndepOn (φ.symm '' s) hs' hi
  have hm := (linearIndepOn_id_imageₛ_iff (f := φ.toLinearMap) φ.injective.injOn).2 hf
  simpa [Set.image_image, Function.comp_def] using hm

theorem isFullLattice_map {O : Type} [CommRing O] [Algebra O F] {V W : Type}
    [AddCommGroup V] [Module F V] [Module O V] [IsScalarTower O F V]
    [AddCommGroup W] [Module F W] [Module O W] [IsScalarTower O F W]
    (φ : V ≃ₗ[F] W) (L : Submodule O V) (hL : Submodule.IsFullLattice F L) :
    Submodule.IsFullLattice F (L.map (φ.toLinearMap.restrictScalars O)) := by
  haveI := isLattice_map φ L hL.toIsLattice
  refine { span_eq_top := ?_ }
  change Submodule.span F (φ.toLinearMap '' (L : Set V)) = ⊤
  rw [← Submodule.map_span φ.toLinearMap, hL.span_eq_top, Submodule.map_top, LinearEquiv.range]

theorem latticeNormalFormCoord_of : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalForm → GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalFormCoord := by
  intro H O F _ _ _ _ _ _ q hq n c L hL Λ hΛ
  let φ := LinearEquiv.ofInjective (Loc.inX F n c) inX_injective
  obtain ⟨r, e, z, hr, ⟨z', rfl⟩, h⟩ := H O F (Fin (n + c) → F) q hq c _ _ isFrame _ (by
    first | exact isFullLattice_map φ L hL | exact isLattice_map φ L hL) Λ hΛ
  refine ⟨r, mem_unipotentRadical_of_isSemidirect hr, e, z', ?_⟩
  rw [h]
  congr 1
  unfold inY
  rw [← Submodule.map_comp]
  rfl

end GlobalTheory.Proof.lattice_normal_form_coordinates
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.QNormalShape

section Abstract

variable {O F : Type} [CommRing O] [Field F] [Algebra O F]

theorem mem_span_basis_iff [IsDomain O] [IsFractionRing O F] {N : ℕ} (b : Module.Basis (Fin N) F (Fin N → F)) (v : Fin N → F) :
    v ∈ Submodule.span O (Set.range b) ↔ ∀ l, b.repr v l ∈ Set.range (algebraMap O F) :=
  b.mem_span_iff_repr_mem O v

theorem isLattice_span_basis {N : ℕ} (b : Module.Basis (Fin N) F (Fin N → F)) :
    Submodule.IsFullLattice F (Submodule.span O (Set.range b)) := by
  have hfg : (Submodule.span O (Set.range b)).FG := Submodule.fg_span (Set.finite_range _)
  have hspan : Submodule.span F (↑(Submodule.span O (Set.range b)) : Set (Fin N → F)) = ⊤ := by
    rw [Submodule.span_span_of_tower, b.span_eq]
  refine { fg := hfg, span_eq_top := hspan, linearIndepOn := ?_ }
  intro s hs hli
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · exact linearIndepOn_empty F id
  · have : Nontrivial O := (algebraMap O F).domain_nontrivial
    have : FaithfulSMul O F := (faithfulSMul_iff_algebraMap_injective O F).2 <| by
      intro a a' heq
      apply hli.linearIndependent.smul_left_injective ⟨x, hx⟩
      simpa only [id_eq, algebraMap_smul] using congrArg (fun t : F => t • x) heq
    refine Submodule.linearIndepOn_of_finrank_le_finrank_span _ hfg ?_ hs hli
    rw [hspan, finrank_top, Module.finrank_eq_card_basis b]
    exact finrank_range_le_card b

theorem mem_normalForm_iff {Y : Type} [AddCommGroup Y] [Module F Y] [Module O Y] {c : ℕ} (q : O)
    (M : Submodule O Y) (a : Fin c → Y) (e : Fin c → ℤ) (z y : Y) :
    y ∈ IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.normalForm F q M a e z ↔ ∃ m ∈ M, ∃ s : Fin c → O,
      y = m + ∑ i, s i • ((algebraMap O F q) ^ (e i) • (a i + if i.1 = 0 then z else 0)) := by
  unfold IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.normalForm
  rw [← Submodule.span_range_eq_iSup, Submodule.mem_sup]
  simp only [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨m, hm, _, ⟨s, rfl⟩, rfl⟩
    exact ⟨m, hm, s, rfl⟩
  · rintro ⟨m, hm, s, rfl⟩
    exact ⟨m, hm, _, ⟨s, rfl⟩, rfl⟩

theorem irreducible_of_notMem_sq [IsDomain O] [IsDiscreteValuationRing O] {q : O}
    (h1 : q ∈ IsLocalRing.maximalIdeal O) (h2 : q ∉ IsLocalRing.maximalIdeal O ^ 2) : Irreducible q := by
  refine ⟨h1, fun a b hab => ?_⟩
  by_contra h
  rw [not_or] at h
  exact h2 (hab ▸ pow_two (IsLocalRing.maximalIdeal O) ▸ Ideal.mul_mem_mul h.1 h.2)

end Abstract

theorem exists_shape : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalFormCoord → ∀ (E : Type) [Field E] [NumberField E] [StarRing E]
    (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (n c : ℕ)
    (h : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)), ∃ r ∈ Loc.R1 E n c, ∃ (e : Fin c → ℤ) (z : Fin n → E),
      (r * h) '' {v | IntV P v} = GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P n c e z := by
  intro H E _ _ _ P hd n c h
  have hP := P.isPrime
  have hS : P.asIdeal.primeCompl ≤ (𝓞 E)⁰ := Ideal.primeCompl_le_nonZeroDivisors _
  let A := Localization.subalgebra.ofField E P.asIdeal.primeCompl hS
  have : IsLocalization.AtPrime A P.asIdeal := Localization.subalgebra.isLocalization_ofField E _ hS
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) P.ne_bot A
  have : IsFractionRing A E := Localization.subalgebra.isFractionRing_ofField E _ hS
  have hA : ∀ a : E, a ∈ Set.range (algebraMap A E) ↔ IntAt P a := by
    intro a
    constructor
    · rintro ⟨⟨x, r, s, hs, rfl⟩, rfl⟩
      refine ⟨r, s, hs, ?_⟩
      have : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)
      change algebraMap (𝓞 E) E s * (algebraMap (𝓞 E) E r * (algebraMap (𝓞 E) E s)⁻¹) = _
      field_simp
    · rintro ⟨r, s, hs, e⟩
      have : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)
      refine ⟨⟨a, r, s, hs, ?_⟩, rfl⟩
      rw [← e]
      field_simp
  have hmax : Ideal.map (algebraMap (𝓞 E) A) P.asIdeal = IsLocalRing.maximalIdeal A :=
    IsLocalization.AtPrime.map_eq_maximalIdeal P.asIdeal A
  have hq : Irreducible (algebraMap (𝓞 E) A ((qOf P : ℕ) : 𝓞 E)) := by
    refine irreducible_of_notMem_sq ?_ ?_
    · rw [← hmax]
      exact Ideal.mem_map_of_mem _ (Ideal.absNorm_mem _)
    · rw [← hmax, ← Ideal.map_pow, IsLocalization.algebraMap_mem_map_algebraMap_iff P.asIdeal.primeCompl]
      rintro ⟨s, hs, hm⟩
      exact (Ideal.IsPrime.mul_mem_pow _ hm).elim hs hd.2
  obtain ⟨r, hr, e, z, hz⟩ := H A E _ hq n c
    (Submodule.span A (Set.range (Pi.basisFun E (Fin n))))
    (by first | exact isLattice_span_basis (Pi.basisFun E (Fin n))
              | exact (isLattice_span_basis (Pi.basisFun E (Fin n))).toIsLattice)
    (Submodule.span A (Set.range ((Pi.basisFun E (Fin (n + c))).map h)))
    (by first | exact isLattice_span_basis ((Pi.basisFun E (Fin (n + c))).map h)
              | exact (isLattice_span_basis ((Pi.basisFun E (Fin (n + c))).map h)).toIsLattice)
  refine ⟨r, hr, e, z, ?_⟩
  have hqE : algebraMap A E (algebraMap (𝓞 E) A ((qOf P : ℕ) : 𝓞 E)) = (qOf P : E) := by
    rw [map_natCast, map_natCast]
  ext y
  have hy := SetLike.ext_iff.1 hz y
  rw [mem_normalForm_iff, hqE] at hy
  simp only [IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.moveBy, Submodule.mem_map, mem_span_basis_iff, hA, Module.Basis.map_repr,
    LinearEquiv.trans_apply, Pi.basisFun_repr, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe] at hy
  simp only [Set.mem_image, Set.mem_ofPred_eq, IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat, mem_stdAt_iff, IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨_, ⟨l, hl, rfl⟩, s, hs⟩ := hy.1 ⟨h v, by simpa [IntV] using hv, rfl⟩
    exact ⟨l, hl, fun i => algebraMap A E (s i), fun i => (hA _).1 ⟨_, rfl⟩, by simpa only [algebraMap_smul] using hs⟩
  · rintro ⟨l, hl, s, hs, rfl⟩
    choose t ht using fun i => (hA _).2 (hs i)
    obtain ⟨v, hv, hv'⟩ := hy.2 ⟨_, ⟨l, hl, rfl⟩, t, by simp only [← ht, algebraMap_smul]⟩
    refine ⟨h.symm v, hv, ?_⟩
    rw [← hv']
    simp

end GlobalTheory.QNormalShape
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

private theorem rank_k_ineqs_poly_wide (C w y n m k : ℝ) (hw : 0 < w) (hy : 128 * |C| + 2 ≤ y)
    (hn1 : w ^ 4 * y ^ 128 ≤ n) (hn2 : n ≤ 2 * (w ^ 4 * y ^ 129))
    (hm1 : w / y ≤ m) (hm2 : m ≤ 2 * (w / y))
    (hk1 : w ^ 9 * y ^ 160 ≤ k) (hk2 : k ≤ 2 * (w ^ 9 * y ^ 160)) :
    C * m ^ 5 * (2 * n) * y ^ 16 * y ^ 16 ≤ k ∧ k ≤ w * n * (n * (y ^ 16)⁻¹) ∧
      Real.sqrt (k / m) ≤ n * (y ^ 16)⁻¹ := by
  have hC := abs_nonneg C
  have hy2 : 2 ≤ y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn1
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm1
  have hR : w ^ 4 * y ^ 112 ≤ n * (y ^ 16)⁻¹ := by
    calc w ^ 4 * y ^ 112 = (w ^ 4 * y ^ 128) * (y ^ 16)⁻¹ := by field_simp
      _ ≤ n * (y ^ 16)⁻¹ := by gcongr
  refine ⟨?_, ?_, ?_⟩
  · have h5 : 128 * |C| ≤ y ^ 4 := by
      calc 128 * |C| ≤ y := by linarith
        _ ≤ y ^ 4 := le_self_pow₀ hy1 (by norm_num)
    calc C * m ^ 5 * (2 * n) * y ^ 16 * y ^ 16
        ≤ |C| * (2 * (w / y)) ^ 5 * (2 * (2 * (w ^ 4 * y ^ 129))) * y ^ 16 * y ^ 16 := by
          gcongr
          exact le_abs_self C
      _ = (128 * |C|) * (w ^ 9 * y ^ 156) := by field_simp; ring
      _ ≤ y ^ 4 * (w ^ 9 * y ^ 156) := by gcongr
      _ = w ^ 9 * y ^ 160 := by ring
      _ ≤ k := hk1
  · have h80 : 2 ≤ y ^ 80 := hy2.trans (le_self_pow₀ hy1 (by norm_num))
    calc k ≤ 2 * (w ^ 9 * y ^ 160) := hk2
      _ ≤ y ^ 80 * (w ^ 9 * y ^ 160) := by gcongr
      _ = w * (w ^ 4 * y ^ 128) * (w ^ 4 * y ^ 112) := by ring
      _ ≤ w * n * (n * (y ^ 16)⁻¹) := by gcongr
  · have h63 : 2 ≤ y ^ 63 := hy2.trans (le_self_pow₀ hy1 (by norm_num))
    refine le_trans ?_ hR
    rw [Real.sqrt_le_left (by positivity)]
    have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk1
    calc k / m ≤ (2 * (w ^ 9 * y ^ 160)) / (w / y) := by gcongr
      _ = 2 * (w ^ 8 * y ^ 161) := by field_simp
      _ ≤ y ^ 63 * (w ^ 8 * y ^ 161) := by gcongr
      _ = (w ^ 4 * y ^ 112) ^ 2 := by ring

theorem explicitChoice_rankK_lower_upper_bounds :
    SzRow (fun C D L => (C.P.CkLow * (D.R.m : ℝ) ^ jG * D.R.f * L.sc.L * L.sc.x ^ L.sc.eps ≤ D.R.k) ∧
      ((D.R.k : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 2) * D.R.n * R0 L) ∧ (Real.sqrt ((D.R.k : ℝ) / D.R.m) ≤ R0 L)) := by
  intro eps he _ C _
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩
  have ht : Filter.Tendsto (fun x : ℝ => x ^ (eps / 16)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by positivity)
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop (128 * |C.P.CkLow| + 2))
  refine ⟨x0, fun D L hε hx hV => ?_⟩
  have hn2 : (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 16) := by
    have h1 : L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100) ≤ L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 16) :=
      Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le (by linarith [L.sc.eps_pos])
    linarith [hV.ranks.n_le]
  obtain ⟨⟨hn1, -⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, -⟩ := hV.ranks
  have hy := hx0 _ hx
  rw [← hε] at hy
  have hxp : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have key : ∀ (a b : ℕ), (L.sc.x ^ ((1 : ℝ) / 2)) ^ a * (L.sc.x ^ (L.sc.eps / 16)) ^ b =
      L.sc.x ^ ((a : ℝ) / 2 + b * L.sc.eps / 16) := by
    intro a b
    rw [← Real.rpow_mul_natCast hxp.le, ← Real.rpow_mul_natCast hxp.le, ← Real.rpow_add hxp]
    congr 1; ring
  have e1 : L.sc.x ^ (2 + 8 * L.sc.eps) = (L.sc.x ^ ((1 : ℝ) / 2)) ^ 4 * (L.sc.x ^ (L.sc.eps / 16)) ^ 128 := by
    rw [key]; congr 1; push_cast; ring
  have e1' : L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 16) =
      (L.sc.x ^ ((1 : ℝ) / 2)) ^ 4 * (L.sc.x ^ (L.sc.eps / 16)) ^ 129 := by
    rw [key]; congr 1; push_cast; ring
  have e2 : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) = (L.sc.x ^ ((1 : ℝ) / 2)) ^ 9 * (L.sc.x ^ (L.sc.eps / 16)) ^ 160 := by
    rw [key]; congr 1; push_cast; ring
  have e3 : L.sc.x ^ L.sc.eps = (L.sc.x ^ (L.sc.eps / 16)) ^ 16 := by
    rw [← Real.rpow_mul_natCast hxp.le]; congr 1; push_cast; ring
  have e4 : Real.sqrt (L.sc.x * L.sc.delta1) = L.sc.x ^ ((1 : ℝ) / 2) / L.sc.x ^ (L.sc.eps / 16) := by
    unfold Scale.delta1
    rw [Real.sqrt_eq_rpow, Real.mul_rpow hxp.le (by positivity), ← Real.rpow_mul hxp.le, div_eq_mul_inv (_ ^ _),
      ← Real.rpow_neg hxp.le]
    congr 2; ring
  have hf : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by
    unfold Ranks.f; push_cast; rfl
  rw [e1] at hn1
  rw [e1'] at hn2
  rw [e2] at hk1 hk2
  rw [e4] at hm1 hm2
  have h := rank_k_ineqs_poly_wide C.P.CkLow _ _ _ _ _ (by positivity) hy hn1 hn2 hm1 hm2 hk1 hk2
  simp only [R0, jG, Scale.L, hf, Real.rpow_neg hxp.le, e3]
  exact h

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem SzRow.and {P Q : FC → ∀ D : D7, SizeData₂ D → Prop} (hP : SzRow P) (hQ : SzRow Q) :
    SzRow (fun C D L => P C D L ∧ Q C D L) := by
  intro eps h0 h1 C hC
  obtain ⟨a1, ha1⟩ := hP eps h0 h1 C hC
  obtain ⟨b1, hb1⟩ := hQ eps h0 h1 C hC
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  refine ⟨max a3 b3, fun D L he hx hV => ⟨?_, ?_⟩⟩
  · exact ha3 D L he (le_trans (le_max_left _ _) hx) hV
  · exact hb3 D L he (le_trans (le_max_right _ _) hx) hV

theorem SzRow.imp {P Q : FC → ∀ D : D7, SizeData₂ D → Prop} (hP : SzRow P)
    (h : ∀ C cD ch D L, Std C → Val C cD ch L → P C D L → Q C D L) : SzRow Q := by
  intro eps h0 h1 C hC
  obtain ⟨a1, ha1⟩ := hP eps h0 h1 C hC
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun D L he hx hV => h C cD ch D L hC hV (ha3 D L he hx hV)⟩

theorem szRow_and_imp :
    (∀ P Q : FC → ∀ D : D7, SizeData₂ D → Prop, SzRow P → SzRow Q → SzRow (fun C D L => P C D L ∧ Q C D L)) ∧
    (∀ P Q : FC → ∀ D : D7, SizeData₂ D → Prop, SzRow P →
      (∀ C cD ch D L, Std C → Val C cD ch L → P C D L → Q C D L) → SzRow Q) :=
  ⟨fun _ _ hP hQ => hP.and hQ, fun _ _ hP h => hP.imp h⟩

end GlobalTheory.EX
end
