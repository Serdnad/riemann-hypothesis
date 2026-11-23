module

public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.HermitianLattices.Bundle001
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Data.Fintype.Perm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle106
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle108
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle107
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.FieldTheory.Galois.Infinite
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.valuation_pow_apply_div_sub_one_lt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (x : Ω) (hx : x ≠ 0) (i : ℕ) :
    A.valuation ((σ ^ i) x / x - 1) < 1 := by
  induction i with
  | zero => simp [hx]
  | succ i ih =>
    have hy0 : (σ ^ i) x ≠ 0 := (map_ne_zero (σ ^ i)).2 hx
    have hle : A.valuation ((σ ^ i) x / x) ≤ 1 := by
      have e : (σ ^ i) x / x = ((σ ^ i) x / x - 1) + 1 := by ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le ih.le (by simp))
    have key : (σ ^ (i + 1)) x / x - 1 =
        (σ ((σ ^ i) x) / (σ ^ i) x - 1) * ((σ ^ i) x / x) + ((σ ^ i) x / x - 1) := by
      rw [pow_succ', AlgEquiv.mul_apply]
      field_simp
      ring
    rw [key]
    apply Valuation.map_add_lt _ _ ih
    rw [map_mul]
    calc A.valuation (σ ((σ ^ i) x) / (σ ^ i) x - 1) * A.valuation ((σ ^ i) x / x)
        ≤ A.valuation (σ ((σ ^ i) x) / (σ ^ i) x - 1) * 1 := by gcongr
      _ < 1 := by simpa using hσ _ hy0


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.mem_of_wild_of_pow_mem_open_normal :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ (H : Subgroup (_root_.Formalism.ConjugateSelfDual.G E Ω)), H.Normal → IsOpen (H : Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) → ∀ (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) (n : ℕ), ((n : ℕ) : 𝓞 E) ∉ v.asIdeal → (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → σ ^ n ∈ H → σ ∈ H := by
  intro E Ω _ _ _ _ _ A v hA H _ hH σ n hn hσ hpow
  change Ω ≃ₐ[E] Ω at σ
  have hv : A.valuation (n : Ω) = 1 := by
    have h1 : ¬ A.valuation (n : Ω) < 1 := by
      intro h
      apply hn
      rw [← hA]
      simpa using h
    have h2 : A.valuation (n : Ω) ≤ 1 := by
      simpa using A.valuation_le_one (n : A)
    exact le_antisymm h2 (not_lt.1 h1)
  have hn0 : (n : Ω) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  obtain ⟨s, hsdef⟩ : ∃ s : Ω → Ω, ∀ z, s z = ∑ i ∈ Finset.range n, (σ ^ i) z :=
    ⟨_, fun _ => rfl⟩
  have hs : ∀ z, (σ ^ n) z = z → σ (s z) = s z := by
    intro z hz
    have e1 := Finset.sum_range_succ (fun i => (σ ^ i) z) n
    have e2 := Finset.sum_range_succ' (fun i => (σ ^ i) z) n
    simp only [hz, pow_zero, AlgEquiv.one_apply] at e1 e2

    rw [hsdef, map_sum]
    have e3 : ∑ i ∈ Finset.range n, σ ((σ ^ i) z) = ∑ i ∈ Finset.range n, (σ ^ (i + 1)) z :=
      Finset.sum_congr rfl fun i _ => by rw [pow_succ', AlgEquiv.mul_apply]
    rw [e3]
    exact add_right_cancel (e2.symm.trans e1)
  have hk : ∀ w, σ w = w → ∀ k : ℕ, (σ ^ k) w = w := by
    intro w hw k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hw]
  have hne : ∀ z, z ≠ 0 → s z ≠ 0 := by
    intro z hz h0
    have hlt : A.valuation (∑ i ∈ Finset.range n, ((σ ^ i) z / z - 1)) < 1 :=
      Valuation.map_sum_lt _ one_ne_zero
        (fun i _ => _root_.GlobalTheory.valuation_pow_apply_div_sub_one_lt A σ hσ z hz i)
    have e : ∑ i ∈ Finset.range n, ((σ ^ i) z / z - 1) = s z / z - n := by
      simp [hsdef, Finset.sum_sub_distrib, Finset.sum_div]
    rw [e, h0, zero_div, zero_sub, Valuation.map_neg, hv] at hlt
    exact lt_irrefl _ hlt
  have hfix : ∀ y : Ω, (σ ^ n) y = y → σ y = y := by
    intro y hy
    have hsy := hs y hy
    have h1 : ∀ i, (σ ^ i) ((n : Ω) * y - s y) = n * (σ ^ i) y - s y := fun i => by
      rw [map_sub, map_mul, map_natCast, hk (s y) hsy i]
    have hsz : s ((n : Ω) * y - s y) = 0 := by
      rw [hsdef, Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← hsdef, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_self]
    have hz : (n : Ω) * y - s y = 0 := by
      by_contra h
      exact hne _ h hsz
    have hy' : s y = n * y := (sub_eq_zero.1 hz).symm
    have e := congrArg σ hy'
    rw [hsy, map_mul, map_natCast, hy'] at e
    exact (mul_left_cancel₀ hn0 e).symm
  haveI : IsGalois E Ω := inferInstance
  have hcl : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) := H.isClosed_of_isOpen hH
  have hH' := InfiniteGalois.fixingSubgroup_fixedField (⟨H, hcl⟩ : ClosedSubgroup (Ω ≃ₐ[E] Ω))
  have hmem : σ ∈ (IntermediateField.fixedField H).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    apply hfix
    exact (IntermediateField.mem_fixedField_iff H y).1 hy _ hpow
  rw [hH'] at hmem
  exact hmem

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace GlobalTheory.WildInertiaChar

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]

theorem wild_pow (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω)
    (h : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (i : ℕ) :
    ∀ y : Ω, y ≠ 0 → A.valuation ((σ ^ i) y / y - 1) < 1 := by
  induction i with
  | zero => intro y hy; simp [hy]
  | succ i ih =>
    intro y hy
    have hz : (σ ^ i) y ≠ 0 := (map_ne_zero (σ ^ i)).mpr hy
    have h1 := h _ hz
    have h2 := ih y hy
    have e : (σ ^ (i + 1)) y / y - 1
        = (σ ((σ ^ i) y) / (σ ^ i) y - 1) * ((σ ^ i) y / y - 1)
          + ((σ ((σ ^ i) y) / (σ ^ i) y - 1) + ((σ ^ i) y / y - 1)) := by
      rw [pow_succ', AlgEquiv.mul_apply]
      field_simp
      ring
    rw [e]
    refine A.valuation.map_add_lt ?_ (A.valuation.map_add_lt h1 h2)
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' h2.le) h1

theorem fixed_of_pow_fixed (A : ValuationSubring Ω) (τ : Ω ≃ₐ[E] Ω)
    (h : ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) (k : ℕ)
    (hk : ¬ A.valuation (k : Ω) < 1) (x : Ω) (hx : (τ ^ k) x = x) : τ x = x := by
  by_contra hne
  have hd : τ x - x ≠ 0 := sub_ne_zero.mpr hne
  have hs : ∑ i ∈ Finset.range k, (τ ^ i) (τ x - x) = 0 := by
    have : ∀ i, (τ ^ i) (τ x - x) = (τ ^ (i + 1)) x - (τ ^ i) x := by
      intro i; rw [map_sub, pow_succ, AlgEquiv.mul_apply]
    simp_rw [this]
    rw [Finset.sum_range_sub (fun i => (τ ^ i) x), hx]
    simp
  have e : (k : Ω) = - ∑ i ∈ Finset.range k, ((τ ^ i) (τ x - x) / (τ x - x) - 1) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hs]
    simp
  apply hk
  rw [e, Valuation.map_neg]
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => wild_pow A τ h i _ hd

theorem trivial_on_wild (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (l : ℕ)
    (hl : l.Prime) (hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (hA : IsPlaceOver A v)
    (Γ : Type) [CommGroup Γ] (ψ : G E Ω →* Γ) (hop : IsOpen (ψ.ker : Set (G E Ω)))
    (hψ : ∀ g, ∃ n : ℕ, ψ g ^ (l ^ n) = 1) (σ : G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : ψ σ = 1 := by
  have hvl : ¬ A.valuation (l : Ω) < 1 := by
    intro h
    apply hlv
    rw [← hA]
    simpa using h
  have hvl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp
    (hop.mem_nhds (one_mem ψ.ker))
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have hidx : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  have hτ : σ ^ m ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro x hx
    refine fixed_of_pow_fixed A (σ ^ m) (wild_pow A σ hσ m) (l ^ a) ?_ x ?_
    · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
    · rw [← pow_mul, mul_comm]; exact hmem x hx
  have h1 : ψ σ ^ m = 1 := by
    rw [← map_pow]; exact hsub hτ
  obtain ⟨n, hn⟩ := hψ σ
  have hc : Nat.Coprime (l ^ n) m := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hm).pow_left n
  have := (pow_gcd_eq_one (a := ψ σ) (m := l ^ n) (n := m)).mpr ⟨hn, h1⟩
  rwa [hc, pow_one] at this

end GlobalTheory.WildInertiaChar
end

section

open Formalism.BasicNotions NumberField

namespace GlobalTheory

theorem exists_frames_normAt_eq_norm : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (e : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (c : Module.Basis (Fin n) ℂ W) (L : Submodule (𝓞 K) (Fin n → K)), ∃ X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ v, IsUnit (X v).det) ∧ ∀ x : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X (InfinitePlace.mk e) x = ‖∑ i, e (x i) • c i‖ := by
  intro K _ _ _ e W _ _ n c _
  have : FiniteDimensional ℂ W := Module.Finite.of_basis c
  have hn : Module.finrank ℂ W = n := by simpa using Module.finrank_eq_card_basis c
  let o : OrthonormalBasis (Fin n) ℂ W := (stdOrthonormalBasis ℂ W).reindex (finCongr hn)
  set A : Matrix (Fin n) (Fin n) ℂ := o.toBasis.toMatrix c with hA
  have hAu : IsUnit A.det :=
    Matrix.isUnit_det_of_right_inverse (o.toBasis.toMatrix_mul_toMatrix_flip c)
  have key : ∀ y : Fin n → ℂ, Formalism.HermitianLatticesTheory.cnorm (A.mulVec y) = ‖∑ i, y i • c i‖ := by
    intro y
    rw [← o.repr.norm_map, EuclideanSpace.norm_eq]
    unfold Formalism.HermitianLatticesTheory.cnorm
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    simp [hA, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, mul_comm]
  rcases InfinitePlace.embedding_mk_eq e with h | h
  · refine ⟨fun _ => A⁻¹, fun _ => Matrix.isUnit_nonsing_inv_det A hAu, fun x => ?_⟩
    rw [← key]
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
    rw [Matrix.nonsing_inv_nonsing_inv A hAu]
    congr 2
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt, h]
  · have hBu : IsUnit (A.map (starRingEnd ℂ)).det := by
      have := hAu.map (starRingEnd ℂ)
      rwa [RingHom.map_det] at this
    refine ⟨fun _ => (A.map (starRingEnd ℂ))⁻¹, fun _ => Matrix.isUnit_nonsing_inv_det _ hBu,
      fun x => ?_⟩
    rw [← key]
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
    rw [Matrix.nonsing_inv_nonsing_inv _ hBu]
    unfold Formalism.HermitianLatticesTheory.cnorm
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [← RCLike.norm_conj (A.mulVec (fun i => e (x i)) j)]
    congr 1
    simp [Formalism.HermitianLatticesTheory.vecAt, h, Matrix.mulVec, dotProduct]

end GlobalTheory
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem exists_cocycle_extension_of_neg_action : ∀ (G : Type) [Group G] (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (ρ : G → V →ₗ[R] V), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → IsUnit (2 : R) → ∀ (S : Submodule R V), (∀ g, ∀ v ∈ S, ρ g v ∈ S) → ∀ (Δ : Subgroup G), Δ.Normal → (∀ δ ∈ Δ, ∀ v, ρ δ v = v) → ∀ c : G, (∀ v ∈ S, ρ c v = -v) → (∀ g, c * g * c⁻¹ * g⁻¹ ∈ Δ) → ∀ φ : G → V, (∀ δ ∈ Δ, φ δ ∈ S) → (∀ δ ∈ Δ, ∀ δ' ∈ Δ, φ (δ * δ') = φ δ + φ δ') → (∀ g, ∀ δ ∈ Δ, ρ g (φ (g * δ * g⁻¹)) = φ δ) → ∃ z : G → V, (∀ g, z g ∈ S) ∧ (∀ g h, z (g * h) = ρ h (z g) + z h) ∧ ∀ δ ∈ Δ, z δ = φ δ := by
  intro G _ R _ V _ _ ρ hmul hone h2 S hS Δ hΔ hΔtriv c hc hk φ hφS hφadd hφinv
  obtain ⟨u, hu⟩ := h2
  have hinv : ∀ g v, ρ g (ρ g⁻¹ v) = v := by
    intro g v; rw [← hmul, inv_mul_cancel, hone]
  have hconj : ∀ g, ∀ δ ∈ Δ, φ (g * δ * g⁻¹) = ρ g⁻¹ (φ δ) := by
    intro g δ hδ
    rw [← hφinv g δ hδ, ← hmul, mul_inv_cancel, hone]
  have hkmul : ∀ g h : G, c * (g * h) * c⁻¹ * (g * h)⁻¹
      = (c * g * c⁻¹ * g⁻¹) * (g * (c * h * c⁻¹ * h⁻¹) * g⁻¹) := by
    intro g h; group
  have hw : ∀ g h : G, ρ (g * h) (φ (c * (g * h) * c⁻¹ * (g * h)⁻¹))
      = ρ h (ρ g (φ (c * g * c⁻¹ * g⁻¹))) + ρ h (φ (c * h * c⁻¹ * h⁻¹)) := by
    intro g h
    rw [hkmul, hφadd _ (hk g) _ (hΔ.conj_mem _ (hk h) g), hconj g _ (hk h), hmul,
      map_add, map_add, hinv]
  have h1 : φ 1 = 0 := by
    have := hφadd 1 Δ.one_mem 1 Δ.one_mem
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hneg : ∀ δ ∈ Δ, φ δ⁻¹ = -φ δ := by
    intro δ hδ
    have := hφadd δ hδ δ⁻¹ (Δ.inv_mem hδ)
    rw [mul_inv_cancel, h1] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  refine ⟨fun g => -(↑u⁻¹ : R) • ρ g (φ (c * g * c⁻¹ * g⁻¹)), ?_, ?_, ?_⟩
  · intro g
    exact S.smul_mem _ (hS g _ (hφS _ (hk g)))
  · intro g h
    simp only
    rw [hw, smul_add, map_smul]
  · intro δ hδ
    simp only
    have hcδ : c * δ * c⁻¹ ∈ Δ := hΔ.conj_mem _ hδ c
    have hc' : φ (c * δ * c⁻¹) = -φ δ := by
      have e1 := hφinv c δ hδ
      rw [hc _ (hφS _ hcδ)] at e1
      rw [← e1, neg_neg]
    rw [hΔtriv δ hδ, hφadd _ hcδ _ (Δ.inv_mem hδ), hc', hneg δ hδ,
      show -φ δ + -φ δ = -((2 : R) • φ δ) by rw [two_smul, neg_add],
      smul_neg, neg_smul, neg_neg, smul_smul, ← hu, Units.inv_mul, one_smul]

end GlobalTheory.KZ.H3
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.finrank_range_le_sum_three_complements : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (P a b : Module.End ℂ M), Module.finrank ℂ (LinearMap.range P) ≤ Module.finrank ℂ (LinearMap.range (a * b * P)) + Module.finrank ℂ (LinearMap.range ((1 - a) * P)) + Module.finrank ℂ (LinearMap.range ((1 - b) * P)) := by
  first | exact @GlobalTheory.BadShare.finrank_range_le_three | exact GlobalTheory.BadShare.finrank_range_le_three | (intros; apply GlobalTheory.BadShare.finrank_range_le_three <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.representation_root_subgroup_exchange : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (B X Y : Subgroup G) (χ : G → ℂ), (∀ x ∈ X, x ∈ B → x = 1) → (∀ b ∈ B, ∀ x ∈ X, ∃ x' ∈ X, ∃ b' ∈ B, b * x = x' * b' ∧ χ b' = χ b) → (∀ x ∈ X, ∀ y ∈ Y, y⁻¹ * x⁻¹ * y * x ∈ B) → (∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → ∃ y ∈ Y, χ (y⁻¹ * x⁻¹ * y * x) ≠ χ (y⁻¹ * x'⁻¹ * y * x')) → ∀ (n : ℕ) (v : Fin n → M), LinearIndependent ℂ v → (∀ i, (∀ b ∈ B, ρ b (v i) = χ b • v i) ∧ ∀ y ∈ Y, ρ y (v i) = v i) → ∃ w : Fin n → M, LinearIndependent ℂ w ∧ ∀ i, (∀ b ∈ B, ρ b (w i) = χ b • w i) ∧ ∀ x ∈ X, ρ x (w i) = w i := by
  first | exact @GlobalTheory.BadShare.root_exchange | exact GlobalTheory.BadShare.root_exchange | (intros; apply GlobalTheory.BadShare.root_exchange <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.factorial_le_two_mul_card_perm_with_fixedPoint : ∀ (α : Type) [Fintype α] [DecidableEq α], Nonempty α → (Fintype.card α).factorial ≤ 2 * (Finset.univ.filter fun σ : Equiv.Perm α => ∃ i, σ i = i).card := by
  first | exact @GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed | exact GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed | (intros; apply GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.exists_algEquiv_map_valuationSubring_over_prime : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A B : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ((p : ℕ) : Ω) ∈ B.nonunits → ∃ σ : Ω ≃ₐ[ℚ] Ω, ∀ x, σ x ∈ B ↔ x ∈ A := by
  first | exact @GlobalTheory.ValConjClosure.exists_conj_over_prime | exact GlobalTheory.ValConjClosure.exists_conj_over_prime | (intros; apply GlobalTheory.ValConjClosure.exists_conj_over_prime <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.gauss_valuation_extension_unique_bertiniNoether : ∀ {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra.IsAlgebraic ℚ F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W₁ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W₁.valuation (Polynomial.aeval t P) = 1)) → ((∀ a : F, algebraMap F L a ∈ W₂ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W₂.valuation (Polynomial.aeval t P) = 1)) → W₁ = W₂ := by
  first | exact @GlobalTheory.BertiniNoether.gauss_extension_unique | exact GlobalTheory.BertiniNoether.gauss_extension_unique | (intros; apply GlobalTheory.BertiniNoether.gauss_extension_unique <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_lagrange_resolvent_of_pGroup_faithful : ∀ (L : Type) [Field L] (p : ℕ), p.Prime → ∀ (G : Type) [Group G] [MulSemiringAction G L] [Finite G] [Nontrivial G] [FaithfulSMul G L], IsPGroup p G → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ∃ (σ : G) (α : L), α ≠ 0 ∧ σ • α = ζ * α ∧ ∀ g : G, g • α ^ p = α ^ p := by
  first | exact @GlobalTheory.AlmostEt.exists_lagrange_resolvent | exact GlobalTheory.AlmostEt.exists_lagrange_resolvent | (intros; apply GlobalTheory.AlmostEt.exists_lagrange_resolvent <;> assumption)
end

section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.card_perm_partition_parts_mul_centralizer : ∀ (N : ℕ) (μ : Multiset ℕ), (∀ d ∈ μ, 0 < d) → μ.sum = N → (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ).card * ∏ d ∈ μ.toFinset, (d ^ μ.count d * (μ.count d).factorial) = N.factorial := by
  first | exact @GlobalTheory.BadShare.card_perm_partition_parts_mul | exact GlobalTheory.BadShare.card_perm_partition_parts_mul | (intros; apply GlobalTheory.BadShare.card_perm_partition_parts_mul <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory

theorem homogeneous_poly_coeff_eq_zero (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    (htf : ∀ (c : ℤ_[l]) (x : M), c ≠ 0 → c • x = 0 → x = 0) (w : ℕ) (c : Fin (w + 1) → M)
    (hv : ∀ u : Fin 2 → ℤ_[l], ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i = 0) :
    c = 0 := by
  set V : Matrix (Fin (w + 1)) (Fin (w + 1)) ℤ_[l] := Matrix.vandermonde (fun t : Fin (w + 1) => ((t : ℕ) : ℤ_[l])) with hVdef
  have hrow : ∀ t : Fin (w + 1), ∑ i, V t i • c i = 0 := by
    intro t
    have := hv ![((t : ℕ) : ℤ_[l]), 1]
    simpa [hVdef, Matrix.vandermonde_apply] using this
  have hdet : V.det ≠ 0 := by
    rw [hVdef, Matrix.det_vandermonde_ne_zero_iff]
    intro a b hab
    apply Fin.ext
    have hab' : ((a : ℕ) : ℤ_[l]) = ((b : ℕ) : ℤ_[l]) := hab
    exact_mod_cast hab'
  have key : ∀ j, V.det • c j = 0 := by
    intro j
    have h1 : ∑ t, V.adjugate j t • ∑ i, V t i • c i = 0 := by simp [hrow]
    have h2 : ∑ t, V.adjugate j t • ∑ i, V t i • c i = ∑ i, (V.adjugate * V) j i • c i := by
      simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
    rw [h2, Matrix.adjugate_mul] at h1
    simpa [Matrix.smul_apply, Matrix.one_apply, ite_smul, Finset.sum_ite_eq] using h1
  funext j
  exact htf _ _ hdet (key j)

end GlobalTheory
end
