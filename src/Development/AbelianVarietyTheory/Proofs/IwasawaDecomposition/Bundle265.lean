module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle254
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleModule.Isotypic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.FieldsEx

theorem exists_unif_one_mod {R : Type} [CommRing R] [IsDedekindDomain R] (𝔮 : Ideal R) (h𝔮 : 𝔮 ≠ ⊥)
    (v : HeightOneSpectrum R) : ∃ c : R, c ∈ v.asIdeal ∧ c ∉ v.asIdeal ^ 2 ∧
      ∀ w : HeightOneSpectrum R, w ≠ v → w.asIdeal ∣ 𝔮 → c - 1 ∈ w.asIdeal := by
  classical
  have hfin := Ideal.finite_factors h𝔮
  let S : Finset (HeightOneSpectrum R) := hfin.toFinset.erase v
  have hcop : IsCoprime (v.asIdeal ^ 2) (∏ w ∈ S, w.asIdeal) := by
    refine IsCoprime.pow_left (IsCoprime.prod_right fun w hw => ?_)
    have hne : v.asIdeal ≠ w.asIdeal := fun h => (Finset.ne_of_mem_erase hw) (HeightOneSpectrum.ext h).symm
    exact Ideal.isCoprime_iff_sup_eq.2 (v.isMaximal.coprime_of_ne w.isMaximal hne)
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 hcop
  obtain ⟨π, hπ1, hπ2⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
  rw [pow_one] at hπ1
  refine ⟨π * b + a, ?_, ?_, fun w hw hd => ?_⟩
  · exact v.asIdeal.add_mem (v.asIdeal.mul_mem_right _ hπ1) (Ideal.pow_le_self two_ne_zero ha)
  · intro hc
    apply hπ2
    have : π = (π * b + a) + a * (π - 1) := by linear_combination (-π) * hab
    rw [this]
    exact Ideal.add_mem _ hc (Ideal.mul_mem_right _ _ ha)
  · have hS : w ∈ S := Finset.mem_erase.2 ⟨hw, hfin.mem_toFinset.2 hd⟩
    have hb' : b ∈ w.asIdeal := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hS) hb
    have : π * b + a - 1 = b * (π - 1) := by linear_combination hab
    rw [this]
    exact Ideal.mul_mem_right _ _ hb'

theorem exists_gen_pow_prime_one_mod (L : Type) [Field L] [NumberField L] (𝔮 : Ideal (𝓞 L)) (h : ℕ) (h𝔮 : 𝔮 ≠ ⊥)
    (H : ∀ I : Ideal (𝓞 L), I ≠ ⊥ → IsCoprime I 𝔮 →
      ∃ α β : 𝓞 L, RayPair 𝔮 α β ∧ I ^ h * Ideal.span {β} = Ideal.span {α})
    (v : HeightOneSpectrum (𝓞 L)) : ∃ k : Lˣ,
      FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h ∧
      ∀ w : HeightOneSpectrum (𝓞 L), w ≠ v → w.asIdeal ∣ 𝔮 → w.valuation L ((k : L) - 1) < 1 := by
  obtain ⟨c, hc1, hc2, hc3⟩ := exists_unif_one_mod 𝔮 h𝔮 v
  have hc0 : c ≠ 0 := by rintro rfl; exact hc2 (Ideal.zero_mem _)
  obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {c} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hc1)
  have hcJ : c ∈ v.asIdeal * J := hJ ▸ Ideal.mem_span_singleton_self c
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hcJ
    exact hc0 hcJ
  have hcop : IsCoprime J 𝔮 := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hm0 : m ≠ ⊥ := fun h0 => h𝔮 (le_bot_iff.1 (h0 ▸ le_sup_right.trans hle))
    let w : HeightOneSpectrum (𝓞 L) := ⟨m, hm.isPrime, hm0⟩
    have hJm : J ≤ m := le_sup_left.trans hle
    by_cases hw : w = v
    · apply hc2
      have : v.asIdeal = m := hw ▸ rfl
      rw [sq]
      exact Ideal.mul_mono_right (this ▸ hJm) hcJ
    · have h1 : c - 1 ∈ m := hc3 w hw (Ideal.dvd_iff_le.2 (le_sup_right.trans hle))
      have h2 : c ∈ m := hJm (Ideal.le_of_dvd (dvd_mul_left J v.asIdeal) hcJ)
      exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using m.sub_mem h2 h1))
  obtain ⟨α, β, ⟨hα0, hβ0, hα, -, hαβ, -⟩, hE⟩ := H J hJ0 hcop
  have hαL : algebraMap (𝓞 L) L α ≠ 0 := by simpa using hα0
  have hβL : algebraMap (𝓞 L) L β ≠ 0 := by simpa using hβ0
  have hcL : algebraMap (𝓞 L) L c ≠ 0 := by simpa using hc0
  refine ⟨Units.mk0 (algebraMap (𝓞 L) L (c ^ h * β) / algebraMap (𝓞 L) L α)
    (div_ne_zero (by rw [map_mul, map_pow]; exact mul_ne_zero (pow_ne_zero _ hcL) hβL) hαL), ?_, fun w hw hd => ?_⟩
  · have hI : Ideal.span {c ^ h * β} = v.asIdeal ^ h * Ideal.span {α} := by
      rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hJ, mul_pow, mul_assoc, hE]
    have hne : FractionalIdeal.spanSingleton (𝓞 L)⁰ (algebraMap (𝓞 L) L α) ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.2 hαL
    apply mul_right_cancel₀ hne
    rw [Units.val_mk0, FractionalIdeal.spanSingleton_mul_spanSingleton, div_mul_cancel₀ _ hαL,
      ← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_span_singleton, hI,
      FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow]
  · have hle : 𝔮 ≤ w.asIdeal := Ideal.le_of_dvd hd
    have hαw : α ∉ w.asIdeal := fun hm => w.isPrime.ne_top (top_le_iff.1 (by
      rw [← Ideal.isCoprime_iff_sup_eq.1 hα]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hm) hle))
    have hp : c ^ h - 1 ∈ w.asIdeal := by
      have := sub_dvd_pow_sub_pow c 1 h
      rw [one_pow] at this
      obtain ⟨t, ht⟩ := this
      rw [ht]
      exact Ideal.mul_mem_right _ _ (hc3 w hw hd)
    have hm : c ^ h * β - α ∈ w.asIdeal := by
      have : c ^ h * β - α = (c ^ h - 1) * β - (α - β) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hp) (hle hαβ)
    rw [Units.val_mk0, div_sub_one hαL, ← map_sub, map_div₀,
      (w.valuation_eq_one_iff_notMem (K := L)).2 hαw, div_one]
    exact (w.valuation_lt_one_iff_mem (K := L) _).2 hm

end GlobalTheory.Mem.FieldsEx

end
end

section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published

namespace GlobalTheory.Mem.UnramTower

theorem unramIn_trans : ∀ (K L N : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field N] [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L] [IsGalois K N], (∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn L 𝔭) → (∀ P : HeightOneSpectrum (𝓞 L), GlobalTheory.NT.UnramIn N P) → ∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn N 𝔭 := by
  intro K L N _ _ _ _ _ _ _ _ _ _ _ _ hL hN 𝔭 σ hσ
  obtain ⟨Q, hQ, hQo, hσ⟩ := hσ
  have hσ' : ∀ x : 𝓞 N, σ • x - x ∈ Q := fun x => hσ x
  have hPo : (Q.under (𝓞 L)).LiesOver 𝔭.asIdeal := inferInstance
  have hP : (Q.under (𝓞 L)).IsPrime := inferInstance
  have h1 : σ.restrictNormal L = 1 := by
    refine hL 𝔭 _ ⟨Q.under (𝓞 L), hP, hPo, ?_⟩
    intro x
    have hx := hσ' (algebraMap (𝓞 L) (𝓞 N) x)
    have e : algebraMap (𝓞 L) (𝓞 N) ((σ.restrictNormal L) • x) = σ • algebraMap (𝓞 L) (𝓞 N) x := by
      apply RingOfIntegers.ext
      exact AlgEquiv.restrictNormal_commutes σ L (x : L)
    show (σ.restrictNormal L) • x - x ∈ Ideal.comap (algebraMap (𝓞 L) (𝓞 N)) Q
    rw [Ideal.mem_comap, map_sub, e]
    exact hx
  have hfix : ∀ y : L, σ (algebraMap L N y) = algebraMap L N y := by
    intro y
    rw [← AlgEquiv.restrictNormal_commutes σ L y, h1]
    rfl
  let τ : N ≃ₐ[L] N := { σ.toRingEquiv with commutes' := hfix }
  let P : HeightOneSpectrum (𝓞 L) :=
    ⟨Q.under (𝓞 L), hP, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot _⟩
  have h2 : τ = 1 := by
    refine hN P τ ⟨Q, hQ, ⟨rfl⟩, ?_⟩
    intro x
    exact hσ' x
  ext y
  exact DFunLike.congr_fun h2 y

end GlobalTheory.Mem.UnramTower
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.RayNorm

theorem int_norm_pos (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {x : 𝓞 K} (hx : x ≠ 0) :
    0 < Algebra.norm ℤ x := by
  classical
  have hx' : (x : K) ≠ 0 := by exact_mod_cast hx

  have fibre : ∀ w : InfinitePlace K,
      ∏ φ ∈ (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w), φ (x : K) =
        ((Complex.normSq (w.embedding (x : K)) : ℝ) : ℂ) := by
    intro w
    have hset : (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      have key := InfinitePlace.mk_eq_iff (φ := φ) (ψ := w.embedding)
      rw [InfinitePlace.mk_embedding] at key
      rw [key]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · right; rw [← h]; exact (star_star φ).symm
      · rintro (h | h)
        · exact Or.inl h
        · right; rw [h]; exact star_star w.embedding
    have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
      intro h
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w))
        (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm))
    rw [hset, Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj]
  have hprod : (algebraMap ℚ ℂ) (Algebra.norm ℚ (x : K)) =
      ((∏ w : InfinitePlace K, Complex.normSq (w.embedding (x : K)) : ℝ) : ℂ) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ (x : K)]
    rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ (x : K)) _
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])]
    rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ (x : K))]
    push_cast
    exact Finset.prod_congr rfl (fun w _ => fibre w)
  have hpos : (0 : ℝ) < ∏ w : InfinitePlace K, Complex.normSq (w.embedding (x : K)) :=
    Finset.prod_pos fun w _ => Complex.normSq_pos.mpr ((map_ne_zero _).mpr hx')
  have hreal : ((Algebra.norm ℚ (x : K) : ℚ) : ℝ) =
      ∏ w : InfinitePlace K, Complex.normSq (w.embedding (x : K)) := by
    apply Complex.ofReal_injective
    rw [← hprod]
    simp
  have hq : (0 : ℚ) < Algebra.norm ℚ (x : K) := by
    have := hreal ▸ hpos
    exact_mod_cast this
  rw [← Algebra.coe_norm_int] at hq
  exact_mod_cast hq

theorem norm_cast_eq (K : Type) [Field K] [NumberField K] (p : ℕ) {x y : 𝓞 K}
    (h : x - y ∈ Ideal.span {(p : 𝓞 K)}) :
    ((Algebra.norm ℤ x : ℤ) : ZMod p) = ((Algebra.norm ℤ y : ℤ) : ZMod p) := by
  classical
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp h
  have hx : x = y + (p : 𝓞 K) * z := by rw [mul_comm, hz]; ring
  let b := RingOfIntegers.basis K
  have h0 : (Int.castRingHom (ZMod p)).mapMatrix (Algebra.leftMulMatrix b (p : 𝓞 K)) = 0 := by
    rw [map_natCast, map_natCast]
    ext i j
    simp
  have hmat : (Int.castRingHom (ZMod p)).mapMatrix (Algebra.leftMulMatrix b x) =
      (Int.castRingHom (ZMod p)).mapMatrix (Algebra.leftMulMatrix b y) := by
    rw [hx, map_add (f := _), map_mul, map_add (f := _), map_mul, h0, zero_mul, add_zero]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b]
  have e1 := RingHom.map_det (Int.castRingHom (ZMod p)) (Algebra.leftMulMatrix b x)
  have e2 := RingHom.map_det (Int.castRingHom (ZMod p)) (Algebra.leftMulMatrix b y)
  simp only [eq_intCast] at e1 e2
  rw [e1, e2, hmat]

theorem absNorm_modEq_one : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (𝔮 : Ideal (𝓞 K)) (p : ℕ), 𝔮 ≤ Ideal.span {(p : 𝓞 K)} → ∀ (I : Ideal (𝓞 K)) (α β : 𝓞 K), RayPair 𝔮 α β → I * Ideal.span {β} = Ideal.span {α} → Ideal.absNorm I ≡ 1 [MOD p] := by
  intro K _ _ _ 𝔮 p h𝔮 I α β hR hI
  unfold GlobalTheory.NT.RayPair at hR
  obtain ⟨hα, hβ, -, hβq, hαβ, -⟩ := hR

  have hnorm : (Ideal.absNorm I : ℤ) * Algebra.norm ℤ β = Algebra.norm ℤ α := by
    have e := congrArg Ideal.absNorm hI
    rw [map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at e
    have e' : ((Ideal.absNorm I * (Algebra.norm ℤ β).natAbs : ℕ) : ℤ) =
        ((Algebra.norm ℤ α).natAbs : ℤ) := by rw [e]
    push_cast at e'
    rwa [abs_of_pos (int_norm_pos K hβ), abs_of_pos (int_norm_pos K hα)] at e'

  have htop : Ideal.span {β} ⊔ Ideal.span {(p : 𝓞 K)} = ⊤ := by
    rw [Ideal.isCoprime_iff_sup_eq] at hβq
    exact eq_top_mono (sup_le_sup_left h𝔮 _) hβq
  have h1 : (1 : 𝓞 K) ∈ Ideal.span {β} ⊔ Ideal.span {(p : 𝓞 K)} := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp h1
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  have hu : β * u - 1 ∈ Ideal.span {(p : 𝓞 K)} := by
    have e : β * u - 1 = -c := by rw [← hac]; ring
    rw [e]; exact neg_mem hc
  have hinv := norm_cast_eq K p hu
  rw [map_mul, map_one] at hinv
  push_cast at hinv
  have hmod := norm_cast_eq K p (h𝔮 hαβ)
  have key : ((Ideal.absNorm I : ℕ) : ZMod p) * ((Algebra.norm ℤ β : ℤ) : ZMod p) =
      ((Algebra.norm ℤ β : ℤ) : ZMod p) := by
    have e := congrArg (fun t : ℤ => (t : ZMod p)) hnorm
    push_cast at e
    rw [e, hmod]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [Nat.cast_one]
  linear_combination (1 - ((Ideal.absNorm I : ℕ) : ZMod p)) * hinv +
    ((Algebra.norm ℤ u : ℤ) : ZMod p) * key

end GlobalTheory.Mem.RayNorm
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

noncomputable section

namespace GlobalTheory.RepCount

theorem iSup_range_homInto_inf_killed_eq_bot : ∀ (H S0 X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (ρ : Representation ℂ H X) (C : Submodule ℂ X) (I : Set (MonoidAlgebra ℂ H)), σ0.IsIrreducible → killed σ0 I = ⊥ → ((⨆ f ∈ homInto σ0 ρ C, LinearMap.range f) ⊓ killed ρ I : Submodule ℂ X) = ⊥ := by
  intro H S0 X _ _ _ _ _ σ0 ρ C I hirr hk
  haveI hS : IsSimpleModule (MonoidAlgebra ℂ H) σ0.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ0).1 hirr
  let N : Submodule (MonoidAlgebra ℂ H) ρ.asModule :=
    ⨆ (f : S0 →ₗ[ℂ] X) (hf : f ∈ homInto σ0 ρ C), LinearMap.range (modMap f hf.2)
  have hN : N ≤ isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule σ0.asModule := by
    refine iSup₂_le fun f hf => ?_
    rcases LinearMap.injective_or_eq_zero (modMap f hf.2) with hi | h0
    · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
    · rw [h0, LinearMap.range_zero]; exact bot_le
  haveI : IsSemisimpleModule (MonoidAlgebra ℂ H) N :=
    IsSemisimpleModule.of_injective _ (Submodule.inclusion_injective hN)
  have hiso : IsIsotypicOfType (MonoidAlgebra ℂ H) N σ0.asModule :=
    (IsIsotypicOfType.isotypicComponent _ _ _).of_injective _ (Submodule.inclusion_injective hN)
  obtain ⟨ι, ⟨e⟩⟩ := hiso.linearEquiv_finsupp
  rw [eq_bot_iff]
  rintro v ⟨hv1, hv2⟩
  rw [Submodule.mem_bot]
  by_contra hv0
  have hvN : ρ.asModuleEquiv.symm v ∈ N := by
    have hle : (⨆ f ∈ homInto σ0 ρ C, LinearMap.range f : Submodule ℂ X) ≤
        (N.restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap := by
      refine iSup₂_le fun f hf => ?_
      rintro _ ⟨s, rfl⟩
      have hfs : ρ.asModuleEquiv.symm (f s) = modMap f hf.2 (σ0.asModuleEquiv.symm s) := by
        rw [LinearEquiv.symm_apply_eq, modMap_apply, LinearEquiv.apply_symm_apply]
      show ρ.asModuleEquiv.symm (f s) ∈ N
      rw [hfs]
      exact (le_iSup₂ (f := fun (f : S0 →ₗ[ℂ] X) (hf : f ∈ homInto σ0 ρ C) =>
        LinearMap.range (modMap f hf.2)) f hf) ⟨_, rfl⟩
    exact hle hv1
  let w : N := ⟨_, hvN⟩
  have hw : w ≠ 0 := fun h => hv0 (by
    have := congrArg (fun x : N => ρ.asModuleEquiv x.1) h
    simpa [w] using this)
  have hew : e w ≠ 0 := fun h => hw (e.map_eq_zero_iff.1 h)
  obtain ⟨i, hi⟩ : ∃ i, e w i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hew (Finsupp.ext h)
  refine killed_ne_bot (LinearEquiv.refl _ σ0.asModule) hi (fun x hx => ?_) hk
  have hxw : x • w = 0 := by
    apply Subtype.ext
    show x • ρ.asModuleEquiv.symm v = 0
    apply ρ.asModuleEquiv.injective
    rw [Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply, mem_killed.1 hv2 x hx,
      map_zero]
  have := congrArg (fun u => e u i) hxw
  simpa [map_smul, Finsupp.smul_apply] using this

end GlobalTheory.RepCount

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.MultIso

variable {H S0 S X : Type} [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S]
  [AddCommGroup X] [Module ℂ X]

def precomp (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X) (B : Submodule ℂ X)
    (φ : S →ₗ[ℂ] S0) (hφ : ∀ g s, φ (σ g s) = σ0 g (φ s)) : homInto σ0 ρ B →ₗ[ℂ] homInto σ ρ B where
  toFun T := ⟨T.1 ∘ₗ φ, fun s => T.2.1 (φ s), fun g s => by
    show T.1 (φ (σ g s)) = ρ g (T.1 (φ s))
    rw [hφ]; exact T.2.2 g (φ s)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rank_homInto_of_asModule (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X)
    (B : Submodule ℂ X) (e : σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) :
    Module.rank ℂ (homInto σ ρ B) = Module.rank ℂ (homInto σ0 ρ B) := by
  let φ : S →ₗ[ℂ] S0 :=
    { toFun := fun s => σ0.asModuleEquiv (e (σ.asModuleEquiv.symm s))
      map_add' := fun a b => by simp
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        rw [show e (c • σ.asModuleEquiv.symm a) = c • e (σ.asModuleEquiv.symm a) from
          LinearMap.map_smul_of_tower e.toLinearMap c _, map_smul] }
  let ψ : S0 →ₗ[ℂ] S :=
    { toFun := fun s => σ.asModuleEquiv (e.symm (σ0.asModuleEquiv.symm s))
      map_add' := fun a b => by simp
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        rw [show e.symm (c • σ0.asModuleEquiv.symm a) = c • e.symm (σ0.asModuleEquiv.symm a) from
          LinearMap.map_smul_of_tower e.symm.toLinearMap c _, map_smul] }
  have hφψ : ∀ s, φ (ψ s) = s := fun s => by simp [φ, ψ]
  have hψφ : ∀ s, ψ (φ s) = s := fun s => by simp [φ, ψ]
  have φeq : ∀ g s, φ (σ g s) = σ0 g (φ s) := fun g s => by
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]
  have ψeq : ∀ g s, ψ (σ0 g s) = σ g (ψ s) := fun g s => by
    simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]
  let E : homInto σ0 ρ B ≃ₗ[ℂ] homInto σ ρ B :=
    { precomp σ0 σ ρ B φ φeq with
      invFun := precomp σ σ0 ρ B ψ ψeq
      left_inv := fun T => Subtype.ext (LinearMap.ext fun s => by
        show T.1 (φ (ψ s)) = T.1 s
        rw [hφψ])
      right_inv := fun T => Subtype.ext (LinearMap.ext fun s => by
        show T.1 (ψ (φ s)) = T.1 s
        rw [hψφ]) }
  exact E.rank_eq.symm

theorem homInto_iSup_range (σ0 : Representation ℂ H S0) (ρ : Representation ℂ H X) (C : Submodule ℂ X) :
    homInto σ0 ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) = homInto σ0 ρ C := by
  have hle : (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) ≤ C := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨s, rfl⟩
    exact hg.1 s
  ext f
  refine ⟨fun hf => ⟨fun s => hle (hf.1 s), hf.2⟩, fun hf => ⟨fun s => ?_, hf.2⟩⟩
  exact (le_iSup₂_of_le f hf le_rfl : LinearMap.range f ≤ ⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) ⟨s, rfl⟩

theorem rank_homInto_iSup_range : ∀ (H S0 S X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S]
    [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X)
    (C : Submodule ℂ X), Nonempty (σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) →
    Module.rank ℂ (homInto σ ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g)) = Module.rank ℂ (homInto σ0 ρ C) := by
  intro H S0 S X _ _ _ _ _ _ _ σ0 σ ρ C ⟨e⟩
  rw [rank_homInto_of_asModule σ0 σ ρ _ e, homInto_iSup_range]

end GlobalTheory.MultIso
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical


theorem _root_.GlobalTheory.T.fullFlagBundle_point_at_genericLift_image : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ r : Sp Y₂.Fn ⟶ Y₁.X, r ≫ f₁ = (ratOf Y₂).pt ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (r ≫ f₁) r (ratOf Y₂).pt → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (p' : Sp K ⟶ Y₂.X), p (IsLocalRing.closedPoint K) = r (IsLocalRing.closedPoint Y₂.Fn) → p ≫ f₁ = p' ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p p' → p' (IsLocalRing.closedPoint K) = genericPoint Y₂.X := by
  first | exact @GlobalTheory.FlagBundle.conclusion | exact GlobalTheory.FlagBundle.conclusion | (intros; apply GlobalTheory.FlagBundle.conclusion <;> assumption)
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

theorem _root_.GlobalTheory.T.finiteDimensional_of_bounded_Korbit_dimension : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (U : Submodule ℂ H) (M : ℕ), (∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ M ∧ u ∈ S ∧ IsKStableOn ε σ S) → FiniteDimensional ℂ U := by
  first | exact @GlobalTheory.TypeSum.finiteDimensional_of_bounded_orbits | exact GlobalTheory.TypeSum.finiteDimensional_of_bounded_orbits | (intros; apply GlobalTheory.TypeSum.finiteDimensional_of_bounded_orbits <;> assumption)
end
