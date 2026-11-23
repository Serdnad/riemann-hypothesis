module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientLattice
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealEmbeddingCharacters
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PerpLatticeTransfer

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace FiniteTranslateSets

open NumberField Module

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def Sh (R : ℝ) : Set E :=
  {β | ∃ α : 𝓞 E, (α : E) = (X.den : E) * β ∧ ∀ σ : E →+* ℂ, ‖σ (α : E)‖ ≤ R}

theorem Sh_finite (R : ℝ) (hR : 0 ≤ R) : (Sh X R).Finite := by
  have hS := NumberField.Embeddings.finite_of_norm_le E ℂ R
  have hd : ((X.den : 𝓞 E) : E) ≠ 0 := by exact_mod_cast X.den_ne
  refine (hS.image fun x => x / (X.den : E)).subset ?_
  rintro β ⟨α, hα, hb⟩
  refine ⟨(α : E), ⟨α.isIntegral_coe, hb⟩, ?_⟩
  show (α : E) / (X.den : E) = β
  rw [hα]
  field_simp

def Sz (T : ℝ) : Set ℤ := {n | ((n : ℝ)) ^ 2 ≤ T}

theorem Sz_finite (T : ℝ) : (Sz T).Finite := by
  refine (Set.finite_Icc (-⌈T⌉) ⌈T⌉).subset ?_
  intro n hn
  have hn' : ((n : ℝ)) ^ 2 ≤ T := hn
  have h1 : |n| ≤ n ^ 2 := by
    rcases eq_or_ne n 0 with h | h
    · simp [h]
    · have h0 : 1 ≤ |n| := Int.one_le_abs h
      nlinarith [abs_mul_abs_self n, abs_nonneg n]
  have h2 : ((|n| : ℤ) : ℝ) ≤ T := by
    have h4 : ((|n| : ℤ) : ℝ) ≤ ((n ^ 2 : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h4 ⊢
    linarith
  have h3 : |n| ≤ ⌈T⌉ := by exact_mod_cast h2.trans (Int.le_ceil T)
  exact Set.mem_Icc.mpr ⟨by linarith [neg_abs_le n], by linarith [le_abs_self n]⟩

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def TS (R T : ℝ) : Set ((ι → ι → E) × (Free.ChooseBasisIndex ℤ (𝓞 E) → ι → ι → ℤ)) :=
  {t | ∃ f : Basis ι ℤ X.Λ, ((∀ i j, (HermitianLatticeMaps.ty X f).1 i j ∈ Sh X R) ∧
    ∀ k i j, (HermitianLatticeMaps.ty X f).2 k i j ∈ Sz T) ∧ HermitianLatticeMaps.ty X f = t}

theorem TS_finite (R T : ℝ) (hR : 0 ≤ R) : (TS X (ι := ι) R T).Finite := by
  have hA : (Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => Sh X R).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => Sh_finite X R hR
  have hB : (Set.univ.pi fun _ : Free.ChooseBasisIndex ℤ (𝓞 E) =>
      Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => Sz T).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.Finite.pi fun _ => Sz_finite T
  refine (hA.prod hB).subset ?_
  rintro t ⟨f, ⟨h1, h2⟩, rfl⟩
  exact ⟨fun i _ j _ => h1 i j, fun k _ i _ j _ => h2 k i j⟩

end FiniteTranslateSets

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
  ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (g : ℕ)

lemma cc_mul'' (x y : E) : cc (x * y) = cc x * cc y := map_mul (IsCMField.complexConj E) x y

lemma im_of_fixed {a : E} (ha : cc a = a) (τ : E →+* ℂ) : (τ a).im = 0 := by
  have h : conj (τ a) = τ a := by
    rw [← NumberField.IsCMField.complexEmbedding_complexConj E τ a]
    exact congrArg τ ha
  exact Complex.conj_eq_iff_im.mp h

lemma span_Lc (hg : 0 < g) :
    Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ)) = ⊤ := by
  set Sp := Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ)) with hSp
  have hsub : ∀ b ∈ X.LZ g, kap b ∈ Sp := fun b hb =>
    Submodule.subset_span ((mem_Lc X g).2 ⟨b, hb, rfl⟩)
  have hcr := cr_pos (E := E) g hg
  have hposition : ∀ (i0 k0 : Fin 2), (∀ a : E, cc a = a → IsIntegral ℤ a →
      intersection_update_fsHerm_neg_one i0 k0 (cr (E := E) g • fun τ : X.Ψ => (τ.1 a).re) ∈ Sp) → ∀ p, intersection_update_fsHerm_neg_one i0 k0 p ∈ Sp := by
    intro i0 k0 h p
    have := span_gen X g ((intersection_update_fsHerm_neg_one i0 k0).comp (cr (E := E) g • LinearMap.id)) (fun a ha hai => by
      simpa using h a ha hai) ((cr (E := E) g)⁻¹ • p)
    simpa [smul_smul, inv_mul_cancel₀ hcr.ne'] using this
  have h00 : ∀ p, intersection_update_fsHerm_neg_one 0 0 p ∈ Sp := hposition 0 0 fun a ha hai => by
    have hm := mem_LZ_of X g !![a, 0; 0, 0]
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [ha, RealEmbeddingCharacters.cc_zero'])
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [hai, isIntegral_zero])
    convert hsub _ hm using 1
    funext τ i k
    fin_cases i <;> fin_cases k <;> simp [kap, position_apply, Data.embH, emb_cE]
  have h11 : ∀ p, intersection_update_fsHerm_neg_one 1 1 p ∈ Sp := hposition 1 1 fun a ha hai => by
    have hm := mem_LZ_of X g !![0, 0; 0, a]
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [ha, RealEmbeddingCharacters.cc_zero'])
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [hai, isIntegral_zero])
    convert hsub _ hm using 1
    funext τ i k
    fin_cases i <;> fin_cases k <;> simp [kap, position_apply, Data.embH, emb_cE]
  have h01 : ∀ p, intersection_update_fsHerm_neg_one 0 1 p ∈ Sp := hposition 0 1 fun a ha hai => by
    have hm := mem_LZ_of X g !![0, a; a, 0]
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [ha, RealEmbeddingCharacters.cc_zero'])
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [hai, isIntegral_zero])
    convert hsub _ hm using 1
    funext τ i k
    fin_cases i <;> fin_cases k <;> simp [kap, position_apply, Data.embH, emb_cE, im_of_fixed ha]
  obtain ⟨η, hηcc, hηi, hηne⟩ : ∃ η : E, cc η = -η ∧ IsIntegral ℤ η ∧ η ≠ 0 := by
    have halg : IsAlgebraic ℤ X.ξ0 :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic X.ξ0)
    obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
    refine ⟨k • X.ξ0, ?_, hki, smul_ne_zero hk X.ξ0_ne⟩
    rw [show cc (k • X.ξ0) = k • cc X.ξ0 from map_zsmul _ k _, X.ξ0_im, smul_neg]
  have hre : ∀ τ : E →+* ℂ, (τ η).re = 0 := fun τ => by
    have h := emb_cc' τ η
    rw [hηcc, map_neg] at h
    have := congrArg Complex.re h
    simp at this
    linarith
  have him : ∀ τ : E →+* ℂ, (τ η).im ≠ 0 := fun τ h => by
    have : τ η = 0 := Complex.ext (hre τ) h
    exact hηne ((map_eq_zero τ).1 this)
  have h10 : ∀ p, intersection_update_fsHerm_neg_one 1 0 p ∈ Sp := by
    set D : (X.Ψ → ℝ) →ₗ[ℝ] (X.Ψ → ℝ) :=
      LinearMap.pi fun τ : X.Ψ => (cr (E := E) g * (τ.1 η).im) • LinearMap.proj τ with hD
    have hDapp : ∀ q τ, D q τ = cr (E := E) g * (τ.1 η).im * q τ := fun q τ => by simp [hD]
    have key : ∀ q, (intersection_update_fsHerm_neg_one 1 0).comp D q ∈ Sp := span_gen X g _ fun a ha hai => by
      have hm := mem_LZ_of X g !![0, η * a; -(η * a), 0]
        (fun i k => by
          fin_cases i <;> fin_cases k <;>
            simp [ha, RealEmbeddingCharacters.cc_zero', cc_mul'', hηcc, RealEmbeddingCharacters.cc_neg'])
        (fun i k => by fin_cases i <;> fin_cases k <;> simp [(hηi.mul hai), (hηi.mul hai).neg, isIntegral_zero])
      convert hsub _ hm using 1
      funext τ i k
      rw [LinearMap.comp_apply]
      fin_cases i <;> fin_cases k <;>
        simp [kap, position_apply, Data.embH, emb_cE, hDapp, Complex.mul_re, Complex.mul_im, hre,
          im_of_fixed ha]
      ring
    intro p
    have e : D (fun τ => p τ / (cr (E := E) g * (τ.1 η).im)) = p := by
      funext τ
      rw [hDapp]
      have : cr (E := E) g * (τ.1 η).im ≠ 0 := mul_ne_zero hcr.ne' (him τ.1)
      field_simp [him τ.1]
    have := key (fun τ => p τ / (cr (E := E) g * (τ.1 η).im))
    rwa [LinearMap.comp_apply, e] at this
  refine eq_top_iff.2 fun y _ => ?_
  rw [sum_position y]
  refine Submodule.sum_mem _ fun i0 _ => Submodule.sum_mem _ fun k0 _ => ?_
  fin_cases i0 <;> fin_cases k0
  exacts [h00 _, h01 _, h10 _, h11 _]

theorem exists_basis (hg : 0 < g) : ∃ ω, X.IsLZBasis g ω := by
  have : Fact (0 < g) := ⟨hg⟩
  have : IsZLattice ℝ (Lc X g) := ⟨span_Lc X g hg⟩
  have := ZLattice.module_free ℝ (Lc X g)
  have := ZLattice.module_finite ℝ (Lc X g)
  have hrank : Module.finrank ℤ (Lc X g) = 4 * Fintype.card X.Ψ := by
    rw [ZLattice.rank ℝ (Lc X g), finrank_rfam]
  set bZ := Module.finBasisOfFinrankEq ℤ (Lc X g) hrank
  set eR := bZ.ofZLatticeBasis ℝ (Lc X g)
  have heR : ∀ j, eR j = (bZ j : X.Ψ → Fin 2 → Fin 2 → ℝ) := fun j =>
    bZ.ofZLatticeBasis_apply ℝ (Lc X g) j
  have hthinj : LinearMap.ker (thL : (X.Ψ → Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] _) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro z z' h
    rw [← kap_th z, ← kap_th z']
    exact congrArg kap h
  have hli : LinearIndependent ℝ (fun j => th (eR j)) := eR.linearIndependent.map' thL hthinj
  have hc : ∀ (m : ℤ) (v : X.Ψ → Fin 2 → Fin 2 → ℂ), (m : ℂ) • v = (m : ℝ) • v := fun m v => by
    rw [← Complex.ofReal_intCast, Complex.coe_smul]
  refine ⟨fun j => th (eR j), fun j => ?_, fun b hb => ?_, hli⟩
  · obtain ⟨b, hb, hkb⟩ := (mem_Lc X g).1 (show eR j ∈ Lc X g by rw [heR]; exact (bZ j).2)
    show th (eR j) ∈ X.LZ g
    rw [← hkb, th_kap (herm_of_LZ X g hb)]
    exact hb
  · have hmem : kap b ∈ Lc X g := (mem_Lc X g).2 ⟨b, hb, rfl⟩
    set n := bZ.repr ⟨kap b, hmem⟩
    have h1 := congrArg Subtype.val (bZ.sum_repr ⟨kap b, hmem⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h1
    have hb' : b = ∑ j, (n j : ℂ) • th (eR j) := by
      calc b = thL (kap b) := (th_kap (herm_of_LZ X g hb)).symm
        _ = thL (∑ j, ((n j : ℝ)) • eR j) := by
            congr 1
            rw [← h1]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [heR, Int.cast_smul_eq_zsmul]
        _ = ∑ j, (n j : ℂ) • th (eR j) := by

            rw [map_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul, hc]
            rfl
    refine ⟨n, hb', fun n' hn' => ?_⟩
    have e : ∑ j, (n' j : ℝ) • th (eR j) = ∑ j, (n j : ℝ) • th (eR j) := by
      have := hn'.symm.trans hb'
      simpa only [hc] using this
    have hz := Fintype.linearIndependent_iff.1 hli (fun j => (n' j : ℝ) - n j) (by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [e, sub_self])
    funext j
    have := sub_eq_zero.1 (hz j)
    exact_mod_cast this

end

end ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace QuadraticOffDiagonalBounds

open NumberField Complex
open scoped ComplexConjugate ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem quad_nonneg {M : Fin 2 → Fin 2 → ℂ} (hM : (Matrix.of M).PosSemidef) (v : Fin 2 → ℂ) :
    0 ≤ (∑ i, ∑ k, M i k * v i * conj (v k)).re := by
  have h := hM.dotProduct_mulVec_nonneg (star v)
  have e : dotProduct (star (star v)) ((Matrix.of M).mulVec (star v)) = ∑ i, ∑ k, M i k * v i * conj (v k) := by
    simp only [star_star, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.star_apply, ← starRingEnd_apply]
    ring
  rw [e] at h
  simpa using (Complex.le_def.mp h).1

theorem quad_comb {M : Fin 2 → Fin 2 → ℂ} (hM : (Matrix.of M).PosSemidef) (α β : ℂ)
    (v w : Fin 2 → ℂ) :
    (∑ i, ∑ k, M i k * (α • v + β • w) i * conj ((α • v + β • w) k)).re ≤
      (‖α‖ ^ 2 + ‖β‖ ^ 2) * ((∑ i, ∑ k, M i k * v i * conj (v k)).re +
        (∑ i, ∑ k, M i k * w i * conj (w k)).re) := by
  have hid : (∑ i, ∑ k, M i k * (α • v + β • w) i * conj ((α • v + β • w) k)) +
      (∑ i, ∑ k, M i k * (conj β • v - conj α • w) i * conj ((conj β • v - conj α • w) k)) =
      (α * conj α + β * conj β) * ((∑ i, ∑ k, M i k * v i * conj (v k)) +
        (∑ i, ∑ k, M i k * w i * conj (w k))) := by
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _),
      map_sub, map_mul, Complex.conj_conj]
    ring
  have h0 := quad_nonneg hM (conj β • v - conj α • w)
  have hαβ : α * conj α + β * conj β = ((‖α‖ ^ 2 + ‖β‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hre := congrArg Complex.re hid
  rw [Complex.add_re, hαβ, Complex.re_ofReal_mul, Complex.add_re] at hre
  linarith

theorem offdiag_le {M : Fin 2 → Fin 2 → ℂ} (hM : (Matrix.of M).PosSemidef)
    (h10 : M 1 0 = conj (M 0 1)) : 2 * ‖M 0 1‖ ≤ (M 0 0).re + (M 1 1).re := by
  have d0 := quad_nonneg hM ![1, 0]
  have d1 := quad_nonneg hM ![0, 1]
  simp [Fin.sum_univ_two] at d0 d1
  rcases eq_or_ne (M 0 1) 0 with h0 | h0
  · rw [h0, norm_zero, mul_zero]
    linarith
  · have hn : 0 < ‖M 0 1‖ := norm_pos_iff.mpr h0
    have hs : M 0 1 * conj (M 0 1) = ((‖M 0 1‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    have h := quad_nonneg hM ![conj (M 0 1), -((‖M 0 1‖ : ℝ) : ℂ)]
    have e : (∑ i, ∑ k, M i k * ![conj (M 0 1), -((‖M 0 1‖ : ℝ) : ℂ)] i *
        conj (![conj (M 0 1), -((‖M 0 1‖ : ℝ) : ℂ)] k)) =
        ((‖M 0 1‖ ^ 2 : ℝ) : ℂ) * (M 0 0 + M 1 1) - ((2 * ‖M 0 1‖ ^ 3 : ℝ) : ℂ) := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        map_neg, Complex.conj_conj, Complex.conj_ofReal, h10]
      push_cast
      linear_combination (M 0 0 - 2 * ((‖M 0 1‖ : ℝ) : ℂ)) * hs
    rw [e] at h
    have h' := h
    simp only [Complex.zero_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.add_re,
      Complex.ofReal_re] at h'
    by_contra hlt
    push_neg at hlt
    have hm := mul_lt_mul_of_pos_left hlt (pow_pos hn 2)
    nlinarith

variable {r : ℕ} {X : Data E r}

private theorem Hf_smul_add_smul_right (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) (a b : ℂ) :
    X.Hf z τ u (a • v + b • w) = conj a * X.Hf z τ u v + conj b * X.Hf z τ u w := by
  simp only [Data.Hf, hermC, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul]
  ring

theorem coord {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (f1 f2 e : Fin r → ℂ) (a0 a1 : ℂ)
    (c : ℝ) (he : e = a0 • f1 + a1 • f2) (h1 : c * (X.Hf z τ f1 f1).re = 1)
    (h2 : X.Hf z τ e f1 = 0) (h3 : c * (X.Hf z τ e e).re = 1) :
    ∃ p q : ℂ, q * a0 + p = 0 ∧ q * a1 = 1 ∧ ‖p‖ ^ 2 + ‖q‖ ^ 2 = c * (X.Hf z τ f2 f2).re := by
  have hc : ∀ u w, conj (X.Hf z τ u w) = X.Hf z τ w u := fun u w => UnipotentCoefficientShift.Hf_conj hz τ u w
  have hL : ∀ w, X.Hf z τ e w = a0 * X.Hf z τ f1 w + a1 * X.Hf z τ f2 w := by
    intro w
    rw [← hc w e, he, Hf_smul_add_smul_right, map_add (f := _), map_mul, map_mul, Complex.conj_conj, Complex.conj_conj,
      hc, hc]
  have h2' : a0 * X.Hf z τ f1 f1 + a1 * X.Hf z τ f2 f1 = 0 := by rw [← hL, h2]
  have hee : X.Hf z τ e e = conj a0 * X.Hf z τ e f1 + conj a1 * X.Hf z τ e f2 := by
    have := Hf_smul_add_smul_right z τ e f1 f2 a0 a1
    rwa [← he] at this
  rw [h2, mul_zero, zero_add, hL f2, ← hc f2 f1] at hee
  have hA : conj (X.Hf z τ f1 f1) = X.Hf z τ f1 f1 := hc f1 f1
  have hD : conj (X.Hf z τ f2 f2) = X.Hf z τ f2 f2 := hc f2 f2
  have hB : conj a1 * conj (X.Hf z τ f2 f1) = -(conj a0 * X.Hf z τ f1 f1) := by
    rw [← map_mul, show a1 * X.Hf z τ f2 f1 = -(a0 * X.Hf z τ f1 f1) by linear_combination h2',
      map_neg, map_mul, hA]
  have hee2 : X.Hf z τ e e = -(a0 * conj a0) * X.Hf z τ f1 f1 + (a1 * conj a1) * X.Hf z τ f2 f2 := by
    rw [hee]
    linear_combination a0 * hB
  have hAr : ((X.Hf z τ f1 f1).re : ℂ) = X.Hf z τ f1 f1 := Complex.conj_eq_iff_re.mp hA
  have hDr : ((X.Hf z τ f2 f2).re : ℂ) = X.Hf z τ f2 f2 := Complex.conj_eq_iff_re.mp hD
  have hre : (X.Hf z τ e e).re =
      -(‖a0‖ ^ 2) * (X.Hf z τ f1 f1).re + ‖a1‖ ^ 2 * (X.Hf z τ f2 f2).re := by
    rw [hee2, ← hAr, ← hDr, Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [hre] at h3
  have key : ‖a1‖ ^ 2 * (c * (X.Hf z τ f2 f2).re) = 1 + ‖a0‖ ^ 2 := by
    linear_combination h3 + ‖a0‖ ^ 2 * h1
  have ha1 : a1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at key
    nlinarith [sq_nonneg ‖a0‖]
  have hn : 0 < ‖a1‖ := norm_pos_iff.mpr ha1
  have hcd : c * (X.Hf z τ f2 f2).re = (1 + ‖a0‖ ^ 2) / ‖a1‖ ^ 2 := by
    rw [eq_div_iff (by positivity)]
    linear_combination key
  refine ⟨-a0 * a1⁻¹, a1⁻¹, by ring, inv_mul_cancel₀ ha1, ?_⟩
  rw [hcd, norm_mul, norm_neg, norm_inv]
  field_simp
  ring

end QuadraticOffDiagonalBounds

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
  ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def eps' (p : ℕ) {n : ℕ} (k : Fin n) : ℂ := if (k : ℕ) < p then 1 else -1

section Coord

variable (X : Data E r) (τ : X.Ψ) {n : ℕ} (p : ℕ) (f : Fin n → Fin r → ℂ)
  (hf : ∀ k l, hermC τ.1 X.Gm (f k) (f l) = if k = l then eps' p k else 0)
include hf

end Coord

def uc (X : Data E r) (z0 : Frame X.Ψ r) (ξ : Fin r → E) (τ : X.Ψ) (v : Fin r → ℂ) : Fin r → ℂ :=
  v - (X.Hf z0 τ v (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
    Data.emb τ.1 ξ

section Uc

variable (X : Data E r) {z0 : Frame X.Ψ r} (ξ : Fin r → E) (τ : X.Ψ)

lemma uc_comb (hz : z0 ∈ X.dom) {n : ℕ} (a : Fin n → ℂ) (V : Fin n → Fin r → ℂ) :
    uc X z0 ξ τ (∑ k, a k • V k) = ∑ k, a k • uc X z0 ξ τ (V k) := by
  let L : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := X.ppos z0 τ, map_add' := X.ppos_add z0 τ,
      map_smul' := fun k u => X.ppos_smul_eq z0 τ k u }
  have hHf : ∀ u w, X.Hf z0 τ u w = hermC τ.1 X.Gm ((2 : ℂ) • L u - u) w := fun u w => rfl
  have hsum : X.Hf z0 τ (∑ k, a k • V k) (Data.emb τ.1 ξ) =
      ∑ k, a k * X.Hf z0 τ (V k) (Data.emb τ.1 ξ) := by

    rw [hHf, map_sum]
    simp only [map_smul]
    have e : (2 : ℂ) • ∑ k, a k • L (V k) - ∑ k, a k • V k =
        ∑ k, a k • ((2 : ℂ) • L (V k) - V k) := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_sub, smul_comm]
    rw [e, hermC_sum_left]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hermC_smul_left, hHf]
  unfold uc
  rw [hsum]
  simp only [smul_sub, Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_smul, smul_smul,
    mul_div_assoc]

lemma uc_perp (hξξ : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (v v' : Fin r → ℂ)
    (hv : hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0) (hv' : hermC τ.1 X.Gm v' (Data.emb τ.1 ξ) = 0) :
    hermC τ.1 X.Gm (uc X z0 ξ τ v') (uc X z0 ξ τ v) = hermC τ.1 X.Gm v' v := by
  have hsubR : ∀ u w w' : Fin r → ℂ,
      hermC τ.1 X.Gm u (w - w') = hermC τ.1 X.Gm u w - hermC τ.1 X.Gm u w' := by
    intro u w w'
    simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
  have hsmulR : ∀ (c : ℂ) (u w : Fin r → ℂ),
      hermC τ.1 X.Gm u (c • w) = conj c * hermC τ.1 X.Gm u w := by
    intro c u w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hsym : hermC τ.1 X.Gm (Data.emb τ.1 ξ) v = 0 := by
    have hc : hermC τ.1 X.Gm (Data.emb τ.1 ξ) v = conj (hermC τ.1 X.Gm v (Data.emb τ.1 ξ)) := by

      simp only [hermC, map_sum, map_mul, Complex.conj_conj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [← ReciprocityTheory.ChartRestriction.G.FD.emb_cc, X.Gm_herm]
      ring
    rw [hc, hv, map_zero]
  unfold uc
  simp only [hermC_sub_left, hsubR, hermC_smul_left, hsmulR, hv', hξξ, hsym, mul_zero, sub_zero]

end Uc

end

end ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination
end
