module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle076
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraZmodTorsorBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle105
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle111
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle172
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
import Mathlib.Analysis.Fourier.Notation
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.kummerAlgebra_zmod_torsor_bijective : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) [NeZero q] (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B), IsUnit (q : B) → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → ∀ (ζ : B) (hζ : ζ ^ q = 1), (∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) → Function.Bijective (Algebra.TensorProduct.productMap (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun _ => AlgHom.id B (GlobalTheory.KummerAlg.Alg φ))) (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun g => (GlobalTheory.KummerAlg.act φ ζ hζ g).toAlgHom))) := by
  first | exact @GlobalTheory.KummerTorsor.bijective | exact GlobalTheory.KummerTorsor.bijective | (intros; apply GlobalTheory.KummerTorsor.bijective <;> assumption)
end

section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitaryStandardLattice_form_complexStructure_baseChange_pos : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ), (S.map (Int.cast : ℤ → ℝ)).PosDef → ∀ x : ℝ ⊗[ℤ] GlobalTheory.UnitaryStd.Lat ρ g, x ≠ 0 → 0 < (GlobalTheory.UnitaryStd.form ρ g S).baseChange ℝ ((GlobalTheory.UnitaryStd.cx ρ g).baseChange ℝ x) x := by
  first | exact @GlobalTheory.UnitaryStd.form_cx_baseChange_pos | exact GlobalTheory.UnitaryStd.form_cx_baseChange_pos | (intros; apply GlobalTheory.UnitaryStd.form_cx_baseChange_pos <;> assumption)
end

section

noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.LocMatrix

variable (ℓ : ℕ) [Fact ℓ.Prime] (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B]
  [Algebra ℚ B] [IsScalarTower ℚ F B]

theorem cenMap_tmul (q : ℚ_[ℓ]) (f : F) : cenMap ℓ F B (q ⊗ₜ f) = q ⊗ₜ algebraMap F B f := by
  simp [cenMap]

theorem cenMap_mem (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ)
    {a : ℚ_[ℓ] ⊗[ℚ] F} (ha : a ∈ cenOrder ℓ F) : cenMap ℓ F B a ∈ locOrder ℓ Λ := by
  have h : cenOrder ℓ F ≤ (locOrder ℓ Λ).comap ((cenMap ℓ F B).restrictScalars ℤ_[ℓ]) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨a, rfl⟩
    show cenMap ℓ F B _ ∈ locOrder ℓ Λ
    rw [cenMap_tmul]
    exact Algebra.subset_adjoin ⟨_, hΛ a, rfl⟩
  exact h ha

theorem cenMap_commute (a : ℚ_[ℓ] ⊗[ℚ] F) (y : ℚ_[ℓ] ⊗[ℚ] B) : Commute (cenMap ℓ F B a) y := by
  first
  | exact @_root_.GlobalTheory.CentralizerMapTensor.commute_cenMap
  | exact _root_.GlobalTheory.CentralizerMapTensor.commute_cenMap
  | (apply _root_.GlobalTheory.CentralizerMapTensor.commute_cenMap <;> assumption)
  | (intros; apply _root_.GlobalTheory.CentralizerMapTensor.commute_cenMap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CentralizerMapTensor.commute_cenMap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CentralizerMapTensor.commute_cenMap ..)

def cenIncl (Λ : Subring B) (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) :
    cenOrder ℓ F →ₐ[ℤ_[ℓ]] locOrder ℓ Λ :=
  (((cenMap ℓ F B).restrictScalars ℤ_[ℓ]).comp (cenOrder ℓ F).val).codRestrict (locOrder ℓ Λ)
    (fun a => cenMap_mem ℓ F B Λ hΛ a.2)

theorem coe_cenIncl (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) (a : cenOrder ℓ F) :
    (cenIncl ℓ F B Λ hΛ a : ℚ_[ℓ] ⊗[ℚ] B) = cenMap ℓ F B a := rfl

def cenAlgebra (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) :
    Algebra (cenOrder ℓ F) (locOrder ℓ Λ) :=
  (cenIncl ℓ F B Λ hΛ).toRingHom.toAlgebra' fun a x => Subtype.ext (cenMap_commute ℓ F B a x)

theorem algebraMap_cenAlgebra (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) (a : cenOrder ℓ F) :
    letI := cenAlgebra ℓ F B Λ hΛ
    algebraMap (cenOrder ℓ F) (locOrder ℓ Λ) a = cenIncl ℓ F B Λ hΛ a := rfl

theorem isScalarTower_cenAlgebra (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) :
    letI := cenAlgebra ℓ F B Λ hΛ
    IsScalarTower ℤ_[ℓ] (cenOrder ℓ F) (locOrder ℓ Λ) := by
  letI := cenAlgebra ℓ F B Λ hΛ
  exact IsScalarTower.of_algebraMap_eq fun r => ((cenIncl ℓ F B Λ hΛ).commutes r).symm

end GlobalTheory.LocMatrix
end
end

section

open NumberField

theorem _root_.GlobalTheory.T.latticeDeterminantSpan_span_eq_generator_dets : ∀ {F : Type} [Field F] [NumberField F] (p : ℕ) (S : Set (Fin p → F)),
    GlobalTheory.IdxTensor.dets F p (Submodule.span (𝓞 F) S) =
      Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} := by
  first | exact @GlobalTheory.IdxTensor.dets_span_eq | exact GlobalTheory.IdxTensor.dets_span_eq | (intros; apply GlobalTheory.IdxTensor.dets_span_eq <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.span_scaled_mapped_row_dets_eq_pow_mul_span : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K), (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) → ∀ (p : ℕ)
    (𝔟 : Submodule (𝓞 K) K) (Λ : Submodule (𝓞 E) (Fin p → E)),
    Submodule.span (𝓞 K) {d | ∃ y : Fin p → Fin p → K,
        (∀ i, y i ∈ {x : Fin p → K | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) ∧ d = (Matrix.of y).det} =
      𝔟 ^ p * Submodule.span (𝓞 K) (τE '' GlobalTheory.IdxTensor.dets E p Λ) := by
  first | exact @GlobalTheory.span_twistDets_eq | exact GlobalTheory.span_twistDets_eq | (intros; apply GlobalTheory.span_twistDets_eq <;> assumption)
end

section

open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.GaussExt.UnitIdx

variable (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]

theorem aeval_neg_ii : aeval (-ii F) (X ^ 2 + 1 : F[X]) = 0 := by
  simp only [map_add (f := _), map_pow, aeval_X, map_one, neg_sq, ii_sq F]; ring

def conj : Ext F →ₐ[F] Ext F := AdjoinRoot.liftAlgHom (X ^ 2 + 1 : F[X]) (Algebra.ofId F (Ext F)) (-ii F)
  (by have := aeval_neg_ii F; rwa [aeval_def] at this)

theorem conj_ii : conj F (ii F) = -ii F := by
  simp [conj, ii]

theorem conj_algebraMap (a : F) : conj F (algebraMap F (Ext F) a) = algebraMap F (Ext F) a :=
  (conj F).commutes a

theorem exists_repr (x : Ext F) : ∃ a b : F, x = algebraMap F (Ext F) a + algebraMap F (Ext F) b * ii F := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  have hm : (X ^ 2 + 1 : F[X]).Monic := by monicity!
  have hdeg : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!
  set r := p %ₘ (X ^ 2 + 1 : F[X])
  have hr : AdjoinRoot.mk (X ^ 2 + 1 : F[X]) p = AdjoinRoot.mk _ r := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨p /ₘ (X ^ 2 + 1), by have := modByMonic_add_div p (X ^ 2 + 1 : F[X]); linear_combination -this⟩
  have hrd : r.natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt p hm (by intro h; have := congrArg natDegree h; rw [hdeg] at this; simp at this)
    change (p %ₘ (X ^ 2 + 1 : F[X])).natDegree ≤ 1
    omega
  refine ⟨r.coeff 0, r.coeff 1, ?_⟩
  rw [hr, eq_X_add_C_of_natDegree_le_one hrd]
  simp [ii, AdjoinRoot.algebraMap_eq, add_comm]

theorem ii_ne_zero : ii F ≠ 0 := by
  intro h
  have := ii_sq F
  rw [h] at this
  norm_num at this

theorem mem_range_of_conj_eq (x : Ext F) (hx : conj F x = x) : ∃ a : F, algebraMap F (Ext F) a = x := by
  obtain ⟨a, b, rfl⟩ := exists_repr F x
  refine ⟨a, ?_⟩
  simp only [map_add (f := _), map_mul, conj_algebraMap, conj_ii] at hx
  have h2 : (2 : Ext F) * algebraMap F (Ext F) b * ii F = 0 := by linear_combination -hx
  have hb : algebraMap F (Ext F) b = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h two_ne_zero
      · exact h
    · exact absurd h (ii_ne_zero F)
  rw [hb]; ring

theorem embedding_conj (φ : Ext F →+* ℂ) (x : Ext F) : φ (conj F x) = starRingEnd ℂ (φ x) := by
  have key : φ.comp (conj F).toRingHom = (starRingEnd ℂ).comp φ := by
    apply AdjoinRoot.ringHom_ext
    · ext a
      have hre := NumberField.IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F (Ext F)))
      have h1 := hre.coe_embedding_apply a
      simp only [RingHom.comp_apply, AdjoinRoot.algebraMap_eq] at h1 ⊢
      have h3 : (conj F).toRingHom (AdjoinRoot.of _ a) = AdjoinRoot.of _ a := by
        rw [← AdjoinRoot.algebraMap_eq]; exact conj_algebraMap F a
      rw [h3, ← h1, Complex.conj_ofReal]
    · have h := congrArg φ (ii_sq F)
      simp only [map_pow, map_neg, map_one] at h
      have hc : (φ (ii F) - I) * (φ (ii F) + I) = 0 := by linear_combination h - I_sq
      simp only [RingHom.comp_apply]
      change φ (conj F (ii F)) = starRingEnd ℂ (φ (ii F))
      rw [conj_ii, map_neg]
      rcases mul_eq_zero.1 hc with h' | h'
      · rw [sub_eq_zero.1 h']; simp
      · rw [eq_neg_of_add_eq_zero_left h']; simp
  exact congrArg (fun f => f x) key

theorem isIntegral_conj {x : Ext F} (hx : IsIntegral ℤ x) : IsIntegral ℤ (conj F x) :=
  hx.map ((conj F).toRingHom.toIntAlgHom)

theorem pow_mem_range (u : (𝓞 (Ext F))ˣ) :
    ∃ m : ℕ, 0 < m ∧ u ^ m ∈ (Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom).range := by
  set x : Ext F := ((u : 𝓞 (Ext F)) : Ext F)
  set y : Ext F := (((u⁻¹ : (𝓞 (Ext F))ˣ) : 𝓞 (Ext F)) : Ext F)
  have hxy : x * y = 1 := by
    have := congrArg (fun z : 𝓞 (Ext F) => (z : Ext F)) u.mul_inv
    simpa [x, y] using this
  have hx0 : x ≠ 0 := left_ne_zero_of_mul_eq_one hxy
  have hint : IsIntegral ℤ (x * conj F y) :=
    (RingOfIntegers.isIntegral_coe _).mul (isIntegral_conj F (RingOfIntegers.isIntegral_coe _))
  obtain ⟨m, hm, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one (Ext F) ℂ hint fun φ => by
    have h1 : φ x * φ y = 1 := by rw [← map_mul, hxy, map_one]
    rw [map_mul, embedding_conj, norm_mul, Complex.norm_conj, ← norm_mul, h1, norm_one]
  refine ⟨m, hm, ?_⟩

  have hcxy : conj F x * conj F y = 1 := by rw [← map_mul, hxy, map_one]
  have hfix : conj F (x ^ m) = x ^ m := by
    have : (x * conj F y) ^ m * (conj F x) ^ m = (conj F x) ^ m := by rw [hpow, one_mul]
    rw [map_pow, ← this, ← mul_pow, mul_assoc, mul_comm (conj F y), hcxy, mul_one]
  obtain ⟨a, ha⟩ := mem_range_of_conj_eq F _ hfix
  have hai : IsIntegral ℤ a := by
    refine (isIntegral_algebraMap_iff (B := Ext F)).1 ?_
    rw [ha]; exact (RingOfIntegers.isIntegral_coe _).pow m

  have hfix' : conj F (y ^ m) = y ^ m := by
    have e : y ^ m = (x ^ m)⁻¹ := by rw [← inv_pow, inv_eq_of_mul_eq_one_right hxy]
    rw [e, map_inv₀, hfix]
  obtain ⟨b, hb⟩ := mem_range_of_conj_eq F _ hfix'
  have hbi : IsIntegral ℤ b := by
    refine (isIntegral_algebraMap_iff (B := Ext F)).1 ?_
    rw [hb]; exact (RingOfIntegers.isIntegral_coe _).pow m
  have hab : a * b = 1 := by
    apply (algebraMap F (Ext F)).injective
    rw [map_mul, ha, hb, ← mul_pow, hxy, one_pow, map_one]
  let A : 𝓞 F := ⟨a, hai⟩
  let B : 𝓞 F := ⟨b, hbi⟩
  have hAB : A * B = 1 := RingOfIntegers.ext hab
  refine ⟨⟨A, B, hAB, by rw [mul_comm]; exact hAB⟩, ?_⟩
  apply Units.ext
  apply RingOfIntegers.ext
  simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
  rw [show (((u : 𝓞 (Ext F)) ^ m : 𝓞 (Ext F)) : Ext F) = x ^ m by simp [x], ← ha]
  rfl

theorem finite_quot : Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸
    (Units.map (algebraMap (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) := by
  haveI : Group.FG (𝓞 (Ext F))ˣ := Group.fg_iff_monoid_fg.2 inferInstance
  refine CommGroup.finite_of_fg_torsion _ fun q => ?_
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨m, hm, hu⟩ := pow_mem_range F u
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact hu

end GlobalTheory.GaussExt.UnitIdx

theorem GlobalTheory.GaussExt.finite_units_quot_units : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
    Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸
      (Units.map (algebraMap (NumberField.RingOfIntegers F)
        (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) :=
  fun F _ _ _ => GlobalTheory.GaussExt.UnitIdx.finite_quot F
end
end

section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

theorem _root_.GlobalTheory.T.covolume_fractionalIdealRealLatticeImage : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)] [IsZLattice ℝ (latOf N)], ZLattice.covolume (latOf N) = covol N := by
  first | exact @GlobalTheory.LipschitzCovol.covolume_latOf | exact GlobalTheory.LipschitzCovol.covolume_latOf | (intros; apply GlobalTheory.LipschitzCovol.covolume_latOf <;> assumption)
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isExcisionNbhd_trans' : ∀ (A A' A'' : Type) [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A' A''] [Algebra A A''] [IsScalarTower A A' A''] (h : A), IsExcisionNbhd A A' h → IsExcisionNbhd A' A'' (algebraMap A A' h) → IsExcisionNbhd A A'' h := by
  first | (exact @GlobalTheory.EtC.isExcisionNbhd_trans) | (exact GlobalTheory.EtC.isExcisionNbhd_trans) | (intros; apply GlobalTheory.EtC.isExcisionNbhd_trans  <;> assumption)
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_unit_form_localization_etale_nbhd : ∀ (B A₂ : Type) [CommRing B] [CommRing A₂] [Algebra B A₂] (f : B), IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ (b₁ : B) (m : ℕ) (e : A₂), e - 1 ∈ Ideal.span {algebraMap B A₂ f} ∧ algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) = (c : Localization.Away (algebraMap B A₂ f)) * algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) := by
  first | (exact @GlobalTheory.DivUnitForm.unit_form) | (exact GlobalTheory.DivUnitForm.unit_form) | (intros; apply GlobalTheory.DivUnitForm.unit_form  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isExcisionNbhd_away_of_isUnit_mod' : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B), IsExcisionNbhd B A' f → IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) → IsExcisionNbhd B (Localization.Away (algebraMap B A' s)) f := by
  first | (exact @GlobalTheory.EtC.isExcisionNbhd_away_of_isUnit_mod) | (exact GlobalTheory.EtC.isExcisionNbhd_away_of_isUnit_mod) | (intros; apply GlobalTheory.EtC.isExcisionNbhd_away_of_isUnit_mod  <;> assumption)
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_excisionNbhd_with_root_of_isUnit : ∀ (A : Type) [CommRing A] (h : A) (q : ℕ), IsUnit (q : A) → ∀ ε r : A, IsUnit ε → ε - r ^ q ∈ Ideal.span {h} → ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'), IsExcisionNbhd A A' h ∧ ∃ x : A', algebraMap A A' ε = x ^ q := by
  first | (exact @GlobalTheory.EtC.exists_excisionNbhd_adjoin_root) | (exact GlobalTheory.EtC.exists_excisionNbhd_adjoin_root) | (intros; apply GlobalTheory.EtC.exists_excisionNbhd_adjoin_root  <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_etale_chart_smooth_algebra_local_point : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R), ∃ (g : ℕ) (t : Fin g → A) (h : A), (∀ i, ε (t i) = 0) ∧ IsUnit (ε h) ∧ GlobalTheory.DenseSec.EtChart R A t h := by
  first | exact @GlobalTheory.DenseSec.exists_etChart | exact GlobalTheory.DenseSec.exists_etChart | (intros; apply GlobalTheory.DenseSec.exists_etChart <;> assumption)
end
