module

import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCoveringOfTraceDualLowerBound
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexIntegrableShareTopLevelVectors
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle160
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeFrameConditionCharacterLocal
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle162
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle161
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormCongruenceLiftSmallGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.SizesProof

theorem vand_pos {n : ℕ} {x : Fin n → ℝ} (h : StrictAnti x) : 0 < Formalism.MainNotions.S.vand x :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hb => sub_pos.2 (h (Finset.mem_filter.1 hb).2)

theorem sizes_of_hyp : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), D.host.rdE ≤ large₂.sc.b →
    HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → Sizes D large₂ Cl Cg CT := by
  apply GlobalTheory.Amp.RangeModel.sizes_of <;> assumption

end GlobalTheory.Amp.SizesProof
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual

namespace GlobalTheory.MeanDual.LatticeDual

variable {E : Type} [Field E] [NumberField E]

theorem sum_embeddings_pairs (hE : IsTotallyComplex E) (f : (E →+* ℂ) → ℂ) :
    ∑ φ : E →+* ℂ, f φ =
      ∑ w : InfinitePlace E, (f w.embedding + f (ComplexEmbedding.conjugate w.embedding)) := by
  classical
  rw [← Finset.sum_fiberwise (s := univ) (g := fun φ : E →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro h
    have hc := IsTotallyComplex.isComplex (K := E) w
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff] at hc
    exact hc h.symm
  rw [← Finset.sum_pair hne]
  congr 1
  ext φ
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  conv_lhs => rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [← h]; ext x; simp
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [h]; ext x; simp

theorem sum_re_embedding (hE : IsTotallyComplex E) (e : E) :
    ∑ w : InfinitePlace E, (w.embedding e).re = ((Algebra.trace ℚ E e : ℚ) : ℝ) / 2 := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := e)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ e = ∑ φ : E →+* ℂ, φ e :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ (fun φ => rfl)).symm
  rw [h2, sum_embeddings_pairs hE] at h1
  have h3 := congrArg Complex.re h1
  simp only [eq_ratCast, Complex.ratCast_re, Complex.re_sum, Complex.add_re,
    ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] at h3
  rw [h3, Finset.sum_add_distrib]; ring

theorem eq_zero_of_sum_re (hE : IsTotallyComplex E) (c : InfinitePlace E → ℂ)
    (h : ∀ e : E, ∑ w : InfinitePlace E, (w.embedding e * c w).re = 0) : c = 0 := by
  apply GlobalTheory.TraceCover.eq_zero_of_sum_re <;> assumption

theorem exists_int_smul_mem {j : ℕ} (Λ : Submodule (𝓞 E) (Fin j → E))
    (hΛ : Submodule.IsFullLattice E Λ) (x : Fin j → E) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • x ∈ Λ := by
  exact _root_.GlobalTheory.IntegralMultiple.main Λ hΛ x

theorem pairing_rational (hE : IsTotallyComplex E) {j : ℕ} (x y : Fin j → E) :
    ∑ w : InfinitePlace E,
      ((fun a => w.embedding (x a)) ⬝ᵥ (fun a => w.embedding (y a))).re =
      ((Algebra.trace ℚ E (x ⬝ᵥ y) : ℚ) : ℝ) / 2 := by
  rw [← sum_re_embedding hE]
  refine Finset.sum_congr rfl fun w _ => ?_

  simp only [dotProduct, map_sum, map_mul]

theorem exists_trDual (hE : IsTotallyComplex E) {j : ℕ} (Λ : Submodule (𝓞 E) (Fin j → E))
    (hΛ : Submodule.IsFullLattice E Λ) (u : InfinitePlace E → Fin j → ℂ)
    (hu : ∀ x ∈ Λ, ∃ z : ℤ, ∑ w : InfinitePlace E, ((fun a => w.embedding (x a)) ⬝ᵥ u w).re = z) :
    ∃ y ∈ trDual E j Λ, ∀ w a, u w a = w.embedding (y a) := by
  classical
  let φ : (Fin j → E) →+ ℝ :=
    { toFun := fun x => ∑ w : InfinitePlace E, ((fun a => w.embedding (x a)) ⬝ᵥ u w).re
      map_zero' := by simp [dotProduct]
      map_add' := by
        intro x y
        simp [dotProduct, add_mul, Finset.sum_add_distrib] }
  have hq : ∀ x, ∃ q : ℚ, φ x = q := by
    intro x
    obtain ⟨n, hn, hx⟩ := exists_int_smul_mem Λ hΛ x
    obtain ⟨z, hz⟩ := hu _ hx
    have h1 : φ (n • x) = z := by
      rw [← Int.cast_smul_eq_zsmul E]; exact hz
    rw [map_zsmul, zsmul_eq_mul] at h1
    refine ⟨z / n, ?_⟩
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    push_cast
    field_simp
    linarith
  choose q hq using hq
  let ψ : (Fin j → E) →+ ℚ :=
    { toFun := q
      map_zero' := by
        apply Rat.cast_injective (α := ℝ)
        rw [← hq]; simp
      map_add' := by
        intro x y
        apply Rat.cast_injective (α := ℝ)
        rw [Rat.cast_add, ← hq, ← hq, ← hq, map_add (f := _)] }
  have hy : ∀ a : Fin j, ∃ y : E, ∀ e : E,
      Algebra.trace ℚ E (y * e) = 2 * q (Pi.single a e) := by
    intro a
    obtain ⟨y, hy⟩ := ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).surjective
      ((2 : ℚ) • (ψ.toRatLinearMap ∘ₗ LinearMap.single ℚ (fun _ => E) a))
    refine ⟨y, fun e => ?_⟩
    have := LinearMap.congr_fun hy e
    rw [LinearMap.BilinForm.toDual_def] at this
    simpa [ψ] using this
  choose y hy using hy
  have key : ∀ w a, u w a = w.embedding (y a) := by
    intro w a
    have := eq_zero_of_sum_re hE (fun w => u w a - w.embedding (y a)) (by
      intro e
      have h1 : φ (Pi.single a e) = ∑ w : InfinitePlace E, (w.embedding e * u w a).re := by
        refine Finset.sum_congr rfl fun w _ => ?_
        congr 1
        simp only [dotProduct]
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb; simp [hb]
        · simp
      have h2 := sum_re_embedding hE (y a * e)
      rw [hy] at h2
      simp only [mul_sub, Complex.sub_re, Finset.sum_sub_distrib, ← map_mul]
      rw [← h1, hq, mul_comm e, h2]; push_cast; ring)
    exact sub_eq_zero.1 (congrFun this w)
  refine ⟨y, ?_, key⟩
  intro x hx
  obtain ⟨z, hz⟩ := hu x hx
  refine ⟨z, ?_⟩
  have h1 := pairing_rational hE x y
  have h2 : ∀ w, u w = fun a => w.embedding (y a) := fun w => funext (key w)
  simp only [h2] at hz
  rw [hz] at h1
  apply Rat.cast_injective (α := ℝ)
  push_cast
  linarith

end GlobalTheory.MeanDual.LatticeDual

namespace GlobalTheory.MeanDual
open LatticeDual

theorem dualAt_latAt_eq_latAt_trDual : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsFullLattice E Λ → ∀ g : MatInf E j, 0 < _root_.GlobalTheory.FlagMeas.detNorm E j g → dualAt E j (latAt E j Λ g) = latAt E j (trDual E j Λ) (invT E j g) := by
  intro E _ _ hE j Λ hΛ g hg
  have hdet : ∀ w, IsUnit (of (g w)).det := fun w =>
    isUnit_iff_ne_zero.2 ((detNorm_pos_iff E j g).1 hg w)
  have hinv : ∀ w, (of (invT E j g w))⁻¹ = (of (g w))ᵀ := by
    intro w
    rw [of_invT, ← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ (hdet w)]
  have hadj : ∀ (w : InfinitePlace E) (v v' : Fin j → ℂ),
      ((of (g w))⁻¹ *ᵥ v) ⬝ᵥ v' = v ⬝ᵥ ((of (g w))⁻¹ᵀ *ᵥ v') := by
    intro w v v'
    rw [Matrix.mulVec_transpose, dotProduct_comm v, ← Matrix.dotProduct_mulVec, dotProduct_comm]
  have hc1 : ∀ (w : InfinitePlace E) (v : Fin j → ℂ),
      (of (g w))⁻¹ᵀ *ᵥ ((of (g w))ᵀ *ᵥ v) = v := by
    intro w v
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ (hdet w)]; simp
  have hc2 : ∀ (w : InfinitePlace E) (v : Fin j → ℂ),
      (of (g w))ᵀ *ᵥ ((of (g w))⁻¹ᵀ *ᵥ v) = v := by
    intro w v
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (hdet w)]; simp
  apply le_antisymm
  · refine Submodule.span_le.2 fun v hv => ?_
    obtain ⟨y, hy, hyv⟩ := exists_trDual hE Λ hΛ (fun w => (of (g w))⁻¹ᵀ *ᵥ v w) (by
      intro x hx
      obtain ⟨z, hz⟩ := hv _ (Submodule.subset_span ⟨x, hx, rfl⟩)
      refine ⟨z, ?_⟩
      rw [← hz]
      exact Finset.sum_congr rfl fun w _ => by rw [← hadj])
    refine Submodule.subset_span ⟨y, hy, ?_⟩
    funext w
    have : (fun a => w.embedding (y a)) = (of (g w))⁻¹ᵀ *ᵥ v w := funext fun a => (hyv w a).symm
    simp only [hinv, this, hc2]
  · refine Submodule.span_mono ?_
    rintro _ ⟨y, hy, rfl⟩ v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, hx, rfl⟩ := hv
      obtain ⟨z, hz⟩ := hy x hx
      refine ⟨z, ?_⟩
      simp only [hinv, hadj, hc1]
      rw [pairing_rational hE, hz]; push_cast; ring
    | zero => exact ⟨0, by simp⟩
    | add v v' _ _ h h' =>
      obtain ⟨z, hz⟩ := h
      obtain ⟨z', hz'⟩ := h'
      refine ⟨z + z', ?_⟩
      push_cast
      rw [← hz, ← hz', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← Complex.add_re, ← add_dotProduct]; rfl
    | smul n v _ h =>
      obtain ⟨z, hz⟩ := h
      refine ⟨n * z, ?_⟩
      push_cast
      rw [← hz, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      have : (n • v) w = n • v w := rfl
      rw [this, smul_dotProduct]; simp

end GlobalTheory.MeanDual
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.FlagRareProof

theorem flagRare_of_nonzeroFlagBound : GlobalTheory.FlagMeas.NonzeroFlagBound → GlobalTheory.IndefiniteRowSideFullHecke.RareFlags.FlagRare := by
  intro h
  refine ⟨⌈Real.exp 15⌉₊, ?_⟩
  intro B p q hsig hn hq hrd hf

  have hn' : Real.exp 15 ≤ (B.I.n : ℝ) := Nat.ceil_le.1 hn
  have hn1 : 1 ≤ B.I.n := by
    have : 0 < ⌈Real.exp 15⌉₊ := Nat.ceil_pos.2 (Real.exp_pos 15)
    omega
  have hlog : 15 ≤ Real.log B.I.n := by
    have := Real.log_le_log (Real.exp_pos 15) hn'
    rwa [Real.log_exp] at this
  have key := h B.I B.μf B.fund B.fund_spec p q hsig hlog hq hrd hf

  have hset : {x | least B.I x < 1 / 2} = {x | stepLt B.I x (1 / 2) ≠ ⊥} := by
    ext x
    have hx := ((GlobalTheory.CountSteps.steps B.I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.2 hn1).2.2
    simp only [Set.mem_ofPred_eq, ne_eq, hx, not_le]
  have hnf : 0 ≤ (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith)
  rw [prob, hset, Formalism.MainNotions.S.AutInst.vol, ← ENNReal.toReal_div]
  calc _ ≤ Real.exp (-(1 / 3 * (B.I.n : ℝ) * B.I.f * Real.log B.I.n)) :=
        ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le key
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)

end GlobalTheory.FlagRareProof
end

section

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

noncomputable section

namespace GlobalTheory.SerSys.LabLoc

open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem eq_of_roots_eq {f h : (ZMod g)[X]} (hf : f.Monic) (hh : h.Monic)
    (e : Formalism.CyclotomicNorms.rootsBar f = Formalism.CyclotomicNorms.rootsBar h) : f = h := by
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
  rw [(IsAlgClosed.splits (f.map _)).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (h.map _)).eq_prod_roots_of_monic (hh.map _)]
  exact congrArg (fun m : Multiset (Formalism.CyclotomicNorms.Fbar g) => (m.map fun a => X - C a).prod) e

theorem ne_zero_of_mem_roots {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) {x : Formalism.CyclotomicNorms.Fbar g}
    (hx : x ∈ Formalism.CyclotomicNorms.rootsBar f) : x ≠ 0 := by
  rintro rfl
  have hf : f.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) ≠ 0 := (mem_roots'.1 hx).1
  have := (mem_roots'.1 hx).2
  rw [IsRoot, eval_map, eval₂_at_zero] at this
  exact h0 ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective (by simpa using this))

theorem map_eq_map {τ : Formalism.CyclotomicNorms.Fbar g →* ℂ} (hτ : Set.InjOn τ {x | x ≠ 0}) {A B : Multiset (Formalism.CyclotomicNorms.Fbar g)}
    (hA : ∀ x ∈ A, x ≠ 0) (hB : ∀ x ∈ B, x ≠ 0) (e : A.map τ = B.map τ) : A = B := by
  rw [Multiset.ext]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [Multiset.count_eq_zero.2 (fun h => hA 0 h rfl), Multiset.count_eq_zero.2 (fun h => hB 0 h rfl)]
  have key : ∀ C : Multiset (Formalism.CyclotomicNorms.Fbar g), (∀ y ∈ C, y ≠ 0) → C.count x = (C.map τ).count (τ x) := by
    intro C hC
    rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
    congr 1
    refine Multiset.filter_congr fun y hy => ⟨fun h => h ▸ rfl, fun h => hτ hx (hC y hy) h⟩
  rw [key A hA, key B hB, e]

theorem actK_finset_sum {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) ℚ_[g]) V) {ι : Type} (T : Finset ι) (a : ι → MonoidAlgebra ℂ (Gn g n)) :
    actK ρ (∑ i ∈ T, a i) = ∑ i ∈ T, actK ρ (a i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [actK]
  | insert i T hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    simp [actK, add_smul, Finset.sum_add_distrib]

theorem actK_one_of_mem {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) ℚ_[g]) V) {v : V} (hv : v ∈ fixK1 ρ) : actK ρ 1 v = v := by
  have hs : actK ρ 1 = ρ (lift g n 1) := by
    unfold actK
    rw [MonoidAlgebra.one_def, Finset.sum_eq_single 1]
    · simp
    · intro y _ hy
      simp [Finsupp.single_eq_of_ne hy]
    · simp
  have hk : red g n (Function.invFun (red g n) 1) = 1 := Function.invFun_eq ⟨1, map_one _⟩
  rw [hs, lift]
  have := (Submodule.mem_iInf _).1 hv ⟨_, hk⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  simpa using this

end GlobalTheory.SerSys.LabLoc

end
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.selfDual_hermitianLattice_mass_bounds : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → 2 * m + 3 ≤ n → ∀ Λ0, IsLat L Λ0 → ∃ κ : ℝ, 0 < κ ∧ ∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → IsIntM L (gramT L Hm (rmul x A⁻¹)) → ENNReal.ofReal (κ / 2 * (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m)))) ≤ sigMass L Hm (Submodule.span E (Set.range x)) Λ0 (Submodule.span L.O (Set.range (rmul x A⁻¹))) ∧ sigMass L Hm (Submodule.span E (Set.range x)) Λ0 (Submodule.span L.O (Set.range (rmul x A⁻¹))) ≤ ENNReal.ofReal (2 * κ * (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m)))) := by
  first | exact @GlobalTheory.HL.Unfold.mass_bounds | exact GlobalTheory.HL.Unfold.mass_bounds | (intros; apply GlobalTheory.HL.Unfold.mass_bounds <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.indexIntegrable_share_top_level_vectors : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → 1 ≤ βJ ∧ 1 ≤ β ∧ Nice (S.refB (j + 1) Λ) (ind fun b : S.V × S.V => b ∈ S.refB (j + 1) Λ ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = j + 1) ∧ cint (S.refB (j + 1) Λ) (ind fun b : S.V × S.V => b ∈ S.refB (j + 1) Λ ∧ S.lev (S.fr d Λ) (S.fr' d Λ) (b.1 + b.2) = j + 1) = (βJ : ℂ) / (β : ℂ) := by
  first | exact @GlobalTheory.TopLevelShare.main | exact GlobalTheory.TopLevelShare.main | (intros; apply GlobalTheory.TopLevelShare.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.adelicLatticeFrame_condition_character_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (k : ℕ) (gp : Fin 2 → ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (Fr : AdFrame cm.sig J (hat F L) (gp 0 * gp 1) k), (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → IsLat L → (∀ x ∈ L, x ∈ dualSet (cm.sig : E →+* E) J L) → ∀ y : GL (Fin n) (E ⊗[F] Ad F), y ∈ stabGL (hat F L) → ((∀ i : Fin k, InModL (hat F L) (gp 0 * gp 1) (Fr.b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ Fr.b i)) ↔ ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → Fr.LocK L v (bc (prV (E := E) v) y)) ∧ Fr.chi y = ∏ i : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (gp i : 𝓞 F) ∈ v.asIdeal), Fr.locChi v (bc (prV (E := E) v) y) := by
  first | exact @GlobalTheory.St.G.frame_local | exact GlobalTheory.St.G.frame_local | (intros; apply GlobalTheory.St.G.frame_local <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.hermitian_dual_vector_norm_inv_not_mem_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), (∀ x ∈ L, x ∈ dualSet (cm.sig : E →+* E) J L) → ∀ (d : Fin n → E) (T : ℕ), 0 < T → d ∈ dualL cm.sig J L → Formalism.UG.hform (cm.sig : E →+* E) J d d - ((T : E))⁻¹ ∈ (algebraMap (𝓞 E) E).range → ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∃ x ∈ loc v (dualL cm.sig J L), x ∉ loc v L := by
  first | exact @GlobalTheory.St.G.dual_not_loc_of_norm_inv | exact GlobalTheory.St.G.dual_not_loc_of_norm_inv | (intros; apply GlobalTheory.St.G.dual_not_loc_of_norm_inv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.split_place_dual_quotient_components_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ((∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) ↔ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2)) := by
  first | exact @GlobalTheory.St.G.dual_components_iff | exact GlobalTheory.St.G.dual_components_iff | (intros; apply GlobalTheory.St.G.dual_components_iff <;> assumption)
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.der_tail_of_lt_of_le : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i m n : ℕ) (F : Gn g n → ℂ), i < m → m ≤ n → der ψ i (tail ψ m F) = der ψ i F := by
  first | exact @GlobalTheory.GLm.DerTail.der_tail | exact GlobalTheory.GLm.DerTail.der_tail | (intros; apply GlobalTheory.GLm.DerTail.der_tail <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePair_exists_unipotent_split_lattice : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ s ∈ N.R, N.Split (s • Λ) := by
  first | exact @GlobalTheory.DegCnt.SplitLift.main | exact GlobalTheory.DegCnt.SplitLift.main | (intros; apply GlobalTheory.DegCnt.SplitLift.main <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePairNormalForm_congruence_lift_smallGroup : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ 𝔫 : Ideal (𝓞 K), (∀ x ∈ 𝔫, ∃ y ∈ 𝔫, (y : K) = star (x : K)) → ∀ s ∈ N.R, (∀ x ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'), s x - x ∈ (Ideal.span {(N.T : 𝓞 K)} * 𝔫) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'))) → ∃ s' ∈ N.Rs, (∀ y ∈ V0 N.F N.F', s' y = s y) ∧ ∀ x ∈ N.P0, s' x - x ∈ 𝔫 • N.P0 := by
  first | exact @GlobalTheory.DegCnt.LiftS.lift_congruence | exact GlobalTheory.DegCnt.LiftS.lift_congruence | (intros; apply GlobalTheory.DegCnt.LiftS.lift_congruence <;> assumption)
end
