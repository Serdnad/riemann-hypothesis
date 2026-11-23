module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryAdelicProdLocalCompacts
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EtaInfSign

open GlobalTheory.QuadSymbol

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem mem_normGroup_of_pos (v : InfinitePlace (maximalRealSubfield E)) (y : (v.Completion)ˣ)
    (hy : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion)) :
    y ∈ normGroup (maximalRealSubfield E) E v.Completion := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq (maximalRealSubfield E) E
  rw [mem_normGroup_iff_form b h0 h1]
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hy' : 0 < e y := hy
  refine ⟨e.symm (Real.sqrt (e y)), 0, e.injective ?_⟩
  simp only [map_sub, map_pow, map_mul, map_zero, RingEquiv.apply_symm_apply]
  rw [zero_pow two_ne_zero, mul_zero, sub_zero, Real.sq_sqrt hy'.le]

theorem not_mem_normGroup_of_neg (v : InfinitePlace (maximalRealSubfield E)) (y : (v.Completion)ˣ)
    (hy : InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion) < 0) :
    y ∉ normGroup (maximalRealSubfield E) E v.Completion := by
  intro hmem
  have hneg : (-y) ∈ normGroup (maximalRealSubfield E) E v.Completion := by
    refine mem_normGroup_of_pos E v (-y) ?_
    rw [Units.val_neg, map_neg]
    exact neg_pos.2 hy
  have h1 : (-1 : (v.Completion)ˣ) ∈ normGroup (maximalRealSubfield E) E v.Completion := by
    have : (-1 : (v.Completion)ˣ) = y * (-y)⁻¹ := by
      rw [inv_neg, mul_neg, mul_inv_cancel]
    rw [this]
    exact mul_mem hmem (inv_mem hneg)
  exact eta_eq_neg_one_iff.1 (GlobalTheory.GalOfCusp.eta_neg_one E v) h1

theorem eta_real (v : InfinitePlace (maximalRealSubfield E)) (y : (v.Completion)ˣ) :
    eta (maximalRealSubfield E) E v.Completion y =
      if 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion)
      then 1 else -1 := by
  split_ifs with h
  · exact eta_eq_one_iff.2 (mem_normGroup_of_pos E v y h)
  · have h0 : InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion) ≠ 0 :=
      fun h' => y.ne_zero ((InfinitePlace.Completion.extensionEmbeddingOfIsReal _).injective (h'.trans (map_zero _).symm))
    exact eta_eq_neg_one_iff.2 (not_mem_normGroup_of_neg E v y (lt_of_le_of_ne (not_lt.1 h) h0))

theorem embedding_comp_algebraMap (w : InfinitePlace E) :
    (w.comap (algebraMap (maximalRealSubfield E) E)).embedding =
      w.embedding.comp (algebraMap (maximalRealSubfield E) E) := by
  have hw : w.comap (algebraMap (maximalRealSubfield E) E) =
      InfinitePlace.mk (w.embedding.comp (algebraMap (maximalRealSubfield E) E)) := by
    conv_lhs => rw [← InfinitePlace.mk_embedding w]
    rw [InfinitePlace.comap_mk]
  rw [hw]
  rcases InfinitePlace.embedding_mk_eq (w.embedding.comp (algebraMap (maximalRealSubfield E) E)) with h | h
  · exact h
  · rw [h]
    exact ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal _)

theorem extensionEmbedding_completionMap (w : InfinitePlace E)
    (x : (w.comap (algebraMap (maximalRealSubfield E) E)).Completion) :
    InfinitePlace.Completion.extensionEmbedding w
      (AbsoluteValue.Completion.map (w.comap (algebraMap (maximalRealSubfield E) E)).1 w.1 x) =
    ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal _) x : ℝ) : ℂ) := by
  induction x using AbsoluteValue.Completion.induction_on with
  | hp =>
    exact isClosed_eq ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
        (AbsoluteValue.Completion.continuous_map _ _))
      (Complex.continuous_ofReal.comp (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous)
  | ih a =>
    rw [AbsoluteValue.Completion.map_coe, InfinitePlace.Completion.extensionEmbedding_coe,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, InfinitePlace.embedding_of_isReal_apply,
      embedding_comp_algebraMap]
    rfl

theorem unitDir_ofReal (r : ℝ) (hr : r ≠ 0) (u : ℂˣ) (hu : (u : ℂ) = r) :
    GlobalTheory.ConsEta.unitDir u = Units.map (Int.castRingHom ℂ).toMonoidHom (if 0 < r then 1 else -1) := by
  ext
  change (u : ℂ) / (‖(u : ℂ)‖ : ℂ) = _
  rw [hu, Complex.norm_real, Real.norm_eq_abs]
  split_ifs with h
  · rw [abs_of_pos h, div_self (Complex.ofReal_ne_zero.2 hr)]
    simp
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hr), Complex.ofReal_neg, div_neg, div_self (Complex.ofReal_ne_zero.2 hr)]
    simp

end GlobalTheory.EtaInfSign


open GlobalTheory.QuadSymbol in
theorem GlobalTheory.EtaInfSign.quadChar_eq_infSign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    (∀ v, (b : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 v = 1) →
    (GlobalTheory.GalOfCusp.quadChar E).1 b = GlobalTheory.ConsEta.infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) := by
  intro E _ _ _ b hb
  have hfin : GlobalTheory.IdeleNormChar.finComp b = 1 := funext fun v => Units.ext (hb v)
  have hL : (GlobalTheory.GalOfCusp.quadChar E).1 b = Units.map (Int.castRingHom ℂ).toMonoidHom
      (∏ v : InfinitePlace (maximalRealSubfield E),
        eta (maximalRealSubfield E) E v.Completion (GlobalTheory.IdeleNormChar.infComp b v)) := by
    change Units.map _ (etaProd _ E (GlobalTheory.IdeleNormChar.finComp b) (GlobalTheory.IdeleNormChar.infComp b)) = _
    unfold etaProd
    rw [hfin]
    have h1 : (fun v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) =>
        eta (maximalRealSubfield E) E (v.adicCompletion _) ((1 : FinFam (maximalRealSubfield E)) v)) = fun _ => 1 :=
      funext fun v => eta_eq_one_iff.2 (one_mem _)
    rw [h1, finprod_one, one_mul]
  rw [hL, map_prod, GlobalTheory.ConsEta.infSign, MonoidHom.finsetProd_apply]
  symm
  refine Fintype.prod_equiv (IsCMField.equivInfinitePlace E) _ _ fun w => ?_
  rw [IsCMField.equivInfinitePlace_apply, GlobalTheory.EtaInfSign.eta_real]
  have hv := IsTotallyReal.isReal (w.comap (algebraMap (maximalRealSubfield E) E))
  refine GlobalTheory.EtaInfSign.unitDir_ofReal _ ?_ _ ?_
  · intro h'
    exact (GlobalTheory.IdeleNormChar.infComp b _).ne_zero
      ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective (by rw [map_zero]; exact h'))
  · exact GlobalTheory.EtaInfSign.extensionEmbedding_completionMap E w _
end
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_unitaryAdelicPoint_of_eventually_integral_local : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (h : ∀ v : AwayP p, Gv G v), (∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), h v ∈ IntV G v) → ∃ g : G.GAf, ∀ v, piV G v g = h v := by
  first | (exact @GlobalTheory.OrbFinAf.exists_glue) | (exact GlobalTheory.OrbFinAf.exists_glue) | (intros; apply GlobalTheory.OrbFinAf.exists_glue  <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eventually_isIntV_one_tmul : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] c) := by
  first | (exact @GlobalTheory.OrbFinAfFixed.isIntV_one_tmul_eventually) | (exact GlobalTheory.OrbFinAfFixed.isIntV_one_tmul_eventually) | (intros; apply GlobalTheory.OrbFinAfFixed.isIntV_one_tmul_eventually  <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.isCompact_unitaryPointsAtPlace_fst_mem_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C); ∀ K : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact K → IsCompact {d : Gv G v | (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ K} := by
  first | (exact @GlobalTheory.OrbFinAf.isCompact_setOf_fst_mem) | (exact GlobalTheory.OrbFinAf.isCompact_setOf_fst_mem) | (intros; apply GlobalTheory.OrbFinAf.isCompact_setOf_fst_mem  <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.star_preserves_integrality : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a : Qv v ⊗[ℚ] G.C, IsIntV G v a → IsIntV G v (starT G.star (Qv v) a).unop := by
  first | (exact @GlobalTheory.OrbFinAf.isIntV_star_eventually) | (exact GlobalTheory.OrbFinAf.isIntV_star_eventually) | (intros; apply GlobalTheory.OrbFinAf.isIntV_star_eventually  <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eventually_compact_unitaryAdelic_image_integral : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω → ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), piV G v '' Ω ⊆ IntV G v := by
  first | (exact @GlobalTheory.OrbFinAf.cptInt) | (exact GlobalTheory.OrbFinAf.cptInt) | (intros; apply GlobalTheory.OrbFinAf.cptInt  <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eventually_integral_tensor_points_sharp_stable_ring : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v 1 ∧ (∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) ∧ (∀ y : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v (starT G.star (Qv v) y).unop) := by
  first | (exact @GlobalTheory.OrbFinAf.intV_order_eventually) | (exact GlobalTheory.OrbFinAf.intV_order_eventually) | (intros; apply GlobalTheory.OrbFinAf.intV_order_eventually  <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eventually_isIntegralInCompletedTensorBasis_mul_explicit : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a b : Qv v ⊗[ℚ] G.C, IsIntV G v a → IsIntV G v b → IsIntV G v (a * b) := by
  first | (exact @GlobalTheory.OrbFinAf.isIntV_mul_eventually') | (exact GlobalTheory.OrbFinAf.isIntV_mul_eventually') | (intros; apply GlobalTheory.OrbFinAf.isIntV_mul_eventually' <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_sqrt_fixed_near_one_commutative_centralizer : ∀ (p : ℕ) [Fact p.Prime] (v : AwayP p) (B : Type) [Ring B] [Algebra (Qv v) B] [Module.Finite (Qv v) B], letI : TopologicalSpace B := moduleTopology (Qv v) B; ∀ (e : B) (σ : B →ₗ[Qv v] B), (∀ a b : B, a * e = e * a → b * e = e * b → a * b = b * a) → (∀ a : B, a * e = e * a → σ a * e = e * σ a) → (∀ a b : B, a * e = e * a → b * e = e * b → σ (a * b) = σ a * σ b) → σ 1 = 1 → ∃ W ∈ nhds (1 : B), ∀ s ∈ W, s * e = e * s → σ s = s → ∃ r : B, r * e = e * r ∧ σ r = r ∧ r * r = s := by
  first | (exact @GlobalTheory.sqrt_fix_near_one_centralizer) | (exact GlobalTheory.sqrt_fix_near_one_centralizer) | (intros; apply GlobalTheory.sqrt_fix_near_one_centralizer <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.local_units_locally_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C); T2Space (Qv v ⊗[ℚ] G.C)ˣ ∧ LocallyCompactSpace (Qv v ⊗[ℚ] G.C)ˣ ∧ SigmaCompactSpace (Qv v ⊗[ℚ] G.C)ˣ := by
  first | (exact @GlobalTheory.OrbFinAf.topA) | (exact GlobalTheory.OrbFinAf.topA) | (intros; apply GlobalTheory.OrbFinAf.topA  <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.unitaryAdelicPoint_ext_of_components : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g g' : G.GAf), (∀ v : AwayP p, piV G v g = piV G v g') → g = g' := by
  first | (exact @GlobalTheory.OrbFinAf.ext_of_piV) | (exact GlobalTheory.OrbFinAf.ext_of_piV) | (intros; apply GlobalTheory.OrbFinAf.ext_of_piV  <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.isCompact_unitaryAdelic_prod_local_compacts : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (D : ∀ v : AwayP p, Set (Gv G v)), (∀ v, IsCompact (D v)) → (∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), D v ⊆ IntV G v) → IsCompact {g : G.GAf | ∀ v, piV G v g ∈ D v} := by
  first | (exact @GlobalTheory.OrbFinAf.isCompact_prod_local) | (exact GlobalTheory.OrbFinAf.isCompact_prod_local) | (intros; apply GlobalTheory.OrbFinAf.isCompact_prod_local  <;> assumption)
end
