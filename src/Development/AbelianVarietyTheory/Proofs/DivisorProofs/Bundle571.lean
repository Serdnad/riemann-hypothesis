module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle524
import Formalism.DoubleCosetMeasures.Statement
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle516

@[expose] public section

section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer


theorem _root_.GlobalTheory.T.first_maximal_minor_locally_constant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d), IsFirstMax Y J →
    ∀ᶠ Y' in nhds Y, IsFirstMax Y' J := by
  first | exact @GlobalTheory.RankFibreKer.isFirstMax_eventually | exact GlobalTheory.RankFibreKer.isFirstMax_eventually | (intros; apply GlobalTheory.RankFibreKer.isFirstMax_eventually <;> assumption)
end

section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer


theorem _root_.GlobalTheory.T.exists_first_maximal_minor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k), (∃ J, minor Y J ≠ 0) → ∃ J, IsFirstMax Y J := by
  first | exact @GlobalTheory.RankFibreKer.exists_isFirstMax | exact GlobalTheory.RankFibreKer.exists_isFirstMax | (intros; apply GlobalTheory.RankFibreKer.exists_isFirstMax <;> assumption)
end

section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer


theorem _root_.GlobalTheory.T.full_rank_iff_nonzero_minor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k), Y.rank = a ↔ ∃ J, minor Y J ≠ 0 := by
  first | exact @GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero | exact GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero | (intros; apply GlobalTheory.RankFibreKer.rank_eq_iff_exists_minor_ne_zero <;> assumption)
end

section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer


theorem _root_.GlobalTheory.T.section_inverse_into_slice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d), IsFirstMax Y J →
    ((sec Y)⁻¹).val * Y ∈ slice k a d := by
  first | exact @GlobalTheory.RankFibreKer.sec_inv_mul_mem_slice | exact GlobalTheory.RankFibreKer.sec_inv_mul_mem_slice | (intros; apply GlobalTheory.RankFibreKer.sec_inv_mul_mem_slice <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isSheaf_projBundleCochainPresheaf_etale : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ), Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n) :=
  _root_.GlobalTheory.T.projBundleCochainPresheaf_isSheaf
end

section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem _root_.GlobalTheory.T.isClopen_unit_minor_set : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ),
    IsClopen (GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d) := by
  first | exact @GlobalTheory.FullRankCoinv.UnitMinor.isClopen_unitMinorSet | exact GlobalTheory.FullRankCoinv.UnitMinor.isClopen_unitMinorSet | (intros; apply GlobalTheory.FullRankCoinv.UnitMinor.isClopen_unitMinorSet <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem _root_.GlobalTheory.T.rank_eq_of_unit_minor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (Y : Matrix (Fin n) (Fin d) k), Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → Y.rank = n := by
  first | exact @GlobalTheory.unitMinorSet_rank_eq | exact GlobalTheory.unitMinorSet_rank_eq | (intros; apply GlobalTheory.unitMinorSet_rank_eq <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem _root_.GlobalTheory.T.unit_minor_stable_integral_group : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k), E ∈ GlobalTheory.SplitWeil.KO k (Fin n) →
    Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d := by
  first | exact @GlobalTheory.UnitMinorStable.mul_mem_unitMinorSet | exact GlobalTheory.UnitMinorStable.mul_mem_unitMinorSet | (intros; apply GlobalTheory.UnitMinorStable.mul_mem_unitMinorSet <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem _root_.GlobalTheory.T.exists_unit_minor_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (Y : Matrix (Fin n) (Fin d) k), Y.rank = n →
    ∃ E : GL (Fin n) k, E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d := by
  first | exact @GlobalTheory.FullRankCoinv.UnitMinor.exists_GL_mul_mem_unitMinorSet | exact GlobalTheory.FullRankCoinv.UnitMinor.exists_GL_mul_mem_unitMinorSet | (intros; apply GlobalTheory.FullRankCoinv.UnitMinor.exists_GL_mul_mem_unitMinorSet <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem _root_.GlobalTheory.T.integral_group_of_unit_minor_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k), Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d →
    E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → E ∈ GlobalTheory.SplitWeil.KO k (Fin n) := by
  first | exact @GlobalTheory.FullRankCoinv.UnitMinor.mem_KO_of_mul_mem_unitMinorSet | exact GlobalTheory.FullRankCoinv.UnitMinor.mem_KO_of_mul_mem_unitMinorSet | (intros; apply GlobalTheory.FullRankCoinv.UnitMinor.mem_KO_of_mul_mem_unitMinorSet <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

theorem _root_.GlobalTheory.T.cochain_product_vanishing_above_degree : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (p : ℤ) (hα : ∀ c r hr, p < c → α.v c r hr = 0) (c l t : ℤ) (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c, l) = t) (r : ℤ) (hr : t + k = r) (hc : p < c), (biChains R (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ (crossT V ℓ μ hk α z).v t r hr = 0 := by
  first | (exact @GlobalTheory.PBFc.crossT_ι_eq_zero_of_vanish) | (exact GlobalTheory.PBFc.crossT_ι_eq_zero_of_vanish) | (intros; apply GlobalTheory.PBFc.crossT_ι_eq_zero_of_vanish  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

theorem _root_.GlobalTheory.T.projectiveBundleCochain_apply_bisimplex : ∀ (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (n : ℤ) (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U), evT (phi q V ℓ i z n α) a b s h U y = ∑ j : Fin N, (twPairI q i ((j : ℕ) : ℤ)).mul U (-(a : ℤ) + (n - 2 * ((j : ℕ) : ℤ))) (-(b : ℤ) + 2 * ((j : ℕ) : ℤ)) s (by push_cast at h; omega) (ev (α j) a _ rfl U (baseS V y)) (ev (z j) b _ rfl U (vertS V ℓ y)) := by
  first | (exact @GlobalTheory.PBFc.evT_phi) | (exact GlobalTheory.PBFc.evT_phi) | (intros; apply GlobalTheory.PBFc.evT_phi  <;> assumption)
end
