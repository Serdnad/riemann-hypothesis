module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle019
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem finite_image_of_isOpen_stabilizer (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (hH : IsOpen {g : G | ρ g v = v})
    (S : Set G) (hS : IsCompact S) : ((fun g => ρ g v) '' S).Finite := by
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun s : G => (fun x => s⁻¹ * x) ⁻¹' {g : G | ρ g v = v})
    (fun s => hH.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  refine ((t : Set G).toFinite.image (fun g => ρ g v)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 (ht hx)
  refine ⟨s, hs, ?_⟩
  have h1 : ρ (s⁻¹ * x) v = v := hxs
  have hx' : x = s * (s⁻¹ * x) := by group
  show ρ s v = ρ x v
  conv_rhs => rw [hx', map_mul, Module.End.mul_apply, h1]

end GlobalTheory
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory

theorem valuation_chain_ratio_bounds (k : Type) [Field k] [ValuativeRel k] (m : ℕ) (r1 r2 : Fin m → kˣ) :
    ∃ R1 R2 : kˣ, 1 ≤ valuation k (R1 : k) ∧ valuation k (R2 : k) ≤ 1 ∧
      ∀ t : Fin (m + 1) → kˣ, t (Fin.last m) = 1 →
        (∀ i : Fin m, valuation k (r2 i : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) ∧
          valuation k ((t i.castSucc : k) / t i.succ) ≤ valuation k (r1 i : k)) →
        ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k) := by
  induction m with
  | zero =>
    refine ⟨1, 1, by simp, by simp, ?_⟩
    intro t ht _ i
    have hi : i = Fin.last 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    subst hi
    rw [ht]; simp
  | succ m ih =>
    obtain ⟨R1', R2', h1', h2', hR⟩ := ih (fun j => r1 j.succ) (fun j => r2 j.succ)
    set a : kˣ := if valuation k (r1 0 : k) ≤ 1 then 1 else r1 0 with ha_def
    set b : kˣ := if 1 ≤ valuation k (r2 0 : k) then 1 else r2 0 with hb_def
    have ha1 : 1 ≤ valuation k (a : k) := by
      rw [ha_def]; split_ifs with h
      · simp
      · exact le_of_lt (not_le.mp h)
    have har : valuation k (r1 0 : k) ≤ valuation k (a : k) := by
      rw [ha_def]; split_ifs with h
      · simpa using h
      · exact le_rfl
    have hb1 : valuation k (b : k) ≤ 1 := by
      rw [hb_def]; split_ifs with h
      · simp
      · exact le_of_lt (not_le.mp h)
    have hbr : valuation k (b : k) ≤ valuation k (r2 0 : k) := by
      rw [hb_def]; split_ifs with h
      · simpa using h
      · exact le_rfl
    refine ⟨R1' * a, R2' * b, ?_, ?_, ?_⟩
    · simp only [Units.val_mul, map_mul]
      exact one_le_mul h1' ha1
    · simp only [Units.val_mul, map_mul]
      exact mul_le_one' h2' hb1
    intro t ht hrat
    have hT := hR (fun j => t j.succ) (by simp only [Fin.succ_last]; exact ht) (fun i => by
      have := hrat i.succ
      rw [← Fin.succ_castSucc] at this; exact this)
    have hR1le : valuation k (R1' : k) ≤ valuation k ((R1' * a : kˣ) : k) := by
      simp only [Units.val_mul, map_mul]; exact le_mul_of_one_le_right' ha1
    have hR2le : valuation k ((R2' * b : kˣ) : k) ≤ valuation k (R2' : k) := by
      simp only [Units.val_mul, map_mul]; exact mul_le_of_le_one_right' hb1
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h0 := hrat 0
      have ht1 := hT 0
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at h0 ht1
      have hne : ((t 1 : kˣ) : k) ≠ 0 := (t 1).ne_zero
      have hsplit : ((t 0 : kˣ) : k) = ((t 0 : k) / t 1) * t 1 := by field_simp
      rw [hsplit, map_mul]
      constructor
      · simp only [Units.val_mul, map_mul]
        calc valuation k (R2' : k) * valuation k (b : k)
            = valuation k (b : k) * valuation k (R2' : k) := mul_comm _ _
          _ ≤ valuation k (r2 0 : k) * valuation k (t 1 : k) := mul_le_mul' hbr ht1.1
          _ ≤ _ := mul_le_mul' h0.1 le_rfl
      · simp only [Units.val_mul, map_mul]
        calc valuation k ((t 0 : k) / t 1) * valuation k (t 1 : k)
            ≤ valuation k (r1 0 : k) * valuation k (R1' : k) := mul_le_mul' h0.2 ht1.2
          _ ≤ valuation k (a : k) * valuation k (R1' : k) := mul_le_mul' har le_rfl
          _ = _ := mul_comm _ _
    · have := hT j
      exact ⟨hR2le.trans this.1, this.2.trans hR1le⟩

theorem chain_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (r1 r2 : Fin m → kˣ), ∃ R1 R2 : kˣ, ∀ t : Fin (m + 1) → kˣ, t (Fin.last m) = 1 → (∀ i : Fin m, valuation k (r2 i : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) ∧ valuation k ((t i.castSucc : k) / t i.succ) ≤ valuation k (r1 i : k)) → ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k) := by
  intro k _ _ _ _ m r1 r2
  obtain ⟨R1, R2, -, -, h⟩ := valuation_chain_ratio_bounds k m r1 r2
  exact ⟨R1, R2, h⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem isOpen_setOf_valuation_lt_of_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    IsOpen {x : k | valuation k x < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hx hy ⊢
  have h := (valuation k).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact h.trans_lt (max_lt hy hx)

theorem isCompact_boundedTorus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (R1 R2 : kˣ), IsCompact {t : Fin m → kˣ | ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k)} := by
  intro k _ _ _ _ m R1 R2
  have hS : IsCompact {x : kˣ | valuation k (R2 : k) ≤ valuation k (x : k) ∧ valuation k (x : k) ≤ valuation k (R1 : k)} := by
    rw [Units.isEmbedding_val₀.isCompact_iff]
    have himg : (Units.val '' {x : kˣ | valuation k (R2 : k) ≤ valuation k (x : k) ∧ valuation k (x : k) ≤ valuation k (R1 : k)})
        = {y : k | valuation k y ≤ valuation k (R1 : k)} ∩ {y : k | valuation k (R2 : k) ≤ valuation k y} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx.2, hx.1⟩
      · rintro ⟨h1, h2⟩
        have hy : y ≠ 0 := by
          rintro rfl
          simp at h2
        exact ⟨Units.mk0 y hy, ⟨h2, h1⟩, rfl⟩
    rw [himg]
    refine (IsNonarchimedeanLocalField.isCompact_closedBall k _).inter_right ?_
    have hne : valuation k (R2 : k) ≠ 0 := by simp
    have ho := isOpen_setOf_valuation_lt_of_ne_zero (valuation k (R2 : k)) hne
    have hc : {y : k | valuation k (R2 : k) ≤ valuation k y} = {y : k | valuation k y < valuation k (R2 : k)}ᶜ := by
      ext y; simp
    rw [hc]
    exact ho.isClosed_compl
  have : {t : Fin m → kˣ | ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k)}
      = Set.pi Set.univ (fun _ => {x : kˣ | valuation k (R2 : k) ≤ valuation k (x : k) ∧ valuation k (x : k) ≤ valuation k (R1 : k)}) := by
    ext t; simp
  rw [this]
  exact isCompact_univ_pi fun _ => hS

end GlobalTheory
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem adicCompletion_trace_norm_continuous : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), Continuous f → letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) → Continuous (Algebra.trace (v.adicCompletion K) (v'.adicCompletion L)) ∧ Continuous (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) := by
  intro K L _ _ _ _ v v' f hf
  letI := f.toAlgebra
  intro hfd
  letI : NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField _ _
  haveI : CompleteSpace (v.adicCompletion K) := inferInstance
  haveI : ContinuousSMul (v.adicCompletion K) (v'.adicCompletion L) := continuousSMul_of_algebraMap _ _ hf
  refine ⟨LinearMap.continuous_of_finiteDimensional _, ?_⟩
  let b := Module.finBasis (v.adicCompletion K) (v'.adicCompletion L)
  have hn : (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) = fun y => (Algebra.leftMulMatrix b y).det := by
    funext y; exact Algebra.norm_eq_matrix_det b y
  rw [hn]
  have hl : Continuous (fun y => Algebra.leftMulMatrix b y) :=
    (LinearMap.continuous_of_finiteDimensional (Algebra.leftMulMatrix b).toLinearMap)
  exact hl.matrix_det

end GlobalTheory
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem algebraMap_mem_span_of_mem_span {K L A M : Type} [Field K] [Field L] [Algebra K L]
    [Field A] [CommRing M] [Algebra L M] [Algebra A M] (g : K →+* A)
    (hg : ∀ c : K, algebraMap A M (g c) = algebraMap L M (algebraMap K L c))
    {ι : Type} (s : ι → L) (x : L) (hx : x ∈ Submodule.span K (Set.range s)) :
    algebraMap L M x ∈ Submodule.span A (Set.range fun i => algebraMap L M (s i)) := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [Algebra.smul_def, map_mul, ← hg, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hy

theorem linearIndependent_completion_of_irreducible_minpoly :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → (∀ α : L, Irreducible ((minpoly K α).map (algebraMap K (v.adicCompletion K)))) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L), LinearIndependent (v.adicCompletion K) fun i => algebraMap L (v'.adicCompletion L) (b i) := by
  intro K L _ _ _ _ _ v v' f hf hirr
  letI := f.toAlgebra
  intro n b
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hcomp : f.comp (algebraMap K (v.adicCompletion K)) =
      (algebraMap L (v'.adicCompletion L)).comp (algebraMap K L) := RingHom.ext hf
  have hroot : Polynomial.aeval (algebraMap L (v'.adicCompletion L) α)
      ((minpoly K α).map (algebraMap K (v.adicCompletion K))) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    change Polynomial.eval₂ (f.comp (algebraMap K (v.adicCompletion K))) _ _ = 0
    rw [hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  have hmin : (minpoly K α).map (algebraMap K (v.adicCompletion K)) =
      minpoly (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) α) :=
    minpoly.eq_of_irreducible_of_monic (hirr α) hroot ((minpoly.monic hint).map _)
  have hdeg : (minpoly (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) α)).natDegree
      = n := by
    rw [← hmin, (minpoly.monic hint).natDegree_map, ← IntermediateField.adjoin.finrank hint, hα,
      IntermediateField.finrank_top', Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hpow := linearIndependent_pow (K := v.adicCompletion K)
    (algebraMap L (v'.adicCompletion L) α)
  have hle : Submodule.span (v.adicCompletion K) (Set.range fun i : Fin (minpoly
      (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) α)).natDegree =>
        (algebraMap L (v'.adicCompletion L) α) ^ (i : ℕ)) ≤
      Submodule.span (v.adicCompletion K)
        (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have := algebraMap_mem_span_of_mem_span (M := v'.adicCompletion L)
      (algebraMap K (v.adicCompletion K)) hf b (α ^ (i : ℕ)) (by rw [b.span_eq]; trivial)
    simpa using this
  have h1 := finrank_span_eq_card hpow
  have h2 := finrank_range_le_card (R := v.adicCompletion K)
    (fun i => algebraMap L (v'.adicCompletion L) (b i))
  haveI : Module.Finite (v.adicCompletion K) (Submodule.span (v.adicCompletion K)
      (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i))) :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have h3 := Submodule.finrank_mono hle
  rw [linearIndependent_iff_card_eq_finrank_span]
  simp only [Fintype.card_fin] at h1 h2 ⊢
  rw [Set.finrank] at h2 ⊢
  omega

end GlobalTheory
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem span_basis_image_adicCompletion_eq_top
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L))
    (f : v.adicCompletion K →+* v'.adicCompletion L) (hfc : Continuous f)
    (hf : ∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) :
    letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L),
      Submodule.span (v.adicCompletion K)
        (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) = ⊤ := by
  letI := f.toAlgebra
  intro n b
  letI : NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField _ _
  set S := Submodule.span (v.adicCompletion K)
    (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) with hS
  haveI : ContinuousSMul (v.adicCompletion K) (v'.adicCompletion L) := by
    constructor
    have : (fun p : v.adicCompletion K × v'.adicCompletion L => p.1 • p.2)
        = fun p => f p.1 * p.2 := by
      funext p; exact Algebra.smul_def _ _
    rw [this]
    exact (hfc.comp continuous_fst).mul continuous_snd
  haveI : FiniteDimensional (v.adicCompletion K) S :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hclosed : IsClosed (S : Set (v'.adicCompletion L)) := S.closed_of_finiteDimensional
  have hmem : ∀ z : L, algebraMap L (v'.adicCompletion L) z ∈ S := by
    intro z

    rw [← b.sum_repr z, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : algebraMap L (v'.adicCompletion L) (b.repr z i • b i)
        = (algebraMap K (v.adicCompletion K) (b.repr z i)) •
            algebraMap L (v'.adicCompletion L) (b i) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, hf]
    rw [this]
    exact S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdense := HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) L v'
  have hsub : Set.range (algebraMap L (v'.adicCompletion L)) ⊆ (S : Set _) := by
    rintro _ ⟨z, rfl⟩; exact hmem z
  have huniv : (S : Set (v'.adicCompletion L)) = Set.univ := by
    have := closure_minimal hsub hclosed
    rw [hdense.closure_range] at this
    exact Set.univ_subset_iff.mp this
  exact eq_top_iff.mpr fun x _ => by
    have : x ∈ (S : Set (v'.adicCompletion L)) := huniv ▸ Set.mem_univ x
    exact this

end GlobalTheory
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.adicCompletion_trace_norm_of_basis_image : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L) (b' : Module.Basis (Fin n) (v.adicCompletion K) (v'.adicCompletion L)), (∀ i, b' i = algebraMap L _ (b i)) → ∀ z : L, Algebra.trace (v.adicCompletion K) (v'.adicCompletion L) (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z) ∧ Algebra.norm (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) z) = algebraMap K _ (Algebra.norm K z) := by
  intro K L _ _ _ _ _ v v' f hf
  letI := f.toAlgebra
  intro n b b' hb z
  have hM : Algebra.leftMulMatrix b' (algebraMap L (v'.adicCompletion L) z) =
      (Algebra.leftMulMatrix b z).map (algebraMap K (v.adicCompletion K)) := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
    have key : algebraMap L (v'.adicCompletion L) z * b' j =
        ∑ k, (algebraMap K (v.adicCompletion K) (b.repr (z * b j) k)) • b' k := by
      rw [hb, ← map_mul]
      conv_lhs => rw [← b.sum_repr (z * b j)]

      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb, Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, hf]
    rw [key, b'.repr_sum_self]
  rw [Algebra.trace_eq_matrix_trace b', Algebra.norm_eq_matrix_det b', hM,
    Algebra.trace_eq_matrix_trace b, Algebra.norm_eq_matrix_det b]
  refine ⟨?_, ?_⟩
  · exact (AddMonoidHom.map_trace (algebraMap K (v.adicCompletion K)).toAddMonoidHom _).symm
  · exact (RingHom.map_det _ _).symm
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DenseCompl


open scoped WithZeroTopology in
theorem exists_extension_pow (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ) (he : 0 < e)
    (hv : ∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e) :
    ∃ f : v.adicCompletion K →+* v'.adicCompletion L, Continuous f ∧
      (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧
      ∀ y, Valued.v (f y) = Valued.v y ^ e := by
  first
  | exact @_root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom
  | exact _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom
  | (apply _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom <;> assumption)
  | (intros; apply _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom ..)

end GlobalTheory.DenseCompl
end
