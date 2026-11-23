module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle594
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle052
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RemainderTermSummable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546

@[expose] public section

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.quadExt_topological_properties : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ), FiniteDimensional F E ∧ IsTopologicalRing E ∧ ContinuousInv₀ E ∧ T2Space E ∧ Continuous c ∧ Continuous (Algebra.norm F : E → F) ∧ Continuous (Algebra.trace F E) ∧ ∀ (α ν : Type) [Fintype α] [Fintype ν], IsModuleTopology F (Matrix α ν E) ∧ Good (Matrix α ν E) := by
  first | exact @GlobalTheory.quadExt_topology | exact GlobalTheory.quadExt_topology | (intros; apply GlobalTheory.quadExt_topology <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMTypeImPos

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem denseRange_embeddings : DenseRange fun (x : E) (w : InfinitePlace E) => w.embedding x := by
  first
  | exact @_root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi
  | exact _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi
  | (apply _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi ..)

theorem exists_im_pos (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) : ∃ θ : E, ∀ i, 0 < (φ i θ).im := by
  classical

  let f : I → (InfinitePlace E → ℂ) → ℝ := fun i z =>
    if (InfinitePlace.mk (φ i)).embedding = φ i then (z (InfinitePlace.mk (φ i))).im
    else -(z (InfinitePlace.mk (φ i))).im
  have hfc : ∀ i, Continuous (f i) := by
    intro i
    by_cases h : (InfinitePlace.mk (φ i)).embedding = φ i
    · simp only [f, h, if_true]
      exact Complex.continuous_im.comp (continuous_apply _)
    · simp only [f, h, if_false]
      exact (Complex.continuous_im.comp (continuous_apply _)).neg
  let U : Set (InfinitePlace E → ℂ) := {z | ∀ i, 0 < f i z}
  have hU : IsOpen U := by
    have : U = ⋂ i, {z | 0 < f i z} := by ext z; simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (hfc i)

  let y : InfinitePlace E → ℂ := fun w => if ∃ j, w.embedding = φ j then Complex.I else -Complex.I
  have hy : y ∈ U := by
    intro i
    have hnr : ¬ ComplexEmbedding.IsReal (φ i) :=
      InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex _)
    rcases InfinitePlace.embedding_mk_eq (φ i) with h | h
    · have hex : ∃ j, (InfinitePlace.mk (φ i)).embedding = φ j := ⟨i, h⟩
      simp [f, y, h, hex]
    · have hne : (InfinitePlace.mk (φ i)).embedding ≠ φ i := by
        rw [h]; exact fun h' => hnr (ComplexEmbedding.isReal_iff.2 h')
      have hex : ¬ ∃ j, (InfinitePlace.mk (φ i)).embedding = φ j := by
        rintro ⟨j, hj⟩
        obtain ⟨k, _, hk⟩ := hφ (InfinitePlace.mk (φ i)).embedding
        have hi : i = k := hk i (Or.inr h)
        have hj' : j = k := hk j (Or.inl hj)
        subst hi; subst hj'
        exact hne hj
      simp [f, y, hne, hex]
  obtain ⟨θ, hθ⟩ := denseRange_embeddings.exists_mem_open hU ⟨y, hy⟩
  refine ⟨θ, fun i => ?_⟩
  have := hθ i
  rcases InfinitePlace.embedding_mk_eq (φ i) with h | h
  · simpa [f, h] using this
  · by_cases h' : (InfinitePlace.mk (φ i)).embedding = φ i
    · simpa [f, h'] using this
    · simp only [f, h', if_false] at this
      rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_im] at this
      linarith

end GlobalTheory.CMTypeImPos
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.exists_conj_idempotent_mod_prime_pow : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℕ), ∃ ε u v : 𝓞 D.F, ε + D.bar ε = 1 + (p : 𝓞 D.F) ^ r * u ∧ ε * D.bar ε = (p : 𝓞 D.F) ^ r * v := by
  first | (exact @GlobalTheory.UPel.HT.SplitIdem.exists_conj_idem) | (exact GlobalTheory.UPel.HT.SplitIdem.exists_conj_idem) | (intros; apply GlobalTheory.UPel.HT.SplitIdem.exists_conj_idem  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.exists_compatible_similitude_level_tower : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] (Q : Type) [CommGroup Q] (act : D.O → Q → Q) (W : ℕ → Q → Q → kˣ) (ζ : ℕ → kˣ), (∀ c a b, act c (a * b) = act c a * act c b) → (∀ r, ζ (r + 1) ^ p = ζ r) → (∀ r (a b : Q), a ^ (p ^ (r + 1)) = 1 → b ^ (p ^ (r + 1)) = 1 → W r (a ^ p) (b ^ p) = W (r + 1) a b ^ p) → (∀ r, ∃ f : D.La → Q, ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧ (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) ∧ ∀ x y, W r (f x) (f y) = ζ r ^ D.EF x y) → ∃ ev : ℕ → D.La → Q, (∀ r, ((∀ x y, ev r (x + y) = ev r x * ev r y) ∧ (∀ (c : D.O) x, ev r (c • x) = act c (ev r x)) ∧ (∀ x, ev r x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, ev r x = g)) ∧ ∀ x y, W r (ev r x) (ev r y) = ζ r ^ D.EF x y) ∧ ∀ r x, ev (r + 1) x ^ p = ev r x := by
  first | (exact @GlobalTheory.TowerLev.exists_compatible) | (exact GlobalTheory.TowerLev.exists_compatible) | (intros; apply GlobalTheory.TowerLev.exists_compatible  <;> assumption)
end

section

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.order_surjects_matrix_algebra_mod_prime_power : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal →
    (p : 𝓞 D.F) ∈ w0 →
    ∃ φ : D.O →ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⧸ w0 ^ r), Function.Surjective φ ∧
      ∀ b, φ b = 0 → b ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.O) := by
  first | (exact @GlobalTheory.UPel.HT.MatRed.exists_matRed) | (exact GlobalTheory.UPel.HT.MatRed.exists_matRed) | (intros; apply GlobalTheory.UPel.HT.MatRed.exists_matRed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.etale_torsion_subgroup_universal : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r r' : ℕ), r ≤ r' → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (H : Over S) (i : H ⟶ o.A), IsFinite H.hom → Etale H.hom → (∀ c ∈ w0 ^ r', i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x) → ∃ (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom ∧ Etale K.hom ∧ (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.exists_rep_pow_of_le) | (exact GlobalTheory.UPel.HT.EtLev.exists_rep_pow_of_le) | (intros; apply GlobalTheory.UPel.HT.EtLev.exists_rep_pow_of_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.torsion_subgroup_universal : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (H : Over S) (i : H ⟶ o.A), IsFinite H.hom → Flat H.hom → (∀ c ∈ w0 ^ r, i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (v : epsPtR x ⟶ o.A), spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → (∀ c ∈ w0 ^ r, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → v = 1) → Etale H.hom := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.etale_of_killed_tangent_trivial) | (exact GlobalTheory.UPel.HT.EtLev.etale_of_killed_tangent_trivial) | (intros; apply GlobalTheory.UPel.HT.EtLev.etale_of_killed_tangent_trivial <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_ringHom_order_pi_matrix_embeddings : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), ∃ φ : D.O →+* ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ), (∀ (c : 𝓞 D.F) τ, φ (algebraMap (𝓞 D.F) D.O c) τ = Matrix.scalar (Fin D.m) (τ (c : D.F))) ∧ Submodule.span ℂ (Set.range φ) = ⊤ := by
  first | exact @GlobalTheory.UPel.HT.SplitC.exists_ringHom_pi_matrix | exact GlobalTheory.UPel.HT.SplitC.exists_ringHom_pi_matrix | (intros; apply GlobalTheory.UPel.HT.SplitC.exists_ringHom_pi_matrix <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct


theorem _root_.GlobalTheory.T.exists_level_structure_on_torsion : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ∀ j : ℕ, ∃ f : (Fin (D.m * D.n) → 𝓞 D.F ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 D.F)}) → (Over.mk x ⟶ o.A), (∀ a a', f (a + a') = f a * f a') ∧ (∀ (c : 𝓞 D.F) a, f (Ideal.Quotient.mk (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 D.F)}) c • a) = f a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ∧ Function.Injective f ∧ ∀ g : Over.mk x ⟶ o.A, g ^ (ℓ ^ j) = 1 → ∃ a, f a = g := by
  first | (exact @GlobalTheory.QuotientCardinalityFinrank.torsion_points_free) | (exact GlobalTheory.QuotientCardinalityFinrank.torsion_points_free) | (intros; apply GlobalTheory.QuotientCardinalityFinrank.torsion_points_free  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.NormCover

theorem isIso_ι_of_eq_top {Z : Scheme.{0}} (V : Z.Opens) (hV : V = ⊤) : IsIso V.ι := by
  rw [← Z.isoOfEq_hom_ι hV, ← Z.topIso_hom]
  infer_instance

theorem isUnit_of_basicOpen_eq_top {Z : Scheme.{0}} (a : Γ(Z, ⊤)) (h : Z.basicOpen a = ⊤) : IsUnit a :=
  Z.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => (Z.mem_basicOpen _ x hx).1 (h.ge hx)

theorem preimage_eq_top {X Y₀ : Scheme.{0}} (U : X.Opens) (g : Y₀ ⟶ U) : (g ≫ U.ι) ⁻¹ᵁ U = ⊤ := by
  refine top_unique fun x _ => ?_
  change (g ≫ U.ι) x ∈ U
  rw [Scheme.Hom.comp_apply]
  exact (g x).2

theorem exists_normalization_of_etale {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X Y₀ : Scheme.{0}} (π : X ⟶ Sp R) [Smooth π] (U : X.Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (g : Y₀ ⟶ U) [IsFinite g] [Etale g] (hchar : ∀ y : Y₀, CharZero (Y₀.residueField y)) :
    ∃ (Y : Scheme.{0}) (s : Y ⟶ X) (i : Y₀ ⟶ Y), IsOpenImmersion i ∧ IsDominant i ∧ i ≫ s = g ≫ U.ι ∧
      IsFinite s ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧ Flat (s ≫ π) ∧
      IsLocallyNoetherian Y ∧
      ∀ (S : Scheme.{0}) (f : S ⟶ Y), Set.range (f ≫ s) ⊆ U → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f := by
  let s₀ := g ≫ U.ι
  haveI : QuasiCompact s₀ := inferInstance
  haveI : QuasiSeparated s₀ := inferInstance
  haveI : Smooth (s₀ ≫ π) := inferInstance
  haveI : GlobalTheory.IsNormalScheme Y₀ := GlobalTheory.isNormalScheme_of_smooth (s₀ ≫ π)
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : IsLocallyNoetherian Y₀ := LocallyOfFiniteType.isLocallyNoetherian (s₀ ≫ π)
  haveI : IsReduced Y₀ := inferInstance
  haveI hfin : IsFinite s₀.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_locallyOfFiniteType (o := CommRingCat.of R) s₀ π fun y _ => hchar y
  haveI : GlobalTheory.IsNormalScheme s₀.normalization := GlobalTheory.IsNormalScheme.normalization s₀
  have htop₀ : s₀ ⁻¹ᵁ U = ⊤ := preimage_eq_top U g
  haveI : IsIntegralHom (s₀ ∣_ U) := by
    haveI := isIso_ι_of_eq_top _ htop₀
    have e : s₀ ∣_ U = (s₀ ⁻¹ᵁ U).ι ≫ g := by
      rw [← cancel_mono U.ι, morphismRestrict_ι, Category.assoc]
    rw [e]
    infer_instance
  let W := s₀.fromNormalization ⁻¹ᵁ U
  haveI hiso : IsIso (s₀.toNormalization ∣_ W) := GlobalTheory.isIso_toNormalization_morphismRestrict s₀ U
  have htop : s₀.toNormalization ⁻¹ᵁ W = ⊤ := by
    refine top_unique fun x _ => ?_
    change s₀.fromNormalization (s₀.toNormalization x) ∈ U
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact (g x).2
  haveI := isIso_ι_of_eq_top _ htop
  have hi : s₀.toNormalization = inv (s₀.toNormalization ⁻¹ᵁ W).ι ≫ (s₀.toNormalization ∣_ W) ≫ W.ι := by
    rw [morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  haveI : Flat (s₀.toNormalization ≫ s₀.fromNormalization ≫ π) := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
    infer_instance
  refine ⟨s₀.normalization, s₀.fromNormalization, s₀.toNormalization, ?_, inferInstance,
    Scheme.Hom.toNormalization_fromNormalization s₀, hfin,
    fun y => ((GlobalTheory.isNormalScheme_iff _).mp inferInstance y).2,
    GlobalTheory.flat_normalization s₀ (s₀.fromNormalization ≫ π),
    LocallyOfFiniteType.isLocallyNoetherian s₀.fromNormalization, ?_⟩
  · rw [hi]
    infer_instance
  · intro S f hf
    have hr : Set.range f ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hf ⟨x, rfl⟩
    refine ⟨IsOpenImmersion.lift W.ι f hr ≫ inv (s₀.toNormalization ∣_ W) ≫ (s₀.toNormalization ⁻¹ᵁ W).ι, ?_⟩
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]

end GlobalTheory.UPel.HT.ES.NormCover

namespace GlobalTheory.UPel.HT.ES.NormCover

theorem exists_finite_normal_model : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (M : Model b N) (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ M.X) (g : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), IsFinite g → Etale g → g ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → ∃ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i ∧ IsDominant i ∧ i ≫ s = s₀ ∧ IsFinite s ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧ Flat (s ≫ M.s) ∧ IsLocallyNoetherian Y ∧ (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) := by
  intro p _ D R _ _ _ _ b N _ M Y₀ s₀ g hgf hge hs
  subst hs
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  have hp : IsUnit ((p : ℕ) : Γ(Y₀, ⊤)) := by
    apply isUnit_of_basicOpen_eq_top
    have h := preimage_eq_top (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) g
    rw [Scheme.Hom.preimage_basicOpen, map_natCast] at h
    exact h
  have hcop : ∀ m : ℕ, m.Coprime p → IsUnit ((m : ℕ) : Γ(Y₀, ⊤)) := by
    intro m hm
    have := (b.unit m hm).map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (g ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι ≫ M.s).appTop).hom
    rwa [map_natCast] at this
  have hunit : ∀ n : ℕ, n ≠ 0 → IsUnit ((n : ℕ) : Γ(Y₀, ⊤)) := by
    intro n hn
    obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
    push_cast
    exact (hp.pow a).mul (hcop m ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm).symm)
  have hchar : ∀ y : Y₀, CharZero (Y₀.residueField y) := by
    intro y
    refine charZero_of_inj_zero fun n hn => ?_
    by_contra h
    have := (hunit n h).map (Y₀.Γevaluation y).hom
    rw [map_natCast, hn] at this
    exact not_isUnit_zero this
  obtain ⟨Y, s, i, h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_normalization_of_etale M.s _ g hchar
  refine ⟨Y, s, i, h1, h2, h3, h4, h5, h6, h7, fun S f hpS => h8 S f ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ (f ≫ s) ⁻¹ᵁ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) := by
    rw [Scheme.Hom.preimage_basicOpen, map_natCast]
    have hpS' : IsUnit ((p : ℕ) : Γ(S, (f ≫ s) ⁻¹ᵁ ⊤)) := hpS
    exact (Scheme.basicOpen_of_isUnit S hpS').ge trivial
  exact hx

end GlobalTheory.UPel.HT.ES.NormCover
end
end

section

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

def Datum.VF : Type := D.VQ

instance Datum.acgVF : AddCommGroup D.VF := inferInstanceAs (AddCommGroup D.VQ)

instance Datum.modQVF : Module ℚ D.VF := inferInstanceAs (Module ℚ D.VQ)

instance Datum.modFVF : Module D.F D.VF :=
  Module.compHom D.VQ ((D.endO.val : D.endO →ₐ[ℚ] Module.End ℚ D.VQ).toRingHom.comp D.actF.toRingHom)

theorem Datum.smul_VF (x : D.F) (v : D.VF) :
    x • v = (((D.actF x : D.endO) : Module.End ℚ D.VQ) (v : D.VQ) : D.VF) := rfl

instance Datum.towerVF : IsScalarTower ℚ D.F D.VF :=
  ⟨fun q x v => by
    show ((D.actF (q • x) : D.endO) : Module.End ℚ D.VQ) v = q • ((D.actF x : D.endO) : Module.End ℚ D.VQ) v
    rw [map_smul]; rfl⟩

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime] (D : Datum p)

theorem Datum.finrank_VF : Module.finrank D.F D.VF = D.m * D.n := by
  have h1 : Module.finrank ℚ D.VF = D.m * D.n * Module.finrank ℚ D.F := by
    haveI := D.freeLa; haveI := D.finLa
    show Module.finrank ℚ (ℚ ⊗[ℤ] D.La) = _
    rw [Module.finrank_baseChange, D.rankLa]
  haveI : FiniteDimensional ℚ D.VF := D.finVQ
  haveI : FiniteDimensional D.F D.VF := Module.Finite.of_restrictScalars_finite ℚ D.F D.VF
  rw [← Module.finrank_mul_finrank ℚ D.F D.VF, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.MatUnit

open Module

variable {L U R : Type} [Field L] [AddCommGroup U] [Module L U] [Ring R] {m : ℕ}
  (σ : Matrix (Fin m) (Fin m) R →+* Module.End L U)

variable {A : Type} [Ring A] (α : A →+* Module.End L U)

end GlobalTheory.UPel.HT.MatUnit

section Main

open NumberField Matrix

end Main
end
end

section

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime] (D : Datum p)

def Datum.algO : Subalgebra ℚ (Module.End ℚ D.VQ) := Algebra.adjoin ℚ (Set.range D.actQ)

theorem Datum.actQ_mem_algO (b : D.O) : D.actQ b ∈ D.algO := Algebra.subset_adjoin ⟨b, rfl⟩

theorem Datum.centralizer_algO : Subalgebra.centralizer ℚ (D.algO : Set (Module.End ℚ D.VQ)) = D.endO := by
  apply le_antisymm
  · exact Subalgebra.centralizer_le ℚ _ _ (Algebra.subset_adjoin)
  · intro g hg
    rw [Subalgebra.mem_centralizer_iff]
    intro h hh
    have hle : D.algO ≤ Subalgebra.centralizer ℚ ({g} : Set (Module.End ℚ D.VQ)) := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨b, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact (D.mem_endO.1 hg b).symm
    exact ((Subalgebra.mem_centralizer_iff ℚ).1 (hle hh) g rfl).symm

instance Datum.nontrivialVQ : Nontrivial D.VQ := by
  apply Module.nontrivial_of_finrank_pos (R := ℚ)
  haveI := D.freeLa; haveI := D.finLa
  rw [Module.finrank_baseChange, D.rankLa]
  exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) Module.finrank_pos

end GlobalTheory.UPel.HT
end
end
