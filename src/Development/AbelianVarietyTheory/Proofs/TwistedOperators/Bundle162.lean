module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle009
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField IsDedekindDomain

namespace GlobalTheory.QuadSymbol

theorem exists_basis_of_isQuadraticExtension (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] :
    ∃ (δ : K) (e : Module.Basis (Fin 2) K L), ¬ IsSquare δ ∧ e 0 = 1 ∧ e 1 * e 1 = algebraMap K L δ := by
  apply GlobalTheory.QuadSymbol.AlmostNorm.exists_basis_sq <;> assumption

theorem exists_completion_hom_real {K : Type} [Field K] (σ : K →+* ℝ) :
    ∃ (w : InfinitePlace K) (f : w.Completion →+* ℝ), ∀ x : K, f (algebraMap K w.Completion x) = σ x := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp
  have hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := InfinitePlace.isReal_mk_iff.2 hφ
  refine ⟨_, InfinitePlace.Completion.extensionEmbeddingOfIsReal hw, fun x => ?_⟩
  have he := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
    ((WithAbs.equiv _).symm x)
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply]
  refine Eq.trans he ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  simp

theorem normTheorem : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L], NormTheorem K L := by
  intro K L _ _ _ _ _ _ t
  obtain ⟨δ, e, hδ, h0, h1⟩ := exists_basis_of_isQuadraticExtension K L
  have : FiniteDimensional K L := Module.Finite.of_basis e
  refine ⟨fun h => ⟨fun v => toUnits_mem_normGroup _ h, fun w => toUnits_mem_normGroup _ h⟩, ?_⟩
  rintro ⟨hf, hi⟩
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hδ ⟨0, by simp⟩
  obtain ⟨a, b, hab⟩ := GlobalTheory.QNorm.hasseNormSt K δ t hδ0 t.ne_zero
    (fun σ => by
      obtain ⟨w, f, hw⟩ := exists_completion_hom_real σ
      obtain ⟨a, b, hab⟩ := (mem_normGroup_iff_form e h0 h1).1 (hi w)
      refine ⟨f a, f b, ?_⟩
      have h3 : algebraMap K w.Completion t = a ^ 2 - algebraMap K w.Completion δ * b ^ 2 := hab
      rw [← hw, ← hw, h3, map_sub, map_mul, map_pow, map_pow])
    (fun v => (mem_normGroup_iff_form e h0 h1).1 (hf v))
  refine mem_globalNorms_iff.2 ⟨a • e 0 + b • e 1, ?_⟩
  rw [hab]
  refine GlobalTheory.QuadNormBase.norm_of_basis e δ h0 ?_ a b
  rw [h1, h0, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.QuadSymbol
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.FinZeta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def KerGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {r : ℕ} (N : ℕ) (z : ℂˣ)
    (φ : GL (Fin r) (w.adicCompletion E) → ℂ) : Prop :=
  ∀ ϖ, IsUnifV E w ϖ → ∀ (d : Fin r → ℤ) (t : GL (Fin r) (w.adicCompletion E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
    ∀ k₁ ∈ KGL w (n := r), ∀ k₂ ∈ KGL w (n := r),
      φ (k₁ * t * k₂) = (z : ℂ) ^ (∑ i, d i) * (qV E w : ℂ) ^ (-((N : ℂ) / 2) * ((∑ i, |d i| : ℤ) : ℂ))

def KerU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ} (ϖ : L) (q N : ℕ) (z : ℂˣ)
    (φ : GU σ r → ℂ) : Prop :=
  ∀ (d : Fin r → ℤ) (t : GU σ r), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU σ r, ∀ k₂ ∈ KU σ r,
    φ (k₁ * t * k₂) = ((z : ℂ) * ((q : ℂ) ^ N)⁻¹) ^ (∑ i, max (d i) 0)

variable {D : D7}

abbrev Gv (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Type := GLoc D.sp.cm.sig V.gram v

abbrev Kv (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Subgroup (Gv V v) := stabLoc D.sp.cm.sig V.gram (frameLat V) v

abbrev embV (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Gv V v →* GA D V := emb D.sp.cm.sig V.gram v

abbrev projV (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : GA D V →* Gv V v := proj D.sp.cm.sig V.gram v

def IsLocKer (V : HSp D) (N : ℕ) (z : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : Gv V v → ℂ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v),
    (IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e → KerGL w N (z w) (φ ∘ e.symm)) ∧
    (IsInertAt D.host.F D.host.E v w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) →
      IsInertChart D.sp.cm.sig V.gram (frameLat V) h c e → KerU ϖ (qV D.host.F v) N (z w) (φ ∘ e.symm))

def VacFin (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) (latO S T (frameLat S) (frameLat T) fun u => u = v) f

def bddAut (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | Continuous f ∧ (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) ∧ ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C}
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl, 0, fun _ => by simp⟩
  add_mem' := by
    rintro f f' ⟨h1, h2, C, h3⟩ ⟨h1', h2', C', h3'⟩
    exact ⟨h1.add h1', fun γ hγ g => by simp [h2 γ hγ, h2' γ hγ], C + C',
      fun g => (norm_add_le _ _).trans (add_le_add (h3 g) (h3' g))⟩
  smul_mem' := by
    rintro c f ⟨h1, h2, C, h3⟩
    exact ⟨h1.const_smul c, fun γ hγ g => by simp [h2 γ hγ], ‖c‖ * C,
      fun g => (norm_smul c (f g)).le.trans (mul_le_mul_of_nonneg_left (h3 g) (norm_nonneg _))⟩

def bddRep (V : HSp D) : Representation ℂ (GA D V) (bddAut V) :=
  GlobalTheory.PRep.sub (GlobalTheory.PRep.rightReg ℂ (GA D V) ℂ) (bddAut V) (by
    rintro g f ⟨h1, h2, C, h3⟩
    haveI : IsTopologicalGroup (GA D V) := isTopologicalGroup_HA _ _ _
    exact ⟨h1.comp (continuous_mul_const g), fun γ hγ x => by
      show f (γ * x * g) = f (x * g)
      rw [mul_assoc, h2 γ hγ], C, fun x => h3 _⟩)

theorem coe_bddRep (V : HSp D) (g : GA D V) (f : bddAut V) : (bddRep V g f : GA D V → ℂ) = rTr V g f := rfl


open Classical in
def levDatum (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank)
    (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D) : WO S T → ℂ :=
  fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) then
    omegaG LT m (fun PP => redM PP (frMapAdj S T βS βT x)) * omegaQ Q T.rank m (-1) (fun PP => redM PP (frMapAdj S T βS βT x))
    else 0

open Classical in
theorem isLevelVec_iff {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)} {LT : LevDat D.host.E ℂ T.rank} {Q : Finset (Pl D.host.E)}
    {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsLevelVec ψ θ S T sT ΛS ΛT βS βT LT Q m f₀ f ↔
      IsVacO ψ θ S T (fun _ => 1) sT ΛS ΛT f₀ ∧ ∃ e : AE D, IsIdemSum e (LT.Pg ∪ Q) ∧
        IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀ (levDatum S T βS βT LT Q m e) f :=
  Iff.rfl

end GlobalTheory.FinZeta

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnfoldRat

def ratEquiv (D : D7) (m n : ℕ) : Matrix (Fin m) (Fin n) D.host.E ≃ GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n :=
  Equiv.ofBijective (fun ξ => ⟨ξ.map (incA D), ξ, rfl⟩)
    ⟨fun _ _ h => GlobalTheory.MixModel.rat_injective (congrArg Subtype.val h), fun ⟨_, ξ, hξ⟩ => ⟨ξ, Subtype.ext hξ⟩⟩

theorem countable_ratMx (D : D7) (m n : ℕ) : Countable (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : DiscreteTopology (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) := i5
  exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance

theorem countable_mat (D : D7) (m n : ℕ) : Countable (Matrix (Fin m) (Fin n) D.host.E) := by
  haveI := countable_ratMx D m n
  exact (ratEquiv D m n).injective.countable

theorem lintegral_unfold {D : D7} {m n : ℕ} {μ : Measure (Mx D m n)} {𝓨 : Set (Mx D m n)}
    (hcov : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) μ 𝓨) (φ : Mx D m n → ℝ≥0∞) :
    ∫⁻ u, φ u ∂μ = ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ t in 𝓨, φ (ξ.map (incA D) + t) ∂μ := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := countable_ratMx D m n
  haveI := hcov.1
  rw [hcov.2.1.lintegral_eq_tsum'' φ, ← (ratEquiv D m n).tsum_eq]
  rfl

theorem integral_unfold {D : D7} {m n : ℕ} {μ : Measure (Mx D m n)} {𝓨 : Set (Mx D m n)}
    (hcov : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) μ 𝓨) (φ : Mx D m n → ℂ) (hφ : Integrable φ μ) :
    ∫ u, φ u ∂μ = ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫ t in 𝓨, φ (ξ.map (incA D) + t) ∂μ := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := countable_ratMx D m n
  haveI := hcov.1
  rw [hcov.2.1.integral_eq_tsum'' φ hφ, ← (ratEquiv D m n).tsum_eq]
  rfl

theorem unfold : ∀ (D : D7) (m n : ℕ) (X : Type) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (ν : Measure X) [IsFiniteMeasure ν] (μ : Measure (Mx D m n)) (𝓨 : Set (Mx D m n)),
    IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) μ 𝓨 → ∀ (h : X → Mx D m n → ℂ), Continuous (Function.uncurry h) →
    ∀ M : ℝ, (∀ x u, Summable (fun ξ : Matrix (Fin m) (Fin n) D.host.E => ‖h x (ξ.map (incA D) + u)‖) ∧
      ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + u)‖ ≤ M) →
    Integrable (fun u => ∫ x, h x u ∂ν) μ ∧ ∫ u, (∫ x, h x u ∂ν) ∂μ =
      ∫ t in 𝓨, (∫ x, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, h x (ξ.map (incA D) + t) ∂ν) ∂μ := by
  intro D m n X _ _ _ _ ν _ μ 𝓨 hcov h hc M hM
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := countable_mat D m n
  haveI := hcov.1
  haveI : FirstCountableTopology (Mx D m n) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  have hr0 : (0 : Matrix (Fin m) (Fin n) D.host.E).map (incA D) = 0 := Matrix.map_zero _ (map_zero (incA D))

  have hb : ∀ x u, ‖h x u‖ ≤ M := fun x u => by
    have h0 := (hM x u).1.le_tsum 0 (fun _ _ => norm_nonneg _)
    rw [hr0, zero_add] at h0
    exact h0.trans (hM x u).2
  have hcx : ∀ x, Continuous (h x) := fun x => hc.comp (continuous_const.prodMk continuous_id)
  have hcu : ∀ u, Continuous fun x => h x u := fun u => hc.comp (continuous_id.prodMk continuous_const)
  have hmeas : Measurable (Function.uncurry h) := hc.measurable

  have hmx : ∀ x (ξ : Matrix (Fin m) (Fin n) D.host.E), Measurable fun t => ‖h x (ξ.map (incA D) + t)‖ₑ :=
    fun x ξ => ((hcx x).comp ((continuous_const.add continuous_id))).measurable.enorm
  have hmu : ∀ t (ξ : Matrix (Fin m) (Fin n) D.host.E), Measurable fun x => ‖h x (ξ.map (incA D) + t)‖ₑ :=
    fun t ξ => (hcu (ξ.map (incA D) + t)).measurable.enorm
  have hsum : ∀ x t, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + t)‖ₑ ≤ ENNReal.ofReal M := fun x t => by
    simp_rw [← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hM x t).1]
    exact ENNReal.ofReal_le_ofReal (hM x t).2
  have hlx : ∀ x, ∫⁻ u, ‖h x u‖ₑ ∂μ ≤ ENNReal.ofReal M := fun x => by
    have e1 : ∫⁻ t in 𝓨, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + t)‖ₑ ∂μ =
        ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ t in 𝓨, ‖h x (ξ.map (incA D) + t)‖ₑ ∂μ :=
      lintegral_tsum fun ξ => (hmx x ξ).aemeasurable
    rw [lintegral_unfold hcov (fun u => ‖h x u‖ₑ), ← e1]
    refine (lintegral_mono fun t => hsum x t).trans ?_
    rw [setLIntegral_const, hcov.2.2, mul_one]

  have hGc : Continuous fun u => ∫ x, h x u ∂ν :=
    continuous_of_dominated (bound := fun _ => M) (fun u => (hcu u).aestronglyMeasurable)
      (fun u => Filter.Eventually.of_forall fun x => hb x u) (integrable_const M)
      (Filter.Eventually.of_forall fun x => hcx x)

  have hGi : Integrable (fun u => ∫ x, h x u ∂ν) μ := by
    refine ⟨hGc.aestronglyMeasurable, ?_⟩
    have h1 : ∫⁻ u, ‖∫ x, h x u ∂ν‖ₑ ∂μ ≤ ∫⁻ u, ∫⁻ x, ‖h x u‖ₑ ∂ν ∂μ :=
      lintegral_mono fun u => enorm_integral_le_lintegral_enorm _
    have h2 : ∫⁻ u, ∫⁻ x, ‖h x u‖ₑ ∂ν ∂μ = ∫⁻ x, ∫⁻ u, ‖h x u‖ₑ ∂μ ∂ν :=
      lintegral_lintegral_swap (hmeas.enorm.comp measurable_swap).aemeasurable
    have h3 : ∫⁻ x, ∫⁻ u, ‖h x u‖ₑ ∂μ ∂ν ≤ ENNReal.ofReal M * ν Set.univ := by
      rw [← lintegral_const]; exact lintegral_mono fun x => hlx x
    exact lt_of_le_of_lt (h1.trans (h2.le.trans h3)) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
  refine ⟨hGi, ?_⟩
  rw [integral_unfold hcov _ hGi]

  have hA : ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ t in 𝓨, ‖∫ x, h x (ξ.map (incA D) + t) ∂ν‖ₑ ∂μ ≠ ∞ := by
    rw [← lintegral_unfold hcov (fun u => ‖∫ x, h x u ∂ν‖ₑ)]; exact hGi.2.ne
  have e3 : ∫ t in 𝓨, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫ x, h x (ξ.map (incA D) + t) ∂ν ∂μ =
      ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫ t in 𝓨, ∫ x, h x (ξ.map (incA D) + t) ∂ν ∂μ :=
    integral_tsum (fun ξ => (hGc.comp ((continuous_const.add continuous_id))).aestronglyMeasurable) hA
  rw [← e3]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)

  have hB : ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ x, ‖h x (ξ.map (incA D) + t)‖ₑ ∂ν ≠ ∞ := by
    have e2 : ∫⁻ x, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + t)‖ₑ ∂ν =
        ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫⁻ x, ‖h x (ξ.map (incA D) + t)‖ₑ ∂ν :=
      lintegral_tsum fun ξ => (hmu t ξ).aemeasurable
    rw [← e2]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun x => hsum x t) ?_)
    rw [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have e4 : ∫ x, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, h x (ξ.map (incA D) + t) ∂ν =
      ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ∫ x, h x (ξ.map (incA D) + t) ∂ν :=
    integral_tsum (fun (ξ : Matrix (Fin m) (Fin n) D.host.E) => (hcu (ξ.map (incA D) + t)).aestronglyMeasurable) hB
  exact e4.symm

end GlobalTheory.UnfoldRat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.Periodize

theorem integral_eq_setIntegral_tsum (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n))
    (hμ : μ.IsAddHaarMeasure) (hF : IsAddFundamentalDomain (ratMx D m n) 𝓕 μ) (c : Mx D m n → ℂ)
    (hc : Integrable c μ) :
    (∀ᵐ y ∂(μ.restrict 𝓕), Summable fun a : Matrix (Fin m) (Fin n) D.host.E => ‖c (y + a.map (incA D))‖) ∧
      ∫ y, c y ∂μ = ∫ y in 𝓕, ∑' a : Matrix (Fin m) (Fin n) D.host.E, c (y + a.map (incA D)) ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D m n) := i5
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance

  let e : Matrix (Fin m) (Fin n) D.host.E ≃ ratMx D m n :=
    Equiv.ofBijective (fun a => ⟨a.map (incA D), a, rfl⟩)
      ⟨fun a b h => Matrix.map_injective GlobalTheory.MixModel.incA_injective (congrArg Subtype.val h),
        fun γ => by obtain ⟨a, ha⟩ := γ.2; exact ⟨a, Subtype.ext ha⟩⟩
  have he : ∀ a, ((e a : ratMx D m n) : Mx D m n) = a.map (incA D) := fun _ => rfl

  have hm : ∀ γ : ratMx D m n, AEStronglyMeasurable (fun y => c (y + γ)) (μ.restrict 𝓕) := by
    intro γ
    have := hc.1.comp_quasiMeasurePreserving (measurePreserving_add_right μ (γ : Mx D m n)).quasiMeasurePreserving
    exact this.restrict

  have hl : ∑' γ : ratMx D m n, ∫⁻ y in 𝓕, ‖c (y + γ)‖ₑ ∂μ = ∫⁻ y, ‖c y‖ₑ ∂μ := by
    rw [hF.lintegral_eq_tsum'' (fun y => ‖c y‖ₑ)]
    refine tsum_congr fun γ => ?_
    simp only [AddSubgroup.vadd_def, vadd_eq_add, add_comm (γ : Mx D m n)]
  have hfin : ∑' γ : ratMx D m n, ∫⁻ y in 𝓕, ‖c (y + γ)‖ₑ ∂μ ≠ ⊤ := by
    rw [hl]; exact hc.2.ne

  have hae : ∀ᵐ y ∂(μ.restrict 𝓕), Summable fun γ : ratMx D m n => ‖c (y + γ)‖ := by
    have h1 : ∫⁻ y in 𝓕, ∑' γ : ratMx D m n, ‖c (y + γ)‖ₑ ∂μ ≠ ⊤ := by
      rw [lintegral_tsum fun γ => (hm γ).enorm]; exact hfin
    have h2 : AEMeasurable (fun y => ∑' γ : ratMx D m n, ‖c (y + γ)‖ₑ) (μ.restrict 𝓕) :=
      AEMeasurable.tsum fun γ => (hm γ).enorm
    filter_upwards [ae_lt_top' h2 h1] with y hy
    have : ∑' γ : ratMx D m n, (‖c (y + γ)‖₊ : ENNReal) ≠ ⊤ := by
      simpa only [enorm_eq_nnnorm] using hy.ne
    exact (NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 this)).congr fun _ => rfl
  refine ⟨?_, ?_⟩
  · filter_upwards [hae] with y hy
    exact (e.summable_iff.2 hy).congr fun a => by rw [Function.comp_apply, he]
  · have h3 : ∫ y in 𝓕, ∑' γ : ratMx D m n, c (y + γ) ∂μ = ∑' γ : ratMx D m n, ∫ y in 𝓕, c (y + γ) ∂μ :=
      integral_tsum hm hfin
    have h4 : ∫ y, c y ∂μ = ∑' γ : ratMx D m n, ∫ y in 𝓕, c (y + γ) ∂μ := by
      rw [hF.integral_eq_tsum' c hc, ← (Equiv.neg (ratMx D m n)).tsum_eq]
      refine tsum_congr fun γ => ?_
      simp only [Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add, add_comm (γ : Mx D m n)]
    rw [h4, ← h3]
    congr 1
    funext y
    rw [← e.tsum_eq]
    rfl

end GlobalTheory.Twist.Periodize
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoFrameAct

open scoped GlobalTheory.MixModel

theorem actO_isoPart_of_mul : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (a : GL (Fin r) (AE D)) (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → ∀ (h : GA D W) (z : Mx D W.rank r), actO V W m h (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C z) = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h) z) (GlobalTheory.MixModel.adj a.val)) := by
  intro D V W r C a m hm h z
  have e : (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram).map (incA D) =
      GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V := by
    change GlobalTheory.MixModel.rat (Cᴴ * V.gram) = _
    exact Matrix.map_mul
  have hg : GlobalTheory.MixModel.gA V * GlobalTheory.MixModel.giA V = 1 := by
    change (V.gram.map (incA D)) * (V.gram⁻¹.map (incA D)) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
    exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
  have hg' : GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.gA V = 1 := by
    change (V.gram⁻¹.map (incA D)) * (V.gram.map (incA D)) = 1
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
    exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
  have adjmul {l n k : ℕ} (x : Mx D l n) (y : Mx D n k) :
      GlobalTheory.MixModel.adj (x * y) = GlobalTheory.MixModel.adj y * GlobalTheory.MixModel.adj x :=
    Formalism.UG.cT_mul (cA D) x y
  have hinv : Formalism.L2.Theta.mt V m⁻¹ = GlobalTheory.MixModel.giA V *
      (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V) := by
    have hh : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V) * Formalism.L2.Theta.mt V m = 1 := by
      have hr : GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V m = GlobalTheory.MixModel.gA V := mt_rel V m
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (GlobalTheory.MixModel.adj _), hr, hg']
    rw [← Matrix.one_mul (Formalism.L2.Theta.mt V m⁻¹), ← hh, Matrix.mul_assoc]
    have hm_inv : Formalism.L2.Theta.mt V m * Formalism.L2.Theta.mt V m⁻¹ = 1 := by
      change (m.val * m⁻¹.val).val = 1
      exact congrArg Units.val (mul_inv_cancel m.val)
    rw [hm_inv, Matrix.mul_one]
  have key : GlobalTheory.MixModel.adj (C.map (incA D)) * (GlobalTheory.MixModel.gA V * (GlobalTheory.MixModel.giA V *
      (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V))) =
      GlobalTheory.MixModel.adj a.val * (GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V) := by
    rw [← Matrix.mul_assoc (GlobalTheory.MixModel.gA V), hg, Matrix.one_mul, ← Matrix.mul_assoc, ← adjmul, hm, adjmul,
      Matrix.mul_assoc]
  change Formalism.L2.Theta.mt W h * (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C z) * Formalism.L2.Theta.mt V m⁻¹ = _
  rw [hinv]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart]
  rw [e]
  simp only [Matrix.mul_assoc]
  rw [key]

end GlobalTheory.IsoFrameAct

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoPartPairing

open GlobalTheory.MixModel

theorem hO_isoPart {D : D7} (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1) (u y : Mx D W.rank r) :
    hO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) =
      (GlobalTheory.MixModel.adj y ⬝ (GlobalTheory.MixModel.gA W ⬝ u)).trace := by
  have hC0 : Cᴴ * V.gram * C' = 1 := hC
  have hC1 : C'ᴴ * V.gram * C = 1 := by
    have h := congrArg Matrix.conjTranspose hC0
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      GlobalTheory.MixModel.gram_conjTranspose, Matrix.conjTranspose_one, ← Matrix.mul_assoc] at h
  have hx : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u = u ⬝ rat (C'ᴴ * V.gram) := rfl
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y = y ⬝ rat (Cᴴ * V.gram) := rfl
  have hg : giA V ⬝ adj (rat (Cᴴ * V.gram)) = rat C := by
    rw [← rat_conjTranspose, Matrix.conjTranspose_mul, GlobalTheory.MixModel.gram_conjTranspose,
      Matrix.conjTranspose_conjTranspose, giA, ← rat_mul, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
  rw [hx, hz, hO_eq_trace, adj_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (giA V), hg]
  rw [show rat C ⬝ (adj y ⬝ (gA W ⬝ (u ⬝ rat (C'ᴴ * V.gram)))) = (rat C ⬝ adj y ⬝ gA W ⬝ u) ⬝ rat (C'ᴴ * V.gram) by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← rat_mul, hC1, rat_one,
    Matrix.one_mul, Matrix.mul_assoc]

theorem trHalf_add_self {D : D7} (z : AE D) :
    trHalf D z + trHalf D z = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * z) := by
  show algebraMap D.host.F (AF D.host.F) (1 / 2) * _ + algebraMap D.host.F (AF D.host.F) (1 / 2) * _ = _
  rw [← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

theorem symplOH_isoPart_add_self : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → ∀ u y : Mx D W.rank r, symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) + symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (HMul.hMul (GlobalTheory.MixModel.adj y) (HMul.hMul (GlobalTheory.MixModel.gA W) u)).trace) := by
  intro D V W r C C' hC u y
  rw [symplOH_eq, hO_isoPart V W C C' hC u y, trHalf_add_self]

end GlobalTheory.IsoPartPairing
end
end
