module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle056
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle057
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle452
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle614
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle621
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftSideFormula
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle613
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle054
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree

namespace PureTuple

open NumberField IsDedekindDomain
open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem coord_projV (v : HeightOneSpectrum (𝓞 F)) {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin n → Fin M → Af F ⊗[F] E) (a : Fin n) (i : Fin M) (k : Fin d) :
    PureSB.coordH (Fv F v) b (projV v X a i) k = (PureSB.coordH (Af F) b (X a i) k) v :=
  PureSB.repr_map b (evalV F v) (X a i) k

theorem continuous_projV (v : HeightOneSpectrum (𝓞 F)) {d M n : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (projV v : (Fin n → Fin M → Af F ⊗[F] E) → Fin n → Fin M → Fv F v ⊗[F] E) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  have h : (fun X : Fin n → Fin M → Af F ⊗[F] E => projV v X a i) = fun X =>
      (PureSB.coordH (Fv F v) b).symm (fun k => (PureSB.coordH (Af F) b (X a i) k) v) := by
    funext X
    apply (PureSB.coordH (Fv F v) b).injective
    rw [Homeomorph.apply_symm_apply]
    funext k
    exact coord_projV v b X a i k
  rw [h]
  refine (PureSB.coordH (Fv F v) b).symm.continuous.comp (continuous_pi fun k => ?_)
  exact (RestrictedProduct.continuous_eval v).comp ((continuous_apply k).comp
    ((PureSB.coordH (Af F) b).continuous.comp ((continuous_apply i).comp (continuous_apply a))))

theorem projV_mem_latV (v : HeightOneSpectrum (𝓞 F)) {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin n → Fin M → Af F ⊗[F] E) :
    projV v X ∈ latV b v ↔ ∀ a i k, (PureSB.coordH (Af F) b (X a i) k) v ∈ v.adicCompletionIntegers F := by
  refine forall_congr' fun a => forall_congr' fun i => forall_congr' fun k => ?_
  rw [← coord_projV v b X a i k]
  rfl

variable {d M n : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F)))
  (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))


include b in
theorem isClosed_boxF (hA : ∀ v, IsCompact (A v)) : IsClosed (boxF A) := by
  have h : boxF A = ⋂ v, projV v ⁻¹' A v := by
    ext X
    exact ⟨fun h => Set.mem_iInter.2 h, fun h => Set.mem_iInter.1 h⟩
  rw [h]
  refine isClosed_iInter fun v => ?_
  haveI : T2Space (Fv F v ⊗[F] E) := (PureSB.coordH (Fv F v) b).isEmbedding.t2Space
  exact (hA v).isClosed.preimage (continuous_projV v b)

theorem isOpen_boxF (hA : ∀ v, IsOpen (A v)) (hS : ∀ v, v ∉ S → A v = latV b v) : IsOpen (boxF A) := by
  have hT : IsOpen {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem fun v => Valued.isOpen_valuationSubring _
  have hI : IsOpen {X : Fin n → Fin M → Af F ⊗[F] E | ∀ a i k,
      PureSB.coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} := by
    have e : {X : Fin n → Fin M → Af F ⊗[F] E | ∀ a i k,
        PureSB.coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} =
        ⋂ a, ⋂ i, ⋂ k, (fun X : Fin n → Fin M → Af F ⊗[F] E => PureSB.coordH (Af F) b (X a i) k) ⁻¹'
          {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [e]
    refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => ?_
    have hc : Continuous fun X : Fin n → Fin M → Af F ⊗[F] E => PureSB.coordH (Af F) b (X a i) k :=
      (continuous_apply k).comp
        ((PureSB.coordH (Af F) b).continuous.comp ((continuous_apply i).comp (continuous_apply a)))
    exact hT.preimage hc
  have h : boxF A = {X : Fin n → Fin M → Af F ⊗[F] E | ∀ a i k,
      PureSB.coordH (Af F) b (X a i) k ∈ {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}} ∩
      ⋂ v ∈ S, projV v ⁻¹' A v := by
    ext X
    constructor
    · intro hX
      refine ⟨fun a i k v hv => ?_, Set.mem_iInter₂.2 fun v _ => hX v⟩
      have := hX v
      rw [hS v hv] at this
      exact (projV_mem_latV v b X).1 this a i k
    · rintro ⟨h1, h2⟩ v
      by_cases hv : v ∈ S
      · exact Set.mem_iInter₂.1 h2 v hv
      · rw [hS v hv]
        exact (projV_mem_latV v b X).2 fun a i k => h1 a i k v hv
  rw [h]
  exact hI.inter (isOpen_biInter_finset fun v _ => (hA v).preimage (continuous_projV v b))

theorem isCompact_boxF (hA : ∀ v, IsCompact (A v)) (hS : ∀ v, v ∉ S → A v = latV b v) :
    IsCompact (boxF A) := by
  let B : Fin n → Fin M → Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) :=
    fun a i k v => (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => PureSB.coordH (Fv F v) b (Y a i) k) '' A v
  have hB : ∀ a i k v, IsCompact (B a i k v) := fun a i k v =>
    (hA v).image ((continuous_apply k).comp
      ((PureSB.coordH (Fv F v) b).continuous.comp ((continuous_apply i).comp (continuous_apply a))))
  have hBS : ∀ a i k v, v ∉ S →
      B a i k v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    rintro a i k v hv _ ⟨Y, hY, rfl⟩
    rw [hS v hv] at hY
    exact hY a i k
  let eW : (Fin n → Fin M → Af F ⊗[F] E) ≃ₜ (Fin n → Fin M → Fin d → Af F) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => PureSB.coordH (Af F) b
  have hL : IsCompact (eW ⁻¹' Set.pi Set.univ fun a => Set.pi Set.univ fun i => Set.pi Set.univ fun k =>
      {y : Af F | ∀ v, y v ∈ B a i k v}) :=
    eW.isCompact_preimage.2 (isCompact_univ_pi fun a => isCompact_univ_pi fun i =>
      isCompact_univ_pi fun k => PureSB.isCompact_box S (B a i k) (hB a i k) (hBS a i k))
  refine hL.of_isClosed_subset (isClosed_boxF b A hA) fun X hX a _ i _ k _ v => ?_
  exact ⟨projV v X, hX v, coord_projV v b X a i k⟩

end PureTuple

theorem pureN_isSchwartzBruhat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) → GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (pureN φ A) := by
  intro F E _ _ _ _ _ σ _ M J _ n _ _ d b S φ A hφ hA hS
  have hc := PureTuple.isCompact_boxF b S A (fun v => (hA v).1) hS
  have hcl := PureTuple.isClosed_boxF b A fun v => (hA v).1
  have ho := PureTuple.isOpen_boxF b S A (fun v => (hA v).2) hS
  refine GlobalTheory.Published.SiegelOneVector.isSchwartzBruhat_of_prod hφ (Φf := (boxF A).indicator fun _ => (1 : ℂ)) ⟨?_, ?_⟩ fun _ => rfl
  · exact (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) ⟨hcl, ho⟩).isLocallyConstant
  · exact HasCompactSupport.intro' hc hcl fun Y hY => Set.indicator_of_notMem hY _

end GlobalTheory.CompanionTheory.WhitFree
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open NumberField IsDedekindDomain
open scoped HeckeCharacterZeroLocus.SiegelWeilU

namespace GlobalTheory.CompanionTheory.WhitFree.CoefLim

theorem repr_map {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (f : A →ₐ[F] B) {d : ℕ} (b : Module.Basis (Fin d) F E) (y : A ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis B b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) k =
      f ((Algebra.TensorProduct.basis A b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_linear (L : (R ⊗[F] E) →ₗ[R] R) : Continuous L := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap L

theorem continuous_entry (σ : E →ₐ[F] E) {n : ℕ} (a c : Fin n) :
    Continuous fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => (B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a c :=
  (continuous_id.matrix_elem a c).comp continuous_subtype_val

theorem continuous_trace_pair [FiniteDimensional F E] (σ : E →ₐ[F] E) {n : ℕ}
    (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Continuous fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => Algebra.trace R (R ⊗[F] E)
      (Matrix.trace (T * (B : Matrix (Fin n) (Fin n) (R ⊗[F] E)))) := by
  have h : (fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => Algebra.trace R (R ⊗[F] E)
      (Matrix.trace (T * (B : Matrix (Fin n) (Fin n) (R ⊗[F] E))))) =
      fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => ∑ a, ∑ c, (Algebra.trace R (R ⊗[F] E) ∘ₗ LinearMap.mulLeft R (T a c))
        ((B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) c a) := by
    funext B

    simp [Matrix.trace, Matrix.mul_apply, map_sum]
  rw [h]
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ =>
    (continuous_linear _).comp (continuous_entry σ c a)

end Cont

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem mem_intH_iff (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n) :
    B ∈ intH σ b S ↔ ∀ v, v ∉ S → ∀ a i k, (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
      ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (a i : Fin n) (k : Fin d),
      (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b).repr
        (HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin (fun a i => (B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i)) a i) k =
      (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v := by
    intro v a i k
    simp only [HeckeCharacterZeroLocus.SiegelWeilU.projV, HeckeCharacterZeroLocus.SiegelWeilU.projFin]
    rw [repr_map, repr_map]
    rfl
  simp only [intH, HeckeCharacterZeroLocus.SiegelWeilU.latV, Set.mem_setOf_eq, key]

theorem measurableSet_intH (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSet (intH (n := n) σ b S) := by
  haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n) := ⟨rfl⟩
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  have hset : intH (n := n) σ b S = ⋂ v : HeightOneSpectrum (𝓞 F), ⋂ _ : v ∉ S, ⋂ a : Fin n, ⋂ i : Fin n,
      ⋂ k : Fin d, {B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n | (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F} := by
    ext B
    simp only [mem_intH_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hset]
  refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun a =>
    MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => ?_
  have hO : IsOpen (v.adicCompletionIntegers F : Set (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v)) := Valued.isOpen_valuationSubring _
  have hev : Continuous fun y : HeckeCharacterZeroLocus.SiegelWeilU.Af F => y v := RestrictedProduct.continuous_eval v
  have hsnd : Continuous (fun c : HeckeCharacterZeroLocus.SiegelWeilU.AF F => HeckeCharacterZeroLocus.SiegelWeilU.sndA F c) := continuous_snd
  have hc : Continuous fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n => (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
      ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v :=
    hev.comp (hsnd.comp ((continuous_linear (Finsupp.lapply k ∘ₗ
      (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr.toLinearMap)).comp (continuous_entry σ a i)))
  exact (hO.preimage hc).measurableSet

theorem eventually_mem_intH (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E) (B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n) :
    ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 F)) in Filter.atTop, B ∈ intH σ b S := by
  have hfin : ∀ (a i : Fin n) (k : Fin d), {v : HeightOneSpectrum (𝓞 F) |
      ¬ (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F}.Finite :=
    fun a i k => (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)).2
  have hall : ∀ (a i : Fin n) (k : Fin d), ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 F)) in Filter.atTop,
      ∀ v, v ∉ S → (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F := by
    intro a i k
    filter_upwards [Filter.eventually_ge_atTop (hfin a i k).toFinset] with S hS v hv
    by_contra hcon
    exact hv (hS ((hfin a i k).mem_toFinset.2 hcon))
  have hall' := Filter.eventually_all.2 fun a : Fin n => Filter.eventually_all.2 fun i : Fin n =>
    Filter.eventually_all.2 fun k : Fin d => hall a i k
  filter_upwards [hall'] with S hS
  exact (mem_intH_iff σ b S B).2 fun v hv a i k => hS a i k v hv

end Adelic

theorem coefS_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)) (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Integrable (starN σ J ψ dx Φ) db → ∀ T : Matrix (Fin n) (Fin n) E, Filter.Tendsto (fun S => coefS σ J ψ dx db Φ T b S) Filter.atTop (nhds (coefN σ J ψ dx db Φ T)) := by
  intro F E _ _ _ _ _ σ _ M J _ n _ _ ψ hψ dx db d b Φ hI T
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  obtain ⟨hψc, hψn, -, -⟩ := hψ
  have hchar : Continuous fun B : HermR (AF F) σ n =>
      ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace (T.map (inclR (AF F)) * (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))))) :=
    hψc.comp ((continuous_const.mul (continuous_trace_pair σ _)).neg)
  have hf := hI.aestronglyMeasurable.mul hchar.aestronglyMeasurable
  unfold coefS coefN
  refine tendsto_integral_filter_of_dominated_convergence (fun B => ‖starN σ J ψ dx Φ B‖) ?_ ?_ hI.norm ?_
  · refine Filter.Eventually.of_forall fun S => ?_
    have hind : Measurable ((intH (n := n) σ b S).indicator (fun _ => (1 : ℂ))) :=
      measurable_const.indicator (measurableSet_intH σ b S)
    exact hind.aestronglyMeasurable.mul hf
  · refine Filter.Eventually.of_forall fun S => Filter.Eventually.of_forall fun B => ?_
    have h1 : ‖(intH (n := n) σ b S).indicator (fun _ => (1 : ℂ)) B‖ ≤ 1 := by
      by_cases h : B ∈ intH (n := n) σ b S <;> simp [h]
    rw [norm_mul, norm_mul, hψn, mul_one]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  · refine Filter.Eventually.of_forall fun B => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_intH σ b B] with S hS
    simp only [Set.indicator_of_mem hS, one_mul]
    rfl

end GlobalTheory.CompanionTheory.WhitFree.CoefLim
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LFun PositivityTheory.JacquetShalikaLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JSUnit

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem norm_central (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ) (hp : ∀ φ, φ ≠ 0 → 0 < (H φ φ).re)
    (hi : ∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) {ω : HChar E} (hω : π.HasCentChar ω) (z) :
    ‖((ω.1 (finId E z) : ℂˣ) : ℂ)‖ = 1 := by
  have := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  obtain ⟨x, hx⟩ := exists_ne (0 : π.V)
  have h1 : π.op (.fin (GeneralLinearGroup.scalar (Fin a) z)) x = ((ω.1 (finId E z) : ℂˣ) : ℂ) • x := hω z x
  have h2 := hi (GeneralLinearGroup.scalar (Fin a) z) x x
  rw [h1] at h2
  generalize ((ω.1 (finId E z) : ℂˣ) : ℂ) = c at h2 ⊢
  simp only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
  have hne : H x x ≠ 0 := fun e => by
    have h := hp x hx
    simp [e] at h
  have h3 : starRingEnd ℂ c * c = 1 := mul_right_cancel₀ hne (by linear_combination h2)
  rw [Complex.conj_mul'] at h3
  have h4 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4

theorem norm_loc (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ) (hp : ∀ φ, φ ≠ 0 → 0 < (H φ φ).re)
    (hi : ∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) (χ : HChar E) {ω : HChar E} (hu : ω.IsUnitary)
    (hω : (π.twist χ).HasCentChar ω) (ha : a ≠ 0) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) :
    ‖((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ = 1 := by
  have e : (π.twist χ).twist χ⁻¹ = π := by
    rw [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]
  have h2 := hω.twist χ⁻¹
  rw [e] at h2
  have h3 := norm_central π H hp hi h2 (GeneralLinearGroup.det (locGL E a w g))
  rw [finId_det_locGL] at h3
  generalize GeneralLinearGroup.det g = u at h3 ⊢
  have h4 : ‖((ω.loc w u : ℂˣ) : ℂ)‖ = 1 := hu _
  have h5 : (ω * χ⁻¹ ^ a).loc w u = ω.loc w u * (χ.loc w u)⁻¹ ^ a := rfl
  change ‖(((ω * χ⁻¹ ^ a).loc w u : ℂˣ) : ℂ)‖ = 1 at h3
  rw [h5] at h3
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, norm_mul, norm_pow, norm_inv, h4,
    one_mul] at h3
  have h6 := (pow_eq_one_iff_of_nonneg (by positivity) ha).1 h3
  exact inv_eq_one.1 h6

theorem exists_unit_form : G1 := by
  intro E _ _ _ a π hu w
  obtain ⟨ω, hωu, hω⟩ := hu
  rw [CG.hasCentChar_mk] at hω
  obtain ⟨π₀, χ, hn, rfl⟩ := GlobalTheory.CompanionTheory.TwistNorm.exists_twist_normalised π
  obtain ⟨H, h1, h2, h3, -, -⟩ := GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian
    GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E a π₀ hn
  let T := π₀.toTwist χ
  have hT : ∀ g x, (π₀.twist χ).locRep w g (T x) =
      ((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • T (π₀.locRep w g x) := fun g x => by
    rw [CuspSub.locRep_eq, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, opMul, CuspSub.chiDet_locGL]
    rfl
  have hn1 : ∀ g : GL (Fin a) (w.adicCompletion E), ‖((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ = 1 := fun g => by
    rcases eq_or_ne a 0 with rfl | ha
    · rw [show GeneralLinearGroup.det g = 1 from Units.ext (by simp [Matrix.det_isEmpty]), map_one]
      simp
    · exact norm_loc π₀ H h2 h3 χ hωu hω ha w g
  refine ⟨(H.comp T.symm.toLinearMap).compl₂ T.symm.toLinearMap, ?_⟩
  refine And.intro (fun u v => ?_) (And.intro (fun u hu => ?_) fun g u v => ?_)
  · simpa using h1 (T.symm u) (T.symm v)
  · exact h2 _ (T.symm.map_ne_zero_iff.2 hu)
  · obtain ⟨u, rfl⟩ := T.surjective u
    obtain ⟨v, rfl⟩ := T.surjective v
    rw [hT, hT]
    generalize hc : ((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = c
    have hcc : starRingEnd ℂ c * c = 1 := by
      rw [Complex.conj_mul', ← hc, hn1 g]
      simp
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smulₛₗ, map_smul, LinearMap.smul_apply,
      LinearEquiv.symm_apply_apply, smul_eq_mul]
    rw [CuspSub.locRep_eq, h3, ← mul_assoc, RingHom.id_apply, mul_comm c, hcc, one_mul]

end GlobalTheory.CompanionTheory.JSUnit

end
end

section


theorem _root_.GlobalTheory.T.real_read_levi : PositivityTheory.Rg.BcB.F.Tail.RReadLev := by
  first | exact @GlobalTheory.CompanionTheory.ReadLevel.rReadLev | exact GlobalTheory.CompanionTheory.ReadLevel.rReadLev | (intros; apply GlobalTheory.CompanionTheory.ReadLevel.rReadLev <;> assumption)
end

section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.left_side_formula : Equi → CoCpt → LSide := by
  first | exact @GlobalTheory.CompanionTheory.SW.LS.lside | exact GlobalTheory.CompanionTheory.SW.LS.lside | (intros; apply GlobalTheory.CompanionTheory.SW.LS.lside <;> assumption)
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.exists_large_prime_in_ray_class : ∀ (F : Type) [Field F] [NumberField F] (𝔣 𝔞 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ → CoprimeTo F 𝔣 𝔞 → ∀ (W : Finset (𝓞 F)) (B : ℕ), (∀ x ∈ W, x ≠ 0) → ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ (Ideal.absNorm 𝔠).Prime ∧ B < Ideal.absNorm 𝔠 ∧ CoprimeTo F 𝔣 𝔠 ∧ RayRel F 𝔣 𝔠 𝔞 ∧ ∀ x ∈ W, x ∉ 𝔠 := by
  first | exact @GlobalTheory.CompanionTheory.DegOneRay.exists_degOne_prime_in_rayClass | exact GlobalTheory.CompanionTheory.DegOneRay.exists_degOne_prime_in_rayClass | (intros; apply GlobalTheory.CompanionTheory.DegOneRay.exists_degOne_prime_in_rayClass <;> assumption)
end
