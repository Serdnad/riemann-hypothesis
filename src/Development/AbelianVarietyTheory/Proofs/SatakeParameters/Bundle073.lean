module

public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle233
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle236
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteContinuousCocyclesLocalGaloisRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle261
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle065
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle063
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle047
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle001
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

noncomputable section

namespace GlobalTheory.KerJ.RatPts

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Host NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.Mem.Chr (finPartI)

theorem isFin_finPart {L : Type} [Field L] [NumberField L] (a : Ideles L) : IsFinIdele (finPartI L a) := fun _ => rfl

end GlobalTheory.KerJ.RatPts

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host NumberField Classical Formalism.FrobeniusOrbits GlobalTheory.KerJ.RatPts

end GlobalTheory.KerJ
end
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section
namespace GlobalTheory.IrrTransfer

open Matrix

theorem span_top_of_irred_algClosed {Γ : Type} [Group Γ] {k K : Type} [Field k] [Field K] [IsAlgClosed K]
    {r : ℕ} (hr : 1 ≤ r) (rb : Γ →* GL (Fin r) k) (ι : k →+* K)
    (h : ∀ W : Submodule K (Fin r → K), IsInv (mapRep ι rb) W → W = ⊥ ∨ W = ⊤) :
    Submodule.span k (Set.range fun g => (rb g : Matrix (Fin r) (Fin r) k)) = ⊤ := by
  letI : Algebra k K := ι.toAlgebra
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hirr : IsIrrSub (mapRep ι rb) ⊤ :=
    ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => h W hW⟩
  have hs := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr
  apply GlobalTheory.BurnsideField.span_eq_top_of_span_map (K := K)
  convert hs using 3
  ext g a b
  simp [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep, RingHom.algebraMap_toAlgebra]

theorem span_image_top (k' : Type) [Field k'] (n : ℕ) :
    Submodule.span (AlgebraicClosure k')
      ((fun v : Fin n → k' => (algebraMap k' (AlgebraicClosure k')) ∘ v) ''
        ((⊤ : Submodule k' (Fin n → k')) : Set (Fin n → k'))) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  rw [pi_eq_sum_univ' u]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Pi.single a 1, trivial, ?_⟩)
  ext c
  by_cases hc : c = a
  · subst hc; simp
  · simp [Pi.single_eq_of_ne hc]

theorem absIrr_of_algClosed {Γ : Type} [Group Γ] {k K k' : Type} [Field k] [Field K] [IsAlgClosed K]
    [Field k'] {r : ℕ} (hr : 1 ≤ r) (rb : Γ →* GL (Fin r) k) (ι : k →+* K)
    (h : ∀ W : Submodule K (Fin r → K), IsInv (mapRep ι rb) W → W = ⊥ ∨ W = ⊤) (φ : k →+* k') :
    AbsIrrSub (mapRep φ rb) ⊤ := by
  have hsp := span_top_of_irred_algClosed hr rb ι h
  letI : Algebra k (AlgebraicClosure k') := ((algebraMap k' (AlgebraicClosure k')).comp φ).toAlgebra
  have hirr := GlobalTheory.BurnsideIff.eq_bot_or_top_of_span_eq_top (K := AlgebraicClosure k') _ hsp
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  rw [AbsIrrSub, span_image_top]
  refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => hirr W fun g v hv => ?_⟩
  have := hW g v hv
  simpa [mapRep, Matrix.map_map, RingHom.algebraMap_toAlgebra] using this

end GlobalTheory.IrrTransfer

namespace GlobalTheory.StringRepresentationDecomposition

theorem irr_transfer_absIrr : ∀ {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {k k' : Type} [Field k] [Field k']
    {r : ℕ}, 1 ≤ r → ∀ (rb : Γ →* GL (Fin r) k) (ι : k →+* Formalism.CyclotomicNorms.Fbar l),
    Formalism.CyclotomicNorms.IrredOn (mapRep ι rb) ⊤ → ∀ φ : k →+* k', AbsIrrSub (mapRep φ rb) ⊤ := by
  intro l _ Γ _ k k' _ _ r hr rb ι h φ
  exact GlobalTheory.IrrTransfer.absIrr_of_algClosed hr rb ι (fun W hW => h W fun g _ v hv => hW g v hv) φ

end GlobalTheory.StringRepresentationDecomposition
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.span_restrict_eq_top_of_absIrrSub_alt : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W), AbsIrrSub ρ W → Submodule.span k (Set.range fun g => (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ := by
  first | exact @GlobalTheory.BurnsideSub.span_restrict_eq_top_of_absIrrSub | exact GlobalTheory.BurnsideSub.span_restrict_eq_top_of_absIrrSub | (intros; apply GlobalTheory.BurnsideSub.span_restrict_eq_top_of_absIrrSub <;> assumption)
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

namespace GlobalTheory.LocalH1Finiteness

theorem matRep_apply' {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {k : ℕ}
    (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (g : ↥(GK K)) (v : Fin k → ↥LL.1) (a : Fin k) :
    matRep M g v a = ∑ b, M g a b * v b := rfl

theorem finite_continuous_cocycles_matRep (hK : Formalism.GaloisCohomology.LocalFinitenessK) {l : ℕ} [Fact l.Prime] (K LL : FinExt l)
    {k : ℕ} (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hM : Continuous fun g => M g)
    (hi : ∀ g a b, ‖((M g a b : ↥LL.1) : Om l)‖ ≤ 1) :
    Module.Finite ↥LL.1 (continuousCocycles (matRep M)) := by
  have := LL.2
  have := K.2
  let φ : Formalism.GaloisCohomology.GK l K.1 →* ↥(GK K) :=
    (IntermediateField.fixingSubgroupEquiv K.1).symm.toMonoidHom
  have hφ : Continuous φ := (GlobalTheory.fixingSubgroupEquiv_bicontinuous _ _ K.1).2
  have hφs : Function.Surjective φ := (IntermediateField.fixingSubgroupEquiv K.1).symm.surjective
  have hc : ReciprocityTheory.Gal.ContAction (matRep M) := by
    refine continuous_pi fun a => ?_
    simp only [matRep_apply']
    refine continuous_finsetSum _ fun b _ =>
      Continuous.mul ?_ ((continuous_apply b).comp continuous_snd)
    exact (hM.comp continuous_fst).matrix_elem a b
  have hn : ∀ g v, ‖matRep M g v‖ ≤ ‖v‖ := fun g v => by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun a => ?_
    rw [matRep_apply']
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg v) fun b _ => ?_
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hi g a b)).trans (norm_le_pi_norm v b)
  exact finite_cocycles_of_compact_cover (l := l) (matRep M) hc hn φ hφ hφs
    (fun r N _ _ _ _ _ rho hr hrho => (hK l K.1 K.2 r N rho hr hrho).2.1)

theorem finite_H1fV_matRep : Formalism.GaloisCohomology.LocalFinitenessK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (K LL : FinExt l) (k : ℕ) (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1),
    Continuous (fun g => M g) → (∀ g a b, ‖((M g a b : ↥LL.1) : Om l)‖ ≤ 1) →
    Module.Finite ↥LL.1 (FiniteCohomology (P.PD K) (matRep M)) := by
  intro hK l _ P K LL k M hM hi
  have h1 := finite_continuous_cocycles_matRep hK K LL M hM hi
  set_option synthInstance.maxHeartbeats 200000 in
  have h2 : Module.Finite ↥LL.1 (finiteCocycles (P.PD K) (matRep M)) :=
    Module.Finite.of_injective (Submodule.inclusion (fun _ hx => hx.1 :
      finiteCocycles (P.PD K) (matRep M) ≤ continuousCocycles (matRep M))) (Submodule.inclusion_injective _)
  exact Module.Finite.quotient _ _

end GlobalTheory.LocalH1Finiteness
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.RowTieLP

open GlobalTheory.WeilDeligne

theorem matrix_charpoly_smul {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (c : ℂ) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  by_cases hc : c = 0
  · subst hc
    ext i
    rw [zero_smul, Matrix.charpoly_zero, coeff_scaleRoots, M.charpoly_natDegree_eq_dim, coeff_X_pow]
    by_cases hi : i = Fintype.card n
    · subst hi
      have := M.charpoly_monic.coeff_natDegree
      rw [M.charpoly_natDegree_eq_dim] at this
      simp [this]
    · rcases lt_or_gt_of_ne hi with h | h
      · have : Fintype.card n - i ≠ 0 := by omega
        simp [hi, this]
      · simp [hi, coeff_eq_zero_of_natDegree_lt (p := M.charpoly) (by rwa [M.charpoly_natDegree_eq_dim])]
  · apply Polynomial.funext
    intro t
    have h1 : (M.charpoly.scaleRoots c).eval (c * (t / c)) = c ^ M.charpoly.natDegree * M.charpoly.eval (t / c) := by
      simpa using scaleRoots_eval₂_mul (RingHom.id ℂ) (t / c) c (p := M.charpoly)
    rw [mul_div_cancel₀ _ hc, M.charpoly_natDegree_eq_dim] at h1
    rw [h1, Matrix.eval_charpoly, Matrix.eval_charpoly, ← Matrix.det_smul]
    congr 1
    ext i j
    simp [Matrix.scalar_apply, Matrix.sub_apply, Matrix.diagonal_apply, mul_sub]
    split_ifs <;> field_simp

theorem charpoly_smul_end {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (c : ℂ) : (c • f).charpoly = f.charpoly.scaleRoots c := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, matrix_charpoly_smul,
    LinearMap.charpoly_toMatrix]

theorem charpoly_map_line {V L : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup L] [Module ℂ L] [FiniteDimensional ℂ L] (hL : Module.finrank ℂ L = 1)
    (f : Module.End ℂ V) (c : ℂ) :
    (TensorProduct.map f (c • (1 : Module.End ℂ L))).charpoly = f.charpoly.scaleRoots c := by
  let e : L ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq L ℂ (by simp [hL])
  let E : TensorProduct ℂ V L ≃ₗ[ℂ] V :=
    (TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)
  have key : ∀ x, E (TensorProduct.map f (c • (1 : Module.End ℂ L)) x) = (c • f) (E x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul v l =>
      simp [E, TensorProduct.map_tmul, smul_comm c, map_smul]
  have h2 : E.conj (TensorProduct.map f (c • (1 : Module.End ℂ L))) = c • f := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := E.surjective v
    simpa [LinearEquiv.conj_apply] using key x
  rw [← charpoly_smul_end, ← h2, LinearEquiv.charpoly_conj]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem inePol_char {a c : WD h} (hc : c.lpDim = 1) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B)
    {z : ℂ} (hz : c.inePol σ = X - C z) : (a.lpChar c).inePol σ = (a.inePol σ).scaleRoots z := by
  induction a using WD.ind with
  | hP m a =>
  induction c using WD.ind with
  | hP n c =>
    rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk] at hz
    rw [WD.lpDim_mk] at hc
    have h1 := LinearMap.aeval_self_charpoly (c.ρ (ineIncl h ⟨σ, hσ⟩))
    rw [hz, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h1
    rw [WD.lpChar_mk, WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.charPol_mk,
      WDRep.tensor_ρ, h1, charpoly_map_line hc]

end GlobalTheory.RowTieLP

theorem GlobalTheory.RowTieLP.main : ∀ (D : D7), WDTie D.nd D.naut → Formalism.MainNotions.SumRepresentations.At.TieLP D.nd D.naut := by
  intro D T w a b χ χ' s h1 h2
  obtain ⟨l1, l2, l3, l4, l5⟩ := (GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification _ _ _ _ _ T).2.1 w a b χ χ' s h1 h2
  refine ⟨l1, l2, l3, l4, l5, fun σ hσ => ⟨⟨?_, ?_⟩, fun c hc => ?_⟩⟩
  · rw [T.inePol w a σ hσ, GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ hσ]
    exact GlobalTheory.WeilDeligne.WD.charPol_monic _ _
  · rw [T.inePol w a σ hσ, GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ hσ, GlobalTheory.WeilDeligne.WD.charPol_natDegree, T.dim]
  · rw [T.inePol w χ σ hσ] at hc
    have hd : (T.e w χ).lpDim = 1 := by rw [T.dim, h1]
    rw [T.inePol w _ σ hσ, T.char _ _ _ h1, T.inePol w a σ hσ]
    exact GlobalTheory.RowTieLP.inePol_char hd hσ hc
end
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.ResidualRankCount

section Alg

variable {Γ : Type} [Group Γ]

theorem absIrr_id {K : Type} [Field K] [IsAlgClosed K] {n : ℕ} (hn : 1 ≤ n) (ρ : Γ →* GL (Fin n) K)
    (h : ∀ W : Submodule K (Fin n → K), IsInv ρ W → W = ⊥ ∨ W = ⊤) : AbsIrrSub ρ ⊤ := by
  first
  | exact @_root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top
  | exact _root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top
  | (apply _root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top ..)

theorem twGL_val {K : Type} [Field K] {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL _ K) : Matrix (Fin a) (Fin a) K) =
      (χ g : K) • ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K) := by
  show algebraMap K (Matrix (Fin a) (Fin a) K) (χ g : K) * ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K) = _
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem isInv_of_twGL {K : Type} [Field K] {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ)
    (W : Submodule K (Fin a → K)) (h : IsInv (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) W) : IsInv ρ W := by
  intro g v hv
  have h1 := W.smul_mem ((χ g : K)⁻¹) (h g v hv)
  rwa [twGL_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at h1

theorem charpoly_smul_inf {K : Type} [Field K] [Infinite K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K}
    (hc : c ≠ 0) : (c • M).charpoly = M.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

theorem charpoly_twGL {K : Type} [Field K] [Infinite K] {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL _ K) : Matrix (Fin a) (Fin a) K).charpoly =
      ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K).charpoly.scaleRoots (χ g : K) := by
  rw [twGL_val, charpoly_smul_inf _ (Units.ne_zero _)]

theorem charpoly_scal {K : Type} [Field K] (c : K) :
    (algebraMap K (Matrix (Fin 1) (Fin 1) K) c).charpoly = X - C c := by
  rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal, Fin.prod_univ_one]

theorem sub_fin_one {K : Type} [Field K] (W : Submodule K (Fin 1 → K)) : W = ⊥ ∨ W = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SatakeMainTheorem.main
  | exact _root_.GlobalTheory.SatakeMainTheorem.main
  | (apply _root_.GlobalTheory.SatakeMainTheorem.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SatakeMainTheorem.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SatakeMainTheorem.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SatakeMainTheorem.main ..)

theorem scaleRoots_list_prod {K : Type} [Field K] (l : List K[X]) (s : K) :
    l.prod.scaleRoots s = (l.map fun p => p.scaleRoots s).prod := by
  induction l with
  | nil => rw [List.prod_nil, one_scaleRoots, List.map_nil, List.prod_nil]
  | cons p l ih => rw [List.prod_cons, mul_scaleRoots_of_noZeroDivisors, ih, List.map_cons, List.prod_cons]

theorem charpoly_list_monic {K : Type} [Field K] (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (g : Γ) :
    (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod.Monic ∧
    (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod.natDegree =
      (L.map fun p => p.1).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ⟨(Matrix.charpoly_monic _).mul ih.1, ?_⟩
    rw [(Matrix.charpoly_monic _).natDegree_mul ih.1, ih.2, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

end Alg

section Lists

theorem prod_map_flatMap {α β M : Type} [CommMonoid M] (l : List α) (f : α → List β) (F : β → M) :
    ((l.flatMap f).map F).prod = (l.map fun a => ((f a).map F).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.map_append, List.prod_append, ih, List.map_cons, List.prod_cons]

theorem coe_flatMap {α β : Type} (l : List α) (f : α → List β) :
    ((l.flatMap f : List β) : Multiset β) = (l.map fun a => ((f a : List β) : Multiset β)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, List.sum_cons]

theorem prod_range_list {M : Type} [CommMonoid M] (f : ℕ → M) : ∀ d : ℕ,
    ∏ a ∈ Finset.range d, f a = ((List.range d).map f).prod
  | 0 => by simp
  | d + 1 => by
    rw [Finset.prod_range_succ, prod_range_list f d, List.range_succ, List.map_append, List.prod_append]
    simp

theorem sum_range_const {M : Type} [AddCommMonoid M] (x : M) : ∀ d : ℕ,
    ((List.range d).map fun _ => x).sum = d • x
  | 0 => by simp
  | d + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_const x d, succ_nsmul]
    simp

end Lists

section Psi

theorem exists_psi {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (NA : NAut N) (i : N.Loc)
    {B : Type} [CommRing B] [IsLocalRing B] (j : B →+* Qbar (N.l i)) (hj : Function.Injective j)
    (hran : Set.range j = {x : Qbar (N.l i) | ‖x‖ ≤ 1})
    (hmax : ∀ x : B, x ∈ IsLocalRing.maximalIdeal B ↔ ‖j x‖ < 1) :
    ∃ ψ : N.O i →+* B, (∀ a, j (ψ a) = iotaOQ N NA i a) ∧
      ∃ φ : IsLocalRing.ResidueField (N.O i) →+* IsLocalRing.ResidueField B,
        ∀ a, φ (IsLocalRing.residue (N.O i) a) = IsLocalRing.residue B (ψ a) := by
  have hmem : ∀ a, ∃ b, j b = iotaOQ N NA i a := fun a => by
    have : iotaOQ N NA i a ∈ Set.range j := by
      rw [hran]; exact Formalism.MainNotions.SumRepresentations.norm_iotaOQ_le_one N NA i a
    exact this
  choose f hf using hmem
  let ψ : N.O i →+* B :=
    { toFun := f
      map_one' := hj (by rw [hf, map_one, map_one])
      map_mul' := fun a b => hj (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := hj (by rw [hf, map_zero, map_zero])
      map_add' := fun a b => hj (by rw [hf, map_add (f := _), map_add (f := _), hf, hf]) }
  have hψ : ∀ a, j (ψ a) = iotaOQ N NA i a := hf
  refine ⟨ψ, hψ, Ideal.Quotient.lift (IsLocalRing.maximalIdeal (N.O i)) ((IsLocalRing.residue B).comp ψ)
    fun a ha => ?_, fun a => Ideal.Quotient.lift_mk _ _ _⟩
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, hmax, hψ]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (N.O i)
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at ha
  obtain ⟨b, rfl⟩ := ha
  rw [map_mul, norm_mul]
  calc ‖iotaOQ N NA i b‖ * ‖iotaOQ N NA i ϖ‖ ≤ 1 * ‖iotaOQ N NA i ϖ‖ := by
        gcongr; exact Formalism.MainNotions.SumRepresentations.norm_iotaOQ_le_one N NA i b
    _ < 1 := by rw [one_mul]; exact Formalism.MainNotions.SumRepresentations.norm_iotaOQ_irreducible N NA i hϖ

end Psi

end GlobalTheory.ResidualRankCount
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.heckeGaloisRepQbar_conjugate_unique : ∀ D : D7, SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (ρ ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ' → ∃ Pm : GL (Fin D.R.nV) (Qbar (D.nd.l i)), ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm := by
  first | exact @GlobalTheory.RepConjUniq.main | exact GlobalTheory.RepConjUniq.main | (intros; apply GlobalTheory.RepConjUniq.main <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem orderOf_moving (fr : Formalism.HC.Frame) (φ : fr.GG) (h : φ.1.2 = -1) : orderOf φ = Nat.lcm 2 (orderOf φ.2) :=
  UpperTheory.KStar.Words.orderOf_moving φ h

theorem orderOf_moving_stmt : ∀ {fr : Formalism.HC.Frame} (φ : fr.GG), φ.1.2 = -1 → orderOf φ = Nat.lcm 2 (orderOf φ.2) :=
  fun {fr} φ h => orderOf_moving fr φ h

end GlobalTheory
end
