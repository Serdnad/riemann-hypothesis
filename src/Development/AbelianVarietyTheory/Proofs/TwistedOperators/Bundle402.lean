module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle374
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle373
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle375
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleIrreducibleTorusCharacters
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorMemSpanLocalHeisenbergTranslates
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle387
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffRapidDecayRealFunctional
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.trace_mul_endomorphism_isotypicRep : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible → (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) → IsIsotypicAlg π ρ → ∀ H : X →ₗ[ℂ] X, (∀ g x, H (ρ g x) = ρ g (H x)) → (∃ s : Finset (π.IntertwiningMap ρ), LinearMap.range H ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap) → ∃ c : ℂ, ∀ (A : N →ₗ[ℂ] N) (B : X →ₗ[ℂ] X), (∀ φ : π.IntertwiningMap ρ, B ∘ₗ φ.toLinearMap = φ.toLinearMap ∘ₗ A) → ∀ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace A b → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (H ∘ₗ B) (c * b) := by
  first | exact @GlobalTheory.IsoTrace.trace_mul_isotypic | exact GlobalTheory.IsoTrace.trace_mul_isotypic | (intros; apply GlobalTheory.IsoTrace.trace_mul_isotypic <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.parabolic_and_constant_term

section Star

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem starFn_tensor (fa : ∀ w, GArch σ J w → ℂ) (ff : ∀ v, GLoc σ J v → ℂ) :
    starFn (tensor σ J fa ff) = tensor σ J (fun w => starFn (fa w)) (fun v => starFn (ff v)) := by
  funext g
  simp only [starFn, tensor, map_mul, map_prod, map_inv]
  congr 1
  exact MonoidHom.map_finprod_of_injective (starRingEnd ℂ).toMonoidHom (starRingEnd ℂ).injective _

theorem starFn_unitLoc (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) :
    starFn (unitLoc σ J L v) = unitLoc σ J L v := by
  funext g
  by_cases hg : g ∈ stabLoc σ J L v
  · simp [starFn, unitLoc, hg, Set.indicator_of_mem, inv_mem hg]
  · have : g⁻¹ ∉ stabLoc σ J L v := fun h => hg (by simpa using inv_mem h)
    simp [starFn, unitLoc, hg, this]

theorem isFinFamily_starFn {L : Submodule (𝓞 E) (Fin n → E)} {ff : ∀ v, GLoc σ J v → ℂ}
    (h : IsFinFamily σ J L ff) : IsFinFamily σ J L (fun v => starFn (ff v)) :=
  ⟨fun v => starFn_mem_SB (h.1 v), h.2.mono fun v hv => by simp only [hv, starFn_unitLoc]⟩

end Star

theorem inConjParabolic_mono {k : Type} [Field k] {r : ℕ} {H H' : Subgroup (GL (Fin r) k)} (h : H ≤ H') {a : ℕ}
    (h' : InConjParabolic H' a) : InConjParabolic H a :=
  let ⟨g, hg⟩ := h'; ⟨g, fun p hp => hg p (h hp)⟩

theorem parabolicAtSplitPlaces : ParabolicAtSplitPlaces := by
  intro D V hodd T 𝔉 hP
  let i : Fin (𝔉.k + 1) := ⟨1, Nat.succ_lt_succ hP⟩
  have hi : i ≠ 0 := Fin.ne_of_val_ne one_ne_zero
  have hW := 𝔉.isIsotropic hi
  obtain ⟨h0, h2⟩ := GlobalTheory.T.totallyIsotropic_dim_bounds_oddRank D V hodd _ hW
  refine ⟨_, h0, h2, fun v => ?_⟩
  have hle : parAt 𝔉 (T.frame v) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (Fv D.host.F v.1) (𝔉.X i)).map
      ((T.frame v).equiv : GLoc D.sp.cm.sig V.gram v.1 →* GL (Fin V.rank) (Fv D.host.F v.1)) :=
    Subgroup.map_mono (𝔉.par_le_parab _ _ i)
  obtain ⟨h3, h4⟩ := GlobalTheory.T.isotropicStabilizer_splitPlace_inConjParabolics D V v.1 (T.frame v) _ hW
  exact ⟨inConjParabolic_mono hle h3, inConjParabolic_mono hle h4⟩

end GlobalTheory.Proof.parabolic_and_constant_term

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistSwap

open GlobalTheory.MixModel

variable {D : D7}

theorem covolOne_map {a b c d : ℕ} (f : Mx D a b ≃+ Mx D c d) (hf : Continuous f) (hfs : Continuous f.symm)
    (hΓ : ∀ x, f x ∈ ratMx D c d ↔ x ∈ ratMx D a b) {μ : Measure (Mx D a b)} {𝓖 : Set (Mx D a b)}
    (h : IsCovolOne (ratMx D a b) μ 𝓖) :
    IsCovolOne (ratMx D c d) (μ.map f) (f.symm ⁻¹' 𝓖) ∧
      ∀ g : Mx D c d → ℂ, ∫ x in f.symm ⁻¹' 𝓖, g x ∂(μ.map f) = ∫ y in 𝓖, g (f y) ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D a b
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D c d
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  haveI : BorelSpace (Mx D c d) := ⟨rfl⟩
  let m : Mx D a b ≃ᵐ Mx D c d :=
    { toEquiv := f.toEquiv
      measurable_toFun := hf.measurable
      measurable_invFun := hfs.measurable }
  have hm : (m : Mx D a b → Mx D c d) = f := rfl
  have hmp : MeasurePreserving m μ (μ.map f) := ⟨m.measurable, rfl⟩
  have hmp' : MeasurePreserving f.symm (μ.map f) μ := hmp.symm
  have hpre : f ⁻¹' (f.symm ⁻¹' 𝓖) = 𝓖 := by
    ext y; simp
  obtain ⟨hμ, hF, h1⟩ := h
  refine ⟨⟨f.isAddHaarMeasure_map μ hf hfs, ?_, ?_⟩, fun g => ?_⟩
  · let e : ratMx D a b → ratMx D c d := fun y => ⟨f y, (hΓ _).2 y.2⟩
    have he : Function.Bijective e := by
      constructor
      · intro x y hxy
        exact Subtype.ext (f.injective (congrArg Subtype.val hxy))
      · intro x
        refine ⟨⟨f.symm x, (hΓ _).1 (by simpa using x.2)⟩, Subtype.ext ?_⟩
        simp [e]
    refine hF.preimage_of_equiv hmp'.quasiMeasurePreserving he ?_
    intro y x
    simp [e, AddSubgroup.vadd_def]
  · rw [← hm, MeasurableEquiv.map_apply, hm, hpre, h1]
  · rw [← hm, m.measurableEmbedding.setIntegral_map, hm, hpre]

def swapE (S : HSp D) (t : ℕ) : Mx D S.rank t ≃+ Mx D t S.rank where
  toFun y := adj y ⬝ gA S
  invFun x := giA S ⬝ adj x
  left_inv y := by
    simp only [adj_mul, adj_gA, adj_adj, giA_gA_cancel]
  right_inv x := by
    simp only [adj_mul, adj_giA, adj_adj, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one]
  map_add' x y := by
    simp only [adj_add, Matrix.add_mul]

theorem swapE_apply (S : HSp D) (t : ℕ) (y : Mx D S.rank t) : swapE S t y = adj y ⬝ gA S := rfl

theorem swapE_symm_apply (S : HSp D) (t : ℕ) (x : Mx D t S.rank) : (swapE S t).symm x = giA S ⬝ adj x := rfl

theorem continuous_swapE (S : HSp D) (t : ℕ) : Continuous (swapE S t) :=
  continuous_adj.matrix_mul continuous_const

theorem continuous_swapE_symm (S : HSp D) (t : ℕ) : Continuous (swapE S t).symm :=
  continuous_const.matrix_mul continuous_adj

theorem swapE_mem_iff (S : HSp D) (t : ℕ) (y : Mx D S.rank t) :
    swapE S t y ∈ ratMx D t S.rank ↔ y ∈ ratMx D S.rank t := by
  constructor
  · intro hy
    have e : y = (swapE S t).symm (swapE S t y) := ((swapE S t).symm_apply_apply y).symm
    rw [e, swapE_symm_apply]
    exact ratMx_mul (rat_mem _) (ratMx_adj hy)
  · intro hy
    exact ratMx_mul (ratMx_adj hy) (rat_mem _)

theorem swapE_symm_mem_iff (S : HSp D) (t : ℕ) (x : Mx D t S.rank) :
    (swapE S t).symm x ∈ ratMx D S.rank t ↔ x ∈ ratMx D t S.rank := by
  rw [← swapE_mem_iff, AddEquiv.apply_symm_apply]

end GlobalTheory.TwistSwap

namespace GlobalTheory.TwistSwap

open GlobalTheory.MixModel

variable {D : D7}

theorem adjO_split (S T T' : HSp D) {t : ℕ} (ι : T'.V →ₗ[D.host.E] T.V) (C : Matrix (Fin T.rank) (Fin t) D.host.E)
    (y : Mx D S.rank t) (w' : WO T' S) :
    GlobalTheory.PairLift.adjO S T ((y : Matrix (Fin S.rank) (Fin t) (AE D)) *
                 GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ct C * T.gram) +
      (w' : Matrix (Fin S.rank) (Fin T'.rank) (AE D)) *
        GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (T'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ct (frameMat T T' ι) * T.gram)) =
    GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel C * (swapE S t y : Matrix (Fin t) (Fin S.rank) (AE D)) +
      GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (frameMat T T' ι) * GlobalTheory.PairLift.adjO S T' w' := by
  have e1 : ∀ {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel x = rat x := fun _ => rfl
  have e2 : ∀ {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ct x = xᴴ := fun _ => rfl
  have e3 : ∀ (A B : HSp D) (z : WO B A), GlobalTheory.PairLift.adjO A B z = giA B ⬝ adj z ⬝ gA A := fun _ _ _ => rfl
  have g1 : ∀ A : HSp D, rat A.gram = gA A := fun _ => rfl
  have g2 : ∀ A : HSp D, rat A.gram⁻¹ = giA A := fun _ => rfl
  rw [e3, e3, e1, e1, e1, e2, e2, swapE_apply]
  simp only [e1, rat_mul, rat_conjTranspose, g1, g2, adj_add, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc, giA_gA_cancel]

theorem res_dag_swap : ∀ (D : D7) (S T T' : HSp D) (t : ℕ) (ι : T'.V →ₗ[D.host.E] T.V) (C : Matrix (Fin T.rank) (Fin t) D.host.E), (∀ μ 𝓖, IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D t S.rank) μ 𝓖 → ∃ μ' 𝓖', IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D S.rank t) μ' 𝓖' ∧ ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS T T' S ι C μ' 𝓖' (GlobalTheory.PairLift.dag S T φ) = GlobalTheory.PairLift.dag S T' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT S T T' ι C μ 𝓖 φ)) ∧ ∀ μ' 𝓖', IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D S.rank t) μ' 𝓖' → ∃ μ 𝓖, IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D t S.rank) μ 𝓖 ∧ ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS T T' S ι C μ' 𝓖' (GlobalTheory.PairLift.dag S T φ) = GlobalTheory.PairLift.dag S T' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT S T T' ι C μ 𝓖 φ) := by
  intro D S T T' t ι C
  have key : ∀ (μ : Measure (Mx D t S.rank)) (𝓖 : Set (Mx D t S.rank)) (μ' : Measure (Mx D S.rank t))
      (𝓖' : Set (Mx D S.rank t)),
      (∀ G : Mx D t S.rank → ℂ, ∫ y in 𝓖', G (swapE S t y) ∂μ' = ∫ x in 𝓖, G x ∂μ) →
      ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS T T' S ι C μ' 𝓖' (GlobalTheory.PairLift.dag S T φ) =
        GlobalTheory.PairLift.dag S T' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT S T T' ι C μ 𝓖 φ) := by
    intro μ 𝓖 μ' 𝓖' hI φ
    funext w'
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT, GlobalTheory.PairLift.dag, adjO_split]
    rw [integral_conj, hI (fun x => φ (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel C * (x : Matrix (Fin t) (Fin S.rank) (AE D)) +
      GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (frameMat T T' ι) * GlobalTheory.PairLift.adjO S T' w'))]
  refine ⟨fun μ 𝓖 h => ?_, fun μ' 𝓖' h => ?_⟩
  · obtain ⟨h1, h2⟩ := covolOne_map (swapE S t).symm (continuous_swapE_symm S t) (continuous_swapE S t)
      (swapE_symm_mem_iff S t) h
    refine ⟨_, _, h1, key μ 𝓖 _ _ fun G => ?_⟩
    exact (h2 fun y => G (swapE S t y)).trans (by simp)
  · obtain ⟨h1, h2⟩ := covolOne_map (swapE S t) (continuous_swapE S t) (continuous_swapE_symm S t) (swapE_mem_iff S t) h
    exact ⟨_, _, h1, key _ _ μ' 𝓖' fun G => (h2 G).symm⟩

end GlobalTheory.TwistSwap
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowSizes

theorem sizes_of_sizeRows : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D := by
  intro D large₂ h
  obtain ⟨⟨Pm, _, _⟩, _, hmf, hm44, _⟩ := h
  refine ⟨?_, ?_⟩
  · have h1 := D.R.f_le_k
    have h2 : D.R.f = 2 * D.R.ord := rfl
    have h3 : D.R.r = D.R.k + D.R.m - 1 := rfl
    have h4 : 44 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm44 4
    omega
  · intro τ j hj
    have hg := (Pm.nodes_gap τ j hj).1
    have hf := Pm.heightBound_ge_rank_cubic
    have hN : ((GlobalTheory.Grid.bigN D : ℕ) : ℝ) = (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1) := by
      unfold GlobalTheory.Grid.bigN GlobalTheory.Grid.sLen; push_cast; ring
    have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    have key : ((2 * (GlobalTheory.Grid.bigN D : ℚ) ^ 3 : ℚ) : ℝ) <
        (((D.hc τ).b ⟨j + 1, hj⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := by
      push_cast at hg ⊢
      rw [hN]
      linarith
    exact_mod_cast key

end GlobalTheory.RowSizes
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLift

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem row_induction {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)
    (C : ∀ i, Set (Fn G (.grid i 0))) : ∀ (n : ℕ) (f : ∀ i : Fin n, Sch G (.right (i : ℕ) 0)),
    (∀ (i : Fin n) F, F ∈ C i → LiftConv W M (.right (i : ℕ) 0) (f i) F ∧
      liftA W M (.right (i : ℕ) 0) (f i) F ∈ C ((i : ℕ) + 1)) →
    ∀ F ∈ C 0, PathConv W M (rowPath T 0 n) (rowFam 0 n f) F ∧ liftP W M (rowPath T 0 n) (rowFam 0 n f) F ∈ C n
  | 0, _, _, _, hF => ⟨trivial, hF⟩
  | n + 1, f, h, F, hF => by
    have ih := row_induction W M C n (fun i => f i.castSucc) (fun i F hF => h i.castSucc F hF) F hF
    have := h (Fin.last n) _ ih.2
    exact ⟨⟨ih.1, this.1⟩, this.2⟩

theorem isAutFun_zero (V : HSp D) : IsAutFun V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, continuous_const⟩

theorem isAutFun_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsAutFun V f) (hg : IsAutFun V g) : IsAutFun V (f + g) := by
  obtain ⟨U, hU, h⟩ := hf.level
  obtain ⟨U', hU', h'⟩ := hg.level
  refine ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.left γ hγ x, hg.left γ hγ x], ⟨U ⊓ U', hU.inter hU', fun k hk hf x => ?_⟩,
    hf.cont.add hg.cont⟩
  simp only [Pi.add_apply, h k hk.1 hf x, h' k hk.2 hf x]

theorem isAutFun_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsAutFun V f) (a : ℂ) : IsAutFun V (a • f) := by
  obtain ⟨U, hU, h⟩ := hf.level
  refine ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.left γ hγ x], ⟨U, hU, fun k hk hf x => ?_⟩, hf.cont.const_smul a⟩
  simp only [Pi.smul_apply, h k hk hf x]

theorem isAutFun_of_mem_cusp (N : GlobalTheory.Grid.Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsAutFun N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have hU' : ∀ w, IsAutFun N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => (hx.aut w).toIsAutFun
    | zero => exact fun w => isAutFun_zero _
    | add x y _ _ hx hy => exact fun w => isAutFun_add (hx w) (hy w)
    | smul c x _ hx => exact fun w => isAutFun_smul (hx w) c
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using isAutFun_smul (hU' f) r
  | add x y hx hy => simpa using isAutFun_add hx hy

theorem start_mem {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (u : R.HE.H) :
    PiTensorProduct.lift (R.HE.e u) ∈ (GlobalTheory.Grid.nodeY R 0).Cusp R.θ := by
  have h1 : R.HE.e u ∈ R.EEat R.triv := h.models.HE.2.1 ▸ LinearMap.mem_range_self _ u
  have h2 := Formalism.IndefR.Mult.goodPart_le R.θ (R.MY 0) _ _ _ h1
  exact GlobalTheory.Grid.Node.multT_le_cusp (GlobalTheory.Grid.nodeY R 0) R.θ _ _ (Submodule.mem_map_of_mem h2)

theorem rowBase_of_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R :=
  ⟨h.lev, h.models.inf, h.models.νY, h.models.νY', h.models.νX⟩

end GlobalTheory.RowLift

end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.admissible_irreducible_torus_characters : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IwahoriTrace → GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.ExponentsSeparate → ∀ (D : D7) (V : HSp D) (U : AuxiliaryPlaceHermitianSpace V) (μ : Measure (Gv V U.u)), μ.IsHaarMeasure → ∀ (n : ℕ) (N : Fin n → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (π : ∀ i, Representation ℂ (Gv V U.u) (N i)), (∀ i, (π i).IsIrreducible) → (∀ i, IsAdmissible (π i)) → ∀ d : Fin n → ℂ, (∀ t ∈ strictTorus V.rank U.ϖ, ∀ b : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace μ (π i) (U.frame.cosetFn t) (b i)) → ∑ i, d i * b i = 0) → ∀ f ∈ CcLoc D.sp.cm.sig V.gram U.u, (∀ k ∈ U.frame.iwahori, ∀ g, f (k * g) = f g) → ∀ b : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace μ (π i) f (b i)) → ∑ i, d i * b i = 0 := by
  first | exact @GlobalTheory.IwahoriRel.relation_of_iwahoriTrace | exact GlobalTheory.IwahoriRel.relation_of_iwahoriTrace | (intros; apply GlobalTheory.IwahoriRel.relation_of_iwahoriTrace <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.localFactor_mem_span_localHeisenbergTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : FinPl D) (x : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → x ∈ Submodule.span ℂ (Set.range fun w : WO S T => heisO ψ S T (wAt (.inl v) w) f₀) := by
  first | exact @GlobalTheory.LocalSpan.mem_span_local | exact GlobalTheory.LocalSpan.mem_span_local | (intros; apply GlobalTheory.LocalSpan.mem_span_local <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LatSum

theorem norm_deriv_psi_symplO_lineAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : WO S T), ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ = 2 * Real.pi * |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ z (compAt θ τ w)| := by
  intro D ψ hψ θ hθ S T τ z w
  set a : ℝ := GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ z (compAt θ τ w) with ha
  have h2 : ∀ x y : WO S T, symplO S T x y = symplOH S T x y + symplOH S T x y := by
    intro x y
    unfold symplOH
    rw [← add_mul, ← map_add (f := _)]
    norm_num
  have hphase : ∀ t : ℝ, ψ (symplO S T (lineAt θ τ z t) w) =
      Complex.exp ((-(2 * Real.pi * Complex.I * (a : ℂ))) * (t : ℂ)) := by
    intro t
    rw [GlobalTheory.Asc.symplO_swap, h2, AddChar.map_neg_eq_inv, AddChar.map_add_eq_mul,
      GlobalTheory.ThetaDecay.psi_symplOH_lineAt hψ hθ S T w τ z t, ← Complex.exp_add, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have hfun : (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) =
      fun t : ℝ => Complex.exp ((-(2 * Real.pi * Complex.I * (a : ℂ))) * (t : ℂ)) := funext hphase
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((-(2 * Real.pi * Complex.I * (a : ℂ))) * (t : ℂ)))
      (-(2 * Real.pi * Complex.I * (a : ℂ))) 0 := by
    have h3 : HasDerivAt (fun u : ℂ => Complex.exp ((-(2 * Real.pi * Complex.I * (a : ℂ))) * u))
        (Complex.exp ((-(2 * Real.pi * Complex.I * (a : ℂ))) * ((0:ℝ):ℂ)) * ((-(2 * Real.pi * Complex.I * (a : ℂ))) * 1))
        ((0:ℝ):ℂ) :=
      ((hasDerivAt_id _).const_mul (-(2 * Real.pi * Complex.I * (a : ℂ)))).cexp
    refine h3.comp_ofReal.congr_deriv ?_
    simp
  rw [hfun, hd.deriv, norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  simp

end GlobalTheory.LatSum
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem toPair_mul (p : Pair T) (g k : GA D (G.V p.small)) (h k' : GA D (G.V p.big)) :
    G.toPair p (g * k) (h * k') = G.toPair p g h * G.toPair p k k' := by
  cases p <;> simp [GridData.toPair, map_mul]

theorem ker_mul (W : G.Weil) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (g k : GA D (G.V p.small))
    (h k' : GA D (G.V p.big)) : W.ker p f (g * k) (h * k') = W.ker p (W.om p (G.toPair p k k') f) g h := by
  simp only [GridData.Weil.ker, thetaKO, toPair_mul, Prod.fst_mul, Prod.snd_mul, ← Prod.mk_mul_mk, Prod.mk.eta, map_mul,
    Module.End.mul_apply]

end GlobalTheory.RowReal
end
end
