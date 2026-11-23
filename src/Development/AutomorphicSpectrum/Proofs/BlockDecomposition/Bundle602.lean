module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFour
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.InUQT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle594
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle590
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle010
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle595
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle229
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactUnitHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle509
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairLocalAuxiliaryStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfTwist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedOrbitalSwapConvolution
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle596

@[expose] public section

section


theorem _root_.GlobalTheory.T.unramified_quadratic_condition_four : PositivityTheory.SiegelWeilFormula.Gunr.Q4 := by
  first | exact @GlobalTheory.CompanionTheory.DiscriminantUnit.q4 | exact GlobalTheory.CompanionTheory.DiscriminantUnit.q4 | (intros; apply GlobalTheory.CompanionTheory.DiscriminantUnit.q4 <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution CrystallineSemistableComparison.Pb.LsQ

theorem _root_.GlobalTheory.T.witt_coord_quotient_pull_bijective : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ} (hn : n ≠ 0) {W : X.Opens} {d : ℕ} (cW : Coord q W d) (j : ℕ), Function.Bijective (((mqS q ρ hn {W}).o (IdF.span _ ((l : WittVector l k) ^ n)) (fun _ => le_rfl)).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal.local_bij | exact GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal.local_bij | (intros; apply GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal.local_bij <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

theorem _root_.GlobalTheory.T.constant_term_finite_of_smaller : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) → ∀ r, 0 < r → r < a → CTFin E a r := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.ctFin | exact GlobalTheory.CompanionTheory.CTFin.ctFin | (intros; apply GlobalTheory.CompanionTheory.CTFin.ctFin <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

theorem _root_.GlobalTheory.T.cube_theorem_of_perfect : GlobalTheory.SpreadingModels.PerfAll → GlobalTheory.Published.CubeTheorem := by
  first | exact @GlobalTheory.CompanionTheory.CubePerf.cubeTheorem_of_perfAll | exact GlobalTheory.CompanionTheory.CubePerf.cubeTheorem_of_perfAll | (intros; apply GlobalTheory.CompanionTheory.CubePerf.cubeTheorem_of_perfAll <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

theorem _root_.GlobalTheory.T.perfect_of_models : (∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f → ∀ M : LB Y, M.IsLB → GlobalTheory.SpreadingModels.HasModel f M) → GlobalTheory.SpreadingModels.PerfAll := by
  first | exact @GlobalTheory.CompanionTheory.SpreadingModels.perfAll_of_hasModel | exact GlobalTheory.CompanionTheory.SpreadingModels.perfAll_of_hasModel | (intros; apply GlobalTheory.CompanionTheory.SpreadingModels.perfAll_of_hasModel <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermVol

variable (D : D7) (r : ℕ)

def hermPart (x : Mx D r r) : Mx D r r := half D • (x + adj x)

variable {D r}

theorem hermPart_mem (x : Mx D r r) : hermPart D r x ∈ hermA D r := by
  change adj (hermPart D r x) = hermPart D r x
  rw [hermPart, adj_smul, cA_half, adj_add, adj_adj, add_comm]

theorem hermPart_of_mem {c : Mx D r r} (hc : c ∈ hermA D r) : hermPart D r c = c := by
  have h : adj c = c := hc
  rw [hermPart, h, smul_add, half_smul_add]

theorem hermPart_add (x y : Mx D r r) : hermPart D r (x + y) = hermPart D r x + hermPart D r y := by
  rw [hermPart, hermPart, hermPart, adj_add, add_add_add_comm, smul_add]

theorem hermPart_rat {x : Mx D r r} (hx : x ∈ ratMx D r r) : hermPart D r x ∈ ratMx D r r := by
  obtain ⟨γ, rfl⟩ := (mem_ratMx).1 hx
  refine (mem_ratMx).2 ⟨(1 / 2 : D.host.E) • (γ + γᴴ), ?_⟩
  rw [rat_smul, rat_add, rat_conjTranspose]; rfl


theorem continuous_hermPart : Continuous (hermPart D r) :=
  haveI : IsTopologicalAddGroup (Mx D r r) := (lattice_Mx D r r).1
  show Continuous fun x => half D • (x + adj x) from (continuous_id.add continuous_adj).const_smul (half D)

theorem isClosed_hermA : IsClosed (hermA D r : Set (Mx D r r)) :=
  haveI : T2Space (Mx D r r) := (lattice_Mx D r r).2.2.2.1
  isClosed_eq continuous_adj continuous_id

theorem isCoLat_herm : GlobalTheory.CuspGeneric.IsCoLat (ratHerm D r) := by
  obtain ⟨-, -, -, -, i5, K, hK, hKc⟩ := lattice_Mx D r r
  refine ⟨?_, ?_⟩
  · let φ : ratHerm D r → ratMx D r r := fun q => ⟨q.1.1, q.2⟩
    have hinj : Function.Injective φ := fun a b h =>
      Subtype.ext (Subtype.ext (by simpa [φ] using congrArg Subtype.val h))
    have hcont : Continuous φ :=
      ((continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hcont hinj
  · let P : Mx D r r → hermA D r := fun x => ⟨hermPart D r x, hermPart_mem x⟩
    have hP : Continuous P := continuous_hermPart.subtype_mk _
    refine ⟨P '' K, hK.image hP, fun x => ?_⟩
    obtain ⟨γ, hγ, hx⟩ := hKc x.1
    refine ⟨P γ, AddSubgroup.mem_comap.2 (hermPart_rat hγ), γ + x.1, hx, ?_⟩
    apply Subtype.ext
    change hermPart D r (γ + x.1) = hermPart D r γ + x.1
    rw [hermPart_add, hermPart_of_mem x.2]

theorem exists_isCovolOneH : ∀ (D : Formalism.BasicNotions.D7) (r : ℕ), ∃ (lam : Measure (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)) (𝓖 : Set (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)), PositivityTheory.GramSchwartzFunctions.BC.IsCovolOneH lam 𝓖 := by
  intro D r
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : LocallyCompactSpace (Mx D r r) := i2
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : T2Space (Mx D r r) := i4
  haveI : SecondCountableTopology (hermA D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D r) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : LocallyCompactSpace (hermA D r) := (isClosed_hermA (D := D) (r := r)).locallyCompactSpace
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ :=
    GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one (hermA D r) _ isCoLat_herm
  exact ⟨μ, 𝓕, hμ, hF, h1⟩

end GlobalTheory.CompanionTheory.HermVol
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.det_ne_zero_of_gram_nondegenerate : ∀ (D : D7) (W : HSp D) (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → x₀.det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.Frame.det_ne_zero_of_gramQ | exact GlobalTheory.CompanionTheory.ColumnSplitting.Frame.det_ne_zero_of_gramQ | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.Frame.det_ne_zero_of_gramQ <;> assumption)
end

section

open PositivityTheory.Rg.BcB.F.Eig

theorem _root_.GlobalTheory.T.compact_unit_holds : CompUnit := by
  first | exact @GlobalTheory.CompanionTheory.CompUnitary.compUnit | exact GlobalTheory.CompanionTheory.CompUnitary.compUnit | (intros; apply GlobalTheory.CompanionTheory.CompUnitary.compUnit <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have key : ∀ S : Subgroup H, S = ⊤ → ((S.index : ℂ))⁻¹ * ∑ᶠ _ : H ⧸ S, c = c := by
    rintro S rfl
    haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
    haveI : Unique (H ⧸ (⊤ : Subgroup H)) := Unique.mk' _
    rw [finsum_unique, Subgroup.index_top]
    simp
  exact key _ (by ext k; simp [rStab])

theorem ctT_split_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ν : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : w.adicCompletion E), IsSplitAt w → IsUnifV E w ϖ → ∀ (k : ℕ) (m : GLw a w × GLw b w), ctT h w ν ϖ k m = (ν ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) * (absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * hint (intMat a b w) fun X => Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) := by
  intro E _ _ _ n a b h w ν ϖ hw hϖ k m
  have hT : UL n w = ⊤ := if_pos hw
  have hv : ∀ y : GLw n w, ((toSub (UL n w) y : UL n w) : GLw n w) = y := fun y => by
    have hy : y ∈ UL n w := hT ▸ Subgroup.mem_top y
    simp [toSub, hy]
  have hc : ∀ (x : GLw n w) (g : GlobalTheory.LFun.KGL w (n := n)),
      Tj ℂ n (Ov E w) ϖ k ((g : GLw n w)⁻¹ * x * g) = Tj ℂ n (Ov E w) ϖ k x := fun x g =>
    (Tj_mem_hecke (n := n) hϖ k).1 g⁻¹ g x
  unfold ctT ctMu ct
  congr 2
  congr 1
  funext X
  simp only [hv, hc]
  exact avg_const (H := GlobalTheory.LFun.KGL w (n := n)) _

end GlobalTheory.CompanionTheory.CtS

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical


theorem _root_.GlobalTheory.T.aux_statement_22 : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (v : PlF E) (w : Above v), IsSplitAt w.1 →
  ∃ e : Yv a b v ≃ₜ* ((GLw a w.1 × GLw b w.1) × (GLw a w.1 × GLw b w.1)), (∀ y, (e y).1 = evw w y) ∧
    (∀ y, e (thv a b v y) = swTw (sgP a b w.1) (e y)) ∧ (∀ y, y ∈ Kv a b v ↔ e y ∈ (K2 a b w.1).prod (K2 a b w.1)) ∧
    ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), e (pv a b v (ratF E a δ₁, ratF E b δ₂)) =
      ((ratW a w.1 δ₁, ratW b w.1 δ₂),
        (ratW a w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₁),
         ratW b w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₂))) := by
  first | exact @GlobalTheory.CompanionTheory.SplitIso.split_iso | exact GlobalTheory.CompanionTheory.SplitIso.split_iso | (intros; apply GlobalTheory.CompanionTheory.SplitIso.split_iso <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finite_support_of_twist : PositivityTheory.Rg.BcB.G8.Fin.SuppFinOf := by
  first | exact @GlobalTheory.CompanionTheory.SuppFinTw.suppFinOf | exact GlobalTheory.CompanionTheory.SuppFinTw.suppFinOf | (intros; apply GlobalTheory.CompanionTheory.SuppFinTw.suppFinOf <;> assumption)
end

section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

theorem _root_.GlobalTheory.T.twisted_orbital_swap_convolution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (K L : Subgroup H) (N : H) (f₁ f₂ : H → ℂ),
  IsOpen (K : Set H) → IsCompact (K : Set H) → IsOpen (L : Set H) → L ≤ K → IsHecke L f₁ → IsHecke L f₂ → Good (MonoidHom.id H) K N →
  (∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C → ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d) →
  twOrb ((MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (N, 1) (fun y => f₁ y.1 * f₂ y.2) =
    twOrb (MonoidHom.id H) K N (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  first | exact @GlobalTheory.CompanionTheory.SplitSwap.main | exact GlobalTheory.CompanionTheory.SplitSwap.main | (intros; apply GlobalTheory.CompanionTheory.SplitSwap.main <;> assumption)
end
