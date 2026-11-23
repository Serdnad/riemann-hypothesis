module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle580
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairFirstStep
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle581
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.CompanionTheory.EGlue

theorem _root_.GlobalTheory.T.pair_second_step : GlobalTheory.CompanionTheory.EGlue.PairSlices → GlobalTheory.CompanionTheory.EGlue.PairStep₂ := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.pairStep₂ | exact GlobalTheory.CompanionTheory.EGlue.pairStep₂ | (intros; apply GlobalTheory.CompanionTheory.EGlue.pairStep₂ <;> assumption)
end

section

open GlobalTheory.CompanionTheory.EGlue

theorem _root_.GlobalTheory.T.leaf_bound_alt : GlobalTheory.CompanionTheory.EGlue.DiscInf → GlobalTheory.CompanionTheory.EGlue.TopInf → GlobalTheory.CompanionTheory.EGlue.InfOfEq → GlobalTheory.CompanionTheory.EGlue.LeafBound := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.LeafB.leafBound | exact GlobalTheory.CompanionTheory.EGlue.LeafB.leafBound | (intros; apply GlobalTheory.CompanionTheory.EGlue.LeafB.leafBound <;> assumption)
end

section

open GlobalTheory.CompanionTheory.EGlue

theorem _root_.GlobalTheory.T.pair_first_step : GlobalTheory.CompanionTheory.EGlue.PairSlices → GlobalTheory.CompanionTheory.EGlue.PairStep₁ := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.TensorOne.pairStep₁_of_slices | exact GlobalTheory.CompanionTheory.EGlue.TensorOne.pairStep₁_of_slices | (intros; apply GlobalTheory.CompanionTheory.EGlue.TensorOne.pairStep₁_of_slices <;> assumption)
end

section

noncomputable section

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

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Form

theorem continuous_jn_pair {D : D7} {a r t n : ℕ} (hn : r + t = n) :
    Continuous fun z : Mx D a r × Mx D a t => jn hn z.1 z.2 := by
  unfold jn
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.submatrix_apply, id]
  cases (finSumFinEquiv.trans (finCongr hn)).symm j with
  | inl c => simpa using continuous_fst.matrix_elem i c
  | inr c => simpa using continuous_snd.matrix_elem i c

theorem continuous_yv_pair {D : D7} {r t : ℕ} (V : HSp D) (b₀ : HermE D r) :
    Continuous (yv (t := t) V b₀) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold yv ip
  exact continuous_const.matrix_mul ((continuous_adj.comp continuous_fst).matrix_mul
    (continuous_const.matrix_mul continuous_snd))

theorem nuT_form : ZpEq → AcEq → JnPi → Ext0 → Fub4 → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t)
    (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure →
    ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → ∀ Φ ∈ schwartzA θ B.rank n,
    ∀ η ∈ schwartzA θ W.rank t, Integrable (core hn I x₀ Φ η) (I.νK.prod (Q0 I μ)) →
    Integrable (fun z => Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z))) (nuT hn I μ x₀) ∧
    ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z)) ∂(nuT hn I μ x₀) =
      ∫ y, orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀) * conj (η y) ∂μ := by
  intro hZ hA hJ hE hF D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx Φ hΦ η hη hint
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  obtain ⟨-, -, p3, -, p5⟩ := top_mx (D := D) B.rank W.rank
  obtain ⟨-, -, p3', -, p5'⟩ := top_mx (D := D) B.rank t
  have hΦc := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ Φ hΦ).1
  have hηc := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ η hη).1
  have hGc : Continuous fun z : Mx D B.rank W.rank × Mx D B.rank t =>
      Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z)) :=
    (hΦc.comp (continuous_jn_pair hn)).mul
      (Complex.continuous_conj.comp (hηc.comp (continuous_yv_pair B b₀)))
  have hπ := measurable_pi hn I x₀
  have hcomp : (fun z : Mx D B.rank W.rank × Mx D B.rank t => Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z))) ∘
      (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) = core hn I x₀ Φ η := by
    funext p
    obtain ⟨k, q⟩ := p
    simp only [Function.comp, core]
    rw [hJ D n t B W d hn x₀ _ q, (hA D W.rank t B b₀ _ _).2.1, (hZ D n t B W d hn b₀ hb x₀ hx q).2.1]
  refine ⟨?_, ?_⟩
  · unfold nuT
    rw [integrable_map_measure hGc.aestronglyMeasurable hπ.aemeasurable, hcomp]
    exact hint
  · have e1 : ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z)) ∂(nuT hn I μ x₀) =
        ∫ p, core hn I x₀ Φ η p ∂(I.νK.prod (Q0 I μ)) := by
      unfold nuT
      rw [integral_map hπ.aemeasurable hGc.aestronglyMeasurable, ← hcomp]
      rfl
    rw [e1]
    obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
    obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
    obtain ⟨-, k2, k3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
    have : BorelSpace (GA D W) := ⟨rfl⟩
    obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
    have := hf.1
    have := I.haar
    have := I.probK
    have e2 := (hF I.l.K (GA D W) (Mx D t n) (Mx D W.rank t) I.νK I.m I.μ₁ μ).1 _ hint
    unfold Q0
    rw [e2]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [core]
    simp_rw [integral_mul_const]
    congr 1
    unfold orb
    refine integral_congr_ae (ae_of_all _ fun h => ?_)
    simp only [hE D n t W hn x₀ h, ikp, ikS, projS, XU]
    refine integral_congr_ae (ae_of_all _ fun u => integral_congr_ae (ae_of_all _ fun k => ?_))
    simp only [mm, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.ColumnSplitting.Form

end
end

section

noncomputable section

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

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem nuT_shear_invariant : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
    (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (y : Mx D W.rank t),
    (nuT hn I μ x₀).map (fun z => (z.1, z.2 + mm z.1 y)) = nuT hn I μ x₀ := by
  intro D n t B W d hn I μ hμ x₀ y
  have hring := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨i1, i2, i3, i4, i5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) t n
  obtain ⟨k1, -, -, -, -⟩ := top_mx (D := D) B.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  have := I.probK
  have hQ := sigmaFinite_parameter_product_measure I μ hμ
  obtain ⟨p1, p2⟩ := top_pair (D := D) B.rank W.rank t
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := p1.opensMeasurable
  have hS : Measurable fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, z.2 + mm z.1 y) :=
    (continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))).measurable
  have hτ : MeasurePreserving (fun p : I.l.K × Par D n t W => (p.1, p.2.1, p.2.2.1, p.2.2.2 + y))
      (I.νK.prod (Q0 I μ)) (I.νK.prod (Q0 I μ)) := by
    unfold Q0
    exact (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod
      ((MeasurePreserving.id _).prod (measurePreserving_add_right μ y)))
  have hπ := measurable_pi (d := d) hn I x₀
  have hcomp : (fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, z.2 + mm z.1 y)) ∘
        (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) =
      (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ∘
        (fun p : I.l.K × Par D n t W => (p.1, p.2.1, p.2.2.1, p.2.2.2 + y)) := by
    funext p
    refine Prod.ext rfl ?_
    have key : ∀ {a b c : ℕ} (g : Mx D a a) (ξ : Mx D a b) (u : Mx D a c) (y' y : Mx D b c),
        mm g (mm ξ y' + u) + mm (mm g ξ) y = mm g (mm ξ (y' + y) + u) := by
      intro a b c g ξ u y' y
      simp only [mm, Matrix.mul_add, Matrix.mul_assoc]
      abel
    exact key _ _ _ _ _
  unfold nuT
  rw [Measure.map_map hS hπ, hcomp, ← Measure.map_map hπ hτ.measurable, hτ.map_eq]

end GlobalTheory.CompanionTheory.ColumnSplitting

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

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem sand {k l a b c : ℕ} (G : Mx D k k) (x : Mx D k l) (u : Mx D l a) (y : Mx D k b) (v : Mx D b c) :
    adj (x ⬝ u) ⬝ (G ⬝ (y ⬝ v)) = adj u ⬝ ((adj x ⬝ (G ⬝ y)) ⬝ v) := by
  simp only [adj_mul, Matrix.mul_assoc]

theorem gram_ww (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : GA D W) :
    adj (ww W x₀ h) ⬝ (gA W ⬝ ww W x₀ h) = rat (gramQ W x₀) := by
  have hu := mt_unitary W h⁻¹
  have hr : adj (rat x₀) ⬝ (gA W ⬝ rat x₀) = rat (gramQ W x₀) :=
    gram_rat W (a := x₀) (b := x₀) (c := gramQ W x₀) (by
      show x₀ᴴ * W.gram * x₀ = x₀ᴴ * (W.gram * x₀)
      rw [Matrix.mul_assoc])
  have e : adj (ww W x₀ h) ⬝ (gA W ⬝ ww W x₀ h)
      = adj (rat x₀) ⬝ ((adj (mt W h⁻¹) ⬝ (gA W ⬝ mt W h⁻¹)) ⬝ rat x₀) :=
    sand (gA W) (mt W h⁻¹) (rat x₀) (mt W h⁻¹) (rat x₀)
  rw [e, hu, hr]

theorem frame_perp (d : HypDec B W t) {a c : ℕ} (u : Mx D t a) (w : Mx D W.rank a) (v : Mx D t c) :
    adj (d.jX ⬝ u + d.j0 ⬝ w) ⬝ (gA B ⬝ (d.jX ⬝ v)) = 0 := by
  rw [adj_add, Matrix.add_mul, sand, sand, d.gram_XX, d.gram_0X]
  simp

theorem frame_gram (d : HypDec B W t) {a : ℕ} (u : Mx D t a) (w : Mx D W.rank a) :
    adj (d.jX ⬝ u + d.j0 ⬝ w) ⬝ (gA B ⬝ (d.jX ⬝ u + d.j0 ⬝ w)) = adj w ⬝ (gA W ⬝ w) := by
  have h1 := frame_perp d u w u
  have h2 : adj (d.jX ⬝ u + d.j0 ⬝ w) ⬝ (gA B ⬝ (d.j0 ⬝ w)) = adj w ⬝ (gA W ⬝ w) := by
    rw [adj_add, Matrix.add_mul, sand, sand, d.wittDecomp_gram_X_anisotropic, d.gram_00]
    simp
  rw [Matrix.mul_add, Matrix.mul_add, h1, h2, zero_add]

theorem pair_gram (d : HypDec B W t) (b₀ : HermE D W.rank) (hdet : b₀.1.det ≠ 0) (ξ : Mx D B.rank W.rank) (v : Mx D t t)
    (y : Mx D W.rank t) (hg : adj ξ ⬝ (gA B ⬝ ξ) = rat b₀.1) (hp : adj ξ ⬝ (gA B ⬝ (d.jX ⬝ v)) = 0) :
    yv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v) = y ∧ qv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v) = 0 := by
  have h2 : adj ξ ⬝ (gA B ⬝ (ξ ⬝ y + d.jX ⬝ v)) = rat b₀.1 ⬝ y := by
    rw [Matrix.mul_add, Matrix.mul_add, hp, add_zero, ← Matrix.mul_assoc (gA B), ← Matrix.mul_assoc (adj ξ), hg]
  have hinv : rat b₀.1⁻¹ ⬝ rat b₀.1 = (1 : Mx D W.rank W.rank) := by
    rw [← rat_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), rat_one]
  have h3 : yv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v) = y := by
    show rat b₀.1⁻¹ ⬝ (adj ξ ⬝ (gA B ⬝ (ξ ⬝ y + d.jX ⬝ v))) = y
    rw [h2, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hxξ : adj (d.jX ⬝ v) ⬝ (gA B ⬝ ξ) = 0 := by
    have := gram_swap B hp
    rwa [adj_zero] at this
  have hxx : adj (d.jX ⬝ v) ⬝ (gA B ⬝ (d.jX ⬝ v)) = 0 := by
    rw [sand, d.gram_XX]
    simp
  have hq : adj (d.jX ⬝ v) ⬝ (gA B ⬝ (ξ ⬝ y + d.jX ⬝ v)) = 0 := by
    rw [Matrix.mul_add, Matrix.mul_add, hxx, add_zero, ← Matrix.mul_assoc (gA B), ← Matrix.mul_assoc (adj (d.jX ⬝ v)),
      hxξ, Matrix.zero_mul]
  have h4 : ip B (ξ ⬝ y + d.jX ⬝ v) (ξ ⬝ y + d.jX ⬝ v) = adj y ⬝ (rat b₀.1 ⬝ y) := by
    show adj (ξ ⬝ y + d.jX ⬝ v) ⬝ (gA B ⬝ (ξ ⬝ y + d.jX ⬝ v)) = _
    rw [adj_add, Matrix.add_mul, hq, add_zero, adj_mul ξ y, Matrix.mul_assoc, h2]
  refine ⟨h3, ?_⟩
  show ip B (ξ ⬝ y + d.jX ⬝ v) (ξ ⬝ y + d.jX ⬝ v)
    - pr b₀ (yv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v)) (yv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v)) = 0
  rw [h3, h4]
  exact sub_eq_zero.2 rfl

theorem zp_eq : ZpEq := by
  intro D n t B W d hn b₀ hdet x₀ hx p
  have hg : adj (d.jX ⬝ c1 hn p.2.1 + d.j0 ⬝ ww W x₀ p.1) ⬝ (gA B ⬝ (d.jX ⬝ c1 hn p.2.1 + d.j0 ⬝ ww W x₀ p.1)) = rat b₀.1 := by
    rw [frame_gram, gram_ww, hx]
  have hp := frame_perp d (c1 hn p.2.1) (ww W x₀ p.1) (c2 hn p.2.1)
  obtain ⟨h3, h5⟩ := pair_gram d b₀ hdet _ (c2 hn p.2.1) p.2.2 hg hp
  exact ⟨hg, h3, h5⟩

end GlobalTheory.CompanionTheory.ColumnSplitting

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

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

variable {D : D7}

theorem continuous_adjM {a b : ℕ} : Continuous (adj : Mx D a b → Mx D b a) := by
  have hc : Continuous (cA D) := GlobalTheory.FockCompare.ThetaCont.continuous_conj
  exact (continuous_id.matrix_map hc).matrix_transpose

theorem continuous_ipM {X : Type} [TopologicalSpace X] (V : HSp D) {a b : ℕ} {f : X → Mx D V.rank a}
    {g : X → Mx D V.rank b} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => ip V (f x) (g x) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact (continuous_adjM.comp hf).matrix_mul (continuous_const.matrix_mul hg)

theorem continuous_qvM (V : HSp D) {r t : ℕ} (b₀ : HermE D r) :
    Continuous (qv (t := t) V b₀) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hT := (top_mx (D := D) t t).1
  have hy : Continuous (yv (t := t) V b₀) :=
    continuous_const.matrix_mul (continuous_ipM V continuous_fst continuous_snd)
  have h2 : Continuous fun z : Mx D V.rank r × Mx D V.rank t => ip V z.2 z.2 :=
    continuous_ipM V continuous_snd continuous_snd
  have h3 : Continuous fun z : Mx D V.rank r × Mx D V.rank t =>
      pr b₀ (yv V b₀ z) (yv V b₀ z) :=
    (continuous_adjM.comp hy).matrix_mul (continuous_const.matrix_mul hy)
  have hs : ContinuousSub (Mx D t t) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hT
  exact h2.sub h3

theorem nuT_supp : ZpEq → AcEq → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → nuT hn I μ x₀ {z | ¬ ((1 : AE D) • z.1 = z.1 ∧ (1 : AE D) • z.2 = z.2 ∧ ip B z.1 z.1 = (1 : AE D) • rat b₀.1 ∧ qv B b₀ z = 0)} = 0 := by
  intro hZ hA D n t B W d hn I μ _ b₀ hb x₀ hx
  obtain ⟨g1, -⟩ := top_pair (D := D) B.rank W.rank t
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := g1.opensMeasurable
  have t1 := (top_mx (D := D) W.rank W.rank).2.2.2.1
  have t2 := (top_mx (D := D) t t).2.2.2.1
  have hcl : IsClosed {z : Mx D B.rank W.rank × Mx D B.rank t |
      ip B z.1 z.1 = rat b₀.1 ∧ qv B b₀ z = 0} :=
    (isClosed_eq (continuous_ipM B continuous_fst continuous_fst)
      continuous_const).inter (isClosed_eq (continuous_qvM B b₀) continuous_const)
  have hS : {z : Mx D B.rank W.rank × Mx D B.rank t | ¬ ((1 : AE D) • z.1 = z.1 ∧ (1 : AE D) • z.2 = z.2 ∧
      ip B z.1 z.1 = (1 : AE D) • rat b₀.1 ∧ qv B b₀ z = 0)} =
      {z | ip B z.1 z.1 = rat b₀.1 ∧ qv B b₀ z = 0}ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, one_smul, true_and]
  rw [hS]
  unfold nuT
  rw [Measure.map_apply (measurable_pi hn I x₀) hcl.measurableSet.compl]
  have hE : (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ⁻¹'
      {z | ip B z.1 z.1 = rat b₀.1 ∧ qv B b₀ z = 0}ᶜ = ∅ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    obtain ⟨a1, -, a3⟩ := hA D W.rank t B b₀ ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)
    obtain ⟨z1, -, z3⟩ := hZ D n t B W d hn b₀ hb x₀ hx p.2
    exact ⟨a1.trans z1, a3.trans z3⟩
  rw [hE, measure_empty]

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

section

noncomputable section

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

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem jn_firstCols {D : D7} {a r t n : ℕ} (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) :
    (jn hn w v).submatrix id (fun j : Fin r => finCongr hn (Fin.castAdd t j)) = w := by
  ext i j
  have e : (finSumFinEquiv.trans (finCongr hn)).symm (finCongr hn (Fin.castAdd t j)) = Sum.inl j := by
    rw [Equiv.symm_apply_eq]
    simp
  simp only [jn, Matrix.submatrix_apply, id, e, Matrix.fromCols_apply_inl]

theorem continuous_jn_pair {D : D7} {a r t n : ℕ} (hn : r + t = n) :
    Continuous fun p : Mx D a r × Mx D a t => jn hn p.1 p.2 := by
  refine continuous_matrix fun i j => ?_
  simp only [jn, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with k | k
  · simpa using (continuous_fst.matrix_elem i k)
  · simpa using (continuous_snd.matrix_elem i k)

theorem continuous_orb_shear : IkSch → Dom → OrbFin → Shift → JnBl → Ext0 → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t)
    (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 →
    ∀ Φ ∈ schwartzA θ B.rank n,
      Continuous (fun y : Mx D W.rank t => orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀)) := by
  intro hIk hDom hOrb hShift hJn hExt D n t B W d hn I θ hθ x₀ hx Φ hΦ
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨hT, -, hS, -, -⟩ := top_mx (D := D) W.rank t
  obtain ⟨hT', -, -, -, -⟩ := top_mx (D := D) W.rank W.rank
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hBor : BorelSpace (GA D W) := ⟨rfl⟩
  have hΨ : ikp I Φ ∈ schwartzA θ W.rank n := (hIk D n t B W d I θ hθ Φ hΦ).2
  have hcΨ : Continuous (ikp I Φ) := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ _ hΨ).1
  have hinj : Function.Injective fun j : Fin W.rank => finCongr hn (Fin.castAdd t j) := by
    intro a b h
    exact Fin.castAdd_injective _ _ ((finCongr hn).injective h)
  obtain ⟨M, hM, -, hMd⟩ := hDom D θ hθ W.rank n W.rank _ hinj _ hΨ
  have hcM : Continuous M := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ M hM).1
  have hform : ∀ (y : Mx D W.rank t) (h : GA D W),
      (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (mm (mt W h⁻¹) (rat (ext0 hn x₀))) =
        ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) := by
    intro y h
    rw [hShift D n t B W d hn I Φ y, hExt D n t W hn x₀ h, hJn D n t W.rank W.rank hn]
  have hfun : (fun y : Mx D W.rank t => orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀)) =
      fun y => ∫ h, ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) ∂I.m := by
    funext y
    exact integral_congr_ae (Eventually.of_forall fun h => hform y h)
  rw [hfun]
  have hcw := continuous_ww (D := D) (W := W) x₀
  have hb : Integrable (fun h => M (ww W x₀ h)) I.m :=
    ⟨(hcM.comp hcw).aestronglyMeasurable, hOrb D θ hθ W I.m I.haar x₀ hx M hM⟩
  have hpt : ∀ (h : GA D W), Continuous fun y : Mx D W.rank t => ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) := by
    intro h
    refine hcΨ.comp ((continuous_jn_pair hn).comp (continuous_const.prodMk ?_))
    exact (continuous_const.matrix_mul continuous_id).add continuous_const
  have hmeas : ∀ y : Mx D W.rank t, Continuous fun h : GA D W => ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) := by
    intro y
    refine hcΨ.comp ((continuous_jn_pair hn).comp (hcw.prodMk ?_))
    exact (hcw.matrix_mul continuous_const).add continuous_const
  have hF : FirstCountableTopology (Mx D W.rank t) :=
    @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ hS
  refine continuous_of_dominated (bound := fun h => ‖M (ww W x₀ h)‖)
    (fun y => (hmeas y).aestronglyMeasurable) (fun y => Eventually.of_forall fun h => ?_) hb.norm
    (Eventually.of_forall hpt)
  have h1 := hMd (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0))
  rw [jn_firstCols] at h1
  exact h1.trans (Complex.re_le_norm _)

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

section


theorem _root_.GlobalTheory.T.fixed_field_structure : PositivityTheory.SiegelWeilFormula.Gunr.FixedK := by
  first | exact @GlobalTheory.CompanionTheory.FixedPointsCM.fixedK | exact GlobalTheory.CompanionTheory.FixedPointsCM.fixedK | (intros; apply GlobalTheory.CompanionTheory.FixedPointsCM.fixedK <;> assumption)
end

section


theorem _root_.GlobalTheory.T.integral_hermitian_invariance : PositivityTheory.SiegelWeilFormula.Gunr.HermitianLatticeInvariance := by
  first | exact @GlobalTheory.CompanionTheory.GunrInv.integrand_invariant_integral_hermitian | exact GlobalTheory.CompanionTheory.GunrInv.integrand_invariant_integral_hermitian | (intros; apply GlobalTheory.CompanionTheory.GunrInv.integrand_invariant_integral_hermitian <;> assumption)
end
