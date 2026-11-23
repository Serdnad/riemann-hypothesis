module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
open MeasureTheory

theorem _root_.GlobalTheory.T.schwartzBruhat_matrixCoefficient_compactSupport_finitePlace : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : MeasureTheory.Measure (κ → Fv F v))
    [μ.IsAddHaarMeasure], Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    ∀ φ ∈ SB (κ → Fv F v), ∀ g ∈ SB (κ → Fv F v),
    ∃ C : Set ((κ → Fv F v) × (κ → Fv F v)), IsCompact C ∧
      ∀ w, ∫ y, schr ψ₀ w φ y * (starRingEnd ℂ) (g y) ∂μ ≠ 0 → w ∈ C := by
  first | exact @GlobalTheory.SchrSuppFin.support_compact | exact GlobalTheory.SchrSuppFin.support_compact | (intros; apply GlobalTheory.SchrSuppFin.support_compact <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.schwartzBruhat_span_box_indicator_schrodinger : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ), (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ] (s : (κ → Fv F v) → ℂ), s ∈ SB (κ → Fv F v) → s ≠ 0 → ∃ (x₀ : κ → Fv F v) (N₀ : ℕ), ∀ N ≥ N₀, Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ) ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) := by
  first | exact @GlobalTheory.SchrBox.indicator_box_mem_span | exact GlobalTheory.SchrBox.indicator_box_mem_span | (intros; apply GlobalTheory.SchrBox.indicator_box_mem_span <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.rationalTopFormPullback_bijective_birational : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ n : ℕ, Function.Bijective (EtaleKlt.ratPull p s n) := by
  first | exact @GlobalTheory.EtaleKlt.ratPull_bijective_of_birational | exact GlobalTheory.EtaleKlt.ratPull_bijective_of_birational | (intros; apply GlobalTheory.EtaleKlt.ratPull_bijective_of_birational <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.rationalTopFormPullback_ne_zero_of_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → (U : Set M).Nonempty → ∀ η : RatForms p n, η ≠ 0 → GlobalTheory.EtaleKlt.ratPull p f n η ≠ 0 := by
  first | exact @GlobalTheory.EtaleKlt.ratPull_ne_zero | exact GlobalTheory.EtaleKlt.ratPull_ne_zero | (intros; apply GlobalTheory.EtaleKlt.ratPull_ne_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cubeValueTimesThetaFrames_chartGauge : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g) (geo : Geo ν d) (x y z : Fin g → ℂ) (j : thK → D.P.L.ι), ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j → cubF d x y z * ∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I = valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val := by
  first | exact @GlobalTheory.MBLow.Cl.CubHol.cubF_mul_prod_frG | exact GlobalTheory.MBLow.Cl.CubHol.cubF_mul_prod_frG | (intros; apply GlobalTheory.MBLow.Cl.CubHol.cubF_mul_prod_frG <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cubeLocalUnit_value_holomorphic_third : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g), Geo ν d → ∀ (x y : Fin g → ℂ) (j : thK → D.P.L.ι), IsOpen {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} ∧ DifferentiableOn ℂ (fun z => valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val) {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} := by
  first | exact @GlobalTheory.MBLow.Cl.CubHol.isOpen_and_differentiableOn_valF_pt3_cubW | exact GlobalTheory.MBLow.Cl.CubHol.isOpen_and_differentiableOn_valF_pt3_cubW | (intros; apply GlobalTheory.MBLow.Cl.CubHol.isOpen_and_differentiableOn_valF_pt3_cubW <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.holomorphicFrame_partialSum_diff_ne_zero : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g) (geo : Geo ν d) (x y : Fin g → ℂ) (j : thK → D.P.L.ι) (I : thK), DifferentiableOn ℂ (fun z => geo.frG (j I) (wI x y z I)) {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} ∧ ∀ z, ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j → geo.frG (j I) (wI x y z I) ≠ 0 := by
  first | exact @GlobalTheory.MBLow.Cl.CubHol.frG_wI_hol_ne | exact GlobalTheory.MBLow.Cl.CubHol.frG_wI_hol_ne | (intros; apply GlobalTheory.MBLow.Cl.CubHol.frG_wI_hol_ne <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

theorem _root_.GlobalTheory.T.transitionUnitPowValueAtPoint_cocycle : ∀ {X : Scheme.{0}} (L : LB X), L.IsLB → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b c : L.ι) (n : ℤ),
    ⊤ ≤ y ⁻¹ᵁ L.U a → ⊤ ≤ y ⁻¹ᵁ L.U b → ⊤ ≤ y ⁻¹ᵁ L.U c →
    trV L y a b n * trV L y b c n = trV L y a c n := by
  first | exact @GlobalTheory.MBLow.TanGauge.trV_cocycle | exact GlobalTheory.MBLow.TanGauge.trV_cocycle | (intros; apply GlobalTheory.MBLow.TanGauge.trV_cocycle <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

theorem _root_.GlobalTheory.T.generatorValue_linComb_change_of_charts : ∀ {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j' →
    valR y (LB.wchart L φ j) (t.s j).val =
      (∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k)) * valR y (LB.wchart L φ j') (t.s j').val := by
  first | exact @GlobalTheory.MBLow.TanGauge.valR_gen_linComb | exact GlobalTheory.MBLow.TanGauge.valR_gen_linComb | (intros; apply GlobalTheory.MBLow.TanGauge.valR_gen_linComb <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

theorem _root_.GlobalTheory.T.sectionValue_linComb_change_of_charts : ∀ {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j' →
    valR y (LB.wchart L φ j) (s.f j) =
      (∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k)) * valR y (LB.wchart L φ j') (s.f j') := by
  first | exact @GlobalTheory.MBLow.TanGauge.valR_linComb_sec | exact GlobalTheory.MBLow.TanGauge.valR_linComb_sec | (intros; apply GlobalTheory.MBLow.TanGauge.valR_linComb_sec <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTwKU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_KGL_iff_val {u : Pl E} (x : GLw n u) :
    x ∈ GlobalTheory.LFun.KGL u (n := n) ↔ (∀ i j, Valued.v (x.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((x⁻¹).val i j) ≤ 1 := by
  refine ⟨?_, fun h => ⟨⟨Matrix.of fun i j => ⟨_, h.1 i j⟩, Matrix.of fun i j => ⟨_, h.2 i j⟩, ?_, ?_⟩, rfl⟩⟩
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
  · refine Matrix.map_injective (Ov E u).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective (Ov E u).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem mem_Kglob_iff (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    g ∈ GlobalTheory.EulerTw.Kglob E n ↔ ∀ u : Pl E, GeneralLinearGroup.map (pLoc E u) g ∈ GlobalTheory.LFun.KGL u (n := n) := by
  unfold GlobalTheory.EulerTw.Kglob
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap]

theorem pLoc_prjG (T : Finset (Pl E)) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (u : Pl E) :
    GeneralLinearGroup.map (pLoc E u) (GlobalTheory.EulerTw.prjG E n T g) =
      if u ∈ T then GeneralLinearGroup.map (pLoc E u) g else 1 := by
  have hid : pLoc E u (GlobalTheory.EulerTw.idem E T) = if u ∈ T then 1 else 0 := rfl
  split_ifs with hu
  · refine Units.ext (Matrix.ext fun i j => ?_)
    show pLoc E u ((GlobalTheory.EulerTw.idem E T • g.val + (1 - GlobalTheory.EulerTw.idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) = pLoc E u (g.val i j)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub, map_one, hid, if_pos hu]
    simp
  · refine Units.ext (Matrix.ext fun i j => ?_)
    show pLoc E u ((GlobalTheory.EulerTw.idem E T • g.val + (1 - GlobalTheory.EulerTw.idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub, map_one, hid, if_neg hu]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]

theorem val_pLoc_thF (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (u : Pl E) (i j : Fin n) :
    Valued.v ((GeneralLinearGroup.map (pLoc E u) (thF E n g)).val i j) =
      Valued.v ((GeneralLinearGroup.map (pLoc E (conjSrc (IsCMField.complexConj E).toRingEquiv u)) g⁻¹).val j.rev i.rev) := by
  show Valued.v (pLoc E u ((thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) g).val i j)) = _
  rw [GlobalTheory.ThetaPull.thetaGL_apply, map_mul, Valuation.map_mul, pLoc_conjFin, (conjLoc_spec _ u).2.2]
  have : Valued.v (pLoc E u ((-1) ^ ((i : ℕ) + j))) = 1 := by
    rw [map_pow, map_neg, map_one, Valuation.map_pow, Valuation.map_neg, Valuation.map_one, one_pow]
  rw [this, one_mul]
  rfl

theorem thF_mem_Kglob (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (hg : g ∈ GlobalTheory.EulerTw.Kglob E n) :
    thF E n g ∈ GlobalTheory.EulerTw.Kglob E n := by
  rw [mem_Kglob_iff] at hg ⊢
  intro u
  have hs := (mem_KGL_iff_val _).1 (hg (conjSrc (IsCMField.complexConj E).toRingEquiv u))
  rw [mem_KGL_iff_val]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [val_pLoc_thF, map_inv]
    exact hs.2 _ _
  · rw [← map_inv, ← map_inv, val_pLoc_thF, inv_inv]
    exact hs.1 _ _

end GlobalTheory.EulerTwKU
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTwU

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem gl_ext {k k' : GL (Fin n) (Af E)}
    (h : ∀ v : Pl E, GeneralLinearGroup.map (pLoc E v) k = GeneralLinearGroup.map (pLoc E v) k') : k = k' := by
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun v => congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j) (h v)

theorem cPl_cPl (v : Pl E) : cPl E (cPl E v) = v := GlobalTheory.ThetaPull.conjSrc_conjSrc v

theorem pc_thF (v : Pl E) (x : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E v) (thF E n x) = thetaGL n (RingHom.id _)
      (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv v)
        (GeneralLinearGroup.map (pLoc E (cPl E v)) x)) :=
  GlobalTheory.ThetaPull.map_thetaGL (pLoc E v) (RingHom.id _) (RingHom.id _) (fun _ => rfl)
    (GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) x)

theorem thF_thF (x : GL (Fin n) (Af E)) : thF E n (thF E n x) = x :=
  GlobalTheory.ThetaPull.thetaGL_thetaGL _ (fun y => GlobalTheory.ThetaPull.cFin_cFin y) x

theorem pc_ratF (v : Pl E) (δ : GL (Fin n) E) :
    GeneralLinearGroup.map (pLoc E v) (ratF E n δ) = GeneralLinearGroup.map (algebraMap E (v.adicCompletion E)) δ :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem continuous_pc (v : Pl E) : Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E v)) :=
  Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval v))

theorem eventually_int (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) x).2

theorem mem_GLint {L : Type} [Field L] (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_pc_ratF_mem (g : GL (Fin n) E) : ∀ᶠ v : Pl E in cofinite,
    GeneralLinearGroup.map (pLoc E v) (ratF E n g) ∈ GlobalTheory.LFun.KGL v (n := n) := by
  have h : ∀ g : GL (Fin n) E, ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (g.val i j) ∈ w.adicCompletionIntegers E := fun g => by
    simp only [Filter.eventually_all]; exact fun i j => eventually_int _
  filter_upwards [h g, h g⁻¹] with w a b
  rw [pc_ratF]
  exact mem_GLint _ _ a (by rw [← map_inv]; exact b)

end GlobalTheory.EulerTwU
end
end
