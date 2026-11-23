module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Mathlib.Topology.Compactness.Paracompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CuspFormLin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {d : ℕ}

theorem growth_smul_add (c : ℂ) {f f' : GL (Fin d) (Cinf E) → ℂ}
    (h : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N)
    (h' : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f' y‖ ≤ C * height y ^ N) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖c * f y + f' y‖ ≤ C * height y ^ N := by
  obtain ⟨C, N, h⟩ := h
  obtain ⟨C', N', h'⟩ := h'
  refine ⟨‖c‖ * |C| + |C'|, N + N', fun y => ?_⟩
  have h1 := one_le_height y
  have e : ‖f y‖ ≤ |C| * height y ^ (N + N') :=
    (h y).trans (mul_le_mul (le_abs_self C) (pow_le_pow_right₀ h1 (Nat.le_add_right N N'))
      (by positivity) (abs_nonneg C))
  have e' : ‖f' y‖ ≤ |C'| * height y ^ (N + N') :=
    (h' y).trans (mul_le_mul (le_abs_self C') (pow_le_pow_right₀ h1 (Nat.le_add_left N' N))
      (by positivity) (abs_nonneg C'))
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, add_mul, mul_assoc]
  exact add_le_add (mul_le_mul_of_nonneg_left e (norm_nonneg c)) e'

theorem isAutForm_smul_add (c : ℂ) {φ ψ : Sm E d} (h : IsAutForm φ) (h' : IsAutForm ψ) :
    IsAutForm (c • φ + ψ) := by
  refine { left := ?_, level := ?_, kfin := ?_, zfin := ?_, growth := ?_ }
  · intro γ g
    change c * φ.1 _ + ψ.1 _ = c * φ.1 _ + ψ.1 _
    rw [h.left, h'.left]
  · refine isOpen_stab_of_mem_nhds (finRep E d) (c • φ + ψ) (Filter.mem_of_superset
      ((h.level.inter h'.level).mem_nhds ⟨by simp, by simp⟩) ?_)
    intro k hk
    have h1 : finRep E d k φ = φ := hk.1
    have h2 : finRep E d k ψ = ψ := hk.2
    change finRep E d k (c • φ + ψ) = c • φ + ψ
    rw [map_add (f := _), map_smul, h1, h2]
  · have := h.kfin
    have := h'.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E d k φ) ⊔
      Submodule.span ℂ (Set.range fun k => cptRep E d k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    change cptRep E d k (c • φ + ψ) ∈ _
    rw [map_add (f := _), map_smul]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
      (Submodule.subset_span ⟨k, rfl⟩)
  · have := h.zfin
    have := h'.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E d) => z φ) '' Zalg E d) ⊔
        Submodule.span ℂ ((fun z : Module.End ℂ (Sm E d) => z ψ) '' Zalg E d)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    change z (c • φ + ψ) ∈ _
    rw [map_add (f := _), map_smul]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩))
      (Submodule.subset_span ⟨z, hz, rfl⟩)
  · intro g
    exact growth_smul_add c (h.growth g) (h'.growth g)

theorem isCuspForm_smul_add (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (d : ℕ) (c : ℂ)
    (φ ψ : Sm E d) (h : IsCuspForm φ) (h' : IsCuspForm ψ) : IsCuspForm (c • φ + ψ) := by
  refine ⟨isAutForm_smul_add c h.1 h'.1, fun r h0 h1 _ _ ν 𝓕 hν h𝓕 g => ?_⟩
  have i := CuspidalL2GL.integrableOn_unip (ContAut.continuous_of_isOpen_stab E d φ h.1.level) h.1.left ν h𝓕 g
  have i' := CuspidalL2GL.integrableOn_unip (ContAut.continuous_of_isOpen_stab E d ψ h'.1.level) h'.1.left ν h𝓕 g
  change ∫ x in 𝓕, (c * φ.1 (unip x * g) + ψ.1 (unip x * g)) ∂ν = 0
  rw [integral_add (i.const_mul c) i', integral_const_mul, h.2 r h0 h1 ν 𝓕 hν h𝓕 g, h'.2 r h0 h1 ν 𝓕 hν h𝓕 g,
    mul_zero, add_zero]

end GlobalTheory.CuspFormLin
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Cartier

variable {Y : Scheme.{0}} [IsIntegral Y]

def chartEqn {D : CartierDiv Y} (i : (toLB D).ι) : Y.functionFieldˣ := (show EqnChart D from i).1.2

theorem gen_mem_chart {D : CartierDiv Y} (i : (toLB D).ι) : genericPoint Y ∈ (toLB D).U i :=
  (show EqnChart D from i).2.1

theorem isEqn_chartEqn {D : CartierDiv Y} (i : (toLB D).ι) {x : Y} (hx : x ∈ (toLB D).U i) :
    D.IsEqn x (chartEqn i) :=
  (show EqnChart D from i).2.2 x hx

theorem fnOf_g_chart {D : CartierDiv Y} (i j : (toLB D).ι) (h) :
    fnOf _ h ((toLB D).g i j).val = (chartEqn i : Y.functionField) / (chartEqn j : Y.functionField) :=
  fnOf_toLB_g i j h

def genChart (D : CartierDiv Y) : (toLB D).ι :=
  (exists_chart (isLB_toLB D) (genericPoint Y)).choose

def coordFn {D : CartierDiv Y} {W : Y.Opens}
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    Γ(Y, W ⊓ (toLB D).U i) :=
  Twist.coord (sectionsOn.toΓ _ _ a) i

theorem coordFn_zero {D : CartierDiv Y} {W : Y.Opens} (i : (toLB D).ι) :
    coordFn (0 : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) i = 0 := rfl

theorem coordFn_add {D : CartierDiv Y} {W : Y.Opens}
    (a b : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    coordFn (a + b) i = coordFn a i + coordFn b i := rfl


open Classical in
def ratOn (D : CartierDiv Y) (W : Y.Opens) :
    sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W →+ Y.functionField where
  toFun a := if h : genericPoint Y ∈ W then
      fnOf _ (memInf h (gen_mem_chart (genChart D))) (coordFn a (genChart D)) /
        (chartEqn (genChart D) : Y.functionField)
    else 0
  map_zero' := by
    split_ifs with h
    · rw [coordFn_zero, map_zero, zero_div]
    · rfl
  map_add' a b := by
    split_ifs with h
    · rw [coordFn_add, map_add (f := _), add_div]
    · rw [add_zero]

theorem ratOn_apply (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) :
    ratOn D W a = fnOf _ (memInf h (gen_mem_chart (genChart D))) (coordFn a (genChart D)) /
      (chartEqn (genChart D) : Y.functionField) :=
  dif_pos h

theorem ratOn_mul (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    ratOn D W a * chartEqn i = fnOf _ (memInf h (gen_mem_chart i)) (coordFn a i) := by
  set j := genChart D
  have hij : genericPoint Y ∈ W ⊓ (toLB D).U i ⊓ (toLB D).U j :=
    memInf (memInf h (gen_mem_chart i)) (gen_mem_chart j)
  have e0 : resG Y (inf_le_left : W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U i) (coordFn a i) =
      resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ (toLB D).U i ⊓ (toLB D).U j) ((toLB D).g i j).val *
        resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U j) (coordFn a j) :=
    Twist.coord_rel (sectionsOn.toΓ _ _ a) i j _ _ _
  have e := congrArg (fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij) e0
  rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, fnOf_g_chart] at e
  rw [ratOn_apply D h, e]
  have := (chartEqn j).ne_zero
  field_simp
  exact mul_comm _ _

end GlobalTheory.Cartier

namespace GlobalTheory.Cartier

variable {Y : Scheme.{0}} [IsIntegral Y]

theorem ratOn_regularAt (D : CartierDiv Y) {W : Y.Opens}
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) {y : Y} (hy : y ∈ W) :
    D.RegularAt y (ratOn D W a) := by
  obtain ⟨i, hi⟩ : ∃ i, y ∈ (toLB D).U i := exists_chart (isLB_toLB D) y
  refine ⟨chartEqn i, isEqn_chartEqn i hi, ?_⟩
  rw [ratOn_mul D (gen_mem hy) a i]
  exact regAt_fnOf (memInf hy hi) _ _

theorem exists_ratOn_eq (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    {f : Y.functionField} (hf : ∀ y ∈ W, D.RegularAt y f) :
    ∃ a, ratOn D W a = f := by
  have key (i : (toLB D).ι) : ∃ b : Γ(Y, W ⊓ (toLB D).U i),
      fnOf _ (memInf h (gen_mem_chart i)) b = f * chartEqn i :=
    exists_fnOf_eq _ fun x hx => (isEqn_chartEqn i hx.2).regularAt_iff.1 (hf x hx.1)
  choose b hb using key
  have hmem : b ∈ Twist.secGroup (GlobalTheory.structureModule Y) (toLB D) W := fun i j =>
    fn_ext (U := W ⊓ (toLB D).U i ⊓ (toLB D).U j) fun hij => by
      show fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij
          (resG Y (inf_le_left : W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U i) (b i)) =
        fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij
          (resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
              W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ (toLB D).U i ⊓ (toLB D).U j) ((toLB D).g i j).val *
            resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
              W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U j) (b j))
      rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, hb, hb, fnOf_g_chart]
      have := (chartEqn j).ne_zero
      field_simp
  refine ⟨(sectionsOn.toΓ _ _).symm (Twist.mkSec b hmem), ?_⟩
  have e := ratOn_mul D h ((sectionsOn.toΓ _ _).symm (Twist.mkSec b hmem)) (genChart D)
  exact mul_right_cancel₀ (chartEqn (genChart D)).ne_zero (e.trans (hb _))

theorem ratOn_res (D : CartierDiv Y) {W W' : Y.Opens} (hle : W' ≤ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (h : genericPoint Y ∈ W') :
    ratOn D W' (sectionsOn.res Γ(Y, ⊤) _ hle a) = ratOn D W a := by
  rw [ratOn_apply D h, ratOn_apply D (hle h)]
  have e : coordFn (sectionsOn.res Γ(Y, ⊤) _ hle a) (genChart D) =
      resG Y (inf_le_inf_right _ hle) (coordFn a (genChart D)) := rfl
  rw [e, fnOf_resG]

theorem exists_ratOn_twist : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y), ∃ ρ : ∀ W : Y.Opens, sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W →+ Y.functionField, (∀ (W : Y.Opens) (a), ∀ y ∈ W, D.RegularAt y (ρ W a)) ∧ (∀ (W : Y.Opens) (f : Y.functionField), genericPoint Y ∈ W → (∀ y ∈ W, D.RegularAt y f) → ∃ a, ρ W a = f) ∧ ∀ (W W' : Y.Opens) (h : W' ≤ W) (a), genericPoint Y ∈ W' → ρ W' (sectionsOn.res Γ(Y, ⊤) _ h a) = ρ W a :=
  fun Y _ D => ⟨ratOn D, fun _ a _ hy => ratOn_regularAt D a hy,
    fun _ _ h hf => exists_ratOn_eq D h hf, fun _ _ hle a h => ratOn_res D hle a h⟩

end GlobalTheory.Cartier
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.mem_finiteUnitIdeles_of_map_maxRealSubfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b ∈ GlobalTheory.Mem.Chr.unitIdl E → b ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) := by
  first | exact @GlobalTheory.UnitDown.unit_down | exact GlobalTheory.UnitDown.unit_down | (intros; apply GlobalTheory.UnitDown.unit_down <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

theorem dbl_of_isClosedImmersion_lift : ∀ (F : Type) [Field F] (Y : Var F) (Z : Scheme.{0}) [IsIntegral Z] (p₁ p₂ : Z ⟶ Y.X) (h : p₁ ≫ Y.str = p₂ ≫ Y.str), IsClosedImmersion (Limits.pullback.lift p₁ p₂ h) → Limits.pullback.diagonal Y.str (genericPoint Y.X) ∈ Set.range (Limits.pullback.lift p₁ p₂ h) → IsProjOver (p₁ ≫ Y.str) ∧ ∃ δ : Y.X ⟶ Z, IsClosedImmersion δ ∧ δ ≫ p₁ = 𝟙 _ ∧ δ ≫ p₂ = 𝟙 _ ∧ ∀ (K : Type) [Field K] (w : Sp K ⟶ Z), w ≫ p₁ = w ≫ p₂ → w (IsLocalRing.closedPoint K) ∈ Set.range δ := by
  intro F _ Y Z _ p₁ p₂ h hi hη
  have hp₁ : p₁ = Limits.pullback.lift p₁ p₂ h ≫ Limits.pullback.fst Y.str Y.str :=
    (Limits.pullback.lift_fst _ _ _).symm
  have hp₂ : p₂ = Limits.pullback.lift p₁ p₂ h ≫ Limits.pullback.snd Y.str Y.str :=
    (Limits.pullback.lift_snd _ _ _).symm
  refine ⟨?_, ?_⟩
  · rw [hp₁, Category.assoc]
    exact ProjSpace.isProjOver_comp_of_isClosedImmersion _
      (ProjSpace.isProjOver_pullback Y.isProjOver Y.isProjOver)
  have hc : IsClosed (Set.range (Limits.pullback.lift p₁ p₂ h)) :=
    (Limits.pullback.lift p₁ p₂ h).isClosedEmbedding.isClosed_range
  have hrange : Set.range (Limits.pullback.diagonal Y.str) ⊆ Set.range (Limits.pullback.lift p₁ p₂ h) := by
    rintro _ ⟨y, rfl⟩
    have hs := ((genericPoint_spec Y.X).specializes (Set.mem_univ y)).map
      (Limits.pullback.diagonal Y.str).continuous
    exact hs.mem_closed hc hη
  have hle : (Limits.pullback.lift p₁ p₂ h).ker ≤ (Limits.pullback.diagonal Y.str).ker := by
    refine le_trans ?_ (ReducedSubgroup.vanishingIdeal_le_ker _ ⟨_, hc⟩ hrange)
    rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    exact (Limits.pullback.lift p₁ p₂ h).range_subset_ker_support
  have hδ := IsClosedImmersion.lift_fac (Limits.pullback.lift p₁ p₂ h) (Limits.pullback.diagonal Y.str) hle
  refine ⟨IsClosedImmersion.lift _ _ hle, ?_, ?_, ?_, ?_⟩
  · have : IsClosedImmersion (IsClosedImmersion.lift _ _ hle ≫ Limits.pullback.lift p₁ p₂ h) := by
      rw [hδ]; infer_instance
    exact IsClosedImmersion.of_comp _ (Limits.pullback.lift p₁ p₂ h)
  · have e₁ := hδ =≫ Limits.pullback.fst Y.str Y.str
    rwa [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.diagonal_fst] at e₁
  · have e₂ := hδ =≫ Limits.pullback.snd Y.str Y.str
    rwa [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.diagonal_snd] at e₂
  · intro K _ w hw
    have e : w = (w ≫ p₁) ≫ IsClosedImmersion.lift _ _ hle := by
      rw [← cancel_mono (Limits.pullback.lift p₁ p₂ h), Category.assoc, hδ]
      apply Limits.pullback.hom_ext
      · simp only [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.diagonal_fst, Category.comp_id]
      · simp only [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.diagonal_snd, Category.comp_id, hw]
    refine ⟨(w ≫ p₁) (IsLocalRing.closedPoint K), ?_⟩
    have e' := congrArg (fun f : Sp K ⟶ Z => f (IsLocalRing.closedPoint K)) e
    exact e'.symm

end GlobalTheory.FlagPush
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPush

theorem exists_lift_of_var : ∀ (F : Type) [Field F] (X Y : Var F) (f : Y.X ⟶ X.X), f ≫ X.str = Y.str → ∀ (K : Type) [Field K] (V : ValuationSubring K) (v₁ : Sp V ⟶ Y.X) (q₂ : Sp K ⟶ Y.X), q₂ ≫ f = spMap (algebraMap V K) ≫ v₁ ≫ f → ∃ v₂ : Sp V ⟶ Y.X, spMap (algebraMap V K) ≫ v₂ = q₂ ∧ v₂ ≫ f = v₁ ≫ f := by
  intro F _ X Y f hs K _ V v₁ q₂ hq
  haveI : IsProper (f ≫ X.str) := hs ▸ inferInstance
  haveI : UniversallyClosed f := UniversallyClosed.of_comp_of_isSeparated f X.str
  have hE : ValuativeCriterion.Existence f :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) f).1
  obtain ⟨⟨l⟩⟩ := hE { R := V, K := K, i₁ := q₂, i₂ := v₁ ≫ f, commSq := ⟨hq⟩ }
  exact ⟨l.l, l.fac_left, l.fac_right⟩

end GlobalTheory.FlagPush
end
end

section

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}

theorem cInfAt_inv_of_ne_zero {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ} (h : CInfAt f y)
    (h0 : f y ≠ 0) : CInfAt (fun z => (f z)⁻¹) y := by
  obtain ⟨W, ι, _, g, G, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨W, ι, inferInstance, g, fun v => (G v)⁻¹, O ∩ G ⁻¹' {0}ᶜ, h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_compl_singleton, ⟨h₃, ?_⟩,
    (h₄.mono Set.inter_subset_left).inv fun _ hv => hv.2, ?_⟩
  · exact fun e => h0 (h₅.eq_of_nhds.trans e)
  · filter_upwards [h₅] with z e
    rw [e]

theorem cInfAt_finset_sum {ι : Type} (s : Finset ι) {f : ι → CxPts X.str σ → ℝ}
    {y : CxPts X.str σ} (h : ∀ i, CInfAt (f i) y) : CInfAt (fun z => ∑ i ∈ s, f i z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const 0 y
  | insert a s ha ih => simpa only [Finset.sum_insert ha] using (h a).add ih

theorem exists_cInf_bump (y : CxPts X.str σ) {U : Set (CxPts X.str σ)} (hU : U ∈ 𝓝 y) :
    ∃ χ : CxPts X.str σ → ℝ, (∀ z, CInfAt χ z) ∧ (∀ z, 0 ≤ χ z) ∧ 0 < χ y ∧ tsupport χ ⊆ U := by
  classical
  haveI := CxPts.compactSpace σ X.isProjOver
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ X.isProjOver
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := X.dim) y
  obtain ⟨K, hKy, hKc, hKV⟩ :=
    exists_mem_nhds_isClosed_subset (inter_mem hU (c.e.open_source.mem_nhds hc))
  have hn : c.e.symm ⁻¹' K ∈ 𝓝 (c.e y) :=
    c.e.continuousAt_symm (c.e.map_source hc) (by rwa [c.e.left_inv hc])
  obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.1 hn
  let b : ContDiffBump (c.e y) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hsupp : ∀ z ∈ c.e.source, b (c.e z) ≠ 0 → z ∈ K := by
    intro z hz h
    have h₁ : c.e z ∈ Metric.ball (c.e y) r := by
      have : c.e z ∈ Function.support b := h
      rwa [b.support_eq] at this
    have h₂ : c.e.symm (c.e z) ∈ K := hrO h₁
    rwa [c.e.left_inv hz] at h₂
  refine ⟨fun z => if z ∈ c.e.source then b (c.e z) else 0, fun z => ?_, fun z => ?_, ?_, ?_⟩
  · by_cases hz : z ∈ c.e.source
    · refine cInfAt_of_chart isOpen_univ c ?_ hz trivial
      refine (b.contDiff (n := ⊤)).contDiffOn.congr fun v hv => ?_
      simp only [Function.comp_apply, if_pos (c.e.map_target hv.1), c.e.right_inv hv.1]
    · have hzK : z ∉ K := fun h => hz (hKV h).2
      refine (cInfAt_const 0 z).congr ?_
      filter_upwards [hKc.isOpen_compl.mem_nhds hzK] with w hw
      by_cases hwS : w ∈ c.e.source
      · simp only [if_pos hwS]
        by_contra h
        exact hw (hsupp w hwS h)
      · simp only [if_neg hwS]
  · dsimp only
    split_ifs
    · exact b.nonneg
    · exact le_rfl
  · simp only [if_pos hc]
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    exact one_pos
  · refine (closure_minimal (fun z hz => ?_) hKc).trans fun z hz => (hKV hz).1
    by_cases hzS : z ∈ c.e.source
    · exact hsupp z hzS (by simpa only [Function.mem_support, if_pos hzS] using hz)
    · simp only [Function.mem_support, if_neg hzS, ne_eq, not_true_eq_false] at hz

theorem exists_cInf_partition : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} (W : CxPts X.str σ → Set (CxPts X.str σ)), (∀ y, W y ∈ 𝓝 y) → ∃ (s : Finset (CxPts X.str σ)) (ρ : s → CxPts X.str σ → ℝ), (∀ i y, CInfAt (ρ i) y) ∧ (∀ i, tsupport (ρ i) ⊆ W i) ∧ ∀ y, ∑ i, ρ i y = 1 := by
  intro F _ σ X W hW
  haveI := CxPts.compactSpace σ X.isProjOver
  choose χ hχ h0 hpos hs using fun y => exists_cInf_bump y (hW y)
  obtain ⟨s, hcov⟩ := CompactSpace.elim_nhds_subcover (fun y => {z | 0 < χ y z})
    fun y => (hχ y y).continuousAt.eventually (lt_mem_nhds (hpos y))
  have hT (z) : ∑ i : s, χ i z ≠ 0 := by
    have hz : z ∈ ⋃ y ∈ s, {z | 0 < χ y z} := hcov ▸ Set.mem_univ z
    obtain ⟨y, hy, hz⟩ := Set.mem_iUnion₂.1 hz
    exact (Finset.sum_pos' (f := fun i : s => χ i z) (fun i _ => h0 i z)
      ⟨⟨y, hy⟩, Finset.mem_univ _, hz⟩).ne'
  refine ⟨s, fun i z => χ i z * (∑ j : s, χ j z)⁻¹, fun i y => ?_,
    fun i => (tsupport_mul_subset_left).trans (hs i), fun y => ?_⟩
  · exact (hχ i y).comp₂ (cInfAt_inv_of_ne_zero
      (cInfAt_finset_sum Finset.univ fun j : s => hχ j y) (hT y))
      (G := fun x => x.1 * x.2) (contDiff_fst.mul contDiff_snd)
  · rw [← Finset.sum_mul, mul_inv_cancel₀ (hT y)]

end GlobalTheory.GoodTop
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) ∧ ∀ A : FinHolAtlas Y.dim (CxPts Y.str (RingHom.id ℂ)), IsAlgAtlas A → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = mInt A (fun _ => φ.locPot) (fun _ => 1) := by
  first | exact @GlobalTheory.chernInt_one_eq_mInt | exact GlobalTheory.chernInt_one_eq_mInt | (intros; apply GlobalTheory.chernInt_one_eq_mInt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.exists_rational_pure_quaternion_sq_of_adelic : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ c : F, c ≠ 0 → ∀ q : DA F a b, q.re = 0 → q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → ∃ p : ℍ[F, a, b], p.re = 0 ∧ p * p = algebraMap F ℍ[F, a, b] c := by
  first | exact @GlobalTheory.QSA.PureSq.exists_rat_of_adelic | exact GlobalTheory.QSA.PureSq.exists_rat_of_adelic | (intros; apply GlobalTheory.QSA.PureSq.exists_rat_of_adelic <;> assumption)
end
