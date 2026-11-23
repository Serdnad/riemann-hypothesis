module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle415
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle402
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle408
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle405
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle403
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

@[expose] public section

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.subgroup_one_parameter_closed_eq_top : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Subgroup (GL (Fin a) (Cinf E))), (∀ (c : ℝ → GL (Fin a) (Cinf E)) (X : GlobalTheory.CuspRep.Lie E a), Continuous c → c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → HasDerivAt (fun t => toL (c t).val) X 0 → ∀ t, c t ∈ S) → S = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GenOneParam.eq_top_of_oneParam_Cinf | exact GlobalTheory.CompanionTheory.GenOneParam.eq_top_of_oneParam_Cinf | (intros; apply GlobalTheory.CompanionTheory.GenOneParam.eq_top_of_oneParam_Cinf <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.Dblock

theorem lie_skew_mem_of_cpt_stable : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (F : Submodule ℂ (Sm E a)), FiniteDimensional ℂ F → (∀ k, ∀ φ ∈ F, cptRep E a k φ ∈ F) →
    ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ φ ∈ F, lie E a X φ ∈ F := by
  intro E _ _ _ a F hf hK X hX φ hφ
  obtain ⟨c, -, h0, -, hc, hu⟩ := GlobalTheory.CompanionTheory.LieCurve.exists_curve E a X
  let W' : Submodule ℂ (GA E a → ℂ) := F.map (Sm E a).subtype
  have hfin : FiniteDimensional ℂ W' := by
    have := hf
    exact inferInstance
  have hcl : IsClosed (W' : Set (GA E a → ℂ)) := W'.closed_of_finiteDimensional
  let G : ℝ → GA E a → ℂ := fun t g => φ.1 (g * infGL E a (c t))
  have hG : ∀ t, G t ∈ W' := fun t =>
    ⟨cptRep E a ⟨(c t).val, hu hX t⟩ φ, hK _ _ hφ, funext fun g => by
      have : Unitary.toUnits (⟨(c t).val, hu hX t⟩ : Kinf E a) = c t := Units.ext rfl
      change φ.1 (g * infGL E a (Unitary.toUnits _)) = _
      rw [this]⟩
  have hd : Filter.Tendsto (slope G 0) (nhdsWithin 0 {0}ᶜ) (nhds (lieD X φ.1)) :=
    tendsto_pi_nhds.2 fun g => hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_curve φ g c X h0 hc)
  have hm : lieD X φ.1 ∈ W' := hcl.mem_of_tendsto hd (Filter.Eventually.of_forall fun t =>
    W'.smul_of_tower_mem _ (W'.sub_mem (hG t) (hG 0)))
  obtain ⟨w, hw, e⟩ := hm
  rwa [show lie E a X φ = w from Subtype.ext e.symm]

end GlobalTheory.CompanionTheory.Dblock
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

theorem _root_.GlobalTheory.T.trace_operator_eigenvalue_sum : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar τ m → ∀ φ ∈ π.V, (∑ i : Fin a, Eop τ i i) φ = m.sum • φ := by
  first | exact @GlobalTheory.CompanionTheory.CapelliTrace.trace_Eop_eq | exact GlobalTheory.CompanionTheory.CapelliTrace.trace_Eop_eq | (intros; apply GlobalTheory.CompanionTheory.CapelliTrace.trace_Eop_eq <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

theorem _root_.GlobalTheory.T.finite_z_span_integral_representation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) →
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) →
    ∀ [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
      (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure],
      ∃ κ : AutomorphicForm.archGroup E a → ℂ, Continuous κ ∧ HasCompactSupport κ ∧
        ∀ g : GA E a, φ.1 g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * κ y ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.GrowthKernel.exists_kernel_of_finite | exact GlobalTheory.CompanionTheory.HCRep.GrowthKernel.exists_kernel_of_finite | (intros; apply GlobalTheory.CompanionTheory.HCRep.GrowthKernel.exists_kernel_of_finite <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic

theorem _root_.GlobalTheory.T.lie_derivative_convolution_kernel : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ : Sm E a), IsAutForm φ → ∀ X : Lie E a, ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : GA E a, (lie E a X φ).1 g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.LieConv.lie_eq_conv | exact GlobalTheory.CompanionTheory.LieConv.lie_eq_conv | (intros; apply GlobalTheory.CompanionTheory.LieConv.lie_eq_conv <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic

theorem _root_.GlobalTheory.T.moderate_growth_convolution_integral : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ ψ : GA E a → ℂ), Continuous φ → (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * infGL E a y)‖ ≤ C * height y ^ N) → ∀ D : AutomorphicForm.archGroup E a → ℂ, Continuous D → HasCompactSupport D → (∀ g, ψ g = ∫ y, φ (g * AutomorphicForm.infEmb E a y) * D y ∂ν) → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ (g * infGL E a y)‖ ≤ C * height y ^ N := by
  first | exact @GlobalTheory.CompanionTheory.GrowthConv.growth_conv | exact GlobalTheory.CompanionTheory.GrowthConv.growth_conv | (intros; apply GlobalTheory.CompanionTheory.GrowthConv.growth_conv <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.CompanionTheory.MPDict

open GlobalTheory.ArithmeticHeightTower ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

abbrev Bk (n : Fin (m + 1) → ℕ) : Fin (m + 1) → Type := fun c => Fin (n c + 1)

abbrev σ₀ : ℤ →+* ℂ := Int.castRingHom ℂ

abbrev prB (n : Fin (m + 1) → ℕ) (k : Fin (m + 1)) : MP ℤ m n ⟶ PSpace ℤ (n k) := pr ℤ m n k

abbrev blockChart (n : Fin (m + 1) → ℕ) (k : Fin (m + 1)) (i : Bk n k) : (MP ℤ m n).Opens :=
  prB n k ⁻¹ᵁ chart ℤ (n k) i

def mchart (c : ∀ k, Bk n k) : (MP ℤ m n).Opens :=
  ⟨⋂ k, (blockChart n k (c k) : Set (MP ℤ m n)),
    isOpen_iInter_of_finite fun k => (blockChart n k (c k)).isOpen⟩

theorem mchart_le (c : ∀ k, Bk n k) (k : Fin (m + 1)) : mchart c ≤ blockChart n k (c k) :=
  fun _ hx => Set.mem_iInter.1 hx k

def blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) : Γ(MP ℤ m n, W)ˣ :=
  res h (pullU (prB n k) _ (ratioUnit _ i j inf_le_left inf_le_right))

def ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : Bk n k :=
  (exists_mem_chart ℤ (n k) (prB n k x)).choose

theorem mem_ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : x ∈ blockChart n k (ptChart x k) :=
  (exists_mem_chart ℤ (n k) (prB n k x)).choose_spec

def ptCoord (x : MP ℤ m n) (p : Σ k, Bk n k) : (MP ℤ m n).residueField x :=
  ((MP ℤ m n).evaluation (blockChart n p.1 (ptChart x p.1)) x (mem_ptChart x p.1)).hom
    (pullRatio (prB n p.1) _ (ptChart x p.1) le_rfl p.2)

def ptIdeal (x : MP ℤ m n) : Ideal (Geo.MRing (Bk n)) := Geo.mCoordIdeal (ptCoord x)

def IsUnder (y : CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ) : Prop :=
  ∀ (k : Fin (m + 1)) (i : Bk n k), (y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) ↔ z ⟨k, i⟩ ≠ 0) ∧
    ∀ j : Bk n k, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) →
      CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y = z ⟨k, j⟩ / z ⟨k, i⟩

def IsHermRep (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)) : Prop :=
  ∃ u : ∀ (i : M.B.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, M.B.U i ⊓ mchart c)ˣ,
    (∀ i j c,
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U j ⊓ mchart c) (u j c) =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U i ⊓ mchart c) (u i c)) ∧
    (∀ i c c',
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ mchart c) (u i c) =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ mchart c') (u i c') *
        ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
          ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ A.a k) ∧
    ∀ (i : M.B.ι) (c : ∀ k, Bk n k) (y : CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), IsUnder y z →
      y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) →
      A.h z = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) *
        ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖ *
          Real.exp ((M.φ σ₀).φ i y / 2)

abbrev consN (n' : ℕ) (n : Fin (m + 1) → ℕ) : Fin (m + 2) → ℕ := Fin.cons n' n

def sv (n' : ℕ) (n : Fin (m + 1) → ℕ) : (Σ k, Bk n k) → Σ k', Bk (consN n' n) k' :=
  fun p => ⟨p.1.succ, p.2⟩

theorem isBlockMap_sv (n' : ℕ) (n : Fin (m + 1) → ℕ) :
    IsBlockMap (ι := Bk n) (ι' := Bk (consN n' n)) Fin.succ (sv n' n) := by
  refine ⟨Fin.succ_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', j⟩ h
    have hk : k.succ = k'.succ := congrArg Sigma.fst h
    obtain rfl : k = k' := Fin.succ_injective _ hk
    have h' : (⟨k.succ, i⟩ : Σ k', Bk (consN n' n) k') = ⟨k.succ, j⟩ := h
    have hij : i = j := sigma_mk_injective (β := Bk (consN n' n)) (i := k.succ) h'
    rw [hij]
  · rintro ⟨k', j⟩ ⟨k, rfl⟩
    exact ⟨⟨k, j⟩, rfl⟩

def pullLine (n' : ℕ) (A : Geo.HermLine (Bk n)) : Geo.HermLine (Bk (consN n' n)) where
  a := pullDeg Fin.succ A.a
  h z := A.h fun p => z (sv n' n p)
  pos z hz := A.pos _ fun k => hz k.succ
  smul c z hc := by
    have e := A.smul (fun k => c k.succ) (fun p => z (sv n' n p)) fun k => hc k.succ
    refine e.trans ?_
    have h0 : pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) A.a 0 = 0 := by
      unfold pullDeg
      rw [Function.extend_apply']
      · rfl
      · rintro ⟨k, hk⟩
        exact Fin.succ_ne_zero k hk
    have hs (k : Fin (m + 1)) : pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) A.a k.succ = A.a k :=
      (Fin.succ_injective _).extend_apply _ _ _
    rw [Fin.prod_univ_succ (fun k' => ‖c k'‖ ^ pullDeg Fin.succ A.a k'), h0, zpow_zero, one_mul]
    simp only [hs]

theorem isPullHerm_pullLine (n' : ℕ) (A : Geo.HermLine (Bk n)) :
    IsPullHerm Fin.succ (sv n' n) A (pullLine n' A) :=
  ⟨rfl, fun _ => rfl⟩

end GlobalTheory.CompanionTheory.MPDict
end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.modulus_trivial_on_compact_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : ℕ) (e : Fin a ⊕ Fin b ≃ Fin n) (K : Subgroup (GL (Fin n) k)), IsCompact (K : Set (GL (Fin n) k)) → ∀ p : parab k (two e), (p : GL (Fin n) k) ∈ K → deltaHalf k (Two (Fin a) (Fin b)) (leviProj k (two e) p) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.ModCompactParab.deltaHalf_leviProj_eq_one_of_isCompact | exact GlobalTheory.CompanionTheory.ModCompactParab.deltaHalf_leviProj_eq_one_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.ModCompactParab.deltaHalf_leviProj_eq_one_of_isCompact <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.gelfand_kazhdan_local : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k := by
  first | exact @GlobalTheory.CompanionTheory.GenGK.gkLocal_gen | exact GlobalTheory.CompanionTheory.GenGK.gkLocal_gen | (intros; apply GlobalTheory.CompanionTheory.GenGK.gkLocal_gen <;> assumption)
end

section

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SaGen

structure PlaceMap (F K : Type) [Field F] [NumberField F] [Field K] [Algebra F K] [TopologicalSpace K] where

  proj : AF F →ₐ[F] K

  inj : K →ₙₐ[F] AF F
  proj_inj : ∀ x, proj (inj x) = x
  inj_proj : ∀ a, inj (proj a) = inj 1 * a
  cont_proj : Continuous proj
  cont_inj : Continuous inj

section Inhabitants

variable {F : Type} [Field F] [NumberField F]

theorem adele_ext {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : sndA F a = sndA F b) : a = b :=
  Prod.ext h1 h2

theorem finAdele_ext {x y : Af F} (h : ∀ w, evalV F w x = evalV F w y) : x = y :=
  RestrictedProduct.ext _ _ h

theorem fstA_pairA (x : Ainf F) (y : Af F) : fstA F (pairA F x y) = x := rfl

theorem sndA_pairA (x : Ainf F) (y : Af F) : sndA F (pairA F x y) = y := rfl

theorem continuous_singleV' (v : HeightOneSpectrum (𝓞 F)) : Continuous (singleV F v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem evalV_singleV_eq (v w : HeightOneSpectrum (𝓞 F)) (y : Fv F v) (f : ∀ u, Fv F u → Fv F u)
    (h0 : ∀ u, f u 0 = 0) :
    f w (evalV F w (singleV F v y)) = evalV F w (singleV F v (f v y)) := by
  by_cases h : w = v
  · subst h
    rw [StrongApprox.evalV_single_same, StrongApprox.evalV_single_same]
  · rw [StrongApprox.evalV_single_ne h, StrongApprox.evalV_single_ne h, h0]

def placeMapFin (v : HeightOneSpectrum (𝓞 F)) : PlaceMap F (Fv F v) where
  proj := (evalV F v).comp (sndA F)
  inj :=
    { toFun := fun y => pairA F 0 (singleV F v y)
      map_smul' := by
        intro c y
        refine adele_ext ?_ (finAdele_ext fun w => ?_)
        · rw [map_smul, fstA_pairA, fstA_pairA, smul_zero]
        · rw [map_smul, sndA_pairA, sndA_pairA, map_smul]
          exact (evalV_singleV_eq v w y (fun u t => c • t) (fun u => smul_zero c)).symm ▸ rfl
      map_zero' := by
        refine adele_ext rfl (finAdele_ext fun w => ?_)
        rw [sndA_pairA, map_zero, map_zero]
        by_cases h : w = v
        · subst h
          rw [StrongApprox.evalV_single_same]
        · rw [StrongApprox.evalV_single_ne h]
      map_add' := by
        intro x y
        refine adele_ext ?_ (finAdele_ext fun w => ?_)
        · rw [map_add (f := _), fstA_pairA, fstA_pairA, fstA_pairA, add_zero]
        · rw [map_add (f := _), sndA_pairA, sndA_pairA, sndA_pairA, map_add (f := _)]
          by_cases h : w = v
          · subst h
            simp only [StrongApprox.evalV_single_same]
          · simp only [StrongApprox.evalV_single_ne h, add_zero]
      map_mul' := by
        intro x y
        refine adele_ext ?_ (finAdele_ext fun w => ?_)
        · rw [map_mul, fstA_pairA, fstA_pairA, fstA_pairA, mul_zero]
        · rw [map_mul, sndA_pairA, sndA_pairA, sndA_pairA, map_mul]
          by_cases h : w = v
          · subst h
            simp only [StrongApprox.evalV_single_same]
          · simp only [StrongApprox.evalV_single_ne h, mul_zero] }
  proj_inj := fun x => StrongApprox.evalV_single_same v x
  inj_proj := by
    intro a
    refine adele_ext ?_ (finAdele_ext fun w => ?_)
    · change (0 : Ainf F) = fstA F (pairA F 0 (singleV F v 1) * a)
      rw [map_mul, fstA_pairA, zero_mul]
    · change evalV F w (singleV F v (evalV F v (sndA F a))) = evalV F w (sndA F (pairA F 0 (singleV F v 1) * a))
      rw [map_mul, map_mul, sndA_pairA]
      by_cases h : w = v
      · subst h
        simp only [StrongApprox.evalV_single_same, one_mul]
      · simp only [StrongApprox.evalV_single_ne h, zero_mul]
  cont_proj := StrongApprox.continuous_evalV v
  cont_inj := continuous_const.prodMk (continuous_singleV' v)


open Classical in
def singleI (w : InfinitePlace F) (y : w.Completion) : Ainf F :=
  (Pi.single (M := fun u : InfinitePlace F => u.Completion) w y : ∀ u : InfinitePlace F, u.Completion)

open Classical in
theorem singleI_self (w : InfinitePlace F) (y : w.Completion) : (singleI w y : ∀ u : InfinitePlace F, u.Completion) w = y :=
  Pi.single_eq_same (M := fun u : InfinitePlace F => u.Completion) w y

open Classical in
theorem singleI_ne {w u : InfinitePlace F} (h : u ≠ w) (y : w.Completion) :
    (singleI w y : ∀ u : InfinitePlace F, u.Completion) u = 0 :=
  Pi.single_eq_of_ne (M := fun u : InfinitePlace F => u.Completion) h y

theorem ainf_ext {x y : Ainf F} (h : ∀ u, (x : ∀ u : InfinitePlace F, u.Completion) u = (y : ∀ u : InfinitePlace F, u.Completion) u) : x = y :=
  funext h


open Classical in
def placeMapInf (w : InfinitePlace F) : PlaceMap F w.Completion where
  proj := (Pi.evalAlgHom F (fun u : InfinitePlace F => u.Completion) w).comp (fstA F)
  inj :=
    { toFun := fun y => pairA F (singleI w y) 0
      map_smul' := by
        intro c y
        refine adele_ext ?_ ?_
        · rw [map_smul, fstA_pairA, fstA_pairA]
          exact Pi.single_smul (f := fun u : InfinitePlace F => u.Completion) w c y
        · rw [map_smul, sndA_pairA, sndA_pairA, smul_zero]
      map_zero' := by
        refine adele_ext ?_ rfl
        rw [fstA_pairA, map_zero]
        exact Pi.single_zero (M := fun u : InfinitePlace F => u.Completion) w
      map_add' := by
        intro x y
        refine adele_ext ?_ ?_
        · rw [map_add (f := _), fstA_pairA, fstA_pairA, fstA_pairA]
          exact Pi.single_add (f := fun u : InfinitePlace F => u.Completion) w x y
        · rw [map_add (f := _), sndA_pairA, sndA_pairA, sndA_pairA, add_zero]
      map_mul' := by
        intro x y
        refine adele_ext ?_ ?_
        · rw [map_mul, fstA_pairA, fstA_pairA, fstA_pairA]
          exact Pi.single_mul (α := fun u : InfinitePlace F => u.Completion) w x y
        · rw [map_mul, sndA_pairA, sndA_pairA, sndA_pairA, mul_zero] }
  proj_inj := fun x => singleI_self w x
  inj_proj := by
    intro a
    refine adele_ext ?_ ?_
    · change singleI w (fstA F a w) = fstA F (pairA F (singleI w 1) 0 * a)
      rw [map_mul, fstA_pairA]
      refine ainf_ext fun u => ?_
      change (singleI w (fstA F a w) : ∀ u : InfinitePlace F, u.Completion) u =
        (singleI w 1 : ∀ u : InfinitePlace F, u.Completion) u * fstA F a u
      by_cases h : u = w
      · subst h
        rw [singleI_self, singleI_self, one_mul]
      · rw [singleI_ne h, singleI_ne h, zero_mul]
    · change (0 : Af F) = sndA F (pairA F (singleI w 1) 0 * a)
      rw [map_mul, sndA_pairA, zero_mul]
  cont_proj := (continuous_apply w).comp continuous_fst
  cont_inj := (continuous_single w).prodMk continuous_const

end Inhabitants

section Ring

variable {R : Type} [CommRing R] {M : ℕ}

end Ring

section Lift

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

def iB (P : PlaceMap F K) : K ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  TensorProduct.map { toFun := P.inj, map_add' := map_add _, map_smul' := map_smul _ } LinearMap.id

end Lift

section Iso

variable {F E : Type} [Field F] [Field E] [Algebra F E]

end Iso

end GlobalTheory.CompanionTheory.SaGen
end
end
