module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle132
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle028
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactnessStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle033
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle122
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle108
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle092
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle091
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle065
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle123
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle124
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001

@[expose] public section

section

open Matrix Filter Topology ValuativeRel

namespace GlobalTheory.CompanionTheory.LocalFieldChar

theorem circle_eq_one_of_forall_re_pow_pos (z : Circle)
    (h : ∀ n : ℕ, 0 < ((z ^ n : Circle) : ℂ).re) : z = 1 := by
  have hsq : ∀ w : Circle, (w : ℂ).re ^ 2 + (w : ℂ).im ^ 2 = 1 := by
    intro w
    have := Circle.normSq_coe w
    rw [Complex.normSq_apply] at this
    nlinarith
  by_contra hz
  have ha0 : (z : ℂ).re < 1 := by
    by_contra hge
    push_neg at hge
    have h2 := hsq z
    have him : (z : ℂ).im = 0 := by nlinarith [sq_nonneg (z : ℂ).im, sq_nonneg ((z : ℂ).re - 1)]
    have hre : (z : ℂ).re = 1 := by
      rw [him] at h2
      nlinarith
    exact hz (Circle.ext (Complex.ext (by simpa using hre) (by simpa using him)))
  set a : ℕ → ℝ := fun j => ((z ^ (2 ^ j) : Circle) : ℂ).re with ha
  have hstep : ∀ j, a (j + 1) = 2 * a j ^ 2 - 1 := by
    intro j
    have h2 := hsq (z ^ (2 ^ j))
    have hp : z ^ (2 ^ (j + 1)) = z ^ (2 ^ j) * z ^ (2 ^ j) := by
      rw [pow_succ, pow_mul, sq]
    simp only [ha]
    rw [hp, Circle.coe_mul, Complex.mul_re]
    nlinarith
  have hlow : ∀ j, (2 : ℝ) ^ j * (1 - (z : ℂ).re) ≤ 1 - a j := by
    intro j
    induction j with
    | zero => simp [ha]
    | succ j ih =>
      have hpos : 0 < a j := h _
      have hle : a j ≤ 1 := by
        have := hsq (z ^ (2 ^ j))
        have h3 : a j ^ 2 ≤ 1 := by
          simp only [ha]
          nlinarith [sq_nonneg ((z ^ (2 ^ j) : Circle) : ℂ).im]
        nlinarith
      rw [hstep, pow_succ]
      nlinarith
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / (1 - (z : ℂ).re)) (by norm_num : (1 : ℝ) < 2)
  have hd : 0 < 1 - (z : ℂ).re := by linarith
  rw [div_lt_iff₀ hd] at hj
  have := hlow j
  have hpos : 0 < a j := h _
  linarith

theorem isOpen_addChar_ker : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ →
    IsOpen {x : k | ψ x = 1} := by
  apply GlobalTheory.CompanionTheory.BZFun.isOpen_addChar_eq_one <;> assumption

end GlobalTheory.CompanionTheory.LocalFieldChar
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

theorem _root_.GlobalTheory.T.perfect_base_change : ∀ {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {Y₀ Y : Scheme.{0}} (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) (f : Y ⟶ Spec (CommRingCat.of R)) (π : Y ⟶ Y₀), IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ)) → ∀ (M₀ : LB Y₀), M₀.IsLB → Perf f₀ M₀ → Nonempty (Perf f (M₀.pull π)) := by
  first | exact @GlobalTheory.CompanionTheory.PerfBase.perf_pull | exact GlobalTheory.CompanionTheory.PerfBase.perf_pull | (intros; apply GlobalTheory.CompanionTheory.PerfBase.perf_pull <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis

theorem flat_sec_of_smooth : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Smooth s →
    ∀ U : X.affineOpens, Module.Flat R (Sec s U.1) := by
  intro R _ X s hs U
  haveI : Smooth s := hs
  have hfl : Flat s := inferInstance
  have hT : IsAffineOpen (⊤ : (Sp R).Opens) := isAffineOpen_top (Sp R)
  have h1 := HasRingHomProperty.appLE @Flat s hfl ⟨⊤, hT⟩ U le_top
  have h2 : RingHom.Flat (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have h3 := RingHom.Flat.comp h2 h1
  exact h3

end GlobalTheory.CompanionTheory.Axis
end

section

open Matrix Topology Filter

theorem _root_.GlobalTheory.T.lie_algebra_of_exp_local : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → ∃ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) ∧ ∃ V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤 := by
  first | exact @GlobalTheory.CompanionTheory.LinRedLie.exists_lieAlgebra | exact GlobalTheory.CompanionTheory.LinRedLie.exists_lieAlgebra | (intros; apply GlobalTheory.CompanionTheory.LinRedLie.exists_lieAlgebra <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.DegenerateSeries

theorem isUnitarisable_degenerateSeries (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (_ : IsSmoothChar χ₁)
    (_ : IsSmoothChar χ₂) (h₁ : IsUnitaryChar χ₁) (h₂ : IsUnitaryChar χ₂) :
    IsUnitarisable (parInd (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)) := by
  apply GlobalTheory.SmGL.UnitInd.isUnitarisable_prod₂
  · rw [GlobalTheory.SmGL.detRep, GlobalTheory.SmGL.isUnitarisable_ofChar_iff]
    intro g
    exact h₁ _
  · rw [GlobalTheory.SmGL.detRep, GlobalTheory.SmGL.isUnitarisable_ofChar_iff]
    intro g
    exact h₂ _

end GlobalTheory.CompanionTheory.DegenerateSeries
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct ValuativeRel

namespace GlobalTheory.CompanionTheory.IwahoriDatumGL

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

theorem fact_up' {x : GL (Fin n) k} (hx : x ∈ iwahori k (Fin n)) :
    ∃ c ∈ iwahori k (Fin n) ⊓ unipB k (Fin n), ∃ b ∈ iwahori k (Fin n) ⊓ (diagT k (Fin n)).range,
      ∃ a ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n), x = c * b * a := by
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := GlobalTheory.IwahoriTraceProof.iwahori_factorisation hx
  exact ⟨u, ⟨(GlobalTheory.IwahoriTraceProof.mem_unipO_iff hu.1).2 hu, hu.1⟩, _,
    ⟨diagT_mem_iwahori hd, ⟨d, rfl⟩⟩, c, ⟨KOne_le_iwahori k (Fin n) hc.2, hc.1⟩, rfl⟩

end GlobalTheory.CompanionTheory.IwahoriDatumGL

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.CellDiag

def evalOne {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (H : Subgroup G) (σ : Representation ℂ H W) :
    smoothPart (ind H σ) →ₗ[ℂ] W :=
  (LinearMap.proj (1 : G)).comp ((indSpace H σ).subtype.comp (smoothPart (ind H σ)).subtype)

theorem evalOne_injective {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (H : Subgroup G) (hH : H = ⊤) (σ : Representation ℂ H W) :
    Function.Injective (evalOne H σ) := by
  subst hH
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro v hv
  have h0 : (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 1 = 0 := hv
  have hmem : ∀ (h : (⊤ : Subgroup G)) (x : G),
      (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 (↑h * x) =
        σ h ((v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 x) :=
    (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).2
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have key : (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 x =
      σ ⟨x, Subgroup.mem_top x⟩ ((v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 1) := by
    have := hmem ⟨x, Subgroup.mem_top x⟩ 1
    rwa [mul_one] at this
  rw [key, h0, map_zero]
  first
  | rfl
  | simp

theorem dichotomy {V X T : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup T] [Module ℂ T] [Module.Finite ℂ X] (hX : Module.finrank ℂ X ≤ 1)
    (hT : Module.finrank ℂ T = 1) (ι : V →ₗ[ℂ] X) (hι : Function.Injective ι)
    (φ ψ : V →ₗ[ℂ] T) : φ = 0 ∨ ∃ c : ℂ, ψ = c • φ := by
  classical
  by_cases hφ : φ = 0
  · exact Or.inl hφ
  right
  haveI : Module.Finite ℂ V := Module.Finite.of_injective ι hι
  have hV : Module.finrank ℂ V ≤ 1 := (LinearMap.finrank_le_finrank_of_injective hι).trans hX
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hφ (LinearMap.ext hne)
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv (map_zero φ)
  haveI : Nontrivial V := ⟨⟨v, 0, hv0⟩⟩
  have hV1 : Module.finrank ℂ V = 1 := le_antisymm hV Module.finrank_pos
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (φ v) hv).mp hT (ψ v)
  refine ⟨c, LinearMap.ext fun w => ?_⟩
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' v hv0).mp hV1 w
  first
  | (rw [← ht, map_smul, map_smul, LinearMap.smul_apply, ← hc]; done)
  | (rw [← ht, ← hc]; simp [smul_comm])
  | (subst ht; simp [← hc, smul_smul, mul_comm])

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sizeMatrix_true_false {a b : ℕ}
    (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (h : B.1 false true = 0) :
    B.1 true false = 0 := by
  have hr := B.2.1 false
  have hc := B.2.2 false
  first
  | (rw [Fintype.sum_bool] at hr hc; omega)
  | (simp only [Fintype.sum_bool] at hr hc; omega)

theorem relParab_eq_top {a b : ℕ}
    (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (h : B.1 false true = 0)
    (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j) :
    relParab k (c := fun j i => Fin (B.1 i j)) g = ⊤ := by
  have h' := GlobalTheory.CompanionTheory.CellDiag.sizeMatrix_true_false B h
  rw [eq_top_iff]
  intro x _
  rw [GlobalTheory.SmGL.relParab, Subgroup.mem_pi]
  intro j _
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro p q i i' hqp
  rw [Bool.lt_iff] at hqp
  obtain ⟨rfl, rfl⟩ := hqp
  exfalso
  cases j
  · have := i.isLt
    omega
  · have := i'.isLt
    omega

theorem diag_cell_at_most_one_map : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) i) (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j), B.1 false true = 0 → (∀ φ ψ : (cellFunctor f g ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro k _ _ _ _ a b χ₁ χ₂ B f g h φ ψ
  have hT : Module.finrank ℂ (ℂ ⊗[ℂ] ℂ) = 1 := by
    first
    | rw [Module.finrank_tensorProduct, Module.finrank_self]
    | simp [Module.finrank_tensorProduct]
    | simp
  refine GlobalTheory.CompanionTheory.CellDiag.dichotomy ?_ hT
    (GlobalTheory.CompanionTheory.CellDiag.evalOne _ _)
    (GlobalTheory.CompanionTheory.CellDiag.evalOne_injective _ (GlobalTheory.CompanionTheory.CellDiag.relParab_eq_top (k := k) B h g) _)
    φ.toLinearMap ψ.toLinearMap
  first
  | exact (Submodule.finrank_quotient_le _).trans hT.le
  | exact (Submodule.finrank_quotient_le _).trans (le_of_eq hT)
  | (refine (Submodule.finrank_quotient_le _).trans ?_; simp)

end GlobalTheory.CompanionTheory.CellDiag
end
end

section

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem integrable_prod_detW_rpow : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
    ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
    Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  intro W _ n s hs ν hν
  let μ₀ : Measure (hermC n) := Measure.addHaar
  have hf : ∀ _w : W, Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) μ₀ :=
    fun _ => GlobalTheory.T.hua_determinant_integrable_of_lt n s hs μ₀ inferInstance
  have hpi := Integrable.fintype_prod (μ := fun _ : W => μ₀)
    (f := fun _ : W => fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) hf
  rw [Measure.isAddLeftInvariant_eq_smul ν (Measure.pi fun _ : W => μ₀)]
  exact hpi.smul_measure_nnreal

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end

section

open GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.compactness_statement : GlobalTheory.CompanionTheory.Jp.JpCmp := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Cmp.jpCmp | exact GlobalTheory.CompanionTheory.Jp.Cmp.jpCmp | (intros; apply GlobalTheory.CompanionTheory.Jp.Cmp.jpCmp <;> assumption)
end

section

noncomputable section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
namespace GlobalTheory.CompanionTheory.SiegLoc

theorem gauss1 {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (R ⧸ lev ϖ k)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (hε : (ε : ℂ) ^ 2 = 1) (j : ℕ) (a : R) (ha : σ a = a) (ha' : a ∉ lev ϖ 1) :
    (∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w))) = ((ε : ℂ) * q) ^ j := by
  induction j using Nat.twoStepInduction with
  | zero =>
    have : Subsingleton (R ⧸ lev ϖ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp [lev])
    rw [Fintype.sum_subsingleton _ 0]
    simp
  | one => simpa using GlobalTheory.T.gauss_sum_hermitian_norm_level_one R σ ϖ q ε hR ψ hψ a ha ha'
  | more j ih _ =>
    rw [GlobalTheory.T.gauss_sum_hermitian_norm_level_shift R σ ϖ q ε hR ψ hψ j a ha ha', ih, pow_add, mul_pow (ε : ℂ) (q : ℂ) 2, hε]
    ring

theorem gauss_full {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (R ⧸ lev ϖ k)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (hε : (ε : ℂ) ^ 2 = 1) {m n : ℕ} (k : ℕ) (S : Matrix (Fin m) (Fin m) R) (hS : IsUnimod σ S)
    (B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (hB : B ∈ hermMod σ ϖ n k) :
    (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ψ k (Matrix.trace (B * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x)))) =
      (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) * (((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B)) := by
  obtain ⟨h, hh, rfl⟩ := hB
  obtain ⟨g, g', d, hgg, hgg', hd, hgd⟩ := GlobalTheory.T.hermitian_matrix_diagonalizable R σ ϖ q ε hR n h hh
  obtain ⟨p, p', e, hpp, hpp', he, hpe⟩ := GlobalTheory.T.hermitian_matrix_diagonalizable R σ ϖ q ε hR m S hS.1
  have hq0 : (q : ℂ) ≠ 0 := by
    have := hR.one_lt
    exact_mod_cast (by omega : q ≠ 0)
  have hunit : ∀ l, e l ∉ lev ϖ 1 := by
    intro l hl
    have h1 : IsUnit p.det := Matrix.isUnit_det_of_right_inverse hpp
    have h2 : IsUnit (cT σ p).det := by
      have : cT σ p * cT σ p' = 1 := by
        have : cT σ (p' * p) = cT σ p * cT σ p' := by
          simp [cT, Matrix.transpose_mul, Matrix.map_mul]
        rw [← this, hpp']
        simp [cT]
      exact Matrix.isUnit_det_of_right_inverse this
    have h3 : IsUnit (Matrix.diagonal e).det := by
      rw [← hpe, Matrix.det_mul, Matrix.det_mul]
      exact (h2.mul hS.2).mul h1
    rw [Matrix.det_diagonal] at h3
    have h4 : IsUnit (e l) := isUnit_of_dvd_unit (Finset.dvd_prod_of_mem _ (Finset.mem_univ l)) h3
    obtain ⟨c, hc⟩ := mem_lev_iff.1 hl
    rw [hc, pow_one] at h4
    exact hR.notUnit (isUnit_of_mul_isUnit_left h4)
  choose eI heI hcard hsum using fun i => GlobalTheory.T.card_range_mul_quotient_bounded_level R σ ϖ q ε hR ψ hψ (fun j a ha ha' => gauss1 hR hψ hε j a ha ha') k (d i) (hd i)
  rw [GlobalTheory.T.matrix_gauss_sum_congr_invariance R σ ϖ hR.fix_ϖ hR.inv k (ψ k) m n h _ g g' S _ p p' hgg hgg' hpp hpp' hgd hpe,
    GlobalTheory.T.matrix_gauss_sum_diagonal_factor R σ ϖ hR.fix_ϖ k (ψ k) m n d e,
    GlobalTheory.T.multiplicity_reduction_diagonal_prod R σ ϖ hR.fix_ϖ hR.inv k n h g g' d hgg hgg' hgd]
  have hq2 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) hR.one_lt
  have hnu : (∏ i, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) (d i))) = (q ^ 2) ^ (∑ i, eI i) := by
    rw [Finset.prod_congr rfl (fun i _ => hcard i), Finset.prod_pow_eq_pow_sum]
  rw [hnu, Nat.log_pow hq2]
  have hM : (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) = ((q : ℂ) ^ (2 * k)) ^ (m * n) := by
    have hc : Nat.card (R ⧸ lev ϖ k) = q ^ (2 * k) := GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR k
    have : Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) = (q ^ (2 * k)) ^ (m * n) := by
      show Nat.card (Fin m → Fin n → R ⧸ lev ϖ k) = _
      rw [Nat.card_fun, Nat.card_fun, hc]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      rw [← pow_mul, mul_comm n m]
    rw [this]; push_cast; rfl
  rw [hM]
  have hc' : ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) = ((ε : ℂ) / q) ^ m := by
    rw [div_pow, zpow_neg, zpow_natCast, div_eq_mul_inv]
  rw [hc']
  simp only [fun i l => hsum i (e l) (he l) (hunit l), Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mul_pow, Finset.prod_mul_distrib]
  rw [← pow_mul, ← pow_mul]
  congr 1
  have hx : ∀ x, (((ε : ℂ) / q) ^ eI x) ^ m = (((ε : ℂ) / q) ^ m) ^ eI x := fun x => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [hx]
  rw [Finset.prod_pow_eq_pow_sum]

end GlobalTheory.CompanionTheory.SiegLoc
end
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.delta_block_quotient_injection : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ m : ℕ, ∃ ι : (hermE σ (m + 1) ⧸ hermO σ (m + 1)) → (hermE σ m ⧸ hermO σ m) × ((Fin m → E) ⧸ intVec E m) × FQ F, Function.Injective ι ∧ ∀ x, delta (Quotient.out x).1 = delta (blk σ (Quotient.out (ι x).1).1 (Quotient.out (ι x).2.1) (algebraMap F E ((Quotient.out (ι x).2.2 : Fin 1 → F) 0))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp.hermClass_blocks | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp.hermClass_blocks | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp.hermClass_blocks <;> assumption)
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.torsion_orthogonality_integral_solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (b : E), (∀ t ∈ tor c u, σ (t : E) * b ∈ (1 : Submodule (𝓞 E) E)) → ∃ y : Fin m → 𝓞 E, y ∈ Kc c ∧ b - ∑ j, σ (u j) * (y j : E) ∈ (1 : Submodule (𝓞 E) E) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.dual_cover | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.dual_cover | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.dual_cover <;> assumption)
end
