module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle464
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionRegularOnNonvanishingChart
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle492
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle541
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle493
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpinTensorHighestWeight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKHighestWeight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle509
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle543
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

theorem _root_.GlobalTheory.T.projection_regular_on_nonvanishing_chart : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (N : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog N a →
    ∀ (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ),
      y ∈ c.e.source → GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z → eval z (map (Int.castRingHom ℂ) N) ≠ 0 → Ψ (segre z) 0 ≠ 0 →
      GlobalTheory.CompanionTheory.MixZ.ArchEq.IsRegAt i Ψ c y → y ∈ GlobalTheory.CompanionTheory.MixZ.ArchEq.pieceSet i Ψ N := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.PieceAt.mem_pieceSet | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.PieceAt.mem_pieceSet | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.PieceAt.mem_pieceSet <;> assumption)
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

theorem _root_.GlobalTheory.T.dual_weights_dominated : ∀ {n : ℕ} (lam : Fin n → ℤ), Antitone lam → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T → (⨆ μ, wtDual E μ) = ⊤ ∧ ∀ μ, wtDual E μ ≠ ⊥ → DomLE (wtR μ) (m0 lam) := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.TopeG.topeG | exact GlobalTheory.CompanionTheory.RealCountG.TopeG.topeG | (intros; apply GlobalTheory.CompanionTheory.RealCountG.TopeG.topeG <;> assumption)
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

theorem _root_.GlobalTheory.T.spin_tensor_highest_weight : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    ∀ q : ι → ℂ, q ≠ 0 → (∀ a, spinM c a a *ᵥ q = ((-(rhoV n a) : ℝ) : ℂ) • q) →
    (∀ a b, a < b → spinM c b a *ᵥ q = 0) →
    ∀ {Z : Type} [AddCommGroup Z] [Module ℂ Z] (E : Fin n → Fin n → Module.End ℂ Z), Formalism.REAL.GlRel E →
    ∀ (ν : Fin n → ℝ) (z : Z), (∀ a, E a a z = ((ν a - rhoV n a : ℝ) : ℂ) • z) →
    (∀ i j : Fin n, (j : ℕ) = i + 1 → ((E i j) ^ 2) z = 0) →
    ∃ φ : (ι → ℂ) →ₗ[ℂ] Z, φ q = z ∧ (∀ a b, a < b → ∀ f, φ (spinM c a b *ᵥ f) = E a b (φ f)) ∧
      ∀ a f, φ (spinM c a a *ᵥ f) = E a a (φ f) - ((ν a : ℝ) : ℂ) • φ f := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.SpinMap.exists_spin_map | exact GlobalTheory.CompanionTheory.RealCount.SpinMap.exists_spin_map | (intros; apply GlobalTheory.CompanionTheory.RealCount.SpinMap.exists_spin_map <;> assumption)
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

theorem _root_.GlobalTheory.T.exists_dual_lie_family : ∀ {n : ℕ} (E : KMod n), ∃ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.dualFam_exists | exact GlobalTheory.CompanionTheory.RealCountG.dualFam_exists | (intros; apply GlobalTheory.CompanionTheory.RealCountG.dualFam_exists <;> assumption)
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.inducedFunction_k_finite : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ F : GlobalTheory.CompanionTheory.ModelS.SmF n, F.1 = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev → ∃ S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n), FiniteDimensional ℂ S ∧ F ∈ S ∧ ∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.FFin.fRaw_finite | exact GlobalTheory.CompanionTheory.ModelS.FFin.fRaw_finite | (intros; apply GlobalTheory.CompanionTheory.ModelS.FFin.fRaw_finite <;> assumption)
end

section

open PositivityTheory.RgBcC.RealD (IsLev)
open GlobalTheory.CompanionTheory.ModelS (SmF fRaw Kf muZ)

theorem GlobalTheory.T.inducedFunction_k_highest_weight :
    ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam →
      ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ F : SmF n, F.1 = fRaw lam lev →
        (∀ a b : Fin n, a < b → Kf a b F = 0) ∧
          ∀ a : Fin n, Kf a a F = (muZ lam lev a : ℂ) • F :=
  GlobalTheory.CompanionTheory.ModelS.f_highest
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem dsum_stronglyMeasurable : ∀ {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (Φ : Mx D ρ p → ℂ), StronglyMeasurable Φ → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖)) → StronglyMeasurable (fun v : Mx D ρ p × Mx D ρ p => GlobalTheory.CompanionTheory.FJE.dsum ψ b₀ Φ v.2 v.1) := by
  intro D ρ p ψ hψ b₀ Φ hΦ hs
  haveI := (GlobalTheory.T.countable_matrices_and_cosets D ρ p).1
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  obtain ⟨_, _, _, _, _, hc⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws ψ hψ b₀
  have hterm : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, Measurable fun v : Mx D ρ p × Mx D ρ p =>
      GlobalTheory.CompanionTheory.FJE.chv ψ b₀ v.2 (GlobalTheory.CompanionTheory.FJE.rt ξ) * Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + v.1) := by
    intro ξ
    have h1 : Measurable fun y : Mx D ρ p => GlobalTheory.CompanionTheory.FJE.chv ψ b₀ y (GlobalTheory.CompanionTheory.FJE.rt ξ) :=
      (hc.comp (continuous_id.prodMk continuous_const)).measurable
    have h2 : Measurable fun y : Mx D ρ p => Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y) :=
      hΦ.measurable.comp (continuous_const_add (GlobalTheory.CompanionTheory.FJE.rt ξ)).measurable
    exact (h1.comp measurable_snd).mul (h2.comp measurable_fst)
  exact (Measurable.tsum hterm).stronglyMeasurable

end GlobalTheory.CompanionTheory.FJE
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {ρ p : ℕ}

open scoped Pointwise

theorem trace_single_mul_eq {R : Type} [CommRing R] {a b : ℕ} (j : Fin a) (i : Fin b) (w : R)
    (M : Matrix (Fin b) (Fin a) R) : Matrix.trace (Matrix.single j i w * M) = w * M i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem trA_algebraMap_half [Nontrivial (AF D.host.F)] (t : AF D.host.F) :
    trA (D := D) (algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2) * t)) = t := by
  have h2 : Module.finrank D.host.F D.host.E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  show Algebra.trace (AF D.host.F) (AE D) (algebraMap (AF D.host.F) (AE D)
    (algebraMap D.host.F (AF D.host.F) (1 / 2) * t)) = t
  rw [Algebra.trace_algebraMap, Module.finrank_baseChange, h2, two_nsmul, ← add_mul, ← map_add (f := _)]
  norm_num

theorem exists_chv_ne_one (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (hdet : b₀.1.det ≠ 0) (ζ : Matrix (Fin ρ) (Fin p) D.host.E) (hζ : ζ ≠ 0) :
    ∃ x₀ : Mx D ρ p, chv ψ b₀ x₀ (rt ζ) ≠ 1 := by
  obtain ⟨-, -, -, t, ht⟩ := hψ
  have hB : b₀.1 * ζ ≠ 0 := by
    intro h0
    apply hζ
    have hu : IsUnit b₀.1.det := isUnit_iff_ne_zero.2 hdet
    calc ζ = b₀.1⁻¹ * (b₀.1 * ζ) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = 0 := by rw [h0, Matrix.mul_zero]
  obtain ⟨i, j, hij⟩ : ∃ i j, (b₀.1 * ζ) i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hB (Matrix.ext hc)
  obtain ⟨c, hc⟩ : ∃ c : AE D, c = algebraMap (AF D.host.F) (AE D)
      (algebraMap D.host.F (AF D.host.F) (1 / 2) * t) * incA D ((b₀.1 * ζ) i j)⁻¹ := ⟨_, rfl⟩
  refine ⟨adj (Matrix.single j i c), ?_⟩
  have key : Matrix.trace (pr b₀ (adj (Matrix.single j i c)) (rt ζ)) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2) * t) := by
    show Matrix.trace (adj (adj (Matrix.single j i c)) * (b₀.1.map (incA D) * rt ζ)) = _
    rw [adj_adj, show b₀.1.map (incA D) * rt ζ = rat (b₀.1 * ζ) from (rat_mul _ _).symm,
      trace_single_mul_eq]
    show c * incA D ((b₀.1 * ζ) i j) = _
    rw [hc, mul_assoc, ← map_mul, inv_mul_cancel₀ hij, map_one, mul_one]
  show ψ (trA (Matrix.trace (pr b₀ _ (rt ζ)))) ≠ 1
  haveI : Nontrivial (AF D.host.F) :=
    nontrivial_of_ne t 0 (fun h => ht (by rw [h, AddChar.map_zero_eq_one]))
  rw [key, trA_algebraMap_half]
  exact ht

theorem integral_chv_rt_eq_zero {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (hdet : b₀.1.det ≠ 0)
    (ζ : Matrix (Fin ρ) (Fin p) D.host.E) (hζ : ζ ≠ 0) :
    ∫ x in m.𝓕, chv ψ b₀ x (rt ζ) ∂m.μ = 0 := by
  obtain ⟨x₀, hx₀⟩ := exists_chv_ne_one ψ hψ b₀ hdet ζ hζ
  obtain ⟨hadd, -, -, -, hrat, -⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws ψ hψ b₀
  have hper : ∀ γ ∈ ratMx D ρ p, ∀ a, chv ψ b₀ (γ + a) (rt ζ) = chv ψ b₀ a (rt ζ) := by
    intro γ hγ a
    obtain ⟨g, rfl⟩ := mem_ratMx.1 hγ
    rw [hadd, show rat g = rt g from rfl, hrat, one_mul]
  have h := covolOne_integral_add m.hμ (fun x => chv ψ b₀ x (rt ζ)) hper x₀
  simp only [hadd] at h
  rw [MeasureTheory.integral_mul_const] at h
  have h2 : (∫ x in m.𝓕, chv ψ b₀ x (rt ζ) ∂m.μ) * (chv ψ b₀ x₀ (rt ζ) - 1) = 0 := by
    rw [mul_sub, mul_one, h, sub_self]
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hx₀)

end GlobalTheory.CompanionTheory.FJE
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {ρ p : ℕ}

theorem rt_add_periodic (ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E) :
    rt (ξ + ξ') = (rt ξ + rt ξ' : Mx D ρ p) := by
  ext i j
  simp [rt, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]

theorem dsum_add_rt (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (Φ : Mx D ρ p → ℂ) (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (x y : Mx D ρ p) :
    dsum ψ b₀ Φ x (y + rt ξ) = conj (chv ψ b₀ x (rt ξ)) * dsum ψ b₀ Φ x y := by
  obtain ⟨-, h2, h3, -, -, -⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws (D := D) (ρ := ρ) (p := p) ψ hψ b₀
  unfold dsum
  rw [← tsum_mul_left, ← (Equiv.addRight ξ).tsum_eq
    (fun η : Matrix (Fin ρ) (Fin p) D.host.E =>
      conj (chv ψ b₀ x (rt ξ)) * (chv ψ b₀ x (rt η) * Φ (rt η + y)))]
  refine tsum_congr fun η => ?_
  have hn : conj (chv ψ b₀ x (rt ξ)) * chv ψ b₀ x (rt ξ) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h3]
    simp
  simp only [Equiv.coe_addRight]
  rw [rt_add_periodic, h2, show rt η + rt ξ + y = rt η + (y + rt ξ) by abel]
  linear_combination (-(chv ψ b₀ x (rt η) * Φ (rt η + (y + rt ξ)))) * hn

theorem dsum_add_rt_left (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (Φ : Mx D ρ p → ℂ) (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (x y : Mx D ρ p) :
    dsum ψ b₀ Φ (x + rt ξ) y = dsum ψ b₀ Φ x y := by
  obtain ⟨h1, -, -, -, h5, -⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws (D := D) (ρ := ρ) (p := p) ψ hψ b₀
  unfold dsum
  refine tsum_congr fun η => ?_
  rw [h1, h5, mul_one]

theorem ap_periodic (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (Φ φ : Mx D ρ p → ℂ) (ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E)
    (v : Mx D ρ p × Mx D ρ p) :
    Ap ψ b₀ Φ φ (v + (rt ξ₁, rt ξ₂)) = Ap ψ b₀ Φ φ v := by
  obtain ⟨-, -, h3, -, -, -⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws (D := D) (ρ := ρ) (p := p) ψ hψ b₀
  obtain ⟨y, x⟩ := v
  show dsum ψ b₀ Φ (x + rt ξ₂) (y + rt ξ₁) * conj (dsum ψ b₀ φ (x + rt ξ₂) (y + rt ξ₁)) =
    dsum ψ b₀ Φ x y * conj (dsum ψ b₀ φ x y)
  have hn : conj (chv ψ b₀ x (rt ξ₁)) * chv ψ b₀ x (rt ξ₁) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h3]
    simp
  rw [dsum_add_rt_left ψ hψ, dsum_add_rt_left ψ hψ, dsum_add_rt ψ hψ, dsum_add_rt ψ hψ, map_mul,
    Complex.conj_conj]
  linear_combination (dsum ψ b₀ Φ x y * conj (dsum ψ b₀ φ x y)) * hn

theorem ap_periodic_all : ∀ {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ (b₀ : HermE D ρ) (Φ φ : Mx D ρ p → ℂ) (ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E)
      (v : Mx D ρ p × Mx D ρ p),
      GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ Φ φ (v + (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂)) = GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ Φ φ v :=
  fun ψ hψ b₀ Φ φ ξ₁ ξ₂ v => ap_periodic ψ hψ b₀ Φ φ ξ₁ ξ₂ v

end GlobalTheory.CompanionTheory.FJE
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.TransportLoc

variable {G G' : Type} [Group G] [Group G']

theorem mem_twCent_iff (e : G ≃* G') (θ : G →* G) (θ' : G' →* G') (h : ∀ x, e (θ x) = θ' (e x)) (d x : G) :
    x ∈ twCent θ d ↔ e x ∈ twCent θ' (e d) := by
  show x * d = d * θ x ↔ e x * e d = e d * θ' (e x)
  rw [← h, ← map_mul, ← map_mul, e.injective.eq_iff]

theorem map_twConj (e : G ≃* G') (θ : G →* G) (θ' : G' →* G') (h : ∀ x, e (θ x) = θ' (e x)) (d y : G) :
    e (y⁻¹ * d * θ y) = (e y)⁻¹ * e d * θ' (e y) := by
  simp only [map_mul, map_inv, h]

theorem twConj_mul (θ : G →* G) (d t w : G) (ht : t ∈ twCent θ d) :
    (t * w)⁻¹ * d * θ (t * w) = w⁻¹ * d * θ w := by
  have ht' : t * d = d * θ t := ht
  rw [map_mul, _root_.mul_inv_rev]
  calc w⁻¹ * t⁻¹ * d * (θ t * θ w) = w⁻¹ * t⁻¹ * (d * θ t) * θ w := by group
    _ = w⁻¹ * d * θ w := by rw [← ht']; group

theorem finite_support (e : G ≃* G') (θ : G →* G) (θ' : G' →* G')
    (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ)
    (hθ : ∀ x, e (θ x) = θ' (e x)) (hK : ∀ x, x ∈ K ↔ e x ∈ K') (hf : ∀ x, f x = f' (e x))
    (hfin : {q : DoubleCoset.Quotient (twCent θ' (e d) : Set G') (K' : Set G') |
      ∃ k ∈ K', f' ((Quotient.out q * k)⁻¹ * e d * θ' (Quotient.out q * k)) ≠ 0}.Finite) :
    {q : DoubleCoset.Quotient (twCent θ d : Set G) (K : Set G) |
      ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * d * θ (Quotient.out q * k)) ≠ 0}.Finite := by
  refine Set.Finite.of_injOn
    (f := fun q : DoubleCoset.Quotient (twCent θ d : Set G) (K : Set G) =>
      DoubleCoset.mk (twCent θ' (e d)) K' (e (Quotient.out q))) ?_ ?_ hfin
  · rintro q ⟨k, hk, hne⟩
    obtain ⟨t, ht₀, k₁, hk₁, hout⟩ := DoubleCoset.mk_out_eq_mul (twCent θ' (e d)) K' (e (Quotient.out q))
    refine ⟨k₁⁻¹ * e k, K'.mul_mem (K'.inv_mem hk₁) ((hK k).1 hk), ?_⟩
    have hmul : Quotient.out (DoubleCoset.mk (twCent θ' (e d)) K' (e (Quotient.out q))) *
        (k₁⁻¹ * e k) = t * e (Quotient.out q * k) := by
      rw [hout, map_mul]; group
    simp only []
    rw [hmul, twConj_mul θ' (e d) t _ ht₀, ← map_twConj e θ θ' hθ, ← hf]
    exact hne
  · intro q₁ _ q₂ _ heq
    obtain ⟨t', ht', k', hk', hy⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 heq
    have h₂ : Quotient.out q₂ = e.symm t' * Quotient.out q₁ * e.symm k' := by
      apply e.injective
      simp only [map_mul, e.apply_symm_apply]
      exact hy
    have ht : e.symm t' ∈ twCent θ d := by
      rw [mem_twCent_iff e θ θ' hθ, e.apply_symm_apply]; exact ht'
    have hk : e.symm k' ∈ K := by
      rw [hK, e.apply_symm_apply]; exact hk'
    rw [← DoubleCoset.out_eq' q₁, ← DoubleCoset.out_eq' q₂]
    exact (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨_, ht, _, hk, h₂⟩

theorem index_ne_zero (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G') (hK : ∀ x, x ∈ K ↔ e x ∈ K')
    (u : K → ℂ) (u' : K' → ℂ) (hu : ∀ k : K, u k = u' ⟨e k, (hK k).1 k.2⟩)
    (h : (rStab u').index ≠ 0) : (rStab u).index ≠ 0 := by
  let φ : K →* K' :=
    { toFun := fun k => ⟨e k, (hK k).1 k.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hφ : Function.Surjective φ := fun k' =>
    ⟨⟨e.symm k', by rw [hK, e.apply_symm_apply]; exact k'.2⟩, by ext; simp [φ]⟩
  have hu' : ∀ k : K, u k = u' (φ k) := hu
  have hstab : rStab u = (rStab u').comap φ := by
    ext k
    constructor
    · intro hk x'
      obtain ⟨x, rfl⟩ := hφ x'
      show u' (φ x * φ k) = u' (φ x)
      rw [← map_mul, ← hu', ← hu']
      exact hk x
    · intro hk x
      show u (x * k) = u x
      rw [hu', hu', map_mul]
      exact hk (φ x)
  rw [hstab, Subgroup.index_comap_of_surjective _ hφ]
  exact h

theorem mem_conj_iff (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G') (hK : ∀ x, x ∈ K ↔ e x ∈ K') (y x : G) :
    x ∈ K.map (MulAut.conj y).toMonoidHom ↔ e x ∈ K'.map (MulAut.conj (e y)).toMonoidHom := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨e k, (hK k).1 hk, by simp [MulAut.conj_apply]⟩
  · rintro ⟨k', hk', h⟩
    refine ⟨e.symm k', by rw [SetLike.mem_coe, hK, e.apply_symm_apply]; exact hk', ?_⟩
    apply e.injective
    rw [← h]
    simp [MulAut.conj_apply]

variable [TopologicalSpace G] [TopologicalSpace G']

theorem isCompact_closure_zpowers_iff (e : G ≃ₜ* G') (t : G) :
    IsCompact (closure (Subgroup.zpowers t : Set G)) ↔
      IsCompact (closure (Subgroup.zpowers (e t) : Set G')) := by
  have h : (Subgroup.zpowers (e t) : Set G') = e.toHomeomorph '' (Subgroup.zpowers t : Set G) := by
    have := MonoidHom.map_zpowers e.toMulEquiv.toMonoidHom t
    exact (congrArg (fun S : Subgroup G' => (S : Set G')) this).symm
  rw [h, ← e.toHomeomorph.image_closure, e.toHomeomorph.isCompact_image]

theorem map_cptPart (e : G ≃ₜ* G') (T : Subgroup G) (T' : Subgroup G') (hT : ∀ x, x ∈ T ↔ e x ∈ T') :
    (cptPart T).map e.toMulEquiv.toMonoidHom = cptPart T' := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  ext t'
  constructor
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨(hT t).1 ht, (isCompact_closure_zpowers_iff e t).1 hc⟩
  · rintro ⟨ht', hc⟩
    refine ⟨e.symm t', ⟨?_, ?_⟩, e.apply_symm_apply t'⟩
    · rw [hT]; simpa using ht'
    · rw [isCompact_closure_zpowers_iff e]; simpa using hc

theorem locConds_of_equiv : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → LocConds θ' K' (e d) f' → LocConds θ K d f := by
  intro G G' _ _ _ _ e θ θ' K K' d f f' hθ hK hf h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  have hθm : ∀ x, e.toMulEquiv (θ x) = θ' (e.toMulEquiv x) := hθ
  have hKm : ∀ x, x ∈ K ↔ e.toMulEquiv x ∈ K' := hK
  have hfm : ∀ x, f x = f' (e.toMulEquiv x) := hf
  have hT : ∀ x, x ∈ twCent θ d ↔ e.toMulEquiv x ∈ twCent θ' (e.toMulEquiv d) :=
    mem_twCent_iff e.toMulEquiv θ θ' hθm d
  refine ⟨?_, ?_, finite_support e.toMulEquiv θ θ' K K' d f f' hθm hKm hfm h₃, ?_⟩
  · intro x hx y hy
    apply e.toMulEquiv.injective
    rw [map_mul, map_mul]
    exact h₁ _ ((hT x).1 hx) _ ((hT y).1 hy)
  · intro y
    refine index_ne_zero e.toMulEquiv K K' hKm _ _ ?_ (h₂ (e y))
    intro k
    have := map_twConj e.toMulEquiv θ θ' hθm d (y * k)
    rw [hfm, this, map_mul]
    rfl
  · intro y
    obtain ⟨ha, hb⟩ := h₄ (e y)
    have hB := map_cptPart e (twCent θ d) (twCent θ' (e d)) hT
    have hA : twCent θ d ⊓ K.map (MulAut.conj y).toMonoidHom =
        (twCent θ' (e d) ⊓ K'.map (MulAut.conj (e y)).toMonoidHom).comap e.toMulEquiv.toMonoidHom := by
      ext x
      rw [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_inf]
      exact and_congr (hT x) (mem_conj_iff e.toMulEquiv K K' hKm y x)
    constructor
    · rw [hA]
      intro x hx
      have hx' := ha hx
      rw [← hB] at hx'
      obtain ⟨z, hz, hzx⟩ := hx'
      rwa [← e.toMulEquiv.injective hzx]
    · rw [hA, Subgroup.relIndex_comap, hB]
      exact hb

end GlobalTheory.CompanionTheory.TransportLoc

end
end
