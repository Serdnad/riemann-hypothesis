module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle019
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle485
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle489
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle355
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle340
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle590
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle551
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle054
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle137
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle686
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DnFormApprox
variable {D : D7}
end GlobalTheory.DnFormApprox
namespace GlobalTheory.DnFormApprox
theorem decay_integral_approximation (s2 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → ∀ M : ℕ, ∃ (d : ℕ) (C : NNReal), ∀ ψ : GA D (G.P (i + 1)).V → ℂ, IsAutFun (G.P (i + 1)).V ψ → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, ψ (g * k) = ψ g) → ψ ∈ GlobalTheory.Mem.AutSpace.SmFun R.θ (G.P (i + 1)).V → (∀ k, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V k 0 ψ ≠ ⊤) → IsCuspFun (G.P (i + 1)).V ψ → GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M ψ ≤ (C : ENNReal) * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 ψ) (s3 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, φ (g * k) = φ g) → ∀ (d : ℕ) (δ : ENNReal), 0 < δ → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ k ∈ K, ∀ u ∈ U, u ∈ GfC (G.P (i + 1)).V → ∀ g, F k (v k) (g * u) = F k (v k) g) ∧ (∀ e, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V e 0 (φ - ∑ k ∈ K, F k (v k)) ≠ ⊤) ∧ GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) < δ) : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∀ (M : ℕ) (δ : ENNReal), 0 < δ → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M (φ - ∑ k ∈ K, F k (v k)) < δ := by
  intro hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi φ hφ M δ hδ
  obtain ⟨U, hU, hk⟩ := hφ.1.level
  obtain ⟨d, C, hC⟩ := s2 hP D hS G₀ Pl0 T A Ks R G hB hG i hi U hU M
  set C' : ENNReal := (C : ENNReal) + 1 with hC'
  have hC0 : C' ≠ 0 := by simp [C']
  have hCt : C' ≠ ⊤ := by simp [C']
  obtain ⟨K, F, v, hF, hlev, hfin, hd⟩ := s3 hP D hS G₀ Pl0 T A Ks R G hB hG i hi φ hφ U hU hk d (δ / C')
    (ENNReal.div_pos hδ.ne' hCt)
  refine ⟨K, F, v, hF, ?_⟩
  have hs := autSm_cusp_sum K (fun k => F k (v k)) fun k hk => autSm_cusp_of_mem_cusp _ _ (hF k hk) (v k)
  have hψ : IsAutFunSm R.θ (G.P (i + 1)).V (φ - ∑ k ∈ K, F k (v k)) ∧ IsCuspFun (G.P (i + 1)).V (φ - ∑ k ∈ K, F k (v k)) := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (∑ k ∈ K, F k (v k))]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hφ.1 (GlobalTheory.MultMem.isAutFunSm_smul _ hs.1),
      GlobalTheory.MultMem.isCuspFun_add hφ.1.toIsAutFun (GlobalTheory.MultMem.isAutFunSm_smul _ hs.1).toIsAutFun hφ.2.1
        (GlobalTheory.MultMem.isCuspFun_smul _ hs.2)⟩
  have hlevψ : ∀ u ∈ U, u ∈ GfC (G.P (i + 1)).V → ∀ g, (φ - ∑ k ∈ K, F k (v k)) (g * u) = (φ - ∑ k ∈ K, F k (v k)) g := by
    intro u hu hu' g
    simp only [Pi.sub_apply, Finset.sum_apply]
    rw [hk u hu hu' g]
    congr 1
    exact Finset.sum_congr rfl fun k hkK => hlev k hkK u hu hu' g
  calc GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M (φ - ∑ k ∈ K, F k (v k))
      ≤ (C : ENNReal) * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) :=
        hC _ hψ.1.toIsAutFun hlevψ hψ.1.smooth hfin hψ.2
    _ ≤ C' * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) :=
        by gcongr; exact le_self_add
    _ < C' * (δ / C') := ENNReal.mul_lt_mul_right hC0 hCt hd
    _ = δ := ENNReal.mul_div_cancel hC0 hCt
theorem downward_form_approximation_of_decay (s1 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∃ C : NNReal, ∀ f : GA D (G.P (i + 1)).V → ℂ, GlobalTheory.Size.growthSize (G.P i).V N (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * f g ∂(G.mP (i + 1)).ν) ≤ (C : ENNReal) * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N f) (s2 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → ∀ M : ℕ, ∃ (d : ℕ) (C : NNReal), ∀ ψ : GA D (G.P (i + 1)).V → ℂ, IsAutFun (G.P (i + 1)).V ψ → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, ψ (g * k) = ψ g) → ψ ∈ GlobalTheory.Mem.AutSpace.SmFun R.θ (G.P (i + 1)).V → (∀ k, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V k 0 ψ ≠ ⊤) → IsCuspFun (G.P (i + 1)).V ψ → GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd M ψ ≤ (C : ENNReal) * GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 ψ) (s3 : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, φ (g * k) = φ g) → ∀ (d : ℕ) (δ : ENNReal), 0 < δ → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ k ∈ K, ∀ u ∈ U, u ∈ GfC (G.P (i + 1)).V → ∀ g, F k (v k) (g * u) = F k (v k) g) ∧ (∀ e, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V e 0 (φ - ∑ k ∈ K, F k (v k)) ≠ ⊤) ∧ GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) < δ) : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * φ g ∂(G.mP (i + 1)).ν) - ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε := by
  intro hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi φ hφ
  obtain ⟨N, hN⟩ := s1 hP D hS G₀ Pl0 T A Ks R G hB hG i hi
  refine ⟨N, fun Φ hΦ ε hε => ?_⟩
  obtain ⟨C, hC⟩ := hN Φ hΦ
  set C' : ENNReal := (C : ENNReal) + 1 with hC'
  have hC0 : C' ≠ 0 := by simp [C']
  have hCt : C' ≠ ⊤ := by simp [C']
  obtain ⟨K, F, v, hF, hd⟩ := _root_.GlobalTheory.DnFormApprox.decay_integral_approximation s2 s3 hP D hS G₀ Pl0 T A Ks R G hB hG i hi φ hφ N (ε / C')
    (ENNReal.div_pos hε.ne' hCt)
  refine ⟨K, F, v, hF, ?_⟩
  obtain ⟨hν, h𝓕⟩ := GlobalTheory.DownConv.MeasDat.haar_fd (hG.meas.P (i + 1) hi)
  have hint : ∀ u : GA D (G.P (i + 1)).V → ℂ, IsAutFunSm R.θ (G.P (i + 1)).V u → IsCuspFun (G.P (i + 1)).V u → ∀ h,
      IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * u g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := fun u hu hc h =>
    GlobalTheory.DownConv.integrableOn_thetaKO_mul_cusp hP.cuspRapidDecay hB.inf true ((hG.arrows.dn i hi).weil) hΦ hν h𝓕 hu hc h
  have e : (fun h => (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) -
      ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * (F k (v k)) g ∂(G.mP (i + 1)).ν) =
      fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * (φ - ∑ k ∈ K, F k (v k)) g ∂(G.mP (i + 1)).ν := by
    funext h
    have hk : ∀ k ∈ K, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * (F k (v k)) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν :=
      fun k hk => hint _ (autSm_cusp_of_mem_cusp _ _ (hF k hk) (v k)).1 (autSm_cusp_of_mem_cusp _ _ (hF k hk) (v k)).2 h
    rw [← integral_finsetSum _ hk, ← integral_sub (hint φ hφ.1 hφ.2.1 h) (integrable_finsetSum _ hk)]
    congr 1
    funext g
    simp [Pi.sub_apply, Finset.sum_apply, mul_sub, Finset.mul_sum]
  rw [e]
  calc GlobalTheory.Size.growthSize (G.P i).V N (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * (φ - ∑ k ∈ K, F k (v k)) g ∂(G.mP (i + 1)).ν)
      ≤ (C : ENNReal) * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N (φ - ∑ k ∈ K, F k (v k)) := hC _
    _ ≤ C' * GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.decayInt (G.mP (i + 1)).ν (G.mP (i + 1)).fd N (φ - ∑ k ∈ K, F k (v k)) :=
        by gcongr; exact le_self_add
    _ < C' * (ε / C') := ENNReal.mul_lt_mul_right hC0 hCt hd
    _ = ε := ENNReal.mul_div_cancel hC0 hCt
end GlobalTheory.DnFormApprox
namespace GlobalTheory.DnFormApprox
theorem downward_form_approximation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * φ g ∂(G.mP (i + 1)).ν) - ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε :=
  _root_.GlobalTheory.DnFormApprox.downward_form_approximation_of_decay _root_.GlobalTheory.T.lifted_growth_bounded_by_decay_integral _root_.GlobalTheory.T.decay_integral_bounded_by_sobolev_growth _root_.GlobalTheory.T.cuspForm_sobolev_density
end GlobalTheory.DnFormApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twisted_form_downward_approximation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * φ g ∂(G.mP (i + 1)).ν) - ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε := by
  first | exact @_root_.GlobalTheory.DnFormApprox.downward_form_approximation | exact _root_.GlobalTheory.DnFormApprox.downward_form_approximation | (intros; apply _root_.GlobalTheory.DnFormApprox.downward_form_approximation <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.LocActV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.WeilM
theorem finite_adele_acts_placewise : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    (∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V.J,
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1) = 0) →
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = G.M.vac v) ∧
          (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v) ∧
          om (g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ') ∧
    ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V'.J,
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1) = 0) →
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = G.M'.vac v) ∧
          (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' v) ∧
          om' (g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hT
  obtain ⟨S₀, hS₀⟩ := _root_.GlobalTheory.T.lattice_stabilizer_fixes_vacuum_vector hPr F E σ B a a' G X om om' hT
  have key : ∀ {n : ℕ} (Y : Spc F E n) (M : Model σ Y G.W) (χX χW : Chr F E) (ω : Rep σ Y G.W) (r s r' s' : ℕ),
      GlobalTheory.ThK.IsPair B M χX χW ω r s r' s' →
      (∀ v ∉ S₀, ∀ k ∈ GlobalTheory.InertSph.KAt σ Y v, Acts (evFin F v) (ω (k, 1)) (M.vac v) (M.vac v)) →
      ∀ g : UA σ Y.J, (∀ u : AF F, At (evI F) u → u • (mat g - 1) = 0) →
      ∀ (f : SInf F (Fin n × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ SB (Fin n × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ SB (Fin n × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = M.vac v) ∧
          (∀ v, φ' v - φ v ∈ augAt ω v) ∧ ω (g, 1) (pure f φ) = pure f φ' := by
    intro n Y M χX χW ω r s r' s' hP hsph g hg f φ hφ hvac
    classical
    obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.exists_finset_adelicUnitary_preserves_lattice_almost_all σ Y hP.herm.lat g
    have hfin := Filter.eventually_cofinite.1 hvac
    set S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) := S₀ ∪ S₁ ∪ hfin.toFinset with hSdef
    obtain ⟨gS, k, hgk, hgS, hkS, hkI, hkL⟩ := GlobalTheory.T.exists_adelicUnitary_factor_finiteSetOfPlaces σ Y g S
    obtain ⟨φ', hφ'SB, hφ'off, hφ'aug, hφ'eq⟩ := GlobalTheory.T.finiteSupport_unitaryPoint_replaces_pureTensorFactors σ B Y G.W M χX χW ω r s r' s' hP S gS hgS f φ hφ hvac
    have hk : ω (k, 1) (pure f φ) = pure f φ := by
      refine GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor_left σ B Y G.W M χX χW ω r s r' s' hP S (fun v hv => hsph v (fun h => hv (by simp [hSdef, h])))
        k (fun u hu => by rw [hkI u hu]; exact hg u hu) hkS (fun w hw z hz => ?_) f φ hφ (fun w hw => ?_)
      · have hw1 : w ∉ S₁ := fun h => hw (by simp [hSdef, h])
        rw [(hkL w hw z hz).1, (hkL w hw z hz).2]
        exact hS₁ w hw1 z hz
      · by_contra hne
        exact hw (by simp [hSdef, hne])
    refine ⟨φ', hφ'SB, ?_, hφ'aug, ?_⟩
    · filter_upwards [hvac, S.finite_toSet.compl_mem_cofinite] with v hv hvS
      rw [hφ'off v hvS, hv]
    · have e : ((g, 1) : UA σ Y.J × UA σ G.W.J) = (gS, 1) * (k, 1) := by
        rw [hgk, Prod.mk_mul_mk, one_mul]
      rw [e, map_mul, Module.End.mul_apply, hk, hφ'eq]
  exact ⟨fun g hg f φ hφ hvac => key G.V G.M _ _ om _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT) (fun v hv => (hS₀ v hv).1) g hg f φ hφ hvac,
    fun g hg f φ hφ hvac => key G.V' G.M' _ _ om' _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hT) (fun v hv => (hS₀ v hv).2) g hg f φ hφ hvac⟩
end GlobalTheory.LocActV
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.local_action_finite_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    (∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V.J,
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1) = 0) →
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = G.M.vac v) ∧
          (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v) ∧
          om (g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ') ∧
    ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V'.J,
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1) = 0) →
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = G.M'.vac v) ∧
          (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' v) ∧
          om' (g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' := by
  first | exact @_root_.GlobalTheory.LocActV.finite_adele_acts_placewise | exact _root_.GlobalTheory.LocActV.finite_adele_acts_placewise | (intros; apply _root_.GlobalTheory.LocActV.finite_adele_acts_placewise <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
open scoped ComplexOrder
open GlobalTheory.ClassRegroup GlobalTheory.DefiniteClassAvg GlobalTheory.DefiniteClassReal
namespace GlobalTheory.RowTest.BottomClassSum
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}
theorem integral_eq_bottom_classSum : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (v : ℝ) (N : ℕ) (z : Fin N → GA D A') (w : Fin N → ℕ) (κ : Measure (GinfC A')), 0 < v ∧ (∀ l, z l ∈ GfC A') ∧
      (∀ l, 0 < w l) ∧ κ.IsMulLeftInvariant ∧ IsProbabilityMeasure κ ∧
      ∀ (t : T) (P : PolF D WW.rank A'.rank), ∀ h ∈ GfC WW,
        X.I' W.ψ W.θ t P h = (v : ℂ) * ∑ l, ((w l : ℂ))⁻¹ * ∫ g, X.ker' W.ψ W.θ t P h (z l * (g : GA D A')) ∂κ := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ hL hX
  have hV : ∀ φ : D.host.E →+* ℂ, (A'.gram.map φ).PosDef := fun φ => by
    rw [hX.std'.1, Matrix.map_one φ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one
  let V' : HSp D := { A' with sig := fun _ => (A'.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC A' : Set (GA D A')) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  haveI : CompactSpace (GinfC A') := isCompact_iff_compactSpace.1 hGc
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A'
  have hLC := hT.1
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  obtain ⟨K'', hK'', hr⟩ := level_all μ₀ hX
  have hfin0 : Finite (FinCl A' K'') := (finite_finCl_and_gamOrd A' K'' hV hK'').1
  let μ := X.m'
  haveI : μ.IsHaarMeasure := hX.is.meas'.1
  have hfd : IsFundamentalDomain (GQ A') X.fd' μ := hX.is.meas'.2
  let J : Subgroup (GA D A') := K''.comap (Lev.finE A')
  have hJo : IsOpen (J : Set (GA D A')) := hK''.1
  have hJc : IsCompact (J : Set (GA D A')) := by
    refine (hK''.2.mul hGc).of_isClosed_subset (Subgroup.isClosed_of_isOpen J hK''.1) ?_
    intro k hk
    exact ⟨finPart A' k, finPart_mem_levA A' hk, realPart A' k, realPart_mem A' k, finPart_mul_realPart A' k⟩
  have hJtop : μ J ≠ ⊤ := hJc.measure_lt_top.ne
  have hJ0 : μ J ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have hinfJ : GinfC A' ≤ J := by
    show GinfC A' ≤ K''.comap (Lev.finE A')
    rw [GlobalTheory.Mass.Levels.comap_finE]
    exact le_sup_right
  let κ : Measure (GinfC A') := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (GinfC A'))
  haveI hκH : κ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hκ1 : κ Set.univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC A')))
    simpa using this
  haveI : IsProbabilityMeasure κ := ⟨hκ1⟩
  let e := finEquiv A'
  have he : ∀ γ, e (((finPt A').comp (GQ A').subtype) γ) = Bridge.ratF A' γ := fun γ => e.apply_symm_apply _
  have hJe : ∀ a, e a ∈ GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin A' K'' ↔ a ∈ K''.comap (finG A') := fun a => Iff.rfl
  have hy := isReps_transfer _ _ e he _ _ hJe _ (isReps_out A' K'')
  let N := Nat.card (FinCl A' K'')
  let eq : FinCl A' K'' ≃ Fin N := Finite.equivFin _
  let y : FinCl A' K'' → Bridge.Gf A' := fun c => e (Quotient.out c)
  let zc : FinCl A' K'' → GA D A' := fun c => ((Quotient.out c : GfC A') : GA D A')
  have hz : ∀ c, (finHom A').rangeRestrict (zc c) = y c := fun c => rfl
  have hu0 : ∀ x : GA D A', ∃! c, ∃ γ ∈ GQ A', ∃ k ∈ J, x = γ * zc c * k :=
    existsUnique_doubleCoset (finHom A').rangeRestrict (GQ A') (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin A' K'') y hy zc hz
  let z : Fin N → GA D A' := fun l => zc (eq.symm l)
  have hu : ∀ x : GA D A', ∃! l, ∃ γ ∈ GQ A', ∃ k ∈ J, x = γ * z l * k := fun x =>
    (eq.existsUnique_congr_left (p := fun c => ∃ γ ∈ GQ A', ∃ k ∈ J, x = γ * zc c * k)).1 (hu0 x)
  have hfinΓ : ∀ l, {γ : GQ A' | (z l)⁻¹ * (γ : GA D A') * z l ∈ J}.Finite := fun l =>
    GlobalTheory.InnerClassSum.finite_stab_of_measure μ (GQ A') J hfd hJ0 hJtop (z l)
  have him : ∀ l, {γ : GA D A' | γ ∈ GQ A' ∧ (z l)⁻¹ * γ * z l ∈ J} =
      Subtype.val '' {γ : GQ A' | (z l)⁻¹ * (γ : GA D A') * z l ∈ J} := by
    intro l
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
  have hfin : ∀ l, {γ : GA D A' | γ ∈ GQ A' ∧ (z l)⁻¹ * γ * z l ∈ J}.Finite := fun l =>
    him l ▸ (hfinΓ l).image _
  have hdec : ∀ k ∈ J, ∃ k' ∈ Lev.levA A' K'', ∃ w : GinfC A', k = k' * (GinfC A').subtype w := fun k hk =>
    ⟨finPart A' k, finPart_mem_levA A' hk, ⟨realPart A' k, realPart_mem A' k⟩, (finPart_mul_realPart A' k).symm⟩
  have hcomm : ∀ k ∈ Lev.levA A' K'', ∀ w : GinfC A', k * (GinfC A').subtype w = (GinfC A').subtype w * k :=
    fun k hk w => (Formalism.IndefR.Eqv.Act.comm_inf_fin w.2 (Subgroup.mem_inf.1 hk).1).symm
  have hrt : ∀ w : GinfC A', MeasurePreserving (· * (GinfC A').subtype w) μ μ := fun w =>
    measurePreserving_mul_right_of_mem μ J hJo hJ0 hJtop (hinfJ w.2)
  refine ⟨(μ J).toReal, N, z, fun l => {γ : GA D A' | γ ∈ GQ A' ∧ (z l)⁻¹ * γ * z l ∈ J}.ncard, κ,
    ENNReal.toReal_pos hJ0 hJtop, fun l => (Quotient.out (eq.symm l)).2, fun l => ?_, inferInstance, inferInstance,
    fun t P h _ => ?_⟩
  · exact (Set.ncard_pos (hfin l)).2 ⟨1, (GQ A').one_mem, by simp [J.one_mem]⟩
  · have hcont : Continuous (X.ker' W.ψ W.θ t P h) :=
      continuous_of_level A' K'' hK''.1 _ (fun k hk g => hr t P h k hk g) (ker'_cont hX t P h)
    obtain ⟨-, heq⟩ := integral_eq_sum_avg (GA D A') μ (GQ A') J (Lev.levA A' K'') X.fd' hfd hJo hJtop (GinfC A') κ
      (GinfC A').subtype continuous_subtype_val hrt hdec hcomm (Fin N) z hu hfin (X.ker' W.ψ W.θ t P h) hcont
      (ker'_left hX t P h) (fun k hk g => hr t P h k hk g)
    exact heq
end GlobalTheory.RowTest.BottomClassSum
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.twist_integral_eq_bottom_classSum : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (v : ℝ) (N : ℕ) (z : Fin N → GA D A') (w : Fin N → ℕ) (κ : Measure (GinfC A')), 0 < v ∧ (∀ l, z l ∈ GfC A') ∧
      (∀ l, 0 < w l) ∧ κ.IsMulLeftInvariant ∧ IsProbabilityMeasure κ ∧
      ∀ (t : T) (P : PolF D WW.rank A'.rank), ∀ h ∈ GfC WW,
        X.I' W.ψ W.θ t P h = (v : ℂ) * ∑ l, ((w l : ℂ))⁻¹ * ∫ g, X.ker' W.ψ W.θ t P h (z l * (g : GA D A')) ∂κ := by
  first | exact @_root_.GlobalTheory.RowTest.BottomClassSum.integral_eq_bottom_classSum | exact _root_.GlobalTheory.RowTest.BottomClassSum.integral_eq_bottom_classSum | (intros; apply _root_.GlobalTheory.RowTest.BottomClassSum.integral_eq_bottom_classSum <;> assumption)
end
end
