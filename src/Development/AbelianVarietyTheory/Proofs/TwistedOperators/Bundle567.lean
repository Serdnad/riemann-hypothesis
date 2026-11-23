module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceTuplesOneOrbitModUniformizerPower
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle404
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTranslateOrthogonalOfSupportMovedOff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle557
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle560
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarHeckeTraceThetaGeneratorFamily
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle561
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitaryEmbeddingLattice

variable {D : D7} {Y V : HSp D}

local notation "inc" => (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))

def phiRow (d : HermitianOrthogonalExtensionData Y V 1 1) : Matrix (Fin 1) (Fin V.rank) D.host.E :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.a * V.gram

theorem cT_zero {m p : ℕ} : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (0 : Matrix (Fin m) (Fin p) D.host.E) = 0 := by
  ext i j; simp [Formalism.UG.cT]

theorem qM_mul_a (d : HermitianOrthogonalExtensionData Y V 1 1) : GlobalTheory.UnitaryEmbeddingProperties.qM d * d.a = 0 := by
  rw [GlobalTheory.UnitaryEmbeddingProperties.qM, Matrix.mul_assoc, d.perp, Matrix.mul_zero]

theorem phiRow_mul_P (d : HermitianOrthogonalExtensionData Y V 1 1) : phiRow d * frameMat V Y d.ι = 0 := by
  have h := congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) d.perp
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, GlobalTheory.AutFunCounterexample.gram_herm, GlobalTheory.AutFunCounterexample.cT_cT, cT_zero] at h
  rw [phiRow, Matrix.mul_assoc, h]

theorem phiRow_mul_a (d : HermitianOrthogonalExtensionData Y V 1 1) : phiRow d * d.a = 1 := by
  rw [phiRow, d.gram]
  ext i j
  fin_cases i; fin_cases j
  simp [antiDiagonalSignGramMatrix]

theorem P_Q_add (d : HermitianOrthogonalExtensionData Y V 1 1) : frameMat V Y d.ι * GlobalTheory.UnitaryEmbeddingProperties.qM d + d.a * phiRow d = 1 := by
  have h : Matrix.fromRows (GlobalTheory.UnitaryEmbeddingProperties.qM d) (phiRow d) * Matrix.fromCols (frameMat V Y d.ι) d.a = 1 := by
    rw [Matrix.fromRows_mul_fromCols, GlobalTheory.UnitaryEmbeddingProperties.qM_mul, qM_mul_a, phiRow_mul_P, phiRow_mul_a, Matrix.fromBlocks_one]
  have h2 := (Matrix.mul_eq_one_comm_of_equiv (finSumFinEquiv.trans (finCongr d.rank))).1 h
  rwa [Matrix.fromCols_mul_fromRows] at h2

theorem decomp (d : HermitianOrthogonalExtensionData Y V 1 1) (v : Fin V.rank → D.host.E) :
    v = frameMat V Y d.ι *ᵥ (GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ v) + (phiRow d *ᵥ v) 0 • zv d := by
  conv_lhs => rw [← Matrix.one_mulVec v, ← P_Q_add d]
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  congr 1
  funext i
  simp [Matrix.mulVec, dotProduct, zv, mul_comm]

theorem finiteAdele_unitaryEmbedding (d : HermitianOrthogonalExtensionData Y V 1 1) (h : GA D Y) :
    (Lev.finE V (stabilizerEmbedding d h)).1 = GlobalTheory.UnitaryEmbeddingProperties.ex ((frameMat V Y d.ι).map inc) ((GlobalTheory.UnitaryEmbeddingProperties.qM d).map inc)
      (Lev.finE Y h).1 := by
  rw [GlobalTheory.LevSplit.finE_val, GlobalTheory.LevSplit.finE_val]
  unfold Formalism.L2.Theta.mt
  rw [GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_matrix_formula, GlobalTheory.UnitaryEmbeddingProperties.ex_map, Matrix.map_map, Matrix.map_map]
  rfl

theorem summandEmbedding_inv (d : HermitianOrthogonalExtensionData Y V 1 1) (h : GA D Y) : stabilizerEmbedding d h⁻¹ = (stabilizerEmbedding d h)⁻¹ :=
  map_inv (MonoidHom.mk' (stabilizerEmbedding d) (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d)) h

theorem Q_ex {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)
    (hQP : Q * P = 1) (h : Matrix (Fin r) (Fin r) R) : Q * GlobalTheory.UnitaryEmbeddingProperties.ex P Q h = h * Q := by
  simp only [GlobalTheory.UnitaryEmbeddingProperties.ex, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hQP, Matrix.one_mul,
    Matrix.sub_mul]
  abel

theorem row_ex {R : Type} [CommRing R] {n r k : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)
    (φ : Matrix (Fin k) (Fin n) R) (hφ : φ * P = 0) (h : Matrix (Fin r) (Fin r) R) :
    φ * GlobalTheory.UnitaryEmbeddingProperties.ex P Q h = φ := by
  simp only [GlobalTheory.UnitaryEmbeddingProperties.ex, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hφ, Matrix.zero_mul, add_zero]


theorem incl_vec_mem {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {v : Fin n → D.host.E} (hv : v ∈ L) :
    (fun i => inc (v i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L :=
  Submodule.subset_span ⟨v, hv, rfl⟩




theorem mulVec_mem_of {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (S : Submodule (Formalism.L2.Herm.intAf D.host.F D.host.E) (Fin m → Lev.EAf D))
    (hM : ∀ v ∈ L, (fun i => inc ((M *ᵥ v) i)) ∈ S) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) L, M.map inc *ᵥ z ∈ S := by
  let S' : Submodule (Formalism.L2.Herm.intAf D.host.F D.host.E) (Fin n → Lev.EAf D) :=
    { carrier := {z | M.map inc *ᵥ z ∈ S}
      add_mem' := fun {x y} hx hy => by
        show M.map inc *ᵥ (x + y) ∈ S
        rw [Matrix.mulVec_add]
        exact S.add_mem hx hy
      zero_mem' := by
        show M.map inc *ᵥ (0 : Fin n → Lev.EAf D) ∈ S
        rw [Matrix.mulVec_zero]; exact S.zero_mem
      smul_mem' := fun c x hx => by
        show M.map inc *ᵥ (c • x) ∈ S
        rw [Matrix.mulVec_smul]
        exact S.smul_mem c hx }
  have hle : Formalism.L2.Herm.hatL (F := D.host.F) L ≤ S' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    show M.map inc *ᵥ (fun i => inc (v i)) ∈ S
    convert hM v hv using 1
    funext i
    exact (RingHom.map_mulVec inc M v i).symm
  exact fun z hz => hle hz

end GlobalTheory.UnitaryEmbeddingLattice

namespace GlobalTheory.UnitaryEmbeddingLattice

variable {D : D7} {Y V : HSp D}

local notation "inc" => (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))

theorem mulVec_incl {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (v : Fin n → D.host.E) :
    M.map inc *ᵥ (fun i => inc (v i)) = fun i => inc ((M *ᵥ v) i) := by
  funext i
  exact (RingHom.map_mulVec inc M v i).symm

def qLin (d : HermitianOrthogonalExtensionData Y V 1 1) : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin Y.rank → D.host.E) where
  toFun v := GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ v
  map_add' := Matrix.mulVec_add _
  map_smul' r v := Matrix.mulVec_smul _ r v

def phiLin (d : HermitianOrthogonalExtensionData Y V 1 1) : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] D.host.E where
  toFun v := (phiRow d *ᵥ v) 0
  map_add' v w := by rw [Matrix.mulVec_add]; rfl
  map_smul' r v := by rw [Matrix.mulVec_smul]; rfl

theorem lat_mem_Q (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat Y) {v : Fin V.rank → D.host.E} (hv : v ∈ d.lat Λ fun _ => 1) :
    GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ v ∈ Λ ∧ ∃ o : 𝓞 D.host.E, (o : D.host.E) = (phiRow d *ᵥ v) 0 := by
  obtain ⟨y, hy, u, hu, rfl⟩ := hv
  have e1 : GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ (frameMat V Y d.ι *ᵥ y + d.a *ᵥ u) = y := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, GlobalTheory.UnitaryEmbeddingProperties.qM_mul, qM_mul_a,
      Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
  have e2 : phiRow d *ᵥ (frameMat V Y d.ι *ᵥ y + d.a *ᵥ u) = u := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, phiRow_mul_P, phiRow_mul_a,
      Matrix.one_mulVec, Matrix.zero_mulVec, zero_add]
  refine ⟨by rw [e1]; exact hy, ?_⟩
  rw [e2]
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 (hu 0)
  exact ⟨o, ho⟩




theorem gen_props (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat Y) (x : GA D Y) (y : Fin V.rank → D.host.E)
    (hy : (Lev.finE V (stabilizerEmbedding d x)⁻¹).1 *ᵥ (fun i => y i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1)) :
    GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ y ∈ latAt Λ x ∧ (phiRow d *ᵥ y) 0 ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  have hQP := GlobalTheory.UnitaryEmbeddingProperties.qM_mul_map inc d
  have hφP : (phiRow d).map inc * (frameMat V Y d.ι).map inc = 0 := by
    rw [← Matrix.map_mul, phiRow_mul_P, Matrix.map_zero _ (map_zero _)]
  have hy' : GlobalTheory.UnitaryEmbeddingProperties.ex ((frameMat V Y d.ι).map inc) ((GlobalTheory.UnitaryEmbeddingProperties.qM d).map inc) (Lev.finE Y x⁻¹).1 *ᵥ
      (fun i => inc (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1) := by
    rw [← finiteAdele_unitaryEmbedding, summandEmbedding_inv]
    exact hy
  constructor
  · have h1 := mulVec_mem_of (GlobalTheory.UnitaryEmbeddingProperties.qM d) _ (Formalism.L2.Herm.hatL (F := D.host.F) Λ)
      (fun v hv => incl_vec_mem (lat_mem_Q d Λ hv).1) _ hy'
    rw [Matrix.mulVec_mulVec, Q_ex _ _ hQP, ← Matrix.mulVec_mulVec, mulVec_incl] at h1
    exact Submodule.subset_span h1
  · have h2 := mulVec_mem_of (phiRow d) _ (Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Col.stdLat D.host.E 1))
      (fun v hv => by
        rw [GlobalTheory.CongStdLoc.mem_hatL_std_iff]
        intro i
        obtain ⟨o, ho⟩ := (lat_mem_Q d Λ hv).2
        rw [Subsingleton.elim i 0, ← ho]
        exact (GlobalTheory.NormSum.AdLattice.incl_mem_iff _).2 ⟨o, rfl⟩) _ hy'
    rw [Matrix.mulVec_mulVec, row_ex _ _ _ hφP, mulVec_incl] at h2
    obtain ⟨o, ho⟩ := (GlobalTheory.NormSum.AdLattice.incl_mem_iff _).1 ((GlobalTheory.CongStdLoc.mem_hatL_std_iff _).1 h2 0)
    exact Submodule.mem_one.2 ⟨o, ho⟩




theorem mem_smul_lattice_unitaryEmbedding : ∀ (D : D7) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat Y) (x : GA D Y) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin V.rank → D.host.E), w ∈ 𝔪 • latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) → ∃ y ∈ 𝔪 • latAt Λ x, ∃ u : 𝓞 D.host.E, u ∈ 𝔪 ∧ w = frameMat V Y d.ι *ᵥ y + (u : D.host.E) • zv d := by
  intro D Y V d Λ x 𝔪 w hw
  have hQ : latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) ≤ (latAt Λ x).comap (qLin d) :=
    Submodule.span_le.2 fun y hy => (gen_props d Λ x y hy).1
  have hφ : latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) ≤ (1 : Submodule (𝓞 D.host.E) D.host.E).comap (phiLin d) :=
    Submodule.span_le.2 fun y hy => (gen_props d Λ x y hy).2
  have hQm : 𝔪 • latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) ≤ (𝔪 • latAt Λ x).comap (qLin d) :=
    Submodule.smul_le.2 fun r hr n hn => by
      rw [Submodule.mem_comap, map_smul]
      exact Submodule.smul_mem_smul hr (hQ hn)
  have hφm : 𝔪 • latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) ≤
      (Submodule.map (Algebra.linearMap (𝓞 D.host.E) D.host.E) 𝔪).comap (phiLin d) :=
    Submodule.smul_le.2 fun r hr n hn => by
      rw [Submodule.mem_comap, map_smul]
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hφ hn)
      rw [← ho]
      exact ⟨r * o, Ideal.mul_mem_right o 𝔪 hr, by simp [Algebra.smul_def]⟩
  obtain ⟨u, hu, hu'⟩ := hφm hw
  refine ⟨GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ w, hQm hw, u, hu, ?_⟩
  have e : (u : D.host.E) = (phiRow d *ᵥ w) 0 := hu'
  rw [e]
  exact decomp d w

end GlobalTheory.UnitaryEmbeddingLattice
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

theorem _root_.GlobalTheory.T.splitPlace_tuples_one_orbit_mod_uniformizer_power : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (W : HSp D) (ρ : ℕ) (β : GlobalTheory.FinPl.Frame p W (Fin W.rank)) (x : Mx D W.rank (ρ + 1))
  (ι ι' : Fin (ρ + 1) → Fin W.rank) (s t : Fin (ρ + 1) → k) (e : ℕ), 0 < e → Function.Injective ι → Function.Injective ι' →
  (∀ a b, ι' b = ι a → a = Fin.last ρ ∧ b = Fin.last ρ) →
  (∀ q, s q • (β.b' *ᵥ fun i => p.pr (x i q)) = Pi.single (ι q) 1) →
  (∀ q, t q • ((fun i => p.pr (cA D (x i q))) ᵥ* (W.gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (ι' q) 1) →
  ∀ g ∈ grpAt W (· = p.v), ∀ (u : UX D (ρ + 1)) (a : Mx D W.rank (ρ + 1)),
  (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ e, (z : k) = s q * (β.b' *ᵥ fun j => p.pr (a j q)) i) →
  (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ e,
    (z : k) = t q * ((fun j => p.pr (cA D (a j q))) ᵥ* (W.gram.map (fun c => p.pr (incA D c)) * β.b)) i) →
  MxOff (· = p.v) (mt W g⁻¹ ⬝ (x ⬝ u.1.1) - x - a) →
  ∃ k₀ : GL (Fin W.rank) 𝒪[k], (∀ i j, (k₀.1 - 1) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ e) ∧
    MxOff (· = p.v) (mt W (β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)) ⬝ x - mt W g⁻¹ ⬝ (x ⬝ u.1.1)) := by
  first | exact @GlobalTheory.AscFin.OneOrbitAt.one_orbit | exact GlobalTheory.AscFin.OneOrbitAt.one_orbit | (intros; apply GlobalTheory.AscFin.OneOrbitAt.one_orbit <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepRows

namespace WeakSepPf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)


variable (G) in
theorem nonempty_coreVol : Nonempty (CoreVol G) := ⟨fun i => (GlobalTheory.Unf.Inhab.nonempty_vol (G.V (.core i))).some⟩

theorem rapidDec_of_rapidRow {M : Vol G} {u : GA D (Yc D 0) → ℂ} (h : RapidRow W M u) : RapidDec (Yc D 0) u :=
  h (fun _ => 0) (fun _ => default) 0 (Nat.zero_le _)

theorem rapidDec_of_reach {v : CoreVol G} {F : Fn G (.core 0)} (h : F ∈ Reach W v) : RapidDec (G.V (.core 0)) F := by
  obtain ⟨Ψ, hΨ, rfl, -⟩ := h
  exact hΨ.1 0 (Nat.zero_le _)

theorem integrableOn_corePeriod_rapidlyDecreasing {M : Vol G} (hM : M.IsRow) {F : Fn G (.core 0)}
    (hF : RapidDec (G.V (.core 0)) F) {u : GA D (Yc D 0) → ℂ} (hu : RapidDec (Yc D 0) u) :
    IntegrableOn (fun h => F (stabilizerEmbedding G.sp.dec0 h) * u h) (M.fd (.grid 0 0)) (M.ν (.grid 0 0)) := by
  obtain ⟨h1, h2⟩ := (hM.row 0 (Nat.zero_le _)).haar_fund
  obtain ⟨C, hC⟩ := hF.2.2 0
  exact RapidDec.integrableOn_mul_of_le (V := Yc D 0) (f := fun h => F (stabilizerEmbedding G.sp.dec0 h)) hu h1 h2
    ((hF.2.1.comp (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding G.sp.dec0)).aestronglyMeasurable) (C := C) (A := 0)
    fun g => by simpa using hC _

theorem exists_reach_of_span {M : Vol G} (hM : M.IsRow) {v : CoreVol G}
    {u : GA D (Yc D 0) → ℂ} (hu : RapidDec (Yc D 0) u) {F : Fn G (.core 0)} (hF : F ∈ Submodule.span ℂ (Reach W v))
    (h0 : per0 G M F u ≠ 0) : ∃ F' ∈ Reach W v, per0 G M F' u ≠ 0 := by
  by_contra hn
  push_neg at hn
  have key : IntegrableOn (fun h => F (stabilizerEmbedding G.sp.dec0 h) * u h) (M.fd (.grid 0 0)) (M.ν (.grid 0 0)) ∧
      per0 G M F u = 0 := by
    clear h0
    induction hF using Submodule.span_induction with
    | mem x hx => exact ⟨integrableOn_corePeriod_rapidlyDecreasing hM (rapidDec_of_reach W hx) hu, hn x hx⟩
    | zero => exact ⟨by simp only [Pi.zero_apply, zero_mul]; exact integrableOn_zero, by simp [per0]⟩
    | add x y _ _ hx hy =>
      have e : (fun h => (x + y) (stabilizerEmbedding G.sp.dec0 h) * u h) =
          fun h => x (stabilizerEmbedding G.sp.dec0 h) * u h + y (stabilizerEmbedding G.sp.dec0 h) * u h := by
        funext h; simp [add_mul]
      refine ⟨e ▸ hx.1.add hy.1, ?_⟩
      have a := hx.2
      have b := hy.2
      unfold per0 at a b ⊢
      erw [e, integral_add hx.1 hy.1, a, b, add_zero]
    | smul c x _ hx =>
      have e : (fun h => (c • x) (stabilizerEmbedding G.sp.dec0 h) * u h) = fun h => c * (x (stabilizerEmbedding G.sp.dec0 h) * u h) := by
        funext h; simp [mul_assoc]
      refine ⟨e ▸ hx.1.const_mul c, ?_⟩
      have a := hx.2
      unfold per0 at a ⊢
      erw [e, integral_const_mul, a, mul_zero]
  exact h0 key.2

end WeakSepPf

theorem weakSep_of_steps : SizeGap → CoreModels → RowRapid → PeriodNe → CoreOnto → Ascent → WeakSep := by
  intro hs h1 h2 h3 h4 h5 ε CF hCF
  obtain ⟨x, hx⟩ := h3 ε CF hCF
  obtain ⟨x', hx'⟩ := hs ε
  refine ⟨max x x', fun D large₂ e a b T L μ0 hL G W M hM M₀ hc0 t ht t0 w w0 => ?_⟩
  have q := offQ_of_sizeRows b
  have s := hx' D large₂ e (le_trans (le_max_right _ _) a) b
  obtain ⟨MP, hMP⟩ := h1 D q T L μ0 hL _ G W M hM 0 (Nat.zero_le _)
  obtain ⟨y, hy, v, hv, hp⟩ := hx D large₂ e (le_trans (le_max_left _ _) a) b T L μ0 hL G W M hM M₀ MP t ht t0 w w0
  obtain ⟨vol⟩ := WeakSepPf.nonempty_coreVol G
  have hr := (h2 D q s T L μ0 hL _ rfl G W M hM M₀ hc0 t ht w).1
  obtain ⟨F, ⟨Ψ, hΨ, rfl, c, hcol, ξ, hξ⟩, hF⟩ := WeakSepPf.exists_reach_of_span W hM (WeakSepPf.rapidDec_of_rapidRow W hr)
    (h4 D q s T L μ0 hL _ rfl G W M hM vol MP hMP y hy v hv) hp
  obtain ⟨ρ, Φ, hB⟩ := h5 D q T L μ0 hL _ G W M hM vol Ψ hΨ _ hr hF
  exact ⟨ρ, ξ, c, hcol, Φ, by rw [fPsiPhi, ← hξ]; exact hB⟩

end GlobalTheory.SepRows

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaTranslate_orthogonal_of_support_moved_off : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ (f₀ Φ f : WO S T → ℂ), IsSBHalf (cA D e) (latO S T ΛS ΛT fun _ => True) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀ Φ f → IsThetaFunO ψ S T f → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ g ∈ GfC T, (∀ x, Φ x ≠ 0 → Φ (actO S T 1 g x) = 0) → l2 μ 𝓕 (om (1, g) f) f = 0 := by
  first | exact @GlobalTheory.ThetaOrth.orth | exact GlobalTheory.ThetaOrth.orth | (intros; apply GlobalTheory.ThetaOrth.orth <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tameHecke_integralUnits_eq_residueCharProduct : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (e : AE D) (P : Finset (Pl D.host.E)) (cR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), ChrEq c χ → (∀ PP, χ.TameAt PP) → IsIdemSum e P → (∀ PP, PP ∉ P → (¬ ∃ PP' ∈ P, Lev.IsConjPl PP' PP) → χ.UnrAt PP) → (∀ PP ∈ P, IsRes χ PP (cR PP)) → TameOn c e P cR := by
  first | exact @GlobalTheory.TameProd.tameOn_of_tame | exact GlobalTheory.TameProd.tameOn_of_tame | (intros; apply GlobalTheory.TameProd.tameOn_of_tame <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResNormFourier

theorem resNorm_fourier : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * C' = 0 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), IsCovolOne (ratL W V) μ₀ 𝓕₀ → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), IsCovolOne (ratL W V') μ' 𝓕' → ∀ f, IsThetaFunO ψ V W f → ∀ y : Mx D W.rank r, ∫ w in 𝓕₀, heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) f w * starRingEnd ℂ (f w) ∂μ₀ = ∫ u, ψ (symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) + symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y)) * GlobalTheory.LeviNorm.resNorm ψ V V' W C C' B μ 𝓨 μ' 𝓕' f u ∂μ := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hY μ₀ 𝓕₀ h0 μ' 𝓕' h' f hf y
  have L := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W
  have hR := GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hψ μ 𝓨 hY
  obtain ⟨-, -, hP⟩ := GlobalTheory.T.mixedModel_parseval_thetaInnerProduct D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hY μ₀ 𝓕₀ h0 μ' 𝓕' h' _ f
    (L.1 _ f hf) hf
  rw [hP]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hsm : ∀ (c : ℂ) (g : WO V W → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (c • g) =
      c • GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 g := by
    intro c g; funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res, Pi.smul_apply, smul_eq_mul, integral_const_mul]
  have key : ∀ a b : WO V W, heisO ψ V W a (heisO ψ V W b f) =
      ψ (symplOH V W a b + symplOH V W a b) • heisO ψ V W b (heisO ψ V W a f) := by
    intro a b
    rw [L.2.1 a b f, L.2.1 b a f, smul_smul, add_comm b a, GlobalTheory.MixModel.symplOH_skew V W b a,
      ← AddChar.map_add_eq_mul]
    congr 2
    abel
  simp only
  rw [key, hsm, (hR.1 _ (L.1 _ f hf)).2.2.2 y]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul]
  rfl

end GlobalTheory.ResNormFourier
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heckeChar_trivial_on_idempotentIntegralUnits : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (P : Finset (Pl D.host.E)) (e : AE D), ChrEq c χ → IsIdemSum e P → (∀ PP', PP' ∉ P → (∀ PP ∈ P, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → χ.UnrAt PP') → UnrOff (e + cA D e) c := by
  first | exact @GlobalTheory.ChrOff.unrOff_of_unrAt | exact GlobalTheory.ChrOff.unrOff_of_unrAt | (intros; apply GlobalTheory.ChrOff.unrOff_of_unrAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem _root_.GlobalTheory.T.exists_scalar_heckeTrace_thetaGenerator_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i n : ℕ) (T : Type) [CommRing T] [IsReduced T] [Algebra c.F T] (y : FrPt Xo c T) (x' : Sp T ⟶ Xo.X) (Ψ : Gx y.x ⟶ Gx x') (σ : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)) (s₀ : LB.Sec (PPx x')), admitted l P p → IsHeckeFam P p i Ψ → IsListed Ψ σ → SecGen x' s₀ → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω) (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁'), FrMap χ y y₁ → IsFib χ.toRingHom Ψ Ψ₁ → ∃ s', IsThGen x₁' s' ∧ IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ₁ p y₁.s s') → ∃ a : T, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω) (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁') (s' : LB.Sec (PPx x₁')), FrMap χ y y₁ → IsFib χ.toRingHom Ψ Ψ₁ → IsThGen x₁' s' → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ₁ p y₁.s s' → SecBC χ.toRingHom a x' x₁' s₀ s' := by
  first | exact @GlobalTheory.HeckeScal.exists_scal_of_family | exact GlobalTheory.HeckeScal.exists_scal_of_family | (intros; apply GlobalTheory.HeckeScal.exists_scal_of_family <;> assumption)
end

section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

theorem _root_.GlobalTheory.T.heckeIsogeny_generatorRatio_pointwise_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → ∃ (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (Fd Fd' : Set (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (u u' : (Fin g → ℂ) → ℝ) (v : Fin (Ideal.absNorm P ^ i) → (Fin g → ℂ)), Countable Λ ∧ Countable Λ' ∧ MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume ∧ MeasureTheory.IsAddFundamentalDomain Λ' Fd' MeasureTheory.volume ∧ (∀ a ∈ Λ, h a ∈ Λ') ∧ (∀ z, 0 ≤ u z) ∧ (∀ z, 0 ≤ u' z) ∧ (∀ a ∈ Λ, ∀ z, u (z + a) = u z) ∧ (∀ a ∈ Λ', ∀ z, u' (z + a) = u' z) ∧ (∫ z in Fd, u z ^ 2) / (MeasureTheory.volume Fd).toReal = 1 ∧ (∫ z in Fd', u' z ^ 2) / (MeasureTheory.volume Fd').toReal = 1 ∧ ∀ w, cabs (t none : CAt σ) * u' (h w) ≤ ∑ m, u ((p : ℂ) • w + v m) := by
  first | exact @GlobalTheory.HeckeGenBound.exists_pointwise_bound | exact GlobalTheory.HeckeGenBound.exists_pointwise_bound | (intros; apply GlobalTheory.HeckeGenBound.exists_pointwise_bound <;> assumption)
end
