module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle336
import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEigenpartEqRowsFullHecke
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelVectorGoodTypeStableSubspace
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleTransportSameRanksConstants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace
open Formalism.IndefR.Datum

noncomputable section

namespace GlobalTheory.DblThetaRestrict

open Formalism.IndefR.Datum GlobalTheory.DblBox MeasureTheory

theorem scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
      ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
        Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
        ∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∃ c : ℂ, ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = c • (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) := by
  intro D ψ hψ S T χS χT ω hω ωd hωd h hd hh
  have hθ := GlobalTheory.T.isThetaFun_doubledSpaceBoxProduct D ψ hψ S
  have hH := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  let ι : Type := {p : (WO S T → ℂ) × (WO S T → ℂ) // IsThetaFunO ψ S T p.1 ∧ IsThetaFunO ψ S T p.2}
  let X : ι → WO S (GlobalTheory.Doubling.dblSp T) → ℂ := fun p => ωd (1, hd) (box p.1.1 p.1.2)
  let Y : ι → WO S (GlobalTheory.Doubling.dblSp T) → ℂ := fun p => box (ω (1, h) p.1.1) p.1.2
  let act : WO S (GlobalTheory.Doubling.dblSp T) → ι → ι := fun w p =>
    ⟨(heisO ψ S T (top w) p.1.1, heisO ψ S T (bot w) p.1.2), hH _ _ p.2.1, hH _ _ p.2.2⟩
  let g : WO S (GlobalTheory.Doubling.dblSp T) → WO S (GlobalTheory.Doubling.dblSp T) := actO S (GlobalTheory.Doubling.dblSp T) 1 hd
  have hg : Function.Surjective g := fun y => ⟨actO S (GlobalTheory.Doubling.dblSp T) 1 hd⁻¹ y, by
    simp only [g, actO, inv_one, show Formalism.L2.Theta.mt S 1 = 1 from rfl, Matrix.mul_one, ← Matrix.mul_assoc]
    rw [show Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd * Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd⁻¹ =
      Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) (hd * hd⁻¹) from rfl, mul_inv_cancel,
      show Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) 1 = 1 from rfl, Matrix.one_mul]⟩
  have hbox : ∀ p : ι, IsThetaFunO ψ S (GlobalTheory.Doubling.dblSp T) (box p.1.1 p.1.2) := fun p => hθ T _ _ p.2.1 p.2.2
  have hX : ∀ p, IsThetaFunO ψ S (GlobalTheory.Doubling.dblSp T) (X p) := fun p => hωd.om_pres _ _ (hbox p)
  have hY : ∀ p, IsThetaFunO ψ S (GlobalTheory.Doubling.dblSp T) (Y p) := fun p => hθ T _ _ (hω.om_pres _ _ p.2.1) p.2.2
  have hXa : ∀ w p, X (act w p) = heisO ψ S (GlobalTheory.Doubling.dblSp T) (g w) (X p) := fun w p => by
    show ωd (1, hd) (box (heisO ψ S T (top w) p.1.1) (heisO ψ S T (bot w) p.1.2)) = _
    rw [← heisO_box hψ, hωd.om_heis _ _ _ _ (hbox p)]
  have hYa : ∀ w p, Y (act w p) = heisO ψ S (GlobalTheory.Doubling.dblSp T) (g w) (Y p) := fun w p => by
    show box (ω (1, h) (heisO ψ S T (top w) p.1.1)) (heisO ψ S T (bot w) p.1.2) = _
    rw [hω.om_heis _ _ _ _ p.2.1, heisO_box hψ, top_actO hh, bot_actO hh, actO_one_one]
  obtain ⟨μ, 𝓕, μ₁, 𝓕₁, hμ, h𝓕, hμ₁, h𝓕₁, hprod⟩ := GlobalTheory.T.doubledSpace_boxProduct_inner_factorizes D ψ hψ S T
  have hn : ∀ p q : ι, ∫ x in 𝓕, X p x * star (X q x) ∂μ = ∫ x in 𝓕, Y p x * star (Y q x) ∂μ := fun p q => by
    have e1 := GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S (GlobalTheory.Doubling.dblSp T) μ 𝓕 hμ h𝓕 (ωd (1, hd))
      (hωd.om_pres _) (hωd.om_unit μ 𝓕 hμ h𝓕 _) _ _ (hbox p) (hbox q)
    have e2 := GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ₁ 𝓕₁ hμ₁ h𝓕₁ (ω (1, h))
      (hω.om_pres _) (hω.om_unit μ₁ 𝓕₁ hμ₁ h𝓕₁ _) _ _ p.2.1 q.2.1
    show ∫ x in 𝓕, X p x * star (X q x) ∂μ = ∫ x in 𝓕, box (ω (1, h) p.1.1) p.1.2 x * star (box (ω (1, h) q.1.1) q.1.2 x) ∂μ
    rw [e1, hprod _ _ _ _ p.2.1 q.2.1 p.2.2 q.2.2, hprod _ _ _ _ (hω.om_pres _ _ p.2.1) (hω.om_pres _ _ q.2.1) p.2.2 q.2.2, e2]
  obtain ⟨c, hc⟩ := GlobalTheory.T.thetaFun_families_same_heisenberg_inner_eq_smul D ψ hψ S (GlobalTheory.Doubling.dblSp T) ι X Y act g hg hX hY hXa hYa μ 𝓕 hμ h𝓕 hn
  exact ⟨c, fun f₁ f₂ hf₁ hf₂ => hc ⟨(f₁, f₂), hf₁, hf₂⟩⟩

end GlobalTheory.DblThetaRestrict
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ChiGrid
open GlobalTheory.SqTop (twPl Qn)
open GlobalTheory.Square (IsAwayUnit)
open GlobalTheory.RowTest (LocIn NumbersIn)

namespace GlobalTheory.KappaArith

theorem isAwayUnit_of_pow_eq_one {K : Type} [Field K] (m : ℕ) {z : K} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) :
    IsAwayUnit m z := by
  have hint : IsIntegral ℤ z :=
    ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [hz]⟩
  let a : 𝓞 K := ⟨z, hint⟩
  have ha : (a : K) = z := rfl
  refine ⟨a, 0, 0, ⟨a ^ (n - 1), ?_⟩, by simp [ha]⟩
  rw [pow_zero]
  apply RingOfIntegers.ext
  have e1 : ((a * a ^ (n - 1) : 𝓞 K) : K) = z * z ^ (n - 1) := by rw [← ha]; norm_cast
  rw [e1, ← pow_succ', Nat.sub_add_cancel hn, hz]
  rfl

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc)

def AwayIm (D : D7) (m : ℕ) (z : ℂ) : Prop := ∃ ζ : D.what₂.LL, IsAwayUnit m ζ ∧ D.what₂.embLL ζ = z

theorem awayIm_one (m : ℕ) : AwayIm D m 1 := ⟨1, IsAwayUnit.one m, map_one _⟩

theorem AwayIm.mul {m : ℕ} {z z' : ℂ} (h : AwayIm D m z) (h' : AwayIm D m z') : AwayIm D m (z * z') := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨b, hb, rfl⟩ := h'
  exact ⟨a * b, ha.mul hb, map_mul _ _ _⟩

theorem AwayIm.prod {m : ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, AwayIm D m (f i)) :
    AwayIm D m (∏ i ∈ s, f i) :=
  Finset.prod_induction f (AwayIm D m) (fun _ _ => AwayIm.mul) (awayIm_one m) h

theorem awayIm_val {μ₀ : T} (hL : Lc.Is μ₀) {t : T} (hx : LocIn D.what₂.embLL (Lc.xiH t)) (m : ℕ)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (x : (w.adicCompletion D.host.E)ˣ) :
    AwayIm D m ((Lc.xiH t).loc w x : ℂ) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  obtain ⟨ζ, hζ⟩ := hx w x
  have h1 : ((Lc.xiH t).loc w x) ^ n = 1 := by
    have : ((Lc.xiH t) ^ n).loc w x = 1 := by rw [show (Lc.xiH t) ^ n = 1 from ho]; rfl
    exact this
  have h2 : ζ ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, hζ, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one])
  exact ⟨ζ, isAwayUnit_of_pow_eq_one m hn h2, hζ⟩

end GlobalTheory.KappaArith

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.W_forms_parts_of_distinct_types_orthogonal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ i p q, p ≠ q → ∀ w ∈ R.Wp3 i p, ∀ w' ∈ R.Wp3 i q, ⟪w, w'⟫_ℂ = 0 := by
  first | exact @GlobalTheory.OrthW.inner_wp3_eq_zero_of_ne | exact GlobalTheory.OrthW.inner_wp3_eq_zero_of_ne | (intros; apply GlobalTheory.OrthW.inner_wp3_eq_zero_of_ne <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section
namespace GlobalTheory.BaseVec

theorem coeff_conj_of_central {K : Type} [Field K] {H : Type} [Group H] (z : MonoidAlgebra K H)
    (hz : ∀ b, b * z = z * b) (g h : H) : z.coeff (g * h * g⁻¹) = z.coeff h := by
  have e := congrArg (fun y : MonoidAlgebra K H => y.coeff (g * h)) (hz (MonoidAlgebra.single g 1))
  simpa [mul_assoc] using e.symm

section Levels

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem baseLevelDatum_level_eq (P' : LevelP R.Pg D.R.r ℂ) : (R.dat0 P').P = P' := by
  simp [LevCh.dat0, datY]

theorem mem_levS (P' : LevelP R.Pg D.R.r ℂ) (x : GA D (Yc D 0)) :
    x ∈ levS _ (R.βY 0) (R.dat0 P') ↔ x ∈ GfC (Yc D 0) ∧ finE (Yc D 0) x ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) ∧
      rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) x) ∈ P'.H := by
  show x ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) x ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P') ∧
      rTup (R.βY 0) (R.dat0 P') (finE (Yc D 0) x) ∈ (R.dat0 P').P.H) ↔ _
  rw [baseLevelDatum_level_eq]
  rfl

theorem principalRowLevelCharacter_trivial (P' : LevelP R.Pg D.R.r ℂ) (x : GA D (Yc D 0)) :
    levChi _ (R.βY 0) (R.dat0 P') x = ((ext1 P'.H P'.chi (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) x)) : ℂˣ) : ℂ) := by
  simp [levChi, levFn, LevCh.dat0, datY]
  rfl

theorem conj_mem_principal {x y : GA D (Yc D 0)} (hx : x ∈ levS _ (R.βY 0) (R.dat0 R.triv)) (hy1 : y ∈ GfC (Yc D 0))
    (hy2 : finE (Yc D 0) y ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv)) :
    y⁻¹ * x * y ∈ levS _ (R.βY 0) (R.dat0 R.triv) := by
  rw [mem_levS] at hx ⊢
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hyi := Subgroup.inv_mem _ hy2
  refine ⟨(GfC _).mul_mem ((GfC _).mul_mem ((GfC _).inv_mem hy1) hx1) hy1, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyi hx2) hy2
  · rw [map_mul, map_mul, map_inv, rTup_mul (Subgroup.mul_mem _ hyi hx2) hy2, rTup_mul hyi hx2, rTup_inv hy2]
    have : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) x) = 1 := Subgroup.mem_bot.1 hx3
    rw [this, mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _

theorem lift_div_principal {g0 : G0 R.Pg D.R.r} {κ κ' : GA D (Yc D 0)}
    (hκ : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) (hκ' : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ') :
    κ⁻¹ * κ' ∈ levS _ (R.βY 0) (R.dat0 R.triv) := by
  rw [mem_levS]
  have hi := Subgroup.inv_mem _ hκ.2.1
  refine ⟨(GfC _).mul_mem ((GfC _).inv_mem hκ.1) hκ'.1, ?_, ?_⟩
  · rw [map_mul, map_inv]; exact Subgroup.mul_mem _ hi hκ'.2.1
  · refine Subgroup.mem_bot.2 ?_
    rw [map_mul, map_inv, rTup_mul hi hκ'.2.1, rTup_inv hκ.2.1, hκ.2.2, hκ'.2.2]
    exact inv_mul_cancel g0

end Levels


open Formalism.IndefR.principalLevelFrame in
theorem exists_base_vec : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) (π : Formalism.L2.NG.FinTyp D.host.E n) (v : Formalism.AUTREP.GAf D.host.E n → ℂ), v ∈ π.S → v ≠ 0 → principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv)) (fun _ => 1) v → (∀ κ : G → Formalism.AUTREP.GAf D.host.E n, (∀ g, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ (κ g))) → ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (κ g) v = v) → ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 (R.levR F false))) (fun κ => levChi _ (R.βY 0) (R.dat0 (R.levR F false)) (PY.ψ κ)) x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hC hne n PY π v hvS hv0 hvT hgood
  classical
  have hL := GlobalTheory.DimFull.liftsY' hC
  have hex : ∀ g : G, ∃ κ : Formalism.AUTREP.GAf D.host.E n,
      IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ κ) := by
    intro g
    obtain ⟨κ, hκ⟩ := hL (R.eG g)
    obtain ⟨h, rfl⟩ := PY.onto κ hκ.1
    exact ⟨h, hκ⟩
  choose k hk using hex
  set J0 := PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv) with hJ0
  have hvfix : ∀ c ∈ J0, Formalism.L2.NG.rt D.host.E n c v = v := fun c hc => by
    simpa using hvT c hc
  set Ws : Submodule ℂ (Formalism.AUTREP.GAf D.host.E n → ℂ) :=
    Submodule.span ℂ (Set.range fun g => Formalism.L2.NG.rt D.host.E n (k g) v) with hWs
  have hfix : ∀ w ∈ Ws, ∀ c ∈ J0, Formalism.L2.NG.rt D.host.E n c w = w := by
    intro w hw c hc
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      have hc' : (k g)⁻¹ * c * k g ∈ J0 := by
        rw [hJ0, Set.mem_preimage]
        rw [map_mul, map_mul, map_inv]
        exact GlobalTheory.BaseVec.conj_mem_principal R hc (hk g).1 (hk g).2.1
      rw [rt_rt, show c * k g = k g * ((k g)⁻¹ * c * k g) by group, ← rt_rt, hvfix _ hc']
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul a x _ hx => rw [map_smul, hx]
  have hprod : ∀ g h, ∀ w ∈ Ws, Formalism.L2.NG.rt D.host.E n (k g) (Formalism.L2.NG.rt D.host.E n (k h) w) =
      Formalism.L2.NG.rt D.host.E n (k (g * h)) w := by
    intro g h w hw
    have hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (g * h)) (PY.ψ (k g * k h)) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [map_mul]; exact (GfC _).mul_mem (hk g).1 (hk h).1
      · rw [map_mul, map_mul]; exact Subgroup.mul_mem _ (hk g).2.1 (hk h).2.1
      · rw [map_mul, map_mul, rTup_mul (hk g).2.1 (hk h).2.1, (hk g).2.2, (hk h).2.2]
        exact (map_mul R.eG g h).symm
    have hc : (k (g * h))⁻¹ * (k g * k h) ∈ J0 := by
      rw [hJ0, Set.mem_preimage]
      rw [map_mul, map_inv]
      exact GlobalTheory.BaseVec.lift_div_principal R (hk (g * h)) hl
    rw [rt_rt, show k g * k h = k (g * h) * ((k (g * h))⁻¹ * (k g * k h)) by group, ← rt_rt, hfix w hw _ hc]
  have hk1 : k 1 ∈ J0 := by
    rw [hJ0, Set.mem_preimage, GlobalTheory.BaseVec.mem_levS]
    refine ⟨(hk 1).1, (hk 1).2.1, Subgroup.mem_bot.2 ?_⟩
    rw [(hk 1).2.2]
    exact map_one R.eG
  have hvWs : v ∈ Ws := by
    have : Formalism.L2.NG.rt D.host.E n (k 1) v ∈ Ws := Submodule.subset_span ⟨1, rfl⟩
    rwa [hvfix _ hk1] at this
  have hstab : ∀ g, ∀ w ∈ Ws, Formalism.L2.NG.rt D.host.E n (k g) w ∈ Ws := by
    intro g w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [hprod g h v hvWs]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Ws.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Ws.smul_mem a hx
  let ρ : Representation ℂ G Ws :=
    { toFun := fun g => (Formalism.L2.NG.rt D.host.E n (k g)).restrict (fun w hw => hstab g w hw)
      map_one' := LinearMap.ext fun w => Subtype.ext (hfix w w.2 _ hk1)
      map_mul' := fun g h => LinearMap.ext fun w => Subtype.ext (hprod g h w w.2).symm }
  haveI : FiniteDimensional ℂ Ws := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hX : ∀ χ ∈ A.X, IsAbsIrrChar χ := hOk.irr
  have hcen : ∀ g h : G, RealDat.eC (A := A) D.what₂.embLL (g * h * g⁻¹) = RealDat.eC (A := A) D.what₂.embLL h := fun g h => by
    unfold RealDat.eC
    rw [GlobalTheory.BaseVec.coeff_conj_of_central _ (fun b => idemOf_central A.X hX b) g h]
  have hgoodv : ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (k g) v = v := hgood k hk
  have hgoodW : ∀ w ∈ Ws, ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (k g) w = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      simp only [hprod _ h v hvWs]
      conv_rhs => rw [← hgoodv]

      rw [map_sum]
      simp only [map_smul, hprod h _ v hvWs]
      refine Fintype.sum_equiv (MulAut.conj h⁻¹).toEquiv _ _ fun g => ?_
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
      rw [hcen, show h * (h⁻¹ * g * h⁻¹⁻¹) = g * h by group]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), smul_add, Finset.sum_add_distrib, hx, hy]
    | smul a x _ hx =>
      simp only [map_smul]
      simp only [smul_comm _ a, ← Finset.smul_sum, hx]
  have hbot : (⊤ : Submodule ℂ Ws) ≠ ⊥ := by
    intro h
    have h0 : (⟨v, hvWs⟩ : Ws) ∈ (⊥ : Submodule ℂ Ws) := h ▸ Submodule.mem_top
    exact hv0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h0))
  obtain ⟨u, -, hu0, hu⟩ := GlobalTheory.Hk3.exists_level_vector D.what₂.embLL A.X F.P0 F.ψ0 ρ ⊤ hX hne (fun _ => le_top) hbot
    (fun u _ => Subtype.ext (by
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact hgoodW u u.2))
  refine ⟨(u : Formalism.AUTREP.GAf D.host.E n → ℂ), ?_, fun h => hu0 (Subtype.ext h), ?_⟩
  · exact (Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact π.stable _ _ hvS)) u.2
  · intro κ hκ
    obtain ⟨h1, h2, h3⟩ := (GlobalTheory.BaseVec.mem_levS R _ (PY.ψ κ)).1 hκ
    have hgP : R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ))) ∈ F.P0 := h3
    have hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv)
        (R.eG (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ))))) (PY.ψ κ) :=
      ⟨h1, h2, (MulEquiv.apply_symm_apply R.eG _).symm⟩
    have hc : (k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ)))))⁻¹ * κ ∈ J0 := by
      rw [hJ0, Set.mem_preimage]
      rw [map_mul, map_inv]
      exact GlobalTheory.BaseVec.lift_div_principal R (hk _) hl
    have e1 : Formalism.L2.NG.rt D.host.E n κ (u : _ → ℂ) =
        Formalism.L2.NG.rt D.host.E n (k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ))))) u := by
      conv_lhs => rw [show κ = k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ)))) *
        ((k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ)))))⁻¹ * κ) by group]
      rw [← rt_rt, hfix u u.2 _ hc]
    have e2 := congrArg Subtype.val (hu ⟨_, hgP⟩)
    rw [e1]
    refine e2.trans ?_
    show _ = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F false)) (PY.ψ κ) • _
    rw [GlobalTheory.BaseVec.principalRowLevelCharacter_trivial, Submodule.coe_smul]
    congr 1
    exact ((congrArg (fun u : ℂˣ => (u : ℂ)) (extendOne_of_mem (R.levR F false).chi h3)).trans rfl).symm

end GlobalTheory.BaseVec
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

theorem _root_.GlobalTheory.T.siegel_square_root_weil_pairing_standard : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp K) (c : SiegPre h k ζ s) (p : Sp ℂ ⟶ S) (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ c.A.left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → p ≫ s = spMap σ → SqOf P c p φ → (∀ a, (lev a).left ≫ φ = p ≫ (c.lev a).left) → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ k = 1) → ∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) → Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e) := by
  first | exact @GlobalTheory.SqRootPairing.weilIs_lev_of_sqOf | exact GlobalTheory.SqRootPairing.weilIs_lev_of_sqOf | (intros; apply GlobalTheory.SqRootPairing.weilIs_lev_of_sqOf <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.exists_tameCharacters_seriesIdempotentsTameLabelled : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∃ om, GlobalTheory.DimPartsCompare.TameTie D om := by
  first | exact @GlobalTheory.TameTieOfGood.exists_tameTie_of_given | exact GlobalTheory.TameTieOfGood.exists_tameTie_of_given | (intros; apply GlobalTheory.TameTieOfGood.exists_tameTie_of_given <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.heisenbergDerivative_fockVectors_uniform_operator : ∀ {D : D7} {V W : HSp D} (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) → IsInfFam θ → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ), ∃ Δ : PolF D W.rank V.rank →ₗ[ℂ] PolF D W.rank V.rank, ∀ f, GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ P, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (GlobalTheory.ChainFr.ptF ψ θ A B f P) = GlobalTheory.ChainFr.ptF ψ θ A B f (Δ P) := by
  first | exact @GlobalTheory.FockDerUnif.dRho_ptF_uniform | exact GlobalTheory.FockDerUnif.dRho_ptF_uniform | (intros; apply GlobalTheory.FockDerUnif.dRho_ptF_uniform <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.gridSquareCharQuotient_finiteUnitIdele_rootOfUnity : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ →
    CharsIn G D.what₂.embLL → ∀ (i j : Fin D.R.m) (t : T) (x : (AE D)ˣ), Formalism.L2.Pj.FinUnit x →
    ∃ ζ : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧
      D.what₂.embLL ζ = (((Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) /
        (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) x : Circle) : ℂ) := by
  first | exact @GlobalTheory.SquareCharUnit.nu_finUnit_root | exact GlobalTheory.SquareCharUnit.nu_finUnit_root | (intros; apply GlobalTheory.SquareCharUnit.nu_finUnit_root <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.definiteBottomTriple_transport_same_ranks_constants : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁),
    IsBottomTri W i j X → IsBottomTri W i j Y →
    ∃ X₁ : Tri T B B' WW₁, IsBottomTri W i j X₁ ∧ ∀ c : T → ℂ, X₁.IsConst W.ψ W.θ c → X.IsConst W.ψ W.θ c := by
  first | exact @GlobalTheory.SpaceMove.bottom_transport | exact GlobalTheory.SpaceMove.bottom_transport | (intros; apply GlobalTheory.SpaceMove.bottom_transport <;> assumption)
end

section


theorem _root_.GlobalTheory.T.normalisedFamily_nonzeroThetaVectors_numberField : GlobalTheory.ColNorms.FamilyVectors := by
  first | exact @GlobalTheory.ColNorms.familyVectors | exact GlobalTheory.ColNorms.familyVectors | (intros; apply GlobalTheory.ColNorms.familyVectors <;> assumption)
end
