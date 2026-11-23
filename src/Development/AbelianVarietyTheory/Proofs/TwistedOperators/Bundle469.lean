module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle154
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle041
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle148
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def PeriodsOnLine (ch : Choice R) : Prop :=
  ∃ ell : PolCol ch.G × PolRow ch.G → ℂ, ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
    IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y,
      ∃ κ : ℂ, ∀ P, defPer t ch.S.toGridChoice M P d (colFn ch a) (formTop ch t y) = κ * ell P

def RealLine (ch : Choice R) : Prop :=
  ∃ ell : PolCol ch.G × PolRow ch.G → ℂ, ell ≠ 0 ∧
    (∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G, IsTermVol t ch.S.toGridChoice (ch.Phi a) β M →
      ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ y, ∃ K : ℂ, ∀ σ : PolCol ch.G × PolRow ch.G →₀ ℂ,
        defTot t ch.S.toGridChoice M σ τ (colFn ch a) (formTop ch t y) = (σ.sum fun P c => c * ell P) * K) ∧
    ∀ z : ℂ, ∃ σ : PolCol ch.G × PolRow ch.G →₀ ℂ, (z = 0 → σ = 0) ∧ (σ.sum fun P c => c * ell P) = z

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem sum_sum_line {P D' : Type} (σ : P →₀ ℂ) (τ : D' →₀ ℂ) (f : P → D' → ℂ) (ell : P → ℂ)
    (κ : D' → ℂ) (h : ∀ d ∈ τ.support, ∀ p, f p d = κ d * ell p) :
    (σ.sum fun p c => τ.sum fun d c' => c * c' * f p d) =
      (σ.sum fun p c => c * ell p) * τ.sum fun d c' => c' * κ d := by
  rw [Finsupp.sum_mul]
  refine Finsupp.sum_congr fun p _ => ?_
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun d hd => ?_
  rw [h d hd p]
  ring

theorem realLine_of_periodsOnLine (ch : Choice R) (h : PeriodsOnLine ch) : RealLine ch := by
  obtain ⟨ell₀, h₀⟩ := h
  classical
  let ell : PolCol ch.G × PolRow ch.G → ℂ := if ell₀ = 0 then fun _ => 1 else ell₀
  have hne : ell ≠ 0 := by
    by_cases e : ell₀ = 0
    · simp only [ell, e, if_true]
      intro h1
      have := congrFun h1 (Classical.arbitrary _)
      simp at this
    · simpa [ell, e] using e
  have hline : ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
      IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y,
        ∃ κ : ℂ, ∀ P, defPer t ch.S.toGridChoice M P d (colFn ch a) (formTop ch t y) = κ * ell P := by
    intro t a hS β hβ M hM τ hτ d hd y
    obtain ⟨κ, hκ⟩ := h₀ t a hS β hβ M hM τ hτ d hd y
    by_cases e : ell₀ = 0
    · refine ⟨0, fun P => ?_⟩
      rw [hκ P, e]
      simp
    · exact ⟨κ, fun P => by simp only [ell, e, if_false]; exact hκ P⟩
  refine ⟨ell, hne, fun t a hS β hβ M hM τ hτ y => ?_, fun z => ?_⟩
  · choose κ hκ using hline t a hS β hβ M hM τ hτ
    let κ' : PureDat ch.G t → ℂ := fun d => if hd : d ∈ τ.support then κ d hd y else 0
    refine ⟨τ.sum fun d c' => c' * κ' d, fun σ => ?_⟩
    refine sum_sum_line σ τ _ ell κ' fun d hd P => ?_
    simp only [κ', dif_pos hd]
    exact hκ d hd y P
  · obtain ⟨P₀, hP₀⟩ := Function.ne_iff.1 hne
    refine ⟨Finsupp.single P₀ (z / ell P₀), fun hz => by simp [hz], ?_⟩
    rw [Finsupp.sum_single_index (zero_mul _)]
    exact div_mul_cancel₀ z hP₀

theorem big_mono {Q Q' : ChP} (h : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), Q ch → Q' ch) (hQ : Big Q) : Big Q' := by
  obtain ⟨CF0, hC⟩ := hQ
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hC ε CF hCF
  exact ⟨x₀, fun D large₂ he hx' Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => h ch (hx D large₂ he hx' Γ Pl0 T A Ks R F hS ch hch hsc)⟩

end GlobalTheory.RowReal
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

noncomputable section
namespace GlobalTheory.MovedDict
variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}

def srcLat (S : GridChoice W Set.univ) : ∀ p : GlobalTheory.ChiGrid.Pair T, FinPt G p.small → FinPt G p.big →
    Submodule (𝓞 D.host.E) (Fin (G.pS p).rank → D.host.E)
  | .chi i j, _, y => GlobalTheory.SumSize.latAt S (.grid (i + 1) j) y
  | .mu _ i j, x, _ => GlobalTheory.SumSize.latAt S (.grid i j) x
  | .core i, _, y => GlobalTheory.SumSize.latAt S (.core (i + 1)) y
  | .top _ j, x, _ => GlobalTheory.SumSize.latAt S (.top j) x

def tgtLat (S : GridChoice W Set.univ) : ∀ p : GlobalTheory.ChiGrid.Pair T, FinPt G p.small → FinPt G p.big →
    Submodule (𝓞 D.host.E) (Fin (G.pT p).rank → D.host.E)
  | .chi i j, x, _ => GlobalTheory.SumSize.latAt S (.grid i j) x
  | .mu _ i j, _, y => GlobalTheory.SumSize.latAt S (.grid i (j + 1)) y
  | .core i, x, _ => GlobalTheory.SumSize.latAt S (.core i) x
  | .top _ j, _, y => GlobalTheory.SumSize.latAt S (.top (j + 1)) y

end GlobalTheory.MovedDict
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.SplitParity

theorem exists_eq_of_sigR_fixed {F E R : Type} [Field F] [CharZero F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hr : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x)
    (z : R ⊗[F] E) (hz : sigR R σ z = z) : ∃ r : R, algebraMap R (R ⊗[F] E) r = z := by
  obtain ⟨δ, b, -, hb0, hb1, -⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hr hσ hne
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have h0 : B 0 = 1 := by rw [hB, hb0]; rfl
  have hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := fun r e => rfl
  have hz' := B.sum_repr z
  rw [Fin.sum_univ_two] at hz'
  set x := B.repr z 0
  set y := B.repr z 1
  have e : sigR R σ (x • B 0 + y • B 1) = x • B 0 - y • B 1 := by
    rw [map_add (f := _), hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hs, hs, hb1, hb0,
      map_one, TensorProduct.tmul_neg, sub_eq_add_neg]
  rw [← hz', e] at hz
  have h2 : (2 * y) • B 1 = 0 := by
    have : x • B 0 - y • B 1 - (x • B 0 + y • B 1) = 0 := by rw [hz, sub_self]
    rw [two_mul, add_smul]
    linear_combination (-1 : R ⊗[F] E) * this
  have h3 : 2 * y = 0 := by
    have := congrArg (fun w => B.repr w 1) h2
    simpa using this
  have h4 : y = 0 := by
    have hu : (2 : R) * algebraMap F R (1 / 2) = 1 := by
      rw [← map_ofNat (algebraMap F R) 2, ← map_mul]; norm_num
    calc y = algebraMap F R (1 / 2) * (2 * y) := by linear_combination (-y) * hu
      _ = 0 := by rw [h3, mul_zero]
  refine ⟨x, ?_⟩
  rw [← hz', h4, zero_smul, add_zero, h0, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.SplitParity

namespace GlobalTheory.SplitParity

theorem exists_idF_of_fixed (D : D7) (u : (AE D)ˣ) (hu : cA D (u : AE D) = u) : ∃ y, idF D y = u := by
  have hfx : ∀ z : AE D, cA D z = z → ∃ r : AF D.host.F, algebraMap (AF D.host.F) (AE D) r = z := fun z hz =>
    exists_eq_of_sigR_fixed D.sp.cm.sig D.sp.cm.deg2 (fun x => star_star x)
      (GlobalTheory.VolHeckeCompare.exists_not_fixed D) z hz
  obtain ⟨r, hr⟩ := hfx _ hu
  have hu' : cA D ((u⁻¹ : (AE D)ˣ) : AE D) = ((u⁻¹ : (AE D)ˣ) : AE D) := by
    have h1 : (u : AE D) * cA D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := by
      rw [← hu, ← map_mul, Units.mul_inv, map_one]
    exact (Units.inv_eq_of_mul_eq_one_right h1).symm
  obtain ⟨r', hr'⟩ := hfx _ hu'
  have m1 : r * r' = 1 := GlobalTheory.VolHeckeCompare.algebraMap_AE_injective D (by
    rw [map_mul, hr, hr', Units.mul_inv, map_one])
  refine ⟨⟨r, r', m1, by rw [mul_comm]; exact m1⟩, Units.ext ?_⟩
  exact hr

theorem exists_int_add_half : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ) (τ : D.what₂.Tau) (a : ℚ),
    IsHeckeChar D χ → ResEta D χ n → HasInfExp D χ τ a → ∃ e : ℤ, (e : ℚ) = a + (n : ℚ) / 2 := by
  intro D χ n τ a _ hr ha
  classical
  obtain ⟨N, hN, ⟨θ, hθ⟩, hχ⟩ := ha
  obtain ⟨η, -, -, hη1, hη2⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨N1, hN1, -, hηx⟩ := hη2 τ
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom h
  set w : D.what₂.Tau → ℂ := Pi.mulSingle τ (-1) with hw
  have wτ : w τ = -1 := by simp [w]
  have wo : ∀ τ', τ' ≠ τ → w τ' = 1 := fun τ' ht => by simp [w, Pi.mulSingle_eq_of_ne ht]
  have ww : w * w = 1 := by
    funext τ'
    by_cases ht : τ' = τ
    · subst ht; simp [wτ]
    · simp [wo τ' ht]
  let x : (AE D)ˣ := ⟨e w, e w, by rw [← map_mul, ww, map_one], by rw [← map_mul, ww, map_one]⟩
  have x1 : finPart D (x : AE D) = 1 := e1 w
  have x2 : ∀ τ', θ τ' (infPart D (x : AE D)) = w τ' := e2 w
  have xτ : θ τ (infPart D (x : AE D)) = -1 := by rw [x2, wτ]
  have xo : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1 := fun τ' ht => by rw [x2, wo τ' ht]
  have hcx : ((χ x : Circle) : ℂ) = (-1 : ℂ) ^ N := by rw [hχ θ hθ x x1 xo, xτ]; simp
  have hN1' : N1 = 1 := by
    have : (N1 : ℚ) = 1 := by rw [hN1]; norm_num
    exact_mod_cast this
  have hηc : ((η x : Circle) : ℂ) = -1 := by rw [hηx θ hθ x x1 xo, xτ, hN1']; simp
  have hfix : cA D (x : AE D) = x := by
    refine GlobalTheory.SplitCharExp.ext_of_chart h ?_ fun τ' => ?_
    · have e3 : finPart D (cA D (x : AE D)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) :=
        GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (x : AE D)
      rw [e3, x1, RingHom.map_one]
    · rw [GlobalTheory.FockCompare.comp_cA hθ, x2]
      by_cases ht : τ' = τ
      · rw [ht, wτ]; simp
      · rw [wo τ' ht]; simp
  obtain ⟨y, hy⟩ := exists_idF_of_fixed D x hfix
  obtain ⟨⟨ε, hε⟩, hrχ⟩ := hr
  have c1 := hrχ ε hε y
  have c2 := hη1.2 ε hε y
  rw [hy] at c1 c2
  have c2' : ((ε y : Circle) : ℂ) = -1 := by rw [← hηc, c2, pow_one]
  have c1' : ((χ x : Circle) : ℂ) = (-1 : ℂ) ^ n := by rw [c1, Circle.coe_pow, c2']
  have hE : (-1 : ℂ) ^ N = (-1 : ℂ) ^ (n : ℤ) := by rw [← hcx, c1', zpow_natCast]
  have hP : (-1 : ℂ) ^ (N + (n : ℤ)) = 1 := by
    rw [zpow_add₀ (by norm_num), hE, ← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num
  rcases Int.even_or_odd (N + (n : ℤ)) with ⟨k, hk⟩ | ho
  · refine ⟨k, ?_⟩
    have : ((N + (n : ℤ) : ℤ) : ℚ) = ((k + k : ℤ) : ℚ) := by rw [hk]
    push_cast at this
    linarith
  · rw [ho.neg_one_zpow] at hP
    norm_num at hP

end GlobalTheory.SplitParity
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

namespace GlobalTheory.GramOneCompact

theorem isCompact_GinfC_of_gram_eq_one : ∀ (D : D7) (V : HSp D), V.gram = 1 → IsCompact (GinfC V : Set (GA D V)) := by
  intro D V hg
  have hL : (GlobalTheory.SW.stdL D.host.E V.rank).FG ∧ Submodule.span D.host.E
      (GlobalTheory.SW.stdL D.host.E V.rank : Set (Fin V.rank → D.host.E)) = ⊤ := by
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    apply Submodule.subset_span
    exact ⟨a, by simp⟩
  obtain ⟨C, hC, hCm⟩ := GlobalTheory.Ker.CongTop.exists_compact V _ hL.1 hL.2
  refine hC.of_isClosed_subset (GlobalTheory.Ker.CongTop.isClosed_GinfC V) fun k hk => hCm k ?_ (Or.inr hg)
  have hk1 : finHom V k = 1 := hk
  have h1 : GlobalTheory.Ker.fmt V k = GlobalTheory.Ker.fmt V 1 := by
    rw [GlobalTheory.Ker.CongTop.fmt_eq, GlobalTheory.Ker.CongTop.fmt_eq, hk1, map_one]
  rw [h1]
  exact (GlobalTheory.Ker.CongTop.congSub V (GlobalTheory.SW.stdL D.host.E V.rank) 1).one_mem.1

end GlobalTheory.GramOneCompact
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitCartanGen

open Formalism.UG

section Local

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

def dg : (Fin n → (v.adicCompletion F)ˣ) →* GL (Fin n) (v.adicCompletion F) :=
  (Units.map (Matrix.diagonalRingHom (Fin n) (v.adicCompletion F)).toMonoidHom).comp
    MulEquiv.piUnits.symm.toMonoidHom

theorem dg_val (u : Fin n → (v.adicCompletion F)ˣ) :
    (dg u).1 = Matrix.diagonal fun i => (u i : v.adicCompletion F) := rfl

def heckeL (ϖ : v.adicCompletion F) : Set (GL (Fin n) (v.adicCompletion F)) :=
  {x | ∃ k : ℕ, (∀ i j, x.1 i j ∈ Ov F v) ∧ (∀ i j, ϖ * (x⁻¹).1 i j ∈ Ov F v) ∧
    Valued.v x.1.det = Valued.v ϖ ^ k}

theorem single_mem {ϖ : v.adicCompletion F} (h0 : ϖ ≠ 0) (hϖO : ϖ ∈ Ov F v) (i : Fin n) :
    dg (Pi.mulSingle i (Units.mk0 ϖ h0)) ∈ heckeL (n := n) ϖ := by
  classical
  refine ⟨1, fun a b => ?_, fun a b => ?_, ?_⟩
  · rw [dg_val, Matrix.diagonal_apply]
    split_ifs with hab
    · rw [Pi.mulSingle_apply]
      split_ifs
      · simpa using hϖO
      · simpa using one_mem (Ov F v)
    · exact zero_mem _
  · rw [← map_inv, dg_val, Matrix.diagonal_apply]
    split_ifs with hab
    · rw [Pi.inv_apply, Pi.mulSingle_apply]
      split_ifs
      · simpa [h0] using one_mem (Ov F v)
      · simpa using hϖO
    · rw [mul_zero]; exact zero_mem _
  · rw [dg_val, Matrix.det_diagonal, ← Units.coe_prod, Finset.prod_pi_mulSingle']
    simp

theorem local_closure {ϖ : v.adicCompletion F} (hϖ : IsUnifV F v ϖ) (hϖO : ϖ ∈ Ov F v)
    (g : GL (Fin n) (v.adicCompletion F)) :
    g ∈ Submonoid.closure ((GLint (Fin n) (Ov F v) : Set (GL (Fin n) (v.adicCompletion F))) ∪ heckeL ϖ ∪
      {x | x⁻¹ ∈ heckeL ϖ}) := by
  classical
  have h0 : ϖ ≠ 0 := (GlobalTheory.SplitPlace.unif_facts hϖ).1
  set S := ((GLint (Fin n) (Ov F v) : Set (GL (Fin n) (v.adicCompletion F))) ∪ heckeL ϖ ∪
      {x | x⁻¹ ∈ heckeL ϖ}) with hS
  set M := (Submonoid.closure S).comap (dg (v := v) (n := n)) with hM
  have hz : ∀ i (z : ℤ), Pi.mulSingle i (Units.mk0 ϖ h0 ^ z) ∈ M := by
    intro i z
    have hmz := map_zpow (MonoidHom.mulSingle (fun _ : Fin n => (v.adicCompletion F)ˣ) i) (Units.mk0 ϖ h0) z
    simp only [MonoidHom.mulSingle_apply] at hmz
    rw [hmz]
    have m1 : Pi.mulSingle i (Units.mk0 ϖ h0) ∈ M :=
      Submonoid.subset_closure (Or.inl (Or.inr (single_mem h0 hϖO i)))
    have m2 : (Pi.mulSingle i (Units.mk0 ϖ h0))⁻¹ ∈ M := by
      refine Submonoid.subset_closure (Or.inr ?_)
      change (dg _)⁻¹ ∈ heckeL ϖ
      rw [map_inv, inv_inv]
      exact single_mem h0 hϖO i
    rcases z with m | m
    · rw [Int.ofNat_eq_coe, zpow_natCast]; exact pow_mem m1 m
    · rw [zpow_negSucc, ← inv_pow]; exact pow_mem m2 _
  obtain ⟨a, -, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp F v n ϖ hϖO hϖ g
  have hu : (fun i => Units.mk0 ϖ h0 ^ a i) ∈ M := by
    rw [← Finset.univ_prod_mulSingle (fun i => Units.mk0 ϖ h0 ^ a i)]
    exact Submonoid.prod_mem M fun i _ => hz i (a i)
  have hg : g = k₁ * dg (fun i => Units.mk0 ϖ h0 ^ a i) * k₂ := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, dg_val, e]
    congr 2
    simp [diagPow, Units.val_zpow_eq_zpow_val]
  rw [hg]
  exact mul_mem (mul_mem (Submonoid.subset_closure (Or.inl (Or.inl hk₁))) hu)
    (Submonoid.subset_closure (Or.inl (Or.inl hk₂)))

end Local

end GlobalTheory.SplitCartanGen

namespace GlobalTheory.SplitCartanGen

open Formalism.UG GlobalTheory.SplitPlace

theorem supp_mem_closure : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal →
    ϖ ∉ P.asIdeal ^ 2 → ∀ h ∈ GfC V, Formalism.L2.Theta.SuppAt e V h →
      h ∈ Submonoid.closure ({g | g ∈ KsphC V ∅ ∧ Formalism.L2.Theta.SuppAt e V g} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α⁻¹}) := by
  intro D V P e ϖ he hP hP2 h _ hs
  classical
  obtain ⟨v, π, s, h1, h2, h3, h4, h5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_basis V e v π s he.1.1 h2 h3 h4
    (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2
  obtain ⟨hex, hinj⟩ := comp_bij (V := V) (B := B) he.1 h1 h2
  have hK := fun g => K_iff (g := g) he.1 h2 h3 hB
  have hu := isUnif he h4 h5 ϖ hP hP2
  have hH := hecke_iff he.1 h1 h2 h3 h4 hB (unif_facts hu).1
  have hloc := local_closure hu (unif_facts hu).2 (comp V π B h)
  have s1 : Formalism.L2.Theta.SuppAt e V 1 := by
    rw [suppAt_iff, mt_one, sub_self, smul_zero]
  suffices key : ∀ a ∈ Submonoid.closure ((GLint (Fin V.rank) (Ov D.host.F v) : Set (GL (Fin V.rank) (Fv D.host.F v))) ∪
      heckeL (π (finPart D (incA D (ϖ : D.host.E)))) ∪ {x | x⁻¹ ∈ heckeL (π (finPart D (incA D (ϖ : D.host.E))))}),
      ∀ g, Formalism.L2.Theta.SuppAt e V g → comp V π B g = a → g ∈ Submonoid.closure ({g | g ∈ KsphC V ∅ ∧ Formalism.L2.Theta.SuppAt e V g} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α} ∪
        {α | ∃ k, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α⁻¹}) from key _ hloc h hs rfl
  intro a ha
  induction ha using Submonoid.closure_induction with
  | mem x hx =>
    intro g hg hgx
    apply Submonoid.subset_closure
    rcases hx with (hx | ⟨k, hx⟩) | ⟨k, hx⟩
    · exact Or.inl (Or.inl ⟨(hK g hg).2 (hgx ▸ hx), hg⟩)
    · exact Or.inl (Or.inr ⟨k, (hH k g).2 ⟨hg, hgx ▸ hx⟩⟩)
    · refine Or.inr ⟨k, (hH k g⁻¹).2 ⟨suppAt_inv hg, ?_⟩⟩
      rw [map_inv, hgx]
      exact hx
  | one =>
    intro g hg hg1
    have : g = 1 := hinj _ _ hg s1 (by rw [hg1, map_one])
    rw [this]
    exact one_mem _
  | mul x y _ _ ihx ihy =>
    intro g hg hgxy
    obtain ⟨gx, sx, rfl⟩ := hex x
    obtain ⟨gy, sy, rfl⟩ := hex y
    have : g = gx * gy := hinj _ _ hg (suppAt_mul sx sy) (by rw [hgxy, map_mul])
    rw [this]
    exact mul_mem (ihx gx sx rfl) (ihy gy sy rfl)

end GlobalTheory.SplitCartanGen
end
end
