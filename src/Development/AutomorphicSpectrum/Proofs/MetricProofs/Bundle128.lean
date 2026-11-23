module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatrixChartRatios
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle039
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle044
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle144
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle038
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle065
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle116
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle066
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle044
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle117
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar

section Fields

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {G : Type} [Field G] [CharZero G]


omit [∀ k, Fintype (ι k)] in
theorem prod_div_mem (y : (Σ k, ι k) → G) (u v : ∀ k, ι k) :
    (∏ k, y ⟨k, u k⟩) / (∏ k, y ⟨k, v k⟩) ∈ blockFnField y := by
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨⟨k, u k⟩, ⟨k, v k⟩, rfl, rfl⟩


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem blockFnField_eq_top [Algebra ℤ G] (y : (Σ k, ι k) → G) {κ : Type} (f : κ → G) (c₀ : κ)
    (hsub : ∀ j, f j / f c₀ ∈ blockFnField y)
    (hgen : ∀ a : G, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => f j / f c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => f j / f c₀), h ≠ 0 ∧ a = g / h) :
    blockFnField y = ⊤ := by
  have hle : ∀ g ∈ Algebra.adjoin ℤ (Set.range fun j => f j / f c₀), g ∈ blockFnField y := by
    intro g hg
    induction hg using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hsub j
    | algebraMap r => rw [eq_intCast]; exact intCast_mem (blockFnField y) r
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  rw [eq_top_iff]
  intro a _
  obtain ⟨g, hg, h, hh, -, rfl⟩ := hgen a
  exact div_mem (hle g hg) (hle h hh)

theorem trdeg_top : Algebra.trdeg ℤ (⊤ : IntermediateField ℚ G) = Algebra.trdeg ℤ G := by
  have e : (⊤ : IntermediateField ℚ G) ≃ₐ[ℤ] G := (IntermediateField.topEquiv (F := ℚ) (E := G)).restrictScalars ℤ
  exact e.trdeg_eq

end Fields

section Gen

variable (Ω : Type) [Field Ω] [CharZero Ω] {S : Type} (r : S → ℕ)

theorem trdeg_genField [inst : Algebra ℤ (GenField Ω r)] :
    Algebra.trdeg ℤ (GenField Ω r) = Algebra.trdeg ℤ Ω + Cardinal.mk (GenIx r) := by
  obtain rfl : inst = OreLocalization.instAlgebra := Subsingleton.elim _ _
  haveI : Algebra.IsAlgebraic (MvPolynomial (GenIx r) Ω) (GenField Ω r) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (GenIx r) Ω))
  haveI : FaithfulSMul ℤ Ω := (faithfulSMul_iff_algebraMap_injective ℤ Ω).mpr
    (by simpa using (Int.cast_injective (α := Ω)))
  have h1 := trdeg_add_eq ℤ Ω (A := GenField Ω r)
  have h2 := trdeg_add_eq Ω (MvPolynomial (GenIx r) Ω) (A := GenField Ω r)
  rw [trdeg_eq_zero (R := MvPolynomial (GenIx r) Ω) (A := GenField Ω r), add_zero, MvPolynomial.trdeg_of_isDomain] at h2
  rw [← h1, ← h2, Cardinal.lift_id]

end Gen

section Dim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {G : Type} [Field G] [CharZero G]

theorem isArithVar_of_trdeg [Nonempty K] (y : (Σ k, ι k) → G) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e : ℕ)
    (htr : Algebra.trdeg ℤ (blockFnField y) = e) : IsArithVar (mCoordIdeal y) (e + 1) := by
  refine ⟨‹_›, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal y, relevant y c hc⟩, horizontal y, ?_⟩
  rw [GlobalTheory.CompanionTheory.Ar.Cmp.ringKrullDim_coord y c hc, htr, map_add (f := _), Cardinal.toENat_nat, Cardinal.toENat_nat]
  have h4 : (e : ℕ∞) + (Fintype.card K : ℕ∞) + 1 = ((e + 1 + Fintype.card K : ℕ) : ℕ∞) := by
    push_cast
    ring
  rw [h4]
  rfl

theorem trdeg_of_isArithVar (x : (Σ k, ι k) → G) (d : ℕ) (hx : IsArithVar (mCoordIdeal x) (d + 1)) :
    ∃ c : ∀ k, ι k, (∀ k, x ⟨k, c k⟩ ≠ 0) ∧ Algebra.trdeg ℤ (blockFnField x) = d := by
  obtain ⟨-, ⟨-, -, hrel⟩, -, hdim⟩ := hx
  have hne : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, MvPolynomial.aeval_X, h0, map_zero, zero_mul]
  choose c hc using hne
  refine ⟨c, hc, ?_⟩
  rw [GlobalTheory.CompanionTheory.Ar.Cmp.ringKrullDim_coord x c hc] at hdim
  have h1 : (Algebra.trdeg ℤ (blockFnField x) + (Fintype.card K : Cardinal)).toENat + 1 =
      ((d + 1 + Fintype.card K : ℕ) : ℕ∞) := WithBot.coe_injective hdim
  rw [map_add (f := _), Cardinal.toENat_nat] at h1
  have h3 : (Algebra.trdeg ℤ (blockFnField x)).toENat + ((Fintype.card K + 1 : ℕ) : ℕ∞) =
      (d : ℕ∞) + ((Fintype.card K + 1 : ℕ) : ℕ∞) := by
    push_cast at h1 ⊢
    rw [← add_assoc, h1]
    ring
  have h2 : (Algebra.trdeg ℤ (blockFnField x)).toENat = (d : ℕ∞) :=
    WithTop.add_right_cancel (ENat.coe_ne_top _) h3
  exact Cardinal.toENat_eq_natCast.mp h2

end Dim

section Main

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ}

theorem mk_genIx : Cardinal.mk (GenIx (rk Ψ p q)) = ((Fintype.card Ψ * (p.choose 2 + q.choose 2) : ℕ) : Cardinal) := by
  show Cardinal.mk (Σ s : Ψ ⊕ Ψ, {lk : Fin (rk Ψ p q s) × Fin (rk Ψ p q s) // lk.2 < lk.1}) = _
  rw [Cardinal.mk_fintype, Fintype.card_sigma]
  simp only [FlagTrdeg.card_below_diagonal]
  rw [Fintype.sum_sum_type]
  simp [rk, Nat.choose_two_right]
  ring

variable {Ω : Type} [Field Ω] [CharZero Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {n : Ψ ⊕ Ψ → ℕ} (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (rk Ψ p q s) → E)
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω)

abbrev vals (s : Ψ ⊕ Ψ) : Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω := Matrix.of fun j l => φ s j (c s l)

def chartOf (j : FlagIx ((k : K₀) → J₀ k) n (rk Ψ p q)) : ∀ k, idx (p := p) (q := q) J₀ n k
  | .inl k => j.1 k
  | .inr t => j.2 t

theorem flagCoord_eq_prod (j : FlagIx ((k : K₀) → J₀ k) n (rk Ψ p q)) :
    flagCoord _ (seg x₀) φ c j = ∏ k, yv (vals φ c) x₀ ⟨k, chartOf j k⟩ := by
  rw [Fintype.prod_sum_type]
  simp only [flagCoord, yv, chartOf, seg, map_prod]
  rfl

theorem isArithVar_yv (hB : ∀ s, ∃ B : Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω, B * vals φ c s = 1)
    (hgen : ∀ c₀, seg x₀ c₀ ≠ 0 → ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => seg x₀ j / seg x₀ c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => seg x₀ j / seg x₀ c₀), h ≠ 0 ∧ a = g / h)
    (d : ℕ) (hx : IsArithVar (mCoordIdeal x₀) (d + 1)) :
    IsArithVar (mCoordIdeal (yv (vals φ c) x₀)) (d + Fintype.card Ψ * (p.choose 2 + q.choose 2) + 1) := by
  classical
  obtain ⟨c₀, hc₀, htr⟩ := trdeg_of_isArithVar x₀ d hx
  have hs : seg x₀ c₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc₀ k
  obtain ⟨J, hJ, hfrac⟩ := CoordGen.flagCoord_generate Ω E (Ψ ⊕ Ψ) (rk Ψ p q) n _ (seg x₀) φ c c₀ hs (hgen c₀ hs) hB
  haveI : CharZero (GenField Ω (rk Ψ p q)) :=
    charZero_of_injective_algebraMap (algebraMap Ω (GenField Ω (rk Ψ p q))).injective
  have hy : ∀ k, yv (vals φ c) x₀ ⟨k, chartOf J k⟩ ≠ 0 := by
    rw [flagCoord_eq_prod] at hJ
    exact fun k => Finset.prod_ne_zero_iff.1 hJ k (Finset.mem_univ k)
  have htop := blockFnField_eq_top (yv (vals φ c) x₀) (flagCoord _ (seg x₀) φ c) J
    (fun j => by rw [flagCoord_eq_prod, flagCoord_eq_prod]; exact prod_div_mem _ _ _) hfrac
  have htop0 := blockFnField_eq_top x₀ (seg x₀) c₀ (fun j => prod_div_mem x₀ _ _) (hgen c₀ hs)
  haveI : Nonempty (K₀ ⊕ StepIx Ψ p q) := ⟨.inl hx.1.some⟩
  refine isArithVar_of_trdeg _ (chartOf J) hy _ ?_
  rw [htop, trdeg_top, trdeg_genField, ← trdeg_top (G := Ω), ← htop0, htr, mk_genIx]
  push_cast
  rfl

end Main

theorem isArithVar_flagModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → IsArithVar (mCoordIdeal x₀) (d + 1) → IsArithVar (mCoordIdeal (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2) + 1) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ d hF hx
  exact isArithVar_yv φ (cc 𝔐 bW bO) x₀ hF.2.2.2
    (fun c₀ hc₀ => FracChart.exists_eq_div_adjoin 𝔐.X Ω 𝔐.ξ _ (seg x₀) c₀ 𝔐.tie hc₀) d hx

end GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY
end
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.BlockEmbeddings

theorem det_mul_cols {R : Type} [CommRing R] {N d : ℕ} (M : Matrix (Fin d) (Fin N) R)
    (B : Matrix (Fin N) (Fin N) R) (C : Finset (Fin N)) (hC : C.card = d) :
    (M * B.submatrix id (C.orderEmbOfFin hC)).det =
      ∑ I : Finset (Fin N), (if e : I.card = d then (M.submatrix id (I.orderEmbOfFin e)).det else 0) *
        minorIJ B I C := by
  rw [GroundTheory.PAdicHodge.det_mul_eq_sum_minors]
  have h1 : ∑ I : Finset (Fin N), (if e : I.card = d then (M.submatrix id (I.orderEmbOfFin e)).det else 0) *
        minorIJ B I C =
      ∑ I ∈ Finset.univ.filter (fun I : Finset (Fin N) => I.card = d),
        (if e : I.card = d then (M.submatrix id (I.orderEmbOfFin e)).det else 0) * minorIJ B I C := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun s _ hs => ?_
    have hc : s.card ≠ d := fun hc => hs (by simp [hc])
    rw [dif_neg hc, zero_mul]
  rw [h1, Finset.sum_subtype (Finset.univ.filter fun I : Finset (Fin N) => I.card = d)
    (p := fun s : Finset (Fin N) => s.card = d) (fun s => by simp)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [dif_pos s.2, MinorCalc.minorIJ_eq_det B s.1 C d s.2 hC]
  rfl

variable {Ψ : Type} {p q : ℕ}

theorem blockEquiv_symm_omEmb (a : Fin q) : (blockEquiv p q).symm (omEmb p q a) = Sum.inl a := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp [blockEquiv, omEmb]

theorem blockEquiv_symm_wEmb (a : Fin p) : (blockEquiv p q).symm (wEmb p q a) = Sum.inr a := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp [blockEquiv, wEmb]
  omega

theorem blocks_wEmb {R : Type} [Zero R] (X : Matrix (Fin q) (Fin q) R) (Y : Matrix (Fin p) (Fin p) R) (a b : Fin p) :
    (Matrix.fromBlocks X 0 0 Y).submatrix (blockEquiv p q).symm (blockEquiv p q).symm (wEmb p q a) (wEmb p q b) =
      Y a b := by
  rw [Matrix.submatrix_apply, blockEquiv_symm_wEmb, blockEquiv_symm_wEmb, Matrix.fromBlocks_apply₂₂]

theorem blocks_omEmb {R : Type} [Zero R] (X : Matrix (Fin q) (Fin q) R) (Y : Matrix (Fin p) (Fin p) R) (a b : Fin q) :
    (Matrix.fromBlocks X 0 0 Y).submatrix (blockEquiv p q).symm (blockEquiv p q).symm (omEmb p q a) (omEmb p q b) =
      X a b := by
  rw [Matrix.submatrix_apply, blockEquiv_symm_omEmb, blockEquiv_symm_omEmb, Matrix.fromBlocks_apply₁₁]

theorem gMat_posOf (Ω : Type) [Field Ω] (τ : Ψ) (s : Ψ ⊕ Ψ) (hs : s = .inl τ ∨ s = .inr τ)
    (l l' : Fin (rk Ψ p q s)) :
    gMat p q Ω τ (posOf p q s l) (posOf p q s l') = genU Ω (rk Ψ p q) s l l' := by
  rcases hs with rfl | rfl
  · exact blocks_wEmb _ _ l l'
  · exact blocks_omEmb _ _ l l'

theorem posOf_strictMono (s : Ψ ⊕ Ψ) : StrictMono (posOf p q s) := by
  rcases s with τ | τ
  · exact wEmb_strictMono p q
  · exact omEmb_strictMono p q

theorem sum_aExt_mul {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ} (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    {L : Type} [Field L] (f : Ω →+* L) (s : Ψ ⊕ Ψ) (j : Fin (n s)) (G : Fin (p + q) → L) :
    ∑ a, f (aExt A s j a) * G a = ∑ l, f (A s j l) * G (posOf p q s l) := by

  simp only [aExt, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single (posOf p q s l)]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem stepOf_fst (r : Ψ × Fin (p + q)) :
    (stepOf Ψ p q r).1 = .inl r.1 ∨ (stepOf Ψ p q r).1 = .inr r.1 := by
  unfold stepOf
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem mem_stepCols_iff (r : Ψ × Fin (p + q)) (a : Fin (p + q)) :
    a ∈ stepCols (p + q) p r.2 ↔
      ∃ y : Fin (((stepOf Ψ p q r).2 : ℕ) + 1),
        posOf p q (stepOf Ψ p q r).1 (Fin.castLE (stepOf Ψ p q r).2.2 y) = a := by
  have hr := r.2.2
  by_cases h : (r.2 : ℕ) < p
  · have e : stepOf Ψ p q r = ⟨.inl r.1, ⟨r.2, h⟩⟩ := dif_pos h
    rw [e]
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_pos (by omega)]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨a - q, ?_⟩, Fin.ext ?_⟩
      · show (a : ℕ) - q < (r.2 : ℕ) + 1
        omega
      · show q + ((a : ℕ) - q) = a
        omega
    · rintro ⟨y, rfl⟩
      have hy : (y : ℕ) < (r.2 : ℕ) + 1 := y.2
      show p + q - p ≤ q + (y : ℕ) ∧ q + (y : ℕ) < p + q - p + ((r.2 : ℕ) + 1)
      omega
  · have e : stepOf Ψ p q r = ⟨.inr r.1, ⟨r.2 - p, by show _ < q; omega⟩⟩ := dif_neg h
    rw [e]
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_neg (by omega)]
    constructor
    · intro h1
      refine ⟨⟨a, ?_⟩, Fin.ext rfl⟩
      show (a : ℕ) < (r.2 : ℕ) - p + 1
      omega
    · rintro ⟨y, rfl⟩
      have hy : (y : ℕ) < (r.2 : ℕ) - p + 1 := y.2
      show (y : ℕ) < (r.2 : ℕ) + 1 - p
      omega

theorem det_fMat_eq {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ} (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    {K₀ : Type} {J₀ : K₀ → Type} (τ : Ψ) (t : StepIx Ψ p q) (hs : t.1 = .inl τ ∨ t.1 = .inr τ)
    (C : Finset (Fin (p + q)))
    (hC : ∀ a, a ∈ C ↔ ∃ y : Fin ((t.2 : ℕ) + 1), posOf p q t.1 (Fin.castLE t.2.2 y) = a)
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) :
    ((fMat A t.1).submatrix J (Fin.castLE t.2.2)).det =
      ∑ I, algebraMap Ω (GenField Ω (rk Ψ p q))
        (coefF (K₀ := K₀) (J₀ := J₀) A ⟨.inr t, J⟩ I) * minorIJ (gMat p q Ω τ) I C := by
  have hf : StrictMono fun y : Fin ((t.2 : ℕ) + 1) => posOf p q t.1 (Fin.castLE t.2.2 y) :=
    (posOf_strictMono t.1).comp (Fin.strictMono_castLE _)
  have hCe : C = Finset.univ.image fun y : Fin ((t.2 : ℕ) + 1) => posOf p q t.1 (Fin.castLE t.2.2 y) := by
    ext a
    simp [hC]
  have hcard : C.card = (t.2 : ℕ) + 1 := by
    rw [hCe, Finset.card_image_of_injective _ hf.injective]
    simp
  have henum : ∀ y, C.orderEmbOfFin hcard y = posOf p q t.1 (Fin.castLE t.2.2 y) := fun y =>
    congrFun (Finset.orderEmbOfFin_unique hcard (fun x => (hC _).2 ⟨x, rfl⟩) hf).symm y
  have hmat : (fMat A t.1).submatrix J (Fin.castLE t.2.2) =
      ((aExt A t.1).map (algebraMap Ω (GenField Ω (rk Ψ p q)))).submatrix J id *
        (gMat p q Ω τ).submatrix id (C.orderEmbOfFin hcard) := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.map_apply, id, fMat]
    rw [sum_aExt_mul A _ t.1 (J x) fun a => gMat p q Ω τ a (C.orderEmbOfFin hcard y)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [henum, gMat_posOf Ω τ t.1 hs]
  rw [hmat, det_mul_cols _ _ C hcard]
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  by_cases e : I.card = (t.2 : ℕ) + 1
  · rw [dif_pos e]
    simp only [coefF]
    rw [dif_pos e, RingHom.map_det]
    rfl
  · rw [dif_neg e]
    simp [coefF, e]

theorem yv_step :
    ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ)
      (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀]
      (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω),
    ∀ r k, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = some k → ∀ i : idx J₀ n k,
      yv A x₀ ⟨k, i⟩ = ∑ I, algebraMap Ω (GenField Ω (rk Ψ p q)) (coefF A ⟨k, i⟩ I) *
        minorIJ (gMat p q Ω r.1) I (stepCols (p + q) p r.2) := by
  intro Ψ _ p q Ω _ n A K₀ _ J₀ _ x₀ r k hk i
  unfold blkF at hk
  split_ifs at hk with hp
  obtain rfl := Option.some.inj hk
  exact det_fMat_eq A r.1 (stepOf Ψ p q r) (stepOf_fst r) _ (mem_stepCols_iff r) i

end GlobalTheory.CompanionTheory.Ar.PB.FMX.BlockEmbeddings
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem _root_.GlobalTheory.T.value_constant_on_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (s : Ω) (z z' : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal x) → SameOrbit z z' → valAt x s z = valAt x s z' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit <;> assumption)
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

open GroundTheory.Heights₂.Heights.ComplexSets

theorem setChartIdeal_le_chartIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {S : Set ((Σ k, ι k) → ℂ)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ0 : ∀ w, Ψ w 0 = w i) :
    GlobalTheory.CompanionTheory.Ar.Pub.CxChart.setChartIdeal S σ Ψ ≤ GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal S σ i := by
  have hset : GlobalTheory.CompanionTheory.Ar.Pub.CxChart.setChartSet S σ Ψ = GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSet S σ i := by
    ext x
    simp only [GlobalTheory.CompanionTheory.Ar.Pub.CxChart.setChartSet, GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSet, hΨ0]
  rw [GlobalTheory.CompanionTheory.Ar.Pub.CxChart.setChartIdeal, GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal, hset]

theorem chartProj_finite : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ w, Ψ w 0 = w i) →
    (∀ J ∈ chartComponents (conePts Q) σ i, ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)) →
    ∀ J ∈ chartComponents (conePts Q) σ i,
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) := by
  intro K _ _ ι _ Q e m σ i Ψ hQ hΨ hΨ0 hdim J hJ
  have hJm := GlobalTheory.CompanionTheory.Ar.Pub.CxChart.mem_chartComponents.1 hJ
  have hR : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ.2.1.2.1
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cone_pow_mem hR hΨ
        ((setChartIdeal_le_chartIdeal hΨ0).trans hJm.1.2) a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨FiniteProjHomInjective.proof m e J _ hJm.1.1 (hdim J hJ) hfin, hfin⟩

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem _root_.GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic : ∀ (e : ℕ) (f : (Fin e → ℂ) → ℂ) (z : Fin e → ℂ), AnalyticAt ℂ f z → f z ≠ 0 → ∃ Hh : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, Real.log ‖f z'‖ = (Hh z').re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_eventually_eq_re_analyticAt | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_eventually_eq_re_analyticAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_eventually_eq_re_analyticAt <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem _root_.GlobalTheory.T.generic_degree_of_arith_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → GenDegStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system | exact GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system <;> assumption)
end
