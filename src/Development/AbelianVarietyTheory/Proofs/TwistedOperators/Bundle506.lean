module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle216
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle121
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle128
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Formalism.LocalToGlobal.Columns.Adelic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle211
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.LocalToGlobal.Columns.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle471
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle470
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle236
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle333
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowTheta

theorem isThetaFunO_cosVec {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (i : ℕ) (hi : i < D.R.m) (κ : G.CosAt i) :
    IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (W.cosVec i κ) := by
  obtain ⟨e, -, h⟩ := W.cosVec_is
  exact GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is (h i hi κ) (W.vac_is i hi).2.2

theorem isThetaFunO_datum {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (ρ : G.RealVec) (Φ : G.Datum) (i : Fin D.R.m) :
    IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (W.datum ρ Φ i) :=
  GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ (isThetaFunO_cosVec W i i.2 (Φ i)) (ρ i)

end GlobalTheory.RowTheta

theorem GlobalTheory.RowTheta.rowDatum_isThetaFunO : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {_} _ _ _ _ _ {_} ch => ∀ (Φ : ch.G.Datum) (i : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.chi i 0)) (ch.G.pT (.chi i 0)) (ch.W.datum ch.ρ Φ i) :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ Φ i =>
    GlobalTheory.RowTheta.isThetaFunO_datum ch.W ch.ρ Φ i⟩⟩

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj
open Formalism.L2.Ker MvPolynomial

noncomputable section

namespace GlobalTheory.KernelAlg


open GlobalTheory.ThetaAlgebraic in
theorem coefIn_dict (D : D7) (hI : GlobalTheory.NormSum.Inp D) {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (hC : StandardLatticesGL3.Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t0) {N N' : ℕ} (e0 : TaylorLogMetric.VC D N N' → ℂ)
    (he : StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) t0 (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') e0)
    (Ls : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (κ : ℂ) (hκ : κ ∈ TaylorLogMetric.Qbar) {n : ℕ} (r : Fin n → TaylorLogMetric.Qbar) (s : Fin n → TaylorLogMetric.VC D N N') (k : ℕ) (hk : 0 < k)
    (hs : ∀ i, k • s i ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) Ls Lt) :
    TaylorLogMetric.CoefIn D (fun z => κ * ∑ i, (r i : ℂ) * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (s i)
      (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.La0 D (TaylorLogMetric.tor0 D cc δ) N N') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) Ls Lt) e0) z) TaylorLogMetric.Qbar := by
  obtain ⟨b, κ0, hb, hκ0, rfl⟩ := he
  have hG := hI.g1
  have hU := hI.use1
  have hg := ((good_theta hG hU hC hb ht).iop hG hC hb (StandardLatticesGL3.LaB D (TaylorLogMetric.tor0 D cc δ) b) _
    (la_le cc δ hG hb (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).const_mul hκ0.1
  have hg2 := hg.iop hG hC hb (StandardLatticesGL3.La0 D (TaylorLogMetric.tor0 D cc δ) N N') _ (la_le cc δ hG hb Ls Lt)
  have hT : ∀ i, Good cc δ b (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (s i)
      (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.La0 D (TaylorLogMetric.tor0 D cc δ) N N') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) Ls Lt)
        fun z => κ0 * TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.LaB D (TaylorLogMetric.tor0 D cc δ) b) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
          (StandardLatticesGL3.pullB D (TaylorLogMetric.tor0 D cc δ) b (GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) t0)) z)) := fun i =>
    hg2.transl hG hC hb (sat_of_nsmul hk (la_le cc δ hG hb Ls Lt (hs i)))
  exact ((Good.sum Finset.univ _ fun i _ => (hT i).const_mul (r i).2).const_mul hκ).coefIn

theorem applyAt0_monomial_mem (D : D7) {N N' : ℕ} (m : GL3Theta.Idx D N N' →₀ ℕ) {G : TaylorLogMetric.VC D N N' → ℂ}
    (hG : TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar) : GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) G ∈ TaylorLogMetric.Qbar := by
  classical
  unfold GL3Theta.applyAt0
  refine sum_mem fun α _ => mul_mem (mul_mem ?_ (prod_mem fun _ _ => natCast_mem _ _)) (hG α)
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem opp_isAlgebraic {T : Type} (p : GlobalTheory.ChiGrid.Pair T) {z : ℂ} (hz : IsAlgebraic ℚ z) : IsAlgebraic ℚ (opp p z) :=
  IsAlgebraic.algHom (opp p).toRatAlgHom hz

theorem fvar_fst {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) (p : GlobalTheory.ChiGrid.Pair T)
    (k : DVar D.what₂.Tau (G.V p.small).rank (G.V p.big).rank) : (fvar G p k).1 = k.1 := by
  cases p <;> rfl

theorem kk_isAlgebraic : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → GlobalTheory.NormSum.Inp D → GlobalTheory.SumSize.DictAt ch → ∀ (t : T) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p → WtOK ch.G p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 → d.P = locPl ch.G t → ch.S.Z.HasVec d → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (a : VVIdx (wt ch.G p.big)) (b : VVIdx (wt ch.G p.small)), IsAlgebraic ℚ (ch.S.Z.kk d x y a b) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hS ch hch hInp hDict t p hp hW k d hk hcos hz hP hV x y a b
  obtain ⟨Ls, Lt, κ, n, r, s, hLs, hLt, hκ, hs, -, -, -, hJ⟩ := hDict t p hp k d hk hcos hz hP x y
  set Z := ch.S.Z
  have hF := coefIn_dict D hInp Z.crv Z.pt0 (Z.e0 p) (Z.e0_is p hp).2.2.2.1 Ls Lt κ hκ.1 r s k hk hs
  set FF := (fun z => κ * ∑ i, ((r i : TaylorLogMetric.Qbar) : ℂ) * TaylorLogMetric.U D (TaylorLogMetric.tor0 D D.host.ccK Z.δ) (s i)
      (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D D.host.ccK Z.δ) (StandardLatticesGL3.La0 D (TaylorLogMetric.tor0 D D.host.ccK Z.δ) _ _)
        (TaylorLogMetric.La D (TaylorLogMetric.tor0 D D.host.ccK Z.δ) Ls Lt) (Z.e0 p)) z) with hFF
  set J2 : (DVar D.what₂.Tau (ch.G.V p.small).rank (ch.G.V p.big).rank →₀ ℕ) → ℂ := fun m =>
    opp p (GL3Theta.applyAt0 D (MvPolynomial.monomial (m.mapDomain (fvar ch.G p)) 1) FF) with hJ2
  have hA : ∀ m, IsAlgebraic ℚ (J2 m) := fun m =>
    opp_isAlgebraic p (mem_algebraicClosure_iff.1 (applyAt0_monomial_mem D _ hF))
  set c : D.what₂.Tau → ℂ := fun τ => opp p (period Z.δ τ) with hc
  have hJf : jetTab ch.W ch.S.N.frC p (Z.vec d) (x * ch.S.N.u _) (y * ch.S.N.u _) =
      fun m => (Z.c0 p : ℂ) * ((m.prod fun k e => c k.1 ^ e) * J2 m) := by
    funext m
    rw [hJ m, map_mul]
    congr 2
    rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), map_finsuppProd]
    simp only [map_pow, fvar_fst, hc]
  have hop : ∀ P : Formalism.L2.DIV.VV ℂ (wt ch.G p.small),
      jetOp (wt ch.G p.small) (wt ch.G p.big) (jetTab ch.W ch.S.N.frC p (Z.vec d) (x * ch.S.N.u _) (y * ch.S.N.u _))
        (nuEnd ch.G p) P = ((Z.c0 p : ℂ) * ∏ τ, c τ ^ fockDeg ch.G p τ) • jetOp _ _ J2 (nuEnd ch.G p) P := by
    intro P
    rw [hJf]
    simp only [jetOp, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [GlobalTheory.T.thetaJetMap_weighted_table_scale, GlobalTheory.T.blockAction_diagonal_coefficientSpace_smul _ _ _ (hW.2 J2 P.1 P.2), smul_smul, map_smul]
    rfl
  simp only [Normal.kk, Normal.kkIn, Normal.kkMap, LinearMap.toMatrix_apply, LinearMap.smul_apply, fockComp]
  rw [hop, map_smul, map_smul]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  have hR := GlobalTheory.T.jetOperator_bideterminantBasis_repr_isAlgebraic _ _ J2 (nuEnd ch.G p) hA hW.2 a b
  have e : Z.scal 1 p * ((Z.c0 p : ℂ) * ∏ τ, c τ ^ fockDeg ch.G p τ) =
      ∏ τ, opp p ((1 / period Z.δ τ) * period Z.δ τ) ^ fockDeg ch.G p τ := by
    simp only [Normal.scal, Pi.one_apply, hc, map_mul, mul_pow, Finset.prod_mul_distrib]
    rw [mul_mul_mul_comm, Units.inv_mul, one_mul]
  have hK : Z.scal 1 p * ((Z.c0 p : ℂ) * ∏ τ, c τ ^ fockDeg ch.G p τ) ∈ TaylorLogMetric.Qbar := by
    rw [e]
    refine prod_mem fun τ _ => pow_mem ?_ _
    rw [mem_algebraicClosure_iff]
    apply opp_isAlgebraic
    by_cases h : period Z.δ τ = 0
    · simp [h, isAlgebraic_zero]
    · simp [h, isAlgebraic_one]
  rw [← mul_assoc, ← mem_algebraicClosure_iff]
  exact mul_mem hK (mem_algebraicClosure_iff.2 hR)

end GlobalTheory.KernelAlg
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

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC



namespace GlobalTheory.MovedSD

open Matrix

open Formalism.UG in
theorem colLat_one_eq_stdLat (D : D7) (n : ℕ) :
    colLat (1 : GL (Fin n) D.host.E) = Formalism.L2.Col.stdLat D.host.E n := by
  ext x
  rw [GlobalTheory.TestLat.Inhabitant.mem_colLat_one]
  simp [Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]

theorem move_vec (D : D7) {n : ℕ} (fr : GL (Fin n) D.host.E) (a b : GL (Fin n) (Lev.EAf D)) (v : Fin n → D.host.E) :
    (fr⁻¹).val.map (eToEAf D) *ᵥ ((b⁻¹).val *ᵥ ((a⁻¹).val *ᵥ fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((fr.val *ᵥ v) i))) =
      (Formalism.UG.bc (eToEAf D) fr⁻¹ * b⁻¹ * a⁻¹ * Formalism.UG.bc (eToEAf D) fr).val *ᵥ fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (v i) := by
  have hb : ∀ g : GL (Fin n) D.host.E, (Formalism.UG.bc (eToEAf D) g).val = g.val.map (eToEAf D) := fun _ => rfl
  have ev : (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((fr.val *ᵥ v) i)) =
      fr.val.map (eToEAf D) *ᵥ fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (v i) := by
    funext i
    exact RingHom.map_mulVec (eToEAf D) fr.val v i
  rw [ev]
  simp only [Units.val_mul, hb, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem mem_globLat_move (D : D7) {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (fr : GL (Fin n) D.host.E)
    (a b : GL (Fin n) (Lev.EAf D))
    (hu : ∀ w, w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔ b.val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (v : Fin n → D.host.E) :
    fr.val *ᵥ v ∈ Formalism.UG.CS.globLat a Λ ↔
      v ∈ Formalism.UG.CS.globLat (Formalism.UG.bc (eToEAf D) fr⁻¹ * (a * b) * Formalism.UG.bc (eToEAf D) fr) (Formalism.L2.Col.stdLat D.host.E n) := by
  change (_ ∈ Formalism.L2.Herm.hatL (F := D.host.F) _) ↔ (_ ∈ Formalism.L2.Herm.hatL (F := D.host.F) _)
  generalize hw : ((a⁻¹).val *ᵥ fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((fr.val *ᵥ v) i)) = w
  have h1 := hu ((b⁻¹).val *ᵥ w)
  have e1 : b.val *ᵥ ((b⁻¹).val *ᵥ w) = w := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [e1] at h1
  rw [← h1]
  have hm := GlobalTheory.LatMulAd.mem_hatL_colLat_mul D fr 1 ((b⁻¹).val *ᵥ w)
  rw [mul_one, colLat_one_eq_stdLat] at hm
  rw [hm, ← hw]
  have eg : ((Formalism.UG.bc (eToEAf D) fr⁻¹ * (a * b) * Formalism.UG.bc (eToEAf D) fr)⁻¹ : GL (Fin n) (Lev.EAf D)) =
      Formalism.UG.bc (eToEAf D) fr⁻¹ * b⁻¹ * a⁻¹ * Formalism.UG.bc (eToEAf D) fr := by
    simp only [_root_.mul_inv_rev, ← map_inv, inv_inv, mul_assoc]
  rw [eg]
  refine Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Col.stdLat D.host.E n)) ?_)
  exact move_vec D fr a b v

theorem cT_map_inclE (D : D7) {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) :
    Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (M.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  rfl

theorem move_mem_UAd (D : D7) {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (fr : GL (Fin n) D.host.E)
    (hfr : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.val * J * fr.val = 1) (a b : GL (Fin n) (Lev.EAf D))
    (ha : a ∈ Formalism.L2.DIV.UA D.sp.cm J) (hb : b ∈ Formalism.L2.DIV.UA D.sp.cm J) :
    Formalism.UG.bc (eToEAf D) fr⁻¹ * (a * b) * Formalism.UG.bc (eToEAf D) fr ∈ Formalism.L2.Col.UAd D.sp.cm n := by
  have hab : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (a * b).val *
      J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * (a * b).val =
      J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := mul_mem ha hb
  set A := (a * b).val
  set ι := Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (Formalism.L2.Herm.Af D.host.F)
  set σR := Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)
  have hm : ∀ g : GL (Fin n) D.host.E, (Formalism.UG.bc (eToEAf D) g).val = g.val.map ι := fun _ => rfl
  have hF : Formalism.UG.cT σR (fr.val.map ι) * J.map ι * fr.val.map ι = 1 := by
    rw [cT_map_inclE, ← Matrix.map_mul, ← Matrix.map_mul, hfr, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : fr.val.map ι * (fr⁻¹).val.map ι = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT σR ((fr⁻¹).val.map ι) * (fr⁻¹).val.map ι = J.map ι := by
    calc Formalism.UG.cT σR ((fr⁻¹).val.map ι) * (fr⁻¹).val.map ι
        = Formalism.UG.cT σR ((fr⁻¹).val.map ι) * (Formalism.UG.cT σR (fr.val.map ι) * J.map ι * fr.val.map ι) * (fr⁻¹).val.map ι := by
          rw [hF, Matrix.mul_one]
      _ = Formalism.UG.cT σR (fr.val.map ι * (fr⁻¹).val.map ι) * J.map ι * (fr.val.map ι * (fr⁻¹).val.map ι) := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J.map ι := by
          rw [h1]; simp [Formalism.UG.cT]
  show Formalism.UG.cT σR (_ : GL (Fin n) (Lev.EAf D)).val * (1 : Matrix (Fin n) (Fin n) D.host.E).map ι * _ = _
  rw [Units.val_mul, Units.val_mul, hm, hm, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  calc Formalism.UG.cT σR ((fr⁻¹).val.map ι * A * fr.val.map ι) * ((fr⁻¹).val.map ι * A * fr.val.map ι)
      = Formalism.UG.cT σR (fr.val.map ι) * (Formalism.UG.cT σR A * (Formalism.UG.cT σR ((fr⁻¹).val.map ι) * (fr⁻¹).val.map ι) * A) * fr.val.map ι := by
        rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hJ, hab, hF]

theorem sd_latAt {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (hX : DefNode D.R.m X) (x : FinPt G X) : SD D (GlobalTheory.SumSize.latAt S X x) := by
  have e : GlobalTheory.SumSize.latAt S X x = Formalism.UG.CS.globLat (Formalism.UG.bc (eToEAf D) (S.N.fr X)⁻¹ *
      (finG (G.V X) x * Lev.finE (G.V X) (S.N.u X : Formalism.L2.Theta.GA D (G.V X))) * Formalism.UG.bc (eToEAf D) (S.N.fr X))
      (Formalism.L2.Col.stdLat D.host.E _) := by
    ext v
    exact mem_globLat_move D (G.Λ X) (S.N.fr X) _ _ (S.N.u_lat X hX) v
  have ha : finG (G.V X) x ∈ Formalism.L2.DIV.UA D.sp.cm (G.V X).gram := GlobalTheory.LevSplit.finE_mem_UA (G.V X) x.1
  have hb := GlobalTheory.LevSplit.finE_mem_UA (G.V X) (S.N.u X : Formalism.L2.Theta.GA D (G.V X))
  show IsSDLat D.host.E _ _
  rw [e]
  exact Formalism.L2.Col.DetChrChi.isSDLat_globLat D.sp.cm (move_mem_UAd D _ _ (S.N.fr_on X hX) _ _ ha hb)

end GlobalTheory.MovedSD
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cosetSum_heisenberg_isEigenvector : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (Λd : AddSubgroup (WO S T)) (R : Finset (WO S T)) (x : WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ ∀ u ∈ Λd, ψ (symplO S T u y) = 1) → (∀ y, IsHalf (cA D e) y → (∀ u ∈ Λd, ψ (symplO S T u y) = 1) → ∃ y' ∈ R, y - y' ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) → (∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → y = y') → (∀ a ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf (cA D e) a → ψ (symplO S T x a) = 1) → ∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) g → ∀ y, IsHalf (cA D e) y → (∀ u ∈ Λd, ψ (symplO S T u y) = 1) → heisO ψ S T y (∑ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T z g) = ψ (symplO S T x y) • ∑ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T z g := by
  first | exact @GlobalTheory.CosetEigen.cosetSum_eigen | exact GlobalTheory.CosetEigen.cosetSum_eigen | (intros; apply GlobalTheory.CosetEigen.cosetSum_eigen <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.infinitePart_eq_zero_of_isHalf_idempotentSum : ∀ {D : D7} (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ {m n : ℕ} (y : Mx D m n), (IsHalf e y ∨ IsHalf (cA D e) y) → y.map (infPart D) = 0 := by
  first | exact @GlobalTheory.IdemHalf.halfFin | exact GlobalTheory.IdemHalf.halfFin | (intros; apply GlobalTheory.IdemHalf.halfFin <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isThetaFunction_finiteHeisenbergCombination : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (g : WO S T → ℂ), IsThetaFunO ψ S T g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, (t z).map (infPart D) = 0) → IsThetaFunO ψ S T (∑ z ∈ R, c z • heisO ψ S T (t z) g) ∧ ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ), pureTensorO ψ θ S T sS sT BS BT (∑ z ∈ R, c z • heisO ψ S T (t z) g) φ = ∑ z ∈ R, c z • heisO ψ S T (t z) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
  first | exact @GlobalTheory.CombTheta.comb_theta | exact GlobalTheory.CombTheta.comb_theta | (intros; apply GlobalTheory.CombTheta.comb_theta <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isTheta_isLatticeVacuum_fockPureTensor : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) (latO S T LS LT P) g → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ), IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT g φ) ∧ IsLatVac (heisO ψ S T) (latO S T LS LT P) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
  first | exact @GlobalTheory.FockLatVac.theta_isLatVac_pureTensorO | exact GlobalTheory.FockLatVac.theta_isLatVac_pureTensorO | (intros; apply GlobalTheory.FockLatVac.theta_isLatVac_pureTensorO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sum_heisenbergTranslates_latticeVacuum_ne_zero : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (R : Finset (WO S T)), (∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → ∃ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf e u ∧ ψ (symplO S T u y) ≠ ψ (symplO S T u y')) → ∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) g → g ≠ 0 → ∀ c : WO S T → ℂ, (∃ z ∈ R, c z ≠ 0) → ∑ z ∈ R, c z • heisO ψ S T z g ≠ 0 := by
  first | exact @GlobalTheory.HeisJointEigen.sum_heisO_ne_zero | exact GlobalTheory.HeisJointEigen.sum_heisO_ne_zero | (intros; apply GlobalTheory.HeisJointEigen.sum_heisO_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.symplecticForm_offIdempotentPart_orthogonal_half : ∀ (D : D7) (S T : HSp D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ w x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → symplO S T ((1 - e - cA D e) • w) x = 0 := by
  first | exact @GlobalTheory.IdemOffOrth.symplO_compl_half | exact GlobalTheory.IdemOffOrth.symplO_compl_half | (intros; apply GlobalTheory.IdemOffOrth.symplO_compl_half <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.dual_irreducible_coefficientSpace_realPlaces : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is → ∀ N : Submodule ℂ (Module.Dual ℂ c.W), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ f ∈ N, (c.ρ (atTau θ V τ g)⁻¹).dualMap f ∈ N) → N = ⊥ ∨ N = ⊤ := by
  first | exact @GlobalTheory.DualIrr.dual_irr | exact GlobalTheory.DualIrr.dual_irr | (intros; apply GlobalTheory.DualIrr.dual_irr <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockRealMove

theorem compAt_mt_of_mem_GfC {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) {x : GA D V} (hx : x ∈ GfC V) :
    compAt θ τ (mt V x) = 1 :=
  GlobalTheory.LocWeil.CompactPart.infMat_of_fin V (θ τ) hx

theorem om_fin_fockVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ x ∈ GfC S, ∀ y ∈ GfC T, IsThetaFunO ψ S T (om (x, y) f) ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (om (x, y) f) := by
  intro D ψ θ S T χS χT om hW hθ sS sT f hf hvac x hx y hy
  refine ⟨hW.om_pres _ _ hf, fun τ z => ?_⟩
  have hS : sS τ * compAt θ τ (mt S x) = compAt θ τ (mt S x) * sS τ := by
    rw [compAt_mt_of_mem_GfC θ τ S hx, Matrix.mul_one, Matrix.one_mul]
  have hT : sT τ * compAt θ τ (mt T y) = compAt θ τ (mt T y) * sT τ := by
    rw [compAt_mt_of_mem_GfC θ τ T hy, Matrix.mul_one, Matrix.one_mul]
  have key := GlobalTheory.FockMove.om_annih hW hθ x y τ hS hT (compAt θ τ (mt T y⁻¹) * z * compAt θ τ (mt S x)) hf
  rw [hvac τ, map_zero] at key
  have e : compAt θ τ (mt T y) * (compAt θ τ (mt T y⁻¹) * z * compAt θ τ (mt S x)) * compAt θ τ (mt S x⁻¹) = z := by
    rw [compAt_mt_of_mem_GfC θ τ S hx, compAt_mt_of_mem_GfC θ τ S (inv_mem hx),
      compAt_mt_of_mem_GfC θ τ T hy, compAt_mt_of_mem_GfC θ τ T (inv_mem hy)]
    simp
  rw [e] at key
  exact key.symm

end GlobalTheory.FockRealMove

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isFockVacuumAt_finiteHeisenbergCombination : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (τ : D.what₂.Tau) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ J g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, (t z).map (infPart D) = 0) → IsFockVacAt (heisO ψ S T) θ τ J (∑ z ∈ R, c z • heisO ψ S T (t z) g) := by
  first | exact @GlobalTheory.CombFockTranslate.isFockVacAt_comb | exact GlobalTheory.CombFockTranslate.isFockVacAt_comb | (intros; apply GlobalTheory.CombFockTranslate.isFockVacAt_comb <;> assumption)
end
