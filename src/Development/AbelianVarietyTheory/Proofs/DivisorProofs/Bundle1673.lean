module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1629
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridTopVertexFramePointTransportLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEntireLatticeSumOfHeckeLContinuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValCoordOfMemHatOUnits
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1631
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1632
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

@[expose] public section

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.finrank_deepestFiltrationStep_eq_rational : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → F) (δ : ℕ) (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ), FiniteDimensional E (Φ.U (S.T - S.D)) ∧ Module.finrank E (Φ.U (S.T - S.D)) = S.deepRank s ∧ S.deepRank s ≤ Module.finrank F (S.V S.T) := by
  first | exact @GlobalTheory.HSShort.deepStep_finrank | exact GlobalTheory.HSShort.deepStep_finrank | (intros; apply GlobalTheory.HSShort.deepStep_finrank <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.gridTopVertex_frame_point_transport_lattice : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : Consts) (G : GridData L sc) (S : Finset ℕ)
    (fr₀ : GL (Fin (G.V (.grid D.R.m D.R.m)).rank) D.host.E) (u₀ : FinPt G (.grid D.R.m D.R.m)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr₀.1 * (G.V (.grid D.R.m D.R.m)).gram * fr₀.1 = 1 →
    (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u₀.1 ∧ ∀ w ∈ P, Off S w) →
    (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr₀) ↔
        (Formalism.IndefR.Lev.finE (G.V (.grid D.R.m D.R.m)) u₀.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid D.R.m D.R.m))) →
    ∃ (fr : GL (Fin (G.V (.top D.R.m)).rank) D.host.E) (u : FinPt G (.top D.R.m)),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * (G.V (.top D.R.m)).gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u.1 ∧ ∀ w ∈ P, Off S w) ∧
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE (G.V (.top D.R.m)) u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.top D.R.m))) ∧
      (∀ i (k : Fin (G.V (.grid D.R.m D.R.m)).rank), fr.1 i (Formalism.L2.Col.Br.iC G.sp.topDec.rank.symm k) =
        (frameMat _ _ G.sp.topDec.ι * fr₀.1) i k) ∧
      (∀ i, fr.1 i (Formalism.L2.Col.Br.iL G.sp.topDec.rank.symm) = G.sp.topDec.a i 0) ∧
      HMul.hMul (mt (G.V (.top D.R.m)) u.1) (topEmb G) = HMul.hMul (topEmb G) (mt (G.V (.grid D.R.m D.R.m)) u₀.1) ∧
      mt (G.V (.top D.R.m)) u.1 *ᵥ topVec G = topVec G := by
  first | exact @GlobalTheory.FunObj.top_transport | exact GlobalTheory.FunObj.top_transport | (intros; apply GlobalTheory.FunObj.top_transport <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

theorem _root_.GlobalTheory.T.zero_dim_support_euler_char : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (L : LB Y) (hL : L.IsLB) (F : Y.Modules) [IsFiniteQC F], suppDim F ≤ 0 → ∀ j : ℤ, (GlobalTheory.hdim k (GlobalTheory.twistZ F L j) 0 : ℤ) = GlobalTheory.chi k F := by
  first | exact @GlobalTheory.HSCore.hdim_zero_twistZ_eq_chi_of_suppDim_le_zero | exact GlobalTheory.HSCore.hdim_zero_twistZ_eq_chi_of_suppDim_le_zero | (intros; apply GlobalTheory.HSCore.hdim_zero_twistZ_eq_chi_of_suppDim_le_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth

theorem _root_.GlobalTheory.T.detFactorDepthInChart_independent_closedField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X X' : ValExt T p) (f : Lt1 Dw) (k : ℕ), nuFacC Ch X f k = nuFacC Ch X' f k := by
  first | exact @GlobalTheory.DepthField.nuFacC_field | exact GlobalTheory.DepthField.nuFacC_field | (intros; apply GlobalTheory.DepthField.nuFacC_field <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

theorem _root_.GlobalTheory.T.exists_local_lift_sectionsOnClosedSubscheme : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (B : LB Y), B.IsLB → ∀ (I : Y.IdealSheafData) (g : sectionsOnClosedSubscheme p B I) (y : Y), ∃ (W : Y.Opens) (_ : y ∈ W) (b : Vanishing.H0 p B W), ∀ (z : I.subscheme) (hz : I.subschemeι z ∈ W) (j : (B.pull I.subschemeι).ι) (hj : z ∈ (B.pull I.subschemeι).U j), Vanishing.H0.germ j z (TopologicalSpace.Opens.mem_top z) hj g = (I.subschemeι.stalkMap z).hom (Vanishing.H0.germ (j PUnit.unit) (I.subschemeι z) hz (mem_pull.1 hj) b) := by
  first | exact @GlobalTheory.Vanishing.exists_local_lift_H0On | exact GlobalTheory.Vanishing.exists_local_lift_H0On | (intros; apply GlobalTheory.Vanishing.exists_local_lift_H0On <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.AbsHalfInv

theorem v_det_KGL {E : Type} [Field E] [NumberField E] {w : Pl E} {n : ℕ} {k : GLw n w}
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v (k.val.det) = 1 := by
  obtain ⟨y, rfl⟩ := hk
  have hu : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  obtain ⟨u, hu⟩ := hu
  have hdet : (Formalism.UG.bc (Ov E w).subtype y).val.det = ((u : Ov E w) : w.adicCompletion E) := by
    rw [hu]
    change (y.val.map (Ov E w).subtype).det = _
    exact (RingHom.map_det (Ov E w).subtype y.val).symm
  rw [hdet]
  have h1 : Valued.v ((u : Ov E w) : w.adicCompletion E) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (u : Ov E w).2
  have h2 : Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 ((u⁻¹ : (Ov E w)ˣ) : Ov E w).2
  have h3 : Valued.v ((u : Ov E w) : w.adicCompletion E) *
      Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, map_one]
  by_contra hne
  have hlt := lt_of_le_of_ne h1 hne
  have : Valued.v ((u : Ov E w) : w.adicCompletion E) *
      Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [h3] at this
  exact lt_irrefl _ this

theorem v_det_mul_left {E : Type} [Field E] [NumberField E] {w : Pl E} {n : ℕ} {k m : GLw n w}
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v ((k * m).val.det) = Valued.v m.val.det := by
  rw [Units.val_mul, Matrix.det_mul, map_mul, v_det_KGL hk, one_mul]

theorem v_det_mul_right {E : Type} [Field E] [NumberField E] {w : Pl E} {n : ℕ} {k m : GLw n w}
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v ((m * k).val.det) = Valued.v m.val.det := by
  rw [Units.val_mul, Matrix.det_mul, map_mul, v_det_KGL hk, mul_one]

theorem absHalf_congr {E : Type} [Field E] [NumberField E] {w : Pl E} {x y : w.adicCompletion E}
    (h : Valued.v x = Valued.v y) : absHalf w x = absHalf w y := by
  have : ordL x = ordL y := by unfold ordL; simp only [h]
  unfold absHalf
  rw [this]

end GlobalTheory.BCT.AbsHalfInv

open GlobalTheory.BCT.AbsHalfInv in
theorem GlobalTheory.BCT.absHalf_blockDet_KGL_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m k : GLw a w × GLw b w),
    k.1 ∈ GlobalTheory.LFun.KGL w (n := a) → k.2 ∈ GlobalTheory.LFun.KGL w (n := b) →
    absHalf w ((k * m).1.val.det ^ b / (k * m).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) ∧
      absHalf w ((m * k).1.val.det ^ b / (m * k).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) := by
  intro E _ _ _ a b w m k h1 h2
  refine ⟨absHalf_congr ?_, absHalf_congr ?_⟩
  · rw [map_div₀, map_div₀, map_pow, map_pow, map_pow, map_pow, Prod.fst_mul, Prod.snd_mul,
      v_det_mul_left h1, v_det_mul_left h2]
  · rw [map_div₀, map_div₀, map_pow, map_pow, map_pow, map_pow, Prod.fst_mul, Prod.snd_mul,
      v_det_mul_right h1, v_det_mul_right h2]
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.orbitalIntegral_restrictedProduct_eq_prod : ∀ (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)] (p : ∀ i, G →* H i) (K : Subgroup G) (KH : ∀ i, Subgroup (H i)) (δ : G) (f : ∀ i, H i → ℂ), (∀ i, Continuous (p i)) → (∀ x y : G, (∀ i, p i x = p i y) → x = y) → (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) → IsCompact {x : G | ∀ i, p i x ∈ C i}) → (∀ i, IsCompact (KH i : Set (H i))) → (∀ i, ∀ a ∈ twCent (MonoidHom.id (H i)) (p i δ), ∀ b ∈ twCent (MonoidHom.id (H i)) (p i δ), a * b = b * a) → (∀ i (x : H i), twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ∧ (twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) ≠ 0) → (∀ i (x : H i), (rStab fun k : KH i => f i ((x * k)⁻¹ * p i δ * (x * k))).index ≠ 0) → (∀ i, {q : DoubleCoset.Quotient (twCent (MonoidHom.id (H i)) (p i δ) : Set (H i)) (KH i : Set (H i)) | ∃ k ∈ KH i, f i ((Quotient.out q * k)⁻¹ * p i δ * (Quotient.out q * k)) ≠ 0}.Finite) → (∀ᶠ i in cofinite, p i δ ∈ KH i ∧ f i = (KH i : Set (H i)).indicator 1 ∧ (∀ g : H i, g⁻¹ * p i δ * g ∈ KH i → ∃ t ∈ twCent (MonoidHom.id (H i)) (p i δ), t⁻¹ * g ∈ KH i) ∧ cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ≤ KH i) → twOrb (MonoidHom.id G) K δ (fun x => ∏ᶠ i, f i (p i x)) = ∏ᶠ i, twOrb (MonoidHom.id (H i)) (KH i) (p i δ) (f i) := by
  first | exact @GlobalTheory.RestrProd.twOrb_restrProd | exact GlobalTheory.RestrProd.twOrb_restrProd | (intros; apply GlobalTheory.RestrProd.twOrb_restrProd <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

theorem exists_open_conjStable_sub_level (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (K' : Subgroup (UL n w)) (hw : IsSplitAt w) (hK : IsLevel (MonoidHom.id _) (KL n w) K') :
    ∃ N : Subgroup (GLw n w), IsOpen (N : Set (GLw n w)) ∧
      N ≤ K'.map (UL n w).subtype ∧ (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x ∈ N, k⁻¹ * x * k ∈ N) ∧
      (K' = KL n w → N = GlobalTheory.LFun.KGL w (n := n)) := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hUtop : UL n w = ⊤ := by unfold UL; rw [if_pos hw]
  have hUo : IsOpen (UL n w : Set (GLw n w)) := by rw [hUtop]; exact isOpen_univ
  have hmemU : ∀ x : GLw n w, x ∈ UL n w := fun x => by rw [hUtop]; trivial
  by_cases hKL : K' = KL n w
  · refine ⟨GlobalTheory.LFun.KGL w (n := n), hKo, ?_, ?_, fun _ => rfl⟩
    · intro x hx
      refine Subgroup.mem_map.2 ⟨⟨x, hmemU x⟩, ?_, rfl⟩
      rw [hKL, KL, Subgroup.mem_subgroupOf]
      exact hx
    · intro k hk x hx
      exact (GlobalTheory.LFun.KGL w (n := n)).mul_mem ((GlobalTheory.LFun.KGL w (n := n)).mul_mem ((GlobalTheory.LFun.KGL w (n := n)).inv_mem hk) hx) hk
  · set S : Subgroup (GLw n w) := K'.map (UL n w).subtype with hSdef
    have hSo : IsOpen (S : Set (GLw n w)) := by
      rw [hSdef, Subgroup.coe_map]
      exact hUo.isOpenMap_subtype_val _ hK.1
    haveI : CompactSpace (GlobalTheory.LFun.KGL w (n := n)) := isCompact_iff_compactSpace.1 hKc
    have hWo : IsOpen ((S.subgroupOf (GlobalTheory.LFun.KGL w (n := n)) : Subgroup _) : Set (GlobalTheory.LFun.KGL w (n := n))) := by
      rw [Subgroup.coe_subgroupOf]
      exact hSo.preimage continuous_subtype_val
    obtain ⟨V, hV⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
      ⟨Subgroup.isClosed_of_isOpen _ hWo, hWo⟩ (Subgroup.one_mem _)
    refine ⟨V.toSubgroup.map (GlobalTheory.LFun.KGL w (n := n)).subtype, ?_, ?_, ?_, fun h => absurd h hKL⟩
    · rw [Subgroup.coe_map]
      exact hKo.isOpenMap_subtype_val _ V.isOpen'
    · rintro _ ⟨v, hv, rfl⟩
      have := hV hv
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at this
      exact this
    · rintro k hk _ ⟨v, hv, rfl⟩
      refine ⟨(⟨k, hk⟩ : GlobalTheory.LFun.KGL w (n := n))⁻¹ * v * (⟨k, hk⟩ : GlobalTheory.LFun.KGL w (n := n)), ?_, ?_⟩
      · have := V.isNormal'.conj_mem v hv (⟨k, hk⟩ : GlobalTheory.LFun.KGL w (n := n))⁻¹
        simpa using this
      · simp

end GlobalTheory.BCT.CtLevel
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds

namespace GlobalTheory.ToricDenomRow

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem beta_eq_pow (d s : ℕ) (κ : I → ℕ) (Λ : PeriodPair) {Ω : ℂ} (hΩ : Ω ^ 12 = latDisc Λ) (T : ℂ) :
    beta E d s κ Λ T = ((C0 E d (2 * s) κ : ℂ) * T / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) ^ 12 := by
  rw [beta, div_pow, ← pow_mul, mul_comm _ 12, pow_mul, hΩ]

theorem classTerm_rep [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)}
    (hc : c ≠ ⊥) {χ : HChar E} (hinf : HasInf χ φ (fun i => (κ i : ℤ) + s)) (htriv : ∀ u ∈ hatOUnits c, finPart χ u = 1)
    {l : ℕ} (hl : l.Prime) (hex : ∀ y : (Af E)ˣ, ∃ S, IsLatSum φ (2 * s) κ (lattice c y) S)
    (y : (Af E)ˣ) (S : ℂ → ℂ) (hS : IsLatSum φ (2 * s) κ (lattice c y) S) :
    ∃ y' : (Af E)ˣ, OneOver l y' ∧ ∃ S' : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y') S' ∧ ∃ u : ℂ, IntAt l u ∧
      ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0 = u * S' 0 := by
  obtain ⟨y', hy', hone⟩ := GlobalTheory.CMVal.TrivAbove.exists_rep_trivial_above E c l hc hl (QuotientGroup.mk y)
  obtain ⟨S', hS'⟩ := hex y'
  refine ⟨y', hone, S', hS', ((finPart χ y' : ℂ) * ((modF y' ^ s : ℝ) : ℂ))⁻¹, ?_, ?_⟩
  · have hu := GlobalTheory.CMVal.value_unitAt E I φ hφ s κ c χ l hc hl hinf htriv y' fun w hw => by
      rw [hone w hw, map_one]
    exact (GlobalTheory.CMVal.LUnit.unitAt_inv hu).2.1
  · exact GlobalTheory.ClassInvAny.classInv_of_unit_trivial E I φ hφ s κ c χ hinf htriv y y' S S' hy'.symm hS hS'

theorem toricDenominator (hZ : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (hR : LatIntRam) (hU : LatIntUnr) :
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator := by
  intro E _ _ _ _ I _ d φ s hd hs
  obtain ⟨z, hz⟩ := (hZ E s hs).1
  have hzc : IsClassZetaVals (2 * s) z := hz
  refine ⟨z, hzc, fun κ 𝔣 Λ χ hb hΛ hχ => ?_⟩
  have hUr : UnramFin E := hd.2.2.1
  have hφ : IsCMType φ := hd.2.2.2.2.2.2.1
  obtain ⟨Ω, hΩ⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ) (by norm_num : 0 < 12)
  intro l hl Q hQ hQl
  set c := condQ 𝔣 Q with hcdef
  have hc : c ≠ ⊥ := mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hle : condQ 𝔣 Q ≤ condQ 𝔣 ∅ := by
    rw [show condQ 𝔣 ∅ = 𝔣 by simp [condQ]]
    exact Ideal.dvd_iff_le.1 (dvd_mul_right 𝔣 _)
  have h0 := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 ∅ χ hUr hb
    (fun _ h => absurd h (Finset.notMem_empty _)) hχ
  have htriv : ∀ u ∈ hatOUnits c, finPart χ u = 1 := fun u hu => h0 u (hatOUnits_mono hle hu)
  have hex : ∀ y : (Af E)ˣ, ∃ S, IsLatSum φ (2 * s) κ (lattice c y) S := fun y =>
    GlobalTheory.CMVal.LatEnt.exists_isLatSum GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ hφ s κ 𝔣 c χ hUr hs hb
      (dvd_mul_right _ _) hc hχ.1 hχ.2.2.1 htriv y
  set x : ℂ → ℂ := fun T => (C0 E d (2 * s) κ : ℂ) * T / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ with hxdef
  have hx : ∀ T, beta E d s κ Λ T = x T ^ 12 := fun T => beta_eq_pow d s κ Λ hΩ T
  have hxmul : ∀ u T, x (u * T) = u * x T := fun u T => by simp only [hxdef]; ring

  have hlat : ∀ y' : (Af E)ˣ, OneOver l y' → ∀ S' : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y') S' →
      ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (x (S' 0) ^ 12) := fun y' hy' S' hS' => by
    rw [← hx]
    by_cases h : c_vp 𝔣 l = 0
    · exact hU E I d φ s hd hs z hzc 𝔣 Λ hb hΛ l hl Q hQ hQl y' hy' h κ S' hS'
    · exact hR E I d φ s hd hs z hzc 𝔣 Λ hb hΛ l hl Q hQ hQl y' hy' h κ S' hS'

  have hterm : ∀ χ' : HChar E, HasInf χ' φ (fun i => (κ i : ℤ) + s) → (∀ u ∈ hatOUnits c, finPart χ' u = 1) →
      ∀ (y : (Af E)ˣ) (S : ℂ → ℂ), IsLatSum φ (2 * s) κ (lattice c y) S →
      ∃ u w : ℂ, IntAt l u ∧ ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (w ^ 12) ∧
        x (((finPart χ' y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0) = u * w := by
    intro χ' hinf' htriv' y S hS
    obtain ⟨y', hy', S', hS', u, hu, e⟩ := classTerm_rep hφ hc hinf' htriv' hl hex y S hS
    exact ⟨u, x (S' 0), hu, hlat y' hy' S' hS', by rw [e, hxmul]⟩
  refine ⟨fun y T ⟨S, hS, hT⟩ => ?_, fun ψ T hψ ⟨hfin, S, hS, hT⟩ => ?_⟩
  · obtain ⟨u, w, hu, hw, e⟩ := hterm χ hχ.2.2.1 htriv y S hS
    have := GlobalTheory.T.powerValuationLowerBound_sum_pow_twelve l hl (betaBound_vp d s κ 𝔣 z l) Unit (fun _ => u) (fun _ => w) (fun _ => hu) (fun _ => hw)
    rw [hx, hT, e]
    simpa using this
  · have hinf' : HasInf (χ * ψ) φ (fun i => (κ i : ℤ) + s) := hχ.2.2.1.mul_triv hψ.1
    have htriv' : ∀ u ∈ hatOUnits c, finPart (χ * ψ) u = 1 := fun u hu => by
      show finPart χ u * finPart ψ u = 1
      rw [htriv u hu, hψ.2 u hu, one_mul]
    have := Fintype.ofFinite (PicO c)
    choose u w hu hw e using fun q : PicO c => hterm (χ * ψ) hinf' htriv' q.out (S q) (hS q)
    have key := GlobalTheory.T.powerValuationLowerBound_sum_pow_twelve l hl (betaBound_vp d s κ 𝔣 z l) (PicO c) u w hu hw
    rw [hx, hT, finsum_eq_sum_of_fintype]
    have : x (∑ q, ((finPart (χ * ψ) q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * S q 0) = ∑ q, u q * w q := by
      rw [← Finset.sum_congr rfl fun q _ => e q]
      simp only [hxdef, Finset.mul_sum, Finset.sum_div]
    rw [this]
    exact key

end GlobalTheory.ToricDenomRow
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DepthDegree

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth GlobalTheory.LawLog GlobalTheory.FactorDepth GlobalTheory.DepthField

variable {C : Type} [Field C]

theorem le_order_subst_monomial {σ τ : Type} {E : σ → MvPowerSeries τ C} (hE : HasSubst E)
    (h0 : ∀ s, constantCoeff (E s) = 0) (β : σ →₀ ℕ) :
    (((Finsupp.degree β : ℕ)) : ℕ∞) ≤ (subst E (monomial β (1 : C))).order := by
  classical
  rw [subst_monomial hE, map_one, one_mul, Finsupp.prod]
  refine le_trans ?_ (le_order_prod _ _)
  rw [show ((β.degree : ℕ) : ℕ∞) = ∑ s ∈ β.support, ((β s : ℕ) : ℕ∞) by
    rw [Finsupp.degree_apply, Nat.cast_sum]]
  exact Finset.sum_le_sum fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (h0 s)

theorem derivAt0_eq_zero_of_lt_order {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C)
    (h : (P.totalDegree : ℕ∞) < g.order) : derivAt0 P g = 0 := by
  refine Finset.sum_eq_zero fun α hα => ?_
  have h1 : (((Finsupp.degree α : ℕ)) : ℕ∞) < g.order := by
    refine lt_of_le_of_lt ?_ h
    exact_mod_cast (MvPolynomial.le_totalDegree hα)
  rw [coeff_of_lt_order h1, mul_zero]

theorem depth_eq_iInf_monomial_degree_le : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (P : MvPolynomial (Σ b, ι b) C), depth G u P = ⨅ β ∈ {β : (Σ b, Fin (d b)) →₀ ℕ | β.degree ≤ P.totalDegree}, toE (v (derivAt0 P (subst (expAlong G u) (monomial β (1 : C))))) := by
  intro C _ _ v κ _ _ d G ι _ _ u P
  rw [depth_eq_iInf_monomial]
  refine le_antisymm (le_iInf₂ fun β _ => iInf_le _ β) (le_iInf fun β => ?_)
  by_cases hβ : β.degree ≤ P.totalDegree
  · exact iInf₂_le β hβ
  · have h0 : ∀ x, constantCoeff (expAlong G u x) = 0 := fun x =>
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (hasSubst_lin u x.1)) (hasSubst_lin u x.1)
        ((isExp_expOf (G x.1)).1 x.2)
    have hz := derivAt0_eq_zero_of_lt_order P _ (lt_of_lt_of_le (by exact_mod_cast not_le.1 hβ)
      (le_order_subst_monomial (hasSubst_expAlong G u) h0 β))
    rw [hz, v.map_zero]
    exact le_top

end GlobalTheory.DepthDegree
end
end

section

open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory

theorem cent_subset_KG_of_regSS {n : ℕ} {ε : Fin n → Bool} {k : UJ ε} (hk : k ∈ KG ε)
    (hr : IsRegSS (ujMat ε k)) : (cent k : Set (UJ ε)) ⊆ (KG ε : Set (UJ ε)) := by
  intro g hg
  have hg' : g * k = k * g := mem_cent.1 hg
  have h1 : ujMat ε g * ujMat ε k = ujMat ε k * ujMat ε g := by
    rw [← map_mul, ← map_mul, hg']
  have h2 : Jm ε * ujMat ε k = ujMat ε k * Jm ε := hk.2.symm
  have hJ : ujMat ε g * Jm ε = Jm ε * ujMat ε g := hr.commute h1 h2
  have hU : (ujMat ε g)ᴴ * Jm ε * ujMat ε g = Jm ε := g.2
  have hJJ := Formalism.REAL.Jm_mul_self ε
  refine ⟨?_, hJ⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  change (ujMat ε g)ᴴ * ujMat ε g = 1
  calc (ujMat ε g)ᴴ * ujMat ε g = (ujMat ε g)ᴴ * (Jm ε * Jm ε) * ujMat ε g := by rw [hJJ, Matrix.mul_one]
    _ = ((ujMat ε g)ᴴ * Jm ε * ujMat ε g) * Jm ε := by
        rw [Matrix.mul_assoc (ujMat ε g)ᴴ (Jm ε * Jm ε), Matrix.mul_assoc (Jm ε), ← hJ]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU, hJJ]

theorem isCompact_cent_of_mem_KG : ∀ (n : ℕ) (ε : Fin n → Bool) (k : UJ ε), k ∈ KG ε → IsRegSS (ujMat ε k) →
    IsCompact (cent k : Set (UJ ε)) := by
  intro n ε k hk hr
  have hK : IsCompact (KG ε : Set (UJ ε)) := by
    simpa [Subtype.range_coe] using (isCompact_univ (X := KG ε)).image continuous_subtype_val
  exact hK.of_isClosed_subset (isClosed_cent k) (cent_subset_KG_of_regSS hk hr)

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.unitary_cuspidal_satake_parameter_star_eq_inv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ), (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) → (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) → (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) → ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w (π.locRep w) B → B.map star = B.map (·⁻¹) := by
  first | exact @GlobalTheory.CuspRep.UnitaryParam.map_star_eq_map_inv_of_form | exact GlobalTheory.CuspRep.UnitaryParam.map_star_eq_map_inv_of_form | (intros; apply GlobalTheory.CuspRep.UnitaryParam.map_star_eq_map_inv_of_form <;> assumption)
end
