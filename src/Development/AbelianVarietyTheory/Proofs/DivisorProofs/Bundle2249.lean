module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle011
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.derivative_basePullback_eq_zero_along_verticalDeformation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.Opens) (W : (Y₀ TF.X Z).Opens) (hW : W ≤ toBase TF Z ⁻¹ᵁ U) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (N' : GlobalTheory.FlagTan.FIx Dw → K) (w : FrPt Xo c (DualNumber K)) (zw : Sp (DualNumber K) ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W), IsVert P N' w → zw ≫ inc₀ TF.X Z = TF.X.ptY w → ∀ r, (ev zw W hzw (((toBase TF Z).appLE U W hW).hom r)).snd = 0 := by
  first | exact @GlobalTheory.LogPole.snd_ev_toBase_of_isVert | exact GlobalTheory.LogPole.snd_ev_toBase_of_isVert | (intros; apply GlobalTheory.LogPole.snd_ev_toBase_of_isVert <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.exists_semiAbelian_pullback_framed_tangent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1), IsBaseFrame TF U e v P hU → ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → GlobalTheory.DeRham.epsRed K ≫ y' = frX P → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G P.x π → IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' → i ≫ π' = π → (∀ σ k, (ub σ k).left ≫ π = P.u σ k) → ∃ (ι : A.left ⟶ TF.Y.t.G.left) (ι' : A'.left ⟶ TF.Y.t.G.left), IsGrpPullback A TF.Y.t.G (frX P ≫ TF.Y.j) ι ∧ IsGrpPullback A' TF.Y.t.G (y' ≫ TF.Y.j) ι' ∧ i ≫ ι' = ι ∧ (∀ σ k, (ub σ k).left ≫ ι = spMap (dualMap (ev (frX P ≫ TF.Y.j) U.1 hU)) ≫ v (e ⟨σ, k⟩)) ∧ LBIso (TF.Y.t.PP.L.pull ι) (Xo.univ.t.PP.L.pull π) ∧ ⨆ k, (Xo.univ.t.PP.L.pull π).U k = ⊤ := by
  first | exact @GlobalTheory.FramedTransport.exists_model_pullback | exact GlobalTheory.FramedTransport.exists_model_pullback | (intros; apply GlobalTheory.FramedTransport.exists_model_pullback <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.framedPointVectors_verticalDeformation_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (K : Type) [Field K] [Algebra c.F K] (P₀ P : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1) (G : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K), GlobalTheory.Frames.FrChg G 1 P₀ P → IsBaseFrame TF U e v P₀ hU → ∀ (N' : GlobalTheory.FlagTan.FIx Dw → K) (w : FrPt Xo c (DualNumber K)) (x : Sp (DualNumber K) ⟶ TF.Y.X) (hx : frX w ≫ TF.Y.j = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1) (M : GlobalTheory.Reg.MChart TF.Y) (hM : ⊤ ≤ x ⁻¹ᵁ M.U), IsVert P N' w → ∀ σ i, IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) (fun j => (GlobalTheory.FlagTan.unip K N' σ * (G σ).map (fun r => (TrivSqZeroExt.inl r : DualNumber K))) i j) (tv (frVec TF.Y w hx σ i)).left := by
  first | exact @GlobalTheory.LogPole.frVec_isVert_isCombAtG | exact GlobalTheory.LogPole.frVec_isVert_isCombAtG | (intros; apply GlobalTheory.LogPole.frVec_isVert_isCombAtG <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.bigCell_eigenbasisCombination_coeff_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (S : Type) [CommRing S] (zw : Sp S ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W) (x : Sp S ⟶ TF.Y.X) (hx : zw ≫ toBase TF Z = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1) (σ : E →+* ℂ) (a b : Fin (Dw.mult σ) → S) (w' : Sp (DualNumber S) ⟶ TF.Y.t.G.left), IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) a w' → IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) b w' → a = b := by
  first | exact @GlobalTheory.LogPole.cell_eigComb_coeff_unique | exact GlobalTheory.LogPole.cell_eigComb_coeff_unique | (intros; apply GlobalTheory.LogPole.cell_eigComb_coeff_unique <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.bigCell_framedPointVectors_lowerTriangular_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (S : Type) [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (zw : Sp S ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W) (x : Sp S ⟶ TF.Y.X) (hx : frX w ≫ TF.Y.j = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1), zw ≫ inc₀ TF.X Z = TF.X.ptY w → ∃ B : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, (∀ σ i j, i < j → B σ i j = 0) ∧ (∀ σ i, IsUnit (B σ i i)) ∧ ∀ σ i, IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) (fun j => (B σ * (L σ * N σ).map (ev zw W hzw)) i j) (tv (frVec TF.Y w hx σ i)).left := by
  first | exact @GlobalTheory.LogPole.frVec_cell_comb | exact GlobalTheory.LogPole.frVec_cell_comb | (intros; apply GlobalTheory.LogPole.frVec_cell_comb <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.exists_bigCell_framedPoints_triangular_frameChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (K : Type) [Field K] [Algebra c.F K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (Q : FrPt Xo c K), TF.X.F.ChartFr k (z ≫ inc₀ TF.X Z) hk Q → ∃ (P₀ P : FrPt Xo c K) (t : Ix Dw → Kˣ) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), FrBor t Q P ∧ (∀ σ i, (t (some ⟨σ, i⟩) : K) * ev z W hz (L σ i i) = 1) ∧ GlobalTheory.Frames.FrChg (fun σ => (N σ).map (ev z W hz)) 1 P₀ P ∧ IsBaseFrame TF U e v P₀ hU := by
  first | exact @GlobalTheory.LogPole.exists_cellFrames | exact GlobalTheory.LogPole.exists_cellFrames | (intros; apply GlobalTheory.LogPole.exists_cellFrames <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical


theorem _root_.GlobalTheory.T.bigCell_point_eq_of_base_and_cellCoordinates_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N) (S : Type) [CommRing S] (z₁ z₂ : Sp S ⟶ Y₀ TF.X Z) (h₁ : ⊤ ≤ z₁ ⁻¹ᵁ W) (h₂ : ⊤ ≤ z₂ ⁻¹ᵁ W), ⊤ ≤ z₁ ⁻¹ᵁ U₀ TF.X Z → ⊤ ≤ z₂ ⁻¹ᵁ U₀ TF.X Z → (∀ r, ev z₁ W h₁ (((toBase TF Z).appLE U.1 W h.2.1).hom r) = ev z₂ W h₂ (((toBase TF Z).appLE U.1 W h.2.1).hom r)) → (∀ i, ev z₁ W h₁ (cellCoord N i) = ev z₂ W h₂ (cellCoord N i)) → z₁ = z₂ := by
  first | exact @GlobalTheory.LogPole.eq_of_cellCoord_eq | exact GlobalTheory.LogPole.eq_of_cellCoord_eq | (intros; apply GlobalTheory.LogPole.eq_of_cellCoord_eq <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical


theorem _root_.GlobalTheory.T.locallyQuasiFinite_bigCell_to_base_prod_affineSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)))) := by
  first | exact @GlobalTheory.LogPole.locallyQuasiFinite_cellMap | exact GlobalTheory.LogPole.locallyQuasiFinite_cellMap | (intros; apply GlobalTheory.LogPole.locallyQuasiFinite_cellMap <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm

theorem _root_.GlobalTheory.T.exists_squareBundle_descent_of_defect_killed : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ) (u : Γ(pullback f f, ⊤)ˣ), DescCompat f M φ → Defect f M φ D → KillsSq f D u → ∃ (M₂ : LB X) (ψ : ∀ i j, Γ(pullback f f, chart f M₂ i j)ˣ), M₂.IsLB ∧ LBIso (lbPow M 2) M₂ ∧ DescCompat f M₂ ψ ∧ DescCocycle f M₂ ψ := by
  first | exact @GlobalTheory.SqDatum.exists_sq_descent | exact GlobalTheory.SqDatum.exists_sq_descent | (intros; apply GlobalTheory.SqDatum.exists_sq_descent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

theorem _root_.GlobalTheory.T.mumfordBundleRoot_exists_over_fg_subalgebra : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → ∀ (k : Type) [Field k] (t : Sp k ⟶ S) (C : Type) [CommRing C] [Algebra k C], Root A P (spMap (algebraMap k C) ≫ t) → ∃ B : Subalgebra k C, B.FG ∧ Root A P (spMap (algebraMap k B) ≫ t) := by
  first | exact @GlobalTheory.RootFG.root_fg | exact GlobalTheory.RootFG.root_fg | (intros; apply GlobalTheory.RootFG.root_fg <;> assumption)
end

section

open NumberField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM GlobalTheory.CM.IntCoord

set_option autoImplicit false

namespace GlobalTheory.FlatCM.HomLat

theorem sum_smul_diff_mem_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0), ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ e ∈ FP.eigLat (X.A true).t.act τ,
            ∑ a, τE (c a) • MP a e ∈ FB.eigLat X.B.t.act τ := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X FP FB MP hMP τ _ τE hτE c hc e he
  obtain ⟨n, hn, x, hx, f, hf, hfn⟩ := hc
  have hcA := integral_tangent_coordinates K _ FP
  have hcB := integral_tangent_coordinates K _ FB
  obtain ⟨u, hu, heig⟩ := (hcA.2.2.2.2.2 _ _ τ e).1 he
  have := hf.isMonHom
  have ht : IsTangent (u ≫ f) := by
    have hv := hu.1
    unfold IsTangent at hv ⊢
    rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨d, hd, -⟩ := hcB.1 _ ht
  have hs : ∀ a, FB.IsCoord (u ≫ ((X.A true).t.act.act (x a) ≫ phiP X a)) (MP a (τ (x a) • e)) := by
    intro a
    rw [← Category.assoc]
    exact hMP a _ _ (isCoord_smul FP hu (heig (x a)))
  have hprod : ∀ s : Finset (Fin p), FB.IsCoord (u ≫ ∏ a ∈ s, ((X.A true).t.act.act (x a) ≫ phiP X a))
      (∑ a ∈ s, MP a (τ (x a) • e)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, comp_one]
      exact isCoord_one FB
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, comp_mul]
      exact isCoord_mul FB (hs a) ih
  have hpow : ∀ m : ℕ, FB.IsCoord ((u ≫ f) ^ m) (m • d) := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, zero_smul]
      exact isCoord_one FB
    | succ m ih =>
      rw [pow_succ, succ_nsmul]
      exact isCoord_mul FB ih hd
  have heq : n • d = ∑ a, MP a (τ (x a) • e) := by
    have h1 := hpow n
    rw [← comp_pow, hfn] at h1
    exact (hcB.1 _ h1.1).unique h1 (hprod Finset.univ)
  have hdval : d = ∑ a, τE (c a) • MP a e := by
    have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    refine smul_right_injective _ hn0 ?_
    show (n : K) • d = (n : K) • ∑ a, τE (c a) • MP a e
    rw [Nat.cast_smul_eq_nsmul, heq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul K (τ (x a)) e, map_smul, smul_smul]
    congr 1
    show ((τ (x a) : 𝓞 K) : K) = (n : K) * τE (c a)
    rw [← hτE, hx a, map_mul, map_natCast]
  rw [← hdval]
  refine (hcB.2.2.2.2.2 _ _ τ _).2 ⟨u ≫ f, hd, fun s => ?_⟩
  rw [isLieComb_one_iff, Category.assoc, ← hf.comm s, ← Category.assoc, (isLieComb_one_iff _ _ _).1 (heig s),
    Category.assoc]

end GlobalTheory.FlatCM.HomLat
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.TorusTateLie
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PointMap

section General

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P P' : Point p v O Λ}
  (α : P.A.A ⟶ P'.A.A) [IsMonHom α]

section Lattices

variable [Algebra ℤ_[p] C]

variable [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C]

end Lattices

variable [IsAlgClosed C] [CharZero C]

theorem pairV_mapV [Algebra ℤ_[p] C] (x : P.V) (y : P'.V) :
    P'.pairV (mapV P P' α x) y = P.pairV x (adjV P P' α y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, hx, hx']
  | tmul c s =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add (f := _), hy, hy']
    | tmul d t => exact congrArg (· • (c * d)) (pairT_mapT P P' α s t)

theorem weil_adjT (he : P'.eps = P.eps) (t : P'.T) {n : ℕ} {z : ChTor.Pts P.A.A} (hz : z ^ p ^ n = 1) :
    weil P'.A (p ^ n) (z ≫ α) (t.lev n) = weil P.A (p ^ n) z ((adjT P P' α t).lev n) := by
  obtain ⟨s, rfl⟩ := (tate_free_of_card p _ _ P.card_torsion).2.1 n z hz
  rw [← pow_pairT P.A P.eps, ← pairT_mapT, ← he, pow_pairT, lev_mapT]

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  (β : P.Gt ⟶ P'.Gt) [IsMonHom β] (he : P'.eps = P.eps) (hβ : ∀ x, P'.toA (x ≫ β) = P.toA x ≫ α)

include he hβ

theorem weilChar_adjT (t : P'.T) (n : ℕ) : (P.weilChar (adjT P P' α t)).χ n =
    ExtensionTorsion.torsionHom β (p ^ n) ≫ (P'.weilChar t).χ n := P.char_ext fun w => by
  rw [← Category.assoc, P.isWeilChar_weilChar, P'.isWeilChar_weilChar, Category.assoc,
    ExtensionTorsion.torsionHom_ι, ← Category.assoc, hβ, weil_adjT α he t (P.toA_pow w)]

variable [Algebra ℤ_[p] O]

theorem al₀_adjT (t : P'.T) (x : LieG P.Gt) :
    (P.al₀ (adjT P P' α t)).1 x = (P'.al₀ t).1 (lieMap β x) := by
  refine HodgeTateImage.eq_of_forall (p := p) fun n => ?_
  have hR := HodgeTateImage.pow_quot (O := O) (p := p) n
  have h1 := isAl_dlogTv (P.weilChar (adjT P P' α t)) n _ hR x _ (HodgeTateImage.lift_ι hR x)
  have h2 := isAl_dlogTv (P'.weilChar t) n _ hR (lieMap β x)
    (HodgeTateImage.lift hR x ≫ ExtensionTorsion.torsionHom β (p ^ n)) (by
      rw [Category.assoc, ExtensionTorsion.torsionHom_ι, ← Category.assoc, HodgeTateImage.lift_ι]
      exact Category.assoc _ _ _)
  rw [Category.assoc, ← weilChar_adjT α β he hβ, h1] at h2
  change algebraMap O _ ((dlogTv (P.weilChar (adjT P P' α t))).1 x) =
    algebraMap O _ ((dlogTv (P'.weilChar t)).1 (lieMap β x))
  simpa [Algebra.algebraMap_eq_smul_one] using congrArg TrivSqZeroExt.snd h2

variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

theorem mapV_bLie (x : LieG P.Gt) : mapV P P' α (P.bLie x) = P'.bLie (lieMap β x) :=
  P'.eq_of_pairV fun t => by
    rw [pairV_mapV, adjV_tmul, Point.pairV_bLie, Point.pairV_bLie, al₀_adjT α β he hβ]

end General

section Good

variable {Λ : Type} [CommRing Λ] [StarRing Λ] {p : ℕ} [Fact p.Prime] {C : Type} [Field C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) (ε : Eps p C) {R : Type}
  [CommRing R] (j : R →+* O) {B B' B'' : Out.PolAV (Sp R)} (o : B.OAct Λ) (o' : B'.OAct Λ) (o'' : B''.OAct Λ)

theorem homT_act (a : Λ) [IsMonHom (o.act a)] : homT hv ε j o o (o.act a) = (goodPoint hv ε j B o).actT a :=
  LinearMap.ext fun t => Tate.ext fun n => congrArg (t.lev n ≫ ·) (goodPoint_oA hv ε j o a).symm

theorem homT_id : homT hv ε j o o (𝟙 B.A) = LinearMap.id :=
  LinearMap.ext fun t => Tate.ext fun n =>
    (congrArg (t.lev n ≫ ·) ((congrArg _ ((Over.pullback _).map_id _)).trans ((Over.pullback _).map_id _))).trans
      (Category.comp_id _)

section Linear

variable {f : B.A ⟶ B'.A} [IsMonHom f]

variable [Algebra ℤ_[p] C]

variable [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C]

end Linear

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem toG_goodPoint (x : specO O O ⟶ (goodPoint hv ε j B o).Gt) : (goodPoint hv ε j B o).toG x = x :=
  (goodPoint hv ε j B o).hom_ext_red fun m => (goodPoint hv ε j B o).red_toG x m

theorem toA_homO (f : B.A ⟶ B'.A) (x : specO O O ⟶ (goodPoint hv ε j B o).Gt) :
    (goodPoint hv ε j B' o').toA (x ≫ homO hv ε j o o' f) = (goodPoint hv ε j B o).toA x ≫ homC hv ε j o o' f := by
  have h1 := ((goodPoint hv ε j B o).eq_toA_iff x _).1 rfl
  have h2 : (homC hv ε j o o' f).left ≫ (goodPoint hv ε j B' o').gen =
      (goodPoint hv ε j B o).gen ≫ (homO hv ε j o o' f).left := pullback.lift_fst _ _ _
  rw [toG_goodPoint] at h1
  symm
  rw [Point.eq_toA_iff, toG_goodPoint, Over.comp_left, Category.assoc, h2]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (homO hv ε j o o' f).left) h1).trans (Category.assoc _ _ _))

variable [IsAlgClosed C] [CharZero C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

theorem homV_bLie (f : B.A ⟶ B'.A) [IsMonHom f] (x : LieG (goodPoint hv ε j B o).Gt) :
    homV hv ε j o o' f ((goodPoint hv ε j B o).bLie x) = (goodPoint hv ε j B' o').bLie (homLie hv ε j o o' f x) :=
  mapV_bLie _ (homO hv ε j o o' f) rfl (toA_homO hv ε j o o' f) x

variable {f : B.A ⟶ B'.A} [IsMonHom f]


end Good

section Triples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] {ℓ : ℕ} [Fact ℓ.Prime]
  {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O)
  (ε : Eps ℓ C) (i : K →+* C) {T T' : PAT H (Sp (𝓞 K))} {f g : T.t.G ⟶ T'.t.G}
  (hf : Serre.IsLinearHom T.t.act T'.t.act f) (hg : Serre.IsLinearHom T.t.act T'.t.act g)

variable [Algebra ℤ_[ℓ] C]

variable [Algebra ℤ_[ℓ] O] [IsScalarTower ℤ_[ℓ] O C]

variable [Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [IsAlgClosed C] [CharZero C]

theorem patV_bLie : letI := H.starRing
    ∀ x, patV hv ε i hf ((patPoint hv ε i T).bLie x) = (patPoint hv ε i T').bLie (patLie hv ε i hf x) :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  homV_bLie (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') f

end Triples

end GlobalTheory.PointMap
end
end
