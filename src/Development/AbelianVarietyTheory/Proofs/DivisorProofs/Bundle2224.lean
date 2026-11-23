module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle109
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle065
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle207
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole.CellQF

open GlobalTheory.FlagMod (initSpan initSpan_le_of_tri)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM)

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

section Lin

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {m : ℕ}

theorem initSpan_eq_of_lower {v v' : Fin m → M} (L : Matrix (Fin m) (Fin m) R)
    (hL : ∀ i j, i < j → L i j = 0) (hd : ∀ i, IsUnit (L i i))
    (h : ∀ i, v' i = ∑ j, L i j • v j) (i : ℕ) : initSpan R v' i = initSpan R v i := by
  have ht : L.IsLowerTriangular := fun a b hab => hL a b hab
  have hdet : IsUnit L.det := by
    rw [Matrix.det_of_lowerTriangular L ht]
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun a _ => hd a)
  haveI : Invertible L := Matrix.invertibleOfIsUnitDet L hdet
  have hti : L⁻¹.BlockTriangular OrderDual.toDual := Matrix.blockTriangular_inv_of_blockTriangular ht
  have hinv : ∀ a, v a = ∑ j, L⁻¹ a j • v' j := fun a => by
    simp only [h, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul L hdet, Matrix.one_apply]
    simp
  refine le_antisymm (initSpan_le_of_tri (B := L.transpose) (fun a b hab => hL b a hab) h i)
    (initSpan_le_of_tri (B := (L⁻¹).transpose) (fun a b hab => hti hab) hinv i)

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def baseVec (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (hv : ∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) {K : Type} [CommRing K] (x : Sp K ⟶ TF.Y.X)
    (hU : ⊤ ≤ x ⁻¹ᵁ U.1) (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) : TanM x TF.Y.t.G :=
  LieMet.tanOf (v := spMap (dualMap (ev x U.1 hU)) ≫ v (e ⟨σ, j⟩)) (by
    have := GlobalTheory.FactorDepth.isTanAtG_map TF.Y.t (ev x U.1 hU) (hv (e ⟨σ, j⟩))
    unfold LogKS.chart at this
    rwa [GlobalTheory.FlagMod.spMap_ev x U.2 hU] at this)

theorem vecAt_eq_sum (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (hv : ∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J)
    (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W))
    (h : IsCell TF Z U e v W k L N) {K : Type} [CommRing K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W)
    {x : Sp K ⟶ TF.Y.X} (ex : z ≫ toBase TF Z = x) (hU : ⊤ ≤ x ⁻¹ᵁ U.1)
    (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = x)
    (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i =
      ∑ j, ev z W hz ((L σ * N σ) i j) • baseVec TF U e v hv x hU σ j := by
  subst ex
  have hc := h.2.2.2.2.2.2.2 K z hz hU hk hx σ i
  exact (LieMet.isComb_iff (fun j => baseVec TF U e v hv _ hU σ j)
    (fun j => ev z W hz ((L σ * N σ) i j)) _).1 hc

theorem step_eq_cell (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (hv : ∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J)
    (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W))
    (h : IsCell TF Z U e v W k L N) {K : Type} [CommRing K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W)
    {x : Sp K ⟶ TF.Y.X} (ex : z ≫ toBase TF Z = x) (hU : ⊤ ≤ x ⁻¹ᵁ U.1)
    (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = x) (σ : E →+* ℂ) (i : ℕ) :
    TF.X.F.step (z ≫ inc₀ TF.X Z) hx σ i =
      initSpan K (fun a => ∑ j, ev z W hz (N σ a j) • baseVec TF U e v hv x hU σ j) i := by
  have hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_map (inc₀ TF.X Z) h.2.2.1 hz
  rw [TF.X.F.step_eq k _ hk hx]
  refine initSpan_eq_of_lower (fun a b => ev z W hz (L σ a b))
    (fun a b hab => by rw [h.2.2.2.1 σ a b hab, map_zero]) (fun a => (h.2.2.2.2.1 σ a).map _) (fun a => ?_) i
  rw [vecAt_eq_sum TF Z U e v hv W k L N h z hz ex hU hk hx σ a]

  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

end GlobalTheory.LogPole.CellQF

namespace GlobalTheory.LogPole.CellQF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem locallyOfFiniteType_cell (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J)
    (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W))
    (h : IsCell TF Z U e v W k L N) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)))) := by
  have hπ : LocallyOfFiniteType (toBase TF Z) := by
    have : IsProper TF.X.π := TF.X.proper
    infer_instance
  have h1 := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (toBase TF Z) hπ U ⟨W, h.1⟩ h.2.1
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  refine RingHom.FiniteType.of_comp_finiteType
    (f := (MvPolynomial.C : Γ(TF.Y.X, U.1) →+* MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))) ?_
  rw [CommRingCat.hom_ofHom, MvPolynomial.eval₂Hom_comp_C]
  exact h1

end GlobalTheory.LogPole.CellQF



open GlobalTheory.LogPole.CellQF in
theorem GlobalTheory.LogPole.locallyQuasiFinite_cellMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)))) := by
  intro E _ _ _ H Dw l Xo c TF Z _ U n e v hv W k L N h
  haveI := locallyOfFiniteType_cell TF Z U e v W k L N h
  refine GlobalTheory.locallyQuasiFinite_of_finite_geometric_points _ fun Ω _ _ y => ?_
  have hfs : IsOpenImmersion h.1.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec h.1
  have hzW : ∀ x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W), ⊤ ≤ (x ≫ h.1.fromSpec) ⁻¹ᵁ W :=
    fun x => GlobalTheory.FlagMod.le_preimage_comp x (GlobalTheory.FlagMod.tau_le h.1 le_rfl)
  have hsp : ∀ x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W),
      spMap (ev (x ≫ h.1.fromSpec) W (hzW x)) = x := fun x => by
    rw [← cancel_mono h.1.fromSpec]
    exact GlobalTheory.FlagMod.spMap_ev _ h.1 _
  have hy : ∀ x : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y},
      spMap ((ev (x.1 ≫ h.1.fromSpec) W (hzW x.1)).comp
        (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y := fun x => by
    rw [← spMap_comp', hsp]
    exact x.2
  have hρ : ∀ x x' : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y},
      (ev (x.1 ≫ h.1.fromSpec) W (hzW x.1)).comp
        (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)) =
      (ev (x'.1 ≫ h.1.fromSpec) W (hzW x'.1)).comp
        (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)) := fun x x' =>
    congrArg CommRingCat.Hom.hom (Spec.map_injective ((hy x).trans (hy x').symm))
  have hN : ∀ x x' : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y}, ∀ σ a b,
      ev (x.1 ≫ h.1.fromSpec) W (hzW x.1) (N σ a b) = ev (x'.1 ≫ h.1.fromSpec) W (hzW x'.1) (N σ a b) := by
    intro x x' σ a b
    rcases lt_trichotomy a b with hab | rfl | hab
    · have e1 : N σ a b = MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)
          (MvPolynomial.X ⟨σ, ⟨(a, b), hab⟩⟩) := by
        rw [MvPolynomial.eval₂Hom_X']; rfl
      rw [e1]
      exact congrArg (fun f => f (MvPolynomial.X ⟨σ, ⟨(a, b), hab⟩⟩)) (hρ x x')
    · rw [h.2.2.2.2.2.2.1 σ a, map_one, map_one]
    · rw [h.2.2.2.2.2.1 σ a b hab]
      exact (RingHom.map_zero _).trans (RingHom.map_zero _).symm
  have hUx : ∀ x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W),
      ⊤ ≤ ((x ≫ h.1.fromSpec) ≫ toBase TF Z) ⁻¹ᵁ U.1 :=
    fun x => GlobalTheory.FlagMod.le_preimage_map (toBase TF Z) h.2.1 (hzW x)
  have hev : ∀ x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W),
      ev ((x ≫ h.1.fromSpec) ≫ toBase TF Z) U.1 (hUx x) = ((ev (x ≫ h.1.fromSpec) W (hzW x)).comp
        (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))).comp MvPolynomial.C :=
    fun x => by
    ext r
    rw [← GlobalTheory.FlagMod.ev_appLE _ _ h.2.1 (hzW x)]
    simp
  have hB : ∀ x x' : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y},
      (x.1 ≫ h.1.fromSpec) ≫ toBase TF Z = (x'.1 ≫ h.1.fromSpec) ≫ toBase TF Z := fun x x' => by
    refine (GlobalTheory.FlagMod.spMap_ev _ U.2 (hUx x.1)).symm.trans (Eq.trans ?_ (GlobalTheory.FlagMod.spMap_ev _ U.2 (hUx x'.1)))
    rw [hev x.1, hev x'.1, hρ x x']
  rcases isEmpty_or_nonempty {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map
      (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y}
    with h0 | hne
  · exact @Finite.of_subsingleton _ ⟨fun a => (h0.false a).elim⟩
  obtain ⟨x₀⟩ := hne
  have ex₀ : (x₀.1 ≫ h.1.fromSpec) ≫ toBase TF Z = ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π :=
    (Category.assoc _ _ _).symm
  have hU0 : ⊤ ≤ (((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π) ⁻¹ᵁ U.1 := by
    rw [← ex₀]; exact hUx x₀.1
  have hfin := TF.flag.fin Ω ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z)
  have key : ∀ x : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y},
      ∃ hx : ((x.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π,
      ∀ (σ : E →+* ℂ) (i : ℕ), TF.X.F.step ((x.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) hx σ i =
        TF.X.F.step ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) rfl σ i := fun x => by
    have ex : (x.1 ≫ h.1.fromSpec) ≫ toBase TF Z = ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π :=
      (hB x x₀).trans ex₀
    have hx : ((x.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π :=
      (Category.assoc _ _ _).trans ex
    refine ⟨hx, fun σ i => ?_⟩
    refine (step_eq_cell TF Z U e v hv.1 W k L N h _ (hzW x.1) ex hU0 hx σ i).trans ?_
    refine Eq.trans ?_ (step_eq_cell TF Z U e v hv.1 W k L N h _ (hzW x₀.1) ex₀ hU0 rfl σ i).symm
    simp only [hN x x₀]
  have hinj : Function.Injective
      (fun x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) => (x ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) :=
    fun a b hab => (cancel_mono h.1.fromSpec).1 ((cancel_mono (inc₀ TF.X Z)).1 hab)
  have hS : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) | x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y}.Finite :=
    (hfin.preimage hinj.injOn).subset fun x hx => key ⟨x, hx⟩
  exact hS.to_subtype
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

noncomputable section

open GlobalTheory

namespace GlobalTheory.RootFG

theorem lbIso_of_factor {Y Y' X₀ : Scheme.{0}} {M N : LB X₀} (a : Y ⟶ X₀) (j : Y' ⟶ Y) (a' : Y' ⟶ X₀)
    (e : a' = j ≫ a) (h : LBIso (M.pull a) (N.pull a)) : LBIso (M.pull a') (N.pull a') :=
  LBIso.chartPull (chartPullSame M _ _ _ j fun _ => e) (chartPullSame N _ _ _ j fun _ => e) h

theorem exists_fg_lbIso_of_isPullback {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C] {X : Scheme.{0}}
    (pB : X ⟶ Sp k) [QuasiCompact pB] [QuasiSeparated pB] {R₀ : Subalgebra k C} (h₀ : R₀.FG) {Y₀ Y : Scheme.{0}}
    (q₀ : Y₀ ⟶ Sp R₀) (a₀ : Y₀ ⟶ X) (hY₀ : IsPullback a₀ q₀ pB (spMap (algebraMap k R₀)))
    (y : Y ⟶ Y₀) (q : Y ⟶ Sp C) (hY : IsPullback y q q₀ (spMap R₀.val.toRingHom))
    (M N : LB Y₀) (hM : M.IsLB) (hN : N.IsLB) (H : LBIso (M.pull y) (N.pull y)) :
    ∃ (R : Subalgebra k C) (hR : R₀ ≤ R), R.FG ∧ ∀ (Y₁ : Scheme.{0}) (q₁ : Y₁ ⟶ Sp R) (y₁ : Y₁ ⟶ Y₀),
      y₁ ≫ q₀ = q₁ ≫ spMap (Subalgebra.inclusion hR).toRingHom → LBIso (M.pull y₁) (N.pull y₁) := by
  let e : pullback pB (spMap (algebraMap k R₀)) ⟶ Y₀ :=
    hY₀.lift (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  have e₁ : e ≫ a₀ = pullback.fst _ _ := hY₀.lift_fst _ _ _
  have e₂ : e ≫ q₀ = pullback.snd _ _ := hY₀.lift_snd _ _ _
  let f : pullback pB (spMap (algebraMap k C)) ⟶ Y :=
    hY.lift (baseChangeMap pB R₀.val ≫ e) (pullback.snd _ _) (by
      rw [Category.assoc, e₂, baseChangeMap_snd])
  have hf : f ≫ y = baseChangeMap pB R₀.val ≫ e := hY.lift_fst _ _ _
  have H₀ : LBIso ((M.pull e).pull (baseChangeMap pB R₀.val)) ((N.pull e).pull (baseChangeMap pB R₀.val)) := by
    have := lbIso_of_factor y f _ hf.symm H
    exact LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) (pull_isLB (pull_isLB hN _) _)
      (Spread.lbIso_pull_pull hM _ rfl).symm
      (LBIso.trans (pull_isLB hM _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) this
        (Spread.lbIso_pull_pull hN _ rfl))
  obtain ⟨R, hR, hRfg, H₁⟩ := exists_fg_lbIso pB h₀ (M.pull e) (N.pull e) (pull_isLB hM _) (pull_isLB hN _) H₀
  refine ⟨R, hR, hRfg, fun Y₁ q₁ y₁ w => ?_⟩
  have H₂ : LBIso (M.pull (baseChangeMap pB (Subalgebra.inclusion hR) ≫ e))
      (N.pull (baseChangeMap pB (Subalgebra.inclusion hR) ≫ e)) :=
    LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hN _)
      (Spread.lbIso_pull_pull hM _ rfl)
      (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hN _) H₁
        (Spread.lbIso_pull_pull hN _ rfl).symm)
  have hs : spMap (Subalgebra.inclusion hR).toRingHom ≫ spMap (algebraMap k R₀) = spMap (algebraMap k R) := by
    rw [spMap_comp_ring]; rfl
  let m : Y₁ ⟶ pullback pB (spMap (algebraMap k R)) :=
    pullback.lift (y₁ ≫ a₀) q₁ (by rw [Category.assoc, hY₀.w, ← Category.assoc, w, Category.assoc, hs])
  refine lbIso_of_factor _ m y₁ ?_ H₂
  apply hY₀.hom_ext
  · rw [Category.assoc, Category.assoc, e₁, baseChangeMap_fst, pullback.lift_fst]
  · rw [Category.assoc, Category.assoc, e₂, baseChangeMap_snd, pullback.lift_snd_assoc, w]

end GlobalTheory.RootFG


open GlobalTheory GlobalTheory.RootFG in
theorem GlobalTheory.RootFG.root_fg : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left),
    P.IsLB → ∀ (k : Type) [Field k] (t : Sp k ⟶ S) (C : Type) [CommRing C] [Algebra k C],
    Root A P (spMap (algebraMap k C) ≫ t) → ∃ B : Subalgebra k C, B.FG ∧ Root A P (spMap (algebraMap k B) ≫ t) := by
  intro S A _ hA P hP k _ t C _ _ hRt
  obtain ⟨B', _, _, β, β₂, hβ, hsq, L, hL, H⟩ := hRt
  obtain ⟨A₀, _, φ₀, h₀⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A t
  have hA₀ : IsAbelianScheme A₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₀
  have := hA₀.proper
  have : IsProper (A₀ ⊗ A₀).hom := by
    change IsProper (pullback.fst A₀.hom A₀.hom ≫ A₀.hom)
    infer_instance

  let φ' : B'.left ⟶ A₀.left := h₀.1.lift β (B'.hom ≫ spMap (algebraMap k C)) (by rw [hβ.1.w, Category.assoc])
  have hφ'₁ : φ' ≫ φ₀ = β := h₀.1.lift_fst _ _ _
  have hφ'₂ : φ' ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k C) := h₀.1.lift_snd _ _ _
  have hB'₀ : IsGrpPullback B' A₀ (spMap (algebraMap k C)) φ' :=
    IsGrpPullback.cancel h₀ (by rw [hφ'₁]; exact hβ) hφ'₂

  obtain ⟨R₁, M, ρ, hR₁, hM, hρ₁, hρ₂, HL⟩ := GlobalTheory.LBDescent.exists_fg_lb A₀.hom B'.hom φ' hB'₀.1 L hL
  obtain ⟨B₁, _, β₁, h₁⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A₀ (spMap (algebraMap k R₁))
  have hB₁ : IsAbelianScheme B₁ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ h₁
  haveI : IsCommMonObj B₁ := hB₁.comm
  let e₁ : B₁.left ⟶ pullback A₀.hom (spMap (algebraMap k R₁)) := h₁.1.isoPullback.hom
  let L₁ : LB B₁.left := M.pull e₁
  have hL₁ : L₁.IsLB := pull_isLB hM _
  let σ : Sp C ⟶ Sp R₁ := spMap R₁.val.toRingHom
  have hσ : σ ≫ spMap (algebraMap k R₁) = spMap (algebraMap k C) := by
    rw [spMap_comp_ring]; rfl
  let ψ : B'.left ⟶ B₁.left := h₁.1.lift φ' (B'.hom ≫ σ) (by rw [hφ'₂, Category.assoc, hσ])
  have hψ₁ : ψ ≫ β₁ = φ' := h₁.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ B₁.hom = B'.hom ≫ σ := h₁.1.lift_snd _ _ _
  have hψ : IsGrpPullback B' B₁ σ ψ := IsGrpPullback.cancel h₁ (by rw [hψ₁, hσ]; exact hB'₀) hψ₂
  have hρψ : ρ = ψ ≫ e₁ := by
    apply pullback.hom_ext
    · rw [hρ₁, Category.assoc, IsPullback.isoPullback_hom_fst, hψ₁]
    · rw [hρ₂, Category.assoc, IsPullback.isoPullback_hom_snd, hψ₂]
  have HL₁ : LBIso L (L₁.pull ψ) :=
    LBIso.trans hL (pull_isLB hM _) (pull_isLB hL₁ _) HL (Spread.lbIso_pull_pull hM ψ hρψ)

  have hc : IsGrpPullback B₁ A (spMap (algebraMap k R₁) ≫ t) (β₁ ≫ φ₀) := h₁.comp h₀
  let β₂₁ := (lift (pushPt hc.1.w (fst B₁ B₁)) (pushPt hc.1.w (snd B₁ B₁))).left
  have hsq₁ : IsSquare (β₁ ≫ φ₀) β₂₁ := GlobalTheory.LamPull.exists_isSquare hc.1.w
  let V := lift (pushPt hψ.1.w (fst B' B')) (pushPt hψ.1.w (snd B' B'))
  have hsqψ : IsSquare ψ V.left := GlobalTheory.LamPull.exists_isSquare hψ.1.w
  have c₁ : LBIso (abelian₂ B' L) ((abelian₂ B₁ L₁).pull V.left) :=
    GlobalTheory.SymSpread.lbIso_cube hψ hL₁ hL HL₁ (x2 B₁) (x2 B') V (fun i => by fin_cases i <;> simp [V, x2])
  have hβ₂ : β₂ = V.left ≫ β₂₁ := by
    have h' := GlobalTheory.ZM.SiegPull.isSquare_comp hsqψ hsq₁
    have eβ : ψ ≫ β₁ ≫ φ₀ = β := by rw [← Category.assoc, hψ₁, hφ'₁]
    rw [eβ] at h'
    apply pullback.hom_ext
    · exact hsq.1.trans h'.1.symm
    · exact hsq.2.trans h'.2.symm
  have hΛ₁ : (abelian₂ B₁ L₁).IsLB := LB.isLB_linComb hL₁ _ _
  have hΛ' : (abelian₂ B' L).IsLB := LB.isLB_linComb hL _ _
  have HV : LBIso ((abelian₂ B₁ L₁).pull V.left) ((P.pull β₂₁).pull V.left) :=
    LBIso.trans (pull_isLB hΛ₁ _) hΛ' (pull_isLB (pull_isLB hP _) _) c₁.symm
      (LBIso.trans hΛ' (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) H (Spread.lbIso_pull_pull hP V.left hβ₂))

  obtain ⟨R₂, h₁₂, hR₂, HD⟩ := exists_fg_lbIso_of_isPullback (A₀ ⊗ A₀).hom hR₁ (B₁ ⊗ B₁).hom _
    (GlobalTheory.SymSpread.isPullback_square h₁) V.left (B' ⊗ B').hom (GlobalTheory.SymSpread.isPullback_square hψ)
    (abelian₂ B₁ L₁) (P.pull β₂₁) hΛ₁ (pull_isLB hP _) HV
  let τ : Sp R₂ ⟶ Sp R₁ := spMap (Subalgebra.inclusion h₁₂).toRingHom
  have hτ : τ ≫ spMap (algebraMap k R₁) = spMap (algebraMap k R₂) := by
    rw [spMap_comp_ring]; rfl
  obtain ⟨B₂, _, κ, hκ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback B₁ τ
  have hB₂ : IsAbelianScheme B₂ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB₁ hκ
  haveI : IsCommMonObj B₂ := hB₂.comm
  refine ⟨R₂, hR₂, ?_⟩
  rw [← hτ, Category.assoc]
  let W := lift (pushPt hκ.1.w (fst B₂ B₂)) (pushPt hκ.1.w (snd B₂ B₂))
  have hsqW : IsSquare κ W.left := GlobalTheory.LamPull.exists_isSquare hκ.1.w
  have hL₂ : (L₁.pull κ).IsLB := pull_isLB hL₁ κ
  refine ⟨B₂, inferInstance, inferInstance, κ ≫ β₁ ≫ φ₀, W.left ≫ β₂₁, hκ.comp hc,
    GlobalTheory.ZM.SiegPull.isSquare_comp hsqW hsq₁, L₁.pull κ, hL₂, ?_⟩
  have d₁ : LBIso (abelian₂ B₂ (L₁.pull κ)) ((abelian₂ B₁ L₁).pull W.left) :=
    GlobalTheory.SymSpread.lbIso_cube hκ hL₁ hL₂ (lbIso_refl hL₂) (x2 B₁) (x2 B₂) W (fun i => by fin_cases i <;> simp [W, x2])
  have d₂ : LBIso ((abelian₂ B₁ L₁).pull W.left) ((P.pull β₂₁).pull W.left) :=
    HD _ (B₂ ⊗ B₂).hom W.left (GlobalTheory.SymSpread.isPullback_square hκ).w
  exact LBIso.trans (LB.isLB_linComb hL₂ _ _) (pull_isLB hΛ₁ _) (pull_isLB hP _) d₁
    (LBIso.trans (pull_isLB hΛ₁ _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) d₂
      (Spread.lbIso_pull_pull hP W.left rfl).symm)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip


theorem _root_.GlobalTheory.T.mixedModel_vacuum_eq_smul_integralMatrix_indicator : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X → ∀ w ∈ locPl G t, ∀ ι : ToB G t i j w, IsMixModelB W B t e Γ w ι →
      ι (Γ.M'.vac _) = ι (Γ.M'.vac _) 0 • Set.indicator {Z | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer} 1 := by
  first | exact @GlobalTheory.TopFlip.MixVacSmall.mixVac_eq_indicator | exact GlobalTheory.TopFlip.MixVacSmall.mixVac_eq_indicator | (intros; apply GlobalTheory.TopFlip.MixVacSmall.mixVac_eq_indicator <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.affineOpen_meeting_fibres_is_nonvanishingLocus : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ c : Pic A.left, IsLocus c V := by
  first | exact @GlobalTheory.AffineLocus.isLocus_of_isAffineOpen_of_meets_fibres | exact GlobalTheory.AffineLocus.isLocus_of_isAffineOpen_of_meets_fibres | (intros; apply GlobalTheory.AffineLocus.isLocus_of_isAffineOpen_of_meets_fibres <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspFormValues

theorem evEx_of_range {K C H X : Type} [Field K] [AddCommGroup C] [Module K C] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup X] [Module ℂ X] (σ : K →+* ℂ) (ev : H → X) (φ : C → X) (hinj : Function.Injective ev)
    (hadd : ∀ x y, ev (x + y) = ev x + ev y) (hsmul : ∀ (a : ℂ) x, ev (a • x) = a • ev x)
    (hφa : ∀ f g, φ (f + g) = φ f + φ g) (hφs : ∀ (a : K) f, φ (a • f) = σ a • φ f)
    (hmem : ∀ f, φ f ∈ Set.range ev) : EvEx σ ev φ := by
  choose j hj using hmem
  exact ⟨{ toFun := j
           map_add' := fun f g => hinj (by rw [hadd, hj, hj, hj, hφa])
           map_smul' := fun a f => hinj (by rw [hsmul, hj, hj, hφs]) }, hj⟩

theorem phiC_eq {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T hV a f = adel W (castDict hV (T.dict j σ)) (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ))
      ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) • rdU (T.U j σ) f) := by
  subst hV
  rw [map_smul]
  rfl

theorem jEvExists : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → JEvExists T R κ v₀ := by
  intro hdec hvol D G _ _ Pl0 T0 A T _ R κ v₀ hlev hmod htie hpb i σ hσ hV
  have hr := GlobalTheory.T.hilbertModel_extremalValues_eq_holomorphicCuspForms hdec hvol D G Pl0 T0 A T R κ v₀ hlev hmod htie hpb i σ hσ hV
  refine evEx_of_range _ _ _ (GlobalTheory.EvalAtUnitVector.evInj T R v₀ hmod.HW htie.hv₀ i σ hσ) (fun x y => ?_) (fun a x => ?_)
    (fun f g => ?_) (fun a f => ?_) (fun f => ?_)
  · unfold evAt
    rw [map_add (f := _)]
    rfl
  · unfold evAt
    rw [map_smul]
    rfl
  · simp only [phiC_eq]
    rw [Submodule.coe_add, map_add (f := _), smul_add, map_add (f := _)]
  · simp only [phiC_eq]
    rw [Submodule.coe_smul, map_smulₛₗ (rdU _), smul_comm, map_smul]
  · rw [hr, phiC_eq]
    exact ⟨_, Submodule.smul_mem _ _
      (Submodule.mem_inf.2 ⟨((mem_cusp _ _ _ _ _ _).1 f.2).2 _ hσ, rdU_mem_offZero _ _⟩), rfl⟩

end GlobalTheory.CuspFormValues
end
