module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle745
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle712
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle734
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle736
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle716
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle746
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle717
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle526
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralLinearOfDensityEqSum
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open GlobalTheory.PointFormSign Matrix
open ReciprocityTheory.L2DbarEstimates (V)


theorem _root_.GlobalTheory.T.lieEigenspaceHodgeGram_local_holomorphic_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ τ : GlobalTheory.AllWt.Psi H, ∃ (κ : ℝ) (W : V X.dim → Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) ℂ) (Z : V X.dim → (Fin (Dw.mult τ.1) → Fin (Dw.p + Dw.q - Dw.mult τ.1) → ℂ)), 0 < κ ∧ (∀ᶠ u in 𝓝 (c'.e y), lieGram e U hj f₀ A₀ A (c'.e.symm u) τ.1 = (κ : ℂ) • ((W u)ᵀ * domGram _ _ (Z u) * (W u)ᴴᵀ)) ∧ (∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ Z u) ∧ (∀ i j, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => W u i j) u) ∧ IsUnit (W (c'.e y)).det ∧ (1 - Matrix.of (Z (c'.e y)) * (Matrix.of (Z (c'.e y)))ᴴ).PosDef := by
  first | exact @GlobalTheory.LieBase.LocalModel.lieGram_local_model | exact GlobalTheory.LieBase.LocalModel.lieGram_local_model | (intros; apply GlobalTheory.LieBase.LocalModel.lieGram_local_model <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.psiCoordinates_evenCharacters_fourthPowers_associated : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (y : D'.toPre.X) (r r' : R), PsiCoord D.toPre (xe (2 • y)) r → PsiCoord D'.toPre (2 • y) r' → Associated (r ^ 4) (r' ^ 4) := by
  first | exact @GlobalTheory.PsiFourth.main | exact GlobalTheory.PsiFourth.main | (intros; apply GlobalTheory.PsiFourth.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.HodgeRelation

theorem chernTop_lieGram_rel_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ (τ : GlobalTheory.AllWt.Psi H) (k' : ℕ) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), 1 ≤ k' → chernTop ((∑ a ∈ Finset.range (k' + 1), MvPolynomial.C ((-1 : ℝ) ^ (k' - a)) * MvPolynomial.X (τ.1, a) * MvPolynomial.X (conjEmb τ.1, k' - a)) * Q) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) = 0 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA τ k' Q hk
  obtain ⟨-, hXd⟩ := GlobalTheory.T.flagComponent_dim_and_base_dim E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL
  have hcard : Fintype.card (Fin X.dim) = Fintype.card (GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) := by
    simp [hXd, Fintype.card_prod]
  let ix : Fin X.dim ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q := Fintype.equivOfCardEq hcard
  obtain ⟨φ, g, cc, hcc, hφ, hg, hgu, hdom, hev⟩ :=
    GlobalTheory.T.hodgeGram_localModel_algebraicChart_holomorphic E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA ix
  set v := c'.e y
  set M : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ := fun u => modelGram H Dw (coordOf ix u) with hM
  have hsm := GlobalTheory.T.boundedDomainModelGram_contDiff_isUnit E H Dw ix (φ v) hdom
  have hφr : ContDiffAt ℝ 2 φ v := (hφ.contDiffAt (n := 2)).restrict_scalars ℝ
  have hK2 : ∀ τ, MContDiffAt 2 (fun w => M (φ w) τ) v := fun τ a b => ((hsm τ).1 a b).comp v hφr
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.chernPolyTopDensity_boundedDomainModel_eq_mul_origin E H Dw ix (φ v) hdom
  change chernTop (relPoly τ k' * Q) _ v = 0
  rw [GlobalTheory.T.topChernDensity_invariant_holomorphic_frameChange _ _ (fun w => M (φ w)) g cc v hcc hg hgu hK2 (fun τ => (hsm τ).2) hev,
    GlobalTheory.T.chernPolyTopDensity_comp_holomorphic_normSq_det _ M φ v hφ (fun τ => (hsm τ).1) (fun τ => (hsm τ).2), hκ, GlobalTheory.T.chernPolyTopDensity_grassmannRelation_origin_zero E H Dw ix τ k' hk Q,
    mul_zero, mul_zero]

end GlobalTheory.HodgeRelation
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.LevExt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gridCharacter_eq_reference_at_base_tuple {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {t : T} (h : L.Is t) (j : ℕ) : L.mu t j = L.mu0 j := by
  have hx := h.xi t
  rw [h.xi_base] at hx
  have e : L.xi t = 1 := MonoidHom.ext (GlobalTheory.ChrEqUnique.eq_one_of_chrEq hx)
  show L.mu0 j * L.xi t = L.mu0 j
  rw [e, mul_one]

theorem Q_eq_empty {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {t : T} (h : L.Is t) : L.Q t = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
  have h1 := (h.Q_ram t PP).2 (Or.inl hPP)
  rw [h.xi_base] at h1
  exact h1 fun _ _ => rfl

theorem isRes_unique' {D : D7} {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : IsRes χ P c) (h' : IsRes χ P c') : c = c' := by
  refine MonoidHom.ext fun u => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  haveI : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h0
    have h1 : a = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    apply u.ne_zero
    rw [← ha, h1, map_zero]
  rw [h a (Units.mk0 _ ha0) u rfl ha.symm, h' a (Units.mk0 _ ha0) u rfl ha.symm]

section Gen

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}

theorem idc_heq (hP : B'.toPre = B.toPre) {c : (AE a.D)ˣ →* Circle} {c' : (AE a'.D)ˣ →* Circle}
    {χ : Formalism.L2.Host.HChar a.D.host.E} {χ' : Formalism.L2.Host.HChar a'.D.host.E} (hχ : HEq χ' χ) (h : ChrEq c χ)
    (h' : ChrEq c' χ') : HEq c' c := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (χ')) ((by with_unfolding_all exact ((χ) :))) (χ') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (χ')) (χ') (((χ))) (((hχ)))).symm : _))
  clear (hχ)
  subst e))
  have e : @Eq ((AE a.D)ˣ →* Circle) ((by with_unfolding_all exact (c' :))) c := GlobalTheory.ChrEqUnique.idc_unique a.D _ c χ ((by with_unfolding_all exact (h' :))) h
  exact (by with_unfolding_all exact ((heq_of_eq e) :))

theorem res_heq (hP : B'.toPre = B.toPre) {χ : Formalism.L2.Host.HChar a.D.host.E} {χ' : Formalism.L2.Host.HChar a'.D.host.E} (hχ : HEq χ' χ)
    {PP : Pl a.D.host.E} {PP' : Pl a'.D.host.E} (hPP : HEq PP' PP) {c : (kP PP)ˣ →* ℂˣ} {c' : (kP PP')ˣ →* ℂˣ}
    (h : IsRes χ PP c⁻¹) (h' : IsRes χ' PP' c'⁻¹) : HEq c' c := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (χ')) ((by with_unfolding_all exact ((χ) :))) (χ') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (χ')) (χ') (((χ))) (((hχ)))).symm : _))
  clear (hχ)
  subst e))
  ( (
  have e : @Eq (type_of% (PP')) ((by with_unfolding_all exact ((PP) :))) (PP') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (PP')) (PP') (((PP))) (((hPP)))).symm : _))
  clear (hPP)
  subst e))
  have e : ((by with_unfolding_all exact (c' :)) : (kP PP)ˣ →* ℂˣ)⁻¹ = c⁻¹ := isRes_unique' (D := a.D) ((by with_unfolding_all exact (h' :))) h
  have e' : @Eq ((kP PP)ˣ →* ℂˣ) ((by with_unfolding_all exact (c' :))) c := inv_inj.1 e
  exact (by with_unfolding_all exact ((heq_of_eq e') :))

theorem hermitianCodeCharFrame_referenceCharacter_heq (hP : B'.toPre = B.toPre) {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} (hf : HEq f' f) {i : Fin a.D.R.m}
    {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') : HEq ((Top.Fr.at a'.st f').mu0 i') ((Top.Fr.at a.st f).mu0 i) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))
  clear (hf)
  subst e))
  have e : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i' := (by with_unfolding_all exact ((Fin.ext h : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i') :))
  clear h
  subst e
  exact (by with_unfolding_all exact ((HEq.refl ((Top.Fr.at a.st f).mu0 i)) :))

theorem frat_eta_heq (hP : B'.toPre = B.toPre) {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} (hf : HEq f' f) :
    HEq (Top.Fr.at a'.st f').eta (Top.Fr.at a.st f).eta := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))
  clear (hf)
  subst e))
  exact (by with_unfolding_all exact ((HEq.refl (Top.Fr.at a.st f).eta) :))

theorem mem_vGs (hP : B'.toPre = B.toPre) {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px)
    {PP : Pl a.D.host.E} {PP' : Pl a'.D.host.E} (hPP : HEq PP' PP) (h : PP ∈ (B.primes px).vGs) : PP' ∈ (B'.primes px').vGs := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (px')) ((by with_unfolding_all exact ((px) :))) (px') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (px')) (px') (((px))) (((hpx)))).symm : _))
  clear (hpx)
  subst e))
  ( (
  have e : @Eq (type_of% (PP')) ((by with_unfolding_all exact ((PP) :))) (PP') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (PP')) (PP') (((PP))) (((hPP)))).symm : _))
  clear (hPP)
  subst e))
  exact (by with_unfolding_all exact (h :))

end Gen

end GlobalTheory.Mem.R3.Rw.LevExt


open GlobalTheory.Mem.R3.Rw.LevExt in

theorem GlobalTheory.Mem.R3.Rw.LevExt.levSame_of_levOf : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh → LevSame z Wt' R' := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hf hpx hL'
  have hP : B'.toPre = B.toPre := hE.1
  have hC : z.R.toLevCh.C = Top.Fr.at (w.st Z) f := z.lev.C.trans (by rw [w.C_eq])
  have hC' : R'.toLevCh.C = Top.Fr.at (w'.st Z') f' := hL'.C.trans (by rw [w'.C_eq])
  have hmu0 : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
      HEq (R'.toLevCh.C.mu0 i') (z.R.toLevCh.C.mu0 i) := by
    intro i i' h
    rw [hC, hC']
    exact hermitianCodeCharFrame_referenceCharacter_heq (a := Z) (a' := Z') hP hf h
  have heta : HEq R'.toLevCh.C.eta z.R.toLevCh.C.eta := by
    rw [hC, hC']
    exact frat_eta_heq (a := Z) (a' := Z') hP hf
  have hs := z.lev.is
  have hs' := hL'.is
  refine ⟨fun i i' h => ⟨?_, fun PP' PP hPP hm => ?_⟩, ?_, Q_eq_empty hs', Q_eq_empty hs⟩
  · rw [gridCharacter_eq_reference_at_base_tuple hs', gridCharacter_eq_reference_at_base_tuple hs]
    exact idc_heq (a := Z) (a' := Z') hP (hmu0 i i' h) (hs.mu0 i) (hs'.mu0 i')
  · have hm0 : PP ∈ (B.primes w.px).vGs := by
      have e := z.lev.Pg
      rw [← e]
      exact hm
    have hm' : PP' ∈ R'.toLevCh.Pg := by
      rw [hL'.Pg]
      exact mem_vGs (a := Z) (a' := Z') hP hpx hPP hm0
    exact res_heq (a := Z) (a' := Z') hP (hmu0 i i' h) hPP (hs.chi i PP hm) (hs'.chi i' PP' hm')
  · exact idc_heq (a := Z) (a' := Z') hP heta hs.eta hs'.eta
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.ChiWExt

section Move

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt}

theorem m_eq (hP : B'.toPre = B.toPre) : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  exact (by with_unfolding_all exact ((Eq.refl (w.st Z).toD7.R.m) :))

theorem gc_eq (hP : B'.toPre = B.toPre) {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px) : Gc B' px' = Gc B px := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (px')) ((by with_unfolding_all exact ((px) :))) (px') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (px')) (px') (((px))) (((hpx)))).symm : _))
  clear (hpx)
  subst e))
  exact (by with_unfolding_all exact ((Eq.refl (Gc B px)) :))

theorem prod_move (hP : B'.toPre = B.toPre) {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px)
    {Pg : Finset (Pl (w.st Z).toD7.host.E)} {Pg' : Finset (Pl (w'.st Z').toD7.host.E)} (hPg : HEq Pg' Pg)
    {eG : Gc B px ≃* G0 Pg (w.st Z).toD7.R.r} {eG' : Gc B' px' ≃* G0 Pg' (w'.st Z').toD7.R.r} (heG : HEq eG' eG)
    {χ : ∀ PP : Pl (w.st Z).toD7.host.E, (kP PP)ˣ →* ℂˣ} {χ' : ∀ PP : Pl (w'.st Z').toD7.host.E, (kP PP)ˣ →* ℂˣ}
    (hχ : ∀ PP' PP, HEq PP' PP → PP ∈ Pg → HEq (χ' PP') (χ PP)) {g : Gc B px} {g' : Gc B' px'} (hg : HEq g' g) :
    ∏ PP : Pg', ((χ' PP (Matrix.GeneralLinearGroup.det (eG' g' PP)) : ℂˣ) : ℂ) =
      ∏ PP : Pg, ((χ PP (Matrix.GeneralLinearGroup.det (eG g PP)) : ℂˣ) : ℂ) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (px')) ((by with_unfolding_all exact ((px) :))) (px') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (px')) (px') (((px))) (((hpx)))).symm : _))
  clear (hpx)
  subst e))
  ( (
  have e : @Eq (type_of% (Pg')) ((by with_unfolding_all exact ((Pg) :))) (Pg') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Pg')) (Pg') (((Pg))) (((hPg)))).symm : _))
  clear (hPg)
  subst e))
  ( (
  have e : @Eq (type_of% (eG')) ((by with_unfolding_all exact ((eG) :))) (eG') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (eG')) (eG') (((eG))) (((heG)))).symm : _))
  clear (heG)
  subst e))
  ( (
  have e : @Eq (type_of% (g')) ((by with_unfolding_all exact ((g) :))) (g') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (g')) (g') (((g))) (((hg)))).symm : _))
  clear (hg)
  subst e))
  have e : ∀ PP : Pl (w.st Z).toD7.host.E, PP ∈ Pg → HEq (χ' ((by with_unfolding_all exact (PP :)))) (χ PP) :=
    fun PP hm => hχ ((by with_unfolding_all exact (PP :))) PP ((by with_unfolding_all exact ((HEq.refl PP) :))) hm
  refine Finset.prod_congr rfl fun PP _ => ?_
  exact congrArg (fun c : ℂˣ => (c : ℂ)) (DFunLike.congr_fun (eq_of_heq (e PP.1 PP.2)) _)

end Move



theorem grp_chiW_ext : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq w'.px w.px → RSideW z Wt' R' → LevSame z Wt' R' → R'.toRealDat.grp_chiW := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hpx hS hL
  have hc := z.pins.char.base.grp.chiW
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL :=
    (B'.embLL.rangeRestrictFieldEquiv.symm : B'.embLL.fieldRange →+* B'.LL).comp
      (B.embLL.codRestrict B'.embLL.fieldRange fun x => hE.2.2.2 ⟨x, rfl⟩)
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := fun x =>
    congrArg Subtype.val (B'.embLL.rangeRestrictFieldEquiv.apply_symm_apply ⟨B.embLL x, hE.2.2.2 ⟨x, rfl⟩⟩)
  intro i' g'
  have hm := m_eq (w := w) (w' := w') (Z := Z) (Z' := Z') hE.1
  let i : Fin (w.st Z).toD7.R.m := ⟨i', by have := i'.2; omega⟩
  have hi : (i : ℕ) = i' := rfl
  let g : Gc B w.px := cast (gc_eq hE.1 hpx) g'
  have hg : HEq g' g := (cast_heq _ _).symm
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hPg, heG, -, hW, -⟩ := hS'
  have hWi := hW i i' hi
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hWι⟩ := hWi
  have hch := (hWι ι hι).2.2.1 g' g hg
  rw [hch, hι, hc i g]
  exact (prod_move hE.1 hpx hPg heG (fun PP' PP h hm => (hL.1 i i' hi).2 PP' PP h hm) hg).symm

end GlobalTheory.Mem.R3.Rw.ChiWExt
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.WeilExt



theorem idemSame_of_keep : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → GrpTrue Z.N f → GrpTrue Z'.N f' → RSideW z Wt' R' →
  ∀ cG : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd, Keep R'.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).lv2 cG → IdemSame z Xg := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hf hp hG hG' hR cG hK g' g hg
  obtain ⟨-, -, -, -, -, -, -, -, -, hPg, heG, -⟩ := hR
  have hB := hE.1
  cases B
  cases B'
  dsimp only at hB
  subst hB
  cases hf
  have hpx : w'.px = w.px := eq_of_heq hp
  cases w'
  dsimp only at hpx
  subst hpx
  cases hg
  obtain ⟨plg, iso, hpl, hid, -, hbc⟩ := z.pins.keep.grp
  obtain ⟨plg2, iso', hpl', hid', -, hbc'⟩ := hK.grp
  refine (hid' g).trans (Eq.trans ?_ (hid g).symm)
  refine Eq.trans ?_ (TypesTrue.typeIdempotent_coeff_across_layers hG hG' ((z.R.eG.trans z.cG) g))
  congr 1
  funext kv'
  obtain ⟨k, v'⟩ := kv'
  obtain ⟨v, rfl⟩ : ∃ v, v' = plEquiv Z.N.naut Z'.N.naut k v := ⟨_, (Equiv.apply_symm_apply _ v').symm⟩
  show _ = ((z.R.eG.trans z.cG) g) ⟨k, (plEquiv Z.N.naut Z'.N.naut k).symm (plEquiv Z.N.naut Z'.N.naut k v)⟩
  rw [Equiv.symm_apply_apply]
  have hP : R'.Pg = z.R.Pg := eq_of_heq hPg
  have hQ : (plg2 ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩).1 = (plg ⟨k, v⟩).1 := by
    rw [hpl', hpl]
    exact TypesTrue.plGw_plEquiv hG hG' k v
  exact GlobalTheory.Mem.R3.DefLatBC.bc_eq_of_heq hP z.R.eG R'.eG heG g _ _ hQ (iso ⟨k, v⟩)
    (iso' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩) _ _ (hbc g ⟨k, v⟩) (hbc' g ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩)

end GlobalTheory.Mem.R3.Rw.WeilExt
end

section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

theorem _root_.GlobalTheory.T.hasChernIntegral_linear_of_density_eq_sum : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (R : MvPolynomial (ι × ℕ) ℝ) (J : Type) [Fintype J] (M : J → ℕ) (E' : ∀ j, Fr (ratOf X) (fun _ : Unit => M j) 0) (H' : ∀ j, Mat (fun _ : Unit => M j) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => M j) ℂ) (R' : MvPolynomial (Unit × ℕ) ℝ) (a t : J → ℝ), IsMetricOn E O H → (∀ j, IsMetricOn (E' j) O (H' j)) → (∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∃ A ∈ E.S (under y), ∃ B : ∀ j, Mat (fun _ : Unit => M j) X.Fn, (∀ j, B j ∈ (E' j).S (under y)) ∧ chernTop R (fun v => H A (c.e.symm v)) (c.e y) = ∑ j, a j * chernTop R' (fun v => H' j (B j) (c.e.symm v)) (c.e y)) → (∀ j, HasChernIntegral (E' j) O (H' j) R' (t j)) → HasChernIntegral E O H R (∑ j, a j * t j) := by
  first | exact @GlobalTheory.GoodMetric.hasChernIntegral_of_eq_sum | exact GlobalTheory.GoodMetric.hasChernIntegral_of_eq_sum | (intros; apply GlobalTheory.GoodMetric.hasChernIntegral_of_eq_sum <;> assumption)
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame


theorem _root_.GlobalTheory.T.hodgeMetric_chernDensity_lieGram_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ (τ : GlobalTheory.AllWt.Psi H) (k' : ℕ) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), 1 ≤ k' → chernTop ((∑ a ∈ Finset.range (k' + 1), MvPolynomial.C ((-1 : ℝ) ^ (k' - a)) * MvPolynomial.X (τ.1, a) * MvPolynomial.X (conjEmb τ.1, k' - a)) * Q) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) = 0 := by
  first | exact @GlobalTheory.HodgeRelation.chernTop_lieGram_rel_mul | exact GlobalTheory.HodgeRelation.chernTop_lieGram_rel_mul | (intros; apply GlobalTheory.HodgeRelation.chernTop_lieGram_rel_mul <;> assumption)

end
end
