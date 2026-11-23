module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2735
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2659
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderActionRosatiAdjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderIsRingActionOnProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.VarFlag

theorem isIso_restrict_Vo : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (h : GlobalTheory.CompHS.Y₀ X Z ⟶ C.Y.X) [IsProper h], (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), ∃! p : Sp K ⟶ C.Y.X, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p) → (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) (z ≫ h)) → IsIso (h ∣_ GlobalTheory.VarFlag.Vo C) := by
  intro E _ _ _ H Dw l Xo c Y X Z hF C hT B j _ f hπ hB h _ hU hH
  have := C.Y.isNormalScheme
  have hN := GlobalTheory.IsNormalScheme.pred (GlobalTheory.VarFlag.Vo C).toScheme
  have : IsLocallyNoetherian C.Y.X := LocallyOfFiniteType.isLocallyNoetherian C.Y.str
  refine GlobalTheory.isIso_of_isProper_of_existsUnique_field_point _ _ _ inferInstance inferInstance hN inferInstance
    fun K _ w => ?_
  have hp : ∀ s, (w ≫ (GlobalTheory.VarFlag.Vo C).ι) s ∈ GlobalTheory.VarFlag.Vo C := fun s => by
    rw [Scheme.Hom.comp_apply]; exact (w s).2
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.exists_flagModel_point_of_flagBundle_fieldPoint X Z hF C hT B j f hπ hB K _ hp
  have e₀ : z₀ ≫ h = w ≫ (GlobalTheory.VarFlag.Vo C).ι := (hU K z₀).unique (hH K z₀) hz₀
  have P := (isPullback_morphismRestrict h (GlobalTheory.VarFlag.Vo C)).flip
  refine ⟨P.lift z₀ w e₀, P.lift_snd _ _ _, fun y hy => ?_⟩
  apply P.hom_ext
  · rw [P.lift_fst]
    have ey : (y ≫ (h ⁻¹ᵁ GlobalTheory.VarFlag.Vo C).ι) ≫ h = w ≫ (GlobalTheory.VarFlag.Vo C).ι := by
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy]
    have hr := hH K (y ≫ (h ⁻¹ᵁ GlobalTheory.VarFlag.Vo C).ι)
    rw [ey] at hr
    have := GlobalTheory.T.flagBundle_point_flags_unique_flagCover_point X C hF hT K _ _ _ hp hr hz₀
    exact (cancel_mono (GlobalTheory.CompHS.inc₀ X Z)).1 this
  · rw [P.lift_snd]; exact hy

end GlobalTheory.VarFlag
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

theorem _root_.GlobalTheory.T.exists_const_mul_horizontalDetLieCoordinate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (e : c.F →+* ℂ) (h : CxFr Y e → ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y) (V : Set (gen Y)), IsOpenImmersion io → Set.range io = V → io ≫ genStr Y = B.str → τ (H.rt : E) = H.rt0 → HorFn τ h → ∀ σb : RuleY Y, SecY Y V τ σb → ∃ κ : ℂ, ∀ (a : CxFr Y e) v w, Inner a.1 → FrY Y V τ e a.1.1 v w → Match τ a.2 v w → σb ℂ a.1.1 v w = κ * h a := by
  first | exact @GlobalTheory.DetLine.HorConst.exists_const_mul_horFn | exact GlobalTheory.DetLine.HorConst.exists_const_mul_horFn | (intros; apply GlobalTheory.DetLine.HorConst.exists_const_mul_horFn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

theorem _root_.GlobalTheory.T.exists_nonvanishing_detLine_section_of_horizontal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (e : c.F →+* ℂ) (h : CxFr Y e → ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y) (V : Set (gen Y)), IsOpenImmersion io → Set.range io = V → io ≫ genStr Y = B.str → τ (H.rt : E) = H.rt0 → HorFn τ h → ∃ σb : RuleY Y, SecY Y V τ σb ∧ NzY Y V τ σb := by
  first | exact @GlobalTheory.DetLine.FromHorizontal.exists_section_of_horFn | exact GlobalTheory.DetLine.FromHorizontal.exists_section_of_horFn | (intros; apply GlobalTheory.DetLine.FromHorizontal.exists_section_of_horFn <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.chartFunction_rel_of_translate_section_values : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (k : ℕ) (σ : SecM (GlobalTheory.HeatTrans.tr Y.H x ≫ Y.q.left) Q.P.L k) (τ : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ r z J = sval τ (r ≫ GlobalTheory.HeatTrans.tr Y.H x) z J) → ∀ (c : Q.P.L.ι) (U : Y.H.left.Opens), U ≤ Y.q.left ⁻¹ᵁ Q.P.L.U c → rsT (σ.f fun _ => c) (GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U) = pbT (GlobalTheory.HeatTrans.tr Y.H x) (rsT (τ.f fun _ => c) U) (GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U) := by
  first | exact @GlobalTheory.HeatTrans.chart_rel_of_sval | exact GlobalTheory.HeatTrans.chart_rel_of_sval | (intros; apply GlobalTheory.HeatTrans.chart_rel_of_sval <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.invariantVectorField_commutes_pointTranslation : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left), IsInv G v dd → ∀ (x : 𝟙_ (Over (Sp R)) ⟶ G) (O O' : G.left.Opens), O' ≤ GlobalTheory.HeatTrans.tr G x ⁻¹ᵁ O → ∀ f : Γ(G.left, O), dd O' (pbT (GlobalTheory.HeatTrans.tr G x) f O') = pbT (GlobalTheory.HeatTrans.tr G x) (dd O f) O' := by
  first | exact @GlobalTheory.Heat.IsInv.pbT_tr | exact GlobalTheory.Heat.IsInv.pbT_tr | (intros; apply GlobalTheory.Heat.IsInv.pbT_tr <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.toricChart_ringMap_flat_and_comap_maximalIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ∀ mm : Ideal Γ(Y.X, U.1), mm.IsMaximal → (∀ f ∈ mm, genι Y (ξ (closedPoint _)) ∉ Y.X.basicOpen f) → (GlobalTheory.LocReg.chartHom Y U ξ hx).Flat ∧ (maximalIdeal (ChartRing k m d)).comap (GlobalTheory.LocReg.chartHom Y U ξ hx) = mm := by
  first | exact @GlobalTheory.LocRegFlat.chartHom_flat_comap | exact GlobalTheory.LocRegFlat.chartHom_flat_comap | (intros; apply GlobalTheory.LocRegFlat.chartHom_flat_comap <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_basicOpen_interior_containing_toricChart_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U W : Y.X.affineOpens), W.1 = U.1 ⊓ interior Y → ∀ (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∃ h : Γ(Y.X, U.1), Y.X.basicOpen h ≤ W.1 ∧ GlobalTheory.LocReg.chartHom Y U ξ hx h ≠ 0 := by
  first | exact @GlobalTheory.LocReg.exists_basicOpen_chartHom_ne_zero | exact GlobalTheory.LocReg.exists_basicOpen_chartHom_ne_zero | (intros; apply GlobalTheory.LocReg.exists_basicOpen_chartHom_ne_zero <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.toricChart_comp_genericFibreInclusion_eq_spec_chartMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), ξ ≫ genι Y = spMap (GlobalTheory.LocReg.chartHom Y U ξ hx) ≫ chart U := by
  first | exact @GlobalTheory.LocReg.comp_genι_eq_spMap_chartHom | exact GlobalTheory.LocReg.comp_genι_eq_spMap_chartHom | (intros; apply GlobalTheory.LocReg.comp_genι_eq_spMap_chartHom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring


theorem _root_.GlobalTheory.T.eighth_power_symmetric_ample : ∀ {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (A ⊗ A).left), IsSymmetricPair h A P → Out.RelAmple A (diagPull A P) → IsAbelianScheme (Out.powObj A 8) ∧ (powLB A P).IsLB ∧ Out.RelAmple (Out.powObj A 8) (powLB A P) ∧ Out.Rigidified (Out.powObj A 8) (powLB A P) ∧ Out.Sym (Out.powObj A 8) (powLB A P) := by
  first | exact @GlobalTheory.EighthPowerBundle.powLB_props | exact GlobalTheory.EighthPowerBundle.powLB_props | (intros; apply GlobalTheory.EighthPowerBundle.powLB_props <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring


theorem _root_.GlobalTheory.T.kernel_condition_along_baseChange_of_pullback : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S') [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over S) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), P₁.IsLB → IsGrpPullback A A₁ f φ → IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → (∀ (T : Over S') (x : T ⟶ A), IsTrivial (slice A P x) → x = 1) → KerAlong A₁ P₁ f := by
  first | exact @GlobalTheory.PrincSubring.kerAlong_of_pull | exact GlobalTheory.PrincSubring.kerAlong_of_pull | (intros; apply GlobalTheory.PrincSubring.kerAlong_of_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc


theorem _root_.GlobalTheory.T.zarhinOrderAction_rosati_adjoint : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → Adj (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu) (GlobalTheory.ZarhinFam.bar d) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) := by
  first | (exact @GlobalTheory.ZarhinFam.AdjPf.adj_actZ) | (exact GlobalTheory.ZarhinFam.AdjPf.adj_actZ) | (intros; apply GlobalTheory.ZarhinFam.AdjPf.adj_actZ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc


theorem _root_.GlobalTheory.T.zarhinOrder_isRingAction_on_product : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → IsRAct (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) := by
  first | (exact @GlobalTheory.ZarhinFam.RAct.actZ_isRAct) | (exact GlobalTheory.ZarhinFam.RAct.actZ_isRAct) | (intros; apply GlobalTheory.ZarhinFam.RAct.actZ_isRAct <;> assumption)
end
