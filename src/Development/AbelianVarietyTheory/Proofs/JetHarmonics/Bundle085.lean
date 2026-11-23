module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegenerateFormalBiextensionSquare
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle059
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle081
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle079
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle080
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle020
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle068
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle012
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
public import Formalism.FlagUnipotentLattices.AlgebraicIdentityHigherDegree
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.exists_idempotent_frobeniusOrbit_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (d : ℕ) [NeZero d] (tau : ZMod d → (E →+* ℂ)), FrobOrd V io ι tau → ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (V.l : 𝓞 E) * y) ∧ (∀ a, V.MM (emA3 io ι (tau a) ε - 1)) ∧ ∀ x : 𝓞 E, (∀ a, V.MM (emA3 io ι (tau a) x)) → ∃ y, ε * x = (V.l : 𝓞 E) * y := by
  first | exact @GlobalTheory.exists_idempotent_of_unramified_place | exact GlobalTheory.exists_idempotent_of_unramified_place | (intros; apply GlobalTheory.exists_idempotent_of_unramified_place <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.nonDegenerate_formalBiextension_square : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), NDG Y → NonDeg (Y.rawSelf p) V := by
  first | exact @GlobalTheory.NonDegSquare.nonDeg_rawSelf | exact GlobalTheory.NonDegSquare.nonDeg_rawSelf | (intros; apply GlobalTheory.NonDegSquare.nonDeg_rawSelf <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem germOfFam_holds : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → GermOfFamT := by
  intro hL hL2 hL4 hT E _ _ _ H Dw l Xo c inst hstar
  obtain rfl := starSt E H inst hstar
  let := H.starRing
  intro T io y C htr P ϖ hϖ Q hQ n _ D' A' G' _ _ pD pA pG U' PU F _ _ _ _ v hv q hq
  have hu := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n _ pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨τ, hτ, ht, hiff⟩ := frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT C.wPT
    C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  refine ⟨fun σ' => ?_, fun s σ' hE hs g hg => ?_⟩
  · obtain ⟨f, hf⟩ := (GlobalTheory.GermBasic.main T.V D' A' G' U' _ _ hu τ hτ F q).2.2 (ht htr) σ'
    exact ⟨f, (hiff F q σ' f).2 hf⟩
  · exact GlobalTheory.IntegralGerm.main hL hL2 hL4 hT T.V ϖ hϖ D' A' G' U' _ _ hu τ hτ F v hv q hq σ' s g hE
      ((hiff F q σ' g).1 hg)
      (n1e T.V ϖ hϖ D' _ (GlobalTheory.QBox.main T.V ϖ hϖ n P.D D' pD Q hQ) F v q s hs)

end GlobalTheory.PowGerm
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm.BoxGerm
open GlobalTheory.BoxFamily GlobalTheory.PowGerm.FrameN

section General

variable {X X' Y Y₀ Y₁ Z : Scheme.{0}} {M : LB X}

theorem gs_stalkMap (r : Z ⟶ X') (β : X' ⟶ X) (z : Z) (U : X.Opens) (h : β (r z) ∈ U) (a : Γ(X, U)) :
    (r.stalkMap z).hom (gs β (r z) U a) = gs (r ≫ β) z U a := by
  rw [← gs_pull r β z U h, gs_eq β _ U h, gs_eq r z _ h]
  exact Scheme.Hom.germ_stalkMap_apply r (β ⁻¹ᵁ U) z h _

theorem sval_along (hM : M.IsLB) (g : Y₁ ⟶ X) (z : Y ⟶ Y₁) (x : Y₀ ⟶ X) (s : Y ⟶ Y₀) (hzg : z ≫ g = s ≫ x) (q : ℕ)
    (σ : LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => g) (fun _ => (q : ℤ))))
    (τ : LB.Gen (LB.LinComb M (K := Fin 1) (fun _ => x) (fun _ => (1 : ℤ)))) (a : Γ(Y, ⊤))
    (H : ∀ y J, Good M y J → sval σ z y J = gs (𝟙 Y) y ⊤ a * (val τ s y J ^ q).val)
    (r : Z ⟶ Y) (y : Z) (J) (hJ : Good M y J) :
    sval σ (r ≫ z) y J = gs r y ⊤ a * (val τ (r ≫ s) y J ^ q).val := by
  have m₀ : (z ≫ g) (r y) ∈ M.U (J (r ≫ z ≫ g)) := hJ (r ≫ z ≫ g)
  obtain ⟨J₀, hJ₀, e⟩ := exists_good M hM (r y) (fun _ : PUnit => z ≫ g) (fun _ => J (r ≫ z ≫ g)) (fun _ _ _ => rfl)
    (fun _ => m₀)
  have e' : J₀ (z ≫ g) = J (r ≫ z ≫ g) := e PUnit.unit
  have h := congrArg (r.stalkMap y).hom (H (r y) J₀ hJ₀)
  have m₁ : z (r y) ∈ LB.wchart M (fun _ : Fin 1 => g) (fun _ => J (r ≫ z ≫ g)) := Set.mem_iInter.2 fun _ => m₀
  have m₂ : s (r y) ∈ LB.wchart M (fun _ : Fin 1 => x) (fun _ => J (r ≫ z ≫ g)) :=
    Set.mem_iInter.2 fun _ => (show (s ≫ x) (r y) ∈ M.U (J (r ≫ z ≫ g)) from hzg ▸ m₀)
  rw [sval_of σ z _ J₀ (fun _ => J (r ≫ z ≫ g)) (fun _ => e'),
    val_of τ s _ J₀ (fun _ => J (r ≫ z ≫ g)) (fun _ => by rw [← hzg]; exact e'), map_mul,
    gs_stalkMap r (𝟙 Y) y ⊤ trivial, Category.comp_id, Units.val_pow_eq_pow_val, map_pow] at h
  rw [sval_of σ (r ≫ z) y J (fun _ => J (r ≫ z ≫ g)) (fun _ => by rw [Category.assoc]),
    val_of τ (r ≫ s) y J (fun _ => J (r ≫ z ≫ g)) (fun _ => by rw [Category.assoc, ← hzg]),
    Units.val_pow_eq_pow_val]
  refine (gs_stalkMap r z y _ m₁ _).symm.trans (h.trans (congrArg (fun u => gs r y ⊤ a * u ^ q) ?_))
  exact (congrArg (r.stalkMap y).hom (gs_unit s _ _ m₂ _).symm).trans
    ((gs_stalkMap r s y _ m₂ _).trans (gs_unit (r ≫ s) y _ m₂ _))

theorem gs_spMap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (y : Sp B) (a : A) :
    gs (spMap φ) y ⊤ (toΓ A a) = gs (𝟙 (Sp B)) y ⊤ (toΓ B (φ a)) := by
  have e : (spMap φ).appTop.hom (toΓ A a) = toΓ B (φ a) :=
    (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm
  rw [← e]
  exact ((gs_pull (𝟙 _) (spMap φ) y ⊤ trivial _).trans (by rw [Category.id_comp])).symm

end General

theorem psJet_boxSer {F : Type} [CommRing F] {n d : ℕ} (m : ℕ) (f : Fin n → PS F 1 d) :
    psJet m (boxSer f) = ∏ i, jetCopy (S := F) d m i (psJet m (f i)) := by
  have hp : ∀ (S : Finset (Fin n)) (g : Fin n → PS F n d), psJet m (∏ i ∈ S, g i) = ∏ i ∈ S, psJet m (g i) := by
    intro S g
    induction S using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.prod_empty, FBIdJet.psJet_one]
    | insert a S ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, FBIdJet.psJet_mul, ih]
  rw [boxSer, hp]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [MvPowerSeries.rename_eq_subst, FBIdJet.psJet_subst m _ (fun p => by simp)]
  refine DFunLike.congr_fun (GermD.jet_hom_ext fun p => ?_) _
  rw [jetCopy, GermD.jetMap_mk, GermD.jetMap_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X, Function.comp_apply,
    ← MvPolynomial.coe_X, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]

theorem exists_lift {V : Type} [CommRing V] [IsDomain V] (G : Over (Sp V)) (F : Type) [Field F]
    [Algebra (FractionRing V) F] {Y : Scheme.{0}} (a : Y ⟶ (TFK (R := V) F).left) (b : Y ⟶ G.left)
    (h : b ≫ G.hom = a ≫ (TFK (R := V) F).hom ≫ jK V) :
    ∃ z : Y ⟶ (UnifPre.GF (R := V) (G := G) F).left,
      z ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = a ∧
      z ≫ UnifPre.gFK (R := V) (G := G) F = b := by
  let T : Over (TK V).left := Over.mk (a ≫ (TFK (R := V) F).hom)
  let u : T ⟶ TFK (R := V) F := Over.homMk a rfl
  let w : T ⟶ (Over.pullback (jK V)).obj G :=
    Over.homMk (pullback.lift b (a ≫ (TFK (R := V) F).hom) (by rw [h, Category.assoc])) (pullback.lift_snd _ _ _)
  refine ⟨(lift u w).left, congrArg (fun q => q.left) (lift_fst u w), ?_⟩
  have e : (lift u w).left ≫ (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = w.left :=
    congrArg (fun q => q.left) (lift_snd u w)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans (pullback.lift_fst _ _ _))

end GlobalTheory.PowGerm.BoxGerm

namespace GlobalTheory.PowGerm
open GlobalTheory.BoxFamily FrameN BoxGerm



theorem boxGermSt_holds : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → BoxGermSt := by
  intro h₁ h₂ h₄ hT E _ _ _ H V _ _ _ _ t P d FT act ph1 ph2 sy ad tg xT eT wPT hch hfr hpr τ₁ g₁ el n D' A' G' _ _
    pD pA pG U' PU F _ _ _ _ q hq σ s f σ' S hσ hS hE' m
  have hM : P.U.LG.L.IsLB := P.U.LG.isLB
  have hM' : U'.LG.L.IsLB := U'.LG.isLB
  obtain ⟨τ, hτ, hv₀⟩ := exists_boxPull_gen (pr := fun i => (pG.pr i).left) PU.wL PU.wL_gen hM hM' (K := Fin 1)
      (φ' := fun _ => (zV pG xT m).left) (φ := fun _ _ => (xT m).left) (ε := fun _ => 1) (cpy V n d m)
      (fun i _ => zV_pr pG xT m i) (fun _ => τ₁ m) (fun _ => g₁ m)
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V (Fin n × Fin d) m)) (y : Z) (J J'), Good P.U.LG.L y J →
      Good U'.LG.L y J' →
      om PU.wL y J J' (r ≫ (zV pG xT m).left) * val τ r y J' = ∏ i, val (τ₁ m) (r ≫ cpy V n d m i) y J := by
    intro Z r y J J' hJ hJ'
    have := hv₀ Z r y J J' hJ hJ'
    rwa [Fin.prod_univ_one, zpow_one] at this
  obtain ⟨z, h₀, hzg⟩ := exists_lift G' F (spMap (algebraMap F (Jet F (Fin n × Fin d) m)))
    (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m) ≫ (zV pG xT m).left) (by
      rw [Category.assoc _ (zV pG xT m).left, Over.w (zV pG xT m)]
      symm
      show spMap _ ≫ spMap (algebraMap (FractionRing V) F) ≫ spMap (algebraMap V (FractionRing V)) =
        spMap _ ≫ spMap (algebraMap V (Jet V (Fin n × Fin d) m)) ≫ 𝟙 _
      simp only [spMap, Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [JetTr.jetCoef_alg, ← IsScalarTower.algebraMap_eq])
  have hp : ∀ i, z ≫ UnifPre.gFK (R := V) (G := G') F ≫ (pG.pr i).left = jptN xT F n m i := fun i => by
    rw [← Category.assoc, hzg, Category.assoc, zV_pr, ← Category.assoc, coef_cpy, jptN]
  choose zi hz₀ hz₁ hz₂ using fun i => (hσ i).2 m
  have hc : ∀ i, cpy F n d m i ≫ spMap (jetCoef (algebraMap V F) (Fin 1 × Fin d) m) = jcN V F d n m i := fun i => by
    rw [jcN]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have main := GlobalTheory.BoxSectionValues.main h₁ h₂ h₄ hT V n P.D D' P.A A' t.G G' pD pA pG U' P.U PU F q hq σ s σ' S
    (fun i => (hσ i).1) hS hE' _ z (fun i => cpy F n d m i ≫ zi i)
    (fun i => by rw [hp, Category.assoc, hz₁, ← Category.assoc, hc, jptN])
    (fun i => by
      rw [h₀, Category.assoc, hz₀]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [AlgHom.comp_algebraMap])
  have core := core_iff (pr := fun i => (pG.pr i).left) hM hM' PU.wL PU.wL_gen (τ₁ m) (g₁ m) (cpy V n d m)
      (zV_pr pG xT m) τ hτ hv (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m))
      (UnifPre.gFK (R := V) (G := G') F) z hzg q
      (genCast (congrArg RigLB.L P.bundle).symm _ _ (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
        LB.pullGen t.PP.L _ _ (genPowG t _ _ (eLG t (𝟙 (Sp V)) d xT act eT wPT m) q) (jcN V F d n m i)))
      (fun y J hJ => (val_cast_prod t _ _ _ _ _ q _ y J hJ).trans (Finset.prod_congr rfl fun i _ => by
        rw [coef_cpy]
        have := val_along hM _ _ _ _ (el m) (jcN V F d n m i) y J hJ
        rw [Category.comp_id] at this
        exact congrArg (· ^ q) this.symm)) σ' (toΓ _ (psJet m (boxSer f)))
  obtain ⟨a, b, k₂, k₃, k₄⟩ := core.2 fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_at hM y
    have e₁ : (om PU.wL y J J' (z ≫ UnifPre.gFK (R := V) (G := G') F) ^ q).val * sval σ' z y J' =
        ∏ i, sval (σ i) (cpy F n d m i ≫ zi i) y J := main y J J' hJ hJ'
    have e₂ : ∀ i, sval (σ i) (cpy F n d m i ≫ zi i) y J =
        gs (𝟙 _) y ⊤ (toΓ _ (jetCopy (S := F) d m i (psJet m (f i)))) *
          (val (τ₁ m) (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m) ≫ cpy V n d m i) y J ^ q).val := fun i => by
      rw [sval_along hM _ (zi i) _ _ (hz₁ i) q (σ i) (τ₁ m) _ (hz₂ i) (cpy F n d m i) y J hJ, hc, coef_cpy, gs_spMap]
      rfl
    have e₃ := hv _ (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m)) y J J' hJ hJ'
    rw [← hzg] at e₃
    rw [Finset.prod_congr rfl fun i _ => e₂ i, Finset.prod_mul_distrib, ← Units.coe_prod, Finset.prod_pow, ← e₃,
      mul_pow, Units.val_mul, mul_left_comm, ← gs_prod _ y ⊤ trivial, ← map_prod, ← psJet_boxSer] at e₁
    exact (Units.mul_right_inj _).1 e₁
  exact ⟨z, a, b, h₀, hp, k₂, (corr_genCast _ _ _).2 k₃, k₄⟩

end GlobalTheory.PowGerm
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem family_through_discreteSeries : Hyps → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b bv ga h : ℝ) (q0 : ℕ) (R0 : Rep k r), Num k r lam u b bv ga h q0 →
    R0.IsDS (PI.BesselPeriodGGP.eps48 k r) lam →
    ∃ R : (Fin (2 * r + k + 1) → ℤ) → Rep k r, IsFam lam q0 R ∧ R 0 = R0 := by
  intro hH k r lam u b bv ga h q0 R0 hN hR0
  classical
  have hex : DSExist := hH.2.2.2.1
  have hC : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P := by
    obtain ⟨P, hP, -⟩ := hR0.2
    exact ⟨P, hP⟩
  have hfam := (GlobalTheory.T.numericalFamily_shape_gaps k r lam u b bv ga h q0 hN).2
  have key : ∀ ν : Fin (2 * r + k + 1) → ℤ, ∃ R : Rep k r,
      (∑ a, (ν a).natAbs ≤ q0 → R.IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ))) ∧
      (ν = 0 → R = R0) := by
    intro ν
    by_cases h0 : ν = 0
    · refine ⟨R0, fun _ => ?_, fun _ => rfl⟩
      subst h0
      simpa using hR0
    · by_cases hq : ∑ a, (ν a).natAbs ≤ q0
      · obtain ⟨R, hR⟩ := hex k r _ _ (hfam ν hq).1 hC
        exact ⟨R, fun _ => hR, fun h => absurd h h0⟩
      · exact ⟨R0, fun h => absurd h hq, fun _ => rfl⟩
  choose R hR using key
  exact ⟨R, fun ν hν => (hR ν).1 hν, (hR 0).2 rfl⟩

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.PieriBound

theorem bound_cast (k M n : ℕ) (hn : n = k + M) (lam mu : Fin n → ℝ) (u : ℕ → ℝ) (b bv ga q0 : ℝ) (s : Fin n)
    (hk : 1 ≤ k) (hM : 1 ≤ M) (h1 : StrictAnti lam) (h2 : ∀ a c, ∃ z : ℤ, lam a - lam c = (z : ℝ))
    (h3 : ∀ a, ∀ i ∈ Icc 1 k, ∃ m : ℤ, lam a - u i = (m : ℝ) + 1 / 2)
    (h4 : ∀ a : Fin n, a.val < k → lam a < u (a.val + 1))
    (h5 : ∀ a : Fin n, a.val + 1 < k → u (a.val + 2) < lam a)
    (h6 : ∀ a : Fin n, a.val + 1 < k → 0 ≤ lam a ∧ lam a ≤ bv / 8)
    (h7 : ∀ a : Fin n, k ≤ a.val + 1 → -2 * bv ≤ lam a ∧ lam a ≤ -bv)
    (h8 : ∀ a, |lam a| ≤ b) (h9 : ∀ i ∈ Icc 1 k, |u i| ≤ b)
    (h10 : ∀ a c : Fin n, a < c → c.val + 1 < k → ga ≤ lam a - lam c) (h11 : 4 ≤ ga)
    (h12 : ∀ a, ∃ z : ℤ, mu a - lam a = (z : ℝ)) (h13 : StrictAnti mu)
    (h14 : ∑ a, |mu a - lam a| ≤ q0) (h15 : q0 ≤ ga / 8) (h16 : q0 ≤ bv / 4) (h17 : q0 ≤ b)
    (h18 : ∀ s', s' ≠ s → mu s - 1 ≠ mu s') :
    (∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ s' ∈ univ.erase s, |mu s - 1 - mu s'| ≤
      if (s : ℕ) + 1 < k then 64 * Real.exp 1 * Real.sqrt k * b ^ 3 else 16 * Real.exp 1 * b ^ 2 := by
  subst hn
  have hmem : ∀ i : Fin k, (i : ℕ) + 1 ∈ Icc 1 k := fun i => by
    rw [Finset.mem_Icc]; have := i.2; omega
  have key := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.sup_l2_ratio_majorant k M lam mu (fun i => u (i.val + 1)) b bv ga q0 s hk hM
    ⟨h1, h2, fun a i => h3 a _ (hmem i), fun i => h4 (Fin.castAdd M i) i.2,
      fun i j hij => by
        have := h5 (Fin.castAdd M i) (by have := j.2; simp only [Fin.val_castAdd]; omega)
        simp only [Fin.val_castAdd] at this
        show u (j.val + 1) < _
        rw [← hij]; exact this,
      h6, h7, h8, fun i => h9 _ (hmem i), h10, h11, h12, h13, h14, h15, h16, h17⟩ h18
  have e : (∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) = ∏ i : Fin k, |mu s - 1 / 2 - u (i.val + 1)| := by
    rw [Fin.prod_univ_eq_prod_range (fun i => |mu s - 1 / 2 - u (i + 1)|) k, Finset.range_eq_Ico,
      Finset.prod_Ico_add' (fun i => |mu s - 1 / 2 - u i|) 0 k 1]
    rfl
  rw [e]; exact key

theorem lowering_bound : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → ∀ s, (∏ i ∈ Icc 1 k, |lam s + (ν s : ℝ) - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - 1 - (lam t + (ν t : ℝ))| ≤ b ^ 4 := by
  intro k r lam u b bv ga h q0 hN ν hν s
  obtain ⟨⟨hb, hbv, -, hq, -⟩, hf⟩ := GlobalTheory.T.numericalFamily_shape_gaps k r lam u b bv ga h q0 hN
  obtain ⟨-, -, -, hgap⟩ := hf ν hν
  obtain ⟨hk, hHC, h3, h4, h5, h6, h7, h8, h9, h10, -, -, hga, -, hbig⟩ := hN
  have hq0 : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
  have key := bound_cast k (2 * r + 1) (2 * r + k + 1) (by omega) lam (fun a => lam a + (ν a : ℝ)) u b bv ga q0 s hk
    (by omega) hHC.1
    (fun a c => by
      obtain ⟨m, hm⟩ := hHC.2 a
      obtain ⟨m', hm'⟩ := hHC.2 c
      exact ⟨m - m', by push_cast at hm hm' ⊢; linarith⟩) h3 h4 h5 h6 h7 h8 h9 h10 (by linarith)
    (fun a => ⟨ν a, by ring⟩) (fun a c hac => by have := hgap a c hac; show _ < _; linarith)
    (by
      have : ((n1 ν : ℕ) : ℝ) ≤ q0 := by exact_mod_cast hν
      refine le_trans (le_of_eq ?_) this
      unfold n1
      push_cast
      refine Finset.sum_congr rfl fun a _ => ?_
      simp)
    (by linarith) (by linarith) (by linarith)
    (fun t ht => by
      rcases lt_or_gt_of_ne ht with hlt | hlt
      · have := hgap t s hlt
        intro e; linarith
      · have := hgap s t hlt
        intro e; linarith)
  refine key.trans ?_
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hb0 : (0 : ℝ) ≤ b := by linarith
  split_ifs
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hs : Real.sqrt k ≤ k := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hkn : (k : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hp : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 :=
      le_self_pow₀ (by linarith) (by norm_num)
    have h64 : 64 * Real.exp 1 * Real.sqrt k ≤ b := by
      have : Real.exp 1 * Real.sqrt k ≤ 3 * k := mul_le_mul he hs (Real.sqrt_nonneg _) (by norm_num)
      norm_num at hbig hp hkn ⊢
      nlinarith
    calc _ ≤ b * b ^ 3 := mul_le_mul_of_nonneg_right h64 (by positivity)
      _ = b ^ 4 := by ring
  · have h16 : 16 * Real.exp 1 ≤ b ^ 2 := by nlinarith
    calc _ ≤ b ^ 2 * b ^ 2 := mul_le_mul_of_nonneg_right h16 (by positivity)
      _ = b ^ 4 := by ring

end GlobalTheory.PieriBound
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.unitaryGl_projection_level_sum_sq_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, (∀ s, Lev ε (F s) (μ - Pi.single s 1) (j + 2) (pr s (Pi.single c w))) ∧ ∑ s, ‖pr s (Pi.single c w)‖ ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.lev_proj_and_sum_sq_le | exact GlobalTheory.lev_proj_and_sum_sq_le | (intros; apply GlobalTheory.lev_proj_and_sum_sq_le <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem quotMeas_ae_mem_and_measurable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → SideG k r z π u μW μN μG νq → (∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r) ∧ (∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V), ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq) ∧ (∀ a, AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => lenA k r z (Matrix.of x) a) νq) ∧ ∀ l, IsBes R z π l → ∀ w ∈ R.sm, AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => l (R.σ (Matrix.of x) w)) νq := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq hR hS
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  have hae : ∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r := by
    obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
    exact Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  have hmeas : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} := by
    convert (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl using 1
    ext x
    simp
  have hrestr : νq.restrict {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} = νq :=
    Measure.restrict_eq_self_of_ae_mem hae
  have hcont : ∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V),
      ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq := by
    intro V _ _ φ hφ
    have hof : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : Mx k r)) := continuous_id
    have h1 : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x))
        {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} :=
      hφ.comp hof.continuousOn (fun x hx => hx)
    have h2 := h1.aestronglyMeasurable (μ := νq) hmeas
    rwa [hrestr] at h2
  refine ⟨hae, hcont, ?_, ?_⟩
  · intro a
    exact (hcont ℝ _ (GlobalTheory.LengthCont.lenA_continuousOn k r z hz hT a)).aemeasurable
  · intro l hl w hw
    exact hcont Wp _ (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp l hl.1 hl.2.1 hl.2.2.2 w hw).1

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapUnitary

theorem diag_single {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    PI.UpqRep.Jm ε * Matrix.single b a (1 : ℂ) * PI.UpqRep.Jm ε
      = ((Formalism.REAL.sgn ε a b : ℝ) : ℂ) • Matrix.single b a (1 : ℂ) := by
  ext i j
  unfold PI.UpqRep.Jm Formalism.REAL.sgn
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
  by_cases h : b = i ∧ a = j
  · obtain ⟨rfl, rfl⟩ := h
    cases ε a <;> cases ε b <;> simp
  · simp [h]

theorem adj_unit {n : ℕ} (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (a b : Fin n) :
    (Qᴴ * PI.UpqRep.Jm ε * Q) * (Q⁻¹ * Matrix.single a b 1 * Q)ᴴ * (Qᴴ * PI.UpqRep.Jm ε * Q)
      = ((Formalism.REAL.sgn ε a b : ℝ) : ℂ) • (Q⁻¹ * Matrix.single b a 1 * Q) := by
  have h1 : Q * Qᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hQ
  have hi : Q⁻¹ = Qᴴ := Matrix.inv_eq_right_inv h1
  have h2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, Q * (Qᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hi, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_single, star_one, ← Matrix.smul_mul, ← Matrix.mul_smul, ← diag_single]
  simp only [Matrix.mul_assoc, h2]

theorem isUnitary_of_isE : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → Formalism.REAL.IsUnitary ε E := by
  intro hK k r ε mu R hR Q E hQ hE a b x y
  obtain ⟨-, -, hlin, -, -, hadj⟩ := GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hR
  have hH : Formalism.QuantumDeterminants.Hpk k r = Qᴴ * PI.UpqRep.Jm ε * Q := hQ.1.2.symm
  have h0 : R.dC 0 (y : R.H) = 0 := by
    have := hlin 0 0 1 y y.2
    simpa using this
  have hs : ∀ (c : ℂ) Y, R.dC (c • Y) (y : R.H) = c • R.dC Y (y : R.H) := fun c Y => by
    have := hlin Y 0 c y y.2
    rwa [add_zero, h0, add_zero] at this
  rw [Submodule.coe_inner, Submodule.coe_inner, hE, hE, hadj _ _ x.2 _ y.2, hH, adj_unit ε Q hQ.2, hs,
    inner_smul_right]

end GlobalTheory.CapUnitary
end
