module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle497
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle062
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2622
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero

@[expose] public section

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

noncomputable section

namespace GlobalTheory.HeatMod

section Values

variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}

def germConstHom (q : Z ⟶ Sp R) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_id_scal_eq_germConstHom (q : Z ⟶ Sp R) (z : Z) (a : R) :
    gs (𝟙 Z) z ⊤ (scal q a) = germConstHom q z a := by
  rw [gs_eq (𝟙 Z) z ⊤ trivial]; rfl

theorem gs_constFn_eq_germConstHom (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (a : R) :
    gs r z ⊤ (constFn p ⊤ a) = germConstHom (r ≫ p) z a := by
  have : constFn p ⊤ a = (p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) := by
    unfold constFn
    rw [← Scheme.Hom.appLE_eq_app]; rfl
  exact (congrArg (gs r z ⊤) this).trans ((gs_eq r z ⊤ trivial _).trans rfl)

theorem sval_sub_constFn_smul {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ Sp R)
    (s s' : LB.Sec (LB.LinComb L φ ε)) (a : R) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (s' - constFn p ⊤ a • s) r z J = sval s' r z J - germConstHom (r ≫ p) z a * sval s r z J := by
  have hm := hJ.mem φ r
  have h₁ : sval (s' - constFn p ⊤ a • s) r z J + sval (constFn p ⊤ a • s) r z J = sval s' r z J :=
    (gs_add r z _ hm _ _).symm.trans (congrArg (gs r z _) (sub_add_cancel _ _))
  have h₂ : sval (constFn p ⊤ a • s) r z J = germConstHom (r ≫ p) z a * sval s r z J :=
    (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
      ((gs_res r z le_top hm _).trans (gs_constFn_eq_germConstHom p r z a)) rfl)
  rw [← h₁, h₂, add_sub_cancel_right]

end Values

theorem shiftEq_of_sub_constFn_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (mu α : Q.X) (σ σ' : Q.SecB k α) (σ₁ σ₁' : Q.SecB k (α + k • mu)) (c e e₁ : R), ShiftEq Q k mu α σ σ₁ 0 σ₁ → ShiftEq Q k mu α (σ' - constFn Q.P.A.hom ⊤ e • σ) (σ₁' - constFn Q.P.A.hom ⊤ e₁ • σ₁) c σ₁ → ShiftEq Q k mu α σ' σ₁' (c + e₁ - e) σ₁ := by
  intro R _ _ Q k mu α σ σ' σ₁ σ₁' c e e₁ h₀ h₁ u hu hc z J hJ
  have a₀ := h₀ u hu hc z J hJ
  have a₁ := h₁ u hu hc z J hJ
  rw [sval_sub_constFn_smul _ _ _ _ _ _ hJ, sval_sub_constFn_smul _ _ _ _ _ _ hJ, Over.w, Over.w,
    gs_id_scal_eq_germConstHom] at a₁
  rw [gs_id_scal_eq_germConstHom, map_zero, zero_mul, add_zero] at a₀
  rw [gs_id_scal_eq_germConstHom, map_sub, map_add (f := _)]
  linear_combination a₁ + germConstHom (DegPre.BF Q (FractionRing R)).hom z e * a₀

end GlobalTheory.HeatMod
end
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat

theorem IsInv.apply_constFn {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) (hinv : IsInv G v dd) (O : G.left.Opens) (r : R) :
    dd O (constFn G.hom O r) = 0 := by

  have key : ∀ (U : G.left.Opens) (hU : IsAffineOpen U) (hle : U ≤ O),
      (G.left.presheaf.map (homOfLE hle).op).hom (dd O (constFn G.hom O r)) = 0 := by
    intro U hU hle
    let g : Sp Γ(G.left, U) ⟶ G.left := hU.fromSpec
    let φ : R →+* Γ(G.left, U) := (Spec.preimage (g ≫ G.hom)).hom
    have hφ : g ≫ G.hom = spMap φ := by simp [φ, spMap]
    have hgU : ⊤ ≤ g ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
    have hgO : ⊤ ≤ g ⁻¹ᵁ O := hgU.trans (g.preimage_mono hle)

    have e : (dualMap φ).comp (algebraMap R (DualNumber R)) =
        (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))).comp φ := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    have hv : (tv v).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) :=
      (Over.w (tv v)).trans (Category.comp_id _)
    have h2 : (spMap (dualMap φ) ≫ (tv v).left) ≫ G.hom = (tEpsG (g ≫ G.hom)).hom := by
      show _ = spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g ≫ G.hom
      refine (Category.assoc _ _ _).trans ((congrArg (spMap (dualMap φ) ≫ ·) hv).trans ?_)
      rw [hφ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
    let g' : tEpsG (g ≫ G.hom) ⟶ G :=
      Over.homMk (spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g) (Category.assoc _ _ _)
    let v' : tEpsG (g ≫ G.hom) ⟶ G := Over.homMk (spMap (dualMap φ) ≫ (tv v).left) h2
    have htr : IsTr G φ g v (g' * v').left := ⟨g', v', rfl, rfl, rfl⟩
    have hval := hinv.2 _ φ g _ O (constFn G.hom O r) hφ hgO htr

    have hw : (g' * v').left ≫ G.hom =
        spMap ((algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))).comp φ) := by
      refine (Over.w (g' * v')).trans ?_
      show spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g ≫ G.hom = _
      rw [hφ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h0 : (valR (g' * v').left O (constFn G.hom O r)).snd = 0 := by
      by_cases hO : ⊤ ≤ (g' * v').left ⁻¹ᵁ O
      · rw [GlobalTheory.ArcPts.SecValue.valR_constFn G.hom _ _ hw O hO r]
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      · rw [valR, dite_eq_right hO]
        rfl
    rw [h0, ← GlobalTheory.HolHom.valR_res g hle _ hgU] at hval
    rw [← GlobalTheory.DetRatio.valR_fromSpec hU ((G.left.presheaf.map (homOfLE hle).op).hom (dd O (constFn G.hom O r)))]
    exact hval.symm
  refine G.left.sheaf.eq_of_locally_eq' (fun k : {U : G.left.Opens // IsAffineOpen U ∧ U ≤ O} => k.1) O
    (fun k => homOfLE k.2.2) ?_ _ 0 fun k => ?_
  · intro x hx
    obtain ⟨U, hU, hxU, hUO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hxU⟩
  · exact (key k.1 k.2.1 k.2.2).trans (map_zero _).symm

end GlobalTheory.Heat
end
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

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Heat.TermDescent

theorem gs_top_appLE {Y X : Scheme.{0}} (φ : Y ⟶ X) (y : Y) (U : X.Opens) (h : ⊤ ≤ φ ⁻¹ᵁ U) (a : Γ(X, U)) :
    gs (𝟙 Y) y ⊤ ((φ.appLE U ⊤ h).hom a) = gs φ y U a := by
  have e := gs_appLE φ U ⊤ h (𝟙 Y) y trivial a
  rwa [Category.id_comp] at e

theorem gs_of_valR {S : Type} [CommRing S] {X : Scheme.{0}} (x x' : Sp S ⟶ X) (V : X.Opens) (f : Γ(X, V))
    (c : Sˣ) (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ x' ⁻¹ᵁ V) (e : valR x' V f = c * valR x V f) (y : Sp S) :
    gs x' y V f = (gm (𝟙 (Sp S)) y ⊤ (unitOn c)).val * gs x y V f := by
  rw [valR, valR, dif_pos h, dif_pos h'] at e
  have e' : (x'.appLE V ⊤ h').hom f = (unitOn c).val * (x.appLE V ⊤ h).hom f := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom e
    rw [map_mul] at this
    simpa [unitOn] using this
  rw [← gs_top_appLE x' y V h', ← gs_top_appLE x y V h, e', gs_mul _ y ⊤ trivial, gs_unit _ y ⊤ trivial]

theorem gen_ratio {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {S : Type} [CommRing S] {K : Type} [Fintype K]
    {φ φ' : K → (Sp S ⟶ X)} (ε : K → ℤ) (e : φ = φ') (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε)) (ht : t.IsGen) (ht' : t'.IsGen) : ∃ c : Sˣ, ∀ y J, Good L y J →
      val t' (𝟙 _) y J = gm (𝟙 (Sp S)) y ⊤ (unitOn c) * val t (𝟙 _) y J := by
  subst e
  let u := LB.mulGen L φ ε φ (fun k => - ε k) t' (LB.invGen L φ ε t)
  have hu : u.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ ht' (DVR.invGen_isGen _ _ _ _ ht)
  have hF : FormEq (Sum.elim φ φ) (Sum.elim ε fun k => - ε k) (K' := PEmpty.{1}) PEmpty.elim PEmpty.elim := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib,
      mul_inv_cancel, Fintype.prod_empty]
  obtain ⟨t₀, -, h₀⟩ := exists_gen hL hF u hu
  have le : (⊤ : (Sp S).Opens) ≤ LB.wchart L (K := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  let v : Γ(Sp S, ⊤)ˣ := res le (t₀.s PEmpty.elim)
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.toMonoidHom v, fun y J hJ => ?_⟩
  have hv : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.toMonoidHom v) = v := by
    ext; simp [unitOn]
  have e₀ : gm (𝟙 (Sp S)) y ⊤ v = val t₀ (𝟙 _) y J :=
    (gm_res _ y le trivial _).trans (val_of t₀ _ y J PEmpty.elim fun k => k.elim).symm
  rw [hv, e₀, h₀ _ _ y J hJ, val_mul hJ, val_inv, inv_mul_cancel_right]

end GlobalTheory.Heat.TermDescent

namespace GlobalTheory.Heat
open GlobalTheory.Heat.TermDescent

theorem isTerm_of_isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (k : ℕ) (α : Q.X) (τ : SecM Y.q.left Q.P.L k) (J : Type) (V : J → Q.P.A.left.Opens) (j : J → Fin 1 → Q.P.L.ι), ⨆ i, Y.q.left ⁻¹ᵁ V i = ⊤ → (∀ i, Y.q.left ⁻¹ᵁ V i ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (j i)) → (∀ i, IsWt Y α (Y.q.left ⁻¹ᵁ V i) (rsT (τ.f (j i)) (Y.q.left ⁻¹ᵁ V i))) → ∃ σ' : Q.SecB k α, IsTerm Y k α σ' τ := by
  intro R _ _ Q O _ _ _ oa Y k α τ Jt V j hcov hle hwt
  have hL := Q.P.isLB
  obtain ⟨hs, hqc⟩ := GlobalTheory.T.ray_q_surjective_and_quasiCompact Y
  have := Ray.smooth_q Y
  let t := (Y.Φ Y.H (𝟙 _)).s α
  have ht : t.IsGen := (Y.Φ Y.H (𝟙 _)).isGen α
  have hF : FormEq (Sum.elim (fun _ : Fin 1 => 𝟙 _ ≫ Y.q.left) (DegPre.gtφT Q Y.H Y.q α))
      (Sum.elim (fun _ => (k : ℤ)) (fun a => - DegPre.gtε a)) (fun i => Y.q.left ≫ DegPre.famφB Q α i)
      (DegPre.famε k) := by
    intro U _ h
    have e := GlobalTheory.RayEv.formEq_term Y k α U h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp, zpow_neg,
      Finset.prod_inv_distrib] at e ⊢
    rw [← e, mul_inv_cancel_right]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF (pullMulSec τ (𝟙 _) (LB.invGen Q.P.L _ _ t) (DVR.invGen_isGen _ _ _ _ ht))
  have vσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) J, Good Q.P.L z J →
      sval σ r z J = sval τ r z J * ((val t r z J)⁻¹).val := by
    intro Z r z J hJ
    rw [hσ Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, Category.comp_id]
    exact congrArg (fun u => sval τ r z J * u.val) (val_inv (z := z) (J := J) t r)
  have vt : ∀ (T : Over (Sp R)) (x : T ⟶ Y.H) (y : T.left) J, Good Q.P.L y J →
      val t x.left y J = val ((Y.Φ T x).s α) (𝟙 _) y J := by
    intro T x y J hJ
    obtain ⟨-, h₂⟩ := (GlobalTheory.TorusModel.isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))
    have e := h₂ α y J hJ
    rw [Category.comp_id] at e
    exact e.symm
  have hdesc : ∀ (S : Type) [CommRing S] [IsLocalRing S] (g₁ g₂ : Sp S ⟶ Y.H.left), g₁ ≫ Y.q.left = g₂ ≫ Y.q.left →
      ∀ J, Good Q.P.L (closedPoint S) J → sval σ g₁ (closedPoint S) J = sval σ g₂ (closedPoint S) J := by
    intro S _ _ g₁ g₂ hg J hJ
    have hA : g₂ ≫ Y.H.hom = g₁ ≫ Y.H.hom := by
      rw [← Over.w Y.q, ← Category.assoc, ← Category.assoc, hg]
    obtain ⟨φ, hφ⟩ : ∃ φ : R →+* S, g₁ ≫ Y.H.hom = spMap φ :=
      ⟨(Spec.preimage (g₁ ≫ Y.H.hom)).hom, (Spec.map_preimage _).symm⟩
    let x₁ : Over.mk (spMap φ) ⟶ Y.H := Over.homMk g₁ hφ
    let x₂ : Over.mk (spMap φ) ⟶ Y.H := Over.homMk g₂ (hA.trans hφ)
    have hx : x₂ ≫ Y.q = x₁ ≫ Y.q := Over.OverMorphism.ext hg.symm
    have hc : ∀ χ, ∃ c : Sˣ, ∀ y J, Good Q.P.L y J → val ((Y.Φ _ x₂).s χ) (𝟙 _) y J =
        gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn c) * val ((Y.Φ _ x₁).s χ) (𝟙 _) y J := fun χ =>
      gen_ratio Q.P.L hL DegPre.gtε (by rw [Ray.Φ_b, Ray.Φ_b, hx]) _ _ ((Y.Φ _ x₁).isGen χ) ((Y.Φ _ x₂).isGen χ)
    choose c hc using hc
    obtain ⟨i, hi⟩ : ∃ i, g₁ (closedPoint S) ∈ Y.q.left ⁻¹ᵁ V i := by
      have : g₁ (closedPoint S) ∈ (⨆ i, Y.q.left ⁻¹ᵁ V i : Y.H.left.Opens) := by rw [hcov]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    have hi₂ : g₂ (closedPoint S) ∈ Y.q.left ⁻¹ᵁ V i := by
      show (g₂ ≫ Y.q.left) (closedPoint S) ∈ V i
      rw [← hg]; exact hi
    have h₁ : ⊤ ≤ g₁ ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V i) :=
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of S) g₁ hi).ge
    have h₂ : ⊤ ≤ g₂ ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V i) :=
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of S) g₂ hi₂).ge
    have hw := hwt i S φ x₁ x₂ c g₁ g₂ rfl rfl h₁ h₂ hx hc
    have hg' := gs_of_valR g₁ g₂ _ _ (c α) h₁ h₂ hw (closedPoint S)
    have s_i : ∀ g : Sp S ⟶ Y.H.left, g (closedPoint S) ∈ Y.q.left ⁻¹ᵁ V i →
        gs g (closedPoint S) (Y.q.left ⁻¹ᵁ V i) (rsT (τ.f (j i)) (Y.q.left ⁻¹ᵁ V i)) =
          (trF (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ)) g (closedPoint S) (j i)
            (fun _ => J (g ≫ Y.q.left))).val * sval τ g (closedPoint S) J := by
      intro g hm
      have er : rsT (τ.f (j i)) (Y.q.left ⁻¹ᵁ V i) = resG _ (hle i) (τ.f (j i)) := dif_pos (hle i)
      rw [er]
      exact (gs_res g _ (hle i) hm _).trans (sec_trans τ g _ (hle i hm) (hJ.mem _ g))
    have htr : trF (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ)) g₂ (closedPoint S) (j i)
        (fun _ => J (g₂ ≫ Y.q.left)) = trF (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ)) g₁ (closedPoint S) (j i)
        (fun _ => J (g₁ ≫ Y.q.left)) := by
      simp only [trF]
      rw [hg]
    set C : ((Sp S).presheaf.stalk (closedPoint S))ˣ := gm (𝟙 (Sp S)) (closedPoint S) ⊤ (unitOn (c α)) with hC
    have sv : sval τ g₂ (closedPoint S) J = C.val * sval τ g₁ (closedPoint S) J := by
      have e := hg'
      rw [s_i g₂ hi₂, s_i g₁ hi, htr, mul_left_comm] at e
      exact (Units.mul_right_inj _).1 e
    have vv : val t g₂ (closedPoint S) J = C * val t g₁ (closedPoint S) J :=
      (vt _ x₂ _ J hJ).trans ((hc α _ J hJ).trans (congrArg (C * ·) (vt _ x₁ _ J hJ).symm))
    rw [vσ _ g₁ _ J hJ, vσ _ g₂ _ J hJ, sv, vv, mul_inv_rev, Units.val_mul]
    linear_combination (-(sval τ g₁ (closedPoint S) J * ((val t g₁ (closedPoint S) J)⁻¹).val)) * C.mul_inv

  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_section_descent_flat_surjective_quasiCompact Q.P.L hL Y.q.left inferInstance hs hqc (DegPre.famφB Q α) (DegPre.famε k) σ hdesc
  refine ⟨b, fun T x y J hJ => ?_⟩
  have e1 := hb _ x.left y J hJ
  rw [vσ _ _ y J hJ, vt T x y J hJ] at e1
  show sval τ x.left y J = sval b (x.left ≫ Y.q.left) y J * _
  rw [← e1, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]

end GlobalTheory.Heat
end
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DerFieldExt

theorem cover' (X : Scheme.{0}) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens} (h : W ≤ W₀) :
    W ≤ ⨆ i : {f : Γ(X, W₀) // X.basicOpen f ≤ W}, X.basicOpen i.1 := by
  intro y hy
  obtain ⟨f, hf, hx⟩ := hW.exists_basicOpen_le (V := W) ⟨y, hy⟩ (h hy)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hx⟩

theorem sep' (X : Scheme.{0}) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens} (h : W ≤ W₀) (s t : Γ(X, W))
    (e : ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG X k s = resG X k t) : s = t :=
  X.sheaf.eq_of_locally_eq' (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => X.basicOpen i.1)
    W (fun i => homOfLE i.2) (cover' X hW h) s t (fun i => e i.1 i.2)

theorem exists_field : ∀ (Z : Scheme.{0}) (U : Z.Opens), IsAffineOpen U → ∀ δ : Γ(Z, U) → Γ(Z, U),
    (∀ a b, δ (a + b) = δ a + δ b) → (∀ a b, δ (a * b) = a * δ b + b * δ a) →
    ∃ d : Fld Z, IsField U d ∧ d U = δ := by
  intro X W₀ hW d₀ hadd hmul
  have H : ∀ f : Γ(X, W₀), ∃ δ : Γ(X, X.basicOpen f) → Γ(X, X.basicOpen f),
      (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧
      ∀ a, δ (resG X (X.basicOpen_le f) a) = resG X (X.basicOpen_le f) (d₀ a) := by
    intro f
    haveI := hW.isLocalization_basicOpen f
    obtain ⟨δ, h1, h2, h3⟩ := GlobalTheory.LocDerExt.der_exists f (RingHom.id _)
      (fun a => resG X (X.basicOpen_le f) (d₀ a)) (fun a b => by simp only [hadd, map_add (f := _)])
      (fun a b => by simp only [hmul, map_add (f := _), map_mul, RingHom.id_apply]; rfl)
    exact ⟨δ, h1, fun a b => by simpa using h2 a b, h3⟩
  choose δ δadd δmul δres using H
  have compat : ∀ (f g : Γ(X, W₀)) (k : X.basicOpen g ≤ X.basicOpen f) (s : Γ(X, X.basicOpen f)),
      resG X k (δ f s) = δ g (resG X k s) := by
    intro f g k s
    haveI := hW.isLocalization_basicOpen f
    refine GlobalTheory.LocDerExt.der_unique f (resG X k)
      (fun s => resG X k (δ f s)) (fun s => δ g (resG X k s)) (fun a b => ?_)
      (fun a b => ?_) (fun a => ?_) s
    · simp only [δmul, map_add (f := _), map_mul]
    · simp only [δmul, map_mul]
    · change resG X k (δ f (resG X (X.basicOpen_le f) a)) =
        δ g (resG X k (resG X (X.basicOpen_le f) a))
      rw [GlobalTheory.LocDerExt.res_res X, δres, δres, GlobalTheory.LocDerExt.res_res X]
  have G : ∀ (W : X.Opens), W ≤ W₀ → ∀ s : Γ(X, W), ∃ t : Γ(X, W),
      ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG X k t = δ f (resG X k s) := by
    intro W h s
    obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing'
      (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => X.basicOpen i.1)
      W (fun i => homOfLE i.2) (cover' X hW h)
      (fun i => δ i.1 (resG X i.2 s)) (fun i j => by
        have e : X.basicOpen (i.1 * j.1) = X.basicOpen i.1 ⊓ X.basicOpen j.1 := X.basicOpen_mul _ _
        have ki : X.basicOpen (i.1 * j.1) ≤ X.basicOpen i.1 := e.le.trans inf_le_left
        have kj : X.basicOpen (i.1 * j.1) ≤ X.basicOpen j.1 := e.le.trans inf_le_right
        have k : X.basicOpen i.1 ⊓ X.basicOpen j.1 ≤ X.basicOpen (i.1 * j.1) := e.ge
        have e' : resG X ki (δ i.1 (resG X i.2 s)) = resG X kj (δ j.1 (resG X j.2 s)) := by
          rw [compat _ _ ki, compat _ _ kj, GlobalTheory.LocDerExt.res_res X, GlobalTheory.LocDerExt.res_res X]
        have e'' := congrArg (resG X k) e'
        rw [GlobalTheory.LocDerExt.res_res X, GlobalTheory.LocDerExt.res_res X] at e''
        exact e'')
    exact ⟨t, fun f k => ht ⟨f, k⟩⟩
  choose t ht using G
  classical
  refine ⟨fun W s => if h : W ≤ W₀ then t W h s else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro W h a b
    simp only [dif_pos h]
    refine sep' X hW h _ _ (fun f k => ?_)
    rw [map_add (f := _), ht W h _ f k, ht W h _ f k, ht W h _ f k, map_add (f := _), δadd]
  · intro W h a b
    simp only [dif_pos h]
    refine sep' X hW h _ _ (fun f k => ?_)
    rw [map_add (f := _), map_mul, map_mul, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_mul, δmul]
  · intro W W' h' h a
    simp only [dif_pos h, dif_pos (h'.trans h)]
    refine sep' X hW (h'.trans h) _ _ (fun f k => ?_)
    refine Eq.trans ?_ (GlobalTheory.LocDerExt.res_res X h' k _).symm
    rw [ht W' _ _ f k, ht W h a f (k.trans h'), GlobalTheory.LocDerExt.res_res X]
  · funext a
    simp only [dif_pos (le_refl W₀)]
    refine sep' X hW le_rfl _ _ (fun f k => ?_)
    rw [ht W₀ _ _ f k, δres]

end GlobalTheory.DerFieldExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ModelRelDim

theorem relDim_and_isVB_omega : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) Y.t.G.hom ∧ GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega Y.t.G) (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) := by
  intro E _ _ _ H Dw l Xo c Y
  have := Y.t.semi
  have hsm : Smooth Y.t.G.hom := Y.t.semi.smooth
  have : IsIso (spMap (RingHom.id c.F)) := by
    unfold spMap
    rw [CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  have : IsDominant Y.jQ := ⟨Y.jQ_dense⟩
  have hdom : IsDominant (Y.jQ ≫ pullback.fst Y.s (spMap (RingHom.id c.F))) := inferInstance
  have hg : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) Y.t.G.hom :=
    GlobalTheory.smoothOfRelativeDimension_of_isPullback_isDominant _ _ _ _ _ Y.t.G.hom Y.oF.t.G.hom Y.m.φ _
      Y.m.cart.1 hdom hsm (GlobalTheory.ObjDim.smoothOfRelativeDimension Y.oF)
  exact ⟨hg, GlobalTheory.LieVB.isVB_omega Y.t.G _⟩

end GlobalTheory.ModelRelDim
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth


theorem _root_.GlobalTheory.T.exists_harmonicPoly_localInvariant_nonpos_char0 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∃ P₁ ∈ harmA (Dw := Dw) c a n, ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), CharZero (IsLocalRing.ResidueField T.V) → ∀ e k : ℕ, 0 < e → GlobalTheory.FactorDepth.nuLocOf C e k (MvPolynomial.map io P₁) ≤ 0 := by
  first | exact @GlobalTheory.ResZeroDepth.exists_harmA_nuLocOf_nonpos | exact GlobalTheory.ResZeroDepth.exists_harmA_nuLocOf_nonpos | (intros; apply GlobalTheory.ResZeroDepth.exists_harmA_nuLocOf_nonpos <;> assumption)
end
