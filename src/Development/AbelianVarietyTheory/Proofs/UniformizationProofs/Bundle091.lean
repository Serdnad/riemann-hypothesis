module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005

@[expose] public section

open AlgebraicGeometry CategoryTheory
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable local instance (priority := high) grpObjPullbackForUniformization091
    {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.FormalValue

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NormGen

theorem exists_factor {V W : Type} [CommRing V] [CommRing W] (I : Ideal V) (φ : V →+* W) (e : ℕ) {Z : Scheme.{0}}
    (r : Z ⟶ Sp W) (σ : Z ⟶ Sp (V ⧸ I ^ (e + 1))) (h : σ ≫ thick V I e = r ≫ spMap φ) :
    ∃ ρ : Z ⟶ Sp (W ⧸ I.map φ ^ (e + 1)), ρ ≫ thick W (I.map φ) e = r := by
  let ψ : CommRingCat.of W ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ r.appTop
  have hr : Z.toSpecΓ ≫ Spec.map ψ = r := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hk : I.map φ ^ (e + 1) ≤ RingHom.ker ψ.hom := by
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro v hv
    have e₁ : CommRingCat.ofHom φ ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ I ^ (e + 1)))).inv ≫ σ.appTop := by
      rw [Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop,
        ← Scheme.Hom.comp_appTop, h]
    have e₂ := congrArg (fun q => q.hom v) e₁
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      Ideal.Quotient.eq_zero_iff_mem.2 hv, map_zero] at e₂
    exact e₂
  refine ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ ψ.hom hk)), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← hr]
  rfl

theorem gs_valR {A : Type} [CommRing A] {X Z : Scheme.{0}} (ρ : Z ⟶ Sp A) (y : Sp A ⟶ X) (V : X.Opens)
    (ht : ⊤ ≤ y ⁻¹ᵁ V) (s : Γ(X, V)) (z : Z) :
    gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (valR y V s)) = gs (ρ ≫ y) z V s := by
  rw [valR, dite_eq_left ht, Iso.hom_inv_id_apply, ← gs_pull ρ y z V (ht trivial)]
  exact gs_res ρ z ht trivial _

theorem valR_id {A : Type} [CommRing A] (a : A) :
    valR (𝟙 (Sp A)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = a := by
  rw [valR, dite_eq_left (show ⊤ ≤ 𝟙 (Sp A) ⁻¹ᵁ ⊤ from le_top)]
  have : Scheme.Hom.appLE (𝟙 (Sp A)) ⊤ ⊤ le_top = 𝟙 _ := by
    exact (Category.id_comp _).trans ((Sp A).presheaf.map_id _)
  rw [this]
  exact Iso.inv_hom_id_apply _ _

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_limit_unit (U : PreU I D A G) {W : Type} [CommRing W] [IsLocalRing W] (φ : R →+* W)
    [IsAdicComplete (I.map φ) W] (x : Sp W ⟶ G.left) (hx : x ≫ G.hom = spMap φ) (b : Sp W ⟶ D.P.A.left)
    (hb : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → xe ≫ (U.gt e).pG.left = r ≫ b)
    {jL : U.P.L.L.ι} {jM : D.P.L.ι} (hL : ⊤ ≤ x ⁻¹ᵁ U.P.L.L.U jL) (hM : ⊤ ≤ b ⁻¹ᵁ D.P.L.U jM) :
    ∃ a : Γ(Sp W, ⊤)ˣ, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, gm r z ⊤ a * gw (U.w e) xe z jM (fun _ => jL) = 1 := by
  choose y hy using exists_lift_thick I G φ x hx
  have mL : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (fstG I e G).left (xe z) ∈ U.P.L.L.U jL := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ U.P.L.L.U jL) h).mpr (hL (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  have mM : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (U.gt e).pG.left (xe z) ∈ D.P.L.U jM := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ D.P.L.U jM) (hb e Z r xe h)).mpr (hM (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  let O : ∀ e, (thickObj R I e G).left.Opens := fun e =>
    (D.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓ (U.P.L.L.pull (fstG I e G).left).U (fun _ => jL)
  let s : ∀ e, Γ((thickObj R I e G).left, O e)ˣ := fun e => (U.w e).s (fun _ => jM, fun _ => jL)
  have mO : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, xe z ∈ O e := fun e Z r xe h z =>
    ⟨mem_pull.2 (mM e Z r xe h z), mem_pull.2 (mL e Z r xe h z)⟩
  have ht : ∀ e, ⊤ ≤ y e ⁻¹ᵁ O e := fun e z _ => mO e _ _ _ (hy e) z
  have hc : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))
      (valR (y (e + 1)) (O (e + 1)) (s (e + 1)).val) = valR (y e) (O e) (s e).val := fun e => by
    have := isLocalRing_quotient_pow (ne_top_of_isHausdorff (I.map φ)) e
    have := fstG_mono (I := I) (G := G) (e + 1)
    have e₁ : thickTrans W (I.map φ) e ≫ y (e + 1) = y e ≫ thickMap R I e G := by
      rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, hy,
        show thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left from thickMap_comp_fGl I e G, hy,
        ← Category.assoc, thickTrans_comp]
    apply toStkA_injective
    refine (toStkA_map_valR _ _ _ _ (ht _) _).trans (Eq.trans ?_ (toStkA_valR_eq_gs _ _ _ (ht _) _).symm)
    refine (gs_unit _ _ _ (mO (e + 1) _ (thickTrans W (I.map φ) e ≫ thick W (I.map φ) (e + 1)) _ (by
      rw [Category.assoc, hy, Category.assoc]) _) _).trans (Eq.trans ?_ (gs_unit _ _ _ (mO e _ _ _ (hy e) _) _).symm)
    refine congrArg Units.val ((congrArg (fun q => gm q _ (O (e + 1)) (s (e + 1))) e₁).trans ?_)
    exact U.w_compat e _ (y e) _ jM jL (mM e _ _ _ (hy e) _) (mL e _ _ _ (hy e) _)
  obtain ⟨a, ha⟩ := exists_unit_limit (I.map φ) _ hc fun e => isUnit_valR _ _ (ht e) _
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.toMonoidHom a, fun e Z r xe h z => ?_⟩
  obtain ⟨ρ, rfl⟩ := exists_factor I φ e r (xe ≫ (thickObj R I e G).hom) (by
    rw [← hx, ← Category.assoc r, ← h, Category.assoc, Category.assoc]
    exact congrArg (xe ≫ ·) pullback.condition.symm)
  have := fstG_mono (I := I) (G := G) e
  obtain rfl : xe = ρ ≫ y e := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc, Category.assoc, hy]
  apply Units.ext
  have H := congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) (ha e)
  simp only [map_mul, map_one] at H
  rw [gs_mul ρ z ⊤ trivial, gs_valR _ _ _ (ht e), gs_unit _ _ _ (mO e _ _ _ h z), gs_eq ρ z ⊤ trivial 1, map_one,
    map_one] at H
  refine Eq.trans (congrArg₂ (· * ·) ?_ rfl) H
  rw [← gs_unit _ z ⊤ trivial, ← gs_valR ρ (thick W (I.map φ) e) ⊤ le_top]
  refine congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) ?_
  have k := valR_spMap (Ideal.Quotient.mk (I.map φ ^ (e + 1))) (𝟙 (Sp W)) ⊤ le_top
    ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a.val)
  rw [valR_id, Category.comp_id] at k
  exact k

theorem one_pG (U : PreU I D A G) {T : Over (Spec (CommRingCat.of R))} (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T.left)
    (oe : Z ⟶ (thickObj R I e G).left) (h : oe ≫ (fstG I e G).left = r ≫ (1 : T ⟶ G).left) :
    oe ≫ (U.gt e).pG.left = r ≫ (1 : T ⟶ D.P.A).left := by
  have hf : ∀ (H : Over (Spec (CommRingCat.of R))) [GrpObj H],
      eSec (thickObj R I e H) ≫ (fstG I e H).left = thick R I e ≫ eSec H := fun H _ => by
    show eSec (thickObj R I e H) ≫ pullback.fst H.hom (thick R I e) = _
    simp [eSec]
  have hp : eSec (thickObj R I e G) ≫ (U.gt e).pG.left = thick R I e ≫ eSec D.P.A := by
    have := (U.gt e).q_hom
    have h : eSec (thickObj R I e G) ≫ (U.gt e).q.left = eSec (thickObj R I e D.P.A) :=
      congrArg (·.left) (IsMonHom.one_hom (U.gt e).q)
    rw [← hf D.P.A, ← h, Category.assoc]
    rfl
  have hσ : (oe ≫ (thickObj R I e G).hom) ≫ thick R I e = r ≫ T.hom := by
    rw [← Over.w (1 : T ⟶ G), ← Category.assoc r, ← h, Category.assoc, Category.assoc]
    exact congrArg (oe ≫ ·) pullback.condition.symm
  have := fstG_mono (I := I) (G := G) e
  have ho : oe = (oe ≫ (thickObj R I e G).hom) ≫ eSec (thickObj R I e G) := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc _ (eSec _), hf, ← Category.assoc _ (thick R I e), hσ,
      one_left, Category.assoc]
  rw [ho, Category.assoc _ (eSec _), hp, ← Category.assoc _ (thick R I e), hσ, one_left, Category.assoc]

theorem gw_change (U : PreU I D A G) (e : ℕ) {Z : Scheme.{0}} (xe : Z ⟶ (thickObj R I e G).left) (z : Z)
    {p : Z ⟶ G.left} {q : Z ⟶ D.P.A.left} (hp : xe ≫ (fstG I e G).left = p) (hq : xe ≫ (U.gt e).pG.left = q)
    {j j' : D.P.L.ι} {k k' : U.P.L.L.ι} (hj : q z ∈ D.P.L.U j) (hj' : q z ∈ D.P.L.U j') (hk : p z ∈ U.P.L.L.U k)
    (hk' : p z ∈ U.P.L.L.U k') :
    gw (U.w e) xe z j (fun _ => k) =
      gm q z _ (D.P.L.g j j') * (gm p z _ (U.P.L.L.g k k'))⁻¹ * gw (U.w e) xe z j' (fun _ => k') := by
  subst hp hq
  have w := (isGen_iff _).1 (U.w_gen e) Z xe z j j' (fun _ => k) (fun _ => k') hj hj' (mem_pull.2 hk) (mem_pull.2 hk')
  rw [gm_pull_g _ _ xe z _ _ (mem_pull.2 hk) (mem_pull.2 hk')] at w
  exact w

theorem exists_normAt : AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (a : Multiplicative D.X →* Wˣ) (x : TA V W ⟶ G), U.TorPt a x → ∃ ν, U.NormAt x ν := by
  intro V _ _ _ _ D A G _ _ U W _ _ _ hW a x hx
  have := hW.2.2.2.2
  obtain ⟨jx, hjx⟩ := exists_chart U.P.L.isLB (x.left (cpt W))
  obtain ⟨jo, hjo⟩ := exists_chart U.P.L.isLB ((1 : TA V W ⟶ G).left (cpt W))
  obtain ⟨jM, hjM⟩ := exists_chart D.P.isLB ((1 : TA V W ⟶ D.P.A).left (cpt W))
  replace hjx := (top_le_iff_cpt (A := W) x.left _).2 hjx
  replace hjo := (top_le_iff_cpt (A := W) (1 : TA V W ⟶ G).left _).2 hjo
  replace hjM := (top_le_iff_cpt (A := W) (1 : TA V W ⟶ D.P.A).left _).2 hjM
  obtain ⟨α, hα⟩ := exists_limit_unit U (algebraMap V W) x.left (Over.w x) (1 : TA V W ⟶ D.P.A).left
    (fun e Z r xe h => (hx e Z r xe h).1) hjx hjM
  obtain ⟨β, hβ⟩ := exists_limit_unit U (algebraMap V W) (1 : TA V W ⟶ G).left (Over.w _) (1 : TA V W ⟶ D.P.A).left
    (fun e Z r xe h => one_pG U (T := TA V W) e Z r xe h) hjo hjM
  obtain ⟨ν, hν⟩ := exists_gen_of_local (V := W) U.P.L.L U.P.L.isLB (K := Fin 2) ![x.left, (1 : TA V W ⟶ G).left] ![-1, 1]
  have ht : ⊤ ≤ LB.wchart U.P.L.L (K := Fin 2) ![x.left, (1 : TA V W ⟶ G).left] ![jx, jo] := fun y _ =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [hjx trivial, hjo trivial]
  obtain ⟨n, hn⟩ : ∃ n : Γ(Sp W, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JG), Good U.P.L.L z JG →
      val ν r z JG = (gm (r ≫ x.left) z _ (U.P.L.L.g (JG (r ≫ x.left)) jx))⁻¹ *
        gm (r ≫ (1 : TA V W ⟶ G).left) z _ (U.P.L.L.g (JG (r ≫ (1 : TA V W ⟶ G).left)) jo) * gm r z ⊤ n := by
    refine ⟨res (X := Sp W) ht (ν.s ![jx, jo]), fun Z r z JG hG => ?_⟩
    refine (gen_trans hν r z (hG.mem _ r) (ht trivial)).trans (congrArg₂ (· * ·) ?_ (gm_res r z ht trivial _).symm)
    rw [trF, Fin.prod_univ_two]
    exact congrArg₂ (· * ·) (zpow_neg_one _) (zpow_one _)
  refine ⟨UU.scaleGen (β * α⁻¹ * n⁻¹ : Γ(Sp W, ⊤)ˣ) ν, UU.scaleGen_isGen _ hν,
    fun e Z (r : Z ⟶ Sp W) xe oe h₁ h₂ z JG J hG hJ => ?_⟩
  have q₁ := (hx e Z r xe h₁).1
  have q₂ := one_pG U (T := TA V W) e Z r oe h₂
  have m : ∀ {X : Scheme.{0}} {f : Sp W ⟶ X} {O : X.Opens}, ⊤ ≤ f ⁻¹ᵁ O → (r ≫ f) z ∈ O := fun h => h trivial
  have a₁ := eq_inv_of_mul_eq_one_right (hα e Z r xe h₁ z)
  have a₂ := eq_inv_of_mul_eq_one_right (hβ e Z r oe h₂ z)
  have w₁ : U.wv e xe z JG J = _ := (congrArg₂ (fun j k => gw (U.w e) xe z (J j) (fun _ => JG k)) q₁ h₁).trans
    (gw_change U e xe z h₁ q₁ (hJ _) (m hjM) (hG _) (m hjx))
  have w₂ : U.wv e oe z JG J = _ := (congrArg₂ (fun j k => gw (U.w e) oe z (J j) (fun _ => JG k)) q₂ h₂).trans
    (gw_change U e oe z h₂ q₂ (hJ _) (m hjM) (hG _) (m hjo))
  rw [a₁] at w₁
  rw [a₂] at w₂
  have v := val_scaleGen (β * α⁻¹ * n⁻¹) ν r hG
  rw [hn Z r z JG hG, map_mul, map_mul, map_inv, map_inv] at v
  refine (congrArg₂ (· * ·) v w₂).trans (Eq.trans ?_ w₁.symm)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.NormGen
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU.TorMul

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def germScal {W : Type} [CommRing W] {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (z : Z) :
    W →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom)

theorem gs_scal {W : Type} [CommRing W] {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (z : Z) (c : W) :
    gs (𝟙 Z) z ⊤ (scal (R := W) r c) = germScal r z c :=
  gs_eq (𝟙 Z) z ⊤ trivial _

def push (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
  pushHom (isGrpPullback_pullback G (thick R I e)) T

theorem push_inj (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    Function.Injective (push I e G T) := fun y y' h =>
  Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) h) ((Over.w y).trans (Over.w y').symm))

theorem push_surj (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    Function.Surjective (push I e G T) := fun x =>
  ⟨Over.homMk (pullback.lift x.left T.hom (Over.w x)) (pullback.lift_snd _ _ _),
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩

def Coord {e : ℕ} (g : GtCoord I D e G) {W : Type} [CommRing W]
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (r : T.left ⟶ Spec (CommRingCat.of W))
    (a : Multiplicative D.X →* Wˣ) (y : T ⟶ thickObj R I e G) : Prop :=
  GlobalTheory.TorusCoord.im g y = 1 ∧ ∀ (χ : D.X) (z : T.left) (J), Good D.P.L z J →
    val (g.t χ) y.left z J = Units.map (germScal r z : W →* _) (a (Multiplicative.ofAdd χ))

section
variable {e : ℕ} (g : GtCoord I D e G) {W : Type} [CommRing W]
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (r : T.left ⟶ Spec (CommRingCat.of W))

theorem coord_one : Coord g r 1 (1 : T ⟶ thickObj R I e G) :=
  ⟨GlobalTheory.TorusCoord.im_one g, fun χ z J hJ => (GlobalTheory.TorusCoord.val_unit g χ hJ).trans (map_one _).symm⟩

theorem val_mul_of (hG : GlobalFnsSt) {y y' : T ⟶ thickObj R I e G} (h : GlobalTheory.TorusCoord.im g y = 1)
    (χ : D.X) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val (g.t χ) (y * y').left z J = val (g.t χ) y.left z J * val (g.t χ) y'.left z J := by
  have k := GlobalTheory.TorusCoord.val_t_mul_points g hG χ y y' z J hJ
  have c : GlobalTheory.TorusCoord.cubeVal g χ z J y y' = 1 := by
    unfold GlobalTheory.TorusCoord.cubeVal
    rw [h]
    exact (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj T) hJ).face₂ _ _
  rwa [c, _root_.mul_one] at k

theorem coord_mul (hG : GlobalFnsSt) {a a' : Multiplicative D.X →* Wˣ} {y y' : T ⟶ thickObj R I e G}
    (h : Coord g r a y) (h' : Coord g r a' y') : Coord g r (a * a') (y * y') := by
  refine ⟨by rw [GlobalTheory.TorusCoord.im_mul, h.1, h'.1, _root_.mul_one], fun χ z J hJ => ?_⟩
  exact (val_mul_of g hG h.1 χ z J hJ).trans
    ((congrArg₂ (· * ·) (h.2 χ z J hJ) (h'.2 χ z J hJ)).trans (map_mul _ _ _).symm)

theorem coord_inv (hG : GlobalFnsSt) {a : Multiplicative D.X →* Wˣ} {y : T ⟶ thickObj R I e G}
    (h : Coord g r a y) : Coord g r a⁻¹ y⁻¹ := by
  refine ⟨?_, fun χ z J hJ => ?_⟩
  · have := GlobalTheory.TorusCoord.im_mul g y y⁻¹
    rw [mul_inv_cancel, GlobalTheory.TorusCoord.im_one, h.1, _root_.one_mul] at this
    exact this.symm
  · have k := (((GlobalTheory.TorusCoord.val_unit g χ hJ).symm.trans
      (GlobalTheory.TorusCoord.val_congr g χ (mul_inv_cancel y).symm z J)).trans (val_mul_of g hG h.1 χ z J hJ)).symm
    exact ((eq_inv_of_mul_eq_one_right k).trans (congrArg (·⁻¹) (h.2 χ z J hJ))).trans (map_inv _ _).symm
end

theorem comp_one_left {S : Scheme.{0}} (B : Over S) [GrpObj B] {T T' : Over S} (ρ : T' ⟶ T) :
    ρ.left ≫ (1 : T ⟶ B).left = (1 : T' ⟶ B).left :=
  congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_one ρ)

theorem torPt_iff (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W] (a : Multiplicative D.X →* Wˣ)
    (x : TA R W ⟶ G) : U.TorPt a x ↔ ∀ (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (ρ : (Over.map (thick R I e)).obj T ⟶ TA R W) (y : T ⟶ thickObj R I e G),
      push I e G T y = ρ ≫ x → Coord (U.gt e) ρ.left a y := by
  constructor
  · intro h e T ρ y hy
    obtain ⟨h₁, h₂⟩ := h e T.left ρ.left y.left (congrArg (fun q => q.left) hy)
    refine ⟨Over.OverMorphism.ext (h₁.trans (comp_one_left D.P.A ρ)),
      fun χ z J hJ => Units.ext ((h₂ χ z J hJ).trans (gs_scal _ _ _))⟩
  · intro h e Z r xe hx
    let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (xe ≫ (thickObj R I e G).hom)
    have hw : r ≫ (TA R W).hom = (xe ≫ (thickObj R I e G).hom) ≫ thick R I e := by
      rw [← Over.w x, ← Category.assoc, ← hx, Category.assoc, Category.assoc]
      exact congrArg (xe ≫ ·) (Over.w (fstG I e G))
    let ρ : (Over.map (thick R I e)).obj T ⟶ TA R W := Over.homMk r hw
    let y : T ⟶ thickObj R I e G := Over.homMk xe rfl
    obtain ⟨h₁, h₂⟩ := h e T ρ y (Over.OverMorphism.ext hx)
    exact ⟨(congrArg (fun q => q.left) h₁).trans (comp_one_left D.P.A ρ).symm,
      fun χ z J hJ => (congrArg Units.val (h₂ χ z J hJ)).trans (gs_scal _ _ _).symm⟩

section
variable (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W]

theorem torPt_one : U.TorPt (1 : Multiplicative D.X →* Wˣ) 1 := by
  refine (torPt_iff U _ _).2 fun e T ρ y hy => ?_
  obtain rfl : y = 1 := push_inj e T (hy.trans ((MonObj.comp_one ρ).trans (map_one _).symm))
  exact coord_one _ _

theorem torPt_mul (hG : GlobalFnsSt) {a a' : Multiplicative D.X →* Wˣ} {x x' : TA R W ⟶ G}
    (h : U.TorPt a x) (h' : U.TorPt a' x') : U.TorPt (a * a') (x * x') := by
  refine (torPt_iff U _ _).2 fun e T ρ y hy => ?_
  obtain ⟨p, hp⟩ := push_surj e T (ρ ≫ x)
  obtain ⟨p', hp'⟩ := push_surj e T (ρ ≫ x')
  obtain rfl : y = p * p' := push_inj e T (by rw [hy, map_mul, hp, hp', MonObj.comp_mul])
  exact coord_mul _ _ hG ((torPt_iff U _ _).1 h e T ρ p hp) ((torPt_iff U _ _).1 h' e T ρ p' hp')

theorem torPt_inv (hG : GlobalFnsSt) {a : Multiplicative D.X →* Wˣ} {x : TA R W ⟶ G}
    (h : U.TorPt a x) : U.TorPt a⁻¹ x⁻¹ := by
  refine (torPt_iff U _ _).2 fun e T ρ y hy => ?_
  obtain ⟨p, hp⟩ := push_surj e T (ρ ≫ x)
  obtain rfl : y = p⁻¹ := push_inj e T (by rw [hy, map_inv, hp]; exact map_inv (preHom ρ) x)
  exact coord_inv _ _ hG ((torPt_iff U _ _).1 h e T ρ p hp)

theorem torPt_pow (hG : GlobalFnsSt) {a : Multiplicative D.X →* Wˣ} {x : TA R W ⟶ G}
    (h : U.TorPt a x) (k : ℕ) : U.TorPt (a ^ k) (x ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact torPt_one U
  | succ k ih => rw [pow_succ, pow_succ]; exact torPt_mul U hG ih h
end

end GlobalTheory.UU.TorMul

theorem GlobalTheory.UU.torPt_group : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (W : Type) [CommRing W] [Algebra R W], U.TorPt (1 : Multiplicative D.X →* Wˣ) 1 ∧ ∀ (a a' : Multiplicative D.X →* Wˣ) (x x' : TA R W ⟶ G), U.TorPt a x → (U.TorPt a' x' → U.TorPt (a * a') (x * x')) ∧ U.TorPt a⁻¹ x⁻¹ ∧ ∀ k : ℕ, U.TorPt (a ^ k) (x ^ k) :=
  fun hG _ _ _ _ _ _ _ _ _ U _ _ _ => ⟨TorMul.torPt_one U, fun _ _ _ _ h =>
    ⟨fun h' => TorMul.torPt_mul U hG h h', TorMul.torPt_inv U hG h, TorMul.torPt_pow U hG h⟩⟩

end
end
