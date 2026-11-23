module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle139
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.QkClosure

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt

attribute [local instance] gtGroup

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀]
  [Field F] [Algebra (FractionRing R) F] (f : F₀ →+* F)
  (hf : f.comp (algebraMap (FractionRing R) F₀) = algebraMap (FractionRing R) F)

theorem val_eq_of_ext {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((TF (R := R) F₀).left ⟶ D.P.A.left)}
    {ε : K → ℤ} {φ' : K' → ((TF (R := R) F₀).left ⟶ D.P.A.left)} {ε' : K' → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (t' : LB.Gen (LB.LinComb D.P.L φ' ε'))
    (h : ∀ z J, Good D.P.L z J → val t (extMap (R := R) f hf).left z J = val t' (extMap (R := R) f hf).left z J)
    {y J} (hJ : Good D.P.L y J) : val t (𝟙 _) y J = val t' (𝟙 _) y J :=
  val_corr hJ (GlobalTheory.corr_of_val_field_extension _ _ f _ D.P.L D.P.isLB _ _ _ _ _ _ t t' h) _

theorem val_tau_ext (x χ : D.X) {z J} (hJ : Good D.P.L z J) :
    val (LB.pullGen D.P.L _ _ (D.tau x χ) (jFK (R := R) F₀)) (extMap (R := R) f hf).left z J = tauVal D F x χ z J := by
  rw [val_pull hJ, tauVal, ← extMap_jFK f hf]


include f hf in
theorem exists_isIota_of_ext {x : D.X} {h' : GtPtF D F} (hh' : GtPtF.IsIota x h') : ∃ g : GtPtF D F₀, GtPtF.IsIota x g := by
  obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 hh'
  have vv : ∀ χ y J, Good D.P.L y J → val (LB.pullGen D.P.L _ _ (D.tau x χ) (jFK (R := R) F₀))
      (𝟙 (TF (R := R) F₀).left) y J = tauVal D F₀ x χ y J := fun χ y J hJ => val_pull hJ _ _ _
  obtain ⟨g, hb, hv⟩ := exists_gt (F := F₀) (cP D _ x) (fun χ => LB.pullGen D.P.L _ _ (D.tau x χ) (jFK (R := R) F₀))
    (fun χ => pullGen_isGen _ _ _ _ (tau_isGen D x χ) _) (fun χ U _ h => by
      have a : ∀ w : D.X, jFK (R := R) F₀ ≫ ptK (D.c w) = (cP D (TF (R := R) F₀) w).left := fun w =>
        (Category.assoc _ _ _).symm
      have a₀ : jFK (R := R) F₀ ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F₀ ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      rw [prod_gt, ← cPoint_add, add_comm χ x, ← a, ← a, ← a, ← a₀]
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, zpow_one]
      rw [mul_right_comm _ (h _) (h _)]) (fun y J hJ => by
      refine (val_eq_of_ext f hf _ (LB.oneGen D.P.L) (fun z J' hJ' => ?_) hJ).trans (val_one _)
      exact (val_tau_ext f hf x 0 hJ').trans ((v' 0 z J' hJ').symm.trans ((charVal_zero h' hJ').trans (val_one _).symm)))
    (fun χ χ' y J hJ => by
      refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAt hJ _ _ _))).symm.trans
        ((val_eq_of_ext f hf _ _ (fun z J' hJ' => ?_) hJ).trans (val_mul hJ _ _ _))
      have c := val_cub D.cub (extMap (R := R) f hf) hJ' (cP D _ χ) (cP D _ χ') (cP D _ x)
      rw [comp_cP, comp_cP, comp_cP] at c
      have e := charVal_add h' hJ' χ χ'
      rw [b', v' _ _ _ hJ', v' _ _ _ hJ', v' _ _ _ hJ'] at e
      refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
      exact (congrArg₂ (· * ·) (val_tau_ext f hf _ _ hJ') c).trans
        (e.trans (congrArg₂ (· * ·) (val_tau_ext f hf _ _ hJ') (val_tau_ext f hf _ _ hJ')).symm))
  exact ⟨g, (isIota_iff_val _ _).2 ⟨hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩⟩

end GlobalTheory.QkClosure

namespace GlobalTheory.QkClosure

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt

attribute [local instance] gtGroup

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀]
  [Field F] [Algebra (FractionRing R) F] (f : F₀ →+* F)
  (hf : f.comp (algebraMap (FractionRing R) F₀) = algebraMap (FractionRing R) F) {k : ℕ}

include hf

theorem isIota_gtExt {x : D.X} {h : GtPtF D F₀} (hh : GtPtF.IsIota x h) : GtPtF.IsIota x (gtExt D f hf h) := by
  obtain ⟨b, -⟩ := (isIota_iff_val _ _).1 hh
  refine (isIota_iff_val _ _).2 ⟨by rw [gtExt_b, b, comp_cP], fun χ y J hJ => ?_⟩
  rw [gtExt_val f hf _ χ hJ, tauVal, ← extMap_jFK f hf]
  exact (val_corr hJ (hh.2 χ) _).trans (val_pull hJ _ _ _)

theorem exists_qkExt (p : QkPt D F₀ k) : ∃ p' : QkPt D F k, QkExt f p p' := by
  obtain ⟨h, h₁, h₂⟩ := p.eq
  obtain rfl := (isNsmul_iff_eq _ _ _).1 h₁
  exact ⟨⟨p.y, gtExt D f hf p.g, gtExt D f hf (k • p.g), (isNsmul_iff_eq _ _ _).2 (map_nsmul _ _ _),
    isIota_gtExt f hf h₂⟩, rfl, (eq_gtExt_iff f hf _ _).1 rfl⟩

theorem qkExt_unique {p : QkPt D F₀ k} {p₁ p₂ : QkPt D F k} (h₁ : QkExt f p p₁) (h₂ : QkExt f p p₂) : p₁ = p₂ :=
  qk_ext (h₁.1.trans h₂.1.symm) (((eq_gtExt_iff f hf _ _).2 h₁.2).trans ((eq_gtExt_iff f hf _ _).2 h₂.2).symm)

theorem qkExt_inj {p₁ p₂ : QkPt D F₀ k} {p' : QkPt D F k} (h₁ : QkExt f p₁ p') (h₂ : QkExt f p₂ p') : p₁ = p₂ :=
  qk_ext (h₁.1.symm.trans h₂.1)
    (GlobalTheory.ArcExt.gtExt_injective f hf (((eq_gtExt_iff f hf _ _).2 h₁.2).symm.trans ((eq_gtExt_iff f hf _ _).2 h₂.2)))

theorem exists_qkExt_descent [IsAlgClosed F₀] [IsAlgClosed F] (hk : (k : F₀) ≠ 0) (p' : QkPt D F k) :
    ∃ p : QkPt D F₀ k, QkExt f p p' := by
  have hL : Laws := GlobalTheory.allSixLaws.1
  have hk0 : k ≠ 0 := by rintro rfl; exact hk Nat.cast_zero
  obtain ⟨h', h₁', h₂'⟩ := p'.eq
  obtain rfl := (isNsmul_iff_eq _ _ _).1 h₁'
  obtain ⟨h₀, hh₀⟩ := exists_isIota_of_ext f hf h₂'
  have e₀ : gtExt D f hf h₀ = k • p'.g := isIota_unique (isIota_gtExt f hf hh₀) h₂'
  obtain ⟨g₀, hg₀⟩ := exists_nsmul_eq hL.mulN (Or.inr hL.polBaseChange) hk0 h₀
  have ht' : k • (p'.g - gtExt D f hf g₀) = 0 := by
    rw [nsmul_sub, ← map_nsmul, hg₀, e₀, sub_self]
  obtain ⟨t, ht⟩ := GlobalTheory.ArcExt.exists_gtExt_of_torsion f hf hL hk _ ht'
  have ht0 : k • t = 0 := GlobalTheory.ArcExt.gtExt_injective f hf (by rw [map_nsmul, ht, ht', map_zero])
  have e : p'.g = gtExt D f hf (g₀ + t) := by rw [map_add (f := _), ht, add_sub_cancel]
  refine ⟨⟨p'.y, g₀ + t, h₀, (isNsmul_iff_eq _ _ _).2 ?_, hh₀⟩, rfl, (eq_gtExt_iff f hf _ _).1 e⟩
  rw [nsmul_add, ht0, add_zero, hg₀]

end GlobalTheory.QkClosure

namespace GlobalTheory.Mum

theorem qkPt_algClosure_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → (∀ p : QkPt D (Kb R) N, ∃! p' : QkPt D F N, QkExt em.toRingHom p p') ∧ ∀ p' : QkPt D F N, ∃! p : QkPt D (Kb R) N, QkExt em.toRingHom p p' := by
  intro R _ _ _ D F _ _ _ em N hN
  have hf := em.comp_algebraMap
  have : CharZero (Kb R) := (RingHom.charZero_iff (algebraMap (FractionRing R) (Kb R)).injective).1 inferInstance
  have hk : (N : Kb R) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨fun p => ?_, fun p' => ?_⟩
  · obtain ⟨p', hp'⟩ := GlobalTheory.QkClosure.exists_qkExt em.toRingHom hf p
    exact ⟨p', hp', fun q hq => GlobalTheory.QkClosure.qkExt_unique em.toRingHom hf hq hp'⟩
  · obtain ⟨p, hp⟩ := GlobalTheory.QkClosure.exists_qkExt_descent em.toRingHom hf hk p'
    exact ⟨p, hp, fun q hq => GlobalTheory.QkClosure.qkExt_inj em.toRingHom hf hq hp⟩

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.RescaleLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem isUnit_of_basicOpen_top {Y : Scheme.{0}} (s : Γ(Y, ⊤)) (h : Y.basicOpen s = ⊤) : IsUnit s :=
  Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => (Y.mem_basicOpen _ x hx).1 (h.ge hx)

abbrev fnSp (A : Type) [CommRing A] : A →+* Γ(Sp A, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem appTop_comp_spMap {R₀ A : Type} [CommRing R₀] [CommRing A] (α : R₀ →+* A) {Z : Scheme.{0}}
    (s : Z ⟶ Sp A) (r : R₀) : (s ≫ spMap α).appTop.hom (fnSp R₀ r) = s.appTop.hom (fnSp A (α r)) := by
  have nat := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom α))
  rw [Scheme.Hom.comp_appTop]
  exact congrArg s.appTop.hom nat.symm

def fnOn {R₀ : Type} [CommRing R₀] (W : (Sp R₀).Opens) : R₀ →+* Γ(W.toScheme, ⊤) :=
  W.ι.appTop.hom.comp (fnSp R₀)

theorem appTop_fnOn {R₀ A : Type} [CommRing R₀] [CommRing A] (W : (Sp R₀).Opens) (α : R₀ →+* A) {Z : Scheme.{0}}
    (t : Z ⟶ W.toScheme) (s : Z ⟶ Sp A) (h : t ≫ W.ι = s ≫ spMap α) (r : R₀) :
    t.appTop.hom (fnOn W r) = s.appTop.hom (fnSp A (α r)) := by
  have e : t.appTop.hom (fnOn W r) = (t ≫ W.ι).appTop.hom (fnSp R₀ r) := by
    rw [Scheme.Hom.comp_appTop]; rfl
  rw [e, h, appTop_comp_spMap]

theorem gm_fnOn {R₀ A : Type} [CommRing R₀] [CommRing A] (W : (Sp R₀).Opens) (α : R₀ →+* A) {Z : Scheme.{0}}
    (t : Z ⟶ W.toScheme) (s : Z ⟶ Sp A) (h : t ≫ W.ι = s ≫ spMap α) (r : R₀) (u : Γ(W.toScheme, ⊤)ˣ) (v : Aˣ)
    (hu : (u : Γ(W.toScheme, ⊤)) = fnOn W r) (hv : (v : A) = α r) (z : Z) :
    gm t z ⊤ u = gm s z ⊤ (unitOn v) := by
  rw [GlobalTheory.UU.gm_top t, GlobalTheory.UU.gm_top s]
  congr 1
  apply Units.ext
  show t.appTop.hom (u : Γ(W.toScheme, ⊤)) = s.appTop.hom (fnSp A (v : A))
  rw [hu, hv, appTop_fnOn W α t s h r]

theorem isUnit_fnOn {R₀ : Type} [CommRing R₀] (f r : R₀) (N : ℕ) (hr : r ∣ f ^ N) :
    IsUnit (fnOn ((Sp R₀).basicOpen (fnSp R₀ f)) r) := by
  set W := (Sp R₀).basicOpen (fnSp R₀ f)
  have hf : IsUnit (fnOn W f) := isUnit_of_basicOpen_top _ (by
    have e := Scheme.preimage_basicOpen W.ι (fnSp R₀ f)
    rw [Scheme.Opens.ι_preimage_self] at e
    exact e.symm)
  exact isUnit_of_dvd_unit (map_dvd (fnOn W) hr |>.trans (by rw [map_pow])) (hf.pow N)

end GlobalTheory.RescaleLift

namespace GlobalTheory.RescaleLift

theorem exists_psiOn_rescale {R₀ : Type} [CommRing R₀] [IsDomain R₀] (D₁ : DegPre R₀) (κ₀ : D₁.X → (FractionRing R₀)ˣ)
    {W W' : (Sp R₀).Opens} (ψ : PsiOn D₁ W) (hle : W' ≤ W) (u : D₁.X → Γ(W'.toScheme, ⊤)ˣ) (r : D₁.X → R₀)
    (hu : ∀ y, (u y : Γ(W'.toScheme, ⊤)) = fnOn W' (r y)) (hr : ∀ y, algebraMap R₀ (FractionRing R₀) (r y) = κ₀ y) :
    ∃ ψW : PsiOn (GlobalTheory.PolDeg.rescale D₁ κ₀) W', ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J,
      Good D₁.P.L z J → val (ψW.psi y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ (Sp R₀).homOfLE hle) z J := by
  let m : W'.toScheme ⟶ W.toScheme := (Sp R₀).homOfLE hle
  have hm : m ≫ W.ι = W'.ι := Scheme.homOfLE_ι _ _
  have hφ : ∀ y : D₁.X, m ≫ (toUnit (TW W) ≫ D₁.c y).left = (toUnit (TW W') ≫ D₁.c y).left := fun y => by
    show m ≫ W.ι ≫ (D₁.c y).left = W'.ι ≫ (D₁.c y).left
    rw [← Category.assoc, hm]
  choose b hb vb using fun y : D₁.X => exists_gen D₁.P.isLB (K' := PUnit)
    (φ' := fun _ => (toUnit (TW W') ≫ D₁.c y).left) (ε' := fun _ => -1)
    (fun U _ k => Finset.prod_congr rfl fun _ _ => congrArg (fun q => k q ^ (-1 : ℤ)) (hφ y))
    (GlobalTheory.UU.scaleGen (u y) (LB.pullGen D₁.P.L _ _ (ψ.psi y) m))
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ.psi_gen y) m))
  have ev : ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J, Good D₁.P.L z J →
      val (b y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ m) z J := fun y Z t z J hJ =>
    (vb y Z t z J hJ).trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)))
  refine ⟨{ psi := b, psi_gen := hb, psi_eq := fun y => corr_of_val D₁.P.isLB fun z J hJ => ?_ }, ev⟩
  refine (val_pull hJ _ _ _).trans ((ev y _ z J hJ).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  refine (congrArg₂ (· * ·) ?_ ?_).trans (GlobalTheory.UU.val_scaleGen (unitOn (κ₀ y)) (D₁.psi y) _ hJ).symm
  · refine gm_fnOn W' (algebraMap R₀ (FractionRing R₀)) _ _ ?_ (r y) _ _ (hu y) (hr y).symm z
    rw [Category.id_comp, Category.id_comp, morphismRestrict_ι]
  · refine GlobalTheory.ArcSpecialise.psiOn_generic ψ y _ _ ?_ hJ
    rw [Category.assoc, hm, Category.id_comp, Category.id_comp, morphismRestrict_ι]

end GlobalTheory.RescaleLift

namespace GlobalTheory.RescaleLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

end GlobalTheory.RescaleLift
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

theorem rescale_tau_val {R' : Type} [CommRing R'] [IsDomain R'] (D : DegPre R') (g : D.X → (FractionRing R')ˣ)
    (a b : D.X) {z : (TK R').left} {J : ((TK R').left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    val ((rescale D g).tau a b) (𝟙 _) z J =
      gm (𝟙 (TK R').left) z ⊤ (unitOn (g (a + b))) * (gm (𝟙 (TK R').left) z ⊤ (unitOn (g a)))⁻¹ *
        (gm (𝟙 (TK R').left) z ⊤ (unitOn (g b)))⁻¹ * val (D.tau a b) (𝟙 _) z J := by
  have hJ' : Good (rescale D g).P.L z J := hJ
  unfold DegPre.tau
  simp only [val_mul hJ', val_mul hJ, val_inv]
  erw [val_inv, val_inv, val_inv]
  have e1 : ∀ χ, val ((rescale D g).psi χ) (𝟙 _) z J = gm (𝟙 (TK R').left) z ⊤ (unitOn (g χ)) * val (D.psi χ) (𝟙 _) z J :=
    fun χ => GlobalTheory.UU.val_scaleGen _ _ _ hJ
  have e2 : val (rescale D g).rigK (𝟙 _) z J = val D.rigK (𝟙 _) z J := rfl
  erw [e1 (a + b), e1 a, e1 b, e2]
  simp only [mul_inv]
  ac_rfl

theorem half_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f f' : D.X → D.X → (FractionRing R')ˣ) (g : D.X → (FractionRing R')ˣ), Half Q ρ D e f → (∀ a b, f a b = g (a + b) * (g a)⁻¹ * (g b)⁻¹ * f' a b) → Half Q ρ (rescale D g) e f' := by
  intro R _ _ R' _ _ Q ρ D e f f' g h hf
  obtain ⟨β, β₂, w, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  refine ⟨β, β₂, w, h₁, h₂, h₃, h₄, h₅, fun κ hκ a b z J J' hJ hJ' => ?_⟩
  have H := h₆ κ hκ a b z J J' hJ hJ'
  have E := rescale_tau_val D g a b hJ'
  have key : ∀ x y : D.X, gm (𝟙 (TK R').left) z ⊤ (unitOn (f x y)) = gm (𝟙 (TK R').left) z ⊤ (unitOn (g (x + y))) *
      (gm (𝟙 (TK R').left) z ⊤ (unitOn (g x)))⁻¹ * (gm (𝟙 (TK R').left) z ⊤ (unitOn (g y)))⁻¹ *
        gm (𝟙 (TK R').left) z ⊤ (unitOn (f' x y)) := fun x y => by
    rw [hf x y]; simp only [unitOn, map_mul, map_inv]
  erw [E]
  refine Eq.trans ?_ H
  erw [key a b]
  ac_rfl

end GlobalTheory.PolDeg
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.QuadIff

variable {R : Type} [CommRing R] [IsDomain R]

def germU (z : (TK R).left) : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ :=
  (gm (𝟙 (TK R).left) z ⊤).comp (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom.toMonoidHom)

theorem bimult_iff (D : DegPre R) : D.TauBimult ↔ ∀ (a a' b : D.X) z J, Good D.P.L z J →
    val (D.tau (a + a') b) (𝟙 _) z J *
      val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      val (D.tau a b) (𝟙 _) z J * val (D.tau a' b) (𝟙 _) z J :=
  ⟨fun h a a' b _ _ hJ => (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h a a' b) (𝟙 _)).trans (val_mul hJ _ _ _)),
    fun h a a' b => corr_of_val D.P.isLB fun y J hJ =>
      (val_mul hJ _ _ _).trans ((h a a' b y J hJ).trans (val_mul hJ _ _ _).symm)⟩

theorem val_tau_eq (D : DegPre R) {z : (TK R).left} {J} (hJ : Good D.P.L z J) (a b : D.X) :
    val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem val_psi_rescale (D : DegPre R) (g : D.X → (FractionRing R)ˣ) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (χ : D.X) : val ((rescale D g).psi χ) (𝟙 (TK R).left) z J =
      germU z (g χ) * val (D.psi χ) (𝟙 (TK R).left) z J :=
  GlobalTheory.UU.val_scaleGen (Y := (TK R).left) (L := D.P.L) (unitOn (g χ)) (D.psi χ) (𝟙 _) hJ

theorem val_tau_rescale (D : DegPre R) (g : D.X → (FractionRing R)ˣ) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (a b : D.X) : val ((rescale D g).tau a b) (𝟙 (TK R).left) z J =
      germU z (g (a + b)) * (germU z (g a))⁻¹ * (germU z (g b))⁻¹ * val (D.tau a b) (𝟙 (TK R).left) z J := by
  have key : ∀ (A B C p q r s : ((TK R).left.presheaf.stalk z)ˣ),
      A * p * (B * q)⁻¹ * (C * r)⁻¹ * s = A * B⁻¹ * C⁻¹ * (p * q⁻¹ * r⁻¹ * s) := fun A B C p q r s => by
    simp only [_root_.mul_inv]
    ac_rfl
  refine (val_tau_eq (rescale D g) hJ a b).trans (Eq.trans ?_ (congrArg (_ * ·) (val_tau_eq D hJ a b)).symm)
  refine Eq.trans ?_ (key _ _ _ _ _ _ _)
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (val_psi_rescale D g hJ (a + b))
    (congrArg (·⁻¹) (val_psi_rescale D g hJ a))) (congrArg (·⁻¹) (val_psi_rescale D g hJ b))) rfl

end GlobalTheory.PolDeg.QuadIff
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg

theorem gm_spMap_unitOn {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) (y : Sp B) :
    gm (spMap f) y ⊤ (unitOn u) = gm (𝟙 (Sp B)) y ⊤ (unitOn (Units.map f.toMonoidHom u)) := by
  apply Units.ext
  rw [gm_val _ y ⊤ trivial, gm_val _ y ⊤ trivial]
  have nat := congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  exact congrArg ((Sp B).presheaf.germ ⊤ y trivial).hom nat.symm

theorem evenDefect_baseChange : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β → v.IsGen → (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) → GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v → GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) → ∀ h : D₁.X → (FractionRing R₁)ˣ, EvenDefect D₁ h → EvenDefect D₂ fun χ => Units.map gam.toMonoidHom (h (xe χ)) := by
  intro R₁ _ _ R₂ _ _ σ D₁ D₂ β v xe gam hgam gp hv hc _ hψ h hE χ z J₂ hJ₂
  beta_reduce
  have hgam' : spMap gam ≫ jK R₁ = jK R₂ ≫ spMap σ := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hgam
  have cx : ∀ a, D₂.xK a ≫ β = spMap gam ≫ D₁.xK (xe a) := fun a => by
    show (jK R₂ ≫ (D₂.c a).left) ≫ β = spMap gam ≫ jK R₁ ≫ (D₁.c (xe a)).left
    rw [Category.assoc, hc, ← Category.assoc, ← hgam', Category.assoc]
  have cn : D₂.xK (-χ) = D₂.xK χ ≫ (ι[D₂.P.A]).left := by
    show (toUnit _ ≫ D₂.c (-χ)).left = _
    rw [GlobalTheory.PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]
  choose J₁ hJ₀ using fun φ : (TK R₂).left ⟶ D₁.P.A.left => exists_chart D₁.P.isLB (φ z)
  have hJ₁ : Good D₁.P.L z J₁ := hJ₀
  have vψ : ∀ a, val (D₁.psi (xe a)) (spMap gam) z J₁ =
      (gw v (D₂.xK a) z (J₁ (D₂.xK a ≫ β)) (J₂ (D₂.xK a)))⁻¹ * val (D₂.psi a) (𝟙 _) z J₂ := fun a => by
    have := GlobalTheory.CubTransport.val_pmaps (fun _ => cx a) (hψ a) (𝟙 _) hJ₁ hJ₂
    rwa [Fintype.prod_unique, Category.id_comp, Category.id_comp, zpow_neg_one] at this
  have hcorr := corr_of_val D₁.P.isLB (t := LB.mulGen _ _ _ _ _ (D₁.psi (-(xe χ))) (LB.pullGen _ _ _ D₁.sym (D₁.xK (xe χ))))
    (t' := GlobalTheory.UU.scaleGen (unitOn (h (xe χ))) (D₁.psi (xe χ))) fun y J hJ => by
      rw [val_mul hJ, val_pull hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, Category.id_comp]
      exact hE (xe χ) y J hJ
  have e := val_corr hJ₁ hcorr (spMap gam)
  have hg : gm (spMap gam) z ⊤ (unitOn (h (xe χ))) =
      gm (𝟙 (TK R₂).left) z ⊤ (unitOn (Units.map gam.toMonoidHom (h (xe χ)))) := gm_spMap_unitOn gam _ z
  rw [val_mul hJ₁, val_pull hJ₁, GlobalTheory.UU.val_scaleGen _ _ _ hJ₁, hg, ← cx, ← map_neg xe χ, vψ, vψ] at e
  have hs := GlobalTheory.PsiRing.val_sym_comp GlobalTheory.globalFns_holds gp hv (D₂.xK χ) z hJ₁ hJ₂
  rw [← cn] at hs
  rw [hs] at e
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory.PolDeg
end
end
