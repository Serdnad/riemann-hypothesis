module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSheafComplexPairingTensorAssocDesc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaceSubMid
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.EtC.PicSpec

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  Eq.symm (NatTrans.naturality_apply φ.hom g.op x)

theorem sec_map_comp {R : Type} [CommRing R] {F G K : Shv R} (ψ : F ⟶ G) (φ : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map φ (Sec.map ψ x) = Sec.map (ψ ≫ φ) x := rfl

theorem sec_eq_zero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (a : Sec F U) : a = 0 := by
  have h := hF.eq_of_src (𝟙 F) 0
  have : Sec.map (𝟙 F) a = Sec.map (0 : F ⟶ F) a := by rw [h]
  simpa [Sec.map] using this

theorem res_isZero {R : Type} [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) :=
  CochainComplex.isZero_of_isStrictlyGE ((injectiveResolution F).cochainComplex) 0 s hs

theorem resι_d {R : Type} [CommRing R] (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  unfold resι res
  rw [Category.assoc, (injectiveResolution F).ι'.comm 0 1]
  simp

theorem unitSec_mul {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v := by
  unfold unitSec ofRings.sec
  exact map_add (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom)
    (show (Scheme.Γ ⋙ unitsF).obj (op U) from ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v))

theorem unitSec_res {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  unfold unitSec ofRings.sec
  have := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op
  have h2 := congrArg (fun f => f.hom (show (Scheme.Γ ⋙ unitsF).obj (op U) from ULift.up (Additive.ofMul u))) this
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2.symm

theorem glMat_map {U V : Scheme.{0}} (g : V ⟶ U) (y : Sx (ofCat (glCat 1)) 1 U) :
    glMat (((ofCat (glCat 1)).obj (op (SimplexCategory.mk 1))).map g.op y) =
      Matrix.GeneralLinearGroup.map g.appTop.hom (glMat y) := rfl

theorem generalLinearGroup_det_map_fin_one {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (M : GL (Fin 1) A) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f M) =
      Units.map f.toMonoidHom (Matrix.GeneralLinearGroup.det M) := by
  ext
  simp

theorem glMat_δ1 {U : Scheme.{0}} (y : Sx (ofCat (glCat 1)) 2 U) :
    glMat (((ofCat (glCat 1)).δ 1).app (op U) y) =
      glMat (((ofCat (glCat 1)).δ 0).app (op U) y) * glMat (((ofCat (glCat 1)).δ 2).app (op U) y) := by
  have h : ((show ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 from y).map' 0 2) =
      (show ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 from y).map' 0 1 ≫
        (show ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 from y).map' 1 2 :=
    ComposableArrows.map'_comp _ 0 1 2
  exact h

theorem face_nat {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 2 U) (i : Fin 3) :
    (L.app (op (SimplexCategory.mk 1))).app (op U) ((E.δ i).app (op U) x) =
      ((ofCat (glCat 1)).δ i).app (op U) ((L.app (op (SimplexCategory.mk 2))).app (op U) x) := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (SimplicialObject.δ_naturality L i) (op U)) x
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
  exact this

theorem lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  unfold lineUnit Sx.res
  rw [NatTrans.naturality_apply (L.app (op (SimplexCategory.mk 1))) g.op x, glMat_map, generalLinearGroup_det_map_fin_one]

theorem lineUnit_face {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 2 U) :
    lineUnit L (x.face 1) = lineUnit L (x.face 0) * lineUnit L (x.face 2) := by
  unfold lineUnit Sx.face
  rw [face_nat, face_nat, face_nat, glMat_δ1, map_mul]

def fam {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res ℤ Gm).X s) U
  | 1, s, h, _, x => Sec.map ((res ℤ Gm).XIsoOfEq (show (0 : ℤ) = s by omega)).hom
      (Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)))
  | _, _, _, _, _ => 0

theorem fam_zero {E : Spc} (L : E ⟶ ofCat (glCat 1)) (s : ℤ) (h : -((0 : ℕ) : ℤ) + 1 = s) (U : Scheme.{0})
    (x : Sx E 0 U) : fam L 0 s h U x = 0 := rfl

theorem fam_add_two {E : Spc} (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ) (h : -((p + 2 : ℕ) : ℤ) + 1 = s)
    (U : Scheme.{0}) (x : Sx E (p + 2) U) : fam L (p + 2) s h U x = 0 := rfl

theorem fam_one {E : Spc} (L : E ⟶ ofCat (glCat 1)) (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0})
    (x : Sx E 1 U) : fam L 1 0 h U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
  simp [fam, Sec.map]

theorem fam_nat {E : Spc} (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0})
    (g : V ⟶ U) (x : Sx E p U) : Sec.res g (fam L p s h U x) = fam L p s h V (x.res g) := by
  match p with
  | 0 => simp [fam_zero]
  | 1 =>
    simp only [fam]
    rw [sec_map_res, sec_map_res, unitSec_res, lineUnit_res]
  | p + 2 => simp [fam_add_two]

theorem sec_map_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem sec_map_add {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ _ _

theorem ev_zero_cochain {E : Spc} {I : Cx ℤ} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (0 : Cochain ((chains ℤ).obj E) I n) p s h U x = 0 := by
  have hZero := CupSpec.ev_zero (I := I) p s h U x
  exact hZero

theorem fam_cocycle {E : Spc} (L : E ⟶ ofCat (glCat 1)) (α : Cochain ((chains ℤ).obj E) (res ℤ Gm) 1)
    (hα : ∀ p s h U x, ev α p s h U x = fam L p s h U x) : δ 1 2 α = 0 := by
  have hExt := CupSpec.ev_ext (δ 1 2 α) 0
  apply hExt
  intro p t ht U x
  rw [ev_zero_cochain]
  have hDeltaSucc := CupSpec.ev_δ_succ (m := 2) (by norm_num) α U
  match p with
  | 0 =>
    obtain rfl : t = 2 := by omega
    have hDeltaZero := CupSpec.ev_δ_zero (m := 2) (by norm_num) α U 1 2 (by simp) ht x
    rw [hDeltaZero, hα, fam_zero, sec_map_zero]
  | 1 =>
    obtain rfl : t = 1 := by omega
    have key : ev (δ 1 2 α) 1 1 ht U x = Sec.map ((res ℤ Gm).d 0 1) (ev α 1 0 (by simp) U x) +
        (2 : ℤ).negOnePow • ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • ev α 0 1 (by simp) U (x.face i) :=
      hDeltaSucc 0 0 1 (by simp) ht x
    rw [key]
    simp only [hα, fam_zero, fam_one, smul_zero, Finset.sum_const_zero, add_zero, sec_map_comp, resι_d]
    rfl
  | 2 =>
    obtain rfl : t = 0 := by omega
    have key : ev (δ 1 2 α) 2 0 ht U x = Sec.map ((res ℤ Gm).d (-1) 0) (ev α 2 (-1) (by simp) U x) +
        (2 : ℤ).negOnePow • ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • ev α 1 0 (by simp) U (x.face i) :=
      hDeltaSucc 1 (-1) 0 (by simp) ht x
    rw [key]
    simp only [hα, fam_one]
    rw [show fam L 2 (-1) (by simp) U x = 0 from rfl, sec_map_zero, zero_add, Fin.sum_univ_three, lineUnit_face,
      unitSec_mul, sec_map_add]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    simp
  | p + 3 =>
    have key := hDeltaSucc (p + 2) (t - 1) t (by omega) ht x
    rw [key]
    simp only [hα, fam_add_two, sec_map_zero, zero_add, smul_zero, Finset.sum_const_zero]

theorem exists_cocycle {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
  have hExists := GlobalTheory.EtC.exists_cochain_ev_eq_of_natural ℤ (fam L) (fam_nat L)
  obtain ⟨α, hα⟩ := hExists
  refine ⟨Cocycle.mk α 2 (by norm_num) (fam_cocycle L α hα), fun U x => ?_, fun U x => ?_⟩
  · exact (hα 0 1 _ U x).trans (fam_zero L 1 _ U x)
  · exact (hα 1 0 _ U x).trans (fam_one L _ U x)

theorem spec {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, CohomologyClass.mk γ = picClass L ∧
      (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
  obtain ⟨γ, h0, h1⟩ := exists_cocycle L
  exact pick_spec (P := fun c => ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, CohomologyClass.mk γ = c ∧
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)))
    ⟨_, γ, rfl, h0, h1⟩

theorem cocycle_ext {E : Spc} (γ γ' : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1)
    (h0 : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = ev γ'.1 0 1 (by simp) U x)
    (h1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = ev γ'.1 1 0 (by simp) U x) : γ = γ' := by
  have hExt := CupSpec.ev_ext γ.1 γ'.1
  refine Cocycle.ext (hExt fun p s h U x => ?_)
  match p with
  | 0 =>
    obtain rfl : s = 1 := by omega
    exact h0 U x
  | 1 =>
    obtain rfl : s = 0 := by omega
    exact h1 U x
  | p + 2 =>
    have hZ := res_isZero Gm s (by omega)
    exact (sec_eq_zero hZ _).trans (sec_eq_zero hZ _).symm

end GlobalTheory.EtC.PicSpec
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.PairDich

theorem isUnit_ι_appTop {T : Scheme.{0}} (W : T.Opens) (E : Γ(T, ⊤)) (h : W ≤ T.basicOpen E) :
    IsUnit (W.ι.appTop E) := by
  refine W.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun w _ => ?_
  have hw : w ∈ W.ι ⁻¹ᵁ T.basicOpen E := h w.2
  rw [Scheme.preimage_basicOpen_top] at hw
  exact (Scheme.mem_basicOpen_top _ _ _).1 hw

theorem mem_basicOpen_or {T : Scheme.{0}} (E : Γ(T, ⊤)) (t : T) :
    t ∈ T.basicOpen E ∨ t ∈ T.basicOpen (1 - E) := by
  rw [Scheme.mem_basicOpen_top, Scheme.mem_basicOpen_top, map_sub, map_one]
  exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

theorem comp_rule {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) {T : Scheme.{0}}
    (y : T ⟶ Spec (CommRingCat.of B)) (a : A) :
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (y ≫ Spec.map (CommRingCat.ofHom g)).appTop).hom a =
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ y.appTop).hom (g a) := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end GlobalTheory.EtC.PairDich

namespace GlobalTheory.EtC.PairDich

theorem pair_dich : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) (e u : A' ⊗[A] A'), (∀ a : A', (a ⊗ₜ[A] (1 : A') - (1 : A') ⊗ₜ[A] a) * e = 0) → algebraMap A (A' ⊗[A] A') f * u = 1 - e → ∀ (T : Scheme.{0}) (y y' : T ⟶ Spec (CommRingCat.of A')), y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) = y' ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) → Loc T fun V k => k ≫ y = k ≫ y' ∨ IsUnit (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (k ≫ y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop).hom f) := by
  intro A A' _ _ _ f e u he hu T y y' hyy
  let φ : A' →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of A')).inv ≫ y.appTop).hom
  let φ' : A' →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of A')).inv ≫ y'.appTop).hom
  have hA : ∀ r : A, φ (algebraMap A A' r) = φ' (algebraMap A A' r) := by
    intro r
    have := congrArg (fun m : T ⟶ Spec (CommRingCat.of A) =>
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ m.appTop).hom r) hyy
    simp only at this
    rw [comp_rule, comp_rule] at this
    exact this
  letI : Algebra A Γ(T, ⊤) := (φ.comp (algebraMap A A')).toAlgebra
  let φa : A' →ₐ[A] Γ(T, ⊤) := ⟨φ, fun _ => rfl⟩
  let φa' : A' →ₐ[A] Γ(T, ⊤) := ⟨φ', fun r => (hA r).symm⟩
  let ψ := Algebra.TensorProduct.productMap φa φa'
  have hE : ∀ a : A', (φ a - φ' a) * ψ e = 0 := by
    intro a
    have := congrArg ψ (he a)
    rw [map_mul, map_sub, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.productMap_apply_tmul, map_one, map_one, mul_one, one_mul, map_zero] at this
    exact this
  have hF : ψ (algebraMap A _ f) * ψ u = 1 - ψ e := by rw [← map_mul, hu, map_sub, map_one]
  have hψf : ψ (algebraMap A _ f) = φ (algebraMap A A' f) := by rw [AlgHom.commutes]; rfl
  rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover]
  · intro t
    have key : ∀ G : Γ(T, ⊤), t ∈ T.basicOpen G → ∃ W : T.Opens, IsAffine W ∧ t ∈ W ∧ IsUnit (W.ι.appTop G) := by
      intro G hG
      obtain ⟨W0, hW, htW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) hG
      exact ⟨W0, hW, htW, isUnit_ι_appTop W0 G hWle⟩
    rcases mem_basicOpen_or (ψ e) t with h1 | h2
    · obtain ⟨W, hW, htW, hunit⟩ := key _ h1
      refine ⟨W, W.ι, hW, inferInstance, by rw [Scheme.Opens.range_ι]; exact htW, Or.inl ?_⟩
      apply ext_to_Spec
      simp only [Scheme.Γ_map_op, Scheme.Hom.comp_appTop]
      ext a
      have h0 := congrArg W.ι.appTop.hom (hE a)
      rw [map_mul, map_sub, map_zero, hunit.mul_left_eq_zero, sub_eq_zero] at h0
      exact h0
    · obtain ⟨W, hW, htW, hunit⟩ := key _ h2
      refine ⟨W, W.ι, hW, inferInstance, by rw [Scheme.Opens.range_ι]; exact htW, Or.inr ?_⟩
      rw [← Category.assoc, comp_rule, Scheme.Hom.comp_appTop]
      have h0 := congrArg W.ι.appTop.hom hF
      rw [map_mul, hψf] at h0
      rw [← h0] at hunit
      exact isUnit_of_mul_isUnit_left hunit
  · rintro V W g k (h | h)
    · exact Or.inl (by rw [Category.assoc, h, Category.assoc])
    · right
      have hc : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ((k ≫ g) ≫ y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop
          = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (g ≫ y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop) ≫ k.appTop := by
        simp only [Scheme.Hom.comp_appTop, Category.assoc]
      rw [hc, CommRingCat.hom_comp, RingHom.comp_apply]
      exact h.map _

end GlobalTheory.EtC.PairDich
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_sheafComplexPairing_tensor_assoc_desc : ∀ (R : Type) [CommRing R] {I J K T T3 : Cx R} (τ : Pair I J T) (τ' : Pair T K T3), τ.IsTensor → τ'.IsTensor → ∀ {M L : Cx R} (μ' : Pair J K M) (ν' : Pair I M L), ∃ ν : Pair T K L, ∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c, ν.mul U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c) := by
  first | exact @GlobalTheory.EtC.tensor_assoc_desc | exact GlobalTheory.EtC.tensor_assoc_desc | (intros; apply GlobalTheory.EtC.tensor_assoc_desc <;> assumption)
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.AWChain

open GlobalTheory.EtC.CupSpec (sub_δ_val δ_sub_val sub_val hom_ext_val)

def cm (N j l : ℕ) : SimplexCategory.mk l ⟶ SimplexCategory.mk N :=
  if h : j + l ≤ N then SimplexCategory.subinterval j l h else SimplexCategory.const _ _ 0

theorem cm_eq (N j l : ℕ) (h : j + l ≤ N) : cm N j l = SimplexCategory.subinterval j l h := dif_pos h

section
variable {N : ℕ}

theorem cm_δ_le (j l : ℕ) (h : j + l ≤ N) (i : Fin (N + 2)) (hi : (i : ℕ) ≤ j) : cm N j l ≫ SimplexCategory.δ i = cm (N + 1) (j + 1) l := by
  rw [cm_eq N j l h, cm_eq (N + 1) (j + 1) l (by omega)]
  refine hom_ext_val _ _ fun v => ?_
  rw [sub_δ_val, sub_val]
  split_ifs <;> omega

theorem cm_δ_gt (j l : ℕ) (h : j + l ≤ N) (i : Fin (N + 2)) (hi : j + l < (i : ℕ)) : cm N j l ≫ SimplexCategory.δ i = cm (N + 1) j l := by
  rw [cm_eq N j l h, cm_eq (N + 1) j l (by omega)]
  refine hom_ext_val _ _ fun v => ?_
  rw [sub_δ_val, sub_val]
  split_ifs <;> omega

theorem cm_δ_mid (j l : ℕ) (h : j + l ≤ N) (i : Fin (N + 2)) (i' : Fin (l + 2)) (hi : (i : ℕ) = j + i') :
    cm N j l ≫ SimplexCategory.δ i = SimplexCategory.δ i' ≫ cm (N + 1) j (l + 1) := by
  rw [cm_eq N j l h, cm_eq (N + 1) j (l + 1) (by omega)]
  refine hom_ext_val _ _ fun v => ?_
  rw [sub_δ_val, δ_sub_val]
  split_ifs <;> omega

end

theorem telescope {N : ℕ} {A : Type*} [AddCommGroup A] {p r : ℕ} (hN : p + r = N)
    (φ : (SimplexCategory.mk p ⟶ SimplexCategory.mk (N + 1)) → (SimplexCategory.mk r ⟶ SimplexCategory.mk (N + 1)) → A) :
    ∑ i : Fin (N + 2), (-1 : ℤ) ^ (i : ℕ) • φ (cm N 0 p ≫ SimplexCategory.δ i) (cm N p r ≫ SimplexCategory.δ i) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • φ (SimplexCategory.δ i ≫ cm (N + 1) 0 (p + 1)) (cm (N + 1) (p + 1) r) +
      (-1 : ℤ) ^ p • ∑ j : Fin (r + 2), (-1 : ℤ) ^ (j : ℕ) •
        φ (cm (N + 1) 0 p) (SimplexCategory.δ j ≫ cm (N + 1) p (r + 1)) := by
  have e1 : SimplexCategory.δ (Fin.last (p + 1)) ≫ cm (N + 1) 0 (p + 1) = cm (N + 1) 0 p := by
    rw [cm_eq (N + 1) 0 (p + 1) (by omega), cm_eq (N + 1) 0 p (by omega)]
    refine hom_ext_val _ _ fun v => ?_
    rw [δ_sub_val, sub_val]
    have := v.2
    simp only [Fin.val_last]
    split_ifs <;> omega
  have e2 : SimplexCategory.δ 0 ≫ cm (N + 1) p (r + 1) = cm (N + 1) (p + 1) r := by
    rw [cm_eq (N + 1) p (r + 1) (by omega), cm_eq (N + 1) (p + 1) r (by omega)]
    refine hom_ext_val _ _ fun v => ?_
    rw [δ_sub_val, sub_val]
    simp; omega
  rw [← Fin.sum_congr' _ (show (p + 1) + (r + 1) = N + 2 by omega), Fin.sum_univ_add,
    Fin.sum_univ_castSucc (n := p + 1), Fin.sum_univ_succ (n := r + 1), e1, e2, smul_add, Finset.smul_sum]
  have c : (-1 : ℤ) ^ ((Fin.last (p + 1) : Fin (p + 2)) : ℕ) • φ (cm (N + 1) 0 p) (cm (N + 1) (p + 1) r) +
      (-1 : ℤ) ^ p • (-1 : ℤ) ^ ((0 : Fin (r + 2)) : ℕ) • φ (cm (N + 1) 0 p) (cm (N + 1) (p + 1) r) = 0 := by
    simp [pow_succ]
  have key : ∀ a b c d e f : A, c + d = 0 → a = e → b = f → a + b = e + c + (d + f) := by
    rintro a b c d _ _ h rfl rfl
    rw [add_assoc, ← add_assoc c, h, zero_add]
  refine key _ _ _ _ _ _ c (Finset.sum_congr rfl fun i _ => ?_) (Finset.sum_congr rfl fun j _ => ?_)
  · have := i.2
    rw [cm_δ_mid 0 p (by omega) _ i.castSucc (by simp), cm_δ_le p r (by omega) _ (by simp; omega)]
    rfl
  · have := j.2
    rw [cm_δ_mid p r (by omega) _ j.succ (by simp; omega), cm_δ_gt 0 p (by omega) _ (by simp; omega), smul_smul, ← pow_add]
    congr 2
    simp; omega

theorem aw_eq (N : ℕ) : Pr.aw N = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal N,
    Finsupp.single (⟨q.1, q.2, cm N 0 q.1, cm N q.1 q.2⟩ : Pr N) (1 : ℤ) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range, Pr.aw]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := p.2
  rw [cm_eq N 0 p (by omega), cm_eq N p (N - p) (by omega)]

theorem d₁_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨0, r, a, b⟩ : Pr N) = 0 := rfl

theorem d₂_zero {N p : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, 0, a, b⟩ : Pr N) = 0 := rfl

theorem d₁_succ {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨p + 1, r, a, b⟩ : Pr N) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (⟨p, r, SimplexCategory.δ i ≫ a, b⟩ : Pr N) (1 : ℤ) := by
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

theorem d₂_succ {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (r + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, r + 1, a, b⟩ : Pr N) =
      ∑ j : Fin (r + 2), (-1 : ℤ) ^ (j : ℕ) • Finsupp.single (⟨p, r, a, SimplexCategory.δ j ≫ b⟩ : Pr N) (1 : ℤ) := by
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

theorem d_aw (N : ℕ) : Pr.d (N + 1) (Pr.aw (N + 1)) = Pr.bd (Pr.aw N) := by

  rw [aw_eq, aw_eq, map_sum]
  simp only [Pr.d, Finsupp.linearCombination_single, one_smul, Finset.sum_add_distrib]
  rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
  simp only [d₁_zero, d₂_zero, smul_zero, zero_add, d₁_succ, d₂_succ]

  simp only [Pr.bd, map_sum, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finset.smul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hN : q.1 + q.2 = N := by simpa using hq
  symm
  refine (telescope hN (fun a b => Finsupp.single (⟨q.1, q.2, a, b⟩ : Pr (N + 1)) (1 : ℤ))).trans ?_
  rw [Finset.smul_sum]

theorem wa_eq (N : ℕ) : Pr.wa N = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal N,
    (-1 : ℤ) ^ (q.1 * q.2) • Finsupp.single (⟨q.2, q.1, cm N q.1 q.2, cm N 0 q.1⟩ : Pr N) (1 : ℤ) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range, Pr.wa]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := p.2
  rw [cm_eq N 0 p (by omega), cm_eq N p (N - p) (by omega), Finsupp.smul_single, smul_eq_mul, mul_one]

theorem d_wa (N : ℕ) : Pr.d (N + 1) (Pr.wa (N + 1)) = Pr.bd (Pr.wa N) := by

  rw [wa_eq, wa_eq, map_sum]
  simp only [map_zsmul, Pr.d, Finsupp.linearCombination_single, one_smul, smul_add, Finset.sum_add_distrib]
  rw [Finset.Nat.sum_antidiagonal_succ', Finset.Nat.sum_antidiagonal_succ]
  simp only [d₁_zero, d₂_zero, smul_zero, zero_add, d₁_succ, d₂_succ]

  simp only [Pr.bd, map_sum, map_zsmul, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finset.smul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hN : q.1 + q.2 = N := by simpa using hq
  obtain ⟨p, r⟩ := q
  dsimp only at hN ⊢
  have T := telescope hN (fun a b => Finsupp.single (⟨r, p, b, a⟩ : Pr (N + 1)) (1 : ℤ))
  conv_rhs => arg 2; ext x; rw [smul_comm]
  rw [← Finset.smul_sum (r := (-1 : ℤ) ^ (p * r)), T, smul_add, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
  conv_rhs => rw [add_comm]
  have s1 : (-1 : ℤ) ^ (p * (r + 1)) = (-1) ^ (p * r) * (-1) ^ p := by ring
  have s2 : (-1 : ℤ) ^ ((p + 1) * r) * (-1) ^ r = (-1) ^ (p * r) := by
    rw [← pow_add, show (p + 1) * r + r = p * r + 2 * r by ring, pow_add, pow_mul]
    norm_num
  congr 1 <;> refine Finset.sum_congr rfl fun x _ => ?_
  · simp only [smul_smul, s1, mul_assoc]
  · simp only [smul_smul]
    rw [← mul_assoc, s2]

theorem aw_wa_chain : ∀ N, Pr.d (N + 1) (Pr.aw (N + 1)) = Pr.bd (Pr.aw N) ∧
    Pr.d (N + 1) (Pr.wa (N + 1)) = Pr.bd (Pr.wa N) :=
  fun N => ⟨d_aw N, d_wa N⟩

end GlobalTheory.EtC.AWChain

end
end
