module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor CategoryTheory.MonObj GlobalTheory.AbelianLetters

namespace GlobalTheory.AbelianLetters.TorusRatio

theorem valR_of_corr_one {A : Type} [CommRing A] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {ε : K → ℤ}
    {φ : K → (Y ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (h : LB.Gen.Corr L _ _ _ _ t (LB.oneGen L))
    (x : Sp A ⟶ Y) (j : K → L.ι) (hj : LB.Coh L φ j) (hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j) :
    valR x (LB.wchart L φ j) (t.s j).val = 1 := by
  have e := h j PEmpty.elim hj (fun k => k.elim) (fun _ k => k.elim)
  have hx' : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim) :=
    fun y hy => ⟨hx hy, Set.mem_iInter.2 fun k => k.elim⟩
  have e1 : res (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim ≤ _)
      (t.s j) = 1 := e.trans (map_one _)
  refine (HolHom.valR_res x inf_le_left _ hx').symm.trans ?_
  refine (congrArg (fun q => valR x _ q.val) e1).trans ?_
  exact (HolHom.valR_eq x _ hx' _).trans (map_one _)

theorem isZero_of_isAdd {R : Type} [CommRing R] [IsDomain R] {D : Out.DegPre R} {T : Over (Sp R)}
    {g : Out.GtPt D T} (hb : g.b = 1) (h : Out.GtPt.IsAdd g g g) (χ : D.X) :
    LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (LB.oneGen D.P.L) := by
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    ((val_corr hJ (h.2 χ) (𝟙 _)).trans (val_mul hJ _ _ _))
  have c1 : TorusCoord.cubVal (𝟙 _ ≫ (lift (Out.DegPre.cT D T χ) (lift g.b g.b)).left) y J = 1 := by
    rw [Category.id_comp, hb]
    exact (isCub_cubV D.cub hJ).face₂ _ _
  have e2 := (congrArg (val (g.s χ) (𝟙 _) y J * ·) c1).symm.trans e
  rw [_root_.mul_one] at e2
  exact (mul_eq_left.1 e2.symm).trans (val_one _).symm

theorem ratio_eq_torus_coord [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ)
    (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt)
    (hb : ∀ Tt b, (sB Tt b).b = b ^ n)
    (hadd : ∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b')))
    (hpull : ∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b)))
    (hex : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) :
    (∀ p : Out.GtPtF D ℂ, p.IsZero → IsTorusPt p (fun _ => 1)) ∧
      ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u → ∀ (z : Fin g → ℂ) (xv : D.X → ℂ),
        (ex z).b = Out.DegPre.zeroF D ℂ → IsTorusPt (ex ((n : ℂ) • z)) xv → ∀ x, u x z = xv x := by
  refine ⟨fun p hp => ⟨hp.1, fun χ j hj hc => valR_of_corr_one (hp.2 χ) (𝟙 (Sp ℂ)) j hj hc⟩,
    fun u hu z xv hz ht x => ?_⟩
  have hz1 : (ex z).b = 1 := hz
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (Z := Sp ℂ) (IsLocalRing.closedPoint ℂ)
  have hs : (sB (Out.TF (R := ℂ) ℂ) 1).b = (ex ((n : ℂ) • z)).b := by
    rw [hb, b_nsmul hex, hz1]
  let j : Fin 4 → D.P.L.ι := fun k => J (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x k)
  have hj : LB.Coh D.P.L (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x) j := fun _ _ e => congrArg J e
  have hc : ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x) j := fun y _ =>
    Set.mem_iInter.2 fun k => by
      obtain rfl : y = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      exact hJ _
  have h1 := hu x z j hc
  rw [ht.2 x j hj hc] at h1
  have hp := hpull D.P.A (Out.TF (R := ℂ) ℂ) (ex z).b (𝟙 _)
  have ha := hadd (Out.TF (R := ℂ) ℂ) 1 1
  rw [_root_.mul_one] at ha
  have e1 : (ex z).b ≫ 𝟙 D.P.A = 1 := (Category.comp_id _).trans hz1
  rw [e1] at hp
  have h2 := valR_of_isPull (A := ℂ) (p := (Out.TF (R := ℂ) ℂ).hom) hp x j
  have h3 := valR_of_corr_one (isZero_of_isAdd ((hb _ _).trans (one_pow n)) ha x) (𝟙 (Sp ℂ)) j
    (by rw [hs]; exact hj) (by rw [hs]; exact hc)
  have h4 := h2.symm.trans h3
  exact ((congrArg (u x z * ·) h4).trans (_root_.mul_one _)).symm.trans h1.symm

end GlobalTheory.AbelianLetters.TorusRatio
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbelianLetters

theorem exists_ratio_valR {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {ε : K → ℤ} (hL : L.IsLB) {φ φ' : K → (Sp A ⟶ X)} (e : φ = φ') (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε)) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ a : Γ(Sp A, ⊤)ˣ, (∀ z J, Good L z J → val t (𝟙 _) z J = gm (𝟙 _) z ⊤ a * val t' (𝟙 _) z J) ∧
      ∀ j, ⊤ ≤ LB.wchart L φ j → valR (𝟙 (Sp A)) (LB.wchart L φ j) (t.s j).val =
        valR (𝟙 (Sp A)) ⊤ a.val * valR (𝟙 (Sp A)) (LB.wchart L φ' j) (t'.s j).val := by
  subst e
  obtain ⟨a, ha⟩ := TorusCoord.exists_ratio hL (fun _ _ _ => rfl) t ht t' ht'
  refine ⟨a, fun z J hJ => ha _ _ z J hJ, fun j hj => ?_⟩
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hL (cpt A)
  have toStkA_valR {B : Type} [CommRing B] {Y : Scheme.{0}} (x : Sp B ⟶ Y)
      (U : Y.Opens) (z : Sp B) (ht : ⊤ ≤ x ⁻¹ᵁ U) (b : Γ(Y, U)ˣ) :
      toStkA z (valR x U b.val) = (gm x z U b).val := by
    have hz : x z ∈ U := ht (show z ∈ (⊤ : (Sp B).Opens) from trivial)
    have e1 : ∀ c, (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom c) = c :=
      fun c => congrArg (fun f => CommRingCat.Hom.hom f c)
        (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of B)))
    rw [valR, dite_eq_left ht, gm, dite_eq_left hz]
    show ((Sp B).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((x.appLE U ⊤ ht).hom b.val))) =
      ((Sp B).presheaf.germ (x ⁻¹ᵁ U) z hz).hom ((x.app U).hom b.val)
    rw [e1]
    exact TopCat.Presheaf.germ_res_apply (Sp B).presheaf (homOfLE ht) z trivial ((x.app U).hom b.val)
  apply toStkA_injective
  have hm : (𝟙 (Sp A) : Sp A ⟶ Sp A) (cpt A) ∈ LB.wchart L φ j := hj (x := cpt A) trivial
  rw [map_mul, toStkA_valR _ ⊤ _ le_rfl, toStkA_valR _ (LB.wchart L φ j) _ hj (t.s j),
    toStkA_valR _ (LB.wchart L φ j) _ hj (t'.s j), ← Units.val_mul,
    gen_trans ht _ _ hm (hJ.mem φ _), gen_trans ht' _ _ hm (hJ.mem φ _), mul_left_comm]
  exact congrArg (fun q => Units.val (_ * q)) (ha _ _ _ J hJ)

theorem exists_isRatio_mul [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ)
    (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt)
    (hb : ∀ Tt b, (sB Tt b).b = b ^ n)
    (hadd : ∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b')))
    (hpull : ∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b)))
    (hex : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) :
    ∃ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u ∧ (∀ x z, u x z ≠ 0) ∧
      ∀ x z z', u x (z + z') = u x z * u x z' := by
  have eb : ∀ z, (ex ((n : ℂ) • z)).b = (sB (Out.TF (R := ℂ) ℂ) (ex z).b).b := fun z => by
    rw [b_nsmul hex, hb]
  choose a ha hv using fun x z => exists_ratio_valR (A := ℂ) D.P.isLB
    (φ := Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x)
    (φ' := Out.DegPre.gtφT D (Out.TF (R := ℂ) ℂ) (sB (Out.TF (R := ℂ) ℂ) (ex z).b).b x)
    (by rw [eb]; rfl) ((ex ((n : ℂ) • z)).s x) ((sB (Out.TF (R := ℂ) ℂ) (ex z).b).s x)
    ((ex _).isGen x) ((sB _ _).isGen x)
  have hev : ∀ c : Γ(Sp ℂ, ⊤), valR (𝟙 (Sp ℂ)) ⊤ c = HolHom.evalHom (𝟙 (Sp ℂ)) ⊤ le_rfl c := fun c =>
    HolHom.valR_eq _ _ _ c
  refine ⟨fun x z => valR (𝟙 (Sp ℂ)) ⊤ (a x z).val, fun x z j hj => ?_, fun x z => ?_, fun x z z' => ?_⟩
  · refine (hv x z j hj).trans (congrArg (_ * ·) ?_)
    have H := hpull D.P.A _ (ex z).b (𝟙 _)
    rw [Category.comp_id] at H
    exact valR_of_isPull H x j
  · exact (hev _).trans_ne ((a x z).isUnit.map _).ne_zero
  · have : a x (z + z') = a x z * a x z' := unit_ext fun w _ => by
      obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB w
      have e1 := (val_mul hJ _ _ _).symm.trans
        ((val_corr hJ ((hex ((n : ℂ) • z) ((n : ℂ) • z')).2 x) (𝟙 _)).trans (val_mul hJ _ _ _))
      have e2 := (val_mul hJ _ _ _).symm.trans
        ((val_corr hJ ((hadd _ (ex z).b (ex z').b).2 x) (𝟙 _)).trans (val_mul hJ _ _ _))
      have e3 : val (Out.DegPre.cubAt D ℂ (Out.DegPre.cF D ℂ x) (ex ((n : ℂ) • z)).b (ex ((n : ℂ) • z')).b) (𝟙 _) w J =
          val (Out.DegPre.cubAtT D _ (Out.DegPre.cT D _ x) (sB (Out.TF (R := ℂ) ℂ) (ex z).b).b
            (sB (Out.TF (R := ℂ) ℂ) (ex z').b).b) (𝟙 _) w J := by
        rw [eb, eb]; rfl
      rw [← smul_add] at e1
      rw [← b_add hex] at e2
      have key : ∀ {U : Type} [CommGroup U] {p q r c c' p' q' r' k₁ k₂ k₃ : U}, r * c = p * q → r' * c' = p' * q' →
          c = c' → p = k₁ * p' → q = k₂ * q' → r = k₃ * r' → k₃ = k₁ * k₂ := by
        intro U _ p q r c c' p' q' r' k₁ k₂ k₃ h₁ h₂ h₃ h₄ h₅ h₆
        rw [h₃, h₄, h₅, h₆, _root_.mul_assoc, h₂, _root_.mul_mul_mul_comm] at h₁
        exact mul_right_cancel h₁
      rw [map_mul]
      exact key e1 e2 e3 (ha x z w J hJ) (ha x z' w J hJ) (ha x (z + z') w J hJ)
    simp only [this, hev, Units.val_mul, map_mul]

end GlobalTheory.AbelianLetters
end
end

section

noncomputable section

namespace GlobalTheory.TorusExt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

attribute [local instance] gtGroup

theorem qk_ext {k : ℕ} {p p' : QkPt D F k} (hy : p.y = p'.y) (hg : p.g = p'.g) : p = p' := by
  obtain ⟨y, g, e⟩ := p
  obtain ⟨y', g', e'⟩ := p'
  obtain rfl : y = y' := hy
  obtain rfl : g = g' := hg
  rfl

variable (hB : D.TauBimult) {k : ℕ}

theorem qk_nsmul (p : QkPt D F k) : k • p.g = iota hB F p.y := by
  obtain ⟨h, h₁, h₂⟩ := p.eq
  exact ((isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((isIota_iff_eq hB _ _).1 h₂)

def qkMk (y : D.X) (g : GtPtF D F) (h : k • g = iota hB F y) : QkPt D F k :=
  ⟨y, g, k • g, (isNsmul_iff_eq _ _ _).2 rfl, (isIota_iff_eq hB _ _).2 h⟩

@[simp] theorem qkMk_y (y : D.X) (g : GtPtF D F) (h : k • g = iota hB F y) : (qkMk hB y g h).y = y := rfl

@[simp] theorem qkMk_g (y : D.X) (g : GtPtF D F) (h : k • g = iota hB F y) : (qkMk hB y g h).g = g := rfl

theorem equiv_iff (p p' : QkPt D F k) :
    QkPt.Equiv D F p p' ↔ ∃ z : D.X, p'.y = p.y + k • z ∧ p'.g = p.g + iota hB F z :=
  exists_congr fun z => and_congr Iff.rfl
    ⟨fun ⟨_, h₁, h₂⟩ => ((isAdd_iff_eq _ _ _).1 h₂).trans (congrArg (p.g + ·) ((isIota_iff_eq hB _ _).1 h₁)),
      fun h => ⟨_, isIota_iota hB z, (isAdd_iff_eq _ _ _).2 h⟩⟩

include hB in
theorem equiv_symm {p p' : QkPt D F k} (h : QkPt.Equiv D F p p') : QkPt.Equiv D F p' p := by
  obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 h
  exact (equiv_iff hB _ _).2 ⟨-z, by rw [hy, smul_neg, add_neg_cancel_right], by rw [hg, map_neg, add_neg_cancel_right]⟩

include hB in
theorem equiv_trans {p p' p'' : QkPt D F k} (h : QkPt.Equiv D F p p') (h' : QkPt.Equiv D F p' p'') :
    QkPt.Equiv D F p p'' := by
  obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 h
  obtain ⟨z', hy', hg'⟩ := (equiv_iff hB _ _).1 h'
  exact (equiv_iff hB _ _).2 ⟨z + z', by rw [hy', hy, smul_add, add_assoc], by rw [hg', hg, map_add (f := _), add_assoc]⟩

include hB in
theorem equiv_equivalence : Equivalence (QkPt.Equiv D F (k := k)) :=
  ⟨qk_equiv_refl hB, equiv_symm hB, equiv_trans hB⟩

def qkZero (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) : QkPt D F k :=
  qkMk hB 0 0 (by rw [nsmul_zero, map_zero])

def qkAdd (p p' : QkPt D F k) : QkPt D F k :=
  qkMk hB (p.y + p'.y) (p.g + p'.g) (by rw [nsmul_add, qk_nsmul hB, qk_nsmul hB, map_add (f := _)])

def qkNeg (p : QkPt D F k) : QkPt D F k :=
  qkMk hB (-p.y) (-p.g) (by rw [smul_neg, qk_nsmul hB, map_neg])

def qkShift (p : QkPt D F k) (z : D.X) : QkPt D F k :=
  qkMk hB (p.y + k • z) (p.g + iota hB F z) (by rw [nsmul_add, qk_nsmul hB, map_add (f := _), map_nsmul])

theorem equiv_qkShift (p : QkPt D F k) (z : D.X) : QkPt.Equiv D F p (qkShift hB p z) :=
  (equiv_iff hB _ _).2 ⟨z, rfl, rfl⟩

theorem qkAdd_iff (p p' p'' : QkPt D F k) : QkAdd p p' p'' ↔ QkPt.Equiv D F (qkAdd hB p p') p'' :=
  ⟨fun ⟨q, hy, hg, he⟩ => (qk_ext hy ((isAdd_iff_eq _ _ _).1 hg) : q = qkAdd hB p p') ▸ he,
    fun h => ⟨_, rfl, (isAdd_iff_eq _ _ _).2 rfl, h⟩⟩

theorem qkAdd_qkAdd (p p' : QkPt D F k) : QkAdd p p' (qkAdd hB p p') := (qkAdd_iff hB _ _ _).2 (qk_equiv_refl hB _)

theorem qkAdd_congr {p p' q q' : QkPt D F k} (h : QkPt.Equiv D F p q) (h' : QkPt.Equiv D F p' q') :
    QkPt.Equiv D F (qkAdd hB p p') (qkAdd hB q q') := by
  obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 h
  obtain ⟨z', hy', hg'⟩ := (equiv_iff hB _ _).1 h'
  refine (equiv_iff hB _ _).2 ⟨z + z', ?_, ?_⟩
  · show q.y + q'.y = p.y + p'.y + k • (z + z')
    rw [hy, hy', smul_add, add_add_add_comm]
  · show q.g + q'.g = p.g + p'.g + iota hB F (z + z')
    rw [hg, hg', map_add (f := _), add_add_add_comm]


include hB in
theorem qkAdd_iff_of_equiv {p p' q q' r r' : QkPt D F k} (h : QkPt.Equiv D F p q) (h' : QkPt.Equiv D F p' q')
    (e : QkAdd p p' r) : QkAdd q q' r' ↔ QkPt.Equiv D F r r' := by
  have a := (qkAdd_iff hB _ _ _).1 e
  have c := qkAdd_congr hB h h'
  rw [qkAdd_iff hB]
  exact ⟨fun b => equiv_trans hB (equiv_symm hB a) (equiv_trans hB c b),
    fun b => equiv_trans hB (equiv_symm hB c) (equiv_trans hB a b)⟩

section Action

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X] (hG : GlobalFnsSt) (oa : D.OAct O)

def qkSmul (a : O) (p : QkPt D F k) : QkPt D F k :=
  qkMk hB (a • p.y) (gtSmul hG oa a p.g) (by
    rw [iota_smul hG oa, ← qk_nsmul hB]; exact (map_nsmul (gtSmulHom hG oa F a) k p.g).symm)

theorem qkAct_iff (a : O) (p p' : QkPt D F k) : QkAct oa a p p' ↔ QkPt.Equiv D F (qkSmul hB hG oa a p) p' :=
  ⟨fun ⟨q, hy, hg, he⟩ => (qk_ext hy ((gtAct_iff_eq_gtSmul hG oa _ _ _).1 hg) : q = qkSmul hB hG oa a p) ▸ he,
    fun h => ⟨_, rfl, gtAct_gtSmul hG oa _ _, h⟩⟩

theorem qkAct_qkSmul (a : O) (p : QkPt D F k) : QkAct oa a p (qkSmul hB hG oa a p) :=
  (qkAct_iff hB hG oa _ _ _).2 (qk_equiv_refl hB _)

theorem qkSmul_congr (a : O) {p q : QkPt D F k} (h : QkPt.Equiv D F p q) :
    QkPt.Equiv D F (qkSmul hB hG oa a p) (qkSmul hB hG oa a q) := by
  obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 h
  refine (equiv_iff hB _ _).2 ⟨a • z, ?_, ?_⟩
  · show a • q.y = a • p.y + k • a • z
    rw [hy, smul_add, smul_comm a k z]
  · show gtSmul hG oa a q.g = gtSmul hG oa a p.g + iota hB F (a • z)
    rw [hg, gtSmul_add, iota_smul hG oa]


include hB hG in
theorem qkAct_iff_of_equiv {a : O} {p q r r' : QkPt D F k} (h : QkPt.Equiv D F p q) (e : QkAct oa a p r) :
    QkAct oa a q r' ↔ QkPt.Equiv D F r r' := by
  have a₁ := (qkAct_iff hB hG oa _ _ _).1 e
  have c := qkSmul_congr hB hG oa a h
  rw [qkAct_iff hB hG]
  exact ⟨fun b => equiv_trans hB (equiv_symm hB a₁) (equiv_trans hB c b),
    fun b => equiv_trans hB (equiv_symm hB c) (equiv_trans hB a₁ b)⟩

end Action

section Extension

variable {F' : Type} [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
  (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

def qkExt (p : QkPt D F k) : QkPt D F' k :=
  qkMk hB p.y (gtExt D f hf p.g) (by rw [← map_nsmul, qk_nsmul hB, gtExt_iota])

theorem qkExt_iff (p : QkPt D F k) (p' : QkPt D F' k) : QkExt f p p' ↔ p' = qkExt hB f hf p :=
  ⟨fun h => qk_ext h.1 ((eq_gtExt_iff f hf _ _).2 h.2), fun h => h ▸ ⟨rfl, (eq_gtExt_iff f hf _ _).1 rfl⟩⟩

include hB hf in
theorem existsUnique_qkExt (p : QkPt D F k) : ∃! p' : QkPt D F' k, QkExt f p p' :=
  ⟨_, (qkExt_iff hB f hf _ _).2 rfl, fun _ h => (qkExt_iff hB f hf _ _).1 h⟩

theorem qkExt_congr {p q : QkPt D F k} (h : QkPt.Equiv D F p q) :
    QkPt.Equiv D F' (qkExt hB f hf p) (qkExt hB f hf q) := by
  obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 h
  refine (equiv_iff hB _ _).2 ⟨z, hy, ?_⟩
  show gtExt D f hf q.g = gtExt D f hf p.g + iota hB F' z
  rw [hg, map_add (f := _), gtExt_iota]

theorem qkExt_qkAdd (p q : QkPt D F k) :
    qkExt hB f hf (qkAdd hB p q) = qkAdd hB (qkExt hB f hf p) (qkExt hB f hf q) :=
  qk_ext rfl (map_add (gtExt D f hf) p.g q.g)

include hB hf in
theorem equiv_of_qkExt {p q : QkPt D F k} {p' q' : QkPt D F' k} (hp : QkExt f p p') (hq : QkExt f q q')
    (h : QkPt.Equiv D F p q) : QkPt.Equiv D F' p' q' := by
  rw [(qkExt_iff hB f hf _ _).1 hp, (qkExt_iff hB f hf _ _).1 hq]
  exact qkExt_congr hB f hf h

include hB hf in
theorem qkAdd_of_qkExt {p q r : QkPt D F k} {p' q' r' : QkPt D F' k} (hp : QkExt f p p') (hq : QkExt f q q')
    (hr : QkExt f r r') (h : QkAdd p q r) : QkAdd p' q' r' := by
  rw [(qkExt_iff hB f hf _ _).1 hp, (qkExt_iff hB f hf _ _).1 hq, (qkExt_iff hB f hf _ _).1 hr, qkAdd_iff hB,
    ← qkExt_qkAdd]
  exact qkExt_congr hB f hf ((qkAdd_iff hB _ _ _).1 h)

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X] (hG : GlobalFnsSt) (oa : D.OAct O)

theorem qkExt_qkSmul (a : O) (p : QkPt D F k) :
    qkExt hB f hf (qkSmul hB hG oa a p) = qkSmul hB hG oa a (qkExt hB f hf p) :=
  qk_ext rfl (gtExt_gtSmul f hf hG oa a p.g)

include hB hf hG in
theorem qkAct_of_qkExt {a : O} {p r : QkPt D F k} {p' r' : QkPt D F' k} (hp : QkExt f p p') (hr : QkExt f r r')
    (h : QkAct oa a p r) : QkAct oa a p' r' := by
  rw [(qkExt_iff hB f hf _ _).1 hp, (qkExt_iff hB f hf _ _).1 hr, qkAct_iff hB hG, ← qkExt_qkSmul]
  exact qkExt_congr hB f hf ((qkAct_iff hB hG oa _ _ _).1 h)

end Extension

end GlobalTheory.TorusExt
end
end
