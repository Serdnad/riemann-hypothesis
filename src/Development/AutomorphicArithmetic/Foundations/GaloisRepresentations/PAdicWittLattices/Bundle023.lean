module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLevelObjPullbackOfCharZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem pol_step {S : Scheme.{0}} {A₁ A₂ A : Over S} [GrpObj A₁] [IsCommMonObj A₁] [GrpObj A₂] [IsCommMonObj A₂]
    [GrpObj A] [IsCommMonObj A] {P₁ : LB (G2 A₁).left} {P₂ : LB (G2 A₂).left} {P : LB (G2 A).left}
    (h₁ : P₁.IsLB) (h₂ : P₂.IsLB) (h : P.IsLB) (θ : A₁ ⟶ A₂) (ψ₁ : A₁ ⟶ A) (ψ₂ : A₂ ⟶ A) (e : θ ≫ ψ₂ = ψ₁)
    (i₁ : LBIso (Hecke.lbPow P₁ 1) (P.pull (Hecke.sq2 ψ₁))) (i₂ : LBIso (Hecke.lbPow P₂ 1) (P.pull (Hecke.sq2 ψ₂))) :
    LBIso (Hecke.lbPow P₁ 1) (P₂.pull (Hecke.sq2 θ)) := by
  have pw : ∀ {X : Scheme} (L : LB X), L.IsLB → (Hecke.lbPow L 1).IsLB := by
    intro X L hL
    unfold Hecke.lbPow
    exact LB.isLB_linComb hL _ _
  have c₁ := (GlobalTheory.CechPic.cls_eq_iff (pw P₁ h₁) (pull_isLB h (Hecke.sq2 ψ₁))).mpr i₁
  have c₂ := (GlobalTheory.CechPic.cls_eq_iff (pw P₂ h₂) (pull_isLB h (Hecke.sq2 ψ₂))).mpr i₂
  rw [Hecke.Comp.cls_lbPow' h₁ 1 (pw P₁ h₁), one_smul] at c₁
  rw [Hecke.Comp.cls_lbPow' h₂ 1 (pw P₂ h₂), one_smul] at c₂
  rw [GlobalTheory.CechPic.cls_pull h] at c₁ c₂
  apply (GlobalTheory.CechPic.cls_eq_iff (pw P₁ h₁) (pull_isLB h₂ (Hecke.sq2 θ))).mp
  rw [Hecke.Comp.cls_lbPow' h₁ 1 (pw P₁ h₁), one_smul, GlobalTheory.CechPic.cls_pull h₂, c₁, c₂, ← e,
    Hecke.Comp.grpSchemeSquareProductMap_comp, GlobalTheory.CechPic.pull_comp]

private theorem isMonHom_inv' {C : Type*} [Category C] [MonoidalCategory C] {A B : C} [MonObj A] [MonObj B]
    (f : A ⟶ B) [IsIso f] [IsMonHom f] : IsMonHom (inv f) := by
  have : IsMonHom (asIso f).inv := inferInstance
  simpa using this

theorem UpperTheory.Gal.G3.pTransOrbit :
    MultBasic → RelComp → TateDiff → TateTwist → KNCong → TransIso → TransOrbit := by
  intro hMB hRC hTD hTT hKN hTI p _ D G L R _ _ gb k _ _ s N' N o₁ o₂ o ψ₁ ψ₂ h₁ h₂
  have one_mem : (1 : G.GAf) ∈ L.KN 1 := (L.KN 1).one_mem
  have kn1 : ∀ {M : ℕ} {g : G.GAf}, g ∈ L.KN M → g ∈ L.KN 1 :=
    fun hg => UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hg
  haveI : IsIso ψ₁ := hTI p D G L R gb _ s _ _ o₁ o ψ₁ 1 one_mem h₁
  haveI : IsIso ψ₂ := hTI p D G L R gb _ s _ _ o₂ o ψ₂ 1 one_mem h₂
  unfold UpperTheory.Gal.Int.Geo.IsTrans at h₁ h₂
  haveI hm₁ : IsMonHom ψ₁ := h₁.1
  haveI hm₂ : IsMonHom ψ₂ := h₂.1
  haveI hmi₁ : IsMonHom (inv ψ₁) := isMonHom_inv' ψ₁
  haveI hmi₂ : IsMonHom (inv ψ₂) := isMonHom_inv' ψ₂
  have hNpos : 0 < (N' : ℕ) := by
    have := N'.2.1
    omega
  have hNcop : (N' : ℕ).Coprime p := N'.2.2
  have flip : ∀ {X Y : Over (Sp k)} (a : X ⟶ X) (b : Y ⟶ Y) (ψ : X ⟶ Y) [IsIso ψ],
      a ≫ ψ = ψ ≫ b → b ≫ inv ψ = inv ψ ≫ a := by
    intro X Y a b ψ _ h
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have rev : ∀ {k' : Type} [Field k'] {t : Sp k' ⟶ Sp k} (I : UpperTheory.Gal.Int.Geo.TIso o₂ t)
      (J : UpperTheory.Gal.Int.Geo.TIso o t),
      UpperTheory.Gal.G3.Rel L I J ψ₂ 1 → UpperTheory.Gal.G3.Rel L J I (inv ψ₂) 1 := by
    intro k' _ t I J hIJ n hn hc x y
    rw [IsIso.comp_inv_eq]
    refine (eq_comm.trans (hIJ n hn hc y x)).trans ?_
    simp only [map_one, Module.End.one_apply]
    constructor
    · rintro ⟨v, hv, e⟩
      exact ⟨-v, neg_mem hv, by rw [e, smul_neg, add_neg_cancel_right]⟩
    · rintro ⟨v, hv, e⟩
      exact ⟨-v, neg_mem hv, by rw [e, smul_neg, add_neg_cancel_right]⟩
  have key : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (t : Sp k' ⟶ Sp k) (β' : R →+* k'),
      t ≫ s = spMap β' →
      ∃ (I' : UpperTheory.Gal.Int.Geo.TIso o₁ t) (I'' : UpperTheory.Gal.Int.Geo.TIso o₂ t),
        UpperTheory.Gal.G3.Ind o₁ I' ∧ UpperTheory.Gal.G3.Ind o₂ I'' ∧
          ∃ w ∈ L.KN N, UpperTheory.Gal.G3.Rel L I' I'' (ψ₁ ≫ inv ψ₂) w := by
    intro k' _ _ t β' ht
    obtain ⟨I₁', I₁'', a₁, b₁, r₁⟩ := h₁.2.2.2.2 k' t β' ht
    obtain ⟨I₂', I₂'', a₂, b₂, r₂⟩ := h₂.2.2.2.2 k' t β' ht
    obtain ⟨w, hw, rr⟩ := hTD p D G L R gb _ s N o k' t I₁'' I₂'' b₁ b₂
    have s1 := (hRC p D G L R gb _ s _ _ _ o₁ o o k' t I₁' I₁'' I₂'' ψ₁ (𝟙 _) 1 w hm₁ inferInstance
      (UpperTheory.Gal.Int.Geo.integ_of_mem (kn1 hw))).2 r₁ rr
    have s2 := (hRC p D G L R gb _ s _ _ _ o₁ o o₂ k' t I₁' I₂'' I₂' (ψ₁ ≫ 𝟙 _) (inv ψ₂) (w * 1) 1
      inferInstance hmi₂ (UpperTheory.Gal.Int.Geo.integ_of_mem one_mem)).2 s1 (rev I₂' I₂'' r₂)
    refine ⟨I₁', I₂', a₁, a₂, w, hw, ?_⟩
    rw [Category.comp_id, _root_.mul_one, _root_.one_mul] at s2
    exact s2
  obtain ⟨I₀', I₀'', hI₀', hI₀'', w₀, hw₀, r₀⟩ :=
    key k (𝟙 (Sp k)) (Spec.preimage s).hom (by simp [spMap])
  obtain ⟨c₁, hc₁, ⟨i₁⟩, t₁, t₁', x1, x2, x3, x4⟩ := h₁.2.2.2.1
  have e₁ : c₁ = 1 := (hMB p).1 _ c₁ 1 hc₁ (Nat.coprime_one_left p) ⟨t₁, t₁', x1, x2, x3, x4⟩
    ((hMB p).2.2 D G L 1 one_mem)
  subst e₁
  obtain ⟨c₂, hc₂, ⟨i₂⟩, t₂, t₂', y1, y2, y3, y4⟩ := h₂.2.2.2.1
  have e₂ : c₂ = 1 := (hMB p).1 _ c₂ 1 hc₂ (Nat.coprime_one_left p) ⟨t₂, t₂', y1, y2, y3, y4⟩
    ((hMB p).2.2 D G L 1 one_mem)
  subst e₂
  refine ⟨w₀, hw₀, ψ₁ ≫ inv ψ₂, ?_, by simp⟩
  unfold UpperTheory.Gal.Int.Geo.IsTrans
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · intro c
    rw [← Category.assoc, h₁.2.1 c, Category.assoc, flip _ _ ψ₂ (h₂.2.1 c)]
    simp only [Category.assoc]
  · refine ⟨ψ₂ ≫ inv ψ₁, 1, inferInstance, ?_, by simp, by simp, Nat.coprime_one_left p⟩
    intro c
    rw [← Category.assoc, h₂.2.1 c, Category.assoc, flip _ _ ψ₁ (h₁.2.1 c)]
    simp only [Category.assoc]
  · exact ⟨1, Nat.coprime_one_left p,
      ⟨pol_step o₁.isLB o₂.isLB o.isLB (ψ₁ ≫ inv ψ₂) ψ₁ ψ₂ (by simp) i₁ i₂⟩,
      (hMB p).2.2 D G L w₀ (kn1 hw₀)⟩
  · intro k' _ _ t β' ht
    obtain ⟨I', I'', hI', hI'', w, hw, r⟩ := key k' t β' ht
    have A : ∀ x y : D.La, (∃ v ∈ LaHat D, (L.actG w₀) (inAf D x) = inAf D y + (N' : ℕ) • v) →
        ∃ v ∈ LaHat D, (L.actG w) (inAf D x) = inAf D y + (N' : ℕ) • v := by
      intro x y hxy
      have e0 := (r₀ N' hNpos hNcop x y).mpr hxy
      apply (r N' hNpos hNcop x y).mp
      rw [← hI₀' x, ← hI₀'' y] at e0
      rw [← hI' x, ← hI'' y]
      have hu : toUnit (Over.mk t) =
          Over.homMk (U := Over.mk t) (V := Over.mk (𝟙 (Sp k))) t (by simp) ≫ toUnit (Over.mk (𝟙 (Sp k))) :=
        toUnit_unique _ _
      rw [hu]
      simp only [Category.assoc] at e0 ⊢
      rw [e0]
    have cong : ∀ x : D.La, ∃ m ∈ LaHat D,
        (L.actG (w₀ * w⁻¹)) (inAf D x) = inAf D x + (N' : ℕ) • m := by
      intro x
      have hwi : w⁻¹ ∈ L.KN 1 := (L.KN 1).inv_mem (kn1 hw)
      obtain ⟨x', m, hm, hz⟩ := exists_inAf_add_nsmul_of_mem_laHat p D N' hNpos hNcop _
        (UpperTheory.Gal.Int.Geo.integ_of_mem hwi _ (GlobalTheory.HeckeApprox.inAf_mem D x))
      obtain ⟨y', m₁, hm₁, e₁⟩ := exists_inAf_add_nsmul_of_mem_laHat p D N' hNpos hNcop _
        (UpperTheory.Gal.Int.Geo.integ_of_mem (kn1 hw₀) _ (GlobalTheory.HeckeApprox.inAf_mem D x'))
      obtain ⟨m₂, hm₂, e₂⟩ := A x' y' ⟨m₁, hm₁, e₁⟩
      have hback : (L.actG w) ((L.actG w⁻¹) (inAf D x)) = inAf D x := by
        rw [← Module.End.mul_apply, ← map_mul, _root_.mul_inv_cancel, map_one, Module.End.one_apply]
      refine ⟨m₁ - m₂ + ((L.actG w₀) m - (L.actG w) m), ?_, ?_⟩
      · exact add_mem (sub_mem hm₁ hm₂) (sub_mem (UpperTheory.Gal.Int.Geo.integ_of_mem (kn1 hw₀) _ hm)
          (UpperTheory.Gal.Int.Geo.integ_of_mem (kn1 hw) _ hm))
      · rw [map_mul, Module.End.mul_apply, hz, map_add (f := _), map_nsmul, e₁]
        rw [hz, map_add (f := _), map_nsmul, e₂] at hback
        rw [← hback]
        simp only [smul_add, smul_sub]
        abel
    have hv : w₀ * w⁻¹ ∈ L.KN (N' : ℕ) :=
      hKN p D G L N' hNpos hNcop _ (mul_mem (kn1 hw₀) (inv_mem (kn1 hw))) cong
    obtain ⟨J, hJ, rJ⟩ := hTT p D G L R gb _ s N' o₂ k' t I'' hI'' _ hv
    refine ⟨I', J, hI', hJ, ?_⟩
    have := (hRC p D G L R gb _ s _ _ _ o₁ o₂ o₂ k' t I' I'' J (ψ₁ ≫ inv ψ₂) (𝟙 _) w (w₀ * w⁻¹)
      inferInstance inferInstance (UpperTheory.Gal.Int.Geo.integ_of_mem (kn1 hv))).2 r rJ
    rw [Category.comp_id, _root_.inv_mul_cancel_right] at this
    exact this
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem gObjMap_comp_φ {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G₀ R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁}
    {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : GObjMap o₁ o₂ f)
    (h₂ : GObjMap o₂ o₃ g) : ∃ m : GObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

private theorem gObjMap_cast {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G₀ R} {N : ℕ}
    {S₁ S₂ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂}
    {f f' : S₁ ⟶ S₂} (e : f = f') (m : GObjMap o₁ o₂ f) : ∃ m' : GObjMap o₁ o₂ f', m'.φ = m.φ := by
  subst e
  exact ⟨m, rfl⟩

theorem UpperTheory.Gal.G3.pPtEq :
    TransSelf → TransComp → TransPull → TransUniqPt → Rigid → PtEq := by
  intro hS hC hP hU hRg p _ D G L R _ _ gb N₁ N₂ N X₁ X₂ X h₁ h₂ g u π₁ Φ₁ π₂ Φ₂ w₁ w₂ i₁ i₂ a₁ a₂ hu he
    k _ _ s x y hx hy ox oy mx my θ hθ
  obtain ⟨e₁, o₁, ψ₁, f₁, t₁, rfl⟩ := w₁
  obtain ⟨e₂, o₂, ψ₂, f₂, t₂, rfl⟩ := w₂
  obtain ⟨o₁x, ⟨n₁⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero s x hx o₁
  obtain ⟨o₂y, ⟨n₂⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero s y hy o₂
  obtain ⟨ψ₁', t₁', c₁⟩ := hP p D G L R gb X₁.X (Sp k) X₁.s s x hx _ _ X₁.univ o₁ ox o₁x mx n₁ ψ₁ h₁ t₁
  obtain ⟨ψ₂', t₂', c₂⟩ := hP p D G L R gb X₂.X (Sp k) X₂.s s y hy _ _ X₂.univ o₂ oy o₂y my n₂ ψ₂ h₂ t₂
  have iu : Integ L u := UpperTheory.Gal.Int.Geo.integ_of_mem (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu)
  have au : AdmK L N N u := fun v hv =>
    (L.KN N).mul_mem ((L.KN N).mul_mem hu hv) ((L.KN N).inv_mem hu)
  have t₃ := hC p D G L R gb (Sp k) s N₁ N₂ N ox oy o₂y θ ψ₂' g h₂ i₂ a₂ hθ t₂'
  have t₄ := hC p D G L R gb (Sp k) s N₁ N N ox o₂y o₂y (θ ≫ ψ₂') (𝟙 _) (h₂ * g) u iu au t₃
    ((hS p D G L R gb (Sp k) s N).1 o₂y u hu)
  rw [← he] at t₄
  obtain ⟨m, hm⟩ := hU p D G L R gb k s N₁ N ox o₁x o₂y ψ₁' _ h₁ i₁ a₁ t₁' t₄
  obtain ⟨A, hA⟩ := gObjMap_comp_φ n₁ f₁
  obtain ⟨B₀, hB₀⟩ := gObjMap_comp_φ n₂ f₂
  obtain ⟨B, hB⟩ := gObjMap_comp_φ m B₀
  have hxs : (x ≫ π₁) ≫ X.s = s := by rw [Category.assoc, e₁, hx]
  have hys : (𝟙 (Sp k) ≫ y ≫ π₂) ≫ X.s = s := by simp [Category.assoc, e₂, hy]
  have hxy : x ≫ π₁ = 𝟙 (Sp k) ≫ y ≫ π₂ :=
    (X.rep (Sp k) s o₁x).unique ⟨hxs, ⟨A⟩⟩ ⟨hys, ⟨B⟩⟩
  obtain ⟨B', hB'⟩ := gObjMap_cast hxy.symm B
  have hAB := hRg p D R gb X.X (Sp k) X.s s (x ≫ π₁) hxs N X.univ o₁x A B'
  refine ⟨by simpa using hxy, ?_⟩
  rw [hB', hB, hB₀, hA] at hAB
  calc mx.φ ≫ Over.Hom.left ψ₁ ≫ f₁.φ = (mx.φ ≫ Over.Hom.left ψ₁) ≫ f₁.φ := by rw [Category.assoc]
    _ = Over.Hom.left ψ₁' ≫ n₁.φ ≫ f₁.φ := by rw [← c₁, Category.assoc]
    _ = Over.Hom.left ψ₁' ≫ m.φ ≫ n₂.φ ≫ f₂.φ := by rw [hAB]
    _ = Over.Hom.left ((θ ≫ ψ₂') ≫ 𝟙 _) ≫ n₂.φ ≫ f₂.φ := by rw [← hm, Category.assoc]
    _ = Over.Hom.left θ ≫ (Over.Hom.left ψ₂' ≫ n₂.φ) ≫ f₂.φ := by simp
    _ = Over.Hom.left θ ≫ my.φ ≫ Over.Hom.left ψ₂ ≫ f₂.φ := by rw [c₂, Category.assoc]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitUniq :
    GenSm → ExtPts → TransSelf → PtEq → WitUniq := by
  intro hG hE hS hP p _ D G L R _ _ gb N' N X' X h ih ah π Φ π' Φ' w w'
  have hsm : Smooth X'.s := (hG p D R gb N' X').1
  haveI : IsSeparated X.s := (hG p D R gb N X).2.1
  haveI : AlgebraicGeometry.IsReduced X'.X := GlobalTheory.isReduced_of_smooth_of_isReduced X'.s
  have pt : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ X'.X),
      ∃ ox : GObj gb N' (x ≫ X'.s), ∃ mx : GObjMap ox X'.univ x,
        x ≫ π = x ≫ π' ∧ mx.φ ≫ Φ = mx.φ ≫ Φ' := by
    intro Ω _ _ x
    obtain ⟨ox, ⟨mx⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) x rfl X'.univ
    have t := (hS p D G L R gb (Sp Ω) (x ≫ X'.s) N').1 ox 1 (L.KN N').one_mem
    have e := hP p D G L R gb N' N' N X' X' X h h 1 1 π Φ π' Φ' w w' ih ih ah ah
      (L.KN N).one_mem (by simp) Ω (x ≫ X'.s) x x rfl rfl ox ox mx mx (𝟙 _) t
    exact ⟨ox, mx, e.1, by simpa using e.2⟩
  have hπ : π = π' := hE X.s π π' (by rw [w.1, w'.1]) fun Ω _ _ x => by
    obtain ⟨_, _, e, _⟩ := pt Ω x
    exact e
  refine ⟨hπ, ?_⟩
  haveI := X'.univ.ab
  haveI := X.univ.ab
  haveI : Smooth X'.univ.A.hom := IsAbelianScheme.smooth
  haveI : AlgebraicGeometry.IsReduced X'.univ.A.left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced X'.univ.A.hom
  haveI : IsProper X.univ.A.hom := IsAbelianScheme.proper
  refine hE X.univ.A.hom Φ Φ' (by rw [w.w, w'.w, hπ]) fun Ω _ _ z => ?_
  obtain ⟨ox, mx, -, e⟩ := pt Ω (z ≫ X'.univ.A.hom)
  obtain ⟨l, hl, -⟩ := mx.cart.1.exists_lift z (𝟙 _) (by simp)
  calc z ≫ Φ = l ≫ mx.φ ≫ Φ := by rw [← Category.assoc, hl]
    _ = l ≫ mx.φ ≫ Φ' := by rw [e]
    _ = z ≫ Φ' := by rw [← Category.assoc, hl]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem card_eq_relIndex {G Γ : Type} [Group G] (H L : Subgroup G) (r : Γ → G) (hr : ∀ x, r x ∈ L)
    (hu : ∀ k ∈ L, ∃! x, k * (r x)⁻¹ ∈ H) : Nat.card Γ = H.relIndex L := by
  unfold Subgroup.relIndex Subgroup.index
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => (QuotientGroup.mk ⟨(r x)⁻¹, L.inv_mem (hr x)⟩ : L ⧸ H.subgroupOf L)) ⟨?_, ?_⟩)
  · intro x y e
    have e' := QuotientGroup.eq.mp e
    have h2 : r x * (r y)⁻¹ ∈ H := by simpa [Subgroup.mem_subgroupOf] using e'
    have h1 : r x * (r x)⁻¹ ∈ H := by simp [H.one_mem]
    exact (hu (r x) (hr x)).unique h1 h2
  · intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨x, hx, -⟩ := hu (g : G)⁻¹ (L.inv_mem g.2)
      refine ⟨x, QuotientGroup.eq.mpr ?_⟩
      rw [Subgroup.mem_subgroupOf]
      have h3 := H.inv_mem hx
      simpa using h3

private theorem fEt_normal (hb : FEtBasic) (hg : TwGal) {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G)
    (m j : X.ι) (b : X.admitted m j 1) (hn : ∀ k ∈ X.K j, ∀ u ∈ X.K m, k * u * k⁻¹ ∈ X.K m) :
    FEt (X.tr m j 1 b.1 b.2) ((X.K m).relIndex (X.K j)) := by
  obtain ⟨Γ, _, _, r, c, hr, hu, hG⟩ := hg X m j b hn
  rw [← card_eq_relIndex _ _ r hr hu]
  exact hb.2.2 _ Γ _ hG

theorem UpperTheory.Gal.G3.pTwFEt :
    FEtBasic → TwGal → TwFEt := by
  intro hb hg
  unfold TwFEt
  intro B G _ X i j a
  obtain ⟨m, hmj, hn, hS⟩ := X.deep j {(i, 1)}
  have hmi : X.K m ≤ X.K i := fun u hu => by simpa using hS (i, 1) (by simp) u hu
  have hij : X.K i ≤ X.K j := fun u hu => by simpa using a.2 u hu
  have b : X.admitted m j 1 := X.isAdmissibleIntegralBasisChange_one hmj
  have b' : X.admitted m i 1 := X.isAdmissibleIntegralBasisChange_one hmi
  have h1 := fEt_normal hb hg X m j b hn
  have h2 := fEt_normal hb hg X m i b' (fun k hk u hu => hn k (hij hk) u hu)
  have hc : X.tr m i 1 b'.1 b'.2 ≫ X.tr i j 1 a.1 a.2 = X.tr m j 1 b.1 b.2 := by
    have e : ∀ (h : G) (_ : h = 1) p q, X.tr m j h p q = X.tr m j 1 b.1 b.2 := by
      rintro _ rfl _ _; rfl
    rw [X.tr_mul m i j 1 1 b'.1 b'.2 a.1 a.2 (by simpa using a.1) (by simpa using b.2)]
    exact e _ (mul_one 1) _ _
  refine ⟨X.fin i j a.1 a.2, X.etale i j a.1 a.2, fun K _ _ x => ?_⟩
  set s := X.tr i j 1 a.1 a.2 with hs
  set r := X.tr m i 1 b'.1 b'.2 with hr
  have fs : Finite {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x} :=
    have := X.fin i j a.1 a.2
    (UpperTheory.Gal.TranscendenceTraces.fibFin_holds s K x).to_subtype
  have fr : ∀ y : {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x},
      Finite {w : Spec (CommRingCat.of K) ⟶ X.Z m // w ≫ r = y.1} := fun y =>
    have := X.fin m i b'.1 b'.2
    (UpperTheory.Gal.TranscendenceTraces.fibFin_holds r K y.1).to_subtype
  have := Fintype.ofFinite {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x}
  have e1 : {w : Spec (CommRingCat.of K) ⟶ X.Z m // w ≫ X.tr m j 1 b.1 b.2 = x} ≃
      Σ y : {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x},
        {w : Spec (CommRingCat.of K) ⟶ X.Z m // w ≫ r = y.1} :=
    { toFun := fun w => ⟨⟨w.1 ≫ r, by rw [Category.assoc, hc, w.2]⟩, ⟨w.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by rw [← hc, ← Category.assoc, p.2.2, p.1.2]⟩
      left_inv := fun w => rfl
      right_inv := by
        rintro ⟨⟨y, hy⟩, ⟨w, hw⟩⟩
        change w ≫ r = y at hw
        subst hw
        rfl }
  have hcount : Nat.card {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x} * (X.K m).relIndex (X.K i) =
      (X.K m).relIndex (X.K j) := by
    rw [← h1.2.2 K x, Nat.card_congr e1, Nat.card_sigma]
    simp only [h2.2.2 K, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Nat.card_eq_fintype_card]
  have hmul := Subgroup.relIndex_mul_relIndex (X.K m) (X.K i) (X.K j) hmi hij
  have hpos : 0 < (X.K m).relIndex (X.K i) := Nat.pos_of_ne_zero (X.idx m i)
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hmul, ← hcount, mul_comm]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem epi_of_isGrpPullback_etale_surjective {S S' : Scheme} (c : S' ⟶ S) [Etale c] [Surjective c] (A : Over S)
    (A' : Over S') [GrpObj A] [GrpObj A'] (a : A'.left ⟶ A.left) (ha : IsGrpPullback A' A c a) : Epi a := by
  haveI : Etale a := MorphismProperty.of_isPullback (P := @Etale) ha.1.flip ‹Etale c›
  haveI : Surjective a := MorphismProperty.of_isPullback (P := @Surjective) ha.1.flip ‹Surjective c›
  exact AlgebraicGeometry.Flat.epi_of_flat_of_surjective a

private theorem comp_eq_comp_of_over_left_comm {S S' : Scheme} {A B : Over S} {A' B' : Over S'}
    (a : A'.left ⟶ A.left) (b : B'.left ⟶ B.left) [Epi a] (u : A ⟶ A) (v : B ⟶ B) (u' : A' ⟶ A')
    (v' : B' ⟶ B') (f : A ⟶ B) (f' : A' ⟶ B')
    (hf : Over.Hom.left f' ≫ b = a ≫ Over.Hom.left f)
    (hu : Over.Hom.left u' ≫ a = a ≫ Over.Hom.left u)
    (hv : Over.Hom.left v' ≫ b = b ≫ Over.Hom.left v) (h' : u' ≫ f' = f' ≫ v') : u ≫ f = f ≫ v := by
  apply Over.OverMorphism.ext
  rw [← cancel_epi a]
  have e3 : Over.Hom.left u' ≫ Over.Hom.left f' = Over.Hom.left f' ≫ Over.Hom.left v' := by
    rw [← Over.comp_left, h', Over.comp_left]
  simp only [Over.comp_left]
  calc a ≫ Over.Hom.left u ≫ Over.Hom.left f
        = Over.Hom.left u' ≫ Over.Hom.left f' ≫ b := by rw [← reassoc_of% hu, ← hf]
    _ = Over.Hom.left f' ≫ Over.Hom.left v' ≫ b := by rw [reassoc_of% e3]
    _ = a ≫ Over.Hom.left f ≫ Over.Hom.left v := by rw [hv, reassoc_of% hf]

theorem UpperTheory.Gal.G3.pTransDesc :
    IsogFEt → TatePull → HomDesc → PolDesc → TransDesc := by
  intro hIsog hTate hHom hPol p _ D G L R _ _ gb S S' _ s s' c _ _ _ hcs N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ ψ' h hsq hT
  obtain ⟨hmon', hact', ⟨χ', d, hχmon', hχact', hd1', hd2', hdp⟩, ⟨e, hep, hpol', hint⟩, hgeo'⟩ := hT
  haveI : Epi m₁.φ := epi_of_isGrpPullback_etale_surjective c o₁.A o₁'.A m₁.φ m₁.cart
  haveI : Epi m₂.φ := epi_of_isGrpPullback_etale_surjective c o₂.A o₂'.A m₂.φ m₂.cart
  have hH := hHom S S' c o₁.A o₂.A o₁'.A o₂'.A o₁.ab o₂.ab o₂'.ab m₁.φ m₂.φ m₁.cart m₂.cart ψ ψ' hsq hmon'
  have hmon : IsMonHom ψ := hH.1
  have hdpos : 0 < d := Nat.pos_of_ne_zero (by
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' ((Nat.coprime_zero_left p).mp hdp))
  obtain ⟨hfin, -, hsurj⟩ := hIsog R S' s' o₁'.A o₂'.A o₁'.ab o₂'.ab ψ' χ' d hdpos hmon' hχmon' hd1' hd2'
  obtain ⟨χ, hχsq, hd1, hd2⟩ := hH.2 χ' d hχmon' hsurj hfin hd1' hd2'
  have hχmon : IsMonHom χ := (hHom S S' c o₂.A o₁.A o₂'.A o₁'.A o₂.ab o₁.ab o₁'.ab m₂.φ m₁.φ
    m₂.cart m₁.cart χ χ' hχsq hχmon').1
  refine ⟨hmon, fun b => comp_eq_comp_of_over_left_comm m₁.φ m₂.φ _ _ _ _ ψ ψ' hsq (m₁.act b) (m₂.act b) (hact' b),
    ⟨χ, d, hχmon, fun b => comp_eq_comp_of_over_left_comm m₂.φ m₁.φ _ _ _ _ χ χ' hχsq (m₂.act b) (m₁.act b) (hχact' b),
      hd1, hd2, hdp⟩,
    ⟨e, hep, hPol D.toG R gb S S' s s' c N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ ψ' hmon hsq e hpol', hint⟩, ?_⟩
  intro k _ _ t β htβ
  obtain ⟨v, hv⟩ := ‹Surjective c›.surj (UpperTheory.Gal.TranscendenceTraces.pt t)
  obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds c k t v hv
  subst hz
  have hz' : z ≫ s' = spMap β := by
    rw [← hcs, ← Category.assoc]
    exact htβ
  obtain ⟨I₁', I₂', hI₁', hI₂', hiff'⟩ := hgeo' k z β hz'
  obtain ⟨-, hT1⟩ := hTate p D R gb S S' s s' c N₁ o₁ o₁' m₁ k z
  obtain ⟨-, hT2⟩ := hTate p D R gb S S' s s' c N₂ o₂ o₂' m₂ k z
  obtain ⟨I₁, hInd₁, hev₁⟩ := hT1 I₁'
  obtain ⟨I₂, hInd₂, hev₂⟩ := hT2 I₂'
  refine ⟨I₁, I₂, hInd₁ hI₁', hInd₂ hI₂', fun n hn hnp x y => ?_⟩
  have e1 : Over.Hom.left (I₁'.ev n x) ≫ m₁.φ = Over.Hom.left (I₁.ev n x) := hev₁ n x
  have e2 : Over.Hom.left (I₂'.ev n y) ≫ m₂.φ = Over.Hom.left (I₂.ev n y) := hev₂ n y
  rw [← hiff' n hn hnp x y]
  constructor
  · intro hxy
    apply Over.OverMorphism.ext
    apply m₂.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hsq, ← Category.assoc, e1, ← Over.comp_left, hxy, e2]
    · rw [Over.w, Over.w]
  · intro hxy
    apply Over.OverMorphism.ext
    rw [Over.comp_left, ← e1, ← e2, Category.assoc, ← hsq, ← Category.assoc, ← Over.comp_left, hxy]
end
