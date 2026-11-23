module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle853
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem pow_push {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (d : ℕ) :
    ((𝟙 G') ^ d : G' ⟶ G').left ≫ φ = φ ≫ ((𝟙 G) ^ d : G ⟶ G).left := by
  obtain ⟨hpb, hm⟩ := h
  have hw : φ ≫ G.hom = G'.hom ≫ f := hpb.w
  let P : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ (by simpa using hw)
  have key : ∀ n : ℕ, ((𝟙 G') ^ n : G' ⟶ G').left ≫ φ = (P ^ n).left := by
    intro n
    induction n with
    | zero =>
      let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk ((1 : G' ⟶ G').left ≫ φ)
        (by rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
      have e : (x₀ * x₀).left = x₀.left := by
        rw [hm G' 1 1 x₀ x₀ rfl rfl, _root_.mul_one (1 : G' ⟶ G')]
        rfl
      have e2 : x₀ * x₀ = x₀ := Over.OverMorphism.ext e
      have e3 : x₀ = 1 := by simpa using e2
      rw [pow_zero, pow_zero]
      exact congrArg CommaMorphism.left e3
    | succ n ih =>
      rw [pow_succ, pow_succ, ← hm G' _ _ (P ^ n) P ih.symm (by simp [P])]
  rw [key d]
  have hP : P ≫ ((𝟙 G) ^ d) = P ^ d := by rw [MonObj.comp_pow, Category.comp_id]
  rw [← hP]
  rfl

private theorem qinv_pull {S S' : Scheme.{0}} {A₁' A₂' : Over S'} {A₁ A₂ : Over S} [GrpObj A₁'] [GrpObj A₁] {f : S' ⟶ S}
    {φ₁ : A₁'.left ⟶ A₁.left} {φ₂ : A₂'.left ⟶ A₂.left} (c₁ : IsGrpPullback A₁' A₁ f φ₁) {ψ : A₁ ⟶ A₂} {χ : A₂ ⟶ A₁}
    {ψ' : A₁' ⟶ A₂'} {χ' : A₂' ⟶ A₁'} (e : ψ'.left ≫ φ₂ = φ₁ ≫ ψ.left) (e' : χ'.left ≫ φ₁ = φ₂ ≫ χ.left) {d : ℕ}
    (h : ψ ≫ χ = (𝟙 A₁) ^ d) : ψ' ≫ χ' = (𝟙 A₁') ^ d := by
  apply Over.OverMorphism.ext
  apply c₁.1.hom_ext
  · rw [Over.comp_left, Category.assoc, e', ← Category.assoc, e, Category.assoc, ← Over.comp_left, h, pow_push c₁]
  · rw [Over.w, Over.w]

theorem UpperTheory.Gal.G3.pTransPull :
    HomPull → TatePull → TransPull := by
  intro hHom hTate p _ D G L R _ _ gb S S' s s' f hf N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ h hT
  obtain ⟨hmon, hact, ⟨χ, d, hχmon, hχact, e1, e2, hd⟩, ⟨c, hc, ⟨lb⟩, tt⟩, hgeo⟩ := hT
  obtain ⟨ψ', hψ, hmon', hact', hlb'⟩ := hHom D.toG R gb S S' s s' f N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ
  obtain ⟨χ', hχ, hχmon', hχact', -⟩ := hHom D.toG R gb S S' s s' f N₂ N₁ o₂ o₁ o₂' o₁' m₂ m₁ χ
  refine ⟨ψ', ⟨hmon' hmon, hact' hact, ⟨χ', d, hχmon' hχmon, hχact' hχact, qinv_pull m₁.cart hψ hχ e1,
    qinv_pull m₂.cart hχ hψ e2, hd⟩, ⟨c, hc, hlb' c ⟨lb⟩, tt⟩, ?_⟩, hψ⟩
  intro k _ _ t β ht
  obtain ⟨I₁, I₂, hI₁, hI₂, hev⟩ := hgeo k (t ≫ f) β (by rw [Category.assoc, hf, ht])
  obtain ⟨I₁', hI₁', hev₁⟩ := (hTate p D R gb S S' s s' f N₁ o₁ o₁' m₁ k t).1 I₁
  obtain ⟨I₂', hI₂', hev₂⟩ := (hTate p D R gb S S' s s' f N₂ o₂ o₂' m₂ k t).1 I₂
  refine ⟨I₁', I₂', hI₁' hI₁, hI₂' hI₂, fun n hn hnp x y => ?_⟩
  rw [← hev n hn hnp x y]
  constructor
  · intro e
    apply Over.OverMorphism.ext
    have key := congrArg (fun a => a.left ≫ m₂.φ) e
    simp only [Over.comp_left, Category.assoc, hψ] at key
    erw [← Category.assoc, hev₁ n x, hev₂ n y] at key
    rw [Over.comp_left]
    exact key
  · intro e
    apply Over.OverMorphism.ext
    apply m₂.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hψ, ← Category.assoc]
      erw [hev₁ n x, hev₂ n y]
      rw [← Over.comp_left, e]
    · rw [Over.w, Over.w]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitCart :
    TransIso → WitCart := by
  intro hI p _ D G L R _ _ gb N' N X' X u hu π Φ hW
  obtain ⟨-, o, ψ, φ, hT, rfl⟩ := hW
  have hψ : IsIso ψ := hI p D G L R gb X'.X X'.s N' N X'.univ o ψ u hu hT
  have hl : IsIso ψ.left := inferInstanceAs (IsIso ((Over.forget _).map ψ))
  have h₁ : IsPullback ψ.left X'.univ.A.hom o.A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩
  have h₂ := h₁.paste_horiz φ.cart.1
  rwa [Category.id_comp] at h₂
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitDeep :
    KNBasic → GenSm → TransDeep → WitComp → WitForget → WitDeep := by
  intro _ hSm hTD hWC hWF p _ D G L R _ _ gb X N' N h hI
  obtain ⟨k, hk, hAk, hex⟩ := hTD p D G L R gb h hI
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd (Nat.coprime_zero_left _ |>.mp hk) (Fact.out : p.Prime).one_lt.ne'
    · exact hpos
  let Nk : Lv p := ⟨↑N * k, le_trans N.2.1 (Nat.le_mul_of_pos_right _ hk0), Nat.Coprime.mul_left N.2.2 hk⟩
  let M : Lv p := ⟨↑N' * (↑N * k), le_trans Nk.2.1 (Nat.le_mul_of_pos_left _ (by have := N'.2.1; omega)),
    Nat.Coprime.mul_left N'.2.2 Nk.2.2⟩
  have hNkM : (↑Nk : ℕ) ∣ ↑M := Dvd.intro_left _ rfl
  refine ⟨M, Dvd.intro _ rfl, ?_, ?_⟩
  · intro u hu
    exact hAk N u (UpperTheory.Gal.Int.Geo.KN_anti hNkM hu)
  · haveI : Smooth (X Nk).s := (hSm p D R gb Nk (X Nk)).1
    haveI : IsLocallyNoetherian (X Nk).X := LocallyOfFiniteType.isLocallyNoetherian (X Nk).s
    obtain ⟨o, ψ, ht⟩ := hex N (X Nk).X (X Nk).s (X Nk).univ
    obtain ⟨π, ⟨hπ, ⟨φ⟩⟩, -⟩ := (X N).rep (X Nk).X (X Nk).s o
    have w₂ : Wit L h (X Nk) (X N) π (ψ.left ≫ φ.φ) := ⟨hπ, o, ψ, φ, ht, rfl⟩
    obtain ⟨c, Φc, w₁, -⟩ := hWF p D G L R gb Nk M hNkM (X Nk) (X M)
    have := (hWC p D G L R gb M Nk N (X M) (X Nk) (X N) 1 h).2 hI (hAk N) c Φc π _ w₁ w₂
    rw [_root_.mul_one] at this
    exact ⟨_, _, this⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitTrans :
    KNBasic → PtEq → PtOrbit → WitComp → WitTrans := by
  intro hKN hEq hOrb hWC p _ D G L R _ _ gb X N' N π Φ hW k _ _ x y hxy
  obtain ⟨ox, oy, mx, my, hys, u, hu, θ, hθ, hθΦ⟩ := hOrb p D G L R gb N' N (X N') (X N) π Φ hW k x y hxy
  refine ⟨u, hu, fun π' Φ' hW' => ?_⟩
  have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
  have h1 : (1 : G.GAf) ∈ L.KN 1 := one_mem _
  have hid := (hWC p D G L R gb N' N' N' (X N') (X N') (X N') 1 1).1 1 (one_mem _)
  obtain ⟨hA, hB⟩ := hEq p D G L R gb N' N' N' (X N') (X N') (X N') u 1 u 1 π' Φ' (𝟙 _) (𝟙 _) hW' hid
    (UpperTheory.Gal.Int.Geo.integ_of_mem hu1) (UpperTheory.Gal.Int.Geo.integ_of_mem h1)
    ((hKN p D G L N').1 u hu1) ((hKN p D G L N').1 1 h1) (one_mem _) (by simp) k (x ≫ (X N').s) x y rfl hys
    ox oy mx my θ hθ
  refine ⟨by simpa using hA, fun a ha => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ mx.φ = a :=
    ⟨_, mx.cart.1.lift_fst a (𝟙 _) (by rw [ha, Category.id_comp])⟩
  simp only [Category.assoc]
  rw [reassoc_of% hB, hθΦ]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem square_map_isSquare {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (ψ : A ⟶ B) :
    Geo.Tor.IsSquare ψ.left (Hecke.sq2 ψ) := by
  constructor
  · rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  · rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem UpperTheory.Gal.G3.pHomPull :
    HomPull := by
  intro G₀ R _ _ gb S S' s s' f N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ
  let g : Over.mk (o₁'.A.hom ≫ f) ⟶ o₂.A := GlobalTheory.ObjPull.pushEquiv m₁.cart o₁'.A (𝟙 o₁'.A) ≫ ψ
  refine ⟨(GlobalTheory.ObjPull.pushEquiv m₂.cart o₁'.A).symm g, ?_⟩
  set ψ' := (GlobalTheory.ObjPull.pushEquiv m₂.cart o₁'.A).symm g with hψ'eq
  have hψ' : ψ'.left ≫ m₂.φ = m₁.φ ≫ ψ.left := by
    rw [← GlobalTheory.ObjPull.pushEquiv_left m₂.cart, hψ'eq, MulEquiv.apply_symm_apply]
    simp only [g, Over.comp_left, GlobalTheory.ObjPull.pushEquiv_left, Over.id_left, Category.id_comp]
  have key : ∀ (T : Over S') (z : T ⟶ o₁'.A),
      GlobalTheory.ObjPull.pushEquiv m₂.cart T (z ≫ ψ') = GlobalTheory.ObjPull.pushEquiv m₁.cart T z ≫ ψ := by
    intro T z
    apply Over.OverMorphism.ext
    simp only [GlobalTheory.ObjPull.pushEquiv_left, Over.comp_left, Category.assoc, hψ']
  have inj : ∀ {T : Over S'} (u v : T ⟶ o₂'.A), u.left ≫ m₂.φ = v.left ≫ m₂.φ → u = v := by
    intro T u v huv
    apply (GlobalTheory.ObjPull.pushEquiv m₂.cart T).injective
    apply Over.OverMorphism.ext
    rw [GlobalTheory.ObjPull.pushEquiv_left, GlobalTheory.ObjPull.pushEquiv_left, huv]
  have hsq : m₁.φ₂ ≫ Hecke.sq2 ψ = Hecke.sq2 ψ' ≫ m₂.φ₂ := by
    have a := MapComp.isSquare_comp m₁.sq (square_map_isSquare ψ)
    have b := MapComp.isSquare_comp (square_map_isSquare ψ') m₂.sq
    rw [hψ'] at b
    exact MapComp.isSquare_unique a b
  refine ⟨hψ', ?_, ?_, ?_⟩
  · intro hψ
    apply GlobalTheory.Serre.isMonHom_of_mul_comp
    intro T x y
    apply (GlobalTheory.ObjPull.pushEquiv m₂.cart T).injective
    rw [map_mul, key, key, key, map_mul, MonObj.mul_comp]
  · intro hc c
    apply inj
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hψ', m₂.act,
      ← Category.assoc ψ'.left, hψ', ← Category.assoc, m₁.act, Category.assoc, Category.assoc,
      ← Over.comp_left, ← Over.comp_left, hc c]
  · intro c hc
    obtain ⟨e⟩ := hc
    have h1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o₁.isLB _ _) (pull_isLB o₂.isLB _)).2 e
    have hP1 := (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o₁.isLB m₁.φ₂)).2 m₁.pol
    have hP2 := (GlobalTheory.CechPic.cls_eq_iff o₂'.isLB (pull_isLB o₂.isLB m₂.φ₂)).2 m₂.pol
    rw [GlobalTheory.CechPic.cls_pull o₁.isLB] at hP1
    rw [GlobalTheory.CechPic.cls_pull o₂.isLB] at hP2
    rw [GlobalTheory.CechPic.cls_pull o₂.isLB, GlobalTheory.CechPic.cls_linComb o₁.isLB] at h1
    simp only [GlobalTheory.CechPic.pull_id] at h1
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o₁'.isLB _ _) (pull_isLB o₂'.isLB _)).1 ?_⟩
    rw [GlobalTheory.CechPic.cls_linComb o₁'.isLB, GlobalTheory.CechPic.cls_pull o₂'.isLB, hP1, hP2]
    simp only [GlobalTheory.CechPic.pull_id]
    rw [← GlobalTheory.CechPic.pull_comp, ← hsq, GlobalTheory.CechPic.pull_comp, ← h1]

    simp [map_sum, map_zsmul]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

namespace UpperTheory.Gal.G3

private theorem pow_left {S S' : Scheme.{0}} {c : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
    {a : A'.left ⟶ A.left} (h : IsGrpPullback A' A c a) (d : ℕ) :
    ((𝟙 A') ^ d).left ≫ a = a ≫ ((𝟙 A) ^ d).left := by
  have e1 := GlobalTheory.ObjPull.pushEquiv_left h A' ((𝟙 A') ^ d)
  have e2 := GlobalTheory.ObjPull.pushEquiv_left h A' (𝟙 A')
  rw [map_pow] at e1
  have e3 : (GlobalTheory.ObjPull.pushEquiv h A' (𝟙 A')) ^ d = GlobalTheory.ObjPull.pushEquiv h A' (𝟙 A') ≫ (𝟙 A) ^ d := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [← e1, e3, Over.comp_left, e2]
  simp

private theorem push_comp {S S' : Scheme.{0}} {c : S' ⟶ S} {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj B]
    [GrpObj A'] [GrpObj B'] {a : A'.left ⟶ A.left} {b : B'.left ⟶ B.left} (hA : IsGrpPullback A' A c a)
    (hB : IsGrpPullback B' B c b) (ψ : A ⟶ B) (ψ' : A' ⟶ B') (e : ψ'.left ≫ b = a ≫ ψ.left) (T : Over S') (x : T ⟶ A') :
    GlobalTheory.ObjPull.pushEquiv hA T x ≫ ψ = GlobalTheory.ObjPull.pushEquiv hB T (x ≫ ψ') := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, GlobalTheory.ObjPull.pushEquiv_left, GlobalTheory.ObjPull.pushEquiv_left, Over.comp_left, Category.assoc,
    Category.assoc, e]

private theorem monHom_desc {S S' : Scheme.{0}} (c : S' ⟶ S) [Flat c] [Surjective c] {A B : Over S} {A' B' : Over S'}
    [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] {a : A'.left ⟶ A.left} {b : B'.left ⟶ B.left}
    (hA : IsGrpPullback A' A c a) (hB : IsGrpPullback B' B c b) (ψ : A ⟶ B) (ψ' : A' ⟶ B')
    (e : ψ'.left ≫ b = a ≫ ψ.left) [IsMonHom ψ'] : IsMonHom ψ := by
  apply GlobalTheory.Serre.isMonHom_of_mul_comp
  intro T x y
  let T' : Over S' := Over.mk (pullback.snd T.hom c)
  let q : Over.mk (T'.hom ≫ c) ⟶ T := Over.homMk (pullback.fst T.hom c) (by simp [T', pullback.condition])
  have hq : Epi (pullback.fst T.hom c) := Flat.epi_of_flat_of_surjective _
  have hx : q ≫ x = GlobalTheory.ObjPull.pushEquiv hA T' ((GlobalTheory.ObjPull.pushEquiv hA T').symm (q ≫ x)) := by simp
  have hy : q ≫ y = GlobalTheory.ObjPull.pushEquiv hA T' ((GlobalTheory.ObjPull.pushEquiv hA T').symm (q ≫ y)) := by simp
  set x' := (GlobalTheory.ObjPull.pushEquiv hA T').symm (q ≫ x)
  set y' := (GlobalTheory.ObjPull.pushEquiv hA T').symm (q ≫ y)
  have key : q ≫ ((x * y) ≫ ψ) = q ≫ (x ≫ ψ * y ≫ ψ) := by
    calc q ≫ ((x * y) ≫ ψ) = (q ≫ x * q ≫ y) ≫ ψ := by rw [← Category.assoc, MonObj.comp_mul]
      _ = GlobalTheory.ObjPull.pushEquiv hA T' (x' * y') ≫ ψ := by rw [hx, hy, map_mul]
      _ = GlobalTheory.ObjPull.pushEquiv hB T' (x' ≫ ψ' * y' ≫ ψ') := by
        rw [push_comp hA hB ψ ψ' e, MonObj.mul_comp]
      _ = (GlobalTheory.ObjPull.pushEquiv hA T' x' ≫ ψ) * (GlobalTheory.ObjPull.pushEquiv hA T' y' ≫ ψ) := by
        rw [map_mul, push_comp hA hB ψ ψ' e, push_comp hA hB ψ ψ' e]
      _ = q ≫ (x ≫ ψ * y ≫ ψ) := by
        rw [← hx, ← hy, MonObj.comp_mul, Category.assoc, Category.assoc]
  ext1
  have hl := congrArg Over.Hom.left key
  simp only [Over.comp_left, q, Over.homMk_left] at hl
  exact (cancel_epi _).1 hl

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.pHomDesc :
    EtDesc → HomDesc := by
  intro etd S S' _ c _ _ _ A B _ _ _ _ A' B' _ _ _ _ hAab hBab hB'ab a b hA hB ψ ψ' e hψ'
  haveI : Flat c := inferInstance
  have hψ : IsMonHom ψ := monHom_desc c hA hB ψ ψ' e
  refine ⟨hψ, ?_⟩
  intro χ' d hχ' hsurj hfin h1 h2
  haveI : Smooth B'.hom := hB'ab.smooth
  haveI : AlgebraicGeometry.IsReduced B'.left := GlobalTheory.isReduced_of_smooth_of_isReduced B'.hom
  haveI : IsFinite b := MorphismProperty.of_isPullback (P := @IsFinite) hB.1.flip ‹_›
  haveI : Etale b := MorphismProperty.of_isPullback (P := @Etale) hB.1.flip ‹_›
  haveI : Surjective b := MorphismProperty.of_isPullback (P := @Surjective) hB.1.flip ‹_›
  haveI : Flat a := MorphismProperty.of_isPullback (P := @Flat) hA.1.flip ‹_›
  haveI : Surjective a := MorphismProperty.of_isPullback (P := @Surjective) hA.1.flip ‹_›
  haveI : IsProper A.hom := hAab.proper
  have ea : a ≫ A.hom = A'.hom ≫ c := hA.1.w
  have eb : b ≫ B.hom = B'.hom ≫ c := hB.1.w
  have hcond : (χ'.left ≫ a) ≫ A.hom = b ≫ B.hom := by
    rw [Category.assoc, ea, ← Category.assoc, Over.w χ', eb]
  have hpts : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x y : sp Ω ⟶ B'.left), x ≫ b = y ≫ b →
      x ≫ (χ'.left ≫ a) = y ≫ (χ'.left ≫ a) := by
    intro Ω _ _ x y hxy
    haveI := hfin
    have lift : ∀ z : sp Ω ⟶ B'.left, ∃ z' : sp Ω ⟶ A'.left, z' ≫ ψ'.left = z := by
      intro z
      obtain ⟨v, hv⟩ := hsurj.surj (UpperTheory.Gal.TranscendenceTraces.pt z)
      obtain ⟨z', hz', -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds ψ'.left Ω z v hv
      exact ⟨z', hz'⟩
    obtain ⟨x', hx'⟩ := lift x
    obtain ⟨y', hy'⟩ := lift y
    have red : ∀ (z : sp Ω ⟶ B'.left) (z' : sp Ω ⟶ A'.left), z' ≫ ψ'.left = z →
        z ≫ χ'.left ≫ a = z' ≫ a ≫ ((𝟙 A) ^ d).left := by
      intro z z' hz
      rw [← hz, ← pow_left hA d, ← h1, Over.comp_left]
      simp only [Category.assoc]
    rw [red x x' hx', red y y' hy']
    have hx2 : x' ≫ A'.hom = x ≫ B'.hom := by rw [← hx', Category.assoc, Over.w ψ']
    have hy2 : y' ≫ A'.hom = y ≫ B'.hom := by rw [← hy', Category.assoc, Over.w ψ']
    have hyx : (y ≫ B'.hom) ≫ c = (x ≫ B'.hom) ≫ c := by
      rw [Category.assoc, Category.assoc, ← eb, ← Category.assoc, ← Category.assoc, hxy]
    let T' : Over S' := Over.mk (x ≫ B'.hom)
    let U : Over.mk (T'.hom ≫ c) ⟶ A := Over.homMk (x' ≫ a) (by
      show (x' ≫ a) ≫ A.hom = (x ≫ B'.hom) ≫ c
      rw [Category.assoc, ea, ← Category.assoc, hx2])
    let V : Over.mk (T'.hom ≫ c) ⟶ A := Over.homMk (y' ≫ a) (by
      show (y' ≫ a) ≫ A.hom = (x ≫ B'.hom) ≫ c
      rw [Category.assoc, ea, ← Category.assoc, hy2, hyx])
    have hUV : U ≫ ψ = V ≫ ψ := by
      ext1
      simp only [Over.comp_left, U, V, Over.homMk_left]
      rw [Category.assoc, ← e, ← Category.assoc, hx', Category.assoc, ← e, ← Category.assoc, hy', hxy]
    have hW : (U / V) ≫ ψ = 1 := by
      rw [div_eq_mul_inv, MonObj.mul_comp, GrpObj.inv_comp, hUV, mul_inv_cancel]
    have hW' : GlobalTheory.ObjPull.pushEquiv hA T' ((GlobalTheory.ObjPull.pushEquiv hA T').symm (U / V)) = U / V := by simp
    set W' := (GlobalTheory.ObjPull.pushEquiv hA T').symm (U / V)
    have hW'ψ : W' ≫ ψ' = 1 := by
      apply (GlobalTheory.ObjPull.pushEquiv hB T').injective
      rw [← push_comp hA hB ψ ψ' e, hW', hW, map_one]
    have hpow : W' ^ d = 1 := by
      calc W' ^ d = W' ≫ (𝟙 A') ^ d := by rw [MonObj.comp_pow, Category.comp_id]
        _ = W' ≫ ψ' ≫ χ' := by rw [h1]
        _ = 1 := by rw [← Category.assoc, hW'ψ, MonObj.one_comp]
    have hWd : (U / V) ^ d = 1 := by rw [← hW', ← map_pow, hpow, map_one]
    have hUd : U ^ d = V ^ d := by rwa [div_pow, div_eq_one] at hWd
    have hU : U ^ d = U ≫ (𝟙 A) ^ d := by rw [MonObj.comp_pow, Category.comp_id]
    have hV : V ^ d = V ≫ (𝟙 A) ^ d := by rw [MonObj.comp_pow, Category.comp_id]
    have hl := congrArg Over.Hom.left hUd
    rw [hU, hV, Over.comp_left, Over.comp_left] at hl
    simpa only [U, V, Over.homMk_left, Category.assoc] using hl
  obtain ⟨hbe, g, hg⟩ := etd b B.hom A.hom (χ'.left ≫ a) hcond hpts
  have hgA : g ≫ A.hom = B.hom := by
    rw [← cancel_epi b, ← Category.assoc, hg, hcond]
  have ha : Epi a := Flat.epi_of_flat_of_surjective a
  refine ⟨Over.homMk g hgA, hg.symm, ?_, ?_⟩
  · ext1
    rw [← cancel_epi a]
    simp only [Over.comp_left, Over.homMk_left]
    rw [← Category.assoc, ← e, Category.assoc, hg, ← Category.assoc, ← Over.comp_left, h1, pow_left hA d]
  · ext1
    rw [← cancel_epi b]
    simp only [Over.comp_left, Over.homMk_left]
    rw [← Category.assoc, hg, Category.assoc, ← e, ← Category.assoc, ← Over.comp_left, h2, pow_left hB d]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private lemma twisted_kernel_forms_nonvanishing (hE : EtDesc) (k : Type) [Field k] [IsAlgClosed k] (A A₁ A₂ : Over (Sp k)) [GrpObj A]
    [GrpObj A₁] [GrpObj A₂] (hA : IsAbelianScheme A) (hA₂ : IsAbelianScheme A₂)
    (ψ₁ : A ⟶ A₁) (ψ₂ : A ⟶ A₂) [IsMonHom ψ₁] [IsMonHom ψ₂] [IsFinite ψ₁.left] [Etale ψ₁.left] [Surjective ψ₁.left]
    (hker : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp k) (a : Over.mk t ⟶ A), a ≫ ψ₁ = 1 → a ≫ ψ₂ = 1) :
    ∃ θ : A₁ ⟶ A₂, ψ₁ ≫ θ = ψ₂ := by
  haveI := hA.smooth
  haveI := hA₂.proper
  haveI : AlgebraicGeometry.IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  have hw : ψ₂.left ≫ A₂.hom = ψ₁.left ≫ A₁.hom := by rw [Over.w, Over.w]
  obtain ⟨hepi, g, hg⟩ := hE ψ₁.left A₁.hom A₂.hom ψ₂.left hw (by
    intro Ω _ _ x y hxy
    have hxy' : x ≫ A.hom = y ≫ A.hom := by
      rw [← Over.w ψ₁, ← Category.assoc, hxy, Category.assoc]
    let X : Over.mk (x ≫ A.hom) ⟶ A := Over.homMk x
    let Y : Over.mk (x ≫ A.hom) ⟶ A := Over.homMk y hxy'.symm
    have h1 : X ≫ ψ₁ = Y ≫ ψ₁ := Over.OverMorphism.ext hxy
    have h2 : (X * Y⁻¹) ≫ ψ₁ = 1 := by
      have e := (IsMonHom.monoidHom ψ₁ (Over.mk (x ≫ A.hom))).map_mul X Y⁻¹
      have e' := map_inv (IsMonHom.monoidHom ψ₁ (Over.mk (x ≫ A.hom))) Y
      simp only [IsMonHom.monoidHom_apply] at e e'
      rw [e, e', h1, mul_inv_cancel]
    have h3 := hker Ω (x ≫ A.hom) (X * Y⁻¹) h2
    have e := (IsMonHom.monoidHom ψ₂ (Over.mk (x ≫ A.hom))).map_mul X Y⁻¹
    have e' := map_inv (IsMonHom.monoidHom ψ₂ (Over.mk (x ≫ A.hom))) Y
    simp only [IsMonHom.monoidHom_apply] at e e'
    rw [e, e', mul_inv_eq_one] at h3
    exact congrArg CommaMorphism.left h3)
  haveI := hepi
  refine ⟨Over.homMk g ?_, ?_⟩
  · rw [← cancel_epi ψ₁.left, ← Category.assoc, hg, hw]
  · exact Over.OverMorphism.ext hg

theorem UpperTheory.Gal.G3.pQuotUniq :
    EtDesc → QuotUniq := by
  intro hE k _ _ A A₁ A₂ _ _ _ _ _ _ hA hA₁ hA₂ ψ₁ ψ₂ h₁ h₂ f₁ e₁ s₁ f₂ e₂ s₂ hker
  obtain ⟨θ, hθ⟩ := twisted_kernel_forms_nonvanishing hE k A A₁ A₂ hA hA₂ ψ₁ ψ₂ (fun Ω _ _ t a => (hker Ω t a).1)
  obtain ⟨θ', hθ'⟩ := twisted_kernel_forms_nonvanishing hE k A A₂ A₁ hA hA₁ ψ₂ ψ₁ (fun Ω _ _ t a => (hker Ω t a).2)
  haveI : Flat ψ₁.left := inferInstance
  haveI : Flat ψ₂.left := inferInstance
  haveI : Epi ψ₁ := GlobalTheory.FlatQuotient.epi_of_flat_surjective ψ₁
  haveI : Epi ψ₂ := GlobalTheory.FlatQuotient.epi_of_flat_surjective ψ₂
  haveI : Epi (ψ₁ ⊗ₘ ψ₁) := GlobalTheory.FlatQuotient.epi_tensorHom ψ₁ ψ₁
  have i1 : θ ≫ θ' = 𝟙 _ := by
    rw [← cancel_epi ψ₁, ← Category.assoc, hθ, hθ', Category.comp_id]
  have i2 : θ' ≫ θ = 𝟙 _ := by
    rw [← cancel_epi ψ₂, ← Category.assoc, hθ', hθ, Category.comp_id]
  refine ⟨θ, ⟨θ', i1, i2⟩, ⟨?_, ?_⟩, hθ⟩
  · rw [← IsMonHom.one_hom ψ₁, Category.assoc, hθ, IsMonHom.one_hom ψ₂]
  · have h1 : (ψ₁ ⊗ₘ ψ₁) ≫ (θ ⊗ₘ θ) = ψ₂ ⊗ₘ ψ₂ := by
      rw [tensorHom_comp_tensorHom, hθ]
    rw [← cancel_epi (ψ₁ ⊗ₘ ψ₁), ← Category.assoc, ← IsMonHom.mul_hom ψ₁, Category.assoc, hθ,
      IsMonHom.mul_hom ψ₂, ← Category.assoc, h1]
end
