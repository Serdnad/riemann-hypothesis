module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2682
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLevelObjPullbackOfCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle001
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem tiso_congr {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase D.toG R}
    {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) {k : Type} [Field k] {t t' : Sp k ⟶ S} (e : t = t')
    (I : UpperTheory.Gal.Int.Geo.TIso o t) (hI : Ind o I) :
    ∃ J : UpperTheory.Gal.Int.Geo.TIso o t', Ind o J ∧ ∀ n x, (J.ev n x).left = (I.ev n x).left := by
  subst e
  exact ⟨I, hI, fun _ _ => rfl⟩

private theorem lbIso_hecke_lbPow_one {X : Scheme.{0}} {P : LB X} (hP : P.IsLB) : LBIso (Hecke.lbPow P 1) P := by
  have h1 : (Hecke.lbPow P 1).IsLB := LB.isLB_linComb hP _ _
  have h2 : (lbPow P 1).IsLB := GlobalTheory.isLB_lbPow hP 1
  have h3 : ((Hecke.lbPow P 1).pull (𝟙 X)).IsLB := pull_isLB h1 _
  exact LBIso.trans h1 h2 hP
    (LBIso.trans h1 h3 h2 (GlobalTheory.DescendedPrincipal.lbIso_pull_id h1).symm
      (GlobalTheory.BiextPairing.lbIso_lbPow_hecke hP 1).symm)
    (GlobalTheory.lbIso_lbPow_one hP)

theorem UpperTheory.Gal.G3.pTransOfMap :
    MultBasic → RelComp → TatePull → TransOfMap := by
  intro MB RC TP p _ D G L R _ _ gb S s N o o' m
  have hw : m.φ ≫ o'.A.hom = o.A.hom := by simpa using m.cart.1.w
  let θ : o.A ⟶ o'.A := Over.homMk m.φ hw
  have hθ : θ.left = m.φ := rfl
  refine ⟨θ, rfl, ?_⟩
  have hmon : IsMonHom θ :=
    GlobalTheory.AmpleRigid.isMonHom_of_mul_comp θ
      (fun T => GlobalTheory.AmpleRigid.mul_comp_of_grpPullback_id (T := T) θ m.cart)
  have hact : ∀ c, o.act.act c ≫ θ = θ ≫ o'.act.act c := by
    intro c
    ext
    simpa [θ] using m.act c
  haveI : IsIso m.φ := m.cart.1.isIso_fst_of_isIso
  haveI : IsIso θ := by
    have : IsIso ((Over.forget S).map θ) := by
      change IsIso m.φ
      infer_instance
    exact isIso_of_reflects_iso θ (Over.forget S)
  have hsq : Hecke.sq2 θ = m.φ₂ := by
    apply Hecke.ProdGalois.grpScheme_square_hom_ext_fst_snd
    · rw [Hecke.ProdGalois.grpSchemeSquareProductMap_comp_fst, m.sq.1, hθ]
    · rw [Hecke.ProdGalois.grpSchemeSquareProductMap_comp_snd, m.sq.2, hθ]
  have hmon' : IsMonHom (asIso θ).hom := hmon
  have hinvmon : IsMonHom (inv θ) := (inferInstance : IsMonHom (asIso θ).inv)
  refine ⟨hmon, hact, ⟨inv θ, 1, hinvmon, ?_, ?_, ?_, by simp⟩, ⟨1, by simp, ?_, ?_⟩, ?_⟩
  · intro c
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← hact c, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · rw [pow_one]
    exact IsIso.hom_inv_id θ
  · rw [pow_one]
    exact IsIso.inv_hom_id θ
  · refine ⟨?_⟩
    rw [hsq]
    exact LBIso.trans (LB.isLB_linComb o.isLB _ _) o.isLB (pull_isLB o'.isLB _)
      (lbIso_hecke_lbPow_one o.isLB) m.pol
  · exact (MB p).2.2 D G L 1 (Subgroup.one_mem _)
  · intro k _ _ t β ht
    obtain ⟨I₁, hI₁⟩ := o.geom k t β ht
    obtain ⟨I₂, hind, hev⟩ := (TP p D R gb S S s s (𝟙 S) (↑N) o' o m k t).2 I₁
    obtain ⟨J, hJ, hJe⟩ := tiso_congr o' (Category.comp_id t) I₂ (hind hI₁)
    refine ⟨I₁, J, hI₁, hJ, ?_⟩
    intro n hn hcop x y
    have key : I₁.ev n x ≫ θ = J.ev n x := by
      ext
      exact (hev n x).trans (hJe n x).symm
    rw [key]
    have hint : Integ L 1 := by
      intro v hv
      simpa using hv
    have hR := (RC p D G L R gb S s (↑N) (↑N) (↑N) o' o' o' k t J J J (𝟙 _) (𝟙 _) 1 1
      inferInstance inferInstance hint).1 n hn hcop x y
    simpa using hR
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

namespace UpperTheory.Gal.G3

section Maps

open GlobalTheory.UPel.HT.Hecke

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

private theorem exists_map_id {b : GBase G R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : GObj b N s) :
    ∃ m : GObjMap o o (𝟙 S), m.φ = 𝟙 _ :=
  ⟨{ φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id o.A, sq := ⟨by simp, by simp⟩,
     act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB, eta := fun y => by simp }, rfl⟩

private theorem exists_map_comp {b : GBase G R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R}
    {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g) : ∃ m : GObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
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

end Maps

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.pWitComp :
    TransSelf → TransComp → TransPull → WitComp := by
  intro hS hC hP
  intro p _ D G L R _ _ gb N₁ N₂ N₃ X₁ X₂ X₃ h h'
  refine ⟨fun u hu => ?_, fun hI hA π Φ π' Φ' hW hW' => ?_⟩
  · obtain ⟨m, hm⟩ := exists_map_id X₁.univ
    refine ⟨by simp, X₁.univ, 𝟙 _, m, (hS p D G L R gb X₁.X X₁.s N₁).1 X₁.univ u hu, ?_⟩
    rw [hm]
    simp
  · obtain ⟨hπ, o, ψ, φ, hT, hΦ⟩ := hW
    obtain ⟨hπ', o', ψ', φ', hT', hΦ'⟩ := hW'
    obtain ⟨o'', ⟨m''⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero X₁.s π hπ o'
    obtain ⟨ψ'', hT'', hsq⟩ := hP p D G L R gb X₂.X X₁.X X₂.s X₁.s π hπ _ _ X₂.univ o' o o'' φ m'' ψ' h' hT'
    have hTT := hC p D G L R gb X₁.X X₁.s N₁ N₂ N₃ X₁.univ o o'' ψ ψ'' h h' hI hA hT hT''
    obtain ⟨mm, hmm⟩ := exists_map_comp m'' φ'
    refine ⟨by rw [Category.assoc, hπ', hπ], o'', ψ ≫ ψ'', mm, hTT, ?_⟩
    rw [hmm, hΦ, hΦ', Over.comp_left, Category.assoc, Category.assoc, ← Category.assoc φ.φ, ← hsq,
      Category.assoc]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem square_map_comp {S : Scheme.{0}} {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [GrpObj C] [IsCommMonObj C] (f : A ⟶ B) (g : B ⟶ C) :
    Hecke.sq2 f ≫ Hecke.sq2 g = Hecke.sq2 (f ≫ g) := by
  unfold Hecke.sq2
  rw [← Over.comp_left]
  congr 1
  ext <;> simp

private theorem square_map_id {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] :
    Hecke.sq2 (𝟙 A) = 𝟙 _ := by
  simp [Hecke.sq2]

private theorem cls_pow' {X : Scheme.{0}} {P : LB X} (hP : P.IsLB) (n : ℕ) (h : (Hecke.lbPow P n).IsLB) :
    GlobalTheory.CechPic.cls (Hecke.lbPow P n) h = n • GlobalTheory.CechPic.cls P hP := by
  unfold Hecke.lbPow at h ⊢
  rw [GlobalTheory.CechPic.cls_linComb hP]
  simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

private theorem bundle_cancel {S : Scheme.{0}} {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [GrpObj C] [IsCommMonObj C] (θ : A ⟶ B) [IsIso θ] (χ : B ⟶ C) (P : LB (G2 A).left) (Q : LB (G2 B).left)
    (T : LB (G2 C).left) (hP : P.IsLB) (hQ : Q.IsLB) (hT : T.IsLB) (c : ℕ)
    (h₁ : LBIso (Hecke.lbPow P 1) (Q.pull (Hecke.sq2 θ)))
    (h₂ : LBIso (Hecke.lbPow P c) (T.pull (Hecke.sq2 (θ ≫ χ)))) :
    LBIso (Hecke.lbPow Q c) (T.pull (Hecke.sq2 χ)) := by
  have hQθ := pull_isLB hQ (Hecke.sq2 θ)
  have hTχ := pull_isLB hT (Hecke.sq2 χ)
  have hTθχ := pull_isLB hT (Hecke.sq2 (θ ≫ χ))
  have hP1 : (Hecke.lbPow P 1).IsLB := LB.isLB_linComb hP _ _
  have hPc : (Hecke.lbPow P c).IsLB := LB.isLB_linComb hP _ _
  have hQc : (Hecke.lbPow Q c).IsLB := LB.isLB_linComb hQ _ _
  rw [← GlobalTheory.CechPic.cls_eq_iff hP1 hQθ, cls_pow' hP, GlobalTheory.CechPic.cls_pull hQ] at h₁
  rw [← GlobalTheory.CechPic.cls_eq_iff hPc hTθχ, cls_pow' hP, GlobalTheory.CechPic.cls_pull hT] at h₂
  rw [← GlobalTheory.CechPic.cls_eq_iff hQc hTχ, cls_pow' hQ, GlobalTheory.CechPic.cls_pull hT]
  have key : ∀ x, GlobalTheory.CechPic.pull (Hecke.sq2 (inv θ)) (GlobalTheory.CechPic.pull (Hecke.sq2 θ) x) = x := by
    intro x
    rw [← GlobalTheory.CechPic.pull_comp, square_map_comp, IsIso.inv_hom_id, square_map_id, GlobalTheory.CechPic.pull_id]
  rw [← key (c • _), ← key (GlobalTheory.CechPic.pull (Hecke.sq2 χ) _), map_nsmul, ← h₁, one_smul, h₂,
    ← square_map_comp, GlobalTheory.CechPic.pull_comp]

theorem UpperTheory.Gal.G3.pTransCancel :
    MultBasic → RelComp → TateDiff → TateTwist → TransIso → TransCancel := by
  intro hMB hRC hTD hTT hTI p _ D G L R _ _ gb S s M N' N o o₁ o₂ θ χ h hint hadm hθ hθχ
  have hθiso : IsIso θ := hTI p D G L R gb S s M N' o o₁ θ 1 (one_mem _) hθ
  obtain ⟨hθm, hθa, ⟨θ', d₁, hθ'm, hθ'a, hθθ', hθ'θ, hd₁⟩, ⟨c₁, hc₁, ⟨hPθ⟩, t₁, t₁', ht₁, ht₁', htt₁, hc₁e⟩, hθpt⟩ := hθ
  obtain ⟨hχm₀, hχa₀, ⟨ω, d, hωm, hωa, hχω, hωχ, hd⟩, ⟨c, hc, ⟨hPχ⟩, t, t', ht, ht', htt, hce⟩, hχpt⟩ := hθχ
  have hinvm : IsMonHom (inv θ) := by
    constructor
    · rw [← cancel_mono θ]
      simp
    · rw [← cancel_mono θ]
      simp [IsMonHom.mul_hom]
  have hχm : IsMonHom χ := by
    have e : χ = inv θ ≫ (θ ≫ χ) := by simp
    rw [e]
    infer_instance
  have hc1 : c₁ = 1 :=
    (hMB p).1 _ c₁ 1 hc₁ (Nat.coprime_one_left p) ⟨t₁, t₁', ht₁, ht₁', htt₁, hc₁e⟩
      ((hMB p).2.2 D G L 1 (one_mem _))
  subst hc1
  refine ⟨hχm, ?_, ⟨ω ≫ θ, d, inferInstance, ?_, ?_, ?_, hd⟩,
    ⟨c, hc, ⟨bundle_cancel θ χ o.P o₁.P o₂.P o.isLB o₁.isLB o₂.isLB c hPθ hPχ⟩, t, t', ht, ht', htt, hce⟩, ?_⟩
  · intro e
    rw [← cancel_epi θ, ← Category.assoc, ← hθa e, Category.assoc, hχa₀ e, Category.assoc]
  · intro e
    rw [← Category.assoc, hωa e, Category.assoc, hθa e, Category.assoc]
  · rw [← cancel_epi θ]
    simp only [← Category.assoc]
    rw [hχω, MonObj.pow_comp, MonObj.comp_pow]
    simp
  · rw [Category.assoc]
    exact hωχ
  · intro k _ _ tt β htβ
    obtain ⟨I, I₁, hI, hI₁, hr₁⟩ := hθpt k tt β htβ
    obtain ⟨J, J₂, hJ, hJ₂, hr₂⟩ := hχpt k tt β htβ
    obtain ⟨u, hu, hIJ⟩ := hTD p D G L R gb S s M o k tt I J hI hJ
    obtain ⟨J', hJ', hJJ'⟩ := hTT p D G L R gb S s N o₂ k tt J₂ hJ₂ (h * u⁻¹ * h⁻¹) (hadm _ (inv_mem hu))
    have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
    have hu'1 : h * u⁻¹ * h⁻¹ ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) (hadm _ (inv_mem hu))
    have r0 : UpperTheory.Gal.G3.Rel L I₁ I (inv θ) 1 := by
      intro n hn hnp x y
      have e : I₁.ev n x ≫ inv θ = I.ev n y ↔ I.ev n y ≫ θ = I₁.ev n x := by
        constructor
        · intro e
          rw [← e]
          simp
        · intro e
          rw [← e]
          simp
      rw [e, hr₁ n hn hnp y x]
      simp only [map_one, Module.End.one_apply]
      constructor
      · rintro ⟨v, hv, e⟩
        exact ⟨-v, neg_mem hv, by rw [e]; simp⟩
      · rintro ⟨v, hv, e⟩
        exact ⟨-v, neg_mem hv, by rw [e]; simp⟩
    have r1 := (hRC p D G L R gb S s N' M M o₁ o o k tt I₁ I J (inv θ) (𝟙 o.A) 1 u inferInstance
      inferInstance (UpperTheory.Gal.Int.Geo.integ_of_mem hu1)).2 r0 hIJ
    have r2 := (hRC p D G L R gb S s N' M N o₁ o o₂ k tt I₁ J J₂ (inv θ ≫ 𝟙 o.A) (θ ≫ χ) (u * 1) h
      inferInstance inferInstance hint).2 r1 hr₂
    have r3 := (hRC p D G L R gb S s N' N N o₁ o₂ o₂ k tt I₁ J₂ J' ((inv θ ≫ 𝟙 o.A) ≫ (θ ≫ χ))
      (𝟙 o₂.A) (h * (u * 1)) (h * u⁻¹ * h⁻¹) inferInstance inferInstance
      (UpperTheory.Gal.Int.Geo.integ_of_mem hu'1)).2 r2 hJJ'
    have e1 : ((inv θ ≫ 𝟙 o.A) ≫ (θ ≫ χ)) ≫ 𝟙 o₂.A = χ := by simp
    have e2 : h * u⁻¹ * h⁻¹ * (h * (u * 1)) = h := by group
    rw [e1, e2] at r3
    exact ⟨I₁, J', hI₁, hJ', r3⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransUniqPt :
    MultBasic → IsogFEt → TransKer → QuotUniq → PolUniq → MapOfIso → TransUniqPt := by
  intro hMB hFE hTK hQU hPU hMI p _ D G L R _ _ gb k _ _ s N' N o o₁ o₂ ψ₁ ψ₂ h hint hadm tr₁ tr₂
  have hK := hTK p D G L R gb (Sp k) s N' N o o₁ o₂ ψ₁ ψ₂ h hint hadm tr₁ tr₂
  obtain ⟨mon₁, -, ⟨ψ₁', d₁, mon₁', -, e₁, e₁', cop₁⟩, ⟨c₁, hc₁, ⟨lb₁⟩, t₁, t₁', i₁, i₁', tt₁, hm₁⟩, -⟩ := id tr₁
  obtain ⟨mon₂, -, ⟨ψ₂', d₂, mon₂', -, e₂, e₂', cop₂⟩, ⟨c₂, hc₂, ⟨lb₂⟩, t₂, t₂', i₂, i₂', tt₂, hm₂⟩, -⟩ := id tr₂
  have dpos : ∀ d : ℕ, d.Coprime p → 0 < d := fun d hd => Nat.pos_of_ne_zero fun h0 => by
    subst h0
    exact (Fact.out : p.Prime).one_lt.ne' (by simpa using hd)
  obtain ⟨f₁, et₁, sj₁⟩ := hFE R (Sp k) s o.A o₁.A o.ab o₁.ab ψ₁ ψ₁' d₁ (dpos _ cop₁) mon₁ mon₁' e₁ e₁'
  obtain ⟨f₂, et₂, sj₂⟩ := hFE R (Sp k) s o.A o₂.A o.ab o₂.ab ψ₂ ψ₂' d₂ (dpos _ cop₂) mon₂ mon₂' e₂ e₂'
  obtain ⟨θ, isoθ, monθ, hθ⟩ := hQU k o.A o₁.A o₂.A o.ab o₁.ab o₂.ab ψ₁ ψ₂ mon₁ mon₂ f₁ et₁ sj₁ f₂ et₂ sj₂
    (fun Ω _ _ t a => (hK Ω t).1 a)
  have lin₁ := tr₁.2.1
  have lin₂ := tr₂.2.1
  haveI := f₁
  haveI := et₁
  haveI := sj₁
  haveI : Epi ψ₁.left := Flat.epi_of_flat_of_surjective _
  have cancel : ∀ {X : Over (Sp k)} (a b : o₁.A ⟶ X), ψ₁ ≫ a = ψ₁ ≫ b → a = b := fun a b e =>
    Over.OverMorphism.ext ((cancel_epi ψ₁.left).1 (by simpa using congrArg (·.left) e))
  have lin : ∀ c, o₁.act.act c ≫ θ = θ ≫ o₂.act.act c := fun c => cancel _ _ (by
    rw [← Category.assoc, ← lin₁ c, Category.assoc, hθ, lin₂ c, ← hθ, Category.assoc])
  have hcc : c₁ = c₂ := (hMB p).1 (mul h) c₁ c₂ hc₁ hc₂ ⟨t₁, t₁', i₁, i₁', tt₁, hm₁⟩ ⟨t₂, t₂', i₂, i₂', tt₂, hm₂⟩
  subst hcc
  have hPo := o.isLB
  have hP1 := o₁.isLB
  have hP2 := o₂.isLB
  have hQ : (o₂.P.pull (Hecke.sq2 θ)).IsLB := pull_isLB hP2 _
  have sqc : Hecke.sq2 ψ₁ ≫ Hecke.sq2 θ = Hecke.sq2 ψ₂ := by
    rw [← hθ]
    simp only [Hecke.sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc]
  have key : LBIso (o₁.P.pull (Hecke.sq2 ψ₁)) ((o₂.P.pull (Hecke.sq2 θ)).pull (Hecke.sq2 ψ₁)) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP1 _) (pull_isLB hQ _)).1 ?_
    have a1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hPo _ _) (pull_isLB hP1 _)).2 lb₁
    have a2 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hPo _ _) (pull_isLB hP2 _)).2 lb₂
    rw [← a1, a2, GlobalTheory.CechPic.cls_pull hP2, GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hP2,
      ← GlobalTheory.CechPic.pull_comp, sqc]
  have r₁ : ∃ t : ((o₂.P.pull (Hecke.sq2 θ)).pull (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left).Gen, t.IsGen := by
    refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hQ _)).1 ?_
    have e : (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left ≫ Hecke.sq2 θ =
        θ.left ≫ (lift (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A)).left := by
      simp only [Hecke.sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
        Category.comp_id, one_comp, comp_one]
    rw [GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hP2, ← GlobalTheory.CechPic.pull_comp, e, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull hP2 _ (pull_isLB hP2 _), (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP2 _)).2 o₂.rig₁, map_zero]
  have r₂ : ∃ t : ((o₂.P.pull (Hecke.sq2 θ)).pull (lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)).left).Gen, t.IsGen := by
    refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hQ _)).1 ?_
    have e : (lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)).left ≫ Hecke.sq2 θ =
        θ.left ≫ (lift (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A)).left := by
      simp only [Hecke.sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
        Category.comp_id, one_comp, comp_one]
    rw [GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hP2, ← GlobalTheory.CechPic.pull_comp, e, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull hP2 _ (pull_isLB hP2 _), (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP2 _)).2 o₂.rig₂, map_zero]
  have pol : LBIso o₁.P (o₂.P.pull (Hecke.sq2 θ)) :=
    hPU (Sp k) o.A o₁.A o.ab o₁.ab ψ₁ mon₁ f₁ et₁ sj₁ o₁.P _ hP1 hQ o₁.rig₁ o₁.rig₂ r₁ r₂ key
  have lev : ∀ y, o₁.eta y ≫ θ = o₂.eta y := by
    intro y
    obtain ⟨v, hv⟩ := sj₁.surj (UpperTheory.Gal.TranscendenceTraces.pt (toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y).left)
    obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds ψ₁.left k (toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y).left v hv
    let a : Over.mk (𝟙 (Sp k)) ⟶ o.A := Over.homMk z (by
      have w1 := Over.w ψ₁
      have w2 := Over.w (toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y)
      simp only [Over.mk_hom] at w2 ⊢
      rw [← w1, ← Category.assoc, hz, w2])
    have ha : a ≫ ψ₁ = toUnit _ ≫ o₁.eta y := Over.OverMorphism.ext hz
    have hb := ((hK k (𝟙 _)).2 a y).1 ha
    have e : toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y ≫ θ = toUnit (Over.mk (𝟙 (Sp k))) ≫ o₂.eta y := by
      rw [← Category.assoc, ← ha, Category.assoc, hθ, hb]
    let i : 𝟙_ (Over (Sp k)) ⟶ Over.mk (𝟙 (Sp k)) := Over.mkIdTerminal.from _
    have hi : i ≫ toUnit (Over.mk (𝟙 (Sp k))) = 𝟙 _ := toUnit_unique _ _
    have e' := congrArg (i ≫ ·) e
    simpa [← Category.assoc, hi] using e'
  obtain ⟨m, hm⟩ := hMI D.toG R gb (Sp k) s N.1 o₁ o₂ θ isoθ monθ lin pol lev
  exact ⟨m, by rw [hm, ← hθ, Over.comp_left]⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

namespace UpperTheory.Gal.G3

private theorem conj_core {V : Type*} [AddCommGroup V] [Module ℚ V] (H U Hi : V →+ V) {k N : ℕ} (hk : 0 < k) {v w : V}
    (hv : H (Hi v) = v) (e : U (k • Hi v) = k • Hi v + (N * k) • w) : H (U (Hi v)) = v + N • H w := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have h1 := congrArg H e
  simp only [map_nsmul, map_add (f := _), hv] at h1
  have h2 : k • H (U (Hi v)) = k • (v + N • H w) := by
    rw [h1, smul_add, mul_comm N k, mul_smul]
  rw [← Nat.cast_smul_eq_nsmul ℚ k, ← Nat.cast_smul_eq_nsmul ℚ k] at h2
  exact MulAction.injective₀ hk' h2

private theorem congOne_conj {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {h u : G.GAf} {k N : ℕ}
    (hI : Integ L h) (hk : 0 < k) (hinv : ∀ v ∈ LaHat D, k • L.actG h⁻¹ v ∈ LaHat D) (hu : L.CongOne (N * k) u) :
    L.CongOne N (h * u * h⁻¹) := by
  intro v hv
  obtain ⟨w, hw, e⟩ := hu _ (hinv v hv)
  refine ⟨L.actG h w, hI w hw, ?_⟩
  have hhv : L.actG h (L.actG h⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have := conj_core (L.actG h).toAddMonoidHom (L.actG u).toAddMonoidHom (L.actG h⁻¹).toAddMonoidHom hk (v := v) (w := w) hhv e
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  exact this

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.pAdmOf :
    AdmOf := by
  intro p _ D G L h k N hI hk hinv u hu
  refine ⟨congOne_conj L hI hk hinv hu.1, ?_⟩
  have e : (h * u * h⁻¹)⁻¹ = h * u⁻¹ * h⁻¹ := by group
  rw [e]
  exact congOne_conj L hI hk hinv hu.2
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pMapOfIso :
    MapOfIso := by
  intro G₀ R _ _ gb S s N o o' θ hiso hmon hact hpol heta
  haveI : IsIso θ.left := (Over.forget S).map_isIso θ
  refine ⟨⟨θ.left, Hecke.sq2 θ, ⟨IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩, ?_⟩, ⟨?_, ?_⟩,
    fun c => ?_, hpol, fun y => ?_⟩, rfl⟩
  · intro T x y x₀ y₀ hx hy
    let u : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
    have ex : x₀ = u ≫ x ≫ θ := Over.OverMorphism.ext (by simp [u, hx])
    have ey : y₀ = u ≫ y ≫ θ := Over.OverMorphism.ext (by simp [u, hy])
    rw [ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]
    simp [u]
  · rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  · rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]
  · rw [← Over.comp_left, hact c, Over.comp_left]
  · rw [← Over.comp_left, heta y, Category.id_comp]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransFree :
    KNCong → TransFree := by
  intro hK p _ D G L R _ _ gb k _ _ s N o u hu hT
  obtain ⟨-, -, -, -, hp⟩ := hT
  obtain ⟨I', I'', h', h'', hr⟩ := hp k (𝟙 _) (Spec.preimage (𝟙 _ ≫ s)).hom (by
    simp [spMap])
  refine hK p D G L N.1 (by have := N.2.1; omega) N.2.2 u hu fun x => ?_
  exact (hr N.1 (by have := N.2.1; omega) N.2.2 x x).1 (by
    rw [← h' x, ← h'' x]; simp)
end
