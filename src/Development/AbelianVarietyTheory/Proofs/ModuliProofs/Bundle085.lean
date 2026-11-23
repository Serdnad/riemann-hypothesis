module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle049
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELPeriod

theorem adjoint_baseChange {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : B' ⟶ B} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (h : IsGrpPullback G' G f φ) (hb : LBIso L' (L.pull φ)) {w wd : G ⟶ G} {w' wd' : G' ⟶ G'}
    (hw : w'.left ≫ φ = φ ≫ w.left) (hwd : wd'.left ≫ φ = φ ≫ wd.left)
    (ha : LBIso (cubeLB G ![fst G G ≫ w, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ wd] L)) :
    LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ wd'] L') := by
  have pa : ∀ {T : Over B'} (x : T ⟶ G'), pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
  have pd : ∀ {T : Over B'} (x : T ⟶ G'), pushPt h.1.w (x ≫ wd') = pushPt h.1.w x ≫ wd := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hwd, Category.assoc])
  have hB : (L.pull φ).IsLB := DVR.linComb_isLB L hL _ _
  have h₁ : LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] (L.pull φ))
      (cubeLB G' ![fst G' G', snd G' G' ≫ wd'] (L.pull φ)) := by
    let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
    refine LBIso.chartPull (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) ha
    · fin_cases i
      · exact (pa _).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pd _).trans (by simp [U])
  exact LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _)
    (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
    (LBIso.trans (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _) h₁
      (GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _))

def tateIsoMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {k : Type} [Field k]
    {Q Q' : Type} [Group Q] [Group Q'] {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop}
    {e' : ℕ → Q' → Q' → kˣ → Prop} (I : TateIso D k Q act e) (ψ : Q ≃* Q')
    (ha : ∀ c y, ψ (act c y) = act' c (ψ y)) (he : ∀ n y y' c, e n y y' c → e' n (ψ y) (ψ y') c) :
    TateIso D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n x := ψ (I.ev n x)
  add n x y := by rw [I.add, map_mul]
  lin n c x := by rw [I.lin, ha]
  ker n hn x := by rw [← I.ker n hn, map_eq_one_iff ψ ψ.injective]
  onto n hn x := by
    obtain ⟨x, rfl⟩ := ψ.surjective x
    rw [← map_pow, map_eq_one_iff ψ ψ.injective, I.onto n hn]
    simp only [ψ.injective.eq_iff]
  tower n m hn hm x := by rw [← map_pow, I.tower n m hn hm]
  isom n hn x y := he _ _ _ _ (I.isom n hn x y)

theorem exists_act {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {o : Type}
    [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {em : o →+* ℂ} {a : J → 𝓞 E}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {ρ : o} {t : TObj g k J b (spMap em)} (h : PELClass D a bas ρ em t) :
    ∃ act : OAct (𝓞 E) t.pol.A, (∀ j, act.act (a j) = t.act j) ∧ DetCond D act (𝟙 (Sp ℂ)) (em ρ) ∧
      (∀ c, LBIso (cubeLB t.pol.A ![fst t.pol.A t.pol.A ≫ act.act c, snd t.pol.A t.pol.A] t.pol.L)
        (cubeLB t.pol.A ![fst t.pol.A t.pol.A, snd t.pol.A t.pol.A ≫ act.act (H.bar c)] t.pol.L)) ∧
      ∃ I : TateIso D ℂ (Over.mk (𝟙 (Sp ℂ)) ⟶ t.pol.A) (fun c y => y ≫ act.act c)
          (fun n y y' c => Out.WeilIs t.pol.A t.pol.L n y y' (unitOn c)),
        (I.ζ k : ℂ) = em b.ζ ∧ ∀ i, (I.ev k (bas (Pi.single i 1))).left = (t.pt i).left := by
  obtain ⟨τ, φ, hφ, hL, hj, hd⟩ := h
  haveI := hφ
  haveI := t.ab.comm
  have hi : IsGrpPullback t.A τ.G (𝟙 _) φ.inv.left := GlobalTheory.FibreAct.isGrpPullback_of_iso φ.inv
  have e₁ : φ.inv.left ≫ φ.hom.left = 𝟙 _ := by rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]
  have hL' : LBIso t.L (τ.PP.L.pull φ.inv.left) :=
    LBIso.chartPull (chartPullSec t.L _ _ e₁) (chartPullPull τ.PP.L _ _ rfl) hL.symm
  obtain ⟨act, hact⟩ := GlobalTheory.FibreAct.exists_lift_act hi τ.act
  have hact' : ∀ c, act.act c ≫ φ.inv = φ.inv ≫ τ.act.act c := fun c => Over.OverMorphism.ext (hact c)
  have hact'' : ∀ c, τ.act.act c ≫ φ.hom = φ.hom ≫ act.act c := fun c => by
    rw [← Iso.inv_comp_eq, ← Category.assoc, ← hact', Category.assoc, φ.inv_hom_id, Category.comp_id]
  obtain ⟨hdet, I, hζ, hpt⟩ := hd ℂ (𝟙 _) em (Category.id_comp _)
  refine ⟨act, fun j => ?_, fun σ => ?_, fun c => ?_, ?_⟩
  · exact (cancel_epi φ.hom).1 ((hact'' _).symm.trans (hj j))
  · have L : ∀ n, LieMult act (𝟙 _) σ n ↔ LieMult τ.act (𝟙 _) σ n := fun n => by
      rw [GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ hi hact ℂ _ σ n, Category.comp_id]
    exact ⟨fun hs => (L _).2 ((hdet σ).1 hs), fun hs => (L _).2 ((hdet σ).2 hs)⟩
  · exact adjoint_baseChange τ.PP.isLB t.isLB hi hL' (hact c) (hact _) (τ.adj c)
  · let ψ : (Over.mk (𝟙 (Sp ℂ)) ⟶ τ.G) ≃* (Over.mk (𝟙 (Sp ℂ)) ⟶ t.A) :=
      { toFun := fun y => y ≫ φ.hom
        invFun := fun y => y ≫ φ.inv
        left_inv := fun y => by simp
        right_inv := fun y => by simp
        map_mul' := fun y y' => MonObj.mul_comp _ _ _ }
    have W : ∀ (s : Sp ℂ ⟶ Sp ℂ), 𝟙 (Sp ℂ) ≫ 𝟙 (Sp ℂ) = s → ∀ (n : ℤ) (x y : Over.mk (𝟙 (Sp ℂ)) ⟶ t.A)
        (x₀ y₀ : Over.mk s ⟶ τ.G) (c : Γ(Sp ℂ, ⊤)ˣ), x₀.left = x.left ≫ φ.inv.left →
        y₀.left = y.left ≫ φ.inv.left → Out.WeilIs τ.G τ.PP.L n x₀ y₀ c → Out.WeilIs t.A t.L n x y c := by
      rintro _ rfl n x y x₀ y₀ c hx hy
      exact (GlobalTheory.weilIs_grpPullback_of_comm _ _ τ.G t.A _ _ _ _ τ.PP.isLB t.isLB hi hL' (Over.mk (𝟙 _)) n x y
        x₀ y₀ c hx hy).2
    have hψ : ∀ y : Over.mk (𝟙 (Sp ℂ)) ⟶ τ.G, y.left = (ψ y).left ≫ φ.inv.left := fun y => by
      show y.left = ((y ≫ φ.hom) ≫ φ.inv).left
      simp
    refine ⟨tateIsoMap I ψ (fun c y => ?_) (fun n y y' c => W _ (Category.id_comp _) n _ _ y y' _ (hψ y) (hψ y')),
      hζ, fun i => ?_⟩
    · show (y ≫ τ.act.act c) ≫ φ.hom = (y ≫ φ.hom) ≫ act.act c
      rw [Category.assoc, hact'', Category.assoc]
    · exact (congrArg (fun z => z.left) (hpt i)).trans (Category.id_comp _)

end GlobalTheory.PELPeriod
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkSetPull

theorem range_of_isPullback {P X Y Z : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {c : X ⟶ Z} {d : Y ⟶ Z}
    (h : IsPullback a b c d) : Set.range a = c ⁻¹' Set.range d := by
  rw [← AlgebraicGeometry.Scheme.Pullback.range_fst c d]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨h.isoPullback.hom q, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩
  · rintro ⟨q, rfl⟩
    exact ⟨h.isoPullback.inv q, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]⟩

theorem exists_equiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G), ∀ x, (ρ x).left = x.left ≫ φ := by
  refine ⟨{ toFun := fun x => Over.homMk (x.left ≫ φ) (by rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]; rfl)
            invFun := fun y => Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _)
            left_inv := fun x => by
              apply Over.OverMorphism.ext
              apply h.1.hom_ext
              · exact h.1.lift_fst _ _ _
              · exact (h.1.lift_snd _ _ _).trans (Over.w x).symm
            right_inv := fun y => by
              apply Over.OverMorphism.ext
              exact h.1.lift_fst _ _ _
            map_mul' := fun x y => by
              apply Over.OverMorphism.ext
              exact (h.2 T x y _ _ rfl rfl).symm }, fun x => rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} {t : SAB H S}
  {t' : SAB H S'} {f : S' ⟶ S}

theorem heckeKer_iff (D : Datum H) (P : Ideal (𝓞 E)) (p i : ℕ) (m : SABMap t' t f) (T : Over S')
    (C' : Subgroup (T ⟶ t'.G)) (C : Subgroup (Over.mk (T.hom ≫ f) ⟶ t.G))
    (h : ∀ (u : T ⟶ t'.G) (v : Over.mk (T.hom ≫ f) ⟶ t.G), v.left = u.left ≫ m.φ → (u ∈ C' ↔ v ∈ C)) :
    t'.HeckeKer T D P p i C' ↔ t.HeckeKer (Over.mk (T.hom ≫ f)) D P p i C := by
  obtain ⟨ρ, hρ⟩ := exists_equiv m.cart T
  have hC : ∀ u, u ∈ C' ↔ ρ u ∈ C := fun u => h u (ρ u) (hρ u)
  have hact : ∀ u a, ρ (u ≫ t'.act.act a) = ρ u ≫ t.act.act a := by
    intro u a
    apply Over.OverMorphism.ext
    rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, Category.assoc]
    exact congrArg (u.left ≫ ·) (m.act a)
  have htors : ∀ I u, u ∈ t'.tors T I ↔ ρ u ∈ t.tors (Over.mk (T.hom ≫ f)) I := by
    intro I u
    simp only [SAB.tors, Set.mem_ofPred_eq]
    refine forall₂_congr fun a _ => ?_
    rw [← hact, map_eq_one_iff ρ ρ.injective]
  have hL : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hW : ∀ u v, Out.WeilIs t'.G t'.PP.L ((p : ℤ) ^ 2) u v 1 ↔ Out.WeilIs t.G t.PP.L ((p : ℤ) ^ 2) (ρ u) (ρ v) 1 :=
    fun u v => GlobalTheory.weilIs_iff_of_isGrpPullback_comm S S' t.G t'.G f m.φ t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart hL
      T _ u v (ρ u) (ρ v) 1 (hρ u) (hρ v)
  have cC : Nat.card C' = Nat.card C := Nat.card_congr (ρ.toEquiv.subtypeEquiv hC)
  have cT : ∀ I, Nat.card (t'.tors T I) = Nat.card (t.tors (Over.mk (T.hom ≫ f)) I) :=
    fun I => Nat.card_congr (ρ.toEquiv.subtypeEquiv (htors I))
  have cI : ∀ I, Nat.card ((C' : Set (T ⟶ t'.G)) ∩ t'.tors T I : Set (T ⟶ t'.G)) =
      Nat.card ((C : Set (Over.mk (T.hom ≫ f) ⟶ t.G)) ∩ t.tors (Over.mk (T.hom ≫ f)) I : Set (Over.mk (T.hom ≫ f) ⟶ t.G)) :=
    fun I => Nat.card_congr (ρ.toEquiv.subtypeEquiv fun u => (hC u).and (htors I u))
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx a
      obtain ⟨u, rfl⟩ := ρ.surjective x
      rw [← hact]
      exact (hC _).mp (h1 u ((hC u).mpr hx) a)
    · intro J hJ x hx
      obtain ⟨u, rfl⟩ := ρ.surjective x
      exact (hC u).mp (h2 J hJ ((htors J u).mpr hx))
    · intro x hx
      obtain ⟨u, rfl⟩ := ρ.surjective x
      exact (htors _ u).mp (h3 ((hC u).mpr hx))
    · intro x hx y hy
      obtain ⟨u, rfl⟩ := ρ.surjective x
      obtain ⟨v, rfl⟩ := ρ.surjective y
      exact (hW u v).mp (h4 u ((hC u).mpr hx) v ((hC v).mpr hy))
    · rw [← cC]
      exact h5
    · rw [← cT, ← cI]
      exact h6
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu a
      rw [hC, hact]
      exact h1 _ ((hC u).mp hu) a
    · intro J hJ u hu
      exact (hC u).mpr (h2 J hJ ((htors J u).mp hu))
    · intro u hu
      exact (htors _ u).mpr (h3 ((hC u).mp hu))
    · intro u hu v hv
      exact (hW u v).mpr (h4 _ ((hC u).mp hu) _ ((hC v).mp hv))
    · rw [cC]
      exact h5
    · rw [cT, cI]
      exact h6

theorem heckeSet_pull (D : Datum H) (P : Ideal (𝓞 E)) (p i : ℕ) (m : SABMap t' t f) (K : Set t.G.left)
    (hK : HeckeSet D t P p i K) : HeckeSet D t' P p i (m.φ ⁻¹' K) := by
  intro k _ _ x
  obtain ⟨C, hCK, hC⟩ := hK k (x ≫ f)
  obtain ⟨ρ, hρ⟩ := exists_equiv m.cart (Over.mk x)
  refine ⟨C.comap ρ.toMonoidHom, fun z => ?_, ?_⟩
  · show ρ z ∈ C ↔ _
    rw [hCK, hρ]
    simp only [Set.range_subset_iff, Set.mem_preimage, Scheme.Hom.comp_apply]
    exact Iff.rfl
  · refine (heckeKer_iff D P p i m (Over.mk x) _ C ?_).mpr hC
    intro u v huv
    obtain rfl : v = ρ u := Over.OverMorphism.ext (huv.trans (hρ u).symm)
    exact Iff.rfl

theorem etSet_pull {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom f)
    (K : Set G.left) (hK : EtSet G K) : EtSet G' (φ ⁻¹' K) := by
  obtain ⟨C, j, hfin, het, hcl, hCK⟩ := hK
  have w : (pullback.fst C.hom f ≫ j.left) ≫ G.hom = pullback.snd C.hom f ≫ f := by
    rw [Category.assoc, Over.w j, pullback.condition]
  let j' : Over.mk (pullback.snd C.hom f) ⟶ G' :=
    Over.homMk (h.lift (pullback.fst C.hom f ≫ j.left) (pullback.snd C.hom f) w) (h.lift_snd _ _ _)
  have sq : IsPullback (pullback.fst C.hom f) j'.left j.left φ := by
    refine IsPullback.of_bot (v₂₁ := G'.hom) (v₂₂ := G.hom) (h₃₁ := f) ?_ (h.lift_fst _ _ _).symm h
    have e : j'.left ≫ G'.hom = pullback.snd C.hom f := h.lift_snd _ _ _
    rw [e, Over.w j]
    exact IsPullback.of_hasPullback C.hom f
  refine ⟨Over.mk (pullback.snd C.hom f), j', ?_, ?_, ?_, ?_⟩
  · show IsFinite (pullback.snd C.hom f)
    infer_instance
  · show Etale (pullback.snd C.hom f)
    infer_instance
  · exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq hcl
  · rw [range_of_isPullback sq.flip, hCK]

theorem lists_pull {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (K : Set G.left) (N n : ℕ) (σ : Fin n → (𝟙_ (Over S) ⟶ G)) (hK : Lists N σ K) :
    ∃ σ' : Fin n → (𝟙_ (Over S') ⟶ G'), (∀ j, (σ' j).left ≫ φ = f ≫ (σ j).left) ∧ Lists N σ' (φ ⁻¹' K) := by
  obtain ⟨ρ, hρ⟩ := exists_equiv h (𝟙_ (Over S'))
  let σ' : Fin n → (𝟙_ (Over S') ⟶ G') := fun j => ρ.symm (toUnit _ ≫ σ j)
  have key : ∀ j, (σ' j).left ≫ φ = f ≫ (σ j).left := by
    intro j
    rw [← hρ, MulEquiv.apply_symm_apply, Over.comp_left, Over.toUnit_left]
    simp [Over.tensorUnit_hom]
  have sq : ∀ j, IsPullback (σ' j).left f φ (σ j).left := by
    intro j
    refine (IsPullback.of_bot (v₂₁ := G'.hom) (v₂₂ := G.hom) (h₃₁ := f) ?_ (key j).symm h.1).flip
    rw [Over.w (σ' j), Over.w (σ j)]
    simp only [Over.tensorUnit_hom]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  refine ⟨σ', key, ?_, ?_, ?_⟩
  · intro j
    apply ρ.injective
    rw [map_pow, MulEquiv.apply_symm_apply, ← MonObj.comp_pow, hK.1 j, MonObj.comp_one, map_one]
  · rw [hK.2.1, Set.preimage_iUnion]
    exact Set.iUnion_congr fun j => (range_of_isPullback (sq j)).symm
  · intro k _ _ x i j hij
    apply hK.2.2 k (x ≫ f)
    have e := congrArg (· ≫ φ) hij
    simp only [Category.assoc, key] at e
    simpa only [Category.assoc] using e

end GlobalTheory.HkSetPull

theorem GlobalTheory.heckeSets_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f), IsProper t.G.hom → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S') (C' : Subgroup (Over.mk x ⟶ t'.G)) (C : Subgroup (Over.mk (x ≫ f) ⟶ t.G)), (∀ (u : Over.mk x ⟶ t'.G) (v : Over.mk (x ≫ f) ⟶ t.G), v.left = u.left ≫ m.φ → (u ∈ C' ↔ v ∈ C)) → (t'.HeckeKer (Over.mk x) D 𝔓 p i C' ↔ t.HeckeKer (Over.mk (x ≫ f)) D 𝔓 p i C)) ∧ ∀ K : Set t.G.left, (HeckeSet D t 𝔓 p i K → HeckeSet D t' 𝔓 p i (m.φ ⁻¹' K)) ∧ (EtSet t.G K → EtSet t'.G (m.φ ⁻¹' K)) ∧ ∀ (N n : ℕ) (σ : Fin n → (𝟙_ (Over S) ⟶ t.G)), Lists N σ K → ∃ σ' : Fin n → (𝟙_ (Over S') ⟶ t'.G), (∀ j, (σ' j).left ≫ m.φ = f ≫ (σ j).left) ∧ Lists N σ' (m.φ ⁻¹' K) := by
  intro E _ _ _ H D 𝔓 p i S S' t t' f m _
  exact ⟨fun k _ _ x C' C h => GlobalTheory.HkSetPull.heckeKer_iff D 𝔓 p i m (Over.mk x) C' C h,
    fun K => ⟨fun hK => GlobalTheory.HkSetPull.heckeSet_pull D 𝔓 p i m K hK,
      fun hK => GlobalTheory.HkSetPull.etSet_pull m.cart.1 K hK,
      fun N n σ hK => GlobalTheory.HkSetPull.lists_pull m.cart K N n σ hK⟩⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.TUniq
open GlobalTheory.SegreCoord ReciprocityTheory.ChartRestriction.G.Out

theorem secCoord_of_ratio {X X' : Scheme.{0}} {M : LB X} {M' : LB X'} (hM' : M'.IsLB) {σ : Type} {th : σ → M.Sec}
    {th' : σ → M'.Sec} {B : Type} [Field B] {x : Sp B ⟶ X} {x' : Sp B ⟶ X'} (p : Sp B) {j : M.ι} {j' : M'.ι}
    (hj : x p ∈ M.U j) (hj' : x' p ∈ M'.U j') (c : ((Sp B).presheaf.stalk p)ˣ)
    (h : ∀ i, gs x' p _ ((th' i).f j') = c * gs x p _ ((th i).f j)) {v : σ → B} (H : SecCoord M th x v) :
    SecCoord M' th' x' v := by
  have hs : ∀ y : Sp B, y = p := fun y => Subsingleton.elim (α := PrimeSpectrum B) _ _
  obtain ⟨u, hu⟩ := loc_of_secCoord H p j hj
  by_cases hv : Ideal.span (Set.range v) = ⊤
  · refine secCoord_of_loc hv fun y l hl => ?_
    obtain rfl := hs y
    refine ⟨gm x' y _ (M'.g l j') * (c * u), fun i => ?_⟩
    rw [gs_sec (th' i) x' y hl hj', h, hu, Units.val_mul, Units.val_mul]
    ring
  · have h0 : ∀ i, v i = 0 := fun i => by
      by_contra hi
      exact hv (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (IsUnit.mk0 _ hi))
    obtain ⟨w, hw⟩ := exists_secCoord (th := th') hM' (x := x') (k := j') fun y => by rw [hs y]; exact hj'
    obtain ⟨u', hu'⟩ := loc_of_secCoord hw p j' hj'
    have : w = v := funext fun i => ev_ext fun y => by
      obtain rfl := hs y
      have := hu' i
      rw [h, hu, h0, map_zero, zero_mul, mul_zero] at this
      rw [h0, map_zero]
      exact (Units.mul_left_eq_zero _).1 this.symm
    exact this ▸ hw

variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {S S' : Scheme.{0}} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}

theorem secCoord_of_sv {A : Over S} [GrpObj A] {A' : Over S'} [GrpObj A'] {L : LB A.left} {L' : LB A'.left}
    (hL' : L'.IsLB) {a a' : ℤ} {T : Over S} {T' : Over S'} {σ : Type} {th : σ → LB.Sec (LPow A L a T)}
    {th' : σ → LB.Sec (LPow A' L' a' T')} {B : Type} [Field B] {x : Sp B ⟶ (T ⊗ A).left}
    {x' : Sp B ⟶ (T' ⊗ A').left} (p : Sp B) {I I'} (hI : Good L p I) (hI' : Good L' p I')
    (c : ((Sp B).presheaf.stalk p)ˣ)
    (h : ∀ i, VVRank.sv A' (th' i) x' p I' = c * VVRank.sv A (th i) x p I) {v : σ → B}
    (H : SecCoord _ th x v) : SecCoord _ th' x' v :=
  secCoord_of_ratio (LB.isLB_linComb hL' _ _) p (hI.mem (fun _ : Fin 1 => (snd T A).left) x)
    (hI'.mem (fun _ : Fin 1 => (snd T' A').left) x') c h H

theorem lab_pow (t : TObj g (N' ^ 2) J b s) (a : Ix g (N' ^ 2)) : t.lab a ^ (N' ^ 2) = 1 := by
  have := t.ab.comm
  have cm : ∀ x y : Out.baseOver S ⟶ t.A, Commute x y := fun x y => _root_.mul_comm x y
  refine List.prod_induction (fun y => y ^ (N' ^ 2) = 1) (fun x y hx hy => ?_) (one_pow _) fun y hy => ?_
  · rw [(cm x y).mul_pow, hx, hy, _root_.mul_one]
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hy
    rw [← pow_mul, Nat.mul_comm, pow_mul, t.torsion, one_pow]

theorem MapBy.lab {u : TObj g (N' ^ 2) J b s'} {t : TObj g (N' ^ 2) J b s} {f : S' ⟶ S} {φ : u.A.left ⟶ t.A.left}
    (h : MapBy u t f φ) (a : Ix g (N' ^ 2)) : f ≫ (t.lab a).left = (u.lab a).left ≫ φ := by
  have hτ : f ≫ (baseOver S).hom = (baseOver S').hom ≫ f := (Category.comp_id _).trans (Category.id_comp _).symm
  refine (ThetaPtMove.over_iff h.1 (T := baseOver S') (T₀ := baseOver S) f hτ _ _).2 ?_
  simp only [TObj.lab, linComb, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp_apply, map_pow]
  congr 1
  exact (ThetaPtMove.over_iff h.1 (T := baseOver S') (T₀ := baseOver S) f hτ _ _).1 (h.2.2.1 i).symm

theorem emb_move {u : TObj g (N' ^ 2) J b s'} {t : TObj g (N' ^ 2) J b s} {f : S' ⟶ S} {φ : u.A.left ⟶ t.A.left}
    (h : MapBy u t f φ) {m : ℕ} (hm : m ∣ N') {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) [IsIso τ]
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) {σ₀} (H : t.Emb m T₀ σ₀) : ∃ σ, u.Emb m T σ ∧
      ∀ (B : Type) [Field B] (y : Sp B ⟶ (T ⊗ u.A).left) (y₀ : Sp B ⟶ (T₀ ⊗ t.A).left),
        y₀ ≫ (fst T₀ t.A).left = y ≫ (fst T u.A).left ≫ τ → y₀ ≫ (snd T₀ t.A).left = y ≫ (snd T u.A).left ≫ φ →
        ∀ w, SecCoord _ σ y w ↔ SecCoord _ σ₀ y₀ w := by
  obtain ⟨w, hw⟩ := h.2.1
  have hp := h.1
  have hL₀ := t.isLB
  have hL₁ := u.isLB
  have := u.ab.comm
  obtain ⟨th₀, s₀, α₀, U₀, h₁, h₂, h₄, h₅, h₆⟩ := H
  obtain ⟨th, hth⟩ := ThetaPtMove.exists_secRel hp τ hτ hw hL₀ hL₁ th₀
  obtain ⟨s₁, hs⟩ := ThetaPtMove.exists_secRel hp τ hτ hw hL₀ hL₁ s₀
  choose σ hσ using fun i => ThetaPtMove.exists_secRel hp τ hτ hw hL₀ hL₁ (σ₀ i)
  obtain ⟨α, hα, vα⟩ := ThetaPtMove.exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (ThetaPtMove.psi_pow hp τ hτ m) α₀ h₂
  have hx : ∀ a, τ ≫ ((Over.homMk T₀.hom (by simp) : T₀ ⟶ Out.baseOver S) ≫ t.lab a).left =
      ((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S') ≫ u.lab a).left ≫ φ := fun a => by
    show τ ≫ T₀.hom ≫ _ = (T.hom ≫ _) ≫ φ
    rw [← Category.assoc, hτ, Category.assoc, h.lab, Category.assoc]
  have hk : ∀ a, (((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S') ≫ u.lab a) ^ ((N' / m) ^ 2)) ^ (m ^ 2) = 1 :=
    fun a => by
      rw [← pow_mul, ← mul_pow, Nat.div_mul_cancel hm, ← MonObj.comp_pow, lab_pow, MonObj.comp_one]
  choose U hU hU' using fun i =>
    ThetaPtMove.symLift_move hp τ hτ hw hL₀ hL₁ (ThetaPtMove.over_pow hp τ hτ (hx i) _) (hk i) (h₅ i)
  have hg : IsGenSec t.A t.L 1 (VVRank.pullS t.A 1 (𝟙 T₀) th₀) :=
    ThetaCoord.isGenSec_pullS hL₀ _ (𝟙 T₀) (Category.comp_id _) h₁
  refine ⟨σ, ⟨th, s₁, α, U, ThetaPtMove.isGenSec_move hp τ hτ hw hL₀ hL₁ τ (𝟙 T₀) (Category.comp_id _) hth hg, hα,
    ThetaPtMove.isTwistPull_move hp τ hτ hL₀ hL₁ (ThetaPtMove.psi_pow hp τ hτ m) hα vα hth hs h₄, hU,
    fun i => hU' i _ _ _ _ hs (hσ i) (h₆ i)⟩, fun B _ y y₀ e₁ e₂ v => ?_⟩
  obtain rfl : y₀ = y ≫ ThetaPtMove.psi hp τ hτ := ThetaPtMove.psi_ext
    (by rw [e₁, Category.assoc, ThetaPtMove.psi_fst']) (by rw [e₂, Category.assoc, ThetaPtMove.psi_snd'])
  let p : Sp B := (default : PrimeSpectrum B)
  obtain ⟨I, hI⟩ := ConstFam.exists_good' hL₀ p
  obtain ⟨I', hI'⟩ := ConstFam.exists_good' hL₁ p
  exact ⟨secCoord_of_sv hL₀ p hI' hI _ fun i => hσ i _ y p I I' hI hI',
    secCoord_of_sv hL₁ p hI hI' _ fun i => (Units.eq_inv_mul_iff_mul_eq _).2 (hσ i _ y p I I' hI hI').symm⟩

theorem emb_unique (hG : GlobalFnsSt) (t : TObj g (N' ^ 2) J b s) {m : ℕ} (hm : Odd m) {T : Over S}
    [Subsingleton T.left] {σ σ'} (H : t.Emb m T σ) (H' : t.Emb m T σ') {B : Type} [Field B]
    (y : Sp B ⟶ (T ⊗ t.A).left) {w} (h : SecCoord _ σ y w) : SecCoord _ σ' y w := by
  obtain ⟨th, s₁, α, U, h₁, h₂, h₄, h₅, h₆⟩ := H
  obtain ⟨th', s₁', α', U', h₁', h₂', h₄', h₅', h₆'⟩ := H'
  have hL := t.isLB
  obtain ⟨c, hc⟩ := ThetaCoord.exists_unit_of_isGenSec h₁' h₁
  let p : Sp B := (default : PrimeSpectrum B)
  obtain ⟨I, hI⟩ := ConstFam.exists_good' hL p
  refine secCoord_of_sv hL p hI hI
    (val α' y p I * (val α y p I)⁻¹ * gm (y ≫ (fst T t.A).left) p ⊤ c) (fun a => ?_) h
  have e₀ : (U' a).pt = (U a).pt := (h₅' a).pt_eq.trans (h₅ a).pt_eq.symm
  have e₁ := val_corr hI (SymLiftOdd.symLift_unique hG t.ab hL hm.pow _ _ (h₅' a) (h₅ a)) y
  have f₁ : (y ≫ (translT t.A (U a).pt).left) ≫ (fst T t.A).left = y ≫ (fst T t.A).left := by
    rw [Category.assoc, ← Over.comp_left, translT, lift_fst]
  have f₂ : ((y ≫ (translT t.A (U a).pt).left) ≫ (mulT t.A T m).left) ≫ (fst T t.A).left = y ≫ (fst T t.A).left := by
    rw [Category.assoc, ← Over.comp_left, mulT, lift_fst, f₁]
  have e₂ := CommPairing.val_div_eq hL (fst T t.A).left (CommPairing.surj_fst hG t.ab T) h₂' h₂ _ _ f₁ p I hI
  have e₃ := ThetaAct.sv_smul (c : Γ(T.left, ⊤)) (SecM.ofSec t.A th)
    ((y ≫ (translT t.A (U a).pt).left) ≫ (mulT t.A T m).left) p hI
  rw [← hc, f₂, gs_unit _ _ ⊤ trivial] at e₃
  rw [VVRank.sv_of_isTwistPull t.A (h₆ a) y p hI, VVRank.sv_of_isTwistPull t.A (h₆' a) y p hI,
    VVRank.sv_of_isTwistPull t.A h₄ _ p hI, VVRank.sv_of_isTwistPull t.A h₄' _ p hI, ← e₂]
  erw [e₁]
  rw [e₀]
  rw [show VVRank.sv t.A th' _ p I = _ * VVRank.sv t.A th _ p I from e₃]
  simp only [Units.val_mul]
  have key : ∀ {Q : Type} [CommRing Q] (a a' : Qˣ) (x y z : Q), x * (a' * (y * z)) = a' * ↑a⁻¹ * y * (x * (a * z)) :=
    fun a a' x y z => by linear_combination (-(x * a' * y * z)) * a.inv_mul
  exact key _ _ _ _ _

end GlobalTheory.TUniq
end
end
