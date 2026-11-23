module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle021
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
noncomputable section

namespace GlobalTheory.Poinc.Eq8

theorem exists_matEnd {S : Scheme.{0}} {B C : Over S} [GrpObj B] [GrpObj C] (pr : Fin 8 → (B ⟶ C))
    (hpr : ∀ a, IsMonHom (pr a))
    (hu : ∀ (T' : Over S) (y : Fin 8 → (T' ⟶ C)), ∃! z : T' ⟶ B, ∀ a, z ≫ pr a = y a) (a b : Fin 8) :
    ∃ f : B ⟶ B, MatEnd pr a b f := by
  obtain ⟨f, hf, -⟩ := hu B (fun w => if w = a then pr b else 1)
  have ext : ∀ {T : Over S} (z z' : T ⟶ B), (∀ w, z ≫ pr w = z' ≫ pr w) → z = z' := by
    intro T z z' h
    obtain ⟨_, -, hz⟩ := hu T (fun w => z' ≫ pr w)
    exact (hz z h).trans (hz z' fun _ => rfl).symm
  have mul : ∀ (T : Over S) (x y : T ⟶ B), (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
    intro T x y
    refine ext _ _ fun w => ?_
    have hw := hpr w
    have e : ((x ≫ f) * (y ≫ f)) ≫ pr w = (x ≫ f ≫ pr w) * (y ≫ f ≫ pr w) := by
      rw [MonObj.mul_comp, Category.assoc, Category.assoc]
    rw [e, Category.assoc, hf]
    split_ifs
    · have := hpr b
      rw [MonObj.mul_comp]
    · simp
  refine ⟨f, ⟨?_, ?_⟩, hf⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over S) ⟶ B) ≫ f = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul (B ⊗ B) (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

theorem matOn_exists : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ (C : Over (Sp S.R)) [GrpObj C] [IsCommMonObj C] (pr : Fin 8 → (ρ.P.A ⟶ C)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp S.R)) (y : Fin 8 → (T' ⟶ C)), ∃! z : T' ⟶ ρ.P.A, ∀ a, z ≫ pr a = y a) → ∀ a b, ∃ f, MatOn FinalForm pr a b f := by
  intro o' Ω _ _ _ _ S ρ M U₀ EE FinalForm hU C _ _ pr hpr hu a b
  obtain ⟨f₁, hf₁⟩ := exists_matEnd pr hpr hu a b
  have : IsMonHom f₁ := hf₁.1

  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := w) trivial
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hr
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  let Q := (Over.pullback FinalForm.u₀).obj ρ.P.A
  let ν : pullback FinalForm.G.hom M.pt ⟶ pullback ρ.P.A.hom FinalForm.u₀ :=
    FinalForm.cart.1.lift (pullback.fst FinalForm.G.hom M.pt) (pullback.snd FinalForm.G.hom M.pt ≫ x)
             (by rw [pullback.condition, Category.assoc, hx])
  have hν₁ : ν ≫ FinalForm.φ = pullback.fst FinalForm.G.hom M.pt := FinalForm.cart.1.lift_fst _ _ _
  have hν₂ : ν ≫ Q.hom = pullback.snd FinalForm.G.hom M.pt ≫ x := FinalForm.cart.1.lift_snd _ _ _
  have gη : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) FinalForm.G (x ≫ U₀.ι) (ν ≫ FinalForm.φ) :=
    (isGrpPullback_pullback FinalForm.G M.pt).congr hx.symm hν₁.symm
  have gν : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) Q x ν := FinalForm.cart.cancel gη hν₂
  have gψ := gν.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)
  obtain ⟨w', hw', pa⟩ := GlobalTheory.SymBaseChange.exists_endo gψ f₁
  have hw'l : w'.left ≫ ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) ≫ f₁.left := by
    have := congrArg (fun z => z.left) (pa (𝟙 _))
    simpa [pushPt] using this
  obtain ⟨F, ⟨hF, hFw⟩, -⟩ := FinalForm.endo w' hw'
  refine ⟨F, hF, f₁, hf₁, ?_⟩
  have hsep : IsSeparated FinalForm.G.hom := FinalForm.semi.separated
  have hsm : Smooth FinalForm.G.hom := FinalForm.semi.smooth
  have hQf : Flat Q.hom := MorphismProperty.of_isPullback (P := @Flat) FinalForm.cart.1 inferInstance
  have hqc : QuasiCompact M.pt := by
    have : IsSeparated M.s := M.sep
    have : QuasiCompact (M.pt ≫ M.s) := by rw [M.pt_s]; infer_instance
    exact QuasiCompact.of_comp M.pt M.s
  have hdom : IsSchemeTheoreticallyDominant M.pt := .of_isDominant M.pt
  let p : pullback ρ.P.A.hom FinalForm.u₀ ⟶ M.Z := Q.hom ≫ U₀.ι
  let j := pullback.fst p M.pt
  have hj : j ≫ Q.hom = pullback.snd p M.pt ≫ x := by
    rw [← cancel_mono U₀.ι, Category.assoc, Category.assoc, hx]
    exact pullback.condition
  let k : pullback p M.pt ⟶ pullback FinalForm.G.hom M.pt := pullback.lift (j ≫ FinalForm.φ) (pullback.snd p M.pt) (by
    rw [Category.assoc, FinalForm.cart.1.w]; exact pullback.condition)
  have hk₁ : k ≫ pullback.fst FinalForm.G.hom M.pt = j ≫ FinalForm.φ := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd FinalForm.G.hom M.pt = pullback.snd p M.pt := pullback.lift_snd _ _ _
  have hkν : k ≫ ν = j := by
    apply FinalForm.cart.1.hom_ext
    · rw [Category.assoc, hν₁, hk₁]
    · rw [Category.assoc, hν₂, ← Category.assoc, hk₂, hj]
  have hF' : ((Over.pullback M.pt).map F).left ≫ pullback.fst FinalForm.G.hom M.pt = pullback.fst FinalForm.G.hom M.pt ≫ F.left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  have hw₂ : w'.left ≫ pullback.snd FinalForm.G.hom M.pt = pullback.snd FinalForm.G.hom M.pt := Over.w w'
  have key : k ≫ w'.left ≫ ν = j ≫ ((Over.pullback FinalForm.u₀).map f₁).left := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hw'l]
      simp only [← Category.assoc]
      rw [hkν]
      simp only [Category.assoc, Over.pullback_map_left]
      exact congrArg (j ≫ ·) (pullback.lift_fst _ _ _).symm
    · have e : ((Over.pullback FinalForm.u₀).map f₁).left ≫ Q.hom = Q.hom := Over.w ((Over.pullback FinalForm.u₀).map f₁)
      show (k ≫ w'.left ≫ ν) ≫ Q.hom = (j ≫ ((Over.pullback FinalForm.u₀).map f₁).left) ≫ Q.hom
      simp only [Category.assoc]
      rw [hν₂, e, hj, ← Category.assoc w'.left, hw₂, ← Category.assoc, hk₂]
  refine GlobalTheory.SS.GenProj.ext_of_dense j FinalForm.G.hom ?_ ?_
  · have e1 : j ≫ FinalForm.φ ≫ F.left = k ≫ w'.left ≫ ν ≫ FinalForm.φ := by
      rw [hν₁, ← hFw, hF', ← Category.assoc k, hk₁, Category.assoc]
    rw [e1]
    simp only [← Category.assoc] at key ⊢
    rw [key]
  · rw [Category.assoc, Category.assoc, Over.w F, FinalForm.cart.1.w, ← Category.assoc, Over.w]

end GlobalTheory.Poinc.Eq8
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.TwoFac
variable {R : Type} [CommRing R] [IsDomain R] {D₁ D₂ D' : DegPre R}

theorem inc_pr_inc (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (he : F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e) :
    F₂.inc ≫ F₁.pr ≫ F₁.inc = F₂.inc := by
  rw [F₁.pr_inc, he, ← F₂.pr_inc, ← Category.assoc, F₂.inc_pr, Category.id_comp]

theorem comp_inv (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (he : F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e) :
    (F₂.inc ≫ F₁.pr) ≫ (F₁.inc ≫ F₂.pr) = 𝟙 _ := by
  simp only [Category.assoc]
  rw [← Category.assoc F₁.pr, ← Category.assoc F₂.inc, inc_pr_inc F₁ F₂ he, F₂.inc_pr]

theorem inv_comp (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (he : F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e) :
    (F₁.inc ≫ F₂.pr) ≫ (F₂.inc ≫ F₁.pr) = 𝟙 _ := by
  simp only [Category.assoc]
  rw [← Category.assoc F₂.pr, F₂.pr_inc, ← he, ← F₁.pr_inc, Category.assoc F₁.pr, ← Category.assoc F₁.inc, F₁.inc_pr,
    Category.id_comp]

theorem xi_xp_xi (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (hXe : ∀ z : D'.X, F₁.e • z = F₂.e • z) (a : D₂.X) :
    F₁.xi (F₁.xp (F₂.xi a)) = F₂.xi a := by
  rw [F₁.xi_xp, hXe, ← F₂.xi_xp, F₂.xp_xi]

theorem c_comp (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (hXe : ∀ z : D'.X, F₁.e • z = F₂.e • z) (a : D₂.X) :
    D₂.c a ≫ F₂.inc ≫ F₁.pr = D₁.c (F₁.xp (F₂.xi a)) := by
  have h := F₁.c_xi (F₁.xp (F₂.xi a))
  rw [xi_xp_xi F₁ F₂ hXe] at h
  rw [← Category.assoc, ← F₂.c_xi, h, Category.assoc, F₁.inc_pr, Category.comp_id]

def xEquiv (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (hXe : ∀ z : D'.X, F₁.e • z = F₂.e • z) : D₂.X ≃+ D₁.X where
  toFun a := F₁.xp (F₂.xi a)
  invFun a := F₂.xp (F₁.xi a)
  left_inv a := by
    show F₂.xp (F₁.xi (F₁.xp (F₂.xi a))) = a
    rw [xi_xp_xi F₁ F₂ hXe, F₂.xp_xi]
  right_inv a := by
    show F₁.xp (F₂.xi (F₂.xp (F₁.xi a))) = a
    rw [F₂.xi_xp, ← hXe, ← F₁.xi_xp, F₁.xp_xi, F₁.xp_xi]
  map_add' a b := by simp

theorem lift_comp (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (he : F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e)
    (hf : F₁.o.onB.act F₁.f = F₂.o.onB.act F₂.f) :
    (lift (fst D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₁.pr) (snd D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₁.pr) : G2 D₂.P.A ⟶ G2 D₁.P.A).left ≫
      (lift (fst D₁.P.A D₁.P.A ≫ F₁.inc) (snd D₁.P.A D₁.P.A ≫ F₁.inc ≫ F₁.o.onB.act F₁.f) : G2 D₁.P.A ⟶ G2 D'.P.A).left =
    (lift (fst D₂.P.A D₂.P.A ≫ F₂.inc) (snd D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₂.o.onB.act F₂.f) : G2 D₂.P.A ⟶ G2 D'.P.A).left := by
  rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]
  simp only [Category.assoc]
  rw [reassoc_of% (inc_pr_inc F₁ F₂ he), inc_pr_inc F₁ F₂ he, hf]

theorem formEq_cancel {X Y Y' : Scheme.{0}} {K : Type} [Fintype K] (ε : K → ℤ) (A B : K → (Y ⟶ X)) (A₁ B₁ : K → (Y' ⟶ X))
    (h : Y ⟶ Y') (hA : ∀ k, h ≫ A₁ k = A k) :
    FormEq (Sum.elim (Sum.elim A B) (fun k => h ≫ Sum.elim A₁ B₁ k))
      (Sum.elim (Sum.elim ε (fun k => - ε k)) (fun k => - Sum.elim ε (fun k => - ε k) k))
      (Sum.elim (fun k => h ≫ B₁ k) B) (Sum.elim ε (fun k => - ε k)) := by
  intro U _ g
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hA, neg_neg, zpow_neg, Finset.prod_inv_distrib]
  generalize ∏ a₁, g (A a₁) ^ ε a₁ = a
  generalize ∏ x, g (B x) ^ ε x = b
  generalize ∏ x, g (h ≫ B₁ x) ^ ε x = c
  rw [mul_inv, inv_inv, _root_.mul_comm a, _root_.mul_assoc, mul_inv_cancel_left, _root_.mul_comm]

theorem samePol_of_two_factors : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ D' : DegPre R), D₁.TauBimult → ∀ (F₁ : Factor D₁ D') (F₂ : Factor D₂ D'), F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e → F₁.o.onB.act F₁.f = F₂.o.onB.act F₂.f → (∀ z : D'.X, F₁.e • z = F₂.e • z) → (∀ z : D'.X, F₁.f • z = F₂.f • z) → SamePol D₁ D₂ := by
  intro R _ _ D₁ D₂ D' hB F₁ F₂ he hf hXe hXf
  haveI := F₂.inc_hom
  haveI := F₁.pr_hom
  let eI : D₂.P.A ≅ D₁.P.A := ⟨F₂.inc ≫ F₁.pr, F₁.inc ≫ F₂.pr, comp_inv F₁ F₂ he, inv_comp F₁ F₂ he⟩
  haveI : IsMonHom eI.hom := inferInstanceAs (IsMonHom (F₂.inc ≫ F₁.pr))
  have hs : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  refine ⟨GlobalTheory.PolDeg.Wit.ofDeg D₁ hB, AddEquiv.refl _, xEquiv F₁ F₂ hXe, GlobalTheory.PolDeg.Wit.refines_ofDeg D₁ hB, ?_⟩
  let β₂ := (lift (fst D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₁.pr) (snd D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₁.pr) : G2 D₂.P.A ⟶ G2 D₁.P.A).left
  have hsq : IsSquare (F₂.inc ≫ F₁.pr).left β₂ := by
    constructor
    · rw [← Over.comp_left, lift_fst, Over.comp_left]
    · rw [← Over.comp_left, lift_snd, Over.comp_left]

  haveI : Nonempty (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0}) :=
    ⟨(coprod.inl : D₁.P.A.left ⟶ _) (Classical.arbitrary _)⟩
  have hL₁ := D₁.P.isLB
  have hL₂ := D₂.P.isLB
  have hL' := D'.P.isLB
  have h₁₂ := join_isLB hL₁ hL₂
  have hN := join_isLB h₁₂ hL'
  have P₁ : IsPart (join (join D₁.P.L D₂.P.L) D'.P.L) D₁.P.L (coprod.inl ≫ coprod.inl) (Prod.fst ∘ Prod.fst) :=
    (isPart_inl _ _).trans (isPart_inl _ _)
  have P₂ : IsPart (join (join D₁.P.L D₂.P.L) D'.P.L) D₂.P.L (coprod.inr ≫ coprod.inl) (Prod.snd ∘ Prod.fst) :=
    (isPart_inl _ _).trans (isPart_inr _ _)
  have P' : IsPart (join (join D₁.P.L D₂.P.L) D'.P.L) D'.P.L coprod.inr Prod.snd := isPart_inr _ _
  have sπ₁ : Function.Surjective (Prod.fst ∘ Prod.fst : (join (join D₁.P.L D₂.P.L) D'.P.L).ι → D₁.P.L.ι) :=
    (fst_surjective hL₂).comp (fst_surjective hL')
  have sπ₂ : Function.Surjective (Prod.snd ∘ Prod.fst : (join (join D₁.P.L D₂.P.L) D'.P.L).ι → D₂.P.L.ι) :=
    (snd_surjective hL₁).comp (fst_surjective hL')
  obtain ⟨t₂, ht₂, vt₂⟩ := exists_gen_of_iso P' P₂ F₂.w F₂.w_gen
  obtain ⟨t₁, ht₁, vt₁⟩ := exists_gen_of_iso P' P₁ F₁.w F₁.w_gen
  have hℓ := lift_comp F₁ F₂ he hf
  let t := LB.mulGen _ _ _ _ _ t₂ (LB.invGen _ _ _ (LB.pullGen _ _ _ t₁ β₂))
  have ht : t.IsGen := LB.isGen_mulGen _ _ _ _ _ _ _ ht₂ (LB.isGen_invGen _ _ _ _ (LB.isGen_pullGen _ _ _ _ ht₁ _))
  obtain ⟨t', ht', vt'⟩ := exists_gen hN (formEq_cancel _ _ _ _ _ β₂ (fun k => by rw [← Category.assoc, hℓ])) t ht
  obtain ⟨w, hw, vw⟩ := exists_iso_of_gen P₁ P₂ hL₁ hL₂ sπ₁ sπ₂ t' ht'
  refine ⟨(F₂.inc ≫ F₁.pr).left, β₂, w, (isGrpPullback_of_iso eI).congr hs.symm rfl, hsq, hw, fun a => ?_, ?_⟩
  · show (D₂.c a).left ≫ (F₂.inc ≫ F₁.pr).left = spMap (RingHom.id R) ≫ (D₁.c (F₁.xp (F₂.xi a))).left
    rw [hs, Category.id_comp, ← Over.comp_left, c_comp F₁ F₂ hXe]
  intro κ hκ a b z J J' hJ hJ'
  obtain rfl : κ = 𝟙 _ := by
    rw [hs, Category.comp_id] at hκ
    have : Mono (jK R) := GlobalTheory.PolDeg.Wit.mono_jK
    exact (cancel_mono (jK R)).1 (hκ.trans (Category.id_comp _).symm)
  obtain ⟨J₁₂, hJ₁₂, e₁, e₂⟩ := exists_good_join hL₁ hL₂ hJ hJ'
  choose I hI using fun χ : (TK R).left ⟶ D'.P.A.left => exists_chart hL' (χ z)
  obtain ⟨JN, hJN, e₃, e₄⟩ := exists_good_join h₁₂ hL' hJ₁₂ (J₂ := I) hI
  have r₁ : GlobalTheory.Mum.Two.rs (coprod.inl ≫ coprod.inl) (Prod.fst ∘ Prod.fst) JN = J := by
    rw [← e₁, ← e₃]; funext ψ; simp only [GlobalTheory.Mum.Two.rs, GlobalTheory.Mum.Two.rl, GlobalTheory.Mum.Two.rr, Function.comp, Category.assoc]
  have r₂ : GlobalTheory.Mum.Two.rs (coprod.inr ≫ coprod.inl) (Prod.snd ∘ Prod.fst) JN = J' := by
    rw [← e₂, ← e₃]; funext ψ; simp only [GlobalTheory.Mum.Two.rs, GlobalTheory.Mum.Two.rl, GlobalTheory.Mum.Two.rr, Function.comp, Category.assoc]
  have r₃ : GlobalTheory.Mum.Two.rs coprod.inr Prod.snd JN = I := e₄
  have hp : (lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left ≫ β₂ =
      (lift (toUnit (TK R) ≫ D₁.c (F₁.xp (F₂.xi a))) (toUnit (TK R) ≫ D₁.c (F₁.xp (F₂.xi b)))).left := by
    simp only [β₂]
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc, Category.assoc,
      c_comp F₁ F₂ hXe, c_comp F₁ F₂ hXe]
  have v := vw _ (lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left z JN hJN
  rw [vt' _ _ z JN hJN] at v
  have hv : val t (lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left z JN =
      val t₂ (lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left z JN *
        (val t₁ ((lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left ≫ β₂) z JN)⁻¹ := by
    rw [val_mul hJN, val_inv, val_pull hJN]
  rw [hv, vt₂ _ _ z JN hJN, vt₁ _ _ z JN hJN, r₁, r₂, r₃, hp] at v
  have hF₂ := F₂.tau a b z I J' hI hJ'
  have hF₁ := F₁.tau (F₁.xp (F₂.xi a)) (F₁.xp (F₂.xi b)) z I J hI hJ
  rw [xi_xp_xi F₁ F₂ hXe, xi_xp_xi F₁ F₂ hXe, hXf] at hF₁
  have hQ := (GlobalTheory.PolDeg.Wit.exists_tau D₁ (F₁.xp (F₂.xi a)) (F₁.xp (F₂.xi b))).choose_spec.2 _ (𝟙 _) z J hJ
  change GlobalTheory.PolDeg.lamVal w _ z J J' = GlobalTheory.PolDeg.lamVal F₂.w _ z I J' * (GlobalTheory.PolDeg.lamVal F₁.w _ z I J)⁻¹ at v
  rw [hF₂]
  refine Eq.trans ?_ (congrArg₂ (· * ·) v.symm hQ.symm)
  rw [hF₁, _root_.mul_assoc, inv_mul_cancel_left]

end GlobalTheory.Mum.TwoFac
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumCmp.SamePolIso
variable {R : Type} [CommRing R] [IsDomain R]

theorem grp_iso {B Q : Over (Sp R)} [GrpObj B] [GrpObj Q] {β : B.left ⟶ Q.left}
    (h : IsGrpPullback B Q (spMap (RingHom.id R)) β) : ∃ f : B ≅ Q, f.hom.left = β ∧ IsMonHom f.hom := by
  have hs : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  have h1 := h.1
  rw [hs] at h1
  have : IsIso β := h1.isIso_fst_of_isIso
  let f : B ⟶ Q := Over.homMk β (by simpa using h1.w)
  have : IsIso ((Over.forget (Sp R)).map f) := (inferInstance : IsIso β)
  have : IsIso f := isIso_of_reflects_iso f (Over.forget _)
  refine ⟨asIso f, rfl, isMonHom_of_mul _ fun T x y => ?_⟩
  let ρ : Over.mk (T.hom ≫ spMap (RingHom.id R)) ⟶ T := Over.homMk (𝟙 T.left) (by simp [hs])
  have e := h.2 T x y (ρ ≫ x ≫ f) (ρ ≫ y ≫ f) (by simp [ρ, f]) (by simp [ρ, f])
  apply Over.OverMorphism.ext
  rw [← MonObj.comp_mul] at e
  simpa [ρ, f] using e.symm

theorem gw_congr {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    {f f' : Y ⟶ X'} (hf : f = f') (y : Y) {j j' : L.ι} (hj : j = j') {k k' : L'.ι} (hk : k = k') :
    gw w f y j k = gw w f' y j' k' := by
  subst hf hj hk; rfl

theorem exists_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D : DegPre R), SamePol D₀ D →
  ∃ (β : D₀.P.A ≅ D.P.A) (xe : D₀.X ≃+ D.X), IsMonHom β.hom ∧ (∀ χ, D₀.c χ ≫ β.hom = D.c (xe χ)) ∧
    ∃ wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L)
        ((abelian₂ D.P.A D.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) : G2 D₀.P.A ⟶ G2 D.P.A).left),
      wΛ.IsGen ∧
      ∀ (a a' : D₀.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι)
        (J' : ((TK R).left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D.P.L z J → Good D₀.P.L z J' →
        val (D₀.tau a a') (𝟙 _) z J' =
          GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z J J' *
            val (D.tau (xe a) (xe a')) (𝟙 _) z J := by
  intro R _ _ D₀ D h
  obtain ⟨Q, e₀, e, ⟨β₀, β₂₀, w₀, p₀, s₀, g₀, c₀, t₀⟩, ⟨β₁, β₂₁, w₁, p₁, s₁, g₁, c₁, t₁⟩⟩ := h
  have hs : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  obtain ⟨f₀, hf₀, m₀⟩ := grp_iso p₀
  obtain ⟨f₁, hf₁, m₁⟩ := grp_iso p₁
  have cc₀ : ∀ a, D₀.c a ≫ f₀.hom = Q.c (e₀ a) := fun a => Over.OverMorphism.ext (by
    rw [Over.comp_left, hf₀, c₀ a, hs, Category.id_comp])
  have cc₁ : ∀ a, D.c a ≫ f₁.hom = Q.c (e a) := fun a => Over.OverMorphism.ext (by
    rw [Over.comp_left, hf₁, c₁ a, hs, Category.id_comp])
  have ea : ∀ x, e ((e₀.trans e.symm) x) = e₀ x := fun x => by simp
  have hcβ : ∀ χ, D₀.c χ ≫ (f₀ ≪≫ f₁.symm).hom = D.c ((e₀.trans e.symm) χ) := fun χ => by
    rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, cc₀, Iso.comp_inv_eq, cc₁, ea]
  have hF : (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) :
      G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁ = β₂₀ := by
    apply pullback.hom_ext
    · change _ ≫ β₂₁ ≫ (fst Q.B Q.B).left = β₂₀ ≫ (fst Q.B Q.B).left
      rw [s₁.1, s₀.1, ← Category.assoc, ← Over.comp_left, lift_fst, ← hf₁, ← hf₀, ← Over.comp_left, ← Over.comp_left]
      simp
    · change _ ≫ β₂₁ ≫ (snd Q.B Q.B).left = β₂₀ ≫ (snd Q.B Q.B).left
      rw [s₁.2, s₀.2, ← Category.assoc, ← Over.comp_left, lift_snd, ← hf₁, ← hf₀, ← Over.comp_left, ← Over.comp_left]
      simp

  subst hF
  have hLQ : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ Q.M.isLB _ _
  have hLD : (abelian₂ D.P.A D.P.L).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  have hLD₀ : (abelian₂ D₀.P.A D₀.P.L).IsLB := DVR.linComb_isLB _ D₀.P.isLB _ _
  obtain ⟨wΛ, T⟩ := exists_cancel hLQ w₁ w₀ ((isGen_iff _).1 g₁) ((isGen_iff _).1 g₀) hLD hLD₀
  refine ⟨f₀ ≪≫ f₁.symm, e₀.trans e.symm, ?_, hcβ, wΛ,
    (isGen_iff _).2 (T.pgen_cancel hLQ ((isGen_iff _).1 g₁) ((isGen_iff _).1 g₀)), ?_⟩
  · show IsMonHom (f₀.hom ≫ f₁.inv)
    infer_instance
  intro a a' z J J' hJ hJ'
  choose d hd using fun χ : (TK R).left ⟶ Q.B.left => exists_chart Q.M.isLB (χ z)
  have hκ : 𝟙 (TK R).left ≫ jK R = jK R ≫ spMap (RingHom.id R) := by rw [hs]; simp
  have A₀ := t₀ (𝟙 _) hκ a a' z d J' hd hJ'
  have A₁ := t₁ (𝟙 _) hκ ((e₀.trans e.symm) a) ((e₀.trans e.symm) a') z d J hd hJ
  rw [ea, ea] at A₁
  have hP : (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left = (lift (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a)) (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a'))).left := by
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc, Category.assoc, hcβ, hcβ]
  have m₁ : β₂₁ ((lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z)) ∈ (abelian₂ Q.B Q.M.L).U
      (fun I => d ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ ((lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁) ≫ (psum Q.B (x2 Q.B) I.down).left)) := by
    have := Good.mem (L := Q.M.L) hd (fun I : ULift (Finset (Fin 2)) => (psum Q.B (x2 Q.B) I.down).left) ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁)
    simp only [Category.assoc] at this ⊢
    exact this
  have m₂ : (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z) ∈ (abelian₂ D.P.A D.P.L).U (fun I => J ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ (psum D.P.A (x2 D.P.A) I.down).left)) := by
    have := Good.mem (L := D.P.L) hJ (fun I : ULift (Finset (Fin 2)) => (psum D.P.A (x2 D.P.A) I.down).left) ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left)
    simp only [Category.assoc] at this
    exact this
  have m₃ : (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z ∈ (abelian₂ D₀.P.A D₀.P.L).U (fun I => J' ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (psum D₀.P.A (x2 D₀.P.A) I.down).left)) :=
    Good.mem (L := D₀.P.L) hJ' (fun I : ULift (Finset (Fin 2)) => (psum D₀.P.A (x2 D₀.P.A) I.down).left) (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left
  have key := T _ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z _ _ _ m₁ m₂ m₃
  have k₁ : gw w₁ ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left) z (fun I => d ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ ((lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁) ≫ (psum Q.B (x2 Q.B) I.down).left))
      (fun I => J ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ (psum D.P.A (x2 D.P.A) I.down).left)) =
      GlobalTheory.PolDeg.lamVal w₁ (lift (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a))
        (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a'))).left z d J :=
    gw_congr w₁ hP z (funext fun I => by rw [← hP]; simp only [Category.assoc])
      (funext fun I => by rw [← hP]; simp only [Category.assoc])
  rw [k₁] at key
  rw [A₀, A₁]
  change gw w₀ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z _ _ * _ = gw wΛ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z _ _ * _
  rw [key, _root_.mul_assoc, _root_.mul_left_comm]
end GlobalTheory.MumCmp.SamePolIso
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.MatEndPull

theorem ext_of_pb {T T' : Scheme.{0}} {t : T' ⟶ T} {G : Over T} {G' : Over T'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G t φ) {X : Over T'} {x y : X ⟶ G'}
    (e : x.left ≫ φ = y.left ≫ φ) : x = y := by
  apply Over.OverMorphism.ext
  apply h.1.hom_ext e
  rw [Over.w x, Over.w y]

theorem one_left_eq {T : Scheme.{0}} {X M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

theorem mul_comp_lift {T T' : Scheme.{0}} {t : T' ⟶ T} {B : Over T} {B' : Over T'} [GrpObj B] [GrpObj B']
    {φ : B'.left ⟶ B.left} (h : IsGrpPullback B' B t φ) {f : B ⟶ B} [IsMonHom f] {f' : B' ⟶ B'}
    (e : f'.left ≫ φ = φ ≫ f.left) {X : Over T'} (x y : X ⟶ B') :
    (x * y) ≫ f' = (x ≫ f') * (y ≫ f') := by
  apply ext_of_pb h
  have e₁ := h.2 X x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl
  have e₂ := h.2 X (x ≫ f') (y ≫ f') (pushPt h.1.w x ≫ f) (pushPt h.1.w y ≫ f)
    (by simp [pushPt, e]) (by simp [pushPt, e])
  rw [← e₂, Over.comp_left, Category.assoc, e, ← Category.assoc, ← e₁, ← Over.comp_left, mul_comp]

theorem isMonHom_lift {T T' : Scheme.{0}} {t : T' ⟶ T} {B : Over T} {B' : Over T'} [GrpObj B] [GrpObj B']
    {φ : B'.left ⟶ B.left} (h : IsGrpPullback B' B t φ) {f : B ⟶ B} [IsMonHom f] {f' : B' ⟶ B'}
    (e : f'.left ≫ φ = φ ≫ f.left) : IsMonHom f' := by
  have h1 : ∀ (X : Over T'), (1 : X ⟶ B') ≫ f' = 1 := fun X => by
    have := mul_comp_lift h e (1 : X ⟶ B') 1
    rw [_root_.mul_one] at this
    exact mul_eq_left.1 this.symm
  refine ⟨?_, ?_⟩
  · have := h1 (𝟙_ _)
    simpa [Hom.one_def] using this
  · have := mul_comp_lift h e (fst B' B') (snd B' B')
    simpa [Hom.mul_def] using this

theorem unit_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'}
    [GrpObj G'] {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G f φ) :
    η[G'].left ≫ φ = f ≫ η[G].left := by
  have h := hG.2 (𝟙_ _) 1 1 (pushPt hG.1.w 1) (pushPt hG.1.w 1) rfl rfl
  rw [_root_.mul_one] at h
  have h3 : pushPt hG.1.w (1 : 𝟙_ (Over S') ⟶ G') * pushPt hG.1.w 1 = pushPt hG.1.w 1 :=
    Over.OverMorphism.ext h
  have h4 : (1 : 𝟙_ (Over S') ⟶ G').left ≫ φ = (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G).left :=
    congrArg Over.Hom.left (mul_eq_left.1 h3)
  rw [one_left_eq, one_left_eq] at h4
  simpa using h4

theorem matEnd_pull : ∀ {T T' : Scheme.{0}} {t : T' ⟶ T} {B C : Over T} [GrpObj B] [GrpObj C] {B' C' : Over T'} [GrpObj B'] [GrpObj C'] {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} (pr : Fin 8 → (B ⟶ C)) (pr' : Fin 8 → (B' ⟶ C')) (a b : Fin 8) (f₁ : B ⟶ B) (f₁' : B' ⟶ B'), IsGrpPullback B' B t φB → IsGrpPullback C' C t χ → (∀ w, (pr' w).left ≫ χ = φB ≫ (pr w).left) → f₁'.left ≫ φB = φB ≫ f₁.left → MatEnd pr a b f₁ → MatEnd pr' a b f₁' := by
  intro T T' t B C _ _ B' C' _ _ φB χ pr pr' a b f₁ f₁' hB hC hpr e hf
  obtain ⟨hm, hw⟩ := hf
  haveI := hm
  refine ⟨isMonHom_lift hB e, fun w => ?_⟩
  apply ext_of_pb hC
  have key : (f₁' ≫ pr' w).left ≫ χ = φB ≫ (f₁ ≫ pr w).left := by
    rw [Over.comp_left, Category.assoc, hpr, ← Category.assoc, e, Category.assoc, ← Over.comp_left]
  rw [key, hw w]
  split_ifs
  · exact (hpr b).symm
  · rw [one_left_eq, one_left_eq, ← Category.assoc, hB.1.w, Category.assoc, Category.assoc,
      unit_pull hC]

end GlobalTheory.MatEndPull

end
end
