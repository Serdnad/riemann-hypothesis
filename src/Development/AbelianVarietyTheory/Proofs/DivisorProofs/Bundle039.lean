module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Basic.Complex.Basic
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Mathlib.AlgebraicGeometry.Group.Affine

@[expose] public section

section

noncomputable section

open AlgebraicGeometry NumberField
open scoped Matrix

namespace GlobalTheory.BalProj

def eigSp {O k : Type} [Field k] {n : ℕ} (B : O → Matrix (Fin n) (Fin n) k) (χ : O → k) :
    Submodule k (Fin n → k) where
  carrier := {c | ∀ a, c ᵥ* B a = χ a • c}
  zero_mem' := fun a => by simp
  add_mem' := fun {c d} hc hd a => by rw [Matrix.add_vecMul, hc a, hd a, smul_add]
  smul_mem' := fun r c hc a => by rw [Matrix.smul_vecMul, hc a, smul_comm]

def eigRank {O R k : Type} [CommRing R] [Field k] (φ : R →+* k) {n : ℕ} (A : O → Matrix (Fin n) (Fin n) R)
    (χ : O → R) : ℕ :=
  Module.finrank k (eigSp (fun a => (A a).map φ) (fun a => φ (χ a)))

def embR {E : Type} [Field E] (F : IntermediateField ℚ ℂ) (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) {R : Type}
    [CommRing R] (ι : F →+* R) (τ : E →+* ℂ) (a : 𝓞 E) : R :=
  ι ⟨τ (a : E), hF τ a⟩

def fnHom {K : Type} [CommRing K] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) : K →+* Γ(X, U) :=
  (s.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

end GlobalTheory.BalProj
end
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem scheme_hom_ext_of_jointly_injective : ∀ (Z Z₁ Z₂ X : Scheme.{0}) (e₁ : Z₁ ⟶ Z) (e₂ : Z₂ ⟶ Z), (∀ z : Z, (∃ z₁, e₁ z₁ = z) ∨ ∃ z₂, e₂ z₂ = z) → (∀ (W : Z.Opens) (a b : Γ(Z, W)), e₁.app W a = e₁.app W b → e₂.app W a = e₂.app W b → a = b) → ∀ f g : Z ⟶ X, e₁ ≫ f = e₁ ≫ g → e₂ ≫ f = e₂ ≫ g → f = g := by
  intro Z Z₁ Z₂ X e₁ e₂ hcov hinj f g h₁ h₂
  have hbase : f.base = g.base := by
    ext z
    rcases hcov z with ⟨z₁, rfl⟩ | ⟨z₂, rfl⟩
    · have := congrArg (fun k : Z₁ ⟶ X => k z₁) h₁
      simpa [Scheme.Hom.comp_apply] using this
    · have := congrArg (fun k : Z₂ ⟶ X => k z₂) h₂
      simpa [Scheme.Hom.comp_apply] using this
  have key : ∀ {Y : Scheme.{0}} (e : Y ⟶ Z), e ≫ f = e ≫ g → ∀ U : X.Opens,
      (f.app U ≫ Z.presheaf.map (eqToHom congr((TopologicalSpace.Opens.map $hbase.symm).obj U)).op) ≫
        e.app (g ⁻¹ᵁ U) = g.app U ≫ e.app (g ⁻¹ᵁ U) := by
    intro Y e he U
    rw [Category.assoc, Scheme.Hom.naturality, ← Category.assoc, ← Scheme.Hom.comp_app,
      Scheme.Hom.congr_app he]
    simp [Scheme.Hom.comp_app]
    conv_rhs => rw [← Category.comp_id (Scheme.Hom.app e (g ⁻¹ᵁ U))]
    congr 2
    exact (Y.presheaf.map_comp _ _).symm.trans
      ((congrArg Y.presheaf.map (Subsingleton.elim _ _)).trans (Y.presheaf.map_id _))
  refine Scheme.Hom.ext hbase fun U => ?_
  ext s
  apply hinj (g ⁻¹ᵁ U)
  · exact congr(($(key e₁ h₁ U)).hom s)
  · exact congr(($(key e₂ h₂ U)).hom s)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchBasis

theorem isPullback_iff_elem {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (i : C ⟶ D)
    (w : f ≫ h = g ≫ i) :
    IsPullback f g h i ↔ (∀ x y, f.hom x = f.hom y → g.hom x = g.hom y → x = y) ∧
      ∀ b c, h.hom b = i.hom c → ∃ a, f.hom a = b ∧ g.hom a = c := by
  constructor
  · intro H
    have H' := (Types.isPullback_iff _ _ _ _).1 (H.map (forget CommRingCat))
    exact ⟨fun x y hx hy ↦ H'.2.1 x y ⟨hx, hy⟩, fun b c hbc ↦ H'.2.2 b c hbc⟩
  · rintro ⟨h₁, h₂⟩
    refine IsPullback.of_map (forget CommRingCat) w ((Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩)
    · ext x
      simpa using congrArg (fun φ : A ⟶ D ↦ φ.hom x) w
    · exact fun x y hxy ↦ h₁ x y hxy.1 hxy.2
    · exact fun b c hbc ↦ h₂ b c hbc

lemma app_res {X Y : Scheme.{0}} (f : X ⟶ Y) {W V : Y.Opens} (i : W ⟶ V) (s : Γ(Y, V)) :
    (f.app W).hom ((Y.presheaf.map i.op).hom s) =
      (X.presheaf.map ((TopologicalSpace.Opens.map f.base).map i).op).hom ((f.app V).hom s) :=
  congrArg (fun φ => φ.hom s) (f.naturality i.op)

lemma appLE_res {X Y : Scheme.{0}} (g : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens} (hU : U' ≤ U)
    (hV : V' ≤ V) (e : V ≤ g ⁻¹ᵁ U) (e' : V' ≤ g ⁻¹ᵁ U') (b : Γ(Y, U)) :
    (g.appLE U' V' e').hom ((Y.presheaf.map (homOfLE hU).op).hom b) =
      (X.presheaf.map (homOfLE hV).op).hom ((g.appLE U V e).hom b) := by
  have h1 := congrArg (fun φ => φ.hom b) (g.map_appLE e' (homOfLE hU).op)
  have h2 := congrArg (fun φ => φ.hom b) (g.appLE_map e (homOfLE hV).op)
  exact h1.trans h2.symm

lemma res_res (X : Scheme.{0}) {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V) (k : W ⟶ U) (s : Γ(X, U)) :
    (X.presheaf.map j.op).hom ((X.presheaf.map i.op).hom s) = (X.presheaf.map k.op).hom s := by
  have := congrArg (fun φ => φ.hom s) (X.presheaf.map_comp i.op j.op)
  exact this.symm.trans rfl

theorem isPullback_app_of_isBasis : ∀ (Y₀ Y₁ Y₂ Y : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (𝒱 : Set Y.Opens), TopologicalSpace.Opens.IsBasis 𝒱 → (∀ V ∈ 𝒱, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)) := by
  intro Y₀ Y₁ Y₂ Y i₁ i₂ j₁ j₂ hw 𝒱 h𝒱 hP
  have hle : ∀ V : Y.Opens, (i₁ ≫ j₁) ⁻¹ᵁ V ≤ i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ V) := fun V => by rw [hw]; exact le_rfl
  have hcomm : ∀ V : Y.Opens, j₁.app V ≫ i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl =
      j₂.app V ≫ i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (hle V) := by
    intro V
    have key : ∀ (k k' : Y₀ ⟶ Y), k = k' → ∀ (e : (i₁ ≫ j₁) ⁻¹ᵁ V ≤ k ⁻¹ᵁ V)
        (e' : (i₁ ≫ j₁) ⁻¹ᵁ V ≤ k' ⁻¹ᵁ V), k.appLE V ((i₁ ≫ j₁) ⁻¹ᵁ V) e = k'.appLE V ((i₁ ≫ j₁) ⁻¹ᵁ V) e' := by
      rintro k _ rfl e e'; rfl
    exact (Scheme.Hom.comp_appLE i₁ j₁ V _ le_rfl).symm.trans
      ((key _ _ hw _ _).trans (Scheme.Hom.comp_appLE i₂ j₂ V _ (hle V)))
  have hcovY : ∀ U : Y.Opens, U ≤ ⨆ W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ U}, W.1 := by
    intro U y hy
    obtain ⟨W, hW, hyW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 h𝒱 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW, hWU⟩, hyW⟩
  have hcov : ∀ {Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens),
      f ⁻¹ᵁ U ≤ ⨆ W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ U}, f ⁻¹ᵁ W.1 := by
    intro Z f U z hz
    obtain ⟨W, hW, hzW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 h𝒱 (x := f z) hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW, hWU⟩, hzW⟩

  have inj : ∀ (U : Y.Opens) (s t : Γ(Y, U)), (j₁.app U).hom s = (j₁.app U).hom t →
      (j₂.app U).hom s = (j₂.app U).hom t → s = t := by
    intro U s t h₁ h₂
    refine Y.sheaf.eq_of_locally_eq' (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ U} => W.1) U
      (fun W => homOfLE W.2.2) (hcovY U) s t ?_
    rintro ⟨W, hW, hWU⟩
    obtain ⟨hinj, -⟩ := (isPullback_iff_elem _ _ _ _ (hcomm W)).1 (hP W hW)
    apply hinj
    · exact (app_res j₁ (homOfLE hWU) s).trans ((congrArg _ h₁).trans (app_res j₁ (homOfLE hWU) t).symm)
    · exact (app_res j₂ (homOfLE hWU) s).trans ((congrArg _ h₂).trans (app_res j₂ (homOfLE hWU) t).symm)

  have surj : ∀ (V : Y.Opens) (b : Γ(Y₁, j₁ ⁻¹ᵁ V)) (c : Γ(Y₂, j₂ ⁻¹ᵁ V)),
      (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl).hom b =
        (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (hle V)).hom c →
      ∃ a, (j₁.app V).hom a = b ∧ (j₂.app V).hom a = c := by
    intro V b c hbc
    have loc : ∀ W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V}, ∃ a : Γ(Y, W.1),
        (j₁.app W.1).hom a = (Y₁.presheaf.map (homOfLE (j₁.preimage_mono W.2.2)).op).hom b ∧
        (j₂.app W.1).hom a = (Y₂.presheaf.map (homOfLE (j₂.preimage_mono W.2.2)).op).hom c := by
      rintro ⟨W, hW, hWV⟩
      obtain ⟨-, hex⟩ := (isPullback_iff_elem _ _ _ _ (hcomm W)).1 (hP W hW)
      apply hex
      have e1 := appLE_res i₁ (j₁.preimage_mono hWV) ((i₁ ≫ j₁).preimage_mono hWV) le_rfl le_rfl b
      have e2 := appLE_res i₂ (j₂.preimage_mono hWV) ((i₁ ≫ j₁).preimage_mono hWV) (hle V) (hle W) c
      exact e1.trans ((congrArg _ hbc).trans e2.symm)
    choose sf hsf₁ hsf₂ using loc
    have hcompat : TopCat.Presheaf.IsCompatible Y.sheaf.1 (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V} => W.1) sf := by
      intro W W'
      apply inj
      · refine (app_res j₁ _ _).trans (Eq.trans ?_ (app_res j₁ _ _).symm)
        rw [hsf₁, hsf₁]
        exact (res_res Y₁ _ _ (homOfLE (j₁.preimage_mono (inf_le_left.trans W.2.2))) b).trans
          (res_res Y₁ _ _ (homOfLE (j₁.preimage_mono (inf_le_left.trans W.2.2))) b).symm
      · refine (app_res j₂ _ _).trans (Eq.trans ?_ (app_res j₂ _ _).symm)
        rw [hsf₂, hsf₂]
        exact (res_res Y₂ _ _ (homOfLE (j₂.preimage_mono (inf_le_left.trans W.2.2))) c).trans
          (res_res Y₂ _ _ (homOfLE (j₂.preimage_mono (inf_le_left.trans W.2.2))) c).symm
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V} => W.1) V
      (fun W => homOfLE W.2.2) (hcovY V) sf hcompat
    refine ⟨s, ?_, ?_⟩
    · refine Y₁.sheaf.eq_of_locally_eq' (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V} => j₁ ⁻¹ᵁ W.1) (j₁ ⁻¹ᵁ V)
        (fun W => homOfLE (j₁.preimage_mono W.2.2)) (hcov j₁ V) _ _ ?_
      intro W
      exact (app_res j₁ (homOfLE W.2.2) s).symm.trans ((congrArg (j₁.app W.1).hom (hs W)).trans (hsf₁ W))
    · refine Y₂.sheaf.eq_of_locally_eq' (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V} => j₂ ⁻¹ᵁ W.1) (j₂ ⁻¹ᵁ V)
        (fun W => homOfLE (j₂.preimage_mono W.2.2)) (hcov j₂ V) _ _ ?_
      intro W
      exact (app_res j₂ (homOfLE W.2.2) s).symm.trans ((congrArg (j₂.app W.1).hom (hs W)).trans (hsf₂ W))
  intro V
  exact (isPullback_iff_elem _ _ _ _ (hcomm V)).2 ⟨fun x y hx hy => inj V x y hx hy, surj V⟩

end GlobalTheory.PinchBasis
end
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

theorem pow_kills_on_compact_of_local : ∀ (S : Scheme.{0}) (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop) (W : S.Opens), IsCompact (W : Set S) → ∀ (s c : Γ(S, W)), (∀ y ∈ W, ∃ (V : S.Opens) (hV : V ≤ W), y ∈ V ∧ ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0) → ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app W).hom (s ^ n * c) = 0 := by
  intro S Φ W hW s c h
  have h' : ∀ y : W, ∃ (V : S.Opens) (hV : V ≤ W), y.1 ∈ V ∧ ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0 :=
    fun y => h y.1 y.2
  choose V hV hyV n hn using h'
  obtain ⟨F, hF⟩ := hW.elim_finite_subcover (fun y : W => (V y : Set S)) (fun y => (V y).isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩)
  refine ⟨∑ y ∈ F, n y, fun T t hΦ => ?_⟩
  apply TopCat.Presheaf.section_ext T.sheaf (t ⁻¹ᵁ W)
  intro x hx
  have hxW : t.base x ∈ (W : Set S) := hx
  obtain ⟨y, hyF, hxy⟩ := Set.mem_iUnion₂.1 (hF hxW)
  have hle : t ⁻¹ᵁ V y ≤ t ⁻¹ᵁ W := fun z hz => hV y hz
  have hxV : x ∈ t ⁻¹ᵁ V y := hxy
  have hN : n y ≤ ∑ y ∈ F, n y := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hyF
  have key : (T.presheaf.map (homOfLE hle).op).hom ((t.app W).hom (s ^ (∑ y ∈ F, n y) * c)) = 0 := by
    have e := congrArg (fun φ => φ.hom (s ^ (∑ y ∈ F, n y) * c)) (t.naturality (homOfLE (hV y)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    have e2 : s ^ (∑ y ∈ F, n y) * c = s ^ (∑ y ∈ F, n y - n y) * (s ^ n y * c) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hN]
    refine Eq.trans ?_ (e.symm.trans ?_)
    · rfl
    · rw [e2, map_mul, map_mul, hn y T t hΦ, mul_zero]
  have := congrArg (T.presheaf.germ (t ⁻¹ᵁ V y) x hxV).hom key
  rw [TopCat.Presheaf.germ_res_apply, map_zero] at this
  exact this.trans (map_zero _).symm

end GlobalTheory
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.SpecialConn

variable {O : Type} [CommRing O] [IsLocalRing O] {Y : Scheme.{0}} (f : Y ⟶ Spec (.of O))

abbrev thickQ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    O →+* O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1) :=
  Ideal.Quotient.mk _

def thickR (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1 + 1) →+* O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

theorem thickR_comp (n : ℕ) : (thickR O n).comp (thickQ O (n + 1)) = thickQ O n := rfl

def thickFib (n : ℕ) : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (thickQ O n)))

def thickι (n : ℕ) : thickFib f n ⟶ Y := pullback.fst _ _

def thickTr (n : ℕ) : thickFib f n ⟶ thickFib f (n + 1) :=
  pullback.map _ _ _ _ (𝟙 Y) (Spec.map (CommRingCat.ofHom (thickR O n))) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, thickR_comp])

theorem thickTr_ι (n : ℕ) : thickTr f n ≫ thickι f (n + 1) = thickι f n :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

end GlobalTheory.SpecialConn
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory


set_option backward.isDefEq.respectTransparency.types false in
theorem exists_valuationRing_of_specializes (X : Scheme.{0}) (x' x : X) (h : x' ⤳ x) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : ValuationRing V)
      (g : Spec (CommRingCat.of V) ⟶ X),
      g (IsLocalRing.closedPoint V) = x ∧ g (⊥ : PrimeSpectrum V) = x' := by
  let φ : X.presheaf.stalk x ⟶ X.residueField x' :=
    X.presheaf.stalkSpecializes h ≫ X.residue x'
  obtain ⟨A, hA, hA_local⟩ := IsLocalRing.exists_factor_valuationRing φ.hom
  let ψ : X.presheaf.stalk x ⟶ .of A := CommRingCat.ofHom (φ.hom.codRestrict _ hA)
  have w : X.fromSpecResidueField x' =
      Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField x'))) ≫
        Spec.map ψ ≫ X.fromSpecStalk x := by
    rw [Scheme.fromSpecResidueField, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  refine ⟨A, inferInstance, inferInstance, inferInstance, Spec.map ψ ≫ X.fromSpecStalk x, ?_, ?_⟩
  · simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    have : Spec.map ψ (IsLocalRing.closedPoint A) =
        IsLocalRing.closedPoint (X.presheaf.stalk x) :=
      IsLocalRing.comap_closedPoint (S := A) (φ.hom.codRestrict A.toSubring hA)
    rw [this, X.fromSpecStalk_closedPoint]
  · have h1 : Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField x')))
        (IsLocalRing.closedPoint (X.residueField x')) = (⊥ : PrimeSpectrum A) := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap A (X.residueField x'))
        (IsLocalRing.maximalIdeal (X.residueField x')) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective _ Subtype.val_injective
    rw [← h1, ← Scheme.Hom.comp_apply, ← w, Scheme.fromSpecResidueField_apply]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace GlobalTheory.QcSub

variable {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)

def gen {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) : Subring (F.obj (op W)) :=
  Subring.closure (Set.range (α.app (op W)).hom ∪ (F.map (homOfLE h).op).hom '' T)

lemma algebraMap_mem_gen {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) (r : Γ(X, W)) :
    (α.app (op W)).hom r ∈ gen F α h T :=
  Subring.subset_closure (Or.inl ⟨r, rfl⟩)

lemma res_mem_gen {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) {t : F.obj (op V)}
    (ht : t ∈ T) : (F.map (homOfLE h).op).hom t ∈ gen F α h T :=
  Subring.subset_closure (Or.inr ⟨t, ht, rfl⟩)

lemma map_gen_le {V W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) (T : Set (F.obj (op V))) :
    (gen F α h T).map (F.map (homOfLE h').op).hom ≤ gen F α (h'.trans h) T := by
  rw [gen, RingHom.map_closure, Subring.closure_le]
  rintro _ ⟨y, (⟨r, rfl⟩ | ⟨t, ht, rfl⟩), rfl⟩
  · have := congr($(α.naturality (homOfLE h').op).hom r)
    simp only [CommRingCat.comp_apply] at this
    rw [← this]
    exact algebraMap_mem_gen F α _ T _
  · rw [← CommRingCat.comp_apply, ← F.map_comp]
    exact res_mem_gen F α _ T ht

lemma res_mem_gen_of_mem {V W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) (T : Set (F.obj (op V)))
    {b : F.obj (op W)} (hb : b ∈ gen F α h T) :
    (F.map (homOfLE h').op).hom b ∈ gen F α (h'.trans h) T :=
  map_gen_le F α h h' T ⟨b, hb, rfl⟩

lemma gen_eq_adjoin {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) :
    (letI := (α.app (op W)).hom.toAlgebra
     gen F α h T = (Algebra.adjoin Γ(X, W) ((F.map (homOfLE h).op).hom '' T)).toSubring) := by
  let := (α.app (op W)).hom.toAlgebra
  rw [Algebra.adjoin_eq_ring_closure]
  rfl

variable {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j))))

def sub (W : X.Opens) : Subring (F.obj (op W)) :=
  ⨅ (j : ι) (W' : X.Opens) (_ : IsAffineOpen W') (hW : W' ≤ W) (hV : W' ≤ V j),
    (gen F α hV (T j)).comap (F.map (homOfLE hW).op).hom

lemma mem_sub {W : X.Opens} {b : F.obj (op W)} :
    b ∈ sub F α V T W ↔ ∀ (j : ι) (W' : X.Opens), IsAffineOpen W' → ∀ (hW : W' ≤ W)
      (hV : W' ≤ V j), (F.map (homOfLE hW).op).hom b ∈ gen F α hV (T j) := by
  simp only [sub, Subring.mem_iInf, Subring.mem_comap]

lemma algebraMap_mem_sub (W : X.Opens) (r : Γ(X, W)) : (α.app (op W)).hom r ∈ sub F α V T W := by
  rw [mem_sub]
  intro j W' _ hW hV
  have := congr($(α.naturality (homOfLE hW).op).hom r)
  simp only [CommRingCat.comp_apply] at this
  rw [← this]
  exact algebraMap_mem_gen F α _ _ _

lemma res_mem_sub {W W₁ : X.Opens} (h : W₁ ≤ W) {b : F.obj (op W)} (hb : b ∈ sub F α V T W) :
    (F.map (homOfLE h).op).hom b ∈ sub F α V T W₁ := by
  rw [mem_sub] at hb ⊢
  intro j W' hW' hW hV
  rw [← CommRingCat.comp_apply, ← F.map_comp]
  exact hb j W' hW' (hW.trans h) hV

def subMap (W : X.Opens) : Γ(X, W) →+* sub F α V T W :=
  (α.app (op W)).hom.codRestrict _ (algebraMap_mem_sub F α V T W)

def subFunctor : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj W := CommRingCat.of (sub F α V T W.unop.1)
  map {W W₁} f := CommRingCat.ofHom
    ((F.map ((Scheme.AffineZariskiSite.toOpensFunctor X).map f.unop).op).hom.restrict _ _
      (fun _ hb ↦ res_mem_sub F α V T _ hb))
  map_id W := by
    ext b
    change (F.map _).hom b.1 = b.1
    rw [Subsingleton.elim ((Scheme.AffineZariskiSite.toOpensFunctor X).map (𝟙 W).unop).op (𝟙 _)]
    erw [F.map_id]
    rfl
  map_comp {W₁ W₂ W₃} f g := by
    ext b
    change (F.map _).hom b.1 = (F.map _).hom ((F.map _).hom b.1)
    rw [← CommRingCat.comp_apply]
    erw [← F.map_comp]
    rfl

def subNat : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ subFunctor F α V T where
  app W := CommRingCat.ofHom (subMap F α V T W.unop.1)
  naturality {W W₁} f := by
    ext r
    exact Subtype.ext congr($(α.naturality ((Scheme.AffineZariskiSite.toOpensFunctor X).map f.unop).op).hom r)

def subIncl : subFunctor F α V T ⟶ (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ F where
  app W := CommRingCat.ofHom (sub F α V T W.unop.1).subtype
  naturality _ _ _ := rfl

lemma subNat_comp_subIncl :
    subNat F α V T ≫ subIncl F α V T = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α :=
  rfl

lemma subIncl_injective (W : X.AffineZariskiSiteᵒᵖ) : Function.Injective ((subIncl F α V T).app W).hom :=
  Subtype.val_injective

lemma isLocalizationAway
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {W : X.Opens} (hW : IsAffineOpen W) (f : Γ(X, W)) :
    (letI := (F.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
     IsLocalization.Away ((α.app (op W)).hom f) (F.obj (op (X.basicOpen f)))) :=
  Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mp hα ⟨W, hW⟩ f

end GlobalTheory.QcSub
end
