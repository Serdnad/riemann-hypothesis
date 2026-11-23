module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeDescendsAlongEtaleIsogeny
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle105
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open CechPic

theorem exists_heckeQuotient_triple_of_laws : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left) := by
  intro laws E _ _ _ H k _ _ _ t g p C hp hprop hsm hamp hK hst hpow
    hweil hcard
  have glob : Out.GlobalFnsSt := laws.globalFns
  have cube := GlobalTheory.Moduli.cube_of_isLB
  have cubeDesc := GlobalTheory.cube_descends_along_etale_isogeny glob
  have quot := GlobalTheory.exists_quotient_by_finite_group_of_points laws
  have split := GlobalTheory.lbPow_descends_of_isotropic_of_laws laws
  have princ := GlobalTheory.kTriv_of_descent laws
  have amp := GlobalTheory.relAmple_finite_pow_iso
  have prim := GlobalTheory.PrimNorm.exists_primitive_normalisation glob
  have seesaw := GlobalTheory.T.seesaw_triviality_on_dense_fibres_product_abelian glob
  have hA : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hL := t.PP.isLB
  let P : Out.PolAV (Sp k) :=
    { A := t.G, isAb := hA, g := g, smoothDim := hsm, L := t.PP.L, isLB := hL,
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := sym_of_isSymmetric t.PP t.sym, ample := hamp, ktriv := hK }
  have hn : 0 < p ^ 2 := pow_pos hp 2
  have hfin : Finite C := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (pow_pos hp _).ne')
  obtain ⟨B, gB, ψ, hB, hψ, hf, he, hs, hker, huniv⟩ :
      ∃ (B : Over (Sp k)) (_ : GrpObj B) (ψ : t.G ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧
        Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧
        ∀ (Y : Over (Sp k)) (f : t.G ⟶ Y), (∀ x ∈ C, ((toUnit t.G ≫ x) * 𝟙 t.G) ≫ f = f) →
          ∃! f' : B ⟶ Y, ψ ≫ f' = f := quot k P C hfin
  have := hB.comm
  obtain ⟨M, hM, hiso⟩ : ∃ M : LB B.left, M.IsLB ∧ LBIso (lbPow t.PP.L (p ^ 2)) (M.pull ψ.left) :=
    split k P (p ^ 2) C B ψ hn (Nat.cast_ne_zero.2 hn.ne') hpow hweil hψ hf he hs hker
  have hΘ : ∃ s : LB.Gen (Theta B M), s.IsGen :=
    cubeDesc k t.G B ψ M hA hB hM hψ hf he hs (cube _ P (M.pull ψ.left) (pull_isLB hM _))
  have hn' : (lbPow t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb hL _ _
  have hid : IsFinite (𝟙 t.G : t.G ⟶ t.G).left := by rw [Over.id_left]; infer_instance
  have a₁ : Out.RelAmple t.G (lbPow t.PP.L (p ^ 2)) :=
    (amp _ t.G t.G (𝟙 _) t.PP.L (p ^ 2) hn hA hA hL hid).2.1.2 hamp

  have hMamp : Out.RelAmple B M :=
    (amp _ t.G B ψ M 1 one_pos hA hB hM hf).2.2.1 inferInstance hs
      ((amp _ t.G t.G (𝟙 _) _ 1 one_pos hA hA hn' hid).2.2.2 _ (pull_isLB hM _) hiso a₁)

  have fac : ∀ (Y : Over (Sp k)) [GrpObj Y] (f : t.G ⟶ Y) [IsMonHom f], (∀ x ∈ C, x ≫ f = 1) →
      ∃ f' : B ⟶ Y, ψ ≫ f' = f := fun Y _ f _ h =>
    (huniv Y f fun x hx => by
      rw [MonObj.mul_comp, Category.assoc, h x hx, MonObj.comp_one, _root_.one_mul, Category.id_comp]).exists
  have canc : ∀ (Y : Over (Sp k)) (f f' : B ⟶ Y), ψ ≫ f = ψ ≫ f' → f = f' := fun Y f f' h =>
    (huniv Y (ψ ≫ f) fun x hx => by
      rw [← Category.assoc, MonObj.mul_comp, Category.assoc, (hker x).2 hx, MonObj.comp_one, _root_.one_mul,
        Category.id_comp]).unique rfl h.symm
  have hact : ∀ a, ∃ f' : B ⟶ B, ψ ≫ f' = t.act.act a ≫ ψ := fun a => by
    have := t.act.hom a
    exact fac B _ fun x hx => by rw [← Category.assoc]; exact (hker _).2 (hst x hx a)
  choose α hα using hact
  let act : OAct (𝓞 E) B :=
    { act := α
      hom := fun a => laws.rigidity _ B B hB hB _ (by
        have := t.act.hom a
        rw [← IsMonHom.one_hom ψ, Category.assoc, hα, ← Category.assoc, IsMonHom.one_hom])
      one := canc _ _ _ (by rw [hα, t.act.one, Category.id_comp, Category.comp_id])
      mul := fun a b => canc _ _ _ (by
        rw [hα, t.act.mul, ← Category.assoc ψ, hα, Category.assoc, Category.assoc, hα])
      add := fun a b => canc _ _ _ (by rw [hα, t.act.add, MonObj.mul_comp, MonObj.comp_mul, hα, hα]) }
  have hαhom : ∀ a, IsMonHom (α a) := act.hom

  set l := cls t.PP.L hL with hl
  set m := cls M hM with hm
  have hψm : pull ψ.left m = (p ^ 2) • l := by
    rw [← cls_lbPow hL (p ^ 2) (LB.isLB_linComb hL _ _)]
    exact ((cls_eq_iff _ (pull_isLB hM _)).2 hiso).symm
  have lamψ : ∀ {T : Over (Sp k)} (u v : T ⟶ t.G), lam m (u ≫ ψ) (v ≫ ψ) = (p ^ 2) • lam l u v := fun u v => by
    rw [← lam_pull, hψm, lam_nsmul]

  have hpowhom : IsMonHom (𝟙 t.G ^ p ^ 2) := laws.rigidity _ _ _ hA hA _ (by
    have e₁ : (η[t.G] : 𝟙_ _ ⟶ t.G) = 1 := by rw [Hom.one_def]; simp
    rw [MonObj.comp_pow, Category.comp_id, e₁, one_pow])
  obtain ⟨π, hπ⟩ := fac t.G (𝟙 t.G ^ p ^ 2) fun x hx => by rw [MonObj.comp_pow, Category.comp_id, hpow x hx]
  have hπψ : π ≫ ψ = 𝟙 B ^ p ^ 2 := canc _ _ _ (by
    rw [← Category.assoc, hπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id])
  have adj : ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M)
      (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M) := by
    intro a
    have := hαhom a
    have := hαhom (H.bar a)
    have adjA : ∀ {T : Over (Sp k)} (u v : T ⟶ t.G), lam l (u ≫ t.act.act a) v = lam l u (v ≫ t.act.act (H.bar a)) := by
      intro T u v
      have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (t.adj a)
      have h' := congrArg (pull (lift u v).left)
        ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
      simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
    have adjψ : ∀ {T : Over (Sp k)} (u v : T ⟶ t.G),
        lam m (u ≫ ψ ≫ α a) (v ≫ ψ) = lam m (u ≫ ψ) (v ≫ ψ ≫ α (H.bar a)) := by
      intro T u v
      rw [hα, hα, ← Category.assoc, ← Category.assoc, lamψ, lamψ, adjA]
    have h₁ : (cubeLB B ![fst B B ≫ α a, snd B B] M).IsLB := LB.isLB_linComb hM _ _
    have h₂ : (cubeLB B ![fst B B, snd B B ≫ α (H.bar a)] M).IsLB := LB.isLB_linComb hM _ _
    have hN := LB.isLB_div h₂ h₁
    have val : ∀ {T : Over (Sp k)} (x y : T ⟶ B), lam m (x ≫ α a) y = lam m x (y ≫ α (H.bar a)) →
        ∃ s : ((LB.div (cubeLB B ![fst B B, snd B B ≫ α (H.bar a)] M)
          (cubeLB B ![fst B B ≫ α a, snd B B] M)).pull (lift x y).left).Gen, s.IsGen := by
      intro T x y h
      refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
      rw [cls_pull hN, cls_div h₂ h₁, cls_cube_two hM, cls_cube_two hM, map_sub, pull_lam, pull_lam, lift_fst,
        lift_snd, lift_fst_assoc, lift_snd_assoc, ← hm, h, sub_self]
    refine seesaw k B B _ M hB hB hM hMamp hN (val _ _ ?_) ?_ (val _ _ ?_)
    · rw [MonObj.one_comp, lam_one_left, lam_one_left]
    · have hs' : Surjective (𝟙 t.G ^ p ^ 2).left := (laws.mulN _ P (p ^ 2) hn).2.2.1
      have hs'' : Surjective ((𝟙 t.G ^ p ^ 2) ≫ ψ).left := by rw [Over.comp_left]; infer_instance
      refine dense_image_points ((𝟙 t.G ^ p ^ 2) ≫ ψ) _ fun u => val _ _ ?_
      have h := adjψ (toUnit B ≫ u) π
      rw [← Category.assoc π, hπψ, MonObj.pow_comp, lam_pow_right hM hΘ, lam_pow_right hM hΘ] at h
      rw [MonObj.pow_comp, MonObj.comp_pow, MonObj.comp_pow, MonObj.pow_comp, lam_pow_left hM hΘ,
        lam_pow_left hM hΘ]
      simpa only [Category.assoc, Category.id_comp] using h
    · rw [MonObj.one_comp, lam_one_right, lam_one_right]
  obtain ⟨PP, cub, hsym, hPP, -, hprim, hadj⟩ := prim E H _ B act M hB hM hΘ adj
  have hP' := PP.isLB
  have hpull : pull ψ.left (cls PP.L hP') = (p ^ 2) • l := by
    have h := (cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 t.prim
    have h' := (cls_eq_iff hP' (LB.isLB_linComb hM _ _)).2 hPP
    have e : l = lam l (𝟙 _) (t.act.act H.w0) := h.trans (cls_cube_two hL _ _ _)
    have e' : cls PP.L hP' = lam m (𝟙 _) (α H.w0) := h'.trans (cls_cube_two hM _ _ _)
    rw [e', pull_lam, hα, Category.comp_id, ← Category.id_comp ψ, ← Category.assoc, Category.comp_id, lamψ, ← e]
  have hfinal : LBIso (lbPow t.PP.L (p ^ 2)) (PP.L.pull ψ.left) := by
    rw [← cls_eq_iff hn' (pull_isLB hP' _), cls_lbPow hL, cls_pull hP', hpull]
  have a₂ : Out.RelAmple t.G (PP.L.pull ψ.left) :=
    (amp _ t.G t.G (𝟙 _) _ 1 one_pos hA hA hn' hid).2.2.2 _ (pull_isLB hP' _) hfinal a₁
  have a₃ : Out.RelAmple B PP.L :=
    (amp _ t.G B ψ PP.L 1 one_pos hA hB hP' hf).2.2.1 inferInstance hs a₂
  have hc : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ t.G // x ≫ ψ = 1} = (p ^ 2) ^ g := by
    rw [← pow_mul, ← hcard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hker)
  have hlam : LBIso (abelian₂ t.G (lbPow t.PP.L (p ^ 2))) (abelian₂ t.G (PP.L.pull ψ.left)) := by
    refine (cls_eq_iff (LB.isLB_linComb hn' _ _) (LB.isLB_linComb (pull_isLB hP' _) _ _)).1 ?_
    refine (cls_cube_two hn' _ _ _).trans (Eq.trans ?_ (cls_cube_two (pull_isLB hP' _) _ _ _).symm)
    rw [(cls_eq_iff hn' (pull_isLB hP' _)).2 hfinal]
  have a₄ : Out.KTriv B PP.L := princ k P (p ^ 2) B ψ PP.L hn hB hP' hψ hf he hs hc hlam
  exact ⟨{ G := B, semi := isSemiAbelian_of_isAbelianScheme B hB, act := act, PP := PP, cub := cub, sym := hsym,
           adj := hadj, prim := hprim }, ψ, hB.proper, a₃, a₄, hψ, hf, he, hs, hker, fun a => (hα a).symm, hfinal⟩

end GlobalTheory
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.KTrivGlob

private theorem mul_left_congr_of_base_eq {S T : Scheme.{0}} {G : Over S} [GrpObj G] {a b : T ⟶ S} (hab : a = b)
    (u v : Over.mk a ⟶ G) (u' v' : Over.mk b ⟶ G) (hu : u.left = u'.left) (hv : v.left = v'.left) :
    (u * v).left = (u' * v').left := by
  subst hab
  have h1 : u = u' := Over.OverMorphism.ext hu
  have h2 : v = v' := Over.OverMorphism.ext hv
  subst h1 h2
  rfl

private theorem exists_isGrpPullback_factor {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂}
    [GrpObj G] [GrpObj G₁] [GrpObj G₂] {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} {φ₁ : G₁.left ⟶ G.left}
    {φ₂ : G₂.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G f₁ φ₁) (h₂ : IsGrpPullback G₂ G (g ≫ f₁) φ₂) :
    ∃ ψ : G₂.left ⟶ G₁.left, ψ ≫ φ₁ = φ₂ ∧ IsGrpPullback G₂ G₁ g ψ := by
  obtain ⟨hp₁, hm₁⟩ := h₁
  obtain ⟨hp₂, hm₂⟩ := h₂
  have hw : φ₂ ≫ G.hom = (G₂.hom ≫ g) ≫ f₁ := by rw [hp₂.w]; simp
  refine ⟨hp₁.lift φ₂ (G₂.hom ≫ g) hw, hp₁.lift_fst _ _ _, ?_, ?_⟩
  · refine IsPullback.of_right ?_ (hp₁.lift_snd _ _ _) hp₁
    rw [hp₁.lift_fst]
    exact hp₂
  · intro T x y x₀ y₀ hx hy
    apply hp₁.hom_ext
    · have ex : (x₀.left ≫ φ₁) ≫ G.hom = (T.hom ≫ g) ≫ f₁ := by
        rw [Category.assoc, hp₁.w, ← Category.assoc, Over.w x₀]; rfl
      have ey : (y₀.left ≫ φ₁) ≫ G.hom = (T.hom ≫ g) ≫ f₁ := by
        rw [Category.assoc, hp₁.w, ← Category.assoc, Over.w y₀]; rfl
      have fx : (x.left ≫ φ₂) ≫ G.hom = T.hom ≫ g ≫ f₁ := by
        rw [Category.assoc, hp₂.w, ← Category.assoc, Over.w x]
      have fy : (y.left ≫ φ₂) ≫ G.hom = T.hom ≫ g ≫ f₁ := by
        rw [Category.assoc, hp₂.w, ← Category.assoc, Over.w y]
      have A := hm₁ (Over.mk (T.hom ≫ g)) x₀ y₀ (Over.homMk (x₀.left ≫ φ₁) ex) (Over.homMk (y₀.left ≫ φ₁) ey) rfl rfl
      have B := hm₂ T x y (Over.homMk (x.left ≫ φ₂) fx) (Over.homMk (y.left ≫ φ₂) fy) rfl rfl
      have C := mul_left_congr_of_base_eq (Category.assoc T.hom g f₁) (Over.homMk (x₀.left ≫ φ₁) ex)
        (Over.homMk (y₀.left ≫ φ₁) ey) (Over.homMk (x.left ≫ φ₂) fx) (Over.homMk (y.left ≫ φ₂) fy)
        (by simp [hx, hp₁.lift_fst]) (by simp [hy, hp₁.lift_fst])
      rw [← A, C, B, Category.assoc, hp₁.lift_fst]
    · rw [Over.w (x₀ * y₀), Category.assoc, hp₁.lift_snd, ← Category.assoc, Over.w (x * y)]
      rfl

private theorem isGrpPullback_comp' {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂}
    [GrpObj G] [GrpObj G₁] [GrpObj G₂] {f : S₁ ⟶ S} {g : S₂ ⟶ S₁} {φ : G₁.left ⟶ G.left}
    {ψ : G₂.left ⟶ G₁.left} (h₂ : IsGrpPullback G₂ G₁ g ψ) (h₁ : IsGrpPullback G₁ G f φ) :
    IsGrpPullback G₂ G (g ≫ f) (ψ ≫ φ) := by
  obtain ⟨hp₁, hm₁⟩ := h₁
  obtain ⟨hp₂, hm₂⟩ := h₂
  refine ⟨hp₂.paste_horiz hp₁, ?_⟩
  intro T x y x₀ y₀ hx hy
  have ex : (x.left ≫ ψ) ≫ G₁.hom = T.hom ≫ g := by
    rw [Category.assoc, hp₂.w, ← Category.assoc, Over.w x]
  have ey : (y.left ≫ ψ) ≫ G₁.hom = T.hom ≫ g := by
    rw [Category.assoc, hp₂.w, ← Category.assoc, Over.w y]
  have ex' : ((x.left ≫ ψ) ≫ φ) ≫ G.hom = (T.hom ≫ g) ≫ f := by
    rw [Category.assoc, hp₁.w, ← Category.assoc, ex]
  have ey' : ((y.left ≫ ψ) ≫ φ) ≫ G.hom = (T.hom ≫ g) ≫ f := by
    rw [Category.assoc, hp₁.w, ← Category.assoc, ey]
  have A := hm₂ T x y (Over.homMk (x.left ≫ ψ) ex) (Over.homMk (y.left ≫ ψ) ey) rfl rfl
  have B := hm₁ (Over.mk (T.hom ≫ g)) (Over.homMk (x.left ≫ ψ) ex) (Over.homMk (y.left ≫ ψ) ey)
    (Over.homMk ((x.left ≫ ψ) ≫ φ) ex') (Over.homMk ((y.left ≫ ψ) ≫ φ) ey') rfl rfl
  have C := mul_left_congr_of_base_eq (Category.assoc T.hom g f).symm x₀ y₀ (Over.homMk ((x.left ≫ ψ) ≫ φ) ex')
    (Over.homMk ((y.left ≫ ψ) ≫ φ) ey') (by simp [hx]) (by simp [hy])
  rw [C, B, A, Category.assoc]

theorem kTriv_transfer {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂} [GrpObj G] [GrpObj G₁]
    [GrpObj G₂] {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} {φ₁ : G₁.left ⟶ G.left} {φ₂ : G₂.left ⟶ G.left} {L : LB G.left}
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} (hL : L.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB)
    (h₁ : IsGrpPullback G₁ G f₁ φ₁) (h₂ : IsGrpPullback G₂ G (g ≫ f₁) φ₂)
    (e₁ : LBIso L₁ (L.pull φ₁)) (e₂ : LBIso L₂ (L.pull φ₂)) (hK : Out.KTriv G₁ L₁) : Out.KTriv G₂ L₂ := by
  obtain ⟨ψ, hψ, hG⟩ := exists_isGrpPullback_factor h₁ h₂
  have e₃ : LBIso (L₁.pull ψ) (L.pull φ₂) := GlobalTheory.GenSpread.lbIso_pull_of_lbIso e₁ ψ hψ.symm
  have hψL : (L₁.pull ψ).IsLB := pull_isLB hL₁ ψ
  have e₄ : LBIso L₂ (L₁.pull ψ) := LBIso.trans hL₂ (pull_isLB hL φ₂) hψL e₂ (LBIso.symm e₃)
  obtain ⟨w, hw⟩ := e₄
  exact kTriv_pull hG hL₁ hL₂ ((isGen_iff w).1 hw) hK


private theorem exists_open_kTriv_restrict_of_kTriv_fibre {S S' : Scheme.{0}} [IsLocallyNoetherian S] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hG : IsAbelianScheme G) (hA : Out.RelAmple G L) (h : IsGrpPullback G' G f φ) (e : LBIso L' (L.pull φ))
    (hK : Out.KTriv G' L') (q : S') :
    ∃ U : S.Opens, f q ∈ U ∧ Out.KTriv ((Over.pullback U.ι).obj G) (L.pull (pullback.fst G.hom U.ι)) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hfqV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f q)) isOpen_univ
  replace hV : IsAffineOpen V := hV
  haveI : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hAp : IsGrpPullback ((Over.pullback hV.fromSpec).obj G) G hV.fromSpec (pullback.fst G.hom hV.fromSpec) :=
    isGrpPullback_pullback G hV.fromSpec
  have hLA : (L.pull (pullback.fst G.hom hV.fromSpec)).IsLB := pull_isLB hL _
  obtain ⟨hAb, hAamp, -⟩ := GlobalTheory.pol_pull S _ G ((Over.pullback hV.fromSpec).obj G) hV.fromSpec _ L _ hL hLA hG hAp
    (PolBaseChange.lbIso_refl hLA)
  have hrange : Set.range (S'.fromSpecResidueField q ≫ f) ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨z, rfl⟩
    rw [hV.range_fromSpec]
    simpa using hfqV
  obtain ⟨m, hm⟩ : ∃ m : Spec (S'.residueField q) ⟶ Spec Γ(S, V),
      m ≫ hV.fromSpec = S'.fromSpecResidueField q ≫ f :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  have hx : spMap (Spec.preimage m).hom = m := Spec.map_preimage m
  have hpt : spMap (Spec.preimage m).hom ≫ hV.fromSpec = S'.fromSpecResidueField q ≫ f := by rw [hx, hm]
  have h₂ := IsGrpPullback.congr (isGrpPullback_comp'
    (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G) (spMap (Spec.preimage m).hom)) hAp) hpt rfl
  have hK₀ := kTriv_transfer hL hL' (pull_isLB hLA _) h h₂ e
    (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hL _ rfl)) hK
  obtain ⟨r, hr, hsp⟩ := GlobalTheory.T.exists_basicOpen_kTriv_of_fibre Γ(S, V) ((Over.pullback hV.fromSpec).obj G)
    (L.pull (pullback.fst G.hom hV.fromSpec)) (S'.residueField q) (Spec.preimage m).hom
    ((Over.pullback (spMap (Spec.preimage m).hom)).obj ((Over.pullback hV.fromSpec).obj G))
    (pullback.fst ((Over.pullback hV.fromSpec).obj G).hom (spMap (Spec.preimage m).hom)) hAb hLA (hAamp hA)
    (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G) (spMap (Spec.preimage m).hom)) hK₀
  have hmem : f q ∈ S.basicOpen r := by
    let z : Spec (S'.residueField q) := IsLocalRing.closedPoint (S'.residueField q)
    have e1 : (m ≫ hV.fromSpec) z = (S'.fromSpecResidueField q ≫ f) z := by rw [hm]
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at e1
    rw [← e1]
    show m z ∈ hV.fromSpec ⁻¹ᵁ S.basicOpen r
    rw [hV.fromSpec_preimage_basicOpen]
    have hmz : m z = PrimeSpectrum.comap (Spec.preimage m).hom z :=
      (congrArg (fun k : Spec (S'.residueField q) ⟶ Spec Γ(S, V) => k z) (Spec.map_preimage m)).symm
    rw [hmz]
    show r ∉ (PrimeSpectrum.comap (Spec.preimage m).hom z).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    intro hin
    apply hr
    have : ¬ IsUnit ((Spec.preimage m).hom r) := (IsLocalRing.mem_maximalIdeal _).1 hin
    simpa using this
  have hU := hV.basicOpen r
  refine ⟨S.basicOpen r, hmem, ?_⟩
  have hunit : IsUnit ((S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom r) :=
    S.toRingedSpace.isUnit_res_basicOpen r
  have hK' := hsp Γ(S, S.basicOpen r) (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom
    ((Over.pullback (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom)).obj
      ((Over.pullback hV.fromSpec).obj G))
    (pullback.fst ((Over.pullback hV.fromSpec).obj G).hom (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom))
    hunit (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G) (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom))
  have h₁' := isGrpPullback_comp' (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G)
    (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom)) hAp
  have hιeq : (S.basicOpen r).ι = hU.isoSpec.hom ≫
      (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom ≫ hV.fromSpec) := by
    rw [show spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom ≫ hV.fromSpec = hU.fromSpec from
      hV.map_fromSpec hU (homOfLE (S.basicOpen_le r)).op, hU.isoSpec_hom_fromSpec]
  have h₂' := IsGrpPullback.congr (isGrpPullback_pullback G (S.basicOpen r).ι) hιeq rfl
  exact kTriv_transfer hL (pull_isLB hLA _) (pull_isLB hL _) h₁' h₂'
    (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hL _ rfl)) (PolBaseChange.lbIso_refl (pull_isLB hL _)) hK'

theorem exists_open {S S' : Scheme.{0}} [IsLocallyNoetherian S] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hG : IsAbelianScheme G) (hA : Out.RelAmple G L) (h : IsGrpPullback G' G f φ) (e : LBIso L' (L.pull φ))
    (hK : Out.KTriv G' L') (q : S') :
    ∃ U : S.Opens, f q ∈ U ∧ Out.KTriv ((Over.pullback U.ι).obj G) (L.pull (pullback.fst G.hom U.ι)) := exists_open_kTriv_restrict_of_kTriv_fibre hL hL' hG hA h e hK q

theorem kTriv_of_forall_point : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (_ : SABMap t' t f), p ∈ Set.range f ∧ Out.KTriv t'.G t'.PP.L) → Out.KTriv t.G t.PP.L := by
  intro hLaws E _ _ _ H S _ t hP hA h
  haveI : IsProper t.G.hom := hP
  have hAb : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hL : t.PP.L.IsLB := t.PP.isLB
  have hU : ∀ p : S, ∃ U : S.Opens, p ∈ U ∧
      Out.KTriv ((Over.pullback U.ι).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom U.ι)) := by
    intro p
    obtain ⟨S', f, t', ⟨cm, cart, -, -, lin⟩, ⟨q, rfl⟩, hk⟩ := h p
    obtain ⟨w, hw, -⟩ := lin
    exact exists_open hL t'.PP.isLB hAb hA cart ⟨w, hw⟩ hk q
  choose U hpU hKU using hU
  letI : ∀ p : S, GrpObj ((Over.pullback (U p).ι).obj t.G) := fun p =>
    letI : (Over.pullback (U p).ι).Monoidal := (Over.instBraidedPullback (f := (U p).ι)).toMonoidal
    Functor.grpObjObj (F := Over.pullback (U p).ι)
  exact GlobalTheory.CoverGlue.kTriv_of_cover S S U t.G (fun p => (Over.pullback (U p).ι).obj t.G)
    (fun p => pullback.fst t.G.hom (U p).ι)
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hpU x⟩)
    (fun p => isGrpPullback_pullback t.G (U p).ι) t.PP.L (fun p => t.PP.L.pull (pullback.fst t.G.hom (U p).ι))
    hL (fun p => pull_isLB hL _) (fun p => PolBaseChange.lbIso_refl (pull_isLB hL _)) hAb
    (fun p => (GlobalTheory.pol_pull S (U p).toScheme t.G _ (U p).ι _ t.PP.L _ hL (pull_isLB hL _) hAb
      (isGrpPullback_pullback t.G (U p).ι) (PolBaseChange.lbIso_refl (pull_isLB hL _))).1) hKU

end GlobalTheory.KTrivGlob
end
end
