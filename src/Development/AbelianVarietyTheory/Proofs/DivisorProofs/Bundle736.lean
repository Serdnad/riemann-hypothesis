module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaceSubMid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle699
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle700
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle701
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

namespace GlobalTheory.EtC.KumPic.Cobd

theorem res_zero {F : Shv ℤ} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem res_id {F : Shv ℤ} {U : Scheme.{0}} (s : Sec F U) : Sec.res (𝟙 U) s = s := by simp [Sec.res]

theorem res_res {F : Shv ℤ} {W V U : Scheme.{0}} (g : V ⟶ U) (g' : W ⟶ V) (s : Sec F U) :
    Sec.res g' (Sec.res g s) = Sec.res (g' ≫ g) s := by simp [Sec.res]

theorem umap_id {U : Scheme.{0}} (b : (Γ(U, ⊤))ˣ) : Units.map (𝟙 U : U ⟶ U).appTop.hom.toMonoidHom b = b := by
  ext; simp

theorem umap_comp {W V U : Scheme.{0}} (g : V ⟶ U) (g' : W ⟶ V) (b : (Γ(U, ⊤))ˣ) :
    Units.map (g' ≫ g).appTop.hom.toMonoidHom b =
      Units.map g'.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom b) := by
  ext; simp; rfl

theorem ev_sub {E : Spc} {I : Cx ℤ} {n : ℤ} (a b : Cochain ((chains ℤ).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (a - b) p s h U x = ev a p s h U x - ev b p s h U x := map_sub (CupSpec.evHom I n p s h U x) a b

theorem ev_comp {E : Spc} {L M : Cx ℤ} {n₁ n₂ n : ℤ} (a : Cochain ((chains ℤ).obj E) L n₁) (b : Cochain L M n₂)
    (hn : n₁ + n₂ = n) (p : ℕ) (t s : ℤ) (ht : -(p : ℤ) + n₁ = t) (hs : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (a.comp b hn) p s hs U x = Sec.map (b.v t s (by omega)) (ev a p t ht U x) := by
  rw [CupSpec.ev_def, CupSpec.ev_def, Cochain.comp_v a b hn (-(p : ℤ)) t s ht (by omega)]
  rfl

theorem sglZ (C : Shv ℤ) (k : ℤ) (hk : k ≠ 0) : IsZero ((sgl C).X k) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 C k hk

theorem face_two {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 2 = x.sub 0 1 (by omega) := by
  have e : (SimplexCategory.δ (2 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
      SimplexCategory.subinterval 0 1 (by omega) :=
    CupSpec.hom_ext_val _ _ fun v => by
      rw [CupSpec.δ_val, CupSpec.sub_val]; have := v.2; simp; omega
  show (E.map (SimplexCategory.δ (2 : Fin 3)).op).app (op U) x = _
  rw [e]; rfl

theorem face_zero {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 0 = x.sub 1 1 (by omega) := by
  have e : (SimplexCategory.δ (0 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
      SimplexCategory.subinterval 1 1 (by omega) :=
    CupSpec.hom_ext_val _ _ fun v => by
      rw [CupSpec.δ_val, CupSpec.sub_val]; simp
  show (E.map (SimplexCategory.δ (0 : Fin 3)).op).app (op U) x = _
  rw [e]; rfl

theorem mkiff {E : Spc} {I : Cx ℤ} (a b : Cocycle ((chains ℤ).obj E) I 2) :
    CohomologyClass.mk a = CohomologyClass.mk b ↔ ∃ w : Cochain _ I 1, δ 1 2 w = a.1 - b.1 := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)]
  rfl

theorem sep_zero {F : Shv ℤ} {U : Scheme.{0}} (s : Sec F U) (h : Loc U fun _ g => Sec.res g s = 0) : s = 0 := by
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ F U).1 s 0 ?_
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => (hP V g hg).trans (res_zero g).symm⟩

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem isUnit_of_sx {q : ℕ} {E : Spc} (hE : Inv q E) {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    IsUnit (q : Γ(U, ⊤)) :=
  hE U ⟨x.sub 0 0 (by omega)⟩

theorem eta_unique (q : ℕ) [NeZero q] (φ : Gm ⟶ (res ℤ (twZ q)).X 0) {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤)))
    (b : (Γ(U, ⊤))ˣ) (η η' : Sec ((res ℤ (twZ q)).X 0) U)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b →
      Sec.res g η = dv q φ V v)
    (h' : ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b →
      Sec.res g η' = dv q φ V v) : η = η' :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ _ U).1 η η' (loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.2.2 hq b)
    fun V g ⟨v, hv⟩ => (h V g v hv).trans (h' V g v hv).symm)

def thF (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res ℤ (twZ q)).X s) U
  | 1, s, h, U, x => Sec.map ((res ℤ (twZ q)).XIsoOfEq (show (0 : ℤ) = s by omega)).hom (η U x)
  | _, _, _, _, _ => 0

theorem thF_zero (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U) (s : ℤ)
    (h : -((0 : ℕ) : ℤ) + 1 = s) (U : Scheme.{0}) (x : Sx E 0 U) : thF q η 0 s h U x = 0 := rfl

theorem thF_two (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U) (p : ℕ) (s : ℤ)
    (h : -((p + 2 : ℕ) : ℤ) + 1 = s) (U : Scheme.{0}) (x : Sx E (p + 2) U) : thF q η (p + 2) s h U x = 0 := rfl

theorem thF_one (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U)
    (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0}) (x : Sx E 1 U) : thF q η 1 0 h U x = η U x := by
  simp [thF, Sec.map]

theorem thF_nat (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U)
    (hη : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (η U x) = η V (x.res g)) :
    ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
      Sec.res g (thF q η p s h U x) = thF q η p s h V (x.res g) := by
  intro p s h V U g x
  match p with
  | 0 => rw [thF_zero, thF_zero, res_zero]
  | 1 =>
    obtain rfl : s = 0 := by omega
    rw [thF_one, thF_one, hη]
  | p + 2 => rw [thF_two, thF_two, res_zero]

theorem thF_one' (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U)
    (h : -((0 + 1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0}) (x : Sx E (0 + 1) U) : thF q η (0 + 1) 0 h U x = η U x :=
  thF_one q η h U x

theorem thF_two' (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U)
    (h : -((1 + 1 : ℕ) : ℤ) + 1 = -1) (U : Scheme.{0}) (x : Sx E (1 + 1) U) : thF q η (1 + 1) (-1) h U x = 0 := rfl

theorem smap_sub {F G : Shv ℤ} (f : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map f (a - b) = Sec.map f a - Sec.map f b := map_sub _ _ _

theorem cobd : ∀ (q : ℕ) [NeZero q] (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → ∀ (φ : Gm ⟶ (res ℤ (twZ q)).X 0), (∀ (U : Scheme.{0}) (b : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) → ∃ η : Sec ((res ℤ (twZ q)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b → Sec.res g η = dv q φ V v) → ∀ (C : Shv ℤ) (a : Cocycle ((chains ℤ).obj E) (sgl C) 1) (w : Cocycle (sgl C) (res ℤ (twZ q)) 1), (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → Sec.map (w.1.v 0 1 (zero_add 1)) (ev a.1 1 0 (by simp) U x) = Sec.map ((res ℤ (twZ q)).d 0 1) (Sec.map φ (unitSec v))) → CohomologyClass.mk (zcomp a w rfl) = restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) := by
  intro q _ E L hE φ hφ C a w hw
  obtain ⟨γ, hγ, hγ0, hγ1, hγ2⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).1 L hE
  obtain ⟨β, hβ⟩ := SemiMap.image_exists (restrMap (Int.castRingHom (ZMod q)) (tw q 1)) E 2 γ
  have hβc : restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) = CohomologyClass.mk β := by
    rw [← hγ]; exact SemiMap.op_spec _ E 2 γ β hβ
  rw [hβc]
  have h2 : (1 : ℤ) + 1 = 2 := by norm_num
  change CohomologyClass.mk (zcomp a w h2) = _
  choose η hη using fun (U : Scheme.{0}) (x : Sx E 1 U) => hφ U (lineUnit L x) (isUnit_of_sx hE x)
  have ηnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (η U x) = η V (x.res g) := by
    intro V U g x
    refine eta_unique q φ (isUnit_of_sx hE (x.res g)) (lineUnit L (x.res g)) _ _ (fun V' g' v hv => ?_)
      (hη V (x.res g))
    rw [res_res]
    exact hη U x V' (g' ≫ g) v (by rw [umap_comp, ← PicSpec.lineUnit_res]; exact hv)
  have ηroot : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → η U x = dv q φ U v := by
    intro U x v hv
    have := hη U x U (𝟙 U) v (by rw [umap_id]; exact hv)
    rwa [res_id] at this
  obtain ⟨θ, hθ⟩ := CupSpec.ev_exists (E := E) (I := res ℤ (twZ q)) (n := 1) (thF q η) (thF_nat q η ηnat)
  have hzc : (zcomp a w h2).1 = a.1.comp w.1 h2 := rfl
  have key1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev (δ 1 2 θ - ((zcomp a w h2).1 - β.1)) 1 1 (by simp) U x = 0 := by
    intro U x v hv
    rw [ev_sub, ev_sub, CupSpec.ev_δ_succ (by norm_num) θ U 0 0 1 (by simp) (by simp) x, hzc,
      ev_comp a.1 w.1 h2 1 0 1 (by simp) (by simp) U x, hw U x v hv, hβ, hγ1 U x v hv,
      ← (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).comm]
    simp only [hθ, thF_zero, thF_one', ηroot U x v hv, dv, smap_sub, smul_zero, Finset.sum_const_zero, add_zero]
    abel
  have key2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v u : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      u ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev (δ 1 2 θ - ((zcomp a w h2).1 - β.1)) 2 0 (by simp) U x = 0 := by
    intro U x v u hv hu
    rw [ev_sub, ev_sub, CupSpec.ev_δ_succ (by norm_num) θ U 1 (-1) 0 (by simp) (by simp) x, hzc,
      ev_comp a.1 w.1 h2 2 (-1) 0 (by simp) (by simp) U x,
      PicSpec.sec_eq_zero (sglZ C (-1) (by omega)) (ev a.1 2 (-1) _ U x), PicSpec.sec_map_zero, hβ,
      hγ2 U x v u hv hu, Fin.sum_univ_three]
    simp only [hθ, thF_two', thF_one, PicSpec.sec_map_zero]
    have e2 : η U (x.face 2) = dv q φ U v := ηroot U _ v (by rw [face_two]; exact hv)
    have e0 : η U (x.face 0) = dv q φ U u := ηroot U _ u (by rw [face_zero]; exact hu)
    have e1 : η U (x.face 1) = dv q φ U (v * u) := ηroot U _ (v * u) (by
      rw [PicSpec.lineUnit_face, face_two, face_zero, mul_pow, hv, hu, mul_comm])
    rw [e0, e1, e2]
    have hn2 : (2 : ℤ).negOnePow = 1 := by decide
    simp only [dv, PicSpec.unitSec_mul, PicSpec.sec_map_add, smap_sub, map_add (f := _), map_sub, hn2, one_smul, Fin.val_zero,
      Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, neg_smul]
    abel
  refine (mkiff _ _).2 ⟨θ, sub_eq_zero.mp (CupSpec.ev_ext _ _ fun p s h U x => ?_)⟩
  rw [CupSpec.ev_zero]
  match p with
  | 0 =>
    obtain rfl : s = 2 := by omega
    rw [ev_sub, ev_sub, CupSpec.ev_δ_zero (by norm_num) θ U 1 2 (by simp) h x, hθ, thF_zero, PicSpec.sec_map_zero, hzc,
      ev_comp a.1 w.1 h2 0 1 2 (by simp) h U x, PicSpec.sec_eq_zero (sglZ C 1 (by omega)) (ev a.1 0 1 _ U x),
      PicSpec.sec_map_zero, hβ, hγ0, map_zero]
    simp
  | 1 =>
    obtain rfl : s = 1 := by omega
    apply sep_zero
    refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.2.2 (isUnit_of_sx hE x) (lineUnit L x)) fun V g ⟨v, hv⟩ => ?_
    rw [CupSpec.ev_res]
    exact key1 V (x.res g) v (by rw [PicSpec.lineUnit_res]; exact hv)
  | 2 =>
    obtain rfl : s = 0 := by omega
    apply sep_zero
    refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.2.2 (isUnit_of_sx hE x) (lineUnit L (x.sub 0 1 (by omega))))
      fun V g ⟨v, hv⟩ => ?_
    rw [CupSpec.ev_res]
    apply sep_zero
    refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.2 (isUnit_of_sx hE (x.res g)) (lineUnit L ((x.res g).sub 1 1 (by omega))))
      fun V' g' ⟨u, hu⟩ => ?_
    rw [CupSpec.ev_res]
    refine key2 V' ((x.res g).res g') (Units.map g'.appTop.hom.toMonoidHom v) u ?_ ?_
    · rw [CupSpec.sub_res, CupSpec.sub_res, PicSpec.lineUnit_res, PicSpec.lineUnit_res, ← hv, map_pow]
    · rw [CupSpec.sub_res, PicSpec.lineUnit_res]; exact hu
  | p + 3 =>
    exact PicSpec.sec_eq_zero (PicSpec.res_isZero _ s (by omega)) _

end GlobalTheory.EtC.KumPic.Cobd

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem finite_piTensorProduct_const (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Module.Finite A A']
    (ι : Type) [Fintype ι] : Module.Finite A (PiTensorProduct A fun _ : ι => A') := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := A')
  refine ⟨⟨Finset.univ.image (fun r : ι → S => PiTensorProduct.tprod A (fun i => (r i : A'))), ?_⟩⟩
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  have hm : ∀ i, m i ∈ Submodule.span A (S : Set A') := fun i => hS ▸ Submodule.mem_top
  choose c hc using fun i => (Submodule.mem_span_finset).1 (hm i)
  have hm' : m = fun i => ∑ s ∈ S, c i s • s := funext fun i => ((hc i).2).symm
  rw [hm', MultilinearMap.map_sum_finset]
  refine Submodule.sum_mem _ fun r hr => ?_
  rw [MultilinearMap.map_smul_univ]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [Finset.coe_image]
  refine ⟨fun i => ⟨r i, Fintype.mem_piFinset.1 hr i⟩, by simp, rfl⟩

theorem level_vanish : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 2 ≤ s → s < n →
  Subsingleton (Ht q (disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌))) s i) := by
  intro q _ n hyp A _ _ hSH hq A' _ _ hfin k s i hs hsn
  obtain ⟨_, e, -, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  have hT := GlobalTheory.T.tateTwistCohomology_laurent_vanishing_finite_algebra q n hyp A hSH hq (PiTensorProduct A fun _ : Fin (k + 1) => A')
    (finite_piTensorProduct_const A A' (Fin (k + 1))) s i hs hsn
  haveI : Subsingleton (Ht q (disc.obj (yoneda.obj (Spec (CommRingCat.of
    (LaurentPolynomial (PiTensorProduct A fun _ : Fin (k + 1) => A')))))) s i) := hT
  let f := disc.mapIso e
  have inj : Function.Injective (pull (ZMod q) f.hom (tw q i) s) := fun x y h => by
    have h' := congrArg (pull (ZMod q) f.inv (tw q i) s) h
    rwa [← pull_comp, ← pull_comp, Iso.inv_hom_id, pull_id, pull_id] at h'
  exact inj.subsingleton

end GlobalTheory.EtC.GmStep
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

namespace GlobalTheory.Obs.BC

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]

theorem isAffineHom_of_isPullback {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) : IsAffineHom pr :=
  MorphismProperty.of_isPullback hp.flip inferInstance

theorem res_bijective (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) {X₀ X₁ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀} (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    [IsAffineHom pr] : Function.Bijective (CoefMap.restrict (OAff s₁) (preAff pr)).pull1 :=
  have H := GlobalTheory.T.affineOpensPreimage_baseChange_isBasis X₀ X₁ pr (GlobalTheory.T.exists_open_preimage_eq_baseChange_sqZero_augmentation R₀ R₁ q hq X₀ X₁ s₀ s₁ pr hp)
  GlobalTheory.T.restrict_structureSheaf_affineBasis_pull1_bijective R₁ X₁ s₁ _ (preAff pr) H.1 H.2

theorem tens_bijective {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) [IsAffineHom pr] :
    Function.Bijective (tensCoef hp.w).pull1 := by
  exact GlobalTheory.T.natural_bijective_coefficients_pull1_bijective R₁ _ _ _ _ (tensCoef hp.w).naturality (tensCoef hp.w).smul fun U ↦ GlobalTheory.T.baseChangeTensorSectionsHom_bijective R₀ R₁ X₀ X₁ s₀ s₁ pr hp U.unop _

def trEquiv (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) (X₀ X₁ : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) :
    CatCoh.H1 (OAff s₁) ≃+ CatCoh.H1 (ext R₁ (OAff s₀)) :=
  haveI := isAffineHom_of_isPullback hp
  (AddEquiv.ofBijective (CoefMap.restrict (OAff s₁) (preAff pr)).pull1 (res_bijective q hq hp)).trans
    (AddEquiv.ofBijective (tensCoef hp.w).pull1 (tens_bijective hp)).symm

theorem tens_trEquiv (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) {X₀ X₁ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀} (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    [IsAffineHom pr] (c : CatCoh.H1 (OAff s₁)) :
    (tensCoef hp.w).pull1 (trEquiv q hq X₀ X₁ s₀ s₁ pr hp c) = (CoefMap.restrict (OAff s₁) (preAff pr)).pull1 c :=
  (AddEquiv.ofBijective (tensCoef hp.w).pull1 (tens_bijective hp)).apply_symm_apply _

section Compat

variable {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
  {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀} [IsAffineHom pr] [IsAffineHom pr']
  {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁} (e : f₁ ≫ pr = pr' ≫ f₀)

def pullBC (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) :
    CoefMap (RingHom.id R₁) (preAff pr ⋙ OAff s₁) (pairBC pr pr' e ⋙ OPair f₁ t₁) where
  G := pairSnd f₀
  α p := (pairPull h₁).α ((pairBC pr pr' e).obj p)
  naturality a b := (pairPull h₁).naturality ((pairBC pr pr' e).map a) b
  smul p r b := (pairPull h₁).smul ((pairBC pr pr' e).obj p) r b

def resBC : CoefMap (RingHom.id R₁) (preAff pr' ⋙ OAff t₁) (pairBC pr pr' e ⋙ OPair f₁ t₁) where
  G := pairFst f₀
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

end Compat

end GlobalTheory.Obs.BC

namespace GlobalTheory.Obs.BC

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]

theorem extendedCoefficients_pullback_compat (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0)
    {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
    (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀}
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) (e : f₁ ≫ pr = pr' ≫ f₀)
    (c : CatCoh.H1 (OAff s₁)) (c' : CatCoh.H1 (OAff t₁))
    (H : IsExtendedPullbackDegOne R₁ h₀ (trEquiv q hq X₀ X₁ s₀ s₁ pr hp c) (trEquiv q hq Y₀ Y₁ t₀ t₁ pr' hp' c')) :
    IsPullO h₁ c c' := by
  haveI := isAffineHom_of_isPullback hp
  haveI := isAffineHom_of_isPullback hp'
  have kd := tens_trEquiv q hq hp c
  have kd' := tens_trEquiv q hq hp' c'
  let Φ := CoefMap.restrict (OPair f₁ t₁) (pairBC pr pr' e)
  have inj : Function.Injective Φ.pull1 := by
    intro x x' hx
    obtain ⟨y, rfl⟩ := (pairRes_bijective f₁ t₁).1.2 x
    obtain ⟨y', rfl⟩ := (pairRes_bijective f₁ t₁).1.2 x'
    have HH := GlobalTheory.T.affinePairPreimage_baseChange_fst_isBasis X₀ X₁ Y₀ Y₁ pr pr' f₀ f₁ e (GlobalTheory.T.exists_open_preimage_eq_baseChange_sqZero_augmentation R₀ R₁ q hq Y₀ Y₁ t₀ t₁ pr' hp')
    have B := GlobalTheory.T.restrict_structureSheaf_affineBasis_pull1_bijective R₁ Y₁ t₁ _ (pairBC pr pr' e ⋙ pairFst f₁) HH.1 HH.2
    have k : ∀ z, Φ.pull1 ((pairRes f₁ t₁).pull1 z) =
        (CoefMap.restrict (OAff t₁) (pairBC pr pr' e ⋙ pairFst f₁)).pull1 z := by
      intro z; obtain ⟨z, rfl⟩ := H1.mk_surjective _ z; rfl
    rw [k, k] at hx
    rw [B.1 hx]
  have k1 : Φ.pull1 ((pairPull h₁).pull1 c) = (tensPair hp'.w e).pull1 ((extMap R₁ (pairPull h₀)).pull1
      (trEquiv q hq X₀ X₁ s₀ s₁ pr hp c)) := by
    have a1 : Φ.pull1 ((pairPull h₁).pull1 c) =
        (pullBC e h₁).pull1 ((CoefMap.restrict (OAff s₁) (preAff pr)).pull1 c) := by
      obtain ⟨z, rfl⟩ := H1.mk_surjective _ c; rfl
    rw [a1, ← kd, ← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    refine CoefMap.pullCohomologyOne_eq_of_natTrans ((tensCoef hp.w).comp (pullBC e h₁))
      ((extMap R₁ (pairPull h₀)).comp (tensPair hp'.w e)) (𝟙 (pairSnd f₀)) (fun p b ↦ ?_) _
    refine (congrArg _ (mp_id (ext R₁ (OAff s₀)) _ b)).trans ?_
    exact GlobalTheory.T.baseChange_coefficient_comparison_comm_pairPullback R₀ R₁ X₀ X₁ Y₀ Y₁ s₀ s₁ pr t₀ t₁ pr' hp.w hp'.w f₀ f₁ h₀ h₁ e p b
  have k2 : Φ.pull1 ((pairRes f₁ t₁).pull1 c') = (tensPair hp'.w e).pull1 ((extMap R₁ (pairRes f₀ t₀)).pull1
      (trEquiv q hq Y₀ Y₁ t₀ t₁ pr' hp' c')) := by
    have a2 : Φ.pull1 ((pairRes f₁ t₁).pull1 c') =
        (resBC e).pull1 ((CoefMap.restrict (OAff t₁) (preAff pr')).pull1 c') := by
      obtain ⟨z, rfl⟩ := H1.mk_surjective _ c'; rfl
    rw [a2, ← kd', ← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    refine CoefMap.pullCohomologyOne_eq_of_natTrans ((tensCoef hp'.w).comp (resBC e))
      ((extMap R₁ (pairRes f₀ t₀)).comp (tensPair hp'.w e)) (𝟙 (pairFst f₀)) (fun p b ↦ ?_) _
    refine (congrArg _ (mp_id (ext R₁ (OAff t₀)) _ b)).trans ?_
    have hc : coefHom (pairRes f₀ t₀) p = AlgHom.id R₀ _ := AlgHom.ext fun _ ↦ rfl
    change (tensPair hp'.w e).α p (extHom R₁ (coefHom (pairRes f₀ t₀) p) b) = _
    rw [hc]
    exact congrArg ((tensPair hp'.w e).α p) (DFunLike.congr_fun Algebra.TensorProduct.map_id b)
  apply inj
  unfold IsExtendedPullbackDegOne at H
  rw [k1, k2, H]

end GlobalTheory.Obs.BC

theorem GlobalTheory.Obs.BC.extO1 : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0), ∃ e : ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → (GlobalTheory.CatCoh.H1 (OAff s₁) ≃+ GlobalTheory.CatCoh.H1 (ext R₁ (OAff s₀))), ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (Y₀ Y₁ : Scheme.{0}) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)), f₁ ≫ pr = pr' ≫ f₀ → ∀ c c', IsExtendedPullbackDegOne R₁ h₀ (e X₀ X₁ s₀ s₁ pr hp c) (e Y₀ Y₁ t₀ t₁ pr' hp' c') → IsPullO h₁ c c' :=
  fun _ _ _ _ _ q hq ↦ ⟨GlobalTheory.Obs.BC.trEquiv q hq, fun _ _ _ _ _ hp _ _ _ _ _ hp' _ _ h₀ h₁ e c c' H ↦
    GlobalTheory.Obs.BC.extendedCoefficients_pullback_compat q hq hp hp' h₀ h₁ e c c' H⟩
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.weightTwoDerivativeEisensteinTerm_uniform_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (m : I → ℕ) (σ : ℂ) (r : ℝ), 0 ≤ σ.re → r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) → ∀ x : E, x ≠ 0 → ‖eTerm φ m σ z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(1 + σ.re)) := by
  first | exact @GlobalTheory.WeightTwoSum.Bound.eTerm_bound | exact GlobalTheory.WeightTwoSum.Bound.eTerm_bound | (intros; apply GlobalTheory.WeightTwoSum.Bound.eTerm_bound <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

theorem _root_.GlobalTheory.T.exists_local_unit_representatives_split_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)), Splits q → Over P q → ∃ R : Finset (P.adicCompletion E)ˣ, R.card + 1 = Ideal.absNorm q.asIdeal ∧ (∀ r ∈ R, Valued.v (r : P.adicCompletion E) = 1) ∧ ∀ y : (Af E)ˣ, (∀ P', Over P' q → Valued.v ((y : Af E) P') = 1) → ∃! r, r ∈ R ∧ LocIn 1 q (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) := by
  first | exact @GlobalTheory.CMVal.Euler.Resid.exists_representatives | exact GlobalTheory.CMVal.Euler.Resid.exists_representatives | (intros; apply GlobalTheory.CMVal.Euler.Resid.exists_representatives <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical


theorem _root_.GlobalTheory.T.mem_adelicSchwartzSpace_of_level_compact_schwartz : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (Φ : (Fin N → AF F) → ℂ), (∃ U : AddSubgroup (Fin N → AF F), IsOpen (U : Set (Fin N → AF F)) ∧ ∀ u ∈ U, inf u = 0 → ∀ x, Φ (x + u) = Φ x) → (∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ x, Φ x ≠ 0 → fin x ∈ K) → (∀ x, ∃ g : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = Φ (x + embR t)) → Φ ∈ GlobalTheory.WeilM.schA F (Fin N) := by
  first | exact @GlobalTheory.LevelSchwartz.mem_schA_of_level | exact GlobalTheory.LevelSchwartz.mem_schA_of_level | (intros; apply GlobalTheory.LevelSchwartz.mem_schA_of_level <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

theorem _root_.GlobalTheory.T.adelicSymplecticForm_realOneParamLine_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F → ∀ M : ℝ →+ VA F N, IsRealLine M → ∀ t s : ℝ, symV (M t) (M s) = 0 := by
  first | exact @GlobalTheory.ThetaTransform.symV_realLine_eq_zero | exact GlobalTheory.ThetaTransform.symV_realLine_eq_zero | (intros; apply GlobalTheory.ThetaTransform.symV_realLine_eq_zero <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical


theorem _root_.GlobalTheory.T.hasDerivAt_inverseThetaTransform_heisenberg_oneParam : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ (f f' : VA F N → ℂ) (C : ℝ), Continuous f → Continuous f' → (∀ w, ‖f w‖ ≤ C) → (∀ w, ‖f' w‖ ≤ C) → ∀ M : ℝ →+ VA F N, Continuous M → (∀ w s, HasDerivAt (fun t : ℝ => heisV ψ (M t) f w) (heisV ψ (M s) f' w) s) → ∀ x, HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0 := by
  first | exact @GlobalTheory.ThetaTransform.hasDerivAt_invV_heisV | exact GlobalTheory.ThetaTransform.hasDerivAt_invV_heisV | (intros; apply GlobalTheory.ThetaTransform.hasDerivAt_invV_heisV <;> assumption)
end
