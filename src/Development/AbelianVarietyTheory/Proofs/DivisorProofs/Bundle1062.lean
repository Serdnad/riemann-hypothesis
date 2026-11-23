module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem gm_eq_stalkMap {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)ˣ) :
    gm r z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm (𝟙 X) (r z) U a) := by
  apply Units.ext
  rw [gm_val r z U h, Units.coe_map, gm_val (𝟙 X) (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r U z h a.val).symm

theorem pull_isLB_of_isOn : ∀ (X Z : Scheme.{0}) (W : X.Opens) (L : LB X) (r : Z ⟶ X), IsOn W L → (∀ z, r z ∈ W) →
    (L.pull r).IsLB := by
  intro X Z W L r hL hr
  have coc : ∀ (z : Z) (a b c : L.ι), r z ∈ L.U a → r z ∈ L.U b → r z ∈ L.U c →
      gm r z _ (L.g a b) * gm r z _ (L.g b c) = gm r z _ (L.g a c) := by
    intro z a b c ha hb hc
    rw [gm_eq_stalkMap r z (L.U a ⊓ L.U b) ⟨ha, hb⟩, gm_eq_stalkMap r z (L.U b ⊓ L.U c) ⟨hb, hc⟩,
      gm_eq_stalkMap r z (L.U a ⊓ L.U c) ⟨ha, hc⟩, ← map_mul,
      hL.coc (r z) a b c ha hb hc]
  refine ⟨?_, ?_, ?_⟩
  · refine top_le_iff.1 fun z _ => ?_
    obtain ⟨a, ha⟩ := hL.cov (r z) (hr z)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => a, mem_pull.2 ha⟩
  · intro J
    refine unit_ext fun z hz => ?_
    rw [gm_res (𝟙 Z) z _ hz, map_one, gm_pull_g L r (𝟙 Z) z J J hz hz, Category.id_comp]
    have hJ := mem_pull.1 hz
    exact mul_eq_left.1 (coc z _ _ _ hJ hJ hJ)
  · intro I J K
    refine unit_ext fun z hz => ?_
    rw [map_mul, gm_res (𝟙 Z) z _ hz, gm_res (𝟙 Z) z _ hz, gm_res (𝟙 Z) z _ hz, gm_pull_g L r (𝟙 Z) z I J hz.1.1 hz.1.2,
      gm_pull_g L r (𝟙 Z) z J K hz.1.2 hz.2, gm_pull_g L r (𝟙 Z) z I K hz.1.1 hz.2, Category.id_comp]
    exact coc z _ _ _ (mem_pull.1 hz.1.1) (mem_pull.1 hz.1.2) (mem_pull.1 hz.2)

end GlobalTheory.PicGlue
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PicGlue

variable {X : Scheme.{0}} {Ix : Type}

def sigmaGlue (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k))
    (hL : ∀ i, IsOn (W i) (L i)) : LB X :=
  ⟨Σ i, (L i).ι, fun p ↦ (L p.1).U p.2,
    fun p q ↦ res (le_inf (inf_le_inf ((hL p.1).le p.2) ((hL q.1).le q.2)) le_rfl) (w p.1 q.1 p.2 q.2)⟩

theorem gm_sigmaGlue_g (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k))
    (hL : ∀ i, IsOn (W i) (L i)) (x : X) (p q : (sigmaGlue W L w hL).ι)
    (hp : x ∈ (L p.1).U p.2) (hq : x ∈ (L q.1).U q.2) :
    gm (𝟙 X) x _ ((sigmaGlue W L w hL).g p q) = gm (𝟙 X) x _ (w p.1 q.1 p.2 q.2) :=
  gm_res (𝟙 X) x _ (show x ∈ (L p.1).U p.2 ⊓ (L q.1).U q.2 from ⟨hp, hq⟩) _

theorem lb_glue : ∀ (X : Scheme.{0}) (Ix : Type) (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k)), (∀ x, ∃ i, x ∈ W i) → (∀ i, IsOn (W i) (L i)) → (∀ i k, IsoOn (W i ⊓ W k) (L i) (L k) (w i k)) → (∀ (i j k : Ix) (x : X) (a : (L i).ι) (b : (L j).ι) (c : (L k).ι), x ∈ (L i).U a → x ∈ (L j).U b → x ∈ (L k).U c → gm (𝟙 X) x _ (w i j a b) * gm (𝟙 X) x _ (w j k b c) = gm (𝟙 X) x _ (w i k a c)) → ∃ N : LB X, N.IsLB ∧ ∀ i, ∃ v : Cmp (W i) N (L i), IsoOn (W i) N (L i) v := by
  intro X Ix W L w hW hL hiso hcoc
  have hdiag : ∀ i (a : (L i).ι) (x : X), x ∈ (L i).U a → gm (𝟙 X) x _ (w i i a a) = 1 :=
    fun i a x ha ↦ mul_eq_left.1 (hcoc i i i x a a a ha ha ha)
  have hgi : ∀ i (x : X) (b b' : (L i).ι), x ∈ (L i).U b → x ∈ (L i).U b' → x ∈ W i →
      gm (𝟙 X) x _ ((L i).g b b') = gm (𝟙 X) x _ (w i i b b') := by
    intro i x b b' hb hb' hx
    have h1 := hiso i i x ⟨hx, hx⟩ b b b b' hb hb hb hb'
    have h2 : gm (𝟙 X) x _ ((L i).g b b) = 1 := mul_eq_left.1 ((hL i).coc x b b b hb hb hb)
    rw [hdiag i b x hb, _root_.one_mul, h2, _root_.one_mul] at h1
    exact h1
  have hg := gm_sigmaGlue_g W L w hL
  refine ⟨sigmaGlue W L w hL, ⟨?_, ?_, ?_⟩, fun i ↦ ⟨fun p b ↦ res (le_inf (le_inf
    (inf_le_right.trans (inf_le_left.trans ((hL p.1).le p.2))) inf_le_left) inf_le_right) (w p.1 i p.2 b), ?_⟩⟩
  · refine eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ?_
    obtain ⟨i, hi⟩ := hW x
    obtain ⟨a, ha⟩ := (hL i).cov x hi
    exact ⟨⟨i, a⟩, ha⟩
  · intro p
    refine unit_ext fun x hx ↦ ?_
    rw [gm_res (𝟙 X) x _ hx, map_one, hg x p p hx hx, hdiag p.1 p.2 x hx]
  · intro p q r
    refine unit_ext fun x hx ↦ ?_
    rw [map_mul, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx,
      hg x p q hx.1.1 hx.1.2, hg x q r hx.1.2 hx.2, hg x p r hx.1.1 hx.2]
    exact hcoc _ _ _ x _ _ _ hx.1.1 hx.1.2 hx.2
  · intro x hx p p' b b' hp hp' hb hb'
    beta_reduce
    erw [gm_res (𝟙 X) x _ (show x ∈ W i ⊓ ((sigmaGlue W L w hL).U p ⊓ (L i).U b) from ⟨hx, hp, hb⟩),
      gm_res (𝟙 X) x _ (show x ∈ W i ⊓ ((sigmaGlue W L w hL).U p' ⊓ (L i).U b') from ⟨hx, hp', hb'⟩),
      hg x p p' hp hp', hgi i x b b' hb hb' hx, hcoc _ _ _ x _ _ _ hp hb hb', hcoc _ _ _ x _ _ _ hp hp' hb']

end GlobalTheory.PicGlue
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem isoOn_gm {X Z : Scheme.{0}} {W : X.Opens} {L M : LB X} {w : Cmp W L M} (hw : IsoOn W L M w) (r : Z ⟶ X)
    (y : Z) {a a' : L.ι} {b b' : M.ι} (h0 : r y ∈ W) (ha : r y ∈ L.U a) (ha' : r y ∈ L.U a') (hb : r y ∈ M.U b)
    (hb' : r y ∈ M.U b') :
    gm r y _ (w a b) * gm r y _ (M.g b b') = gm r y _ (L.g a a') * gm r y _ (w a' b') := by
  have h1 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ W ⊓ (L.U a ⊓ M.U b) := inf_le_left
  have h2 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ M.U b ⊓ M.U b' :=
    le_inf (inf_le_left.trans (inf_le_right.trans inf_le_right)) (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have h3 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ L.U a ⊓ L.U a' :=
    le_inf (inf_le_left.trans (inf_le_right.trans inf_le_left)) (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have h4 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ W ⊓ (L.U a' ⊓ M.U b') := inf_le_right
  have key : ∀ (T : Scheme.{0}) (f : T ⟶ X) (t : T), f t ∈ (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) →
      gm f t _ (res h1 (w a b) * res h2 (M.g b b')) = gm f t _ (w a b) * gm f t _ (M.g b b') ∧
      gm f t _ (res h3 (L.g a a') * res h4 (w a' b')) = gm f t _ (L.g a a') * gm f t _ (w a' b') :=
    fun T f t ht ↦ ⟨(map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f t h1 ht _) (gm_res f t h2 ht _)),
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f t h3 ht _) (gm_res f t h4 ht _))⟩
  have e : res h1 (w a b) * res h2 (M.g b b') = res h3 (L.g a a') * res h4 (w a' b') :=
    unit_ext fun x hx ↦ (key X (𝟙 X) x hx).1.trans ((hw x (h1 hx).1 a a' b b' (h3 hx).1 (h3 hx).2 (h2 hx).1 (h2 hx).2).trans
      (key X (𝟙 X) x hx).2.symm)
  have hm : r y ∈ (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) := ⟨⟨h0, ha, hb⟩, ⟨h0, ha', hb'⟩⟩
  exact (key Z r y hm).1.symm.trans ((congrArg (gm r y _) e).trans (key Z r y hm).2)

theorem lbIso_pull_of_isoOn (X Z : Scheme.{0}) (W : X.Opens) (L M : LB X) (w : Cmp W L M) (r : Z ⟶ X)
    (hw : IsoOn W L M w) (hr : ∀ z, r z ∈ W) : LBIso (L.pull r) (M.pull r) := by
  have le : ∀ p : (PUnit → M.ι) × (PUnit → L.ι), (M.pull r).U p.1 ⊓ (L.pull r).U p.2 ≤
      r ⁻¹ᵁ (W ⊓ (L.U (p.2 PUnit.unit) ⊓ M.U (p.1 PUnit.unit))) :=
    fun p y hy ↦ ⟨hr y, mem_pull.1 hy.2, mem_pull.1 hy.1⟩
  refine ⟨⟨fun p ↦ (res (le p) (pullU r _ (w (p.2 PUnit.unit) (p.1 PUnit.unit))))⁻¹⟩, fun p q ↦ unit_ext fun y hy ↦ ?_⟩
  have val : ∀ p : (PUnit → M.ι) × (PUnit → L.ι), y ∈ (M.pull r).U p.1 ⊓ (L.pull r).U p.2 →
      gm (𝟙 Z) y _ (res (le p) (pullU r _ (w (p.2 PUnit.unit) (p.1 PUnit.unit))))⁻¹ =
        (gm r y _ (w (p.2 PUnit.unit) (p.1 PUnit.unit)))⁻¹ := fun p hp ↦
    (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res (𝟙 Z) y (le p) hp _).trans
      ((gm_pull (𝟙 Z) r y _ (le p hp) _).trans (by rw [Category.id_comp]))))
  have hM := gm_pull_g M r (𝟙 Z) y p.1 q.1 hy.1.1 hy.2.1
  have hL := gm_pull_g L r (𝟙 Z) y p.2 q.2 hy.1.2 hy.2.2
  rw [Category.id_comp] at hM hL
  have hd := gm_div (L.pull r) (M.pull r) (𝟙 Z) y p q hy
  have k := isoOn_gm hw r y (hr y) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2.2) (mem_pull.1 hy.1.1) (mem_pull.1 hy.2.1)
  refine (gm_res (𝟙 Z) y inf_le_left hy _).trans ((val p hy.1).trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans ?_
  refine (congrArg₂ (· * ·) (hd.trans (congrArg₂ (fun u v ↦ u * v⁻¹) hM hL))
    ((gm_res (𝟙 Z) y inf_le_right hy _).trans (val q hy.2))).trans ?_
  rw [eq_mul_inv_of_mul_eq k]
  simp only [mul_inv_rev, inv_inv]
  ac_rfl

end GlobalTheory.PicGlue
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PicGlue

theorem cocycle_defect_eq {G : Type} [CommGroup G] {A B C A' B' C' G₁ G₂ G₃ : G} (h₁ : A * G₂ = G₁ * A')
    (h₂ : B * G₃ = G₂ * B') (h₃ : C * G₃ = G₁ * C') : A * B * C⁻¹ = A' * B' * C'⁻¹ := by
  have e₁ : A' = G₁⁻¹ * (A * G₂) := by rw [h₁, inv_mul_cancel_left]
  have e₂ : B' = G₂⁻¹ * (B * G₃) := by rw [h₂, inv_mul_cancel_left]
  have e₃ : C' = G₁⁻¹ * (C * G₃) := by rw [h₃, inv_mul_cancel_left]
  subst e₁ e₂ e₃
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem cocycle_defect_one {G : Type} [CommGroup G] {A B C R₁ R₂ R₃ : G} (h₁ : A * R₂ = R₁) (h₂ : B * R₃ = R₂)
    (h₃ : C * R₃ = R₁) : A * B * C⁻¹ = 1 := by
  rw [mul_inv_eq_one]
  apply mul_right_cancel (b := R₃)
  rw [_root_.mul_assoc, h₂, h₁, h₃]

theorem norm_cocycle : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X), e ≫ p = 𝟙 Y → FnBij p → ∀ (V : Y.Opens) (W₁ W₂ W₃ W₁₂ W₂₃ W₁₃ : X.Opens) (L₁ L₂ L₃ : LB X) (w₁₂ : Cmp W₁₂ L₁ L₂) (w₂₃ : Cmp W₂₃ L₂ L₃) (w₁₃ : Cmp W₁₃ L₁ L₃) (r₁ : RigD e L₁) (r₂ : RigD e L₂) (r₃ : RigD e L₃), IsOn W₁ L₁ → IsOn W₂ L₂ → IsOn W₃ L₃ → p ⁻¹ᵁ V ≤ W₁ ⊓ W₂ ⊓ W₃ → p ⁻¹ᵁ V ≤ W₁₂ ⊓ W₂₃ ⊓ W₁₃ → IsoOn W₁₂ L₁ L₂ w₁₂ → IsoOn W₂₃ L₂ L₃ w₂₃ → IsoOn W₁₃ L₁ L₃ w₁₃ → Norm e W₁₂ L₁ L₂ w₁₂ r₁ r₂ → Norm e W₂₃ L₂ L₃ w₂₃ r₂ r₃ → Norm e W₁₃ L₁ L₃ w₁₃ r₁ r₃ → ∀ (x : X) (a : L₁.ι) (b : L₂.ι) (c : L₃.ι), p x ∈ V → x ∈ L₁.U a → x ∈ L₂.U b → x ∈ L₃.U c → gm (𝟙 X) x _ (w₁₂ a b) * gm (𝟙 X) x _ (w₂₃ b c) = gm (𝟙 X) x _ (w₁₃ a c) := by
  intro X Y p e hep hp V W₁ W₂ W₃ W₁₂ W₂₃ W₁₃ L₁ L₂ L₃ w₁₂ w₂₃ w₁₃ r₁ r₂ r₃ h₁ h₂ h₃ hVW hVW' i₁₂ i₂₃ i₁₃
    n₁₂ n₂₃ n₁₃ x a b c hx ha hb hc
  let O : L₁.ι × L₂.ι × L₃.ι → X.Opens := fun j ↦ p ⁻¹ᵁ V ⊓ (L₁.U j.1 ⊓ L₂.U j.2.1 ⊓ L₃.U j.2.2)
  have mO : ∀ (j : L₁.ι × L₂.ι × L₃.ι) (z : X),
      z ∈ O j ↔ p z ∈ V ∧ z ∈ L₁.U j.1 ∧ z ∈ L₂.U j.2.1 ∧ z ∈ L₃.U j.2.2 := by
    intro j z
    simp only [O, TopologicalSpace.Opens.mem_inf, and_assoc]
    rfl
  have mW : ∀ z : X, p z ∈ V → (z ∈ W₁ ∧ z ∈ W₂ ∧ z ∈ W₃) ∧ z ∈ W₁₂ ∧ z ∈ W₂₃ ∧ z ∈ W₁₃ := by
    intro z hz
    have e₁ := hVW (show z ∈ p ⁻¹ᵁ V from hz)
    have e₂ := hVW' (show z ∈ p ⁻¹ᵁ V from hz)
    simp only [TopologicalSpace.Opens.mem_inf] at e₁ e₂
    exact ⟨⟨e₁.1.1, e₁.1.2, e₁.2⟩, e₂.1.1, e₂.1.2, e₂.2⟩
  have l₁₂ : ∀ j, O j ≤ W₁₂ ⊓ (L₁.U j.1 ⊓ L₂.U j.2.1) := fun j z hz ↦ by
    rw [mO] at hz
    simp only [TopologicalSpace.Opens.mem_inf]
    exact ⟨(mW z hz.1).2.1, hz.2.1, hz.2.2.1⟩
  have l₂₃ : ∀ j, O j ≤ W₂₃ ⊓ (L₂.U j.2.1 ⊓ L₃.U j.2.2) := fun j z hz ↦ by
    rw [mO] at hz
    simp only [TopologicalSpace.Opens.mem_inf]
    exact ⟨(mW z hz.1).2.2.1, hz.2.2.1, hz.2.2.2⟩
  have l₁₃ : ∀ j, O j ≤ W₁₃ ⊓ (L₁.U j.1 ⊓ L₃.U j.2.2) := fun j z hz ↦ by
    rw [mO] at hz
    simp only [TopologicalSpace.Opens.mem_inf]
    exact ⟨(mW z hz.1).2.2.2, hz.2.1, hz.2.2.2⟩
  let u : ∀ j, Γ(X, O j)ˣ := fun j ↦
    res (l₁₂ j) (w₁₂ j.1 j.2.1) * res (l₂₃ j) (w₂₃ j.2.1 j.2.2) * (res (l₁₃ j) (w₁₃ j.1 j.2.2))⁻¹
  have hu : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (j : L₁.ι × L₂.ι × L₃.ι), f z ∈ O j →
      gm f z (O j) (u j) = gm f z _ (w₁₂ j.1 j.2.1) * gm f z _ (w₂₃ j.2.1 j.2.2) * (gm f z _ (w₁₃ j.1 j.2.2))⁻¹ := by
    intro Z f z j hz
    simp only [u, map_mul, map_inv]
    rw [gm_res f z (l₁₂ j) hz, gm_res f z (l₂₃ j) hz, gm_res f z (l₁₃ j) hz]
  have compat : ∀ i j, ∀ z ∈ O i ⊓ O j, gm (𝟙 X) z (O i) (u i) = gm (𝟙 X) z (O j) (u j) := by
    intro i j z hz
    rw [TopologicalSpace.Opens.mem_inf] at hz
    have hzi := hz.1
    have hzj := hz.2
    rw [hu (𝟙 X) z i hzi, hu (𝟙 X) z j hzj]
    rw [mO] at hzi hzj
    have hW := mW z hzi.1
    exact cocycle_defect_eq (i₁₂ z hW.2.1 i.1 j.1 i.2.1 j.2.1 hzi.2.1 hzj.2.1 hzi.2.2.1 hzj.2.2.1)
      (i₂₃ z hW.2.2.1 i.2.1 j.2.1 i.2.2 j.2.2 hzi.2.2.1 hzj.2.2.1 hzi.2.2.2 hzj.2.2.2)
      (i₁₃ z hW.2.2.2 i.1 j.1 i.2.2 j.2.2 hzi.2.1 hzj.2.1 hzi.2.2.2 hzj.2.2.2)
  have chart : ∀ z : X, p z ∈ V → ∃ j, z ∈ O j := by
    intro z hz
    have hW := mW z hz
    obtain ⟨a', ha'⟩ := h₁.cov z hW.1.1
    obtain ⟨b', hb'⟩ := h₂.cov z hW.1.2.1
    obtain ⟨c', hc'⟩ := h₃.cov z hW.1.2.2
    exact ⟨(a', b', c'), (mO _ z).2 ⟨hz, ha', hb', hc'⟩⟩
  have hcov : p ⁻¹ᵁ V ≤ iSup O := fun z hz ↦ by
    obtain ⟨j, hj⟩ := chart z hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨ρ, hρ⟩ := glue_unit (p ⁻¹ᵁ V) O (fun j ↦ inf_le_left) hcov u compat

  let φ := RingEquiv.ofBijective (p.app V).hom (hp V)
  let v : Γ(Y, V)ˣ := Units.map φ.symm.toMonoidHom ρ
  have hv : pullU p V v = ρ := by
    apply Units.ext
    exact φ.apply_symm_apply ρ.val

  have hepy : ∀ y : Y, p (e y) = y := fun y ↦ by
    change (e ≫ p) y = y
    rw [hep]
    rfl
  have hρe : ∀ y : Y, y ∈ V → gm e y (p ⁻¹ᵁ V) ρ = 1 := by
    intro y hy
    have hy' : p (e y) ∈ V := by rw [hepy]; exact hy
    obtain ⟨j, hj⟩ := chart (e y) hy'
    rw [← gm_res e y (inf_le_left : O j ≤ p ⁻¹ᵁ V) hj, hρ j, hu e y j hj]
    rw [mO] at hj
    have hW := mW (e y) hj.1
    exact cocycle_defect_one (n₁₂ y j.1 j.2.1 hW.2.1 hj.2.1 hj.2.2.1) (n₂₃ y j.2.1 j.2.2 hW.2.2.1 hj.2.2.1 hj.2.2.2)
      (n₁₃ y j.1 j.2.2 hW.2.2.2 hj.2.1 hj.2.2.2)
  have hv1 : v = 1 := by
    apply unit_ext
    intro y hy
    rw [map_one]
    have hy' : p (e y) ∈ V := by rw [hepy]; exact hy
    have h := gm_pull e p y V hy' v
    rw [hep, hv] at h
    rw [← h]
    exact hρe y hy
  have hρ1 : ρ = 1 := by rw [← hv, hv1, map_one]

  have hxO : x ∈ O (a, b, c) := (mO _ x).2 ⟨hx, ha, hb, hc⟩
  have h := hu (𝟙 X) x (a, b, c) hxO
  rw [← hρ, hρ1, map_one, map_one] at h
  exact (mul_inv_eq_one.1 h.symm)

end GlobalTheory.PicGlue
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_integral_of_modelAt (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (V : ValuationSubring ℂ) (A : WeierstrassCurve F) (D : F)
    (hV : ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F) (hD : D ≠ 0)
    (h : ModelAt V F (A.map (algebraMap F ℂ)) (D : ℂ)) :
    ∃ (C : VariableChange F) (u : (w.valuationSubringAtPrime F)ˣ),
      (C • A).IsIntegral (w.valuationSubringAtPrime F) ∧
        (C • A).Δ = ((u : w.valuationSubringAtPrime F) : F) * D := by
  obtain ⟨C, hu, hr, hs, ht, ⟨h1, h2, h3, h4, h6⟩, hΔ⟩ := h
  have hu0 : (⟨(C.u : ℂ), hu⟩ : F) ≠ 0 := by
    intro h0
    exact C.u.ne_zero (congrArg (fun x : F => (x : ℂ)) h0)
  let C' : VariableChange F := ⟨Units.mk0 _ hu0, ⟨C.r, hr⟩, ⟨C.s, hs⟩, ⟨C.t, ht⟩⟩
  have hC : C'.map (algebraMap F ℂ) = C := by
    ext <;> rfl
  have hmap : (C' • A).map (algebraMap F ℂ) = C • A.map (algebraMap F ℂ) := by
    rw [← hC, map_variableChange]
  rw [← hmap] at h1 h2 h3 h4 h6 hΔ
  set W := C' • A with hW
  have hD' : (D : ℂ) ≠ 0 := fun h0 => hD (Subtype.ext h0)
  have hvD : V.valuation (D : ℂ) ≠ 0 := by simpa using hD'
  rw [map_Δ] at hΔ
  have hΔ' : V.valuation ((W.Δ : F) : ℂ) = V.valuation (D : ℂ) := hΔ
  have hW0 : W.Δ ≠ 0 := by
    intro h0
    rw [h0] at hΔ'
    exact hvD (by simpa using hΔ'.symm)
  have hx : W.Δ / D ∈ w.valuationSubringAtPrime F := by
    rw [← hV, ← V.valuation_le_one_iff]
    push_cast
    rw [map_div₀, hΔ', div_self hvD]
  have hy : D / W.Δ ∈ w.valuationSubringAtPrime F := by
    rw [← hV, ← V.valuation_le_one_iff]
    push_cast
    rw [map_div₀, hΔ', div_self hvD]
  refine ⟨C', ⟨⟨_, hx⟩, ⟨_, hy⟩, ?_, ?_⟩, ?_, ?_⟩
  · apply Subtype.ext
    show W.Δ / D * (D / W.Δ) = 1
    field_simp
  · apply Subtype.ext
    show D / W.Δ * (W.Δ / D) = 1
    field_simp
  · refine ⟨⟨⟨⟨W.a₁, (hV _).1 h1⟩, ⟨W.a₂, (hV _).1 h2⟩, ⟨W.a₃, (hV _).1 h3⟩, ⟨W.a₄, (hV _).1 h4⟩,
      ⟨W.a₆, (hV _).1 h6⟩⟩, ?_⟩⟩
    ext <;> rfl
  · show W.Δ = W.Δ / D * D
    field_simp

end GlobalTheory.CMModel
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem mem_of_pow_mem_valSubring (V : ValuationSubring ℂ) {x : ℂ} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ V) :
    x ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff_of_nonneg zero_le' hn).1 h

theorem inv_two_three_mem (V : ValuationSubring ℂ) (h : V.valuation (6 : ℂ) = 1) :
    (2 : ℂ)⁻¹ ∈ V ∧ (3 : ℂ)⁻¹ ∈ V := by
  have h6 : (6 : ℂ)⁻¹ ∈ V := by
    rw [← V.valuation_le_one_iff, map_inv₀, h, inv_one]
  have h2 : (2 : ℂ) ∈ V := by simpa using natCast_mem V 2
  have h3 : (3 : ℂ) ∈ V := by simpa using natCast_mem V 3
  constructor
  · have : (2 : ℂ)⁻¹ = 3 * 6⁻¹ := by norm_num
    rw [this]; exact mul_mem h3 h6
  · have : (3 : ℂ)⁻¹ = 2 * 6⁻¹ := by norm_num
    rw [this]; exact mul_mem h2 h6

theorem short_coeff_mem (V : ValuationSubring ℂ) (h : V.valuation (6 : ℂ) = 1) (a b j : ℂ) (hj : j ∈ V)
    (hd : -16 * (4 * a ^ 3 + 27 * b ^ 2) ∈ V)
    (he : j * (-16 * (4 * a ^ 3 + 27 * b ^ 2)) = (-48 * a) ^ 3) : a ∈ V ∧ b ∈ V := by
  obtain ⟨h2, h3⟩ := inv_two_three_mem V h
  have h1 : -48 * a ∈ V := mem_of_pow_mem_valSubring V (n := 3) (by norm_num) (he ▸ mul_mem hj hd)
  have ha : a ∈ V := by
    have : a = -(((2 : ℂ)⁻¹) ^ 4 * 3⁻¹ * (-48 * a)) := by ring
    rw [this]
    exact neg_mem (mul_mem (mul_mem (pow_mem h2 4) h3) h1)
  refine ⟨ha, mem_of_pow_mem_valSubring V (n := 2) (by norm_num) ?_⟩
  have h4 : (4 : ℂ) ∈ V := by simpa using natCast_mem V 4
  have : b ^ 2 = ((3 : ℂ)⁻¹) ^ 3 * (-(((2 : ℂ)⁻¹) ^ 4 * (-16 * (4 * a ^ 3 + 27 * b ^ 2))) - 4 * a ^ 3) := by
    ring
  rw [this]
  exact mul_mem (pow_mem h3 3) (sub_mem (neg_mem (mul_mem (pow_mem h2 4) hd)) (mul_mem h4 (pow_mem ha 3)))

theorem modelAt_short_of_six_unit :
    ∀ (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (a₄ a₆ j u D : ℂ), j ∈ V → j * (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ = (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).c₄ ^ 3 → V.valuation (6 : ℂ) = 1 → u ∈ F → u ≠ 0 → D ∈ V → V.valuation u ^ 12 * V.valuation D = V.valuation (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ → ModelAt V F ⟨0, 0, 0, a₄, a₆⟩ D := by
  intro V F a₄ a₆ j u D hj he h6 hu hu0 hD hv
  set C : VariableChange ℂ := ⟨Units.mk0 u hu0, 0, 0, 0⟩ with hC
  have hΔ : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ = -16 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    ring
  have hc : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).c₄ = -48 * a₄ := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have hval : V.valuation (u⁻¹ ^ 12 * (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ) = V.valuation D := by
    have hvu : V.valuation u ≠ 0 := by simpa using hu0
    rw [map_mul, map_pow, map_inv₀, ← hv, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hvu, one_pow, one_mul]
  have hmem : u⁻¹ ^ 12 * (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ ∈ V := by
    rw [← V.valuation_le_one_iff, hval, V.valuation_le_one_iff]; exact hD
  have hab := short_coeff_mem V h6 (u⁻¹ ^ 4 * a₄) (u⁻¹ ^ 6 * a₆) j hj
    (by convert hmem using 1; rw [hΔ]; ring)
    (by rw [hΔ, hc] at he; linear_combination u⁻¹ ^ 12 * he)
  refine ⟨C, hu, zero_mem F, zero_mem F, zero_mem F, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [hC, variableChange_a₁, zero_mem]
  · simp [hC, variableChange_a₂, zero_mem]
  · simp [hC, variableChange_a₃, zero_mem]
  · simpa [hC, variableChange_a₄] using hab.1
  · simpa [hC, variableChange_a₆] using hab.2
  · rw [variableChange_Δ, ← hval]; simp [hC]

end GlobalTheory.CMModel
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem GlobalTheory.CMModel.tangentSlope_mem : ∀ (V : ValuationSubring ℂ) (a₄ a₆ r s t X Y : ℂ) (u : ℂˣ), IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) → (X - r) / (u : ℂ) ^ 2 ∈ V → (Y - t - s * (X - r)) / (u : ℂ) ^ 3 ∈ V → V.valuation (2 * Y) = V.valuation (u : ℂ) ^ 3 → ((3 * X ^ 2 + a₄) / (2 * Y) - s) / (u : ℂ) ∈ V := by
  intro V a₄ a₆ r s t X Y u hI hx hy hv
  obtain ⟨h1, h2, -, h4, -⟩ := hI
  set W' := (⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ) with hW'
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  have hY : 2 * Y ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact pow_ne_zero 3 ((Valuation.ne_zero_iff _).2 hu) hv.symm
  have hY0 : Y ≠ 0 := right_ne_zero_of_mul hY
  have hq : (u : ℂ) ^ 3 / (2 * Y) ∈ V := by
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀, map_pow, ← hv, div_self]
    exact (Valuation.ne_zero_iff _).2 hY
  have hE : 3 * ((X - r) / (u : ℂ) ^ 2) ^ 2 + 2 * W'.a₂ * ((X - r) / (u : ℂ) ^ 2) + W'.a₄
      - W'.a₁ * ((Y - t - s * (X - r)) / (u : ℂ) ^ 3) ∈ V := by
    have h3 : (3 : ℂ) ∈ V := by simpa using natCast_mem V 3
    have h2' : (2 : ℂ) ∈ V := by simpa using natCast_mem V 2
    exact sub_mem (add_mem (add_mem (mul_mem h3 (pow_mem hx 2)) (mul_mem (mul_mem h2' h2) hx)) h4)
      (mul_mem h1 hy)
  have key : ((3 * X ^ 2 + a₄) / (2 * Y) - s) / (u : ℂ) =
      (3 * ((X - r) / (u : ℂ) ^ 2) ^ 2 + 2 * W'.a₂ * ((X - r) / (u : ℂ) ^ 2) + W'.a₄
      - W'.a₁ * ((Y - t - s * (X - r)) / (u : ℂ) ^ 3)) * ((u : ℂ) ^ 3 / (2 * Y)) := by
    simp only [hW', WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₄, Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [key]
  exact mul_mem hE hq
end
