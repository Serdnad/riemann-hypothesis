module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} in
theorem _root_.GlobalTheory.tateIso_ev_eq_iff (I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a b : D.La) :
    I.ev n a = I.ev n b ↔ D.ModN n (a - b) := by
  have key : I.ev n (a - b) * I.ev n b = I.ev n a := by rw [← I.add, sub_add_cancel]
  rw [show D.ModN n (a - b) ↔ ∃ c, a - b = n • c from Iff.rfl, ← I.ker n hn, ← key]
  exact mul_eq_right


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} in
theorem _root_.GlobalTheory.tateIso_ev_pow (I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a : D.La) :
    I.ev n a ^ n = 1 :=
  (I.onto n hn _).mpr ⟨a, rfl⟩

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} in
private lemma exists_linearMap_ev_eq_of_tateIso (I I' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) {n : ℕ} (hn : 0 < n) :
    ∃ f : D.La →ₗ[𝓞 E] D.La, ∀ a, I.ev n (f a) = I'.ev n a := by
  classical
  haveI := D.proj
  let N : Submodule (𝓞 E) D.La := LinearMap.range ((n : 𝓞 E) • LinearMap.id)
  have hN : ∀ x, x ∈ N ↔ D.ModN n x := by
    intro x
    show (∃ y, (n : 𝓞 E) • y = x) ↔ ∃ y, x = n • y
    simp only [Nat.cast_smul_eq_nsmul]
    constructor <;> rintro ⟨y, hy⟩ <;> exact ⟨y, hy.symm⟩
  have hrel : ∀ x y, I.ev n x = I.ev n y ↔ x - y ∈ N := fun x y =>
    (_root_.GlobalTheory.tateIso_ev_eq_iff I hn x y).trans (hN _).symm
  have hs : ∀ a, ∃ b, I.ev n b = I'.ev n a :=
    fun a => (I.onto n hn _).mp (_root_.GlobalTheory.tateIso_ev_pow I' hn a)
  choose s hs using hs
  let g : D.La →ₗ[𝓞 E] D.La ⧸ N :=
    { toFun := fun a => N.mkQ (s a)
      map_add' := fun a b => by
        rw [← map_add (f := _), Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hrel,
          I.add, hs, hs, hs, I'.add]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply,
          Submodule.Quotient.eq, ← hrel, I.lin, hs, hs, I'.lin] }
  obtain ⟨f, hf⟩ := Module.projective_lifting_property N.mkQ g (Submodule.mkQ_surjective N)
  refine ⟨f, fun a => ?_⟩
  have h1 : N.mkQ (f a) = N.mkQ (s a) := LinearMap.congr_fun hf a
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hrel] at h1
  rw [h1, hs]


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.tateIso_differ_by_similitude :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop), (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → ∀ I I' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e, ∃ g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n := by
  intro E _ _ _ H D k _ Q _ act e he I I'
  have hf : ∀ n, ∃ f : D.La →ₗ[𝓞 E] D.La, 0 < n → ∀ a, I.ev n (f a) = I'.ev n a := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨f, hf⟩ := exists_linearMap_ev_eq_of_tateIso I I' hn
      exact ⟨f, fun _ => hf⟩
  choose f hf using hf
  have hk : ∀ n, ∃ ν : ℤ, 0 < n → I'.ζ n = I.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
    · haveI : NeZero n := ⟨hn.ne'⟩
      have hprim : IsPrimitiveRoot ((I.ζ n : kˣ) : k) n :=
        IsPrimitiveRoot.coe_units_iff.mpr (I.ζ_prim n hn)
      have hpow : ((I'.ζ n : kˣ) : k) ^ n = 1 := by
        rw [← Units.val_pow_eq_pow_val, (I'.ζ_prim n hn).pow_eq_one, Units.val_one]
      obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hpow
      refine ⟨i, fun _ => ?_⟩
      ext
      rw [zpow_natCast, Units.val_pow_eq_pow_val, hi]
  choose ν hν using hk
  refine ⟨⟨f, ν, ?_, ?_, ?_⟩, fun n hn => ⟨fun a => (hf n hn a).symm, hν n hn⟩⟩
  · intro n m hn hm a
    rw [← _root_.GlobalTheory.tateIso_ev_eq_iff I hn, ← I.tower n m hn hm, hf (n * m) (Nat.mul_pos hn hm),
      hf n hn, I'.tower n m hn hm]
  · intro n hn
    obtain ⟨g, hg⟩ := exists_linearMap_ev_eq_of_tateIso I' I hn
    refine ⟨g, fun a => ⟨?_, ?_⟩⟩
    · rw [← _root_.GlobalTheory.tateIso_ev_eq_iff I' hn, hg, hf n hn]
    · rw [← _root_.GlobalTheory.tateIso_ev_eq_iff I hn, hf n hn, hg]
  · intro n hn a b
    have h1 := I.isom n hn (f n a) (f n b)
    have h2 := I'.isom n hn a b
    rw [hf n hn, hf n hn] at h1
    have hc := he n _ _ _ _ hn (_root_.GlobalTheory.tateIso_ev_pow I' hn a)
      (_root_.GlobalTheory.tateIso_ev_pow I' hn b) h1 h2
    rw [hν n hn, ← zpow_mul] at hc
    rw [← (I.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, hc, mul_inv_cancel]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.PartialCocycle

private theorem gm_res_eq_gm {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) {U V : X.Opens} (hle : V ≤ U)
    (hz : f z ∈ V) (u : Γ(X, U)ˣ) : gm f z V (res hle u) = gm f z U u := by
  have key : X.presheaf.map (homOfLE hle).op ≫ f.app V ≫ Z.presheaf.germ (f ⁻¹ᵁ V) z hz =
      f.app U ≫ Z.presheaf.germ (f ⁻¹ᵁ U) z (hle hz) := by
    rw [← Scheme.Hom.germ_stalkMap, ← Scheme.Hom.germ_stalkMap, ← Category.assoc, TopCat.Presheaf.germ_res]
  unfold gm
  rw [dite_eq_left hz, dite_eq_left (hle hz)]
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map]
  unfold res pullU
  have h2 := congrArg (fun g => g.hom (u : Γ(X, U))) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  exact h2

theorem gm_iso {X Z : Scheme.{0}} {L M : LB X} {w : LB.Iso L M} (hw : w.IsGen) (f : Z ⟶ X) (z : Z)
    (a a' : M.ι) (b b' : L.ι) (ha : f z ∈ M.U a) (ha' : f z ∈ M.U a') (hb : f z ∈ L.U b) (hb' : f z ∈ L.U b') :
    gm f z (M.U a ⊓ L.U b) (w.s (a, b)) =
      gm f z (M.U a ⊓ M.U a') (M.g a a') * (gm f z (L.U b ⊓ L.U b') (L.g b b'))⁻¹ *
        gm f z (M.U a' ⊓ L.U b') (w.s (a', b')) := by
  have hz : f z ∈ (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') := ⟨⟨ha, hb⟩, ⟨ha', hb'⟩⟩
  have h₁ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a ⊓ L.U b := inf_le_left
  have h₂ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a ⊓ M.U a' :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have h₃ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ L.U b ⊓ L.U b' :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have h₄ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a' ⊓ L.U b' := inf_le_right
  have h1 := hw (a, b) (a', b')
  calc gm f z (M.U a ⊓ L.U b) (w.s (a, b))
      = gm f z _ (res h₁ (w.s (a, b))) := (gm_res_eq_gm f z h₁ hz _).symm
    _ = gm f z _ (res h₂ (M.g a a') * (res h₃ (L.g b b'))⁻¹ * res h₄ (w.s (a', b'))) := congrArg _ h1
    _ = _ := by
      rw [map_mul, map_mul, map_inv, gm_res_eq_gm f z h₂ hz, gm_res_eq_gm f z h₃ hz]
      exact congrArg _ (gm_res_eq_gm f z h₄ hz _)

private theorem algebraMap_OmS_eq_algebraMap_comp {G : Type*} [CommGroup G] (A B C s t u : G) :
    A * B⁻¹ * s * (B * C⁻¹ * t) * (A * C⁻¹ * u)⁻¹ = s * t * u⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem gm_val_eq_germ_app' {X Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) (U : X.Opens) (hz : g z ∈ U)
    (u : Γ(X, U)ˣ) : ((gm g z U u : Z.presheaf.stalk z)) = Z.presheaf.germ (g ⁻¹ᵁ U) z hz (g.app U u.val) := by
  unfold gm
  rw [dite_eq_left hz]
  rfl

private theorem gm_id_val_eq_germ' {X : Scheme.{0}} (z : X) (U : X.Opens) (hz : z ∈ U)
    (u : Γ(X, U)ˣ) : ((gm (𝟙 X) z U u : X.presheaf.stalk z)) = X.presheaf.germ U z hz u.val := by
  exact gm_val_eq_germ_app' (𝟙 X) z U hz u

theorem cocycle_of_rigid : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (V₁ V₂ V₃ : S.Opens) (M₁ M₂ M₃ : LB X) (w₁₂ : LB.Iso M₂ M₁) (w₂₃ : LB.Iso M₃ M₂) (w₁₃ : LB.Iso M₃ M₁), e ≫ p = 𝟙 S → (∀ (V : S.Opens) (u : Γ(X, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → ⨆ a, M₁.U a = p ⁻¹ᵁ V₁ → ⨆ a, M₂.U a = p ⁻¹ᵁ V₂ → ⨆ a, M₃.U a = p ⁻¹ᵁ V₃ → w₁₂.IsGen → w₂₃.IsGen → w₁₃.IsGen → (∀ (x : S) a b c, e x ∈ M₁.U a → e x ∈ M₂.U b → e x ∈ M₃.U c → gm e x (M₁.U a ⊓ M₂.U b) (w₁₂.s (a, b)) * gm e x (M₂.U b ⊓ M₃.U c) (w₂₃.s (b, c)) = gm e x (M₁.U a ⊓ M₃.U c) (w₁₃.s (a, c))) → ∀ (y : X) a b c, y ∈ M₁.U a → y ∈ M₂.U b → y ∈ M₃.U c → gm (𝟙 X) y (M₁.U a ⊓ M₂.U b) (w₁₂.s (a, b)) * gm (𝟙 X) y (M₂.U b ⊓ M₃.U c) (w₂₃.s (b, c)) = gm (𝟙 X) y (M₁.U a ⊓ M₃.U c) (w₁₃.s (a, c)) := by
  intro X S p e V₁ V₂ V₃ M₁ M₂ M₃ w₁₂ w₂₃ w₁₃ hep hrig hU₁ hU₂ hU₃ hg₁₂ hg₂₃ hg₁₃ hcoc y a b c hya hyb hyc
  let T : M₁.ι × M₂.ι × M₃.ι → X.Opens := fun i => M₁.U i.1 ⊓ M₂.U i.2.1 ⊓ M₃.U i.2.2
  have l₁ : ∀ i, T i ≤ M₁.U i.1 ⊓ M₂.U i.2.1 := fun i => inf_le_left
  have l₂ : ∀ i, T i ≤ M₂.U i.2.1 ⊓ M₃.U i.2.2 := fun i => le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l₃ : ∀ i, T i ≤ M₁.U i.1 ⊓ M₃.U i.2.2 := fun i => le_inf (inf_le_left.trans inf_le_left) inf_le_right
  let t : ∀ i, Γ(X, T i)ˣ := fun i => res (l₁ i) (w₁₂.s (i.1, i.2.1)) * res (l₂ i) (w₂₃.s (i.2.1, i.2.2)) *
    (res (l₃ i) (w₁₃.s (i.1, i.2.2)))⁻¹
  have hprod : ∀ {Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) i (hz : g z ∈ T i), gm g z (T i) (t i) =
      gm g z (M₁.U i.1 ⊓ M₂.U i.2.1) (w₁₂.s (i.1, i.2.1)) * gm g z (M₂.U i.2.1 ⊓ M₃.U i.2.2) (w₂₃.s (i.2.1, i.2.2)) *
        (gm g z (M₁.U i.1 ⊓ M₃.U i.2.2) (w₁₃.s (i.1, i.2.2)))⁻¹ := by
    intro Z g z i hz
    simp only [t, map_mul, map_inv]
    exact congrArg₂ _ (congrArg₂ _ (gm_res_eq_gm g z (l₁ i) hz _) (gm_res_eq_gm g z (l₂ i) hz _))
      (congrArg _ (gm_res_eq_gm g z (l₃ i) hz _))
  have hindep : ∀ {Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) i j (hi : g z ∈ T i) (hj : g z ∈ T j),
      gm g z (T i) (t i) = gm g z (T j) (t j) := by
    intro Z g z i j hi hj
    rw [hprod g z i hi, hprod g z j hj]
    obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
    obtain ⟨⟨hj1, hj2⟩, hj3⟩ := hj
    rw [gm_iso hg₁₂ g z i.1 j.1 i.2.1 j.2.1 hi1 hj1 hi2 hj2, gm_iso hg₂₃ g z i.2.1 j.2.1 i.2.2 j.2.2 hi2 hj2 hi3 hj3,
      gm_iso hg₁₃ g z i.1 j.1 i.2.2 j.2.2 hi1 hj1 hi3 hj3]
    exact algebraMap_OmS_eq_algebraMap_comp _ _ _ _ _ _
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 T (fun i => (t i).val) := by
    intro i j
    apply TopCat.Presheaf.section_ext X.sheaf
    intro z hz
    show X.presheaf.germ (T i ⊓ T j) z hz (X.presheaf.map (TopologicalSpace.Opens.infLELeft (T i) (T j)).op (t i).val) =
      X.presheaf.germ (T i ⊓ T j) z hz (X.presheaf.map (TopologicalSpace.Opens.infLERight (T i) (T j)).op (t j).val)
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    rw [← gm_id_val_eq_germ' z (T i) _ (t i), ← gm_id_val_eq_germ' z (T j) _ (t j)]
    exact congrArg Units.val (hindep (𝟙 X) z i j hz.1 hz.2)
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing T (fun i => (t i).val) hcompat
  have hcov : p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃) ≤ iSup T := by
    intro x hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    have m1 : x ∈ ⨆ a, M₁.U a := by rw [hU₁]; exact h1
    have m2 : x ∈ ⨆ a, M₂.U a := by rw [hU₂]; exact h2
    have m3 : x ∈ ⨆ a, M₃.U a := by rw [hU₃]; exact h3
    obtain ⟨a₁, ha₁⟩ := TopologicalSpace.Opens.mem_iSup.1 m1
    obtain ⟨a₂, ha₂⟩ := TopologicalSpace.Opens.mem_iSup.1 m2
    obtain ⟨a₃, ha₃⟩ := TopologicalSpace.Opens.mem_iSup.1 m3
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a₁, a₂, a₃), ⟨⟨ha₁, ha₂⟩, ha₃⟩⟩
  have hV : V₁ ⊓ V₂ ⊓ V₃ ≤ e ⁻¹ᵁ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) := by
    intro x hx
    show (e ≫ p) x ∈ V₁ ⊓ V₂ ⊓ V₃
    rw [hep]
    exact hx
  let u : Γ(X, p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) := X.presheaf.map (homOfLE hcov).op s
  have hsT : ∀ i (z : X) (hz : z ∈ T i) (hz' : z ∈ iSup T),
      X.presheaf.germ (iSup T) z hz' s = X.presheaf.germ (T i) z hz (t i).val := by
    intro i z hz hz'
    have h := hs i
    dsimp only at h
    rw [← h]
    exact (TopCat.Presheaf.germ_res_apply X.presheaf (TopologicalSpace.Opens.leSupr T i) z hz s).symm
  have hu1 : (e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV).hom u = 1 := by
    apply TopCat.Presheaf.section_ext S.sheaf
    intro x hx
    have hex : e x ∈ p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃) := hV hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov hex)
    show S.presheaf.germ _ x hx ((e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV).hom u) = S.presheaf.germ _ x hx 1
    rw [map_one]
    have k1 : e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV ≫ S.presheaf.germ _ x hx =
        X.presheaf.germ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (e x) hex ≫ e.stalkMap x := by
      rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    have k2 := congrArg (fun g => g.hom u) k1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at k2
    rw [k2]
    have hg1 : gm e x (T i) (t i) = 1 := by
      rw [hprod e x i hi]
      obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
      rw [hcoc x i.1 i.2.1 i.2.2 hi1 hi2 hi3, mul_inv_cancel]
    rw [← Units.val_one, ← hg1, gm_val_eq_germ_app' e x (T i) hi]
    simp only [u]
    erw [TopCat.Presheaf.germ_res_apply, hsT i (e x) hi, Scheme.Hom.germ_stalkMap_apply]
  have hu : u = 1 := hrig _ u hV hu1
  have hyT : y ∈ T (a, b, c) := ⟨⟨hya, hyb⟩, hyc⟩
  have hyS : y ∈ iSup T := TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b, c), hyT⟩
  have fin : gm (𝟙 X) y (T (a, b, c)) (t (a, b, c)) = 1 := by
    apply Units.ext
    rw [gm_id_val_eq_germ' y _ hyT, Units.val_one, ← hsT (a, b, c) y hyT hyS]
    have hyV : y ∈ p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃) := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have := (le_iSup M₁.U a) hya
        rw [hU₁] at this
        exact this
      · have := (le_iSup M₂.U b) hyb
        rw [hU₂] at this
        exact this
      · have := (le_iSup M₃.U c) hyc
        rw [hU₃] at this
        exact this
    have k3 := congrArg (X.presheaf.germ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) y hyV) hu
    simp only [u, map_one] at k3
    erw [TopCat.Presheaf.germ_res_apply] at k3
    exact k3
  rw [hprod (𝟙 X) y (a, b, c) hyT] at fin
  exact mul_inv_eq_one.1 fin

end GlobalTheory.PartialCocycle
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.BaseChangeFns

private theorem surjective_appTop_of_iso {X Y : Scheme.{0}} (e : X ≅ Y) : Function.Surjective e.hom.appTop.hom := by
  first
  | exact (ConcreteCategory.bijective_of_isIso e.hom.appTop).2
  | exact (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
  | exact fun a => ⟨e.inv.appTop.hom a, by
      rw [← CommRingCat.comp_apply, ← Scheme.comp_appTop, e.inv_hom_id, Scheme.id_appTop]; rfl⟩

private theorem surjective_appTop_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (q : Y ⟶ Z)
    (hp : Function.Surjective p.appTop.hom) (hq : Function.Surjective q.appTop.hom) :
    Function.Surjective (p ≫ q).appTop.hom := by
  first
  | exact hp.comp hq
  | (rw [Scheme.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]; exact hp.comp hq)
  | exact surj_comp hp hq

private theorem surjective_of_comp_surjective_of_injective {A B C : CommRingCat} (g : A ⟶ B) (m : B ⟶ C)
    (hm : Function.Injective m.hom) (h : Function.Surjective (g ≫ m).hom) : Function.Surjective g.hom := by
  intro y
  obtain ⟨x, hx⟩ := h (m.hom y)
  exact ⟨x, hm hx⟩

private theorem injective_presheaf_map_eqToHom {X : Scheme.{0}} {V W : X.Opens} (p : V = W) :
    Function.Injective (X.presheaf.map (eqToHom p).op).hom := by
  subst p
  first
  | (intro a b hab; simpa using hab)
  | (simp only [eqToHom_refl, op_id, Functor.map_id, CommRingCat.hom_id]; exact Function.injective_id)

private theorem isAbelianScheme_pullback' {S₀ S : Scheme.{0}} {B : Over S₀} [GrpObj B] (t : S ⟶ S₀)
    (hB : IsAbelianScheme B) : IsAbelianScheme ((Over.pullback t).obj B) := by
  have h1 := hB.smooth
  have h2 := hB.proper
  have h3 := hB.geomConnected
  have h4 := hB.comm
  constructor
  case comm =>
    first
    | infer_instance
    | exact Functor.obj.instIsCommMonObj _
  case smooth =>
    show Smooth (pullback.snd B.hom t)
    first
    | infer_instance
    | exact MorphismProperty.pullback_snd _ _ h1
  case proper =>
    show IsProper (pullback.snd B.hom t)
    first
    | infer_instance
    | exact MorphismProperty.pullback_snd _ _ h2
  case geomConnected =>
    show GeometricallyConnected (pullback.snd B.hom t)
    first
    | infer_instance
    | exact MorphismProperty.pullback_snd _ _ h3

theorem appTop_surjective (hG : Out.GlobalFnsSt) {S₀ : Scheme.{0}} {B : Over S₀} [GrpObj B]
    (hB : IsAbelianScheme B) {S X : Scheme.{0}} {t : S ⟶ S₀} {π : X ⟶ B.left} {f : X ⟶ S}
    (h : IsPullback π f B.hom t) : Function.Surjective f.appTop.hom := by
  have key : Function.Surjective (pullback.snd B.hom t).appTop.hom :=
    (hG S ((Over.pullback t).obj B) (isAbelianScheme_pullback' t hB)).2
  rw [← h.isoPullback_hom_snd]
  exact surjective_appTop_comp _ _ (surjective_appTop_of_iso _) key

theorem app_surjective : Out.GlobalFnsSt → ∀ (S₀ : Scheme.{0}) (B : Over S₀) [GrpObj B], IsAbelianScheme B → ∀ (S X : Scheme.{0}) (t : S ⟶ S₀) (π : X ⟶ B.left) (f : X ⟶ S), IsPullback π f B.hom t → ∀ U : S.Opens, Function.Surjective (f.app U).hom := by
  intro hG S₀ B _ hB S X t π f h U
  have hP : IsPullback ((f ⁻¹ᵁ U).ι ≫ π) (f ∣_ U) B.hom (U.ι ≫ t) :=
    (isPullback_morphismRestrict f U).flip.paste_horiz h
  have hres := appTop_surjective hG hB hP
  rw [morphismRestrict_appTop] at hres
  have hV := surjective_of_comp_surjective_of_injective _ _ (injective_presheaf_map_eqToHom _) hres
  change Function.Surjective (f.app (U.ι ''ᵁ ⊤)).hom at hV
  rwa [Scheme.Opens.ι_image_top] at hV

end GlobalTheory.BaseChangeFns
end
end
