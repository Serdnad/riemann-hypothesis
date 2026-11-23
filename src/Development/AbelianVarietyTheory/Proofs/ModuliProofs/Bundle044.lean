module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertDataOfIsoCube
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevelCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sab_comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    (m' : SABMap t'' t' g) (m : SABMap t' t f) {e : S'' ⟶ S} (he : g ≫ f = e) :
    ∃ n : SABMap t'' t e, n.φ = m'.φ ≫ m.φ := by
  subst he
  exact sabComp pullCubComp E H S S' S'' t t' t'' f g m m'

theorem sab_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {e : S'' ⟶ S}
    (m : SABMap t' t f) (n : SABMap t'' t e) (g : S'' ⟶ S') (he : g ≫ f = e) :
    ∃ m' : SABMap t'' t' g, m'.φ ≫ m.φ = n.φ := by
  subst he
  obtain ⟨m', h⟩ := sabCancel pullCubCancel E H S S' S'' t t' t'' f g m n
  exact ⟨m', h.symm⟩

theorem sec_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    (m' : SABMap t'' t' g) (m : SABMap t' t f) (x : 𝟙_ (Over S'') ⟶ t''.G) (y : 𝟙_ (Over S') ⟶ t'.G)
    (h : x.left ≫ m'.φ ≫ m.φ = g ≫ y.left ≫ m.φ) : x.left ≫ m'.φ = g ≫ y.left := by
  apply m.cart.1.hom_ext
  · simpa only [Category.assoc] using h
  · have a₁ : x.left ≫ t''.G.hom = 𝟙 _ := Over.w x
    have a₂ : y.left ≫ t'.G.hom = 𝟙 _ := Over.w y
    rw [Category.assoc, m'.cart.1.w, ← Category.assoc, a₁, Category.assoc, a₂]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem sec_pow {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (x : 𝟙_ (Over S') ⟶ t'.G) (y : 𝟙_ (Over S) ⟶ t.G)
    (h : x.left ≫ m.φ = f ≫ y.left) (k : ℕ) : (x ^ k).left ≫ m.φ = f ≫ (y ^ k).left := by
  let U : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ 𝟙_ (Over S) :=
    Over.homMk f ((Category.comp_id _).trans (Category.id_comp _).symm)
  have e : pushHom m.cart _ x = preHom U y := Over.OverMorphism.ext h
  have e' : pushHom m.cart _ (x ^ k) = preHom U (y ^ k) := by rw [map_pow, map_pow, e]
  exact congrArg (fun z => z.left) e'

theorem zeta_dvd {a b : ℕ} (hb : 0 < b) (h : a ∣ b) : zeta a = zeta b ^ (b / a) := by
  obtain ⟨k, rfl⟩ := h
  have ha : a ≠ 0 := by rintro rfl; simp at hb
  have hk : k ≠ 0 := by rintro rfl; simp at hb
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha), zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  push_cast
  field_simp

noncomputable def baseOf (l : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) : Base l F where
  unit n hn := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hn.ne')
  ρ := (IntermediateField.inclusion h).toRingHom (baseKA l).ρ
  ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  ζ := (IntermediateField.inclusion h).toRingHom (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective (RingHom.injective _)

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

theorem spMap_inclusion_self {F : IntermediateField ℚ ℂ} (h : F ≤ F) :
    spMap (IntermediateField.inclusion h).toRingHom = 𝟙 (Sp F) := by
  rw [← spMap_id']
  exact congrArg spMap (RingHom.ext fun x => Subtype.ext (IntermediateField.coe_inclusion h x))

theorem baseOf_rho_coe (l : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) :
    (((baseOf l F h).ρ : F) : ℂ) = H.rt0 := IntermediateField.coe_inclusion h (baseKA l).ρ

theorem baseOf_rho (l l₂ : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) (h₂ : KA l₂ ≤ F) :
    (baseOf l F h).ρ = (baseOf l₂ F h₂).ρ :=
  Subtype.ext ((baseOf_rho_coe l F h).trans (baseOf_rho_coe l₂ F h₂).symm)

theorem baseOf_zeta (l l₂ : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) (h₂ : KA l₂ ≤ F) (hd : l.A ∣ l₂.A) :
    (baseOf l F h).ζ = (baseOf l₂ F h₂).ζ ^ (l₂.A / l.A) := Subtype.ext (by
  rw [IntermediateField.coe_pow]
  exact (IntermediateField.coe_inclusion h _).trans ((zeta_dvd l₂.A_pos hd).trans
    (congrArg (· ^ (l₂.A / l.A)) (IntermediateField.coe_inclusion h₂ (baseKA l₂).ζ).symm)))

def ObjCompSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)

variable {D : Datum H} {l l₂ : Level H}

def Represents {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {s : X ⟶ Sp B} (o : Obj D l b s) : Prop :=
  ∀ (S : Scheme.{0}) (s' : S ⟶ Sp B) (o' : Obj D l b s'), IsReduced S →
    ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o' o f)

theorem represents_pullback (hC : ObjCompSt) (Xo : Moduli D l) {B : Type} [CommRing B] {b : Base l B} (j : KA l →+* B)
    (hR : ∀ (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S →
      ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f))
    {s : pullback Xo.s (spMap j) ⟶ Sp B} (hs : s = pullback.snd _ _) (o : Obj D l b s)
    (mo : ObjMap o Xo.univ (pullback.fst _ _)) : Represents o := by
  subst hs
  intro S s' o' hS
  obtain ⟨g, ⟨hg, ⟨u⟩⟩, huniq⟩ := hR S s' o' hS
  have hl : pullback.lift g s' hg ≫ pullback.fst _ _ = g := pullback.lift_fst _ _ _
  refine ⟨pullback.lift g s' hg, ⟨pullback.lift_snd _ _ _, ?_⟩, ?_⟩
  · obtain ⟨u', -⟩ := ((hC E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o o').2 _ (pullback.lift g s' hg) mo).2
      (hl.symm ▸ u)
    exact ⟨u'⟩
  · rintro f ⟨hf, ⟨v⟩⟩
    apply pullback.hom_ext
    · rw [hl]
      obtain ⟨v', -⟩ := ((hC E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o o').2 _ f mo).1 v
      exact huniq _ ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, hf], ⟨v'⟩⟩
    · rw [hf, pullback.lift_snd]

theorem iso_cover (hC : ObjCompSt) {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} (k k' : ℕ)
    {X X₂ Y : Scheme.{0}} {s : X ⟶ Sp B} {r : X₂ ⟶ X} {π : Y ⟶ X} (o : Obj D l b s) (o₂ : Obj D l₂ b₂ (r ≫ s))
    (oc : Obj D l₂ b₂ (π ≫ s)) (o₁ : Obj D l b (π ≫ s)) (n : ObjMap o₁ o π)
    (m : SABMap o₂.t o.t r) (mc : SABMap oc.t o.t π)
    (hm : (∀ a, (o₂.eta a ^ k).left ≫ m.φ = r ≫ (o.eta a).left) ∧
      (∀ a, (o₂.etaA a ^ k').left ≫ m.φ = r ≫ (o.etaA a).left))
    (hmc : (∀ a, (oc.eta a ^ k).left ≫ mc.φ = π ≫ (o.eta a).left) ∧
      (∀ a, (oc.etaA a ^ k').left ≫ mc.φ = π ≫ (o.etaA a).left))
    (hX : Represents o) (hX₂ : Represents o₂) (rX₂ : IsReduced X₂) (rY : IsReduced Y)
    (rig : ∀ m m' : SABMap o₁.t o.t π, (∀ a, ∃ σ, (o₁.eta a).left ≫ m.φ = σ ∧ (o₁.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ)
    (univ : ∀ (T : Scheme.{0}) (f : T ⟶ X) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f),
      (∀ a, (o'.eta a ^ k).left ≫ m'.φ = f ≫ (o.eta a).left) ∧
        (∀ a, (o'.etaA a ^ k').left ≫ m'.φ = f ≫ (o.etaA a).left) →
      ∃! h : T ⟶ Y, h ≫ π = f ∧ ∃ u : ObjMap o' oc h, u.toSABMap.φ ≫ mc.φ = m'.φ) :
    ∃ h : X₂ ⟶ Y, IsIso h ∧ h ≫ π = r := by
  obtain ⟨h, ⟨hh, u, hu⟩, -⟩ := univ X₂ r o₂ m hm
  obtain ⟨g, ⟨hg, ⟨w⟩⟩, -⟩ := hX₂ Y (π ≫ s) oc rY
  obtain ⟨v, hv⟩ := sab_cancel mc n.toSABMap (𝟙 Y) (Category.id_comp _)
  have v₁ : ∀ a, (o₁.eta a).left ≫ v.φ = (oc.eta a ^ k).left := fun a =>
    (sec_cancel v mc _ _ (by rw [hv, hmc.1, Category.id_comp]; exact n.eta a)).trans (Category.id_comp _)
  have v₂ : ∀ a, (o₁.etaA a).left ≫ v.φ = (oc.etaA a ^ k').left := fun a =>
    (sec_cancel v mc _ _ (by rw [hv, hmc.2, Category.id_comp]; exact n.etaA a)).trans (Category.id_comp _)
  obtain ⟨vw, hvw⟩ := sab_comp v w.toSABMap (Category.id_comp g)
  have key : ∀ (e : Y ⟶ X) (he : g ≫ r = e), ∃ z : ObjMap o₁ o e, z.toSABMap.φ = v.φ ≫ w.toSABMap.φ ≫ m.φ := by
    intro e he
    obtain ⟨z, hz⟩ := sab_comp vw m he
    rw [hvw, Category.assoc] at hz
    refine ⟨⟨z, fun a => ?_, fun a => ?_⟩, hz⟩
    · show _ ≫ z.φ = _
      rw [hz, ← Category.assoc, v₁, ← Category.assoc, sec_pow w.toSABMap _ _ (w.eta a), Category.assoc, hm.1,
        ← Category.assoc, he]
    · show _ ≫ z.φ = _
      rw [hz, ← Category.assoc, v₂, ← Category.assoc, sec_pow w.toSABMap _ _ (w.etaA a), Category.assoc, hm.2,
        ← Category.assoc, he]
  have hgr : g ≫ r = π := by
    obtain ⟨z, -⟩ := key _ rfl
    exact (hX Y (π ≫ s) o₁ rY).unique ⟨by rw [Category.assoc, hg], ⟨z⟩⟩ ⟨rfl, ⟨n⟩⟩
  obtain ⟨z, hz⟩ := key _ hgr
  have hzn : z.toSABMap.φ = n.toSABMap.φ := rig _ _ fun a => ⟨_, z.eta a, n.eta a⟩
  have : IsIso v.φ := v.cart.1.isIso_fst_of_isIso
  have hwm : w.toSABMap.φ ≫ m.φ = mc.φ := by
    rw [← cancel_epi v.φ, ← hz, hzn, hv]
  refine ⟨h, ⟨g, ?_, ?_⟩, hh⟩
  · obtain ⟨x, -⟩ := ((hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ o₂ oc o₂).2 g h w).1 u
    obtain ⟨y, -⟩ := (hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ o₂ o₂ o₂).1
    exact (hX₂ X₂ (r ≫ s) o₂ rX₂).unique
      ⟨by rw [Category.assoc, hg, ← Category.assoc, hh], ⟨x⟩⟩ ⟨Category.id_comp _, ⟨y⟩⟩
  · obtain ⟨x, hx⟩ := ((hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ oc o₂ oc).2 h g u).1 w
    obtain ⟨y, hy⟩ := (hC E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ oc oc oc).1
    exact (univ Y π oc mc hmc).unique
      ⟨by rw [Category.assoc, hh, hgr], x, by rw [hx, Category.assoc, hu, hwm]⟩
      ⟨Category.id_comp _, y, by rw [hy, Category.id_comp]⟩

end GlobalTheory.LevelCover
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.PulledBiextFrame

open GlobalTheory.CubeValues GlobalTheory.SelfCube

def combUnif {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {K : Type} [Fintype K] (φ : K → (A.left ⟶ A.left))
    (p : K → (Fin g → ℂ) → (Fin g → ℂ)) (hd : ∀ k, Differentiable ℂ (p k)) (ε : K → ℤ)
    (hp : ∀ k z, (u.ex z).left ≫ φ k = (u.ex (p k z)).left) :
    HolUnif A (LB.LinComb L φ ε) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fun j z => ∏ k, u.fr (j k) (p k z) ^ ε k
  fr_hol := fun j => by
    have hD : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.LinComb L φ ε).U j →
        ∀ k, ⊤ ≤ (u.ex (p k z)).left ⁻¹ᵁ L.U (j k) := fun z hz k => by
      rw [← hp]; exact (le_preimage_wchart (u.ex z).left L φ j).1 hz k
    refine differentiableOn_prod' _ fun k => DifferentiableOn.zpow
      ((u.fr_hol (j k)).comp (hd k).differentiableOn fun z hz => hD z hz k) ?_
    exact Or.inl fun z hz => u.fr_ne _ _ (hD z hz k)
  fr_ne := fun j z hz => by
    refine Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (u.fr_ne _ _ ?_)
    rw [← hp]; exact (le_preimage_wchart (u.ex z).left L φ j).1 hz k
  fr_compat := fun j j' z hz => by
    obtain ⟨h1, h2⟩ := (le_preimage_inf _ _ _).1 hz
    have e := val_linComb (u.ex z).left GlobalTheory.valAt'_rules L φ ε j j' h1 h2
    refine Eq.trans ?_ (congrArg (· * _) e.symm)
    simp only [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have a1 := (le_preimage_wchart (u.ex z).left L φ j).1 h1 k
    have a2 := (le_preimage_wchart (u.ex z).left L φ j').1 h2 k
    rw [hp] at a1 a2 ⊢
    rw [u.fr_compat _ _ _ ((le_preimage_inf _ _ _).2 ⟨a1, a2⟩), mul_zpow]

theorem exists_appellHumbert_frame :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ) (w : P.A ⟶ P.A) (F F' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)), u.IsAH Hm χ → (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → (∀ z, u.ex (F z) = u.ex z ≫ w) → F + F' = LinearMap.id → (∀ z z', hermForm Hm (F z) z' = hermForm Hm z (F' z')) → ∃ (u₁ : HolUnif P.A (cubeLB P.A ![𝟙 P.A, w] P.L) P.g) (χ₁ : u₁.Λ → ℂ), u₁.ex = u.ex ∧ u₁.Λ = u.Λ ∧ u₁.IsAH Hm χ₁ ∧ ∀ (l : u₁.Λ) (a b : u.Λ), (a : Fin P.g → ℂ) = l → (b : Fin P.g → ℂ) = F l → χ₁ l = (-1) ^ Ef a b := by
  intro _ _ _ _ P u Hm χ Ef w F F' ⟨hH, hpos, hχ, hfr⟩ hE hw hFF hadj
  classical
  have hv : ValueRules := GlobalTheory.valAt'_rules
  have hF : ∀ l ∈ u.Λ, F l ∈ u.Λ := fun l hl => by
    have h0 := hw 0
    rw [map_zero, ex_zero] at h0
    rw [← u.ker, hw, (u.ker l).2 hl, ← h0]
  have hsc := fun l m => semicharacter_rule hv P.isLB u hH χ hfr l m _ (hE l m)
  have hχ0 : ∀ l, χ l ≠ 0 := fun l h => by simpa [h] using hχ l
  let Y : Fin 2 → (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ) := ![LinearMap.id, F]
  have hy : ∀ k z, u.ex z ≫ (![𝟙 P.A, w] : Fin 2 → _) k = u.ex (Y k z) := by
    intro k z
    fin_cases k
    · exact Category.comp_id _
    · exact (hw z).symm
  let p : ULift.{0} (Finset (Fin 2)) → (Fin P.g → ℂ) → (Fin P.g → ℂ) := fun I z => ∑ k ∈ I.down, Y k z
  have hpd : ∀ I, Differentiable ℂ (p I) := fun I =>
    Differentiable.fun_sum fun k _ => (LinearMap.toContinuousLinearMap (Y k)).differentiable
  have hps : ∀ (I : ULift.{0} (Finset (Fin 2))) z,
      (u.ex z).left ≫ (psum P.A ![𝟙 P.A, w] I.down).left = (u.ex (p I z)).left := fun I z => by
    rw [← Over.comp_left, comp_psum u (u.ex z) _ (fun k => Y k z) (fun k => hy k z)]
  refine ⟨combUnif u _ p hpd _ hps, fun l : u.Λ => (-1) ^ Ef l ⟨F l, hF l l.2⟩, rfl, rfl,
    ⟨hH, hpos, fun l => by simp [norm_zpow], ?_⟩, ?_⟩
  · intro (l : u.Λ) j z hz
    have hc : ∀ I, ⊤ ≤ (u.ex (p I z)).left ⁻¹ᵁ P.L.U (j I) := fun I => by
      rw [← hps]; exact (le_preimage_wchart (u.ex z).left P.L _ j).1 hz I
    change ∏ I, u.fr (j I) (p I z) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      (-1) ^ Ef l ⟨F l, hF l l.2⟩ *
        Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) *
        ∏ I, u.fr (j I) (p I (z + l)) ^ ((-1 : ℤ) ^ (2 - I.down.card))
    rw [prod_finset_fin_two fun I => u.fr (j ⟨I⟩) (p ⟨I⟩ z) ^ ((-1 : ℤ) ^ (2 - I.card)),
      prod_finset_fin_two fun I => u.fr (j ⟨I⟩) (p ⟨I⟩ (z + l)) ^ ((-1 : ℤ) ^ (2 - I.card))]
    have p0 : ∀ x, p ⟨∅⟩ x = 0 := fun x => by simp [p]
    have p1 : ∀ x, p ⟨{0}⟩ x = x := fun x => by simp [p, Y]
    have p2 : ∀ x, p ⟨{1}⟩ x = F x := fun x => by simp [p, Y]
    have p3 : ∀ x, p ⟨{0, 1}⟩ x = x + F x := fun x => by simp [p, Y]
    have c1 := hc ⟨{0}⟩
    have c2 := hc ⟨{1}⟩
    have c3 := hc ⟨{0, 1}⟩
    rw [p1] at c1
    rw [p2] at c2
    rw [p3] at c3
    have e1 := hfr l _ _ c1
    have e2 := hfr ⟨F l, hF l l.2⟩ _ _ c2
    have e3 := hfr (l + ⟨F l, hF l l.2⟩) _ _ c3
    rw [hsc] at e3
    have k2 : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
    have s3 : z + F z + ((l + ⟨F l, hF l l.2⟩ : u.Λ) : Fin P.g → ℂ) = z + l + F (z + l) := by
      simp only [Submodule.coe_add, map_add (f := _)]; abel
    rw [s3] at e3
    have hsum : ∀ x y, hermForm Hm x (F y) + hermForm Hm (F x) y = hermForm Hm x y := fun x y => by
      rw [hadj, ← herm_add_right]
      exact congrArg _ (LinearMap.congr_fun hFF y)
    change _ = _ * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * _ at e1
    change _ = _ * Complex.exp (Real.pi * hermForm Hm (F z) (F l) +
      Real.pi / 2 * hermForm Hm (F l) (F l)) * u.fr _ (F z + F l) at e2
    change _ = _ * Complex.exp (Real.pi * hermForm Hm (z + F z) (l + F l) +
      Real.pi / 2 * hermForm Hm (l + F l) (l + F l)) * _ at e3
    rw [← map_add (f := _)] at e2
    have hx : Real.pi * hermForm Hm (z + F z) (l + F l) +
        Real.pi / 2 * hermForm Hm (l + F l) (l + F l) =
        (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) +
        (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) +
        (Real.pi * hermForm Hm (F z) (F l) + Real.pi / 2 * hermForm Hm (F l) (F l)) := by
      simp only [herm_add_left, herm_add_right]
      linear_combination (Real.pi : ℂ) * hsum z l + (Real.pi / 2 : ℂ) * hsum l l
    rw [hx, Complex.exp_add, Complex.exp_add (_ + _) (_ + _)] at e3
    simp only [p0, p1, p2, p3, k2, Finset.card_empty, Finset.card_singleton]
    rw [e1, e2, e3]
    have n1 := hχ0 l
    have n2 := hχ0 ⟨F l, hF l l.2⟩
    norm_num
    field_simp
  · intro (l : u.Λ) a b ha hb
    obtain rfl : a = l := Subtype.ext ha
    obtain rfl : b = ⟨F a, hF a a.2⟩ := Subtype.ext hb
    rfl

end GlobalTheory.PulledBiextFrame
end
end

section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HolPeriods

section HolTo

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {X : Scheme.{0}}

theorem isHolTo_congr {B : Set V} {y y' : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (hy : ∀ b ∈ B, y' b = y b) :
    IsHolTo B y' := by
  intro U f
  have hs : {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, hy b h1 ▸ h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hy b h1).symm ▸ h2⟩
  rw [hs]
  exact ⟨(h U f).1, (h U f).2.congr fun b hb => by rw [hy b hb.1]⟩

theorem isHolTo_comp {B : Set V} {C : Set W} {y : V → (Sp ℂ ⟶ X)} {φ : W → V} (h : IsHolTo B y)
    (hC : IsOpen C) (hφ : DifferentiableOn ℂ φ C) (hm : Set.MapsTo φ C B) :
    IsHolTo C (fun c => y (φ c)) := by
  intro U f
  have hs : {c ∈ C | ⊤ ≤ y (φ c) ⁻¹ᵁ U} = C ∩ φ ⁻¹' {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext c
    exact ⟨fun hc => ⟨hc.1, hm hc.1, hc.2⟩, fun hc => ⟨hc.1, hc.2.2⟩⟩
  refine ⟨?_, ?_⟩
  · rw [hs]; exact hφ.continuousOn.isOpen_inter_preimage hC (h U f).1
  · exact (h U f).2.comp (hφ.mono fun c hc => hc.1) fun c hc => ⟨hm hc.1, hc.2⟩

theorem isHolTo_of_local {B : Set V} {y : V → (Sp ℂ ⟶ X)}
    (h : ∀ b ∈ B, ∃ B' : Set V, b ∈ B' ∧ B' ⊆ B ∧ IsHolTo B' y) : IsHolTo B y := by
  intro U f
  have key : ∀ b ∈ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}, {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} ∈ nhds b ∧
      DifferentiableAt ℂ (fun b => valAt' (y b) U f) b := by
    intro b hb
    obtain ⟨B', hb', hsub, hB'⟩ := h b hb.1
    have hn := (hB' U f).1.mem_nhds (⟨hb', hb.2⟩ : b ∈ {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ U})
    exact ⟨Filter.mem_of_superset hn fun c hc => ⟨hsub hc.1, hc.2⟩, (hB' U f).2.differentiableAt hn⟩
  exact ⟨isOpen_iff_mem_nhds.2 fun b hb => (key b hb).1,
    fun b hb => (key b hb).2.differentiableWithinAt⟩

end HolTo

theorem exists_local_section {n : ℕ} {U : Set (Fin n → ℂ)} {F : (Fin n → ℂ) → (Fin n → ℂ)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {a : Fin n → ℂ} (ha : a ∈ U) (hb : Function.Bijective (fderiv ℂ F a)) :
    ∃ (W : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → (Fin n → ℂ)), IsOpen W ∧ F a ∈ W ∧ DifferentiableOn ℂ G W ∧
      ∀ w ∈ W, G w ∈ U ∧ F (G w) = w := by
  have han : AnalyticAt ℂ F a := GlobalTheory.SCV.analyticAt_of_differentiableOn hF (hU.mem_nhds ha)
  have hc : ContDiffAt ℂ ⊤ F a := han.contDiffAt
  let f' : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    (LinearEquiv.ofBijective (fderiv ℂ F a : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) hb).toContinuousLinearEquiv
  have hd : HasFDerivAt F (f' : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) a := by
    have : (f' : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F a := by ext1; rfl
    rw [this]; exact han.differentiableAt.hasFDerivAt
  have hinv := hc.to_localInverse hd (by simp)
  have hs := hc.hasStrictFDerivAt' hd (by simp)
  have h1 : ∀ᶠ w in nhds (F a), F (hc.localInverse hd (by simp) w) = w := hs.eventually_right_inverse
  have h2 : ∀ᶠ w in nhds (F a), hc.localInverse hd (by simp) w ∈ U := by
    have := hinv.continuousAt
    rw [ContinuousAt, hc.localInverse_apply_image] at this
    exact this (hU.mem_nhds ha)
  have h3 : ∀ᶠ w in nhds (F a), DifferentiableAt ℂ (hc.localInverse hd (by simp)) w :=
    (hinv.analyticAt.eventually_analyticAt).mono fun w hw => hw.differentiableAt
  obtain ⟨W, hW, hWo, hWa⟩ := eventually_nhds_iff.1 (h1.and (h2.and h3))
  exact ⟨W, _, hWo, hWa, fun w hw => (hW w hw).2.2.differentiableWithinAt,
    fun w hw => ⟨(hW w hw).2.1, (hW w hw).1⟩⟩

theorem exists_differentiableOn_transfer {V Λ : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [AddCommGroup Λ]
    {g : ℕ} {B : Set V} (hB : IsOpen B) {Q Q' : V → (Λ →+ (Fin g → ℂ))}
    (hQ : ∀ x, DifferentiableOn ℂ (fun b => Q b x) B) (hQ' : ∀ x, DifferentiableOn ℂ (fun b => Q' b x) B)
    {b₀ : V} (hb₀ : b₀ ∈ B) (hspan : Submodule.span ℝ (Set.range (Q b₀)) = ⊤)
    (k : V → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) (hk : ∀ b ∈ B, ∀ x, Q' b x = k b (Q b x)) :
    ∃ B' : Set V, IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧
      DifferentiableOn ℂ (fun bz : V × (Fin g → ℂ) => k bz.1 bz.2) (B' ×ˢ Set.univ) := by
  classical
  have hc : ∀ i : Fin g, ∃ c : Λ →₀ ℝ, (c.sum fun a r => r • Q b₀ a) = Pi.single i 1 := fun i =>
    Finsupp.mem_span_range_iff_exists_finsupp.1 (by rw [hspan]; trivial)
  choose c hc using hc
  let M : (V → (Λ →+ (Fin g → ℂ))) → V → ((Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) := fun R b =>
    ∑ i, (ContinuousLinearMap.proj i : (Fin g → ℂ) →L[ℂ] ℂ).smulRight
      (∑ a ∈ (c i).support, ((c i a : ℝ) : ℂ) • R b a)
  have hM : ∀ R : V → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => R b x) B) →
      DifferentiableOn ℂ (M R) B := by
    intro R hR
    refine DifferentiableOn.fun_sum fun i _ => ?_
    refine ((StrongDual.smulRightL ℂ (Fin g → ℂ) (Fin g → ℂ)
      (ContinuousLinearMap.proj i)).differentiable.comp_differentiableOn ?_)
    exact DifferentiableOn.fun_sum fun a _ => (hR a).fun_const_smul _
  have h0 : M Q b₀ = 1 := by
    ext1 z
    have : ∀ i, ∑ a ∈ (c i).support, ((c i a : ℝ) : ℂ) • Q b₀ a = Pi.single i 1 := fun i => by
      rw [← hc i]; simp [Finsupp.sum]
    simp only [M, this, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.one_apply]
    ext j; simp [Pi.single_apply]
  have hkM : ∀ b ∈ B, ∀ z, k b (M Q b z) = M Q' b z := by
    intro b hb z

    simp [M, map_sum, hk b hb]
  refine ⟨B ∩ M Q ⁻¹' {x | IsUnit x}, (hM Q hQ).continuousOn.isOpen_inter_preimage hB Units.isOpen,
    ⟨hb₀, by simp [h0]⟩, Set.inter_subset_left, ?_⟩
  have hd : DifferentiableOn ℂ (fun b => M Q' b * Ring.inverse (M Q b)) (B ∩ M Q ⁻¹' {x | IsUnit x}) := by
    refine ((hM Q' hQ').mono Set.inter_subset_left).mul fun b hb => ?_
    exact (differentiableAt_inverse hb.2).comp_differentiableWithinAt b
      ((hM Q hQ).mono Set.inter_subset_left b hb)
  have hd2 : DifferentiableOn ℂ (fun bz : V × (Fin g → ℂ) => (M Q' bz.1 * Ring.inverse (M Q bz.1)) bz.2)
      ((B ∩ M Q ⁻¹' {x | IsUnit x}) ×ˢ Set.univ) :=
    (hd.comp differentiableOn_fst (fun (bz : V × (Fin g → ℂ))
      (hbz : bz ∈ (B ∩ M Q ⁻¹' {x | IsUnit x}) ×ˢ Set.univ) => hbz.1)).clm_apply differentiableOn_snd
  refine hd2.congr fun bz hbz => ?_
  rw [ContinuousLinearMap.mul_apply, ← hkM _ hbz.1.1, ← ContinuousLinearMap.mul_apply,
    Ring.mul_inverse_cancel _ hbz.1.2, ContinuousLinearMap.one_apply]

theorem isDerivAt0_comp_equiv {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 (fun z => e (k z)) w v ↔ IsDerivAt0 e (k w) v := by
  have : ∀ (U : X.Opens) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (k z)) U f) 0 w =
      fderiv ℂ (fun z => valAt' (e z) U f) 0 (k w) := by
    intro U f
    have := k.toContinuousLinearEquiv.comp_right_fderiv (f := fun z => valAt' (e z) U f) (x := 0)
    have h2 := congrArg (fun L => L w) this
    simpa [Function.comp_def] using h2
  simp only [IsDerivAt0, map_zero, this]

end GlobalTheory.HolPeriods
end
