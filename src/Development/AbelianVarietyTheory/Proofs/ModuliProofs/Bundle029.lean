module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.Moduli.LevelAction

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem exists_inv_sabMap {S : Scheme.{0}} {t t' : SAB H S} (m : SABMap t' t (𝟙 S)) (i : SABMap t t (𝟙 S))
    (hi : i.φ = 𝟙 _) : ∃ k : SABMap t t' (𝟙 S), m.φ ≫ k.φ = 𝟙 _ := by
  have i' : {n : SABMap t t (𝟙 S ≫ 𝟙 S) // n.φ = 𝟙 _} := by
    rw [Category.comp_id]; exact ⟨i, hi⟩
  obtain ⟨k, hk⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m i'.1
  rw [i'.2] at hk
  refine ⟨k, ?_⟩
  haveI : IsIso m.φ := m.cart.1.isIso_fst_of_isIso
  rw [← cancel_mono m.φ, Category.assoc, ← hk, Category.comp_id, Category.id_comp]

theorem exists_comp_sabMap {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''}
    {f : S' ⟶ S} {g : S'' ⟶ S'} (m' : SABMap t'' t' g) (m : SABMap t' t f) {h : S'' ⟶ S} (e : g ≫ f = h) :
    ∃ n : SABMap t'' t h, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m'

section Add

variable {L Q : Type} [AddCommGroup L] [Group Q] {w : L → Q}

theorem map_zero_of_add (h : ∀ a c, w (a + c) = w a * w c) : w 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact left_eq_mul.mp this

theorem map_nsmul_of_add (h : ∀ a c, w (a + c) = w a * w c) (n : ℕ) (a : L) : w (n • a) = w a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, map_zero_of_add h]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

theorem map_eq_of_sub (h : ∀ a c, w (a + c) = w a * w c) {a c : L} (e : w (a - c) = 1) : w a = w c := by
  rw [← sub_add_cancel a c, h, e, _root_.one_mul]

end Add

theorem mem_of_modN (l : Level H) {x : D.La} (h : D.ModN l.M x) : x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨b, rfl⟩ := h
  have h₁ : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]; exact Ideal.mem_span_singleton_self _
  have h₂ : (l.M : 𝓞 E) ∈ l.Mb := by
    refine Submodule.mul_induction_on h₁ (fun x hx y _ => l.Mb.mul_mem_right y hx) fun x y hx hy => l.Mb.add_mem hx hy
  have h₃ : l.M • b = (l.M : 𝓞 E) • b := (Nat.cast_smul_eq_nsmul (𝓞 E) l.M b).symm
  rw [h₃]
  exact Submodule.smul_mem_smul h₂ Submodule.mem_top

section Obj

variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem eta_congr (o : Obj D l b s) {x y : D.La} (h : x - y ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    o.eta x = o.eta y := map_eq_of_sub o.eta_add (o.eta_ker _ h)

theorem etaA_congr (o : Obj D l b s) {x y : D.La} (h : D.ModN l.A (x - y)) :
    o.etaA x = o.etaA y := by
  obtain ⟨c, hc⟩ := h
  exact map_eq_of_sub o.etaA_add (by rw [hc, o.etaA_ker])

end Obj

def Twists {l : Level H} (Xo : Moduli D l) (g : Sim D) (f : Xo.X ⟶ Xo.X) : Prop :=
  f ≫ Xo.s = Xo.s ∧ ∃ ν : SABMap Xo.univ.t Xo.univ.t f,
    (∀ a, (Xo.univ.eta (g.f l.M a)).left ≫ ν.φ = f ≫ (Xo.univ.eta a).left) ∧
    ∀ a, (Xo.univ.etaA (g.f l.A a)).left ≫ ν.φ = f ≫ (Xo.univ.etaA a).left

theorem exists_twists {l : Level H} (Xo : Moduli D l) (g : Sim D) (hred : IsReduced Xo.X)
    (i : SABMap Xo.univ.t Xo.univ.t (𝟙 _)) (hi : i.φ = 𝟙 _)
    (o' : Obj D l (baseKA l) Xo.s) (m : SABMap o'.t Xo.univ.t (𝟙 _))
    (h₁ : ∀ a, (o'.eta a).left ≫ m.φ = (Xo.univ.eta (g.f l.M a)).left)
    (h₂ : ∀ a, (o'.etaA a).left ≫ m.φ = (Xo.univ.etaA (g.f l.A a)).left) : ∃ f, Twists Xo g f := by
  obtain ⟨f, ⟨hf, ⟨n⟩⟩, -⟩ := Xo.rep _ Xo.s hred o'
  obtain ⟨k, hk⟩ := exists_inv_sabMap m i hi
  obtain ⟨ν, hν⟩ := exists_comp_sabMap k n.toSABMap (Category.id_comp f)
  refine ⟨f, hf, ν, fun a => ?_, fun a => ?_⟩
  · rw [hν, ← h₁, Category.assoc, ← Category.assoc m.φ, hk, Category.id_comp]; exact n.eta a
  · rw [hν, ← h₂, Category.assoc, ← Category.assoc m.φ, hk, Category.id_comp]; exact n.etaA a

theorem comp_eq_id_of_twists {l : Level H} (Xo : Moduli D l) {g g' : Sim D} (hred : IsReduced Xo.X)
    (i : ObjMap Xo.univ Xo.univ (𝟙 _)) {f f' : Xo.X ⟶ Xo.X} (h : Twists Xo g f) (h' : Twists Xo g' f')
    (hM : ∀ a, D.ModN l.M (g.f l.M (g'.f l.M a) - a)) (hA : ∀ a, D.ModN l.A (g.f l.A (g'.f l.A a) - a)) :
    f ≫ f' = 𝟙 _ := by
  obtain ⟨hf, ν, e₁, e₂⟩ := h
  obtain ⟨hf', ν', e₁', e₂'⟩ := h'
  obtain ⟨n, hn⟩ := exists_comp_sabMap ν ν' rfl
  refine (Xo.rep _ Xo.s hred Xo.univ).unique ⟨by rw [Category.assoc, hf', hf], ⟨⟨n, fun a => ?_, fun a => ?_⟩⟩⟩
    ⟨Category.id_comp _, ⟨i⟩⟩
  · show _ ≫ n.φ = _
    rw [hn, Category.assoc, ← e₁', ← Category.assoc, ← Category.assoc, ← e₁,
      eta_congr Xo.univ (mem_of_modN l (hM a))]
  · show _ ≫ n.φ = _
    rw [hn, Category.assoc, ← e₂', ← Category.assoc, ← Category.assoc, ← e₂, etaA_congr Xo.univ (hA a)]

theorem zeta_pow_div {A A₂ : ℕ} (hA : 0 < A₂) (h : A ∣ A₂) : zeta A₂ ^ (A₂ / A) = zeta A := by
  obtain ⟨d, rfl⟩ := h
  have hA' : 0 < A := Nat.pos_of_mul_pos_right hA
  have hd : 0 < d := Nat.pos_of_mul_pos_left hA
  rw [Nat.mul_div_cancel_left _ hA', zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  have : (A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hA'.ne'
  have : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  push_cast
  field_simp

theorem modN_tower (g : Sim D) {n m : ℕ} (hm : 0 < m) (h : n ∣ m) (a : D.La) : D.ModN n (g.f m a - g.f n a) := by
  obtain ⟨d, rfl⟩ := h
  exact g.tower n d (Nat.pos_of_mul_pos_right hm) (Nat.pos_of_mul_pos_left hm) a

theorem sec_ext {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {x y : 𝟙_ (Over S') ⟶ t'.G} (h : x.left ≫ m.φ = y.left ≫ m.φ) : x = y :=
  Over.OverMorphism.ext (m.cart.1.hom_ext h (by rw [Over.w x, Over.w y]))

def lowerBase {l l₂ : Level H} (jK : KA l →+* KA l₂) : Base l (KA l₂) where
  unit := (baseKA l₂).unit
  ρ := (baseKA l₂).ρ
  ρ_sq := (baseKA l₂).ρ_sq
  ζ := jK (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective jK.injective

theorem lowerBase_zeta {l l₂ : Level H} (jK : KA l →+* KA l₂) (hl : l.A ∣ l₂.A)
    (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) :
    (lowerBase jK).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := by
  apply Subtype.ext
  have h₁ : (((lowerBase jK).ζ : KA l₂) : ℂ) = zeta l.A := hj (baseKA l).ζ
  have h₂ : (((baseKA l₂).ζ : KA l₂) : ℂ) = zeta l₂.A := rfl
  rw [h₁, SubmonoidClass.coe_pow, h₂, zeta_pow_div l₂.A_pos hl]

theorem lowerBase_rho {l l₂ : Level H} (jK : KA l →+* KA l₂)
    (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) : jK (baseKA l).ρ = (lowerBase jK).ρ := by
  apply Subtype.ext
  have h₁ : (((lowerBase jK).ρ : KA l₂) : ℂ) = H.rt0 := rfl
  have h₂ : (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl
  rw [hj, h₁, h₂]

theorem similitude_acts : (∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o₂ : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o : Obj D l b s) (m : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (g : Sim D), 1 ≤ D.p + D.q → (l.A : ℤ) ∣ g.ν l.A - 1 → ∃ (o' : Obj D l b s) (m : SABMap o'.t o.t (𝟙 S)), (∀ a, (o'.eta a).left ≫ m.φ = (o.eta (g.f l.M a)).left) ∧ ∀ a, (o'.etaA a).left ≫ m.φ = (o.etaA (g.f l.A a)).left) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r := by
  intro hsm hcomp hlow hrep hsim halg E _ _ _ H D l l₂ Xo Xo₂ hpq hl r jK m ⟨hj, hr, hE, hEA⟩ g ⟨hν, hgM, hgA⟩
  have hred : IsReduced Xo₂.X := by
    haveI := Xo₂.smooth
    exact (hsm _ _ Xo₂.s (SmoothOfRelativeDimension.smooth D.dim _)).1
  have hM₂ : 0 < l₂.M := lt_of_lt_of_le (by norm_num) l₂.three_le
  obtain ⟨i, hi⟩ := (hcomp E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ Xo₂.univ Xo₂.univ Xo₂.univ).1
  obtain ⟨g', hg'⟩ := (halg E H D hpq).2.2.2 g
  have hν' : (l₂.A : ℤ) ∣ g'.ν l₂.A - 1 := by
    have h₁ := (hg' l₂.A l₂.A_pos).2
    have : g'.ν l₂.A - 1 = (g.ν l₂.A * g'.ν l₂.A - 1) - (g.ν l₂.A - 1) * g'.ν l₂.A := by ring
    rw [this]
    exact dvd_sub h₁ (hν.mul_right _)
  obtain ⟨o₁, m₁, a₁, b₁⟩ := hsim E H D l₂ _ _ _ _ Xo₂.univ g hpq hν
  obtain ⟨o₂, m₂, a₂, b₂⟩ := hsim E H D l₂ _ _ _ _ Xo₂.univ g' hpq hν'
  obtain ⟨f, hf⟩ := exists_twists Xo₂ g hred i.toSABMap hi o₁ m₁ a₁ b₁
  obtain ⟨f', hf'⟩ := exists_twists Xo₂ g' hred i.toSABMap hi o₂ m₂ a₂ b₂
  refine ⟨⟨f, f', comp_eq_id_of_twists Xo₂ hred i hf hf' (fun a => ((hg' _ hM₂).1 a).2)
      (fun a => ((hg' _ l₂.A_pos).1 a).2),
    comp_eq_id_of_twists Xo₂ hred i hf' hf (fun a => ((hg' _ hM₂).1 a).1)
      (fun a => ((hg' _ l₂.A_pos).1 a).1)⟩, hf, ?_⟩
  show f ≫ r = r
  obtain ⟨hfs, ν, e₁, e₂⟩ := hf
  have hζ := lowerBase_zeta jK hl.2.2 hj
  obtain ⟨o, k, c₁, c₂⟩ := hlow E H D l l₂ _ (lowerBase jK) (baseKA l₂) _ _ Xo₂.univ hl rfl hζ
  obtain ⟨id₀, hid₀⟩ := (hcomp E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o o).1
  obtain ⟨k', hk'⟩ := exists_inv_sabMap k id₀.toSABMap hid₀
  have d₁ : ∀ a, (o.eta a).left ≫ k'.φ = (Xo₂.univ.eta a ^ (l₂.M / l.M)).left := fun a => by
    rw [← (c₁ a).trans (Category.id_comp _), Category.assoc, hk', Category.comp_id]
  have d₂ : ∀ a, (o.etaA a).left ≫ k'.φ = (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left := fun a => by
    rw [← (c₂ a).trans (Category.id_comp _), Category.assoc, hk', Category.comp_id]
  obtain ⟨n, hn⟩ := exists_comp_sabMap k' m (Category.id_comp r)
  obtain ⟨n₀, hn₀⟩ := exists_comp_sabMap k' ν (Category.id_comp f)
  obtain ⟨n', hn'⟩ := exists_comp_sabMap n₀ m rfl
  have t₁ : ∀ a, Xo₂.univ.eta a ^ (l₂.M / l.M) = Xo₂.univ.eta (g.f l₂.M ((l₂.M / l.M) • a)) := fun a => by
    rw [map_nsmul, map_nsmul_of_add Xo₂.univ.eta_add]
    apply sec_ext m
    rw [hE, hE, eta_congr Xo.univ (mem_of_modN l (modN_tower g hM₂ hl.1 a)), eta_congr Xo.univ (hgM a)]
  have t₂ : ∀ a, Xo₂.univ.etaA a ^ (l₂.A / l.A) = Xo₂.univ.etaA (g.f l₂.A ((l₂.A / l.A) • a)) := fun a => by
    rw [map_nsmul, map_nsmul_of_add Xo₂.univ.etaA_add]
    apply sec_ext m
    rw [hEA, hEA, etaA_congr Xo.univ (modN_tower g l₂.A_pos hl.2.2 a), etaA_congr Xo.univ (hgA a)]
  refine (hrep E H D l Xo _ (lowerBase jK) jK _ _ o hred (lowerBase_rho jK hj) rfl).unique
    ⟨by rw [Category.assoc, hr, ← Category.assoc, hfs], ⟨⟨n', fun a => ?_, fun a => ?_⟩⟩⟩
    ⟨hr, ⟨⟨n, fun a => ?_, fun a => ?_⟩⟩⟩
  · show _ ≫ n'.φ = _
    rw [hn', hn₀, ← Category.assoc, ← Category.assoc, d₁, t₁, e₁, map_nsmul_of_add Xo₂.univ.eta_add,
      Category.assoc, hE, Category.assoc]
  · show _ ≫ n'.φ = _
    rw [hn', hn₀, ← Category.assoc, ← Category.assoc, d₂, t₂, e₂, map_nsmul_of_add Xo₂.univ.etaA_add,
      Category.assoc, hEA, Category.assoc]
  · show _ ≫ n.φ = _
    rw [hn, ← Category.assoc, d₁, hE]
  · show _ ≫ n.φ = _
    rw [hn, ← Category.assoc, d₂, hEA]

end GlobalTheory.Moduli.LevelAction
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem exists_prime_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ n : ℕ, n.Prime ∧ Odd n ∧
      ∀ A₀ : ℕ, 0 < A₀ → ∃ l₀ l₂ : Level H, l₀.M = n ∧ l₀.A = A₀ ∧ l₀.Dvd l₂ ∧ l.Dvd l₂ := by
  intro E _ _ _ H l
  have hM1 : l.M ≠ 1 := by have := l.three_le; omega
  obtain ⟨n, hn, hnM⟩ := Nat.exists_prime_and_dvd hM1
  have hodd : Odd n := Odd.of_dvd_nat l.odd hnM
  have h3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases hodd with ⟨k, hk⟩
    omega
  refine ⟨n, hn, hodd, fun A₀ hA₀ => ?_⟩
  have hmap : (l.Mb ⊔ Ideal.span {(n : 𝓞 E)}).map (H.bar : 𝓞 E →+* 𝓞 E) =
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ⊔ Ideal.span {(n : 𝓞 E)} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast]
  have hMn : Ideal.span {(l.M : 𝓞 E)} ≤ Ideal.span {(n : 𝓞 E)} :=
    Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hnM)
  refine ⟨⟨n, h3, hodd, l.Mb ⊔ Ideal.span {(n : 𝓞 E)}, ?_, ?_, ?_, A₀, hA₀⟩,
    ⟨l.M, l.three_le, l.odd, l.Mb, l.fromK, l.prod, l.coprime, Nat.lcm l.A A₀, Nat.lcm_pos l.A_pos hA₀⟩,
    rfl, rfl, ⟨hnM, le_sup_left, Nat.dvd_lcm_right _ _⟩, ⟨dvd_rfl, le_rfl, Nat.dvd_lcm_left _ _⟩⟩
  · apply le_antisymm
    · apply sup_le
      · refine l.fromK.le.trans (Ideal.span_mono ?_)
        intro a ha
        exact ⟨Ideal.mem_sup_left ha.1, ha.2⟩
      · refine Ideal.span_mono ?_
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        exact ⟨Ideal.mem_sup_right (Ideal.mem_span_singleton_self _), natCast_mem _ _⟩
    · exact Ideal.span_le.2 fun a ha => ha.1
  · rw [hmap, Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, l.prod]
    set N : Ideal (𝓞 E) := Ideal.span {(n : 𝓞 E)}
    apply le_antisymm
    · refine sup_le (sup_le hMn ?_) (sup_le ?_ ?_) <;>
        first | exact Ideal.mul_le_left | exact Ideal.mul_le_right
    · calc N = N * (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) := by rw [l.coprime, Ideal.mul_top]
        _ = l.Mb * N ⊔ N * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [Ideal.mul_sup, mul_comm N l.Mb]
        _ ≤ _ := sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_right)
  · rw [hmap, eq_top_iff, ← l.coprime]
    exact sup_le_sup le_sup_left le_sup_left

end GlobalTheory.ZM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SymSignature

theorem finite_hom (E : Type) [Field E] [NumberField E] (K : Type) [Field K] :
    Finite (𝓞 E →+* K) :=
  Finite.of_injective (fun τ : 𝓞 E →+* K => τ.toIntAlgHom) RingHom.toIntAlgHom_injective

theorem card_hom_le (E : Type) [Field E] [NumberField E] (K : Type) [Field K] :
    Nat.card (𝓞 E →+* K) ≤ Module.finrank ℚ E := by
  rw [← RingOfIntegers.rank E]
  exact (Nat.card_le_card_of_injective (fun τ : 𝓞 E →+* K => τ.toIntAlgHom)
    RingHom.toIntAlgHom_injective).trans (card_algHom_le_finrank ℤ (𝓞 E) K)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem root_ne_neg (H : Host E) {K : Type} [Field K] [CharZero K] {ρ : K}
    (hρ : ρ ^ 2 = -(H.d : K)) : -ρ ≠ ρ := by
  intro h
  have h0 : ρ = 0 := by linear_combination (-1 / 2 : K) * h
  rw [h0] at hρ
  have : (H.d : K) = 0 := by linear_combination hρ
  exact H.d_prime.ne_zero (by exact_mod_cast this)

theorem map_rt (H : Host E) {K : Type} [Field K] {ρ : K} (hρ : ρ ^ 2 = -(H.d : K))
    (τ : 𝓞 E →+* K) : τ H.rt = ρ ∨ τ H.rt = -ρ := by
  have := congrArg τ H.rt_sq
  rw [map_pow, map_neg, map_natCast, ← hρ] at this
  exact sq_eq_sq_iff_eq_or_eq_neg.mp this

theorem card_type_le (H : Host E) {K : Type} [Field K] [CharZero K] {ρ : K}
    (hρ : ρ ^ 2 = -(H.d : K)) :
    Nat.card {τ : 𝓞 E →+* K // τ H.rt = ρ} ≤ Module.finrank ℚ E / 2 := by
  haveI := finite_hom E K
  have hne := root_ne_neg H hρ
  let f : {τ : 𝓞 E →+* K // τ H.rt = ρ} ⊕ {τ : 𝓞 E →+* K // τ H.rt = ρ} → (𝓞 E →+* K) :=
    Sum.elim (fun τ => τ.1) (fun τ => τ.1.comp (H.bar : 𝓞 E →+* 𝓞 E))
  have hf : Function.Injective f := by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exfalso
      have := RingHom.congr_fun h H.rt
      simp [f, HostModel.bar_rt, a.2, b.2] at this
      exact hne this.symm
    · exfalso
      have := RingHom.congr_fun h H.rt
      simp [f, HostModel.bar_rt, a.2, b.2] at this
      exact hne this
    · refine congrArg Sum.inr (Subtype.ext (RingHom.ext fun x => ?_))
      have := RingHom.congr_fun h (H.bar x)
      simpa [f, HostModel.bar_bar] using this
  have h1 := (Nat.card_le_card_of_injective f hf).trans (card_hom_le E K)
  rw [Nat.card_sum] at h1
  omega

theorem finrank_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q g : ℕ) (K : Type) [Field K] [CharZero K] (ρ : K) (ty : Fin g → (𝓞 E →+* K)) (V : Submodule K (Matrix (Fin g) (Fin g) K)), ρ ^ 2 = -(H.d : K) → (∀ τ : 𝓞 E →+* K, (τ H.rt = ρ → Nat.card {i // ty i = τ} = p) ∧ (τ H.rt ≠ ρ → Nat.card {i // ty i = τ} = q)) → (∀ Θ ∈ V, Θ.IsSymm ∧ ∀ a : 𝓞 E, Matrix.diagonal (fun i => ty i a) * Θ = Θ * (Matrix.diagonal (fun i => ty i (H.bar a))).transpose) → Module.finrank K V ≤ Module.finrank ℚ E / 2 * p * q := by
  intro E _ _ _ H p q g K _ _ ρ ty V hρ hty hV
  classical
  haveI := finite_hom E K
  have hne := root_ne_neg H hρ
  let S : Type := Σ τ : {τ : 𝓞 E →+* K // τ H.rt = ρ},
    {i // ty i = τ.1} × {j // ty j = τ.1.comp (H.bar : 𝓞 E →+* 𝓞 E)}
  haveI : Fintype S := Fintype.ofFinite S
  haveI : Fintype {τ : 𝓞 E →+* K // τ H.rt = ρ} := Fintype.ofFinite _
  have hS : Nat.card S = Nat.card {τ : 𝓞 E →+* K // τ H.rt = ρ} * p * q := by
    rw [Nat.card_sigma, Finset.sum_congr rfl (g := fun _ => p * q)]
    · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, Nat.mul_assoc]
    · intro τ _
      rw [Nat.card_prod, (hty τ.1).1 τ.2, (hty _).2]
      simpa [HostModel.bar_rt, τ.2] using hne
  let f : V →ₗ[K] (S → K) :=
    { toFun := fun Θ s => Θ.1 s.2.1.1 s.2.2.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro Θ h0
    obtain ⟨hs, hc⟩ := hV Θ.1 Θ.2
    have key : ∀ i j, ty i H.rt = ρ → Θ.1 i j = 0 := by
      intro i j hi
      by_contra hij
      refine hij (congrFun h0 ⟨⟨ty i, hi⟩, ⟨i, rfl⟩, ⟨j, RingHom.ext fun a => ?_⟩⟩)
      have := congrFun (congrFun (hc (H.bar a)) i) j
      rw [Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal,
        HostModel.bar_bar, mul_comm] at this
      exact (mul_left_cancel₀ hij this).symm
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    show Θ.1 i j = 0
    rcases map_rt H hρ (ty i) with hi | hi
    · exact key i j hi
    · by_contra hij
      have := congrFun (congrFun (hc H.rt) i) j
      rw [Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal,
        HostModel.bar_rt, mul_comm, map_neg, hi] at this
      have hj : ty j H.rt = ρ := (neg_injective (mul_left_cancel₀ hij this)).symm
      exact hij ((hs.apply j i).trans (key j i hj))
  have h1 := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, hS] at h1
  exact h1.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (card_type_le H hρ)))

end GlobalTheory.SymSignature
end
