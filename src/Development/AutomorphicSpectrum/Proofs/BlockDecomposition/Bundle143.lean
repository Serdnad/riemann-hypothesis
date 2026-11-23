module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle126
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeStair

theorem stCol : CrystallineSemistableComparison.E.StCol := by
  intro R _ C _ F T hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k z
    funext s
    change ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((T.K 0).map (GlobalTheory.CatH.toLast i s)).hom (T.ι _ (z (GlobalTheory.CatH.face i s))) =
      T.ι _ (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        (F.map (GlobalTheory.CatH.toLast i s)).hom (z (GlobalTheory.CatH.face i s)))

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hG.ι_nat]
  · intro s k a
    funext t
    change ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((T.K (s + 1)).map (GlobalTheory.CatH.toLast i t)).hom (T.dv s _ (a (GlobalTheory.CatH.face i t))) =
      T.dv s _ (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((T.K s).map (GlobalTheory.CatH.toLast i t)).hom (a (GlobalTheory.CatH.face i t)))

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hG.dv_nat]
  · intro k x y h
    funext s
    exact hG.inj _ (congrFun h s)
  · intro k x
    constructor
    · intro h
      have hz : ∀ s, ∃ z, T.ι _ z = x s := fun s => (hG.ex0 _ (x s)).1 (congrFun h s)
      choose z hz using hz
      exact ⟨z, funext hz⟩
    · rintro ⟨z, rfl⟩
      funext s
      exact (hG.ex0 _ _).2 ⟨_, rfl⟩
  · intro s k x
    constructor
    · intro h
      have hz : ∀ t, ∃ a, T.dv s _ a = x t := fun t => (hG.ex s _ (x t)).1 (congrFun h t)
      choose a ha using hz
      exact ⟨a, funext ha⟩
    · rintro ⟨a, rfl⟩
      funext t
      exact (hG.ex s _ _).2 ⟨_, rfl⟩

end GlobalTheory.CompanionTheory.EdgeStair
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeStair

theorem stEx_of_stCol : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StEx := by
  intro hcol R _ C _ F T hG s
  obtain ⟨hι, hdv, hinj, hex0, hex⟩ := hcol R C F T hG
  induction s with
  | zero =>
    intro k j hsk x hv hd
    have hjk : j = k := by omega
    subst hjk
    obtain ⟨z, hz⟩ := (hex0 j x).1 hv
    refine ⟨z, ?_, ⟨rfl, hz⟩⟩
    apply hinj (j + 1)
    rw [← hι, hz, hd, map_zero]
  | succ s ih =>
    intro k j hsk x hv hd
    obtain ⟨a, ha⟩ := (hex s k x).1 hv
    have h1 : T.dvC s (k + 1) ((-1 : ℤ) ^ k • d (T.K s) k a) = 0 := by
      rw [map_zsmul, ← hdv, ha, hd, smul_zero]
    have h2 : d (T.K s) (k + 1) ((-1 : ℤ) ^ k • d (T.K s) k a) = 0 := by
      rw [map_zsmul, d_d, smul_zero]
    obtain ⟨z, hz, hst⟩ := ih (k + 1) j (by omega) _ h1 h2
    exact ⟨z, hz, ⟨a, ha, hst⟩⟩

end GlobalTheory.CompanionTheory.EdgeStair
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem stTop_of_stCol : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StTop := by
  intro hCol R _ C _ F T hT j z hz s
  obtain ⟨hι, hdv, -, hex0, hex⟩ := hCol R C F T hT
  induction s with
  | zero =>
    intro k x hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨(hex0 j _).2 ⟨_, rfl⟩, by rw [hι, hz, map_zero]⟩
  | succ s ih =>
    intro k x hx
    obtain ⟨a, rfl, ha⟩ := hx
    have h1 := (ih (k + 1) _ ha).1
    rw [map_zsmul] at h1
    have h2 : T.dvC s (k + 1) (d _ k a) = 0 :=
      (IsUnit.smul_eq_zero ((isUnit_neg_one (α := ℤ)).pow k)).1 h1
    exact ⟨(hex s k _).2 ⟨a, rfl⟩, by rw [hdv]; exact h2⟩

end GlobalTheory.CompanionTheory.EdgeMap
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeStair

theorem stUniq : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StUniq := by
  intro hcol R _ C _ F T hT j z
  obtain ⟨hι, hdv, hinj, hex0, hex⟩ := hcol R C F T hT
  have key : ∀ (s k : ℕ) (x : Cn (T.K s) k), T.St z s k x → T.BZ s k x → z ∈ (cx F).B j := by
    intro s
    induction s with
    | zero =>
      intro k x hS hB
      obtain ⟨h, rfl⟩ := hS
      subst h
      cases j with
      | zero =>
        have h0 : T.ιC 0 z = 0 := hB
        have hz : z = 0 := hinj 0 (by rw [h0, map_zero])
        rw [hz]
        exact Submodule.zero_mem _
      | succ k =>
        obtain ⟨b, hb, hdb⟩ := hB
        obtain ⟨z', rfl⟩ := (hex0 k b).1 hb
        refine (⟨z', ?_⟩ : z ∈ LinearMap.range (d F k))
        apply hinj (k + 1)
        rw [← hι]
        exact hdb
    | succ s ih =>
      intro k x hS hB
      obtain ⟨a, rfl, hS'⟩ := hS
      cases k with
      | zero =>
        exact ih 1 _ hS' ⟨a, hB, by simp⟩
      | succ k =>
        obtain ⟨b, hb, hdb⟩ := hB
        obtain ⟨b', rfl⟩ := (hex s k b).1 hb
        refine ih (k + 2) _ hS' ⟨(-1 : ℤ) ^ (k + 1) • (a - d _ k b'), ?_, ?_⟩
        · rw [map_zsmul, map_sub, ← hdv, hdb, sub_self, smul_zero]
        · rw [map_zsmul, map_sub, d_d, sub_zero]
  intro s k x hS hB
  exact key s k x hS hB

end GlobalTheory.CompanionTheory.EdgeStair
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.Staircase

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem term_ιC {F : C ⥤ ModuleCat.{0} R} (T : Res.{1} F) (hT : T.Good) {p n : ℕ}
    (s : ComposableArrows C n) (z : Cn F p) (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    term (T.K 0) s (T.ιC p z) g hg = T.ι _ (term F s z g hg) :=
  (hT.ι_nat _ _).symm

theorem term_dvC {F : C ⥤ ModuleCat.{0} R} (T : Res.{1} F) (hT : T.Good) (t : ℕ) {p n : ℕ}
    (s : ComposableArrows C n) (a : Cn (T.K t) p) (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    term (T.K (t + 1)) s (T.dvC t p a) g hg = T.dv t _ (term (T.K t) s a g hg) :=
  (hT.dv_nat t _ _).symm

theorem sign_cancel {i k r : ℕ} (h : i + k = r) : (-1 : ℤ) ^ r * (-1 : ℤ) ^ i = (-1 : ℤ) ^ k := by
  subst h
  rw [pow_add, mul_comm ((-1 : ℤ) ^ i), mul_assoc, ← mul_pow]
  simp

theorem stCupB : CupLeib.{1} → StCol → StCupB := by
  intro hL hC R _ C _ F₁ F₂ F₃ T₁ T₂ T₃ P μ g₁ g₂ i j n hn z z' hz t
  induction t with
  | zero =>
    intro k r h y hy
    obtain ⟨rfl, rfl⟩ := hy
    subst h
    subst hn
    refine ⟨rfl, ?_⟩
    funext s
    change T₃.ι _ (P.μ _ (term F₁ s z _ _) (term F₂ s z' _ _)) =
      (μ.μ 0 0 0 (zero_add 0)).μ _ (term (T₁.K 0) s (T₁.ιC i z) _ _) (term (T₂.K 0) s (T₂.ιC _ z') _ _)
    rw [term_ιC T₁ g₁, term_ιC T₂ g₂]
    exact (μ.ι _ _ _).symm
  | succ t ih =>
    intro k r h y hy
    obtain ⟨a, rfl, ha⟩ := hy
    have hd : d (T₁.K 0) i (T₁.ιC i z) = 0 := by
      rw [(hC R C F₁ T₁ g₁).1, hz, map_zero]
    refine ⟨(μ.μ 0 t t (zero_add t)).cupC h (T₁.ιC i z) a, ?_, ?_⟩
    · funext s
      change T₃.dv t _ ((μ.μ 0 t t (zero_add t)).μ _ (term (T₁.K 0) s (T₁.ιC i z) _ _) (term (T₂.K t) s a _ _)) =
        (μ.μ 0 (t + 1) (t + 1) (zero_add (t + 1))).μ _ (term (T₁.K 0) s (T₁.ιC i z) _ _)
          (term (T₂.K (t + 1)) s (T₂.dvC t k a) _ _)
      rw [μ.leib 0 t t (zero_add t), term_dvC T₂ g₂, term_ιC T₁ g₁,
        (g₁.ex0 _ _).mpr ⟨_, rfl⟩, map_zero, LinearMap.zero_apply, zero_add, pow_zero, one_smul]
    · have e := hL R C (T₁.K 0) (T₂.K t) (T₃.K t) (μ.μ 0 t t (zero_add t)) i k r h (T₁.ιC i z) a
      have key := ih (k + 1) (r + 1) (by omega) ((-1 : ℤ) ^ k • d (T₂.K t) k a) ha
      have e' : (-1 : ℤ) ^ r • d (T₃.K t) r ((μ.μ 0 t t (zero_add t)).cupC h (T₁.ιC i z) a) =
          (μ.μ 0 t t (zero_add t)).cupC (show i + (k + 1) = r + 1 by omega) (T₁.ιC i z)
            ((-1 : ℤ) ^ k • d (T₂.K t) k a) := by
        rw [e, hd, map_zero, LinearMap.zero_apply, zero_add, smul_smul, sign_cancel h, map_zsmul]
      rw [e']
      exact key

end GlobalTheory.CompanionTheory.Staircase
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtaleChernClass

open GlobalTheory.CatH (face toLast)

universe w

section Cochains

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{w} R)

theorem d_zero_apply (f : Cn F 0) (s : ComposableArrows C 1) :
    d F 0 f s = (show F.obj (s.obj (Fin.last 1)) from f (face 0 s)) - (show F.obj (s.obj (Fin.last 1)) from (F.map (s.map' 0 1)).hom (f (face 1 s))) := by
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (f (face i s)) = _
  rw [Fin.sum_univ_two]
  have e0 : toLast (0 : Fin 2) s = 𝟙 _ := s.map_id _
  have e1 : toLast (1 : Fin 2) s = s.map' 0 1 := rfl
  rw [e0, e1, F.map_id]
  simp [sub_eq_add_neg]
  rfl

theorem d_one_apply (f : Cn F 1) (s : ComposableArrows C 2) :
    d F 1 f s = (show F.obj (s.obj (Fin.last 2)) from f (face 0 s)) - (show F.obj (s.obj (Fin.last 2)) from f (face 1 s)) +
      (show F.obj (s.obj (Fin.last 2)) from (F.map (s.map' 1 2)).hom (f (face 2 s))) := by
  change ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (f (face i s)) = _
  rw [Fin.sum_univ_three]
  have e0 : toLast (0 : Fin 3) s = 𝟙 _ := s.map_id _
  have e1 : toLast (1 : Fin 3) s = 𝟙 _ := s.map_id _
  have e2 : toLast (2 : Fin 3) s = s.map' 1 2 := rfl
  rw [e0, e1, e2, F.map_id]
  simp [sub_eq_add_neg]
  rfl

end Cochains

theorem close_sum {M : Type*} [AddCommGroup M] (tce tbe tbc kv kw ku kvw i : M)
    (h₁ : tce - tbe + tbc = kv + kw - kvw) (h₂ : kvw = ku + i) :
    (-1 : ℤ) ^ 1 • ((tce - kw) - (tbe - ku) + (tbc - kv)) = i := by
  have e : tce = kv + kw - kvw + tbe - tbc := by rw [← h₁]; abel
  rw [e, h₂]
  simp only [pow_one, neg_smul, one_smul]
  abel

theorem u_congr {X : Scheme.{0}} (D : LineData X) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y}
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) (ha : a = a') (hb : b = b') :
    D.u a b h = D.u a' b' h' := by
  subst ha hb; rfl

theorem etale_chern_class_eq_kummer_class : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.ResGood → CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.FirstChernCoboundary → CrystallineSemistableComparison.E.KumPow →
    CrystallineSemistableComparison.E.EtaleFirstChernKummer := by
  intro hES hRG hSC hCP hKP hGen hKum hC1 q _ C _ P X Y D L hL hInv x hx z Λ
  obtain ⟨a, η, θ, hRep, hηn, hθn, hdη, hdiff, hcoc⟩ := hCP hC1 q X D L hL hInv x hx
  have hθc : ∀ (V : Scheme.{0}) (b b' c : V ⟶ D.Y) (h : b ≫ D.f = c ≫ D.f) (h' : b' ≫ D.f = c ≫ D.f),
      b = b' → θ V b c h = θ V b' c h' := by
    intro V b b' c h h' e
    subst e
    rfl
  have hG : (P.res 1).Good := hRG hGen q C P 1
  obtain ⟨hιd, hdd, hinj, -, -⟩ := hSC ℤ C P.L (P.res 1) hG
  have hpp : ∀ {c c' : C} (φ : c ⟶ c'), ((P.S.map φ).unop ≫ Λ.p c) ≫ D.f = Λ.p c' ≫ D.f := by
    intro c c' φ
    rw [Category.assoc, Λ.hp, Λ.hp, Y.nat]
  let A₀ : ∀ {c c' : C} (φ : c ⟶ c'), Sec ((res _ (tw q 1)).X 0) (P.U c') := fun {c c'} φ =>
    θ _ ((P.S.map φ).unop ≫ Λ.p c) (Λ.p c') (hpp φ) - kumT q _ (Λ.r φ)
  let a₁ : Cn ((P.res 1).K 1) 0 := fun s => η _ (Λ.p (s.obj 0))
  let a₀ : Cn ((P.res 1).K 0) 1 := fun s => A₀ (s.map' 0 1)
  have h1 : (P.res 1).dvC 1 0 a₁ = Y.glob 1 2 a := by
    funext s
    refine (hdη _ (Λ.p (s.obj 0))).trans ?_
    rw [Λ.hp]
    rfl
  have h2 : (-1 : ℤ) ^ 0 • d ((P.res 1).K 1) 0 a₁ = (P.res 1).dvC 0 1 a₀ := by
    funext s
    rw [pow_zero, one_smul, d_zero_apply]
    have e := hdiff _ ((P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) (Λ.p (s.obj 1)) (hpp (s.map' 0 1)) _ (Λ.hr _)
    rw [← hηn] at e
    exact e
  have h3 : (-1 : ℤ) ^ 1 • d ((P.res 1).K 0) 1 a₀ = (P.res 1).ιC 2 z := by
    funext s
    rw [Pi.smul_apply, d_one_apply]
    let g := (P.S.map (s.map' 1 2)).unop
    have hg : g ≫ (P.S.map (s.map' 0 1)).unop = (P.S.map (s.map' 0 2)).unop := by
      have e : s.map' 0 2 = s.map' 0 1 ≫ s.map' 1 2 := s.map_comp _ _
      rw [e, P.S.map_comp, unop_comp]
    have hb : g ≫ (P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0) =
        (P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0) := by
      rw [← Category.assoc, hg]
    have hbc' : (g ≫ (P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) ≫ D.f = (g ≫ Λ.p (s.obj 1)) ≫ D.f := by
      have e : ((P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) ≫ D.f = Λ.p (s.obj 1) ≫ D.f := hpp (s.map' 0 1)
      rw [Category.assoc g, e, Category.assoc]
    have hbc : ((P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0)) ≫ D.f = (g ≫ Λ.p (s.obj 1)) ≫ D.f := by
      rw [← hb]
      exact hbc'
    let v := Units.map g.appTop.hom.toMonoidHom (Λ.r (s.map' 0 1))
    let w := Λ.r (s.map' 1 2)
    let u := Λ.r (s.map' 0 2)
    have hv : v ^ q = D.u _ _ hbc := by
      change Units.map g.appTop.hom.toMonoidHom (Λ.r (s.map' 0 1)) ^ q = _
      rw [← map_pow, Λ.hr, ← D.nat]
      exact u_congr D _ _ hb rfl
    have hw : w ^ q = D.u (g ≫ Λ.p (s.obj 1)) (Λ.p (s.obj 2)) (hpp (s.map' 1 2)) := Λ.hr _
    have hc := hcoc _ _ _ _ hbc (hpp (s.map' 1 2)) v w hv hw
    have hk := hKP hKum q _ (P.ζ (s.obj (Fin.last 2))) (z s) (v * w * u⁻¹) u (Λ.hz s)
    rw [inv_mul_cancel_right] at hk
    have hn : ((((P.res 1).K 0).map (s.map' 1 2)).hom (a₀ (face 2 s))) =
        θ _ ((P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0)) (g ≫ Λ.p (s.obj 1)) hbc - kumT q _ v := by
      have t₁ : Sec.res g (θ _ ((P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) (Λ.p (s.obj 1)) (hpp (s.map' 0 1))) =
          θ _ ((P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0)) (g ≫ Λ.p (s.obj 1)) hbc :=
        (hθn _ _ g _ _ _ hbc').trans (hθc _ _ _ _ _ _ hb)
      have t₂ : Sec.res g (kumT q _ (Λ.r (s.map' 0 1))) = kumT q _ v := (hKum q).1 _ _ g _ (P.ζ _).2.1
      exact (map_sub _ _ _).trans (congrArg₂ (· - ·) t₁ t₂)
    rw [hn]
    exact close_sum _ _ _ _ _ _ _ _ hc hk
  have hSt : (P.res 1).St z 2 0 (Y.glob 1 2 a) := ⟨a₁, h1, a₀, h2.symm, rfl, h3.symm⟩
  have hz : d P.L 2 z = 0 := by
    apply hinj 3
    rw [map_zero, ← hιd, ← h3, map_smul, d_d, smul_zero]
  exact ⟨hz, ((hES hGen q C P X Y 1 2 x).2 _ ⟨a, hRep, z, hz, hSt, rfl⟩).symm⟩

end GlobalTheory.CompanionTheory.EtaleChernClass
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GlobRel

theorem subsingleton_H_of_retract {R : Type} [CommRing R] {K L : Cx R}
    (φ : Cx.Hom K L (RingHom.id R)) (ψ : Cx.Hom L K (RingHom.id R))
    (h : ∀ n x, ψ.f n (φ.f n x) = x) (n : ℕ) (hL : Subsingleton (L.H n)) : Subsingleton (K.H n) := by
  have key : ∀ a : K.H n, ψ.mapH n (φ.mapH n a) = a := by
    intro a
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    change Submodule.Quotient.mk (ψ.mapZ n (φ.mapZ n z)) = Submodule.Quotient.mk z
    congr 1
    exact Subtype.ext (h n z.1)
  refine ⟨fun a b => ?_⟩
  rw [← key a, ← key b, Subsingleton.elim (φ.mapH n a) (φ.mapH n b)]

theorem subsingleton_HU_iter {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
    (F : C ⥤ ModuleCat.{0} R) (A B : ObjectProperty C) (P : ObjectProperty A.FullSubcategory)
    (hBA : ∀ T, B T → A T) (hP : ∀ T : A.FullSubcategory, P T ↔ B T.obj) (j : ℕ)
    (hB : Subsingleton (HU F B j)) : Subsingleton (HU (A.ι ⋙ F) P j) := by
  let G : B.FullSubcategory ⥤ P.FullSubcategory :=
    P.lift (A.lift B.ι fun T => hBA _ T.property) fun T => (hP _).2 T.property
  let G' : P.FullSubcategory ⥤ B.FullSubcategory :=
    B.lift (P.ι ⋙ A.ι) fun T => (hP _).1 T.property
  let m : CH.Mor (P.ι ⋙ A.ι ⋙ F) (B.ι ⋙ F) (RingHom.id R) := ⟨G, fun _ => LinearMap.id, fun _ _ => rfl⟩
  let m' : CH.Mor (B.ι ⋙ F) (P.ι ⋙ A.ι ⋙ F) (RingHom.id R) := ⟨G', fun _ => LinearMap.id, fun _ _ => rfl⟩
  exact subsingleton_H_of_retract m.hom m'.hom (fun n x => funext fun s => rfl) j hB

theorem glob_van_rel : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type} [Fintype ι]
    (W : ι → ObjectProperty C) (hW : ∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T') (s : ℕ),
    ((∀ S : Finset ι, S.Nonempty → ∀ j < s, Subsingleton (HU F (capS W S) j)) →
      ∀ j < s, Subsingleton (CH.H ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ F) j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (capS W S) j)) →
      ∀ j, Subsingleton (CH.H ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ F) j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j > s, Subsingleton (HU F (capS W S) j)) →
      ∀ j, s + Fintype.card ι ≤ j → Subsingleton (CH.H ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ F) j)) := by
  intro R _ C _ F ι _ W hW s
  let U' : ι → ObjectProperty (ObjectProperty.FullSubcategory fun T : C => ∃ α, W α T) :=
    fun α T => W α T.obj
  have hU : ∀ α, Cosieve (U' α) := fun α T T' f h => hW α f.hom h T'.property
  have hc : ∀ T, ∃ α, U' α T := fun T => T.property
  have tr : ∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (capS W S) j) →
      Subsingleton (HU ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ F) (capS U' S) j) := by
    intro S hS j h
    obtain ⟨a, ha⟩ := hS
    exact subsingleton_HU_iter F _ (capS W S) (capS U' S) (fun T hT => ⟨a, hT a ha⟩)
      (fun T => Iff.rfl) j h
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.cech_vanishing_from_cover ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ F) U' hU hc s
  exact ⟨fun h j hj => h1 (fun S hS j hj => tr S hS j (h S hS j hj)) j hj,
    fun h j => h2 (fun S hS j => tr S hS j (h S hS j)) j,
    fun h j hj => h3 (fun S hS j hj => tr S hS j (h S hS j hj)) j hj⟩

end GlobalTheory.CompanionTheory.GlobRel
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CoordRes

theorem etale_rs {X : Scheme.{0}} {V W : X.Opens} (h : W ≤ V) (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    (rs h).Etale := by
  have key := HasRingHomProperty.appLE @Etale (𝟙 X) inferInstance ⟨V, hV⟩ ⟨W, hW⟩ h
  have e : Scheme.Hom.appLE (𝟙 X) V W h = X.presheaf.map (homOfLE h).op := by
    simp [Scheme.Hom.appLE] <;> rfl
  rw [e] at key
  exact key

theorem rs_comp_strV {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V W : X.Opens}
    (h : W ≤ V) : (rs h).comp (strV q V) = strV q W := by
  simp only [rs, strV]
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.appLE_map]

theorem main : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {V W : X.Opens} {d : ℕ}
    (c : Coord q V d) (h : W ≤ V) (hW : IsAffineOpen W), ∃ c' : Coord q W d, ∀ i, c'.t i = rs h (c.t i) := by
  intro O _ X q V W d c h hW
  refine ⟨⟨hW, fun i => rs h (c.t i), ?_⟩, fun i => rfl⟩
  have e1 : MvPolynomial.eval₂Hom (strV q W) (fun i => rs h (c.t i)) =
      (rs h).comp (MvPolynomial.eval₂Hom (strV q V) c.t) := by
    rw [MvPolynomial.comp_eval₂Hom, rs_comp_strV]
  rw [e1]
  exact RingHom.Etale.stableUnderComposition _ _ c.etale (etale_rs h c.affine hW)

end GlobalTheory.CompanionTheory.CoordRes
end
