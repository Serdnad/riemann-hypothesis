module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2711
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle068
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsGenVal

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

structure VPre {O : Type} [CommRing O] (bar : O → O) (q : ℕ) {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ)
    (A : Type) [CommRing A] [IsLocalRing A] : Type 2 where
  posW : PosW W

  Y : Type 1

  V : Y → Type
  [ring : ∀ y, CommRing (V y)]
  [dom : ∀ y, IsDomain (V y)]
  [loc : ∀ y, IsLocalRing (V y)]
  cn : ∀ y, IsCN (V y)

  ev : ∀ y, A →+* V y
  ev_loc : ∀ y, IsLocalHom (ev y)

  X : Y → Type
  [add : ∀ y, AddCommGroup (X y)]
  [mod : ∀ y, Module O (X y)]
  [fin : ∀ y, Module.Finite O (X y)]
  [proj : ∀ y, Module.Projective O (X y)]
  [freeZ : ∀ y, Module.Free ℤ (X y)]
  [finZ : ∀ y, Module.Finite ℤ (X y)]
  rank_le : ∀ y, Module.finrank O (X y) ≤ q

  m : Y → ℕ

  t : ∀ y, Fin (m y) → V y
  t_mem : ∀ y i, t y i ∈ maximalIdeal (V y) ∧ t y i ≠ 0

  δ : ∀ y, Fin (m y) → LinearMap.BilinForm ℤ (X y)
  bal : ∀ y i, δ y i ∈ balForms bar (X y)
  nonneg : ∀ y i x, 0 ≤ δ y i x x
  pos : ∀ y x, x ≠ 0 → ∃ i, 0 < δ y i x x

  Q : Type

  u : ∀ y, (Fin s → X y) → Q → V y
  u_unit : ∀ y mu, ∃ c, IsUnit (u y mu c)

attribute [instance] VPre.ring VPre.dom VPre.loc VPre.add VPre.mod VPre.fin VPre.proj VPre.freeZ VPre.finZ

section
variable {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {A : Type} [CommRing A] [IsLocalRing A]

def VSys.pre {N₁ : ℕ} (Φ : VSys bar q W N₁ A) : VPre bar q W A where
  posW := Φ.posW
  Y := Φ.Y
  V := Φ.V
  cn := Φ.cn
  ev := Φ.ev
  ev_loc := Φ.ev_loc
  X := Φ.X
  rank_le := Φ.rank_le
  m := Φ.m
  t := Φ.t
  t_mem := Φ.t_mem
  δ := Φ.δ
  bal := Φ.bal
  nonneg := Φ.nonneg
  pos := Φ.pos
  Q := Φ.Q
  u := Φ.u
  u_unit := Φ.u_unit

namespace VPre
variable (Φ : VPre bar q W A)

def term (y : Φ.Y) (mu : Fin s → Φ.X y) (c : Φ.Q) : Φ.V y := Φ.u y mu c * mono W (Φ.t y) (Φ.δ y) mu

def abelian₂ : Prop :=
  ∃ C : ℕ, ∀ y, Φ.m y = 1 → ∀ i x, x ≠ 0 → ∃ h ∈ maximalIdeal A, Φ.ev y h ∣ Φ.t y i ^ (C * (Φ.δ y i x x).toNat)

def Four (N₁ : ℕ) : Prop :=
  ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ N₁ ∣ N ∧ ∃ k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y, k y₀ = LinearMap.id ∧
    (∀ y, IsUnimodMod O N (k y)) ∧ ∀ (l : ℕ) (a : Fin l × Fin s → Φ.X y₀) (c : Fin l → Φ.Q) (e : ℕ), ∃ f : A,
      ∀ (y : Φ.Y) (j : ℕ), ∃ S : Finset (Fin l × Fin s → Φ.X y), (↑S : Set _) ⊆ orbit O N₁ N (k y) a ∧
        (∀ mu ∈ orbit O N₁ N (k y) a, mu ∉ S → (j : ℤ) ≤ ∑ i, lin W mu (Φ.δ y i)) ∧
        Φ.ev y f - ∑ mu ∈ S, ∏ i, Φ.u y (fun v => mu (i, v)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun v => mu (i, v)) ∈
          maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y)

def IsClassSum (y : Φ.Y) (N : ℕ) (κ : Fin s → Φ.X y) (c : Φ.Q) {V' : Type} [CommRing V'] [IsLocalRing V']
    (io : Φ.V y →+* V') (x : V') : Prop :=
  ∀ j : ℕ, ∃ S : Finset (Fin s → Φ.X y), (∀ mu ∈ S, ∀ v, CongMod N (mu v) (κ v)) ∧
    (∀ mu, (∀ v, CongMod N (mu v) (κ v)) → mu ∉ S → (j : ℤ) ≤ ∑ i, qW W (Φ.δ y i) mu) ∧
    x - io (∑ mu ∈ S, Φ.term y mu c) ∈ maximalIdeal V' ^ j

def Exact (N₁ : ℕ) : Prop :=
  ∀ (y : Φ.Y) (κ : Fin s → Φ.X y) (c : Φ.Q), ∃ h : A, Φ.IsClassSum y N₁ κ c (RingHom.id _) (Φ.ev y h)

def ClassSums [IsDomain A] (N₁ : ℕ) : Prop :=
  ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ 1 ≤ N ∧ N₁ ∣ N ∧ ∃ k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y, k y₀ = LinearMap.id ∧
    (∀ y, IsUnimodMod O N (k y)) ∧ ∃ (L : Type) (_ : Field L) (_ : Algebra (FractionRing A) L) (_ : Algebra A L)
      (_ : IsScalarTower A (FractionRing A) L) (_ : FiniteDimensional (FractionRing A) L) (_ : IsGalois (FractionRing A) L)
      (𝔷 : Ideal (integralClosure A L)) (f : (Fin s → Φ.X y₀) → Φ.Q → integralClosure A L), 𝔷.IsMaximal ∧
      (∀ κ κ' c, (∀ v, CongMod N (κ v) (κ' v)) → f κ c = f κ' c) ∧
      (∀ y, ∃ (V' : Type) (_ : CommRing V') (_ : IsLocalRing V') (io : Φ.V y →+* V') (ev' : integralClosure A L →+* V'),
        io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal (Φ.V y), (I.map io).comap io = I) ∧
        ev'.comp (algebraMap A _) = io.comp (Φ.ev y) ∧ (maximalIdeal V').comap ev' = 𝔷 ∧
        ∀ κ c, Φ.IsClassSum y N (fun v => k y (κ v)) c io (ev' (f κ c))) ∧
      ∀ σ : L ≃ₐ[FractionRing A] L, (∀ x x' : integralClosure A L, (x' : L) = σ x → (x ∈ 𝔷 ↔ x' ∈ 𝔷)) →
        ∃ ga : Φ.X y₀ →ₗ[ℤ] Φ.X y₀, (∀ (b : O) x, CongMod N (ga (b • x)) (b • ga x)) ∧ (N : ℤ) ∣ LinearMap.det ga - 1 ∧
          (∀ x, CongMod N₁ (ga x) x) ∧ ∀ κ c, σ (f κ c : L) = (f (fun v => ga (κ v)) c : L)

def rescale (v : ∀ y, (Φ.V y)ˣ) : VPre bar q W A :=
  { Φ with
    u := fun y mu c => Φ.u y mu c * v y
    u_unit := fun y mu => (Φ.u_unit y mu).imp fun _ h => h.mul (v y).isUnit }

def toVSys (N₁ : ℕ) (hl : Φ.abelian₂) (hf : Φ.Four N₁) : VSys bar q W N₁ A where
  posW := Φ.posW
  Y := Φ.Y
  V := Φ.V
  cn := Φ.cn
  ev := Φ.ev
  ev_loc := Φ.ev_loc
  X := Φ.X
  rank_le := Φ.rank_le
  m := Φ.m
  t := Φ.t
  t_mem := Φ.t_mem
  δ := Φ.δ
  bal := Φ.bal
  nonneg := Φ.nonneg
  pos := Φ.pos
  Q := Φ.Q
  u := Φ.u
  u_unit := Φ.u_unit
  lam := hl
  four := hf

end VPre

end

namespace Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def IsThetaTerms₀ (D : DegPre V₁) (N₁ : ℕ) {X C : Type} [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V₁) : Prop :=
  ∃ (th : Fam D (FractionRing V₁) 1) (g : C → GtPtF D (FractionRing V₁)) (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A))
    (w : ∀ c, Frm D (FractionRing V₁) 1 (g c).b),
    (∀ c, (g c).b = toUnit _ ≫ b c) ∧ (∀ c, ∃ o, GtPtF.IsNsmul N₁ (g c) o ∧ o.IsZero) ∧
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ N₁ = 1 →
      ∃ c, p = toUnit _ ≫ b c) ∧
    (∀ c, (w c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
      val (w c) (𝟙 _) z J ^ (N₁ ^ 2) * val κ (g c).b.left z J = 1) ∧
    (∀ mu c, IsCoef 1 (g c) (w c) (e mu) (th.s (e mu)) (algebraMap V₁ (FractionRing V₁) (T mu c)))

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  (X₁ : Setup F W i) (z₁ : X₁.M.Z)

def RegAt (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) : Prop :=
  ∀ a ∈ X₁.S.R, a ∈ X₁.M.O ((jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V₁)))

variable (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁))

def HasTraitsR : Prop :=
  ∀ (T : Trait F) (ev : X₁.M.Z.presheaf.stalk z₁ →+* T.V), IsLocalHom ev → RegAt X₁ z₁ ev →
    jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = T.y ≫ i →
    ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃+ T.D.toPre.X), Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧
      Function.Injective f ∧ IsLocalHom f ∧ f.comp ev = Φ.ev y ∧
      ∀ k, Φ.t y k = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.β (e a) (e b)

def IsChartMemberP [IsLocalRing V] (N₁ : ℕ) (Q : Data V) (ξ : Sp V ⟶ Z) {m : ℕ} (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ Q.X) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m) : Prop :=
  Function.Injective ρ ∧ ρ.Finite ∧ spMap (Φ.ev y) ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = spMap ρ ≫ ξ ∧
    (∀ k, Φ.t y k = ρ (t (h k)) ∧ ∀ a b, Φ.δ y k a b = δ (h k) (e a) (e b)) ∧
    ∃ (D : DegPre (Φ.V y)) (e₈ : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e₈ ∧
      IsThetaTerms₀ D N₁ e₈ fun mu c => Φ.term y (fun a => e.symm (mu a)) c

end Sep

end GlobalTheory.Poinc
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.TraitWit

open GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R]

theorem comp_tensφ {S : Scheme.{0}} {B B' T : Over S} [GrpObj B] {r : ℕ} (pr : Fin r → (B' ⟶ B)) (x : T ⟶ B')
    (k : (Fin r × Fin r) × Fin 4) : x.left ≫ tensφ pr k = lamPts (x ≫ pr k.1.1) (x ≫ pr k.1.2) k.2 := by
  obtain ⟨⟨i, j⟩, k⟩ := k
  fin_cases k
  · exact congrArg (·.left) (MonObj.comp_mul x (pr i) (pr j))
  · rfl
  · rfl
  · exact congrArg (·.left) (MonObj.comp_one (M := B) x)

theorem formula_trans (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) {B' : Over (Sp R)} {L' : LB B'.left}
    (pr : Fin r → (B' ⟶ D.P.A)) {w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))} (hw : w.IsGen) (x : TK R ⟶ B')
    (y : Fin r → D.X) (hx : ∀ i, x ≫ pr i = toUnit (TK R) ≫ D.c (y i)) (z : (TK R).left) (J J₀) (hJ : Good D.P.L z J)
    (hJ₀ : Good D.P.L z J₀) (k k₀ : L'.ι) (hk : x.left z ∈ L'.U k) (hk₀ : x.left z ∈ L'.U k₀) :
    gm x.left z _ (w.s (fun a => J (x.left ≫ tensφ pr a), k)) * ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z J ^ W i j =
      (gm x.left z _ (L'.g k k₀))⁻¹ * (gm x.left z _ (w.s (fun a => J₀ (x.left ≫ tensφ pr a), k₀)) *
        ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z J₀ ^ W i j) := by
  let H : ((TK R).left ⟶ D.P.A.left) → ((TK R).left.presheaf.stalk z)ˣ := fun ψ => gm ψ z _ (D.P.L.g (J ψ) (J₀ ψ))
  let F : Fin r → Fin r → ((TK R).left.presheaf.stalk z)ˣ := fun i j =>
    ∏ a, H (lamPts (toUnit (TK R) ≫ D.c (y i)) (toUnit (TK R) ≫ D.c (y j)) a) ^ Oε a
  have h₁ : gm x.left z _ (w.s (fun a => J (x.left ≫ tensφ pr a), k)) =
      gm x.left z _ ((LB.LinComb D.P.L (tensφ pr) (tensε W)).g
        (fun a => J (x.left ≫ tensφ pr a)) (fun a => J₀ (x.left ≫ tensφ pr a))) *
      (gm x.left z _ (L'.g k k₀))⁻¹ *
      gm x.left z _ (w.s (fun a => J₀ (x.left ≫ tensφ pr a), k₀)) := by
    have hm : x.left z ∈ (LB.LinComb D.P.L (tensφ pr) (tensε W)).U (fun a => J (x.left ≫ tensφ pr a)) ⊓ L'.U k ⊓
        ((LB.LinComb D.P.L (tensφ pr) (tensε W)).U (fun a => J₀ (x.left ≫ tensφ pr a)) ⊓ L'.U k₀) :=
      ⟨⟨hJ.mem (tensφ pr) x.left, hk⟩, hJ₀.mem (tensφ pr) x.left, hk₀⟩
    have e := congrArg (gm x.left z _) (hw (fun a => J (x.left ≫ tensφ pr a), k)
      (fun a => J₀ (x.left ≫ tensφ pr a), k₀))
    exact (gm_res x.left z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_div L' _ x.left z _ _ hm) (gm_res x.left z _ hm _))))
  have h₂ : gm x.left z _ ((LB.LinComb D.P.L (tensφ pr) (tensε W)).g (fun a => J (x.left ≫ tensφ pr a))
      (fun a => J₀ (x.left ≫ tensφ pr a))) = ∏ i, ∏ j, F i j ^ W i j := by
    refine (gm_linComb D.P.L (tensφ pr) (tensε W) x.left z _ _ (hJ.mem (tensφ pr) x.left) (hJ₀.mem (tensφ pr) x.left)).trans ?_
    change ∏ a, H (x.left ≫ tensφ pr a) ^ tensε W a = _
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [comp_tensφ, hx, hx, ← zpow_mul, mul_comm]
    rfl
  have h₃ : ∀ i j, val (D.tau (y i) (y j)) (𝟙 _) z J = (F i j)⁻¹ * val (D.tau (y i) (y j)) (𝟙 _) z J₀ := fun i j => by
    obtain ⟨t, ht, hv⟩ := exists_tau_four D (y i) (y j)
    refine (hv _ _ z J hJ).symm.trans ((gen_trans ht (𝟙 _) z (hJ.mem _ _) (hJ₀.mem _ _)).trans
      (congrArg₂ (· * ·) ?_ (hv _ _ z J₀ hJ₀)))
    change ∏ a, H (𝟙 _ ≫ lamPts (toUnit (TK R) ≫ D.c (y i)) (toUnit (TK R) ≫ D.c (y j)) a) ^ negε a = _
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Category.id_comp, ← zpow_neg]
    congr 1
    fin_cases a <;> rfl
  refine (congrArg₂ (· * ·) (h₁.trans (congrArg (· * _ * _) h₂)) (Finset.prod_congr rfl fun i _ =>
    Finset.prod_congr rfl fun j _ => congrArg (· ^ W i j) (h₃ i j))).trans ?_
  simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_psi (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) {B' : Over (Sp R)} {L' : LB B'.left} (hL : L'.IsLB)
    (pr : Fin r → (B' ⟶ D.P.A)) {w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))} (hw : w.IsGen) (x : TK R ⟶ B')
    (y : Fin r → D.X) (hx : ∀ i, x ≫ pr i = toUnit (TK R) ≫ D.c (y i)) :
    ∃ t : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => x.left) (fun _ => -1)), t.IsGen ∧
      ∀ z J J', Good D.P.L z J → Good L' z J' → val t (𝟙 _) z J' =
        gm x.left z _ (w.s (fun a => J (x.left ≫ tensφ pr a), J' x.left)) *
          ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z J ^ W i j := by
  let z₀ : (TK R).left := closedPoint (FractionRing R)
  obtain ⟨J₀, hJ₀, -⟩ := exists_good _ D.P.isLB z₀ (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
  obtain ⟨J₁, hJ₁, -⟩ := exists_good _ hL z₀ (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
  obtain ⟨t, ht, hv⟩ := exists_gen_val (F := FractionRing R) hL (K := PUnit) (fun _ => x.left) (fun _ => -1) hJ₁
    (gm x.left z₀ _ (w.s (fun a => J₀ (x.left ≫ tensφ pr a), J₁ x.left)) *
      ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z₀ J₀ ^ W i j)
  refine ⟨t, ht, fun z J J' hJ hJ' => ?_⟩
  obtain rfl : z = z₀ := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
  have a := gen_trans ht (𝟙 (TK R).left) z₀ (hJ'.mem (fun _ : PUnit => x.left) _) (hJ₁.mem (fun _ : PUnit => x.left) _)
  have b : trF (L := L') (fun _ : PUnit => x.left) (fun _ => -1) (𝟙 (TK R).left) z₀ (fun _ => J' (𝟙 _ ≫ x.left))
      (fun _ => J₁ (𝟙 _ ≫ x.left)) = (gm x.left z₀ _ (L'.g (J' x.left) (J₁ x.left)))⁻¹ := by
    rw [trF, Fintype.prod_unique, zpow_neg_one, Category.id_comp]
  exact (a.trans (congrArg₂ (· * ·) b hv)).trans
    (formula_trans D W pr hw x y hx z₀ J J₀ hJ hJ₀ (J' x.left) (J₁ x.left) (hJ' _) (hJ₁ _)).symm

end GlobalTheory.Mum.TraitWit
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsDomain R]

structure Ext (D : DegPre R) : Type 1 where

  H : Over (Sp R)
  [grp : GrpObj H]
  [comm : IsCommMonObj H]

  Φ : ∀ T, (T ⟶ H) ≃ GtPt D T
  isGt : (GlobalTheory.TorusModel.splitExt D).IsGt H
  rep : GlobalTheory.TorusModel.Represents Φ

attribute [instance] Ext.grp Ext.comm


open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht GlobalTheory.TorusModel GlobalTheory.TorusExt GlobalTheory.Serre in
instance (D : DegPre R) : Nonempty (Ext D) := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨H, _, _, hH⟩ := exists_isGt hL (GlobalTheory.TorusModel.splitExt D)
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.TorusModel.exists_points hL hH
  exact ⟨{ H := H, Φ := Φ, isGt := hH, rep := hΦ }⟩

def Ext.q {D : DegPre R} (Y : Ext D) : Y.H ⟶ D.P.A := (Y.Φ Y.H (𝟙 _)).b

def IsTermOf {D : DegPre R} (Y : Ext D) {k : ℕ} {α : D.X} (b : D.SecB k α) (τ : SecK D.P.L Y.q.left k) : Prop :=
  ∀ (T : Over (Sp R)) (x : T ⟶ Y.H) y J, Good D.P.L y J →
    sval τ x.left y J = sval b (x ≫ Y.q).left y J * (val ((Y.Φ T x).s α) (𝟙 _) y J).val

def VanMod (I : Ideal R) {D : DegPre R} {k : ℕ} {α : D.X} (b : D.SecB k α) (e : ℕ) : Prop :=
  ∀ j : Fin 4 → D.P.L.ι, ((pullback.fst D.P.A.hom (thick R I e)).app _).hom (b.f j) = 0

structure IntFam (I : Ideal R) (D : DegPre R) (k : ℕ) where

  F : Fam D (FractionRing R) k

  f : ∀ α : D.X, D.SecB k α
  ext : ∀ α : D.X, GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F.s α)
    (D.famφB α) (DegPre.famε k) (f α) (DegPre.prB D (FractionRing R)).left
    (scal (DegPre.BF D (FractionRing R)).hom 1)
  small : ∀ e : ℕ, {α | ¬ VanMod I (f α) e}.Finite

def IntFam.Lead {I : Ideal R} {D : DegPre R} {k : ℕ} (F : IntFam I D k) (α : D.X) (b : D.SecB k α) : Prop :=
  F.f α = b ∧ ∀ β, β ≠ α → VanMod I (F.f β) 0

def PullB {R' : Type} [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D')
    {k : ℕ} (x : D'.X) (b : D.SecB k (hD.xe x)) (b' : D'.SecB k x) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι),
    (∀ κ, (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((D'.famφB x) κ (r z)) ∈ D.P.L.U (p κ)) →
    (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) →
    gs (r ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) z (LB.wchart D.P.L (D.famφB (hD.xe x)) p) (b.f p) =
      (∏ κ, gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val *
        gs r z (LB.wchart D'.P.L (D'.famφB x) q) (b'.f q)

end

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}

structure Trait (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] where
  cdvr : GlobalTheory.LN.CDvr W

  φ : R →+* W
  inj : Function.Injective φ
  loc : IsLocalHom φ

  ξ : Sp W ⟶ C.S
  ξ_π : ξ ≫ C.π = spMap φ

  G : Over (Sp W)
  [grp : GrpObj G]
  [comm : IsCommMonObj G]

  β : G.left ⟶ C.G.left
  cart : IsGrpPullback G C.G ξ β

  D' : DegData W (maximalIdeal W)

  A : PolAV (Sp (FractionRing W))

  U : Unif (maximalIdeal W) D' A G

  hD : IsPullDeg φ D.toPre D'.toPre

  ℓ : LB.Iso U.LG.L (C.P.L.L.pull β)
  ℓ_gen : ℓ.IsGen
  lab : ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] [Algebra (FractionRing R) F]
    (em : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] F),
    (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (φ r))) →
    ∀ (j : ℕ) (p : QkPt D.toPre (AlgebraicClosure (FractionRing R)) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j))
      (p' : QkPt D'.toPre F (C.n ^ j)) (x' : TFK (R := W) F ⟶ A.A),
      QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD F p₁.g p'.g →
      x'.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK W) ≫ β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α →
      QkToAkU U.toUnifPre F (C.n ^ j) p' x'

attribute [instance] Trait.grp Trait.comm

def Trait.Carries {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (u : W) {k : ℕ}
    (σ' : H0 T.U.LG.L k) (σ : SecK C.P.L.L T.β k) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) J J', Good C.P.L.L z J → Good T.U.LG.L z J' →
    sval σ r z J = gs r z ⊤ (scal T.G.hom u) * (gw T.ℓ r z (J (r ≫ T.β)) (J' r) ^ k).val * sval σ' r z J'

def Trait.ExpBy {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (u : W) {k : ℕ}
    (σ : SecK C.P.L.L T.β k) (F : IntFam (maximalIdeal R) D.toPre k) : Prop :=
  ∃ (σ' : H0 T.U.LG.L k) (f' : ∀ x, T.D'.toPre.SecB k x),
    T.Carries u σ' σ ∧ (∀ x, PullB T.hD x (F.f (T.hD.xe x)) (f' x)) ∧ ∀ e, T.U.ExpandsAt e k σ' f'

def Trait.Exp {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W) {k : ℕ}
    (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) : Prop :=
  ∃ σ : SecK C.P.L.L T.β k, T.ExpBy b σ F ∧
    ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval s p' z J

theorem LabCover.exists_trait (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.LN.CDvr W)
    (φ : R →+* W) (ξ : Sp W ⟶ C.S) (hφ : Function.Injective φ) (hl : IsLocalHom φ) (hξ : ξ ≫ C.π = spMap φ) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (T : Trait C W'),
      Function.Injective io ∧ io.Finite ∧ T.φ = io.comp φ ∧ T.ξ = spMap io ≫ ξ := by
  obtain ⟨W', _, _, _, io, G', _, _, β, D', A', U', hD, hW', hi, hf, hc, ⟨ℓ, hℓ⟩, hlab⟩ := C.trait W hW φ ξ hφ hl hξ
  have hio : IsLocalHom io := by
    letI := io.toAlgebra
    have : Module.Finite W W' := hf
    have : FaithfulSMul W W' := (faithfulSMul_iff_algebraMap_injective W W').2 hi
    exact (inferInstance : IsLocalHom (algebraMap W W'))
  refine ⟨W', inferInstance, inferInstance, inferInstance, io,
    { cdvr := hW', φ := io.comp φ, inj := hi.comp hφ, loc := inferInstance, ξ := spMap io ≫ ξ, ξ_π := ?_, G := G', β := β,
      cart := hc, D' := D', A := A', U := U', hD := hD, ℓ := ℓ, ℓ_gen := hℓ, lab := hlab }, hi, hf, rfl, rfl⟩
  rw [Category.assoc, hξ, ← Spec.map_comp]; rfl


end GlobalTheory.Mum
end
end
