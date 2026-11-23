module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
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
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.Ideal
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

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def Base (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] : Prop := AdmBase R (maximalIdeal R) ∧ CharZero R

def FinExt {R R' : Type} [CommRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') : Prop :=
  AdmBase R' (maximalIdeal R') ∧ Function.Injective ρ ∧ ρ.Finite

section

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

def Has (D : DegData R (maximalIdeal R)) : Prop :=
  ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (A : PolAV (Sp (FractionRing R))),
    IsSemiAbelian G ∧ Nonempty (Unif (maximalIdeal R) D A G)

def HasFin (D : DegData R (maximalIdeal R)) : Prop :=
  ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D' : DegData R' (maximalIdeal R')),
    FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ Has D'

def EvenOn {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G) : Prop :=
  ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
    (Q₀ : GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) X) (P₀ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G)),
    GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₀ P ∧ ∃ σ : GlobalTheory.UU.CubTriv P₀.c Q₀.i, σ.Even

end

structure Modif (R : Type) [CommRing R] [IsDomain R] where

  S : Scheme.{0}

  π : S ⟶ Sp R
  proper : IsProper π
  integral : IsIntegral S

  gp : Sp (FractionRing R) ⟶ S
  gp_π : gp ≫ π = jK R
  dominant : IsDominant gp

def Modif.self (R : Type) [CommRing R] [IsDomain R] : Modif R where
  S := Sp R
  π := 𝟙 _
  proper := inferInstance
  integral := inferInstance
  gp := jK R
  gp_π := Category.comp_id _
  dominant := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]; exact bot_le)⟩

section

variable {R : Type} [CommRing R] [IsDomain R]

def IsFactor (D D' : DegPre R) : Prop :=
  letI := D.P.isAb.comm
  letI := D'.P.isAb.comm
  ∃ (O : Type) (_ : Ring O) (_ : StarRing O) (_ : Module O D'.X) (o : D'.OAct O) (e f : O)
    (inc : D.P.A ⟶ D'.P.A) (pr : D'.P.A ⟶ D.P.A) (xi : D.X →+ D'.X) (xp : D'.X →+ D.X)
    (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D'.P.A D'.P.L).pull
      (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o.onB.act f) : G2 D.P.A ⟶ G2 D'.P.A).left)),
    e * e = e ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o.onB.act e ∧
    (∀ y, xp (xi y) = y) ∧ (∀ z, xi (xp z) = e • z) ∧ (∀ y, D'.c (xi y) = D.c y ≫ inc) ∧
    (Function.Injective (fun y => star e • f • xi y) ∧ ∀ z, ∃ y, star e • z = star e • f • xi y) ∧ w.IsGen ∧
    ∀ a b z J J', Good D'.P.L z J → Good D.P.L z J' →
      val (D.tau a b) (𝟙 _) z J' =
        GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J J' *
          val (D'.tau (xi a) (f • xi b)) (𝟙 _) z J

def PelOK {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dm : Datum H) (D : DegPre R)
    [Module (𝓞 E) D.X] (o : letI := H.starRing; D.OAct (𝓞 E)) : Prop :=
  letI := H.starRing
  Dm.p = Dm.q ∧ 1 ≤ Dm.p ∧ TraceFormTwistIso D o H.w0 ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
      (∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct o.onB.toRingAct)
        (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))) τ n ∧ n + Module.finrank (𝓞 E) D.X = Dm.p) ∧
      ∀ ζ : ℕ → Fˣ, (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) →
        ∃ I : TateIsoQ Dm D o F, I.ζ = ζ

end

structure LabCover {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) extends Modif R where

  G : Over S
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G

  P : GlobalTheory.UU.CP G

  A : PolAV (Sp (FractionRing R))

  α : A.A.left ⟶ G.left
  α_cart : IsGrpPullback A.A G gp α
  α_lb : LBIso A.L (P.L.L.pull α)

  n : ℕ
  n_prime : n.Prime
  n_odd : Odd n
  n_unit : IsUnit (n : R)

  lab : ∀ j : ℕ, QkPt D.toPre (AlgebraicClosure (FractionRing R)) (n ^ j) →
    (TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A.A)
  trait : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ S),
    Function.Injective φ → IsLocalHom φ → ξ ≫ π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (G' : Over (Sp W'))
      (_ : GrpObj G') (_ : IsCommMonObj G') (β : G'.left ⟶ G.left) (D' : DegData W' (maximalIdeal W'))
      (A' : PolAV (Sp (FractionRing W'))) (U' : Unif (maximalIdeal W') D' A' G')
      (hD : IsPullDeg (io.comp φ) D.toPre D'.toPre),
      GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsGrpPullback G' G (spMap io ≫ ξ) β ∧
      LBIso U'.LG.L (P.L.L.pull β) ∧
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W') F] [Algebra (FractionRing R) F]
        (em : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] F),
        (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W') F (algebraMap W' _ (io (φ r)))) →
        ∀ (j : ℕ) (p : QkPt D.toPre (AlgebraicClosure (FractionRing R)) (n ^ j)) (p₁ : QkPt D.toPre F (n ^ j))
          (p' : QkPt D'.toPre F (n ^ j)) (x' : TFK (R := W') F ⟶ A'.A),
          QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF (io.comp φ) hD F p₁.g p'.g →
          x'.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK W') ≫ β = spMap em.toRingHom ≫ (lab j p).left ≫ α →
          QkToAkU U'.toUnifPre F (n ^ j) p' x'

attribute [instance] LabCover.grp LabCover.comm

section Inhabitants

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem base_powerSeries : Base (PowerSeries ℚ) := by
  have hc : IsAdicComplete (maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  exact ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, algebraRat.charZero _⟩

end Inhabitants

end GlobalTheory.Mum
end
end

section

noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.Poinc

def mono {s m : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] {V : Type} [CommRing V] (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (μ : Fin s → X) : V := ∏ i, t i ^ (qW W (δ i) μ).toNat

def lin {s l : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (a : Fin l × Fin s → X)
    (β : LinearMap.BilinForm ℤ X) : ℤ := ∑ i, qW W β fun u => a (i, u)

theorem qW_nonneg {s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} (hW : PosW W) {X : Type} [AddCommGroup X]
    {β : LinearMap.BilinForm ℤ X} (hs : ∀ a b, β a b = β b a) (hβ : ∀ y, 0 ≤ β y y) (y : Fin s → X) : 0 ≤ qW W β y := by
  obtain ⟨c, hc0, hc⟩ := QWDom.qW_ge s W hW
  have h2 : (0 : ℝ) ≤ ((∑ u, β (y u) (y u) : ℤ) : ℝ) := by
    exact_mod_cast Finset.sum_nonneg fun u _ => hβ _
  exact_mod_cast (mul_nonneg hc0.le h2).trans (hc X β hs hβ y)

structure Dominant {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) (d N₁ : ℕ) {s l : ℕ} (W : Matrix (Fin s) (Fin s) ℤ)
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {r : ℕ} (γ : Fin r → LinearMap.BilinForm ℤ X)
    (a : Fin l × Fin s → X) : Prop where
  span : Submodule.span ℤ (Set.range a) = ⊤
  le : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → d * φ.evalZ β ≤ (lin W a β : ℤ)
  min : ∀ e : X ≃ₗ[O] X, (∀ x, CongMod N₁ (e x) x) → ∀ j, lin W a (γ j) ≤ lin W (fun i => e (a i)) (γ j)
  strict : ∀ e : X ≃ₗ[O] X, (∀ x, CongMod N₁ (e x) x) → (∃ x, e x ≠ x) → ∃ j, lin W a (γ j) < lin W (fun i => e (a i)) (γ j)

structure VSys {O : Type} [CommRing O] (bar : O → O) (q : ℕ) {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (N₁ : ℕ)
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
  u_unit : ∀ y μ, ∃ c, IsUnit (u y μ c)
  lam : ∃ C : ℕ, ∀ y, m y = 1 → ∀ i x, x ≠ 0 → ∃ h ∈ maximalIdeal A, ev y h ∣ t y i ^ (C * (δ y i x x).toNat)
  four : ∀ (y₀ : Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ N₁ ∣ N ∧ ∃ k : ∀ y, X y₀ →ₗ[ℤ] X y, k y₀ = LinearMap.id ∧
    (∀ y, IsUnimodMod O N (k y)) ∧ ∀ (l : ℕ) (a : Fin l × Fin s → X y₀) (c : Fin l → Q) (e : ℕ), ∃ f : A, ∀ (y : Y) (j : ℕ),
      ∃ S : Finset (Fin l × Fin s → X y), (↑S : Set _) ⊆ orbit O N₁ N (k y) a ∧
        (∀ μ ∈ orbit O N₁ N (k y) a, μ ∉ S → (j : ℤ) ≤ ∑ i, lin W μ (δ y i)) ∧
        ev y f - ∑ μ ∈ S, ∏ i, u y (fun v => μ (i, v)) (c i) * mono W (t y) (δ y) (fun v => μ (i, v)) ∈
          maximalIdeal (V y) ^ j ⊔ (maximalIdeal A ^ e).map (ev y)

attribute [instance] VSys.ring VSys.dom VSys.loc VSys.add VSys.mod VSys.fin VSys.proj VSys.freeZ VSys.finZ

namespace VSys

variable {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {N₁ : ℕ} {A : Type} [CommRing A]
  [IsLocalRing A] (Φ : VSys bar q W N₁ A)

theorem qW_nonneg (y : Φ.Y) (i : Fin (Φ.m y)) (μ : Fin s → Φ.X y) : 0 ≤ qW W (Φ.δ y i) μ :=
  GlobalTheory.Poinc.qW_nonneg Φ.posW (Φ.bal y i).1 (Φ.nonneg y i) μ

def monoT (y : Φ.Y) {l : ℕ} (a : Fin l × Fin s → Φ.X y) : Φ.V y := ∏ i, mono W (Φ.t y) (Φ.δ y) fun v => a (i, v)

def coefT (y : Φ.Y) {l : ℕ} (a : Fin l × Fin s → Φ.X y) (c : Fin l → Φ.Q) : Φ.V y := ∏ i, Φ.u y (fun v => a (i, v)) (c i)

def OrdGe (φ : InvFun O) (d e : ℕ) (f : A) : Prop :=
  ∀ y, IsPrincipalIdealRing (Φ.V y) → Φ.m y = 1 → ∀ i : Fin (Φ.m y),
    Φ.ev y f ∈ Ideal.span {Φ.t y i ^ ⌈(d : ℝ) * φ.evalZ (Φ.δ y i)⌉₊} ⊔ ((maximalIdeal A).map (Φ.ev y)) ^ e


variable {Φ} in
theorem OrdGe.mem {φ : InvFun O} {d e : ℕ} {f : A} (h : Φ.OrdGe φ d e f) (y : Φ.Y) (hP : IsPrincipalIdealRing (Φ.V y))
    (hm : Φ.m y = 1) (i : Fin (Φ.m y)) (b : ℕ) (hb : (b : ℝ) = d * φ.evalZ (Φ.δ y i)) :
    Φ.ev y f ∈ Ideal.span {Φ.t y i ^ b} ⊔ ((maximalIdeal A).map (Φ.ev y)) ^ e := by
  have := h y hP hm i
  rwa [← hb, Nat.ceil_natCast] at this

theorem ordGe_of_forall {φ : InvFun O} {d e : ℕ} {f : A}
    (h : ∀ y, IsPrincipalIdealRing (Φ.V y) → Φ.m y = 1 → ∀ (i : Fin (Φ.m y)) (b : ℕ),
      (∀ n : ℕ, d * φ.evalZ (Φ.δ y i) ≤ n → b ≤ n) →
      Φ.ev y f ∈ Ideal.span {Φ.t y i ^ b} ⊔ ((maximalIdeal A).map (Φ.ev y)) ^ e) : Φ.OrdGe φ d e f :=
  fun y hP hm i => h y hP hm i _ fun _ hn => Nat.ceil_le.2 hn

def Leads (y : Φ.Y) {l : ℕ} (a : Fin l × Fin s → Φ.X y) (c : Fin l → Φ.Q) (e : ℕ) (f : A) : Prop :=
  Φ.ev y f - Φ.coefT y a c * Φ.monoT y a ∈
    Ideal.span {Φ.monoT y a} * Ideal.span (Set.range (Φ.t y)) ⊔ maximalIdeal (Φ.V y) ^ e

end VSys

end GlobalTheory.Poinc
end
end
