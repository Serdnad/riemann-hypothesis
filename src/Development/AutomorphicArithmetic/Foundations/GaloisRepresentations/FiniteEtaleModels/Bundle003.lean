module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle118
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels.O

def Cg {M : Type} [AddCommGroup M] (n : ℕ) (x y : M) : Prop := ∃ z, x = y + n • z

def MOne : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 →
  Function.Bijective (algebraMap (𝓞 D.F) D.O) ∧ Module.Projective D.O D.La ∧ Module.Finite D.O D.La

def Idem : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (r : ℤ), (q : ℤ) ∣ r ^ 2 - D.tr * r + D.nm → ∃ ε : ℕ → 𝓞 D.F, ∀ e : ℕ,
  1 - ε e ∈ ES.uIdeal D r ^ e ∧ D.bar (ε e) ∈ ES.uIdeal D r ^ e ∧ (∀ x ∈ ES.uIdeal D r ^ e, (q : 𝓞 D.F) ^ e ∣ ε e * x) ∧
  (q : 𝓞 D.F) ^ e ∣ ε e + D.bar (ε e) - 1 ∧ (q : 𝓞 D.F) ^ e ∣ ε (e + 1) - ε e ∧
  ∀ (𝔞 : Ideal (𝓞 D.F)), (∃ f : ℕ, ES.uIdeal D r ^ f ≤ 𝔞) → (q : 𝓞 D.F) ^ e ∈ 𝔞 → ES.uIdeal D r ^ e ≤ 𝔞

def LiftUnit : Prop := ∀ (A M : Type) [CommRing A] [IsDedekindDomain A] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M]
  (u 𝔞 : Ideal A), u ≠ ⊥ → (∃ f : ℕ, u ^ f ≤ 𝔞) → ∀ g₀ : (M ⧸ (𝔞 • ⊤ : Submodule A M)) ≃ₗ[A] (M ⧸ (𝔞 • ⊤ : Submodule A M)),
  ∃ (g : M →ₗ[A] M) (h : ℕ → (M →ₗ[A] M)), (∀ x, (𝔞 • ⊤ : Submodule A M).mkQ (g x) = g₀ ((𝔞 • ⊤ : Submodule A M).mkQ x)) ∧
    ∀ e x, g (h e x) - x ∈ (u ^ e • ⊤ : Submodule A M) ∧ h e (g x) - x ∈ (u ^ e • ⊤ : Submodule A M)

def Adj : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (e : ℕ), (∀ x : D.La, (∀ y, ((q ^ e : ℕ) : ℤ) ∣ D.EF x y) → Cg (q ^ e) x 0) ∧
  (∀ h : D.La →ₗ[D.O] D.La, ∃ k : D.La →+ D.La, (∀ x y, ((q ^ e : ℕ) : ℤ) ∣ D.EF (h x) y - D.EF x (k y)) ∧
    ∀ (c : D.O) y, Cg (q ^ e) (k (c • y)) (c • k y)) ∧
  ∀ g : D.La →+ D.La, (∀ x y, ((q ^ e : ℕ) : ℤ) ∣ D.EF (g x) (g y) - D.EF x y) →
    (∀ x, Cg (q ^ e) (g x) 0 → Cg (q ^ e) x 0) ∧ ∀ x, ∃ y, Cg (q ^ e) (g y) x

def QSys : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 → ∀ (r : ℤ), (q : ℤ) ∣ r ^ 2 - D.tr * r + D.nm → ∀ (𝔞 : Ideal (𝓞 D.F)),
  (∃ e : ℕ, ES.uIdeal D r ^ e ≤ 𝔞) → ∀ g₀ : LevGrp D 𝔞 1, ∃ g : ℕ → D.La →+ D.La, ∀ e : ℕ,
    (∀ (c : D.O) x, Cg (q ^ e) (g e (c • x)) (c • g e x)) ∧ (∀ x y, ((q ^ e : ℕ) : ℤ) ∣ D.EF (g e x) (g e y) - D.EF x y) ∧
    (∀ x, Cg (q ^ e) (g (e + 1) x) (g e x)) ∧ ((q : 𝓞 D.F) ^ e ∈ 𝔞 → ∀ x, (wSub D 𝔞 1).mkQ (g e x) = g₀ ((wSub D 𝔞 1).mkQ x))

structure IsSys {G : GDatum} (g : ℕ → G.La →+ G.La) : Prop where
  lin : ∀ n, 0 < n → ∀ (c : G.O) x, ∃ z, g n (c • x) = c • g n x + n • z
  onto : ∀ n, 0 < n → ∀ x, ∃ y z, g n y = x + n • z
  inj : ∀ n, 0 < n → ∀ x z, g n x = n • z → ∃ v, x = n • v
  iso : ∀ n : ℕ, 0 < n → ∀ x y, (n : ℤ) ∣ G.EF (g n x) (g n y) - G.EF x y
  tow : ∀ n m, 0 < n → 0 < m → ∀ x, ∃ z, g (n * m) x = g n x + n • z

def TResim : Prop := ∀ (G : GDatum) (k : Type) [Field k] (Q : Type) [Group Q] (act : G.O → Q → Q) (e : ℕ → Q → Q → kˣ → Prop)
  (I : GTateIso G k Q act e) (g : ℕ → G.La →+ G.La), IsSys g → ∃ I' : GTateIso G k Q act e, ∀ n, 0 < n → ∀ x, I'.ev n x = I.ev n (g n x)

def OResim : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R)
  (gb : GBase D.toG R') (N N₀ c : ℕ), N = N₀ * c → 0 < N → ∀ (X X₁ : Scheme.{0}) (s : X ⟶ Sp R') (s₁ : X₁ ⟶ Sp R) (o : GObj gb N s)
  (u : Obj b N₀ s₁) (f : X ⟶ X₁) (n : QMap o u f c) (g : ℕ → D.La →+ D.La), IsSys (G := D.toG) g → (∀ x, ∃ z, g N₀ x = x + N₀ • z) →
  ∃ (o' : GObj gb N s) (n' : QMap o' u f c), ∀ y : D.La, (o'.eta y).left ≫ n'.φ = (o.eta (g N y)).left ≫ n.φ

def TExt : Prop := ∀ (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase G R) (N : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
  (σ : Sp Ω ⟶ Sp R) (o : GObj gb N σ)
  (I : GTateIso G Ω (Over.mk (𝟙 (Sp Ω)) ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)))
  (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp Ω),
  ∃ I' : GTateIso G k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
    ∀ n, 0 < n → ∀ y, (I'.ev n y).left = x ≫ (I.ev n y).left

def Raise : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R)
  (gb : GBase D.toG R') (β : R →+* R'), Match b gb β → ∀ (N N₀ c : ℕ), N = N₀ * c → 0 < N → N₀.Coprime q →
  ∀ (X₁ : Scheme.{0}) (s₁ : X₁ ⟶ Sp R) (u : Obj b N₀ s₁) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Sp Ω ⟶ X₁) (σ : Sp Ω ⟶ Sp R'),
  y ≫ s₁ = σ ≫ spMap β → ∃ o : GObj gb N σ, Nonempty (QMap o u y c)

def ClsAt : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 → ∀ (r : ℤ), (q : ℤ) ∣ r ^ 2 - D.tr * r + D.nm →
  ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R) (gb : GBase D.toG R') (β : R →+* R'), Match b gb β →
  ∀ (N N₀ c : ℕ) (a : 𝓞 D.F) (𝔞 : Ideal (𝓞 D.F)), N = N₀ * c → 0 < N → N₀.Coprime q → IsGen a N 𝔞 → (∃ e : ℕ, ES.uIdeal D r ^ e ≤ 𝔞) →
  ∀ (Y : EtModel b N₀ 𝔞 1) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Sp Ω ⟶ Y.X) (σ : Sp Ω ⟶ Sp R'), y ≫ Y.s = σ ≫ spMap β →
  ∃ (o : GObj gb N σ) (C : Cls Y β o c a), C.j = y

def EpsEx : Prop := ∀ (A : Type) [CommRing A] [IsDedekindDomain A] [CharZero A] (𝔟₁ 𝔟₂ : Ideal A) (a₁ a₂ : A) (M₁ M₂ t : ℕ), 0 < M₁ →
  M₁ = M₂ * t → 𝔟₁ ≤ 𝔟₂ → IsGen a₁ M₁ 𝔟₁ → IsGen a₂ M₂ 𝔟₂ → ∃ ε : A, (M₁ : A) ∣ ε * a₁ - t * a₂ ∧ (Ideal.span {ε} ⊔ 𝔟₁) * 𝔟₂ = 𝔟₁

def LevDown : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 → ∀ (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R)
  (o : Obj b N s) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (ε : 𝓞 D.F), 𝔟₁ ≠ ⊥ → (Ideal.span {ε} ⊔ 𝔟₁) * 𝔟₂ = 𝔟₁ → ∀ l : D.La → (𝟙_ (Over S) ⟶ o.A),
  IsEtLev o 𝔟₁ 1 l → IsEtLev o 𝔟₂ 1 fun y => l (algebraMap (𝓞 D.F) D.O ε • y)

def DownEx : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → D.a = 1 → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
  (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫)
  (N₀ κ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S (N₀ * κ) 𝔟₁) (X₂ : Ext S N₀ 𝔟₂) (ε : 𝓞 D.F), (Ideal.span {ε} ⊔ 𝔟₁) * 𝔟₂ = 𝔟₁ →
  ∃ (t : X₁.Y.X ⟶ X₂.Y.X) (m : ObjMap (X₁.Y.univ.forget N₀ (Dvd.intro _ rfl) X₁.lev.2.1) X₂.Y.univ t), t ≫ X₂.Y.s = X₁.Y.s ∧ IsFinite t ∧ Etale t ∧
    ∀ y : D.La, (X₁.Y.lv (algebraMap (𝓞 D.F) D.O ε • y)).left ≫ m.φ = t ≫ (X₂.Y.lv y).left

end UpperTheory.Gal.FiniteEtaleModels.O
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct

namespace UpperTheory.Gal.FiniteEtaleModels

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E] {gb : GBase D.toG E}
  {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)} {S : Site gb w q r 𝔴 𝔫} {k : ℕ} {T : KS L gb k}
  {N₀ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₀ 𝔟₁} {X₂ : Ext S N₀ 𝔟₂} {𝔴' : Ideal (𝓞 D.F)} {i : ℕ} {h : G.GAf} {M₁ M₂ : Lv p}
  {c₁ c₂ : ℕ} {a₁ a₂ : 𝓞 D.F}

structure BPt (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T h M₁ M₂)
    {f : X₁.Y.X ⟶ X₂.M.X} (mf : ObjMap X₁.Y.univ X₂.M.univ f) {c : ℕ} (Tj : TjD X₂.M r 𝔴' i c) : Type where
  y : (T.M M₁).X ⟶ Tj.Y
  ys : y ≫ Tj.s = C₁.j ≫ f
  yt : y ≫ Tj.t = W.π ≫ C₂.j ≫ X₂.π
  fa : (T.M M₁).univ.A.left ⟶ Tj.o.A.left
  fb : W.o.A.left ⟶ Tj.o'.A.left
  ca : IsGrpPullback (T.M M₁).univ.A Tj.o.A y fa
  cb : IsGrpPullback W.o.A Tj.o'.A y fb
  sq : fa ≫ Tj.ψ.left = W.ψ.left ≫ fb
  ms : fa ≫ Tj.ms.φ = C₁.m.φ ≫ mf.φ
  mt : fb ≫ Tj.mt.φ = W.φ.φ ≫ C₂.m.φ ≫ X₂.mπ.φ

end

def IsogG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R' : Type) [CommRing R'] [Algebra ℚ R'] (gb : GBase D.toG R')
    (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴₀ 𝔴 : Ideal (𝓞 D.F)) (atq : AtPrime D q r 𝔴₀)
    (sp : Nonempty ((D.O ⊗[ℤ] ℤ_[q]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[q]))), D.m = 1 → 𝔴.IsMaximal → uId D q r ≤ 𝔴 →
    ∀ (R : Type) [CommRing R] (b : Base (datAt atq sp) R) (N₀ : ℕ), N₀.Coprime q → ∀ (i e : ℕ), Ideal.absNorm 𝔴 ^ i = q ^ e →
    ∀ (h u : G.GAf), IsTjElt L q r 𝔴 i h → Integ L h → u ∈ L.KN N₀ → ∀ (N' N : Lv p) (c' c : ℕ), N'.1 = N₀ * c' → N.1 = N₀ * c →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp R') (o' : GObj gb N'.1 s) (o : GObj gb N.1 s) (ψ : o'.A ⟶ o.A), IsTrans L (h * u) o' o ψ →
    ∀ (s₀ : X ⟶ Sp R) (o₁ o₂ : Obj b N₀ s₀) (n₁ : QMap (D := datAt atq sp) (gb := gb) o' o₁ (𝟙 _) c')
      (n₂ : QMap (D := datAt atq sp) (gb := gb) o o₂ (𝟙 _) c),
    ∃ ψ₀ : o₁.A ⟶ o₂.A, n₁.φ ≫ ψ₀.left = ψ.left ≫ n₂.φ ∧ ES.IsPIsog (q ^ e) o₁ o₂ ψ₀ ∧ ES.IsTj (D := datAt atq sp) r 𝔴 i o₁ o₂ ψ₀

def TjExG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ),
    3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j e : ℕ), w.IsMaximal →
    ES.uIdeal D r ≤ w → j ≤ D.n → (0 < j → 0 < e) → ∀ M : Model b N, Nonempty (TjD M r w j (p ^ e))

def SecInjG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
    ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j e : ℕ), w.IsMaximal → ES.uIdeal D r ≤ w → j ≤ D.n → (0 < j → 0 < e) →
    ∀ (M : Model b N) (T : TjD M r w j (p ^ e)) (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
      (x : Sp K ⟶ M.X) (y y' : Sp K ⟶ T.Y), y ≫ T.s = x → y' ≫ T.s = x →
    (∀ g : Over.mk x ⟶ M.univ.A, ES.KilledBy M.univ w g → (KerAt T y g.left ↔ KerAt T y' g.left)) → y = y'

def DescExt : Prop :=
  ∀ (O E : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E]
    (V X Y B : Scheme.{0}) (s : X ⟶ Sp O) (σ : V ⟶ Sp E) (j : V ⟶ X) (ov : j ≫ s = σ ≫ spMap (algebraMap O E)), Smooth s →
    IsFinite (pullback.lift j σ ov) → Etale (pullback.lift j σ ov) →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ X) (τ : Sp Ω ⟶ Sp E), x ≫ s = τ ≫ spMap (algebraMap O E) → ∃ v, v ≫ j = x ∧ v ≫ σ = τ) →
    ∀ (f : X ⟶ B) (g : Y ⟶ B) (y : V ⟶ Y), IsFinite g → y ≫ g = j ≫ f →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : Sp Ω ⟶ V), x ≫ j = x' ≫ j → x ≫ y = x' ≫ y) → ∃ y' : X ⟶ Y, j ≫ y' = y ∧ y' ≫ g = f

def LatB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (q : ℕ) (r : ℤ) (𝔴 𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (i : ℕ) (h : G.GAf),
    AtPrime D q r 𝔴 → IsTjElt L q r 𝔴 i h → Integ L h → 𝔟₁ ≤ 𝔟₂ * 𝔴 → (∃ e : ℕ, uId D q r ^ e ≤ 𝔟₁) →
    ∀ (M₁ M₂ : Lv p) (a₁ a₂ : 𝓞 D.F), IsGen a₁ M₁.1 𝔟₁ → IsGen a₂ M₂.1 𝔟₂ → ∀ y : D.La, ∃ x : D.La, ∃ v ∈ LaHat D,
      L.actG h (inAf D (M₂.1 • algebraMap (𝓞 D.F) D.O a₁ • x)) = inAf D (M₁.1 • algebraMap (𝓞 D.F) D.O a₂ • y) + (M₁.1 * M₂.1) • v

def EtaPtB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R)
    (h : G.GAf) (X : Scheme.{0}) (s : X ⟶ Sp R) (N' N : Lv p) (o' : GObj gb N'.1 s) (o : GObj gb N.1 s) (ψ : o'.A ⟶ o.A), IsTrans L h o' o ψ →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : Sp Ω ⟶ X) (x y : D.La),
    (∃ v ∈ LaHat D, L.actG h (inAf D (N.1 • x)) = inAf D (N'.1 • y) + (N'.1 * N.1) • v) →
    toUnit (Over.mk z) ≫ o'.eta x ≫ ψ = toUnit (Over.mk z) ≫ o.eta y

def BRead : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (N₀ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S N₀ 𝔟₁) (X₂ : Ext S N₀ 𝔟₂) (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal → uId D q r ≤ 𝔴' →
    𝔟₁ ≤ 𝔟₂ * 𝔴' → i ≤ D.n → ∀ (h : G.GAf), Integ L h → IsTjElt L q r 𝔴' i h → ∀ (M₁ M₂ : Lv p) (c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F),
    X₁.site.Num M₁.1 c₁ a₁ → X₂.site.Num M₂.1 c₂ a₂ →
    ∀ (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T h M₁ M₂)
      (f : X₁.Y.X ⟶ X₂.M.X) (mf : ObjMap X₁.Y.univ X₂.M.univ f), f ≫ X₂.M.s = X₁.Y.s →
    ∀ (e : ℕ), Ideal.absNorm 𝔴' ^ i = q ^ e → (0 < i → 0 < e) → ∀ (Tj : TjD X₂.M r 𝔴' i (q ^ e)),
    Nonempty (BPt C₁ C₂ W mf Tj)

def BKer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (N₀ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S N₀ 𝔟₁) (X₂ : Ext S N₀ 𝔟₂) (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal → uId D q r ≤ 𝔴' →
    𝔟₁ ≤ 𝔟₂ * 𝔴' → i ≤ D.n → ∀ (h : G.GAf), Integ L h → IsTjElt L q r 𝔴' i h → ∀ (M₁ M₂ : Lv p) (c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F),
    X₁.site.Num M₁.1 c₁ a₁ → X₂.site.Num M₂.1 c₂ a₂ →
    ∀ (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T h M₁ M₂)
      (f : X₁.Y.X ⟶ X₂.M.X) (mf : ObjMap X₁.Y.univ X₂.M.univ f), f ≫ X₂.M.s = X₁.Y.s →
    ∀ (e : ℕ), Ideal.absNorm 𝔴' ^ i = q ^ e → (0 < i → 0 < e) → ∀ (Tj : TjD X₂.M r 𝔴' i (q ^ e)),
    ∀ (P : BPt C₁ C₂ W mf Tj) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : Sp Ω ⟶ (T.M M₁).X), x ≫ C₁.j = x' ≫ C₁.j → x ≫ P.y = x' ≫ P.y

def BLev : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (N₀ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S N₀ 𝔟₁) (X₂ : Ext S N₀ 𝔟₂) (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal → uId D q r ≤ 𝔴' →
    𝔟₁ ≤ 𝔟₂ * 𝔴' → i ≤ D.n → ∀ (h : G.GAf), Integ L h → IsTjElt L q r 𝔴' i h → ∀ (M₁ M₂ : Lv p) (c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F),
    X₁.site.Num M₁.1 c₁ a₁ → X₂.site.Num M₂.1 c₂ a₂ →
    ∀ (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T h M₁ M₂)
      (f : X₁.Y.X ⟶ X₂.M.X) (mf : ObjMap X₁.Y.univ X₂.M.univ f), f ≫ X₂.M.s = X₁.Y.s →
    ∀ (e : ℕ), Ideal.absNorm 𝔴' ^ i = q ^ e → (0 < i → 0 < e) → ∀ (Tj : TjD X₂.M r 𝔴' i (q ^ e)),
    ∀ (P : BPt C₁ C₂ W mf Tj) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : Sp Ω ⟶ (T.M M₁).X), x ≫ C₁.j = x' ≫ C₁.j → x ≫ P.y = x' ≫ P.y →
      x ≫ W.π ≫ C₂.j = x' ≫ W.π ≫ C₂.j

end UpperTheory.Gal.FiniteEtaleModels
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

private theorem conj_congOne {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {u v : G.GAf} {N : ℕ}
    (hu : u ∈ L.KN 1) (hv : L.CongOne N v) : L.CongOne N (u * v * u⁻¹) := by
  intro z hz
  have hu' : L.CongOne 1 u ∧ L.CongOne 1 u⁻¹ := hu
  obtain ⟨w1, hw1, e1⟩ := hu'.2 z hz
  have hz' : L.actG u⁻¹ z ∈ LaHat D := by
    rw [e1, one_smul]
    exact add_mem hz hw1
  obtain ⟨w2, hw2, e2⟩ := hv _ hz'
  obtain ⟨w3, hw3, e3⟩ := hu'.1 w2 hw2
  refine ⟨L.actG u w2, ?_, ?_⟩
  · rw [e3, one_smul]
    exact add_mem hw2 hw3
  · have key : L.actG u (L.actG u⁻¹ z) = z := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e2, map_add (f := _), map_nsmul, key]

private theorem inAf_mem' {p : ℕ} [Fact p.Prime] (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

private theorem cl_cast {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E]
    {gb : GBase D.toG E} {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)}
    (S : Site gb w q r 𝔴 𝔫) {k : ℕ} (T : KS L gb k) (M : Lv p) {c c' : ℕ} {a a' : 𝓞 D.F} (hc : c' = c) (ha : a' = a)
    (C : S.Cl (T.M M).univ c a) : ∃ C' : S.Cl (T.M M).univ c' a', S.pi T C' = S.pi T C := by
  subst hc ha
  exact ⟨C, rfl⟩

theorem UpperTheory.Gal.FiniteEtaleModels.quotOf_holds :
    PowCart → PiInv → PiFet → PiSep → CongCRT → BaseOnto → QuotOf := by
  intro hPC hPI hPF hPS hCRT hBO p _ D G L hSc E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hK M c a hNum C
  have hM := hNum.1
  have hGen := hNum.2
  let N0 : Lv p := ⟨S.N₀, S.std.three, S.cop⟩
  have hMpos : 0 < M.1 := by have := M.2.1; omega
  have hdvd : S.N₀ ∣ M.1 := ⟨c, hM⟩
  have hup := S.upow
  have hcop : S.N₀.Coprime q := S.std.cop
  have hK₀le : K₀ ≤ L.KN S.N₀ := by
    have key : ∀ g, g ∈ K₀ → L.CongOne S.N₀ g := fun g hg => by
      have h := (hK g).1 hg
      have h2 := h.2
      rw [S.lev] at h2
      exact (((hCRT p D G L q r S.N₀ S.𝔞 hcop hup g (integ_of_mem h.1)).1).1 h2).1
    exact fun g hg => ⟨key g hg, key _ (inv_mem hg)⟩
  have hKM : L.KN M.1 ≤ K₀ := by
    intro g hg
    have h1 : g ∈ L.KN 1 := KN_anti (one_dvd _) hg
    have hcrt := hCRT p D G L q r S.N₀ S.𝔞 hcop hup g (integ_of_mem h1)
    have h2 : L.CongOne S.N₀ g := (KN_anti hdvd hg).1
    have h3 : CongId L S.𝔞 g := (hcrt.2 a M.1 hMpos M.2.2 hGen).2 fun y => hg.1 _ (inAf_mem' D _)
    exact (hK g).2 ⟨h1, by rw [S.lev]; exact hcrt.1.2 ⟨h2, h3⟩⟩
  have hX : T.X.K (T.lev M) = L.KN M.1 := T.K_eq M
  have hX0 : T.X.K (T.lev N0) = L.KN S.N₀ := T.K_eq N0
  refine ⟨?ov, ?le, ?idx, ?adm, ?inv, ?fib, ?free, ?onto⟩
  · obtain ⟨e, -⟩ := hPF p D G L E gb w q r 𝔴 𝔫 S k T M c a hNum C
    exact e
  · rw [hX]; exact hKM
  · rw [hX]
    have h := T.X.idx (T.lev M) (T.lev N0)
    rw [hX, hX0] at h
    exact fun e => h (Subgroup.relIndex_eq_zero_of_le_right hK₀le e)
  · intro u hu
    have hu1 := ((hK u).1 hu).1
    refine ⟨(T.Δ_eq u).2 (integ_of_mem hu1), fun v hv => ?_⟩
    rw [hX] at hv ⊢
    refine ⟨conj_congOne L hu1 hv.1, ?_⟩
    have e : (u * v * u⁻¹)⁻¹ = u * v⁻¹ * u⁻¹ := by group
    rw [e]; exact conj_congOne L hu1 hv.2
  · intro u hu x y
    obtain ⟨C', hC'⟩ := cl_cast (a' := ((1 : ℕ) : 𝓞 D.F) * a) S T M (_root_.mul_one c) (by simp) C
    have h := hPI p D G L E gb w q r 𝔴 𝔫 S k T K₀ hK M M 1 c a (_root_.mul_one _).symm hNum C' C u hu x y
    rwa [hC'] at h
  · intro Ω _ _ x y h
    exact hPS p D G L E gb w q r 𝔴 𝔫 S k T K₀ hK M c a hNum C Ω x y h
  · intro u hu x y Ω _ _ z hz
    exact T.X.free _ (T.lev N0) (by rw [hX, hX0]; exact KN_anti hdvd) u (by rw [hX0]; exact hK₀le hu) x y Ω z hz
  · intro Ω _ _ y σ hy
    obtain ⟨x₀, hx₀, -⟩ := hBO p D G L hSc E gb w q r 𝔴 𝔫 S k T M c a hNum C Ω (y ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom) σ
      (by simpa using hy)
    have hpb := (hPC _ _ _ (T.M M).univ.A S.Y.univ.A S.Y.univ.A C.j (𝟙 _) C.m.φ (𝟙 _) C.m.cart.1.w (by simp) k).1 C.m.cart.1
    refine ⟨hpb.lift y x₀ hx₀.symm ≫ (T.e M).inv, ?_⟩
    simp only [Site.pi, Cls.pw, Category.assoc, Iso.inv_hom_id_assoc]
    exact hpb.lift_fst _ _ _
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.extEx_holds :
    MIn → PowProj → ExtEx := by
  intro hM hPP p _ D G hSc E _ _ gb w q _ r 𝔴 𝔫 S N₁ 𝔟 hL
  obtain ⟨h3, hcq, hcp, hsup, hpow⟩ := hL
  obtain ⟨M⟩ := hM.ex q _ (Ow w) S.b N₁ h3 hcq
  have het : IsEtIdeal S.b 𝔟 :=
    (hM.placeOf q _ (Ow w) S.b r 𝔴 S.atq.max S.std.pmem S.std.a1 S.std.ule S.std.tw 𝔟 hsup).2 hpow
  obtain ⟨Y, π, ρ, hov, ⟨m⟩, hG⟩ := hM.finModel q _ (Ow w) S.b N₁ h3 hcq 𝔟 1 het M
  have hfin : IsFinite π := hG.fin
  have het' : Etale π := hG.etale
  have hMp : IsProjOver M.s := hM.proj q _ (Ow w) S.b N₁ h3 hcq hSc.cpt M
  have hYp : IsProjOver Y.s := by
    rw [← hov]
    exact GlobalTheory.isProjOver_comp_of_finite (Ow w) M.X Y.X π M.s hfin hMp
  have hYs : ∃ d, SmoothOfRelativeDimension d Y.s := by
    have h0 := het'
    rw [Etale.iff_smoothOfRelativeDimension_zero] at h0
    have key : ∀ n, SmoothOfRelativeDimension n M.s → SmoothOfRelativeDimension (0 + n) (π ≫ M.s) :=
      fun n hn => inferInstance
    rw [← hov]
    exact ⟨_, key _ M.smooth⟩
  refine ⟨⟨⟨h3, hcq, hcp, hsup, hpow⟩, M, Y, π, hov, m, hfin, het', fun k => ?_, fun k => ?_⟩⟩
  · exact (hPP q _ (Ow w) S.b N₁ h3 hcq Y.X Y.s Y.univ k).1 hYp
  · obtain ⟨d, hd⟩ := hYs
    exact (hPP q _ (Ow w) S.b N₁ h3 hcq Y.X Y.s Y.univ k).2 d hd
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.lCount_holds :
    LSigPt → LSigFin → LCount := by
  intro hpt hfin I B _ _ W Z Y Y' cls f kc π s m hf he hs hes hm h
  obtain ⟨hsF, hsE⟩ := hfin B Y' Y s hs hes
  obtain ⟨hdF, hdE⟩ := hfin I W Z f hf he
  set sB : (∐ fun _ : B => Y') ⟶ Y := Sigma.desc fun _ : B => s with hsB
  set ℓ := pullback.lift _ _ h with hℓ
  have hℓ1 : ℓ ≫ pullback.fst π sB = Sigma.desc fun _ : I => f := pullback.lift_fst _ _ h
  have hℓ2 : ℓ ≫ pullback.snd π sB =
      Sigma.desc fun c : I => kc c ≫ Sigma.ι (fun _ : B => Y') (cls c) := pullback.lift_snd _ _ h
  haveI := hsF
  haveI := hsE
  haveI : IsFinite (pullback.fst π sB) := inferInstance
  haveI : Etale (pullback.fst π sB) := inferInstance
  haveI : IsFinite (ℓ ≫ pullback.fst π sB) := by rw [hℓ1]; exact hdF
  haveI : Etale (ℓ ≫ pullback.fst π sB) := by rw [hℓ1]; exact hdE
  refine ⟨IsFinite.of_comp ℓ (pullback.fst π sB), Etale.of_comp ℓ (pullback.fst π sB), ?_⟩
  intro K _ _ x
  obtain ⟨⟨b, y'⟩, hb⟩ := (hpt B Y' K).2 (x ≫ pullback.snd π sB)
  replace hb : y' ≫ Sigma.ι (fun _ : B => Y') b = x ≫ pullback.snd π sB := hb
  have hy : y' ≫ s = (x ≫ pullback.fst π sB) ≫ π := by
    calc y' ≫ s = (y' ≫ Sigma.ι (fun _ : B => Y') b) ≫ sB := by simp [hsB]
      _ = (x ≫ pullback.fst π sB) ≫ π := by
        rw [hb, Category.assoc, Category.assoc, pullback.condition]
  have key : ∀ (c : I) (v : sp K ⟶ W), (v ≫ Sigma.ι (fun _ : I => W) c) ≫ ℓ = x ↔
      v ≫ f = x ≫ pullback.fst π sB ∧ cls c = b ∧ v ≫ kc c = y' := by
    intro c v
    have e1 : ((v ≫ Sigma.ι (fun _ : I => W) c) ≫ ℓ) ≫ pullback.fst π sB = v ≫ f := by
      rw [Category.assoc, hℓ1]; simp
    have e2 : ((v ≫ Sigma.ι (fun _ : I => W) c) ≫ ℓ) ≫ pullback.snd π sB =
        (v ≫ kc c) ≫ Sigma.ι (fun _ : B => Y') (cls c) := by
      rw [Category.assoc, hℓ2]; simp
    constructor
    · intro hx
      rw [hx] at e1 e2
      have h2 : (fun p : B × (sp K ⟶ Y') => p.2 ≫ Sigma.ι (fun _ : B => Y') p.1) (cls c, v ≫ kc c) =
          (fun p : B × (sp K ⟶ Y') => p.2 ≫ Sigma.ι (fun _ : B => Y') p.1) (b, y') := by
        show (v ≫ kc c) ≫ Sigma.ι (fun _ : B => Y') (cls c) = y' ≫ Sigma.ι (fun _ : B => Y') b
        rw [← e2, hb]
      obtain ⟨h3, h4⟩ := Prod.mk.inj ((hpt B Y' K).1 h2)
      exact ⟨e1.symm, h3, h4⟩
    · rintro ⟨h1, h3, h4⟩
      apply pullback.hom_ext
      · rw [e1, h1]
      · rw [e2, h3, h4, hb]
  rw [← hm K (x ≫ pullback.fst π sB) b y' hy]
  let F : {cx : I × (sp K ⟶ W) // cx.2 ≫ f = x ≫ pullback.fst π sB ∧ cls cx.1 = b ∧ cx.2 ≫ kc cx.1 = y'} →
      {y : sp K ⟶ ∐ (fun _ : I => W) // y ≫ ℓ = x} :=
    fun p => ⟨p.1.2 ≫ Sigma.ι (fun _ : I => W) p.1.1, (key _ _).2 p.2⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨⟨c, v⟩, hv⟩ ⟨⟨c', v'⟩, hv'⟩ e
      have e' : (fun p : I × (sp K ⟶ W) => p.2 ≫ Sigma.ι (fun _ : I => W) p.1) (c, v) =
          (fun p : I × (sp K ⟶ W) => p.2 ≫ Sigma.ι (fun _ : I => W) p.1) (c', v') :=
        congrArg Subtype.val e
      exact Subtype.ext ((hpt I W K).1 e')
    · rintro ⟨y, hy'⟩
      obtain ⟨⟨c, v⟩, hv⟩ := (hpt I W K).2 y
      replace hv : v ≫ Sigma.ι (fun _ : I => W) c = y := hv
      subst hv
      exact ⟨⟨(c, v), (key c v).1 hy'⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective F hF)).symm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.lSigPt_holds :
    LSigPt := by
  intro I W Ω _
  haveI : Unique (sp Ω) := inferInstanceAs (Unique (PrimeSpectrum Ω))
  constructor
  · rintro ⟨i, x⟩ ⟨j, x'⟩ h
    have h' : x ≫ Sigma.ι (fun _ : I => W) i = x' ≫ Sigma.ι (fun _ : I => W) j := h
    have e : (Sigma.ι (fun _ : I => W) i) (x default) = (Sigma.ι (fun _ : I => W) j) (x' default) := by
      have := congrArg (fun f : sp Ω ⟶ _ => f default) h'
      simpa using this
    have e2 := (sigmaι_eq_iff _ _ _ _ _).mp e
    obtain ⟨rfl⟩ : i = j := congrArg Sigma.fst e2
    have : x = x' := (cancel_mono (Sigma.ι (fun _ : I => W) i)).mp h'
    rw [this]
  · intro y
    obtain ⟨i, w, hw⟩ := (sigmaOpenCover fun _ : I => W).exists_eq (y default)
    have hr : Set.range y ⊆ Set.range (Sigma.ι (fun _ : I => W) i) := by
      rintro _ ⟨p, rfl⟩
      rw [Subsingleton.elim p default]
      exact ⟨w, hw⟩
    exact ⟨(i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => W) i) y hr), IsOpenImmersion.lift_fac _ _ _⟩
end
