module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.DegeneratingToriPeriodMapEqBaseOfYEqZero
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace AnArc

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

def perFactor (w : ℂ) (la : A.La) (v : A.V) : ℂ :=
  A.ah la.l (v.2 + A.ct la.y) * (A.psi la.y * eTwoPi (v.1 la.y) * eTwoPi (w * A.q la.y))⁻¹


open AlgebraicGeometry CategoryTheory Limits in
variable {O : Type} [CommRing O] [StarRing O] (A : _root_.GlobalTheory.AnArc O) in
open _root_.GlobalTheory.AnArc.La in
theorem _root_.GlobalTheory.AnArc.term_add_period {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (w : ℂ)
    (la : A.La) (μ : A.X) (v : A.V) :
    A.term j α th μ (v + A.Pw w la) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α μ) =
      A.perFactor w la v ^ j *
        (A.term j α th (μ + la.y) v *
          _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α (μ + la.y))) := by
  set y := la.y with hy
  set n := la.n with hn
  set l := la.l with hl
  set L : A.La := _root_.GlobalTheory.AnArc.La.mk 0 0 l
  set M : A.La := _root_.GlobalTheory.AnArc.La.mk 0 n 0
  set Y : A.La := _root_.GlobalTheory.AnArc.La.mk y 0 0
  have hPw : A.Pw w la = A.Pw w Y + A.P0 M + A.P0 L := by
    conv_lhs => rw [eq_add_parts la]
    rw [map_add (f := _), map_add (f := _), _root_.GlobalTheory.AnArc.degeneratingTori_periodMap_eq_base_of_y_eq_zero _ _ (mk_y _ _ _),
      _root_.GlobalTheory.AnArc.degeneratingTori_periodMap_eq_base_of_y_eq_zero _ _ (mk_y _ _ _)]
  set v' : A.V := v + A.P0 L + A.P0 M
  have hv : v + A.Pw w la = v' + A.Pw w Y := by
    rw [hPw]
    simp only [v']
    abel
  have key := A.term_add_Pw_y j α th w μ y v'
  rw [← hv] at key
  have hterm : A.term j α th (μ + y) v' =
      (A.chi l * Complex.exp (Real.pi * A.H v.2 l + Real.pi / 2 * A.H l l)) ^ j *
        A.term j α th (μ + y) v := by
    rw [_root_.GlobalTheory.AnArc.term_add_P0_n,
      _root_.GlobalTheory.AnArc.term_add_P0_l A h]
  have hv1 : v'.1 y = v.1 y + (n y : ℂ) + -(A.H (A.ct y) l / (2 * Complex.I)) := by
    simp [v', L, M, Prod.fst_add, _root_.GlobalTheory.AnArc.degeneratingTori_basePeriodMap_fst_apply, mk_y, mk_n, mk_l]
    ring
  set X : ℂ := A.psi y * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (v.1 y) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.q y)
  set X' : ℂ := A.psi y * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (v'.1 y) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.q y)
  have hX' : X' = X * Complex.exp (-(Real.pi * A.H (A.ct y) l)) := by
    simp only [X', X, hv1, _root_.GlobalTheory.AnArc.e_add, _root_.GlobalTheory.AnArc.e_intCast, _root_.GlobalTheory.AnArc.e_neg_div]
    ring
  have hX'0 : X' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Units.ne_zero _) (_root_.GlobalTheory.AnArc.e_ne_zero _)) (_root_.GlobalTheory.AnArc.e_ne_zero _)
  have hfac : A.perFactor w la v =
      A.chi l * Complex.exp (Real.pi * A.H v.2 l + Real.pi / 2 * A.H l l) * X'⁻¹ := by
    rw [_root_.GlobalTheory.AnArc.perFactor, ← hy, ← hl, _root_.GlobalTheory.AnArc.ah_add, hX']
    simp only [mul_inv, ← Complex.exp_neg, neg_neg, _root_.GlobalTheory.AnArc.ah, X]
    ring
  calc A.term j α th μ (v + A.Pw w la) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α μ)
      = (X' ^ j)⁻¹ *
          (X' ^ j * (A.term j α th μ (v + A.Pw w la) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α μ))) := by
        rw [inv_mul_cancel_left₀ (pow_ne_zero _ hX'0)]
    _ = _ := by
        rw [key, hterm, hfac]
        ring


open AlgebraicGeometry CategoryTheory Limits in
variable {O : Type} [CommRing O] [StarRing O] (A : _root_.GlobalTheory.AnArc O) in
theorem _root_.GlobalTheory.AnArc.Sum_add_period {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (w : ℂ)
    (la : A.La) (v : A.V) :
    A.Sum j α th w (v + A.Pw w la) = A.perFactor w la v ^ j * A.Sum j α th w v := by
  simp only [_root_.GlobalTheory.AnArc.Sum, A.term_add_period h w la]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight la.y).tsum_eq
    fun μ => A.term j α th μ v * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α μ)

def FSumShift (k : ℕ) [NeZero k] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (la : A.La) (z : A.V) : LaurentSeries ℂ :=
  HahnSeries.ofSuppBddBelow
    (fun n => ∑ μ ∈ A.level k (α + la.y) (n - A.be la.y α / k), A.term k α th μ (z + (k : ℂ)⁻¹ • A.P0 la))
    ⟨-A.be (α + la.y) (α + la.y) + A.be la.y α / k, fun n hn => by
      by_contra h
      exact hn (by simp only [A.level_eq_empty (j := k) (α := α + la.y) (n := n - A.be la.y α / k) (by omega),
        Finset.sum_empty])⟩

theorem coeff_FSumShift (k : ℕ) [NeZero k] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (la : A.La) (z : A.V) (n : ℤ) :
    (A.FSumShift k α th la z).coeff n =
      ∑ μ ∈ A.level k (α + la.y) (n - A.be la.y α / k), A.term k α th μ (z + (k : ℂ)⁻¹ • A.P0 la) := rfl

end AnArc

section Along

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

def IsRigFrame (L : RigLB G) (y : Sp ℂ ⟶ S) (e : V → (Sp ℂ ⟶ G.left)) (fr : L.L.ι → V → ℂ) : Prop :=
  (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.L.U j}) ∧ (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.L.U j → fr j z ≠ 0) ∧
    (∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.L.U j ⊓ L.L.U j') →
      fr j z = valAt' (e z) (L.L.U j ⊓ L.L.U j') (L.L.g j j').val * fr j' z) ∧
    ∀ j, ⊤ ≤ e 0 ⁻¹ᵁ L.L.U j → fr j 0 = valAt' y ((L.L.pull (eSec G)).U (fun _ => j)) (L.rig.s (fun _ => j)).val

variable {V' : Type} [NormedAddCommGroup V'] [NormedSpace ℂ V']


end Along

end GlobalTheory
end
end

section

noncomputable section

namespace GlobalTheory.ArcCM

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) [StarRing (𝓞 E)]

def AbDat (A : AnArc (𝓞 E)) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂) : Prop :=
  (∀ a z i, A.F a z i = tyB i (a : E) * z i) ∧ IsTypeFn H DB.p DB.q tyB ∧
    (∀ (a : 𝓞 E) x, eB (a • x) = A.FLam a (eB x)) ∧ (∀ x x', DB.EF x x' = A.Ef (eB x) (eB x')) ∧
    IsPeriod DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom)

def PrimAn (A : AnArc (𝓞 E)) : Prop :=
  (∀ l, A.chi l = (-1) ^ A.Ef (A.FLam H.w0 l) l) ∧ ∀ x, (A.psi x : ℂ) = eTwoPi (A.T x (H.w0 • x))


omit [IsCMField E] [NumberField E] in
def NormAn (A : AnArc (𝓞 E)) (n : ℕ) : Prop :=
  (∀ y, n • A.ct y ∈ A.abelian₂) ∧
    ∀ y y', eTwoPi (A.T (n • y) (n • y')) * Complex.exp (Real.pi * A.H (n • A.ct y) (n • A.ct y')) = 1

end GlobalTheory.ArcCM
end
end

section

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure GtAn [Algebra (FractionRing ℂ) ℂ] {b : O →+* ℂ} (a : ArcIn D l β ℂ b) where
  star_eq : (inferInstance : StarRing (𝓞 E)) = H.starRing
  A : AnArc (𝓞 E)
  ε : A.X ≃ₗ[𝓞 E] a.D₀.X
  be_eq : ∀ x y, A.be x y = a.be (ε x) (ε y)
  gB_eq : A.gB = a.D₀.P.g
  u : HolUnif a.D₀.P.A a.D₀.P.L A.gB
  lam : u.Λ = A.abelian₂
  ah : u.IsAH A.Hm (fun m => A.chi ⟨m.1, lam ▸ m.2⟩)
  rig : u.IsRig a.D₀.rig
  tan : (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v
  pow : ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn A.Hm (fun m => A.chi ⟨m.1, lam ▸ m.2⟩) n θ ∧ u.IsFnPow n s θ) ∧
    ∀ θ, u.IsThetaFn A.Hm (fun m => A.chi ⟨m.1, lam ▸ m.2⟩) n θ → ∃! s, u.IsFnPow n s θ
  act : ∀ x z, u.ex (A.F x z) = u.ex z ≫ (letI := H.starRing; a.oa.onB.act x)
  ct : ∀ x, u.ex (A.ct x) = a.D₀.c (ε x)
  psi : ∀ x, FrameValue.genVal u a.D₀.P.isLB (a.D₀.psi (ε x)) (Out.jFK (R := ℂ) ℂ) (fun _ => A.ct x) = A.psi x
  ex0 : A.V → Out.GtPtF a.D₀ ℂ
  ex0_b : ∀ v, (show Sp ℂ ⟶ _ from (ex0 v).b.left) = (u.ex v.2).left
  arcDict_expZero_section : ∀ v x, FrameValue.genVal u a.D₀.P.isLB ((ex0 v).s (ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
    ![A.ct x + v.2, A.ct x, v.2, 0] = eTwoPi (v.1 x)

def GtAn.fn [Algebra (FractionRing ℂ) ℂ] {b : O →+* ℂ} {a : ArcIn D l β ℂ b} (Λ : GtAn a) (j : ℕ) (α : Λ.A.X)
    (s : a.D₀.SecB j (Λ.ε α)) (z : Fin Λ.A.gB → ℂ) : ℂ :=
  FrameValue.secVal Λ.u a.D₀.P.isLB s (Λ.u.ex z).left ![z, z + Λ.A.ct α, Λ.A.ct α, 0]

def GtAn.Rep [Algebra (FractionRing ℂ) ℂ] {b : O →+* ℂ} {a : ArcIn D l β ℂ b} (Λ : GtAn a) (k : ℕ)
    (p : Out.QkPt a.D₀ (FractionRing ℂ) k) (la : Λ.A.La) : Prop :=
  ∀ q : Out.QkPt a.D₀ ℂ k, QkExt (algebraMap _ ℂ) p q → q.y = Λ.ε la.y ∧ q.g = Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 la)

end GlobalTheory.ArcPts
end
end
