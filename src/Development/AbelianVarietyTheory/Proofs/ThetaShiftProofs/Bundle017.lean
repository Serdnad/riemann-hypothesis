module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle011
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.AnalyticTorusPointBaseEqHolUnifEx
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts.GtKer

theorem ker_iota_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a), (∀ z, (Λ.ex0 z).IsZero ↔ ∃ la : Λ.A.La, la.y = 0 ∧ z = Λ.A.P0 la) ∧ (∀ la : Λ.A.La, Out.GtPtF.IsIota (Λ.ε la.y) (Λ.ex0 (Λ.A.P0 la))) ∧ (∀ lam : Λ.A.X →+ ℂ, IsTorusPt (Λ.ex0 (lam, 0)) (fun x => eTwoPi (lam (Λ.ε.symm x)))) ∧ ∀ z x, IsTorusPt (Λ.ex0 z) x → z.2 ∈ Λ.A.abelian₂ := by
  intro E _ _ _ H _ D l c O _ β _ _ b a Λ
  refine ⟨GtAnModel.isZero_iff Λ, GtAnModel.isIota Λ, fun lam => ⟨?_, fun x j hc hj => ?_⟩, fun z x h => ?_⟩
  · rw [GtAnModel.analyticTorusPoint_base_eq_holUnif_ex, GtAnModel.ex_zero]
  · obtain ⟨x, rfl⟩ := Λ.ε.surjective x
    have hz := GtAnModel.isLift_gt Λ (lam, 0) x
    have h := FrameValue.valAt'_gen a.D₀.P.isLB ((Λ.ex0 (lam, 0)).isGen _) hz (j := j) hj
    have h1 := Λ.arcDict_expZero_section (lam, 0) x
    have e : ∀ k k', ![Λ.A.ct x + (0 : Fin Λ.A.gB → ℂ), Λ.A.ct x, 0, 0] k = ![Λ.A.ct x + 0, Λ.A.ct x, 0, 0] k' →
        j k = j k' := fun k k' hk =>
      hc k k' (((Category.id_comp _).symm.trans (hz k)).trans
        ((congrArg (fun w => (Λ.u.ex w).left) hk).trans ((Category.id_comp _).symm.trans (hz k')).symm))
    have e₁ : j 0 = j 1 := e 0 1 (by simp)
    have e₂ : j 2 = j 3 := e 2 3 (by simp)
    have n₁ := Λ.u.fr_ne _ _ ((hz.le_iff j).1 hj 1)
    have n₃ := Λ.u.fr_ne _ _ ((hz.le_iff j).1 hj 3)
    have hf : FrameValue.frameProd Λ.u Out.DegPre.gtε ![Λ.A.ct x + (0 : Fin Λ.A.gB → ℂ), Λ.A.ct x, 0, 0] j = 1 := by
      simp only [Matrix.cons_val] at n₁ n₃
      simp only [FrameValue.frameProd, Fin.prod_univ_four, Out.DegPre.gtε, Matrix.cons_val, e₁, e₂, add_zero,
        zpow_neg, zpow_one]
      field_simp
    refine h.trans ((congrArg₂ (· * ·) h1 hf).trans ?_)
    simp
  · have h0 : Λ.u.ex z.2 = 1 := Over.OverMorphism.ext ((Λ.ex0_b z).symm.trans ((congrArg (·.left) h.1).trans
      ((toUnit_TF_comp_left _).trans (by rw [Hom.one_def, toUnit_unit, Category.id_comp]))))
    exact Λ.lam.le ((Λ.u.ker _).1 h0)

end GlobalTheory.ArcPts.GtKer
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section
namespace GlobalTheory.GermRing
open GlobalTheory.Conv

def Rep (w : ℂ) (f : ℂ⸨X⸩) (x : ℂ) : Prop :=
  ∃ (T : ℝ) (hw : T < w.im) (a s : halfRing T),
    ev T w hw s ≠ 0 ∧ (s : ℂ⸨X⸩) * f = a ∧ ev T w hw a = x * ev T w hw s

theorem Rep.common {w : ℂ} {f g : ℂ⸨X⸩} {x y : ℂ} (hf : Rep w f x) (hg : Rep w g y) :
    ∃ (T : ℝ) (hw : T < w.im) (a s b t : halfRing T),
      (ev T w hw s ≠ 0 ∧ (s : ℂ⸨X⸩) * f = a ∧ ev T w hw a = x * ev T w hw s) ∧
      (ev T w hw t ≠ 0 ∧ (t : ℂ⸨X⸩) * g = b ∧ ev T w hw b = y * ev T w hw t) := by
  obtain ⟨T, hw, a, s, h⟩ := hf
  obtain ⟨T', hw', b, t, h'⟩ := hg
  exact ⟨max T T', max_lt hw hw', ⟨a, halfRing_mono (le_max_left _ _) a.2⟩,
    ⟨s, halfRing_mono (le_max_left _ _) s.2⟩, ⟨b, halfRing_mono (le_max_right _ _) b.2⟩,
    ⟨t, halfRing_mono (le_max_right _ _) t.2⟩, h, h'⟩

theorem Rep.unique {w : ℂ} {f : ℂ⸨X⸩} {x y : ℂ} (hx : Rep w f x) (hy : Rep w f y) : x = y := by
  obtain ⟨T, hw, a, s, b, t, ⟨h1, h2, h3⟩, k1, k2, k3⟩ := hx.common hy
  have e : a * t = b * s := Subtype.ext (by
    push_cast
    rw [← h2, ← k2]; ring)
  have e' := congrArg (ev T w hw) e
  rw [map_mul, map_mul, h3, k3] at e'
  apply mul_right_cancel₀ (mul_ne_zero h1 k1)
  linear_combination e'

theorem Rep.add {w : ℂ} {f g : ℂ⸨X⸩} {x y : ℂ} (hx : Rep w f x) (hy : Rep w g y) :
    Rep w (f + g) (x + y) := by
  obtain ⟨T, hw, a, s, b, t, ⟨h1, h2, h3⟩, k1, k2, k3⟩ := hx.common hy
  refine ⟨T, hw, a * t + b * s, s * t, by rw [map_mul]; exact mul_ne_zero h1 k1, ?_, ?_⟩
  · push_cast
    rw [← h2, ← k2]; ring
  · rw [map_add (f := _), map_mul, map_mul, map_mul, h3, k3]; ring

theorem Rep.mul {w : ℂ} {f g : ℂ⸨X⸩} {x y : ℂ} (hx : Rep w f x) (hy : Rep w g y) :
    Rep w (f * g) (x * y) := by
  obtain ⟨T, hw, a, s, b, t, ⟨h1, h2, h3⟩, k1, k2, k3⟩ := hx.common hy
  refine ⟨T, hw, a * b, s * t, by rw [map_mul]; exact mul_ne_zero h1 k1, ?_, ?_⟩
  · push_cast
    rw [← h2, ← k2]; ring
  · rw [map_mul, map_mul, h3, k3]; ring

theorem rep_of_mem {T : ℝ} {w : ℂ} (hw : T < w.im) (s : halfRing T) :
    Rep w (s : ℂ⸨X⸩) (ev T w hw s) :=
  ⟨T, hw, s, 1, by rw [map_one]; exact one_ne_zero, by simp, by rw [map_one, _root_.mul_one]⟩

theorem rep_algebraMap (w c : ℂ) : Rep w (algebraMap ℂ ℂ⸨X⸩ c) c := by
  have hw : w.im - 1 < w.im := sub_one_lt _
  have h := rep_of_mem hw (algebraMap ℂ (halfRing (w.im - 1)) c)
  rw [AlgHom.commutes] at h
  exact h

theorem Rep.inv {w : ℂ} {f : ℂ⸨X⸩} {x : ℂ} (hx : Rep w f x) (h0 : x ≠ 0) :
    ∃ g, Rep w g x⁻¹ ∧ f * g = 1 := by
  obtain ⟨T, hw, a, s, h1, h2, h3⟩ := hx
  have ha : ev T w hw a ≠ 0 := by rw [h3]; exact mul_ne_zero h0 h1
  have ha' : (a : ℂ⸨X⸩) ≠ 0 := fun h => ha (by rw [show a = 0 from Subtype.ext h, map_zero])
  have hf : f ≠ 0 := fun h => ha' (by rw [← h2, h, mul_zero])
  refine ⟨f⁻¹, ⟨T, hw, s, a, ha, ?_, ?_⟩, mul_inv_cancel₀ hf⟩
  · rw [← h2, _root_.mul_assoc, mul_inv_cancel₀ hf, _root_.mul_one]
  · rw [h3, ← _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.one_mul]

def ring (w : ℂ) : Subalgebra ℂ ℂ⸨X⸩ where
  carrier := {f | ∃ x, Rep w f x}
  mul_mem' := fun ⟨_, hx⟩ ⟨_, hy⟩ => ⟨_, hx.mul hy⟩
  add_mem' := fun ⟨_, hx⟩ ⟨_, hy⟩ => ⟨_, hx.add hy⟩
  algebraMap_mem' c := ⟨c, rep_algebraMap w c⟩

def val (w : ℂ) (f : ring w) : ℂ := Classical.choose (show ∃ x, Rep w f x from f.2)

theorem rep_val (w : ℂ) (f : ring w) : Rep w f (val w f) := Classical.choose_spec (show ∃ x, Rep w f x from f.2)

def evRing (w : ℂ) : ring w →ₐ[ℂ] ℂ where
  toFun := val w
  map_one' := (rep_val w 1).unique (by simpa using rep_algebraMap w 1)
  map_mul' f g := (rep_val w (f * g)).unique ((rep_val w f).mul (rep_val w g))
  map_zero' := (rep_val w 0).unique (by simpa using rep_algebraMap w 0)
  map_add' f g := (rep_val w (f + g)).unique ((rep_val w f).add (rep_val w g))
  commutes' c := (rep_val w _).unique (rep_algebraMap w c)

def germs : Germs where
  R := ring
  ev := evRing
  unit w s hs := by
    obtain ⟨g, hg, h⟩ := (rep_val w s).inv hs
    exact IsUnit.of_mul_eq_one (⟨g, _, hg⟩ : ring w) (Subtype.ext h)
  le T w hw f hf := ⟨_, rep_of_mem hw ⟨f, hf⟩⟩
  ev_eq T w hw s := (rep_val w _).unique (rep_of_mem hw s)
  frac w f := by
    obtain ⟨T, hw, a, s, h1, h2, -⟩ := rep_val w f
    exact ⟨T, hw, a, s, h1, h2⟩

theorem germs_spec : Nonempty Germs ∧ ∀ (Γ : Germs) (w : ℂ), IsLocalRing (Γ.R w) ∧ (∀ f : Γ.R w, (f : ℂ⸨X⸩) ∈ Conv.convLaurent) ∧ ∀ (f : Γ.R w) (g : ℂ⸨X⸩), Γ.ev w f ≠ 0 → (f : ℂ⸨X⸩) * g ∈ Γ.R w → g ∈ Γ.R w := by
  refine ⟨⟨germs⟩, fun Γ w => ⟨?_, fun f => ?_, fun f g hf h => ?_⟩⟩
  · refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f => ?_
    by_cases h : Γ.ev w f = 0
    · exact Or.inr (Γ.unit w _ (by rw [map_sub, map_one, h, sub_zero]; exact one_ne_zero))
    · exact Or.inl (Γ.unit w _ h)
  · obtain ⟨T, hw, a, s, h1, h2⟩ := Γ.frac w f
    have hs : (s : ℂ⸨X⸩) ≠ 0 := fun h => h1 (by rw [show s = 0 from Subtype.ext h, map_zero])
    have e : (f : ℂ⸨X⸩) = (s : ℂ⸨X⸩)⁻¹ * a := by
      rw [← h2, ← _root_.mul_assoc, inv_mul_cancel₀ hs, _root_.one_mul]
    rw [e]
    exact mul_mem (convLaurent.inv_mem (halfRing_le_convLaurent T s.2)) (halfRing_le_convLaurent T a.2)
  · obtain ⟨k, hk⟩ := (Γ.unit w f hf).exists_left_inv
    have hk' : (k : ℂ⸨X⸩) * f = 1 := congrArg Subtype.val hk
    have e : g = k * (f * g) := by rw [← _root_.mul_assoc, hk', _root_.one_mul]
    rw [e]
    exact mul_mem k.2 h

end GlobalTheory.GermRing
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem isFShift_iff {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (k : ℕ) [NeZero k] (α : A.X)
    (th : (Fin A.gB → ℂ) → ℂ) (la : A.La) (z : A.V) (F : ℂ⸨X⸩)
    (hd : (k : ℤ) ∣ A.be la.y α := by apply_assumption) :
    IsFShift A k α th la z F ↔ F = A.FSumShift k α th la z := by
  have key : ∀ n : ℤ, (∑ᶠ (m : A.X) (_ : A.exponent k (α + la.y) m + A.be la.y α / k = n),
      A.term k α th m (z + (k : ℂ)⁻¹ • A.P0 la)) = (A.FSumShift k α th la z).coeff n := fun n => by
    rw [AnArc.coeff_FSumShift]
    refine finsum_cond_eq_sum_of_cond_iff _ fun {m} _ => ?_
    rw [AnArc.mem_level, eq_sub_iff_add_eq]
  unfold IsFShift
  simp only [key]
  exact ⟨fun h => HahnSeries.ext (funext h.2), fun h => ⟨⟨NeZero.ne k, hd⟩, fun n => by rw [h]⟩⟩

theorem theta_sum_shift : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∀ (k : ℕ) [NeZero k] (la : A.La), (∀ α, (k : ℤ) ∣ A.be la.y α) → ∃ cz : A.V → ℂ, (∀ z, cz z ≠ 0) ∧ ∀ α, ∀ th ∈ A.Theta k α, ∃ th' ∈ A.Theta k (α + la.y), (th ≠ 0 → th' ≠ 0) ∧ ∀ z, (∀ F, IsFShift A k α th la z F ↔ F = HahnSeries.single (A.be la.y α / k) (cz z) * A.FSum k (α + la.y) th' z) ∧ ∀ w : ℂ, A.Sum k α th w (z + (k : ℂ)⁻¹ • A.Pw w la) = cz z * eTwoPi (w * ((A.be la.y α / k : ℤ) : ℂ)) * A.Sum k (α + la.y) th' w z := by
  intro O _ _ A k _ la hla
  have hk : (k : ℂ) ≠ 0 := NeZero.ne _
  refine ⟨fun z => Complex.exp (A.lin la z), fun z => Complex.exp_ne_zero _, fun α th hth =>
    ⟨A.shift k la α th, A.shift_mem_Theta hth la, fun h h' => h ?_, fun z => ⟨fun F => ?_, fun w => ?_⟩⟩⟩
  · exact A.shift_injective k la α (h'.trans (map_zero _).symm)
  · rw [isFShift_iff A k α th la z F (hla α), A.FSumShift_eq k la (Int.mul_ediv_cancel' (hla α)).symm]
  · obtain ⟨m, hm⟩ := hla α
    rw [A.Sum_add_Pw_div, hm, Int.mul_ediv_cancel_left _ (NeZero.ne (k : ℤ))]
    congr 3
    push_cast
    field_simp

end GlobalTheory.ArcPts
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory

theorem AnArc.FSum_sum_smul {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (j : ℕ) [NeZero j] (α : A.X)
    {K : Type} (s : Finset K) (c : K → ℂ) (th : K → (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSum j α (∑ i ∈ s, c i • th i) v = ∑ i ∈ s, HahnSeries.single 0 (c i) * A.FSum j α (th i) v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := A.FSum_smul j α 0 0 v
    rw [zero_smul, zero_smul] at h
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, A.FSum_add, ih, A.FSum_smul,
      HahnSeries.single_zero_mul_eq_smul]

theorem AnArc.exists_basis_FSum : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), AnFin A → ∀ (j : ℕ) [NeZero j], ∃ (n : ℕ) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ) (T₀ : ℝ), (∀ i, th i ∈ A.Theta j (α i)) ∧ LinearIndependent ℂ⸨X⸩ (fun i v => A.FSum j (α i) (th i) v) ∧ (∀ w : ℂ, T₀ < w.im → LinearIndependent ℂ (fun i v => A.Sum j (α i) (th i) w v)) ∧ ∀ α', ∀ th' ∈ A.Theta j α', ∃ r : Fin n → ℂ⸨X⸩, (∀ i T, r i ∈ Conv.halfRing T) ∧ ∀ v, A.FSum j α' th' v = ∑ i, r i * A.FSum j (α i) (th i) v := by
  intro O _ _ A hA j _
  classical
  have hj : 1 ≤ j := Nat.one_le_iff_ne_zero.2 (NeZero.ne j)
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul A.X j hj
  obtain ⟨T₀, hT⟩ := A.exists_isConvLine
  have : ∀ c, Module.Finite ℂ (A.Theta j (e c)) := fun c => hA.1 j (e c) hj
  let b := fun c => Module.finBasis ℂ (A.Theta j (e c))
  let I := fun c => Fin (Module.finrank ℂ (A.Theta j (e c)))
  let t : ∀ c, I c → (Fin A.gB → ℂ) → ℂ := fun c i => b c i
  have ht : ∀ c, LinearIndependent ℂ (t c) := fun c =>
    (b c).linearIndependent.map' (A.Theta j (e c)).subtype (Submodule.ker_subtype _)
  have htm : ∀ c i, t c i ∈ A.Theta j (e c) := fun c i => (b c i).2
  have hrep : ∀ c c' y, e c = e c' + j • y → c = c' := fun c c' y h =>
    (he (e c)).unique ⟨0, by simp⟩ ⟨y, h⟩
  let s := (Fintype.equivFin (Σ c, I c)).symm
  refine ⟨_, fun i => e (s i).1, fun i => t (s i).1 (s i).2, T₀, fun i => htm _ _,
    (A.linearIndependent_FSum_sigma hrep ht).comp s s.injective, fun w hw =>
    (A.linearIndependent_Sum_sigma (NeZero.ne j) hrep ht w fun c i z =>
      AnArc.summable_term hT (NeZero.ne j) (htm c i) hw (0, z)).comp s s.injective, fun α' th' hth' => ?_⟩
  obtain ⟨c, ⟨m, hm⟩, -⟩ := he α'
  have hα : α' + j • (-m) = e c := by rw [hm]; simp
  have hmem := A.translate_mem_Theta hth' (-m)
  rw [hα] at hmem
  let x := (b c).repr ⟨_, hmem⟩
  have hx : (fun z => th' (z + A.ct (-m))) = ∑ i, x i • t c i := by
    have := congrArg Subtype.val ((b c).sum_repr ⟨_, hmem⟩)
    rw [Submodule.coe_sum] at this
    exact this.symm
  let u : ℂ⸨X⸩ := HahnSeries.single (A.exponent j α' (-m)) ((A.psi (-m) : ℂ) ^ j * eTwoPi (A.T (-m) α'))
  obtain ⟨r, hr1, hr0⟩ : ∃ r : ∀ c', I c' → ℂ⸨X⸩, (∀ i, r c i = u * HahnSeries.single 0 (x i)) ∧
      ∀ c', c' ≠ c → ∀ i, r c' i = 0 :=
    ⟨Pi.single (M := fun c' => I c' → ℂ⸨X⸩) c fun i => u * HahnSeries.single 0 (x i),
      fun i => by rw [Pi.single_eq_same], fun c' h i => by rw [Pi.single_eq_of_ne h]; rfl⟩
  refine ⟨fun i => r (s i).1 (s i).2, fun i T => ?_, fun v => ?_⟩
  · beta_reduce
    generalize s i = p
    obtain ⟨c', i'⟩ := p
    by_cases h : c' = c
    · subst h
      rw [hr1]
      exact mul_mem (Conv.single_mem_halfRing _ _ _) (Conv.single_mem_halfRing _ _ _)
    · rw [hr0 c' h]
      exact zero_mem _
  · rw [s.sum_comp (fun p : Σ c, I c => r p.1 p.2 * A.FSum j (e p.1) (t p.1 p.2) v), Fintype.sum_sigma,
      Finset.sum_eq_single c (fun c' _ h => by simp [hr0 c' h]) (by simp),
      A.FSum_eq_translate j α' th' (-m) v, hα, hx, A.FSum_sum_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hr1, _root_.mul_assoc]

end GlobalTheory
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecCoord

theorem germ_le_preimage (Γ : Germs) (w : ℂ) {Z : Scheme.{0}} (x : Sp (Γ.R w) ⟶ Z) (U : Z.Opens)
    (h : ⊤ ≤ (spMap (Γ.ev w).toRingHom ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro q _
  let p : PrimeSpectrum (Γ.R w) := spMap (Γ.ev w).toRingHom (default : PrimeSpectrum ℂ)
  have hp : p ∈ (show Set (PrimeSpectrum (Γ.R w)) from (x ⁻¹ᵁ U).carrier) :=
    h (x := (default : PrimeSpectrum ℂ)) trivial
  have hle : (show PrimeSpectrum (Γ.R w) from q) ≤ p := by
    intro s hs
    by_contra hn
    refine (show PrimeSpectrum (Γ.R w) from q).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hs (Γ.unit w s fun h0 => hn ?_))
    show (Γ.ev w).toRingHom s ∈ (default : PrimeSpectrum ℂ).asIdeal
    rw [show (Γ.ev w).toRingHom s = 0 from h0]
    exact zero_mem _
  exact ((PrimeSpectrum.le_iff_specializes _ _).1 hle).mem_open (x ⁻¹ᵁ U).isOpen hp

theorem comp_le_preimage {X Y Z : Scheme.{0}} (g : X ⟶ Y) (x : Y ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ (g ≫ x) ⁻¹ᵁ U := fun p _ => h (x := g p) trivial

theorem exists_ev_le_preimage {Z : Scheme.{0}} {T : ℝ} (yT : Sp (Conv.halfRing T) ⟶ Z) (U : Z.Opens)
    (hU : ⊤ ≤ (spMap (Conv.halfRing T).val.toRingHom ≫ yT) ⁻¹ᵁ U) :
    ∃ T' ≥ T, ∀ w : ℂ, T' < w.im → ∀ hw : T < w.im, ⊤ ≤ (spMap (Conv.ev T w hw).toRingHom ≫ yT) ⁻¹ᵁ U := by
  have hfac : spMap (Conv.halfRing T).val.toRingHom ≫ yT =
      spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫
        (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) := by
    rw [← Category.assoc, ← spMap_comp]
    rfl
  have hU' : ⊤ ≤ (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) ⁻¹ᵁ U := by
    intro p _
    rw [hfac] at hU
    obtain rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
      Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
    exact hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial
  obtain ⟨T', h, hT'⟩ := Conv.exists_le_preimage_inclusion yT hU'
  refine ⟨T', h, fun w hw' hw => ?_⟩
  have e : (Conv.ev T w hw).toRingHom = (Conv.ev T' w hw').toRingHom.comp
      (Subalgebra.inclusion (Conv.halfRing_mono h) : Conv.halfRing T →+* Conv.halfRing T') :=
    RingHom.ext fun r => Conv.ev_congr hw hw' rfl
  rw [e, spMap_comp, Category.assoc]
  exact comp_le_preimage _ _ _ hT'

theorem spec_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), ∀ (N : ℕ) [NeZero N] (C : Coords Φ N), ∃ T' ≥ Ψ.T, ∃ hT : C.T ≤ T', ∀ w (hw : T' < w.im), ⊤ ≤ Ψ.yw w ⁻¹ᵁ C.U ∧ (∀ hw', ⊤ ≤ (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw')).toRingHom ≫ Ψ.yT) ⁻¹ᵁ C.U) ∧ ∀ i v (x' : Sp ℂ ⟶ (o.t.G.hom ⁻¹ᵁ C.U).toScheme) (j : o.t.PP.L.ι), x' ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Ψ.pi w v).left → ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j → valR x' ((Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) = Conv.ev C.T w (lt_of_le_of_lt hT hw) (C.cf i v) * Ψ.fr w j v ^ N := by
  intro E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ N _ C
  obtain ⟨T₁, hT₁, hU⟩ := exists_ev_le_preimage Ψ.yT C.U (by rw [Ψ.yT_gen]; exact C.mem)
  refine ⟨max T₁ C.T, le_max_of_le_left hT₁, le_max_right _ _, fun w hw => ?_⟩
  have hw1 : T₁ < w.im := (le_max_left _ _).trans_lt hw
  have hwC : C.T < w.im := (le_max_right _ _).trans_lt hw
  have hwT : Ψ.T < w.im := lt_of_le_of_lt hT₁ hw1
  have hy : ⊤ ≤ Ψ.yw w ⁻¹ᵁ C.U := by
    rw [Ψ.yw_eq w hwT]
    exact hU w hw1 hwT
  have hg : ⊤ ≤ (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hwT)).toRingHom ≫ Ψ.yT) ⁻¹ᵁ C.U := by
    apply germ_le_preimage
    have e : (Γ.ev w).toRingHom.comp (Subalgebra.inclusion (Γ.le Ψ.T w hwT)).toRingHom =
        (Conv.ev Ψ.T w hwT).toRingHom := RingHom.ext fun r => Γ.ev_eq Ψ.T w hwT r
    rw [← Category.assoc, ← spMap_comp, e, ← Ψ.yw_eq w hwT]
    exact hy
  refine ⟨hy, fun _ => hg, fun i v x' j hx' hj => ?_⟩
  have hxU : ⊤ ≤ (Ψ.xt w hwT v).left ⁻¹ᵁ (o.t.G.hom ⁻¹ᵁ C.U) := by
    rw [← Scheme.Hom.comp_preimage, Over.w]
    exact hg
  have hxj : ⊤ ≤ (Ψ.xt w hwT v).left ⁻¹ᵁ o.t.PP.L.U j := by
    apply germ_le_preimage
    rw [← Ψ.pi_eq w hwT v]
    exact hj
  obtain ⟨z, hz⟩ : ∃ z : Sp (Γ.R w) ⟶ (o.t.G.hom ⁻¹ᵁ C.U).toScheme,
      z ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Ψ.xt w hwT v).left :=
    ⟨IsOpenImmersion.lift (o.t.G.hom ⁻¹ᵁ C.U).ι (Ψ.xt w hwT v).left (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hxU (x := p) trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have hzj : ⊤ ≤ z ⁻¹ᵁ (Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j) := by
    intro p _
    rw [← hz] at hxj
    exact Set.mem_iInter.2 fun _ => hxj (x := p) trivial
  have ex : x' = spMap (Γ.ev w).toRingHom ≫ z := by
    rw [← cancel_mono (o.t.G.hom ⁻¹ᵁ C.U).ι, hx', Category.assoc, hz, Ψ.pi_eq w hwT v]
  have hgen : (spMap (Γ.R w).val.toRingHom ≫ z) ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Φ.x v).left := by
    rw [Category.assoc, hz, Ψ.xt_gen]
  have hv := C.val i v _ j hgen (by rw [← Ψ.xt_gen w hwT v]; exact comp_le_preimage _ _ _ hxj)
  rw [HolHom.valR_spMap _ _ _ hzj, ← Ψ.τt_gen w hwT v j hxj] at hv
  have hr : valR z ((Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) =
      Subalgebra.inclusion (Γ.le C.T w hwC) (C.cf i v) * Ψ.τt w v j ^ N := Subtype.ext hv
  rw [ex, HolHom.valR_spMap _ _ _ hzj, hr, map_mul, map_pow]
  exact congrArg (· * _) (Γ.ev_eq C.T w hwC (C.cf i v))

end GlobalTheory.SpecCoord
end
end

section

noncomputable section

namespace GlobalTheory.ArcPts

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory Filter
open scoped LaurentSeries PowerSeries

theorem exists_coeff_mem_subfield {k L V ι : Type*} [Field k] [Field L] [Algebra k L] [Fintype ι]
    (K : IntermediateField k L) (r : ι → L) (g : ι → V → L) (f : V → L) (hg : ∀ i v, g i v ∈ K)
    (hf : ∀ v, f v ∈ K) (h : ∀ v, f v = ∑ i, r i * g i v) :
    ∃ s : ι → L, (∀ i, s i ∈ K) ∧ ∀ v, f v = ∑ i, s i * g i v := by
  obtain ⟨π, hπ⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)
  refine ⟨fun i => π (r i), fun i => (π (r i)).2, fun v => ?_⟩
  have h1 : π (f v) = ⟨f v, hf v⟩ := LinearMap.congr_fun hπ ⟨f v, hf v⟩
  have h2 : π (f v) = ∑ i, π (r i) * ⟨g i v, hg i v⟩ := by

    rw [h v, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : r i * g i v = (⟨g i v, hg i v⟩ : K) • r i := by
      rw [mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have h3 := congrArg (fun x : K => (x : L)) (h1.symm.trans h2)
  simpa using h3

theorem exists_isComb_halfRing : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), AnFin A →
    ∀ (j : ℕ) [NeZero j] (f : A.V → ℂ⸨X⸩), IsComb A j Set.univ f → (∀ v, f v ∈ Conv.convLaurent) →
    ∃ T : ℝ, IsComb A j (Conv.halfRing T) f ∧ ∀ v, f v ∈ Conv.halfRing T := by
  rintro O _ _ A - j _ f ⟨n, r, α, th, h1, h2⟩ hf
  obtain ⟨T₀, h₀⟩ := A.exists_isConvLine
  have hm : ∀ i v, A.FSum j (α i) (th i) v ∈ Conv.halfRing T₀ := fun i v _ hw =>
    (AnArc.hasSum_coeff_FSum h₀ (h1 i).2 hw v).summable
  obtain ⟨s, hs, hfs⟩ := exists_coeff_mem_subfield Conv.convLaurent r (fun i v => A.FSum j (α i) (th i) v) f
    (fun i v => Conv.halfRing_le_convLaurent T₀ (hm i v)) hf h2
  obtain ⟨T, hT, hT₀⟩ := ((eventually_all.2 fun i => Conv.eventually_mem_halfRing (hs i)).and
    (eventually_ge_atTop T₀)).exists
  refine ⟨T, ⟨n, s, α, th, fun i => ⟨hT i, (h1 i).2⟩, hfs⟩, fun v => ?_⟩
  rw [hfs v]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hT i) (Conv.halfRing_mono hT₀ (hm i v))

end GlobalTheory.ArcPts
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem ex0_additive_surjective_equivariant : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b)
    (Λ : GtAn a), (∀ z z', (Λ.ex0 z).IsAdd (Λ.ex0 z') (Λ.ex0 (z + z'))) ∧ Function.Surjective Λ.ex0 ∧
      ∀ (x : 𝓞 E) z, @GtAct ℂ _ _ (𝓞 E) _ H.starRing a.D₀ ℂ _ _ _ a.oa x (Λ.ex0 z) (Λ.ex0 (Λ.A.actV x z)) := by
  intro _ _ E _ _ _ H inst D l c O _ β _ _ b a Λ
  refine ⟨GtAnModel.isAdd Λ, GtAnModel.analyticTorusPoint_surjective Λ, ?_⟩
  obtain rfl : inst = H.starRing := Λ.star_eq
  exact GtAnModel.gtAct Λ

end GlobalTheory.ArcPts
end
