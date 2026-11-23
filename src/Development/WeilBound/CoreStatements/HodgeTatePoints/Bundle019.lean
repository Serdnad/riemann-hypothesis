module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.CbBase
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivHopf
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
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
public import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects

@[expose] public section

section

noncomputable section

namespace PositivityTheory.HtPt.Cb

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open ReciprocityTheory.ChartRestriction.G.TB

section

variable {R : Type} [CommRing R] {d n : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
variable {x y z w : Pt R n d}

theorem first_form_zero_left (hy : Z y) (hz : Z z) : ev ![0, y, z] B.ph1 = 1 := by
  have hb : ZZ ![y, z] := ZZ_cons hy (ZZ_cons hz ZZ_nil)
  have h := congrArg (ev ![y, z]) B.cocycleLeft_zero_fst
  rw [ev3 hb Z_zero (Z_pt _) (Z_pt _), ep_zero hb, ev_one] at h
  simpa [ep_pt hb] using h

theorem first_form_zero_right (hy : Z y) (hz : Z z) : ev ![y, z, 0] B.ph1 = 1 := by
  have hb : ZZ ![y, z] := ZZ_cons hy (ZZ_cons hz ZZ_nil)
  have h := congrArg (ev ![y, z]) B.cocycleLeft_zero_thd
  rw [ev3 hb (Z_pt _) (Z_pt _) Z_zero, ep_zero hb, ev_one] at h
  simpa [ep_pt hb] using h

theorem first_form_comm_at (hx : Z x) (hy : Z y) (hz : Z z) : ev ![x, y, z] B.ph1 = ev ![y, x, z] B.ph1 := by
  have hb : ZZ ![x, y, z] := ZZ_cons hx (ZZ_cons hy (ZZ_cons hz ZZ_nil))
  have h := congrArg (ev ![x, y, z]) B.cocycleLeft_comm
  rw [ev3 hb (Z_pt _) (Z_pt _) (Z_pt _)] at h
  simp only [ep_pt hb] at h
  simpa using h.symm

theorem first_form_assoc_at (hx : Z x) (hy : Z y) (hw : Z w) (hz : Z z) :
    ev ![x, y, z] B.ph1 * ev ![B.G.add x y, w, z] B.ph1 = ev ![y, w, z] B.ph1 * ev ![x, B.G.add y w, z] B.ph1 := by
  have hb : ZZ ![x, y, w, z] := ZZ_cons hx (ZZ_cons hy (ZZ_cons hw (ZZ_cons hz ZZ_nil)))
  have h := congrArg (ev ![x, y, w, z]) B.cocycleLeft_assoc
  simp only [evm hb] at h
  rw [ev3 hb (Z_pt _) (Z_pt _) (Z_pt _), ev3 hb (Z_add _ (Z_pt _) (Z_pt _)) (Z_pt _) (Z_pt _),
    ev3 hb (Z_pt _) (Z_pt _) (Z_pt _), ev3 hb (Z_pt _) (Z_add _ (Z_pt _) (Z_pt _)) (Z_pt _),
    ep_add _ hb (Z_pt _) (Z_pt _), ep_add _ hb (Z_pt _) (Z_pt _)] at h
  simp only [ep_pt hb] at h
  simpa using h

private theorem fgLaw_add_comm (G : FGLaw R d) (hx : Z x) (hy : Z y) : G.add x y = G.add y x := by
  have hb : ZZ ![x, y] := ZZ_cons hx (ZZ_cons hy ZZ_nil)
  have e : G.add (pt R d 1) (pt R d 0) = (G.add (pt R d 0) (pt R d 1) : Pt R 2 d) := by
    funext i
    exact (G.comm i).trans (eval_points_two _).symm
  have h := congrArg (ep ![x, y]) e
  rw [ep_add G hb (Z_pt _) (Z_pt _), ep_add G hb (Z_pt _) (Z_pt _)] at h
  simpa [ep_pt hb] using h.symm

private theorem fgLaw_add_assoc (G : FGLaw R d) (hx : Z x) (hy : Z y) (hz : Z z) :
    G.add (G.add x y) z = G.add x (G.add y z) := by
  have hb : ZZ ![x, y, z] := ZZ_cons hx (ZZ_cons hy (ZZ_cons hz ZZ_nil))
  have e : G.add (G.add (pt R d 0) (pt R d 1)) (pt R d 2) =
      (G.add (pt R d 0) (G.add (pt R d 1) (pt R d 2)) : Pt R 3 d) := by
    funext i
    exact G.assoc i
  have h := congrArg (ep ![x, y, z]) e
  rw [ep_add G hb (Z_add _ (Z_pt _) (Z_pt _)) (Z_pt _), ep_add G hb (Z_pt _) (Z_pt _),
    ep_add G hb (Z_pt _) (Z_add _ (Z_pt _) (Z_pt _)), ep_add G hb (Z_pt _) (Z_pt _)] at h
  simpa [ep_pt hb] using h

theorem first_form_four_term {a b c e : Pt R n d} (ha : Z a) (hb : Z b) (hc : Z c) (he : Z e) (hz : Z z) :
    ev ![a, b, z] B.ph1 * ev ![c, e, z] B.ph1 * ev ![B.G.add a b, B.G.add c e, z] B.ph1 =
      ev ![a, c, z] B.ph1 * ev ![b, e, z] B.ph1 * ev ![B.G.add a c, B.G.add b e, z] B.ph1 := by
  have A1 := first_form_assoc_at B (Z_add B.G ha hb) hc he hz
  have A2 := first_form_assoc_at B ha hb hc hz
  have A3 := first_form_assoc_at B (Z_add B.G ha hc) hb he hz
  have A4 := first_form_assoc_at B ha hc hb hz
  have e1 : B.G.add c b = B.G.add b c := fgLaw_add_comm B.G hc hb
  have e2 : B.G.add (B.G.add a c) b = B.G.add (B.G.add a b) c := by
    rw [fgLaw_add_assoc B.G ha hc hb, e1, ← fgLaw_add_assoc B.G ha hb hc]
  rw [e1, first_form_comm_at B hc hb hz] at A4
  rw [e2] at A3
  linear_combination ev ![B.G.add (B.G.add a b) c, e, z] B.ph1 * A2 -
    ev ![B.G.add (B.G.add a b) c, e, z] B.ph1 * A4 - ev ![a, b, z] B.ph1 * A1 + ev ![a, c, z] B.ph1 * A3

theorem first_power_eq_prod_at (hx : Z x) (hz : Z z) (k : ℕ) :
    ev ![x, z] (pow1 B k) = ∏ j ∈ Finset.range k, ev ![comp1 (B.A.act (j : O)) x, x, z] B.ph1 := by
  rw [pow1]
  have hb : ZZ ![x, z] := ZZ_cons hx (ZZ_cons hz ZZ_nil)
  rw [evprod hb]
  apply Finset.prod_congr rfl
  intro j _
  rw [ev3 hb (Z_comp1 (Z_act _ _) (Z_pt _)) (Z_pt _) (Z_pt _),
    ep_comp1 _ hb (Z_pt _), ep_pt hb, ep_pt hb]
  rfl

private theorem comp1_act_natCast_zero (hx : Z x) : comp1 (B.A.act ((0 : ℕ) : O)) x = 0 := by
  rw [Nat.cast_zero, act_zero]
  funext i
  exact evz (ZZ_cons hx ZZ_nil)

private theorem comp1_act_natCast_succ (hx : Z x) (k : ℕ) :
    comp1 (B.A.act ((k + 1 : ℕ) : O)) x = B.G.add (comp1 (B.A.act (k : O)) x) x := by
  rw [Nat.cast_succ, PositivityTheory.HtPt.Cb.add_act B.A _ _ hx, B.A.one_act]
  congr 1
  exact ep_pt (ZZ_cons hx ZZ_nil) 0

private theorem ev_pow1_succ (hx : Z x) (hz : Z z) (k : ℕ) :
    ev ![x, z] (pow1 B (k + 1)) = ev ![x, z] (pow1 B k) * ev ![comp1 (B.A.act (k : O)) x, x, z] B.ph1 := by
  rw [first_power_eq_prod_at B hx hz, first_power_eq_prod_at B hx hz, Finset.prod_range_succ]

theorem first_power_add_at (hx : Z x) (hy : Z y) (hz : Z z) (k : ℕ) :
    ev ![B.G.add x y, z] (pow1 B k) * ev ![x, y, z] B.ph1 ^ k =
      ev ![x, z] (pow1 B k) * ev ![y, z] (pow1 B k) *
        ev ![comp1 (B.A.act (k : O)) x, comp1 (B.A.act (k : O)) y, z] B.ph1 := by
  induction k with
  | zero =>
    rw [first_power_eq_prod_at B (Z_add B.G hx hy) hz, first_power_eq_prod_at B hx hz, first_power_eq_prod_at B hy hz, Finset.prod_range_zero,
      comp1_act_natCast_zero B hx, comp1_act_natCast_zero B hy, first_form_zero_left B Z_zero hz]
    simp
  | succ k ih =>
    have hkx : Z (comp1 (B.A.act (k : O)) x) := Z_comp1 (Z_act _ _) hx
    have hky : Z (comp1 (B.A.act (k : O)) y) := Z_comp1 (Z_act _ _) hy
    have h4 := first_form_four_term B hkx hky hx hy hz
    rw [ev_pow1_succ B (Z_add B.G hx hy) hz, ev_pow1_succ B hx hz, ev_pow1_succ B hy hz,
      comp1_act_natCast_succ B hx, comp1_act_natCast_succ B hy, act_add B.A _ hx hy]
    linear_combination ev ![x, y, z] B.ph1 *
        ev ![B.G.add (comp1 (B.A.act (k : O)) x) (comp1 (B.A.act (k : O)) y), B.G.add x y, z] B.ph1 * ih +
      ev ![x, z] (pow1 B k) * ev ![y, z] (pow1 B k) * h4

theorem adjoint_law_first_at (a : O) (hx : Z x) (hy : Z y) (hz : Z z) :
    ev ![comp1 (B.A.act a) x, comp1 (B.A.act a) y, z] B.ph1 * ev ![B.G.add x y, z] (B.ad a) =
      ev ![x, z] (B.ad a) * ev ![y, z] (B.ad a) * ev ![x, y, comp1 (B.A.act (star a)) z] B.ph1 := by
  have hb : ZZ ![x, y, z] := ZZ_cons hx (ZZ_cons hy (ZZ_cons hz ZZ_nil))
  have h := congrArg (ev ![x, y, z]) (B.adjoint_compat_left a)
  simp only [evm hb] at h
  rw [ev3 hb (Z_comp1 (Z_act _ _) (Z_pt _)) (Z_comp1 (Z_act _ _) (Z_pt _)) (Z_pt _),
    ev2 hb (Z_add _ (Z_pt _) (Z_pt _)) (Z_pt _), ev2 hb (Z_pt _) (Z_pt _), ev2 hb (Z_pt _) (Z_pt _),
    ev3 hb (Z_pt _) (Z_pt _) (Z_comp1 (Z_act _ _) (Z_pt _)),
    ep_comp1 _ hb (Z_pt _), ep_comp1 _ hb (Z_pt _), ep_comp1 _ hb (Z_pt _),
    ep_add _ hb (Z_pt _) (Z_pt _)] at h
  simp only [ep_pt hb] at h
  simpa using h

theorem ad_zero_left (a : O) (hz : Z z) : ev ![0, z] (B.ad a) = 1 := by
  have hb : ZZ ![z] := ZZ_cons hz ZZ_nil
  have h := congrArg (ev ![z]) (B.adjoint_zero_fst a)
  rw [ev2 hb Z_zero (Z_pt _), ep_zero hb, ev_one] at h
  simpa [ep_pt hb] using h

theorem first_power_adjoint_at (a : O) (hx : Z x) (hz : Z z) (k : ℕ) :
    ev ![comp1 (B.A.act a) x, z] (pow1 B k) * ev ![comp1 (B.A.act (k : O)) x, z] (B.ad a) =
      ev ![x, z] (B.ad a) ^ k * ev ![x, comp1 (B.A.act (star a)) z] (pow1 B k) := by
  induction k with
  | zero =>
    rw [first_power_eq_prod_at B (Z_comp1 (Z_act _ _) hx) hz, first_power_eq_prod_at B hx (Z_comp1 (Z_act _ _) hz), Finset.prod_range_zero,
      Finset.prod_range_zero, comp1_act_natCast_zero B hx, ad_zero_left B a hz]
    simp
  | succ k ih =>
    have hkx : Z (comp1 (B.A.act (k : O)) x) := Z_comp1 (Z_act _ _) hx
    have law := adjoint_law_first_at B a hkx hx hz
    rw [ev_pow1_succ B (Z_comp1 (Z_act _ _) hx) hz, ev_pow1_succ B hx (Z_comp1 (Z_act _ _) hz),
      comp1_act_natCast_succ B hx, act_comm B.A (k : O) a hx]
    linear_combination ev ![comp1 (B.A.act a) x, z] (pow1 B k) * law +
      ev ![x, z] (B.ad a) * ev ![comp1 (B.A.act (k : O)) x, x, comp1 (B.A.act (star a)) z] B.ph1 * ih

theorem first_power_zero_left (hz : Z z) (k : ℕ) : ev ![0, z] (pow1 B k) = 1 := by
  rw [first_power_eq_prod_at B Z_zero hz]
  apply Finset.prod_eq_one
  intro j _
  rw [germComp1_zero_of_noConstantCoeff (Z_act _ _)]
  exact first_form_zero_left B Z_zero hz

theorem first_power_zero_right (hx : Z x) (k : ℕ) : ev ![x, 0] (pow1 B k) = 1 := by
  rw [first_power_eq_prod_at B hx Z_zero]
  exact Finset.prod_eq_one fun j _ => first_form_zero_right B (Z_comp1 (Z_act _ _) hx) hx

end

theorem first_power_add : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (n : ℕ), ev (n := 3) ![B.G.add (pt R d 0) (pt R d 1), pt R d 2] (pow1 B n) * B.ph1 ^ n = ev (n := 3) ![pt R d 0, pt R d 2] (pow1 B n) * ev (n := 3) ![pt R d 1, pt R d 2] (pow1 B n) * ev (n := 3) ![comp1 (B.A.act (n : O)) (pt R d 0), comp1 (B.A.act (n : O)) (pt R d 1), pt R d 2] B.ph1 := by
  intro R _ d O _ _ B n
  have h := first_power_add_at B (Z_pt (n := 3) 0) (Z_pt 1) (Z_pt 2) n
  rwa [eval_points_three] at h

theorem first_power_adjoint : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (a : O) (n : ℕ), ev (n := 2) ![comp1 (B.A.act a) (pt R d 0), pt R d 1] (pow1 B n) * ev (n := 2) ![comp1 (B.A.act (n : O)) (pt R d 0), pt R d 1] (B.ad a) = B.ad a ^ n * ev (n := 2) ![pt R d 0, comp1 (B.A.act (star a)) (pt R d 1)] (pow1 B n) := by
  intro R _ d O _ _ B a n
  have h := first_power_adjoint_at B a (Z_pt (n := 2) 0) (Z_pt 1) n
  rwa [eval_points_two] at h

end PositivityTheory.HtPt.Cb
end
end

section

noncomputable section

namespace PositivityTheory.HtPt.Twpdiv

open TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT Coalgebra Bialgebra

section Lev

variable {La : Type} [AddCommGroup La] (p : ℕ)

theorem lev_surjective (n : ℕ) : Function.Surjective (lev (La := La) p n) := fun t =>
  Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)

theorem lev_eq_iff (n : ℕ) (a a' : La) : lev p n a = lev p n a' ↔ ∃ b : La, a - a' = (p ^ n) • b := by
  rw [lev, lev, Multiplicative.ofAdd.apply_eq_iff_eq, Submodule.Quotient.eq]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩

theorem lev_add (n : ℕ) (a a' : La) : lev p n (a + a') = lev p n a * lev p n a' := rfl

theorem lev_zero (n : ℕ) : lev p n (0 : La) = 1 := rfl

theorem lev_nsmul (n k : ℕ) (a : La) : lev p n (k • a) = lev p n a ^ k := by
  induction k with
  | zero => simp [lev_zero]
  | succ k ih => rw [succ_nsmul, lev_add, ih, pow_succ]

theorem lev_pow (n : ℕ) (t : LevGrp La p n) : t ^ p ^ n = 1 := by
  obtain ⟨a, rfl⟩ := lev_surjective p n t
  rw [← lev_nsmul, ← lev_zero, lev_eq_iff]
  exact ⟨a, sub_zero _⟩

def incl (n : ℕ) : LevGrp La p n →* LevGrp La p (n + 1) :=
  AddMonoidHom.toMultiplicative (Submodule.mapQ _ _ (p • (LinearMap.id : La →ₗ[ℤ] La)) (by
    rintro _ ⟨b, rfl⟩
    exact ⟨b, by simp only [LinearMap.smul_apply, LinearMap.id_apply, pow_succ', mul_smul]⟩)).toAddMonoidHom

theorem incl_lev (n : ℕ) (a : La) : incl p n (lev p n a) = lev p (n + 1) (p • a) := rfl

theorem card_lev [Module.Free ℤ La] [Module.Finite ℤ La] (n : ℕ) :
    Nat.card (LevGrp La p n) = p ^ (n * Module.finrank ℤ La) := by
  rw [pow_mul, ← AddSubgroup.index_range_nsmul]
  have : (nsmulAddMonoidHom (α := La) (p ^ n)).range =
      (LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))).toAddSubgroup := by
    ext x; exact Iff.rfl
  rw [this]
  rfl

instance [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] (n : ℕ) : Finite (LevGrp La p n) :=
  Nat.finite_of_card_ne_zero (by rw [card_lev]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

end Lev

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {La : Type} [AddCommGroup La] [Module.Free ℤ La]
  [Module.Finite ℤ La] {L : Type} [AddCommGroup L] [Module O L] (X : OrdTower p O La L)

def resT (n : ℕ) : Ord (X.hopf (n + 1)) →ₐc[O] Ord (X.hopf n) :=
  Ord.comap (X.hopf n) (X.hopf (n + 1)) (incl p n) fun f hf => (X.res_iff n _).2 ⟨f, hf, fun _ => rfl⟩

theorem ev_resT (n : ℕ) (t : LevGrp La p n) (f : Ord (X.hopf (n + 1))) :
    Ord.ev _ t (resT X n f) = Ord.ev _ (incl p n t) f := Ord.ev_comap _ _ _ _ t f

theorem resT_surjective (n : ℕ) : Function.Surjective (resT X n) := fun g => by
  obtain ⟨f, hf, h⟩ := (X.res_iff n _).1 (Ord.equiv _ g).2
  refine ⟨(Ord.equiv _).symm ⟨f, hf⟩, Ord.sep _ _ _ fun t => ?_⟩
  obtain ⟨a, rfl⟩ := lev_surjective p n t
  rw [ev_resT]
  exact (h a).symm

theorem ker_resT (n : ℕ) :
    RingHom.ker (resT X n) = torsionIdeal (R := O) (A := Ord (X.hopf (n + 1))) (p ^ n) := by
  apply le_antisymm
  · intro f hf
    have hf' : resT X n f = 0 := hf
    have h1 := X.ker_res n (Ord.equiv _ f) fun a => by
      have := ev_resT X n (lev p n a) f
      rw [hf', map_zero] at this
      exact this.symm
    have h2 : Ideal.span {g : X.A (n + 1) | ∃ h ∈ X.A (n + 1), ∀ t, g.1 t = h (t ^ p ^ n) - h 1} ≤
        (torsionIdeal (R := O) (A := Ord (X.hopf (n + 1))) (p ^ n)).comap
          (Ord.equiv (X.hopf (n + 1))).symm := by
      rw [Ideal.span_le]
      rintro g ⟨u, hu, hg⟩
      let u' := (Ord.equiv (X.hopf (n + 1))).symm ⟨u, hu⟩
      have h3 : (Ord.equiv (X.hopf (n + 1))).symm g =
          mulBy (R := O) (A := Ord (X.hopf (n + 1))) (p ^ n)
            (u' - algebraMap O _ (counit u')) := Ord.sep _ _ _ fun t => by
        rw [Ord.ev_mulBy, map_sub, AlgHom.commutes, Ord.counit_eq]
        exact hg t
      change (Ord.equiv (X.hopf (n + 1))).symm g ∈ torsionIdeal (R := O) (A := Ord (X.hopf (n + 1))) (p ^ n)
      rw [h3]
      have hu' : u' - algebraMap O _ (counit u') ∈ augIdeal (R := O) (A := Ord (X.hopf (n + 1))) := by
        change counit (R := O) (u' - algebraMap O _ (counit (R := O) u')) = 0
        rw [map_sub, counit_algebraMap, sub_self]
      unfold torsionIdeal kerIdeal
      exact Ideal.mem_map_of_mem (mulBy (R := O) (A := Ord (X.hopf (n + 1))) (p ^ n)).toAlgHom hu'
    exact h2 h1
  · refine (kerIdeal_le_ker_iff _ (resT X n : Ord (X.hopf (n + 1)) →ₐ[O] Ord (X.hopf n))).2 fun c =>
      Ord.sep _ _ _ fun t => ?_
    rw [AlgHom.commutes]
    change Ord.ev _ t (resT X n _) = _
    rw [ev_resT, Ord.ev_mulBy, ← map_pow, lev_pow, map_one, Ord.counit_eq]
    rfl

variable [IsDomain O] [IsLocalRing O]

def grp : PDivGroup p O where
  height := Module.finrank ℤ La
  A n := Ord (X.hopf n)
  rank_eq n q := by rw [Ord.rankAtStalk_eq, card_lev]
  res := resT X
  res_surjective := resT_surjective X
  ker_res := ker_resT X

def tau : La →+ (grp X).Tate :=
  AddMonoidHom.mk' (fun a => ⟨fun n => Ord.ev (X.hopf n) (lev p n a), fun n => AlgHom.ext fun g => by
      obtain ⟨f, rfl⟩ := (grp X).res_surjective n g
      refine (congrArg (Ord.ev (X.hopf (n + 1)) (lev p (n + 1) a)) ((grp X).mulP_res n f)).trans ?_
      refine (Ord.ev_mulBy _ _ p f).trans ?_
      rw [← lev_nsmul]
      exact (ev_resT X n (lev p n a) f).symm⟩)
    fun a b => TateOver.ext_conv fun n => map_mul (Ord.evHom (X.hopf n)) (lev p n a) (lev p n b)

theorem realises : X.Realises (grp X) (fun n => Ord.equiv (X.hopf n)) (tau X) :=
  ⟨fun n f a => ev_resT X n (lev p n a) f, fun _ _ _ => rfl⟩

theorem exists_tate : ∃ j : ℤ_[p] ⊗[ℤ] La ≃ₗ[ℤ_[p]] (grp X).Tate, ∀ a, j (1 ⊗ₜ a) = tau X a :=
  tate_equiv (tau X)
    (fun n a a' => ((Ord.evHom_bijective (X.hopf n)).1.eq_iff (a := lev p n a) (b := lev p n a')).trans
      (lev_eq_iff p n a a'))
    fun n y => by
      obtain ⟨t, ht⟩ := (Ord.evHom_bijective (X.hopf n)).2 y
      obtain ⟨a, rfl⟩ := lev_surjective p n t
      exact ⟨a, ht⟩

end PositivityTheory.HtPt.Twpdiv

end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem PositivityTheory.HtPt.Twpdiv.tower_pdiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L), ∃ (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate), X.Realises G e τ ∧ G.height = Module.finrank ℤ La ∧ ∃ j : ℤ_[p] ⊗[ℤ] La ≃ₗ[ℤ_[p]] G.Tate, ∀ a, j (1 ⊗ₜ a) = τ a := by
  intro p _ C _ _ _ v O _ _ _ hv _ _ La _ _ _ L _ _ X
  have : ValuationRing O := ValuationRing.of_integers v hv
  exact ⟨PositivityTheory.HtPt.Twpdiv.grp X, _, _, PositivityTheory.HtPt.Twpdiv.realises X, rfl, PositivityTheory.HtPt.Twpdiv.exists_tate X⟩
end

section

noncomputable section

namespace PositivityTheory.HtPt.Hcptgen

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem aeval_scale {σ K R A : Type} [Fintype K] [CommRing R] [CommRing A] [Algebra R A] (w : σ → K → ℕ)
    (c : K → A) (z : σ → A) {f : MvPolynomial σ R} {d : K → ℕ} (hf : IsWeightedHomogeneous w f d) :
    aeval (fun p => (∏ k, c k ^ w p k) * z p) f = (∏ k, c k ^ d k) * aeval z f := by
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, mul_add]
  | monomial m r hm =>
    rw [aeval_monomial, aeval_monomial, ← hm]
    have e : (∏ k, c k ^ (Finsupp.weight w m) k) = m.prod fun p n => (∏ k, c k ^ w p k) ^ n := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow,
        ← pow_mul, mul_comm]
      exact Finset.prod_comm
    rw [e]
    simp only [mul_pow, Finsupp.prod_mul]
    ring

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K] {J : K → Type}

theorem ratio_eq [DecidableEq K] (y : (Σ k, J k) → Ω) (s : ∀ k, J k) (hs : mseg y s ≠ 0) (k : K) (i : J k) :
    y ⟨k, i⟩ / y ⟨k, s k⟩ = mseg y (Function.update s k i) / mseg y s := by
  have hk : y ⟨k, s k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)
  rw [div_eq_div_iff hk hs]
  unfold mseg
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
    Function.update_self]
  have e : ∏ j ∈ Finset.univ.erase k, y ⟨j, Function.update s k i j⟩ = ∏ j ∈ Finset.univ.erase k, y ⟨j, s j⟩ :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [e]
  ring


open GroundTheory.Heights₂.Heights.NumbersDVR in
theorem chartRing_mseg (y : (Σ k, J k) → Ω) (s : ∀ k, J k) (hs : mseg y s ≠ 0) :
    chartRing o (mseg y) s = Algebra.adjoin o (Set.range fun j => mseg y j / mseg y s) := by
  classical
  refine le_antisymm (fun u hu => ?_) (Algebra.adjoin_le ?_)
  · have hk : ∀ k, y ⟨k, s k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)
    obtain ⟨n, U, hU, hv⟩ := GenericProjClosureDivisor.chart_form (O := o) (Φ := Ω) y (Pi.basisFun Ω (Fin 0))
      (Fin.elim0 : Fin 0 → _) (Fin.elim0 : Fin 0 → _) Fin.elim0 s hs hu
    let c : Option (Option K) → Ω := fun b => b.elim 1 fun b' => b'.elim 1 fun k => y ⟨k, s k⟩
    let z : (Σ b, bundleIdx (bundleIdx J 0) 0 b) → Ω := fun p =>
      pairProjCoord y (Pi.basisFun Ω (Fin 0)) (Fin.elim0 : Fin 0 → _) (Fin.elim0 : Fin 0 → _) Fin.elim0 p / c p.1
    have hc : ∀ b, c b ≠ 0 := by
      rintro (_ | _ | k)
      · exact one_ne_zero
      · exact one_ne_zero
      · exact hk k
    have h := aeval_scale _ c z hU
    have e1 : (fun p => (∏ b, c b ^ blockWeight (bundleIdx (bundleIdx J 0) 0) p b) * z p) =
        pairProjCoord y (Pi.basisFun Ω (Fin 0)) (Fin.elim0 : Fin 0 → _) (Fin.elim0 : Fin 0 → _) Fin.elim0 := by
      funext p
      have : ∏ b, c b ^ blockWeight (bundleIdx (bundleIdx J 0) 0) p b = c p.1 := by
        rw [Finset.prod_eq_single p.1]
        · simp [blockWeight]
        · intro b _ hb
          simp [blockWeight, Pi.single_eq_of_ne hb]
        · simp
      rw [this]
      exact mul_div_cancel₀ _ (hc _)
    have e2 : ∏ b, c b ^ GenericProjClosureDivisor.vdeg (fun _ : K => n) b = segreVec y s ^ n := by
      simp [Fintype.prod_option, c, GenericProjClosureDivisor.vdeg, segreVec, Finset.prod_pow]
    rw [e1, e2, hv, Algebra.algebraMap_self_apply, mul_comm] at h
    have hu' : u = aeval z U := mul_left_cancel₀ (pow_ne_zero n hs) h
    have hz : aeval z U ∈ Algebra.adjoin o (Set.range z) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨U, rfl⟩
    rw [hu']
    refine Algebra.adjoin_mono ?_ hz
    rintro _ ⟨⟨_ | _ | k, i⟩, rfl⟩
    · exact Fin.elim0 i
    · exact Fin.elim0 i
    · exact ⟨Function.update s k i, (ratio_eq y s hs k i).symm⟩
  · rintro _ ⟨j, rfl⟩
    exact div_mem_chartRing _ _ _

end PositivityTheory.HtPt.Hcptgen
end
end
