module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
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
import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BC

theorem bcSp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def bcPm {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) : Gx (spMap ψ ≫ x) ⟶ Gx x :=
  pullback.lift (pullback.fst (Over.mk (spMap ψ ≫ x)).hom Xo.univ.t.G.hom ≫ spMap ψ)
    (pullback.snd (Over.mk (spMap ψ ≫ x)).hom Xo.univ.t.G.hom)
    (by rw [Category.assoc]; exact pullback.condition)

theorem bcPm_snd {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
  rw [Over.snd_left, Over.snd_left]
  exact pullback.lift_snd _ _ _

theorem bcPm_fst {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left ≫ spMap ψ := by
  rw [Over.fst_left, Over.fst_left]
  exact pullback.lift_fst _ _ _

theorem bcOver {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    {x : Sp S ⟶ Xo.X} (h : x ≫ Xo.s = sOf c S) : (spMap ψ.toRingHom ≫ x) ≫ Xo.s = sOf c T := by
  rw [Category.assoc, h]
  unfold sOf
  rw [bcSp]
  congr 1
  ext a
  simp



end BC

section Loc

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

end Loc

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

section Fin

variable (d : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))

def DivFin : Prop := ∀ (Z : Comp Xo c) (r : Om Z), r ≠ 0 → {v | d.admitted Z v ∧ v r ≠ 0}.Finite

def FrShFin (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) : Prop :=
  ∀ Z : Comp Xo c, {v | d.admitted Z v ∧ δ Z v ≠ 0}.Finite

theorem lawA3'_of (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (hord : ∀ Z v, d.ord Z v = ordC (δ Z v) v) (hD : DivFin d) (hF : FrShFin d δ) : LawA3' d := by
  intro Z G f hf hf0
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hf
  have ha : a ≠ 0 := by
    rintro rfl
    exact hf0 (zero_smul _ _)
  have hcoeff : (a • (AddMonoidAlgebra.single G (1 : Om Z))).coeff G = a := by
    first
      | simp
      | simp [AddMonoidAlgebra.smul_single']
      | (rw [AddMonoidAlgebra.smul_single', mul_one]; rfl)
  refine ((hD Z a ha).union (hF Z)).subset ?_
  rintro v ⟨hadm, hne⟩
  rw [hord] at hne
  unfold ordC at hne
  rw [hcoeff] at hne
  by_cases hv : v a = 0
  · refine Or.inr ⟨hadm, fun hδ => hne ?_⟩
    rw [hv, hδ]
    have hz : frW (0 : Ix Dw → ℤ) G = 0 := by
      unfold frW
      simp
    rw [hz]
    rfl
  · exact Or.inl ⟨hadm, hv⟩

end Fin

section Data

variable (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

theorem lawA3'_dataOf
    (hD : DivFin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR
      etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (hF : FrShFin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR
      etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) δ) :
    LawA3' (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR
      etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) :=
  lawA3'_of _ δ (fun _ _ => rfl) hD hF

end Data

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open MeasureTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

section Gen

variable (d : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))

def A13ContinuousOffNull : Prop :=
  ∀ Z (sg : c.F →+* ℂ) {G : WTZ E} {f : AC Z}, f ∈ AG Z G → f ≠ 0 →
    ∃ S : Set (Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1),
      MeasurableSet S ∧ d.sphMeasure S = 0 ∧
      ContinuousOn (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 =>
        ∑ᶠ P ∈ d.ST Z sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j),
          Real.log (d.nrm Z G f P)) Sᶜ

theorem lawA13_of_continuous (hc : A13ContinuousOffNull d) : A13Measurable d := by
  intro Z sg G f hf hf0
  obtain ⟨S, hSm, hS0, hcont⟩ := hc Z sg hf hf0
  have h1 := hcont.aemeasurable (μ := d.sphMeasure) hSm.compl
  have h2 : d.sphMeasure.restrict Sᶜ = d.sphMeasure :=
    Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.2 hS0)
  rw [h2] at h1
  exact h1

end Gen

def NrmContOff (h : GenFrEx Xo c) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N : ℕ) (uL : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1)) : Prop :=
  ∀ Z (sg : c.F →+* ℂ) {G : WTZ E} {f : AC Z}, f ∈ AG Z G → f ≠ 0 →
    ∃ S : Set (Fin Dd → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1),
      MeasurableSet S ∧
      Measure.pi (fun _ => (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere) S = 0 ∧
      ContinuousOn (fun t : Fin Dd → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1 =>
        ∑ᶠ P ∈ {P : Om Z →+* ℂ | P ∈ PT sg ∧ ∀ i, ∑ j, (t i : EuclideanSpace ℂ (Fin (N + 1))) j *
            P (ratio (Ω := Om Z) (valG h uL (wR j) Z) (valG h uL (wR (jc Z)) Z)) = 0},
          Real.log (nrmC fn (yP Z) G f P)) Sᶜ

theorem lawA13_of_data (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    (hc : NrmContOff h fn yP Dd N uL wR jc) :
    A13Measurable (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR
      etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) :=
  lawA13_of_continuous _ hc

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj.PointsOfFlagModel

open AlgebraicGeometry CategoryTheory Limits MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

inductive MdlC : Type
  | xm : MdlC
  | yy : MdlC
  | xn : ℕ → MdlC

section PtC

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure PtC {p : ℕ} (Y : Model Xo c β) (C : SCF p) where
  alg : O →+* intO ↥C.S
  fK : c.F →+* ↥C.S
  compat : (intO ↥C.S).subtype.comp alg = fK.comp β
  y : Sp ↥C.S ⟶ Xo.XF c
  y_over : y ≫ pullback.snd _ _ = spMap fK
  yt : Sp ↥(intO ↥C.S) ⟶ Y.X
  yt_over : yt ≫ Y.s = spMap alg
  ext : spMap (intO ↥C.S).subtype ≫ yt = y ≫ Y.j

namespace PtC

variable {p : ℕ} {Y : Model Xo c β} {C : SCF p} (P : PtC Y C)

def x0 : Sp ↥C.S ⟶ Y.X := P.y ≫ Y.j

abbrev base : Over Y.X := Over.mk P.x0

abbrev epsB : Over Y.X := Over.mk (spMap (algebraMap ↥C.S (DualNumber ↥C.S)) ≫ P.x0)

def IsTan (v : P.epsB ⟶ Y.t.G) : Prop :=
  spMap (TrivSqZeroExt.fstHom ↥C.S ↥C.S ↥C.S).toRingHom ≫ v.left = (1 : P.base ⟶ Y.t.G).left

def emb (τ : E →+* ℂ) (a : 𝓞 E) : ↥C.S := P.fK ⟨τ (a : E), c.conj τ a⟩

def IsEig (τ : E →+* ℂ) (v : P.epsB ⟶ Y.t.G) : Prop :=
  ∀ a : 𝓞 E, (v ≫ Y.t.act.act a).left = spMap (epsMul (P.emb τ a)) ≫ v.left

def IsComb {m : ℕ} (v : Fin m → (P.epsB ⟶ Y.t.G)) (a : Fin m → ↥C.S) (w : P.epsB ⟶ Y.t.G) : Prop :=
  ∃ u : Fin m → (P.epsB ⟶ Y.t.G), (∀ i, (u i).left = spMap (epsMul (a i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod

structure Flag where
  u : ∀ τ : E →+* ℂ, Fin (D.mult τ) → (P.epsB ⟶ Y.t.G)
  tan : ∀ τ i, P.IsTan (u τ i)
  eig : ∀ τ i, P.IsEig τ (u τ i)
  basis : ∀ τ (w : P.epsB ⟶ Y.t.G), P.IsTan w → P.IsEig τ w →
    ∃! a : Fin (D.mult τ) → ↥C.S, P.IsComb (u τ) a w

end PtC

end PtC

section Tower

variable {D : Datum H} {l : Level H}

abbrev abelian₂ (p : ℕ) (c : Coeff l) : Type :=
  {v : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) // (p : 𝓞 c.F) ∈ v.asIdeal}

def BaseAt {c : Coeff l} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F)) {O : Type} [CommRing O] (β : O →+* c.F) :
    Prop :=
  Function.Injective β ∧ ∀ x : c.F, x ∈ Set.range β ↔ v.valuation c.F x ≤ 1

structure Tower (p : ℕ) (Xo : Moduli D l) (c : Coeff l) where
  O : abelian₂ p c → Type
  [ring : ∀ v, CommRing (O v)]
  β : ∀ v, O v →+* c.F
  Y : ∀ v, Model Xo c (β v)
  lvN : ℕ → Level H
  XoN : ∀ n, Moduli D (lvN n)
  cN : ∀ n, Coeff (lvN n)
  ON : ∀ n, abelian₂ p (cN n) → Type
  [ringN : ∀ n w, CommRing (ON n w)]
  βN : ∀ n w, ON n w →+* (cN n).F
  YN : ∀ n w, Model (XoN n) (cN n) (βN n w)

attribute [instance] Tower.ring Tower.ringN

def TowerAt {p : ℕ} {Xo : Moduli D l} {c : Coeff l} (T : Tower p Xo c) : Prop :=
  (∀ v, BaseAt v.1 (T.β v) ∧ Nonempty (T.Y v).X) ∧
  ∀ n, l.Dvd (T.lvN n) ∧ p ^ n * l.A ∣ (T.lvN n).A ∧
    ∀ w, (BaseAt w.1 (T.βN n w) ∧ Nonempty (T.YN n w).X) ∧
      ∃ (v : abelian₂ p c) (bm : T.O v →+* T.ON n w) (π : (T.YN n w).X ⟶ (T.Y v).X), IsTransition (T.Y v) (T.YN n w) bm π

end Tower

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

def Pt {p : ℕ} (T : Tower p Xo c) : MdlC → Type
  | .xm => Σ v : abelian₂ p c, Σ C : SCF p, PtC (T.Y v) C
  | .yy => Σ v : abelian₂ p c, Σ C : SCF p, Σ P : PtC (T.Y v) C, P.Flag
  | .xn n => Σ w : abelian₂ p (T.cN n), Σ C : SCF p, PtC (T.YN n w) C

def fld {p : ℕ} {T : Tower p Xo c} : ∀ {Z : MdlC}, Pt T Z → Formalism.MainNotions.ModuliIntegralCharts.CF p
  | .xm, y => y.2.1.toCF
  | .yy, y => y.2.1.toCF
  | .xn _, y => y.2.1.toCF

end Formalism.L2.Pj.PointsOfFlagModel
end
end
