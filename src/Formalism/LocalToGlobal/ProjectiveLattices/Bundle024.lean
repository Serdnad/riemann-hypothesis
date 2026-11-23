module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle817
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Formalism.SharpRestriction.Bundle001
public import Formalism.LocalRingCardinality.DataParams
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle002
public import Formalism.LocalRingCardinality.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.SetTheory.ZFC.PSet
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj.CompSplitPfB

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem cspB_over {S : Type} [CommRing S] [Algebra c.F S] {x : Sp S ⟶ Xo.X} (hx : x ≫ Xo.s = sOf c S) :
    x ≫ Xo.s = spMap (algebraMap c.F S) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
  rw [hx, sOf, ← Spec.map_comp]
  rfl

def cspB_lift {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    Sp S ⟶ Xo.XF c :=
  pullback.lift x (spMap (algebraMap c.F S)) (cspB_over hx)

theorem cspB_lift_fst {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    cspB_lift x hx ≫ pullback.fst _ _ = x := by
  unfold cspB_lift
  exact pullback.lift_fst _ _ _

theorem cspB_lift_snd {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    cspB_lift x hx ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by
  unfold cspB_lift
  exact pullback.lift_snd _ _ _

theorem cspB_lift_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {x : Sp S ⟶ Xo.X} (hx : x ≫ Xo.s = sOf c S) {z : Sp T ⟶ Xo.X} (hz : z ≫ Xo.s = sOf c T)
    (hzx : z = spMap φ.toRingHom ≫ x) : cspB_lift z hz = spMap φ.toRingHom ≫ cspB_lift x hx := by
  apply pullback.hom_ext
  · rw [cspB_lift_fst, Category.assoc, cspB_lift_fst, hzx]
  · rw [cspB_lift_snd, Category.assoc, cspB_lift_snd, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (AlgHom.comp_algebraMap φ).symm

theorem cspB_idem_eq_of {S : Type} [CommRing S] {a b : S} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : ∀ q : PrimeSpectrum S, a ∉ q.asIdeal ↔ b ∉ q.asIdeal) : a = b := by
  apply GlobalTheory.DimSplit.idem_eq_of <;> assumption

variable (C : Set (Xo.XF c)) (hC : IsClopen C)

def cspB_idem {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) : S :=
  ((PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).symm
    ⟨(cspB_lift x hx) ⁻¹' C, hC.preimage (cspB_lift x hx).continuous⟩).1

theorem cspB_idem_idem {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    IsIdempotentElem (cspB_idem C hC x hx) := by
  unfold cspB_idem
  exact ((PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).symm _).2

theorem cspB_idem_spec {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S)
    (q : PrimeSpectrum S) : cspB_idem C hC x hx ∉ q.asIdeal ↔ cspB_lift x hx q ∈ C := by
  have h1 := (PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).apply_symm_apply
    ⟨(cspB_lift x hx) ⁻¹' C, hC.preimage (cspB_lift x hx).continuous⟩
  have h2 : q ∈ ((((PrimeSpectrum.isIdempotentElemEquivClopens (R := S))
      ((PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).symm
        ⟨(cspB_lift x hx) ⁻¹' C, hC.preimage (cspB_lift x hx).continuous⟩)) :
          TopologicalSpace.Clopens (PrimeSpectrum S)) : Set (PrimeSpectrum S)) ↔
      q ∈ (cspB_lift x hx) ⁻¹' C := by
    rw [h1]
    rfl
  exact h2

theorem cspB_idem_congr {S : Type} [CommRing S] [Algebra c.F S] {x x' : Sp S ⟶ Xo.X}
    (hx : x ≫ Xo.s = sOf c S) (hx' : x' ≫ Xo.s = sOf c S) (h : x' = x) :
    cspB_idem C hC x' hx' = cspB_idem C hC x hx := by
  subst h
  rfl

theorem cspB_idem_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {x : Sp S ⟶ Xo.X} (hx : x ≫ Xo.s = sOf c S) {z : Sp T ⟶ Xo.X} (hz : z ≫ Xo.s = sOf c T)
    (hzx : z = spMap φ.toRingHom ≫ x) : φ (cspB_idem C hC x hx) = cspB_idem C hC z hz := by
  apply cspB_idem_eq_of ((cspB_idem_idem C hC x hx).map φ) (cspB_idem_idem C hC z hz)
  intro q
  rw [cspB_idem_spec C hC z hz q, cspB_lift_map φ hx hz hzx]
  exact cspB_idem_spec C hC x hx (PrimeSpectrum.comap φ.toRingHom q)


variable (Xo c) in
def cspB_rule : Rul Xo c := fun _ y => cspB_idem C hC y.x y.x_over

theorem cspB_rule_natural : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
    (cspB_rule Xo c C hC) := by
  intro p q φ y z hyz
  first
  | exact cspB_idem_map C hC φ y.x_over z.x_over hyz.1
  | exact (cspB_idem_map C hC φ y.x_over z.x_over hyz.1).symm

theorem cspB_rule_bor (p : TRing c.F) (t : Ix Dw → (p.R)ˣ) (y y' : FrPt Xo c p.R) (hb : FrBor t y y') :
    cspB_rule Xo c C hC p y' = cspB_rule Xo c C hC p y := by
  exact cspB_idem_congr C hC y.x_over y'.x_over hb.1

theorem cspB_evR {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (hy : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    evR Xo c (cspB_rule Xo c C hC) y = cspB_idem C hC y.x y.x_over := by
  unfold evR evalAt
  rw [dite_eq_left hy]
  first
  | exact cspB_idem_map C hC _ _ _ hy.choose_spec.choose_spec.choose_spec.1
  | exact cspB_idem_map C hC _ _ _ hy.choose_spec.choose_spec.choose_spec.1.1

theorem cspB_evR_zero {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (hy : ¬ FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) (f : Rul Xo c) :
    evR Xo c f y = 0 := by
  unfold evR evalAt
  rw [dite_eq_right hy]

theorem cspB_evR_mul {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (f g : Rul Xo c) :
    evR Xo c (f * g) y = evR Xo c f y * evR Xo c g y := by
  exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g y

theorem cspB_genPt_mem (Z : Comp Xo c) : genPt Z ∈ (Z : Set (Xo.XF c)) := by
  unfold genPt
  have hcl : IsClosed (Z : Set (Xo.XF c)) := isClosed_of_mem_irreducibleComponents _ Z.2
  have hS : IsIrreducible (Z : Set (Xo.XF c)) := Z.2.1
  have hg : IsGenericPoint hS.genericPoint (closure (Z : Set (Xo.XF c))) := by
    first
    | exact hS.isGenericPoint_genericPoint_closure
    | exact hS.genericPoint_spec
  rw [hcl.closure_eq] at hg
  exact hg.mem

theorem cspB_isClopen (hdisj : ∀ Z Z' : Comp Xo c, Z ≠ Z' → Disjoint (Z : Set (Xo.XF c)) Z')
    (Z : Comp Xo c) : IsClopen (Z : Set (Xo.XF c)) := by
  have := CompFin.finite_comp Xo c
  refine ⟨isClosed_of_mem_irreducibleComponents _ Z.2, ?_⟩
  have hU : (Z : Set (Xo.XF c)) = (⋃ Z' : {Z' : Comp Xo c // Z' ≠ Z}, (Z'.1 : Set (Xo.XF c)))ᶜ := by
    ext p
    constructor
    · intro hp hp'
      obtain ⟨⟨Z', hne⟩, hZ'⟩ := Set.mem_iUnion.1 hp'
      exact Set.disjoint_left.1 (hdisj Z Z' (Ne.symm hne)) hp hZ'
    · intro hp
      have hall : p ∈ ⋃₀ irreducibleComponents (Xo.XF c) := by
        rw [sUnion_irreducibleComponents]; trivial
      obtain ⟨W, hW, hpW⟩ := Set.mem_sUnion.1 hall
      by_contra hpZ
      refine hp (Set.mem_iUnion.2 ⟨⟨⟨W, hW⟩, fun hWZ => hpZ ?_⟩, hpW⟩)
      rw [← hWZ]
      exact hpW
  rw [hU]
  exact (isClosed_iUnion_of_finite fun Z' : {Z' : Comp Xo c // Z' ≠ Z} =>
    isClosed_of_mem_irreducibleComponents _ Z'.1.2).isOpen_compl



end Formalism.L2.Pj.CompSplitPfB
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def N3AtPoints (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C), Nonempty (DatAt Y P)

def BetaAdd (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C) (A : DatAt Y P) (a a' b : A.Ylat),
    A.beta (a + a') b = A.beta a b + A.beta a' b

def BetaBal (Y : Model Xo c β) (p : ℕ) (cj : E → E) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C) (A : DatAt Y P) (x x' : 𝓞 E), (x' : E) = cj (x : E) →
    ∀ a b : A.Ylat, A.beta (x • a) b = A.beta a (x' • b)

def BetaPosDef (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C) (A : DatAt Y P),
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ A.Ylat),
      ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * A.beta (b i) (b k)

namespace DatAt

variable {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

theorem beta_add_right (hA : BetaAdd Y p) (A : DatAt Y P) (a b b' : A.Ylat) :
    A.beta a (b + b') = A.beta a b + A.beta a b' := by
  rw [A.beta_symm, hA C P A, A.beta_symm b, A.beta_symm b']

def beLin (hA : BetaAdd Y p) (A : DatAt Y P) : A.Ylat →ₗ[ℤ] A.Ylat →ₗ[ℤ] ℝ :=
  (AddMonoidHom.mk' (fun a => (AddMonoidHom.mk' (fun b => A.beta a b)
      (fun b b' => A.beta_add_right hA a b b')).toIntLinearMap)
    (fun a a' => by
      ext b
      simp [hA C P A a a' b])).toIntLinearMap

theorem beLin_apply (hA : BetaAdd Y p) (A : DatAt Y P) (a b : A.Ylat) : A.beLin hA a b = A.beta a b := rfl

end DatAt

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.I2

variable {D : D7}

theorem hostSize_finrank (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]
  first
  | ring
  | rfl
  | omega
  | (simp only [Formalism.BasicNotions.Ranks.ord]; ring)

theorem hostSize_f (D : D7) : PT.f D.host.E = D.R.f := by
  simp only [ReciprocityTheory.ChartRestriction.G.I2.PT.f, hostSize_finrank D]
  omega

theorem hostSize_rd (D : D7) : PT.rd D.host.E = D.host.rdE := rfl

theorem hostSize_n_sqrt_le (D : D7) :
    Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
  (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1

theorem hostSize_sqrt_gt {large₂ : SizeData₂ D} (P : ParameterChoice' D large₂) :
    ((D.R.f : ℝ) + 6) ^ 2 < Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
  obtain ⟨hq, hd⟩ := D.host.qd_big
  have hf : D.R.f = 2 * D.R.ord := Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)
  have hfk := D.R.f_le_k
  have hm := D.R.two_le_m
  have hmf := D.R.m_le_f
  have ht := D.R.rank_add_five_le
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have h1 : D.R.f + 6 ≤ D.R.t := by omega
  have h2 : D.R.f + 6 ≤ 4 * D.R.r := by omega
  have key : (D.R.f + 6) ^ 2 < 4 * D.R.t * D.R.r + 1 := by
    have := Nat.mul_le_mul h1 h2
    nlinarith
  have keyR : ((D.R.f : ℝ) + 6) ^ 2 < ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) := by exact_mod_cast key
  have hA : (0 : ℝ) ≤ ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hqR : ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) < (D.host.q : ℝ) := by exact_mod_cast hq
  have hdR : ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) < (D.host.d : ℝ) := by exact_mod_cast hd
  have hsq : ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) < Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
    rw [Real.lt_sqrt hA]
    nlinarith
  linarith

theorem host_f_sq_le_rd {large₂ : SizeData₂ D} (P : ParameterChoice' D large₂) : (PT.f D.host.E : ℝ) ^ 2 ≤ PT.rd D.host.E := by
  have h1 := hostSize_sqrt_gt P
  have h2 := hostSize_n_sqrt_le D
  rw [hostSize_f D, hostSize_rd D]
  have h0 : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem host_rd_ge_sixteen {large₂ : SizeData₂ D} (P : ParameterChoice' D large₂) : 16 ≤ PT.rd D.host.E := by
  have h1 := hostSize_sqrt_gt P
  have h2 := hostSize_n_sqrt_le D
  rw [hostSize_rd D]
  have h0 : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem host_m_pow_four_le_f {large₂ : SizeData₂ D} (hS : SizesAt large₂) : D.R.m ^ 4 ≤ PT.f D.host.E := by
  have hx : 1 < large₂.sc.x := large₂.sc.one_lt_alt
  have hx0 : 0 < large₂.sc.x := by linarith
  have he : 0 < large₂.sc.eps := large₂.sc.eps_pos
  obtain ⟨⟨hN1, -⟩, ⟨-, hM2⟩, -⟩ := hS
  simp only [Formalism.MainNotions.szTh, Formalism.BasicNotions.Scale.delta1] at hN1 hM2
  have hA : Real.sqrt (large₂.sc.x * large₂.sc.x ^ (-(large₂.sc.eps / 8))) =
      large₂.sc.x ^ ((1 + -(large₂.sc.eps / 8)) * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_mul hx0.le, Real.rpow_add hx0, Real.rpow_one]
  rw [hA, ← Real.rpow_add hx0] at hM2
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have h4 : (D.R.m : ℝ) ^ 4 ≤ (large₂.sc.x ^ (large₂.sc.eps / 100 + (1 + -(large₂.sc.eps / 8)) * (1 / 2))) ^ 4 :=
    pow_le_pow_left₀ hm0 hM2 4
  have h5 : (large₂.sc.x ^ (large₂.sc.eps / 100 + (1 + -(large₂.sc.eps / 8)) * (1 / 2))) ^ 4 =
      large₂.sc.x ^ ((large₂.sc.eps / 100 + (1 + -(large₂.sc.eps / 8)) * (1 / 2)) * 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have h6 : large₂.sc.x ^ ((large₂.sc.eps / 100 + (1 + -(large₂.sc.eps / 8)) * (1 / 2)) * 4) ≤
      large₂.sc.x ^ (2 + 8 * large₂.sc.eps - large₂.sc.eps / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have key : ((D.R.m ^ 4 : ℕ) : ℝ) ≤ (D.R.n : ℝ) := by
    push_cast
    linarith
  have hmn : D.R.m ^ 4 ≤ D.R.n := by exact_mod_cast key
  have hn : D.R.n = D.R.ord := rfl
  rw [hostSize_f D, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]
  omega

end Formalism.L2.Pj
end
end
