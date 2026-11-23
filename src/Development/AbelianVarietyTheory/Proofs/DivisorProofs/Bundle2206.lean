module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.LatDiv

variable {p : ℕ} [Fact p.Prime]

def intAf (p : ℕ) : AddSubgroup (AfP p) where
  carrier := {a | IsIntAf a}
  zero_mem' := fun v => by simp
  add_mem' := fun ha hb v => by
    rw [map_add]
    exact add_mem (ha v) (hb v)
  neg_mem' := fun ha v => by rw [map_neg]; exact neg_mem (ha v)

def extF (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) : AfP p ⊗[ℚ] VQ D →ₗ[AfP p] AfP p :=
  LinearMap.liftBaseChange (AfP p)
    ((Algebra.linearMap ℚ (AfP p)) ∘ₗ LinearMap.liftBaseChange ℚ ((Algebra.linearMap ℤ ℚ) ∘ₗ f))

theorem extF_tmul (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) (a : AfP p) (x : D.La) :
    extF D f (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) = a * ((f x : ℤ) : AfP p) := by
  simp [extF, LinearMap.liftBaseChange_tmul, Algebra.smul_def]

theorem extF_mem (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) {w : AfP p ⊗[ℚ] VQ D} (hw : w ∈ LaHat D) :
    extF D f w ∈ intAf p := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    intro v
    rw [extF_tmul, map_mul, map_intCast]
    exact mul_mem (ha v) (intCast_mem _ _)
  | zero => simpa using (intAf p).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem int_dvd (D : Datum p) (f : D.La →ₗ[ℤ] ℤ) (x : D.La) (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p)
    (w : AfP p ⊗[ℚ] VQ D) (hw : w ∈ LaHat D) (h : inAf D x = n • w) : (n : ℤ) ∣ f x := by
  have hb := extF_mem D f hw
  have e : ((f x : ℤ) : AfP p) = (n : AfP p) * extF D f w := by
    have := congrArg (extF D f) h
    rw [inAf, extF_tmul, _root_.one_mul, _root_.map_nsmul, nsmul_eq_mul] at this
    exact this
  set q : ℚ := (f x : ℚ) / n with hq
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hval : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, v.valuation ℚ q ≤ 1 := by
    intro v
    by_cases hv : v.asIdeal = Ideal.span {(p : ℤ)}
    · have h1 : v.valuation ℚ (n : ℚ) = 1 := by
        have : (n : ℚ) = algebraMap ℤ ℚ (n : ℤ) := by simp
        rw [this, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff, hv, Ideal.mem_span_singleton]
        intro hd
        have : (p : ℤ) ∣ (n : ℤ) := hd
        have h2 : p ∣ n := by exact_mod_cast this
        have h3 : p ∣ Nat.gcd n p := Nat.dvd_gcd h2 dvd_rfl
        rw [hnp] at h3
        exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)
      have h2 : v.valuation ℚ ((f x : ℤ) : ℚ) ≤ 1 := by
        rw [← eq_intCast (algebraMap ℤ ℚ), IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact v.intValuation_le_one _
      rw [hq, map_div₀, h1, div_one]; exact h2
    · let v' : AwayP p := ⟨v, hv⟩
      have hbv := hb v'
      have e2 := congrArg (AfP.eval v') e
      rw [map_intCast, map_mul, map_natCast] at e2
      have hqv : algebraMap ℚ (v.adicCompletion ℚ) q = AfP.eval v' (extF D f w) := by
        have hn' : algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ) ≠ 0 := (map_ne_zero _).2 hn0
        have : algebraMap ℚ (v.adicCompletion ℚ) q * algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ) =
            ((f x : ℤ) : v.adicCompletion ℚ) := by
          rw [← map_mul, hq, div_mul_cancel₀ _ hn0, map_intCast]
        rw [← mul_left_inj' hn', this, e2, map_natCast]
        ring
      have hc : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) = v.valuation ℚ q :=
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q
      rw [← hc, hqv]
      exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hbv
  obtain ⟨k, hk⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q hval
  refine ⟨k, ?_⟩
  have : ((k : ℤ) : ℚ) = (f x : ℚ) / n := by rw [← eq_intCast (algebraMap ℤ ℚ)]; exact hk.trans hq
  have h4 : ((f x : ℤ) : ℚ) = ((n : ℤ) * k : ℤ) := by
    push_cast; rw [this]; field_simp
  exact_mod_cast h4

end GlobalTheory.LKGeo.LatDiv

namespace GlobalTheory.LKGeo.LatDiv

theorem eq_nsmul_of_inAf_eq_nsmul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (x : D.La) (n : ℕ), 0 < n → n.Coprime p →
    ∀ w ∈ LaHat D, inAf D x = n • w → ∃ z, x = n • z := by
  intro p _ D x n hn hnp w hw h
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  have hd : ∀ i, (n : ℤ) ∣ b.coord i x := fun i => int_dvd D (b.coord i) x n hn hnp w hw h
  choose c hc using hd
  refine ⟨∑ i, c i • b i, ?_⟩
  conv_lhs => rw [← b.sum_repr x]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : b.repr x i = (n : ℤ) * c i := hc i
  rw [this, mul_smul]
  exact Nat.cast_smul_eq_nsmul ℤ n _

end GlobalTheory.LKGeo.LatDiv
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo

variable {p : ℕ} [Fact p.Prime]

def actAf (D : Datum p) (c : D.O) : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  Module.End.baseChangeHom ℚ (AfP p) (VQ D) (actQ D c)

theorem actAf_tmul (D : Datum p) (c : D.O) (a : AfP p) (x : D.La) :
    actAf D c (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) = a ⊗ₜ ((1 : ℚ) ⊗ₜ (c • x)) := by
  show LinearMap.baseChange (AfP p) (actQ D c) (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) = _
  rw [LinearMap.baseChange_tmul, actQ, LinearMap.baseChange_tmul]
  rfl

theorem actAf_inAf (D : Datum p) (c : D.O) (x : D.La) : actAf D c (inAf D x) = inAf D (c • x) :=
  actAf_tmul D c 1 x

theorem actAf_mem_laHat (D : Datum p) (c : D.O) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    actAf D c v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    rw [actAf_tmul]
    exact AddSubgroup.subset_closure ⟨a, c • x, ha, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [map_add]; exact add_mem hu hw
  | neg u _ hu => rw [map_neg]; exact neg_mem hu

theorem actG_actAf {D : Datum p} {G : HTGroup p} (L : Link D G) (g : G.GAf) (c : D.O)
    (v : AfP p ⊗[ℚ] VQ D) : L.actG g (actAf D c v) = actAf D c (L.actG g v) := by
  have key : ∀ z : AfP p ⊗[ℚ] G.C, Commute (actOn L.rep (AfP p) z) (actAf D c) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
      have h1 : Commute (L.rep x) (actQ D c) := (L.rep_range (L.rep x)).1 ⟨x, rfl⟩ c
      simp only [actOn]
      refine Commute.mul_left ?_ ?_
      · exact Algebra.commute_algebraMap_left r _
      · exact h1.map (Module.End.baseChangeHom ℚ (AfP p) (VQ D))
    | add a b ha hb => rw [map_add (f := _)]; exact ha.add_left hb
  unfold Link.actG
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  exact LinearMap.congr_fun (key _).eq v

end GlobalTheory.LKGeo

namespace GlobalTheory.LKGeo

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.LKGeo
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo

variable {p : ℕ} [Fact p.Prime]

theorem isIntAf_zero : IsIntAf (0 : AfP p) := fun v => by rw [map_zero]; exact zero_mem _

theorem isIntAf_add {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

theorem isIntAf_neg {a : AfP p} (ha : IsIntAf a) : IsIntAf (-a) := fun v => by
  rw [map_neg]; exact neg_mem (ha v)

theorem isIntAf_zsmul_mul (n : ℤ) {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) :
    IsIntAf ((n : ℚ) • (a * b)) := fun v => by
  rw [Int.cast_smul_eq_zsmul, map_zsmul, map_mul]
  exact zsmul_mem (mul_mem (ha v) (hb v)) n

theorem formInt_gen (D : Datum p) (a a' : AfP p) (x y : D.La) (ha : IsIntAf a) (ha' : IsIntAf a') :
    IsIntAf ((D.EF.baseChange ℚ).baseChange (AfP p) (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) (a' ⊗ₜ ((1 : ℚ) ⊗ₜ y))) := by
  rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, _root_.mul_one, zsmul_eq_mul, _root_.mul_one]
  exact isIntAf_zsmul_mul _ ha ha'

theorem formInt_laHat : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (v w : AfP p ⊗[ℚ] VQ D), v ∈ LaHat D → w ∈ LaHat D →
    IsIntAf ((D.EF.baseChange ℚ).baseChange (AfP p) v w) := by
  intro p _ D v w hv hw
  set B := (D.EF.baseChange ℚ).baseChange (AfP p)

  have hgen : ∀ z ∈ {z | ∃ (a : AfP p) (x : D.La), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)},
      ∀ w ∈ LaHat D, IsIntAf (B z w) := by
    rintro z ⟨a, x, ha, rfl⟩ w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw' =>
      obtain ⟨a', y, ha', rfl⟩ := hw'
      exact formInt_gen D a a' x y ha ha'
    | zero => rw [map_zero]; exact isIntAf_zero
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add (f := _)]; exact isIntAf_add h₁ h₂
    | neg w _ h => rw [map_neg]; exact isIntAf_neg h
  induction hv using AddSubgroup.closure_induction with
  | mem z hz => exact hgen z hz w hw
  | zero => rw [map_zero, LinearMap.zero_apply]; exact isIntAf_zero
  | add v₁ v₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact isIntAf_add h₁ h₂
  | neg v _ h => rw [map_neg, LinearMap.neg_apply]; exact isIntAf_neg h

end GlobalTheory.LKGeo
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.MultScale

variable {p : ℕ} [Fact p.Prime]

def EFA (D : Datum p) : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  (D.EF.baseChange ℚ).baseChange (AfP p)

theorem EFA_tmul (D : Datum p) (a a' : AfP p) (x x' : D.La) :
    EFA D (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) (a' ⊗ₜ ((1 : ℚ) ⊗ₜ x')) = a * a' * ((D.EF x x' : ℤ) : AfP p) := by
  simp only [EFA, LinearMap.BilinForm.baseChange_tmul, _root_.mul_one]
  rw [Algebra.smul_def, zsmul_eq_mul, _root_.mul_one, map_intCast, mul_comm]

theorem EFA_inAf (D : Datum p) (x y : D.La) : EFA D (inAf D x) (inAf D y) = ((D.EF x y : ℤ) : AfP p) := by
  rw [inAf, inAf, EFA_tmul, _root_.one_mul, _root_.one_mul]

theorem isIntAf_intCast (z : ℤ) : IsIntAf ((z : AfP p)) := fun v => by
  rw [map_intCast]; exact intCast_mem _ z

theorem isIntAf_add {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

theorem isIntAf_neg {a : AfP p} (ha : IsIntAf a) : IsIntAf (-a) := fun v => by
  rw [map_neg]; exact neg_mem (ha v)

theorem isIntAf_mul {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem isIntAf_zero : IsIntAf (0 : AfP p) := by simpa using isIntAf_intCast (p := p) 0

theorem isIntAf_EFA (D : Datum p) {v w : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) :
    IsIntAf (EFA D v w) := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, x, ha, rfl⟩ := hv
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a', x', ha', rfl⟩ := hw
      rw [EFA_tmul]; exact isIntAf_mul (isIntAf_mul ha ha') (isIntAf_intCast _)
    | zero => simpa using isIntAf_zero
    | add u u' _ _ h h' => rw [map_add (f := _)]; exact isIntAf_add h h'
    | neg u _ h => rw [map_neg]; exact isIntAf_neg h
  | zero => simpa using isIntAf_zero
  | add u u' _ _ h h' => rw [map_add (f := _), LinearMap.add_apply]; exact isIntAf_add h h'
  | neg u _ h => rw [map_neg, LinearMap.neg_apply]; exact isIntAf_neg h

section Sim

variable {D : Datum p} {G : HTGroup p}

theorem bc_adj {V : Type} [AddCommGroup V] [Module ℚ V] (A : Type) [CommRing A] [Algebra ℚ A]
    (B : LinearMap.BilinForm ℚ V) (f g : Module.End ℚ V) (h : ∀ v w, B (f v) w = B v (g w)) (v w : A ⊗[ℚ] V) :
    B.baseChange A (f.baseChange A v) w = B.baseChange A v (g.baseChange A w) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v v' hv hv' => simp only [map_add (f := _), LinearMap.add_apply, hv, hv']
  | tmul a x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w w' hw hw' => simp only [map_add (f := _), hw, hw']
    | tmul a' y => simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, h]

theorem actOn_tmul {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (R : Type) [CommRing R] [Algebra ℚ R] (r : R) (c : C) :
    actOn rep R (r ⊗ₜ c) = r • (rep c).baseChange R := by
  rw [Algebra.smul_def]
  first
  | exact Algebra.TensorProduct.lift_tmul _ _ _ r c
  | (erw [Algebra.TensorProduct.lift_tmul]; rfl)
  | rfl

theorem EFA_actOn (L : Link D G) (X : AfP p ⊗[ℚ] G.C) (v w : AfP p ⊗[ℚ] VQ D) :
    EFA D (actOn L.rep (AfP p) X v) w = EFA D v (actOn L.rep (AfP p) (starT G.star (AfP p) X).unop w) := by
  induction X using TensorProduct.induction_on with
  | zero => simp
  | add X X' hX hX' => simp only [map_add (f := _), MulOpposite.unop_add, LinearMap.add_apply, hX, hX']
  | tmul r c =>
    rw [starT_tmul, actOn_tmul, actOn_tmul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul,
      LinearMap.smul_apply, map_smul]
    congr 1
    exact bc_adj (AfP p) (D.EF.baseChange ℚ) (L.rep c) (L.rep (sh G c)) (fun v w => L.adj c v w) v w

theorem EFA_actG (L : Link D G) (g : G.GAf) (v w : AfP p ⊗[ℚ] VQ D) :
    EFA D (L.actG g v) (L.actG g w) = ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) * EFA D v w := by
  obtain ⟨⟨u, c⟩, hmem⟩ := g
  have h1 : (u : AfP p ⊗[ℚ] G.C) * (starT G.star (AfP p) u).unop = algebraMap (AfP p) _ (c : AfP p) := hmem
  have h2 : (starT G.star (AfP p) u).unop * u = algebraMap (AfP p) _ (c : AfP p) := by
    have e : (starT G.star (AfP p) u).unop = ((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        algebraMap (AfP p) _ (c : AfP p) := by
      rw [← h1, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
    rw [e, _root_.mul_assoc, Algebra.commutes, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  have hg : ∀ z, L.actG ⟨⟨u, c⟩, hmem⟩ z = actOn L.rep (AfP p) (u : AfP p ⊗[ℚ] G.C) z := fun z => rfl
  rw [hg, hg, EFA_actOn, ← Module.End.mul_apply, ← map_mul, h2, AlgHom.commutes, Module.algebraMap_end_apply,
    map_smul, smul_eq_mul]
  rfl

end Sim

theorem isIntAf_one : IsIntAf (1 : AfP p) := by simpa using isIntAf_intCast (p := p) 1

theorem inAf_mem (D : Datum p) (z : D.La) : inAf D z ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, z, isIntAf_one, rfl⟩

end GlobalTheory.LKGeo.MultScale

namespace GlobalTheory.LKGeo

end GlobalTheory.LKGeo
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeckeApprox

variable {p : ℕ} [Fact p.Prime]

abbrev fAf (D : Datum p) : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D) := (D.EF.baseChange ℚ).baseChange (AfP p)

theorem isInt_one : IsIntAf (1 : AfP p) := fun v => by rw [map_one]; exact one_mem _
theorem isInt_mul {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)
theorem isInt_add {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)
theorem isInt_sub {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a - b) := fun v => by
  rw [map_sub]; exact sub_mem (ha v) (hb v)
theorem isInt_intCast (k : ℤ) : IsIntAf (k : AfP p) := fun v => by rw [map_intCast]; exact intCast_mem _ k
theorem isInt_natCast (k : ℕ) : IsIntAf (k : AfP p) := fun v => by rw [map_natCast]; exact natCast_mem _ k

def inAfH (D : Datum p) : D.La →+ AfP p ⊗[ℚ] VQ D := AddMonoidHom.mk' (inAf D) (fun x y => by
  simp only [inAf, TensorProduct.tmul_add])

theorem inAf_sub (D : Datum p) (x y : D.La) : inAf D (x - y) = inAf D x - inAf D y := map_sub (inAfH D) x y
theorem inAf_add (D : Datum p) (x y : D.La) : inAf D (x + y) = inAf D x + inAf D y := map_add (inAfH D) x y
theorem inAf_nsmul (D : Datum p) (n : ℕ) (x : D.La) : inAf D (n • x) = n • inAf D x := map_nsmul (inAfH D) n x
theorem inAf_mem (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, isInt_one, rfl⟩

theorem form_inAf (D : Datum p) (x y : D.La) : fAf D (inAf D x) (inAf D y) = (D.EF x y : AfP p) := by
  simp [fAf, inAf, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]

end GlobalTheory.HeckeApprox
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.AllWt (exOf)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

abbrev ksOpen (i : M.K.bundle.ι) (k : X.F.J) : M.X.Opens :=
  M.off ⊓ (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k)

def KSRel (i : M.K.bundle.ι) (k : X.F.J) {K : Type} [Field K] (z : Sp K ⟶ M.X) (x : K) : Prop :=
  ∀ [Algebra c.F K] (P Q : FrPt Xo c K) (t : Ix Dw → Kˣ) (v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K))
    (zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)) (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i)
    (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hz : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k),
    X.F.ChartFr k (z ≫ toFlag M) hk Q → FrBor t Q P → IsTanFrame (psiSet H) P v →
    (∀ b, zv b ≫ toFlag M = X.ptY (v b)) →
    x * (Matrix.of fun a b =>  (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      (∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix).val * evalPt z O hz (M.K.jacobian i hO g)

theorem isKS_iff_ksRel (ω : H0 M.str (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) M.off) :
    IsKS M ω ↔ ∀ (K : Type) [Field K] (z : Sp K ⟶ M.X) (i : M.K.bundle.ι) (k : X.F.J) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
      (hi : ⊤ ≤ z ⁻¹ᵁ (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k)),
      KSRel M i k z (H0.val (B := LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi ω) :=
  ⟨fun h K _ z i k ho hi _ P Q t v zv O hO g hz hzv hk hQ ht hv hl =>
      h K P Q t v z zv i k O hO g hz hzv hk ho hi hQ ht hv hl,
    fun h K _ _ P Q t v z zv i k O hO g hz hzv hk ho hi hQ ht hv hl =>
      h K z i k ho hi P Q t v zv O hO g hz hzv hk hQ ht hv hl⟩

end GlobalTheory.CompHS
end
end
