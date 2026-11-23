module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle039
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2145
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.InvDegInverse

variable {K : Type} [Field K]

def invKer {A B : AbVar K} (f : A ⟶ B) : Subgroup A.Pt where
  carrier := {x | ptMap f x = 1 ∧ ∃ k : ℕ, (k : K) ≠ 0 ∧ x ^ k = 1}
  one_mem' := ⟨map_one _, 1, by simp, one_pow _⟩
  mul_mem' := by
    rintro x y ⟨hx, a, ha, hxa⟩ ⟨hy, b, hb, hyb⟩
    refine ⟨by rw [map_mul, hx, hy, _root_.one_mul], a * b, by push_cast; exact mul_ne_zero ha hb, ?_⟩
    rw [mul_pow, pow_mul, hxa, one_pow, mul_comm a b, pow_mul, hyb, one_pow, _root_.one_mul]
  inv_mem' := by
    rintro x ⟨hx, a, ha, hxa⟩
    exact ⟨by rw [map_inv, hx, inv_one], a, ha, by rw [inv_pow, hxa, inv_one]⟩

theorem finite_invKer {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) : Finite (invKer f) := by
  have : Finite (ptMap f).ker := (GlobalTheory.AV.AbVar.isFinite_iff_finite_ker K A B f).1 hf.1
  exact Finite.of_injective (fun x : invKer f => (⟨x.1, x.2.1⟩ : (ptMap f).ker))
    (fun x y h => Subtype.ext (congrArg (fun z : (ptMap f).ker => (z : A.Pt)) h))

theorem card_invKer_ne_zero {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) :
    ((Nat.card (invKer f) : ℕ) : K) ≠ 0 := by
  haveI := finite_invKer f hf
  intro h0
  have hpos : 0 < Nat.card (invKer f) := Nat.card_pos
  have hpd : ringChar K ∣ Nat.card (invKer f) := (ringChar.spec K _).1 h0
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hpp | hp0
  · haveI := Fact.mk hpp
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (ringChar K) hpd
    obtain ⟨_, k, hk, hyk⟩ := y.2
    have : ringChar K ∣ k := by
      rw [← hy, ← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hyk
    exact hk ((ringChar.spec K k).2 this)
  · rw [hp0, zero_dvd_iff] at hpd
    omega

theorem galPts_mem_invKer {A B : AbVar K} (f : A ⟶ B) (σ : Gal K) (x : A.Pt) (hx : x ∈ invKer f) :
    galPts A.X σ x ∈ invKer f := by
  obtain ⟨h1, k, hk, hxk⟩ := hx
  refine ⟨?_, k, hk, by rw [← map_pow, hxk, map_one]⟩
  have e : ptMap f (galPts A.X σ x) = galPts B.X σ (ptMap f x) :=
    show (specAut σ ≫ x) ≫ f.hom = specAut σ ≫ (x ≫ f.hom) from Category.assoc _ _ _
  rw [e, h1, map_one]

end GlobalTheory.AV.AbVar.InvDegInverse
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finiteEtale_subgroupScheme_of_galoisStable_points : ∀ (K : Type) [Field K] (A : AbVar K) (G : Subgroup A.Pt), Finite G → ((Nat.card G : ℕ) : K) ≠ 0 → (∀ (σ : Gal K) (x : A.Pt), x ∈ G → galPts A.X σ x ∈ G) → ∃ (H : Over (Sp K)) (_ : GrpObj H) (i : H ⟶ A.X), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Etale H.hom ∧ ∀ x : A.Pt, x ∈ G ↔ ∃ y, y ≫ i = x := by
  first | (exact @GlobalTheory.FinEtSubgroup.exists_finiteEtale_subgroup_of_points) | (exact GlobalTheory.FinEtSubgroup.exists_finiteEtale_subgroup_of_points) | (intros; apply GlobalTheory.FinEtSubgroup.exists_finiteEtale_subgroup_of_points  <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PointMap

section General

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P P' : Point p v O Λ)

def mapT (α : P.A.A ⟶ P'.A.A) [IsMonHom α] : P.T →ₗ[ℤ_[p]] P'.T :=
  Tate.map p (IndepPoint.ptsHom α _)

theorem lev_mapT (α : P.A.A ⟶ P'.A.A) [IsMonHom α] (t : P.T) (n : ℕ) :
    (mapT P P' α t).lev n = t.lev n ≫ α := rfl

def mapV [Algebra ℤ_[p] C] (α : P.A.A ⟶ P'.A.A) [IsMonHom α] : P.V →ₗ[C] P'.V :=
  (mapT P P' α).baseChange C

variable [IsAlgClosed C] [CharZero C]

def adjT (α : P.A.A ⟶ P'.A.A) [IsMonHom α] : P'.T →ₗ[ℤ_[p]] P.T :=
  (LinearEquiv.ofBijective _ P.pairT_bijective).symm.toLinearMap ∘ₗ (mapT P P' α).dualMap ∘ₗ pairT P'.A P'.eps

theorem pairT_adjT_left (α : P.A.A ⟶ P'.A.A) [IsMonHom α] (t : P'.T) (s : P.T) :
    pairT P.A P.eps (adjT P P' α t) s = pairT P'.A P'.eps t (mapT P P' α s) :=
  LinearMap.congr_fun ((LinearEquiv.ofBijective _ P.pairT_bijective).apply_symm_apply
    ((mapT P P' α).dualMap (pairT P'.A P'.eps t))) s

theorem pairT_mapT (α : P.A.A ⟶ P'.A.A) [IsMonHom α] (s : P.T) (t : P'.T) :
    pairT P'.A P'.eps (mapT P P' α s) t = pairT P.A P.eps s (adjT P P' α t) := by
  rw [← (isAlt_pairT P'.A P'.eps).neg_eq t, ← pairT_adjT_left, (isAlt_pairT P.A P.eps).neg_eq]

def adjV [Algebra ℤ_[p] C] (α : P.A.A ⟶ P'.A.A) [IsMonHom α] : P'.V →ₗ[C] P.V :=
  (adjT P P' α).baseChange C

theorem adjV_tmul [Algebra ℤ_[p] C] (α : P.A.A ⟶ P'.A.A) [IsMonHom α] (c : C) (t : P'.T) :
    adjV P P' α (c ⊗ₜ t) = c ⊗ₜ adjT P P' α t := rfl

end General

section Good

variable {Λ : Type} [CommRing Λ] [StarRing Λ]

def pullAct {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Out.PolAV S) (o : B.OAct Λ) :
    (StrictPull.polPull B f).OAct Λ := (exists_oAct_polPull f B o).choose

theorem eq_map_of_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (a : X ⟶ Y)
    (b : (Over.pullback f).obj X ⟶ (Over.pullback f).obj Y)
    (h : b.left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left) : b = (Over.pullback f).map a :=
  Over.OverMorphism.ext (pullback.hom_ext (h.trans (pullback.lift_fst _ _ _).symm)
    ((Over.w b).trans (Over.w ((Over.pullback f).map a)).symm))

theorem pullAct_act {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Out.PolAV S) (o : B.OAct Λ) (a : Λ) :
    (pullAct f B o).act a = (Over.pullback f).map (o.act a) :=
  eq_map_of_fst f _ _ ((exists_oAct_polPull f B o).choose_spec a)

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] (hv : v.Integers O) (ε : Eps p C) {R : Type} [CommRing R] (j : R →+* O)

def goodPoint (B : Out.PolAV (Sp R)) (o : B.OAct Λ) : Point p v O Λ :=
  ofGoodReduction hv ε (StrictPull.polPull B (spMap j)) (pullAct (spMap j) B o)

variable {B B' : Out.PolAV (Sp R)} (o : B.OAct Λ) (o' : B'.OAct Λ)

theorem goodPoint_oA (a : Λ) : (goodPoint hv ε j B o).oA.act a =
    (Over.pullback (spMap (algebraMap O C))).map ((Over.pullback (spMap j)).map (o.act a)) :=
  (pullAct_act _ _ (pullAct (spMap j) B o) a).trans (congrArg _ (pullAct_act _ B o a))

def homO (f : B.A ⟶ B'.A) : (goodPoint hv ε j B o).Gt ⟶ (goodPoint hv ε j B' o').Gt :=
  (Over.pullback (spMap j)).map f

def homC (f : B.A ⟶ B'.A) : (goodPoint hv ε j B o).A.A ⟶ (goodPoint hv ε j B' o').A.A :=
  (Over.pullback (spMap (algebraMap O C))).map ((Over.pullback (spMap j)).map f)

instance (f : B.A ⟶ B'.A) [IsMonHom f] : IsMonHom (homO hv ε j o o' f) :=
  inferInstanceAs (IsMonHom ((Over.pullback (spMap j)).map f))

instance (f : B.A ⟶ B'.A) [IsMonHom f] : IsMonHom (homC hv ε j o o' f) :=
  inferInstanceAs (IsMonHom ((Over.pullback (spMap (algebraMap O C))).map ((Over.pullback (spMap j)).map f)))

def homT (f : B.A ⟶ B'.A) [IsMonHom f] : (goodPoint hv ε j B o).T →ₗ[ℤ_[p]] (goodPoint hv ε j B' o').T :=
  mapT _ _ (homC hv ε j o o' f)

def homV [Algebra ℤ_[p] C] (f : B.A ⟶ B'.A) [IsMonHom f] :
    (goodPoint hv ε j B o).V →ₗ[C] (goodPoint hv ε j B' o').V :=
  mapV _ _ (homC hv ε j o o' f)

def homLie (f : B.A ⟶ B'.A) [IsMonHom f] (x : LieG (goodPoint hv ε j B o).Gt) : LieG (goodPoint hv ε j B' o').Gt :=
  TorusTateLie.lieMap (homO hv ε j o o' f) x

theorem lev_homT (f : B.A ⟶ B'.A) [IsMonHom f] (t : (goodPoint hv ε j B o).T) (n : ℕ) :
    (homT hv ε j o o' f t).lev n = t.lev n ≫ homC hv ε j o o' f := rfl

end Good

section Triples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def patAct {S : Scheme.{0}} (T : PAT H S) : letI := H.starRing; T.pol.OAct (𝓞 E) :=
  letI := H.starRing
  haveI : IsCommMonObj T.t.G := T.ab.comm
  ⟨T.t.act.toRingAct, fun a =>
    (GlobalTheory.RosLam.rosatiAdj_iff_lamEq GlobalTheory.firstFiveLaws.1.globalFns _ T.pol _ _ (T.t.act.hom a) (T.t.act.hom _)).2 (by
      change GlobalTheory.CM.LamEq _ _ _ _ _ (T.t.act.act (H.bar a))
      simpa [GlobalTheory.CM.LamEq] using T.t.adj a)⟩

variable {K : Type} [Field K] {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

abbrev patPoint (T : PAT H (Sp (𝓞 K))) : letI := H.starRing; Point ℓ v O (𝓞 E) :=
  letI := H.starRing
  goodPoint hv ε (embO hv i) T.pol (patAct T)

section Linear

variable {T T' : PAT H (Sp (𝓞 K))} {f : T.t.G ⟶ T'.t.G} (hf : Serre.IsLinearHom T.t.act T'.t.act f)

abbrev patT : letI := H.starRing; (patPoint hv ε i T).T →ₗ[ℤ_[ℓ]] (patPoint hv ε i T').T :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  homT (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') f

abbrev patV [Algebra ℤ_[ℓ] C] : letI := H.starRing; (patPoint hv ε i T).V →ₗ[C] (patPoint hv ε i T').V :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  homV (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') f

abbrev patLie : letI := H.starRing; LieG (patPoint hv ε i T).Gt → LieG (patPoint hv ε i T').Gt :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  homLie (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') f

end Linear

variable [NumberField K] {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)

abbrev pointB : letI := H.starRing; Point ℓ v O (𝓞 E) := patPoint hv ε i X.B

abbrev pointA (b : Bool) : letI := H.starRing; Point ℓ v O (𝓞 E) := patPoint hv ε i (X.A b)

abbrev phiV [Algebra ℤ_[ℓ] C] (k : Fin p ⊕ Fin q) :
    letI := H.starRing; (pointA hv ε i X k.isLeft).V →ₗ[C] (pointB hv ε i X).V := patV hv ε i (X.lin k)

abbrev phiLie (k : Fin p ⊕ Fin q) :
    letI := H.starRing; LieG (pointA hv ε i X k.isLeft).Gt → LieG (pointB hv ε i X).Gt := patLie hv ε i (X.lin k)

abbrev phiVP [Algebra ℤ_[ℓ] C] (a : Fin p) :
    letI := H.starRing; (pointA hv ε i X true).V →ₗ[C] (pointB hv ε i X).V :=
  patV (T := X.A true) hv ε i (X.lin (Sum.inl a))

abbrev phiVQ [Algebra ℤ_[ℓ] C] (b : Fin q) :
    letI := H.starRing; (pointA hv ε i X false).V →ₗ[C] (pointB hv ε i X).V :=
  patV (T := X.A false) hv ε i (X.lin (Sum.inr b))

end Triples

end GlobalTheory.PointMap
end
end

section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.FlagBasis

theorem exists_coeff {C U : Type} [Field C] [AddCommGroup U] [Module C U] {n : ℕ} (b : Fin n → U) (i : ℕ)
    {y : U} (hy : y ∈ step C b i) : ∃ r : Fin n → C, (∀ j : Fin n, i ≤ j → r j = 0) ∧ ∑ j, r j • b j = y := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨Pi.single k 1, fun j hj => Pi.single_eq_of_ne ?_ _, by simp [Pi.single_apply]⟩
    rintro rfl
    exact absurd hk (not_lt.2 hj)
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨r + s, fun j hj => by simp [hr j hj, hs j hj], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨a • r, fun j hj => by simp [hr j hj], by simp [Finset.smul_sum, smul_smul]⟩

theorem exists_lift {O C U : Type} [CommRing O] [Field C] [Algebra O C] [AddCommGroup U] [Module C U] [Module O U]
    [IsScalarTower O C U] {v : Valuation C ℝ≥0} (hv : v.Integers O) {n : ℕ} {La : Submodule O U} (hfg : La.FG)
    {b : Fin n → U} (hb : LinearIndependent C b) (i : Fin n) {a : C} (ha : a ≠ 0) (hLa : a • b i ∈ La) :
    ∃ (w : U) (c : C), c ≠ 0 ∧ w ∈ La ∧ w - c • b i ∈ step C b i ∧
      ∀ x ∈ La, x ∈ step C b (i + 1) → ∃ o : O, x - o • w ∈ step C b i := by
  obtain ⟨c, hc, e, -⟩ := exists_grAt_eq hv hfg b i (hb.notMem_span_image (by simp)) ha
    (Submodule.zero_mem _) (by rwa [add_zero])
  obtain ⟨w, hw, hw'⟩ : c • (step C b i).mkQ (b i) ∈ grAt C La b i :=
    e ▸ Submodule.mem_span_singleton_self _
  have hw'' : (step C b i).mkQ w = c • (step C b i).mkQ (b i) := hw'
  refine ⟨w, c, hc, hw.1, (Submodule.Quotient.eq _).1 hw'', fun x hx hx' => ?_⟩
  have h1 : (step C b i).mkQ x ∈ grAt C La b i := ⟨x, ⟨hx, hx'⟩, rfl⟩
  rw [e, ← hw''] at h1
  obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 h1
  exact ⟨o, (Submodule.Quotient.eq _).1 ho.symm⟩

theorem exists_adapted_basis : ∀ (O C U : Type) [CommRing O] [Field C] [Algebra O C] [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] (v : Valuation C ℝ≥0), v.Integers O → ∀ (n : ℕ) (La : Submodule O U), La.FG → ∀ b : Fin n → U, LinearIndependent C b → (∀ j, ∃ a : C, a ≠ 0 ∧ a • b j ∈ La) → ∃ g : Matrix (Fin n) (Fin n) C, (∀ i j, i < j → g i j = 0) ∧ (∀ i, g i i ≠ 0) ∧ IsLatBasis C La fun i => ∑ j, g i j • b j := by
  intro O C U _ _ _ _ _ _ _ v hv n La hfg b hb hLa
  classical
  choose a ha hLa using hLa
  choose w c hc hw hwb hgen using fun i => exists_lift hv hfg hb i (ha i) (hLa i)
  choose r hr hrb using fun i => exists_coeff b _ (hwb i)
  let g : Matrix (Fin n) (Fin n) C := fun i j => r i j + if j = i then c i else 0
  have hg : ∀ i j, i < j → g i j = 0 := fun i j h => by
    simp [g, hr i j h.le, h.ne']
  have hd : ∀ i, g i i ≠ 0 := fun i => by simpa [g, hr i i le_rfl] using hc i
  have hgw : (fun i => ∑ j, g i j • b j) = w := funext fun i => by
    simp [g, add_smul, Finset.sum_add_distrib, hrb]
  have hws : ∀ i : Fin n, w i ∈ step C b (i + 1) := fun i => by
    simpa using Submodule.add_mem _ (step_mono b (Nat.le_succ _) (hwb i))
      (Submodule.smul_mem _ (c i) (mem_step_succ b i))
  refine ⟨g, hg, hd, ?_, ?_⟩
  · have hu : IsUnit g := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isLowerTriangular _ fun i j hij => hg i j hij]
      exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
    exact (Matrix.linearIndependent_rows_iff_isUnit.2 hu).map' (Fintype.linearCombination C b)
      (LinearMap.ker_eq_bot.2 fun s t h => funext (Fintype.linearIndependent_iffₛ.1 hb s t h))
  · rw [hgw]
    refine le_antisymm (le_inf (Submodule.span_le.2 (Set.range_subset_iff.2 hw))
      (Submodule.span_le_restrictScalars O C _)) ?_
    have key : ∀ k, k ≤ n → ∀ x ∈ La, x ∈ step C b k → x ∈ Submodule.span O (Set.range w) := by
      intro k
      induction k with
      | zero =>
        intro _ x _ hx
        rw [step_zero, Submodule.mem_bot] at hx
        exact hx ▸ Submodule.zero_mem _
      | succ k ih =>
        intro hk x hx hx'
        obtain ⟨o, ho⟩ := hgen ⟨k, hk⟩ x hx hx'
        have h1 := ih (Nat.le_of_succ_le hk) _ (La.sub_mem hx (La.smul_mem o (hw _))) ho
        simpa using Submodule.add_mem _ h1
          (Submodule.smul_mem _ o (Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩))
    rintro x ⟨hx, hx'⟩
    exact key n le_rfl x hx (Submodule.span_le.2 (Set.range_subset_iff.2 fun i =>
      step_mono b (Nat.succ_le_of_lt i.2) (hws i)) hx')

end GlobalTheory.CompHt.FlagBasis
end

section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

theorem alC_surjective_and_linearIndependent_bLie :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), HTChar p v P.Gt → Function.Surjective P.alC ∧ ∀ (n : ℕ) (x : Fin n → LieG P.Gt), LinearIndependent C (fun j => evLie P (x j)) → LinearIndependent C (fun j => P.bLie (x j)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P hHT
  have hp : p.Prime := Fact.out
  have h0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hs : Function.Surjective P.alC := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    rintro w -
    induction w using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add a b ha hb => exact Submodule.add_mem _ ha hb
    | tmul c f =>
      have h1 : v (algebraMap O C (p : O)) ^ (p - 1) ≤ v (p : C) := by
        have hle := P.integers.map_le_one (p : O)
        rw [map_natCast] at hle ⊢
        exact pow_le_of_le_one zero_le hle (by have := hp.two_le; omega)
      have h2 := hHT (p : O) h1 f.1 f.2
      rw [← (weilChar_surjective_and_map_range_al p C v O Λ P).2] at h2
      obtain ⟨_, ⟨t, rfl⟩, ht⟩ := h2
      have h3 : P.al t = (p : O) • f := Subtype.ext ht
      refine ⟨(c * (p : C)⁻¹) • P.inclT t, ?_⟩
      rw [map_smul, P.alC_inclT, h3, map_smul, ← algebraMap_smul C (p : O), map_natCast, smul_smul,
        inv_mul_cancel_right₀ h0, Point.inclOm, TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul,
        _root_.mul_one]
  refine ⟨hs, fun n x hx => LinearIndependent.of_comp P.pairV ?_⟩
  have e : (⇑P.pairV ∘ fun j => P.bLie (x j)) = ⇑P.alC.dualMap ∘ fun j => evLie P (x j) :=
    funext fun j => LinearMap.ext fun w => pairV_bLie_eq_evLie (x j) w
  rw [e]
  exact hx.map' _ (LinearMap.ker_eq_bot.2 (LinearMap.dualMap_injective_of_surjective hs))

end GlobalTheory.CompHt
end

section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

section Lat

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {n : ℕ}

theorem diag_ne_zero_of_linearIndependent {w : Fin n → U} {g : Matrix (Fin n) (Fin n) C}
    (hg : ∀ i j, i < j → g i j = 0) (h : LinearIndependent C fun i => ∑ j, g i j • w j) (i : Fin n) : g i i ≠ 0 := by
  have hl : LinearIndependent C g.row := LinearIndependent.of_comp (Fintype.linearCombination C w) h
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hl)
  rw [Matrix.det_of_lowerTriangular _ fun i j hij => hg i j hij] at hu
  exact Finset.prod_ne_zero_iff.1 hu.ne_zero i (Finset.mem_univ i)

theorem IsLatBasis.diag_le {v : Valuation C ℝ≥0} (hv : v.Integers O) {La : Submodule O U} {w : Fin n → U}
    {g g' : Matrix (Fin n) (Fin n) C} (hg : ∀ i j, i < j → g i j = 0) (hg' : ∀ i j, i < j → g' i j = 0)
    (h : IsLatBasis C La fun i => ∑ j, g i j • w j) (i : Fin n) (h' : ∑ j, g' i j • w j ∈ La) :
    v (g' i i) ≤ v (g i i) := by
  have hd : IsUnit g.det := lowerTri_isUnit_det g hg fun i => (diag_ne_zero_of_linearIndependent hg h.1 i).isUnit
  have e : (g' * g⁻¹) * g = g' := Matrix.nonsing_inv_mul_cancel_right _ _ hd
  have e1 : ∑ j, (g' * g⁻¹) i j • ∑ k, g j k • w k = ∑ k, g' i k • w k := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_smul, ← Matrix.mul_apply, e]
  obtain ⟨b, hb⟩ := (h.sum_mem_iff ((g' * g⁻¹) i)).1 (e1 ▸ h') i
  have e2 := lowerTri_mul_diag _ _ (lowerTri_mul _ _ hg' (lowerTri_inv g hg hd)) hg i
  rw [e] at e2
  rw [e2, map_mul, ← hb]
  exact mul_le_of_le_one_left' (hv.map_le_one b)

theorem IsLatBasis.mem {La : Submodule O U} {w : Fin n → U} (h : IsLatBasis C La w) (i : Fin n) : w i ∈ La :=
  (h.2.le (Submodule.subset_span ⟨i, rfl⟩)).1

end Lat

attribute [local instance] algPadicInt algPadicField towerPadic factPadic PadicComplexHost.isAdicComplete

end GlobalTheory.CompHt
end
