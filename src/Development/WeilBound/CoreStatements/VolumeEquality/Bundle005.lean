module

public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle167
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle025
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushFibLinkA
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushFibLinkB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis

@[expose] public section

section

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

section Lin

variable {Ω₃ : Type} [Field Ω₃] (O : ValuationSubring Ω₃) {r : ℕ}

theorem mu_det_le (T T' : Matrix (Fin r) (Fin r) Ω₃)
    (h : ∀ k, (fun m => T m k) ∈ Submodule.span O (Set.range fun k m => T' m k)) :
    O.valuation T.det ≤ O.valuation T'.det := by
  choose N hN using fun k => (Submodule.mem_span_range_iff_exists_fun O).1 (h k)
  have e : T = T' * (Matrix.of fun a b => N b a).map O.subtype := by
    ext m k
    have := congrFun (hN k) m
    simp only [Finset.sum_apply, Pi.smul_apply] at this
    rw [← this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have e2 : ((Matrix.of fun a b => N b a).map O.subtype).det = ((Matrix.of fun a b => N b a).det : O) :=
    (RingHom.map_det O.subtype _).symm
  rw [e, Matrix.det_mul, map_mul, e2]
  exact mul_le_of_le_one_right' (O.valuation_le_one _)

theorem mu_det_eq (T T' : Matrix (Fin r) (Fin r) Ω₃)
    (h : Submodule.span O (Set.range fun k m => T m k) = Submodule.span O (Set.range fun k m => T' m k)) :
    O.valuation T.det = O.valuation T'.det :=
  le_antisymm (mu_det_le O T T' fun k => h ▸ Submodule.subset_span ⟨k, rfl⟩)
    (mu_det_le O T' T fun k => h ▸ Submodule.subset_span ⟨k, rfl⟩)

theorem mu_coord {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] (R : Subring Ω) (i : Ω →+* Ω₃) (hi : ∀ a ∈ R, i a ∈ O)
    (c : Fin r → V) (hc : LinearIndependent Ω c) (Z : Set V) (Λ : Submodule O (Fin r → Ω₃))
    (hZ : ∀ w ∈ Z, ∃ x : Fin r → Ω, w = ∑ m, x m • c m ∧ (fun m => i (x m)) ∈ Λ) (x : Fin r → Ω)
    (hx : ∑ m, x m • c m ∈ Submodule.span R Z) : (fun m => i (x m)) ∈ Λ := by
  have key : ∀ w ∈ Submodule.span R Z, ∃ x : Fin r → Ω, w = ∑ m, x m • c m ∧ (fun m => i (x m)) ∈ Λ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact hZ w hw
    | zero => exact ⟨0, by simp, by simp only [Pi.zero_apply, map_zero]; exact Λ.zero_mem⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, rfl, hx⟩ := ha
      obtain ⟨y, rfl, hy⟩ := hb
      refine ⟨x + y, by simp [add_smul, Finset.sum_add_distrib], ?_⟩
      convert Λ.add_mem hx hy using 1
      ext m; simp
    | smul a w _ hw =>
      obtain ⟨x, rfl, hx⟩ := hw
      refine ⟨fun m => (a : Ω) * x m, ?_, ?_⟩
      · rw [Subring.smul_def]
        simp [Finset.smul_sum, mul_smul]
      · convert Λ.smul_mem ⟨i a, hi a a.2⟩ hx using 1
        ext m
        show i (a * x m) = i a * i (x m)
        exact map_mul _ _ _
  obtain ⟨x', e, hx'⟩ := key _ hx
  have : x = x' := funext (Fintype.linearIndependent_iffₛ.1 hc x x' e)
  exact this ▸ hx'

theorem mu_alg {G : Type} [CommGroupWithZero G] {m₁ m₂ e₁ e₂ t₁ t₂ r₁ r₂ : G} (h₁ : m₁ * e₁ * t₁ = 1) (h₂ : m₂ * e₂ * t₂ = 1)
    (h : r₁ * t₁ = r₂ * t₂) (hr : r₁ ≠ 0) : m₂ = e₁ * r₂ / (r₁ * e₂) * m₁ := by
  have he : e₂ ≠ 0 := by rintro rfl; simp at h₂
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hr he)]
  calc m₂ * (r₁ * e₂) = m₂ * (r₁ * e₂) * (m₁ * e₁ * t₁) := by rw [h₁, mul_one]
    _ = m₂ * e₂ * (r₁ * t₁) * (m₁ * e₁) := by ac_rfl
    _ = m₂ * e₂ * t₂ * (e₁ * r₂ * m₁) := by rw [h]; ac_rfl
    _ = _ := by rw [h₂, one_mul]

end Lin

section Lats

variable {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] {ξ : Sp Ω ⟶ X} {q : Cpt ξ}

theorem mu_gen_ratio {Λ : Lat ξ Ω} {t t' : Ω} (h : Λ.IsGenAt q t) (h' : Λ.IsGenAt q t') : t' / t ∈ regAt ξ q := by
  have : t' ∈ Submodule.span (regAt ξ q) {t} := h.2 ▸ h'.2 ▸ Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
  have e : (a : Ω) * t = t' := ha
  rw [← e, mul_div_cancel_right₀ _ h.1]
  exact a.2

theorem mu_gen_val {O : ValuationSubring Ω₃} {i : Ω →+* Ω₃} (hD : Dom O i ξ q) {Λ : Lat ξ Ω} {t t' : Ω} (h : Λ.IsGenAt q t)
    (h' : Λ.IsGenAt q t') : O.valuation (i t) = O.valuation (i t') := by
  have k : ∀ {t t' : Ω}, Λ.IsGenAt q t → Λ.IsGenAt q t' → O.valuation (i t') ≤ O.valuation (i t) := fun {t t'} h h' => by
    have h1 := (O.valuation_le_one_iff _).2 (hD.1 _ (mu_gen_ratio h h'))
    have e : t' = t * (t' / t) := (mul_div_cancel₀ _ h.1).symm
    rw [e, map_mul, map_mul]
    exact mul_le_of_le_one_right' h1
  exact le_antisymm (k h' h) (k h h')

theorem mu_tens_gen {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} (a : I → ℤ) {t : I → Ω} (h : ∀ j, (Λ j).IsGenAt q (t j)) :
    (Lat.tens Λ a).IsGenAt q (∏ j, t j ^ a j) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ (h j).1, le_antisymm (Submodule.span_le.2 ?_)
    (Submodule.span_le.2 ?_)⟩
  · rintro _ ⟨s, hs, rfl⟩
    have hm : ∏ j, (s j / t j) ^ a j ∈ regAt ξ q := prod_mem fun j _ => by
      obtain ⟨n, e | e⟩ := (a j).eq_nat_or_neg
      · rw [e, zpow_natCast]; exact pow_mem (mu_gen_ratio (h j) (hs j)) _
      · rw [e, zpow_neg, zpow_natCast, ← inv_pow, inv_div]; exact pow_mem (mu_gen_ratio (hs j) (h j)) _
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hm⟩, ?_⟩
    show (∏ j, (s j / t j) ^ a j) * ∏ j, t j ^ a j = _
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [← mul_zpow, div_mul_cancel₀ _ (h j).1]
  · rintro _ rfl
    exact Submodule.subset_span ⟨t, h, rfl⟩

theorem mu_tens_ex {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} {a : I → ℤ} {w : Ω} (h : (Lat.tens Λ a).IsGenAt q w) :
    ∃ t : I → Ω, ∀ j, (Λ j).IsGenAt q (t j) := by
  by_contra hn
  have e : (Lat.tens Λ a) q = ⊥ := by
    refine le_bot_iff.1 (Submodule.span_le.2 ?_)
    rintro _ ⟨s, hs, rfl⟩
    exact absurd ⟨s, hs⟩ hn
  have : w ∈ (Lat.tens Λ a) q := h.2 ▸ Submodule.mem_span_singleton_self _
  rw [e] at this
  exact h.1 this

theorem mu_deg_gen {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {Λ : Lat ξ Ω} {a : K → ℤ} {e : Ω}
    (h : Λ.IsDegOn Set.univ y a e) {ch : ∀ k, J k} (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ch q) :
    Λ.IsGenAt q ((∏ k, y ⟨k, ch k⟩ ^ a k) * e) :=
  ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ _))) h.1,
    h.2 q trivial ch hc⟩

theorem mu_char0 [Algebra ℚ Ω₃] {O : ValuationSubring Ω₃} {i : Ω →+* Ω₃} (hD : Dom O i ξ q)
    (hO : ∀ x : ℚ, algebraMap ℚ Ω₃ x ∈ O) (p : ℕ) (hp : p.Prime) : ¬ InFibre ξ p q := by
  have : CharZero Ω₃ := algebraRat.charZero Ω₃
  have h0 : (p : Ω) ≠ 0 := fun h => by
    have := congrArg i h
    rw [map_natCast, map_zero] at this
    exact hp.ne_zero (Nat.cast_eq_zero.1 this)
  refine not_not.2 ⟨h0, natCast_mem _ _, hD.2 _ (natCast_mem _ _) h0 ?_⟩
  simpa using hO (p : ℚ)⁻¹

theorem mu_side {V : Type} [AddCommGroup V] [Module Ω V] (L : Lat ξ V) {r r' : ℕ} (hr : r = r') (W : Submodule Ω V)
    (hL : L.IsVB r W) (c : Fin r → V) (hc : LinearIndependent Ω c) (hW : Submodule.span Ω (Set.range c) = W)
    (s : Fin r' → V) (hs : LinearIndependent Ω s) (hsW : ∀ k, s k ∈ W) :
    ∃ ρ : Ω, ρ ≠ 0 ∧ ∀ (q : Cpt ξ) (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃) (Ω₀ : Type) (ψ : Ω₀ → Ω) (B : Set (Fin r → Ω₀)),
      Dom O i ξ q → L q = Submodule.span (regAt ξ q) {w | ∃ a ∈ B, w = ∑ m, ψ (a m) • c m} →
      ∃ (t : Ω) (T : Matrix (Fin r) (Fin r) Ω₃), (detLat L s).IsGenAt q t ∧ T.det = i (ρ * t) ∧
        Submodule.span O (Set.range fun k m => T m k) = Submodule.span O {x | ∃ a ∈ B, x = fun m => i (ψ (a m))} := by
  subst hr
  subst hW
  choose P hP using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hsW k)
  have hPi : LinearIndependent Ω P := by
    refine LinearIndependent.of_comp (Fintype.linearCombination Ω c) ?_
    convert hs using 1
    funext k
    simpa [Fintype.linearCombination_apply] using hP k
  set Pm : Matrix (Fin r) (Fin r) Ω := (Matrix.of P).transpose with hPm
  have hd : Pm.det ≠ 0 := by
    rw [hPm, Matrix.det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hPi)).ne_zero
  refine ⟨Pm.det, hd, fun q O i Ω₀ ψ B hD hq => ?_⟩
  obtain ⟨U, hU, b, hb, hf⟩ := hL q trivial
  have hf := hf q trivial hU
  choose T₀ hT using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1
    (show b k ∈ Submodule.span Ω (Set.range c) from hb ▸ Submodule.subset_span ⟨k, rfl⟩)
  set Tm : Matrix (Fin r) (Fin r) Ω := (Matrix.of T₀).transpose with hTm
  have hPT : Pm * (Pm⁻¹ * Tm) = Tm := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hd), Matrix.one_mul]
  have hbs : ∀ k, b k = ∑ k', (Pm⁻¹ * Tm) k' k • s k' := fun k => by
    rw [← hT k]
    simp only [← hP, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have := congrFun (congrFun hPT m) k
    rw [Matrix.mul_apply] at this
    rw [show T₀ k m = Tm m k from rfl, ← this]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  refine ⟨(Pm⁻¹ * Tm).det, Tm.map i, GlobalTheory.T.det_lattice_frame_gen X Ω ξ V L r s b _ q hs hf hbs, ?_, le_antisymm (Submodule.span_le.2 ?_)
    (Submodule.span_le.2 ?_)⟩
  · rw [← Matrix.det_mul, hPT]
    exact (RingHom.map_det i _).symm
  · rintro _ ⟨k, rfl⟩
    refine mu_coord O (regAt ξ q) i hD.1 c hc {w | ∃ a ∈ B, w = ∑ m, ψ (a m) • c m} _ ?_ (T₀ k) ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨_, rfl, Submodule.subset_span ⟨a, ha, rfl⟩⟩
    · rw [← hq, hT k, hf.2]
      exact Submodule.subset_span ⟨k, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine mu_coord O (regAt ξ q) i hD.1 c hc (Set.range b) _ ?_ (fun m => ψ (a m)) ?_
    · rintro _ ⟨k, rfl⟩
      exact ⟨T₀ k, (hT k).symm, Submodule.subset_span ⟨k, rfl⟩⟩
    · rw [← hf.2, hq]
      exact Submodule.subset_span ⟨a, ha, rfl⟩

end Lats

end SheetDecomposition
end
end

section

noncomputable section

namespace SheetDecomposition

open scoped TensorProduct

namespace Join

theorem tower {P Ω : Type} [Field P] [Field Ω] (φ : P →+* Ω) (K₀ : Subfield P) :
    Module.finrank (K₀.map φ) Ω = Module.finrank K₀ P * Module.finrank φ.fieldRange Ω := by
  letI : Algebra P Ω := φ.toAlgebra
  letI : Algebra K₀ Ω := (φ.comp K₀.subtype).toAlgebra
  haveI : IsScalarTower K₀ P Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : Module.finrank P Ω = Module.finrank φ.fieldRange Ω :=
    Algebra.finrank_eq_of_equiv_equiv φ.rangeRestrictFieldEquiv (RingEquiv.refl Ω) (RingHom.ext fun _ => rfl)
  have h2 : Module.finrank K₀ Ω = Module.finrank (K₀.map φ) Ω :=
    Algebra.finrank_eq_of_equiv_equiv (K₀.toSubring.equivMapOfInjective φ φ.injective) (RingEquiv.refl Ω)
      (RingHom.ext fun _ => rfl)
  rw [← h1, ← h2, Module.finrank_mul_finrank]

theorem finrank_congr {Ω : Type} [Field Ω] {A B : Subfield Ω} (h : A = B) : Module.finrank A Ω = Module.finrank B Ω := by
  subst h; rfl

theorem map_adjoin {F P Ω : Type} [Field F] [Field P] [Field Ω] [Algebra F P] [Algebra F Ω] (φ : P →+* Ω)
    (hφ : φ.comp (algebraMap F P) = algebraMap F Ω) {I : Type} (w : I → P) :
    (IntermediateField.adjoin F (Set.range w)).toSubfield.map φ =
      (IntermediateField.adjoin F (Set.range fun q => φ (w q))).toSubfield := by
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield, RingHom.map_field_closure, Set.image_union,
    ← Set.range_comp, ← Set.range_comp, ← hφ]
  rfl

theorem core (F A B : Type) [Field F] [Field A] [Field B] [Algebra F A] [Algebra F B] {I : Type} (w : I → B) (d₂ e : ℕ)
    (hw : AlgebraicIndependent F w) (hd : 0 < d₂) (hB : Module.finrank (IntermediateField.adjoin F (Set.range w)) B = d₂)
    (he : 0 < e) (hA : Module.finrank F A = e) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra A Ω) (i : B →+* Ω) (d n : ℕ),
      i.comp (algebraMap F B) = (algebraMap A Ω).comp (algebraMap F A) ∧ AlgebraicIndependent A (fun q => i (w q)) ∧ 0 < d ∧
      Module.finrank (IntermediateField.adjoin A (Set.range fun q => i (w q))) Ω = d ∧
      Module.finrank i.fieldRange Ω = n ∧ 0 < n ∧ n * d₂ = d * e := by
  haveI : FiniteDimensional F A := Module.finite_of_finrank_pos (hA ▸ he)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (B ⊗[F] A)
  letI : Field ((B ⊗[F] A) ⧸ m) := Ideal.Quotient.field m
  let j : A →ₐ[F] ((B ⊗[F] A) ⧸ m) := (Ideal.Quotient.mkₐ F m).comp Algebra.TensorProduct.includeRight
  letI : Algebra A ((B ⊗[F] A) ⧸ m) := j.toRingHom.toAlgebra
  haveI : IsScalarTower F A ((B ⊗[F] A) ⧸ m) := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Module.Finite B ((B ⊗[F] A) ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ B m).toLinearMap (Ideal.Quotient.mkₐ_surjective B m)
  let Ω := ((B ⊗[F] A) ⧸ m)
  let i : B →+* Ω := algebraMap B Ω
  have hi : i.comp (algebraMap F B) = algebraMap F Ω := (IsScalarTower.algebraMap_eq F B Ω).symm
  have hx0 : AlgebraicIndependent F (fun q => i (w q)) :=
    hw.map' (f := IsScalarTower.toAlgHom F B Ω) (algebraMap B Ω).injective
  have hx : AlgebraicIndependent A (fun q => i (w q)) := hx0.extendScalars A
  have hn : 0 < Module.finrank i.fieldRange Ω := by
    rw [← Algebra.finrank_eq_of_equiv_equiv i.rangeRestrictFieldEquiv (RingEquiv.refl Ω) (RingHom.ext fun _ => rfl)]
    exact Module.finrank_pos
  have t1 := tower i (IntermediateField.adjoin F (Set.range w)).toSubfield
  rw [finrank_congr (map_adjoin i hi w)] at t1
  let P := FractionRing (MvPolynomial I A)
  let φ : P →+* Ω := (IntermediateField.adjoin A (Set.range fun q => i (w q))).val.toRingHom.comp hx.aevalEquivField.toRingEquiv.toRingHom
  letI : Algebra F P := ((algebraMap A P).comp (algebraMap F A)).toAlgebra
  have hφA : ∀ a, φ (algebraMap A P a) = algebraMap A Ω a := fun a => congrArg Subtype.val (hx.aevalEquivField.commutes a)
  have hφ : φ.comp (algebraMap F P) = algebraMap F Ω := RingHom.ext fun a =>
    (hφA _).trans (IsScalarTower.algebraMap_apply F A Ω a).symm
  have hX : (fun q => φ (algebraMap (MvPolynomial I A) P (MvPolynomial.X q))) = fun q => i (w q) := funext fun q =>
    (hx.aevalEquivField_algebraMap_apply_coe _).trans (MvPolynomial.aeval_X _ q)
  have hr : φ.fieldRange = (IntermediateField.adjoin A (Set.range fun q => i (w q))).toSubfield := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (hx.aevalEquivField y).2
    · intro hz
      exact ⟨hx.aevalEquivField.symm ⟨z, hz⟩, congrArg Subtype.val (hx.aevalEquivField.apply_symm_apply ⟨z, hz⟩)⟩
  have t2 := tower φ (IntermediateField.adjoin F (Set.range fun q => algebraMap (MvPolynomial I A) P (MvPolynomial.X q))).toSubfield
  rw [finrank_congr (map_adjoin φ hφ _), hX, finrank_congr hr] at t2
  have t3 := GlobalTheory.CompanionTheory.FieldDeg.finrank_fraction_over_adjoin_X_eq F A I rfl
  have key : d₂ * Module.finrank i.fieldRange Ω =
      e * Module.finrank (IntermediateField.adjoin A (Set.range fun q => i (w q))) Ω := by
    rw [← hB, ← hA, ← t3]
    exact t1.symm.trans t2
  refine ⟨Ω, inferInstance, inferInstance, i, _, _, hi.trans (IsScalarTower.algebraMap_eq F A Ω), hx, ?_, rfl, rfl, hn, ?_⟩
  · refine Nat.pos_of_ne_zero fun h => ?_
    rw [h, mul_zero] at key
    exact (Nat.mul_pos hd hn).ne' key
  · rw [mul_comm, key, mul_comm]

theorem adjoin_entries (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {S : Type} {r : S → ℕ}
    (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1) (h0 : ∀ s l m, l < m → u s l m = 0) :
    IntermediateField.adjoin k (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin k
        (Set.range fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ ?_)
  · rintro _ ⟨⟨s, l, m⟩, rfl⟩
    show u s l m ∈ _
    rcases lt_trichotomy l m with h | rfl | h
    · rw [h0 s l m h]; exact zero_mem _
    · rw [h1]; exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, ⟨(l, m), h⟩⟩, rfl⟩
  · rintro _ ⟨⟨s, lm, h⟩, rfl⟩
    exact ⟨⟨s, lm⟩, rfl⟩

end Join

theorem fieldJoin : FieldJoin := by
  intro Ω₀ Ω₁ Ω₂ _ _ _ _ _ S _ r u d₂ e ⟨h1, h0, hi, hd, hf⟩ he hA
  rw [Join.adjoin_entries Ω₀ u h1 h0] at hf
  obtain ⟨Ω, _, _, i, d, n, a1, a2, a3, a4, a5, a6, a7⟩ := Join.core Ω₀ Ω₁ Ω₂ _ d₂ e hi hd hf he hA
  have g1 : ∀ s m, (u s).map i m m = 1 := fun s m => by simp [h1]
  have g0 : ∀ s l m, l < m → (u s).map i l m = 0 := fun s l m h => by simp [h0 s l m h]
  refine ⟨Ω, inferInstance, inferInstance, i, d, n, a1, ⟨g1, g0, a2, a3, ?_⟩, a5, a6, a7⟩
  rw [Join.adjoin_entries Ω₁ (fun s => (u s).map i) g1 g0]
  exact a4

end SheetDecomposition
end
end

section

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem exists_root {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (s : CMType H ⊕ CMType H)
    (m : Fin (labelRk D s)) : ∃ ρ : CMType H × Fin (D.p + D.q), HodgeCpt.rootIdx D ρ = ⟨s, m⟩ ∧
      HodgeCpt.rootSgn D ρ * HodgeCpt.rootSgn D ρ = 1 ∧
      ∀ (K : Type) (x : CMType H × Fin (D.p + D.q) → K → ℤ), grDeg x s m = HodgeCpt.rootSgn D ρ • x ρ := by
  rcases s with τ | τ
  · have hm : (m : ℕ) < D.p := m.2
    refine ⟨(τ, ⟨m, by omega⟩), ?_, ?_, fun K x => ?_⟩
    · simp only [HodgeCpt.rootIdx, hm, dif_pos]
    · simp [HodgeCpt.rootSgn, hm]
    · simp [HodgeCpt.rootSgn, hm, grDeg]
  · have hm : (m : ℕ) < D.q := m.2
    have h : ¬ D.p + D.q - 1 - m < D.p := by omega
    refine ⟨(τ, ⟨D.p + D.q - 1 - m, by omega⟩), ?_, ?_, fun K x => ?_⟩
    · simp only [HodgeCpt.rootIdx, h, dif_neg, not_false_eq_true]
      congr 1
      exact Fin.ext (by show D.p + D.q - 1 - (D.p + D.q - 1 - m) = m; omega)
    · simp [HodgeCpt.rootSgn, h]
    · simp [HodgeCpt.rootSgn, h, grDeg]

theorem val_tens {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃) {ξ : Sp Ω ⟶ X}
    (q : Cpt ξ) (hR : ∀ a ∈ regAt ξ q, i a ∈ O) (Λ : Lat ξ Ω) {t M : Ω} (ε : ℤ) (ht : Λ.IsGenAt q t)
    (h : Lat.tens (fun _ : Unit => Λ) (fun _ => ε) q = Submodule.span (regAt ξ q) {M}) :
    O.valuation (i M) = O.valuation (i t) ^ ε := by
  refine le_antisymm (val_le_of_mem_span O i _ hR (S := {t | ∃ s : Unit → Ω, (∀ j, Λ.IsGenAt q (s j)) ∧ t = ∏ j, s j ^ ε}) ?_
    (show M ∈ Lat.tens (fun _ : Unit => Λ) (fun _ => ε) q from h ▸ Submodule.mem_span_singleton_self M)) ?_
  · rintro _ ⟨s, hs, rfl⟩
    simp [val_eq_of_span_eq O i _ hR ((hs ()).2.symm.trans ht.2)]
  · have : t ^ ε ∈ Submodule.span (regAt ξ q) {M} :=
      h ▸ Submodule.subset_span ⟨fun _ => t, fun _ => ht, by simp⟩
    simpa using val_le_of_mem_span O i _ hR (S := {M}) (γ := O.valuation (i M)) (by rintro _ rfl; rfl) this

theorem val_step {Ω Ω₃ K : Type} [Field Ω] [Field Ω₃] [Fintype K] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃) (w : K → Ω)
    (x : K → ℤ) {ε : ℤ} (hε : ε * ε = 1) {e t : Ω} (he : e ≠ 0)
    (h : O.valuation (i ((∏ a, w a ^ x a) • e)) = O.valuation (i t) ^ ε) :
    O.valuation (i (∏ a, w a ^ (ε • x) a)) = O.valuation (i t) * O.valuation (i (e ^ ε)⁻¹) := by
  have h3 := congrArg (· ^ ε) h
  simp only [← zpow_mul, hε, zpow_one] at h3
  have h4 : O.valuation (i e) ≠ 0 := by simpa using he
  rw [← h3, smul_eq_mul, map_mul, map_mul, mul_zpow, map_inv₀, map_inv₀, map_zpow₀, map_zpow₀,
    mul_inv_cancel_right₀ (zpow_ne_zero _ h4), ← map_zpow₀, ← map_zpow₀, ← Finset.prod_zpow]
  simp only [← zpow_mul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem rootLat_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type}
    [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} (Fl : 𝔐.Flag)
    (ρ : CMType H × Fin (D.p + D.q)) (s : CMType H ⊕ CMType H) (m : Fin (labelRk D s)) (h : HodgeCpt.rootIdx D ρ = ⟨s, m⟩) :
    Fl.rootLat ρ = Lat.tens (fun _ : Unit => (𝔐.V s).gr (Fl.b s) m) fun _ => HodgeCpt.rootSgn D ρ := by
  unfold HodgeCpt.Flag.rootLat
  generalize HodgeCpt.rootIdx D ρ = z at h
  subst h
  rfl

theorem fibLink : ChartVal → Centre → CoordLat → FibLink := by
  intro hCV hC hL E _ _ _ H D l Xo c Y S' Ω' _ K' _ J' _ y' 𝔐 Fl x e b u k _ _ Ω₃ _ _ i hRL hb _ _ hfl hk s m
  classical
  obtain ⟨A, hA, hind, -⟩ := hL E H D l Xo c Y S' Ω' K' J' y' 𝔐 Fl b hb
  have h₀ : LinearIndependent Ω' (Fl.b s) := by
    obtain ⟨_, _, -, -, -, h, -⟩ := Fl.generic
    exact h s
  obtain ⟨β, hβ, hV⟩ := flag_val 𝔐.fn i (fun m => Fl.j (b s m)) (Fl.b s) (u s) (hind s).1 h₀ (hfl s)
  choose ρ hρ hε hx using exists_root D s
  refine ⟨i ((∏ m' ∈ Finset.Iic m, β m') * ∏ m' ∈ Finset.Iic m, (e (ρ m') ^ HodgeCpt.rootSgn D (ρ m'))⁻¹),
    (map_ne_zero i).2 (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun m' _ => hβ m')
      (Finset.prod_ne_zero_iff.2 fun m' _ => inv_ne_zero (zpow_ne_zero _ (hRL _).1))), fun O hO => ?_⟩
  obtain ⟨q, -, hq, -, -⟩ := hC E H D l Xo c Y S' S' Ω' Ω' Ω₃ K' K' J' J' y' y' 𝔐 𝔐 i i O rfl
  have hch : ∀ p : ℕ, p.Prime → ¬ InFibre 𝔐.ξ p q := fun p hp hn => by
    have : CharZero Ω₃ := charZero_of_injective_algebraMap (algebraMap k Ω₃).injective
    have : CharZero Ω' := i.charZero
    have h0 : (p : Ω') ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    refine hn ⟨h0, natCast_mem _ _, hq.2 _ (natCast_mem _ _) h0 ?_⟩
    simpa using hO (p : k)⁻¹
  obtain ⟨ch, hc⟩ := 𝔐.tie.cover q
  have hy : ∀ a, y' ⟨a, ch a⟩ ≠ 0 := fun a => Finset.prod_ne_zero_iff.1 hc.1 a (Finset.mem_univ a)
  obtain ⟨U, hU, bb, hbf, hbq⟩ := Fl.sub s q trivial
  obtain ⟨hbi, hbs⟩ := hbq q trivial hU
  obtain ⟨t, ht, hv⟩ := hV O (regAt 𝔐.ξ q) (A s (𝔐.f q.1)) bb hq.1 (fun a => by
    obtain ⟨z, hz⟩ := hk a
    exact hz ▸ hO z) hbi hbf (hbs.symm.trans (hA q hch s))
  have hgen : ∀ m', ((𝔐.V s).gr (Fl.b s) m').IsGenAt q (t m') := fun m' => by
    have := gr_span h₀ hbi hbf (regAt 𝔐.ξ q) m' (ht m')
    rw [← hbs] at this
    exact this
  have hstep : ∀ m', O.valuation (i (∏ a, y' ⟨a, ch a⟩ ^ grDeg x s m' a)) =
      O.valuation (i (t m')) * O.valuation (i (e (ρ m') ^ HodgeCpt.rootSgn D (ρ m'))⁻¹) := fun m' => by
    have h1 := (hRL (ρ m')).2 q trivial ch hc
    have h2 : Fl.rootLat (ρ m') = Lat.tens (fun _ : Unit => (𝔐.V s).gr (Fl.b s) m') fun _ => HodgeCpt.rootSgn D (ρ m') :=
      rootLat_eq Fl (ρ m') s m' (hρ m')
    rw [h2] at h1
    rw [hx]
    exact val_step O i _ _ (hε m') (hRL _).1 (val_tens O i q hq.1 _ _ (hgen m') h1)
  have hm : (∏ a, y' ⟨a, ch a⟩ ^ stepDeg x s m a) = ∏ m' ∈ Finset.Iic m, ∏ a, y' ⟨a, ch a⟩ ^ grDeg x s m' a := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [stepDeg, Finset.sum_apply]
    induction Finset.Iic m using Finset.induction_on with
    | empty => simp
    | insert j S hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add₀ (hy a), ih]
  have hpl : vdeg O (plPt fun s => (u s).map i) (plDeg ⟨s, m⟩) = (Finset.univ.sup fun I : Fin (m + 1) → Fin (labelRk D s) =>
      O.valuation (Matrix.of fun a b : Fin (m + 1) => (u s).map i (I a) (Fin.castLE m.2 b)).det)⁻¹ := by
    rw [vdeg, Finset.prod_eq_single (⟨s, m⟩ : Σ s, Fin (labelRk D s)) (fun z _ hz => by simp [plDeg, hz]) (by simp)]
    simp only [plDeg, if_pos, zpow_neg, zpow_one]
    rfl
  have h5 := hv m
  have h6 : O.valuation (i (∏ m' ∈ Finset.Iic m, β m')) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero i).2 (Finset.prod_ne_zero_iff.2 fun m' _ => hβ m'))
  rw [hCV _ _ _ O i 𝔐.ξ q K' J' y' ch _ hq hc, hm, hpl, map_mul, map_mul, ← h5, mul_right_comm,
    mul_inv_cancel_right₀ (right_ne_zero_of_mul (h5 ▸ h6)), map_prod, map_prod, map_prod, map_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m' _ => hstep m'

end SheetDecomposition
end
end
