module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemPuncturedRingIffPowerSeriesPart
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Mathlib.RingTheory.Nullstellensatz
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.ZMod.Defs
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators Topology

namespace GlobalTheory.Ex.ArcForm

theorem hasSum_regroup {X : Type} (e : X → ℤ) (h0 : ∀ χ, 0 ≤ e χ) (hf : ∀ n : ℤ, {χ | e χ = n}.Finite)
    (a : X → ℂ) (u x : ℂ) (h : HasSum (fun χ => u ^ e χ * a χ) x) :
    HasSum (fun n : ℕ => (∑ᶠ (χ : X) (_ : e χ = n), a χ) * u ^ n) x := by
  have h1 := h.tsum_fiberwise fun χ => (e χ).toNat
  refine h1.congr_fun fun n => ?_
  have hs : (fun χ => (e χ).toNat) ⁻¹' {n} = ((hf n).toFinset : Set X) := by
    ext χ
    have := h0 χ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    omega
  rw [hs, Finset.tsum_subtype' (hf n).toFinset fun χ => u ^ e χ * a χ]
  have h2 : (∑ᶠ (χ : X) (_ : e χ = n), a χ) = ∑ χ ∈ (hf n).toFinset, a χ :=
    finsum_mem_eq_finite_toFinset_sum a (hf n)
  rw [h2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have : e χ = n := by simpa using hχ
  rw [this, zpow_natCast, mul_comm]

theorem finite_fibre {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ≠ 0)
    (y : N.X) (n : ℤ) : {χ : N.X | β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) = n}.Finite := by
  have h := GlobalTheory.ClassMin.finite_sublevel
    (GlobalTheory.ClassMin.realExtension_ofIntBilin_posDef β.symm β.pos) (((n + 1) * (2 * m ^ 2) : ℤ) / 2 : ℝ)
  have hinj : Function.Injective fun χ : N.X => y + m • χ := fun a b hab =>
    smul_right_injective N.X (Int.natCast_ne_zero.2 hm) (by
      simpa only [natCast_zsmul] using add_left_cancel hab)
  refine (h.preimage hinj.injOn).subset fun χ hχ => ?_
  have hχ' : β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) = n := hχ
  have hpos : (0 : ℤ) < 2 * m ^ 2 := by positivity
  have h2 := Int.lt_ediv_add_one_mul_self (β.be (y + m • χ) (y + m • χ)) hpos
  rw [hχ'] at h2
  simp only [Set.mem_preimage, Set.mem_setOf_eq, GlobalTheory.ClassMin.ofIntBilin_apply]
  have h3 : ((β.be (y + m • χ) (y + m • χ) : ℤ) : ℝ) ≤ (((n + 1) * (2 * m ^ 2) : ℤ) : ℝ) := by
    exact_mod_cast h2.le
  linarith

theorem exponent_nonneg {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (m : ℕ) (y : N.X) :
    0 ≤ β.be y y / (2 * m ^ 2) := by
  refine Int.ediv_nonneg ?_ (by positivity)
  by_cases h : y = 0
  · simp [h]
  · exact (β.pos y h).le

theorem hasSum_arcTx (N : NumD ℂ) {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ^ 2 ∣ k) (ho : Odd m)
    (p : N.QT (m ^ 2)) (u : ℂˣ) (h : Summable fun χ => ‖(N.twist β u).txT m (N.twQ β u hm p) χ‖) :
    HasSum (fun n => PowerSeries.coeff n (N.arcTx β.be m p) * (u : ℂ) ^ n)
      ((N.twist β u).tx m (N.twQ β u hm p)) := by
  have h1 : HasSum (fun χ : N.X => (N.twist β u).txT m (N.twQ β u hm p) χ)
      ((N.twist β u).tx m (N.twQ β u hm p)) := h.of_norm.hasSum
  have h2 := hasSum_regroup _ (fun χ => exponent_nonneg β m (p.1.1.toAdd + m • χ))
    (finite_fibre β ho.pos.ne' p.1.1.toAdd) (N.txT m p) u _ (h1.congr_fun fun χ => by
      rw [(GlobalTheory.Ex.twist_terms ℂ N k β u m hm ho p χ).1, Units.val_zpow_eq_zpow_val])
  simpa only [NumD.arcTx, PowerSeries.coeff_mk] using h2

theorem aeval_eq_zero {ι : Type} (f : ι → PowerSeries ℂ) (F : MvPolynomial ι ℂ) {ε : ℝ} (hε : 0 < ε)
    (v : ℂˣ → ι → ℂ) (hs : ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → ∀ i,
      HasSum (fun n => PowerSeries.coeff n (f i) * (u : ℂ) ^ n) (v u i))
    (hF : ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → MvPolynomial.eval (v u) F = 0) : MvPolynomial.aeval f F = 0 := by
  have hmem : ∀ i, f i ∈ GlobalTheory.Conv.discSeries ε := fun i u hu => by
    rcases eq_or_ne u 0 with rfl | h0
    · exact summable_of_ne_finset_zero (s := {0}) fun n hn => by
        simp [show n ≠ 0 by simpa using hn]
    · exact (hs (Units.mk0 u h0) hu i).summable
  set G : GlobalTheory.Conv.discSeries ε := MvPolynomial.aeval (fun i => (⟨f i, hmem i⟩ : GlobalTheory.Conv.discSeries ε)) F with hG
  have hGv : (G : PowerSeries ℂ) = MvPolynomial.aeval f F :=
    MvPolynomial.comp_aeval_apply _ (GlobalTheory.Conv.discSeries ε).val F
  rw [← hGv]
  refine GlobalTheory.Conv.eq_zero_of_frequently_sum_eq_zero (GlobalTheory.Conv.discSeries_le_convSeries hε G.2)
    (Filter.Eventually.frequently ?_)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) hε)] with u h0 hu
  have h0' : u ≠ 0 := h0
  have hu' : ‖u‖ < ε := by simpa using hu
  rw [← GlobalTheory.Conv.evalDisc_apply hu', hG, MvPolynomial.comp_aeval_apply, ← hF (Units.mk0 u h0') hu',
    MvPolynomial.aeval_eq_eval]
  congr 2
  funext i
  exact (hs (Units.mk0 u h0') hu' i).tsum_eq

theorem aeval_arcTx_eq_zero : ∀ (N : NumD ℂ) (k : ℕ) (β : N.Form k) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (ι : Type) (p : ι → N.QT (m ^ 2)) (F : MvPolynomial ι ℂ) (ε : ℝ), 0 < ε → (∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ i, Summable fun χ => ‖(N.twist β u).txT m (N.twQ β u hm (p i)) χ‖) ∧ MvPolynomial.eval (fun i => (N.twist β u).tx m (N.twQ β u hm (p i))) F = 0) → MvPolynomial.aeval (fun i => N.arcTx β.be m (p i)) F = 0 :=
  fun N _ β m hm ho _ p F _ hε h =>
    aeval_eq_zero _ F hε (fun u i => (N.twist β u).tx m (N.twQ β u hm (p i)))
      (fun u hu i => hasSum_arcTx N β hm ho (p i) u ((h u hu).1 i)) fun u hu => (h u hu).2

end GlobalTheory.Ex.ArcForm
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ConeClosed

theorem exists_homogenisation {k J : Type} [Field k] (i : J) (P : MvPolynomial J k) :
    ∃ (n : ℕ) (Q : MvPolynomial J k), ∀ w : J → k, w i ≠ 0 →
      MvPolynomial.eval w Q = w i ^ n * MvPolynomial.eval (fun j => w j / w i) P := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨0, MvPolynomial.C a, fun w _ => by simp⟩
  | add P P' h h' =>
    obtain ⟨n, Q, hQ⟩ := h
    obtain ⟨n', Q', hQ'⟩ := h'
    refine ⟨n + n', MvPolynomial.X i ^ n' * Q + MvPolynomial.X i ^ n * Q', fun w hw => ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, MvPolynomial.eval_X, hQ w hw, hQ' w hw]
    ring
  | mul_X P j h =>
    obtain ⟨n, Q, hQ⟩ := h
    refine ⟨n + 1, Q * MvPolynomial.X j, fun w hw => ?_⟩
    simp only [map_mul, MvPolynomial.eval_X, hQ w hw]
    field_simp
    ring

def constHom {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) : k →+* Γ(X, U) :=
  (p.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem exists_point {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {U : X.Opens}
    (hU : IsAffineOpen U) (φ : Γ(X, U) →+* k) (hφ : ∀ a, φ (constFn p U a) = a) :
    ∃ x : Sp k ⟶ X, x ≫ p = 𝟙 _ ∧ ⊤ ≤ x ⁻¹ᵁ U ∧ ∀ f, GlobalTheory.ZH.valR x U f = φ f := by
  let ψ : Γ(X, U) ⟶ CommRingCat.of k := CommRingCat.ofHom φ
  have hx := GlobalTheory.Points.le_preimage_specMap_fromSpec hU ψ
  have hv : ∀ f, ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (Spec.map ψ ≫ hU.fromSpec) U f = φ f := fun f => by
    rw [GlobalTheory.Points.valR_eq _ U hx, GlobalTheory.Points.valMap_specMap_fromSpec]
    rfl
  refine ⟨Spec.map ψ ≫ hU.fromSpec, ?_, hx, hv⟩
  rw [← Spec.map_preimage ((Spec.map ψ ≫ hU.fromSpec) ≫ p), ← Spec.map_id]
  congr 1
  ext a
  rw [← GlobalTheory.Points.valR_constFn p _ U hx, hv, hφ]
  rfl

theorem valR_eval₂ {k J : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {U : X.Opens}
    (x : Sp k ⟶ X) (hp : x ≫ p = 𝟙 _) (hx : ⊤ ≤ x ⁻¹ᵁ U) (r : J → Γ(X, U)) (P : MvPolynomial J k) :
    GlobalTheory.ZH.valR x U (MvPolynomial.eval₂Hom (constHom p U) r P) =
      MvPolynomial.eval (fun j => GlobalTheory.ZH.valR x U (r j)) P := by
  have e : (CrdCalc.valHom x U hx).comp (MvPolynomial.eval₂Hom (constHom p U) r) =
      MvPolynomial.eval (fun j => GlobalTheory.ZH.valR x U (r j)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C, ← CrdCalc.valR_eq]
      exact GlobalTheory.Points.valR_constFn_of_section p x hp U hx a
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X, ← CrdCalc.valR_eq]
  rw [CrdCalc.valR_eq x U hx, ← e]
  rfl

theorem mem_cone_of_vanishing : (∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) [Fintype J] (s : J → H.Sec) (J₀ : Set J), H.IsLB → ImmBy p H s J₀ → ∀ v : J → k, (∃ i ∈ J₀, v i ≠ 0) → (∀ Pf ∈ MvPolynomial.vanishingIdeal k (cone p H s), MvPolynomial.eval v Pf = 0) → v ∈ cone p H s) := by
  intro k _ _ X p H J _ s J₀ hH him v ⟨i, hi, hvi⟩ hv
  obtain ⟨hU, r, hr, hgen⟩ := him.2 i hi
  let Φ : MvPolynomial J k →+* Γ(X, (Out.nonzeroLocus (s i))) := MvPolynomial.eval₂Hom (constHom p (Out.nonzeroLocus (s i))) r
  have hsurj : Function.Surjective Φ := by
    rw [← RingHom.range_eq_top, eq_top_iff, ← hgen, Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
    · exact ⟨MvPolynomial.X j, MvPolynomial.eval₂Hom_X' _ _ _⟩
  have hker : RingHom.ker Φ ≤ RingHom.ker (MvPolynomial.eval fun j => v j / v i) := by
    intro P hP
    obtain ⟨n, Q, hQ⟩ := exists_homogenisation i P
    have hmem : MvPolynomial.X i * Q ∈ MvPolynomial.vanishingIdeal k (cone p H s) := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      rintro w ⟨x, hp, hw⟩
      rw [MvPolynomial.aeval_eq_eval, map_mul, MvPolynomial.eval_X]
      by_cases hwi : w i = 0
      · rw [hwi, zero_mul]
      have hx : ⊤ ≤ x ⁻¹ᵁ (Out.nonzeroLocus (s i)) := (CrdCalc.crd_isUnit_iff i hw).1 (Ne.isUnit hwi)
      have e : (fun j => w j / w i) = fun j => GlobalTheory.ZH.valR x (Out.nonzeroLocus (s i)) (r j) := funext fun j => by
        rw [CrdCalc.crd_ratio hw (hr j) hx, mul_div_cancel_right₀ _ hwi]
      rw [hQ w hwi, e, ← valR_eval₂ p x hp hx r P, RingHom.mem_ker.1 hP, CrdCalc.valR_eq x (Out.nonzeroLocus (s i)) hx, map_zero,
        mul_zero, mul_zero]
    have h := hv _ hmem
    rw [map_mul, MvPolynomial.eval_X, hQ v hvi] at h
    exact (mul_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hvi)).resolve_left (pow_ne_zero _ hvi)
  let φ : Γ(X, (Out.nonzeroLocus (s i))) →+* k := Φ.liftOfSurjective hsurj ⟨_, hker⟩
  have hφ : ∀ P, φ (Φ P) = MvPolynomial.eval (fun j => v j / v i) P := fun P =>
    RingHom.liftOfSurjective_comp_apply Φ hsurj ⟨_, hker⟩ P
  obtain ⟨x, hp, hx, hval⟩ := exists_point p hU φ fun a => by
    have := hφ (MvPolynomial.C a)
    rwa [MvPolynomial.eval_C, show Φ (MvPolynomial.C a) = constFn p (Out.nonzeroLocus (s i)) a from
      MvPolynomial.eval₂Hom_C _ _ _] at this
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists hH s x
  have hwi : w i ≠ 0 := ((CrdCalc.crd_isUnit_iff i hw).2 hx).ne_zero
  refine ⟨x, hp, ?_⟩
  have h := CrdCalc.crd_smul (Units.mk0 (v i / w i) (div_ne_zero hvi hwi)) hw
  convert h using 2 with j
  have h₁ := hφ (MvPolynomial.X j)
  rw [MvPolynomial.eval_X, show Φ (MvPolynomial.X j) = r j from MvPolynomial.eval₂Hom_X' _ _ _] at h₁
  rw [CrdCalc.crd_ratio hw (hr j) hx, hval, h₁, Units.val_mk0]
  field_simp

end GlobalTheory.ZH.ConeClosed
end
end

section

open GlobalTheory.UT

namespace GlobalTheory.TestFibre

theorem exists_val_le_of_sumV_characters : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X T : Type) [Fintype T] (χ : T → X → F) (cf : X → F) (ζ w : T → F) (α : X) (q : ℚ), (∀ t, SumV v (fun β => χ t β * cf β) (ζ t * w t)) → (∀ t, v (ζ t) = 0) → (∀ t β, v (χ t β) = 0) → v ((Fintype.card T : ℕ) : F) = 0 → v (cf α) = (q : WithTop ℚ) → (∀ β, β ≠ α → ∑ t, (χ t α)⁻¹ * χ t β = 0 ∨ (q : WithTop ℚ) < v (cf β)) → ∃ t, v (w t) ≤ (q : WithTop ℚ) := by
  classical
  intro F _ v X T _ χ cf ζ w α q hS hζ hχ hT hα hβ
  by_contra hcon
  have hw : ∀ t, (q : WithTop ℚ) < v (w t) := fun t => lt_of_not_ge fun h => hcon ⟨t, h⟩
  have hq : (q : WithTop ℚ) ≠ ⊤ := WithTop.coe_ne_top
  have hne : ∀ t, χ t α ≠ 0 := fun t h => by
    have h1 := hχ t α
    rw [h, v.map_zero] at h1
    exact WithTop.top_ne_zero h1
  have hinv : ∀ t, v (χ t α)⁻¹ = 0 := fun t => by
    have h1 : v ((χ t α)⁻¹ * χ t α) = 0 := by rw [inv_mul_cancel₀ (hne t), v.map_one]
    rwa [v.map_mul, hχ t α, add_zero] at h1
  choose S hS' using fun t => hS t (q + 1)
  set U : Finset X := insert α (Finset.univ.biUnion S) with hU
  have hαU : α ∈ U := Finset.mem_insert_self _ _
  have hSU : ∀ t, S t ⊆ U := fun t x hx =>
    Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨t, Finset.mem_univ _, hx⟩)
  have hq1 : (q : WithTop ℚ) < ((q + 1 : ℚ) : WithTop ℚ) := WithTop.coe_lt_coe.2 (by linarith)
  have hA : (q : WithTop ℚ) < v (∑ t, (χ t α)⁻¹ * (ζ t * w t)) :=
    v.map_lt_sum hq fun t _ => by
      rw [v.map_mul, v.map_mul, hinv, hζ, zero_add, zero_add]; exact hw t
  have hB : (q : WithTop ℚ) < v (∑ t, (χ t α)⁻¹ * (ζ t * w t - ∑ β ∈ U, χ t β * cf β)) :=
    v.map_lt_sum hq fun t _ => by
      rw [v.map_mul, hinv, zero_add]; exact hq1.trans_le (hS' t U (hSU t))
  have hC : (q : WithTop ℚ) < v (∑ β ∈ U.erase α, (∑ t, (χ t α)⁻¹ * χ t β) * cf β) :=
    v.map_lt_sum hq fun β hb => by
      rcases hβ β (Finset.ne_of_mem_erase hb) with h | h
      · rw [h, zero_mul, v.map_zero]; exact WithTop.coe_lt_top q
      · rw [v.map_mul]
        have h0 : (0 : WithTop ℚ) ≤ v (∑ t, (χ t α)⁻¹ * χ t β) :=
          v.map_le_sum fun t _ => by rw [v.map_mul, hinv, hχ, add_zero]
        exact h.trans_le (le_add_of_nonneg_left h0)
  have e1 : ∑ t, (χ t α)⁻¹ * χ t α = ((Fintype.card T : ℕ) : F) := by
    rw [Finset.sum_congr rfl fun t _ => inv_mul_cancel₀ (hne t)]
    simp
  have e2 : ∑ t, (χ t α)⁻¹ * (∑ β ∈ U, χ t β * cf β) = ∑ β ∈ U, (∑ t, (χ t α)⁻¹ * χ t β) * cf β := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  have e : ((Fintype.card T : ℕ) : F) * cf α =
      (∑ t, (χ t α)⁻¹ * (ζ t * w t)) +
        (-(∑ t, (χ t α)⁻¹ * (ζ t * w t - ∑ β ∈ U, χ t β * cf β)) +
          -(∑ β ∈ U.erase α, (∑ t, (χ t α)⁻¹ * χ t β) * cf β)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [e2, ← Finset.add_sum_erase U _ hαU, e1]
    ring
  have hfin : (q : WithTop ℚ) < v (((Fintype.card T : ℕ) : F) * cf α) := by
    rw [e]
    exact v.map_lt_add hA (v.map_lt_add (by rwa [v.map_neg]) (by rwa [v.map_neg]))
  rw [v.map_mul, hT, zero_add, hα] at hfin
  exact lt_irrefl _ hfin

end GlobalTheory.TestFibre
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaReal

def UnivBasis {S : Scheme.{0}} (P : PolAV S) (n : ℤ) {T₀ : Over S} {κ : Type} (b : κ → SecM P.A P.L n T₀) : Prop :=
  ∀ (T : Over S) [IsAffine T.left] (h : T ⟶ T₀), ∃ c : Module.Basis κ Γ(T.left, ⊤) (SecM P.A P.L n T),
    ∀ i, c i = VVRank.pullM P.A P.L n h (b i)

theorem exists_univBasis (h : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) (n : ℕ) (hn : 1 ≤ n) (p : S) :
    ∃ V : S.Opens, p ∈ V ∧ ∃ b : Fin (n ^ P.g) → SecM P.A P.L n (overRes (T := baseOver S) V), UnivBasis P n b := by
  obtain ⟨V, hV, b, hb⟩ := h S P n hn p
  exact ⟨V, hV, fun i => SecM.ofSec P.A (b i), fun T _ h => VVRank.exists_basis P n b hb T h⟩

end GlobalTheory.ThetaReal
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

namespace GlobalTheory.ZH.UFib

theorem gm_charUnit_zero {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X)
    (z : Z.left) : gm τ.left z ⊤ (charUnit S X 0) = 1 := by
  have a : splitTorusPointsEquiv S X Z τ (Multiplicative.ofAdd 0) = pullU τ.left ⊤ (charUnit S X 0) :=
    Units.ext (splitTorusPointsEquiv_val S X Z τ 0)
  have b : pullU τ.left ⊤ (charUnit S X 0) = 1 := a.symm.trans (map_one _)
  have c := gm_pull (𝟙 Z.left) τ.left z ⊤ trivial (charUnit S X 0)
  rw [b, map_one, Category.id_comp] at c
  exact c.symm

theorem gs_id_appLE {X Z : Scheme.{0}} (r : Z ⟶ X) (U : X.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (z : Z) (f : Γ(X, U)) :
    gs (𝟙 Z) z ⊤ ((r.appLE U ⊤ h).hom f) = gs r z U f := by
  have e := gs_pull (𝟙 Z) r z U (h trivial) f
  rw [Category.id_comp] at e
  exact (gs_res (𝟙 Z) z h trivial _).trans e

theorem exists_app_eq_of_hasWt_zero : ∀ (k : Type) [Field k] [IsAlgClosed k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] (D : E.GtDatum G) (W : E.B.left.Opens) (f : Γ(G.left, D.q.left ⁻¹ᵁ W)), UFib.HasWt D.i (D.q.left ⁻¹ᵁ W) f 0 → ∃ a : Γ(E.B.left, W), (D.q.left.app W).hom a = f := by
  intro k _ _ E G _ D W f hf
  have := D.q_affine
  refine (invariant_functions_descend _ G E.B _ D.q D.i D.q_hom D.i_hom D.q_flat D.q_surjective inferInstance
    D.isKernel W).2.2 f fun Z t g h₁ h₂ => fn_ext fun z _ => ?_
  rw [gs_id_appLE, gs_id_appLE, hf Z t g z (h₂ trivial), gm_charUnit_zero, Units.val_one, _root_.one_mul]

end GlobalTheory.ZH.UFib
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gs_linSum {Y Z : Scheme.{0}} {R : Type} [CommRing R] (p : Y ⟶ Sp R) {I : Type} [Fintype I] (a : I → R)
    (r : Z ⟶ Y) (z : Z) (W : Y.Opens) (hm : r z ∈ W) (f : I → Γ(Y, W)) :
    gs r z W (∑ i, constFn p W (a i) * f i) = ∑ i, cst (r ≫ p) z (a i) * gs r z W (f i) := by
  have e : ∀ (b : I → Γ(Y, W)), gs r z _ (∑ i, b i) = ∑ i, gs r z _ (b i) := fun b => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gs_eq r z _ hm, map_sum]
  rw [e]
  exact Finset.sum_congr rfl fun i _ => (gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_constFn p _ r z hm _) rfl)

theorem isLin_iff_of_red : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → ∀ (I : Type) [Fintype I] (b : I → LB.Sec (LB.LinComb L ψ ε)) (φ : I → (Φ.H 1).Sec) (b₀ : LB.Sec (LB.LinComb L ψ ε)) (φ₀ : (Φ.H 1).Sec) (a : I → k), (∀ i, UFib.Red Φ c t (b i) (φ i)) → UFib.Red Φ c t b₀ φ₀ → (IsLin Φ.E.B.hom b a b₀ ↔ IsLin Φ.G.hom φ a φ₀) := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t _ I _ b φ b₀ φ₀ a hb hb₀
  have pick : ∀ (y : Φ.G.left) (l : Φ.N₀.ι), y ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l →
      ∃ J, Good L y J ∧ J (𝟙 _ ≫ Φ.D.q.left ≫ π) = c.idx l := fun y l hy => by
    obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun _ : PUnit => 𝟙 _ ≫ Φ.D.q.left ≫ π) (fun _ => c.idx l)
      (fun _ _ _ => rfl) (fun _ => c.le l hy)
    exact ⟨J, hJ, e PUnit.unit⟩
  have hw : (𝟙 _ ≫ Φ.D.q.left) ≫ Φ.E.B.hom = 𝟙 _ ≫ Φ.G.hom := by
    rw [Category.assoc, Over.w]
  constructor
  · intro h l
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, e⟩ := pick y l hy
    refine (hb₀ _ (𝟙 _) y J hJ l hy e).trans (Eq.trans ?_ (gs_linSum Φ.G.hom a (𝟙 _) y _ hy _).symm)
    have m := hJ.mem ψ (𝟙 _ ≫ Φ.D.q.left)
    have e₁ : sval b₀ (𝟙 _ ≫ Φ.D.q.left) y J =
        ∑ i, cst (𝟙 _ ≫ Φ.G.hom) y (a i) * sval (b i) (𝟙 _ ≫ Φ.D.q.left) y J := by
      rw [← hw]
      exact (congrArg (gs _ y _) (h _)).trans (gs_linSum Φ.E.B.hom a _ y _ m _)
    rw [e₁, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (mul_assoc _ _ _).trans (congrArg _ (hb i _ (𝟙 _) y J hJ l hy e).symm)
  · intro h j
    have := Φ.D.q_flat
    have := Φ.D.q_surjective
    apply GlobalTheory.FunDescent.app_injective Φ.D.q.left
    refine fn_ext fun y hy => ?_
    refine (gs_pull (𝟙 _) Φ.D.q.left y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) Φ.D.q.left y _ hy _).symm)
    refine Eq.trans ?_ (gs_linSum Φ.E.B.hom a (𝟙 _ ≫ Φ.D.q.left) y _ hy _).symm
    obtain ⟨l, hl⟩ := exists_chart Φ.isLB (Φ.D.q.left y)
    obtain ⟨J, hJ, e⟩ := pick y l hl
    have m := hJ.mem ψ (𝟙 _ ≫ Φ.D.q.left)
    have e₁ : sval b₀ (𝟙 _ ≫ Φ.D.q.left) y J =
        ∑ i, cst (𝟙 _ ≫ Φ.G.hom) y (a i) * sval (b i) (𝟙 _ ≫ Φ.D.q.left) y J := by
      refine (Units.mul_left_inj (val t (𝟙 _) y J)).1 ?_
      refine (hb₀ _ (𝟙 _) y J hJ l hl e).symm.trans ((congrArg (gs _ y _) (h l)).trans
        ((gs_linSum Φ.G.hom a (𝟙 _) y _ hl _).trans ?_))
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact (congrArg _ (hb i _ (𝟙 _) y J hJ l hl e)).trans (mul_assoc _ _ _).symm
    refine (sec_trans b₀ (𝟙 _ ≫ Φ.D.q.left) y (j := j) hy m).trans ((congrArg _ e₁).trans ?_)
    rw [Finset.mul_sum, hw]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (mul_left_comm _ _ _).trans (congrArg _ (sec_trans (b i) (𝟙 _ ≫ Φ.D.q.left) y (j := j) hy m).symm)

end GlobalTheory.ZH.UFib
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

theorem _root_.GlobalTheory.T.closure_zmodPow_eq_top_of_meets_torsion_cosets : ∀ (κ : Type) (n J M : ℕ), 1 ≤ n → 2 ≤ J → M = n ^ J → ∀ X : Set (κ → ZMod M), (∀ a : κ → ZMod M, ∃ y : κ → ZMod M, n • y = 0 ∧ a + y ∈ X) → AddSubgroup.closure X = ⊤ := by
  first | exact @GlobalTheory.ThetaReal.closure_eq_top_of_meets_torsion_cosets | exact GlobalTheory.ThetaReal.closure_eq_top_of_meets_torsion_cosets | (intros; apply GlobalTheory.ThetaReal.closure_eq_top_of_meets_torsion_cosets <;> assumption)
end
