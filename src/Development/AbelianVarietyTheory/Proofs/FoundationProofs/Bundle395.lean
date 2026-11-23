module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle393
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle045
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle027
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsQuotientMapToGSProd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle355
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle363
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle360
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle371
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle352
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle359
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle012

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.Ord2.localDuality_char : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (k k' a b : G ℚ Ω → Qbar l), OverL l A → ContinuousOn k (Dec (F := ℚ) A) → ContinuousOn k' (Dec (F := ℚ) A) → ContinuousOn a (Dec (F := ℚ) A) → ContinuousOn b (Dec (F := ℚ) A) → (∀ s ∈ Dec (F := ℚ) A, k s ∈ c.O ∧ k' s ∈ c.O ∧ a s ∈ c.O ∧ b s ∈ c.O ∧ k s * k' s = eps l s) → (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, k (s * t) = k s * k t ∧ k' (s * t) = k' s * k' t ∧ b (s * t) = b s + k s * b t ∧ a (s * t) = a s + k' s * a t) → (∃ s ∈ Dec (F := ℚ) A, k s ≠ 1) → (∃ s ∈ Dec (F := ℚ) A, k' s ≠ 1) → (∀ n : ℕ, Cob2 c n (Dec (F := ℚ) A) (fun s t => b s * (k' s * a t))) → (∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, b s = k s * x - x) ∨ ∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, a s = k' s * x - x := by
  intro hL l _ Ω _ _ _ c A k k' a b hA hk hk' ha hb hint hmul hk1 hk'1 hcob
  by_cases hac : ∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, a s = k' s * x - x
  · exact Or.inr hac
  left
  obtain ⟨θ, hθc, hθ⟩ := GlobalTheory.T.exists_unitCharacter_of_integral_cyclotomic_product l Ω c A k k' hk
    (fun s hs => ⟨(hint s hs).1, (hint s hs).2.1, (hint s hs).2.2.2.2⟩) (fun s hs t ht => (hmul s hs t ht).1)
  obtain ⟨θ', hθ'c, hθ'⟩ := GlobalTheory.T.exists_unitCharacter_of_integral_cyclotomic_product l Ω c A k' k hk'
    (fun s hs => ⟨(hint s hs).2.1, (hint s hs).1, by rw [mul_comm]; exact (hint s hs).2.2.2.2⟩)
    (fun s hs t ht => (hmul s hs t ht).2.1)
  have hN := GlobalTheory.T.norm_le_pow_iff_dvd l c
  have hchi : ∀ s : G ℚ Ω, ((((UpperTheory.V.Base.chiO ℚ Ω l c.O) s : c.Oˣ) : c.O) : Qbar l) = eps l s := by
    intro s; rfl
  have hcyc : θ * θ' = (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype := by
    refine MonoidHom.ext fun g => Units.ext (Subtype.ext ?_)
    simp only [MonoidHom.mul_apply, Units.val_mul, Subalgebra.coe_mul, hθ, hθ', MonoidHom.comp_apply,
      Subgroup.coe_subtype, hchi]
    exact (hint g g.2).2.2.2.2
  have hθ1 : ∃ g, θ g ≠ 1 := by
    obtain ⟨s, hs, hne⟩ := hk1
    exact ⟨⟨s, hs⟩, fun h => hne (by have e := hθ ⟨s, hs⟩; rw [h] at e; exact e.symm.trans rfl)⟩
  have hθ'1 : ∃ g, θ' g ≠ 1 := by
    obtain ⟨s, hs, hne⟩ := hk'1
    exact ⟨⟨s, hs⟩, fun h => hne (by have e := hθ' ⟨s, hs⟩; rw [h] at e; exact e.symm.trans rfl)⟩
  have hθ'ne : ∃ g, θ' g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g := by
    obtain ⟨s, hs, hne⟩ := hk1
    refine ⟨⟨s, hs⟩, fun h => hne ?_⟩
    have e := DFunLike.congr_fun hcyc ⟨s, hs⟩
    rw [MonoidHom.mul_apply, ← h] at e
    have e1 : θ ⟨s, hs⟩ = 1 := mul_eq_right.1 e
    have e2 := hθ ⟨s, hs⟩; rw [e1] at e2; exact e2.symm.trans rfl
  set p : c.O := ((l : ℕ) : c.O) with hp
  let aO : ↥(Dec (F := ℚ) A) → c.O := fun s => ⟨a s, (hint s.1 s.2).2.2.1⟩
  let bO : ↥(Dec (F := ℚ) A) → c.O := fun s => ⟨b s, (hint s.1 s.2).2.2.2.1⟩
  have haO : Continuous aO := (continuousOn_iff_continuous_domRestrict.1 ha).subtype_mk _
  have hbO : Continuous bO := (continuousOn_iff_continuous_domRestrict.1 hb).subtype_mk _
  have haOc : ∀ s t, aO (s * t) = aO s + ((θ' s : c.Oˣ) : c.O) * aO t := fun s t => Subtype.ext (by
    simp only [aO, Subalgebra.coe_add, Subalgebra.coe_mul, hθ']
    exact (hmul s.1 s.2 t.1 t.2).2.2.2)
  have hbOc : ∀ s t, bO (s * t) = bO s + ((θ s : c.Oˣ) : c.O) * bO t := fun s t => Subtype.ext (by
    simp only [bO, Subalgebra.coe_add, Subalgebra.coe_mul, hθ]
    exact (hmul s.1 s.2 t.1 t.2).2.2.1)
  have hnorm1 : ∀ x : c.O, ‖((x : c.O) : Qbar l)‖ ≤ 1 := fun x => by
    have := (hN 0 x).2 (by simp); simpa using this
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_annihilatorDepth_of_not_coboundary l (Set.univ : Set ↥(Dec (F := ℚ) A)) (fun s => k' s) (fun s => a s)
    (by obtain ⟨s, hs, hne⟩ := hk'1; exact ⟨⟨s, hs⟩, trivial, hne⟩)
    (fun ⟨X, hX⟩ => hac ⟨X, fun s hs => hX ⟨s, hs⟩ trivial⟩)
  have hann : ∀ n : ℕ, ∀ x y : c.O, (∀ s, p ^ n ∣ x * aO s - (((θ' s : c.Oˣ) : c.O) * y - y)) → p ^ (n - r) ∣ x := by
    intro n x y h
    refine (hN (n - r) x).1 (hr n x y (hnorm1 x) fun s _ => ?_)
    have := (hN n _).2 (h s)
    simpa [aO, hθ'] using this
  obtain ⟨m, hm0, hAF⟩ := GlobalTheory.T.exists_mul_scalarClass_eq_smul_add_coboundary_modPrimePow hL.lf hL.lt hL.le l Ω c A hA θ' hθ'c hθ'1 hθ'ne r
  have key : ∀ n : ℕ, 1 ≤ n → ∃ x : c.O, ∀ s, p ^ n ∣ (m : c.O) * bO s - (((θ s : c.Oˣ) : c.O) * x - x) := by
    intro n hn
    refine GlobalTheory.T.coboundary_of_orthogonal_dualCharacter_modPrimePow hL.lf hL.lt l Ω c A hA θ θ' hθc hθ'c hcyc n hn (fun s => (m : c.O) * bO s)
      (continuous_const.mul hbO) (fun s t => ?_) (fun a' ha' hca' => ?_)
    · rw [hbOc s t]; ring_nf; exact dvd_zero _
    obtain ⟨x, y, hxy⟩ := hAF n hn aO haO (fun s t => by rw [haOc s t, sub_self]; exact dvd_zero _)
      (hann n) a' ha' hca'
    obtain ⟨u, huc, huO, hu⟩ := hcob n
    let u0 : ↥(Dec (F := ℚ) A) → c.O := fun s => ⟨u s, huO s⟩
    have hu0c : Continuous u0 := (continuousOn_iff_continuous_domRestrict.1 huc).subtype_mk _
    have hu0 : ∀ s t, p ^ n ∣ bO s * (((θ' s : c.Oˣ) : c.O) * aO t) -
        ((((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O)) * u0 t - u0 (s * t) + u0 s) := by
      intro s t
      refine (hN n _).1 ?_
      have e : ‖b s.1 * (k' s.1 * a t.1) - (eps l s.1 * u t.1 - u (s.1 * t.1) + u s.1)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ :=
        hu s.1 s.2 t.1 t.2
      have he : k s.1 * k' s.1 = eps l s.1 := (hint s.1 s.2).2.2.2.2
      rw [← he] at e
      convert e using 2
      simp only [aO, bO, u0, Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul, hθ, hθ']
      rfl
    have hbt : Continuous (fun s => bO s * ((θ' s : c.Oˣ) : c.O)) := hbO.mul hθ'c
    have hcu : Continuous (fun s => x * u0 s - bO s * ((θ' s : c.Oˣ) : c.O) * y) :=
      (continuous_const.mul hu0c).sub (hbt.mul continuous_const)
    refine ⟨fun s => x * u0 s - bO s * ((θ' s : c.Oˣ) : c.O) * y, hcu, fun s t => ?_⟩
    obtain ⟨q1, hq1⟩ := hxy t
    obtain ⟨q2, hq2⟩ := hu0 s t
    refine ⟨bO s * ((θ' s : c.Oˣ) : c.O) * q1 + x * q2, ?_⟩
    simp only []
    rw [hbOc s t, map_mul θ' s t, Units.val_mul]
    linear_combination (bO s * ((θ' s : c.Oˣ) : c.O)) * hq1 + x * hq2
  obtain ⟨s0, hs0, hne0⟩ := hk1
  refine GlobalTheory.T.coboundary_of_uniform_limit_coboundaries (Dec (F := ℚ) A : Set (G ℚ Ω)) k b ⟨s0, hs0, hne0⟩ fun ε hε => ?_
  have hl1 : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
    rw [e, norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hm : (0 : ℝ) < ‖((m : ℕ) : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hm0.ne')
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (mul_pos hε hm) hl1
  obtain ⟨x, hx⟩ := key (n + 1) (Nat.le_add_left 1 n)
  refine ⟨(x : Qbar l) / (m : Qbar l), fun s hs => ?_⟩
  have e := (hN (n + 1) _).2 (hx ⟨s, hs⟩)
  have e2 : ((((m : c.O) * bO ⟨s, hs⟩ - (((θ ⟨s, hs⟩ : c.Oˣ) : c.O) * x - x) : c.O)) : Qbar l) =
      (m : Qbar l) * (b s - (k s * ((x : Qbar l) / (m : Qbar l)) - (x : Qbar l) / (m : Qbar l))) := by
    have hm' : (m : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hm0.ne'
    have hb' : ((bO ⟨s, hs⟩ : c.O) : Qbar l) = b s := rfl
    have hk'' : (((θ ⟨s, hs⟩ : c.Oˣ) : c.O) : Qbar l) = k s := hθ _
    push_cast [hb', hk'']
    field_simp
  rw [e2, norm_mul] at e
  have e3 : ‖((l : ℕ) : Qbar l) ^ (n + 1)‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ n := by
    rw [norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hl1.le (Nat.le_succ n)
  rw [← le_div_iff₀' hm] at e
  refine e.trans ?_
  rw [div_le_iff₀ hm]
  linarith
end

section

noncomputable section

namespace GlobalTheory.FlatLine.Definite

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_bc {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) : ∃ z, FrMap φ y z :=
  GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c S T φ y

theorem frMap_of_comp {R S T : Type} [CommRing R] [Algebra c.F R] [CommRing S] [Algebra c.F S] [CommRing T]
    [Algebra c.F T] {φ : R →ₐ[c.F] S} {ψ : S →ₐ[c.F] T} {χ : R →ₐ[c.F] T} (h : ψ.comp φ = χ) {y : FrPt Xo c R}
    {z : FrPt Xo c S} {w : FrPt Xo c T} (hz : FrMap φ y z) (hw : FrMap χ y w) : FrMap ψ z w := by
  obtain ⟨w', hw'⟩ := exists_bc ψ z
  rwa [(frMap_unique_refl_iff E H Dw l Xo c R T χ y).1 w w' hw (h ▸ ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hz hw')]

abbrev idemAt (Z : Comp Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : S :=
  CompSplitPfB.cspB_idem _ (CompSplitPfB.cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z) y.x y.x_over

theorem idemAt_eq_one_iff (Z : Comp Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    idemAt Z y = 1 ↔ LiesOn Z y := by
  refine ⟨fun h q => (CompSplitPfB.cspB_idem_spec _
    (CompSplitPfB.cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z) y.x y.x_over q).1 ?_, fun h => ?_⟩
  · show idemAt Z y ∉ _
    rw [h]
    exact (Ideal.ne_top_iff_one _).1 q.isPrime.ne_top
  · refine CompSplitPfB.cspB_idem_eq_of (CompSplitPfB.cspB_idem_idem _ _ _ _) IsIdempotentElem.one fun q => ?_
    rw [CompSplitPfB.cspB_idem_spec]
    exact iff_of_true (h q) ((Ideal.ne_top_iff_one _).1 q.isPrime.ne_top)

def IsCoef (Z : Comp Xo c) (y₀ : FrPt Xo c c.F) (τ : E →+* ℂ) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (s : S) : Prop :=
  idemAt Z y * s = s ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (w z : FrPt Xo c T)
    (g : (∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) T)) (a : T),
    FrMap φ y w → FrMap (Algebra.ofId c.F T) y₀ z → FrChg g a w z → φ s = (g τ).det

theorem eq_of_mk_eq {S : Type} [CommRing S] {e s t : S} (he : IsIdempotentElem e) (hs : e * s = s) (ht : e * t = t)
    (h : Ideal.Quotient.mk (Ideal.span {1 - e}) s = Ideal.Quotient.mk (Ideal.span {1 - e}) t) : s = t := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
  have := he.eq
  linear_combination ht - hs - e * hb - b * this

theorem exists_isCoef {Z : Comp Xo c} {y₀ : FrPt Xo c c.F} (h₀ : LiesOn Z y₀)
    (hy₀ : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y →
      y.x = spMap (algebraMap c.F S) ≫ y₀.x) (τ : E →+* ℂ) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) : ∃ s s' : S, IsCoef Z y₀ τ y s ∧ (∀ t, IsCoef Z y₀ τ y t → t = s) ∧
      idemAt Z y * s' = s' ∧ s * s' = idemAt Z y := by
  have he : IsIdempotentElem (idemAt Z y) := CompSplitPfB.cspB_idem_idem _ _ _ _
  let π := Ideal.Quotient.mkₐ c.F (Ideal.span {1 - idemAt Z y})
  have hπ : π (idemAt Z y) = 1 := by
    rw [← map_one π]
    exact (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self _)).symm
  obtain ⟨w, hw⟩ := exists_bc π y
  obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F (S ⧸ Ideal.span {1 - idemAt Z y})) y₀
  have hwZ : LiesOn Z w := (idemAt_eq_one_iff Z w).1
    ((CompSplitPfB.cspB_idem_map _ _ π y.x_over w.x_over hw.1).symm.trans hπ)
  obtain ⟨g, a, hg, hc⟩ := (frChg_exists_unique E H Dw l Xo c _ w z).1 (hz.1.trans (hy₀ _ w hwZ).symm)
  obtain ⟨d', hd'⟩ := (hg τ).exists_right_inv
  obtain ⟨s, hs⟩ := Ideal.Quotient.mkₐ_surjective c.F _ (g τ).det
  obtain ⟨s', hs'⟩ := Ideal.Quotient.mkₐ_surjective c.F _ d'
  have k : ∀ t, idemAt Z y * (idemAt Z y * t) = idemAt Z y * t := fun t => by rw [← mul_assoc, he.eq]
  have hs₁ : π (idemAt Z y * s) = (g τ).det := by rw [map_mul, hπ, one_mul]; exact hs
  have hs₂ : π (idemAt Z y * s') = d' := by rw [map_mul, hπ, one_mul]; exact hs'
  refine ⟨idemAt Z y * s, idemAt Z y * s', ⟨k s, fun T _ _ φ w' z' g' a' hw' hz' hc' => ?_⟩,
    fun t ht => eq_of_mk_eq he ht.1 (k s) ((ht.2 _ π w z g a hw hz hc).trans hs₁.symm), k s',
    eq_of_mk_eq he (by rw [← mul_assoc, k]) he.eq ?_⟩
  · have h1 : φ (idemAt Z y) = 1 := (CompSplitPfB.cspB_idem_map _ _ φ y.x_over w'.x_over hw'.1).trans
      ((CompSplitPfB.cspB_idem_congr _ _ z'.x_over w'.x_over hc'.1.symm).trans
        ((idemAt_eq_one_iff Z z').2 (liesOn_frMap hz' h₀)))
    let ψ := Ideal.Quotient.liftₐ (Ideal.span {1 - idemAt Z y}) φ fun b hb => by
      obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.1 hb
      rw [map_mul, map_sub, h1, map_one, sub_self, mul_zero]
    have hψ : ψ.comp π = φ := Ideal.Quotient.liftₐ_comp _ _ _
    have c₁ := (ChgBC.frChg_baseChange E H Dw l Xo c _ T ψ w z w' z' g a hc (frMap_of_comp hψ hw hw')).1
      (frMap_of_comp (Subsingleton.elim _ _) hz hz')
    rw [((frChg_exists_unique E H Dw l Xo c T w' z').2 _ _ _ _ hc' c₁).1, ← hψ, AlgHom.comp_apply, hs₁]
    exact ψ.toRingHom.map_det (g τ)
  · show π _ = π _
    rw [map_mul, hs₁, hs₂, hd', hπ]

theorem prod_exOf_flatWt (hq : Dw.q = 0) (τ : Psi H) {G : Type} [CommGroup G] (t : Ix Dw → G) :
    ∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i = (∏ i, t (some ⟨τ.1, i⟩))⁻¹ := by
  have h : ∀ (ρ : E →+* ℂ) (i : Fin (Dw.mult ρ)),
      exOf Dw (flatWt Dw τ) 0 (some ⟨ρ, i⟩) = open Classical in if ρ = τ.1 then -1 else 0 := fun ρ i => by
    have hi := i.2
    have hρ : ρ (H.rt : E) = H.rt0 := by
      by_contra hn
      simp [Datum.mult, hn, hq] at hi
    refine (wtOf_big (flatWt Dw τ) 0 ⟨ρ, hρ⟩ i (by simpa [Datum.mult, hρ] using hi)).trans ?_
    simp only [flatWt, parWt, sub_zero]
    by_cases h1 : ρ = τ.1
    · rw [if_pos h1, if_pos (Subtype.ext h1)]
    · rw [if_neg h1, if_neg fun h2 => h1 (congrArg Subtype.val h2)]
  have h0 : exOf Dw (flatWt Dw τ) 0 none = 0 := rfl
  rw [Fintype.prod_option, h0, zpow_zero, one_mul, Fintype.prod_sigma, Finset.prod_eq_single τ.1
    (fun ρ _ hρ => by simp [h, hρ]) (by simp)]
  simp [h]

theorem inv_mem_secZ_on {Z : Comp Xo c} {e : Ix Dw → ℤ} {f f' : Rul Xo c} (hf : f ∈ secZ Xo c e)
    (h1 : idem Z * f' = f') (h2 : f * f' = idem Z) : f' ∈ secZ Xo c (-e) := by
  have k1 : ∀ p y, idem Z p y * f' p y = f' p y := fun p y => congrFun (congrFun h1 p) y
  have k2 : ∀ p y, f p y * f' p y = idem Z p y := fun p y => congrFun (congrFun h2 p) y
  have hi := idem_mem_secZ Z
  refine ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩
  · have a1 := congrArg φ (k1 p y)
    have a2 := congrArg φ (k2 p y)
    rw [map_mul, ← hi.1 p q φ y z h] at a1
    rw [map_mul, ← hi.1 p q φ y z h, ← hf.1 p q φ y z h] at a2
    linear_combination a1 - k1 q z - f' q z * a2 + φ (f' p y) * k2 q z
  · have a1 := k2 p y'
    have a0 : idem Z p y' = idem Z p y := by simpa using hi.2 p t y y' h
    have a4 := k1 p y'
    rw [hf.2 p t y y' h, a0] at a1
    rw [a0] at a4
    have a3 : ((∏ i, t i ^ (-e) i : (p.R)ˣ) : p.R) * ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) = 1 := by
      rw [← Units.val_mul, ← Finset.prod_mul_distrib]; simp
    generalize ((∏ i, t i ^ (-e) i : (p.R)ˣ) : p.R) = A at *
    generalize ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) = B at *
    linear_combination A * f' p y * a1 - a4 - f' p y' * k2 p y + A * k1 p y - f p y * f' p y * f' p y' * a3

theorem exists_flatRule : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 → ∀ (Z : Comp Xo c) (τ : Psi H) (y₀ : FrPt Xo c c.F), LiesOn Z y₀ → (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → y.x = spMap (algebraMap c.F S) ≫ y₀.x) → ∃ f f' : Rul Xo c, f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) ∧ f' ∈ secZ Xo c (-exOf Dw (flatWt Dw τ) 0) ∧ idem Z * f = f ∧ idem Z * f' = f' ∧ f * f' = idem Z ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y z : FrPt Xo c S) (g : (∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) S)) (a : S), Tested y → FrMap (Algebra.ofId c.F S) y₀ z → FrChg g a y z → evR Xo c f y = (g τ.1).det := by
  intro E _ _ _ H Dw l Xo c hq Z τ y₀ h₀ hy₀
  choose f f' hf hu h1 h2 using fun (p : TRing c.F) (y : FrPt Xo c p.R) => exists_isCoef h₀ hy₀ τ.1 y
  have i1 : idem Z * f' = f' := funext fun p => funext fun y => h1 p y
  have i2 : (f : Rul Xo c) * f' = idem Z := funext fun p => funext fun y => h2 p y
  have hm : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) := by
    refine ⟨fun p q φ y z h => (hu q z _ ⟨?_, fun T _ _ ψ w z' g a hw hz hc => ?_⟩).symm,
      fun p t y y' h => (hu p y' _ ⟨?_, fun T _ _ ψ w' z' g a hw hz hc => ?_⟩).symm⟩
    · rw [idemAt, ← CompSplitPfB.cspB_idem_map _ _ φ y.x_over z.x_over h.1, ← map_mul]
      exact congrArg φ (hf p y).1
    · exact (hf p y).2 T (ψ.comp φ) w z' g a (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ h hw) hz hc
    · rw [mul_left_comm, idemAt, CompSplitPfB.cspB_idem_congr _ _ y.x_over y'.x_over h.1]
      exact congrArg _ (hf p y).1
    · obtain ⟨k, k0, k1, hk⟩ := ((frBor_calculus E H Dw l Xo c _ y y' y').1 t).1 h
      obtain ⟨w, hw₀⟩ := exists_bc ψ y
      have c₁ := (ChgBC.frChg_baseChange E H Dw l Xo c _ T ψ y y' w w' k _ hk hw₀).1 hw
      have c₂ := (frChg_refl_and_comp E H Dw l Xo c T w w' z').2 _ _ _ _ c₁ hc
      have hd : (k τ.1).det = ((∏ i, t (some ⟨τ.1, i⟩) : (p.R)ˣ) : p.R) := by
        rw [Matrix.det_of_isLowerTriangular _ (fun i j hij => k0 τ.1 i j hij), Units.coe_prod]
        exact Finset.prod_congr rfl fun i _ => k1 τ.1 i
      have hd' : ((k τ.1).map ψ).det = ψ (k τ.1).det := (ψ.toRingHom.map_det (k τ.1)).symm
      rw [map_mul, (hf p y).2 T ψ w z' _ _ hw₀ hz c₂, Matrix.det_mul, hd', hd, prod_exOf_flatWt hq, mul_left_comm,
        ← map_mul, Units.inv_mul, map_one, mul_one]
  refine ⟨f, f', hm, inv_mem_secZ_on hm i1 i2, funext fun p => funext fun y => (hf p y).1, i1, i2,
    fun S _ _ y z g a ht hz hc => ?_⟩
  unfold evR evalAt
  rw [dite_eq_left ht]
  exact (hf _ _).2 S _ y z g a ht.choose_spec.choose_spec.choose_spec hz hc

end GlobalTheory.FlatLine.Definite
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.Rec

open GlobalTheory.Published.PoitouTate

variable {l : ℕ} [Fact l.Prime] {c : Coef l}
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {n : ℕ} {S : Finset Pl}
  {ξ : G ℚ Ω → G ℚ Ω → Qbar l}

def zcl {μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ} (hμ : μ.comp (toGS Ω _) = cycMod ℚ Ω l n)
    (hξ : Coc2 c n S ξ) (i : Ix c) : H2 (charRep μ) :=
  Submodule.Quotient.mk ⟨zc c n S ξ i, zc_mem hμ hξ i⟩

theorem res_zcl_eq_zero {μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ}
    (hμ : μ.comp (toGS Ω _) = cycMod ℚ Ω l n) (hξ : Coc2 c n S ξ) (Av : S → ValuationSubring Ω) (v : S)
    (hcob : Cob2 c n (Dec (F := ℚ) (Av v)) ξ) (i : Ix c) :
    resH2 (charRep μ) (locFam S Av v) (continuous_locFam S Av v) (zcl hμ hξ i) = 0 := by
  obtain ⟨u, hu, huO, hcu⟩ := hcob
  unfold zcl resH2
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    separated_dvr_second_cohomology_mem]
  refine ⟨fun g => crd c n i (u g), continuous_crd hu.domRestrict (fun g => huO _) n i, ?_⟩
  funext ⟨g, h⟩
  rw [d1_apply, restrictCocycles2_apply]
  change _ = zc c n S ξ i (((g : G ℚ Ω) : GS Ω (S : Set Pl)), ((h : G ℚ Ω) : GS Ω (S : Set Pl)))
  rw [zc_mk hξ, MonoidHom.coe_comp, Function.comp_apply, charRep_apply]
  have hμg : ((μ (locFam S Av v g) : ZMod (l ^ n))) = PadicInt.toZModPow n (cycZ ℚ Ω l g : ℤ_[l]) :=
    congrArg Units.val (DFunLike.congr_fun hμ (g : G ℚ Ω))
  rw [hμg]
  have hc := (cg_iff (hξ.int g h) (c.O.add_mem (c.O.sub_mem (algebraMap_mul_mem _ (huO h)) (huO _)) (huO g))).1
    (hcu g g.2 h h.2) i
  rw [crd_add i (c.O.sub_mem (algebraMap_mul_mem _ (huO h)) (huO _)) (huO g),
    crd_sub i (algebraMap_mul_mem _ (huO h)) (huO _), crd_algebraMap_mul i _ (huO h)] at hc
  rw [hc]; rfl

theorem cob_of_res_zcl_eq_zero {μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ}
    (hμ : μ.comp (toGS Ω _) = cycMod ℚ Ω l n) (hξ : Coc2 c n S ξ) (Av : S → ValuationSubring Ω) (v : S)
    (h0 : ∀ i, resH2 (charRep μ) (locFam S Av v) (continuous_locFam S Av v) (zcl hμ hξ i) = 0) :
    Cob2 c n (Dec (F := ℚ) (Av v)) ξ := by
  have hb : ∀ i, ∃ ci : Dec (F := ℚ) (Av v) → ZMod (l ^ n), Continuous ci ∧
      d1 ((charRep μ).comp (locFam S Av v)) ci =
        fun p => zc c n S ξ i (((p.1 : G ℚ Ω) : GS Ω (S : Set Pl)), ((p.2 : G ℚ Ω) : GS Ω (S : Set Pl))) := by
    intro i
    have := h0 i
    unfold zcl resH2 at this
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
      separated_dvr_second_cohomology_mem] at this
    exact this
  choose ci hci hd using hb
  classical
  refine ⟨fun s => if hs : s ∈ Dec (F := ℚ) (Av v) then lft c n (fun i => ci i ⟨s, hs⟩) else 0, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (Set.domRestrict (Dec (F := ℚ) (Av v) : Set (G ℚ Ω))
        fun s => if hs : s ∈ Dec (F := ℚ) (Av v) then lft c n (fun i => ci i ⟨s, hs⟩) else 0) =
        fun g => lft c n (fun i => ci i g) := by
      funext g; exact dif_pos g.2
    rw [this]
    exact Continuous.comp (g := lft c n) (f := fun g i => ci i g) continuous_of_discreteTopology
      (continuous_pi fun i => hci i)
  · intro s
    dsimp only
    split_ifs
    · exact lft_mem _ _
    · exact c.O.zero_mem
  · intro s hs t ht
    dsimp only
    rw [dif_pos ht, dif_pos ((Dec (F := ℚ) (Av v)).mul_mem hs ht), dif_pos hs]
    have hm : ∀ a, lft c n a ∈ c.O := lft_mem n
    refine (cg_iff (hξ.int s t) (c.O.add_mem (c.O.sub_mem (algebraMap_mul_mem _ (hm _)) (hm _)) (hm _))).2
      fun i => ?_
    rw [crd_add i (c.O.sub_mem (algebraMap_mul_mem _ (hm _)) (hm _)) (hm _),
      crd_sub i (algebraMap_mul_mem _ (hm _)) (hm _), crd_algebraMap_mul i _ (hm _), crd_lft, crd_lft, crd_lft]
    have e := congrFun (hd i) (⟨s, hs⟩, ⟨t, ht⟩)
    rw [zc_mk hξ, d1_apply, MonoidHom.coe_comp, Function.comp_apply, charRep_apply] at e
    have hμg : ((μ (locFam S Av v ⟨s, hs⟩) : ZMod (l ^ n))) = PadicInt.toZModPow n (cycZ ℚ Ω l s : ℤ_[l]) :=
      congrArg Units.val (DFunLike.congr_fun hμ s)
    rw [hμg] at e
    rw [← e]; rfl

end GlobalTheory.Ord2.Rec

namespace GlobalTheory.Ord2.Rec

open GlobalTheory.Published.PoitouTate

theorem reciprocity : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (v₀ : Pl),
    l ≠ 2 → ContainsAbove S l → Coc2 c n S ξ → v₀ ∈ S →
    (∀ v ∈ S, v ≠ v₀ → ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Cob2 c n (Dec (F := ℚ) B) ξ) →
    ∀ B : ValuationSubring Ω, IsPlaceOver B v₀ → Cob2 c n (Dec (F := ℚ) B) ξ := by
  intro hL l _ Ω _ _ _ c n S ξ v₀ hl hS hξ hv₀ hloc B hB
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun _ => 0, continuousOn_const, fun _ => c.O.zero_mem, fun s _ t _ => ?_⟩
    unfold Cg
    simp only [mul_zero, sub_zero, add_zero, pow_zero, norm_one]
    exact norm_le_one_of_mem (hξ.int s t)
  obtain ⟨ζ, hζ⟩ := GlobalTheory.Published.exists_primitiveRoot_pow ℚ Ω l n
  obtain ⟨inv, hinv, hPT⟩ := hL.pt ℚ Ω l n (Or.inl hl) hn ζ hζ
  classical
  let Av : S → ValuationSubring Ω := fun v =>
    if h : v.1 = v₀ then B else Classical.choose (hloc v.1 v.2 h)
  have hAv : ∀ v, IsPlaceOver (Av v) v.1 := by
    intro v
    by_cases h : v.1 = v₀
    · simp only [Av, dif_pos h]; rw [h]; exact hB
    · simp only [Av, dif_neg h]; exact (Classical.choose_spec (hloc v.1 v.2 h)).1
  obtain ⟨μ, hμ⟩ := exists_lift_cycMod (F := ℚ) (Ω := Ω) (r := n) hS
  have hNT := (hPT S hS Av hAv μ hμ (ZMod (l ^ n)) (charRep μ) (contAction_charRep hμ)).1
  have hres : ∀ i, resH2 (charRep μ) (locFam S Av ⟨v₀, hv₀⟩) (continuous_locFam S Av _)
      (zcl hμ hξ i) = 0 := by
    intro i
    have hsum := hNT.sum_eq_zero (zcl hμ hξ i)
    rw [Finset.sum_eq_single ⟨v₀, hv₀⟩] at hsum
    · have hinj : Function.Injective (invAt S Av μ hμ inv ⟨v₀, hv₀⟩) :=
        (hinv _ _ (hAv ⟨v₀, hv₀⟩)).1.1.comp (toMuLoc_bijective S Av μ hμ _).1
      exact hinj (by rw [hsum, map_zero])
    · intro v _ hv
      have hne : v.1 ≠ v₀ := fun h => hv (Subtype.ext h)
      have hcob : Cob2 c n (Dec (F := ℚ) (Av v)) ξ := by
        simp only [Av, dif_neg hne]; exact (Classical.choose_spec (hloc v.1 v.2 hne)).2
      rw [res_zcl_eq_zero hμ hξ Av v hcob i, map_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hcob := cob_of_res_zcl_eq_zero hμ hξ Av ⟨v₀, hv₀⟩ hres
  have hA : Av ⟨v₀, hv₀⟩ = B := dif_pos rfl
  rw [hA] at hcob
  exact hcob

end GlobalTheory.Ord2.Rec
end
end
