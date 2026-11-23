module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle138
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Mathlib.Analysis.Meromorphic.Order
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle137
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle141
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle140
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetSpanPrincipalCongruenceLevelFunction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTranslatesLevelAndScalarMod
public import Formalism.FormalDegreeBessel.StatementIO
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.eq_or_eq_neg_of_weierstrassP_torsion_eq : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 → wp N x τ = wp N y τ → x = y ∨ x = -y := by
  first | exact @GlobalTheory.FN.WpSep.main | exact GlobalTheory.FN.WpSep.main | (intros; apply GlobalTheory.FN.WpSep.main <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
open Filter Topology

namespace GlobalTheory.KZ.MeroRoot

theorem valAt {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (τ : ℂ) (hτ : τ ∈ Hs) :
    ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ x : X.K, W.valuation x = 1 → ∀ φ : ℂ → ℂ,
      X.an x = (φ : Mero) → meromorphicOrderAt φ τ = 0 := GlobalTheory.T.exists_place_over_jLine_of_upperHalfPlane_point X τ hτ

theorem repAt {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (x : X.K) (φ : ℂ → ℂ)
    (hφ : X.an x = (φ : Mero)) (τ : ℂ) (hτ : τ ∈ Hs) :
    MeromorphicAt φ τ ∧ (x ≠ 0 → meromorphicOrderAt φ τ ≠ ⊤) := GlobalTheory.T.an_meromorphicAt_upperHalfPlane X x φ hφ τ hτ

theorem rootHs (h : ℂ → ℂ) (m : ℕ) (hm : 0 < m) (hh : DifferentiableOn ℂ h Hs)
    (hdiv : ∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt h τ = (k : WithTop ℤ) → (m : ℤ) ∣ k) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Hs ∧ ∀ z ∈ Hs, g z ^ m = h z := GlobalTheory.T.exists_holomorphic_root_upperHalfPlane_of_order_dvd h m hm hh hdiv

end GlobalTheory.KZ.MeroRoot

namespace GlobalTheory.KZ.MeroRoot

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem nhdsNE_of_codisc {F G : ℂ → ℂ} (hFG : F =ᶠ[codiscreteWithin Hs] G) {τ : ℂ} (hτ : τ ∈ Hs) :
    F =ᶠ[𝓝[≠] τ] G := by
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hFG) τ hτ
  have h2 : Hs ∈ 𝓝[≠] τ := nhdsWithin_le_nhds (isOpen_Hs.mem_nhds hτ)
  filter_upwards [h1, h2] with z hz1 hz2
  rcases hz1 with hz | hz
  · exact hz
  · exact absurd hz2 hz

theorem germ_rep (x : Mero) : ∃ φ : ℂ → ℂ, x = (φ : Mero) := by
  induction x using Filter.Germ.inductionOn with
  | h φ => exact ⟨φ, rfl⟩

theorem wt_dvd {m : ℕ} (hm : 0 < m) {k : ℤ} {u v : WithTop ℤ}
    (hk : (k : WithTop ℤ) = (m : WithTop ℤ) * u + (m : WithTop ℤ) * v) : (m : ℤ) ∣ k := by
  have hm0 : (m : WithTop ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  cases u with
  | top => rw [WithTop.mul_top hm0, WithTop.top_add] at hk; exact absurd hk (WithTop.coe_ne_top)
  | coe p =>
    cases v with
    | top => rw [WithTop.mul_top hm0, WithTop.add_top] at hk; exact absurd hk (WithTop.coe_ne_top)
    | coe q =>
      have : k = (m : ℤ) * p + (m : ℤ) * q := by exact_mod_cast hk
      exact ⟨p + q, by rw [this]; ring⟩

theorem orders_dvd {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (m : ℕ) (hm : 0 < m)
    (f : X.Kˣ) (hf : f ∈ X.Un m) (a b : ℂ → ℂ) (hb : DifferentiableOn ℂ b Hs)
    (hab : X.an (f : X.K) * (b : Mero) = (a : Mero)) :
    ∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt (fun z => a z * b z ^ (m - 1)) τ = (k : WithTop ℤ) → (m : ℤ) ∣ k := by
  intro τ hτ k hk
  obtain ⟨W, hW, hWv⟩ := valAt X τ hτ
  obtain ⟨g, hg⟩ := hf W hW
  obtain ⟨φf, hφf⟩ := germ_rep (X.an (f : X.K))
  obtain ⟨φg, hφg⟩ := germ_rep (X.an (g : X.K))
  obtain ⟨ψ, hψ⟩ := germ_rep (X.an ((f : X.K) / (g : X.K) ^ m))
  have hψ0 : meromorphicOrderAt ψ τ = 0 := hWv _ hg ψ hψ
  have hfm := (repAt X _ φf hφf τ hτ).1
  have hgm := (repAt X _ φg hφg τ hτ).1
  have hψm := (repAt X _ ψ hψ τ hτ).1
  have hbm : MeromorphicAt b τ :=
    ((hb.analyticOnNhd isOpen_Hs) τ hτ).meromorphicAt

  have e1 : (φf : Mero) = ((fun z => ψ z * φg z ^ m : ℂ → ℂ) : Mero) := by
    have : (f : X.K) = ((f : X.K) / (g : X.K) ^ m) * (g : X.K) ^ m := by
      rw [div_mul_cancel₀]; exact pow_ne_zero _ g.ne_zero
    rw [← hφf, this, map_mul, map_pow, hψ, hφg]; rfl
  have e1' : φf =ᶠ[𝓝[≠] τ] (fun z => ψ z * φg z ^ m) := nhdsNE_of_codisc (Filter.Germ.coe_eq.1 e1) hτ
  have e2 : ((fun z => a z * b z ^ (m - 1) : ℂ → ℂ) : Mero) = ((fun z => φf z * b z ^ m : ℂ → ℂ) : Mero) := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    show ((a * b ^ n : ℂ → ℂ) : Mero) = ((φf * b ^ (n + 1) : ℂ → ℂ) : Mero)
    rw [Filter.Germ.coe_mul, Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow, ← hab, hφf, pow_succ]
    ring
  have e2' := nhdsNE_of_codisc (Filter.Germ.coe_eq.1 e2) hτ
  have o1 : meromorphicOrderAt φf τ = (m : WithTop ℤ) * meromorphicOrderAt φg τ := by
    rw [meromorphicOrderAt_congr e1']
    rw [show (fun z => ψ z * φg z ^ m) = ψ * φg ^ m from rfl, meromorphicOrderAt_mul hψm (hgm.pow m),
      meromorphicOrderAt_pow hgm, hψ0, zero_add]
  rw [meromorphicOrderAt_congr e2', show (fun z => φf z * b z ^ m) = φf * b ^ m from rfl,
    meromorphicOrderAt_mul hfm (hbm.pow m), meromorphicOrderAt_pow hbm, o1] at hk
  exact wt_dvd hm hk.symm

end GlobalTheory.KZ.MeroRoot

namespace GlobalTheory.KZ.MeroRoot

theorem exists_mero_root : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧
      (b : Mero) ≠ 0 ∧ X.an (f : X.K) * (b : Mero) ^ m = (a : Mero) ^ m := by
  intro Ω _ _ _ ε X _ _ m hm f hf
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero (f : X.K)
  obtain ⟨g, hg, hgm⟩ := rootHs (fun z => a z * b z ^ (m - 1)) m hm (ha.mul (hb.pow _))
    (orders_dvd X m hm f hf a b hb hab)
  refine ⟨g, b, hg, hb, hb0, ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have e : ((fun z => a z * b z ^ n : ℂ → ℂ) : Mero) = ((fun z => g z ^ (n + 1) : ℂ → ℂ) : Mero) := by
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
    simpa using (hgm z hz).symm
  rw [pow_succ, mul_comm ((b : Mero) ^ n), ← mul_assoc, hab, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow,
    ← Filter.Germ.coe_mul]
  exact e

end GlobalTheory.KZ.MeroRoot
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory

theorem primCan_mul_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (c : Ω) (a b : HahnSeries ℚ Ω)
    (ha : ∀ r, a.coeff r ∈ A) (hb : ∀ r, ∃ z ∈ A, b.coeff r = c * z) :
    ∀ r, ∃ z ∈ A, (a * b).coeff r = c * z := by
  intro r
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_induction _ (fun x => ∃ z ∈ A, x = c * z) ?_ ?_ ?_
  · rintro x y ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨z + w, A.add_mem _ _ hz hw, by ring⟩
  · exact ⟨0, A.zero_mem, by simp⟩
  · intro ij _
    obtain ⟨z, hz, e⟩ := hb ij.2
    exact ⟨a.coeff ij.1 * z, A.mul_mem _ _ (ha _) hz, by rw [e]; ring⟩

theorem primCan : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω),
    ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (P φ : HahnSeries ℚ Ω), 0 < L → Prim A P →
    (∀ r : ℚ, P.coeff r ≠ 0 → (r * L).den = 1) → (∀ r, φ.coeff r ∈ A) →
    (∀ r, CgA A l n ((φ * P).coeff r) 0) → ∀ r, CgA A l n (φ.coeff r) 0 := by
  intro Ω _ _ _ l _ A hl n L P φ hL hP hden hφ hφP
  obtain ⟨Q, hQ, -, hQP⟩ := GlobalTheory.T.primitive_hahnSeries_invertible_mod_prime_pow l A hl n L P hL hP hden
  have h1 : ∀ r, ∃ z ∈ A, (Q * P - 1).coeff r = (l : Ω) ^ n * z := by
    intro r
    obtain ⟨z, hz, e⟩ := hQP r
    exact ⟨z, hz, by rw [HahnSeries.coeff_sub]; exact e⟩
  have h2 := primCan_mul_dvd A _ φ _ hφ h1
  have h3 : ∀ r, ∃ z ∈ A, (Q * (φ * P)).coeff r = (l : Ω) ^ n * z := by
    refine primCan_mul_dvd A _ Q _ hQ ?_
    intro r
    obtain ⟨z, hz, e⟩ := hφP r
    exact ⟨z, hz, by rw [← e, sub_zero]⟩
  intro r
  obtain ⟨z, hz, ez⟩ := h3 r
  obtain ⟨w, hw, ew⟩ := h2 r
  have hid : φ = Q * (φ * P) - φ * (Q * P - 1) := by ring
  refine ⟨z - w, sub_mem hz hw, ?_⟩
  rw [sub_zero, hid, HahnSeries.coeff_sub, ez, ew]
  ring

end GlobalTheory
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory

theorem isDl_finset_prod_zpow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (ι : Type) (I : Finset ι) (f : ι → X.K) (φ : ι → HahnSeries ℚ Ω) (m : ι → ℤ), (∀ i ∈ I, IsDl X A l n s (f i) (φ i)) → IsDl X A l n s (∏ i ∈ I, f i ^ m i) (∑ i ∈ I, m i • φ i) := by
  intro Ω _ _ _ ε X hj l _ A hl n s ι I f φ m h
  classical
  have C := fun (a b : X.K) (u v : HahnSeries ℚ Ω) => GlobalTheory.T.isLogDerivQExpansionModPrimePow_calculus ε X hj l A hl n s a b u v
  have one : IsDl X A l n s (1 : X.K) 0 := by
    have := (C 1 1 0 0).2.2.2.1 1 one_ne_zero
    simpa using this
  have npow : ∀ (g : X.K) (u : HahnSeries ℚ Ω), IsDl X A l n s g u → ∀ k : ℕ, IsDl X A l n s (g ^ k) (k • u) := by
    intro g u hg k
    induction k with
    | zero => simpa using one
    | succ k ih =>
      rw [pow_succ, succ_nsmul]
      exact (C (g ^ k) g (k • u) u).1 ih hg
  have zp : ∀ (g : X.K) (u : HahnSeries ℚ Ω), IsDl X A l n s g u → ∀ k : ℤ, IsDl X A l n s (g ^ k) (k • u) := by
    intro g u hg k
    cases k with
    | ofNat k =>
      rw [Int.ofNat_eq_coe, zpow_natCast, natCast_zsmul]
      exact npow g u hg k
    | negSucc k =>
      rw [zpow_negSucc, negSucc_zsmul]
      exact (C (g ^ (k + 1)) 1 ((k + 1) • u) 0).2.1 (npow g u hg (k + 1))
  induction I using Finset.induction_on with
  | empty => simpa using one
  | insert a I ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (C _ _ _ _).1 (zp _ _ (h a (Finset.mem_insert_self a I)) (m a))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end GlobalTheory
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.dehomogeniseBinaryPoly_homogeneous_equiv_slash : ∀ w : ℕ, (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) ℂ), p.IsHomogeneous w → deh (slP m p) = GlobalTheory.HeckeFamilyMatrices.slP w m (deh p)) ∧ (∀ p : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w → deh p ∈ Polynomial.degreeLT ℂ (w + 1)) ∧ (∀ q ∈ Polynomial.degreeLT ℂ (w + 1), ∃ p : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w ∧ deh p = q) ∧ (∀ p p' : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w → p'.IsHomogeneous w → deh p = deh p' → p = p') := by
  first | exact @GlobalTheory.KZ.H3.deh_homog_iso | exact GlobalTheory.KZ.H3.deh_homog_iso | (intros; apply GlobalTheory.KZ.H3.deh_homog_iso <;> assumption)
end

section

noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3.PotCoc

def orbSetoid (Γ : Subgroup SL(2, ℤ)) : Setoid Hs where
  r a b := ∃ γ ∈ Γ, mob (ofSL γ) a.1 = b.1
  iseqv := by
    obtain ⟨-, hmul, hone, -⟩ := GlobalTheory.KZ.mob_laws
    refine ⟨fun a => ⟨1, Γ.one_mem, by simp [hone]⟩, ?_, ?_⟩
    · rintro a b ⟨γ, hγ, h⟩
      refine ⟨γ⁻¹, Γ.inv_mem hγ, ?_⟩
      rw [← h, ← hmul _ _ _ a.2, ← map_mul, inv_mul_cancel, map_one, hone]
    · rintro a b c ⟨γ, hγ, h⟩ ⟨δ, hδ, h'⟩
      refine ⟨δ * γ, Γ.mul_mem hδ hγ, ?_⟩
      rw [map_mul, hmul _ _ _ a.2, h, h']

def rep (Γ : Subgroup SL(2, ℤ)) (a : Hs) : Hs := (Quotient.mk (orbSetoid Γ) a).out

theorem rep_rel (Γ : Subgroup SL(2, ℤ)) (a : Hs) : ∃ γ ∈ Γ, mob (ofSL γ) (rep Γ a).1 = a.1 :=
  Quotient.mk_out (s := orbSetoid Γ) a


open Classical in
def gel (Γ : Subgroup SL(2, ℤ)) (τ : ℂ) : SL(2, ℤ) :=
  if h : τ ∈ Hs then (rep_rel Γ ⟨τ, h⟩).choose else 1

theorem gel_spec (Γ : Subgroup SL(2, ℤ)) {τ : ℂ} (h : τ ∈ Hs) :
    gel Γ τ ∈ Γ ∧ mob (ofSL (gel Γ τ)) (rep Γ ⟨τ, h⟩).1 = τ := by
  simp only [gel, dif_pos h]
  exact (rep_rel Γ ⟨τ, h⟩).choose_spec

theorem rep_eq (Γ : Subgroup SL(2, ℤ)) {δ : SL(2, ℤ)} (hδ : δ ∈ Γ) {τ : ℂ} (h : τ ∈ Hs)
    (h' : mob (ofSL δ) τ ∈ Hs) : rep Γ ⟨mob (ofSL δ) τ, h'⟩ = rep Γ ⟨τ, h⟩ := by
  unfold rep
  congr 1
  exact Quotient.sound (s := orbSetoid Γ) ⟨δ⁻¹, Γ.inv_mem hδ, by
    obtain ⟨-, hmul, hone, -⟩ := GlobalTheory.KZ.mob_laws
    show mob (ofSL δ⁻¹) (mob (ofSL δ) τ) = τ
    rw [← hmul _ _ _ h, ← map_mul, inv_mul_cancel, map_one, hone]⟩

theorem slPS {R : Type} [CommRing R] (a c : SL(2, ℤ)) (p : MvPolynomial (Fin 2) R) :
    slP (c : Matrix (Fin 2) (Fin 2) ℤ) (slP (a : Matrix (Fin 2) (Fin 2) ℤ) p) =
      slP ((a * c : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) p := by
  rw [GlobalTheory.KZ.Betti.polySlash_polySlash, Matrix.SpecialLinearGroup.coe_mul]

def potOf {R : Type} [CommRing R] (Γ : Subgroup SL(2, ℤ)) (z : SL(2, ℤ) → MvPolynomial (Fin 2) R) (τ : ℂ) :
    MvPolynomial (Fin 2) R :=
  slP (((gel Γ τ)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (z (gel Γ τ))

end GlobalTheory.KZ.H3.PotCoc


open GlobalTheory.KZ.H3.PotCoc GlobalTheory.KZ.Betti in
theorem GlobalTheory.KZ.H3.exists_pot_of_isCoc : ∀ (R : Type) [CommRing R] (w N l : ℕ), 4 ≤ N →
    ∀ z : SL(2, ℤ) → MvPolynomial (Fin 2) R, IsCoc w (Gam N l) z → ∃ F ∈ Pot R w (Gam N l),
      ∀ γ ∈ Gam N l, ∀ τ ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) τ)) - F τ = z γ := by
  intro R _ w N l hN z hz
  obtain ⟨hmem, hmul, hone, -⟩ := GlobalTheory.KZ.mob_laws
  set Γ := Gam N l
  have key : ∀ γ ∈ Γ, ∀ τ ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (potOf Γ z (mob (ofSL γ) τ)) - potOf Γ z τ = z γ := by
    intro δ hδ τ hτ
    have hτ' : mob (ofSL δ) τ ∈ Hs := hmem _ _ hτ
    obtain ⟨hg1, hg2⟩ := gel_spec Γ hτ
    obtain ⟨hg1', hg2'⟩ := gel_spec Γ hτ'
    rw [rep_eq Γ hδ hτ hτ'] at hg2'
    set g := gel Γ τ
    set g' := gel Γ (mob (ofSL δ) τ)
    have hg : g' = δ * g := by
      have hfree := GlobalTheory.T.gamma1CapGamma0Level_acts_freely_upperHalfPlane N l hN (g'⁻¹ * (δ * g)) (Γ.mul_mem (Γ.inv_mem hg1') (Γ.mul_mem hδ hg1))
        _ (rep Γ ⟨τ, hτ⟩).2 (by
          rw [map_mul, hmul _ _ _ (rep Γ ⟨τ, hτ⟩).2, map_mul, hmul _ _ _ (rep Γ ⟨τ, hτ⟩).2, hg2, ← hg2',
            ← hmul _ _ _ (rep Γ ⟨τ, hτ⟩).2, ← map_mul, inv_mul_cancel, map_one, hone])
      exact (inv_mul_eq_one.mp hfree)
    show slP (δ : Matrix (Fin 2) (Fin 2) ℤ) (slP ((g'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (z g')) -
      slP ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (z g) = z δ
    rw [hg, (hz.2 δ hδ g hg1)]
    have e1 : (δ * g)⁻¹ * δ = g⁻¹ := by group
    have e2 : g * (δ * g)⁻¹ * δ = 1 := by rw [mul_assoc, e1]; group
    simp only [map_add (f := _), slPS, e1, e2, Matrix.SpecialLinearGroup.coe_one, polySlash_one]
    abel
  refine ⟨potOf Γ z, ⟨fun τ => ?_, fun γ hγ => ⟨z γ, key γ hγ⟩⟩, key⟩
  by_cases hτ : τ ∈ Hs
  · exact polySlash_isHomogeneous _ (hz.1 _ (gel_spec Γ hτ).1)
  · have : gel Γ τ = 1 := by simp [gel, dif_neg hτ]
    unfold potOf
    rw [this]
    exact polySlash_isHomogeneous _ (hz.1 _ Γ.one_mem)
end
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.kummerPotentialRelation_trivial_eq_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ → ∀ b F, Rel X l b F → F ∈ Triv ℤ_[l] w Γ → b = 0 := by
  first | exact @GlobalTheory.KZ.H3.rel_triv_eq_zero | exact GlobalTheory.KZ.H3.rel_triv_eq_zero | (intros; apply GlobalTheory.KZ.H3.rel_triv_eq_zero <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.homogeneousPolyCocycle_diff_coboundary_of_eqOn : ∀ (N l w n : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ z z' : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)), IsCoc w (Gam N l) z → IsCoc w (Gam N l) z' → Near z z' → ∃ p : MvPolynomial (Fin 2) (ZMod (l ^ n)), p.IsHomogeneous w ∧ ∀ γ ∈ Gam N l, z γ - z' γ = slP (γ : Matrix (Fin 2) (Fin 2) ℤ) p - p := by
  first | exact @GlobalTheory.KZ.H3.adj_of_near | exact GlobalTheory.KZ.H3.adj_of_near | (intros; apply GlobalTheory.KZ.H3.adj_of_near <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.uniform_congruence_level_gamma1CapGamma0 : ∀ (N l : ℕ) (R : Type) [CommRing R] (Φ : SL(2, ℤ) → MvPolynomial (Fin 2) R), 0 < N → 0 < l → (∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M, Φ (δ * δ') = Φ δ + Φ δ') → (∀ γ ∈ Gam N l, Near (fun δ => slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ (γ * δ * γ⁻¹))) Φ) → ∃ M : ℕ, 0 < M ∧ ∀ γ ∈ Gam N l, ∀ δ ∈ CongruenceSubgroup.Gamma M, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ (γ * δ * γ⁻¹)) = Φ δ := by
  first | exact @GlobalTheory.KZ.H3.unif_level | exact GlobalTheory.KZ.H3.unif_level | (intros; apply GlobalTheory.KZ.H3.unif_level <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.exists_finset_span_principalCongruenceLevel_functions : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ M : ℕ, 0 < M → ∃ T : Finset X.K, (∀ x ∈ T, Lev X M x) ∧ ∀ f : X.K, Lev X M f → f ∈ Submodule.span (IntermediateField.adjoin Ω {X.jK}) (T : Set X.K) := by
  first | exact @GlobalTheory.KZ.ES.LevFin.exists_finset_span | exact GlobalTheory.KZ.ES.LevFin.exists_finset_span | (intros; apply GlobalTheory.KZ.ES.LevFin.exists_finset_span <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.jTranslates_level_and_scalar_mod : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ m : ℕ, 0 < m → (∀ g ∈ ({!![(m : ℤ), 0; 0, 1], !![1, 0; 0, (m : ℤ)], !![1, 1; 0, (m : ℤ)]} : Set (Matrix (Fin 2) (Fin 2) ℤ)), Lev X m (X.sl (toGQ g) X.jK)) ∧ ∀ γ : SL(2, ℤ), (∀ g ∈ ({!![(m : ℤ), 0; 0, 1], !![1, 0; 0, (m : ℤ)], !![1, 1; 0, (m : ℤ)]} : Set (Matrix (Fin 2) (Fin 2) ℤ)), X.sl (ofSL γ) (X.sl (toGQ g) X.jK) = X.sl (toGQ g) X.jK) → (en γ 0 1 : ZMod m) = 0 ∧ (en γ 1 0 : ZMod m) = 0 ∧ (en γ 0 0 : ZMod m) = en γ 1 1 := by
  first | exact @GlobalTheory.KZ.ES.Scal.lev_and_scalar | exact GlobalTheory.KZ.ES.Scal.lev_and_scalar | (intros; apply GlobalTheory.KZ.ES.Scal.lev_and_scalar <;> assumption)
end

section

open Formalism.QuantumDeterminants

namespace GlobalTheory.EquivariantSubspace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smoothOnH_zero (H : Matrix (Fin n) (Fin n) ℂ) :
    SmoothOnH H (0 : Matrix (Fin n) (Fin n) ℂ → E) :=
  fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem smoothOnH_add {H : Matrix (Fin n) (Fin n) ℂ} {f f' : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : SmoothOnH H f) (hf' : SmoothOnH H f') : SmoothOnH H (f + f') := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + F' g, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), ?_⟩
  intro g hg hH
  rw [Pi.add_apply, hfF g hg.1 hH, hfF' g hg.2 hH]

theorem smoothOnH_smul {H : Matrix (Fin n) (Fin n) ℂ} {f : Matrix (Fin n) (Fin n) ℂ → E} (a : ℂ)
    (hf : SmoothOnH H f) : SmoothOnH H (a • f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun g => a • F g, hU, hgU, hF.const_smul a, ?_⟩
  intro g hg hH
  rw [Pi.smul_apply, hfF g hg hH]

end GlobalTheory.EquivariantSubspace
end
