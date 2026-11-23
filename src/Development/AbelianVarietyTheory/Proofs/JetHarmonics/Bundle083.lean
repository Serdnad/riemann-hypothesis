module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqZeroOfGe
public import Formalism.LocalToGlobal.CharacterGerms.Bundle002
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ImaginaryRootConj
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle078
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle054
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle033
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle032
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle027
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle030
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.MvPowerSeries.Expand
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.Bundle001
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.IncomingBounds.Bundle001
import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
import Formalism.LocalToGlobal.Divisibility.Numbers
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Mathlib.Algebra.CharP.Algebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.NabTrans

@[expose] public section

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.SeriesFrobRoot

theorem eq_pow_of_pderiv {k σ : Type} [CommRing k] [IsDomain k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (b c : MvPowerSeries σ k) (hb : ∀ i, MvPowerSeries.pderiv (R := k) i b = 0)
    (hc : ∀ ν, MvPowerSeries.coeff ν c ^ p = MvPowerSeries.coeff (p • ν) b) : b = c ^ p := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [← MvPowerSeries.map_frobenius_expand p hp]
  ext μ
  rw [MvPowerSeries.coeff_map]
  by_cases h : ∀ i, p ∣ μ i
  · obtain ⟨m, hm⟩ : ∃ m, p • m = μ := ⟨μ.mapRange (fun a ↦ a / p) (by simp),
      by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    rw [← hm, MvPowerSeries.coeff_expand_smul, frobenius_def, hc]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [MvPowerSeries.coeff_expand_of_not_dvd p hp _ hi, map_zero]
    have h0 : μ i ≠ 0 := fun h => hi (h ▸ dvd_zero p)
    have hle : Finsupp.single i 1 ≤ μ := by
      rw [Finsupp.single_le_iff]; omega
    have h1 := congrArg (MvPowerSeries.coeff (μ - Finsupp.single i 1)) (hb i)
    rw [MvPowerSeries.coeff_pderiv, tsub_add_cancel_of_le hle, map_zero] at h1
    refine (mul_eq_zero.1 h1).resolve_right fun h2 => hi ?_
    rw [← CharP.cast_eq_zero_iff k p]
    have h3 : μ i = ((μ - Finsupp.single i 1 : σ →₀ ℕ) i) + 1 := by
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]; omega
    rw [h3]; push_cast; exact h2

variable {C : Type} [Field C] {V : VF C} {σ : Type}

open TeichPair

theorem exists_lift {f : MvPowerSeries σ C} (hf : IntS V f) :
    ∃ F : MvPowerSeries σ (intRing V), MvPowerSeries.map (intRing V).subtype F = f :=
  ⟨fun μ => ⟨MvPowerSeries.coeff μ f, hf μ⟩, by ext μ; rfl⟩

theorem mm_iff (F : MvPowerSeries σ (intRing V)) :
    (∀ μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.map (intRing V).subtype F))) ↔
      MvPowerSeries.map (Ideal.Quotient.mk (maxId V)) F = 0 := by
  rw [MvPowerSeries.ext_iff]
  refine forall_congr' fun μ => ?_
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  rfl

theorem charP_res (V : VF C) : CharP (intRing V ⧸ maxId V) V.l := by
  refine (CharP.charP_iff_prime_eq_zero V.l_prime).2 ?_
  rw [← map_natCast (Ideal.Quotient.mk (maxId V)), Ideal.Quotient.eq_zero_iff_mem]
  show 0 < V.v (((V.l : ℕ) : intRing V) : C)
  rw [show (((V.l : ℕ) : intRing V) : C) = (V.l : C) by simp, V.v_l]
  exact zero_lt_one

theorem pderiv_map' {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (i : σ) (F : MvPowerSeries σ R) :
    MvPowerSeries.pderiv (R := S) i (MvPowerSeries.map φ F) = MvPowerSeries.map φ (MvPowerSeries.pderiv (R := R) i F) := by
  ext μ
  simp [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_map]

theorem ge_of_pow {x : C} {n : ℕ} (hn : n ≠ 0) (h : V.Ge 0 (x ^ n)) : V.Ge 0 x := by
  unfold VF.Ge at h ⊢
  rw [V.v.map_pow] at h
  by_contra hx
  rw [not_le] at hx
  induction hv : V.v x using WithTop.recTopCoe with
  | top => rw [hv] at hx; exact not_top_lt hx
  | coe t =>
    rw [hv] at hx h
    rw [← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul] at h
    rw [WithTop.coe_lt_coe] at hx
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    nlinarith

theorem main : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) [Fintype σ], (∀ b : MvPowerSeries σ C, IntS V b → (∀ i μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv (R := C) i b))) → ∃ b' : MvPowerSeries σ C, IntS V b' ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ (b - b' ^ V.l))) ∧ (∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → (∀ μ, V.MM (MvPowerSeries.coeff μ (f ^ V.l - g ^ V.l))) → ∀ μ, V.MM (MvPowerSeries.coeff μ (f - g))) ∧ ∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → ∀ μ, V.MM (MvPowerSeries.coeff μ ((f + g) ^ V.l - f ^ V.l - g ^ V.l)) ∧ V.MM (MvPowerSeries.coeff μ ((f - g) ^ V.l - (f ^ V.l - g ^ V.l))) := by
  intro C _ _ V σ _
  have : Fact V.l.Prime := ⟨V.l_prime⟩
  have := charP_res V
  have : CharP (MvPowerSeries σ (intRing V ⧸ maxId V)) V.l :=
    charP_of_injective_ringHom (MvPowerSeries.C_injective (σ := σ)) V.l
  have : IsDomain (MvPowerSeries σ (intRing V ⧸ maxId V)) := NoZeroDivisors.to_isDomain _
  refine ⟨fun b hb hd => ?_, fun f g hf hg h => ?_, fun f g hf hg => ?_⟩
  · choose r hr using fun ν : σ →₀ ℕ =>
      IsAlgClosed.exists_pow_nat_eq (MvPowerSeries.coeff (V.l • ν) b) V.l_prime.pos
    have hri : ∀ ν, V.Ge 0 (r ν) := fun ν => ge_of_pow V.l_prime.ne_zero (by rw [hr]; exact hb _)
    obtain ⟨B, rfl⟩ := exists_lift hb
    let B' : MvPowerSeries σ (intRing V) := fun ν => ⟨r ν, hri ν⟩
    refine ⟨MvPowerSeries.map (intRing V).subtype B', hri, ?_⟩
    rw [← map_pow, ← map_sub, mm_iff, map_sub, map_pow, sub_eq_zero]
    refine eq_pow_of_pderiv V.l _ _ (fun i => ?_) fun ν => ?_
    · rw [pderiv_map', ← mm_iff, ← pderiv_map']
      exact hd i
    · rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, ← map_pow]
      congr 1
      exact Subtype.ext (hr ν)
  · obtain ⟨F, rfl⟩ := exists_lift hf
    obtain ⟨G, rfl⟩ := exists_lift hg
    rw [← map_pow, ← map_pow, ← map_sub, mm_iff, map_sub, map_pow, map_pow, ← sub_pow_char] at h
    rw [← map_sub, mm_iff, map_sub]
    exact (pow_eq_zero_iff V.l_prime.ne_zero).1 h
  · obtain ⟨F, rfl⟩ := exists_lift hf
    obtain ⟨G, rfl⟩ := exists_lift hg
    rw [forall_and]
    constructor
    · rw [← map_add (f := _), ← map_pow, ← map_pow, ← map_pow, ← map_sub, ← map_sub, mm_iff]
      simp only [map_sub, map_pow, map_add (f := _), add_pow_char]
      ring
    · rw [← map_sub, ← map_pow, ← map_pow, ← map_pow, ← map_sub, ← map_sub, mm_iff]
      simp only [map_sub, map_pow, sub_pow_char]
      ring

end GlobalTheory.SeriesFrobRoot
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

def frobKer {R C : Type} [CommRing R] [Field C] (V : VF C) (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) : Ideal R where
  carrier := {x | V.MM (f x)}
  add_mem' := fun {a b} ha hb => by
    show 0 < V.v (f (a + b))
    rw [map_add (f := _)]
    exact V.v.map_lt_add ha hb
  zero_mem' := by
    show 0 < V.v (f 0)
    rw [map_zero, V.v.map_zero]
    exact WithTop.coe_lt_top (0 : ℝ)
  smul_mem' := fun a b hb => by
    show 0 < V.v (f (a * b))
    rw [map_mul, V.v.map_mul]
    exact lt_of_lt_of_le hb (le_add_of_nonneg_left (hf a))

theorem frobKer_isPrime {R C : Type} [CommRing R] [Field C] (V : VF C) (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) :
    (frobKer V f hf).IsPrime := by
  constructor
  · rw [Ideal.ne_top_iff_one]
    show ¬ 0 < V.v (f 1)
    rw [map_one, V.v.map_one]
    exact lt_irrefl _
  · intro a b h
    have h' : 0 < V.v (f (a * b)) := h
    rw [map_mul, V.v.map_mul] at h'
    change 0 < V.v (f a) ∨ 0 < V.v (f b)
    by_contra! hn
    exact (not_le_of_gt h') (add_nonpos hn.1 hn.2)

theorem exists_frob_of_hom {E C : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field C] (V : VF C)
    (f : 𝓞 E →+* C) (hf : ∀ x, V.Ge 0 (f x)) :
    ∃ φ : E ≃ₐ[ℚ] E, ∀ x : 𝓞 E, V.MM (f (φ • x) - f x ^ V.l) := by
  set P := frobKer V f hf with hP
  haveI : P.IsPrime := frobKer_isPrime V f hf
  have hl : ((V.l : ℕ) : 𝓞 E) ∈ P := by
    show 0 < V.v (f _)
    rw [map_natCast, V.v_l]
    exact zero_lt_one
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hl
    exact V.l_prime.ne_zero (by exact_mod_cast hl)
  haveI : Finite (𝓞 E ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  have hu : P.under ℤ = Ideal.span {(V.l : ℤ)} := by
    have hmax : (Ideal.span {(V.l : ℤ)}).IsMaximal :=
      ((Ideal.span_singleton_prime (by exact_mod_cast V.l_prime.ne_zero)).2
        (Nat.prime_iff_prime_int.1 V.l_prime)).isMaximal (by
          rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast V.l_prime.ne_zero)
    refine (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hl
  obtain ⟨φ, hφ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (E ≃ₐ[ℚ] E) P
  refine ⟨φ, fun x => ?_⟩
  have h := hφ x
  rw [hu, Int.card_ideal_quot] at h
  have h' : V.MM (f (φ • x - x ^ V.l)) := h
  rwa [map_sub, map_pow] at h'

theorem exists_aut_comp_eq {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] (τ₀ τ : E →+* ℂ) :
    ∃ σ : E ≃ₐ[ℚ] E, τ = τ₀.comp (σ : E →+* E) := by
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) τ₀ τ (Subsingleton.elim _ _)
  exact ⟨σ.symm, hσ.symm⟩

theorem exists_frob_all_embeddings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → IsGalois ℚ E → (∀ σ σ' : E ≃ₐ[ℚ] E, σ * σ' = σ' * σ) → ∃ φ : E ≃ₐ[ℚ] E, ∀ (τ : E →+* ℂ) (x : 𝓞 E), V.MM (emA3 io ι (τ.comp (φ : E →+* E)) x - emA3 io ι τ x ^ V.l) := by
  intro E _ _ _ H lv c T io C _ _ V ι hι hG hab
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have key : ∀ (τ : E →+* ℂ) (s : E ≃ₐ[ℚ] E) (x : 𝓞 E),
      emA3 io ι (τ.comp (s : E →+* E)) x = emA3 io ι τ (s • x) := fun τ s x => rfl
  obtain ⟨φ, hφ⟩ := exists_frob_of_hom V (emA3 io ι τ₀)
    (fun x => GlobalTheory.RowChartCounterexample.em_int_holds τ₀ x hι)
  refine ⟨φ, fun τ x => ?_⟩
  obtain ⟨σ, rfl⟩ := exists_aut_comp_eq τ₀ τ
  rw [key, key, key, ← mul_smul, hab, mul_smul]
  exact hφ _

end GlobalTheory.RowAt
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.glRelation_row_steps_functional_eigen : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ), 1 ≤ k → Formalism.REAL.GlRel E → (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ else 0)) → 1 ≤ r → ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E (Fin.succAbove (Fin.last (2 * r + k))) (Fin.succAbove 0) u v) = c • l (Formalism.REAL.qminor E (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1))) (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1, by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) := by
  first | exact @GlobalTheory.RowChain.chain_rows | exact GlobalTheory.RowChain.chain_rows | (intros; apply GlobalTheory.RowChain.chain_rows <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.OrbitPlace


open ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs in
theorem mem_emb_of_congr_pow (A : Type) [CommRing A] (p : ℕ) [Fact p.Prime] (O : Type)
    [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O] (hp : ¬ IsUnit (p : O))
    (e : ℤ_[p] ⊗[ℤ] A) (he : e * e = e) (σ σ' : A →+* O)
    (h : ∀ x, σ' x - σ x ^ p ∈ IsLocalRing.maximalIdeal O) (hσ : σ ∈ Emb (O := O) e) :
    σ' ∈ Emb (O := O) e := by
  obtain ⟨s, x, hx⟩ := GlobalTheory.CharDepth.padicTensor_eq_mul_add A p e
  have hp0 : IsLocalRing.residue O (p : O) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 hp
  have key : ∀ ρ : A →+* O,
      IsLocalRing.residue O (tauExt ρ e) = IsLocalRing.residue O (ρ x) := by
    intro ρ
    have h1 : tauExt (p := p) ρ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) = ρ x := by simp [tauExt]
    rw [hx, map_add (f := _), map_mul, map_natCast, h1, map_add (f := _), map_mul, hp0, zero_mul, zero_add]
  have h1 : IsLocalRing.residue O (σ x) = 1 := by
    have : tauExt σ e = 1 := hσ
    rw [← key, this, map_one]
  have h2 : IsLocalRing.residue O (tauExt σ' e) = 1 := by
    have := (IsLocalRing.residue_eq_zero_iff _).2 (h x)
    rw [map_sub, map_pow, h1, one_pow, sub_eq_zero] at this
    rw [key, this]
  have hu : IsUnit (tauExt σ' e) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, h2]
    exact one_ne_zero
  have hid : tauExt σ' e * tauExt σ' e = tauExt σ' e * 1 := by rw [← map_mul, he, mul_one]
  exact hu.mul_left_cancel hid

theorem exists_placeU_of_frobenius_orbit : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [IsLocalRing O] [Algebra ℤ_[p] O], ¬ IsUnit (p : O) → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (d : ℕ) [NeZero d] (τ : ZMod d → (𝓞 E →+* O)), Function.Injective τ → (∀ s x, τ (s + 1) x - τ s x ^ p ∈ IsLocalRing.maximalIdeal O) → ∃ (w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p (𝓞 E)) (_ : w.n = d) (t : Fin w.n ≃ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e), (∀ j : Fin w.n, ((t j : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e) : 𝓞 E →+* O) = τ ((j.val : ℕ) : ZMod d)) ∧ ∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)), IsUnit (Matrix.det (Matrix.of fun i j => ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt ((t j : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e) : 𝓞 E →+* O) (b i : ℤ_[p] ⊗[ℤ] 𝓞 E))) := by
  intro E _ _ p hpp C _ _ _ v O _ _ hv _ _ hp hd d _ τ hτ hfr
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  obtain ⟨w, hw⟩ := GlobalTheory.exists_placeU_mem_emb p (𝓞 E) O (τ 0)
  have hsep := GlobalTheory.ringOfIntegers_hom_eq_of_congr_maximalIdeal E p hpp.out hd C v O hv hp
  have hmem : ∀ k : ℕ, τ (k : ZMod d) ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e := by
    intro k
    induction k with
    | zero => simpa using hw
    | succ k ih =>
      rw [Nat.cast_succ]
      exact mem_emb_of_congr_pow _ p O hp w.e w.idem _ _ (hfr _) ih
  have hpow : ∀ (k : ℕ) x, IsLocalRing.residue O (τ (k : ZMod d) x) =
      IsLocalRing.residue O (τ 0 x) ^ (p ^ k) := by
    intro k x
    induction k with
    | zero => simp
    | succ k ih =>
      have := (IsLocalRing.residue_eq_zero_iff _).2 (hfr (k : ZMod d) x)
      rw [map_sub, map_pow, sub_eq_zero] at this
      rw [Nat.cast_succ, this, ih, ← pow_mul, pow_succ]
  have hsurj : ∀ σ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e, ∃ s, τ s = σ := by
    intro σ hσ
    obtain ⟨i, hi⟩ := GlobalTheory.EmbFrob.exists_frobenius_pow p (𝓞 E) C v O hv hp w (τ 0) σ hw hσ
    refine ⟨(i : ZMod d), hsep _ _ fun x => ?_⟩
    have h1 : σ x - τ 0 x ^ (p ^ i) ∈ IsLocalRing.maximalIdeal O := by
      intro hu
      exact (hi x).ne (hv.one_of_isUnit hu)
    have := (IsLocalRing.residue_eq_zero_iff _).2 h1
    rw [map_sub, map_pow, sub_eq_zero] at this
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hpow, this, sub_self]
  have hmem' : ∀ s : ZMod d, τ s ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e := by
    intro s
    have := hmem s.val
    rwa [ZMod.natCast_zmod_val] at this
  have hbij : Function.Bijective
      (fun s : ZMod d => (⟨τ s, hmem' s⟩ : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e)) :=
    ⟨fun a b h => hτ (congrArg Subtype.val h), fun σ => by
      obtain ⟨s, hs⟩ := hsurj σ.1 σ.2
      exact ⟨s, Subtype.ext hs⟩⟩
  obtain ⟨⟨t₀⟩, -⟩ := GlobalTheory.EmbCount.card_emb E p C v O hv w.e w.idem
  have hn : w.n = d := by
    have h1 := Nat.card_congr (t₀.trans (Equiv.ofBijective _ hbij).symm)
    rw [Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    exact h1
  have hcast : Function.Bijective (fun j : Fin w.n => ((j.val : ℕ) : ZMod d)) := by
    refine ⟨fun a b h => ?_, fun s => ⟨⟨s.val, hn ▸ ZMod.val_lt s⟩, ZMod.natCast_zmod_val s⟩⟩
    have h' := congrArg ZMod.val h
    simp only [ZMod.val_natCast] at h'
    rw [Nat.mod_eq_of_lt (hn ▸ a.2), Nat.mod_eq_of_lt (hn ▸ b.2)] at h'
    exact Fin.ext h'
  let t : Fin w.n ≃ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e :=
    (Equiv.ofBijective _ hcast).trans (Equiv.ofBijective _ hbij)
  refine ⟨w, hn, t, fun j => rfl, ?_⟩
  exact GlobalTheory.tau_basis_unit_determinant.exists_basis_isUnit_det p (𝓞 E) O w (fun j => (t j).1) (fun j => (t j).2)
    (fun j j' h => t.injective (Subtype.ext (hsep _ _ h)))

end GlobalTheory.OrbitPlace
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.PullbackColumn

variable {k : Type} [CommRing k] {d : ℕ}

theorem expS_pow [Algebra ℚ k] {n : ℕ} (g : PS k n d) (hg : constantCoeff g = 0) (m : ℕ) :
    FB.expS k g ^ m = FB.expS k ((m : k) • g) := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, zero_smul, nt_expS_zero]
  | succ m ih =>
    rw [pow_succ, ih, Nat.cast_succ, add_smul, one_smul,
      gt_expS_add _ _ (by rw [nt_const_smul, hg, mul_zero]) hg]

theorem dpolyOf_monomial_one (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (mo : ι →₀ ℕ) (g : PS k 1 d) :
    DpolyOf F u (MvPolynomial.monomial mo (1 : k)) g = DmonOf F u mo g := by
  classical
  have e : DpolyOf F u (MvPolynomial.monomial mo (1 : k)) g =
      ∑ m ∈ ({mo} : Finset (ι →₀ ℕ)), C ((MvPolynomial.monomial mo (1 : k)).coeff m) * DmonOf F u m g := by
    unfold DpolyOf
    refine Finset.sum_subset MvPolynomial.support_monomial_subset fun x _ hx => ?_
    rw [MvPolynomial.notMem_support_iff.1 hx, map_zero, zero_mul]
  rw [e, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl, map_one, one_mul]

end GlobalTheory.PullbackColumn

namespace GlobalTheory

open PullbackColumn

theorem nabVal_pullback_monomial : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w0 a : O) (N m : ℕ) (w : PS R 1 d), FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) → ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → k) (α : ι → k), (∀ l, (dAct k B a).mulVec (u l) = α l • u l) → ∀ (f : PS k 1 d) (mo : ι →₀ ℕ), B.nabVal k h w0 (N * m) (ev (n := 1) ![B.actK k a] f * FB.toK k w ^ m) u (MvPolynomial.monomial mo 1) = (∏ l, α l ^ mo l) * B.nabVal k h w0 m f u (MvPolynomial.monomial mo 1) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 a N m w hw ι _ u α hα f mo
  have hA : ∀ b : O, GP (B.actK k b) := fun b => QuadDeriv.constantCoeff_mapP_eq_zero _ _ (B.A.const b)
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have cL : constantCoeff (B.hL k h w0) = 0 :=
    gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (hA w0) (gp_pt 0))) h hh0
  have cA : constantCoeff (ev (n := 1) ![B.actK k a] (B.hL k h w0)) = 0 :=
    gt_const_ev _ (single_point_zero_constant (hA a)) _ cL
  have cD : constantCoeff (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) = 0 := by
    rw [map_sub, cA, nt_const_smul, cL, mul_zero, sub_zero]
  have hG : ev (n := 1) ![B.actK k a] f * FB.toK k w ^ m * FB.expS k (((N * m : ℕ) : k) • B.hL k h w0) =
      ev (n := 1) ![B.actK k a] (f * FB.expS k ((m : k) • B.hL k h w0)) := by
    rw [hw, expS_pow _ cD, mul_assoc, ← gt_expS_add _ _ (by rw [nt_const_smul, cD, mul_zero])
      (by rw [nt_const_smul, cL, mul_zero]), gt_ev_mul _ (single_point_zero_constant (hA a)),
      gt_ev_expS _ (single_point_zero_constant (hA a)) _ (by rw [nt_const_smul, cL, mul_zero]), nt_ev_smul _ (single_point_zero_constant (hA a)),
      smul_sub, smul_smul, Nat.cast_mul, mul_comm (N : k) (m : k), sub_add_cancel]
  unfold FB.nabVal
  rw [hG, dpolyOf_monomial_one, dpolyOf_monomial_one]
  exact (invariantDeriv_along_endo R d O k B a).2 ι u α hα mo _

end GlobalTheory
end
end
