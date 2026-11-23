module

public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle002
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle329
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle249
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle002
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle335
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Mathlib.FieldTheory.Finite.Basic
public import ReciprocityTheory.DualLattices.Bundle008
public import ReciprocityTheory.DualLattices.Bundle010
public import ReciprocityTheory.DualLattices.Bundle016
import ReciprocityTheory.DualLattices.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.DetLe

theorem re_det_one_sub_le_of_unique {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι] [Unique ι]
    (Z : Matrix κ ι ℂ) : ((1 - Zᴴ * Z).det).re ≤ 1 := by
  rw [Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.sub_re, Complex.one_re, Complex.re_sum]
  have : ∀ a : κ, 0 ≤ (star (Z a default) * Z a default).re := by
    intro a
    rw [show star (Z a default) = (starRingEnd ℂ) (Z a default) from rfl, mul_comm, Complex.mul_conj]
    simp [Complex.normSq_nonneg]
  linarith [Finset.sum_nonneg fun a (_ : a ∈ Finset.univ) => this a]

theorem re_det_one_sub_le_of_unique' {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] [Unique κ] (Z : Matrix κ ι ℂ) : ((1 - Zᴴ * Z).det).re ≤ 1 := by
  rw [Matrix.det_one_sub_mul_comm]
  have := re_det_one_sub_le_of_unique (Zᴴ)
  rwa [Matrix.conjTranspose_conjTranspose] at this

end GlobalTheory.IntBall.DetLe

namespace GlobalTheory.IntBall

open GlobalTheory.IntBall.DetLe

theorem zDet_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 1 ∨ X.p0 + 1 = r) → ∀ z : V (nd X), z ∈ Om X → ∀ τ : X.Ψ, zDet X z τ ≤ 1 := by
  intro E _ _ _ r X h z _ τ
  have hle := X.p0_le
  unfold zDet
  rcases h with h | h
  · letI : Unique {b : Fin r // (b : ℕ) < X.p0} :=
      { default := ⟨⟨0, by omega⟩, by simp [h]⟩
        uniq := fun b => Subtype.ext (Fin.ext (by have := b.2; simp only; omega)) }
    exact re_det_one_sub_le_of_unique _
  · letI : Unique {a : Fin r // X.p0 ≤ (a : ℕ)} :=
      { default := ⟨⟨X.p0, by omega⟩, le_refl _⟩
        uniq := fun a => Subtype.ext (Fin.ext (by have := a.2; have := a.1.2; simp only; omega)) }
    exact re_det_one_sub_le_of_unique' _

end GlobalTheory.IntBall
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem prod_rootSum_map_algEquiv : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F']
    (θ : AlgebraicClosure F' →* ℂ) (k : ℕ) (P : F'[X]),
    ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F')) =
      ∏ j ∈ Finset.range (Module.finrank F F'), rootSum θ (k * Nat.card F ^ j) P := by
  intro F F' _ _ _ _ θ k P
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  letI := Fintype.ofFinite F
  have hb := FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F'
  rw [← Fintype.prod_bijective _ hb
    (fun n => rootSum θ k (P.map ((FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ n.1 : F' ≃ₐ[F] F') : F' →+* F')))
    _ (fun _ => rfl)]
  rw [Finset.prod_range (fun j => rootSum θ (k * Nat.card F ^ j) P)]
  refine Finset.prod_congr rfl fun n _ => ?_
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨r, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
  have key := GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul F' θ
    ((FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ n.1 : F' ≃ₐ[F] F') : F' →+* F') (r * n.1) (fun x => by
      rw [hchar, pow_mul, ← hcard]
      show (FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ n.1) x = _
      rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]) k P
  rw [key, hchar, pow_mul, ← hcard, Nat.card_eq_fintype_card]

end GlobalTheory.Shin
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in
private theorem exists_eisensteinCombination_of_isModularForm {w : ℕ} {F : ℍ → ℂ}
    (hF : _root_.ReciprocityTheory.ChartRestriction.L1.IsMF (w : ℤ) F) :
    ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ), (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧
      ∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  obtain ⟨f, hf⟩ := hF
  have hmem := _root_.ReciprocityTheory.PGsh.coe_mem_monoSpanF w f
  unfold _root_.ReciprocityTheory.PGsh.monoSpanF at hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  classical
  refine ⟨(_root_.ReciprocityTheory.PGsh.monoIdx w).image fun a => (a, _root_.ReciprocityTheory.PGsh.monoB w a),
    fun p => if hp : p.1 ∈ _root_.ReciprocityTheory.PGsh.monoIdx w then c ⟨p.1, hp⟩ else 0, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp
    exact _root_.ReciprocityTheory.PGsh.monoIdx_wt ha
  · intro τ
    rw [Finset.sum_image (fun x _ y _ h => congrArg Prod.fst h), ← hf τ, ← hc]
    rw [Finset.sum_apply, ← Finset.sum_attach (_root_.ReciprocityTheory.PGsh.monoIdx w)]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, a.2, dif_pos]
    rw [_root_.ReciprocityTheory.PGsh.coe_monoW a.2]
    rfl

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in
private theorem qConj_eisensteinCombination (g : ℂ ≃+* ℂ) {N : ℕ}
    (hN : 0 < N) {ι : Type} (s : Finset ι) (c : ι → ℂ) (u v : ι → ℕ) :
    _root_.GlobalTheory.QFam.QConj g N (fun τ => ∑ i ∈ s, c i * (E₄ τ ^ u i * E₆ τ ^ v i))
      (fun τ => ∑ i ∈ s, g (c i) * (E₄ τ ^ u i * E₆ τ ^ v i)) := by
  refine _root_.GlobalTheory.QFam.QConj.sum s fun i _ => ?_
  have h₄ := _root_.GlobalTheory.QFam.eis_qConj N hN _ (Or.inl rfl) g
  have h₆ := _root_.GlobalTheory.QFam.eis_qConj N hN _ (Or.inr (Or.inl rfl)) g
  exact (_root_.GlobalTheory.QFam.QConj.const g N (c i)).mul hN
    ((h₄.pow hN (u i)).mul hN (h₆.pow hN (v i)))


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in
theorem _root_.GlobalTheory.QFam.levelPoly_conj : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ),
    0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → _root_.GlobalTheory.QFam.QConj g N F F' →
    ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ), (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧
      (∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ∧
      ∀ τ, F' τ = ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  intro g w N F F' hN hinv hconj
  obtain ⟨a, ha, ha'⟩ := hconj
  obtain ⟨s, c, hw, hF⟩ := exists_eisensteinCombination_of_isModularForm
    (_root_.GlobalTheory.QFam.isMF_of_invariant_of_hasQ N w F a hN hinv ha)
  refine ⟨s, c, hw, hF, ?_⟩
  obtain ⟨b, hb, hb'⟩ :=
    qConj_eisensteinCombination g hN s c Prod.fst Prod.snd
  have hFeq : F = fun τ => ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := funext hF
  rw [← hFeq] at hb
  have hab : a = b := ha.coeff_unique hN hb
  subst hab
  intro τ
  exact congrFun (ha'.fun_unique hb') τ

end GlobalTheory.QFam
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.G2_add_weierstrassP_row_sum : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 2) (EisensteinSeries.G2 τ + (tauPair τ).weierstrassP z) := by
  first | exact @GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP | exact GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP | (intros; apply GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.eisenstein_delta_qExpansion_integrality : ∀ (N : ℕ), 0 < N → ∀ F : ℍ → ℂ, (F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD) → (∃ a : ℕ → ℤ, HasQ N F fun n => (a n : ℂ)) ∧ (∀ R : Subring ℂ, QAll (· ∈ R) N F) ∧ ∀ g : ℂ ≃+* ℂ, QConj g N F F := by
  first | exact @GlobalTheory.QFam.eis_q | exact GlobalTheory.QFam.eis_q | (intros; apply GlobalTheory.QFam.eis_q <;> assumption)
end

section

noncomputable section

open WittVector Ideal

namespace GlobalTheory.AinfXi

section Tilt

variable {p : ℕ} [hp : Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]

theorem coeff_pow_pow_zero (x : PreTilt O p) (n : ℕ) :
    PreTilt.coeff n x ^ p ^ n = PreTilt.coeff 0 x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, PreTilt.coeff_pow_p, ih]

theorem isUnit_of_coeff_zero {x : PreTilt O p} (h : IsUnit (PreTilt.coeff 0 x)) : IsUnit x := by
  have hn : ∀ n, IsUnit (PreTilt.coeff n x) := fun n =>
    (isUnit_pow_iff (pow_ne_zero n hp.out.ne_zero)).1 (by rw [coeff_pow_pow_zero]; exact h)
  have hu : ∀ n, (hn (n + 1)).unit ^ p = (hn n).unit := fun n =>
    Units.ext (by simp [PreTilt.coeff_pow_p])
  let f : ℕ → ModP O p := fun n => (((hn n).unit⁻¹ : (ModP O p)ˣ) : ModP O p)
  have hf : ∀ n, f (n + 1) ^ p = f n := fun n => by
    simp only [f]
    rw [← Units.val_pow_eq_pow_val, inv_pow, hu]
  let y : PreTilt O p := (⟨f, hf⟩ : Perfection (ModP O p) p)
  refine isUnit_iff_exists_inv.2 ⟨y, ?_⟩
  refine Perfection.ext fun n => ?_
  change PreTilt.coeff n (x * y) = PreTilt.coeff n 1
  rw [map_mul, map_one]
  change PreTilt.coeff n x * f n = 1
  exact IsUnit.mul_val_inv (hn n)

end Tilt

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]

theorem witt_isUnit (c : WittVector p R) (h : IsUnit (constantCoeff c)) : IsUnit c := by
  obtain ⟨u, hu⟩ := h
  have hmem : c * teichmuller p ((u⁻¹ : Rˣ) : R) - 1 ∈ span {(p : WittVector p R)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul, map_one, ← hu,
      constantCoeff_apply (x := teichmuller p _), teichmuller_coeff_zero, Units.mul_inv, sub_self]
  have hj := IsAdicComplete.le_jacobson_bot (span {(p : WittVector p R)}) hmem
  have h1 := (mem_jacobson_bot.1 hj) 1
  rw [mul_one, sub_add_cancel] at h1
  exact isUnit_of_mul_isUnit_left h1

end Witt

section Main

open GlobalTheory.Sandwich

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

theorem isDomain_ainf (hv : v.Integers O) : IsDomain (Ainf p O) := by
  have : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  infer_instance

theorem isLocalRing_preTilt (hv : v.Integers O) : IsLocalRing (PreTilt O p) := by
  have : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  haveI : IsLocalRing O := ReciprocityTheory.PGsh.Ainf.O_local O hv
  haveI : Nontrivial (ModP O p) := ReciprocityTheory.PGsh.Ainf.quot_nontrivial _ (by
    rw [Ne, Ideal.span_singleton_eq_top]; exact Fact.out)
  haveI : IsLocalRing (ModP O p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (PreTilt.coeff 0 a) with h | h
  · exact Or.inl (isUnit_of_coeff_zero h)
  · exact Or.inr (isUnit_of_coeff_zero (by rwa [map_sub, map_one]))

theorem isLocalRing_ainf (hv : v.Integers O) : IsLocalRing (Ainf p O) := by
  haveI := isDomain_ainf (p := p) hv
  haveI := isLocalRing_preTilt (p := p) hv
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (constantCoeff a) with h | h
  · exact Or.inl (witt_isUnit a h)
  · exact Or.inr (witt_isUnit _ (by rwa [map_sub, map_one]))

variable (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (root ε).untilt p)
include hv hε

theorem ker_theta : RingHom.ker (fontaineTheta O p) = span {xi ε} :=
  ReciprocityTheory.PGsh.Ainf.ker_theta p O hv ε hε

theorem xi_nzd (y : Ainf p O) (hy : y * xi ε = 0) : y = 0 :=
  ReciprocityTheory.PGsh.Ainf.xi_nzd p O hv ε hε y hy

theorem dvd_of_dvd_mul_p (N : ℕ) (z : Ainf p O) (h : xi ε ^ N ∣ z * p) : xi ε ^ N ∣ z := by
  induction N generalizing z with
  | zero => simp
  | succ N ih =>
    obtain ⟨w, hw⟩ := h
    have h1 : fontaineTheta O p (z * p) = 0 := by
      rw [hw, map_mul, map_pow,
        show fontaineTheta O p (xi ε) = 0 from ReciprocityTheory.PGsh.Ainf.theta_xi p O hv ε hε,
        zero_pow (Nat.succ_ne_zero _), zero_mul]
    rw [map_mul, map_natCast] at h1
    have h0 : fontaineTheta O p z = 0 :=
      ReciprocityTheory.PGsh.Ainf.torsion_free p O hv 1 _ (by rw [pow_one]; exact h1)
    obtain ⟨z1, rfl⟩ := mem_span_singleton'.1 (by rw [← ker_theta hv ε hε]; exact h0)
    have h2 : (z1 * p - xi ε ^ N * w) * xi ε = 0 := by linear_combination hw
    obtain ⟨w', hw'⟩ := ih z1 ⟨w, sub_eq_zero.1 (xi_nzd hv ε hε _ h2)⟩
    exact ⟨w', by rw [hw']; ring⟩

theorem coeff_zero_eq_zero (x : Ainf p O) (hx : ∀ N, xi ε ^ N ∣ x) : constantCoeff x = 0 := by
  obtain ⟨⟨pf, hpf⟩, -, -, hX, -, -⟩ := ReciprocityTheory.PGsh.a0 p C v O hv
  obtain ⟨u, hu⟩ := ((hX ε hv hε).2.2.2 pf hpf).2
  have hu' : xi ε = u * ((p : Ainf p O) - teichmuller p pf) := hu
  have hxi : constantCoeff (xi ε) = constantCoeff (u : Ainf p O) * (-pf) := by
    rw [hu', map_mul, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub,
      constantCoeff_apply (x := teichmuller p pf), teichmuller_coeff_zero]
  refine Perfection.ext fun n => ?_
  obtain ⟨w, hw⟩ := hx (p ^ n)
  change PreTilt.coeff n (constantCoeff x) = PreTilt.coeff n 0
  have h0 : PreTilt.coeff n (-pf) ^ p ^ n = 0 := by
    rw [coeff_pow_pow_zero, map_neg, ← PreTilt.mk_untilt_eq_coeff_zero, hpf, neg_eq_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  simp only [hw, hxi, map_mul, map_pow, mul_pow]
  rw [h0, mul_zero, zero_mul, map_zero]

theorem eq_zero_of_forall_dvd (x : Ainf p O) (hx : ∀ N, xi ε ^ N ∣ x) : x = 0 := by
  have key : ∀ k, ∀ x : Ainf p O, (∀ N, xi ε ^ N ∣ x) → (p : Ainf p O) ^ k ∣ x := by
    intro k
    induction k with
    | zero => intro x _; rw [pow_zero]; exact one_dvd _
    | succ k ih =>
      intro x hx
      have h0 := coeff_zero_eq_zero hv ε hε x hx
      rw [constantCoeff_apply] at h0
      obtain ⟨z, rfl⟩ := mem_span_singleton'.1 ((mem_span_p_iff_coeff_zero_eq_zero x).2 h0)
      obtain ⟨w, hw⟩ := ih z fun N => dvd_of_dvd_mul_p hv ε hε N z (hx N)
      exact ⟨w, by rw [hw]; ring⟩
  ext n
  have h := (mem_span_p_pow_iff_le_coeff_eq_zero x (n + 1)).1
    (mem_span_singleton.2 (key (n + 1) x hx)) n (Nat.lt_succ_self n)
  simpa using h

theorem exists_order (x : Ainf p O) (hx : x ≠ 0) :
    ∃ (N : ℕ) (y : Ainf p O), x = xi ε ^ N * y ∧ fontaineTheta O p y ≠ 0 := by
  classical
  have hex : ∃ N, ¬ xi ε ^ N ∣ x := by
    by_contra h
    exact hx (eq_zero_of_forall_dvd hv ε hε x fun N => by_contra fun h' => h ⟨N, h'⟩)
  have hM := Nat.find_spec hex
  have hM0 : Nat.find hex ≠ 0 := fun h => hM (by rw [h, pow_zero]; exact one_dvd _)
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero hM0
  obtain ⟨y, hy⟩ : xi ε ^ N ∣ x := not_not.1 (Nat.find_min hex (by omega))
  refine ⟨N, y, hy, fun h0 => hM ?_⟩
  obtain ⟨y1, rfl⟩ := mem_span_singleton'.1 (by rw [← ker_theta hv ε hε]; exact h0)
  rw [hN, Nat.succ_eq_add_one]
  exact ⟨y1, by rw [hy]; ring⟩

end Main

section Statement

open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix

theorem ainf_local_xi_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ ε : PreTilt O p, IsPrimitiveRoot (root ε).untilt p → IsDomain (Ainf p O) ∧ IsLocalRing (Ainf p O) ∧ RingHom.ker (WittVector.fontaineTheta O p) = Ideal.span {xi ε} ∧ Function.Surjective (WittVector.fontaineTheta O p) ∧ WittVector.fontaineTheta O p (nu ε) ≠ 0 ∧ xi ε ≠ 0 ∧ (∀ x : Ainf p O, x ≠ 0 → ∃ (N : ℕ) (y : Ainf p O), x = xi ε ^ N * y ∧ WittVector.fontaineTheta O p y ≠ 0) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε
  haveI := isDomain_ainf (p := p) hv
  refine ⟨inferInstance, isLocalRing_ainf hv, ker_theta hv ε hε,
    ReciprocityTheory.PGsh.Ainf.theta_surj p O hv, ReciprocityTheory.PGsh.Ainf.theta_nu p O hv ε hε, fun h => ?_,
    fun x hx => exists_order hv ε hε x hx⟩
  exact one_ne_zero (xi_nzd hv ε hε 1 (by rw [h, mul_zero]))

end Statement

end GlobalTheory.AinfXi
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_jet_factor {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) {k : K.K} {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C) (hd : f₁.deg = f₂.deg)
    (hJ : ∀ a, n a ∈ T.J) (hn : ∀ a b, n a * n b = 0)
    (hf : ∀ x : Hol (K.W k), f₂.φ x = f₁.φ x + ∑ a, f₁.φ (dw a x : Hol (K.W k)) * n a) :
    ∃ χ : K.jet k ⟶ T, χ.deg = f₁.deg ∧ jet0 k ≫ χ = f₁ ∧ jet1 k ≫ χ = f₂ ∧
      ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)),
        χ.φ x = f₁.φ (x.fst : Hol (K.W k)) + ∑ a, f₁.φ (x.snd a : Hol (K.W k)) * n a := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | exact @_root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | exact _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | (apply _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet ..)

end GlobalTheory.AnPer.Charts
end
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.cechDifferential_adjoint_cupProductPairing : ∀ (k : Type) [Field k] (d : ℕ) (E : Type) [AddCommGroup E] [Module k E] (E' : Type) [AddCommGroup E'] [Module k E'] (A : Finset (Fin (d + 1)) → Submodule k E) (B : Finset (Fin (d + 1)) → Submodule k E') (β : E →ₗ[k] E' →ₗ[k] k), (∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) → (∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t) → (∀ i, (Finset.univ.erase i).Nonempty → ∀ a ∈ A (Finset.univ.erase i), ∀ b ∈ B (Finset.univ.erase i), β a b = 0) → Adj (cech A) (cech B) (cupPair β) d := by
  first | (exact @GlobalTheory.PD.CupAdj.cech_adj) | (exact GlobalTheory.PD.CupAdj.cech_adj) | (intros; apply GlobalTheory.PD.CupAdj.cech_adj  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_filtered_colimit_of_etale_of_indEt : ∀ (A O : Type) [CommRing A] [CommRing O] [Algebra A O], IndEt A O → ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ Under (CommRingCat.of A)) (ι : D ⟶ (Functor.const J).obj (Under.mk (CommRingCat.ofHom (algebraMap A O)))), Nonempty (IsColimit (Cocone.mk _ ι)) ∧ ∀ j, (D.obj j).hom.hom.Etale := by
  first | (exact @GlobalTheory.EtC.exists_filtered_colimit_etale_of_indEt) | (exact GlobalTheory.EtC.exists_filtered_colimit_etale_of_indEt) | (intros; apply GlobalTheory.EtC.exists_filtered_colimit_etale_of_indEt  <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.isOpen_atlasSectionNonvanishingSet_and_mem_iff : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → IsOpen (nz A τ) ∧ ∀ i y, y ∈ (A.chart i).source → (y ∈ nz A τ ↔ τ i y ≠ 0) := by
  first | exact @GlobalTheory.OTY.isOpen_nz_and_mem_nz_iff | exact GlobalTheory.OTY.isOpen_nz_and_mem_nz_iff | (intros; apply GlobalTheory.OTY.isOpen_nz_and_mem_nz_iff <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.sq_sqrt_add_mul_le_of_twisted_absorption : ∀ (T x u g t k1 k2 E : ℝ), 0 ≤ u → 0 ≤ g → 0 < k2 → 0 < E → |t| ≤ 3 / 4 → wT T x / 8 ≤ (1 - k1 ^ 2 / k2) * E → ((-T - 1 ≤ x ∧ x ≤ -T + 1) → E / k2 ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (k1 ^ 2 / k2)) * E) → (¬ (-T - 1 ≤ x ∧ x ≤ -T + 1) → t = 0) → (Real.sqrt (t ^ 2 * g ^ 2 / k2) + u * Real.sqrt (k1 ^ 2 / k2)) ^ 2 * E + u ^ 2 * (wT T x / 8) ≤ u ^ 2 * E + (if (-T - 1 ≤ x ∧ x ≤ -T + 1) then 15 / 4 * g ^ 2 else 0) := by
  first | exact @GlobalTheory.pointwise_absorption_twisted | exact GlobalTheory.pointwise_absorption_twisted | (intros; apply GlobalTheory.pointwise_absorption_twisted <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.atlasSections_mul_div_nonvanishing_isOpen : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), (∀ (la mu : La) (a b : ι → Y → ℂ), A.IsSec la a → A.IsSec mu b → A.IsSec (la + mu) (fun i y => a i y * b i y) ∧ ∀ y, A.nsq (la + mu) (fun i y => a i y * b i y) y = A.nsq la a y * A.nsq mu b y) ∧ (∀ (la : La) (a : ι → Y → ℂ), A.IsSec la a → IsOpen (nz A a)) ∧ (∀ (B la : La) (a b : ι → Y → ℂ) (U : Set Y), A.IsSec (B + la) a → A.IsSec B b → (∀ y ∈ U, a (A.pick y) y ≠ 0 ∧ b (A.pick y) y ≠ 0) → A.IsFrameOn la U (fun i y => a i y / b i y)) := by
  first | exact @GlobalTheory.OTY.sections_prod_quot_open | exact GlobalTheory.OTY.sections_prod_quot_open | (intros; apply GlobalTheory.OTY.sections_prod_quot_open <;> assumption)
end
