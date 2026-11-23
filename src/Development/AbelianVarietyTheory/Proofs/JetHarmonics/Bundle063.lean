module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SpansOverField
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle057
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle044
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle036
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle015
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle027
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle031
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle059
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameWConjMatrixUnits
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.TorsionFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointStepCompare

open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement
open GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace (Bil leastExponent IsIntegralFn IsPositiveFn IsBalancedSpace evalSum)

section Lattice

variable (E : Type) [Field E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]


end Lattice

section Phi

variable (E : Type) [Field E] [NumberField E]

theorem trace_pos {u : 𝓞 E} (h : ∀ τ : E →+* ℂ, 0 < (τ (u : E)).re) :
    0 < Algebra.trace ℤ (𝓞 E) u := by
  have h1 := congrArg Complex.re (trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := (u : E)))
  rw [← Algebra.coe_trace_int, Complex.re_sum] at h1
  have h2 : 0 < ∑ σ : E →ₐ[ℚ] ℂ, (σ (u : E)).re := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact Finset.sum_pos (fun σ _ => h σ.toRingHom) ⟨τ.toRatAlgHom, Finset.mem_univ _⟩
  rw [← h1] at h2
  simpa using h2

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem smul_ne_zero_of_free [Module.Free ℤ X] {c : 𝓞 E} {x : X} (hc : c ≠ 0) (hx : x ≠ 0) :
    c • x ≠ 0 := by
  intro h
  obtain ⟨r, hr, α, hα⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) c).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hc)
  have : r • x = 0 := by
    rw [← algebraMap_smul (𝓞 E) r x, hα, mul_comm, mul_smul, h, smul_zero]
  exact hx ((smul_eq_zero.1 this).resolve_left hr)

theorem projective_of_free [Module.Free ℤ X] [Module.Finite ℤ X] : Module.Projective (𝓞 E) X := by
  have : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Module.Flat (𝓞 E) X := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨c, hc⟩
    by_contra hx
    exact smul_ne_zero_of_free E (nonZeroDivisors.coe_ne_zero c) hx hc
  have : Module.FinitePresentation (𝓞 E) X := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

variable [IsCMField E]

theorem bar_bar (a : 𝓞 E) : bar E (bar E a) = a := by
  ext; simp [IsCMField.coe_ringOfIntegersComplexConj]

theorem emb_bar (τ : E →+* ℂ) (a : 𝓞 E) : τ (bar E a : E) = starRingEnd ℂ (τ (a : E)) :=
  IsCMField.complexEmbedding_complexConj E τ _

theorem trace_bar (a : 𝓞 E) : Algebra.trace ℤ (𝓞 E) (bar E a) = Algebra.trace ℤ (𝓞 E) a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.ringOfIntegersComplexConj E).restrictScalars ℤ) a

theorem sum_pos_of_isPosHerm [Module.Free ℤ X] [Module.Finite ℤ X] {n : ℕ} {x x' : Fin n → X}
    (hl : IsPosHerm E (outer E x x')) (γ : Bil X) (hγ : GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.IsBalanced E γ)
    (hp : ∀ a, 0 ≤ γ a a) (h0 : γ ≠ 0) : 0 < ∑ i, γ (x i) (x' i) := by
  obtain ⟨N, ι, _, ω, θ, hN, hsum, htr⟩ := exists_traceDual E
  have htr' : ∀ (f : X →ₗ[ℤ] ℤ) (a : X) (α : 𝓞 E),
      Algebra.trace ℤ (𝓞 E) (α * ∑ s, f (ω s • a) • θ s) = N * f (α • a) := fun f a α =>
    htr (f ∘ₗ (LinearMap.toSpanSingleton (𝓞 E) X a).restrictScalars ℤ) α
  let up : (X →ₗ[ℤ] ℤ) → Module.Dual (𝓞 E) X := fun f =>
    { toFun := fun a => ∑ s, f (ω s • a) • θ s
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        rw [← sub_eq_zero]
        refine eq_zero_of_trace_mul E fun α => ?_
        rw [mul_sub, map_sub, htr', RingHom.id_apply, smul_eq_mul, ← mul_assoc, htr', mul_smul,
          sub_self] }
  have hup : ∀ f a, up f a = ∑ s, f (ω s • a) • θ s := fun _ _ => rfl
  have key : ∀ f g : X →ₗ[ℤ] ℤ, Algebra.trace ℤ (𝓞 E) (outer E x x' (up f) (up g)) =
      N * ∑ p : Fin n × ι, f (ω p.2 • x p.1) * g (bar E (θ p.2) • x' p.1) := by
    intro f g

    rw [outer, map_sum, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [hup f, Finset.sum_mul, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e : θ s * bar E (up g (x' i)) = bar E (bar E (θ s) * up g (x' i)) := by
      conv_lhs => rw [← bar_bar E (θ s)]
      exact (map_mul (IsCMField.ringOfIntegersComplexConj E) _ _).symm
    rw [smul_mul_assoc, map_smul, e, trace_bar, hup g, htr', smul_eq_mul]
    ring
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have h1 := sum_pos_of_tensor_pos X (Fin n × ι) (fun p => ω p.2 • x p.1) (fun p => bar E (θ p.2) • x' p.1)
    (fun f g => by
      apply mul_left_cancel₀ hN'.ne'
      rw [← key, ← key, hl.1 (up g) (up f), trace_bar])
    (fun f hf => by
      have hne : up f ≠ 0 := by
        intro h
        apply hf
        ext a
        have := htr' f a 1
        rw [← hup, h] at this
        simpa [hN.ne'] using this
      have := trace_pos E (hl.2 _ hne)
      rw [key] at this
      exact pos_of_mul_pos_right this hN'.le) γ hγ.1 hp h0
  have h2 : ∑ p : Fin n × ι, γ (ω p.2 • x p.1) (bar E (θ p.2) • x' p.1) =
      N * ∑ i, γ (x i) (x' i) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∀ s, γ (ω s • x i) (bar E (θ s) • x' i) = γ ((θ s * ω s) • x i) (x' i) := fun s => by
      rw [← hγ.2, mul_smul]
    simp only [this]

    rw [← LinearMap.sum_apply, ← map_sum, ← Finset.sum_smul, hsum, Nat.cast_smul_eq_nsmul, map_nsmul,
    LinearMap.smul_apply, nsmul_eq_mul]
  rw [h2] at h1
  exact pos_of_mul_pos_right h1 (Nat.cast_nonneg N)

def rankOne (η : Module.Dual (𝓞 E) X) (τ : E →+* ℂ) : Bil X :=
  LinearMap.mk₂ ℤ (fun a c => (τ (η a : E) * starRingEnd ℂ (τ (η c : E))).re)
    (fun a a' c => by simp [add_mul])
    (fun k a c => by simp [mul_assoc, mul_add])
    (fun a c c' => by simp [mul_add])
    (fun k a c => by simp [mul_add, mul_left_comm])

omit [IsCMField E] in
theorem rankOne_apply (η : Module.Dual (𝓞 E) X) (τ : E →+* ℂ) (a c : X) :
    rankOne E η τ a c = (τ (η a : E) * starRingEnd ℂ (τ (η c : E))).re := rfl


theorem bar_outer {n : ℕ} (x x' : Fin n → X) (η η' : Module.Dual (𝓞 E) X) :
    bar E (outer E x x' η η') = outer E x' x η' η := by
  have := bar_bar E

  simp only [outer, bar, map_sum, map_mul] at this ⊢
  simp only [this, mul_comm]

theorem re_outer {n : ℕ} (x x' : Fin n → X) (η : Module.Dual (𝓞 E) X) (τ : E →+* ℂ) :
    (τ (outer E x x' η η : E)).re = ∑ i, rankOne E η τ (x i) (x' i) := by
  simp only [outer, rankOne_apply]
  push_cast

  rw [map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← emb_bar]

variable {S : Submodule ℝ (Bil X)}

variable [Module.Free ℤ X] [Module.Finite ℤ X]

theorem exists_admissible (hS : IsBalancedSpace E S) :
    ∃ l : S →ₗ[ℝ] ℝ, IsIntegralFn S l ∧ IsPositiveFn S l := by
  let b := Module.finBasis ℤ X
  refine ⟨evalSum S b b, GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.isIntegralFn_evalSum S _ _, fun γ h1 h2 => ?_⟩
  refine sum_pos_of_isPosHerm E ⟨fun η η' => (bar_outer E _ _ _ _).symm, fun η hη τ => ?_⟩ _
    ((hS _).1 γ.2) h1 fun h => h2 (Subtype.ext h)
  rw [re_outer]
  simp only [rankOne_apply, Complex.mul_conj, Complex.ofReal_re]
  refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) fun h0 => hη ?_
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1 h0.symm
  have : η.restrictScalars ℤ = 0 := b.ext fun i => by simpa using hz i (Finset.mem_univ _)
  exact LinearMap.ext fun a => LinearMap.congr_fun this a

end Phi

abbrev FormSpaces : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (_ : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    Submodule ℝ (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)

abbrev FormValues (S : FormSpaces) : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    S E cj Y → ℝ

section Clauses

variable {S : FormSpaces} {φ : FormValues S}

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  (D : DegData V (maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)

end Clauses

end GlobalTheory.PointStepCompare
end
end

section

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem ev_pow_of_intg (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (σ : Type) [Fintype σ] (x : σ → K) (hx : ∀ i, ‖x i‖ < 1) (S : MvPowerSeries σ K)
    (hS : Intg S) (k : ℕ) : ev (S ^ k) x = ev S x ^ k := by
  obtain ⟨-, halg, hC, -⟩ := GlobalTheory.T.mvPowerSeriesEvalTsum_openPolydisc_properties K σ x hx
  obtain ⟨-, -, hpow, -⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ
  have hB : Bdd S := (hpow S 0).2.2 hS
  induction k with
  | zero => simpa using hC 1
  | succ k ih => rw [pow_succ, (halg _ _ ((hpow S k).2.1 hB) hB).2.2, ih, pow_succ]

theorem exists_intg_polynomial_level (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K) (hF : Intg F.toPowerSeries)
    (t : ℕ → K) (ht : ∀ n, ‖t n‖ < 1) (h0 : t 0 = 0) (h1 : t 1 ≠ 0)
    (hp : ∀ n, ev1 (nMul F p) (t (n + 1)) = t n) (n : ℕ) (ζ : K) (hζ : ζ ^ (p ^ n) = 1) :
    ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧
      ∀ j : ℕ, g.eval (ev1 (nMul F j) (t n)) = ζ ^ j := by
  classical
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hord := (GlobalTheory.T.formalGroup_torsionTower_exact_order K p F hF t ht h0 h1 hp).2.2 n
  obtain ⟨-, -, hnorm, hadd, -⟩ := (GlobalTheory.T.formalGroupNatMulSeries_eval_openDisc_properties K F hF).2 (t n) (ht n)
  set x : ZMod (p ^ n) → K := fun i => ev1 (nMul F i.val) (t n) with hx
  have hxlt : ∀ i, ‖x i‖ < 1 := fun i => (hnorm i.val).1.trans_lt (ht n)
  have hinj : Function.Injective x := by
    intro i j hij
    have := (hord _ _).1 hij
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 this
    simpa using h2
  have hxadd : ∀ i j, x (i + j) = ev F.toPowerSeries ![x i, x j] := by
    intro i j
    simp only [hx]
    rw [hadd, hord, ZMod.val_add]
    exact Nat.mod_modEq _ _
  have hχ : ∀ i j : ZMod (p ^ n), ζ ^ (i + j).val = ζ ^ i.val * ζ ^ j.val := by
    intro i j
    rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hζ]
  have hcard : (Finset.univ.image x).card = Fintype.card (ZMod (p ^ n)) := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  obtain ⟨g, hg, hgx⟩ := GlobalTheory.T.exists_integral_poly_of_character' K (ZMod (p ^ n)) x (fun i => ζ ^ i.val) hinj hχ (by
    intro k
    have hc := GlobalTheory.T.exists_integral_coeff_interpolation_bivariate_series K (Finset.univ.image x) (F.toPowerSeries ^ (k : ℕ))
      (by
        intro y hy
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
        exact hxlt i)
      (((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K (Fin 2)).2.2.1 _ _).1 hF)
    rw [hcard] at hc
    obtain ⟨c, hc1, hc2⟩ := hc
    refine ⟨c, hc1, fun i j => ?_⟩
    rw [← hc2 _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)) _
      (Finset.mem_image_of_mem _ (Finset.mem_univ j)), hxadd,
      ev_pow_of_intg K (Fin 2) _ _ _ hF]
    intro l
    fin_cases l
    · exact hxlt i
    · exact hxlt j)
  refine ⟨g, hg, fun j => ?_⟩
  have := hgx (j : ZMod (p ^ n))
  simp only [hx, ZMod.val_natCast] at this
  rw [← pow_eq_pow_mod _ hζ] at this
  rw [← this, (hord j (j % p ^ n)).2 (Nat.mod_modEq _ _).symm]

end GlobalTheory.ConvSer
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem sum_normSq_proj_single_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, ∑ s, ‖pr s (Pi.single c w)‖ ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) * ‖w‖ ^ 2 := by
  intro M _ _ n ε E N _ _ F io pr μ kk j bv w hE hF hA hS hj hw c
  have hnorm : ∀ s, ‖pr s (Pi.single c w)‖ ^ 2 =
      ‖hhJ ε (io s (pr s (Pi.single c w))) (io s (pr s (Pi.single c w)))‖ := by
    intro s
    obtain ⟨e, he, hs⟩ := hA.sign s
    rw [hs, norm_mul, inner_self_eq_norm_sq_to_K]
    rcases he with rfl | rfl <;> simp
  have hcomp := GlobalTheory.T.unitary_glModule_proj_components_level_add_two M n ε E N F io pr μ j w hE.2.1 (fun s => (hF s).2.1) hA hw
  have hproj := GlobalTheory.T.cloudNode_projection_norm_lowLevel M n ε E N F io pr μ kk j bv w hE hF hA hS hj hw c
  have hq := GlobalTheory.T.sum_norm_hhJ_self_le_of_orthogonal M n ε (fun s => io s (pr s (Pi.single c w)))
    (univ.filter (fun a : Fin n => a.val + 1 < kk)) (18 / 13) (3 * (6 * bv) ^ (n - kk)) (‖w‖ ^ 2)
    (fun s t hst => hA.orth s t hst _ _)
    (fun s hs => GlobalTheory.T.invariantHermitianForm_nonneg_of_cloud_eigen M n ε E μ kk (j + 2) bv _ hE hS (by omega) (fun d => hcomp s c d) s
      (Finset.mem_filter.1 hs).2 (GlobalTheory.splitCas_eigenvalue_summand M n ε E N F io pr μ hE hF hA s _))
    hproj.1
    (fun s hs => hproj.2 s (by simpa using hs))
  obtain ⟨h1, h2, -, -, -, hb⟩ := hS
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnb : (n : ℝ) ≤ bv := by
    have h7 : (n : ℝ) ≤ (n : ℝ) ^ 7 := le_self_pow₀ hn1 (by norm_num)
    have : (0 : ℝ) ≤ (n : ℝ) ^ 7 := by positivity
    nlinarith
  obtain ⟨hcard, harith⟩ := GlobalTheory.card_filter_le_succ_and_sq_sum_le_pow n kk bv h1 h2 hnb
  have hcompl : (univ.filter (fun a : Fin n => a.val + 1 < kk))ᶜ =
      univ.filter (fun a : Fin n => kk ≤ a.val + 1) := by
    ext a; simp
  rw [hcompl, hcard] at hq
  rw [Finset.sum_congr rfl (fun s _ => hnorm s)]
  exact hq.trans (mul_le_mul_of_nonneg_right harith (by positivity))

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.isFRep_dual_standard_unitaryRep : ∀ (k r : ℕ), IsFRep (k := k) (r := r) dualM (Formalism.QuantumDeterminants.Hpk k r) 1 := by
  first | exact @GlobalTheory.isFRep_dualM | exact GlobalTheory.isFRep_dualM | (intros; apply GlobalTheory.isFRep_dualM <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselCharacter_unipotentRadical_properties : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ g, ‖Formalism.QuantumDeterminants.psi k r z c g‖ = 1) ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ m' ∈ Formalism.QuantumDeterminants.Nset k r, m * m' ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c (m * m') = Formalism.QuantumDeterminants.psi k r z c m * Formalism.QuantumDeterminants.psi k r z c m') ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, m⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c m⁻¹ = star (Formalism.QuantumDeterminants.psi k r z c m)) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, g * m * g⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ g⁻¹ * m * g ∈ Formalism.QuantumDeterminants.Nset k r ∧ Formalism.QuantumDeterminants.psi k r z c (g * m * g⁻¹) = Formalism.QuantumDeterminants.psi k r z c m ∧ Formalism.QuantumDeterminants.psi k r z c (g⁻¹ * m * g) = Formalism.QuantumDeterminants.psi k r z c m) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ g' ∈ Formalism.QuantumDeterminants.UWset k r z, g * g' ∈ Formalism.QuantumDeterminants.UWset k r z ∧ g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z ∧ g ∈ GG k r) ∧ ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, m ∈ GG k r := by
  first | exact @GlobalTheory.BesselPsi.psi_character | exact GlobalTheory.BesselPsi.psi_character | (intros; apply GlobalTheory.BesselPsi.psi_character <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.compoundMatrix_cauchyBinet_properties : ∀ (n l : ℕ) (g h : Matrix (Fin n) (Fin n) ℂ), cmp l (g * h) = cmp l g * cmp l h ∧ cmp l gᴴ = (cmp l g)ᴴ ∧ cmp l (1 : Matrix (Fin n) (Fin n) ℂ) = 1 ∧ ∀ f : Fin l → Fin n → ℂ, cmp l g *ᵥ wedge f = wedge (fun b => g *ᵥ f b) := by
  first | exact @GlobalTheory.compound_properties | exact GlobalTheory.compound_properties | (intros; apply GlobalTheory.compound_properties <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.discreteSeries_unitary_smooth_basic : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → (∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v)) ∧ (∀ v, R.σ 1 v = v) ∧ (∀ g ∈ GG k r, ∀ v w, ⟪R.σ g v, R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.sm, R.σ g v ∈ R.sm) ∧ (∀ v ∈ R.TK, v ∈ R.sm) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.TK, R.σ g v ∈ R.TK) ∧ (∀ v, R.KFin v → v ∈ R.TK) ∧ (∃ w, ‖w‖ = 1 ∧ R.KFin w ∧ PI.UpqRep.IsLowUnitH k r ε mu R.σ w) ∧ (∀ v, ContinuousOn (fun g => R.σ g v) (GG k r)) := by
  first | exact @GlobalTheory.rep_basic_of_isDS | exact GlobalTheory.rep_basic_of_isDS | (intros; apply GlobalTheory.rep_basic_of_isDS <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.frep_discrete_series_sum : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ I, ∀ y ∈ (RI I).sm, ∀ x : ι → R.H, (∀ c, x c ∈ R.sm) → hh Γ R (fun c => io I c y) x = (ep I : ℂ) * ⟪∑ c, pr I c (x c), y⟫_ℂ) ∧ (∀ x x' : ι → R.H, (∀ c, x c ∈ R.sm) → (∀ c, x' c ∈ R.sm) → hh Γ R x x' = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (x' c), ∑ c, pr I c (x c)⟫_ℂ) ∧ (∀ (a : ι → ℂ) (x : ι → R.H) (v : R.H), hh Γ R x (tm R a v) = ⟪v, ev Γ R a x⟫_ℂ) ∧ (∀ I, ∀ y ∈ (RI I).sm, ‖y‖ ^ 2 ≤ ∑ c, ‖io I c y‖ ^ 2) ∧ ∀ (a a' : ι → ℂ), ∀ v ∈ R.sm, ∀ v' ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a') a * ⟪v, R.σ g v'⟫_ℂ = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (tm R a v c), (RI I).σ g (∑ c, pr I c (tm R a' v' c))⟫_ℂ := by
  first | exact @GlobalTheory.TensAdj.tens_adj | exact GlobalTheory.TensAdj.tens_adj | (intros; apply GlobalTheory.TensAdj.tens_adj <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem map_sum_of_add_on_sm {k r : ℕ} (R : Rep k r) {Wp : Type} [AddCommGroup Wp] [Module ℂ Wp] (l : R.H → Wp)
    (hadd : ∀ v ∈ R.sm, ∀ w ∈ R.sm, l (v + w) = l v + l w) (hsmul : ∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v)
    {α : Type} (s : Finset α) (f : α → R.H) (hf : ∀ i, f i ∈ R.sm) : l (∑ i ∈ s, f i) = ∑ i ∈ s, l (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (0 : R.H) ∈ R.sm := R.smSub.zero_mem
    simpa using hsmul 0 0 h0
  | insert a s ha ih =>
    have hs : ∑ i ∈ s, f i ∈ R.sm := R.smSub.sum_mem fun i _ => hf i
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd _ (hf a) _ hs, ih]

theorem herm_smul_eq_sum_of_tensRaw : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (om : ι → ℂ) (l : R.H → Wp) (lI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → TensRaw ρ R RI io pr → (∀ v ∈ R.sm, ∀ w ∈ R.sm, l (v + w) = l v + l w) → (∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v) → (∀ I, ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = β I • lI I y) → ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a) om • l (R.σ g w) = ∑ I, β I • lI I ((RI I).σ g (∑ c, pr I c (tm R a w c))) := by
  intro hK k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI Wp _ _ _ _ om l lI β hR hRI hT hadd hsmul hl a w hw g hg
  have hσw : R.σ g w ∈ R.sm := (rep_basic_of_isDS hK k r ε mu R hR).2.2.2.1 g hg w hw
  have htm : ∀ c, tm R a w c ∈ R.sm := fun c => R.smSub.smul_mem (a c) hw
  have hact : ∀ c, act ρ R g (tm R a w) c = (ρ g *ᵥ a) c • R.σ g w := by
    intro c
    simp only [act, tm, map_smul, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  have hx : ∀ c, act ρ R g (tm R a w) c ∈ R.sm := fun c => by
    rw [hact]; exact R.smSub.smul_mem _ hσw
  set y : ∀ I, (RI I).H := fun I => (RI I).σ g (∑ c, pr I c (tm R a w c)) with hy
  have hyeq : ∀ I, ∑ c, pr I c (act ρ R g (tm R a w) c) = y I := fun I => hT.pr_eq I g hg _ htm
  have hysm : ∀ I, y I ∈ (RI I).sm := fun I => by
    rw [← hyeq]
    exact (RI I).smSub.sum_mem fun c _ => (hT.pr_sm I c).mem _ (hx c)
  have hdec : ∀ c, ∑ I, io I c (y I) = (ρ g *ᵥ a) c • R.σ g w := fun c => by
    rw [← hact, ← hT.sum_io_pr _ hx c]
    simp only [hyeq]
  have hev : ∀ I, ev Γ R om (fun c => io I c (y I)) ∈ R.sm := fun I =>
    R.smSub.sum_mem fun i _ => R.smSub.sum_mem fun j _ => R.smSub.smul_mem _ ((hT.io_sm I j).mem _ (hysm I))
  have hsum : ∑ I, ev Γ R om (fun c => io I c (y I)) = Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a) om • R.σ g w := by
    simp only [ev]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ I, ∑ j, (star (om i) * Γ i j) • io I j (y I)
        = ∑ j, (star (om i) * Γ i j * (ρ g *ᵥ a) j) • R.σ g w := fun i => by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.smul_sum, hdec, smul_smul]
    simp only [this, ← Finset.sum_smul]
    congr 1
    generalize ρ g *ᵥ a = b
    simp only [Formalism.QuantumDeterminants.herm, Matrix.mulVec, dotProduct, Finset.mul_sum, Pi.star_apply, mul_assoc]
  rw [← hsmul _ _ hσw, ← hsum, map_sum_of_add_on_sm R l hadd hsmul _ _ hev]
  exact Finset.sum_congr rfl fun I _ => hl I _ (hysm I)

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.sum_norm_sq_herm_translates_orthonormal : ∀ (k r : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : Mx k r → Matrix ι ι ℂ) (Γ U : Matrix ι ι ℂ) (d : ℕ) (om : ι → ℂ), IsFRep ρ Γ d → U ∈ Matrix.unitaryGroup ι ℂ → ∀ g ∈ GG k r, ∑ e, ‖Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ (fun c => U e c)) om‖ ^ 2 = ∑ i, ‖(ρ g⁻¹ *ᵥ om) i‖ ^ 2 := by
  first | exact @GlobalTheory.MomentParseval.sum_herm_sq | exact GlobalTheory.MomentParseval.sum_herm_sq | (intros; apply GlobalTheory.MomentParseval.sum_herm_sq <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.frameW_conj_matrix_units : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : Mx k r), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.UpqRep.IsFrameW k r z g → IsUnit g ∧ (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → (g * Matrix.single a b (1 : ℂ) * g⁻¹) i j = 0) ∧ ‖Formalism.QuantumDeterminants.ell k r z (g * Matrix.single a b 1 * g⁻¹) - star (Formalism.QuantumDeterminants.ell k r z (-((Formalism.QuantumDeterminants.Hpk k r) * (g * Matrix.single a b (1 : ℂ) * g⁻¹)ᴴ * (Formalism.QuantumDeterminants.Hpk k r))))‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) else 0)) ∧ (Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] (fun i : Fin k => g *ᵥ Pi.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) 1) ∧ ∀ i j : Fin k, Formalism.FourierDecayAlt.Q.unitB (Formalism.QuantumDeterminants.Hpk k r) (fun i : Fin k => g *ᵥ Pi.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) 1) i j = g * Matrix.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) 1 * g⁻¹) ∧ g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z 0 = (if r = 0 then ((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) • Pi.single (Fin.last (2 * r + k)) 1 else Pi.single 0 1) ∧ gᵀ *ᵥ (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) = (if r = 0 then -((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) else 1) • Pi.single (Fin.last (2 * r + k)) 1 := by
  first | exact @GlobalTheory.CapFrame.frame_matrix_units | exact GlobalTheory.CapFrame.frame_matrix_units | (intros; apply GlobalTheory.CapFrame.frame_matrix_units <;> assumption)
end
