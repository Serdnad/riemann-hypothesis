module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle166
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle174
public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle175
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.RingTheory.Localization.NormTrace

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory

section TraceFormSpan

variable {ι K L : Type} [Field K] [Field L] [Algebra K L] {a : ℕ}

theorem map_mem_span_map_of_mem_span (A : ι → Matrix (Fin a) (Fin a) K)
    {x : Matrix (Fin a) (Fin a) K} (hx : x ∈ Submodule.span K (Set.range A)) :
    x.map (algebraMap K L) ∈
      Submodule.span L (Set.range fun g => (A g).map (algebraMap K L)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero =>
    rw [Matrix.map_zero _ (map_zero _)]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [Matrix.map_add _ (map_add _)]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have : (c • y).map (algebraMap K L) = algebraMap K L c • y.map (algebraMap K L) := by
      ext i j; simp
    rw [this]
    exact Submodule.smul_mem _ _ hy

theorem map_linearForm_mem_span_of_mem_span_map (A : ι → Matrix (Fin a) (Fin a) K)
    {y : Matrix (Fin a) (Fin a) L}
    (hy : y ∈ Submodule.span L (Set.range fun g => (A g).map (algebraMap K L)))
    (φ : L →ₗ[K] K) : y.map φ ∈ Submodule.span K (Set.range A) := by
  induction hy using Submodule.span_induction generalizing φ with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    have : ((A g).map (algebraMap K L)).map φ = φ 1 • A g := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]
    beta_reduce
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  | zero =>
    rw [Matrix.map_zero _ (map_zero _)]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [Matrix.map_add _ (map_add _)]
    exact Submodule.add_mem _ (hy φ) (hz φ)
  | smul c y _ hy =>
    have : (c • y).map φ = y.map (φ ∘ₗ LinearMap.mulLeft K c) := by
      ext i j; simp
    rw [this]
    exact hy _

theorem trace_map_linearForm_mul (φ : L →ₗ[K] K) (y : Matrix (Fin a) (Fin a) L)
    (m : Matrix (Fin a) (Fin a) K) :
    (y.map φ * m).trace = φ ((y * m.map (algebraMap K L)).trace) := by

  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (y i j), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem traceForm_span_nondegenerate_map_iff (A : ι → Matrix (Fin a) (Fin a) K) :
    (∀ x ∈ Submodule.span L (Set.range fun g => (A g).map (algebraMap K L)),
      (∀ g, (x * (A g).map (algebraMap K L)).trace = 0) → x = 0) ↔
    (∀ x ∈ Submodule.span K (Set.range A), (∀ g, (x * A g).trace = 0) → x = 0) := by
  constructor
  · intro h x hx htr
    have h0 := h _ (map_mem_span_map_of_mem_span A hx) fun g => by
      rw [← Matrix.map_mul, ← AddMonoidHom.map_trace, htr g, map_zero]
    ext i j
    have := congrFun (congrFun h0 i) j
    simpa using this
  · intro h y hy htr
    ext i j
    refine (Module.forall_dual_apply_eq_zero_iff K _).1 fun φ => ?_
    have h0 := h _ (map_linearForm_mem_span_of_mem_span_map A hy φ) fun g => by
      rw [trace_map_linearForm_mul, htr g, map_zero]
    simpa using congrFun (congrFun h0 i) j

end TraceFormSpan

theorem traceForm_span_rep_nondegenerate_mapRep_iff :
    ∀ (Γ K L : Type) [Group Γ] [Field K] [Field L] (f : K →+* L) (a : ℕ) (ρ : Γ →* GL (Fin a) K), (∀ x ∈ Submodule.span L (Set.range fun g => ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)), (∀ g, (x * ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)).trace = 0) → x = 0) ↔ (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) := by
  intro Γ K L _ _ _ f a ρ
  letI := f.toAlgebra
  exact traceForm_span_nondegenerate_map_iff (L := L)
    (fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K))

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.TraceSemisimple

def spanAlg {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (ρ : Γ →* GL (Fin a) K) :
    Subalgebra K (Matrix (Fin a) (Fin a) K) :=
  (Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K))).toSubalgebra
    (Submodule.subset_span ⟨1, by simp⟩)
    (by
      intro x y hx hy
      have h := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at h
      refine Submodule.span_mono ?_ h
      rintro _ ⟨_, ⟨g, rfl⟩, _, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, by simp⟩)

theorem mem_spanAlg {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (ρ : Γ →* GL (Fin a) K)
    (x : Matrix (Fin a) (Fin a) K) :
    x ∈ spanAlg ρ ↔ x ∈ Submodule.span K
      (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)) := Iff.rfl

theorem isSemisimpleRing_spanAlg {Γ K : Type} [Group Γ] [Field K] {a : ℕ}
    (ρ : Γ →* GL (Fin a) K)
    (h : ∀ x ∈ Submodule.span K
      (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)),
      (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) :
    IsSemisimpleRing (spanAlg ρ) := by
  have : IsArtinianRing (spanAlg ρ) := IsArtinianRing.of_finite K _
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  apply Subtype.ext
  refine h x.1 x.2 fun g => ?_
  let y : spanAlg ρ := ⟨(ρ g : GL (Fin a) K), Submodule.subset_span ⟨g, rfl⟩⟩
  have hxy : x * y ∈ Ring.jacobson (spanAlg ρ) := Ideal.mul_mem_right _ _ hx
  obtain ⟨n, hn⟩ : IsNilpotent (Ring.jacobson (spanAlg ρ)) := IsSemiprimaryRing.isNilpotent
  have h1 : (x * y) ^ n = 0 := by
    have := Ideal.pow_mem_pow hxy n
    rw [hn] at this
    simpa using this
  have h2 : IsNilpotent ((x * y : spanAlg ρ) : Matrix (Fin a) (Fin a) K) :=
    ⟨n, by simpa using congrArg Subtype.val h1⟩
  exact (Matrix.isNilpotent_trace_of_isNilpotent h2).eq_zero

theorem isSSRep_of_trace_nondegenerate :
    ∀ (Γ K : Type) [Group Γ] [Field K] (a : ℕ) (ρ : Γ →* GL (Fin a) K),
    (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)),
      (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) →
    IsSSRep ρ := by
  intro Γ K _ _ a ρ h W hW
  have := isSemisimpleRing_spanAlg ρ h
  let f : spanAlg ρ →+* Module.End K (Fin a → K) :=
    ((Matrix.toLinAlgEquiv' (R := K) (n := Fin a)).toAlgHom.comp (spanAlg ρ).val).toRingHom
  let : Module (spanAlg ρ) (Fin a → K) := Module.compHom _ f
  have hW' : ∀ x ∈ Submodule.span K
      (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)),
      ∀ v ∈ W, x.mulVec v ∈ W := by
    intro x hx v hv
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hW g v hv
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact W.add_mem hx hy
    | smul c x _ hx => rw [Matrix.smul_mulVec]; exact W.smul_mem c hx
  let U : Submodule (spanAlg ρ) (Fin a → K) :=
    { toAddSubmonoid := W.toAddSubmonoid
      smul_mem' := fun x v hv => hW' x.1 x.2 v hv }
  obtain ⟨U', hU⟩ := exists_isCompl U
  let W' : Submodule K (Fin a → K) :=
    { toAddSubmonoid := U'.toAddSubmonoid
      smul_mem' := fun c v hv => by
        have : (c • (1 : Matrix (Fin a) (Fin a) K)).mulVec v ∈ U' :=
          U'.smul_mem ⟨c • 1, (spanAlg ρ).smul_mem (spanAlg ρ).one_mem c⟩ hv
        rwa [Matrix.smul_mulVec, Matrix.one_mulVec] at this }
  refine ⟨W', fun g v hv => ?_, ?_, ?_⟩
  · exact U'.smul_mem ⟨(ρ g : GL (Fin a) K), Submodule.subset_span ⟨g, rfl⟩⟩ hv
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    exact (Submodule.disjoint_def.1 hU.disjoint) v hv hv'
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have : v ∈ U ⊔ U' := by rw [hU.sup_eq_top]; trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 this
    exact Submodule.add_mem_sup hx hy

end GlobalTheory.TraceSemisimple
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.LocIneq

theorem term_prime_pow (b : ℕ → ℂ) (s : ℝ) (p : ℕ) (hp : p.Prime) (e : ℕ) :
    LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e) = b (p ^ e) * ((1 / (p : ℝ) ^ (1 + s) : ℝ) : ℂ) ^ e := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hne : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [LSeries.term_of_ne_zero hne]
  have h1 : ((p ^ e : ℕ) : ℂ) ^ ((1 + s : ℝ) : ℂ) = ((((p : ℝ) ^ (1 + s)) ^ e : ℝ) : ℂ) := by
    rw [show ((p ^ e : ℕ) : ℂ) = (((p ^ e : ℕ) : ℝ) : ℂ) by push_cast; rfl]
    rw [← Complex.ofReal_cpow (Nat.cast_nonneg _)]
    congr 1
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul hp0, mul_comm, Real.rpow_mul_natCast hp0]
  rw [h1, div_eq_mul_inv]
  congr 1
  push_cast
  rw [one_div, inv_pow]

theorem real_term_prime_pow (b : ℕ → ℂ) (s : ℝ) (p : ℕ) (e : ℕ) :
    ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) = ‖b (p ^ e)‖ ^ 2 * (1 / (p : ℝ) ^ (1 + s)) ^ e := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul hp0, mul_comm, Real.rpow_mul_natCast hp0, div_eq_mul_inv,
    one_div, inv_pow]

theorem local_positivity_eulerFactor : ∀ (b ω : ℕ → ℂ) (s C : ℝ) (p : ℕ), 0 < s → p.Prime → b 1 = 1 → ‖ω p‖ = 1 → (∀ r : ℕ, b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → Real.exp (‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ * ‖∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e)‖ ^ 2 * (∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s)) * (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ := by
  intro b ω s C p hs hp hb1 hω hrec hbd
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hC : 0 ≤ C := by
    have := hbd 1
    rw [hb1] at this
    simp at this
    linarith
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (b p ^ 2 - 4 * ω p)
  set x : ℂ := (b p + z) / 2 with hx
  set y : ℂ := (b p - z) / 2 with hy
  have hxy : x + y = b p := by rw [hx, hy]; ring
  have hxy' : x * y = ω p := by rw [hx, hy]; linear_combination (1 / 4 : ℂ) * hz
  have hc0 : b (p ^ 0) = 1 := by simpa using hb1
  have hc1 : b (p ^ 1) = x + y := by rw [pow_one, hxy]
  have hcr : ∀ r, b (p ^ (r + 2)) = (x + y) * b (p ^ (r + 1)) - x * y * b (p ^ r) := by
    intro r; rw [hxy, hxy']; exact hrec r
  have hroots := GlobalTheory.roots_norm_le_of_bounded_two_step_recursion x y (fun r => b (p ^ r))
    (Real.sqrt C) (Real.sqrt p) (Real.sqrt_nonneg _) hc0 hc1 hcr (by
      intro r
      have h := hbd (p ^ r)
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
      rw [mul_pow, ← pow_mul, mul_comm r 2, pow_mul, Real.sq_sqrt hC, Real.sq_sqrt hp0.le]
      simpa using h)
  have hP : (p : ℝ) < (p : ℝ) ^ (1 + s) := by
    conv_lhs => rw [← Real.rpow_one (p : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
  have hP0 : 0 < (p : ℝ) ^ (1 + s) := by linarith
  have hsq : 1 / (p : ℝ) ^ (2 * (1 + s)) = (1 / (p : ℝ) ^ (1 + s)) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hp0.le, Real.rpow_two, div_pow, one_pow]
  simp only [term_prime_pow b s p hp, real_term_prime_pow b s p, hsq]
  rw [div_eq_mul_one_div (‖1 + b p‖ ^ 2)]
  have hT0 : 0 < 1 / (p : ℝ) ^ (1 + s) := by positivity
  have hpT : p * (1 / (p : ℝ) ^ (1 + s)) < 1 := by
    rw [mul_one_div, div_lt_one hP0]; exact hP
  generalize 1 / (p : ℝ) ^ (1 + s) = T at hT0 hpT ⊢
  have hT1 : T < 1 := by nlinarith
  have hb : ∀ w : ℂ, ‖w‖ ≤ Real.sqrt p → ‖w‖ ^ 2 * T < 1 := by
    intro w hw
    have : ‖w‖ ^ 2 ≤ p := by
      rw [← Real.sq_sqrt hp0.le]
      exact pow_le_pow_left₀ (norm_nonneg _) hw 2
    nlinarith
  have hxT := hb x hroots.1
  have hyT := hb y hroots.2
  obtain ⟨hL, hR⟩ := GlobalTheory.T.twoStepRecursion_localEulerFactors x y (fun r => b (p ^ r)) T hT0.le hT1 hxT hyT hc0 hc1 hcr
  have hI := GlobalTheory.EisM.locineq x y T hT0.le hT1 hxT hyT
  rw [add_assoc, hxy] at hI
  rw [hxy', hω] at hR
  have hR0 : 0 ≤ ∑' r : ℕ, ‖b (p ^ r)‖ ^ 2 * T ^ r := tsum_nonneg fun r => by positivity
  have hLn := congrArg (fun w : ℂ => ‖w‖ ^ 2) hL
  simp only [norm_one, one_pow] at hLn
  rw [norm_mul, mul_pow] at hLn
  have hL0 : 0 ≤ ‖∑' r : ℕ, b (p ^ r) * (T : ℂ) ^ r‖ ^ 2 := by positivity
  generalize (∑' r : ℕ, ‖b (p ^ r)‖ ^ 2 * T ^ r) = R at hR hR0 ⊢
  generalize ‖∑' r : ℕ, b (p ^ r) * (T : ℂ) ^ r‖ ^ 2 = L at hLn hL0 ⊢
  generalize ‖(1 - x * T) * (1 - y * T)‖ ^ 2 = D at hLn hI
  generalize (1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2 = E at hR hI
  generalize Real.exp (‖1 + b p‖ ^ 2 * T) = A at hI ⊢
  have h1 : 0 < 1 - T := by linarith
  have h2 : 0 < 1 - T ^ 2 := by nlinarith
  rw [one_pow, one_mul] at hR
  have hK : 0 ≤ (1 - T)⁻¹ * L * R * (1 - T ^ 2)⁻¹ := by positivity
  have hone : ((1 - T) * D * E) * ((1 - T)⁻¹ * L * R * (1 - T ^ 2)⁻¹) = 1 := by
    calc ((1 - T) * D * E) * ((1 - T)⁻¹ * L * R * (1 - T ^ 2)⁻¹)
        = ((1 - T) * (1 - T)⁻¹) * (L * D) * ((R * E) * (1 - T ^ 2)⁻¹) := by ring
      _ = 1 := by rw [hLn, hR, mul_inv_cancel₀ h1.ne', mul_inv_cancel₀ h2.ne']; ring
  have h3 := mul_le_mul_of_nonneg_right hI hK
  rwa [mul_assoc, hone, mul_one, one_mul] at h3

end GlobalTheory.LocIneq
end

section

open Polynomial

namespace GlobalTheory


open Polynomial in
theorem _root_.GlobalTheory.exists_integral_norm_natDegree_mod_eq_one :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
      [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] (N : ℕ), 1 ≤ N →
      ∃ f : FunctionField.ringOfIntegers k K, f ≠ 0 ∧ (Algebra.norm k[X] f).natDegree % N = 1 % N := by
  intro k K _ _ _ _ _ _ _ _ N hN
  set O := FunctionField.ringOfIntegers k K
  have hC1 : _root_.GlobalTheory.NeedB.IsFirstChernClassOfLineBundle (RatFunc k) := by
    unfold _root_.GlobalTheory.NeedB.IsFirstChernClassOfLineBundle
    intro n d f hf hd hdn
    obtain ⟨x, hx, h⟩ := _root_.GlobalTheory.tsenLang_ratFunc k n 1 d (fun _ => f) (fun _ => hf) hd (by simpa using hdn)
    exact ⟨x, hx, h 0⟩
  obtain ⟨x, hx⟩ := _root_.GlobalTheory.norm_surjective_of_is_c1 (RatFunc k) K hC1
    RatFunc.X RatFunc.X_ne_zero
  haveI : Module.IsTorsionFree k[X] K := .trans_faithfulSMul k[X] (RatFunc k) K
  haveI : Module.Free k[X] O := Module.free_of_finite_type_torsion_free'
  haveI := IsIntegralClosure.isLocalization k[X] (RatFunc k) K O
  have hnorm : ∀ a : O, algebraMap k[X] (RatFunc k) (Algebra.norm k[X] a) =
      Algebra.norm (RatFunc k) (algebraMap O K a) := fun a =>
    (Algebra.norm_localization k[X] (nonZeroDivisors k[X]) (Rₘ := RatFunc k) (Sₘ := K) a).symm
  obtain ⟨⟨a, s⟩, hxa⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid O (nonZeroDivisors k[X])) x
  obtain ⟨b, hb, hbs⟩ := s.2
  simp only at hxa
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set r := Module.finrank k[X] O
  have hs : Algebra.norm k[X] (s : O) = b ^ r := by rw [← hbs]; exact Algebra.norm_algebraMap b
  have ha : Algebra.norm k[X] a = X * b ^ r := by
    apply IsFractionRing.injective k[X] (RatFunc k)
    rw [hnorm, ← hxa, map_mul, hx, ← hnorm, hs, map_mul, RatFunc.algebraMap_X]
  have hexp : r + r * (N - 1) = r * N := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hf : Algebra.norm k[X] (a * (s : O) ^ (N - 1)) = X * b ^ (r * N) := by
    rw [map_mul, map_pow, ha, hs, mul_assoc, ← pow_mul, ← pow_add, hexp]
  refine ⟨a * (s : O) ^ (N - 1), ?_, ?_⟩
  · intro h
    have h0 := hf
    rw [h, Algebra.norm_zero] at h0
    exact mul_ne_zero X_ne_zero (pow_ne_zero _ hb0) h0.symm
  · rw [hf, natDegree_mul X_ne_zero (pow_ne_zero _ hb0), natDegree_X, natDegree_pow,
      show r * N * b.natDegree = r * b.natDegree * N by ring, Nat.add_mul_mod_self_right]

end GlobalTheory
end
