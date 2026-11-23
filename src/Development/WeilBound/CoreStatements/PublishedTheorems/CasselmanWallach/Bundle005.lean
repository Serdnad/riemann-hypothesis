module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle011
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import GroundTheory.GlobalFields.Artin.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IsInLieAlgebraISmulAddConjTranspose
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift

@[expose] public section

section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CompactGroupFacts

variable {n : ℕ}

theorem mul_mem (ε : Fin n → Bool) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) :
    g * h ∈ UJset ε := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hh' : hᴴ * Jm ε * h = Jm ε := hh
  show (g * h)ᴴ * Jm ε * (g * h) = Jm ε
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg', hh']

theorem hilbert_schmidt_continuous : Continuous (hs2 : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold hs2
  fun_prop

theorem isClosed_UJ (ε : Fin n → Bool) : IsClosed (UJset ε) := by
  have : UJset ε = (fun g : Matrix (Fin n) (Fin n) ℂ => gᴴ * Jm ε * g) ⁻¹' {Jm ε} := rfl
  rw [this]
  exact isClosed_singleton.preimage (by fun_prop)

theorem entry_le (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖g i j‖ ^ 2 ≤ hs2 g := by
  unfold hs2
  calc ‖g i j‖ ^ 2 ≤ ∑ j', ‖g i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖g i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem compact (ε : Fin n → Bool) (ρ : ℝ) : IsCompact {g | g ∈ UJset ε ∧ hs2 g ≤ ρ} := by
  let K : Set (Fin n → Fin n → ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) (Real.sqrt ρ)
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset ((isClosed_UJ ε).inter (isClosed_le hilbert_schmidt_continuous continuous_const)) ?_
  rintro g ⟨-, hg⟩ i - j -
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact Real.le_sqrt_of_sq_le ((entry_le g i j).trans hg)

theorem Xp_inP (ε : Fin n → Bool) (p : Fin n × Fin n) (hp : p ∈ nc ε) : inP ε (Xp p.1 p.2) := by
  obtain ⟨a, b⟩ := p
  have hab : ε a ≠ ε b := by simpa [nc] using hp
  have hne : a ≠ b := fun h => hab (h ▸ rfl)
  set σ : Fin n → ℂ := fun k => if ε k then 1 else -1 with hσdef
  have hσ : σ b = -σ a := by
    simp only [hσdef]; revert hab; cases ε a <;> cases ε b <;> simp
  have h2 : Xp a b * Jm ε = -(Jm ε * Xp a b) := by
    show Xp a b * Matrix.diagonal σ = -(Matrix.diagonal σ * Xp a b)
    ext i j
    simp only [Xp, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, Matrix.add_apply,
      Matrix.single_apply]
    by_cases h1 : a = i ∧ b = j <;> by_cases h3 : b = i ∧ a = j
    · exact absurd (h1.1.trans h3.1.symm) hne
    · obtain ⟨rfl, rfl⟩ := h1; simp only [if_neg h3, hσ]; ring
    · obtain ⟨rfl, rfl⟩ := h3; simp only [if_neg h1, hσ]; ring
    · simp only [if_neg h1, if_neg h3]; ring
  have hh : (Xp a b)ᴴ = Xp a b := by
    ext i j
    simp only [Xp, Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.single_apply]
    by_cases hi : a = i <;> by_cases hj : b = j <;> by_cases hi' : b = i <;> by_cases hj' : a = j <;>
      subst_vars <;> simp_all [Complex.ext_iff]
  refine ⟨?_, h2⟩
  show (Xp a b)ᴴ * Jm ε + Jm ε * Xp a b = 0
  rw [hh, h2, neg_add_cancel]

end CompactGroupFacts

theorem group_facts_holds : UnitaryGroupFacts := by
  intro n ε
  refine ⟨CompactGroupFacts.compact ε, ?_, ?_, ?_, CompactGroupFacts.hilbert_schmidt_continuous, CompactGroupFacts.Xp_inP ε⟩
  · show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  · intro g hg X hX t
    refine CompactGroupFacts.mul_mem ε hg ?_
    have := rq_exp_mem ε X hX.1 t
    rwa [Complex.coe_smul] at this
  · intro X s t
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left s |>.smul_right t)

end PositivityTheory.CW

end
end

section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace SumSquaresShift

theorem shift {n : ℕ} {ε : Fin n → Bool} (hB3g : UnitaryGroupFacts) (F0 : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : inP ε X) (D : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => F0 (g * NormedSpace.exp (t • X))) (D g) 0)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ UJset ε) (t : ℝ) :
    HasDerivAt (fun t : ℝ => F0 (g * NormedSpace.exp (t • X))) (D (g * NormedSpace.exp (t • X))) t := by
  obtain ⟨-, -, hmem, hadd, -⟩ := hB3g n ε
  have hg' := hmem g hg X hX t
  have h1 := h _ hg'
  have h0 : HasDerivAt (fun s : ℝ => F0 (g * NormedSpace.exp (t • X) * NormedSpace.exp (s • X)))
      (D (g * NormedSpace.exp (t • X))) (t - t) := by
    rw [sub_self]; exact h1
  have h4 := h0.comp_sub_const t t
  refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  have hu : t + (u - t) = u := by ring
  show F0 (g * NormedSpace.exp (u • X)) = F0 (g * NormedSpace.exp (t • X) * NormedSpace.exp ((u - t) • X))
  rw [mul_assoc, ← hadd X t (u - t), hu]

end SumSquaresShift

open SumSquaresShift in
theorem second_derivatives_of_growth : B1 → UnitaryGroupFacts → SumSquaresSecondDerivative := by
  intro hB1 hB3g n ε V _ _ E hMod ι b μ hEig κ hκ F hF S a g hg
  obtain ⟨hXp, hcas, hnorm⟩ := hB1 n ε V E hMod
  have hd : ∀ p ∈ nc ε, ∀ (v : V) (t : ℝ),
      HasDerivAt (fun s : ℝ => F v (g * NormedSpace.exp (s • Xp p.1 p.2)))
        (F (actM E (Xp p.1 p.2) v) (g * NormedSpace.exp (t • Xp p.1 p.2))) t := by
    intro p hp v t
    exact shift hB3g (F v) (Xp p.1 p.2) (hXp p hp) (fun k => F (actM E (Xp p.1 p.2) v) k)
      (fun k hk => hF _ (hXp p hp) v k hk) g hg t
  have hexp0 : ∀ X : Matrix (Fin n) (Fin n) ℂ, g * NormedSpace.exp ((0:ℝ) • X) = g := by
    intro X
    simp [NormedSpace.exp_zero]
  refine ⟨fun p => ∑ i ∈ S, a i * (2 * (inner ℝ (F (b i) g)
      (F (actM E (Xp p.1 p.2) (actM E (Xp p.1 p.2) (b i))) g) + ‖F (actM E (Xp p.1 p.2) (b i)) g‖ ^ 2)), ?_, ?_⟩
  · intro p hp
    refine ⟨fun t => ∑ i ∈ S, a i * (2 * inner ℝ (F (b i) (g * NormedSpace.exp (t • Xp p.1 p.2)))
      (F (actM E (Xp p.1 p.2) (b i)) (g * NormedSpace.exp (t • Xp p.1 p.2)))), ?_, ?_⟩
    · intro t
      beta_reduce
      apply HasDerivAt.fun_sum
      intro i _
      exact ((hd p hp (b i) t).norm_sq).const_mul (a i)
    · beta_reduce
      apply HasDerivAt.fun_sum
      intro i _
      have h1 := hd p hp (b i) 0
      have h2 := hd p hp (actM E (Xp p.1 p.2) (b i)) 0
      have h3 := ((HasDerivAt.inner ℝ h1 h2).const_mul 2).const_mul (a i)
      rw [hexp0] at h3
      refine h3.congr_deriv ?_
      rw [real_inner_self_eq_norm_sq]
  · dsimp only
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hN : ∑ p ∈ nc ε, ‖F (actM E (Xp p.1 p.2) (b i)) g‖ ^ 2
        = ∑ p ∈ nc ε, ‖F (E p.1 p.2 (b i)) g‖ ^ 2 :=
      hnorm ((LinearMap.proj g).comp F) (b i)
    have hs : ∑ p ∈ nc ε, F (actM E (Xp p.1 p.2) (actM E (Xp p.1 p.2) (b i))) g
        = ((κ - μ i : ℝ) : ℂ) * F (b i) g := by
      have h0 := congrArg (fun v => F v g) (hcas κ hκ (b i))

      simp only [map_sum, Finset.sum_apply] at h0
      rw [h0, (hEig.eig i : casimirK ε E (b i) = _)]
      simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    have hI : ∑ p ∈ nc ε, inner ℝ (F (b i) g) (F (actM E (Xp p.1 p.2) (actM E (Xp p.1 p.2) (b i))) g)
        = (κ - μ i) * ‖F (b i) g‖ ^ 2 := by
      rw [← inner_sum, hs, ← Complex.real_smul, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, hI, hN]
    ring

end PositivityTheory.CW

end
end

section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CWB

open PositivityTheory.CW

namespace WordFiltrationCommute

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)

theorem U_mono {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k :=
  Submodule.span_mono fun _ ⟨l, hl, hx⟩ => ⟨l, hl.trans h, hx⟩

theorem one_mem : (1 : Module.End ℂ V) ∈ U E 0 :=
  Submodule.subset_span ⟨[], by simp, by simp⟩

theorem gen_mem (a b : Fin n) : E a b ∈ U E 1 :=
  Submodule.subset_span ⟨[(a, b)], by simp, by simp⟩

theorem mul_mem {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y ∈ U E (j + k) :=
  by apply _root_.UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.main <;> assumption

theorem bracket_mem (hE : IsGlRep E) {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y - y * x ∈ U E (j + k - 1) :=
  by apply _root_.UpperTheory.Reformulated.B.ParabolicUnipotentGL.main <;> assumption

end WordFiltrationCommute

theorem word_filtration_of_length : A1 := by
  intro n ε V _ _ E hM
  have hE : IsGlRep E := hM.gl
  have hC : casimirK ε E ∈ U E 2 := by
    unfold casimirK
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    exact WordFiltrationCommute.U_mono E (by norm_num : 1 + 1 ≤ 2) (WordFiltrationCommute.mul_mem E (WordFiltrationCommute.gen_mem E a b) (WordFiltrationCommute.gen_mem E b a))
  refine ⟨fun j k h => WordFiltrationCommute.U_mono E h, WordFiltrationCommute.one_mem E, WordFiltrationCommute.gen_mem E,
    fun j k x hx y hy => WordFiltrationCommute.mul_mem E hx hy, fun j k x hx y hy => WordFiltrationCommute.bracket_mem E hE hx hy, hC,
    fun a b => ?_⟩
  have hZ := WordFiltrationCommute.bracket_mem E hE hC (WordFiltrationCommute.gen_mem E a b)
  unfold Z
  exact WordFiltrationCommute.U_mono E (by norm_num : 2 + 1 - 1 ≤ 2) hZ

end PositivityTheory.CWB

end
end

section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace MatrixActionSingle

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def act (A : Matrix (Fin n) (Fin n) (Module.End ℂ V)) : Module.End ℂ (PiLp 2 fun _ : Fin n => V) where
  toFun u := WithLp.toLp 2 (fun a => ∑ b, A a b (u b))
  map_add' u w := by ext a; simp [Finset.sum_add_distrib]
  map_smul' c u := by ext a; simp [Finset.smul_sum]

lemma act_apply (A : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (u : PiLp 2 fun _ : Fin n => V) (a : Fin n) :
    act A u a = ∑ b, A a b (u b) := rfl

lemma act_mul (A B : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (u : PiLp 2 fun _ : Fin n => V) :
    act (A * B) u = act A (act B u) := by
  ext a

  simp only [act_apply, Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  exact Finset.sum_comm

lemma act_pow (A : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (m : ℕ) (u : PiLp 2 fun _ : Fin n => V) :
    act (A ^ m) u = (act A ^ m) u := by
  induction m generalizing u with
  | zero =>
    ext a
    simp [act_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  | succ m ih => rw [pow_succ, act_mul, ih, pow_succ, Module.End.mul_apply]

lemma adjSign_symm (ε : Fin n → Bool) (a b : Fin n) : adjSign ε a b = adjSign ε b a := by
  simp [adjSign, eq_comm]

lemma adj (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E)
    (u w : PiLp 2 fun _ : Fin n => V) :
    inner ℂ (act (Mm E) u) w = inner ℂ u (act (Md ε E) w) := by
  simp only [PiLp.inner_apply, act_apply, Mm, Md, Matrix.of_apply, sum_inner, inner_sum,
    LinearMap.smul_apply, inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [adjSign_symm]
  exact hu a b _ _

lemma adj' (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E)
    (u w : PiLp 2 fun _ : Fin n => V) :
    inner ℂ (act (Md ε E) u) w = inner ℂ u (act (Mm E) w) := by
  rw [← inner_conj_symm, ← adj ε E hu, inner_conj_symm]

lemma act_single (A : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (e a : Fin n) (v : V) :
    act A (PiLp.single 2 e v) a = A a e v := by
  rw [act_apply, Finset.sum_eq_single e]
  · simp [PiLp.single_apply]
  · intro b _ hb
    simp [PiLp.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ e) h

lemma inner_single (e : Fin n) (v : V) (w : PiLp 2 fun _ : Fin n => V) :
    inner ℂ (PiLp.single 2 e v) w = inner ℂ v (w e) := by
  rw [PiLp.inner_apply, Finset.sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
  simp

end MatrixActionSingle

open MatrixActionSingle in
theorem column_moments_of_symmetric : A7 → ColumnOperatorMoments := by
  intro h7
  unfold ColumnOperatorMoments ForMod
  intro n ε V _ _ E hM v hv e j
  have hu := hM.uni
  have hsa : ∀ y z : PiLp 2 (fun _ : Fin n => V),
      inner ℂ (act (Md ε E * Mm E) y) z = inner ℂ y (act (Md ε E * Mm E) z) := by
    intro y z
    rw [act_mul, act_mul, adj' ε E hu, adj ε E hu]
  have hxn : ‖(PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))‖ = 1 := by
    rw [PiLp.norm_single, hv]
  have hn : ‖act (Mm E) (PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))‖ ^ 2
      = ∑ a, ‖E a e v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := act_single (Mm E) e a v
    simp only [Mm, Matrix.of_apply] at this
    rw [← this]
    rfl
  have hq : inner ℂ (PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))
      (act (Md ε E * Mm E) (PiLp.single 2 e v)) = ((∑ a, ‖E a e v‖ ^ 2 : ℝ) : ℂ) := by
    rw [act_mul, ← adj ε E hu, inner_self_eq_norm_sq_to_K, ← hn]
    norm_cast
  have hre : (inner ℂ (PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))
      (act (Md ε E * Mm E) (PiLp.single 2 e v))).re = ∑ a, ‖E a e v‖ ^ 2 := by
    rw [hq, Complex.ofReal_re]
  have key := h7 (PiLp 2 (fun _ : Fin n => V)) (act (Md ε E * Mm E)) hsa
    (PiLp.single 2 e v) hxn (by rw [hre]; positivity) j
  rw [hre, ← act_pow, inner_single, act_single] at key
  exact key

end PositivityTheory.CW

end
end

section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CharpolyPowerTraces

open Polynomial

theorem coeff_succ {R : Type} [CommRing R] {n : ℕ} (N : Matrix (Fin n) (Fin n) R)
    (h : ∀ k, (N ^ (k + 1)).trace = 0) (m : ℕ) :
    ((m : R) + 1) * N.charpolyRev.coeff (m + 1) = 0 := by
  have hps : (PowerSeries.mk fun k => (N ^ (k + 1)).trace) = 0 := by
    ext k
    simp [h]
  have hd : derivative N.charpolyRev = 0 := by
    have hc := GroundTheory.Global.coe_derivative_charpolyRev N
    rw [hps, mul_zero] at hc
    exact Polynomial.coe_eq_zero_iff.mp hc
  have hm := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p m) hd
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hm
  rw [mul_comm]
  exact hm

theorem coeff_succ_zero {R : Type} [CommRing R] [Algebra ℚ R] {n : ℕ} (N : Matrix (Fin n) (Fin n) R)
    (h : ∀ k, (N ^ (k + 1)).trace = 0) (m : ℕ) : N.charpolyRev.coeff (m + 1) = 0 := by
  have hu : IsUnit ((m : R) + 1) := by
    have : ((m : R) + 1) = algebraMap ℚ R ((m : ℚ) + 1) := by simp
    rw [this]; exact (IsUnit.mk0 _ (by positivity)).map _
  exact hu.mul_right_eq_zero.mp (coeff_succ N h m)

theorem charpoly_eq {R : Type} [CommRing R] [Algebra ℚ R] [Nontrivial R] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) R) (h : ∀ k, (N ^ (k + 1)).trace = 0) : N.charpoly = X ^ n := by
  have hRev : ∀ i, 1 ≤ i → N.charpolyRev.coeff i = 0 := by
    intro i hi
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hi
    exact coeff_succ_zero N h m
  have hdeg : N.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  ext j
  rw [Polynomial.coeff_X_pow]
  rcases lt_trichotomy j n with hj | hj | hj
  · rw [if_neg hj.ne]
    have hz := hRev (n - j) (by omega)
    rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, hdeg,
      Polynomial.revAt_le (by omega)] at hz
    rwa [show n - (n - j) = j by omega] at hz
  · rw [if_pos hj]
    have hl := (Matrix.charpoly_monic N).leadingCoeff
    rw [Polynomial.leadingCoeff, hdeg] at hl
    rw [hj]
    exact hl
  · rw [if_neg hj.ne']
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

end CharpolyPowerTraces

theorem nilpotent_of_power_traces : A4 := by
  unfold A4
  intro R _ _ n N h
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hc := Matrix.aeval_self_charpoly N
  rw [CharpolyPowerTraces.charpoly_eq N h, Polynomial.aeval_X_pow] at hc
  exact hc

end PositivityTheory.CW

end
end
