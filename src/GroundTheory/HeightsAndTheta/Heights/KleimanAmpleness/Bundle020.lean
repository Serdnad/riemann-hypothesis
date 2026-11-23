module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle011
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

universe u w

theorem SectionCount.proof (hT : SectionCount.Top.Statement.{u, w})
    (hD : SectionCount.Drop.Statement.{u, w}) : SectionCount.Statement.{u, w} := by
  intro k _ Ω _ _ N x d Nb b hZ hN hb
  obtain ⟨C₁, h₁⟩ := hT k Ω N x d Nb hZ hN
  obtain ⟨C₂, h₂⟩ := hD k Ω N x d Nb b hZ hN hb
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂, eventually_ge_atTop 1] with n hn₁ hn₂ hn
  set f : ℕ → ℝ := fun i =>
    (Module.finrank k (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).secs : ℝ) with hf
  set Y : ℝ := (interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) : ℝ) with hY
  set X : ℝ := (interNum (primeOf (S := k) x) (Fin.cons (α := fun _ => SubSystem k x Ω)
    (twistSys k x (b : ℤ)) (fun _ : Fin d => Nb.toSubSystem)) : ℝ) with hX
  have h0 : f 0 = (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ) :=
    congrArg (fun m : ℤ => (Module.finrank k (twistMul Nb.toSubSystem n m).secs : ℝ)) (by simp)
  have htel : f 0 - f n = ∑ i ∈ Finset.range n, (f i - f (i + 1)) := by
    rw [Finset.sum_range_sub']
  have hsum : ∑ i ∈ Finset.range n, (f i - f (i + 1)) ≤
      ∑ _i ∈ Finset.range n, (X * (n : ℝ) ^ d / (d.factorial : ℝ) + C₂ * (n : ℝ) ^ d / n) :=
    Finset.sum_le_sum fun i hi => hn₂ i (Finset.mem_range.mp hi)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : ((d + 1).factorial : ℝ) = ((d : ℝ) + 1) * (d.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hdf : (0 : ℝ) < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have key : (n : ℝ) * (X * (n : ℝ) ^ d / (d.factorial : ℝ) + C₂ * (n : ℝ) ^ d / n) =
      ((d : ℝ) + 1) * X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) + C₂ * (n : ℝ) ^ d := by
    rw [hfac]; field_simp; ring
  rw [key] at hsum
  rw [← h0] at hn₁
  have hgoal : f n = (Module.finrank k (twistMul Nb.toSubSystem n (-((n : ℤ) * b))).secs : ℝ) := rfl
  rw [← hgoal]
  push_cast
  have e1 : (Y - ((d : ℝ) + 1) * X) * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) =
      Y * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) -
        ((d : ℝ) + 1) * X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) := by ring
  rw [e1]
  linarith

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Sections

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem mul_mem_pow_succ (Q : SubSystem k x Ω) (I : Chart x) {m : ℕ} {a q : Ω}
    (ha : a ∈ (Q.pow m).sub I) (hq : q ∈ Q.sub I) : a * q ∈ (Q.pow (m + 1)).sub I :=
  Submodule.subset_span ⟨q, hq, a, ha, by rw [smul_eq_mul, mul_comm]⟩

theorem mul_pow_mem_pow (Q : SubSystem k x Ω) (I : Chart x) {m : ℕ} {a q : Ω}
    (ha : a ∈ (Q.pow m).sub I) (hq : q ∈ Q.sub I) (j : ℕ) : a * q ^ j ∈ (Q.pow (m + j)).sub I := by
  induction j with
  | zero => simpa using ha
  | succ j ih =>
    rw [pow_succ, ← mul_assoc, ← add_assoc]
    exact mul_mem_pow_succ Q I ih hq

theorem aeval_mem_pow (Q : SubSystem k x Ω) {r : ℕ} {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ Q.secs)
    (I : Chart x) {f : MvPolynomial (Fin (r + 1)) k} {n : ℕ} (hf : f.IsHomogeneous n) :
    aeval h f ∈ (Q.pow n).sub I := by
  have hI : ∀ l, h l ∈ Q.sub I := fun l =>
    (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp (hh l) I)
  have hprod : ∀ (α : Fin (r + 1) →₀ ℕ) (s : Finset (Fin (r + 1))),
      ∏ i ∈ s, h i ^ α i ∈ (Q.pow (∑ i ∈ s, α i)).sub I := by
    intro α s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty]
      exact one_mem_twistMod_zero (S := k) I
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, mul_comm, add_comm]
      exact mul_pow_mem_pow Q I ih (hI j) (α j)

  rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [aeval_monomial]
  have hdeg : ∑ i ∈ α.support, α i = n := by
    have := hf (mem_support_iff.mp hα)
    rw [Finsupp.weight_apply, Finsupp.sum] at this
    simpa using this
  have hmem := hprod α α.support
  rw [hdeg] at hmem
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  exact Submodule.smul_of_tower_mem _ _ hmem

theorem coordGraded_le_secs (Q : SubSystem k x Ω) {r : ℕ} {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ Q.secs)
    (n : ℕ) : (coordGraded k h).piece (n : ℤ) ≤ (twistMul Q n 0).secs := by
  rw [twistMul, SubSystem.twist_twistSys_zero]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, e, hf, he, rfl⟩
  have hen : e = n := by exact_mod_cast he
  subst hen
  exact (Submodule.mem_iInf _).mpr fun I =>
    (Submodule.restrictScalars_mem k _ _).mpr (aeval_mem_pow Q hh I hf)

theorem finite_secs_twistMul (hTF : TwistFinite.Statement.{u, w}) (Nb : LineBundle k x) {r : ℕ}
    {h : Fin (r + 1) → Ω} (hx : x ≠ 0) (hV : IsVeryAmpleBy Nb.toSubSystem h) (n : ℕ) :
    Module.Finite k (twistMul Nb.toSubSystem n 0).secs := by
  obtain ⟨m, deg, gen, -, hspan⟩ :=
    hTF k Ω N x (twistBundle k x 0) Nb r h hx hV.mem_secs hV.generates
  have e1 : (twistBundle k x 0).toSubSystem.twist (Nb.toSubSystem.pow n) =
      twistMul Nb.toSubSystem n 0 := by
    rw [twistMul, SubSystem.twist_twistSys_zero]
    exact twistSys_zero_twist _
  have hle := hspan n
  rw [e1] at hle
  let T : Submodule k Ω := ⨆ j : Fin m, (homogeneousSubmodule (Fin (r + 1)) k (n - deg j)).map
    ((LinearMap.mulRight k (gen j)).comp (aeval h).toLinearMap)
  have hT : T.FG := Submodule.fg_iSup _ fun j => (homogeneousSubmodule_fg (Fin (r + 1)) k (n - deg j)).map _
  have hle' : Submodule.span k {z | ∃ (j : Fin m) (f : MvPolynomial (Fin (r + 1)) k) (e : ℕ),
      f.IsHomogeneous e ∧ e + deg j = n ∧ z = aeval h f * gen j} ≤ T := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, f, e, hf, hed, rfl⟩
    refine Submodule.mem_iSup_of_mem j ⟨f, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_homogeneousSubmodule]
    convert hf using 1
    omega
  have : FiniteDimensional k T := Module.Finite.iff_fg.mpr hT
  exact Submodule.finiteDimensional_of_le (hle.trans hle')

end Sections

theorem SectionCount.Top.proof (hHP : HilbertPositive.Statement.{u, w})
    (hTie : InterNumTie.Statement.{u, w}) (hTF : TwistFinite.Statement.{u, w})
    (hDim : VeryAmpleDim.Statement.{u, w}) (hDeg : VeryAmpleDegree.Statement.{u, w}) :
    SectionCount.Top.Statement.{u, w} := by
  intro k _ Ω _ _ N x d Nb hZ hN
  obtain ⟨r, h, hV⟩ := hN
  have hx : x ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := hZ.relevant
    exact hi ((mem_primeOf_of_isHomogeneous _ (isHomogeneous_X k i)).mpr (by simp))
  have hZh := hDim k Ω N x (d + 1) Nb r h hZ hV
  obtain ⟨⟨C, hC⟩, -, -⟩ := hHP k Ω r h (d + 1) (Nat.le_add_left 1 d) hZh
  have hnum : interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) =
      NumbersDVR.intNum k (primeOfOne (S := k) h) (fun _ : Fin (d + 1) => fun _ : Unit => (1 : ℤ)) := by
    rw [hDeg k Ω N x (d + 1) Nb r h hZ hV]
    exact hTie k Ω r h (d + 1) (primeOf (S := k) h) (fun _ => 1) hZh
  refine ⟨C, ?_⟩
  filter_upwards [hC] with n hn
  have hle : (Module.finrank k ((coordGraded k h).piece (n : ℤ)) : ℝ) ≤
      (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ) := by
    have := finite_secs_twistMul hTF Nb hx hV n
    exact_mod_cast Submodule.finrank_mono (coordGraded_le_secs Nb.toSubSystem hV.mem_secs n)
  rw [hnum]
  rw [Nat.add_sub_cancel] at hn
  have := (abs_le.mp hn).1
  linarith

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Tilde

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem FinGradedSub.tildeSys_natCast_eq_twist (M : FinGradedSub (S := S) (x := x) E) (a : ℕ) :
    M.tildeSys (a : ℤ) = (M.tildeSys 0).twist (twistSys S x (a : ℤ)) := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have hA : x i ^ a ∈ twistMod S x (a : ℤ) I := by
    rw [twistMod_eq_span _ I hi, zpow_natCast]
    exact Submodule.mem_span_singleton_self _
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    refine Submodule.subset_span ⟨x i ^ a, hA, (aeval x (s * X i ^ a))⁻¹ • m,
      Submodule.subset_span ⟨m, s * X i ^ a, b, e + a, mul_mem hs (pow_mem (X_mem_monos hi) a),
        hse.mul (isHomogeneous_X_pow i a), hm, by push_cast; omega, rfl⟩, ?_⟩
    rw [smul_smul, map_mul, map_pow, aeval_X, mul_inv, ← mul_assoc, mul_comm (x i ^ a),
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero a hxi), mul_one]
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ twistMod S x (a : ℤ) I at hq
    rw [twistMod_eq_span _ I hi, zpow_natCast, Submodule.mem_span_singleton] at hq
    obtain ⟨β, rfl⟩ := hq
    have key : x i ^ a • y ∈ M.tilde (a : ℤ) I := by
      refine Submodule.span_induction (p := fun y _ => x i ^ a • y ∈ M.tilde (a : ℤ) I) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩
        refine Submodule.subset_span ⟨aeval x (X i ^ a : Poly S N) • m, s, b + a, e, hs, hse,
          M.smul_mem a b _ m (isHomogeneous_X_pow i a) hm, by omega, ?_⟩
        rw [smul_smul, smul_smul, map_pow, aeval_X, mul_comm]
      · rw [smul_zero]
        exact Submodule.zero_mem _
      · intro y y' _ _ h h'
        rw [smul_add]
        exact Submodule.add_mem _ h h'
      · intro c y _ h
        rw [Subalgebra.smul_def, smul_smul, mul_comm, ← smul_smul, ← Subalgebra.smul_def]
        exact Submodule.smul_mem _ c h
    rw [SetLike.mem_coe, chartRing_smul_def, ← smul_smul, ← Subalgebra.smul_def]
    exact Submodule.smul_mem _ β key

end Tilde

theorem AmpleVanish.proof (hC : VeryAmpleCech.Statement.{u, v, w}) (hE : Extension.Statement.{u, v, w})
    (hT : TildeVanish.Statement.{u, v, w}) : AmpleVanish.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ F hF H hH
  obtain ⟨r, h, hh⟩ := hH
  obtain ⟨F', hF', hiso⟩ := hC S Ω N x E F hF H r h hh
  obtain ⟨M, -, hM⟩ := hE S Ω r h E F' hF'
  obtain ⟨c₀, hc₀⟩ := hT S Ω r h E M
  refine ⟨c₀.toNat, fun i a hi ha => ?_⟩
  obtain ⟨e⟩ := hiso a i
  have hsys : F'.toSubSystem = M.tildeSys 0 := SubSystem.ext_sub fun J => (hM J).symm
  have hv := hc₀ i hi a (by omega)
  rw [M.tildeSys_natCast_eq_twist a, ← hsys] at hv
  exact e.toEquiv.subsingleton

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Defs

variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

def eulerCharQuot {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ : SubSystem k x E) : ℤ :=
  ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (Module.finrank k (SubSystem.quotH F₁ F₂ i) : ℤ)

def pieceChar (pp : Ideal (Poly k N)) (a : ℤ) {t : ℕ} (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ) : ℤ :=
  eulerCharQuot k
    (((twistSys k x a).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
    ((((twistSys k x a).twist (idealSys x pp)).twistPows t (fun j => (L j).toSubSystem) n).twist
      (twistSys k x c))

end Defs

def IsNumPolyLT (t D : ℕ) (f : (Fin t → ℕ) → ℤ → ℚ) : Prop :=
  ∃ Q : MvPolynomial (Fin (t + 1)) ℚ, (Q = 0 ∨ Q.totalDegree < D) ∧
    ∀ (n : Fin t → ℕ) (c : ℤ), f n c = eval (Fin.snoc (α := fun _ => ℚ) (fun j => (n j : ℚ)) (c : ℚ)) Q

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

theorem eulerChar_eq_finrank_H0 {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (F : SubSystem k x Ω) (hF : ∀ i, 1 ≤ i → Subsingleton (F.H i)) :
    eulerChar k F = Module.finrank k (F.H 0) := by
  unfold eulerChar
  rw [Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp
  · intro i _
    have := hF (i + 1) (by omega)
    simp [Module.finrank_zero_of_subsingleton]

theorem VeryAmpleSnapper.proof (hF : SnapperFinite.Statement.{u, w, w}) (hS : Snapper.Statement.{u, w, w})
    (hV : TwistVanishAll.Statement.{u, w}) (hA : AmpleVanish.Statement.{u, w, w}) :
    VeryAmpleSnapper.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb hZ hNb
  obtain ⟨r, h, hh⟩ := hNb
  have hx : x ≠ 0 := by
    obtain ⟨i, hi⟩ := hZ.relevant
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X] at hi
    exact fun h0 => hi (congrFun h0 i)
  set O := twistBundle k x 0
  have hsys : ∀ (a : ℕ) (c : ℤ), (O.toSubSystem.twistPows 1 (fun j => (![Nb] j).toSubSystem)
      (fun _ => a)).twist (twistSys k x c) = twistMul Nb.toSubSystem a c := by
    intro a c
    change ((twistSys k x 0).twist (Nb.toSubSystem.pow a)).twist _ = _
    rw [twistSys_zero_twist]
    rfl
  have hpt : ∀ a c : ℚ, (Fin.snoc (α := fun _ => ℚ) (fun _ : Fin 1 => a) c : Fin 2 → ℚ) = ![a, c] := by
    intro a c; funext i; fin_cases i <;> rfl
  have h0 : ∀ F : SubSystem k x Ω, Module.finrank k (F.H 0) = Module.finrank k F.secs := fun F =>
    (CechZerothCohomologySections.proof k Ω N x Ω F hx).some.finrank_eq
  obtain ⟨Q, hQ, hχ⟩ := hS k Ω N x e hZ Ω O.toSubFamily O.fg 1 ![Nb]
  obtain ⟨c₀, hc₀⟩ := hV k Ω N x O Nb r h hh.mem_secs hh.generates
  obtain ⟨a₀, ha₀⟩ := hA k Ω N x Ω O.toSubFamily O.fg Nb ⟨r, h, hh⟩
  refine ⟨fun a c => ?_, Q, c₀, hQ, fun a c hc => ?_, ?_⟩
  · have := hF k Ω N x Ω O.toSubFamily O.fg 1 ![Nb] (fun _ => a) c 0
    rw [hsys] at this
    exact (CechZerothCohomologySections.proof k Ω N x Ω _ hx).some.finiteDimensional
  · have hv : ∀ i, 1 ≤ i → Subsingleton ((twistMul Nb.toSubSystem a c).H i) := by
      intro i hi
      have := hc₀ i a c hi hc
      change Subsingleton ((((twistSys k x 0).twist (Nb.toSubSystem.pow a)).twist _).H i) at this
      rwa [twistSys_zero_twist] at this
    have := hχ (fun _ => a) c
    rw [hsys, hpt, eulerChar_eq_finrank_H0 _ hv, h0] at this
    exact_mod_cast this
  · filter_upwards [eventually_ge_atTop a₀] with a ha
    have hv : ∀ i, 1 ≤ i → Subsingleton ((Nb.toSubSystem.pow a).H i) := by
      intro i hi
      have := ha₀ i a hi ha
      change Subsingleton (((twistSys k x 0).twist (Nb.toSubSystem.pow a)).H i) at this
      rwa [twistSys_zero_twist] at this
    have := hχ (fun _ => a) 0
    rw [hsys, hpt, twistMul, SubSystem.twist_twistSys_zero, eulerChar_eq_finrank_H0 _ hv, h0] at this
    exact_mod_cast this

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Tilde

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]


omit [IsScalarTower S Ω E] in
theorem FinGradedSub.zpow_smul_mem_tilde (M : FinGradedSub (S := S) (x := x) E) {I : Chart x}
    {i : Fin (N + 1)} (hi : i ∈ I.1) (c d : ℤ) {y : E} (hy : y ∈ M.tilde d I) :
    x i ^ c • y ∈ M.tilde (d + c) I := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  refine Submodule.span_induction (p := fun y _ => x i ^ c • y ∈ M.tilde (d + c) I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · refine Submodule.subset_span ⟨aeval x (X i ^ n : Poly S N) • m, s, a + n, e, hs, hse,
        M.smul_mem n a _ m (isHomogeneous_X_pow i n) hm, by omega, ?_⟩
      rw [smul_smul, smul_smul]
      congr 1
      simp only [map_pow, aeval_X, zpow_natCast]
      ring
    · refine Submodule.subset_span ⟨m, s * X i ^ n, a, e + n, mul_mem hs (pow_mem (X_mem_monos hi) n),
        hse.mul (isHomogeneous_X_pow i n), hm, by push_cast; omega, ?_⟩
      rw [smul_smul]
      congr 1
      simp only [map_mul, map_pow, aeval_X, zpow_neg, zpow_natCast, mul_inv]
      ring
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro a y _ hy
    have : x i ^ c • (a • y) = a • (x i ^ c • y) := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ a hy

theorem TildeShift.proof : TildeShift.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ M c
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  apply le_antisymm
  · intro y hy
    have h0 : x i ^ (-c) • y ∈ M.tilde 0 I := by
      simpa using M.zpow_smul_mem_tilde hi (-c) c hy
    refine Submodule.subset_span ⟨x i ^ c, ?_, x i ^ (-c) • y, h0, ?_⟩
    · change x i ^ c ∈ twistMod S x c I
      rw [twistMod_eq_span c I hi]
      exact Submodule.mem_span_singleton_self _
    · rw [smul_smul, ← zpow_add₀ hxi, add_neg_cancel, zpow_zero, one_smul]
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ twistMod S x c I at hq
    rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
    obtain ⟨a, rfl⟩ := hq
    have hy' : x i ^ c • y ∈ M.tilde c I := by
      simpa using M.zpow_smul_mem_tilde hi c 0 hy
    have : (a • x i ^ c) • y = a • (x i ^ c • y) := by
      rw [chartRing_smul_def, Subalgebra.smul_def, smul_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ a hy'

end Tilde

end

end GroundTheory.Heights₂.Heights.Kleiman
end
