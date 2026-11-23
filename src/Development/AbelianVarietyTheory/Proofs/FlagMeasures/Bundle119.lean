module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle004
public import Mathlib.GroupTheory.Nilpotent
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle103
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle104
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.DerOf

variable {n : ℕ} {ε : Fin n → Bool}

theorem rd_congr {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g, inUJ ε g → f g = f' g)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) : Rd X f g = Rd X f' g := by
  unfold Rd
  congr 1
  funext t
  exact h _ (indefinite_unitary_mul_mem ε hg (exp_indefinite_unitary_holds n ε X hX t))

theorem eab_congr {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g, inUJ ε g → f g = f' g)
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : Eab ε a b f g = Eab ε a b f' g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold Eab Ec
  rw [rd_congr h h1 hg, rd_congr h h2 hg]

theorem J_single_J (a b : Fin n) :
    Jm ε * Matrix.single a b (1 : ℂ) * Jm ε = (sgn ε a b : ℂ) • Matrix.single a b (1 : ℂ) := by
  ext i j
  simp only [Jm, sgn, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    cases ε a <;> cases ε b <;> simp
  · simp [h]

theorem sgn_comm (a b : Fin n) : sgn ε a b = sgn ε b a := by
  simp only [sgn, eq_comm]

theorem sgn_sq (a b : Fin n) : (sgn ε a b : ℂ) * sgn ε a b = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem cpart1_swap (a b : Fin n) : cpart1 ε (Matrix.single a b (1 : ℂ)) =
    ((-sgn ε a b : ℝ) : ℂ) • cpart1 ε (Matrix.single b a (1 : ℂ)) := by
  simp only [cpart1, conjTranspose_single, star_one, J_single_J, sgn_comm (ε := ε) b a]
  have := sgn_sq (ε := ε) a b
  push_cast
  match_scalars
  · linear_combination (-1 / 2 : ℂ) * this
  · ring

theorem cpart2_swap (a b : Fin n) : cpart2 ε (Matrix.single a b (1 : ℂ)) =
    ((sgn ε a b : ℝ) : ℂ) • cpart2 ε (Matrix.single b a (1 : ℂ)) := by
  simp only [cpart2, conjTranspose_single, star_one, J_single_J, sgn_comm (ε := ε) b a]
  have := sgn_sq (ε := ε) a b
  match_scalars
  · linear_combination (-1 / (2 * Complex.I) : ℂ) * this
  · ring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {V : Submodule ℂ H}

theorem exists_D (hV : ∀ v ∈ V, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∃ v' ∈ V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∃ D : Module.End ℂ V, inG ε X → ∀ v : V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) (D v : H) 0 := by
  by_cases hX : inG ε X
  · choose d hd hd' using fun v : V => hV v v.2 X hX
    refine ⟨⟨⟨fun v => ⟨d v, hd v⟩, fun v w => Subtype.ext ?_⟩, fun c v => Subtype.ext ?_⟩, fun _ v => hd' v⟩
    · refine (hd' (v + w)).unique ?_
      simpa using (hd' v).fun_add (hd' w)
    · refine (hd' (c • v)).unique ?_
      simpa using (hd' v).fun_const_smul c
  · exact ⟨0, fun h => absurd h hX⟩

theorem rd_coef (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v v' : H}
    (h : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) (y : H)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Rd X (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g v'⟫_ℂ := by
  have h1 := (((innerSL ℂ y).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h
  refine Eq.trans ?_ h1.deriv
  unfold Rd
  congr 1
  funext t
  have := hσ.1.2 g hg _ (exp_indefinite_unitary_holds n ε X hX t)
  simp only [this]
  rfl

theorem skew (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {x x' y y' : H}
    (hx : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) x) x' 0)
    (hy : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) y) y' 0) :
    ⟪x', y⟫_ℂ = -⟪x, y'⟫_ℂ := by
  have h := hx.inner ℂ hy
  have hc : (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • X)) x, σ (NormedSpace.exp ((t : ℂ) • X)) y⟫_ℂ)
      = fun _ => ⟪x, y⟫_ℂ := by
    funext t
    exact LinearIsometry.inner_map_map
      ⟨(σ (NormedSpace.exp ((t : ℂ) • X))).toLinearMap, hσ.2.1 _ (exp_indefinite_unitary_holds n ε X hX t)⟩ x y
  rw [hc] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, ContinuousLinearMap.one_apply] at h0
  linear_combination h0

theorem exists_isDer : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H),
    IsURepOn (UJset ε) σ →
    (∀ v ∈ V, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∃ v' ∈ V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) →
    (∀ v ∈ V, ∀ y : H, SmoothOnG ε (fun g => ⟪y, σ g v⟫_ℂ)) →
    ∃ E : Fin n → Fin n → Module.End ℂ V, IsDer ε σ V E := by
  intro n ε H _ _ _ σ V hσ hV hs
  choose D hD using exists_D hV
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  have h1 : ∀ v : H, σ 1 v = v := fun v => by rw [hσ.1.1]; rfl
  have hc := fun a b : Fin n => complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  have hR : ∀ X, inG ε X → ∀ (v : V) (y : H) g, inUJ ε g →
      Rd X (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g (D X v)⟫_ℂ :=
    fun X hX v y g hg => rd_coef hσ hX (hD X hX v) y hg
  set E : Fin n → Fin n → Module.End ℂ V := fun a b =>
    D (cpart1 ε (Matrix.single a b 1)) + Complex.I • D (cpart2 ε (Matrix.single a b 1)) with hE
  have hEab : ∀ a b (v : V) (y : H) g, inUJ ε g →
      Eab ε a b (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g (E a b v)⟫_ℂ := by
    intro a b v y g hg
    unfold Eab Ec
    rw [hR _ (hc a b).1 v y g hg, hR _ (hc a b).2.1 v y g hg]
    simp [hE, inner_add_right, inner_smul_right]
  have hsm : ∀ X (r : ℝ), inG ε X → inG ε ((r : ℂ) • X) → ∀ v : V,
      (D ((r : ℂ) • X) v : H) = (r : ℂ) • (D X v : H) := by
    intro X r hX hrX v
    refine ext_inner_left ℂ fun y => ?_
    have := (rdLin n ε _ _ X X r 0 1 (hs v v.2 y) (hs v v.2 y) hX hX hone).2.1
    rwa [hR _ hX v y 1 hone, hR _ hrX v y 1 hone, h1, h1, ← inner_smul_right] at this
  refine ⟨E, ?_, ?_, ?_, fun v y => hs v v.2 y⟩
  · intro a b c d
    refine LinearMap.ext fun v => Subtype.ext (ext_inner_left ℂ fun y => ?_)
    have := eabGl n ε _ a b c d 1 (hs v v.2 y) hone
    rw [eab_congr (hEab c d v y) a b hone, eab_congr (hEab a b v y) c d hone] at this
    simp only [hEab _ _ _ y 1 hone, h1] at this
    split_ifs at this ⊢ <;> simpa [inner_sub_right] using this
  · intro a b x y
    have e1 := hsm _ (-sgn ε a b) (hc b a).1 (cpart1_swap a b ▸ (hc a b).1) y
    have e2 := hsm _ (sgn ε a b) (hc b a).2.1 (cpart2_swap a b ▸ (hc a b).2.1) y
    rw [← cpart1_swap] at e1
    rw [← cpart2_swap] at e2
    have s1 := skew hσ (hc a b).1 (hD _ (hc a b).1 x) (hD _ (hc a b).1 y)
    have s2 := skew hσ (hc a b).2.1 (hD _ (hc a b).2.1 x) (hD _ (hc a b).2.1 y)
    rw [e1, inner_smul_right] at s1
    rw [e2, inner_smul_right] at s2
    simp only [hE, Submodule.coe_inner, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add,
      Submodule.coe_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, s1, s2,
      Complex.conj_I]
    push_cast
    ring
  · intro X hX v
    convert hD X hX v using 1
    refine ext_inner_left ℂ fun y => ?_
    have := ecSumV n ε ℂ _ X 1 (hs v v.2 y) hone
    obtain ⟨e1, e2⟩ := (complex_parts_mem_lie_algebra_holds n ε X).2.2.2 hX
    simp only [eabV_eq, hEab _ _ _ y 1 hone, h1] at this
    rw [EcV, e1, e2, rdV_eq, rdV_eq, hR _ hX v y 1 hone, h1] at this
    simpa [Rd, inner_sum, inner_smul_right] using this.symm

end GlobalTheory.DerOf
end
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.NonOpenCell

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

theorem pm_val (σ : Equiv.Perm (Fin n)) :
    ((pm g σ : Gn g n) : Mt g n) = fun r j : Fin n => if r = σ j then 1 else 0 := by
  have h : IsUnit (show Mt g n from fun r j : Fin n => if r = σ j then 1 else 0) := by
    refine IsUnit.of_mul_eq_one (show Mt g n from fun r j : Fin n => if j = σ r then 1 else 0) ?_
    ext r c
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm r)]
    · simp [Matrix.one_apply, eq_comm]
    · intro k _ hk
      have : r ≠ σ k := fun h => hk (by simp [h])
      simp [this]
    · simp
  unfold pm toG
  rw [dite_eq_left h]
  rfl

theorem conj_apply (σ : Equiv.Perm (Fin n)) (x : Gn g n) (r c : Fin n) :
    (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) r c = (x : Mt g n) (σ r) (σ c) := by
  have h : ((pm g σ : Gn g n) : Mt g n) * (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n)
      = (x : Mt g n) * ((pm g σ : Gn g n) : Mt g n) := by
    rw [← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  generalize (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) = Y at h ⊢
  have h2 := congrFun (congrFun h (σ r)) c
  rw [Matrix.mul_apply, Matrix.mul_apply] at h2
  have h3 : ∀ r j, ((pm g σ : Gn g n) : Mt g n) r j = if r = σ j then 1 else 0 := fun r j => by
    rw [pm_val]
  simpa [h3] using h2

noncomputable def elem (p q : Fin n) (h : p ≠ q) (t : ZMod g) : Gn g n :=
  ⟨Matrix.transvection p q t, Matrix.transvection p q (-t),
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp,
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp⟩

theorem mul_elem_apply (p q : Fin n) (h : p ≠ q) (t : ZMod g) (x : Gn g n) (r c : Fin n) :
    ((x * elem p q h t : Gn g n) : Mt g n) r c
      = (x : Mt g n) r c + if c = q then t * (x : Mt g n) r p else 0 := by
  change ((x : Mt g n) * Matrix.transvection p q t) r c = _
  by_cases hc : c = q
  · subst hc; simp
  · simp [hc]

theorem isUniUp_of_col {M M' : Mt g n} {p q : Fin n} (hpq : p < q) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = q then t * M r p else 0) (hM : IsUniUp M) : IsUniUp M' := by
  intro r c
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [h, (hM r c).1 hc]
    split_ifs with h1
    · rw [(hM r p).1 (by subst h1; exact hpq.trans hc)]; simp
    · simp
  · rw [h, (hM r c).2 hc]
    split_ifs with h1
    · rw [(hM r p).1 (by subst h1; subst hc; exact hpq)]; simp
    · simp

theorem isUniUp_iff_of_col {M M' : Mt g n} {p q : Fin n} (hpq : p < q) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = q then t * M r p else 0) : IsUniUp M' ↔ IsUniUp M := by
  refine ⟨isUniUp_of_col hpq (-t) fun r c => ?_, isUniUp_of_col hpq t h⟩
  rw [h r c, h r p, if_neg hpq.ne]
  split_ifs <;> ring

theorem supFrom_of_col {M M' : Mt g n} {p q : Fin n} (hpq : (q : ℕ) = p + 1) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = q then t * M r p else 0) (hM : IsUniUp M) :
    supFrom 0 M' = supFrom 0 M + t := by
  have hq := q.2
  have : ∀ k ∈ Finset.Ico 0 (n - 1),
      entN M' k (k + 1) = entN M k (k + 1) + if k = (p : ℕ) then t else 0 := by
    intro k hk
    have hk' : k < n ∧ k + 1 < n := by have := (Finset.mem_Ico.1 hk).2; omega
    unfold entN
    rw [dite_eq_left hk', dite_eq_left hk', h]
    congr 1
    by_cases hkp : k = (p : ℕ)
    · rw [if_pos hkp, if_pos (Fin.ext (by simp [hkp, hpq])), (hM _ p).2 (Fin.ext hkp), mul_one]
    · rw [if_neg hkp, if_neg]
      intro h1
      have := congrArg Fin.val h1
      simp only at this
      omega
  unfold supFrom
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos]
  rw [Finset.mem_Ico]; omega

theorem inPar_iff_of_col {M M' : Mt g n} {a : ℕ} {i j : Fin n} (hj : a ≤ (j : ℕ)) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = j then t * M r i else 0) : InPar a M' ↔ InPar a M := by
  refine forall_congr' fun r => forall_congr' fun c => forall_congr' fun hc => ?_
  rw [h, if_neg (by rintro rfl; omega), add_zero]

theorem tl_of_col {M M' : Mt g n} {a : ℕ} {i j : Fin n} (hj : a ≤ (j : ℕ)) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = j then t * M r i else 0) : tl a M' = tl a M := by
  ext r c
  unfold tl entN
  split_ifs with h1
  · rw [h, if_neg, add_zero]
    rintro rfl
    have := c.2
    simp only at hj
    omega
  · rfl

theorem br_of_col {M M' : Mt g n} {a b : ℕ} {i j : Fin n} (hi : (i : ℕ) < a) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = j then t * M r i else 0) (hM : InPar a M) :
    br a b M' = br a b M := by
  ext r c
  unfold br entN
  split_ifs with h1
  · rw [h, hM _ i hi (by simp)]; simp
  · rfl

theorem whittaker_term_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (a b n : ℕ) (σ : Equiv.Perm (Fin n)) (Φ : Gn g a → Gn g b → ℂ) (i j : Fin n), n = a + b → (i : ℕ) < a → a ≤ (j : ℕ) → (σ j : ℕ) = σ i + 1 → (∑ x : Gn g n, if IsUniUp (x : Mt g n) ∧ InPar a (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) then (ψ (supFrom 0 (x : Mt g n)))⁻¹ * Φ (toG (tl a (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n))) (toG (br a b (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n))) else 0) = 0 := by
  intro g _ ψ hψ a b n σ Φ i j _ hi hj hσ
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hψ (by ext t; simpa using hc t)
  have hlt : σ i < σ j := by rw [Fin.lt_def]; omega
  set F : Gn g n → ℂ := fun x => if IsUniUp (x : Mt g n) ∧ InPar a (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) then (ψ (supFrom 0 (x : Mt g n)))⁻¹ * Φ (toG (tl a (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n))) (toG (br a b (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n))) else 0 with hF
  have key : ∀ x, F (x * elem (σ i) (σ j) hlt.ne t) = (ψ t)⁻¹ * F x := by
    intro x
    have h1 := mul_elem_apply (σ i) (σ j) hlt.ne t x
    have h2 : ∀ r c, (((pm g σ)⁻¹ * (x * elem (σ i) (σ j) hlt.ne t) * pm g σ : Gn g n) : Mt g n) r c
        = (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) r c
          + if c = j then t * (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) r i else 0 := by
      intro r c
      rw [conj_apply, conj_apply, conj_apply, h1]
      simp only [σ.apply_eq_iff_eq]
    simp only [hF]
    rw [isUniUp_iff_of_col hlt t h1, inPar_iff_of_col hj t h2]
    split_ifs with hx
    · rw [supFrom_of_col hσ t h1 hx.1, tl_of_col hj t h2, br_of_col hi t h2 hx.2, AddChar.map_add_eq_mul,
        mul_inv]
      ring
    · simp
  have hS : ∑ x, F x = (ψ t)⁻¹ * ∑ x, F x := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulRight (elem (σ i) (σ j) hlt.ne t)) F]
    exact Finset.sum_congr rfl fun x _ => key x
  change ∑ x, F x = 0
  by_contra hne
  apply ht
  have : (ψ t)⁻¹ = 1 := mul_right_cancel₀ hne (by rw [one_mul]; exact hS.symm)
  exact inv_eq_one.1 this

end GlobalTheory.GLm.NonOpenCell
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas.UnipRad

variable {n : ℕ} {ε : Fin n → Bool}

private lemma uMat_mul' (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

private lemma uMat_one' : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

private lemma inv_mulVec_mulVec (g : Formalism.REAL.UJ ε) (y : Fin n → ℂ) : uMat g⁻¹ *ᵥ (uMat g *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← uMat_mul', inv_mul_cancel, uMat_one', Matrix.one_mulVec]

lemma inv_keeps (g : Formalism.REAL.UJ ε) (V : Submodule ℂ (Fin n → ℂ)) (h : ∀ y ∈ V, uMat g *ᵥ y ∈ V) :
    ∀ y ∈ V, uMat g⁻¹ *ᵥ y ∈ V := by
  intro y hy
  have h' : ∀ y ∈ V, Matrix.toLin' (uMat g) y ∈ V := fun y hy => by simpa using h y hy
  have hinj : Function.Injective ((Matrix.toLin' (uMat g)).restrict h') := by
    intro x z hxz
    have h1 : uMat g *ᵥ (x : Fin n → ℂ) = uMat g *ᵥ (z : Fin n → ℂ) := by
      simpa using congrArg Subtype.val hxz
    apply Subtype.ext
    rw [← inv_mulVec_mulVec g x, h1, inv_mulVec_mulVec]
  obtain ⟨x, hx⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨y, hy⟩
  have h1 : uMat g *ᵥ (x : Fin n → ℂ) = y := by simpa using congrArg Subtype.val hx
  rw [← h1, inv_mulVec_mulVec]
  exact x.2

lemma keeps {a : ℕ} {j : Fin a → ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (hW : IsIsoFlag ε j W)
    (u : Formalism.REAL.UJ ε) (hu : u ∈ flagN ε W) (i : Fin (a + 1)) : ∀ y ∈ W i, uMat u *ᵥ y ∈ W i := by
  intro y hy
  induction i using Fin.cases with
  | zero =>
    rw [hW.1] at hy ⊢
    rw [(Submodule.mem_bot ℂ).mp hy]
    simp
  | succ i =>
    have h1 := hW.2.1 (Fin.castSucc_le_succ i) (hu.1 i y hy)
    simpa using (W i.succ).add_mem h1 hy

private lemma step_mul (g h : Formalism.REAL.UJ ε) (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ)
    (hk : ∀ y ∈ V, uMat g *ᵥ y ∈ V) (h1 : uMat g *ᵥ y - y ∈ V) (h2 : uMat h *ᵥ y - y ∈ V) :
    uMat (g * h) *ᵥ y - y ∈ V := by
  have := V.add_mem (hk _ h2) h1
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← uMat_mul'] at this
  simpa using this

private lemma step_inv (g : Formalism.REAL.UJ ε) (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ)
    (hk : ∀ y ∈ V, uMat g *ᵥ y ∈ V) (h1 : uMat g *ᵥ y - y ∈ V) :
    uMat g⁻¹ *ᵥ y - y ∈ V := by
  have := V.neg_mem (inv_keeps g V hk _ h1)
  rw [Matrix.mulVec_sub, inv_mulVec_mulVec] at this
  simpa using this

private lemma closed_step (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    IsClosed {g : Formalism.REAL.UJ ε | uMat g *ᵥ y - y ∈ V} := by
  have hc : Continuous fun g : Formalism.REAL.UJ ε => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  exact V.closed_of_finiteDimensional.preimage
    ((hc.matrix_mulVec continuous_const).sub continuous_const)

theorem flagN_subgroup_closed_keeps (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (hW : IsIsoFlag ε j W) :
    (∃ N : Subgroup (Formalism.REAL.UJ ε), (N : Set (Formalism.REAL.UJ ε)) = flagN ε W) ∧ IsClosed (flagN ε W) ∧
      ∀ u ∈ flagN ε W, ∀ i, ∀ y ∈ W i, uMat u *ᵥ y ∈ W i := by
  refine ⟨⟨{ carrier := flagN ε W, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩, ?_,
    fun u hu i => keeps hW u hu i⟩
  · intro g h hg hh
    exact ⟨fun i y hy => step_mul g h _ y (keeps hW g hg _) (hg.1 i y hy) (hh.1 i y hy),
      fun y hy => step_mul g h _ y (keeps hW g hg _) (hg.2 y hy) (hh.2 y hy)⟩
  · refine ⟨fun i y _ => ?_, fun y _ => ?_⟩ <;>
    · rw [uMat_one', Matrix.one_mulVec, sub_self]
      exact Submodule.zero_mem _
  · intro g hg
    exact ⟨fun i y hy => step_inv g _ y (keeps hW g hg _) (hg.1 i y hy),
      fun y hy => step_inv g _ y (keeps hW g hg _) (hg.2 y hy)⟩
  · unfold flagN
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_iInter fun y => isClosed_iInter fun _ => closed_step _ y).inter
      (isClosed_iInter fun y => isClosed_iInter fun _ => closed_step _ y)

end GlobalTheory.FlagMeas.UnipRad
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.folner_single_translate_proportion_tendsto_one : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r)) (Om : ℕ → Set (Mt k r)), IsFolner S μ Om → ∀ p ∈ S, Filter.Tendsto (fun j => μ {s | s ∈ Om j ∧ lmulM p s ∈ Om j} / μ (Om j)) Filter.atTop (nhds 1) := by
  first | exact @GlobalTheory.SgInf.folner_single_translate | exact GlobalTheory.SgInf.folner_single_translate | (intros; apply GlobalTheory.SgInf.folner_single_translate <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.isCompact_normBounded_besselClosedSubgroup : ∀ (k r : ℕ) (S : Set (Mat k r)), IsClosedSub k r S → ∀ R : ℝ, IsCompact {g | g ∈ S ∧ opn g ≤ R} := by
  first | exact @GlobalTheory.SgInf.isCompact_normBounded | exact GlobalTheory.SgInf.isCompact_normBounded | (intros; apply GlobalTheory.SgInf.isCompact_normBounded <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselFormalDegree_eq_of_schurOrthogonality : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (d : ℝ) (w : H), SchurH μG σ d → w ≠ 0 → fdegH μG σ w = d := by
  first | exact @GlobalTheory.SgInf.fdegH_eq_of_schurH | exact GlobalTheory.SgInf.fdegH_eq_of_schurH | (intros; apply GlobalTheory.SgInf.fdegH_eq_of_schurH <;> assumption)
end
