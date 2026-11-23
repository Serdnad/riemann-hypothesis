module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle006
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {F : Type} [Field F] {n : ℕ}

private def sgnM (F : Type) [Field F] (n a : ℕ) : Matrix (Fin n) (Fin n) F :=
  Matrix.diagonal fun i => if (i : ℕ) < a then 1 else -1

private theorem sgnM_sq (a : ℕ) : sgnM F n a * sgnM F n a = 1 := by
  rw [sgnM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  split_ifs <;> simp

private theorem sgnM_conj_apply (a : ℕ) (X : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    (sgnM F n a * X * sgnM F n a) i j = if ((i : ℕ) < a ↔ (j : ℕ) < a) then X i j else -X i j := by
  simp only [sgnM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj]

private theorem sgnM_ev (a : ℕ) {X : Matrix (Fin n) (Fin n) F} (hX : X ∈ Ev F F n a) :
    sgnM F n a * X * sgnM F n a = X := by
  have hX' : ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊤ : Submodule F F)) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊥ : Submodule F F)) := hX
  ext i j
  rw [sgnM_conj_apply]
  split_ifs with h
  · rfl
  · have h0 : X i j = 0 := by simpa using (hX' i j).2 h
    rw [h0, neg_zero]

private theorem sgnM_od (a : ℕ) {X : Matrix (Fin n) (Fin n) F} (hX : X ∈ Od F F n a) :
    sgnM F n a * X * sgnM F n a = -X := by
  have hX' : ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊥ : Submodule F F)) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊤ : Submodule F F)) := hX
  ext i j
  rw [sgnM_conj_apply, Matrix.neg_apply]
  split_ifs with h
  · have h0 : X i j = 0 := by simpa using (hX' i j).1 h
    rw [h0, neg_zero]
  · rfl

private theorem od_of_sgnM (two : (2 : F) ≠ 0) (a : ℕ) {X : Matrix (Fin n) (Fin n) F}
    (hX : sgnM F n a * X * sgnM F n a = -X) : X ∈ Od F F n a := by
  show ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊥ : Submodule F F)) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → X i j ∈ (⊤ : Submodule F F))
  intro i j
  refine ⟨fun h => ?_, fun _ => Submodule.mem_top⟩
  have e := congrFun (congrFun hX i) j
  rw [sgnM_conj_apply, if_pos h, Matrix.neg_apply] at e
  have h2 : (2 : F) * X i j = 0 := by rw [two_mul]; nth_rewrite 1 [e]; ring
  rw [Submodule.mem_bot]
  exact (mul_eq_zero.mp h2).resolve_left two

private theorem sgnM_mul (a : ℕ) (X Y : Matrix (Fin n) (Fin n) F) :
    sgnM F n a * (X * Y) * sgnM F n a = (sgnM F n a * X * sgnM F n a) * (sgnM F n a * Y * sgnM F n a) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (sgnM F n a) (sgnM F n a), sgnM_sq, Matrix.one_mul]

private theorem sgnM_dTw {G : Type} [Group G] (D : DetFr F G n) (χ : G → F) (Y : Matrix (Fin n) (Fin n) F) (g : G) :
    sgnM F n D.a * dTw χ D.r Y g * sgnM F n D.a = dTw χ D.r (sgnM F n D.a * Y * sgnM F n D.a) g := by
  simp only [dTw, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, sgnM_mul,
    sgnM_ev D.a (D.ev g), sgnM_ev D.a (D.ev g⁻¹)]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.Det.infres :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (z : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F), (∀ g h, χ (g * h) = χ g * χ h) → (∀ g ∈ D.G', χ g = 1) → TwCoc χ D.r Set.univ z → (∀ g, z g ∈ Od F F n D.a) → (∀ g ∈ D.G', z g = dTw χ D.r Y g) → ∃ Y' ∈ Od F F n D.a, ∀ g, z g = dTw χ D.r Y' g := by
  intro F G _ _ n D χ z Y hχ hχ' hz hzod hzG
  have two : (2 : F) ≠ 0 := D.two
  have hdTw_sub : ∀ A B g, dTw χ D.r (A - B) g = dTw χ D.r A g - dTw χ D.r B g := by
    intro A B g
    simp only [dTw, Matrix.mul_sub, Matrix.sub_mul, smul_sub]
    abel
  have hdTw_smul : ∀ (c : F) A g, dTw χ D.r (c • A) g = c • dTw χ D.r A g := by
    intro c A g
    simp only [dTw, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    rw [smul_comm]
  have hdTw_neg : ∀ A g, dTw χ D.r (-A) g = -dTw χ D.r A g := by
    intro A g
    simp only [dTw, Matrix.mul_neg, Matrix.neg_mul, smul_neg]
    abel
  have hdc : ∀ A g h, dTw χ D.r A (g * h) = dTw χ D.r A g + χ g • (D.r g * dTw χ D.r A h * D.r g⁻¹) := by
    intro A g h
    simp only [dTw, hχ, _root_.mul_inv_rev, map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_sub, smul_smul, Matrix.mul_assoc]
    abel
  have hss := sgnM_sq (F := F) (n := n) D.a
  have hcc : ∀ A : Matrix (Fin n) (Fin n) F,
      sgnM F n D.a * (sgnM F n D.a * A * sgnM F n D.a) * sgnM F n D.a = A := by
    intro A
    rw [show sgnM F n D.a * (sgnM F n D.a * A * sgnM F n D.a) * sgnM F n D.a
        = (sgnM F n D.a * sgnM F n D.a) * A * (sgnM F n D.a * sgnM F n D.a) by
      simp only [Matrix.mul_assoc], hss, Matrix.one_mul, Matrix.mul_one]
  set Y' : Matrix (Fin n) (Fin n) F := (2 : F)⁻¹ • (Y - sgnM F n D.a * Y * sgnM F n D.a) with hY'
  have hY'od : Y' ∈ Od F F n D.a := by
    apply od_of_sgnM two
    rw [hY', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, hcc, ← smul_neg, neg_sub]
  have hG' : ∀ h ∈ D.G', z h = dTw χ D.r Y' h := by
    intro h hh
    have h1 := hzG h hh
    have h2 : -z h = dTw χ D.r (sgnM F n D.a * Y * sgnM F n D.a) h := by
      rw [← sgnM_od D.a (hzod h), h1, sgnM_dTw]
    rw [hY', hdTw_smul, hdTw_sub, ← h1, ← h2, sub_neg_eq_add, ← two_smul F (z h), smul_smul,
      inv_mul_cancel₀ two, one_smul]
  have key : ∀ g, z g - dTw χ D.r Y' g = 0 := by
    intro g
    set w : G → Matrix (Fin n) (Fin n) F := fun x => z x - dTw χ D.r Y' x with hw
    have hwc : ∀ x y, w (x * y) = w x + χ x • (D.r x * w y * D.r x⁻¹) := by
      intro x y
      simp only [hw]
      rw [hz x trivial y trivial, hdc]
      simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub]
      abel
    have hw0 : ∀ h ∈ D.G', w h = 0 := fun h hh => by
      simp only [hw]
      rw [hG' h hh, sub_self]
    have hcomm : ∀ h ∈ D.G', D.r h * w g = w g * D.r h := by
      intro h hh
      have hh' : g⁻¹ * h * g ∈ D.G' := by
        have hm := D.G'.mul_mem (D.comm g⁻¹ h) hh
        simpa [mul_assoc] using hm
      have e1 := hwc g (g⁻¹ * h * g)
      have e2 := hwc h g
      rw [hw0 _ hh', Matrix.mul_zero, Matrix.zero_mul, smul_zero, add_zero] at e1
      rw [hw0 _ hh, hχ' h hh, one_smul, zero_add] at e2
      have heq : g * (g⁻¹ * h * g) = h * g := by group
      rw [heq, e2] at e1
      calc D.r h * w g = D.r h * w g * (D.r h⁻¹ * D.r h) := by
            rw [← map_mul D.r h⁻¹ h, inv_mul_cancel, map_one, Matrix.mul_one]
        _ = (D.r h * w g * D.r h⁻¹) * D.r h := by simp only [Matrix.mul_assoc]
        _ = w g * D.r h := by rw [e1]
    have hwod : w g ∈ Od F F n D.a := by
      simp only [hw]
      refine Submodule.sub_mem _ (hzod g) ?_
      apply od_of_sgnM two
      rw [sgnM_dTw, sgnM_od D.a hY'od, hdTw_neg]
    exact (Det.central D (w g) hcomm).1 hwod
  exact ⟨Y', hY'od, fun g => sub_eq_zero.mp (key g)⟩
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem shapiro_projection_twisted_cocycle {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (s : F)
    (z : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F) (hχ : ∀ g, χ (D.σ g) = χ g)
    (hs : s * s = 1) (hp : ∀ g, z (D.σ g) = s • (z g)ᵀ)
    (P : Matrix (Fin n) (Fin n) F → Matrix (Fin n) (Fin n) F)
    (hPP : ∀ Z, P (P Z) = P Z) (hPs : ∀ Z, P (s • Z) = s • P Z)
    (hPd : ∀ g, P (dTw χ D.r Y g) = dTw χ D.r (P Y) g)
    (hsum : ∀ g, P (z g) + (P (z g)ᵀ)ᵀ = z g)
    (h1 : P Y ∈ Od F F n D.a) (h2 : (P Y)ᵀ ∈ Od F F n D.a)
    (h : ∀ g, P (z g) = dTw χ D.r Y g) :
    ∃ Y' ∈ Od F F n D.a, s • Y'ᵀ = Y' ∧ ∀ g, z g = dTw χ D.r Y' g := by
  refine ⟨P Y + s • (P Y)ᵀ, Submodule.add_mem _ h1 (Submodule.smul_mem _ s h2), ?_, ?_⟩
  · rw [transpose_add, transpose_smul, transpose_transpose, smul_add, smul_smul, hs, one_smul,
      add_comm]
  · intro g
    have hA : ∀ k, dTw χ D.r (P Y) k = P (z k) := fun k => by
      rw [← hPd, ← h, hPP]
    have hzT : (z g)ᵀ = s • z (D.σ g) := by
      rw [hp, smul_smul, hs, one_smul]
    have hB : s • dTw χ D.r (P Y)ᵀ g = (P (z g)ᵀ)ᵀ := by
      rw [hzT, hPs, ← hA, Det.dSigma D χ (P Y) g hχ, transpose_smul, transpose_transpose]
    have hlin : dTw χ D.r (P Y + s • (P Y)ᵀ) g = dTw χ D.r (P Y) g + s • dTw χ D.r (P Y)ᵀ g := by
      simp only [dTw, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      module
    rw [hlin, hA, hB, hsum]

theorem UpperTheory.V.Pa.Det.shapiro :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (s : F) (z : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F), (∀ g, χ (D.σ g) = χ g) → s * s = 1 → TwCoc χ D.r Set.univ z → (∀ g, z g ∈ Od F F n D.a) → (∀ g, z (D.σ g) = s • (z g)ᵀ) → ((∀ g, cV D.a (z g) = dTw χ D.r Y g) ∨ ∀ g, cV' D.a (z g) = dTw χ D.r Y g) → ∃ Y' ∈ Od F F n D.a, s • Y'ᵀ = Y' ∧ ∀ g, z g = dTw χ D.r Y' g := by
  intro F G _ _ n D χ s z Y hχ hs hz hod hp h
  obtain ⟨-, -, hd, hc⟩ := UpperTheory.V.Pa.Det.cornerCoc D χ Set.univ z hz
  have ht : ∀ Z : Matrix (Fin n) (Fin n) F, (cV' D.a Z)ᵀ = cV D.a Zᵀ := fun Z => by
    have := (hc Zᵀ).2.2.1
    rw [transpose_transpose] at this
    rw [← this, transpose_transpose]
  rcases h with h | h
  · refine shapiro_projection_twisted_cocycle D χ s z Y hχ hs hp (cV D.a) (fun Z => ?_) (fun Z => ?_) (fun g => (hd Y g).1)
      (fun g => ?_) (hc Y).1 ?_ h
    · ext i j
      simp only [cV, Matrix.of_apply]
      split_ifs <;> rfl
    · ext i j
      simp only [cV, Matrix.of_apply, Matrix.smul_apply]
      split_ifs <;> simp
    · rw [(hc _).2.2.1, transpose_transpose]
      exact (hc _).2.2.2 (hod g)
    · rw [(hc _).2.2.1]
      exact (hc _).2.1
  · refine shapiro_projection_twisted_cocycle D χ s z Y hχ hs hp (cV' D.a) (fun Z => ?_) (fun Z => ?_) (fun g => (hd Y g).2)
      (fun g => ?_) (hc Y).2.1 ?_ h
    · ext i j
      simp only [cV', Matrix.of_apply]
      split_ifs <;> rfl
    · ext i j
      simp only [cV', Matrix.of_apply, Matrix.smul_apply]
      split_ifs <;> simp
    · rw [ht, transpose_transpose, add_comm]
      exact (hc _).2.2.2 (hod g)
    · rw [ht]
      exact (hc _).1
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.kapPush :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext2 x' j → ∀ k : Kap x, ∃ (k' : Kap x') (e : k'.g = k.g), (∀ i g, k'.κ i g = (k.κ (Fin.cast e i) g).map j) ∧ ∀ i v, k'.Y i v = (k.Y (Fin.cast e i) v).map j := by
  intro l _ F n x x' j hE k
  obtain ⟨m, b, p, -, hb, hp, -, hc, e, u, -, hu⟩ := UpperTheory.V.Pa.Det.extFree j hE.1.1 hE.1.2.1 hE.1.2.2.1
  obtain ⟨pS, pB, pL⟩ := UpperTheory.V.Pa.Det.pushSel x x' j hE
  have cS := fun i => (UpperTheory.V.Pa.Det.compSel x x' j hE (p i) (hp i) (fun N => (hc N).imp fun _ h y hy => h y hy i)).1
  have cB := fun i => (UpperTheory.V.Pa.Det.compSel x x' j hE (p i) (hp i) (fun N => (hc N).imp fun _ h y hy => h y hy i)).2
  obtain ⟨S, hS⟩ := (UpperTheory.V.Pa.Det.selSub F x'.t (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (Od x'.A x'.A n x'.a)).2
  have ha : x'.a = x.a := hE.1.2.2.2.2.1
  refine ⟨⟨k.g, fun i g => (k.κ i g).map j, fun i => pS _ (k.mem i), fun i v => (k.Y i v).map j, ?_,
    fun i v => pL _ _ _ (k.loc i v), ?_, ?_⟩, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro i v r s
    refine ⟨fun h => ?_, fun _ => Submodule.mem_top⟩
    have := (k.Y_mem i v r s).1 (by rw [← ha]; exact h)
    rw [Submodule.mem_bot] at this ⊢
    simp [this]
  · intro c hcB
    have h0 : ∀ i, (fun a => p i (c a)) = 0 := by
      intro i
      apply k.indep
      convert cB i _ hcB using 1
      funext g
      ext r s : 1

      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_comm (c a), hp, mul_comm]
    funext a
    rw [hb (c a)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show p i (c a) = 0 from congrFun (h0 i) a, map_zero, zero_mul]
  · intro z hz
    choose s c hsc using fun i => k.gen _ (cS i z hz)
    have hle : ∀ i, s i ≤ ∑ i, s i := fun i =>
      Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    set N := ∑ i, s i with hN
    let d : Fin m → x'.A := fun i => ((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) * b i * j (x.t ^ (N - s i))
    have h3 : (u : x'.A) ^ N * ((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow, Units.val_one]
    have key : ∀ y : x'.A, ∑ i, d i * j (x.t ^ s i * p i y) = x'.t ^ (e * N) * y := by
      intro y
      conv_rhs => rw [hb y, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h4 : j (x.t ^ (N - s i)) * j (x.t ^ s i) = (u : x'.A) ^ N * x'.t ^ (e * N) := by
        rw [← map_mul, ← pow_add, Nat.sub_add_cancel (hle i), map_pow, hu, mul_pow, pow_mul]
      simp only [d, map_mul]
      linear_combination (((u⁻¹ ^ N : (PowerSeries x'.K)ˣ) : x'.A) * b i * j (p i y)) * h4
        + (x'.t ^ (e * N) * b i * j (p i y)) * h3
    refine ⟨e * N, fun a => ∑ i, d i * j (c i a), ?_⟩
    have hm : ∑ i, d i • (fun g => ((x.t ^ s i • (fun g => (z g).map (p i)) - ∑ a, c i a • k.κ a) g).map j) ∈ S := by
      refine S.sum_mem fun i _ => S.smul_mem _ ?_
      have := pB _ (hsc i)
      rw [← hS] at this
      exact this
    rw [← hS, SetLike.mem_coe]
    convert hm using 1
    funext g
    ext r t : 1

    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul, map_sum, map_sub, mul_sub, Finset.sum_sub_distrib, key, Finset.sum_mul,
    Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    simp only [map_mul, mul_assoc]
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem charP_of_padic {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) :
    CharP K l := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpp : p.Prime := CharP.char_is_prime K p
  have hpK : ((p : ℕ) : K) = 0 := CharP.cast_eq_zero K p
  have hpl : p = l := by
    by_contra hne
    have hcop : l.Coprime p := (Nat.coprime_primes (Fact.out) hpp).2 (Ne.symm hne)
    have hu : IsUnit ((p : ℕ) : ℤ_[l]) :=
      PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hcop)
    have hu' := hu.map f
    rw [map_natCast, hpK] at hu'
    exact not_isUnit_zero hu'
  subst hpl
  exact hp

theorem UpperTheory.V.Pa.Det.kapEx :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n), PhiCond F.Γ l → Nonempty (Kap x) := by
  intro l _ F n x hΦ
  letI : Field x.K := x.field
  haveI : Finite x.K := x.fin
  letI : Algebra ℤ_[l] x.K := x.algZ
  haveI : CharP x.K l := charP_of_padic (algebraMap ℤ_[l] x.K)
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (F.η.ker.isClosed_of_isOpen F.η_open).isCompact
  have hΦ0 : PhiCond F.G₀ l := UpperTheory.V.Pa.Det.phiSub l F.η.ker F.η_open hΦ
  have hρ : x.ρX x.A = fun g => mat x.ρ g := by
    funext g
    simp [UpperTheory.V.Pa.NP.ρX, Algebra.algebraMap_self]
  obtain ⟨⟨S, hS⟩, ⟨B, hB⟩⟩ := UpperTheory.V.Pa.Det.selSub F (A := x.A) (R := x.A) x.t (x.ρX x.A)
    (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a)
  have hSfg : S.FG := by
    refine UpperTheory.V.Pa.Det.matFg l (K := x.K) (G := F.G₀) (R := x.A) (1 : F.G₀ →* x.A) (mat x.ρ) S hΦ0
      ?_ ?_ ?_
    · intro N
      simp only [MonoidHom.one_apply]
      exact IsLocallyConstant.const (X := F.G₀) _
    · intro i j
      have h := x.cont i j
      simpa [PowerSeries.maximalIdeal_eq_span_X] using h
    · intro z hz
      rw [← SetLike.mem_coe, hS] at hz
      refine ⟨hz.2.1, ?_⟩
      intro g _ h _
      have e := hz.2.2.1 g h
      rw [hρ] at e
      simpa using e
  obtain ⟨g, κ, hmem, hind, hgen⟩ :=
    UpperTheory.V.Pa.Det.maxIndep x.t S B PowerSeries.X_irreducible hSfg
  have hsel : ∀ j, κ j ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a) := by
    intro j
    rw [← hS]
    exact hmem j
  have hloc : ∀ j v, ∃ Y ∈ Od x.A x.A n x.a,
      LocAt F (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (κ j) v Y :=
    fun j v => (hsel j).2.2.2.2.2 v
  choose Y hYmem hYloc using hloc
  refine ⟨⟨g, κ, hsel, Y, hYmem, hYloc, ?_, ?_⟩⟩
  · intro c hc
    apply hind c
    rw [← SetLike.mem_coe, hB]
    exact hc
  · intro z hz
    rw [← hS] at hz
    obtain ⟨s, c, hsc⟩ := hgen z hz
    refine ⟨s, c, ?_⟩
    rw [← hB]
    exact hsc
end
