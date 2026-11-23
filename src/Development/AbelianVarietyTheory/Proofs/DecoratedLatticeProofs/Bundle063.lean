module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle124
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle057
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle061
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymChainPatternIffPlaceConditions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelTestFunctionsAgreeRationalPoints
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralEqFiniteSumOverNumberField
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelsCharactersDoubleCosetsAgreeRation
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle056
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain.ExchangeProof

section Step
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_inv_mul_le_one (a : kˣ) (z : k) :
    valuation k (((a⁻¹ : kˣ) : k) * z) ≤ 1 ↔ valuation k z ≤ valuation k (a : k) := by
  have : 0 < valuation k (a : k) := by simp [zero_lt_iff]
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_one₀ this]

variable [MeasurableSpace k] [BorelSpace k]


open Classical in
theorem opE_step (ν : Measure k) (hν : IsUnitVol ν) {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t]
    [DecidableEq t] (hP : S.Pattern t) (j c : ℕ) (H : j + c = s) (q : Fin c) (hq : q.val + 1 ≤ S.ρ)
    (hqc : q.val + 2 ≤ c) : ∃ C : ℝ, 0 < C ∧
      opE S.ψ ν (q.val + 2) ((S.T t).Phi j c H) = (C : ℂ) • opE S.ψ ν (q.val + 1) ((S.T t).Phi j c H) := by
  haveI := hν.1
  have := secondCountable k
  have := t2Space k
  set Φ := (S.T t).Phi j c H with hΦ
  let I := (XIx (Fin κ) t (j + 1) ⊕ Fin c) × (XIx (Fin κ) t j ⊕ Fin (c + 1))
  let A : I → Prop := fun i => i.1 = Sum.inr q ∧ i.2.isLeft = true
  let B : I → Prop := fun i => i.2 = Sum.inr q.succ ∧ i.1.isLeft = true
  let R : I → Prop := fun i => Free (q.val + 1) i ∧ ¬ B i
  let a : kˣ := S.ϖ ^ (q.val + 1)
  let b : kˣ := S.ϖ ^ (q.val + 2)
  let sA : Set k := cball a
  let sB : Set k := (fun z => (b : k) * z) ⁻¹' {z | valuation k z < 1}
  have oB : IsOpen sB := IsOpen.preimage (by fun_prop) (by simpa using (valuation k).isOpen_ball 1)
  have sBc : sB ⊆ cball b⁻¹ := fun z hz => by
    have hz : valuation k ((b : k) * z) < 1 := hz
    have : 0 < valuation k (b : k) := by simp [zero_lt_iff]
    rw [map_mul] at hz
    change valuation k z ≤ valuation k ((b⁻¹ : kˣ) : k)
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    have h1 : valuation k z = (valuation k (b : k))⁻¹ * (valuation k (b : k) * valuation k z) := by
      rw [← mul_assoc, inv_mul_cancel₀ this.ne', one_mul]
    rw [h1]; exact mul_le_of_le_one_right' hz.le
  have mA : MeasurableSet sA := (isOpen_cball a).measurableSet
  have mB : MeasurableSet sB := oB.measurableSet
  have fA : ν sA ≠ ⊤ := (isCompact_cball a).measure_lt_top.ne
  have fB : ν sB ≠ ⊤ := ((isCompact_cball b⁻¹).measure_lt_top.trans_le' (measure_mono sBc)).ne
  have pA : 0 < ν sA := (isOpen_cball a).measure_pos ν ⟨0, by simp [sA, cball]⟩
  have pB : 0 < ν sB := oB.measure_pos ν ⟨0, by simp [sB]⟩
  let G : Matrix (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) k → (I → k) → ℂ := fun x₀ m =>
    Φ (basePt c x₀ + Matrix.of fun r s' => m (r, s')) * (S.ψ (-ch (basePt c x₀ + Matrix.of fun r s' => m (r, s'))) : ℂ)
  have hR2 : ∀ i, R i ↔ Free (q.val + 2) i ∧ ¬ A i := by
    rintro ⟨r | r, s' | s'⟩ <;> simp [R, A, B, Free, Fin.ext_iff] <;> omega
  have hR1 : ∀ i, R i ↔ Free (q.val + 1) i ∧ ¬ B i := fun i => Iff.rfl
  have hA : ∀ i, A i → Free (q.val + 2) i := by
    rintro ⟨r | r, s' | s'⟩ h <;> simp_all [A, Free]
  have hB : ∀ i, B i → Free (q.val + 1) i := by
    rintro ⟨r | r, s' | s'⟩ h <;> simp_all [B, Free]
  have gA : ∀ x₀ (m : I → k), G x₀ m = (if ∀ i, A i → m i ∈ sA then (1 : ℂ) else 0) * G x₀ (fun i => if A i then 0 else m i) := by
    intro x₀ m
    let v : XIx (Fin κ) t j → k := fun s' => m (Sum.inr q, Sum.inl s')
    have hx : (basePt c x₀ + Matrix.of fun r s' => m (r, s')) = (basePt c x₀ + Matrix.of fun r s' =>
        (if A (r, s') then 0 else m (r, s'))) + Matrix.of fun r s' => if r = Sum.inr q then Sum.elim v 0 s' else 0 := by
      ext (r | r) (s' | s')
      · simp [A]
      · simp [A]
      · by_cases h : r = q
        · subst h; simp [A, v, basePt]
        · simp [A, h]
      · simp [A]
    have hch : ch (basePt c x₀ + Matrix.of fun r s' => m (r, s')) =
        ch (basePt c x₀ + Matrix.of fun r s' => (if A (r, s') then 0 else m (r, s'))) := by
      simp [ch, A]
    have row0 : ∀ s', (basePt c x₀ + Matrix.of fun r s' => (if A (r, s') then 0 else m (r, s'))) (Sum.inr q) (Sum.inl s') = 0 := by
      intro s'; simp [basePt, A]
    have hiff : (∀ s', valuation k ((((S.ϖ ^ (q.val + 1))⁻¹ : kˣ) : k) * v s') ≤ 1) ↔ ∀ i, A i → m i ∈ sA := by
      constructor
      · rintro h ⟨r, s' | s'⟩ ⟨rfl, hs⟩
        · exact (val_inv_mul_le_one a _).1 (h s')
        · simp at hs
      · intro h s'; exact (val_inv_mul_le_one a _).2 (h (Sum.inr q, Sum.inl s') ⟨rfl, rfl⟩)
    simp only [G]
    rw [hch, hx, hΦ, GlobalTheory.T.symLevelChain_testFunction_add_row k s κ S t hP j c H q hq _ row0 v]
    by_cases hc : ∀ i, A i → m i ∈ sA
    · rw [if_pos (hiff.2 hc), if_pos hc, one_mul]
    · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc, zero_mul, zero_mul]
  have gB : ∀ x₀ (m : I → k), G x₀ m = (if ∀ i, B i → m i ∈ sB then (1 : ℂ) else 0) * G x₀ (fun i => if B i then 0 else m i) := by
    intro x₀ m
    let w : XIx (Fin κ) t (j + 1) → k := fun r => m (Sum.inl r, Sum.inr q.succ)
    have hx : (basePt c x₀ + Matrix.of fun r s' => m (r, s')) = (basePt c x₀ + Matrix.of fun r s' =>
        (if B (r, s') then 0 else m (r, s'))) + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0 := by
      ext (r | r) (s' | s')
      · simp [B]
      · by_cases h : s' = q.succ
        · subst h; simp [B, w, basePt]
        · simp [B, h]
      · simp [B]
      · simp [B]
    have hch : ch (basePt c x₀ + Matrix.of fun r s' => m (r, s')) =
        ch (basePt c x₀ + Matrix.of fun r s' => (if B (r, s') then 0 else m (r, s'))) := by
      simp [ch, B]
    have col0 : ∀ r, (basePt c x₀ + Matrix.of fun r s' => (if B (r, s') then 0 else m (r, s'))) (Sum.inl r) (Sum.inr q.succ) = 0 := by
      intro r; simp [basePt, B]
    have hiff : (∀ r, valuation k (((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r) < 1) ↔ ∀ i, B i → m i ∈ sB := by
      constructor
      · rintro h ⟨r | r, s'⟩ ⟨rfl, hs⟩
        · exact h r
        · simp at hs
      · intro h r; exact h (Sum.inl r, Sum.inr q.succ) ⟨rfl, rfl⟩
    simp only [G]
    rw [hch, hx, hΦ, GlobalTheory.T.matrix_block_column_vanishing_step k s κ S t hP j c H q hq hqc _ col0 w]
    by_cases hc : ∀ i, B i → m i ∈ sB
    · rw [if_pos (hiff.2 hc), if_pos hc, one_mul]
    · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc, zero_mul, zero_mul]
  have e2 : ∀ x₀, opE S.ψ ν (q.val + 2) Φ x₀ = (((ν sA).toReal ^ Fintype.card {i // A i} : ℝ) : ℂ) *
      ∫ e : {i // R i} → k, G x₀ (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) :=
    fun x₀ => GlobalTheory.T.integral_pi_block_indicator_eq_pow_mul k ν I (Free (q.val + 2)) A R hR2 hA sA mA fA (G x₀) (gA x₀)
  have e1 : ∀ x₀, opE S.ψ ν (q.val + 1) Φ x₀ = (((ν sB).toReal ^ Fintype.card {i // B i} : ℝ) : ℂ) *
      ∫ e : {i // R i} → k, G x₀ (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) :=
    fun x₀ => GlobalTheory.T.integral_pi_block_indicator_eq_pow_mul k ν I (Free (q.val + 1)) B R hR1 hB sB mB fB (G x₀) (gB x₀)
  have tA : 0 < (ν sA).toReal := ENNReal.toReal_pos pA.ne' fA
  have tB : 0 < (ν sB).toReal := ENNReal.toReal_pos pB.ne' fB
  refine ⟨(ν sA).toReal ^ Fintype.card {i // A i} / (ν sB).toReal ^ Fintype.card {i // B i},
    div_pos (pow_pos tA _) (pow_pos tB _), funext fun x₀ => ?_⟩
  rw [Pi.smul_apply, e2, e1, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ _ (pow_pos tB _).ne']

end Step

theorem exchangeAt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type)
    [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hP j c H p hp1
  induction p, hp1 using Nat.le_induction with
  | base => intro _ _; exact ⟨1, one_pos, by simp⟩
  | succ p hp ih =>
    intro hpc hpρ
    obtain ⟨C, hC, e⟩ := ih (by omega) (by omega)
    obtain ⟨C', hC', e'⟩ := opE_step ν hν S t hP j c H ⟨p - 1, by omega⟩ (by simp; omega) (by simp; omega)
    have h2 : (p - 1) + 2 = p + 1 := by omega
    have h1 : (p - 1) + 1 = p := by omega
    simp only [h1, h2] at e'
    refine ⟨C' * C, mul_pos hC' hC, ?_⟩
    rw [e', e, smul_smul, Complex.ofReal_mul]

end GlobalTheory.SymChain.ExchangeProof
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.isUnramifiedHeightFunction_lowerBlock : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (H : GL (A ⊕ D) k → ℝ), IsHgt ϖ H → IsHgt ϖ (fun m : GL D k => H (emb₂ k (Equiv.refl (A ⊕ D)) (1, m))) := by
  first | exact @GlobalTheory.ParHecke.isHgt_lower | exact GlobalTheory.ParHecke.isHgt_lower | (intros; apply GlobalTheory.ParHecke.isHgt_lower <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.unramifiedTwist_sphericalFunction_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (N : ℕ) (ε : Fin N ≃ D) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (μ₀ : kˣ →* ℂˣ), IsUnram μ₀ → ∀ (β : Multiset ℂˣ) (f : GL D k → ℂ), (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) β s.card * f m) → ∀ f₂ : GL (Fin N) k → ℂ, (∀ m, f₂ m = (((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * f (GlobalTheory.ChainStepSupp.reGL k ε m)) → (∀ κ ∈ KO k (Fin N), ∀ m, f₂ (κ * m) = f₂ m ∧ f₂ (m * κ) = f₂ m) ∧ ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f₂ (m * g) = (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card * genVal (resCard k) 0 N β s.card * f₂ m := by
  first | exact @GlobalTheory.TwistRenumber.twist_renumber | exact GlobalTheory.TwistRenumber.twist_renumber | (intros; apply GlobalTheory.TwistRenumber.twist_renumber <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem GlobalTheory.ParHecke.heckeIdentity_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D D' : Type) [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ t : ℕ, Fintype.card D' = Fintype.card D + t → ∀ (s : Finset D') RK, IsRepsK (torusElt k D' ϖ (indic s)) RK → ∀ (sn : ℕ → Finset D) (Rn : ℕ → Finset (GL D k)), (∀ n ≤ Fintype.card D, (sn n).card = n ∧ IsRepsK (torusElt k D ϖ (-indic (sn n))) (Rn n)) → ∀ y : Matrix D' D k, ∑ g ∈ RK, intInd ((g⁻¹).1 * y) = ∑ n ∈ Finset.range (Fintype.card D + 1), (if n ≤ s.card then ((resCard k ^ (n * (t - (s.card - n))) * Formalism.L2.Col.gaussBin (resCard k) t (s.card - n) : ℕ) : ℂ) else 0) * ∑ g ∈ Rn n, intInd (y * g.1) := by
  intro k _ _ _ _ D D' _ _ _ _ ϖ hϖ t ht s RK hRK sn Rn hRn y
  have hL := GlobalTheory.T.sum_integralIndicator_cosets_subspaces_containing k D D' ϖ hϖ s RK hRK y
  by_cases hy : ∀ i j, y i j ∈ 𝒪[k]
  · let y₀ : Matrix D' D 𝒪[k] := fun i j => ⟨y i j, hy i j⟩
    have hy₀ : y = y₀.map (algebraMap 𝒪[k] k) := by
      ext i j; rfl
    rw [hL.2 y₀ hy₀]
    have hR : ∀ n ∈ Finset.range (Fintype.card D + 1), ∑ g ∈ Rn n, intInd (y * g.1) =
        (Nat.card {U : Submodule 𝓀[k] (D → 𝓀[k]) // U ≤ LinearMap.ker (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ∧ Module.finrank 𝓀[k] U = n} : ℂ) := by
      intro n hn
      have hn' : n ≤ Fintype.card D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      obtain ⟨hc, hr⟩ := hRn n hn'
      rw [(GlobalTheory.T.sum_integralIndicator_cosets_kernel_subspaces k D D' ϖ hϖ (sn n) (Rn n) hr y).2 y₀ hy₀, hc]
    rw [Finset.sum_congr rfl (fun n hn => by rw [hR n hn])]
    have hC := GlobalTheory.T.card_subspaces_containing_range_qVandermonde 𝓀[k] (D → 𝓀[k]) (D' → 𝓀[k]) (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin t s.card
      (by simp only [Module.finrank_fintype_fun_eq_card]; exact ht)
      (by simp only [Module.finrank_fintype_fun_eq_card]; exact Finset.card_le_univ s)
    simp only [Module.finrank_fintype_fun_eq_card] at hC
    rw [hC]
    push_cast
    refine Finset.sum_congr rfl (fun n _ => ?_)
    split_ifs <;> simp [resCard]
  · rw [hL.1 hy]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    have hn' : n ≤ Fintype.card D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [(GlobalTheory.T.sum_integralIndicator_cosets_kernel_subspaces k D D' ϖ hϖ (sn n) (Rn n) (hRn n hn').2 y).1 hy, mul_zero]
end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

theorem _root_.GlobalTheory.T.fockSubstitution_identities : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b), (∀ (g : ι → Matrix (Fin a) (Fin a) ℂ) (h y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a), mvZ g h (subY hab y' F) = subY hab (fun τ => h τ * y' τ) (lft g F)) ∧ (∀ (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (h h' : ι → Matrix (Fin b) (Fin b) ℂ) (P : FP ι a b), mvZ g h (mvZ g' h' P) = mvZ (fun τ => g' τ * g τ) (fun τ => h τ * h' τ) P) ∧ (∀ P : FP ι a b, mvZ (fun _ => 1) (fun _ => 1) P = P) ∧ (∀ (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a), lft g (lft g' F) = lft (fun τ => g' τ * g τ) F) ∧ (∀ F : PY ι a, lft (fun _ => 1) F = F) ∧ (∀ (g y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a), evalAt y (lft g F) = evalAt (fun τ => g τ * y τ) F) ∧ (∀ F : PY ι a, (∀ y, IsInv y → evalAt y F = 0) → F = 0) ∧ ∀ (c t : ι → ℂ) (G : VCx ι a b → ℂ) (y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a), jetL c G (subY hab (fun τ => t τ • y' τ) F) = jetL (fun τ => c τ * t τ) G (subY hab y' F) := by
  first | exact @GlobalTheory.KJInf.substIdentities | exact GlobalTheory.KJInf.substIdentities | (intros; apply GlobalTheory.KJInf.substIdentities <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.eq_of_same_doubleCoset_completion_rowRepresentatives : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s), Set.InjOn (DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J ) {g : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k | ∃ b : L.β (j + 1), IsGL ι (L.h (j + 1) b P) g} := by
  first | exact @GlobalTheory.TwBridge.RepsInj.reps_injOn | exact GlobalTheory.TwBridge.RepsInj.reps_injOn | (intros; apply GlobalTheory.TwBridge.RepsInj.reps_injOn <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.LevProd

theorem prX_le_KO_of_prCat (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀)
    (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (hok : cst.Ok) (hat : AtTwist (R := R) sel mu cst σ₀ P ι s W)
    (j c : ℕ) (h : j + (c + 1) = s + 1) (γ : AutY X R j) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)
    (hg : IsGL ι γ g) (hle : prCat (Pr := Pr) cst.sharp j P.1 γ ≤ GLint X.E (R.N j) P.1) :
    prX (Cgrp ((W.T s R).lev j (c + 1) h).J g) ≤ KO k _ := by
  have hLev := GlobalTheory.TwBridge.Lev.levelAgree X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hat
  obtain ⟨e, he, hge⟩ := hg
  have hcc : cOf R j = c + 1 := by unfold cOf; have := hat.steps; omega
  have heR : ∀ i : Fin (c + 1), (e (Sum.inr i)).val = R.N j + i.val := fun i => he (Sum.inr i)
  have hgφ : g = GlobalTheory.VolBridge.locHom ι e γ := Units.ext hge
  have hreg : (W.T s R).Regular := Chain.ofTwist_regular _ _ _ _ _
  obtain ⟨hJo, -, -⟩ := hreg.2.2 j (c + 1) h
  set J := ((W.T s R).lev j (c + 1) h).J with hJdef
  set φ := GlobalTheory.VolBridge.locHom ι e with hφ
  have hcompl := hat.compl
  have hIsGL : ∀ x : AutY X R j, IsGL ι (γ⁻¹ * x * γ) (g⁻¹ * φ x * g) := by
    intro x
    refine ⟨e, he, ?_⟩
    rw [hgφ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hC : ∀ x : AutY X R j, x ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ↔ φ x ∈ Cgrp J g := by
    intro x
    rw [mem_Cgrp, ← GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange ι e hcc heR x, (hLev j (c + 1) h _ _ (hIsGL x)).1]
    simp [Loc.Cbe, Subgroup.mem_comap, MulAut.conj_apply]
  have hN1 := GlobalTheory.UnipRead.mem_N1_iff_local_hom ι e hcc heR
  have hdN := GlobalTheory.VolBridge.exists_N1_local_hom_mem_open ι hcompl.dense e hcc heR
  set e' := GlobalTheory.VolBridge.eX e hcc heR with he'
  set φ' := GlobalTheory.VolBridge.locHom ι e' with hφ'
  have hOo : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
    hJo.preimage (by fun_prop)
  have hOR : ∀ z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1,
      z ∈ Cgrp J g ↔ z ∈ {w | g⁻¹ * w * g ∈ J} := fun z hz => by
    simp [mem_Cgrp, hz]
  have hCR : Cgrp J g ≤ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := fun z hz => (mem_Cgrp.1 hz).1
  have hP : ∀ y, y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ ↔ φ' y ∈ prX (Cgrp J g) :=
    GlobalTheory.VolBridge.prX_iff_locHom ι e hcc heR hN1 hdN _ _ _ hOo hOR hCR hC
  have hG : ∀ y, y ∈ GLint X.E (R.N j) P.1 ↔ φ' y ∈ KO k _ := fun y =>
    GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO P.1 ι hcompl.int e' y
  have hpo : IsOpen (prX (Cgrp J g) : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)) :=
    GlobalTheory.OpenPr.isOpen_prX _ _ hOo (by simp [J.one_mem]) (fun z hz hzO => (hOR z hz).2 hzO)
  intro z hz
  have hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j) k |
      v⁻¹ * z ∈ ((prX (Cgrp J g) ⊓ KO k _ : Subgroup _) : Set _)} :=
    (hpo.inter GlobalTheory.SplitFlip.isOpen_KO).preimage (by fun_prop)
  obtain ⟨y, hy⟩ := GlobalTheory.denseGL_completion ι hcompl.dense e' z _ hV (by simp [one_mem, hz])
  have hy1 : (φ' y)⁻¹ * z ∈ prX (Cgrp J g) := hy.1
  have hy2 : (φ' y)⁻¹ * z ∈ KO k _ := hy.2
  have hyC : φ' y ∈ prX (Cgrp J g) := by
    have := mul_mem hz (inv_mem hy1); simpa using this
  have hyK : φ' y ∈ KO k _ := (hG y).1 (hle ((hP y).2 hyC))
  have := mul_mem hyK hy2; simpa using this

end GlobalTheory.LevProd
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.mem_integralGL_iff_isUnit_det_at_prime : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (κ l τ j : ℕ) (M : ℕ → ℕ → E), (∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = Matrix.of fun a b => ι (M (zPos a) (zPos b))) ↔ (∀ p p', p < κ + l + j * τ → p' < κ + l + j * τ → IntAt P (M p p')) ∧ IsUnit (redP P (Matrix.det (Matrix.of fun s s' : Fin (κ + l + j * τ) => M s.1 s'.1))) := by
  first | exact @GlobalTheory.SymBridge.mem_KO_iff_intAt_isUnit_det | exact GlobalTheory.SymBridge.mem_KO_iff_intAt_isUnit_det | (intros; apply GlobalTheory.SymBridge.mem_KO_iff_intAt_isUnit_det <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.symChainPattern_iff_place_conditions : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (κ l ρ τ j : ℕ) (M : ℕ → ℕ → E), (∀ p p', p < κ + l + j * τ → p' < κ + l + j * τ → IntAt P (M p p')) → ((∀ a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j, ¬ FreeIx ρ a b → valuation k (ι (M (zPos a) (zPos b)) - (1 : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k) a b) < 1) ↔ ((∀ p', p' < κ + l → redP P (M p' p') = 1 ∧ ∀ p, p < κ + l + j * τ → p ≠ p' → (κ + l ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → redP P (M p p') = 0) ∧ (∀ p p', κ + l ≤ p' → p' < κ + l + j * τ → p < κ + l + j * τ → (p' - (κ + l)) / τ < (p - (κ + l)) / τ → redP P (M p p') = 0))) := by
  first | exact @GlobalTheory.PatResidue.pattern_iff_places | exact GlobalTheory.PatResidue.pattern_iff_places | (intros; apply GlobalTheory.PatResidue.pattern_iff_places <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.symLevelTestFunctions_agree_rationalPoints : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → PhiAgree P q ι σ₀ ψ₀ χ S := by
  first | exact @GlobalTheory.SymBridge.PhiAgreeProof.phiAgree | exact GlobalTheory.SymBridge.PhiAgreeProof.phiAgree | (intros; apply GlobalTheory.SymBridge.PhiAgreeProof.phiAgree <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.unfoldingIntegral_eq_finiteSum_overNumberField : SumAgree := by
  first | exact @GlobalTheory.UnfoldSum.sumAgree | exact GlobalTheory.UnfoldSum.sumAgree | (intros; apply GlobalTheory.UnfoldSum.sumAgree <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem _root_.GlobalTheory.T.isOpen_mirabolicConj_inf_integralGL_unipotent : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A] {c : ℕ} (J : Subgroup (GL (A ⊕ Fin c) k)) (g : GL (A ⊕ Fin c) k), IsOpen (J : Set (GL (A ⊕ Fin c) k)) → IsCompact (J : Set (GL (A ⊕ Fin c) k)) → IsOpen ((((Cgrp J g).subgroupOf (N k A c 1)) ⊓ ((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1)) : Subgroup (N k A c 1)) : Set (N k A c 1)) ∧ IsCompact (((Cgrp J g).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) ∧ IsCompact (((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) := by
  first | exact @GlobalTheory.UnipLevelTopo.isOpen_inf_isCompact | exact GlobalTheory.UnipLevelTopo.isOpen_inf_isCompact | (intros; apply GlobalTheory.UnipLevelTopo.isOpen_inf_isCompact <;> assumption)
end
