module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineHomAdjointTwistMemCompletedHomLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl.CoupStab
open GlobalTheory.StepData GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_mem_box {n : Type} [Fintype n] {M : Matrix n n k} (hM : IntM M) {c : kˣ} {y : n → k}
    (hy : y ∈ box n c) : M *ᵥ y ∈ box n c := by
  rw [mem_box] at hy ⊢
  intro i
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le (hM i j) (hy j)

theorem toBlocks₁₁_mul {n : Type} [Fintype n] (M N : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  ext i j; simp [Matrix.mul_apply, Matrix.toBlocks₁₁, Fintype.sum_sum_type]

theorem toBlocks₁₁_one {n : Type} [Fintype n] [DecidableEq n] :
    (1 : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k).toBlocks₁₁ = 1 := by
  ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]

theorem withCol_mul {n n' : Type} [Fintype n] (κ : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) (x₀ : Matrix n n' k)
    (y : n → k) : κ * withCol x₀ y = withCol (κ.toBlocks₁₁ * x₀) (κ.toBlocks₁₁ *ᵥ y) := by
  ext (r | r) (c | c)
  · simp [withCol, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁]
  · simp [withCol, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.mulVec, dotProduct]
  · exact r.elim0
  · exact r.elim0

theorem box_eq_preimage {n : Type} (c : kˣ) :
    (box n c : Set (n → k)) = (fun y : n → k => ((c⁻¹ : kˣ) : k) • y) ⁻¹' Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
  ext y
  simp only [SetLike.mem_coe, mem_box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Pi.smul_apply,
    smul_eq_mul]
  refine forall_congr' fun i => ?_
  rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  have hc : 0 < valuation k (c : k) := by
    rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 c.ne_zero
  rw [inv_mul_le_iff₀ hc, mul_one]

theorem isOpen_box {n : Type} [Fintype n] (c : kˣ) : IsOpen (box n c : Set (n → k)) := by
  rw [box_eq_preimage]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => (valuation k).isOpen_integer).preimage (continuous_const_smul _)

theorem isCompact_box {n : Type} [Fintype n] (c : kˣ) : IsCompact (box n c : Set (n → k)) := by
  have hK : IsCompact (𝒪[k] : Set k) := isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[k]))
  have e : (box n c : Set (n → k)) = (fun y : n → k => (c : k) • y) '' Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
    rw [box_eq_preimage, Set.image_eq_preimage_of_inverse]
    · intro y; simp [smul_smul]
    · intro y; simp [smul_smul]
  rw [e]
  exact (isCompact_univ_pi fun _ => hK).image (continuous_const_smul _)

theorem finite_image_box {n : Type} [Fintype n] (c₁ c₂ : kˣ) :
    ((Submodule.Quotient.mk (p := box n c₂)) '' (box n c₁ : Set (n → k))).Finite := by
  obtain ⟨t, -, ht⟩ := (isCompact_box (n := n) c₁).elim_nhds_subcover
    (fun y => (fun z => z - y) ⁻¹' (box n c₂ : Set (n → k)))
    (fun y _ => ((isOpen_box c₂).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by show y - y ∈ box n c₂; rw [sub_self]; exact zero_mem _))
  refine (t.finite_toSet.image (Submodule.Quotient.mk (p := box n c₂))).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (ht hy)
  refine ⟨z, hz, (Submodule.Quotient.eq _).2 ?_⟩
  rw [← neg_sub]; exact neg_mem hyz

theorem om_one_ne {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (h : GL b k) (Φ : Matrix b a k → ℂ) (x : Matrix b a k) (hx : om μ 1 h Φ x ≠ 0) : Φ ((h⁻¹ : GL b k).val * x) ≠ 0 := by
  unfold om at hx
  have := right_ne_zero_of_mul hx
  simpa using this

theorem om_g_ne {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (Φ : Matrix b a k → ℂ) (x x' : Matrix b a k) (hx : om μ g 1 Φ x ≠ 0)
    (h : Φ (x * g.val) ≠ 0 → Φ (x' * g.val) ≠ 0) : om μ g 1 Φ x' ≠ 0 := by
  unfold om at *
  simp only [inv_one, Units.val_one, Matrix.one_mul] at *
  exact mul_ne_zero (left_ne_zero_of_mul hx) (h (right_ne_zero_of_mul hx))

end GlobalTheory.QPl.CoupStab

namespace GlobalTheory.QPl.CoupStab
open GlobalTheory.StepData GlobalTheory.SplitWeil

theorem psi_ne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
    (T : Chain k s X Z) (hL : T.Laws) {κ : GL (X (s + 1) ⊕ Fin 0) k} (hκ : κ ∈ (T.lev (s + 1) 0 rfl).J)
    (g : GL (X s ⊕ Fin (0 + 1)) k) (x₀ : Matrix (X (s + 1)) (X s) k) (y : X (s + 1) → k) (h : T.Psi g x₀ y ≠ 0) :
    T.Psi g (κ.val.toBlocks₁₁ * x₀) (κ.val.toBlocks₁₁ *ᵥ y) ≠ 0 := by
  have hPhi : ∀ x, T.Phi s 0 rfl x ≠ 0 → T.Phi s 0 rfl (κ.val * x) ≠ 0 := by
    intro x hx
    have e := congrFun ((hL.1 s 0 rfl).2 ⟨κ⁻¹, inv_mem hκ⟩) x
    have hr : om (T.mu (s + 1)) 1 (κ⁻¹ : GL (X (s + 1) ⊕ Fin 0) k) (T.Phi s 0 rfl) x ≠ 0 := by
      rw [e, Pi.smul_apply, smul_eq_mul]; exact mul_ne_zero (Units.ne_zero _) hx
    simpa using om_one_ne _ _ _ _ hr
  unfold Chain.Psi at *
  refine om_g_ne _ _ _ _ _ h fun h' => ?_
  rw [← withCol_mul, Matrix.mul_assoc]
  exact hPhi _ h'

theorem coupIdx_stab : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), (Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂)).Finite ∧ (∀ yb, SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb) ∧ (∀ yb yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb) ∧ (∀ yb yb' yb'', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb'' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb'') ∧ ∀ yb ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂), ∀ yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → yb' ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) := by
  intro D c v χ Q
  have hB : ∀ {g : GL (Q.X (Q.s + 1) ⊕ Fin 0) Q.k}, g ∈ (Q.T.lev (Q.s + 1) 0 rfl).J → IntM g.val.toBlocks₁₁ :=
    fun hg i j => intM_of_mem_KO (Q.le _ _ _ hg) (.inl i) (.inl j)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (finite_image_box Q.c₁ Q.c₂).subset (by rintro _ ⟨y, hy, rfl, -⟩; exact ⟨y, hy, rfl⟩)
  · intro yb
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ yb
    refine ⟨1, one_mem _, y, rfl, ?_⟩
    rw [Units.val_one, toBlocks₁₁_one, Matrix.one_mulVec]
  · rintro _ _ ⟨g, hg, y, rfl, rfl⟩
    refine ⟨g⁻¹, inv_mem hg, _, rfl, ?_⟩
    rw [Matrix.mulVec_mulVec, ← toBlocks₁₁_mul, Units.inv_mul, toBlocks₁₁_one, Matrix.one_mulVec]
  · rintro _ _ _ ⟨g, hg, y, rfl, h1⟩ ⟨g', hg', y', h2, h3⟩
    refine ⟨g' * g, mul_mem hg' hg, y, rfl, ?_⟩
    rw [← h3, Units.val_mul, toBlocks₁₁_mul, ← Matrix.mulVec_mulVec]
    refine (Submodule.Quotient.eq _).2 ?_
    rw [← Matrix.mulVec_sub]
    exact mulVec_mem_box (hB hg') ((Submodule.Quotient.eq _).1 (h1.trans h2.symm))
  · rintro _ ⟨y₁, -, rfl, g, hg, x₀, hΨ⟩ _ ⟨κ, hκ, y, hy, rfl⟩
    have hd : y - y₁ ∈ box _ Q.c₂ := (Submodule.Quotient.eq _).1 hy
    have hΨy : Q.T.Psi g x₀ y ≠ 0 := by
      rw [show y = y₁ + (y - y₁) by abel, (Q.adapt g hg x₀ y₁).2 _ hd]; exact hΨ
    exact ⟨_, mulVec_mem_box (hB hκ) ((Q.adapt g hg x₀ y).1 hΨy), rfl, g, hg, _,
      psi_ne Q.T Q.laws hκ g x₀ y hΨy⟩

end GlobalTheory.QPl.CoupStab
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw



theorem idV_incA_mul {D : D7} (c : D.host.E) (𝔞 : FI D) (v : Pl D) {y : AE D} (hy : y ∈ idV 𝔞 v) :
    incA D c * y ∈ idV (FractionalIdeal.spanSingleton _ c * 𝔞) v := by
  have hle : idV 𝔞 v ≤ (idV (FractionalIdeal.spanSingleton _ c * 𝔞) v).comap (AddMonoidHom.mulLeft (incA D c)) := by
    rw [idV, AddSubgroup.closure_le]
    rintro _ ⟨α, h₁, h₂, a, ha, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, h₁, h₂, c * a,
      FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ c) ha, ?_⟩
    show incA D c * _ = _
    simp [incA, inclR, Algebra.TensorProduct.tmul_mul_tmul]
  exact hle hy

theorem idV_le_idAt {D : D7} (𝔞 : FI D) (v : Pl D) : idV 𝔞 v ≤ (idAt D (· = v)).toAddSubgroup := by
  rw [idV, AddSubgroup.closure_le]
  rintro _ ⟨α, h₁, h₂, a, ha, rfl⟩
  simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, idAt, Submodule.mem_inf, Submodule.mem_iInf,
    RingHom.mem_ker]
  refine ⟨?_, fun w => ?_⟩
  · change (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id _ _)) ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a) = 0
    rw [Algebra.TensorProduct.map_tmul]
    change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E a) = 0
    exact TensorProduct.zero_tmul _ _
  · have e : FinPl.compAt D w.1 ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a) = (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] a := rfl
    rw [e, h₂ w.1 w.2]
    exact TensorProduct.zero_tmul _ _

theorem idV_spanSingleton_mul_iff : ∀ (D : D7) (v : Pl D) (𝔞 : FI D) (x : D.host.E), x ≠ 0 → ∀ s,
    s ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔞) v ↔ incA D x⁻¹ * s ∈ idV 𝔞 v ∧ s ∈ idAt D (· = v) := by
  intro D v 𝔞 x hx s
  constructor
  · intro hs
    refine ⟨?_, idV_le_idAt _ v hs⟩
    have h := idV_incA_mul x⁻¹ _ v hs
    rwa [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hx,
      FractionalIdeal.spanSingleton_one, one_mul] at h
  · rintro ⟨h, -⟩
    have h' := idV_incA_mul x 𝔞 v h
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hx, map_one, one_mul] at h'

end GlobalTheory.SeeSaw
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.IdVMul

variable {D : D7}

theorem intAE_mul_mem' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D)
    (hy : y ∈ intAE D) : x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, w, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w' => ?_, u * w, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w') (hb w')
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

variable {v : Pl D}

theorem intAt_mul {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [(finPart D).map_mul]; exact intAE_mul_mem' ha.2 hb.2⟩

theorem intAt_zero : (0 : AE D) ∈ intAt D (· = v) :=
  ⟨zero_mem _, by rw [(finPart D).map_zero]; exact zero_mem _⟩

theorem intAt_add {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a + b ∈ intAt D (· = v) :=
  ⟨add_mem ha.1 hb.1, by rw [(finPart D).map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg {a : AE D} (ha : a ∈ intAt D (· = v)) : -a ∈ intAt D (· = v) :=
  ⟨neg_mem ha.1, by rw [(finPart D).map_neg]; exact neg_mem ha.2⟩

theorem pairA_zero_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  show ((0 : Ainf D.host.F) * 0, α * β) = ((0 : Ainf D.host.F), α * β)
  rw [zero_mul]

theorem evalV_single_self (v : Pl D) : evalV D.host.F v (singleV D.host.F v 1) = 1 := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : Pl D => w.adicCompletionIntegers D.host.F) v 1

theorem evalV_single_ne {v w : Pl D} (hw : w ≠ v) : evalV D.host.F w (singleV D.host.F v 1) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : Pl D => w.adicCompletionIntegers D.host.F) 1 hw

theorem single_int (v : Pl D) : singleV D.host.F v 1 ∈ intAf D.host.F := fun w => by
  by_cases hw : w = v
  · subst hw; rw [evalV_single_self]; exact one_mem _
  · rw [evalV_single_ne hw]; exact zero_mem _

theorem mul_single {α : Af D.host.F} (hα : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    α * singleV D.host.F v 1 = α := by
  apply RestrictedProduct.ext
  intro w
  change evalV D.host.F w (α * singleV D.host.F v 1) = evalV D.host.F w α
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [evalV_single_self, mul_one]
  · rw [hα w hw, zero_mul]

theorem gen_mem {𝔞 : FI D} {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (hαv : ∀ w, w ≠ v → evalV D.host.F w α = 0)
    {a : D.host.E} (ha : a ∈ 𝔞) : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] a ∈ idV 𝔞 v :=
  AddSubgroup.subset_closure ⟨α, hα, hαv, a, ha, rfl⟩

theorem tmul_mem_idAt {α : Af D.host.F} (hαv : ∀ w, w ≠ v → evalV D.host.F w α = 0) (x : D.host.E) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x ∈ idAt D (· = v) := by
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [hαv _ w.2, TensorProduct.zero_tmul]

theorem tmul_one_mem_intAt {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (hαv : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨tmul_mem_idAt hαv 1, ?_⟩
  change α ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAE D
  exact AddSubgroup.subset_closure ⟨α, hα, 1, by simp⟩

theorem tmul_mul_tmul' (α β : Af D.host.F) (a b : D.host.E) :
    ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) * ((pairA D.host.F 0 β) ⊗ₜ[D.host.F] b) =
      (pairA D.host.F 0 (α * β)) ⊗ₜ[D.host.F] (a * b) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_zero_mul]

theorem incA_mul_tmul (x : D.host.E) (α : AF D.host.F) (b : D.host.E) :
    incA D x * (α ⊗ₜ[D.host.F] b : AE D) = α ⊗ₜ[D.host.F] (x * b) := by
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) * (α ⊗ₜ[D.host.F] b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem mul_mem_idV {𝔞 𝔟 : FI D} {a b : AE D} (ha : a ∈ idV 𝔞 v) (hb : b ∈ idV 𝔟 v) : a * b ∈ idV (𝔞 * 𝔟) v := by
  induction ha using AddSubgroup.closure_induction with
  | mem a' ha' =>
    obtain ⟨α, hα, hαv, a, ha, rfl⟩ := ha'
    induction hb using AddSubgroup.closure_induction with
    | mem b' hb' =>
      obtain ⟨β, hβ, hβv, b, hb, rfl⟩ := hb'
      rw [tmul_mul_tmul']
      refine gen_mem (fun w => ?_) (fun w hw => ?_) (FractionalIdeal.mul_mem_mul ha hb)
      · rw [map_mul]; exact mul_mem (hα w) (hβ w)
      · rw [map_mul, hαv w hw, zero_mul]
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg x _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg x _ h => rw [neg_mul]; exact neg_mem h

theorem incA_mul_mem {𝔞 𝔟 : FI D} {x : D.host.E} (hx0 : x ≠ 0)
    (hx : ∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) {t : AE D} (ht : t ∈ idV 𝔟 v) :
    incA D x * t ∈ idV (𝔞 * 𝔟) v := by
  induction ht using AddSubgroup.closure_induction with
  | mem t' ht' =>
    obtain ⟨β, hβ, hβv, b, hb, rfl⟩ := ht'
    have e : incA D x * ((pairA D.host.F 0 β) ⊗ₜ[D.host.F] b) =
        ((pairA D.host.F 0 β) ⊗ₜ[D.host.F] x : AE D) * ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b) := by
      rw [incA_mul_tmul, tmul_mul_tmul', mul_single hβv]
    rw [e]
    refine mul_mem_idV ((hx _).2 ⟨?_, tmul_mem_idAt hβv x⟩)
      (gen_mem (single_int v) (fun w hw => evalV_single_ne hw) hb)
    rw [incA_mul_tmul, inv_mul_cancel₀ hx0]
    exact tmul_one_mem_intAt hβ hβv
  | zero => rw [mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [mul_neg]; exact neg_mem ha

theorem idV_mul_gen : ∀ (D : D7) (v : Pl D) (𝔞 𝔟 : FI D) (x y : D.host.E), x ≠ 0 → y ≠ 0 → (∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) → (∀ s, s ∈ idV 𝔟 v ↔ incA D y⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) → ∀ s, s ∈ idV (𝔞 * 𝔟) v ↔ incA D (x * y)⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v) := by
  intro D v 𝔞 𝔟 x y hx0 hy0 hx hy
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
  intro s
  constructor
  · intro hs
    refine AddSubgroup.closure_induction (p := fun s _ => incA D (x * y)⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v))
      ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨α, hα, hαv, c, hc, rfl⟩
      refine FractionalIdeal.mul_induction_on (C := fun c => incA D (x * y)⁻¹ * ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] c) ∈
        intAt D (· = v) ∧ (pairA D.host.F 0 α) ⊗ₜ[D.host.F] c ∈ idAt D (· = v)) hc ?_ ?_
      · intro a ha b hb
        have hA := (hx _).1 (gen_mem hα hαv ha)
        have hB := (hy _).1 (gen_mem (single_int v) (fun w hw => evalV_single_ne hw) hb)
        have e : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * b) =
            ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) * ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b) := by
          rw [tmul_mul_tmul', mul_single hαv]
        rw [e]
        refine ⟨?_, Ideal.mul_mem_right _ _ hA.2⟩
        have e2 : incA D (x * y)⁻¹ * (((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) *
            ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b)) =
            (incA D x⁻¹ * ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a)) *
              (incA D y⁻¹ * ((pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] b)) := by
          rw [mul_inv, (incA D).map_mul]; ring
        rw [e2]
        exact intAt_mul hA.1 hB.1
      · intro c d hc hd
        rw [TensorProduct.tmul_add, mul_add]
        exact ⟨intAt_add hc.1 hd.1, add_mem hc.2 hd.2⟩
    · rw [mul_zero]; exact ⟨intAt_zero, zero_mem _⟩
    · intro a b _ _ ha hb
      rw [mul_add]; exact ⟨intAt_add ha.1 hb.1, add_mem ha.2 hb.2⟩
    · intro a _ ha
      rw [mul_neg]; exact ⟨intAt_neg ha.1, neg_mem ha.2⟩
  · rintro ⟨ho, hs⟩
    have hso : s = incA D x * (incA D y * (incA D (x * y)⁻¹ * s)) := by
      rw [← mul_assoc, ← mul_assoc, ← (incA D).map_mul, ← (incA D).map_mul, mul_inv_cancel₀ hxy0, (incA D).map_one,
        one_mul]
    have ht : incA D y * (incA D (x * y)⁻¹ * s) ∈ idV 𝔟 v := by
      refine (hy _).2 ⟨?_, Ideal.mul_mem_left _ _ ho.1⟩
      rw [← mul_assoc, ← (incA D).map_mul, inv_mul_cancel₀ hy0, (incA D).map_one, one_mul]
      exact ho
    rw [hso]
    exact incA_mul_mem hx0 hx ht

end GlobalTheory.SeeSaw.IdVMul

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem natInv_mem_adicIntegers (F : Type) [Field F] [NumberField F] (T : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (h : ((T : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    algebraMap F (v.adicCompletion F) ((T : F)⁻¹) ∈ v.adicCompletionIntegers F := by
  have h1 : v.valuation F (T : F) = 1 := by
    have : (T : F) = algebraMap (𝓞 F) F (T : 𝓞 F) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) ((T : F)⁻¹)) = v.valuation F ((T : F)⁻¹) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [h2, map_inv₀, h1, inv_one]

theorem natInv_smul_mem_intAf (F : Type) [Field F] [NumberField F] (T : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (h : ((T : ℕ) : 𝓞 F) ∉ v.asIdeal) (α : Af F) (h1 : α ∈ intAf F) (h2 : ∀ w, w ≠ v → evalV F w α = 0) :
    ((T : F)⁻¹ : F) • α ∈ intAf F ∧ ∀ w, w ≠ v → evalV F w (((T : F)⁻¹ : F) • α) = 0 := by
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · change evalV F w _ ∈ w.adicCompletionIntegers F
    rw [map_smul]
    by_cases hw : w = v
    · subst hw
      rw [Algebra.smul_def]
      exact mul_mem (natInv_mem_adicIntegers F T w h) (h1 w)
    · rw [h2 w hw, smul_zero]; exact zero_mem _
  · rw [map_smul, h2 w hw, smul_zero]

theorem smul_pairA_zero (F : Type) [Field F] [NumberField F] (t : F) (α : Af F) :
    t • pairA F 0 α = pairA F 0 (t • α) := by
  rw [Algebra.smul_def, Algebra.smul_def]
  exact Prod.ext (mul_zero _) rfl

theorem pairA_zero_tmul_smul (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (t : F) (α : Af F) (c : E) :
    pairA F 0 α ⊗ₜ[F] (t • c) = pairA F 0 (t • α) ⊗ₜ[F] c := by
  rw [← smul_pairA_zero, TensorProduct.smul_tmul]

theorem idV_natInv_mul_le (D : D7) (𝔠 : FI D) (T : ℕ) (v : Pl D) (h : ((T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) :
    idV (FractionalIdeal.spanSingleton _ ((T : D.host.E)⁻¹) * 𝔠) v ≤ idV 𝔠 v := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, h1, h2, a, ha, rfl⟩
  obtain ⟨c, hc, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 ha
  have e : ((T : D.host.E)⁻¹) * c = ((T : D.host.F)⁻¹ : D.host.F) • c := by
    rw [Algebra.smul_def, map_inv₀, map_natCast]
  obtain ⟨g1, g2⟩ := natInv_smul_mem_intAf D.host.F T v h α h1 h2
  refine AddSubgroup.subset_closure ⟨((T : D.host.F)⁻¹ : D.host.F) • α, g1, g2, c, hc, ?_⟩
  rw [e]
  exact pairA_zero_tmul_smul D.host.F D.host.E _ α c

end GlobalTheory.SeeSaw
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lineHomAdjointTwist_mem_completedHomLattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S L L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (MS : GlobalTheory.FinPl.Lat S) (LL : GlobalTheory.FinPl.Lat L) (LZ : GlobalTheory.FinPl.Lat L''), q.UnitAA → IsSelfDualC S MS → IsSelfDualC L LL → IsSelfDualC L'' LZ → (∀ y ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v), (rat τ : Mx D L.rank L''.rank) *ᵥ y ∈ GlobalTheory.FinPl.latV L LL (· = q.v)) → ∀ w ∈ latO S L'' (MS : Set _) (LZ : Set _) (· = q.v), GlobalTheory.FinPl.kap τ S w ∈ latO L S (LL : Set _) (MS : Set _) (· = q.v) := by
  first | exact @GlobalTheory.KapLat2.kap_mem_latO | exact GlobalTheory.KapLat2.kap_mem_latO | (intros; apply GlobalTheory.KapLat2.kap_mem_latO <;> assumption)
end
