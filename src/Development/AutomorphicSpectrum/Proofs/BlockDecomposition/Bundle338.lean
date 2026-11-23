module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle132
import GroundTheory.AutomorphicForms.GLnLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

theorem intC_one_of_bump : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (s : kˣ)
    (hψ1 : ∀ y ∈ GlobalTheory.SplitWeil.cball s, ψ y = 1) (w : τ.V ⊗[ℂ] σ.V) (F : XS τ σ)
    (h1 : ∀ d : Fin (t + 1) → k, (∀ j, d j ∈ GlobalTheory.SplitWeil.cball s) → evX F (dEmb k i t d) = w)
    (h0 : ∀ d : Fin (t + 1) → k, (¬ ∀ j, d j ∈ GlobalTheory.SplitWeil.cball s) → evX F (dEmb k i t d) = 0),
  ∃ c : ℂ, c ≠ 0 ∧ intC ψ F 1 = c • w := by
  intro k _ _ _ _ i t ψ τ σ s hψ1 w F h1 h0
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  letI : MeasurableSpace (Fin (t + 1) → k) := borel _
  haveI : BorelSpace (Fin (t + 1) → k) := ⟨rfl⟩
  let A : Set (Fin (t + 1) → k) := Set.pi Set.univ fun _ => GlobalTheory.SplitWeil.cball s
  have hAc : IsCompact A := isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball s
  have hAo : IsOpen A := isOpen_set_pi Set.finite_univ fun _ _ => GlobalTheory.SplitWeil.isOpen_cball s
  have hne : A.Nonempty := ⟨0, fun _ _ => by simp [GlobalTheory.SplitWeil.cball]⟩
  have hmem : ∀ d, d ∈ A ↔ ∀ j, d j ∈ GlobalTheory.SplitWeil.cball s :=
    fun d => ⟨fun h j => h j (Set.mem_univ j), fun h j _ => h j⟩
  haveI : (muD k (t + 1)).IsAddHaarMeasure := by
    unfold muD
    infer_instance
  have hpos : 0 < muD k (t + 1) A := hAo.measure_pos _ hne
  have htop : muD k (t + 1) A < ⊤ := hAc.measure_lt_top
  refine ⟨(((muD k (t + 1) A).toReal : ℝ) : ℂ), ?_, ?_⟩
  · exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos hpos.ne' htop.ne).ne'
  · have e : (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) •
        evX F (dEmb k i t d * (1 : Mir k ((i + 1) + t + 1)))) = A.indicator fun _ => w := by
      funext d
      have e1 : dEmb k i t d * (1 : Mir k ((i + 1) + t + 1)) = dEmb k i t d := mul_one _
      rw [e1]
      by_cases hd : d ∈ A
      · rw [Set.indicator_of_mem hd, h1 d ((hmem d).1 hd), hψ1 _ ((hmem d).1 hd _)]
        simp
      · rw [Set.indicator_of_notMem hd, h0 d (fun h => hd ((hmem d).2 h)), smul_zero]
    show @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) _ = _
    rw [e]
    exact GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_indicator _ A w

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem colMat_mem_ball {s : kˣ} {n : ℕ} {v : Fin n → k} (hv : ∀ a, v a ∈ GlobalTheory.SplitWeil.cball s)
    (a b : Fin (n + 1)) : colMat k n v a b ∈ GlobalTheory.SplitWeil.cball s := by
  have h0 : (0 : k) ∈ GlobalTheory.SplitWeil.cball s := by simp [GlobalTheory.SplitWeil.cball]
  by_cases hb : b = Fin.last n
  · subst hb
    induction a using Fin.lastCases with
    | last => simpa [GlobalTheory.BZMir.colMat] using h0
    | cast a => simpa [GlobalTheory.BZMir.colMat] using hv a
  · simpa [GlobalTheory.BZMir.colMat, hb] using h0

theorem unip_mem_congGL {s : kˣ} (hs : ValuativeRel.valuation k (s : k) ≤ 1) {n : ℕ} {v : Fin n → k}
    (hv : ∀ a, v a ∈ GlobalTheory.SplitWeil.cball s) :
    unip k n (Multiplicative.ofAdd v) ∈ congGL k s hs (n + 1) := by
  have h1 : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s (1 + GlobalTheory.BZMir.colMat k n v) := by
    intro a b
    rw [Matrix.add_apply, add_sub_cancel_left]
    exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.colMat_mem_ball hv a b
  have h2 : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s (1 - GlobalTheory.BZMir.colMat k n v) := by
    intro a b
    rw [Matrix.sub_apply, sub_sub_cancel_left]
    exact GlobalTheory.SplitWeil.neg_mem_cball (GlobalTheory.CompanionTheory.BZPhiPG.Onto.colMat_mem_ball hv a b)
  exact And.intro h1 h2

theorem colMat_mul_apply {n : ℕ} (v : Fin n → k) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (a : Fin n)
    (c : Fin (n + 1)) : (colMat k n v * A) (Fin.castSucc a) c = v a * A (Fin.last n) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
  · simp [GlobalTheory.BZMir.colMat]
  · intro j _ hj
    simp [GlobalTheory.BZMir.colMat, hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ball_of_unip_eq_mul {s : kˣ} (hs : ValuativeRel.valuation k (s : k) ≤ 1) {n : ℕ} {v : Fin n → k}
    {h κ : GL (Fin (n + 1)) k} (heq : unip k n (Multiplicative.ofAdd v) = h * κ)
    (hκ : κ ∈ congGL k s hs (n + 1)) (a : Fin n)
    (h0 : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.last n) = 0)
    (h1 : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1) :
    v a ∈ GlobalTheory.SplitWeil.cball s := by
  have hinv : κ⁻¹ = (GlobalTheory.BZMir.unip k n (Multiplicative.ofAdd v))⁻¹ * h := by
    rw [heq, _root_.mul_inv_rev, inv_mul_cancel_right]
  have hmat : ((κ⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      (1 - GlobalTheory.BZMir.colMat k n v) * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    rw [hinv, Units.val_mul]
    rfl
  have hc := (show _ ∧ GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s ((κ⁻¹ : GL (Fin (n + 1)) k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) k) from hκ).2 (Fin.castSucc a) (Fin.last n)
  rw [hmat, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, GlobalTheory.CompanionTheory.BZPhiPG.Onto.colMat_mul_apply, h0, h1,
    Matrix.one_apply_ne (Fin.castSucc_ne_last a)] at hc
  simp only [zero_sub, mul_one, sub_zero] at hc
  have hneg := GlobalTheory.SplitWeil.neg_mem_cball hc
  rwa [neg_neg] at hneg

theorem Mir_last_last {n : ℕ} (g : Mir k n) :
    ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  have hrow := (GlobalTheory.BZMir.mem_Mir_iff k (g : GL (Fin (n + 1)) k)).1 g.2
  have hentry := congrFun hrow (Fin.last n)
  simpa [GlobalTheory.BZMir.eLast] using hentry

theorem ePG_true_natAdd (i t : ℕ) (j : Fin (t + 1)) :
    ePG (i + 1) (t + 1) ⟨true, j⟩ = Fin.castSucc (Fin.natAdd (i + 1) j) := by
  first
    | rfl
    | exact Fin.ext rfl
    | (ext; simp [GlobalTheory.BZMir.Leib.ePG])

theorem HPG_entry_zero {i t : ℕ} (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1)) (j : Fin (t + 1)) :
    ((h : GL (Fin ((i + 1) + (t + 1) + 1)) k) : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) j)) (Fin.last ((i + 1) + (t + 1))) = 0 := by
  have hh' : (h : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈
      GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1)) := hh
  have hz := GlobalTheory.SmGL.mem_parab_iff.1 hh' true false j (Fin.last (i + 1)) (by decide)
  rwa [GlobalTheory.CompanionTheory.BZPhiPG.Onto.ePG_true_natAdd, GlobalTheory.BZMir.Leib.ePG_false_last] at hz

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

theorem GlobalTheory.CompanionTheory.BZPhiPG.Onto.dEmb_mem_congM_and_ball : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (d : Fin (t + 1) → k),
  ((∀ j, d j ∈ GlobalTheory.SplitWeil.cball s) → dEmb k i t d ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t + 1)) ∧
  ∀ (h : Mir k ((i + 1) + t + 1)), h ∈ HPG k (i + 1) (t + 1) → ∀ κ ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t + 1),
    dEmb k i t d = h * κ → ∀ j, d j ∈ GlobalTheory.SplitWeil.cball s := by
  intro k _ _ _ _ i t s hs d
  refine ⟨fun hd => ?_, fun h hh κ hκ he j => ?_⟩
  · have hv : ∀ a, Fin.append (0 : Fin (i + 1) → k) d a ∈ GlobalTheory.SplitWeil.cball s := by
      intro a
      refine Fin.addCases (fun a => ?_) (fun b => ?_) a
      · rw [Fin.append_left]
        simp [GlobalTheory.SplitWeil.cball]
      · rw [Fin.append_right]
        exact hd b
    first
      | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.unip_mem_congGL hs hv
      | exact Subgroup.mem_comap.2 (GlobalTheory.CompanionTheory.BZPhiPG.Onto.unip_mem_congGL hs hv)
  · have he' : GlobalTheory.BZMir.unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append (0 : Fin (i + 1) → k) d)) =
        (h : GL (Fin ((i + 1) + (t + 1) + 1)) k) * (κ : GL (Fin ((i + 1) + (t + 1) + 1)) k) :=
      congrArg Subtype.val he
    have hmem := GlobalTheory.CompanionTheory.BZPhiPG.Onto.ball_of_unip_eq_mul hs he' hκ (Fin.natAdd (i + 1) j)
      (GlobalTheory.CompanionTheory.BZPhiPG.Onto.HPG_entry_zero h hh j)
      (GlobalTheory.CompanionTheory.BZPhiPG.Onto.Mir_last_last h)
    rwa [Fin.append_right] at hmem

end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nearOne_glEmbMat_iff (s : kˣ) (m : ℕ) (A : Matrix (Fin m) (Fin m) k) :
    NearOne s (glEmbMat k m A) ↔ NearOne s A := by
  have e1 : ∀ a b : Fin m, glEmbMat k m A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
    intro a b
    simp [glEmbMat]
  have e2 : ∀ a b : Fin m, (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.castSucc a) (Fin.castSucc b) =
      (1 : Matrix (Fin m) (Fin m) k) a b := by
    intro a b
    simp [Matrix.one_apply, Fin.castSucc_inj]
  have z : (0 : k) ∈ (ballSub s : Set k) := (ballSub s).zero_mem
  constructor
  · intro h a b
    have h1 := h (Fin.castSucc a) (Fin.castSucc b)
    rwa [e1, e2] at h1
  · intro h a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last =>
        have e : glEmbMat k m A (Fin.last m) (Fin.last m) - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) (Fin.last m) = 0 := by
          simp [glEmbMat]
        rw [e]
        exact z
      | cast j =>
        have e : glEmbMat k m A (Fin.last m) (Fin.castSucc j) - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) (Fin.castSucc j) = 0 := by
          rw [Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne', sub_zero]
          simp [glEmbMat]
        rw [e]
        exact z
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        have e : glEmbMat k m A (Fin.castSucc i) (Fin.last m) - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.castSucc i) (Fin.last m) = 0 := by
          rw [Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne, sub_zero]
          simp [glEmbMat]
        rw [e]
        exact z
      | cast j =>
        rw [e1, e2]
        exact h i j

theorem sEmb_mem_congM_iff (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (x : Mir k n) :
    sEmb k n x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs (n + 1) ↔ x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n := by
  have e1 : (((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) =
      glEmbMat k (n + 1) ((x : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := rfl
  have e2 : ((((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k)⁻¹ : GL (Fin (n + 1 + 1)) k) :
        Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) =
      glEmbMat k (n + 1) (((x : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    have : ((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k)⁻¹ = ((sEmb k n x⁻¹ : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) := by
      rw [map_inv]; rfl
    rw [this]
    rfl
  show (NearOne s (((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) ∧
        NearOne s ((((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k)⁻¹ : GL (Fin (n + 1 + 1)) k) :
          Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k)) ↔
      (NearOne s ((x : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∧
        NearOne s (((x : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
  rw [e1, e2, nearOne_glEmbMat_iff, nearOne_glEmbMat_iff]

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Grp

section Alg

variable {k : Type} [Field k]

theorem mirProj_eq_one_of_mem {n : ℕ} (u : Mir k n) (hu : u ∈ MirUin k n) : mirabolicProjection k n u = 1 := by
  obtain ⟨v, hv⟩ := (Subgroup.mem_subgroupOf.1 hu : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  apply Units.ext
  ext a b
  show ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = _
  rw [← hv]
  simp [unip, colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one' {n : ℕ} (u : Mir k n) (hu : mirabolicProjection k n u = 1) : u ∈ MirUin k n := by
  have hb : ∀ a b : Fin n, ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = if a = b then 1 else 0 := by
    intro a b
    have := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) a b) hu
    exact (this : ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = _).trans (by simp [Matrix.one_apply])
  have hl := (mem_Mir_iff k (u : GL (Fin (n + 1)) k)).1 u.2
  refine Subgroup.mem_subgroupOf.2 ⟨Multiplicative.ofAdd fun a => ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.last n), ?_⟩
  apply Units.ext
  ext a b
  have hlb := congrFun hl b
  induction a using Fin.lastCases with
  | last =>
    rw [hlb]
    induction b using Fin.lastCases <;> simp [unip, colMat, Matrix.one_apply, eLast, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  | cast a =>
    induction b using Fin.lastCases with
    | last => simp [unip, colMat, Matrix.one_apply, Fin.castSucc_ne_last]
    | cast b =>
      rw [hb]
      simp [unip, colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mirUin_normal (n : ℕ) : (MirUin k n).Normal := by
  refine ⟨fun u hu g => mem_of_mirProj_eq_one' _ ?_⟩
  rw [map_mul, map_mul, mirProj_eq_one_of_mem u hu, mul_one, map_inv, mul_inv_cancel]

theorem mirUin_comm {n : ℕ} {a b : Mir k n} (ha : a ∈ MirUin k n) (hb : b ∈ MirUin k n) : a * b = b * a := by
  obtain ⟨v, hv⟩ := (Subgroup.mem_subgroupOf.1 ha : ((a : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 hb : ((b : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  apply Subtype.ext
  show (a : GL (Fin (n + 1)) k) * (b : GL (Fin (n + 1)) k) = (b : GL (Fin (n + 1)) k) * (a : GL (Fin (n + 1)) k)
  rw [← hv, ← hw, ← map_mul, mul_comm, map_mul]

def prodSub {n : ℕ} (L₁ L₂ : Subgroup (Mir k n)) (h₁ : L₁ ≤ MirUin k n) (h₂ : L₂ ≤ MirUin k n) : Subgroup (Mir k n) where
  carrier := (L₁ : Set (Mir k n)) * (L₂ : Set (Mir k n))
  one_mem' := ⟨1, L₁.one_mem, 1, L₂.one_mem, one_mul 1⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    refine ⟨a * c, L₁.mul_mem ha hc, b * d, L₂.mul_mem hb hd, ?_⟩
    show a * c * (b * d) = a * b * (c * d)
    rw [mul_assoc a c, ← mul_assoc c b, mirUin_comm (h₁ hc) (h₂ hb)]
    simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, L₁.inv_mem ha, b⁻¹, L₂.inv_mem hb, ?_⟩
    show a⁻¹ * b⁻¹ = (a * b)⁻¹
    rw [_root_.mul_inv_rev]
    exact mirUin_comm (MirUin k n |>.inv_mem (h₁ ha)) (MirUin k n |>.inv_mem (h₂ hb))

theorem hpg_entry {i t : ℕ} (g : Mir k ((i + 1) + t + 1)) (hg : g ∈ HPG k (i + 1) (t + 1))
    (l : Fin ((i + 1) + t + 2)) (hl : i < l.val) (hl2 : l.val ≠ (i + 1) + t + 1) (c : Fin (i + 1)) :
    ((g : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) l
      (Fin.castLE (by omega) c) = 0 := by
  have hp : (g : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ GlobalTheory.SmGL.parab k (ePG (i + 1) (t + 1)) := hg
  have hlt := l.isLt
  have h0 := mem_parab_iff.1 hp true false (⟨l.val - (i + 1), by omega⟩ : Fin (t + 1)) (Fin.castSucc c : Fin (i + 1 + 1)) (by decide)
  have e1 : ePG (i + 1) (t + 1) ⟨true, (⟨l.val - (i + 1), by omega⟩ : Fin (t + 1))⟩ = l := by
    apply Fin.ext
    simp [ePG, two]
    omega
  have e2 : ePG (i + 1) (t + 1) ⟨false, (Fin.castSucc c : Fin (i + 1 + 1))⟩ = Fin.castLE (by omega) c := by
    apply Fin.ext
    simp [ePG, two]
  rw [e1, e2] at h0
  exact h0

theorem Cl_left {i t : ℕ} (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1)) (x : Mir k ((i + 1) + t + 1))
    (hx : x ∈ Cl k i t) : h * x ∈ Cl k i t := by
  intro c
  rw [_root_.mul_inv_rev]
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h1 : l.val ≤ i
  · have := hx ⟨l.val, by omega⟩
    have e : Fin.castLE (by omega) (⟨l.val, by omega⟩ : Fin (i + 1)) = l := Fin.ext rfl
    rw [e] at this
    rw [this, zero_mul]
  · by_cases h2 : l.val = (i + 1) + t + 1
    · have e : l = Fin.last _ := Fin.ext h2
      have hm := (mem_Mir_iff k ((h⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k)).1 (h⁻¹).2
      have hc := congrFun hm (Fin.castLE (by omega) c)
      rw [e, hc]
      have : Fin.castLE (by omega) c ≠ Fin.last ((i + 1) + t + 1) := by
        intro e'
        have := congrArg Fin.val e'
        simp at this
        omega
      simp [eLast, Pi.single_apply, this]
    · rw [hpg_entry _ ((HPG k (i + 1) (t + 1)).inv_mem hh) l (by omega) h2 c, mul_zero]

theorem Cl_right {i t : ℕ} (x : Mir k ((i + 1) + t + 1)) (hx : x ∈ Cl k i t) (u : Mir k ((i + 1) + t + 1))
    (hu : u ∈ MirUin k ((i + 1) + t + 1)) : x * u ∈ Cl k i t := by
  intro c
  obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 ((MirUin k ((i + 1) + t + 1)).inv_mem hu) :
    ((u⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) ∈ MirU k ((i + 1) + t + 1))
  rw [_root_.mul_inv_rev]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [← hw]
  have hv : ((unip k ((i + 1) + t + 1) w : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) = 1 + colMat k _ w.toAdd := rfl
  rw [hv, add_mul, one_mul, Matrix.add_apply, hx c, zero_add, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l = Fin.last _
  · have hm := (mem_Mir_iff k ((x⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k)).1 (x⁻¹).2
    have hc := congrFun hm (Fin.castLE (by omega) c)
    rw [hl, hc]
    have : Fin.castLE (by omega) c ≠ Fin.last ((i + 1) + t + 1) := by
      intro e'
      have := congrArg Fin.val e'
      simp at this
      omega
    simp [eLast, Pi.single_apply, this]
  · simp [colMat, hl]

end Alg

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mirChar_ker_open (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) :
    IsOpen ((mirChar k ψ n).ker : Set (MirUin k (n + 1))) := by
  have he : ((mirChar k ψ n).ker : Set (MirUin k (n + 1))) =
      (fun u : MirUin k (n + 1) => GlobalTheory.CompanionTheory.BZFun.lastCol k u (Fin.last n)) ⁻¹' {x : k | ψ x = 1} := by
    ext u
    obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 u.2 : ((u : Mir k (n + 1)) : GL (Fin (n + 2)) k) ∈ MirU k (n + 1))
    have hl : GlobalTheory.CompanionTheory.BZFun.lastCol k u (Fin.last n) = w.toAdd (Fin.last n) := by
      simp only [GlobalTheory.CompanionTheory.BZFun.lastCol, ← hw]
      exact unip_apply_castSucc_last k (n + 1) w _
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_setOf_eq, hl,
      mirChar_eq k ψ n u w hw.symm]
    constructor
    · intro h
      apply Circle.ext
      simpa using congrArg Units.val h
    · intro h
      rw [h, map_one]
  rw [he]
  exact (GlobalTheory.CompanionTheory.BZFun.isOpen_addChar_eq_one k ψ hψ).preimage
    ((continuous_apply _).comp (GlobalTheory.CompanionTheory.BZFun.continuous_lastCol k (n + 1)))

theorem isClosed_Cl (i t : ℕ) : IsClosed (Cl k i t) := by
  have hc : Continuous fun p : Mir k ((i + 1) + t + 1) =>
      (((p⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)
  have he : Cl k i t = ⋂ c : Fin (i + 1), {p : Mir k ((i + 1) + t + 1) |
      (((p⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
        (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castLE (by omega) c) = 0} := by
    ext p
    simp [Cl]
  rw [he]
  exact isClosed_iInter fun c => isClosed_eq (hc.matrix_elem _ _) continuous_const

end Top

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) (i t : ℕ),
  (MirUin k ((i + 1) + t + 1)).Normal ∧ IsOpen ((mirChar k ψ ((i + 1) + t)).ker : Set (MirUin k ((i + 1) + t + 1))) ∧
    IsClosed (Cl k i t) ∧ (∀ h ∈ HPG k (i + 1) (t + 1), ∀ x ∈ Cl k i t, h * x ∈ Cl k i t) ∧
    (∀ x ∈ Cl k i t, ∀ u ∈ MirUin k ((i + 1) + t + 1), x * u ∈ Cl k i t) ∧
    ∀ L₁ L₂ : Subgroup (Mir k ((i + 1) + t + 1)), L₁ ≤ MirUin k ((i + 1) + t + 1) → L₂ ≤ MirUin k ((i + 1) + t + 1) →
      IsCompact (L₁ : Set (Mir k ((i + 1) + t + 1))) → IsCompact (L₂ : Set (Mir k ((i + 1) + t + 1))) →
      ∃ L : Subgroup (Mir k ((i + 1) + t + 1)), L ≤ MirUin k ((i + 1) + t + 1) ∧ IsCompact (L : Set (Mir k ((i + 1) + t + 1))) ∧
        L₁ ≤ L ∧ L₂ ≤ L := by
  intro k _ _ _ _ ψ hψ i t
  refine ⟨mirUin_normal _, mirChar_ker_open ψ hψ _, isClosed_Cl i t, fun h hh x hx => Cl_left h hh x hx,
    fun x hx u hu => Cl_right x hx u hu, fun L₁ L₂ h₁ h₂ c₁ c₂ => ⟨prodSub L₁ L₂ h₁ h₂, ?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact (MirUin k _).mul_mem (h₁ ha) (h₂ hb)
  · exact (c₁.mul c₂ : IsCompact ((L₁ : Set (Mir k ((i + 1) + t + 1))) * (L₂ : Set (Mir k ((i + 1) + t + 1)))))
  · intro a ha
    exact ⟨a, ha, 1, L₂.one_mem, mul_one a⟩
  · intro b hb
    exact ⟨1, L₁.one_mem, b, hb, one_mul b⟩

end GlobalTheory.CompanionTheory.BZPhiPG.Grp

end
end
