module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Mathlib.Topology.Algebra.Group.Units
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle117
public import Mathlib.Topology.Instances.Matrix
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem polyBall_le_of_valuation_le {n : ℕ} {s₁ s₂ : kˣ}
    (h : valuation k (s₁ : k) ≤ valuation k (s₂ : k)) : polyBall n s₁ ≤ polyBall n s₂ := by
  intro x hx i
  exact le_trans (show valuation k (Multiplicative.toAdd x i) ≤ valuation k (s₁ : k) from hx i) h

theorem twKer_polyBall_le_of_valuation_le (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (a : Fin n → k) {s₁ s₂ : kˣ}
    (h : valuation k (s₁ : k) ≤ valuation k (s₂ : k)) :
    twKer ρ (polyBall n s₁) (resChr ψ a (polyBall n s₁)) ≤
      twKer ρ (polyBall n s₂) (resChr ψ a (polyBall n s₂)) := by
  apply Submodule.span_mono
  rintro w ⟨m, u, rfl⟩
  exact ⟨⟨m.1, polyBall_le_of_valuation_le h m.2⟩, u, rfl⟩

theorem resChr_polyBall_eq (ψ : AddChar k Circle) {n : ℕ} {c s : kˣ}
    (hc : ∀ y ∈ cball c, ψ y = 1) {a b : Fin n → k}
    (hab : ∀ i, (a - b) i ∈ cball (c * s⁻¹)) :
    resChr ψ a (polyBall n s) = resChr ψ b (polyBall n s) := by
  ext x
  have hx : ∀ i, valuation k ((Multiplicative.toAdd x.1) i) ≤ valuation k (s : k) := x.2
  have hd : (a - b) ⬝ᵥ Multiplicative.toAdd x.1 ∈ cball c := by
    show valuation k _ ≤ valuation k (c : k)
    unfold dotProduct
    refine Valuation.map_sum_le _ fun i _ => ?_
    rw [Valuation.map_mul]
    calc valuation k ((a - b) i) * valuation k ((Multiplicative.toAdd x.1) i)
        ≤ valuation k ((c * s⁻¹ : kˣ) : k) * valuation k (s : k) := mul_le_mul' (hab i) (hx i)
      _ = valuation k (c : k) := by rw [← Valuation.map_mul, ← Units.val_mul, inv_mul_cancel_right]
  have key : a ⬝ᵥ Multiplicative.toAdd x.1 = b ⬝ᵥ Multiplicative.toAdd x.1 + (a - b) ⬝ᵥ Multiplicative.toAdd x.1 := by
    rw [sub_dotProduct]
    abel
  show ((Circle.toUnits (ψ (a ⬝ᵥ Multiplicative.toAdd x.1)) : ℂˣ) : ℂ) =
    ((Circle.toUnits (ψ (b ⬝ᵥ Multiplicative.toAdd x.1)) : ℂˣ) : ℂ)
  rw [key, AddChar.map_add_eq_mul, hc _ hd, mul_one]

theorem exists_unit_valuation_ge {ι : Type} (S : ι → kˣ) (T : Finset ι) :
    ∃ s : kˣ, ∀ a ∈ T, valuation k (S a : k) ≤ valuation k (s : k) := by
  classical
  rcases T.eq_empty_or_nonempty with hT | hT
  · exact ⟨1, by simp [hT]⟩
  · obtain ⟨a₀, -, ha₀⟩ := T.exists_max_image (fun a => valuation k (S a : k)) hT
    exact ⟨S a₀, ha₀⟩

end

private theorem isHecke_div_and_resEtaPow_div {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (hψ : Continuous ψ) : ∃ c : kˣ, ∀ y ∈ GlobalTheory.SplitWeil.cball c, ψ y = 1 := by
  have hU : IsOpen {z : Circle | 0 < (z : ℂ).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
  have hW : ψ ⁻¹' {z : Circle | 0 < (z : ℂ).re} ∈ 𝓝 (0 : k) := by
    apply hψ.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact hU.mem_nhds (by simp)
  have hW' : {f : Fin 1 → k | f 0 ∈ ψ ⁻¹' {z : Circle | 0 < (z : ℂ).re}} ∈ 𝓝 (0 : Fin 1 → k) :=
    (continuous_apply 0).continuousAt.preimage_mem_nhds hW
  obtain ⟨c, hcW⟩ := GlobalTheory.SplitWeil.FourierPi.exists_box_subset hW'
  refine ⟨c, fun y hy => ?_⟩
  have hmem : ∀ m : ℕ, m • y ∈ GlobalTheory.SplitWeil.cball c := by
    intro m
    induction m with
    | zero => simp only [zero_smul, GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, map_zero]; exact zero_le'
    | succ m ih =>
      rw [succ_nsmul]
      simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at ih hy ⊢
      exact Valuation.map_add_le _ ih hy
  have hpos : ∀ m : ℕ, 0 < (((ψ y) ^ m : Circle) : ℂ).re := by
    intro m
    have := hcW (show (fun _ : Fin 1 => m • y) ∈ GlobalTheory.SplitWeil.FourierPi.box (Fin 1) c from fun i _ => hmem m)
    rw [← AddChar.map_nsmul_eq_pow]
    exact this
  have hn : ∀ w : Circle, (w : ℂ).re * (w : ℂ).re + (w : ℂ).im * (w : ℂ).im = 1 := by
    intro w
    rw [← Complex.normSq_apply]
    exact Circle.normSq_coe w
  have hsq : ∀ w : Circle, ((w ^ 2 : Circle) : ℂ).re = 2 * (w : ℂ).re ^ 2 - 1 := by
    intro w
    have h2 : ((w ^ 2 : Circle) : ℂ) = (w : ℂ) * (w : ℂ) := by rw [pow_two]; rfl
    rw [h2, Complex.mul_re]
    nlinarith [hn w]
  have hle1 : ∀ w : Circle, (w : ℂ).re ≤ 1 := fun w => by nlinarith [hn w]
  have hstep : ∀ j : ℕ, (ψ y) ^ (2 ^ (j + 1)) = ((ψ y) ^ (2 ^ j)) ^ 2 := fun j => by rw [pow_succ, pow_mul]
  have hgrow : ∀ j : ℕ, (2 : ℝ) ^ j * (1 - ((ψ y : Circle) : ℂ).re) ≤ 1 - ((((ψ y) ^ (2 ^ j) : Circle)) : ℂ).re := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [hstep j, hsq]
      have h0 := hpos (2 ^ j)
      have h1 := hle1 ((ψ y) ^ (2 ^ j))
      rw [pow_succ]
      nlinarith
  have hx0 : 1 ≤ ((ψ y : Circle) : ℂ).re := by
    by_contra hlt
    push_neg at hlt
    have hd : 0 < 1 - ((ψ y : Circle) : ℂ).re := by linarith
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / (1 - ((ψ y : Circle) : ℂ).re)) (by norm_num : (1 : ℝ) < 2)
    have h1 := hgrow j
    have h2 := hpos (2 ^ j)
    have h3 : 1 < (2 : ℝ) ^ j * (1 - ((ψ y : Circle) : ℂ).re) := by
      rw [div_lt_iff₀ hd] at hj
      linarith
    linarith
  have hre : ((ψ y : Circle) : ℂ).re = 1 := le_antisymm (hle1 _) hx0
  have him : ((ψ y : Circle) : ℂ).im = 0 := by nlinarith [hn (ψ y)]
  apply Circle.ext
  apply Complex.ext
  · simp [hre]
  · simp [him]

theorem exists_polyBall_twKer_uniform : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ →
    ∀ {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (v : V) (t : kˣ),
    (∀ a : Fin n → k, ∃ s : kˣ, v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s))) →
    ∃ s : kˣ, ∀ a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall n t →
      v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s)) := by
  intro k _ _ _ _ ψ hψ n V _ _ ρ v t hv
  obtain ⟨c, hc⟩ := isHecke_div_and_resEtaPow_div ψ hψ
  choose S hS using hv
  obtain ⟨T, hT⟩ := (GlobalTheory.SplitWeil.FourierPi.isCompact_box (n := Fin n) t).elim_finite_subcover
    (fun a : Fin n → k => (fun b => b - a) ⁻¹' GlobalTheory.SplitWeil.FourierPi.box (Fin n) (c * (S a)⁻¹))
    (fun a => (GlobalTheory.SplitWeil.FourierPi.isOpen_box _).preimage (continuous_id.sub continuous_const))
    (fun b _ => Set.mem_iUnion.2 ⟨b, fun i _ => by simp only [sub_self, Pi.zero_apply, GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, map_zero]; exact zero_le'⟩)
  obtain ⟨s, hs⟩ := exists_unit_valuation_ge S T
  refine ⟨s, fun a ha => ?_⟩
  have haK : a ∈ GlobalTheory.SplitWeil.FourierPi.box (Fin n) t := fun i _ => ha i
  obtain ⟨b, hbT, hab⟩ := Set.mem_iUnion₂.1 (hT haK)
  have heq : resChr ψ a (polyBall n (S b)) = resChr ψ b (polyBall n (S b)) :=
    resChr_polyBall_eq ψ hc (fun i => hab i (Set.mem_univ i))
  have h1 := hS b
  rw [← heq] at h1
  exact twKer_polyBall_le_of_valuation_le ψ ρ a (hs b hbT) h1

end GlobalTheory.CompanionTheory.MirFourier

end
end

section

noncomputable section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier
namespace GlobalTheory.CompanionTheory.MirLevi
variable {k : Type} [Field k]

def uv (n : ℕ) (v : Fin n → k) : Mir k n := unipIn k n (Multiplicative.ofAdd v)


variable (k) in
def LH (n : ℕ) : Subgroup (Mir k n) := (levi k n).range


variable (k) in
def lv (n : ℕ) : GL (Fin n) k →* LH k n := (levi k n).rangeRestrict

def colv {n : ℕ} (g : Mir k n) : Fin n → k :=
  fun i => ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n)

def mvec {n : ℕ} (g : Mir k n) : Fin n → k :=
  (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec (colv g)

theorem mirProj_levi (n : ℕ) (m : GL (Fin n) k) : mirabolicProjection k n (levi k n m) = m := by
  apply Units.ext
  ext i j
  show GlobalTheory.BZMir.glEmbMat k n (m : Matrix (Fin n) (Fin n) k) (Fin.castSucc i) (Fin.castSucc j) = _
  simp [GlobalTheory.BZMir.glEmbMat]

theorem mirProj_uv (n : ℕ) (v : Fin n → k) : mirabolicProjection k n (uv n v) = 1 := by
  apply Units.ext
  ext i j
  show (1 + GlobalTheory.BZMir.colMat k n v) (Fin.castSucc i) (Fin.castSucc j) = (1 : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem coe_levi_mul_uv (n : ℕ) (m : GL (Fin n) k) (v : Fin n → k) :
    (((levi k n m * uv n v : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      glEmbMat k n (m : Matrix (Fin n) (Fin n) k) + colMat k n ((m : Matrix (Fin n) (Fin n) k).mulVec v) := by
  show GlobalTheory.BZMir.glEmbMat k n (m : Matrix (Fin n) (Fin n) k) * (1 + GlobalTheory.BZMir.colMat k n v) = _
  rw [mul_add, mul_one, GlobalTheory.BZMir.glEmbMat_mul_colMat]

theorem colv_levi_mul_uv (n : ℕ) (m : GL (Fin n) k) (v : Fin n → k) :
    colv (levi k n m * uv n v) = (m : Matrix (Fin n) (Fin n) k).mulVec v := by
  funext i
  simp only [GlobalTheory.CompanionTheory.MirLevi.colv]
  rw [GlobalTheory.CompanionTheory.MirLevi.coe_levi_mul_uv]
  simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat]

theorem mvec_levi_mul_uv (n : ℕ) (m : GL (Fin n) k) (v : Fin n → k) :
    mvec (levi k n m * uv n v) = v := by
  unfold GlobalTheory.CompanionTheory.MirLevi.mvec
  rw [GlobalTheory.CompanionTheory.MirLevi.colv_levi_mul_uv, map_mul, GlobalTheory.CompanionTheory.MirLevi.mirProj_levi,
    GlobalTheory.CompanionTheory.MirLevi.mirProj_uv, mul_one, Matrix.mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem decomp {n : ℕ} (g : Mir k n) : g = levi k n (mirabolicProjection k n g) * uv n (mvec g) := by
  have hA : ((GlobalTheory.BZMir.mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec
      (GlobalTheory.CompanionTheory.MirLevi.mvec g) = GlobalTheory.CompanionTheory.MirLevi.colv g := by
    unfold GlobalTheory.CompanionTheory.MirLevi.mvec
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hP : ∀ i j, ((GlobalTheory.BZMir.mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc j) :=
    fun _ _ => rfl
  have hlast := (GlobalTheory.BZMir.mem_Mir_iff k (g : GL (Fin (n + 1)) k)).1 g.2
  apply Subtype.ext
  apply Units.ext
  rw [GlobalTheory.CompanionTheory.MirLevi.coe_levi_mul_uv, hA]
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [congrFun hlast j]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, GlobalTheory.BZMir.eLast]
    · simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, GlobalTheory.BZMir.eLast, Pi.single_apply,
        Fin.castSucc_ne_last]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, GlobalTheory.CompanionTheory.MirLevi.colv]
    · simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, hP, Fin.castSucc_ne_last]

theorem mvec_uv (n : ℕ) (v : Fin n → k) : mvec (uv n v) = v := by
  have h := GlobalTheory.CompanionTheory.MirLevi.mvec_levi_mul_uv n (1 : GL (Fin n) k) v
  rwa [map_one, one_mul] at h

theorem mvec_levi_mul (n : ℕ) (m : GL (Fin n) k) (g : Mir k n) : mvec (levi k n m * g) = mvec g := by
  conv_lhs => rw [GlobalTheory.CompanionTheory.MirLevi.decomp g, ← mul_assoc, ← map_mul]
  rw [GlobalTheory.CompanionTheory.MirLevi.mvec_levi_mul_uv]

theorem uv_add (n : ℕ) (v w : Fin n → k) : uv n (v + w) = uv n v * uv n w := by
  simp only [GlobalTheory.CompanionTheory.MirLevi.uv, ofAdd_add, map_mul]

theorem uv_zero (n : ℕ) : uv n (0 : Fin n → k) = 1 := by
  simp [GlobalTheory.CompanionTheory.MirLevi.uv]

theorem uv_mul_levi (n : ℕ) (m : GL (Fin n) k) (v : Fin n → k) :
    uv n v * levi k n m = levi k n m * uv n (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) := by
  apply Subtype.ext
  have h := GlobalTheory.BZMir.glEmb_mul_unip' k n m
    (Multiplicative.ofAdd (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v))
  rw [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mulVec] at h
  exact h.symm

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E)

def restr : cIndSpace (LH k n) ρ →ₗ[ℂ] (Fin n → k) → E where
  toFun f v := f.1.1.1 (uv n v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restr_injective : Function.Injective (restr ρ) := by
  intro f f' h
  have key : ∀ (F : GlobalTheory.PRep.cIndSpace (GlobalTheory.CompanionTheory.MirLevi.LH k n) ρ)
      (x : GlobalTheory.CompanionTheory.MirLevi.LH k n) (g : GlobalTheory.BZMir.Mir k n),
      F.1.1.1 ((x : GlobalTheory.BZMir.Mir k n) * g) = ρ x (F.1.1.1 g) := by
    intro F x g
    first
    | exact F.1.1.2 x g
    | exact F.1.2 x g
    | exact F.2 x g
    | simpa using F.1.1.2 x g
  have hv : ∀ v, f.1.1.1 (GlobalTheory.CompanionTheory.MirLevi.uv n v) = f'.1.1.1 (GlobalTheory.CompanionTheory.MirLevi.uv n v) :=
    fun v => congrFun h v
  have hall : ∀ g, f.1.1.1 g = f'.1.1.1 g := by
    intro g
    have e : GlobalTheory.BZMir.levi k n (GlobalTheory.BZMir.mirabolicProjection k n g) =
        ((GlobalTheory.CompanionTheory.MirLevi.lv k n (GlobalTheory.BZMir.mirabolicProjection k n g) :
          GlobalTheory.CompanionTheory.MirLevi.LH k n) : GlobalTheory.BZMir.Mir k n) := rfl
    rw [GlobalTheory.CompanionTheory.MirLevi.decomp g, e, key f, key f', hv]
  first
  | exact Subtype.ext (Subtype.ext (Subtype.ext (funext hall)))
  | exact Subtype.ext (Subtype.ext (Subtype.ext (by ext g; exact hall g)))

theorem restr_uv (a : Fin n → k) (f : cIndSpace (LH k n) ρ) (v : Fin n → k) :
    restr ρ (cInd (LH k n) ρ (uv n a) f) v = restr ρ f (v + a) := by
  show f.1.1.1 (GlobalTheory.CompanionTheory.MirLevi.uv n v * GlobalTheory.CompanionTheory.MirLevi.uv n a) = _
  exact congrArg (fun g => f.1.1.1 g) (GlobalTheory.CompanionTheory.MirLevi.uv_add n v a).symm

theorem restr_levi (m : GL (Fin n) k) (f : cIndSpace (LH k n) ρ) (v : Fin n → k) :
    restr ρ (cInd (LH k n) ρ (levi k n m) f) v =
      ρ (lv k n m) (restr ρ f (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v)) := by
  have key : ∀ (x : GlobalTheory.CompanionTheory.MirLevi.LH k n) (g : GlobalTheory.BZMir.Mir k n),
      f.1.1.1 ((x : GlobalTheory.BZMir.Mir k n) * g) = ρ x (f.1.1.1 g) := by
    intro x g
    first
    | exact f.1.1.2 x g
    | exact f.1.2 x g
    | exact f.2 x g
    | simpa using f.1.1.2 x g
  have e : GlobalTheory.BZMir.levi k n m =
      ((GlobalTheory.CompanionTheory.MirLevi.lv k n m : GlobalTheory.CompanionTheory.MirLevi.LH k n) : GlobalTheory.BZMir.Mir k n) := rfl
  show f.1.1.1 (GlobalTheory.CompanionTheory.MirLevi.uv n v * GlobalTheory.BZMir.levi k n m) = _
  rw [GlobalTheory.CompanionTheory.MirLevi.uv_mul_levi, e, key]
  rfl

end Rep

end GlobalTheory.CompanionTheory.MirLevi
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colMat_toAdd (n : ℕ) :
    Continuous fun x : Multiplicative (Fin n → k) => colMat k n x.toAdd := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases hj : j = Fin.last n
  · subst hj
    induction i using Fin.lastCases with
    | last => simpa [colMat] using continuous_const
    | cast i =>
      have h : Continuous fun a : Multiplicative (Fin n → k) => Multiplicative.toAdd a i :=
        (continuous_apply i).comp continuous_toAdd
      simpa [colMat] using h
  · simpa [colMat, hj] using continuous_const

theorem continuous_unipMir (n : ℕ) : Continuous (unipMir k n) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_const.add (continuous_colMat_toAdd n)
  · have h : Continuous fun x : Multiplicative (Fin n → k) => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) - colMat k n x.toAdd :=
      continuous_const.sub (continuous_colMat_toAdd n)
    exact h

theorem isSmooth_comp_unipMir : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V), IsSmooth τ → IsSmooth (τ.comp (unipMir k n)) := by
  intro k _ _ _ _ n V _ _ τ h w
  exact (h w).preimage (continuous_unipMir n)

end GlobalTheory.CompanionTheory.MirFourier

end
end

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CoordR

theorem coordInf : PositivityTheory.PfSWUS.SchInf.CoordInf := by
  intro F E _ _ _ _ _ σ hσ n M
  obtain ⟨-, e, -, he, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hσ.1
  let eh : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph _
  have heh : ∀ y, eh y = e y := fun _ => rfl
  haveI : SecondCountableTopology (Ainf F) := eh.secondCountableTopology
  haveI : T2Space (Ainf F) := eh.symm.t2Space
  obtain ⟨i1, i2, i3, i4, -, -, hb, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  let d := Module.finrank F E
  let b : Module.Basis (Fin d) F E := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (Ainf F) b
  let Hs : (Ainf F ⊗[F] E) ≃ₜ (Fin d → Ainf F) := (hb d b).homeomorph _
  have hHs : ∀ y k, Hs y k = B.repr y k := fun _ _ => rfl
  let I := Fin n × Fin M × Fin d × InfinitePlace F
  let q : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let eH : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin (Fintype.card I) → ℝ) :=
    { toFun := fun X t => eh (Hs (X (q.symm t).1 (q.symm t).2.1) (q.symm t).2.2.1) (q.symm t).2.2.2
      invFun := fun y a j => Hs.symm fun k => eh.symm fun w => y (q (a, j, k, w))
      left_inv := fun X => by simp
      right_inv := fun y => by
        funext t
        simp
      continuous_toFun := continuous_pi fun t =>
        (continuous_apply _).comp (eh.continuous.comp ((continuous_apply _).comp
          (Hs.continuous.comp ((continuous_apply _).comp (continuous_apply _)))))
      continuous_invFun := continuous_pi fun a => continuous_pi fun j =>
        Hs.symm.continuous.comp (continuous_pi fun k => eh.symm.continuous.comp
          (continuous_pi fun w => continuous_apply _)) }
  have hadd : ∀ X Y, eH (X + Y) = eH X + eH Y := by
    intro X Y
    funext t
    change eh (Hs (X _ _ + Y _ _) _) _ = eh (Hs (X _ _) _) _ + eh (Hs (Y _ _) _) _
    simp only [hHs, heh, map_add (f := _), Finsupp.add_apply, Pi.add_apply]
  let eV : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin (Fintype.card I) → ℝ) :=
    { eH.toEquiv with map_add' := hadd }
  have hV : ∀ X, eV X = eH X := fun _ => rfl
  have hVs : ∀ y, eV.symm y = eH.symm y := fun _ => rfl
  have hc : Continuous fun p : (Fin n → Fin M → Ainf F ⊗[F] E) × Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) =>
      rmul (Ainf F) p.1 p.2 := by
    refine continuous_pi fun a => continuous_pi fun i => continuous_finsetSum _ fun c _ => ?_
    have h1 : Continuous fun p : (Fin n → Fin M → Ainf F ⊗[F] E) ×
        Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) => p.1 c i :=
      (continuous_apply i).comp ((continuous_apply c).comp continuous_fst)
    exact h1.mul (continuous_snd.matrix_elem c a)
  have hrad : ∀ (g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (X Y : Fin n → Fin M → Ainf F ⊗[F] E),
      rmul (Ainf F) (X + Y) g = rmul (Ainf F) X g + rmul (Ainf F) Y g := by
    intro g X Y
    funext a i
    simp [rmul, add_mul, Finset.sum_add_distrib]
  let L0 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → (Fin (Fintype.card I) → ℝ) →+ (Fin (Fintype.card I) → ℝ) :=
    fun g => AddMonoidHom.mk' (fun y => eV (rmul (Ainf F) (eV.symm y) g)) fun y z => by
      rw [map_add (f := _), hrad, map_add (f := _)]
  have hL0 : ∀ g, Continuous (L0 g) := fun g =>
    eH.continuous.comp (hc.comp (eH.symm.continuous.prodMk continuous_const))
  let L : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → (Fin (Fintype.card I) → ℝ) →L[ℝ] (Fin (Fintype.card I) → ℝ) :=
    fun g => (L0 g).toRealLinearMap (hL0 g)
  refine ⟨Fintype.card I, eV, eH.continuous, eH.symm.continuous, L, ?_, ?_⟩
  · refine continuous_clm_apply.2 fun y => ?_
    exact eH.continuous.comp (hc.comp (continuous_const.prodMk continuous_id))
  · intro g X
    change eV _ = eV (rmul (Ainf F) (eV.symm (eV X)) g)
    rw [AddEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.SW.CoordR

end
end
