module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionOfBasicOpenCover
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.RealLift.FirstLine

open scoped Matrix Classical
open Formalism.BasicNotions.TH

open GlobalTheory.RealLift GlobalTheory.RealLift.LieFirstPf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf' {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem fockMap_swap {σ : E →ₐ[F] E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    {P Q R S : ℕ} {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w} {JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    {JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ}
    {d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ} {A : InfinitePlace F → Matrix α (Ix P Q) ℂ}
    {C : InfinitePlace F → Matrix β (Ix R S) ℂ} {Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ} (hΦ : IsFockMap ψ τ d A C Φ)
    (hdd : ∀ x : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = d.e x) :
    IsFockMap ψ τ d' C A (Φ ∘ₗ (swapT (InfinitePlace F) P Q R S).toLinearMap) := by
  refine ⟨hΦ.1.comp (swapT (InfinitePlace F) P Q R S).injective, fun u hu c hc T => ?_⟩
  have hu' : At (evI F) uᵀ := fun x hx => by rw [← Matrix.transpose_smul, hu x hx, Matrix.transpose_zero]
  have hc' : ∀ w, uᵀ.map (piInf (τ w)) = A w * (c w)ᵀ * (C w)ᵀ := fun w => by
    rw [Matrix.transpose_map, hc w]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have key := hΦ.2 uᵀ hu' (fun w => (c w)ᵀ) hc' (swapT (InfinitePlace F) P Q R S T)
  have hr : ∀ t : ℝ, d'.rho ψ (realAd F t • u) = d.rho ψ (realAd F t • uᵀ) := fun t => by
    show schr ψ (d'.e _) = schr ψ (d.e _)
    rw [← hdd, Matrix.transpose_smul, Matrix.transpose_transpose]
  set_option backward.isDefEq.respectTransparency false in
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr]
    rwa [swapT_sumPl (fun w => heisOp (c w)) (fun w => heisOp (c w)ᵀ) (fun w f => swapE_heisOp (c w) f)]

end GlobalTheory.RealLift.FirstLine
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealEquiv

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : Datum.InfFam D} {M : DSModel V S}
  {J : Set (GA D V)} {χ : GA D V → ℂ}


open Classical in
theorem list_equiv {U : MMap M} (hU : IsMultMap θ M J χ U)
    (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : ∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ))
    (v w : M.Vec) (h : ∀ ρ, (w ρ : M.H ρ) = M.rep ρ (g ρ) (v ρ : M.H ρ)) (l : List D.what₂.Tau) (hl : l.Nodup) :
    U (fun ρ => if ρ ∈ l then w ρ else v ρ) = rTr V (l.map fun ρ => atTau θ V ρ (g ρ)).prod (U v) := by
  induction l with
  | nil =>
    funext x
    simp [rTr]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have e := hU.equiv a (g a) (hg a) (fun ρ => if ρ ∈ l then w ρ else v ρ) (w a) (by
      simp only [if_neg hl.1]; exact h a)
    rw [ih hl.2] at e
    have e2 : rTr V ((a :: l).map fun ρ => atTau θ V ρ (g ρ)).prod (U v) =
        rTr V (atTau θ V a (g a)) (rTr V (l.map fun ρ => atTau θ V ρ (g ρ)).prod (U v)) := by
      funext x
      simp only [rTr, List.map_cons, List.prod_cons, mul_assoc]
    rw [e2, ← e]
    congr 1
    funext ρ
    by_cases hρ : ρ = a
    · subst hρ
      simp
    · rw [Function.update_of_ne hρ]
      simp [hρ]

theorem mult_realElt : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : Datum.InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ U ∈ Mult θ M J χ, ∀ g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)) → ∀ v w : M.Vec, (∀ ρ, (w ρ : M.H ρ) = M.rep ρ (g ρ) (v ρ : M.H ρ)) → U w = rTr V (realElt θ V g) (U v) := by
  intro D V S θ M J χ U hU g hg v w h
  classical
  induction hU using Submodule.span_induction with
  | mem U hU =>
    have e := list_equiv hU g hg v w h (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _)
    rw [realElt, ← e]
    congr 1
    funext ρ
    simp
  | zero => funext x; simp [rTr]
  | add U U' _ _ h1 h2 =>
    funext x
    have a := congrFun h1 x
    have b := congrFun h2 x
    simp only [rTr, MultilinearMap.add_apply, Pi.add_apply] at a b ⊢
    rw [a, b]
  | smul c U _ h1 =>
    funext x
    have a := congrFun h1 x
    simp only [rTr, MultilinearMap.smul_apply, Pi.smul_apply] at a ⊢
    rw [a]

end GlobalTheory.RealEquiv
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicScalar.SizeBounds

theorem one_le_rdE (D : D7) : (1 : ℝ) ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.one_le_rpow
  · have h := NumberField.discr_ne_zero D.host.E
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs h
  · positivity

theorem one_le_b (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) : 1 ≤ b := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Sizes at h
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]
    show 0 < 2 * D.R.ord
    have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    omega
  obtain ⟨-, -, -, hb⟩ := h.1 τ
  have hq := (D.hc τ).gap_be i
  have hr : ((((D.R.t : ℚ) + 3) / 2 : ℚ) : ℝ) ≤ (((D.hc τ).e i - (D.hc τ).b i : ℚ) : ℝ) := by
    exact_mod_cast hq
  push_cast at hr
  have habs := abs_le.mp (hb i)
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  linarith [habs.1, habs.2]

theorem lam_bounds (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (τ : D.what₂.Tau) (n : ℕ) :
    -b ≤ ((Formalism.L2.NTheta.lamAt (D.hc τ) n : ℚ) : ℝ) + (((D.hc τ).e i : ℚ) : ℝ) ∧
      ((Formalism.L2.NTheta.lamAt (D.hc τ) n : ℚ) : ℝ) + (((D.hc τ).e i : ℚ) : ℝ) ≤ 3 * b := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Sizes at h
  obtain ⟨he0, he2, hv, hb⟩ := h.1 τ
  have hb0 : (0 : ℝ) ≤ b := by linarith
  unfold Formalism.L2.NTheta.lamAt
  split_ifs with h1 h2
  · obtain ⟨hv0, hv1⟩ := hv ⟨n, h1⟩
    constructor <;> linarith
  · have habs := abs_le.mp (hb ⟨n - (D.R.k - 1), h2⟩)
    push_cast
    constructor <;> linarith [habs.1, habs.2]
  · push_cast
    constructor <;> linarith

theorem toNat_floor_le (x : ℚ) (c : ℝ) (hc : 0 ≤ c) (hx : (x : ℝ) ≤ c) : ((⌊x⌋.toNat : ℕ) : ℝ) ≤ c := by
  rcases le_or_gt ⌊x⌋ 0 with h0 | h0
  · rw [Int.toNat_of_nonpos h0]
    simpa using hc
  · have h1 : ((⌊x⌋.toNat : ℕ) : ℤ) = ⌊x⌋ := Int.toNat_of_nonneg h0.le
    have h2 : ((⌊x⌋.toNat : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast h1
    rw [h2]
    have h3 : ((⌊x⌋ : ℤ) : ℝ) ≤ ((x : ℚ) : ℝ) := by exact_mod_cast Int.floor_le x
    linarith

theorem aPl_le (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (p : ℕ) (τ : D.what₂.Tau) (n : ℕ) :
    (aPl D i p τ n : ℝ) ≤ 3 * b := by
  have hlam := (lam_bounds D i b h τ n).2
  have hb1 := one_le_b D i b h
  unfold aPl
  split_ifs with hn
  · apply toNat_floor_le _ _ (by linarith)
    push_cast
    have hnp : (n : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
    have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith
  · simp only [Nat.cast_zero]
    linarith

theorem aMi_le (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (p q : ℕ) (τ : D.what₂.Tau) (n : ℕ) :
    (aMi D i p q τ n : ℝ) ≤ 3 * b := by
  have hlam := (lam_bounds D i b h τ (p + (q - n) - 1)).1
  have hb1 := one_le_b D i b h
  unfold aMi
  split_ifs with hn
  · apply toNat_floor_le _ _ (by linarith)
    push_cast
    have hqn : (0 : ℝ) ≤ ((q - n : ℕ) : ℝ) := Nat.cast_nonneg _
    have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith
  · simp only [Nat.cast_zero]
    linarith

theorem degAt_le (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    (degAt D i σ ρ : ℝ) ≤ 3 * (D.R.r : ℝ) * b := by
  have hb1 := one_le_b D i b h
  have hi := i.isLt
  have hs := D.sp.W_sigval ((i : ℕ) + 1) (by omega) (by omega) (tauE D ρ)
  have hP : ∀ n, ((aPlAt D i σ ρ n : ℕ) : ℝ) ≤ 3 * b := fun n => aPl_le D i b h _ _ n
  have hM : ∀ n, ((aMiAt D i σ ρ n : ℕ) : ℝ) ≤ 3 * b := fun n => aMi_le D i b h _ _ _ n
  have h1 := Finset.sum_le_sum (s := Finset.range (pW D i ρ)) (fun n _ => hP n)
  have h2 := Finset.sum_le_sum (s := Finset.range (qW D i ρ)) (fun n _ => hM n)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1 h2
  have hr : (pW D i ρ : ℝ) + (qW D i ρ : ℝ) = (D.R.r : ℝ) := by
    have hn : pW D i ρ + qW D i ρ = D.R.r := by
      simp only [pW, qW, Wc, hs]
      unfold Formalism.BasicNotions.Ranks.sigW Formalism.BasicNotions.Ranks.r
      dsimp only
      omega
    exact_mod_cast hn
  unfold degAt
  push_cast
  calc _ ≤ (pW D i ρ : ℝ) * (3 * b) + (qW D i ρ : ℝ) * (3 * b) := add_le_add h1 h2
    _ = 3 * (D.R.r : ℝ) * b := by rw [← hr]; ring

theorem sizes : ∀ (D : D7) (i : Fin D.R.m) (b : ℝ), Sizes D i b → (5.5 : ℝ) ≤ Lp D b ∧ Real.log (D.R.nV : ℝ) ≤ Lp D b ∧ 0 ≤ b ∧ Real.log (3 * (D.R.r : ℝ) * b + 2) ≤ 2 * Lp D b ∧ ∀ (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), (degAt D i σ ρ : ℝ) ≤ 3 * (D.R.r : ℝ) * b := by
  intro D i b h
  have hb1 := one_le_b D i b h
  have hrd := one_le_rdE D
  have hnV : (1 : ℝ) ≤ (D.R.nV : ℝ) := by
    have h1 := D.R.t_odd.pos
    have h2 : 1 ≤ D.R.nV := by
      unfold Formalism.BasicNotions.Ranks.nV
      omega
    exact_mod_cast h2
  have hk5 : 5 ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    have := D.R.two_le_m
    omega
  have hrk : D.R.r ≤ 2 * D.R.k := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hk : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk5
  have hr2 : (D.R.r : ℝ) ≤ 2 * (D.R.k : ℝ) := by exact_mod_cast hrk
  have hgl := h.2
  have hg0 := hgl 0
  have hg1 := hgl 1
  set y : ℝ := (D.R.k : ℝ) * b with hy
  have hy5 : 5 ≤ y := by nlinarith
  have hy8 : y ^ 3 ≤ y ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hyy : 25 ≤ y * y := by nlinarith
  have hy3 : 25 * y ≤ y ^ 3 := by nlinarith [mul_le_mul_of_nonneg_right hyy (by linarith : (0 : ℝ) ≤ y)]
  have hyP : (390625 : ℝ) ≤ y ^ 8 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hy5 8
    norm_num at this
    linarith
  have hg1' : (1 : ℝ) ≤ (D.host.g 1 : ℝ) := by linarith
  have hg0' : (0 : ℝ) ≤ (D.host.g 0 : ℝ) := Nat.cast_nonneg _
  have hbr : (1 : ℝ) ≤ b * D.host.rdE := one_le_mul_of_one_le_of_one_le hb1 hrd
  have hG : (D.host.g 0 : ℝ) ≤ (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := le_mul_of_one_le_right hg0' hg1'
  have hA : (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) :=
    le_mul_of_one_le_left (by positivity) hbr
  have hB : b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤
      b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) :=
    le_mul_of_one_le_right (by positivity) hnV
  have hC : (1 : ℝ) ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by linarith
  have hD : (D.R.nV : ℝ) ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) :=
    le_mul_of_one_le_left (by positivity) hC
  have hX : y ^ 8 ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) := by linarith
  have hL : Lp D b = Real.log (b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ)) := rfl
  have hXpos : 0 < b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) := by linarith
  have he6 : Real.exp (5.5 : ℝ) ≤ 729 := by
    have h1 : Real.exp (5.5 : ℝ) ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
    have h2 : Real.exp 6 = Real.exp 1 ^ 6 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h3 : Real.exp 1 ^ 6 ≤ (3 : ℝ) ^ 6 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) 6
    norm_num at h3
    linarith
  have h55 : (5.5 : ℝ) ≤ Lp D b := by
    rw [hL]
    calc (5.5 : ℝ) = Real.log (Real.exp 5.5) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by linarith)
  refine ⟨h55, ?_, by linarith, ?_, fun σ ρ => degAt_le D i b h σ ρ⟩
  · rw [hL]
    exact Real.log_le_log (by linarith) hD
  · have hb0 : (0 : ℝ) ≤ b := by linarith
    have hrb : (D.R.r : ℝ) * b ≤ (2 * (D.R.k : ℝ)) * b := mul_le_mul_of_nonneg_right hr2 hb0
    have h32 : 3 * (D.R.r : ℝ) * b + 2 ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) := by
      nlinarith
    have hpos : 0 < 3 * (D.R.r : ℝ) * b + 2 := by positivity
    have hlog := Real.log_le_log hpos h32
    rw [← hL] at hlog
    linarith

end GlobalTheory.AdelicScalar.SizeBounds
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicScalar

theorem conjFrame_mem_UH : ∀ (p q n : ℕ), p + q = n → ∀ (Gm : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), (Aᴴ * Formalism.UG.Jpq p q * A : Matrix (Fin n) (Fin n) ℂ) = Gm → IsUnit Gm.det → ∀ b : UpqT p q, conjFrame Gm A (UpqT.mat b) ∈ Formalism.QuantumDeterminants.UH Gm := by
  intro p q n hn Gm A hA hG b
  have hJ : (Formalism.UG.Jpq p q)ᴴ = Formalism.UG.Jpq p q := by simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]
  have h1 : Gm⁻¹ * Gm = 1 := Matrix.nonsing_inv_mul _ hG
  have hb : (UpqT.mat b)ᴴ * Formalism.UG.Jpq p q * UpqT.mat b = Formalism.UG.Jpq p q := b.2
  have hl : (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * A = 1 := by rw [Matrix.mul_assoc, hA, h1]
  have e : Fin n ≃ Fin p ⊕ Fin q := (finCongr hn.symm).trans finSumFinEquiv.symm
  have hr : A * (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hl
  have hc : A * conjFrame Gm A (UpqT.mat b) = UpqT.mat b * A := by
    have : A * conjFrame Gm A (UpqT.mat b) = A * (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * (UpqT.mat b * A) := by
      simp only [conjFrame, Matrix.mul_assoc]
    rw [this, hr, Matrix.one_mul]
  change (conjFrame Gm A (UpqT.mat b))ᴴ * Gm * conjFrame Gm A (UpqT.mat b) = Gm
  generalize conjFrame Gm A (UpqT.mat b) = C at hc
  calc Cᴴ * Gm * C = (A * C)ᴴ * Formalism.UG.Jpq p q * (A * C) := by
        rw [← hA]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Aᴴ * ((UpqT.mat b)ᴴ * Formalism.UG.Jpq p q * UpqT.mat b) * A := by
        rw [hc]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Gm := by rw [hb, hA]

end GlobalTheory.AdelicScalar
end

section

noncomputable section

namespace GlobalTheory.CovTop.VolUp

open NumberField MeasureTheory Matrix Formalism.BasicNotions GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

def dg {ι : Type} [DecidableEq ι] (a₀ : ι) (z : ℂ) : Matrix ι ι ℂ := Matrix.diagonal (Function.update 1 a₀ z)

def sMat {p q : ℕ} (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  UpqT.mat u * dg a₀ (UpqT.mat u).det⁻¹

def permM {ι : Type} {r : ℕ} (e : ι ≃ Fin r) : Matrix ι (Fin r) ℂ := Matrix.of fun i j => if e i = j then 1 else 0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def frBall (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (ε : ℝ) : Set (realSU Ψ G) :=
  {s | ∀ τ a b, ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ < ε}

def IsIdent {κ : Type} (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ)
    (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) : Prop :=
  ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ = -(G.map (σ ρ).1)ᵀ ∧ A ρ * mat x (σ ρ) = permM (e ρ)

def IsProj {κ : Type} (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (σ : κ ≃ Ψ)
    (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ))
    (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G) : Prop :=
  ∀ b ρ, A ρ * (((π b).1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = sMat (a₀ ρ) (b ρ) * A ρ

section Adelic

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Datum GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsRealPart {D : D7} (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V → ∀ ρ, Upq V ρ) : Prop :=
  ∀ h ρ, UpqT.mat (rp h ρ) * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h

end Adelic

theorem permM_mul_transpose {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin r) : permM e * (permM e)ᵀ = 1 := by
  ext i j
  simp [permM, Matrix.mul_apply, Matrix.one_apply, eq_comm]

theorem transpose_mul_permM {ι : Type} [Fintype ι] (e : ι ≃ Fin r) : (permM e)ᵀ * permM e = 1 := by
  ext i j
  rw [Matrix.mul_apply, ← e.symm.sum_comp]
  simp [permM, Matrix.one_apply, eq_comm]

theorem det_dg {ι : Type} [Fintype ι] [DecidableEq ι] (a₀ : ι) (z : ℂ) : (dg a₀ z).det = z := by
  rw [dg, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp

end GlobalTheory.CovTop.VolUp
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc.LeviBlockConjugation

theorem blk_val {E : Type} [Field E] [NumberField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val = Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
  have hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
    exact (m.1.isUnit.map Matrix.detMonoidHom).mul (m.2.isUnit.map Matrix.detMonoidHom)
  unfold blk
  simp only [dif_pos hU, IsUnit.unit_spec]

theorem conj_blk (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w 1 X)⁻¹ * blk h w m 0 * blk h w 1 X = blk h w m (GlobalTheory.LeviDesc.adL m.1 m.2.val X) := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  ext : 1
  simp only [Units.val_mul, blk_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  congr 1
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.fromBlocks_inj, true_and, and_true]
  simp only [adL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_sub, ← Matrix.mul_assoc]
  rw [show m.1.val * (m.1⁻¹ : GL (Fin a) _).val = 1 from by simp]
  simp [Matrix.one_mul, add_sub_cancel]

end GlobalTheory.LeviDesc.LeviBlockConjugation
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylor_lie_condition_of_basicOpen_cover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0})
  (A : Over S) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (R' : Type) [CommRing R'] (β : R →+* R')
  (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
  (∀ r ∈ t, LieAt b act ((algebraMap R' (Localization.Away r)).comp β) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) →
  LieAt b act β x := by
  first | exact @GlobalTheory.UPel.HT.LieLoc.lieAt_of_cover | exact GlobalTheory.UPel.HT.LieLoc.lieAt_of_cover | (intros; apply GlobalTheory.UPel.HT.LieLoc.lieAt_of_cover; all_goals assumption)
end
