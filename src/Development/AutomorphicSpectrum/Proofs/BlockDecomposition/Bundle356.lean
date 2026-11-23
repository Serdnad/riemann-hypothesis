module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle345
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle339
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle335
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Small

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def rowD (i t : ℕ) (b : Fin (t + 1)) : Fin ((i + 1) + (t + 1) + 1) := Fin.castSucc (Fin.natAdd (i + 1) b)

theorem ePG_true_rowD (i t : ℕ) (b : Fin (t + 1)) : ePG (i + 1) (t + 1) ⟨true, b⟩ = rowD i t b :=
  Fin.ext (by simp [rowD, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val])

def ent {n : ℕ} (a b : Fin (n + 1)) (p : Mir k n) : k :=
  ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b

theorem continuous_ent {n : ℕ} (a b : Fin (n + 1)) : Continuous (ent (k := k) a b) :=
  (Units.continuous_val.comp continuous_subtype_val).matrix_elem a b

theorem ent_last_last {n : ℕ} (p : Mir k n) : ent (Fin.last n) (Fin.last n) p = 1 := by
  have hh := (mem_Mir_iff k _).1 p.2
  show ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1
  rw [hh]
  simp [eLast]

theorem colMat_mul_castSucc {n : ℕ} (v : Fin n → k) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (a : Fin n)
    (c : Fin (n + 1)) : (colMat k n v * A) (Fin.castSucc a) c = v a * A (Fin.last n) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
  · simp [colMat]
  · intro l _ hl
    simp [colMat, hl]
  · simp

theorem continuous_colMat_append (i t : ℕ) :
    Continuous fun d : Fin (t + 1) → k => colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := by
  refine continuous_matrix fun a b => ?_
  by_cases hb : b = Fin.last _
  · subst hb
    induction a using Fin.lastCases with
    | last => simpa [colMat] using continuous_const
    | cast a =>
      induction a using Fin.addCases with
      | left a => simpa [colMat] using continuous_const
      | right a =>
        have e : ∀ d : Fin (t + 1) → k, colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)
            (Fin.castSucc (Fin.natAdd (i + 1) a)) (Fin.last _) = d a := by
          intro d
          unfold colMat
          rw [if_pos rfl, Fin.lastCases_castSucc, Fin.append_right]
        exact (continuous_apply a).congr fun d => (e d).symm
  · simpa [colMat, hb] using continuous_const

theorem continuous_dEmb (i t : ℕ) : Continuous (dEmb k i t) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_const.add (continuous_colMat_append i t)
  · exact continuous_const.sub (continuous_colMat_append i t)

theorem dEmb_zero (i t : ℕ) : dEmb k i t 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  show (1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) 0) : Matrix _ _ k) = 1
  have : Fin.append (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
    funext a
    induction a using Fin.addCases <;> simp
  rw [this, colMat_zero, add_zero]

def delta (i t : ℕ) (u : Mir k ((i + 1) + (t + 1))) : Fin (t + 1) → k :=
  fun b => - ent (rowD i t b) (Fin.last _) u

theorem continuous_delta (i t : ℕ) : Continuous (delta (k := k) i t) :=
  continuous_pi fun b => (continuous_ent _ _).neg

theorem delta_one (i t : ℕ) : delta (k := k) i t 1 = 0 := by
  funext b
  have h0 : (1 : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) (rowD i t b) (Fin.last _) = 0 :=
    Matrix.one_apply_ne (Fin.castSucc_ne_last _)
  show - ((1 : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k) (rowD i t b) (Fin.last _)) = 0
  rw [h0, neg_zero]

theorem eq_delta (i t : ℕ) (h u : Mir k ((i + 1) + (t + 1))) (hH : h ∈ HPG k (i + 1) (t + 1))
    (d : Fin (t + 1) → k) (e : h = dEmb k i t d * u) : d = delta i t u := by
  funext b
  have hp : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ parab k (ePG (i + 1) (t + 1)) := hH
  have hz := mem_parab_iff.1 hp true false b (Fin.last (i + 1)) (by decide)
  rw [ePG_true_rowD, ePG_false_last] at hz
  have hv : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val =
      (1 + colMat k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d)) *
        ((u : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val := by
    rw [e]; rfl
  have hz' : ((h : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val
      (rowD i t b) (Fin.last _) = 0 := hz
  rw [hv, add_mul, one_mul, Matrix.add_apply, rowD, colMat_mul_castSucc] at hz'
  have h1 : ((u : Mir k ((i + 1) + (t + 1))) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val (Fin.last _) (Fin.last _) = 1 :=
    ent_last_last u
  rw [h1, mul_one, Fin.append_right] at hz'
  show d b = - ent (rowD i t b) (Fin.last _) u
  exact eq_neg_of_add_eq_zero_right hz'

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Small

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

open Small in
theorem h_small : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (O : Set (Mir k ((i + 1) + t + 1))) (hO : O ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1))),
    ∃ N ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1)), ∀ (h : Mir k ((i + 1) + (t + 1))), h ∈ HPG k (i + 1) (t + 1) →
      ∀ (d : Fin (t + 1) → k) (x : Mir k ((i + 1) + t + 1)), x ∈ N →
        dEmb k i t d * wEl k i t = h * wEl k i t * x → h ∈ O := by
  intro k _ _ _ _ i t O hO
  let w : Mir k ((i + 1) + (t + 1)) := wEl k i t
  let f : Mir k ((i + 1) + (t + 1)) → Mir k ((i + 1) + (t + 1)) :=
    fun x => dEmb k i t (delta i t (w * x⁻¹ * w⁻¹)) * (w * x⁻¹ * w⁻¹)
  have hu : Continuous fun x : Mir k ((i + 1) + (t + 1)) => w * x⁻¹ * w⁻¹ :=
    (continuous_const.mul continuous_inv).mul continuous_const
  have hf : Continuous f :=
    ((continuous_dEmb i t).comp ((continuous_delta i t).comp hu)).mul hu
  have f1 : f 1 = 1 := by
    have e : w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹ = 1 := by group
    show dEmb k i t (delta i t (w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹)) * (w * (1 : Mir k ((i + 1) + (t + 1)))⁻¹ * w⁻¹) = 1
    rw [e, delta_one, dEmb_zero, one_mul]
  refine ⟨f ⁻¹' O, hf.continuousAt.preimage_mem_nhds (by rw [f1]; exact hO), ?_⟩
  intro h hH d x hx e
  have e' : h = dEmb k i t d * (w * x⁻¹ * w⁻¹) := by
    have e2 : dEmb k i t d * w = h * w * x := e
    calc h = (h * w * x) * x⁻¹ * w⁻¹ := by group
      _ = (dEmb k i t d * w) * x⁻¹ * w⁻¹ := by rw [e2]
      _ = dEmb k i t d * (w * x⁻¹ * w⁻¹) := by group
  have hd := eq_delta i t h _ hH d e'
  have hfx : f x = h := by
    show dEmb k i t (delta i t (w * x⁻¹ * w⁻¹)) * (w * x⁻¹ * w⁻¹) = h
    rw [← hd, ← e']
  have : f x ∈ O := hx
  rwa [hfx] at this

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mirabolic_double_coset_decomposition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ),
  (∀ p ∈ Cl k i t, ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)),
      p = h * dEmb k i t d * sEmb k ((i + 1) + t) m) ∧
  (∀ p, p ∉ Cl k i t → ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)),
      p = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) m) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Cells.cells | exact GlobalTheory.CompanionTheory.BZPhiPG.Cells.cells | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Cells.cells <;> assumption)
end

section

noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)
open Formalism.BasicNotions Formalism.GradedWeylDivisibility

namespace GlobalTheory.CompanionTheory.RmHol.HW

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def hv (lam : Fin n → ℤ) : nablaSq ℂ n (dw lam) :=
  ⟨extremal ℂ n (dw lam), hwMem ℂ n n le_rfl _ (factNatW n (dw lam)).1⟩

theorem hv_ne (lam : Fin n → ℤ) : hv lam ≠ 0 := fun h =>
  hwNe ℂ n n le_rfl (dw lam).natW (congrArg Subtype.val h)

theorem dw_w {lam : Fin n → ℤ} (h : Antitone lam) (a : Fin n) : (dw lam).w a = lam a := by
  unfold dw
  rw [dite_eq_left h]

theorem Rm_mulVec (lam : Fin n → ℤ) {x : Mat n} (h : IsUnit x.det) (v : nablaSq ℂ n (dw lam)) :
    Rm lam x *ᵥ ((wb lam).repr v : Jd n lam → ℂ) =
      ((wb lam).repr (GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit x h) v) : Jd n lam → ℂ) := by
  rw [Rm_of_unit lam h]
  exact LinearMap.toMatrix_mulVec_repr _ _ _ _

theorem hasDerivAt_mulVec {lam : Fin n → ℤ} (hD : HolRm lam) (B : Mat n) (c : Jd n lam → ℂ)
    (i : Jd n lam) :
    HasDerivAt (fun t : ℂ => (Rm lam (1 + t • B) *ᵥ c) i) ((XA lam B *ᵥ c) i) 0 := by
  simp only [Matrix.mulVec, dotProduct]
  exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_line hD B i j).mul_const _

theorem fix_upper (lam : Fin n → ℤ) {a b : Fin n} (hab : a < b) {t : ℂ}
    (h : IsUnit ((1 : Mat n) + t • Matrix.single a b (1 : ℂ)).det) :
    GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit _ h) (hv lam) = hv lam := by
  apply Subtype.ext
  refine (factSqHighestWeight ℂ n (dw lam)).2 _ ?_ ?_
  · intro i j hij
    have hij' : j < i := hij
    show ((1 : Mat n) + t • Matrix.single a b (1 : ℂ)) i j = 0
    have h1 : (1 : Mat n) i j = 0 := Matrix.one_apply_ne (ne_of_gt hij')
    have h2 : Matrix.single a b (1 : ℂ) i j = 0 := by
      rw [Matrix.single_apply_of_ne]
      rintro ⟨rfl, rfl⟩
      exact absurd hab (not_lt.2 hij'.le)
    rw [Matrix.add_apply, Matrix.smul_apply, h1, h2]
    simp
  · intro i
    show ((1 : Mat n) + t • Matrix.single a b (1 : ℂ)) i i = 1
    have h2 : Matrix.single a b (1 : ℂ) i i = 0 := by
      rw [Matrix.single_apply_of_ne]
      rintro ⟨rfl, h⟩
      exact hab.ne' h
    rw [Matrix.add_apply, Matrix.smul_apply, h2]
    simp

theorem diag_act {lam : Fin n → ℤ} (hA : Antitone lam) (a : Fin n) {t : ℂ} (ht : 1 + t ≠ 0)
    (h : IsUnit ((1 : Mat n) + t • Matrix.single a a (1 : ℂ)).det) :
    GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit _ h) (hv lam) =
      ((1 + t) ^ (lam a)) • hv lam := by
  classical
  let u : Fin n → ℂˣ := fun i => if i = a then Units.mk0 (1 + t) ht else 1
  have e : Matrix.nonsingInvUnit _ h = diagGL ℂ n u := by
    apply Units.ext
    ext i j
    show ((1 : Mat n) + t • Matrix.single a a (1 : ℂ)) i j = Matrix.diagonal (fun k => (u k : ℂ)) i j
    by_cases hij : i = j
    · subst hij
      by_cases hia : i = a
      · subst hia; simp [u]
      · have h2 : Matrix.single a a (1 : ℂ) i i = 0 := by
          rw [Matrix.single_apply_of_ne]
          rintro ⟨h, -⟩
          exact hia h.symm
        rw [Matrix.add_apply, Matrix.smul_apply, h2]
        simp [u, hia]
    · have h2 : Matrix.single a a (1 : ℂ) i j = 0 := by
        rw [Matrix.single_apply_of_ne]
        rintro ⟨h, h'⟩
        exact hij (h.symm.trans h')
      rw [Matrix.add_apply, Matrix.smul_apply, h2, Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
      simp
  have hp : ((∏ i, (u i) ^ ((dw lam).w i) : ℂˣ) : ℂ) = (1 + t) ^ (lam a) := by
    rw [Finset.prod_eq_single a]
    · simp [u, dw_w hA]
    · intro b _ hb
      simp [u, hb]
    · simp
  rw [e]
  apply Subtype.ext
  have hh := (factSqHighestWeight ℂ n (dw lam)).1 u
  rw [hp] at hh
  exact hh

theorem exists_hw (n : ℕ) (lam : Fin n → ℤ) (hD : HolRm lam) (hA : Antitone lam) :
    ∃ v : Formalism.BasicNotions.nablaSq ℂ n (dw lam), v ≠ 0 ∧
      (∀ a b : Fin n, a < b → Xu lam a b *ᵥ ((wb lam).repr v : Jd n lam → ℂ) = 0) ∧
      ∀ a : Fin n, Xu lam a a *ᵥ ((wb lam).repr v : Jd n lam → ℂ) =
        (lam a : ℂ) • ((wb lam).repr v : Jd n lam → ℂ) := by
  refine ⟨hv lam, hv_ne lam, fun a b hab => ?_, fun a => ?_⟩
  · ext i
    have h1 := hasDerivAt_mulVec hD (Matrix.single a b (1 : ℂ)) ((wb lam).repr (hv lam)) i
    have hev : (fun t : ℂ => (Rm lam (1 + t • Matrix.single a b (1 : ℂ)) *ᵥ
        ((wb lam).repr (hv lam) : Jd n lam → ℂ)) i) =ᶠ[𝓝 0]
        fun _ => ((wb lam).repr (hv lam) : Jd n lam → ℂ) i := by
      filter_upwards [eventually_line_unit (Matrix.single a b (1 : ℂ))] with t ht
      rw [Rm_mulVec lam ht, fix_upper lam hab ht]
    have h2 := (hasDerivAt_const (0 : ℂ) (((wb lam).repr (hv lam) : Jd n lam → ℂ) i)).congr_of_eventuallyEq hev
    simpa [Xu] using h1.unique h2
  · ext i
    have h1 := hasDerivAt_mulVec hD (Matrix.single a a (1 : ℂ)) ((wb lam).repr (hv lam)) i
    have hne : ∀ᶠ t : ℂ in 𝓝 0, 1 + t ≠ 0 := by
      have hc : ContinuousAt (fun t : ℂ => 1 + t) 0 := by fun_prop
      exact hc.eventually_ne (by simp)
    have hev : (fun t : ℂ => (Rm lam (1 + t • Matrix.single a a (1 : ℂ)) *ᵥ
        ((wb lam).repr (hv lam) : Jd n lam → ℂ)) i) =ᶠ[𝓝 0]
        fun t => (1 + t) ^ (lam a) * ((wb lam).repr (hv lam) : Jd n lam → ℂ) i := by
      filter_upwards [eventually_line_unit (Matrix.single a a (1 : ℂ)), hne] with t ht ht'
      rw [Rm_mulVec lam ht, diag_act hA a ht' ht]
      simp
    have hz : HasDerivAt (fun t : ℂ => (1 + t) ^ (lam a)) (lam a : ℂ) 0 := by
      have h0 := hasDerivAt_zpow (lam a) ((1 : ℂ) + 0) (Or.inl (by simp))
      have h3 := h0.comp_const_add 1 0
      have e : (lam a : ℂ) * ((1 : ℂ) + 0) ^ (lam a - 1) = lam a := by simp
      rw [e] at h3
      exact h3
    have h2 := (hz.mul_const (((wb lam).repr (hv lam) : Jd n lam → ℂ) i)).congr_of_eventuallyEq hev
    simpa [Xu] using h1.unique h2

end GlobalTheory.CompanionTheory.RmHol.HW
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

section CosetDecomp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem self_mem_cosetSet_decomp (t : ℕ) (c : k) (a : Fin t → k) : a ∈ cosetSet t c a := by
  show Multiplicative.ofAdd (a - a) ∈ Lc t c
  rw [sub_self, ofAdd_zero]
  exact (Lc t c).one_mem

theorem cosetSet_symm_decomp {t : ℕ} {c : k} {a b : Fin t → k} (h : a ∈ cosetSet t c b) :
    b ∈ cosetSet t c a := by
  have h' : Multiplicative.ofAdd (a - b) ∈ Lc t c := h
  show Multiplicative.ofAdd (b - a) ∈ Lc t c
  rw [← neg_sub, ofAdd_neg]
  exact (Lc t c).inv_mem h'

theorem cosetSet_trans_decomp {t : ℕ} {c : k} {a b d : Fin t → k} (h : a ∈ cosetSet t c b)
    (h' : b ∈ cosetSet t c d) : a ∈ cosetSet t c d := by
  have h1 : Multiplicative.ofAdd (a - b) ∈ Lc t c := h
  have h2 : Multiplicative.ofAdd (b - d) ∈ Lc t c := h'
  show Multiplicative.ofAdd (a - d) ∈ Lc t c
  rw [← sub_add_sub_cancel a b d, ofAdd_add]
  exact (Lc t c).mul_mem h1 h2

theorem exists_coset_reps (t : ℕ) (c : k) (S : Finset (Fin t → k)) :
    ∃ A : Finset (Fin t → k), (∀ s ∈ S, ∃ a ∈ A, s ∈ cosetSet t c a) ∧
      ∀ a ∈ A, ∀ b ∈ A, a ∈ cosetSet t c b → a = b := by
  classical
  refine Finset.induction_on S ?_ ?_
  · exact ⟨∅, by simp, by simp⟩
  · intro x S _ ih
    obtain ⟨A, hcov, huniq⟩ := ih
    by_cases hex : ∃ a ∈ A, x ∈ cosetSet t c a
    · refine ⟨A, ?_, huniq⟩
      intro s hs
      rcases Finset.mem_insert.1 hs with hsx | hsS
      · rw [hsx]
        exact hex
      · exact hcov s hsS
    · push_neg at hex
      refine ⟨insert x A, ?_, ?_⟩
      · intro s hs
        rcases Finset.mem_insert.1 hs with hsx | hsS
        · exact ⟨x, Finset.mem_insert_self _ _, hsx ▸ self_mem_cosetSet_decomp t c x⟩
        · obtain ⟨a, ha, hsa⟩ := hcov s hsS
          exact ⟨a, Finset.mem_insert_of_mem ha, hsa⟩
      · intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with hax | haA
        · rcases Finset.mem_insert.1 hb with hbx | hbA
          · rw [hax, hbx]
          · rw [hax] at hab
            exact absurd hab (hex b hbA)
        · rcases Finset.mem_insert.1 hb with hbx | hbA
          · rw [hbx] at hab
            exact absurd (cosetSet_symm_decomp hab) (hex a haA)
          · exact huniq a haA b hbA hab

end CosetDecomp

theorem eq_sum_coset_indicators : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (φ : (Fin t → k) → Z) (c : k), c ≠ 0 → HasCompactSupport φ → (∀ o ∈ Lc t c, ∀ v, φ (v + o.toAdd) = φ v) → ∃ A : Finset (Fin t → k), ∀ v, φ v = ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => φ a) v := by
  intro k _ _ _ _ t Z _ _ φ c _ hφ hinv
  classical
  have hval : ∀ a v, v ∈ cosetSet t c a → φ v = φ a := by
    intro a v hv
    have := hinv (Multiplicative.ofAdd (v - a)) hv a
    simpa using this
  have hopen : ∀ a, IsOpen (cosetSet t c a) := by
    intro a
    open ValuativeRel in
    have e : cosetSet t c a = ⋂ j, (fun v : Fin t → k => c * (v j - a j)) ⁻¹' ((𝒪[k] : Subring k) : Set k) := by
      ext v
      simp only [Set.mem_iInter, Set.mem_preimage]
      exact Iff.rfl
    rw [e]
    exact isOpen_iInter_of_finite fun j => (SplitWeil.isOpen_int k).preimage (by fun_prop)
  obtain ⟨S, hS⟩ := hφ.elim_finite_subcover (fun a : tsupport φ => cosetSet t c a) (fun a => hopen a)
    (fun v hv => Set.mem_iUnion.2 ⟨⟨v, hv⟩, self_mem_cosetSet_decomp t c v⟩)
  obtain ⟨A, hAcov, hAuniq⟩ := exists_coset_reps t c (S.image Subtype.val)
  refine ⟨A, fun v => ?_⟩
  by_cases hv : ∃ a ∈ A, v ∈ cosetSet t c a
  · obtain ⟨a, ha, hva⟩ := hv
    rw [Finset.sum_eq_single a]
    · rw [Set.indicator_of_mem hva]
      exact hval a v hva
    · intro b hb hba
      rw [Set.indicator_of_notMem]
      intro hvb
      exact hba (hAuniq b hb a ha (cosetSet_trans_decomp (cosetSet_symm_decomp hvb) hva))
    · intro haA
      exact absurd ha haA
  · push_neg at hv
    rw [Finset.sum_eq_zero]
    · by_contra hne
      have hvs : v ∈ tsupport φ := subset_tsupport _ hne
      obtain ⟨s, hsS, hvs'⟩ := Set.mem_iUnion₂.1 (hS hvs)
      obtain ⟨a, ha, hsa⟩ := hAcov s (Finset.mem_image_of_mem _ hsS)
      exact hv a ha (cosetSet_trans_decomp hvs' hsa)
    · intro a ha
      exact Set.indicator_of_notMem (hv a ha) _

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

theorem volume_cosetSet_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k), c ≠ 0 → (((μ (cosetSet t c 0)).toReal : ℝ) : ℂ) ≠ 0 := by
  intro k _ _ _ _ t _ _ μ _ c hc
  have h0 : (0 : Fin t → k) ∈ cosetSet t c 0 := by
    show Multiplicative.ofAdd ((0 : Fin t → k) - 0) ∈ Lc t c
    rw [sub_zero, ofAdd_zero]
    exact one_mem _
  have hpos : 0 < μ (cosetSet t c 0) := (isClopen_cosetSet t c 0).isOpen.measure_pos μ ⟨0, h0⟩
  have hfin : μ (cosetSet t c 0) < ⊤ := (isCompact_cosetSet t hc 0).measure_lt_top
  rw [Complex.ofReal_ne_zero]
  exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.exists_theta_kernel_eq_filtration_one : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), ∃ θ : A.Acr n →+* A.Un n, (∀ x : A.W, θ (A.toAcr n x) = Ideal.Quotient.mk _ (A.th x)) ∧ RingHom.ker θ = A.Fil n 1 := by
  first | exact @GlobalTheory.CompanionTheory.PerfectAlg.exists_theta_mod | exact GlobalTheory.CompanionTheory.PerfectAlg.exists_theta_mod | (intros; apply GlobalTheory.CompanionTheory.PerfectAlg.exists_theta_mod <;> assumption)
end
