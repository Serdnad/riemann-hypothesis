module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle014
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle072
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle097
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle033
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst

@[expose] public section

section

noncomputable section

namespace GlobalTheory.HolEval

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

section Ring

variable {K : Type} [Field K] {σ : K →+* ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {A : Type} [CommRing A] [Algebra K A]

theorem toC_mul (x y : CAt σ) : _root_.Formalism.L2.PjFree.toC (x * y) = _root_.Formalism.L2.PjFree.toC x * _root_.Formalism.L2.PjFree.toC y := rfl
theorem toC_add (x y : CAt σ) : _root_.Formalism.L2.PjFree.toC (x + y) = _root_.Formalism.L2.PjFree.toC x + _root_.Formalism.L2.PjFree.toC y := rfl
theorem toC_one : _root_.Formalism.L2.PjFree.toC (1 : CAt σ) = 1 := rfl

def holSub (B : Set V) (k : V → (A →ₐ[K] CAt σ)) : Subalgebra K A where
  carrier := {t | DifferentiableOn ℂ (fun b => _root_.Formalism.L2.PjFree.toC (k b t)) B}
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, map_mul, toC_mul] at *
    exact hx.mul hy
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, map_add (f := _), toC_add] at *
    exact hx.add hy
  algebraMap_mem' := fun r => by
    simp only [Set.mem_setOf_eq, AlgHom.commutes]
    exact differentiableOn_const _

theorem mem_holSub {B : Set V} {k : V → (A →ₐ[K] CAt σ)} {t : A} :
    t ∈ holSub B k ↔ DifferentiableOn ℂ (fun b => _root_.Formalism.L2.PjFree.toC (k b t)) B := Iff.rfl

theorem inv_mem_holSub {B : Set V} {k : V → (A →ₐ[K] CAt σ)} {d x : A} (hx : x ∈ holSub B k)
    (h : d * x = 1) : d ∈ holSub B k := by
  rw [mem_holSub] at hx ⊢
  have key : ∀ b, _root_.Formalism.L2.PjFree.toC (k b d) * _root_.Formalism.L2.PjFree.toC (k b x) = 1 := fun b => by
    rw [← toC_mul, ← map_mul, h, map_one, toC_one]
  have hne : ∀ b, _root_.Formalism.L2.PjFree.toC (k b x) ≠ 0 := fun b hb => by
    have h1 := key b
    rw [hb, mul_zero] at h1
    exact zero_ne_one h1
  have heq : (fun b => _root_.Formalism.L2.PjFree.toC (k b d)) = fun b => (_root_.Formalism.L2.PjFree.toC (k b x))⁻¹ :=
    funext fun b => eq_inv_of_mul_eq_one_left (key b)
  rw [heq]
  exact hx.inv fun b _ => hne b

theorem det_mem {n : ℕ} (A' : Subalgebra K A) (X : Matrix (Fin n) (Fin n) A) (h : ∀ i j, X i j ∈ A') :
    X.det ∈ A' := by
  rw [Matrix.det_apply]
  refine sum_mem fun e _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => h _ _) _

private theorem evR_eq_of_frMap {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (hS : Out.SecBaseChangeSt) {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c w n)
    {S : Type} [CommRing S] [Algebra c.F S] (q : TRing c.F) (κ : q.R →ₐ[c.F] S) (u : FrPt Xo c q.R)
    (x : FrPt Xo c S) (h : FrMap κ u x) : evR Xo c f x = κ (f q u) := by
  have hW := (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.2.1
  unfold sec secW at hf
  obtain ⟨hn, -⟩ := hf
  unfold evR evalAt
  split_ifs with hT
  · exact hW f hn S _ q _ κ _ u x hT.choose_spec.choose_spec.choose_spec h
  · exact absurd ⟨q, κ, u, h⟩ hT

end Ring

theorem differentiableOn_evR : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (p : TRing c.F) (y₀ : FrPt Xo c p.R) (ψ : V → (p.R →ₐ[c.F] CAt σ)) (z y : V → FrPt Xo c (CAt σ)) (G : V → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : V → CAt σ), (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b)) → (∀ t, DifferentiableOn ℂ (fun b => _root_.Formalism.L2.PjFree.toC (ψ b t)) B) → (∀ τ i j, DifferentiableOn ℂ (fun b => _root_.Formalism.L2.PjFree.toC (G b τ i j)) B) → DifferentiableOn ℂ (fun b => _root_.Formalism.L2.PjFree.toC (a b)) B → ∀ w n, ∀ f ∈ sec Xo c w n, DifferentiableOn ℂ (fun b => _root_.Formalism.L2.PjFree.toC (evR Xo c f (y b))) B := by
  intro hS E _ _ _ H Dw l Xo c σ V _ _ B p y₀ ψ z y G a hzy hψ hG ha w n f hf
  obtain ⟨A, π, X, s, u, hU⟩ := GlobalTheory.T.exists_universalFrame_testRing hS E H Dw l Xo c p y₀
  obtain ⟨hFR, u₀, hπ, hch⟩ := hU
  have hk : ∀ b ∈ B, ∃ kk : A.R →ₐ[c.F] CAt σ,
      kk.comp π = ψ b ∧ (∀ τ, (X τ).map kk = G b τ) ∧ kk (s : A.R) = a b := by
    intro b hb
    obtain ⟨-, hc⟩ := hzy b hb
    obtain ⟨hex, huniq⟩ := GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) (z b) (y b)
    obtain ⟨g, a', hdet, hc'⟩ := hex hc.1
    obtain ⟨hg, ha'⟩ := huniq _ _ _ _ hc hc'
    obtain ⟨kk, ⟨h1, h2, h3⟩, -⟩ := hFR.2 (CAt σ) (ψ b) g a' hdet
    exact ⟨kk, h1, fun τ => (h2 τ).trans (congrFun hg τ).symm, h3.trans ha'.symm⟩
  rcases B.eq_empty_or_nonempty with hB | ⟨b₀, hb₀⟩
  · rw [hB]
    exact differentiableOn_empty
  have : Nonempty (A.R →ₐ[c.F] CAt σ) := ⟨(hk b₀ hb₀).choose⟩
  choose! kk hkk using hk
  have hX : ∀ τ i j, X τ i j ∈ holSub B kk := by
    intro τ i j
    rw [mem_holSub]
    refine (hG τ i j).congr fun b hb => ?_
    show _root_.Formalism.L2.PjFree.toC (kk b (X τ i j)) = _root_.Formalism.L2.PjFree.toC (G b τ i j)
    rw [← (hkk b hb).2.1 τ]
    rfl
  have hs : (s : A.R) ∈ holSub B kk := by
    rw [mem_holSub]
    refine ha.congr fun b hb => ?_
    show _root_.Formalism.L2.PjFree.toC (kk b (s : A.R)) = _root_.Formalism.L2.PjFree.toC (a b)
    rw [(hkk b hb).2.2]
  have hA' := GlobalTheory.T.universalFrameRing_subalgebra_eq_top c.F (E →+* ℂ) (fun τ => Dw.mult τ) p.R A.R π X s hFR (holSub B kk)
    (fun t => by
      rw [mem_holSub]
      refine (hψ t).congr fun b hb => ?_
      show _root_.Formalism.L2.PjFree.toC (kk b (π t)) = _root_.Formalism.L2.PjFree.toC (ψ b t)
      rw [← (hkk b hb).1]
      rfl)
    hX hs (inv_mem_holSub hs (Units.inv_mul s))
    (fun τ => by
      obtain ⟨v, hv⟩ := hFR.1 τ
      refine ⟨((v⁻¹ : (A.R)ˣ) : A.R), inv_mem_holSub (det_mem _ (X τ) (hX τ)) ?_, ?_⟩ <;>
        · rw [← hv]
          exact Units.inv_mul v)
  have he : f A u ∈ holSub B kk := by
    rw [hA']
    exact Algebra.mem_top
  rw [mem_holSub] at he
  refine he.congr fun b hb => ?_
  show _root_.Formalism.L2.PjFree.toC (evR Xo c f (y b)) = _root_.Formalism.L2.PjFree.toC (kk b (f A u))
  congr 1
  apply evR_eq_of_frMap hS hf A (kk b) u (y b)
  obtain ⟨hm, hc⟩ := hzy b hb
  have hb1 : FrMap (kk b) u₀ (z b) :=
    ((GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).2.1 p.R A.R (CAt σ) π (kk b) y₀ u₀ (z b) hπ).2
      (by rw [(hkk b hb).1]; exact hm)
  apply (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c A.R (CAt σ) (kk b) u₀ u (z b) (y b) X s hch hb1).2
  have e1 : (fun τ => (X τ).map (kk b)) = G b := funext (hkk b hb).2.1
  rw [e1, (hkk b hb).2.2]
  exact hc

end GlobalTheory.HolEval
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem test_value_eq_const_mul_reading : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : _root_.Formalism.L2.PjFree.Unf Xo c σ r), IsUnf U → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ), ∃ (k : U.Comp) (x : (U.X k).dom) (u : ℂ), ∀ f ∈ sec Xo c a n, _root_.Formalism.L2.PjFree.toC (ψ (f p y)) = u * _root_.Formalism.L2.PjFree.rdU U f k x.1 := by
  intro hSB E _ _ _ H Dw l Xo c σ r U hU a n p y ψ
  obtain ⟨-, -, hWD, -, -, -, hBor⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hSB E H Dw l Xo c
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hSB E H Dw l Xo c p.R (CAt σ) ψ y
  obtain ⟨-, -, hcov, -⟩ := hU
  obtain ⟨k, x, t, ht⟩ := hcov z
  have hred : _root_.IsReduced (CAt σ) := by
    unfold CAt
    exact isReduced_of_noZeroDivisors
  refine ⟨k, x, _root_.Formalism.L2.PjFree.toC (wchar (ex Dw a n) t), ?_⟩
  intro f hf
  have hf' := hf
  unfold sec secW at hf'
  obtain ⟨hN, -⟩ := hf'
  have h1 : evR Xo c f z = ψ (f p y) := by
    have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, ψ, y, hz⟩
    unfold evR evalAt
    rw [dif_pos hT]
    exact hWD f hN _ _ _ _ _ _ _ _ hT.choose_spec.choose_spec.choose_spec hz
  have h2 : _root_.Formalism.L2.PjFree.rdU U f k x.1 = _root_.Formalism.L2.PjFree.toC (evR Xo c f (U.un k x)) := by
    unfold _root_.Formalism.L2.PjFree.rdU
    exact dif_pos x.2
  have h3 := hBor (CAt σ) hred a n f hf t (U.un k x) z ht
  rw [← h1, h2, h3]
  rfl

end GlobalTheory.FrameUnif
end
