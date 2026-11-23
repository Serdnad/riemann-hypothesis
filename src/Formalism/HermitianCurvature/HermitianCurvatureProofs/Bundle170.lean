module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle158
import Formalism.FormalDegreeBessel.FinalG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatQMinOp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

noncomputable section

section defs

variable (k r : ℕ)

def colsV (t : Fin (k + 1)) : Fin (r + k) → Fin (2 * r + k + 1) :=
  fun j => ⟨if j.val < t.val then r + j.val else r + j.val + 1, by have := j.isLt; have := t.isLt; split_ifs <;> omega⟩

def rowV (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1))
    (p : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  fun q =>
    if h : p.val < r then herm (Hpk k r) (g *ᵥ bvec q) (bvec (eI k r ⟨p.val, h⟩))
    else if h2 : p.val = r then herm (Hpk k r) (g *ᵥ bvec q) z
    else if q = J ⟨p.val - r - 1, by have := p.isLt; omega⟩ then 1 else 0

def alJ (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1)) : ℂ :=
  (Matrix.of fun p q => rowV k r z g J p q).det

def rvhatOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => ∑ t : Fin (k + 1), ∑ J ∈ jSetR k r,
    (((-1 : ℂ) ^ (t : ℕ)) * z' (wI k r t) * alJ k r z g J) •
      qminorOp (Q.EH k r) J (colsV k r t) (Q.uC k r (Fin.last r) Y - 1) f g

end defs

def JDRRadM : Prop :=
  ∀ k r : ℕ, ∃ ε : ℂ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      Q.resG k r (Fin.last r) (fun x => ε • rvhatOp k r z z' Y J x) c g =
        rhvGrp k r z z' Y (Q.resG k r (Fin.last r) J) c g

def JDRRealInvM : Prop :=
  ∀ (ε : ℂ) (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧
        ∀ (U : Set (Q.Mx S.G.k S.G.r)) (F : Q.Mx S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsOpen U →
          Q.SmoothLev S.G.k S.G.r 0 U F → ∀ g ∈ Q.Glev S.G.k S.G.r 0 ∩ U,
            B.opApply Θ F g = ε • rvhatOp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) F g

private theorem isDom_OmP_levTower_base {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f) :
    Q.IsDom S.G.k S.G.r (T v).base.z (T v).base.z' 0 (OmP S T v) := by
  refine ⟨?_, ?_⟩
  · have hD : ∀ l, Continuous fun g : Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin (2 * S.G.r + S.G.k + 1)) ℂ =>
        Formalism.QuantumDeterminants.Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g l := by
      intro l
      unfold Formalism.QuantumDeterminants.Dmin Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm
      simp only [Matrix.mulVec, dotProduct]
      fun_prop
    have hG : Continuous fun g : Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin (2 * S.G.r + S.G.k + 1)) ℂ =>
        Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g := by
      unfold Formalism.QuantumDeterminants.Gf
      exact (Complex.continuous_normSq.comp (hD _)).sub
        (continuous_const.mul (Complex.continuous_normSq.comp (hD _)))
    unfold OmP
    rw [Set.setOf_and, Set.setOf_forall]
    exact (isOpen_lt continuous_const hG).inter
      (isOpen_iInter_of_finite fun a => isOpen_ne_fun (hD _) continuous_const)
  · rintro g ⟨-, hgD⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hs : h * m ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T v).base.z := ⟨h, hh, m, hm.1, rfl⟩
    have hs' : h' * m' ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T v).base.z' := ⟨h', hh', m', hm'.1, rfl⟩
    refine ⟨?_, fun a => ?_⟩
    · rw [Formalism.QuantumDeterminants.gInv _ _ _ _ (T v).base.z_mem (T v).base.z'_mem _ hs _ hs']
      exact hgD.1
    · rw [Formalism.QuantumDeterminants.dInv _ _ _ _ (T v).base.z_mem (T v).base.z'_mem _ hs _ hs']
      exact hgD.2 a

private theorem w1_mem_UH_Hpk_of_ne_zero {k r : ℕ} (l : Fin r) (x : ℂ) (hx : x ≠ 0) :
    Q.w1 k r l x ∈ Formalism.QuantumDeterminants.UH (Hpk k r) := by
  have hl := l.isLt
  have hes : eI k r l ≠ esI k r l := by
    simp only [eI, esI, ne_eq, Fin.ext_iff]
    omega
  have hcol : ∀ j q, Q.w1 k r l x j q =
      if j = (if q = eI k r l then esI k r l else if q = esI k r l then eI k r l else q) then
        (if q = eI k r l then x else if q = esI k r l then (star x)⁻¹ else 1) else 0 := by
    intro j q
    simp only [Q.w1]
    by_cases hq1 : q = eI k r l <;> by_cases hq2 : q = esI k r l <;>
      by_cases hj1 : j = eI k r l <;> by_cases hj2 : j = esI k r l <;> simp_all <;>
      (intro h; first | exact absurd h.symm hq1 | exact absurd h.symm hq2)
  have hHe : ∀ p, p ≠ esI k r l → Hpk k r p (eI k r l) = 0 := by
    intro p hp
    rw [Ne, Fin.ext_iff] at hp
    simp only [esI] at hp
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHs : ∀ p, p ≠ eI k r l → Hpk k r p (esI k r l) = 0 := by
    intro p hp
    rw [Ne, Fin.ext_iff] at hp
    simp only [eI] at hp
    simp only [Hpk, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHe' : ∀ q, q ≠ esI k r l → Hpk k r (eI k r l) q = 0 := by
    intro q hq
    rw [Ne, Fin.ext_iff] at hq
    simp only [esI] at hq
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHs' : ∀ q, q ≠ eI k r l → Hpk k r (esI k r l) q = 0 := by
    intro q hq
    rw [Ne, Fin.ext_iff] at hq
    simp only [eI] at hq
    simp only [Hpk, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHes : Hpk k r (eI k r l) (esI k r l) = 1 := by
    have h1 : (l : ℕ) + (2 * r + k - l) = 2 * r + k := by omega
    simp [Hpk, eI, esI, hl, h1]
  have hHse : Hpk k r (esI k r l) (eI k r l) = 1 := by
    have h2 : ¬ (2 * r + k - (l : ℕ) < r) := by omega
    have h3 : 2 * r + k - (l : ℕ) + l = 2 * r + k := by omega
    simp [Hpk, eI, esI, hl, h2, h3]
  show (Q.w1 k r l x)ᴴ * Hpk k r * Q.w1 k r l x = Hpk k r
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol, apply_ite star, star_zero, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hp1 : p = eI k r l <;> by_cases hp2 : p = esI k r l <;>
    by_cases hq1 : q = eI k r l <;> by_cases hq2 : q = esI k r l <;>
    first
    | exact absurd (hp1.symm.trans hp2) hes
    | exact absurd (hq1.symm.trans hq2) hes
    | simp [hp1, hp2, hq1, hq2, hes, hes.symm, hHe, hHs, hHe', hHs', hHes, hHse, hx]

private theorem mul_mem_UH_of_mem_of_mem {n : ℕ} {H g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH H)
    (hh : h ∈ Formalism.QuantumDeterminants.UH H) : g * h ∈ Formalism.QuantumDeterminants.UH H := by
  have hg' : gᴴ * H * g = H := hg
  have hh' : hᴴ * H * h = H := hh
  show (g * h)ᴴ * H * (g * h) = H
  rw [Matrix.conjTranspose_mul,
    show hᴴ * gᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h by simp only [Matrix.mul_assoc], hg', hh']

private theorem wCell_mem_UH_Hpk_of_ne_zero {k r : ℕ} (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (i : Fin (r + 1)) :
    Q.wCell k r i c ∈ Formalism.QuantumDeterminants.UH (Hpk k r) := by
  unfold Q.wCell
  induction ((List.finRange r).filter fun a => a.val < i.val) with
  | nil =>
    show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem_UH_of_mem_of_mem (w1_mem_UH_Hpk_of_ne_zero a (c a) (hc a)) ih

private theorem wCell_last_mul_mem_Glev_zero {k r : ℕ} (c : Fin r → ℂ) (hc : c ∈ OmX r) (g : Q.Mx k r)
    (hg : g ∈ Q.Glev k r (Fin.last r)) : Q.wCell k r (Fin.last r) c * g ∈ Q.Glev k r 0 :=
  ⟨mul_mem_UH_of_mem_of_mem (wCell_mem_UH_Hpk_of_ne_zero c hc _) hg.1, fun a ha => absurd ha (by simp)⟩

theorem jDRGrpM_of_parts (hR : JDRRadM) (hI : JDRRealInvM) : JDRGrpM := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨ε, hε⟩ := hR S.G.k S.G.r
  obtain ⟨Θ, hP, hC, hA⟩ := hI ε Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  refine ⟨Θ, hP, hC, ?_⟩
  intro J hJ c hc g hg hx
  have key := hε (Wp (S.pl v)) (Wq (S.pl v)) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'
    (OmP S T v) (y : ℂ) (T v).base.z_mem (T v).base.z'_mem (isDom_OmP_levTower_base S T v) J hJ c hc g hg hx
  rw [← key]
  have hx0 := wCell_last_mul_mem_Glev_zero c hc g hg
  obtain ⟨U, F, hU, hxU, hF, hFJ⟩ := hJ.1 _ ⟨hx0, hx⟩
  have hS : Q.SmoothLev S.G.k S.G.r 0 U J := fun g₀ hg₀ => ⟨U, F, hU, hg₀.2, hF, hFJ⟩
  have := hA U J hU hS _ ⟨hx0, hxU⟩
  simp only [Q.resG, this]

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def JDRInvFn : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Y : ℂ) (p : B.SS k r), D.inSS p →
    ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((r + k : ℕ) : ℕ∞) (B.GV k r) F →
      ∀ g ∈ B.GPos D, rhatOp k r D.z D.z' Y (B.rho D p F) g = B.rho D p (rhatOp k r D.z D.z' Y F) g

section poly

open Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {k r : ℕ}

theorem ri_mul_left {a : ℕ} {P : Q.Mx k r → ℂ} (c : ℂ) (h : U.IsPolyDeg a P) :
    U.IsPolyDeg a (fun g => c * P g) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨MvPolynomial.C c * q, ?_, fun g => by simp [hP g]⟩
  calc (MvPolynomial.C c * q).totalDegree ≤ (MvPolynomial.C c).totalDegree + q.totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ a := by simp [hq]

theorem ri_mul_right {a : ℕ} {P : Q.Mx k r → ℂ} (h : U.IsPolyDeg a P) (c : ℂ) :
    U.IsPolyDeg a (fun g => P g * c) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨q * MvPolynomial.C c, ?_, fun g => by simp [hP g]⟩
  calc (q * MvPolynomial.C c).totalDegree ≤ q.totalDegree + (MvPolynomial.C c).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ a := by simp [hq]

theorem ri_ginv (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g => (ginvH k r g *ᵥ v) p) := by
  have hdeg : ∀ (a : ℂ) (i : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))),
      (MvPolynomial.C a * MvPolynomial.X i : MvPolynomial _ ℂ).totalDegree ≤ 1 := fun a i =>
    (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  refine ⟨∑ c, ∑ b, ∑ a, MvPolynomial.C (Hpk k r p a * Hpk k r b c * v c) * MvPolynomial.X (Sum.inr (b, a)),
    ?_, fun g => ?_⟩
  · exact (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ =>
      (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun b _ =>
        (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun a _ => hdeg _ _)))
  · set_option synthInstance.maxHeartbeats 100000 in
    simp only [ginvH, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Sum.elim_inr, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring

theorem ri_colR (z : Fin (2 * r + k + 1) → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (q p : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g => colR k r z g J q p) := by
  by_cases h1 : (q : ℕ) < r
  · simp only [colR, dif_pos h1]
    exact ri_ginv _ p
  · by_cases h2 : (q : ℕ) = r
    · simp only [colR, dif_neg h1, dif_pos h2]
      exact ri_ginv z p
    · refine ⟨MvPolynomial.C (colR k r z 0 J q p), by simp, fun g => ?_⟩
      simp [colR, h1, h2]

theorem ri_beJ (z : Fin (2 * r + k + 1) → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) :
    U.IsPolyDeg (2 * r + k + 1) (fun g => beJ k r z g J) := by
  choose Pq hPdeg hPev using fun q p => ri_colR (k := k) (r := r) z J q p
  refine ⟨(Matrix.of fun p q => Pq q p).det, ?_, fun g => ?_⟩
  · rw [Matrix.det_apply']
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun σ _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h0 : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial
        ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) ℂ)).totalDegree = 0 := by
      have hc : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial
          ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) ℂ) =
          MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℂ) := by simp
      rw [hc]
      exact MvPolynomial.totalDegree_C _
    rw [h0, zero_add]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    calc ∑ i, (Matrix.of (fun p q => Pq q p) (σ i) i).totalDegree ≤ ∑ _i : Fin (2 * r + k + 1), 1 :=
          Finset.sum_le_sum fun i _ => hPdeg _ _
      _ = 2 * r + k + 1 := by simp
  · show (Matrix.of fun p q => colR k r z g J q p).det = _
    rw [RingHom.map_det]
    congr 1
    ext p q
    simp [RingHom.mapMatrix_apply, hPev]

end poly

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem ri_order_le {t κ : ℕ} : ∀ Θ : B.DiffOp k r Wp Wq, PolyOp t κ Θ → B.opOrder Θ ≤ t
  | [], _ => by simp [B.opOrder]
  | Tm :: Θ, h => by
    have h1 := (h Tm (List.mem_cons_self ..)).1
    have h2 := ri_order_le Θ fun T' hT' => h T' (List.mem_cons_of_mem _ hT')
    unfold B.opOrder at h2 ⊢
    simp only [List.map_cons, List.foldr_cons]
    exact max_le h1 h2

def riCat (Θs : Fin (k + 1) → B.DiffOp k r Wp Wq) : List (Fin (k + 1)) → B.DiffOp k r Wp Wq
  | [] => []
  | i :: l => Θs i ++ riCat Θs l

theorem riCat_poly {Θs : Fin (k + 1) → B.DiffOp k r Wp Wq} {t κ : ℕ} (h : ∀ i, PolyOp t κ (Θs i)) :
    ∀ l, PolyOp t κ (riCat Θs l)
  | [] => fun T hT => absurd hT List.not_mem_nil
  | i :: l => QMinOp.polyOp_append (h i) (riCat_poly h l)

theorem riCat_apply (Θs : Fin (k + 1) → B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    ∀ l, B.opApply (riCat Θs l) F g = (l.map fun i => B.opApply (Θs i) F g).sum
  | [] => by simp [riCat, B.opApply]
  | i :: l => by rw [riCat, QMinOp.opApply_append, riCat_apply Θs F g l, List.map_cons, List.sum_cons]

private theorem foldr_max_eq_max_foldr_max_zero : ∀ (L : List ℕ) (x : ℕ), L.foldr max x = max (L.foldr max 0) x := by
  intro L
  induction L with
  | nil => intro x; simp
  | cons y L ih => intro x; simp only [List.foldr_cons]; rw [ih x, max_assoc]

theorem riCat_order {Θs : Fin (k + 1) → B.DiffOp k r Wp Wq} {t κ : ℕ} (h : ∀ i, PolyOp t κ (Θs i))
    (ho : ∀ i, B.opOrder (Θs i) = t) (i : Fin (k + 1)) (l : List (Fin (k + 1))) :
    B.opOrder (riCat Θs (i :: l)) = t := by
  have hle : B.opOrder (riCat Θs l) ≤ t := ri_order_le _ (riCat_poly h l)
  have h1 := ho i
  simp only [B.opOrder] at h1 hle
  simp only [riCat, B.opOrder, List.map_append, List.foldr_append]
  rw [foldr_max_eq_max_foldr_max_zero, h1]
  exact max_eq_left hle

theorem ri_real (z z' : Fin (2 * r + k + 1) → ℂ) (Y ε : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
        ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ε • rhatOp k r z z' Y F g := by
  have h : ∀ i : Fin (k + 1), ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
        ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ∑ J ∈ jSetR k r,
          (fun (J : Fin (r + k) → Fin (2 * r + k + 1)) (g : B.Mat k r) =>
            ε * (((-1 : ℂ) ^ (i : ℕ)) * herm (Hpk k r) (bvec (wI k r i)) z' * beJ k r z g J)) J g •
            qminorOp (Q.EH k r) (rowsR k r i) J (Q.uC k r 0 Y) F g := fun i =>
    QMinOp.qminOpRep (jSetR k r) (rowsR k r i) (fun J => J) _
      (fun J _ => ri_mul_left _ (ri_mul_left _ (ri_beJ z J))) _
  choose Θs hP hO hR using h
  refine ⟨riCat Θs (List.finRange (k + 1)), riCat_poly hP _, ?_, ?_⟩
  · have e : List.finRange (k + 1) = (0 : Fin (k + 1)) :: (List.finRange k).map Fin.succ := List.finRange_succ
    rw [e]
    exact riCat_order hP hO _ _
  · intro UU F hF g hgU hg
    rw [riCat_apply, ← Fin.sum_univ_def]
    simp only [rhatOp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hR i UU F hF g hgU hg]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [smul_smul]

end ops

theorem jDRRealInvP_of_inv (hI : JDRInvFn) : JDRRealInvP := by
  intro ε Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨Θ, hP, hO, hR⟩ := ri_real (Wp := Wp (S.pl v)) (Wq := Wq (S.pl v)) (T v).base.z (T v).base.z' (y : ℂ) ε
  have hn : 0 < 2 * S.G.r + S.G.k + 1 := by omega
  refine ⟨Θ, QMinOp.polyOp_mono hP (by omega) (Nat.le_mul_of_pos_left _ (by omega)), ?_, ?_⟩
  · intro p hp F hF g hg
    rw [hO] at hF
    have hgG : g ∈ B.GV S.G.k S.G.r := hg.1
    have hsg : B.sgs p g ∈ B.GV S.G.k S.G.r := Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group (T v).base hp hgG
    rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho (T v).base hp hF) g hgG hgG]
    have e2 : B.rho (T v).base p (B.opApply Θ F) g =
        B.rho (T v).base p (fun x => ε • rhatOp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) F x) g := by
      simp only [B.rho]
      rw [hR _ _ hF _ hsg hsg]
    rw [e2, hI S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base (y : ℂ) p hp F hF g hg]
    simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  · intro U F hU hF g hg
    have hgG : g ∈ B.GV S.G.k S.G.r := by simpa [Q.Glev] using hg.1
    refine hR (Q.Glev S.G.k S.G.r 0 ∩ U) F ?_ g hg hgG
    intro g₀ hg₀
    obtain ⟨U', F', hU', hg₀U, hc, he⟩ := hF g₀ hg₀
    refine ⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun x hx hxG => he x hx ?_⟩
    simpa [Q.Glev] using hxG

end

end Formalism.FourierDecayAlt.P.CutMP
end
