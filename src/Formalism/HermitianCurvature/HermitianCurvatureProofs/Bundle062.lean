module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle053
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorSumCounterexample
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle051
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle055
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle054
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ENNReal

noncomputable section

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def FamilyDerivativeExpansion (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) : Prop :=
  ∃ (Par : Type) (_ : AddCommGroup Par) (fam : Par → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (lam : Par)
    (N1 Ninf : Par → ℕ) (c0 q0 : ℕ) (Gam : ℝ),
    fam lam = f ∧ 0 ≤ Gam ∧
    (∀ x y, N1 (x + y) ≤ N1 x + N1 y) ∧ (∀ x y, Ninf (x + y) ≤ Ninf x + Ninf y) ∧ N1 0 = 0 ∧ Ninf 0 = 0 ∧
    (∀ μ, N1 (μ - lam) + c0 ≤ q0 → ∃ a : Par →₀ ℂ,
      (fun c => (D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det • p.V (fam μ) (TBB.bigPt P.r c)) =
          a.sum (fun ν z => z • fun c => p.V (fam (μ + ν)) (TBB.bigPt P.r c)) ∧
        (a.sum fun _ z => ‖z‖) ≤ Gam ^ (P.r + 1) ∧ ∀ ν ∈ a.support, N1 ν ≤ P.r + 1 ∧ Ninf ν ≤ 1) ∧
    (P.r + 1) * a₁ + c0 ≤ q0 ∧
    Gam ^ (P.r + 1) ≤ b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2) ∧
    (∀ μ, TBB.jN2 p (fam μ) ≤ TBB.jN2 p f) ∧
    (∀ μ, AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fam μ) (P.r + 1) [] (TBB.bigPt P.r c)))

theorem big_cell_expansion_of_subadditive (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ Gam : ℝ) (a₁ : ℕ)
    (hb : 0 ≤ b) (hGam : 0 ≤ Gam) (Par : Type) [AddCommGroup Par] (fam : Par → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (lam : Par) (hf : fam lam = f) (N1 Ninf : Par → ℕ) (c0 q0 : ℕ)
    (hN1 : ∀ x y, N1 (x + y) ≤ N1 x + N1 y) (hNinf : ∀ x y, Ninf (x + y) ≤ Ninf x + Ninf y)
    (hN10 : N1 0 = 0) (hNinf0 : Ninf 0 = 0)
    (hstep : ∀ μ, N1 (μ - lam) + c0 ≤ q0 → ∃ a : Par →₀ ℂ,
      (fun c => (D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det • p.V (fam μ) (TBB.bigPt P.r c)) =
          a.sum (fun ν z => z • fun c => p.V (fam (μ + ν)) (TBB.bigPt P.r c)) ∧
        (a.sum fun _ z => ‖z‖) ≤ Gam ^ (P.r + 1) ∧ ∀ ν ∈ a.support, N1 ν ≤ P.r + 1 ∧ Ninf ν ≤ 1)
    (hrange : (P.r + 1) * a₁ + c0 ≤ q0)
    (hGb : Gam ^ (P.r + 1) ≤ b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2))
    (hnorm : ∀ μ, TBB.jN2 p (fam μ) ≤ TBB.jN2 p f)
    (hmeas : ∀ μ, AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fam μ) (P.r + 1) [] (TBB.bigPt P.r c))) :
    BigCellDerivativeExpansion p f b C₃ a₁ := by
  subst hf
  intro a ha
  let Dop : Unit → Module.End ℂ ((Fin (P.r + 1) → ℂ) → (Wq →L[ℂ] Wp)) := fun _ =>
    { toFun := fun φ c => (D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det • φ c
      map_add' := fun φ ψ => by funext c; simp only [Pi.add_apply, smul_add]
      map_smul' := fun z φ => by
        funext c; simp only [Pi.smul_apply, RingHom.id_apply]; rw [smul_comm] }
  have hDop : ∀ (n : ℕ) (φ : (Fin (P.r + 1) → ℂ) → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ),
      ((Dop ()) ^ n) φ c = (D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det ^ n • φ c := by
    intro n
    induction n with
    | zero => intro φ c; simp
    | succ n ih =>
      intro φ c
      rw [pow_succ]
      show ((Dop ()) ^ n) ((Dop ()) φ) c = _
      rw [ih, pow_succ, mul_smul]
      rfl
  have key := Formalism.HermitianLatticeCounting.P.iterated_sum_bound_holds ((Fin (P.r + 1) → ℂ) → (Wq →L[ℂ] Wp)) Par Unit
    (fun μ c => p.V (fam μ) (TBB.bigPt P.r c)) Dop (fun _ => P.r + 1) N1 Ninf lam Gam c0 q0 hGam hN1 hNinf
    hN10 hNinf0 (fun μ _ hμ => hstep μ hμ) lam (List.replicate a ()) (by
      simp only [sub_self, hN10, List.map_replicate, List.sum_replicate, smul_eq_mul, zero_add]
      nlinarith [Nat.mul_le_mul_right (P.r + 1) ha])
  obtain ⟨A, hA, hAn, -⟩ := key
  let e := A.support.equivFin
  refine ⟨A.support.card, fun i => fam (lam + (e.symm i).1), fun i => A (e.symm i).1, ?_,
    fun i => hnorm _, fun i => hmeas _, ?_⟩
  · have h1 : ∑ i : Fin A.support.card, ‖A (e.symm i).1‖ = A.sum fun _ z => ‖z‖ := by
      rw [Finsupp.sum, ← Finset.sum_coe_sort A.support]
      exact e.symm.sum_comp (fun x : A.support => ‖A x.1‖)
    rw [h1]
    refine hAn.trans ?_
    simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]
    rw [pow_mul']
    have hGp : 0 ≤ Gam ^ (P.r + 1) := pow_nonneg hGam _
    calc (Gam ^ (P.r + 1)) ^ a ≤ (b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2)) ^ a := by
          first
            | exact pow_le_pow_left₀ hGp hGb a
            | exact pow_le_pow_left hGp hGb a
      _ = b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * (a : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
  · intro c _ _
    have h2 := congrFun hA c
    rw [List.map_replicate, List.prod_replicate, hDop, Finsupp.sum, Finset.sum_apply] at h2
    simp only [Pi.smul_apply] at h2
    refine h2.trans ?_
    rw [← Finset.sum_coe_sort A.support]
    exact (e.symm.sum_comp (fun x : A.support => A x.1 • p.V (fam (lam + x.1)) (TBB.bigPt P.r c))).symm

theorem big_cell_expansion_of_family (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) (hb : 0 ≤ b)
    (h : FamilyDerivativeExpansion p f b C₃ a₁) : BigCellDerivativeExpansion p f b C₃ a₁ := by
  obtain ⟨Par, _, fam, lam, N1, Ninf, c0, q0, Gam, hf, hGam, hN1, hNinf, hN10, hNinf0, hstep, hrange, hGb, hnorm,
    hmeas⟩ := h
  exact big_cell_expansion_of_subadditive p f b C₃ Gam a₁ hb hGam Par fam lam hf N1 Ninf c0 q0 hN1 hNinf hN10 hNinf0 hstep hrange hGb
    hnorm hmeas

end place

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

abbrev HS (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : Type :=
  PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)

abbrev HT (I : Type) [Fintype I] (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : Type :=
  PiLp 2 (fun _ : I => HS Wp Wq)

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]

def vecT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (Q : C.LPt) : HT I Wp Wq :=
  WithLp.toLp 2 (fun i => ((√(c i) * omT p N Q : ℝ) : ℂ) • L i (p.V (Fi i) Q))

theorem vecT_apply (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (Q : C.LPt) (i : I) :
    vecT p N c Fi L Q i = ((√(c i) * omT p N Q : ℝ) : ℂ) • L i (p.V (Fi i) Q) := rfl

theorem inner_vecT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (Q Q' : C.LPt) :
    ⟪vecT p N c Fi L Q, vecT p N c Fi L Q'⟫_ℂ =
      ∑ i, (c i : ℂ) * ⟪(omT p N Q : ℂ) • L i (p.V (Fi i) Q), (omT p N Q' : ℂ) • L i (p.V (Fi i) Q')⟫_ℂ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : ((√(c i) : ℝ) : ℂ) * ((√(c i) : ℝ) : ℂ) = (c i : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hc i)]
  rw [vecT_apply, vecT_apply, inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal, Complex.ofReal_mul, map_mul]
  rw [← hs]
  ring

def utT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (s : ℕ) (h : C.LPt) (x D : ℂ) : HT I Wp Wq :=
  ((‖x‖ ^ (s - 1) : ℝ) : ℂ) • vecT p N c Fi L (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)])

def btT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (s : ℕ) (h : C.LPt) (u : ℂ) : HT I Wp Wq :=
  if u = 0 then 0 else ((Real.pi ^ (s - 1) * ((s : ℝ) * ‖u‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • vecT p N c Fi L (h ++ [(s, u)])

end place

structure VecHyp {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) : Prop where
  hc : ∀ i, 0 ≤ c i
  hFi : ∀ i, KB.CptCoef p.T.base (Fi i)
  gram : ∀ Q Q' : C.LPt, TBB.NP p nn F (P.r + 1) w Q Q' =
    ∑ i, (c i : ℂ) * ⟪(omT p w.length Q' : ℂ) • L i (p.V (Fi i) Q'), (omT p w.length Q : ℂ) • L i (p.V (Fi i) Q)⟫_ℂ
  int : ∀ a : C.LPt, D.IsLocPt a P.r →
    Integrable (fun c : ℂ => TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a ++ [(1, c)]))
  fibre : ∀ a a' : C.LPt, D.IsLocPt a P.r → D.IsLocPt a' P.r →
    TBB.NP p nn F P.r w a a' = ∫ c : ℂ, TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)])
  cont : ∀ i (m : ℕ) (h : C.LPt), (∀ q ∈ h, 1 ≤ q.1 ∧ q.2 ≠ 0) → 1 ≤ m → D.ptSize h + m = P.r + 1 →
    ContinuousOn (fun c : ℂ => (omT p w.length (h ++ [(m, c)]) : ℂ) • p.V (Fi i) (h ++ [(m, c)])) {0}ᶜ

def FieldMemU : Prop :=
  ∀ {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq),
    VecHyp p nn F w c Fi L → ∀ (b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ x : ℂ, x ≠ 0 → MemLp (utT p w.length c Fi L s h x) 2 volume

def FieldSup : Prop :=
  ∀ {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq),
    VecHyp p nn F w c Fi L → ∀ (b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ x : ℂ, x ≠ 0 → ∫ D, ‖utT p w.length c Fi L s h x D‖ ^ 2 = TBB.Ew p nn F P.r w (h ++ [(s - 1, x⁻¹)])

def FieldMeas : Prop :=
  ∀ {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq),
    VecHyp p nn F w c Fi L → ∀ (b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    StronglyMeasurable (btT p w.length c Fi L s h)

def FieldLoc : Prop :=
  ∀ {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq),
    VecHyp p nn F w c Fi L → ∀ (b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖PBK.bz s (btT p w.length c Fi L s h) z‖ ^ 2) K

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def dTy (P : M.Par) (ρ : M.Ty P) : M.Ty P → ℂ := fun σ => if σ = ρ then 1 else 0

def GTCCurvId : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ ρ : M.Ty P,
      (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * d.κ (dTy P ρ) =
        algebraMap ℂ (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) *
          (d.L.GGi * d.L.GGi) * d.κ (dTy P ρ)

def GTCCurvTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → (∀ ρ, ∀ ζ ∈ Ann P, B ρ ζ = star (A ρ ζ)) →
        (∀ ρ : M.Ty P, (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * d.κ (dTy P ρ) =
          algebraMap ℂ (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) *
            (d.L.GGi * d.L.GGi) * d.κ (dTy P ρ)) →
        ∀ ρ, ∀ ζ ∈ Ann P, (NF.dZb (fun w => modA P ρ w - A ρ w) ζ).re = 0

def GTCRefTrace : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e0 ∧ KapF P Bs d e0 ∧
      ∃ A0 B0 : M.Ty P → ℂ → ℂ, SmAB P A0 B0 ∧ ConnF P Bs d e0 A0 B0 ∧
        ∀ ρ, ∃ n : ℤ, ∀ ζ ∈ Ann P, (ζ * (modA P ρ ζ - A0 ρ ζ)).re = (n : ℝ) / 2

def GTCRefAn : Prop :=
  ∀ (TT : ℝ) (α : ℂ → ℂ) (c : ℝ), 0 ≤ TT →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α {ζ : ℂ | TT < Complex.normSq ζ} →
    (∀ ζ : ℂ, TT < Complex.normSq ζ → (ζ * α ζ).re = c) →
    ∀ R : ℝ, 0 < R → TT < R ^ 2 → (circleIntegral α 0 R).im = 2 * Real.pi * c

def GTCRefOfCut : Prop := GTCReal → GTCCurvId → GTCCurvTr → GTCRefTrace → GTCRefAn → GTCRef

private theorem contDiffOn_modA_ann (P : M.Par) (ρ : M.Ty P) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modA P ρ) (Ann P) := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => star ζ) := by
    first
    | exact contDiff_id.star
    | exact Complex.conjCLE.contDiff
    | simpa using (Complex.conjCLE.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have h : modA P ρ = fun ζ : ℂ => (M.aC P ρ : ℂ) * star ζ * (ζ * star ζ - (P.TT : ℂ))⁻¹ := by
    funext ζ
    simp only [modA, div_eq_mul_inv]
    rw [← Complex.mul_conj]
    rfl
  rw [h]
  apply ContDiffOn.mul
  · exact (contDiff_const.mul hs).contDiffOn
  · apply ContDiffOn.inv
    · exact ((contDiff_id.mul hs).sub contDiff_const).contDiffOn
    · intro ζ hζ
      have hz : ζ * star ζ = ((Complex.normSq ζ : ℝ) : ℂ) := Complex.mul_conj ζ
      rw [hz, ← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr hζ).ne'

theorem gTCRef_of_cut : GTCRefOfCut := by
  intro hReal hCurvId hCurvTr hTrace hAn Wp Wq _ _ _ _ _ _ P Bs X d hH
  obtain ⟨e0, he0, hk0, A0, B0, hAB, hC, hn⟩ := hTrace Wp Wq P Bs X d hH
  have hB : ∀ ρ, ∀ ζ ∈ Ann P, B0 ρ ζ = star (A0 ρ ζ) := hReal Wp Wq P Bs X d hH e0 he0 hk0 A0 B0 hAB hC
  refine ⟨e0, he0, hk0, A0, B0, hAB, hC,
    hCurvTr Wp Wq P Bs X d hH e0 he0 hk0 A0 B0 hAB hC hB (hCurvId Wp Wq P Bs X d hH), ?_⟩
  intro ρ R hR hR2
  obtain ⟨n, hn'⟩ := hn ρ
  refine ⟨n, ?_⟩
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modA P ρ) (Ann P) := contDiffOn_modA_ann P ρ
  have key := hAn (max P.TT 0) (fun w => modA P ρ w - A0 ρ w) ((n : ℝ) / 2) (le_max_right _ _)
    ((hsm.sub (hAB ρ).1).mono (fun ζ hζ => show P.TT < Complex.normSq ζ from
      lt_of_le_of_lt (le_max_left _ _) (show max P.TT 0 < Complex.normSq ζ from hζ)))
    (fun ζ hζ => hn' ζ (show P.TT < Complex.normSq ζ from lt_of_le_of_lt (le_max_left _ _) hζ)) R hR (max_lt hR2 (pow_pos hR 2))
  rw [key]; ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def SliceLoc (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Prop :=
  ∀ (Φ Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c c' : Fin P.r → ℂ), c ∈ OmX P.r → c' ∈ OmX P.r →
    (∀ ζ ∈ Ann P, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      (Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ)) →
    ∀ ζ ∈ Ann P, (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      (T Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ)

end preds

def GTSSLSliceDZ : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' →
    ∀ T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), RadDZ P Bs T → SliceLoc P Bs T

def GTSSLSliceSS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → (∀ (Y : ℂ) (a b : Fin 2), SliceLoc P Bs (X.t Y a b)) →
    ∀ l ∈ Finset.Icc 1 (P.k - 1), SliceLoc P Bs (d.SS l).1 ∧ SliceLoc P Bs (star (d.SS l)).1

def GTSSLMat : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    (∀ l ∈ Finset.Icc 1 (P.k - 1), SliceLoc P Bs (d.SS l).1 ∧ SliceLoc P Bs (star (d.SS l)).1) →
      ∃ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t ∧ SSLoc P Bs d e s t

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def RhoUni : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (p : B.SS k r), D.inSS p → ∃ p' : B.SS k r, D.inSS p' ∧
      ∀ X Y : B.Mat k r → (Wq →L[ℂ] Wp),
        ∫ x : Mt k r, B.hsInner (B.rho D p X (Matrix.of x)) (Y (Matrix.of x)) ∂D.μG =
          ∫ x : Mt k r, B.hsInner (X (Matrix.of x)) (B.rho D p' Y (Matrix.of x)) ∂D.μG

def FormAdj : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ → B.Commutes D (B.GPos D) Θ →
    ∀ F F' : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F → HasCompactSupport F → B.SuppIn (B.GPos D) F →
      B.CkOn ⊤ (B.GV k r) F' → HasCompactSupport F' → B.SuppIn (B.GPos D) F' →
      ∫ x : Mt k r, B.hsInner (B.opApply Θ F (Matrix.of x)) (F' (Matrix.of x)) ∂D.μG =
        ∫ x : Mt k r, B.hsInner (F (Matrix.of x)) (B.opAdj Θ F' (Matrix.of x)) ∂D.μG

def AdjIntAsm : Prop := RhoUni → FormAdj → AdjInt

theorem adjInt_of_parts (hA : AdjIntAsm) (hU : RhoUni) (hF : FormAdj) : AdjInt := hA hU hF

end

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

section

open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ckExt_proof : CkExt := by
  intro k r E _ _ F hF hc
  haveI : ProperSpace (B.Mat k r) := FiniteDimensional.proper ℝ _
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_ball (0 : B.Mat k r)
  choose U f' hUo hmem hsm hag using hF
  let V : B.GV k r → Set (B.Mat k r) := fun i => U i.1 i.2 ∩ Metric.ball 0 R
  have hVo : ∀ i, IsOpen (V i) := fun i => (hUo i.1 i.2).inter Metric.isOpen_ball
  have hs : IsClosed (tsupport F ∩ B.GV k r) := (isClosed_tsupport F).inter B5.GV_closed
  have hcov : tsupport F ∩ B.GV k r ⊆ ⋃ i, V i := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx.2⟩, hmem x hx.2, hR hx.1⟩
  obtain ⟨ρ, hρ⟩ := @SmoothPartitionOfUnity.exists_isSubordinate _ (B.Mat k r) _ _ (B.Mat k r) _
    (modelWithCornersSelf ℝ (B.Mat k r)) (B.Mat k r) _ (chartedSpaceSelf _) _ _ _ _ _ hs V hVo hcov
  refine ⟨fun x => ∑ᶠ i, ρ i x • f' i.1 i.2 x, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    refine ρ.contDiffAt_finsum fun i hi => ?_
    have hx : x ∈ U i.1 i.2 := (hρ i hi).1
    exact (hsm i.1 i.2).contDiffAt ((hUo i.1 i.2).mem_nhds hx)
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : B.Mat k r) R) fun x hx => ?_
    have h0 : ∀ i, ρ i x = 0 := fun i => by
      by_contra h
      exact hx (Metric.ball_subset_closedBall (hρ i (subset_tsupport _ h)).2)
    simp [h0]
  · intro g hg
    have key : ∀ i, ρ i g • f' i.1 i.2 g = ρ i g • F g := fun i => by
      by_cases h : ρ i g = 0
      · simp [h]
      · rw [← hag i.1 i.2 g (hρ i (subset_tsupport _ h)).1 hg]
    simp only [key]
    rw [← finsum_smul]
    by_cases hF0 : g ∈ tsupport F
    · rw [ρ.sum_eq_one ⟨hF0, hg⟩, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport hF0, smul_zero]

end Formalism.FourierDecayAlt.P.CutSH.SFG
end
end
