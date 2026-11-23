module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexIteratedLevelChainInFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle067
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle343
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle345
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle149
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle327
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesPair

theorem besz_pairings : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (ρ : ℕ) (B : BesLev D ρ) (s : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)),
    p.IsBesFrame B s FA F → valuation k s = 1 → valuation k (p.hz B) = 1 →
    ∃ m₀ : n ⊕ Fin c, (∀ r, s * p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r) = F.β r m₀) ∧
      (∀ m, ∑ r, F.β r m * p.pr (star ((B.V.gram *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ)) r)) ∈ 𝒪[k]) ∧
      ∃ m, valuation k (∑ r, F.β r m * p.pr (star ((B.V.gram *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ)) r))) = 1 := by
  intro D k _ _ _ _ p ρ B s n _ _ c FA F hF hs hz
  obtain ⟨rfl, h1, h2, h3, h4⟩ := hF
  have hG := GlobalTheory.MixModel.gram_conjTranspose (S := B.V)
  have hp0 : p.pr 0 = 0 := map_zero (GlobalTheory.LocMod.Witness.prH p)
  have hl : ∀ r, p.pr (star ((B.V.gram *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ)) r)) =
      p.pr ((star (B.d.i₀ *ᵥ vecB B.o B.ζ) ᵥ* B.V.gram) r) := fun r => by
    conv_rhs => rw [← hG, ← Matrix.star_mulVec]
    rfl
  have hM : ∀ {ι : Type} [Fintype ι] (M : Matrix (Fin B.V.rank) ι D.host.E),
      star (B.d.i₀ *ᵥ vecB B.o B.ζ) ᵥ* B.V.gram ᵥ* M = star (vecB B.o B.ζ) ᵥ* (B.d.i₀ᴴ * B.V.gram * M) := fun M => by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  have hsum : ∀ (t : k) {ι : Type} [Fintype ι] (M : Matrix (Fin B.V.rank) ι D.host.E) (i : ι),
      ∑ r, t * p.pr (M r i) * p.pr ((star (B.d.i₀ *ᵥ vecB B.o B.ζ) ᵥ* B.V.gram) r) =
        t * p.pr ((star (B.d.i₀ *ᵥ vecB B.o B.ζ) ᵥ* B.V.gram ᵥ* M) i) := by
    intro t ι _ M i
    change _ = t * GlobalTheory.LocMod.Witness.prH p _

    rw [Matrix.vecMul, dotProduct, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul]
    change t * GlobalTheory.LocMod.Witness.prH p (M r i) * GlobalTheory.LocMod.Witness.prH p _ =
      t * (GlobalTheory.LocMod.Witness.prH p _ * GlobalTheory.LocMod.Witness.prH p (M r i))
    ring
  have hE : star (B.d.i₀ *ᵥ vecB B.o B.ζ) ᵥ* B.V.gram ᵥ* B.d.e = 0 := by
    rw [hM, B.d.i₀e, Matrix.vecMul_zero]
  have hE' : star (B.d.i₀ *ᵥ vecB B.o B.ζ) ᵥ* B.V.gram ᵥ* B.d.e' = 0 := by
    rw [hM, B.d.i₀e', Matrix.vecMul_zero]
  have hA : star (B.d.i₀ *ᵥ vecB B.o B.ζ) ᵥ* B.V.gram ᵥ* (B.d.i₀ * B.o.iA) = 0 := by
    rw [hM, ← Matrix.mul_assoc, B.d.iso, vecB, Matrix.star_mulVec, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, B.o.orth,
      Matrix.vecMul_zero]
  have hdot : (star (B.d.i₀ *ᵥ vecB B.o B.ζ) ᵥ* B.V.gram) ⬝ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ := by
    rw [Matrix.dotProduct_mulVec, hM, B.d.iso, vecB, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
    simp only [Matrix.vecMul_vecMul]
    rw [B.o.isoB, ← Matrix.dotProduct_mulVec]
  have hcore : ∀ a, ∑ r, F.β r (Sum.inl a) * p.pr (star ((B.V.gram *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ)) r)) = 0 := by
    intro a
    simp_rw [h1, hl, Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    have := hsum (FA.β b a) (B.d.i₀ * B.o.iA) b
    rw [hA, Pi.zero_apply, hp0, mul_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hval : ∀ j : Fin (2 * ρ + 1), j.val = ρ →
      ∑ r, F.β r (Sum.inr j) * p.pr (star ((B.V.gram *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ)) r)) = s * p.hz B := by
    intro j hj
    simp_rw [h3 j hj, hl]
    change _ = s * GlobalTheory.LocMod.Witness.prH p _

    rw [← hdot, dotProduct, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul]
    change s * GlobalTheory.LocMod.Witness.prH p _ * GlobalTheory.LocMod.Witness.prH p _ =
      s * (GlobalTheory.LocMod.Witness.prH p _ * GlobalTheory.LocMod.Witness.prH p _)
    ring
  have hunit : valuation k (s * p.hz B) = 1 := by rw [map_mul, hs, hz, one_mul]
  refine ⟨Sum.inr ⟨ρ, by omega⟩, fun r => (h3 _ rfl r).symm, fun m => ?_, Sum.inr ⟨ρ, by omega⟩, by rw [hval _ rfl, hunit]⟩
  rcases m with a | j
  · rw [hcore a]; exact zero_mem _
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · simp_rw [h2 ⟨j.val, hj⟩ j rfl, hl]
    rw [hsum, hE, Pi.zero_apply, hp0, mul_zero]; exact zero_mem _
  · rw [hval j hj]
    exact (Valuation.mem_integer_iff _ _).2 (le_of_eq hunit)
  · have hj2 := j.isLt
    simp_rw [h4 ⟨2 * ρ - j.val, by omega⟩ j (by simp only; omega), hl]
    rw [hsum, hE', Pi.zero_apply, hp0, mul_zero]; exact zero_mem _
end GlobalTheory.BesPair
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace.TraceBwd

open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge GlobalTheory.RootEx

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem colGroup_of_embX {s κ τ : ℕ} (S : SymData k s κ) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hg : embX (s + 1) g ∈ ((S.T (Fin τ)).lev 0 (s + 1) (Nat.zero_add _)).J) : g ∈ colGroup k κ (Fin τ) := by
  obtain ⟨h1, -, -⟩ := GlobalTheory.FirstVertexFrame.firstVertex_typeChain k S.ψ S.ϖ s (Fin τ) κ S.P
    (GlobalTheory.SymShape.sym_shape _ _ _ _ _ _ _ S.sym) S.μ S.tame (s + 1) (Nat.zero_add _)
  rw [← h1]
  refine ⟨1, one_mem _, mem_Cgrp.2 ⟨?_, ?_⟩⟩
  · rw [one_mul]
    exact (le_sup_left : (embX (s + 1)).range ≤ R k _ (s + 1) 1) ⟨g, rfl⟩
  · rw [inv_one, one_mul, mul_one, one_mul]
    exact hg

theorem entries_of_colGroup {κ τ n : ℕ} (e : XIx (Fin κ) (Fin τ) 0 ≃ Fin n) (he : IsOrd xPos e) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hg : g ∈ colGroup k κ (Fin τ)) (a b : XIx (Fin κ) (Fin τ) 0) :
    g.val a b ∈ 𝒪[k] ∧ (e b ≤ e a → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1) := by
  have hp : ∀ c, colPos κ (Fin τ) c = (e c).val := fun c => by
    rw [he c]
    rcases c with (c | c) | c
    exacts [rfl, c.elim0, c.1.elim0]
  obtain ⟨_, ⟨g₀, rfl, rfl⟩, hu⟩ := hg
  refine ⟨(g₀.val a b).2, fun hab => ?_⟩
  have h1 : residue 𝒪[k] (g₀.val a b) = (1 : Matrix _ _ 𝓀[k]) a b := hu a b (by rw [hp, hp]; exact hab)
  have h2 : (1 : Matrix _ _ 𝓀[k]) a b = residue 𝒪[k] ((1 : Matrix _ _ 𝒪[k]) a b) := by
    simp only [Matrix.one_apply, apply_ite (residue 𝒪[k]), map_one, map_zero]
  rw [h2, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at h1
  have h3 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 h1
  convert h3 using 2
  simp only [Matrix.one_apply]
  split_ifs <;> rfl

theorem exists_mat {D : D7} (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k V.rank Y) (e : Y ≃ Fin V.rank) (hβ : F.β = (1 : Matrix (Fin V.rank) (Fin V.rank) k).submatrix id e) (x : GA D V) :
    ∃ g : GL Y k, (mt V x).map q.pr = F.β * g.val * F.γ ∧ ∀ a b, g.val a b = (mt V x).map q.pr (e a) (e b) := by
  have hmul : ∀ y z : GA D V, y * z = 1 → (F.γ * (mt V y).map q.pr * F.β) * (F.γ * (mt V z).map q.pr * F.β) = 1 := fun y z h => by
    have h1 : mt V y * mt V z = 1 := by
      have h2 : mt V y * mt V z = mt V (y * z) := rfl
      rw [h2, h]
      rfl
    have h3 : (mt V y).map q.pr * (mt V z).map q.pr = 1 := by
      rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    calc _ = F.γ * ((mt V y).map q.pr * (F.β * F.γ) * (mt V z).map q.pr) * F.β := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [F.βγ, Matrix.mul_one, h3, Matrix.mul_one, F.γβ]
  let g : GL Y k := ⟨_, _, hmul x x⁻¹ (mul_inv_cancel x), hmul x⁻¹ x (inv_mul_cancel x)⟩
  have hg : (mt V x).map q.pr = F.β * g.val * F.γ := by
    calc _ = (F.β * F.γ) * (mt V x).map q.pr * (F.β * F.γ) := by rw [F.βγ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [g, Matrix.mul_assoc]
  refine ⟨g, hg, fun a b => ?_⟩
  have h1 : (mt V x).map q.pr * F.β = F.β * g.val := by rw [hg, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  have h2 := congrFun (congrFun h1 (e a)) b
  rw [hβ] at h2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h2.symm

end Loc


end GlobalTheory.FamTrace.TraceBwd

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FlatBFLoc.ModelModul
variable {D : D7}

theorem symplectic_pairing_ext_zero_inc_zero {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (t : WO V W)
    (y : WO V₀ W₀) : symplO V W t (dV.ext0 W (dW.inc0 V₀ y)) = symplO V₀ W₀ (dW.p0 ⬝ t ⬝ dV.j0) y := by
  unfold symplO
  congr 2
  have h1 : dW.pY ⬝ (dW.j0 ⬝ y) = 0 := by rw [← Matrix.mul_assoc, HypDec.pY_j0, Matrix.zero_mul]
  have h2 : dW.pX ⬝ (dW.j0 ⬝ y) = 0 := by rw [← Matrix.mul_assoc, HypDec.pX_j0, Matrix.zero_mul]
  have h3 : dW.p0 ⬝ (dW.j0 ⬝ y) = y := by rw [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
  rw [dV.hO_coordS, dW.hO_coordT]
  simp only [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_assoc, HypDec.p0_jX, HypDec.p0_jY, HypDec.p0_j0,
    Matrix.mul_zero, Matrix.mul_one, h1, h2, h3]
  simp [pairS, pairT]

theorem isHalf_mul {a b c d : ℕ} {e : AE D} (A : Mx D a b) {y : Mx D b c} (C : Mx D c d) (hy : IsHalf e y) :
    IsHalf e (A ⬝ y ⬝ C) := by
  have h : e • y = y := Matrix.ext fun i j => hy i j
  intro i j
  have h2 : e • (A ⬝ y ⬝ C) = A ⬝ y ⬝ C := by rw [← Matrix.smul_mul, ← Matrix.mul_smul, h]
  exact congrFun (congrFun h2 i) j

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem mul_iota (b : AE D) (a : k) : b * p.ι a = p.ι (p.π b * a) := by
  have h1 : p.e * p.ι a = p.ι a := by rw [← p.ι_π, p.π_ι]
  have h2 := p.ι_π (b * p.ι a)
  rw [map_mul, p.π_ι, mul_left_comm, h1] at h2
  exact h2.symm

theorem rat_mul_iota {a b c : ℕ} (R : Matrix (Fin a) (Fin b) D.host.E) (A : Matrix (Fin b) (Fin c) k) :
    rat R ⬝ (A.map p.ι : Mx D b c) = ((R.map p.pr * A).map p.ι : Mx D a c) := by
  ext i j

  simp only [rat, Matrix.mul_apply, Matrix.map_apply, map_sum, mul_iota, Place.pr]

theorem iota_mul_rat {a b c : ℕ} (A : Matrix (Fin a) (Fin b) k) (R : Matrix (Fin b) (Fin c) D.host.E) :
    (A.map p.ι : Mx D a b) ⬝ rat R = ((A * R.map p.pr).map p.ι : Mx D a c) := by
  ext i j

  simp only [rat, Matrix.mul_apply, Matrix.map_apply, map_sum, Place.pr]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm, mul_iota, mul_comm]

theorem map_pr_mul {a b c : ℕ} (R : Matrix (Fin a) (Fin b) D.host.E) (R' : Matrix (Fin b) (Fin c) D.host.E) :
    (R * R').map p.pr = R.map p.pr * R'.map p.pr :=
  Matrix.map_mul (f := p.π.comp (incA D))

theorem q_zero_projection_identities {W W₀ : HSp D} {σ : ℕ} (d : HypDec W W₀ σ) :
    d.q0.map p.pr * d.i₀.map p.pr = 1 ∧ d.q0.map p.pr * d.e.map p.pr = 0 ∧ d.q0.map p.pr * d.e'.map p.pr = 0 := by
  have h1 : d.q0 * d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.p0_j0)
  have h2 : d.q0 * d.e = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.p0_jX)
  have h3 : d.q0 * d.e' = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.p0_jY)
  have z : p.pr 0 = 0 := map_zero (p.π.comp (incA D))
  have o : p.pr 1 = 1 := map_one (p.π.comp (incA D))
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_pr_mul, h1, Matrix.map_one _ z o]
  · rw [← map_pr_mul, h2, Matrix.map_zero _ z]
  · rw [← map_pr_mul, h3, Matrix.map_zero _ z]

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem q_zero_jacobi_frame_projection {ρ : ℕ} (J : JacLev D ρ) (s hh : k) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c))
    (h : p.IsJacFrame J s hh G₀ FW) : J.d.q0.map p.pr * FW.β = fromCols G₀.β 0 := by
  obtain ⟨hc, h0, hX, hY⟩ := h
  obtain ⟨q1, q2, q3⟩ := q_zero_projection_identities p J.d
  have key : ∀ (E : Matrix (Fin J.W.rank) (Fin ρ) D.host.E), J.d.q0.map p.pr * E.map p.pr = 0 → ∀ (a : k) (i : Fin ρ)
      (j : Fin c), (∀ r, FW.β r (Sum.inr j) = a * p.pr (E r i)) → ∀ r, (J.d.q0.map p.pr * FW.β) r (Sum.inr j) = 0 := by
    intro E hE a i j hj r
    have := congrFun (congrFun hE r) i
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, hj]
    rw [← mul_zero a, ← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  ext r q
  rcases q with a | j
  · have : (J.d.q0.map p.pr * FW.β) r (Sum.inl a) = (J.d.q0.map p.pr * (J.d.i₀.map p.pr * G₀.β)) r a := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [h0]
    rw [this, ← Matrix.mul_assoc, q1, Matrix.one_mul, fromCols_apply_inl]
  · rw [fromCols_apply_inr, Matrix.zero_apply]
    by_cases hj : j.val < ρ
    · exact key _ q2 _ ⟨j.val, hj⟩ j (hX ⟨j.val, hj⟩ j rfl) r
    · have := j.2
      exact key _ q3 _ ⟨2 * ρ - 1 - j.val, by omega⟩ j (hY ⟨2 * ρ - 1 - j.val, by omega⟩ j (by simp only []; omega)) r

theorem bessel_normal_frame_core_frame_part {ρ : ℕ} (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (FV : Frame k B.V.rank (n' ⊕ Fin c)) (h₀ : p.IsCoreFrame B s FA F₀) (h : p.IsBesFrame B s FA FV) (j : Fin c)
    (hj : j.val = ρ) : B.d.i₀.map p.pr * F₀.β = FV.β.submatrix id (Sum.map id fun _ => j) := by
  obtain ⟨-, h0, -, hz, -⟩ := h
  ext r q
  rcases q with a | u
  · have : (B.d.i₀.map p.pr * F₀.β) r (Sum.inl a) = (B.d.i₀.map p.pr * (B.o.iA.map p.pr * FA.β)) r a := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [h₀.1]
    rw [this, ← Matrix.mul_assoc, ← map_pr_mul]
    exact (h0 r a).symm
  · cases u
    have h2 : p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r) = ∑ m, p.pr (B.d.i₀ r m) * p.pr (vecB B.o B.ζ m) := by

      simp only [Place.pr, Matrix.mulVec, dotProduct, map_sum, map_mul]
    simp only [Matrix.submatrix_apply, Sum.map_inr, id, hz j hj r, h2, Matrix.mul_apply, Matrix.map_apply, h₀.2,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem core_up {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) (s hh : k) (FA : Frame k B.A.rank n')
    (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n)
    (FW : Frame k J.W.rank (n ⊕ Fin c)) (h₀ : p.IsCoreFrame B s FA F₀) (hB : p.IsBesFrame B s FA FV)
    (hJ : p.IsJacFrame J s hh G₀ FW) (j : Fin (c + 1)) (hj : j.val = ρ) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    J.d.p0 ⬝ (p.up FV FW t : WO B.V J.W) ⬝ B.d.j0 = p.up F₀ G₀ (t.submatrix Sum.inl (Sum.map id fun _ => j)) := by
  have h1 := q_zero_jacobi_frame_projection p J s hh G₀ FW hJ
  have h2 := bessel_normal_frame_core_frame_part p B s FA F₀ FV h₀ hB j hj
  have h3 : t * FV.γ * B.d.i₀.map p.pr = t.submatrix id (Sum.map id fun _ => j) * F₀.γ := by
    rw [← Matrix.mul_one (t * FV.γ * B.d.i₀.map p.pr), ← F₀.βγ, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ F₀.β, h2]
    congr 1
    have : t * FV.γ * FV.β = t := by rw [Matrix.mul_assoc, FV.γβ, Matrix.mul_one]
    ext r q
    conv_rhs => rw [← this]
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  unfold Place.up HypDec.p0 HypDec.j0
  rw [rat_mul_iota, iota_mul_rat]
  congr 1
  rw [Matrix.mul_assoc FW.β, ← Matrix.mul_assoc _ FW.β, h1, Matrix.mul_assoc, h3]
  refine (Matrix.mul_assoc _ _ _).symm.trans ?_
  congr 1
  ext r q
  simp [Matrix.mul_apply, Fintype.sum_sum_type]

theorem submatrix_affPt (ρ : ℕ) (j : Fin (c + 1)) (hj : j.val = ρ) (x : Matrix n (n' ⊕ Unit) k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} → k) :
    (affPt (ρ + 1) x.toCols₁ e + GlobalTheory.LocFlat.colAt n' c (ρ + 1) fun r => x r (Sum.inr ())).submatrix Sum.inl
      (Sum.map id fun _ => j) = x := by
  ext r q
  rcases q with a | u
  · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, Free]
  · cases u
    simp [affPt, basePt, GlobalTheory.LocFlat.colAt, Free, hj]

theorem continuous_hO_up {S T : HSp D} (FS : Frame k S.rank n') (FT : Frame k T.rank n) (y : WO S T) :
    Continuous fun t => p.π (hO S T (p.up FS FT t) y) := by
  have hx : ∀ i j, Continuous fun t => p.up FS FT t i j := fun i j =>
    p.cont_ι.comp (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem i j)
  refine p.cont_π.comp ?_
  exact continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
      continuous_finsetSum _ fun _ _ => continuous_const.mul (hx _ _)

theorem model_modul : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ) → ∀ (y : WO B.V₀ J.W₀), IsHalf (cA D p.e) y → ∀ (Ψ Ψ' : SB (Matrix n (n' ⊕ Unit) k)), (∀ t, Ψ'.1 t = ψ (symplO B.V₀ J.W₀ (p.up F₀ G₀ t) y) * Ψ.1 t) → L₀ Ψ' = heisO ψ B.V₀ J.W₀ y (L₀ Ψ) := by
  intro D _ hLaws _ k _ _ _ _ _ _ p ν hν ψ ψk hψk ρ B J st s _ n n' _ _ _ _ c FA F₀ FV G₀ FW h₀ hB hJ Tm hTm L₀ hL₀ y hy
    Ψ Ψ' hΨ'
  have hψc : Continuous ψk := ((GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ st.weil.std).2.1 ψk hψk).1
  have hc : c = 2 * ρ := hJ.1
  obtain ⟨Φ, hΦSB, hΦ⟩ := ((GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective k ψk ν hψc hν n n' c (ρ + 1) (by omega)).1 (by omega)).2 Ψ.1 Ψ.2
  have hy' : IsHalf (cA D p.e) (B.d.ext0 J.W (J.d.inc0 B.V₀ y)) := isHalf_mul J.d.j0 B.d.p0 hy
  have hχ : IsLocallyConstant fun t => ψ (symplO B.V J.W (p.up FV FW t) (B.d.ext0 J.W (J.d.inc0 B.V₀ y))) := by
    have h := (GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψk hψc).comp_continuous
      (continuous_hO_up p FV FW (B.d.ext0 J.W (J.d.inc0 B.V₀ y)))
    have h4 := (GlobalTheory.T.heisenberg_frame_half_inverse D k p _ _ B.V J.W FV FW ψ ψk hψk).2.2.2.1
    have h5 : (fun t => ψ (symplO B.V J.W (p.up FV FW t) (B.d.ext0 J.W (J.d.inc0 B.V₀ y)))) = _ :=
      funext fun t => h4 t _ hy'
    rw [h5]
    exact h
  let Φ₁ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) := ⟨Φ, hΦSB⟩
  let Φ₂ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
    ⟨fun t => ψ (symplO B.V J.W (p.up FV FW t) (B.d.ext0 J.W (J.d.inc0 B.V₀ y))) * Φ t,
      hχ.mul hΦSB.1, hΦSB.2.mul_left⟩
  have h1 := hTm.modul _ hy' Φ₁ Φ₂ fun t => rfl
  have hMx : GlobalTheory.FinPl.MxAt (fun _ => True) y := fun i j =>
    ⟨congrFun (congrFun (GlobalTheory.SplitScalar.half_fin (GlobalTheory.SplitScalar.isSplitIdem_conj p.split) hy) i) j,
      Ideal.mem_iInf.2 fun w => (w.2 trivial).elim⟩
  have h2 := ((hLaws ψ fun _ => True).1 ρ B J st).Heisenberg₂.core (Tm Φ₁) (hTm.theta Φ₁) y hMx
  have h3 := hL₀ Φ₁ Ψ hΦ.symm
  have h4 : Ψ'.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ₂.1 := by
    funext x
    rw [hΨ' x, ← hΦ]
    unfold GlobalTheory.LocFlat.flCol GlobalTheory.RootEx.opE
    rw [← integral_const_mul]
    congr 1
    funext e
    have hj : ρ < c + 1 := by omega
    simp only [Φ₂]
    rw [symplectic_pairing_ext_zero_inc_zero, core_up p B J s _ FA F₀ FV G₀ FW h₀ hB hJ ⟨ρ, hj⟩ rfl, submatrix_affPt ρ ⟨ρ, hj⟩ rfl, mul_assoc]
  rw [← hL₀ Φ₂ Ψ' h4, h1, h2, h3]

end GlobalTheory.FlatBFLoc.ModelModul
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

namespace GlobalTheory.FlatFBUnip

theorem det_of_mem_N {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ} {g : GL (n ⊕ Fin c) k}
    (hg : g ∈ N k n c p) : Matrix.GeneralLinearGroup.det g = 1 := by
  refine Subgroup.closure_induction (p := fun g _ => Matrix.GeneralLinearGroup.det g = 1) ?_ ?_ ?_ ?_ hg
  · intro g hg
    have hb : (g.val).BlockTriangular (lev p) := fun r s h => by
      rw [hg r s h.le, Matrix.one_apply_ne]
      rintro rfl; exact lt_irrefl _ h
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hb.det, Units.val_one]
    refine Finset.prod_eq_one fun a _ => ?_
    have : g.val.toSquareBlock (lev p) a = 1 := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
      rw [hg i j (by rw [hi, hj])]
      by_cases h : i = j
      · subst h; simp
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]; intro e; exact h (congrArg Subtype.val e)
    rw [this, Matrix.det_one]
  · exact map_one _
  · intro x y _ _ hx hy; rw [map_mul, hx, hy, one_mul]
  · intro x _ hx; rw [map_inv, hx, inv_one]

end GlobalTheory.FlatFBUnip

namespace GlobalTheory.FlatFBUnip

theorem unip_law : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ u : GL (Fin c) k, embA n u ∈ N k n c (σ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → flatFB st (Tm Φ') = (ψk (-simpleSum (embA n u)) : ℂ) • flatFB st (Tm Φ) := by
  intro D hFL hOm k _ _ _ _ _ _ p ψ ψk hχ σ J B st s hs n n' _ _ _ _ c G₀ FW FA F₀ FV hJ hC hB Tm hTm u hu Φ Φ' hΦ
  obtain ⟨v, ε, hv, hε⟩ := p.split.2.2
  have hF := (hFL ψ (· = v)).2 σ J B st
  obtain ⟨g, hg, -⟩ := ((GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p).1 B.V (n ⊕ Fin c) FV).1 (embA n u)
  have hgN : g ∈ flagN B.d := GlobalTheory.T.mem_flagUnipotentRadical_of_besselNormalFrameLocal D k p σ B (s * p.xi) n c FA FV hB g (embA n u) hu hg
  have hgP : g ∈ GlobalTheory.FinPl.grpAt B.V (· = v) := by
    have hS := hg.1
    obtain rfl := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 hv
    rw [SuppAt, hε] at hS
    simp only [← GlobalTheory.FinPl.Model.mem_idAt_iff] at hS
    rw [GlobalTheory.FinPl.grpAt, GlobalTheory.FinPl.congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
    intro i j
    have h1 := hS i j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at h1
    have : Ideal.Quotient.mk (GlobalTheory.FinPl.idAt D (· = v)) ((1 : Matrix (Fin B.V.rank) (Fin B.V.rank) (AE D)) i j) =
        (1 : Matrix (Fin B.V.rank) (Fin B.V.rank) (AE D ⧸ GlobalTheory.FinPl.idAt D (· = v))) i j := by
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [this] at h1
    exact h1
  have hdet : Matrix.GeneralLinearGroup.det (embA n u) = 1 := det_of_mem_N hu
  obtain ⟨-, -, -, -, hcomp⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ st.weil.std
  obtain ⟨μS, hμS⟩ := hcomp st.χV
  obtain ⟨μT, hμT⟩ := hcomp st.χW
  have h1 : p.IsLoc FW (1 : GA D J.W) 1 := by
    refine ⟨fun i j => ?_, ?_⟩
    · simp [mt_one]
    · rw [mt_one, Matrix.map_one _ (map_zero p.π) (map_one p.π), Units.val_one, Matrix.mul_one, FW.βγ]
  have hΦ'' : Φ'.1 = (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det (1 : GL (n' ⊕ Fin (c + 1)) k)) : ℂˣ) : ℂ) •
      om μS⁻¹ 1 (embA n u) Φ.1 := by
    funext t
    simp only [om, hdet, map_one, Units.val_one, nabs, Real.one_rpow, inv_one, one_mul, one_smul, Pi.smul_apply,
      Matrix.mul_one, hΦ t]
    norm_num
  have hω := hOm k p ψ J.W B.V st.χV st.χW st.om st.weil μS μT hμS hμT (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) FW FV Tm hTm
    1 1 g (embA n u) h1 hg Φ Φ' hΦ''
  have heq := hF.equiv (Tm Φ) (hTm.theta Φ) g hgN hgP 1 (one_mem _)
  rw [map_one, mul_one, Prod.mk_one_one, map_one, Prod.mk_one_one, map_one] at heq
  rw [← hω, heq, GlobalTheory.T.besselCharacter_localElement_eq_simpleEntrySum D k p ψ ψk hχ σ B (s * p.xi) n c FA FV hB g (embA n u) hu hg]
  simp only [Module.End.one_apply]
  congr 1
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

end GlobalTheory.FlatFBUnip
end
