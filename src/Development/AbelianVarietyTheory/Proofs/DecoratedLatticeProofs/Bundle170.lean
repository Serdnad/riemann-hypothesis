module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle145
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle151
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realTranslation_cuspFormMaps_eq_smooth_linear_map : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → ∀ g ∈ GinfC V, ∃ σ : SmT M →ₗ[ℂ] SmT M, ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ MultT θ M J χ, ∀ x, T (σ x) = rTrans g (T x) := by
  first | exact @GlobalTheory.RealTransSm.rTrans_eq_map | exact GlobalTheory.RealTransSm.rTrans_eq_map | (intros; apply GlobalTheory.RealTransSm.rTrans_eq_map <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.SBesEx

theorem gram_scaled {E : Type} [Field E] [StarRing E] {n k l : Type} [Fintype n] (G : Matrix n n E)
    (A : Matrix n k E) (B : Matrix n l E) (α : k → E) (β : l → E) (x : k → n → E) (y : l → n → E)
    (hA : ∀ i a, A i a = α a * x a i) (hB : ∀ i b, B i b = β b * y b i) (a : k) (b : l) :
    (Aᴴ * G * B) a b = star (α a) * β b * (star (x a) ⬝ᵥ (G *ᵥ y b)) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, conjTranspose_apply, hA, hB, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum,
    star_mul']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_sum {E : Type} [Field E] [StarRing E] {n k l m : Type} [Fintype n] [Fintype k] [Fintype l]
    (G : Matrix n n E) (I : Matrix n k E) (J : Matrix n l E) (P : Matrix k m E) (Q : Matrix l m E)
    (hIJ : Iᴴ * G * J = 0) (hJI : Jᴴ * G * I = 0) :
    (I * P + J * Q)ᴴ * G * (I * P + J * Q) = Pᴴ * (Iᴴ * G * I) * P + Qᴴ * (Jᴴ * G * J) * Q := by
  have e : (I * P + J * Q)ᴴ * G * (I * P + J * Q) =
      Pᴴ * (Iᴴ * G * I) * P + Qᴴ * (Jᴴ * G * J) * Q + Pᴴ * (Iᴴ * G * J) * Q + Qᴴ * (Jᴴ * G * I) * P := by
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [e, hIJ, hJI]
  simp

theorem gram_sum_zero {E : Type} [Field E] [StarRing E] {n k l m p : Type} [Fintype n] [Fintype k] [Fintype l]
    (G : Matrix n n E) (I : Matrix n k E) (J : Matrix n l E) (P : Matrix k m E) (Q : Matrix l m E) (C : Matrix n p E)
    (hI : Iᴴ * G * C = 0) (hJ : Jᴴ * G * C = 0) :
    (I * P + J * Q)ᴴ * G * C = 0 := by
  have e : (I * P + J * Q)ᴴ * G * C = Pᴴ * (Iᴴ * G * C) + Qᴴ * (Jᴴ * G * C) := by
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_assoc]
  rw [e, hI, hJ]
  simp

theorem exists_hypDec : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → (∀ y y' : (VS D).V, star (GlobalTheory.Core.SBesEx.cY X h y') ⬝ᵥ ((D.sp.Y 0).gram *ᵥ GlobalTheory.Core.SBesEx.cY X h y) = (VS D).hT y' y) → (∀ (i j : Fin (D.sp.X 0).rank) (a : Fin D.R.rS), (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j)) = (D.sp.X 0).gram i j ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.eX a) = 0 ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.fY a) = 0 ∧ (VS D).hT (X.zu u) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) = 0) → ∀ (L : HSp D), L.rank = 1 → (∀ i j, L.gram i j = star t * t * (VS D).hT (X.zu u) (X.zu u)) → ∀ (V₀ : HSp D) (o : OrthDec V₀ (D.sp.X 0) L), ∃ d : HypDec (D.sp.Y 0) V₀ D.R.rS, d.e = GlobalTheory.Core.SBesEx.eM X h t lam ∧ d.e' = GlobalTheory.Core.SBesEx.e'M X h t lam ∧ d.i₀ = GlobalTheory.Core.SBesEx.i0M X h u tr.wt t o := by
  intro D X h u F₀ tr t lam ht hlam hiso hfr L hL hLg V₀ o
  have hsym : ∀ x y : (VS D).V, (VS D).hT y x = star ((VS D).hT x y) := fun x y =>
    (LinearMap.isSymm_def.1 (VS D).herm x y).symm
  have hs : ∀ a : Fin D.R.rS, star (scl t lam a) ≠ 0 := fun a =>
    star_ne_zero.2 (mul_ne_zero ht (pow_ne_zero _ hlam))
  set q : Fin (D.sp.X 0).rank → (VS D).V := fun i =>
    Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i) with hq
  have hE : ∀ i a, eM X h t lam i a = scl t lam a * cY X h (X.eX a) i := fun _ _ => rfl
  have hE' : ∀ i a, e'M X h t lam i a = (star (scl t lam a))⁻¹ * cY X h (X.fY a) i := fun _ _ => rfl
  have hQ : ∀ i a, qM X h tr.wt i a = (1 : D.host.E) * cY X h (q a) i := fun _ _ => (one_mul _).symm
  have hZ : ∀ i a, zM X h u t L i a = t * cY X h (X.zu u) i := fun _ _ => rfl
  have hzq : ∀ i, (VS D).hT (X.zu u) (q i) = 0 := by
    intro i
    rw [hsym, ← tr.wt_isom, tr.weight_z]
    simp only [hq, Formalism.L2.SG.ColDict.qFr, LinearEquiv.apply_symm_apply, Formalism.L2.SG.ColDict.xFr, D7.zmOf, map_smul]
    rw [D.sp.zm_orth, smul_zero, star_zero]
  have hqq : ∀ i j, (VS D).hT (q i) (q j) = (D.sp.X 0).gram i j := by
    intro i j
    rw [← tr.wt_isom]
    simp only [hq, Formalism.L2.SG.ColDict.qFr, LinearEquiv.apply_symm_apply, Formalism.L2.SG.ColDict.xFr]
    rw [D.sp.iXY_isom 0 (lt_of_lt_of_le two_pos D.R.two_le_m)]
    rfl
  have hQZ : (qM X h tr.wt)ᴴ * (D.sp.Y 0).gram * zM X h u t L = 0 := by
    ext a b
    rw [gram_scaled _ _ _ _ (fun _ => t) _ (fun _ => cY X h (X.zu u)) hQ hZ, hiso, hsym, hzq]
    simp
  have hZQ : (zM X h u t L)ᴴ * (D.sp.Y 0).gram * qM X h tr.wt = 0 := by
    ext a b
    rw [gram_scaled _ _ _ (fun _ => t) _ (fun _ => cY X h (X.zu u)) _ hZ hQ, hiso, hzq]
    simp
  have hQQ : (qM X h tr.wt)ᴴ * (D.sp.Y 0).gram * qM X h tr.wt = (D.sp.X 0).gram := by
    ext a b
    rw [gram_scaled _ _ _ _ _ _ _ hQ hQ, hiso, hqq]
    simp
  have hZZ : (zM X h u t L)ᴴ * (D.sp.Y 0).gram * zM X h u t L = L.gram := by
    ext a b
    rw [gram_scaled _ _ _ (fun _ => t) (fun _ => t) (fun _ => cY X h (X.zu u)) (fun _ => cY X h (X.zu u)) hZ hZ,
      hiso, hLg]
  refine ⟨⟨eM X h t lam, e'M X h t lam, i0M X h u tr.wt t o, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl⟩
  · ext a b
    rw [gram_scaled _ _ _ _ _ _ _ hE hE, hiso, X.ee]
    simp
  · ext a b
    rw [gram_scaled _ _ _ _ _ _ _ hE' hE', hiso, X.ff]
    simp
  · ext a b
    rw [gram_scaled _ _ _ _ _ _ _ hE' hE, hiso, hsym, X.ef, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      have := hs a
      rw [star_ne_zero] at this
      simp [this]
    · simp [hab, Ne.symm hab]
  · rw [i0M, gram_sum _ _ _ _ _ hQZ hZQ, hQQ, hZZ]
    have := gram_sum V₀.gram o.iA o.iB o.qA o.qB o.orth' o.orth
    rw [o.iA_qA_add, o.isoA, o.isoB] at this
    rw [← this]
    simp
  · refine gram_sum_zero _ _ _ _ _ _ ?_ ?_
    · ext a b
      rw [gram_scaled _ _ _ _ _ _ _ hQ hE, hiso, (hfr a a b).2.1]
      simp
    · ext a b
      rw [gram_scaled _ _ _ (fun _ => t) _ (fun _ => cY X h (X.zu u)) _ hZ hE, hiso, hsym, (X.zu_orth u b).1]
      simp
  · refine gram_sum_zero _ _ _ _ _ _ ?_ ?_
    · ext a b
      rw [gram_scaled _ _ _ _ _ _ _ hQ hE', hiso, (hfr a a b).2.2.1]
      simp
    · ext a b
      rw [gram_scaled _ _ _ (fun _ => t) _ (fun _ => cY X h (X.zu u)) _ hZ hE', hiso, hsym, (X.zu_orth u b).2]
      simp
  · have h1 := o.rank_add
    have h2 := D.sp.X_rank 0 (Nat.zero_le _)
    have h3 := D.sp.Y_rank 0 (Nat.zero_le _)
    have h4 := D.R.two_le_m
    obtain ⟨c, hc⟩ := D.R.m_even
    simp only [Ranks.N, Ranks.rankY, Ranks.r, Ranks.rS, zero_mul, add_zero] at h2 h3 ⊢
    omega

end GlobalTheory.Core.SBesEx

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KappaRowChar

variable {D : D7}

theorem half_mul_right {m n r : ℕ} {f : AE D} {M : Mx D m n} (h : IsHalf f M) (N : Mx D n r) : IsHalf f (M ⬝ N) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, h i _]

theorem half_mul_left {m n r : ℕ} {f : AE D} {M : Mx D n r} (N : Mx D m n) (h : IsHalf f M) : IsHalf f (N ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h k j]

theorem half_smul {m n : ℕ} {f : AE D} {M : Mx D m n} (c : AE D) (h : IsHalf f M) : IsHalf f (c • M) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, h i j]

theorem half_adj {m n : ℕ} {f : AE D} {M : Mx D m n} (h : IsHalf f M) : IsHalf (cA D f) (adj M) := by
  intro i j
  show cA D f * cA D (M j i) = cA D (M j i)
  rw [← map_mul, h j i]

theorem trace_half {n : ℕ} {f : AE D} {M : Mx D n n} (h : IsHalf f M) : f * M.trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum, h _ _]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_sec (p : GlobalTheory.FinPl.SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem wRow_half {n : Type} [Fintype n] [DecidableEq n] (p : GlobalTheory.FinPl.SplitPt D k) {W₀ L' : HSp D}
    (ζ' : Fin L'.rank → D.host.E) (β : GlobalTheory.FinPl.Frame p W₀ n) (t : n → k) :
    IsHalf p.e (GlobalTheory.FinPl.LineAct.wRow p ζ' β t) := by
  intro i j
  exact e_mul_sec p _

theorem trace_vecMulVec_mul {R : Type} [CommRing R] {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
    (u : a → R) (v : b → R) (X : Matrix b c R) (J : Matrix c a R) :
    (vecMulVec u v * X * J).trace = v ⬝ᵥ (X *ᵥ (J *ᵥ u)) := by
  rw [Matrix.mul_assoc, Matrix.mulVec_mulVec]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.KappaRowChar

end

namespace GlobalTheory.KappaRowChar

open GlobalTheory.FinPl.LineAct (iota)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_trace {n : Type} [Fintype n] [DecidableEq n] (p : GlobalTheory.FinPl.SplitPt D k) {W₀ L' : HSp D} {a b : ℕ}
    (τ : Matrix (Fin a) (Fin L'.rank) D.host.E) (ζ' : Fin L'.rank → D.host.E) (ζ : Fin a → D.host.E) (hτ : τ *ᵥ ζ' = -ζ)
    (β : GlobalTheory.FinPl.Frame p W₀ n) (t : n → k) (x : Mx D W₀.rank b) (iB : Matrix (Fin b) (Fin a) D.host.E) :
    p.pr (((rat τ : Mx D a L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ (x ⬝ (rat iB : Mx D b a))).trace =
      -(t ⬝ᵥ (β.b' *ᵥ (x.map p.pr *ᵥ (iB.map (iota p) *ᵥ fun i => iota p (ζ i))))) := by

  rw [show p.pr (((rat τ : Mx D a L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ (x ⬝ (rat iB : Mx D b a))).trace =
    ((((rat τ : Mx D a L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ (x ⬝ (rat iB : Mx D b a))).map p.pr).trace from by
  simp only [Matrix.trace, Matrix.diag, map_sum]; rfl]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
  have hτm : (rat τ : Mx D a L'.rank).map p.pr = τ.map (iota p) := rfl
  have hwm : (GlobalTheory.FinPl.LineAct.wRow p ζ' β t).map p.pr = vecMulVec (fun i => iota p (ζ' i)) (t ᵥ* β.b') := by
    ext i j
    simp only [Matrix.map_apply, GlobalTheory.FinPl.LineAct.wRow, Matrix.of_apply, p.pr_sec, vecMulVec_apply]
  have hjm : (rat iB : Mx D b a).map p.pr = iB.map (iota p) := rfl
  have ha : τ.map (iota p) *ᵥ (fun i => iota p (ζ' i)) = -(fun i => iota p (ζ i)) := by
    funext i
    have h := RingHom.map_mulVec (iota p) τ ζ' i
    rw [hτ] at h
    simp only [Pi.neg_apply, map_neg] at h ⊢
    exact h.symm
  rw [hτm, hwm, hjm, Matrix.mul_vecMulVec, ← Matrix.mul_assoc, trace_vecMulVec_mul, ha, Matrix.mulVec_neg,
    Matrix.mulVec_neg, dotProduct_neg, Matrix.dotProduct_mulVec t]

end GlobalTheory.KappaRowChar

namespace GlobalTheory.KappaRowChar

open GlobalTheory.FinPl.LineAct (iota)



theorem kappa_wRow_char : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (L' W₀ : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n), IsSumFrame B.o B.ζ α α₀ → ∀ t : n → k, IsHalf (cA D p.e) ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t))) ∧ ∀ x : WO B.V₀ W₀, IsHalf p.e x → ψ (symplO B.V₀ W₀ x ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t)))) = (χ (-(t ⬝ᵥ fun i => rd α₀ β x i (Sum.inr 0))) : ℂ) := by
  intro D k _ _ _ _ p ψ χ hχ n n' _ _ _ _ ρ B L' W₀ ζ' l α α₀ β hsum t
  have hwh : IsHalf p.e (GlobalTheory.FinPl.LineAct.wRow p ζ' β t) := wRow_half p ζ' β t
  have hmh : IsHalf p.e ((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) := half_mul_left _ hwh
  have hk : l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t) = incA D (-D.host.xi0⁻¹) •
      (giA W₀ ⬝ (adj ((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ gA B.L)) := rfl
  have hu : (B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t)) =
      l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ B.o.pB := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
  refine ⟨?_, fun x _ => ?_⟩
  · rw [hu, hk]
    exact half_mul_right (half_smul _ (half_mul_left _ (half_mul_right (half_adj hmh) _))) _
  · have h0 : symplO B.A W₀ ((B.o.resS W₀) x).1 0 = 0 := by simp [symplO, hO]
    have hxi : incA D D.host.xi0 * cA D (incA D (-D.host.xi0⁻¹)) = 1 := by
      have hne := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
      rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, neg_inv, neg_neg,
        mul_inv_cancel₀ hne, map_one]
    have hxi' : ∀ T : AE D, incA D D.host.xi0 * (cA D (incA D (-D.host.xi0⁻¹)) * T) = T := fun T => by
      rw [← mul_assoc, hxi, one_mul]
    have hs : symplO B.V₀ W₀ x ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t))) =
        Algebra.trace (AF D.host.F) (AE D)
          (((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ (x ⬝ B.o.jB)).trace := by
      rw [OrthDec.symplO_resS, AddEquiv.apply_symm_apply, h0, zero_add, symplO, hO_eq_trace, hk]
      simp only [adj_smul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
        giA_gA_cancel, trace_smul, smul_eq_mul, OrthDec.resS_apply]
      rw [hxi']
    rw [hs, show B.o.jB = (rat B.o.iB : Mx D B.V₀.rank B.L.rank) from rfl]
    have hc := trace_half (half_mul_right hmh (x ⬝ (rat B.o.iB : Mx D B.V₀.rank B.L.rank)))
    have hsec : p.sec (p.pr (((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝
        (x ⬝ (rat B.o.iB : Mx D B.V₀.rank B.L.rank))).trace) =
        (((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝
          (x ⬝ (rat B.o.iB : Mx D B.V₀.rank B.L.rank))).trace := by
      rw [p.sec_pr]; exact hc
    show psiE ψ _ = _
    rw [← hsec, ← hχ, pr_trace p l.τ ζ' B.ζ l.map β t x B.o.iB]
    have hb : ∀ r, α₀.b r (Sum.inr 0) = (B.o.iB.map (iota p) *ᵥ fun i => iota p (B.ζ i)) r := by
      intro r
      rw [hsum]
      simp only [fromCols_apply_inr, replicateCol_apply, ratV, vecB]
      exact RingHom.map_mulVec (iota p) B.o.iB B.ζ r
    have hcol : (fun i => rd α₀ β x i (Sum.inr 0)) =
        β.b' *ᵥ (x.map p.pr *ᵥ (B.o.iB.map (iota p) *ᵥ fun i => iota p (B.ζ i))) := by
      funext i
      rw [Matrix.mulVec_mulVec]
      simp only [rd, Matrix.mul_apply, hb]
      rfl
    rw [hcol]

end GlobalTheory.KappaRowChar
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct.ConjModul

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_sec (p : SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem pr_trace (p : SplitPt D k) {m : ℕ} (M : Mx D m m) : p.pr M.trace = (M.map p.pr).trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]

theorem map_rat (p : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    (rat M).map p.pr = M.map (iota p) := by
  ext i j; rfl


open GlobalTheory.FinPl.LineAct in
set_option maxHeartbeats 1600000 in
theorem conj_half_modul : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → ∀ (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (S₀ A L W₀ : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (β : Frame p W₀ n) (γ : Frame p A n'') (γ₀ : Frame p S₀ (n'' ⊕ Fin 1)), IsSumFrame o ζ γ γ₀ → ∀ t : n → k, IsHalf (cA D p.e) ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wCol p ζ β t)) ∧ ∀ x : WO W₀ S₀, IsHalf p.e x → ψ (symplO W₀ S₀ x ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wCol p ζ β t))) = (χ (-((fun j => rd β γ₀ x (Sum.inr 0) j) ⬝ᵥ t)) : ℂ) := by
  intro D k _ _ _ _ p ψ χ hχ n n'' _ _ _ _ S₀ A L W₀ o ζ hζ β γ γ₀ hγ t
  refine ⟨fun i j => ?_, fun x _ => ?_⟩
  · rw [OrthDec.resT_symm_apply]
    simp only [Matrix.mul_zero, zero_add, Matrix.mul_neg, Matrix.neg_apply, mul_neg, Matrix.mul_apply, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [wCol, Matrix.of_apply]
    rw [mul_left_comm, ← map_mul, e_mul_sec]
  · have hy : (o.resT W₀) ((o.resT W₀).symm (0, -wCol p ζ β t)) = (0, -wCol p ζ β t) := AddEquiv.apply_symm_apply _ _
    rw [OrthDec.symplO_resT, hy]
    have h0 : symplO W₀ A ((o.resT W₀) x).1 0 = 0 := by
      rw [symplO_eq, hO_eq_trace, adj_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.trace_zero, mul_zero, map_zero]
    rw [h0, zero_add, symplO_eq, OrthDec.resT_apply, hO_eq_trace]
    set T := (giA W₀ ⬝ (adj (-wCol p ζ β t) ⬝ (gA L ⬝ (o.pB ⬝ x)))).trace with hT
    set u' : Fin L.rank → k := dualPick ((L.gram.map (iota p)) *ᵥ fun i => iota p (ζ i)) with hu'
    set v : Fin W₀.rank → k := fun j => (iota p D.host.xi0)⁻¹ * ((W₀.gram.map (iota p)) *ᵥ (β.b *ᵥ t)) j with hv
    have hadj : adj (-wCol p ζ β t) = Matrix.of fun i j => -p.sec (u' j * v i) := by
      ext i j
      simp only [adj, wCol, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, Matrix.of_apply, map_neg,
        Formalism.L2.Theta.cA_cA, hu', hv]
    have hZ : p.e • adj (-wCol p ζ β t) = adj (-wCol p ζ β t) := by
      rw [hadj]
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, mul_neg, e_mul_sec]
    have heT : p.e * T = T := by
      conv_rhs => rw [hT, ← hZ]
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hc : p.e * (incA D D.host.xi0 * T) = incA D D.host.xi0 * T := by rw [mul_left_comm, heT]
    have key : ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * T)) =
        (χ (p.pr (incA D D.host.xi0 * T)) : ℂ) := by
      rw [hχ, p.sec_pr, hc]; rfl
    rw [key]
    have hxi : iota p D.host.xi0 ≠ 0 := (map_ne_zero (iota p)).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
    set ζb : Fin L.rank → k := fun i => iota p (ζ i) with hζb
    set R := rd β γ₀ x with hR
    set η : n → k := fun j => R (Sum.inr 0) j with hη
    have hx : x.map p.pr = γ₀.b * R * β.b' := by
      rw [hR, rd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, γ₀.bb', Matrix.one_mul, Matrix.mul_assoc, β.bb',
        Matrix.mul_one]
    have hvec : (fun m => p.pr (ratV (vecB o ζ) m)) = (o.iB.map (iota p)) *ᵥ ζb := by
      funext m
      exact RingHom.map_mulVec (iota p) o.iB ζ m
    have hQ : o.qB.map (iota p) * γ₀.b = fromCols 0 (replicateCol (Fin 1) ζb) := by
      rw [hγ, Matrix.mul_fromCols, OrthDec.jA, map_rat, ← Matrix.mul_assoc, ← Matrix.map_mul, o.qB_iA,
        Matrix.map_zero _ (map_zero _), Matrix.zero_mul]
      congr 1
      ext i j
      simp only [Matrix.mul_apply, Matrix.replicateCol_apply]
      change (o.qB.map (iota p) *ᵥ fun m => p.pr (ratV (vecB o ζ) m)) i = ζb i
      rw [hvec, Matrix.mulVec_mulVec, ← Matrix.map_mul, o.qB_iB, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec]
    have hQR : fromCols (0 : Matrix (Fin L.rank) n'' k) (replicateCol (Fin 1) ζb) * R = vecMulVec ζb η := by
      ext i j
      simp [Matrix.mul_apply, Fintype.sum_sum_type, vecMulVec_apply, hη]
    have hqx : o.qB.map (iota p) * x.map p.pr = vecMulVec ζb (η ᵥ* β.b') := by
      rw [hx, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, hQR, vecMulVec_mul]
    have hg : L.gram.map (iota p) *ᵥ ζb ≠ 0 := by
      intro h0
      apply hζ.2
      have h1 : L.gram *ᵥ ζ = 0 := by
        funext i
        apply (iota p).injective
        rw [RingHom.map_mulVec, Pi.zero_apply, map_zero]
        exact congrFun h0 i
      rw [h1, dotProduct_zero]
    have hu1 : u' ⬝ᵥ (L.gram.map (iota p) *ᵥ ζb) = 1 := dualPick_dot _ hg
    have hZb : (Matrix.of fun i j => -p.sec (u' j * v i)).map p.pr = -vecMulVec v u' := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply, map_neg, p.pr_sec, Matrix.neg_apply, vecMulVec_apply, mul_comm]
    have hv' : v = (iota p D.host.xi0)⁻¹ • ((W₀.gram.map (iota p)) *ᵥ (β.b *ᵥ t)) := rfl
    have hGi : (W₀.gram⁻¹).map (iota p) * W₀.gram.map (iota p) = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (gram_isUnit_det W₀), Matrix.map_one _ (map_zero _) (map_one _)]
    have hval : p.pr (incA D D.host.xi0 * T) = -(η ⬝ᵥ t) := by
      rw [map_mul, hT, pr_trace, hadj]
      simp only [Matrix.map_mul, giA, gA, OrthDec.pB, map_rat, hZb]
      rw [hqx, Matrix.mul_vecMulVec, Matrix.neg_mul, Matrix.vecMulVec_mul_vecMulVec, hu1, one_smul, Matrix.mul_neg,
        Matrix.mul_vecMulVec, Matrix.trace_neg, Matrix.trace_vecMulVec, hv', Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        hGi, Matrix.one_mulVec, smul_dotProduct, smul_eq_mul, dotProduct_comm, Matrix.dotProduct_mulVec,
        Matrix.vecMul_vecMul, β.b'b, Matrix.vecMul_one]
      change iota p D.host.xi0 * -((iota p D.host.xi0)⁻¹ * (η ⬝ᵥ t)) = -(η ⬝ᵥ t)
      field_simp
    rw [hval]

end GlobalTheory.FinPl.LineAct.ConjModul
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

namespace GlobalTheory.FixedUnitNorm

theorem compAt_mem_intV_of_intAt : ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ intAt D (· = v) → compAt D v a ∈ intV D v := by
  intro D v a ha
  have h : finPart D a ∈ intAE D := ha.2
  show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (finPart D a) ∈ intV D v
  generalize finPart D a = b at h ⊢
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    exact ⟨_, hα v, x, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [RingHom.map_add (f := _)]; exact add_mem hy hz
  | neg y _ hy => rw [RingHom.map_neg]; exact neg_mem hy

end GlobalTheory.FixedUnitNorm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kFinite_vectors_discrete_series_smooth_absolutely_irreducible : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ ∧ ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), GlobalTheory.Chain.IoLift.IsKAct M τ a ∧ GlobalTheory.Chain.IoLift.AbsIrr (fun X : lieAt V τ => a X) := by
  first | exact @GlobalTheory.KFinLoc.kFin_smooth_absIrr | exact GlobalTheory.KFinLoc.kFin_smooth_absIrr | (intros; apply GlobalTheory.KFinLoc.kFin_smooth_absIrr <;> assumption)
end
