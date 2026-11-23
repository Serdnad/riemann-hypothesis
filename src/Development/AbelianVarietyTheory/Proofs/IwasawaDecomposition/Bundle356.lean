module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle002
public import Formalism.GradedWeylDivisibility.StatementA
public import Mathlib.Analysis.Normed.Field.Instances
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle104
public import Formalism.LocalRingCardinality.FactDelDualNabla
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.FintypeColChoice
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle007
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle079
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle044
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.CanonicalSurjection

namespace GlobalTheory.Mem.RangeMinors

theorem exists_dual_sum_smul_eq {V ι : Type} [AddCommGroup V] [Module ℚ V] [Fintype ι] (n : ι → V) (J₀ : ι) :
    ∃ ψ : Module.Dual ℚ V, ∑ J, ψ (n J) • n J = n J₀ := by
  let T : Module.Dual ℚ V →ₗ[ℚ] V :=
    { toFun := fun ψ => ∑ J, ψ (n J) • n J
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.smul_sum, mul_smul] }
  by_contra h
  have hn : n J₀ ∉ LinearMap.range T := fun ⟨ψ, hψ⟩ => h ⟨ψ, hψ⟩
  obtain ⟨φ, hφ, hbot⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have h0 : φ (T φ) = 0 := by
    have : φ (T φ) ∈ (LinearMap.range T).map φ := Submodule.mem_map_of_mem ⟨φ, rfl⟩
    rw [hbot] at this
    simpa using this
  have h1 : ∑ J, φ (n J) * φ (n J) = 0 := by

    simpa [T, map_sum] using h0
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun J _ => mul_self_nonneg (φ (n J)))).1 h1 J₀ (Finset.mem_univ _)
  exact hφ (mul_self_eq_zero.1 h2)

theorem exists_dual_baseChange {σ : Type} (k : Type) [Field k] [CharZero k] (ψ : Module.Dual ℚ (MvPolynomial σ ℚ)) :
    ∃ ph : Module.Dual k (MvPolynomial σ k),
      ∀ F : MvPolynomial σ ℚ, ph (MvPolynomial.map (algebraMap ℚ k) F) = algebraMap ℚ k (ψ F) := by
  refine ⟨(MvPolynomial.basisMonomials σ k).constr k fun m => algebraMap ℚ k (ψ (MvPolynomial.monomial m 1)), fun F => ?_⟩
  induction F using MvPolynomial.induction_on' with
  | monomial m a =>
    have e1 : (MvPolynomial.monomial m a : MvPolynomial σ ℚ) = a • MvPolynomial.monomial m 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have e2 : MvPolynomial.map (algebraMap ℚ k) (MvPolynomial.monomial m a : MvPolynomial σ ℚ) =
        algebraMap ℚ k a • MvPolynomial.basisMonomials σ k m := by
      rw [MvPolynomial.map_monomial, MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e2, map_smul, Module.Basis.constr_basis]
    conv_rhs => rw [e1, map_smul, smul_eq_mul, map_mul]
    rw [smul_eq_mul]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]

theorem eval_nablaX_eq_minY {Lt k : Type} [Fintype Lt] [DecidableEq Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram)
    (J : KM.ColChoice N nu) (y : Lt → Fin N → ℕ → k) :
    MvPolynomial.eval (fun v : Lt × ℕ × Fin N => y v.1 v.2.2 v.2.1)
      (MvPolynomial.map (Int.castRingHom k) (KM.nablaX N nu J)) = GL3Columns.minY N nu J y := by
  unfold KM.nablaX GL3Columns.minY
  simp only [map_prod]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp

theorem exists_dual_DeX_eq_minY : ∀ (D : D7) (k : Type) [Field k] [CharZero k] (N : ℕ) (nu : Bool × Formalism.MainNotions.G.HH D → YoungDiagram)
    (J : KM.ColChoice N nu), ∃ ph : Module.Dual k (MvPolynomial ((Bool × Formalism.MainNotions.G.HH D) × ℕ × Fin N) k),
      ∀ y : Bool × Formalism.MainNotions.G.HH D → Fin N → ℕ → k, ph (GL3Columns.DeX N nu y) = GL3Columns.minY N nu J y := by
  intro D k _ _ N nu J₀
  classical
  haveI : Finite (KM.ColChoice N nu) := by
    unfold KM.ColChoice
    infer_instance
  letI : Fintype (KM.ColChoice N nu) := Fintype.ofFinite _
  obtain ⟨ψ, hψ⟩ := exists_dual_sum_smul_eq
    (fun J : KM.ColChoice N nu => MvPolynomial.map (Int.castRingHom ℚ) (KM.nablaX N nu J)) J₀
  obtain ⟨ph, hph⟩ := exists_dual_baseChange k ψ
  have hm : ∀ J : KM.ColChoice N nu, MvPolynomial.map (algebraMap ℚ k)
      (MvPolynomial.map (Int.castRingHom ℚ) (KM.nablaX N nu J)) =
      MvPolynomial.map (Int.castRingHom k) (KM.nablaX N nu J) := fun J => by
    rw [MvPolynomial.map_map]
    congr 2
    exact RingHom.ext_int _ _
  refine ⟨ph, fun y => ?_⟩

  rw [GL3Columns.wwCB_holds D k N nu y, finsum_eq_sum_of_fintype, map_sum]
  have h := congrArg (fun F => MvPolynomial.eval (fun v : (Bool × Formalism.MainNotions.G.HH D) × ℕ × Fin N => y v.1 v.2.2 v.2.1)
    (MvPolynomial.map (algebraMap ℚ k) F)) hψ

  simp only [map_sum] at h
  rw [hm, eval_nablaX_eq_minY] at h
  rw [← h]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← MvPolynomial.smul_eq_C_mul, map_smul, ← hm, hph, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_mul,
    MvPolynomial.eval_C, hm, eval_nablaX_eq_minY, smul_eq_mul, mul_comm]

end GlobalTheory.Mem.RangeMinors
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KForm.WWUnique

theorem aeval_map_nablaX {Lt : Type} [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) :
    MvPolynomial.aeval (R := ℂ_[l]) (fun v : Lt × ℕ × Fin N1 => ∑ a : Fin N0,
        (MvPolynomial.X (Sum.inl (v.1, v.2.1, a)) * MvPolynomial.X (Sum.inr (v.1, a, v.2.2)) :
          MvPolynomial (KM.XZ Lt N0 N1) ℂ_[l]))
      (MvPolynomial.map (Int.castRingHom ℂ_[l]) (KM.nablaX N1 nu I)) =
    MvPolynomial.map (Int.castRingHom ℂ_[l]) (KM.Gxz N0 N1 nu I) := by
  simp only [KM.nablaX, KM.Gxz, KM.minorXZ, map_prod]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det, RingHom.map_det, AlgHom.map_det]
  congr 1
  ext i k

  simp [MvPolynomial.map_X, MvPolynomial.aeval_X, map_sum, map_mul]

theorem ww_unique : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (N0 N1 : ℕ) (hN : N0 ≤ N1) (nu : Bool × HH D → YoungDiagram)
    (hnu : ∀ z, (nu z).colLen 0 ≤ N0) (Th : MvPowerSeries ((Bool × HH D) × Fin N0 × Fin N1) ℂ_[p])
    (ph : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N0) ℂ_[p]))
    (ph' : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]))
    (κ : ℂ_[p]) (Q : MvPolynomial ((Bool × HH D) × Fin N0 × ℕ) ℂ_[p])
    (hQ : ∀ y : Bool × HH D → Fin N0 → ℕ → ℂ_[p], MvPolynomial.eval (fun v => y v.1 v.2.1 v.2.2) Q = ph (GL3Columns.DeX N0 nu y))
    (h : ∀ y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p],
      ph' (GL3Columns.DeX N1 nu fun s => GL3Columns.colsOf (y' (tauPl D s))) = κ * GL3Columns.applyQ p N0 N1 Th Q (fun s => GL3Columns.colsOf (y' (tauPl D s))))
    (I : KM.ColChoice N1 nu), ph' (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N1 nu I)) = κ * ph (KM.applyAt0 N0 N1 p Th (KM.Gxz N0 N1 nu I)) := by
  intro D p _ N0 N1 hN nu hnu Th ph ph' κ Q hQ h I
  classical
  haveI : Finite (KM.ColChoice N1 nu) := by
    unfold KM.ColChoice
    infer_instance
  letI : Fintype (KM.ColChoice N1 nu) := Fintype.ofFinite _
  let J : ((Bool × HH D) × Fin N0 × Fin N1 →₀ ℕ) → ℂ_[p] :=
    fun m => (m.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff m Th
  let σ : (Bool × HH D) × ℕ × Fin N1 → MvPolynomial (KM.XZ (Bool × HH D) N0 N1) ℂ_[p] :=
    fun v => ∑ a : Fin N0, MvPolynomial.X (Sum.inl (v.1, v.2.1, a)) * MvPolynomial.X (Sum.inr (v.1, a, v.2.2))
  let L : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]) :=
    ph ∘ₗ GlobalTheory.KFormCore.jetL J ∘ₗ (MvPolynomial.aeval (R := ℂ_[p]) σ).toLinearMap
  have hL : ∀ J' : KM.ColChoice N1 nu, L (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N1 nu J')) =
      ph (KM.applyAt0 N0 N1 p Th (KM.Gxz N0 N1 nu J')) := by
    intro J'
    simp only [L, LinearMap.comp_apply, AlgHom.toLinearMap_apply, σ]
    rw [aeval_map_nablaX, GlobalTheory.KFormCore.applyAt0_eq]
  have hLD : ∀ y, L (GL3Columns.DeX N1 nu y) = GL3Columns.applyQ p N0 N1 Th Q y := by
    intro y

    rw [GL3Columns.ww_holds D p N0 N1 nu Th ph Q hQ y, GL3Columns.wwCB_holds D ℂ_[p] N1 nu y, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun J' _ => ?_
    rw [← MvPolynomial.smul_eq_C_mul, map_smul, hL, smul_eq_mul]
  let ψ : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]) := ph' - κ • L
  have hψ : ∀ y, ψ (GL3Columns.DeX N1 nu y) = 0 := by
    intro y
    let e := Equiv.ofBijective (tauPl D) (tauPl_bij D)
    let y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p] := fun τ => Matrix.of fun a b => y (e.symm τ) a b
    have hy : GL3Columns.DeX N1 nu y = GL3Columns.DeX N1 nu (fun s => GL3Columns.colsOf (y' (tauPl D s))) := by
      unfold GL3Columns.DeX
      refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
      congr 1
      ext i j
      have hj : (j : ℕ) < N1 :=
        lt_of_lt_of_le j.2 ((YoungDiagram.colLen_anti _ 0 c (Nat.zero_le _)).trans ((hnu s).trans hN))
      have hs : e.symm (tauPl D s) = s := e.symm_apply_apply s
      simp [GL3Columns.colsOf, hj, y', hs]
    rw [hy]
    simp only [ψ, LinearMap.sub_apply, LinearMap.smul_apply, h, hLD, smul_eq_mul, sub_self]
  have h4 := GL3Columns.wwInj_holds D p N1 nu ψ hψ I
  simp only [ψ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hL] at h4
  exact sub_eq_zero.mp h4

end GlobalTheory.KForm.WWUnique
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DelWSub

def intBall (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := GlobalTheory.ClosedBallValuationSubring.closedBallSubring ℂ_[p]

theorem eval_rowAct {R : Type} [CommRing R] {N : ℕ} (G Y : Matrix (Fin N) (Fin N) R)
    (P : MvPolynomial (Fin N × Fin N) R) :
    MvPolynomial.eval (fun k => Y k.1 k.2) (Formalism.GradedWeylDivisibility.rowAct R G P) =
      MvPolynomial.eval (fun k => (G * Y) k.1 k.2) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul, MvPolynomial.eval_mul, MvPolynomial.eval_mul, hp]
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]

theorem weyl_eq (N : ℕ) (ν : Fin N → ℕ) :
    WeylLatticeDuality.weyl ℤ N N le_rfl ν = Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν := rfl

theorem rowSub_expand (p : ℕ) [Fact p.Prime] {N : ℕ} (ν : Fin N → ℕ)
    (g : Matrix (Fin N) (Fin N) ℂ_[p]) (hg : ∀ a b, ‖g a b‖ ≤ 1)
    (f : MvPolynomial (Fin N × Fin N) ℤ) (hf : f ∈ WeylLatticeDuality.weyl ℤ N N le_rfl ν) :
    ∃ (s : Finset (List (Fin N × Fin N × ℕ))) (o : List (Fin N × Fin N × ℕ) → ℂ_[p]),
      (∀ w, ‖o w‖ ≤ 1) ∧ ∀ Y : Matrix (Fin N) (Fin N) ℂ_[p],
        MvPolynomial.eval (fun k => (g * Y) k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p]) f) =
          ∑ w ∈ s, o w * MvPolynomial.eval (fun k => Y k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p])
            (WeylLatticeDuality.applyWord ℤ w (WeylLatticeDuality.hw ℤ le_rfl ν))) := by
  classical
  let O := intBall p
  let gO : Matrix (Fin N) (Fin N) O := fun a b => ⟨g a b, hg a b⟩
  have hgO : gO.map O.subtype = g := by ext a b; rfl
  have hfO : MvPolynomial.map (Int.castRingHom O) f ∈ Formalism.GradedWeylDivisibility.weyl O N N le_rfl ν :=
    GlobalTheory.WeylRowAll.map_mem_weyl (Int.castRingHom O) le_rfl ν f (by rw [← weyl_eq]; exact hf)
  have hQ := GlobalTheory.WeylRowAll.rowAct_mem_weyl O le_rfl ν gO _ hfO
  unfold Formalism.GradedWeylDivisibility.weyl at hQ
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hQ
  refine ⟨c.support, fun w => (c w : ℂ_[p]), fun w => (c w).2, fun Y => ?_⟩
  have h1 : MvPolynomial.map (Int.castRingHom ℂ_[p]) f =
      MvPolynomial.map O.subtype (MvPolynomial.map (Int.castRingHom O) f) := by
    rw [MvPolynomial.map_map]; congr 1
  have hterm : ∀ w, MvPolynomial.map O.subtype (Formalism.GradedWeylDivisibility.applyWord O w (Formalism.GradedWeylDivisibility.hw O le_rfl ν)) =
      MvPolynomial.map (Int.castRingHom ℂ_[p])
        (WeylLatticeDuality.applyWord ℤ w (WeylLatticeDuality.hw ℤ le_rfl ν)) := by
    intro w
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
    show _ = MvPolynomial.map _ (Formalism.GradedWeylDivisibility.applyWord ℤ w (Formalism.GradedWeylDivisibility.hw ℤ le_rfl ν))
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]

  rw [h1, ← eval_rowAct, ← hgO, ← GlobalTheory.WeylRowAll.map_rowAct, ← hc, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, hterm]
  rfl

def act (p : ℕ) [Fact p.Prime] (T : Type) (N : ℕ) (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) :
    ((T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) →+ ((T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) where
  toFun F := fun y => c * F (fun τ => g τ * y τ)
  map_zero' := by funext y; simp
  map_add' F G := by funext y; simp [mul_add]

theorem mem_delW_act (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ)
    (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) (hg : ∀ τ a b, ‖g τ a b‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) (hF : F ∈ WeylLatticeDuality.DelW p T N ν) :
    (fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν := by
  classical
  refine (AddSubgroup.closure_le ((WeylLatticeDuality.DelW p T N ν).comap (act p T N g c))).2 ?_ hF
  rintro _ ⟨r, f, hr, hf, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap]
  choose s o ho hexp using fun τ => rowSub_expand p (ν τ) (g τ) (hg τ) (f τ) (hf τ)
  have heq : act p T N g c (fun y => r * ∏ τ, MvPolynomial.eval (fun k : Fin N × Fin N => y τ k.1 k.2)
      (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f τ))) =
      ∑ x ∈ Fintype.piFinset s, fun y => (c * r * ∏ τ, o τ (x τ)) *
        ∏ τ, MvPolynomial.eval (fun k : Fin N × Fin N => y τ k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p])
          (WeylLatticeDuality.applyWord ℤ (x τ) (WeylLatticeDuality.hw ℤ le_rfl (ν τ)))) := by
    funext y
    rw [Finset.sum_apply]
    show c * (r * ∏ τ, MvPolynomial.eval (fun k : Fin N × Fin N => (g τ * y τ) k.1 k.2)
      (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f τ))) = _
    simp only [hexp]
    rw [Finset.prod_univ_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.prod_mul_distrib]; ring
  rw [heq]
  refine AddSubgroup.sum_mem _ fun x _ => AddSubgroup.subset_closure
    ⟨c * r * ∏ τ, o τ (x τ), fun τ => WeylLatticeDuality.applyWord ℤ (x τ) (WeylLatticeDuality.hw ℤ le_rfl (ν τ)),
      ?_, fun τ => Submodule.subset_span ⟨x τ, rfl⟩, rfl⟩
  rw [norm_mul, norm_mul, norm_prod]
  exact mul_le_one₀ (mul_le_one₀ hc (norm_nonneg _) hr) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun τ _ => ho τ _)

theorem exists_int_inv (p : ℕ) [Fact p.Prime] {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ_[p])
    (hg : ∀ a b, ‖g a b‖ ≤ 1) (hdet : ‖g.det‖ = 1) :
    ∃ h : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖h a b‖ ≤ 1) ∧ g * h = 1 := by
  classical
  let O := intBall p
  let gO : Matrix (Fin N) (Fin N) O := fun a b => ⟨g a b, hg a b⟩
  have hmap : gO.map O.subtype = g := by ext a b; rfl
  have hd : O.subtype gO.det = g.det := by rw [RingHom.map_det]; rfl
  have hdne : g.det ≠ 0 := norm_ne_zero_iff.1 (by rw [hdet]; exact one_ne_zero)
  have hu : IsUnit gO.det := by
    refine IsUnit.of_mul_eq_one (⟨g.det⁻¹, ?_⟩ : O) ?_
    · show ‖g.det⁻¹‖ ≤ 1
      rw [norm_inv, hdet, inv_one]
    · apply Subtype.ext
      show O.subtype gO.det * g.det⁻¹ = 1
      rw [hd, mul_inv_cancel₀ hdne]
  refine ⟨gO⁻¹.map O.subtype, fun a b => (gO⁻¹ a b).2, ?_⟩
  rw [← hmap, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]

theorem delW_rowSub : ∀ (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]), (∀ τ a b, ‖g τ a b‖ ≤ 1) → (∀ τ, ‖(g τ).det‖ = 1) → ‖c‖ = 1 → ∀ F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p], F ∈ WeylLatticeDuality.DelW p T N ν ↔ (fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν := by
  intro p _ T _ N ν g c hg hdet hc F
  constructor
  · exact mem_delW_act p T N ν g c hg hc.le F
  · intro h
    have hinv := fun τ => exists_int_inv p (g τ) (hg τ) (hdet τ)
    choose hm hmI hmul using hinv
    have hc0 : c ≠ 0 := norm_ne_zero_iff.1 (by rw [hc]; exact one_ne_zero)
    have := mem_delW_act p T N ν hm c⁻¹ hmI (by rw [norm_inv, hc, inv_one]) _ h
    convert this using 1
    funext y
    rw [inv_mul_cancel_left₀ hc0]
    congr 1
    funext τ
    simp [← Matrix.mul_assoc, hmul]

end GlobalTheory.DelWSub
end
end
