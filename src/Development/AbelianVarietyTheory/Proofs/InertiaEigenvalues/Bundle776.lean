module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle760
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle761
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeDiscPeriodDataOfAcrisPeriods
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle710
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle292
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle347
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle554
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle363
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle762
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle707
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle555
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle379
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle188
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle226
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqAct
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.mem_OE_of_invariant_frobenius_solution : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ] (x : κ → WCb l) (c : κ → κ → WCb l), (∀ i j, c i j ∈ bk.OE) → (∀ j, x j = ∑ i, frobW l (x i) * c i j) → (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x j) = x j) → ∀ j, x j ∈ bk.OE := by
  first | exact @GlobalTheory.BSP.invariant_phi_solution_mem_OE | exact GlobalTheory.BSP.invariant_phi_solution_mem_OE | (intros; apply GlobalTheory.BSP.invariant_phi_solution_mem_OE <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isUnit_of_saturated' : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y A : Matrix (Fin d) (Fin d) (WCb l)), Y.det ≠ 0 → (∀ i j, A i j ∈ bk.OE) → Y.map (frobW l) = Y * A → (∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (WCb l), IsUnit R ∧ R * Y.map (galW l (g : GQ l)) = Y) → (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → (∀ i, ((l : ℕ) : WCb l) ∣ Y.mulVec v i) → ∀ i, ((l : ℕ) : WCb l) ∣ v i) → IsUnit Y := by
  first | exact @GlobalTheory.SatInvUnit.isUnit_of_saturated | exact GlobalTheory.SatInvUnit.isUnit_of_saturated | (intros; apply GlobalTheory.SatInvUnit.isUnit_of_saturated <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.stratPeriodMatrix_equivariant_hom_comm_frobenius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∀ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T → bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A) := by
  first | exact @GlobalTheory.BSP.mreal_hom_frob | exact GlobalTheory.BSP.mreal_hom_frob | (intros; apply GlobalTheory.BSP.mreal_hom_frob <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.eisenstein_pow_dvd_of_bdRPlus_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), aDp l (bk.ev bk.E) ≠ 0 ∧ ∀ (m : ℕ) (s : bk.S), aDp l (bk.ev bk.E) ^ m ∣ aDp l (bk.ev s) → bk.E ^ m ∣ s := by
  first | exact @GlobalTheory.BSP.DivTransfer.div_transfer | exact GlobalTheory.BSP.DivTransfer.div_transfer | (intros; apply GlobalTheory.BSP.DivTransfer.div_transfer <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem _root_.GlobalTheory.T.invariantEtaleBasis_change_by_OE_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (T0 Wm Wm' A0 A0' : Matrix (Fin d) (Fin d) (WCb l)), (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T0.map (galW l (g : GQ l)) = T0) → (∀ i j, A0 i j ∈ bk.OE) → (∀ i j, A0' i j ∈ bk.OE) → T0.map (frobW l) = T0 * A0 → A0 * A0' = 1 → (∀ i j, Wm i j ∈ bk.OE) → (∀ i j, Wm' i j ∈ bk.OE) → Wm * Wm' = 1 → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * (T0 * Wm).map (galW l (g : GQ l)) = T0 * Wm) ∧ ∃ A1 A1' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A1 i j ∈ bk.OE) ∧ (∀ i j, A1' i j ∈ bk.OE) ∧ (T0 * Wm).map (frobW l) = (T0 * Wm) * A1 ∧ A1 * A1' = 1 := by
  first | (exact @GlobalTheory.ChangeEtaleBasis.main) | (exact GlobalTheory.ChangeEtaleBasis.main) | (intros; apply GlobalTheory.ChangeEtaleBasis.main  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem _root_.GlobalTheory.T.limitVectors_invertible_basis_over_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (d' : ℕ → ℕ) (R : ∀ n, Matrix (Fin d) (Fin (d' n)) (WCb l)), (∀ n, ∃ R' : Matrix (Fin (d' n)) (Fin d) (WCb l), (∀ i j, R' i j ∈ bk.OE) ∧ ∀ i j, (l : WCb l) ^ n ∣ (R n * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → (∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ n i j, R n i j ∈ bk.OE) → ∃ V V' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, V i j ∈ bk.OE) ∧ (∀ i j, V' i j ∈ bk.OE) ∧ V * V' = 1 ∧ ∀ j k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ ((fun i => V i j) - R k *ᵥ fun a => bk.evW (s' a)) i := by
  first | (exact @GlobalTheory.LimVec.invertible_basis) | (exact GlobalTheory.LimVec.invertible_basis) | (intros; apply GlobalTheory.LimVec.invertible_basis  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_envelope_dvd_prime_of_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (An : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (q : Hom En.Q An.Q), q.comp En.inl = An.inl.comp bk.ι → q.comp En.inr = An.inr → ∀ x : En.Q.A, ((l : ℕ) : An.Q.A) ∣ q.f x → ((l : ℕ) : En.Q.A) ∣ x := by
  first | exact @GlobalTheory.BSP.envPush_dvd_l | exact GlobalTheory.BSP.envPush_dvd_l | (intros; apply GlobalTheory.BSP.envPush_dvd_l <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.exists_integralWittLattice_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y1 : Matrix (Fin d) (Fin d) (WCb l)), Y1.det ≠ 0 → ∃ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) ∧ P.det ≠ 0 ∧ (l : WCb l) ^ m • Y' = Y1 * P ∧ (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1 *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) ∧ ∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i := by
  first | exact @GlobalTheory.SatLattice.exists_lattice_basis | exact GlobalTheory.SatLattice.exists_lattice_basis | (intros; apply GlobalTheory.SatLattice.exists_lattice_basis <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.crystallineLatticeDiscPeriodData_of_acris_periods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (N c₁ c₂ c₃ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)) (X X' : Matrix (Fin d) (Fin d) (bk.S)), F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) → X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) → (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, ∀ i j, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (X'.map (BK.hf f) * X.map (BK.hf g)) i j) → ∀ Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l), (Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), C.t ^ N • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • Z) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N))) → Nonempty (Seed bk d ρ τ) := by
  first | exact @GlobalTheory.BSP.seed_of_periods | exact GlobalTheory.BSP.seed_of_periods | (intros; apply GlobalTheory.BSP.seed_of_periods <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BcSpehProof

theorem hasInfCharGL_unique {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} (hV : V ≠ ⊥) {τ : E →+* ℂ} {m m' : Multiset ℂ} (h : HasInfCharGL V τ m)
    (h' : HasInfCharGL V τ m') : m = m' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV
  have e : ((m.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod =
      ((m'.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod := by
    refine Polynomial.funext fun u => ?_
    have := smul_left_injective ℂ h0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map] using this
  have e2 := congrArg Polynomial.roots e
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e2
  exact Multiset.map_injective neg_injective e2

theorem spehInf_eq (d : ℕ) (m : Multiset ℂ) : GlobalTheory.SphGal.spehInf d m = GlobalTheory.DefiniteBC.spehInf d m := by
  unfold GlobalTheory.SphGal.spehInf GlobalTheory.DefiniteBC.spehInf
  rw [← List.sum_ofFn, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

end GlobalTheory.BcSpehProof

namespace GlobalTheory.BcSpehProof

theorem isUnitarisable_of_equiv' {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : π.Equiv σ) (h : IsUnitarisable π) : IsUnitarisable σ := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨(B ∘ₗ φ.symm.toLinearEquiv.toLinearMap).compl₂ φ.symm.toLinearEquiv.toLinearMap, fun v w => h1 _ _,
    fun v hv => h2 _ (φ.symm.toLinearEquiv.map_ne_zero_iff.2 hv), fun g v w => ?_⟩
  have e : ∀ v, φ.symm.toLinearEquiv (σ g v) = π g (φ.symm.toLinearEquiv v) := fun v =>
    φ.symm.toIntertwiningMap.isIntertwining _ _ g v
  show B (φ.symm.toLinearEquiv (σ g v)) (φ.symm.toLinearEquiv (σ g w)) = _
  rw [e, e, h3]
  rfl

theorem isUnitarisable_of_isLocComp (H : GlobalTheory.Published.DiscreteSpectrumGL) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {a : ℕ} (ha : 1 ≤ a) (P : CuspSub E a) (hP : GlobalTheory.DiscSpec.IsNormalised P)
    (w : HeightOneSpectrum (𝓞 E)) (ρ : LocIrr w a) (hρ : P.IsLocComp w ρ) : IsUnitarisable ρ.ρ := by
  obtain ⟨V, ⟨hV, hS⟩, -⟩ := (H E a ha).2.1 a 1 P (one_mul a) hP
  have hc := (H E a ha).2.2.2.2 V hV a 1 P hP hS
  obtain ⟨-, σ', -, hσ'⟩ := hc.exLoc w
  obtain ⟨hd, h1⟩ := hc.loc w ρ σ' hρ hσ'
  obtain ⟨hd', h2⟩ := GlobalTheory.LocGL.isSpeh_one (GlobalTheory.LocGL.IrrGL.of ρ.ρ ρ.smooth ρ.irred)
  obtain ⟨e⟩ := h1.unique h2
  have hu := GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable E a V hV w σ' hσ'
  exact isUnitarisable_of_equiv' ((GlobalTheory.LocGL.IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).trans e).symm hu

theorem hasInfChar_eq_of_sigma {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a b : ℕ} {P : CuspSub E a}
    {Q : CuspSub E b} (h : (⟨a, CG.mk P⟩ : Σ c, CG E c) = ⟨b, CG.mk Q⟩) {τ : E →+* ℂ} {m m' : Multiset ℂ}
    (hm : P.HasInfChar τ m) (hm' : Q.HasInfChar τ m') : m = m' := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h
  exact (CuspSub.Iso.hasInfChar (Quotient.exact (eq_of_heq h2)) hm).unique hm'

end GlobalTheory.BcSpehProof

namespace GlobalTheory.BcSpehProof

theorem baseChange_speh_of_discreteSeries (H : GlobalTheory.Published.DiscreteSpectrumGL)
    (hW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
      ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ τ : E →+* ℂ, ∃ lam : Formalism.BasicNotions.DomWeight n, HasWeightAt π τ lam)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 1 ≤ n)
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) {c : ℕ} {N : Fin c → ℕ} {h : ∑ i, N i = n}
    {V : ∀ i, Submodule ℂ (Sm E (N i))} {σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E))}
    {m : Fin c → (E →+* ℂ) → Multiset ℂ} (bc : IsBaseChange π h V σ m) (a d : Fin c → ℕ) (P : ∀ i, CuspSub E (a i))
    (hPn : ∀ i, GlobalTheory.DiscSpec.IsNormalised (P i)) (hPs : ∀ i, GlobalTheory.DiscSpec.IsSpehOf (V i) (P i) (d i))
    (hNad : ∀ i, N i = d i * a i) :
    ∃ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i)) (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i))
        (m : Fin c → (E →+* ℂ) → Multiset ℂ) (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (d i * a i)), Parts π a d h P ρ m ∧
        (∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ ∧ GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ) ∧
        ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w)) := by
  have hN : ∀ i, 1 ≤ N i := bc.pos
  have hc : ∀ i, GlobalTheory.DiscSpec.HasSpehComp (V i) (P i) (d i) := fun i =>
    (H E (N i) (hN i)).2.2.2.2 (V i) (bc.discrete i) (a i) (d i) (P i) (hPn i) (hPs i)
  choose ρ σ' hρ hσ' using fun i w => (hc i).exLoc w
  choose m' hm1 hm2 using fun i τ => (hc i).inf τ
  have hmm : ∀ i τ, m i τ = GlobalTheory.DefiniteBC.spehInf (d i) (m' i τ) := fun i τ =>
    (hasInfCharGL_unique (bc.discrete i).ne_bot (bc.inf i τ) (hm2 i τ)).trans (spehInf_eq _ _)
  have hpos : ∀ i, 1 ≤ a i ∧ 1 ≤ d i := fun i => by
    have := hN i
    rw [hNad i] at this
    exact ⟨Nat.one_le_iff_ne_zero.2 fun e => by simp [e] at this, Nat.one_le_iff_ne_zero.2 fun e => by simp [e] at this⟩
  have hcsd : ∀ i, (P i).IsCsd := fun i =>
    GlobalTheory.DiscSpec.isCsd_of_isSpehOf H (hN i) (bc.discrete i) (bc.csd i) (hPn i) (hPs i)
  have hsp : ∀ i w, GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ :=
    fun i w => (hc i).loc w (ρ i w) (σ i w) (hρ i w) (bc.loc i w)
  have hun : ∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ := fun i w =>
    ⟨isUnitarisable_of_isLocComp H (hpos i).1 (P i) (hPn i) w (ρ i w) (hρ i w),
      GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable E (N i) (V i) (bc.discrete i) w (σ i w) (bc.loc i w)⟩
  have hm0 : ∀ i τ, m i τ ≠ 0 := fun i τ h0 => by
    have h1 := (bc.inf i τ).1
    rw [h0, Multiset.card_zero] at h1
    have := hN i
    omega
  obtain rfl : N = fun i => d i * a i := funext hNad
  refine ⟨c, a, d, h, P, ρ, m', σ, ⟨hpos, hcsd, hρ, hm1, fun τ lam hl => ?_, fun i j hd hs => ?_, ?_⟩,
    fun i w => ⟨(hun i w).1, (hun i w).2, hsp i w⟩, bc.split⟩
  · rw [← bc.weight τ lam hl]
    exact Finset.sum_congr rfl fun i _ => (hmm i τ).symm
  · obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨lam, hl⟩ := hW E n hn π hπ τ
    refine GlobalTheory.eq_of_nodup_sum_multiset_of_eq (Fin c) (m · τ) (bc.weight τ lam hl ▸ nodup_infOfWeight lam) i j
      (hm0 i τ) ?_
    rw [hmm i τ, hmm j τ, hd, hasInfChar_eq_of_sigma hs (hm1 i τ) (hm1 j τ)]
  · intro w s ϖ q hs hU α hα
    exact GlobalTheory.T.satakeParameter_spherical_product_spehQuotients E w c n a d h (ρ · w) (σ · w) (fun i => (hpos i).2) (fun i => hsp i w) _
      (bc.inert w s ϖ q hs hU α hα)

end GlobalTheory.BcSpehProof

theorem GlobalTheory.BcSpeh.bcSpeh_of_baseChange : GlobalTheory.Published.BaseChangeDefiniteUnitary → GlobalTheory.Published.DiscreteSpectrumGL → BcSpeh := by
  intro H1 H2 E _ _ _ hE n hn π hπ
  obtain ⟨c, N, h, V, σ, m, bc⟩ := H1 E hE n hn π hπ
  choose a d P _ hPn hPs using fun i => (H2 E (N i) (bc.pos i)).1 (V i) (bc.discrete i)
  exact GlobalTheory.BcSpehProof.baseChange_speh_of_discreteSeries H2 GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary hn hπ bc a d P hPn hPs fun i => (hPs i).mul_eq.symm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.GoodTypeNoChi

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

theorem p_comp : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank),
    LiftsExist V β L → ∀ {G : Type} [Group G] [Fintype G] (eG : G ≃* Formalism.L2.DIV.G0 L.Pg L.r) (c c' : G → ℂ) (F : GA D V → ℂ),
    HasType V β (flag1L L) F →
      gaL V β L eG c (gaL V β L eG c' F) = gaL V β L eG (fun x => ∑ y, c y * c' (y⁻¹ * x)) F := by
  intro D V β L hL G _ _ eG c c' F hF
  have hm : ∀ y z : G, actL V β L (eG y) (actL V β L (eG z) F) = actL V β L (eG (y * z)) F := fun y z => by
    rw [map_mul]
    exact Formalism.IndefR.Eqv.Act.levelGroupAction_mul_of_lifts hL (eG y) (eG z) hF
  have lhs : gaL V β L eG c (gaL V β L eG c' F) =
      ∑ y : G, ∑ z : G, (c y * c' z) • actL V β L (eG (y * z)) F := by

    simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    rw [mul_comm]
  have rhs : gaL V β L eG (fun x => ∑ y, c y * c' (y⁻¹ * x)) F =
      ∑ y : G, ∑ x : G, (c y * c' (y⁻¹ * x)) • actL V β L (eG x) F := by
    simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  rw [lhs, rhs]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun z => by simp

theorem p_lifts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 →
    ∀ (i : Fin D.R.m) (t : T), LiftsExist (Vc D i) (R.βV i) (R.datVt i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h i t
  obtain ⟨c, hc⟩ := h.βV i
  refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_)
    (GlobalTheory.LevelRamif.ramif_at_levels D T R.toLevCh A.μ0 h t i).1
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  rcases hP' with hP' | hP'
  · obtain ⟨k', hk'⟩ := (h.Pg PP').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  · intro hc
    obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (h.Q_pl t) hP'
    exact GlobalTheory.LevelRamif.not_two_primes PP' hq (D.host.g_prime k) (hne k) hm
      (GlobalTheory.LevelRamif.natCast_mem_conj hc (GlobalTheory.LevelRamif.typePrime_mem hk))

theorem isClass_irr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, -, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem charLab_inv {g : ℕ} [Fact g.Prime] {L : LabelDatum g} {θ : (ZMod g)ˣ →* ℂˣ} {c : ZMod g}
    (h : GlobalTheory.GLp.IsCharLab L θ c) : GlobalTheory.GLp.IsCharLab L θ⁻¹ c⁻¹ := by
  obtain ⟨hc, hv⟩ := h
  refine ⟨inv_ne_zero hc, fun u hu => ?_⟩
  have e1 : ((θ⁻¹ u : ℂˣ) : ℂ) = ((θ u : ℂˣ) : ℂ)⁻¹ := by simp
  have hx : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective]
  have e2 : L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c⁻¹) = (L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c))⁻¹ := by
    rw [map_inv₀]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  rw [e1, hv u hu, e2]

theorem seriesKillsAvg : SeriesKillsAvg := by
  intro g _ L r f θ c hc hf hf' a b ha
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := by
    cases r with
    | zero => exact absurd (_root_.funext fun i : Fin 0 => Fin.elim0 i) ha
    | succ n => exact ⟨n, rfl⟩
  obtain ⟨hfin, -⟩ := irr_finite_and_finsum_zOf_eq_one (Gn g (n + 1))
  rw [eSerC_eq_sum L (n + 1) hfin f, Finset.sum_mul]
  refine Finset.sum_eq_zero fun ψ hψ => ?_
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hψ
  obtain ⟨hirr, hlab⟩ := hψ
  apply GlobalTheory.T.centralIdempotent_mul_mirabolicDetAverage_eq_zero g (n + 1) ψ hirr θ a b
  rw [GlobalTheory.T.trace_mirabolicDetCharacterAverage_vector_indep g n ψ (isClass_irr hirr) θ a ha b]
  have hinv := charLab_inv hc
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [(GlobalTheory.T.trace_mirabolicDetAverage_eq_harishChandraRestriction g n ψ θ).1]
    by_contra hne
    obtain ⟨σ, hσ, hip⟩ := (GlobalTheory.T.exists_irr_harishChandraInduction_thetaInv_det g n ψ hirr θ).1 (right_ne_zero_of_mul hne)
    exact hf' ((GlobalTheory.T.detCharacterLabel_root_of_harishChandraConstituent g L n ψ f hirr hlab σ hσ θ⁻¹ c⁻¹ hinv).1 hip)
  · simp only [if_true]
    rw [(GlobalTheory.T.trace_mirabolicDetAverage_eq_harishChandraRestriction g n ψ θ).2]
    by_contra hne
    obtain ⟨σ, hσ, hip⟩ := (GlobalTheory.T.exists_irr_harishChandraInduction_thetaInv_det g n ψ hirr θ).2 (right_ne_zero_of_mul hne)
    exact hf' ((GlobalTheory.T.detCharacterLabel_root_of_harishChandraConstituent g L n ψ f hirr hlab σ hσ θ⁻¹ c⁻¹ hinv).2 hip)

theorem goodNoChi : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GoodNoChi R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t
  have hc : GlobalTheory.Hk3.Core R F := hG.core
  have hl : R.toLevCh.Is A.μ0 := hc.lev
  have hL : LiftsExist (Vc D i) (R.βV i) (R.datVt i t) := p_lifts D G Pl0 T A Ks R hl i t
  intro y hy PP a ha b ε hε l
  have hT : HasType (Vc D i) (R.βV i) (flag1L (R.datVt i t)) (fun h => l (R.extV i t y h)) :=
    GlobalTheory.T.definiteSpace_forms_functional_principalType D G Pl0 T A Ks R F hc i t y l
  have hy' := hy l
  have e1 := p_comp _ _ _ hL R.eG (mirC R i PP a b ε) (RealDat.eC (A := A) (sg0 D A)) _ hT
  have e0 := congrArg (gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (mirC R i PP a b ε)) hy'
  have h0 : (fun x => ∑ y, mirC R i PP a b ε y * RealDat.eC (A := A) (sg0 D A) (y⁻¹ * x)) = fun _ => 0 :=
    funext (GlobalTheory.T.goodProjector_conv_mirabolicAvg_eq_zero seriesKillsAvg D G Pl0 T A Ks R F hG i PP a ha b ε hε)
  have e2 := congrArg (fun c => gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG c (fun h => l (R.extV i t y h))) h0
  have e3 : gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (fun _ : G => (0 : ℂ)) (fun h => l (R.extV i t y h)) = 0 := by
    simp only [gaL, zero_smul, Finset.sum_const_zero, LinearMap.zero_apply]
  exact e0.symm.trans (e1.trans (e2.trans e3))

end GlobalTheory.GoodTypeNoChi

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.exists_newPlace_frobeniusConjugate_modOpenNormalSubgroup : Cheb → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → n < R → ∀ (H : Subgroup (GE N)) (S : Finset (PlE D.host)), AdmFam X i M H S d → L ≤ H → ∀ (U : Subgroup (GE N)) (h : GE N), IsOpen (U : Set (GE N)) → U.Normal → U ≤ L → h ∈ L → (∀ b : Fin R, b.val < n → d (P (.inl b)) h = 1) → (∀ b : Fin R, n ≤ b.val → Ine (F := D.host.E) (N.plOm.1 (P (.inl b))) ≤ U) → ∃ P' : Fin R ⊕ Fin (n + 1) → PlE D.host, Ext P P' ∧ PiLocalization₂ i M d A₀ L z P' ∧ ∃ σ γ g : GE N, NewPl i M L (P' (.inr (Fin.last n))) (d (P' (.inr (Fin.last n)))) σ γ ∧ d (P' (.inr (Fin.last n))) σ = 1 ∧ g * σ * g⁻¹ * h⁻¹ ∈ U := by
  first | exact @GlobalTheory.NewPrimePick.exists_newPlace | exact GlobalTheory.NewPrimePick.exists_newPlace | (intros; apply GlobalTheory.NewPrimePick.exists_newPlace <;> assumption)
end
