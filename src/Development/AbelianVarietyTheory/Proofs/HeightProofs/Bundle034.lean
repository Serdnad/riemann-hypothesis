module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle004
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle033
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Formalism.SatakeDualWeyl.Statement
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle002
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_real_chart_infiniteAdeles_cmType : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (Function.Bijective fun τ : D.what₂.Tau => NumberField.InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) → ∃ ρ : (D.what₂.Tau → ℝ) →+ Ainf D.host.F, Continuous ρ ∧ (∀ x τ, θ τ (ρ x ⊗ₜ[D.host.F] (1 : D.host.E)) = (x τ : ℂ)) ∧ ∀ a : Ainf D.host.F, (∀ τ, θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 0) → a = 0 := by
  first | exact @GlobalTheory.FockCompare.exists_real_chart | exact GlobalTheory.FockCompare.exists_real_chart | (intros; apply GlobalTheory.FockCompare.exists_real_chart <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}

theorem isThetaFun_zero : IsThetaFun ψ V W 0 := {
  quasi γ w := by simp
  level := ⟨⊤, by change IsOpen (Set.univ : Set (WA V W)); exact isOpen_univ, fun u _ _ => by funext w; simp [Heisenberg₂]⟩
  cont := continuous_const
  smooth _ _ _ _ _ := contDiff_const }

theorem isThetaFun_add {f g : WA V W → ℂ} (hf : IsThetaFun ψ V W f) (hg : IsThetaFun ψ V W g) :
    IsThetaFun ψ V W (f + g) := {
  quasi γ w := by simp only [Pi.add_apply, hf.quasi γ w, hg.quasi γ w, mul_add]
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    obtain ⟨U', hU'o, hU'⟩ := hg.level
    refine ⟨U ⊓ U', by change IsOpen ((U : Set (WA V W)) ∩ (U' : Set (WA V W))); exact hUo.inter hU'o, fun u hu hinf => ?_⟩
    have e1 := hU u (AddSubgroup.mem_inf.1 hu).1 hinf
    have e2 := hU' u (AddSubgroup.mem_inf.1 hu).2 hinf
    funext w
    have h1 := congrFun e1 w
    have h2 := congrFun e2 w
    simp only [Heisenberg₂, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  cont := hf.cont.add hg.cont
  smooth k L hL hfin w := (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w) }

theorem isThetaFun_smul (c : ℂ) {f : WA V W → ℂ} (hf : IsThetaFun ψ V W f) :
    IsThetaFun ψ V W (c • f) := {
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul, hf.quasi γ w, mul_left_comm]
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hinf => ?_⟩
    funext w
    have h1 := congrFun (hU u hu hinf) w
    simp only [Heisenberg₂, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [mul_left_comm, h1]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := contDiff_const.mul (hf.smooth k L hL hfin w) }

theorem exists_thetaSubmodule : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D),
    ∃ M : Submodule ℂ (WA V W → ℂ), ∀ f, f ∈ M ↔ IsThetaFun ψ V W f := by
  intro D ψ V W
  refine ⟨{ carrier := {f | IsThetaFun ψ V W f}
            add_mem' := fun hf hg => isThetaFun_add hf hg
            zero_mem' := isThetaFun_zero
            smul_mem' := fun c _ hf => isThetaFun_smul c hf }, fun f => Iff.rfl⟩

end GlobalTheory.FockCompare
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem map_trace_tensor {F E A B : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (p : A →ₐ[F] B) (z : A ⊗[F] E) :
    p (Algebra.trace A (A ⊗[F] E) z) =
      Algebra.trace B (B ⊗[F] E) (Algebra.TensorProduct.map p (AlgHom.id F E) z) := by
  have key : ∀ (C : Type) [CommRing C] [Algebra F C] (c : C) (e : E),
      Algebra.trace C (C ⊗[F] E) (c ⊗ₜ[F] e) = c * algebraMap F C (Algebra.trace F E e) := by
    intro C _ _ c e
    have h1 : (c ⊗ₜ[F] e : C ⊗[F] E) = c • ((1 : C) ⊗ₜ[F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, smul_eq_mul]
    congr 1
    rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
    congr 1
    ext x
    simp
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e => rw [Algebra.TensorProduct.map_tmul, key, key, map_mul, AlgHom.commutes]; rfl

theorem map_sesq_sum_eq_zero {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (q : A →+* B) (σ : A →+* A)
    (hσ : ∀ z, q z = 0 → q (σ z) = 0) (a : Fin m → Fin m → A) (b : Fin n → Fin n → A)
    (x y : Matrix (Fin m) (Fin n) A) (h : x.map q = 0 ∨ y.map q = 0) :
    q (∑ i, ∑ j, ∑ k, ∑ l, σ (y i j) * a k i * b j l * x k l) = 0 := by
  have hk : ∀ i j k l (a b : A), q (σ (y i j) * a * b * x k l) = 0 := by
    intro i j k l a b
    rw [map_mul, map_mul, map_mul]
    rcases h with h | h
    · have h1 : q (x k l) = 0 := congrFun (congrFun h k) l
      rw [h1, mul_zero]
    · have h1 : q (y i j) = 0 := congrFun (congrFun h i) j
      rw [hσ _ h1, zero_mul, zero_mul, zero_mul]

  simp only [map_sum, hk, Finset.sum_const_zero]

theorem map_trace_sesq_eq_zero {F E A B : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (p : A →ₐ[F] B) (s : E →ₐ[F] E) {m n : ℕ}
    (c : A ⊗[F] E) (a : Fin m → Fin m → A ⊗[F] E) (b : Fin n → Fin n → A ⊗[F] E)
    (x y : Matrix (Fin m) (Fin n) (A ⊗[F] E))
    (h : x.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0 ∨
      y.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0) :
    p (Algebra.trace A (A ⊗[F] E) (c * ∑ i, ∑ j, ∑ k, ∑ l, sigR A s (y i j) * a k i * b j l * x k l)) = 0 := by
  have hc : ∀ z : A ⊗[F] E, (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom (sigR A s z) =
      sigR B s ((Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [RingHom.map_zero]
    | add a b ha hb => simp only [RingHom.map_add (f := _), ha, hb]
    | tmul a e => rfl
  have hh := map_sesq_sum_eq_zero (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom (sigR A s)
    (fun z hz => by rw [hc, hz, map_zero]) a b x y h
  rw [map_trace_tensor, map_mul]
  erw [hh]
  rw [mul_zero, map_zero]

variable {D : D7}

theorem map_sympl_eq_zero {B : Type} [CommRing B] [Algebra D.host.F B] (p : AF D.host.F →ₐ[D.host.F] B)
    (V W : HSp D) (x y : WA V W)
    (h : x.map (Algebra.TensorProduct.map p (AlgHom.id D.host.F D.host.E)).toRingHom = 0 ∨
      y.map (Algebra.TensorProduct.map p (AlgHom.id D.host.F D.host.E)).toRingHom = 0) :
    p (sympl V W x y) = 0 := by
  unfold sympl hHom
  split_ifs
  · exact map_trace_sesq_eq_zero p D.sp.cm.sig _ (fun k i => incA D (V.gram k i))
      (fun j l => incA D (W.gram j l)) x y h
  · exact map_trace_sesq_eq_zero p D.sp.cm.sig _ (fun k i => incA D (V.gram i k))
      (fun j l => incA D (W.gram l j)) x y h

theorem sympl_parts (D : D7) (V W : HSp D) (x y : WA V W) :
    ((IsRealW V W x ∨ IsRealW V W y) → sndA D.host.F (sympl V W x y) = 0) ∧
      ((x.map (infPart D) = 0 ∨ y.map (infPart D) = 0) → fstA D.host.F (sympl V W x y) = 0) :=
  ⟨fun h => map_sympl_eq_zero (sndA D.host.F) V W x y h, fun h => map_sympl_eq_zero (fstA D.host.F) V W x y h⟩

end GlobalTheory.FockCompare
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem dRho_quasi_and_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L : ℝ →+ WA V W) (f : WA V W → ℂ), ((∀ γ w, f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * f w) → ∀ γ w, dRho ψ V W L f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * dRho ψ V W L f w) ∧ ∀ u : WA V W, (∀ t, symplH V W u (L t) = 0 ∧ symplH V W (L t) u = 0) → Heisenberg₂ ψ V W u f = f → Heisenberg₂ ψ V W u (dRho ψ V W L f) = dRho ψ V W L f := by
  intro D ψ V W L f
  refine ⟨fun hf γ w => ?_, fun u hu hf => ?_⟩
  · unfold dRho
    rw [← deriv_const_mul_field]
    congr 1
    funext t
    exact GlobalTheory.DualPairCheck.heis_quasi ψ V W (L t) f hf γ w
  · funext w
    have key : ∀ t, Heisenberg₂ ψ V W u (Heisenberg₂ ψ V W (L t) f) = Heisenberg₂ ψ V W (L t) f := by
      intro t
      conv_rhs => rw [← hf]
      rw [GlobalTheory.DualPairCheck.heis_heis, GlobalTheory.DualPairCheck.heis_heis, (hu t).1, (hu t).2, add_comm]
    have : (fun t => Heisenberg₂ ψ V W (L t) f w) = fun t => Heisenberg₂ ψ V W u (Heisenberg₂ ψ V W (L t) f) w := by
      funext t; rw [key]
    conv_rhs => unfold dRho; rw [this]
    unfold dRho
    rw [Heisenberg₂, ← deriv_const_mul_field]
    rfl

end GlobalTheory.FockCompare
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MonomialSign

theorem diagonal_mul_eq {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (hcard : Fintype.card κ = Fintype.card ι) (ε : ι → ℝ) (hε : ∀ a, ε a = 1 ∨ ε a = -1)
    (M : Matrix ι κ ℂ) (d : κ → ℝ) (hd : ∀ i, d i ≠ 0)
    (hM : Mᴴ * Matrix.diagonal (fun a => (ε a : ℂ)) * M = Matrix.diagonal (fun i => (d i : ℂ)))
    (hrow : ∀ a i j, M a i ≠ 0 → M a j ≠ 0 → i = j) :
    Matrix.diagonal (fun a => (ε a : ℂ)) * M
      = M * Matrix.diagonal (fun i => if 0 < d i then (1 : ℂ) else -1) := by
  have hsum : ∀ i, d i = ∑ a, ε a * Complex.normSq (M a i) := by
    intro i
    have h := congrFun (congrFun hM i) i
    rw [Matrix.diagonal_apply_eq, Matrix.mul_apply] at h
    apply Complex.ofReal_injective
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self,
      Complex.star_def]
    ring
  have hex : ∀ i, ∃ a, M a i ≠ 0 := by
    intro i
    by_contra hne
    push Not at hne
    apply hd i
    rw [hsum i]
    simp [hne]
  choose r hr using hex
  have hinj : Function.Injective r := fun i j hij => hrow (r i) i j (hr i) (hij ▸ hr j)
  have hbij : Function.Bijective r :=
    (Fintype.bijective_iff_injective_and_card r).2 ⟨hinj, hcard⟩
  have huniq : ∀ a i, M a i ≠ 0 → a = r i := by
    intro a i h
    obtain ⟨j, rfl⟩ := hbij.2 a
    rw [hrow (r j) i j h (hr j)]
  ext a i
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : M a i = 0
  · simp [h]
  · have ha := huniq a i h
    have hdi : d i = ε a * Complex.normSq (M a i) := by
      rw [hsum i]
      refine Finset.sum_eq_single a (fun b _ hb => ?_) (by simp)
      have : M b i = 0 := by
        by_contra hb'
        exact hb ((huniq b i hb').trans ha.symm)
      simp [this]
    have hpos : 0 < Complex.normSq (M a i) := Complex.normSq_pos.2 h
    rcases hε a with h1 | h1
    · have : 0 < d i := by rw [hdi, h1]; linarith
      simp [this, h1]
    · have : ¬ 0 < d i := by rw [hdi, h1]; linarith
      simp [this, h1]

theorem Jpq_mul_eq : ∀ (n p q : ℕ), p + q = n → ∀ (M : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (d : Fin n → ℝ), (∀ i, d i ≠ 0) → Mᴴ * Formalism.UG.Jpq p q * M = Matrix.diagonal (fun i => (d i : ℂ)) → (∀ a i j, M a i ≠ 0 → M a j ≠ 0 → i = j) → Formalism.UG.Jpq p q * M = M * Matrix.diagonal (fun i => if 0 < d i then (1 : ℂ) else -1) := by
  intro n p q hn M d hd hM hrow
  have hJ : Formalism.UG.Jpq p q = Matrix.diagonal
      (fun a => ((Sum.elim (fun _ => 1) (fun _ => -1) a : ℝ) : ℂ)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hJ] at hM ⊢
  refine diagonal_mul_eq (by simp [hn]) _ ?_ M d hd hM hrow
  rintro (a | a) <;> simp

end GlobalTheory.MonomialSign
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_le_of_continuous_of_spanning_periods : ∀ (R : Type) [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (g : R → ℝ), Continuous g → ∀ S : Set R, Submodule.span ℝ S = ⊤ → (∀ s ∈ S, ∃ N : ℕ, 0 < N ∧ ∀ x, g (x + (N : ℝ) • s) = g x) → ∃ C : ℝ, ∀ x, g x ≤ C := by
  first | exact @GlobalTheory.bddAbove_of_spanning_periods | exact GlobalTheory.bddAbove_of_spanning_periods | (intros; apply GlobalTheory.bddAbove_of_spanning_periods <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeylNumber

theorem exists_parseval_family {R : Type} [AddCommGroup R] [Module ℝ R] [FiniteDimensional ℝ R]
    (g : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (hs : ∀ u v, g u v = g v u) (hp : ∀ u, u ≠ 0 → 0 < g u u) :
    ∃ (n : ℕ) (e : Fin n → R), ∀ x, ∑ k, g x (e k) • e k = x := by
  first
  | exact @_root_.GlobalTheory.PolynomialCoeffEq.main
  | exact _root_.GlobalTheory.PolynomialCoeffEq.main
  | (apply _root_.GlobalTheory.PolynomialCoeffEq.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialCoeffEq.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialCoeffEq.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialCoeffEq.main ..)

theorem weyl_number : ∀ (M R : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℝ R] [FiniteDimensional ℝ R] (Dop : R → Module.End ℂ M) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (κ : ℂ) (j : R →ₗ[ℝ] R), (∀ u v, Dop (u + v) = Dop u + Dop v) → (∀ (c : ℝ) u, Dop (c • u) = (c : ℂ) • Dop u) → κ ≠ 0 → (∀ u v, Dop u * Dop v - Dop v * Dop u = (κ * (om u v : ℝ)) • (1 : Module.End ℂ M)) → (∀ u v, om v u = -om u v) → (∀ u, j (j u) = -u) → (∀ u v, om (j u) (j v) = om u v) → (∀ u, u ≠ 0 → 0 < om u (j u)) → (∀ u v, ∃ β : ℂ, (Dop u + Complex.I • Dop (j u)) * (Dop v - Complex.I • Dop (j v)) - (Dop v - Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) = β • (1 : Module.End ℂ M)) ∧ ∃ (n : ℕ) (e : Fin n → R) (lam : ℂ), lam ≠ 0 ∧ ∀ u, (Dop u + Complex.I • Dop (j u)) * (∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) = ((∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) + lam • (1 : Module.End ℂ M)) * (Dop u + Complex.I • Dop (j u)) := by
  intro M R _ _ _ _ _ Dop om κ j hadd hsmul hκ hcomm hanti hjj hom hpos
  have h1 : ∀ u v, om (j u) v = -om u (j v) := fun u v => by
    rw [← hom (j u) v, hjj]; simp
  have hc : ∀ u v, Dop u * Dop v = Dop v * Dop u + (κ * (om u v : ℝ)) • (1 : Module.End ℂ M) :=
    fun u v => by rw [← hcomm]; abel
  have hneg : ∀ u, Dop (-u) = -Dop u := fun u => by
    have := hsmul (-1) u
    simpa using this
  have hac : ∀ u v, (Dop u + Complex.I • Dop (j u)) * (Dop v - Complex.I • Dop (j v)) =
      (Dop v - Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) +
        (2 * κ * ((om u v : ℝ) - Complex.I * (om u (j v) : ℝ))) • (1 : Module.End ℂ M) := by
    intro u v
    simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
      Complex.I_mul_I]
    rw [hc u v, hc u (j v), hc (j u) v, hc (j u) (j v), hom, h1]
    push_cast
    match_scalars <;> (try ring_nf) <;> (try simp) <;> (try ring)
  have haa : ∀ u v, (Dop u + Complex.I • Dop (j u)) * (Dop v + Complex.I • Dop (j v)) =
      (Dop v + Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) := by
    intro u v
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      Complex.I_mul_I]
    rw [hc u v, hc u (j v), hc (j u) v, hc (j u) (j v), hom, h1]
    push_cast
    match_scalars <;> (try ring_nf) <;> (try simp) <;> (try ring)
  refine ⟨fun u v => ⟨_, by rw [hac u v, add_sub_cancel_left]⟩, ?_⟩
  obtain ⟨n, e, he⟩ := exists_parseval_family (om.compl₂ j)
    (fun u v => by
      simp only [LinearMap.compl₂_apply]
      rw [hanti (j u) v, h1, neg_neg])
    (fun u hu => by simpa using hpos u hu)
  simp only [LinearMap.compl₂_apply] at he
  let A : R →+ Module.End ℂ M := AddMonoidHom.mk' (fun u => Dop u + Complex.I • Dop (j u))
    (fun u v => by simp only [map_add (f := _), hadd, smul_add]; abel)
  have hA : ∀ u, A u = Dop u + Complex.I • Dop (j u) := fun _ => rfl
  have hAs : ∀ (c : ℝ) u, A (c • u) = (c : ℂ) • A u := fun c u => by
    simp only [hA, map_smul, hsmul]; module
  have hAj : ∀ u, A (j u) = (-Complex.I) • A u := fun u => by
    simp only [hA, hjj, hneg, smul_add, smul_smul, neg_mul, Complex.I_mul_I]
    module
  have hsum : ∀ x, ∑ k, ((om x (j (e k)) : ℝ) : ℂ) • A (e k) = A x := fun x => by

    conv_rhs => rw [← he x, map_sum]
    simp only [hAs]
  refine ⟨n, e, -4 * Complex.I * κ, by simp [hκ], fun u => ?_⟩
  have key : ∀ k, A u * ((Dop (e k) - Complex.I • Dop (j (e k))) * A (e k)) =
      ((Dop (e k) - Complex.I • Dop (j (e k))) * A (e k)) * A u +
        ((2 * κ) • (((om (j u) (j (e k)) : ℝ) : ℂ) • A (e k))
          - (2 * κ * Complex.I) • (((om u (j (e k)) : ℝ) : ℂ) • A (e k))) := fun k => by
    rw [← mul_assoc, hA u, hac, add_mul, mul_assoc, mul_assoc, hA (e k), haa u, hom,
      smul_mul_assoc, one_mul]
    module
  simp only [← hA]
  rw [Finset.mul_sum, add_mul, Finset.sum_mul, Finset.sum_congr rfl fun k _ => key k,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
    hsum, hsum, hAj, smul_mul_assoc, one_mul]
  module

end GlobalTheory.WeylNumber
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.Jpq_mul_monomial_eq_mul_sign_diagonal : ∀ (n p q : ℕ), p + q = n → ∀ (M : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (d : Fin n → ℝ), (∀ i, d i ≠ 0) → Mᴴ * Formalism.UG.Jpq p q * M = Matrix.diagonal (fun i => (d i : ℂ)) → (∀ a i j, M a i ≠ 0 → M a j ≠ 0 → i = j) → Formalism.UG.Jpq p q * M = M * Matrix.diagonal (fun i => if 0 < d i then (1 : ℂ) else -1) := by
  first | exact @GlobalTheory.MonomialSign.Jpq_mul_eq | exact GlobalTheory.MonomialSign.Jpq_mul_eq | (intros; apply GlobalTheory.MonomialSign.Jpq_mul_eq <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.canonicalCommutationRelations_weylNumber : ∀ (M R : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℝ R] [FiniteDimensional ℝ R] (Dop : R → Module.End ℂ M) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (κ : ℂ) (j : R →ₗ[ℝ] R), (∀ u v, Dop (u + v) = Dop u + Dop v) → (∀ (c : ℝ) u, Dop (c • u) = (c : ℂ) • Dop u) → κ ≠ 0 → (∀ u v, Dop u * Dop v - Dop v * Dop u = (κ * (om u v : ℝ)) • (1 : Module.End ℂ M)) → (∀ u v, om v u = -om u v) → (∀ u, j (j u) = -u) → (∀ u v, om (j u) (j v) = om u v) → (∀ u, u ≠ 0 → 0 < om u (j u)) → (∀ u v, ∃ β : ℂ, (Dop u + Complex.I • Dop (j u)) * (Dop v - Complex.I • Dop (j v)) - (Dop v - Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) = β • (1 : Module.End ℂ M)) ∧ ∃ (n : ℕ) (e : Fin n → R) (lam : ℂ), lam ≠ 0 ∧ ∀ u, (Dop u + Complex.I • Dop (j u)) * (∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) = ((∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) + lam • (1 : Module.End ℂ M)) * (Dop u + Complex.I • Dop (j u)) := by
  first | exact @GlobalTheory.WeylNumber.weyl_number | exact GlobalTheory.WeylNumber.weyl_number | (intros; apply GlobalTheory.WeylNumber.weyl_number <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_submodule_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D), ∃ M : Submodule ℂ (WA V W → ℂ), ∀ f, f ∈ M ↔ IsThetaFun ψ V W f := by
  first | exact @GlobalTheory.FockCompare.exists_thetaSubmodule | exact GlobalTheory.FockCompare.exists_thetaSubmodule | (intros; apply GlobalTheory.FockCompare.exists_thetaSubmodule <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenbergDerivative_quasiInvariant_and_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L : ℝ →+ WA V W) (f : WA V W → ℂ), ((∀ γ w, f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * f w) → ∀ γ w, dRho ψ V W L f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * dRho ψ V W L f w) ∧ ∀ u : WA V W, (∀ t, symplH V W u (L t) = 0 ∧ symplH V W (L t) u = 0) → Heisenberg₂ ψ V W u f = f → Heisenberg₂ ψ V W u (dRho ψ V W L f) = dRho ψ V W L f := by
  first | exact @GlobalTheory.FockCompare.dRho_quasi_and_level | exact GlobalTheory.FockCompare.dRho_quasi_and_level | (intros; apply GlobalTheory.FockCompare.dRho_quasi_and_level <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.symplectic_real_part_vanish : ∀ (D : D7) (V W : HSp D) (x y : WA V W), ((IsRealW V W x ∨ IsRealW V W y) → sndA D.host.F (sympl V W x y) = 0) ∧ ((x.map (infPart D) = 0 ∨ y.map (infPart D) = 0) → fstA D.host.F (sympl V W x y) = 0) := by
  first | exact @GlobalTheory.FockCompare.sympl_parts | exact GlobalTheory.FockCompare.sympl_parts | (intros; apply GlobalTheory.FockCompare.sympl_parts <;> assumption)

end
end
