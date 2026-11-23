module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle320
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle296
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.parabolic_proj_unipotent_character_compat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (m j : ℕ) (u : MirUin k (m + (j + 1)))
    (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
    (gpProj k m (j + 1) ⟨u, hh⟩).1 = 1 ∧ ∃ hv : (gpProj k m (j + 1) ⟨u, hh⟩).2 ∈ MirUin k (j + 1),
      mirChar k ψ j ⟨_, hv⟩ = mirChar k ψ (m + j) u := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.gpProj_mirUin_char | exact GlobalTheory.CompanionTheory.LeibPhi.gpProj_mirUin_char | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.gpProj_mirUin_char <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

theorem _root_.GlobalTheory.T.derivative_zero_whittaker_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), twKer π (derUnip k N 0) (derChar k ψ N 0) = twKer π (unipB k (Fin N)) (whitChar ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero | exact GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero | (intros; apply GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

theorem _root_.GlobalTheory.T.mirabolic_twisted_kernel_derivative_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V), twKer τ (MirUin k n) 1 = twKer τ (derUnipM k n n) (derCharM k ψ n n) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM | exact GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM | (intros; apply GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

theorem _root_.GlobalTheory.T.restriction_mirabolic_twisted_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (m n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (m + 1)) k) V), twKer (resM k π).ρ (derUnipM k m n) (derCharM k ψ m n) = twKer π (derUnip k (m + 1) n) (derChar k ψ (m + 1) n) := by
  first | exact @GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM | exact GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM | (intros; apply GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JCScalar

theorem piTensor_zj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL (k := k)) (t : kˣ) (c : Fin h → ℂ), (∀ i, Zl.ScalarBy (x i) t (c i)) → ∀ (j : Fin h) (v : PiTensorProduct ℂ (fun a => (x a).2.rep.V)), piTensor (fun a => (x a).rep) (Zl.JC.zj (fun a => (x a).1) t j) v = (∏ i ∈ Finset.univ.filter (· ≤ j), c i) • v := by
  intro k _ _ _ _ h x t c hc j v
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, smul_comm, piTensor_tprod]
    congr 1
    have hf : ∀ a, (x a).rep (Zl.JC.zj (fun a => (x a).1) t j a) (f a)
        = (if a ≤ j then c a else 1) • f a := by
      intro a
      by_cases ha : a ≤ j
      · simp only [Zl.JC.zj, if_pos ha]
        exact hc a (f a)
      · simp [Zl.JC.zj, if_neg ha]
    simp only [hf]
    rw [MultilinearMap.map_smul_univ, Finset.prod_filter]
    simp only [RingHom.id_apply]
  | add a b ha hb => rw [map_add (f := _), ha, hb, smul_add]

end GlobalTheory.CompanionTheory.JCScalar
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.ScalarUniq

theorem scalarBy_unique (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (t : kˣ) (c c' : ℂ) (h : Zl.ScalarBy x t c) (h' : Zl.ScalarBy x t c') : c = c' := by
  have hirr : x.rep.IsIrreducible := x.2.rep.irr
  have hnt : Nontrivial x.2.rep.V := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    obtain ⟨a, b, hab⟩ := (hirr.toNontrivial : Nontrivial (Subrepresentation x.rep)).exists_pair_ne
    refine hab ?_
    ext v
    simp [Subsingleton.elim v 0]
  obtain ⟨v, hv⟩ := exists_ne (0 : x.2.rep.V)
  have e : c • v = c' • v := (h v).symm.trans (h' v)
  exact smul_left_injective ℂ hv e

end GlobalTheory.CompanionTheory.ScalarUniq
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.ZCentre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem scalar_apply {R : Type} [Field R] {n : Type} [Fintype n] [DecidableEq n] (t : Rˣ) (i j : n) :
    ((Matrix.GeneralLinearGroup.scalar n t : GL n R) : Matrix n n R) i j = if i = j then (t : R) else 0 := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem det_scalar {R : Type} [Field R] {n : Type} [Fintype n] [DecidableEq n] (t : Rˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar n t : GL n R) = t ^ Fintype.card n := by
  ext; simp [Matrix.GeneralLinearGroup.scalar]

theorem scalar_comm {R : Type} [Field R] {n : Type} [Fintype n] [DecidableEq n] (t : Rˣ) (g : GL n R) :
    g * Matrix.GeneralLinearGroup.scalar n t = Matrix.GeneralLinearGroup.scalar n t * g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, mul_comm]

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

theorem sum_card_mul_modExp : ∑ a, (Fintype.card (m a) : ℤ) * modExp m a = 0 := by
  simp only [modExp, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp [mul_comm]


variable (k) in
theorem deltaHalf_scalar (t : kˣ) :
    deltaHalf k m (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) = 1 := by
  have h1 : modulus k m (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) = 1 := by
    have h2 : ∀ a, nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (m a) t : GL (m a) k)) ^ modExp m a =
        nabs k t ^ ((Fintype.card (m a) : ℤ) * modExp m a) := fun a => by
      rw [det_scalar, zpow_mul, zpow_natCast]
      congr 1
      simp [nabs]
    simp only [modulus, h2]
    have h3 : ∀ (s : Finset α) (f : α → ℤ), ∏ a ∈ s, nabs k t ^ f a = nabs k t ^ ∑ a ∈ s, f a := fun s f => by
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ (nabs_pos' k t).ne', ih]
    rw [h3, sum_card_mul_modExp, zpow_zero]
  refine Units.ext ?_
  rw [val_deltaHalf, h1]
  simp

theorem piTensor_scalar {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : α → ℂ)
    (h : ∀ a v, ρ a (g a) v = c a • v) (w : PiTensorProduct ℂ X) :
    piTensor ρ g w = (∏ a, c a) • w := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, piTensor_tprod, smul_comm]
    congr 1
    simp only [h]
    exact MultilinearMap.map_smul_univ _ _ _
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]

theorem scalar_mem_parab (e : (Σ a, m a) ≃ n) (t : kˣ) :
    Matrix.GeneralLinearGroup.scalar n t ∈ parab k e := by
  refine mem_parab.2 fun i j hij => ?_
  rw [scalar_apply, if_neg]
  rintro rfl
  exact lt_irrefl _ hij

theorem leviProj_scalar (e : (Σ a, m a) ≃ n) (t : kˣ) :
    leviProj k e ⟨_, scalar_mem_parab e t⟩ = fun a => Matrix.GeneralLinearGroup.scalar (m a) t := by
  funext a
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [leviProj_apply, scalar_apply, scalar_apply]
  simp

theorem parInd_scalar {W : Type} [AddCommGroup W] [Module ℂ W] (e : (Σ a, m a) ≃ n)
    (ρ : Representation ℂ (Levi k m) W) (t : kˣ) (c : ℂ)
    (h : ∀ w, ρ (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) w = c • w) (f : IndSp e ρ) :
    parInd e ρ (Matrix.GeneralLinearGroup.scalar n t) f = c • f := by
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  have h1 := parInd_law e ρ f ⟨_, scalar_mem_parab e t⟩ g
  rw [leviProj_scalar, deltaHalf_scalar, h] at h1
  rw [parInd_apply, scalar_comm]
  simpa using h1

theorem prodIrr_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (t : kˣ) (c : Fin h → ℂ),
    (∀ a, Zl.ScalarBy (x a) t (c a)) →
      ∀ v, prodIrr x hd (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = (∏ a, c a) • v := by
  intro k _ _ _ _ h N x hd t c hc v
  exact parInd_scalar _ _ t _ (fun w => piTensor_scalar _ _ c (fun a v => hc a v) w) v

end GlobalTheory.CompanionTheory.ZCentre

end
end

section

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel Matrix

namespace GlobalTheory.CompanionTheory.ScalarTwist

theorem acts_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) {g : G} {c : ℂ}
    (h : ∀ v, ρ g v = c • v) (w : W) : σ g w = c • w := by
  obtain ⟨v, rfl⟩ := φ.toLinearEquiv.surjective w
  show σ g (φ.toIntertwiningMap v) = c • φ.toIntertwiningMap v
  rw [← φ.toIntertwiningMap.isIntertwining, h, map_smul]

theorem scalarBy_nu (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (t : kˣ) (c s : ℂ) (h : Zl.ScalarBy x t c) :
    Zl.ScalarBy (x.nu s) t (c * ((absPow k s t : ℂˣ) : ℂ) ^ x.1) := by
  have hdet : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin x.1) t) = t ^ x.1 := by
    ext; simp [GeneralLinearGroup.scalar]
  refine acts_of_equiv (x.twEquiv (absPow k s) (isSmoothChar_absPow s)) (g := GeneralLinearGroup.scalar (Fin x.1) t) ?_
  intro v
  rw [twist_apply, h v, detChar_apply, hdet, smul_smul]
  simp [mul_comm]

end GlobalTheory.CompanionTheory.ScalarTwist
end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.Dblock

theorem smul_of_equiv_nu {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) (g : G) (c : ℂ)
    (h : ∀ v, π g v = c • v) (w : W) : σ g w = c • w := by
  rw [← Representation.Equiv.conj_apply_self g φ, LinearEquiv.conj_apply]
  simp [h]
  congr 1
  exact φ.right_inv w

theorem scalarBy_nu : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (s : ℂ) (t : kˣ) (c : ℂ), Zl.ScalarBy x t c →
      Zl.ScalarBy (x.nu s) t (c * ((absPow k s (t ^ x.1) : ℂˣ) : ℂ)) := by
  intro k _ _ _ _ x s t c hx v
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin x.1) t) = t ^ x.1 := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
  refine smul_of_equiv_nu (x.twEquiv (absPow k s) (isSmoothChar_absPow s))
    (Matrix.GeneralLinearGroup.scalar (Fin x.1) t) _ (fun u => ?_) v
  rw [GlobalTheory.SmGL.twist_apply, GlobalTheory.SmGL.detChar_apply, hx u, smul_smul, hdet, mul_comm]

end GlobalTheory.CompanionTheory.Dblock
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.ScalarEx

theorem exists_scalarBy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (t : kˣ), ∃ c : ℂ, Zl.ScalarBy x t c := by
  intro k _ _ _ _ x t
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar x.2.rep.smooth x.2.rep.irr
  exact ⟨(ω t : ℂ), fun v => hω t v⟩

end GlobalTheory.CompanionTheory.ScalarEx
end

section

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.JacCentral

theorem subQuot_apply_of_smul {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S T : Subrepresentation ρ) {g : G} {c : ℂ}
    (h : ∀ v, ρ g v = c • v) (y : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) :
    subQuot S T g y = c • y := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hs : S.toRepresentation g s = c • s := Subtype.ext (h s)
  show Submodule.Quotient.mk (S.toRepresentation g s) = _
  rw [hs, Submodule.Quotient.mk_smul]

theorem exists_step_of_jhMult_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : jhMult σ ρ ≠ 0) :
    ∃ S T : Subrepresentation ρ, Nonempty ((subQuot S T).Equiv σ) := by
  by_contra hc
  refine h (le_antisymm (iSup₂_le fun r hr => ?_) bot_le)
  rcases Nat.eq_zero_or_pos r with rfl | hpos
  · simp
  · obtain ⟨S, T, -, -, hi⟩ := hr
    exact absurd ⟨S ⟨0, hpos⟩, T ⟨0, hpos⟩, hi ⟨0, hpos⟩⟩ hc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem leviEmb_scalar {s N : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = N) (t : kˣ) :
    leviEmb k (stdBlocks d hd) (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) =
      Matrix.GeneralLinearGroup.scalar (Fin N) t := by
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  · rw [leviEmb_apply_ne k _ _ hab]
    have : (stdBlocks d hd) ⟨a, i⟩ ≠ (stdBlocks d hd) ⟨b, j⟩ := fun h => by
      have := (stdBlocks d hd).injective h
      exact hab (congrArg Sigma.fst this)
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, this]

theorem nabs_det_scalar (n : ℕ) (t : kˣ) :
    nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) t)) =
      nabs k t ^ n := by
  have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) t) = t ^ n := by
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  rw [this]
  simp [nabs]

theorem deltaHalf_scalar (d : Fin 2 → ℕ) (t : kˣ) :
    deltaHalf k (fun a => Fin (d a))
      (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = 1 := by
  have h0 : modExp (fun a => Fin (d a)) (0 : Fin 2) = d 1 := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have h1 : modExp (fun a => Fin (d a)) (1 : Fin 2) = -(d 0 : ℤ) := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have hm : modulus k (fun a => Fin (d a))
      (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = 1 := by
    have hp := (nabs_pos' k t).ne'
    rw [modulus, Fin.prod_univ_two, h0, h1, nabs_det_scalar, nabs_det_scalar, zpow_natCast, zpow_neg,
      zpow_natCast, ← pow_mul, ← pow_mul, mul_comm (d 0) (d 1)]
    exact mul_inv_cancel₀ (pow_ne_zero _ hp)
  apply Units.ext
  rw [val_deltaHalf, hm]
  simp

theorem piTensor_apply_of_smul {h : ℕ} (x : Fin h → IrrGL (k := k)) (g : ∀ a, GL (Fin (x a).1) k)
    (c : Fin h → ℂ) (hc : ∀ a v, (x a).rep (g a) v = c a • v)
    (w : PiTensorProduct ℂ (fun a => (x a).2.rep.V)) :
    piTensor (fun a => (x a).rep) g w = (∏ a, c a) • w := by
  induction w using PiTensorProduct.induction_on with
  | add y z hy hz => rw [map_add (f := _), hy, hz, smul_add]
  | smul_tprod r y =>
    rw [map_smul, piTensor_tprod, smul_comm]
    congr 1
    simp only [hc]
    exact MultilinearMap.map_smul_univ _ _ _

theorem smul_eq_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [Nontrivial W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (E : ρ.Equiv σ) {g : G} {c c' : ℂ} (hρ : ∀ v, ρ g v = c • v) (hσ : ∀ w, σ g w = c' • w) :
    c' = c := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨y, rfl⟩ := E.toLinearEquiv.surjective w
  have hE : E.toIntertwiningMap (ρ g y) = σ g (E.toIntertwiningMap y) :=
    E.toIntertwiningMap.isIntertwining _ _ g y
  rw [hρ, hσ, map_smul] at hE
  have h2 : (c - c') • E.toLinearEquiv y = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact hE
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact (sub_eq_zero.1 h3).symm
  · exact absurd h3 hw

theorem scalar_mul_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), ∀ (x : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Zc.jm x hd π ≠ 0 → ∀ (t : kˣ) (c c0 c1 : ℂ), (∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v) → Zl.ScalarBy (x 0) t c0 → Zl.ScalarBy (x 1) t c1 → c0 * c1 = c := by
  intro k _ _ _ _ N V _ _ π x hd hj t c c0 c1 hc h0 h1
  obtain ⟨S, T, ⟨E⟩⟩ := exists_step_of_jhMult_ne_zero (show jhMult (piTensor fun a => (x a).rep)
    (_root_.GlobalTheory.SmGL.jac (stdBlocks (fun a => (x a).1) hd) π) ≠ 0 from hj)
  let g : Levi k (fun a => Fin (x a).1) := fun a => Matrix.GeneralLinearGroup.scalar (Fin (x a).1) t
  have hjac : ∀ v, _root_.GlobalTheory.SmGL.jac (stdBlocks (fun a => (x a).1) hd) π g v = c • v := by
    intro v
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [_root_.GlobalTheory.SmGL.jac_mk, show deltaHalf k (fun a => Fin (x a).1) g = 1 from deltaHalf_scalar _ t,
      show leviEmb k (stdBlocks (fun a => (x a).1) hd) g = _ from leviEmb_scalar _ hd t, hc]
    simp [Submodule.Quotient.mk_smul]
  let cc : Fin 2 → ℂ := ![c0, c1]
  have hcc : ∀ a v, (x a).rep (g a) v = cc a • v := by
    intro a v
    fin_cases a
    · exact h0 v
    · exact h1 v
  haveI := GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL k x
  have hfin := smul_eq_of_equiv E (subQuot_apply_of_smul S T hjac)
    (piTensor_apply_of_smul x g cc hcc)
  rw [Fin.prod_univ_two] at hfin
  exact hfin

end GlobalTheory.CompanionTheory.JacCentral

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.JacquetCongr

theorem jm_congr_of_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), Nonempty (π.Equiv σ) → jm x hd π = jm x hd σ := by
  intro k _ _ _ _ h N x hd V W _ _ _ _ π σ ⟨φ⟩
  exact jhMult_congr_right _ (GlobalTheory.SmGL.Exponents.jacEquiv _ φ)

end GlobalTheory.CompanionTheory.JacquetCongr
end
