module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle031
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle032
import Mathlib.Algebra.Module.StablyFree.Basic
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.QuasiDeterminantConjInv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckTensHom

variable {k r : ℕ}

theorem sum_list_comm {α β : Type} [Fintype β] (l : List α) (a : α → β → ℝ) :
    ∑ e, (l.map fun w => a w e).sum = (l.map fun w => ∑ e, a w e).sum := by
  induction l with
  | nil => simp
  | cons w l ih => simp [Finset.sum_add_distrib, ih]

theorem act_apply (X : Obj k r) (g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (x : M X) (c : X.1.ι) :
    CompanionTheory.Zuck.act X g x c = ∑ d, X.1.ρ g c d • X.2.sig g (x d) := by
  simp only [CompanionTheory.Zuck.act, CompanionTheory.Zuck.mAct, CompanionTheory.Zuck.dOp, LinearMap.comp_apply, LinearMap.pi_apply,
    LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    LinearMap.compLeft_apply, Function.comp_apply]

theorem act_tens1 (F E : FRep k r) (U : URep k r) (g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (x : M (F.tens E, U)) (e : E.ι) :
    (fun c => CompanionTheory.Zuck.act (F.tens E, U) g x (c, e) : M (F, U)) =
      ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c' => x (c', e')) := by
  funext c
  rw [act_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, act_apply, Finset.smul_sum, smul_smul]
  show ∑ d : F.ι × E.ι, _ = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun c' _ => ?_
  simp [CompanionTheory.Zuck.FRep.tens, mul_comm]

theorem act_tens2 (F E : FRep k r) (U : URep k r) (g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (x : M (E.tens F, U)) (e : E.ι) :
    (fun c => CompanionTheory.Zuck.act (E.tens F, U) g x (e, c) : M (F, U)) =
      ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c' => x (e', c')) := by
  funext c
  rw [act_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, act_apply, Finset.smul_sum, smul_smul]
  show ∑ d : E.ι × F.ι, _ = _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun c' _ => ?_
  simp [CompanionTheory.Zuck.FRep.tens]

theorem sn_tens1 (F E : FRep k r) (U : URep k r) (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) (x : M (F.tens E, U)) :
    sn (F.tens E, U) W x = ∑ e, sn (F, U) W (fun c => x (c, e)) := by
  simp only [CompanionTheory.Zuck.sn]
  show ∑ d : F.ι × E.ι, _ = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem sn_tens2 (F E : FRep k r) (U : URep k r) (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) (x : M (E.tens F, U)) :
    sn (E.tens F, U) W x = ∑ e, sn (F, U) W (fun c => x (e, c)) := by
  simp only [CompanionTheory.Zuck.sn]
  show ∑ d : E.ι × F.ι, _ = _
  rw [Fintype.sum_prod_type]

theorem tensHom : TensHom := by
  intro k r F F' E U U' f hf
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro W hW
    obtain ⟨C, Ws, hWs, hb⟩ := hf.cont W hW
    refine ⟨C, Ws, hWs, fun x => ?_⟩
    rw [sn_tens1]
    calc ∑ e, CompanionTheory.Zuck.sn (F', U') W (fun c => CompanionTheory.Zuck.on1 f x (c, e))
        = ∑ e, CompanionTheory.Zuck.sn (F', U') W (f (fun c => x (c, e))) := rfl
      _ ≤ ∑ e, C * (Ws.map fun W' => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))).sum :=
          Finset.sum_le_sum fun e _ => hb _
      _ = C * ∑ e, (Ws.map fun W' => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))).sum := by
          rw [Finset.mul_sum]
      _ = C * (Ws.map fun W' => ∑ e, CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))).sum :=
          congrArg (C * ·) (sum_list_comm Ws (fun W' e => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))))
      _ = C * (Ws.map fun W' => CompanionTheory.Zuck.sn (F.tens E, U) W' x).sum := by
          simp only [sn_tens1]
  · intro g hg
    apply LinearMap.ext
    intro x
    funext p
    obtain ⟨c', e⟩ := p
    have h2 := act_tens1 F E U g x e
    have h1 := act_tens1 F' E U' g (CompanionTheory.Zuck.on1 f x) e
    calc (CompanionTheory.Zuck.on1 f ∘ₗ CompanionTheory.Zuck.act (F.tens E, U) g) x (c', e)
        = f (fun c => CompanionTheory.Zuck.act (F.tens E, U) g x (c, e)) c' := rfl
      _ = f (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c => x (c, e'))) c' :=
          congrArg (fun y => f y c') h2
      _ = ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (f (fun c => x (c, e'))) c' := by

          rw [map_sum]
          simp only [map_smul, Finset.sum_apply, Pi.smul_apply]
          refine Finset.sum_congr rfl fun e' _ => ?_
          have hq := LinearMap.congr_fun (hf.equiv g hg) (fun c => x (c, e'))
          simp only [LinearMap.comp_apply] at hq
          rw [hq]
      _ = (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (fun c => CompanionTheory.Zuck.on1 f x (c, e'))) c' := by
          simp only [Finset.sum_apply, Pi.smul_apply]
          rfl
      _ = (fun c => CompanionTheory.Zuck.act (F'.tens E, U') g (CompanionTheory.Zuck.on1 f x) (c, e)) c' :=
          (congrFun h1 c').symm
      _ = (CompanionTheory.Zuck.act (F'.tens E, U') g ∘ₗ CompanionTheory.Zuck.on1 f) x (c', e) := rfl
  · intro W hW
    obtain ⟨C, Ws, hWs, hb⟩ := hf.cont W hW
    refine ⟨C, Ws, hWs, fun x => ?_⟩
    rw [sn_tens2]
    calc ∑ e, CompanionTheory.Zuck.sn (F', U') W (fun c => CompanionTheory.Zuck.on2 f x (e, c))
        = ∑ e, CompanionTheory.Zuck.sn (F', U') W (f (fun c => x (e, c))) := rfl
      _ ≤ ∑ e, C * (Ws.map fun W' => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))).sum :=
          Finset.sum_le_sum fun e _ => hb _
      _ = C * ∑ e, (Ws.map fun W' => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))).sum := by
          rw [Finset.mul_sum]
      _ = C * (Ws.map fun W' => ∑ e, CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))).sum :=
          congrArg (C * ·) (sum_list_comm Ws (fun W' e => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))))
      _ = C * (Ws.map fun W' => CompanionTheory.Zuck.sn (E.tens F, U) W' x).sum := by
          simp only [sn_tens2]
  · intro g hg
    apply LinearMap.ext
    intro x
    funext p
    obtain ⟨e, c'⟩ := p
    have h2 := act_tens2 F E U g x e
    have h1 := act_tens2 F' E U' g (CompanionTheory.Zuck.on2 f x) e
    calc (CompanionTheory.Zuck.on2 f ∘ₗ CompanionTheory.Zuck.act (E.tens F, U) g) x (e, c')
        = f (fun c => CompanionTheory.Zuck.act (E.tens F, U) g x (e, c)) c' := rfl
      _ = f (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c => x (e', c))) c' :=
          congrArg (fun y => f y c') h2
      _ = ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (f (fun c => x (e', c))) c' := by

          rw [map_sum]
          simp only [map_smul, Finset.sum_apply, Pi.smul_apply]
          refine Finset.sum_congr rfl fun e' _ => ?_
          have hq := LinearMap.congr_fun (hf.equiv g hg) (fun c => x (e', c))
          simp only [LinearMap.comp_apply] at hq
          rw [hq]
      _ = (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (fun c => CompanionTheory.Zuck.on2 f x (e', c))) c' := by
          simp only [Finset.sum_apply, Pi.smul_apply]
          rfl
      _ = (fun c => CompanionTheory.Zuck.act (E.tens F', U') g (CompanionTheory.Zuck.on2 f x) (e, c)) c' :=
          (congrFun h1 c').symm
      _ = (CompanionTheory.Zuck.act (E.tens F', U') g ∘ₗ CompanionTheory.Zuck.on2 f) x (e, c') := rfl

end GlobalTheory.CompanionTheory.ZuckTensHom

end
end

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker ContDiff

namespace GlobalTheory.CompanionTheory.ZuckWedge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_minor {n l : ℕ} (a b : Fin l → Fin n) :
    ContDiff ℝ ∞ fun g : Matrix (Fin n) (Fin n) ℂ => (g.submatrix a b).det := by
  simp only [det_apply']
  refine ContDiff.sum fun σ _ => ?_
  refine contDiff_const.mul ?_
  refine contDiff_prod fun i _ => ?_
  simp only [submatrix_apply]
  fun_prop

theorem okWedge : OKWedge := by
  intro k r l
  refine FRep.OK.mk ?_ ?_ ?_ ?_
  · exact GlobalTheory.compound_one _ l
  · intro g _ h _
    exact GlobalTheory.compound_mul l g h
  · intro c d g₀ _
    exact ⟨Set.univ, fun g => BranchingSupport.cmp l g c d, isOpen_univ, Set.mem_univ _,
      (contDiff_minor _ _).contDiffOn, fun g _ _ => rfl⟩
  · refine ⟨(Fintype.card (Equiv.Perm (Fin l)) : ℝ), fun g _ c d => ?_⟩
    have hent : ∀ i j, ‖g i j‖ ≤ Formalism.FourierDecayAlt.B.gN g := by
      intro i j
      have h2 : ‖g i j‖ ^ 2 ≤ ∑ i', ∑ j', Complex.normSq (g i' j') := by
        rw [Complex.sq_norm]
        calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
              Finset.single_le_sum (fun j' _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
          _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
              Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
                (fun i' _ => Finset.sum_nonneg fun j' _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
      calc ‖g i j‖ = |‖g i j‖| := (abs_of_nonneg (norm_nonneg _)).symm
        _ ≤ _ := Real.abs_le_sqrt h2
    show ‖(g.submatrix _ _).det‖ ≤ _
    rw [det_apply']
    refine (norm_sum_le _ _).trans ?_
    calc ∑ σ : Equiv.Perm (Fin l), ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, g.submatrix _ _ (σ i) i‖
        ≤ ∑ σ : Equiv.Perm (Fin l), Formalism.FourierDecayAlt.B.gN g ^ l := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
          rw [norm_mul, hs, one_mul, norm_prod]
          calc ∏ i, ‖g.submatrix _ _ (σ i) i‖ ≤ ∏ _i : Fin l, Formalism.FourierDecayAlt.B.gN g :=
                Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hent _ _)
            _ = Formalism.FourierDecayAlt.B.gN g ^ l := by simp
      _ = (Fintype.card (Equiv.Perm (Fin l)) : ℝ) * Formalism.FourierDecayAlt.B.gN g ^ l := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end GlobalTheory.CompanionTheory.ZuckWedge
end

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.finite_dim_invariant_subspace_adjoint_pair : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ι : Type) (T : Submodule ℂ (Cn n V))
    (a b : ι → Module.End ℂ (Cn n V)) (D : Module.End ℂ (Cn n V)) (y : Cn n V), FiniteDimensional ℂ T →
    (∀ i x z, ∑ A, ⟪a i x A, z A⟫_ℂ = ∑ A, ⟪x A, b i z A⟫_ℂ) →
    (∀ i, ∀ t ∈ T, a i t ∈ T) → (∀ i, ∀ t ∈ T, b i t ∈ T) →
    (∀ i, ∀ t ∈ T, a i (D t) = D (a i t)) → (∀ i, ∀ t ∈ T, b i (D t) = D (b i t)) →
    y ∈ T → (∀ i, a i (D y) = 0) → ∃ y' ∈ T, (∀ i, a i y' = 0) ∧ D y' = D y := by
  first | exact @GlobalTheory.CompanionTheory.FarReg.highest_preimage_of_stable | exact GlobalTheory.CompanionTheory.FarReg.highest_preimage_of_stable | (intros; apply GlobalTheory.CompanionTheory.FarReg.highest_preimage_of_stable <;> assumption)
end

section

noncomputable section

open Finset Polynomial

namespace GlobalTheory.CompanionTheory.RgExhHecke.OmScalP

open Formalism.REAL (qdet qminor Tm)
open _root_.CompanionTheory.RgExh
open _root_.CompanionTheory.RgExh.Hk

section Poly

variable {A : Type*} [Ring A] [Algebra ℂ A]

def evAt (u : ℂ) : A[X] →+* A :=
  eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u) fun a => (Algebra.commutes u a).symm

theorem evAt_apply (u : ℂ) (p : A[X]) : evAt u p = eval₂ (RingHom.id A) (algebraMap ℂ A u) p := rfl

def tmPoly {n : ℕ} (E : Fin n → Fin n → A) (v : ℂ) (a b : Fin n) : A[X] :=
  (if a = b then X - C (algebraMap ℂ A v) else 0) + C (E a b)

theorem evAt_tmPoly {n : ℕ} (E : Fin n → Fin n → A) (v u : ℂ) (a b : Fin n) :
    evAt u (tmPoly E v a b) = Tm E (u - v) a b := by
  unfold tmPoly Tm
  by_cases h : a = b <;> simp [h, evAt_apply, map_sub]

def qdetPoly {n : ℕ} (E : Fin n → Fin n → A) : A[X] :=
  ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A[X]) *
    (List.ofFn fun k : Fin n => tmPoly E ((k : ℕ) : ℂ) (σ k) k).prod

theorem evAt_qdetPoly {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : evAt u (qdetPoly E) = qdet E u := by
  unfold qdet qminor qdetPoly

  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  simp [Function.comp_def, evAt_tmPoly]

end Poly

theorem cont {M : Type*} [AddCommGroup M] [Module ℂ M] (p : (Module.End ℂ M)[X]) (q : ℂ[X]) (h : M) (b : ℂ)
    (H : ∀ u, u ≠ b → evAt u p h = q.eval u • h) : evAt b p h = q.eval b • h := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  set r : ℂ[X] := ∑ k ∈ p.support, monomial k (φ (p.coeff k h)) - q * C (φ h) with hr
  have hev : ∀ u, r.eval u = φ (evAt u p h - q.eval u • h) := by
    intro u
    have e1 : evAt u p h = ∑ k ∈ p.support, u ^ k • p.coeff k h := by
      rw [evAt_apply, eval₂_eq_sum, Polynomial.sum_def, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← map_pow, RingHom.id_apply, ← Algebra.commutes, ← Algebra.smul_def]
      rfl
    rw [e1, hr]

    simp [eval_finsetSum, map_sum, eval_monomial, mul_comm]
  have hz : r = 0 := by
    refine eq_zero_of_infinite_isRoot r ?_
    refine Set.Infinite.mono (s := {b}ᶜ) ?_ (Set.finite_singleton b).infinite_compl
    intro u hu
    have hu' : u ≠ b := hu
    change r.eval u = 0
    rw [hev, H u hu', sub_self, map_zero]
  rw [← hev, hz, eval_zero]

theorem compLeft_smul_one {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (c : ℂ) (w : Fin n → V) :
    (c • (1 : Module.End ℂ V)).compLeft (Fin n) w = c • w := by
  funext i
  simp [LinearMap.compLeft_apply]

theorem tens_apply {n : ℕ} (X : GMod n) (χ : Fin n → ℂ) (hS : ScalChar X χ) (u : ℂ) (w : Fin n → X.V) :
    qdet (tensE X) u (u • w + om X w) =
      Formalism.QuantumDeterminants.capP χ (u - cn n) • ((u + 1) • w + om X w) := by
  have hq : qdet X.E u = Formalism.QuantumDeterminants.capP χ (u - cn n) • (1 : Module.End ℂ X.V) := by
    have := hS (u - cn n)
    rwa [show u - cn n + ((n : ℂ) - 1) / 2 = u by unfold cn; ring] at this
  have h := LinearMap.congr_fun (GlobalTheory.T.QuantumDeterminantTensor n X u) w
  rw [hq] at h
  simpa [Module.End.mul_apply, compLeft_smul_one] using h

theorem core {n : ℕ} (X : GMod n) (χ : Fin n → ℂ) (s : Fin n) (hS : ScalChar X χ)
    (hs : ∀ r, r ≠ s → χ r ≠ χ s) (g : Fin n → X.V)
    (h2 : om X (om X g - (χ s - cn n) • g) = (χ s - cn n) • (om X g - (χ s - cn n) • g)) :
    om X g - (χ s - cn n) • g = 0 := by
  set a : ℂ := χ s - cn n with ha
  set h : Fin n → X.V := om X g - a • g with hh
  set ct : ℂ → ℂ := fun u => ∏ t ∈ univ.erase s, (u - cn n + χ t) with hct
  have hc : ∀ u, Formalism.QuantumDeterminants.capP χ (u - cn n) = (u + a) * ct u := by
    intro u
    have := Finset.mul_prod_erase univ (fun t => u - cn n + χ t) (mem_univ s)
    simp only [Formalism.QuantumDeterminants.capP, hct]
    rw [← this, ha]
    ring_nf
  set q : ℂ[X] := (∏ t ∈ univ.erase s, (Polynomial.X - C (cn n) + C (χ t))) * (Polynomial.X + C (a + 1)) with hq
  have hqe : ∀ u, q.eval u = ct u * (u + (a + 1)) := by
    intro u
    simp [hq, hct, eval_prod]
  have hne : ∀ u, u ≠ -a → evAt u (qdetPoly (tensE X)) h = q.eval u • h := by
    intro u hu
    have hw : u + a ≠ 0 := fun e => hu (eq_neg_of_add_eq_zero_left e)
    have e := tens_apply X χ hS u h
    rw [h2, hc] at e
    rw [evAt_qdetPoly, hqe]
    have e1 : u • h + a • h = (u + a) • h := (add_smul _ _ _).symm
    have e2 : (u + 1) • h + a • h = (u + (a + 1)) • h := by rw [← add_smul]; ring_nf
    rw [e1, e2, map_smul, smul_smul, mul_assoc, ← smul_smul] at e
    exact smul_right_injective _ hw e
  have hb := cont _ q h (-a) hne
  rw [evAt_qdetPoly, hqe] at hb
  have hzero : qdet (tensE X) (-a) h = 0 := by
    have e := tens_apply X χ hS (-a) g
    rw [hc] at e
    have e0 : (-a) • g + om X g = h := by rw [hh, neg_smul]; abel
    rw [e0] at e
    rw [e]
    simp
  rw [hzero] at hb
  have hct0 : ct (-a) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun t ht => ?_
    have ht' : t ≠ s := Finset.ne_of_mem_erase ht
    have : -a - cn n + χ t = χ t - χ s := by rw [ha]; ring
    rw [this]
    exact sub_ne_zero.2 (hs t ht')
  have hfin : ct (-a) • h = 0 := by
    have : ct (-a) * (-a + (a + 1)) = ct (-a) := by ring
    rw [this] at hb
    exact hb.symm
  exact (smul_eq_zero.1 hfin).resolve_left hct0

theorem omScal : OmScal := by
  intro n X χ s hS hs f hf
  set T : Module.End ℂ (Fin n → X.V) := om X - (χ s - cn n) • (1 : Module.End ℂ (Fin n → X.V)) with hT
  have hTa : ∀ w, T w = om X w - (χ s - cn n) • w := fun w => by simp [hT]
  have key : ∀ k : ℕ, (T ^ (k + 1)) f = 0 → T f = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      refine ih ?_
      have h2 : T (T ((T ^ k) f)) = 0 := by
        rw [← hk, pow_succ' T (k + 1), pow_succ' T k]
        rfl
      have h3 := core X χ s hS hs ((T ^ k) f) (by
        rw [hTa] at h2
        rw [← hTa]
        exact sub_eq_zero.1 h2)
      rw [← hTa] at h3
      rw [pow_succ' T k]
      exact h3
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hf
  have hk' : (T ^ (k + 1)) f = 0 := by
    rw [pow_succ' T k, Module.End.mul_apply]
    have : (T ^ k) f = 0 := hk
    rw [this, map_zero]
  have := key k hk'
  rw [hTa] at this
  exact sub_eq_zero.1 this

end GlobalTheory.CompanionTheory.RgExhHecke.OmScalP
end
end

section

namespace GlobalTheory.CompanionTheory.RgConjQdet

open Finset

theorem conj_single_apply {n : ℕ} (U Ui : Matrix (Fin n) (Fin n) ℂ) (p q a b : Fin n) :
    (U * Matrix.single p q 1 * Ui : Matrix (Fin n) (Fin n) ℂ) a b = U a p * Ui q b := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem conjQdet : CompanionTheory.RgExh.Dec.J.ConjQdet := by
  intro n X U Ui hUUi hUiU u
  have hE : ∀ (x : ℂ) (p q : Fin n),
      Formalism.REAL.Tm (fun p q => ReciprocityTheory.ChartRestriction.DS.actM X.E (U * Matrix.single p q 1 * Ui)) x p q =
        ∑ c, U.transpose p c • ∑ d, Ui.transpose d q • Formalism.REAL.Tm X.E x c d := by
    intro x p q
    have hd : ∑ c, ∑ d, (U c p * Ui q d) • (if c = d then algebraMap ℂ (Module.End ℂ X.V) x else 0)
        = if p = q then algebraMap ℂ (Module.End ℂ X.V) x else 0 := by
      simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← Finset.sum_smul]
      have hc : ∑ c, U c p * Ui q c = (Ui * U) q p := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
      rw [hc, hUiU, Matrix.one_apply]
      by_cases hpq : p = q
      · subst hpq
        simp
      · rw [if_neg (Ne.symm hpq), if_neg hpq, zero_smul]
    simp only [Formalism.REAL.Tm, ReciprocityTheory.ChartRestriction.DS.actM, conj_single_apply, Matrix.transpose_apply,
      Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib]
    rw [hd]
  have hT : Formalism.REAL.Tm (fun p q => ReciprocityTheory.ChartRestriction.DS.actM X.E (U * Matrix.single p q 1 * Ui)) =
      fun x p q => ∑ c, U.transpose p c • ∑ d, Ui.transpose d q • Formalism.REAL.Tm X.E x c d :=
    funext fun x => funext fun p => funext fun q => hE x p q
  rw [PI.UnitaryGroupMassFormula.DSIC.qdet_eq_qF (fun p q => ReciprocityTheory.ChartRestriction.DS.actM X.E (U * Matrix.single p q 1 * Ui)), hT,
    PI.UnitaryGroupMassFormula.DSIC.qF_row, PI.UnitaryGroupMassFormula.DSIC.qF_col X.E X.gl, smul_smul, Matrix.det_transpose,
    Matrix.det_transpose, ← Matrix.det_mul, hUUi, Matrix.det_one, one_smul]

end GlobalTheory.CompanionTheory.RgConjQdet
end

end

section

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

theorem _root_.GlobalTheory.T.ExteriorPowerIntegral : OKWedge := by
  first | exact @GlobalTheory.CompanionTheory.ZuckWedge.okWedge | exact GlobalTheory.CompanionTheory.ZuckWedge.okWedge | (intros; apply GlobalTheory.CompanionTheory.ZuckWedge.okWedge <;> assumption)

end
end
