module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle127
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle168
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

theorem exists_linearForm_invariant_isotropic_vacuum : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ A : Submodule R X, (∀ a ∈ A, ∀ b ∈ A, γ a b = 1) → ∃ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 ∧ ∀ a ∈ A, ∀ v, ℓ (W a v) = ℓ v := by
  intro R X M _ _ _ _ _ σ w γ W h Λ hΛ s hs hfix hspan A hA
  have key : ∀ z y, y - z ∈ Λ → W z s = γ (w • z) (y - z) • W y s := by
    intro z y hyz
    have h1 := h.comp z (y - z) s
    rwa [hfix _ hyz, add_sub_cancel] at h1
  let P : X ⧸ Λ → Prop := fun q => ∃ a ∈ A, (Submodule.Quotient.mk a : X ⧸ Λ) = q
  let rep : X ⧸ Λ → X := fun q => if hq : P q then hq.choose else Quotient.out q
  have hrep : ∀ q, (Submodule.Quotient.mk (rep q) : X ⧸ Λ) = q := by
    intro q
    by_cases hq : P q
    · simp only [rep, dif_pos hq]; exact hq.choose_spec.2
    · simp only [rep, dif_neg hq]; exact Quotient.out_eq q
  have hrepA : ∀ q, P q → rep q ∈ A := by
    intro q hq
    simp only [rep, dif_pos hq]; exact hq.choose_spec.1
  let e : X ⧸ Λ → M := fun q => W (rep q) s
  have he : ∀ z, W z s = γ (w • z) (rep (Submodule.Quotient.mk z) - z) • e (Submodule.Quotient.mk z) := by
    intro z
    exact key z _ ((Submodule.Quotient.eq Λ).1 (hrep _))
  have hli : LinearIndependent ℂ e := by
    refine linearIndependent_of_simultaneous_eigen e (fun q (l : Λ) => γ l (rep q)) (fun l : Λ => W l) ?_ ?_ ?_
    · intro q q' hq
      have hm : rep q - rep q' ∈ Λ := by
        rw [hΛ]
        intro a ha
        apply h.swap_eq_one
        have h1 : γ a (rep q) = γ a (rep q') := congrFun hq ⟨a, ha⟩
        rw [sub_eq_add_neg, h.add_right, h.neg_right, h1, mul_inv_cancel₀ (h.ne_zero _ _)]
      rw [← hrep q, ← hrep q']
      exact (Submodule.Quotient.eq Λ).2 hm
    · intro l q
      show W l (W (rep q) s) = γ l (rep q) • W (rep q) s
      rw [h.comm, hfix l l.2]
    · intro q h0
      have h1 := h.neg_comp (rep q) s
      rw [show W (rep q) s = 0 from h0, map_zero] at h1
      exact hs ((smul_eq_zero.1 h1.symm).resolve_left (h.ne_zero _ _))
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range e) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    show W z s ∈ _
    rw [he z]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  let b := Module.Basis.mk hli hsp
  let ℓ : M →ₗ[ℂ] ℂ := b.constr ℂ (fun q => if P q then (1 : ℂ) else 0)
  have hℓ : ∀ q, ℓ (e q) = if P q then (1 : ℂ) else 0 := by
    intro q
    have := b.constr_basis ℂ (fun q => if P q then (1 : ℂ) else 0) q
    rwa [Module.Basis.mk_apply] at this
  have hwA : ∀ a ∈ A, ∀ b ∈ A, γ (w • a) b = 1 := fun a ha b hb => hA _ (A.smul_mem w ha) b hb
  refine ⟨ℓ, ?_, ?_⟩
  · have h0 : P (Submodule.Quotient.mk 0) := ⟨0, A.zero_mem, rfl⟩
    have h1 := he 0
    rw [h.zero, hwA 0 A.zero_mem _ (A.sub_mem (hrepA _ h0) A.zero_mem), one_smul] at h1
    rw [h1, hℓ, if_pos h0]
  · intro a ha v
    have hext : ℓ ∘ₗ W a = ℓ := by
      refine b.ext fun q => ?_
      rw [Module.Basis.mk_apply, LinearMap.comp_apply]
      show ℓ (W a (W (rep q) s)) = ℓ (e q)
      rw [h.comp, he (a + rep q), map_smul, map_smul, hℓ, hℓ]
      by_cases hq : P q
      · have hA1 : a + rep q ∈ A := A.add_mem ha (hrepA q hq)
        have hq' : P (Submodule.Quotient.mk (a + rep q)) := ⟨_, hA1, rfl⟩
        rw [if_pos hq, if_pos hq', hwA a ha _ (hrepA q hq), hwA _ hA1 _ (A.sub_mem (hrepA _ hq') hA1)]
        simp
      · have hq' : ¬ P (Submodule.Quotient.mk (a + rep q)) := by
          rintro ⟨c, hc, hce⟩
          apply hq
          refine ⟨c - a, A.sub_mem hc ha, ?_⟩
          rw [Submodule.Quotient.mk_sub, hce, ← Submodule.Quotient.mk_sub, add_sub_cancel_left, hrep]
        rw [if_neg hq, if_neg hq']
        simp
    exact LinearMap.congr_fun hext v

end GlobalTheory.SphTheta
end
end

section

noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix Filter GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped Topology

namespace GlobalTheory.CWGeneral

variable {n : ℕ} {ε : Fin n → Bool}

section Sub

variable {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]


end Sub

section KFin

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)}

theorem dense_smoothAll_of_irred (hσ : IsURepOn (UJset ε) σ) (hi : IsIrredOn (UJset ε) σ) :
    Dense (smoothAll (Jm ε) σ : Set H) := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · intro x
    rw [Subsingleton.elim x 0]
    exact subset_closure (smoothAll (Jm ε) σ).zero_mem
  · refine dense_of_irred hi (fun g hg v hv k x hx hxG => ?_) ?_
    · letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
      letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
      have h1 := hv k (fun t => x t * g) (hx.mul contDiff_const) fun t => mul_mem_UJ (hxG t) hg
      convert h1 using 2 with t
      exact (sigma_mul hσ (hxG t) hg v).symm
    · obtain ⟨v, hv, hs⟩ := GlobalTheory.GardingVec.exists_garding hσ
      exact (Submodule.ne_bot_iff _).2 ⟨v, hs, hv⟩

theorem sm_of_isKFin (hHC : GlobalTheory.Published.HarishChandraModules) (hσ : IsURepOn (UJset ε) σ)
    (hi : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) : Sm ε σ v := by
  have := hHC.smoothVec hσ hi hv (P := 1) (G := Jm ε) isUnit_one (by simp)
  rwa [conj_one_eq] at this

theorem isKFin_dRep_of_irred (hHC : GlobalTheory.Published.HarishChandraModules) (hσ : IsURepOn (UJset ε) σ)
    (hi : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) :
    IsKFin ε σ (dRep σ X v) := by
  obtain ⟨S, h1, h2, h3⟩ := hv
  have hS : S ≤ smooth (Jm ε) σ := fun s hs => sm_of_isKFin hHC hσ hi ⟨S, h1, hs, h3⟩
  let b := Module.finBasis ℝ (lie (Jm ε))
  let L : Fin (Module.finrank ℝ (lie (Jm ε))) → (S →ₗ[ℂ] H) := fun i =>
    (smooth (Jm ε) σ).subtype ∘ₗ dOp (isUnit_Jm ε) hσ (b i).2 ∘ₗ Submodule.inclusion hS
  let T : Submodule ℂ H := ⨆ i, LinearMap.range (L i)
  have hT : ∀ Y ∈ lieSet ε, ∀ s ∈ S, dRep σ Y s ∈ T := by
    intro Y hY s hs
    have e : Y = ∑ i, b.repr ⟨Y, hY⟩ i • (b i : Mx n) := by
      have := congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)
      simpa only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] using this.symm
    rw [e, GlobalTheory.LowTypeDetermined.dRep_sum (isUnit_Jm ε) hσ (dense_smoothAll_of_irred hσ hi) (fun i => (b i).2)
      (hS hs)]
    refine T.sum_mem fun i _ => T.smul_mem _ ?_
    exact Submodule.mem_iSup_of_mem i ⟨⟨s, hs⟩, rfl⟩
  refine ⟨T, inferInstance, hT X hX v h2, fun k hk w hw => ?_⟩
  have hg := K_le_UJ hk
  have : T ≤ T.comap (σ k : H →ₗ[ℂ] H) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨s, rfl⟩
    have hinv : (k⁻¹)⁻¹ = k := Matrix.inv_eq_left_inv (mul_inv_UJ hg)
    have hY : k * (b i : Mx n) * k⁻¹ ∈ lieSet ε := by
      have := conj_mem_lie (isUnit_Jm ε) (inv_mem_UJ hg) (b i).2
      rwa [hinv] at this
    have e := Dw_translate hσ hg (hS s.2) (l := [k * (b i : Mx n) * k⁻¹]) (by simpa using hY)
    have e2 : k⁻¹ * (k * (b i : Mx n) * k⁻¹) * k = b i := by
      rw [← mul_assoc, ← mul_assoc, inv_mul_UJ hg, one_mul, mul_assoc, inv_mul_UJ hg, mul_one]
    simp only [Dw, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, e2] at e
    show σ k (dRep σ (b i) s) ∈ T
    rw [← e]
    exact hT _ hY _ (h3 k hk s s.2)
  exact this hw

end KFin

end GlobalTheory.CWGeneral

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

def bF {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (v : HeightOneSpectrum (𝓞 D.host.F)) : ℝ≥0 :=
  max 1 (Finset.univ.sup fun p : Fin m × Fin n => absFin D.host.F v (compFin D.host.F D.host.E v (Y p.1 p.2)))

theorem absFin_le_bF {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (i : Fin m) (j : Fin n) : absFin D.host.F v (compFin D.host.F D.host.E v (Y i j)) ≤ bF Y v := by
  unfold bF
  refine le_trans ?_ (le_max_right _ _)
  have h := Finset.le_sup (f := fun p : Fin m × Fin n =>
    absFin D.host.F v (compFin D.host.F D.host.E v (Y p.1 p.2))) (Finset.mem_univ (i, j))
  exact h

theorem le_vFin {n : ℕ} (x : Fin n → AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin n) :
    absFin D.host.F v (compFin D.host.F D.host.E v (x i)) ≤ vFin v x := by
  unfold vFin
  have h := Finset.le_sup (f := fun i => absFin D.host.F v (compFin D.host.F D.host.E v (x i))) (Finset.mem_univ i)
  exact h

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

theorem eventually_bF_eq_one {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) :
    ∀ᶠ v in Filter.cofinite, bF Y v = 1 := by
  have h : ∀ᶠ v in Filter.cofinite, ∀ p : Fin m × Fin n,
      absFin D.host.F v (compFin D.host.F D.host.E v (Y p.1 p.2)) ≤ 1 :=
    Filter.eventually_all.2 fun p => eventually_absFin_le_one D.host.F (Y p.1 p.2)
  refine h.mono fun v hv => ?_
  unfold bF
  exact max_eq_left (Finset.sup_le fun p _ => hv p)

theorem finite_mulSupport_bF {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) :
    (Function.mulSupport (bF Y)).Finite :=
  (Filter.eventually_cofinite.1 (eventually_bF_eq_one Y)).subset fun _ hv => hv

theorem vFin_mulVec_le {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (x : Fin n → AE D)
    (v : HeightOneSpectrum (𝓞 D.host.F)) : vFin v (Y *ᵥ x) ≤ bF Y v * vFin v x := by
  rw [vFin]
  refine Finset.sup_le fun i _ => ?_

  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  exact absFin_sum_le D.host.F v _ _ fun j _ =>
    (absFin_mul_le D.host.F v _ _).trans (mul_le_mul' (absFin_le_bF Y v i j) (le_vFin x v j))

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}


open Classical in
def bI {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (w : InfinitePlace D.host.F) : ℝ≥0 :=
  max 1 (Finset.univ.sup fun p : EmbOver D.host.E w × Fin m =>
    ∑ j, ‖infEmb p.1 (compInf D.host.F D.host.E w (Y p.2 j))‖₊)

theorem sum_le_bI {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (w : InfinitePlace D.host.F)
    (τ : EmbOver D.host.E w) (i : Fin m) :
    ∑ j, ‖infEmb τ (compInf D.host.F D.host.E w (Y i j))‖₊ ≤ bI Y w := by
  classical
  unfold bI
  refine le_trans ?_ (le_max_right _ _)
  have h := Finset.le_sup (f := fun p : EmbOver D.host.E w × Fin m =>
    ∑ j, ‖infEmb p.1 (compInf D.host.F D.host.E w (Y p.2 j))‖₊) (Finset.mem_univ (τ, i))
  exact h

theorem le_vInf {n : ℕ} (x : Fin n → AE D) (w : InfinitePlace D.host.F) (τ : EmbOver D.host.E w) (i : Fin n) :
    ‖infEmb τ (compInf D.host.F D.host.E w (x i))‖₊ ≤ vInf w x := by
  classical
  unfold vInf
  have h := Finset.le_sup (f := fun p : EmbOver D.host.E w × Fin n =>
    ‖infEmb p.1 (compInf D.host.F D.host.E w (x p.2))‖₊) (Finset.mem_univ (τ, i))
  exact h

theorem vInf_mulVec_le {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (x : Fin n → AE D)
    (w : InfinitePlace D.host.F) : vInf w (Y *ᵥ x) ≤ bI Y w * vInf w x := by
  rw [vInf]
  refine Finset.sup_le fun p _ => ?_

  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine (nnnorm_sum_le _ _).trans ?_
  refine le_trans ?_ (mul_le_mul' (sum_le_bI Y w p.1 p.2) le_rfl)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [nnnorm_mul]
  exact mul_le_mul' le_rfl (le_vInf x w p.1 j)

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

theorem eventually_vFin_seen_eq_one (V : HSp D) (g : GA D V) {ξ : Fin V.rank → D.host.E} (hξ : ξ ≠ 0) :
    ∀ᶠ v in Filter.cofinite, vFin v (seen V g ξ) = 1 := by
  set u : Fin V.rank → AE D := fun i => incA D (ξ i) with hu
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
  have h1 : ∀ᶠ v in Filter.cofinite, vFin v u ≤ 1 :=
    (Filter.eventually_all.2 fun i => eventually_absFin_le_one D.host.F (u i)).mono fun v hv =>
      Finset.sup_le fun i _ => hv i
  have h2 : ∀ᶠ v in Filter.cofinite, 1 ≤ absFin D.host.F v (compFin D.host.F D.host.E v (incA D (ξ i))) := by
    refine (eventually_absFin_le_one D.host.F (incA D (ξ i)⁻¹)).mono fun v hv => ?_
    have e : incA D (ξ i) * incA D (ξ i)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hi, map_one]
    have := absFin_mul_le D.host.F v (compFin D.host.F D.host.E v (incA D (ξ i)))
      (compFin D.host.F D.host.E v (incA D (ξ i)⁻¹))
    rw [← map_mul, e, map_one, absFin_one] at this
    exact this.trans (mul_le_of_le_one_right' hv)
  refine ((h1.and h2).and ((eventually_bF_eq_one (mt V g⁻¹)).and (eventually_bF_eq_one (mt V g)))).mono
    fun v hv => le_antisymm ?_ ?_
  · refine (vFin_mulVec_le _ u v).trans ?_
    rw [hv.2.1, one_mul]; exact hv.1.1
  · have e : u = mt V g *ᵥ seen V g ξ := by
      rw [seen, Matrix.mulVec_mulVec, GlobalTheory.MixModel.mt_mul_inv, Matrix.one_mulVec]
    refine hv.1.2.trans ((le_vFin u v i).trans ?_)
    rw [e]
    refine (vFin_mulVec_le _ _ v).trans ?_
    rw [hv.2.2, one_mul]

theorem seen_emb {S A B : HSp D} (o : GlobalTheory.MixModel.OrthDec S A B) (h : GA D A) (η : Fin A.rank → D.host.E) :
    seen S (o.emb (h, 1)) (o.iA *ᵥ η) = o.jA *ᵥ seen A h η := by
  have e1 : (o.emb (h, 1))⁻¹ = o.emb (h⁻¹, 1) := by rw [← map_inv, Prod.inv_mk, inv_one]
  have e2 : (fun i => incA D ((o.iA *ᵥ η) i)) = o.jA *ᵥ fun i => incA D (η i) := by
    funext i; exact RingHom.map_mulVec (incA D) o.iA η i
  rw [seen, seen, e1, e2, Matrix.mulVec_mulVec, GlobalTheory.MixModel.OrthDec.emb_jA, Matrix.mulVec_mulVec]

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

theorem vsize_zero {n : ℕ} : vsize (0 : Fin n → AE D) = 0 := by
  have h : ∀ w : InfinitePlace D.host.F, vInf w (0 : Fin n → AE D) = 0 := fun w => by
    classical
    unfold vInf
    refine le_antisymm (Finset.sup_le fun p _ => ?_) zero_le
    simp
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace D.host.F))
  unfold vsize
  rw [Finset.prod_eq_zero (Finset.mem_univ w) (h w), zero_mul, NNReal.coe_zero]

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

theorem vsize_seen_emb_le : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ C : ℝ,
    ∀ (h : GA D A) (η : Fin A.rank → D.host.E),
      GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen S (o.emb (h, 1)) (o.iA *ᵥ η)) ≤ C * GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η) := by
  intro D S A B o
  refine ⟨(((∏ w, bI o.jA w) * ∏ᶠ v, bF o.jA v : ℝ≥0) : ℝ), fun h η => ?_⟩
  by_cases hη : η = 0
  · subst hη
    have e : (o.iA *ᵥ (0 : Fin A.rank → D.host.E)) = 0 := Matrix.mulVec_zero _
    have z : ∀ (V : HSp D) (g : GA D V), seen V g 0 = 0 := fun V g => by
      have h0 : (fun i => incA D ((0 : Fin V.rank → D.host.E) i)) = 0 := funext fun i => map_zero _
      rw [seen, h0, Matrix.mulVec_zero]
    rw [e, z, z, vsize_zero]
    exact mul_nonneg (NNReal.coe_nonneg _) (vsize_nonneg _)
  have hη' : o.iA *ᵥ η ≠ 0 := fun e => hη (by
    have := congrArg (o.qA *ᵥ ·) e
    simpa [Matrix.mulVec_mulVec, GlobalTheory.MixModel.OrthDec.qA_iA] using this)
  have f1 := Filter.eventually_cofinite.1 (eventually_vFin_seen_eq_one A h hη)
  have f2 := Filter.eventually_cofinite.1 (eventually_vFin_seen_eq_one S (o.emb (h, 1)) hη')
  rw [seen_emb] at f2 ⊢
  have hf : (Function.mulSupport fun v => vFin v (seen A h η)).Finite := f1.subset fun v hv => hv
  have hf' : (Function.mulSupport fun v => vFin v (o.jA *ᵥ seen A h η)).Finite := f2.subset fun v hv => hv
  unfold vsize
  rw [← NNReal.coe_mul, NNReal.coe_le_coe]
  calc (∏ w, vInf w (o.jA *ᵥ seen A h η)) * ∏ᶠ v, vFin v (o.jA *ᵥ seen A h η)
      ≤ (∏ w, bI o.jA w * vInf w (seen A h η)) * ∏ᶠ v, bF o.jA v * vFin v (seen A h η) :=
        mul_le_mul' (Finset.prod_le_prod' fun w _ => vInf_mulVec_le o.jA _ w)
          (finprod_le_finprod' hf' (((finite_mulSupport_bF o.jA).union hf).subset (Function.mulSupport_mul _ _))
            fun v => vFin_mulVec_le o.jA _ v)
    _ = _ := by
        rw [Finset.prod_mul_distrib, finprod_mul_distrib (finite_mulSupport_bF o.jA) hf, mul_mul_mul_comm]

end GlobalTheory.HtOrth.Transp

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.ideleChar_restrict_localUnits_residueChar : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → ∀ PP : Pl D.host.E, (∀ a : (kP PP)ˣ →* ℂˣ, χ.TameAt PP → IsRes χ PP a → GlobalTheory.StepLaw.ResAt c PP a) ∧ (χ.UnrAt PP → GlobalTheory.StepLaw.ResAt c PP 1) := by
  first | exact @GlobalTheory.ResLoc.resAt_of_chrEq | exact GlobalTheory.ResLoc.resAt_of_chrEq | (intros; apply GlobalTheory.ResLoc.resAt_of_chrEq <;> assumption)
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.fockOnePlace_iso_directSum_partitions : ∀ (a b : ℕ) (α β : ℤ), Iso (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) => Representation.tprod ((twist (detU a ^ α) ((irr a (GlobalTheory.GLDuality.pad a i)).comp (conjU a))).comp (MonoidHom.fst (U a) (U b))) ((twist (detU b ^ β) (irr b (GlobalTheory.GLDuality.pad b i))).comp (MonoidHom.snd (U a) (U b)))) (fockOne a b α β) := by
  first | exact @GlobalTheory.OneFunctional.iso_directSum_fockOne | exact GlobalTheory.OneFunctional.iso_directSum_fockOne | (intros; apply GlobalTheory.OneFunctional.iso_directSum_fockOne <;> assumption)
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.outerTensor_fockOnePlace_iso_unitaryFock : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (α β : ι → ℤ), Iso (outer₂ fun τ => fockOne a b (α τ) (β τ)) (fock a b α β) := by
  first | exact @GlobalTheory.OneFunctional.FockTensor.outer₂_fockOne_iso | exact GlobalTheory.OneFunctional.FockTensor.outer₂_fockOne_iso | (intros; apply GlobalTheory.OneFunctional.FockTensor.outer₂_fockOne_iso <;> assumption)
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.unitaryIrrep_comp_conj_iso_dual : ∀ (n : ℕ), 0 < n → ∀ lam : DomWeight n, Iso ((irr n lam).comp (conjU n) : Representation ℂ (U n) (nablaSq ℂ n lam)) (irr n lam.dual) := by
  first | exact @GlobalTheory.OneFunctional.iso_irr_comp_conjU | exact GlobalTheory.OneFunctional.iso_irr_comp_conjU | (intros; apply GlobalTheory.OneFunctional.iso_irr_comp_conjU <;> assumption)
end
