module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle003
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemClosureRootsOfUnity
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Formalism.LocalRingCardinality.DataHost
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
public import Mathlib.NumberTheory.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.BeWInertOfSigma
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

namespace GlobalTheory

open Formalism.L2.G.Pend in
theorem wittKbar_eq_zero_of_forall_dvd (p : ℕ) [Fact p.Prime] (z : WW p)
    (h : ∀ N : ℕ, (p : WW p) ^ N ∣ z) : z = 0 := by
  have hc : wToC p z = wToC p 0 := by
    rw [map_zero]
    apply eq_of_close
    intro N
    obtain ⟨b, hb⟩ := h N
    rw [sub_zero, hb]
    exact norm_wToC_pow_mul p N b
  exact wToC_injective p hc

theorem dvd_pow_pow_sub_self_of_dvd {W : Type} [CommRing W] (p n : ℕ)
    (h : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (x : W) :
    ∀ j : ℕ, (p : W) ∣ x ^ (p ^ (n * j)) - x := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have e : x ^ (p ^ (n * (j + 1))) = (x ^ (p ^ (n * j))) ^ (p ^ n) := by
      rw [← pow_mul, ← pow_add, mul_add, mul_one]
    rw [e]
    have := dvd_add (h (x ^ (p ^ (n * j)))) ih
    simpa [sub_add_sub_cancel] using this

theorem ringHom_wittKbar_eq_of_modp (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W] (hn : 0 < n)
    (h : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (f g : W →+* Formalism.L2.G.Pend.WW p)
    (hfg : ∀ x, (p : Formalism.L2.G.Pend.WW p) ∣ f x - g x) : f = g := by
  have key : ∀ k : ℕ, ∀ x : W, (p : Formalism.L2.G.Pend.WW p) ^ k ∣ f x - g x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      obtain ⟨y, hy⟩ := dvd_pow_pow_sub_self_of_dvd p n h x k
      have hx : x = x ^ (p ^ (n * k)) - (p : W) * y := by rw [← hy]; ring
      have h1 : (p : Formalism.L2.G.Pend.WW p) ^ (n * k + 1) ∣ (f x) ^ (p ^ (n * k)) - (g x) ^ (p ^ (n * k)) :=
        dvd_sub_pow_of_dvd_sub (hfg x) (n * k)
      have hk : k + 1 ≤ n * k + 1 := by
        have : k ≤ n * k := Nat.le_mul_of_pos_left k hn
        omega
      have h1' := (pow_dvd_pow (p : Formalism.L2.G.Pend.WW p) hk).trans h1
      have h2 : (p : Formalism.L2.G.Pend.WW p) ^ (k + 1) ∣ (p : Formalism.L2.G.Pend.WW p) * (f y - g y) := by
        rw [pow_succ']
        exact mul_dvd_mul_left _ (ih y)
      have e : f x - g x = ((f x) ^ (p ^ (n * k)) - (g x) ^ (p ^ (n * k))) - (p : Formalism.L2.G.Pend.WW p) * (f y - g y) := by
        conv_lhs => rw [hx]
        simp only [map_sub, map_mul, map_pow, map_natCast]
        ring
      rw [e]
      exact dvd_sub h1' h2
  refine RingHom.ext fun x => ?_
  have := wittKbar_eq_zero_of_forall_dvd p (f x - g x) (fun N => key N x)
  exact sub_eq_zero.mp this

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.CobSimeqProof

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (cob)

theorem simeq_neg {K ι : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {f g : MvPowerSeries ι K}
    (h : Formalism.InvariantFactorPaths.G7.Simeq f g) : Formalism.InvariantFactorPaths.G7.Simeq (-f) (-g) := by
  have h' := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K ι).2.1 f g h
  unfold Formalism.InvariantFactorPaths.G7.Simeq at h' ⊢
  rwa [show -f - -g = g - f by ring]

theorem integral_X {K ι : Type} [NormedField K] (i : ι) : Integral (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem cobSimeq : Formalism.L2.KerInert.BeCob.CobSimeq := by
  intro K _ _ _ F hF0 hFI f f' h
  have R := Formalism.InvariantFactorPaths.G7.Top.simeqRules K Unit
  have hs : ∀ (φ : Unit → MvPowerSeries (Fin 2) K), (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) →
      (∀ i, Integral (φ i)) →
      Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.subst φ (f : MvPowerSeries Unit K))
        (MvPowerSeries.subst φ (f' : MvPowerSeries Unit K)) :=
    fun φ h0 hI => R.2.2.2.2 (Fin 2) f f' φ h0 hI h
  have h1 := hs (fun _ => F) (fun _ => hF0) (fun _ => hFI)
  have h2 := simeq_neg (hs (fun _ => MvPowerSeries.X 0) (fun _ => MvPowerSeries.constantCoeff_X _)
    (fun _ => integral_X _))
  have h3 := simeq_neg (hs (fun _ => MvPowerSeries.X 1) (fun _ => MvPowerSeries.constantCoeff_X _)
    (fun _ => integral_X _))
  have R2 := Formalism.InvariantFactorPaths.G7.Top.simeqRules K (Fin 2)
  have H := R2.2.2.2.1 _ _ _ _ (R2.2.2.2.1 _ _ _ _ h1 h2) h3
  have e : ∀ q : PowerSeries K, cob F q = MvPowerSeries.subst (fun _ => F) (q : MvPowerSeries Unit K) +
      -MvPowerSeries.subst (fun _ => (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) (q : MvPowerSeries Unit K) +
      -MvPowerSeries.subst (fun _ => (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) (q : MvPowerSeries Unit K) := by
    intro q
    unfold cob Formalism.InvariantFactorPaths.G7.at1 PowerSeries.subst
    ring
  rw [e f, e f']
  exact H

end GlobalTheory.CobSimeqProof
end
end

section

noncomputable section

namespace GlobalTheory.CoefWfUnram

open Formalism.MainNotions.GL3Theta

variable {p : ℕ} [Fact p.Prime]

theorem inWf_of_kur {x : ℂ_[p]} (hx : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) : InWf x := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | exact @_root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | exact _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | (apply _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur <;> assumption)
  | (intros; apply _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur ..)

theorem coefWf_phW_of_kur (W : WeierstrassCurve ℂ_[p]) (h1 : W.a₁ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p)
    (h2 : W.a₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (h3 : W.a₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (h4 : W.a₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p)
    (h6 : W.a₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) {s2 : ℂ_[p]} (hs : s2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) :
    CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]) := by
  apply _root_.Formalism.L2.KerInert.Dict.coefWf_phW <;> assumption

theorem coefWf_phW : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]), W.a₁ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → ∀ s2 : ℂ_[p], s2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → Formalism.MainNotions.GL3Theta.CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]) :=
  fun _ _ W h1 h2 h3 h4 h6 _ hs => coefWf_phW_of_kur W h1 h2 h3 h4 h6 hs

end GlobalTheory.CoefWfUnram
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SmoothComponents

open Topology TopologicalSpace

theorem irreducibleComponent_eq_closure (Z : Scheme.{0})
    (hdom : ∀ x : Z, IsDomain (Z.presheaf.stalk x)) {C : Set Z} (hC : C ∈ irreducibleComponents Z)
    {x : Z} (hx : x ∈ C) :
    haveI := hdom x
    C = closure {Z.fromSpecStalk x (genericPoint (Spec (Z.presheaf.stalk x)))} := by
  haveI := hdom x
  set ξ := Z.fromSpecStalk x (genericPoint (Spec (Z.presheaf.stalk x)))
  have hCc : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hgen : IsGenericPoint hC.1.genericPoint C := by
    simpa [hCc.closure_eq] using hC.1.isGenericPoint_genericPoint_closure
  have hηx : hC.1.genericPoint ⤳ x := hgen.specializes hx
  have hmem : hC.1.genericPoint ∈ Set.range (Z.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hηx
  obtain ⟨p, hp⟩ := hmem
  have hξη : ξ ⤳ hC.1.genericPoint := by
    rw [← hp]
    exact ((genericPoint_spec (Spec (Z.presheaf.stalk x))).specializes trivial).map
      (Z.fromSpecStalk x).continuous
  have hsub : C ⊆ closure {ξ} := by
    rw [← hgen.def]
    exact closure_minimal (by simpa using specializes_iff_mem_closure.mp hξη) isClosed_closure
  have hirr : IsIrreducible (closure {ξ}) := isIrreducible_singleton.closure
  exact le_antisymm hsub (hC.2 hirr hsub)

end GlobalTheory.SmoothComponents

namespace GlobalTheory.SmoothComponents

open Topology TopologicalSpace

theorem main : ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s]
    [CompactSpace Z], ∃ (J : Type) (_ : Fintype J) (V : J → Z.Opens),
      (∀ i j, i ≠ j → V i ⊓ V j = ⊥) ∧ iSup V = ⊤ ∧ ∀ j, IsIntegral (V j).toScheme := by
  intro Z s d _ _
  have hs : Smooth s := SmoothOfRelativeDimension.smooth d s
  obtain ⟨hred, -, hln⟩ :=
    isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Z s hs
  have hdom : ∀ x : Z, IsDomain (Z.presheaf.stalk x) := fun x ↦
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth s
      (isDomain_and_isIntegrallyClosed_stalk_Sp ℂ) x).1
  haveI : IsNoetherian Z := ⟨⟩
  have hfin : (irreducibleComponents Z).Finite := finite_irreducibleComponents_of_isNoetherian
  have disj : ∀ C ∈ irreducibleComponents Z, ∀ D ∈ irreducibleComponents Z, C ≠ D →
      Disjoint C D := by
    intro C hC D hD hne
    rw [Set.disjoint_left]
    intro x hxC hxD
    exact hne ((irreducibleComponent_eq_closure Z hdom hC hxC).trans
      (irreducibleComponent_eq_closure Z hdom hD hxD).symm)
  have cover : ∀ x : Z, ∃ C ∈ irreducibleComponents Z, x ∈ C := fun x ↦
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x,
      mem_irreducibleComponent⟩
  have hopen : ∀ C ∈ irreducibleComponents Z, IsOpen C := by
    intro C hC
    have hc : Cᶜ = ⋃ D ∈ irreducibleComponents Z \ {C}, D := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff,
        exists_prop]
      constructor
      · intro hx
        obtain ⟨D, hD, hxD⟩ := cover x
        exact ⟨D, ⟨hD, fun h ↦ hx (h ▸ hxD)⟩, hxD⟩
      · rintro ⟨D, ⟨hD, hne⟩, hxD⟩ hxC
        exact Set.disjoint_left.mp (disj D hD C hC hne) hxD hxC
    rw [← isClosed_compl_iff, hc]
    exact (hfin.subset Set.diff_subset).isClosed_biUnion fun D hD ↦ isClosed_of_mem_irreducibleComponents D hD.1
  letI : Fintype (irreducibleComponents Z) := hfin.fintype
  refine ⟨irreducibleComponents Z, inferInstance, fun C ↦ ⟨C.1, hopen C.1 C.2⟩, ?_, ?_, ?_⟩
  · intro i j hij
    apply Opens.ext
    simp only [Opens.coe_inf, Opens.coe_bot]
    exact Set.disjoint_iff_inter_eq_empty.mp (disj i.1 i.2 j.1 j.2 fun h ↦ hij (Subtype.ext h))
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    rw [Opens.mem_iSup]
    obtain ⟨C, hC, hxC⟩ := cover x
    exact ⟨⟨C, hC⟩, hxC⟩
  · intro C
    have hirr : IsIrreducible C.1 := C.2.1
    haveI : IrreducibleSpace (C.1 : Set Z) := Subtype.irreducibleSpace hirr
    let U : Z.Opens := ⟨C.1, hopen C.1 C.2⟩
    change IsIntegral U.toScheme
    haveI : IrreducibleSpace U.toScheme := this
    exact isIntegral_of_irreducibleSpace_of_isReduced _

end GlobalTheory.SmoothComponents
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

theorem card_le_ker_transpose_eq_card_range_le :
    ∀ (k : Type) [Field k] (m n j : ℕ) (z : Matrix (Fin m) (Fin n) k), Nat.card {W : Submodule k (Fin m → k) // Module.finrank k W + j = m ∧ W ≤ LinearMap.ker zᵀ.mulVecLin} = Nat.card {W' : Submodule k (Fin m → k) // Module.finrank k W' = j ∧ LinearMap.range z.mulVecLin ≤ W'} := by
  intro k _ m n j z
  set B : LinearMap.BilinForm k (Fin m → k) := Matrix.toBilin' (1 : Matrix (Fin m) (Fin m) k) with hBdef
  have hB : ∀ x y, B x y = x ⬝ᵥ y := by
    intro x y
    rw [hBdef, Matrix.toBilin'_apply', Matrix.one_mulVec]
  have hrefl : B.IsRefl := by
    intro x y h
    rw [hB] at h ⊢
    rw [dotProduct_comm]; exact h
  have hnd : B.Nondegenerate := by
    rw [hBdef]
    exact Matrix.Nondegenerate.toBilin' (Matrix.nondegenerate_of_det_ne_zero (by simp))
  have hinv : ∀ W : Submodule k (Fin m → k), B.orthogonal (B.orthogonal W) = W :=
    fun W => LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl W
  have hdim : ∀ W : Submodule k (Fin m → k),
      Module.finrank k W + Module.finrank k (B.orthogonal W) = m := by
    intro W
    have h1 := LinearMap.BilinForm.finrank_orthogonal hnd W
    have h2 := Submodule.finrank_le W
    simp only [Module.finrank_fin_fun] at h1 h2
    omega
  have hker : LinearMap.ker zᵀ.mulVecLin = B.orthogonal (LinearMap.range z.mulVecLin) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff, Matrix.mulVecLin_apply]
    constructor
    · rintro h _ ⟨y, rfl⟩
      show B (z.mulVecLin y) x = 0
      rw [hB, Matrix.mulVecLin_apply, dotProduct_comm, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, h, zero_dotProduct]
    · intro h
      ext i
      have h1 : B (z.mulVecLin (Pi.single i 1)) x = 0 := h _ ⟨_, rfl⟩
      rw [hB, Matrix.mulVecLin_apply, dotProduct_comm, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, dotProduct_single, mul_one] at h1
      simpa using h1
  let e : Submodule k (Fin m → k) ≃ Submodule k (Fin m → k) :=
    ⟨B.orthogonal, B.orthogonal, hinv, hinv⟩
  refine Nat.card_congr (e.subtypeEquiv fun W => ?_)
  show _ ↔ Module.finrank k (B.orthogonal W) = j ∧ LinearMap.range z.mulVecLin ≤ B.orthogonal W
  have hd := hdim W
  refine and_congr ⟨fun h => by omega, fun h => by omega⟩ ?_
  rw [hker]
  constructor
  · intro h
    have := LinearMap.BilinForm.orthogonal_le (B := B) h
    rwa [hinv] at this
  · intro h
    have := LinearMap.BilinForm.orthogonal_le (B := B) h
    rwa [hinv] at this

end GlobalTheory.SplitHecke
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

theorem exists_linearEquiv_map_eq_of_finrank_eq {k V : Type} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (W W' : Submodule k V)
    (h : Module.finrank k W = Module.finrank k W') :
    ∃ e : V ≃ₗ[k] V, W.map e.toLinearMap = W' := by
  obtain ⟨U, hU⟩ := W.exists_isCompl
  obtain ⟨U', hU'⟩ := W'.exists_isCompl
  have h1 := Submodule.finrank_add_eq_of_isCompl hU
  have h2 := Submodule.finrank_add_eq_of_isCompl hU'
  have h3 : Module.finrank k U = Module.finrank k U' := by omega
  let a : W ≃ₗ[k] W' := LinearEquiv.ofFinrankEq _ _ h
  let b : U ≃ₗ[k] U' := LinearEquiv.ofFinrankEq _ _ h3
  let e : V ≃ₗ[k] V := (Submodule.prodEquivOfIsCompl W U hU).symm ≪≫ₗ (a.prodCongr b) ≪≫ₗ
    Submodule.prodEquivOfIsCompl W' U' hU'
  have he : ∀ w : W, e w = a w := by
    intro w
    simp [e]
  refine ⟨e, ?_⟩
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have := he ⟨w, hw⟩
    change e w ∈ W'
    simp only at this
    rw [this]
    exact (a ⟨w, hw⟩).2
  · intro w hw
    refine ⟨a.symm ⟨w, hw⟩, (a.symm ⟨w, hw⟩).2, ?_⟩
    change e _ = w
    rw [he]
    simp

theorem exists_gl_map_residue_eq (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ)
    (W W' : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O))
    (h : Module.finrank (IsLocalRing.ResidueField O) W =
      Module.finrank (IsLocalRing.ResidueField O) W') :
    ∃ g : GL (Fin n) O, W.map (g.1.map (IsLocalRing.residue O)).mulVecLin = W' := by
  obtain ⟨e, he⟩ := exists_linearEquiv_map_eq_of_finrank_eq W W' h
  let M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O) := LinearMap.toMatrix' e.toLinearMap
  choose A hA using fun i j => IsLocalRing.residue_surjective (R := O) (M i j)
  have hAM : (Matrix.of A).map (IsLocalRing.residue O) = M := by
    ext i j
    exact hA i j
  have hM : M.det ≠ 0 := by
    have : M.det = LinearMap.det e.toLinearMap := LinearMap.det_toMatrix' _
    rw [this]
    exact (LinearEquiv.isUnit_det' e).ne_zero
  have hu : IsUnit (Matrix.of A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    change ((Matrix.of A).map (IsLocalRing.residue O)).det ≠ 0
    rw [hAM]
    exact hM
  obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  refine ⟨g, ?_⟩
  rw [hg, hAM, ← he]
  congr 1
  exact Matrix.toLin'_toMatrix' e.toLinearMap

end GlobalTheory.SplitHecke
end

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

theorem UpperTheory.Cb.exists_integral_clopen_decomposition_of_smooth :
    ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s] [CompactSpace Z], ∃ (J : Type) (_ : Fintype J) (V : J → Z.Opens), (∀ i j, i ≠ j → V i ⊓ V j = ⊥) ∧ iSup V = ⊤ ∧ ∀ j, IsIntegral (V j).toScheme := by
  first | exact @GlobalTheory.SmoothComponents.main | exact GlobalTheory.SmoothComponents.main

end
end
