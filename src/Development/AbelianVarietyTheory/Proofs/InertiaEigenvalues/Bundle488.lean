module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle004
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle485
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle179
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle307
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle484
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle080
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle437
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle221
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle479
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle480
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT

@[expose] public section

section

noncomputable section

namespace GlobalTheory.HyodoFE

open Formalism Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HyodoDef TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mem_Dcris_iff (x : V ⊗[Qp] B) : x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem φVB_mem_Dcris {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ := by
  rw [mem_Dcris_iff] at hx ⊢
  intro g
  rw [← GlobalTheory.CobCrisLift.φVB_act, hx g]

def oneSubφ : Dcris PD ρ →ₗ[LL] Dcris PD ρ :=
  (LinearMap.id - φVB PD (LL := LL) (V := V)).restrict (p := Dcris PD ρ) (q := Dcris PD ρ)
    (fun x hx => (Dcris PD ρ).sub_mem hx (φVB_mem_Dcris PD ρ hx))

variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def pairs : Submodule LL ((G → V) × (V ⊗[Qp] B)) where
  carrier := {p | p.1 ∈ continuousCocycles ρ ∧ ∀ g, p.1 g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g p.2 - p.2}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, hx⟩ ⟨hb, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, fun g => ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_tmul, hx, hy, map_add (f := _)]
    abel
  smul_mem' := by
    rintro c a ⟨ha, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, fun g => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

def projZ : pairs PD ρ →ₗ[LL] finiteCocycles PD ρ :=
  LinearMap.codRestrict (finiteCocycles PD ρ) ((LinearMap.fst LL (G → V) (V ⊗[Qp] B)).comp (pairs PD ρ).subtype)
    (fun p => ⟨p.2.1, p.1.2, p.2.2⟩)

theorem projZ_surjective : Function.Surjective (projZ PD ρ) := by
  rintro ⟨c, hc, x, hx⟩
  exact ⟨⟨(c, x), hc, hx⟩, rfl⟩

def toDcris : pairs PD ρ →ₗ[LL] Dcris PD ρ :=
  LinearMap.codRestrict (Dcris PD ρ)
    (((LinearMap.id - φVB PD (LL := LL) (V := V)).comp (LinearMap.snd LL (G → V) (V ⊗[Qp] B))).comp
      (pairs PD ρ).subtype)
    (fun p => GlobalTheory.CobCrisLift.sub_φ_mem_Dcris PD ρ p.1.1 p.1.2 p.2.2)

theorem fst_mem_exponential_cocycles (p : pairs PD ρ) (hp : toDcris PD ρ p ∈ LinearMap.range (oneSubφ PD ρ)) :
    (p : (G → V) × (V ⊗[Qp] B)).1 ∈ crystallineCocycles PD ρ := by
  obtain ⟨e, he⟩ := hp
  have he' : (e : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) e
      = p.1.2 - φVB PD (LL := LL) (V := V) p.1.2 := congrArg Subtype.val he
  refine ⟨p.2.1, p.1.2 - e, ?_, fun g => ?_⟩
  · rw [map_sub]
    calc φVB PD (LL := LL) (V := V) p.1.2 - φVB PD (LL := LL) (V := V) e
        = (p.1.2 - (e : V ⊗[Qp] B)) + (((e : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) e)
          - (p.1.2 - φVB PD (LL := LL) (V := V) p.1.2)) := by abel
      _ = p.1.2 - e := by rw [he', sub_self, add_zero]
  · have hg := (mem_Dcris_iff PD ρ e).1 e.2 g
    rw [p.2.2 g, map_sub, hg]
    abel

theorem finrank_finite_cocycles_le [Module.Finite LL (Dcris PD ρ)] :
    finrank LL (finiteCocycles PD ρ) ≤ finrank LL (crystallineCocycles PD ρ) +
      finrank LL ↥(Dcris PD ρ ⊓ LinearMap.ker (φVB PD (LL := LL) (V := V) - LinearMap.id)) := by
  by_cases hf : Module.Finite LL (finiteCocycles PD ρ)
  swap
  · rw [Module.finrank_of_not_finite hf]; exact Nat.zero_le _
  obtain ⟨s, hs⟩ := (projZ PD ρ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 (projZ_surjective PD ρ))
  set N := LinearMap.range (oneSubφ PD ρ) with hN
  let T : finiteCocycles PD ρ →ₗ[LL] (Dcris PD ρ ⧸ N) := N.mkQ ∘ₗ toDcris PD ρ ∘ₗ s
  have hle : crystallineCocycles PD ρ ≤ finiteCocycles PD ρ := fun c ⟨hc, x, _, hx⟩ => ⟨hc, x, hx⟩
  haveI : Module.Finite LL (crystallineCocycles PD ρ) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hmem : ∀ k : LinearMap.ker T, ((k : finiteCocycles PD ρ) : G → V) ∈ crystallineCocycles PD ρ := by
    intro k
    have hk : T k = 0 := LinearMap.mem_ker.1 k.2
    have h := fst_mem_exponential_cocycles PD ρ (s k) ((Submodule.Quotient.mk_eq_zero N).1 hk)
    have hsk : projZ PD ρ (s k) = k := LinearMap.congr_fun hs k
    have hv : ((s k : pairs PD ρ) : (G → V) × (V ⊗[Qp] B)).1 = ((k : finiteCocycles PD ρ) : G → V) :=
      congrArg Subtype.val hsk
    rwa [hv] at h
  have h1 : finrank LL (LinearMap.ker T) ≤ finrank LL (crystallineCocycles PD ρ) := by
    let j : LinearMap.ker T →ₗ[LL] crystallineCocycles PD ρ :=
      LinearMap.codRestrict (crystallineCocycles PD ρ) ((finiteCocycles PD ρ).subtype ∘ₗ (LinearMap.ker T).subtype) hmem
    have hj : Function.Injective j := by
      intro a b hab
      have h := congrArg Subtype.val hab
      simp only [j, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h
      exact Subtype.ext (Subtype.ext h)
    exact LinearMap.finrank_le_finrank_of_injective hj
  have h2 : finrank LL (LinearMap.range T) ≤ finrank LL (Dcris PD ρ ⧸ N) := Submodule.finrank_le _
  have h3 := Submodule.finrank_quotient_add_finrank N
  have h4 := LinearMap.finrank_range_add_finrank_ker (oneSubφ PD ρ)
  have h5 := LinearMap.finrank_range_add_finrank_ker T
  set W := Dcris PD ρ ⊓ LinearMap.ker (φVB PD (LL := LL) (V := V) - LinearMap.id) with hW
  haveI : Module.Finite LL W :=
    Module.Finite.of_injective (Submodule.inclusion (inf_le_left : W ≤ Dcris PD ρ))
      (Submodule.inclusion_injective _)
  have hmemW : ∀ k : LinearMap.ker (oneSubφ PD ρ), ((k : Dcris PD ρ) : V ⊗[Qp] B) ∈ W := by
    intro k
    have hk : oneSubφ PD ρ k = 0 := LinearMap.mem_ker.1 k.2
    have hk' : ((k : Dcris PD ρ) : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) (k : Dcris PD ρ) = 0 :=
      congrArg Subtype.val hk
    refine Submodule.mem_inf.2 ⟨(k : Dcris PD ρ).2, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
    rw [sub_eq_zero] at hk' ⊢
    exact hk'.symm
  have h6 : finrank LL (LinearMap.ker (oneSubφ PD ρ)) ≤ finrank LL W := by
    let j : LinearMap.ker (oneSubφ PD ρ) →ₗ[LL] W :=
      LinearMap.codRestrict W ((Dcris PD ρ).subtype ∘ₗ (LinearMap.ker (oneSubφ PD ρ)).subtype) hmemW
    have hj : Function.Injective j := by
      intro a b hab
      have h := congrArg Subtype.val hab
      simp only [j, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h
      exact Subtype.ext (Subtype.ext h)
    exact LinearMap.finrank_le_finrank_of_injective hj
  have h7 : finrank LL N = finrank LL (LinearMap.range (oneSubφ PD ρ)) := rfl
  omega

end Generic

end GlobalTheory.HyodoFE

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

theorem GlobalTheory.HyodoFE.finrank_finite_le_exponential_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → IsDR (P.PD K) ρ → finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(Dcris (P.PD K) ρ ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V) - LinearMap.id)) := by
  intro l _ P AI _ K V _ _ _ _ _ _ _ ρ _ hdR
  haveI := GlobalTheory.DcrisFin.dcris_finite_of_isDR l P K V ρ hdR
  exact GlobalTheory.HyodoFE.finrank_finite_cocycles_le (P.PD K) ρ
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.FrobDenom

section Abstract

variable {O RA RW M : Type} [CommRing O] [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
  [AddCommGroup M] [Module O M]

theorem repr_incl {κ : Type} (tb : Module.Basis κ O M) (incl : RA →ₐ[O] RW) (u : RA ⊗[O] M) (k : κ) :
    (Algebra.TensorProduct.basis RW tb).repr
        (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M) u) k =
      incl ((Algebra.TensorProduct.basis RA tb).repr u k) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul r t => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add a b ha hb => simp only [map_add (f := _), Finsupp.add_apply, ha, hb]

theorem map_smul_left (f : RW →ₐ[O] RW) (r : RW) (z : RW ⊗[O] M) :
    TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) (r • z) =
      f r • TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x t => simp [TensorProduct.smul_tmul']
  | add a b ha hb => rw [smul_add, map_add (f := _), ha, hb, map_add (f := _), smul_add]

theorem mem_range_of_frob {κ : Type} [Fintype κ] (tb : Module.Basis κ O M) (incl : RA →ₐ[O] RW)
    (φ : RW →ₐ[O] RW)
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (S : Matrix p p RA)
      (S' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φ = S.map incl * Z * S'.map incl + Y.map incl → ∀ a b, Z a b ∈ Set.range incl)
    (r : RA) (z w : RW ⊗[O] M)
    (hw : w ∈ LinearMap.range (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M)))
    (h : TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[O] M) z = incl r • z + w) :
    z ∈ LinearMap.range (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M)) := by
  classical
  obtain ⟨w', rfl⟩ := hw
  set tt := Algebra.TensorProduct.basis RW tb with htt
  set ta := Algebra.TensorProduct.basis RA tb with hta
  have key := hA κ Unit (Matrix.of fun k _ => tt.repr z k) (Matrix.diagonal fun _ => r) 1
    (Matrix.of fun k _ => ta.repr w' k) (by
      ext k u
      have h1 := congrArg (fun x => tt.repr x k) h
      simp only [map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h1
      rw [htt, GlobalTheory.Sandwich.repr_phi, repr_incl, ← htt, ← hta] at h1
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_map (map_zero _)]
      simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.diagonal_mul]
      exact h1)
  choose c hc using fun k => key k ()
  refine ⟨∑ k, c k ⊗ₜ[O] tb k, ?_⟩
  conv_rhs => rw [← tt.sum_repr z]

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hc k
  simp only [Matrix.of_apply] at this
  rw [← this, htt, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  simp

end Abstract

section Alg

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

theorem φ_prod (φ : A →ₐ[O] A) (X Q : A) (hXQ : φ X = X * Q) (m : ℕ) :
    φ (∏ j ∈ Finset.range (m + 1), (φ ^ j) X) =
      (∏ j ∈ Finset.range (m + 1), (φ ^ j) X) * ∏ j ∈ Finset.range (m + 1), (φ ^ j) Q := by
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← AlgHom.mul_apply, ← pow_succ', pow_succ, AlgHom.mul_apply, hXQ, map_mul]

theorem multiset_dvd (f : ℕ → A) (m : ℕ) (J : Multiset ℕ) (hJ : ∀ j ∈ J, j ≤ m) :
    (J.map f).prod ∣ (∏ j ∈ Finset.range (m + 1), f j) ^ Multiset.card J := by
  induction J using Multiset.induction_on with
  | empty => simp
  | cons j J ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, mul_comm]
    refine mul_dvd_mul (ih fun i hi => hJ i (Multiset.mem_cons_of_mem hi)) ?_
    exact Finset.dvd_prod_of_mem f
      (Finset.mem_range.2 (Nat.lt_succ_of_le (hJ j (Multiset.mem_cons_self j J))))

theorem X_dvd (φ : A →ₐ[O] A) (X : A) (m : ℕ) : X ∣ ∏ j ∈ Finset.range (m + 1), (φ ^ j) X := by
  have := Finset.dvd_prod_of_mem (fun j => (φ ^ j) X) (Finset.mem_range.2 (Nat.succ_pos m))
  simpa using this

end Alg

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n}

theorem jD_smulA (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (a : LetA O n)
    (x : W.DD T) : E.jD T (a • x) = inclR (E.io a) • E.jD T x := by
  rw [← algebraMap_smul W.EE a x, E.jD_smul, E.ioE_ext]



theorem of_sand (E : EtTie W RA RW inclR φR gR πA)
    (hφ : ∀ a, inclR (E.io (W.φA a)) = φR (inclR (E.io a)))
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (S : Matrix p p RA)
      (S' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φR = S.map inclR * Z * S'.map inclR + Y.map inclR → ∀ a b, Z a b ∈ Set.range inclR)
    (T : LocLat G Qp LL O) {κ : Type} [Fintype κ] (tb : Module.Basis κ O ↥T.L.T) (m₀ : ℕ)
    (hm₀ : ∀ x ∈ W.N T, ∃ y : TW RA T, TWincl inclR T y =
      TensorProduct.map (LinearMap.mulLeft O (inclR (E.io W.X) ^ m₀)) LinearMap.id (E.jD T x))
    (J : Multiset ℕ) (y : W.DD T) (hy : (J.map fun j => (W.φA ^ j) W.Q).prod • y ∈ W.N T)
    (b : TW RW T) (hb : TWmap φR T b - b = E.jD T y) (m : ℕ) (hJ : ∀ j ∈ J, j ≤ m) :
    ∃ a : ℕ, TensorProduct.map (LinearMap.mulLeft O
      (inclR (E.io (∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X)) ^ a)) LinearMap.id b ∈
        TAinf inclR T := by
  set Y := ∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X with hY
  set L := ∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.Q with hL
  set Jp := (J.map fun j => (W.φA ^ j) W.Q).prod with hJp
  have hYL : W.φA Y = Y * L := φ_prod W.φA W.X W.Q W.φA_X m
  refine ⟨m₀ + Multiset.card J, ?_⟩
  rw [GlobalTheory.NL.SandArb.map_mulLeft]
  have hdiv : W.X ^ m₀ * Jp ∣ (Y * L) ^ (m₀ + Multiset.card J) := by
    rw [mul_pow, pow_add, pow_add]
    refine (mul_dvd_mul (pow_dvd_pow_of_dvd (X_dvd W.φA W.X m) m₀) (multiset_dvd _ m J hJ)).trans ?_
    exact ⟨Y ^ Multiset.card J * L ^ m₀, by ring⟩
  obtain ⟨R, hR⟩ := hdiv
  set a := m₀ + Multiset.card J with ha
  have hb' : TWmap φR T b = E.jD T y + b := sub_eq_iff_eq_add.mp hb
  have hφc : TensorProduct.map φR.toLinearMap (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T)
      (inclR (E.io Y) ^ a • b) =
      inclR (E.io (L ^ a)) • (inclR (E.io Y) ^ a • b) + inclR (E.io ((Y * L) ^ a)) • E.jD T y := by
    rw [map_smul_left, map_pow, ← hφ, hYL]
    change inclR (E.io (Y * L)) ^ a • TWmap φR T b = _
    rw [hb', smul_add, add_comm, smul_smul, map_pow, map_pow, map_pow, map_pow, map_mul, map_mul,
      mul_pow, mul_comm]
  have hw : inclR (E.io ((Y * L) ^ a)) • E.jD T y ∈
      LinearMap.range (TensorProduct.map inclR.toLinearMap (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T)) := by
    obtain ⟨y', hy'⟩ := hm₀ _ hy
    rw [GlobalTheory.NL.SandArb.map_mulLeft, jD_smulA] at hy'
    rw [hR, map_mul, map_mul, map_mul, map_mul, mul_comm, mul_smul, mul_smul, map_pow, map_pow]
    refine GlobalTheory.Sandwich.incl_smul_mem inclR _ _ ?_
    rw [← hy']
    exact ⟨y', rfl⟩
  have key := mem_range_of_frob tb inclR φR hA (E.io (L ^ a)) _ _ hw hφc
  exact key

end Generic




theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (J : Multiset ℕ) (y : W.DD T), (J.map fun j => (W.φA ^ j) W.Q).prod • y ∈ W.N T → ∀ b : TW (RW LL) T, TWmap (φRW LL) T b - b = E.jD T y → ∀ m : ℕ, (∀ j ∈ J, j ≤ m) → ∃ a : ℕ, TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (inclR LL (E.io (∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X)) ^ a)) LinearMap.id b ∈ TAinf (inclR LL) T := by
  intro D HW F l _ K s LL h W E T hT J y hy b hb m hJ
  obtain ⟨m₀, hm₀, -⟩ := GlobalTheory.NL.SandArb.sandwich D HW F l K s LL h T hT
  have : Module.Free ↥(OL LL) ↥T.L.T := T.L.free
  have : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  exact of_sand E (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.1
    (GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff l LL) T
    (Module.Free.chooseBasis ↥(OL LL) ↥T.L.T) m₀ hm₀ J y hy b hb m hJ

end GlobalTheory.NL.FrobDenom
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem exists_acris_Lam : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (y : ℕ → Fl l), 2 ≤ h → (∀ k, ‖sh (y k)‖ ≤ ‖(l : ℂ_[l])‖) → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = abelian₂ h j y := by
  intro l _ h y hh hy
  choose w hw hθ using fun k => GlobalTheory.T.exists_frobeniusSeries_acris_untilt l h (y k) hh (hy k)
  haveI : IsAdicComplete (Ideal.span {(l : Acris l)}) (Acris l) := (GlobalTheory.MemLoc.acris_basic l).1
  obtain ⟨W, hW, hsum⟩ := GlobalTheory.T.exists_eigenvector_hasSum_adicComplete_frobenius l (Acris l) (GlobalTheory.MemLoc.phiA l) h w hw
  refine ⟨W, hW, fun Θ hΘ htm j => ?_⟩
  set φ := GlobalTheory.MemLoc.phiA l
  have hS := hsum (Θ.comp (φ ^ j)) (fun a => hΘ _)
  simp only [RingHom.coe_comp, RingHom.coe_pow, Function.comp_apply] at hS
  unfold abelian₂
  rw [← hS.tsum_eq]
  congr 1
  funext k
  rw [hθ k Θ hΘ htm j]

end GlobalTheory.PSer
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem untilt_ext_sum_sub_le : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F)
    (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (α : Type) (s : Finset α) (z : α → F) (R : ℝ), 0 ≤ R → (∀ a ∈ s, ‖z a‖ ≤ R) →
      ‖tsh (∑ a ∈ s, z a) - ∑ a ∈ s, tsh (z a)‖ ≤ ‖(l : ℂ_[l])‖ * R := by
  intro l _ F _ ι tsh hn hι hsurj α s z R hR hz
  classical
  obtain ⟨-, -, -, -, -, hon, -, -⟩ := GlobalTheory.PSer.Laws.sh_laws l
  have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := GlobalTheory.PSer.Laws.norm_l
  have hlpos : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by rw [hl]; exact inv_lt_one_of_one_lt₀ hlpos
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := by rw [hl]; exact inv_pos.2 (by linarith)
  obtain ⟨w, hw⟩ := hon (l : ℂ_[l]) hl1.le
  have hnw : ‖ι w‖ = ‖(l : ℂ_[l])‖ := by rw [← hn, hι, hw]

  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖ι w‖ ^ N * R ≤ 1 := by
    rcases le_or_gt R 1 with h | h
    · exact ⟨0, by simpa using h⟩
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (by linarith : (0:ℝ) < R)) (hnw ▸ hl1)
      refine ⟨N, ?_⟩
      have := mul_lt_mul_of_pos_right hN (by linarith : (0:ℝ) < R)
      rw [inv_mul_cancel₀ (by linarith)] at this
      exact this.le
  set c : F := ι w ^ N with hc
  have hcn : ‖c‖ = ‖ι w‖ ^ N := by rw [hc, norm_pow]
  have hcpos : 0 < ‖c‖ := by rw [hcn, hnw]; exact pow_pos hl0 N
  have hx : ∀ a, ∃ x : Fl l, ι x = if a ∈ s then c * z a else 0 := by
    intro a
    split_ifs with ha
    · refine hsurj _ ?_
      rw [norm_mul, hcn]
      calc ‖ι w‖ ^ N * ‖z a‖ ≤ ‖ι w‖ ^ N * R :=
            mul_le_mul_of_nonneg_left (hz a ha) (pow_nonneg (norm_nonneg _) _)
        _ ≤ 1 := hN
    · exact ⟨0, map_zero ι⟩
  choose x hxe using hx
  have hxa : ∀ a ∈ s, ι (x a) = c * z a := fun a ha => by rw [hxe, if_pos ha]
  have hsa : ∀ a ∈ s, sh (x a) = tsh c * tsh (z a) := fun a ha => by
    rw [← hι, hxa a ha, map_mul]
  have hss : sh (∑ a ∈ s, x a) = tsh c * tsh (∑ a ∈ s, z a) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hι, map_sum, Finset.sum_congr rfl hxa, ← Finset.mul_sum, map_mul]
  have hbd : ∀ a ∈ s, ‖sh (x a)‖ ≤ ‖c‖ * R := fun a ha => by
    rw [hsa a ha, norm_mul, hn, hn]
    exact mul_le_mul_of_nonneg_left (hz a ha) (norm_nonneg _)
  have key := (untilt_sum_sub_le l α s (‖c‖ * R) x (mul_nonneg (norm_nonneg _) hR) hbd).1
  rw [hss, Finset.sum_congr rfl hsa, ← Finset.mul_sum, ← mul_sub, norm_mul, hn] at key
  have : ‖c‖ * ‖tsh (∑ a ∈ s, z a) - ∑ a ∈ s, tsh (z a)‖ ≤ ‖c‖ * (‖(l : ℂ_[l])‖ * R) := by
    linarith [key]
  exact le_of_mul_le_mul_left this hcpos

end GlobalTheory
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.norm_sh_sum_sub_sum_sh_le : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (s : Finset ι) (r : ℝ) (x : ι → Fl l), 0 ≤ r → (∀ i ∈ s, ‖sh (x i)‖ ≤ r) → ‖sh (∑ i ∈ s, x i) - ∑ i ∈ s, sh (x i)‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (∑ i ∈ s, x i)‖ ≤ r := by
  first | exact @GlobalTheory.untilt_sum_sub_le | exact GlobalTheory.untilt_sum_sub_le | (intros; apply GlobalTheory.untilt_sum_sub_le <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.exists_cuspidal_list_harishChandra_pairing_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (χ : Gn g n → ℂ), IsIrr χ → ∃ L : List (Pc g), (∀ p ∈ L, IsCusp p.2) ∧ degL L = n ∧ ip χ (hcL L n) ≠ 0 := by
  first | exact @GlobalTheory.GLq.SuppCusp.exists_cusp_list | exact GlobalTheory.GLq.SuppCusp.exists_cusp_list | (intros; apply GlobalTheory.GLq.SuppCusp.exists_cusp_list <;> assumption)
end
