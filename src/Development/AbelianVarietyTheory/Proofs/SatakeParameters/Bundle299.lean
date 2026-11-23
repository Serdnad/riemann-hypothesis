module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle011
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.KernelLattices.Bundle004
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle289
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle017
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle218
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle276
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle288
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.EqOneOfPh
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle005
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle021
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle290
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.admissibleKernelSeries_inertPrime_nonConjugateFrobenius : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∃ ep be, BeFam D ep be ∧ OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be (fun _ _ => -1)) Y := by
  first | exact @GlobalTheory.KerStd.exists_beFam_evenConditionsInert_of_kerEnt | exact GlobalTheory.KerStd.exists_beFam_evenConditionsInert_of_kerEnt | (intros; apply GlobalTheory.KerStd.exists_beFam_evenConditionsInert_of_kerEnt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitGen

theorem top_step : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), _root_.Formalism.DivisionValues.conjPl P ≠ P → ∀ d : List ℤ, IsLab V P d → (∀ x ∈ d, 0 ≤ x) → (∃ x ∈ d, 0 < x) → ∃ m : ℕ, 0 < m ∧ ∃ c : List ℤ →₀ ℂ, (∀ d' ∈ c.support, (∀ x ∈ d', 0 ≤ x) ∧ d'.sum = d.sum ∧ (d'.map fun x => x ^ 2).sum < (d.map fun x => x ^ 2).sum) ∧ ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (d.map fun x => if 0 < x then x - 1 else x) 1) (opOf π P (Finsupp.single (dualLab (splitLab V.rank (d.filter fun x => 0 < x).length)) 1) u) = (m : ℂ) • opOf π P (Finsupp.single d 1) u + opOf π P c u := GlobalTheory.T.sphericalHecke_split_top_degree_recursion

theorem central_shift : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), _root_.Formalism.DivisionValues.conjPl P ≠ P → ∀ (d : List ℤ) (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (splitLab V.rank V.rank) 1) (opOf π P (Finsupp.single d 1) u) = opOf π P (Finsupp.single (d.map fun x => x - 1) 1) u := GlobalTheory.T.sphericalHecke_scalarLabel_comp_eq_shiftDown_split

section Gen

variable {D : D7} (V : HSp D) (P : Pl D.host.E) {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)

def gens : Set (Module.End ℂ M) :=
  {x | ∃ k, k ≤ V.rank ∧ (x = opOf π P (Finsupp.single (splitLab V.rank k) 1) ∨
    x = opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1))}

def Good (c : List ℤ →₀ ℂ) : Prop :=
  ∃ a ∈ Algebra.adjoin ℂ (gens V P π), ∀ u : M, (∀ k ∈ hyp V P, π k u = u) → a u = opOf π P c u

variable {V P π}

theorem opOf_eq_sum (c : List ℤ →₀ ℂ) (u : M) :
    opOf π P c u = ∑ d ∈ c.support, c d • opOf π P (Finsupp.single d 1) u := by
  rw [opOf, Finsupp.sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply, GlobalTheory.SphLabelOps.opOf_single, LinearMap.sum_apply]

theorem good_of_support {c : List ℤ →₀ ℂ} (h : ∀ d ∈ c.support, Good V P π (Finsupp.single d 1)) :
    Good V P π c := by
  classical
  choose a ha he using h
  refine ⟨∑ d ∈ c.support.attach, c d • a d.1 d.2, Subalgebra.sum_mem _ fun d _ => Subalgebra.smul_mem _ (ha _ _) _,
    fun u hu => ?_⟩
  rw [opOf_eq_sum, LinearMap.sum_apply, ← Finset.sum_attach c.support]
  exact Finset.sum_congr rfl fun d _ => by rw [LinearMap.smul_apply, he _ _ u hu]

theorem good_gen {x : Module.End ℂ M} (hx : x ∈ gens V P π) : x ∈ Algebra.adjoin ℂ (gens V P π) :=
  Algebra.subset_adjoin hx

theorem good_nonlab {d : List ℤ} (h : ¬ IsLab V P d) : Good V P π (Finsupp.single d 1) := by
  refine ⟨0, Subalgebra.zero_mem _, fun u _ => ?_⟩
  rw [GlobalTheory.SphLabelOps.opOf_single, Hk3.rep, dite_eq_right h, Finset.sum_empty, LinearMap.zero_apply]

theorem fixed_opOf (c : List ℤ →₀ ℂ) {u : M} (hu : ∀ k ∈ hyp V P, π k u = u) : ∀ k ∈ hyp V P, π k (opOf π P c u) = opOf π P c u :=
  (GlobalTheory.SphLabelOps.label_operators V P).2.1 c M π u hu

theorem good_nonneg (hP : _root_.Formalism.DivisionValues.conjPl P ≠ P) : ∀ s q : ℕ, ∀ d : List ℤ, (∀ x ∈ d, 0 ≤ x) → d.sum = (s : ℤ) →
    (d.map fun x => x ^ 2).sum = (q : ℤ) → Good V P π (Finsupp.single d 1) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ihs =>
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ihq =>
  intro d hd hs hq
  by_cases hl : IsLab V P d
  swap
  · exact good_nonlab hl
  by_cases hpos : ∃ x ∈ d, 0 < x
  · obtain ⟨m, hm, c, hc, hrel⟩ := top_step V P hP d hl hd hpos
    set d1 := d.map fun x => if 0 < x then x - 1 else x with hd1
    have hd1n : ∀ x ∈ d1, 0 ≤ x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have := hd y hy
      split_ifs <;> omega
    have hlt : d1.sum < d.sum := by
      have := List.sum_lt_sum (l := d) (fun x => if 0 < x then x - 1 else x) id
        (fun x _ => by simp only [id]; split_ifs <;> omega)
        (by obtain ⟨x, hx, hx0⟩ := hpos; exact ⟨x, hx, by simp only [id]; rw [if_pos hx0]; omega⟩)
      simpa using this
    have hs1 : 0 ≤ d1.sum := List.sum_nonneg hd1n
    have hq1 : 0 ≤ (d1.map fun x => x ^ 2).sum := List.sum_nonneg fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      positivity
    have g1 : Good V P π (Finsupp.single d1 1) :=
      ihs d1.sum.toNat (by omega) _ d1 hd1n (by omega) (Int.toNat_of_nonneg hq1).symm
    have gc : Good V P π c := good_of_support fun d' hd' => by
      obtain ⟨h1, h2, h3⟩ := hc d' hd'
      have h4 : 0 ≤ (d'.map fun x => x ^ 2).sum := List.sum_nonneg fun x hx => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
        positivity
      exact ihq _ (by omega) d' h1 (by omega) (Int.toNat_of_nonneg h4).symm
    obtain ⟨a1, ha1, e1⟩ := g1
    obtain ⟨ac, hac, ec⟩ := gc
    set k := (d.filter fun x => 0 < x).length
    have hk : k ≤ V.rank := by
      have := ((GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing V P d).1 hl).1
      rw [← this]
      exact List.length_filter_le _ _
    refine ⟨(m : ℂ)⁻¹ • (a1 * opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1) - ac),
      Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.mul_mem _ ha1 (good_gen ⟨k, hk, Or.inr rfl⟩)) hac) _,
      fun u hu => ?_⟩
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, e1 _ (fixed_opOf _ hu), hrel M π u hu,
      ec u hu, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hm', one_smul]
  · push_neg at hpos
    have h0 : d = splitLab V.rank 0 := by
      have hlen := ((GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing V P d).1 hl).1
      rw [splitLab, Nat.sub_zero, List.replicate_zero, List.append_nil, ← hlen]
      exact List.eq_replicate_iff.2 ⟨rfl, fun x hx => le_antisymm (hpos x hx) (hd x hx)⟩
    refine ⟨_, good_gen ⟨0, Nat.zero_le _, Or.inl rfl⟩, fun u _ => by rw [h0]⟩

theorem shift (hP : _root_.Formalism.DivisionValues.conjPl P ≠ P) (u : M) (hu : ∀ k ∈ hyp V P, π k u = u) :
    ∀ (j : ℕ) (d : List ℤ), ((opOf π P (Finsupp.single (splitLab V.rank V.rank) 1)) ^ j)
      (opOf π P (Finsupp.single (d.map fun x => x + (j : ℤ)) 1) u) = opOf π P (Finsupp.single d 1) u := by
  intro j
  induction j with
  | zero => intro d; simp
  | succ j ih =>
    intro d
    rw [pow_succ, Module.End.mul_apply, central_shift V P hP _ M π u hu, List.map_map, ← ih d]
    congr 4
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp_apply, Nat.cast_succ]
    ring

end Gen

theorem gen_split : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), _root_.Formalism.DivisionValues.conjPl P ≠ P → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (d : List ℤ), ∃ a ∈ Algebra.adjoin ℂ {x : Module.End ℂ M | ∃ k, k ≤ V.rank ∧ (x = opOf π P (Finsupp.single (splitLab V.rank k) 1) ∨ x = opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1))}, ∀ u : M, (∀ k ∈ hyp V P, π k u = u) → a u = opOf π P (Finsupp.single d 1) u := by
  intro D V P hP M _ _ π d
  set t : ℕ := (d.map fun x => (-x).toNat).sum
  have ht : ∀ x ∈ d.map (fun x => x + (t : ℤ)), 0 ≤ x := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun x : ℤ => (-x).toNat) hx)
    omega
  have hs : 0 ≤ (d.map fun x => x + (t : ℤ)).sum := List.sum_nonneg ht
  have hq : 0 ≤ ((d.map fun x => x + (t : ℤ)).map fun x => x ^ 2).sum := List.sum_nonneg fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    positivity
  obtain ⟨a, ha, he⟩ := good_nonneg (V := V) (P := P) (π := π) hP _ _ _ ht (Int.toNat_of_nonneg hs).symm
    (Int.toNat_of_nonneg hq).symm
  refine ⟨(opOf π P (Finsupp.single (splitLab V.rank V.rank) 1)) ^ t * a,
    Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (good_gen ⟨V.rank, le_rfl, Or.inl rfl⟩) _) ha, fun u hu => ?_⟩
  rw [Module.End.mul_apply, he u hu, shift hP u hu]

end GlobalTheory.SplitGen
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

open Formalism.UG.P

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def oneExc (w : HeightOneSpectrum (𝓞 F)) (a : w.adicCompletion F) : FiniteAdeleRing (𝓞 F) F :=
  afsplitI w a + (1 - afsplitI w 1)

theorem oneExc_self (w : HeightOneSpectrum (𝓞 F)) (a : w.adicCompletion F) : oneExc w a w = a := by
  rw [oneExc, afsplit_add_apply, afsplit_sub_apply, afsplitI_self, afsplitI_self, afsplit_one_apply, sub_self, add_zero]

theorem oneExc_ne (w w' : HeightOneSpectrum (𝓞 F)) (h : w' ≠ w) (a : w.adicCompletion F) : oneExc w a w' = 1 := by
  rw [oneExc, afsplit_add_apply, afsplit_sub_apply, afsplitI_ne w w' h, afsplitI_ne w w' h, afsplit_one_apply, sub_zero,
    zero_add]

theorem oneExc_mem (w : HeightOneSpectrum (𝓞 F)) (a : w.adicCompletion F) (ha : a ∈ w.adicCompletionIntegers F) :
    oneExc w a ∈ intAd F := by
  intro w'
  by_cases h : w' = w
  · subst h; rw [oneExc_self]; exact ha
  · rw [oneExc_ne w w' h]; exact one_mem _

theorem mem_RInt_of_quad (z : AfE F E) (w : HeightOneSpectrum (𝓞 F)) (a b : w.adicCompletion F)
    (ha : a ∈ w.adicCompletionIntegers F) (hb : b ∈ w.adicCompletionIntegers F)
    (hoff : ∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → prV (E := E) w' z = 1)
    (hv : (prV (E := E) w z - (1 : E) ⊗ₜ[F] a) * (prV (E := E) w z - (1 : E) ⊗ₜ[F] b) = 0) :
    z ∈ RInt F E := by
  obtain ⟨ι, hι⟩ := GlobalTheory.TwU.exists_isAdIso F E
  have hca : ((1 : E) ⊗ₜ[F] oneExc w a : AfE F E) ∈ RInt F E :=
    Subring.subset_closure (Or.inr ⟨⟨_, oneExc_mem w a ha⟩, rfl⟩)
  have hcb : ((1 : E) ⊗ₜ[F] oneExc w b : AfE F E) ∈ RInt F E :=
    Subring.subset_closure (Or.inr ⟨⟨_, oneExc_mem w b hb⟩, rfl⟩)
  have hq : (z - (1 : E) ⊗ₜ[F] oneExc w a) * (z - (1 : E) ⊗ₜ[F] oneExc w b) = 0 := by
    refine afsplit_inj _ fun w' => ?_
    rw [map_mul, map_sub, map_sub, afsplit_prV_tmul, afsplit_prV_tmul]
    by_cases h : w' = w
    · subst h
      rw [oneExc_self, oneExc_self]
      exact hv
    · rw [oneExc_ne w w' h, oneExc_ne w w' h, hoff w' h, ← Algebra.TensorProduct.one_def, sub_self, zero_mul]
  rw [hι.2]
  intro P
  have h1 := congrArg (fun x => ι x P) hq
  simp only [map_mul, map_sub, map_zero] at h1
  have h2 : (ι z P - ι ((1 : E) ⊗ₜ[F] oneExc w a) P) * (ι z P - ι ((1 : E) ⊗ₜ[F] oneExc w b) P) = 0 := h1
  rcases mul_eq_zero.1 h2 with h | h
  · rw [sub_eq_zero.1 h]; exact (hι.2 _).1 hca P
  · rw [sub_eq_zero.1 h]; exact (hι.2 _).1 hcb P

end SlopeTestRemainingChoices

section Main

theorem mem_intU_of_oneOff_ordA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) [Fact p.Prime], LocGood σ J A → LocInt A →
    SplAlg A → ∀ v, ∀ y ∈ U1 σ, OneOff (A.pl v).1 y → ordA A v y = 0 → y ∈ intU F E := by
  intro F E _ _ _ _ _ σ n p G A J _ hG hI hS v y hy hoff hord
  set w := (A.pl v).1 with hw
  set s := A.spl v (prV (E := E) w (y : AfE F E)) with hs_def
  have hy1 : (y : AfE F E) * sigR σ (FiniteAdeleRing (𝓞 F) F) (y : AfE F E) = 1 := by
    have h := congrArg Units.val (MonoidHom.mem_ker.1 hy)
    exact h
  have hprod : prV (E := E) w (y : AfE F E) * sigR σ (w.adicCompletion F) (prV (E := E) w (y : AfE F E)) = 1 := by
    have h := congrArg (prV (E := E) w) hy1
    rw [map_mul, map_one] at h
    rw [← h]
    congr 1
    exact (DFunLike.congr_fun (afsplit_prV_comp_sigR σ w) _).symm
  have hss : s.1 * s.2 = 1 := by
    have h := congrArg (A.spl v) hprod
    rw [map_mul, hG.sig v, map_one] at h
    exact congrArg Prod.fst h
  have hss' : s.2 * s.1 = 1 := by rw [mul_comm]; exact hss
  have hset := G.P.setting v
  haveI := hset.frac_alt
  have hp := hset.p_unif
  set x : G.P.Qq v := (A.eQ v).symm s.1 with hx_def
  have hxe : A.eQ v x = s.1 := RingEquiv.apply_symm_apply _ _
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hxe
    rw [← hxe, zero_mul] at hss
    exact zero_ne_one hss
  obtain ⟨k, u, hu⟩ := exists_eq_unit_mul_zpow₂ hp hx0
  have hk : k = 0 := by
    have h1 : ordA A v y = ordP (G.P.W v) p x := rfl
    rw [h1, hu, ordP_eq hp] at hord
    exact hord
  subst hk
  rw [zpow_zero, mul_one] at hu
  have ha : s.1 ∈ w.adicCompletionIntegers F := by
    rw [← hxe]
    exact (hI v x).1 ⟨u, hu.symm⟩
  have hb : s.2 ∈ w.adicCompletionIntegers F := by
    have h2 : s.2 = A.eQ v x⁻¹ := by
      rw [map_inv₀, hxe]
      exact eq_inv_of_mul_eq_one_right hss
    rw [h2]
    refine (hI v x⁻¹).1 ⟨(u⁻¹ : (G.P.W v)ˣ), ?_⟩
    rw [hu]
    exact map_units_inv (algebraMap (G.P.W v) (G.P.Qq v) : G.P.W v →* G.P.Qq v) u
  have key : ∀ t : E ⊗[F] w.adicCompletion F, ((A.spl v t).1 - s.1) * ((A.spl v t).1 - s.2) = 0 →
      ((A.spl v t).2 - s.1) * ((A.spl v t).2 - s.2) = 0 →
      (t - (1 : E) ⊗ₜ[F] s.1) * (t - (1 : E) ⊗ₜ[F] s.2) = 0 := by
    intro t h1 h2
    apply (A.spl v).injective
    rw [map_mul, map_sub, map_sub, hS v, hS v, map_zero]
    exact Prod.ext h1 h2
  have hyR : (y : AfE F E) ∈ RInt F E := by
    refine mem_RInt_of_quad _ w s.1 s.2 ha hb hoff (key _ ?_ ?_)
    · show (s.1 - s.1) * (s.1 - s.2) = 0
      rw [sub_self, zero_mul]
    · show (s.2 - s.1) * (s.2 - s.2) = 0
      rw [sub_self, mul_zero]
  have hinv : ∀ w' : HeightOneSpectrum (𝓞 F),
      prV (E := E) w' ((y⁻¹ : (AfE F E)ˣ) : AfE F E) * prV (E := E) w' (y : AfE F E) = 1 := by
    intro w'
    rw [← map_mul, Units.inv_mul, map_one]
  set t := A.spl v (prV (E := E) w ((y⁻¹ : (AfE F E)ˣ) : AfE F E)) with ht_def
  have hts : t * s = 1 := by rw [ht_def, hs_def, ← map_mul, hinv w, map_one]
  have ht1 : t.1 = s.2 := by
    have h : t.1 * s.1 = 1 := congrArg Prod.fst hts
    calc t.1 = t.1 * (s.1 * s.2) := by rw [hss, mul_one]
      _ = (t.1 * s.1) * s.2 := (mul_assoc _ _ _).symm
      _ = s.2 := by rw [h, one_mul]
  have ht2 : t.2 = s.1 := by
    have h : t.2 * s.2 = 1 := congrArg Prod.snd hts
    calc t.2 = t.2 * (s.2 * s.1) := by rw [hss', mul_one]
      _ = (t.2 * s.2) * s.1 := (mul_assoc _ _ _).symm
      _ = s.1 := by rw [h, one_mul]
  have hyR' : ((y⁻¹ : (AfE F E)ˣ) : AfE F E) ∈ RInt F E := by
    refine mem_RInt_of_quad _ w s.1 s.2 ha hb (fun w' h => ?_) (key _ ?_ ?_)
    · have h3 := hinv w'
      rwa [hoff w' h, mul_one] at h3
    · show (t.1 - s.1) * (t.1 - s.2) = 0
      rw [ht1, sub_self, mul_zero]
    · show (t.2 - s.1) * (t.2 - s.2) = 0
      rw [ht2, sub_self, zero_mul]
  exact (Submonoid.mem_units_iff _ _).2 ⟨hyR, hyR'⟩

end Main

end GlobalTheory.TwV.Xc

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.Pdv

theorem colSide_of_choices {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts}
    {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hN : GlobalTheory.Pdv.ColNorm I)
    (hX_eq : t.X = B.fields) (hseam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)) (hPr : HEq t.Pr (B.primes X))
    (hCh : HEq t.Ch I.Ch) (hsel : HEq t.sel I.sel) (hS : t.S = I.S) (htup : HEq t.tup I.tup) (hcst : HEq t.cst I.cst)
    (hidx : HEq t.idx I.idx) (hm2 : t.m2 = B.R.m - 2) (hglob : HEq t.glob I.glob) : GlobalTheory.KerJ.ColSide t := by
  have hb := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have kCst : ∀ (X' : Fields) (Pr' : Primes X') (sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)) (S' : Set ℕ)
      (tup' : (I.rec7 l Z).what₂.Tup → Tup X'.F X'.E X'.K S') (cst' : ∀ μ, LocCst X' (rowSG Pr' sel' (tup' μ))),
      X' = B.fields → HEq Pr' (B.primes X) → HEq sel' I.sel → S' = I.S → HEq tup' I.tup → HEq cst' I.cst →
      ∀ μ, (cst' μ).sharp = true ∧ (I.rec7 l Z).R.m ≤ (cst' μ).A ∧ 2 * (cst' μ).M ≤ twTopDepth (I.rec7 l Z).R := by
    rintro X' Pr' sel' S' tup' cst' rfl h1 h2 rfl h3 h4
    obtain rfl := eq_of_heq h1
    obtain rfl := eq_of_heq h2
    obtain rfl := eq_of_heq h3
    obtain rfl := eq_of_heq h4
    intro μ
    have h5 := (hN μ)
    refine ⟨hI.sharp μ, h5.1, ?_⟩
    show 2 * (I.cst μ).M ≤ 4 * B.R.m + 1
    omega
  refine ⟨?fields, ?sel, ?bad, ?chOk, ?chars, ?sharp, ?deep, ?repOne⟩
  case fields => exact hX_eq ▸ hb.1
  case sel =>
    have key : ∀ (X' : Fields) (sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)),
        X' = B.fields → HEq sel' I.sel → IsSel X' sel' := by
      rintro X' sel' rfl h
      obtain rfl := eq_of_heq h
      exact hI.sel_ok
    exact key _ _ hX_eq hsel
  case bad =>
    have key : ∀ (X' : Fields) (Pr' : Primes X'), X' = B.fields → HEq Pr' (B.primes X) → ∀ v, Pr'.T v ∈ I.S := by
      rintro X' Pr' rfl h
      obtain rfl := eq_of_heq h
      exact hI.T_mem
    rw [hS]
    refine ⟨fun i => ?_, key _ _ hX_eq hPr, fun _ hl => hI.small_mem hl, hI.two_q_d_mem.2.1⟩
    rw [t.g_rec]
    exact hI.g_mem i
  case chOk =>
    have key : ∀ (X' : Fields) (Pr' : Primes X') (Ch' : Chars X' Pr' (I.rec7 l Z).R.m), X' = B.fields → HEq Pr' (B.primes X) →
        HEq Ch' I.Ch → Ch'.Ok := by
      rintro X' Pr' Ch' rfl h1 h2
      obtain rfl := eq_of_heq h1
      obtain rfl := eq_of_heq h2
      exact hI.ch_ok
    exact key _ _ _ hX_eq hPr hCh
  case chars =>
    have key : ∀ (X' : Fields) (Pr' : Primes X') (Ch' : Chars X' Pr' (I.rec7 l Z).R.m) (glob' : ChGlob X' (I.rec7 l Z).R.m)
        (seam' : Seam (I.rec7 l Z) X'), X' = B.fields → HEq Pr' (B.primes X) →
        HEq Ch' I.Ch → HEq glob' I.glob → HEq seam' (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) →
        ∃ eta, Ch'.Tied glob'.σ₀ (fun j τ => ((I.rec7 l Z).hc (seam'.iT τ)).e j) glob'.mu0 eta := by
      rintro X' Pr' Ch' glob' seam' rfl h1 h2 h3 h4
      obtain rfl := eq_of_heq h1
      obtain rfl := eq_of_heq h2
      obtain rfl := eq_of_heq h3
      obtain rfl := eq_of_heq h4
      exact ⟨I.C.eta, hI.ch_tied⟩
    exact key _ _ _ _ _ hX_eq hPr hCh hglob hseam
  case sharp => exact fun μ => (kCst _ _ _ _ _ _ hX_eq hPr hsel hS htup hcst μ).1
  case deep => exact fun μ => (kCst _ _ _ _ _ _ hX_eq hPr hsel hS htup hcst μ).2
  case repOne =>
    have key : ∀ (X' : Fields) (Pr' : Primes X') (sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)) (S' : Set ℕ)
        (tup' : (I.rec7 l Z).what₂.Tup → Tup X'.F X'.E X'.K S')
        (idx' : ∀ μ, ChIdx X' Pr' (I.rec7 l Z).R (QE sel' (tup' μ : Chr X'.F X'.E X'.K))),
        X' = B.fields → HEq Pr' (B.primes X) → HEq sel' I.sel → S' = I.S → HEq tup' I.tup → HEq idx' I.idx →
        ∀ μ j, j ≤ B.R.m - 2 + 1 → ∀ (b : (idx' μ).β j) (P : rowSG Pr' sel' (tup' μ)), P.1 ∈ Pr'.vGs → (idx' μ).h j b P = 1 := by
      rintro X' Pr' sel' S' tup' idx' rfl h1 h2 rfl h3 h4
      obtain rfl := eq_of_heq h1
      obtain rfl := eq_of_heq h2
      obtain rfl := eq_of_heq h3
      obtain rfl := eq_of_heq h4
      intro μ
      exact (hN μ).2.2
    rw [hm2]
    exact key _ _ _ _ _ _ hX_eq hPr hsel hS htup hidx

theorem colSide_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → I.StdKer l Z t → GlobalTheory.KerJ.ColSide t := by
  intro B X I hI _ l Z L hT Gi Gl K Y cX ex t hN hS
  exact colSide_of_choices I hI l Z t hN hS.X_eq hS.seam hS.Pr hS.Ch hS.sel hS.S hS.tup hS.cst hS.idx hS.m2 hS.glob

end GlobalTheory.Pdv
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.heckeChar_ramified_of_ramified_localComponent : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (ξ : (w.adicCompletion E)ˣ →* ℂˣ), IsComp χ w ξ → ¬ GlobalTheory.SplitWeil.IsUnram ξ → ¬ χ.UnrAt w := by
  first | exact @GlobalTheory.VTypeTame.ramified_of_isComp | exact GlobalTheory.VTypeTame.ramified_of_isComp | (intros; apply GlobalTheory.VTypeTame.ramified_of_isComp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isotypic_row_local_split_exists : ∀ (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (j : ℕ) (_ : RowMod D rep j) (σ : D.what₂.FT), D.what₂.isot j σ ≠ ⊥ → ∀ s : SplitPlace D.host.E, ∃ τ, IsLocS (rep σ).S s τ := by
  first | exact @GlobalTheory.RowLocal.finTyp_exists_isLocS | exact GlobalTheory.RowLocal.finTyp_exists_isLocS | (intros; apply GlobalTheory.RowLocal.finTyp_exists_isLocS <;> assumption)
end
