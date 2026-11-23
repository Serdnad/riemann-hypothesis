module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle378
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle377
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle374
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle361
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle381
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle382
public import Formalism.SatakeDualWeyl.Bundle001
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeDefs
public import GroundTheory.GlobalFields.NormResidueSymbol.Bundle002
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHecke
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeLocal
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom

@[expose] public section

section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.CassPush

section SlopeTestRemainingChoices

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pi_mul (π : Representation ℂ G V) (a b : G) (v : V) : π a (π b v) = π (a * b) v := by
  rw [map_mul, Module.End.mul_apply]

theorem mem_fixed_iff (π : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ fixed π H ↔ ∀ h ∈ H, π h v = v := by
  constructor
  · intro hv h hh
    have h1 : ∀ h : H, π (h : G) v = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • v := hv
    simpa using h1 ⟨h, hh⟩
  · intro hv
    show ∀ h : H, π (h : G) v = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • v
    intro h
    simpa using hv h h.2

theorem mkQ_avg (W : Submodule ℂ V) (r : ℕ) (hr : 0 < r) (f : Fin r → V) (m : V ⧸ W)
    (h : ∀ i, W.mkQ (f i) = m) : W.mkQ (((r : ℂ)⁻¹) • ∑ i, f i) = m := by
  have hr' : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'

  rw [map_smul, map_sum, Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const, Finset.card_univ,
  Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hr', one_smul]

end SlopeTestRemainingChoices

section Avg

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_avg (K : Subgroup G) (hK : IsCompact (K : Set G)) (π : Representation ℂ G V)
    (hπ : IsSmooth π) (E : V →ₗ[ℂ] V)
    (hE : ∀ (u : V) (H : Subgroup G), H ≤ K → (∀ h ∈ H, π h u = u) → ∀ (r : ℕ) (x : Fin r → G),
      0 < r → (∀ i, x i ∈ K) → (∀ y ∈ K, ∃! i, (x i)⁻¹ * y ∈ H) →
      E u = ((r : ℂ)⁻¹) • ∑ i, π (x i) u)
    (u : V) (A : Subgroup G) (hA : A ≤ K) (hc : ∀ y ∈ K, ∃ a ∈ A, π (a⁻¹ * y) u = u) :
    ∃ (r : ℕ) (x : Fin r → G), 0 < r ∧ (∀ i, x i ∈ A) ∧
      E u = ((r : ℂ)⁻¹) • ∑ i, π (x i) u := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let H' : Subgroup K :=
    { carrier := {g | π (g : G) u = u}
      mul_mem' := by
        intro a b ha hb
        show π ((a * b : K) : G) u = u
        rw [Subgroup.coe_mul, ← pi_mul, show π (b : G) u = u from hb, show π (a : G) u = u from ha]
      one_mem' := by
        show π ((1 : K) : G) u = u
        simp
      inv_mem' := by
        intro a ha
        show π ((a⁻¹ : K) : G) u = u
        have ha' : π (a : G) u = u := ha
        conv_lhs => rw [← ha']
        rw [pi_mul]
        simp }
  have hH' : IsOpen (H' : Set K) := (hπ u).preimage continuous_subtype_val
  have hcomp : IsCompact (((⊤ : Subgroup K)) : Set K) := by
    simpa using (isCompact_univ : IsCompact (Set.univ : Set K))
  obtain ⟨r, hr, x, hxA, hx⟩ := GlobalTheory.T.compact_group_finite_coset_reps K ⊤ H' (A.subgroupOf K) hcomp hH' le_top le_top (by
    intro y _
    obtain ⟨a, ha, hau⟩ := hc y y.2
    refine ⟨⟨a, hA ha⟩, Subgroup.mem_subgroupOf.2 ha, ?_⟩
    show π (((⟨a, hA ha⟩ : K)⁻¹ * y : K) : G) u = u
    simpa using hau)
  refine ⟨r, fun i => (x i : G), hr, fun i => Subgroup.mem_subgroupOf.1 (hxA i),
    hE u (H'.map K.subtype) ?_ ?_ r _ hr (fun i => (x i).2) ?_⟩
  · rintro _ ⟨g, _, rfl⟩
    exact g.2
  · rintro _ ⟨g, hg, rfl⟩
    exact hg
  · intro y hy
    obtain ⟨i, hi, huniq⟩ := hx ⟨y, hy⟩ trivial
    refine ⟨i, ⟨(x i)⁻¹ * ⟨y, hy⟩, hi, by simp⟩, ?_⟩
    rintro i' ⟨g, hg, e⟩
    refine huniq i' ?_
    have : (x i')⁻¹ * ⟨y, hy⟩ = g := by
      apply Subtype.ext
      simpa using e.symm
    show (x i')⁻¹ * ⟨y, hy⟩ ∈ H'
    rw [this]
    exact hg

end Avg

section Dom

variable {G : Type} [Group G] [TopologicalSpace G]

theorem conj_pow_mem (D : CassData G) (t : D.T) (hd : D.IsDom t) (j : ℕ) :
    ∀ b ∈ D.J ⊓ D.T, ((t : G) ^ j)⁻¹ * b * (t : G) ^ j ∈ D.J ⊓ D.T := by
  induction j with
  | zero => intro b hb; simpa using hb
  | succ j ih =>
    intro b hb
    have h := (hd.2.2 _ (ih b hb)).2
    have e : ((t : G) ^ (j + 1))⁻¹ * b * (t : G) ^ (j + 1)
        = (t : G)⁻¹ * (((t : G) ^ j)⁻¹ * b * (t : G) ^ j) * (t : G) := by
      rw [pow_succ]; group
    rw [e]
    exact h

end Dom

theorem exists_fixed_proj_eq_piN_pow : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ t : D.T, D.IsStrDom t → ∀ w ∈ fixed (D.piN π) D.JT, ∃ j : ℕ, ∃ v : fixed π D.J, D.proj π (v : V) = D.piN π (t ^ j) w := by
  intro G _ _ _ D V _ _ π hπ t ht w hw
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨hd, -, hsh⟩ := ht
  obtain ⟨j, hj⟩ := hsh {g | π g u = u} (hπ u) (by simp)
  have hwT := (mem_fixed_iff _ _ _).1 hw
  have hKc : IsCompact ((D.J ⊓ D.T : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact D.isCompact_J.inter_right D.isClosed_alt
  have hN : ∀ n ∈ D.N, ∀ v : V,
      (twKer π D.N 1).mkQ (π n v) = (twKer π D.N 1).mkQ v := by
    intro n hn v
    refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨n, hn⟩, v, by simp⟩)

  obtain ⟨x, hxdef⟩ : ∃ x, x = π ((t : G) ^ j) u := ⟨_, rfl⟩
  have hxNm : ∀ n ∈ D.J ⊓ D.Nm, π n x = x := by
    intro n hn
    have h1 : π (((t : G) ^ j)⁻¹ * n * (t : G) ^ j) u = u := hj n hn
    rw [hxdef]
    conv_rhs => rw [← h1]
    rw [pi_mul, pi_mul]
    congr 2
    group

  obtain ⟨E1, hE1fix, -, -, -, hE1⟩ := GlobalTheory.T.compact_fixed_vector_projection G (D.J ⊓ D.T) hKc V π hπ
  obtain ⟨r, b, hr, hb, hy⟩ := exists_avg (D.J ⊓ D.T) hKc π hπ E1 hE1 x (D.J ⊓ D.T) le_rfl
    (fun y hy => ⟨y, hy, by simp⟩)
  obtain ⟨y, hydef⟩ : ∃ y, y = E1 x := ⟨_, rfl⟩
  rw [← hydef] at hy
  have hyK : ∀ k ∈ D.J ⊓ D.T, π k y = y := by
    rw [hydef]
    exact (mem_fixed_iff _ _ _).1 (hE1fix x)
  have hyNm : ∀ n ∈ D.J ⊓ D.Nm, π n y = y := by
    intro n hn

    rw [hy, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hbi := hb i
    have hn' : (b i)⁻¹ * n * b i ∈ D.J ⊓ D.Nm := by
      refine ⟨D.J.mul_mem (D.J.mul_mem (inv_mem hbi.1) hn.1) hbi.1, ?_⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 (D.norm_Nm _ (inv_mem hbi.2)) n).1 hn.2
      simpa using h2
    have h3 := hxNm _ hn'
    conv_rhs => rw [← h3]
    rw [pi_mul, pi_mul]
    congr 2
    group
  have hmk : (twKer π D.N 1).mkQ y = D.piN π (t ^ j) (Submodule.Quotient.mk u) := by
    rw [hy]
    refine mkQ_avg _ r hr _ _ fun i => ?_
    have hc := conj_pow_mem D t hd j (b i) (hb i)
    have hfix := hwT ⟨_, hc.2⟩ hc.1
    have h4 : π (b i) x = π ((t : G) ^ j) (π (((t : G) ^ j)⁻¹ * b i * (t : G) ^ j) u) := by
      rw [hxdef, pi_mul, pi_mul]
      congr 2
      group
    rw [h4]
    have h5 : (twKer π D.N 1).mkQ (π (((t : G) ^ j)⁻¹ * b i * (t : G) ^ j) u)
        = Submodule.Quotient.mk u := hfix
    have h6 : ∀ m : V, (twKer π D.N 1).mkQ (π ((t : G) ^ j) m)
        = D.piN π (t ^ j) ((twKer π D.N 1).mkQ m) := by
      intro m
      have : (((t ^ j : D.T)) : G) = (t : G) ^ j := by simp
      rw [← this]
      rfl
    rw [h6, h5]

  obtain ⟨E2, hE2fix, -, -, -, hE2⟩ := GlobalTheory.T.compact_fixed_vector_projection G D.J D.isCompact_J V π hπ
  obtain ⟨r2, c, hr2, hc, hv⟩ := exists_avg D.J D.isCompact_J π hπ E2 hE2 y (D.J ⊓ D.N) inf_le_left
    (fun g hg => by
      obtain ⟨c, hc, b', hb', a, ha, rfl⟩ := D.fact_up g hg
      refine ⟨c, hc, ?_⟩
      have e : c⁻¹ * (c * b' * a) = b' * a := by group
      rw [e, ← pi_mul, hyNm a ha, hyK b' hb'])
  refine ⟨j, ⟨E2 y, hE2fix y⟩, ?_⟩
  show (twKer π D.N 1).mkQ (E2 y) = _
  rw [hv]
  refine mkQ_avg _ r2 hr2 _ _ fun i => ?_
  rw [hN _ (hc i).2, hmk]

end GlobalTheory.CompanionTheory.CassPush
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc GlobalTheory.CompanionTheory.LbElem.ConjMonomial

namespace GlobalTheory.CompanionTheory.LbElem.MonomialInJ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem diag_ne_zero_of_offDiag {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) (i : Fin N) :
    (x : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
  intro h0
  have h1 := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i i) (mul_inv_cancel x)
  simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_eq] at h1
  rw [Finset.sum_eq_zero] at h1
  · exact zero_ne_one h1
  · intro l _
    by_cases hl : i = l
    · subst hl
      rw [h0, zero_mul]
    · rw [h i l hl, zero_mul]

private def o {N : ℕ} (a : Fin N) : Fin (ones N a) := ⟨0, by simp [ones]⟩

theorem nup_entries {N : ℕ} {c : GL (Fin N) k} (hc : c ∈ unipRad k (stdBlocks (ones N) (sum_ones N))) :
    (∀ i j : Fin N, j < i → (c : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      ∀ i : Fin N, (c : Matrix (Fin N) (Fin N) k) i i = 1 := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hc
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have := mem_parab_iff.1 h1 i j (o i) (o j) hij
    rwa [stdBlocks_ones, stdBlocks_ones] at this
  · have := h2 i (o i) (o i)
    rwa [stdBlocks_ones, Matrix.one_apply_eq] at this

theorem nlo_entries {N : ℕ} {a : GL (Fin N) k}
    (ha : a ∈ unipRadLower k (stdBlocks (ones N) (sum_ones N))) :
    (∀ i j : Fin N, i < j → (a : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      ∀ i : Fin N, (a : Matrix (Fin N) (Fin N) k) i i = 1 := by
  obtain ⟨h1, h2⟩ := (mem_unipRadLower k).1 ha
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have := (mem_parabLower_iff k).1 h1 i j (o i) (o j) hij
    rwa [stdBlocks_ones, stdBlocks_ones] at this
  · have := h2 i (o i) (o i)
    rwa [stdBlocks_ones, Matrix.one_apply_eq] at this

end GlobalTheory.CompanionTheory.LbElem.MonomialInJ

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.JacSmooth

theorem jac_fixed_of_smooth : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (hd : ∑ _a : Fin n, 1 = n) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    ∀ w : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)), ∃ m, 1 ≤ m ∧
      ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n m) (fun _ : Fin n => 1) hd,
        _root_.GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd) π u w = w := by
  intro k _ _ _ _ n hd V _ _ π hπ w
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨m, hm, hK⟩ := GlobalTheory.T.congruence_subgroup_basis_nhds k n {g | π g v = v} (hπ v) (by simp)
  refine ⟨m, hm, fun u hu => ?_⟩
  have hδ : deltaHalf k (PositivityTheory.Lbc.Bl (fun _ : Fin n => 1)) u = 1 :=
    GlobalTheory.T.modulus_trivial_on_levi_compact k n n (fun _ : Fin n => 1) hd (Zls.Km k n m) (GlobalTheory.CompanionTheory.HeckeKm.isCompact_Km n m) u hu
  have hv : π (leviEmb k (stdBlocks (fun _ : Fin n => 1) hd) u) v = v := hK hu
  rw [_root_.GlobalTheory.SmGL.jac_mk, hv, hδ]
  simp

end GlobalTheory.CompanionTheory.JacSmooth

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

theorem _root_.GlobalTheory.T.jacquet_hecke_condition_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.CH k := by
  first | exact @GlobalTheory.CompanionTheory.HeckeExist.exists_heckeOp | exact GlobalTheory.CompanionTheory.HeckeExist.exists_heckeOp | (intros; apply GlobalTheory.CompanionTheory.HeckeExist.exists_heckeOp <;> assumption)
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

section U

variable {L : Type} [Field L] {σ : L →+* L} {n : ℕ}

def IsPermW (w : GU σ n) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ a c : Fin n, ((w : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a c = if c = π a then 1 else 0

variable [Valued L (WithZero (Multiplicative ℤ))]

def permWt (t : GU σ n) (π : Equiv.Perm (Fin n)) : ℤ :=
  ∑ a : Fin n, ((a.val : ℤ) + 1) * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (π a) (π a))

end U

def aOp {G : Type} [Group G] (R : Finset G) (t : G) (φ : G → ℂ) : G → ℂ :=
  fun g => ∑ r ∈ R, φ (g * r * t)

end GlobalTheory.CompanionTheory.SatPow

end
end

section

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField Ad3 Ad3.R
open GroundTheory.Global.RationalSymbol (prime unitAt)
open GroundTheory.Automorphic.GodementSection (adeleAt)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.RankinSelbergQ

open DirichletHecke
open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract RationalSymbol

theorem mem_adicCompletionIntegers_of_ord_nonneg (v : Pl) {x : Qv v} (hx : x ≠ 0) (h : 0 ≤ ord x) :
    x ∈ v.adicCompletionIntegers ℚ := by
  have h1 : normalizedValuation (Qv v) x ≤ normalizedValuation (Qv v) 1 := by
    rw [map_one, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have h2 := normalizedValuation_le_iff.1 h1
  rw [map_one] at h2
  exact (mem_valuationInteger_iff v x).1 h2

theorem norm_padicRingEquiv_of_ord_eq_zero (v : Pl) (a : (Qv v)ˣ) (h : ord (a : Qv v) = 0) :
    ‖padicRingEquiv v (a : Qv v)‖ = 1 := by
  refine norm_padicRingEquiv_eq_one ((Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩)
  · exact mem_adicCompletionIntegers_of_ord_nonneg v a.ne_zero h.ge
  · refine mem_adicCompletionIntegers_of_ord_nonneg v (a⁻¹).ne_zero ?_
    rw [ord_units_inv, h]
    simp

theorem ofFinite_mem_positiveSubgroup (e : Afˣ) (h : ∀ v, ord (lf v e : Qv v) = 0) :
    IdeleGroup.ofFinite e ∈ RationalIdeles.positiveSubgroup := by
  refine mem_positiveSubgroup_of (fun w => norm_padicRingEquiv_of_ord_eq_zero w (lf w e) (h w)) ?_
  change 0 < ((RationalIdeles.realUnitsEquiv.toMulEquiv.toMonoidHom
    (IdeleGroup.toInfinite ℚ (IdeleGroup.ofFinite e)) : ℝˣ) : ℝ)
  rw [IdeleGroup.toInfinite_ofFinite, map_one, Units.val_one]
  exact one_pos

theorem toZModPow_eq_of_congr {N : ℕ} [NeZero N] (w : Pl) (x : Qv w) (u : ℤ_[prime w]) (n : ℤ)
    (hu : (u : ℚ_[prime w]) = padicRingEquiv w x)
    (hx : ((N : Qv w))⁻¹ * (x - n) ∈ 𝒪[Qv w]) :
    PadicInt.toZModPow (N.factorization (prime w)) u =
      ZMod.castHom (Nat.ordProj_dvd N (prime w)) _ (n : ZMod N) := by
  have hO := (mem_valuationInteger_iff w _).1 hx
  have hn : ‖padicRingEquiv w (((N : Qv w))⁻¹ * (x - n))‖ ≤ 1 :=
    (PadicInt.mem_subring_iff _).1 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn w).mapsTo hO)
  let z : ℤ_[prime w] := ⟨_, hn⟩
  have hN : ((N : ℕ) : ℚ_[prime w]) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hz : u = (n : ℤ_[prime w]) + (N : ℤ_[prime w]) * z := by
    apply PadicInt.ext
    have hzc : ((z : ℤ_[prime w]) : ℚ_[prime w]) = ((N : ℚ_[prime w]))⁻¹ * (padicRingEquiv w x - n) := by
      change padicRingEquiv w (((N : Qv w))⁻¹ * (x - n)) = _
      simp only [map_mul, map_inv₀, map_sub, map_natCast, map_intCast]
    rw [PadicInt.coe_add, PadicInt.coe_mul, hzc, hu]
    push_cast
    field_simp
    ring
  have h0 : ((N : ℕ) : ZMod (prime w ^ N.factorization (prime w))) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (Nat.ordProj_dvd N (prime w))
  rw [hz, map_add (f := _), map_mul, map_natCast, map_intCast, map_intCast, h0, zero_mul, add_zero]

theorem heckeCharacter_ofFinite_mul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (d : Afˣ) (n : ℤ)
    (h0 : ∀ v, ord (lf v d : Qv v) = 0)
    (h1 : ∀ v, pOf v ∣ N → ((N : Qv v))⁻¹ * ((lf v d : Qv v) - n) ∈ 𝒪[Qv v]) :
    ((heckeCharacter χ).toIdele (IdeleGroup.ofFinite d) : ℂ) * χ (n : ZMod N) = 1 := by
  have hinv : ∀ v, ord (lf v d⁻¹ : Qv v) = 0 := fun v => by
    have : lf v d⁻¹ = (lf v d)⁻¹ := map_inv (Units.map (adeleAt v).toMonoidHom) d
    rw [this, ord_units_inv, h0 v]
    simp
  let y : RationalIdeles.positiveSubgroup :=
    ⟨IdeleGroup.ofFinite d⁻¹, ofFinite_mem_positiveSubgroup d⁻¹ hinv⟩
  have key : (heckeCharacter χ (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)) : ℂ) = χ (n : ZMod N) := by
    refine coe_heckeCharacter_mk_of_forall χ y fun w hw => ?_
    refine toZModPow_eq_of_congr w (lf w d : Qv w) _ n ?_ (h1 w ?_)
    · have hc := coe_unitAt y w
      have hy : (IdeleGroup.finiteProj w (y : IdeleGroup ℚ) : Qv w) = ((lf w d : Qv w))⁻¹ := by
        have : lf w d⁻¹ = (lf w d)⁻¹ := map_inv (Units.map (adeleAt w).toMonoidHom) d
        change ((lf w d⁻¹ : (Qv w)ˣ) : Qv w) = _
        rw [this, Units.val_inv_eq_inv_val]
      have hm : ((((unitAt y w)⁻¹ : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) *
          ((unitAt y w : ℤ_[prime w]) : ℚ_[prime w]) = 1 := by
        rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]
      rw [hc, hy, map_inv₀] at hm
      have hne : padicRingEquiv w (lf w d : Qv w) ≠ 0 := (map_ne_zero _).2 (lf w d).ne_zero
      field_simp at hm
      exact hm
    · rw [show pOf w = prime w from absNorm_asIdeal w]
      exact hw
  rw [← key, HeckeCharacter.toIdele_apply, ← Circle.coe_mul, ← map_mul, ← map_mul, ← map_mul]
  simp [y]

theorem f0 : Ad3.R.B0 → Ad3.R.F0 := fun _ _ _ χ =>
  ⟨heckeCharacter χ, ⟨isOfFinOrder_heckeCharacter χ, fun d n h0 h1 =>
    heckeCharacter_ofFinite_mul χ d n h0 h1⟩⟩

end GlobalTheory.CompanionTheory.RankinSelbergQ
end
end
