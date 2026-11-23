module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import GroundTheory.PAdicHodge.ACrisLog
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle145
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle319
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle230
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle243
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle190
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle200
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
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.TensOne

open TensorProduct

section Generic

variable {R S W C : Type} [CommRing R] [CommRing S] [CommRing W] [CommRing C]
  [Algebra R S] [Algebra R W] [Algebra R C]

theorem tmul_mul_natCast_mem (p : ℕ) (e : S) (x : W) :
    (e * (p : S)) ⊗ₜ[R] x ∈ Ideal.span {(p : S ⊗[R] W)} := by
  have hp : (p : S ⊗[R] W) = (p : S) ⊗ₜ[R] (1 : W) :=
    (map_natCast (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] W) p).symm
  have : (e * (p : S)) ⊗ₜ[R] x = (p : S ⊗[R] W) * (e ⊗ₜ[R] x) := by
    rw [hp, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem tmul_natCast_mul_mem (p : ℕ) (e : S) (x : W) :
    e ⊗ₜ[R] (x * (p : W)) ∈ Ideal.span {(p : S ⊗[R] W)} := by
  have hp : (p : S ⊗[R] W) = (1 : S) ⊗ₜ[R] (p : W) :=
    (map_natCast (Algebra.TensorProduct.includeRight : W →ₐ[R] S ⊗[R] W).toRingHom p).symm
  have : e ⊗ₜ[R] (x * (p : W)) = (p : S ⊗[R] W) * (e ⊗ₜ[R] x) := by
    rw [hp, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm x]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def gsum (d : ℕ → S) (w : ℕ →₀ W) : S ⊗[R] W := w.sum fun k x => d k ⊗ₜ[R] x

theorem gsum_add (d : ℕ → S) (w w' : ℕ →₀ W) :
    (gsum d (w + w') : S ⊗[R] W) = gsum d w + gsum d w' :=
  Finsupp.sum_add_index' (fun _ => TensorProduct.tmul_zero _ _) fun _ _ _ => TensorProduct.tmul_add _ _ _

theorem exists_gsum (p : ℕ) (d : ℕ → S)
    (hsurj : ∀ a : S, ∃ (s : Finset ℕ) (c : ℕ → R), a - ∑ k ∈ s, algebraMap R S (c k) * d k ∈ Ideal.span {(p : S)})
    (z : S ⊗[R] W) : ∃ w : ℕ →₀ W, z - gsum d w ∈ Ideal.span {(p : S ⊗[R] W)} := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    obtain ⟨s, c, hc⟩ := hsurj a
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hc
    refine ⟨∑ k ∈ s, Finsupp.single k (c k • x), ?_⟩
    have h1 : (gsum d (∑ k ∈ s, Finsupp.single k (c k • x)) : S ⊗[R] W) =
        (∑ k ∈ s, algebraMap R S (c k) * d k) ⊗ₜ[R] x := by
      rw [gsum, ← Finsupp.sum_finsetSum_index (fun _ => TensorProduct.tmul_zero _ _)
        (fun _ _ _ => TensorProduct.tmul_add _ _ _), TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finsupp.sum_single_index (h := fun k x => d k ⊗ₜ[R] x) (TensorProduct.tmul_zero _ _), ← Algebra.smul_def,
        TensorProduct.smul_tmul]
    rw [h1, ← TensorProduct.sub_tmul, ← he]
    exact tmul_mul_natCast_mem p e x
  | add x y hx hy =>
    obtain ⟨w, hw⟩ := hx
    obtain ⟨w', hw'⟩ := hy
    refine ⟨w + w', ?_⟩
    have : x + y - gsum d (w + w') = (x - gsum d w) + (y - gsum d w') := by
      rw [gsum_add]; ring
    rw [this]
    exact add_mem hw hw'

theorem generic (p : ℕ) (d : ℕ → S) (r0 : R) (f : S →ₐ[R] C) (g : W →ₐ[R] C)
    (hsurj : ∀ a : S, ∃ (s : Finset ℕ) (c : ℕ → R), a - ∑ k ∈ s, algebraMap R S (c k) * d k ∈ Ideal.span {(p : S)})
    (hv : ∀ k, algebraMap R S r0 * d k ∈ Ideal.span {(p : S)})
    (hK : ∀ (s : Finset ℕ) (w : ℕ → W), ∑ k ∈ s, f (d k) * g (w k) = 0 →
      ∀ k ∈ s, w k ∈ Ideal.span {algebraMap R W r0, (p : W)})
    (hC : (p : C) = 0) (z : S ⊗[R] W)
    (hz : Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) z = 0) :
    z ∈ Ideal.span {(p : S ⊗[R] W)} := by
  obtain ⟨w, hw⟩ := exists_gsum p d hsurj z
  have hL : Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) (z - gsum d w) = 0 := by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hw
    rw [← hy, map_mul, map_natCast, hC, mul_zero]

  rw [map_sub, hz, zero_sub, neg_eq_zero, gsum, Finsupp.sum, map_sum] at hL
  have hsum : ∑ k ∈ w.support, f (d k) * g (w k) = 0 := by
    rw [← hL]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.TensorProduct.lift_tmul]
  have hk := hK _ _ hsum
  have hG : (gsum d w : S ⊗[R] W) ∈ Ideal.span {(p : S ⊗[R] W)} := by
    refine Ideal.sum_mem _ fun k hks => ?_
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (hk k hks)
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (hv k)
    have h1 : d k ⊗ₜ[R] (u * algebraMap R W r0) = (e * (p : S)) ⊗ₜ[R] u := by
      rw [he, mul_comm u, ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
    change d k ⊗ₜ[R] (w k) ∈ _
    rw [← huv, TensorProduct.tmul_add, h1]
    exact add_mem (tmul_mul_natCast_mem p e u) (tmul_natCast_mul_mem p (d k) v)
  have := add_mem hw hG
  rwa [sub_add_cancel] at this

end Generic

section Specific

variable {l : ℕ} [Fact l.Prime]

def base : PAlg l where
  A := Ob l
  s := RingHom.id _
  perf := inferInstance
  compl := GlobalTheory.CompanionTheory.TiltCompl.complete_tf.1
  tf := GlobalTheory.CompanionTheory.TiltCompl.complete_tf.2

theorem isBase_base : IsBase l (base (l := l)) := Function.bijective_id

def d (k : ℕ) : Acris l := AdicCompletion.of _ _ (ACris.dpowZero (xi0_mem (l := l)) k)

theorem cris_d (A : PAlg l) (n k : ℕ) : A.cris n (d k) = A.dxi n k := by
  rw [d, cris_of]
  refine congrArg (A.mkAcr n) (Subtype.ext ?_)
  exact awayW_dpw A.s k (ACris.isUnit_natCast (K := ℂ_[l]) (p := l) k.factorial_ne_zero) (xi0 l)

theorem sW_base (x : Ainf l) : (base (l := l)).sW x = x := wmap_id x

theorem cris_teich (a : Ob l) :
    (base (l := l)).cris 1 (algebraMap (Ainf l) (Acris l) (WittVector.teichmuller l a)) =
      (base (l := l)).aTo1 a := by
  have h1 := (base (l := l)).aTo1_coeff (WittVector.teichmuller l a)
  rw [WittVector.teichmuller_coeff_zero] at h1
  have h2 := (base (l := l)).cris_algebraMap 1 (WittVector.teichmuller l a)
  rw [sW_base] at h2
  rw [h1]
  exact h2

theorem mem_of_cris (a : Acris l) (h : (base (l := l)).cris 1 a = 0) : a ∈ Ideal.span {(l : Acris l)} := by
  have := (RingHom.mem_ker).2 h
  rwa [((GlobalTheory.T.period_ring_comparison_of_base base isBase_base).2 1).2, pow_one] at this

theorem hsurj (a : Acris l) : ∃ (s : Finset ℕ) (c : ℕ → Ainf l),
    a - ∑ k ∈ s, algebraMap (Ainf l) (Acris l) (c k) * d (l * k) ∈ Ideal.span {(l : Acris l)} := by
  obtain ⟨c, hc⟩ := (GlobalTheory.T.expansion_surjective_additive_linear (base (l := l))).1 ((base (l := l)).cris 1 a)
  refine ⟨c.support, fun k => WittVector.teichmuller l (c k), mem_of_cris _ ?_⟩
  have e : (base (l := l)).expand c =
      ∑ k ∈ c.support, (base (l := l)).aTo1 (c k) * (base (l := l)).dxi 1 (l * k) := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, ← hc, e, sub_eq_zero, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, cris_teich, cris_d]

def r0 : Ainf l := WittVector.teichmuller l (pFlat l ^ l)

theorem hv (k : ℕ) : algebraMap (Ainf l) (Acris l) (r0 (l := l)) * d k ∈ Ideal.span {(l : Acris l)} := by
  refine mem_of_cris _ ?_
  rw [map_mul, r0, cris_teich, cris_d]
  exact (GlobalTheory.T.expansion_surjective_additive_linear (base (l := l))).2.2.2 k

theorem hK (A : PAlg l) (s : Finset ℕ) (w : ℕ → A.W)
    (h : ∑ k ∈ s, A.cris 1 (d (l * k)) * A.toAcr 1 (w k) = 0) (k : ℕ) (hks : k ∈ s) :
    w k ∈ Ideal.span {algebraMap (Ainf l) A.W r0, (l : A.W)} := by
  have hexp : A.expand (Finsupp.indicator s fun k _ => (w k).coeff 0) = 0 := by
    rw [expand, Finsupp.sum_of_support_subset _ (Finsupp.support_indicator_subset _ _) _ (by simp), ← h]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finsupp.indicator_of_mem hk, aTo1_coeff, cris_d, mul_comm]
  have hk := (GlobalTheory.T.expansion_eq_zero_iff_coeffs_mem A _).1 hexp k
  rw [Finsupp.indicator_of_mem hks] at hk
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hk
  have hr : algebraMap (Ainf l) A.W r0 = WittVector.teichmuller l (A.pi ^ l) := by
    change A.sW _ = _
    rw [r0, sW, WittVector.map_teichmuller, map_pow]
    rfl
  have hz : (w k - WittVector.teichmuller l b * algebraMap (Ainf l) A.W r0).coeff 0 = 0 := by
    rw [← WittVector.constantCoeff_apply, map_sub, map_mul, hr]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [hb, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff _).2 hz)
  exact Ideal.mem_span_pair.2 ⟨WittVector.teichmuller l b, t, by rw [ht]; ring⟩

theorem natCast_acr (A : PAlg l) : (l : A.Acr 1) = 0 := by
  have := A.pow_l_acr 1
  rwa [pow_one] at this

theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (z : TensorProduct (Ainf l) (Acris l) A.W),
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr 1))
      (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr 1)) (fun _ _ => Commute.all _ _) z = 0 →
    z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W)} := by
  intro l _ A z hz
  exact generic (R := Ainf l) (S := Acris l) (W := A.W) (C := A.Acr 1) l (fun k => d (l * k)) r0
    (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr 1)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr 1))
    hsurj (fun k => hv _) (fun s w h k hk => hK A s w h k hk) (natCast_acr A) z hz

end Specific

end GlobalTheory.CompanionTheory.TensOne
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZarCap

attribute [local instance] MvPolynomial.gradedAlgebra

theorem inU_inf {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (V W : X.Opens) (T : Thick (nlFun γ p X q κ)) :
    InU (V ⊓ W) T ↔ InU V T ∧ InU W T := by
  unfold InU
  rw [← le_inf_iff]
  exact Iff.rfl

theorem irrelevant_le_span (K : Type) [Field K] (N : ℕ) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K)) := by
  intro x hx
  rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hx
  have h0 : AddMonoidAlgebra.coeff x 0 = 0 := by
    erw [MvPolynomial.decomposition.decompose'_apply, MvPolynomial.homogeneousComponent_zero] at hx
    exact MvPolynomial.C_eq_zero.1 hx
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra hne
  have hm0 : m = 0 := Finsupp.ext fun i => by
    by_contra hi
    exact hne ⟨i, Set.mem_univ i, hi⟩
  subst hm0
  exact (MvPolynomial.mem_support_iff.1 hm) h0

theorem iSup_wch {K : Type} [Field K] {X : Scheme.{0}} (N : ℕ) (i : X ⟶ PSpace K N) : (⨆ j, wch i j) = ⊤ := by
  have h := AlgebraicGeometry.Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
    (fun j => MvPolynomial.X j) (irrelevant_le_span K N)
  simp only [wch]
  rw [← Scheme.Hom.preimage_iSup, h, Scheme.Hom.preimage_top]

theorem resU_eq {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) :
    resU (sq (thFil L r) (thFil L r')) h = (incl h).sq (incl_fil h r) (incl_fil h r') := by
  unfold resU CrystallineSemistableComparison.Pb.SMor.sq
  congr 1
  funext T
  refine LinearMap.ext fun x => Subtype.ext ?_
  obtain ⟨z, hz⟩ := x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

private theorem isHecke_div_and_resEtaPow_div {X : Scheme.{0}} {m N : ℕ} (u : Fin m → X.Opens) (w : Fin (N + 1) → X.Opens)
    (hw : (⨆ j, w j) = ⊤) (S : Finset (Fin m)) :
    (⨅ k ∈ S, u k) ≤ ⨆ c : Fin m → Fin (N + 1), ⨅ k ∈ S, (u k ⊓ w (c k)) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · exact le_iSup_of_le (fun _ => 0) (by simp)
  · intro a S ha ih
    rw [Finset.iInf_insert]
    calc u a ⊓ ⨅ k ∈ S, u k ≤ (⨆ j, u a ⊓ w j) ⊓ ⨆ c : Fin m → Fin (N + 1), ⨅ k ∈ S, (u k ⊓ w (c k)) :=
          inf_le_inf (by rw [← inf_iSup_eq, hw, inf_top_eq]) ih
      _ = ⨆ j, ⨆ c : Fin m → Fin (N + 1), (u a ⊓ w j) ⊓ ⨅ k ∈ S, (u k ⊓ w (c k)) := by
          rw [iSup_inf_eq]
          simp_rw [inf_iSup_eq]
      _ ≤ ⨆ c : Fin m → Fin (N + 1), ⨅ k ∈ insert a S, (u k ⊓ w (c k)) := by
          refine iSup_le fun j => iSup_le fun c => le_iSup_of_le (Function.update c a j) ?_
          rw [Finset.iInf_insert]
          refine inf_le_inf (by simp) (le_iInf₂ fun k hk => (iInf₂_le k hk).trans ?_)
          have hka : k ≠ a := fun h => ha (h ▸ hk)
          simp [hka]

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty)
    (r r' : ℤ) (j : ℕ),
    ∃ h : capS (wK q i y s) S ≤ KS q s {⨅ k ∈ S, uy i y k},
      Function.Bijective ((resU (sq (thFil (smFun X q) r) (thFil (smFun X q) r')) h).pull j) := by
  intro K _ X q N m i y s S hS r r' j
  classical
  have e : capS (wK q i y s) S = KS q s (Set.range fun c : Fin m → Fin (N + 1) => ⨅ k ∈ S, (uy i y k ⊓ wch i (c k))) := by
    funext T
    apply propext
    constructor
    · intro hT
      obtain ⟨k0, hk0⟩ := hS
      refine ⟨(hT k0 hk0).1, ?_⟩
      have hc : ∀ k, ∃ c : Fin (N + 1), k ∈ S → InU (uy i y k ⊓ wch i c) T := by
        intro k
        by_cases hk : k ∈ S
        · obtain ⟨_, V, ⟨c, rfl⟩, hV⟩ := hT k hk
          exact ⟨c, fun _ => hV⟩
        · exact ⟨0, fun h => absurd h hk⟩
      choose c hc using hc
      exact ⟨_, ⟨c, rfl⟩, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun k => uy i y k ⊓ wch i (c k)) S _).2 hc⟩
    · rintro ⟨hT, V, ⟨c, rfl⟩, hV⟩ k hk
      exact ⟨hT, _, ⟨c k, rfl⟩, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun k => uy i y k ⊓ wch i (c k)) S _).1 hV k hk⟩
  rw [e]
  have hle : KS q s (Set.range fun c : Fin m → Fin (N + 1) => ⨅ k ∈ S, (uy i y k ⊓ wch i (c k))) ≤
      KS q s {⨅ k ∈ S, uy i y k} := by
    rintro T ⟨hT, V, ⟨c, rfl⟩, hV⟩
    refine ⟨hT, _, Set.mem_singleton _, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (uy i y) S _).2 fun k hk => ?_⟩
    exact ((inU_inf _ _ _).1 ((GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun k => uy i y k ⊓ wch i (c k)) S _).1 hV k hk)).1
  have hc : ∀ W ∈ ({⨅ k ∈ S, uy i y k} : Set X.Opens),
      W ≤ sSup (Set.range fun c : Fin m → Fin (N + 1) => ⨅ k ∈ S, (uy i y k ⊓ wch i (c k))) := by
    intro W hW
    rw [Set.mem_singleton_iff] at hW
    subst hW
    rw [sSup_range]
    exact isHecke_div_and_resEtaPow_div (uy i y) (wch i) (iSup_wch N i) S
  refine ⟨hle, ?_⟩
  rw [resU_eq]
  exact (GlobalTheory.CompanionTheory.NlZar.zariski_descent (CrystallineSemistableComparison.Pb.TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) _ _ hle hc j).1 r r'

end GlobalTheory.CompanionTheory.ConeZarCap
end

section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

namespace GlobalTheory.CompanionTheory.MoyPrasad

theorem factor_Gx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ Gx k e,
    ∃ m ∈ (Gx k e).comap (leviEmb k e), ∃ x ∈ unipRad k e, ∃ c ∈ lowC k e, g = leviEmb k e m * x * c := by
  intro k _ _ _ _ n s d e g hg
  obtain ⟨u, hu, h, hh, rfl⟩ := GlobalTheory.T.parahoric_unipotent_times_kernel k n s d e g hg
  obtain ⟨m, hLm, x, hx, c, hc, hdec⟩ := GlobalTheory.T.iwahori_levi_unipotent_factor k n s d e h hh
  have hm : GlobalTheory.SmGL.leviEmb k e m ∈ PositivityTheory.LowerBoundConstant.Gx k e := by
    unfold PositivityTheory.LowerBoundConstant.Gx
    exact Subgroup.mem_sup_left hLm
  have hconj : (GlobalTheory.SmGL.leviEmb k e m)⁻¹ * u * GlobalTheory.SmGL.leviEmb k e m
      ∈ GlobalTheory.SmGL.unipRad k e := by
    have hn := GlobalTheory.SmGL.leviEmb_mem_normalizer k e m⁻¹
    rw [map_inv] at hn
    have h' := (Subgroup.mem_normalizer_iff.mp hn u).mp hu.1
    rwa [inv_inv] at h'
  refine ⟨m, Subgroup.mem_comap.mpr hm,
    (GlobalTheory.SmGL.leviEmb k e m)⁻¹ * u * GlobalTheory.SmGL.leviEmb k e m * x,
    mul_mem hconj hx.1, c, hc, ?_⟩
  rw [hdec]; group

end GlobalTheory.CompanionTheory.MoyPrasad
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Coc

theorem continuous_levi_mir (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) : Continuous (levi k n) := by
  have hval : Continuous fun g : GL (Fin n) k => GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k) :=
    GlobalTheory.CompanionTheory.LeibPhi.continuous_glEmbMat_comp n Units.continuous_val
  have hinv : Continuous fun g : GL (Fin n) k =>
      GlobalTheory.BZMir.glEmbMat k n ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) :=
    GlobalTheory.CompanionTheory.LeibPhi.continuous_glEmbMat_comp n Units.continuous_coe_inv
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact hval
  · exact hinv

theorem hgp_cocompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ), ∃ C : Set (Mir k ((i + 1) + t)), IsCompact C ∧
      ∀ g : Mir k ((i + 1) + t), ∃ h ∈ MirabolicParabolic k (i + 1) t, ∃ c ∈ C, g = h * c := by
  intro k _ _ _ _ i t
  refine ⟨GlobalTheory.BZMir.levi k ((i + 1) + t) ''
      (GlobalTheory.SplitWeil.KO k (Fin ((i + 1) + t)) : Set (GL (Fin ((i + 1) + t)) k)),
    GlobalTheory.SplitFlip.isCompact_KO.image (GlobalTheory.CompanionTheory.BZPhiPG.Coc.continuous_levi_mir k _), ?_⟩
  intro g
  obtain ⟨p, w, hw, hx⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul
    (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : (i + 1) + t = (i + 1) + t)))
    (GlobalTheory.BZMir.mirabolicProjection k ((i + 1) + t) g)
  refine ⟨g * (GlobalTheory.BZMir.levi k _ w)⁻¹, ?_, GlobalTheory.BZMir.levi k _ w, ⟨w, hw, rfl⟩,
    (inv_mul_cancel_right g _).symm⟩
  have hmem : ∀ (g : Mir k ((i + 1) + t)),
      g ∈ MirabolicParabolic k (i + 1) t ↔
        mirabolicProjection k ((i + 1) + t) g ∈ parab k (two (stdSum (rfl : (i + 1) + t = (i + 1) + t))) := by
    intro g
    have hlast : ((g : GL (Fin ((i + 1) + t + 1)) k) : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k)
        (Fin.last ((i + 1) + t)) = GlobalTheory.BZMir.eLast k ((i + 1) + t) :=
      (GlobalTheory.BZMir.mem_Mir_iff k (g : GL (Fin ((i + 1) + t + 1)) k)).1 g.2
    have hproj : ∀ a b : Fin ((i + 1) + t),
        ((mirabolicProjection k ((i + 1) + t) g : GL (Fin ((i + 1) + t)) k) : Matrix _ _ k) a b =
          ((g : GL (Fin ((i + 1) + t + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) := fun _ _ => rfl
    simp only [GlobalTheory.BZMir.Leib.MirabolicParabolic, GlobalTheory.BZMir.Leib.eGP, Subgroup.mem_comap,
      Subgroup.coe_subtype, GlobalTheory.SmGL.mem_parab_two, hproj]
    constructor
    · intro h b a
      convert h (Fin.castSucc b) a using 2 <;> apply Fin.ext <;>
        simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
    · intro h b a
      induction b using Fin.lastCases with
      | last =>
        have h0 : ((g : GL (Fin ((i + 1) + t + 1)) k) : Matrix _ _ k)
            (Fin.last ((i + 1) + t))
            (Fin.castSucc (GlobalTheory.SmGL.stdSum (rfl : (i + 1) + t = (i + 1) + t) (Sum.inl a))) = 0 := by
          rw [hlast]
          simp only [GlobalTheory.BZMir.eLast, Pi.single_apply]
          rw [if_neg (Fin.castSucc_lt_last _).ne]
        convert h0 using 2 <;> apply Fin.ext <;>
          simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
      | cast b =>
        convert h b a using 2 <;> apply Fin.ext <;>
          simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
  rw [hmem]
  have hlevi : mirabolicProjection k ((i + 1) + t) (levi k _ w) = w := by
    apply Units.ext
    ext a b
    show GlobalTheory.BZMir.glEmbMat k _ (w : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = _
    simp [GlobalTheory.BZMir.glEmbMat]
  have hproj : GlobalTheory.BZMir.mirabolicProjection k ((i + 1) + t) (g * (GlobalTheory.BZMir.levi k _ w)⁻¹) = p := by
    rw [map_mul, map_inv, hlevi, hx, mul_inv_cancel_right]
  rw [hproj]
  exact p.2

end GlobalTheory.CompanionTheory.BZPhiPG.Coc

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_unipotent_lift_parabolic_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (n : MirUin k (j + 1)),
    ∃ (u : MirUin k (m + (j + 1))) (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
      gpProj k m (j + 1) ⟨u, hh⟩ = (1, (n : Mir k (j + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.exists_mirUin_gpProj_lift | exact GlobalTheory.CompanionTheory.LeibPhi.exists_mirUin_gpProj_lift | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.exists_mirUin_gpProj_lift <;> assumption)
end
