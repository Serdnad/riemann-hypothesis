module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle586
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle481
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle576
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle483
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormOneUnitHilbertNinety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

namespace GlobalTheory.CompanionTheory.EllCRT

private theorem monic_of_mem_normalizedFactors' {K : Type} [Field K] {P q : K[X]}
    (hq : q ∈ UniqueFactorizationMonoid.normalizedFactors P) : q.Monic := by
  have hq0 : q ≠ 0 := (UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq).ne_zero
  rw [← UniqueFactorizationMonoid.normalize_normalized_factor q hq]
  exact Polynomial.monic_normalize hq0

private theorem span_sup_span_eq_unit_ideal_of_ne_normalizedFactors {K : Type} [Field K] {P p q : K[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors P)
    (hq : q ∈ UniqueFactorizationMonoid.normalizedFactors P) (hpq : p ≠ q) :
    Ideal.span {p} ⊔ Ideal.span {q} = ⊤ := by
  have hpi : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
  have hqi : Irreducible q := UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
  have hcop : IsCoprime p q := by
    rw [Irreducible.coprime_iff_not_dvd hpi]
    intro hd
    exact hpq (Polynomial.eq_of_monic_of_associated (monic_of_mem_normalizedFactors' hp)
      (monic_of_mem_normalizedFactors' hq) (hpi.associated_of_dvd hqi hd))
  exact (Ideal.sup_eq_top_iff_isCoprime p q).mpr hcop

theorem exists_congr_monic_factors {K : Type} [Field K] {P : K[X]} (hP : P ≠ 0) (t : K[X] → K[X]) :
    ∃ m : K[X], ∀ f : K[X], f.Monic → Irreducible f → f ∣ P → f ∣ m - t f := by
  classical
  let S : Finset K[X] := (UniqueFactorizationMonoid.normalizedFactors P).toFinset
  have hcop : Pairwise (Function.onFun IsCoprime (fun i : S => Ideal.span {(i : K[X])})) := by
    intro i j hij
    show IsCoprime (Ideal.span {(i : K[X])}) (Ideal.span {(j : K[X])})
    exact Ideal.isCoprime_iff_sup_eq.mpr (span_sup_span_eq_unit_ideal_of_ne_normalizedFactors (Multiset.mem_toFinset.mp i.2)
      (Multiset.mem_toFinset.mp j.2) (fun h => hij (Subtype.ext h)))
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal hcop (fun i : S => t i)
  refine ⟨r, fun f hfm hfi hfP => ?_⟩
  obtain ⟨q, hq, hfq⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hP hfi hfP
  have hfeq : f = q := Polynomial.eq_of_monic_of_associated hfm (monic_of_mem_normalizedFactors' hq) hfq
  subst hfeq
  have h := hr ⟨f, Multiset.mem_toFinset.mpr hq⟩
  exact Ideal.mem_span_singleton.mp h

private theorem adjoinRoot_exists_mk_eq {R : Type} [CommRing R] {f : R[X]} (x : AdjoinRoot f) :
    ∃ p : R[X], AdjoinRoot.mk f p = x :=
  AdjoinRoot.mk_surjective x

private theorem adjoinRoot_mk_eq_of_selfRecip_val_eq {E : Type} [Field E] [NumberField E] [IsCMField E]
    (g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q) {r r' : ℕ} (Q : SelfRecip E r)
    (Q' : SelfRecip E r') (hQ : Q'.1 = Q.1) (l : E[X])
    (hl : (AdjoinRoot.mk Q'.1 l : Fld Q') = g r' Q') :
    (AdjoinRoot.mk Q.1 l : Fld Q) = g r Q := by
  have h1 : Q'.1.natDegree = r' := Q'.2.2.2.1
  have h2 : Q.1.natDegree = r := Q.2.2.2.1
  rw [hQ] at h1
  have hrr : r' = r := h1.symm.trans h2
  subst hrr
  obtain rfl : Q' = Q := Subtype.ext hQ
  exact hl

private theorem exists_polynomial_lift_adjoinRoot_selfRecip {E : Type} [Field E] [NumberField E] [IsCMField E]
    (g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q) :
    ∃ t : E[X] → E[X], ∀ (r : ℕ) (Q : SelfRecip E r),
      (AdjoinRoot.mk Q.1 (t Q.1) : Fld Q) = g r Q := by
  classical
  refine ⟨fun f => if h : ∃ Q' : SelfRecip E f.natDegree, Q'.1 = f then
      (adjoinRoot_exists_mk_eq (f := h.choose.1) (g f.natDegree h.choose)).choose else 0, ?_⟩
  intro r Q
  have hex : ∃ Q' : SelfRecip E Q.1.natDegree, Q'.1 = Q.1 :=
    ⟨⟨Q.1, by rw [Q.2.2.2.1]; exact Q.2⟩, rfl⟩
  dsimp only
  rw [dite_eq_left hex]
  exact adjoinRoot_mk_eq_of_selfRecip_val_eq g Q hex.choose hex.choose_spec _
    (adjoinRoot_exists_mk_eq (f := hex.choose.1) (g Q.1.natDegree hex.choose)).choose_spec

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E),
    γ₀.val.charpoly ∈ Ell E n → ∀ g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q, ∃ m : E[X],
      ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly →
        (AdjoinRoot.mk Q.1 m : Fld Q) = g r Q := by
  intro E _ _ _ n γ₀ _ g
  obtain ⟨t, ht⟩ := exists_polynomial_lift_adjoinRoot_selfRecip g
  obtain ⟨m, hm⟩ := exists_congr_monic_factors (Matrix.charpoly_monic γ₀.val).ne_zero t
  refine ⟨m, fun r Q hQ => ?_⟩
  rw [← ht r Q]
  exact AdjoinRoot.mk_eq_mk.mpr (hm Q.1 Q.2.1 Q.2.2.1 hQ)

end GlobalTheory.CompanionTheory.EllCRT
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

namespace GlobalTheory.CompanionTheory.HermFixed

theorem dvd_of_monic_irreducible_factors {K : Type} [Field K] {P d : K[X]} (hs : P.Separable)
    (h : ∀ Q : K[X], Q.Monic → Irreducible Q → Q ∣ P → Q ∣ d) : P ∣ d := by
  by_cases hd : d = 0
  · simp [hd]
  have hP0 : P ≠ 0 := hs.ne_zero
  have hnd : (UniqueFactorizationMonoid.normalizedFactors P).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP0).1 hs.squarefree
  refine (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP0 hd).2 ?_
  refine (Multiset.le_iff_subset hnd).2 fun Q hQ => ?_
  have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor Q hQ
  have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor Q hQ
  have hmon : Q.Monic := by
    rw [← hnorm]
    exact Polynomial.monic_normalize hirr.ne_zero
  have hdvd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ
  exact UniqueFactorizationMonoid.mem_normalizedFactors_iff' hd |>.2 ⟨hirr, hnorm, h Q hmon hirr hdvd⟩

theorem dvd_map_comp_sub {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r)
    (m r₀ : E[X]) (hr : Q.1 ∣ X * r₀ - 1)
    (hfix : invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) :
    Q.1 ∣ (m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀ - m := by
  have h1 : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0 := AdjoinRoot.mk_eq_zero.2 hr
  rw [map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h1
  have hR : AdjoinRoot.mk Q.1 r₀ = (AdjoinRoot.root Q.1)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hinv : invol Q (AdjoinRoot.mk Q.1 m : Fld Q)
      = AdjoinRoot.mk Q.1 ((m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀) := by
    show AdjoinRoot.lift ((AdjoinRoot.of Q.1).comp (IsCMField.complexConj E : E →+* E)) (AdjoinRoot.root Q.1)⁻¹
      (eval₂_conj_inv_root Q) (AdjoinRoot.mk Q.1 m) = _
    rw [AdjoinRoot.lift_mk, ← hR, Polynomial.comp, Polynomial.hom_eval₂, eval₂_map]
    rfl
  have heq : AdjoinRoot.mk Q.1 ((m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀)
      = AdjoinRoot.mk Q.1 m := hinv.symm.trans hfix
  refine AdjoinRoot.mk_eq_zero.1 ?_
  rw [map_sub, heq, sub_self]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m) := by
  intro E _ _ _ n γ₀ hell H₀ hH _ hiso m hfix
  have hsep : γ₀.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ₀.val (γ₀⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ₀.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ₀.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]
  have hAB : aeval γ₀.val r₀ * γ₀.val = 1 := by rw [← hr₀, Units.inv_mul]
  have key := GlobalTheory.CompanionTheory.AdjointPoly.cT_aeval_mul_eq E (IsCMField.complexConj E).toRingEquiv.toRingHom n
    γ₀.val H₀ r₀ hiso hAB m
  have hdvd : γ₀.val.charpoly ∣
      (m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀ - m :=
    dvd_of_monic_irreducible_factors hsep fun Q hmon hirr hQ =>
      dvd_map_comp_sub ⟨Q, GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell E n _ hell Q hmon hirr hQ⟩ m r₀
        (hQ.trans hPr) (hfix _ ⟨Q, GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell E n _ hell Q hmon hirr hQ⟩ hQ)
  have heq : aeval γ₀.val ((m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀)
      = aeval γ₀.val m := by
    obtain ⟨t, ht⟩ := hdvd
    have h0 : aeval γ₀.val ((m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀ - m) = 0 := by
      rw [ht, map_mul, Matrix.aeval_self_charpoly, zero_mul]
    rwa [map_sub, sub_eq_zero] at h0
  have hH' : cT (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ = H₀ := hH
  have hmul : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m)
      = cT (IsCMField.complexConj E).toRingEquiv.toRingHom (aeval γ₀.val m)
        * cT (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ := by
    simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
  show cT (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m) = H₀ * aeval γ₀.val m
  rw [hmul, hH', key, heq]

end GlobalTheory.CompanionTheory.HermFixed
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwLevels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem KGL_eq_KO (w : Pl E) (n : ℕ) :
    GlobalTheory.LFun.KGL w (n := n) = GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) := by
  ext g
  rw [GlobalTheory.CompanionTheory.IwEntries.mem_KGL_iff, GlobalTheory.CompanionTheory.IwEntries.mem_KO_iff]

theorem isCompact_KGL (w : Pl E) (n : ℕ) : IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) := by
  rw [KGL_eq_KO]
  exact GlobalTheory.SplitFlip.isCompact_KO

theorem iwGL_le_KGL (w : Pl E) (n : ℕ) : iwGL n w ≤ GlobalTheory.LFun.KGL w (n := n) := by
  rw [KGL_eq_KO]
  exact GlobalTheory.SmGL.iwahori_le_KO _ _

theorem isClosed_UL {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (hc : Continuous (cj w)) :
    IsClosed (UL n w : Set (GLw n w)) := by
  rw [GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]
  exact GlobalTheory.CompanionTheory.UnitaryWitt.isClosed_UJ_one n hc

theorem isOpen_KL (n : ℕ) (w : Pl E) : IsOpen (KL n w : Set (UL n w)) := by
  have h : IsOpen (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) := by
    rw [KGL_eq_KO]
    exact GlobalTheory.SplitFlip.isOpen_KO
  exact h.preimage (continuous_subtype_val (p := (· ∈ UL n w)))

theorem isCompact_KL {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (hc : Continuous (cj w)) :
    IsCompact (KL n w : Set (UL n w)) :=
  (isClosed_UL hw n hc).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_KGL w n)

theorem isOpen_iwU (n : ℕ) (w : Pl E) (b : GLw n w) : IsOpen (iwU n w b : Set (UL n w)) := by
  have ho : IsOpen (iwGL n w : Set (GLw n w)) :=
    GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin n)
  have hcont : Continuous fun γ : UL n w => b⁻¹ * γ.1 * b :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  have e : (iwU n w b : Set (UL n w)) = (fun γ : UL n w => b⁻¹ * γ.1 * b) ⁻¹' (iwGL n w : Set (GLw n w)) := by
    ext γ
    exact GlobalTheory.CompanionTheory.UnitaryWitt.mem_iwU_iff n w b γ
  rw [e]
  exact ho.preimage hcont

theorem iwU_le_KL (n : ℕ) (w : Pl E) (b : GLw n w) (hb : b ∈ GlobalTheory.LFun.KGL w (n := n)) :
    iwU n w b ≤ KL n w := by
  intro γ hγ
  have h1 := iwGL_le_KGL w n ((GlobalTheory.CompanionTheory.UnitaryWitt.mem_iwU_iff n w b γ).1 hγ)
  have h2 : γ.1 = b * (b⁻¹ * γ.1 * b) * b⁻¹ := by group
  rw [KL, Subgroup.mem_subgroupOf, h2]
  exact mul_mem (mul_mem hb h1) (inv_mem hb)

theorem relIndex_ne_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H K : Subgroup G}
    (hH : IsOpen (H : Set G)) (hK : IsCompact (K : Set G)) : H.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let U : OpenSubgroup K := ⟨H.subgroupOf K, hH.preimage continuous_subtype_val⟩
  haveI : Finite (K ⧸ (U : Subgroup K)) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  exact Subgroup.index_ne_zero_of_finite

theorem isCompact_support_fU {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w)
    (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) (hc : Continuous (cj w)) :
    IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0} := by
  set t : GLw n w := b * tdiag ϖ (wexp n l) * b⁻¹ with ht
  have hI : IsCompact (iwU n w b : Set (UL n w)) :=
    GlobalTheory.CompanionTheory.UnitaryWitt.isCompact_iwU hw n b hc
  have hS : IsCompact ((fun p : UL n w × UL n w => p.1.1 * t * p.2.1) ''
      ((iwU n w b : Set (UL n w)) ×ˢ (iwU n w b : Set (UL n w)))) :=
    (hI.prod hI).image (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
      (continuous_subtype_val.comp continuous_snd))
  have e : {g : UL n w | fU n w b ϖ l g ≠ 0} = Subtype.val ⁻¹'
      ((fun p : UL n w × UL n w => p.1.1 * t * p.2.1) ''
        ((iwU n w b : Set (UL n w)) ×ˢ (iwU n w b : Set (UL n w)))) := by
    ext γ
    simp only [Set.mem_setOf_eq, fU, Set.mem_preimage, Set.mem_image, Set.mem_prod, SetLike.mem_coe]
    constructor
    · intro h
      by_contra hn
      refine h (if_neg ?_)
      rintro ⟨x, hx, z, hz, e⟩
      exact hn ⟨(x, z), ⟨hx, hz⟩, e.symm⟩
    · rintro ⟨⟨x, z⟩, ⟨hx, hz⟩, e⟩
      rw [if_pos ⟨x, hx, z, hz, e.symm⟩]
      exact one_ne_zero
  rw [e]
  exact (isClosed_UL hw n hc).isClosedEmbedding_subtypeVal.isCompact_preimage hS

theorem levels_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ), IsUnifAt ϖ → Cone l → IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ IsLevel (MonoidHom.id _) (KL n w) (iwU n w b) ∧ (iwU n w b).relIndex (KL n w) ≠ 0 ∧ IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0} := by
  intro E _ _ _ hU w hw n b hb ϖ l _ _
  have hc : Continuous (cj w) := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1
  exact ⟨isOpen_KL n w, isCompact_KL hw n hc,
    ⟨isOpen_iwU n w b, iwU_le_KL n w b hb.1, fun k hk => hk⟩,
    relIndex_ne_zero (isOpen_iwU n w b) (isCompact_KL hw n hc),
    isCompact_support_fU hw n b ϖ l hc⟩

end GlobalTheory.CompanionTheory.IwLevels
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.DiagCoset

theorem v_eq_of_ne {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L} (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dite_eq_right h0]
  simp

theorem diagT_mem_iwGL {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ)
    (τ : Fin n → (w.adicCompletion E)ˣ) (hτ : ∀ i, Valued.v (τ i : w.adicCompletion E) = 1) :
    GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ ∈ iwGL n w := by
  have hinv : ∀ i, Valued.v ((τ⁻¹) i : w.adicCompletion E) = 1 := by
    intro i
    have : (((τ⁻¹) i : (w.adicCompletion E)ˣ) : w.adicCompletion E) = (τ i : w.adicCompletion E)⁻¹ := by
      simp
    rw [this, map_inv₀, hτ, inv_one]
  have hle : ∀ (ρ : Fin n → (w.adicCompletion E)ˣ), (∀ i, Valued.v (ρ i : w.adicCompletion E) = 1) →
      ∀ i j, Valued.v ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) ρ).val i j) ≤ 1 := by
    intro ρ hρ i j
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, hρ]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero]
      exact zero_le'
  refine ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1).2 ⟨hle τ hτ, ?_, ?_⟩
  · rw [← map_inv]
    exact hle _ hinv
  · intro i j hij
    rw [GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_ne _ (ne_of_gt hij), map_zero]
    exact zero_lt_one

theorem fU_diag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → ∀ (γ : UL n w) (u : Fin n → (w.adicCompletion E)ˣ), (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) → γ.1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ → ∀ x ∈ iwU n w b, ∀ z ∈ iwU n w b, fU n w b ϖ l (x * γ * z) = 1 := by
  intro E _ _ _ hU w hw n b hb ϖ hϖ l hl γ u hu hγ x hx z hz
  obtain ⟨hUL, hiw, -, hdiag⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  have hrev := (GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).2

  set τ : Fin n → (w.adicCompletion E)ˣ := fun i => u i * (ϖ ^ wexp n l i)⁻¹ with hτdef
  have hvϖ : Valued.v (ϖ : w.adicCompletion E) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [v_eq_of_ne ϖ.ne_zero, hϖ.1]
  have hvpow : ∀ d : ℤ, Valued.v (((ϖ ^ d : (w.adicCompletion E)ˣ)) : w.adicCompletion E) =
      ((Multiplicative.ofAdd (-d) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro d
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hvϖ, ← WithZero.coe_zpow, ← ofAdd_zsmul]
    simp
  have hτ : ∀ i, Valued.v (τ i : w.adicCompletion E) = 1 := by
    intro i
    have e : ((τ i : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        (u i : w.adicCompletion E) * (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹ := by
      simp [hτdef]
    rw [e, map_mul, map_inv₀, hvpow, v_eq_of_ne (u i).ne_zero, hu i]
    exact mul_inv_cancel₀ WithZero.coe_ne_zero
  have hfac : GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u =
      tdiag ϖ (wexp n l) * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ := by
    rw [tdiag, ← map_mul]
    congr 1
    funext i
    simp [hτdef]

  have hu1 : ∀ i, cj w (u i : w.adicCompletion E) * (u (Fin.rev i) : w.adicCompletion E) = 1 := by
    have h1 : b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ ∈ UL n w := hγ ▸ γ.2
    exact (hdiag u).1 ((hUL _).1 h1)
  have hcjϖ : ∀ d : ℤ, cj w (((ϖ ^ d : (w.adicCompletion E)ˣ)) : w.adicCompletion E) =
      ((ϖ ^ d : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    intro d
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ.2]
  have hτ1 : ∀ i, cj w (τ i : w.adicCompletion E) * (τ (Fin.rev i) : w.adicCompletion E) = 1 := by
    intro i
    have e : ∀ j, ((τ j : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        (u j : w.adicCompletion E) * (((ϖ ^ wexp n l j : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹ := by
      intro j
      simp [hτdef]
    rw [e, e, map_mul, map_inv₀, hcjϖ, hrev i, _root_.zpow_neg]
    have h2 := hu1 i
    have hp : (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E) ≠ 0 := Units.ne_zero _
    simp only [Units.val_inv_eq_inv_val, inv_inv]
    calc _ = (cj w (u i : w.adicCompletion E) * (u (Fin.rev i) : w.adicCompletion E)) *
          ((((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹ *
            (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E)) := by ring
      _ = 1 := by rw [h2, inv_mul_cancel₀ hp, one_mul]
  have hκU : b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ * b⁻¹ ∈ UL n w :=
    (hUL _).2 ((hdiag τ).2 hτ1)
  let κ : UL n w := ⟨_, hκU⟩
  have hκ : κ ∈ iwU n w b := by
    rw [hiw]
    have : b⁻¹ * κ.1 * b = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ := by
      change b⁻¹ * (b * _ * b⁻¹) * b = _
      group
    rw [this]
    exact diagT_mem_iwGL w n τ hτ
  unfold fU
  refine if_pos ⟨x, hx, κ * z, mul_mem hκ hz, ?_⟩
  change x.1 * γ.1 * z.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * ((b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ * b⁻¹) * z.1)
  rw [hγ, hfac]
  group

end GlobalTheory.CompanionTheory.DiagCoset
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitary_iwahori_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → (∀ g : GLw n w, b * g * b⁻¹ ∈ UL n w ↔ g ∈ UJ (cj w) (antiJ (w.adicCompletion E) n)) ∧ (∀ γ : UL n w, γ ∈ iwU n w b ↔ b⁻¹ * γ.1 * b ∈ iwGL n w) ∧ IsCompact (iwU n w b : Set (UL n w)) ∧ ∀ u : Fin n → (w.adicCompletion E)ˣ, GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u ∈ UJ (cj w) (antiJ (w.adicCompletion E) n) ↔ ∀ i, cj w (u i) * u (Fin.rev i) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis | exact GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis | (intros; apply GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.norm_one_unit_hilbert_ninety : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ c : w.adicCompletion E, cj w c = c → Valued.v c = 1 → ∃ s : w.adicCompletion E, Valued.v s = 1 ∧ cj w s * s = c := by
  first | exact @GlobalTheory.CompanionTheory.UnitNormLocal.exists_unit_norm_eq | exact GlobalTheory.CompanionTheory.UnitNormLocal.exists_unit_norm_eq | (intros; apply GlobalTheory.CompanionTheory.UnitNormLocal.exists_unit_norm_eq <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS
open GlobalTheory.LFun.ConjPlace (invT dGL apply_heckeVec_shift Tj_invT Tj_shift_self map_mem_Ov_iff mem_iff_invT satEig_inv_mul satEig_zero)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ThetaSatPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

variable {u w : Pl E}

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem embT_cw (a : ℕ) (u : Pl E) (g : GLw a (GlobalTheory.ThetaSatake.cw u)) :
    embT a (GlobalTheory.ThetaSatake.cw u) g =
      embW a u (PhiU a _ * invT (GlobalTheory.ThetaSatake.cloc u) a g * (PhiU a _)⁻¹) := by
  change GlobalTheory.ThetaPull.thetaA E a (finGL E a (locGL E a (GlobalTheory.ThetaSatake.cw u) g)) = finGL E a (locGL E a u _)
  rw [GlobalTheory.ThetaPull.thetaA_finGL, GlobalTheory.ThetaSatake.theta_locGL, GlobalTheory.ThetaSatake.thetaGL_conj]

theorem invT_symm {K K' : Type} [Field K] [Field K'] (c : K ≃+* K') (n : ℕ) (g : GL (Fin n) K') :
    (invT c n).symm g = invT c.symm n g := rfl

end GlobalTheory.CompanionTheory.ThetaSatPair
end
end
