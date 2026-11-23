module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle007
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Bundle003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle183
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateOperatorLevelComplement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Formalism.SharpRestriction.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle460
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle018
public import Formalism.SharpRestriction.LevelLetterCocycles.ExportBoundOfAdmissible
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle024
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Nonarchimedean.Completion
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
public import Mathlib.Algebra.Group.AddChar
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory

theorem card_dual_zmod_le_card :
    ∀ (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A] [Module (ZMod n) A] [Finite A],
      Nat.card (Module.Dual (ZMod n) A) ≤ Nat.card A := by
  apply GlobalTheory.TateTop.card_dual_le <;> assumption

end GlobalTheory
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitRowProbe

namespace GlobalTheory.SplitType

theorem exists_sqrt (l d : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2) (hj : jacobiSym (-(d : ℤ)) l = 1) :
    ∃ s : ℤ_[l], s ^ 2 = -(d : ℤ_[l]) ∧ ‖2 * s‖ = 1 := by
  have hd : ¬ (l : ℤ) ∣ (d : ℤ) := by
    intro h
    have : jacobiSym (-(d : ℤ)) l = 0 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h.neg_right
    omega
  have h2' : ¬ (l : ℤ) ∣ 2 := fun h =>
    h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 (by exact_mod_cast h))
  have one_of : ∀ k : ℤ, ¬ (l : ℤ) ∣ k → ‖(k : ℤ_[l])‖ = 1 := fun k hk =>
    le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hk ((PadicInt.norm_int_lt_one_iff_dvd k).1 h))
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective r
  have ha : (l : ℤ) ∣ a ^ 2 + d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hr ⊢
    linear_combination -hr
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  have ha' : ¬ (l : ℤ) ∣ 2 * a := by
    intro h
    rcases hp.dvd_or_dvd h with h | h
    · exact h2' h
    · exact hd ((dvd_add_right (dvd_pow h two_ne_zero)).1 ha)
  obtain ⟨s, hs⟩ := Misc.isSquare_of_hensel l d a (by
    rw [one_of _ ha', one_pow]
    exact (PadicInt.norm_int_lt_one_iff_dvd _).2 ha)
  have hs2 : s ^ 2 = -(d : ℤ_[l]) := by
    rw [sq, ← hs]; simp
  refine ⟨s, hs2, ?_⟩
  have n2 : ‖(2 : ℤ_[l])‖ = 1 := by simpa using one_of 2 h2'
  have nd : ‖(d : ℤ_[l])‖ = 1 := by simpa using one_of d hd
  have : ‖s‖ ^ 2 = 1 := by rw [← norm_pow, hs2, norm_neg, nd]
  rw [norm_mul, n2, one_mul]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this

theorem exists_root {l d : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] (f : ℤ_[l] →+* A)
    {s : ℤ_[l]} (hs : s ^ 2 = -(d : ℤ_[l])) {y : A} (hy : y ^ 2 = -(d : A)) :
    ∃ t : ℤ_[l], (t = s ∨ t = -s) ∧ f t = y := by
  have : y ^ 2 = (f s) ^ 2 := by rw [← map_pow, hs, hy]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h
  · exact ⟨s, Or.inl rfl, h.symm⟩
  · exact ⟨-s, Or.inr rfl, by rw [map_neg, h]⟩

section Host
variable {R : Ranks} (H : Host R)

theorem sqrtE_sq : (H.sqd) ^ 2 = -(H.d : H.E) := H.sqd_sq

theorem map_sqrt_sq {A : Type} [CommRing A] (φ : H.E →+* A) : φ (H.sqd) ^ 2 = -(H.d : A) := by
  rw [← map_pow, sqrtE_sq]; simp

theorem conj_sqrtE : H.conj (H.sqd) = -H.sqd := by
  apply H.φ₀.injective
  have h : H.φ₀ (H.sqd) = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [conj_sqrt, map_neg, h]
  simp

theorem isIntegral_sqrtE : IsIntegral ℤ (H.sqd) := by
  refine IsIntegral.of_pow two_pos ?_
  rw [sqrtE_sq]
  exact (isIntegral_natCast _).neg

end Host

section Loc
variable (D : D7) (i : D.nd.Loc)

theorem root_of_embIn (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    {s₀ t : ℤ_[D.nd.l i]}
    (h₀ : algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (algebraMap ℤ_[D.nd.l i] (D.nd.O i) s₀) =
      D.nd.embK i (D.embE (D.host.sqd)))
    (ht : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (D.host.sqd)))
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) :
    (EmbIn (N := D.nd) D.nbr i true w hw τ → t = s₀) ∧
      (EmbIn (N := D.nd) D.nbr i false w hw τ → t = -s₀) := by
  have e1 : τ (Br.cEw D.nbr i w hw (D.host.sqd)) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (t : ℚ_[D.nd.l i]) := by
    rw [← τ.commutes]
    exact congrArg τ (Subtype.ext ht.symm)
  have e2 : Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sqd))) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (s₀ : ℚ_[D.nd.l i]) := by
    rw [← h₀, Br.toLLK_alg, (D.nbr i w hw).eO_alg]
    rfl
  have e3 : D.what₂.embLL (D.embE (D.host.sqd)) =
      Complex.I * (Real.sqrt D.host.d : ℂ) :=
    (DFunLike.congr_fun D.embE_φ₀ _).trans D.host.φ₀_mem
  have inj := (algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)).injective
  constructor
  · rintro ⟨h1, φ, hφ, h2⟩
    obtain ⟨y, hy⟩ := h1 (D.host.sqd)
    have hφ' : φ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ) := hφ
    have : y = D.embE (D.host.sqd) :=
      D.what₂.embLL.injective ((h2 _ y hy).trans (hφ'.trans e3.symm))
    rw [this, e1, e2] at hy
    exact Subtype.ext (inj hy).symm
  · rintro ⟨h1, φ, hφ, h2⟩
    obtain ⟨y, hy⟩ := h1 (D.host.sqd)
    have hφ' := (mem_halfType_false D.host φ).1 hφ
    have : y = -D.embE (D.host.sqd) :=
      D.what₂.embLL.injective (by rw [h2 _ y hy, hφ', map_neg, e3])
    rw [this, e1, map_neg, map_neg, e2, ← map_neg] at hy
    exact Subtype.ext (inj hy).symm

theorem mem_iff_norm (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (x : 𝓞 D.host.E) (z : ℤ_[D.nd.l i])
    (hz : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (z : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (x : D.host.E))) :
    x ∈ w.asIdeal ↔ ‖z‖ < 1 := by
  rw [bridge_place D i w hw x, ← hz, norm_algebraMap', PadicInt.norm_def]

theorem root_ne (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hw' : w' ∈ placesOver D.host.E (D.nd.l i)) (hc : IsConjPl D.host w w') {t : ℤ_[D.nd.l i]}
    (hn : ‖2 * t‖ = 1)
    (ht : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (D.host.sqd)))
    (ht' : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w' hw').j (algebraMap D.host.E D.nd.Om (D.host.sqd))) : False := by
  let β : 𝓞 D.host.E := ⟨D.host.sqd, isIntegral_sqrtE D.host⟩
  have hβ : (β : D.host.E) = D.host.sqd := rfl
  set n : ℕ := t.zmodRepr with hn'
  have h1 : ‖t - n‖ < 1 := PadicInt.mem_nonunits.1 (PadicInt.sub_zmodRepr_mem t)
  have hx : ((β - n : 𝓞 D.host.E) : D.host.E) = D.host.sqd - n := by
    simp [← hβ]
  have hy : ((-β - n : 𝓞 D.host.E) : D.host.E) = -D.host.sqd - n := by
    simp [← hβ]
  have h2 : β - n ∈ w.asIdeal := (mem_iff_norm D i w hw _ (t - n) (by
    rw [hx, map_sub, map_sub, ← ht]; simp)).2 h1
  have h3 : -β - n ∈ w'.asIdeal := (hc (β - n) (-β - n) (by
    rw [hx, hy, map_sub, conj_sqrtE, map_natCast])).1 h2
  have h4 : ‖-t - n‖ < 1 := (mem_iff_norm D i w' hw' _ (-t - n) (by
    rw [hy, map_sub, map_sub, map_neg, map_neg, ← ht']; simp)).1 h3
  have h5 : 2 * t = (t - n) + -(-t - n) := by ring
  have h6 := PadicInt.nonarchimedean (t - (n : ℤ_[D.nd.l i])) (-(-t - (n : ℤ_[D.nd.l i])))
  rw [← h5, hn, norm_neg] at h6
  exact absurd h6 (not_le.2 (max_lt h1 h4))

end Loc

theorem place_type_conj : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) →
    ∀ (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (hw' : w' ∈ placesOver D.host.E (D.nd.l i)), IsConjPl D.host w w' →
      (PlIn (N := D.nd) D.nbr i true w hw ∧ PlIn (N := D.nd) D.nbr i false w' hw') ∨
        (PlIn (N := D.nd) D.nbr i false w hw ∧ PlIn (N := D.nd) D.nbr i true w' hw') := by
  intro D i hl w w' hw hw' hc
  obtain ⟨-, h5, hq, hd, -, hcls⟩ := hl
  have h2 : D.nd.l i ≠ 2 := by omega
  have hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1 := by
    by_contra hj
    simp only [Host.cls, primeClass, if_neg h2, if_neg hq, if_neg hd, if_neg hj] at hcls
    split_ifs at hcls
  obtain ⟨s, hs, hn⟩ := exists_sqrt (D.nd.l i) D.host.d h2 hj
  obtain ⟨s₀, hs₀, h₀⟩ := exists_root
    ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).comp (algebraMap ℤ_[D.nd.l i] (D.nd.O i))) hs
    (map_sqrt_sq D.host ((D.nd.embK i).comp D.embE))
  have hs0 : s₀ ^ 2 = -(D.host.d : ℤ_[D.nd.l i]) := by rcases hs₀ with rfl | rfl <;> simp [hs]
  have hn0 : ‖2 * s₀‖ = 1 := by rcases hs₀ with rfl | rfl <;> simpa using hn
  have hne : s₀ ≠ -s₀ := fun e => by
    rw [show 2 * s₀ = 0 by linear_combination e] at hn0
    simp at hn0
  have key : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.nd.l i)),
      ∃ t : ℤ_[D.nd.l i], algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
        (D.nbr i v hv).j (algebraMap D.host.E D.nd.Om (D.host.sqd)) ∧
        ((t = s₀ ∧ PlIn (N := D.nd) D.nbr i true v hv) ∨ (t = -s₀ ∧ PlIn (N := D.nd) D.nbr i false v hv)) := by
    intro v hv
    obtain ⟨t, ht, h⟩ := exists_root
      ((algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i))).comp PadicInt.Coe.ringHom) hs0
      (map_sqrt_sq D.host ((D.nbr i v hv).j.comp (algebraMap D.host.E D.nd.Om)))
    refine ⟨t, h, ?_⟩
    rcases ht with ht | ht
    · refine Or.inl ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact e.1
      · exact absurd (ht.symm.trans ((root_of_embIn D i v hv h₀ h τ).2 e.1)) hne
    · refine Or.inr ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact absurd (((root_of_embIn D i v hv h₀ h τ).1 e.1).symm.trans ht) hne
      · exact e.1
  obtain ⟨t, ht, h⟩ := key w hw
  obtain ⟨t', ht', h'⟩ := key w' hw'
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases h' with ⟨e, h'⟩ | ⟨e, h'⟩
  · exact (root_ne D i w w' hw hw' hc hn0 ht (e ▸ ht')).elim
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr ⟨h, h'⟩
  · exact (root_ne D i w w' hw hw' hc (by simpa using hn0) ht (e ▸ ht')).elim

end GlobalTheory.SplitType

end
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∀ d ∈ Dec (F := E) A, ∀ y : Ω, ∃ τ ∈ Weil h, τ y = d y := by
  first | exact @GlobalTheory.WeilDeligne.exists_weil_apply_eq | exact GlobalTheory.WeilDeligne.exists_weil_apply_eq | (intros; apply GlobalTheory.WeilDeligne.exists_weil_apply_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.AveragingRankOne

theorem exists_reps {G : Type*} [Group G] (H U V : Subgroup G) [U.FiniteIndex]
    (hV : ∀ g ∈ H, g ∈ V ↔ g ∈ U) :
    ∃ S : Finset G, (∀ s ∈ S, s ∈ H) ∧ ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ V := by
  classical
  letI : Fintype (H ⧸ U.subgroupOf H) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : H ⧸ U.subgroupOf H => (q.out : G)), ?_, ?_⟩
  · intro s hs
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
    exact q.out.2
  · intro h hh
    have key : ∀ q : H ⧸ U.subgroupOf H, (q.out : G)⁻¹ * h ∈ V ↔ q = ((⟨h, hh⟩ : H) : H ⧸ U.subgroupOf H) := by
      intro q
      rw [hV _ (H.mul_mem (H.inv_mem q.out.2) hh)]
      conv_rhs => rw [← q.out_eq']
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      rfl
    refine ⟨(((⟨h, hh⟩ : H) : H ⧸ U.subgroupOf H).out : G),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (key _).2 rfl⟩, ?_⟩
    rintro s ⟨hs, hs'⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
    rw [(key q).1 hs']

variable {l : ℕ} [Fact l.Prime]

theorem exists_field (F : IntermediateField ℚ_[l] (Om l)) (W : Set (GQ l)) (hW : W ∈ nhds (1 : GQ l)) :
    ∃ (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)), F ≤ L ∧
      (∀ h ∈ F.fixingSubgroup, ∀ x ∈ L, h x ∈ L) ∧ (∀ s ∈ S, s ∈ F.fixingSubgroup) ∧
      (∀ h ∈ F.fixingSubgroup, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) ∧
      ∀ g ∈ L.fixingSubgroup, g ∈ W := by
  obtain ⟨E, hfd, hN, hE⟩ := (krullTopology_mem_nhds_one_iff_of_normal ℚ_[l] (Om l) W).1 hW
  haveI : E.fixingSubgroup.FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen E.fixingSubgroup E.fixingSubgroup_isOpen
    exact Subgroup.finiteIndex_of_finite_quotient
  have hsup : (F ⊔ E).fixingSubgroup = F.fixingSubgroup ⊓ E.fixingSubgroup :=
    IntermediateField.fixingSubgroup_sup
  obtain ⟨S, hS, hS'⟩ := exists_reps F.fixingSubgroup E.fixingSubgroup (F ⊔ E).fixingSubgroup
    (fun g hg => by rw [hsup, Subgroup.mem_inf]; exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩)
  refine ⟨F ⊔ E, S, le_sup_left, ?_, hS, hS', fun g hg => hE ?_⟩
  · intro h hh
    have : F ⊔ E ≤ (F ⊔ E).comap (h : Om l →ₐ[ℚ_[l]] Om l) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · have h1 : h x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x hx
        change h x ∈ F ⊔ E
        rw [h1]; exact (le_sup_left : F ≤ F ⊔ E) hx
      · change h x ∈ F ⊔ E
        have h1 := AlgEquiv.restrictNormal_commutes h E ⟨x, hx⟩
        have h2 : h x ∈ E := by
          have : h x = (h.restrictNormal E ⟨x, hx⟩ : E) := h1.symm
          rw [this]; exact Subtype.property _
        exact (le_sup_right : E ≤ F ⊔ E) h2
    exact fun x hx => this hx
  · rw [hsup] at hg; exact hg.2

theorem average {G C : Type*} [Group G] [NormedField C] [IsUltrametricDist C]
    (act : G →* (C ≃+* C)) (hn : ∀ g y, ‖act g y‖ = ‖y‖) (H V : Subgroup G) (S : Finset G)
    (hS : ∀ s ∈ S, s ∈ H) (hS' : ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ V)
    (a b : C) (hb : ‖b‖ ≤ 1) (hbV : ∀ g ∈ V, act g b = b) (hab : ∑ s ∈ S, act s b = a)
    (c : G → C) (hc : ∀ g ∈ H, ∀ h ∈ H, c (g * h) = c g + act g (c h))
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε : 0 ≤ ε) (ht : ∀ g ∈ H, ‖c g‖ ≤ t)
    (hV : ∀ g ∈ H, g ∈ V → ‖c g‖ ≤ ε) :
    ∃ x : C, ‖x‖ ≤ t ∧ ∀ h ∈ H, ‖a * c h - (act h x - x)‖ ≤ ε := by
  first
  | exact @_root_.GlobalTheory.PermutationExistence.main
  | exact _root_.GlobalTheory.PermutationExistence.main
  | (apply _root_.GlobalTheory.PermutationExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PermutationExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PermutationExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PermutationExistence.main ..)

theorem step (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (hact : IsActC act) (K : FinExt l)
    (a : PadicComplex l) (ha : a ∈ inC (Kinf K)) (ha1 : ‖a‖ < 1) (c : GQ l → PadicComplex l)
    (hcont : ContinuousOn c (Hinf K))
    (hc : ∀ g ∈ Hinf K, ∀ h ∈ Hinf K, c (g * h) = c g + act g (c h))
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε : 0 < ε) (ht : ∀ g ∈ Hinf K, ‖c g‖ ≤ t) :
    ∃ x : PadicComplex l, ‖x‖ ≤ t ∧ ∀ h ∈ Hinf K, ‖a * c h - (act h x - x)‖ ≤ ε := by
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  have hc1 : c 1 = 0 := by
    have := hc 1 (one_mem _) 1 (one_mem _)
    simpa using this
  have hev : ∀ᶠ g in nhdsWithin (1 : GQ l) (Hinf K), ‖c g‖ < ε := by
    have := (hcont 1 (one_mem _)).norm
    refine this.eventually (p := fun r => r < ε) (gt_mem_nhds ?_)
    simpa [hc1] using hε
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨L, S, hL, hst, hS, hS', hW⟩ := exists_field (Kinf K) _ hev
  obtain ⟨b, hbL, hb1, hb⟩ := GlobalTheory.T.cyclotomicTower_trace_almost_surjective l K L S hL hst hS hS' a₀ ha₀ (by simpa using ha1)
  refine average act hact.2 (Hinf K) L.fixingSubgroup S hS hS' _ (b : PadicComplex l)
    (by simpa using hb1) (fun g hg => ?_) ?_ c hc t ε ht0 hε.le ht (fun g hg hg' => (hW g hg' hg).le)
  · rw [hact.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg b hbL]
  · simp only [hact.1, ← hb]
    exact (map_sum (algebraMap (Om l) (PadicComplex l)) _ _).symm

theorem rank_one (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (hact : IsActC act)
    (K : FinExt l) (a : PadicComplex l) (ha : a ∈ inC (Kinf K)) (ha1 : ‖a‖ < 1)
    (c : GQ l → PadicComplex l) (hcont : ContinuousOn c (Hinf K))
    (hc : ∀ g ∈ Hinf K, ∀ h ∈ Hinf K, c (g * h) = c g + act g (c h))
    (ht : ∀ g ∈ Hinf K, ‖c g‖ ≤ 1) :
    ∃ x : PadicComplex l, ‖x‖ ≤ 1 ∧ ∀ h ∈ Hinf K, a * c h = act h x - x := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact ⟨0, by simp, by simp⟩
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hfix : ∀ g ∈ Hinf K, act g a = a := by
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    intro g hg
    rw [hact.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg a₀ ha₀]
  let Q : ℕ → PadicComplex l → Prop := fun n y =>
    ‖y‖ ≤ 1 ∧ ∀ h ∈ Hinf K, ‖a * c h - (act h y - y)‖ ≤ ‖a‖ * (1 / 2) ^ n
  have hstep : ∀ n y, Q n y → ∃ y', Q (n + 1) y' ∧ dist y y' ≤ 1 * (1 / 2 : ℝ) ^ n := by
    rintro n y ⟨hy1, hy⟩
    obtain ⟨x, hx, hx'⟩ := step act hact K a ha ha1 (fun g => c g - a⁻¹ * (act g y - y))
      (hcont.sub (continuousOn_const.mul
        ((GlobalTheory.T.continuous_orbit_padicComplex l act hact y).continuousOn.sub continuousOn_const)))
      (fun g hg h hh => by
        simp only [hc g hg h hh, map_mul, map_sub, map_inv₀, hfix g hg, RingAut.mul_apply]
        ring)
      ((1 / 2) ^ n) (‖a‖ * (1 / 2) ^ (n + 1)) (by positivity) (by positivity)
      (fun g hg => by
        have e : c g - a⁻¹ * (act g y - y) = a⁻¹ * (a * c g - (act g y - y)) := by
          field_simp
        rw [e, norm_mul, norm_inv, inv_mul_le_iff₀ hapos]
        exact hy g hg)
    refine ⟨y + x, ⟨?_, fun h hh => ?_⟩, ?_⟩
    · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy1 (hx.trans ?_))
      exact pow_le_one₀ (by norm_num) (by norm_num)
    · have e : a * c h - (act h (y + x) - (y + x)) =
          a * (c h - a⁻¹ * (act h y - y)) - (act h x - x) := by
        rw [map_add (f := _)]; field_simp; ring
      rw [e]; exact hx' h hh
    · simpa [dist_eq_norm] using hx
  choose! f hfQ hfd using hstep
  let y : ℕ → PadicComplex l := fun n => Nat.rec 0 f n
  have hQ : ∀ n, Q n (y n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [y], fun h hh => ?_⟩
      simpa [y] using mul_le_mul_of_nonneg_left (ht h hh) hapos.le
    | succ n ih => exact hfQ n _ ih
  have hcau : CauchySeq y :=
    cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num) fun n => hfd n _ (hQ n)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨x, le_of_tendsto' hx.norm fun n => (hQ n).1, fun h hh => ?_⟩
  have hiso : Continuous (act h) :=
    (AddMonoidHomClass.isometry_of_norm (act h) (hact.2 h)).continuous
  have h1 : Filter.Tendsto (fun n => ‖a * c h - (act h (y n) - y n)‖) Filter.atTop
      (nhds ‖a * c h - (act h x - x)‖) :=
    (tendsto_const_nhds.sub (((hiso.tendsto x).comp hx).sub hx)).norm
  have h2 : Filter.Tendsto (fun n : ℕ => ‖a‖ * (1 / 2 : ℝ) ^ n) Filter.atTop (nhds (‖a‖ * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
  have := le_of_tendsto_of_tendsto' h1 h2 fun n => (hQ n).2 h hh
  rw [mul_zero, norm_le_zero_iff, sub_eq_zero] at this
  exact this

theorem cyclotomic_maximalIdeal_smul_cocycle_isCoboundary : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ (K : FinExt l) (r : ℕ) (a : PadicComplex l), a ∈ inC (Kinf K) → ‖a‖ < 1 → ∀ c : GQ l → Fin r → PadicComplex l, CocOn (Hinf K) (fun g y k => act g (y k)) (ball l r) c → CobOn (Hinf K) (fun g y k => act g (y k)) (ball l r) (fun g => a • c g) := by
  intro l _ act hact K r a ha ha1 c ⟨h1, h2, h3⟩
  choose x hx hx' using fun k : Fin r => rank_one act hact K a ha ha1 (fun g => c g k)
    ((continuous_apply k).comp_continuousOn h1)
    (fun g hg h hh => congrFun (h3 g hg h hh) k) (fun g hg => h2 g hg k)
  exact ⟨x, hx, fun g hg => funext fun k => hx' k g hg⟩

end GlobalTheory.Cyc.AveragingRankOne
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.exists_tate_operator_levelComplement : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ g, IsGen χ K j g → ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ l → ∃ S : PadicComplex l → PadicComplex l, (∀ x ∈ Xj K j, S x ∈ Xj K j ∧ act g (S x) - S x = (ζ - 1) * x ∧ S (act g x - x) = (ζ - 1) * x) ∧ (∀ x ∈ Xj K j, ∀ x' ∈ Xj K j, S (x + x') = S x + S x') ∧ ∀ y ∈ intC (Ks K j), ∀ x ∈ Xj K j, S (y * x) = y * S x := by
  first | exact @GlobalTheory.Cyc.exists_tate_operator | exact GlobalTheory.Cyc.exists_tate_operator | (intros; apply GlobalTheory.Cyc.exists_tate_operator <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.LinkFam

theorem main : ∀ {eps : ℝ} (Fm : FamP eps), ConclF Fm → Formalism.MainNotions.LinkN Fm := by
  intro eps Fm hC
  obtain ⟨C, x0, h⟩ := hC
  have hA : Formalism.MainNotions.TwistedPlaces.AdmF Fm := ⟨C, x0, fun x hx hx1 i hS => by
    obtain ⟨X, hX⟩ := h x hx hx1 i hS
    exact GlobalTheory.T.admittedStatements_of_localBoundsConclusion_alt _ _ _ X C hX⟩
  exact Formalism.MainNotions.N.linkN_of Fm hA (Formalism.MainNotions.TwistedPlaces.stmtF_holds Fm)

end GlobalTheory.LinkFam
end
