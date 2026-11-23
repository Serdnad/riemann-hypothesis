module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle505
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle473
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle867
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle975
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)
open GlobalTheory.ThetaTransform

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.adelicCoordinates_rationalMatrices_onto_rational : ∀ (D : D7) (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AE D) ≃ₗ[AF D.host.F] VA D.host.F N), (∀ x : Matrix (Fin m) (Fin n) D.host.E, ∃ y z : Fin N → D.host.F, e (incM D.host.F x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) → ∀ y z : Fin N → D.host.F, ∃ x : Matrix (Fin m) (Fin n) D.host.E, e (incM D.host.F x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := by
  first | exact @GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps | exact GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps | (intros; apply GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (n : ℕ) (X : Spc D.host.F D.host.E n) (r s : ℕ), X.IsHerm D.sp.cm.sig B r s →
      (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).IsSymm ∧ (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).Nondegenerate ∧
        Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ) X.L := by
  first | exact @GlobalTheory.WeilSchrodingerHerm.main | exact GlobalTheory.WeilSchrodingerHerm.main | (intros; apply GlobalTheory.WeilSchrodingerHerm.main <;> assumption)
end

section

noncomputable section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

namespace GlobalTheory.ParamLabel

variable {p : ℕ} [Fact p.Prime]

theorem bb_eq (p r : ℕ) : BB p r = Formalism.CyclotomicNorms.BB r p := by
  ext l
  simp only [BB, Formalism.CyclotomicNorms.BB, Formalism.CyclotomicNorms.Exc, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, ← pow_mul, mul_comm 4]
  refine or_congr_right ⟨fun ⟨h, a, h1, h2, h3⟩ => ⟨a, h1, h2, h, h3⟩, fun ⟨a, h1, h2, h, h3⟩ => ⟨h, a, h1, h2, h3⟩⟩

theorem primeToPart_frob (l i : ℕ) (z : Fbar p) (a : ZMod p) :
    Formalism.CyclotomicNorms.primeToPart l (z ^ p ^ i) = Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) a) ↔
      Formalism.CyclotomicNorms.primeToPart l z = Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) a) := by
  let β : Fbar p ≃* Fbar p := (iterateFrobeniusEquiv (Fbar p) p i).toMulEquiv
  have h1 : z ^ p ^ i = β z := rfl
  have h2 : β (algebraMap (ZMod p) (Fbar p) a) = algebraMap (ZMod p) (Fbar p) a := by
    show algebraMap (ZMod p) (Fbar p) a ^ p ^ i = _
    rw [← map_pow, ZMod.pow_card_pow]
  conv_lhs => rw [h1, ← h2, GlobalTheory.GoodCharsCompare.primeToPart_map, GlobalTheory.GoodCharsCompare.primeToPart_map]
  exact β.injective.eq_iff

section Good

variable {L : GlobalTheory.GLq.LabelDatum p} {r : ℕ} {s : SSParam p ℂ r} {x : Cyc s.1 → Fbar p} {f : (ZMod p)[X]}

theorem Labels.root (h : Labels L s x f) (y) : LabelsChar L (rootChar s y) (rootElt x y) :=
  (GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L _ r.factorial_pos).1 _ (cycLen_dvd s.1 y.1) _ _ _ (h.1 y.1)

theorem Labels.cyc (h : Labels L s x f) (c) : LabelsChar L (cycChar s c) (x c) := by
  have := (GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L _ r.factorial_pos).1 _ (cycLen_dvd s.1 c) _ _ 1 (h.1 c)
  rwa [pow_one, pow_one] at this

theorem Labels.mem_roots (h : Labels L s x f) (z : Fbar p) : z ∈ Formalism.CyclotomicNorms.rootsBar f ↔ ∃ y, rootElt x y = z := by
  rw [h.2.2.2]; simp

theorem Labels.regular_iff (h : Labels L s x f) : IsRegularParam s ↔ Squarefree f := by
  rw [(GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2).2.2.1]
  exact forall₂_congr fun y y' => by
    rw [(GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart p L _ r.factorial_pos _ _ _ _ (h.root y) (h.root y')).1]

theorem Labels.two_iff (h : Labels L s x f) (hs : Squarefree f) {l : ℕ} (hl : l.Prime) :
    (∀ y y', y ≠ y' → ¬ CongrMod l (rootChar s y) (rootChar s y')) ↔
      ∀ z ∈ Formalism.CyclotomicNorms.rootsBar f, ∀ z' ∈ Formalism.CyclotomicNorms.rootsBar f, Formalism.CyclotomicNorms.primeToPart l z = Formalism.CyclotomicNorms.primeToPart l z' → z = z' := by
  have hi := (GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2).2.2.1.1 hs
  simp only [h.mem_roots, forall_exists_index, forall_apply_eq_imp_iff, hi.eq_iff]
  exact forall₂_congr fun y y' => by
    rw [(GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart p L _ r.factorial_pos _ _ _ _ (h.root y) (h.root y')).2 l hl, not_imp_not]

theorem Labels.three_iff (h : Labels L s x f) {χ : (ZMod p)ˣ →* ℂˣ} {a : (ZMod p)ˣ} (ha : LabelsTame L χ a)
    {l : ℕ} (hl : l.Prime) :
    (∀ c, ¬ CongrMod l (cycChar s c) (χ.comp (baseNorm p r.factorial))) ↔
      ∀ z ∈ Formalism.CyclotomicNorms.rootsBar f, Formalism.CyclotomicNorms.primeToPart l z ≠
        Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) := by
  have hχ := ((GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L _ r.factorial_pos).2 χ a ha).1
  simp only [h.mem_roots, forall_exists_index, forall_apply_eq_imp_iff, rootElt, Ne, primeToPart_frob,
    (GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart p L _ r.factorial_pos _ _ _ _ (h.cyc _) hχ).2 l hl]
  exact ⟨fun H y => H y.1, fun H c => H ⟨c, ⟨0, cycLen_pos _ c⟩⟩⟩

theorem Labels.ne_of (h : Labels L s x f) {χ : (ZMod p)ˣ →* ℂˣ} {a : (ZMod p)ˣ} (ha : LabelsTame L χ a) {l : ℕ}
    (H : ∀ z ∈ Formalism.CyclotomicNorms.rootsBar f, Formalism.CyclotomicNorms.primeToPart l z ≠
        Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a : ZMod p))) (y) :
    rootChar s y ≠ χ.comp (baseNorm p r.factorial) := fun e => by
  have hχ := ((GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L _ r.factorial_pos).2 χ a ha).1
  have := (GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart p L _ r.factorial_pos _ _ _ _ (h.root y) hχ).1.1 e
  exact H _ ((h.mem_roots _).2 ⟨y, rfl⟩) (by rw [this])

theorem Labels.dvd_iff (h : Labels L s x f) (hs : Squarefree f) :
    (∀ a : ℕ, (∃ q : (ZMod p)[X], q ∣ f ∧ q.natDegree = a) ↔ ∃ A : Finset (Cyc s.1), ∑ c ∈ A, cycLen s.1 c = a) ∧
    ∀ Q : ℕ → Prop, (∃ q : (ZMod p)[X], Irreducible q ∧ q ∣ f ∧ Q q.natDegree) ↔ ∃ c, Q (cycLen s.1 c) := by
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2).2.2.2 hs
  have := GlobalTheory.T.natDegree_divisors_prod_distinct_monic_irreducible (ZMod p) _ _ (fun c => ⟨minpoly.monic (Algebra.IsIntegral.isIntegral (x c)),
    minpoly.irreducible (Algebra.IsIntegral.isIntegral (x c))⟩) h2
  simp only [h1, ← h3] at this
  exact this

end Good

theorem good_iff (L : GlobalTheory.GLq.LabelDatum p) (h5 : 5 ≤ p) {r : ℕ} {ι J : Type} (s : ι → SSParam p ℂ r)
    (x : ∀ v, Cyc (s v).1 → Fbar p) (f : ι → (ZMod p)[X]) (h : ∀ v, Labels L (s v) (x v) (f v))
    (χ : J → (ZMod p)ˣ →* ℂˣ) (a : ι → J → (ZMod p)ˣ)
    (ha : ∀ v j, LabelsTame L (χ j) (a v j) ∨ LabelsTame L (χ j)⁻¹ (a v j)) :
    GoodAt χ s ↔ Formalism.CyclotomicNorms.IsGood r p f a ∧ Formalism.CyclotomicNorms.IsGood r p f fun v j => (a v j)⁻¹ := by
  have inv : ∀ {χ : (ZMod p)ˣ →* ℂˣ} {a}, LabelsTame L χ a → LabelsTame L χ⁻¹ a⁻¹ := fun h =>
    ((GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L 1 one_pos).2 _ _ h).2
  have three : ∀ l : ℕ, l.Prime → ∀ v j,
      ((∀ c, ¬ CongrMod l (cycChar (s v) c) ((χ j).comp (baseNorm p r.factorial))) ∧
        ∀ c, ¬ CongrMod l (cycChar (s v) c) ((χ j)⁻¹.comp (baseNorm p r.factorial))) ↔
      (∀ z ∈ Formalism.CyclotomicNorms.rootsBar (f v), Formalism.CyclotomicNorms.primeToPart l z ≠
        Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a v j : ZMod p))) ∧
      ∀ z ∈ Formalism.CyclotomicNorms.rootsBar (f v), Formalism.CyclotomicNorms.primeToPart l z ≠
        Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) ((a v j)⁻¹ : (ZMod p)ˣ)) := by
    intro l hl v j
    rcases ha v j with H | H
    · rw [(h v).three_iff H hl, (h v).three_iff (inv H) hl]
    · have H' := inv H
      rw [inv_inv] at H'
      rw [(h v).three_iff H hl, (h v).three_iff H' hl, and_comm]
  have base := fun v => GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ (x v) (f v) (h v).2
  constructor
  · rintro ⟨g1, g2, ⟨g3, -⟩, g4, g5⟩
    have hs := fun v => (h v).regular_iff.1 (g1 v)
    have k3 := fun l hl hp v j => (three l hl v j).1 ⟨fun c => (g3 l hl hp v j c).1, fun c => (g3 l hl hp v j c).2⟩
    have key : ∀ a' : ι → J → (ZMod p)ˣ, (∀ l : ℕ, l.Prime → l ≠ p → ∀ v j, ∀ z ∈ Formalism.CyclotomicNorms.rootsBar (f v),
        Formalism.CyclotomicNorms.primeToPart l z ≠ Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a' v j : ZMod p))) →
        Formalism.CyclotomicNorms.IsGood r p f a' := fun a' H => by
      refine ⟨fun v => ⟨(h v).2.2.1, (base v).1, (base v).2.1⟩, hs,
        fun l hl hb v => ((h v).two_iff (hs v) hl).1 (g2 l hl (bb_eq p r ▸ hb) v), H, fun n h1 h2 => ?_, ?_⟩
      · by_contra hc
        push Not at hc
        exact g4 ⟨n, h1, h2, fun v => (((h v).dvd_iff (hs v)).1 n).1 (hc v)⟩
      · obtain ⟨v, hv⟩ := g5
        exact ⟨v, (((h v).dvd_iff (hs v)).2 fun d => d.Prime ∧ r < 2 * d ∧ d + 3 ≤ r).2 hv⟩
    exact ⟨key _ fun l hl hp v j => (k3 l hl hp v j).1, key _ fun l hl hp v j => (k3 l hl hp v j).2⟩
  · rintro ⟨⟨-, hs, g2, g3, g4, v₀, g5⟩, -, -, -, g3', -⟩
    have k3 := fun l hl hp v j => (three l hl v j).2 ⟨g3 l hl hp v j, g3' l hl hp v j⟩
    refine ⟨fun v => (h v).regular_iff.2 (hs v), fun l hl hb v => ((h v).two_iff (hs v) hl).2 (g2 l hl (bb_eq p r ▸ hb) v),
      ⟨fun l hl hp v j c => ⟨(k3 l hl hp v j).1 c, (k3 l hl hp v j).2 c⟩, fun v j y => ?_⟩, ?_,
      v₀, (((h v₀).dvd_iff (hs v₀)).2 fun d => d.Prime ∧ r < 2 * d ∧ d + 3 ≤ r).1 g5⟩
    · have e1 := g3 2 Nat.prime_two (by omega) v j
      have e2 := g3' 2 Nat.prime_two (by omega) v j
      rcases ha v j with H | H
      · exact ⟨(h v).ne_of H e1 y, (h v).ne_of (inv H) e2 y⟩
      · have H' := inv H
        rw [inv_inv] at H'
        exact ⟨(h v).ne_of H' e2 y, (h v).ne_of H e1 y⟩
    · rintro ⟨n, h1, h2, H⟩
      obtain ⟨v, hv⟩ := g4 n h1 h2
      exact hv ((((h v).dvd_iff (hs v)).1 n).2 (H v))

theorem Labels.series (hG : GlobalTheory.GLq.Green) {L : GlobalTheory.GLq.LabelDatum p} (h5 : 5 ≤ p) {r : ℕ} {s : SSParam p ℂ r}
    {x : Cyc s.1 → Fbar p} {f : (ZMod p)[X]} (h : Labels L s x f) (hs : Squarefree f) :
    {χ | GlobalTheory.GLq.IsIrr χ ∧ GlobalTheory.GLq.HasLabel L χ f} = {typeChar s} ∧
      GlobalTheory.GLq.eSerC L r f = centralIdem (typeChar s) := by
  obtain ⟨d1, d2, -, d3⟩ := GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2
  obtain ⟨h1, h2, h3⟩ := d3 hs
  obtain ⟨l, hl, hl', e⟩ := GlobalTheory.T.harishChandraInducedTypeChar_eq_productList p r s
  let Q : List ((ZMod p)[X] × GlobalTheory.GLq.Pc p) := l.map fun c => (minpoly (ZMod p) (x c), ⟨cycLen s.1 c, cuspOn (s.2 c)⟩)
  have hsnd : Q.map Prod.snd = l.map fun c => (⟨cycLen s.1 c, cuspOn (s.2 c)⟩ : GlobalTheory.GLq.Pc p) := by
    rw [List.map_map]; rfl
  have hfst : Q.map Prod.fst = l.map fun c => minpoly (ZMod p) (x c) := by
    rw [List.map_map]; rfl
  have hQ : ∀ q ∈ Q, GlobalTheory.GLq.IsCuspOf L q.1 q.2.2 := by
    intro q hq
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hq
    exact GlobalTheory.T.greenCuspidalChar_isCuspidalOfMinpoly_of_param hG p L h5 _ (s.2 c) (x c) (cycLen_pos _ c) (h.1 c) (h1 c)
  have hprod : f = (Q.map Prod.fst).prod := by
    classical
    rw [hfst, h3, ← List.prod_toFinset _ hl]
    congr 1
    exact (Finset.eq_univ_of_forall fun c => List.mem_toFinset.2 (hl' c)).symm
  have hdeg : GlobalTheory.GLq.degL (Q.map Prod.snd) = r := by
    rw [← (GlobalTheory.GLq.Label.prod_props L Q hQ).2.1, ← hprod, d1]
  have hnd : (Q.map Prod.snd).Nodup := by
    apply List.Nodup.of_map (GlobalTheory.GLq.Label.lab L)
    rw [← GlobalTheory.GLq.Label.map_fst_eq L h5 Q hQ, hfst]
    exact hl.map h2
  rw [← hsnd] at e
  have hip := (GlobalTheory.T.characterPairing_harishChandra_cuspidal_mackey p _ _ r hdeg hdeg (GlobalTheory.GLq.Label.cusp_snd L Q hQ) (GlobalTheory.GLq.Label.cusp_snd L Q hQ)).2 hnd
  have hirr : GlobalTheory.GLq.IsIrr (typeChar s) :=
    e ▸ (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ _).2.2.2.1 (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant p _ [] r hdeg.symm (GlobalTheory.GLq.Label.char_snd L Q hQ)).1 hip
  have hlab : GlobalTheory.GLq.HasLabel L (typeChar s) f := ⟨Q, hQ, hdeg, hprod, by rw [e, hip]; exact one_ne_zero⟩
  obtain ⟨Q', -, -, -, hset⟩ := GlobalTheory.GLq.Label.squarefree_series L h5 hG r f h.2.2.1 d1 d2 hs
  have : typeChar s = GlobalTheory.GLq.hcL (Q'.map Prod.snd) r := by
    rw [← Set.mem_singleton_iff, ← hset]; exact ⟨hirr, hlab⟩
  refine ⟨this ▸ hset, ?_⟩
  unfold GlobalTheory.GLq.eSerC
  rw [hset, finsum_mem_singleton, ← this]
  unfold GlobalTheory.GLq.zOf centralIdem
  rw [Nat.card_eq_fintype_card]
  convert rfl

end GlobalTheory.ParamLabel

end
end

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.SliceTwo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def contLeft : Submodule ℂ (Sm E a) where
  carrier := {f | Continuous f.1 ∧ ∀ γ g, f.1 (ratGL E a γ * g) = f.1 g}
  zero_mem' := ⟨continuous_const, fun _ _ => rfl⟩
  add_mem' := fun {f h} hf hh => ⟨hf.1.add hh.1, fun γ g => by
    change f.1 _ + h.1 _ = f.1 _ + h.1 _
    rw [hf.2, hh.2]⟩
  smul_mem' := fun c f hf => ⟨hf.1.const_smul c, fun γ g => by
    change c • f.1 _ = c • f.1 _
    rw [hf.2]⟩

theorem span_cpt_le_contLeft {φ : Sm E a} (hA : IsAutForm φ) :
    Submodule.span ℂ (Set.range fun k => cptRep E a k φ) ≤ contLeft E a := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, rfl⟩
  have hc := ContAut.continuous_of_isOpen_stab E a φ hA.level
  refine ⟨hc.comp (continuous_mul_const _), fun γ g => ?_⟩
  change φ.1 (ratGL E a γ * g * _) = φ.1 (g * _)
  rw [mul_assoc, hA.left]

variable {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]

def sliceLin (μ : Measure (BlockIx a r → Ad E)) [μ.IsAddHaarMeasure] {𝓕 : Set (BlockIx a r → Ad E)}
    (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) (hr : r ≤ a) (m₁ : GA E r) (t : GL (Fin a) (Af E))
    (κ : Kinf E a) : contLeft E a →ₗ[ℂ] (GA E (a - r) → ℂ) where
  toFun f := slice E μ 𝓕 hr f.1.1 m₁ t κ
  map_add' f h := by
    funext m₂
    exact integral_add (CuspidalL2GL.integrableOn_unip f.2.1 f.2.2 μ h𝓕 _) (CuspidalL2GL.integrableOn_unip h.2.1 h.2.2 μ h𝓕 _)
  map_smul' c f := by
    funext m₂
    exact integral_const_mul c _

theorem slice_kfin : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, IsAutForm φ → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (ψ : Sm E (a - r)),
      ψ.1 = GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ →
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (a - r) k ψ)) := by
  intro E _ _ _ a r hr _ _ μ 𝓕 hμ h𝓕 _ φ hA m₁ t κ ψ hψ
  set V := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) with hV
  have hfin : FiniteDimensional ℂ V := hA.kfin
  have hle := span_cpt_le_contLeft hA
  let L : V →ₗ[ℂ] (GA E (a - r) → ℂ) := sliceLin μ h𝓕 hr m₁ t κ ∘ₗ Submodule.inclusion hle
  have hR : FiniteDimensional ℂ (LinearMap.range L) := inferInstance
  set S := Submodule.span ℂ (Set.range fun k => cptRep E (a - r) k ψ)
  have hS : S.map (Sm E (a - r)).subtype ≤ LinearMap.range L := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨⟨cptRep E a (κ⁻¹ * blkK hr k * κ) φ, Submodule.subset_span ⟨_, rfl⟩⟩, ?_⟩
    funext g
    change slice E μ 𝓕 hr (cptRep E a (κ⁻¹ * blkK hr k * κ) φ).1 m₁ t κ g =
      ψ.1 (g * infGL E (a - r) (Unitary.toUnits k))
    rw [hψ, slice_mul_cpt]
    unfold slice
    congr 1
    funext x
    change φ.1 (_ * _ * _) = _
    simp only [mul_assoc]
    rfl
  have h1 : FiniteDimensional ℂ (S.map (Sm E (a - r)).subtype) := Submodule.finiteDimensional_of_le hS
  exact Module.Finite.equiv (Submodule.equivMapOfInjective (Sm E (a - r)).subtype Subtype.val_injective S).symm

end GlobalTheory.SliceTwo

end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.exists_archimedeanMatrixSmoothing_ne_zero_at_one : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (W : GL (Fin n) (Cinf E) → ℂ), Continuous W → W 1 ≠ 0 → ∃ α : (Fin n → Fin n → Cinf E) → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ tsupport α ⊆ {x | IsUnit (Matrix.of x)} ∧ smoothMatInf α W 1 ≠ 0 := by
  first | exact @GlobalTheory.JSW.MirCinf.exists_smoothMatInf_ne_zero_at_one | exact GlobalTheory.JSW.MirCinf.exists_smoothMatInf_ne_zero_at_one | (intros; apply GlobalTheory.JSW.MirCinf.exists_smoothMatInf_ne_zero_at_one <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem smoothMatInf_keeps_modGrowth : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ)
    (α : (Fin n → Fin n → Cinf E) → ℂ), Continuous α → HasCompactSupport α →
    tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W →
    IsModGrowthInf (smoothMatInf α W) :=
  isModGrowthInf_smoothMatInf

end GlobalTheory.JSW.MirCinf
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.isArchimedeanModerateGrowth_matrixSmoothingIntegral : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (α : (Fin n → Fin n → Cinf E) → ℂ), Continuous α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → IsModGrowthInf (smoothMatInf α W) := by
  first | (exact @GlobalTheory.JSW.MirCinf.isModGrowthInf_smoothMatInf) | (exact GlobalTheory.JSW.MirCinf.isModGrowthInf_smoothMatInf) | (intros; apply GlobalTheory.JSW.MirCinf.isModGrowthInf_smoothMatInf  <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.isArchimedeanRapidKernelOperator_finset_sum : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (ι : Type) [Fintype ι] (T : ι → (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ), (∀ i, IsKerOpInf (T i)) → IsKerOpInf (fun W z g => ∑ i, T i W z g) := by
  first | (exact @GlobalTheory.JSW.MirCinf.isKerOpInf_fintype_sum) | (exact GlobalTheory.JSW.MirCinf.isKerOpInf_fintype_sum) | (intros; apply GlobalTheory.JSW.MirCinf.isKerOpInf_fintype_sum  <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid


open GlobalTheory.SerreField in
theorem serreAmple_of_finiteOrder_of_separated :
    FiniteOrderSt → SeparatedSt → SerreAmpleSt := by
  intro hfin hsep K _ _ A _ _ hA L hL hamp N hN3 hNK σ hσ hpull hfix
  haveI := hσ
  obtain ⟨m, hm0, hord⟩ := hfin K A hA L hL hamp σ hσ hpull
  have hFS : ∀ n : ℕ, 1 ≤ n → Flat (Out.mulA A n).left ∧ Surjective (Out.mulA A n).left :=
    fun n hn => flat_and_surjective_of_isFinite_abelianEnd
      forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K A hA _
      (GlobalTheory.AbLaw.MulN.isMonHom_mulA A n) (GlobalTheory.MulFiniteAny.isFinite_mulA K A hA n hn)
  have hu : IsMonHom (σ.hom * (𝟙 A)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨-, hdiv⟩ := GlobalTheory.TorsionDivisible.finite_torsion_and_divisible K A hA N hNK
  obtain ⟨φ, hφ, e⟩ := hdiv (σ.hom * (𝟙 A)⁻¹) hu (fun x hx => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hfix K (𝟙 _) x hx, Category.comp_id, mul_inv_cancel])
  haveI := hφ
  have key : toRing σ.hom = 1 := by
    refine GlobalTheory.eq_one_of_pow_eq_one_of_congr_one (homRing A) N hN3 ?_ ?_ (toRing σ.hom) (toRing φ) m
      hm0 ?_ ?_
    · rintro k ⟨f, u, hu, hf⟩ hk h
      have h1 := congrArg (fun g : homRing A => g.1 (Additive.ofMul (𝟙 A))) h
      simp only [natCast_mul_apply, hf, Category.id_comp] at h1
      have h2 : u ^ k = 1 := h1
      have h3 : u = 1 := by
        obtain ⟨_, _⟩ := hFS k (by omega)
        haveI : Epi (Out.mulA A k).left := Flat.epi_of_flat_of_surjective _
        refine Over.OverMorphism.ext ((cancel_epi (Out.mulA A k).left).1 ?_)
        rw [← Over.comp_left, ← Over.comp_left, MonObj.comp_one, Out.mulA, MonObj.pow_comp,
          Category.id_comp, h2]
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · rintro q ⟨f, u, hu, hf⟩ hq h
      have h3 : u = 1 := hsep K A hA L hL hamp q hq u fun k => by
        obtain ⟨⟨g, v, hv, hg⟩, e⟩ := h k
        refine ⟨v, hv, ?_⟩
        have h1 := congrArg (fun g : homRing A => g.1 (Additive.ofMul (𝟙 A))) e
        simp only [← Nat.cast_pow, natCast_mul_apply, hf, hg, Category.id_comp] at h1
        exact h1
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · refine homRing_ext ?_
      change _ = Additive.ofMul (𝟙 A) + ((N : homRing A) * toRing φ).1 _
      rw [natCast_mul_apply, toRing_apply, toRing_apply, Category.id_comp, Category.id_comp,
        ← ofMul_pow, ← e, ← ofMul_mul, mul_comm, inv_mul_cancel_right]
    · rw [toRing_pow]
      exact homRing_ext (by rw [toRing_apply, hord, Category.id_comp]; rfl)
  have h1 := congrArg (fun g : homRing A => g.1 (Additive.ofMul (𝟙 A))) key
  simp only [toRing_apply, Category.id_comp] at h1
  exact h1

end GlobalTheory.AmpleRigid
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.prod_derivWeierstrassP_kerReps_pow_four_mul' : ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S → Even S.card → (∏ t ∈ S, L.derivWeierstrassP t) ^ 4 * α ^ 12 = (latticeCurve L).Δ ^ S.card := by
  first | exact @GlobalTheory.CMModel.prod_derivWeierstrassP_kerReps_pow_four_mul | exact GlobalTheory.CMModel.prod_derivWeierstrassP_kerReps_pow_four_mul | (intros; apply GlobalTheory.CMModel.prod_derivWeierstrassP_kerReps_pow_four_mul <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.ordFrac_functionFieldMap_of_essentiallyEtale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (E : DivOver p) (E' : DivOver (f ≫ p)) (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring), (∀ x, functionFieldMap f x ∈ E'.ring → x ∈ E.ring) → ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale → ((functionFieldMap f).restrict E.ring E'.ring h).EssFiniteType → ∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := by
  first | exact @GlobalTheory.EtaleKlt.ord_functionFieldMap_of_formallyEtale | exact GlobalTheory.EtaleKlt.ord_functionFieldMap_of_formallyEtale | (intros; apply GlobalTheory.EtaleKlt.ord_functionFieldMap_of_formallyEtale <;> assumption)
end
