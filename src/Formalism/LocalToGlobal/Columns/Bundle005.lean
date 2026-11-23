module

public import Formalism.HarderNarasimhan.Bundle001
public import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PExtInvMuB
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.LocalToGlobal.Divisibility.CoefMod
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
import Mathlib.Tactic.Lemma
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
import Formalism.GL3MeanSquares.Bundle002
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.GlobalTheory.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.HermitianLattices.TraceIntegrality

section Places

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex E] [_root_.NumberField.IsTotallyComplex K]

theorem mean_over_places_comap (φ : E →+* K) (G : InfinitePlace E → ℝ) :
    (1 / (nPl K : ℝ)) * ∑ v : InfinitePlace K, G (v.comap φ) = (∑ w, G w) / (nPl E : ℝ) := by
  classical
  let _ : Algebra E K := φ.toAlgebra
  have hc := Formalism.L2.Geo.ExtensionFiltration.ExtInvMu.card_fiber E K
  have hn := Formalism.L2.Geo.ExtensionFiltration.ExtInvMu.nPl_ext E K
  have hs : ∑ v : InfinitePlace K, G (v.comap φ) = (Module.finrank E K : ℝ) * ∑ w, G w := by
    rw [← Finset.sum_fiberwise Finset.univ (fun v : InfinitePlace K => v.comap φ) (fun v => G (v.comap φ)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (fun v hv => congrArg G (Finset.mem_filter.1 hv).2), Finset.sum_const, nsmul_eq_mul]
    congr 2
    convert hc w
  have hK : (0 : ℝ) < (nPl K : ℝ) := by
    unfold nPl
    exact_mod_cast Fintype.card_pos
  have hE : (0 : ℝ) < (nPl E : ℝ) := by
    unfold nPl
    exact_mod_cast Fintype.card_pos
  have hn' : (nPl K : ℝ) = (Module.finrank E K : ℝ) * (nPl E : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < (Module.finrank E K : ℝ) := by
    by_contra h
    have h0 : (Module.finrank E K : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [h0, zero_mul] at hn'
    exact hK.ne' hn'
  rw [hs, hn']
  field_simp

end Places

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
end
end

section

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section Paths

theorem double_sum_eq_of_filter_card {α M : Type} [DecidableEq α] [AddCommMonoid M] (A A' : Finset α) (B B' : α → Finset α) (φ : α → M)
    (h : ∀ f, (A.filter fun e => f ∈ B e).card = (A'.filter fun e => f ∈ B' e).card) :
    ∑ e ∈ A, ∑ f ∈ B e, φ f = ∑ e ∈ A', ∑ f ∈ B' e, φ f := by

  have key : ∀ (A : Finset α) (B : α → Finset α) (U : Finset α), (∀ e ∈ A, B e ⊆ U) →
      ∑ e ∈ A, ∑ f ∈ B e, φ f = ∑ f ∈ U, (A.filter fun e => f ∈ B e).card • φ f := by
    intro A B U hU
    rw [Finset.sum_comm' (t' := U) (s' := fun f => A.filter fun e => f ∈ B e)]
    · simp only [Finset.sum_const]
    · intro e f
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨he, hf⟩
        exact ⟨⟨he, hf⟩, hU e he hf⟩
      · rintro ⟨⟨he, hf⟩, -⟩
        exact ⟨he, hf⟩
  set U := A.biUnion B ∪ A'.biUnion B'
  rw [key A B U (fun e he => (Finset.subset_biUnion_of_mem B he).trans Finset.subset_union_left),
    key A' B' U (fun e he => (Finset.subset_biUnion_of_mem B' he).trans Finset.subset_union_right)]
  exact Finset.sum_congr rfl fun f _ => by rw [h f]

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}


open Classical in
def decorationPathCount (P Q : Ideal (𝓞 E)) (i j : ℕ) (d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : ℕ :=
  ((d.heckeNb P i).filter fun e => f ∈ e.heckeNb Q j).card

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

open Classical in
theorem card_filter_neighbours_eq_paths (c : DecoPts S E n ST SG) (P Q : Ideal (𝓞 E)) (i j : ℕ) (d f : S.D) :
    ((c.nb P i d).filter fun e => f ∈ c.nb Q j e).card = decorationPathCount P Q i j (c.pts d) (c.pts f) := by
  show ((((c.pts d).heckeNb P i).map c.pts.symm.toEmbedding).filter fun e => f ∈ c.nb Q j e).card = _
  rw [Finset.filter_map, Finset.card_map]
  unfold decorationPathCount
  congr 1
  ext x
  simp only [Finset.mem_filter, Function.comp_apply, Equiv.toEmbedding_apply, DecoPts.mem_nb,
    Equiv.apply_symm_apply]

theorem heckeOperators_commute_of_paths (c : DecoPts S E n ST SG) (P Q : Ideal (𝓞 E)) (i j : ℕ)
    (h : ∀ d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG), decorationPathCount P Q i j d f = decorationPathCount Q P j i d f) :
    Commute (heckeD c P i).op (heckeD c Q j).op := by
  classical
  refine LinearMap.ext fun φ => Subtype.ext (funext fun d => ?_)
  show (((heckeD c P i).op ((heckeD c Q j).op φ) : S.EqFun) : S.D → S.V) d =
    (((heckeD c Q j).op ((heckeD c P i).op φ) : S.EqFun) : S.D → S.V) d
  simp only [heckeD, LocOp.ofNbr_op_apply, LinearMap.id_apply]
  refine double_sum_eq_of_filter_card _ _ _ _ _ fun f => ?_
  rw [card_filter_neighbours_eq_paths, card_filter_neighbours_eq_paths, h]

def DecorationPathSymmetry (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ P Q : HeightOneSpectrum (𝓞 E), conjPrime₂ P ≠ P → conjPrime₂ Q ≠ Q →
    (∀ R : ST, R.1 ≠ P ∧ R.1 ≠ conjPrime₂ P) → (∀ w : SG, w.1 ≠ P ∧ w.1 ≠ conjPrime₂ P) →
    (∀ R : ST, R.1 ≠ Q ∧ R.1 ≠ conjPrime₂ Q) → (∀ w : SG, w.1 ≠ Q ∧ w.1 ≠ conjPrime₂ Q) →
    ∀ (i j : ℕ) (d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)), decorationPathCount P.asIdeal Q.asIdeal i j d f = decorationPathCount Q.asIdeal P.asIdeal j i d f

private lemma levOff_conjP_ne_and_ne_places {S0 : Set (HeightOneSpectrum (𝓞 E))} (x : LevOff ST SG S0) :
    conjPrime₂ x.1 ≠ x.1 ∧ (∀ R : ST, R.1 ≠ x.1 ∧ R.1 ≠ conjPrime₂ x.1) ∧ (∀ w : SG, w.1 ≠ x.1 ∧ w.1 ≠ conjPrime₂ x.1) := by
  obtain ⟨P, h1, h2, h3⟩ := x
  rw [conjIdeal_asIdeal] at h1 h3
  refine ⟨fun h => h1 (congrArg HeightOneSpectrum.asIdeal h), fun R => ⟨?_, ?_⟩, fun w => ⟨?_, ?_⟩⟩
  · intro h
    have h' : R.1 = P := h
    apply h2
    rw [← h']
    exact Or.inl (Or.inr (Finset.mem_coe.2 R.2))
  · intro h
    exact h3 R.1 (Or.inl (Or.inr (Finset.mem_coe.2 R.2))) (congrArg HeightOneSpectrum.asIdeal h)
  · intro h
    have h' : w.1 = P := h
    apply h2
    rw [← h']
    exact Or.inr (Finset.mem_coe.2 w.2)
  · intro h
    exact h3 w.1 (Or.inr (Finset.mem_coe.2 w.2)) (congrArg HeightOneSpectrum.asIdeal h)

theorem heckeComm_of_paths (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) (h : DecorationPathSymmetry E n ST SG) :
    HeckeComm c S0 := by
  intro x y
  obtain ⟨hx1, hx2, hx3⟩ := levOff_conjP_ne_and_ne_places x.1
  obtain ⟨hy1, hy2, hy3⟩ := levOff_conjP_ne_and_ne_places y.1
  exact heckeOperators_commute_of_paths c _ _ _ _ fun d f => h x.1.1 y.1.1 hx1 hy1 hx2 hx3 hy2 hy3 x.2 y.2 d f

end Paths

end Formalism.L2.Col
end
end

section

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section InertNbr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

abbrev inType (P : Ideal (𝓞 E)) (s : List ℕ) : Type := ∀ i : Fin s.length, 𝓞 E ⧸ P ^ s.get i

def IsInertNbr (P : Ideal (𝓞 E)) (s : List ℕ) (N N' : Submodule (𝓞 E) (Sp E n)) : Prop :=
  Nonempty ((N ⧸ (N' ⊓ N).comap N.subtype) ≃ₗ[𝓞 E] inType P s) ∧
    Nonempty ((N' ⧸ (N ⊓ N').comap N'.subtype) ≃ₗ[𝓞 E] inType P s)

theorem IsInertNbr.symm {P : Ideal (𝓞 E)} {s : List ℕ} {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : IsInertNbr P s N N') : IsInertNbr P s N' N := ⟨h.2, h.1⟩

theorem IsInertNbr.gmap {P : Ideal (𝓞 E)} {s : List ℕ} {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : IsInertNbr P s N N') (g : Sp E n ≃ₗ[E] Sp E n) : IsInertNbr P s (gmap g N) (gmap g N') := by
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := h
  exact ⟨⟨(quotMapEquiv (g.restrictScalars (𝓞 E)) N' N).symm.trans e1⟩,
    ⟨(quotMapEquiv (g.restrictScalars (𝓞 E)) N N').symm.trans e2⟩⟩

theorem inType_smul_eq_zero {P : Ideal (𝓞 E)} {s : List ℕ} {r : 𝓞 E} (hr : r ∈ P ^ s.sum) (x : inType P s) :
    r • x = 0 := by
  funext i
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (x i)
  rw [Pi.smul_apply, ← hy, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (List.le_sum_of_mem (List.get_mem s i)) hr)

theorem IsInertNbr.smul_le {P : Ideal (𝓞 E)} {s : List ℕ} {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : IsInertNbr P s N N') : (P ^ s.sum) • N ≤ N' ∧ (P ^ s.sum) • N' ≤ N := by
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := h
  constructor
  · rw [Submodule.smul_le]
    intro r hr x hx
    have h0 : e1 (Submodule.Quotient.mk (r • (⟨x, hx⟩ : N))) = 0 := by
      rw [Submodule.Quotient.mk_smul, map_smul]
      exact inType_smul_eq_zero hr _
    rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at h0
    exact (Submodule.mem_inf.1 (Submodule.mem_comap.1 h0)).1
  · rw [Submodule.smul_le]
    intro r hr x hx
    have h0 : e2 (Submodule.Quotient.mk (r • (⟨x, hx⟩ : N'))) = 0 := by
      rw [Submodule.Quotient.mk_smul, map_smul]
      exact inType_smul_eq_zero hr _
    rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at h0
    exact (Submodule.mem_inf.1 (Submodule.mem_comap.1 h0)).1

variable {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.inertSet (P : Ideal (𝓞 E)) (s : List ℕ) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : Set (DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :=
  {d' | IsInertNbr P s d.1.N d'.1.N ∧ d'.1.f = d.1.f ∧ d'.1.be = d.1.be}


open Classical in
def DecoSet.inertNb (P : Ideal (𝓞 E)) (s : List ℕ) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : Finset (DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :=
  if h : (d.inertSet P s).Finite then h.toFinset else ∅

theorem DecoSet.smul_mem_inertSet {P : Ideal (𝓞 E)} {s : List ℕ} (a : UF E n × GLG (E := E) (n := n) (SG := SG))
    {d e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} (h : e ∈ d.inertSet P s) : a • e ∈ (a • d).inertSet P s := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [DecoSet.smul_val, DecoSet.smul_val]
    exact h1.gmap _
  · rw [DecoSet.smul_val, DecoSet.smul_val]
    simp only [Deco.act, h2]
  · rw [DecoSet.smul_val, DecoSet.smul_val]
    simp only [Deco.act, h3]

theorem DecoSet.smul_mem_inertSet_iff {P : Ideal (𝓞 E)} {s : List ℕ} (a : UF E n × GLG (E := E) (n := n) (SG := SG))
    {d e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} : a • e ∈ (a • d).inertSet P s ↔ e ∈ d.inertSet P s := by
  constructor
  · intro h
    have := DecoSet.smul_mem_inertSet a⁻¹ h
    simpa only [inv_smul_smul] using this
  · exact DecoSet.smul_mem_inertSet a

theorem DecoSet.inertSet_smul (P : Ideal (𝓞 E)) (s : List ℕ) (a : UF E n × GLG (E := E) (n := n) (SG := SG))
    (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : (a • d).inertSet P s = (fun e => a • e) '' d.inertSet P s := by
  ext e
  constructor
  · intro he
    refine ⟨a⁻¹ • e, ?_, smul_inv_smul a e⟩
    rw [← DecoSet.smul_mem_inertSet_iff a, smul_inv_smul]
    exact he
  · rintro ⟨e', he', rfl⟩
    exact DecoSet.smul_mem_inertSet a he'

theorem DecoSet.smul_mem_inertNb_iff {P : Ideal (𝓞 E)} {s : List ℕ} (a : UF E n × GLG (E := E) (n := n) (SG := SG))
    {d e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} : a • e ∈ (a • d).inertNb P s ↔ e ∈ d.inertNb P s := by
  classical
  unfold DecoSet.inertNb
  have hfin : ((a • d).inertSet P s).Finite ↔ (d.inertSet P s).Finite := by
    rw [DecoSet.inertSet_smul]
    exact Set.finite_image_iff (MulAction.injective a).injOn
  by_cases h : (d.inertSet P s).Finite
  · rw [dite_eq_left (hfin.2 h), dite_eq_left h, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact DecoSet.smul_mem_inertSet_iff a
  · rw [dite_eq_right (mt hfin.1 h), dite_eq_right h]
    simp

end InertNbr

section HeckeI

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

def DecoPts.nbI (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (s : List ℕ) (d : S.D) : Finset S.D :=
  ((c.pts d).inertNb P s).map c.pts.symm.toEmbedding

theorem DecoPts.mem_nbI (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (s : List ℕ) (d e : S.D) :
    e ∈ c.nbI P s d ↔ c.pts e ∈ (c.pts d).inertNb P s := by
  unfold DecoPts.nbI
  rw [Finset.mem_map_equiv, Equiv.symm_symm]

def heckeI (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (s : List ℕ) : LocOp S S :=
  LocOp.ofNbr (MonoidHom.id S.G) (c.nbI P s) LinearMap.id
    (by
      intro g d' d
      rw [c.mem_nbI, c.mem_nbI, MonoidHom.id_apply, c.pts_smul, c.pts_smul]
      exact DecoSet.smul_mem_inertNb_iff (c.hom g))
    (by intro g x; rfl)

theorem heckeI_op_apply (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (s : List ℕ) (φ : S.EqFun) (d : S.D) :
    (((heckeI c P s).op φ : S.EqFun) : S.D → S.V) d = ∑ e ∈ c.nbI P s d, (φ : S.D → S.V) e := by
  simp only [heckeI, LocOp.ofNbr_op_apply, LinearMap.id_apply]

def InertOff (S0 : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  {P : HeightOneSpectrum (𝓞 E) // conjPrime₂ P = P ∧ (∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal) ∧ P ∉ S0}

def InertOff.q {S0 : Set (HeightOneSpectrum (𝓞 E))} (P : InertOff S0) : ℕ := Nat.card (𝓞 E ⧸ P.1.asIdeal)

abbrev LevOffI (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  InertOff (S0 ∪ (↑ST : Set (HeightOneSpectrum (𝓞 E))) ∪ (↑SG : Set (HeightOneSpectrum (𝓞 E))))

def heckeFamI (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) :
    LevOffI ST SG S0 × List ℕ → End K S.EqFun := fun x => (heckeI c x.1.1.asIdeal x.2).op


variable (ST SG) in
abbrev HeckeIx (S0 : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  (LevOff ST SG S0 × ℕ) ⊕ (LevOffI ST SG S0 × List ℕ)

def heckeFamAll (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) :
    HeckeIx ST SG S0 → End K S.EqFun :=
  Sum.elim (heckeFam c S0) (heckeFamI c S0)

def HeckeCommAll (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  PairComm (heckeFamAll c S0)

def HeckeFieldsInI (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  SplitOver (heckeFamI c S0)

def HeckeFieldsInAll (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  SplitOver (heckeFamAll c S0)

end HeckeI

section Cartan

def CartanInert (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), conjPrime₂ P = P → (∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal) →
    ∀ N N' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → Submodule.IsLattice E N' →
      IsUnimodular (hStd E n) N → IsUnimodular (hStd E n) N' →
      (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q N N') →
      ∃ g ∈ UF E n, SameAt P (gmap g N) N' ∧ SameAt P (gmap g N') N

end Cartan

end Formalism.L2.Col
end
end

section

noncomputable section

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

namespace Formalism.L2.Col

section Map

variable {K K' : Type} [Field K] [Field K'] (s : K →+* K')

theorem mti_map_colAddGen {r n : ℕ} (l j : Fin n) (P : MvPolynomial (Fin r × Fin n) K) :
    map s (Formalism.GradedWeylDivisibility.colAddGen K l j P) = Formalism.GradedWeylDivisibility.colAddGen K' l j (map s P) := by
  have h : (map s).comp (Formalism.GradedWeylDivisibility.colAddGen K (r := r) l j).toRingHom =
      (Formalism.GradedWeylDivisibility.colAddGen K' (r := r) l j).toRingHom.comp (map s) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Formalism.GradedWeylDivisibility.colAddGen]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_X, Formalism.GradedWeylDivisibility.colAddGen, aeval_X]
      split_ifs <;> simp
  exact congrArg (fun φ : MvPolynomial (Fin r × Fin n) K →+* MvPolynomial (Option (Fin r × Fin n)) K' => φ P) h

theorem mti_map_rename_some {r n : ℕ} (P : MvPolynomial (Fin r × Fin n) K) :
    map s (rename (some : Fin r × Fin n → Option (Fin r × Fin n)) P) = rename some (map s P) :=
  map_rename s _ P

theorem mti_map_weighted {r n : ℕ} (ν : Fin n → ℕ) {P : MvPolynomial (Fin r × Fin n) K}
    (hP : P ∈ weightedHomogeneousSubmodule K (Formalism.GradedWeylDivisibility.colW r n) ν) :
    map s P ∈ weightedHomogeneousSubmodule K' (Formalism.GradedWeylDivisibility.colW r n) ν := by
  rw [mem_weightedHomogeneousSubmodule] at hP ⊢
  intro m hm
  rw [coeff_map] at hm
  apply hP
  intro h0
  rw [h0, map_zero] at hm
  exact hm rfl

theorem mti_map_dualWeyl {r n : ℕ} (ν : Fin n → ℕ) {P : MvPolynomial (Fin r × Fin n) K}
    (hP : P ∈ Formalism.GradedWeylDivisibility.dualWeyl K r n ν) : map s P ∈ Formalism.GradedWeylDivisibility.dualWeyl K' r n ν := by
  rw [Formalism.GradedWeylDivisibility.dualWeyl, Submodule.mem_inf] at hP ⊢
  refine ⟨mti_map_weighted s ν hP.1, ?_⟩
  have h2 := hP.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero] at h2 ⊢
  intro l j hlj
  rw [← mti_map_colAddGen, ← mti_map_rename_some, h2 l j hlj]

end Map

section VVMap

variable {K K' : Type} [Field K] [Field K'] (s : K →+* K') {ι : Type} [Fintype ι] {n : ℕ}

theorem mti_map_ten (F : ι → MvPolynomial (Fin n × Fin n) K) :
    map s (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (F τ)) = ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K' τ (map s (F τ)) := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact map_rename s _ (F τ)

theorem mti_map_mem_VV (lam : ι → DomWeight n) {F : Pol K ι n} (hF : F ∈ VV K lam) : map s F ∈ VV K' lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF ⊢
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨G, hG, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun τ => map s (G τ), fun τ => ?_, mti_map_ten s G⟩
    exact mti_map_dualWeyl s _ (hG τ)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

end VVMap

section RhoMap

variable {K K' : Type} [Field K] [Field K'] (s : K →+* K') {ι : Type} [Fintype ι] {n : ℕ}

end RhoMap

end Formalism.L2.Col
end
end
