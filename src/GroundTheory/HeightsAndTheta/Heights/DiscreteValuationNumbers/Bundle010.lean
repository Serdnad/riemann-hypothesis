module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem weightedHomogeneousComponent_mem_span_of_isMultiHomog {R : Type*} [CommRing R] {K : Type*}
    [DecidableEq K] {ι : K → Type*} {s : MRing ι R} {c : K → ℕ} (hs : IsMultiHomog s c)
    {t : MRing ι R} (ht : t ∈ Ideal.span {s}) (b : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) b t ∈ Ideal.span {s} := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp ht

  rw [a.as_sum, Finset.sum_mul, map_sum]
  refine Ideal.sum_mem _ fun d _ => ?_
  have hd : IsWeightedHomogeneous (blockWeight ι) (monomial d (AddMonoidAlgebra.coeff a d) * s)
      (Finsupp.weight (blockWeight ι) d + c) :=
    (isWeightedHomogeneous_monomial _ d _ rfl).mul hs
  by_cases hb : b = Finsupp.weight (blockWeight ι) d + c
  · subst hb
    rw [hd.weightedHomogeneousComponent_same]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rw [hd.weightedHomogeneousComponent_ne b hb]
    exact Ideal.zero_mem _

theorem isMultiHomogIdeal_sup_span_of_form {R : Type*} [CommRing R] {K : Type*} [DecidableEq K]
    {ι : K → Type*} {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) {s : MRing ι R}
    {c : K → ℕ} (hs : IsMultiHomog s c) : IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by
  intro f hf b
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add (f := _)]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (hI y hy b))
    (Ideal.mem_sup_right (weightedHomogeneousComponent_mem_span_of_isMultiHomog hs hz b))

theorem withBot_lt_of_add_one_lt {d : WithBot ℕ∞} {N : ℕ}
    (h : d + 1 < ((N + 1 : ℕ) : WithBot ℕ∞)) : d < ((N : ℕ) : WithBot ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe x =>
    induction x using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := rfl
      rw [this] at h
      exact absurd h (not_lt.mpr (WithBot.coe_le_coe.mpr le_top))
    | coe k =>
      have h' : ((k + 1 : ℕ) : WithBot ℕ∞) < ((N + 1 : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast h
      have h'' : k + 1 < N + 1 := by exact_mod_cast h'
      have : k < N := by omega
      exact_mod_cast this

theorem CutByForm.proof (h1 : IntNumAssoc.Statement.{u}) (h2 : HilbFnCut.Statement.{u})
    (h3 : MixedDiffLinear.Statement) : CutByForm.Statement.{u} := by
  intro F _ K _ _ ι _ n G hGp hG hdim s c hs hsG bs
  have : G.IsPrime := hGp
  set J : Ideal (MRing ι F) := G ⊔ Ideal.span {s} with hJdef
  set c' : K → ℤ := fun k => (c k : ℤ) with hc'

  have hnzd : ∀ y, s * y ∈ G → y ∈ G := fun y hy => (hGp.mem_or_mem hy).resolve_left hsG
  have hH : hilbFn J = diffStep c' (hilbFn G) := by
    funext m
    exact h2 F K ι G s c hG hs hnzd m

  have hnum : intNum F G (Matrix.vecCons c' bs) = intNum F J bs := by
    obtain ⟨-, -, -, h4, h5⟩ := h3 K n bs (hilbFn G) (hilbFn G) 0 0 c'
    unfold intNum
    rw [h5, ← h4, hH]

  have hJ : IsMultiHomogIdeal J := isMultiHomogIdeal_sup_span_of_form hG hs

  have hle : G ≤ J := le_sup_left
  have hr : Ideal.Quotient.mk G s ∈ nonZeroDivisors (MRing ι F ⧸ G) :=
    mem_nonZeroDivisors_of_ne_zero fun h => hsG (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hsucc : ringKrullDim (MRing ι F ⧸ J) + 1 ≤ ringKrullDim (MRing ι F ⧸ G) :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle) hr (by
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hdimJ : ringKrullDim (MRing ι F ⧸ J) <
      ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    apply withBot_lt_of_add_one_lt
    have he : n + 1 + Fintype.card K + 1 = n + 2 + Fintype.card K := by omega
    rw [he]
    exact lt_of_le_of_lt hsucc hdim

  rw [hnum, h1 F K ι n J hJ hdimJ bs, divCycle_eq_idealCycle]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Reduction

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem map_residue_weightedHomogeneousComponent (m : K → ℕ) (f : MRing ι O) :
    MvPolynomial.map (IsLocalRing.residue O) (weightedHomogeneousComponent (blockWeight ι) m f) =
      weightedHomogeneousComponent (blockWeight ι) m (MvPolynomial.map (IsLocalRing.residue O) f) := by
  classical
  ext d
  simp only [coeff_map, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

theorem map_residue_mem_weightedHomogeneousSubmodule {m : K → ℕ} {f : MRing ι O}
    (hf : f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m) :
    MvPolynomial.map (IsLocalRing.residue O) f ∈
      weightedHomogeneousSubmodule (IsLocalRing.ResidueField O) (blockWeight ι) m := by
  rw [mem_weightedHomogeneousSubmodule] at hf ⊢
  rw [← weightedHomogeneousComponent_eq_self hf, map_residue_weightedHomogeneousComponent]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem exists_form_map_residue_eq {m : K → ℕ} {g : MRing ι (IsLocalRing.ResidueField O)}
    (hg : g ∈ weightedHomogeneousSubmodule (IsLocalRing.ResidueField O) (blockWeight ι) m) :
    ∃ f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m,
      MvPolynomial.map (IsLocalRing.residue O) f = g := by
  obtain ⟨f, rfl⟩ := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective g
  refine ⟨weightedHomogeneousComponent (blockWeight ι) m f, ?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · rw [map_residue_weightedHomogeneousComponent]
    exact weightedHomogeneousComponent_eq_self ((mem_weightedHomogeneousSubmodule _ _ _ _).1 hg)

theorem exists_eq_add_mul_of_map_residue_mem {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)}
    (hP : IsMultiHomogIdeal P) {m : K → ℕ} {f : MRing ι O}
    (hf : f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m)
    (hfP : MvPolynomial.map (IsLocalRing.residue O) f ∈ specialIdeal P) :
    ∃ p ∈ P, ∃ g ∈ weightedHomogeneousSubmodule O (blockWeight ι) m, f = p + C ϖ * g := by
  have hfh := (mem_weightedHomogeneousSubmodule _ _ _ _).1 hf
  obtain ⟨p, hp, hpf⟩ := (Ideal.mem_map_iff_of_surjective _
    (MvPolynomial.map_surjective _ IsLocalRing.residue_surjective)).1 hfP
  have hpm : weightedHomogeneousComponent (blockWeight ι) m p ∈ P := hP p hp m
  have hker : f - weightedHomogeneousComponent (blockWeight ι) m p ∈
      RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) : MRing ι O →+* _) := by
    rw [RingHom.mem_ker, map_sub, map_residue_weightedHomogeneousComponent, hpf,
      weightedHomogeneousComponent_eq_self ((mem_weightedHomogeneousSubmodule _ _ _ _).1
        (map_residue_mem_weightedHomogeneousSubmodule hf)), sub_self]
  rw [MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton, Ideal.mem_span_singleton'] at hker
  obtain ⟨g, hg⟩ := hker
  refine ⟨_, hpm, weightedHomogeneousComponent (blockWeight ι) m g, ?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · have h2 : C ϖ * weightedHomogeneousComponent (blockWeight ι) m g =
        f - weightedHomogeneousComponent (blockWeight ι) m p := by
      rw [C_mul', ← map_smul, ← C_mul', mul_comm, hg, map_sub, weightedHomogeneousComponent_eq_self hfh,
        weightedHomogeneousComponent_eq_self (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]
    rw [h2]
    ring

end Reduction

theorem SpecialPieceRank.proof (h1 : GradedPieceFree.Statement.{u}) : SpecialPieceRank.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P hP htor m
  obtain ⟨hfree, hfin⟩ := h1 O ϖ hϖ K ι P htor m
  let ρ : MRing ι O →ₐ[O] MRing ι (IsLocalRing.ResidueField O) :=
    mapAlgHom (Algebra.ofId O (IsLocalRing.ResidueField O))
  have hρ : ∀ f, ρ f = MvPolynomial.map (IsLocalRing.residue O) f := fun f => rfl
  have hle : P ≤ (specialIdeal P).comap ρ := fun x hx => by
    rw [Ideal.mem_comap, hρ]
    exact Ideal.mem_map_of_mem _ hx
  let T := Ideal.quotientMapₐ (specialIdeal P) ρ hle
  have hT : ∀ f, T (Ideal.Quotient.mk P f) =
      Ideal.Quotient.mk (specialIdeal P) (MvPolynomial.map (IsLocalRing.residue O) f) := fun f => rfl
  have hTM : ∀ y ∈ gradedPieceR P m, T y ∈ gradedPiece (specialIdeal P) m := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    exact Submodule.mem_map.2 ⟨_, map_residue_mem_weightedHomogeneousSubmodule hf, (hT f).symm⟩
  let b := Module.Free.chooseBasis O (gradedPieceR P m)
  let v : Module.Free.ChooseBasisIndex O (gradedPieceR P m) → gradedPiece (specialIdeal P) m :=
    fun i => ⟨T (b i), hTM _ (b i).2⟩
  have hv : ∀ i, ((v i : gradedPiece (specialIdeal P) m) : _) = T (b i) := fun i => rfl
  have hsmul : ∀ (c : O) (x : MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P),
      IsLocalRing.residue O c • x = c • x := fun c x => by
    rw [← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
  have hli : LinearIndependent (IsLocalRing.ResidueField O) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose c hc using fun j => IsLocalRing.residue_surjective (g j)
    let y : gradedPieceR P m := ∑ j, c j • b j
    obtain ⟨f, hf, hfy⟩ := Submodule.mem_map.1 y.2
    have hfy' : Ideal.Quotient.mk P f = (y : MRing ι O ⧸ P) := hfy
    have h0 : Ideal.Quotient.mk (specialIdeal P) (MvPolynomial.map (IsLocalRing.residue O) f) = 0 := by
      rw [← hT, hfy']
      have hg' := congrArg Subtype.val hg
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, hv] at hg'

      simp only [y, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
      rw [← hg']
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hc j, hsmul]
    obtain ⟨p, hp, g0, hg0, hfp⟩ :=
      exists_eq_add_mul_of_map_residue_mem hϖ hP hf (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    let z : gradedPieceR P m := ⟨Ideal.Quotient.mk P g0, Submodule.mem_map.2 ⟨g0, hg0, rfl⟩⟩
    have hyz : y = ϖ • z := by
      apply Subtype.ext
      rw [← hfy', hfp, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_add, map_mul,
        Submodule.coe_smul]
      show _ = ϖ • Ideal.Quotient.mk P g0
      rw [← map_mul, C_mul']
      exact map_smul (Ideal.Quotient.mkₐ O P) ϖ g0
    have hbli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hbli
    have key : ∑ j, (c j - ϖ * b.repr z j) • b j = 0 := by
      have e1 : ∑ j, (c j - ϖ * b.repr z j) • b j =
          ∑ j, c j • b j - ϖ • ∑ j, b.repr z j • b j := by
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact (sub_smul (c j) (ϖ * b.repr z j) (b j)).trans
          (congrArg (c j • b j - ·) (mul_smul ϖ (b.repr z j) (b j)))
      rw [e1, b.sum_repr]
      exact sub_eq_zero.2 hyz
    have hi := hbli _ key i
    rw [← hc i, sub_eq_zero.1 hi, map_mul, (IsLocalRing.residue_eq_zero_iff ϖ).2
      ((IsLocalRing.mem_maximalIdeal ϖ).2 (mem_nonunits_iff.2 hϖ.not_isUnit)), zero_mul]
  have hsp : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField O) (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨f, hf, rfl⟩ := exists_form_map_residue_eq hg
    let y : gradedPieceR P m := ⟨Ideal.Quotient.mk P f, Submodule.mem_map.2 ⟨f, hf, rfl⟩⟩
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun j => IsLocalRing.residue O (b.repr y j), ?_⟩
    apply Subtype.ext
    have hy := congrArg Subtype.val (b.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hy ⊢
    change _ = T (y : MRing ι O ⧸ P)

    rw [← hy, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hv, hsmul]
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Module.finrank_eq_card_chooseBasisIndex]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem IntNumAssoc.list_sum_finset_sum {α β : Type*} (l : List α) (s : Finset β)
    (f : α → β → ℤ) :
    (l.map fun a => ∑ b ∈ s, f a b).sum = ∑ b ∈ s, (l.map fun a => f a b).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib]

theorem IntNumAssoc.list_sum_ite_enat {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P] :
    (l.map fun a => if P a then (1 : ℕ∞) else 0).sum =
      ((l.map fun a => if P a then (1 : ℕ) else 0).sum : ℕ) := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : P a <;> simp [h, ih]

theorem IntNumAssoc.list_sum_ite_mul {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P]
    (c : ℤ) :
    (l.map fun a => if P a then c else 0).sum =
      ((l.map fun a => if P a then (1 : ℕ) else 0).sum : ℤ) * c := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : P a <;> simp [h, ih, add_mul]

theorem IntNumAssoc.proof (h1 : PrimeFiltration.Statement.{u})
    (h2 : IntNumOfFiltration.Statement.{u}) (h3 : MultAtPrimeAtMinimal.Statement.{u})
    (h4 : IntNumVanish.Statement.{u}) (h5 : TopDimMinimal.Statement.{u})
    (h6 : HilbDegBound.Statement.{u}) : IntNumAssoc.Statement.{u} := by
  classical
  intro F _ K _ _ ι _ n J hJ hdim bs
  obtain ⟨l, hl, hhilb, hmult⟩ := h1 F K ι J hJ
  have hdimp : ∀ p ∈ l, ringKrullDim (MRing ι F ⧸ p.1) <
      ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := fun p hp =>
    lt_of_le_of_lt (ringKrullDim_le_of_surjective (Ideal.Quotient.factor (hl p hp).2.2)
      (Ideal.Quotient.factor_surjective (hl p hp).2.2)) hdim
  have hdeg : ∀ p ∈ l, DegLT (hilbFn p.1) (n + 1) := fun p hp =>
    h6 F K ι (n + 1) p.1 (hl p hp).1 (hl p hp).2.1 (hdimp p hp)
  rw [h2 F K ι n J l hdeg hhilb bs]
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MRing ι F) J
  have hp : ∀ p ∈ l, intNum F p.1 bs =
      ∑ W ∈ hfin.toFinset, if p.1 = W then (if IsRelevant W then intNum F W bs else 0) else 0 := by
    intro p hpl
    rw [Finset.sum_ite_eq]
    by_cases hz : intNum F p.1 bs = 0
    · rw [hz]
      simp
    · have := (hl p hpl).1
      have hrel : IsRelevant p.1 := by
        by_contra hr
        exact hz (h4 F K ι n p.1 (hl p hpl).1 (hl p hpl).2.1 (Or.inl hr) bs)
      have hbig : ¬ ringKrullDim (MRing ι F ⧸ p.1) <
          ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := fun hs =>
        hz (h4 F K ι n p.1 (hl p hpl).1 (hl p hpl).2.1 (Or.inr hs) bs)
      have hJ' : ringKrullDim (MRing ι F ⧸ J) <
          ((n + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
        have e : n + Fintype.card K + 1 = n + 1 + Fintype.card K := by omega
        rw [e]
        exact hdim
      have hmin := h5 _ J p.1 (n + Fintype.card K) (hl p hpl).2.2 hJ' hbig
      rw [if_pos (hfin.mem_toFinset.mpr hmin), if_pos hrel]
  have hl2 : (l.map fun p => intNum F p.1 bs) = l.map fun p =>
      ∑ W ∈ hfin.toFinset, if p.1 = W then (if IsRelevant W then intNum F W bs else 0) else 0 :=
    List.map_congr_left hp
  rw [hl2, IntNumAssoc.list_sum_finset_sum]
  have hsupp : Function.support (fun W => idealCycle J W * intNum F W bs) ⊆
      (hfin.toFinset : Set (Ideal (MRing ι F))) := by
    intro W hW
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra hn
    apply Function.mem_support.mp hW
    unfold idealCycle
    rw [dite_eq_right (fun h => hn h.1), zero_mul]
  unfold cycEval
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun W hW => ?_
  have hWm : W ∈ J.minimalPrimes := hfin.mem_toFinset.mp hW
  have : W.IsPrime := hWm.1.1
  rw [IntNumAssoc.list_sum_ite_mul]
  unfold idealCycle
  by_cases hr : IsRelevant W
  · rw [dite_eq_left ⟨hWm, hr⟩, if_pos hr]
    have hcount : multAt J W = (l.map fun p => if p.1 = W then (1 : ℕ∞) else 0).sum := by
      rw [hmult W]
      congr 1
      apply List.map_congr_left
      intro p hpl
      have := (hl p hpl).1
      exact h3 F K ι J p.1 W (hl p hpl).2.2 hWm
    rw [hcount, IntNumAssoc.list_sum_ite_enat, ENat.toNat_natCast]
  · rw [dite_eq_right (fun h => hr h.2), if_neg hr]
    simp

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem AssociatedMultiHomogPrime.proof (h1 : MultiHomogPrimeCriterion.Statement.{u})
    (h2 : ColonMultiHomog.Statement.{u}) : AssociatedMultiHomogPrime.Statement.{u} := by
  intro F _ K _ _ ι _ J hJ hJtop
  classical

  let A : Set (Ideal (MRing ι F)) :=
    {Q | ∃ (f : MRing ι F) (s : K → ℕ), IsMultiHomog f s ∧ f ∉ J ∧ Q = J.colon {f}}
  have hne : A.Nonempty := by
    refine ⟨J.colon {1}, 1, 0, ?_, ?_, rfl⟩
    · exact isWeightedHomogeneous_one F (blockWeight ι)
    · intro h
      exact hJtop ((Ideal.eq_top_iff_one J).2 h)
  have hnoeth : IsNoetherianRing (MRing ι F) := inferInstance
  obtain ⟨Q, ⟨f, s, hf, hfJ, rfl⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian (R := MRing ι F) (M := MRing ι F)).2 hnoeth A hne
  refine ⟨f, s, hf, hfJ, ?_⟩
  apply h1 F K ι (J.colon {f}) (h2 F K ι J f s hJ hf)
  · intro htop
    apply hfJ
    have h1mem : (1 : MRing ι F) ∈ J.colon {f} := by rw [htop]; exact Submodule.mem_top
    simpa using (Submodule.mem_colon_singleton.1 h1mem)
  · intro a b sa sb _ hb hab
    by_cases hbQ : b ∈ J.colon {f}
    · exact Or.inr hbQ
    left
    have hbf : b * f ∉ J := by
      intro h
      apply hbQ
      exact Submodule.mem_colon_singleton.2 (by simpa [smul_eq_mul] using h)
    have hform : IsMultiHomog (b * f) (sb + s) := hb.mul hf
    have hle : J.colon {f} ≤ J.colon {b * f} := by
      intro x hx
      have hx' : x * f ∈ J := by simpa [smul_eq_mul] using Submodule.mem_colon_singleton.1 hx
      refine Submodule.mem_colon_singleton.2 ?_
      have : b * (x * f) ∈ J := J.mul_mem_left b hx'
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using this
    have heq : J.colon {f} = J.colon {b * f} := by
      by_contra hne'
      exact hmax _ ⟨b * f, sb + s, hform, hbf, rfl⟩ (lt_of_le_of_ne hle hne')
    rw [heq]
    refine Submodule.mem_colon_singleton.2 ?_
    have hab' : a * b * f ∈ J := by simpa [smul_eq_mul] using Submodule.mem_colon_singleton.1 hab
    simpa [smul_eq_mul, mul_assoc] using hab'

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

theorem EventualValueFacts.proof : EventualValueFacts.Statement := by
  intro K f c s
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hex : ∃ c, ∀ᶠ m in Filter.atTop, f m = c := ⟨c, h⟩
    rw [eventualValue, dite_eq_left hex]
    obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and h).exists
    exact hm1.symm.trans hm2
  · have ht : Filter.Tendsto (fun m : K → ℤ => m - s) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      refine ⟨b + s, fun a ha => ?_⟩
      simpa using sub_le_sub_right ha s
    exact ht.eventually h

end GroundTheory.Heights₂.Heights.NumbersDVR
end
