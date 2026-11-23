module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle055
public import Formalism.CharacterColumnKernels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle071
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle068
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Complex.BigOperators
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

noncomputable section

namespace GlobalTheory.SupercuspUnitary

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def scal (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) : Subgroup G where
  carrier := {h | ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ y, l (ρ h y) = c * l y}
  mul_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    refine ⟨c * d, by rw [norm_mul, hc, hd, one_mul], fun y => ?_⟩
    rw [map_mul, Module.End.mul_apply, ha, hb, mul_assoc]
  one_mem' := ⟨1, by simp, fun y => by simp⟩
  inv_mem' := by
    rintro a ⟨c, hc, ha⟩
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    refine ⟨c⁻¹, by rw [norm_inv, hc, inv_one], fun y => ?_⟩
    have h := ha (ρ a⁻¹ y)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

def term (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (g : G) : ℂ :=
  l (ρ g⁻¹ v) * starRingEnd ℂ (l (ρ g⁻¹ w))

theorem term_mul {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} (v w : V) (g : G) {h : G}
    (hh : h ∈ scal ρ l) : term ρ l v w (g * h) = term ρ l v w g := by
  obtain ⟨c, hc, hl⟩ := (scal ρ l).inv_mem hh
  have h1 : c * starRingEnd ℂ c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  simp only [term, mul_inv_rev, map_mul, Module.End.mul_apply, hl]
  linear_combination (l (ρ g⁻¹ v) * starRingEnd ℂ (l (ρ g⁻¹ w))) * h1

theorem term_inv_mul (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (x g : G) :
    term ρ l v w (x⁻¹ * g) = term ρ l (ρ x v) (ρ x w) g := by
  simp only [term, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]

def qterm (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (q : G ⧸ scal ρ l) : ℂ :=
  term ρ l v w q.out

theorem qterm_mk (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (g : G) :
    qterm ρ l v w (g : G ⧸ scal ρ l) = term ρ l v w g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (scal ρ l) g
  rw [qterm, hh, term_mul v w g h.2]

theorem center_le_scal {ρ : Representation ℂ G V} (l : Module.Dual ℂ V)
    (hz : ∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v) :
    Subgroup.center G ≤ scal ρ l := fun z hz' => by
  obtain ⟨c, hc, h⟩ := hz z hz'
  exact ⟨c, hc, fun y => by rw [h, map_smul, smul_eq_mul]⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isOpen_scal {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} (hl : l ∈ smoothPart ρ.dual) :
    IsOpen (scal ρ l : Set G) := by
  refine (scal ρ l).isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset ((show IsOpen
    {g : G | ρ.dual g l = l} from hl).mem_nhds (by
      simp only [Set.mem_setOf_eq, map_one, Module.End.one_apply])) fun g hg => ⟨1, by simp, fun y => ?_⟩)
  have h1 : (ρ.dual g l) (ρ g y) = l (ρ g y) := by rw [show ρ.dual g l = l from hg]
  rw [Representation.dual_apply] at h1
  simp only [Module.Dual.transpose_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel, map_one, Module.End.one_apply] at h1
  rw [one_mul, h1]

theorem exists_finset {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} (hl : l ∈ smoothPart ρ.dual)
    (hsc : IsSupercuspidal ρ) (hz : ∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v)
    (v : V) : ∃ s : Finset (G ⧸ scal ρ l), ∀ g : G, l (ρ g⁻¹ v) ≠ 0 → (g : G ⧸ scal ρ l) ∈ s := by
  obtain ⟨C, hC, hCz⟩ := hsc.2 v l hl
  haveI := QuotientGroup.discreteTopology (isOpen_scal hl)
  have hD : ((fun c : G => ((c⁻¹ : G) : G ⧸ scal ρ l)) '' C).Finite :=
    (hC.image (by fun_prop)).finite_of_discrete
  refine ⟨hD.toFinset, fun g hg => ?_⟩
  obtain ⟨z, hz', c, hc, e⟩ := hCz g⁻¹ hg
  rw [Set.Finite.mem_toFinset]
  refine ⟨c, hc, QuotientGroup.eq.2 ?_⟩
  have h2 : (c⁻¹)⁻¹ * g = z⁻¹ := by rw [← inv_inv g, e]; group
  rw [h2]
  exact center_le_scal l hz (inv_mem hz')

end GlobalTheory.SupercuspUnitary

namespace GlobalTheory


open GlobalTheory.SupercuspUnitary in
theorem isUnitarisable_of_isSupercuspidal : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (l : Module.Dual ℂ V), l ∈ smoothPart ρ.dual →
    l ≠ 0 → ρ.IsIrreducible → IsSupercuspidal ρ →
    (∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v) → IsUnitarisable ρ := by
  intro G V _ _ _ _ _ ρ l hl hl0 hirr hsc hz
  have hfin : ∀ v w, (Function.support (qterm ρ l v w)).Finite := fun v w => by
    obtain ⟨s, hs⟩ := exists_finset hl hsc hz v
    refine s.finite_toSet.subset fun q hq => ?_
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [Function.mem_support, qterm_mk] at hq
      exact hs g (left_ne_zero_of_mul hq)

  have hadd1 : ∀ v v' w q, qterm ρ l (v + v') w q = qterm ρ l v w q + qterm ρ l v' w q := by
    intro v v' w q
    induction q using QuotientGroup.induction_on with
    | H g => simp only [qterm_mk, term, map_add (f := _), add_mul]
  have hsmul1 : ∀ (a : ℂ) v w q, qterm ρ l (a • v) w q = a * qterm ρ l v w q := by
    intro a v w q
    induction q using QuotientGroup.induction_on with
    | H g => simp only [qterm_mk, term, map_smul, smul_eq_mul, mul_assoc]
  have hadd2 : ∀ v w w' q, qterm ρ l v (w + w') q = qterm ρ l v w q + qterm ρ l v w' q := by
    intro v w w' q
    induction q using QuotientGroup.induction_on with
    | H g => simp only [qterm_mk, term, map_add (f := _), mul_add]
  have hsmul2 : ∀ (a : ℂ) v w q, qterm ρ l v (a • w) q = starRingEnd ℂ a * qterm ρ l v w q := by
    intro a v w q
    induction q using QuotientGroup.induction_on with
    | H g =>
      simp only [qterm_mk, term, map_smul, smul_eq_mul, map_mul]
      ring
  have hconj : ∀ v w q, qterm ρ l w v q = starRingEnd ℂ (qterm ρ l v w q) := by
    intro v w q
    induction q using QuotientGroup.induction_on with
    | H g =>
      simp only [qterm_mk, term, map_mul, Complex.conj_conj]
      ring
  have hinv : ∀ (x : G) v w q, qterm ρ l (ρ x v) (ρ x w) q = qterm ρ l v w (x⁻¹ • q) := by
    intro x v w q
    induction q using QuotientGroup.induction_on with
    | H g => rw [MulAction.Quotient.smul_mk, smul_eq_mul, qterm_mk, qterm_mk, term_inv_mul]
  let B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => ∑ᶠ q, qterm ρ l v w q)
    (fun v v' w => by simp only [hadd1]; exact finsum_add_distrib (hfin v w) (hfin v' w))
    (fun a v w => by simp only [hsmul1, RingHom.id_apply, smul_eq_mul, mul_finsum])
    (fun v w w' => by simp only [hadd2]; exact finsum_add_distrib (hfin v w) (hfin v w'))
    (fun a v w => by simp only [hsmul2, smul_eq_mul, mul_finsum])
  have hB : ∀ v w, B v w = ∑ᶠ q, qterm ρ l v w q := fun v w => LinearMap.mk₂'ₛₗ_apply _ _ _
  refine ⟨B, fun v w => ?_, fun v hv => ?_, fun x v w => ?_⟩
  · rw [hB, hB, map_finsum _ (hfin v w)]
    exact finsum_congr fun q => hconj v w q
  · have hex : ∃ g : G, l (ρ g v) ≠ 0 := by
      by_contra! h0
      let U : Subrepresentation ρ :=
        { toSubmodule := ⨅ g : G, LinearMap.ker (l ∘ₗ (ρ g : V →ₗ[ℂ] V))
          apply_mem_toSubmodule := fun g y hy => by
            simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hy ⊢
            intro g'
            rw [← Module.End.mul_apply, ← map_mul]
            exact hy _ }
      haveI := hirr
      rcases eq_bot_or_eq_top U with hU | hU
      · have hvU : v ∈ U.toSubmodule := by
          simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
          exact h0
        rw [hU] at hvU
        exact hv ((Submodule.mem_bot ℂ).1 hvU)
      · refine hl0 (LinearMap.ext fun y => ?_)
        have hyU : y ∈ U.toSubmodule := by rw [hU]; exact Submodule.mem_top
        simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hyU
        simpa using hyU 1
    obtain ⟨g, hg⟩ := hex
    rw [hB, finsum_eq_sum _ (hfin v v), Complex.re_sum]
    refine Finset.sum_pos' (fun q _ => ?_) ⟨((g⁻¹ : G) : G ⧸ scal ρ l), ?_, ?_⟩
    · induction q using QuotientGroup.induction_on with
      | H g' =>
        rw [qterm_mk, term, Complex.mul_conj, Complex.ofReal_re]
        exact Complex.normSq_nonneg _
    · rw [Set.Finite.mem_toFinset, Function.mem_support, qterm_mk, term, inv_inv, Complex.mul_conj]
      exact_mod_cast (Complex.normSq_pos.2 hg).ne'
    · rw [qterm_mk, term, inv_inv, Complex.mul_conj, Complex.ofReal_re]
      exact Complex.normSq_pos.2 hg
  · rw [hB, hB]
    simp only [hinv]
    exact finsum_comp_equiv (MulAction.toPerm (x⁻¹ : G) : Equiv.Perm (G ⧸ scal ρ l))

end GlobalTheory
end
end

section

namespace GlobalTheory.QuotientGenerator

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def gen (ρ : Representation ℂ G V) (x : V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g => ρ g x)
  apply_mem_toSubmodule g v hv := by
    have h : (Submodule.span ℂ (Set.range fun g => ρ g x)).map (ρ g) ≤ Submodule.span ℂ (Set.range fun g => ρ g x) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp⟩
    exact h ⟨v, hv, rfl⟩

theorem self_mem_gen (ρ : Representation ℂ G V) (x : V) : x ∈ (gen ρ x).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩

theorem eq_top_of_mem (ρ : Representation ℂ G V) (x : V) (M : Subrepresentation (gen ρ x).toRepresentation)
    (hx : (⟨x, self_mem_gen ρ x⟩ : (gen ρ x).toSubmodule) ∈ M.toSubmodule) : M.toSubmodule = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨v, hv⟩ -
  have h : (gen ρ x).toSubmodule ≤ M.toSubmodule.map (gen ρ x).toSubmodule.subtype := by
    change Submodule.span ℂ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨_, M.apply_mem_toSubmodule g hx, rfl⟩
  obtain ⟨w, hw, rfl⟩ := h hv
  exact hw

theorem exists_maximal (ρ : Representation ℂ G V) (x : V) (hx : x ≠ 0) :
    ∃ M : Subrepresentation ρ, Maximal (fun N : Subrepresentation ρ => x ∉ N.toSubmodule) M := by
  have key := zorn_le_nonempty₀ {N : Subrepresentation ρ | x ∉ N.toSubmodule} ?_ ⊥ hx
  · obtain ⟨m, -, hm⟩ := key
    exact ⟨m, hm⟩
  intro c hc hch y hy
  have hne : (Subrepresentation.toSubmodule '' c).Nonempty := ⟨_, y, hy, rfl⟩
  have hd : DirectedOn (· ≤ ·) (Subrepresentation.toSubmodule '' c) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨d, hd, h1, h2⟩ := hch.directedOn a ha b hb
    exact ⟨_, ⟨d, hd, rfl⟩, h1, h2⟩
  refine ⟨⟨sSup (Subrepresentation.toSubmodule '' c), fun g v hv => ?_⟩, fun h => ?_, fun z hz => ?_⟩
  · rw [Submodule.mem_sSup_of_directed hne hd] at hv ⊢
    obtain ⟨_, ⟨a, ha, rfl⟩, hv⟩ := hv
    exact ⟨_, ⟨a, ha, rfl⟩, a.apply_mem_toSubmodule g hv⟩
  · obtain ⟨_, ⟨a, ha, rfl⟩, hv⟩ := (Submodule.mem_sSup_of_directed hne hd).1 h
    exact hc ha hv
  · exact (le_sSup ⟨z, hz, rfl⟩ : z.toSubmodule ≤ sSup (Subrepresentation.toSubmodule '' c))

noncomputable def quot (ρ : Representation ℂ G V) (M : Subrepresentation ρ) : Representation ℂ G (V ⧸ M.toSubmodule) :=
  ρ.quotient M.toSubmodule fun g _ hv => M.apply_mem_toSubmodule g hv

theorem quot_mk (ρ : Representation ℂ G V) (M : Subrepresentation ρ) (g : G) (v : V) :
    quot ρ M g (M.toSubmodule.mkQ v) = M.toSubmodule.mkQ (ρ g v) := rfl

theorem quot_irreducible (ρ : Representation ℂ G V) (x : V)
    (hcyc : ∀ N : Subrepresentation ρ, x ∈ N.toSubmodule → N.toSubmodule = ⊤) (M : Subrepresentation ρ)
    (hM : Maximal (fun N : Subrepresentation ρ => x ∉ N.toSubmodule) M) : (quot ρ M).IsIrreducible := by
  have hx0 : M.toSubmodule.mkQ x ≠ 0 := fun h => hM.1 ((Submodule.Quotient.mk_eq_zero _).1 h)
  haveI : Nontrivial (Subrepresentation (quot ρ M)) := ⟨⟨⊥, ⊤, fun h => hx0 (by
    have h1 : M.toSubmodule.mkQ x ∈ (⊤ : Subrepresentation (quot ρ M)).toSubmodule := Submodule.mem_top
    rw [← h] at h1
    exact h1)⟩⟩
  refine ⟨fun T => ?_⟩
  let T' : Subrepresentation ρ := ⟨T.toSubmodule.comap M.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
  by_cases hx : x ∈ T'.toSubmodule
  · right
    apply Subrepresentation.toSubmodule_injective
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨v, rfl⟩ := M.toSubmodule.mkQ_surjective w
    have : v ∈ T'.toSubmodule := by rw [hcyc T' hx]; trivial
    exact this
  · left
    have hle : M ≤ T' := fun v hv => by
      change M.toSubmodule.mkQ v ∈ T.toSubmodule
      have : M.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 hv
      rw [this]
      exact zero_mem _
    have hge : T' ≤ M := hM.2 hx hle
    apply Subrepresentation.toSubmodule_injective
    refine eq_bot_iff.2 fun w hw => ?_
    obtain ⟨v, rfl⟩ := M.toSubmodule.mkQ_surjective w
    exact (Submodule.Quotient.mk_eq_zero _).2 (hge (show v ∈ T' from hw))

theorem exists_irreducible_subquotient (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V)
    (hx : x ≠ 0) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y) (y : Y),
      Representation.IsIrreducible τ ∧ GlobalTheory.SmGL.IsSubquotient τ ρ ∧ y ≠ 0 ∧
      ∀ (ι : Type) (s : Finset ι) (f : ι → G) (c : ι → ℂ) (b : ℂ),
        ∑ i ∈ s, c i • ρ (f i) x = b • x → ∑ i ∈ s, c i • τ (f i) y = b • y := by
  let x' : (gen ρ x).toSubmodule := ⟨x, self_mem_gen ρ x⟩
  have hx' : x' ≠ 0 := fun h => hx (congrArg Subtype.val h)
  obtain ⟨M, hM⟩ := exists_maximal (gen ρ x).toRepresentation x' hx'
  refine ⟨_, inferInstance, inferInstance, quot _ M, M.toSubmodule.mkQ x',
    quot_irreducible _ x' (eq_top_of_mem ρ x) M hM,
    ⟨gen ρ x, ⟨M.toSubmodule.mkQ, fun g => LinearMap.ext fun v => (quot_mk _ M g v).symm⟩, M.toSubmodule.mkQ_surjective⟩,
    fun h => hM.1 ((Submodule.Quotient.mk_eq_zero _).1 h), fun ι s f c b h => ?_⟩
  have h' : ∑ i ∈ s, c i • (gen ρ x).toRepresentation (f i) x' = b • x' := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact h
  have h2 := congrArg M.toSubmodule.mkQ h'

  rw [map_sum, map_smul] at h2
  simpa only [map_smul, quot_mk] using h2

end GlobalTheory.QuotientGenerator
end

section

open GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory.HermDualSelf

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def sesqMap (π : Representation ℂ G V) {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (C : V →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (hC : ∀ g v w, C (π g v) (σ g w) = C v w) :
    W →ₗ⋆[ℂ] smoothPart π.dual :=
  LinearMap.codRestrict (smoothPart π.dual) C.flip fun w =>
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((hσ w).mem_nhds (by simp)) fun g hg => by
      have hg' : σ g w = w := hg
      ext a
      show C (π g⁻¹ a) w = C a w
      have h := hC g (π g⁻¹ a) w
      rw [hg'] at h
      rw [← h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])

theorem sesqMap_apply (π : Representation ℂ G V) {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (C : V →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (hC : ∀ g v w, C (π g v) (σ g w) = C v w) (w : W) (a : V) :
    ((sesqMap π hσ C hC w : smoothPart π.dual) : Module.Dual ℂ V) a = C a w := rfl

theorem sesqMap_comm (π : Representation ℂ G V) {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (C : V →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (hC : ∀ g v w, C (π g v) (σ g w) = C v w) (g : G) (w : W) :
    sesqMap π hσ C hC (σ g w) = contra π g (sesqMap π hσ C hC w) := by
  refine Subtype.ext (LinearMap.ext fun a => ?_)
  rw [contra_apply, sesqMap_apply, sesqMap_apply]
  have h := hC g (π g⁻¹ a) w
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  exact h

theorem sesqMap_bijective (π : Representation ℂ G V) {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (C : V →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (hC : ∀ g v w, C (π g v) (σ g w) = C v w)
    (hinj : ∀ w, (∀ v, C v w = 0) → w = 0) (hne : ∃ w : W, w ≠ 0)
    (hirr : (contra π).IsIrreducible) : Function.Bijective (sesqMap π hσ C hC) := by
  set f := sesqMap π hσ C hC with hf
  have hi : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine hinj w fun v => ?_
    have := congrArg (fun l : smoothPart π.dual => (l : Module.Dual ℂ V) v) hw
    simpa [hf, sesqMap_apply] using this
  refine ⟨hi, ?_⟩
  let R : Subrepresentation (contra π) :=
    { toSubmodule := LinearMap.range f
      apply_mem_toSubmodule := fun g l hl => by
        obtain ⟨w, rfl⟩ := hl
        exact ⟨σ g w, sesqMap_comm π hσ C hC g w⟩ }
  rcases hirr.eq_bot_or_eq_top R with hR | hR
  · exfalso
    obtain ⟨w, hw⟩ := hne
    have : f w ∈ R.toSubmodule := ⟨w, rfl⟩
    rw [hR] at this
    exact hw (hi (by rw [(Submodule.mem_bot ℂ).1 this, map_zero]))
  · intro l
    have : l ∈ R.toSubmodule := by rw [hR]; exact Submodule.mem_top
    obtain ⟨w, hw⟩ := this
    exact ⟨w, hw⟩

end GlobalTheory.HermDualSelf
end
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.card_H0_level_rep_eq : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M]
    [Module O M] (ρ : Representation O G M) (c : O), Finite ρ.invariants →
    Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRep ρ c)) =
      Nat.card (ρ.invariants ⧸ LinearMap.range (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) := by
  first | exact @GlobalTheory.ShapeNeg.card_H0_level_rep | exact GlobalTheory.ShapeNeg.card_H0_level_rep | (intros; apply GlobalTheory.ShapeNeg.card_H0_level_rep <;> assumption)
end

section

open GlobalTheory.PMonE

namespace GlobalTheory.PMonE

theorem winPt_card (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F)
    (lam π : Fin h → F) (hπ : ∀ j, π j ≠ 0) (L U : ℕ) (M : ℕ → Matrix (Fin h) (Fin h) F)
    (hM : ∀ z, gsum (p ^ h) (L + U) M z = 0 ↔ ∀ r, rowS p ϖ lam L U (winPt p π L z) r = 0) :
    Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam L U x r = 0} =
      Nat.card {z : Fin h → F // Integral z ∧ gsum (p ^ h) (L + U) M z = 0} := by
  set φ := iterateFrobeniusEquiv F p (h * (L - 1)) with hφ
  have hpow : ∀ y : F, φ y = y ^ (p ^ h) ^ (L - 1) := fun y => by
    rw [hφ, iterateFrobeniusEquiv_def, pow_mul]
  have hN : (p ^ h) ^ (L - 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hwin : ∀ z : Fin h → F, ∀ j, winPt p π L z j = π j * φ (z j) := fun z j => by
    simp only [winPt, hpow]
  symm
  refine Nat.card_congr
    { toFun := fun z => ⟨winPt p π L z.1, fun j => ?_, (hM z.1).1 z.2.2⟩
      invFun := fun x => ⟨fun j => φ.symm (x.1 j / π j), fun j => ?_, ?_⟩
      left_inv := fun z => ?_
      right_inv := fun x => ?_ }
  · rw [hwin, norm_mul, hpow, norm_pow]
    have h0 : 0 ≤ ‖z.1 j‖ := norm_nonneg _
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ h0 (z.2.1 j))
  · have hx : ‖φ (φ.symm (x.1 j / π j))‖ ≤ 1 := by
      rw [RingEquiv.apply_symm_apply, norm_div, div_le_one (norm_pos_iff.2 (hπ j))]
      exact x.2.1 j
    rw [hpow, norm_pow] at hx
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hN).1 hx
  · rw [hM]
    have : winPt p π L (fun j => φ.symm (x.1 j / π j)) = x.1 := by
      funext j
      rw [hwin, RingEquiv.apply_symm_apply, mul_div_cancel₀ _ (hπ j)]
    rw [this]; exact x.2.2
  · apply Subtype.ext
    funext j
    simp only [hwin]
    rw [mul_div_cancel_left₀ _ (hπ j), RingEquiv.symm_apply_apply]
  · apply Subtype.ext
    funext j
    simp only [hwin]
    rw [RingEquiv.apply_symm_apply, mul_div_cancel₀ _ (hπ j)]

end GlobalTheory.PMonE
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.fractionRingQuot_killed_by_pow_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  first | exact @GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer | exact GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer | (intros; apply GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer <;> assumption)
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.fractionRingQuot_divisible_by_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ y : Formalism.NG.KO O, ϖ • y = x := by
  first | exact @GlobalTheory.KO_divisible_by_uniformiser | exact GlobalTheory.KO_divisible_by_uniformiser | (intros; apply GlobalTheory.KO_divisible_by_uniformiser <;> assumption)
end
