module

public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotShiftPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle002
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle003
public import ReciprocityTheory.SemistableReduction.Bundle015
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH

variable {K₁ : Type} [Field K₁] [NumberField K₁] (w : HeightOneSpectrum (𝓞 K₁))

instance isFractionRing_Rv : IsFractionRing (Rv K₁ w) K₁ :=
  (inferInstance : IsFractionRing (w.valuationSubringAtPrime K₁) K₁)

variable {U : Type} [AddCommGroup U] [Module K₁ U] [FiniteDimensional K₁ U]
  [Module (Rv K₁ w) U] [IsScalarTower (Rv K₁ w) K₁ U]

theorem local_len (hL : QuotLocalStatement) (P : Submodule K₁ U) (Mw : Submodule (Rv K₁ w) U)
    (hMw : Mw.FG) (hMspan : Submodule.span K₁ (Mw : Set U) = ⊤) {ρ : ℕ}
    (hρ : finrank K₁ (U ⧸ P) = ρ) (e : Fin ρ → U) (he : ∀ j, e j ∈ Mw)
    (c : Fin ρ → U →ₗ[K₁] K₁) (hcP : ∀ i, ∀ x ∈ P, c i x = 0) (s : Fin ρ → ℝ) (β : ℝ)
    (hint : ∀ i, ∀ y ∈ Mw, c i y ≠ 0 → -β ≤ (ordAt w (c i y) : ℝ) + s i)
    (hdet : (Matrix.of fun i j => c i (e j)).det ≠ 0) :
    ∃ n : ℕ, Module.length (Rv K₁ w) (Mw ⧸ ((Submodule.span (Rv K₁ w) (P : Set U) ⊓ Mw) ⊔
        Submodule.span (Rv K₁ w) (Set.range e)).comap Mw.subtype) = n ∧
      (n : ℝ) ≤ (ordAt w (Matrix.of fun i j => c i (e j)).det : ℝ) + ∑ i, s i + ρ * β := by
  classical
  set N : Submodule (Rv K₁ w) Mw := (Submodule.span (Rv K₁ w) (P : Set U) ⊓ Mw).comap Mw.subtype
    with hN
  set T : Submodule (Rv K₁ w) Mw := ((Submodule.span (Rv K₁ w) (P : Set U) ⊓ Mw) ⊔
      Submodule.span (Rv K₁ w) (Set.range e)).comap Mw.subtype with hT

  have hspanP : ∀ x : U, x ∈ Submodule.span (Rv K₁ w) (P : Set U) → x ∈ P := fun x hx =>
    (Submodule.span_le (p := P.restrictScalars (Rv K₁ w))).mpr (fun y hy => hy) hx
  have hmemN : ∀ y : Mw, y ∈ N ↔ (y : U) ∈ P := by
    intro y
    constructor
    · intro hy
      exact hspanP _ (Submodule.mem_inf.mp (Submodule.mem_comap.mp hy)).1
    · intro hy
      exact Submodule.mem_comap.mpr (Submodule.mem_inf.mpr ⟨Submodule.subset_span hy, y.2⟩)

  let cQ : Fin ρ → (Mw ⧸ N) →ₗ[Rv K₁ w] K₁ := fun i =>
    N.liftQ (((c i).restrictScalars (Rv K₁ w)).comp Mw.subtype) (by
      intro y hy
      rw [LinearMap.mem_ker]
      exact hcP i _ ((hmemN y).mp hy))
  have hc' : ∀ i (q : Mw ⧸ N), cQ i q ≠ 0 → -β ≤ (ordAt w (cQ i q) : ℝ) + s i := by
    intro i q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N q
    exact hint i y y.2 hq
  let e' : Fin ρ → Mw := fun j => ⟨e j, he j⟩
  let th : Fin ρ → Mw ⧸ N := fun j => N.mkQ (e' j)
  have hdet' : (Matrix.of fun i j => cQ i (th j)).det ≠ 0 := hdet

  let ι : (Mw ⧸ N) →ₗ[Rv K₁ w] (U ⧸ P) :=
    N.liftQ ((P.mkQ.restrictScalars (Rv K₁ w)).comp Mw.subtype) (by
      intro y hy
      rw [LinearMap.mem_ker]
      exact (Submodule.Quotient.mk_eq_zero P (x := (y : U))).mpr ((hmemN y).mp hy))
  have hι : Function.Injective ι := by
    refine (injective_iff_map_eq_zero ι).mpr ?_
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N q
    exact (Submodule.Quotient.mk_eq_zero N (x := y)).mpr
      ((hmemN y).mpr ((Submodule.Quotient.mk_eq_zero P (x := (y : U))).mp hq))
  haveI : Module.Finite (Rv K₁ w) Mw := Module.Finite.iff_fg.mpr hMw
  haveI : NoZeroSMulDivisors (Rv K₁ w) (Mw ⧸ N) := by
    refine ⟨fun {r q} hrq => ?_⟩
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    apply hι
    rw [map_zero]
    have h1 : r • ι q = 0 := by rw [← map_smul, hrq, map_zero]
    have hr' : (r • (1 : K₁)) ≠ 0 := by
      rw [Subring.smul_def, smul_eq_mul, mul_one]
      exact fun h => hr (Subtype.ext h)
    have h2 : (r • (1 : K₁)) • ι q = 0 := by rw [smul_one_smul]; exact h1
    exact (smul_eq_zero.mp h2).resolve_left hr'
  haveI : Module.Free (Rv K₁ w) (Mw ⧸ N) := Module.free_of_finite_type_torsion_free'

  have hthli : LinearIndependent (Rv K₁ w) th := by
    apply LinearIndependent.of_comp (LinearMap.pi fun i => cQ i)
    have hK : LinearIndependent K₁ (fun j => Matrix.transpose (Matrix.of fun i j => c i (e j)) j) :=
      Matrix.linearIndependent_cols_of_isUnit
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
    exact (LinearIndependent.iff_fractionRing (Rv K₁ w) K₁).mpr hK
  have hle1 : ρ ≤ Module.finrank (Rv K₁ w) (Mw ⧸ N) := by
    simpa using hthli.fintype_card_le_finrank
  have hle2 : Module.finrank (Rv K₁ w) (Mw ⧸ N) ≤ ρ := by
    let b := Module.Free.chooseBasis (Rv K₁ w) (Mw ⧸ N)
    have hli : LinearIndependent (Rv K₁ w) (ι ∘ b) :=
      b.linearIndependent.map' ι (LinearMap.ker_eq_bot.mpr hι)
    have hliK : LinearIndependent K₁ (ι ∘ b) :=
      (LinearIndependent.iff_fractionRing (Rv K₁ w) K₁).mp hli
    rw [Module.finrank_eq_card_chooseBasisIndex, ← hρ]
    exact hliK.fintype_card_le_finrank
  have hb : Nonempty (Module.Basis (Fin ρ) (Rv K₁ w) (Mw ⧸ N)) :=
    ⟨Module.finBasisOfFinrankEq _ _ (le_antisymm hle2 hle1)⟩
  obtain ⟨n, hn, hle⟩ := exists_length_quotient_span_le hL w (Mw ⧸ N) ρ hb cQ s β th hc' hdet'

  have hmapE : (Submodule.span (Rv K₁ w) (Set.range e')).map Mw.subtype =
      Submodule.span (Rv K₁ w) (Set.range e) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hmapTh : (Submodule.span (Rv K₁ w) (Set.range e')).map N.mkQ =
      Submodule.span (Rv K₁ w) (Set.range th) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hNT : N ≤ T := Submodule.comap_mono le_sup_left
  have hspan : T.map N.mkQ = Submodule.span (Rv K₁ w) (Set.range th) := by
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap]
      intro y hy
      rw [Submodule.mem_comap]
      have hy' : (y : U) ∈ (Submodule.span (Rv K₁ w) (P : Set U) ⊓ Mw) ⊔
          Submodule.span (Rv K₁ w) (Set.range e) := hy
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy'
      rw [← hmapE] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      have hyab : y = ⟨a, ha.2⟩ + b' := Subtype.ext (by simpa using hab.symm)
      have h0 : N.mkQ ⟨a, ha.2⟩ = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact (hmemN _).mpr (hspanP a ha.1)
      rw [hyab, map_add (f := _), h0, zero_add, ← hmapTh]
      exact Submodule.mem_map_of_mem hb'
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨e' j, Submodule.mem_comap.mpr
        (Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)), rfl⟩
  let E : ((Mw ⧸ N) ⧸ Submodule.span (Rv K₁ w) (Set.range th)) ≃ₗ[Rv K₁ w] (Mw ⧸ T) :=
    (Submodule.quotEquivOfEq _ _ hspan.symm).trans (Submodule.quotientQuotientEquivQuotient N T hNT)
  exact ⟨n, (LinearEquiv.length_eq E).symm.trans hn, hle⟩

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction
end

section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct
open TensorProduct

theorem exists_finset_inf_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Set (Submodule K V)) : ∃ t : Finset (Submodule K V), (t : Set _) ⊆ S ∧ ∀ N ∈ S, t.inf id ≤ N := by
  classical
  let T : Set (Submodule K V) :=
    {N | ∃ t : Finset (Submodule K V), (t : Set (Submodule K V)) ⊆ S ∧ N = t.inf id}
  have hT : T.Nonempty := ⟨⊤, ∅, by simp, by simp⟩
  obtain ⟨N0, hN0, hmin⟩ := (wellFounded_lt (α := Submodule K V)).has_min T hT
  obtain ⟨t0, ht0S, rfl⟩ := hN0
  refine ⟨t0, ht0S, fun N hN => ?_⟩
  have hmem : (insert N t0).inf id ∈ T :=
    ⟨insert N t0, by
      rw [Finset.coe_insert, Set.insert_subset_iff]
      exact ⟨hN, ht0S⟩, rfl⟩
  have hle : (insert N t0).inf id ≤ t0.inf id := Finset.inf_mono (Finset.subset_insert _ _)
  have heq : (insert N t0).inf id = t0.inf id := eq_of_le_of_not_lt hle (hmin _ hmem)
  rw [Finset.inf_insert] at heq
  calc t0.inf id = N ⊓ t0.inf id := heq.symm
    _ ≤ N := inf_le_left

theorem kerCore_holds : KerCoreStatement := by
  intro K _ _ V _ _ _ W Fam hkill hdet henl
  classical

  let S : Set (Submodule K V) := {N | ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁)
    (f : V →ₗ[K] K₁), Fam K₁ f ∧ N = LinearMap.ker f}
  obtain ⟨t, htS, htinf⟩ := exists_finset_inf_eq S
  have hmem : ∀ N : t, ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁)
      (f : V →ₗ[K] K₁), Fam K₁ f ∧ (N : Submodule K V) = LinearMap.ker f := fun N => htS N.2
  choose Ki fKi nfKi aKi fi hfam hNker using hmem
  have hWinf : t.inf id = W := by
    apply le_antisymm
    · intro v hv
      apply hdet v
      intro K₁ _ _ _ f hf
      have := htinf (LinearMap.ker f) ⟨K₁, inferInstance, inferInstance, inferInstance, f, hf, rfl⟩ hv
      exact this
    · refine Finset.le_inf fun N hN => ?_
      have h1 := hNker ⟨N, hN⟩
      simp only at h1
      show W ≤ N
      rw [h1]
      exact hkill _ _ (hfam ⟨N, hN⟩)
  have hWmem : ∀ v, v ∈ W ↔ ∀ N : t, fi N v = 0 := by
    intro v
    rw [← hWinf, Finset.inf_eq_iInf]
    simp only [Submodule.mem_iInf, id]
    constructor
    · intro hv N
      have h1 := hv N N.2
      rw [hNker N] at h1
      exact h1
    · intro h N hN
      have h1 := hNker ⟨N, hN⟩
      simp only at h1
      rw [h1]
      exact h ⟨N, hN⟩

  let Ω := AlgebraicClosure K
  have hfinKi : ∀ N, FiniteDimensional K (Ki N) := fun N =>
    Module.Finite.of_restrictScalars_finite ℚ K (Ki N)
  let ιi : ∀ N : t, Ki N →ₐ[K] Ω := fun N =>
    have := hfinKi N
    IsAlgClosed.lift
  let M : IntermediateField K Ω := ⨆ N : t, (ιi N).fieldRange
  have hMfin : FiniteDimensional K M := by
    have : ∀ N : t, FiniteDimensional K (ιi N).fieldRange := fun N =>
      haveI := hfinKi N
      (AlgHom.equivFieldRange (ιi N)).toLinearEquiv.finiteDimensional
    exact IntermediateField.finiteDimensional_iSup_of_finite
  let L : IntermediateField K Ω := IntermediateField.normalClosure K M Ω
  have hLfin : FiniteDimensional K L := inferInstance
  have hLgal : IsGalois K L := inferInstance
  have hML : M ≤ L := IntermediateField.le_normalClosure M
  have hQL : FiniteDimensional ℚ L := Module.Finite.trans K L
  have hnfL : NumberField L := ⟨⟩

  have hrange : ∀ N (x : Ki N), ιi N x ∈ L := fun N x =>
    hML (le_iSup (fun N : t => (ιi N).fieldRange) N ⟨x, rfl⟩)
  let e0 : ∀ N : t, Ki N →ₐ[K] L := fun N => (ιi N).codRestrict L.toSubalgebra (hrange N)

  have hg : ∀ (N : t) (e : Ki N →ₐ[K] L), ∃ g : V →ₗ[K] L, Fam L g ∧ ∀ v, g v = e (fi N v) :=
    fun N e => henl (Ki N) L e (fi N) (hfam N)
  choose g hgfam hgval using hg
  let gh : (Σ N : t, (Ki N →ₐ[K] L)) → Module.Dual L (L ⊗[K] V) :=
    fun p => (g p.1 p.2).liftBaseChange L
  have hgh1 : ∀ p v, gh p ((1 : L) ⊗ₜ[K] v) = g p.1 p.2 v := fun p v =>
    LinearMap.liftBaseChange_one_tmul _ _ _
  let Kc : Submodule L (L ⊗[K] V) := ⨅ p, LinearMap.ker (gh p)

  have hkey : ∀ (σ : L ≃ₐ[K] L) (N : t) (e : Ki N →ₐ[K] L) (x : L ⊗[K] V),
      gh ⟨N, e⟩ (galAct σ x) = σ (gh ⟨N, (σ.symm.toAlgHom).comp e⟩ x) := by
    intro σ N e x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      simp only [gh, galAct_tmul, LinearMap.liftBaseChange_tmul, hgval, smul_eq_mul, map_mul,
        AlgHom.comp_apply]
      congr 1
      exact (σ.apply_symm_apply _).symm
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have hstab : ∀ σ : L ≃ₐ[K] L, ∀ x ∈ Kc, galAct σ x ∈ Kc := by
    intro σ x hx
    rw [Submodule.mem_iInf] at hx ⊢
    rintro ⟨N, e⟩
    rw [LinearMap.mem_ker, hkey, LinearMap.mem_ker.mp (hx ⟨N, _⟩), map_zero]
  have hGD := galoisDescent_holds K L V Kc hstab
  have hkP : kPoints Kc = W := by
    ext v
    rw [hWmem]
    show (1 : L) ⊗ₜ[K] v ∈ Kc ↔ _
    rw [Submodule.mem_iInf]
    constructor
    · intro h N
      have h1 := LinearMap.mem_ker.mp (h ⟨N, e0 N⟩)
      have h2 : e0 N (fi N v) = 0 := by
        have h3 := hgval N (e0 N) v
        rw [← h3]
        simpa [hgh1] using h1
      exact (e0 N).toRingHom.injective (by simpa using h2)
    · intro h p
      rw [LinearMap.mem_ker, hgh1, hgval p.1 p.2 v, h p.1, map_zero]
  have hKc : Kc = baseSpan L W := by rw [hGD, hkP]

  let G : Set (Module.Dual L (L ⊗[K] V)) := Set.range gh
  obtain ⟨t', ht'sub, ht'span, ht'li⟩ := exists_linearIndependent L G
  have ht'fin : t'.Finite := ht'li.setFinite
  have : Fintype t' := ht'fin.fintype
  set ρ := Fintype.card t' with hρ
  let eT := Fintype.equivFin t'
  have hpick : ∀ i : Fin ρ, ∃ p, gh p = (eT.symm i : Module.Dual L (L ⊗[K] V)) :=
    fun i => ht'sub (eT.symm i).2
  choose pk hpk using hpick
  let cfL : Fin ρ → Module.Dual L (L ⊗[K] V) := fun i => (eT.symm i : Module.Dual L (L ⊗[K] V))
  have hcomm : ∀ x : L ⊗[K] V, (∀ i, cfL i x = 0) ↔ x ∈ Kc := by
    intro x
    constructor
    · intro h
      rw [Submodule.mem_iInf]
      intro p
      rw [LinearMap.mem_ker]
      have hsp : Submodule.span L t' ≤ LinearMap.ker (Module.Dual.eval L (L ⊗[K] V) x) := by
        refine Submodule.span_le.mpr fun φ hφ => ?_
        have := h (eT ⟨φ, hφ⟩)
        simpa [cfL] using this
      have hmem : gh p ∈ Submodule.span L t' := ht'span ▸ Submodule.subset_span ⟨p, rfl⟩
      simpa using hsp hmem
    · intro hx i
      rw [Submodule.mem_iInf] at hx
      show (eT.symm i : Module.Dual L (L ⊗[K] V)) x = 0
      rw [← hpk i]
      exact LinearMap.mem_ker.mp (hx (pk i))
  have hcoan : (Submodule.span L t').dualCoannihilator = Kc := by
    ext x
    rw [Submodule.mem_dualCoannihilator, ← hcomm]
    constructor
    · intro h i
      exact h _ (Submodule.subset_span (eT.symm i).2)
    · intro h φ hφ
      have hsp : Submodule.span L t' ≤ LinearMap.ker (Module.Dual.eval L (L ⊗[K] V) x) := by
        refine Submodule.span_le.mpr fun ψ hψ => ?_
        have := h (eT ⟨ψ, hψ⟩)
        simpa [cfL] using this
      simpa using hsp hφ
  have hWfd : FiniteDimensional K W := inferInstance
  have hdim : Module.finrank K W + ρ = Module.finrank K V := by
    have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span L t')
    rw [hcoan, hKc, finrank_baseSpan L W, Module.finrank_baseChange] at h1
    have h2 : Module.finrank L (Submodule.span L t') = ρ := by
      rw [hρ, finrank_span_set_eq_card ht'li, Set.toFinset_card]
    omega
  refine ⟨L, inferInstance, hnfL, inferInstance, ρ, fun i => g (pk i).1 (pk i).2, cfL,
    fun i => hgfam _ _, fun i v => ?_, fun x => ?_, hdim⟩
  · rw [show cfL i = gh (pk i) from (hpk i).symm, hgh1]
  · rw [hcomm, hKc]

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

theorem disc_bound {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (K₀ : Subfield K) (hres : ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K)) (c : ℤ → K)
    (S : Set K)
    (hc : ∀ t ∈ S,
        Filter.Tendsto (fun n => ‖c n * t ^ n‖) Filter.cofinite (nhds 0) ∧
        ∀ τ ∈ K₀, ‖τ‖ = 1 → ‖∑' n, c n * (t * τ) ^ n‖ ≤ 1)
    (t : K) (htS : t ∈ S) (n : ℤ) : ‖c n‖ * ‖t‖ ^ n ≤ 1 := by
  obtain ⟨hlim, hbd⟩ := hc t htS
  let e := Equiv.funUnique (Fin 1) ℤ
  have key := ReciprocityTheory.MultiplicativeHeights.cauchy_inequality_on_torus K K₀ hres 1 (fun χ => c (χ 0) * t ^ (χ 0)) ?_ ?_ (fun _ => n)
  · simpa [norm_mul, norm_zpow] using key
  · exact (hlim.comp e.injective.tendsto_cofinite :)
  · intro τ hτ
    have h := hbd (τ 0) (hτ 0).1 (hτ 0).2
    unfold ReciprocityTheory.MultiplicativeHeights.torusSum
    have h2 : (fun χ : Fin 1 → ℤ => c (χ 0) * t ^ (χ 0) * ∏ i, τ i ^ χ i) =
        fun χ => (fun m : ℤ => c m * (t * τ 0) ^ m) (e χ) := by
      funext χ
      simp [e, Fin.prod_univ_one, mul_zpow, mul_assoc]
    rw [h2]
    convert h using 2
    exact e.tsum_eq (fun m : ℤ => c m * (t * τ 0) ^ m)

theorem disc_holds : DiscStatement := by
  intro K _ _ _ K₀ hres S hS hdense c b hb hc n
  have hbd : ∀ t ∈ S, ‖c n‖ * ‖t‖ ^ n ≤ 1 := fun t ht => disc_bound K₀ hres c S hc t ht n
  constructor
  · by_contra hlt
    push_neg at hlt
    have hcont : ContinuousAt (fun x : ℝ => ‖c n‖ * x ^ n) 1 :=
      continuousAt_const.mul (continuousAt_zpow₀ (1 : ℝ) n (Or.inl one_ne_zero))
    have hev : ∀ᶠ x in nhds (1 : ℝ), 1 < ‖c n‖ * x ^ n :=
      hcont.eventually (lt_mem_nhds (by simpa using hlt))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set r : ℝ := max (1 / 2) (1 - ε / 2) with hr
    have hr0 : 0 < r := lt_max_of_lt_left (by norm_num)
    have hr1 : r < 1 := max_lt (by norm_num) (by linarith)
    obtain ⟨t, htS, ht⟩ :=
      hdense r hr0 hr1 (min (ε / 2) (1 - r)) (lt_min (by linarith) (by linarith))
    have h1 := hbd t htS
    have h2 := (hS t htS).2
    have hdist : dist ‖t‖ 1 < ε := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith : (0 : ℝ) < 1 - ‖t‖)]
      have h4 := (abs_lt.1 ht).1
      have h5 : min (ε / 2) (1 - r) ≤ ε / 2 := min_le_left _ _
      have h3 : 1 - ε / 2 ≤ r := le_max_right _ _
      linarith
    exact absurd h1 (not_le.2 (hball hdist))
  · intro hn
    by_contra hne
    have hq : 0 < ‖c n‖ := norm_pos_iff.2 hne
    have hm : 0 < -n := by omega
    have hcont : ContinuousAt (fun x : ℝ => x ^ (-n)) 0 :=
      continuousAt_zpow₀ (0 : ℝ) (-n) (Or.inr hm.le)
    have h0 : (fun x : ℝ => x ^ (-n)) 0 = 0 := zero_zpow _ hm.ne'
    have hev : ∀ᶠ x in nhds (0 : ℝ), x ^ (-n) < ‖c n‖ :=
      hcont.eventually (gt_mem_nhds (by rw [h0]; exact hq))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set r : ℝ := min (1 / 2) (ε / 2) with hr
    have hr0 : 0 < r := lt_min (by norm_num) (by linarith)
    have hr1 : r < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    obtain ⟨t, htS, ht⟩ := hdense r hr0 hr1 r hr0
    have htpos := (hS t htS).1
    have hdist : dist ‖t‖ 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
      have h4 := (abs_lt.1 ht).2
      have h5 : r ≤ ε / 2 := min_le_right _ _
      linarith
    have h6 := hball hdist
    have h1 := hbd t htS
    have h7 : ‖t‖ ^ n * ‖t‖ ^ (-n) = 1 := by
      rw [← zpow_add₀ htpos.ne', add_neg_cancel, zpow_zero]
    have h9 : ‖c n‖ ≤ ‖t‖ ^ (-n) := by
      have h10 := mul_le_mul_of_nonneg_right h1 (zpow_pos htpos (-n)).le
      rw [mul_assoc, h7, mul_one, one_mul] at h10
      exact h10
    linarith

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end
