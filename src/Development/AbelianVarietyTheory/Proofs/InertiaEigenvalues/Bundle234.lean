module

public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract

@[expose] public section

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC

namespace GlobalTheory.ContCocycleDualLattice

universe u

section

variable {O G VT VT' : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] (D : LatData O G VT VT')

theorem mem_dualLat_iff_of_span (s : Finset VT) (hs : Submodule.span O (s : Set VT) = D.T) (f : VT') :
    f ∈ D.T' ↔ ∀ x ∈ s, D.bT x f ∈ Set.range (algebraMap O (FractionRing O)) := by
  constructor
  · intro hf x hx
    have := hf x (hs ▸ Submodule.subset_span hx)
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 this
    exact ⟨y, hy⟩
  · intro hf x hx
    rw [← hs] at hx
    have hle : Submodule.span O (s : Set VT) ≤
        (1 : Submodule O (FractionRing O)).comap (D.bT.flip f) := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨y, hy⟩ := hf x hx
      exact Submodule.mem_one.2 ⟨y, hy⟩
    exact hle hx

theorem isOpen_dualLat (hO : IsOpen (Set.range (algebraMap O (FractionRing O)))) (hT : D.T.FG) :
    IsOpen (D.T' : Set VT') := by
  obtain ⟨s, hs⟩ := hT
  have e : (D.T' : Set VT') = ⋂ x ∈ s, (fun f => D.bT x f) ⁻¹' Set.range (algebraMap O (FractionRing O)) := by
    ext f
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
    exact mem_dualLat_iff_of_span D s hs f
  rw [e]
  refine isOpen_biInter_finset fun x _ => hO.preimage ?_
  exact D.contbT.comp (continuous_const.prodMk continuous_id)

theorem exists_smul_mem_dualLat (hT : D.T.FG) (f : VT') : ∃ c : O, c ≠ 0 ∧ c • f ∈ D.T' := by
  obtain ⟨s, hs⟩ := hT
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) s (fun x => D.bT x f)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, (mem_dualLat_iff_of_span D s hs _).2 fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hb x hx
  refine ⟨y, ?_⟩
  rw [map_smul]
  exact hy

theorem exists_smul_subset_dualLat (hO : IsOpen (Set.range (algebraMap O (FractionRing O))))
    (hT : D.T.FG) {S : Set VT'} (hS : IsCompact S) : ∃ c : O, c ≠ 0 ∧ ∀ f ∈ S, c • f ∈ D.T' := by
  classical
  choose c hc0 hc using exists_smul_mem_dualLat D hT
  have hopen : IsOpen (D.T' : Set VT') := isOpen_dualLat D hO hT
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun v => (fun w : VT' => c v • w) ⁻¹' (D.T' : Set VT'))
    (fun v => hopen.preimage (continuous_const_smul (c v))) (fun f _ => Set.mem_iUnion.2 ⟨f, hc f⟩)
  refine ⟨∏ v ∈ t, c v, Finset.prod_ne_zero_iff.2 fun v _ => hc0 v, fun f hf => ?_⟩
  obtain ⟨v, hv, hfv⟩ := Set.mem_iUnion₂.1 (ht hf)
  rw [← Finset.mul_prod_erase t c hv, mul_comm, mul_smul]
  exact D.T'.smul_mem _ hfv

theorem exists_smul_mem_range_j' [CompactSpace G]
    (hO : IsOpen (Set.range (algebraMap O (FractionRing O)))) (hT : D.T.FG) (y : H1 D.ρT') :
    ∃ c : O, c ≠ 0 ∧ c • y ∈ LinearMap.range D.j' := by
  induction y using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨c, hc0, hc⟩ := exists_smul_subset_dualLat D hO hT (isCompact_range z.2.1)
    let z' : Z1 D.ρTl' := ⟨fun g => ⟨c • z.1 g, hc _ ⟨g, rfl⟩⟩,
      Continuous.subtype_mk (z.2.1.const_smul c) _, fun g h => by
        apply Subtype.ext
        show c • z.1 (g * h) = c • z.1 g + D.ρT' g (c • z.1 h)
        rw [z.2.2 g h, map_smul, smul_add]⟩
    refine ⟨c, hc0, Submodule.Quotient.mk z', ?_⟩
    rw [← Submodule.Quotient.mk_smul]
    rfl

end

end GlobalTheory.ContCocycleDualLattice

namespace GlobalTheory

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC

theorem jSpan_holds : ReciprocityTheory.ChartRestriction.T2.JSpan := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ _ hF i D hD y
  haveI : IsGalois K (PadicAlgCl p) := by
    have : IsGalois ℚ_[p] (PadicAlgCl p) := inferInstance
    infer_instance
  haveI : CompactSpace (Formalism.GaloisCohomology.GK p K) := inferInstance
  haveI : CompactSpace G := i.symm.surjective.compactSpace i.symm.continuous
  exact ContCocycleDualLattice.exists_smul_mem_range_j' D hF.emb.isOpen_range hD.lat.1 y

end GlobalTheory
end

section

open ReciprocityTheory.ChartRestriction.T2

namespace GlobalTheory

theorem isPrecomplete_of_compact_isAdic {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] (I : Ideal O) (h : IsAdic I) : IsPrecomplete I O := by
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := exists_clusterPt_of_compactSpace (Filter.map f Filter.atTop)
  refine ⟨L, fun n => ?_⟩
  have hopen : IsOpen ((I ^ n : Ideal O) : Set O) := (isAdic_iff.mp h).1 n
  have hclosed : IsClosed ((I ^ n : Ideal O) : Set O) :=
    AddSubgroup.isClosed_of_isOpen (I ^ n).toAddSubgroup hopen
  have hc : IsClosed {x : O | f n - x ∈ I ^ n} :=
    hclosed.preimage (f := fun x => f n - x) (continuous_const.sub continuous_id)
  have hmem : {x : O | f n - x ∈ I ^ n} ∈ Filter.map f Filter.atTop := by
    rw [Filter.mem_map]
    filter_upwards [Filter.eventually_ge_atTop n] with k hk
    have := hf hk
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    exact this
  have hLm : L ∈ {x : O | f n - x ∈ I ^ n} := by
    rw [← hc.closure_eq]
    exact mem_closure_iff_clusterPt.mpr (hL.mono (Filter.le_principal_iff.mpr hmem))
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  exact hLm

theorem isAdicComplete_of_padicCoeff {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] (h : PadicCoeff p O) : IsAdicComplete (IsLocalRing.maximalIdeal O) O := by
  haveI := h.ring
  haveI := h.compact
  haveI := isPrecomplete_of_compact_isAdic _ h.adic
  haveI : IsHausdorff (IsLocalRing.maximalIdeal O) O := inferInstance
  exact ⟨⟩

end GlobalTheory
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

namespace GlobalTheory

theorem fractionRing_t2_of_openEmbedding {O : Type} [CommRing O] [IsDomain O]
    [TopologicalSpace O] [T2Space O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)]
    (he : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))) : T2Space (FractionRing O) := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  set ι := algebraMap O (FractionRing O)
  have hsub : (ι ⁻¹' {x}).Subsingleton := fun a ha b hb => he.injective (ha.trans hb.symm)
  have hcl : IsClosed (ι ⁻¹' {x}) := hsub.isClosed
  refine ⟨ι '' (ι ⁻¹' {x})ᶜ, ?_, ?_⟩
  · refine (he.isOpenMap _ hcl.isOpen_compl).mem_nhds ⟨0, ?_, map_zero ι⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, map_zero]
    exact fun h => hx h.symm
  · rintro ⟨a, ha, hax⟩
    exact ha hax

theorem isFGTop_comap_lsmul_one : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)],
    PadicCoeff p O → FracTop O → ∀ n : ℕ,
    IsFGTop O ((1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))) := by
  intro p O _ _ _ _ _ _ _ hO hF n
  haveI := hO.t2
  haveI := fractionRing_t2_of_openEmbedding hF.emb
  set S := (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))
  refine ⟨?_, inferInstance, inferInstance⟩
  haveI : Module.Finite O (1 : Submodule O (FractionRing O)) := by
    rw [Module.Finite.iff_fg, Submodule.one_eq_span]
    exact Submodule.fg_span (Set.finite_singleton _)
  haveI : IsNoetherian O (1 : Submodule O (FractionRing O)) := inferInstance
  let f : S →ₗ[O] (1 : Submodule O (FractionRing O)) :=
    (LinearMap.lsmul O (FractionRing O) ((p : O) ^ n)).restrict (fun x hx => hx)
  refine Module.Finite.of_injective f ?_
  intro a b hab
  have h := congrArg Subtype.val hab
  simp only [f, LinearMap.restrict_apply, LinearMap.lsmul_apply] at h
  have hp : ((p : O) ^ n) ≠ 0 := pow_ne_zero _ hO.p_ne
  exact Subtype.ext (smul_right_injective (FractionRing O) hp h)

end GlobalTheory
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

noncomputable section

namespace GlobalTheory.CycImage

theorem cyc_eq_image : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G], PadicCoeff p O → ∀ (φ : ℤ_[p] →+* O) (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ g : G, ((ε g : Oˣ) : O) = φ ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) : ℤ_[p]ˣ) : ℤ_[p]) := by
  intro p _ K O _ _ _ _ G _ _ hO φ i ε hε g
  set c : ℤ_[p] := ((cyclotomicCharacter (PadicAlgCl p) p
    (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) : ℤ_[p]ˣ) : ℤ_[p]) with hcdef
  have key : ∀ n : ℕ, ((ε g : Oˣ) : O) - φ c ∈ Ideal.span {(p : O) ^ n} := by
    intro n
    obtain ⟨ζ, hζ⟩ : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ (p ^ n) :=
      HasEnoughRootsOfUnity.exists_primitiveRoot _ _
    obtain ⟨a, ha, hmem⟩ := hε (i g) n ζ hζ.pow_eq_one
    have hcar : ((carry i ε (i g) : Oˣ) : O) = ((ε g : Oˣ) : O) := by
      simp only [carry, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
      congr 2
      exact i.symm_apply_apply g
    rw [hcar] at hmem
    have hsp := cyclotomicCharacter.spec (L := PadicAlgCl p) p (n := n)
      (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) ζ hζ.pow_eq_one
    have h1 : (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) ζ = (i g) ζ := rfl
    rw [h1, ha] at hsp
    set v : ℕ := (PadicInt.toZModPow n c).val with hv
    have hmod : a ≡ v [MOD p ^ n] := by
      have hne : ζ ≠ 0 := hζ.ne_zero (NeZero.ne _)
      have hz : ζ ^ ((a : ℤ) - (v : ℤ)) = 1 := by
        rw [zpow_sub₀ hne, zpow_natCast, zpow_natCast, hsp, div_self (pow_ne_zero _ hne)]
      have hd := (hζ.zpow_eq_one_iff_dvd _).1 hz
      exact (Nat.modEq_iff_dvd.2 (by
        have : ((p ^ n : ℕ) : ℤ) ∣ -((a : ℤ) - (v : ℤ)) := (dvd_neg).2 (by exact_mod_cast hd)
        simpa using this))
    have hc : c - (v : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, hv,
        ZMod.natCast_zmod_val, sub_self]
    have hφ : φ c - (v : O) ∈ Ideal.span {(p : O) ^ n} := by
      have := Ideal.mem_map_of_mem φ hc
      rw [Ideal.map_span, Set.image_singleton] at this
      simpa using this
    have hav : (a : O) - (v : O) ∈ Ideal.span {(p : O) ^ n} := by
      rw [Ideal.mem_span_singleton]
      have hd : ((p ^ n : ℕ) : ℤ) ∣ (v : ℤ) - (a : ℤ) := (Nat.modEq_iff_dvd.1 hmod)
      obtain ⟨k, hk⟩ := hd
      refine ⟨-(k : O), ?_⟩
      have hk' : ((v : ℤ) : O) - ((a : ℤ) : O) = (((p ^ n : ℕ) : ℤ) : O) * (k : O) := by
        rw [← Int.cast_sub, hk, Int.cast_mul]
      push_cast at hk'
      linear_combination -hk'
    have hsum : ((ε g : Oˣ) : O) - φ c =
        ((((ε g : Oˣ) : O) - a) + ((a : O) - v)) - (φ c - v) := by ring
    rw [hsum]
    exact Ideal.sub_mem _ (Ideal.add_mem _ hmem hav) hφ
  have hbot : ((ε g : Oˣ) : O) - φ c ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal O) ^ n := by
    refine Ideal.mem_iInf.2 fun n => ?_
    have h := key n
    have hle : Ideal.span {(p : O) ^ n} ≤ (IsLocalRing.maximalIdeal O) ^ n := by
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem _).2 hO.p_mem) n
    exact hle h
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top, Ideal.mem_bot] at hbot
  exact sub_eq_zero.1 hbot

end GlobalTheory.CycImage
end
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.FunctorialityH2

theorem cyc_char_continuous {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    {G : Type} [Group G] [TopologicalSpace G] (hO : PadicCoeff p O) (i : G ≃ₜ* GK p K)
    {ε : G →* Oˣ} (hc : IsCyc p K (carry i ε)) :
    Continuous (fun g : G => ((ε g : Oˣ) : O)) := by
  have := hO.ring
  set ε' : GK p K →* Oˣ := carry i ε with hε'
  have key : ∀ k : ℕ, ∃ H : Subgroup (GK p K), IsOpen (H : Set (GK p K)) ∧
      ∀ h ∈ H, ((ε' h : Oˣ) : O) - 1 ∈ Ideal.span {(p : O) ^ k} := by
    intro k
    have hN : 0 < p ^ k := pow_pos hp.out.pos k
    haveI : NeZero ((p ^ k : ℕ) : PadicAlgCl p) := ⟨by exact_mod_cast hN.ne'⟩
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (p ^ k) (PadicAlgCl p))
      (Polynomial.degree_cyclotomic_pos (p ^ k) (PadicAlgCl p) hN).ne'
    have hpr : IsPrimitiveRoot ζ (p ^ k) := Polynomial.isRoot_cyclotomic_iff.1 hζ
    have hint : IsIntegral K ζ :=
      IsIntegral.of_pow hN (by rw [hpr.pow_eq_one]; exact isIntegral_one)
    haveI := IntermediateField.adjoin.finiteDimensional hint
    refine ⟨(IntermediateField.adjoin K {ζ}).fixingSubgroup,
      IntermediateField.fixingSubgroup_isOpen _, fun h hh => ?_⟩
    have hfix : h ζ = ζ := hh ⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩
    obtain ⟨a, ha, hmem⟩ := hc h k ζ hpr.pow_eq_one
    have hz : ζ ≠ 0 := hpr.ne_zero hN.ne'
    have h1 : ζ ^ ((a : ℤ) - 1) = 1 := by
      rw [zpow_sub₀ hz, zpow_natCast, zpow_one, ← ha, hfix, div_self hz]
    obtain ⟨c, hcdef⟩ := (hpr.zpow_eq_one_iff_dvd _).1 h1
    have h2 : ((a : O) - 1) = ((p : O) ^ k) * (c : O) := by
      have := congrArg (fun z : ℤ => (z : O)) hcdef
      push_cast at this
      exact this
    have h3 : ((ε' h : Oˣ) : O) - 1 = (((ε' h : Oˣ) : O) - a) + ((a : O) - 1) := by ring
    rw [h3, h2]
    exact Ideal.add_mem _ hmem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hcont' : Continuous (fun g : GK p K => ((ε' g : Oˣ) : O)) := by
    rw [continuous_iff_continuousAt]
    intro g0
    rw [ContinuousAt, Filter.tendsto_def]
    intro U hU
    have hV : (fun o : O => ((ε' g0 : Oˣ) : O) + o) ⁻¹' U ∈ nhds (0 : O) :=
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨m, hm⟩ := (isAdic_iff.1 hO.adic).2 _ hV
    obtain ⟨H, hHo, hH⟩ := key m
    have hle : Ideal.span {(p : O) ^ m} ≤ IsLocalRing.maximalIdeal O ^ m :=
      (Ideal.span_singleton_le_iff_mem _).2 (Ideal.pow_mem_pow hO.p_mem m)
    refine Filter.mem_of_superset
      ((hHo.preimage (continuous_const_mul g0⁻¹)).mem_nhds (by simpa using H.one_mem)) ?_
    intro g hg
    have h1 := hH _ hg
    have h2 : ((ε' g : Oˣ) : O) - (ε' g0 : O) ∈ Ideal.span {(p : O) ^ m} := by
      have e : ((ε' g : Oˣ) : O) - (ε' g0 : O) =
          (ε' g0 : O) * (((ε' (g0⁻¹ * g) : Oˣ) : O) - 1) := by
        rw [map_mul, Units.val_mul, mul_sub, ← mul_assoc, ← Units.val_mul, ← map_mul,
          mul_inv_cancel, map_one, Units.val_one, one_mul, mul_one]
      rw [e]
      exact Ideal.mul_mem_left _ _ h1
    have h3 := hm (hle h2)
    simpa using h3
  have e : (fun g : G => ((ε g : Oˣ) : O)) = (fun g : GK p K => ((ε' g : Oˣ) : O)) ∘ i := by
    funext g
    simp only [Function.comp_apply, hε', carry, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    first
    | rw [ContinuousMulEquiv.symm_apply_apply]
    | exact congrArg (fun x => ((ε x : Oˣ) : O)) (i.toMulEquiv.symm_apply_apply g).symm
  rw [e]
  exact hcont'.comp i.continuous

end GlobalTheory.FunctorialityH2
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory

theorem padicInt_ringHom_continuous_of_padicCoeff : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O], PadicCoeff p O → ∀ φ : ℤ_[p] →+* O, Continuous φ := by
  intro p _ O _ _ _ _ hO φ
  haveI := hO.ring
  refine continuous_of_continuousAt_zero φ ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := (isAdic_iff.mp hO.adic).2 s hs
  have hball : Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(n : ℤ))) ∈ nhds (0 : ℤ_[p]) := by
    apply Metric.closedBall_mem_nhds
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  refine Filter.mem_map.mpr (Filter.mem_of_superset hball ?_)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, PadicInt.norm_le_pow_iff_mem_span_pow] at hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  apply hn
  show φ (a * (p : ℤ_[p]) ^ n) ∈ ((IsLocalRing.maximalIdeal O) ^ n : Ideal O)
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hO.p_mem n)

end GlobalTheory
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.NatQuot

theorem quot_pow_maximalIdeal_discrete_finite :
    ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
      [IsTopologicalRing O], PadicCoeff p O → ∀ k : ℕ,
      DiscreteTopology (O ⧸ IsLocalRing.maximalIdeal O ^ k) ∧ Finite (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  intro p O _ _ _ _ _ hO k
  haveI : CompactSpace O := hO.compact
  set I : Ideal O := IsLocalRing.maximalIdeal O ^ k with hI
  have hopen : IsOpen ((I : Ideal O) : Set O) := (isAdic_iff.mp hO.adic).1 k
  have hdisc : DiscreteTopology (O ⧸ I) := by
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have himg : (Ideal.Quotient.mk I) '' (I : Set O) = {0} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [Ideal.Quotient.eq_zero_iff_mem] using hx
      · rintro rfl
        exact ⟨0, I.zero_mem, map_zero _⟩
    rw [← himg]
    exact QuotientRing.isOpenMap_coe I _ hopen
  refine ⟨hdisc, ?_⟩
  haveI : CompactSpace (O ⧸ I) := Quotient.compactSpace
  exact finite_of_compact_of_discrete

end GlobalTheory.NatQuot
end

section

open ReciprocityTheory.Gal
open Formalism.NG
namespace GlobalTheory

theorem hcLC_exists_pow_smul_eq_zero : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O),
    (∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0) → ∀ x ∈ ReciprocityTheory.ChartRestriction.T2.HcLC ρ, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  intro O _ G _ _ _ M _ _ ρ ϖ hM x hx
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.1 hx
  have hlc : IsLocallyConstant (c : G → M) := hc
  classical
  let f : M → ℕ := fun m => Classical.choose (hM m)
  have hf : ∀ m, ϖ ^ f m • m = 0 := fun m => Classical.choose_spec (hM m)
  have hfin : (Set.range (c : G → M)).Finite := hlc.range_finite
  obtain ⟨N, hN⟩ := (hfin.image f).bddAbove
  refine ⟨N, ?_⟩
  have hc0 : ϖ ^ N • c = 0 := by
    apply Subtype.ext
    funext g
    have hk : f ((c : G → M) g) ≤ N := hN ⟨_, ⟨g, rfl⟩, rfl⟩
    show ϖ ^ N • (c : G → M) g = 0
    rw [← Nat.sub_add_cancel hk, pow_add, mul_smul, hf, smul_zero]
  rw [← LinearMap.map_smul, hc0, map_zero]

end GlobalTheory
end
