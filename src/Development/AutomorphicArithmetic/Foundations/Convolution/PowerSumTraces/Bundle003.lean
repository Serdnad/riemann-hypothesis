module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportHfun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private lemma powSum_eq_count (s : Multiset ℂ) (S : Finset ℂ) (h : ∀ z ∈ s, z ∈ S) (j : ℕ) :
    (s.map (· ^ j)).sum = ∑ z ∈ S, (s.count z : ℂ) * z ^ j := by
  classical
  rw [Finset.sum_multiset_map_count]
  have hsub : s.toFinset ⊆ S := fun z hz => h z (Multiset.mem_toFinset.1 hz)
  rw [← Finset.sum_subset hsub]
  · exact Finset.sum_congr rfl fun z _ => by simp [nsmul_eq_mul]
  · intro z _ hz
    have : s.count z = 0 := Multiset.count_eq_zero.2 fun hm => hz (Multiset.mem_toFinset.2 hm)
    simp [this]

private def powHom (z : ℂ) : Multiplicative ℕ →* ℂ where
  toFun n := z ^ n.toAdd
  map_one' := by simp
  map_mul' a b := by simp [pow_add]

private lemma powHom_injective : Function.Injective powHom := by
  intro a b h
  have := DFunLike.congr_fun h (Multiplicative.ofAdd 1)
  simpa [powHom] using this

theorem UpperTheory.ConvolutionTheory.C.powIndep :
    UpperTheory.ConvolutionTheory.C.PowIndep := by
  classical
  intro ι _ c Z hZ hev ζ
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let S : Finset ℂ := Finset.univ.biUnion fun i => (Z i).toFinset
  let a : ℂ → ℂ := fun z => ∑ i, c i * ((Z i).count z : ℂ)
  have hmem : ∀ i, ∀ z ∈ Z i, z ∈ S := fun i z hz =>
    Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Multiset.mem_toFinset.2 hz⟩
  have key : ∀ j, N ≤ j → ∑ z ∈ S, a z * z ^ j = 0 := by
    intro j hj
    have h0 := hN j hj
    simp only [powSum_eq_count _ S (hmem _) j, Finset.mul_sum] at h0
    rw [Finset.sum_comm] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [a, Finset.sum_mul, mul_assoc]
  have hne : ∀ z ∈ S, z ≠ 0 := by
    intro z hz h0
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hz
    exact hZ i (h0 ▸ Multiset.mem_toFinset.1 hi)
  have lin : LinearIndependent ℂ (fun z : S => (powHom z : Multiplicative ℕ → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp (fun z : S => powHom z)
      (powHom_injective.comp Subtype.val_injective)
  rw [Fintype.linearIndependent_iff] at lin
  have hb := lin (fun z => a z * (z : ℂ) ^ N) (by
    funext n
    have := key (N + n.toAdd) (Nat.le_add_right _ _)
    rw [← Finset.sum_coe_sort S] at this
    simpa [powHom, pow_add, mul_assoc, Finset.sum_apply] using this)
  have ha : a ζ = 0 := by
    by_cases hζ : ζ ∈ S
    · have := hb ⟨ζ, hζ⟩
      exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (hne ζ hζ))
    · refine Finset.sum_eq_zero fun i _ => ?_
      have : (Z i).count ζ = 0 := Multiset.count_eq_zero.2 fun hm => hζ (hmem i ζ hm)
      simp [this]
  rw [← ha]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  rw [Multiset.filter_eq', Multiset.card_replicate]
end

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

noncomputable section

namespace UpperTheory.ConvolutionTheory.C.CharIndepProof

open GlobalTheory.OpTrace

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {V : Type} [AddCommGroup V] [Module ℂ V]

omit [MeasurableSpace G] [BorelSpace G] in
private theorem isLocallyConstant_of_right {U : Subgroup G} (hUo : IsOpen (U : Set G)) {f : G → ℂ}
    (hf : ∀ k ∈ U, ∀ x, f (x * k) = f x) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' (U : Set G), hUo.preimage (continuous_const_mul _), by simp [U.one_mem],
    fun x hx => ?_⟩
  have := hf _ hx g
  simpa using this

private theorem isIntegralOp_smoothOp (m : Measure G) [IsFiniteMeasureOnCompacts m] {ρ : Representation ℂ G V}
    (hρ : GlobalTheory.PRep.IsSmooth ρ) {f : G → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    IsIntegralOp m ρ f (smoothOp ρ m f) := by
  intro v l
  have hi := hρ.smoothOp_integrand hf hc v
  refine ⟨?_, ?_⟩
  · have := integrable_map (μ := m) hi.1 hi.2 l l.map_zero
    simpa only [map_smul, smul_eq_mul] using this
  · rw [hρ.map_smoothOp (μ := m) hf hc l v]
    simp only [smul_eq_mul]

private theorem smoothOp_eq_levOp (m : Measure G) [m.IsHaarMeasure] {U : Subgroup G} (hUo : IsOpen (U : Set G))
    (hUc : IsCompact (U : Set G)) {ρ : Representation ℂ G V} (hρ : GlobalTheory.PRep.IsSmooth ρ) {f : G → ℂ}
    (hf : GlobalTheory.BCT.IsHecke U f) {v : V} (hv : v ∈ fixed ρ U) :
    smoothOp ρ m f v = (m.real (U : Set G) : ℂ) • GlobalTheory.BCT.levOp ρ U U f LinearMap.id v := by
  have hlc := isLocallyConstant_of_right hUo (fun k hk x => (hf.2 k hk x).2)
  have hs := GlobalTheory.TwTrLevel.finite_supp U hUo f hf.1
  rw [GlobalTheory.TwTrLevel.levOp_apply ρ U U f LinearMap.id v hs, Subgroup.relIndex_self]
  simp only [Nat.cast_one, inv_one, one_smul, LinearMap.id_apply]
  rw [finsum_eq_sum_of_support_subset (s := hs.toFinset) _ (by
    intro q hq
    simp only [Function.mem_support, ne_eq] at hq
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hq (by rw [h0, zero_smul]))]
  refine GlobalTheory.OpTrace.eq_of_forall_dual fun l => ?_

  rw [hρ.map_smoothOp hlc hf.1 l v,
  GlobalTheory.HaarSum.integral_eq_sum_cosets m U hUo hUc.measure_ne_top (fun g => f g • l (ρ g v)) ?_ hs.toFinset ?_,
  map_smul, map_sum]
  · simp
  · intro x s hs'
    rw [(hf.2 s hs' x).2, map_mul, Module.End.mul_apply, (mem_fixed.1 hv) s hs']
  · intro q hq
    have : f q.out = 0 := by simpa using hq
    simp [this]

private theorem finRankTrace_smoothOp (m : Measure G) [m.IsHaarMeasure] {U : Subgroup G} (hUo : IsOpen (U : Set G))
    (hUc : IsCompact (U : Set G)) {ρ : Representation ℂ G V} (hρ : GlobalTheory.PRep.IsSmooth ρ)
    [FiniteDimensional ℂ (fixed ρ U)] {f : G → ℂ} (hf : GlobalTheory.BCT.IsHecke U f) :
    finRankTrace (smoothOp ρ m f) = (m.real (U : Set G) : ℂ) * GlobalTheory.BCT.twTr ρ U U f LinearMap.id := by
  have hlc := isLocallyConstant_of_right hUo (fun k hk x => (hf.2 k hk x).2)
  have hW : ∀ x, smoothOp ρ m f x ∈ fixed ρ U :=
    hρ.smoothOp_mem_fixed hlc hf.1 (fun k hk g => (hf.2 k hk g).1)
  have hmem : ∀ v ∈ fixed ρ U, GlobalTheory.BCT.levOp ρ U U f LinearMap.id v ∈ fixed ρ U := fun v hv =>
    GlobalTheory.TwTrLevel.levOp_mem_fixed ρ (MonoidHom.id G) (fun _ => rfl) LinearMap.id (fun _ => rfl) U U hUo
      (fun _ h => h) f hf v hv
  rw [finRankTrace_eq _ (fixed ρ U) hW, GlobalTheory.BCT.twTr, dite_eq_left hmem, ← smul_eq_mul, ← map_smul]
  congr 1
  refine LinearMap.ext fun v => Subtype.ext ?_
  simpa using smoothOp_eq_levOp m hUo hUc hρ hf v.2

end UpperTheory.ConvolutionTheory.C.CharIndepProof

open UpperTheory.ConvolutionTheory.C.CharIndepProof GlobalTheory.OpTrace in
theorem UpperTheory.ConvolutionTheory.C.charIndep :
    UpperTheory.ConvolutionTheory.C.CharIndep := by
  classical
  intro G _ _ _ _ _ _ _ _ m _ _ U hU ι _ σ c hfd hc i₀ hi₀
  obtain ⟨hUc, hUo⟩ := hU
  have hfx : ∀ i, fixed (σ i).ρ U = fixedVectors (σ i).ρ U := fun i =>
    Submodule.ext fun v => GlobalTheory.OpTrace.mem_fixed
  haveI hfd' : ∀ i, FiniteDimensional ℂ (fixed (σ i).ρ U) := fun i => by rw [hfx i]; exact hfd i
  let S : Setoid ι := ⟨fun i j => Nonempty ((σ i).ρ.Equiv (σ j).ρ),
    ⟨fun i => ⟨Representation.Equiv.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩⟩
  let mk : ι → Quotient S := Quotient.mk S
  let r : Quotient S → ι := Quotient.out
  haveI : Fintype (Quotient S) := Fintype.ofFinite _
  have hmkr : ∀ q, mk (r q) = q := fun q => Quotient.out_eq q
  have hr : ∀ i, Nonempty ((σ i).ρ.Equiv (σ (r (mk i))).ρ) := fun i =>
    (Quotient.exact (hmkr (mk i))).elim fun e => ⟨e.symm⟩
  let c' : Quotient S → ℂ := fun q => ∑ i with mk i = q, c i
  have hvol : (m.real (U : Set G) : ℂ) ≠ 0 := by
    have h1 : m (U : Set G) ≠ 0 := (hUo.measure_pos m ⟨1, U.one_mem⟩).ne'
    have h2 : m.real (U : Set G) ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h1, hUc.measure_ne_top⟩
    exact_mod_cast h2
  have key : ∀ f, GlobalTheory.BCT.IsHecke U f →
      ∑ q : {q : Quotient S // fixed (σ (r q)).ρ U ≠ ⊥},
        c' q * GlobalTheory.BCT.twTr (σ (r q)).ρ U U f LinearMap.id = 0 := by
    intro f hf
    have hlc : IsLocallyConstant f := isLocallyConstant_of_right hUo (fun k hk x => (hf.2 k hk x).2)
    have hW : ∀ i x, smoothOp (σ i).ρ m f x ∈ fixed (σ i).ρ U := fun i =>
      (σ i).smooth.smoothOp_mem_fixed hlc hf.1 (fun k hk g => (hf.2 k hk g).1)
    have hfr : ∀ i, FiniteDimensional ℂ (LinearMap.range (smoothOp (σ i).ρ m f)) := fun i =>
      Submodule.finiteDimensional_of_le (S₂ := fixed (σ i).ρ U) (by rintro _ ⟨x, rfl⟩; exact hW i x)
    let s : ι → ℂ := fun i => finRankTrace (smoothOp (σ i).ρ m f)
    have h0 := hc f s ⟨hlc, hf.1⟩ (fun u hu g => hf.2 u hu g) (fun i =>
      ⟨_, isIntegralOp_smoothOp m (σ i).smooth hlc hf.1, hfr i, rfl⟩)
    have hconst : ∀ i, s i = s (r (mk i)) := fun i => by
      obtain ⟨e⟩ := hr i
      haveI := hfr i
      exact ((finRankTrace_eq_of_equiv e.toLinearEquiv (T := smoothOp (σ i).ρ m f)
        (T' := smoothOp (σ (r (mk i))).ρ m f)
        ((σ i).smooth.map_smoothOp_of_intertwining (σ (r (mk i))).smooth hlc hf.1 e.toLinearEquiv.toLinearMap
          (fun g v => Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v))).2).symm
    have hzero : ∀ q, ¬ fixed (σ (r q)).ρ U ≠ ⊥ → s (r q) = 0 := fun q hq => by
      have hb : fixed (σ (r q)).ρ U = ⊥ := not_not.1 hq
      have hW' : ∀ x, smoothOp (σ (r q)).ρ m f x ∈ (⊥ : Submodule ℂ (σ (r q)).V) := fun x => hb ▸ hW (r q) x
      show finRankTrace _ = 0
      rw [finRankTrace_eq _ ⊥ hW', Subsingleton.elim (LinearMap.restrict _ _) 0, map_zero]
    have h1 : ∑ q, c' q * s (r q) = 0 := by
      rw [← h0, ← Finset.sum_fiberwise (s := Finset.univ) (g := mk)]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hconst i, (Finset.mem_filter.1 hi).2]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun q => fixed (σ (r q)).ρ U ≠ ⊥),
      Finset.sum_eq_zero (s := Finset.univ) (f := fun q : {q // ¬ fixed (σ (r q)).ρ U ≠ ⊥} => c' q * s (r q))
        (fun q _ => by rw [hzero q q.2, mul_zero]), add_zero] at h1
    have h2 : ∀ q : {q : Quotient S // fixed (σ (r q)).ρ U ≠ ⊥}, c' q * s (r q) =
        (m.real (U : Set G) : ℂ) * (c' q * GlobalTheory.BCT.twTr (σ (r q)).ρ U U f LinearMap.id) := fun q => by
      show c' q * finRankTrace _ = _
      rw [finRankTrace_smoothOp m hUo hUc (σ (r q)).smooth hf]
      ring
    simp only [h2, ← Finset.mul_sum] at h1
    exact (mul_eq_zero.1 h1).resolve_left hvol
  have hli := GlobalTheory.HeckeTraceIndep.twTr_linearIndependent G U hUo hUc U ⟨hUo, le_rfl, fun _ h => h⟩
    {q : Quotient S // fixed (σ (r q)).ρ U ≠ ⊥} (fun q => σ (r q)) (fun q => ⟨hfd' _, q.2⟩)
    (fun q q' h => Subtype.ext (by rw [← hmkr q, ← hmkr q']; exact Quotient.sound h))
    (fun q => c' q) key
  have hq : fixed (σ (r (mk i₀))).ρ U ≠ ⊥ := by
    obtain ⟨e⟩ := hr i₀
    rw [← hfx i₀] at hi₀
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hi₀
    refine (Submodule.ne_bot_iff _).2 ⟨e.toLinearEquiv v, mem_fixed.2 fun k hk => ?_, ?_⟩
    · have := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap k v
      rw [mem_fixed.1 hv k hk] at this
      exact this.symm
    · simpa using hv0
  have hfin := hli ⟨mk i₀, hq⟩
  have hset : {i | Nonempty ((σ i).ρ.Equiv (σ i₀).ρ)} =
      ↑(Finset.univ.filter fun i => mk i = mk i₀) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩
  rw [hset, finsum_mem_coe_finset]
  exact hfin
end
end

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.C.HopfExpansion

section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem setInt_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (m : Measure G) [m.IsMulLeftInvariant]
    (f : G → E) (y : G) {S T : Set G} (hS : MeasurableSet S) (hT : MeasurableSet T) (h : ∀ x, x ∈ S ↔ y * x ∈ T) :
    ∫ x in S, f (y * x) ∂m = ∫ x in T, f x ∂m := by
  rw [← integral_indicator hS, ← integral_indicator hT, ← integral_mul_left_eq_self (T.indicator f) y]
  congr 1
  ext x
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((h x).1 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx ((h x).2 h'))]

private theorem avg (π : UnitaryRep G H) (m : Measure G) [m.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts m]
    (J : Subgroup G) (hJ : IsCompact (J : Set G)) (hJo : IsOpen (J : Set G)) (hm : m J = 1)
    (W : Submodule ℂ H) (hW : ∀ v, v ∈ W ↔ ∀ j ∈ J, π j v = v) (u v : H) :
    ∫ j in (J : Set G), ⟪u, π j v⟫_ℂ ∂m = ⟪u, prj W v⟫_ℂ := by
  have hmeas : MeasurableSet (J : Set G) := hJo.measurableSet
  have hint : IntegrableOn (fun j => π j v) (J : Set G) m :=
    (π.continuous_orbit v).continuousOn.integrableOn_compact' hJ hmeas
  have hcl : IsClosed (W : Set H) := by
    have : (W : Set H) = ⋂ j ∈ J, {v | π j v = v} := by
      ext v
      simp [hW]
    rw [this]
    exact isClosed_biInter fun j _ => isClosed_eq (π j).continuous continuous_id
  have hA : (∫ j in (J : Set G), π j v ∂m) ∈ W := by
    rw [hW]
    intro j₀ hj₀
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    have := setInt_shift m (fun j => π j v) j₀ hmeas hmeas (fun x => by
      simp [Subgroup.mul_mem_cancel_left J hj₀])
    simpa [UnitaryRep.map_mul_apply] using this
  have hin : ∀ w ∈ W, ⟪w, ∫ j in (J : Set G), π j v ∂m⟫_ℂ = ⟪w, v⟫_ℂ := by
    intro w hw
    rw [← integral_inner hint w]
    have : ∀ j ∈ (J : Set G), ⟪w, π j v⟫_ℂ = ⟪w, v⟫_ℂ := by
      intro j hj
      rw [UnitaryRep.inner_map_right, (hW w).1 hw _ (J.inv_mem hj)]
    rw [setIntegral_congr_fun hmeas this]
    simp [Measure.real, hm]
  have hP : prj W v = ∫ j in (J : Set G), π j v ∂m := by
    change W.topologicalClosure.starProjection v = _
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.le_topologicalClosure _ hA) ?_
    intro w hw
    rw [hcl.submodule_topologicalClosure_eq] at hw
    rw [inner_sub_left, ← inner_conj_symm, ← inner_conj_symm _ w, hin w hw]
    simp
  rw [hP, integral_inner hint u]

private theorem main (π : UnitaryRep G H) (m : Measure G) [m.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts m]
    (J : Subgroup G) (hJ : IsCompact (J : Set G)) (hJo : IsOpen (J : Set G)) (hm : m J = 1)
    (W : Submodule ℂ H) (hW : ∀ v, v ∈ W ↔ ∀ j ∈ J, π j v = v) (x : G) (u v : H) :
    ⟪u, (∑ᶠ c ∈ {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}, π c.out) (prj W v)⟫_ℂ =
      ∫ g, Set.indicator {g | ∃ a ∈ J, ∃ b ∈ J, g = a * x * b} 1 g * ⟪u, π g v⟫_ℂ ∂m := by
  haveI : DiscreteTopology (G ⧸ J) := QuotientGroup.discreteTopology hJo
  set S : Set (G ⧸ J) := {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} with hSdef
  have hSfin : S.Finite := by
    have e : S = (fun k : G => (QuotientGroup.mk (k * x) : G ⧸ J)) '' (J : Set G) := by
      ext c
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨k, hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨k, hk, rfl⟩
    rw [e]
    exact (hJ.image (QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const))).finite_of_discrete
  set D : Set G := {g | ∃ a ∈ J, ∃ b ∈ J, g = a * x * b} with hDdef
  let P : G ⧸ J → Set G := fun c => QuotientGroup.mk ⁻¹' {c}
  have hPo : ∀ c, IsOpen (P c) := fun c => (isOpen_discrete {c}).preimage QuotientGroup.continuous_mk
  have hPmem : ∀ (c : G ⧸ J) (h : G), h ∈ (J : Set G) ↔ c.out * h ∈ P c := by
    intro c h
    have : (QuotientGroup.mk (c.out * h) : G ⧸ J) = c ↔ h ∈ J := by
      conv_lhs => rhs; rw [← QuotientGroup.out_eq' c]
      rw [QuotientGroup.eq]
      simp
    exact this.symm
  have hD : D = ⋃ c ∈ hSfin.toFinset, P c := by
    ext g
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨QuotientGroup.mk (a * x), ⟨a, ha, rfl⟩, ?_⟩
      change (QuotientGroup.mk (a * x * b) : G ⧸ J) = QuotientGroup.mk (a * x)
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using J.inv_mem hb
    · rintro ⟨c, ⟨k, hk, rfl⟩, hg⟩
      have hg' : (QuotientGroup.mk g : G ⧸ J) = QuotientGroup.mk (k * x) := hg
      have := QuotientGroup.eq.1 hg'.symm
      exact ⟨k, hk, _, this, by group⟩
  have hDm : MeasurableSet D := by
    rw [hD]
    exact Finset.measurableSet_biUnion _ fun c _ => (hPo c).measurableSet
  have hcont : Continuous fun g => ⟪u, π g v⟫_ℂ := continuous_const.inner (π.continuous_orbit v)
  have hPint : ∀ c, IntegrableOn (fun g => ⟪u, π g v⟫_ℂ) (P c) m := by
    intro c
    have e : P c = (fun h => c.out * h) '' (J : Set G) := by
      ext g
      constructor
      · intro hg
        refine ⟨c.out⁻¹ * g, (hPmem c _).2 (by simpa using hg), by simp⟩
      · rintro ⟨h, hh, rfl⟩
        exact (hPmem c h).1 hh
    have hc : IsCompact (P c) := by
      rw [e]
      exact hJ.image (continuous_const.mul continuous_id)
    exact hcont.continuousOn.integrableOn_compact' hc (hPo c).measurableSet
  have hind : (fun g => D.indicator (1 : G → ℂ) g * ⟪u, π g v⟫_ℂ) = D.indicator fun g => ⟪u, π g v⟫_ℂ := by
    ext g
    by_cases hg : g ∈ D <;> simp [hg]
  rw [hind, integral_indicator hDm, hD, integral_biUnion_finset _ (fun c _ => (hPo c).measurableSet) ?_
    (fun c _ => hPint c), finsum_mem_eq_finite_toFinset_sum _ hSfin, ContinuousLinearMap.sum_apply, inner_sum]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [← setInt_shift m (fun g => ⟪u, π g v⟫_ℂ) c.out hJo.measurableSet (hPo c).measurableSet (hPmem c)]
    rw [UnitaryRep.inner_map_right, ← avg π m J hJ hJo hm W hW]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp only [UnitaryRep.map_mul_apply]
    exact (UnitaryRep.inner_map_right π _ _ _).symm
  · intro c _ d _ hcd
    refine Set.disjoint_left.2 fun g hg hg' => hcd ?_
    exact (hg : _ = c).symm.trans hg'

end
end UpperTheory.ConvolutionTheory.C.HopfExpansion

theorem UpperTheory.ConvolutionTheory.C.hopOloc :
    UpperTheory.ConvolutionTheory.C.HopOloc := by
  intro K _ _ n μ _ w _ _ m _ J x hJ hm u v
  let φ : Gw n w →* normOneGL (K := K) (n := n) := (MultiplicityOne.finProj K n).comp (AdelicGLn.localEmbedding w)
  have hφ : Continuous φ := MultiplicityOne.continuous_finProj.comp (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1
  let π : UnitaryRep (Gw n w) (LL μ) := (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom φ hφ
  have hπ : ∀ x, π x = rhoL μ w x := fun _ => rfl
  have hW : ∀ v, v ∈ fixL μ w J ↔ ∀ j ∈ J, π j v = v := by
    intro v
    simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, Subgroup.mem_map]
    constructor
    · intro h j hj
      simpa [hπ, rhoL] using h _ ⟨j, hj, rfl⟩
    · rintro h _ ⟨j, hj, rfl⟩
      simpa [hπ, rhoL] using h j hj
  exact HopfExpansion.main π m J hJ.1 hJ.2 hm (fixL μ w J) hW x u v
end

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.C.olocEx :
    UpperTheory.ConvolutionTheory.C.OlocEx := by
  intro K _ _ n μ _ w _ _ m _ φ hφ
  have hL : MemLp φ 1 m := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2
  let π : UnitaryRep (Gw n w) (LL μ) := (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom
    ((MultiplicityOne.finProj K n).comp (AdelicGLn.localEmbedding w))
    (MultiplicityOne.continuous_finProj.comp (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1)
  refine ⟨π.integrated m hL.toLp, fun u v => ?_, fun T hT => ?_⟩
  · have hπ : ∀ g, π g v = rhoL μ w g v := fun _ => rfl
    rw [UnitaryRep.inner_integrated]
    refine integral_congr_ae ((MemLp.coeFn_toLp hL).mono fun g hg => ?_)
    simp only [hπ]
    rw [hg]
  · refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
    rw [hT u v, UnitaryRep.inner_integrated]
    have hπ : ∀ g, π g v = rhoL μ w g v := fun _ => rfl
    refine integral_congr_ae ((MemLp.coeFn_toLp hL).mono fun g hg => ?_)
    simp only [hπ]
    rw [hg]
end
