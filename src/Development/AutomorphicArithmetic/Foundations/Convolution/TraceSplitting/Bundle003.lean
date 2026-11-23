module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TypedEx
public import Development.WeilBound.CuspidalAdmissibility.OccursIff
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle018
import Mathlib.Algebra.Module.StablyFree.Basic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle009
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Separation.Connected
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf
open scoped InnerProductSpace

section Abs

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]

private theorem fixed_of_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) (τ : Representation ℂ G X) (hτ : ∀ x, IsOpen {g | τ g x = x})
    (J : Subgroup G) (hJ : IsCompact (J : Set G)) (f : X →ₗ[ℂ] H) (hf : ∀ g x, f (τ g x) = π g (f x))
    (v : H) (hv : ∀ u ∈ J, π u v = v) (x : X) (h0 : ⟪v, f x⟫_ℂ ≠ 0) :
    fixedVectors τ J ≠ ⊥ := by
  have hfin : ((fun g => τ g x) '' (J : Set G)).Finite := by
    obtain ⟨t, -, ht⟩ := hJ.elim_nhds_subcover (fun g => {h | τ h x = τ g x}) fun g _ => by
      have h1 : IsOpen ((fun h => g⁻¹ * h) ⁻¹' {g | τ g x = x}) := (hτ x).preimage (by fun_prop)
      refine Filter.mem_of_superset (h1.mem_nhds (by simp)) fun h hh => ?_
      have h2 : τ (g⁻¹ * h) x = x := hh
      show τ h x = τ g x
      conv_rhs => rw [← h2]
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    refine (t.finite_toSet.image fun g => τ g x).subset ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (ht hg)
    exact ⟨i, hi, (h : τ g x = τ i x).symm⟩
  classical
  set S := hfin.toFinset with hS
  have hm : ∀ y, y ∈ S ↔ ∃ g ∈ J, τ g x = y := fun y => by simp [hS]
  have hpos : 0 < S.card := Finset.card_pos.2 ⟨x, (hm x).2 ⟨1, J.one_mem, by simp⟩⟩
  have hc' : (S.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
  have hst : ∀ u ∈ J, ∀ y ∈ S, τ u y ∈ S := fun u hu y hy => by
    obtain ⟨g, hg, rfl⟩ := (hm y).1 hy
    exact (hm _).2 ⟨u * g, J.mul_mem hu hg, by rw [map_mul]; rfl⟩
  have hy : ∀ y ∈ S, ⟪v, f y⟫_ℂ = ⟪v, f x⟫_ℂ := fun y hy => by
    obtain ⟨g, hg, rfl⟩ := (hm y).1 hy
    rw [hf]
    have h1 := UnitaryRep.inner_map_map π g v (f x)
    rwa [hv g hg] at h1
  have hmem : (S.card : ℂ)⁻¹ • ∑ y ∈ S, y ∈ fixedVectors τ J := fun u hu => by

    rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_nbij' (τ u) (τ u⁻¹) (hst u hu) (hst _ (J.inv_mem hu)) (fun y _ => ?_) (fun y _ => ?_) fun _ _ => rfl
    · rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  intro hb
  rw [hb, Submodule.mem_bot] at hmem
  have h1 : ⟪v, f ((S.card : ℂ)⁻¹ • ∑ y ∈ S, y)⟫_ℂ = ⟪v, f x⟫_ℂ := by

    rw [map_smul, inner_smul_right, map_sum, inner_sum, Finset.sum_congr rfl hy, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]
  rw [hmem, map_zero, inner_zero_right] at h1
  exact h0 h1.symm

private theorem trace_ne [MeasurableSpace G] [BorelSpace G] (m : Measure G) [m.IsHaarMeasure]
    (τ : Representation ℂ G X) (J : Subgroup G) (hJ : CO J) (hx : fixedVectors τ J ≠ ⊥) {s : ℂ}
    (hs : HasTrace m τ ((J : Set G).indicator 1) s) : s ≠ 0 := by
  obtain ⟨A, hA, hfd, rfl⟩ := hs
  have hmeas : MeasurableSet (J : Set G) := hJ.2.measurableSet
  set c : ℂ := (m.real (J : Set G) : ℂ) with hcdef
  have hc : c ≠ 0 := by
    have h1 : 0 < m (J : Set G) := hJ.2.measure_pos m ⟨1, J.one_mem⟩
    have h2 : m (J : Set G) < ⊤ := hJ.1.measure_lt_top
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos h1.ne' h2.ne).ne'
  have hfix : ∀ y ∈ fixedVectors τ J, A y = c • y := fun y hy => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, (hA y l).2, map_smul, smul_eq_mul, sub_eq_zero]
    have e : (fun g => (J : Set G).indicator (1 : G → ℂ) g * l (τ g y)) = (J : Set G).indicator (fun _ => l y) := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, Pi.one_apply, one_mul, hy g hg]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
    rw [e, integral_indicator hmeas, setIntegral_const]
    simp [hcdef]
  have hran : ∀ v, A v ∈ fixedVectors τ J := fun v h hh => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero]
    change (l ∘ₗ τ h) (A v) = _
    rw [(hA v (l ∘ₗ τ h)).2, (hA v l).2]
    refine Eq.trans ?_ (integral_mul_left_eq_self (μ := m) (fun g => (J : Set G).indicator (1 : G → ℂ) g * l (τ g v)) h)
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have hi : (J : Set G).indicator (1 : G → ℂ) (h * g) = (J : Set G).indicator (1 : G → ℂ) g := by
      by_cases hg : g ∈ J
      · rw [Set.indicator_of_mem (show h * g ∈ (J : Set G) from J.mul_mem hh hg),
          Set.indicator_of_mem (show g ∈ (J : Set G) from hg)]
        rfl
      · rw [Set.indicator_of_notMem (show h * g ∉ (J : Set G) from fun e => hg ((Subgroup.mul_mem_cancel_left J hh).1 e)),
          Set.indicator_of_notMem (show g ∉ (J : Set G) from hg)]
    show (J : Set G).indicator (1 : G → ℂ) g * l (τ h (τ g v)) = (J : Set G).indicator (1 : G → ℂ) (h * g) * l (τ (h * g) v)
    rw [hi, map_mul, Module.End.mul_apply]
  obtain ⟨x, hxf, hx0⟩ := (Submodule.ne_bot_iff _).1 hx
  have hxr : x ∈ LinearMap.range A :=
    ⟨c⁻¹ • x, by rw [map_smul, hfix x hxf, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  have hres : A.restrict (p := LinearMap.range A) (q := LinearMap.range A) (fun v _ => LinearMap.mem_range_self A v) =
      c • LinearMap.id := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    obtain ⟨z, hz⟩ := y.2
    exact hfix y.1 (hz ▸ hran z)
  haveI : FiniteDimensional ℂ (LinearMap.range A) := hfd
  haveI : Nontrivial (LinearMap.range A) :=
    ⟨⟨⟨x, hxr⟩, 0, fun e => hx0 (congrArg Subtype.val e)⟩⟩
  rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul]
  exact mul_ne_zero hc (Nat.cast_ne_zero.2 Module.finrank_pos.ne')

end Abs

theorem UpperTheory.ConvolutionTheory.T.unitTrace :
    UpperTheory.ConvolutionTheory.T.UnitTrace := by
  intro K _ _ n μ _ V hV w _ _ m hm τ J hocc hJ hne
  haveI := hm
  have hcl : IsClosed (J : Set (Gw n w)) := J.isClosed_of_isOpen hJ.2
  have hind : ∀ u ∈ J, ∀ g, (J : Set (Gw n w)).indicator (1 : Gw n w → ℂ) (u * g) = (J : Set (Gw n w)).indicator 1 g ∧
      (J : Set (Gw n w)).indicator (1 : Gw n w → ℂ) (g * u) = (J : Set (Gw n w)).indicator 1 g := by
    intro u hu g
    have h1 : u * g ∈ J ↔ g ∈ J := Subgroup.mul_mem_cancel_left J hu
    have h2 : g * u ∈ J ↔ g ∈ J := Subgroup.mul_mem_cancel_right J hu
    by_cases hg : g ∈ J
    · rw [Set.indicator_of_mem (show u * g ∈ (J : Set (Gw n w)) from h1.2 hg),
        Set.indicator_of_mem (show g * u ∈ (J : Set (Gw n w)) from h2.2 hg),
        Set.indicator_of_mem (show g ∈ (J : Set (Gw n w)) from hg)]
      exact ⟨rfl, rfl⟩
    · rw [Set.indicator_of_notMem (show u * g ∉ (J : Set (Gw n w)) from fun e => hg (h1.1 e)),
        Set.indicator_of_notMem (show g * u ∉ (J : Set (Gw n w)) from fun e => hg (h2.1 e)),
        Set.indicator_of_notMem (show g ∉ (J : Set (Gw n w)) from hg)]
      exact ⟨rfl, rfl⟩
  have htest : Test ((J : Set (Gw n w)).indicator (1 : Gw n w → ℂ)) := by
    refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro hJ.1 fun x hx => Set.indicator_of_notMem hx _⟩
    by_cases hx : x ∈ (J : Set (Gw n w))
    · exact ⟨_, hJ.2, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
    · exact ⟨_, hcl.isOpen_compl, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  have hfix : fixedVectors τ.ρ J ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
    have hvJ : ∀ u ∈ J, locU μ w u v = v := by
      have h1 : v ∈ fixU (locU μ w) J := by
        rw [fixU_locU]
        exact hv.2
      exact h1
    by_contra hbot
    have hle : spanAll τ.ρ (locU μ w) V ≤ (ℂ ∙ v)ᗮ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, hf, x, rfl⟩
      refine Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_
      by_contra h
      exact fixed_of_inner (locU μ w) τ.ρ (fun x => τ.smooth x) J hJ.1 f hf.map v hvJ x h hbot
    have h2 := Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _)
      (UpperTheory.summand_le_closure_span_local_type_images K n μ V w τ hV hocc hv.1)
    exact hv0 (inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 h2))
  obtain ⟨-, -, h3⟩ := UpperTheory.ConvolutionTheory.C.occursBasics K n μ V w m hV
  obtain ⟨s, hs⟩ := h3 τ hocc _ htest
  exact ⟨hfix, htest, hind, s, trace_ne m τ.ρ J hJ hfix hs, hs⟩
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

private theorem mem_fixL' {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (Gw n w)) (x : LL μ) (h : ∀ g ∈ J, rhoL μ w g x = x) : x ∈ fixL μ w J := by
  simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus]
  rintro _ ⟨g, hg, rfl⟩
  exact h g hg

private theorem exists_fixed {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V) (w : Pl K) :
    ∃ (S : Subgroup (Gw n w)) (x : LL μ), IsOpen (S : Set (Gw n w)) ∧ x ∈ V ∧ x ≠ 0 ∧ ∀ g ∈ S, rhoL μ w g x = x := by
  letI : MeasurableSpace (Gw n w) := borel _
  haveI : BorelSpace (Gw n w) := ⟨rfl⟩
  obtain ⟨⟨σ, f, hf0, hfV, hfe⟩, -, -⟩ := UpperTheory.ConvolutionTheory.C.occursBasics K n μ V w (Measure.haar) hV
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf0 (LinearMap.ext hc)
  refine ⟨{ carrier := {g | σ.ρ g x = x}
            mul_mem' := fun {a b} ha hb => by
              simp only [Set.mem_setOf_eq] at ha hb ⊢
              rw [map_mul, Module.End.mul_apply, hb, ha]
            one_mem' := by simp
            inv_mem' := fun {a} ha => by
              simp only [Set.mem_setOf_eq] at ha ⊢
              conv_lhs => rw [← ha]
              rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] },
    f x, σ.smooth x, hfV x, hx, fun g hg => ?_⟩
  rw [← hfe g x]
  exact congrArg f hg

theorem splitLev : SplitLev := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV v hv
  choose S x hSo hxV hx0 hxS using fun u : PlacesOver E v => exists_fixed μ V hV u.1
  have hsp := fun u : PlacesOver E v => (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hv u) n).1
  choose e he using hsp
  let U : Subgroup (Gw n v) := GLnLocal.integralGL (v.adicCompletion F) n ⊓
    ⨅ u : PlacesOver E v, (S u).comap (mapGL n (completionMap v u.1))
  have hUo : IsOpen (U : Set (Gw n v)) := by
    have h2 : IsOpen (⋂ u : PlacesOver E v, (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1))) := by
      refine isOpen_iInter_of_finite fun u => ?_
      have : (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1)) = (e u) ⁻¹' (S u : Set (Gw n u.1)) := by
        ext g; simp only [Set.mem_preimage, he]
      rw [this]
      exact (hSo u).preimage (e u).continuous
    have h3 : (U : Set (Gw n v)) = (GLnLocal.integralGL (v.adicCompletion F) n : Set (Gw n v)) ∩
        ⋂ u : PlacesOver E v, (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1)) := by
      ext g
      simp [U, Subgroup.mem_inf, Subgroup.mem_iInf]
    rw [h3]
    exact (GLnLocal.isOpen_integralGL _ n).inter h2
  have hUle : U ≤ GLnLocal.integralGL (v.adicCompletion F) n := inf_le_left
  have hUc : IsCompact (U : Set (Gw n v)) :=
    (GLnLocal.isCompact_integralGL _ n).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hUo) hUle
  have hinj : ∀ u : PlacesOver E v, Function.Injective (mapGL n (completionMap v u.1)) := fun u a b h =>
    (e u).injective (by rw [he, he, h])
  refine ⟨U, fun u => U.map (mapGL n (completionMap v u.1)), ⟨hUc, hUo⟩, hUle, fun u => ?_⟩
  have himg : ((U.map (mapGL n (completionMap v u.1)) : Subgroup (Gw n u.1)) : Set (Gw n u.1)) = (e u) '' (U : Set (Gw n v)) := by
    ext y
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, he]
  refine ⟨⟨?_, ?_⟩, fun g => ?_, ?_⟩
  · rw [himg]
    exact hUc.image (e u).continuous
  · rw [himg]
    exact (e u).toHomeomorph.isOpenMap _ hUo
  · exact (Subgroup.mem_map_iff_mem (hinj u)).symm
  · intro hbot
    have hmem : x u ∈ V ⊓ fixL μ u.1 (U.map (mapGL n (completionMap v u.1))) := by
      refine ⟨hxV u, mem_fixL' μ u.1 _ _ ?_⟩
      rintro _ ⟨g, hg, rfl⟩
      exact hxS u _ ((Subgroup.mem_iInf.1 hg.2) u)
    rw [hbot, Submodule.mem_bot] at hmem
    exact hx0 u hmem

end UpperTheory.ConvolutionTheory.T
end
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.ConvolutionTheory.T

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private lemma mem_fixL_iff (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) (J : Subgroup (Gw n w))
    (v : LL μ) : v ∈ fixL μ w J ↔ ∀ g ∈ J, rhoL μ w g v = v := by
  simp [fixL, fixF, rhoL, Submodule.mem_iInf, LinearMap.mem_eqLocus, Subgroup.mem_map]

private lemma co_integral (w : Pl K) : CO (GLnLocal.integralGL (w.adicCompletion K) n) :=
  ⟨GLnLocal.isCompact_integralGL _ n, GLnLocal.isOpen_integralGL _ n⟩

private lemma isChr_one {G : Type} [Group G] [TopologicalSpace G] (J : Subgroup G) : IsChr J (1 : G → ℂ) :=
  ⟨IsLocallyConstant.const (1 : ℂ), fun _ _ => by simp, fun _ _ _ _ => by simp⟩

private lemma exists_local_level (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ))
    (hV : IsSummand μ V) (w : Pl K) :
    ∃ U : Subgroup (Gw n w), CO U ∧ U ≤ GLnLocal.integralGL (w.adicCompletion K) n ∧ V ⊓ fixL μ w U ≠ ⊥ := by
  letI : MeasurableSpace (Gw n w) := borel _
  haveI : BorelSpace (Gw n w) := ⟨rfl⟩
  let P : TopologicalSpace.PositiveCompacts (Gw n w) :=
    { carrier := GLnLocal.integralGL (w.adicCompletion K) n
      isCompact' := GLnLocal.isCompact_integralGL _ n
      interior_nonempty' := by
        rw [(GLnLocal.isOpen_integralGL _ n).interior_eq]
        exact ⟨1, Subgroup.one_mem _⟩ }
  obtain ⟨⟨σ, f, hf0, hfV, hfe⟩, -, -⟩ := occursBasics K n μ V w (Measure.haarMeasure P) hV
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (LinearMap.ext h)
  let U : Subgroup (Gw n w) := stabilizerOf σ.ρ x ⊓ GLnLocal.integralGL (w.adicCompletion K) n
  have hUo : IsOpen (U : Set (Gw n w)) := by
    rw [Subgroup.coe_inf]
    exact (σ.smooth x).inter (GLnLocal.isOpen_integralGL _ n)
  have hUc : IsCompact (U : Set (Gw n w)) :=
    (GLnLocal.isCompact_integralGL _ n).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hUo)
      (by rw [Subgroup.coe_inf]; exact Set.inter_subset_right)
  refine ⟨U, ⟨hUc, hUo⟩, inf_le_right, fun hb => hx ?_⟩
  have hm : f x ∈ V ⊓ fixL μ w U := by
    refine Submodule.mem_inf.2 ⟨hfV x, (mem_fixL_iff μ w U _).2 fun g hg => ?_⟩
    rw [← hfe g x]
    exact congrArg f hg.1
  rw [hb] at hm
  exact (Submodule.mem_bot ℂ).1 hm

end UpperTheory.ConvolutionTheory.T

theorem UpperTheory.ConvolutionTheory.T.levelEx :
    UpperTheory.ConvolutionTheory.T.LevelEx := by
  intro K _ _ n μ _ V hV S hS
  choose U₀ hU₀ hU₀le hU₀ne using fun w : Pl K => exists_local_level μ V hV w
  let J : ∀ w : Pl K, Subgroup (Gw n w) := fun w =>
    if w ∈ S then U₀ w else GLnLocal.integralGL (w.adicCompletion K) n
  have hJin : ∀ w ∈ S, J w = U₀ w := fun w hw => if_pos hw
  have hJout : ∀ w, w ∉ S → J w = GLnLocal.integralGL (w.adicCompletion K) n := fun w hw => if_neg hw
  have hco : ∀ w, CO (J w) := fun w => by
    by_cases hw : w ∈ S
    · rw [hJin w hw]; exact hU₀ w
    · rw [hJout w hw]; exact co_integral w
  have hle : ∀ w, J w ≤ GLnLocal.integralGL (w.adicCompletion K) n := fun w => by
    by_cases hw : w ∈ S
    · rw [hJin w hw]; exact hU₀le w
    · rw [hJout w hw]
  have heig : ∀ w, eigL μ w (J w) 1 = fixL μ w (J w) := fun w =>
    (eigBasic K n μ w (J w) 1 (hco w) (isChr_one _)).2.1
  have hloc : ∀ w, V ⊓ eigL μ w (J w) 1 ≠ ⊥ := fun w => by
    rw [heig w]
    by_cases hw : w ∈ S
    · rw [hJin w hw]; exact hU₀ne w
    · rw [hJout w hw]; exact hS w hw
  have hall := typedEx K n μ V hV J (fun _ => 1) (fun w => ⟨hco w, isChr_one _⟩)
    ((S.finite_toSet.eventually_cofinite_notMem).mono fun w hw => ⟨hJout w hw, rfl⟩) hloc
  refine ⟨J, fun w => ⟨hco w, hle w⟩, fun hb => hall (eq_bot_iff.2 ?_)⟩
  rw [← hb]
  refine le_inf (le_inf inf_le_left ?_) ?_
  · refine inf_le_right.trans (le_iInf₂ fun w hw => (iInf_le _ w).trans ?_)
    rw [heig w, hJout w hw]
  · refine inf_le_right.trans (le_iInf₂ fun w _ => (iInf_le _ w).trans ?_)
    rw [heig w]
end
end
