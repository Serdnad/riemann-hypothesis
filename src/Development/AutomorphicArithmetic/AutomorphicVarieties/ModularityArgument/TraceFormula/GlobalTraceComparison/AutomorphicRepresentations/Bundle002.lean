module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory Filter GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.zero_pf :
    AeEq → Zero := by
  intro hAe E _ _ _ n D f I hf hinv hI h
  classical
  haveI := CuspidalL2GL.t2Space_GA E n
  haveI := CuspidalL2GL.t2Space_GA E 0
  haveI := CuspidalL2GL.locallyCompactSpace_GA E n
  haveI := CuspidalL2GL.locallyCompactSpace_GA E 0
  haveI := CuspidalL2GL.secondCountableTopology_GA E n
  haveI := CuspidalL2GL.secondCountableTopology_GA E 0
  haveI : SigmaCompactSpace (H E n 0) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
  have key : ∀ K : Set (H E n 0), IsCompact K → ∀ᵐ x ∂D.ν, x ∈ K → ldet x ∈ I → f x = 0 := by
    intro K hK
    set S : Set (H E n 0) := K ∩ ldet ⁻¹' I with hS
    have hSm : MeasurableSet S :=
      hK.isClosed.measurableSet.inter (hI.preimage continuous_ldet).measurableSet
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
    have hνS : D.ν S < ⊤ :=
      lt_of_le_of_lt ((Measure.restrict_apply_le _ _).trans (measure_mono Set.inter_subset_left))
        (hK.measure_lt_top_of_nhdsWithin fun x _ => D.μ.finiteAt_nhdsWithin x K)
    set w : H E n 0 → ℂ := S.indicator fun x => starRingEnd ℂ (f x) with hwdef
    have hw : MemLp w 2 D.ν := by
      rw [hwdef, memLp_indicator_iff_restrict hSm.nullMeasurableSet]
      haveI : IsFiniteMeasure (D.ν.restrict S) := isFiniteMeasure_restrict.2 hνS.ne
      refine MemLp.of_bound (Complex.continuous_conj.comp hf).aestronglyMeasurable B
        ((ae_restrict_iff' hSm).2 (Eventually.of_forall fun x hx => ?_))
      simpa using hB x hx.1
    have hv : (hw.toLp w : H E n 0 → ℂ) =ᵐ[D.ν] w := hw.coeFn_toLp
    have h0 := h (hw.toLp w) (hv.mono fun y hy hl => by
      rw [hy]
      exact Set.indicator_of_notMem (by exact fun hs => hl hs.2) _)
    have hpt : ∀ y, w y * f y = ((‖w y‖ ^ 2 : ℝ) : ℂ) := by
      intro y
      by_cases hy : y ∈ S
      · simp only [hwdef, Set.indicator_of_mem hy, RCLike.norm_conj]
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      · simp [hwdef, Set.indicator_of_notMem hy]
    have h1 : ∫ y, ‖w y‖ ^ 2 ∂D.ν = 0 := by
      have e : ∫ y, (hw.toLp w : H E n 0 → ℂ) y * f y ∂D.ν = ∫ y, ((‖w y‖ ^ 2 : ℝ) : ℂ) ∂D.ν :=
        integral_congr_ae (hv.mono fun y hy => by
          show (hw.toLp w : H E n 0 → ℂ) y * f y = ((‖w y‖ ^ 2 : ℝ) : ℂ)
          rw [hy, hpt])
      rw [e, integral_complex_ofReal] at h0
      exact_mod_cast h0
    have hint : Integrable (fun y => ‖w y‖ ^ 2) D.ν := hw.integrable_norm_pow two_ne_zero
    have h2 := (integral_eq_zero_iff_of_nonneg (fun y => by positivity) hint).1 h1
    refine h2.mono fun x hx hxK hxI => ?_
    have hx0 : w x = 0 := by simpa using hx
    have hxS : x ∈ S := ⟨hxK, hxI⟩
    rw [hwdef, Set.indicator_of_mem hxS] at hx0
    simpa using hx0
  have all : ∀ᵐ x ∂D.ν, ∀ m : ℕ, x ∈ compactCovering (H E n 0) m → ldet x ∈ I → f x = 0 :=
    ae_all_iff.2 fun m => key _ (isCompact_compactCovering _ m)
  refine hAe E n D f (fun _ => 0) I hf continuous_const hinv (fun _ _ => rfl) hI (all.mono fun x hx hl => ?_)
  obtain ⟨m, hm⟩ := exists_mem_compactCovering x
  exact hx m hm hl
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.evalBasis_pf :
    EvalBasis := by
  intro X V _ _ ev hsep W hW
  classical
  haveI := hW
  let r : X → Module.Dual ℂ W := fun x => (ev x).domRestrict W
  have hspan : Submodule.span ℂ (Set.range r) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    obtain ⟨v, rfl⟩ := (Module.evalEquiv ℂ W).surjective f
    have hv : (v : V) = 0 := hsep v fun x => by
      have h := hf (Submodule.subset_span (Set.mem_range_self x))
      simpa [r] using h
    have hv0 : v = 0 := Subtype.ext hv
    exact hf0 (by simp [hv0])
  obtain ⟨b, hbs, hbspan, hli⟩ := exists_linearIndependent ℂ (Set.range r)
  let B0 := Module.Basis.mk hli (by simp [hbspan, hspan])
  haveI : Finite b := Module.Finite.finite_basis B0
  letI := Fintype.ofFinite b
  let B := B0.reindex (Fintype.equivFin b)
  have hx : ∀ i, ∃ x, r x = B i := fun i => by
    have hm : B i ∈ b := by simp [B, B0]
    exact hbs hm
  choose x hx using hx
  refine ⟨Fintype.card b, x, fun i => ((Module.evalEquiv ℂ W).symm (B.coord i) : W),
    fun i => Subtype.coe_prop _, fun v hv => ?_⟩
  have key : (⟨v, hv⟩ : W) = ∑ i, (B i ⟨v, hv⟩) • (Module.evalEquiv ℂ W).symm (B.coord i) := by
    apply (Module.evalEquiv ℂ W).injective

    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    exact (B.sum_dual_apply_smul_coord _).symm
  have h2 := congrArg (Subtype.val) key
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  refine h2.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [← hx i]
  rfl
end

section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem trFin_pf : TrFin := by
  intro V B _ _ _ L w e h
  classical
  have hr : ∀ r : LinearMap.range L, (r : V) = ∑ b, e b (r : V) • w b := by
    rintro ⟨_, v, rfl⟩
    exact h v
  let A : LinearMap.range L →ₗ[ℂ] (B → ℂ) :=
    LinearMap.pi fun b => (e b).comp (LinearMap.range L).subtype
  let c : (B → ℂ) →ₗ[ℂ] LinearMap.range L :=
    L.rangeRestrict.comp (Fintype.linearCombination ℂ w)
  have hA : Function.Injective A := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr0
    apply Subtype.ext
    rw [hr r]
    have hz : ∀ b, e b (r : V) = 0 := fun b => congrFun hr0 b
    simp [hz]
  haveI : FiniteDimensional ℂ (LinearMap.range L) := FiniteDimensional.of_injective A hA
  have hL : (L.restrict fun x _ => LinearMap.mem_range_self L x) = c ∘ₗ A := by
    ext r
    have h1 : (c (A r) : V) = L (∑ b, e b (r : V) • w b) := by
      simp [c, A, Fintype.linearCombination_apply]
    rw [LinearMap.comp_apply, h1, ← hr r]
    rfl
  rw [hL, LinearMap.trace_comp_comm', LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ B)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [c, A, Fintype.linearCombination_apply, Pi.single_apply, ite_smul]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.supp_pf :
    Basic → Zero → KInv → PSupp → Ker → Supp := by
  intro hB hZ hK hP hKer E _ _ _ n ι _ s m R hR x y hxy
  obtain ⟨hac, hmul, -, -, hone, -, hldth, hthth, hthmul, hrat, -, hthc⟩ := hB E n s.pos
  have hl1 : ldet (1 : H E n 0) = 0 := by
    have h := hac 0
    rwa [hone] at h
  have hlinv : ∀ z : H E n 0, ldet z⁻¹ = -ldet z := by
    intro z
    have h := hmul z z⁻¹
    rw [mul_inv_cancel, hl1] at h
    linarith
  have hf : Continuous fun w : H E n 0 => m.G x (th w) := by
    show Continuous fun w : H E n 0 => ∑ i, inner ℂ (s.k₁ x i) (m.Uπ (s.k₂ (th w) i))
    refine continuous_finsetSum _ fun i _ => ?_
    exact continuous_const.inner (m.Uπ.continuous.comp (((s.vecs.cont i).2).comp hthc))
  have hinv : Inv fun w : H E n 0 => m.G x (th w) := by
    intro γ w
    have h := (hK E n ι s).2 ⟨th (γ : H E n 0), (hrat γ).2⟩ (th w)
    show Gk s.k₁ s.k₂ m.Uπ x (th ((γ : H E n 0) * w)) = Gk s.k₁ s.k₂ m.Uπ x (th w)
    rw [hthmul]
    unfold Gk
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show s.k₂ (th (γ : H E n 0) * th w) = s.k₂ (th w) from h]
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = (|ldet x + ldet y| - R) / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have key := hZ E n s.D (fun w => m.G x (th w)) (Set.Ioo (-ldet y - δ) (-ldet y + δ)) hf hinv isOpen_Ioo ?_ (th y) ?_
  · simpa only [hthth] using key
  · intro v hv
    refine ((hKer E n ι s m v x).2).trans ?_
    have hPv := hP E n s.D s.π (-ldet y - δ) (-ldet y + δ) v
      (hv.mono fun w h h' => h fun hI => h' (Set.Ioo_subset_Icc_self hI))
    apply integral_eq_zero_of_ae
    filter_upwards [hPv] with w hw
    by_cases hI : ldet w ∈ Set.Icc (-ldet y - δ) (-ldet y + δ)
    · have hk : kerH m.φ x w = 0 := by
        unfold kerH
        refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
        by_contra hne
        have h1 := hR _ hne
        rw [hmul, hmul, hlinv, (hrat γ).1] at h1
        obtain ⟨a1, a2⟩ := abs_le.mp h1
        obtain ⟨b1, b2⟩ := hI
        rcases abs_cases (ldet x + ldet y) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hδ <;> linarith
      simp [hk]
    · simp [hw hI]
  · rw [hldth]
    exact ⟨by linarith, by linarith⟩
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.diagInt_pf :
    GFac → HalfTerm → DiagInt := by
  intro hF hH
  unfold DiagInt ForSu
  intro E _ _ _ n ι _ s m
  obtain ⟨p, hp⟩ := hF E n ι s
  have hb := fun b => (hH E n ι s m (p.w b) (p.mem b) (p.x b) (p.zero b)).1
  have hsum := MeasureTheory.integrable_finsetSum (Finset.univ : Finset p.B) fun b _ => hb b
  refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Finset.sum_apply]
  exact (hp m x x).symm
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private def evAt {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (π : CuspSub E n) (x : H E n 0) :
    π.V →ₗ[ℂ] ℂ where
  toFun ψ := ψ.1.1 x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.finFac_pf :
    Basic → EvalBasis → FinGen → FinFac := by
  intro hB hE hG E _ _ _ n ι _ s
  obtain ⟨hl, hmul, -⟩ := hB E n s.pos
  obtain ⟨W, hWV, hWf, hW⟩ := hG E n ι s
  have sep : ∀ ψ : s.π.V, (∀ x : {x : H E n 0 // ldet x = 0}, evAt s.π x.1 ψ = 0) → ψ = 0 := by
    intro ψ h
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    have hy : ldet (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)) = 0 := by
      rw [hmul, hl]; ring
    have h0 := h ⟨_, hy⟩
    have h1 := s.fix.1 ψ.1 ψ.2 (-ldet ((g, 1) : H E n 0) / (n * Module.finrank ℚ E)) g
    exact h1.symm.trans h0
  haveI : FiniteDimensional ℂ W := hWf
  obtain ⟨d, xs, ws, hw, hrep⟩ := hE {x : H E n 0 // ldet x = 0} s.π.V (fun x => evAt s.π x.1) sep
    (LinearMap.range (Submodule.inclusion hWV)) inferInstance
  refine ⟨{ B := Fin d, w := fun b => (ws b).1, x := fun b => (xs b).1, mem := fun b => (ws b).2,
            zero := fun b => (xs b).2 }, ?_⟩
  have key : ∀ v : Hs (ι := ι) s.D, IsPiVec s.D s.π v → ∀ (x : H E n 0) (i : ι),
      inner ℂ (s.k₁ x i) v =
        ∑ b, (ws b).1.1 x.1 * inner ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i) v := by
    intro v hv x i
    obtain ⟨ψ, hψ, hval⟩ := hW v hv i (ldet x)
    have hb : ∀ b, inner ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i) v = ψ.1 (xs b).1.1 := by
      intro b
      rw [hval _ (by rw [hmul, hl, (xs b).2, add_zero])]
      exact s.fix.1 ψ (hWV hψ) _ _
    have hr := congrArg (evAt s.π x) (hrep ⟨ψ, hWV hψ⟩ ⟨⟨ψ, hψ⟩, rfl⟩)

    rw [map_sum] at hr
    rw [hval x rfl]
    refine hr.trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [map_smul, hb b, smul_eq_mul, mul_comm]
    rfl
  intro v hv x i
  let L : Hs (ι := ι) s.D →L[ℂ] ℂ := innerSL ℂ (s.k₁ x i) -
    ∑ b, (ws b).1.1 x.1 • innerSL ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i)
  have hL : ∀ f, L f = inner ℂ (s.k₁ x i) f -
      ∑ b, (ws b).1.1 x.1 * inner ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i) f := by
    intro f
    simp [L, ContinuousLinearMap.sum_apply]
  have hle : Submodule.span ℂ {f | IsPiVec s.D s.π f} ≤ LinearMap.ker (L : Hs (ι := ι) s.D →ₗ[ℂ] ℂ) :=
    Submodule.span_le.2 fun f hf => by
      have := key f hf x i
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      rw [hL, this, sub_self]
  have hv' : v ∈ closure ((Submodule.span ℂ {f | IsPiVec s.D s.π f} : Submodule ℂ (Hs (ι := ι) s.D)) : Set (Hs (ι := ι) s.D)) := hv
  have h0 : L v = 0 :=
    closure_minimal (t := {f | L f = 0}) (fun f hf => LinearMap.mem_ker.1 (hle hf))
      (isClosed_eq L.continuous continuous_const) hv'
  rw [hL] at h0
  exact sub_eq_zero.1 h0

end
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1 GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.uncutOf_pf :
    Basic → GFac → HalfTerm → RangeW → TrFin → DiscreteGroups.T1.G.UncutHalf := by
  intro hB hF hH hR hT E _ _ _ n hn D π hπ ι _ Φ₁ Φ₂ T₁ T₂ M k₁ k₂ a1 a2 hfin b1 b2 hv U Uπ Φ t c1 c2 hpi ht
  let s : Su E n ι := ⟨D, π, Φ₁, Φ₂, T₁, T₂, M, k₁, k₂, hn, hπ, a1, a2, hfin, b1, b2, hv⟩
  let m : Mid s := ⟨U, Uπ, Φ, c1, c2, hpi⟩
  obtain ⟨p, hp⟩ := hF E n ι s
  obtain ⟨hac, hmul, -⟩ := hB E n hn
  have hsum : lInt0 D k₁ k₂ Uπ = fun x => ∑ b, (p.w b).1 x.1 * m.G (ac E n (ldet x) * p.x b) x :=
    funext fun x => hp m x x
  have hterm := fun b => hH E n ι s m (p.w b) (p.mem b) (p.x b) (p.zero b)
  obtain ⟨L, hL, -, rfl⟩ := ht
  let w : p.B → π.V := fun b => ⟨p.w b, p.mem b⟩
  let e : p.B → (π.V →ₗ[ℂ] ℂ) := fun b =>
    { toFun := fun ψ => ψ.1.1 (p.x b).1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hcentre : ∀ (ψ : Sm E n), ψ ∈ π.V → ∀ g : GA E n,
      ψ.1 (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)).1 = ψ.1 g := by
    intro ψ hψ g
    exact hπ.1 ψ hψ _ g
  have hspan : ∀ v, L v = ∑ b, e b (L v) • w b := by
    intro v
    apply Subtype.ext
    apply Subtype.ext
    funext g
    have h0 : ldet (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)) = 0 := by
      rw [hmul, hac]; ring
    have h1 := hR E n ι s p hp m v.1 v.2 _ h0
    have h2 : (L v).1.1 g = ∑ b, (L v).1.1 (p.x b).1 * (p.w b).1 g := by
      rw [← hcentre (L v).1 (L v).2 g, hL v]
      refine h1.trans (Finset.sum_congr rfl fun b _ => ?_)
      rw [hcentre _ (p.mem b), hL v, mul_comm]
      rfl
    let ev : π.V →ₗ[ℂ] ℂ :=
      { toFun := fun ψ => ψ.1.1 g, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have h3 : (∑ b, e b (L v) • w b).1.1 g = ev (∑ b, e b (L v) • w b) := rfl

    rw [h3, map_sum]
    exact h2
  have htr := hT π.V p.B L w e hspan
  refine ⟨?_, ?_⟩
  · rw [hsum]
    exact integrable_finsetSum _ fun b _ => (hterm b).1
  · rw [hsum, integral_finsetSum _ fun b _ => (hterm b).1, htr, Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [(hterm b).2]
    congr 1
    exact (hL (w b) (p.x b).1).symm
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.dropP_pf :
    Zero → KInv → Basic → Weak → PointRep → PComm → DropP := by
  intro hZ hK hB hW hR hC E _ _ _ n ι _ s m x y
  classical
  obtain ⟨-, -, -, -, -, -, -, hthth, hthmul, hrat, -, hthc⟩ := hB E n s.pos
  set S := piSp s.D s.π ι with hS
  set P := S.starProjection with hP
  have hmem : ∀ f, P f ∈ S := fun f => Submodule.starProjection_apply_mem S f
  have hPP : ∀ f, P (P f) = P f := fun f => (Submodule.starProjection_eq_self_iff).2 (hmem f)
  have hUπ : ∀ f, m.Uπ f = m.U (P f) := fun f => by
    have h2 : f - P f ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal f
    have hdec : P f + (f - P f) = f := by abel
    calc m.Uπ f = m.Uπ (P f + (f - P f)) := by rw [hdec]
      _ = m.U (P f) := by rw [map_add (f := _), m.pp.1 _ (hmem f), m.pp.2 _ h2, add_zero]
  have C₁ : ∀ f, P (s.T₁ f) = s.T₁ (P f) := hC E n s.pos s.D s.π s.fix ι s.Φ₁ s.T₁ s.t₁ s.o₁
  have C₂ : ∀ f, P (s.T₂ f) = s.T₂ (P f) := hC E n s.pos s.D s.π s.fix ι s.Φ₂ s.T₂ s.t₂ s.o₂
  have C₃ : ∀ f, P ((s.T₁ * m.U * s.T₂) f) = (s.T₁ * m.U * s.T₂) (P f) := hC E n s.pos s.D s.π s.fix ι m.Φ (s.T₁ * m.U * s.T₂) m.t m.o
  set Q : Hs (ι := ι) s.D →L[ℂ] Hs (ι := ι) s.D := (ContinuousLinearMap.id ℂ _ - P) ∘L m.Uπ with hQ
  have hQa : ∀ f, Q f = m.Uπ f - P (m.Uπ f) := fun f => rfl
  have key : ∀ g, s.T₁ (Q (s.T₂ g)) = 0 := fun g => by
    have e : s.T₁ (m.U (s.T₂ (P g))) = (s.T₁ * m.U * s.T₂) (P g) := rfl
    rw [hQa, map_sub, ← C₁, hUπ, C₂, e, ← C₃, hPP, sub_self]
  have hz : ∀ g i, inner ℂ (s.k₁ x i) (Q (s.T₂ g)) = 0 := fun g i => by
    have h0 := hR E n ι s s.Φ₁ s.T₁ s.t₁ s.o₁ (Q (s.T₂ g)) 0 (by rw [map_zero]; exact key g) x i
    rw [h0]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj : (((0 : Hs (ι := ι) s.D) j : Lp ℂ 2 s.D.ν) : H E n 0 → ℂ) =ᵐ[s.D.ν] 0 := Lp.coeFn_zero _ _ _
    rw [integral_congr_ae (g := fun _ => (0 : ℂ)) (hj.mono fun z hz => by rw [hz]; simp)]
    simp
  set f : H E n 0 → ℂ := fun z => ∑ i, inner ℂ (s.k₁ x i) (Q (s.k₂ (th z) i)) with hf
  have hfc : Continuous f := continuous_finsetSum _ fun i _ =>
    continuous_const.inner (Q.continuous.comp ((s.vecs.cont i).2.comp hthc))
  have hfi : Inv f := fun γ z => by
    have h := (hK E n ι s).2 ⟨th (γ : H E n 0), (hrat γ).2⟩ (th z)
    simp only [hf, hthmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show s.k₂ (th (γ : H E n 0) * th z) = s.k₂ (th z) from h]
  have hf0 := hZ E n s.D f Set.univ hfc hfi isOpen_univ (fun v _ => by
    have hw := fun i => hW E n ι s v (ContinuousLinearMap.adjoint Q (s.k₁ x i)) i
    have hpt : ∀ z, (v : H E n 0 → ℂ) z * f z =
        ∑ i, (v : H E n 0 → ℂ) z * inner ℂ (ContinuousLinearMap.adjoint Q (s.k₁ x i)) (s.k₂ (th z) i) := fun z => by
      simp only [hf, Finset.mul_sum, ContinuousLinearMap.adjoint_inner_left]
    simp only [hpt]
    rw [integral_finsetSum _ fun i _ => (hw i).1]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(hw i).2, ContinuousLinearMap.adjoint_inner_left]
    exact hz _ i)
  have h1 := hf0 (th y) (Set.mem_univ _)
  simp only [hf, hthth, hQa, inner_sub_right, Finset.sum_sub_distrib] at h1
  exact sub_eq_zero.1 h1
end
