module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle013
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.VolStabS.TopoMeas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Filter Topology PI.VolFromSW
open scoped TensorProduct

theorem measurable_finprod {X ι : Type} [MeasurableSpace X] [Countable ι] (f : ι → X → ℂ)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun x => ∏ᶠ i, f i x) := by
  classical
  obtain ⟨e, he⟩ := exists_injective_nat ι
  have hfin : ∀ n : ℕ, {i | e i < n}.Finite := fun n =>
    (Set.finite_lt_nat n).preimage he.injOn
  let s : ℕ → Finset ι := fun n => (hfin n).toFinset
  let A : ℕ → Set X := fun n => ⋂ i, ⋂ (_ : n ≤ e i), f i ⁻¹' {1}
  let h : ℕ → X → ℂ := fun n x => if x ∈ A n then ∏ i ∈ s n, f i x else 1
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => hf i (measurableSet_singleton 1)
  have hh : ∀ n, Measurable (h n) := fun n =>
    Measurable.ite (hA n) (Finset.measurable_prod (s n) fun i _ => hf i) measurable_const
  refine measurable_of_tendsto_metrizable hh (tendsto_pi_nhds.2 fun x => ?_)
  have hev : ∀ᶠ n in atTop, h n x = ∏ᶠ i, f i x := by
    by_cases hs : (Function.mulSupport fun i => f i x).Finite
    · obtain ⟨N, hN⟩ : ∃ N, ∀ i ∈ hs.toFinset, e i < N :=
        ⟨hs.toFinset.sup e + 1, fun i hi => Nat.lt_succ_of_le (Finset.le_sup hi)⟩
      refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      have hxA : x ∈ A n := by
        simp only [A, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
        intro i hi
        by_contra hne
        have : i ∈ hs.toFinset := by simpa using hne
        have := hN i this
        omega
      simp only [h, hxA, if_true]
      refine (finprod_eq_prod_of_mulSupport_subset _ ?_).symm
      intro i hi
      have := hN i (by simpa using hi)
      simp only [s, Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
      omega
    · refine Eventually.of_forall fun n => ?_
      have hxA : x ∉ A n := by
        intro hx
        apply hs
        refine (hfin n).subset fun i hi => ?_
        simp only [A, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] at hx
        by_contra hlt
        exact hi (hx i (not_lt.1 hlt))
      simp only [h, hxA, if_false]
      exact (finprod_of_infinite_mulSupport hs).symm
  exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem continuous_projV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    {M a : ℕ} : Continuous (projV (F := F) (E := E) v (M := M) (n := a)) :=
  continuous_pi fun x => continuous_pi fun i =>
    (PI.VolStabS.PositiveNearLattice.continuous_map_tens b (evalV F v)
      (by exact RestrictedProduct.continuous_eval v)).comp
      ((continuous_apply i).comp (continuous_apply x))

theorem measurable_adm {M a : ℕ} (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ) (hΦ : IsAdm F E Φ) :
    Measurable Φ := by
  obtain ⟨d, b, Φinf, Φf, Φv, hc, -, ⟨hSB, -, hprod⟩, hIF⟩ := hΦ
  have e1 : Φ = fun X => Φinf (projInf X) * Φf (projFin X) := funext hIF
  have e2 : Φf = fun Y => ∏ᶠ v, Φv v (projV v Y) := funext hprod
  have hf : Measurable Φf := by
    rw [e2]
    exact measurable_finprod _ fun v =>
      ((hSB v).1.continuous.comp (continuous_projV b v)).measurable
  rw [e1]
  exact ((hc.comp (PI.VolStabS.PositiveNearLattice.continuous_projInf b)).measurable).mul
    (hf.comp (PI.VolStabS.PositiveNearLattice.continuous_projFin b).measurable)

end PI.VolStabS.TopoMeas

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField MeasureTheory PI.VolFromSW

theorem measOrb_holds : MeasOrb := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet Φ hΦ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact (TopoMeas.measurable_adm Φ hΦ).comp
    (PositiveNearLattice.continuous_orbit σ J (ratTup (AF F) X0)).measurable

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter
open scoped TensorProduct

def qV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (Nat.card (𝓞 F ⧸ v.asIdeal) : ℝ)

def QvSum : Prop := ∀ (F : Type) [Field F] [NumberField F],
  Summable fun v : HeightOneSpectrum (𝓞 F) => (qV v)⁻¹ ^ 2

def ArchPos : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∃ Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φinf ∧ HasCompactSupport Φinf ∧
      ∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)) ≠ 0

def LocPos : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
    IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ∃ Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φv ∧
      ∫ X, Φv X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) ≠ 0

def DensAA : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ C : ℝ,
    ∀ᶠ v in cofinite,
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
    IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ‖∫ X, (latV b v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) - 1‖ ≤
      C * (qV v)⁻¹ ^ 2

theorem nuNeZero_of_dens (hA : ArchPos) (hL : LocPos) (hD : DensAA) (hQ : QvSum) : NuNeZero := by
  classical
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν h0
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨⟨μinf, hμinf⟩, a1⟩ := hν.2
  obtain ⟨⟨νinf, hνinf⟩, a2⟩ := a1 μinf hμinf
  obtain ⟨⟨μv, hμv⟩, a3⟩ := a2 νinf hνinf
  obtain ⟨⟨νv, hνv⟩, a4⟩ := a3 μv hμv
  obtain ⟨⟨fibInf, hfi⟩, a5⟩ := a4 νv hνv
  obtain ⟨⟨fibV, hfv⟩, a6⟩ := a5 fibInf hfi
  let b := Module.finBasis F E
  obtain ⟨C, hC⟩ := hD F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ _ b
  obtain ⟨Φinf, hcΦ, hcs, hIinf⟩ :=
    hA F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf fibInf hfi
  have hpos := fun v => hL F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v)
    (νv v) (hνv v) (fibV v) (hfv v)
  choose Φp hΦpSB hΦp using hpos
  let I : HeightOneSpectrum (𝓞 F) → ℂ := fun v =>
    ∫ X, (latV b v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 F) => C * (qV v)⁻¹ ^ 2 := (hQ F).mul_left C
  have hsmall : ∀ᶠ v in cofinite, C * (qV v)⁻¹ ^ 2 < 1 :=
    hsum.tendsto_cofinite_zero.eventually (gt_mem_nhds one_pos)
  let good : HeightOneSpectrum (𝓞 F) → Prop := fun v =>
    ‖I v - 1‖ ≤ C * (qV v)⁻¹ ^ 2 ∧ C * (qV v)⁻¹ ^ 2 < 1
  have hgood : ∀ᶠ v in cofinite, good v := by
    filter_upwards [hC, hsmall] with v hv1 hv2
    exact ⟨hv1 (μv v) (hμv v) (νv v) (hνv v) (fibV v) (hfv v), hv2⟩
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ := fun v =>
    if good v then (latV b v).indicator 1 else Φp v
  let Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ := fun Y => ∏ᶠ v, Φv v (projV v Y)
  let Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ := fun X => Φinf (projInf X) * Φf (projFin X)
  have hSB : ∀ v, IsSB (Φv v) := fun v => by
    by_cases h : good v
    · rw [show Φv v = (latV b v).indicator 1 from if_pos h]
      exact PositiveNearLattice.isSB_latV b v a M
    · rw [show Φv v = Φp v from if_neg h]
      exact hΦpSB v
  have hpure : IsPureFin b Φf Φv := by
    refine ⟨hSB, ?_, fun _ => rfl⟩
    filter_upwards [hgood] with v hv
    exact if_pos hv
  obtain ⟨-, -, heq⟩ := a6 fibV hfv _ b Φ Φinf Φf Φv hcΦ hcs hpure (fun _ => rfl)
  rw [h0, integral_zero_measure] at heq
  let Jv : HeightOneSpectrum (𝓞 F) → ℂ := fun v =>
    ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))
  have hJ0 : ∀ v, Jv v ≠ 0 := fun v => by
    by_cases h : good v
    · have e : Jv v = I v := by
        simp only [Jv, I, Φv, if_pos h]
      rw [e]
      intro hI
      have := h.1
      rw [hI, zero_sub, norm_neg, norm_one] at this
      linarith [h.2]
    · have e : Jv v = ∫ X, Φp v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) := by
        simp only [Jv, Φv, if_neg h]
      rw [e]
      exact hΦp v
  have hJs : Summable fun v => ‖Jv v - 1‖ := by
    refine Summable.of_norm_bounded_eventually hsum ?_
    filter_upwards [hgood] with v hv
    have e : Jv v = I v := by
      simp only [Jv, I, Φv, if_pos hv]
    rw [e, norm_norm]
    exact hv.1
  have hne : ∏' v, (1 + (Jv v - 1)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (fun v => by rw [add_sub_cancel]; exact hJ0 v) hJs
  simp only [add_sub_cancel] at hne
  exact mul_ne_zero hIinf hne heq.symm

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct

theorem hasCOSub_of_lat {𝕜 V : Type} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] (L : AddSubgroup V)
    (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V)) (π : 𝕜) (h0 : π ≠ 0)
    (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0)) : HasCOSub V := by
  intro N hN
  have hev : ∀ᶠ c in 𝓝 (0 : 𝕜), ∀ y ∈ (L : Set V), c • y ∈ N := by
    apply hLc.eventually_forall_of_forall_eventually
    intro y _
    have hc : Tendsto (fun p : 𝕜 × V => p.1 • p.2) (𝓝 ((0 : 𝕜), y)) (𝓝 ((0 : 𝕜) • y)) :=
      continuous_smul.tendsto _
    rw [zero_smul] at hc
    exact hc hN
  obtain ⟨k, hk⟩ := (hπ.eventually hev).exists
  have hpk : π ^ k ≠ 0 := pow_ne_zero k h0
  have he : ((L.map (DistribSMul.toAddMonoidHom V (π ^ k)) : AddSubgroup V) : Set V) =
      (fun x => π ^ k • x) '' (L : Set V) := AddSubgroup.coe_map _ _
  refine ⟨L.map (DistribSMul.toAddMonoidHom V (π ^ k)), ?_, ?_, ?_⟩
  · rw [he]
    exact (Homeomorph.smulOfNeZero (π ^ k) hpk).isOpenMap _ hLo
  · rw [he]
    exact hLc.image (continuous_const_smul _)
  · rw [he]
    rintro _ ⟨y, hy, rfl⟩
    exact hk y hy

theorem exists_pow_tendsto_zero_Fv {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fv F v, π ≠ 0 ∧ Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation' π, hπ]
  refine ⟨π, fun h => ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have h1 : Valued.v (π : v.adicCompletion F) < 1 := by
      rw [hv]
      decide
    have hlt : ‖(π : v.adicCompletion F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt

def latSub {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (a M : ℕ) :
    AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E) where
  carrier := latV (M := M) (n := a) b v
  add_mem' := by
    intro x y hx hy
    simp only [latV, Set.mem_setOf_eq] at hx hy ⊢
    intro i j k
    simp only [Pi.add_apply, map_add (f := _), Finsupp.add_apply]
    exact add_mem (hx i j k) (hy i j k)
  zero_mem' := by
    simp only [latV, Set.mem_setOf_eq]
    intro i j k
    simp only [Pi.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem _
  neg_mem' := by
    intro x hx
    simp only [latV, Set.mem_setOf_eq] at hx ⊢
    intro i j k
    simp only [Pi.neg_apply, map_neg, Finsupp.neg_apply]
    exact neg_mem (hx i j k)

theorem tensNA_holds : TensNA := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨π, h0, hπ⟩ := exists_pow_tendsto_zero_Fv v
  exact hasCOSub_of_lat (latSub (Module.finBasis F E) v a M)
    (PositiveNearLattice.isClopen_latV (Module.finBasis F E) v a M).isOpen
    (PositiveNearLattice.isCompact_latV (Module.finBasis F E) v a M) π h0 hπ

def scaledB (𝕜 : Type) {V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (L : AddSubgroup V)
    (Λ : AddSubgroup V) : Prop :=
  ∃ c : 𝕜, c ≠ 0 ∧ Λ = L.map (DistribSMul.toAddMonoidHom V c)

theorem isCOBasis_scaled {𝕜 V : Type} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] (L : AddSubgroup V)
    (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V)) (π : 𝕜) (h0 : π ≠ 0)
    (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0)) : IsCOBasis (scaledB 𝕜 L) := by
  intro N hN
  have hev : ∀ᶠ c in 𝓝 (0 : 𝕜), ∀ y ∈ (L : Set V), c • y ∈ N := by
    apply hLc.eventually_forall_of_forall_eventually
    intro y _
    have hc : Tendsto (fun p : 𝕜 × V => p.1 • p.2) (𝓝 ((0 : 𝕜), y)) (𝓝 ((0 : 𝕜) • y)) :=
      continuous_smul.tendsto _
    rw [zero_smul] at hc
    exact hc hN
  obtain ⟨k, hk⟩ := (hπ.eventually hev).exists
  have hpk : π ^ k ≠ 0 := pow_ne_zero k h0
  have he : ((L.map (DistribSMul.toAddMonoidHom V (π ^ k)) : AddSubgroup V) : Set V) =
      (fun x => π ^ k • x) '' (L : Set V) := AddSubgroup.coe_map _ _
  refine ⟨L.map (DistribSMul.toAddMonoidHom V (π ^ k)), ⟨π ^ k, hpk, rfl⟩, ?_, ?_, ?_⟩
  · rw [he]
    exact (Homeomorph.smulOfNeZero (π ^ k) hpk).isOpenMap _ hLo
  · rw [he]
    exact hLc.image (continuous_const_smul _)
  · rw [he]
    rintro _ ⟨y, hy, rfl⟩
    exact hk y hy

theorem isCOBasis_latSub {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (a M : ℕ) :
    IsCOBasis (scaledB (Fv F v) (latSub b v a M)) := by
  obtain ⟨π, h0, hπ⟩ := exists_pow_tendsto_zero_Fv v
  exact isCOBasis_scaled (latSub b v a M) (PositiveNearLattice.isClopen_latV b v a M).isOpen
    (PositiveNearLattice.isCompact_latV b v a M) π h0 hπ

def DensVLat : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
      DensCosB (scaledB (Fv F v) (latSub b v a M)) μv (gramR (Fv F v) σ J) Subtype.val νv
        {X | LinearIndependent (Fv F v ⊗[F] E) X}

theorem densVLC_of_lat (hT : TensAll) (hC : DensVLat) : DensVLC := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν
  obtain ⟨_t1, t2, _t3, _t4, _t5, _t6, _t7⟩ := (hT F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet).2 v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := hμ.1
  have := hν.1
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  exact densLC_of_cosB _ _ (isCOBasis_latSub (Module.finBasis F E) v a M)
    (hC F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν _ (Module.finBasis F E))

theorem densV_of_lat (hT : TensAll) (hC : DensVLat) : DensV :=
  densV_of hT tensNA_holds (densVLC_of_lat hT hC)

end PI.VolStabS
end
end
