module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle985
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle087
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle995
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle988
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle572
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle583
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle993
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle979
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle578
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CompIntField
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coverForm_rational_descent_to_base : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ φ ∈ C.ratForms (wtA (κ i)) (κ i).n, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) ∧ φ = ∑ a, C.σ₂ (x a) • ψ a := by
  first | exact @GlobalTheory.CoverDescRat.cover_desc_rat | exact GlobalTheory.CoverDescRat.cover_desc_rat | (intros; apply GlobalTheory.CoverDescRat.cover_desc_rat <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.XiIntSteps

theorem exists_local_basis {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) {V : Type} [AddCommGroup V]
    [Module F V] (C : Submodule F V) [FiniteDimensional F C] (Int : V → Prop) (h0 : Int 0)
    (hadd : ∀ f g, Int f → Int g → Int (f + g)) (hsmul : ∀ (a : F) f, p.valuation F a ≤ 1 → Int f → Int (a • f))
    (hbd : ∀ f ∈ C, ∃ κ : F, κ ≠ 0 ∧ Int (κ • f)) {M : ℕ} (g : Fin M → V) (hg : ∀ i, g i ∈ C)
    (hgen : ∀ f ∈ C, Int f → ∃ o : Fin M → F, (∀ i, p.valuation F (o i) ≤ 1) ∧ f = ∑ i, o i • g i) :
    ∃ (m : ℕ) (β : Fin m → V), (∀ k, β k ∈ C ∧ Int (β k)) ∧ (∀ f ∈ C, ∃ c : Fin m → F, f = ∑ k, c k • β k) ∧
      ∀ c : Fin m → F, Int (∑ k, c k • β k) → ∀ k, p.valuation F (c k) ≤ 1 := by
  classical
  let B₀ := Module.finBasis F C
  choose κ hκ0 hκ using fun i => hbd (B₀ i : V) (B₀ i).2
  let B := B₀.unitsSMul fun i => Units.mk0 (κ i) (hκ0 i)
  have hB : ∀ i, ((B i : C) : V) = κ i • (B₀ i : V) := fun i => by
    simp [B, Module.Basis.unitsSMul_apply, Units.smul_def]
  let e : (Fin (Module.finrank F C) → F) →ₗ[F] V := C.subtype ∘ₗ (B.equivFun.symm : _ →ₗ[F] C)
  have heC : ∀ x, e x ∈ C := fun x => (B.equivFun.symm x).2
  have he1 : ∀ f : C, e (B.equivFun f) = f := fun f => by simp [e]
  have heinj : Function.Injective e := Subtype.val_injective.comp B.equivFun.symm.injective
  have hsingle : ∀ i, e (Pi.single i 1) = κ i • (B₀ i : V) := fun i => by
    rw [← hB, ← he1 (B i)]
    congr 1
    funext k
    simp [Module.Basis.equivFun_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
  let S : Set (Fin (Module.finrank F C) → F) := {x | Int (e x)}
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F))
    (fun ki : Fin M × Fin (Module.finrank F C) => B.equivFun ⟨g ki.1, hg ki.1⟩ ki.2)
  have hvle : ∀ s : 𝓞 F, p.valuation F (algebraMap (𝓞 F) F s) ≤ 1 := fun s => by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact p.intValuation_le_one s
  obtain ⟨m, b, hbM, hbsp, hbli⟩ := GlobalTheory.T.exists_basis_bounded_module_valuationRing_pi p _ S (by show Int (e 0); rw [map_zero]; exact h0)
    (fun x hx y hy => by show Int (e (x + y)); rw [map_add (f := _)]; exact hadd _ _ hx hy)
    (fun a ha x hx => by show Int (e (a • x)); rw [map_smul]; exact hsmul _ _ ha hx)
    (fun i => by show Int (e _); rw [hsingle]; exact hκ i)
    ⟨algebraMap (𝓞 F) F d, (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (nonZeroDivisors.coe_ne_zero d),
      fun x hx i => by
        obtain ⟨o, ho, hxo⟩ := hgen (e x) (heC x) hx
        have hx' : x = ∑ k, o k • B.equivFun ⟨g k, hg k⟩ := heinj (by

          rw [hxo, map_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [map_smul, he1])
        rw [hx', Finset.sum_apply, Finset.mul_sum]
        refine Valuation.map_sum_le _ fun k _ => ?_
        obtain ⟨r, hr⟩ := hd (k, i)
        rw [Pi.smul_apply, smul_eq_mul, mul_left_comm, map_mul, ← Algebra.smul_def]
        refine mul_le_one' (ho k) ?_
        rw [← hr]
        exact hvle r⟩
  refine ⟨m, fun k => e (b k), fun k => ⟨heC _, hbM k⟩, fun f hf => ?_, fun c hc k => ?_⟩
  · have hxsp : B.equivFun ⟨f, hf⟩ ∈ Submodule.span F (Set.range b) := by
      rw [← Finset.univ_sum_single (B.equivFun ⟨f, hf⟩)]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : Pi.single i (B.equivFun ⟨f, hf⟩ i) = B.equivFun ⟨f, hf⟩ i • (Pi.single i (1 : F) : Fin _ → F) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this]
      refine Submodule.smul_mem _ _ ?_
      obtain ⟨a, -, ha⟩ := hbsp (Pi.single i 1) (by show Int (e _); rw [hsingle]; exact hκ i)
      rw [ha]; exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hxsp
    refine ⟨c, ?_⟩
    have := he1 ⟨f, hf⟩

    rw [← hc, map_sum] at this
    exact this.symm.trans (Finset.sum_congr rfl fun k _ => map_smul _ _ _)
  · have hy : (∑ k, c k • b k) ∈ S := by
      show Int (e _)
      convert hc using 1

      rw [map_sum]; exact Finset.sum_congr rfl fun k _ => map_smul _ _ _
    obtain ⟨a, ha, hya⟩ := hbsp _ hy
    have hz : ∑ k, (c k - a k) • b k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]; rw [← hya, sub_self]
    rw [sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hbli _ hz k)]
    exact ha k

theorem intForm_descent_below (l e : ℕ) (hl : l.Prime) : ∃ c₀ : ℕ, ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j →
    ∀ w : WeightFamilies.Wt D j, w.LastPos → Dom (wtA w) w.n →
    holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) ≤ Submodule.span ℂ (rdU (T.U j T.σ₀) ''
      {f | f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ rdU (T.U j T.σ₀) f ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)}) →
    (∀ k ∈ T.Kf j T.σ₀, ∀ h, T.mu j T.σ₀ (h * k) = T.mu j T.σ₀ h) →
    ∀ C : Cover T j T.σ₀, C.IsUnif → C.IsPinned (wtA w) w.n →
    ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (p : HeightOneSpectrum (𝓞 T.Q.c.F)),
      la.asIdeal.comap (RingOfIntegers.mapRingHom C.inc) = p.asIdeal →
      ((l : ℕ) : 𝓞 C.d.c₂.F) ∈ la.asIdeal → ((l : ℕ) : 𝓞 C.d.c₂.F) ∉ la.asIdeal ^ (e + 1) →
      ∀ φ ∈ C.intForms (wtA w) w.n {la}, (∀ k ∈ T.Kf j T.σ₀, ∀ h, φ (h * k) = φ h) →
        ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V j T.σ₀) → ℂ)), (∀ i, la.valuation C.d.c₂.F (x i) ≤ 1) ∧
          (∀ i, ψ i ∈ baseInt T j T.σ₀ (wtA w) w.n {p}) ∧ ((l : ℂ) ^ c₀) • φ = ∑ i, C.σ₂ (x i) • ψ i := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.relative_different_order_bounded_absolute_ramification l e hl
  refine ⟨c, ?_⟩
  intro D T hL j hj w hlast hD hspan hK C hU hP la p hp0 hl1 hl2 φ hφ hφK
  letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra
  have hp : la.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal := by
    rw [← hp0]; ext x; rfl
  have hσ := T.toCore.good_σ₀
  have hlp : ((l : ℕ) : 𝓞 T.Q.c.F) ∈ p.asIdeal := by
    rw [← hp0, Ideal.mem_comap, map_natCast]; exact hl1
  have hgood : T.Q.l.GoodAt l :=
    Formalism.L2.Pj.goodAt_of_two_primes hL.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne l hl
  have hfd := hL.cuspFD _ hj _ _ hD
  obtain ⟨M, g, hg, hgen⟩ := GlobalTheory.SupFinite.supSet_finitelyGenerated _ _ _ _ (T.Q.Xo j) T.Q.c _ (T.U j) (hL.unf _ hj) p l hl hlp
    hgood (wtA w) w.n hD hfd
  have hval := GlobalTheory.TowVal.bddAll_one_iff_valSet_nonneg _ _ _ _ (T.Q.Xo j) T.Q.c p
  obtain ⟨m, β, hβ, hspanβ, hprim⟩ := exists_local_basis p (cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n)
    (GlobalTheory.GoodPts.BddAll (T.Q.Xo j) T.Q.c p 1)
    ((hval 0).2 (by rintro _ ⟨y, rfl⟩; rw [vAtV_zero]; exact le_top))
    (fun f g => GlobalTheory.GoodPtsModel.bddAll_add)
    (fun a f ha hf => by
      by_cases h0 : a = 0
      · subst h0
        set_option synthInstance.maxHeartbeats 100000 in
          rw [zero_smul]
        exact (hval 0).2 (by rintro _ ⟨y, rfl⟩; rw [vAtV_zero]; exact le_top)
      have hv : (0 : ℤ) ≤ vLa p a := by
        have hne : p.valuation T.Q.c.F a ≠ 0 := (Valuation.ne_zero_iff _).2 h0
        have := (WithZero.log_le_log hne one_ne_zero).2 ha
        simp only [WithZero.log_one] at this
        simp only [vLa]; omega
      exact (GlobalTheory.GoodPtsModel.smul_mem_supSet (W := ⊤) hv ⟨trivial, hf⟩).2)
    (fun f hf => by
      obtain ⟨κ, h1, h2⟩ := GlobalTheory.T.cuspidal_section_bounded_nonzero_multiple _ _ _ _ (T.Q.Xo j) T.Q.c _ (T.U j) (hL.unf _ hj) p l hl hlp hgood (wtA w) w.n f hD hf
      exact ⟨κ, h1, (GlobalTheory.GoodPtsModel.bddAll_iff_smul _ _).1 h2⟩)
    g (fun i => (hg i).1) (fun f hf hb => hgen f ⟨hf, hb⟩)
  have hβs : ∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧
      rdU (T.U j T.σ₀) (β k) ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) := fun k =>
    ⟨cusp_le_sec _ _ _ _ _ (hβ k).1, ReciprocityTheory.ChartRestriction.G.PullbackSections.rdC_mem_holSub0 T.good_σ₀ (wtA w) w.n ⟨β k, (hβ k).1⟩⟩
  obtain ⟨m', x, ψ, hψ, hφe⟩ := GlobalTheory.T.holomorphic_sections_span_restriction D T hL j hj T.σ₀ hσ C hU _ _ hD hP hspan hK φ
    (C.intForms_subset _ _ _ hφ) hφK
  have hcc' : ∀ i, ∃ cc : Fin m → T.Q.c.F, ψ i = ∑ k, T.σ₀ (cc k) • T.phiJ j T.σ₀ (wtA w) (β k) := fun i => by
    obtain ⟨f, hf, hfe⟩ := hψ i
    obtain ⟨cc, hcc⟩ := hspanβ f (GlobalTheory.T.mem_cuspForms_allEmbeddings_of_inclusion_reading D T hL j hj w hlast f hf.1 hf.2)
    refine ⟨cc, ?_⟩
    rw [← hfe, hcc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [CoreJ.phiJ, map_sum, map_smulₛₗ, map_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  choose cc hcc using hcc'
  have hσ₂ : ∀ z, C.σ₂ (C.inc z) = T.σ₀ z := fun z => congrArg (fun f => f z) hU.2.2.1
  let y : Fin m → C.d.c₂.F := fun k => ∑ i, x i * C.inc (cc i k)
  have hsum : φ = ∑ k, C.σ₂ (y k) • T.phiJ j T.σ₀ (wtA w) (β k) := by
    rw [hφe]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, hcc, Finset.smul_sum, smul_smul, map_sum, Finset.sum_smul, map_mul, hσ₂]
    exact Finset.sum_comm
  have hφ' : (∑ k, C.σ₂ (y k) • T.phiJ j T.σ₀ (wtA w) (β k)) ∈ C.intForms (wtA w) w.n {la} := hsum ▸ hφ
  obtain ⟨N, hN⟩ := GlobalTheory.T.traceCombination_coverForm_integral_over_prime D T hL j hj T.σ₀ hσ _ _ hD hspan hK C hU hP la p hp m β hβs
    (fun k => (hval _).1 (hβ k).2) y hφ'
  have hdiff : ∀ k, ∀ d ∈ differentIdeal (𝓞 T.Q.c.F) (𝓞 C.d.c₂.F),
      la.valuation C.d.c₂.F (y k * (d : C.d.c₂.F)) ≤ 1 := fun k =>
    GlobalTheory.T.valuation_mul_le_one_of_trace_approxIdempotent_integral T.Q.c.F C.d.c₂.F la p hp (y k)
      ⟨N, fun b hb => hprim (fun k => Algebra.trace T.Q.c.F C.d.c₂.F ((b : C.d.c₂.F) * y k)) ((hval _).2 (hN b hb)) k⟩
  have hcd := hc T.Q.c.F C.d.c₂.F p la hp hl1 hl2
  refine ⟨m, fun k => (l : C.d.c₂.F) ^ c * y k, fun k => T.phiJ j T.σ₀ (wtA w) (β k), ?_, ?_, ?_⟩
  · exact fun k => GlobalTheory.T.valuation_prime_pow_mul_le_one_of_not_dvd_different l c T.Q.c.F C.d.c₂.F la hl1 hcd (y k) (hdiff k)
  · refine fun k => ⟨β k, ⟨(hβs k).1, (hβs k).2, fun q hq => ?_⟩, rfl⟩
    rw [Set.mem_singleton_iff.1 hq]
    exact (hval _).1 (hβ k).2
  · rw [hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, map_mul, map_pow, map_natCast]

end GlobalTheory.XiIntSteps
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false

namespace GlobalTheory.ConjTwist.FlatSeries

theorem scale {X B : Type} (J : B → X → ℂ) (τ : ℂ ≃+* ℂ) (ζ η C C' : ℂ) (Φ Φ' : X → ℂ)
    (h1 : ∃ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), ∀ g, Φ g = ∑ k, a k * J (f k) g)
    (h2 : ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), (∀ g, Φ g = ∑ k, a k * J (f k) g) →
      ∀ g, Φ' g = ∑ k, ζ * τ (a k) * J (f k) g)
    (hC : C' = η * τ C) :
    (∃ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), ∀ g, C * Φ g = ∑ k, a k * J (f k) g) ∧
      ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → B), (∀ g, C * Φ g = ∑ k, a k * J (f k) g) →
        ∀ g, C' * Φ' g = ∑ k, ζ * η * τ (a k) * J (f k) g := by
  refine ⟨?_, ?_⟩
  · obtain ⟨n, a, f, h⟩ := h1
    refine ⟨n, fun k => C * a k, f, fun g => ?_⟩
    rw [h g, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · intro n a f ha g
    by_cases hC0 : C = 0
    · subst hC0
      obtain ⟨n₀, b, e, hb⟩ := h1
      have hC' : C' = 0 := by simp [hC]
      have hz : ∀ g, ∑ k, a k * J (f k) g = 0 := fun g => by simpa using (ha g).symm
      have hcat : ∀ g, Φ g = ∑ k, (Fin.append b a) k * J ((Fin.append e f) k) g := fun g => by
        rw [Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right]
        rw [hz g, add_zero, hb g]
      have e1 := h2 _ _ _ hcat g
      have e2 := h2 _ _ _ hb g
      rw [Fin.sum_univ_add] at e1
      simp only [Fin.append_left, Fin.append_right] at e1
      rw [e2] at e1
      have e3 : ∑ k, ζ * τ (a k) * J (f k) g = 0 := by simpa using e1.symm
      have e4 : ∑ k, ζ * η * τ (a k) * J (f k) g = η * ∑ k, ζ * τ (a k) * J (f k) g := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e4, e3, hC']
      simp
    · have hτ : τ C ≠ 0 := fun h => hC0 ((map_eq_zero_iff τ τ.injective).1 h)
      have hexp : ∀ g, Φ g = ∑ k, (C⁻¹ * a k) * J (f k) g := fun g => by
        have : Φ g = C⁻¹ * (C * Φ g) := by field_simp
        rw [this, ha g, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [h2 _ _ _ hexp g, hC, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_inv₀]
      field_simp

end GlobalTheory.ConjTwist.FlatSeries

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem GlobalTheory.ConjTwist.FlatSeries.conjFun_scale (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) {ζ η C C' : ℂ}
    {Φ Φ' : GA D (Wc D i) → ℂ} (h : ConjFun O κ τ ζ Φ Φ') (hC : C' = η * τ C) :
    ConjFun O κ τ (ζ * η) (fun g => C * Φ g) (fun g => C' * Φ' g) := by
  have key := GlobalTheory.ConjTwist.FlatSeries.scale
    (fun (b : T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) (g : GA D (Wc D i)) =>
      ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
        O.phi (T.cE ((i : ℕ) + 1) O.s0) (b : T.toCore.R ((i : ℕ) + 1)) g))
    τ ζ η C C' Φ Φ' h.1 (fun n a f ha g => h.2 n a f ha g) hC
  exact ⟨key.1, fun n a f ha g => key.2 n a f ha g⟩
end



theorem GlobalTheory.ConjTwist.FlatSeries.conj_flat_series : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' → ∃ s : (AE D)ˣ, ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * ser R i t f u h (c x) g) (fun g => ph i * ser R i t' f' u h (c x') g) := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hn hCore hT0 hFW hIo hQ i hPins hPh cc hcc u hu τ hFix
  obtain ⟨ζ0, hζ0, hser⟩ := GlobalTheory.T.conjugate_tuples_twisted_thetaSeries_conjugate hCI D G Pl0 T0 A T R F κ v₀ O ph hn hCore hT0 hFW hIo hQ i hPins hPh cc hcc u hu τ hFix
  refine ⟨ζ0, hζ0, fun t t' hConj f f' hf hf' => ?_⟩
  obtain ⟨s, hs⟩ := hser t t' hConj
  obtain ⟨z, C, C', s₂, hz, rfl, rfl, hC⟩ :=
    GlobalTheory.T.heckeChoice_flatScalar_conj_twist D G Pl0 T0 A T R F κ v₀ hCore hQ i τ t t' hPins.2.lift.std hFix hConj f f' hf hf'
  refine ⟨s * s₂, fun h hh x x' hx => ?_⟩
  have hzG : z ∈ GfC (Vc D i) := hz.2.1
  have base := hs (h * z) ((GfC (Vc D i)).mul_mem hh hzG) x x' hx
  have sc := GlobalTheory.ConjTwist.FlatSeries.conjFun_scale (O i) (κ i) τ base hC
  have e1 : (fun g => ph i * ser R i t (C • R.ωP i t (z, 1) (R.vP i t)) u h (cc x) g) =
      fun g => C * (ph i * ser R i t (R.vP i t) u (h * z) (cc x) g) := funext fun g => by
    rw [GlobalTheory.T.thetaSeries_translated_datum_at_translated_class D G Pl0 T0 A T.Q.c.F R F hCore i t z C hzG u h (cc x) g]
    ring
  have e2 : (fun g => ph i * ser R i t' (C' • R.ωP i t' (z, 1) (R.vP i t')) u h (cc x') g) =
      fun g => C' * (ph i * ser R i t' (R.vP i t') u (h * z) (cc x') g) := funext fun g => by
    rw [GlobalTheory.T.thetaSeries_translated_datum_at_translated_class D G Pl0 T0 A T.Q.c.F R F hCore i t' z C' hzG u h (cc x') g]
    ring
  rw [e1, e2]
  have e3 : ζ0 * ((R.xi t' (s * s₂) : Circle) : ℂ) = ζ0 * ((R.xi t' s : Circle) : ℂ) * ((R.xi t' s₂ : Circle) : ℂ) := by
    rw [map_mul, Circle.coe_mul, mul_assoc]
  rw [e3]
  exact sc
end
