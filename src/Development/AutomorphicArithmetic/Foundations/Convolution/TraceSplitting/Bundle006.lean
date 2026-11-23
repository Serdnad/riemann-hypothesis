module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.ExistsPowerSums
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.ListProdStable
public import Development.WeilBound.CuspidalAdmissibility.OccursIff
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.AmpFin
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle003
import Development.AutomorphicArithmetic.TwistedTraces.Bundle019
import Development.AutomorphicArithmetic.TwistedTraces.IwahoriCompactOpenAndIwCosetIndicatorTest
import Development.AutomorphicArithmetic.TwistedTraces.Bundle015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle009
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical

private theorem trace_range_smul {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) {c s : ℂ} (hc : c ≠ 0)
    (h : HasFinTrace A s) : HasFinTrace (c • A) (c * s) := by
  obtain ⟨hfd, rfl⟩ := h
  have hr : LinearMap.range (c • A) = LinearMap.range A := LinearMap.range_smul _ _ hc
  have key : ∀ W : Submodule ℂ V, W = LinearMap.range A → ∀ h' : ∀ v ∈ W, (c • A) v ∈ W,
      LinearMap.trace ℂ W ((c • A).restrict h') = c * LinearMap.trace ℂ (LinearMap.range A)
        (A.restrict (p := LinearMap.range A) (q := LinearMap.range A) fun v _ => LinearMap.mem_range_self A v) := by
    rintro W rfl h'
    have : (c • A).restrict h' = c • A.restrict (p := LinearMap.range A) (q := LinearMap.range A)
        (fun v _ => LinearMap.mem_range_self A v) := by
      ext v
      rfl
    rw [this, map_smul, smul_eq_mul]
  exact ⟨hr ▸ hfd, key _ hr _⟩

private theorem hasTrace_of_smul {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {s : ℂ} {d : ENNReal} (h0 : d ≠ 0) (ht : d ≠ ⊤)
    (h : HasTrace (d • m) ρ f s) : HasTrace m ρ f (((d.toReal : ℂ))⁻¹ * s) := by
  obtain ⟨A, hA, hT⟩ := h
  have hr : (d.toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos h0 ht).ne'
  refine ⟨((d.toReal : ℂ))⁻¹ • A, fun v l => ?_, trace_range_smul A (inv_ne_zero hr) hT⟩
  obtain ⟨h1, h2⟩ := hA v l
  refine ⟨(integrable_smul_measure h0 ht).1 h1, ?_⟩
  rw [LinearMap.smul_apply, map_smul, h2, integral_smul_measure, smul_eq_mul, Complex.real_smul, inv_mul_cancel_left₀ hr]

private theorem fd_of_trace {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {I : Subgroup G} {s : ℂ} (hIm : MeasurableSet (I : Set G))
    (h0 : m I ≠ 0) (ht : m I ≠ ⊤) (h : HasTrace m ρ ((I : Set G).indicator 1) s) :
    FiniteDimensional ℂ (fixedVectors ρ I) := by
  obtain ⟨A, hA, hfd, -⟩ := h
  have hr : ((m (I : Set G)).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos h0 ht).ne'
  have hfix : ∀ v ∈ fixedVectors ρ I, A v = ((m (I : Set G)).toReal : ℂ) • v := by
    intro v hv
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA v l).2, map_smul, smul_eq_mul]
    have e : (fun g => (I : Set G).indicator (1 : G → ℂ) g * l (ρ g v)) = (I : Set G).indicator fun _ => l v := by
      funext g
      by_cases hg : g ∈ (I : Set G)
      · have : ρ g v = v := hv g hg
        simp [hg, this]
      · simp [hg]
    rw [e, integral_indicator hIm, setIntegral_const, measureReal_def, Complex.real_smul]
  have hle : fixedVectors ρ I ≤ LinearMap.range A := by
    intro v hv
    refine ⟨((m (I : Set G)).toReal : ℂ)⁻¹ • v, ?_⟩
    rw [map_smul, hfix v hv, smul_smul, inv_mul_cancel₀ hr, one_smul]
  exact Submodule.finiteDimensional_of_le hle

private theorem test_ind {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) :
    Test (((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w)).indicator (1 : Gw n w → ℂ)) := by
  obtain ⟨hc, ho⟩ := (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test K n w).1
  have hcl : IsClosed ((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w)) :=
    Subgroup.isClosed_of_isOpen _ ho
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ ((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w))
  · filter_upwards [ho.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    rfl
  · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

private theorem iw_pow_at {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) [MeasurableSpace (Gw n w)]
    [BorelSpace (Gw n w)] (m : Measure (Gw n w)) [m.IsHaarMeasure] (σ : SmIrr (Gw n w)) (ν : Fin n → ℤ) (hν : Antitone ν)
    {s₀ : ℂ} (h₀ : HasTrace m σ.ρ (((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w)).indicator 1) s₀) :
    ∃ (c : ℂ) (Z : Multiset ℂ), 0 ∉ Z ∧ ∀ j : ℕ, HasTrace m σ.ρ ((GM.iwCoset w (j • ν)).indicator 1) (c * (Z.map (· ^ j)).sum) := by
  obtain ⟨hc, ho⟩ := (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test K n w).1
  have hpos : m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) ≠ 0 :=
    (ho.measure_pos m ⟨1, one_mem _⟩).ne'
  have htop : m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) ≠ ⊤ := hc.measure_lt_top.ne
  have hfd := fd_of_trace ho.measurableSet hpos htop h₀
  set d : ENNReal := (m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)))⁻¹ with hd
  have hd0 : d ≠ 0 := ENNReal.inv_ne_zero.2 htop
  have hdt : d ≠ ⊤ := ENNReal.inv_ne_top.2 hpos
  haveI : (d • m).IsHaarMeasure := Measure.IsHaarMeasure.smul m hd0 hdt
  have h1 : (d • m) (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) = 1 := by
    rw [Measure.smul_apply, smul_eq_mul, hd, ENNReal.inv_mul_cancel hpos htop]
  obtain ⟨Z, hZ0, -, hZ⟩ := UpperTheory.ConvolutionTheory.C.iwPow K n w (d • m) h1 σ ν hν hfd
  exact ⟨_, Z, hZ0, fun j => hasTrace_of_smul hd0 hdt (hZ j)⟩

private theorem amp_A_eq {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a : TI K n)
    (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) (h1 : 𝔞.ν = ν) (h2 : 𝔞.a₀ = a) (h3 : 𝔞.U = U) :
    𝔞.A = Oinf μ ν a ∘L prj (fixF μ U) := by
  subst h2 h3
  have : ∀ (ν' : Measure (archGroup K n)) (_ : ν'.IsHaarMeasure) (_ : ν' = ν) , Oinf μ ν' 𝔞.a₀ = Oinf μ ν 𝔞.a₀ := by
    intro ν' _ h; subst h; rfl
  exact congrArg (· ∘L prj (fixF μ 𝔞.U)) (this 𝔞.ν 𝔞.haar h1)

private theorem trOn_bot' {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (B : H →L[ℂ] H) :
    trOn (⊥ : Submodule ℂ H) B = 0 := by
  have := UpperTheory.trOn_eq_mul_of_eq_smul_on_subspace H ⊥ B B 0 inferInstance (fun v hv => by
    rw [(Submodule.mem_bot ℂ).1 hv]; simp)
  simpa using this

theorem UpperTheory.ConvolutionTheory.T.sideSum :
    UpperTheory.ConvolutionTheory.T.SideSum := by
  intro F E _ _ _ _ _ _ σ n l hn μ _ ν _ _ _ m hm a q w₀ S UF e he p x hx
  haveI hmH : ∀ v, (m v).IsHaarMeasure := fun v => (hm v).1
  by_cases hex : ∃ (L : GM.Loc σ n q w₀) (𝔣 : Side (Twist.id μ) l), L.S = S ∧ (∀ v ∈ S, L.UF v = UF v) ∧ GM.IsSideF L ν a e 𝔣
  swap
  · refine ⟨Empty, inferInstance, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim, ?_⟩
    intro L 𝔣 h1 h2 h3
    exact absurd ⟨L, 𝔣, h1, h2, h3⟩ hex
  obtain ⟨L₀, 𝔣₀, hS₀, hU₀, hF₀⟩ := hex
  obtain ⟨κ, -, hT⟩ := UpperTheory.ConvolutionTheory.C.termF F E σ n l hn μ ν m hm
  have hfin := (UpperTheory.ConvolutionTheory.T.ampFin F n hn μ 𝔣₀.toAmp).1 x hx
  set P : Set (Submodule ℂ (LL μ)) := {V | IsSummand μ V ∧ eigIn V 𝔣₀.toAmp.A x ≠ ⊥ ∧ p V} with hP
  have hPfin : P.Finite := hfin.subset fun V h => ⟨h.1, h.2.1⟩
  have hτ : ∀ V : P, ∃ τ : ∀ v : Pl F, SmIrr (Gw n v), ∀ v, Occurs μ V.1 v (τ v) := fun V => by
    have := fun v => (UpperTheory.ConvolutionTheory.C.occursBasics F n μ V.1 v (m v) V.2.1).1
    choose τ hτ using this
    exact ⟨τ, hτ⟩
  choose τ hτ using hτ
  have hZ : ∀ V : P, ∃ (c : ℂ) (Z : Multiset ℂ), 0 ∉ Z ∧ ∀ j : ℕ,
      HasTrace (m q) (τ V q).ρ ((GM.iwCoset q (j • e)).indicator 1) (c * (Z.map (· ^ j)).sum) := fun V => by
    obtain ⟨s₀, hs₀⟩ := (UpperTheory.ConvolutionTheory.C.occursBasics F n μ V.1 q (m q) V.2.1).2.2 (τ V q) (hτ V q) _ (test_ind q)
    exact iw_pow_at q (m q) (τ V q) e he hs₀
  choose c Z hZ0 hZ using hZ
  have hN := fun V : P => hT a q w₀ S V.1 (τ V) x V.2.1 hx (fun v _ => hτ V v)
  choose N hN using hN
  letI : Fintype P := hPfin.fintype
  refine ⟨P, inferInstance, fun V => V.1, τ, fun V => κ * x * N V * c V, Z, fun V => ⟨V.2.1, V.2.2.2, hZ0 V, hτ V⟩, ?_⟩
  intro L 𝔣 hS hU hF s hs j
  have hUF : L.UF = L₀.UF := by
    funext v
    by_cases hv : v ∈ S
    · rw [hU v hv, hU₀ v hv]
    by_cases hq : v = q
    · subst hq
      rw [L.at_q.2.2.2, L₀.at_q.2.2.2]
    · rw [(L.off v (hS ▸ hv) hq).2.2.2, (L₀.off v (hS₀ ▸ hv) hq).2.2.2]
  have hA : 𝔣.toAmp.A = 𝔣₀.toAmp.A := by
    obtain ⟨h1, h2, -, h3, -, -⟩ := hF
    obtain ⟨h1', h2', -, h3', -, -⟩ := hF₀
    rw [amp_A_eq 𝔣.toAmp ν a _ h1 h2 h3, amp_A_eq 𝔣₀.toAmp ν a _ h1' h2' h3', hUF]
  have hid : ∀ V : Submodule ℂ (LL μ), V.map ((Twist.id μ).U : LL μ →ₗ[ℂ] LL μ) = V := fun V => by
    have : ((Twist.id μ).U : LL μ →ₗ[ℂ] LL μ) = LinearMap.id := LinearMap.ext fun _ => rfl
    rw [this, Submodule.map_id]
  have hsum : 𝔣.tr p x j = ∑ᶠ V ∈ P, trOn (eigIn V 𝔣.toAmp.A x) ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) := by
    unfold Side.tr
    refine finsum_mem_inter_support_eq _ _ _ ?_
    ext V
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, hP]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, h4⟩
      refine ⟨⟨h1, fun h => h4 ?_, h3⟩, h4⟩
      rw [hA, h, trOn_bot']
    · rintro ⟨⟨h1, -, h3⟩, h4⟩
      exact ⟨⟨h1, hid V, h3⟩, h4⟩
  rw [hsum, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [(hN V).2 L e 𝔣 hS he hF j _ (s V) (hZ V j) (hs V)]
  ring
end

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped Classical NNReal

section Abs

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem trace_congr {p p' : Submodule ℂ V} (h : p = p') (A : V →ₗ[ℂ] V) (h1 : ∀ v ∈ p, A v ∈ p) (h2 : ∀ v ∈ p', A v ∈ p') :
    LinearMap.trace ℂ p (A.restrict h1) = LinearMap.trace ℂ p' (A.restrict h2) := by
  subst h
  rfl

private theorem hasTrace_smul [MeasurableSpace G] {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {s : ℂ} (c : ℝ≥0)
    (hc : c ≠ 0) (h : HasTrace m ρ f s) : HasTrace (c • m) ρ f (((c : ℝ) : ℂ) * s) := by
  obtain ⟨A, hA, hfin, rfl⟩ := h
  have hc' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hr : LinearMap.range (((c : ℝ) : ℂ) • A) = LinearMap.range A := LinearMap.range_smul _ _ hc'
  refine ⟨((c : ℝ) : ℂ) • A, fun v l => ⟨(hA v l).1.smul_measure_nnreal, ?_⟩, hr ▸ hfin, ?_⟩
  · rw [integral_smul_nnreal_measure, ← (hA v l).2, LinearMap.smul_apply, map_smul]
    rfl
  · rw [trace_congr hr _ _ (fun v _ => Submodule.smul_mem _ _ (LinearMap.mem_range_self A v)), ← smul_eq_mul, ← map_smul]
    rfl

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private theorem vol_pos (m : Measure G) [m.IsHaarMeasure] {U : Subgroup G} (hU : CO U) : 0 < m.real U :=
  ENNReal.toReal_pos (hU.2.measure_pos m ⟨1, one_mem U⟩).ne' hU.1.measure_lt_top.ne

private theorem trace_ind (m : Measure G) [m.IsHaarMeasure] {ρ : Representation ℂ G V} {U : Subgroup G} (hU : CO U) {s : ℂ}
    (h : HasTrace m ρ ((U : Set G).indicator 1) s) :
    FiniteDimensional ℂ (fixedVectors ρ U) ∧ s = (m.real U : ℂ) * Module.finrank ℂ (fixedVectors ρ U) := by
  obtain ⟨A, hA, hfin, rfl⟩ := h
  have hm : MeasurableSet (U : Set G) := hU.2.measurableSet
  have hc : (m.real U : ℂ) ≠ 0 := by exact_mod_cast (vol_pos m hU).ne'
  have h1 : ∀ v, A v ∈ fixedVectors ρ U := fun v => mem_fixedVectors.2 fun a ha => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA v l).2]
    refine (hA v (l ∘ₗ ρ a)).2.trans ?_
    rw [← integral_mul_left_eq_self (fun g => (U : Set G).indicator (1 : G → ℂ) g * l (ρ g v)) a]
    congr 1
    funext g
    by_cases h : g ∈ U
    · simp [h, mul_mem ha h]
    · have : a * g ∉ U := fun h' => h (by simpa using mul_mem (inv_mem ha) h')
      simp [h, this]
  have h2 : ∀ v ∈ fixedVectors ρ U, A v = (m.real U : ℂ) • v := fun v hv => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA v l).2, map_smul]
    have : (fun g => (U : Set G).indicator (1 : G → ℂ) g * l (ρ g v)) = (U : Set G).indicator fun _ => l v := by
      funext g
      by_cases h : g ∈ U
      · simp [h, mem_fixedVectors.1 hv g h]
      · simp [h]
    rw [this, integral_indicator_const _ hm]
    rfl
  have hr : LinearMap.range A = fixedVectors ρ U := by
    refine le_antisymm (by rintro _ ⟨v, rfl⟩; exact h1 v) fun v hv => ⟨(m.real U : ℂ)⁻¹ • v, ?_⟩
    rw [map_smul, h2 v hv, smul_smul, inv_mul_cancel₀ hc, one_smul]
  haveI : FiniteDimensional ℂ (fixedVectors ρ U) := hr ▸ hfin
  refine ⟨this, ?_⟩
  rw [trace_congr hr _ _ (fun v _ => h1 v)]
  have : A.restrict (p := fixedVectors ρ U) (q := fixedVectors ρ U) (fun v _ => h1 v) = (m.real U : ℂ) • LinearMap.id :=
    LinearMap.ext fun v => Subtype.ext (h2 v v.2)
  rw [this, map_smul, LinearMap.trace_id, smul_eq_mul]

private theorem ex_haar [LocallyCompactSpace G] {U : Subgroup G} (hU : CO U) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m U = 1 := by
  obtain ⟨P, hP⟩ : ∃ P : TopologicalSpace.PositiveCompacts G, (P : Set G) = U :=
    ⟨⟨⟨U, hU.1⟩, by
      change (interior (U : Set G)).Nonempty
      rw [hU.2.interior_eq]
      exact ⟨1, one_mem U⟩⟩, rfl⟩
  exact ⟨Measure.haarMeasure P, inferInstance, hP ▸ Measure.haarMeasure_self⟩

private theorem ex_norm (m : Measure G) [m.IsHaarMeasure] {U : Subgroup G} (hU : CO U) :
    ∃ (c : ℝ≥0) (m' : Measure G), c ≠ 0 ∧ m'.IsHaarMeasure ∧ m' U = 1 ∧ m = c • m' := by
  have h0 : m U ≠ 0 := (hU.2.measure_pos m ⟨1, one_mem U⟩).ne'
  have h1 : m U ≠ ⊤ := hU.1.measure_lt_top.ne
  have hc : (m U).toNNReal ≠ 0 := ENNReal.toNNReal_ne_zero.2 ⟨h0, h1⟩
  refine ⟨(m U).toNNReal, (m U).toNNReal⁻¹ • m, hc, Measure.IsHaarMeasure.nnreal_smul m (inv_ne_zero hc), ?_, ?_⟩
  · rw [Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_inv hc, ENNReal.coe_toNNReal h1, smul_eq_mul,
      ENNReal.inv_mul_cancel h0 h1]
  · rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

end Abs

private theorem amp_eq {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (h1 : 𝔞.ν = ν) :
    𝔞.A = Oinf μ ν 𝔞.a₀ ∘L prj (fixF μ 𝔞.U) := by
  subst h1
  rfl

private theorem term {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F]
    {σ : E ≃ₐ[F] E} {n : ℕ} (hn : 0 < n) {μ : Measure (normOneGL (K := F) (n := n))} [μ.IsHaarMeasure] {q : Pl F}
    {w₀ : GroundTheory.Global.SemiLocal.PlacesOver E q} {ν : Measure (archGroup F n)} [ν.IsHaarMeasure] {a : TI F n} {L : Loc σ n q w₀}
    {e : Fin n → ℤ} {l : ℕ} {𝔣 : Side (Twist.id μ) l} (he : Antitone e) (hF : IsSideF L ν a e 𝔣)
    (hf : ∀ v ∈ L.S, L.f v = (L.UF v : Set (Gw n v)).indicator 1) {x : ℝ} (hx : 0 < x) (V : Submodule ℂ (LL μ))
    (hV : IsSummand μ V) (hne : eigIn V 𝔣.toAmp.A x ≠ ⊥) :
    ∃ (c : ℝ) (Z : Multiset ℂ), 0 < c ∧ 0 ∉ Z ∧ Z ≠ 0 ∧ ∀ j : ℕ,
      trOn (eigIn V 𝔣.toAmp.A x) ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) = c * (Z.map (· ^ j)).sum := by
  letI : ∀ v : Pl F, MeasurableSpace (Gw n v) := fun v => borel _
  haveI : ∀ v : Pl F, BorelSpace (Gw n v) := fun v => ⟨rfl⟩
  have hK : ∀ v : Pl F, CO (GLnLocal.integralGL (v.adicCompletion F) n) := fun v =>
    (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n v).2.1 _ (GLnLocal.isOpen_integralGL _ _) le_rfl
  choose m hm using fun v : Pl F => ex_haar (hK v)
  haveI := fun v => (hm v).1
  obtain ⟨κ, hκ, H⟩ := UpperTheory.ConvolutionTheory.C.termF F E σ n l hn μ ν m hm
  choose τ hτ using fun v : Pl F => (occursBasics F n μ V v (m v) hV).1
  obtain ⟨N, hN, H⟩ := H a q w₀ L.S V τ x hV hx fun v _ => hτ v
  have hlev : levF L.UF = levOn (insert q L.S) L.UF := by
    unfold levOn
    congr 1
    funext v
    split_ifs with h
    · rfl
    · rw [Finset.mem_insert, not_or] at h
      exact (L.off v h.2 h.1).2.2.2
  have hne' := hne
  rw [amp_eq 𝔣.toAmp ν hF.1, hF.2.1, hF.2.2.2.1, hlev, UpperTheory.eigenspace_comp_levelProjection_eq_inf_fixed F n hn μ ν V a x _ L.UF hx.ne'] at hne'
  have hN0 : 0 < N := hN.2 (ne_bot_of_le_ne_bot hne' inf_le_left)
  have hCO : ∀ v ∈ insert q L.S, CO (L.UF v) := fun v hv => by
    rcases Finset.mem_insert.1 hv with rfl | hv
    · rw [L.at_q.2.2.2]
      exact (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n v).1
    · exact (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n v).2.1 _ (L.lev v hv).2.2.1 (L.lev v hv).2.2.2
  have hpos : ∀ v ∈ insert q L.S, FiniteDimensional ℂ (fixedVectors (τ v).ρ (L.UF v)) ∧
      0 < Module.finrank ℂ (fixedVectors (τ v).ρ (L.UF v)) ∧ HasTrace (m v) (τ v).ρ ((L.UF v : Set (Gw n v)).indicator 1)
        ((((m v).real (L.UF v) * Module.finrank ℂ (fixedVectors (τ v).ρ (L.UF v)) : ℝ)) : ℂ) := fun v hv => by
    obtain ⟨-, -, -, s, hs0, hs⟩ := T.unitTrace F n μ V hV v (m v) inferInstance (τ v) (L.UF v) (hτ v) (hCO v hv)
      (ne_bot_of_le_ne_bot hne' (inf_le_inf (inf_le_left.trans inf_le_left) (iInf₂_le v hv)))
    obtain ⟨h1, h2⟩ := trace_ind (m v) (hCO v hv) hs
    refine ⟨h1, Nat.pos_of_ne_zero fun h => hs0 (by rw [h2, h]; simp), ?_⟩
    push_cast
    exact h2 ▸ hs
  obtain ⟨hq1, hq2, -⟩ := hpos q (Finset.mem_insert_self _ _)
  rw [L.at_q.2.2.2] at hq1 hq2
  obtain ⟨c, m', hc, hm', hm1, hme⟩ := ex_norm (m q) (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n q).1
  obtain ⟨Z, hZ0, hZc, hZ⟩ := iwPow F n q m' hm1 (τ q) e he hq1
  let s : Pl F → ℝ := fun v => (m v).real (L.UF v) * Module.finrank ℂ (fixedVectors (τ v).ρ (L.UF v))
  have hs : ∀ v ∈ L.S, 0 < s v := fun v hv =>
    mul_pos (vol_pos _ (hCO v (Finset.mem_insert_of_mem hv))) (Nat.cast_pos.2 (hpos v (Finset.mem_insert_of_mem hv)).2.1)
  refine ⟨κ * x * N * c * ∏ v ∈ L.S, s v, Z, ?_, hZ0, ?_, fun j => ?_⟩
  · have h1 : (0 : ℝ) < c := by exact_mod_cast hc.bot_lt
    have h2 : (0 : ℝ) < N := Nat.cast_pos.2 hN0
    have h3 := Finset.prod_pos hs
    positivity
  · rintro rfl
    rw [← hZc] at hq2
    exact lt_irrefl _ hq2
  · have h1 := hasTrace_smul c hc (hZ j)
    rw [← hme] at h1
    rw [H L e 𝔣 rfl he hF j _ (fun v => (s v : ℂ)) h1 fun v hv => by
      rw [hf v hv]
      exact (hpos v (Finset.mem_insert_of_mem hv)).2.2]
    push_cast
    ring

theorem UpperTheory.ConvolutionTheory.T.posSide :
    UpperTheory.ConvolutionTheory.T.PosSide := by
  intro F E _ _ _ _ _ _ _ _ σ _ _ n hn μ _ q w₀ ν _ a L e l 𝔣 he hF hf p V x hV hpV hx hne
  have hfin : {W : Submodule ℂ (LL μ) | (IsSummand μ W ∧ eigIn W 𝔣.toAmp.A x ≠ ⊥) ∧ p W}.Finite :=
    ((T.ampFin F n hn μ 𝔣.toAmp).1 x hx).subset fun W hW => hW.1
  let ι := {W : Submodule ℂ (LL μ) | (IsSummand μ W ∧ eigIn W 𝔣.toAmp.A x ≠ ⊥) ∧ p W}
  haveI : Fintype ι := hfin.fintype
  choose c Z hc hZ0 hZ hT using fun W : ι => term hn he hF hf hx W.1 W.2.1.1 W.2.1.2
  have htr : ∀ j, 𝔣.tr p x j = ∑ W : ι, (c W : ℂ) * ((Z W).map (· ^ j)).sum := fun j => by
    simp only [← hT]
    rw [Side.tr, ← finsum_eq_sum_of_fintype, finsum_set_coe_eq_finsum_mem (s := ι)
      (f := fun W => trOn (eigIn W 𝔣.toAmp.A x) ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U))]
    refine finsum_mem_inter_support_eq' _ _ _ fun W hW => ⟨fun h => ⟨⟨h.1, fun hb => hW ?_⟩, h.2.2⟩, fun h => ⟨h.1.1, ?_, h.2⟩⟩
    · beta_reduce
      rw [hb]
      simpa using UpperTheory.trOn_eq_mul_of_eq_smul_on_subspace (LL μ) ⊥ ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) 0 0 inferInstance fun v hv => by
        rw [(Submodule.mem_bot ℂ).1 hv]
        simp
    · exact Submodule.map_id W
  intro h
  let V₀ : ι := ⟨V, ⟨hV, hne⟩, hpV⟩
  obtain ⟨ζ, hζ⟩ := Multiset.exists_mem_of_ne_zero (hZ V₀)
  have h0 := powIndep ι (fun W => (c W : ℂ)) Z hZ0 (h.mono fun j hj => by rw [← htr]; exact not_not.1 hj) ζ
  have h1 : ∑ W : ι, c W * ((Multiset.filter (· = ζ) (Z W)).card : ℝ) = 0 := by exact_mod_cast h0
  refine (Finset.sum_pos' (fun W _ => mul_nonneg (hc W).le (Nat.cast_nonneg _)) ⟨V₀, Finset.mem_univ _, mul_pos (hc _) ?_⟩).ne' h1
  exact Nat.cast_pos.2 (Multiset.card_pos_iff_exists_mem.2 ⟨ζ, Multiset.mem_filter.2 ⟨hζ, rfl⟩⟩)
end
