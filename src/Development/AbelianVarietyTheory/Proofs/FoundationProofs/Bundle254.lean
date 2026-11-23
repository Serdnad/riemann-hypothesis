module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle244
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle242
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle030
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle141
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle245
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle247
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodularSpan
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open GlobalTheory.AlmostEt GlobalTheory.K5

namespace GlobalTheory.K5.TorsionDiff

theorem dlog_descend {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]
    (a ai b bi P : S) (da db : M) (ha : a * ai = 1) (hb : b * bi = 1)
    (h : b • da = (P * a) • db) : (P * bi) • db = ai • da := by
  have h2 := congrArg (fun m => (ai * bi) • m) h
  simp only [smul_smul] at h2
  have e1 : ai * bi * b = ai := by linear_combination ai * hb
  have e2 : ai * bi * (P * a) = P * bi := by linear_combination (P * bi) * ha
  rw [e1, e2] at h2
  exact h2.symm

theorem exists_inv_zS {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω) (n : ℕ) : ∃ zi, zS T n * zi = 1 := by
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  refine ⟨zS T n ^ (p ^ n - 1), ?_⟩
  rw [← pow_succ', Nat.sub_add_cancel hpos]
  exact Subtype.ext (T.prim n).pow_eq_one

theorem exists_inv_qS {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω) (n : ℕ) : ∃ qi, qS T n * qi = 1 := by
  have hne : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have h1 : qS T n ^ (p ^ n) = algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p) :=
    Subtype.ext (GlobalTheory.AlmostEt.qq_pow T n)
  have h2 : IsUnit (qS T n ^ (p ^ n)) := by
    rw [h1]; exact (GlobalTheory.K5.Basic.isUnit_qO p).map _
  exact ((isUnit_pow_iff hne).1 h2).exists_right_inv

theorem span_core {S M : Type*} [CommRing S] [IsDomain S] [AddCommGroup M] [Module S M]
    (P : S) (hP : P ≠ 0) (n k : ℕ) (hn : 1 ≤ n) (η dz dq dzm dqm : M)
    (zi qi zm qm zim qim x y : S) (hz : zm * zim = 1) (hq : qm * qim = 1)
    (hη : P ^ n • η = 0) (hs : P ^ 2 • η = x • dzm + y • dqm)
    (hdz : (P ^ k * zim) • dzm = zi • dz) (hdq : (P ^ k * qim) • dqm = qi • dq)
    (hind : ∀ x y : S, (x * zim) • dzm + (y * qim) • dqm = 0 →
      (∃ t, P ^ 3 * x = P ^ (n + k - 1) * t) ∧ (∃ t, P ^ 3 * y = P ^ (n + k) * t)) :
    ∃ x y : S, P ^ 6 • η = (x * zi) • dz + (y * qi) • dq := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h0 : (P ^ (n + 1) * x * zm * zim) • dzm + (P ^ (n + 1) * y * qm * qim) • dqm = 0 := by
    rw [mul_assoc _ zm, hz, mul_assoc _ qm, hq, mul_one, mul_one, mul_smul, mul_smul, ← smul_add,
      ← hs, smul_comm, hη, smul_zero]
  obtain ⟨⟨t, ht⟩, ⟨u, hu⟩⟩ := hind _ _ h0
  have e : n + 1 + k - 1 = n + k := by omega
  rw [e] at ht
  have hx : P ^ 4 * x = t * (P ^ k * zim) := by
    apply mul_left_cancel₀ (pow_ne_zero n hP)
    linear_combination zim * ht - P ^ (n + 4) * x * hz
  have hy : P ^ 4 * y = P * u * (P ^ k * qim) := by
    apply mul_left_cancel₀ (pow_ne_zero n hP)
    linear_combination qim * hu - P ^ (n + 4) * y * hq
  refine ⟨t, P * u, ?_⟩
  have e6 : P ^ 6 = P ^ 4 * P ^ 2 := by ring
  rw [e6, mul_smul, hs, smul_add, smul_smul, smul_smul, hx, hy, mul_smul t, mul_smul (P * u),
    hdz, hdq, smul_smul, smul_smul]

theorem torsion_span_and_indep : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ z qn zi qi : integralClosure (O0 p) Ω,
  (z : Ω) = T.ζ n → (qn : Ω) = T.qq n → z * zi = 1 → qn * qi = 1 →
  (∀ η : KaehlerDifferential (O0 p) (integralClosure (O0 p) Ω), (p ^ n : ℕ) • η = 0 →
     ∃ x y : integralClosure (O0 p) Ω, (p ^ c : ℕ) • η =
       (x * zi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) z +
       (y * qi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qn) ∧
  (∀ x y : integralClosure (O0 p) Ω,
     (x * zi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) z +
       (y * qi) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) qn = 0 →
     (∃ t, (p : integralClosure (O0 p) Ω) ^ c * x = (p : integralClosure (O0 p) Ω) ^ (n - 1) * t) ∧
     (∃ t, (p : integralClosure (O0 p) Ω) ^ c * y = (p : integralClosure (O0 p) Ω) ^ n * t)) := by
  intro p _ hp2
  refine ⟨6, ?_⟩
  intro Ω _ _ hΩ T n hn z qn zi qi hz hq hzi hqi
  obtain rfl : z = zS T n := Subtype.ext hz
  obtain rfl : qn = qS T n := Subtype.ext hq
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hΩ
  have hP : (p : integralClosure (O0 p) Ω) ≠ 0 := by
    intro h
    have h2 : (p : Ω) = 0 := by simpa using congrArg Subtype.val h
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h2)
  refine ⟨?_, ?_⟩
  · intro η hη
    obtain ⟨m, hm, x, y, hs⟩ := GlobalTheory.AlmostEt.p_sq_smul_kaehler_mem_span p Ω hp2 hΩ T η n
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    obtain ⟨zim, hzim⟩ := exists_inv_zS T (n + k)
    obtain ⟨qim, hqim⟩ := exists_inv_qS T (n + k)
    obtain ⟨hdz, hdq⟩ := GlobalTheory.AlmostEt.dlog_transition p Ω T n k
    rw [← Nat.cast_smul_eq_nsmul (integralClosure (O0 p) Ω), Nat.cast_pow] at hη ⊢
    exact span_core _ hP n k hn η _ _ _ _ zi qi _ _ zim qim x y hzim hqim hη hs
      (dlog_descend _ _ _ _ _ _ _ hzi hzim hdz) (dlog_descend _ _ _ _ _ _ _ hqi hqim hdq)
      (fun x y h => GlobalTheory.AlmostEt.dlog_indep_pow_three p Ω hp2 hΩ T (n + k) (by omega) x y zim qim hzim hqim h)
  · intro x y h
    obtain ⟨⟨t, ht⟩, ⟨u, hu⟩⟩ := GlobalTheory.AlmostEt.dlog_indep_pow_three p Ω hp2 hΩ T n hn x y zi qi hzi hqi h
    exact ⟨⟨(p : integralClosure (O0 p) Ω) ^ 3 * t, by linear_combination (p : integralClosure (O0 p) Ω) ^ 3 * ht⟩,
      ⟨(p : integralClosure (O0 p) Ω) ^ 3 * u, by linear_combination (p : integralClosure (O0 p) Ω) ^ 3 * hu⟩⟩

end GlobalTheory.K5.TorsionDiff
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.exists_finiteLevel_approx_of_geometric_invariant_modPow : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ x : Ω, IsInt (p := p) x →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong (p := p) k (g x) x) →
  ∃ y : Ω, IsInt (p := p) y ∧ (∃ N, ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) ∧
    Cong (p := p) k ((T.ζ j - 1) * x) y := by
  intro p _ hp2 Ω _ _ hClo T k j hj x hx hfix
  obtain ⟨y₀, E, hy₀, hEH, huniq, hsum⟩ :=
    GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp2 hClo T
      (Ggeo p Ω ⊓ ⨅ n, Gn T n) inf_le_right {x} j hj
  have hgi (g : Gal p Ω) (z : Ω) (hz : IsInt (p := p) z) : IsInt (p := p) (g z) :=
    hz.map (g : Ω →ₐ[O0 p] Ω)
  have hlevel := GlobalTheory.K5.GeoLevel.exists_level_of_fixed hClo T _
    (GlobalTheory.K5.FinLevel.sum_fixed _ E y₀ x hEH huniq)
  refine ⟨∑ g ∈ E, g (y₀ * x), IsIntegral.sum _ (fun g _ => hgi g _ (hy₀.mul hx)), hlevel, ?_⟩
  have hz : ∀ g ∈ E, ∃ z : Ω, IsInt (p := p) z ∧ g x - x = (p : Ω) ^ k * z :=
    fun g hg => hfix g (hEH g hg)
  choose! z hzi hzx using hz
  refine ⟨-∑ g ∈ E, g y₀ * z g, ?_, ?_⟩
  · exact (IsIntegral.sum _ fun g hg => (hgi g _ hy₀).mul (hzi g hg)).neg
  · rw [← hsum, Finset.sum_mul, ← Finset.sum_sub_distrib, mul_neg, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [map_mul]
    linear_combination (-(g y₀)) * hzx g hg
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalConjugacy
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

noncomputable def coordLat (V : Formalism.BasicNotions.HSpace E) (L : Submodule (𝓞 E) V.V) : Submodule (𝓞 E) (Fin V.rank → E) :=
  L.map (V.frame.equivFun.restrictScalars (𝓞 E)).toLinearMap

theorem span_eq_top_of_unimodular (V : Formalism.BasicNotions.HSpace E)
    (L : Submodule (𝓞 E) V.V) (h : Submodule.IsLattice E L)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) :
    Submodule.span E (L : Set V.V) = ⊤ := by
  exact Formalism.HermitianLatticesTheory.IsUnimodular.span_eq_top hu V.herm h.fg

theorem isLattice_coordLat (V : Formalism.BasicNotions.HSpace E) (L : Submodule (𝓞 E) V.V)
    (h : Submodule.IsLattice E L)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L := by exact V.baseLattice_isUnimodular) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (coordLat V L) := by
  refine ⟨h.fg.map _, ?_⟩
  have : (coordLat V L : Set (Fin V.rank → E)) = V.frame.equivFun.toLinearMap '' (L : Set V.V) := rfl
  rw [this, ← Submodule.map_span, span_eq_top_of_unimodular V L h hu, Submodule.map_top, LinearEquiv.range]

theorem herm_coord (V : Formalism.BasicNotions.HSpace E) (x y : V.V) :
    herm V.gramᵀ (V.frame.equivFun x) (V.frame.equivFun y) = V.hT y x := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord, herm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change V.frame.repr x j * V.gram i j * star (V.frame.repr y i) = _
  ring

theorem selfDual_coordLat (V : Formalism.BasicNotions.HSpace E) (L : Submodule (𝓞 E) V.V)
    (h : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) (x : Fin V.rank → E) :
    x ∈ coordLat V L ↔ ∀ y ∈ coordLat V L, IsIntegral ℤ (herm V.gramᵀ x y) := by
  obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective x
  have h1 : V.frame.equivFun x ∈ coordLat V L ↔ x ∈ L :=
    ⟨fun ⟨z, hz, e⟩ => V.frame.equivFun.injective e ▸ hz, fun hx => ⟨x, hx, rfl⟩⟩
  have h2 : x ∈ L ↔ ∀ y ∈ L, V.hT y x ∈ (1 : Submodule (𝓞 E) E) := by
    conv_lhs => rw [← show Formalism.HermitianLatticesTheory.dual V.hT L = L from h]
    simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
  have h3 : ∀ z : E, z ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ z := fun z =>
    Submodule.mem_one.trans ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  rw [h1, h2]
  constructor
  · rintro H _ ⟨y, hy, rfl⟩
    have := (h3 _).1 (H y hy)
    rwa [← herm_coord] at this
  · intro H y hy
    rw [h3, ← herm_coord]
    exact H _ ⟨y, hy, rfl⟩

theorem mem_latLoc_iff (V : Formalism.BasicNotions.HSpace E) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (y : Fin V.rank → LocAlg v) :
    y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V v ↔ y ∈ locLattice v (coordLat V V.L0) := by
  have key : ∀ (a : v.adicCompletionIntegers (maximalRealSubfield E)) (b : v.adicCompletion (maximalRealSubfield E)) (z : E),
      a • (b ⊗ₜ[maximalRealSubfield E] z : LocAlg v) = ((a : v.adicCompletion (maximalRealSubfield E)) * b) ⊗ₜ z := by
    intro a b z
    rw [TensorProduct.smul_tmul']
    rfl
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have := Submodule.smul_mem (locLattice v (coordLat V V.L0)) (⟨a, ha⟩ : v.adicCompletionIntegers (maximalRealSubfield E))
        (Submodule.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩)
      convert this using 1
      funext i
      simp only [Pi.smul_apply, locEmb_apply, key, mul_one]
      rfl
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro hy
    suffices H : ∀ a : v.adicCompletionIntegers (maximalRealSubfield E),
        a • y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V v by
      simpa using H 1
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hy
      intro a
      refine AddSubgroup.subset_closure ⟨a, a.2, x, hx, ?_⟩
      funext i
      simp only [Pi.smul_apply, locEmb_apply, key, mul_one]
      rfl
    | zero => intro a; rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => intro a; rw [smul_add]; exact add_mem (hx a) (hy a)
    | smul c x _ hx => intro a; rw [smul_smul]; exact hx _

theorem exists_conj (hc : CMData (maximalRealSubfield E) E) (V : Formalism.BasicNotions.HSpace E)
    (L : Submodule (𝓞 E) V.V) (h1 : Submodule.IsLattice E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) :
    ∃ γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), HA (Fv (maximalRealSubfield E) v) hc.sig V.gram,
      {v | γ v ≠ 1}.Finite ∧ ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
        (y : Fin V.rank → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E),
        y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V v ↔
          (HA.mat (Fv (maximalRealSubfield E) v) hc.sig V.gram (γ v)).1.mulVec y ∈
            GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) (GlobalTheory.VolRatioCompare.reLat V L h1 h2) v := by
  haveI : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
    Formalism.L2.Pj.unramBridge_holds E fun P hP => by
      obtain ⟨θ, t, e1, e2⟩ := hc.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t :=
        RingOfIntegers.ext e1.symm
      rwa [this]
  have hG : ∀ a b, cc (V.gramᵀ a b) = V.gramᵀ b a := fun a b => V.herm.eq (V.frame b) (V.frame a)
  have hd : V.gramᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero
  obtain ⟨γ, hγ, hfin⟩ := (GlobalTheory.selfDual_lattices_one_genus hG hG hd hd (isLattice_coordLat V L h1 h2)
    (isLattice_coordLat V V.L0 V.standardTuple_isLattice V.baseLattice_isUnimodular)
    (Or.inl ⟨selfDual_coordLat V L h2, selfDual_coordLat V V.L0 V.baseLattice_isUnimodular⟩)).2.1 rfl
  have hmem : ∀ v, γ v ∈ HR (Fv (maximalRealSubfield E) v) hc.sig V.gram := fun v => by
    have h := congrArg Matrix.transpose (hγ v).1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h
    exact h.symm
  refine ⟨fun v => ⟨γ v, hmem v⟩, hfin.subset fun v hv h => hv (Subtype.ext h), fun v y => ?_⟩
  rw [mem_latLoc_iff]
  exact ((hγ v).2 y).trans (mem_latLoc_iff (GlobalTheory.VolRatioCompare.reLat V L h1 h2) v _).symm

end

theorem exists_local_conjugation : ∀ (D : D7) (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L), ∃ γ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), HA (Fv D.host.F v) D.sp.cm.sig V.gram, {v | γ v ≠ 1}.Finite ∧ ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (y : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E), y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) V v ↔ (HA.mat (Fv D.host.F v) D.sp.cm.sig V.gram (γ v)).1.mulVec y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) (GlobalTheory.VolRatioCompare.reLat V L h1 h2) v :=
  fun D V L h1 h2 =>
    haveI : IsCMField D.host.E := D.host.isCMField_hostE
    exists_conj (E := D.host.E) D.sp.cm V L h1 h2

end GlobalTheory.LocalConjugacy
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_nsmul_padded_lattice_mem_basis_product : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' m r : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin (N + m)) D.host.E), OnB D b → (La D (tor0 D cc δ) L L').FG → ∃ R : ℕ, 0 < R ∧ ∀ y ∈ La D (tor0 D cc δ) L L', R • pad D m y ∈ LaB D (tor0 D cc δ) b := by
  first | exact @GlobalTheory.PadCommensurable.nsmul_pad_mem | exact GlobalTheory.PadCommensurable.nsmul_pad_mem | (intros; apply GlobalTheory.PadCommensurable.nsmul_pad_mem <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

theorem _root_.GlobalTheory.T.absNorm_cmPrime_inertPrime_sign : ∀ (D : D7) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → Ev D (Ideal.absNorm P) ∧ (D.host.conj • P = P → sgn D (Ideal.absNorm P) = -1 ∧ ∃ q f : ℕ, q.Prime ∧ InertQ D q ∧ q ≠ 2 ∧ (q : 𝓞 D.host.E) ∈ P ∧ Odd f ∧ Ideal.absNorm P = q ^ (2 * f) ∧ (q ≠ D.host.d → ¬ IsSquare (-(D.host.d : ZMod q)))) ∧ (D.host.conj • P ≠ P → sgn D (Ideal.absNorm P) = 1 ∧ ∀ q : ℕ, q.Prime → (q : 𝓞 D.host.E) ∈ P → ¬ InertQ D q) := by
  first | exact @GlobalTheory.InertResidue.norm_prime | exact GlobalTheory.InertResidue.norm_prime | (intros; apply GlobalTheory.InertResidue.norm_prime <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenThetaTorsion

variable {Λ : AddSubgroup ℂ}

def phase (Λ : AddSubgroup ℂ) (x y : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * (y * (starRingEnd ℂ) x - x * (starRingEnd ℂ) y) / (2 * (area Λ : ℂ)))

theorem phase_ne_zero (x y : ℂ) : phase Λ x y ≠ 0 := Complex.exp_ne_zero _

theorem thetaTranslate_comp_eq_phase_mul_add (x y : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ x (U1 Λ y G) z = phase Λ x y * U1 Λ (x + y) G z := by
  simp only [U1, phase]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc]
  congr 2
  simp only [map_add (f := _)]
  ring

theorem rationalLatticePoint_add {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) : InRationalLattice Λ (x + y) := by
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨n, hn, hy⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have := Λ.add_mem (Λ.nsmul_mem hx n) (Λ.nsmul_mem hy m)
  convert this using 1
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem rationalLatticePoint_of_mem_lattice {x : ℂ} (hx : x ∈ Λ) : InRationalLattice Λ x := ⟨1, one_pos, by simpa using hx⟩

theorem phase_mem (h : IsLat Λ) {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) :
    phase Λ x y ∈ Qbar := by
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨n, hn, hy⟩ := hy
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  obtain ⟨k, hk⟩ := GlobalTheory.exists_int_im_latticeForm L ((hL _).1 hy) ((hL _).1 hx)
  have hA := GlobalTheory.latticeArea_pos L
  rw [GlobalTheory.latticeForm, Complex.div_ofReal_im, div_eq_iff hA.ne', ← GlobalTheory.OddTheta.area_eq L Λ hL] at hk
  rw [← GlobalTheory.OddTheta.area_eq L Λ hL] at hA
  have hA' : (area Λ : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have e := Complex.sub_conj ((n : ℂ) * y * (starRingEnd ℂ) ((m : ℂ) * x))
  rw [hk] at e
  simp only [map_mul, map_natCast, Complex.conj_conj] at e
  push_cast at e
  have hp : phase Λ x y ^ (2 * m * n) = 1 := by
    rw [phase, ← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I k]
    congr 1
    push_cast
    field_simp
    linear_combination e
  rw [mem_algebraicClosure_iff]
  refine IsAlgebraic.of_pow (n := 2 * m * n) (by positivity) ?_
  rw [hp]
  exact isAlgebraic_one

theorem algEnt_const_mul {F : ℂ → ℂ} (hF : AlgEnt F) {κ : ℂ} (hκ : κ ∈ Qbar) :
    AlgEnt fun z => κ * F z := by
  refine ⟨hF.1.const_mul κ, fun n => ?_⟩
  have : coef1 (fun z => κ * F z) n = κ * coef1 F n := by
    rw [coef1, coef1, iteratedDeriv_const_mul_field, mul_div_assoc]
  rw [this]
  exact Qbar.mul_mem hκ (hF.2 n)

theorem thetaTranslate_evenTheta_eq_sigmaStar_translate (t x z : ℂ) : U1 Λ x (GL3Theta.th0 Λ t) z =
    (phase Λ x t / U1 Λ t (sgStar Λ) 0) * U1 Λ (x + t) (sgStar Λ) z := by
  rw [div_mul_eq_mul_div, ← thetaTranslate_comp_eq_phase_mul_add]
  simp only [U1, GL3Theta.th0]
  ring

theorem sigmaStarTranslate_add_lattice_sign_phase (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (y z : ℂ) :
    U1 Λ (y + ω) (sgStar Λ) z =
      ((if ω / 2 ∈ Λ then 1 else -1) / phase Λ y ω) * U1 Λ y (sgStar Λ) z := by
  have e := thetaTranslate_comp_eq_phase_mul_add (Λ := Λ) y ω (sgStar Λ) z
  rw [funext (h.sg_law hω)] at e
  rw [div_mul_eq_mul_div, eq_div_iff (phase_ne_zero _ _), mul_comm, ← e]
  simp only [U1]
  ring

theorem algebraicTaylor_torsionTranslate_evenTheta_alt : ∀ Λ : AddSubgroup ℂ, IsLat Λ → (∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (sgStar Λ))) → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (GL3Theta.th0 Λ t₀)) ∧ ∀ ω ∈ Λ, ∃ κ ∈ Qbar, κ ≠ 0 ∧ ∀ z, U1 Λ (x + ω) (GL3Theta.th0 Λ t₀) z = κ * U1 Λ x (GL3Theta.th0 Λ t₀) z := by
  intro Λ h halg t _ h2 x hx
  have ht : InRationalLattice Λ t := ⟨2, two_pos, by simpa using h2⟩
  have hc : U1 Λ t (sgStar Λ) 0 ∈ Qbar := by
    simpa [coef1] using (halg t ht).2 0
  refine ⟨?_, fun ω hω => ?_⟩
  · rw [funext (thetaTranslate_evenTheta_eq_sigmaStar_translate t x)]
    exact algEnt_const_mul (halg _ (rationalLatticePoint_add hx ht)) (Qbar.div_mem (phase_mem h hx ht) hc)
  · have hω' := rationalLatticePoint_of_mem_lattice hω
    have hs : (if ω / 2 ∈ Λ then 1 else -1 : ℂ) ∈ Qbar := by
      split_ifs
      · exact Qbar.one_mem
      · exact Qbar.neg_mem Qbar.one_mem
    have hs0 : (if ω / 2 ∈ Λ then 1 else -1 : ℂ) ≠ 0 := by
      split_ifs <;> norm_num
    refine ⟨phase Λ (x + ω) t / phase Λ x t * ((if ω / 2 ∈ Λ then 1 else -1) / phase Λ (x + t) ω),
      Qbar.mul_mem (Qbar.div_mem (phase_mem h (rationalLatticePoint_add hx hω') ht) (phase_mem h hx ht))
        (Qbar.div_mem hs (phase_mem h (rationalLatticePoint_add hx ht) hω')),
      mul_ne_zero (div_ne_zero (phase_ne_zero _ _) (phase_ne_zero _ _))
        (div_ne_zero hs0 (phase_ne_zero _ _)), fun z => ?_⟩
    rw [thetaTranslate_evenTheta_eq_sigmaStar_translate, thetaTranslate_evenTheta_eq_sigmaStar_translate, add_right_comm, sigmaStarTranslate_add_lattice_sign_phase h hω]
    have := phase_ne_zero (Λ := Λ) x t
    generalize (if ω / 2 ∈ Λ then 1 else -1 : ℂ) / phase Λ (x + t) ω = s
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    generalize (U1 Λ t (sgStar Λ) 0)⁻¹ = c
    field_simp

end GlobalTheory.EvenThetaTorsion
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem exists_wpF_eq : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ r : ℂ, ∃ Q, Q ∉ Λ ∧ wpF Λ Q = r := by
  intro Λ h r
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  obtain ⟨z, hz, e⟩ := GlobalTheory.exists_weierstrassP_eq L r
  exact ⟨z, (hL z).not.2 hz, (GlobalTheory.OddTheta.wpF_eq L Λ hL z).trans e⟩

end GlobalTheory.EvenTheta
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_matrix_projection_selfDual_lattices : ∀ (D : D7) (n : ℕ) (L₁ L₃ : Lat D n), SD D L₁ → SD D L₃ → ∃ π : Matrix (Fin n) (Fin n) D.host.E, (∀ v ∈ L₁ ⊔ L₃, π.mulVec v ∈ L₁) ∧ (∀ v ∈ L₃, π.mulVec v ∈ L₃) ∧ ∀ v ∈ L₁, v - π.mulVec v ∈ L₃ := by
  first | exact @GlobalTheory.LatticeProjection.exists_matrix_projection | exact GlobalTheory.LatticeProjection.exists_matrix_projection | (intros; apply GlobalTheory.LatticeProjection.exists_matrix_projection <;> assumption)
end
