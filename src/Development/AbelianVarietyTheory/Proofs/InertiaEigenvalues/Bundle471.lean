module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle384
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle083
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle280
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle167
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachModuleOfXPowSmulFrobeniusGamma
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle460
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle437
public import GroundTheory.LocalFields.HerbrandFunction
public import GroundTheory.LocalFields.SeparableClosure
public import Mathlib.FieldTheory.Galois.Abelian
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle461
import GroundTheory.LocalFields.ConductorReciprocity
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CycInvariants

theorem exists_reps {G : Type} [Group G] (H N : Subgroup G) [(N.subgroupOf H).FiniteIndex] :
    ∃ S : Finset G, (∀ s ∈ S, s ∈ H) ∧ ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N := by
  classical
  have : Fintype (H ⧸ N.subgroupOf H) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : H ⧸ N.subgroupOf H => ((q.out : H) : G)), ?_, ?_⟩
  · intro s hs
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
    exact q.out.2
  · intro h hh
    refine ⟨((QuotientGroup.mk (⟨h, hh⟩ : H) : H ⧸ N.subgroupOf H).out : H),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · have h1 := QuotientGroup.out_eq' (QuotientGroup.mk (⟨h, hh⟩ : H) : H ⧸ N.subgroupOf H)
      have h2 := QuotientGroup.eq.1 h1
      simpa [Subgroup.mem_subgroupOf] using h2
    · rintro s ⟨hs, hsN⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
      have : (QuotientGroup.mk q.out : H ⧸ N.subgroupOf H) = QuotientGroup.mk (⟨h, hh⟩ : H) :=
        QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using hsN)
      rw [QuotientGroup.out_eq'] at this
      rw [this]

theorem sum_reps_invariant {G M : Type} [Group G] [AddCommMonoid M] (H N : Subgroup G)
    (S : Finset G) (hS : ∀ s ∈ S, s ∈ H) (hu : ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N)
    (f : G → M) (hf : ∀ g, ∀ n ∈ N, f (g * n) = f g) (h : G) (hh : h ∈ H) :
    ∑ s ∈ S, f (h * s) = ∑ s ∈ S, f s := by
  first
  | exact @_root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal
  | exact _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal
  | (apply _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal ..)

variable {l : ℕ} [Fact l.Prime]

theorem stabilizer_finiteIndex (x : Om l) : (MulAction.stabilizer (GQ l) x).FiniteIndex := by
  refine ⟨?_⟩
  rw [MulAction.index_stabilizer]
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hfin : (MulAction.orbit (GQ l) x).Finite := by
    refine ((minpoly ℚ_[l] x).rootSet_finite (Om l)).subset ?_
    rintro _ ⟨g, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    change Polynomial.aeval (g x) _ = 0
    rw [Polynomial.aeval_algEquiv]
    simp
  exact ((Set.ncard_pos hfin).2 ⟨x, MulAction.mem_orbit_self x⟩).ne'

theorem exists_field (F : IntermediateField ℚ_[l] (Om l)) (x : Om l) :
    ∃ (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)), x ∈ L ∧ F ≤ L ∧
      (∀ h ∈ F.fixingSubgroup, ∀ x ∈ L, h x ∈ L) ∧ (∀ s ∈ S, s ∈ F.fixingSubgroup) ∧
      (∀ h ∈ F.fixingSubgroup, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) := by
  have := stabilizer_finiteIndex x
  set N := (MulAction.stabilizer (GQ l) x).normalCore with hN
  set L := IntermediateField.fixedField (F.fixingSubgroup ⊓ N) with hL
  have hle : F.fixingSubgroup ⊓ N ≤ L.fixingSubgroup :=
    (IntermediateField.le_iff_le _ _).1 le_rfl
  have hfi : (L.fixingSubgroup.subgroupOf F.fixingSubgroup).FiniteIndex := by
    refine Subgroup.finiteIndex_of_le (H := N.subgroupOf F.fixingSubgroup) ?_
    intro g hg
    exact hle ⟨g.2, hg⟩
  obtain ⟨S, hS, hu⟩ := exists_reps F.fixingSubgroup L.fixingSubgroup
  refine ⟨L, S, ?_, ?_, ?_, hS, hu⟩
  · rw [hL, IntermediateField.mem_fixedField_iff]
    intro g hg
    exact Subgroup.normalCore_le _ hg.2
  · exact (IntermediateField.le_iff_le _ _).2 inf_le_left
  · intro h hh y hy
    rw [hL, IntermediateField.mem_fixedField_iff] at hy ⊢
    intro g hg
    have h1 : h⁻¹ * g * h ∈ F.fixingSubgroup ⊓ N :=
      ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hg.1) hh,
        by simpa using (Subgroup.normalCore_normal _).conj_mem g hg.2 h⁻¹⟩
    have h2 := congrArg h (hy _ h1)
    simpa using h2

theorem fixed_iff_mem_Ohat : ∀ (l : ℕ) [Fact l.Prime]
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act →
    ∀ (K : FinExt l) (y : PadicComplex l), ‖y‖ ≤ 1 →
      ((∀ h ∈ Hinf K, act h y = y) ↔ y ∈ Ohat K) := by
  intro l _ act hact K y hy
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  constructor
  · intro hfix
    rw [Ohat, Metric.mem_closure_iff]
    intro ε hε
    set δ : ℝ := min (ε / 2) 1 with hδ
    have hδ0 : 0 < δ := lt_min (by linarith) one_pos
    obtain ⟨x, hx⟩ := (UniformSpace.Completion.denseRange_coe (α := Om l)).exists_dist_lt y
      (div_pos hδ0 hl0)
    rw [dist_eq_norm] at hx
    obtain ⟨L, S, hxL, hKL, hst, hS, hu⟩ := exists_field (Kinf K) x
    have hnl : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
      rw [← map_natCast (algebraMap ℚ_[l] (Om l))]
      exact (PadicAlgCl.norm_extends l _).trans Padic.norm_p
    have hlne : (l : Om l) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    obtain ⟨b, hbL, hb1, hb⟩ := GlobalTheory.T.cyclotomicTower_trace_almost_surjective l K L S hKL hst hS hu (l : Om l)
      (natCast_mem _ _) (by rw [hnl]; exact inv_lt_one_of_one_lt₀ hl1)
    set w : Om l := ∑ s ∈ S, s (b * x) with hw
    have hwK : w ∈ Kinf K := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup (Kinf K), IntermediateField.mem_fixedField_iff]
      intro h hh

      rw [hw, map_sum]
      refine sum_reps_invariant _ _ S hS hu (fun g => g (b * x)) ?_ h hh
      intro g n hn
      have := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hn _ (L.mul_mem hbL hxL)
      simp only [AlgEquiv.mul_apply, this]
    set ι := algebraMap (Om l) (PadicComplex l) with hι
    have hιn : ∀ u, ‖ι u‖ = ‖u‖ := fun u => PadicComplex.norm_extends l u
    have hιa : ∀ g u, act g (ι u) = ι (g u) := hact.1
    have hdiff : ι l * y - ι w = ∑ s ∈ S, act s (ι b * (y - ι x)) := by

      rw [← hb, hw, map_sum, map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [map_mul (act s), map_sub, hfix s (hS s hs), hιa, hιa, map_mul, map_mul, mul_sub]
    have hle : ‖ι l * y - ι w‖ ≤ δ / l := by
      rw [hdiff]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_pos hδ0 hl0).le ?_
      intro s _
      rw [hact.2, norm_mul, hιn]
      calc ‖b‖ * ‖y - ι x‖ ≤ 1 * (δ / l) := mul_le_mul hb1 hx.le (norm_nonneg _) one_pos.le
        _ = δ / l := one_mul _
    have hle' : ‖y - ι (w / l)‖ ≤ δ := by
      have h1 : ι l * y - ι w = ι l * (y - ι (w / l)) := by
        rw [mul_sub, ← map_mul, mul_div_cancel₀ _ hlne]
      rw [h1, norm_mul, hιn, hnl, div_eq_inv_mul δ] at hle
      exact le_of_mul_le_mul_left hle (inv_pos.2 hl0)
    refine ⟨ι (w / l), ⟨⟨w / l, div_mem hwK (natCast_mem _ _), rfl⟩, ?_⟩, ?_⟩
    · have h1 : ι (w / l) = y + -(y - ι (w / l)) := by ring
      rw [h1]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy ?_)
      rw [norm_neg]
      exact hle'.trans (min_le_right _ _)
    · rw [dist_eq_norm]
      exact lt_of_le_of_lt (hle'.trans (min_le_left _ _)) (by linarith)
  · intro hyO h hh
    have hc : Continuous (act h) :=
      (AddMonoidHomClass.isometry_of_norm (act h) (hact.2 h)).continuous
    refine closure_minimal (t := {z | act h z = z}) ?_ (isClosed_eq hc continuous_id) hyO
    rintro _ ⟨⟨u, hu, rfl⟩, -⟩
    change act h (u : PadicComplex l) = (u : PadicComplex l)
    rw [hact.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh u hu]

end GlobalTheory.CycInvariants
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.FracAlg

theorem ratio_adjoin {k Ω B D : Type} [Field k] [Field Ω] [Algebra k Ω] [CommRing B] [CommRing D] [IsDomain D]
    (ι : B →+* D) (hι : Function.Injective ι) (o : Ω →+* D)
    (hk : ∀ c : k, ∃ b : B, ι b = o (algebraMap k Ω c)) (x : Ω)
    (hx : ∃ a b : B, b ≠ 0 ∧ ι a = o x * ι b) (y : Ω) (hy : y ∈ IntermediateField.adjoin k {x}) :
    ∃ a b : B, b ≠ 0 ∧ ι a = o y * ι b := by
  have hne : ∀ b : B, b ≠ 0 → ι b ≠ 0 := fun b hb h => hb (hι (by rw [h, map_zero]))
  have hmul : ∀ b b' : B, b ≠ 0 → b' ≠ 0 → b * b' ≠ 0 := fun b b' hb hb' h =>
    mul_ne_zero (hne b hb) (hne b' hb') (by rw [← map_mul, h, map_zero])
  have h1 : (1 : B) ≠ 0 := fun h => one_ne_zero (α := D) (by rw [← map_one ι, h, map_zero])
  induction hy using IntermediateField.adjoin_induction with
  | mem z hz => rw [Set.mem_singleton_iff.1 hz]; exact hx
  | algebraMap c =>
    obtain ⟨b, hb⟩ := hk c
    exact ⟨b, 1, h1, by rw [hb, map_one, mul_one]⟩
  | add z w _ _ hz hw =>
    obtain ⟨a, b, hb, e⟩ := hz
    obtain ⟨a', b', hb', e'⟩ := hw
    refine ⟨a * b' + a' * b, b * b', hmul _ _ hb hb', ?_⟩
    simp only [map_add (f := _), map_mul, e, e']
    ring
  | inv z _ hz =>
    obtain ⟨a, b, hb, e⟩ := hz
    by_cases h0 : z = 0
    · exact ⟨0, 1, h1, by simp [h0]⟩
    · have ho : o z ≠ 0 := by simpa using h0
      refine ⟨b, a, fun h => mul_ne_zero ho (hne b hb) (by rw [← e, h, map_zero]), ?_⟩
      rw [e, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul]
  | mul z w _ _ hz hw =>
    obtain ⟨a, b, hb, e⟩ := hz
    obtain ⟨a', b', hb', e'⟩ := hw
    refine ⟨a * a', b * b', hmul _ _ hb hb', ?_⟩
    simp only [map_mul, e, e']
    ring

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris


open GlobalTheory.MemLoc in
theorem norm_of_ratio {l : ℕ} [Fact l.Prime] (C : Core l) (a b : Per.Bcris l) (x : Om l) (hb : b ≠ 0)
    (hx : x ≠ 0) (e : C.ι a = C.oD x * C.ι b) : ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k := by
  obtain ⟨r, a', ha'⟩ := bcris_eq_acris_localization_periodT_alt l C a
  obtain ⟨s, b', hb'⟩ := bcris_eq_acris_localization_periodT_alt l C b
  have hu := (core_t_unit_fil l C).1
  have hA : algebraMap (Per.Acris l) (Per.Bcris l) (a' * C.t ^ s) =
      a * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ (r + s) := by
    rw [map_mul, map_pow, ← ha', pow_add, mul_assoc]
  have hB : algebraMap (Per.Acris l) (Per.Bcris l) (b' * C.t ^ r) =
      b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ (r + s) := by
    rw [map_mul, map_pow, ← hb', add_comm r s, pow_add, mul_assoc]
  refine GlobalTheory.MemLoc.GaussCore.norm_eq_zpow l C (a' * C.t ^ s) (b' * C.t ^ r) x (fun h => hb ?_) hx ?_
  · rw [h, map_zero] at hB
    exact ((hu.pow _).mul_left_eq_zero).1 hB.symm
  · apply (BdRField.bdR_isField l).2.1
    rw [map_mul (algebraMap (Per.BdRp l) (Per.BdR l)), ← C.ι_j, ← C.ι_j, hA, hB, map_mul C.ι, map_mul C.ι, e,
      mul_assoc]
    rfl

end

theorem mem_Kur_of_ratio : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (a b : P.R.B) (x : Om l), b ≠ 0 → P.ιB a = algebraMap (Om l) P.R.BdR x * P.ιB b → x ∈ MaximalUnramifiedExtension l := by
  intro l _ P AI T a b x hb e
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨hF, -, hinj, -⟩ := GlobalTheory.Per.TiedField.tied_field l P AI T
  have : IsDomain P.R.BdR := hF.isDomain
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral _
  refine GlobalTheory.UnramValue.le_Kur_of_norm l ⟨IntermediateField.adjoin ℚ_[l] {x}, IntermediateField.adjoin.finiteDimensional hint⟩
    (fun y hy hy0 => ?_) (IntermediateField.mem_adjoin_simple_self ℚ_[l] x)
  obtain ⟨a', b', hb', e'⟩ := ratio_adjoin (k := ℚ_[l]) (P.ιB : P.R.B →+* P.R.BdR) hinj
    (algebraMap (Om l) P.R.BdR)
    (fun c => ⟨algebraMap ℚ_[l] P.R.B c,
      (P.ιB.commutes c).trans (IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR c)⟩) x ⟨a, b, hb, e⟩ y hy
  refine norm_of_ratio C (T.eB a') (T.eB b') y (fun h => hb' (T.eB.injective (h.trans (map_zero _).symm))) hy0 ?_
  rw [← hC.ι, ← hC.ι, ← hC.o, ← map_mul]
  exact congrArg T.eD e'

end GlobalTheory.FracAlg
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TensorInj

theorem exists_div_of_mem_closure {A D : Type} [CommRing A] [Field D] (g : A →+* D) {y : D}
    (hy : y ∈ Subfield.closure (Set.range g)) (h0 : y ≠ 0) : ∃ a b : A, b ≠ 0 ∧ g a = y * g b := by
  obtain ⟨p, hp, q, hq, e⟩ := Subfield.mem_closure_iff.1 hy
  have hr : Subring.closure (Set.range g) = g.range := by
    rw [← RingHom.coe_range, Subring.closure_eq]
  rw [hr] at hp hq
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, rfl⟩ := hq
  have hb : g b ≠ 0 := fun h => h0 (by rw [← e, h, div_zero])
  refine ⟨a, b, fun h => hb (by rw [h, map_zero]), ?_⟩
  rw [← e, div_mul_cancel₀ _ hb]

theorem indep_of_fractions (l : ℕ) [Fact l.Prime] {A B D : Type} [CommRing A] [CommRing B] [CommRing D]
    (hD : IsField D) (g : A →+* D) (ι : B →+* D) (hι : Function.Injective ι) (o : Om l →+* D)
    (hB : ∀ b : B, ∃ a a' : A, g a' ≠ 0 ∧ ι b * g a' = g a)
    (hu : ∀ c : ↥(MaximalUnramifiedExtension l), ∃ b : B, ι b = o (c : Om l))
    (hv : ∀ (a b : A) (x : Om l), b ≠ 0 → x ≠ 0 → g a = o x * g b → ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k)
    (m : ℕ) (x : Fin m → Om l) (hx : LinearIndependent ↥(MaximalUnramifiedExtension l) x) (b : Fin m → B)
    (hb : ∑ i, o (x i) * ι (b i) = 0) (i : Fin m) : b i = 0 := by
  letI : Field D := hD.toField
  let F : Subfield D := Subfield.closure (Set.range g)
  have hg : ∀ a, g a ∈ F := fun a => Subfield.subset_closure ⟨a, rfl⟩
  have hιF : ∀ b, ι b ∈ F := fun b => by
    obtain ⟨a, a', h0, e⟩ := hB b
    rw [eq_div_of_mul_eq h0 e]
    exact F.div_mem (hg a) (hg a')
  have hK : ∀ c : ↥(MaximalUnramifiedExtension l), o (c : Om l) ∈ F := fun c => by
    obtain ⟨b, e⟩ := hu c
    exact e ▸ hιF b
  let E : IntermediateField ℚ_[l] (Om l) :=
    (F.comap o).toIntermediateField fun q => hK (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q)
  have hE : ∀ y : Om l, o y ∈ F → y ∈ MaximalUnramifiedExtension l := fun y hy => by
    have hint : IsIntegral ℚ_[l] y := Algebra.IsIntegral.isIntegral y
    have hle : IntermediateField.adjoin ℚ_[l] {y} ≤ E :=
      IntermediateField.adjoin_simple_le_iff.2 hy
    refine GlobalTheory.UnramValue.le_Kur_of_norm l ⟨IntermediateField.adjoin ℚ_[l] {y},
      IntermediateField.adjoin.finiteDimensional hint⟩ (fun z hz h0 => ?_)
      (IntermediateField.mem_adjoin_simple_self ℚ_[l] y)
    obtain ⟨a, a', h1, e⟩ := exists_div_of_mem_closure g (y := o z) (hle hz) ((map_ne_zero o).2 h0)
    exact hv a a' z h1 h0 e
  haveI : IsGalois ℚ_[l] (Om l) := {}
  haveI : IsGalois ↥(MaximalUnramifiedExtension l) (Om l) := IsGalois.tower_top_of_isGalois ℚ_[l] _ _
  have := GlobalTheory.T.eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent ↥(MaximalUnramifiedExtension l) (Om l) D o F
    (fun y => ⟨fun h => ⟨⟨y, hE y h⟩, rfl⟩, fun ⟨c, h⟩ => h ▸ hK c⟩) m x hx (fun i => ι (b i))
    (fun i => hιF _) hb i
  exact hι (this.trans (map_zero ι).symm)

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem tensorInj (l : ℕ) [Fact l.Prime] (c : Core l) : c.TensorInj := by
  obtain ⟨-, hinj, hD, -⟩ := BdRField.bdR_isField l
  have hι : Function.Injective c.ι := (ULaws.u_laws l c).2.2.2.1
  haveI : Nontrivial (Per.BdR l) := ⟨hD.exists_pair_ne⟩
  refine indep_of_fractions l hD ((algebraMap (Per.BdRp l) (Per.BdR l)).comp c.j) c.ι hι c.oD
    (fun b => ?_) (fun x => ⟨c.u x, c.ι_u x⟩) (fun a b x hb hx e => ?_)
  · obtain ⟨r, a, e⟩ := bcris_eq_acris_localization_periodT_alt l c b
    refine ⟨a, c.t ^ r, ?_, ?_⟩
    · rw [RingHom.comp_apply, ← c.ι_j, map_pow]
      exact ((((core_t_unit_fil l c).1).pow r).map c.ι).ne_zero
    · rw [RingHom.comp_apply, RingHom.comp_apply, ← c.ι_j, ← c.ι_j, ← map_mul, map_pow, e]
  · refine @GlobalTheory.MemLoc.GaussCore.norm_eq_zpow l _ c a b x hb hx (hinj ?_)
    rw [map_mul]
    exact e

end GlobalTheory.MemLoc.TensorInj
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitMatch_all : ∀ r, UnitMatch r :=
  GlobalTheory.T.jacquetRallisUnitMatch_of_weilRep_quadratic GlobalTheory.T.weilRepresentation_quadraticField_exists

end GlobalTheory.JR
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachKernel_mem_frobeniusSpan_after_Q_pow : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))) := by
  first | exact @GlobalTheory.NL.PhiSpanKer.main | exact GlobalTheory.NL.PhiSpanKer.main | (intros; apply GlobalTheory.NL.PhiSpanKer.main <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices


theorem _root_.GlobalTheory.T.mem_wachModule_of_X_pow_smul_frobenius_gamma : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M a : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → W.γ T m - m ∈ aN W T letπ → W.X ^ a • m ∈ W.N T → m ∈ W.N T := by
  first | exact @GlobalTheory.NL.ExtLattice.mem_N | exact GlobalTheory.NL.ExtLattice.mem_N | (intros; apply GlobalTheory.NL.ExtLattice.mem_N <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tiltUntilt_add_estimate_le : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ) (x y : Fl l), ‖sh x‖ ≤ r → ‖sh y‖ ≤ r → ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (x + y)‖ ≤ r := by
  first | exact @GlobalTheory.PSer.sh_add_le | exact GlobalTheory.PSer.sh_add_le | (intros; apply GlobalTheory.PSer.sh_add_le <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.untiltFrobeniusLaurentSeries_eq_polynomial_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (σ : Fl l), 1 ≤ h → μ ≠ 0 → sh σ = l → ∃ (t : ℂ_[l]) (D E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ), t ≠ 0 ∧ M + h ≤ E ∧ (∀ k, k ≤ E → ‖a k‖ ≤ 1) ∧ ‖a (M + h)‖ = 1 ∧ ‖(l : ℂ_[l])‖ ≤ ρ ∧ ρ < 1 ∧ ‖(l : ℂ_[l])‖ * ρ ^ l ^ D = ‖(l : ℂ_[l])‖ ^ l ^ h ∧ ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ ∧ (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) ∧ ∀ u : Fl l, ‖∑ i : Fin h, μ i * lam h i (σ * u ^ l ^ D) - t * ∑ k ∈ Finset.range (E + 1), a k * sh u ^ l ^ k‖ ≤ ‖(l : ℂ_[l])‖ * ‖t‖ := by
  first | exact @GlobalTheory.PolyRoot.poly_root_mod_l | exact GlobalTheory.PolyRoot.poly_root_mod_l | (intros; apply GlobalTheory.PolyRoot.poly_root_mod_l <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.untiltFrobeniusDoubleSeries_hasSum_and_norm_bounds : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (y : ℕ → Fl l), 1 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) ∧ ‖abelian₂ h j y - lam h j (y 0)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r ∧ ‖abelian₂ h j y‖ ≤ gam l h j r ∧ ∀ N : ℕ, abelian₂ h j (fun k => y k ^ l ^ (h * N)) = (l : ℂ_[l]) ^ N * abelian₂ h j y := by
  first | exact @GlobalTheory.PSer.Lam_main | exact GlobalTheory.PSer.Lam_main | (intros; apply GlobalTheory.PSer.Lam_main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem pow_mem_upperRamificationGroup_real : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e : ℕ) (v : ℝ), 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M v, σ ^ p ∈ upperRamificationGroup F ↥M (min (2 * v) (v + e)) := by
  intro F _ _ _ _ M _ _ p e v hv hOrd σ hσ

  have hc : (0 : ℤ) ≤ ⌈v⌉ := Int.ceil_nonneg hv
  have hn : ((⌈v⌉.toNat : ℕ) : ℝ) = ((⌈v⌉ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hc
  have hσn : σ ∈ upperRamificationGroup F ↥M ((⌈v⌉.toNat : ℕ) : ℝ) := by
    rw [hn, ← upperRamificationGroup_eq_ceil]
    exact hσ
  have hpow := GlobalTheory.T.pow_mem_upperRamificationGroup_abelian_nat' F M p e ⌈v⌉.toNat hOrd σ hσn

  have hvn : v ≤ ((⌈v⌉.toNat : ℕ) : ℝ) := by
    rw [hn]; exact Int.le_ceil v
  have hle : min (2 * v) (v + e) ≤ ((min (2 * ⌈v⌉.toNat) (⌈v⌉.toNat + e) : ℕ) : ℝ) := by
    push_cast
    exact min_le_min (by linarith) (by linarith)
  exact upperRamificationGroup_antitone F ↥M hle hpow

end GlobalTheory.PMon.Ram
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exists_phiGammaModel_extension_cocycle_pair : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (A : Ob k G) (z : G → Fin A.m → k), z ∈ M.twistedModelAdmissibleCocycles A → ∃ (N : Lats k n A.m) (b g : ZMod n → Vc k A.m), M.Model A N ∧ Repr F A z b g ∧ InZZ (F.D A) Dt N b g := by
  first | exact @GlobalTheory.TopSteps.ExtPair.exists_model_repr_inZZ | exact GlobalTheory.TopSteps.ExtPair.exists_model_repr_inZZ | (intros; apply GlobalTheory.TopSteps.ExtPair.exists_model_repr_inZZ <;> assumption)
end
