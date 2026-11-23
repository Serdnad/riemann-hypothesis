module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle225
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace GlobalTheory.GoodTop

namespace MixSubst

variable {n : ℕ}

theorem det_rows_sum (x : Fin n → Fin n → ℂ) (k : Fin n → Fin n → Fin n → ℂ) :
    (Matrix.of fun i d => ∑ c, x i c * k i c d).det =
      ∑ c : Fin n → Fin n, (∏ i, x i (c i)) * (Matrix.of fun i d => k i (c i) d).det := by
  have h : (Matrix.of fun i d => ∑ c, x i c * k i c d) = fun i => ∑ c, x i c • k i c := by
    ext i j
    simp
  rw [h]
  change (Matrix.detRowAlternating : AlternatingMap ℂ (Fin n → ℂ) ℂ (Fin n)) _ = _

  rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem sum_sign_prod (J : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) :
    ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * ∏ i, J (c i) (u i) = (J.submatrix c id).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

theorem alt_sum (J : Matrix (Fin n) (Fin n) ℂ) (k : Fin n → Fin n → Fin n → ℂ) :
    ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i d => ∑ c, J c (u i) * k i c d).det =
      J.det * ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * (Matrix.of fun i d => k i (u i) d).det := by
  have h1 : ∀ u : Equiv.Perm (Fin n), (Matrix.of fun i d => ∑ c, J c (u i) * k i c d).det =
      ∑ c : Fin n → Fin n, (∏ i, J (c i) (u i)) * (Matrix.of fun i d => k i (c i) d).det :=
    fun u => det_rows_sum (fun i c => J c (u i)) k
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, sum_sign_prod]
  symm
  refine Fintype.sum_of_injective (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n)) DFunLike.coe_injective _ _
    (fun c hc => ?_) (fun σ => ?_)
  · have hinj : ¬ Function.Injective c := fun h =>
      hc ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp h), rfl⟩
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by
      simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i, j, h, h'⟩ := hinj
      exact ⟨i, j, h, h'⟩
    rw [Matrix.det_zero_of_row_eq hne (by ext l; simp [hij]), zero_mul]
  · rw [Matrix.det_permute, mul_comm J.det]

theorem alt_sum_two (J J' : Matrix (Fin n) (Fin n) ℂ) (k : Fin n → Fin n → Fin n → ℂ) :
    ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => ∑ c, ∑ d, J c (u i) * J' d b * k i c d).det =
      J.det * J'.det *
        ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * (Matrix.of fun i d => k i (u i) d).det := by
  have h1 : ∀ u : Equiv.Perm (Fin n), (Matrix.of fun i b => ∑ c, ∑ d, J c (u i) * J' d b * k i c d) =
      (Matrix.of fun i d => ∑ c, J c (u i) * k i c d) * J' := by
    intro u
    ext i b
    simp only [Matrix.of_apply, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [h1, Matrix.det_mul, ← mul_assoc, ← Finset.sum_mul]
  rw [alt_sum]
  ring

end MixSubst

theorem mixTop_subst {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r)
    (J J' : Matrix (Fin n) (Fin n) ℂ) :
    mixTop (fun i a b => ∑ c, ∑ d, (J c a * J' d b) • K i c d) = J.det * J'.det * mixTop K := by
  unfold mixTop
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  simp_rw [mul_assoc ((Equiv.Perm.sign π : ℤ) : ℂ), ← Finset.mul_sum]
  rw [mul_left_comm, ← MixSubst.alt_sum_two J J' (fun i c d => K i c d (p i) (p (π i)))]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end GlobalTheory.GoodTop
end
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem mixTop_position_zero {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ : EndValuedForm11Coeffs n r) (j : Fin n) :
    mixTop (intersection_update_fsHerm_neg_one K₁ 0 K₀ j) = 0 := by
  unfold mixTop
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun π _ =>
    Finset.sum_eq_zero fun u _ => mul_eq_zero_of_right _ ?_)
  refine Matrix.det_eq_zero_of_row_eq_zero j fun b => ?_
  simp [intersection_update_fsHerm_neg_one]

theorem cutForm_eq_zero {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ}
    (G₀ G₁ : V n → Matrix r r ℂ) {v : V n} (hρ : ρ =ᶠ[𝓝 v] (fun _ => 0)) :
    cutForm ρ G₀ G₁ v = 0 := by
  have h : dbar (fun x => (ρ x : ℂ)) v = dbar (fun _ : V n => (0 : ℂ)) v :=
    dbar_congr (hρ.mono fun x hx => by simp [hx])
  funext a b
  simp [cutForm, h]

theorem corrC_eq_zero_of_eventuallyEq_zero {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ}
    (G₀ G₁ : V n → Matrix r r ℂ) {v : V n} (hρ : ρ =ᶠ[𝓝 v] (fun _ => 0)) : corrC ρ G₀ G₁ v = 0 := by
  unfold corrC
  rw [cutForm_eq_zero G₀ G₁ hρ]
  exact Finset.sum_eq_zero fun j _ => mixTop_position_zero _ _ j

end GlobalTheory.GoodTop
end

section

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem curvAt_germ_congr {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G G' : V n → Matrix r r ℂ} {v : V n}
    (h : G =ᶠ[𝓝 v] G') : curvAt G v = curvAt G' v := by
  funext a b
  exact curv_congr h _ _

theorem cutForm_germ_congr {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ ρ' : V n → ℝ}
    {G₀ G₁ G₀' G₁' : V n → Matrix r r ℂ} {v : V n} (hρ : ρ =ᶠ[𝓝 v] ρ') (h₀ : G₀ =ᶠ[𝓝 v] G₀')
    (h₁ : G₁ =ᶠ[𝓝 v] G₁') : cutForm ρ G₀ G₁ v = cutForm ρ' G₀' G₁' v := by
  funext a b
  have hc : (fun x => (ρ x : ℂ)) =ᶠ[𝓝 v] fun x => (ρ' x : ℂ) := hρ.mono fun x hx => by simp only [hx]
  simp only [cutForm]
  rw [dbar_congr hc, conn_congr h₀, conn_congr h₁]

theorem corrC_germ_congr {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ ρ' : V n → ℝ}
    {G₀ G₁ G₀' G₁' : V n → Matrix r r ℂ} {v : V n} (hρ : ρ =ᶠ[𝓝 v] ρ') (h₀ : G₀ =ᶠ[𝓝 v] G₀')
    (h₁ : G₁ =ᶠ[𝓝 v] G₁') : corrC ρ G₀ G₁ v = corrC ρ' G₀' G₁' v := by
  simp only [corrC]
  rw [curvAt_germ_congr h₀, curvAt_germ_congr h₁, cutForm_germ_congr hρ h₀ h₁]

end GlobalTheory.GoodTop
end

section

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ENNReal

namespace GlobalTheory.GoodTop

theorem hasInt_congr_on : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : κ → OpenPartialHomeomorph Y (V n)) {S : Set Y}, MeasurableSet S → ∀ {d d' : κ → Y → ℝ} {t : ℝ},
    (∀ i y, y ∈ S → y ∈ (e i).source → d i y = d' i y) → HasInt e d S t → HasInt e d' S t := by
  intro n Y κ _ _ _ e S hS d d' t h hd
  have key : ∀ ε : ℤˣ, glueMeas e (fun i y => ENNReal.ofReal ((ε : ℤ) * d' i y)) S =
      glueMeas e (fun i y => ENNReal.ofReal ((ε : ℤ) * d i y)) S := by
    intro ε
    have hm := GlobalTheory.ChernScale.glueMeas_restrict_eq e
      (ρ := fun i y => ENNReal.ofReal ((ε : ℤ) * d' i y)) (ρ' := fun i y => ENNReal.ofReal ((ε : ℤ) * d i y))
      (c := 1) ENNReal.one_ne_top hS (fun i y hy hyS => by rw [one_mul, h i y hyS hy])
    have := congrArg (fun μ : Measure Y => μ S) hm
    simpa only [one_smul, Measure.restrict_apply_self] using this
  refine ⟨fun ε => by rw [key ε]; exact hd.1 ε, ?_⟩
  rw [← hd.2, measureReal_def, measureReal_def, measureReal_def, measureReal_def, key 1, key (-1)]

end GlobalTheory.GoodTop
end
end

section

noncomputable section

namespace GlobalTheory.LatHatClosed

open scoped TensorProduct RestrictedProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU Topology

variable (F : Type) [Field F] [NumberField F]

theorem isCompact_integralFinite :
    IsCompact {b : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), b.1 v ∈ v.adicCompletionIntegers F} := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

def intAd : AddSubgroup (AF F) where
  carrier := {a | evI F a = 0 ∧ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  zero_mem' := ⟨show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0 from map_zero _,
    fun v => by rw [map_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, fun v => ?_⟩
    · simp only [evI] at ha hb ⊢
      rw [show (a + b).1 = a.1 + b.1 from rfl, map_add (f := _), ha, hb, add_zero]
    · rw [map_add (evFin F v)]
      exact add_mem (ha' v) (hb' v)
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, fun v => ?_⟩
    · simp only [evI] at ha ⊢
      rw [show (-a).1 = -a.1 from rfl, map_neg, ha, neg_zero]
    · rw [map_neg]; exact neg_mem (ha' v)

theorem isCompact_intAd : IsCompact (intAd F : Set (AF F)) := by
  have e : (intAd F : Set (AF F)) = (({0} : Set (InfiniteAdeleRing F)) ×ˢ
      {b : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), b.1 v ∈ v.adicCompletionIntegers F} : Set _) := by
    ext a
    simp only [SetLike.mem_coe, Set.mem_prod, Set.mem_singleton_iff, Set.mem_setOf_eq]
    show (evI F a = 0 ∧ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ↔ _
    have h1 : evI F a = 0 ↔ a.1 = 0 := by
      simp only [evI]; exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff
    rw [h1]
    rfl
  rw [e]
  exact isCompact_singleton.prod (isCompact_integralFinite F)

theorem incV_add {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ} (x y : Fin n → E) :
    incV F (x + y) = incV F x + incV F y := by
  funext i; simp [incV, map_add (f := _)]

theorem incV_zero {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ} :
    incV F (0 : Fin n → E) = 0 := by
  funext i; simp [incV]

theorem incV_zsmul {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ} (m : ℤ) (x : Fin n → E) :
    incV F (m • x) = m • incV F x := by
  funext i; simp [incV, map_zsmul]

theorem isClosed_latHat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (X : Spc F E n), X.L.IsLattice E → IsClosed ((latHat X : AddSubgroup (Fin n → AE F E)) : Set (Fin n → AE F E)) := by
  intro F E _ _ _ _ _ n X hL
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  obtain ⟨s, hs⟩ := Submodule.FG.restrictScalars (R := ℤ) hL.fg
  let ψ : (s → AF F) →+ (Fin n → AE F E) :=
    { toFun := fun c => ∑ i, c i • incV F (i : Fin n → E)
      map_zero' := by simp
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib] }
  let P : AddSubgroup (s → AF F) := AddSubgroup.pi Set.univ (fun _ => intAd F)
  have hψc : Continuous ψ :=
    continuous_finsetSum _ fun i _ => by
      show Continuous fun c : s → AF F => c i • incV F (i : Fin n → E)
      exact (continuous_apply i : Continuous fun c : s → AF F => c i).smul
        (continuous_const : Continuous fun _ : s → AF F => incV F (i : Fin n → E))
  have hPc : IsCompact (P : Set (s → AF F)) := by
    have : (P : Set (s → AF F)) = Set.pi Set.univ (fun _ => (intAd F : Set (AF F))) := by
      ext c; simp [P, AddSubgroup.mem_pi]
    rw [this]; exact isCompact_univ_pi fun _ => isCompact_intAd F
  have hsL : ∀ i ∈ s, i ∈ X.L := fun i hi => by
    have : i ∈ Submodule.span ℤ (s : Set (Fin n → E)) := Submodule.subset_span hi
    rw [hs] at this; exact this
  have key : ∀ x ∈ Submodule.span ℤ (s : Set (Fin n → E)), ∀ a ∈ intAd F, a • incV F x ∈ P.map ψ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      intro a ha
      refine ⟨Pi.single ⟨y, hy⟩ a, ?_, ?_⟩
      · intro i _
        by_cases h : i = ⟨y, hy⟩
        · subst h; simpa using ha
        · simp [Pi.single_apply, h, zero_mem]
      · simp [ψ, Pi.single_apply, ite_smul]
    | zero =>
      intro a _
      rw [incV_zero, smul_zero]; exact zero_mem _
    | add y y' _ _ ih ih' =>
      intro a ha
      rw [incV_add, smul_add]; exact add_mem (ih a ha) (ih' a ha)
    | smul m y _ ih =>
      intro a ha
      rw [incV_zsmul, smul_comm, ← smul_assoc]
      exact ih (m • a) (zsmul_mem ha m)
  have heq : latHat X = P.map ψ := by
    apply le_antisymm
    · refine (AddSubgroup.closure_le _).2 ?_
      rintro z ⟨a, ha0, hav, x, hx, rfl⟩
      have hx' : x ∈ Submodule.span ℤ (s : Set (Fin n → E)) := by rw [hs]; exact hx
      exact key x hx' a ⟨ha0, hav⟩
    · rintro z ⟨c, hc, rfl⟩
      exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure
        ⟨c i, (hc i trivial).1, (hc i trivial).2, i, hsL i i.2, rfl⟩
  rw [heq, AddSubgroup.coe_map]
  exact (hPc.image hψc).isClosed

end GlobalTheory.LatHatClosed
end
end

section

noncomputable section

namespace GlobalTheory.ThK.PlaneEv

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {n d d₁ : ℕ}

def idx (hd : d = d₁ + 2) : Fin n × Fin d ≃ Fin n × Fin d₁ ⊕ Fin n × Fin 2 :=
  ((Equiv.refl (Fin n)).prodCongr ((finCongr hd).trans finSumFinEquiv.symm)).trans (Equiv.prodSumDistrib _ _ _)

def ins0 {R : Type} [Zero R] (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → R) : Fin n × Fin d → R :=
  fun k => Sum.elim x 0 (idx hd k)

section Ins

variable {R : Type} (hd : d = d₁ + 2)

@[simp] theorem planeZeroInsertion_apply_inl [Zero R] (x : Fin n × Fin d₁ → R) (p : Fin n × Fin d₁) :
    ins0 hd x ((idx hd).symm (Sum.inl p)) = x p := by
  simp [ins0]

@[simp] theorem planeZeroInsertion_apply_inr [Zero R] (x : Fin n × Fin d₁ → R) (p : Fin n × Fin 2) :
    ins0 hd x ((idx hd).symm (Sum.inr p)) = 0 := by
  simp [ins0]

theorem ins0_zero [Zero R] : ins0 hd (0 : Fin n × Fin d₁ → R) = 0 := by
  funext k; simp only [ins0]; rcases idx hd k with p | p <;> rfl

theorem ins0_add [AddZeroClass R] (x y : Fin n × Fin d₁ → R) : ins0 hd (x + y) = ins0 hd x + ins0 hd y := by
  funext k; simp only [ins0, Pi.add_apply]; rcases idx hd k with p | p <;> simp

theorem ins0_smul {S : Type} [Zero R] [SMulZeroClass S R] (c : S) (x : Fin n × Fin d₁ → R) :
    ins0 hd (c • x) = c • ins0 hd x := by
  funext k; simp only [ins0, Pi.smul_apply]; rcases idx hd k with p | p <;> simp

theorem ins0_map {R' : Type} [Zero R] [Zero R'] (g : R → R') (hg : g 0 = 0) (x : Fin n × Fin d₁ → R) :
    (fun k => g (ins0 hd x k)) = ins0 hd (fun p => g (x p)) := by
  funext k; simp only [ins0]; rcases idx hd k with p | p <;> simp [hg]

theorem ins0_dotProduct [NonUnitalNonAssocSemiring R] (x : Fin n × Fin d₁ → R) (b : Fin n × Fin d → R) :
    ins0 hd x ⬝ᵥ b = x ⬝ᵥ fun p => b ((idx hd).symm (Sum.inl p)) := by
  simp only [dotProduct]
  rw [← (idx hd).symm.sum_comp, Fintype.sum_sum_type]
  simp

theorem ins0_dotProduct_ins0 [NonUnitalNonAssocSemiring R] (x y : Fin n × Fin d₁ → R) :
    ins0 hd x ⬝ᵥ ins0 hd y = x ⬝ᵥ y := by
  rw [ins0_dotProduct]; simp

end Ins

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

def insertZerosCLM (hd : d = d₁ + 2) :
    (Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  LinearMap.toContinuousLinearMap
    { toFun := ins0 hd
      map_add' := ins0_add hd
      map_smul' := fun c x => ins0_smul hd c x }

@[simp] theorem planeZeroInsertionLinear_apply (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) :
    insertZerosCLM F hd x = ins0 hd x := rfl

theorem norm_le_ins0 (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) : ‖x‖ ≤ ‖ins0 hd x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun p => ?_
  have := norm_le_pi_norm (ins0 hd x) ((idx hd).symm (Sum.inl p))
  rwa [planeZeroInsertion_apply_inl] at this

def ei (hd : d = d₁ + 2) : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁) :=
  SchwartzMap.compCLM ℂ (insertZerosCLM F hd).hasTemperateGrowth
    ⟨1, 1, fun x => by
      have := norm_le_ins0 F hd x
      simp only [planeZeroInsertionLinear_apply, pow_one, one_mul]
      linarith [norm_nonneg (ins0 hd x)]⟩

@[simp] theorem ei_apply (hd : d = d₁ + 2) (f : SInf F (Fin n × Fin d)) (x : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) :
    ei F hd f x = f (ins0 hd x) := rfl

variable {F}

def ev (hd : d = d₁ + 2) (v : Pl F) : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ :=
  LinearMap.funLeft ℂ ℂ (ins0 hd)

@[simp] theorem ev_apply (hd : d = d₁ + 2) (v : Pl F) (φ : (Fin n × Fin d → Fv F v) → ℂ) (x : Fin n × Fin d₁ → Fv F v) :
    ev hd v φ x = φ (ins0 hd x) := rfl


variable (F) in
def evA (hd : d = d₁ + 2) : Fn F n d →ₗ[ℂ] Fn F n d₁ := LinearMap.funLeft ℂ ℂ (ins0 hd)

@[simp] theorem evA_apply (hd : d = d₁ + 2) (Φ : Fn F n d) (x : Fin n × Fin d₁ → AF F) : evA F hd Φ x = Φ (ins0 hd x) := rfl

theorem ei_ne_zero (hd : d = d₁ + 2) : ei (n := n) F hd ≠ 0 := by
  classical
  intro h
  let b : ContDiffBump (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hs : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) := b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  have h1 := congrArg (fun T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁) => T (hs.toSchwartzMap hc) 0) h
  have h2 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  simp [ins0_zero, h2] at h1

theorem evA_pure (hd : d = d₁ + 2) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) :
    evA F hd (pure f φ) = pure (ei F hd f) fun v => ev hd v (φ v) := by
  funext x
  simp only [evA_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, ei_apply, ev_apply]
  rw [ins0_map hd (evI F) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : AF F).1 = 0
    rw [show (0 : AF F).1 = 0 from rfl, map_zero])]
  congr 1
  congr 1
  funext v
  rw [ins0_map hd (evFin F v) (map_zero _)]

end GlobalTheory.ThK.PlaneEv
end
end
