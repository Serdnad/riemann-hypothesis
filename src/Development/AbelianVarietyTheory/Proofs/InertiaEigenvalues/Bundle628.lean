module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle559
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle606
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle582
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle565
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle564
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle605
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle589
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle021
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.BKReal GlobalTheory.BKGal
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.XiFil

variable {l : ℕ} [Fact l.Prime]

theorem mem_FilD_zero_iff (x : Per.BdR l) :
    x ∈ Per.FilD l 0 ↔ ∃ z : Per.BdRp l, x = algebraMap (Per.BdRp l) (Per.BdR l) z := by
  have h := GlobalTheory.BdRQuot.mem_FilD_nat (l := l) 0 x
  rw [Nat.cast_zero] at h
  rw [h]
  constructor
  · rintro ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, GlobalTheory.BdRQuot.mem_filtration_zero z, rfl⟩

theorem mul_mem_FilD_of_zero {x y : Per.BdR l} {n : ℤ} (hx : x ∈ Per.FilD l 0) (hy : y ∈ Per.FilD l n) :
    x * y ∈ Per.FilD l n := by
  obtain ⟨z, rfl⟩ := (mem_FilD_zero_iff x).1 hx
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ z hy

theorem mul_mem_FilD_neg {x y : Per.BdR l} {m : ℕ} (hx : x ∈ Per.FilD l m) (hy : y ∈ Per.FilD l (-(m : ℤ))) :
    x * y ∈ Per.FilD l 0 := by
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.BdRField.exists_isEps l
  obtain ⟨w, rfl⟩ := (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff he _ x).1 hx
  obtain ⟨w', rfl⟩ := (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff he _ y).1 hy
  rw [mul_mul_mul_comm, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, one_mul,
    ← map_mul]
  exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero _

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]

def filO (C : GlobalTheory.MemLoc.Core l) (n : ℤ) : Submodule O (OB l O) :=
  Submodule.span O {x | ∃ β : Per.Bcris l, C.ι β ∈ Per.FilD l n ∧ x = (1 : O) ⊗ₜ[ℤ_[l]] β}

variable {O} {K : Type} [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

def filT (C : GlobalTheory.MemLoc.Core l) (T : LocLat G ℚ_[l] K O) (n : ℤ) : Submodule O (TW (OB l O) T) :=
  Submodule.span O {w | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l n ∧
    w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x}

theorem smul_mem_filT {C : GlobalTheory.MemLoc.Core l} {T : LocLat G ℚ_[l] K O} {a b c : ℤ}
    (hmul : ∀ β β' : Per.Bcris l, C.ι β ∈ Per.FilD l a → C.ι β' ∈ Per.FilD l b → C.ι (β * β') ∈ Per.FilD l c)
    {r : OB l O} (hr : r ∈ filO O C a) {v : TW (OB l O) T} (hv : v ∈ filT C T b) : r • v ∈ filT C T c := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨β, hβ, rfl⟩ := hr
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨β', x, hβ', rfl⟩ := hv
      rw [smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      exact Submodule.subset_span ⟨β * β', x, hmul β β' hβ hβ', rfl⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add v v' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | smul o v _ h => rw [smul_comm]; exact Submodule.smul_mem _ o h
  | zero => rw [zero_smul]; exact zero_mem _
  | add r r' _ _ h h' => rw [add_smul]; exact add_mem h h'
  | smul o r _ h => rw [smul_assoc]; exact Submodule.smul_mem _ o h

theorem smul_mem_filT_of_zero {C : GlobalTheory.MemLoc.Core l} {T : LocLat G ℚ_[l] K O} {n : ℤ} {r : OB l O}
    (hr : r ∈ filO O C 0) {v : TW (OB l O) T} (hv : v ∈ filT C T n) : r • v ∈ filT C T n :=
  smul_mem_filT (fun β β' h h' => by rw [map_mul]; exact mul_mem_FilD_of_zero h h') hr hv

theorem smul_mem_filT_neg {C : GlobalTheory.MemLoc.Core l} {T : LocLat G ℚ_[l] K O} {m : ℕ} {r : OB l O}
    (hr : r ∈ filO O C m) {v : TW (OB l O) T} (hv : v ∈ filT C T (-(m : ℤ))) : r • v ∈ filT C T 0 :=
  smul_mem_filT (fun β β' h h' => by rw [map_mul]; exact mul_mem_FilD_neg h h') hr hv

end GlobalTheory.BKGal.XiFil
end
end

section

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.ValGroupKprime

theorem norm_Kunr (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] {c : Om l} (hc : c ∈ Kunr l a) (h0 : c ≠ 0) :
    ∃ m : ℤ, ‖c‖ = (l : ℝ) ^ m := by
  have hK : MaximalUnramifiedExtension l ≤ ReciprocityTheory.ChartRestriction.L1.kurAlg l := by
    refine IntermediateField.adjoin_le_iff.2 fun x ⟨m, hm, hlm, hx⟩ => ?_
    refine ReciprocityTheory.ChartRestriction.L1.mem_kurAlg.2
      (Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨m, hm, hlm, ?_⟩))
    rw [← map_pow, hx, map_one]
  have h1 := ReciprocityTheory.ChartRestriction.L1.mem_kurAlg.1 (hK (Kunr_le_Kur l a hc))
  obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.L1.kur_val l h1 ((map_ne_zero _).2 h0)
  exact ⟨m, by rw [← hm]; exact (PadicComplex.norm_extends l c).symm⟩

theorem norm_natCast_l (l : ℕ) [Fact l.Prime] : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [Padic.norm_p] at this
  simpa using this

theorem norm_pow_field (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e)
    (y : Om l) (hy : y ∈ (ϖ.field a).1) (h0 : y ≠ 0) : ∃ j : ℤ, ‖y‖ ^ e = (l : ℝ) ^ j := by
  set π := ϖ.seq 0 with hπdef
  set E := Kunr l a with hE
  have hπ0 : π ≠ 0 := ϖ.seq_ne_zero 0

  have hy' : y ∈ IntermediateField.adjoin E {π} := by
    have h1 : (ϖ.field a).1 = (IntermediateField.adjoin E {π}).restrictScalars ℚ_[l] := by
      rw [IntermediateField.restrictScalars_adjoin_eq_sup]; rfl
    rw [h1] at hy; exact hy
  have hint : IsAlgebraic E π :=
    (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) π).tower_top.isAlgebraic
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint] at hy'

  let M : Submodule E (Om l) := Submodule.span E (Set.range fun i : Fin e => π ^ (i : ℕ))
  have hlE : (-(l : Om l)) ∈ E := E.neg_mem (IntermediateField.natCast_mem E l)
  have hpow : ∀ n, π ^ n ∈ M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < e
      · exact Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hn)
        have hk : k < e + k := by have := NeZero.pos e; omega
        have h2 : π ^ (e + k) = (⟨-(l : Om l), hlE⟩ : E) • π ^ k := by
          rw [pow_add, ϖ.seq_zero]; rfl
        rw [h2]; exact M.smul_mem _ (ih k hk)
  have hyM : y ∈ M := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
    obtain ⟨p, rfl⟩ := hy'
    show Polynomial.aeval π p ∈ M
    rw [Polynomial.aeval_eq_sum_range]
    exact Submodule.sum_mem _ fun i _ => M.smul_mem _ (hpow i)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hyM
  set t : Fin e → Om l := fun i => (c i : Om l) * π ^ (i : ℕ) with ht
  have hyt : y = ∑ i, t i := by rw [← hc]; rfl

  have hnπ : ‖π‖ ^ e = (l : ℝ)⁻¹ := by
    rw [← norm_pow, ϖ.seq_zero, norm_neg, norm_natCast_l]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith

  have hnt : ∀ i, t i ≠ 0 → ∃ m : ℤ, ‖t i‖ ^ e = (l : ℝ) ^ ((e : ℤ) * m - (i : ℕ)) := by
    intro i hi
    have hci : (c i : Om l) ≠ 0 := fun h => hi (by simp [ht, h])
    obtain ⟨m, hm⟩ := norm_Kunr l a (c i).2 hci
    refine ⟨m, ?_⟩
    rw [ht]; dsimp only
    rw [norm_mul, norm_pow, mul_pow, hm, ← pow_mul, mul_comm (i : ℕ) e, pow_mul, hnπ,
      zpow_sub₀ hl0.ne', inv_pow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm m, zpow_natCast, div_eq_mul_inv]

  have hdist : ∀ i j, t i ≠ 0 → t j ≠ 0 → ‖t i‖ = ‖t j‖ → i = j := by
    intro i j hi hj hij
    obtain ⟨m1, h1⟩ := hnt i hi
    obtain ⟨m2, h2⟩ := hnt j hj
    have h3 : (e : ℤ) * m1 - (i : ℕ) = (e : ℤ) * m2 - (j : ℕ) :=
      zpow_right_injective₀ hl0 hl1.ne' (show (l : ℝ) ^ _ = (l : ℝ) ^ _ by rw [← h1, ← h2, hij])
    have h4 : ((i : ℕ) : ℤ) - (j : ℕ) = 0 := by
      have hi' := i.2
      have hj' := j.2
      refine Int.eq_zero_of_abs_lt_dvd (m := (e : ℤ)) ⟨m1 - m2, by linear_combination -h3⟩ ?_
      rw [abs_lt]; constructor <;> omega
    exact Fin.ext (by omega)

  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => ‖t i‖)
    (Finset.univ_nonempty_iff.2 ⟨⟨0, NeZero.pos e⟩⟩)
  have ht0 : t i0 ≠ 0 := by
    intro h
    apply h0
    rw [hyt]
    refine Finset.sum_eq_zero fun i _ => norm_eq_zero.1 (le_antisymm ?_ (norm_nonneg _))
    simpa [h] using hi0 i (Finset.mem_univ _)
  have hpos : 0 < ‖t i0‖ := norm_pos_iff.2 ht0
  have hrest : ‖∑ i ∈ Finset.univ.erase i0, t i‖ < ‖t i0‖ := by
    have hterm : ∀ i ∈ Finset.univ.erase i0, ‖t i‖ < ‖t i0‖ := by
      intro i hi
      by_cases hti : t i = 0
      · rw [hti, norm_zero]; exact hpos
      refine lt_of_le_of_ne (hi0 i (Finset.mem_univ _)) fun h => ?_
      exact (Finset.mem_erase.1 hi).1 (hdist i i0 hti ht0 h)
    generalize Finset.univ.erase i0 = s at hterm ⊢
    induction s using Finset.induction_on with
    | empty => simpa using hpos
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
        (max_lt (hterm i (Finset.mem_insert_self _ _))
          (ih (fun j hj => hterm j (Finset.mem_insert_of_mem hj))))
  have hy2 : ‖y‖ = ‖t i0‖ := by
    rw [hyt, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0),
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hrest.ne', max_eq_left hrest.le]
  obtain ⟨m, hm⟩ := hnt i0 ht0
  exact ⟨_, by rw [hy2, hm]⟩

end GlobalTheory.ValGroupKprime
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.CrysInteg

theorem mem_of_semiBC {A B M N Q : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [AddCommGroup Q] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u)
    (g : N →+ Q) (H : AddSubgroup Q) (hg : ∀ (r : B) (x : M), g (r • u x) ∈ H) (y : N) : g y ∈ H := by
  have hspan : y ∈ Submodule.span B (Set.range u) := by
    have h1 : (Submodule.span B (Set.range u)).mkQ = 0 := h.hom_ext fun x => by
      rw [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨x, rfl⟩
    have := LinearMap.congr_fun h1 y
    rwa [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  have key : ∀ z ∈ Submodule.span B (Set.range u), ∀ r : B, g (r • z) ∈ H := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      exact fun r => hg r x
    | zero =>
      intro r
      rw [smul_zero, map_zero]
      exact H.zero_mem
    | add z w _ _ hz hw =>
      intro r
      rw [smul_add, map_add (f := _)]
      exact add_mem (hz r) (hw r)
    | smul s z _ hz =>
      intro r
      rw [smul_smul]
      exact hz _
  have := key y hspan 1
  rwa [one_smul] at this

def divSub {R σ ι : Type} [CommRing R] (S : Subring R) (τ : σ) (i : ι) (k : ℕ) :
    AddSubgroup (σ → ι → R⟦X⟧) where
  carrier := {v | (k.factorial : R) * coeff k (v τ i) ∈ S}
  add_mem' {v w} hv hw := by
    change (k.factorial : R) * coeff k (v τ i + w τ i) ∈ S
    rw [map_add (f := _), mul_add]
    exact add_mem hv hw
  zero_mem' := by
    change (k.factorial : R) * coeff k (0 : R⟦X⟧) ∈ S
    rw [map_zero, mul_zero]
    exact zero_mem _
  neg_mem' {v} hv := by
    change (k.factorial : R) * coeff k (-(v τ i)) ∈ S
    rw [map_neg, mul_neg]
    exact neg_mem hv

theorem factorial_mul_coeff_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ x, c x ∈ P.M) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ y (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (J τ y) ∈ S O K e) → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → ∀ y τ i (k : ℕ), (k.factorial : K⟦X⟧) * coeff k (lam y τ i) ∈ S O K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P EE c hc PP p J hJ lam hsm htr y τ i k
  refine mem_of_semiBC (EE.tr_bc p) lam (divSub (S O K e).toSubring τ i k) (fun r x => ?_) y
  change (k.factorial : K⟦X⟧) * coeff k (lam (r • EE.tr p x) τ i) ∈ S O K e
  rw [hsm, htr, PowerSeries.coeff_mul_C, ← mul_assoc]
  exact mul_mem (hJ τ r k) (A_le_S l e (frob_mem_A l (mem_tot.1 (hc x) (τ - 1) i)))

end GlobalTheory.BKGal.CrysInteg
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem wq_map_injective {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [IsDomain O]
    [CharZero O] (w : Wq l a →+* O) : Function.Injective w := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨n, u, rfl⟩ := WittVector.exists_eq_pow_p_mul' x h0
  rw [map_mul, map_pow, map_natCast] at hx
  rcases mul_eq_zero.1 hx with h | h
  · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h
  · exact (u.isUnit.map w).ne_zero h

theorem nonempty_bk_of_finExt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), Nonempty (BK K) := by
  intro l hl K
  obtain ⟨hdvr, hfin, hunit⟩ := GlobalTheory.T.ringOfIntegers_finiteExt_isDVR_finite_unit_iff l K
  obtain ⟨a, ha, w, hK, hw, hres⟩ := GlobalTheory.T.exists_witt_residueField_in_ringOfIntegers l K
  letI : Algebra (Wq l a) ↥(OL K) := w.toRingHom.toAlgebra
  have halg : ∀ c, algebraMap (Wq l a) ↥(OL K) c = w c := fun _ => rfl
  haveI : IsScalarTower ℤ_[l] (Wq l a) ↥(OL K) :=
    IsScalarTower.of_algebraMap_eq fun z => (w.commutes z).symm
  haveI : Module.Finite (Wq l a) ↥(OL K) := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  obtain ⟨π, Ep, hπ, hE, hne, hmin⟩ :=
    GlobalTheory.T.exists_uniformiser_eisenstein_not_in_X_pow l a ↥(OL K) (wq_map_injective _) hres
  obtain ⟨str, hstr⟩ := GlobalTheory.T.breuilKisin_quotient_eisenstein_equiv l a ↥(OL K) π Ep hE hmin
  obtain ⟨hδ, hc⟩ := GlobalTheory.T.eisenstein_distinguished_powerSeries_adicComplete l a Ep hE
  obtain ⟨fl, ev, hfl, hX, hC, hφ⟩ :=
    GlobalTheory.T.exists_breuilKisin_eval_teichmuller_tilt l a (intToOC K π) (fun h => hπ.not_isUnit ((hunit π).2 h))
  have hpoly : ∀ f : Polynomial (Wq l a),
      Per.θ l (ev (f : (Wq l a)⟦X⟧)) = intToOC K (Polynomial.aeval π f) := by
    intro f
    have : ((Per.θ l).comp ev).comp Polynomial.coeToPowerSeries.ringHom =
        (intToOC K).comp (Polynomial.aeval π : Polynomial (Wq l a) →ₐ[Wq l a] ↥(OL K)).toRingHom := by
      refine Polynomial.ringHom_ext (fun c => ?_) ?_
      · change Per.θ l (ev ((Polynomial.C c : Polynomial (Wq l a)) : (Wq l a)⟦X⟧)) =
          intToOC K (Polynomial.aeval π (Polynomial.C c))
        rw [Polynomial.coe_C, hC, Polynomial.aeval_C, halg, hw]
      · change Per.θ l (ev ((Polynomial.X : Polynomial (Wq l a)) : (Wq l a)⟦X⟧)) =
          intToOC K (Polynomial.aeval π (Polynomial.X : Polynomial (Wq l a)))
        rw [Polynomial.coe_X, hX, Polynomial.aeval_X, hfl]
    exact congrArg (fun φ : Polynomial (Wq l a) →+* OC l => φ f) this
  have hE0 : Per.θ l (ev (Ep : (Wq l a)⟦X⟧)) = 0 := by rw [hpoly, hmin.1, map_zero]
  refine ⟨{
    a := a, Ep := Ep, monic := hE.1, deg_pos := hE.2.1, dvd_coeff := hE.2.2.1, coeff_zero := hE.2.2.2
    not_expand := hne, str := str, isUnit_δ := hδ, complete := hc, flat := fl, ev := ev, ev_X := hX
    ev_C := hC, ev_frob := hφ
    span_ev := GlobalTheory.T.span_eq_ker_theta_of_distinguished_ainf l _ hE0 ?_
    θ_ev := fun r x h => ?_
    gal_w := fun g c => gal_wA l a
      (fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 x (hK hx)) c }⟩
  · rw [← (deltaS l a).map_δ_of_map_φ (ainfDelta l) ainf_torsionFree ev hφ]
    exact hδ.map ev
  · obtain ⟨f, rfl⟩ := hmin.2.1 r
    rw [hstr, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h
    obtain ⟨y, hy⟩ := h
    rw [← hpoly, ← sub_eq_zero, ← map_sub, ← map_sub, ← hy, map_mul, map_mul, hE0, mul_zero]

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem disc_coefficients : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ j : bk.DS ρ →+* Disc l (s X) ρ, IsDiscMap (l := _) (u := _) (ρ := _) s j → ∃ cD : ι → (Disc l (s X) ρ →+ bk.DS ρ), (∀ i a, cD i (toDisc l (s X) ρ a) = toDisc l (X : bk.S) ρ (TB.c i a)) ∧ (∀ i x y, cD i (j x * y) = x * cD i y) ∧ (∀ i y, ‖cD i y‖ ≤ ‖y‖) ∧ (∀ y, Filter.Tendsto (fun i => cD i y) Filter.cofinite (nhds 0)) ∧ (∀ y, HasSum (fun i => j (cD i y) * toDisc l (s X) ρ (TB.b i)) y) ∧ (∀ y (r : ℝ), 0 ≤ r → (∀ i, ‖cD i y‖ ≤ r) → ‖y‖ ≤ r) ∧ (∀ z : ι → bk.DS ρ, Filter.Tendsto z Filter.cofinite (nhds 0) → ∃ y, ∀ i, cD i y = z i) ∧ ∀ x, ‖j x‖ = ‖x‖ := by
  intro l _ K bk A _ s ι TB ρ h0 h1 j hj
  obtain ⟨cD, hc1, hc2, hc3⟩ := GlobalTheory.T.exists_topologicalBasis_coeff_disc_extension l K bk A s ι TB ρ h0 h1 j hj
  have hs := GlobalTheory.T.closedDisc_topologicalBasis_expansion l K bk A s ι TB ρ h0 h1 j hj cD ⟨hc1, hc2, hc3⟩
  haveI : IsUltrametricDist (Disc l (s X) ρ) := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).1
  have hb : ∀ (x : bk.DS ρ) (i : ι), ‖j x * toDisc l (s X) ρ (TB.b i)‖ ≤ ‖x‖ := fun x i =>
    (norm_mul_le _ _).trans ((mul_le_mul (hj.norm_le x) (norm_toDisc_le _) (norm_nonneg _)
      (norm_nonneg _)).trans (mul_one _).le)
  have hcont : ∀ i, Continuous (cD i) := fun i =>
    AddMonoidHomClass.continuous_of_bound _ 1 fun y => (hc3 i y).trans (one_mul _).ge
  refine ⟨cD, hc1, hc2, hc3, fun y => (hs y).1, fun y => (hs y).2, ?_, ?_, ?_⟩
  · intro y r hr h
    rw [← (hs y).2.tsum_eq]
    exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr fun i => (hb _ i).trans (h i)
  · intro z hz
    have ht : Filter.Tendsto (fun i => j (z i) * toDisc l (s X) ρ (TB.b i)) Filter.cofinite (nhds 0) :=
      squeeze_zero_norm (fun i => hb (z i) i) (tendsto_zero_iff_norm_tendsto_zero.1 hz)
    have hsum := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ht
    refine ⟨_, fun i => ((hsum.hasSum.map (cD i) (hcont i)).unique ?_)⟩
    classical
    have e : ((cD i) ∘ fun i => j (z i) * toDisc l (s X) ρ (TB.b i)) = fun i' => if i' = i then z i else 0 := by
      funext i'
      simp only [Function.comp]
      rw [hc2, hc1]
      split_ifs with h
      · subst h
        rw [TB.c_self, map_one, mul_one]
      · rw [TB.c_ne _ _ (Ne.symm h), map_zero, mul_zero]
    rw [e]
    exact hasSum_ite_eq i (z i)
  · intro x
    refine le_antisymm (hj.norm_le x) ?_
    have e : cD TB.i₀ (j x * toDisc l (s X) ρ (TB.b TB.i₀)) = x := by
      rw [hc2, hc1, TB.c_self, map_one, mul_one]
    have h := hc3 TB.i₀ (j x * toDisc l (s X) ρ (TB.b TB.i₀))
    rwa [e, TB.b_i₀, map_one, mul_one] at h

end GlobalTheory.BSP
end
