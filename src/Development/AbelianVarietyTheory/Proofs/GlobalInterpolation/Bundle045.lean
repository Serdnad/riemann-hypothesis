module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle007
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle008
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle006
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDirichletLFunctionZeroGapNearOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.SWQ

variable {F : Type} [Field F] {N : ℕ}

namespace HeisenbergBilinear

section Forms

variable {R : Type} [CommRing R] [Algebra F R] (a : Fin N → F)

theorem qd_add (u x : Fin N → R) : qd R a (u + x) = qd R a u + qd R a x + Bd R a u x := by
  simp only [qd, Bd, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_ofNat]
  ring

theorem Bd_add_left (u u' x : Fin N → R) : Bd R a (u + u') x = Bd R a u x + Bd R a u' x := by
  simp only [Bd, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_add_right (u x x' : Fin N → R) : Bd R a u (x + x') = Bd R a u x + Bd R a u x' := by
  simp only [Bd, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_smul_left (t : R) (u x : Fin N → R) : Bd R a (t • u) x = t * Bd R a u x := by
  simp only [Bd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_smul_right (t : R) (u x : Fin N → R) : Bd R a u (t • x) = t * Bd R a u x := by
  simp only [Bd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_neg_left (u x : Fin N → R) : Bd R a (-u) x = -Bd R a u x := by
  simp only [Bd, Pi.neg_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_comm (u x : Fin N → R) : Bd R a u x = Bd R a x u := by
  simp only [Bd]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem Bd_self (x : Fin N → R) : Bd R a x x = 2 * qd R a x := by
  simp only [Bd, qd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_ofNat]
  ring

end Forms

variable [NumberField F]

theorem half_mul_two_AF : algebraMap F (AF F) (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, one_div, inv_mul_cancel₀ two_ne_zero, map_one]

theorem qd_rat (a : Fin N → F) (ξ : Fin N → F) : qd (AF F) a (rat ξ) = algebraMap F (AF F) (qd F a ξ) := by

  simp only [qd, rat, map_sum, map_mul, map_pow]
  rfl

end HeisenbergBilinear

open HeisenbergBilinear in
theorem weil_intertwine : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ)
    (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a →
    ∀ Φ : (Fin N → AF F) → ℂ,
      (∀ b x y, rho ψ a x y (Ub ψ a b Φ) = Ub ψ a b (rho ψ a x (y + b • x) Φ)) ∧
      (∀ (t t' : AF F) x y, t * t' = 1 → rho ψ a x y (Da t Φ) = Da t (rho ψ a (t • x) (t' • y) Φ)) ∧
      (∀ x y, rho ψ a x y (Fo ψ ν a Φ) = Fo ψ ν a (rho ψ a (-y) x Φ)) ∧
      (∀ b : F, th (Ub ψ a (algebraMap F (AF F) b) Φ) = th Φ) ∧
      ∀ t : F, t ≠ 0 → th (Da (algebraMap F (AF F) t) Φ) = th Φ := by
  intro F _ _ N ψ lam ν a hC Φ
  obtain ⟨-, ⟨-, -, hchar, -⟩, -, ⟨hHaar, -⟩, -⟩ := hC
  have hh : algebraMap F (AF F) (1 / 2) * 2 = 1 := half_mul_two_AF
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro b x y
    funext u
    simp only [rho, Ub]
    have key : ψ (Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y) *
          ψ (b * qd (AF F) a (u + x)) =
        ψ (b * qd (AF F) a u) *
          ψ (Bd (AF F) a u (y + b • x) + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x (y + b • x)) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      simp only [qd_add, Bd_add_right, Bd_smul_right, Bd_self]
      linear_combination (-(b * qd (AF F) a x)) * hh
    linear_combination (Φ (u + x)) * key
  ·
    intro t t' x y htt
    funext u
    simp only [rho, Da]
    have key : Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y =
        Bd (AF F) a (t • u) (t' • y) + algebraMap F (AF F) (1 / 2) * Bd (AF F) a (t • x) (t' • y) := by
      simp only [Bd_smul_left, Bd_smul_right]
      linear_combination (-(Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y)) * htt
    rw [key, smul_add]
  ·
    intro x y
    funext u
    have : ν.IsAddHaarMeasure := hHaar
    have : (muV N ν).IsAddRightInvariant := by unfold muV; infer_instance
    simp only [rho, Fo]
    refine Eq.trans ?_ (integral_add_right_eq_self (μ := muV N ν)
      (fun s => ψ (Bd (AF F) a s x + algebraMap F (AF F) (1 / 2) * Bd (AF F) a (-y) x) * Φ (s + -y) *
        ψ (Bd (AF F) a s u)) y)
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    dsimp only
    rw [add_neg_cancel_right]
    have key : ψ (Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y) *
          ψ (Bd (AF F) a s (u + x)) =
        ψ (Bd (AF F) a (s + y) x + algebraMap F (AF F) (1 / 2) * Bd (AF F) a (-y) x) *
          ψ (Bd (AF F) a (s + y) u) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      have e1 := Bd_comm a u y
      have e2 := Bd_comm a x y
      simp only [Bd_add_left, Bd_add_right, Bd_neg_left]
      linear_combination e1 + algebraMap F (AF F) (1 / 2) * e2 + Bd (AF F) a y x * hh
    linear_combination (Φ s) * key
  ·
    intro b
    simp only [th, Ub]
    refine tsum_congr fun ξ => ?_
    rw [qd_rat, ← map_mul, hchar, one_mul]
  ·
    intro t ht
    simp only [th, Da]
    have e : ∀ ξ : Fin N → F, algebraMap F (AF F) t • rat ξ = rat (t • ξ) := by
      intro ξ
      funext l
      simp only [rat, Pi.smul_apply, smul_eq_mul, map_mul]
    simp only [e]
    exact Equiv.tsum_eq
      { toFun := fun ξ : Fin N → F => t • ξ
        invFun := fun ξ => t⁻¹ • ξ
        left_inv := fun ξ => by simp only [smul_smul, inv_mul_cancel₀ ht, one_smul]
        right_inv := fun ξ => by simp only [smul_smul, mul_inv_cancel₀ ht, one_smul] }
      (fun ξ => Φ (rat ξ))

end GlobalTheory.SWQ
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.RatLattice

variable {F : Type} [Field F] [NumberField F]

theorem closure_range_rat (N : ℕ) :
    AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) =
      AddSubgroup.pi Set.univ fun _ : Fin N => (algebraMap F (AF F)).range.toAddSubgroup := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨ξ, rfl⟩ l _
    exact ⟨ξ l, rfl⟩
  · intro u hu
    choose ξ hξ using fun l => hu l trivial
    have : u = rat ξ := funext fun l => (hξ l).symm
    rw [this]
    exact AddSubgroup.subset_closure ⟨ξ, rfl⟩

theorem mem_closure_iff (N : ℕ) (u : Fin N → AF F) :
    u ∈ AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) ↔ ∃ ξ, u = rat ξ := by
  rw [closure_range_rat]
  constructor
  · intro hu
    choose ξ hξ using fun l => hu l trivial
    exact ⟨ξ, funext fun l => (hξ l).symm⟩
  · rintro ⟨ξ, rfl⟩ l _
    exact ⟨ξ l, rfl⟩

theorem rat_injective (N : ℕ) : Function.Injective (rat : (Fin N → F) → (Fin N → AF F)) := by
  haveI : Nontrivial (AF F) := by
    show Nontrivial (AdeleRing (𝓞 F) F)
    unfold AdeleRing
    infer_instance
  intro ξ η h
  funext l
  exact (algebraMap F (AF F)).injective (congrFun h l)

theorem isFD_pi {Y : Type} [AddCommGroup Y] [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]
    {A : AddSubgroup Y} {D : Set Y} (hF : IsAddFundamentalDomain A D ν) (n : ℕ) :
    IsAddFundamentalDomain (AddSubgroup.pi Set.univ fun _ : Fin n => A) (Set.univ.pi fun _ : Fin n => D)
      (Measure.pi fun _ : Fin n => ν) := by
  have hq (i : Fin n) := Measure.quasiMeasurePreserving_eval (fun _ : Fin n => ν) i
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.univ_pi_eq_iInter]
    exact NullMeasurableSet.iInter fun i => hF.nullMeasurableSet.preimage (hq i)
  · have := (ae_all_iff (μ := (Measure.pi fun _ : Fin n => ν))).2 fun i => (hq i).ae hF.ae_covers
    filter_upwards [this] with z hz
    choose a ha using hz
    exact ⟨⟨fun i => a i, fun i _ => (a i).2⟩, fun i _ => ha i⟩
  · intro a b hab
    obtain ⟨i, hi⟩ : ∃ i, a.1 i ≠ b.1 i := by
      by_contra! h
      exact hab (Subtype.ext (funext h))
    have h := hF.aedisjoint (i := ⟨a.1 i, a.2 i trivial⟩) (j := ⟨b.1 i, b.2 i trivial⟩)
      fun e => hi (congrArg Subtype.val e)
    refine measure_mono_null ?_ ((hq i).preimage_null h)
    rintro z ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩
    exact ⟨⟨u i, hu i trivial, congrFun hu' i⟩, ⟨v i, hv i trivial, congrFun hv' i⟩⟩

end GlobalTheory.SWQ.RatLattice

open GlobalTheory.SWQ.RatLattice in
theorem GlobalTheory.SWQ.rat_lattice_fundamentalDomain : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ν : Measure (AF F)), IsCov1 ν → (muV N ν).IsAddHaarMeasure ∧ (∀ u : (Fin N → AF F), u ∈ (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) ↔ ∃ ξ, u = rat ξ) ∧ Function.Injective (rat : (Fin N → F) → (Fin N → AF F)) ∧ (∃ K : Set (Fin N → AF F), IsCompact K ∧ ∀ u, ∃ ξ, u - rat ξ ∈ K) ∧ ∃ D : Set (Fin N → AF F), MeasurableSet D ∧ IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) ∧ muV N ν D = 1 := by
  intro F _ _ N ν hν
  obtain ⟨hH, D₀, hD₀m, hD₀, hD₀1⟩ := hν
  haveI := hH
  refine ⟨?_, mem_closure_iff N, rat_injective N, ?_, ?_⟩
  · unfold muV
    infer_instance
  · obtain ⟨K, hK, hKc⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
    refine ⟨Set.univ.pi fun _ => K, isCompact_univ_pi fun _ => hK, fun u => ?_⟩
    choose ξ hξ using fun l => hKc (u l)
    exact ⟨ξ, fun l _ => hξ l⟩
  · refine ⟨Set.univ.pi fun _ => D₀, MeasurableSet.univ_pi fun _ => hD₀m, ?_, ?_⟩
    · rw [closure_range_rat]
      exact isFD_pi ν hD₀ N
    · unfold muV
      rw [Measure.pi_pi]
      simp [hD₀1]
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem rowDeg_dominated_of_mem_dualWeyl (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ) :
    ∀ f ∈ dualWeyl k N N ν, ∀ m ∈ f.support,
      (∀ j : ℕ, (∑ a : Fin N with a.val < j, rowDeg m a) ≤ ∑ a : Fin N with a.val < j, ν a) ∧
      ∑ a, rowDeg m a = ∑ a, ν a := by
  classical
  intro f hf
  rw [standardMonomialSpanDomain k N N ν] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := bidetDominance k N N K sz hsz I m hm
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

end GlobalTheory.Alc
end

section

open Formalism.L2.Col NumberField IsDedekindDomain

namespace GlobalTheory

theorem colRoots_mem_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A}
    {P : HeightOneSpectrum A} (h : P ∈ divs a) : a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hfin
  · exact (Set.Finite.mem_toFinset hfin).mp h
  · exact absurd h (Finset.notMem_empty P)

theorem colRoots_exists_primitiveRoots (X : Fields) (Pr : Primes X) (m : ℕ) (Ch : Chars X Pr m)
    (hf : 0 < X.f) (hP : Pr.Ok) (hC : Ch.Ok) (i : Fin 2) :
    (∃ ζ : X.K, IsPrimitiveRoot ζ (Pr.g i)) ∧ ∃ ζ : X.K, IsPrimitiveRoot ζ (Pr.g i - 1) := by
  refine ⟨?_, ?_⟩
  · have hcard : 0 < (Pr.vG i).card := by rw [hP.vG_card i]; exact hf
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hcard
    have hwG : w ∈ Pr.vGs := by
      classical
      rw [Primes.vGs, Finset.mem_union]
      fin_cases i
      · exact Or.inl hw
      · exact Or.inr hw
    have hconj : X.conjO (Pr.piG i) ∈ w.asIdeal := colRoots_mem_of_mem_divs hw
    have hg : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal := by
      rw [← hP.piG_norm i]
      exact w.asIdeal.mul_mem_left _ hconj
    have hzero : ((Pr.g i : ℕ) : 𝓞 X.E ⧸ w.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk w.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hg
    exact exists_isPrimitiveRoot_of_addChar_ne_one (𝓞 X.E ⧸ w.asIdeal) X.K (Pr.g i)
      (hP.g_prime i) hzero (Ch.psi0 ⟨w, hwG⟩) (hC.psi_zero_nontrivial_character _)
  · obtain ⟨om, hom, -⟩ := hC.chi_om i
    exact exists_isPrimitiveRoot_of_injective_character X.K (Pr.g i) (hP.g_prime i) om hom

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem lamJ_mem_range_and_pow_eq_one :
    ∀ (k K : Type) [Field k] [Field K] (s : K →+* ℂ) (p : ℕ), p.Prime → Nat.card k = p →
      (∃ ζ : K, IsPrimitiveRoot ζ p) → (∃ ζ : K, IsPrimitiveRoot ζ (p - 1)) →
      ∀ (n : ℕ) (ψ : AddChar k ℂ) (χ : ℕ → MulChar k ℂ) (a t nb skip : ℕ)
        (M : Matrix (Fin n) (Fin n) k),
        (∃ r : K, s r = lamJ ψ χ a t nb skip M) ∧
          (lamJ ψ χ a t nb skip M ≠ 0 → lamJ ψ χ a t nb skip M ^ (p * (p - 1)) = 1) := by
  intro k K _ _ s p hp hk ⟨ζ, hζ⟩ ⟨ξ, hξ⟩ n ψ χ a t nb skip M
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact hp.ne_zero)
  letI : Fintype k := Fintype.ofFinite k
  have hk' : Fintype.card k = p := by rw [← Nat.card_eq_fintype_card]; exact hk
  have hψ : ∀ x : k, ψ x ^ p = 1 := by
    intro x
    rw [← AddChar.map_nsmul_eq_pow, ← hk, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  have hχ : ∀ (i : ℕ) (x : k), χ i x ≠ 0 → χ i x ^ (p - 1) = 1 := by
    intro i x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (MulChar.map_zero _)
    rw [← map_pow, ← hk', FiniteField.pow_card_sub_one_eq_one x hx0, map_one]
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hψr : ∀ x : k, ψ x ∈ s.range := fun x =>
    complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s p ζ hp.pos hζ _ (hψ x)
  have hχr : ∀ (i : ℕ) (x : k), χ i x ∈ s.range := by
    intro i x
    by_cases hx : χ i x = 0
    · rw [hx]; exact zero_mem _
    · exact complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s (p - 1) ξ hp1 hξ _ (hχ i x hx)
  unfold lamJ
  refine ⟨?_, ?_⟩
  · exact mul_mem (hψr _) (prod_mem fun i _ => hχr i _)
  · intro h
    have h2 := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h)
    rw [mul_pow, pow_mul, hψ, one_pow, one_mul, mul_comm p, pow_mul, ← Finset.prod_pow,
      Finset.prod_eq_one (fun i hi => hχ i _ (h2 i hi)), one_pow]

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem lamJ_zero_blocks_mem_range_and_pow_eq_one :
    ∀ (k K : Type) [Field k] [Field K] (s : K →+* ℂ) (p : ℕ), p.Prime → (p : k) = 0 → (∃ ζ : K, IsPrimitiveRoot ζ p) → ∀ (n : ℕ) (ψ : AddChar k ℂ) (χ : ℕ → MulChar k ℂ) (a t skip : ℕ) (M : Matrix (Fin n) (Fin n) k), (∃ r : K, s r = lamJ ψ χ a t 0 skip M) ∧ lamJ ψ χ a t 0 skip M ^ p = 1 := by
  intro k K _ _ s p hp hk ⟨ζ, hζ⟩ n ψ χ a t skip M
  have hψ : ∀ x : k, ψ x ^ p = 1 := fun x => by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hk, zero_mul, AddChar.map_zero_eq_one]
  have h : lamJ ψ χ a t 0 skip M ^ p = 1 := by
    unfold Formalism.L2.Forms.lamJ
    simp [hψ]
  exact ⟨complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s p ζ hp.pos hζ _ h, h⟩

end GlobalTheory
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.exists_dirichletLFunction_zero_gap_near_one : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ), (χ ≠ 1 ∨ ρ ≠ 1) → LFunction χ ρ = 0 → |ρ.im| ≤ 1 → c / ((q : ℝ) ^ 2 * Real.log (3 * q)) ≤ 1 - ρ.re := by
  first | exact @GlobalTheory.ZeroGapNearOne.exists_gap | exact GlobalTheory.ZeroGapNearOne.exists_gap | (intros; apply GlobalTheory.ZeroGapNearOne.exists_gap <;> assumption)
end
