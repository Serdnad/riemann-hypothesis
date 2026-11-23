module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle003
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FinrankRangePowConvex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle208
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle004
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle009
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriUpperLowerFactorization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

section

noncomputable section

open CompanionTheory.Rg.Fl CompanionTheory.D.gk.admitted
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgFl.StarPf

section

variable {A V : Type} [Ring A] [Algebra ℂ A]

def restrictAlg [AddCommGroup V] [Module ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (W : Submodule ℂ V)
    (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) : A →ₐ[ℂ] Module.End ℂ W where
  toFun h := (ρ h).restrict (hW h)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp
  map_zero' := by ext x; simp
  map_add' a b := by ext x; simp
  commutes' c := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one]

theorem restrictAlg_coe [AddCommGroup V] [Module ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (W : Submodule ℂ V)
    (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) (h : A) (x : W) : ((restrictAlg ρ W hW h x : W) : V) = ρ h x := rfl

theorem inf_orthogonal_invariant [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : A →ₐ[ℂ] Module.End ℂ V) (hs : StarClosed ρ) {U W : Submodule ℂ V}
    (hU : ∀ h, ∀ u ∈ U, ρ h u ∈ U) (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) :
    ∀ h, ∀ x ∈ Uᗮ ⊓ W, ρ h x ∈ Uᗮ ⊓ W := by
  intro h x hx
  obtain ⟨hxU, hxW⟩ := Submodule.mem_inf.mp hx
  refine Submodule.mem_inf.mpr ⟨?_, hW h x hxW⟩
  rw [Submodule.mem_orthogonal] at hxU ⊢
  intro u hu
  obtain ⟨h', hh'⟩ := hs h
  rw [← inner_conj_symm, hh' x u, inner_conj_symm]
  exact hxU _ (hU h' u hu)

end

private theorem map_word_one {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (l : List A) : f (word 1 l) = word 1 (l.map f) := by
  induction l with
  | nil =>
    show f 1 = 1
    exact map_one f
  | cons a l ih =>
    show f (1 * a * word 1 l) = 1 * f a * word 1 (l.map f)
    rw [map_mul, map_mul, map_one, ih]

private theorem map_stdPoly_one {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) {M : ℕ} (b : Fin M → A) : f (stdPoly 1 b) = stdPoly 1 (fun i => f (b i)) := by
  unfold stdPoly

  rw [map_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [map_mul, map_intCast, map_word_one, List.map_ofFn]
  rfl

theorem stStar : StStar := by
  unfold StStar
  intro C A _ _ hirr
  suffices key : ∀ n : ℕ, ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V],
      Module.finrank ℂ V = n → ∀ (ρ : A →ₐ[ℂ] Module.End ℂ V), StarClosed ρ →
        ∀ (b : Fin (C ^ 2 + 1) → A), ρ (stdPoly 1 b) = 0 by
    intro V _ _ _ ρ hs b
    exact key _ V rfl ρ hs b
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn ρ hs b
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · have : Subsingleton V := Module.finrank_zero_iff.mp (hn.trans hn0)
    exact LinearMap.ext fun v => Subsingleton.elim _ _
  have : Nontrivial V := Module.finrank_pos_iff.mp (hn ▸ hnpos)
  have hex : ∃ d, ∃ W : Submodule ℂ V, ((∀ h, ∀ w ∈ W, ρ h w ∈ W) ∧ W ≠ ⊥) ∧ Module.finrank ℂ W = d :=
    ⟨_, ⊤, ⟨fun _ _ _ => Submodule.mem_top, bot_ne_top.symm⟩, rfl⟩
  obtain ⟨W, ⟨hWinv, hWne⟩, hWd⟩ := Nat.find_spec hex
  have hmin : ∀ W' : Submodule ℂ V, (∀ h, ∀ w ∈ W', ρ h w ∈ W') → W' ≠ ⊥ →
      Module.finrank ℂ W ≤ Module.finrank ℂ W' := by
    intro W' h1 h2
    rw [hWd]
    exact Nat.find_min' hex ⟨W', ⟨h1, h2⟩, rfl⟩
  have hWirr : ∀ U : Submodule ℂ W, (∀ h, ∀ u ∈ U, restrictAlg ρ W hWinv h u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    by_cases hUb : U = ⊥
    · exact Or.inl hUb
    right
    have hU'inv : ∀ h, ∀ v ∈ U.map W.subtype, ρ h v ∈ U.map W.subtype := by
      intro h v hv
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
      exact Submodule.mem_map.mpr ⟨restrictAlg ρ W hWinv h u, hU h u hu, restrictAlg_coe ρ W hWinv h u⟩
    have hfr : Module.finrank ℂ (U.map W.subtype) = Module.finrank ℂ U := Submodule.finrank_map_subtype_eq W U
    have hU'ne : U.map W.subtype ≠ ⊥ := by
      intro h0
      apply hUb
      apply Submodule.finrank_eq_zero.mp
      rw [← hfr]
      exact Submodule.finrank_eq_zero.mpr h0
    have h1 := hmin _ hU'inv hU'ne
    apply Submodule.eq_top_of_finrank_eq
    exact le_antisymm (Submodule.finrank_le U) (hfr ▸ h1)
  have hdimW : Module.finrank ℂ W ≤ C := hirr W (restrictAlg ρ W hWinv) hWirr
  have hlt : Module.finrank ℂ W ^ 2 < C ^ 2 + 1 := Nat.lt_succ_of_le (Nat.pow_le_pow_left hdimW 2)
  have hPW : ∀ w ∈ W, ρ (stdPoly 1 b) w = 0 := by
    intro w hw
    rw [map_stdPoly_one ρ b]
    exact CompanionTheory.D.gk.admitted.small_irreducible_representation V W W le_rfl 1 (fun w hw => hw) (C ^ 2 + 1) hlt (fun i => ρ (b i))
      (fun i w hw => hWinv (b i) w hw) w hw
  have hperp : ∀ h, ∀ x ∈ Wᗮ, ρ h x ∈ Wᗮ := by
    intro h x hx
    have h1 := inf_orthogonal_invariant ρ hs (U := W) (W := ⊤) hWinv (fun _ _ _ => Submodule.mem_top) h x
      (Submodule.mem_inf.mpr ⟨hx, Submodule.mem_top⟩)
    exact (Submodule.mem_inf.mp h1).1
  have hs2 : StarClosed (restrictAlg ρ Wᗮ hperp) := by
    intro h
    obtain ⟨h', hh'⟩ := hs h
    refine ⟨h', fun u w => ?_⟩
    rw [Submodule.coe_inner, Submodule.coe_inner, restrictAlg_coe, restrictAlg_coe]
    exact hh' u w
  have hWpos : 0 < Module.finrank ℂ W := Nat.pos_of_ne_zero fun h0 => hWne (Submodule.finrank_eq_zero.mp h0)
  have hsum := Submodule.finrank_add_finrank_orthogonal W
  have hltp : Module.finrank ℂ Wᗮ < n := by omega
  have hrest := ih _ hltp Wᗮ rfl (restrictAlg ρ Wᗮ hperp) hs2 b
  have hPperp : ∀ x ∈ Wᗮ, ρ (stdPoly 1 b) x = 0 := by
    intro x hx
    have h0 := congrArg (fun T => ((T ⟨x, hx⟩ : Wᗮ) : V)) hrest
    simpa [restrictAlg_coe] using h0
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ W ⊔ Wᗮ := by
    have htop : W ⊔ Wᗮ = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq W Wᗮ
      have h2 : W ⊓ Wᗮ = ⊥ := disjoint_iff.mp (Submodule.orthogonal_disjoint W)
      rw [h2, Submodule.finrank_eq_zero.mpr rfl] at h1
      omega
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨w, hw, x, hx, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add (f := _), hPW w hw, hPperp x hx, add_zero, LinearMap.zero_apply]

end GlobalTheory.CompanionTheory.RgFl.StarPf
end
end

section

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.Bernstein

theorem arith_nil (N D D' E m K : ℕ) (hN : 0 < N)
    (h1 : D ≤ (2 * N - 1) * D' + E) (h2 : (2 * N - 1 + 1) * E ≤ m ^ 2)
    (h3 : 4 * N ^ 2 * D' ≤ m ^ 2 + K * m) : N * D ≤ m ^ 2 + K * m := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e2 : 2 * (k + 1) - 1 + 1 = 2 * (k + 1) := by omega
  rw [e1] at h1
  rw [e2] at h2
  have h4 : (2 * (k + 1)) * D ≤ (2 * (k + 1)) * ((2 * k + 1) * D') + m ^ 2 := by
    calc (2 * (k + 1)) * D ≤ (2 * (k + 1)) * ((2 * k + 1) * D' + E) :=
          Nat.mul_le_mul_left _ h1
      _ = (2 * (k + 1)) * ((2 * k + 1) * D') + (2 * (k + 1)) * E := by ring
      _ ≤ _ := Nat.add_le_add_left h2 _
  have h5 : (2 * (k + 1)) * ((2 * k + 1) * D') ≤ 4 * (k + 1) ^ 2 * D' := by
    have : (2 * (k + 1)) * ((2 * k + 1) * D') + 2 * (k + 1) * D' = 4 * (k + 1) ^ 2 * D' := by ring
    omega
  have h6 : (2 * (k + 1)) * D ≤ 2 * m ^ 2 + K * m := by omega
  have h7 : 2 * ((k + 1) * D) ≤ 2 * (m ^ 2 + K * m) := by
    have : (2 * (k + 1)) * D = 2 * ((k + 1) * D) := by ring
    omega
  omega

theorem adjoin_shift {V : Type} [AddCommGroup V] [Module ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (μ : ℂ) :
    Algebra.adjoin ℂ (Set.range (Fin.cons (a 0 - algebraMap ℂ _ μ) (fun i : Fin l => a i.succ) :
      Fin (l + 1) → Module.End ℂ V)) = Algebra.adjoin ℂ (Set.range a) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      exact Subalgebra.sub_mem _ (Algebra.subset_adjoin ⟨0, rfl⟩) (Subalgebra.algebraMap_mem _ μ)
    · simp only [Fin.cons_succ]
      exact Algebra.subset_adjoin ⟨j.succ, rfl⟩
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · have h0 : a 0 - algebraMap ℂ _ μ ∈ Algebra.adjoin ℂ (Set.range (Fin.cons (a 0 - algebraMap ℂ _ μ)
          (fun i : Fin l => a i.succ) : Fin (l + 1) → Module.End ℂ V)) :=
        Algebra.subset_adjoin ⟨0, by simp⟩
      have := Subalgebra.add_mem _ h0 (Subalgebra.algebraMap_mem (Algebra.adjoin ℂ (Set.range (Fin.cons (a 0 - algebraMap ℂ _ μ)
          (fun i : Fin l => a i.succ) : Fin (l + 1) → Module.End ℂ V))) μ)
      simpa using this
    · exact Algebra.subset_adjoin ⟨j.succ, by simp⟩

theorem positionOne_invariantIntegral_exchange_step (l N K : ℕ) (hN : 0 < N)
    (hK : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (a : Fin l → Module.End ℂ V), (∀ i j, Commute (a i) (a j)) →
      4 * N ^ 2 * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ V ^ 2 + K * Module.finrank ℂ V) :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (a : Fin (l + 1) → Module.End ℂ V), Module.finrank ℂ V = n → (∀ i j, Commute (a i) (a j)) →
      N * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ V ^ 2 + K * Module.finrank ℂ V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ a hn hc
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) = 0 :=
      Module.finrank_zero_of_subsingleton
    simp [this]
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (a 0)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  set s : Module.End ℂ V := a 0 - algebraMap ℂ _ μ with hs
  have hsc : ∀ i, Commute s (a i) := fun i =>
    (hc 0 i).sub_left (Algebra.commutes μ (a i))
  have hsv : s v = 0 := by
    simp [hs, hv.apply_eq_smul, Module.algebraMap_end_apply]
  obtain ⟨k, hcompl, hk⟩ :=
    ((LinearMap.eventually_isCompl_ker_pow_range_pow s).and (Filter.eventually_ge_atTop 1)).exists
  have hkc : ∀ i, Commute (s ^ k) (a i) := fun i => (hsc i).pow_left k
  have h : ∀ i, ∀ w ∈ LinearMap.ker (s ^ k), a i w ∈ LinearMap.ker (s ^ k) := by
    intro i w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have := congrArg (fun f : Module.End ℂ V => f w) (hkc i).eq
    simp only [Module.End.mul_apply] at this
    rw [this, hw, map_zero]
  have h' : ∀ i, ∀ w ∈ LinearMap.range (s ^ k), a i w ∈ LinearMap.range (s ^ k) := by
    rintro i _ ⟨u, rfl⟩
    refine ⟨a i u, ?_⟩
    have := congrArg (fun f : Module.End ℂ V => f u) (hkc i).eq
    simpa only [Module.End.mul_apply] using this
  by_cases hr : LinearMap.range (s ^ k) = ⊥
  ·
    have hnil : IsNilpotent s := ⟨k, LinearMap.range_eq_bot.mp hr⟩
    set b : Fin (l + 1) → Module.End ℂ V := Fin.cons s (fun i : Fin l => a i.succ) with hb
    have hadj : Algebra.adjoin ℂ (Set.range b) = Algebra.adjoin ℂ (Set.range a) :=
      adjoin_shift a μ
    have hb0 : b 0 = s := rfl
    have hbs : ∀ i : Fin l, b i.succ = a i.succ := fun i => rfl
    have hbc : ∀ i j, Commute (b i) (b j) := by
      intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
      · exact Commute.refl _
      · rw [hb0, hbs]; exact hsc _
      · rw [hb0, hbs]; exact (hsc _).symm
      · rw [hbs, hbs]; exact hc _ _
    have hmem : ∀ c ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range b)), Commute c s := by
      intro c hcm
      have hle : Algebra.adjoin ℂ (Set.range b) ≤ Subalgebra.centralizer ℂ {s} := by
        apply Algebra.adjoin_le
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact hbc 0 i
      have := hle hcm
      rw [Subalgebra.mem_centralizer_iff] at this
      exact (this s rfl).symm
    have h1 := GlobalTheory.CompanionTheory.CommStep.comm_step V l b hbc (2 * N - 1)
    have h2 := GlobalTheory.CompanionTheory.CommNil.succ_mul_finrank_map_le V s hnil (2 * N - 1) _ hmem
    rw [hb0] at h1
    have h3 := hK V (fun i : Fin l => b i.succ) (fun i j => hbc _ _)
    rw [hadj] at h1 h2
    exact arith_nil N _ _ _ _ K hN h1 h2 h3
  ·
    have hker : LinearMap.ker (s ^ k) ≠ ⊥ := by
      intro hbot
      have hmem : v ∈ LinearMap.ker (s ^ k) := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, hsv, map_zero]
      rw [hbot, Submodule.mem_bot] at hmem
      exact hv.2 hmem
    have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
    have p1 : Module.finrank ℂ (LinearMap.ker (s ^ k)) ≠ 0 := fun h0 =>
      hker (Submodule.finrank_eq_zero.mp h0)
    have p2 : Module.finrank ℂ (LinearMap.range (s ^ k)) ≠ 0 := fun h0 =>
      hr (Submodule.finrank_eq_zero.mp h0)
    have hres : ∀ (W : Submodule ℂ V) (g : ∀ i, ∀ w ∈ W, a i w ∈ W) (i j : Fin (l + 1)),
        Commute (((a i).restrict (g i) : Module.End ℂ W)) ((a j).restrict (g j)) := by
      intro W g i j
      show ((a i).restrict (g i) : Module.End ℂ W) * (a j).restrict (g j) =
        ((a j).restrict (g j) : Module.End ℂ W) * (a i).restrict (g i)
      refine LinearMap.ext fun w => Subtype.ext ?_
      have := congrArg (fun f : Module.End ℂ V => f w.1) (hc i j).eq
      simpa [Module.End.mul_apply] using this
    have i1 := ih (Module.finrank ℂ (LinearMap.ker (s ^ k))) (by omega) (LinearMap.ker (s ^ k))
      (fun i => ((a i).restrict (h i) : Module.End ℂ (LinearMap.ker (s ^ k)))) rfl (hres _ h)
    have i2 := ih (Module.finrank ℂ (LinearMap.range (s ^ k))) (by omega) (LinearMap.range (s ^ k))
      (fun i => ((a i).restrict (h' i) : Module.End ℂ (LinearMap.range (s ^ k)))) rfl (hres _ h')
    have h3 := GlobalTheory.CompanionTheory.CommSplit.finrank_adjoin_le_add V (l + 1) a _ _ hcompl h h'
    rw [← hsum]
    calc N * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a))
        ≤ N * (_ + _) := Nat.mul_le_mul_left _ h3
      _ = _ + _ := Nat.mul_add _ _ _
      _ ≤ _ := Nat.add_le_add i1 i2
      _ ≤ _ := by nlinarith [Nat.zero_le (Module.finrank ℂ (LinearMap.ker (s ^ k)) *
            Module.finrank ℂ (LinearMap.range (s ^ k)))]

theorem stComm : StComm := by
  unfold StComm
  intro l
  induction l with
  | zero =>
    intro N
    refine ⟨N, ?_⟩
    intro V _ _ _ a _
    have hr : Set.range a = ∅ := Set.range_eq_empty a
    rw [hr, Algebra.adjoin_empty]
    rcases subsingleton_or_nontrivial V with hV | hV
    · have : Module.finrank ℂ (⊥ : Subalgebra ℂ (Module.End ℂ V)) = 0 :=
        Module.finrank_zero_of_subsingleton
      simp [this]
    · have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
      rw [Subalgebra.finrank_bot]
      nlinarith
  | succ l ih =>
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact ⟨0, fun V _ _ _ a _ => by simp⟩
    obtain ⟨K, hK⟩ := ih (4 * N ^ 2)
    exact ⟨K, fun V _ _ _ a hc => positionOne_invariantIntegral_exchange_step l N K hN hK _ V a rfl hc⟩

end GlobalTheory.CompanionTheory.Bernstein
end

section

noncomputable section

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.RgFl

theorem finrank_sq_le_of_span {A V : Type} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (hρ : Function.Surjective ρ) {d l : ℕ}
    (x y : Fin d → A) (a : Fin l → A)
    (hs : Submodule.span ℂ {z | ∃ i j, ∃ c ∈ Algebra.adjoin ℂ (Set.range a), z = x i * c * y j} = ⊤) :
    Module.finrank ℂ V ^ 2 ≤
      d ^ 2 * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i => ρ (a i))) := by
  classical
  set B := Algebra.adjoin ℂ (Set.range fun i => ρ (a i)) with hB
  have hmap : ∀ c ∈ Algebra.adjoin ℂ (Set.range a), ρ c ∈ B := by
    intro c hc
    have e : B = (Algebra.adjoin ℂ (Set.range a)).map ρ := by
      rw [hB, AlgHom.map_adjoin, ← Set.range_comp]
      rfl
    rw [e]
    exact ⟨c, hc, rfl⟩
  let G : Fin d × Fin d → (B →ₗ[ℂ] Module.End ℂ V) := fun p =>
    (LinearMap.mulLeft ℂ (ρ (x p.1))) ∘ₗ (LinearMap.mulRight ℂ (ρ (y p.2))) ∘ₗ B.val.toLinearMap
  let F : (Fin d × Fin d → B) →ₗ[ℂ] Module.End ℂ V :=
    ∑ p : Fin d × Fin d, G p ∘ₗ LinearMap.proj p
  have hFs : ∀ (p : Fin d × Fin d) (b : B), F (Pi.single p b) = ρ (x p.1) * b * ρ (y p.2) := by
    intro p b
    simp only [F, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single p]
    · simp [G, mul_assoc]
    · intro q _ hq
      simp [Pi.single_eq_of_ne hq]
    · simp
  have hF : LinearMap.range F = ⊤ := by
    rw [eq_top_iff]
    rintro f -
    obtain ⟨g, rfl⟩ := hρ f
    have hg : g ∈ Submodule.span ℂ {z | ∃ i j, ∃ c ∈ Algebra.adjoin ℂ (Set.range a), z = x i * c * y j} := by
      rw [hs]; exact Submodule.mem_top
    induction hg using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, j, c, hc, rfl⟩ := hz
      exact ⟨Pi.single (i, j) ⟨ρ c, hmap c hc⟩, by simp [hFs]⟩
    | zero => simp
    | add u v _ _ hu hv => simpa using Submodule.add_mem _ hu hv
    | smul t u _ hu => simpa using Submodule.smul_mem _ t hu
  have h1 : Module.finrank ℂ (Module.End ℂ V) ≤ Module.finrank ℂ (Fin d × Fin d → B) := by
    have := LinearMap.finrank_range_le F
    rwa [hF, finrank_top] at this
  have h2 : Module.finrank ℂ (Module.End ℂ V) = Module.finrank ℂ V ^ 2 := by
    rw [Module.finrank_linearMap, sq]
  have h3 : Module.finrank ℂ (Fin d × Fin d → B) = d ^ 2 * Module.finrank ℂ B := by
    rw [Module.finrank_pi_fintype]
    simp [sq]
  rw [h2, h3] at h1
  exact h1

theorem stSimple_of_stComm : StComm → StSimple := by
  intro h d l
  obtain ⟨C, hC⟩ := h l (2 * d ^ 2)
  refine ⟨C, fun A _ _ hA V _ _ _ ρ hirr => ?_⟩
  obtain ⟨x, y, a, hcomm, hs⟩ := hA
  rcases subsingleton_or_nontrivial V with hV | hV
  · simp [Module.finrank_zero_of_subsingleton]
  have hsurj := GlobalTheory.CompanionTheory.Burnside.burnside_surj_of_irred ρ hirr
  have h1 := finrank_sq_le_of_span ρ hsurj x y a hs
  have h2 := hC V (fun i => ρ (a i)) (fun i j => (hcomm i j).map ρ)
  have hm : 0 < Module.finrank ℂ V := Module.finrank_pos
  generalize Module.finrank ℂ V = m at *
  generalize Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i => ρ (a i))) = b at *
  have h3 : m * m ≤ C * m := by nlinarith
  exact Nat.le_of_mul_le_mul_right h3 hm

end GlobalTheory.CompanionTheory.RgFl

end
end

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.upper_triangular_inverse_is_upper : ∀ {L V ι : Type} [Field L] [AddCommGroup V] [Module L V] [FiniteDimensional L V] [Fintype ι] (wt : ι → ℕ) (P : ι → Module.End L V), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ a a' : Module.End L V, a * a' = 1 → a' * a = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a' := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv | exact GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv | (intros; apply GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv <;> assumption)
end

section

open CompanionTheory.Rg.FlB

theorem _root_.GlobalTheory.T.iwahori_upper_lower_factorization : ∀ {E ι : Type} [Ring E] [Fintype ι] (wt : ι → ℕ), Function.Injective wt → ∀ (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ J : AddSubgroup E, GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P → ∀ k : E, k - 1 ∈ J → ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a ∧ GlobalTheory.CompanionTheory.Iwahori.IsLowerUni wt P b ∧ k = a * b := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.Gauss.block_gauss | exact GlobalTheory.CompanionTheory.Iwahori.Gauss.block_gauss | (intros; apply GlobalTheory.CompanionTheory.Iwahori.Gauss.block_gauss <;> assumption)
end
