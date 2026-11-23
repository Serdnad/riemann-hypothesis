module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle183
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle184
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle192
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.multiplicative_virtual_character : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (f : WD h → ℂˣ), (∀ x y, f (x.lpSum y) = f x * f y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → f x = f y) → ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (a : ∀ i, WDRep h (Fin (d i) → ℂ)) (c : ι → ℤ), (∀ σ, ∑ i, (c i : ℂ) * LinearMap.trace ℂ (Fin (d i) → ℂ) ((a i).ρ σ) = 0) → ∏ i, f (WD.mk (a i)) ^ c i = 1 := by
  first | exact @GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero | exact GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero | (intros; apply GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_wdRep_pull_finite_twist :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (G : Type)
      [Group G] [Finite G] (π : Weil h →* G),
      IsOpen {σ : Ine (F := E) A | π (ineIncl h σ) = 1} → ∀ (n : ℕ)
      (R : Representation ℂ G (Fin n → ℂ)) (μ : Weil h →* ℂˣ), IsSmooth μ →
      ∃ b : WDRep h (Fin n → ℂ), ∀ σ, b.ρ σ = (μ σ : ℂ) • R (π σ) := by
  intro E Ω _ _ _ _ _ A w h G _ _ π hπ n R μ hμ
  have hsm : IsSmooth (R.comp π) :=
    IsSmooth.of_le (f := π) hπ fun σ hσ => by simp [hσ]
  have hss : ∀ σ, Module.End.IsSemisimple ((R.comp π) σ) := by
    intro σ
    have hu : IsUnit ((R.comp π) σ) := ((R.comp π).toHomUnits σ).isUnit
    refine FrobSemisimple.isSemisimple_of_pow hu (m := Nat.card G) Nat.card_pos ?_
    rw [← map_pow, MonoidHom.comp_apply, map_pow, pow_card_eq_one', map_one]
    exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := Polynomial.X - Polynomial.C 1)
      (Polynomial.irreducible_X_sub_C 1).squarefree (by simp)
  let b0 : WDRep h (Fin n → ℂ) :=
    { ρ := R.comp π
      N := 0
      smooth := hsm
      semisimple := hss
      nilpotent := IsNilpotent.zero
      comm := fun σ => by simp }
  exact ⟨b0.twist μ hμ, fun σ => rfl⟩

end GlobalTheory.WeilDeligne
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module

namespace GlobalTheory.WeilDeligne

section Reduction

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def WDRep.resZero {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (U : Submodule ℂ V) (hU : ∀ σ, ∀ v ∈ U, a.ρ σ v ∈ U) : WDRep h U where
  ρ := { toFun := fun σ => (a.ρ σ).restrict (hU σ)
         map_one' := by ext; simp
         map_mul' := fun σ τ => by ext; simp }
  N := 0
  smooth := a.smooth.of_le fun σ hσ => by ext; simp [hσ]
  semisimple σ := End.IsSemisimple.restrict (hU σ) (a.semisimple σ)
  nilpotent := IsNilpotent.zero
  comm σ := by simp

theorem WDRep.charpoly_eq_mul_of_isCompl {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (a : WDRep h V) (U U' : Submodule ℂ V)
    (hU : ∀ σ, ∀ v ∈ U, a.ρ σ v ∈ U) (hU' : ∀ σ, ∀ v ∈ U', a.ρ σ v ∈ U') (hc : IsCompl U U')
    (σ : Weil h) :
    (a.ρ σ).charpoly = ((a.resZero U hU).ρ σ).charpoly * ((a.resZero U' hU').ρ σ).charpoly := by
  rw [← LinearMap.charpoly_prodMap, ← LinearEquiv.charpoly_conj (Submodule.prodEquivOfIsCompl U U' hc)]
  congr 1
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := (Submodule.prodEquivOfIsCompl U U' hc).surjective v
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simp [Submodule.coe_prodEquivOfIsCompl', WDRep.resZero]

theorem finite_range_of_frob_pow_eq_one {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ) {m : ℕ} (hm : 0 < m)
    (h1 : ρ (frob (h := h)) ^ m = 1) : (Set.range ρ).Finite := by
  refine (Set.Finite.image2 (· * ·) (Set.finite_range fun j : Fin m => ρ (frob (h := h)) ^ (j : ℕ))
    hρ.finite_range).subset ?_
  rintro _ ⟨σ, rfl⟩
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (h := h) deg_frob σ
  have hker : frob (h := h) ^ m ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_pow, h1]
  set k := deg σ
  have hk : frob (h := h) ^ k = frob (h := h) ^ ((k % m).toNat) * (frob (h := h) ^ m) ^ (k / m) := by
    rw [← zpow_natCast (frob (h := h)) m, ← zpow_mul, ← zpow_natCast (frob (h := h)) ((k % m).toNat),
      ← zpow_add, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne')),
      add_comm, Int.mul_ediv_add_emod]
  have hlt : (k % m).toNat < m := by
    have := Int.emod_lt_of_pos k (by exact_mod_cast hm : (0 : ℤ) < m)
    omega
  refine ⟨ρ (frob (h := h)) ^ ((k % m).toNat), ⟨⟨_, hlt⟩, rfl⟩, ρ (ineIncl h τ), ⟨τ, rfl⟩, ?_⟩
  have h2 : ρ ((frob (h := h) ^ m) ^ (k / m)) = 1 := (ρ.ker.zpow_mem hker _)
  show _ = ρ σ
  rw [hτ, hk, map_mul, map_mul, h2, mul_one, map_pow]

theorem exists_of_lpSum_twist_finite (S : WD h → Prop)
    (hsum : ∀ x y, S x → S y → S (x.lpSum y))
    (hfin : ∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ),
      (Set.range a.ρ).Finite → S (WD.mk (a.twist μ hμ))) :
    ∀ (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
      finrank ℂ V = d → ∀ (ρ : Representation ℂ (Weil h) V), IsSmooth ρ →
      (∀ σ, End.IsSemisimple (ρ σ)) → ∃ y : WD h, S y ∧ ∀ σ, y.charPol σ = (ρ σ).charpoly := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V _ _ _ hd ρ hρ hs
  let a0 : WDRep h V := ⟨ρ, 0, hρ, hs, IsNilpotent.zero, by simp⟩
  obtain ⟨m, hm, hcomm⟩ := exists_pow_frob_commute ρ hρ
  have hsm : ρ (frob (h := h)) ^ m = ρ (frob (h := h) ^ m) := (map_pow _ _ _).symm
  by_cases hsc : ∃ c : ℂ, c ≠ 0 ∧ ρ (frob (h := h)) ^ m = c • (1 : Module.End ℂ V)
  · obtain ⟨c, hc0, hsc⟩ := hsc
    obtain ⟨c', hc'⟩ := IsAlgClosed.exists_pow_nat_eq c hm
    have hc'0 : c' ≠ 0 := by rintro rfl; exact hc0 (by rw [← hc', zero_pow hm.ne'])
    set u : ℂˣ := Units.mk0 c' hc'0
    let b : WDRep h V := a0.twist (unrChar h u⁻¹) (isSmooth_unrChar h _)
    have hb1 : b.ρ (frob (h := h)) ^ m = 1 := by
      show ((((unrChar h u⁻¹) (frob (h := h)) : ℂˣ) : ℂ) • ρ (frob (h := h))) ^ m = 1
      rw [_root_.smul_pow, hsc, smul_smul, unrChar_apply, deg_frob, zpow_one, ← Units.val_pow_eq_pow_val,
        inv_pow]
      have : u ^ m = Units.mk0 c hc0 := Units.ext (by simp [u, hc'])
      rw [this]
      simp [hc0]
    have hfinb := finite_range_of_frob_pow_eq_one b.ρ b.smooth hm hb1
    have hfins : (Set.range (WD.std b).2.ρ).Finite :=
      (hfinb.image ((finBasis ℂ V).equivFun.conjAlgEquiv ℂ)).subset (by rintro _ ⟨σ, rfl⟩; exact ⟨_, ⟨σ, rfl⟩, rfl⟩)
    refine ⟨WD.mk ((WD.std b).2.twist (unrChar h u) (isSmooth_unrChar h _)),
      hfin _ _ _ _ hfins, fun σ => ?_⟩
    rw [← WD.sound ((WD.iso_std b).twist _ _), WD.charPol_mk]
    show ((((unrChar h u) σ : ℂˣ) : ℂ) • ((((unrChar h u⁻¹) σ : ℂˣ) : ℂ) • ρ σ)).charpoly = _
    rw [smul_smul, ← Units.val_mul, unrChar_apply, unrChar_apply, ← mul_zpow, mul_inv_cancel,
      one_zpow, Units.val_one, one_smul]
  · have hnt : Nontrivial V := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      exact hsc ⟨1, one_ne_zero, LinearMap.ext fun v => Subsingleton.elim _ _⟩
    set s := ρ (frob (h := h)) ^ m with hs_def
    have hss : End.IsSemisimple s := by rw [hsm]; exact hs _
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue s
    have hinv : ∀ σ α, ∀ v ∈ End.eigenspace s α, ρ σ v ∈ End.eigenspace s α := by
      intro σ α v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [← Module.End.mul_apply, (hcomm σ).eq, Module.End.mul_apply, hv, map_smul]
    set U := End.eigenspace s c
    set U' := ⨆ α ∈ ({c}ᶜ : Set ℂ), End.eigenspace s α
    have hU : ∀ σ, ∀ v ∈ U, ρ σ v ∈ U := fun σ => hinv σ c
    have hU' : ∀ σ, ∀ v ∈ U', ρ σ v ∈ U' := by
      intro σ v hv
      have : U' ≤ U'.comap (ρ σ) := iSup₂_le fun α hα w hw =>
        (le_iSup₂_of_le α hα le_rfl : End.eigenspace s α ≤ U') (hinv σ α w hw)
      exact this hv
    have hcompl : IsCompl U U' := by
      refine ⟨(Module.End.eigenspaces_iSupIndep s).disjoint_biSup (by simp), ?_⟩
      rw [codisjoint_iff, eq_top_iff, ← hss.iSup_eigenspace_eq_top]
      refine iSup_le fun α => ?_
      by_cases hα : α = c
      · subst hα; exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le α hα le_rfl)
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨v, hv, hv0⟩ := hc.exists_hasEigenvector
      apply hv0
      have h1 := Module.End.mem_eigenspace_iff.mp hv
      rw [zero_smul] at h1
      have h1' : ρ (frob (h := h) ^ m) v = 0 := by rw [← hsm]; exact h1
      have := congrArg (ρ (frob (h := h) ^ m)⁻¹) h1'
      rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
        map_zero] at this
    have hUb : U ≠ ⊥ := hc
    have hU'b : U' ≠ ⊥ := by
      intro hb
      apply hsc
      refine ⟨c, hc0, LinearMap.ext fun v => ?_⟩
      have hv : v ∈ U := by
        have := hcompl.sup_eq_top
        rw [hb, sup_bot_eq] at this
        rw [this]; trivial
      rw [Module.End.mem_eigenspace_iff.mp hv]
      simp
    have hrk := Submodule.finrank_add_eq_of_isCompl hcompl
    have h1 : 0 < finrank ℂ U := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hUb)
    have h2 : 0 < finrank ℂ U' :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hU'b)
    obtain ⟨y1, hS1, hy1⟩ := ih (finrank ℂ U) (by omega) U rfl (a0.resZero U hU).ρ
      (a0.resZero U hU).smooth (a0.resZero U hU).semisimple
    obtain ⟨y2, hS2, hy2⟩ := ih (finrank ℂ U') (by omega) U' rfl (a0.resZero U' hU').ρ
      (a0.resZero U' hU').smooth (a0.resZero U' hU').semisimple
    refine ⟨y1.lpSum y2, hsum _ _ hS1 hS2, fun σ => ?_⟩
    rw [WD.charPol_lpSum, hy1, hy2]
    exact (a0.charpoly_eq_mul_of_isCompl U U' hU hU' hcompl σ).symm

end Reduction

theorem WD.induction_lpSum_twist_finite : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (S : WD h → Prop), (∀ x y, S x → S y → S (x.lpSum y)) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → S x → S y) → (∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ), (Set.range a.ρ).Finite → S (WD.mk (a.twist μ hμ))) → ∀ x, S x := by
  intro E Ω _ _ _ _ _ A w h S hsum hchar hfin x
  induction x using WD.ind with
  | hP n a =>
  obtain ⟨y, hy, hyc⟩ := exists_of_lpSum_twist_finite S hsum hfin _ (Fin n → ℂ) rfl a.ρ a.smooth
    a.semisimple
  exact hchar y _ (fun σ => by rw [hyc, WD.charPol_mk]) hy

end GlobalTheory.WeilDeligne
end
end

section

open GlobalTheory.BI GlobalTheory.BrauerZero

namespace GlobalTheory.BrauerZero

theorem ind_ind_of_le {G : Type} [Group G] [Finite G] (K A : Subgroup G) (hKA : K ≤ A)
    (ψ : K → ℂ) :
    ind A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) = ind K ψ := by
  classical
  haveI := Fintype.ofFinite G
  funext g
  have hcard : Nat.card (K.subgroupOf A) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv
  have key : ∀ a y : A, ext0 (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩) (y⁻¹ * a * y)
      = ext0 K ψ ((y : G)⁻¹ * (a : G) * y) := by
    intro a y
    have hc : ((y⁻¹ * a * y : A) : G) = (y : G)⁻¹ * (a : G) * y := by simp
    by_cases h : (y : G)⁻¹ * (a : G) * y ∈ K
    · have h' : y⁻¹ * a * y ∈ K.subgroupOf A := by rw [Subgroup.mem_subgroupOf, hc]; exact h
      rw [ext0, ext0, dite_eq_left h', dite_eq_left h]
      congr 1
    · have h' : y⁻¹ * a * y ∉ K.subgroupOf A := by rw [Subgroup.mem_subgroupOf, hc]; exact h
      rw [ext0, ext0, dite_eq_right h', dite_eq_right h]
  have step : ∀ x : G, ext0 A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) (x⁻¹ * g * x)
      = (Nat.card K : ℂ)⁻¹ * ∑ y : A, ext0 K ψ ((x * y)⁻¹ * g * (x * y)) := by
    intro x
    by_cases hx : x⁻¹ * g * x ∈ A
    · rw [ext0, dite_eq_left hx, ind, hcard, finsum_eq_sum_of_fintype]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [key ⟨_, hx⟩ y]
      congr 1
      simp only [mul_inv_rev]
      group
    · rw [ext0, dite_eq_right hx]
      symm
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y _ => ?_)
      have hn : (x * y)⁻¹ * g * (x * y) ∉ K := by
        intro hk
        apply hx
        have hA : (x * y)⁻¹ * g * (x * y) ∈ A := hKA hk
        have e : x⁻¹ * g * x = (y : G) * ((x * y)⁻¹ * g * (x * y)) * (y : G)⁻¹ := by group
        rw [e]
        exact A.mul_mem (A.mul_mem y.2 hA) (A.inv_mem y.2)
      rw [ext0, dite_eq_right hn]
  rw [ind, ind, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl (fun x _ => step x), ← Finset.mul_sum, Finset.sum_comm]
  have shift : ∀ y : A, ∑ x : G, ext0 K ψ ((x * y)⁻¹ * g * (x * y)) = ∑ z : G, ext0 K ψ (z⁻¹ * g * z) :=
    fun y => Fintype.sum_equiv (Equiv.mulRight (y : G)) _ _ (fun x => rfl)
  rw [Finset.sum_congr rfl (fun y _ => shift y), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  have hA0 : (Nat.card A : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := A)).ne'
  field_simp

end GlobalTheory.BrauerZero
end

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem linApprox_of_polyApprox_trc : ∀ (k Γ : Type) [NormedField k] [IsUltrametricDist k] [Group Γ] (a : ℕ)
    (r : Γ →* GL (Fin a) k) (C : Set (Γ →* GL (Fin a) k)), PolyApprox (trc r) (trc '' C) → LinApprox r C := by
  intro k Γ _ _ _ a r C h ε hε
  classical
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  let f : (Γ → k) → (Γ →* GL (Fin a) k) := Function.invFunOn trc C
  have hf : ∀ η ∈ s, f η ∈ C ∧ trc (f η) = η := fun η hη =>
    ⟨Function.invFunOn_mem (hs hη), Function.invFunOn_eq (hs hη)⟩
  have hinj : Set.InjOn f (s : Set (Γ → k)) := fun x hx y hy hxy => by
    rw [← (hf x hx).2, ← (hf y hy).2, hxy]
  refine ⟨s.image f, fun ρ => c (trc ρ), ?_, fun g => ?_⟩
  · intro ρ hρ
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hρ)
    exact (hf η hη).1
  · have := hP (MvPolynomial.X g)
    simp only [MvPolynomial.aeval_X] at this
    rw [Finset.sum_image hinj]
    have e : ∑ x ∈ s, c (trc (f x)) * trc (f x) g = ∑ η ∈ s, c η * η g :=
      Finset.sum_congr rfl fun η hη => by rw [(hf η hη).2]
    rw [e]
    exact this

end GlobalTheory.Cong
end

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory

theorem polyApprox_trc_locally_cauchy : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ) (θ : J → PadicAlgCl l) (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) → PolyApprox θ ((fun ρ j => trc ρ (x j)) '' C) → ∀ ε : ℝ, 0 < ε → ∀ g : Γ, ∃ V ∈ nhds g, ∀ i j, x i ∈ V → x j ∈ V → ‖θ i - θ j‖ ≤ ε := by
  intro l _ Γ _ _ _ _ a J x θ C hC hA ε hε g
  obtain ⟨s, c, hs, hP⟩ := hA (ε / 2) (by linarith)
  have hmem : ∀ η ∈ s, ∃ ρ ∈ C, (fun j => trc ρ (x j)) = η := fun η hη => hs hη
  choose! R hRC hRη using hmem
  set F : Γ → PadicAlgCl l := fun h => ∑ η ∈ s, c η * trc (R η) h with hF
  have hFc : Continuous F := by
    refine continuous_finsetSum _ fun η hη => continuous_const.mul ?_
    exact (Units.continuous_val.comp (hC _ (hRC η hη))).matrix_trace
  refine ⟨F ⁻¹' Metric.ball (F g) (ε / 4), hFc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by linarith)), ?_⟩
  intro i j hi hj
  have key := hP (MvPolynomial.X i - MvPolynomial.X j)
  simp only [map_sub, MvPolynomial.aeval_X] at key
  have hsum : ∑ η ∈ s, c η * (η i - η j) = F (x i) - F (x j) := by
    rw [hF]; simp only
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun η hη => ?_
    have hi2 : η i = trc (R η) (x i) := (congrFun (hRη η hη) i).symm
    have hj2 : η j = trc (R η) (x j) := (congrFun (hRη η hη) j).symm
    rw [hi2, hj2]; ring
  rw [hsum] at key
  have hi' : ‖F (x i) - F g‖ < ε / 4 := by simpa [dist_eq_norm] using hi
  have hj' : ‖F (x j) - F g‖ < ε / 4 := by simpa [dist_eq_norm] using hj
  have hd : ‖F (x i) - F (x j)‖ ≤ ε / 2 := by
    have e : F (x i) - F (x j) = (F (x i) - F g) - (F (x j) - F g) := by ring
    rw [e]; linarith [norm_sub_le (F (x i) - F g) (F (x j) - F g)]
  have e2 : θ i - θ j = (θ i - θ j - (F (x i) - F (x j))) + (F (x i) - F (x j)) := by ring
  rw [e2]; linarith [norm_add_le (θ i - θ j - (F (x i) - F (x j))) (F (x i) - F (x j))]

end GlobalTheory
end

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem continuous_aeval_comp {Γ k : Type} [TopologicalSpace Γ] [CommRing k] [TopologicalSpace k]
    [IsTopologicalRing k] (f : Γ → k) (hf : Continuous f) (P : MvPolynomial Γ ℤ) :
    Continuous fun u : Γ → Γ => MvPolynomial.aeval (f ∘ u) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.aeval_X, Function.comp_apply]
    exact hp.mul (hf.comp (continuous_apply j))

theorem polyApprox_of_denseRange : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ), DenseRange x → ∀ (T : Γ → PadicAlgCl l), Continuous T →
    ∀ (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) →
    PolyApprox (fun j => T (x j)) ((fun ρ j => trc ρ (x j)) '' C) → PolyApprox T (trc '' C) := by
  intro l _ Γ _ _ _ _ a J x hx T hT C hC h ε hε
  classical
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  have hch : ∀ η ∈ s, ∃ ρ ∈ C, (fun j => trc ρ (x j)) = η := fun η hη => hs hη
  choose! ρ hρC hρη using hch
  have inj : Set.InjOn (fun η => trc (ρ η)) (s : Set (J → PadicAlgCl l)) := by
    intro η₁ h₁ η₂ h₂ e
    rw [← hρη η₁ h₁, ← hρη η₂ h₂]
    simp only at e
    rw [e]
  refine ⟨s.image (fun η => trc (ρ η)), fun σ => c (fun j => σ (x j)), ?_, fun P => ?_⟩
  · intro σ hσ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hσ
    obtain ⟨η, hη, rfl⟩ := hσ
    exact ⟨ρ η, hρC η hη, rfl⟩
  rw [Finset.sum_image inj]
  have hc : ∀ η ∈ s, c (fun j => trc (ρ η) (x j)) = c η := fun η hη => by rw [hρη η hη]
  rw [Finset.sum_congr rfl (fun η hη => by rw [show (fun σ : Γ → PadicAlgCl l => c fun j => σ (x j)) (trc (ρ η)) = c η from hc η hη])]
  have htr : ∀ η ∈ s, Continuous (trc (ρ η)) := fun η hη =>
    (Units.continuous_val.comp (hC _ (hρC η hη))).matrix_trace
  let F : (Γ → Γ) → PadicAlgCl l := fun u =>
    MvPolynomial.aeval (T ∘ u) P - ∑ η ∈ s, c η * MvPolynomial.aeval (trc (ρ η) ∘ u) P
  have hF : Continuous F := by
    refine (continuous_aeval_comp T hT P).sub (continuous_finsetSum _ fun η hη => ?_)
    exact continuous_const.mul (continuous_aeval_comp _ (htr η hη) P)
  have key : ‖F id‖ ≤ ε := by
    refine (DenseRange.piMap (fun _ : Γ => hx)).induction_on (p := fun u => ‖F u‖ ≤ ε) id
      (isClosed_le (continuous_norm.comp hF) continuous_const) fun v => ?_
    have e1 : MvPolynomial.aeval (T ∘ Pi.map (fun _ : Γ => x) v) P =
        MvPolynomial.aeval (fun j => T (x j)) (MvPolynomial.rename v P) := by
      rw [MvPolynomial.aeval_rename]; rfl
    have e2 : ∀ η ∈ s, MvPolynomial.aeval (trc (ρ η) ∘ Pi.map (fun _ : Γ => x) v) P =
        MvPolynomial.aeval η (MvPolynomial.rename v P) := fun η hη => by
      have e3 : trc (ρ η) ∘ Pi.map (fun _ : Γ => x) v = η ∘ v := by
        funext i
        simp only [Function.comp_apply, Pi.map_apply]
        exact congrFun (hρη η hη) (v i)
      rw [MvPolynomial.aeval_rename, e3]
    have := hP (MvPolynomial.rename v P)
    simp only [F]
    rw [e1, Finset.sum_congr rfl (fun η hη => by rw [e2 η hη])]
    exact this
  exact key

end GlobalTheory.Cong
end

section

open GlobalTheory.UnitLemma

theorem _root_.GlobalTheory.T.finite_units_mod_squares_of_unramifiedQuadratic : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [FiniteDimensional K.E L], Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by
  first | exact @GlobalTheory.UnitLemma.UQ.finite_units_mod_sq | exact GlobalTheory.UnitLemma.UQ.finite_units_mod_sq | (intros; apply GlobalTheory.UnitLemma.UQ.finite_units_mod_sq <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.finite_selfDualIntegral_hermitianLattices_modUnits : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x → ∀ c : K.O, c ≠ 0 → ∃ S : Set (Submodule K.O B.A), S.Finite ∧ (∀ J ∈ S, IsLat K.O K.E J) ∧ ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) → (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) → (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈ (algebraMap K.O K.E).range) → ∃ t ∈ B.T, mulLat K.O (t : B.A) J ∈ S := by
  first | exact @GlobalTheory.HullClasses.exists_unit_mulLat_mem_of_selfDual_lattice | exact GlobalTheory.HullClasses.exists_unit_mulLat_mem_of_selfDual_lattice | (intros; apply GlobalTheory.HullClasses.exists_unit_mulLat_mem_of_selfDual_lattice <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_openCompact_annihilator_scaled_integersK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ c : F, c ≠ 0 → ∃ D : AddSubgroup A.K, (D : Set A.K) = {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} ∧ IsOpen (D : Set A.K) ∧ IsCompact (D : Set A.K) := by
  first | exact @GlobalTheory.JR.DualScaledIntegers.exists_open_compact_annihilator | exact GlobalTheory.JR.DualScaledIntegers.exists_open_compact_annihilator | (intros; apply GlobalTheory.JR.DualScaledIntegers.exists_open_compact_annihilator <;> assumption)
end
