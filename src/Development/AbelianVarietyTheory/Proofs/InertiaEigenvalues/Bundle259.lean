module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle235
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrFiniteOverPadicTopologiesExist
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle118
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle090
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle151
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle035
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle229
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.WeaklyAdmissibleFiltrations.Statement

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

noncomputable section

namespace GlobalTheory.DeRhamSymbol

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem mem_iff (K : FinExt l) (a : ℤ) (x : P.R.BdR) :
    x ∈ (P.PD K).Fil a ↔ x ∈ (P.PD (botExt l)).Fil a := by
  have h := P.PD_Fil K (botExt l) a
  rw [← SetLike.mem_coe, h, SetLike.mem_coe]

theorem om_mem (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ (P.PD (botExt l)).Fil 0 := by
  obtain ⟨K, hK⟩ : ∃ K : FinExt l, x ∈ K.1 := ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩,
    IntermediateField.mem_adjoin_simple_self _ x⟩
  have h := ((P.PD K).Fil 0).smul_mem ⟨x, hK⟩ (P.PD K).one_mem
  rw [Algebra.smul_def, mul_one] at h
  exact (mem_iff K 0 _).1 h

theorem t_isUnit (P : LocPrime l) : IsUnit (P.ιB P.tB) := by
  have hu := (P.PD (botExt l)).t_unit
  rw [P.period_datum_t_eq] at hu
  exact hu.map P.ιB

def tU (P : LocPrime l) : P.R.BdRˣ := (t_isUnit P).unit

theorem tU_val : ((tU P : P.R.BdRˣ) : P.R.BdR) = P.ιB P.tB := rfl

theorem act_mem {a : ℤ} (g : GQ l) {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil a) :
    P.actQdR g x ∈ (P.PD (botExt l)).Fil a := by
  have := (P.PD (botExt l)).Fil_G ⟨g, mem_GK_bot g⟩ a x hx
  rwa [P.PD_actdR] at this

theorem actQdR_periodT_eq_cyclotomic_bottom (g : GQ l) :
    P.actQdR g (P.ιB P.tB) = algebraMap ℚ_[l] P.R.BdR (P.χQ g) * P.ιB P.tB := by
  have h := (P.PD (botExt l)).t_act ⟨g, mem_GK_bot g⟩
  rw [P.PD_actB, P.period_datum_t_eq, P.PD_χ] at h
  have h3 := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_bot g⟩ P.tB
  rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at h3
  rw [← h3, h, map_smul, Algebra.smul_def]

theorem act_zpow (g : GQ l) (n : ℤ) :
    P.actQdR g ((tU P ^ n : P.R.BdRˣ) : P.R.BdR) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ n : ℚ_[l]ˣ) : ℚ_[l]) * ((tU P ^ n : P.R.BdRˣ) : P.R.BdR) := by
  have h : Units.map ((P.actQdR g : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →* P.R.BdR) (tU P) =
      Units.map (algebraMap ℚ_[l] P.R.BdR : ℚ_[l] →* P.R.BdR) (P.χQ g) * tU P :=
    Units.ext (actQdR_periodT_eq_cyclotomic_bottom g)
  have h2 := congrArg (fun u : P.R.BdRˣ => ((u ^ n : P.R.BdRˣ) : P.R.BdR)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul] at h2
  rw [map_zpow P.χQ] at h2
  exact h2

variable {AI : LocAinf l P} (J : ThetaL P AI)
include J

theorem zpow_mem (n : ℤ) : ((tU P ^ n : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD (botExt l)).Fil n := by
  have h1 : ((tU P : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD (botExt l)).Fil 1 := by
    have := (P.PD (botExt l)).mem_filtration_one
    rwa [P.PD_ι, P.period_datum_t_eq] at this
  have h2 : (((tU P)⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD (botExt l)).Fil (-1) := by
    obtain ⟨y, hy, e⟩ := (J.fil_succ_iff_mul_t (-1) 1).1 (by simpa using (P.PD (botExt l)).one_mem)
    rw [← tU_val] at e
    rwa [Units.inv_eq_of_mul_eq_one_right e.symm]
  induction n using Int.induction_on with
  | zero => simpa using (P.PD (botExt l)).one_mem
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul]
    exact (P.PD (botExt l)).Fil_mul _ _ _ _ ih h1
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, sub_eq_add_neg]
    exact (P.PD (botExt l)).Fil_mul _ _ _ _ ih h2

theorem shift_iff (a b : ℤ) (x : P.R.BdR) :
    ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x ∈ (P.PD (botExt l)).Fil b ↔
      x ∈ (P.PD (botExt l)).Fil (a + b) := by
  constructor
  · intro h
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ (zpow_mem J a) h
    rwa [← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
      one_mul] at this
  · intro h
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ (zpow_mem J (-a)) h
    rwa [neg_add_cancel_left] at this


omit J in
theorem exists_symbol : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), ThetaL P AI →
    ∀ (K : FinExt l), ∃ sy : ℤ → P.R.BdR → PadicComplex l, ∀ a : ℤ,
      (∀ x ∈ (P.PD K).Fil a, ∀ y ∈ (P.PD K).Fil a, sy a (x + y) = sy a x + sy a y) ∧
      (∀ (c : Om l), ∀ x ∈ (P.PD K).Fil a,
        sy a (algebraMap (Om l) P.R.BdR c * x) = (c : PadicComplex l) * sy a x) ∧
      (∀ x ∈ (P.PD K).Fil a, sy a x = 0 ↔ x ∈ (P.PD K).Fil (a + 1)) ∧
      ∀ (g : GQ l), ∀ x ∈ (P.PD K).Fil a,
        sy a (P.actQdR g x) = chiC P.χQ a g * AI.actC g (sy a x) := by
  intro l _ P AI J K
  refine ⟨fun a x => J.θ (((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x), fun a => ?_⟩
  have key : ∀ x ∈ (P.PD K).Fil a,
      ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x ∈ (P.PD (botExt l)).Fil 0 := fun x hx =>
    (shift_iff J a 0 x).2 (by rw [add_zero]; exact (mem_iff K a x).1 hx)
  refine ⟨fun x hx y hy => ?_, fun c x hx => ?_, fun x hx => ?_, fun g x hx => ?_⟩
  · beta_reduce
    rw [mul_add, J.θ_add _ (key x hx) _ (key y hy)]
  · beta_reduce
    rw [mul_left_comm, J.θ_mul _ (om_mem c) _ (key x hx), J.θ_Om]
  · beta_reduce
    rw [J.θ_ker _ (key x hx), shift_iff J, mem_iff K]
  · beta_reduce
    have e : ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * P.actQdR g x =
        algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l])) *
          P.actQdR g (((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x) := by
      rw [← IsScalarTower.algebraMap_apply, map_mul, act_zpow, ← mul_assoc, ← mul_assoc,
        ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
        map_one, one_mul]
    rw [e, J.θ_mul _ (om_mem _) _ (act_mem g (key x hx)), J.θ_Om, J.θ_act g _ (key x hx)]
    rfl

end GlobalTheory.DeRhamSymbol
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory

theorem isBaseChange_comap_of_exact (A E : Type) [CommRing A] [CommRing E] [Algebra A E]
    [Module.Flat A E] (D₀ D₁ D₂ : Type) [AddCommGroup D₀] [AddCommGroup D₁] [AddCommGroup D₂]
    [Module E D₀] [Module E D₁] [Module E D₂] [Module A D₀] [Module A D₁] [Module A D₂]
    [IsScalarTower A E D₀] [IsScalarTower A E D₁] [IsScalarTower A E D₂]
    (j : D₀ →ₗ[E] D₁) (q : D₁ →ₗ[E] D₂) (N₁ : Submodule A D₁) (N₂ : Submodule A D₂)
    (hj : Function.Injective j) (hex : Function.Exact j q) (_hq : Function.Surjective q)
    (h₁ : IsBaseChange E N₁.subtype) (h₂ : IsBaseChange E N₂.subtype)
    (hN : ∀ x ∈ N₁, q x ∈ N₂) :
    IsBaseChange E (N₁.comap (j.restrictScalars A)).subtype := by
  set N₀ := N₁.comap (j.restrictScalars A) with hN₀
  let ι : N₀ →ₗ[A] N₁ := (j.restrictScalars A).restrict (fun x hx => hx)
  let f : N₁ →ₗ[A] N₂ := (q.restrictScalars A).restrict hN
  have hιv : ∀ y : N₀, (ι y : D₁) = j y := fun _ => rfl
  have hfv : ∀ y : N₁, (f y : D₂) = q y := fun _ => rfl
  have hι : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    apply hj
    have := congrArg Subtype.val hxy
    simpa [ι] using this
  have hιf : Function.Exact ι f := by
    intro y
    constructor
    · intro hy
      have hy' : q (y : D₁) = 0 := by
        have := congrArg Subtype.val hy
        rwa [hfv] at this
      obtain ⟨x, hx⟩ := (hex (y : D₁)).1 hy'
      refine ⟨⟨x, ?_⟩, ?_⟩
      · show j x ∈ N₁
        rw [hx]; exact y.2
      · apply Subtype.ext
        simpa [ι] using hx
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      simp only [f, ι, LinearMap.restrict_apply, LinearMap.restrictScalars_apply,
        ZeroMemClass.coe_zero]
      exact (hex (j x)).2 ⟨x, rfl⟩
  have hιT : Function.Injective (LinearMap.lTensor E ι) :=
    Module.Flat.lTensor_preserves_injective_linearMap ι hι
  have hfT : Function.Exact (LinearMap.lTensor E ι) (LinearMap.lTensor E f) :=
    Module.Flat.lTensor_exact E hιf
  let Φ : E ⊗[A] N₀ →ₗ[E] D₀ := N₀.subtype.liftBaseChange E
  have hcomm₁ : ∀ t : E ⊗[A] N₀, j (Φ t) = h₁.equiv (LinearMap.lTensor E ι t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [Φ, IsBaseChange.equiv_tmul, hιv]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hcomm₂ : ∀ t : E ⊗[A] N₁, h₂.equiv (LinearMap.lTensor E f t) = q (h₁.equiv t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [IsBaseChange.equiv_tmul, hfv]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hΦi : Function.Injective Φ := by
    intro s t hst
    apply hιT
    apply h₁.equiv.injective
    rw [← hcomm₁, ← hcomm₁, hst]
  have hΦs : Function.Surjective Φ := by
    intro d
    obtain ⟨t, ht⟩ := h₁.equiv.surjective (j d)
    have h0 : LinearMap.lTensor E f t = 0 := by
      apply h₂.equiv.injective
      rw [hcomm₂, ht, map_zero]
      exact (hex (j d)).2 ⟨d, rfl⟩
    obtain ⟨s, hs⟩ := (hfT t).1 h0
    refine ⟨s, hj ?_⟩
    rw [hcomm₁, hs, ht]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ ⟨hΦi, hΦs⟩) ?_
  intro x
  show Φ (1 ⊗ₜ x) = x
  simp [Φ, LinearMap.liftBaseChange_tmul]

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem map_eq_prod_of_valuationSubring {O A K F : Type} [CommRing O] [Field K] [CommRing F]
    (B : ValuationSubring K) (j : O →+* K) (φ : B →+* F) (ψ : O →+* F)
    (h : ∀ y, ∃ h : j y ∈ B, φ ⟨_, h⟩ = ψ y) (t : A → K) (ι : A → F)
    (ht : ∀ x, ∃ h : t x ∈ B, ι x = φ ⟨_, h⟩) (p : O[X]) (s : Multiset A)
    (hp : p.map j = (s.map fun x => X - C (t x)).prod) :
    p.map ψ = (s.map fun x => X - C (ι x)).prod := by

  let j' : O →+* B :=
    { toFun := fun y => ⟨j y, (h y).1⟩
      map_one' := Subtype.ext (map_one j)
      map_mul' := fun a b => Subtype.ext (map_mul j a b)
      map_zero' := Subtype.ext (map_zero j)
      map_add' := fun a b => Subtype.ext (map_add j a b) }
  let t' : A → B := fun x => ⟨t x, (ht x).1⟩
  have hψ : ψ = φ.comp j' := by
    ext y
    exact ((h y).2).symm
  have hj : B.subtype.comp j' = j := by
    ext y
    rfl
  have hB : p.map j' = (s.map fun x => X - C (t' x)).prod := by
    apply Polynomial.map_injective B.subtype Subtype.val_injective
    rw [Polynomial.map_map, hj, hp, Polynomial.map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro x _
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  rw [hψ, ← Polynomial.map_map, hB, Polynomial.map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [(ht x).2]

end GlobalTheory.TypeLeaf
end
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

theorem _root_.GlobalTheory.T.exists_H2_preimage_of_monotone_open_exhaustion : ∀ {O : Type} [CommRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    (ε : G →* Oˣ) {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] (N : ℕ → Submodule O M), Monotone N → (∀ n, IsOpen (N n : Set M)) → (∀ x, ∃ n, x ∈ N n) →
    ∀ z : H2 (twist ε M), ∃ n, ∃ z' : H2 (twist ε (N n)),
      mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val (twist_map ε (N n).subtype) z' = z := by
  first | exact @GlobalTheory.h2_twist_exists_of_iUnion_open | exact GlobalTheory.h2_twist_exists_of_iUnion_open | (intros; apply GlobalTheory.h2_twist_exists_of_iUnion_open <;> assumption)
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

theorem _root_.GlobalTheory.T.map_H2_subtype_injective : ∀ {O : Type} [CommRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {ε : G →* Oˣ} (Θ : NatInv ε (fun M _ _ _ => IsFGTop O M))
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] (N : ℕ → Submodule O M), Monotone N → (∀ n, IsOpen (N n : Set M)) → (∀ x, ∃ n, x ∈ N n) →
    ∀ (hfg : ∀ n, IsFGTop O (N n)) (n : ℕ),
      Function.Injective (mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val (twist_map ε (N n).subtype)) := by
  first | exact @GlobalTheory.map_H2_subtype_injective_of_union | exact GlobalTheory.map_H2_subtype_injective_of_union | (intros; apply GlobalTheory.map_H2_subtype_injective_of_union <;> assumption)
end

section


theorem _root_.GlobalTheory.T.dvr_finite_over_padic_topologies_exist : ReciprocityTheory.ChartRestriction.T2.TopEx := by
  first | exact @GlobalTheory.PadicTop.topEx | exact GlobalTheory.PadicTop.topEx | (intros; apply GlobalTheory.PadicTop.topEx <;> assumption)
end

section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal ReciprocityTheory.ChartRestriction.T2

namespace GlobalTheory.FinIsoDualLattice

theorem finIso_of_localTateDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) : FinIso := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ hK hO i D hD
  obtain ⟨hR, hC, hT2, hA, hpm, hp0⟩ := hO
  haveI := hR; haveI := hC; haveI := hT2; haveI := hD.t2'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hFin, hFree⟩ := GlobalTheory.T.dualLat_finite_free_of_isLatticeIn D.bT D.T hD.lat hD.perf
  haveI := hFin; haveI := hFree
  obtain ⟨hcpl, hsep⟩ := GlobalTheory.T.compact_dvr_adic_complete_separated_uniformizer hA ϖ hϖ
  obtain ⟨hcT, hsT⟩ := GlobalTheory.freeModule_adicComplete_separated ϖ hcpl hsep (↥D.T')
  obtain ⟨hcomp, hopen, hemb⟩ := GlobalTheory.T.finite_free_module_compact_adic_dvr hA (M := ↥D.T') ϖ hϖ
  haveI := hcomp
  have hρ : ContAction D.ρTl' := sub_contAction D.contT' D.T' D.stT'
  have hpϖ : (p : O) ∈ Ideal.span {ϖ} := by
    rwa [← Irreducible.maximalIdeal_eq hϖ]
  obtain ⟨s, hs⟩ := GlobalTheory.T.modUniformiser_cocycles_finite_classes_local hT hK i D.ρTl' hρ ϖ hpϖ hopen
  have hl := GlobalTheory.T.cocycle_eq_add_uniformizer_smul_add_coboundary D.ρTl' hρ ϖ hemb.isEmbedding s hs
  have hd : ∀ t : ↥D.T', d0 D.ρTl' t ∈ Z1 D.ρTl' := fun t => by
    refine ⟨?_, fun g h => ?_⟩
    · exact (hρ.comp (continuous_id.prodMk continuous_const)).sub continuous_const
    · simp only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]; abel
  let d : ↥D.T' →ₗ[O] ↥(Z1 D.ρTl') := LinearMap.codRestrict _ (d0 D.ρTl') hd
  have hdN : LinearMap.range d ≤ (B1 D.ρTl').comap (Z1 D.ρTl').subtype := by
    rintro _ ⟨t, rfl⟩; exact ⟨t, rfl⟩
  have hZ : ∀ c : ↥(Z1 D.ρTl'), (∀ n : ℕ, ∃ z : ↥(Z1 D.ρTl'), c = ϖ ^ n • z) → c = 0 := by
    intro c hc
    apply Subtype.ext; funext g
    exact hsT _ fun n => by
      obtain ⟨z, hz⟩ := hc n
      exact ⟨(z : G → ↥D.T') g, by rw [hz]; rfl⟩
  refine GlobalTheory.finite_quotient_of_complete_nakayama ϖ hcpl hcT hZ d _ hdN s fun c => ?_
  obtain ⟨a, c', x, hx⟩ := hl c
  refine ⟨a, c', x, Subtype.ext ?_⟩
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, d, LinearMap.codRestrict_apply]
  exact hx

end GlobalTheory.FinIsoDualLattice
end
