module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.KIface
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CIface
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle074
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace Grp

namespace P_lamMul

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem chk_mul (ψ : kˣ →* ℂˣ) {x y : k} (hx : x ≠ 0) (hy : y ≠ 0) :
    chk ψ (x * y) = chk ψ x * chk ψ y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  unfold chk
  rw [dite_eq_right hxy, dite_eq_right hx, dite_eq_right hy]
  have e : Units.mk0 (x * y) hxy = Units.mk0 x hx * Units.mk0 y hy := Units.ext rfl
  rw [e, map_mul, Units.val_mul]

theorem algebraMap_unit_ne_zero (u : 𝒪[k]ˣ) : algebraMap 𝒪[k] k (u : 𝒪[k]) ≠ 0 :=
  (u.isUnit.map (algebraMap 𝒪[k] k)).ne_zero

theorem chk_unit (ψ : kˣ →* ℂˣ) (u : 𝒪[k]ˣ) :
    chk ψ (algebraMap 𝒪[k] k (u : 𝒪[k])) = ((res ψ u : ℂˣ) : ℂ) := by
  unfold chk
  rw [dite_eq_right (algebraMap_unit_ne_zero u)]
  have e : Units.mk0 (algebraMap 𝒪[k] k (u : 𝒪[k])) (algebraMap_unit_ne_zero u) = unitIncl k u :=
    Units.ext rfl
  rw [e]
  rfl

variable {n : ℕ} (G : Grp k n)

theorem Δ_ne_zero (hU : ModulusOnUnitsProp G) (hB : CompactConductorBoundProp G) {g : GL (Fin n) k} (hg : g ∈ G.JSet)
    (a : Fin G.s) : G.Δ a g ≠ 0 := by
  obtain ⟨u, hu⟩ := hU hB g hg a
  rw [hu]
  exact algebraMap_unit_ne_zero u

theorem Δ_last (a : Fin G.s) (ha : ¬ (a : ℕ) + 1 < G.s) (g : GL (Fin n) k) :
    G.Δ a g = (g : Matrix (Fin n) (Fin n) k).det := by
  have hall : ∀ i : Fin n, G.bl i ≤ a := by
    intro i
    have := (G.bl i).isLt
    rw [Fin.le_def]
    omega
  unfold Δ
  exact Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv hall) _

theorem factor_mul (hC : CompactConductorBasicProp (k := k)) (hU : ModulusOnUnitsProp G) (hM : ModulusMultiplicativeProp G) (hB : CompactConductorBoundProp G)
    {g h : GL (Fin n) k} (hg : g ∈ G.JSet) (hh : h ∈ G.JSet) (a : Fin G.s) :
    chk (G.μ a / G.μnext a) (G.Δ a (g * h)) =
      chk (G.μ a / G.μnext a) (G.Δ a g) * chk (G.μ a / G.μnext a) (G.Δ a h) := by
  have hgz := Δ_ne_zero G hU hB hg a
  have hhz := Δ_ne_zero G hU hB hh a
  by_cases ha : (a : ℕ) + 1 < G.s
  · obtain ⟨u, hu1, hu⟩ := hM hC hB g hg h hh a ha
    have hn : G.μnext a = G.μ ⟨a + 1, ha⟩ := by unfold μnext; rw [dite_eq_left ha]
    have hres : ((res (G.μ a / G.μnext a) u : ℂˣ) : ℂ) = 1 := by
      rw [hn, hB.2.2.2 a ⟨a + 1, ha⟩ u hu1, Units.val_one]
    rw [hu, chk_mul _ (mul_ne_zero hgz hhz) (algebraMap_unit_ne_zero u), chk_unit, hres, mul_one,
      chk_mul _ hgz hhz]
  · rw [Δ_last G a ha, Δ_last G a ha, Δ_last G a ha, Units.val_mul, Matrix.det_mul]
    rw [← Δ_last G a ha g, ← Δ_last G a ha h]
    exact chk_mul _ hgz hhz

theorem lam_mul_of (hC : CompactConductorBasicProp (k := k)) (hU : ModulusOnUnitsProp G) (hM : ModulusMultiplicativeProp G) (hB : CompactConductorBoundProp G)
    {g h : GL (Fin n) k} (hg : g ∈ G.JSet) (hh : h ∈ G.JSet) : G.lam (g * h) = G.lam g * G.lam h := by
  unfold lam
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun a _ => factor_mul G hC hU hM hB hg hh a

end P_lamMul

theorem step_lamMul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : LambdaMultiplicativeProp G := by
  intro hC hU hM hB g hg h hh
  exact P_lamMul.lam_mul_of G hC hU hM hB hg hh

end Grp

end UpperTheory.TNZ
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.CuspidalSupport₂

variable {k : Type} [Field k]

theorem twist_detRep_one (χ η : kˣ →* ℂˣ) :
    twist (detRep (Fin 1) χ) (detChar (Fin 1) η) = detRep (Fin 1) (η * χ) := by
  have h : GlobalTheory.SmGL.detChar (Fin 1) η * GlobalTheory.SmGL.detChar (Fin 1) χ =
      GlobalTheory.SmGL.detChar (R := k) (Fin 1) (η * χ) := by
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.mul_apply, GlobalTheory.SmGL.detChar_apply]
  unfold GlobalTheory.SmGL.detRep GlobalTheory.SmGL.ofChar
  rw [GlobalTheory.SmGL.twist_twist, h]

theorem twist_twist_inv {d : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (σ : Representation ℂ (GL (Fin d) k) X) (η : kˣ →* ℂˣ) :
    twist (twist σ (detChar (Fin d) η⁻¹)) (detChar (Fin d) η) = σ := by
  have h : GlobalTheory.SmGL.detChar (Fin d) η * GlobalTheory.SmGL.detChar (Fin d) η⁻¹ =
      (1 : GL (Fin d) k →* ℂˣ) := by
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.mul_apply, GlobalTheory.SmGL.detChar_apply, MonoidHom.inv_apply,
      mul_inv_cancel, MonoidHom.one_apply]
  rw [GlobalTheory.SmGL.twist_twist, h, GlobalTheory.SmGL.twist_one]

end UpperTheory.TNZ.CuspidalSupport₂

namespace UpperTheory.TNZ

open CuspidalSupport₂ in
theorem step_cuspSupp : CuspidalSupportProp := by
  intro hL k _ _ _ _ d X _ _ σ hs hi η hη hdv
  obtain ⟨v, hv0, hv⟩ := hdv
  set τ := twist σ (detChar (Fin d) η⁻¹) with hτ
  have hτs : IsSmooth τ := isSmooth_twist hs hη.inv.detChar
  have hτi : τ.IsIrreducible := isIrreducible_twist hi _
  have hadm : IsAdmissible τ := (hL.bz k).1 (Fin d) X τ hτs hτi
  have hI : fixed τ (iwahori k (Fin d)) ≠ ⊥ := by
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    have hg := hv h.1 (iwahori_le_KO k _ h.2)
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    show (detChar (Fin d) η⁻¹ h.1 : ℂ) • σ h.1 v = v
    rw [hg, smul_smul, detChar_apply, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_smul]
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm hτi hI
  let χ : Fin d → kˣ →* ℂˣ := fun i => unrChar k (α i)
  have h1 := hα.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k d χ)
  have h2 := isSubquotient_twist h1 (detChar (Fin d) η)
  rw [hτ, twist_twist_inv] at h2
  have hχs : ∀ i, IsSmoothChar (χ i) := fun i => isSmoothChar_of_isUnram (isUnram_unrChar (k := k) (α i))
  let φ := multiProdTwistEquiv (Equiv.sigmaUnique (Fin d) fun _ => Fin 1)
    (fun i => detRep (Fin 1) (χ i)) hη
  have h3 := h2.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have hfam : (fun i => twist (detRep (Fin 1) (χ i)) (detChar (Fin 1) η)) =
      fun i => detRep (Fin 1) (η * χ i) := funext fun i => twist_detRep_one _ _
  rw [hfam] at h3
  refine ⟨fun j => η * χ j, fun j => ⟨hη.mul (hχs j), fun u hu => ?_⟩, hi,
    fun j => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hη.mul (hχs j))⟩, _, h3⟩
  show η u * unrChar k (α j) u = η u
  rw [isUnram_unrChar (k := k) (α j) u hu, mul_one]

end UpperTheory.TNZ
end
end

section

noncomputable section

open ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace UpperTheory.TNZ.ProductIrreducible₂

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem exists_det_eq (u : kˣ) : ∃ g : GL (Fin 1) k, GeneralLinearGroup.det g = u := by
  refine ⟨⟨Matrix.diagonal fun _ => (u : k), Matrix.diagonal fun _ => ((u⁻¹ : kˣ) : k), ?_, ?_⟩, ?_⟩
  · simp [Matrix.diagonal_mul_diagonal]
  · simp [Matrix.diagonal_mul_diagonal]
  · ext
    simp [Matrix.GeneralLinearGroup.val_det_apply]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem char_eq_of_equiv {μ μ' χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ (GL (Fin 1) k) W} (ψ : (detRep (Fin 1) μ').Equiv τ)
    (φ : (detRep (Fin 1) μ).Equiv (twist τ (detChar (Fin 1) χ))) (g : GL (Fin 1) k) :
    (μ (GeneralLinearGroup.det g) : ℂ) =
      (χ (GeneralLinearGroup.det g) : ℂ) * (μ' (GeneralLinearGroup.det g) : ℂ) := by
  have hτ : ∀ w : W, τ g w = (μ' (GeneralLinearGroup.det g) : ℂ) • w := by
    intro w
    obtain ⟨x, rfl⟩ := ψ.toLinearEquiv.surjective w
    have key : ψ.toLinearEquiv (detRep (Fin 1) μ' g x) = τ g (ψ.toLinearEquiv x) :=
      LinearMap.congr_fun (ψ.toIntertwiningMap.isIntertwining' g) x
    rw [← key]
    simp only [detRep, ofChar_apply, detChar_apply]
    rw [← smul_eq_mul, map_smul]
  have key : φ.toLinearEquiv (detRep (Fin 1) μ g 1) = twist τ (detChar (Fin 1) χ) g (φ.toLinearEquiv 1) :=
    LinearMap.congr_fun (φ.toIntertwiningMap.isIntertwining' g) 1
  simp only [detRep, ofChar_apply, detChar_apply, twist_apply, hτ, mul_one, smul_smul] at key
  have hne : φ.toLinearEquiv 1 ≠ 0 := by
    rw [Ne, LinearEquiv.map_eq_zero_iff]
    exact one_ne_zero
  have h1 : φ.toLinearEquiv ((μ (GeneralLinearGroup.det g) : ℂ)) =
      (μ (GeneralLinearGroup.det g) : ℂ) • φ.toLinearEquiv 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [h1] at key
  exact smul_left_injective ℂ hne key

theorem eq_on_units (y : IrrGL (k := k)) (h : 1 = y.1) (μ μ' : kˣ →* ℂˣ) (hμ : IsSmoothChar μ)
    (hs' : IsSmooth (detRep (Fin 1) μ')) (hi' : (detRep (Fin 1) μ').IsIrreducible)
    (hy : IrrGL.of (detRep (Fin 1) μ') hs' hi' = y) (j : ℤ)
    (hφ : Nonempty ((h ▸ GlobalTheory.SplitRead.Irr.ofDet 1 μ hμ : GlobalTheory.SplitRead.Irr k y.1).π.Equiv
      (twist (GlobalTheory.SplitRead.Irr.ofIrrRep y.2.rep).π (detChar (Fin y.1) (absPow k (j : ℂ))))))
    (u : kˣ) (hu : valuation k (u : k) = 1) : μ u = μ' u := by
  subst hy
  obtain ⟨φ⟩ := hφ
  obtain ⟨g, hg⟩ := exists_det_eq u
  have := char_eq_of_equiv (IrrGL.equivOf (detRep (Fin 1) μ') hs' hi') φ g
  rw [hg] at this
  have habs : (absPow k (j : ℂ) u : ℂ) = 1 := by
    rw [val_absPow, nabs_eq_one (k := k) hu]
    simp
  rw [habs, one_mul] at this
  exact Units.ext this

theorem product_irreducible_of_distinct_twists (hL : GlobalTheory.Mem.LiteralAutomorphy.LitLoc) :
    ∀ (s N : ℕ) (d : Fin s → ℕ) (hd : ∑ b, d b = N) (X : Fin s → Type) [∀ b, AddCommGroup (X b)]
      [∀ b, Module ℂ (X b)] (σ : ∀ b, Representation ℂ (GL (Fin (d b)) k) (X b)),
      (∀ b, IsSmooth (σ b)) → (∀ b, (σ b).IsIrreducible) → ∀ η : Fin s → kˣ →* ℂˣ,
      (∀ b c, b ≠ c → ∃ u : kˣ, valuation k (u : k) = 1 ∧ η b u ≠ η c u) →
      ∀ μ : ∀ b, Fin (d b) → kˣ →* ℂˣ,
      (∀ b j, IsSmoothChar (μ b j) ∧ ∀ u : kˣ, valuation k (u : k) = 1 → μ b j u = η b u) →
      (∀ b, IsCuspSupport (σ b) (fun _ => 1) (fun j => detRep (Fin 1) (μ b j))) →
        (multiProd (stdBlocks d hd) σ).IsIrreducible := by
  intro s
  induction s with
  | zero =>
    intros
    exact GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd_zero _ _
  | succ s ih =>
    intro N d hd X _ _ σ hs hi η hη μ hμ hcs
    have e : N = d 0 + ∑ i : Fin s, d i.succ := hd.symm.trans (Fin.sum_univ_succ _)
    subst e
    obtain ⟨E⟩ := GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ d hd σ
    have hτi : (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ).IsIrreducible :=
      ih _ (fun i => d i.succ) rfl (fun i => X i.succ) (fun i => σ i.succ) (fun i => hs _) (fun i => hi _)
        (fun i => η i.succ) (fun b c hbc => hη _ _ fun h => hbc (Fin.succ_injective _ h))
        (fun i => μ i.succ) (fun i => hμ _) (fun i => hcs _)
    have hτs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ) :=
      isSmooth_parInd _ _
    obtain ⟨h', x, hx, hxc⟩ := GlobalTheory.LocGL.SupportRing.hasSupport_multiProd hL.zel (d := fun i : Fin s => d i.succ) rfl
      (fun i => σ i.succ) (fun i => hs _) (fun i => hi _) (fun i => hasSupport_of_isCuspSupport (hcs i.succ)) hτi
    have hP := hL.disj k (d 0) (∑ i : Fin s, d i.succ) (d 0) h'
      { V := X 0, π := σ 0, smooth := hs 0, irr := hi 0 }
      { V := _, π := multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i => σ i.succ, smooth := hτs,
        irr := hτi }
      (fun _ => 1) (fun b => (x b).1) (fun a => GlobalTheory.SplitRead.Irr.ofDet 1 (μ 0 a) (hμ 0 a).1)
      (fun b => GlobalTheory.SplitRead.Irr.ofIrrRep (x b).2.rep) (hcs 0) hxc ?_
    · exact GlobalTheory.Parabolic.isIrreducible_of_equiv E hP
    · intro a b hab j _ hφ
      have hxb : x b ∈ ∑ i : Fin s, Finset.univ.val.map fun a =>
          IrrGL.of (detRep (Fin 1) (μ i.succ a)) ((hcs i.succ).2.1 a).2.2.1 ((hcs i.succ).2.1 a).2.1 := by
        rw [← hx]
        exact Multiset.mem_map_of_mem x (Finset.mem_univ_val b)
      obtain ⟨c, -, hc⟩ := Multiset.mem_sum.1 hxb
      obtain ⟨j', -, hj'⟩ := Multiset.mem_map.1 hc
      obtain ⟨u, hu, hne⟩ := hη 0 c.succ (Fin.succ_ne_zero c).symm
      apply hne
      rw [← (hμ 0 a).2 u hu, ← (hμ c.succ j').2 u hu]
      exact eq_on_units (x b) hab (μ 0 a) (μ c.succ j') (hμ 0 a).1 _ _ hj' j hφ u hu

end UpperTheory.TNZ.ProductIrreducible₂

namespace UpperTheory.TNZ

theorem step_prodIrr : ProductIrreducibleProp := by
  unfold ProductIrreducibleProp
  intro hC hL k _ _ _ _ s N d hd X _ _ σ hs hi η hη hdv hne
  have H := fun b => hC hL k (d b) (X b) (σ b) (hs b) (hi b) (η b) (hη b) (hdv b)
  choose μ hμ hcs using H
  exact ProductIrreducible₂.product_irreducible_of_distinct_twists hL s N d hd X σ hs hi η hne μ hμ hcs

end UpperTheory.TNZ
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

def Need_CMain : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ρ.IsIrreducible →
    (∃ x : V, x ≠ 0 ∧ ∀ g ∈ G.JSet, ρ g x = G.lam g • x) → IsTwSphProd ρ G.d G.hd G.μ

def Need_CProps : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n),
    G.JSet ⊆ KO k (Fin n) ∧ (1 : GL (Fin n) k) ∈ G.JSet ∧
    (∀ g ∈ G.JSet, ∀ g' ∈ G.JSet, g * g' ∈ G.JSet ∧ G.lam (g * g') = G.lam g * G.lam g') ∧
    (∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) ∧ (∀ g ∈ G.JSet, G.lam g ≠ 0) ∧
    IsOpen (KC k n G.lev) ∧ (1 : GL (Fin n) k) ∈ KC k n G.lev ∧ KC k n G.lev ⊆ G.JSet ∧ (∀ g ∈ KC k n G.lev, G.lam g = 1) ∧
    (∀ φ ∈ G.V0sp, ∀ k' : ↥(KO k (Fin n)), rightReg ℂ ↥(KO k (Fin n)) ℂ k' φ ∈ G.V0sp) ∧ FiniteDimensional ℂ G.V0sp ∧
    G.v0 ∈ G.V0sp ∧ G.v0 ≠ 0 ∧
    ∀ j : ↥(KO k (Fin n)), (j : GL (Fin n) k) ∈ G.JSet → rightReg ℂ ↥(KO k (Fin n)) ℂ j G.v0 = G.lam j • G.v0

def Need_Grp : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (μ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (μ i)) →
    ∃ (G : Grp k n) (σ : Fin n ≃ Fin n), ∀ i, res (G.chi i) = res (μ (σ i))

def ArtinTransferDecompositionCharacter : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
    ∀ (n : ℕ) (χ : Fin n → _root_.ReciprocityTheory.Gal.Dec (F := E) A →* ℂˣ), (∀ i, IsOpen ((χ i).ker : Set (_root_.ReciprocityTheory.Gal.Dec (F := E) A))) →
      ∃ μ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ, (∀ i, IsSmoothChar (μ i)) ∧
        ∀ i (σ : Weil h), χ i (Subgroup.inclusion (Weil_le_Dec h) σ) = μ i (a σ)

def LocalArtinCharacterProduct : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
    ∀ (n : ℕ) (χ : Fin n → _root_.ReciprocityTheory.Gal.Dec (F := E) A →* ℂˣ) (ho : ∀ i, IsOpen ((χ i).ker : Set (_root_.ReciprocityTheory.Gal.Dec (F := E) A)))
      (μ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ), (∀ i (σ : Weil h), χ i (Subgroup.inclusion (Weil_le_Dec h) σ) = μ i (a σ)) →
      ∀ (G : Grp (w.adicCompletion E) n) (σ : Fin n ≃ Fin n), (∀ i, res (G.chi i) = res (μ (σ i))) →
        ∀ s : ↥(Ine (F := E) A), (xOf h χ ho).charPol (ineIncl h s) =
          ∏ b, (X - C (((G.μ b (a (ineIncl h s))) : ℂˣ) : ℂ)) ^ G.d b

def FiniteDimensionalTranslationCoordinates : Prop :=
  ∀ (K : Type) [Group K] [TopologicalSpace K] (W : Submodule ℂ (K → ℂ)), FiniteDimensional ℂ W →
    (∀ φ ∈ W, ∀ k : K, rightReg ℂ K ℂ k φ ∈ W) → (∀ φ ∈ W, IsOpen {k : K | rightReg ℂ K ℂ k φ = φ}) →
    ∃ (m : ℕ) (V0 : Representation ℂ K (Fin m → ℂ)) (e : (Fin m → ℂ) →ₗ[ℂ] (K → ℂ)),
      Function.Injective e ∧ LinearMap.range e = W ∧ (∀ k v, e (V0 k v) = rightReg ℂ K ℂ k (e v)) ∧ IsSmooth V0

def TwistedSphericalRepresentative : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V) (h1 : IsSmooth ρ) (h2 : ρ.IsIrreducible)
    (s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = n) (η : Fin s → kˣ →* ℂˣ),
    IsTwSphProd (IrrGL.of ρ h1 h2).rep d hd η ↔ IsTwSphProd ρ d hd η

def DistinctOnUnitsDistinctOnInertia : Prop :=
  ArtinInertiaProp →
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
    ∀ (n : ℕ) (G : Grp (w.adicCompletion E) n) (b c : Fin G.s), b ≠ c →
      ∃ t : ↥(Ine (F := E) A), G.μ b (a (ineIncl h t)) ≠ G.μ c (a (ineIncl h t))

def SmoothVectorsFixedByCongruence : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n),
    IsOpen (KC k n G.lev) → (1 : GL (Fin n) k) ∈ KC k n G.lev →
    ∀ φ ∈ G.V0sp, IsOpen {k' : ↥(KO k (Fin n)) | rightReg ℂ ↥(KO k (Fin n)) ℂ k' φ = φ}

end UpperTheory.NonzeroTypeTheory
end
end
