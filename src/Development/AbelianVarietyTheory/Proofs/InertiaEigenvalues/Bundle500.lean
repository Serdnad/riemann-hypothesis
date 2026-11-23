module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle494
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealSideCharacterMatch
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle363
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle492
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle491
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTateH2Top
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar



noncomputable section

namespace GlobalTheory.ExportSeries

namespace RestrictHalfModel

variable {D : D7} {m n : ℕ}

theorem isHalf_iff' (e : AE D) (u : Mx D m n) : IsHalf e u ↔ e • u = u := GlobalTheory.SplitScalar.isHalf_iff e u

theorem isHalf_smul {e : AE D} (he : e * e = e) (u : Mx D m n) : IsHalf e (e • u) := by
  rw [isHalf_iff', smul_smul, he]

theorem halfInd_smul_congr {e : AE D} (he : e * e = e) (Λ : AddSubgroup (Mx D m n)) {z t : Mx D m n}
    (h : e • z - e • t ∈ Λ) : halfInd e Λ (e • z) = halfInd e Λ (e • t) := by
  unfold halfInd
  have hz := isHalf_smul he z
  have ht := isHalf_smul he t
  by_cases h1 : e • t ∈ Λ
  · rw [if_pos ⟨by simpa using Λ.add_mem h h1, hz⟩, if_pos ⟨h1, ht⟩]
  · rw [if_neg fun h2 => h1 (by simpa using Λ.sub_mem h2.1 h), if_neg fun h2 => h1 h2.1]

theorem smul_of_half {a' b : AE D} (hab : a' * b = 0) {x : Mx D m n} (hx : IsHalf a' x) :
    b • x = 0 ∧ (a' + b) • x = x := by
  rw [isHalf_iff'] at hx
  have h0 : b • x = 0 := by
    rw [← hx, smul_smul, mul_comm, hab, zero_smul]
  exact ⟨h0, by rw [add_smul, hx, h0, add_zero]⟩

theorem isHalf_add_iff {e : AE D} {t u : Mx D m n} (hu : e • u = u) : IsHalf e (t + u) ↔ IsHalf e t := by
  rw [isHalf_iff', isHalf_iff', smul_add, hu, add_left_inj]

theorem isSBHalf_restrictHalf {a' b : AE D} (ha' : a' * a' = a') (hb : b * b = b) {Λ : AddSubgroup (Mx D m n)}
    (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) {Φ : Mx D m n → ℂ} (hΦ : IsSBHalf a' Λ Φ) :
    IsSBHalf (a' + b) Λ (restrictHalf a' b Λ Φ) := by
  obtain ⟨-, k, hk, hinv, hlat⟩ := hΦ
  refine ⟨fun t ht => ?_, k, hk, fun u hu hhu t => ?_, fun t ht => ?_⟩
  · rw [restrictHalf_apply] at ht
    by_contra h
    exact ht (by rw [if_neg h, mul_zero])
  · rw [isHalf_iff'] at hhu
    simp only [restrictHalf_apply]
    have e1 : a' • (t + k • u) = a' • t + k • (a' • u) := by rw [smul_add, smul_comm]
    have e2 : (a' + b) • (k • u) = k • u := by rw [smul_comm, hhu]
    rw [e1, hinv _ (hΛ a' ha' u hu) (isHalf_smul ha' u), halfInd_smul_congr hb Λ (z := t + k • u) (t := t) (by
      rw [smul_add, add_sub_cancel_left, smul_comm]
      exact Λ.nsmul_mem (hΛ b hb u hu) k)]
    simp only [isHalf_add_iff e2]
  · rw [restrictHalf_apply] at ht
    have h1 : Φ (a' • t) ≠ 0 := fun h => ht (by rw [h, zero_mul, zero_mul])
    have h2 : halfInd b Λ (b • t) ≠ 0 := fun h => ht (by rw [h, mul_zero, zero_mul])
    have h3 : IsHalf (a' + b) t := by
      by_contra h
      exact ht (by rw [if_neg h, mul_zero])
    have h2' : b • t ∈ Λ := by
      unfold halfInd at h2
      by_contra h
      exact h2 (if_neg fun h' => h h'.1)
    rw [isHalf_iff', add_smul] at h3
    rw [← h3, smul_add]
    exact Λ.add_mem (hlat _ h1) (Λ.nsmul_mem h2' k)

end RestrictHalfModel


open RestrictHalfModel in
theorem isPlaceModel_comp_restrictHalf : ∀ {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ} {a' b : AE D} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}, a' * a' = a' → b * b = b → a' * b = 0 → (∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a' + b) Λ 1 f₀ T₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a' Λ 1 f₀ (T₀ ∘ₗ restrictHalf a' b Λ) := by
  intro D S T ψ Λ f₀ a' b T₀ ha' hb hab hΛ hT
  have hsb : ∀ Φ, IsSBHalf a' Λ Φ → IsSBHalf (a' + b) Λ (restrictHalf a' b Λ Φ) :=
    fun Φ hΦ => isSBHalf_restrictHalf ha' hb hΛ hΦ
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · obtain ⟨hbx, hax⟩ := smul_of_half hab hx
    have hxa : IsHalf (a' + b) x := (isHalf_iff' _ _).2 hax
    have e : restrictHalf a' b Λ (fun t => Φ (t + x)) = fun t => restrictHalf a' b Λ Φ (t + x) := by
      funext z
      simp only [restrictHalf_apply]
      rw [smul_add, (isHalf_iff' _ _).1 hx, smul_add b, hbx, add_zero, isHalf_add_iff hax]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.trans _ (hsb Φ hΦ) x hxa
  · have hy' : IsHalf (cA D (a' + b)) y := by
      rw [isHalf_iff'] at hy ⊢
      rw [map_add (f := _), add_smul, hy, ← hy, smul_smul, ← map_mul, mul_comm, hab, map_zero, zero_smul, add_zero]
    have e : restrictHalf a' b Λ (fun t => ψ (symplO S T t y) * Φ t) =
        fun t => ψ (symplO S T t y) * restrictHalf a' b Λ Φ t := by
      funext z
      simp only [restrictHalf_apply]
      rw [GlobalTheory.SplitScalar.symplO_smul, (isHalf_iff' _ _).1 hy]
      ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.modul _ (hsb Φ hΦ) y hy'
  · have e : restrictHalf a' b Λ ((1 : ℂ) • halfInd a' Λ) = (1 : ℂ) • halfInd (a' + b) Λ := by
      funext t
      simp only [one_smul, restrictHalf_apply]
      unfold halfInd
      have i1 := isHalf_smul ha' t
      have i2 := isHalf_smul hb t
      by_cases hat : IsHalf (a' + b) t
      · have ht' : t = a' • t + b • t := by rw [← add_smul]; exact ((isHalf_iff' _ _).1 hat).symm
        by_cases ht : t ∈ Λ
        · rw [if_pos ⟨hΛ a' ha' t ht, i1⟩, if_pos ⟨hΛ b hb t ht, i2⟩, if_pos hat, if_pos ⟨ht, hat⟩]
          ring
        · rw [if_neg (show ¬ (t ∈ Λ ∧ IsHalf (a' + b) t) from fun h => ht h.1), if_pos hat, mul_one]
          by_cases h1 : a' • t ∈ Λ
          · rw [if_neg (show ¬ (b • t ∈ Λ ∧ IsHalf b (b • t)) from fun h => ht (by rw [ht']; exact Λ.add_mem h1 h.1)),
              mul_zero]
          · rw [if_neg (show ¬ (a' • t ∈ Λ ∧ IsHalf a' (a' • t)) from fun h => h1 h.1), zero_mul]
      · rw [if_neg hat, mul_zero, if_neg fun h => hat h.2]
    rw [LinearMap.comp_apply, e]
    exact hT.vac

end GlobalTheory.ExportSeries

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SubLevel

open Formalism.IndefR.Bridge GlobalTheory.CharChange

section Gen

variable {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G)

def dcRel (J' : Subgroup G) : Setoid G where
  r h h' := ∃ (γ : Γ) (k : J'), h' = ι γ * h * (k : G)
  iseqv := {
    refl := fun h => ⟨1, 1, by simp⟩
    symm := fun {h h'} ⟨γ, k, e⟩ => ⟨γ⁻¹, k⁻¹, by rw [e, map_inv, Subgroup.coe_inv]; group⟩
    trans := fun {h h' h''} ⟨γ, k, e⟩ ⟨γ₂, k₂, e₂⟩ =>
      ⟨γ₂ * γ, k * k₂, by rw [e₂, e, map_mul, Subgroup.coe_mul]; group⟩ }

theorem stab_mono_mem {J J' : Subgroup G} (hJ : J' ≤ J) {y k : G} (hk : k ∈ J) {g : Γ}
    (hg : g ∈ stab ι J' (y * k)) : g ∈ stab ι J y := by
  rw [mem_stab ι] at hg ⊢
  have h1 : (y * k)⁻¹ * ι g * (y * k) ∈ J := hJ hg
  have e : y⁻¹ * ι g * y = k * ((y * k)⁻¹ * ι g * (y * k)) * k⁻¹ := by group
  rw [e]
  exact J.mul_mem (J.mul_mem hk h1) (J.inv_mem hk)

end Gen

section Main

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable (P : ClassPres ι S σ ρ J χ) (J' : Subgroup G)

def yN (c : Quotient (dcRel ι J')) : G := P.y (P.decC c.out) * (P.decK c.out : G)

theorem yN_rel (c : Quotient (dcRel ι J')) : (dcRel ι J').r (yN P J' c) c.out := by
  show ∃ (γ : Γ) (k : J'), c.out = ι γ * yN P J' c * (k : G)
  refine ⟨P.decG c.out, 1, ?_⟩
  show c.out = ι (P.decG c.out) * (P.y (P.decC c.out) * (P.decK c.out : G)) * ((1 : J') : G)
  rw [Subgroup.coe_one, mul_one, ← mul_assoc]
  exact P.dec_spec c.out

theorem mk_yN (c : Quotient (dcRel ι J')) : Quotient.mk (dcRel ι J') (yN P J' c) = c :=
  (Quotient.sound (yN_rel P J' c)).trans (Quotient.out_eq c)

theorem reps_new : IsReps ι J' (yN P J') := by
  intro h
  refine ⟨Quotient.mk (dcRel ι J') h, ?_, ?_⟩
  · exact Quotient.exact (mk_yN P J' (Quotient.mk (dcRel ι J') h))
  · rintro i ⟨γ, k, e⟩
    have hr : (dcRel ι J').r (yN P J' i) h := ⟨γ, k, e⟩
    exact (mk_yN P J' i).symm.trans (Quotient.sound hr)

theorem stabN_finite (hJ : J' ≤ J) (c : Quotient (dcRel ι J')) : Finite (stab ι J' (yN P J' c)) := by
  haveI : Finite (stab ι J (P.y (P.decC c.out))) := Finite.of_equiv _ (P.stabI (P.decC c.out)).toEquiv
  refine Finite.of_injective
    (fun g : stab ι J' (yN P J' c) =>
      (⟨(g : Γ), stab_mono_mem ι hJ (P.decK c.out).2 g.2⟩ : stab ι J (P.y (P.decC c.out)))) ?_
  intro a b hab
  have hv := congrArg Subtype.val hab
  exact Subtype.ext hv

include P in
theorem cl_finite (hfi : (J'.subgroupOf J).FiniteIndex) : Finite (Quotient (dcRel ι J')) := by
  haveI := hfi
  refine Finite.of_surjective
    (fun p : S.Cl × (J ⧸ J'.subgroupOf J) => Quotient.mk (dcRel ι J') (P.y p.1 * ((p.2.out : J) : G))) ?_
  intro c
  obtain ⟨d, γ, k, e⟩ : ∃ (d : S.Cl) (γ : Γ) (k : J), c.out = ι γ * P.y d * (k : G) :=
    ⟨_, _, _, P.dec_spec c.out⟩
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (s := J'.subgroupOf J) k
  have hjJ' : ((j : J) : G) ∈ J' := Subgroup.mem_subgroupOf.1 j.2
  refine ⟨(d, (QuotientGroup.mk k : J ⧸ J'.subgroupOf J)), ?_⟩
  show Quotient.mk (dcRel ι J') (P.y d * (((QuotientGroup.mk k : J ⧸ J'.subgroupOf J).out : J) : G)) = c
  rw [hj]
  have hr : (dcRel ι J').r (P.y d * ((k * (j : J) : J) : G)) c.out := by
    refine ⟨γ, ⟨((j : J) : G)⁻¹, J'.inv_mem hjJ'⟩, ?_⟩
    show c.out = ι γ * (P.y d * ((k : G) * ((j : J) : G))) * ((j : J) : G)⁻¹
    rw [e]
    group
  exact (Quotient.sound hr).trans (Quotient.out_eq c)

variable (χ' : J' →* ℂˣ) (hχ' : ∀ k, ∃ a : K, σ a = ((χ' k : ℂˣ) : ℂ))
  (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x))

def rhoG (y : G) (g : stab ι J' y) (x : S.V) : W :=
  (χ' (stabK ι g) : ℂ) • ρ (g : Γ) (P.coef x)

include hχ' hρ in
theorem rhoG_rg (y : G) (g : stab ι J' y) (x : S.V) : InRg P (rhoG P J' χ' y g x) := by
  obtain ⟨x', hx'⟩ := hρ (g : Γ) x
  obtain ⟨a, ha⟩ := hχ' (stabK ι g)
  refine ⟨a • x', ?_⟩
  rw [map_smulₛₗ, hx', ha]
  rfl

def rhoGE (y : G) (g : stab ι J' y) : Module.End K S.V where
  toFun x := cinv P (rhoG P J' χ' y g x)
  map_add' x x' := by
    apply coef_injective P
    rw [map_add (f := _), coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _), coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _),
      coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _)]
    simp only [rhoG, map_add (f := _), smul_add]
  map_smul' b x := by
    apply coef_injective P
    rw [map_smulₛₗ, coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _), coef_cinv P (rhoG_rg P J' χ' hχ' hρ _ _ _)]
    simp only [rhoG, map_smulₛₗ, RingHom.id_apply, map_smul]
    rw [smul_comm]

theorem coef_rhoGE (y : G) (g : stab ι J' y) (x : S.V) :
    P.coef (rhoGE P J' χ' hχ' hρ y g x) = rhoG P J' χ' y g x :=
  coef_cinv P (rhoG_rg P J' χ' hχ' hρ y g x)

def rhoGN (y : G) : stab ι J' y →* Module.End K S.V where
  toFun := rhoGE P J' χ' hχ' hρ y
  map_one' := by
    apply LinearMap.ext; intro x
    apply coef_injective P
    rw [coef_rhoGE]
    simp [rhoG, stabK_one']
  map_mul' g g' := by
    apply LinearMap.ext; intro x
    apply coef_injective P
    rw [Module.End.mul_apply, coef_rhoGE, coef_rhoGE]
    simp only [rhoG, coef_rhoGE, map_mul, stabK_mul', Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, map_smul,
      smul_smul, mul_comm]

end Main

end GlobalTheory.SubLevel

namespace GlobalTheory

open Formalism.IndefR.Bridge GlobalTheory.SubLevel

theorem classPres_subLevel : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ) (J' : Subgroup G), J' ≤ J → (J'.subgroupOf J).FiniteIndex → ∀ χ' : J' →* ℂˣ, (∀ k, ∃ a : K, σ a = ((χ' k : ℂˣ) : ℂ)) → (∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) → ∃ (Cl : Type) (fC : Fintype Cl) (π : Cl → S.Cl) (k : Cl → J) (Gam : Cl → Type) (gG : ∀ c, Group (Gam c)) (fG : ∀ c, Fintype (Gam c)) (ρ' : ∀ c, Gam c →* Module.End K S.V) (P' : Bridge.ClassPres ι ({ S with Cl := Cl, finCl := fC, Gam := Gam, grpGam := gG, finGam := fG, ρ := ρ', Nab := fun c => S.Nab (π c), Del := fun c => S.Del (π c) } : CSD K) σ ρ J' χ'), (∀ c : Cl, P'.y c = P.y (π c) * (k c : G)) ∧ P'.coef = P.coef := by
  intro G Γ _ _ ι W _ _ K _ _ _ σ S ρ J χ P J' hJ hfi χ' hχ' hρ
  haveI : Finite (Quotient (SubLevel.dcRel ι J')) := SubLevel.cl_finite P J' hfi
  letI fC : Fintype (Quotient (SubLevel.dcRel ι J')) := Fintype.ofFinite _
  haveI hfS : ∀ c, Finite (stab ι J' (SubLevel.yN P J' c)) := fun c => SubLevel.stabN_finite P J' hJ c
  letI fG : ∀ c, Fintype (stab ι J' (SubLevel.yN P J' c)) := fun c => Fintype.ofFinite _
  exact ⟨Quotient (SubLevel.dcRel ι J'), fC, fun c => P.decC c.out, fun c => P.decK c.out,
    fun c => stab ι J' (SubLevel.yN P J' c), fun c => inferInstance, fG,
    fun c => SubLevel.rhoGN P J' χ' hχ' hρ (SubLevel.yN P J' c),
    { y := SubLevel.yN P J'
      reps := SubLevel.reps_new P J'
      stabI := fun c => MulEquiv.refl _
      coef := P.coef
      coef_li := P.coef_li
      coef_span := P.coef_span
      coef_pair := P.coef_pair
      coef_act := fun c g x => SubLevel.coef_rhoGE P J' χ' hχ' hρ (SubLevel.yN P J' c) g x },
    fun c => rfl, rfl⟩

end GlobalTheory
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PresHecke

open Formalism.IndefR.Bridge GlobalTheory.CharChange

section Raw

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable {I : Type} {inR : I → Prop} {isT isLoc : I → G → Prop}

theorem keepsDcRaw (P : ClassPres ι S σ ρ J χ) (hx : I → G) (hA : I → Finset G)
    (hok : ∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ IsDC J (hx i) (hA i))
    (hloc : ∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧
      (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : J, (k : G) ∈ Lc → χ k = 1)
    (i : I) (hi : inR i) : Keeps P (dcL (W := W) (hA i)) := by
  obtain ⟨Lc, hL1, hL2, hL3⟩ := hloc i hi
  intro F hF hv
  refine ⟨dcOp_mem (hok i hi).2.2 Lc (fun a ha => hL1 _ ((hok i hi).2.1 a ha)) hL2 hL3 hF, fun h => ?_⟩
  exact InRg.sum _ _ fun a _ => hv _


open Classical in
def opRaw (P : ClassPres ι S σ ρ J χ) (hχ : ∀ k, ∃ b : K, σ b = (χ k : ℂ))
    (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) (hx : I → G) (hA : I → Finset G)
    (hok : ∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ IsDC J (hx i) (hA i))
    (hloc : ∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧
      (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : J, (k : G) ∈ Lc → χ k = 1)
    (one : I → Prop) (i : I) : Module.End K S.Forms :=
  if hi : inR i then trE P hχ hρ (keepsDcRaw P hx hA hok hloc i hi) else if one i then 1 else 0

def heckeRaw (P : ClassPres ι S σ ρ J χ) (hχ : ∀ k, ∃ b : K, σ b = (χ k : ℂ))
    (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) (hx : I → G) (hA : I → Finset G)
    (hok : ∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ IsDC J (hx i) (hA i))
    (hloc : ∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧
      (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : J, (k : G) ∈ Lc → χ k = 1)
    (one : I → Prop) : HeckeTie ι P (opRaw P hχ hρ hx hA hok hloc one) inR isT isLoc where
  hx := hx
  hA := hA
  hx_ok i hi := (hok i hi).1
  hA_loc i hi := (hok i hi).2.1
  chi_loc i hi k hk := by
    obtain ⟨Lc, hL1, _, hL3⟩ := hloc i hi
    exact hL3 k (hL1 _ hk)
  hDC i hi := (hok i hi).2.2
  op_eq i hi f := by
    unfold opRaw
    rw [dite_eq_left hi, ext_trE]
    rfl

end Raw

end GlobalTheory.PresHecke

namespace GlobalTheory

open Formalism.IndefR.Bridge GlobalTheory.CharChange GlobalTheory.PresHecke

theorem sideReal_ofPres : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {I : Type} (c : Bridge.CoefDatG Γ) (l : Bridge.LevDatG G) (isT isLoc : I → G → Prop) {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) {G0 : Type} [Group G0] (inR : I → Prop) (P : Bridge.ClassPres ι S σ c.ρ l.J l.χ), (∀ q, ∃ a : K, σ a = ((l.ch q : ℂˣ) : ℂ)) → (∀ γ x, ∃ x', P.coef x' = c.ρ γ (P.coef x)) → ∀ (red : l.Q →* G0), Function.Surjective red → (∀ q : l.Q, red q = 1 ↔ (q : G) ∈ l.J) → ∀ (hx : I → G) (hA : I → Finset G), (∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ Bridge.IsDC l.J (hx i) (hA i)) → (∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧ (∀ k ∈ l.J, ∃ k₁ ∈ l.J, ∃ k₂ ∈ l.J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧ ∀ k : l.J, (k : G) ∈ Lc → l.χ k = 1) → ∀ one : I → Prop, ∃ (act : Representation K G0 S.Forms) (op : I → Module.End K S.Forms) (B : Bridge.SideRealG ι ⟨c, l, isT, isLoc⟩ σ S act op inR), B.pres = P ∧ B.act_tie.red = red ∧ ∀ i, ¬ inR i → (one i → op i = 1) ∧ (¬ one i → op i = 0) := by
  intro G Γ _ _ ι I c l isT isLoc K _ _ _ σ S G0 _ inR P hσ hρ red hsurj hker hx hA hok hloc one
  have hχ : ∀ k : l.J, ∃ b : K, σ b = (l.χ k : ℂ) := fun k => by rw [← l.ch_J]; exact hσ _
  exact ⟨actNew P hχ hρ red hsurj l.J_le hker l.ch l.ch_J hσ,
    opRaw P hχ hρ hx hA hok hloc one,
    ⟨P, actTieNew P hχ hρ red hsurj l.J_le hker l.ch l.ch_J hσ, heckeRaw P hχ hρ hx hA hok hloc one⟩,
    rfl, rfl, fun i hi => ⟨fun ho => by simp [opRaw, hi, ho], fun ho => by simp [opRaw, hi, ho]⟩⟩

end GlobalTheory
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

namespace GlobalTheory.Per.FontaineBound

theorem dcris_finite_le_of_tied {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) :
    Module.Finite ↥LL.1 (Dcris (P.PD K) ρ) ∧
      finrank ↥LL.1 (Dcris (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V := by
  have := isDomain_cris (P.PD K) (isField_of_tied T)
  have := (P.PD K).finK₀
  have := LL.2
  refine finite_finrank_le (P.PD K).actB (fun b b' hb h => GlobalTheory.T.ratio_invariant_in_K0 l P AI T K b' b hb fun g hg => ?_) ρ
  have h1 := h ⟨g, hg⟩
  rw [P.PD_actB, P.PD_actB] at h1
  rw [mul_comm, h1, mul_comm]

theorem fontaineLe_of_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ K LL : FinExt l, FontaineLe (P.PD K) ↥LL.1 ∧
      ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
        [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
        FiniteDimensional ↥LL.1 ↥(Dcris (P.PD K) ρ) :=
  fun _ _ _ _ T K LL => ⟨fun V _ _ _ _ _ ρ => (dcris_finite_le_of_tied T K LL V ρ).2,
    fun V _ _ _ _ _ ρ => (dcris_finite_le_of_tied T K LL V ρ).1⟩

end GlobalTheory.Per.FontaineBound
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

theorem _root_.GlobalTheory.T.directSum_deRham_crystalline_jumps_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (e : V ≃ₗ[↥LL.1] (V₁ × V₂)), (∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2)) → (IsDR (P.PD K) ρ ↔ IsDR (P.PD K) ρ₁ ∧ IsDR (P.PD K) ρ₂) ∧ (IsCrys (P.PD K) ρ ↔ IsCrys (P.PD K) ρ₁ ∧ IsCrys (P.PD K) ρ₂) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) ρ τ a = multV (P.PD K) ρ₁ τ a + multV (P.PD K) ρ₂ τ a := by
  first | exact @GlobalTheory.Per.DirectSumHT.directSum_hodgeTate | exact GlobalTheory.Per.DirectSumHT.directSum_hodgeTate | (intros; apply GlobalTheory.Per.DirectSumHT.directSum_hodgeTate <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isDoubleCoset_of_smaller_level_same_local : ∀ {G : Type} [Group G] (J J' Lc : Subgroup G) (x : G) (A : Finset G), J' ≤ J → J ⊓ Lc ≤ J' → (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ y ∈ Lc, Commute k₂ y) → x ∈ Lc → (∀ a ∈ A, a ∈ Lc) → Bridge.IsDC J x A → Bridge.IsDC J' x A := by
  first | exact @GlobalTheory.isDC_of_smaller_level_same_local | exact GlobalTheory.isDC_of_smaller_level_same_local | (intros; apply GlobalTheory.isDC_of_smaller_level_same_local <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

theorem _root_.GlobalTheory.T.integral_tate_H2_top : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.admH2 i := by
  first | exact @GlobalTheory.IntTateTop.admH2_of_duality | exact GlobalTheory.IntTateTop.admH2_of_duality | (intros; apply GlobalTheory.IntTateTop.admH2_of_duality <;> assumption)
end
