module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle307
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle187
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace UpperTheory.GivenInt

open GlobalTheory.StepData ValuativeRel

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem tame_int {μ : kˣ →* ℂˣ} (hμ : IsTame μ) (x : kˣ) (hx : valuation k (x : k) = 1) :
    IsIntegral ℤ ((μ x : ℂˣ) : ℂ) := by
  obtain ⟨p, hp⟩ := ValuativeRel.valuation_surjective (K := k) (uniformizer k : ValueGroupWithZero k)
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact uniformizer_ne_zero hp.symm
  refine UpperTheory.isIntegral_unitChar_of_conductor_le (Units.mk0 p hp0) 1 μ hp (fun y hy => hμ y ?_) x hx
  refine lt_of_le_of_lt hy.2 ?_
  rw [pow_one, Units.val_mk0, hp]
  exact uniformizer_lt_one

private theorem tame_det_int {a : Type*} [Fintype a] [DecidableEq a] {μ : kˣ →* ℂˣ} (hμ : IsTame μ) {g : GL a k}
    (hg : g ∈ KO k a) : IsIntegral ℤ ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) :=
  tame_int hμ _ (valuation_det_of_mem_KO hg)

private theorem tame_det_inv_int {a : Type*} [Fintype a] [DecidableEq a] {μ : kˣ →* ℂˣ} (hμ : IsTame μ) {g : GL a k}
    (hg : g ∈ KO k a) : IsIntegral ℤ (((μ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) := by
  rw [← map_inv, ← map_inv]
  exact tame_det_int hμ (inv_mem hg)

private theorem lam_step_int {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] (P : TypeDatum k a)
    (μ : kˣ →* ℂˣ) (hμ : IsTame μ) (hP : ∀ g, IsIntegral ℤ ((P.lam g : ℂˣ) : ℂ))
    (h : (P.step t μ hμ).J) : IsIntegral ℤ (((P.step t μ hμ).lam h : ℂˣ) : ℂ) := by
  rw [P.step_lam μ hμ h (P.corner h) (P.corner_val h), Units.val_mul, Units.val_mul]
  exact ((hP _).mul (tame_det_inv_int hμ (P.le_KO (P.corner h).2))).mul (tame_det_int hμ h.2.1)

private theorem lam_iter_int {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hP : ∀ g, IsIntegral ℤ ((P.lam g : ℂˣ) : ℂ))
    (j : ℕ) : ∀ g, IsIntegral ℤ (((P.iter t μ hμ j).lam g : ℂˣ) : ℂ) := by
  induction j with
  | zero => exact fun g => hP _
  | succ j ih => exact fun g => lam_step_int _ _ (hμ _) ih _

private theorem Phi_int {a t : Type*} [Fintype a] [DecidableEq a] (P : TypeDatum k a) (μ : kˣ →* ℂˣ) (hμ : IsTame μ)
    (hP : ∀ g, IsIntegral ℤ ((P.lam g : ℂˣ) : ℂ)) (x : Matrix (a ⊕ t) a k) :
    IsIntegral ℤ (P.Phi t μ x) := by
  by_cases h : P.Phi t μ x = 0
  · rw [h]; exact isIntegral_zero
  · obtain ⟨⟨g, hg, e⟩, h2⟩ := (P.Phi_ne_zero_iff μ).1 h
    rw [P.Phi_of_mem μ ⟨g, hg⟩ e h2]
    exact (hP _).mul (tame_det_inv_int hμ (P.le_KO hg))

private theorem parPhi_int {r s s' : Type*} [Fintype r] [DecidableEq r] (δ : kˣ →* ℂˣ)
    (hδ : ∀ x, IsIntegral ℤ ((δ x : ℂˣ) : ℂ)) (x : Matrix (r ⊕ s) (r ⊕ s') k) : IsIntegral ℤ (parPhi δ x) := by
  by_cases h : parPhi δ x = 0
  · rw [h]; exact isIntegral_zero
  · obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).1 h
    rw [parPhi_of_mem δ hg e h21 h12 h22, ← map_inv]
    exact hδ _

private theorem indicator_int {X : Type*} (S : Set X) (x : X) : IsIntegral ℤ (S.indicator (1 : X → ℂ) x) := by
  classical
  rw [Set.indicator_apply]
  split_ifs
  · exact isIntegral_one
  · exact isIntegral_zero

end Local

section Global

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (w : Pl D.host.E)
variable {t : T} (hxi : ∀ x, IsIntegral ℤ ((L.xiH t).loc w x : ℂ))
include hxi

private theorem stepFn_int (j : ℕ) (x) : IsIntegral ℤ (stepFn L t w j x) := by
  unfold stepFn
  split_ifs
  · exact Phi_int _ _ (isTame_muBase w _) (lam_iter_int _ _ _ (fun _ => isIntegral_one) j) _
  · refine parPhi_int _ (fun y => ?_) _
    rw [MonoidHom.inv_apply, ← map_inv]
    exact hxi _
  · exact indicator_int _ _

private theorem givenDatum_int (B : Frames G) (Φ : G.Datum) (b : Edge) (x) :
    IsIntegral ℤ (givenDatum t w B Φ b x) := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩
  · rcases i with _ | i
    · simp only [givenDatum]
      exact stepFn_int w hxi _ _
    · simp only [givenDatum]
      exact isIntegral_zero
  · rcases j with _ | j
    · simp only [givenDatum]
      split_ifs
      · exact indicator_int _ _
      · exact isIntegral_zero
    · simp only [givenDatum]
      exact isIntegral_zero

end Global

end UpperTheory.GivenInt

theorem UpperTheory.isIntegral_localGrid_tensor_of_levelChar :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E) (z : (locGrid G t w).Args), IsIntegral ℤ ((givenStage t w B Φ).tensor z) := by
  intro D T L sc G μ₀ hL B t Φ w z
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have hxi : ∀ x, IsIntegral ℤ ((L.xiH t).loc w x : ℂ) := fun x => by
    have h1 : ((L.xiH t) ^ n).loc w x = 1 := by rw [show (L.xiH t) ^ n = 1 from ho]; rfl
    have h2 : ((L.xiH t).loc w x) ^ n = 1 := h1
    have h3 : ((L.xiH t).loc w x : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
    exact IsIntegral.of_pow hn (h3 ▸ isIntegral_one)
  show ((GlobalTheory.SplitFlip.givenPath D.R.m).map fun b => givenDatum t w B Φ b (z b)).prod ∈ integralClosure ℤ ℂ
  refine list_prod_mem fun y hy => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
  exact UpperTheory.GivenInt.givenDatum_int w hxi B Φ b _
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem UpperTheory.finiteDimensional_automorphicForms_unitary_of_type_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : infU E n → Module.End ℂ S)
        (K : Subgroup (finU (E := E) (n := n))), IsOpen (K : Set (finU (E := E) (n := n))) → ∀ M : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)),
        (∀ f ∈ M, (∀ v, ∀ γ ∈ ratU E n, ∀ g, f v (γ * g) = f v g) ∧ (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) ∧
          ∀ k ∈ K, ∀ v, RU E n (k : finU (E := E) (n := n)) (f v) = f v) → FiniteDimensional ℂ M := by
  intro E _ _ _ n S _ _ _ ρ K hK M hM
  obtain ⟨R, hR⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n K hK
  let T : M →ₗ[ℂ] (R → Module.Dual ℂ S) :=
    { toFun := fun f s => (LinearMap.proj (R := ℂ) (φ := fun _ : UA E n => ℂ) (s : UA E n)).comp f.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have h0 : ∀ s ∈ R, ∀ v, f.1 v s = 0 := fun s hs v =>
      LinearMap.congr_fun (congrFun hf ⟨s, hs⟩) v
    obtain ⟨h1, h2, h3⟩ := hM f.1 f.2
    refine Subtype.ext (LinearMap.ext fun v => funext fun g => ?_)
    obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hR g
    have e1 : f.1 v (γ * s * x * (k : UA E n)) = f.1 v (γ * s * x) := congrFun (h3 k hk v) (γ * s * x)
    have e2 : f.1 (ρ ⟨x, hx⟩ v) s = f.1 v (s * x) := congrFun (h2 ⟨x, hx⟩ v) s
    show f.1 v (γ * s * x * (k : UA E n)) = 0
    rw [e1, mul_assoc γ s x, h1 v γ hγ, ← e2, h0 s hs]
  exact Module.Finite.of_injective T hT
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

private theorem UpperTheory.exists_infinite_unitary_lift {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]
    (emb : ι → (E →+* ℂ)) (hinj : Function.Injective (fun τ => InfinitePlace.mk (emb τ)))
    (g : ι → GL (Fin n) ℂ)
    (hg : ∀ v, (g v : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ y : infU E n, (MonoidHom.pi fun τ => cEmb (E := E) (n := n) (emb τ)) y.1 = g := by
  classical
  let J : Subgroup (ι → GL (Fin n) ℂ) :=
    ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (emb τ)).comp (infU E n).subtype).range
  let Hs : ι → Subgroup (GL (Fin n) ℂ) := fun _ => (GlobalTheory.Branching.unitaryIncl n).range
  have hle : Subgroup.pi Set.univ Hs ≤ J := by
    rw [Subgroup.pi_le_iff]
    intro v
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n (emb v)
    let x := e.symm u
    have hx := Subgroup.mem_inf.1 x.2
    refine ⟨⟨x.1, hx.1⟩, ?_⟩
    funext v'
    by_cases h : v' = v
    · subst h
      change cEmb (emb v') x.1 = _
      rw [← he, e.apply_symm_apply]
      simp
    · have h5 : x.1 ∈ (cEmb (E := E) (n := n) (emb v')).ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 (emb v')) (fun h' => h (hinj h'))
      change cEmb (emb v') x.1 = _
      rw [MonoidHom.mem_ker.1 h5]
      simp [h]
  obtain ⟨y, hy⟩ : g ∈ J := hle fun v _ => ⟨⟨(g v).val, hg v⟩, Units.ext rfl⟩
  exact ⟨y, hy⟩

theorem UpperTheory.span_highestWeightRep_unitaryGroup_realPoints_image_eq_top :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι] (emb : ι → (E →+* ℂ)), Function.Injective (fun τ => InfinitePlace.mk (emb τ)) →
        ∀ (lam : ι → DomWeight n) [Nontrivial (Formalism.L2.DIV.VV ℂ lam)],
        Submodule.span ℂ (Set.range ((Formalism.L2.DIV.rhoK (K := ℂ) lam).comp
          ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (emb τ)).comp (infU E n).subtype))) = ⊤ := by
  intro E _ _ _ n ι _ emb hinj lam _
  haveI : ∀ v, Finite (Formalism.GradedWeylDivisibility.ssIdx n n (lam v).natW) := fun _ => (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  haveI : FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam) := Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ lam)
  exact GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ _ ((GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨inferInstance, fun U hU =>
    GlobalTheory.CoefIrred.vv_irreducible_unitary ι n lam U fun g hg x hx => by
      obtain ⟨y, rfl⟩ := UpperTheory.exists_infinite_unitary_lift emb hinj g hg
      exact hU y x hx⟩)
end
