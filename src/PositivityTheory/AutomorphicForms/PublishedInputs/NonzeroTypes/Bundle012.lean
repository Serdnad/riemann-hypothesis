module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle425
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle055
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle382
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle035
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorVector

@[expose] public section

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} (G : Grp k n)

theorem exists_equiv_of_map_eq {β : Type*} {h N : ℕ} (x : Fin h → β) (F : Fin N → β)
    (hx : (Finset.univ.val.map x : Multiset β) = Finset.univ.val.map F) :
    ∃ σ : Fin h ≃ Fin N, ∀ a, x a = F (σ a) := by
  have hcount : ∀ {M : ℕ} (f : Fin M → β) (c : β),
      Fintype.card {a // f a = c} = Multiset.count c (Finset.univ.val.map f) := by
    intro M f c
    rw [Multiset.count_map, Fintype.card_subtype]
    simp only [Finset.card, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr fun a _ => eq_comm
  have hcard : ∀ c, Fintype.card {a // x a = c} = Fintype.card {b // F b = c} := fun c => by
    rw [hcount, hcount, hx]
  exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c),
    fun a => (Equiv.ofFiberEquiv_map _ a).symm⟩

theorem sum_map_univ {β : Type*} {s N : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N)
    (f : ∀ a, Fin (d a) → β) (F : Fin N → β) (hF : ∀ a j, F (e ⟨a, j⟩) = f a j) :
    (∑ a, (Finset.univ.val.map (f a) : Multiset β)) = Finset.univ.val.map F := by
  have h1 : ∀ {ι : Type} [Fintype ι] (g : ι → β),
      (Finset.univ.val.map g : Multiset β) = ∑ i, ({g i} : Multiset β) := by
    intro ι _ g
    rw [← Multiset.sum_map_singleton (Finset.univ.val.map g), Multiset.map_map]
    rfl
  rw [h1 F, ← Equiv.sum_comp e, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [h1]
  exact Finset.sum_congr rfl fun j _ => by rw [hF]

theorem deltaHalf_inv_apply (g : Levi k fun a : Fin G.s => Fin (G.d a)) :
    ((((deltaHalf k fun a : Fin G.s => Fin (G.d a))⁻¹ g : ℂˣ)) : ℂ) =
      ∏ a, ((absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))
        (GeneralLinearGroup.det (g a)) : ℂˣ) : ℂ) := by
  rw [MonoidHom.inv_apply, deltaHalf_apply, ← Finset.prod_inv_distrib, Units.coe_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [absPow_neg]
  rfl

theorem piTensor_twD_eq {Y : Fin G.s → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)) :
    piTensor (G.twD τ) = twist (piTensor τ) (deltaHalf k fun a : Fin G.s => Fin (G.d a))⁻¹ := by
  refine MonoidHom.ext fun g => ?_
  apply PiTensorProduct.ext
  refine MultilinearMap.ext fun x => ?_
  simp only [LinearMap.compMultilinearMap_apply, piTensor_tprod, twist_apply, Grp.twD, detChar_apply]
  rw [MultilinearMap.map_smul_univ, deltaHalf_inv_apply]
  simp only [RingHom.id_apply]

theorem isIrreducible_piTensor_twD (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {Y : Fin G.s → Type}
    [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a))
    (hs : ∀ a, IsSmooth (G.twD τ a)) (hi : ∀ a, (G.twD τ a).IsIrreducible) :
    (piTensor (G.twD τ)).IsIrreducible := by
  refine GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ hi fun a => ?_
  exact GlobalTheory.SchurAdm.schur_admissible _ (KO k (Fin (G.d a))) GlobalTheory.SplitFlip.isOpen_KO
    GlobalTheory.SplitFlip.isCompact_KO _ _ (hi a) ((hBZ k).1 (Fin (G.d a)) _ _ (hs a) (hi a))

theorem hasSupport_twD {Y : Fin G.s → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)) (ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ)
    (hν : ∀ a j, IsSmoothChar (ν a j))
    (hc : ∀ a, IsCuspSupport (τ a) (fun _ : Fin (G.d a) => 1) (fun j => detRep (Fin 1) (ν a j))) (a : Fin G.s)
    (hsm : ∀ j, IsSmoothChar (ν a j * absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2)))) :
    HasSupport (G.twD τ a) (Finset.univ.val.map fun j => IrrGL.ofChar _ (hsm j)) := by
  have hψ : IsSmoothChar (absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))) :=
    isSmoothChar_absPow _
  have h2 := (hasSupport_of_isCuspSupport (hc a)).tw _ hψ
  rw [Multiset.map_map] at h2
  have key : (Finset.univ.val.map fun j => IrrGL.ofChar _ (hsm j)) =
      Finset.univ.val.map ((fun y : IrrGL (k := k) => y.tw _ hψ) ∘ fun j =>
        IrrGL.of (detRep (Fin 1) (ν a j)) ((hc a).2.1 j).2.2.1 ((hc a).2.1 j).2.1) :=
    Multiset.map_congr rfl fun j _ => (IrrGL.tw_ofChar (ν a j) _ (hν a j) hψ).symm
  rw [key]
  exact h2

end P_spSupp

open P_spSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ}

theorem step_spSupp (G : Grp k n) : G.SpecialSupportProp := by
  intro hOrd hLit V _ _ π hπs hπi Y _ _ τ hτs hτi ν hν hcs hjac
  have hG := hLit.loc.geo
  have hZ := hLit.loc.zel
  have hBZ := hLit.loc.bz
  have hs' : ∀ a, IsSmooth (G.twD τ a) := fun a =>
    isSmooth_twist (hτs a) (isSmoothChar_absPow _).detChar
  have hi' : ∀ a, (G.twD τ a).IsIrreducible := fun a => GlobalTheory.LocGL.isIrreducible_twist (hτi a) _
  have hτJ : (piTensor (G.twD τ)).IsIrreducible := isIrreducible_piTensor_twD G hBZ τ hs' hi'
  have hJs : IsSubquotient (piTensor (G.twD τ)) (jac G.e π) := by
    rw [piTensor_twD_eq]
    exact GlobalTheory.LocGL.isSubquotient_twist hjac _

  obtain ⟨s, hsπ⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport hZ (IrrGL.of π hπs hπi)
  have hsπ' : HasSupport π s := hsπ.of_equiv (IrrGL.equivOf π hπs hπi).symm

  have hy : ∀ j, ∃ y : IrrRep (GL (Fin (G.d j)) k), IsSubquotient y.ρ
      ((piTensor (G.twD τ)).comp (MonoidHom.mulSingle (fun j => GL (Fin (G.d j)) k) j) :
        Representation ℂ (GL (Fin (G.d j)) k) _) ∧ Nonempty ((G.twD τ j).Equiv y.ρ) := by
    intro j
    obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
      ((piTensor (G.twD τ)).comp (MonoidHom.mulSingle (fun j => GL (Fin (G.d j)) k) j))
      (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτJ)
    have h1 : IsSubquotient υ (G.twD τ j) :=
      GlobalTheory.LocGL.SupportUnique.isSubquotient_factor (G.twD τ) j hυ hυs
    exact ⟨⟨X, υ, h1.isSmooth (hs' j), hυ⟩, hυs,
      GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hυ (hi' j) h1⟩
  choose y hy hyE using hy
  obtain ⟨t, ht, hst⟩ := GlobalTheory.LocGL.SupportUnique.exists_sum_of_jac hG hZ hsπ' G.e hτJ hJs y hy

  have hsm : ∀ a j,
      IsSmoothChar (ν a j * absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))) :=
    fun a j => (hν a j).mul (isSmoothChar_absPow _)
  have htj : ∀ j, t j = Finset.univ.val.map fun i => IrrGL.ofChar _ (hsm j i) := by
    intro j
    obtain ⟨φ⟩ := hyE j
    refine GlobalTheory.LocGL.SupportUnique.eq_of_hasSupport hG hZ (G.d j)
      (IrrGL.of (G.twD τ j) (hs' j) (hi' j)) rfl _ _ ?_ ?_
    · exact ((ht j).of_equiv φ.symm).of_equiv (IrrGL.equivOf _ _ _)
    · exact (hasSupport_twD G τ ν hν hcs j (hsm j)).of_equiv (IrrGL.equivOf _ _ _)
  have hc : ∀ i, IsSmoothChar (G.cOf ν i) := fun i => (hν _ _).mul (isSmoothChar_absPow _)
  have hsF : s = Finset.univ.val.map fun i => IrrGL.ofChar (G.cOf ν i) (hc i) := by
    rw [hst, Finset.sum_congr rfl fun j _ => htj j]
    exact sum_map_univ G.e _ _ fun a j => IrrGL.ofChar_inj.2 (by
      unfold Grp.cOf
      rw [Equiv.symm_apply_apply])

  obtain ⟨h, x, hx, -, -, e, he⟩ := hsπ'
  rw [hsF] at hx
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq x _ hx
  obtain rfl : x = fun a => IrrGL.ofChar (G.cOf ν (σ a)) (hc (σ a)) := funext hσ
  obtain rfl : h = n := by simpa using Fintype.card_congr σ
  let φ := multiProdEquiv e fun a =>
    (GlobalTheory.LocGL.equivRep (IrrRep.det (Fin 1) (G.cOf ν (σ a)) (hc (σ a)))).symm
  have h1 : IsSubquotient π (multiProd e fun a => detRep (Fin 1) (G.cOf ν (σ a))) :=
    he.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have h2 := h1.trans (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e fun a => G.cOf ν (σ a))
  exact hOrd hLit V π hπs hπi (G.cOf ν) hc σ h2

end UpperTheory.TNZ.Grp
end
end

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spLift

variable {Γ V W : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_eigen_lift {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (hρ : IsSmooth ρ)
    (f : ρ.IntertwiningMap σ) {L : Subgroup Γ} (hL : IsCompact (L : Set Γ)) (χ : Γ → ℂ)
    (u : V) (hu : f u ≠ 0) (hχ : ∀ g ∈ L, σ g (f u) = χ g • f u) :
    ∃ v : V, v ≠ 0 ∧ ∀ g ∈ L, ρ g v = χ g • v :=
  _root_.UpperTheory.Reformulated.B.DYka2.main hρ f hL χ u hu hχ

end UpperTheory.TNZ.Grp.P_spLift

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_spLift {n : ℕ} (G : Grp k n) : G.SpecialLiftProp := by
  intro W X _ _ _ _ ρ σ hρ hsq hη
  obtain ⟨S, f, hf⟩ := hsq
  obtain ⟨y, hy, hyη⟩ := hη
  obtain ⟨u, rfl⟩ := hf y
  have hS : IsSmooth S.toRepresentation := fun v => by
    have : {g | S.toRepresentation g v = v} = {g | ρ g (v : W) = v} := by
      ext g
      simp only [Set.mem_ofPred_eq, Subtype.ext_iff]
      rfl
    rw [this]
    exact hρ v
  have hL : IsCompact ((leviK k (fun a : Fin G.s => Fin (G.d a))) :
      Set (Levi k fun a : Fin G.s => Fin (G.d a))) := by
    rw [leviK, Subgroup.coe_pi]
    exact isCompact_univ_pi fun a => GlobalTheory.SplitFlip.isCompact_KO
  obtain ⟨v, hv, hvη⟩ := P_spLift.exists_eigen_lift hS f hL G.eta u hy hyη
  refine ⟨(v : W), fun h => hv (Subtype.ext h), fun m hm => ?_⟩
  exact congrArg Subtype.val (hvη m hm)

end UpperTheory.TNZ.Grp
end
end

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct

namespace UpperTheory.TNZ.Grp

namespace P_spPiEta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} (G : Grp k n)

theorem twD_hasDetVec {Y : Fin G.s → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)) (a : Fin G.s)
    (h : HasDetVec (τ a) (G.μ a)) : HasDetVec (G.twD τ a) (G.μ a) := by
  obtain ⟨v, hv0, hv⟩ := h
  refine ⟨v, hv0, fun g hg => ?_⟩
  have h1 := detChar_of_mem_KO
    (isUnram_absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))) hg
  rw [twD, twist_apply, h1, hv g hg, Units.val_one, one_smul]

theorem twD_isSmooth {Y : Fin G.s → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)) (a : Fin G.s)
    (h : IsSmooth (τ a)) : IsSmooth (G.twD τ a) :=
  isSmooth_twist h (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem jacU_eq_jac {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (m : Levi k fun a : Fin G.s => Fin (G.d a)) (hm : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)))
    (y : Jacquet π (unipRad k G.e)) : jacU G.e π m y = jac G.e π m y := by
  rw [jac, twist_apply, MonoidHom.inv_apply, deltaHalf_of_mem_leviK hm, inv_one, Units.val_one, one_smul]

end P_spPiEta

theorem step_spPiEta {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : G.SpecialRepresentationEtaProp := by
  unfold SpecialRepresentationEtaProp
  intro hLift Y _ _ τ hsm hdet
  obtain ⟨v, hv0, hv⟩ := step_tensorVec k G.s G.d Y (G.twD τ) G.μ
    (fun a => P_spPiEta.twD_hasDetVec G τ a (hdet a))
  have hsm' : IsSmooth (piTensor (G.twD τ)) :=
    isSmooth_piTensor fun a => P_spPiEta.twD_isSmooth G τ a (hsm a)
  obtain ⟨f, hf1, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one G.e (piTensor (G.twD τ)) hsm' v
  let φ := Model.evalOne G.e (Representation.IntertwiningMap.id (multiProd G.e (G.twD τ)))
  have hφ : φ (Submodule.Quotient.mk f) = v := hf1
  let T : Subrepresentation (piTensor (G.twD τ)) := φ.range
  have hmem : ∀ x, φ x ∈ T.toSubmodule := fun x =>
    (Representation.IntertwiningMap.mem_range _ _ _ _).2 ⟨x, rfl⟩
  let ψ : (jac G.e (multiProd G.e (G.twD τ))).IntertwiningMap T.toRepresentation :=
    ⟨LinearMap.codRestrict T.toSubmodule φ.toLinearMap hmem, fun g => LinearMap.ext fun x => Subtype.ext (φ.isIntertwining _ _ g x)⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨w, hw⟩
    obtain ⟨x, rfl⟩ := (Representation.IntertwiningMap.mem_range _ _ _ _).1 hw
    exact ⟨x, rfl⟩
  have hsub : IsSubquotient T.toRepresentation (jac G.e (multiProd G.e (G.twD τ))) :=
    IsSubquotient.of_surjective ψ hψ
  have hη : G.HasEtaVec T.toRepresentation := by
    refine ⟨⟨v, hφ ▸ hmem _⟩, fun h => hv0 (congrArg Subtype.val h), fun m hm => ?_⟩
    apply Subtype.ext
    exact hv m fun a => hm a (Set.mem_univ a)
  obtain ⟨y, hy0, hy⟩ := hLift _ _ _ T.toRepresentation
    (isSmooth_jac G.e (isSmooth_parInd _ _)) hsub hη
  refine ⟨y, hy0, fun m hm => ?_⟩
  exact (P_spPiEta.jacU_eq_jac G _ m hm y).trans (hy m hm)

end UpperTheory.TNZ.Grp
end
end

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spRes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem absPow_unitIncl (z : ℂ) (u : 𝒪[k]ˣ) : absPow k z (unitIncl k u) = 1 := by
  have hu : valuation k ((unitIncl k u : kˣ) : k) = 1 := valuation_eq_one_iff.mpr ⟨u, rfl⟩
  apply Units.ext
  rw [val_absPow, nabs_eq_one (k := k) hu]
  simp

end P_spRes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} (G : Grp k n)


open P_spRes in
theorem step_spRes : G.SpecialRestrictionProp := by
  intro ν hν i
  refine MonoidHom.ext fun u => ?_
  have h1 := DFunLike.congr_fun (hν (G.e.symm i).1 (G.e.symm i).2) u
  simp only [res, MonoidHom.comp_apply] at h1
  simp only [res, cOf, chi, bl, MonoidHom.comp_apply, MonoidHom.mul_apply, absPow_unitIncl, mul_one]
  exact h1

end UpperTheory.TNZ.Grp
end
end

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spTop

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_unitIncl (u : 𝒪[k]ˣ) : valuation k ((unitIncl k u : kˣ) : k) = 1 :=
  valuation_eq_one_iff.mpr ⟨u, rfl⟩

theorem res_eq {μ ν : kˣ →* ℂˣ} (h : ∀ u : kˣ, valuation k (u : k) = 1 → μ u = ν u) : res μ = res ν :=
  MonoidHom.ext fun u => h _ (val_unitIncl u)

theorem exists_unit_ne {μ ν : kˣ →* ℂˣ} (h : res μ ≠ res ν) :
    ∃ u : kˣ, valuation k (u : k) = 1 ∧ μ u ≠ ν u := by
  by_contra hc
  push Not at hc
  exact h (res_eq hc)

theorem isSmooth_prinSeries {n : ℕ} (c : Fin n → kˣ →* ℂˣ) : IsSmooth (prinSeries c) :=
  isSmooth_parInd _ _

theorem isSmoothChar_cOf {n : ℕ} (G : Grp k n) (ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ) (hν : ∀ a j, IsSmoothChar (ν a j))
    (i : Fin n) : IsSmoothChar (G.cOf ν i) :=
  (hν _ _).mul (isSmoothChar_absPow _)

end P_spTop

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem step_spTop (G : Grp k n) : G.NonzeroTopOfSpecialForm := by
  intro hLat hUniq hCount hLift hTw hRes hPiEta hOrd hPiSub hSupp hCusp hProd hTen L V _ _ π hπs hπi Y iY mY τ hτs hτi hτd hsub
  have hc : ∀ a, ∃ μ' : Fin (G.d a) → kˣ →* ℂˣ,
      (∀ j, IsSmoothChar (μ' j) ∧ ∀ u : kˣ, valuation k (u : k) = 1 → μ' j u = G.μ a u) ∧
        IsCuspSupport (τ a) (fun _ => 1) (fun j => detRep (Fin 1) (μ' j)) :=
    fun a => hCusp L.loc k (G.d a) (Y a) (τ a) (hτs a) (hτi a) (G.μ a) (G.smooth a) (hτd a)
  choose ν hν hνc using hc
  have hνs : ∀ a j, IsSmoothChar (ν a j) := fun a j => (hν a j).1
  have hνr : ∀ a j, res (ν a j) = res (G.μ a) := fun a j => P_spTop.res_eq (hν a j).2
  have htw := fun a => hTw Y τ a (hτs a) (hτi a) (hτd a)
  have hPi : (multiProd G.e (G.twD τ)).IsIrreducible :=
    hProd hCusp L.loc k G.s n G.d G.hd Y (G.twD τ) (fun a => (htw a).1) (fun a => (htw a).2.1) G.μ G.smooth
      (fun a => (htw a).2.2) (fun b c hbc => P_spTop.exists_unit_ne (G.dist b c hbc))
  have hπI := hSupp hOrd L V π hπs hπi Y τ hτs hτi ν hνs hνc hsub
  have hPI := hPiSub hOrd L Y τ hτs hτi ν hνs hνc hPi
  obtain ⟨hfd, hle⟩ := hCount L (G.cOf ν) (P_spTop.isSmoothChar_cOf G ν hνs) (hRes ν hνr)
  have hπη : G.HasEtaVec (jacU G.e π) := by
    obtain ⟨v, hv0, hv⟩ := hTen k G.s G.d Y τ G.μ hτd
    refine hLift _ _ (jacU G.e π) (piTensor τ) (isSmooth_jacU G.e hπs) hsub ⟨v, hv0, fun m hm => ?_⟩
    have hm' := hm
    rw [leviK, Subgroup.mem_pi] at hm'
    exact hv m fun a => hm' a (Set.mem_univ a)
  have hPη := hPiEta hLift Y τ hτs hτd
  obtain ⟨e⟩ := hUniq hLat _ (prinSeries (G.cOf ν)) (P_spTop.isSmooth_prinSeries _) hfd hle _ _ π
    (multiProd G.e (G.twD τ)) hπi hPi hπI hPI hπη hPη
  exact ⟨Y, iY, mY, G.twD τ, fun a => (htw a).1, fun a => (htw a).2.1, fun a => (htw a).2.2, ⟨e⟩⟩

end UpperTheory.TNZ.Grp
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

namespace P_spTwBasic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_detAbsPow (N : ℕ) (s : ℂ) : IsSmoothChar (detChar (Fin N) (absPow k s)) :=
  (GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_absPow k s)).detChar

theorem hasDetVec_twist_absPow {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (η : kˣ →* ℂˣ) (s : ℂ) (h : HasDetVec ρ η) :
    HasDetVec (GlobalTheory.SmGL.twist ρ (detChar (Fin N) (absPow k s))) η := by
  obtain ⟨v, hv0, hv⟩ := h
  refine ⟨v, hv0, fun g hg => ?_⟩
  rw [GlobalTheory.SmGL.twist_apply, GlobalTheory.LocGL.detChar_of_mem_KO (GlobalTheory.SmGL.isUnram_absPow k s) hg, hv g hg,
    Units.val_one, one_smul]

end P_spTwBasic

theorem step_spTwBasic {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : G.NonzeroBasicTwistOfSpecialForm := by
  intro Y _ _ τ a hs hi hd
  unfold twD
  exact ⟨GlobalTheory.SmGL.isSmooth_twist hs (P_spTwBasic.isSmoothChar_detAbsPow _ _),
    GlobalTheory.LocGL.isIrreducible_twist hi _, P_spTwBasic.hasDetVec_twist_absPow _ _ _ hd⟩

end UpperTheory.TNZ.Grp
end
end
