module

public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle002
public import Development.WeilBound.ThetaLifts.SphericalLattices.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950
public import Development.WeilBound.ThetaLifts.SphericalLattices.ExistsFixedSum
public import Development.WeilBound.ThetaLifts.SphericalLattices.SplitLoc
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HoweMaximalTori.MaxSplit
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsEigenLift
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitLoc

@[expose] public section

section

noncomputable section

namespace PositivityTheory.Sph.SplitPl

open scoped Matrix Topology
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
  GlobalTheory.SplitFlip PositivityTheory.KCo

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

theorem intInd_eq (v : Pl F) {a b : ℕ} : (SplitDict.intInd v : Matrix (Fin a) (Fin b) (Fv F v) → ℂ) =
    Set.indicator {Z : Matrix (Fin a) (Fin b) (Fv F v) | ∀ i j, Z i j ∈ 𝒪[Fv F v]} (fun _ => (1 : ℂ)) := by
  unfold SplitDict.intInd
  congr 1
  ext Z
  exact forall₂_congr fun i j => (GlobalTheory.WeylFour.IndOSelf.mem_int_iff _).symm

theorem sphAt_of (hL : LatSt) {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
    {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {α : (Fv F v)ˣ →* ℂˣ}
    (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hs : M.vac v ∈ SB _) (hvac : ι (M.vac v) = SplitDict.intInd v)
    (hg : ∀ g₀ : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), Reads v ι (om (g, 1)) (omB 1 α g₀ 1))
    (hh : ∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), Reads v ι (om (1, h)) (omB 1 α 1 h₀)) :
    SphAt M ψ om v := by
  intro ω ρ L
  have rg : ∀ g₀ : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ω (g, 1) φ ∈ SB _ ∧ ι (ω (g, 1) φ) = omB 1 α g₀ 1 (ι φ) := fun g₀ => by
    obtain ⟨g, hg', r⟩ := hg g₀
    refine ⟨g, hg', fun φ hφ => ?_⟩
    obtain ⟨φ₁, h₁, ha, e⟩ := r φ hφ
    rw [(L.acts g hg' 1 (one_mem_UAt W v) φ hφ φ₁).1 ha] at h₁ e
    exact ⟨h₁, e⟩
  have rh : ∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ω (1, h) φ ∈ SB _ ∧ ι (ω (1, h) φ) = omB 1 α 1 h₀ (ι φ) := fun h₀ => by
    obtain ⟨h, hh', r⟩ := hh h₀
    refine ⟨h, hh', fun φ hφ => ?_⟩
    obtain ⟨φ₁, h₁, ha, e⟩ := r φ hφ
    rw [(L.acts 1 (one_mem_UAt X v) h hh' φ hφ φ₁).1 ha] at h₁ e
    exact ⟨h₁, e⟩
  have liftR : ∀ f ∈ Submodule.span ℂ {f | ∃ h : GL (Fin d) (Fv F v), f = fun Y =>
      Set.indicator {Z : Matrix (Fin n) (Fin d) (Fv F v) | ∀ i j, Z i j ∈ 𝒪[Fv F v]} (fun _ => (1 : ℂ)) (Y * h.1)},
      ∃ z ∈ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) (M.vac v)},
        z ∈ SB (Fin n × Fin d → Fv F v) ∧ ι z = f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h₀, rfl⟩ := hx
      obtain ⟨h, hh', r⟩ := rh h₀
      obtain ⟨hS, e⟩ := r _ hs
      have hc : (α (gdet h₀) : ℂ) * apow (gdet h₀) ((n : ℂ) / 2) ≠ 0 := mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
      refine ⟨((α (gdet h₀) : ℂ) * apow (gdet h₀) ((n : ℂ) / 2))⁻¹ • ω (1, h) (M.vac v),
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, hh', rfl⟩), Submodule.smul_mem _ _ hS, ?_⟩
      rw [map_smul, e, hvac, split_weil_rep_right_action, intInd_eq]
      funext Y
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    | zero => exact ⟨0, zero_mem _, zero_mem _, map_zero ι⟩
    | add x y _ _ hx hy =>
      obtain ⟨z, hz, hzS, e⟩ := hx
      obtain ⟨z', hz', hzS', e'⟩ := hy
      exact ⟨z + z', add_mem hz hz', add_mem hzS hzS', by rw [map_add (f := _), e, e']⟩
    | smul a x _ hx =>
      obtain ⟨z, hz, hzS, e⟩ := hx
      exact ⟨a • z, Submodule.smul_mem _ a hz, Submodule.smul_mem _ a hzS, by rw [map_smul, e]⟩
  have liftL : ∀ f ∈ Submodule.span ℂ {f | ∃ g : GL (Fin n) (Fv F v), f = fun Y =>
      Set.indicator {Z : Matrix (Fin n) (Fin d) (Fv F v) | ∀ i j, Z i j ∈ 𝒪[Fv F v]} (fun _ => (1 : ℂ)) (g.1 * Y)},
      ∃ z ∈ Submodule.span ℂ {z | ∃ g ∈ UAt σ X (evFin F v), z = ω (g, 1) (M.vac v)},
        z ∈ SB (Fin n × Fin d → Fv F v) ∧ ι z = f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g₀, rfl⟩ := hx
      obtain ⟨g, hg', r⟩ := rg (invT g₀)⁻¹
      obtain ⟨hS, e⟩ := r _ hs
      have hc : apow (gdet (invT g₀)⁻¹) ((d : ℂ) / 2) ≠ 0 := apow_ne_zero _ _
      refine ⟨(apow (gdet (invT g₀)⁻¹) ((d : ℂ) / 2))⁻¹ • ω (g, 1) (M.vac v),
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg', rfl⟩), Submodule.smul_mem _ _ hS, ?_⟩
      rw [map_smul, e, hvac, split_weil_rep_left_action, intInd_eq, invT_inv_val, Matrix.transpose_transpose]
      funext Y
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    | zero => exact ⟨0, zero_mem _, zero_mem _, map_zero ι⟩
    | add x y _ _ hx hy =>
      obtain ⟨z, hz, hzS, e⟩ := hx
      obtain ⟨z', hz', hzS', e'⟩ := hy
      exact ⟨z + z', add_mem hz hz', add_mem hzS hzS', by rw [map_add (f := _), e, e']⟩
    | smul a x _ hx =>
      obtain ⟨z, hz, hzS, e⟩ := hx
      exact ⟨a • z, Submodule.smul_mem _ a hz, Submodule.smul_mem _ a hzS, by rw [map_smul, e]⟩
  refine ⟨M.vac v, hs, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · obtain ⟨m, g, hgK, hinv⟩ := avgL (hb.1 hφ)
    choose x hx hxr using fun i => rg (invT (g i))
    have hterm : ∀ i, ι (ω (x i, 1) φ) = fun Y => ι φ (((g i)⁻¹).val * Y) := fun i => by
      rw [(hxr i φ hφ).2, split_weil_rep_left_action, apow_KO (invT_mem_KO (hgK i))]
      funext Y
      rw [one_mul, invT_val, Matrix.transpose_transpose]
    set φ' := ∑ i, ω (x i, 1) φ with hφ'
    have hφ'S : φ' ∈ SB _ := sum_mem fun i _ => (hxr i φ hφ).1
    have hφ'ι : ι φ' = fun Y => ∑ i, ι φ (((g i)⁻¹).val * Y) := by

      rw [hφ', map_sum]
      funext Y
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun i _ => congrFun (hterm i) Y
    have hf : (fun Y => ∑ i, ι φ (((g i)⁻¹).val * Y)) ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)) := hφ'ι ▸ hb.1 hφ'S
    obtain ⟨z, hz, hzS, hzι⟩ := liftR _ (hL (Fv F v) n d _ hf fun h hh Y => hinv h hh Y)
    have hz' : z = φ' := hb.2.1 hzS hφ'S (hzι.trans hφ'ι.symm)
    have haug : ((m + 1 : ℕ) : ℂ) • φ - φ' ∈ augAt om v := by
      have e : ((m + 1 : ℕ) : ℂ) • φ - φ' = ∑ i : Fin (m + 1), -(ω (x i, 1) φ - φ) := by
        rw [hφ', Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Nat.cast_smul_eq_nsmul ℂ, neg_sub]
      rw [e]
      exact sum_mem fun i _ => neg_mem (PositivityTheory.Sph.IsLocRep.sub_mem_aug L (hx i) hφ)
    have hc : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)
    refine Submodule.mem_sup.2 ⟨_, Submodule.smul_mem _ (((m + 1 : ℕ) : ℂ)⁻¹) haug, _,
      Submodule.smul_mem _ (((m + 1 : ℕ) : ℂ)⁻¹) (hz' ▸ hz), ?_⟩
    rw [← smul_add, sub_add_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · obtain ⟨m, h, hhK, hinv⟩ := avgR (hb.1 hφ)
    choose y hy hyr using fun i => rh (h i)
    have hterm : ∀ i, ∀ ψ' ∈ SB (Fin n × Fin d → Fv F v),
        ι (((α (gdet (h i)) : ℂ))⁻¹ • ω (1, y i) ψ') = fun Y => ι ψ' (Y * (h i).val) := fun i ψ' hψ' => by
      rw [map_smul, (hyr i ψ' hψ').2, split_weil_rep_right_action, apow_KO (hhK i)]
      funext Y
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
    have hfix : ∀ i, ((α (gdet (h i)) : ℂ))⁻¹ • ω (1, y i) (M.vac v) = M.vac v := fun i =>
      hb.2.1 (Submodule.smul_mem _ _ (hyr i _ hs).1) hs (by
        rw [hterm i _ hs, hvac, intInd_eq]
        funext Y
        exact ind_mulKO Y (hhK i))
    set φ' := ∑ i, ((α (gdet (h i)) : ℂ))⁻¹ • ω (1, y i) φ with hφ'
    have hφ'S : φ' ∈ SB _ := sum_mem fun i _ => Submodule.smul_mem _ _ (hyr i φ hφ).1
    have hφ'ι : ι φ' = fun Y => ∑ i, ι φ (Y * (h i).val) := by

      rw [hφ', map_sum]
      funext Y
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun i _ => congrFun (hterm i φ hφ) Y
    have hf : (fun Y => ∑ i, ι φ (Y * (h i).val)) ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)) := hφ'ι ▸ hb.1 hφ'S
    obtain ⟨z, hz, hzS, hzι⟩ := liftL _ (latT hL hf fun k hk Y => hinv k hk Y)
    have hz' : z = φ' := hb.2.1 hzS hφ'S (hzι.trans hφ'ι.symm)
    obtain ⟨c, hc⟩ := PositivityTheory.Sph.IsLocRep.span_vac L hs hz
    rw [hz', hφ'] at hc
    exact ⟨m, y, fun i => ((α (gdet (h i)) : ℂ))⁻¹, c, fun i => ⟨hy i, hfix i⟩, hc⟩

end PositivityTheory.Sph.SplitPl

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

end PositivityTheory.Sph

end
end

section

noncomputable section

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

section Core

variable {V H : Type} [AddCommGroup V] [Module ℂ V]

def Stab (S A : Submodule ℂ V) (U : Set H) (T : H → Module.End ℂ V) (P : Submodule ℂ V) : Prop :=
  A ≤ P ∧ P ≤ S ∧ ∀ h ∈ U, ∀ x ∈ P, T h x ∈ P

variable {S A : Submodule ℂ V} {U : Set H} {T : H → Module.End ℂ V}

theorem Stab.sup {P P' : Submodule ℂ V} (h : Stab S A U T P) (h' : Stab S A U T P') : Stab S A U T (P ⊔ P') := by
  refine ⟨le_sup_of_le_left h.1, sup_le h.2.1 h'.2.1, fun i hi x hx => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (h.2.2 i hi y hy) (h'.2.2 i hi z hz)

theorem Stab.not_mem {s : V} (hgen : ∀ φ ∈ S, φ ∈ A ⊔ Submodule.span ℂ {z | ∃ h ∈ U, z = T h s}) {P : Submodule ℂ V}
    (h : Stab S A U T P) (hP : P ≠ S) : s ∉ P := by
  intro hs
  refine hP (le_antisymm h.2.1 fun φ hφ => (sup_le h.1 (Submodule.span_le.2 ?_)) (hgen φ hφ))
  rintro _ ⟨i, hi, rfl⟩
  exact h.2.2 i hi s hs

theorem Stab.sup_ne {s : V} (hs : s ∈ S) (hgen : ∀ φ ∈ S, φ ∈ A ⊔ Submodule.span ℂ {z | ∃ h ∈ U, z = T h s})
    (hline : ∀ φ ∈ S, ∃ (m : ℕ) (k : Fin (m + 1) → H) (w : Fin (m + 1) → ℂ) (c : ℂ),
      (∀ i, k i ∈ U ∧ w i • T (k i) s = s) ∧ ∑ i, w i • T (k i) φ - c • s ∈ A)
    {P P' : Submodule ℂ V} (h : Stab S A U T P) (h' : Stab S A U T P') (hP : P ≠ S) (hP' : P' ≠ S) : P ⊔ P' ≠ S := by
  intro e
  have hs' : s ∈ P ⊔ P' := e ▸ hs
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hs'
  obtain ⟨m, k, w, c, hw, hc⟩ := hline x (h.2.1 hx)
  have hxP : ∑ i, w i • T (k i) x ∈ P := P.sum_mem fun i _ => P.smul_mem _ (h.2.2 _ (hw i).1 x hx)
  have hyP : ∑ i, w i • T (k i) y ∈ P' := P'.sum_mem fun i _ => P'.smul_mem _ (h'.2.2 _ (hw i).1 y hy)
  have hsum : ∑ i, w i • T (k i) x + ∑ i, w i • T (k i) y = ((m + 1 : ℕ) : ℂ) • s := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← smul_add, ← map_add (f := _), hxy, (hw _).2]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  have h1 : c • s ∈ P := by
    have := P.sub_mem hxP (h.1 hc)
    rwa [sub_sub_cancel] at this
  have h2 : (((m + 1 : ℕ) : ℂ) - c) • s ∈ P' := by
    have e2 : (((m + 1 : ℕ) : ℂ) - c) • s = ∑ i, w i • T (k i) y + (∑ i, w i • T (k i) x - c • s) := by
      rw [sub_smul, ← hsum]; abel
    rw [e2]
    exact P'.add_mem hyP (h'.1 hc)
  by_cases hc0 : c = 0
  · subst hc0
    refine Stab.not_mem hgen h' hP' ?_
    have := P'.smul_mem (((m + 1 : ℕ) : ℂ))⁻¹ h2
    rwa [sub_zero, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero m), one_smul] at this
  · refine Stab.not_mem hgen h hP ?_
    have := P.smul_mem c⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

end Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
  {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}

omit [NumberField E] in
theorem one_uat (v : Pl F) : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by simp [mat]

theorem stab_of (L : IsLocRep M ψ om v ω ρ) {N} (hN : GlobalTheory.Published.ThetaSub om v N) :
    Stab (SB _) (augAt om v) (UAt σ W (evFin F v)) (fun h => ω (1, h)) N :=
  ⟨hN.1, hN.2.1, fun h hh x hx => hN.2.2 h hh x hx _ (L.pres 1 (one_uat v) h hh x (hN.2.1 hx))
    ((L.acts 1 (one_uat v) h hh x (hN.2.1 hx) _).2 rfl)⟩

theorem thetaSub_of (L : IsLocRep M ψ om v ω ρ) {N}
    (hN : Stab (SB _) (augAt om v) (UAt σ W (evFin F v)) (fun h => ω (1, h)) N) : GlobalTheory.Published.ThetaSub om v N :=
  ⟨hN.1, hN.2.1, fun h hh φ hφ φ₁ _ hA => by
    rw [(L.acts 1 (one_uat v) h hh φ (hN.2.1 hφ) φ₁).1 hA]
    exact hN.2.2 h hh φ hφ⟩

theorem thetaSub_sup (L : IsLocRep M ψ om v ω ρ) {N N'} (hN : GlobalTheory.Published.ThetaSub om v N)
    (hN' : GlobalTheory.Published.ThetaSub om v N') : GlobalTheory.Published.ThetaSub om v (N ⊔ N') :=
  thetaSub_of L ((stab_of L hN).sup (stab_of L hN'))

theorem sup_ne_of (L : IsLocRep M ψ om v ω ρ) (hs : SphAt M ψ om v ∨ IrrAt om v) {N N'} (hN : GlobalTheory.Published.ThetaSub om v N)
    (hN' : GlobalTheory.Published.ThetaSub om v N') (h1 : N ≠ SB _) (h2 : N' ≠ SB _) : N ⊔ N' ≠ SB _ := by
  rcases hs with hs | hs
  · obtain ⟨s, hs⟩ := hs ω ρ L
    exact Stab.sup_ne hs.mem hs.gen hs.line (stab_of L hN) (stab_of L hN') h1 h2
  · have e1 := (hs N hN).resolve_right h1
    have e2 := (hs N' hN').resolve_right h2
    rw [e1, e2, sup_idem]
    rw [e1] at h1
    exact h1

theorem maxAt_of (L : IsLocRep M ψ om v ω ρ) (hs : SphAt M ψ om v ∨ IrrAt om v) : PositivityTheory.HoweDualityUnitaryAlt.MaxAt om v := by
  intro N N' hN hN'
  have hq : GlobalTheory.Published.ThetaSub om v (N ⊔ N') ∧ N ⊔ N' ≠ SB _ :=
    ⟨thetaSub_sup L hN.prop.1 hN'.prop.1, sup_ne_of L hs hN.prop.1 hN'.prop.1 hN.prop.2 hN'.prop.2⟩
  exact (hN.eq_of_ge hq le_sup_left).symm.trans (hN'.eq_of_ge hq le_sup_right)

theorem locRep_tri {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Y : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G Y om om') (v : Pl F) :
    (∃ ω ρ, IsLocRep G.M B.ψ om v ω ρ) ∧ ∃ ω ρ, IsLocRep G.M' B.ψ om' v ω ρ :=
  ⟨PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B G.V G.W G.M om
      ⟨hT.base, ⟨_, _, hT.geo.hV⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM, ⟨_, _, hT.weil⟩⟩ v,
    PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B G.V' G.W G.M' om'
      ⟨hT.base, ⟨_, _, hT.geo.hV'⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM', ⟨_, _, hT.weil'⟩⟩ v⟩

theorem maxFinT_of (h : SphTri) : PositivityTheory.HoweDualityUnitaryAlt.MaxFinT := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v _
  obtain ⟨h1, h2⟩ := h F E σ B a a' G X om om' hT v
  obtain ⟨⟨ω, ρ, L⟩, ⟨ω', ρ', L'⟩⟩ := locRep_tri hT v
  exact ⟨maxAt_of L h1, maxAt_of L' h2⟩

end PositivityTheory.Sph

end
end
