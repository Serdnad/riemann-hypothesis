module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle015
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle014
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section CorrProof

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem Dl_succ {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.Dl f f' (r + 1) = (H.Zhat f f').det := by
  unfold HermSp.Dl
  rw [dite_eq_left le_rfl]
  congr 1

theorem mkW_eq_of_sub_mem {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    {f : Fin (r + 1) → V} {x y : ↥(H.perp (H.X f))} (h : (x : V) - y ∈ H.X f) : H.mkW f x = H.mkW f y := by
  unfold HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  simpa using h

theorem corrIso_holds (M : Model F E) (r n : ℕ) : CorrIso M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD₂
  obtain ⟨hg₁, hF₂, hF₂', hI, hz, hz'⟩ := hyp
  have hT1 := hg₁.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hT1.2.1.2.1, hT1.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hT1.2.2.1.2.1, hT1.2.2.1.2.2.1⟩
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT1.2.2.2.1
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := isUnit_Gdet H _ _ _ _ hT1.2.2.2.2.1
  obtain ⟨hIs, -, hW0c, hom', -, hκ⟩ := hI
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have e := Gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hκ
    have hN₁ : IsUnit (H.normE (H.Dl t₁.f t₁.f' (r + 1))) := hD₁.mul (hD₁.map M.L.cj)
    have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hD₂.mul (hD₂.map M.L.cj)
    have h3 : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [e]
      exact hN₂.mul hG₁
    exact isUnit_of_mul_isUnit_left h3
  have hU₁ := isCompl_span_frames_W0 H t₁.f t₁.f' t₁.T t₁.T' hF₁ hF₁' hD₁ hG₁
  have hU₂ := isCompl_span_frames_W0 H f₂ f₂' t₁.T t₁.T' hF₂ hF₂' hD₂ hG₂
  have hXU : ∀ g g' : Fin (r + 1) → V, H.X g ≤ Submodule.span E (Set.range (Sum.elim g g')) :=
    fun g g' => Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨Sum.inl j.castSucc, rfl⟩)
  have huniq : ∀ (a b : V) (ha : a ∈ H.W0 f₂ f₂') (hb : b ∈ H.W0 f₂ f₂'),
      H.mkW f₂ ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H ha⟩ = H.mkW f₂ ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H hb⟩ → a = b := by
    intro a b ha hb hab
    have h1 := sub_mem_X_of_mkW_eq H hab
    exact sub_eq_zero.1 ((Submodule.disjoint_def.1 hU₂.disjoint) _ (hXU f₂ f₂' h1) (Submodule.sub_mem _ ha hb))
  have hex : ∀ w : ↥(H.W0 t₁.f t₁.f'), ∃ w₂ : ↥(H.W0 f₂ f₂'),
      φ (H.mkW t₁.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩) = H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩ ∧
      φ' (H.mkW t₁.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩) = H.mkW f₂' ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp' H w₂.2⟩ := by
    intro w
    obtain ⟨w₂, hw₂, s1, s2⟩ := hW0c w w.2
    refine ⟨⟨w₂, hw₂⟩, ?_, ?_⟩
    · have := s1 ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H hw₂⟩ rfl rfl
      simpa using this
    · have := s2 ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp' H hw₂⟩ rfl rfl
      simpa using this
  choose ψf hψf using hex
  have hψadd : ∀ a b, ψf (a + b) = ψf a + ψf b := by
    intro a b
    apply Subtype.ext
    apply huniq _ _ (ψf (a + b)).2 (ψf a + ψf b).2
    rw [← (hψf (a + b)).1]
    have e : (⟨((a + b : ↥(H.W0 t₁.f t₁.f')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (a + b).2⟩ : ↥(H.perp (H.X t₁.f))) =
        ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ + ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H b.2⟩ := Subtype.ext rfl
    have e2 : (⟨((ψf a + ψf b : ↥(H.W0 f₂ f₂')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (ψf a + ψf b).2⟩ : ↥(H.perp (H.X f₂))) =
        ⟨ψf a, mem_perp_isotropicSpan_of_mem_framePerp H (ψf a).2⟩ + ⟨ψf b, mem_perp_isotropicSpan_of_mem_framePerp H (ψf b).2⟩ := Subtype.ext rfl
    rw [e, e2, map_add (f := _), map_add (f := _), map_add (f := _), (hψf a).1, (hψf b).1]
  have hψsmul : ∀ (c : E) a, ψf (c • a) = c • ψf a := by
    intro c a
    apply Subtype.ext
    apply huniq _ _ (ψf (c • a)).2 (c • ψf a).2
    rw [← (hψf (c • a)).1]
    have e : (⟨((c • a : ↥(H.W0 t₁.f t₁.f')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (c • a).2⟩ : ↥(H.perp (H.X t₁.f))) =
        c • ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ := Subtype.ext rfl
    have e2 : (⟨((c • ψf a : ↥(H.W0 f₂ f₂')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (c • ψf a).2⟩ : ↥(H.perp (H.X f₂))) =
        c • ⟨ψf a, mem_perp_isotropicSpan_of_mem_framePerp H (ψf a).2⟩ := Subtype.ext rfl
    rw [e, e2, map_smul, map_smul, map_smul, (hψf a).1]
  let ψL : ↥(H.W0 t₁.f t₁.f') →ₗ[E] ↥(H.W0 f₂ f₂') :=
    { toFun := ψf, map_add' := hψadd, map_smul' := hψsmul }
  have hinj : Function.Injective ψL := by
    intro a b hab
    have hab' : ψf a = ψf b := hab
    have e : H.mkW t₁.f ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ = H.mkW t₁.f ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H b.2⟩ :=
      φ.injective (by rw [(hψf a).1, (hψf b).1, hab'])
    have h1 := sub_mem_X_of_mkW_eq H e
    exact Subtype.ext (sub_eq_zero.1 ((Submodule.disjoint_def.1 hU₁.disjoint) _ (hXU t₁.f t₁.f' h1)
      (Submodule.sub_mem _ a.2 b.2)))
  have hsurj : Function.Surjective ψL := by
    intro w₂
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (φ.symm (H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩))
    have hy' : φ (H.mkW t₁.f y) = H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩ := by
      have : H.mkW t₁.f y = φ.symm (H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩) := hy
      rw [this, LinearEquiv.apply_symm_apply]
    have hyU : (y : V) ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')) ⊔ H.W0 t₁.f t₁.f' := by
      rw [hU₁.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hyU
    have hup : u ∈ H.perp (H.X t₁.f) := by
      have : u = (y : V) - w := by rw [← huw]; abel
      rw [this]
      exact Submodule.sub_mem _ y.2 (mem_perp_isotropicSpan_of_mem_framePerp H hw)
    have hZ₁ : IsUnit (H.Zhat t₁.f t₁.f').det := by rw [← Dl_succ]; exact hD₁
    obtain ⟨x, hx, β, γ, hxe⟩ := decomp_U_perpX H hF₁ hZ₁ hu hup
    refine ⟨⟨w, hw⟩, ?_⟩
    set D₂ := H.Dl f₂ f₂' (r + 1)
    set D₁ := H.Dl t₁.f t₁.f' (r + 1)
    let zP₁ : ↥(H.perp (H.X t₁.f)) := ⟨t₁.f (Fin.last r), z_mem_perpX H hF₁⟩
    let oP₁ : ↥(H.perp (H.X t₁.f)) := ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩
    let zP₂ : ↥(H.perp (H.X f₂)) := ⟨f₂ (Fin.last r), z_mem_perpX H hF₂⟩
    let oP₂ : ↥(H.perp (H.X f₂)) := ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩
    let wP : ↥(H.perp (H.X t₁.f)) := ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩
    let vP : ↥(H.perp (H.X f₂)) := ⟨ψf ⟨w, hw⟩, mem_perp_isotropicSpan_of_mem_framePerp H (ψf ⟨w, hw⟩).2⟩
    have hq₁ : H.mkW t₁.f y = H.mkW t₁.f (β • zP₁ + γ • oP₁ + wP) := by
      apply mkW_eq_of_sub_mem
      show (y : V) - (β • t₁.f (Fin.last r) + γ • H.om' t₁.f t₁.f' + w) ∈ H.X t₁.f
      rw [← huw, hxe]
      convert hx using 1
      abel
    have hz1 : φ (H.mkW t₁.f zP₁) = H.mkW f₂ zP₂ := by
      have := hz zP₁ zP₂ rfl rfl
      simpa using this
    have ho0 : D₂ • φ (H.mkW t₁.f oP₁) = D₁ • H.mkW f₂ oP₂ := by
      have := hom' oP₁ oP₂ rfl rfl
      simpa using this
    have ho1 : φ (H.mkW t₁.f oP₁) = (Ring.inverse D₂ * D₁) • H.mkW f₂ oP₂ := by
      rw [mul_smul, ← ho0, smul_smul, Ring.inverse_mul_cancel _ hD₂, one_smul]
    have hw1 : φ (H.mkW t₁.f wP) = H.mkW f₂ vP := (hψf ⟨w, hw⟩).1
    have hq₂ : H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩ =
        H.mkW f₂ (β • zP₂ + (γ * (Ring.inverse D₂ * D₁)) • oP₂ + vP) := by
      rw [← hy', hq₁]
      simp only [map_add (f := _), map_smul, hz1, ho1, hw1, smul_smul]
    have hd := sub_mem_X_of_mkW_eq H hq₂
    have hU2mem : (w₂ : V) - (ψf ⟨w, hw⟩ : V) ∈ Submodule.span E (Set.range (Sum.elim f₂ f₂')) := by
      have e : (w₂ : V) - (ψf ⟨w, hw⟩ : V) =
          ((w₂ : V) - ((β • zP₂ + (γ * (Ring.inverse D₂ * D₁)) • oP₂ + vP : ↥(H.perp (H.X f₂))) : V)) +
            (β • f₂ (Fin.last r) + (γ * (Ring.inverse D₂ * D₁)) • H.om' f₂ f₂') := by
        simp only [Submodule.coe_add, Submodule.coe_smul, zP₂, oP₂, vP]
        abel
      rw [e]
      exact Submodule.add_mem _ (hXU f₂ f₂' hd) (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl (Fin.last r), rfl⟩))
        (Submodule.smul_mem _ _ (om'_mem_U H f₂ f₂')))
    have h0 := (Submodule.disjoint_def.1 hU₂.disjoint) _ hU2mem (Submodule.sub_mem _ w₂.2 (ψf ⟨w, hw⟩).2)
    exact Subtype.ext (sub_eq_zero.1 h0).symm
  refine ⟨LinearEquiv.ofBijective ψL ⟨hinj, hsurj⟩, fun a b => ?_, fun n₁ n₂ => ?_⟩
  · show H.h ((ψf a : ↥(H.W0 f₂ f₂')) : V) ((ψf b : ↥(H.W0 f₂ f₂')) : V) = H.h a b
    exact hIs ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H b.2⟩ ⟨ψf a, mem_perp_isotropicSpan_of_mem_framePerp H (ψf a).2⟩
      ⟨ψf b, mem_perp_isotropicSpan_of_mem_framePerp H (ψf b).2⟩ (hψf a).1 (hψf b).1
  · constructor
    · rintro ⟨h₁, h₂, c1, -⟩
      refine ⟨h₁, ?_⟩
      show ((ψf ⟨n₁, h₁⟩ : ↥(H.W0 f₂ f₂')) : V) = n₂
      exact huniq _ _ (ψf ⟨n₁, h₁⟩).2 h₂ ((hψf ⟨n₁, h₁⟩).1.symm.trans c1)
    · rintro ⟨h₁, rfl⟩
      exact ⟨h₁, (ψf ⟨n₁, h₁⟩).2, (hψf ⟨n₁, h₁⟩).1, (hψf ⟨n₁, h₁⟩).2⟩

end CorrProof

end Formalism.L2.SG.LsDatumA
end
end

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Fwd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]


theorem glueFwd_of (M : Model F E) (r n : ℕ) (hM : M.OK) (hC : CorrIso M r n) (hE : GlueEta M r) :
    GlueFwd M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hT Λ₂ hG₂ hTh
  set t₂ : Term V M r := { abelian₂ := Λ₂, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } with ht₂
  have memS : ∀ (t : Term V M r) (N : Submodule M.L.O V) (w : V),
      w ∈ ThSharp H t N ↔ (w ∈ H.W0 t.f t.f' ∧ ∀ n ∈ N, H.h w n ∈ M.L.O) :=
    fun _ _ _ => Iff.rfl
  have memL : ∀ (t : Term V M r) (w : V), w ∈ ThL H t ↔ (w ∈ t.abelian₂ ∧ w ∈ H.W0 t.f t.f') :=
    fun _ _ => Iff.rfl
  have hDl : IsUnit (H.Dl f₂ f₂' (r + 1)) := by
    obtain ⟨⟨_, _, _, hD, _⟩, _⟩ := hG₂
    exact hD
  have hG₁ : H.IsGeneric t₁ := by
    obtain ⟨h, -⟩ := id hT
    exact h
  obtain ⟨ψ, hψh, hψC⟩ := hC V H hn t₁ f₂ f₂' φ φ' hT hDl
  have key : ∀ (x : V) (hx : x ∈ H.W0 t₁.f t₁.f'), x ∈ t₁.abelian₂ ↔ (ψ ⟨x, hx⟩ : V) ∈ Λ₂ :=
    fun x hx => hTh x _ ((hψC x _).2 ⟨hx, rfl⟩)
  obtain ⟨η₁, hη₁a, hη₁b⟩ := hE hM V H t₁ hG₁
  obtain ⟨η₂, hη₂a, hη₂b⟩ := hE hM V H t₂ hG₂
  have fwd : ∀ (w : V) (hw : w ∈ ThSharp H t₁ (ThL H t₁)),
      (ψ ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₂ (ThL H t₂) := by
    intro w hw
    refine (memS _ _ _).2 ⟨(ψ _).2, ?_⟩
    intro n hn'
    obtain ⟨hnΛ, hnW⟩ := (memL _ _).1 hn'
    have h1 : (ψ (ψ.symm ⟨n, hnW⟩) : V) = n := by simp
    rw [← h1, hψh]
    refine ((memS _ _ _).1 hw).2 _ ((memL _ _).2 ⟨?_, (ψ.symm ⟨n, hnW⟩).2⟩)
    exact (key _ (ψ.symm ⟨n, hnW⟩).2).2 (by simpa [ht₂] using hnΛ)
  have bwd : ∀ (w : V) (hw : w ∈ ThSharp H t₂ (ThL H t₂)),
      (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₁ (ThL H t₁) := by
    intro w hw
    refine (memS _ _ _).2 ⟨(ψ.symm _).2, ?_⟩
    intro n hn'
    obtain ⟨hnΛ, hnW⟩ := (memL _ _).1 hn'
    have h2 := hψh (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩) ⟨n, hnW⟩
    simp only [LinearEquiv.apply_symm_apply] at h2
    rw [← h2]
    exact ((memS _ _ _).1 hw).2 _ ((memL _ _).2 ⟨(key n hnW).1 hnΛ, (ψ ⟨n, hnW⟩).2⟩)
  let e : ThSharp H t₁ (ThL H t₁) ≃ₗ[M.L.O] ThSharp H t₂ (ThL H t₂) :=
    { toFun := fun w => ⟨_, fwd w.1 w.2⟩
      invFun := fun w => ⟨_, bwd w.1 w.2⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        have h := congrArg Subtype.val
          (map_add ψ ⟨(a : V), ((memS _ _ _).1 a.2).1⟩ ⟨(b : V), ((memS _ _ _).1 b.2).1⟩)
        exact h
      map_smul' := by
        intro c a
        apply Subtype.ext
        have h := congrArg Subtype.val (map_smul ψ (c : E) ⟨(a : V), ((memS _ _ _).1 a.2).1⟩)
        exact h
      left_inv := by
        intro a
        apply Subtype.ext
        simp
      right_inv := by
        intro a
        apply Subtype.ext
        simp }
  have hPQ : Submodule.map (e : ThSharp H t₁ (ThL H t₁) →ₗ[M.L.O] ThSharp H t₂ (ThL H t₂))
      (Submodule.comap (ThSharp H t₁ (ThL H t₁)).subtype (ThL H t₁)) =
      Submodule.comap (ThSharp H t₂ (ThL H t₂)).subtype (ThL H t₂) := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨h1, -⟩ := (memL _ _).1 hy
      exact (memL _ _).2 ⟨(key _ _).1 h1, (ψ _).2⟩
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      obtain ⟨h1, -⟩ := (memL _ _).1 hx
      refine (memL _ _).2 ⟨?_, (ψ.symm ⟨(x : V), ((memS _ _ _).1 x.2).1⟩).2⟩
      exact (key _ (ψ.symm ⟨(x : V), ((memS _ _ _).1 x.2).1⟩).2).2 (by simpa [ht₂] using h1)
  let κ : DDW H t₁ (ThL H t₁) ≃ₗ[M.L.O] DDW H t₂ (ThL H t₂) := Submodule.Quotient.equiv _ _ e hPQ
  have hκ : ∀ w, κ (dwMk H t₁ (ThL H t₁) w) = dwMk H t₂ (ThL H t₂) (e w) := fun w => rfl
  have surj : ∀ m : MMsharp H t₁, ∃ w, η₁ (ddMk H t₁ m) = dwMk H t₁ (ThL H t₁) w := by
    intro m
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (η₁ (ddMk H t₁ m))
    exact ⟨w, hw.symm⟩
  have hh : ∀ a b : ThSharp H t₁ (ThL H t₁), H.h (e a : V) (e b : V) = H.h a b :=
    fun a b => hψh ⟨a, ((memS _ _ _).1 a.2).1⟩ ⟨b, ((memS _ _ _).1 b.2).1⟩
  refine ⟨(η₁.trans κ).trans η₂.symm, ?_, ?_⟩
  · intro x y x₂ y₂ hx hy
    obtain ⟨w, hw⟩ := surj x
    obtain ⟨w', hw'⟩ := surj y
    change η₂.symm (κ (η₁ (ddMk H t₁ x))) = _ at hx
    change η₂.symm (κ (η₁ (ddMk H t₁ y))) = _ at hy
    have hx' := (LinearEquiv.symm_apply_eq η₂).1 hx
    have hy' := (LinearEquiv.symm_apply_eq η₂).1 hy
    rw [hw, hκ] at hx'
    rw [hw', hκ] at hy'
    have a1 := hη₁b x y w w' hw hw'
    have a2 := hη₂b x₂ y₂ (e w) (e w') hx'.symm hy'.symm
    rw [hh] at a2
    have a3 := sub_mem a2 a1
    convert a3 using 1
    ring
  · intro m₁ m₂
    obtain ⟨w, hw⟩ := surj m₁
    have hmw : (m₁ : V) + w ∈ t₁.abelian₂ := (hη₁a m₁ w).1 hw
    change η₂.symm (κ (η₁ (ddMk H t₁ m₁))) = _ ↔ _
    rw [hw, hκ]
    constructor
    · intro h
      have h' := (LinearEquiv.symm_apply_eq η₂).1 h
      exact ⟨w, e w, (hψC _ _).2 ⟨((memS _ _ _).1 w.2).1, rfl⟩, hmw, (hη₂a m₂ (e w)).1 h'.symm⟩
    · rintro ⟨n₁, n₂, hc, h1, h2⟩
      obtain ⟨hn₁, hψn⟩ := (hψC n₁ n₂).1 hc
      have hd : n₁ - w ∈ H.W0 t₁.f t₁.f' := Submodule.sub_mem _ hn₁ ((memS _ _ _).1 w.2).1
      have hdL : n₁ - w ∈ t₁.abelian₂ := by
        have h4 := t₁.abelian₂.sub_mem h1 hmw
        simpa using h4
      have hψd : (ψ ⟨n₁ - w, hd⟩ : V) = n₂ - (e w : V) := by
        rw [← hψn]
        exact congrArg Subtype.val (map_sub ψ ⟨n₁, hn₁⟩ ⟨(w : V), ((memS _ _ _).1 w.2).1⟩)
      have h3 := (key _ hd).1 hdL
      rw [hψd] at h3
      have h5 := Λ₂.sub_mem h2 h3
      have h6 : (m₂ : V) + (e w : V) ∈ t₂.abelian₂ := by
        convert h5 using 1
        abel
      apply (LinearEquiv.symm_apply_eq η₂).2
      exact ((hη₂a m₂ (e w)).2 h6).symm

end Fwd

end Formalism.L2.SG.LsDatumA
end
end
