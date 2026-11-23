module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverFrameCoordinates
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDatumOfTermReadOnLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle235
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle236
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc

@[expose] public section

section

noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.PairLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' T₂ : E}
  {Λ : Submodule (𝓞 E) S.V} {g : ℕ}

theorem mem_orth {U : Submodule E S.V} {x : S.V} : x ∈ orth S U ↔ ∀ u ∈ U, S.hT u x = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem hT_z_X (F : LFlag S r T) {x : S.V} (hx : x ∈ Xsp F) : S.hT F.fl.z x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    have h := S.herm.eq (F.fl.e a) F.fl.z
    rw [F.fl.z_orth a] at h
    simpa using h.symm
  | zero => simp
  | add y z _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

theorem X_eq_Xflag (F : LFlag S r T) : Xsp F = Xflag F r := by
  change Submodule.span E (Set.range F.fl.e) = Submodule.span E (F.fl.e '' {i | i.1 < r})
  congr 1
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · rintro ⟨a, _, rfl⟩
    exact ⟨a, rfl⟩

theorem mem_Lsub_of {F : LFlag S r T} {l y : S.V} (hl : l ∈ Lrep Λ F) (h : y - l ∈ Xsp F) :
    y ∈ Lsub Λ F := by
  have hlo : l ∈ orth S (Xsp F) := (Submodule.mem_inf.1 hl).2
  have hy : y = l + (y - l) := by abel
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [hy]
    exact Submodule.add_mem_sup hl h
  · rw [hy]
    exact (orth S (Xsp F)).add_mem hlo (FrEqv.X_le_orth h)

theorem IotaRel_zero (F : LFlag S r T) (F' : LFlag S r T') : IotaRel Λ g F F' 0 :=
  ⟨0, Submodule.zero_mem _, by simp, 0, Submodule.zero_mem _, by simp, by simp⟩

theorem IotaRel_add {F : LFlag S r T} {F' : LFlag S r T'} {x y : S.V}
    (hx : IotaRel Λ g F F' x) (hy : IotaRel Λ g F F' y) : IotaRel Λ g F F' (x + y) := by
  obtain ⟨l, hl, h1, l', hl', h2, h3⟩ := hx
  obtain ⟨m, hm, k1, m', hm', k2, k3⟩ := hy
  refine ⟨l + m, Submodule.add_mem _ hl hm, ?_, l' + m', Submodule.add_mem _ hl' hm', ?_, ?_⟩
  · have := (Xsp F).add_mem h1 k1
    rwa [show x - l + (y - m) = x + y - (l + m) by abel] at this
  · have := (Xsp F').add_mem h2 k2
    rwa [show x - l' + (y - m') = x + y - (l' + m') by abel] at this
  · have := Submodule.add_mem _ h3 k3
    rwa [show l - l' + (m - m') = l + m - (l' + m') by abel] at this

theorem IotaRel_smul {F : LFlag S r T} {F' : LFlag S r T'} {x : S.V} (o : 𝓞 E)
    (hx : IotaRel Λ g F F' x) : IotaRel Λ g F F' (o • x) := by
  obtain ⟨l, hl, h1, l', hl', h2, h3⟩ := hx
  refine ⟨o • l, Submodule.smul_mem _ o hl, ?_, o • l', Submodule.smul_mem _ o hl', ?_, ?_⟩
  · rw [← smul_sub]
    exact (toO S (Xsp F)).smul_mem o h1
  · rw [← smul_sub]
    exact (toO S (Xsp F')).smul_mem o h2
  · rw [← smul_sub]
    exact Submodule.smul_mem _ o h3

theorem La_props {F : LFlag S r T} {F' : LFlag S r T'} {x : S.V} (hx : x ∈ La Λ g F F') :
    x ∈ L0sub Λ F ∧ x ∈ L0sub Λ F' ∧ IotaRel Λ g F F' x := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx.2
  | zero => exact ⟨Submodule.zero_mem _, Submodule.zero_mem _, IotaRel_zero F F'⟩
  | add y z _ _ h1 h2 =>
    exact ⟨Submodule.add_mem _ h1.1 h2.1, Submodule.add_mem _ h1.2.1 h2.2.1, IotaRel_add h1.2.2 h2.2.2⟩
  | smul c y _ h =>
    exact ⟨Submodule.smul_mem _ c h.1, Submodule.smul_mem _ c h.2.1, IotaRel_smul c h.2.2⟩

theorem map_Lrep {F' F'' : LFlag S r T'} {β : S.V ≃ₗ[E] S.V} (hβ : IsAutLam S Λ β)
    (hX : (Xsp F').map (β : S.V →ₗ[E] S.V) = Xsp F'') {l : S.V} (hl : l ∈ Lrep Λ F') :
    β l ∈ Lrep Λ F'' := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hl
  refine Submodule.mem_inf.2 ⟨(FrEqv.aut_mem_iff hβ l).2 h1, ?_⟩
  refine mem_orth.2 fun u hu => ?_
  rw [← hX] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  have := hβ.1 v l
  exact this.trans (mem_orth.1 h2 v hv)

theorem Mlat_le_La_sup (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
    (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hP : IsPair Λ F F' F'' β g) : Mlat Λ F F' F'' β g ≤ La Λ g F F'' ⊔ toO S (Xsp F) := by
  obtain ⟨hβ, hfl, hz, hc⟩ := hP
  have hX : (Xsp F').map (β : S.V →ₗ[E] S.V) = Xsp F'' := by
    rw [X_eq_Xflag F', X_eq_Xflag F'']
    exact hfl r
  intro x₁ hx
  obtain ⟨hLa, hTh⟩ := Submodule.mem_inf.1 hx
  obtain ⟨h0, h0', l, hl, hxl, l', hl', hxl', hll⟩ := La_props hLa
  have hz1 : S.hT F.fl.z x₁ = 0 := (Submodule.mem_inf.1 h0).2
  have hz1' : S.hT F'.fl.z x₁ = 0 := (Submodule.mem_inf.1 h0').2
  obtain ⟨⟨a, x₂⟩, hp, he⟩ := (Submodule.restrictScalars_mem _ _ _).1 hTh
  have hax : a = x₁ := he
  subst hax
  obtain ⟨⟨hprod, h12⟩, hβ12⟩ := Submodule.mem_inf.1 hp |>.imp_left Submodule.mem_inf.1
  have hx₂ : x₂ ∈ Hp Λ F F'' := hprod.2
  have h12 : a - x₂ ∈ Xsp F := h12
  have hβ12 : β a - x₂ ∈ Xsp F'' := hβ12
  have hβl : β l' ∈ Lrep Λ F'' := map_Lrep hβ hX hl'
  have hβd : β (a - l') ∈ Xsp F'' := by
    rw [← hX]
    exact ⟨a - l', hxl', rfl⟩
  have k1 : x₂ - l ∈ Xsp F := by
    have := (Xsp F).sub_mem hxl h12
    rwa [show a - l - (a - x₂) = x₂ - l by abel] at this
  have k2 : x₂ - β l' ∈ Xsp F'' := by
    have := (Xsp F'').sub_mem hβd hβ12
    rwa [map_sub, show β a - β l' - (β a - x₂) = x₂ - β l' by abel] at this
  have m1 : S.hT F.fl.z x₂ = 0 := by
    have := hT_z_X F h12
    rw [map_sub, hz1, zero_sub, neg_eq_zero] at this
    exact this
  have m2 : S.hT F''.fl.z x₂ = 0 := by
    have := hT_z_X F'' hβ12
    rw [map_sub, ← hz, hβ.1 F'.fl.z a, hz1', zero_sub, neg_eq_zero, hz] at this
    exact this
  have hmem : x₂ ∈ La Λ g F F'' := by
    refine Submodule.subset_span ⟨hx₂, Submodule.mem_inf.2 ⟨mem_Lsub_of hl k1, m1⟩,
      Submodule.mem_inf.2 ⟨mem_Lsub_of hβl k2, m2⟩, l, hl, k1, β l', hβl, k2, ?_⟩
    exact (hc l' hl' l hl).1 hll
  have hsum : a = x₂ + (a - x₂) := by abel
  rw [hsum]
  exact Submodule.add_mem_sup hmem h12

end GlobalTheory.LoopC.PairLat

end
end

section

open Formalism.MainNotions.S

namespace GlobalTheory.LocCoef

theorem h_es_eq_zero_of_mem_Fj {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type}
    [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r)
    (a : Fin r) (u : V) (hu : u ∈ Fr.Fj a.val) : H.h u (Fr.es a) = 0 := by
  unfold Formalism.MainNotions.S.LocNG.FrameD.Fj at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' : b.val < a.val := hb
    have hba : b ≠ a := fun h => by subst h; exact lt_irrefl _ hb'
    unfold Formalism.MainNotions.S.LocNG.FrameD.e
    rw [Fr.h_es b a, if_neg hba]
  | zero => exact H.h_zero_left _
  | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]

theorem h_es_mem_O_of_mem_LamStd {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type}
    [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r)
    (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r) (w : V) (hw : w ∈ Fr.LamStd L) :
    H.h w (Fr.es a) ∈ M.L.O := by
  unfold Formalism.MainNotions.S.LocNG.FrameD.LamStd at hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hx.1 a
  | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
  | add x y _ _ hx hy => rw [H.h_add_left]; exact M.L.O.add_mem hx hy
  | smul c x _ hx =>
    have : H.h (c • x) (Fr.es a) = (c : E) * H.h x (Fr.es a) := H.h_smul_left (c : E) x _
    rw [this]; exact M.L.O.mul_mem c.2 hx

end GlobalTheory.LocCoef

theorem GlobalTheory.locCoef_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r) (n : V ≃ₗ[E] V), n ∈ Fr.N → ∀ (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r) (v : V), v ∈ Fr.Fj (a.val + 1) → v ∈ Formalism.MainNotions.S.LocNG.img n (Fr.LamStd L) → H.h v (Fr.es a) ∈ M.L.O := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr n hn L a v hv hvimg
  unfold Formalism.MainNotions.S.LocNG.img at hvimg
  obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hvimg
  have hwv' : n w = v := hwv
  have hu := (GlobalTheory.T.unipotentRadical_isotropicFlag_moves_step_into_prev Fr n hn (a.val + 1) (Nat.succ_le_of_lt a.isLt) v hv).2
  simp only [Nat.add_sub_cancel] at hu
  have hsymm : n.symm v = w := by rw [← hwv']; exact n.symm_apply_apply w
  rw [hsymm] at hu
  have h0 := GlobalTheory.LocCoef.h_es_eq_zero_of_mem_Fj Fr a (w - v) hu
  have hwO := GlobalTheory.LocCoef.h_es_mem_O_of_mem_LamStd Fr L a w hw
  have hdecomp : H.h w (Fr.es a) = H.h (w - v) (Fr.es a) + H.h v (Fr.es a) := by
    rw [← H.h_add_left, sub_add_cancel]
  rw [hdecomp, h0, zero_add] at hwO
  exact hwO
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.LocalMove

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ h ∈ P.UW0, ∀ (d d' : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → LocNG.Datum.Moves h d d' → LocNG.IsTermOver P d' ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ∧ (LocNG.BBne (H := H) ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ↔ LocNG.BBne (H := H) τ) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hP h hh d d' τ hτ hmv
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hrk hP
  obtain ⟨hH0, -, -, hlat, -⟩ := GlobalTheory.HL.CoordMass.transport M hM H r k P S c
  obtain ⟨-, hmov, -⟩ := GlobalTheory.HL.CoordDatum.transport M hM H r k P S c
  obtain ⟨-, hNA, hNB, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have hh0 : c.grp h ∈ S.H0 := (hH0 h).1 hh
  have ge : ∀ (g : V ≃ₗ[E] V) (x : V), c.grp g (c.e x) = c.e (g x) := GlobalTheory.HL.CoordTerm.grp_e c
  obtain ⟨Λ, f, f', T, T'⟩ := τ
  obtain ⟨hT, hT', ⟨n, hn, hf, hΛ⟩, ⟨n', hn', hf', hΛ'⟩, hG⟩ := hτ
  dsimp only at hT hT' hf hΛ hf' hΛ' hG ⊢
  subst hT hT' hf hf'

  have fixA : ∀ b, h (n (P.A.f b)) = n (P.A.f b) := by
    intro b
    apply c.e.injective
    rw [← ge, ← ge, ← c.f_eq]
    exact GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh0 _ (Submodule.mem_sup_left
      (GlobalTheory.HL.ComplAct.nof_mem S (Or.inl ⟨rfl, rfl⟩) ((hNA n).1 hn) (GlobalTheory.HL.ComplAct.mem_spanTo S _ b)))
  have fixB : ∀ b, h (n' (P.B.f b)) = n' (P.B.f b) := by
    intro b
    apply c.e.injective
    rw [← ge, ← ge, ← c.f'_eq]
    exact GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh0 _ (Submodule.mem_sup_right
      (GlobalTheory.HL.ComplAct.nof_mem S (Or.inr ⟨rfl, rfl⟩) ((hNB n').1 hn') (GlobalTheory.HL.ComplAct.mem_spanTo S _ b)))
  simp only [fixA, fixB]
  refine ⟨?_, ?_⟩
  · have hW := (GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d n n' Λ).1
      ⟨⟨rfl, rfl, ⟨n, hn, rfl, hΛ⟩, ⟨n', hn', rfl, hΛ'⟩, hG⟩, hn, hn', hΛ, hΛ'⟩
    obtain ⟨m, m', hW', hm, hm'⟩ := GlobalTheory.HL.ComplAct.termW S hW hh0
    rw [(hmov h hh d d').1 hmv, ← hlat] at hW'
    obtain ⟨m0, rfl⟩ := c.grp.surjective m
    obtain ⟨m0', rfl⟩ := c.grp.surjective m'
    have e1 : (fun b => m0 (P.A.f b)) = fun b => n (P.A.f b) := by
      funext b; apply c.e.injective; rw [← ge, ← ge, ← c.f_eq]; exact hm b
    have e2 : (fun b => m0' (P.B.f b)) = fun b => n' (P.B.f b) := by
      funext b; apply c.e.injective; rw [← ge, ← ge, ← c.f'_eq]; exact hm' b
    have := ((GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d' m0 m0' (LocNG.img h Λ)).2 hW').1
    rw [e1, e2] at this
    exact this
  ·
    set t : Term V M r := ⟨Λ, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ with ht
    have fam : ∀ i, h (H.MMfam t i) = H.MMfam t i := by
      intro i
      unfold HermSp.MMfam
      cases M.split with
      | none => rcases i with b | b <;> simp [ht, fixA, fixB]
      | some g => rcases i with b | b <;> simp [ht, fixA, fixB, map_sub]
    have fixS : ∀ x ∈ Submodule.span E (Set.range (H.MMfam t)), h x = x := by
      intro x hx
      have := LinearMap.eqOn_span' (f := (h : V →ₗ[E] V)) (g := LinearMap.id)
        (s := Set.range (H.MMfam t)) (by rintro _ ⟨i, rfl⟩; exact fam i) hx
      simpa using this
    change (∃ v ∈ LocNG.img h Λ, _) ↔ ∃ v ∈ Λ, _
    constructor
    · rintro ⟨v, hv, hE, hO⟩
      obtain ⟨w, hw, rfl⟩ := hv
      have hw' : h w = w := by
        have := fixS _ hE
        exact h.injective (by simpa using this)
      simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hE hO ⊢
      rw [hw'] at hE hO
      exact ⟨w, hw, hE, hO⟩
    · rintro ⟨v, hv, hE, hO⟩
      exact ⟨v, ⟨v, hv, fixS v hE⟩, hE, hO⟩

end GlobalTheory.HL.LocalMove
end
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.hermitianDatum_of_term_read_on_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → (∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → H.IsTerm t ∧ (d.L : Set (H.Wb P.A.f)) = H.Lset t.abelian₂ P.A.f ∧ (d.L' : Set (H.Wb P.B.f)) = H.Lset t.abelian₂ P.B.f) ∧ ∀ (d d' : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d' t' → H.Lset t.abelian₂ P.A.f = H.Lset t'.abelian₂ P.A.f → H.Lset t.abelian₂ P.B.f = H.Lset t'.abelian₂ P.B.f → (∀ g, M.split = some g → H.iotaGraph g ⟨t.abelian₂, P.A.f, P.B.f, t.T, t.T'⟩ = H.iotaGraph g ⟨t'.abelian₂, P.A.f, P.B.f, t'.T, t'.T'⟩) → d = d' := by
  first | exact @GlobalTheory.LocOver.TermLat.datum_of_lattice | exact GlobalTheory.LocOver.TermLat.datum_of_lattice | (intros; apply GlobalTheory.LocOver.TermLat.datum_of_lattice <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integers_dense_localIntegers_mod_g : ∀ (D : D7) (p : PlF D), ∀ c ∈ (D.s.atP p).O, ∃ a : 𝓞 D.host.E, ∃ o ∈ (D.s.atP p).O, c = (D.s.atP p).ιE (a : D.host.E) + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
  first | exact @GlobalTheory.IotaDense.iota_dense | exact GlobalTheory.IotaDense.iota_dense | (intros; apply GlobalTheory.IotaDense.iota_dense <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_integer_one_mod_g_at_place_zero_elsewhere : ∀ (D : D7) (p : PlF D), ∃ a : 𝓞 D.host.E, (∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (a : D.host.E) - 1 = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o) ∧ ∀ p' : PlF D, p' ≠ p → ∃ o ∈ (D.s.atP p').O, (D.s.atP p').ιE (a : D.host.E) = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) * o := by
  first | exact @GlobalTheory.CrtG.exists_one_here_zero_elsewhere | exact GlobalTheory.CrtG.exists_one_here_zero_elsewhere | (intros; apply GlobalTheory.CrtG.exists_one_here_zero_elsewhere <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem countClauses_of_sizeHyp : ∀ (D : D7) (L : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (n0 : ℕ) (A C cb7 : ℝ),
    0 ≤ C → 0 < cb7 → 2 * Cg ≤ A → (n0 : ℝ) ≤ D.R.k → 2 ≤ Cl → 2 * C ≤ Cl →
    Real.log L.sc.L ≤ cb7 * D.R.k → ArithmeticConditionsOfDatum D → StandingHypotheses D L C' Cl Cg cb Cu cT CT →
    AdmissibleBoundsFromSource.CountTheoremHypotheses D L n0 A C cb7 ∧ 4 * D.R.r < D.host.g 1 := by
  intro D L C' Cl Cg cb Cu cT CT n0 A C cb7 hC hcb hA hn0 hCl2 hCl3 hll hAr hH
  have d1 := data1 L
  have d11 : SplitsE D (D.host.g 0) := hAr.2.1
  have d13 : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 := hAr.2.2.2
  obtain ⟨-, -, -, -, H5, -, H7, H8, -, -, H11, H12, H13, ContinuousCyclotomicCharacter₂, ContinuityOfCyclotomicCharacter, CyclotomicCharacterContinuous, -, -, H19, LocalHeightDeterminant, H21, -, -, -, -⟩ := hH
  have hk5 := Formalism.MainNotions.S.five_le_k (D := D)
  have hf1 := Formalism.MainNotions.S.one_le_f (D := D)
  have hkr := Formalism.MainNotions.S.k_le_r (D := D)
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hL1 := one_lt_scL L
  have hlogb := log_scb L
  have hb2 := two_le_scb L
  have hb0 : 0 < L.sc.b := lt_of_lt_of_le two_pos hb2
  refine ⟨?_, ?_⟩
  swap
  · have h5 : (4 : ℝ) * D.R.r < D.host.g 1 := four_r_lt_g_of_bounds hk5 (by linarith only [hb2]) r_le_two_k ContinuousCyclotomicCharacter₂
    exact_mod_cast h5
  have hlr : 1 ≤ Real.log (D.R.r : ℝ) := one_le_log_of_five_le (le_trans hk5 hkr)
  obtain ⟨hmsq, hLk, hClL⟩ := k_ge_of_chain_bound hm2 hL1 hCl2 H7
  have hrd2 : 2 ≤ D.host.rdE := by
    have h : D.host.v = D.host.rdE / 2 := rfl
    rw [h] at H19; linarith only [H19]
  have hlrd0 : 0 ≤ Real.log D.host.rdE := Real.log_nonneg (by linarith only [hrd2])
  have hDel0 : 0 ≤ (D.s.Del : ℝ) := le_trans (Real.rpow_nonneg (by positivity) _) LocalHeightDeterminant
  have hm1 : 1 ≤ D.R.m := le_trans (by norm_num) D.R.two_le_m
  have hb1nn : ∀ τ j, 1 ≤ j → j ≤ D.R.m → 0 ≤ bOne D τ j := fun τ j h1 h2 =>
    le_trans (by positivity) (H8 τ j h1 h2)
  have hbsq : ∀ τ j, 1 ≤ j → j ≤ D.R.m → bOne D τ j ≤ L.sc.b ^ 2 := fun τ j h1 h2 => by
    have := (CyclotomicCharacterContinuous τ j h1 h2).2
    rwa [Real.rpow_two] at this
  refine ⟨d13, ?_, ?_, ?_, ?_, ?_, ?_, d11, ?_, ?_, hb2, ?_⟩
  · have h2 : n0 ≤ D.R.k := by exact_mod_cast hn0
    have h3 := D.R.two_le_m
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  · have h1 : D.R.m ^ 2 ≤ D.R.k := by exact_mod_cast hmsq
    have h2 : D.R.rS + 1 ≤ D.R.m := by
      have := D.R.two_le_m
      unfold Ranks.rS; omega
    have h3 : (D.R.rS + 1) ^ 2 ≤ D.R.m ^ 2 := Nat.pow_le_pow_left h2 2
    have h4 : D.R.k ≤ D.R.r := by exact_mod_cast hkr
    omega
  · have h1 := Real.log_le_self hlrd0
    have h2 : L.sc.L / Cl ≤ L.sc.L := div_le_self (by linarith only [hL1]) (by linarith only [hCl2])
    linarith only [h1, h2, H11, hLk, hkr]
  · intro τ i
    refine lamS_abs_le τ _ (fun l h1 h2 => ⟨(d1 τ l h1 h2).1, ?_⟩) (fun j h1 h2 => ⟨hb1nn τ j h1 h2, hbsq τ j h1 h2⟩) i
    exact le_of_le_four_mul_of_mul_le_chain (by linarith only [hk5]) hDel0 hCl2 hm2 (d1 τ l h1 h2).2 (H8 τ 1 le_rfl hm1) (hbsq τ 1 le_rfl hm1)
  · unfold gg
    have h1 : (D.host.g 0 : ℝ) * D.host.g 1 ≤ L.sc.b ^ Cg * L.sc.b ^ Cg :=
      mul_le_mul H13 ContinuityOfCyclotomicCharacter (by positivity) (by positivity)
    rw [← Real.rpow_add hb0] at h1
    exact le_trans h1 (Real.rpow_le_rpow_of_exponent_le (by linarith only [hb2]) (by linarith only [hA]))
  · have h5 : (4 : ℝ) * D.R.r < D.host.g 0 := four_r_lt_g_of_bounds hk5 (by linarith only [hb2]) r_le_two_k H12
    exact_mod_cast h5
  · intro τ a c hac
    have hX : 0 ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 := by positivity
    have hle := gap_product_le_of_bounds hC hX hL1 hCl2 hCl3 H11
    have hG0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L := by positivity
    have hg := gapAtLeast_of τ _ hG0 (fun l h1 h2 => (d1 τ l h1 h2).1) (hb1nn τ 1 le_rfl hm1) (H21 τ) a c hac
    rw [Real.log_mul hb0.ne' (by linarith only [hrd2]), hlogb]
    linarith only [hle, hg]
  · refine le_trans H5 (Real.sqrt_le_sqrt ?_)
    have : D.R.rS ≤ D.R.r := by
      have h4 := D.R.m_add_three_le_k
      have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
      unfold Ranks.rS; omega
    exact_mod_cast this
  · rw [hlogb]
    have h1 := mul_le_mul_of_nonneg_left (k_le_rank_product hk5 hkr hf1 hlr) hcb.le
    linarith only [h1, hll]

end GlobalTheory
end
