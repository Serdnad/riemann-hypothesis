module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle066
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle052
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle104
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle105
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle101
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHaarUnimodularNormal
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle232
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle229
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverFrameCoordinates
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle091
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle233
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle184

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical Pointwise

noncomputable section

namespace GlobalTheory.LocOver.OrbitUniq

open GlobalTheory.HL

section Fr

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem change (g : Fin (r + 1) → S.V) (K : Subgroup S.GLV)
    (hon : ∀ n ∈ K, ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      ((∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1) ∧ ∀ j, n (g j) = ∑ i, s i j • g i)
    (σ a b : S.GLV) (ha : a ∈ K) (hb : b ∈ K) (h : ∀ j, σ (a (g j)) = b (g j)) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      ((∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1) ∧ ∀ j, σ (g j) = ∑ i, s i j • g i := by
  obtain ⟨u, hu, hu'⟩ := hon _ (K.mul_mem hb (K.inv_mem ha))
  obtain ⟨w, -, hw⟩ := hon _ (K.inv_mem ha)
  refine ⟨u, hu, fun j => ?_⟩
  rw [← hu' j]
  have e1 : g j = a (a⁻¹ (g j)) := by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
  calc σ (g j) = σ (a (∑ i, w i j • g i)) := by rw [← hw j, ← e1]
    _ = ∑ i, w i j • b (g i) := by simp only [map_sum, map_smul, h]
    _ = b (a⁻¹ (g j)) := by rw [hw j, map_sum]; simp only [map_smul]
    _ = (b * a⁻¹) (g j) := rfl

end Fr

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

theorem grp_e {P : FPair H r} {S : Frames M.L r k} (c : Coord P S) (g : V ≃ₗ[E] V) (x : V) :
    c.grp g (c.e x) = c.e (g x) := by
  show c.e (g (c.e.symm (c.e x))) = _
  simp

theorem grp_iso {P : FPair H r} {S : Frames M.L r k} (c : Coord P S) (g : V ≃ₗ[E] V) (hg : IsUnitary H g)
    (x y : S.V) : hf M.L S.Hm (c.grp g x) (c.grp g y) = hf M.L S.Hm x y := by
  obtain ⟨a, rfl⟩ := c.e.surjective x
  obtain ⟨b, rfl⟩ := c.e.surjective y
  have e := fun u v => c.h_eq u v
  simp only [Frames.h] at e
  rw [grp_e, grp_e, e, e, hg]

end GlobalTheory.LocOver.OrbitUniq

namespace GlobalTheory.LocOver

open GlobalTheory.HL GlobalTheory.LocOver.OrbitUniq

theorem orbit_over_unique : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (d d' : Datum P) (t : Term V M r), Over P d t → Over P d' t → Datum.Rel d d' := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hP d d' t h1 h2
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := CoordExist.exists_coord M hM H r k P hrk hP
  have he := (orbit_reps_over M hM H r P).1
  obtain ⟨g1, hg1, d1, hd1, ht1⟩ := h1
  obtain ⟨g2, hg2, d2, hd2, ht2⟩ := h2
  suffices h12 : Datum.Rel d1 d2 from he.trans hd1 (he.trans h12 (he.symm hd2))
  obtain ⟨-, hNA, hNB, -⟩ := CoordUnip.transport M hM H r k P S c
  obtain ⟨-, -, -, hlat, -⟩ := CoordMass.transport M hM H r k P S c
  obtain ⟨-, -, hRel, -⟩ := CoordDatum.transport M hM H r k P S c
  obtain ⟨hT, -, -⟩ := CoordTermWt.terms_correspond M hM H r k P S c
  obtain ⟨-, -, ⟨n1, hn1, hf1, -⟩, ⟨n1', hn1', hf1', -⟩, -⟩ := id ht1
  obtain ⟨-, -, ⟨m, hm, hfm, -⟩, ⟨m', hm', hfm', -⟩, -⟩ := id ht2
  obtain ⟨on1, on2, -⟩ := FrameOnto.unipotent_onto M.L r k S
  set G1 := c.grp g1 with hG1
  set G2 := c.grp g2 with hG2
  set σ : S.GLV := G2 * G1⁻¹ with hσ
  have hσG : ∀ x, σ (G1 x) = G2 x := fun x => by
    show (G2 * G1⁻¹ * G1) x = G2 x
    rw [inv_mul_cancel_right]
  have hσiso : ∀ x y, hf M.L S.Hm (σ x) (σ y) = hf M.L S.Hm x y := by
    intro x y
    obtain ⟨a, rfl⟩ := G1.surjective x
    obtain ⟨b, rfl⟩ := G1.surjective y
    rw [hσG, hσG, grp_iso c g2 hg2, grp_iso c g1 hg1]
  have rA : ∀ j, σ (c.grp n1 (S.f j)) = c.grp m (S.f j) := fun j => by
    have a1 := congrFun hf1 j
    have a2 := congrFun hfm j
    simp only [move] at a1 a2
    rw [c.f_eq, grp_e, grp_e, ← a1, ← a2, ← grp_e c g1, hσG, grp_e]
  have rB : ∀ j, σ (c.grp n1' (S.f' j)) = c.grp m' (S.f' j) := fun j => by
    have a1 := congrFun hf1' j
    have a2 := congrFun hfm' j
    simp only [move] at a1 a2
    rw [c.f'_eq, grp_e, grp_e, ← a1, ← a2, ← grp_e c g1, hσG, grp_e]
  obtain ⟨u, hu, hσf⟩ := change S S.f S.N on1 σ _ _ ((hNA n1).1 hn1) ((hNA m).1 hm) rA
  obtain ⟨u', hu', hσf'⟩ := change S S.f' S.N' on2 σ _ _ ((hNB n1').1 hn1') ((hNB m').1 hm') rB
  have hZ : cT M.L u * S.Zh * u' = S.Zh := by
    ext a b
    rw [← FrameStab.pair_eq S u u' a b, ← hσf, ← hσf', hσiso]
    rfl
  obtain ⟨st, hst, hsf, hsf'⟩ := ((FrameStab.stab_eq M.L r k S).2 u u' hu hu').1 hZ
  set η : S.GLV := st⁻¹ * σ with hη
  have hηf : ∀ j, η (S.f j) = S.f j := fun j => by
    show st⁻¹ (σ (S.f j)) = S.f j
    rw [hσf, ← hsf, ← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  have hηf' : ∀ j, η (S.f' j) = S.f' j := fun j => by
    show st⁻¹ (σ (S.f' j)) = S.f' j
    rw [hσf', ← hsf', ← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  have fix : ∀ v ∈ S.ME, η v = v := by
    have : S.ME ≤ LinearMap.eqLocus (η : S.V →ₗ[E] S.V) LinearMap.id := by
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨i, -, rfl⟩
        exact hηf i
      · rintro _ ⟨i, -, rfl⟩
        exact hηf' i
    exact fun v hv => this hv
  have hσI : σ ∈ isomG M.L S.Hm := hσiso
  have hη0 : η ∈ S.H0 := by
    refine ⟨(isomG M.L S.Hm).mul_mem ((isomG M.L S.Hm).inv_mem hst.1.1.1) hσI, fun v => ⟨fun h => ?_, fun h => ?_⟩,
      fun v hv => ?_⟩
    · rwa [η.injective (fix _ h)] at h
    · rw [fix v h]; exact h
    · rw [fix v hv, sub_self]; exact zero_mem _
  have hI1 := (hT d1 _ ht1).1
  have hI2 := (hT d2 _ ht2).1
  have e1 : c.lat (move g1 t).abelian₂ = G1 • c.lat t.abelian₂ := hlat g1 t.abelian₂
  have e2 : c.lat (move g2 t).abelian₂ = G2 • c.lat t.abelian₂ := hlat g2 t.abelian₂
  have hA := (ComplAct.main M.L r k S (c.dat d1) _ hI1 η hη0).1
  have hB := (FrameAct.stabiliser_acts_on_terms M.L r k S _ _ hA st hst).1
  have e3 : st • η • c.lat (move g1 t).abelian₂ = c.lat (move g2 t).abelian₂ := by
    rw [e1, e2, smul_smul, smul_smul, hη, mul_inv_cancel_left, hσ, inv_mul_cancel_right]
  rw [e3] at hB
  have hd := (TermBasic.term_basic M.L r k S (c.dat d2) _ hI2).2.2.2.2.2.2.2 _ hB
  exact (hRel d1 d2).2 ⟨η, hη0, hd⟩

end GlobalTheory.LocOver
end
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ComplMove

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

lemma bbne_img (g : V ≃ₗ[E] V) (f f' : Fin (r + 1) → V) (hfix : ∀ b, g (f b) = f b ∧ g (f' b) = f' b)
    (Λ : Submodule M.L.O V) (T T' : F) :
    LocNG.BBne (H := H) (⟨LocNG.img g Λ, f, f', T, T'⟩ : Term V M r) ↔
      LocNG.BBne (H := H) (⟨Λ, f, f', T, T'⟩ : Term V M r) := by
  have hfam : ∀ i, g (H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) i) = H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) i := by
    intro i
    unfold HermSp.MMfam
    rcases hs : M.split with _ | gg <;> rcases i with i | i <;>
      simp [map_smul, map_sub, (hfix i).1, (hfix i).2]
  have hspan : ∀ v ∈ Submodule.span E (Set.range (H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r))), g v = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hfam i
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul s x _ hx => rw [map_smul, hx]
  have e : H.MMfam (⟨LocNG.img g Λ, f, f', T, T'⟩ : Term V M r) = H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) := rfl
  unfold LocNG.BBne
  simp only [e]
  constructor
  · rintro ⟨v, hv, hs, hns⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv
    have ew : g w = w := g.injective (hspan _ hs)
    change g w ∈ _ at hs
    change g w ∉ _ at hns
    rw [ew] at hs hns
    exact ⟨w, hw, hs, hns⟩
  · rintro ⟨v, hv, hs, hns⟩
    exact ⟨v, Submodule.mem_map.2 ⟨v, hv, hspan v hs⟩, hs, hns⟩

lemma fwd (hM : M.OK) (P : LocNG.FPair H r) (S : Frames M.L r k) (c : Coord P S) (g : V ≃ₗ[E] V)
    (hg : c.grp g ∈ S.H0) (d d' : LocNG.Datum P) (hmv : c.grp g • c.dat d = c.dat d')
    (f f' : Fin (r + 1) → V) (Λ : Submodule M.L.O V)
    (hT : LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) :
    LocNG.IsTermOver P d' (⟨LocNG.img g Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) := by
  letI := hM.loc
  haveI := hM.char0
  have hT0 := hT
  obtain ⟨-, -, ⟨n, hn, hf, hΛn⟩, ⟨n', hn', hf', hΛn'⟩, -⟩ := hT
  change f = _ at hf
  change f' = _ at hf'
  change Λ = _ at hΛn
  change Λ = _ at hΛn'
  subst hf hf'
  have hW := (GlobalTheory.T.term_over_frame_coordinates M hM H r k P S c d n n' Λ).1 ⟨hT0, hn, hn', hΛn, hΛn'⟩
  obtain ⟨m, m', hW', hm, hm'⟩ := GlobalTheory.HL.ComplAct.termW S hW hg
  rw [hmv, ← GlobalTheory.HL.CoordTerm.lat_img c] at hW'
  have e1 : c.grp (c.grp.symm m) = m := c.grp.apply_symm_apply m
  have e2 : c.grp (c.grp.symm m') = m' := c.grp.apply_symm_apply m'
  rw [← e1, ← e2] at hW'
  have hR := ((GlobalTheory.T.term_over_frame_coordinates M hM H r k P S c d' (c.grp.symm m) (c.grp.symm m') (LocNG.img g Λ)).2 hW').1
  have k1 : (fun b => c.grp.symm m (P.A.f b)) = fun b => n (P.A.f b) := by
    funext b
    apply c.e.injective
    rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f_eq, e1, hm b]
  have k2 : (fun b => c.grp.symm m' (P.B.f b)) = fun b => n' (P.B.f b) := by
    funext b
    apply c.e.injective
    rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f'_eq, e2, hm' b]
  rw [k1, k2] at hR
  exact hR

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ g ∈ P.UW0, ∀ d d' : LocNG.Datum P, LocNG.Datum.Moves g d d' → (∀ b, g (f b) = f b ∧ g (f' b) = f' b) ∧ LocNG.img g '' {Λ | LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} = {Λ | LocNG.IsTermOver P d' (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hP f f' ⟨n, hn, hf⟩ ⟨n', hn', hf'⟩ g hg d d' hmv
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hk hP
  obtain ⟨hU, -⟩ := GlobalTheory.T.framePairCoordinates_transport_unitary_mass M hM H r k P S c
  obtain ⟨-, hMv, -⟩ := GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData M hM H r k P S c
  obtain ⟨-, hNA, hNB, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have hh := (hU g).1 hg
  have hmv' := (hMv g hg d d').1 hmv
  have fixv : ∀ x : V, c.e x ∈ S.ME → g x = x := by
    intro x hx
    apply c.e.injective
    rw [← GlobalTheory.HL.CoordTerm.grp_e c]
    exact GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh _ hx
  have hfix : ∀ b, g (f b) = f b ∧ g (f' b) = f' b := by
    intro b
    subst hf hf'
    refine ⟨fixv _ ?_, fixv _ ?_⟩
    · rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f_eq]
      exact Submodule.mem_sup_left (GlobalTheory.HL.ComplAct.nof_mem S (Or.inl ⟨rfl, rfl⟩) ((hNA n).1 hn)
        (GlobalTheory.HL.ComplAct.mem_spanTo S S.f b))
    · rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f'_eq]
      exact Submodule.mem_sup_right (GlobalTheory.HL.ComplAct.nof_mem S (Or.inr ⟨rfl, rfl⟩) ((hNB n').1 hn')
        (GlobalTheory.HL.ComplAct.mem_spanTo S S.f' b))
  have hginv : c.grp g⁻¹ ∈ S.H0 := by rw [map_inv]; exact S.H0.inv_mem hh
  have hmvinv : c.grp g⁻¹ • c.dat d' = c.dat d := by
    rw [← hmv', map_inv, inv_smul_smul]
  have hback : ∀ Λ : Submodule M.L.O V, LocNG.img g (LocNG.img g⁻¹ Λ) = Λ := by
    intro Λ
    rw [← GlobalTheory.HL.CoordTerm.lat_inj c, GlobalTheory.HL.CoordTerm.lat_img, GlobalTheory.HL.CoordTerm.lat_img, map_inv,
      smul_inv_smul]
  refine ⟨hfix, ?_⟩
  ext Λ
  constructor
  · rintro ⟨Λ0, ⟨hT, hB⟩, rfl⟩
    exact ⟨fwd hM P S c g hh d d' hmv' f f' Λ0 hT, by rwa [bbne_img g f f' hfix]⟩
  · rintro ⟨hT, hB⟩
    refine ⟨LocNG.img g⁻¹ Λ, ⟨fwd hM P S c g⁻¹ hginv d' d hmvinv f f' Λ hT, ?_⟩, hback Λ⟩
    rw [← bbne_img g f f' hfix, hback Λ]
    exact hB

end GlobalTheory.HL.ComplMove
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

theorem standingHypotheses_of_glob0_nodes_Tr_bounds : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C' Cl Cg : ℝ, 0 < Cl → Cl ≤ CD →
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (large₂ : SizeData₂ D) (cT CT : ℝ), large₂.sc.L = x ^ eps → 8 * large₂.CGam ≤ C' →
      Glob0 D x eps CD Cg → Nodes D x eps →
      (∀ u, large₂.sc.b ^ (cT * (D.R.m : ℝ)) ≤ Tr D u ∧ Tr D u ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ))) →
      StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 cT CT := by
  intro eps CD he he52 hCD C' Cl Cg hCl hClD
  obtain ⟨x1, h1⟩ := GlobalTheory.T.eventually_rankNums_imp_parameter_lower_bounds eps CD he he52 hCD C'
  obtain ⟨x2, h2⟩ := GlobalTheory.T.eventually_rankNums_imp_parameter_lower_bounds eps CD he he52 hCD Cl
  obtain ⟨x3, h3⟩ := GlobalTheory.T.globalRankNumberBounds_rootDiscriminant_clauses eps CD he he52 hCD Cl hCl
  obtain ⟨x4, h4⟩ := GlobalTheory.T.globalRankNumberBounds_size_comparisons eps CD he he52 hCD Cl hCl
  obtain ⟨x5, h5⟩ := GlobalTheory.T.globalRankNumberBounds_gaps_exceed eps CD he he52 hCD Cl hCl
  refine ⟨max x1 (max x2 (max x3 (max x4 x5))), fun x hx D large₂ cT CT hL h8 G N hT => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : x3 ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hx
  have hx4 : x4 ≤ x := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hx
  have hx5 : x5 ≤ x := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hx
  have R := G.nums
  obtain ⟨a1, -, -, -, -, -, -, -⟩ := h1 x hx1 _ _ _ _ _ R
  obtain ⟨-, a2, a3, a4, a5, -, -, -⟩ := h2 x hx2 _ _ _ _ _ R
  obtain ⟨c1, c2, c3⟩ := h3 x hx3 _ _ _ _ _ R
  obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := h4 x hx4 _ _ _ _ _ R
  have e := h5 x hx5 _ _ _ _ _ R (D.R.r : ℝ) k_le_r r_le_two_k
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hb : large₂.sc.b = bx x eps := by
    show Real.exp large₂.sc.L = Real.exp (x ^ eps)
    rw [hL]
  have hrd := G.rd_lo
  have hv : D.host.v = D.host.rdE / 2 := rfl
  have hbj : ∀ τ j, 1 ≤ j → j ≤ D.R.m → Real.sqrt (bx x eps) ≤ bOne D τ j ∧ bOne D τ j ≤ bx x eps ^ 2 := by
    intro τ j h1 h2
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [bOne_succ τ j (by omega)]
    exact N.b_win τ ⟨j, by omega⟩
  have hrS : (D.R.rS : ℝ) = (D.R.m : ℝ) / 2 - 1 := by
    obtain ⟨a, ha⟩ := D.R.m_even
    have h' : D.R.rS + 1 = a := by unfold Ranks.rS; omega
    have e1 : (D.R.rS : ℝ) + 1 = a := by exact_mod_cast h'
    have e2 : (D.R.m : ℝ) = a + a := by exact_mod_cast ha
    linarith
  rw [hb] at hT
  unfold StandingHypotheses
  dsimp only
  rw [hb, hL]
  refine ⟨h8, a1, by exact_mod_cast R.mf, by exact_mod_cast R.fk, by rw [hrS]; exact a2, a3, a4, ?_, ?_, c2, c3,
    (G.g_win 0).1, (G.g_win 0).2, (G.g_win 1).1, (G.g_win 1).2, ?_, ?_, ?_, ?_, d7 hClD, ?_, ?_, hT, a5, hCl⟩
  · intro τ j h1 h2
    exact le_trans d2 (hbj τ j h1 h2).1
  · rw [hv, Real.log_div (by linarith) (by norm_num)]
    exact c1
  · intro τ j h1 h2
    rw [Real.rpow_two]
    exact ⟨le_trans d3 (hbj τ j h1 h2).1, (hbj τ j h1 h2).2⟩
  · intro τ
    have a := N.bm τ
    have e' : D.R.m = D.R.m - 1 + 1 := by omega
    have b := bOne_succ τ (D.R.m - 1) (by omega)
    rw [← e'] at b
    have b0 : bOne D τ 1 = (((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) := bOne_succ τ 0 (by omega)
    rw [b, b0]
    exact a
  · intro u τ
    have e1 : uOne D u τ 1 = uFirst D τ := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, uOne_succ u τ 0 k_pos, D.hcW_first u τ k_pos]
      rfl
    rw [e1]
    by_cases ht : Top D τ
    · exact le_trans (N.top τ ht).2.1 d6
    · have o := (G.off τ ht).2.1
      have v0 := (G.cloud τ ⟨0, by omega⟩).2
      have v0' : vFirst D τ ≤ 4 * (D.R.k : ℝ) * (D.s.Del : ℝ) := v0
      linarith
  · rw [hv]; linarith
  · intro τ j h1 h2
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [bOne_succ τ (j + 1) (by omega), bOne_succ τ j (by omega)]
    have g := G.gap τ j (by omega)
    push_cast at g
    linarith [e.2.2.2]
  · intro τ i h
    by_cases c1 : i.1 + 1 < D.R.k - 1
    · rw [lamS_lo τ i (by omega), lamS_lo τ ⟨i.1 + 1, h⟩ c1, vOne_succ τ i.1 (by omega),
        vOne_succ τ (i.1 + 1) c1]
      have g := D.s.cloud_gap D.u₀ τ i.1 c1
      simp only [D.hcW_v] at g
      have g' := congrArg (fun q : ℚ => (q : ℝ)) g
      push_cast at g'
      linarith [e.1]
    · by_cases c2 : i.1 < D.R.k - 1
      · rw [lamS_lo τ i c2, lamS_hi τ ⟨i.1 + 1, h⟩ c1, vOne_succ τ i.1 c2]
        have e2 : i.1 + 1 - (D.R.k - 1) + 1 = 0 + 1 := by omega
        simp only [e2]
        rw [bOne_succ τ 0 (by omega)]
        have v0 := (G.cloud τ ⟨i.1, c2⟩).1
        have b0 := (N.b_win τ ⟨0, by omega⟩).1
        linarith [e.2.1]
      · have hi := i.isLt
        rw [lamS_hi τ i c2, lamS_hi τ ⟨i.1 + 1, h⟩ c1]
        have e2 : i.1 + 1 - (D.R.k - 1) + 1 = (i.1 - (D.R.k - 1) + 1) + 1 := by omega
        simp only [e2]
        rw [bOne_succ τ (i.1 - (D.R.k - 1)) (by omega), bOne_succ τ (i.1 - (D.R.k - 1) + 1) (by omega)]
        have g := G.gap τ (i.1 - (D.R.k - 1)) (by omega)
        push_cast at g
        linarith [e.2.2.1]

end GlobalTheory.Diag.PG
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.stabilizer_haar_unimodular_normal : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → IsHaarOn (Rset k r g₀) (lebR0 k r j β) ∧ IsUnimod (Rset k r g₀) (lebR0 k r j β) := by
  first | exact @GlobalTheory.Amp.StabHaar.lebesgue_haar_unimodular_stabilizer | exact GlobalTheory.Amp.StabHaar.lebesgue_haar_unimodular_stabilizer | (intros; apply GlobalTheory.Amp.StabHaar.lebesgue_haar_unimodular_stabilizer <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov


theorem _root_.GlobalTheory.T.exists_fundamental_set_rows_middleSpace : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (S : Submodule K V) (HW : HermSpace K S) (k r : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ), (∀ x y : S, HW.B x y = H.B x y) → IsPlaces σ → Module.finrank K S = k + 1 → (∀ v, IsReal H k r (σ v) (Φ v)) → (∀ v, ∀ w ∈ S, inWb k r (Φ v w)) → ∀ (L : Submodule (𝓞 K) V) (𝔡 : Ideal (𝓞 K)) (n : ℤ) (ρ : ℝ), GlobalTheory.HermLat.IsUnimod HW (L.comap (S.subtype.restrictScalars (𝓞 K))) → 𝔡 ≠ ⊥ → 0 < ρ → ∃ F : Set (ι → Fin (k + 1) → ℂ), MeasurableSet F ∧ (∀ a : ι → Fin (k + 1) → ℂ, ∃! x : V, x ∈ ipow 𝔡 n • (L ⊓ rs (𝓞 K) S) ∧ ((fun v => (ρ : ℂ) • fun l => Φ v x (wI k r l)) + a) ∈ F) ∧ volume F = ENNReal.ofReal ((Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι * (Ideal.absNorm 𝔡 : ℝ) ^ n * ρ ^ (2 * Fintype.card ι)) ^ (k + 1)) := by
  first | exact @GlobalTheory.DegVol.RefCov.rowsFund | exact GlobalTheory.DegVol.RefCov.rowsFund | (intros; apply GlobalTheory.DegVol.RefCov.rowsFund <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianFrames_complementUnitary_acts_on_terms : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ h ∈ S.H0, S.IsTerm (h • d) (h • Λ) ∧ S.om (h • d) (h • Λ) = S.om d Λ ∧ S.mu (h • Λ) = S.mu Λ ∧ S.M (h • d) (h • Λ) = S.M d Λ ∧ S.sat (h • Λ) = S.sat Λ ∧ S.Fr (h • d) (h • Λ) = S.Fr d Λ := by
  first | exact @GlobalTheory.HL.ComplAct.main | exact GlobalTheory.HL.ComplAct.main | (intros; apply GlobalTheory.HL.ComplAct.main <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.lintegral_translate_le_multiplicity_fundamental : ∀ (B : RowsAut) (S : Set B.I.Ginf) (y : B.I.GA) (Φ : B.I.GA → ENNReal), 1 ≤ B.I.n → 1 ≤ B.g → MeasurableSet S → (∀ a ∈ S, ∀ a' ∈ S, ∀ v, dOp (uMat ((a * a'⁻¹) v)) ≤ Real.log 2) → Measurable Φ → (∀ γ ∈ B.I.GFset, ∀ z, Φ (γ * z) = Φ z) → (∀ k ∈ B.I.Kg B.g, ∀ z, Φ (z * (1, k)) = Φ z) → B.μf (B.I.Kg B.g) * ∫⁻ a in S, Φ (y * (a, 1)) ∂(muInf B.I) ≤ ENNReal.ofReal ((1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f))) * ∫⁻ z in B.fund, Φ z ∂(B.I.muA B.μf) := by
  first | exact @GlobalTheory.BoundedUnfold.lintegral_le_multiplicity | exact GlobalTheory.BoundedUnfold.lintegral_le_multiplicity | (intros; apply GlobalTheory.BoundedUnfold.lintegral_le_multiplicity <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.isRadial_map_unitaryLeviBlockProduct : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ → (∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) → ∀ c : ℝ, IsGauge ε₀ c → IsRadial (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) (fun g => Formalism.REAL.hs (uMat g - 1)) (n₀ ^ 2 + 2 * ∑ i, j i ^ 2) := by
  first | exact @GlobalTheory.LeviIso.MapRadial.isRadial_map_lev | exact GlobalTheory.LeviIso.MapRadial.isRadial_map_lev | (intros; apply GlobalTheory.LeviIso.MapRadial.isRadial_map_lev <;> assumption)
end
