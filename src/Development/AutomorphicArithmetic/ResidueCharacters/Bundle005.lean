module

public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle004
public import Development.AutomorphicArithmetic.ResidueCharacters.InvariantsKilledOverCyclotomicAlt
public import Development.AutomorphicArithmetic.ResidueCharacters.LenLeTorsion
public import Development.AutomorphicArithmetic.ResidueCharacters.LocNum
public import Development.AutomorphicArithmetic.ResidueCharacters.LocRes
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle007
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle486
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle252
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle523
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle383
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle470
public import Development.AutomorphicArithmetic.ResidueCharacters.TwoRoot
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

@[expose] public section

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem tb_top (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (h4 : LocalSituation.Conclusion4 D HW F) (hCo : CrysOnCond D HW F)
    (hW : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
      EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie)
    (hF : ∀ K LL : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(OL LL))
    (N h n t e g : ℕ) (K LL : FinExt l) (hg : Good K (sN l N) LL) (hKs : Ks K (sN l N) = K.1)
    (U : Finset ℤ) (hn : U.card ≤ n) (hb : ∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) (he : e < t) (ht : t ≤ h)
    (hgl : g ≤ Nat.log l N + 1)
    (Yt Ve : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hcrys : IsCrys ((D.loc l).PD K) Yt.ρ)
    (hjmp : ∀ τ, JumpsInV ((D.loc l).PD K) Yt.ρ τ (U : Set ℤ))
    (p : Yt.V →ₗ[↥LL.1] ↥LL.1) (hp : ∀ g v, p (Yt.ρ g v) = p v)
    (hint : ∀ v ∈ Yt.L.T, p v ∈ Set.range (algebraMap ↥(OL LL) ↥LL.1)) (e₀ : Yt.V) (he₀ : e₀ ∈ Yt.L.T) (hpe : p e₀ = 1)
    (h1 : Module.finrank ↥LL.1 Ve.V = 1)
    (hχ : ∀ g x, Ve.ρ g x = ((algebraMap ℚ_[l] ↥LL.1 (((D.loc l).PD K).χ g : ℚ_[l]))⁻¹) ^ e • x)
    (φ : Yt.V →ₗ[↥(OL LL)] (Ve.V ⧸ Ve.L.T))
    (hφ : ∀ g, ∀ y ∈ Yt.L.T, p y = 0 → φ (Yt.ρ g y) = actD Ve.L g (φ y)) :
    ∃ c : ℕ, c + g ≤ cBL l N h n t ∧
      ((l : ↥(OL LL)) ^ c) • (fun g => φ (Yt.ρ g e₀ - e₀)) ∈ HfD ((D.loc l).PD K) Ve.L := by
  haveI : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  let Y := kerY Yt p e₀ hpe hp hint he₀
  have hcjY := cj_sub (hF K LL) (S := fun _ => (U : Set ℤ)) (GRep.ofLat Yt) (LinearMap.ker p)
    (ker_stable Yt p hp) ⟨hcrys, hjmp⟩
  have hsub : LocalSituation.Jset (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg) Y ⊆ U := fun a ha => by
    obtain ⟨τ, hτ⟩ := JsetEmb.jsetSplit_all D HW l K _ LL hg Y a ha
    exact hcjY.2 τ a hτ
  have hWY := hW K _ LL hg Y h h hcjY.1 fun a ha => hb a (hsub ha)
  have hCt := hCo l K _ LL hg Yt hcrys
  haveI : IsTopologicalRing (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg).LL := inferInstanceAs (IsTopologicalRing ↥LL.1)
  haveI : IsDomain (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg).O := inferInstanceAs (IsDomain ↥(OL LL))
  haveI : IsPrincipalIdealRing (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg).O :=
    inferInstanceAs (IsPrincipalIdealRing ↥(OL LL))
  have key := TBLoc.tb_part1 (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg) Yt p e₀ hpe hp hint he₀
    Subtype.val_injective _ (h4 l K _ LL hg).1 e h h _ Ve h1 hχ hCt hWY le_rfl φ hφ
  have e1 : LocalSituation.ell (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg) = l := (D.loc l).PD_p K
  refine ⟨LocalSituation.cTBY (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg) Y h h e, ?_, ?_⟩
  · have hvd := LocRes.vdeg_le K (s := sN l N) (m := LocalSituation.mN l (sN l N) (h + h))
      (le_max_left _ _) (by unfold LocalSituation.mN; omega)
    have e2 : (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg).W.s = sN l N := (HW l).W_s _ _ _ _
    have e3 : LocalSituation.gK (LocalSituation.sit D.loc HW l (D.locA l) K _ LL hg) = 0 := by
      unfold LocalSituation.gK
      rw [e2]
      show padicValNat _ (Module.finrank ℚ_[l] ↥(Ks K _)) - padicValNat _ (Module.finrank ℚ_[l] ↥K.1) = 0
      rw [hKs, Nat.sub_self]
    unfold LocalSituation.cTBY LocalSituation.vdegMs
    rw [e3, e1, e2]
    exact LocNum.cTB_le l N h n t e _ _ Fact.out U _ hsub hn hb he ht hvd hgl
  · have e4 : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) = (l : ↥(OL LL)) := by rw [(D.loc l).PD_p]
    rw [← e4]
    exact key

end UpperTheory.N

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitRowProbe GlobalTheory.SplitType GlobalTheory.SplitDecl

namespace UpperTheory.N

theorem place_type_conj (D : D7) (i : D.nd.Loc) (h2 : D.nd.l i ≠ 2) (hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1)
    (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hw' : w' ∈ placesOver D.host.E (D.nd.l i)) (hc : IsConjPl D.host w w') :
    (PlIn (N := D.nd) D.nbr i true w hw ∧ PlIn (N := D.nd) D.nbr i false w' hw') ∨
      (PlIn (N := D.nd) D.nbr i false w hw ∧ PlIn (N := D.nd) D.nbr i true w' hw') := by
  obtain ⟨s, hs, hn⟩ := exists_sqrt (D.nd.l i) D.host.d h2 hj
  obtain ⟨s₀, hs₀, h₀⟩ := exists_root
    ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).comp (algebraMap ℤ_[D.nd.l i] (D.nd.O i))) hs
    (map_sqrt_sq D.host ((D.nd.embK i).comp D.embE))
  have hs0 : s₀ ^ 2 = -(D.host.d : ℤ_[D.nd.l i]) := by rcases hs₀ with rfl | rfl <;> simp [hs]
  have hn0 : ‖2 * s₀‖ = 1 := by rcases hs₀ with rfl | rfl <;> simpa using hn
  have hne : s₀ ≠ -s₀ := fun e => by
    rw [show 2 * s₀ = 0 by linear_combination e] at hn0
    simp at hn0
  have key : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.nd.l i)),
      ∃ t : ℤ_[D.nd.l i], algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
        (D.nbr i v hv).j (algebraMap D.host.E D.nd.Om (D.host.sqd)) ∧
        ((t = s₀ ∧ PlIn (N := D.nd) D.nbr i true v hv) ∨ (t = -s₀ ∧ PlIn (N := D.nd) D.nbr i false v hv)) := by
    intro v hv
    obtain ⟨t, ht, h⟩ := exists_root
      ((algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i))).comp PadicInt.Coe.ringHom) hs0
      (map_sqrt_sq D.host ((D.nbr i v hv).j.comp (algebraMap D.host.E D.nd.Om)))
    refine ⟨t, h, ?_⟩
    rcases ht with ht | ht
    · refine Or.inl ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact e.1
      · exact absurd (ht.symm.trans ((root_of_embIn D i v hv h₀ h τ).2 e.1)) hne
    · refine Or.inr ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact absurd (((root_of_embIn D i v hv h₀ h τ).1 e.1).symm.trans ht) hne
      · exact e.1
  obtain ⟨t, ht, h⟩ := key w hw
  obtain ⟨t', ht', h'⟩ := key w' hw'
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases h' with ⟨e, h'⟩ | ⟨e, h'⟩
  · exact (root_ne D i w w' hw hw' hc hn0 ht (e ▸ ht')).elim
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr ⟨h, h'⟩
  · exact (root_ne D i w w' hw hw' hc (by simpa using hn0) ht (e ▸ ht')).elim

theorem columns_xor (D : D7) (i : D.nd.Loc) (h2 : D.nd.l i ≠ 2) (hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1) (s : Bool) :
    ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' →
      Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s) := by
  intro w hw w' h
  have hw' := GlobalTheory.SplitCount.mem_placesOver_of_conj D.host hw h
  have n1 := GlobalTheory.SplitRowProbe.not_both_columns D i w hw
  have n2 := GlobalTheory.SplitRowProbe.not_both_columns D i w' hw'
  rcases place_type_conj D i h2 hj w w' hw hw' h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases s
  · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h1, h3⟩⟩
  · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h3, h2⟩⟩
  · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h2, h3⟩⟩
  · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h3, h1⟩⟩

theorem decl_split (D : D7) (i : D.nd.Loc) (h2 : D.nd.l i ≠ 2) (hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1) (ep : Bool) :
    (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.ambTypeD (D := D) i ep := by
  have hl : D.nd.l i ≠ 0 := (D.nd.lPrime i).out.ne_zero
  have hx := columns_xor D i h2 hj ep
  refine ⟨⟨decl D i hl ep, ?_, ?_⟩, ?_⟩
  · intro v hv
    rw [mem_col, plTypeUe_iff]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hv, hv, h⟩⟩
  · intro v
    rw [mem_row]
    constructor
    · rintro ⟨hv, hnc⟩
      obtain ⟨v', hv', hc⟩ := GlobalTheory.SplitPlaces.exists_conjPl D.host _ v hv
      have hv'c : v' ∈ columns (N := D.nd) D.nbr i ep := by
        rcases hx v hv v' hc with h | h
        · exact absurd h.1 hnc
        · exact h.1
      exact ⟨v', (mem_col D i hl ep v').2 ⟨hv', hv'c⟩, GlobalTheory.Proof.ConjugatePlaces.isConjPl_symm hc⟩
    · rintro ⟨u, hu, hc⟩
      obtain ⟨hu, huc⟩ := (mem_col D i hl ep u).1 hu
      refine ⟨GlobalTheory.SplitCount.mem_placesOver_of_conj D.host hu hc, fun hvc => ?_⟩
      rcases hx u hu v hc with h | h
      · exact h.2 hvc
      · exact h.2 huc
  · intro u hu hU w hw hc τ₀ hτ
    have hnb : ∀ v hv τ, ¬ (EmbIn (N := D.nd) D.nbr i true v hv τ ∧ EmbIn (N := D.nd) D.nbr i false v hv τ) := by
      rintro v hv τ ⟨a, b⟩
      rcases embIn_xor D i v hv τ with h | h
      · exact h.2 b
      · exact h.2 a
    have hUin : ∀ τ, EmbIn (N := D.nd) D.nbr i ep u hu τ := fun τ => (embTypeUe_iff ep τ).1 (hU τ)
    have hwin : EmbIn (N := D.nd) D.nbr i ep w hw τ₀ := (embTypeUe_iff ep τ₀).1 hτ
    rcases place_type_conj D i h2 hj u w hu hw hc with ⟨hpu, hpw⟩ | ⟨hpu, hpw⟩ <;> cases ep
    · obtain ⟨τ⟩ := hpu.1
      exact hnb u hu τ ⟨hpu.2 τ, hUin τ⟩
    · exact hnb w hw τ₀ ⟨hwin, hpw.2 τ₀⟩
    · exact hnb w hw τ₀ ⟨hpw.2 τ₀, hwin⟩
    · obtain ⟨τ⟩ := hpu.1
      exact hnb u hu τ ⟨hUin τ, hpu.2 τ⟩

end UpperTheory.N

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitRowProbe GlobalTheory.SplitType GlobalTheory.SplitDecl

namespace UpperTheory.N.Two

theorem columns_xor (D : D7) (i : D.nd.Loc) (h2 : D.nd.l i = 2) (s : Bool) :
    ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' →
      Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s) := by
  intro w hw w' h
  have hw' := GlobalTheory.SplitCount.mem_placesOver_of_conj D.host hw h
  have n1 := GlobalTheory.SplitRowProbe.not_both_columns D i w hw
  have n2 := GlobalTheory.SplitRowProbe.not_both_columns D i w' hw'
  rcases Two.place_type_conj D i h2 w w' hw hw' h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases s
  · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h1, h3⟩⟩
  · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h3, h2⟩⟩
  · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h2, h3⟩⟩
  · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h3, h1⟩⟩

theorem decl_split (D : D7) (i : D.nd.Loc) (h2 : D.nd.l i = 2) (ep : Bool) :
    (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.ambTypeD (D := D) i ep := by
  have hl : D.nd.l i ≠ 0 := (D.nd.lPrime i).out.ne_zero
  have hx := columns_xor D i h2 ep
  refine ⟨⟨decl D i hl ep, ?_, ?_⟩, ?_⟩
  · intro v hv
    rw [mem_col, plTypeUe_iff]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hv, hv, h⟩⟩
  · intro v
    rw [mem_row]
    constructor
    · rintro ⟨hv, hnc⟩
      obtain ⟨v', hv', hc⟩ := GlobalTheory.SplitPlaces.exists_conjPl D.host _ v hv
      have hv'c : v' ∈ columns (N := D.nd) D.nbr i ep := by
        rcases hx v hv v' hc with h | h
        · exact absurd h.1 hnc
        · exact h.1
      exact ⟨v', (mem_col D i hl ep v').2 ⟨hv', hv'c⟩, GlobalTheory.Proof.ConjugatePlaces.isConjPl_symm hc⟩
    · rintro ⟨u, hu, hc⟩
      obtain ⟨hu, huc⟩ := (mem_col D i hl ep u).1 hu
      refine ⟨GlobalTheory.SplitCount.mem_placesOver_of_conj D.host hu hc, fun hvc => ?_⟩
      rcases hx u hu v hc with h | h
      · exact h.2 hvc
      · exact h.2 huc
  · intro u hu hU w hw hc τ₀ hτ
    have hnb : ∀ v hv τ, ¬ (EmbIn (N := D.nd) D.nbr i true v hv τ ∧ EmbIn (N := D.nd) D.nbr i false v hv τ) := by
      rintro v hv τ ⟨a, b⟩
      rcases embIn_xor D i v hv τ with h | h
      · exact h.2 b
      · exact h.2 a
    have hUin : ∀ τ, EmbIn (N := D.nd) D.nbr i ep u hu τ := fun τ => (embTypeUe_iff ep τ).1 (hU τ)
    have hwin : EmbIn (N := D.nd) D.nbr i ep w hw τ₀ := (embTypeUe_iff ep τ₀).1 hτ
    rcases Two.place_type_conj D i h2 u w hu hw hc with ⟨hpu, hpw⟩ | ⟨hpu, hpw⟩ <;> cases ep
    · obtain ⟨τ⟩ := hpu.1
      exact hnb u hu τ ⟨hpu.2 τ, hUin τ⟩
    · exact hnb w hw τ₀ ⟨hwin, hpw.2 τ₀⟩
    · exact hnb w hw τ₀ ⟨hpw.2 τ₀, hwin⟩
    · obtain ⟨τ⟩ := hpu.1
      exact hnb u hu τ ⟨hUin τ, hpu.2 τ⟩

end UpperTheory.N.Two

end
end
