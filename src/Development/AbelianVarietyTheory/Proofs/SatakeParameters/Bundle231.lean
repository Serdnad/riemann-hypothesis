module

public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffApplyDPIvOfKvalGe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle111
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle218
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle091
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle197
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle113
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle179
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle116
import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU.LowF

theorem kval_orbit (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D)
    (hA : OrbitPlaces.OrbitLetterBoundsAll 11 1) (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge 11 1 K ce)
    (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p) (h0 : IsResidueClassZero D p) (hne : hP D p ≠ 0)
    (hX : (p : ℝ) ≤ L.sc.X'' D.R.n) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (t : HH D)
    [NeZero (nP D p)] (B : OmBasis p (nP D p)) (be : MvPowerSeries (Fin 2) (K0 p)) (hbe : BeProp p be)
    (U : MvPowerSeries (Eidx (nP D p) (D.R.N i) (D.R.N (i + 1)) ⊕ Eidx (nP D p) (D.R.N i) (D.R.N (i + 1))) (K0 p))
    (hU : IntS p (inParam p U)) :
    product_zeroth_first_parts.KvalGe (D.R.N i) (D.R.N (i + 1)) p (fun s : ZMod (nP D p) => E.nu u i (OrbitPlaces.orbMap D p (true, t) s))
      (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U)))
      (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  obtain ⟨bv, h1, h2, h3, h4, hb⟩ := GlobalTheory.T.exists_letterCoordinates_series_onePlace_alt p h.five (nP D p) h.even B be hbe
  obtain ⟨U', hU', e⟩ := hb _ _ U hU
  exact GlobalTheory.T.orbitBound_overSecondEmbedding_anyBasePoint D L X K ce E 11 1 hA hS hC p h h0 hne hX u i hi t 1 (-1) bv (by simp) (Or.inr rfl) h1 h2 h3 h4 _
    ⟨U', hU', e⟩

theorem kval_general (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D)
    (hA : OrbitPlaces.OrbitLetterBoundsAll 11 1) (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge 11 1 K ce)
    (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p) (h0 : IsResidueClassZero D p) (hne : hP D p ≠ 0)
    (hX : (p : ℝ) ≤ L.sc.X'' D.R.n) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (t : HH D)
    (n r0 r1 : ℕ) [NeZero n] (hn : n = nP D p) (h0' : r0 = D.R.N i) (h1' : r1 = D.R.N (i + 1))
    (B : OmBasis p n) (be : MvPowerSeries (Fin 2) (K0 p)) (hbe : BeProp p be)
    (U : MvPowerSeries (Eidx n r0 r1 ⊕ Eidx n r0 r1) (K0 p)) (hU : IntS p (inParam p U)) :
    product_zeroth_first_parts.KvalGe r0 r1 p (fun s : ZMod n => E.nu u i (posPl D p (true, t) s.val))
      (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U)))
      (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  subst hn h0' h1'
  exact kval_orbit D L X K ce E hA hS hC p h h0 hne hX u i hi t B be hbe U hU

theorem lowBound_of_series_bound_one_place {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl)
    [NeZero (X.G.P.n' v)] (nu : ZMod (X.G.P.n' v) → YoungDiagram) (g : ℝ)
    (hcc : MvPowerSeries.constantCoeff be = 0)
    (hnu : ∀ s r, (((nu s).rowLen r : ℕ) : ℤ) = X.nuv v (j + 1) (toFin s) (r + 1))
    (hK : ∀ U : MvPowerSeries (Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) ⊕
        Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) (K0 p), IntS p (inParam p U) →
      product_zeroth_first_parts.KvalGe (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) p nu
        (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne (X.om v) be U))) g) :
    IsPlaceCofactorValuationLowerBound X be j v g := by
  intro U hU I n
  obtain ⟨hU1, e⟩ := restr_onePlace p X be j v U hcc hU
  refine GlobalTheory.KvalAgree.coeff_applyD_PIv_of_KvalGe p X j v nu hnu _ g ?_ I n
  rw [e]
  exact hK _ hU1

theorem lowAt_F : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D), LatTied hT X Y → FillsAll hT Y → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n → ∀ (Lv : Levels (Y.Fl u w hg)) (Ch : Chain Lv) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) Lv Ch std vp unif eO eO_spec dG dG_spec om)), BeProp (D.what₂.places.resChar w) Y5.be → ∀ (v : Fin (D.gat u w hg).P.nV) (t : HH D), (D.gat u w hg).P.n' v = nP D (D.what₂.places.resChar w) → (∀ s : Fin ((D.gat u w hg).P.n' v), hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) (true, t) s.val)) → ∀ i < D.R.m, Y5.LowAt i v (FOrb D (i + 1) (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce (i + 1) (D.what₂.places.resChar w) (true, t)) := by
  intro D u w hg L hT X Y K ce E hTied hFill hA hS hC hX Lv Ch std vp unif eO eO_spec dG dG_spec om Y5 hBe v t hn hpos i hi
  have h0 : IsResidueClassZero D (D.what₂.places.resChar w) := hg.2.2.1
  have hne := (GlobalTheory.T.servedPrime_properties D _ hg.1 h0 hg.2.2.2.1).1
  have hstd := std v
  have hOK : OrbitPlaces.OrbOK D (D.what₂.places.resChar w) := ⟨hg.2.1, hn ▸ hstd.even, hn ▸ hstd.two_le⟩
  have hcc : MvPowerSeries.constantCoeff Y5.be = 0 := by
    by_contra hc
    have := (hBe.ab 0 (by simpa using hc)).1
    simp at this
  haveI : NeZero ((D.gat u w hg).P.n' v) := ⟨by have := hstd.two_le; omega⟩
  have ht : (Y.Fl u w hg).t = D.R.t := (hTied u w hg).2.1
  have hk := hT.gat_k u w hg
  have hN : ∀ j, NN (D.gat u w hg).P.m (Y.Fl u w hg).t j = D.R.N j := fun j => by
    simp only [NN, Ranks.N, ht]
    omega
  refine GlobalTheory.T.lowAt_of_placeCofactorValuationLowerBound _ _ Y5 i v _ hcc ?_
  refine lowBound_of_series_bound_one_place (Sys.mk (D.gat u w hg) (Y.Fl u w hg) Lv Ch std vp unif eO eO_spec dG dG_spec om) Y5.be i v (fun s => E.nu u i (posPl D (D.what₂.places.resChar w) (true, t) s.val)) _ hcc ?_ ?_
  · intro s r
    have h1 := GlobalTheory.T.formalGroup_nu_cast_eq_ite_lt_N D u w hg hT Y hFill ht v (toFin s) i hi r
    have h2 := E.nu_row u i hi (posPl D (D.what₂.places.resChar w) (true, t) s.val) r
    have h3 := hpos (toFin s)
    rw [h3] at h1
    have h4 : (((E.nu u i (posPl D (D.what₂.places.resChar w) (true, t) s.val)).rowLen r : ℕ) : ℝ) =
        ((FormalGroupSystem.nu (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) (i + 1) (toFin s) (r + 1) : ℤ) : ℝ) := by
      rw [h2, h1]; rfl
    exact_mod_cast h4
  · intro U' hU1
    exact kval_general D L X K ce E hA hS hC _ hOK h0 hne hX u i hi t _ _ _ hn
      (hN i) (hN (i + 1)) _ _ hBe _ hU1

end GlobalTheory.TwU.LowF

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.SolvUp

theorem exists_normal_prime_index (Γ : Type) [Group Γ] [Finite Γ] [Nontrivial Γ] [Group.IsSolvable Γ] :
    ∃ H : Subgroup Γ, H.Normal ∧ H.index.Prime := by
  obtain ⟨H, hH, hle⟩ := (eq_top_or_exists_le_coatom (commutator Γ)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Γ).ne
  have hn : H.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ H :=
      hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    simpa using H.mul_mem h1 hn⟩
  refine ⟨H, hn, ?_⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (Γ ⧸ H)) (mt Subgroup.index_eq_one.1 hH.1)
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : (Subgroup.zpowers g).comap (QuotientGroup.mk' H) = ⊤ := by
    refine hH.2 _ (lt_of_le_of_ne (fun x hx => ?_) fun e => ?_)
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact one_mem _
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H g
      have hx : x ∈ H := e ▸ Subgroup.mem_zpowers _
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx, orderOf_one] at hg
      exact hp.one_lt.ne hg
  have h2 : Subgroup.zpowers g = ⊤ :=
    Subgroup.comap_injective (QuotientGroup.mk'_surjective H) (h1.trans (Subgroup.comap_top _).symm)
  rw [Subgroup.index, ← Subgroup.card_top, ← h2, Nat.card_zpowers, hg]
  exact hp

theorem isCMField_of_ringEquiv {A B : Type} [Field A] [NumberField A] [Field B] [NumberField B] [IsCMField A]
    (e : A ≃+* B) : IsCMField B := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  haveI : IsTotallyComplex B := isTotallyComplex_of_algebra A B
  letI : Algebra (maximalRealSubfield A) B :=
    ((e : A →+* B).comp (algebraMap (maximalRealSubfield A) A)).toAlgebra
  let f : A ≃ₐ[maximalRealSubfield A] B := { e with commutes' := fun _ => rfl }
  haveI : Module.Free (maximalRealSubfield A) B := Module.Free.of_equiv f.toLinearEquiv
  haveI : Algebra.IsQuadraticExtension (maximalRealSubfield A) B :=
    ⟨by rw [← f.toLinearEquiv.finrank_eq]; exact Algebra.IsQuadraticExtension.finrank_eq_two _ _⟩
  exact IsCMField.ofCMExtension (maximalRealSubfield A) B

end GlobalTheory.SolvUp

namespace GlobalTheory.SolvUp

theorem isCMField_intermediate (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [Algebra K M]
    [IsScalarTower K M Ω] (L : IntermediateField K M) : IsCMField L := by
  let f := IsScalarTower.toAlgHom K M Ω
  haveI : NumberField f.fieldRange := NumberField.of_ringEquiv M _ (AlgEquiv.ofInjectiveField f).toRingEquiv
  haveI : NumberField (L.map f) := NumberField.of_ringEquiv L _ (IntermediateField.equivMap L f).toRingEquiv
  haveI : IsCMField f.fieldRange := isCMField_of_ringEquiv (AlgEquiv.ofInjectiveField f).toRingEquiv
  have hle : L.map f ≤ f.fieldRange := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := (IntermediateField.mem_map L).1 hy
    exact AlgHom.mem_fieldRange.2 ⟨x, rfl⟩
  haveI : IsCMField (L.map f) := (GlobalTheory.T.cm_subfields_compositum_closed Ω K).2.1 f.fieldRange (L.map f) hle inferInstance
  exact isCMField_of_ringEquiv (IntermediateField.equivMap L f).symm.toRingEquiv

end GlobalTheory.SolvUp
end
end
