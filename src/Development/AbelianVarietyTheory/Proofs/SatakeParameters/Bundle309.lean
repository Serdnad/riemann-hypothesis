module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle217
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle205
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle185
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle232
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle163
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle288
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle303
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle048
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.Bundle001
import Formalism.LocalToGlobal.Columns.ChainInst
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftDictionary



variable {D : D7} {G : Type} [Group G] [Fintype G] {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

section Zero

variable {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} (R : RealDat D A Ks)

theorem hk_zero (V : HSp D) (P : Pl D.host.E) : hk V P 0 = 0 := Finsupp.sum_zero_index

theorem postOn_zero (V : HSp D) {S} (M : DSModel V S) (T : MMap M) : postOn M 0 T = 0 := by
  ext v
  simp [postOn]

theorem hkF_zero (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (F : Bridge.Gf V → W) : hkF V P 0 F = 0 := by
  funext g
  exact Finsupp.sum_zero_index

theorem ops_zero (hM : R.IsModels) (j : Fin D.R.m) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H) (hh : IsOpsV R j t h) (y : (R.HV j t).H) : h P 0 y = 0 := by
  refine (hM.HV j t).1 ?_
  rw [hh P hP 0 y, map_zero]
  exact hkF_zero _ _ _

theorem match_zero (hM : R.IsModels) (j : Fin D.R.m) (t : T) (P : Pl D.host.E) : MatchW R j t P 0 0 := by
  intro y y' hy
  have h0 : y' = 0 := by
    refine (hM.HV j t).1 ?_
    rw [hy, map_zero]
    exact hkF_zero _ _ _
  have e1 : (R.thG j t) y' = 0 := by rw [h0]; exact (R.thG j t).map_zero
  have e2 : (R.HW j (sg0 D A)).e ((R.thG j t) y') = 0 := by rw [e1]; exact (R.HW j (sg0 D A)).e.map_zero
  refine e2.trans ?_
  rw [hk_zero]
  exact (postOn_zero _ _ _).symm

theorem op_zero (hM : R.IsModels) (j : Fin D.R.m) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (o : Module.End D.what₂.LL (A.MtCSD j t).Forms) (ho : o = 0)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H) (hh : IsOpsV R j t h) (x : (A.MtCSD j t).Forms) :
    R.jV j t (o x) = h P 0 (R.jV j t x) := by
  rw [ops_zero R hM j t P hP h hh, ho, LinearMap.zero_apply]
  exact (R.jV j t).map_zero

end Zero

section Cases

variable {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} (R : RealDat D A Ks)

theorem split_good (F : Face D A) (core : Core R F) (t : T) (P : A.ok t) : Good R t (R.pl P) :=
  ((GlobalTheory.GoodPrimes.good_primes R F core.lev).2.2.2 core.fam t P P.2).1

theorem split_low (F : Face D A) (core : Core R F) (hS : SchurAll R) (j : Fin D.R.m) (t : T) (P : A.ok t) (k : ℕ)
    (hk : k ≤ (Vc D j).rank) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R t pl ∧
      (∀ h, IsOpsV R j t h → ∀ x, R.jV j t (A.heckeL j t (P, k) x) = h pl cV (R.jV j t x)) ∧ MatchW R j t pl cV cW := by
  obtain ⟨z, hz, -⟩ := GlobalTheory.T.thetaLift_transfer_heckePoly_splitPrime R F core hS j t P
  exact ⟨R.pl P, Finsupp.single (splitLab (Vc D j).rank k) 1, splitC (Wc D j).rank (z k), split_good R F core t P,
    fun h hh x => (GlobalTheory.SplitHeckeLabel.split_ops R F core.lev core.fam core.models).2 j t h hh P k hk x, hz k hk⟩

theorem split_high (F : Face D A) (core : Core R F) (j : Fin D.R.m) (t : T) (P : A.ok t) (k : ℕ)
    (hk : ¬ k ≤ (Vc D j).rank) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R t pl ∧
      (∀ h, IsOpsV R j t h → ∀ x, R.jV j t (A.heckeL j t (P, k) x) = h pl cV (R.jV j t x)) ∧ MatchW R j t pl cV cW := by
  have h0 : A.heckeL j t (P, k) = 0 := (core.fam.degL j t P).2 k (not_le.1 hk)
  have hg := split_good R F core t P
  refine ⟨R.pl P, 0, 0, hg, fun h hh x => ?_, match_zero R core.models j t _⟩
  exact op_zero R core.models j t (R.pl P) hg (A.heckeL j t (P, k)) h0 h hh x

end Cases

section Inert

variable {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} (R : RealDat3 D A3 Ks) (F : Face3 D A3)

theorem inert_valid (hH : HoweUnram) (hI : GlobalTheory.Chain.LiftInteg D) (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt)
    (hS : SchurAll R.toRealDat) (j : Fin D.R.m) (t : T) (Q : A3.okI t) (s : List ℕ)
    (hs : Formalism.L2.Col.InertTypeOk (Vc D j).rank s) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R.toRealDat t pl ∧
      (∀ h, IsOpsV R.toRealDat j t h → ∀ x, R.jV j t (A3.heckeLI j t (Q, s) x) = h pl cV (R.jV j t x)) ∧
        MatchW R.toRealDat j t pl cV cW := by
  obtain ⟨hCore, -, hGoodI, -, -, -, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := hCore hEx
  obtain ⟨hg, hconj⟩ := hGoodI t Q Q.2
  have two := GlobalTheory.T.twoSidedHeckePartner_inertPrime hH R.toRealDat F.lv2 hI core hS t (R.plI Q) hg hconj (GlobalTheory.T.hyperspecialFixesAllChainVacua_at_inert_prime R F hC t _ hg hconj)
  obtain ⟨cW, hW⟩ := (two.2 j).1 (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank s) 1)
  refine ⟨R.plI Q, Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank s) 1, cW, hg, fun h hh x => ?_, hW⟩
  have hty : ∀ i : A3.okI t × List ℕ, Formalism.L2.Col.InertTypeOk (Vc D j).rank i.2 →
      Good R.toRealDat t (R.plI i.1) ∧ _root_.Formalism.DivisionValues.conjPl (R.plI i.1) = R.plI i.1 ∧
        (GlobalTheory.Hk3.labIn (Vc D j).rank i.2).Pairwise (fun a b => b ≤ a) := by
    intro i hi
    obtain ⟨g1, g2⟩ := hGoodI t i.1 i.1.2
    exact ⟨g1, g2, ((GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents (Vc D j).rank _).2 ⟨i.2, hi.2.2, hi.1, hi.2.1, rfl⟩).2.1⟩
  exact (GlobalTheory.T.inertHeckeOperators_lifts_rational_selfAdjoint_labels R.toRealDat F.lv2 core.lev core.fam core.models j t (A3.okI t × List ℕ) (fun i => R.plI i.1)
    (fun i => GlobalTheory.Hk3.labIn (Vc D j).rank i.2) (A3.heckeLI j t) (fun i => Formalism.L2.Col.InertTypeOk (Vc D j).rank i.2) hty
    (hC.inert.hL j t).some (Q, s) hs).2.2.2 h hh x

theorem inert_vanish (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (j : Fin D.R.m) (t : T) (Q : A3.okI t) (s : List ℕ)
    (h0 : A3.heckeLI j t (Q, s) = 0) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R.toRealDat t pl ∧
      (∀ h, IsOpsV R.toRealDat j t h → ∀ x, R.jV j t (A3.heckeLI j t (Q, s) x) = h pl cV (R.jV j t x)) ∧
        MatchW R.toRealDat j t pl cV cW := by
  obtain ⟨hCore, -, hGoodI, -, -, -, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := hCore hEx
  obtain ⟨hg, -⟩ := hGoodI t Q Q.2
  refine ⟨R.plI Q, 0, 0, hg, fun h hh x => ?_, match_zero R.toRealDat core.models j t _⟩
  exact op_zero R.toRealDat core.models j t (R.plI Q) hg (A3.heckeLI j t (Q, s)) h0 h hh x

end Inert

theorem every_op_label : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ j t, ∃ pl cV cW, LiftDict R j t pl cV cW := by
  intro hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hI hC hEx hS hJ j t
  have core := (GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC).1 hEx
  have key : ∀ i : (A3.liftI j t).OpIx, ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R.toRealDat t pl ∧
      (∀ h, IsOpsV R.toRealDat j t h → ∀ x, R.jV j t ((A3.liftI j t).opAll i x) = h pl cV (R.jV j t x)) ∧
      MatchW R.toRealDat j t pl cV cW := by
    rintro (⟨P, k⟩ | ⟨Q, s⟩)
    · by_cases hk : k ≤ (Vc D j).rank
      · exact split_low R.toRealDat F.lv2 core hS j t P k hk
      · exact split_high R.toRealDat F.lv2 core j t P k hk
    · rcases hJ.L j t Q s with h0 | ⟨s', hs', he⟩
      · exact inert_vanish R F hC hEx j t Q s h0
      · have hrank : A3.A.r + A3.A.t = (Vc D j).rank := (R.B.rankL j).symm
        rw [hrank] at hs'
        obtain ⟨pl, cV, cW, g, o, m⟩ := inert_valid R F hH hI hC hEx hS j t Q s' hs'
        refine ⟨pl, cV, cW, g, fun h hh x => ?_, m⟩
        have e : (A3.liftI j t).opAll (Sum.inr (Q, s)) = A3.heckeLI j t (Q, s') := he
        rw [e]
        exact o h hh x
  choose pl cV cW h1 h2 h3 using key
  exact ⟨pl, cV, cW, ⟨h1, fun h hh i x => h2 i h hh x, h3⟩⟩

end GlobalTheory.LiftDictionary

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem latK_lev_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m) c (x : UA D i hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), ∀ (κ : ((St i hi).K ((St i hi).chOf c)).lev.U), x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 → latK D.sp (gramN D i hi) a x.1 ((St i hi).K ((St i hi).chOf c)).lev.Lb = SDLat.smulLat (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) (t.seam.lat ((t.rd u μ).N i c))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ hT' i hi c x γ hγ κ hx
  have hκ : Formalism.MainNotions.G.KAat.HatStab ((St i hi).K ((St i hi).chOf c)).lev.Lb κ.1 := by
    have h1 := (((St i hi).K ((St i hi).chOf c)).lev.U_eq κ.1).1 κ.2
    have h2 := (GlobalTheory.LatticeStabLocal.mem_levelAfL_iff _ _ (sigD D) _ (gramN D i hi) ((St i hi).K ((St i hi).chOf c)).lev.Lb
      ((St i hi).K ((St i hi).chOf c)).lev.Lb_fin κ.1).2 ⟨h1.1, fun v => ((St i hi).K ((St i hi).chOf c)).lev.Uloc_lev v (h1.2 v)⟩
    exact fun z => ((inv_mem h2).2 z).symm
  rw [hx, Formalism.MainNotions.G.KAat.latK_tr _ _ _ _ _ γ hγ hκ, hT'.latK_eq i hi c, ← Submodule.map_comp]
  unfold SDLat.smulLat
  congr 1
  ext v
  simp [Matrix.toLin'_toMatrix']

end GlobalTheory.TwV
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BadPrimes

theorem mapPrime_conjugate {D : D7} {X : Fields} (s : Seam D X) (hs : s.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    seamP s (conjPrime₂ P) = conjPrime₂ (seamP s P) := by
  apply HeightOneSpectrum.ext
  ext r
  obtain ⟨x, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective r
  have hc : cO D.host.E (RingOfIntegers.mapRingEquiv s.iE x) = RingOfIntegers.mapRingEquiv s.iE (cO X.E x) :=
    RingOfIntegers.ext ((bridge_star_holds D.R D.host (s.iE x)).trans (hs.2 (x : X.E)).symm)
  rw [mem_conjP, hc, mem_seamP, mem_seamP, mem_conjP]

theorem lev_pos_and_noConj :
    UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => 0 < (t.rd u μ).lev ∧ ∀ Q ∈ ssRec t u μ, conjPrime₂ Q ∉ ssRec t u μ) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie
  obtain ⟨hSS, hlev, -⟩ := (isChainTop_iff _ _ _ _ _ _ _ _ _).1 hTie.isChainTop
  refine ⟨?_, ?_⟩
  · rw [hlev]
    have hprod : 0 < ∏ P : rowSG t.Pr t.sel (t.tup μ), Formalism.L2.Col.qOf P.1 :=
      Finset.prod_pos fun P _ => Nat.pos_of_ne_zero fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact Nat.mul_pos (pow_pos hprod _) (Nat.mul_pos (t.pr_ok.T_prime _).pos (pow_pos hprod _))
  · intro Q hQ hQ'
    obtain ⟨P, rfl⟩ : ∃ P, seamP t.seam P = Q :=
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv t.seam.iE)).surjective Q
    rw [← mapPrime_conjugate t.seam t.seam_ok, mem_ssRec, hSS] at hQ'
    rw [mem_ssRec, hSS] at hQ
    exact sall_noConj t.sel (t.tup μ) hP.fields t.pr_ok hP.sel (t.word u) hP.avoid.2 hP.avoid.1 P hQ hQ'

end GlobalTheory.BadPrimes
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwV

open scoped TensorProduct

section Alg

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

theorem coordRat_toLE_mul (g k : GL (Fin N) E) (v : Fin N → E) : toLE (g * k) v = toLE g (toLE k v) := by
  rw [toLE_apply, toLE_apply, toLE_apply, Units.val_mul, Matrix.mulVec_mulVec]

theorem coordRat_toLE_inv_apply (g : GL (Fin N) E) (v : Fin N → E) : toLE g⁻¹ (toLE g v) = v := by
  rw [← coordRat_toLE_mul, inv_mul_cancel, toLE_apply, Units.val_one, Matrix.one_mulVec]

theorem coordRat_toLE_apply_inv (g : GL (Fin N) E) (v : Fin N → E) : toLE g (toLE g⁻¹ v) = v := by
  rw [← coordRat_toLE_mul, mul_inv_cancel, toLE_apply, Units.val_one, Matrix.one_mulVec]

theorem coordRat_toLE_symm (g : GL (Fin N) E) (v : Fin N → E) : (toLE g).symm v = toLE g⁻¹ v := by
  apply (toLE g).injective
  rw [LinearEquiv.apply_symm_apply, coordRat_toLE_apply_inv]

theorem coordRat_inFr {a b : ℕ} (σ : E →+* E) (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E)
    (co γ : GL (Fin a) E) (co' γ' : GL (Fin b) E) (z : (Fin a → E) →ₗ[E] (Fin b → E)) (v : Fin a → E) :
    inFr (toStdCo σ J co) (toStdCo σ J' co') (inFr (stdG σ J γ) (stdG σ J' γ') z) v =
      toLE (co' * γ' * co'⁻¹)⁻¹ (inFr (toStdCo σ J co) (toStdCo σ J' co') z (toLE (co * γ * co⁻¹) v)) := by
  simp only [inFr, toStdCo, stdG, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, coordRat_toLE_symm, LinearEquiv.symm_apply_apply,
    _root_.mul_inv_rev, inv_inv, coordRat_toLE_mul, coordRat_toLE_inv_apply, coordRat_toLE_apply_inv]

end Alg

theorem seamHom_inFr_stdG : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m) (γ : GL (Fin (D.R.N i)) D.host.E) (γ' : GL (Fin (D.R.N (i + 1))) D.host.E)
      (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))),
      seamGL t.seam g.1 = A.crd i (Nat.le_of_succ_le hi) * γ * (A.crd i (Nat.le_of_succ_le hi))⁻¹ →
      seamGL t.seam g'.1 = A.crd (i + 1) hi * γ' * (A.crd (i + 1) hi)⁻¹ → ∀ z : HomE D.host.E (D.R.N i) (D.R.N (i + 1)),
      seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z) =
      g'.1.toLinearMap ∘ₗ seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi))
        (inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
          (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)) ∘ₗ g.1.symm.toLinearMap) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ i hi γ γ' g g' hg hg' z
  have hS : ∀ {p q : ℕ} (x : HomE D.host.E p q) (w : Sp t.X.E p),
      (fun l => t.seam.iE (seamHom t.seam x w l)) = x (fun k => t.seam.iE (w k)) :=
    fun x w => funext (seamHom_apply t.seam x w)
  have hG : ∀ {n : ℕ} (h : Sp t.X.E n ≃ₗ[t.X.E] Sp t.X.E n) (v : Sp t.X.E n),
      (fun l => t.seam.iE (h v l)) = toLE (seamGL t.seam h) (fun l => t.seam.iE (v l)) := by
    intro n h v
    rw [toLE_apply, seamGL_mulVec]
  have hw : ∀ {n : ℕ} (h : Sp t.X.E n ≃ₗ[t.X.E] Sp t.X.E n) (v : Sp t.X.E n),
      (fun l => t.seam.iE (h.symm v l)) = toLE (seamGL t.seam h)⁻¹ (fun l => t.seam.iE (v l)) := by
    intro n h v
    apply (toLE (seamGL t.seam h)).injective
    rw [← hG, LinearEquiv.apply_symm_apply, coordRat_toLE_apply_inv]
  refine LinearMap.ext fun w => funext fun l => ?_
  have key : (fun l => t.seam.iE (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z) w l)) =
      (fun l => t.seam.iE (g'.1 (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi))
        (inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
          (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)) (g.1.symm w)) l)) := by
    rw [hG, hS, hS, hw, hg, hg', coordRat_inFr, coordRat_toLE_apply_inv, coordRat_toLE_apply_inv]
  exact t.seam.iE.injective (congrFun key l)

end GlobalTheory.TwV

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct

namespace GlobalTheory.AwayLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar




theorem prV_pullV_mem_latS_dual : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (l : Fin (D.R.N i) → D.host.E), l ∈ latAd x.1 lev.Lb →
    (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) := by
  intro D i hi T f bad lev x v l hl
  have hmono : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) lev.Lb ≤
      latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) :=
    Submodule.span_mono (Set.image_mono fun y hy => Submodule.subset_span (lev.Lb_int y hy))
  apply hmono
  induction hl using Submodule.span_induction with
  | mem y hy => exact Formalism.L2.Geo.Def.PN.prV_latS lev.Lb v hy
  | zero =>
    have : (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 (0 : Fin (D.R.N i) → D.host.E) k)) = 0 := by
      ext k
      have h0 : pullV (F := D.host.F) x.1 (0 : Fin (D.R.N i) → D.host.E) = 0 := by
        have := pullV_add (F := D.host.F) x.1 (0 : Fin (D.R.N i) → D.host.E) 0
        funext j
        have hj := this j
        rw [add_zero] at hj
        simpa using hj
      rw [h0, Pi.zero_apply, map_zero, Pi.zero_apply]
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 (a + b) k)) =
        (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 a k)) +
          (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 b k)) := by
      ext k
      rw [Pi.add_apply, pullV_add, map_add (f := _)]
    rw [this]; exact add_mem ha hb
  | smul c a _ ha =>
    have hc : inclE (F := D.host.F) (v.adicCompletion D.host.F) (algebraMap (𝓞 D.host.E) D.host.E c) ∈ intV D.host.E v :=
      Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 D.host.E) D.host.E c, ⟨c, rfl⟩⟩, rfl⟩)
    have : (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 (c • a) k)) =
        (⟨_, hc⟩ : intV D.host.E v) • (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 a k)) := by
      ext k
      rw [pullV_osmul, map_mul]
      rfl
    rw [this]; exact Submodule.smul_mem _ _ ha

end GlobalTheory.AwayLat
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) {w : Pr.Word}


open Classical in
theorem cplCoset_frsF_mem {j : ℕ} (p : ChPt (R := R) sel mu w j) (P : rowSG Pr sel mu) (x : Sp X.E (R.N j)) :
    frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  unfold frsF
  split_ifs with h
  · have h1 : p.deco.1.HasLift ⟨P.1, h⟩ := Deco.Ok.hasLift p.deco.2 ⟨P.1, h⟩
    exact (Deco.liftFr_spec h1).1 x
  · exact Subtype.property p ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x

theorem cplCoset_sameCoset_of_common {cst : LocCst X (rowSG Pr sel mu)} {n : ℕ} {P : rowSG Pr sel mu} {x y z : Sp X.E n}
    (h : SameCoset sel mu cst P x z) (h' : SameCoset sel mu cst P y z) : SameCoset sel mu cst P x y := fun l => by
  have h1 := (h l).add (ciIntAt_neg (h' l))
  rwa [← mul_neg, ← Pi.neg_apply, ← mul_add, ← Pi.add_apply, neg_sub, sub_add_sub_cancel] at h1

end Gen

end GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem cplCoset_bound : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ)
  (y : Sp t.X.E (D.R.N (t.m2 + 1))), SameCoset t.sel (t.tup μ) (t.cst μ) P y (y0At A (t.m2 + 1) hi β P) →
  (P.1 ∈ t.Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * y l)) ∧
  (P.1 ∉ t.Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * y l))) := by
  classical
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hP H hi β P y hy
  obtain ⟨⟨c, rfl⟩, -⟩ := ((St (t.m2 + 1) hi).K β).y_bij.2 (Quotient.mk'' 1)
  obtain ⟨y1, hy1, hY⟩ := H.chain.2.1 c
  have hmem : y1 ∈ A.yb c := by rw [hY]; simp
  have h0 := H.coset c y1 hmem P
  have hy' : SameCoset t.sel (t.tup μ) (t.cst μ) P y (A.y0 ((St _ (cpl_lt t μ).le).chOf c) P) := by
    unfold y0At at hy
    rwa [dite_eq_left rfl] at hy
  have hyw := cplCoset_sameCoset_of_common t.sel (t.tup μ) hy' h0
  set p := A.pt (t.m2 + 1) (cpl_lt t μ).le c with hp
  set w := (frsF t.sel (t.tup μ) p P).symm y1 with hw
  have hq0 : (qOf P.1 : t.X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, qOf, Ne, Ideal.absNorm_eq_zero_iff]
    exact P.1.ne_bot
  have hloc := (mem_locLat _ _ _ _).1 hy1 P
  have hw1 : ∀ l, IntAt P.1 ((((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then (-1 : ℤ) else -((t.cst μ).M : ℤ)))⁻¹) * w l) := by
    have h2 : frsF t.sel (t.tup μ) p P ((((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then (-1 : ℤ) else -((t.cst μ).M : ℤ)))⁻¹) • w) ∈ p.deco.1.at P.1 := by
      rw [map_smul, hw, LinearEquiv.apply_symm_apply]
      exact hloc
    have h3 := (ciMem_stdAt _ _).1 ((cplCoset_frsF_mem t.sel (t.tup μ) p P _).1 h2)
    intro l
    simpa using h3 l
  refine ⟨fun hG l => ?_, fun hG l => ?_⟩
  · have h1 := hw1 l
    have h2 := hyw l
    simp only [hG, if_true, pow_zero, inv_one, one_mul, _root_.zpow_neg, zpow_one, inv_inv, Pi.sub_apply] at h1 h2
    have e : (qOf P.1 : t.X.E) * y l = (qOf P.1 : t.X.E) * (y l - w l) + (qOf P.1 : t.X.E) * w l := by ring
    rw [e]
    exact (ciIntAt_q.mul h2).add h1
  · have h1 := hw1 l
    have h2 := hyw l
    simp only [hG, if_false, _root_.zpow_neg, zpow_natCast, inv_inv, Pi.sub_apply] at h1 h2
    have hqM : IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M) := by
      have := IntAt.coe P.1 (((qOf P.1 ^ (t.cst μ).M : ℕ)) : 𝓞 t.X.E)
      rwa [map_natCast, Nat.cast_pow] at this
    have e : (qOf P.1 : t.X.E) ^ (t.cst μ).M * y l = (qOf P.1 : t.X.E) ^ (t.cst μ).M * (qOf P.1 : t.X.E) ^ (t.cst μ).M *
        (((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (y l - w l)) + (qOf P.1 : t.X.E) ^ (t.cst μ).M * w l := by
      field_simp
      ring
    rw [e]
    exact ((hqM.mul hqM).mul h2).add h1

end GlobalTheory.TwV
end
