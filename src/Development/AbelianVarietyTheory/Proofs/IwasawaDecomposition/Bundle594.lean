module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle575
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle576
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle571
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle577
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ExpDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle584
import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle583
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle579
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle567
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr




section Gen
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F}
  {F : Face3 D A3} {X0 : BaseLevelRowSide D} {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {cf : CharFrame D}
  {g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1}

end Gen

section Gen2

def bsTw {D : D7} {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ} (Bs : SideB D cf Rw low Pq S hL eig θ)
    (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp) :
    SideB (thTw D th).toD7 ((thTw D th).cf cf) ((thTw D th).row Rw) low Pq ((thTw D th).rat S) hL eig θ :=
  { Bs with
    twF := { Bs.twF with }
    tw := { Bs.tw with }
    chiD := { Bs.chiD with }
    chi := { Bs.chi with }
    exp :=
      { Bs.exp with
        mtV := fun i j b k Q ψ h1 h2 h =>
          letI : AddCommGroup (Bs.exp.Wt i j b) := Bs.exp.acgWt i j b
          letI : Module (FractionRing ((thTw D th).toD7.ntw.O i)) (Bs.exp.Wt i j b) := Bs.exp.modWt i j b
          { Bs.exp.mtV i j b k Q ψ h1 h2 h with } } }

def lamTw {D : D7} (N : TwNew D) (Z : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.LamDat N.toD7 := ⟨N.cf Z.C, Z.q0, Z.w0, Z.c, Z.chi⟩

theorem lam_thTw {D : D7} (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp) {cf : CharFrame D}
    (h : ∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z) :
    ∃ Z : GlobalTheory.LamTie.LamDat (thTw D th).toD7, Z.Ok ∧ Z.Teich ∧ Z.C = (thTw D th).cf cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 (thTw D th).toD7 ∧
      GlobalTheory.LamTie.IsLamTieFull (thTw D th).toD7.ntw Z := by
  obtain ⟨Z, h1, h2, h3, h4, h5⟩ := h
  exact ⟨lamTw (thTw D th) Z, ⟨h1.places, h1.aux, h1.big⟩, h2, congrArg (TwNew.cf (thTw D th)) h3, h4, h5⟩
end Gen2

section MtCopy
variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

end MtCopy

end GlobalTheory.HeightCounting.Up
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar



noncomputable section
namespace GlobalTheory.HeightCounting.Up.ListCarry
open GlobalTheory.Mem.R3.Tr GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun GlobalTheory.TwInputs.Move


open Classical in
def movePl {D : D7} {I : Type} {L : Formalism.IndefR.Links.LevCh D I} (P : Places L)
    (h4 : ∀ t, ∀ PP ∈ L.Q t, ((q0 D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) (v : HeightOneSpectrum (𝓞 D.host.F))
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hv : ((q0 D : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) (hS : v ∉ S1 D)
    (hu : u.under (𝓞 D.host.F) = v) (hs : ∃ e : Formalism.L2.Theta.AE D, Formalism.L2.NTheta.IsIdemAt e u) : Places L where
  v0 := v
  basePlace_over_qZero := hv
  w := Function.update P.w v u
  w_over x hx := by
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [Function.update_self]; exact hu
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem hx hS)]
      exact P.w_over x (Finset.mem_insert_of_mem hx)
  w_split x hx := by
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [Function.update_self]; exact hs
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem hx hS)]
      exact P.w_split x (Finset.mem_insert_of_mem hx)
  w_g x k hx := by
    have : x ∈ S1 D := (S1_mem_OmF D).2 (by
      fin_cases k
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx))
    rw [Function.update_of_ne (ne_of_mem_of_not_mem this hS)]
    exact P.w_g x k hx
  w_de p hp := (P.w_de p hp).imp fun 𝔭 h x hx => by
    have : x ∈ S1 D := (S1_mem_OmF D).2 (by
      rcases hp with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl hx))
      · exact Or.inr (Or.inr (Or.inr hx)))
    rw [Function.update_of_ne (ne_of_mem_of_not_mem this hS)]
    exact h x hx
  w_Q t PP hP h := by
    rw [Function.update_of_ne (ne_of_mem_of_not_mem h hS)]
    exact P.w_Q t PP hP h
  levelPlace_ne_basePlace t PP hP e := by
    subst e
    refine h4 t PP hP ?_
    have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((q0 D : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal := hv
    rwa [map_natCast] at this

theorem movePl_w {D : D7} {I : Type} {L : Formalism.IndefR.Links.LevCh D I} (P : Places L) (h4 v u hv hS hu hs) :
    (movePl P h4 v u hv hS hu hs).w v = u := by
  simp only [movePl, Function.update_self]

theorem listPin_copy {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e)
    (hj : HEq D.ntw.jL D'.ntw.jL) (hs : HEq D.ntw.s2 D'.ntw.s2) (hX : HEq D.ntw.Xv D'.ntw.Xv) {I I' : Type}
    {Lc : Formalism.IndefR.Links.LevCh D I} {Lc' : Formalism.IndefR.Links.LevCh D' I'} {μ0 : I'} (hL : Lc'.Is μ0)
    (hmu : HEq Lc'.C.mu0 Lc.C.mu0) (hd : HEq Lc'.C.del Lc.C.del) (hd' : HEq Lc'.C.del' Lc.C.del')
    (hP : (∀ k, q0 D' ≠ D'.host.g k) → Nonempty (Places Lc'))
    (h4 : ∀ t, ∀ PP ∈ Lc'.Q t, ((q0 D' : ℕ) : 𝓞 D'.host.E) ∉ PP.asIdeal) {CF b : ℝ} (hp : ListPin D Lc CF b) :
    ListPin D' Lc' CF b := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h.gal
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h.set
  have b1 := h.sp
  have b2 := h.Tau
  have b3 := h.instTau
  have b4 := h.eTau
  have b5 := h.hc
  cases D'
  dsimp only at a1 a2 a3 b1 b2 b3 b4 b5 nOm ninstOm nalgOm nplOm nPlG xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth hj hs hX
  subst a1; subst a2; subst a3; subst b1
  rename Rows.Data _ => rows'
  cases rows'
  dsimp only at b2 b3 b4 b5
  subst b2; subst b3; subst b4; subst b5
  rename NData _ _ _ => N'
  cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  rename NTw _ _ _ _ _ => X'
  cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth hj hs hX
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst hj; subst hs; subst hX
  obtain ⟨G, hF, hT⟩ := hp
  have hmu := eq_of_heq hmu
  have hd := eq_of_heq hd
  have hd' := eq_of_heq hd'
  have h0 := G.ch.basePlace_not_mem_chiGridBadPlaces
  obtain ⟨P₀⟩ := hP fun k e => h0 ((S1_mem_OmF D).2 (by
    have e' : q0 D = D.host.g k := e
    have := G.pl.basePlace_over_qZero
    rw [e'] at this
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)))
  have hm : G.pl.v0 ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)
  let P : Places Lc' := movePl P₀ h4 G.pl.v0 (G.pl.w G.pl.v0) G.pl.basePlace_over_qZero h0 (G.pl.under_w hm) ((G.pl.w_split G.pl.v0 hm))
  have hw : P.w P.v0 = G.pl.w G.pl.v0 := movePl_w ..
  obtain ⟨h1, h2⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA _).2 I' Lc' P ⟨1, CF, b⟩
  obtain ⟨V⟩ := GlobalTheory.ChiGridModel.nonempty_vertices _ I' Lc' _ _ (GlobalTheory.ChiGrid.colY_isV _ I' Lc' μ0 hL 0 (Nat.zero_le _)).sd h1 h2
  let X : Chars P 1 := ⟨G.ch.chiH, (G.ch.chi), (G.ch.chi_eq), (G.ch.triv), (G.ch.inf), (G.ch.unr),
    (G.ch.lev1), (G.ch.wild), (G.ch.lev0)⟩
  refine ⟨⟨P, X, V⟩, ⟨fun i a c v hv => ?_, fun v hv => ?_⟩, fun i hi => ?_⟩
  · obtain ⟨y, hy⟩ := hF.values i a c v hv
    exact ⟨e.symm y, by rw [← h.embLL0_eq, e.apply_symm_apply]; exact hy⟩
  · obtain ⟨z, hz⟩ := hF.roots v hv
    exact ⟨e.symm z, hz.map_of_injective (f := e.symm) e.symm.injective⟩
  · obtain ⟨t0, j, t1, t2⟩ := hT i ((h.inW1 i i HEq.rfl).2 hi)
    have hl : ∀ l a c, (lamOf (⟨P, X, V⟩ : GridData Lc' ⟨1, CF, b⟩)).lam0 l a c = (lamOf G).lam0 l a c := fun l a c => by
      change Lc'.C.mu0 a * (if l = D.host.pde then Lc'.C.del' else Lc'.C.del) * _ = _
      rw [hmu, hd, hd']
      rfl
    have hw' : (lamOf (⟨P, X, V⟩ : GridData Lc' ⟨1, CF, b⟩)).w0 = (lamOf G).w0 := hw
    refine ⟨by rw [hw']; exact t0, j, fun x => ?_, ?_⟩
    · exact (congrArg j (h.embLL0_eq x).symm).trans ((t1 (e x)).trans (congrArg _ (eq_of_heq (h.emb0 i i HEq.rfl x))))
    · simp only [GlobalTheory.LamTie.IsLam, BlochKatoReduction.Gen.SOk, hl, hw']
      exact t2

theorem twistPlaces_not_over_leastSplitAuxiliaryPrime {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {hX : B.fields.Ok} {Wt : Set B.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) : ∀ t, ∀ PP ∈ z.R.toRealDat.toLevCh.Q t,
      ((q0 (w.st Z).toD7 : ℕ) : 𝓞 (w.st Z).toD7.host.E) ∉ PP.asIdeal := by
  intro t PP hP hq
  have hprime := (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec (w.st Z).toD7).1
  have two : ∀ p : ℕ, p.Prime → ((p : ℕ) : 𝓞 B.host.E) ∈ PP.asIdeal → q0 (w.st Z).toD7 = p := fun p hp hm => by
    by_contra hne
    have hc : IsCoprime ((q0 (w.st Z).toD7 : ℕ) : 𝓞 B.host.E) ((p : ℕ) : 𝓞 B.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes hprime hp).2 hne)
    obtain ⟨a, b, hab⟩ := hc
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hm)))
  have hd : f.del.UnrAt PP := f.isDel.unr PP fun h => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrime_ne_typePrimes (w.st Z).toD7).1 (two _ B.host.pde_prime h)
  have hd' : f.del'.UnrAt PP := f.isDel'.unr PP fun h => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrime_ne_typePrimes (w.st Z).toD7).2 (two _ B.host.pde'_prime h)
  have hps : ∀ v, (T.psi v).UnrAt PP := fun v => by
    by_contra hn
    obtain ⟨-, h1, -, h2⟩ := (T.psi_tw v).2.2.2 PP hn
    have hmem := Ideal.absNorm_mem PP.asIdeal
    have e := two _ h1 hmem
    exact h2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e.symm))))))
  refine (z.lev.is.Q_ram t PP).2 (Or.inl hP) ?_
  rw [z.lev.xiH t]
  have hm : w.I.xi (GlobalTheory.Mem.R3.ixOf w.I _ t) ∈ T.set f := w.xi_range ▸ ⟨_, rfl⟩
  rcases hm with (h | h | h) | ⟨v, h⟩
  · rw [h]; intro x _; rfl
  · exact h ▸ hd
  · exact (h : _ = _) ▸ hd'
  · rw [← h]
    unfold TwDat.xiTw
    split_ifs
    · exact HChar.UnrAt.mul hd' (hps v)
    · exact HChar.UnrAt.mul hd (hps v)

theorem fr_heq {A A' : Pre} (h : A' = A) {f : Top.Fr A} {f' : Top.Fr A'} (hf : HEq f' f) :
    HEq f'.mu0 f.mu0 ∧ HEq f'.del f.del ∧ HEq f'.del' f.del' := by
  subst h; cases hf; exact ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem lev_fr {K : Ctx} {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) :
    HEq x.m.z.R.toRealDat.toLevCh.C.mu0 f.mu0 ∧ HEq x.m.z.R.toRealDat.toLevCh.C.del f.del ∧
      HEq x.m.z.R.toRealDat.toLevCh.C.del' f.del' := by
  rw [(GlobalTheory.HeightCounting.Up.ListModel.lev_at_state x).1]
  obtain ⟨h1, h2, h3⟩ := fr_heq rfl (heq_of_eq w.C_eq)
  exact ⟨(h1), (h2), (h3)⟩

theorem listPin_copyN {D D' : D7} {N : TwNew D'} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyN D N ι e)
    {D'' : D7} (hD : D'' = N.toD7) {I I' : Type}
    {Lc : Formalism.IndefR.Links.LevCh D I} {Lc' : Formalism.IndefR.Links.LevCh D'' I'} {μ0 : I'} (hL : Lc'.Is μ0)
    (hmu : HEq Lc'.C.mu0 Lc.C.mu0) (hd : HEq Lc'.C.del Lc.C.del) (hd' : HEq Lc'.C.del' Lc.C.del')
    (hP : (∀ k, q0 D'' ≠ D''.host.g k) → Nonempty (Places Lc'))
    (h4 : ∀ t, ∀ PP ∈ Lc'.Q t, ((q0 D'' : ℕ) : 𝓞 D''.host.E) ∉ PP.asIdeal) {CF b : ℝ} (hp : ListPin D Lc CF b) :
    ListPin D'' Lc' CF b := by
  subst hD
  exact listPin_copy h.cp h.jL h.s2 h.Xv hL hmu hd hd' hP h4 hp

end GlobalTheory.HeightCounting.Up.ListCarry

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar



noncomputable section
namespace GlobalTheory.HeightCounting.Fin3

theorem listPin_datL : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (L : LocAll (lay0 (Dof x))) (cDep : ℝ), ListSt cDep x → ListPin (DL x L) (datL x L).R.toRealDat.toLevCh cDep K.s.b := by
  intro K B f T w P x L cDep h
  obtain ⟨G, hField, hTie⟩ := h
  exact ⟨by
      with_unfolding_all
        exact (GlobalTheory.Mem.GridMove.gdC (a := x.o.Z) (oL x L).Z G :),
    ⟨by with_unfolding_all exact (hField.values :),
      by with_unfolding_all exact (hField.roots :)⟩,
    by with_unfolding_all exact (hTie :)⟩

end GlobalTheory.HeightCounting.Fin3
end
end

section

namespace GlobalTheory.T

alias exists_movedData_state_localisations := GlobalTheory.HeightCounting.Fin3.MvLoc.exists_moved_loc

end GlobalTheory.T
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.generator_not_mem_twist_place : ∀ (D : D7) (i : D.ntw.Tw) (P : PlE D.host) (k : Fin 2), P ∈ D.ntw.pD i →
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  first | exact @GlobalTheory.Mem.PdNotType.pD_not_type | exact GlobalTheory.Mem.PdNotType.pD_not_type | (intros; apply GlobalTheory.Mem.PdNotType.pD_not_type <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.typePlaces_union_ramifiedPlaces_finite : ∀ (D : D7) (η : HChar D.host.E), (gPl D ∪ qPl D η).Finite := by
  first | exact @GlobalTheory.LevCmp.gPl_union_qPl_finite | exact GlobalTheory.LevCmp.gPl_union_qPl_finite | (intros; apply GlobalTheory.LevCmp.gPl_union_qPl_finite <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.exists_local_unit_character_nontrivial : ∀ (D : D7) (cf : CharFrame D) (j : Fin D.R.m) (ξH : HChar D.host.E) (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), ξH.TrivOn D.host.F → (∀ u, ξH.TameAt u) → s.v ∈ qPl D (cf.mu0 j * ξH) → NG.IsCompAt (cf.mu0 j * ξH) s ξ → ∃ a : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ, Valued.v (a : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 ∧ ξ a ≠ 1 := by
  first | exact @GlobalTheory.CompRamified.exists_unit_ne_one | exact GlobalTheory.CompRamified.exists_unit_ne_one | (intros; apply GlobalTheory.CompRamified.exists_unit_ne_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.heckeCharacter_splitPlaceComponent_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (χ : HChar L) (s : SplitPlace L) (ξ ξ' : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.IsCompAt χ s ξ → NG.IsCompAt χ s ξ' → ξ = ξ' := by
  first | exact @GlobalTheory.CompAtUniq.main | exact GlobalTheory.CompAtUniq.main | (intros; apply GlobalTheory.CompAtUniq.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.upperParahoric_lowerDet_unit_and_superdiag_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))), NG.ParaRT s r h → Valued.v (NG.detDD s r h) = 1 ∧ Valued.v (NG.supDiag s r h) ≤ 1 := by
  first | exact @GlobalTheory.ParaUnit.detDD_unit_supDiag_int | exact GlobalTheory.ParaUnit.detDD_unit_supDiag_int | (intros; apply GlobalTheory.ParaUnit.detDD_unit_supDiag_int <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.exists_ne_zero_algebraicModularForm_of_trivial_stabiliser : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (W : Type) [AddCommGroup W] [Module K W] [Nontrivial W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ) (g : GAf L n), (∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1) → ∃ f ∈ NX.TypeSpF L n K ρ J χ, f ≠ 0 := by
  first | exact @GlobalTheory.ClassForm.exists_form_of_trivial_stabiliser | exact GlobalTheory.ClassForm.exists_form_of_trivial_stabiliser | (intros; apply GlobalTheory.ClassForm.exists_form_of_trivial_stabiliser <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevUniLoc

theorem mem_iff_uniRT : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) (kv0 : Σ kk : Fin 2, D.nd.PlG kk),
    (∀ kv, kv ≠ kv0 → (M.sp (NX.pG D kv)).v ≠ (M.sp (NX.pG D kv0)).v) →
    (∀ P ∈ M.QP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) → (∀ P ∈ M.DP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) →
    ∀ κ, TrivOutside {(M.sp (NX.pG D kv0)).v} κ →
      (κ ∈ M.J ↔ NG.UniRT (M.sp (NX.pG D kv0)) D.R.r ((M.sp (NX.pG D kv0)).loc D.R.nV κ)) := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ M kv0 hG hQ hD κ hκ
  rw [M.J_mem κ]
  constructor
  · rintro ⟨hU, hL, -, -⟩
    obtain ⟨⟨_, hll⟩, huni⟩ := hL kv0
    exact ⟨⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).2 hU, hll⟩, huni⟩
  · rintro ⟨⟨hGL, hll⟩, huni⟩
    refine ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).1 hGL, fun kv => ?_, fun P hP => ?_, fun P hP => ?_⟩
    · by_cases hk : kv = kv0
      · subst hk
        exact ⟨⟨fun a b => (GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hGL).1 a b, hll⟩, huni⟩
      · rw [GlobalTheory.LevParaLoc.locM_eq_one_of_ne _ _ hκ (hG kv hk)]; exact NX.inLevG_one _ _
    · rw [GlobalTheory.LevParaLoc.locM_eq_one_of_ne _ _ hκ (hQ P hP)]; exact NX.inParah_one _ _
    · rw [GlobalTheory.LevParaLoc.locM_eq_one_of_ne _ _ hκ (hD P hP)]; exact NX.inParah_one _ _

end GlobalTheory.LevUniLoc

end
end
