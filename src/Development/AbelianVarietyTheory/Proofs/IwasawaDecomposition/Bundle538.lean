module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle505
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle523
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AutConjTranslatesDetCharacterMarkings
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle529
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle534
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.GeoTies

set_option synthInstance.maxHeartbeats 400000 in
def BarAtOne {D : D7} (T : CoreJ D) (j : ℕ) (w : WeightFamilies.Wt D j) (s : T.Q.c.F →+* ℂ) {W : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel W S) (Hm : Links.HMod (MMap M)) (jf : T.cuspA j (wtA w) w.n → Hm.H) (Z : Prop) : Prop :=
  ¬ GoodEmb T.Q.c s → ∀ hV : T.V j ((starRingEnd ℂ).comp s) = W,
    ((∃ v : M.Vec, IsUnitV v ∧ EvEx (C := T.cuspA j (wtA w) w.n) s (fun h : Hm.H => Hm.e h v)
        (fun f g => starRingEnd ℂ (phiC T hV (wtA w) (f : T.R j) g))) →
      ∃ v : M.Vec, IsUnitV v ∧ ∀ f, Hm.e (jf f) v = fun g => starRingEnd ℂ (phiC T hV (wtA w) (f : T.R j) g)) ∧
    (¬ (∃ v : M.Vec, IsUnitV v ∧ EvEx (C := T.cuspA j (wtA w) w.n) s (fun h : Hm.H => Hm.e h v)
        (fun f g => starRingEnd ℂ (phiC T hV (wtA w) (f : T.R j) g))) → Z)

theorem barTie_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (t : FWTie T R κ v₀) :
    BarTie t ↔ ∀ (i : Fin D.R.m) σ, BarAtOne T ((i : ℕ) + 1) (κ i) (res T σ) (R.MW i σ) (R.HW i σ) (fun f => t.jK i σ f) ((R.FW i).j σ = 0) :=
  Iff.rfl

theorem BarAtOne.congr {D : D7} (T T' : CoreJ D) (h1 : HEq T'.Q.H T.Q.H) (h2 : HEq T'.Q.l T.Q.l) (h3 : HEq T'.Q.c T.Q.c)
    (h4 : HEq T'.Q.Dw T.Q.Dw) (h5 : HEq T'.Q.Xo T.Q.Xo) (h6 : HEq T'.U T.U) (h7 : HEq T'.V T.V) (h8 : HEq T'.dict T.dict)
    (h9 : HEq T'.mu T.mu) (h10 : HEq T'.cE T.cE) (j : ℕ) (w w' : WeightFamilies.Wt D j) (hP : HEq w'.aP w.aP) (hM : HEq w'.aM w.aM)
    (hn : w'.n = w.n) (s : T.Q.c.F →+* ℂ) (s' : T'.Q.c.F →+* ℂ)
    (hs : ∀ (y : T.Q.c.F) (y' : T'.Q.c.F), (y' : ℂ) = (y : ℂ) → s' y' = s y)
    {W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel W S) (M' : DSModel W S') (hMM : ModelSame M M')
    (Hm : Links.HMod (MMap M)) (Hm' : Links.HMod (MMap M')) (hH : HEq Hm' Hm)
    (jf : T.cuspA j (wtA w) w.n → Hm.H) (jf' : T'.cuspA j (wtA w') w'.n → Hm'.H)
    (hj : ∀ f f', HEq f' f → HEq (jf' f') (jf f)) {Z Z' : Prop} (hZ : Z → Z') :
    BarAtOne T j w s M Hm jf Z → BarAtOne T' j w' s' M' Hm' jf' Z' := by
  obtain ⟨⟨⟨H, l, c, Dw, Xo, eO⟩, U, V, dict, mu, Kf, pb⟩, cE, chiW, x₀, iota⟩ := T
  obtain ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := T'
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases h6
  cases h7
  cases h8
  cases h9
  cases h10
  obtain ⟨aP, aM, _, _, n, _⟩ := w
  obtain ⟨aP', aM', _, _, n', _⟩ := w'
  dsimp only at hP hM hn
  cases hP
  cases hM
  cases hn
  have hs' : s' = s := RingHom.ext fun y => hs y y rfl
  subst hs'
  obtain ⟨X, σ, lam, ε, fr, _, _, _, _⟩ := M
  obtain ⟨X', σ', lam', ε', fr', _, _, _, _⟩ := M'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := hMM
  dsimp only at m1 m2 m3 m4 m5 m6 m7
  cases m1
  cases m2
  cases m3
  cases m4
  cases m5
  cases m6
  cases m7
  have hH' : Hm' = Hm := eq_of_heq hH
  subst hH'
  have hj' : jf' = jf := funext fun f => eq_of_heq (hj f f HEq.rfl)
  subst hj'
  intro h hg hV
  exact ⟨(h hg hV).1, fun h' => hZ ((h hg hV).2 h')⟩

theorem reading_eq_zero {L L' : Type} [Field L] [Field L'] (ι : L →+* L') (σ' : L' →+* ℂ) {n n' : ℕ} (hn : n = n')
    {A A' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
    (j : (Fin n → L) →ₛₗ[σ'.comp ι] A) (j' : (Fin n' → L') →ₛₗ[σ'] A')
    (h : ∀ x x', CrdOver ι x x' → HEq (j' x') (j x)) (h0 : j = 0) : j' = 0 := by
  subst hn
  subst h0
  have hz : HEq (j' 0) (0 : A) := h 0 0 ⟨rfl, fun k k' _ => (map_zero ι).symm⟩
  have hk : ∀ k, j' (Pi.single k 1) = 0 := fun k => by
    have h1 : HEq (j' (Pi.single k 1)) (0 : A) := h (Pi.single k 1) (Pi.single k 1) ⟨rfl, fun a b hab => by
      obtain rfl : a = b := Fin.ext hab
      by_cases hak : a = k
      · subst hak
        simp
      · simp [Pi.single_apply, hak]⟩
    exact (eq_of_heq (h1.trans hz.symm)).trans (map_zero j')
  refine LinearMap.ext fun x => ?_

  rw [pi_eq_sum_univ' x, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smulₛₗ, hk, smul_zero]

theorem barTie_enl : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq w'.px w.px →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → RSide z Wt' R' →
        ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
        ∀ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (fw' : FWTie core' R'.toRealDat κ' v₀'),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
          ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
          (w'.st Z').toD7.what₂.embLL ((fw'.e i' φ' : (R'.FW i').WK).1 k') = (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k)) →
        GeoTies.MWOver z.R.toRealDat R'.toRealDat → BarTie fw' := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hpins hRS κ' hκ v₀' fw' hcrd hMW
  letI := alg'
  letI := z.alg
  have hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom := SetLike.coe_injective hE.2.1
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := (by with_unfolding_all exact ((congrArg (fun P : Pre => P.R.m) hE.1) :))
  refine (barTie_iff fw').2 fun i' σ' => ?_
  let i : Fin (w.st Z).toD7.R.m := ⟨i'.1, hm ▸ i'.2⟩
  have hi : (i : ℕ) = i' := rfl
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL := (by with_unfolding_all exact ((enlEmb hE.2.2.2) :))
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := (by with_unfolding_all exact ((enlEmb_spec hE.2.2.2) :))
  have hb := (barTie_iff z.geo.fw).1 z.geo.bar i (σ'.comp ι)
  have hMM := hMW i i' hi ι hι σ'
  have hnW := hRS.1.2.2.2.2.2.1
  have hcl := ((hRS.1.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).1 σ'
  have hH := hcl.2.1
  have hjj := hcl.2.2.2
  have hs : ∀ (y : z.core.Q.c.F) (y' : core'.Q.c.F), (y' : ℂ) = (y : ℂ) →
      res core' σ' y' = res z.core (σ'.comp ι) y := fun y y' hy =>
    congrArg σ' ((w'.st Z').toD7.what₂.embLL.injective
      (((by with_unfolding_all exact ((halg y') :)) : (w'.st Z').toD7.what₂.embLL (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y') = (y' : ℂ)).trans
        (hy.trans ((hι _).trans ((by with_unfolding_all exact ((z.alg_eq y) :)) :
          (w.st Z).toD7.what₂.embLL (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL y) = (y : ℂ))).symm)))
  have hgen : ∀ {m m' : ℕ} (_ : m' = m) (a : Fin m → ℕ) (a' : Fin m' → ℕ), HEq a' a → ∀ (k : Fin m) (k' : Fin m'),
      (k : ℕ) = k' → a k = a' k' := by
    intro m m' h a a' ha k k' hk
    subst h
    cases ha
    rw [Fin.ext hk]
  have hn : z.R.nW i = R'.nW i' := hgen hm _ _ hnW i i' hi
  have hj : ∀ φ φ', HEq φ' φ → HEq (fw'.jK i' σ' φ') (z.geo.fw.jK i (σ'.comp ι) φ) := fun φ φ' hφ =>
    hjj _ _ ⟨hn, fun k k' hk => (w'.st Z').toD7.what₂.embLL.injective ((hcrd i i' hi φ φ' hφ k k' hk).trans (hι _).symm)⟩
  have hZ : (z.R.FW i).j (σ'.comp ι) = 0 → (R'.FW i').j σ' = 0 := reading_eq_zero ι σ' hn _ _ hjj
  obtain ⟨hP, hM, hnn⟩ := hκ i i' hi
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, -, c10, -⟩ := hc
  have h1 := hE.1
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  let Q₀ : Formalism.L2.Pj.Par (w'.st Z').toD7 :=
    { H := (by with_unfolding_all exact (z.core.Q.H :)), l := (by with_unfolding_all exact (z.core.Q.l :)), c := (by with_unfolding_all exact (z.core.Q.c :)), Dw := (by with_unfolding_all exact (z.core.Q.Dw :)), Xo := (by with_unfolding_all exact (z.core.Q.Xo :)),
      eO := (by with_unfolding_all exact ((z.core.Q.eO.trans (oEquiv hK)) :)) }
  let core₀ : Formalism.L2.Pj.CoreJ (w'.st Z').toD7 :=
    { toCore :=
        { Q := Q₀, U := (by with_unfolding_all exact (z.core.U :)), V := (by with_unfolding_all exact (z.core.V :)), dict := (by with_unfolding_all exact (z.core.dict :)), mu := (by with_unfolding_all exact (z.core.mu :)),
          Kf := (by with_unfolding_all exact (z.core.Kf :)), pb := (by with_unfolding_all exact (z.core.pb :)) }
      cE := (by with_unfolding_all exact (z.core.cE :)), chiW := (by with_unfolding_all exact (z.core.chiW :)), x₀ := (by with_unfolding_all exact (z.core.x₀ :)), iota := (by with_unfolding_all exact (z.core.iota :)) }
  let κ₀ : WeightFamilies.Wt (w'.st Z').toD7 ((i' : ℕ) + 1) :=
    { aP := (by with_unfolding_all exact ((z.geo.κ i).aP :)), aM := (by with_unfolding_all exact ((z.geo.κ i).aM :)), aPlus_antitone := (by with_unfolding_all exact ((z.geo.κ i).aPlus_antitone :)),
      aM_anti := (by with_unfolding_all exact ((z.geo.κ i).aM_anti :)), n := (z.geo.κ i).n, n_even := (z.geo.κ i).n_even }
  let S₀ : (w'.st Z').toD7.what₂.Tau → SPar := (by with_unfolding_all exact ((parAt (Wc (w.st Z).toD7 i) (σ'.comp ι)) :))
  let M₀ : DSModel (Wc (w'.st Z').toD7 i') S₀ :=
    @DSModel.mk _ _ _ ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).H :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).nacg :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ips :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).σ :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).lam :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ε :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).enum :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ds :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr_unit :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr_gram :)))
  let H₀ : Links.HMod (MMap M₀) := (by with_unfolding_all exact ((z.R.HW i (σ'.comp ι)) :))
  let s₀ : core₀.Q.c.F →+* ℂ := (by with_unfolding_all exact ((res z.core (σ'.comp ι)) :))
  let j₀ : core₀.cuspA ((i' : ℕ) + 1) (wtA κ₀) κ₀.n → H₀.H := (by with_unfolding_all exact ((fun φ => z.geo.fw.jK i (σ'.comp ι) φ) :))
  exact BarAtOne.congr core₀ core' ((by with_unfolding_all exact (c1 :))) ((by with_unfolding_all exact (c2 :))) ((by with_unfolding_all exact (c3 :))) ((by with_unfolding_all exact (c4 :))) ((by with_unfolding_all exact (c5 :))) ((by with_unfolding_all exact (c6 :))) ((by with_unfolding_all exact (c7 :))) ((by with_unfolding_all exact (c8 :))) ((by with_unfolding_all exact (c9 :))) ((by with_unfolding_all exact (c10 :)))
    ((i' : ℕ) + 1) κ₀ (κ' i') ((by with_unfolding_all exact (hP :))) ((by with_unfolding_all exact (hM :))) ((by with_unfolding_all exact (hnn :))) s₀ (res core' σ') ((by with_unfolding_all exact (hs :))) M₀ (R'.MW i' σ') ((by with_unfolding_all exact (hMM :)))
    H₀ (R'.HW i' σ') ((by with_unfolding_all exact (hH :))) j₀ _ ((by with_unfolding_all exact (hj :))) hZ ((by with_unfolding_all exact (hb :)))

end GlobalTheory.Mem.R3.Rw.GeoTies
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.DetUnit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem det_mem_intAE (V : HSp D) (g : GA D V)
    (h : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V),
      finMat D.sp.cm.sig V.gram g *ᵥ y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)) :
    finPart D (Formalism.L2.Theta.mt V g).det ∈ intAE D := by
  obtain ⟨L, hL, hfg, hsp⟩ := GlobalTheory.SplitHeckeLabel.exists_coord_lattice V
  have hd : finPart D (Formalism.L2.Theta.mt V g).det = (finMat D.sp.cm.sig V.gram g).det :=
    RingHom.map_det (finPart D) (Formalism.L2.Theta.mt V g)
  rw [hd, GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers]
  rw [← hL] at h
  exact GlobalTheory.DetTranslate.det_mem_int D.host.F L _ hfg hsp h

theorem part_mem_intAE {e d : AE D} (he : e * e = e) (hd : finPart D d ∈ intAE D) :
    finPart D (e * d + (1 - e)) ∈ intAE D := by
  have h1 : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he])
  have h2 : finPart D (1 - e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul]; congr 1; linear_combination he)
  rw [RingHom.map_add (f := _), RingHom.map_mul]
  exact add_mem (GlobalTheory.SplitHeckeLabel.mul_mem_intA h1 hd) h2

theorem exists_isDetAt_unram : ∀ (D : D7) (V : HSp D) (ε : AF D.host.F) (e : AE D), IsSplitIdem D e → e + cA D e = algebraMap (AF D.host.F) (AE D) ε → ∀ g ∈ KsphC V ∅, ∃ x, IsDetAt e V g x ∧ ∀ χ : (AE D)ˣ →* Circle, UnramAt ε χ → χ x = 1 := by
  intro D V ε e he hε g hg
  obtain ⟨h1, h0, -⟩ := he
  have hm : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hd : (Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, hm, Matrix.det_one]
  have hf : finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram g⁻¹ = 1 := by
    change (finHom V g).1 * (finHom V g⁻¹).1 = 1
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have i1 := det_mem_intAE V g fun y hy => (hg.2.1 y).1 hy
  have i2 := det_mem_intAE V g⁻¹ fun y hy => (hg.2.1 _).2 (by rw [Matrix.mulVec_mulVec, hf, Matrix.one_mulVec]; exact hy)
  generalize (Formalism.L2.Theta.mt V g⁻¹).det = d' at hd i2
  have hx : (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) * (e * d' + (1 - e)) = 1 := by
    linear_combination e * e * hd + (2 - (Formalism.L2.Theta.mt V g).det - d') * h1
  refine ⟨⟨_, _, hx, (mul_comm _ _).trans hx⟩, rfl, fun χ hχ => hχ _ ?_ (part_mem_intAE h1 i1) (part_mem_intAE h1 i2)⟩
  rw [← hε]
  change (e + cA D e) * (e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1
  linear_combination ((Formalism.L2.Theta.mt V g).det - 1) * h1 + ((Formalism.L2.Theta.mt V g).det - 1) * h0

end GlobalTheory.Mem.DetUnit
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFin

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.FlagMod GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)

attribute [local instance] Over.cartesianMonoidalCategory

section Push

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {π : X' ⟶ X} {F : G'.left ⟶ G.left} {S S' : Type} [CommRing S] [CommRing S']

def tanPush (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') : TanM x G' →ₗ[S] TanM (x ≫ π) G where
  toFun v := mkT (pushHom h (overAt x (DualNumber S)) (tv v)) (by
    have e : smT (x ≫ π) 0 (pushHom h (overAt x (DualNumber S)) (tv v)) =
        pushHom h (overAt x (DualNumber S)) (smT x 0 (tv v)) := Over.OverMorphism.ext (Category.assoc _ _ _).symm
    rw [e, tv_mem]
    exact map_one _)
  map_add' u v := tanM_ext (map_mul (pushHom h (overAt x (DualNumber S))) _ _)
  map_smul' a v := tanM_ext (Over.OverMorphism.ext (Category.assoc _ _ _))

theorem tanPush_bijective (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') : Function.Bijective (tanPush h x) := by
  have inj : Function.Injective (pushHom h (overAt x (DualNumber S))) := fun p q hpq =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun V => V.left) hpq) ((Over.w p).trans (Over.w q).symm))
  refine ⟨fun u v e => tanM_ext (inj (congrArg tv e)), fun V => ?_⟩
  let p : overAt x (DualNumber S) ⟶ G' :=
    Over.homMk (h.1.lift (tv V).left (overAt x (DualNumber S)).hom (Over.w (tv V))) (h.1.lift_snd _ _ _)
  have hp : pushHom h (overAt x (DualNumber S)) p = tv V := Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  refine ⟨mkT p (inj ?_), tanM_ext hp⟩
  have e : smT (x ≫ π) 0 (pushHom h (overAt x (DualNumber S)) p) =
      pushHom h (overAt x (DualNumber S)) (smT x 0 p) := Over.OverMorphism.ext (Category.assoc _ _ _).symm
  rw [← e, hp, map_one]
  exact tv_mem V

def tanEquiv (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') : TanM x G' ≃ₗ[S] TanM (x ≫ π) G :=
  LinearEquiv.ofBijective _ (tanPush_bijective h x)

theorem tanPull_tanEquiv (h : IsGrpPullback G' G π F) (φ : S →+* S') {x : Sp S ⟶ X'} {x' : Sp S' ⟶ X'}
    (e : spMap φ ≫ x = x') (e' : spMap φ ≫ x ≫ π = x' ≫ π) (v : TanM x G') :
    tanPull φ e' (tanEquiv h x v) = tanEquiv h x' (tanPull φ e v) :=
  tan_ext_left (Category.assoc _ _ _).symm

end Push

theorem ev_pull_g {X X' : Scheme.{0}} {S : Type} [CommRing S] (L : LB X) (π : X' ⟶ X) (z : Sp S ⟶ X')
    (J J' : PUnit → L.ι) (h : ⊤ ≤ z ⁻¹ᵁ ((L.pull π).U J ⊓ (L.pull π).U J'))
    (h' : ⊤ ≤ (z ≫ π) ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit))) :
    ev z _ h ((L.pull π).g J J').val = ev (z ≫ π) _ h' (L.g (J PUnit.unit) (J' PUnit.unit)).val := by
  have le : (L.pull π).U J ⊓ (L.pull π).U J' ≤ π ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => π) J PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => π) J' PUnit.unit))
  have e : (L.pull π).g J J' = res le (pullU π _ (L.g (J PUnit.unit) (J' PUnit.unit))) := by
    show ∏ _k : PUnit, res le (pullU π _ (L.g (J _k) (J' _k))) ^ (1 : ℤ) = _
    rw [Fintype.prod_unique, zpow_one]
  rw [e, ← ev_appLE z π le h]
  rfl

section Det

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l' : Level H}
  {Xo : Moduli D l} {Xo' : Moduli D l'} {c : Coeff l} {c' : Coeff l'} {O O' : Type} [CommRing O] [CommRing O']
  {β : O →+* c.F} {β' : O' →+* c'.F} {Z : Model Xo c β} {Z' : Model Xo' c' β'} {π : Z'.X ⟶ Z.X}
  {F : Z'.t.G.left ⟶ Z.t.G.left} (h : IsGrpPullback Z'.t.G Z.t.G π F) {S : Type} [CommRing S]


end Det

end GlobalTheory.PolFin
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section
namespace GlobalTheory.AmpleOverBase
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.LBGerm
variable {X Y : Scheme.{0}}

theorem gm_val_stalkMap (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    (gm f y U a).val = (f.stalkMap y).hom (gm (𝟙 X) (f y) U a).val := by
  rw [← gs_unit f y U h, ← gs_unit (𝟙 X) (f y) U h]
  exact gs_stalkMap f y U h a.val

theorem isUnit_gs_id_iff (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    IsUnit (gs (𝟙 X) (f y) U a) ↔ IsUnit (gs f y U a) := by
  rw [isUnit_gs_iff (𝟙 X) (f y) U h, isUnit_gs_iff f y U h]
  rfl

theorem stalkMap_injective (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) : Function.Injective (f.stalkMap y).hom :=
  (ConcreteCategory.bijective_of_isIso (f.stalkMap y)).1

theorem bijective_appLE (f : Y ⟶ X) [IsOpenImmersion f] (W : X.Opens) (hW : W ≤ f.opensRange)
    (U : Y.Opens) (e : U ≤ f ⁻¹ᵁ W) (e' : f ⁻¹ᵁ W ≤ U) : Function.Bijective (f.appLE W U e).hom := by
  obtain rfl : U = f ⁻¹ᵁ W := le_antisymm e e'
  rw [Scheme.Hom.appLE_eq_app]
  have := f.isIso_app W hW
  exact ConcreteCategory.bijective_of_isIso (f.app W)

theorem exists_push {L : LB X} (f : Y ⟶ X) [IsOpenImmersion f] (V : X.Opens) (hV : V = f.opensRange) {n : ℕ}
    (t : (lbPow (L.pull f) n).Sec) :
    ∃ T : ∀ J : PUnit → L.ι, Γ(X, V ⊓ powChart L J), T ∈ secOn (lbPow L n) V ∧
      ∀ (y : Y) (J : PUnit → L.ι), f y ∈ powChart L J →
        (IsUnit (gs (𝟙 X) (f y) _ (T J)) ↔ y ∈ nonzeroLocus t) := by
  let J' : (PUnit → L.ι) → PUnit → PUnit → L.ι := fun J _ _ => J PUnit.unit
  have hm : ∀ (y : Y) (J : PUnit → L.ι), y ∈ powChart (L.pull f) (J' J) ↔ f y ∈ powChart L J := fun y J =>
    mem_powChart.trans (mem_pull.trans mem_powChart.symm)
  have e : ∀ J, powChart (L.pull f) (J' J) ≤ f ⁻¹ᵁ (V ⊓ powChart L J) := fun J y hy =>
    ⟨hV ▸ ⟨y, rfl⟩, (hm y J).1 hy⟩
  have e' : ∀ J, f ⁻¹ᵁ (V ⊓ powChart L J) ≤ powChart (L.pull f) (J' J) := fun J y hy => (hm y J).2 hy.2
  choose T hT using fun J =>
    (bijective_appLE f (V ⊓ powChart L J) (inf_le_left.trans hV.le) _ (e J) (e' J)).2 (powFn t (J' J))
  have key : ∀ (y : Y) (J : PUnit → L.ι) (hJ : f y ∈ powChart L J),
      gs f y _ (T J) = gs (𝟙 Y) y _ (powFn t (J' J)) := fun y J hJ => by
    rw [← hT J, gs_appLE f _ _ (e J) (𝟙 Y) y ((hm y J).2 hJ), Category.id_comp]
  refine ⟨T, mem_secOn_of_germ (M := lbPow L n) (V := V) T fun x J K hx hJ hK => ?_, fun y J hJ => ?_⟩
  · obtain ⟨y, rfl⟩ : ∃ y, f y = x := by
      have : x ∈ f.opensRange := hV ▸ hx
      exact this
    change gs (𝟙 X) (f y) (V ⊓ powChart L J) (T J) =
      (gm (𝟙 X) (f y) ((lbPow L n).U J ⊓ (lbPow L n).U K) ((lbPow L n).g J K)).val *
        gs (𝟙 X) (f y) (V ⊓ powChart L K) (T K)
    replace hJ : f y ∈ powChart L J := hJ
    replace hK : f y ∈ powChart L K := hK
    have hJ' := (hm y J).2 hJ
    have hK' := (hm y K).2 hK
    apply stalkMap_injective f y
    rw [map_mul, ← gs_stalkMap f y _ (show f y ∈ V ⊓ powChart L J from ⟨hx, hJ⟩),
      ← gs_stalkMap f y _ (show f y ∈ V ⊓ powChart L K from ⟨hx, hK⟩), key y J hJ, key y K hK,
      gm_lbPow_g n (𝟙 X) (f y) J K hJ hK, Units.val_pow_eq_pow_val, map_pow,
      ← gm_val_stalkMap f y _ (show f y ∈ L.U (J PUnit.unit) ⊓ L.U (K PUnit.unit) from
        ⟨mem_powChart.1 hJ, mem_powChart.1 hK⟩),
      gs_powFn_compat t (𝟙 Y) y (J' J) (J' K) hJ' hK']
    have hJ'' : y ∈ (L.pull f).U (fun _ => J PUnit.unit) := mem_pull.2 (mem_powChart.1 hJ)
    have hK'' : y ∈ (L.pull f).U (fun _ => K PUnit.unit) := mem_pull.2 (mem_powChart.1 hK)
    rw [gm_pull_g L f (𝟙 Y) y _ _ hJ'' hK'', Category.id_comp]
  · rw [isUnit_gs_id_iff f y _ (show f y ∈ V ⊓ powChart L J from ⟨hV ▸ ⟨y, rfl⟩, hJ⟩), key y J hJ]
    exact (mem_nonzeroLocus_iff_powFn t ((hm y J).2 hJ)).symm

end GlobalTheory.AmpleOverBase
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

theorem _root_.GlobalTheory.T.flagRelativeTangentTopChern_ne_zero : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ), rootDiscr m ≠ 0 := by
  first | exact @GlobalTheory.GoodMetric.rootDiscr_ne_zero | exact GlobalTheory.GoodMetric.rootDiscr_ne_zero | (intros; apply GlobalTheory.GoodMetric.rootDiscr_ne_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

theorem _root_.GlobalTheory.T.symmetric_poly_chern_roots : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (S : MvPolynomial (Root m) ℝ), (∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S) → ∃ R : MvPolynomial (ι × ℕ) ℝ, chernRoots m R = S := by
  first | exact @GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric | exact GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric | (intros; apply GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.flag_space_dimension_eq_sum_choose : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H), Dw.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 = Module.finrank ℚ E / 2 * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) := by
  first | exact @GlobalTheory.FlagDimSum.dim_add_sum_choose | exact GlobalTheory.FlagDimSum.dim_add_sum_choose | (intros; apply GlobalTheory.FlagDimSum.dim_add_sum_choose <;> assumption)
end
