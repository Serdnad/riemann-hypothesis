module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle505
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle538
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle506
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle485
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle494
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle484
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnKernelDataCompatibleStepCharts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle358
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle539
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle028
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieTrF
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle296
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.SelfDualAtColLevel
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo


noncomputable section

namespace GlobalTheory.Mem.R3.Rw.EvZero

open GlobalTheory.Mem.R3.Rw.GeoTies

def NoEvAtOne {D : D7} (T : CoreJ D) (j : ℕ) (w : WeightFamilies.Wt D j) (s : T.Q.c.F →+* ℂ) {W : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel W S) (Hm : Links.HMod (MMap M)) (v : M.Vec) {L : Type} [Field L] (σ : L →+* ℂ) {n : ℕ}
    (c : T.cuspA j (wtA w) w.n → Fin n → L) (Z : Prop) : Prop :=
  GoodEmb T.Q.c s → ∀ hV : T.V j s = W,
    (¬ ∃ j' : (Fin n → L) →ₛₗ[σ] Hm.H, ∀ f : T.cuspA j (wtA w) w.n,
      Hm.e (j' (c f)) v = phiC T hV (wtA w) (f : T.R j)) → Z

theorem exists_extend {L L' : Type} [Field L] [Field L'] (ι : L →+* L') (σ' : L' →+* ℂ) {n : ℕ}
    {A : Type} [AddCommGroup A] [Module ℂ A] (j : (Fin n → L) →ₛₗ[σ'.comp ι] A) :
    ∃ j' : (Fin n → L') →ₛₗ[σ'] A, ∀ x x', CrdOver ι x x' → j' x' = j x := by
  refine ⟨{ toFun := fun x' => ∑ k, σ' (x' k) • j (Pi.single k 1), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    simp only [Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]
  · intro a x
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]
  · intro x x' h
    change ∑ k, σ' (x' k) • j (Pi.single k 1) = j x

    conv_rhs => rw [pi_eq_sum_univ' x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, h.2 k k rfl]
    rfl

theorem NoEvAtOne.congr {D : D7} (T T' : CoreJ D) (h1 : HEq T'.Q.H T.Q.H) (h2 : HEq T'.Q.l T.Q.l) (h3 : HEq T'.Q.c T.Q.c)
    (h4 : HEq T'.Q.Dw T.Q.Dw) (h5 : HEq T'.Q.Xo T.Q.Xo) (h6 : HEq T'.U T.U) (h7 : HEq T'.V T.V) (h8 : HEq T'.dict T.dict)
    (h9 : HEq T'.mu T.mu) (h10 : HEq T'.cE T.cE) (j : ℕ) (w w' : WeightFamilies.Wt D j) (hP : HEq w'.aP w.aP) (hM : HEq w'.aM w.aM)
    (hn : w'.n = w.n) (s : T.Q.c.F →+* ℂ) (s' : T'.Q.c.F →+* ℂ)
    (hs : ∀ (y : T.Q.c.F) (y' : T'.Q.c.F), (y' : ℂ) = (y : ℂ) → s' y' = s y)
    {W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel W S) (M' : DSModel W S') (hMM : ModelSame M M')
    (Hm : Links.HMod (MMap M)) (Hm' : Links.HMod (MMap M')) (hH : HEq Hm' Hm) (v : M.Vec) (v' : M'.Vec) (hv : HEq v' v)
    {L L' : Type} [Field L] [Field L'] (ι : L →+* L') (σ' : L' →+* ℂ) {n n' : ℕ} (hnn : n = n')
    (c : T.cuspA j (wtA w) w.n → Fin n → L) (c' : T'.cuspA j (wtA w') w'.n → Fin n' → L')
    (hc : ∀ f f', HEq f' f → CrdOver ι (c f) (c' f')) {Z Z' : Prop} (hZ : Z → Z') :
    NoEvAtOne T j w s M Hm v (σ'.comp ι) c Z → NoEvAtOne T' j w' s' M' Hm' v' σ' c' Z' := by
  obtain ⟨⟨⟨H, l, cc, Dw, Xo, eO⟩, U, V, dict, mu, Kf, pb⟩, cE, chiW, x₀, iota⟩ := T
  obtain ⟨⟨⟨H', l', cc', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := T'
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
  obtain ⟨aP, aM, _, _, m, _⟩ := w
  obtain ⟨aP', aM', _, _, m', _⟩ := w'
  dsimp only at hP hM hn
  cases hP
  cases hM
  cases hn
  have hs' : s' = s := RingHom.ext fun y => hs y y rfl
  subst hs'
  obtain ⟨X, σ, lam, ε, fr, _, _, _, _⟩ := M
  obtain ⟨X', σ'', lam', ε', fr', _, _, _, _⟩ := M'
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
  have hv' : v' = v := eq_of_heq hv
  subst hv'
  subst hnn
  intro h hg hV hno
  refine hZ (h hg hV ?_)
  rintro ⟨j₀, hj₀⟩
  obtain ⟨j', hj'⟩ := exists_extend ι σ' j₀
  exact hno ⟨j', fun f => by rw [hj' _ _ (hc f f HEq.rfl)]; exact hj₀ f⟩

def intEquivOfEq {F F' : IntermediateField ℚ ℂ} (h : F' = F) : 𝓞 F ≃+* 𝓞 F' := by
  subst h
  exact RingEquiv.refl _

theorem coeff_field_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {l' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H'}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l'}
    (h1 : HEq H' H) (h2 : HEq l' l) (h3 : HEq c' c) : c'.F = c.F := by
  cases h1
  cases h2
  cases h3
  rfl

theorem enlargedBase_reading_zero_without_evaluationProperty : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
    B'.toPre = B.toPre → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt) (hX' : B'.fields.Ok)
    (Wt' : Set B'.places.Pl) (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
    (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
    (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
    Formalism.L2.Pj.LawsCore core'.toCore →
    letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
      (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F),
      RSideW z Wt' R' → HEq R'.toLevCh.mu0 z.R.toLevCh.mu0 →
      ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) →
      ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
      ∀ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ σ' : (w'.st Z').toD7.what₂.LL →+* ℂ,
          HEq (v₀' i' σ') (z.geo.v₀ i (σ'.comp ι))) →
      ∀ (e' : ∀ i : Fin (w'.st Z').toD7.R.m, core'.cuspA ((i : ℕ) + 1) (wtA (κ' i)) (κ' i).n ≃ₗ[core'.Q.c.F] (R'.FW i).WK),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
          CrdOver ι (z.geo.fw.e i φ : (z.R.FW i).WK).1 (e' i' φ' : (R'.FW i').WK).1) →
      ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), Formalism.L2.Pj.GoodEmb core'.Q.c (σ.comp (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL)) →
        ∀ hV : core'.V ((i : ℕ) + 1) (σ.comp (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL)) = Wc (w'.st Z').toD7 i,
        (¬ ∃ j' : (Fin (R'.nW i) → (w'.st Z').toD7.what₂.LL) →ₛₗ[σ] (R'.HW i σ).H, ∀ f : core'.cuspA ((i : ℕ) + 1) (wtA (κ' i)) (κ' i).n,
          ((R'.HW i σ).e (j' ((e' i f : (R'.FW i).WK) : Fin (R'.nW i) → (w'.st Z').toD7.what₂.LL))) (v₀' i σ) =
            hV ▸ core'.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL)) (wtA (κ' i)) (f : core'.R ((i : ℕ) + 1))) →
        (R'.FW i).j σ = 0 := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hc _ Xg tr R' hRS _ ι hι κ' hκ v₀' hv e' he i' σ'
  letI := alg'
  letI := z.alg
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := (by with_unfolding_all exact ((congrArg (fun P : Pre => P.R.m) hPre) :))
  let i : Fin (w.st Z).toD7.R.m := ⟨i'.1, hm ▸ i'.2⟩
  have hi : (i : ℕ) = i' := rfl
  have hb : NoEvAtOne z.core ((i : ℕ) + 1) (z.geo.κ i) (res z.core (σ'.comp ι)) (z.R.MW i (σ'.comp ι)) (z.R.HW i (σ'.comp ι))
      (z.geo.v₀ i (σ'.comp ι)) (σ'.comp ι) (fun φ => (z.geo.fw.e i φ : (z.R.FW i).WK).1) ((z.R.FW i).j (σ'.comp ι) = 0) :=
    z.geo.fw.ev0 i (σ'.comp ι)
  have hnW := hRS.2.2.2.2.2.1
  have hcl := ((hRS.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).1 σ'
  have hMM : ModelSame (z.R.MW i (σ'.comp ι)) (R'.MW i' σ') :=
    ⟨hcl.1.1, hcl.1.2.1, hcl.1.2.2.1, hcl.1.2.2.2.1, hcl.1.2.2.2.2.1, hcl.1.2.2.2.2.2.1, hcl.1.2.2.2.2.2.2.1⟩
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
  have hZ : (z.R.FW i).j (σ'.comp ι) = 0 → (R'.FW i').j σ' = 0 := reading_eq_zero ι σ' hn _ _ hjj
  have hv1 := hv i i' hi σ'
  have he1 := he i i' hi
  obtain ⟨hP, hM, hnn⟩ := hκ i i' hi
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, -, c10, -⟩ := hc
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  let H₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host (w'.st Z').toD7.host.E := (by with_unfolding_all exact (z.core.Q.H :))
  let l₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₁ := (by with_unfolding_all exact (z.core.Q.l :))
  let c₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₁ := (by with_unfolding_all exact (z.core.Q.c :))
  have hF : core'.Q.c.F = c₁.F := coeff_field_eq (H := H₁) (l := l₁) (c := c₁) ((by with_unfolding_all exact (c1 :))) ((by with_unfolding_all exact (c2 :))) ((by with_unfolding_all exact (c3 :)))
  let Q₀ : Formalism.L2.Pj.Par (w'.st Z').toD7 :=
    { H := H₁, l := l₁, c := c₁, Dw := (by with_unfolding_all exact (z.core.Q.Dw :)), Xo := (by with_unfolding_all exact (z.core.Q.Xo :)),
      eO := (intEquivOfEq hF).trans core'.Q.eO }
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
  let u₀ : M₀.Vec := (by with_unfolding_all exact ((z.geo.v₀ i (σ'.comp ι)) :))
  let s₀ : core₀.Q.c.F →+* ℂ := (by with_unfolding_all exact ((res z.core (σ'.comp ι)) :))
  let c₀ : core₀.cuspA ((i' : ℕ) + 1) (wtA κ₀) κ₀.n → Fin (z.R.nW i) → (w.st Z).toD7.what₂.LL :=
    (by with_unfolding_all exact ((fun φ => (z.geo.fw.e i φ : (z.R.FW i).WK).1) :))
  exact (by with_unfolding_all exact ((NoEvAtOne.congr core₀ core' ((c1)) ((c2)) ((c3)) ((c4)) ((c5)) ((c6)) ((c7)) ((c8)) ((c9)) ((c10))
    ((i' : ℕ) + 1) κ₀ (κ' i') ((hP)) ((hM)) ((hnn)) s₀ (res core' σ') ((hs)) M₀ (R'.MW i' σ') ((hMM))
    H₀ (R'.HW i' σ') ((hH)) u₀ (v₀' i' σ') ((hv1)) ι σ' hn c₀ (fun φ => (e' i' φ : (R'.FW i').WK).1) ((he1)) hZ ((hb))) : _))

end GlobalTheory.Mem.R3.Rw.EvZero

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi.LocVal

theorem midLev_one_one {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (al : (I.idx a).β i)
    (P : SBof I a) : GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) 1 1 := by
  classical
  obtain ⟨z, r, hr, hrx, hz⟩ := (GlobalTheory.TwU.exists_midLev_iff I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) 1).2 (Subgroup.one_mem _)
  refine ⟨r, hr, hrx, ?_⟩
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · rw [chiInv_at_type I hOk a i al P hP 1 1 r hr hrx 1 (one_mem _) (fun x _ => by simp) (congE_refl _ _ _)]
    have e : (((I.idx a).levG i al) ⟨P.1, hP⟩).lam ⟨1, one_mem _⟩ = 1 := map_one (((I.idx a).levG i al) ⟨P.1, hP⟩).lam
    rw [e]; simp
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
    rw [chiInv_at_twist I hOk a i hi al P hQ 1 1 r hr hrx 1 (one_mem _) (by simp) (congE_refl _ _ _)]
    have e : (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ⟨1, one_mem _⟩ = 1 := map_one (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam
    rw [e]; simp


open Classical in
theorem exists_frNear_one_over {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (n : ℕ)
    (k : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))
    (hk : bc (prV (E := (I.rec7 l Z).host.E) v) k = 1) :
    ∃ fb : SBof I a → GL (Fin n) (I.rec7 l Z).host.E, FrNear I l Z a k fb ∧ ∀ P, IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → fb P = 1 := by
  obtain ⟨fb0, h0⟩ := GlobalTheory.Mem.Col2.AdT.frNear_exists I hOk l Z a n k
  refine ⟨fun P => if IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) then 1 else fb0 P, fun P => ?_, fun P hP => if_pos hP⟩
  by_cases hv : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)
  · simp only [if_pos hv]
    refine ⟨?_, ?_⟩
    · have h2 := GlobalTheory.AwayFr.congAt_of_prV_eq _ _ hv ((I.cst a).D P) k 1 (by rw [map_one, hk])
      simpa using h2
    · have h2 := GlobalTheory.AwayFr.congAt_of_prV_eq _ _ hv ((I.cst a).D P) 1 k (by rw [map_one, hk])
      simpa using h2
  · simp only [if_neg hv]
    exact h0 P

theorem nearAt_emb_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (hP : ¬ IsOver v P) (d : ℕ)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g : GL (Fin n) E) (hg : g = 1) :
    GlobalTheory.TwU.NearAt P d (y⁻¹ * GlobalTheory.Mem.Col2.ChartLevel.emb v x * y) g := by
  subst hg
  have hw : IsOver (P.under (𝓞 F)) P := by
    unfold IsOver
    rw [HeightOneSpectrum.under_asIdeal]
  have hne : P.under (𝓞 F) ≠ v := fun e => hP (e ▸ hw)
  unfold GlobalTheory.TwU.NearAt
  refine GlobalTheory.AwayFr.congAt_of_prV_eq _ _ hw d _ _ ?_
  rw [map_one, map_one, map_mul, map_mul, GlobalTheory.Mem.Col2.ChartLevel.emb_ne hne, mul_one, ← map_mul, inv_mul_cancel, map_one]

end GlobalTheory.Mem.Col2.QChi.LocVal

namespace GlobalTheory.Mem.Col2.QChi



theorem chi_embU_mul_valV : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Q → ∀ β (x : (K β).lev.Uloc v), (((K β).lev.chi (GlobalTheory.Mem.Col2.ChartLevel.embU (K β).lev v x) : ℂˣ) : ℂ) * GlobalTheory.Mem.Col2.QChi.valV I l Z a v x.1 = 1 := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch _ chOf K g hQ _ _ hRd hFin _ _ Lb0 _ v hvQ β x
  classical
  obtain ⟨k, hR, hk1⟩ := hRd
  obtain ⟨c, rfl⟩ := hR.onto β
  obtain ⟨fb, hfb, hfb1⟩ := LocVal.exists_frNear_one_over I hOk l Z a _ (k (chOf c)) v (hk1 _ v ((hQ v).1 hvQ))
  have hm : B.R.m - 1 < B.R.m := by omega
  have hlast : B.R.m - 1 + 1 = B.R.m := by omega
  let y0 : SBof I a → Sp B.fields.E (B.R.N (B.R.m - 1)) := fun P =>
    ((GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a _ ((I.stp u a _).rep c) P).2 hlast).1.some
  have H := lev_mid hOk hPins hR c hfb (hFin _) hm y0
    (Rel := fun P g z => MidAt I hm c.1 P g z ∧ (B.R.m - 1 + 1 = B.R.m → GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g (y0 P)) (y0 P)))
    (fun _ P => ((GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a _ ((I.stp u a _).rep c) P).2 hlast).1.some_mem) (fun _ _ _ => Iff.rfl)
  have hx : bc (prV (E := (I.rec7 l Z).host.E) v) (GlobalTheory.Mem.Col2.ChartLevel.emb v x.1) ∈ (K (chOf c)).lev.Uloc v := by
    rw [GlobalTheory.Mem.Col2.ChartLevel.emb_self]; exact x.2
  have key : ∀ (P : SBof I a) (j : ℕ), j = B.R.m - 2 + 1 → ∀ b, (I.idx a).h j b P = 1 := by
    rintro P j rfl b
    exact (hOk.idx_ok a).last_h b P
  have hall : ∀ P : SBof I a, ∃ g z, ((MidAt I hm c.1 P g z ∧ (B.R.m - 1 + 1 = B.R.m →
      GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g (y0 P)) (y0 P))) ∧
      GlobalTheory.TwU.InFrame (sm I l Z) fb (I.cst a).D P (GlobalTheory.Mem.Col2.ChartLevel.emb v x.1) g) ∧
      z = (if h : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x.1 g z then h.2.choose_spec.choose else 1) := by
    intro P
    by_cases hP : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)
    · obtain ⟨g, z, hrel, hin⟩ := H.1 P v hP _ (((K (chOf c)).lev.U_eq _).1 (GlobalTheory.Mem.Col2.ChartLevel.embU _ v x).2).1 hx
      have hnp : NearPair I l Z a v P x.1 g z := by
        refine ⟨?_, ?_⟩
        · have hmid := hrel.1
          unfold MidAt at hmid
          rw [key P _ (by omega)] at hmid
          exact hmid
        · have hin' := hin
          unfold NearV
          unfold GlobalTheory.TwU.InFrame at hin'
          rw [hfb1 P hP] at hin'
          first
            | (simp only [GlobalTheory.TwU.ratA, map_one, inv_one, one_mul, mul_one] at hin'; exact hin')
            | (erw [map_one, inv_one, one_mul, mul_one] at hin'; exact hin')
            | (convert hin' using 2; simp)
      have hh : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x.1 g z := ⟨hP, g, z, hnp⟩
      refine ⟨g, z, ⟨hrel, hin⟩, ?_⟩
      rw [dite_eq_left hh]
      exact nearPair_val_unique I hOk l Z a v P x.1 _ _ _ _ hnp hh.2.choose_spec.choose_spec
    · refine ⟨1, 1, ⟨⟨LocVal.midLev_one_one I hOk a _ hm _ P, fun _ t => ?_⟩, ?_⟩, by rw [dite_eq_right (fun h => hP (And.left h))]⟩
      · have e : ((1 : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (y0 P) - y0 P) t = 0 := by
          show (y0 P - y0 P) t = 0
          rw [sub_self]; rfl
        rw [e, mul_zero]
        simpa using GlobalTheory.TopInv.intAt_nat (P := P.1) 0
      · unfold GlobalTheory.TwU.InFrame
        exact LocVal.nearAt_emb_one v _ hP _ _ _ _ (map_one (GlobalTheory.TwU.seamGL (sm I l Z)))
  choose gg zz hgz hz using hall
  have hc := H.2.2 (GlobalTheory.Mem.Col2.ChartLevel.embU _ v x) gg zz hgz
  unfold valV
  rw [← Finset.prod_congr rfl fun P _ => hz P]
  exact hc

end GlobalTheory.Mem.Col2.QChi

end
end

section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.TrueLocal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.LocalPack GlobalTheory.Mem.ConcreteRecord

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

def IsLocalFamily (sc : Scale) (D : D7) (L0 : LevelData D) (T : ∀ u : D.what₂.Word, Forms0 D u)
    (g : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → GAtP (D.what₂.places.resChar w)) : Prop :=
  ∃ (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (L0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (B : GL (Fin D.R.k) D.host.E)
    (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
    (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]),
    Cmp.StdB D B ∧
    (∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B) ∧
    (∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D.what₂.embLL z)) ∧
    (∀ u w hg, (packC D (fun u => L0 u) I ψ u w hg).posOK (iK u w hg) (lam u w hg)) ∧
    (∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
        (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
        ((T u).cls0).lev (L0 u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        (embRec D w (nFr D (D.what₂.places.resChar w))) (ψ u w hg)) ∧
    g = gatOf D L0 I ψ sc



theorem exists_isLocalFamily (sc : Scale) {D : D7} {L0 : LevelData D} (T : ∀ u : D.what₂.Word, Forms0 D u)
    (hS : Formalism.L2.Herm.StdTied D) (hC : Companion D L0) (hJ : ∀ u, Joint0 L0 u (T u)) (hψ : ∀ u, LevelZeroCharacterRational T u) :
    ∃ g, (∀ u w h, (g u w h).d = Module.finrank ℂ (D.mem u).A.Mu0) ∧ IsLocalFamily sc D L0 T g :=
  let I := placeId D L0 hS hC
  have hAway := GlobalTheory.Mem.AwayChar.exists_psi D L0 T hJ hψ
  let ψ := fun u w hg => Classical.choose (hAway u w hg)
  have hTied := fun u w hg => Classical.choose_spec (hAway u w hg)
  let g := gatOf D L0 I ψ sc
  have hd := gatOf_d D L0 T hJ I ψ sc
  have h : IsLocalFamily sc D L0 T g :=
    ⟨I, ψ, stdBasis D hS, embK D L0, embAlg D L0, stdBasis_std D hS, fun _ _ _ _ _ => rfl,
      embK_embAlg D L0, posOK_placeId (D := D) (L0 := L0) hS hC ψ, hTied, rfl⟩
  ⟨g, hd, h⟩



theorem isRecG_of_isLocalFamily {sc : Scale} {D : D7} {L0 : LevelData D} {T : ∀ u : D.what₂.Word, Forms0 D u}
    (hJ : ∀ u, Joint0 L0 u (T u)) (hψ : ∀ u, LevelZeroCharacterRational T u) {g} (hd : ∀ u w h, (g u w h).d = Module.finrank ℂ (D.mem u).A.Mu0)
    (h : IsLocalFamily sc D L0 T g) :
    ∃ (Gt : GatTies (setGat D g hd)) (c : LatCmp (setGat D g hd)) (G : GroupCompatibilityAll (setGat D g hd) Gt c),
      IsRecG sc (setGat D g hd) Gt c G.herm G.forms ∧ (∀ u, G.herm.lev0 u = L0 u) ∧ (∀ u, G.forms u = forms0Set D g hd (T u)) ∧
      ∀ u w hg (v : Fin ((setGat D g hd).gat u w hg).P.nV) (s : Fin (((setGat D g hd).gat u w hg).P.n' v)) (x : 𝓞 D.host.F),
        x ∈ ((G.herm.g u w hg).pl v).1.asIdeal ↔
          (0 : WithTop ℤ) < D.what₂.places.val w (tauLL (setGat D g hd) (Gt.gat_pos u w hg ⟨v, s⟩)
            (algebraMap D.host.F D.host.E (x : D.host.F))) := by
  obtain ⟨I, ψ, B, iK, lam, hBs, hB, hK, hPos, hψ', rfl⟩ := h
  exact
    let buildRec := recC D sc 1 L0 I
    -- Infer the character type from `recC` to reuse its unit instances in the constructions below.
    let ψ := (fun {A : Type} {B : A → Type 1} (_ : ∀ a, B a) (a : A) => a) buildRec ψ
    let D' := buildRec ψ hd
    let H0 : Formalism.L2.Herm.Herm0 D' := ⟨L0, levTieG D sc 1 L0 (packC D L0 I ψ) hd⟩
    have hL : ∀ u, H0.lev0 u = L0 u := fun _ => rfl
    let T' : ∀ u, Forms0 D' u := fun u => forms0Set D D'.gat D'.gat_d (T u)
    let Gt := gatTiesC D sc 1 L0 I ψ hd
    let cmp := cmpInC D sc 1 L0 I ψ hd H0 hL B hBs hB
    have CH := Test.comparison_statements D sc L0 I ψ hd H0 hL T' B hBs hB iK lam hK hPos hJ hψ hψ'
    have hpos := pos_C D sc 1 L0 I ψ hd H0 hL B hBs hB iK lam hK hPos
    have hcmp := (CH.toHyp0 hpos).toHyp
    let c := Cmp.latCmpC T' Gt cmp hcmp
    let G : GroupCompatibilityAll D' Gt c :=
      groupCompatibilityOfRecursion D sc 1 L0 I ψ hd H0 hL T' B hBs hB hcmp
        (fun u w hg => isHyperbolicAt_rec_of_placeIdentification D u w hg (I u w hg))
    have hRec : IsRecG sc D' Gt c H0 T' :=
      IsRecG.intro D L0 I ψ hd H0 hL T' B hBs hB iK lam hK hPos CH rfl
    have hRetie : IsRecG sc D' Gt c G.herm G.forms :=
      LayerTwoModel.isRecG_retie hRec G.herm.g
    have hPlace := GlobalTheory.T.mem_localPlace_asIdeal_iff_val_pos
      D sc 1 L0 I ψ hd H0 hL B hBs hB iK lam hK hPos
    ⟨Gt, c, G, hRetie, fun _ => rfl, fun _ => rfl, hPlace⟩

end GlobalTheory.Mem.Top.Bl.TrueLocal

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_lowestKType_fockMap_thetaVectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → R.thP_pt_theta ∧ ∃ io, ({ R with ioP := io } : RealDat D A Ks).thP_ioP := by
  first | exact @GlobalTheory.JointHarm.exists_ioP | exact GlobalTheory.JointHarm.exists_ioP | (intros; apply GlobalTheory.JointHarm.exists_ioP <;> assumption)
end
