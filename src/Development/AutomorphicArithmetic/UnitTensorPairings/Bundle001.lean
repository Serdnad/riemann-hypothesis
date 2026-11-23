module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo


theorem UpperTheory.cuspCoreDatum_transport_of_same_pre :
    ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
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
          ∃ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ σ' : (w'.st Z').toD7.what₂.LL →+* ℂ,
              HEq (v₀' i' σ') (z.geo.v₀ i (σ'.comp ι))) := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hR hmu ι hι
  obtain ⟨P'⟩ := B'
  dsimp only at hPre
  subst hPre
  clear hmu hlaws hcore
  have key : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ),
      ∃ v : (R'.MW i σ).Vec, HEq v (z.geo.v₀ i (σ.comp ι)) := by
    intro i σ
    have hs := ((hR.2.2.2.2.2.2.2.2.2.2.2.2.1 i i rfl).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).1 σ
    obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, -⟩, -⟩ := hs
    clear hR
    generalize R'.MW i σ = M' at h1 h2 h3 h4 h5 h6 h7 ⊢
    obtain @⟨H, nacg, ips, sg, lam, ep, fr, enum, ds, fu, fg⟩ := M'
    dsimp only at h1 h2 h3 h4 h5 h6 h7
    ( (
  have e : @Eq (type_of% (H)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).H) :))) (H) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (H)) (H) ((((z.R.MW i (σ.comp ι)).H))) (((h1)))).symm : _))
  clear (h1)
  subst e))
    ( (
  have e : @Eq (type_of% (nacg)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).nacg) :))) (nacg) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (nacg)) (nacg) ((((z.R.MW i (σ.comp ι)).nacg))) (((h2)))).symm : _))
  clear (h2)
  subst e))
    ( (
  have e : @Eq (type_of% (ips)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).ips) :))) (ips) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ips)) (ips) ((((z.R.MW i (σ.comp ι)).ips))) (((h3)))).symm : _))
  clear (h3)
  subst e))
    ( (
  have e : @Eq (type_of% (sg)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).σ) :))) (sg) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (sg)) (sg) ((((z.R.MW i (σ.comp ι)).σ))) (((h4)))).symm : _))
  clear (h4)
  subst e))
    ( (
  have e : @Eq (type_of% (lam)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).lam) :))) (lam) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (lam)) (lam) ((((z.R.MW i (σ.comp ι)).lam))) (((h5)))).symm : _))
  clear (h5)
  subst e))
    ( (
  have e : @Eq (type_of% (ep)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).ε) :))) (ep) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ep)) (ep) ((((z.R.MW i (σ.comp ι)).ε))) (((h6)))).symm : _))
  clear (h6)
  subst e))
    ( (
  have e : @Eq (type_of% (fr)) ((by with_unfolding_all exact (((z.R.MW i (σ.comp ι)).fr) :))) (fr) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (fr)) (fr) ((((z.R.MW i (σ.comp ι)).fr))) (((h7)))).symm : _))
  clear (h7)
  subst e))
    exact ⟨(by with_unfolding_all exact ((z.geo.v₀ i (σ.comp ι)) :)), (by with_unfolding_all exact ((HEq.refl (z.geo.v₀ i (σ.comp ι))) :))⟩
  choose v hv using key
  refine ⟨v, fun i i' hi σ' => ?_⟩
  have e : i = i' := Fin.ext hi
  subst e
  exact hv i σ'
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo


private def UpperTheory.LocalNormsMatchCuspForms {D : D7} (T : CoreJ D) (j : ℕ) (w : WeightFamilies.Wt D j)
    (Pt : HeightOneSpectrum (𝓞 T.Q.c.F) → Type) {W : Type} (nrm : ∀ la, Pt la → W → ℝ)
    (e : T.cuspA j (wtA w) w.n → W) (pt : ∀ la, Pt la → T.PtM j la) : Prop :=
  ∀ la (y : Pt la) (f : T.cuspA j (wtA w) w.n), nrm la y (e f) = T.nrmM j la (pt la y) (f : T.R j)

private theorem UpperTheory.congr_of_heq {D : D7} (T T' : CoreJ D) (h1 : HEq T'.Q.H T.Q.H) (h2 : HEq T'.Q.l T.Q.l) (h3 : HEq T'.Q.c T.Q.c)
    (h4 : HEq T'.Q.Dw T.Q.Dw) (h5 : HEq T'.Q.Xo T.Q.Xo) (h6 : HEq T'.U T.U)
    (j : ℕ) (w w' : WeightFamilies.Wt D j) (hP : HEq w'.aP w.aP) (hM : HEq w'.aM w.aM) (hn : w'.n = w.n)
    (Pt : HeightOneSpectrum (𝓞 T.Q.c.F) → Type) (Pt' : HeightOneSpectrum (𝓞 T'.Q.c.F) → Type) (hPt : HEq Pt' Pt)
    {W W' : Type} (Rel : W → W' → Prop) (nrm : ∀ la, Pt la → W → ℝ) (nrm' : ∀ la, Pt' la → W' → ℝ)
    (hnrm : ∀ la' la, HEq la' la → ∀ y' y, HEq y' y → ∀ φ' φ, Rel φ φ' → nrm' la' y' φ' = nrm la y φ)
    (e : T.cuspA j (wtA w) w.n → W) (e' : T'.cuspA j (wtA w') w'.n → W') (he : ∀ φ φ', HEq φ' φ → Rel (e φ) (e' φ'))
    (pt : ∀ la, Pt la → T.PtM j la) (pt' : ∀ la, Pt' la → T'.PtM j la)
    (hpt : ∀ la la', HEq la' la → ∀ y' y, HEq y' y → HEq (pt' la' y') (pt la y)) :
    UpperTheory.LocalNormsMatchCuspForms T j w Pt nrm e pt → UpperTheory.LocalNormsMatchCuspForms T' j w' Pt' nrm' e' pt' := by
  obtain ⟨⟨⟨H, l, cc, Dw, Xo, eO⟩, U, V, dict, mu, Kf, pb⟩, cE, chiW, x₀, iota⟩ := T
  obtain ⟨⟨⟨H', l', cc', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := T'
  dsimp only at h1 h2 h3 h4 h5 h6
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases h6
  obtain ⟨aP, aM, _, _, m, _⟩ := w
  obtain ⟨aP', aM', _, _, m', _⟩ := w'
  dsimp only at hP hM hn
  cases hP
  cases hM
  cases hn
  cases hPt
  intro h la y f
  have k1 := hnrm la la HEq.rfl y y HEq.rfl _ _ (he f f HEq.rfl)
  have k3 : pt' la y = pt la y := eq_of_heq (hpt la la HEq.rfl y y HEq.rfl)
  rw [k1, k3]
  exact h la y f

private noncomputable def UpperTheory.ringOfIntegersEquivOfEqSubfield {F F' : IntermediateField ℚ ℂ} (h : F' = F) : 𝓞 F ≃+* 𝓞 F' := by
  subst h
  exact RingEquiv.refl _

private theorem UpperTheory.coeff_field_eq_of_heq {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {l' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H'}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l'}
    (h1 : HEq H' H) (h2 : HEq l' l) (h3 : HEq c' c) : c'.F = c.F := by
  cases h1
  cases h2
  cases h3
  rfl

theorem UpperTheory.localCuspNorms_indep_of_base_same_pre :
    ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
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
          ∀ (e' : ∀ i : Fin (w'.st Z').toD7.R.m, core'.cuspA ((i : ℕ) + 1) (wtA (κ' i)) (κ' i).n ≃ₗ[core'.Q.c.F] (R'.FW i).WK),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
              CrdOver ι (z.geo.fw.e i φ : (z.R.FW i).WK).1 (e' i' φ' : (R'.FW i').WK).1) →
          ∀ (pt' : ∀ (i : Fin (w'.st Z').toD7.R.m) (la : HeightOneSpectrum (𝓞 core'.Q.c.F)), (R'.FW i).Pt la ≃ core'.PtM ((i : ℕ) + 1) la),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ la la', HEq la' la → ∀ y' y, HEq y' y →
              HEq (pt' i' la' y') (z.geo.fw.pt i la y)) →
          ∀ (i : Fin (w'.st Z').toD7.R.m) (la : HeightOneSpectrum (𝓞 core'.Q.c.F)) (y : (R'.FW i).Pt la) (f : core'.cuspA ((i : ℕ) + 1) (wtA (κ' i)) (κ' i).n),
            (R'.FW i).nrm la y (e' i f) = core'.nrmM ((i : ℕ) + 1) la (pt' i la y) (f : core'.R ((i : ℕ) + 1)) := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hc _ Xg tr R' hRS _ ι hι κ' hκ e' he pt' hpt i'
  letI := alg'
  letI := z.alg
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := (by with_unfolding_all exact ((congrArg (fun P : Pre => P.R.m) hPre) :))
  let i : Fin (w.st Z).toD7.R.m := ⟨i'.1, hm ▸ i'.2⟩
  have hi : (i : ℕ) = i' := rfl
  have hb : UpperTheory.LocalNormsMatchCuspForms z.core ((i : ℕ) + 1) (z.geo.κ i) (z.R.FW i).Pt (W := (z.R.FW i).WK) (z.R.FW i).nrm
      (fun φ => z.geo.fw.e i φ) (fun la y => z.geo.fw.pt i la y) := (by with_unfolding_all exact ((z.geo.fw.nrm_eq i) :))
  have hcl := ((hRS.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).2.2.2.2
  have hPt := hcl.1
  have hnrm := hcl.2
  have he1 := he i i' hi
  have hpt1 := hpt i i' hi
  obtain ⟨hP, hM, hnn⟩ := hκ i i' hi
  obtain ⟨c1, c2, c3, c4, c5, c6, -⟩ := hc
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  let H₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host (w'.st Z').toD7.host.E := (by with_unfolding_all exact (z.core.Q.H :))
  let l₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₁ := (by with_unfolding_all exact (z.core.Q.l :))
  let c₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₁ := (by with_unfolding_all exact (z.core.Q.c :))
  have hF : core'.Q.c.F = c₁.F := UpperTheory.coeff_field_eq_of_heq (H := H₁) (l := l₁) (c := c₁) ((by with_unfolding_all exact (c1 :))) ((by with_unfolding_all exact (c2 :))) ((by with_unfolding_all exact (c3 :)))
  let Q₀ : Formalism.L2.Pj.Par (w'.st Z').toD7 :=
    { H := H₁, l := l₁, c := c₁, Dw := (by with_unfolding_all exact (z.core.Q.Dw :)), Xo := (by with_unfolding_all exact (z.core.Q.Xo :)),
      eO := (UpperTheory.ringOfIntegersEquivOfEqSubfield hF).trans core'.Q.eO }
  let core₀ : Formalism.L2.Pj.CoreJ (w'.st Z').toD7 :=
    { toCore :=
        { Q := Q₀, U := (by with_unfolding_all exact (z.core.U :)), V := (by with_unfolding_all exact (z.core.V :)), dict := (by with_unfolding_all exact (z.core.dict :)), mu := (by with_unfolding_all exact (z.core.mu :)),
          Kf := (by with_unfolding_all exact (z.core.Kf :)), pb := (by with_unfolding_all exact (z.core.pb :)) }
      cE := (by with_unfolding_all exact (z.core.cE :)), chiW := (by with_unfolding_all exact (z.core.chiW :)), x₀ := (by with_unfolding_all exact (z.core.x₀ :)), iota := (by with_unfolding_all exact (z.core.iota :)) }
  let κ₀ : WeightFamilies.Wt (w'.st Z').toD7 ((i' : ℕ) + 1) :=
    { aP := (by with_unfolding_all exact ((z.geo.κ i).aP :)), aM := (by with_unfolding_all exact ((z.geo.κ i).aM :)), aPlus_antitone := (by with_unfolding_all exact ((z.geo.κ i).aPlus_antitone :)),
      aM_anti := (by with_unfolding_all exact ((z.geo.κ i).aM_anti :)), n := (z.geo.κ i).n, n_even := (z.geo.κ i).n_even }
  let Pt₀ : HeightOneSpectrum (𝓞 core₀.Q.c.F) → Type := (by with_unfolding_all exact ((z.R.FW i).Pt :))
  let nrm₀ : ∀ la, Pt₀ la → (z.R.FW i).WK → ℝ := (by with_unfolding_all exact ((z.R.FW i).nrm :))
  let e₀ : core₀.cuspA ((i' : ℕ) + 1) (wtA κ₀) κ₀.n → (z.R.FW i).WK := (by with_unfolding_all exact ((fun φ => z.geo.fw.e i φ) :))
  let pt₀ : ∀ la, Pt₀ la → core₀.PtM ((i' : ℕ) + 1) la := (by with_unfolding_all exact ((fun la y => z.geo.fw.pt i la y) :))
  exact (by with_unfolding_all exact ((UpperTheory.congr_of_heq core₀ core' ((c1)) ((c2)) ((c3)) ((c4)) ((c5)) ((c6))
    ((i' : ℕ) + 1) κ₀ (κ' i') ((hP)) ((hM)) ((hnn)) Pt₀ (R'.FW i').Pt ((hPt))
    (W := (z.R.FW i).WK) (W' := (R'.FW i').WK) (fun φ φ' => CrdOver ι φ.1 φ'.1) nrm₀ (R'.FW i').nrm ((hnrm))
    e₀ (fun φ => e' i' φ) ((he1)) pt₀ (fun la y => pt' i' la y) ((hpt1)) ((hb))) : _))
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo


private theorem ex_equiv_moved {m : ℕ} {L : Type} (P P' Q : Fin m → L → Type) (h : ∀ i, HEq (P' i) (P i))
    (e : ∀ i la, P i la ≃ Q i la) :
    ∃ e' : ∀ i la, P' i la ≃ Q i la, ∀ (i i' : Fin m), (i : ℕ) = i' → ∀ la la', HEq la' la → ∀ y' y, HEq y' y →
      HEq (e' i' la' y') (e i la y) := by
  obtain rfl : P' = P := funext fun i => eq_of_heq (h i)
  refine ⟨e, fun i i' hi la la' hla y' y hy => ?_⟩
  obtain rfl : i = i' := Fin.ext hi
  cases hla
  cases hy
  rfl

theorem UpperTheory.pointEquiv_family_transport_of_same_pre :
    ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
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
          ∃ (pt' : ∀ (i : Fin (w'.st Z').toD7.R.m) (la : HeightOneSpectrum (𝓞 core'.Q.c.F)), (R'.FW i).Pt la ≃ core'.PtM ((i : ℕ) + 1) la),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ la la', HEq la' la → ∀ y' y, HEq y' y →
              HEq (pt' i' la' y') (z.geo.fw.pt i la y)) := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hH hL Xg tr R' hR hmu ι hι
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hH
  obtain ⟨P'⟩ := B'
  dsimp only at hPre
  subst hPre
  obtain ⟨⟨⟨H, l, c, Dw, Xo, eO⟩, U, V, dict, mu, Kf, pb⟩, cE, chiW, x₀, iota⟩ := core'
  have e1 : H = z.core.Q.H := eq_of_heq h1; subst e1
  have e2 : l = z.core.Q.l := eq_of_heq h2; subst e2
  have e3 : c = z.core.Q.c := eq_of_heq h3; subst e3
  have e4 : Dw = z.core.Q.Dw := eq_of_heq h4; subst e4
  have e5 : Xo = z.core.Q.Xo := eq_of_heq h5; subst e5
  letI := z.alg
  exact (by with_unfolding_all exact (ex_equiv_moved (fun i => (z.R.FW i).Pt) (fun i => (R'.FW i).Pt) (fun i la => z.core.PtM ((i : ℕ) + 1) la)
    (fun i => ((hR.2.2.2.2.2.2.2.2.2.2.2.2.1 i i rfl).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).2.2.2.2.1) z.geo.fw.pt :))
end
