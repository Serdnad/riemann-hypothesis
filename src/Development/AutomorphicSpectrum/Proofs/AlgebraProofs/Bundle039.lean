module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.CharacterDataBaseChange
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle033
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle034
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle021
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle019
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle035
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle024
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CbFrob
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
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff

@[expose] public section

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem lattice_base_change_larger_ring : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → CharData RC p (algebraMap Ω C w) (fun τ a => algebraMap Ω C (χ τ a)) ∧ (D.bc RC).Base RC p (algebraMap Ω C w) :=
  @PositivityTheory.Xgn.character_data_base_change

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.QuotEquivIso

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N N₁ : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E E' : ChartBundle O (mseg x) N V) (F F' : ChartBundle O (mseg x) N₁ V₁), QuotEquiv O x E.lat E'.lat F.lat F'.lat ↔ QuotIso O x E E' F F' := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N N₁ V _ _ V₁ _ _ E E' F F'
  unfold GlobalTheory.CompanionTheory.Ar.Num.QuotEquiv GlobalTheory.CompanionTheory.Ar.Num.IsQuotHom
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.QuotIso
  constructor
  · rintro ⟨Γ, ⟨hlat, hΓ⟩, hΓ'⟩
    have hloc : ∀ s, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x s ≠ 0 →
        GlobalTheory.CompanionTheory.Ar.Num.LocFree
          (ReciprocityTheory.ChartRestriction.G.Geo.chartRing O (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) s)
          (N + N₁) (Γ s) := by
      intro s hs
      obtain ⟨h1, h2, h3, _⟩ := hΓ s hs
      obtain ⟨_, h6⟩ := hΓ' s hs
      exact (GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel.main _ N N₁ (E.lat s) (F.lat s) (F'.lat s) (Γ s)
        (((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N V).2 E).2 s hs)
        (((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N₁ V₁).2 F).2 s hs)
        (((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N₁ V₁).2 F').2 s hs)
        (hlat.1 s hs) h1 h2 h3 h6).1
    obtain ⟨Pb, hPb⟩ := (GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x (N + N₁) (V × V₁)).1 Γ hlat hloc
    refine ⟨Pb, fun s hs => ?_⟩
    rw [hPb s hs]
    obtain ⟨h1, h2, h3, h4⟩ := hΓ s hs
    obtain ⟨h5, h6⟩ := hΓ' s hs
    exact ⟨fun v => ⟨h5 v, h4 v⟩, fun v => ⟨fun h => Exists.elim h fun w hw => (h1 v w hw).1, h2 v⟩, h3,
      fun w => ⟨fun h => Exists.elim h fun v hv => (h1 v w hv).2, h6 w⟩⟩
  · rintro ⟨Pb, hPb⟩
    refine ⟨Pb.lat, ⟨((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x _ _).2 Pb).1, fun s hs => ?_⟩,
      fun s hs => ?_⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hPb s hs
      exact ⟨fun v w hvw => ⟨(h2 v).1 ⟨w, hvw⟩, (h4 w).1 ⟨v, hvw⟩⟩, fun v hv => (h2 v).2 hv, h3,
        fun v hv => (h1 v).2 hv⟩
    · obtain ⟨h1, -, -, h4⟩ := hPb s hs
      exact ⟨fun v hv => (h1 v).1 hv, fun w hw => (h4 w).2 hw⟩

end GlobalTheory.CompanionTheory.Ar.Num.QuotEquivIso
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.chart_bundle_base_extension_unique : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → (LatLE O x E E' → LatLE O (joinCoord x z) EB E'B) ∧ (SameGeneric O x E E' → SameGeneric O (joinCoord x z) EB E'B) ∧ (∀ c : Ω, IsScaled x c E.lat E'.lat → IsScaled (joinCoord x z) c EB.lat E'B.lat) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve | exact GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.chart_bundle_product : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), (∀ (N N₁ : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N₁ V₁), ∃ P : ChartBundle O (mseg x) (N + N₁) (V × V₁), ∀ s, mseg x s ≠ 0 → P.lat s = (E.lat s).prod (F.lat s)) ∧ (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V) (c : Ω), c ≠ 0 → ∃ E' : ChartBundle O (mseg x) N V, IsScaled x c E.lat E'.lat) ∧ (∀ (u : Ω) (a : K → ℤ), u ≠ 0 → ∃ A : ChartBundle O (mseg x) 1 Ω, IsLine O x u a A.lat) ∧ (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (t : Module.Basis (Fin N) Ω V), ∃ T : ChartBundle O (mseg x) N V, ∀ s, mseg x s ≠ 0 → ∀ v, v ∈ T.lat s ↔ ∀ i, t.repr v i ∈ chartRing O (mseg x) s) ∧ (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω), Function.Bijective β.flip → ∃ F : ChartBundle O (mseg x) N V₁, IsDualLat O x β E.lat F.lat) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BundleOps.main | exact GlobalTheory.CompanionTheory.Ar.BundleOps.main | (intros; apply GlobalTheory.CompanionTheory.Ar.BundleOps.main <;> assumption)
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.chart_bundle_extension_comparison : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N₀ N N₂ : ℕ) (V₀ : Type) [AddCommGroup V₀] [Module Ω V₀] (V : Type) [AddCommGroup V] [Module Ω V] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (A A' : (∀ k, ι k) → AddSubgroup V₀) (E E' : ChartBundle O (mseg x) N V) (C C' : ChartBundle O (mseg x) N₂ V₂), QuotExact O x A A' E.lat E'.lat C.lat C'.lat → ∃ E'' : ChartBundle O (mseg x) N V, LatLE O x E' E'' ∧ LatLE O x E'' E ∧ QuotEquiv O x A A' E''.lat E'.lat ∧ QuotEquiv O x E.lat E''.lat C.lat C'.lat := by
  exact @GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle.main
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

open Coalgebra Bialgebra PositivityTheory.HtPt.Gi PositivityTheory.HtPt.Twpdiv in
theorem tower_end_pdiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ), (∀ (φ : La →+ La) (dφ : L →ₗ[O] L), X.Acts φ dφ → ∃ f : G ⟶ G, (∀ a, tateMap G G O f (τ a) = τ (φ a)) ∧ ∀ n (g : G.A n) (a : La), (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) ∧ ∀ (H : PDivGroup p O) (f f' : G ⟶ H), (∀ a, tateMap G H O f (τ a) = tateMap G H O f' (τ a)) → f = f' := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ La _ _ _ L _ _ X G e τ hre
  let ev (n : ℕ) (t : LevGrp La p n) : G.A n →ₐ[O] O :=
    (evalAt (X.A n) t).comp (e n).toAlgHom
  have ev_apply (n : ℕ) (t : LevGrp La p n) (g : G.A n) : ev n t g = (e n g).1 t := rfl
  have sep (n : ℕ) : Sep (ev n) := fun _ _ h => (e n).injective (Subtype.ext (funext h))
  have ev_lev (n : ℕ) (a : La) : ev n (lev p n a) = (τ a).pt n :=
    AlgHom.ext fun g => (hre.pt a n g).symm
  refine ⟨?_, ?_⟩
  · intro φ dφ h
    have exists_pullback (n : ℕ) (g : G.A n) :
        ∃ g' : G.A n, ∀ t, ev n t g' = ev n (levMap p n φ t) g := by
      refine ⟨(e n).symm ⟨fun t => (e n g).1 (levMap p n φ t), ?_⟩, ?_⟩
      · exact (h n (e n g).1 _ fun _ => rfl).1 (e n g).2
      · intro t
        rw [ev_apply, AlgEquiv.apply_symm_apply]
        rfl
    let pull (n : ℕ) : G.A n →ₐ[O] G.A n :=
      Ord.liftTo (ev n) (sep n) (fun t => ev n (levMap p n φ t)) (exists_pullback n)
    have comp_pull (n : ℕ) (t : LevGrp La p n) :
        (ev n t).comp (pull n) = ev n (levMap p n φ t) := Ord.ev_liftTo _ _ _ _ t
    have ev_pull (n : ℕ) (t : LevGrp La p n) (g : G.A n) :
        ev n t (pull n g) = ev n (levMap p n φ t) g := DFunLike.congr_fun (comp_pull n t) g
    have ev_one (n : ℕ) (g : G.A n) : ev n 1 g = counit (R := O) g := by
      rw [← lev_zero, ev_lev, map_zero]
      rfl
    have ev_mul (n : ℕ) (s t : LevGrp La p n) (g : G.A n) :
        pair (ev n s) (ev n t) (comul (R := O) g) = ev n (s * t) g := by
      obtain ⟨a, rfl⟩ := lev_surjective p n s
      obtain ⟨b, rfl⟩ := lev_surjective p n t
      rw [← lev_add, ev_lev, ev_lev, ev_lev, map_add (f := τ)]
      exact (AlgHom.convMul_apply ((τ a).conv n) ((τ b).conv n) g).symm
    let app (n : ℕ) : G.A n →ₐc[O] G.A n :=
      BialgHom.ofAlgHom (pull n)
        (AlgHom.ext fun g => by
          change counit (R := O) (pull n g) = counit (R := O) g
          rw [← ev_one, ← ev_one, ev_pull, map_one])
        (AlgHom.ext fun g => (sep n).pair (sep n) _ _ fun z => by
          change pair (ev n z.1) (ev n z.2)
              (Algebra.TensorProduct.map (pull n) (pull n) (comul (R := O) g)) =
            pair (ev n z.1) (ev n z.2) (comul (R := O) (pull n g))
          rw [pair_map, comp_pull, comp_pull, ev_mul, ev_mul, ev_pull, map_mul])
    let f : G ⟶ G := {
      app := app
      comm n := BialgHom.ext fun g => sep n _ _ fun t => by
        obtain ⟨a, rfl⟩ := lev_surjective p n t
        change (e n (G.res n (pull (n + 1) g))).1 _ = ev n _ (pull n (G.res n g))
        rw [hre.res, ← ev_apply, ev_pull, levMap_lev, ev_apply, ev_pull, levMap_lev,
          ev_apply, hre.res, map_nsmul] }
    have app_eval (n : ℕ) (g : G.A n) (a : La) :
        (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a)) :=
      ev_pull n (lev p n a) g
    refine ⟨f, fun a => TateOver.ext (funext fun n => AlgHom.ext fun g => ?_), app_eval⟩
    rw [tateMap_pt, hre.pt, hre.pt, app_eval]
  · intro H f f' hf
    refine PDivGroup.Hom.ext (funext fun n => BialgHom.ext fun g => sep n _ _ fun t => ?_)
    obtain ⟨a, rfl⟩ := lev_surjective p n t
    rw [ev_lev, ← tateMap_pt, ← tateMap_pt, hf]

end GlobalTheory.CompanionTheory.Ar.HT
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.formal_bilinear_term_product : ∀ (R : Type) [CommRing R] (d : ℕ) (f g : PS R 2 d) (φ ψ : Pt R 1 d), AxOne f → AxOne g → (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → AxOne (f * g) ∧ (∀ m, bil (f * g) m 1 = bil f m 1 + bil g m 1) ∧ (∀ n, bil (f * g) 1 n = bil f 1 n + bil g 1 n) ∧ AxOne (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) ∧ bil (ev (n := 2) ![comp1 φ (pt R d 0), comp1 ψ (pt R d 1)] f) 1 1 = (lin φ 1).transpose * bil f 1 1 * lin ψ 1 ∧ (∀ m n, bil (ev (n := 2) ![pt R d 1, pt R d 0] f) m n = (bil f n m).transpose) ∧ ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → bil (ev (n := 2) ![ptPow R d m 0, ptPow R d n 1] f) m n = bil f 1 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.BilCalc.bil_calc | exact GlobalTheory.CompanionTheory.Ar.Conj.BilCalc.bil_calc | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.BilCalc.bil_calc <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.formal_module_action_laws : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), B.A.act 0 = 0 ∧ (∀ n : ℕ, B.A.act ((n + 1 : ℕ) : O) = B.G.add (B.A.act (n : O)) (pt R d 0)) ∧ (∀ a b, comp1 (B.A.act a) (B.A.act b) = comp1 (B.A.act b) (B.A.act a)) ∧ ∀ n, AxOne (pow1 B n) ∧ AxOne (pow2 B n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.NatAct.act_nat_iterated | exact GlobalTheory.CompanionTheory.Ar.Conj.NatAct.act_nat_iterated | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.NatAct.act_nat_iterated <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem iso_pow_one_law : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d) (n : ℕ), IsIso B B₂ φ ψ lam → pow1 B₂ n * ev (n := 2) ![comp1 (B₂.A.act (n : O)) (pt R d 0), pt R d 1] lam = lam ^ n * ev (n := 2) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1)] (pow1 B n) :=
  @PositivityTheory.HtPt.Cc.iso_first_power

end GlobalTheory.CompanionTheory.Ar.Conj
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem pow_interchange : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (m n : ℕ), pow2 B n ^ m * ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] (pow1 B m) = pow1 B m ^ n * ev (n := 2) ![comp1 (B.A.act (m : O)) (pt R d 0), pt R d 1] (pow2 B n) :=
  PositivityTheory.HtPt.Cc.pow_inter

end GlobalTheory.CompanionTheory.Ar.Conj
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem pow_sy_exchange : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (n : ℕ), pow2 B n * B.sy ^ n = ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] B.sy * ev (n := 2) ![pt R d 1, pt R d 0] (pow1 B n) :=
  @PositivityTheory.HtPt.Cc.pow_sy

end GlobalTheory.CompanionTheory.Ar.Conj
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem mulp_factors_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ V : Pt R 1 d, (∀ i, constantCoeff (V i) = 0) ∧ B.A.act (p : O) = comp1 V (ptPow R d p 0) ∧ lin V 1 = hw B p :=
  @PositivityTheory.HtPt.Cb.mulp_V

end GlobalTheory.CompanionTheory.Ar.Conj
end
