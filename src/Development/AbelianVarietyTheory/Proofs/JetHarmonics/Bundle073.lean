module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle018
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle064
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
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LinkLaw

variable {V : Type} [CommRing V]

theorem jetMap_coord {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' V) (hφ : ∀ i, φ i ∈ orig V κ') (j : κ) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk _ (MvPolynomial.X j)) = Ideal.Quotient.mk _ (φ j) := by
  show Ideal.Quotient.mk _ (MvPolynomial.aeval φ (MvPolynomial.X j)) = _
  rw [MvPolynomial.aeval_X]

theorem jetSubstP_coord {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (F : κ → MvPowerSeries κ' V) (j : κ)
    (h : MvPowerSeries.constantCoeff (F j) = 0) :
    jetSubstP m (fun p => psTrunc m (F p)) (Ideal.Quotient.mk _ (MvPolynomial.X j)) = JetSer.toJet m (F j) := by
  unfold jetSubstP
  rw [jetMap_coord]
  have h0 : MvPolynomial.constantCoeff (psTrunc m (F j)) = 0 := by
    rw [Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, MvPolynomial.constantCoeff_eq,
      MvPowerSeries.coeff_truncTotal _ (by simp), MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  rw [h0, map_zero, sub_zero]
  exact congrArg (Ideal.Quotient.mk _) (Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq m (F j))

def toAt (A : Type) [CommRing A] [Algebra V A] : Chart.sp (R₀ := V) A ⟶ overAt (𝟙 (Sp V)) A :=
  Over.homMk (𝟙 _) (by dsimp; simp)

theorem read_match {G : Over (Sp V)} {κ : Type} {N m : ℕ} (z : overAt (𝟙 (Sp V)) (Jet V κ m) ⟶ G)
    (x : Chart.sp (R₀ := V) (Chart.JetR V (Fin N) m) ⟶ G) (e : Chart.JetR V (Fin N) m ≃ₐ[V] Jet V κ m)
    (he : z.left = Geo.Tor.spMap (e : Chart.JetR V (Fin N) m →+* Jet V κ m) ≫ x.left)
    {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (S : Jet V κ m →ₐ[V] B) (Φ : B →ₐ[V] A) :
    (toAt A ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) Φ) ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) S ≫ z =
      Chart.spMap (Φ.comp (S.comp (e : Chart.JetR V (Fin N) m →ₐ[V] Jet V κ m))) ≫ x := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, he, Chart.spMap_left, toAt, Formalism.L2.Pj.homAt, Over.homMk_left, Category.id_comp,
    ← Category.assoc]
  congr 1
  simp only [Geo.Tor.spMap, ← Spec.map_comp]
  rfl

theorem constantCoeff_ev {k n d : ℕ} (a : Fin k → Pt V n d) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0)
    (f : PS V k d) (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 := by
  unfold ev
  have h1 : ∀ p : Fin k × Fin d, MvPowerSeries.constantCoeff ((fun p : Fin k × Fin d => a p.1 p.2) p) = 0 :=
    fun p => ha p.1 p.2
  have h2 : MvPowerSeries.HasSubst (fun p : Fin k × Fin d => a p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero h1
  exact MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin k × Fin d => a p.1 p.2) h2 h1 hf

theorem exists_subst {σ κ : Type} [Finite σ] [Finite κ] (c : σ → MvPowerSeries κ V)
    (hc : ∀ j, MvPowerSeries.constantCoeff (c j) = 0) (m : ℕ) :
    ∃ Φ : Jet V σ m →ₐ[V] Chart.JetR V κ m,
      (∀ j, Φ (Ideal.Quotient.mk _ (MvPolynomial.X j)) = JetSer.toJet m (c j)) ∧
      ∀ g : MvPowerSeries σ V, Φ (JetSer.toJet m g) = JetSer.toJet m (MvPowerSeries.subst c g) := by
  obtain ⟨⟨Φ, hΦ⟩, hsub⟩ := (JetSer.jetAlg V κ).2.2.2.2 σ c hc m
  exact ⟨Φ, hΦ, hsub Φ hΦ⟩

theorem isLawOf_of_match {G : Over (Sp V)} [GrpObj G] {d : ℕ} (F : Fin d → PS V 2 d)
    (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0) (xT : JetPts G (Fin 1 × Fin d))
    (law : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ xT m =
      (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m (0 : Fin 2)) ≫ xT m) *
        (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m (1 : Fin 2)) ≫ xT m))
    (x : JetSer.Fam G (Fin d)) (hM : Match (oneCol d) xT x) : JetSer.IsLawOf x F := by
  refine ⟨hF, fun n a b y z hy hz => ?_⟩
  have hab : ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → Pt V n d) i j) = 0 := by
    intro i j
    fin_cases i
    · exact hy.1 j
    · exact hz.1 j
  refine ⟨fun j => constantCoeff_ev _ hab _ (hF j), fun m => ?_⟩
  obtain ⟨e, he1, he2⟩ := hM m
  obtain ⟨ψa, ha1, ha2⟩ := hy.2 m
  obtain ⟨ψb, hb1, hb2⟩ := hz.2 m
  obtain ⟨Φ, hΦ, hsub⟩ := exists_subst
    (fun p : Fin 2 × Fin d => (![a, b] : Fin 2 → Pt V n d) p.1 p.2) (fun p => hab p.1 p.2) m
  have key : ∀ i : Fin 2, ∀ j, (Φ.comp ((jetCopy d m i).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m))) (Chart.zR m j) =
      JetSer.toJet m ((![a, b] : Fin 2 → Pt V n d) i j) := by
    intro i j
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1, jetCopy, jetMap_coord]
    exact hΦ (i, j)
  have ea : ψa = Φ.comp ((jetCopy d m 0).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)) :=
    Chart.jet_ext fun j => (ha1 j).trans (key 0 j).symm
  have eb : ψb = Φ.comp ((jetCopy d m 1).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)) :=
    Chart.jet_ext fun j => (hb1 j).trans (key 1 j).symm
  refine ⟨Φ.comp ((jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)).comp
    (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)), fun j => ?_, ?_⟩
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1,
      jetSubstP_coord m (fun p : Fin 1 × Fin d => F p.2) _ (hF _)]
    exact hsub _
  · show y m * z m = _
    rw [← read_match (xT m) (x m) e he2, law m, MonObj.comp_mul,
      read_match (xT m) (x m) e he2, read_match (xT m) (x m) e he2, ← ea, ← eb, ← ha2, ← hb2]

theorem isMapOf_of_match {G : Over (Sp V)} {d : ℕ} (φ : Pt V 1 d)
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (xT : JetPts G (Fin 1 × Fin d)) (f : G ⟶ G)
    (hf : ∀ m, xT m ≫ f =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)) ≫ xT m)
    (x : JetSer.Fam G (Fin d)) (hM : Match (oneCol d) xT x) : JetSer.IsMapOf x x f φ := by
  refine ⟨hφ, fun n a y hy => ?_⟩
  have hab : ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![a] : Fin 1 → Pt V n d) i j) = 0 := by
    intro i j
    fin_cases i
    exact hy.1 j
  refine ⟨fun j => constantCoeff_ev _ hab _ (hφ j), fun m => ?_⟩
  obtain ⟨e, he1, he2⟩ := hM m
  obtain ⟨ψa, ha1, ha2⟩ := hy.2 m
  obtain ⟨Φ, hΦ, hsub⟩ := exists_subst
    (fun p : Fin 1 × Fin d => (![a] : Fin 1 → Pt V n d) p.1 p.2) (fun p => hab p.1 p.2) m
  have key : ∀ j, (Φ.comp ((AlgHom.id V _).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m))) (Chart.zR m j) = JetSer.toJet m (a j) := by
    intro j
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1, AlgHom.id_apply]
    exact hΦ (0, j)
  have ea : ψa = Φ.comp ((AlgHom.id V _).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)) :=
    Chart.jet_ext fun j => (ha1 j).trans (key j).symm
  have hid : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (AlgHom.id V (Jet V (Fin 1 × Fin d) m)) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  refine ⟨Φ.comp ((jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)).comp
    (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)), fun j => ?_, ?_⟩
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1,
      jetSubstP_coord m (fun p : Fin 1 × Fin d => φ p.2) _ (hφ _)]
    exact hsub _
  · show y m ≫ f = _
    rw [← read_match (xT m) (x m) e he2, ← hf m, ha2, ea, ← read_match (xT m) (x m) e he2, hid,
      Category.id_comp]
    simp only [Category.assoc]

theorem linkLaw : LinkLawSt := by
  intro E _ _ _ H V _ t d BT tg xT eT wPT hC _ _ x _ hM
  letI := H.starRing
  exact ⟨isLawOf_of_match BT.G.F BT.G.const xT hC.law x hM,
    fun α => isMapOf_of_match (BT.A.act α) (BT.A.const α) xT _ (fun m => hC.act m α) x hM⟩

end GlobalTheory.LinkLaw
end
end

section

noncomputable section

namespace GlobalTheory.UnivJetBaseChange

section General
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.ChartBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback)
attribute [local instance] Over.cartesianMonoidalCategory

variable {R R' : Type} [CommRing R] [CommRing R']

def IsUnivSp (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (κ : Type)
    (x : ∀ m : ℕ, sp (R₀ := R) (JetR R κ m) ⟶ G) : Prop :=
  (∀ m, spMap (jetTruncR R κ m) ≫ x (m + 1) = x m) ∧ (∀ m, spMap (jetAug R κ m) ≫ x m = 1) ∧
  ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), RingHom.ker aug ^ (m + 1) = ⊥ →
    ∀ y : sp (R₀ := R) A ⟶ G, spMap aug ≫ y = 1 →
      ∃! ψ : JetR R κ m →ₐ[R] A, aug.comp ψ = jetAug R κ m ∧ y = spMap ψ ≫ x m

variable [Algebra R R'] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)

theorem isUnivSp_baseChange [IsLocalRing R] {κ : Type} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R κ m) ⟶ G}
    (hx : IsUnivSp G κ x) {x' : ∀ m : ℕ, sp (R₀ := R') (JetR R' κ m) ⟶ G'}
    (hx' : ∀ m, push hπ (x' m) = spMap (jetCoeff R R' κ m) ≫ x m) :
    IsUnivSp G' κ x' := by
  refine ⟨fun m => push_injective hπ ?_, fun m => push_injective hπ ?_, ?_⟩
  · rw [push_spMap, hx', hx', ← hx.1 m, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp]
    congr 2
    refine jet_ext fun j => ?_
    show jetTruncR R' _ m (jetCoeff R R' _ _ (zR _ j)) = jetCoeff R R' _ _ (zR _ j)
    rw [jetCoeff_zR, jetCoeff_zR]
    rfl
  · rw [push_spMap, hx', push_one, ← Category.assoc, spMap_comp]
    have : ((jetAug R' κ m).restrictScalars R).comp (jetCoeff R R' κ m) =
        (Algebra.ofId R R').comp (jetAug R κ m) := by
      refine jet_ext fun j => ?_
      show jetAug R' _ m (jetCoeff R R' _ _ (zR _ j)) = algebraMap R R' (jetAug R _ m (zR m j))
      rw [jetCoeff_zR, jetAug_zR, jetAug_zR, map_zero]
    rw [this, ← spMap_comp, Category.assoc, hx.2.1, MonObj.comp_one]
  intro A _ _ aug m hJ y hy
  letI : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨C⟩ := exists_chart G
  let q : A →ₐ[R] R' := aug.restrictScalars R
  have hq : Function.Surjective q := fun r => ⟨algebraMap R' A r, aug.commutes r⟩
  have hJq : (RingHom.ker q) ^ (m + 1) = ⊥ := hJ
  obtain ⟨h, hh, hqh⟩ := exists_pt_of_aug C q hq hJq (push hπ y) (by
    rw [← push_spMap, hy, push_one])
  obtain ⟨k, hk, hqk⟩ := exists_pt_of_aug C (jetAug R κ m) (fun r => ⟨algebraMap _ _ r, AlgHom.commutes _ r⟩)
    (ker_jetAug_pow _ m) (x m) (hx.2.1 m)
  let h₀ := fibLift q (eps C) h hqh
  obtain ⟨ψ₀, ⟨ha, hψ₀⟩, hu⟩ := hx.2.2 (fib q) (fibFst q) m (fib_ker q hJq) (ReciprocityTheory.ChartRestriction.G.Chart.pt C h₀) (by
    rw [spMap_pt]
    exact pt_eps_self C)
  have hb : ∀ j, fibSnd q (ψ₀ (zR m j)) ∈ RingHom.ker aug := fun j => by
    show q _ = 0
    rw [fib_cond, show fibFst q (ψ₀ (zR m j)) = 0 from (AlgHom.congr_fun ha _).trans (jetAug_zR m j), map_zero]
  refine ⟨jetLift R' (RingHom.ker aug) hJ _ hb, ⟨jet_ext fun j => ?_, push_injective hπ ?_⟩, ?_⟩
  · rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]
    exact hb j
  · have : ((jetLift R' (RingHom.ker aug) hJ _ hb).restrictScalars R).comp (jetCoeff R R' κ m) =
        (fibSnd q).comp ψ₀ := by
      refine jet_ext fun j => ?_
      show jetLift R' (RingHom.ker aug) hJ _ hb (jetCoeff R R' _ _ (zR _ j)) = _
      rw [jetCoeff_zR, jetLift_zR]
      rfl
    rw [push_spMap, hx', ← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, ← hψ₀, spMap_pt, hh]
    rfl
  · rintro ψ ⟨hψa, hψ⟩
    let v := (ψ.restrictScalars R).comp (jetCoeff R R' κ m)
    have hv : q.comp v = (Algebra.ofId R R').comp (jetAug R κ m) := by
      refine jet_ext fun j => ?_
      show aug.comp ψ (jetCoeff R R' _ _ (zR _ j)) = algebraMap R R' (jetAug R _ m (zR m j))
      rw [jetCoeff_zR, hψa, jetAug_zR, jetAug_zR, map_zero]
    have hvk : h = v.comp k := by
      apply pt_injective C
      rw [← hh, hψ, push_spMap, hx', ← Category.assoc, spMap_comp, hk, spMap_pt]
    have e := hu (fibLift q (jetAug R κ m) v hv) ⟨rfl, by
      rw [hk, spMap_pt]
      congr 1
      refine AlgHom.ext fun s => Subtype.ext (Prod.ext ?_ ?_)
      · exact (AlgHom.congr_fun hqk s).symm
      · exact AlgHom.congr_fun hvk s⟩
    refine jet_ext fun j => ?_
    rw [jetLift_zR, ← e]
    show _ = ψ (jetCoeff R R' _ _ (zR _ j))
    rw [jetCoeff_zR]

end General

section Convert
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

variable {V : Type} [CommRing V] {G : Over (Sp V)} {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B]

def toSp (y : overAt (𝟙 (Sp V)) A ⟶ G) : Chart.sp (R₀ := V) A ⟶ G :=
  Over.homMk y.left ((Over.w y).trans (Category.comp_id _))

def ofSp (y : Chart.sp (R₀ := V) A ⟶ G) : overAt (𝟙 (Sp V)) A ⟶ G :=
  Over.homMk y.left ((Over.w y).trans (Category.comp_id _).symm)

theorem toSp_inj {y y' : overAt (𝟙 (Sp V)) A ⟶ G} : toSp y = toSp y' ↔ y = y' :=
  ⟨fun h => Over.OverMorphism.ext (congrArg (fun k => k.left) h), fun h => h ▸ rfl⟩

theorem toSp_one [GrpObj G] : toSp (1 : overAt (𝟙 (Sp V)) A ⟶ G) = 1 := by
  have : toSp (1 : overAt (𝟙 (Sp V)) A ⟶ G) =
      (Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.comp_id _)) :
        Chart.sp (R₀ := V) A ⟶ overAt (𝟙 (Sp V)) A) ≫ (1 : overAt (𝟙 (Sp V)) A ⟶ G) :=
    Over.OverMorphism.ext (Category.id_comp _).symm
  rw [this, MonObj.comp_one]

theorem isUnivJ_iff [GrpObj G] {κ : Type} (z : GlobalTheory.PowGerm.JetPts G κ) :
    GlobalTheory.PowGerm.IsUnivJ G κ z ↔ IsUnivSp G κ (fun m => toSp (z m)) := by
  refine and_congr (forall_congr' fun m => ?_) (and_congr (forall_congr' fun m => ?_) ?_)
  · rw [← toSp_inj]
    exact Iff.rfl
  · rw [← toSp_inj, toSp_one]
    exact Iff.rfl
  · constructor
    · intro H A _ _ aug m hJ y hy
      have := H A aug m hJ (ofSp y) (by rw [← toSp_inj, toSp_one]; exact hy)
      simp only [← toSp_inj] at this
      exact this
    · intro H A _ _ aug m hJ y hy
      have := H A aug m hJ (toSp y) (by rw [← toSp_inj, toSp_one] at hy; exact hy)
      simp only [← toSp_inj]
      exact this

end Convert

end GlobalTheory.UnivJetBaseChange

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem GlobalTheory.UnivJetBaseChange.exists_univ_pullback : ∀ (V V' : Type) [CommRing V] [IsLocalRing V] [CommRing V'] (φ : V →+* V') (G : Over (Sp V)) [GrpObj G] (G' : Over (Sp V')) [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G (spMap φ) F → ∀ (κ : Type) (z : GlobalTheory.PowGerm.JetPts G κ), GlobalTheory.PowGerm.IsUnivJ G κ z → ∃ z' : GlobalTheory.PowGerm.JetPts G' κ, GlobalTheory.PowGerm.IsUnivJ G' κ z' ∧ ∀ m, (z' m).left ≫ F = spMap (jetCoef φ κ m) ≫ (z m).left := by
  intro V V' _ _ _ φ G _ G' _ F hF κ z hz
  letI : Algebra V V' := φ.toAlgebra
  have hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap V V'))) F := hF
  choose x' hx' using fun m => GlobalTheory.ChartBaseChange.push_surjective hπ
    (Chart.spMap (GlobalTheory.ChartBaseChange.jetCoeff V V' κ m) ≫ GlobalTheory.UnivJetBaseChange.toSp (z m))
  refine ⟨fun m => GlobalTheory.UnivJetBaseChange.ofSp (x' m), (GlobalTheory.UnivJetBaseChange.isUnivJ_iff _).2
    (GlobalTheory.UnivJetBaseChange.isUnivSp_baseChange hπ ((GlobalTheory.UnivJetBaseChange.isUnivJ_iff z).1 hz) hx'), fun m => ?_⟩
  have e : (GlobalTheory.ChartBaseChange.jetCoeff V V' κ m).toRingHom = jetCoef φ κ m :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun p => GlobalTheory.ChartBaseChange.jetCoeff_mk m p)
  rw [← e]
  exact congrArg (fun k => k.left) (hx' m)
end
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem exists_frames_eL {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
    (t : SAB H (Sp V)) (L' : LB t.G.left) (h : t.PP.L = L')
    (d : ℕ) (FT : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (ph1 ph2 : PS V 3 d) (sy : PS V 2 d) (ad : 𝓞 E → PS V 2 d)
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (uv : Fin d → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
    (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (wP : PrimTyG t)
    (hch : IsChartG t (𝟙 (Sp V)) d FT act tg uv x) (hfr : IsFrameG t (𝟙 (Sp V)) d x FT act ph1 ph2 sy ad e)
    (hpr : IsPrimG t wP) :
    ∃ τ : Frames L' (κ := Fin 1 × Fin d) x, τ.Gen ∧
      (∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → L'.ι), Good L' y J →
        val (τ m) (𝟙 _) y J = val (genCast h _ _ (eLG t (𝟙 (Sp V)) d x act e wP m)) (𝟙 _) y J) ∧
      (FrTrunc t (𝟙 (Sp V)) d x e → τ.Trunc) := by
  subst h
  have hL := t.PP.isLB
  have heL : ∀ m, (eLG t (𝟙 (Sp V)) d x act e wP m).IsGen := fun m =>
    ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen t.PP.L _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ hpr.1 _)
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ (hfr.gen m) _)
  have hτ : ∀ m, ∃ τ : LB.Gen (LB.LinComb t.PP.L (Y := (jOG (𝟙 (Sp V)) d m 1).left) (K := Fin 1) (fun _ => (x m).left)
      fun _ => (1 : ℤ)), τ.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG (𝟙 (Sp V)) d m 1).left) (z : Z)
        (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
          val τ r z J = val (eLG t (𝟙 (Sp V)) d x act e wP m) r z J := by
    intro m
    refine exists_gen hL ?_ _ (heL m)
    intro U _ hU
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id,
      GermD.formEq_eL hch m]
    rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
    simp only [← zpow_add, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  choose τ hτg hτv using hτ
  refine ⟨τ, hτg, fun m y J hJ => hτv m _ (𝟙 _) y J hJ, fun htr m y J hJ => ?_⟩
  exact (hτv (m + 1) _ (GermD.ρT (𝟙 (Sp V)) d m).left y J hJ).trans
    ((GermD.val_eL_trunc hch e wP htr m y J hJ).trans (hτv m _ (𝟙 _) y J hJ).symm)

theorem frame1St_holds : Frame1St := by
  intro E _ _ _ H V _ _ _ _ t P d FT act ph1 ph2 sy ad tg xT eT wPT hch hfr hpr
  exact exists_frames_eL t P.U.LG.L (congrArg RigLB.L P.bundle).symm d FT act ph1 ph2 sy ad tg _ xT eT wPT hch hfr hpr

end GlobalTheory.PowGerm
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SupMeas

theorem isDS_continuousOn {k r : ℕ} {R : Rep k r} {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    (h : R.IsDS ε μ) (v : R.H) : ContinuousOn (fun g => R.σ g v) (GG k r) := by
  obtain ⟨-, P, hP, -, -, ⟨-, -, hc⟩, -⟩ := h
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hmaps := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.cayley_maps hP
  have e : ∀ g : Mx k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have h3 : Continuous fun g : Mx k r => P * g * P⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have := (hc v).comp h3.continuousOn hmaps
  simpa only [Function.comp_def, e] using this

theorem isCoef_continuousOn {k r : ℕ} {R : Rep k r} {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    {l : R.H → Wp} {l' : R.H → Wq} {F : Mx k r → (Wq →L[ℂ] Wp)} {s : ℂ}
    (h : R.IsDS ε μ) (hF : IsCoef R l l' F s) : ContinuousOn F (GG k r) := by
  obtain ⟨m, x, y, X, -, hF, -⟩ := hF
  refine ContinuousOn.congr ?_ hF
  exact continuousOn_finsetSum _ fun i _ =>
    (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (isDS_continuousOn h (y i))).smul continuousOn_const

end GlobalTheory.SupMeas
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselLine

theorem psi_const : PsiConst := by
  intro k r z c g
  unfold Formalism.QuantumDeterminants.psi Formalism.QuantumDeterminants.ell PI.BesselMapUniq.psiGen PI.BesselMapUniq.ellA
  rw [Finset.mul_sum]

theorem bessel_line : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l l₁ : R.H → Wp), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → NzOn R l → IsBes R z π l₁ → ∃ c : ℂ, ∀ v ∈ R.sm, l₁ v = c • l v := by
  intro hH k r ε mu R Wp _ _ _ _ z π u μW μN μG νq l l₁ hDS hS hl hnz hl₁
  obtain ⟨w, hw, hne⟩ := hnz
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -⟩ := hS
  have hc : Formalism.QuantumDeterminants.cStd ≠ 0 := by
    unfold Formalism.QuantumDeterminants.cStd
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  exact Formalism.FourierDecayAlt.P.DDSmoothness.jsz_line hH.1.2.2.2 psi_const hDS.1 hDS.2 hz hT hc hπ hl hl₁ hw hne

end GlobalTheory.BesselLine
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.tensor_bessel_transfer : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (om : ι → ℂ) (l : R.H → Wp) (lI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → TensRaw ρ R RI io pr → (∀ v ∈ R.sm, ∀ w ∈ R.sm, l (v + w) = l v + l w) → (∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v) → (∀ I, ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = β I • lI I y) → ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a) om • l (R.σ g w) = ∑ I, β I • lI I ((RI I).σ g (∑ c, pr I c (tm R a w c))) := by
  first | exact @GlobalTheory.herm_smul_eq_sum_of_tensRaw | exact GlobalTheory.herm_smul_eq_sum_of_tensRaw | (intros; apply GlobalTheory.herm_smul_eq_sum_of_tensRaw <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exists_lie_unitary_element_simple_root : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∀ g ∈ GG k r, ∀ a : Fin r, ∃ X : Mx k r, PI.UpqRep.InLieHpk k r X ∧ (∑ i, ∑ j, ‖X i j‖ ^ 2 ≤ 4 * lenA k r z g a.castSucc ^ 2) ∧ ∀ t : ℝ, ∃ m ∈ Formalism.QuantumDeterminants.Nset k r, g * NormedSpace.exp ((t : ℂ) • X) = m * g ∧ Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m = Complex.exp (-(2 * (lenA k r z g a.succ : ℂ) * (t : ℂ)) * Complex.I) := by
  first | exact @GlobalTheory.UnipotentElement.exists_element | exact GlobalTheory.UnipotentElement.exists_element | (intros; apply GlobalTheory.UnipotentElement.exists_element <;> assumption)
end
