module

import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle022
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle095
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle020
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle107
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SameGenericPointCharts
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab

theorem exists_labelEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (t : CMType H ⊕ CMType H), ∃ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) ∧ (∀ a : 𝓞 E, (σ.comp (HT.cmConj E).toRingHom) (a : E) = 𝔐.emb t.swap a) ∧ ∀ σ' : E →+* Ω, (∀ a : 𝓞 E, σ' (a : E) = 𝔐.emb t a) → σ' = σ := by
  apply PositivityTheory.Xgn.exists_cm_type_embedding <;> assumption

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem rt0_conj_neg_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  apply Formalism.MainNotions.ModuliIntegralCharts.H1.rt0_conj_neg_ne_zero <;> assumption

theorem rt0_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have hsq := H.sqrt_neg_disc_sq
  rw [h] at hsq
  have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  simp at hsq
  exact H.d_prime.ne_zero hsq

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpChart

open GlobalTheory.HolHom

variable {R : Type} [CommRing R]

def cst {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem valR_cst {C : Type} [CommRing C] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (θ : R →+* C)
    (y : Sp C ⟶ X) (hy : y ≫ p = spMap θ) (h : ⊤ ≤ y ⁻¹ᵁ U) (a : R) : evalHom y U h (cst p U a) = θ a := by
  have e := GlobalTheory.TangentOrigin.evalPt_constFn p y U h a
  have e2 := GlobalTheory.TangentOrigin.evalPt_spMap θ a
  rw [hy] at e
  exact e.trans e2

theorem exists_pt {G : Over (Sp R)} {V : G.left.Opens} (hV : IsAffineOpen V) (θ : R →+* ℂ)
    (χ : Γ(G.left, V) →+* ℂ) (hχ : ∀ r, χ (cst G.hom V r) = θ r) :
    ∃ x : Over.mk (spMap θ) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V ∧ ∀ a, valAt' x.left V a = χ a := by
  obtain ⟨y, hy, he⟩ := GlobalTheory.TangentOrigin.exists_evalPt_eq hV χ
  have hy' : y ≫ G.hom = spMap θ := GlobalTheory.TangentOrigin.eq_spMap_of_evalPt _ θ (fun a => by
    rw [← GlobalTheory.TangentOrigin.evalPt_constFn G.hom y V hy a, he]; exact hχ a)
  refine ⟨Over.homMk y hy', hy, fun a => ?_⟩
  show valAt' y V a = χ a
  rw [GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ _ hy, he]

theorem val_cst {G : Over (Sp R)} (V : G.left.Opens) {θ : R →+* ℂ} (x : Over.mk (spMap θ) ⟶ G)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (r : R) : valAt' x.left V (cst G.hom V r) = θ r :=
  (GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ _ hx _).trans (valR_cst G.hom V θ x.left (Over.w x) hx r)

theorem pt_ext {G : Over (Sp R)} {V : G.left.Opens} (hV : IsAffineOpen V) {θ : R →+* ℂ}
    {x y : Over.mk (spMap θ) ⟶ G} (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (hy : ⊤ ≤ y.left ⁻¹ᵁ V)
    (h : ∀ a, valAt' x.left V a = valAt' y.left V a) : x = y :=
  Over.OverMorphism.ext (point_ext hV hx hy h)

theorem tan_der {X : Scheme.{0}} {x : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X}
    (h : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x) {V : X.Opens} (hx : ⊤ ≤ x ⁻¹ᵁ V) :
    ∃ D : Γ(X, V) →+ ℂ, (∀ f, D f = TrivSqZeroExt.snd (valR v V f)) ∧
      ∀ f f', D (f * f') = valAt' x V f * D f' + valAt' x V f' * D f := by
  have hv := (le_preimage_dual_iff h V).2 hx
  refine ⟨AddMonoidHom.mk' (fun f => TrivSqZeroExt.snd (valR v V f)) fun a b => ?_, fun _ => rfl, fun f f' => ?_⟩
  · simp only [valR_eq _ _ hv, map_add (f := _), TrivSqZeroExt.snd_add]
  · have e1 := fst_valR h hx f
    have e2 := fst_valR h hx f'
    simp only [AddMonoidHom.mk'_apply]
    rw [← e1, ← e2]
    simp only [valR_eq _ _ hv, map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring

theorem one_left_spMap {G : Over (Sp R)} [GrpObj G] (θ : R →+* ℂ) :
    (1 : Over.mk (spMap θ) ⟶ G).left = spMap θ ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left := by
  have e : (Over.homMk (spMap θ) (by simp) : Over.mk (spMap θ) ⟶ Over.mk (𝟙 (Sp R))) ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G) = 1 := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
  exact (congrArg (fun q => Over.Hom.left q) e).symm

theorem tan_base {G : Over (Sp R)} [GrpObj G] {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (𝟙 (Sp R)) E) (θ : R →+* ℂ) (w : E) :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (spMap (dualMap θ) ≫ (M.pt w).left) =
      (1 : Over.mk (spMap θ) ⟶ G).left := by
  rw [one_left_spMap, ← M.tan w, ← Category.assoc, ← Category.assoc]
  congr 1
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun x => ?_
  show TrivSqZeroExt.fst (dualMap θ x) = θ (TrivSqZeroExt.fst x)
  simp [dualMap]

theorem tan_over {G : Over (Sp R)} [GrpObj G] {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (𝟙 (Sp R)) E) (θ : R →+* ℂ) (w : E) :
    (spMap (dualMap θ) ≫ (M.pt w).left) ≫ G.hom = spMap ((algebraMap ℂ (DualNumber ℂ)).comp θ) := by
  have e : (M.pt w).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R) := Over.w (M.pt w)
  rw [Category.assoc, e, Category.comp_id]
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl']

end GlobalTheory.CompanionTheory.Ar.Flat.ExpChart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.ChartHol

open Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt GlobalTheory.HolHom GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

theorem diffOn_div {f g : V → ℂ} {s : Set V} (hf : DifferentiableOn ℂ f s) (hg : DifferentiableOn ℂ g s)
    (h0 : ∀ b ∈ s, g b ≠ 0) : DifferentiableOn ℂ (fun b => f b / g b) s :=
  (hf.mul (hg.inv h0)).congr fun b _ => by simp [div_eq_mul_inv]

theorem holAt_of_isAffineOpen {N : Set V} {c : V → (Sp ℂ ⟶ X)} {A : X.Opens} (hA : IsAffineOpen A) (hN : IsOpen N)
    (hin : ∀ b ∈ N, ⊤ ≤ c b ⁻¹ᵁ A) (hz : ∀ r : Γ(X, A), DifferentiableOn ℂ (fun b => valAt' (c b) A r) N)
    {b₀ : V} (hb₀ : b₀ ∈ N) : HolAt c b₀ := by
  intro U hU
  have hmU : (c b₀) (default : PrimeSpectrum ℂ) ∈ U := (le_preimage_iff _ _).1 hU
  have hmA : (c b₀) (default : PrimeSpectrum ℂ) ∈ A := (le_preimage_iff _ _).1 (hin b₀ hb₀)
  obtain ⟨r, hrU, hr0⟩ := hA.exists_basicOpen_le (V := U) ⟨_, hmU⟩ hmA
  set M := {b ∈ N | valAt' (c b) A r ≠ 0} with hMdef
  have hMo : IsOpen M := (hz r).continuousOn.isOpen_inter_preimage hN isOpen_ne
  have hD : ∀ b ∈ M, ⊤ ≤ c b ⁻¹ᵁ X.basicOpen r := fun b hb =>
    (le_basicOpen_iff (c b) (hin b hb.1) r).2 hb.2
  have hb0M : b₀ ∈ M := ⟨hb₀, (le_basicOpen_iff (c b₀) (hin b₀ hb₀) r).1 ((le_preimage_iff _ _).2 hr0)⟩
  refine ⟨?_, fun f => ?_⟩
  · filter_upwards [hMo.mem_nhds hb0M] with b hb
    exact (hD b hb).trans (Scheme.Hom.preimage_mono _ hrU)
  · haveI := hA.isLocalization_basicOpen r
    obtain ⟨⟨hh, s⟩, hk⟩ := IsLocalization.surj (Submonoid.powers r) (X.presheaf.map (homOfLE hrU).op f)
    obtain ⟨k, hks⟩ := s.2
    dsimp only at hk
    have hval : ∀ b ∈ M, valAt' (c b) U f * valAt' (c b) A r ^ k = valAt' (c b) A hh := by
      intro b hb
      have e := congrArg (valAt' (c b) (X.basicOpen r)) hk
      rw [ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_mul,
        ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_res (c b) hrU (hD b hb)] at e
      have e2 : ∀ x : Γ(X, A), valAt' (c b) (X.basicOpen r) (algebraMap Γ(X, A) Γ(X, X.basicOpen r) x) =
          valAt' (c b) A x := fun x =>
        ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_res (c b) (X.basicOpen_le r) (hD b hb) x
      rw [e2, e2, ← hks] at e
      have e3 : valAt' (c b) A (r ^ k) = valAt' (c b) A r ^ k := map_pow (valHom (c b) A (hin b hb.1)) r k
      rw [e3] at e
      exact e
    have h1 : DifferentiableOn ℂ (fun b => valAt' (c b) A hh) M := (hz hh).mono fun b (hb : b ∈ M) => hb.1
    have h2 : DifferentiableOn ℂ (fun b => valAt' (c b) A r) M := (hz r).mono fun b (hb : b ∈ M) => hb.1
    have h3 : DifferentiableOn ℂ (fun b => valAt' (c b) A hh / valAt' (c b) A r ^ k) M :=
      diffOn_div h1 (h2.fun_pow k) fun b hb => pow_ne_zero _ hb.2
    refine ((h3.congr fun b hb => ?_).differentiableAt (hMo.mem_nhds hb0M))
    rw [eq_div_iff (pow_ne_zero _ hb.2)]
    exact hval b hb

variable {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

theorem genMap_germ {A : X.Opens} (hg : genPt ξ ∈ A) (q : Cpt ξ) (hq : q.1 ∈ A) (r : Γ(X, A)) :
    genMap ξ q (X.presheaf.germ A q.1 hq r) =
      (X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ).hom r := by
  have h1 := X.presheaf.germ_stalkSpecializes (U := A) (y := q.1) hq q.2
  have h3 : X.presheaf.germ A q.1 hq ≫ (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) =
      X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Scheme.stalkClosedPointTo ξ) h1)
  exact congrArg (fun f => f.hom r) h3

theorem valAt_section (hall : ∀ q : X, genPt ξ ⤳ q) {A : X.Opens} (hg : genPt ξ ∈ A) (r : Γ(X, A))
    {z : Sp ℂ ⟶ X} (hz : ⊤ ≤ z ⁻¹ᵁ A) :
    ValAt ξ z ((X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ).hom r) (valAt' z A r) := by
  have hc : centre z ∈ A := (le_preimage_iff z A).1 hz
  refine ⟨hall _, X.presheaf.germ A (centre z) hc r, genMap_germ hg ⟨centre z, hall _⟩ hc r, ?_⟩
  rw [valAt'_of _ _ hz]
  exact congrArg (fun φ => φ.hom r) (GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap z A hz)

theorem exists_hol_value (hall : ∀ q : X, genPt ξ ⤳ q) {N : Set V} {β : V → (Σ k, J k) → ℂ} {ζ : V → (Sp ℂ ⟶ X)}
    (c : (k : K) → J k) (hβ : ∀ p, DifferentiableOn ℂ (fun b => β b p) N)
    (hco : ∀ b ∈ N, CoordsAt ξ y (ζ b) (β b)) (hne : ∀ b ∈ N, ∀ k, β b ⟨k, c k⟩ ≠ 0) {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) :
    ∃ F : V → ℂ, DifferentiableOn ℂ F N ∧ ∀ b ∈ N, ValAt ξ (ζ b) a (F b) := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨j, rfl⟩ := ha
    refine ⟨fun b => ∏ k, β b ⟨k, j k⟩ / β b ⟨k, c k⟩, ?_, fun b hb => ?_⟩
    · have hS : ∀ S : Finset K, DifferentiableOn ℂ (fun b => ∏ k ∈ S, β b ⟨k, j k⟩ / β b ⟨k, c k⟩) N := by
        classical
        intro S
        induction S using Finset.induction_on with
        | empty => simpa using differentiableOn_const (c := (1 : ℂ))
        | insert k S hk ih =>
          simp only [Finset.prod_insert hk]
          exact (diffOn_div (hβ _) (hβ _) fun b hb => hne b hb k).fun_mul ih
      exact hS _
    · simp only [← Finset.prod_div_distrib]
      have hS : ∀ S : Finset K, ValAt ξ (ζ b) (∏ k ∈ S, y ⟨k, j k⟩ / y ⟨k, c k⟩)
          (∏ k ∈ S, β b ⟨k, j k⟩ / β b ⟨k, c k⟩) := by
        classical
        intro S
        induction S using Finset.induction_on with
        | empty => simpa using val_one (ξ := ξ) (z := ζ b) (hall _)
        | insert k S hk ih =>
          rw [Finset.prod_insert hk, Finset.prod_insert hk]
          refine val_mul ?_ ih
          obtain ⟨r, hr, hr'⟩ := ((hco b hb).2 k (c k) (isUnit_iff_ne_zero.2 (hne b hb k))).2 (j k)
          rwa [hr', mul_div_cancel_right₀ _ (hne b hb k)]
      exact hS _
  | algebraMap n =>
    refine ⟨fun _ => (n : ℂ), differentiableOn_const _, fun b _ => ?_⟩
    exact ⟨hall _, (n : X.presheaf.stalk (centre (ζ b))), by simp, map_intCast _ n⟩
  | add a a' _ _ h h' =>
    obtain ⟨F, hF, hv⟩ := h
    obtain ⟨F', hF', hv'⟩ := h'
    exact ⟨fun b => F b + F' b, hF.fun_add hF', fun b hb => val_add (hv b hb) (hv' b hb)⟩
  | mul a a' _ _ h h' =>
    obtain ⟨F, hF, hv⟩ := h
    obtain ⟨F', hF', hv'⟩ := h'
    exact ⟨fun b => F b * F' b, hF.fun_mul hF', fun b hb => val_mul (hv b hb) (hv' b hb)⟩

theorem isHolTo_of_coordsAt (htie : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hall : ∀ q : X, genPt ξ ⤳ q) {B : Set V} {β : V → (Σ k, J k) → ℂ} {ζ : V → (Sp ℂ ⟶ X)} (hB : IsOpen B)
    (hβ : ∀ p, DifferentiableOn ℂ (fun b => β b p) B) (hco : ∀ b ∈ B, CoordsAt ξ y (ζ b) (β b)) :
    IsHolTo B ζ := by
  refine isHolTo_of_holAt hB fun b₁ hb₁ => ?_
  choose c hc using (hco b₁ hb₁).1
  set N := {b ∈ B | ∀ k, β b ⟨k, c k⟩ ≠ 0} with hNdef
  have hNB : N ⊆ B := fun b hb => hb.1
  have hNo : IsOpen N := by
    refine isOpen_iff_mem_nhds.2 fun b hb => ?_
    have hk : ∀ᶠ t in 𝓝 b, ∀ k, β t ⟨k, c k⟩ ≠ 0 := eventually_all.2 fun k =>
      ((hβ _).continuousOn.continuousAt (hB.mem_nhds hb.1)).eventually_ne (hb.2 k)
    filter_upwards [hB.mem_nhds hb.1, hk] with t h1 h2 using ⟨h1, h2⟩
  have hb₁N : b₁ ∈ N := ⟨hb₁, fun k => (hc k).ne_zero⟩
  have hx0 : (∏ k, y ⟨k, c k⟩) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => ((hco b₁ hb₁).2 k (c k) (hc k)).1
  obtain ⟨A, hA, hAq⟩ := htie.affine c hx0
  have hin : ∀ b ∈ N, ⊤ ≤ ζ b ⁻¹ᵁ A := fun b hb =>
    (le_preimage_iff _ _).2 ((hAq _).2 ⟨hall _, in_chart (hall _) (hco b hb.1) hb.2⟩)
  have hg : genPt ξ ∈ A := (hall _).mem_open A.2 ((le_preimage_iff _ _).1 (hin b₁ hb₁N))
  refine holAt_of_isAffineOpen hA hNo hin (fun r => ?_) hb₁N
  have ha := (htie.ring c hx0 ((X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ).hom r)).2
    fun p hp => ⟨_, genMap_germ hg p ((hAq _).2 ⟨p.2, hp⟩) r⟩
  obtain ⟨F, hF, hFv⟩ := exists_hol_value hall c (fun p => (hβ p).mono hNB) (fun b hb => hco b hb.1)
    (fun b hb => hb.2) ha
  refine hF.congr fun b hb => ?_
  exact val_unique htie.gen (valAt_section hall hg r (hin b hb)) (hFv b hb)

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.ChartHol
end
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem dotDual_latFamily : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (r : ℕ) (Γ : (∀ k, J k) → AddSubgroup (Fin r → Ω)), IsLatFamily O y Γ → (∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (Γ c)) → IsLatFamily O y (fun c => dotDual (chartRing O (mseg y) c) (Γ c)) ∧ ∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (dotDual (chartRing O (mseg y) c) (Γ c)) :=
  @PositivityTheory.Xgn.dual_lattice_family

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem gram_invertible_of_unramified : ∀ (E : Type) [Field E] [NumberField E] (cc : E ≃+* E) (p R N : ℕ) [Fact p.Prime], 1 ≤ R → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)), (∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv cc a • y)) → (∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') → ∀ (O Ω : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ¬ IsUnit (p : O) → ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) → ∃ C : Matrix (Fin N) (Fin N) Ω, (∀ i j, C i j ∈ (algebraMap O Ω).range) ∧ (Matrix.of fun i j => ∑ k, σ (HT.dualInt E k) * ((e (Pi.single i (RingOfIntegers.basis E k)) (Pi.single j 1)).val : Ω)) * C = 1 :=
  @PositivityTheory.Xgn.gram_determinant_unit_mod_p

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.BaseChange

theorem torsion_isBaseChange : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R'] (T : Type) [CommGroup T] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (x' : Spec (CommRingCat.of R') ⟶ S), Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x = x' → ∀ (N : ℕ) (i : Γ.G.left ⟶ G.left) (i' : Γ'.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Γ'.IsTorsionAlong G x' N i' → ∀ (a : FractionRing R →+* FractionRing R'), a.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp (algebraMap R R') → (∀ t, Spec.map (CommRingCat.ofHom a) ≫ (Γ.pt t).left ≫ i = (Γ'.pt t).left ≫ i') → ∃ F : Γ'.G.left ⟶ Γ.G.left, F ≫ i = i' ∧ Γ'.IsBaseChange Γ (algebraMap R R') F :=
  @PositivityTheory.Xgn.torsion_group_base_change

end GlobalTheory.CompanionTheory.Ar.BT.BaseChange
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_free_of_smooth : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Nonempty (Module.Basis (Fin g) R E) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.lie_model_free_of_smooth | exact GlobalTheory.CompanionTheory.Relay.lie_model_free_of_smooth | (intros; apply GlobalTheory.CompanionTheory.Relay.lie_model_free_of_smooth <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

theorem _root_.GlobalTheory.T.generic_of_smooth_surjective : ∀ (K : Type) [Field K] (X₀ X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (π : X' ⟶ X₀) (s' : X' ⟶ Spec (CommRingCat.of K)), Smooth s' → ξ' ≫ π = ξ → IsCptGen ξ → Function.Surjective (π.stalkMap (genPt ξ')).hom → IsCptGen ξ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CptLift.isCptGen_of_smooth_of_surjective | exact GlobalTheory.CompanionTheory.Ar.CptLift.isCptGen_of_smooth_of_surjective | (intros; apply GlobalTheory.CompanionTheory.Ar.CptLift.isCptGen_of_smooth_of_surjective <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.btOrder_embedding_iso_finite : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsFinite Γ.G.hom → IsIso j := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.FiniteIso.isIso_of_finite
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem coordTie_points_eq : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → ∀ c : κ, x c ≠ 0 → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra B Ω], Function.Injective (algebraMap B Ω) → (∀ c', x c' / x c ∈ (algebraMap B Ω).range) → ∀ z z' : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ z = ξ → Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ z' = ξ → z = z' :=
  @PositivityTheory.Xgn.same_generic_point_charts

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.valAt_iff_value_at : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), genPt ξ ⤳ centre z → CoordsAt ξ y z w → ∀ (a : Ω) (v : ℂ), ValAt ξ z a v ↔ GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y a w v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords | exact GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords <;> assumption)
end
