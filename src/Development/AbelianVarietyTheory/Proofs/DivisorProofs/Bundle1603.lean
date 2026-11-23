module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle006
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section
namespace GlobalTheory.WeilDatumF

theorem fst_symplOF_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (y z : WOF F E nS nT)
    (h : y.map (infPartF F E) = 0 ∨ z.map (infPartF F E) = 0) : fstA F (symplOF σ JS JT ξ₀ y z) = 0 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.OrientedHeis.map_trace_hO_zero (fstA F) σ (incAF F E ξ₀) (fun a b => incAF F E (JS⁻¹ a b))
    (fun c d => incAF F E (JT c d)) y z h

theorem snd_symplOF_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (y z : WOF F E nS nT)
    (h : y.map (finPartF F E) = 0 ∨ z.map (finPartF F E) = 0) : sndA F (symplOF σ JS JT ξ₀ y z) = 0 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.OrientedHeis.map_trace_hO_zero (sndA F) σ (incAF F E ξ₀) (fun a b => incAF F E (JS⁻¹ a b))
    (fun c d => incAF F E (JT c d)) y z h

theorem symplOF_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (y z : WOF F E nS nT)
    (h1 : y.map (infPartF F E) = 0 ∨ z.map (infPartF F E) = 0)
    (h2 : y.map (finPartF F E) = 0 ∨ z.map (finPartF F E) = 0) : symplOF σ JS JT ξ₀ y z = 0 :=
  Prod.ext (fst_symplOF_eq_zero σ JS JT ξ₀ y z h1) (snd_symplOF_eq_zero σ JS JT ξ₀ y z h2)

theorem symplOHF_fin_real_orth (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (u x : WOF F E nS nT) :
      u.map (infPartF F E) = 0 → x.map (finPartF F E) = 0 → symplOHF σ JS JT ξ₀ u x = 0 ∧ symplOHF σ JS JT ξ₀ x u = 0 := by
  intro hu hx
  have e1 := symplOF_eq_zero σ JS JT ξ₀ u x (Or.inl hu) (Or.inr hx)
  have e2 := symplOF_eq_zero σ JS JT ξ₀ x u (Or.inr hu) (Or.inl hx)
  unfold symplOHF
  rw [e1, e2, mul_zero]
  exact ⟨rfl, rfl⟩

end GlobalTheory.WeilDatumF
end
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.TowerFD

theorem thetaFunOF_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
      ∀ f : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ ψ f → ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  intro F E _ _ _ _ _ σ nS nT JS JT ξ₀ ψ hψ f hf
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleCocompact.exists_compact_adele F)
  choose c hc using hx
  have hKc : IsCompact (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :
      Set (WOF F E nS nT)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun w => ?_⟩
  have hmem : ratWF (Matrix.of fun i j => c (w i j)) + w ∈
      (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) : Set (WOF F E nS nT)) :=
    fun i _ j _ => hc (w i j)
  have h := hC _ hmem
  have hq := hf.quasi (Matrix.of fun i j => c (w i j)) w
  have h2 : ‖f w‖ = ‖f (ratWF (Matrix.of fun i j => c (w i j)) + w)‖ := by
    rw [hq, norm_mul, hψ.2.1, one_mul]
  exact h2.trans_le h

end GlobalTheory.TowerFD
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLifts

theorem prime_eq_of_mem {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (h1 : (p : 𝓞 K) ∈ P.asIdeal) (h2 : (q : 𝓞 K) ∈ P.asIdeal) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ : IsCoprime (p : 𝓞 K) (q : 𝓞 K) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  exact P.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem places_apart {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (h : L.Is μ0) (t : T) :
    (∀ PP ∈ L.Pg, ∀ PP', PP' ∈ L.Pg ∨ PP' ∈ L.Q t → ¬ Lev.IsConjPl PP PP') ∧ Disjoint L.Pg (L.Q t) := by
  have hQ : ∀ PP ∈ L.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hP k hk
    obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := h.Q_pl t PP hP
    have h1 : (q : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rw [← hc]
      rw [← Ideal.absNorm_eq_natCard]
      exact Ideal.absNorm_mem PP.asIdeal
    exact hne k (prime_eq_of_mem PP hq (D.host.g_prime k) h1 hk)
  refine ⟨fun PP hP PP' hP' hc => ?_, Finset.disjoint_left.2 fun PP hP hP' => ?_⟩
  · rcases hP' with hP' | hP'
    · exact GlobalTheory.TypePlaces.not_isConjPl L.C.P L.Pg h.Pg PP hP PP' hP' hc
    · obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
      obtain ⟨c, hc', e⟩ := hc _ (L.C.P.overP hk)
      have e' : c = ((D.host.g k : ℕ) : 𝓞 D.host.E) := RingOfIntegers.ext (by rw [e]; simp)
      exact hQ PP' hP' k (e' ▸ hc')
  · obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
    exact hQ PP hP' k (L.C.P.overP hk)

theorem lifts_exist : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m), (∀ (t : T) (g0 : G0 R.Pg D.R.r), ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ) ∧ ∀ g0 : G0 R.Pg D.R.r, ∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h i
  obtain ⟨c, hc⟩ := h.βV i
  obtain ⟨c', hc'⟩ := h.βW i
  refine ⟨fun t => ?_, ?_⟩
  · exact GlobalTheory.ParahoricLift.liftsExist (Vc D i) (R.βV i) (R.datVt i t) _ _ hc (places_apart _ h t).1 (places_apart _ h t).2
  · refine GlobalTheory.ParahoricLift.liftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) _ _ hc' (fun PP hP PP' hP' => ?_)
      (Finset.disjoint_empty_right _)
    exact (places_apart _ h A.μ0).1 PP hP PP' (hP'.imp id fun h0 => absurd h0 (Finset.notMem_empty _))

end GlobalTheory.StepLifts
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev
  Formalism.IndefR
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodFiniteDim

variable {D : D7}

theorem isOpen_comap_Kg (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (T : Finset (Pl D.host.E)) :
    IsOpen (((Kg D.sp.cm V.gram β T).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β T] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  exact ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩

theorem levFn_eq_one {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {T : Finset (Pl D.host.E)}
    (hg : L.Pg ⊆ T) (hq : L.Q ⊆ T) {x : GL (Fin V.rank) (Lev.EAf D)} (hx : x ∈ Kg D.sp.cm V.gram β T) :
    levFn β L x = 1 := by
  have h3 : ∀ PP ∈ T, redFn β PP x = 1 := by
    have h1 : x ∈ ⨅ PP ∈ T, princAt β PP := hx.2
    exact fun PP hP => (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2
  have h4 : rTup β L x = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 x) = 1
    rw [h3 PP.1 (hg PP.2)]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levFn
  rw [h4, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hP
    rw [h3 PP (hq hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [h3 PP (hg hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]

theorem exists_open_subgroup (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ k ∈ U, k ∈ GfC V → k ∈ (levG V β L : Set (GA D V)) ∧ levChi V β L k = 1 := by
  classical
  refine ⟨_, isOpen_comap_Kg V β (L.Pg ∪ L.Q), fun k hk hf => ⟨⟨hf, ?_⟩, ?_⟩⟩
  · exact Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right hk
  · unfold levChi
    rw [levFn_eq_one Finset.subset_union_left Finset.subset_union_right hk, Units.val_one]

end GlobalTheory.GoodFiniteDim
end

section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LieFaithful

open IsLocalRing

theorem exists_lift_stalk {X : Scheme.{0}} (x : X) {D : CommRingCat.{0}} [IsLocalRing D] (f : Spec D ⟶ X)
    (h : f (closedPoint D) = x) : ∃ ρ : X.presheaf.stalk x ⟶ D, Spec.map ρ ≫ X.fromSpecStalk x = f := by
  subst h
  exact ⟨Scheme.stalkClosedPointTo f, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

theorem stalk_hom_ext {X : Scheme.{0}} (x : X) {D : CommRingCat.{0}} (ρ ρ' : X.presheaf.stalk x ⟶ D)
    (h : Spec.map ρ ≫ X.fromSpecStalk x = Spec.map ρ' ≫ X.fromSpecStalk x) : ρ = ρ' :=
  Spec.map_injective ((cancel_mono _).1 h)

variable {k : Type} [Field k]

section One

variable (G : Over (Sp k)) [GrpObj G]

def unitSec : Sp k ⟶ G.left := (η[G] : 𝟙_ (Over (Sp k)) ⟶ G).left

theorem unitSec_hom : unitSec G ≫ G.hom = 𝟙 _ := Over.w (η[G] : 𝟙_ (Over (Sp k)) ⟶ G)

theorem one_left {T : Over (Sp k)} : (1 : T ⟶ G).left = T.hom ≫ unitSec G := by
  rw [Hom.one_def, Over.comp_left]
  rfl

def origin : G.left := unitSec G (closedPoint k)

abbrev Germ : CommRingCat.{0} := G.left.presheaf.stalk (origin G)

abbrev germMap : Spec (Germ G) ⟶ G.left := G.left.fromSpecStalk (origin G)

def germConst : CommRingCat.of k ⟶ Germ G := Spec.preimage (germMap G ≫ G.hom)

theorem spec_germConst : Spec.map (germConst G) = germMap G ≫ G.hom := Spec.map_preimage _

abbrev germAlg : Algebra k (Germ G) := (germConst G).hom.toAlgebra

attribute [local instance] germAlg

def germEv0 : Germ G ⟶ CommRingCat.of k := (exists_lift_stalk (origin G) (unitSec G) rfl).choose

theorem spec_germEv0 : Spec.map (germEv0 G) ≫ germMap G = unitSec G :=
  (exists_lift_stalk (origin G) (unitSec G) rfl).choose_spec

theorem germConst_germEv0 : germConst G ≫ germEv0 G = 𝟙 _ := by
  apply Spec.map_injective
  rw [Spec.map_comp, spec_germConst, ← Category.assoc, spec_germEv0, unitSec_hom, Spec.map_id]

def germEv : Germ G →ₐ[k] k where
  toRingHom := (germEv0 G).hom
  commutes' a := congrArg (fun φ => φ.hom a) (germConst_germEv0 G)

def tanPt (lam : (RingHom.ker (germEv G)).Cotangent →ₗ[k] k) : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ G :=
  Over.homMk (Spec.map (CommRingCat.ofHom (tanHom (germEv G) lam).toRingHom) ≫ germMap G) (by
    dsimp
    rw [Category.assoc, ← spec_germConst, Category.comp_id, ← Spec.map_comp]
    congr 1
    ext a : 2
    exact (tanHom (germEv G) lam).commutes a)

theorem tanPt_left (lam : (RingHom.ker (germEv G)).Cotangent →ₗ[k] k) : (tanPt G lam).left =
    Spec.map (CommRingCat.ofHom (tanHom (germEv G) lam).toRingHom) ≫ germMap G := rfl

theorem one_left_dual : (1 : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ G).left =
    Spec.map (germEv0 G ≫ CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ germMap G := by
  rw [one_left, Spec.map_comp, Category.assoc, spec_germEv0]
  simp

theorem smT_zero_tanPt (lam : (RingHom.ker (germEv G)).Cotangent →ₗ[k] k) :
    smT (𝟙 (Sp k)) 0 (tanPt G lam) = 1 := by
  apply Over.OverMorphism.ext
  rw [smT_left, tanPt_left, one_left_dual, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a : 2
  change epsMul 0 (tanHom (germEv G) lam a) = algebraMap k (DualNumber k) (germEv G a)
  ext
  · simp [epsMul, tanHom_fst, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

end One

theorem exists_germHom {G H : Over (Sp k)} [GrpObj G] [GrpObj H] (g : G ⟶ H) (hg : η[G] ≫ g = η[H]) :
    ∃ ψ : Germ H ⟶ Germ G, Spec.map ψ ≫ germMap H = germMap G ≫ g.left := by
  refine exists_lift_stalk _ _ ?_
  have h : unitSec G ≫ g.left = unitSec H := congrArg (fun φ => φ.left) hg
  have h1 : germMap G (closedPoint (Germ G)) = origin G := Scheme.fromSpecStalk_closedPoint
  change g.left (germMap G (closedPoint (Germ G))) = _
  rw [h1, origin, origin, ← h]
  rfl

attribute [local instance] germAlg

theorem germ_doubling {G : Over (Sp k)} [GrpObj G] (φ : Germ G ⟶ Germ G)
    (hφ : Spec.map φ ≫ germMap G = germMap G ≫ (𝟙 G * 𝟙 G : G ⟶ G).left) (x : Germ G)
    (hx : x ∈ maximalIdeal (Germ G)) : φ.hom x - 2 * x ∈ maximalIdeal (Germ G) ^ 2 := by
  rw [← ker_eq_maximalIdeal_of_algHom (germEv G)] at hx ⊢
  refine mem_sq_of_tanHom_eq_zero _ _ fun lam => ?_
  have h1 : tanPt G lam ≫ (𝟙 G * 𝟙 G : G ⟶ G) = smT (𝟙 (Sp k)) 2 (tanPt G lam) := by
    rw [MonObj.comp_mul, Category.comp_id, ← one_add_one_eq_two, smT_add _ _ (smT_zero_tanPt G lam), smT_unit]
  have h2 := congrArg (fun φ => φ.left) h1
  simp only [Over.comp_left] at h2
  rw [smT_left, tanPt_left, Category.assoc, ← hφ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp] at h2
  have h3 := congrArg (fun ρ => ρ.hom x) (stalk_hom_ext _ _ _ h2)
  change tanHom (germEv G) lam (φ.hom x) = epsMul 2 (tanHom (germEv G) lam x) at h3
  have h0 : germEv G x = 0 := hx
  rw [map_sub, two_mul, map_add (f := _), h3]
  ext
  · simp [epsMul, tanHom_fst, h0]
  · simp [epsMul, two_mul]

theorem germ_sq_of_tan {G H : Over (Sp k)} [GrpObj G] [GrpObj H] (g : G ⟶ H) (ψ : Germ H ⟶ Germ G)
    (hψ : Spec.map ψ ≫ germMap H = germMap G ≫ g.left)
    (hg : ∀ v : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ G, smT (𝟙 (Sp k)) 0 v = 1 → v ≫ g = 1) (x : Germ H)
    (hx : x ∈ maximalIdeal (Germ H)) : ψ.hom x ∈ maximalIdeal (Germ G) ^ 2 := by
  rw [← ker_eq_maximalIdeal_of_algHom (germEv H)] at hx
  rw [← ker_eq_maximalIdeal_of_algHom (germEv G)]
  refine mem_sq_of_tanHom_eq_zero _ _ fun lam => ?_
  have h2 := congrArg (fun φ => φ.left) (hg _ (smT_zero_tanPt G lam))
  simp only [Over.comp_left] at h2
  rw [one_left_dual, tanPt_left, Category.assoc, ← hψ, ← Category.assoc, ← Spec.map_comp] at h2
  have h3 := congrArg (fun ρ => ρ.hom x) (stalk_hom_ext _ _ _ h2)
  change tanHom (germEv G) lam (ψ.hom x) = algebraMap k (DualNumber k) (germEv H x) at h3
  have h0 : germEv H x = 0 := hx
  rw [h3, h0, map_zero]

theorem germMap_comp_eq_one {G H : Over (Sp k)} [GrpObj G] [GrpObj H] (g : G ⟶ H) (ψ : Germ H ⟶ Germ G)
    (hψ : Spec.map ψ ≫ germMap H = germMap G ≫ g.left)
    (h0 : ∀ x ∈ maximalIdeal (Germ H), ψ.hom x = 0) :
    germMap G ≫ g.left = germMap G ≫ (1 : G ⟶ H).left := by
  have hc : germConst H ≫ ψ = germConst G := by
    apply Spec.map_injective
    rw [Spec.map_comp, spec_germConst, spec_germConst, ← Category.assoc, hψ, Category.assoc, Over.w]
  have he : ψ = germEv0 H ≫ germConst G := by
    ext x : 2
    have h1 : x - algebraMap k (Germ H) (germEv H x) ∈ maximalIdeal (Germ H) := by
      rw [← ker_eq_maximalIdeal_of_algHom (germEv H)]
      exact (kerPart (germEv H) x).2
    have h2 := h0 _ h1
    rw [map_sub, sub_eq_zero] at h2
    rw [h2]
    exact congrArg (fun ρ => ρ.hom (germEv H x)) hc
  rw [← hψ, he, Spec.map_comp, Category.assoc, spec_germEv0, spec_germConst, one_left, Category.assoc]

theorem hom_eq_of_tangent_eq : ∀ (k : Type) [Field k] [CharZero k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (f f' : A ⟶ B) [IsMonHom f] [IsMonHom f'], (∀ v : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ A, smT (𝟙 (Sp k)) 0 v = 1 → v ≫ f = v ≫ f') → f = f' := by
  intro k _ _ A B _ _ _ _ hA hB f f' _ _ h
  have hint := GlobalTheory.isIntegral_left_of_isAbelianScheme_field A hA
  have := hA.proper
  have := hB.proper
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  let g : A ⟶ B := f * f'⁻¹
  have hu : IsMonHom g := by
    simp only [g]
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  have hg : ∀ v : overAt (𝟙 (Sp k)) (DualNumber k) ⟶ A, smT (𝟙 (Sp k)) 0 v = 1 → v ≫ g = 1 := fun v hv => by
    simp only [g]
    rw [MonObj.comp_mul, GrpObj.comp_inv, h v hv, mul_inv_cancel]
  have h2 : ∀ (G : Over (Sp k)) [GrpObj G], η[G] ≫ (𝟙 G * 𝟙 G : G ⟶ G) = η[G] := fun G _ => by
    have e : (η[G] : 𝟙_ (Over (Sp k)) ⟶ G) = 1 := by simp [Hom.one_def]
    rw [MonObj.comp_mul, Category.comp_id, e, _root_.mul_one]
  obtain ⟨ψ, hψ⟩ := exists_germHom g (IsMonHom.one_hom g)
  obtain ⟨φA, hφA⟩ := exists_germHom _ (h2 A)
  obtain ⟨φB, hφB⟩ := exists_germHom _ (h2 B)
  have hcomm : (𝟙 A * 𝟙 A : A ⟶ A) ≫ g = g ≫ (𝟙 B * 𝟙 B : B ⟶ B) := by
    rw [MonObj.mul_comp, MonObj.comp_mul g, Category.comp_id, Category.id_comp]
  have hcomm' : (𝟙 A * 𝟙 A : A ⟶ A).left ≫ g.left = g.left ≫ (𝟙 B * 𝟙 B : B ⟶ B).left :=
    congrArg (fun φ => φ.left) hcomm
  have hc : φB ≫ ψ = ψ ≫ φA := by
    apply stalk_hom_ext
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hφB, hψ, ← Category.assoc, hψ,
      ← Category.assoc, hφA, Category.assoc, Category.assoc, hcomm']
  have h0 := map_eq_zero_of_commute_doubling (k := k) (maximalIdeal (Germ B)) φA.hom φB.hom ψ.hom
    (fun x => congrArg (fun ρ => ρ.hom x) hc) (germ_sq_of_tan g ψ hψ hg) (germ_doubling φA hφA)
    (germ_doubling φB hφB)
  have h3 := germMap_comp_eq_one g ψ hψ h0
  have : IsDominant (germMap A) := ⟨by
    refine dense_iff_closure_eq.2 (top_unique ((genericPoint_spec A.left).def.ge.trans
      (closure_mono (Set.singleton_subset_iff.2 ?_))))
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes _⟩
  have h4 : g = 1 := Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated B.hom ((Over.w _).trans (Over.w _).symm) (germMap A) h3)
  exact mul_inv_eq_one.1 h4

end GlobalTheory.LieFaithful
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.order_lattice_basis_integrality : ∀ {A B : Type} [Ring A] [CommRing B] (j : B →+* A) (Λ : Set A) (R : Set B) (r : ℕ) (e : Fin r → A),
    (0 : A) ∈ Λ → (1 : A) ∈ Λ → (∀ x ∈ Λ, ∀ y ∈ Λ, x + y ∈ Λ) → (∀ x ∈ Λ, -x ∈ Λ) →
    (∀ x ∈ Λ, ∀ y ∈ Λ, x * y ∈ Λ) →
    (0 : B) ∈ R → (1 : B) ∈ R → (∀ x ∈ R, ∀ y ∈ R, x + y ∈ R) → (∀ x ∈ R, -x ∈ R) →
    (∀ x ∈ R, ∀ y ∈ R, x * y ∈ R) →
    (∀ a : A, ∃! β : Fin r → B, a = ∑ i, j (β i) * e i) →
    (∀ β : Fin r → B, (∑ i, j (β i) * e i ∈ Λ) ↔ ∀ i, β i ∈ R) →
    (∀ i i' : Fin r, ∃ (N : ℕ) (ρ : Fin N → B) (μ : Fin N → A), (∀ k, ρ k ∈ R) ∧ (∀ k, μ k ∈ Λ) ∧
      ∀ β : Fin r → B, ∑ k, j (ρ k) * (∑ i'', j (β i'') * e i'') * μ k = j (β i') * e i) →
    (∀ a : A, ∃ D : ℤ, D ≠ 0 ∧ (D : A) * a ∈ Λ) →
    (∀ I : Set B, (0 : B) ∈ I → (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ ∈ R, ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x ∈ R, (D : B) * x ∈ I) ∧ ∀ x ∈ I, (D : B) * x ∈ R) →
      ∃ m : Bˣ, ∀ x, x ∈ I ↔ ∃ ρ ∈ R, x = ↑m * ρ) →
    ∀ X : Aˣ, (∀ ρ ∈ R, (X : A) * j ρ * ↑X⁻¹ ∈ Λ) → ∃ m : Bˣ, (X : A) * j ↑m ∈ Λ ∧ j ↑m⁻¹ * ↑X⁻¹ ∈ Λ := by
  first | (exact @GlobalTheory.AbsLattice.exists_unit_of_conj_stable) | (exact GlobalTheory.AbsLattice.exists_unit_of_conj_stable) | (intros; apply GlobalTheory.AbsLattice.exists_unit_of_conj_stable  <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.coneCoordinate_le_pow_of_prod_eq_one : ∀ (a : ℕ) (t : ℝ), 0 < t → ∃ C : ℝ, 1 ≤ C ∧ ∀ (r : Fin a → ℝ) (ρ : ℝ), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → 1 ≤ ρ → (∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) → ∀ i, r i ≤ C * ρ ^ a ∧ (r i)⁻¹ ≤ C * ρ ^ a := by
  first | exact @GlobalTheory.coneCoord_le_pow_of_prod_eq_one | exact GlobalTheory.coneCoord_le_pow_of_prod_eq_one | (intros; apply GlobalTheory.coneCoord_le_pow_of_prod_eq_one <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_isFinite_restrict_near_codimOne : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → IsProjOver q → topologicalKrullDim Y = D → ∀ π : Y ⟶ X, π ≫ p = q → π (genericPoint Y) = genericPoint X → ∀ z : X, Order.coheight z = 1 → ∃ U : X.Opens, z ∈ U ∧ IsFinite (π ∣_ U) := by
  first | exact @GlobalTheory.FiniteNearCodimOne.exists_isFinite_restrict_of_coheight_eq_one | exact GlobalTheory.FiniteNearCodimOne.exists_isFinite_restrict_of_coheight_eq_one | (intros; apply GlobalTheory.FiniteNearCodimOne.exists_isFinite_restrict_of_coheight_eq_one <;> assumption)
end
