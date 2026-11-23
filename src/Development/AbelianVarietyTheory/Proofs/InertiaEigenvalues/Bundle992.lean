module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1625
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle979
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaLiftsIsConjugateCuspExpansion
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle989
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle087
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle827
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle988
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle814
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle591
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle906
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle990
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle991
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle010
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CompIntField
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.DisjointSplitLevelPlaces
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.DescLoc

theorem holSub0_of_cusp : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ T.cuspA j a n, rdU (T.U j T.σ₀) f ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) a n) := by
  intro D T j a n f hf
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.rdC_mem_holSub0 T.good_σ₀ a n ⟨f, hf⟩

theorem desc_loc : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTowerCover T i l C → C.IsPinned (wtA (κ i)) (κ i).n → ∀ la : HeightOneSpectrum (𝓞 C.d.c₂.F), ((l : ℕ) : 𝓞 C.d.c₂.F) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt C.inc {la} → ∀ φ ∈ C.intForms (wtA (κ i)) (κ i).n {la}, (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) → ∀ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, ψ a ∈ baseForms T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n) → φ = ∑ a, C.σ₂ (x a) • ψ a → ∃ (m' : ℕ) (x' : Fin m' → ℂ) (ψ' : Fin m' → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)), (∀ a, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IntVal C.σ₂ {la} (x' a)) ∧ (∀ a, ψ' a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (κ i).n (GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below C.inc {la})) ∧ φ = ∑ a, x' a • ψ' a := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hLev hGrp hFam hMod hThP hTie i hVstd hV hFP l hl C hC hPin la hla hUn φ hφ hKf m x ψ hψ hsum
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hU := hC.1
  choose f hf hfψ using hψ
  have hfc : ∀ b, f b ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := fun b =>
    GlobalTheory.T.mem_cuspForms_allEmbeddings_of_inclusion_reading D T hL _ hj (κ i) (GlobalTheory.AdTh.lastPos_of_kapIs hTie.kap i) (f b) (hf b).1 (hf b).2
  obtain ⟨p, hbelow, hlp, hval⟩ := GlobalTheory.T.exists_unique_place_below_of_unramified_place_over_prime _ _ C.inc l hl la hla hUn
  obtain ⟨la', hla'⟩ := GlobalTheory.T.exists_finitePlace_valuation_comp_ringEquiv _ _ C.d.eF.toRingEquiv la
  let x' : Fin m → C.c'.F := fun b => C.d.eF.symm (x b)
  have hx' : ∀ b, C.d.eF (x' b) = x b := fun b => C.d.eF.apply_symm_apply (x b)
  have hφ' : (∑ b, C.σ₂ (C.d.eF (x' b)) • T.phiJ ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (f b)) ∈
      C.intForms (wtA (κ i)) (κ i).n {la} := by
    simp only [hx', hfψ]
    rw [← hsum]
    exact hφ
  have hint := GlobalTheory.T.bounded_at_place_of_integral_cover_reading D T hL _ hj T.σ₀ T.good_σ₀ C hU (wtA (κ i)) (κ i).n (dom_wtA (κ i)) hPin la la'
    (fun y => hla' y) m x' f (fun b => (hf b).1) hφ'
  have hmem : (∑ b, x' b • GlobalTheory.FieldBC.rulBC C.hle (f b)) ∈
      cusp (T.Q.Xo ((i : ℕ) + 1)) C.c' (unfBC C.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (κ i).n :=
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _
      ((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ C.hle _ (T.U ((i : ℕ) + 1)) _ _ (f b) (hf b).1).2.2 (hfc b))
  have hgood : T.Q.l.GoodAt l :=
    Formalism.L2.Pj.goodAt_of_two_primes hL.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne l hl
  have hvLa : ∀ y : T.Q.c.F, vLa la' (incF T.Q.c C.c' C.hle y) = vLa p y := fun y => by
    unfold vLa
    rw [hla', ← hval]
    rfl
  obtain ⟨m', as, fs, has, hfs, hBC⟩ := GlobalTheory.T.cuspForm_integral_lattice_unramified_descent _ _ _ _ _ _ _ (T.U ((i : ℕ) + 1)) (hL.unf _ hj) p l hl hlp hgood
    C.c' C.hle la' hvLa (GlobalTheory.SecFieldChange.cuspBC_holds C.hle _) (wtA (κ i)) (κ i).n (dom_wtA (κ i))
    (hL.cuspFD _ hj _ _ (dom_wtA (κ i))) _ hmem hint
  refine ⟨m', fun k => C.σ₂ (C.d.eF (as k)), fun k => T.phiJ ((i : ℕ) + 1) T.σ₀ (wtA (κ i)) (fs k), ?_, ?_, ?_⟩
  · intro k
    refine ⟨C.d.eF (as k), rfl, fun q hq => ?_⟩
    obtain rfl := Set.mem_singleton_iff.1 hq
    exact (hla' (as k)).symm.trans_le (has k)
  · intro k
    rw [hbelow]
    refine ⟨fs k, ⟨(cusp_le_sec _ _ _ _ _ (hfs k).1), holSub0_of_cusp D T _ _ _ (fs k) (hfs k).1, ?_⟩, rfl⟩
    intro q hq v hv
    obtain rfl := Set.mem_singleton_iff.1 hq
    exact (GlobalTheory.T.integral_values_algebraic_points_iff_value_nonneg _ _ _ _ _ _ _ (fs k)).1 (hfs k).2 v hv
  · rw [hsum]
    have e := GlobalTheory.T.sum_adelicReading_eq_of_two_baseChange_decomps_on_cover D T _ T.σ₀ C hU.2.2.1 (wtA (κ i)) (κ i).n m m' x' f as fs (fun b => (hf b).1) hBC
    simp only [hx', hfψ] at e
    exact e

end GlobalTheory.DescLoc
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.coreRationalForms_subset_coverForms : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → baseForms T j σ a n ⊆ C.ratForms a n ∧ ∀ (S : Set (HeightOneSpectrum (𝓞 T.Q.c.F))) (S₂ : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), (∀ la₂ ∈ S₂, ∃ la ∈ S, ∀ x : 𝓞 T.Q.c.F, x ∈ la.asIdeal ↔ la₂.valuation C.d.c₂.F (C.inc x) < 1) → baseInt T j σ a n S ⊆ C.intForms a n S₂ := by
  first | exact @GlobalTheory.CoverUp.baseForms_sub_cover | exact GlobalTheory.CoverUp.baseForms_sub_cover | (intros; apply GlobalTheory.CoverUp.baseForms_sub_cover <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.uniformisedLevelCover_exists_constants_dominantWeights : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∃ cc₂ : C.U₂.Comp → ℂ, ∀ a : (D.host.E →+* ℂ) × ℕ → ℕ, Dom a n → ({ C with cc₂ := cc₂ } : Cover T j σ).IsPinned a n := by
  first | exact @GlobalTheory.CoverRead.Cover.exists_pinned_dom | exact GlobalTheory.CoverRead.Cover.exists_pinned_dom | (intros; apply GlobalTheory.CoverRead.Cover.exists_pinned_dom <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

theorem _root_.GlobalTheory.T.baseSections_values_integral_at_coverLift : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, ∀ C : Cover T j σ, C.IsUnif → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c) (g : Fin m → Rul C.d.Xo₂ C.d.c₂), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n) → (∀ k, g k ∈ sec C.d.Xo₂ C.d.c₂ a n) → (∀ k, C.IsPull (β k) (g k)) → ∀ y : Fin m → C.d.c₂.F, (∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v (∑ k, y k • g k)) → ∀ (T0 : CDVR) (io : T.Q.c.F →+* T0.Fr) (pt : IntFr (T.Q.Xo j) T.Q.c T0 io), T0.FinRes → ∀ (T' : CDVR) (i : T0.Fr →+* T'.Fr) (e' : ℕ) (τ : C.d.c₂.F →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T0.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T0.V z) → T'.FinRes → (∀ z : T.Q.c.F, τ (C.inc z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (evI pt (β k))) ≤ 1 := by
  first | exact @GlobalTheory.CoverLiftVal.le_one_at_lift | exact GlobalTheory.CoverLiftVal.le_one_at_lift | (intros; apply GlobalTheory.CoverLiftVal.le_one_at_lift <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_unitScalar_smul_coreIntegralAdelicForm_places : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)), κ.LastPos → ∀ (q : Ideal (𝓞 T.Q.c.F)), q.IsPrime → ∀ (P : Set (HeightOneSpectrum (𝓞 T.Q.c.F))), P.Finite → ∀ ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n {p | p.asIdeal = q}, ∃ t : 𝓞 T.Q.c.F, t ∉ q ∧ T.σ₀ (t : T.Q.c.F) • ψ ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n P := by
  first | exact @GlobalTheory.ScaleInt.smul_mem_baseInt | exact GlobalTheory.ScaleInt.smul_mem_baseInt | (intros; apply GlobalTheory.ScaleInt.smul_mem_baseInt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.referenceTuple_lifts_equivariant_rootOfUnity : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → M.lev = (O i).lev → (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) → Normal ℚ M.c'.F → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) → (∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e) → ∀ c₀ : M.c'.F, IsRoot1 ((c₀ : M.c'.F) : ℂ) → (∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (x x' : M.Cl' A.μ0 → VsV D i M.c'.F), (∀ k, M.io (x' k) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io (x k))) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M A.μ0 x f → (ta c₀ * c₀⁻¹)⁻¹ • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M A.μ0 x' ((ta c₀ * c₀⁻¹)⁻¹ • galRul hf f)) → ∃ ζ₁ : ℂ, IsRoot1 ζ₁ ∧ ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (y y' : (R.HV i A.μ0).H), (∀ h : GA D (Vc D i), ∃ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) ∧ (R.HV i A.μ0).e y (fin _ h) = M.c0' x ∧ (R.HV i A.μ0).e y' (fin _ h) = M.c0' x') → ConjFun (O i) (κ i) τ 1 (fun g => ζ₁ * ph i * R.thF i A.μ0 y (v₀ i (sg0 D A)) g) (fun g => ζ₁ * ph i * R.thF i A.μ0 y' (v₀ i (sg0 D A)) g) := by
  first | exact @GlobalTheory.ConjRefLift.conjFun_lifts_root | exact GlobalTheory.ConjRefLift.conjFun_lifts_root | (intros; apply GlobalTheory.ConjRefLift.conjFun_lifts_root <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.conjugate_thetaLifts_isConjugateCuspExpansion : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ (y : (R.HV i t).H) (y' : (R.HV i t').H), ConjForm R i τ c t t' y y' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g) (fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g) := by
  first | exact @GlobalTheory.ConjClassSum.conj_lifts | exact GlobalTheory.ConjClassSum.conj_lifts | (intros; apply GlobalTheory.ConjClassSum.conj_lifts <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fullRank_thetaSeries_forms_of_rational_scalars : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ i, BaseTup Y i → (∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  first | exact @GlobalTheory.TieRank.rank_of_ties | exact GlobalTheory.TieRank.rank_of_ties | (intros; apply GlobalTheory.TieRank.rank_of_ties <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.uniformisedCover_invPhase_constants_normalised_dominant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ ph : ℂ, ‖ph‖ = 1 → BaseCc T R i hV ph → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → ∀ cc : C.U₂.Comp → ℂ, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) C.U₂ (castDict hV C.dict₂) (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i) cc → ∀ a, Dom a (κ i).n → ({ C with cc₂ := fun k => ph⁻¹ * cc k } : Cover T ((i : ℕ) + 1) T.σ₀).IsPinned a (κ i).n := by
  first | exact @GlobalTheory.CoverPinDom.isPinned_inv_mul | exact GlobalTheory.CoverPinDom.isPinned_inv_mul | (intros; apply GlobalTheory.CoverPinDom.isPinned_inv_mul <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitBall_finite_unramified_descent_complexPadic : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) → ∀ (F' : Type) [Field F'] [NumberField F'] [Algebra S.Ks F'] (φ' : F' →+* ℂ_[D.ntw.l i]), (∀ a, φ' (algebraMap S.Ks F' a) = embS S iC b a) → (∀ a : S.Ks, vLa (placeAt φ') (algebraMap S.Ks F' a) = vLa (placeAt (embS S iC b)) a) → ∀ (n : ℕ) (a : Fin n → F') (f : Fin n → NX.FmK S ((j : ℕ) + 1)), (∀ z : Pts YS iC b ((j : ℕ) + 1), ‖∑ s, φ' (a s) * valC z.1 (cuspOf YS fw j (f s) : T0.R ((j : ℕ) + 1))‖ ≤ 1) → ∃ (m : ℕ) (β : Fin m → F') (g : Fin m → NX.FmK S ((j : ℕ) + 1)), (∀ t, ‖φ' (β t)‖ ≤ 1) ∧ (∀ t, g t ∈ locBall YS fw iC b j) ∧ ∑ s, a s ⊗ₜ[S.Ks] f s = ∑ t, β t ⊗ₜ[S.Ks] g t := by
  first | exact @GlobalTheory.GeoTie.BallDescent.ball_descent | exact GlobalTheory.GeoTie.BallDescent.ball_descent | (intros; apply GlobalTheory.GeoTie.BallDescent.ball_descent <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj

theorem _root_.GlobalTheory.T.trace_integral_of_small_at_other_places : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ (m : ℕ) (y : Fin m → L), ∃ N : ℕ, ∀ b : 𝓞 L, (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal → b ∈ la'.asIdeal ^ N) → ∀ (T : CDVR), T.FinRes → ∀ (io : K →+* T.Fr) (e : ℕ), OverLa p T.V io e → ∀ x : Fin m → T.Fr, (∀ k, valV T.V (x k) ≤ 1) → (∀ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e' : ℕ) (τ : L →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T.V z) → T'.FinRes → (∀ z : K, τ (algebraMap K L z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (x k)) ≤ 1) → valV T.V (∑ k, io (Algebra.trace K L ((b : L) * y k)) * x k) ≤ 1 := by
  first | exact @GlobalTheory.TraceSmall.trace_le_one | exact GlobalTheory.TraceSmall.trace_le_one | (intros; apply GlobalTheory.TraceSmall.trace_le_one <;> assumption)
end
