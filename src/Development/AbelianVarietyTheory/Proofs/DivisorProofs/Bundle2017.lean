module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefinitePairClassesFixedMinpolyDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticMemClosureGenerators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

namespace GlobalTheory.TowU

theorem card_two_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ]
    {B : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → AF F} (d : Darboux B κ) :
    Fintype.card κ * 2 = Fintype.card α * Fintype.card β * Module.finrank F E := by
  haveI : Nontrivial (AF F) := (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  haveI : FiniteDimensional F E := Module.Finite.right ℚ F E
  have h1 := d.e.finrank_eq
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_matrix,
    Module.finrank_baseChange] at h1
  omega

noncomputable def reidx {F : Type} [Field F] [NumberField F] {κ κ' : Type} (e : κ' ≃ κ) :
    ((κ' → AF F) × (κ' → AF F)) ≃ₗ[AF F] ((κ → AF F) × (κ → AF F)) where
  toFun p := (p.1 ∘ e.symm, p.2 ∘ e.symm)
  invFun p := (p.1 ∘ e, p.2 ∘ e)
  map_add' p q := rfl
  map_smul' c p := rfl
  left_inv p := by ext i <;> simp
  right_inv p := by ext i <;> simp

noncomputable def reindexD {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (d : Darboux B κ') (e : κ' ≃ κ) : Darboux B κ where
  e := d.e.trans (reidx e)
  form w w' := by
    rw [d.form]
    have h : ∀ u v : κ' → AF F, (u ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = u ⬝ᵥ v := fun u v => by
      simp only [dotProduct, Function.comp_apply]
      exact e.symm.sum_comp (fun j => u j * v j)
    simp only [LinearEquiv.trans_apply]
    exact (congrArg₂ (· - ·) (h _ _) (h _ _)).symm

theorem reindexD_e {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (d : Darboux B κ') (e : κ' ≃ κ) (w : W) :
    (reindexD d e).e w = ((d.e w).1 ∘ e.symm, (d.e w).2 ∘ e.symm) := rfl

theorem realised_of_sp {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    [DecidableEq κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (hg : gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0) :
    ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
      IsOp2 ψ (GlobalTheory.AdelicSvN.act g) S S' := by
  have hcl := GlobalTheory.sympGen F κ g hg
  clear hg
  induction hcl using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with (⟨A, hA, rfl⟩ | ⟨C, hC, rfl⟩) | hx
    · exact GlobalTheory.T.exists_darbouxOperators_levi_and_double F ψ hψ κ A hA
    · exact GlobalTheory.T.exists_darbouxChangeOperatorWithDouble_lowerUnipotent F ψ hψ κ C hC
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact GlobalTheory.T.weylElement_realised_by_fourierTransforms F ψ hψ κ
  | one =>
    obtain ⟨S, S', h⟩ := (GlobalTheory.T.darbouxChange_realised_comp_and_reindex F ψ hψ).2 κ κ (Equiv.refl κ)
    refine ⟨S, S', ?_⟩
    have : GlobalTheory.AdelicSvN.act (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) = fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ Equiv.refl κ, w.2 ∘ Equiv.refl κ) := by
      funext w; rw [GlobalTheory.AdelicSvN.act_one]; rfl
    rw [this]; exact h
  | mul x y _ _ hx hy =>
    obtain ⟨S, S', hS⟩ := hx
    obtain ⟨T, T', hT⟩ := hy
    have : GlobalTheory.AdelicSvN.act (x * y) = GlobalTheory.AdelicSvN.act x ∘ GlobalTheory.AdelicSvN.act (R := AF F) y := by
      funext w; exact GlobalTheory.AdelicSvN.act_mul x y w
    rw [this]
    exact ⟨S ∘ₗ T, T' ∘ₗ S', (GlobalTheory.T.darbouxChange_realised_comp_and_reindex F ψ hψ).1 κ κ κ _ _ T T' S S' hT hS⟩

theorem darboux_change : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsStd ψ → ∀ (α β κ κ' : Type) [Fintype α] [Fintype β] [Fintype κ] [Fintype κ'] (B : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → AF F) (d : Darboux B κ) (d' : Darboux B κ'), IsRat d → IsRat d' → ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (fun w => d'.e (d.e.symm w)) S S' := by
  intro F E _ _ _ _ _ σ _ ψ hψ α β κ κ' _ _ _ _ B d d' hd hd'
  have hc := card_two_eq F E d
  have hc' := card_two_eq F E d'
  have hκ : Fintype.card κ' = Fintype.card κ := by omega
  let e : κ' ≃ κ := Fintype.equivOfCardEq hκ
  let d'' := reindexD d' e
  have hd'' : IsRat d'' := fun x => by
    obtain ⟨y, z, h⟩ := hd' x
    refine ⟨y ∘ e.symm, z ∘ e.symm, ?_⟩
    rw [reindexD_e, h]; rfl
  obtain ⟨g, hg, hgd⟩ := GlobalTheory.RatDarboux.exists_rat_symplectic F E α β κ B d d'' hc hd hd''
  obtain ⟨S, S', hS⟩ := realised_of_sp ψ hψ g hg
  obtain ⟨T, T', hT⟩ := (GlobalTheory.T.darbouxChange_realised_comp_and_reindex F ψ hψ).2 κ κ' e
  have hs : (fun w => d'.e (d.e.symm w)) = (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) ∘ GlobalTheory.AdelicSvN.act g := by
    funext w
    have := hgd (d.e.symm w)
    simp only [LinearEquiv.apply_symm_apply] at this
    rw [Function.comp_apply, ← this, reindexD_e]
    ext i <;> simp
  rw [hs]
  exact ⟨T ∘ₗ S, S' ∘ₗ T', (GlobalTheory.T.darbouxChange_realised_comp_and_reindex F ψ hψ).1 κ κ κ' _ _ S S' T T' hS hT⟩

end GlobalTheory.TowU
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.finite_definitePair_classes_fixed_minpoly_degree_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      ∀ P0 : Polynomial G.F, {q : GlobalTheory.LKDef.DCls G | (Quot.out q).pol = P0 ∧ Irreducible (Quot.out q).pol ∧
        (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  first | (exact @GlobalTheory.LKDefFin.finite_classes_of_pol) | (exact GlobalTheory.LKDefFin.finite_classes_of_pol) | (intros; apply GlobalTheory.LKDefFin.finite_classes_of_pol <;> assumption)
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.inner_thetaFunctions_reading_testFunction_frames : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∃ G : Frame X.Ψ r → Frame X.Ψ r → ℂ, ∀ x x' : Frame X.Ψ r, IsONFr X x → IsONFr X x' → G x x' ≠ 0 ∧ (∀ u : GA D W, G (frMove θ W hr X u x) (frMove θ W hr X u x') = G x x') ∧ ∀ v : TF V.rank g, GlobalTheory.SW.IsSB v → v ≠ 0 → ∃ c : ℂ, c ≠ 0 ∧ ∀ y y' : Frame X.Ψ r, IsONFr X y → IsONFr X y' → ∀ (f f' : WO V W → ℂ) (κ κ' : ℂ), IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → Reads θ V W hr X bas idx f (κ • v) y → Reads θ V W hr X bas idx f' (κ' • v) y' → ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∫ w in 𝓕, f w * conj (f' w) ∂μ = κ * conj κ' * (c * G y y') := by
  first | exact @GlobalTheory.AdTh.inner_of_reads | exact GlobalTheory.AdTh.inner_of_reads | (intros; apply GlobalTheory.AdTh.inner_of_reads <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
namespace GlobalTheory.LowRow

theorem lamLow_of_weak : ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → AdelC R.toRealDat F.lv2 → PrimeToHost R.toRealDat A3.A.μ0 → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  intro hCR D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s b C CH hOk hsep hC hEx prim hph hstd fw hbar hio hpins hrow0 htie hsz hlow hnum hAd hPH
  obtain ⟨hcore, hok, hlinks⟩ := GlobalTheory.T.splitPart_baseLinks_of_primitiveRows R F s hOk hsep hC hEx prim hph
  have hgal : ∀ i, GalOut R.toRealDat i 1 := fun i =>
    hCR D G Pl0 T0 A3.A T R.toRealDat F.lv2 κ v₀ O 1 (GlobalTheory.Core5.of_core hcore) hstd fw hbar hio prim.unif hpins i (by
      have h1 := htie i prim.unif (hrow0 i)
      simp only [hph] at h1
      simpa using h1)
  have hext : ∀ i σ, ∃ v : (R.toRealDat.MW i σ).Vec, IsExtVec (R.toRealDat.MW i σ) v := fun i σ => ⟨v₀ i σ, (fw.hv₀ i σ).1⟩
  have htop := GlobalTheory.T.liftAdjoint_eigenvalue_lower_bound_base_embedding R.toRealDat F.lv2 s b hAd hcore hok hPH hsz
  have hform := GlobalTheory.T.rationalLift_lowerBound_off_basePlace R.toRealDat F.lv2 s b hAd hgal hcore hok hext prim.unif hlinks hPH hsz
  have h0 := GlobalTheory.T.log_liftEigenvalue_lowerBound_basePlace R F b hC prim.thmA prim.posScal htop hlow
  have h1 := GlobalTheory.T.log_liftEigenvalue_lowerBound_otherPlaces R F b hC hph prim.posScal prim.scalConj hform hlow
  intro j p v
  have hn := hnum j
  by_cases hv : v = A3.A.v0
  · subst hv
    have := h0 j p
    exact le_trans hn this
  · have := h1 j p v hv
    exact le_trans hn this

end GlobalTheory.LowRow
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.admissibleRep_hasTrace_finiteAdelicPureTensorFunction : ∀ (D : D7) (V : HSp D) (ν : Measure (GfC V)) [ν.IsHaarMeasure] (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → (∃ c, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c) ∧ ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) → IsCompact (K : Set (GfC V)) → (∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g) → ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) 0 → ∃ x : W, x ≠ 0 ∧ ∀ k ∈ K, σ k x = x := by
  first | exact @GlobalTheory.FinTrace.hasTrace_finFn | exact GlobalTheory.FinTrace.hasTrace_finFn | (intros; apply GlobalTheory.FinTrace.hasTrace_finFn <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.gradedLine_potential_hessian_det_own_row : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m), (G (bsL ε w) x.1).PosDef → MContDiffAt 2 (fun v => G v x.1) (bsL ε w) → Fintype.card {j : Cell m // j.root = x} = m x.1 - 1 - x.2 ∧ (Matrix.of fun a b : {j : Cell m // j.root = x} => -leviForm (cellPot ε G x) w (coordVec (ε.symm (.inr a.1))) (coordVec (ε.symm (.inr b.1)))).det = (((G (bsL ε w) x.1).det.re / (leadMinor (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2).re / grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 ^ ((m x.1 - 1 - x.2 : ℕ) + 1) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.FlagCell2.row_levi_det | exact GlobalTheory.FlagCell2.row_levi_det | (intros; apply GlobalTheory.FlagCell2.row_levi_det <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.BearsCell

variable {ι : Type} {m : ι → ℕ}

theorem upM_map {K K' : Type} [Field K] [Field K'] (v : K → K') (h0 : v 0 = 0) (h1 : v 1 = 1) (u : Cell m → K) :
    (upM u).map v = upM fun j => v (u j) := by
  funext τ
  ext a b
  simp only [Mat.map, upM, upU, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp [h0, h1]

theorem det_upM {K : Type} [Field K] (u : Cell m → K) (τ : ι) : (upM u τ).det = 1 :=
  (GlobalTheory.FlagCell2.lowMul_upU_leadMinor_ne_zero K (m τ) _ 1 (fun _ _ h => Matrix.one_apply_ne h.ne) (by simp)).1

theorem exists_lu {K K' : Type} [Field K] [Field K'] {O : Subring K} (v : K → K') (ψ : O →+* K')
    (hv : ∀ x : O, v x = ψ x) (hu : ∀ x : O, ψ x ≠ 0 → (x : K) ≠ 0 ∧ (x : K)⁻¹ ∈ O) {g : Mat m K} (hg : Par 0 O g)
    {y₀ : Cell m → K'} (hP : Par m ⊤ (upM y₀ * (g.map v)⁻¹)) :
    ∃ (u : Cell m → K) (b : Mat m K), Par m O b ∧ g = b * upM u ∧ ∀ j, v (u j) = y₀ j := by
  have hgv := hg.map_of v ψ hv
  have hy : ∀ τ, (upM y₀ τ).det ≠ 0 := fun τ => (det_upM y₀ τ).trans_ne one_ne_zero
  have e : g.map v = (upM y₀ * (g.map v)⁻¹)⁻¹ * upM y₀ := by
    rw [Mat.mul_inv_rev, Mat.inv_inv hgv.det_ne, mul_assoc, Mat.inv_mul hy, mul_one]
  have hmin : ∀ τ (k : ℕ), ((g τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val).det ≠ 0 ∧
      (((g τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val).det)⁻¹ ∈ O := fun τ k => by
    let N : Matrix {a : Fin (m τ) // (a : ℕ) < k} {a : Fin (m τ) // (a : ℕ) < k} O := fun a b => ⟨_, (hg τ).1 a.1 b.1⟩
    have e1 : (N.det : K) = ((g τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val).det :=
      O.subtype.map_det N
    have e2 : ψ.mapMatrix N =
        (g.map v τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val := by
      ext a b
      exact (hv (N a b)).symm
    rw [← e1]
    refine hu _ ?_
    rw [ψ.map_det, e2, e]
    exact (GlobalTheory.FlagCell2.lowMul_upU_leadMinor_ne_zero K' (m τ) _ _ (fun i j h => (hP.inv τ).2.2.2 i j i.2 h) (hP.inv.det_ne τ)).2 k
  choose y b h1 h2 h3 h4 using fun τ => GlobalTheory.FlagLU.exists_lu_subring K O (m τ) (g τ) (hg τ).1 (hmin τ)
  have hgb : g = b * upM (fun j : Cell m => y j.1 j.2) := funext h4
  have hd : ∀ τ, (b τ).det = (g τ).det := fun τ => by
    rw [hgb, Pi.mul_apply, Matrix.det_mul, det_upM, mul_one]
  have hb : Par m O b := fun τ => ⟨h2 τ, hd τ ▸ (hg τ).2.1, hd τ ▸ (hg τ).2.2.1, fun i j _ h => h3 τ i j h⟩
  have hU : Par 0 O (upM fun j : Cell m => y j.1 j.2) := by
    have := (hb.inv.mono (k' := 0) (fun _ => Nat.zero_le _) le_rfl).mul hg
    rwa [hgb, ← mul_assoc, Mat.inv_mul hb.det_ne, one_mul] at this
  refine ⟨_, b, hb, hgb, fun j => ?_⟩
  have e3 : g.map v = Mat.map b v * upM fun j : Cell m => v (y j.1 j.2) := by
    rw [← upM_map v ((hv 0).trans (map_zero ψ)) ((hv 1).trans (map_one ψ)), ← Par.map_mul_of hb hU v ψ hv, ← hgb]
  have e4 : upM y₀ = (upM y₀ * (g.map v)⁻¹ * Mat.map b v) * upM fun j : Cell m => v (y j.1 j.2) := by
    rw [mul_assoc, ← e3, mul_assoc, Mat.inv_mul hgv.det_ne, mul_one]
  have hc := hP.mul (hb.map_of v ψ hv)
  exact (congrFun (GlobalTheory.FlagCell2.upU_unique_of_lower K' (m j.1) _ _ _ (fun i k h => (hc j.1).2.2.2 i k i.2 h) (congrFun e4 j.1)) j.2).symm

theorem bears_iff : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (K : Type) [Field K] (p : Sp K ⟶ Y.X), A ∈ E.S (f (p (IsLocalRing.closedPoint K))) → ∀ y₀ : Cell m → K, Bears E' φ A (upM y₀) p ↔ ∃ u : Cell m → Y.Fn, upM u * A.map φ ∈ E'.S (p (IsLocalRing.closedPoint K)) ∧ ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  intro F _ X Y ι _ m E E' φ f hf A K _ p hA y₀
  have hd : ∀ σ, (A.map φ σ).det ≠ 0 := fun σ =>
    (Mat.det_map A (φ : X.Fn →+* Y.Fn) σ).trans_ne ((map_ne_zero _).2 (Fr.det_ne hA σ))
  have hr := GlobalTheory.ZH.RatModel.range_eq_singleton (M := ratOf Y) p (IsLocalRing.closedPoint K)
  constructor
  · rintro ⟨A', hA', hP⟩
    obtain ⟨u, b, hb, hg, hu⟩ := exists_lu ((ratOf Y).val p) (GlobalTheory.ZH.RatModel.valHom (M := ratOf Y) p _ hr)
      (fun _ => rfl) (fun x hx => (GlobalTheory.ZH.RatModel.isUnit_O_iff x).1
        ((GlobalTheory.ZH.RatModel.val_ne_zero_iff (M := ratOf Y) hr x).1 hx)) (hf.sub _ A' hA' A hA) hP
    refine ⟨u, (Fr.mem_iff hA').2 ?_, hu⟩
    have e : upM u * A.map φ * A'⁻¹ = b⁻¹ := by
      have e1 : upM u = b⁻¹ * (A' * (A.map φ)⁻¹) := by
        rw [hg, ← mul_assoc, Mat.inv_mul hb.det_ne, one_mul]
      rw [e1, mul_assoc b⁻¹, mul_assoc A', Mat.inv_mul hd, mul_one, mul_assoc, Mat.mul_inv (Fr.det_ne hA'), mul_one]
    rw [e]
    exact hb.inv
  · rintro ⟨u, hu, hy⟩
    refine ⟨_, hu, ?_⟩
    rw [mul_assoc, Mat.mul_inv hd, mul_one,
      upM_map ((ratOf Y).val p) (GlobalTheory.ZH.RatModel.val_zero (M := ratOf Y) p)
        (GlobalTheory.ZH.RatModel.val_one (M := ratOf Y) p), show (fun j => (ratOf Y).val p (u j)) = y₀ from funext hy,
      Mat.mul_inv fun τ => (det_upM y₀ τ).trans_ne one_ne_zero]
    exact Par.one

end GlobalTheory.FlagCell2.BearsCell
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.WeilExGen

theorem exists_isWeil : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ M : Model σ X W, M.IsGood B.ψ →
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → ∃ om, M.IsWeil B.ψ χX χW om :=
  fun h => h.weilRepresentationExists

end GlobalTheory.WeilExGen
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SurjAtPlaceV

open GlobalTheory.LeviAtPlace

theorem surj_at_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (g' : GL (Fin a) (Fv F v)), ∃ g ∈ UAt σ G.V (evFin F v), (mat g).map (piW t) = g'.1 := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t g'
  have h := hTr.base.cm
  have hJ : IsUnit (G.V.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hV.sig (InfinitePlace.mk φ))
    have h1 : G.V.J.det ≠ 0 := fun e => h0 (by
      rw [show G.V.J.map _ = RingHom.mapMatrix _ G.V.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show G.V.J.map t = (t : E →+* Fv F v).mapMatrix G.V.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  refine ⟨leviHom h t G.V.J hJ hTr.geo.hV.herm g', lift_sub_one_at v _, ?_⟩
  rw [leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, pairMat_fst]

end GlobalTheory.SurjAtPlaceV
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SkewLevi

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem locMat_unitary_skew (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit (J.map t).det) (skew : ∀ i j, σ (J j i) = -J i j) (g : GL (Fin n) (Fv F v)) :
    (LeviAtPlace.locMat h t J g)ᵀ * J.map (inclR (Fv F v)) * (LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ) =
      J.map (inclR (Fv F v)) := by
  have hJl : ∀ τ : E →ₐ[F] Fv F v, (J.map (inclR (Fv F v))).map (splitProj τ) = J.map τ := fun τ =>
    Matrix.ext fun i j => by
      simp only [Matrix.map_apply]; exact splitProj_inclR τ (J i j)
  have hs1 : ((LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ)).map (splitProj t) = conjComp t J g := by
    rw [Matrix.map_map]
    have : (splitProj t ∘ sigR (Fv F v) σ) = splitProj (t.comp σ) := funext fun y => (splitProj_comp t σ y).symm
    rw [this, LeviAtPlace.locMat, pairMat_snd]
  have hs2 : ((LeviAtPlace.locMat h t J g).map (sigR (Fv F v) σ)).map (splitProj (t.comp σ)) = g := by
    rw [Matrix.map_map]
    have : (splitProj (t.comp σ) ∘ sigR (Fv F v) σ) = splitProj t := funext fun y => splitProj_comp_sigR h t y
    rw [this, LeviAtPlace.locMat, pairMat_fst]
  have hJs : J.map (t.comp σ) = -(J.map t)ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, AlgHom.comp_apply, Matrix.neg_apply]
    rw [skew j i, map_neg]
  refine mat_split_ext h t ?_ ?_
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs1, LeviAtPlace.locMat, pairMat_fst, conjComp]
    set Jt := J.map t
    set A : Matrix (Fin n) (Fin n) (Fv F v) := ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))
    calc (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * Jt * (Jt⁻¹ * Aᵀ * Jt)
        = (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * (Jt * Jt⁻¹) * Aᵀ * Jt := by simp only [Matrix.mul_assoc]
      _ = (A * (g : Matrix (Fin n) (Fin n) (Fv F v)))ᵀ * Jt := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one, Matrix.transpose_mul]
      _ = Jt := by
          rw [show A * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 from Units.inv_mul g, Matrix.transpose_one,
            Matrix.one_mul]
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs2, LeviAtPlace.locMat, pairMat_snd, conjComp, hJs]
    set Jt := J.map t
    set A : Matrix (Fin n) (Fin n) (Fv F v) := ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))
    calc (Jt⁻¹ * Aᵀ * Jt)ᵀ * -Jtᵀ * (g : Matrix (Fin n) (Fin n) (Fv F v))
        = -(Jtᵀ * A * (Jt * Jt⁻¹)ᵀ * (g : Matrix (Fin n) (Fin n) (Fv F v))) := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_neg,
            Matrix.neg_mul]
      _ = -(Jtᵀ * (A * (g : Matrix (Fin n) (Fin n) (Fv F v)))) := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc]
      _ = -Jtᵀ := by rw [show A * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 from Units.inv_mul g, Matrix.mul_one]

theorem surj_at_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (h' : GL (Fin (a + a')) (Fv F v)), ∃ h ∈ UAt σ G.W (evFin F v), (mat h).map (piW t) = h'.1 := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t h'
  have h := hTr.base.cm
  have hJ : IsUnit (G.W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hW.sig (InfinitePlace.mk φ))
    have h1 : G.W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show G.W.J.map _ = RingHom.mapMatrix _ G.W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show G.W.J.map t = (t : E →+* Fv F v).mapMatrix G.W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  refine ⟨⟨adelicGL h t G.W.J hJ h', lift_unitary v σ G.W.J _
    (locMat_unitary_skew h t G.W.J hJ hTr.geo.hW.skew h')⟩, lift_sub_one_at v _, ?_⟩
  change (lift v (LeviAtPlace.locMat h t G.W.J h')).map (piW t) = h'.1
  have key : (lift v (LeviAtPlace.locMat h t G.W.J h')).map (piW t) =
      (LeviAtPlace.locMat h t G.W.J h').map (splitProj t) := by
    conv_rhs => rw [← compFin_lift v (LeviAtPlace.locMat h t G.W.J h'), Matrix.map_map]
    rfl
  rw [key]
  exact pairMat_fst h t _ _

end GlobalTheory.SkewLevi
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.eigen_intertwiner_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := by
  first | exact @GlobalTheory.ThK.EvNeZero.exists_ne_zero | exact GlobalTheory.ThK.EvNeZero.exists_ne_zero | (intros; apply GlobalTheory.ThK.EvNeZero.exists_ne_zero <;> assumption)
end
