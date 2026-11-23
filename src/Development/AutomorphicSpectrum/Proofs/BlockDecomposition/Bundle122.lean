module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle106
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle108
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle109
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle033

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

theorem _root_.GlobalTheory.T.archimedean_fundamental_domain_integers : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ li : Measure (Ainf F), IsStdInf li → ∃ D K₀ : Set (Ainf F), MeasurableSet D ∧ IsCompact K₀ ∧ D ⊆ K₀ ∧ li D = 1 ∧ ∀ y : Ainf F, ∃! a : 𝓞 F, y - algebraMap F (Ainf F) (a : F) ∈ D := by
  first | exact @GlobalTheory.CompanionTheory.Equi.exists_bounded_infDomain | exact GlobalTheory.CompanionTheory.Equi.exists_bounded_infDomain | (intros; apply GlobalTheory.CompanionTheory.Equi.exists_bounded_infDomain <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

theorem _root_.GlobalTheory.T.local_haar_measure_singleton : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → lam {0} = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.isStdV_measure_singleton_zero | exact GlobalTheory.CompanionTheory.Mass.MeanV.isStdV_measure_singleton_zero | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.isStdV_measure_singleton_zero <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen

section Abstract

variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V]

def twRel (ρ : Representation ℂ Γ V) (ψ : Γ →* ℂˣ) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ (γ : Γ) (v : V), w = ρ γ v - (ψ γ : ℂ) • v}

end Abstract

section Fibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

def fibChar (μ : kˣ →* ℂˣ) : GL a k × (GL c k × GL d k) →* ℂˣ :=
  (detChar a (μ⁻¹ * absPow k (((Fintype.card c : ℂ) + Fintype.card d) / 2))).comp (MonoidHom.fst _ _) *
    (detChar c (μ * absPow k (-(Fintype.card a : ℂ) / 2) * absPow k (-(Fintype.card d : ℂ) / 2))).comp
      ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)) *
    (detChar d (μ * absPow k (-(Fintype.card a : ℂ) / 2) * absPow k ((Fintype.card c : ℂ) / 2))).comp
      ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _))

def fibBase (κ : ℕ) :
    Representation ℂ (GL a k × GL c k) (SB (RankIn (k := k) (a := a) (b := c) {κ})) :=
  sbRep (fun x γ => ⟨act x.1 γ, by rw [rank_act]; exact x.2⟩)
    (fun x => Subtype.ext (act_one x.1)) (fun x γ δ => Subtype.ext (act_mul x.1 γ δ))
    (fun γ => ((continuous_act γ).comp continuous_subtype_val).subtype_mk _)

def fibRep (μ : kˣ →* ℂˣ) (κ : ℕ) :
    Representation ℂ (GL a k × (GL c k × GL d k)) (SB (RankIn (k := k) (a := a) (b := c) {κ})) :=
  twist ((fibBase a c κ).comp ((MonoidHom.id _).prodMap (MonoidHom.fst _ _))) (fibChar a c d μ)

theorem fibRep_apply (μ : kˣ →* ℂˣ) (κ : ℕ) (g : GL a k) (p₁ : GL c k) (p₂ : GL d k)
    (φ : SB (RankIn (k := k) (a := a) (b := c) {κ})) (y : RankIn (k := k) (a := a) (b := c) {κ}) :
    (fibRep a c d μ κ (g, p₁, p₂) φ).1 y = (fibChar a c d μ (g, p₁, p₂) : ℂ) *
      φ.1 ⟨act y.1 (g, p₁), by rw [rank_act]; exact y.2⟩ := rfl

def rightRep (κ : ℕ) :
    Representation ℂ (GL a k) (SB (RankIn (k := k) (a := a) (b := c) {κ})) :=
  (fibBase a c κ).comp (MonoidHom.inl _ _)

end Fibre

end GlobalTheory.CompanionTheory.ThetaGLLen
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.PerfBase

section Transfer

variable {X : Scheme.{0}}

theorem res_val {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) : (res h x).val = rs X h x.val := rfl

def secMap {A B : LB X} (q : B.ι → A.ι) (hq : ∀ b, B.U b ≤ A.U (q b))
    (hg : ∀ b b', res (inf_le_inf (hq b) (hq b')) (A.g (q b) (q b')) = B.g b b') (s : LB.Sec A) : LB.Sec B where
  f := fun b => rs X (hq b) (s.f (q b))
  compat := fun b b' => by
    have h := congrArg (rs X (inf_le_inf (hq b) (hq b') : B.U b ⊓ B.U b' ≤ A.U (q b) ⊓ A.U (q b')))
      (s.compat (q b) (q b'))
    change rs X _ (rs X inf_le_left (s.f (q b))) =
      rs X _ ((A.g (q b) (q b')).val * rs X inf_le_right (s.f (q b'))) at h
    change rs X inf_le_left (rs X (hq b) (s.f (q b))) =
      (B.g b b').val * rs X inf_le_right (rs X (hq b') (s.f (q b')))
    rw [← hg, res_val]
    simp only [rs_rs, map_mul] at h ⊢
    exact h

theorem h1_vanishing_of_refinement {A B : LB X} (q : B.ι → A.ι) (hq : ∀ b, B.U b ≤ A.U (q b))
    (hg : ∀ b b', res (inf_le_inf (hq b) (hq b')) (A.g (q b) (q b')) = B.g b b') (hA : FirstCohomologyVanishes A) : FirstCohomologyVanishes B := by
  intro I V c hV hc φ hφ
  obtain ⟨ψ, hψ⟩ := hA I V (fun a => q (c a)) (fun a => (hV a).trans (hq _)) hc φ (by
    intro a b d
    have h := hφ a b d
    rw [← hg, res_val, rs_rs] at h
    exact h)
  refine ⟨ψ, fun a b => ?_⟩
  rw [hψ a b, ← hg (c a) (c b), res_val, rs_rs]

end Transfer

section PullPull

variable {X' Y Y₀ : Scheme.{0}} (M : LB Y₀) (π : Y ⟶ Y₀) (π' : X' ⟶ Y)

theorem le_unfold (j : (M.pull (π' ≫ π)).ι) :
    (M.pull (π' ≫ π)).U j ≤ ((M.pull π).pull π').U (fun _ => j) :=
  fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

theorem le_fold (j : ((M.pull π).pull π').ι) :
    ((M.pull π).pull π').U j ≤ (M.pull (π' ≫ π)).U (fun u => j u u) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) k

theorem g_pull_pull (j j' : ((M.pull π).pull π').ι)
    (h : ((M.pull π).pull π').U j ⊓ ((M.pull π).pull π').U j' ≤
      (π' ≫ π) ⁻¹ᵁ (M.U (j PUnit.unit PUnit.unit) ⊓ M.U (j' PUnit.unit PUnit.unit))) :
    ((M.pull π).pull π').g j j' = res h (pullU (π' ≫ π) _ (M.g (j PUnit.unit PUnit.unit) (j' PUnit.unit PUnit.unit))) := by
  refine (LB.lcg_pull (M.pull π) π' j j').trans ?_
  refine (congrArg (fun x => res (LB.wchart_pu_le (M.pull π) π' j j') (pullU π' _ x))
    (LB.lcg_pull M π (j PUnit.unit) (j' PUnit.unit))).trans ?_
  exact LB.pull_res_comp π' π _ _ _ _ _

theorem g_pull_comp (j j' : (M.pull (π' ≫ π)).ι)
    (h : (M.pull (π' ≫ π)).U j ⊓ (M.pull (π' ≫ π)).U j' ≤
      (π' ≫ π) ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    (M.pull (π' ≫ π)).g j j' = res h (pullU (π' ≫ π) _ (M.g (j PUnit.unit) (j' PUnit.unit))) :=
  LB.lcg_pull M (π' ≫ π) j j'

theorem hg_unfold (j j' : (M.pull (π' ≫ π)).ι) :
    res (inf_le_inf (le_unfold M π π' j) (le_unfold M π π' j'))
      (((M.pull π).pull π').g (fun _ => j) (fun _ => j')) = (M.pull (π' ≫ π)).g j j' := by
  refine (congrArg (res _) (g_pull_pull M π π' (fun _ => j) (fun _ => j')
    (fun y hy => ⟨Set.mem_iInter.1 (Set.mem_iInter.1 hy.1 PUnit.unit) PUnit.unit,
      Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit⟩))).trans ?_
  exact (LB.res_res _ _ _).trans (g_pull_comp M π π' j j'
    (fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩)).symm

theorem hg_fold (j j' : ((M.pull π).pull π').ι) :
    res (inf_le_inf (le_fold M π π' j) (le_fold M π π' j'))
      ((M.pull (π' ≫ π)).g (fun u => j u u) (fun u => j' u u)) = ((M.pull π).pull π').g j j' := by
  refine (congrArg (res _) (g_pull_comp M π π' (fun u => j u u) (fun u => j' u u)
    (fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩))).trans ?_
  exact (LB.res_res _ _ _).trans (g_pull_pull M π π' j j'
    (fun y hy => ⟨Set.mem_iInter.1 (Set.mem_iInter.1 hy.1 PUnit.unit) PUnit.unit,
      Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit⟩)).symm

theorem h1_vanishing_pull_comp (hH : FirstCohomologyVanishes ((M.pull π).pull π')) : FirstCohomologyVanishes (M.pull (π' ≫ π)) :=
  h1_vanishing_of_refinement (A := (M.pull π).pull π') (B := M.pull (π' ≫ π)) (fun j _ => j) (le_unfold M π π') (hg_unfold M π π') hH

def secPullPull : LB.Sec (M.pull (π' ≫ π)) ≃ LB.Sec ((M.pull π).pull π') where
  toFun := secMap (fun j u => j u u) (le_fold M π π') (hg_fold M π π')
  invFun := secMap (fun j _ => j) (le_unfold M π π') (hg_unfold M π π')
  left_inv := fun s => by
    obtain ⟨sf, hs⟩ := s
    simp only [secMap, LB.Sec.mk.injEq]
    funext j
    rw [rs_rs, rs_self]
  right_inv := fun s => by
    obtain ⟨sf, hs⟩ := s
    simp only [secMap, LB.Sec.mk.injEq]
    funext j
    rw [rs_rs, rs_self]

end PullPull

theorem perf_pull {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {Y₀ Y : Scheme.{0}}
    (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) (f : Y ⟶ Spec (CommRingCat.of R)) (π : Y ⟶ Y₀)
    (hπ : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (M₀ : LB Y₀) (_hM : M₀.IsLB) (P : Perf f₀ M₀) :
    Nonempty (Perf f (M₀.pull π)) := by
  have paste : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π' : X' ⟶ Y)
      (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π' f' f (Spec.map (CommRingCat.ofHom g)) →
      IsPullback (π' ≫ π) f' f₀ (Spec.map (CommRingCat.ofHom (g.comp φ))) := by
    intro R' _ g X' π' f' h
    have h' := h.paste_horiz hπ
    rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h'
  have hD₀ : ∀ (R' : Type) [CommRing R'] (g : R →+* R'), (P.D₀.map φ).map g = P.D₀.map (g.comp φ) :=
    fun _ _ _ => by ext; rfl
  have hD₁ : ∀ (R' : Type) [CommRing R'] (g : R →+* R'), (P.D₁.map φ).map g = P.D₁.map (g.comp φ) :=
    fun _ _ _ => by ext; rfl
  exact ⟨{
    a := P.a
    b := P.b
    c := P.c
    D₀ := P.D₀.map φ
    D₁ := P.D₁.map φ
    comp := by rw [← Matrix.map_mul, P.comp, Matrix.map_zero _ (map_zero φ)]
    I := P.I
    W := fun i => π ⁻¹ᵁ P.W i
    ch := fun i _ => P.ch i
    le := fun i => le_pull M₀ π (P.le i)
    cover := by
      refine top_unique fun y _ => ?_
      have hy : π y ∈ ⨆ i, P.W i := by rw [P.cover]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
    u := fun k i => (π.app (P.W i)).hom (P.u k i)
    sec := fun R' _ g X' π' f' h => by
      obtain ⟨E₀, hE⟩ := P.sec R' (g.comp φ) X' (π' ≫ π) f' (paste R' g X' π' f' h)
      refine ⟨(Equiv.subtypeEquivRight (fun v => by rw [hD₀])).trans (E₀.trans (secPullPull M₀ π π')),
        fun v i => ?_⟩
      refine Eq.trans ?_ (hE ⟨v.1, by rw [← hD₀]; exact v.2⟩ i)
      change rs X' _ (rs X' _ _) = _
      rw [rs_rs]
      rfl
    exact := fun R' _ g X' π' f' h hH w hw => by
      rw [hD₁] at hw
      obtain ⟨v, hv⟩ := P.exact R' (g.comp φ) X' (π' ≫ π) f' (paste R' g X' π' f' h)
        (h1_vanishing_pull_comp M₀ π π' hH) w hw
      exact ⟨v, by rw [hD₀]; exact hv⟩ }⟩

end GlobalTheory.CompanionTheory.PerfBase
end
end

section

open MeasureTheory Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi

noncomputable section
namespace GlobalTheory.CompanionTheory.CharacterBiduality

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem indicator_mem_SB {n : ℕ} (A : AddSubgroup (Fin n → k))
    (hAc : IsCompact (A : Set (Fin n → k))) (hAo : IsOpen (A : Set (Fin n → k))) :
    (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) ∈ SB (Fin n → k) := by
  have hcl : IsClopen (A : Set (Fin n → k)) := ⟨AddSubgroup.isClosed_of_isOpen A hAo, hAo⟩
  exact ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hcl).isLocallyConstant,
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _⟩

theorem fourier_sub_translate_eq_zero [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    (ψ : AddChar k Circle) (hψ : Continuous ψ) (μ : Measure (Fin n → k)) [μ.IsAddHaarMeasure]
    (A : AddSubgroup (Fin n → k)) (hAc : IsCompact (A : Set (Fin n → k)))
    (hAo : IsOpen (A : Set (Fin n → k))) (x : Fin n → k)
    (hx : ∀ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) → ψ (η ⬝ᵥ x) = 1) (y : Fin n → k) :
    ∫ z, ((A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) z -
        (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) (z + x)) * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 := by
  haveI := secondCountable k
  haveI := t2Space k
  set g : (Fin n → k) → ℂ := (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) with hgdef
  have hg : g ∈ SB (Fin n → k) := indicator_mem_SB A hAc hAo
  have hc : Continuous fun z : Fin n → k => (ψ (z ⬝ᵥ y) : ℂ) :=
    continuous_subtype_val.comp (hψ.comp (continuous_id.dotProduct continuous_const))
  have hi1 : Integrable (fun z => g z * (ψ (z ⬝ᵥ y) : ℂ)) μ :=
    (hg.1.continuous.mul hc).integrable_of_hasCompactSupport hg.2.mul_right
  have hgx : HasCompactSupport fun z => g (z + x) := hg.2.comp_homeomorph (Homeomorph.addRight x)
  have hi2 : Integrable (fun z => g (z + x) * (ψ (z ⬝ᵥ y) : ℂ)) μ :=
    ((hg.1.continuous.comp (continuous_id.add continuous_const)).mul hc).integrable_of_hasCompactSupport
      hgx.mul_right
  have e1 : ∫ z, g (z + x) * (ψ (z ⬝ᵥ y) : ℂ) ∂μ =
      (ψ (-(x ⬝ᵥ y)) : ℂ) * ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ := by
    have h := integral_add_right_eq_self (μ := μ) (fun w => g w * (ψ ((w - x) ⬝ᵥ y) : ℂ)) x
    simp only [add_sub_cancel_right] at h
    rw [h, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have hwx : (w - x) ⬝ᵥ y = w ⬝ᵥ y + -(x ⬝ᵥ y) := by rw [sub_dotProduct, sub_eq_add_neg]
    beta_reduce
    rw [hwx, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  simp only [sub_mul]
  rw [integral_sub hi1 hi2, e1]
  by_cases hy : ∀ a ∈ A, ψ (y ⬝ᵥ a) = 1
  · have h1 : ψ (x ⬝ᵥ y) = 1 := by rw [dotProduct_comm]; exact hx y hy
    have h2 : ψ (-(x ⬝ᵥ y)) = 1 := by rw [AddChar.map_neg_eq_inv, h1, inv_one]
    simp [h2]
  · push Not at hy
    obtain ⟨a, haA, hne⟩ := hy
    have h0 : ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 := by
      have h := integral_add_right_eq_self (μ := μ) (fun w => g w * (ψ (w ⬝ᵥ y) : ℂ)) a
      have h3 : ∫ z, g (z + a) * (ψ ((z + a) ⬝ᵥ y) : ℂ) ∂μ =
          (ψ (y ⬝ᵥ a) : ℂ) * ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        have hga : g (w + a) = g w := by
          by_cases hw : w ∈ A
          · simp [hgdef, Set.indicator, hw, A.add_mem hw haA]
          · have : w + a ∉ A := fun h => hw (by simpa using A.sub_mem h haA)
            simp [hgdef, Set.indicator, hw, this]
        simp only [hga, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, dotProduct_comm a y]
        ring
      rw [h3] at h
      have h4 : (1 - (ψ (y ⬝ᵥ a) : ℂ)) * ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 := by
        rw [sub_mul, one_mul, h, sub_self]
      refine (mul_eq_zero.1 h4).resolve_left fun h5 => hne (Circle.ext ?_)
      simpa using (sub_eq_zero.1 h5).symm
    simp [h0]

theorem exists_annihilator_ne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) →
    IsOpen (A : Set (Fin n → k)) → ∀ x : Fin n → k, x ∉ A →
    ∃ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) ∧ ψ (η ⬝ᵥ x) ≠ 1 := by
  intro k _ _ _ _ ψ hψ h1 n A hAc hAo x hxA
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := secondCountable k
  haveI := t2Space k
  let μ : Measure (Fin n → k) := Measure.addHaar
  set g : (Fin n → k) → ℂ := (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) with hgdef
  have hg : g ∈ SB (Fin n → k) := indicator_mem_SB A hAc hAo
  have hgx : (fun z => g (z + x)) ∈ SB (Fin n → k) :=
    ⟨hg.1.comp_continuous (continuous_id.add continuous_const),
      hg.2.comp_homeomorph (Homeomorph.addRight x)⟩
  have hf : (fun z => g z - g (z + x)) ∈ SB (Fin n → k) := (SB (Fin n → k)).sub_mem hg hgx
  obtain ⟨s, hs⟩ := fourier_inversion_pi μ hc hf
  have hz : ∀ y : Fin n → k, ∫ z, (g z - g (z + x)) * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 :=
    fourier_sub_translate_eq_zero ψ hψ μ A hAc hAo x hcon
  simp only [hz, integral_zero] at hs
  have hpos : ∀ r : kˣ, 0 < μ.real (box (Fin n) r) := fun r => by
    have h1 : (0 : Fin n → k) ∈ box (Fin n) r := fun i _ => by simp [cball]
    have h2 : 0 < μ (box (Fin n) r) := (isOpen_box r).measure_pos μ ⟨0, h1⟩
    exact ENNReal.toReal_pos h2.ne' (isCompact_box r).measure_lt_top.ne
  have hne : ((μ.real (box (Fin n) s) * μ.real (box (Fin n) (c * s⁻¹)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos (hpos s) (hpos _)).ne'
  have h0 : g 0 - g (0 + x) = 0 := (mul_eq_zero.mp hs.symm).resolve_left hne
  have hg0 : g 0 = 1 := Set.indicator_of_mem (SetLike.mem_coe.2 A.zero_mem) _
  have hgx0 : g (0 + x) = 0 := by
    rw [zero_add]
    exact Set.indicator_of_notMem (fun h => hxA h) _
  rw [hg0, hgx0] at h0
  simp at h0

end GlobalTheory.CompanionTheory.CharacterBiduality
end
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZFun

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

theorem isSmooth_smInd (H : Subgroup G) (σ : Representation ℂ H W) : IsSmooth (smInd H σ) := by
  intro f
  have e : {g : G | smInd H σ g f = f} = {g : G | ind H σ g f.1 = f.1} := by
    ext g
    exact Subtype.ext_iff
  rw [e]
  exact f.2

theorem isSmooth_cInd (H : Subgroup G) (σ : Representation ℂ H W) : IsSmooth (cInd H σ) := by
  intro f
  have e : {g : G | cInd H σ g f = f} = {g : G | smInd H σ g f.1 = f.1} := by
    ext g
    exact Subtype.ext_iff
  rw [e]
  exact isSmooth_smInd H σ f.1

end GlobalTheory.CompanionTheory.BZFun
end

section

open Matrix Topology Filter

theorem _root_.GlobalTheory.T.lie_algebra_star_closed_bracket : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → ∀ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) → (∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) ∧ ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤 := by
  first | exact @GlobalTheory.CompanionTheory.LieStable.lieAlg_stable | exact GlobalTheory.CompanionTheory.LieStable.lieAlg_stable | (intros; apply GlobalTheory.CompanionTheory.LieStable.lieAlg_stable <;> assumption)
end

section

open Matrix Topology Filter

theorem _root_.GlobalTheory.T.local_exp_product_decomposition : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → ∀ 𝔤 𝔨 𝔟 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) → (∃ V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤) → 𝔨 ≤ 𝔤 → 𝔟 ≤ 𝔤 → 𝔤 ≤ 𝔨 ⊔ 𝔟 → ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G → ∃ X ∈ 𝔨, ∃ Y ∈ 𝔟, g = NormedSpace.exp X * NormedSpace.exp Y := by
  first | exact @GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_mul_exp_of_isLinRed | exact GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_mul_exp_of_isLinRed | (intros; apply GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_mul_exp_of_isLinRed <;> assumption)
end

section

open Matrix Topology Filter

theorem _root_.GlobalTheory.T.cartan_local_to_global : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, (∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G → ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id) → ∀ g ∈ G, ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.LinRedFactor.factor_of_local | exact GlobalTheory.CompanionTheory.LinRedFactor.factor_of_local | (intros; apply GlobalTheory.CompanionTheory.LinRedFactor.factor_of_local <;> assumption)
end

section

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch


theorem _root_.GlobalTheory.T.hua_determinant_integrable_of_lt : ∀ (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s → ∀ ν : Measure (hermC n), ν.IsAddHaarMeasure →
  Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.hua_integrable | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.hua_integrable | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.hua_integrable <;> assumption)
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

theorem _root_.GlobalTheory.T.hermitian_vector_values_card : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (∀ c : E, τ c = c → c ≠ 0 → (Nat.card {v : V // B.h v v = c} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 - ((ε : ℝ) / q) ^ m)) ∧ (Nat.card {v : V // B.h v v = 0} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 + ((q : ℝ) - 1) * ((ε : ℝ) / q) ^ m) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.Sphere.count | exact GlobalTheory.CompanionTheory.UnrDens.Sphere.count | (intros; apply GlobalTheory.CompanionTheory.UnrDens.Sphere.count <;> assumption)
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

theorem _root_.GlobalTheory.T.gauss_sum_hermitian_norm_level_one : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → ∀ (a : R), σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ 1, ψ 1 (Ideal.Quotient.mk (lev ϖ 1) a * (barσ σ ϖ hR.fix_ϖ 1 w * w))) = (ε : ℂ) * q := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.gauss_level_one | exact GlobalTheory.CompanionTheory.SiegLoc.gauss_level_one | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.gauss_level_one <;> assumption)
end
