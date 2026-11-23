module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle047
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle042
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdelicQuotientMeasure
public import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle027
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField GlobalTheory.IndefiniteRowSideFullHecke.AdelicQuotientClasses
open scoped ENNReal NNReal Pointwise Classical

namespace GlobalTheory.AutQuotCompare

section First

variable {H : Type} [Group H] (Γ : Subgroup H)

variable [MeasurableSpace H] (P P' : Measure H × Set H → Prop)

end First

section Haar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

end Haar

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (G : Matrix (Fin n) (Fin n) E)

variable {G}

end Adelic

section Transport

variable {H H' : Type} [Group H] [Group H'] [TopologicalSpace H] [TopologicalSpace H']
  {Γ : Subgroup H} {Γ' : Subgroup H'} (e : H ≃ₜ* H') (he : ∀ g, e g ∈ Γ' ↔ g ∈ Γ)


variable [MeasurableSpace H] [BorelSpace H] [MeasurableSpace H'] [BorelSpace H']

end Transport

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {G : Matrix (Fin n) (Fin n) E}
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  {Γ : Subgroup H}

def IsHaarPair (Γ : Subgroup H) (p : Measure H × Set H) : Prop :=
  p.1.IsHaarMeasure ∧ IsFundamentalDomain Γ p.2 p.1

end Main

section Split

open scoped Matrix

variable {R S ι : Type} [CommRing R] [CommRing S] (Φ : R ≃+* (ι → ℂ) × S) {n : ℕ}

def compAt (w : ι) : R →+* ℂ := (Pi.evalRingHom _ w).comp ((RingHom.fst _ _).comp Φ.toRingHom)

def compLast : R →+* S := (RingHom.snd _ _).comp Φ.toRingHom

theorem continuous_map {R R' : Type} [CommRing R] [CommRing R'] [TopologicalSpace R] [TopologicalSpace R']
    {φ : R →+* R'} (h : Continuous φ) : Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) φ) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map h, Units.continuous_coe_inv.matrix_map h⟩

variable [TopologicalSpace R] [TopologicalSpace S] (hc : Continuous Φ) (hc' : Continuous Φ.symm)
  {s : R →+* R} {s' : S →+* S} (hs : ∀ w z, compAt Φ w (s z) = starRingEnd ℂ (compAt Φ w z))
  (hs' : ∀ z, compLast Φ (s z) = s' (compLast Φ z)) {J : Matrix (Fin n) (Fin n) R}
  {A : ι → Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin n) S}
  (hA : ∀ w, Jᵀ.map (compAt Φ w) = A w) (hB : Jᵀ.map (compLast Φ) = B)

end Split

section Adeles

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem sigmaCompact_inf (F : Type) [Field F] [NumberField F] [Algebra F E] : SigmaCompactSpace (Ainf F ⊗[F] E) := by
  have : ∀ v : InfinitePlace F, SigmaCompactSpace v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isClosedEmbedding.sigmaCompactSpace
  have : SigmaCompactSpace (Ainf F) := inferInstanceAs (SigmaCompactSpace (∀ v : InfinitePlace F, v.Completion))
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Ainf F) _
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (Ainf F) (Ainf F ⊗[F] E)
  refine ⟨?_⟩
  rw [← hf.range_eq]
  exact isSigmaCompact_range (IsModuleTopology.continuous_of_linearMap f)

theorem exists_inf_equiv : ∃ Θ : Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E ≃+* (InfinitePlace E → ℂ),
    Continuous Θ ∧ Continuous Θ.symm ∧ (∀ x w, Θ (1 ⊗ₜ x) w = w.embedding x) ∧
      ∀ z w, Θ (GlobalTheory.AdLat.sg _ (IsCMField.complexConj E) z) w = starRingEnd ℂ (Θ z w) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.InfAdeleCM.infAdele_tensor_bijective (maximalRealSubfield E) E (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) inferInstance
    (IsCMField.complexEmbedding_complexConj E)
  choose θ hθ using h1
  obtain ⟨h3, h4, h5⟩ := h2 θ hθ
  have hinj : Function.Injective (fun w : InfinitePlace E => w.embedding) := fun v w h => by
    rw [← v.mk_embedding, ← w.mk_embedding]; exact congrArg _ h
  have hmem : ∀ τ : E →+* ℂ, τ ∈ Set.range (fun w : InfinitePlace E => w.embedding) ↔
      (InfinitePlace.mk τ).embedding = τ := fun τ =>
    ⟨fun ⟨w, hw⟩ => by rw [← hw]; simp only [InfinitePlace.mk_embedding], fun h => ⟨_, h⟩⟩
  have hb := h5 (Set.range fun w : InfinitePlace E => w.embedding) fun τ => by
    have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
      IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)
    rw [hmem, hmem, InfinitePlace.mk_conjugate_eq]
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · rw [h]; simp [hne.symm]
    · rw [h]; simp [hne]
  let f : Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E →+* (InfinitePlace E → ℂ) :=
    Pi.ringHom fun w => θ w.embedding
  have hf : Function.Bijective f :=
    (Equiv.arrowCongr (Equiv.ofInjective _ hinj).symm (Equiv.refl ℂ)).bijective.comp hb
  have hfc : Continuous f := continuous_pi fun w => h3 _
  have := sigmaCompact_inf E (maximalRealSubfield E)
  have : IsModuleTopology (Ainf (maximalRealSubfield E))
    (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) := ⟨rfl⟩
  have : IsTopologicalRing (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) :=
    IsModuleTopology.isTopologicalRing (Ainf (maximalRealSubfield E)) _
  have ho : IsOpenMap f := f.toAddMonoidHom.isOpenMap_of_sigmaCompact hf.2 hfc
  refine ⟨RingEquiv.ofBijective f hf, hfc, ?_, fun x w => (hθ _).1 x, fun z w => h4 _ z⟩
  exact ((RingEquiv.ofBijective f hf).toEquiv.toHomeomorphOfContinuousOpen hfc ho).symm.continuous

end Adeles

section Groups

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end Groups

section Record

open scoped Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} [IsCMField D.host.E] (V : HSp D)

omit [IsCMField D.host.E]

end Record

end GlobalTheory.AutQuotCompare
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CoverFrame

theorem exists_inverse_block {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (w : Fin g → Fin g → ℂ)
    (h : ∀ j, ∃ a : Fin (m (e j).1) → ℂ, ∑ i, a i • w (e.symm ⟨(e j).1, i⟩) = Pi.single j 1) :
    ∃ V : Matrix (Fin g) (Fin g) ℂ, IsUnit V.det ∧ (∀ j j', V j j' ≠ 0 → (e j).1 = (e j').1) ∧
      ∀ j, V *ᵥ w j = Pi.single j 1 := by
  classical
  choose a ha using h
  let cv : Fin g → Fin g → ℂ := fun j => ∑ i, a j i • Pi.single (e.symm ⟨(e j).1, i⟩) 1
  let Wm : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => w j i
  let V : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => cv j i
  have hW : ∀ j, Wm *ᵥ Pi.single j 1 = w j := fun j => by
    ext i; simp [Wm]
  have hV : ∀ j, V *ᵥ Pi.single j 1 = cv j := fun j => by
    ext i; simp [V]
  have hWV : Wm * V = 1 := by
    have : ∀ j, (Wm * V) *ᵥ Pi.single j 1 = Pi.single j 1 := fun j => by
      rw [← Matrix.mulVec_mulVec, hV, ← ha j]
      simp only [cv, Matrix.mulVec_sum, Matrix.mulVec_smul, hW]
    ext i j
    have h1 := congrFun (this j) i
    simpa [Matrix.one_apply, Pi.single_apply] using h1
  have hVW : V * Wm = 1 := mul_eq_one_comm.mp hWV
  refine ⟨V, Matrix.isUnit_det_of_left_inverse hWV, fun j j' hj => ?_, fun j => ?_⟩
  · by_contra hne
    apply hj
    simp only [V, cv, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Pi.single_eq_of_ne, smul_zero]
    intro hh
    apply hne
    rw [hh, Equiv.apply_symm_apply]
  · rw [← hW, Matrix.mulVec_mulVec, hVW, Matrix.one_mulVec]



theorem coverTri : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → CoverTri e F M := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hG hB hN y
  classical
  obtain ⟨k, P, hP, hy⟩ := F.onto y.x y.x_over
  obtain ⟨ht1, ht2, ht3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k P hP
  have hw : ∀ j : Fin g, ∃ w, IsDerivAt0 (fun z => (F.ex k P z).left) w (y.u (e j).1 (e j).2) := fun j =>
    (ht3 (y.u (e j).1 (e j).2) (by rw [hy]; exact y.tan _ _)).exists
  choose w hw using hw
  have hw' : ∀ τ (i : Fin (Dw.mult τ)),
      IsDerivAt0 (fun z => (F.ex k P z).left) (w (e.symm ⟨τ, i⟩)) (y.u τ i) := fun τ i => by
    have := hw (e.symm ⟨τ, i⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this
  have hsp : ∀ j, ∃ a : Fin (Dw.mult (e j).1) → ℂ, ∑ i, a i • w (e.symm ⟨(e j).1, i⟩) = Pi.single j 1 := by
    intro j
    obtain ⟨v, hv⟩ := (ht2 (Pi.single j 1)).exists
    have htan := ht1 _ _ hv
    have heig :=
      (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F k P hP (Pi.single j 1) v (e j).1 hv).2
        (fun j' hj' => by
          by_contra hne
          exact hj' (Pi.single_eq_of_ne (fun hh => hne (by rw [hh])) _))
    have htan' : IsTanAt y.x v := by rw [← hy]; exact htan
    obtain ⟨a, ha⟩ := (y.basis (e j).1 v htan' heig).exists
    have ha' : IsCombAt (F.u k P) (y.u (e j).1) (show Fin (Dw.mult (e j).1) → ℂ from a) v := by
      rw [hy]; exact ha
    have hd := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P hP _ (y.u (e j).1)
      (fun i => w (e.symm ⟨(e j).1, i⟩)) (hw' (e j).1) a v).1 ha'
    exact ⟨a, (ht3 v htan).unique hd hv⟩
  obtain ⟨V, hVu, hVt, hVw⟩ := exists_inverse_block e w hsp
  obtain ⟨P', hP', hP'e⟩ := GlobalTheory.PeriodLin.exists_period_mulVec E H (F.Di k) g _ P V hP hVu
    (fun j j' h => by rw [hVt j j' h])
  obtain ⟨-, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k P P'
    (LinearEquiv.refl _ _) V hP hP' (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩) (fun a => ⟨0, by simp⟩) hP'e
  obtain ⟨Pf, hPf, -, -, -, hon⟩ := GlobalTheory.T.exists_framePeriods_alt E H Dw l Xo c σ g e F r M hG hB hN k
  obtain ⟨x, hx, hxP⟩ := hon P' hP'
  have hy' : F.u k P' = y.x := hu.symm.trans hy
  refine ⟨k, ⟨x, hx⟩, P', fun a j => by rw [← hxP]; exact hPf x a j, hy', fun v hv τ i => ?_⟩
  have hyu : IsDerivAt0 (fun z => (F.ex k P' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i) := by
    have := (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k P hP k P' (Matrix.mulVecLin V) hP' hex
      _ _).1 (hw' τ i)
    rw [Matrix.mulVecLin_apply, hVw] at this
    exact this
  have hc := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P' hP' _ (v τ)
    (fun i => Pi.single (e.symm ⟨τ, i⟩) 1) (hv τ) (Pi.single i 1) (y.u τ i)).2 (by
      rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp),
        Pi.single_eq_same, one_smul]
      exact hyu)
  refine ⟨(Pi.single i 1 : Fin (Dw.mult τ) → ℂ), ?_, fun j hj => Pi.single_eq_of_ne (M := fun _ => ℂ) hj.ne' _, ?_⟩
  · show IsUnit ((Pi.single i 1 : Fin (Dw.mult τ) → ℂ) i)
    rw [Pi.single_eq_same]; exact isUnit_one
  · rw [← hy']; exact hc

end GlobalTheory.CoverFrame
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ModuliChart

theorem exists_sec_of_secOn {X X' S S' : Scheme.{0}} {p : X ⟶ S} {p' : X' ⟶ S'} {t : S' ⟶ S} {F : X' ⟶ X}
    (hF : IsPullback F p' p t) {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull F))
    {V : S.Opens} (hV : ∀ y, t y ∈ V) {θ : ∀ i, Γ(X, p ⁻¹ᵁ V ⊓ L.U i)} (hθ : θ ∈ secOn L (p ⁻¹ᵁ V))
    (hne : ∀ y ∈ V, ∃ (g : X) (i : L.ι), p g = y ∧ g ∈ X.basicOpen (θ i)) :
    ∃ th : L'.Sec, ∀ y : S', ∃ x : X', p' x = y ∧ x ∈ Out.nonzeroLocus th := by
  obtain ⟨w, hw⟩ := hw
  have hFV : ∀ y : X', p (F y) ∈ V := fun y => by
    rw [← Scheme.Hom.comp_apply, hF.w, Scheme.Hom.comp_apply]; exact hV _
  have le : ∀ j, F ⁻¹ᵁ L.U j ≤ F ⁻¹ᵁ (p ⁻¹ᵁ V ⊓ L.U j) := fun j y hy => ⟨hFV y, hy⟩
  have val : ∀ (y : X') j, F y ∈ L.U j → gs (𝟙 X') y _ ((F.appLE _ _ (le j)).hom (θ j)) =
      (F.stalkMap y).hom (gs (𝟙 X) (F y) _ (θ j)) := fun y j h => by
    rw [gs_appLE F _ _ (le j) (𝟙 X') y h, Category.id_comp, gs_stalkMap F y _ (le j h)]
  obtain ⟨th, hth⟩ := sec_down ((isGen_iff w).1 hw) hL hL' (fun j => (F.appLE _ _ (le j)).hom (θ j))
    fun y j j' h h' => by
      rw [val y j h, val y j' h', LBGerm.gs_secOn hθ (F y) j j' (hFV y) h h', map_mul]
      congr 1
      have := PushInv.gm_comp F (𝟙 X) y (L.U j ⊓ L.U j') ⟨h, h'⟩ (L.g j j')
      rw [Category.comp_id] at this
      exact this.symm
  refine ⟨th, fun y => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := hne (t y) (hV y)
  obtain ⟨x, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback hF g y hg
  obtain rfl : F x = g := h₁
  obtain ⟨k, hk⟩ := exists_chart hL' x
  have hm : F x ∈ p ⁻¹ᵁ V ⊓ L.U i := X.basicOpen_le _ hi
  refine ⟨x, h₂, (SectionBaseChange.mem_nonzeroLocus th _).2 ⟨k, hk, ?_⟩⟩
  have e := hth _ (𝟙 _) x i k hm.2 hk
  rw [val x i hm.2] at e
  have hu : IsUnit (gs (𝟙 X) (F x) _ (θ i)) := by
    rw [gs_eq (𝟙 X) (F x) _ hm]
    exact (X.mem_basicOpen _ _ hm).1 hi
  exact isUnit_of_mul_isUnit_right (e ▸ hu.map (F.stalkMap x).hom)

theorem exists_away_point {R : Type} [CommRing R] (p : PrimeSpectrum R) {r : R} (hr : r ∉ p.asIdeal) :
    ∃ q : PrimeSpectrum (Localization.Away r), spMap (algebraMap R (Localization.Away r)) q = p := by
  have h : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  exact h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_pull {B : Type} [CommRing B] {b : Base l B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} (s' : S' ⟶ Sp B)
    (f : S' ⟶ S) (h : f ≫ s = s') (o : Obj D l b s) : ∃ o' : Obj D l b s', Nonempty (ObjMap o' o f) :=
  ObjPull.objPull_of_pol pol_pull E H D l B B b b (RingHom.id B) S S' s s' f rfl rfl
    (h.trans ((Category.comp_id _).symm.trans (congrArg (s' ≫ ·) (Spec.map_id _).symm))) o

theorem objMap_comp {B : Type} [CommRing B] {b : Base l B} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    {s'' : S'' ⟶ Sp B} {o : Obj D l b s} {o' : Obj D l b s'} {o'' : Obj D l b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (m' : ObjMap o'' o' f') (m : ObjMap o' o f) : Nonempty (ObjMap o'' o (f' ≫ f)) := by
  obtain ⟨n, -⟩ := ((ObjMaps.id_comp_cancel E H D l B B B b b b S S' S'' s s' s'' o o' o'').2 f f' m).1 m'
  exact ⟨n⟩

set_option synthInstance.maxHeartbeats 200000 in
theorem exists_eigen_chart (c : Coeff l) {g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H D.p D.q ty)
    {R : Type} [CommRing R] (j : c.F →+* R)
    (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (p : Sp R) :
    ∃ (R' : Type) (_ : CommRing R') (f : R →+* R')
      (o' : Obj D l (baseKA l) (spMap (f.comp j) ≫ spMap (IntermediateField.inclusion c.le).toRingHom))
      (v : Fin g → (epsR R' ⟶ o'.t.G)), IsOpenImmersion (spMap f) ∧ p ∈ Set.range (spMap f) ∧
      Nonempty (ObjMap o' o (spMap f)) ∧ IsLieBasis v ∧
      ∀ i a, (v i ≫ o'.t.act.act a).left =
        spMap (epsScaleR (f.comp j ⟨ty i (a : E), c.conj (ty i) a⟩)) ≫ (v i).left := by
  obtain ⟨r, hr, v₀, hv₀⟩ := LieLoc.lie_locally_free R o.t.G _ (ObjDim.smoothOfRelativeDimension o) p
  obtain ⟨p₁, hp₁⟩ := exists_away_point p hr
  let R₁ := Localization.Away r
  let f₁ : R →+* R₁ := algebraMap R R₁
  obtain ⟨o₁, ⟨m₁⟩⟩ := exists_pull
    (spMap (f₁.comp j) ≫ spMap (IntermediateField.inclusion c.le).toRingHom) (spMap f₁)
    (by rw [spMap_comp j f₁, Category.assoc]) o
  obtain ⟨e, he, -⟩ := grpPullback_iso m₁.cart (isGrpPullback_pullback o.t.G (spMap f₁))
  have hv₁ : IsLieBasis (fun i => v₀ i ≫ e.inv) := Chart.isLieBasis_iso e (by
    simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using hv₀)
  obtain ⟨r', hr', Hv⟩ := exists_isLieBasis_eigen E H D l c g ty hty R₁ (f₁.comp j) o₁ _ _ hv₁ p₁
  obtain ⟨p₂, hp₂⟩ := exists_away_point p₁ hr'
  let R₂ := Localization.Away r'
  let f₂ : R₁ →+* R₂ := algebraMap R₁ R₂
  obtain ⟨o₂, ⟨m₂⟩⟩ := exists_pull
    (spMap ((f₂.comp f₁).comp j) ≫ spMap (IntermediateField.inclusion c.le).toRingHom) (spMap f₂)
    (by rw [RingHom.comp_assoc, spMap_comp (f₁.comp j) f₂, Category.assoc]) o₁
  obtain ⟨v, hv, hev⟩ := Hv o₂.t ⟨m₂.toSABMap⟩
  have i₁ : IsOpenImmersion (spMap f₁) := inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))))
  have i₂ : IsOpenImmersion (spMap f₂) := inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap R₁ (Localization.Away r')))))
  refine ⟨R₂, inferInstance, f₂.comp f₁, o₂, v, ?_, ?_, ?_, hv, hev⟩
  · rw [spMap_comp f₁ f₂]; infer_instance
  · refine ⟨p₂, ?_⟩
    rw [spMap_comp f₁ f₂]
    exact (congrArg (spMap f₁) hp₂).trans hp₁
  · rw [spMap_comp f₁ f₂]; exact objMap_comp m₂ m₁

theorem exists_chart_eigenframe : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → ∀ x : Xo.XF c, ∃ (R : Type) (_ : CommRing R) (_ : Algebra c.F R) (jR : Sp R ⟶ Xo.XF c) (o : Obj D l (baseKA l) (spMap (algebraMap c.F R) ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (v : Fin g → (epsR R ⟶ o.t.G)) (th : o.t.PP.L.Sec), Algebra.FiniteType c.F R ∧ IsReduced R ∧ IsOpenImmersion jR ∧ x ∈ Set.range jR ∧ jR ≫ pullback.snd _ _ = spMap (algebraMap c.F R) ∧ Nonempty (ObjMap o Xo.univ (jR ≫ pullback.fst _ _)) ∧ IsLieBasis v ∧ (∀ i a, (v i ≫ o.t.act.act a).left = spMap (epsScaleR (algebraMap c.F R ⟨ty i (a : E), c.conj (ty i) a⟩)) ≫ (v i).left) ∧ (∀ y : Sp R, ∃ x : o.t.G.left, o.t.G.hom x = y ∧ x ∈ Out.nonzeroLocus th) ∧ (∀ s : o.t.PP.L.Sec, ∃! a : R, ∀ i, s.f i = constFn o.t.G.hom _ a * th.f i) := by
  intro hS E _ _ _ H D l Xo c g ty hty x
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  let π : Xo.XF c ⟶ Xo.X := pullback.fst _ _
  let σ : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  have hσ : Smooth σ := inferInstanceAs (Smooth (pullback.snd Xo.s _))
  have hred : AlgebraicGeometry.IsReduced (Xo.XF c) :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ σ hσ).1
  obtain ⟨V, hV, θ, hθ, -, hne⟩ := PushInv.pushInvertible hS Xo.X (Obj.toPolAV Xo.univ) (π x)
  obtain ⟨B, j₀, hj₀, ⟨p, hp⟩, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := Xo.XF c) (x := x) (U := π ⁻¹ᵁ V) hV
  let j : c.F →+* B := (Spec.preimage (j₀ ≫ σ)).hom
  have hj : j₀ ≫ σ = spMap j := (Spec.map_preimage (j₀ ≫ σ)).symm
  obtain ⟨o₀, ⟨m₀⟩⟩ := exists_pull (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom) (j₀ ≫ π)
    (by rw [← hj, Category.assoc, Category.assoc]; exact congrArg (j₀ ≫ ·) pullback.condition) Xo.univ
  obtain ⟨R, _, f, o, v, hf, ⟨q, hq⟩, ⟨m₁⟩, hv, hev⟩ := exists_eigen_chart c hty j o₀ p
  obtain ⟨m⟩ := objMap_comp m₁ m₀
  let jR : Sp R ⟶ Xo.XF c := spMap f ≫ j₀
  have hjR : IsOpenImmersion jR := IsOpenImmersion.comp (spMap f) j₀
  have hs : jR ≫ σ = spMap (f.comp j) := by
    rw [spMap_comp j f, ← hj]; exact Category.assoc _ _ _
  have hL : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨th, hth⟩ := exists_sec_of_secOn m.cart.1 Xo.univ.t.PP.isLB o.t.PP.isLB hL (V := V)
    (fun y => hsub ⟨spMap f y, rfl⟩) hθ hne
  letI : Algebra c.F R := (f.comp j).toAlgebra
  refine ⟨R, inferInstance, inferInstance, jR, o, v, th, ?_, ?_, hjR, ⟨q, ?_⟩, hs, ?_, hv, hev, hth,
    SectionBaseChange.generates hS (Obj.toPolAV Xo.univ) m.cart.1 o.t.PP.isLB hL th hth⟩
  · have h : LocallyOfFiniteType (spMap (f.comp j)) := by rw [← hs]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := CommRingCat.ofHom (f.comp j))).1 h
  · have h : AlgebraicGeometry.IsReduced (Sp R) := isReduced_of_isOpenImmersion jR
    exact (affine_isReduced_iff (CommRingCat.of R)).1 h
  · exact (congrArg j₀ hq).trans hp
  · have e : jR ≫ π = spMap f ≫ j₀ ≫ π := Category.assoc _ _ _
    exact (congrArg (fun u => Nonempty (ObjMap o Xo.univ u)) e).mpr ⟨m⟩

end GlobalTheory.ModuliChart
end
end
