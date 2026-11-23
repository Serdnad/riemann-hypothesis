module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle018
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle354
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle288
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianIsometryBaseChange
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormClassesIffConjUnitaryTorusEllipticElements
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle286
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLatticeOfRationalMemCompletionAllPlaces
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TestFnCusp

theorem hypH_of_noFixed {D : D7} {V : HSp D} (T : TypeDataG V) (h : NoFixed T) :
    GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ := by
  intro a ha har
  obtain ⟨v, hv⟩ := h.2 a ha har
  refine ⟨v, fun y hy => hv y fun g hg => hy g ?_⟩
  intro i j hij
  by_contra hc
  exact hij (hg i j hc)

theorem isCuspidalOp_tensor : (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.IsCuspidalOp V μ (tensor D.sp.cm.sig V.gram fa ff) := by
  intro hCO hPC D V lam S M T U μa μf μ _ _ fa ff hTD
  obtain ⟨hodd, -, -, hnf, hμ, ha, hb⟩ := hTD
  haveI : ∀ w, (μa w).IsHaarMeasure := hμ.haar_arch
  haveI : ∀ v, (μf v).IsHaarMeasure := hμ.haar_loc
  have hT : IsTestFnG M T U μa μf (tensor D.sp.cm.sig V.gram fa ff) := ⟨fa, ff, ha, hb, rfl⟩
  have hf : tensor D.sp.cm.sig V.gram fa ff ∈ CcGA V := hT.isPureTensor.2
  have hU := hPC.2 D V hodd S M T (hypH_of_noFixed T hnf) U μa μf _ hT
  refine hCO D V μ _ hf ?_ ?_
  · intro 𝔉 h𝔉 ν hν x y
    exact ((hU 𝔉 h𝔉).1 ν x y).2
  · intro 𝔉 h𝔉 ν hν x y
    exact ((hU 𝔉 h𝔉).2 ν x y).2

end GlobalTheory.TestFnCusp

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
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.TypeHypForms


open GlobalTheory.SmGL in
theorem unipBlock_subset_radicalTwo {k : Type} [Field k] {a b r : ℕ} (h : a + b = r) :
    GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.unipBlock k r a ⊆ (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.radicalTwo k h : Set (GL (Fin r) k)) := by
  intro g hg
  rw [SetLike.mem_coe, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.radicalTwo, mem_unipRad]
  refine ⟨(mem_parab_two k).2 fun j i => ?_, ?_⟩
  · have hj := j.isLt
    have hi := i.isLt
    rw [hg (stdSum h (.inr j)) (stdSum h (.inl i)) (by simp only [stdSum_inl, stdSum_inr]; omega),
      Matrix.one_apply_ne]
    intro he
    have := congrArg Fin.val he
    simp only [stdSum_inl, stdSum_inr] at this
    omega
  · rintro (_ | _) i j
    · have hj := j.isLt
      have hi := i.isLt
      show (g : Matrix (Fin r) (Fin r) k) (stdSum h (.inl i)) (stdSum h (.inl j)) = (1 : Matrix (Fin a) (Fin a) k) i j
      rw [hg _ _ (by simp only [stdSum_inl, stdSum_inr]; omega)]
      simp only [Matrix.one_apply, (stdSum h).injective.eq_iff, Sum.inl.injEq]
    · have hj := j.isLt
      have hi := i.isLt
      show (g : Matrix (Fin r) (Fin r) k) (stdSum h (.inr i)) (stdSum h (.inr j)) = (1 : Matrix (Fin b) (Fin b) k) i j
      rw [hg _ _ (by simp only [stdSum_inl, stdSum_inr]; omega)]
      simp only [Matrix.one_apply, (stdSum h).injective.eq_iff, Sum.inr.injEq]

theorem noRadicalFixed_of_noFixed {D : D7} {V : HSp D} (T : TypeDataG V) (hT : NoFixed T) :
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.NoRadicalFixed T := by
  intro a b h ha hb
  obtain ⟨v, hv⟩ := hT.2 a ha (by omega)
  refine ⟨v, (Submodule.eq_bot_iff _).2 fun y hy => hv y fun g hg => ?_⟩
  have := hy ⟨g, unipBlock_subset_radicalTwo h hg⟩
  simpa using this

theorem hypH_of_noFixed {D : D7} {V : HSp D} (T : TypeDataG V) (h : NoFixed T) :
    GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ := by
  intro a ha har
  obtain ⟨v, hv⟩ := h.2 a ha har
  refine ⟨v, fun y hy => hv y fun g hg => hy g ?_⟩
  intro i j hij
  by_contra hc
  exact hij (hg i j hc)

theorem hypH_and_noRadicalFixed : ∀ (D : D7) (V : HSp D) (T : TypeDataG V), NoFixed T → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.NoRadicalFixed T :=
  fun _ _ T h => ⟨hypH_of_noFixed T h, noRadicalFixed_of_noFixed T h⟩

end GlobalTheory.TypeHypForms

end
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEllMeas

open GlobalTheory.RestrMeas

theorem isHaarProd_map_all {X X' W V : Type} {Ya Ya' : W → Type} {Yf Yf' : V → Type} [Fintype W]
    [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X] [BorelSpace X]
    [Group X'] [TopologicalSpace X'] [IsTopologicalGroup X'] [MeasurableSpace X'] [BorelSpace X']
    [∀ w, Group (Ya w)] [∀ w, TopologicalSpace (Ya w)] [∀ w, IsTopologicalGroup (Ya w)]
    [∀ w, MeasurableSpace (Ya w)] [∀ w, BorelSpace (Ya w)]
    [∀ w, Group (Ya' w)] [∀ w, TopologicalSpace (Ya' w)] [∀ w, IsTopologicalGroup (Ya' w)]
    [∀ w, MeasurableSpace (Ya' w)] [∀ w, BorelSpace (Ya' w)]
    [∀ v, Group (Yf v)] [∀ v, TopologicalSpace (Yf v)] [∀ v, IsTopologicalGroup (Yf v)]
    [∀ v, MeasurableSpace (Yf v)] [∀ v, BorelSpace (Yf v)]
    [∀ v, Group (Yf' v)] [∀ v, TopologicalSpace (Yf' v)] [∀ v, IsTopologicalGroup (Yf' v)]
    [∀ v, MeasurableSpace (Yf' v)] [∀ v, BorelSpace (Yf' v)]
    {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K : ∀ v, Subgroup (Yf v)}
    {pa' : ∀ w, X' →* Ya' w} {pf' : ∀ v, X' →* Yf' v} {K' : ∀ v, Subgroup (Yf' v)}
    {μa : ∀ w, Measure (Ya' w)} {μf : ∀ v, Measure (Yf' v)} {ν : Measure X'}
    (h : IsHaarProd pa' pf' K' μa μf ν) (e : X' ≃ₜ* X) (ea : ∀ w, Ya' w ≃ₜ* Ya w) (ef : ∀ v, Yf' v ≃ₜ* Yf v)
    (ha : ∀ w x, pa w (e x) = ea w (pa' w x)) (hf : ∀ v x, pf v (e x) = ef v (pf' v x))
    (hK : ∀ v, IsOpen (K v : Set (Yf v))) (hKK : ∀ᶠ v in cofinite, ∀ t, ef v t ∈ K v ↔ t ∈ K' v) :
    IsHaarProd pa pf K (fun w => (μa w).map (ea w)) (fun v => (μf v).map (ef v)) (ν.map e) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have ma : ∀ w s, (μa w).map (ea w) s = μa w (ea w ⁻¹' s) := fun w s =>
    (ea w).toHomeomorph.toMeasurableEquiv.map_apply s
  have mf : ∀ v s, (μf v).map (ef v) s = μf v (ef v ⁻¹' s) := fun v s =>
    (ef v).toHomeomorph.toMeasurableEquiv.map_apply s
  have m : ∀ s, ν.map e s = ν (e ⁻¹' s) := fun s => e.toHomeomorph.toMeasurableEquiv.map_apply s
  obtain ⟨S₀, hS⟩ := exists_finset_of_eventually (h4.1.and hKK)
  refine ⟨fun w => (ea w).isHaarMeasure_map _, fun v => (ef v).isHaarMeasure_map _, e.isHaarMeasure_map _,
    isCylProd_of_large (K := fun v => (K v : Set (Yf v))) (fun v => (hK v).measurableSet) S₀ (fun v hv => ?_)
      (fun _ _ => rfl) fun S hs A B hA hB => ?_⟩
  · rw [mf, ← (hS v hv).1]
    exact congrArg _ (Set.ext (hS v hv).2)
  · simp only [ma, mf, m]
    rw [← h4.2 S (fun v hv => (hS v fun h' => hv (hs h')).1) _ _
      (fun w => (map_continuous (ea w)).measurable (hA w)) fun v hv => (map_continuous (ef v)).measurable (hB v hv)]
    refine congrArg ν (Set.ext fun x => ?_)
    simp only [mem_preimage, mem_cyl, ha, hf]
    exact and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun v hv =>
      (hS v fun h' => hv (hs h')).2 _

theorem isFundamentalDomain_map {T C : Type} [Group T] [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    [Group C] [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] (e : T ≃ₜ* C) {Γ : Subgroup T}
    {Γ' : Subgroup C} (h : ∀ t, e t ∈ Γ' ↔ t ∈ Γ) {μ : Measure T} {D : Set T} (hD : IsFundamentalDomain Γ D μ) :
    IsFundamentalDomain Γ' (e '' D) (μ.map e) ∧ μ.map e (e '' D) = μ D := by
  refine ⟨hD.image_of_equiv e.toEquiv ?_ (subEquiv e h).symm.toEquiv fun g x => ?_, ?_⟩
  · exact (MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv
      ⟨(map_continuous e).measurable, rfl⟩).quasiMeasurePreserving
  · change e (e.symm g * x) = g * e x
    rw [map_mul, e.apply_symm_apply]
  · rw [show μ.map e (e '' D) = μ (e ⁻¹' (e '' D)) from e.toHomeomorph.toMeasurableEquiv.map_apply _,
      e.injective.preimage_image]

theorem hasOrbInt_comap_congr {H : Type} [Group H] [MeasurableSpace H] {γ γ' : H} (h : γ = γ') (m μ : Measure H)
    (f : H → ℂ) (c : ℂ) : HasOrbInt μ γ (m.comap Subtype.val) f c ↔ HasOrbInt μ γ' (m.comap Subtype.val) f c := by
  subst h
  rfl

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

theorem mapH_diagH {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {k k' : Type} [CommRing k] [Algebra F k] [CommRing k']
    [Algebra F k'] (ψ : k →ₐ[F] k') (g : GRat σ J) : mapH σ J ψ (diagH σ J k g) = diagH σ J k' g := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  change Algebra.TensorProduct.map ψ (AlgHom.id F E) ((1 : k) ⊗ₜ[F] g.1.1 i j) = (1 : k') ⊗ₜ[F] g.1.1 i j
  simp

theorem diagH_surjective {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Function.Surjective (diagH σ J F) := by
  intro g
  let l : F ⊗[F] E →+* E := (Algebra.TensorProduct.lid F E).toRingEquiv.toRingHom
  have hl : ∀ y, (1 : F) ⊗ₜ[F] l y = y := fun y => (Algebra.TensorProduct.lid F E).symm_apply_apply y
  have hl' : ∀ y, l ((1 : F) ⊗ₜ[F] y) = y := fun y => (Algebra.TensorProduct.lid F E).apply_symm_apply y
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapU (sigR F σ) (σ : E →+* E) l (fun y => ?_) (JR F J) J
    (Matrix.ext fun i j => hl' _) g, Subtype.ext (Units.ext (Matrix.ext fun i j => hl _))⟩
  conv_rhs => rw [← hl y]
  exact (hl' (σ (l y))).symm

variable [NumberField F] [NumberField E] {σ}

theorem exists_equiv (hσ : IsCMExt F E σ) {r : ℕ} {P : PPol σ r} {J : Matrix (Fin r) (Fin r) E} (hJ : IsHermND σ J)
    {k : Type} [CommRing k] [Algebra F k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    {x : plusUnits P k} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)} (h : IsIsom P k J x.1.1 φ)
    {γ : HA k σ J} (hγ : gam h = γ) :
    ∃ e : Tor P k ≃ₜ* cent γ, (∀ t, (e t).1 = torEmb h t) ∧ ∀ (dt : Measure (Tor P k)) (x' : plusUnits P k)
      (φ' : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) (h' : IsIsom P k J x'.1.1 φ'), gam h' = γ →
      ∀ μ f c, HasOrbInt μ (gam h') (centMeas h' dt) f c ↔ HasOrbInt μ γ (dt.map e) f c := by
  subst hγ
  obtain ⟨e, he, hm⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure F E σ hσ r r P J hJ k x φ h
  refine ⟨e, he, fun dt x' φ' h' hγ μ f c => ?_⟩
  have h1 : torEmb h' = torEmb h := MonoidHom.ext fun t => by
    simpa using (GlobalTheory.TrEll.cls_conj_torus F E σ hσ r r P J hJ k x φ h x' φ' h').2.2.1 1 (by simpa using hγ) t
  rw [← hm, centMeas, centMeas, h1]
  exact hasOrbInt_comap_congr hγ _ _ _ _

theorem exists_isCentProd_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → ∃ ea ef e, IsCentProd L (ratEmb σ J γ) ea ef e ∧ (∃ 𝓣, IsFundamentalDomain ((ratPts σ J).subgroupOf (cent (ratEmb σ J γ))) 𝓣 e ∧ e 𝓣 = torVol P dt) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin r → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), gam h = proj σ J v (ratEmb σ J γ) → ∀ μ f c, HasOrbInt μ (gam h) (centMeas h (dtf v)) f c ↔ HasOrbInt μ (proj σ J v (ratEmb σ J γ)) (ef v) f c) ∧ ∀ (w : InfinitePlace F) (x : plusUnits P w.Completion) (φ : (w.Completion ⊗[F] Fld P) ≃ₗ[w.Completion ⊗[F] E] (Fin r → w.Completion ⊗[F] E)) (h : IsIsom P w.Completion J x.1.1 φ), gam h = projArch σ J w (ratEmb σ J γ) → ∀ μ f c, HasOrbInt μ (gam h) (centMeas h (dta w)) f c ↔ HasOrbInt μ (projArch σ J w (ratEmb σ J γ)) (ea w) f c := by
  intro F E _ _ _ _ _ σ hσ r P J hJ L _ γ hP dta dtf dt hdt
  obtain ⟨P', hP', _, x₀, φ₀, h₀, -, hγ₀⟩ := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hσ r J hJ).2 γ (hP ▸ P.2.2.1)
  obtain rfl : P = P' := Subtype.ext (hP.symm.trans hP')
  obtain ⟨xA, φA, hA, -, hγA, htA⟩ := GlobalTheory.TrEll.BaseChg.exists_isom_baseChange F E σ hσ r r P J hJ F (AF F) (Algebra.ofId F (AF F)) x₀ φ₀ h₀
  rw [hγ₀, mapH_diagH] at hγA
  replace hγA : gam hA = ratEmb σ J γ := hγA
  choose xf φf hf _ hγf htf using fun v : HeightOneSpectrum (𝓞 F) =>
    GlobalTheory.TrEll.BaseChg.exists_isom_baseChange F E σ hσ r r P J hJ (AF F) (Fv F v) (evFin F v) xA φA hA
  choose xa φa ha _ hγa hta using fun w : InfinitePlace F =>
    GlobalTheory.TrEll.BaseChg.exists_isom_baseChange F E σ hσ r r P J hJ (AF F) w.Completion (evInf F w) xA φA hA
  rw [hγA] at hγf hγa
  replace hγf : ∀ v, gam (hf v) = proj σ J v (ratEmb σ J γ) := hγf
  replace hγa : ∀ w, gam (ha w) = projArch σ J w (ratEmb σ J γ) := hγa
  haveI : T2Space (AF F) := by
    haveI : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space (∀ w : InfinitePlace F, w.Completion))
    haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := inferInstanceAs (T2Space (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite))
    exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  obtain ⟨e, he, -⟩ := exists_equiv hσ hJ hA hγA
  choose ef hef hof using fun v => exists_equiv hσ hJ (hf v) (hγf v)
  choose ea hea hoa using fun w => exists_equiv hσ hJ (ha w) (hγa w)
  refine ⟨fun w => (dta w).map (ea w), fun v => (dtf v).map (ef v), dt.map e, ?_, ?_,
    fun v x φ h hγ => hof v _ x φ h hγ, fun w x φ h hγ => hoa w _ x φ h hγ⟩
  · refine isHaarProd_map_all hdt e ea ef (fun w t => Subtype.ext ?_) (fun v t => Subtype.ext ?_)
      (restrGroup_cent L _).isOpen_K ?_
    · rw [hea]
      exact (congrArg (projArch σ J w) (he t)).trans (hta w t).symm
    · rw [hef]
      exact (congrArg (proj σ J v) (he t)).trans (htf v t).symm
    · filter_upwards [GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local F E σ hσ r P J hJ L, eventually_proj_mem_stabLoc σ J L (ratEmb σ J γ)]
        with v h1 h2 t
      rw [Subgroup.mem_subgroupOf, hef]
      exact h1.2.2.1 _ _ (hf v) (hγf v ▸ h2) t
  · have := hdt.2.2.1
    have hΓ : ∀ t, e t ∈ (ratPts σ J).subgroupOf (cent (ratEmb σ J γ)) ↔ t ∈ ratPts (star' P) (one₁ P) := by
      intro t
      rw [Subgroup.mem_subgroupOf, ← range_ratEmb, ← range_ratEmb]
      constructor
      · rintro ⟨δ, hδ⟩
        have h1 : δ * γ = γ * δ := ratEmb_injective σ J (by
          rw [map_mul, map_mul, hδ]; exact mem_cent.1 (e t).2)
        letI : TopologicalSpace F := ⊥
        haveI : DiscreteTopology F := ⟨rfl⟩
        obtain ⟨e₀, he₀, -⟩ := exists_equiv hσ hJ h₀ hγ₀
        obtain ⟨s, hs⟩ := e₀.surjective ⟨diagH σ J F δ, mem_cent.2 (by rw [← map_mul, ← map_mul, h1])⟩
        obtain ⟨s, rfl⟩ := diagH_surjective (star' P) (one₁ P) s
        refine ⟨s, e.injective (Subtype.ext ?_)⟩
        have h2 := htA (diagH _ _ F s)
        rw [← he₀, hs, mapH_diagH, mapH_diagH] at h2
        rw [he, ← hδ]
        exact h2
      · rintro ⟨s, rfl⟩
        obtain ⟨δ, hδ⟩ := diagH_surjective σ J (torEmb h₀ (diagH _ _ F s))
        have h2 := htA (diagH _ _ F s)
        rw [← hδ, mapH_diagH, mapH_diagH] at h2
        exact ⟨δ, ((he _).trans h2).symm⟩
    have hD := isFundamentalDomain_stdDom (ratPts (star' P) (one₁ P)) dt
    obtain ⟨h1, h2⟩ := isFundamentalDomain_map e hΓ hD
    exact ⟨_, h1, h2.trans (quotMeasure_univ hD).symm⟩

end GlobalTheory.TrEllMeas
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
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

namespace GlobalTheory.LatConjSplit

open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

noncomputable section

theorem toMatrix'_mul_symm {R : Type} [CommRing R] (a : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    LinearMap.toMatrix' (a : (Fin n → R) →ₗ[R] (Fin n → R)) * LinearMap.toMatrix' (a.symm : (Fin n → R) →ₗ[R] (Fin n → R)) = 1 := by
  rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
    LinearMap.toMatrix'_id]

theorem toMatrix'_symm_mul {R : Type} [CommRing R] (a : (Fin n → R) ≃ₗ[R] (Fin n → R)) :
    LinearMap.toMatrix' (a.symm : (Fin n → R) →ₗ[R] (Fin n → R)) * LinearMap.toMatrix' (a : (Fin n → R) →ₗ[R] (Fin n → R)) = 1 := by
  rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
    LinearMap.toMatrix'_id]

def compAt (τ : E →ₐ[F] Fv F v) (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) :
    GL (Fin n) (Fv F v) where
  val := (LinearMap.toMatrix' (a : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] _)).map (splitProj τ)
  inv := (LinearMap.toMatrix' (a.symm : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] _)).map (splitProj τ)
  val_inv := by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, toMatrix'_mul_symm, map_one]
  inv_val := by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, toMatrix'_symm_mul, map_one]

theorem compAt_val (τ : E →ₐ[F] Fv F v)
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) :
    (compAt τ a).1 = (LinearMap.toMatrix' (a : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] _)).map (splitProj τ) := rfl

theorem compAt_inv_val (τ : E →ₐ[F] Fv F v)
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) :
    ((compAt τ a)⁻¹).1 = (LinearMap.toMatrix' (a.symm : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] _)).map (splitProj τ) := rfl

theorem splitVec_apply_equiv (τ : E →ₐ[F] Fv F v)
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) (y : Fin n → Fv F v ⊗[F] E) :
    splitVec τ (a y) = (compAt τ a).1 *ᵥ splitVec τ y := by
  rw [compAt_val, ← splitVec_mulVec, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]

theorem splitVec_symm_apply_equiv (τ : E →ₐ[F] Fv F v)
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) (y : Fin n → Fv F v ⊗[F] E) :
    splitVec τ (a.symm y) = (compAt τ a)⁻¹.1 *ᵥ splitVec τ y := by
  rw [compAt_inv_val, ← splitVec_mulVec, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]

theorem splitHom_conj (hc : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {J J' : Matrix (Fin n) (Fin n) E}
    (j : GLoc σ J v ≃ₜ* GLoc σ J' v) (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
    (h3 : ∀ g y, (matHom _ σ J' (j g)).1 *ᵥ a y = a ((matHom _ σ J g).1 *ᵥ y)) (g : GLoc σ J v) :
    splitHom σ J' τ (j g) = compAt τ a * splitHom σ J τ g * (compAt τ a)⁻¹ := by
  refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun u => ?_))
  obtain ⟨y, rfl⟩ : ∃ y, splitVec τ y = u := ⟨splitIncl hc τ u, splitVec_splitIncl hc τ u⟩
  simp only [Matrix.toLin'_apply, Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [← splitVec_matHom_mulVec, ← splitVec_symm_apply_equiv, ← splitVec_matHom_mulVec, ← splitVec_apply_equiv, ← h3,
    LinearEquiv.apply_symm_apply]

theorem conj_mem_stabLoc_iff {J J' : Matrix (Fin n) (Fin n) E} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (j : GLoc σ J v ≃ₜ* GLoc σ J' v) (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
    (h2 : ∀ y, a y ∈ latLoc F L' v ↔ y ∈ latLoc F L v)
    (h3 : ∀ g y, (matHom _ σ J' (j g)).1 *ᵥ a y = a ((matHom _ σ J g).1 *ᵥ y)) (g : GLoc σ J v) :
    j g ∈ stabLoc σ J' L' v ↔ g ∈ stabLoc σ J L v := by
  rw [mem_stabLoc, mem_stabLoc]
  constructor
  · intro H y
    have := H (a y)
    rwa [h3, h2, h2] at this
  · intro H y'
    obtain ⟨y, rfl⟩ := a.surjective y'
    rw [h3, h2, h2]
    exact H y

theorem isSplitBasis_conj {L L' : Submodule (𝓞 E) (Fin n → E)}
    (a : (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
    (h2 : ∀ y, a y ∈ latLoc F L' v ↔ y ∈ latLoc F L v) (τ : E →ₐ[F] Fv F v) {β : GL (Fin n) (Fv F v)}
    (hβ : IsSplitBasis τ L β) : IsSplitBasis τ L' (compAt τ a * β) := by
  intro u
  rw [hβ u, Units.val_mul, ← Matrix.mulVec_mulVec]
  generalize β.1 *ᵥ u = z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨a y, (h2 y).2 hy, splitVec_apply_equiv τ a y⟩
  · rintro ⟨y', hy', e⟩
    refine ⟨a.symm y', (h2 _).1 (by rwa [a.apply_symm_apply]), ?_⟩
    rw [splitVec_symm_apply_equiv, e, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

theorem split_conj {J J' : Matrix (Fin n) (Fin n) E} {L L' : Submodule (𝓞 E) (Fin n → E)}
    (j : GLoc σ J v ≃ₜ* GLoc σ J' v) (hj : IsLatticeConj L L' j) (hJ' : IsHermND σ J')
    (hL' : IsSelfDualAt σ J' L' v) :
    (∀ g, j g ∈ stabLoc σ J' L' v ↔ g ∈ stabLoc σ J L v) ∧ ∀ s : SplitAt σ J L v, ∃ s' : SplitAt σ J' L' v,
      (∀ g, s'.equiv (j g) = s.equiv g) ∧
      ∀ (k : stabLoc σ J L v) (k' : stabLoc σ J' L' v), (k' : GLoc σ J' v) = j k → s'.red k' = s.red k := by
  obtain ⟨a, -, h2, h3⟩ := hj
  refine ⟨conj_mem_stabLoc_iff j a h2 h3, fun s => ⟨⟨s.emb, compAt s.emb a * s.basis, s.cm, hJ', hL',
    isSplitBasis_conj a h2 s.emb s.isBasis⟩, ?_⟩⟩
  have he : ∀ g, splitEquivIn s.cm hJ' s.emb (compAt s.emb a * s.basis) (j g) = s.equiv g := fun g => by
    rw [splitEquivIn_apply, splitHom_conj s.cm s.emb j a h3, SplitAt.equiv, splitEquivIn_apply]
    group
  refine ⟨he, fun k k' hk => ?_⟩
  apply Units.ext
  simp only [SplitAt.red, splitRed_val]
  congr 1
  ext i l
  rw [coe_stabLocEquiv, coe_stabLocEquiv, hk]
  exact congrArg _ (congrArg (fun x => x.1 i l) (he k))

theorem split_conj_cast {n' : ℕ} (hr : n' = n) {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin n') (Fin n') E}
    {L : Submodule (𝓞 E) (Fin n → E)} {L' : Submodule (𝓞 E) (Fin n' → E)} (j : GLoc σ J v ≃ₜ* GLoc σ J' v)
    (hj : IsLatticeConj L L' j) (hJ' : IsHermND σ J') (hL' : IsSelfDualAt σ J' L' v) :
    (∀ g, j g ∈ stabLoc σ J' L' v ↔ g ∈ stabLoc σ J L v) ∧ ∀ s : SplitAt σ J L v, ∃ s' : SplitAt σ J' L' v,
      (∀ g a b, (s'.equiv (j g)).1 a b = (s.equiv g).1 (a.cast hr) (b.cast hr)) ∧
      ∀ (k : stabLoc σ J L v) (k' : stabLoc σ J' L' v), (k' : GLoc σ J' v) = j k →
        ∀ a b, (s'.red k').1 a b = (s.red k).1 (a.cast hr) (b.cast hr) := by
  subst hr
  obtain ⟨h1, h2⟩ := split_conj j hj hJ' hL'
  refine ⟨h1, fun s => ?_⟩
  obtain ⟨s', e1, e2⟩ := h2 s
  exact ⟨s', fun g a b => by rw [e1]; rfl, fun k k' hk a b => by rw [e2 k k' hk]; rfl⟩

end

end GlobalTheory.LatConjSplit

theorem GlobalTheory.LatConjSplit.splitAt_of_isLatticeConj : ∀ (D : D7) (V V' : HSp D) (hr : V'.rank = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (j : GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), IsLatticeConj (frameLat V) (frameLat V') j → (∀ g, j g ∈ Kv V' v ↔ g ∈ Kv V v) ∧ ∀ s : SplitAt D.sp.cm.sig V.gram (frameLat V) v, ∃ s' : SplitAt D.sp.cm.sig V'.gram (frameLat V') v, (∀ g a b, (s'.equiv (j g)).1 a b = (s.equiv g).1 (a.cast hr) (b.cast hr)) ∧ ∀ (k : Kv V v) (k' : Kv V' v), (k' : GLoc D.sp.cm.sig V'.gram v) = j k → ∀ a b, (s'.red k').1 a b = (s.red k).1 (a.cast hr) (b.cast hr) := by
  intro D V V' hr v j hj
  exact GlobalTheory.LatConjSplit.split_conj_cast hr j hj (GlobalTheory.Orb.isHermND_gram V') (SelfDual.isSelfDualAt_frameLat D V' v)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt intAt latV latA)

theorem _root_.GlobalTheory.T.mem_lattice_of_rational_mem_completion_all_places :
    ∀ (D : D7) (S : HSp D) (L : Lat S), Submodule.IsFullLattice D.host.E L →
      ∀ z : Fin S.rank → D.host.E,
        (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ latV S L (fun _ => True) → z ∈ L :=
  GlobalTheory.RatLat.mem_of_mem_latV
end
