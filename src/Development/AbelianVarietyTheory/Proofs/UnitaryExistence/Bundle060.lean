module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle004
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle029
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle059
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SpGenStatement
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CoreLawsCompare

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Matrix

section Gen

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E] {r : ℕ} (V : ConjugateFieldNorm.HSpace E r)




end Gen

section Rec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

instance totallyReal_host (D : D7) : IsTotallyReal D.host.F := D.sp.cm.totReal

variable {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r)

def crdR : V.V ≃ₗ[D.host.E] (Fin r → D.host.E) := (V.frame.reindex (finCongr hr)).equivFun

def gramR : Matrix (Fin r) (Fin r) D.host.E := (Matrix.reindex (finCongr hr) (finCongr hr) V.gram)ᵀ

theorem herm_crdR (x y : V.V) : herm (gramR V hr) (crdR V hr x) (crdR V hr y) = V.hT y x := by
  subst hr
  rw [Formalism.L2.Herm.hT_crd D.sp.cm V]
  unfold herm Formalism.UG.hform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [crdR, gramR, finCongr_refl, Matrix.reindex_refl_refl, Module.Basis.reindex_refl]
  change _ * V.gram b a * cc _ = cc _ * V.gram b a * _
  unfold Formalism.L2.Herm.crd
  ring

theorem mem_one_iff (z : D.host.E) : z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩

def spOf : ConjugateFieldNorm.HSpace D.host.E r where
  Gm := gramR V hr
  Gm_herm a b := V.herm.eq _ _
  Gm_det h := by
    obtain ⟨v, hv, h0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
    obtain ⟨x, rfl⟩ := (crdR V hr).surjective v
    refine hv ((congrArg _ (V.nondeg.2 x fun y => ?_)).trans (map_zero _))
    rw [← herm_crdR V hr, herm, Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_mul, show ∑ a, crdR V hr x a * gramR V hr a b = 0 from congrFun h0 b, zero_mul]
  L := V.L0.map ((crdR V hr).toLinearMap.restrictScalars (𝓞 D.host.E))
  L_fg := V.standardTuple_isLattice.fg.map _
  L_span := by
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      by_contra hproper
      obtain ⟨φ, hφ, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hproper)
      have hinj : Function.Injective V.hT := LinearMap.ker_eq_bot.mp
        (LinearMap.separatingLeft_iff_ker_eq_bot.mp V.nondeg.1)
      let e := LinearEquiv.ofInjective V.hT hinj
      have hrank : Module.rank D.host.E V.V = Module.rank D.host.E (LinearMap.range V.hT) :=
        rank_eq_of_equiv_equiv (starRingEnd D.host.E) e.toAddEquiv
          (star_involutive.bijective) (map_smulₛₗ e)
      have hsurj : Function.Surjective V.hT := by
        rw [← LinearMap.range_eq_top]
        apply Submodule.eq_top_of_finrank_eq
        change Module.finrank D.host.E (LinearMap.range V.hT) =
          Module.finrank D.host.E (Module.Dual D.host.E V.V)
        rw [Subspace.dual_finrank_eq]
        exact congrArg Cardinal.toNat hrank.symm
      obtain ⟨x, hx⟩ := hsurj φ
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hφ (hx.symm.trans V.hT.map_zero)
      have hline (c : D.host.E) : c • x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap]
        intro y hy
        have hxy : V.hT x y = 0 := by
          rw [hx]
          exact hker (Submodule.subset_span hy)
        rw [LinearMap.restrictScalars_apply, map_smul, V.herm.eq_iff.mp hxy, smul_zero]
        exact Submodule.zero_mem _
      obtain ⟨y, hy⟩ : ∃ y, V.hT y x ≠ 0 := by
        simpa only [not_forall, not_not] using mt (V.nondeg.2 x) hx0
      let f := ((V.hT y).restrictScalars (𝓞 D.host.E)).comp V.L0.subtype
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_surjective f <| by
        intro z
        refine ⟨⟨(z / V.hT y x) • x, hline _⟩, ?_⟩
        change V.hT y ((z / V.hT y x) • x) = z
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hy]
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField RingOfIntegers.coe_injective (Field.toIsField _))
    rw [Submodule.map_coe]
    change Submodule.span D.host.E ((crdR V hr).toLinearMap '' (V.L0 : Set V.V)) = ⊤
    rw [Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  L_dual v := by
    obtain ⟨x, rfl⟩ := (crdR V hr).surjective v
    have h1 : crdR V hr x ∈ V.L0.map ((crdR V hr).toLinearMap.restrictScalars (𝓞 D.host.E)) ↔ x ∈ V.L0 :=
      ⟨fun ⟨y, hy, e⟩ => (crdR V hr).injective e ▸ hy, fun h => ⟨x, h, rfl⟩⟩
    have h2 : x ∈ V.L0 ↔ ∀ y ∈ V.L0, IsIntegral ℤ (V.hT y x) := by
      conv_lhs => rw [← V.baseLattice_isUnimodular]
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, mem_one_iff]
      rfl
    rw [h1, h2]
    constructor
    · rintro h _ ⟨y, hy, rfl⟩
      exact (herm_crdR V hr x y).symm ▸ h y hy
    · intro h y hy
      exact herm_crdR V hr x y ▸ h _ ⟨y, hy, rfl⟩

structure IsCoord (V' : ConjugateFieldNorm.HSpace D.host.E r) (ψ : ConjugateFieldNorm.GA D.host.F V' ≃* GA D V) : Prop where
  sp : V' = spOf V hr
  inf : ∀ g, Matrix.reindex (finCongr hr) (finCongr hr) (infHom V (ψ g)).val = g.1.1.val
  fin : ∀ g, Matrix.reindex (finCongr hr) (finCongr hr) (finHom V (ψ g)).val = g.2.1.val
  top : AutomorphismGroupTopologies.topG D.host.F V' = TopologicalSpace.induced ψ inferInstance

variable {V hr} {V' : ConjugateFieldNorm.HSpace D.host.E r} {ψ : ConjugateFieldNorm.GA D.host.F V' ≃* GA D V}

def IsCoord.quotEquiv (h : IsCoord V hr V' ψ) : AutomorphismGroupTopologies.AutQ D.host.F V' ≃ᵐ Formalism.L2.Pj.AutQ V where
  toEquiv := Quotient.congr ψ.toEquiv fun a b => by
    have mem_GQ (g : ConjugateFieldNorm.GA D.host.F V') :
        ψ g ∈ GQ V ↔ g ∈ AutomorphismGroupTopologies.ratG D.host.F V' := by
      subst hr
      let p := (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
      let q := (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
      have hInf : (matHom V (ψ g)).val.map p = g.1.1.val := h.inf g
      have hFin : (matHom V (ψ g)).val.map q = g.2.1.val := h.fin g
      constructor
      · rintro ⟨γ, -, e⟩
        have he : (matHom V (ψ g)).val = γ.val.map (inclR (AF D.host.F)) :=
          (congrArg Units.val e).symm
        refine ⟨γ, ?_, ?_⟩
        · rw [← hInf, he]
          ext i j
          simp [p, inclR, ConjugateFieldNorm.incl]
        · rw [← hFin, he]
          ext i j
          simp [q, inclR, ConjugateFieldNorm.incl]
      · rintro ⟨γ, eInf, eFin⟩
        obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
        have he' : (matHom V (ψ g)).val = γ.val.map (inclR (AF D.host.F)) := by
          ext i j
          refine e.injective (Prod.ext ?_ ?_)
          · rw [(he _).1, (he _).1]
            exact congrFun (congrFun (hInf.trans eInf) i) j
          · rw [(he _).2, (he _).2]
            exact congrFun (congrFun (hFin.trans eFin) i) j
        refine ⟨γ, ?_, Units.ext he'.symm⟩
        have hu : Formalism.UG.cT (sigR _ D.sp.cm.sig) (matHom V (ψ g)).val *
            JR _ V.gram * (matHom V (ψ g)).val = JR _ V.gram := (ψ g).2
        have hinj : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
          Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
        change Formalism.UG.cT _ γ.val * V.gram * γ.val = V.gram
        refine Matrix.map_injective hinj ?_
        change (_ : Matrix _ _ _).map _ = JR _ V.gram
        rw [← hu, he', Matrix.map_mul, Matrix.map_mul]
        congr 2
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change _ ↔ ψ b * (ψ a)⁻¹ ∈ GQ V
    rw [← map_inv, ← map_mul]
    exact (mem_GQ _).symm
  measurable_toFun s hs := by
    change MeasurableSet[@borel _ (AutomorphismGroupTopologies.topG D.host.F V')] (ψ ⁻¹' (Formalism.L2.Pj.autMk V ⁻¹' s))
    rw [h.top, borel_comap]
    exact ⟨_, hs, rfl⟩
  measurable_invFun s hs := by
    have hs' : MeasurableSet[@borel _ (AutomorphismGroupTopologies.topG D.host.F V')] (AutomorphismGroupTopologies.autMk D.host.F V' ⁻¹' s) := hs
    rw [h.top, borel_comap] at hs'
    obtain ⟨t, ht, e⟩ := hs'
    change MeasurableSet (ψ.symm ⁻¹' (AutomorphismGroupTopologies.autMk D.host.F V' ⁻¹' s))
    rw [← e, ← Set.preimage_comp]
    simpa using ht

def RightInv (V : HSp D) (ν : Measure (Formalism.L2.Pj.AutQ V)) : Prop :=
  ∀ (h : GA D V) (ρ : Formalism.L2.Pj.AutQ V → Formalism.L2.Pj.AutQ V),
    (∀ g : GA D V, ρ (Quotient.mk _ g) = Quotient.mk _ (g * h)) → ∀ s, MeasurableSet s → ν (ρ ⁻¹' s) = ν s

end Rec

end GlobalTheory.CoreLawsCompare
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FibreFlag

theorem blockTriangular_of_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] (f : n → ℕ) (A C : Matrix n n ℂ)
    (h : A * C = 1) (hC : C.BlockTriangular f) : A.BlockTriangular f := by
  haveI : Invertible C := C.invertibleOfIsUnitDet (Matrix.isUnit_det_of_left_inverse h)
  rw [← Matrix.inv_eq_left_inv h]
  exact Matrix.blockTriangular_inv_of_blockTriangular hC

theorem upper_of_blocks {r : ℕ} (q : ℕ) (B : Matrix (Fin r) (Fin r) ℂ) (hB : B.det ≠ 0)
    (h1 : ∀ a c : Fin r, (c : ℕ) < q → c < a → B a c = 0)
    (h2 : ∀ a c : Fin r, q ≤ (c : ℕ) → c < a → B⁻¹ a c = 0) (a c : Fin r) (hca : c < a) : B a c = 0 := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have t1 : B.BlockTriangular (fun a => min (a : ℕ) q) := fun a c h =>
    h1 a c (by simp only at h; omega) (by simp only at h; rw [Fin.lt_def]; omega)
  have t2 := blockTriangular_of_mul_eq_one _ _ _ (Matrix.nonsing_inv_mul B hu) t1
  have t3 : B⁻¹.BlockTriangular (fun a => (a : ℕ)) := fun a c h => by
    by_cases hc : (c : ℕ) < q
    · exact t2 (by simp only at h ⊢; omega)
    · exact h2 a c (not_lt.1 hc) h
  exact blockTriangular_of_mul_eq_one _ _ _ (Matrix.mul_nonsing_inv B hu) t3 hca



theorem fibTri : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → FibTri e F M := by
  classical
  intro E _ _ _ H Dw l Xo c σ g e F r M hσ hM hneg k k' x x' Pm Pm' v v' hP hP' hu hv hv' hcf
  have hper : ∀ (k) (x : (M.X k).dom) (Pm : (F.Di k).La →+ (Fin g → ℂ)),
      (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) →
      IsPeriod (F.Di k) (fun j => relab c σ (e j).1) Pm := by
    intro k x Pm hP
    obtain ⟨⟨idx, hty, -, hfr⟩, hp0, hr, hξ, hpos, hφ⟩ := GlobalTheory.FrameUnif.letter_column_dictionary E H Dw l Xo c σ g e F r M hσ hM hneg k
    have hlat := (hφ ((M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap) (fun _ => rfl)).2
    exact ((FramePeriod.isPeriod_frame E H (F.Di k) r _ _ _ _ (hM.type k).2 g idx _ hty hξ hpos hlat hr).2 x.1
      (hp0 ▸ x.2)).2 Pm fun a j => (hP a j).trans (hfr _ _ _)
  have p := hper k x Pm hP
  have p' := hper k' x' Pm' hP'
  obtain rfl := F.disj k k' _ _ p p' hu
  obtain ⟨⟨idx, hty, hix, hfr⟩, hp0, hr, hξ, hpos, hφ⟩ := GlobalTheory.FrameUnif.letter_column_dictionary E H Dw l Xo c σ g e F r M hσ hM hneg k
  obtain ⟨φ, hφe⟩ : ∃ φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E), ∀ a, φ a = (M.φ k a : Fin r → E) :=
    ⟨(M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap, fun _ => rfl⟩
  obtain ⟨hΛ, hlat⟩ := hφ φ hφe
  have hΨ := (hM.type k).2
  have hx : x.1 ∈ GG (M.X k).Ψ (M.X k).Gm (F.Di k).q := hp0 ▸ x.2
  have hx' : x'.1 ∈ GG (M.X k).Ψ (M.X k).Gm (F.Di k).q := hp0 ▸ x'.2
  obtain ⟨gam, h, hiso, hhalf, hA, hh⟩ := (F.fibre k _ _ p p').1 hu
  obtain ⟨γ, hγ⟩ := FrameFibre.exists_gl φ hlat.1 hlat.2.1 gam
  have hun := FrameFibre.herm_of_trace φ hlat.2.1 (M.X k).Gm γ _ (neg_ne_zero.2 (M.X k).ξ0_ne) fun v w => by
    rw [hγ, hγ, ← hlat.2.2.2.2, ← hlat.2.2.2.2, hiso]
  have hγΓ : γ ∈ (M.X k).Γ := by
    rw [hM.gam]
    refine ⟨⟨hun, fun y => hΛ ▸ (?_ : y ∈ LinearMap.range φ ↔ _ ∈ LinearMap.range φ)⟩, fun a ha => ?_, fun a => ?_⟩
    · constructor
      · rintro ⟨v, rfl⟩
        exact ⟨gam v, (hγ v).symm⟩
      · rintro ⟨v, hv⟩
        refine ⟨gam.symm v, ?_⟩
        apply (Matrix.mulVec_injective_of_isUnit γ.isUnit)
        rw [hγ, LinearEquiv.apply_symm_apply, hv]
    · obtain ⟨b, hb⟩ := hhalf a ha
      exact ⟨b, by rw [← hφe, ← hφe, hγ, hb, map_add (f := _), map_nsmul]⟩
    · obtain ⟨b, hb⟩ := hA a
      exact ⟨b, by rw [← hφe, ← hφe, hγ, hb, map_add (f := _), map_nsmul]⟩
  have hγx := FrameFibre.lact_mem_GG hun hx
  obtain ⟨Pg, hPg⟩ := ((FramePeriod.isPeriod_frame E H (F.Di k) r _ _ _ _ hΨ g idx _ hty hξ hpos hlat hr).2 _ hγx).1
  have hP1 := fun a j => (hP a j).trans (hfr x.1 _ j)
  have hP2 := fun a j => (hP' a j).trans (hfr x'.1 _ j)
  simp only [← hφe] at hP1 hP2
  have hmove := (per_move E H (F.Di k) r _ _ φ _ hΨ g idx _ hty hξ hpos hlat).2.1 x.1 γ Pm Pg hun hP1 hPg
  set A := LinearMap.toMatrix' h.toLinearMap with hAdef
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hAdef, LinearMap.toMatrix'_mulVec]; rfl
  obtain ⟨b, hb, hb0, hb1, hb2, -⟩ := FramePeriod.frame_of_period_linear E H (F.Di k) r _ _ φ _ hΨ g idx _ hty
    hξ hpos hlat Pg _ hγx x'.1 hx' hPg Pm' hP2 A fun v => by
      obtain ⟨a, rfl⟩ := gam.surjective v
      rw [hAv, hh, hmove a (gam a) (hγ a).symm]
  have hrig := (FamRigid.ex_eq_of_level_group latMinkowski E H Dw l Xo _ g _ F k Pm Pm' gam A p p' hiso hhalf hA
    fun a => by rw [hAv, hh]).2.2
  choose cf hcf1 hcf2 hcf3 using hcf
  have hcol : ∀ τ i, A *ᵥ (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) =
      Pi.single (e.symm ⟨τ, i⟩) 1 := by
    intro τ i
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k Pm p _ (v τ) _ (hv τ) (cf τ i) (v' τ i)).1
      (hcf3 τ i)
    have d2 := (ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k Pm p k Pm' h.toLinearMap p'
      (fun z => by rw [← hrig z, hAv]; rfl) _ _).1 d1
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k Pm' p'
    rw [hAv]
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 (hv' τ i)
  let C : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun j j' =>
    (∑ i, (show ℂ from cf (e j').1 (e j').2 i) • (Pi.single (e.symm ⟨(e j').1, i⟩) 1 : Fin g → ℂ)) j
  have hAC : A * C = 1 := by
    ext j j'
    have := congrFun (hcol (e j').1 (e j').2) j
    rw [Sigma.eta, Equiv.symm_apply_apply, Pi.single_apply] at this
    rw [Matrix.one_apply, ← this]
    rfl
  have hC : C.BlockTriangular (fun j => ((e j).2 : ℕ)) := by
    intro j j' hj
    simp only [C, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : j = e.symm ⟨(e j').1, i⟩
    · have h3 : (((e j).2 : ℕ)) = i := by rw [hi, Equiv.apply_symm_apply]
      have h4 : cf (e j').1 (e j').2 i = 0 := hcf2 _ _ i (by rw [Fin.lt_def, ← h3]; exact hj)
      rw [h4]
      exact zero_mul _
    · have h5 : (Pi.single (e.symm ⟨(e j').1, i⟩) 1 : Fin g → ℂ) j = 0 := Pi.single_eq_of_ne hi _
      exact mul_eq_zero_of_right (M₀ := ℂ) _ h5
  have hT := blockTriangular_of_mul_eq_one _ _ _ hAC hC
  have hdet : ∀ τ, (mat b τ).det ≠ 0 := fun τ h0 => (hx' τ).1 (by
    have e1 : mat x'.1 τ = mat (lact γ x.1) τ * mat b τ := by rw [hb]; rfl
    rw [e1, Matrix.det_mul, h0, mul_zero])
  refine ⟨γ, hγΓ, b, fun τ => ⟨hdet τ, upper_of_blocks (F.Di k).q (mat b τ) (hdet τ) ?_ ?_⟩, by rw [← hb]⟩
  · intro a c' hc hca
    by_cases ha : (a : ℕ) < (F.Di k).q
    · have h1 := hb1 (idx.symm (τ, c')) (idx.symm (τ, a))
      have i1 := hix (idx.symm (τ, c'))
      have i2 := hix (idx.symm (τ, a))
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
      rw [Equiv.apply_symm_apply] at i1 i2
      simp only [hc, ha, if_true] at i1 i2
      rw [Fin.lt_def] at hca
      exact (h1 rfl hc ha).symm.trans (hT (by simp only; omega))
    · exact hb0 τ a c' hc (not_lt.1 ha)
  · intro a c' hc hca
    rw [Fin.lt_def] at hca
    have ha : (F.Di k).q ≤ (a : ℕ) := by omega
    have h1 := hb2 (idx.symm (τ, a)) (idx.symm (τ, c'))
    have i1 := hix (idx.symm (τ, c'))
    have i2 := hix (idx.symm (τ, a))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
    rw [Equiv.apply_symm_apply] at i1 i2
    simp only [not_lt.2 hc, not_lt.2 ha, if_false] at i1 i2
    exact (h1 rfl ha hc).symm.trans (hT (by simp only; omega))

end GlobalTheory.FibreFlag
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.cmCurveHom_exists_pureTypeVector_anyLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (φ : C.P.A.left ⟶ Xo.univ.t.G.left) (x : ℂ → (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ε : ℤˣ), (∀ z, (x z).left = C.pt z ≫ φ) → (∀ z w, x (z + w) = x z * x w) → (∀ z, x ((1 + ((ε : ℤ) : ℂ) * H.rt0) / 2 * z) = x z ≫ Xo.univ.t.act.act H.w0) → ∃ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∀ z : ℂ, x z = F.ex i P (z • P a) := by
  first | exact @GlobalTheory.CurveHomLiftAnyLevel.exists_pure_vector | exact GlobalTheory.CurveHomLiftAnyLevel.exists_pure_vector | (intros; apply GlobalTheory.CurveHomLiftAnyLevel.exists_pure_vector <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_cmEndomorphism_comm_conjugation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∃ W : C.P.A ⟶ C.P.A, IsMonHom W ∧ (∀ z, C.pt z ≫ W.left = C.pt (wC H (0, 1) * z)) ∧ (∀ z z', C.pt z = C.pt z' ↔ ∃ a, z - z' = wC H a) ∧ (∀ x : Sp ℂ ⟶ C.P.A.left, x ≫ C.P.A.hom = 𝟙 _ → ∃ z, C.pt z = x) ∧ ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ io : C.P.A.left ⟶ C.P.A.left, IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → W.left ≫ io = io ≫ W.left := by
  first | exact @GlobalTheory.CurveEndo.exists_endo_comm | exact GlobalTheory.CurveEndo.exists_endo_comm | (intros; apply GlobalTheory.CurveEndo.exists_endo_comm <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.GlobalTheory.T.uniformization_period_lattice_change : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P P' : (U.Di i).La →+ (Fin g → ℂ)) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di i).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod (U.Di i) ty P → IsPeriod (U.Di i) ty P' → (∀ a b, (U.Di i).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La), ∃ e, gam a = a + l.M • e) → (∀ a, ∃ e, gam a = a + l.A • e) → (∀ a, P' (gam a) = h₀ *ᵥ P a) → IsUnit h₀.det ∧ U.u i P = U.u i P' ∧ ∀ z, (U.ex i P' (h₀ *ᵥ z)).left = (U.ex i P z).left := by
  first | exact @GlobalTheory.FamRigid.ex_eq_of_level_group | exact GlobalTheory.FamRigid.ex_eq_of_level_group | (intros; apply GlobalTheory.FamRigid.ex_eq_of_level_group <;> assumption)
end
