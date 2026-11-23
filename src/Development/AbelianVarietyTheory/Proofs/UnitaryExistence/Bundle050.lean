module

import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle024
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle038
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle013
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle026
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle047
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemIffConjugateNotMem
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle037
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace

noncomputable section

namespace GlobalTheory

universe u v

theorem isOpen_connectedComponent_of_noetherianSpace {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] (x : X) : IsOpen (connectedComponent x) := by
  have h : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hy
      exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun h => hy (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨Z, ⟨hZ, hZ'⟩, hy⟩ hyx
      apply hZ'
      rw [connectedComponent_eq hyx]
      exact hZ.1.isConnected.subset_connectedComponent hy
  rw [← isClosed_compl_iff, h]
  refine Set.Finite.isClosed_biUnion
    (NoetherianSpace.finite_irreducibleComponents.subset (by exact fun Z hZ => hZ.1)) fun Z hZ => ?_
  exact isClosed_of_mem_irreducibleComponents Z hZ.1

theorem geometricallyConnected_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [ConnectedSpace X] :
    GeometricallyConnected f := by
  apply GlobalTheory.RatPointConn.of_isAlgClosed <;> assumption

section Sub

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A N : C} [GrpObj N]

theorem exists_grpObj_of_mono_of_fac (n : A ⟶ N) [Mono n] (e : 𝟙_ C ⟶ A) (m : A ⊗ A ⟶ A) (i : A ⟶ A)
    (he : e ≫ n = η[N]) (hm : m ≫ n = (n ⊗ₘ n) ≫ μ[N]) (hi : i ≫ n = n ≫ ι[N]) :
    ∃ _ : GrpObj A, IsMonHom n := by
  have he' : ∀ {T : C} (t : T ⟶ 𝟙_ C), t ≫ e ≫ n = 1 := fun t => by
    rw [he, Hom.one_def, toUnit_unique t (toUnit _)]
  have hm' : ∀ {T : C} (t : T ⟶ A ⊗ A), t ≫ m ≫ n = (t ≫ fst _ _ ≫ n) * (t ≫ snd _ _ ≫ n) :=
    fun t => by
      rw [hm, Hom.mul_def, ← Category.assoc]
      congr 1
      ext <;> simp
  have hm'' : m ≫ n = (fst _ _ ≫ n) * (snd _ _ ≫ n) := by simpa using hm' (𝟙 _)
  have hi' : i ≫ n = n⁻¹ := by rw [hi, Hom.inv_def]
  letI : GrpObj A :=
    { one := e
      mul := m
      inv := i
      one_mul := by
        rw [← cancel_mono n, Category.assoc, hm', whiskerRight_fst_assoc, whiskerRight_snd_assoc,
          he', _root_.one_mul, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono n, Category.assoc, hm', whiskerLeft_fst_assoc, whiskerLeft_snd_assoc,
          he', _root_.mul_one, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono n, Category.assoc, hm', Category.assoc, Category.assoc,
          hm' (A ◁ m), whiskerRight_fst_assoc, whiskerRight_snd_assoc, whiskerLeft_fst_assoc,
          whiskerLeft_snd_assoc, hm', hm', MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc]
        simp
      left_inv := by
        rw [← cancel_mono n, Category.assoc, Category.assoc, hm', he', lift_fst_assoc,
          lift_snd_assoc, hi', Category.id_comp, inv_mul_cancel]
      right_inv := by
        rw [← cancel_mono n, Category.assoc, Category.assoc, hm', he', lift_fst_assoc,
          lift_snd_assoc, hi', Category.id_comp, mul_inv_cancel] }
  exact ⟨this, ⟨he, hm⟩⟩

end Sub

theorem finite_points_of_isOpenMap_unit {k : Type} [Field k] [IsAlgClosed k] (N : Over (Sp k))
    [GrpObj N] [LocallyOfFiniteType N.hom] [NoetherianSpace N.left]
    (h : IsOpenMap η[N].left) : Finite (𝟙_ (Over (Sp k)) ⟶ N) := by
  let pt : Sp k := IsLocalRing.closedPoint k
  let F : (𝟙_ (Over (Sp k)) ⟶ N) → N.left := fun x => x.left pt
  have hF : Function.Injective F := fun x y hxy =>
    Over.OverMorphism.ext (ext_of_apply_closedPoint_eq N.hom x.w y.w hxy)
  have ho : ∀ x, IsOpen {F x} := fun x => by
    have hx : η[N] ≫ (GrpObj.mulRight x).hom = x := by
      simpa [comp_lift_assoc] using lift_comp_one_left (𝟙 _) x
    have : IsIso (GrpObj.mulRight x).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulRight x).hom))
    have h₁ : IsOpenMap x.left := by
      rw [← hx, Over.comp_left]
      exact (GrpObj.mulRight x).hom.left.isOpenMap.comp h
    have h₂ := h₁ {pt} (by
      have : Subsingleton (Sp k) := inferInstance
      convert isOpen_univ
      exact Set.eq_univ_of_forall fun a => this.elim _ _)
    rwa [Set.image_singleton] at h₂
  obtain ⟨t, -, ht⟩ := (NoetherianSpace.isCompact (Set.range F)).elim_nhds_subcover
    (fun y => {y}) (by rintro _ ⟨x, rfl⟩; exact (ho x).mem_nhds rfl)
  have : (Set.range F).Finite := t.finite_toSet.subset fun y hy => by simpa using ht hy
  exact (Set.finite_range_iff hF).1 this

theorem exists_neutralComponent : ∀ (k : Type) [Field k] [IsAlgClosed k] (N : Over (Sp k)) [GrpObj N], Smooth N.hom → QuasiCompact N.hom → ∃ (N₀ : Over (Sp k)) (_ : GrpObj N₀) (ν : N₀ ⟶ N) (g : ℕ), IsMonHom ν ∧ IsOpenImmersion ν.left ∧ IsClosedImmersion ν.left ∧ GeometricallyConnected N₀.hom ∧ SmoothOfRelativeDimension g N₀.hom ∧ (g = 0 → Finite (𝟙_ (Over (Sp k)) ⟶ N)) := by
  intro k _ _ N _ hs hq
  have : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have : CompactSpace N.left := QuasiCompact.compactSpace_of_compactSpace N.hom
  have : IsNoetherian N.left := {}
  let pt : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  let e₀ : N.left := η[N].left pt
  let U : N.left.Opens := ⟨connectedComponent e₀, isOpen_connectedComponent_of_noetherianSpace e₀⟩
  let N₀ : Over (Sp k) := Over.mk (U.ι ≫ N.hom)
  let ν : N₀ ⟶ N := Over.homMk U.ι rfl
  have hνo : IsOpenImmersion ν.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hr : Set.range ν.left = connectedComponent e₀ := U.range_ι
  have hνc : IsClosedImmersion ν.left := .of_isPreimmersion _ (hr ▸ isClosed_connectedComponent)
  have : Mono ν := Over.mono_of_mono_left ν
  have hsm : Smooth N₀.hom := inferInstanceAs (Smooth (U.ι ≫ N.hom))
  have hc : ConnectedSpace N₀.left :=
    isConnected_iff_connectedSpace.1 (isConnected_connectedComponent (x := e₀))
  have hg : GeometricallyConnected N₀.hom := geometricallyConnected_of_isAlgClosed N₀.hom

  have fac : ∀ (T : Over (Sp k)) [ConnectedSpace T.left] (φ : T ⟶ N) (t : 𝟙_ _ ⟶ T),
      t ≫ φ = η[N] → ∃ ψ : T ⟶ N₀, ψ ≫ ν = φ := by
    intro T _ φ t ht
    have hsub : Set.range φ.left ⊆ Set.range ν.left := by
      rw [hr]
      refine (isConnected_range φ.left.continuous).subset_connectedComponent ⟨t.left pt, ?_⟩
      simp only [e₀, ← ht, Over.comp_left, Scheme.Hom.comp_apply]
    refine ⟨Over.homMk (IsOpenImmersion.lift ν.left φ.left hsub) ?_, ?_⟩
    · rw [← ν.w, IsOpenImmersion.lift_fac_assoc, φ.w]
    · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac ν.left φ.left hsub)
  have : ConnectedSpace (𝟙_ (Over (Sp k))).left := inferInstanceAs (ConnectedSpace (Sp k))
  obtain ⟨e, he⟩ := fac (𝟙_ _) η[N] (𝟙 _) (Category.id_comp _)
  have : ConnectedSpace (N₀ ⊗ N₀).left :=
    inferInstanceAs (ConnectedSpace ↥(pullback N₀.hom N₀.hom))
  obtain ⟨m, hm⟩ := fac (N₀ ⊗ N₀) ((ν ⊗ₘ ν) ≫ μ[N]) (lift e e)
    (by simpa [he] using lift_comp_one_left (𝟙 _) η[N])
  obtain ⟨i, hi⟩ := fac N₀ (ν ≫ ι[N]) e (by simp [reassoc_of% he])
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono_of_fac ν e m i he hm hi
  obtain ⟨g, hgd⟩ := exists_dim_of_preconnected N₀.hom (e.left pt)
  refine ⟨N₀, G, ν, g, hG, hνo, hνc, hg, hgd, ?_⟩
  rintro rfl
  have : Etale N₀.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hgd
  have : Etale (e.left ≫ N₀.hom) := by
    rw [e.w]; exact inferInstanceAs (Etale (𝟙 (Sp k)))
  have : Etale e.left := Etale.of_comp e.left N₀.hom
  refine finite_points_of_isOpenMap_unit N ?_
  rw [← he, Over.comp_left]
  exact (e.left ≫ ν.left).isOpenMap

end GlobalTheory
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem nonempty_thetaData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, Nonempty (ThetaData e F M k) := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hσ hM hξ k
  obtain ⟨⟨idx, hty, -, hper⟩, hp0, hr, hcc, hpos, hφ⟩ :=
    GlobalTheory.T.cmType_letter_frame_column_dictionary E H Dw l Xo c σ g e F r M hσ hM hξ k
  obtain ⟨Pf, hPf, -, hisPer, hdiff, -⟩ := GlobalTheory.T.exists_framePeriods_alt E H Dw l Xo c σ g e F r M hσ hM hξ k
  have htf : IsTypeFn H (F.Di k).p (F.Di k).q (fun j => relab c σ (e j).1) := by
    rw [(F.sig k).1, (F.sig k).2]
    exact (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw g e
  obtain ⟨hg, -⟩ := (GlobalTheory.PeriodExists.typeFn_period_exist E H (F.Di k)).2.1 g _ htf
  obtain ⟨bas, hsym, had⟩ := GlobalTheory.exists_symplectic_basis_adapted_mod_eight E H (F.Di k) g hg
  let φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hdom : (M.X k).dom = GG (M.X k).Ψ (M.X k).Gm (F.Di k).q := by
    rw [← hp0]
  let co : (Fin (Module.finrank ℂ (Frame (M.X k).Ψ r)) → ℂ) ≃L[ℂ] Frame (M.X k).Ψ r :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨h, ta, c₁, c₂, hnorm, hhol, h1, h2, fr, hf1, hf2, hf3, hf4, hf5⟩ :=
    GlobalTheory.FrameTheta.exists_thetaFrame_frames E H Dw l Xo _ g _ F k r (-(M.X k).ξ0) (M.X k).Gm φ (M.X k).Ψ idx Pf
      (hM.type k).2 hty hcc hpos (hφ φ fun _ => rfl).2 hr (fun x v j => (hPf x v j).trans (hper x _ j))
      (hdom ▸ (GlobalTheory.frames_isConnected E r (M.X k)).isPreconnected) bas hsym _ co
  rw [← hdom] at hnorm hhol hf1 hf2 hf3 hf4 hf5
  exact ⟨{
    Pf := Pf
    per := hPf
    isPer := hisPer
    m := _
    co := co
    holPer := ⟨fun b hb => hisPer _ hb, fun v =>
      (hdiff v).comp co.differentiable.differentiableOn fun _ hb => hb⟩
    bas := bas
    sympl := hsym
    adapt := had
    h := h
    ta := ta
    norm := hnorm
    hol := hhol
    c₁ := c₁
    c₂ := c₂
    half₁ := h1
    half₂ := h2
    fr := fr
    fr_hol := hf1
    fr_ne := hf2
    fr_coc := hf3
    fr_rig := hf4
    fr_sec := hf5 }⟩

end GlobalTheory.FrameUnif
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.UnitDet

theorem eq_of_im_hermForm_eq {g : ℕ} (S : Set (Fin g → ℂ)) (hS : Submodule.span ℝ S = ⊤)
    (A B : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ z ∈ S, ∀ w ∈ S, (hermForm A z w).im = (hermForm B z w).im) : A = B := by
  have h1 : ∀ z, ∀ w ∈ S, (hermForm A z w).im = (hermForm B z w).im := by
    intro z w hw
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => exact h x hx w hw
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, add_dotProduct, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, smul_dotProduct, Complex.smul_im] at hx ⊢
      rw [hx]
  have h2 : ∀ z w, (hermForm A z w).im = (hermForm B z w).im := by
    intro z w
    have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx => exact h1 z x hx
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im] at hx ⊢
      rw [hx]
  ext i j
  have e1 := h2 (Pi.single i 1) (Pi.single j 1)
  have e2 := h2 (Pi.single i Complex.I) (Pi.single j 1)
  simp [hermForm] at e1 e2
  exact Complex.ext e2 e1

theorem hermForm_mulVec {g : ℕ} (A h : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm A (h *ᵥ z) (h *ᵥ w) = hermForm (hᵀ * (A * h.map (starRingEnd ℂ))) z w := by
  have : star (h *ᵥ w) = h.map (starRingEnd ℂ) *ᵥ star w := by
    ext a; simp [Matrix.mulVec, dotProduct]
  rw [hermForm, hermForm, this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec z, Matrix.vecMul_transpose]

theorem det_eq_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k Pf, IsPerFr e F M k Pf → ∀ x ∈ (M.X k).dom, (∀ τ i, ‖dmin (M.X k).Gm x τ i‖ = 1) → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ a b, (hermForm Hm (Pf x a) (Pf x b)).im = (F.Di k).EF a b) → Hm.det = ((∏ j, (2 * ‖relab c σ (e j).1 (M.X k).ξ0‖) : ℝ) : ℂ) := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x hx hu Hm hHm
  obtain ⟨hl1, hl2, -⟩ := GlobalTheory.T.unitFrame_eq_orthonormal_mul_triangular E r (M.X k).p0 (M.X k).Ψ (M.X k).Gm (M.X k).Gm_herm
  obtain ⟨x₀, b, hb, hgr, hb1, rfl⟩ := hl1 x hx hu
  have hx₀ : x₀ ∈ (M.X k).dom := (hl2 x₀ hgr).1
  obtain ⟨h₀, -, hh, -, -, hdet, -⟩ :=
    GlobalTheory.T.triangularFrame_moves_period_blockTriangular E H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x₀ hx₀ b hb
  replace hdet := hdet hb1
  obtain ⟨Pf', -, huniq, hper, -⟩ := GlobalTheory.T.exists_framePeriods_alt E H Dw l Xo c σ g e F r M hG hB hN k
  obtain rfl := huniq Pf hPf
  have hspan := (hper x₀ hx₀).2.2.2.1
  obtain ⟨⟨idx, hty, -, hfr⟩, hp, -, hξ, hpos, hφ⟩ := GlobalTheory.T.cmType_letter_frame_column_dictionary E H Dw l Xo c σ g e F r M hG hB hN k
  let φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hD := GlobalTheory.UnitFrame.im_hermForm_eq E H (F.Di k) r (-(M.X k).ξ0) (M.X k).Gm φ (M.X k).Ψ
    (hB.type k).2 g idx (fun j => relab c σ (e j).1) hty hξ hpos (hφ φ fun _ => rfl).2 x₀ (Pf x₀)
    (fun v j => by rw [hPf, hfr]; rfl) (fun τ => by rw [← hp]; exact hgr τ)
  have key : h₀ᵀ * (Hm * h₀.map (starRingEnd ℂ)) =
      Matrix.diagonal fun j => ((2 * ‖(idx j).1.1 (-(M.X k).ξ0)‖ : ℝ) : ℂ) := by
    refine eq_of_im_hermForm_eq _ hspan _ _ ?_
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [hD, ← hermForm_mulVec, ← hh, ← hh, hHm]
  have h1 := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
  have h2 : h₀.det * starRingEnd ℂ h₀.det = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hdet]; simp
  have h3 : Hm.det = h₀.det * (Hm.det * starRingEnd ℂ h₀.det) := by
    linear_combination (-Hm.det) * h2
  rw [h3, h1, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hty j, map_neg, norm_neg]
  split_ifs
  · rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
  · rfl

end GlobalTheory.UnitDet
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CompRat.SplitSum

theorem finrank_prod_int {E : Type} [Field E] [NumberField E] (M N : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [AddCommGroup N] [Module (𝓞 E) N] [Module.Finite (𝓞 E) M] [Module.Finite (𝓞 E) N] :
    Module.finrank (𝓞 E) (M × N) = Module.finrank (𝓞 E) M + Module.finrank (𝓞 E) N := by
  have h1 := (TensorProduct.isBaseChange (𝓞 E) (M × N) E).finrank_eq
  have h2 := (TensorProduct.isBaseChange (𝓞 E) M E).finrank_eq
  have h2' := (TensorProduct.isBaseChange (𝓞 E) N E).finrank_eq
  have h3 := (TensorProduct.prodRight (𝓞 E) E E M N).finrank_eq
  rw [← h1, h3, Module.finrank_prod, h2, h2']

def prodSubEquiv {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (A : Submodule R M) (B : Submodule R N) : (A.prod B) ≃ₗ[R] A × B where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem finrank_prod_sub {E : Type} [Field E] [NumberField E] {M N : Type} [AddCommGroup M] [Module (𝓞 E) M]
    [AddCommGroup N] [Module (𝓞 E) N] [Module.Finite (𝓞 E) M] [Module.Finite (𝓞 E) N]
    (A : Submodule (𝓞 E) M) (B : Submodule (𝓞 E) N) :
    Module.finrank (𝓞 E) (A.prod B) = Module.finrank (𝓞 E) A + Module.finrank (𝓞 E) B := by
  rw [(prodSubEquiv A B).finrank_eq, finrank_prod_int]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem splitLat_sum {D D' : Datum H} (h : SplitLat D) (h' : SplitLat D') : SplitLat (DatumSum.sumDatum D D') := by
  obtain ⟨Lp, Lm, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨Lp', Lm', h1', h2', h3', h4', h5', h6'⟩ := h'
  have := D.fin
  have := D'.fin
  have hE : ∀ x y : D.La × D'.La, (DatumSum.sumDatum D D').EF x y = D.EF x.1 y.1 + D'.EF x.2 y.2 :=
    fun x y => DatumSum.sumForm_apply D.EF D'.EF x y
  have hR : ∀ x : D.La × D'.La, (DatumSum.sumDatum D D').EF (H.rt • x) x =
      D.EF (H.rt • x.1) x.1 + D'.EF (H.rt • x.2) x.2 := fun x => hE _ _
  refine ⟨Lp.prod Lp', Lm.prod Lm', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : Lp.prod Lp' ⊔ Lm.prod Lm' = ⊤ := by
      rw [Submodule.prod_sup_prod, h1, h1', Submodule.prod_top]
    exact this
  · intro a ha b hb
    refine (hE a b).trans ?_
    rw [h2 _ ha.1 _ hb.1, h2' _ ha.2 _ hb.2, add_zero]
  · exact (finrank_prod_sub Lp Lp').trans (by rw [h3, h3']; rfl)
  · exact (finrank_prod_sub Lm Lm').trans (by rw [h4, h4']; rfl)
  · intro a ha hne
    have := hR a
    erw [this]
    push_cast
    rw [mul_add]
    by_cases h0 : a.1 = 0
    · have h0' : a.2 ≠ 0 := fun h0' => hne (Prod.ext h0 h0')
      simpa [h0] using h5' _ ha.2 h0'
    · by_cases h0' : a.2 = 0
      · simpa [h0'] using h5 _ ha.1 h0
      · exact add_pos (h5 _ ha.1 h0) (h5' _ ha.2 h0')
  · intro a ha hne
    have := hR a
    erw [this]
    push_cast
    rw [mul_add]
    by_cases h0 : a.1 = 0
    · have h0' : a.2 ≠ 0 := fun h0' => hne (Prod.ext h0 h0')
      simpa [h0] using h6' _ ha.2 h0'
    · by_cases h0' : a.2 = 0
      · simpa [h0'] using h6 _ ha.1 h0
      · exact add_neg (h6 _ ha.1 h0) (h6' _ ha.2 h0')

end GlobalTheory.CompRat.SplitSum

namespace GlobalTheory.CompRat

theorem exists_splitLat_of_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ), (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) → ∃ D₀ : Datum H, D₀.p = p ∧ D₀.q = q ∧ SplitLat D₀ := by
  intro E _ _ _ H p q ⟨D, hp, hq⟩
  refine ⟨DatumSum.sumDatum (powDatum D p) (powDatum (CM.ConjDatum.conj D) q), ?_, ?_, ?_⟩
  · change p * D.p + q * D.q = p
    simp [hp, hq]
  · change p * D.q + q * D.p = q
    simp [hp, hq]
  · refine SplitSum.splitLat_sum (GlobalTheory.T.hermitianLatticeSignatureSplit_of_definite E H _ (Or.inr ?_)) (GlobalTheory.T.hermitianLatticeSignatureSplit_of_definite E H _ (Or.inl ?_))
    · change p * D.q = 0
      simp [hq]
    · change q * D.q = 0
      simp [hq]

end GlobalTheory.CompRat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.framedPoint_eigenbasis_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S) (τ : E →+* ℂ) (w : (Sp (DualNumber T) ⟶ Xo.univ.t.G.left)), IsTanAt (spMap ψ.toRingHom ≫ y.x) w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T, IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w := by
  first | exact @GlobalTheory.Frames.eigenbasis_baseChange | exact GlobalTheory.Frames.eigenbasis_baseChange | (intros; apply GlobalTheory.Frames.eigenbasis_baseChange <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.existsUnique_linear_lift_uniformised_fibres : ∀ (X X' : Scheme.{0}) (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (y : Sp ℂ ⟶ X) (y' : Sp ℂ ⟶ X') (g g' : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (e' : (Fin g' → ℂ) → (Over.mk y' ⟶ G')) (ψ : pullback G.hom y ⟶ pullback G'.hom y') (ψp : (Over.mk y ⟶ G) →* (Over.mk y' ⟶ G')), Smooth G'.hom → (∀ z w, e (z + w) = e z * e w) → (∀ z w, e' (z + w) = e' z * e' w) → IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => (e' z).left) → ((∀ w, ∃! v : epsPt y' ⟶ G', IsDerivAt0 (fun z => (e' z).left) w v.left) ∧ ∀ v : epsPt y' ⟶ G', spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) → DiscreteTopology {z // e' z = 1} → ψ ≫ pullback.snd _ _ = pullback.snd _ _ → (∀ x, fibPt G x ≫ ψ = fibPt G' (ψp x)) → ∃! h : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), ∀ z, e' (h z) = ψp (e z) := by
  first | exact @GlobalTheory.existsUnique_linear_lift_fibre | exact GlobalTheory.existsUnique_linear_lift_fibre | (intros; apply GlobalTheory.existsUnique_linear_lift_fibre <;> assumption)
end
