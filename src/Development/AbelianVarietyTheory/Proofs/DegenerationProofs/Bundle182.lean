module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle178
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle078
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.AbelianLocus

theorem char_eq_zero_of_isProper {k : Type} [Field k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G]
    (D : E.GtDatum G) [IsProper G.hom] (a : E.X) : a = 0 := by
  have hi := D.i_hom
  have h1 := GlobalTheory.splitTorus_hom_proper_trivial_field k E.X G D.i hi
  have h2 : 𝟙 (splitTorus (Sp k) E.X) = toUnit _ ≫ η[splitTorus (Sp k) E.X] := by
    refine D.isKernel.hom_ext ?_ (toUnit_unique _ _)
    rw [Category.id_comp, Category.assoc, IsMonHom.one_hom]
    exact h1
  have h3 := Rosenlicht.torusGamma_chi k E.X a
  rw [Rosenlicht.chi, h2, Rosenlicht.coord_toUnit_comp, Rosenlicht.torusGamma_const] at h3
  by_contra ha
  have h4 := congrArg (fun f : AddMonoidAlgebra k E.X => f.coeff a) h3
  simp [Ne.symm ha] at h4

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem perp_top_eq_bot (S : ThetaSys o Ω) : S.perp ⊤ = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun a ha => ?_
  have ha' : ∀ h : S.Gam, eStd S.g _ a h = 0 := fun h => ha h trivial
  funext k
  rcases k with i | i
  · have := ha' (Pi.single (Sum.inr i) 1)
    simpa [eStd, Pi.single_apply] using this
  · have := ha' (Pi.single (Sum.inl i) 1)
    simpa [eStd, Pi.single_apply] using this

theorem proj_eq_one {T : AddSubgroup S.Gam} (h : T = ⊥) : S.proj T 0 = 1 := by
  subst h
  unfold ThetaSys.proj
  rw [finsum_unique, S.ρ_one _ (by rw [AddSubgroup.mem_bot.1 (Subtype.prop _), smul_zero])]
  simp

variable {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem exists_crd_ne_zero (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {K : Type} [Field K]
    (x : Sp K ⟶ Q.P.left) {z : M.Z} (hz : Set.range (x ≫ Q.P.hom) = {z}) (hc : IsClosed ({z} : Set M.Z))
    (hT : S.TT M z = ⊥) : ∃ v, Crd Q.O1 Q.st x v ∧ v ≠ 0 := by
  have hxz : ∀ s, Q.P.hom (x s) = z := fun s => by
    have : (x ≫ Q.P.hom) s ∈ Set.range (x ≫ Q.P.hom) := ⟨_, rfl⟩
    rw [hz] at this
    exact this
  obtain ⟨l, hl⟩ : ∃ l, z ∈ Q.W l := TopologicalSpace.Opens.mem_iSup.1 (by rw [Q.cover]; trivial)
  have hr : Set.range x ⊆ Set.range (Q.P.hom ⁻¹ᵁ Q.W l).ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    change Q.P.hom (x s) ∈ Q.W l
    rwa [hxz]
  obtain ⟨x', rfl⟩ : ∃ x', x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = x :=
    ⟨_, IsOpenImmersion.lift_fac _ x hr⟩
  have hcov := (Q.imm l).1
  have hm : x' (IsLocalRing.closedPoint K) ∈ ⨆ i ∈ (Set.univ : Set S.J), nonzeroLocus (Q.σ l i) := by
    rw [hcov]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, -, hi⟩ := hm
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  obtain ⟨w, hw⟩ : ∃ w, Crd _ (Q.σ l) x' w :=
    ⟨_, m, 1, (CrdCalc.top_le_iff x' _).2 (Scheme.basicOpen_le _ _ hm), fun _ => rfl⟩
  have hwi := ((CrdCalc.crd_isUnit_iff i hw).2 ((CrdCalc.top_le_iff x' _).2 hi)).ne_zero
  refine ⟨_, Q.rel l K x' _ hw, fun h0 => hwi ?_⟩
  have hBm : ∀ a b, Q.B l a b ∈ M.O z := fun a => hB.zero z hc _
    (by rw [Q.basis l z hl]; exact Submodule.subset_span ⟨a, rfl⟩)
    (by rw [proj_eq_one hT, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec])
  let B' : Matrix S.J S.J (M.O z) := fun a b => ⟨_, hBm a b⟩
  let C' : Matrix S.J S.J (M.O z) := fun a b => ⟨_, RatModel.valF_mem_O hl (Q.c l a b)⟩
  have h1 : C' * B' = 1 := by
    apply Matrix.map_injective (f := (M.O z).val.toRingHom) Subtype.val_injective
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Q.c_inv l
  have h2 := congrArg (fun A => A.map (RatModel.valHom _ z hz)) (mul_eq_one_comm.1 h1)
  beta_reduce at h2
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  have h3 : C'.map (RatModel.valHom _ z hz) =
      (Q.c l).map (valR (x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (Q.W l)) := by
    ext a b
    rw [← Category.assoc]
    exact RatModel.val_valF (by rw [hz]; exact Set.singleton_subset_iff.2 hl) _
  have h4 : w = 0 := by
    rw [← Matrix.one_mulVec w, ← h2, ← Matrix.mulVec_mulVec, h3, h0, Matrix.mulVec_zero]
  rw [h4]; rfl

theorem mem_G [ArithBase o Ω] (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (w : Q.P.left)
    (hw : IsClosed ({w} : Set Q.P.left)) (hT : S.TT M (Q.P.hom w) = ⊥) : w ∈ Q.G := by
  have := Q.proper
  have hc : IsClosed ({Q.P.hom w} : Set M.Z) := by
    rw [← Set.image_singleton]
    exact Q.P.hom.isClosedMap _ hw
  let x : Sp (Q.P.left.residueField w) ⟶ Q.P.left := Q.P.left.fromSpecResidueField w
  have hx : ∀ s, x s = w := fun s => Scheme.fromSpecResidueField_apply w s
  have hz : Set.range (x ≫ Q.P.hom) = {Q.P.hom w} := by
    rw [RatModel.range_eq_singleton _ (IsLocalRing.closedPoint _)]
    exact congrArg (fun a => {Q.P.hom a}) (hx _)
  obtain ⟨v, hv, hv0⟩ := exists_crd_ne_zero hB Q x hz hc hT
  have h := (OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q _ x _
    (Spec.preimage (x ≫ Q.P.hom ≫ M.s)).hom v hz (Or.inl hc) (Spec.map_preimage _).symm hv).2 (by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
      refine ⟨i, ?_⟩
      rw [proj_eq_one hT, Finset.sum_eq_single i]
      · simpa using hi
      · intro j _ hj
        simp [hj]
      · simp)
  rw [← hx (IsLocalRing.closedPoint _)]
  exact (CrdCalc.top_le_iff x _).1 h

theorem abelian_locus : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.Fib → IsOpen {z : M.Z | S.TT M z = ⊥} ∧ (∀ w : Q.P.left, IsClosed ({w} : Set Q.P.left) → S.TT M (Q.P.hom w) = ⊥ → w ∈ Q.G) ∧ ∀ z : M.Z, IsClosed ({z} : Set M.Z) → S.TT M z ≠ ⊥ → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (τ : ex.core.Test y), y (GlobalTheory.ZJ.cPt p) = z ∧ ¬ IsProper (pullback.snd τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j)) := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hbig hgeo _
  refine ⟨isOpen_iff_forall_mem_open.2 fun z hz => ⟨_, fun z' h => ?_, OpenPart.isOpen_supI_subset (S := S) z,
    fun _ h => h⟩, mem_G hB Q, fun z hz hT => ?_⟩
  · exact le_bot_iff.1 ((OpenPart.TT_le_TT h).trans (le_of_eq hz))
  obtain ⟨h1, h2⟩ := GlobalTheory.T.exists_geometricTest_map_classicalPoint hL o Ω S ρ M U₀ EE hB Q hbig hgeo
  obtain ⟨p, hp, y, hy⟩ := h2 z hz
  obtain ⟨y₀, t, c, ⟨tm⟩⟩ := h1 p y hy.2
  obtain ⟨τ, e, he, -⟩ := GlobalTheory.T.exists_uniformisationTest_of_geometricTest hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t c tm hbig
  refine ⟨p, hp, y, τ, hy.1, fun hpr => hT ?_⟩
  have : IsProper t.mod.Φ.G.hom := by
    rw [← he] at hpr
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).1 hpr
  have h0 := char_eq_zero_of_isProper t.mod.Φ.E t.mod.Φ.G t.mod.Φ.D
  obtain ⟨e', -⟩ := t.mt
  have hk : t.τ.yy.ker = ⊤ := by
    refine top_unique fun a _ => ?_
    obtain ⟨α, hα⟩ := QuotientAddGroup.mk_surjective (t.τ.yy a)
    have : α = 0 := (e'.trans t.mod.xe.symm).map_eq_zero_iff.1 (h0 _)
    rw [AddMonoidHom.mem_ker, ← hα, this]
    rfl
  rw [ThetaSys.TT, hB.atTest z p y y₀ t.τ hy c.at_, hk, perp_top_eq_bot]

end GlobalTheory.ZH.AbelianLocus
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory

theorem ZJ.Core.Test.exists_fibre_immersion {C : ZJ.Core} (hF : C.Fib) {p : ℕ} [Fact p.Prime]
    {y : Sp (ZJ.OO p) ⟶ C.Z} (τ : C.Test y) :
    ∃ h : pullback τ.H.hom (ZJ.rPt p ≫ spMap τ.j) ⟶ pullback C.GG.hom (ZJ.rPt p ≫ y),
      h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f ∧ h ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      IsClosedImmersion h ∧ Set.range h = Set.univ := by
  have w : (pullback.fst τ.H.hom (ZJ.rPt p ≫ spMap τ.j) ≫ τ.f) ≫ C.GG.hom =
      pullback.snd τ.H.hom (ZJ.rPt p ≫ spMap τ.j) ≫ ZJ.rPt p ≫ y := by
    rw [Category.assoc, τ.f_over, pullback.condition_assoc, Category.assoc, τ.fac]
  let h := pullback.lift _ _ w
  have h₁ : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
  have h₂ : h ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hc := τ.imm h h₁ h₂
  refine ⟨h, h₁, h₂, hc, ?_⟩
  have := (ZJ.kb_isAlgClosed_and_conj p).1
  have := (ZJ.core_basic C).2.1
  let s := pullback.snd C.GG.hom (ZJ.rPt p ≫ y)
  have : JacobsonSpace ↥(pullback C.GG.hom (ZJ.rPt p ≫ y)) := LocallyOfFiniteType.jacobsonSpace s
  rw [← Set.univ_subset_iff, ← closure_closedPoints, h.isClosedEmbedding.isClosed_range.closure_subset_iff]
  intro x hx
  obtain ⟨z, hz, hzx⟩ : ∃ z : Sp (ZJ.kb p) ⟶ pullback C.GG.hom (ZJ.rPt p ≫ y),
      z ≫ pullback.snd _ _ = 𝟙 _ ∧ ∀ q, z q = x :=
    ⟨pointOfClosedPoint s x hx, pointOfClosedPoint_comp s x hx, pointOfClosedPoint_apply s x hx⟩
  obtain ⟨c, hc₁, hc₂⟩ := hF p y τ (z ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, reassoc_of% hz])
  have e : pullback.lift c (𝟙 _) (hc₁.trans (Category.id_comp _).symm) ≫ h = z := by
    apply pullback.hom_ext
    · rw [Category.assoc, h₁, pullback.lift_fst_assoc, hc₂]
    · rw [Category.assoc, h₂, pullback.lift_snd, hz]
  exact ⟨pullback.lift c (𝟙 _) (hc₁.trans (Category.id_comp _).symm) (IsLocalRing.closedPoint (ZJ.kb p)),
    (congrArg (fun g => g (IsLocalRing.closedPoint (ZJ.kb p))) e).trans (hzx _)⟩

theorem ZJ.Core.Test.exists_isGt_special {C : ZJ.Core} {p : ℕ} [Fact p.Prime]
    {y : Sp (ZJ.OO p) ⟶ C.Z} (τ : C.Test y) :
    ∃ E : SplitExt (Sp (ZJ.kb p)), E.IsGt ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H) := by
  have := τ.j_loc
  have hr : Set.range (ZJ.rPt p ≫ spMap τ.j) = {IsLocalRing.closedPoint τ.V} := by
    have h : ∀ q, (ZJ.rPt p ≫ spMap τ.j) q = IsLocalRing.closedPoint τ.V := fun q => by
      rw [Subsingleton.elim q (IsLocalRing.closedPoint (ZJ.kb p))]
      exact (congrArg (PrimeSpectrum.comap τ.j)
        (IsLocalRing.comap_closedPoint (IsLocalRing.residue (ZJ.OO p)))).trans (IsLocalRing.comap_closedPoint τ.j)
    exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint (ZJ.kb p), h _⟩, by
      rintro _ ⟨q, rfl⟩
      exact h q⟩
  obtain ⟨G₁, _, _, E, φ, hE, hφ⟩ := τ.exists_isGt_fibre _ _ hr
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback τ.H _)
  exact ⟨E, isGt_of_iso e hE⟩

theorem ZH.Clos.TMap.eSec_comp_f {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} {Q : Clos ρ M U₀ EE} (ex : Q.Ext) {p : ℕ} [Fact p.Prime]
    {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u} (tm : Q.TMap t c) :
    (eSec t.u.G ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι : Sp t.u.V ⟶ Q.P.left) = c.yV ≫ ex.e ≫ Q.G.ι := by
  have := Q.proper
  have : IsDominant (Out.jK t.u.V) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    rw [CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective t.u.V _)]
    exact bot_le)⟩
  obtain ⟨e₁, he₁, s₁⟩ : ∃ e₁ : Sp t.u.V ⟶ t.u.G.left, e₁ = eSec t.u.G ∧ e₁ ≫ t.u.G.hom = 𝟙 _ :=
    ⟨_, rfl, Over.w η[t.u.G]⟩
  obtain ⟨e₂, he₂, s₂⟩ : ∃ e₂ : Sp (FractionRing t.u.V) ⟶ pullback t.u.G.hom (jK t.u.V),
      e₂ = eSec ((Over.pullback (jK t.u.V)).obj t.u.G) ∧ e₂ ≫ pullback.snd _ _ = 𝟙 _ :=
    ⟨_, rfl, Over.w η[(Over.pullback (jK t.u.V)).obj t.u.G]⟩
  obtain ⟨e₃, he₃, s₃⟩ : ∃ e₃ : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀,
      e₃ = eSec ((Over.pullback Q.u₀).obj ρ.P.A) ∧ e₃ ≫ pullback.snd _ _ = 𝟙 _ :=
    ⟨_, rfl, Over.w η[(Over.pullback Q.u₀).obj ρ.P.A]⟩
  obtain ⟨e₄, he₄⟩ : ∃ e₄ : Sp S.R ⟶ ρ.P.A.left, e₄ = eSec ρ.P.A := ⟨_, rfl⟩
  have h₂ : e₂ ≫ pullback.fst _ _ = jK t.u.V ≫ e₁ := by
    subst he₁ he₂
    exact ZJ.eSec_comp_of_isGrpPullback (isGrpPullback_pullback t.u.G (jK t.u.V))
  have h₃ : e₃ ≫ pullback.fst _ _ = Q.u₀ ≫ e₄ := by
    subst he₃ he₄
    exact ZJ.eSec_comp_of_isGrpPullback (isGrpPullback_pullback ρ.P.A Q.u₀)
  have h₄ : e₂ ≫ t.u.U.gen.hom.left ≫ t.u.φ = spMap t.u.yK ≫ e₄ := by
    subst he₂ he₄
    have := t.u.U.gen_hom
    exact ZJ.eSec_comp_of_isGrpPullback
      (((isGrpPullback_of_iso t.u.U.gen).comp t.u.cart).congr (Category.id_comp _) rfl)
  have h₅ : U₀.ι ≫ ex.e = e₃ ≫ ex.a := he₃ ▸ ex.e_zero
  have h₆ : e₂ ≫ tm.φ = c.yK ≫ e₃ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, tm.φ_fst, h₃, reassoc_of% c.yK_u]
      exact h₄
    · rw [Category.assoc, Category.assoc, tm.φ_snd, s₃, reassoc_of% s₂, Category.comp_id]
  rw [← he₁]
  refine ext_of_isDominant_of_isSeparated Q.P.hom ?_ (Out.jK t.u.V) ?_
  · simp only [Category.assoc]
    rw [tm.f_over, ex.e_sec, reassoc_of% s₁, Category.comp_id]
  · rw [← reassoc_of% c.yK_fac, reassoc_of% h₅, ex.a_eq, ← reassoc_of% h₆, tm.φ_f, reassoc_of% h₂]

theorem ZH.exists_iso_special_fibre_of_test : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c) (τ : ex.core.Test y), S.Big → ex.core.Fib → ∃ e : (Over.pullback (GlobalTheory.ZJ.rPt p ≫ spMap τ.j)).obj τ.H ≅ t.mod.Φ.G, IsMonHom e.hom ∧ e.hom.left ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex p _ y y₀ t c tm τ hS hF
  obtain ⟨τ₀, e₀, he₁, he₂⟩ := GlobalTheory.T.exists_uniformisationTest_of_geometricTest hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t c tm hS
  obtain ⟨h, h₁, h₂, hc, hr⟩ := τ.exists_fibre_immersion hF
  obtain ⟨h₀, h₀₁, h₀₂, hc₀, hr₀⟩ := τ₀.exists_fibre_immersion hF
  obtain ⟨E, hE⟩ := τ.exists_isGt_special
  have := (ZJ.kb_isAlgClosed_and_conj p).1
  have : IsCommMonObj ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H) := Functor.isCommMonObj_obj
  let Y : Over (Sp (ZJ.kb p)) := Over.mk (pullback.snd ex.core.GG.hom (ZJ.rPt p ≫ y))
  let f : (Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H ⟶ Y := Over.homMk h h₂
  have w : (e₀.inv ≫ h₀) ≫ pullback.snd _ _ = t.mod.Φ.G.hom := by
    rw [Category.assoc, h₀₂, ← he₁, Iso.inv_hom_id_assoc]
  let f' : t.mod.Φ.G ⟶ Y := Over.homMk (e₀.inv ≫ h₀) w
  have k : (e₀.inv ≫ h₀) ≫ pullback.fst _ _ ≫ Q.G.ι = t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := by
    rw [Category.assoc, Iso.inv_comp_eq, he₂]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Q.G.ι) h₀₁).trans (Category.assoc _ _ _))
  have k' : h ≫ pullback.fst _ _ ≫ Q.G.ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Q.G.ι) h₁).trans (Category.assoc _ _ _))
  have hr' : Set.range (e₀.inv ≫ h₀) = Set.univ := by
    rw [Set.range_eq_univ] at hr₀ ⊢
    exact hr₀.comp e₀.inv.surjective
  have hone : η[(Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H] ≫ f = η[t.mod.Φ.G] ≫ f' := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · refine (cancel_mono Q.G.ι).1 ?_
      have u₁ := ZJ.eSec_comp_of_isGrpPullback (isGrpPullback_pullback τ.H (ZJ.rPt p ≫ spMap τ.j))
      have u₂ := ZJ.eSec_comp_of_isGrpPullback t.mod.cart
      have v₁ : eSec ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H) ≫ pullback.fst _ _ ≫ τ.f ≫ Q.G.ι =
          (ZJ.rPt p ≫ y ≫ ex.e ≫ Q.G.ι : Sp (ZJ.kb p) ⟶ Q.P.left) := by
        refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ τ.f ≫ Q.G.ι) u₁)).trans ?_
        have a := congrArg (fun g => ZJ.rPt p ≫ spMap τ.j ≫ g ≫ Q.G.ι) τ.eSec_comp_f
        exact a.trans (congrArg (fun g => ZJ.rPt p ≫ g ≫ ex.e ≫ Q.G.ι) τ.fac)
      have v₂ : eSec t.mod.Φ.G ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι =
          (ZJ.rPt p ≫ y ≫ ex.e ≫ Q.G.ι : Sp (ZJ.kb p) ⟶ Q.P.left) := by
        refine ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) u₂)).trans ?_
        have a := congrArg (fun g => ZJ.rPt p ≫ spMap t.u.j ≫ g) (tm.eSec_comp_f ex)
        simp only [Category.assoc] at a ⊢
        rw [reassoc_of% c.fac] at a
        exact a
      rw [← k'] at v₁
      rw [← k] at v₂
      exact v₁.trans v₂.symm
    · exact (Over.w _).trans (Over.w _).symm
  obtain ⟨e, he, hef⟩ := exists_iso_isMonHom_of_isGt_of_range_eq (ZJ.kb p) Y E t.mod.Φ.E _ _ f f' hE ⟨t.mod.Φ.D⟩ hc
    (inferInstanceAs (IsClosedImmersion (e₀.inv ≫ h₀))) (hr.trans hr'.symm) hone
  refine ⟨e, he, ?_⟩
  have hl : e.hom.left ≫ e₀.inv ≫ h₀ = h := congrArg (fun g => g.left) hef
  rw [← k, ← k', ← hl]
  simp only [Category.assoc]

end GlobalTheory
end
