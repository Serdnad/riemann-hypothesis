module

public import Development.EtaleCohomology.EtaleSheaves.Bundle029
public import Development.EtaleCohomology.EtaleSheaves.Bundle013
public import Development.EtaleCohomology.TateTwists.Bundle002
public import Development.EtaleCohomology.TateTwists.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle029
public import Development.EtaleCohomology.TateTwists.Bundle013
public import Development.EtaleCohomology.TateTwists.ExistsNaturalEtaleKummerDegreeOneValueOfRootsKum
public import Development.EtaleCohomology.EtaleSheaves.Bundle030
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.EtaleCohomology.EtaleSheaves.Bundle005
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.EtaleSheaves.Bundle031
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Development.EtaleCohomology.TateTwists.Bundle019
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor

theorem kumT_ex_of (hk : LateralTheory.E.CupProductRingLaws.LeafKumTExists) : LateralTheory.EtaleFoundations.EtaleKummerTriangleExists := by
  intro q _
  unfold kumT
  exact pick_spec (hk q)

theorem prim_loc_of (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally :=
  LateralTheory.EtaleFoundations.etale_locally_roots_of_unity_structure_of_exists_and_kummer LateralTheory.EtaleFoundations.etale_locally_exists_primitive_root_of_unity_of_invertible_order hr

theorem etale_kummer_chern_edge_values_exist_of_local_roots_and_kummer_torsor (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) (hk : LateralTheory.E.CupProductRingLaws.LeafKumTExists) :
    LateralTheory.E.ChernClassExistence.EtaleKummerChernEdgeValuesExistNatural :=
  LateralTheory.EtaleFoundations.exists_natural_etale_kummer_degree_one_value_of_roots_kummer_gluing (prim_loc_of hr) (kumT_ex_of hk) LateralTheory.EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf

end LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.DescentPf

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (h ≫ g) x = Sec.res h (Sec.res g x) := by
  simp [Sec.res]

theorem val_smul {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}} (c : ZMod q) (x : Sec (tw q i) U) :
    c.val • x = (ULift.up c : ULift.{1} (ZMod q)) • x := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  congr 1
  apply ULift.ext
  rw [ULift.down_natCast, ZMod.natCast_zmod_val]

theorem Descent_of (hAC : LateralTheory.E.LCBijPf.TwGenNZAC) : LateralTheory.E.LCSurjPf.Descent := by
  intro q _ i m hm B _ ζ y hloc
  obtain ⟨S, hS, hP⟩ := hloc
  have hform : ∀ {V W : Scheme.{0}} (g : V ⟶ Spec (CommRingCat.of B)) (h : W ⟶ V) (c : ZMod q),
      Sec.res g y = c.val • twGen i ((gam ζ).map g.appTop.hom) →
      Sec.res (h ≫ g) y = c.val • twGen i ((gam ζ).map (h ≫ g).appTop.hom) := by
    intro V W g h c hc
    have hs : ∀ x : Sec (tw q i) V, Sec.res h (c.val • x) = c.val • Sec.res h x := fun x => map_nsmul _ _ x
    rw [res_comp, hc, hs, LateralTheory.E.LCBijPf.twGen_res]
    rfl
  have huniq : ∀ {V1 V2 : Scheme.{0}} (g1 : V1 ⟶ Spec (CommRingCat.of B)) (g2 : V2 ⟶ Spec (CommRingCat.of B))
      (c1 c2 : ZMod q), Sec.res g1 y = c1.val • twGen i ((gam ζ).map g1.appTop.hom) →
      Sec.res g2 y = c2.val • twGen i ((gam ζ).map g2.appTop.hom) →
      ∀ v1 v2, g1 v1 = g2 v2 → c1 = c2 := by
    intro V1 V2 g1 g2 c1 c2 h1 h2 v1 v2 hv
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v1 v2 hv
    let A := (pullback g1 g2).affineOpenCover
    obtain ⟨w, -⟩ := A.covers z
    let a := A.f (A.idx z)
    have e1 := hform g1 (a ≫ pullback.fst g1 g2) c1 h1
    have e2 := hform g2 (a ≫ pullback.snd g1 g2) c2 h2
    have hcomp : (a ≫ pullback.snd g1 g2) ≫ g2 = (a ≫ pullback.fst g1 g2) ≫ g1 := by
      simp [pullback.condition]
    rw [hcomp] at e2
    have hne : Nontrivial (A.X (A.idx z)) := PrimeSpectrum.nontrivial w
    obtain ⟨φ, hφ⟩ := Spec.map_surjective ((a ≫ pullback.fst g1 g2) ≫ g1)
    have key := LateralTheory.E.LCBijPf.twGenNZ_of hAC q i (A.X (A.idx z)) (ζ.map φ.hom) (c1 - c2)
    refine sub_eq_zero.1 (key ?_)
    have e := e1.symm.trans e2
    rw [← hφ] at e
    rw [LateralTheory.E.LCBijPf.gam_map]
    rw [val_smul, val_smul] at e
    have hup : (ULift.up (c1 - c2) : ULift.{1} (ZMod q)) = ULift.up c1 - ULift.up c2 := rfl
    rw [val_smul, hup, sub_smul, sub_eq_zero]
    exact e
  obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
  have hpiece : ∀ x : PrimeSpectrum B, ∃ (R : CommRingCat.{0}) (g : Spec R ⟶ Spec (CommRingCat.of B)),
      Etale g ∧ S.arrows g ∧ x ∈ Set.range g := by
    intro x
    obtain ⟨j, v, hv⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 x
    let A := (𝒰.X j).affineOpenCover
    obtain ⟨w, hw⟩ := A.covers v
    have : Etale (𝒰.f j) := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).2 j
    refine ⟨A.X (A.idx v), A.f (A.idx v) ≫ 𝒰.f j, inferInstance, S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk j)) _, ⟨w, ?_⟩⟩
    rw [Scheme.Hom.comp_apply, hw, hv]
  choose R g hg hSg hx using hpiece
  have hc : ∀ x, ∃ c : ZMod q, Sec.res (g x) y = c.val • twGen i ((gam ζ).map (g x).appTop.hom) :=
    fun x => hP _ _ (hSg x)
  choose c hc using hc
  have key : ∀ (x : PrimeSpectrum B) {V : Scheme.{0}} (g' : V ⟶ Spec (CommRingCat.of B)) (c' : ZMod q),
      Sec.res g' y = c'.val • twGen i ((gam ζ).map g'.appTop.hom) → ∀ v, g' v = x → c x = c' := by
    intro x V g' c' h' v hv
    obtain ⟨u, hu⟩ := hx x
    exact huniq (g x) g' _ _ (hc x) h' u v (hu.trans hv.symm)
  have hlc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    have := hg x
    refine ⟨Set.range (g x), (g x).isOpenMap.isOpen_range, hx x, fun x' hx' => ?_⟩
    obtain ⟨u, hu⟩ := hx'
    exact key x' (g x) (c x) (hc x) u hu
  let ψ : LocallyConstant (PrimeSpectrum B) (ZMod q) := ⟨c, hlc⟩
  refine ⟨ψ, Sieve.ofArrows (fun x => Spec (R x)) g, ?_, ?_⟩
  · exact Scheme.Cover.mem_grothendieckTopology
      (Scheme.Cover.mkOfCovers (P := @Etale) (PrimeSpectrum B) (fun x => Spec (R x)) g
        (fun x => by obtain ⟨u, hu⟩ := hx x; exact ⟨x, u, hu⟩) hg)
  · intro V k hk
    obtain ⟨W, h, k', hk', rfl⟩ := hk
    obtain ⟨x⟩ := hk'
    rw [res_comp, res_comp]
    congr 1
    rw [hc x]
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (g x)
    have hlc' : lcMap φ.hom ψ = LocallyConstant.const _ (c x) := by
      ext u
      exact key _ (g x) (c x) (hc x) u (by rw [← hφ]; rfl)
    have e := hm.1 B (R x) φ.hom ζ ψ
    rw [hlc', hm.2, LateralTheory.E.LCBijPf.gam_map] at e
    rw [← hφ]
    exact e.symm

end LateralTheory.E.DescentPf
end
end

section

noncomputable section

namespace LateralTheory.E.LChartPf

def IdemLiftInt (A : Type) [CommRing A] (I : Ideal A) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (ε : B ⧸ I.map (algebraMap A B)), IsIdempotentElem ε →
    ∃ e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = ε

def LIdemLift : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I], IdemLiftInt A I

def LSurjChart : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A), I ≤ Ideal.jacobson ⊥ → IdemLiftInt A I →
  ∀ (A' : Type) [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I),
  ∃ g : A', IsUnit (φ g) ∧ Function.Surjective (algebraMap A (Localization.Away g))

theorem isStandardEtale_of_surjective (A : Type) [CommRing A] (A' : Type) [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (g : A') (hs : Function.Surjective (algebraMap A (Localization.Away g))) :
    Algebra.IsStandardEtale A (Localization.Away g) :=
  Algebra.IsStandardEtale.of_surjective (S := A) (Algebra.ofId A _) hs

theorem LChart_of (h1 : LIdemLift) (h2 : LSurjChart) : LateralTheory.E.LEtaleLiftPf.LChart := by
  intro A _ I _ A' _ _ _ φ
  obtain ⟨g, hg, hs⟩ := h2 A I (by simpa only [Ideal.jacobson_bot] using
    (HenselianRing.jac : I ≤ Ring.jacobson A)) (h1 A I) A' φ
  exact ⟨g, hg, isStandardEtale_of_surjective A A' g hs⟩

end LateralTheory.E.LChartPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.LeafDescendChainPf

def PreChain {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) {C0 C1 C2 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0)
    (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2) : Prop :=
  (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) ∧
  (LocallyOfFinitePresentation (d1 ≫ q) ∧ QuasiCompact (d1 ≫ q) ∧ QuasiSeparated (d1 ≫ q)) ∧
  (LocallyOfFinitePresentation (d2 ≫ d1 ≫ q) ∧ QuasiCompact (d2 ≫ d1 ≫ q) ∧ QuasiSeparated (d2 ≫ d1 ≫ q)) ∧
  IsPullback v0 c0 q (toR R) ∧ IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (toR R) ∧
  IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (toR R) ∧ γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2

def LeafDescendFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {C0 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω), IsCurve c0 → ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1),
    IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2), PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2

end LateralTheory.E.LeafDescendChainPf

end
end

section

open AlgebraicGeometry CategoryTheory LateralTheory.E.E4 Topology

namespace LateralTheory.E.LeafDimOpenPf

theorem dim_mono {X : Type*} [TopologicalSpace X] {S T : Set X} (h : S ⊆ T) :
    topologicalKrullDim S ≤ topologicalKrullDim T :=
  (IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

theorem dim_basicOpen (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (g : A) (hg : g ≠ 0) {n : ℕ} (hn : Algebra.trdeg k A = n) :
    topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) = n := by
  let B := Localization.Away g
  have hle : Submonoid.powers g ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors hg
  have : IsDomain B := IsLocalization.isDomain_localization hle
  have : Algebra.FiniteType A B := inferInstance
  have : Algebra.FiniteType k B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective B hle)
  have : Algebra.IsAlgebraic A B := IsLocalization.isAlgebraic B (Submonoid.powers g)
  have htr : Algebra.trdeg k B = n := by
    rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top k A B, hn]
  rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
      (PrimeSpectrum.localization_away_isOpenEmbedding B g).isEmbedding
      (PrimeSpectrum.localization_away_comap_range B g),
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, GlobalTheory.ringKrullDim_eq_of_trdeg_eq k B htr]

theorem LeafDimOpen_of : LateralTheory.E.LeafCloseBCut.LeafDimOpen := by
  intro k _ X b _ hX U hU hne
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨A0, _, _, _, _, _, j0, _, ⟨p0, hp0⟩, -, htr0⟩ := GlobalTheory.exists_affine_chart_trdeg_eq b x0
  obtain ⟨n, -, htn⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k A0
  have hK := htr0.symm.trans htn
  have hup : topologicalKrullDim X ≤ n := by
    refine GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
    obtain ⟨A, _, _, _, _, _, j, _, hx, -, htr⟩ := GlobalTheory.exists_affine_chart_trdeg_eq b x
    refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, hx, le_of_eq ?_⟩
    rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding j.isOpenEmbedding.isEmbedding rfl]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans
      (GlobalTheory.ringKrullDim_eq_of_trdeg_eq k A (htr.trans hK))
  refine hup.trans ?_
  have hVo : IsOpen (j0 ⁻¹' U) := hU.preimage j0.isOpenEmbedding.continuous
  have hpV : p0 ∈ j0 ⁻¹' U := by simpa [Set.mem_preimage, hp0] using hx0
  obtain ⟨_, ⟨g, rfl⟩, hpg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpV hVo
  have hg : g ≠ 0 := by
    rintro rfl; exact (PrimeSpectrum.mem_basicOpen _ _).mp hpg (Ideal.zero_mem _)
  have hd := dim_basicOpen k A0 g hg htn
  calc (n : WithBot ℕ∞) = topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A0)) := hd.symm
    _ = topologicalKrullDim (j0 '' (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A0))) :=
      (GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
        (j0.isOpenEmbedding.isEmbedding.comp IsEmbedding.subtypeVal)
        (by rw [Set.range_comp]; exact congrArg _ Subtype.range_coe)).symm
    _ ≤ topologicalKrullDim U := dim_mono (by rintro _ ⟨q, hq, rfl⟩; exact hsub hq)

end LateralTheory.E.LeafDimOpenPf
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.LocFormPf

instance ls (q : ℕ) (i : ℤ) : Presheaf.IsLocallySurjective Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) :=
  Presheaf.isLocallySurjective_toSheafify'.{0, 1} (J := Scheme.etaleTopology.{0}) (Scheme.Γ ⋙ twF q i)

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hS'⟩ := hP
  obtain ⟨T, hT, hT'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hS' V g hg.1, hT' V g hg.2⟩⟩

theorem loc_trans {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (hP : ∀ (V W : Scheme.{0}) (k : W ⟶ V) (g : V ⟶ U), P V g → P W (k ≫ g))
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P := by
  obtain ⟨S, hS, hS'⟩ := h
  let R : Sieve U := { arrows := fun V g => P V g, downward_closed := fun {V W g} hg k => hP V W k g hg }
  refine ⟨R, Scheme.etaleTopology.transitive hS R fun V g hg => ?_, fun V g hg => hg⟩
  obtain ⟨T, hT, hT'⟩ := hS' V g hg
  exact Scheme.etaleTopology.superset_covering (fun W k hk => hT' W k hk) hT

theorem res_comp {R : Type} [CommRing R] (F : Shv R) {X W V : Scheme.{0}} (k : X ⟶ W) (h : W ⟶ V) (s : Sec F V) :
    Sec.res (k ≫ h) s = Sec.res k (Sec.res h s) := by
  show (F.obj.map (k ≫ h).op).hom s = (F.obj.map k.op).hom ((F.obj.map h.op).hom s)
  rw [op_comp, Functor.map_comp]
  rfl

theorem prim_map_comp {q : ℕ} {X W V : Scheme.{0}} (k : X ⟶ W) (h : W ⟶ V) (ζ : Prim q Γ(V, ⊤)) :
    ζ.map (k ≫ h).appTop.hom = (ζ.map h.appTop.hom).map k.appTop.hom := by
  apply Subtype.ext
  show (k ≫ h).appTop.hom ζ.1 = k.appTop.hom (h.appTop.hom ζ.1)
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem sec_res (q : ℕ) (i : ℤ) {W V : Scheme.{0}} (h : W ⟶ V) (x : (twF q i).obj Γ(V, ⊤)) :
    Sec.res h (ofRings.sec (twF q i) V x) = ofRings.sec (twF q i) W ((twF q i).map (Scheme.Γ.map h.op) x) := by
  unfold Sec.res ofRings.sec
  erw [← ModuleCat.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply]

def Q (q : ℕ) (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U) (V : Scheme.{0}) (g : V ⟶ U) : Prop :=
  ∃ c : ULift.{1} (ZMod q), Sec.res g y = c • twGen i (ζ.map g.appTop.hom)

theorem Q_stable (q : ℕ) (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U)
    (V W : Scheme.{0}) (k : W ⟶ V) (g : V ⟶ U) (hg : Q q i ζ y V g) : Q q i ζ y W (k ≫ g) := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨c, ?_⟩
  rw [res_comp, hc, prim_map_comp, ← LateralTheory.E.LCBijPf.twGen_res q i k (ζ.map g.appTop.hom)]
  exact LinearMap.map_smul ((tw q i).obj.map k.op).hom c _

end LateralTheory.E.LocFormPf

namespace LateralTheory.E.LocFormPf

theorem sec_add (q : ℕ) (i : ℤ) (V : Scheme.{0}) (x y : (twF q i).obj Γ(V, ⊤)) :
    ofRings.sec (twF q i) V (x + y) = ofRings.sec (twF q i) V x + ofRings.sec (twF q i) V y := by
  unfold ofRings.sec; exact map_add _ _ _

theorem sec_smul (q : ℕ) (i : ℤ) (V : Scheme.{0}) (c : ULift.{1} (ZMod q)) (x : (twF q i).obj Γ(V, ⊤)) :
    ofRings.sec (twF q i) V (c • x) = c • ofRings.sec (twF q i) V x := by
  unfold ofRings.sec; exact map_smul _ _ _

theorem sec_zero (q : ℕ) (i : ℤ) (V : Scheme.{0}) : ofRings.sec (twF q i) V 0 = 0 := by
  unfold ofRings.sec; exact map_zero _

def S (q : ℕ) (i : ℤ) (V : Scheme.{0}) (f : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) : Sec (tw q i) V :=
  ofRings.sec (twF q i) V (Submodule.Quotient.mk f)

theorem S_zero (q : ℕ) (i : ℤ) (V : Scheme.{0}) : S q i V 0 = 0 := sec_zero q i V

theorem S_add (q : ℕ) (i : ℤ) (V : Scheme.{0}) (f g : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) :
    S q i V (f + g) = S q i V f + S q i V g :=
  sec_add q i V (Submodule.Quotient.mk f) (Submodule.Quotient.mk g)

theorem S_smul (q : ℕ) (i : ℤ) (V : Scheme.{0}) (a : ULift.{1} (ZMod q)) (f : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) :
    S q i V (a • f) = a • S q i V f :=
  sec_smul q i V a (Submodule.Quotient.mk f)

theorem S_single (q : ℕ) (i : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) (a : ULift.{1} (ZMod q)) :
    S q i V (Finsupp.single ζ a) = a • twGen i ζ := by
  have h3 : Finsupp.single ζ a = a • Finsupp.single ζ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h3, S_smul]
  rfl

theorem S_res_single (q : ℕ) (i : ℤ) {W V : Scheme.{0}} (k : W ⟶ V) (ξ : Prim q Γ(V, ⊤)) (a : ULift.{1} (ZMod q)) :
    Sec.res k (S q i V (Finsupp.single ξ a)) = S q i W (Finsupp.single (ξ.map k.appTop.hom) a) := by
  refine (sec_res q i k _).trans ?_
  unfold S
  congr 1
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map k.op).hom) (Finsupp.single ξ a)) = _
  erw [Finsupp.mapDomain_single]
  rfl

theorem S_rel (q : ℕ) (i : ℤ) (W : Scheme.{0}) (ζ ξ : Prim q Γ(W, ⊤)) (e : (ZMod q)ˣ) (he : ξ.1 = ζ.1 ^ (e : ZMod q).val) :
    S q i W (Finsupp.single ξ 1) = S q i W (Finsupp.single ζ (ULift.up ((e ^ i : (ZMod q)ˣ) : ZMod q))) := by
  unfold S
  congr 1
  exact (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, e, he, rfl⟩)

theorem res_add {q : ℕ} (i : ℤ) {W V : Scheme.{0}} (k : W ⟶ V) (x y : Sec (tw q i) V) :
    Sec.res k (x + y) = Sec.res k x + Sec.res k y := map_add _ _ _

theorem res_smul {q : ℕ} (i : ℤ) {W V : Scheme.{0}} (k : W ⟶ V) (c : ULift.{1} (ZMod q)) (x : Sec (tw q i) V) :
    Sec.res k (c • x) = c • Sec.res k x := map_smul _ _ _

theorem res_zero {q : ℕ} (i : ℤ) {W V : Scheme.{0}} (k : W ⟶ V) : Sec.res k (0 : Sec (tw q i) V) = 0 := map_zero _

theorem single_loc (q : ℕ) [NeZero q] (i : ℤ) {V : Scheme.{0}} (ζ ξ : Prim q Γ(V, ⊤)) :
    Loc V fun W k => ∃ c : ULift.{1} (ZMod q), Sec.res k (S q i V (Finsupp.single ξ 1)) = c • twGen i (ζ.map k.appTop.hom) := by
  refine LateralTheory.E.L_prim_locPf.loc_mono' (LateralTheory.E.L_prim_locPf.c2 LateralTheory.E.L_prim_locPf.algPow q V ζ ξ)
    fun W k ⟨e, he⟩ => ⟨ULift.up ((e ^ i : (ZMod q)ˣ) : ZMod q), ?_⟩
  rw [S_res_single, S_rel q i W (ζ.map k.appTop.hom) (ξ.map k.appTop.hom) e he, S_single]

theorem elt_loc (q : ℕ) [NeZero q] (i : ℤ) {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) (f : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) :
    Loc V fun W k => ∃ c : ULift.{1} (ZMod q), Sec.res k (S q i V f) = c • twGen i (ζ.map k.appTop.hom) := by
  induction f using Finsupp.induction_linear with
  | zero => exact loc_top fun W k => ⟨0, by rw [S_zero, res_zero, zero_smul]⟩
  | add f g hf hg =>
    refine LateralTheory.E.L_prim_locPf.loc_mono' (loc_and hf hg) fun W k ⟨⟨c1, h1⟩, ⟨c2, h2⟩⟩ => ⟨c1 + c2, ?_⟩
    rw [S_add, res_add, h1, h2, add_smul]
  | single ξ a =>
    refine LateralTheory.E.L_prim_locPf.loc_mono' (single_loc q i ζ ξ) fun W k ⟨c, h⟩ => ⟨a * c, ?_⟩
    have h3 : Finsupp.single ξ a = a • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h3, S_smul, res_smul, h, mul_smul]

theorem LocForm_of : LateralTheory.E.LCSurjPf.LocForm := by
  intro q _ i B _ ζ y
  have key : Loc (Spec (CommRingCat.of B)) (Q q i (gam ζ) y) := by
    apply loc_trans (Q_stable q i (gam ζ) y)
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i))
      (U := op (Spec (CommRingCat.of B))) y, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hg
    obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (x : (twF q i).obj Γ(V, ⊤))
    have hy : Sec.res g y = S q i V f := by
      refine (hx.symm : _ = ofRings.sec (twF q i) V x).trans ?_
      exact (congrArg (ofRings.sec (twF q i) V) hf).symm
    refine LateralTheory.E.L_prim_locPf.loc_mono' (elt_loc q i ((gam ζ).map g.appTop.hom) f) fun W k ⟨c, hc⟩ => ⟨c, ?_⟩
    rw [res_comp, prim_map_comp, hy, hc]
  refine LateralTheory.E.L_prim_locPf.loc_mono' key fun V g ⟨c, hc⟩ => ⟨c.down, ?_⟩
  rw [hc, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have hcv : ((c.down.val : ℕ) : ULift.{1} (ZMod q)) = c := by
    apply ULift.ext
    rw [ULift.down_natCast, ZMod.natCast_zmod_val]
  rw [hcv]

end LateralTheory.E.LocFormPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafModelCurveCut

def ExistsNormalProperCurveModel : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    ∃ (C0 : Scheme.{0}) (c0 : C0 ⟶ Sp Ω) (x : C0) (ψ : Spec (C0.presheaf.stalk x) ⟶ Sp L),
      IsIntegral C0 ∧ IsProper c0 ∧ (∀ y : C0, IsIntegrallyClosed (C0.presheaf.stalk y)) ∧
      topologicalKrullDim C0 = 1 ∧ IsGenericPoint x (⊤ : Set C0) ∧
      ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = C0.fromSpecStalk x ≫ c0

def LeafSmoothOfNormal : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω),
  IsIntegral C → LocallyOfFiniteType c → (∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y)) →
    topologicalKrullDim C = 1 → SmoothOfRelativeDimension 1 c

theorem goal_of (hN : ExistsNormalProperCurveModel) (hS : LeafSmoothOfNormal) : LateralTheory.E.LeafCurveVCut.LeafModelCurve := by
  intro Ω L _ _ _ _ u hu hfin
  obtain ⟨C0, c0, x, ψ, hint, hprop, hnorm, hdim, hx, hψ⟩ := hN Ω L u hu hfin
  refine ⟨C0, c0, x, ψ, ⟨hint, hprop, ?_⟩, hx, hψ⟩
  have := hprop
  exact hS Ω c0 hint inferInstance hnorm hdim

end LateralTheory.E.LeafModelCurveCut

end
end
