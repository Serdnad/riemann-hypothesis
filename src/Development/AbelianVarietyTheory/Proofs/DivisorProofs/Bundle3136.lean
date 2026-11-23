module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle095
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle089
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3073
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3011
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
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

noncomputable section

namespace GlobalTheory.LowFilt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem datum_finite_int (D : Datum H) : Module.Finite ℤ D.La := by
  haveI := D.fin
  exact Module.Finite.trans (𝓞 E) D.La

theorem datum_isTorsionFree_int (D : Datum H) : Module.IsTorsionFree ℤ D.La := by
  refine Module.isTorsionFree_iff_smul_eq_zero.2 ?_
  intro k x hkx
  by_contra hk
  push_neg at hk
  have hx : x = 0 := D.unimod.1 (LinearMap.ext fun b => by
    have := congrArg (fun v => D.EF v b) hkx
    simp only [map_zsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, smul_eq_mul, mul_eq_zero] at this
    simpa using this.resolve_left hk.1)
  exact hk.2 hx

theorem sub_free_finite (D : Datum H) (Z : Submodule (𝓞 E) D.La) : Module.Free ℤ Z ∧ Module.Finite ℤ Z := by
  haveI := datum_finite_int D
  haveI := datum_isTorsionFree_int D
  haveI : IsNoetherian ℤ D.La := isNoetherian_of_isNoetherianRing_of_finite ℤ D.La
  let f : Z →ₗ[ℤ] D.La := Z.subtype.toAddMonoidHom.toIntLinearMap
  have hf : Function.Injective f := Subtype.val_injective
  haveI : Module.Finite ℤ Z := Module.Finite.of_injective f hf
  haveI : Module.IsTorsionFree ℤ Z := hf.moduleIsTorsionFree f (fun r m => f.map_smul r m)
  exact ⟨inferInstance, inferInstance⟩

theorem IsOpp.finrank_int_eq {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La} (h : IsOpp D Z Z') :
    Module.finrank ℤ Z' = Module.finrank ℤ Z := by
  obtain ⟨hZf, hZn⟩ := sub_free_finite D Z
  let ψ : Z' →ₗ[ℤ] Module.Dual ℤ Z :=
    { toFun := fun b => (D.EF.flip (b : D.La)).comp Z.subtype.toAddMonoidHom.toIntLinearMap
      map_add' := fun b b' => by ext a; simp
      map_smul' := fun k b => by ext a; simp }
  have hψ : Function.Bijective ψ := by
    refine ⟨fun b b' hbb => ?_, fun φ => ?_⟩
    · obtain ⟨c, -, hu⟩ := h.2.2.1 ((ψ b).toAddMonoidHom)
      have e1 := hu b (fun a => rfl)
      have e2 := hu b' (fun a => by rw [hbb]; rfl)
      exact e1.trans e2.symm
    · obtain ⟨b, hb, -⟩ := h.2.2.1 φ.toAddMonoidHom
      exact ⟨b, LinearMap.ext fun a => hb a⟩
  rw [(LinearEquiv.ofBijective ψ hψ).finrank_eq]
  classical
  let bZ := Module.Free.chooseBasis ℤ Z
  rw [Module.finrank_eq_card_basis bZ.dualBasis, Module.finrank_eq_card_basis bZ]

theorem IsOpp.mem_nsmul_of_surj_mod {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (Z Z' : Submodule (𝓞 E) D.La)
    (h : IsOpp D Z Z') (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X)
    (hs : ∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) (b : D.La) (hb : b ∈ Z') (hy : ∃ e, y b = n • e) :
    ∃ e ∈ Z', b = n • e := by
  obtain ⟨hZf, hZn⟩ := sub_free_finite D Z
  obtain ⟨hZf', hZn'⟩ := sub_free_finite D Z'
  have hrank : Module.finrank ℤ Z' = Module.finrank ℤ X := by
    rw [h.finrank_int_eq, GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E Z,
      GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E X, hr]
  let nB : AddSubgroup X := (nsmulAddMonoidHom n : X →+ X).range
  let nA : AddSubgroup Z' := (nsmulAddMonoidHom n : Z' →+ Z').range
  let g : Z' →+ X := y.toAddMonoidHom.comp Z'.subtype.toAddMonoidHom
  let f : Z' →+ X ⧸ nB := (QuotientAddGroup.mk' nB).comp g
  have hf : Function.Surjective f := by
    rintro ⟨x⟩
    obtain ⟨c, hc, e, he⟩ := hs x
    refine ⟨⟨c, hc⟩, ?_⟩
    show (QuotientAddGroup.mk (y c) : X ⧸ nB) = QuotientAddGroup.mk x
    rw [he, QuotientAddGroup.eq]
    exact ⟨-e, by simp⟩
  have hAK : nA ≤ f.ker := by
    rintro _ ⟨a, rfl⟩
    rw [AddMonoidHom.mem_ker]
    show (QuotientAddGroup.mk (y ((n • a : Z') : D.La)) : X ⧸ nB) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨y a, by simp⟩
  have hK : f.ker.index = n ^ Module.finrank ℤ X := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf, AddSubgroup.card_top]
    exact AddSubgroup.index_range_nsmul X n
  have hA : nA.index = n ^ Module.finrank ℤ X := by
    rw [← hrank]
    exact AddSubgroup.index_range_nsmul Z' n
  have hpos : 0 < n ^ Module.finrank ℤ X := pow_pos hn _
  have hrel : nA.relIndex f.ker = 1 := by
    have := AddSubgroup.relIndex_mul_index hAK
    rw [hK, hA] at this
    exact (Nat.mul_eq_right hpos.ne').1 this
  have hmem : (⟨b, hb⟩ : Z') ∈ f.ker := by
    obtain ⟨e, he⟩ := hy
    rw [AddMonoidHom.mem_ker]
    show (QuotientAddGroup.mk (y b) : X ⧸ nB) = 0
    rw [QuotientAddGroup.eq_zero_iff, he]
    exact ⟨e, rfl⟩
  obtain ⟨c, hc⟩ := AddSubgroup.relIndex_eq_one.1 hrel hmem
  exact ⟨c, c.2, (congrArg Subtype.val hc).symm.trans rfl⟩

end GlobalTheory.LowFilt

theorem GlobalTheory.LowFilt.inj_mod_of_surj_mod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∀ b ∈ Z', (∃ e, y b = n • e) → ∃ e ∈ Z', b = n • e :=
  fun D _ _ _ _ _ y n hn Z Z' h hr hs b hb hy => IsOpp.mem_nsmul_of_surj_mod D y n hn Z Z' h hr hs b hb hy
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub)

theorem exists_const_of_glue : ∀ {K : Type} [Field K] (A₀ : Over (Sp K)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ {I : Type} (U : I → A₀.left.Opens) (f : ∀ i, Γ(A₀.left, U i)), ⨆ i, U i = ⊤ → (∀ i i', resG A₀.left (inf_le_left : U i ⊓ U i' ≤ U i) (f i) = resG A₀.left (inf_le_right : U i ⊓ U i' ≤ U i') (f i')) → ∃ c : K, ∀ (Z : Scheme.{0}) (b : Z ⟶ A₀.left) (z : Z) (i : I), b z ∈ U i → gs b z (U i) (f i) = cst (b ≫ A₀.hom) z c := by
  intro K _ A₀ _ hab I U f hcov hcomp
  obtain ⟨F, hF, -⟩ := A₀.left.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) (by rw [hcov]) f hcomp
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨s, hs⟩ := (hG (Sp K) A₀ hab).2 F
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom s, fun Z b z i hz => ?_⟩
  rw [cst, Iso.hom_inv_id_apply, ← gs_pull b A₀.hom z ⊤ trivial s, ← hF i]
  refine (gs_res b z (le_top : U i ≤ ⊤) hz F).trans ?_
  rw [← hs]
  rfl

theorem exists_coordEq : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → ∀ α : Q.X, ChartFree Y h ν m₀ V pb α → ∃ c : K, CoordEq Y h ν m₀ V pb α c := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hC hD α hfree
  obtain ⟨T, hT₁, hT₂⟩ := hF.exists_strictHenselian_absolutely_closed_local_ring α
  have hT0 : T 0 = 𝟙 _ := hF.T_zero (hT₁ 0) (hT₂ 0)
  have hab : IsAbelianScheme A₀ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · haveI := Q.P.isAb.comm
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hF.pull.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hF.pull.2 T x y (pushPt hF.pull.1.w x) (pushPt hF.pull.1.w y) rfl rfl,
        ← hF.pull.2 T y x (pushPt hF.pull.1.w y) (pushPt hF.pull.1.w x) rfl rfl, _root_.mul_comm]
    · exact MorphismProperty.of_isPullback (P := @Smooth) hF.pull.1 Q.P.isAb.smooth
    · exact MorphismProperty.of_isPullback (P := @IsProper) hF.pull.1 Q.P.isAb.proper
    · exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hF.pull.1 Q.P.isAb.geomConnected
  have hV : ∀ i, V i ≤ Q.P.L.U (h.j i) := hC.2.2.1
  let U : (Fin 4 → h.J) → Q.P.A.left.Opens := fun i =>
    V (i 0) ⊓ LB.wchart Q.P.L (Q.famφB α) (fun j => h.j (i j))
  have hU : ∀ i, Y.q.left ⁻¹ᵁ U i ≤ h.W (i 0) ⊓ xU Y α (fun j => h.j (i j)) := by
    intro i y hy
    refine ⟨?_, Set.mem_iInter.2 fun k => ?_⟩
    · rw [hD.1]; exact hy.1
    · have := Set.mem_iInter.1 hy.2 (![1, 2, 0, 3] k)
      show y ∈ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k ⁻¹ᵁ Q.P.L.U (h.j (i (![1, 2, 0, 3] k)))
      rw [gtφT_eq, Scheme.Hom.comp_preimage]
      exact this
  have exA : ∀ i : Fin 4 → h.J, ∃ A : Γ(Q.P.A.left, U i), (Y.q.left.app (U i)).hom A *
      rsT (xc Y α fun j => h.j (i j)).val (Y.q.left ⁻¹ᵁ U i) =
      dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (Y.q.left ⁻¹ᵁ U i)) := fun i =>
    GlobalTheory.T.exists_abelianPart_function_of_weight_unit_logDeriv Y h ν hF.wt hF.basic (i 0) α (U i) ((hU i).trans inf_le_left) _
      (by rw [GlobalTheory.KS.GlueDer.rsT_eq ((hU i).trans inf_le_right)]; exact (Units.isUnit _).map _)
      (GlobalTheory.T.raynaud_coordinate_in_charts_has_character_weight Y α _ _ ((hU i).trans inf_le_right))
  choose A hA using exA
  let Oi : (Fin 4 → h.J) → A₀.left.Opens := fun i =>
    T 0 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 0)) ⊓ T 1 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 1)) ⊓ T 2 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 2)) ⊓ T 3 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 3))
  have memO : ∀ i (p : A₀.left), p ∈ Oi i ↔ ∀ j, m₀ (T j p) ∈ V (i j) := by
    intro i p
    constructor
    · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ j
      fin_cases j
      exacts [h0, h1, h2, h3]
    · intro H
      exact ⟨⟨⟨H 0, H 1⟩, H 2⟩, H 3⟩
  have hOU : ∀ i, Oi i ≤ m₀ ⁻¹ᵁ U i := by
    intro i p hp
    have H := (memO i p).1 hp
    refine ⟨?_, Set.mem_iInter.2 fun k => ?_⟩
    · have := H 0
      rw [hT0] at this
      exact this
    · have := hV _ (H k)
      rw [← Scheme.Hom.comp_apply, hT₁ k, Scheme.Hom.comp_apply] at this
      exact this
  have hOT : ∀ i j, Oi i ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j)) := fun i j p hp => (memO i p).1 hp j
  let f : ∀ i, Γ(A₀.left, Oi i) := fun i =>
    pbT m₀ (A i) (Oi i) + pbT (T 0) (pb (i 0)) (Oi i) - pbT (T 1) (pb (i 1)) (Oi i) +
      pbT (T 2) (pb (i 2)) (Oi i) - pbT (T 3) (pb (i 3)) (Oi i)
  have hCA : ∀ i (Z : Scheme.{0}) (a : Z ⟶ Y.H.left) (b : Z ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ z, b z ∈ Oi i →
      CoordAt Y h ν m₀ V pb α i T a b z (gs b z (Oi i) (f i)) := by
    intro i Z a b w z hz
    have hza : a z ∈ Y.q.left ⁻¹ᵁ U i := by
      show Y.q.left (a z) ∈ U i
      rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
      exact hOU i hz
    have e1 : rsT (xc Y α fun j => h.j (i j)).val (Y.q.left ⁻¹ᵁ U i) =
        resG _ (hU i) (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))) := by
      rw [← GlobalTheory.KS.GlueDer.rsT_eq (hU i)]
      refine fn_ext fun y hy => ?_
      rw [gs_rsT (𝟙 _) y ((hU i).trans inf_le_right) hy, gs_rsT (𝟙 _) y (hU i) hy,
        gs_rsT (𝟙 _) y inf_le_right (hU i hy)]
    have e2 : dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (Y.q.left ⁻¹ᵁ U i)) =
        resG _ (hU i) (dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j)))) := by
      rw [e1]
      exact (isField_dE h ν hF.field (i 0)).2.2 _ _ (hU i) inf_le_left _
    have lhs : gs a z (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))
        (dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j)))) =
        gs (b ≫ m₀) z (U i) (A i) * gs a z (xU Y α fun j => h.j (i j)) (xc Y α fun j => h.j (i j)).val := by
      rw [← gs_res a z (hU i) hza, ← e2, ← hA i, gs_mul a z _ hza, gs_rsT a z ((hU i).trans inf_le_right) hza,
        gs_pull a Y.q.left z (U i) hza, w]
    have rhs : gs b z (Oi i) (f i) = gs (b ≫ m₀) z (U i) (A i) +
        gs (b ≫ T 0) z (m₀ ⁻¹ᵁ V (i 0)) (pb (i 0)) - gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V (i 1)) (pb (i 1)) +
        gs (b ≫ T 2) z (m₀ ⁻¹ᵁ V (i 2)) (pb (i 2)) - gs (b ≫ T 3) z (m₀ ⁻¹ᵁ V (i 3)) (pb (i 3)) := by
      simp only [f, gs_add b z _ hz, gs_sub b z _ hz, gs_pbT b m₀ z (hOU i) hz, gs_pbT b (T _) z (hOT i _) hz]
    unfold CoordAt
    rw [lhs, rhs]
    ring
  have uniq : ∀ i (Z : Scheme.{0}) (a : Z ⟶ Y.H.left) (b : Z ⟶ A₀.left) (z : Z) (w₁ w₂ : Z.presheaf.stalk z),
      a z ∈ xU Y α (fun j => h.j (i j)) → CoordAt Y h ν m₀ V pb α i T a b z w₁ →
      CoordAt Y h ν m₀ V pb α i T a b z w₂ → w₁ = w₂ := by
    intro i Z a b z w₁ w₂ hm h₁ h₂
    unfold CoordAt at h₁ h₂
    rw [h₁, gs_unit a z _ hm] at h₂
    exact add_left_cancel ((Units.isUnit _).mul_left_cancel h₂)
  have hover : ∀ i i', resG A₀.left (inf_le_left : Oi i ⊓ Oi i' ≤ Oi i) (f i) =
      resG A₀.left (inf_le_right : Oi i ⊓ Oi i' ≤ Oi i') (f i') := by
    intro i i'
    refine ext_lift Y m₀ fun Z a b w z hz => ?_
    rw [gs_res b z inf_le_left hz, gs_res b z inf_le_right hz]
    have hi : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i j) := fun j => (memO i (b z)).1 hz.1 j
    have hi' : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i' j) := fun j => (memO i' (b z)).1 hz.2 j
    have h₁ := hfree T hT₁ hT₂ Z a b w z i i' hi hi' _ (hCA i Z a b w z hz.1)
    exact uniq i' Z a b z _ _ (hF.mem_chart hD hV hT₁ w hi').2 h₁ (hCA i' Z a b w z hz.2)
  have hcov : ⨆ i, Oi i = ⊤ := by
    refine eq_top_iff.2 fun p _ => ?_
    have ex : ∀ j, ∃ k, m₀ (T j p) ∈ V k := fun j => by
      have : m₀ (T j p) ∈ (⨆ k, V k) := by rw [hC.2.1]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    choose i hi using ex
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (memO i p).2 hi⟩
  obtain ⟨c, hc⟩ := exists_const_of_glue A₀ hab Oi f hcov hover
  refine ⟨c, fun T' hT'₁ hT'₂ Z a b w z i hi => ?_⟩
  obtain rfl : T' = T := funext fun j =>
    hF.pull.1.hom_ext ((hT'₁ j).trans (hT₁ j).symm) ((hT'₂ j).trans (hT₂ j).symm)
  have hz : b z ∈ Oi i := (memO i (b z)).2 hi
  rw [← hc Z b z i hz]
  exact hCA i Z a b w z hz

end GlobalTheory.HeatConn
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit

noncomputable section

namespace GlobalTheory.Mum.TensPol

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem exists_int (A : Over (Spec (CommRingCat.of R))) [IsSeparated A.hom] (L : LB A.left) (hL : L.IsLB) (z : (TK R).left) :
    ∃ J, Good L z J ∧
      ∀ p : Spec (CommRingCat.of R) ⟶ A.left, p ≫ A.hom = 𝟙 _ → p (closedPoint R) ∈ L.U (J (jK R ≫ p)) := by
  have : IsDominant (jK R) := DVR.isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ A.left => exists_chart hL (p (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good L hL (Z := (TK R).left) z
    (K := {p : Spec (CommRingCat.of R) ⟶ A.left // p ≫ A.hom = 𝟙 _}) (fun p => jK R ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R)) A.hom
      (a.2.trans b.2.symm) (jK R) h))
    (fun p => (IsLocalRing.specializes_closedPoint (jK R z)).mem_open (p.1 ⁻¹ᵁ L.U (pick p.1)).isOpen (hpk p.1))
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

theorem val_mem {A : Over (Spec (CommRingCat.of R))} {L : LB A.left} (z : (TK R).left) {J : ((TK R).left ⟶ A.left) → L.ι}
    (hJ : ∀ p : Spec (CommRingCat.of R) ⟶ A.left, p ≫ A.hom = 𝟙 _ → p (closedPoint R) ∈ L.U (J (jK R ≫ p)))
    {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of R) ⟶ A.left)) (hφ : ∀ k, φ k ≫ A.hom = 𝟙 _) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) : val t (toUnit (TK R)).left z J ∈ unitsS z := by
  have := gm_mem z (𝟙 _) (LB.wchart L φ (fun k => J (jK R ≫ φ k))) (Set.mem_iInter.2 fun k => hJ (φ k) (hφ k))
    (t.s (fun k => J (jK R ≫ φ k)))
  rw [Category.comp_id] at this
  exact this

theorem mem_unitsK (z : (TK R).left) {x : (FractionRing R)ˣ} (h : Units.map (ev z).toMonoidHom x ∈ unitsS z) : x ∈ unitsK R := by
  obtain ⟨y, hy, e⟩ := h
  exact (Units.map_injective (ev_inj z) e) ▸ hy

theorem gm_unitOn (z : (TK R).left) (k : (FractionRing R)ˣ) :
    gm (𝟙 (TK R).left) z ⊤ (unitOn k) = Units.map (ev z).toMonoidHom k :=
  Units.ext ((gs_unit _ z ⊤ trivial _).symm.trans (ev_eq z k))

end GlobalTheory.Mum.TensPol
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RootHom

theorem exists_sqrt_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h : X → (FractionRing R)ˣ) (m : ℕ) (t : Fin m → R), IsCN R → (∀ a b, h (a + b) = h a * h b) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (gam : FractionRing R →+* FractionRing R') (r : Fin m → R') (eta : X → (FractionRing R')ˣ), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ (∀ x, gam (algebraMap R _ x) = algebraMap R' _ (ρ x)) ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ (∀ a b, eta (a + b) = eta a * eta b) ∧ ∀ a, eta a ^ 2 = Units.map gam.toMonoidHom (h a) := by
  intro R _ _ _ X _ _ _ h m t hR hh
  classical
  let b := Module.Free.chooseBasis ℤ X
  have hpq : ∀ k, ∃ p q : R, q ∈ nonZeroDivisors R ∧
      algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) q = (h (b k) : FractionRing R) :=
    fun k => IsFractionRing.div_surjective R _
  choose p q hq hpq using hpq
  obtain ⟨R', _, _, _, ρ, r, hR', hinj, hfin, hloc, hr⟩ :=
    GlobalTheory.T.exists_finite_completeNormal_ext_sqrt_family R (Fin m ⊕ Module.Free.ChooseBasisIndex ℤ X) (Sum.elim t (fun k => p k * q k)) hR
  have hι : Function.Injective (algebraMap R' (FractionRing R')) := IsFractionRing.injective R' (FractionRing R')
  have hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) := hι.comp hinj
  let gam : FractionRing R →+* FractionRing R' := IsFractionRing.lift hinj'
  have hgam : ∀ x, gam (algebraMap R _ x) = algebraMap R' _ (ρ x) := fun x => IsFractionRing.lift_algebraMap hinj' x
  have hq0 : ∀ k, algebraMap R' (FractionRing R') (ρ (q k)) ≠ 0 := by
    intro k h0
    have : ρ (q k) = 0 := hι (by simpa using h0)
    exact nonZeroDivisors.ne_zero (hq k) (hinj (by simpa using this))
  have hp0 : ∀ k, p k ≠ 0 := by
    intro k h0
    have := hpq k
    rw [h0, map_zero, zero_div] at this
    exact (h (b k)).ne_zero this.symm
  have hs : ∀ k, (r (Sum.inr k)) ^ 2 = ρ (p k * q k) := fun k => by simpa using hr (Sum.inr k)
  have hs0 : ∀ k, algebraMap R' (FractionRing R') (r (Sum.inr k)) ≠ 0 := by
    intro k h0
    have h1 : r (Sum.inr k) = 0 := hι (by simpa using h0)
    have h2 := hs k
    rw [h1, zero_pow two_ne_zero] at h2
    exact mul_ne_zero (hp0 k) (nonZeroDivisors.ne_zero (hq k)) (hinj (by simpa using h2.symm))
  let e : Module.Free.ChooseBasisIndex ℤ X → (FractionRing R')ˣ := fun k =>
    Units.mk0 (algebraMap R' _ (r (Sum.inr k)) / algebraMap R' _ (ρ (q k))) (div_ne_zero (hs0 k) (hq0 k))
  let L : X →ₗ[ℤ] Additive (FractionRing R')ˣ := b.constr ℤ (fun k => Additive.ofMul (e k))
  let H : X →+ Additive (FractionRing R)ˣ := AddMonoidHom.mk' (fun a => Additive.ofMul (h a)) (fun a c => by
    simp [hh a c])
  let G : X →+ Additive (FractionRing R')ˣ := (MonoidHom.toAdditive (Units.map gam.toMonoidHom)).comp H
  have hLG : L + L = G.toIntLinearMap := by
    refine b.ext fun k => ?_
    simp only [LinearMap.add_apply, L, Module.Basis.constr_basis, AddMonoidHom.coe_toIntLinearMap, G, H,
      AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.mk'_apply, MonoidHom.toAdditive_apply_apply]
    rw [← ofMul_mul]
    congr 1
    ext
    simp only [Units.val_mul, e, Units.val_mk0, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, toMul_ofMul]
    rw [← hpq k, map_div₀, hgam, hgam, div_mul_div_comm, div_eq_div_iff (mul_ne_zero (hq0 k) (hq0 k)) (hq0 k)]
    have := congrArg (algebraMap R' (FractionRing R')) (hs k)
    rw [map_pow, map_mul, map_mul] at this
    rw [← sq, this]
    ring
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, gam, fun i => r (Sum.inl i), fun a => Additive.toMul (L a),
    hR', hinj, hfin, hloc, hgam, fun i => by simpa using hr (Sum.inl i), fun a c => by simp [map_add (f := _)], fun a => ?_⟩
  have h2 : Additive.toMul (L a + L a) = Units.map gam.toMonoidHom (h a) := by
    rw [← LinearMap.add_apply, LinearMap.congr_fun hLG a]
    rfl
  rw [sq, ← toMul_add]
  exact h2

end GlobalTheory.RootHom
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_completeDVR_of_finite_etale_baseChange : ∀ (A R V : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (ρ : A →+* R) (ψ : A →+* V), IsLocalHom ρ → ρ.Finite → ρ.Etale → IsCN V → IsDiscreteValuationRing V → IsLocalHom ψ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (κ : R →+* V'), IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp ρ = f.comp ψ := by
  first | exact @GlobalTheory.HenselLift.exists_dvr_of_finite_etale | exact GlobalTheory.HenselLift.exists_dvr_of_finite_etale | (intros; apply GlobalTheory.HenselLift.exists_dvr_of_finite_etale <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_completeNormal_galois_cover_of_finite : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing R] [IsDomain R] (b : A →+* R), IsCN A → b.Finite → Function.Injective b → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (θ : R →+* R'), IsCN R' ∧ IsLocalHom θ ∧ Function.Injective θ ∧ θ.Finite ∧ ∀ r : R, (∀ σ : R' ≃+* R', IsOfFinOrder σ → (∀ a, σ (θ (b a)) = θ (b a)) → σ (θ r) = θ r) → r ∈ b.range := by
  first | exact @GlobalTheory.GalCover.exists_isCN_galois_of_finite | exact GlobalTheory.GalCover.exists_isCN_galois_of_finite | (intros; apply GlobalTheory.GalCover.exists_isCN_galois_of_finite <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hodgeFiltrations_orthogonal_lineBundlePairing_product : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → ∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0 := by
  first | exact @GlobalTheory.PtExt.HodgeOrth.fil_orthogonal | exact GlobalTheory.PtExt.HodgeOrth.fil_orthogonal | (intros; apply GlobalTheory.PtExt.HodgeOrth.fil_orthogonal <;> assumption)
end
