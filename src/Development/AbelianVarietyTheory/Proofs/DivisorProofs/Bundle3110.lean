module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3078
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle092
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorValuesOfSectionsCompleteLocalRing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2717
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3042
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle935
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg.SymPol

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem inv_comm (h : IsGrpPullback G' G f φ) : (ι[G']).left ≫ φ = φ ≫ (ι[G]).left := by
  have e := congrArg (fun z => z.left) (map_inv (pushHom h G') (𝟙 G'))
  rw [Hom.inv_def, Hom.inv_def, Category.id_comp] at e
  refine Eq.trans e ?_
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem exists_half (h : IsGrpPullback G' G f φ) (a : 𝟙_ (Over S) ⟶ G) (b : Over.mk f ⟶ G) (hb : b ^ 2 = toUnit _ ≫ a) :
    ∃ b' : 𝟙_ (Over S') ⟶ G',
      ((toUnit G' ≫ b' ^ 2) * 𝟙 G').left ≫ φ = φ ≫ ((toUnit G ≫ a) * 𝟙 G).left := by
  have w : b.left ≫ G.hom = 𝟙 S' ≫ f := (Over.w b).trans (Category.id_comp _).symm
  let b' : 𝟙_ (Over S') ⟶ G' := Over.homMk (h.1.lift _ _ w) (h.1.lift_snd _ _ _)
  have hb' : b'.left ≫ φ = b.left := h.1.lift_fst _ _ _
  let j : Over.mk (G'.hom ≫ f) ⟶ Over.mk f := Over.homMk G'.hom rfl
  have hu : (toUnit G').left = G'.hom := (Category.comp_id _).symm.trans (Over.w (toUnit G'))
  have e₁ : pushHom h G' (toUnit G' ≫ b') = j ≫ b := Over.OverMorphism.ext (by
    show ((toUnit G').left ≫ b'.left) ≫ φ = G'.hom ≫ b.left
    rw [Category.assoc, hb', hu])
  have e₂ : pushHom h G' ((toUnit G' ≫ b' ^ 2) * 𝟙 G') = pushHom h G' (𝟙 G') ≫ ((toUnit G ≫ a) * 𝟙 G) := by
    rw [map_mul, MonObj.comp_pow, map_pow, e₁, ← MonObj.comp_pow, hb, MonObj.comp_mul, Category.comp_id,
      ← Category.assoc, ← Category.assoc, toUnit_unique (j ≫ toUnit _) (pushHom h G' (𝟙 G') ≫ toUnit G)]
  refine ⟨b', (congrArg (fun z => z.left) e₂).trans ?_⟩
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem exists_gen_theta_pull [IsCommMonObj G] [IsCommMonObj G'] (h : IsGrpPullback G' G f φ) {L : LB G.left}
    (ht : ∃ t : LB.Gen (Theta G L), t.IsGen) : ∃ t : LB.Gen (Theta G' (L.pull φ)), t.IsGen := by
  obtain ⟨t, ht⟩ := ht
  exact gen_chartPull (chartPullLinComb L φ _ _ _ (cubeMapOf h).F3 fun I => (cubeMapOf h).psum_comm I.down) t ht

end GlobalTheory.PolDeg.SymPol


open GlobalTheory.PolDeg.SymPol GlobalTheory.CechPic in
theorem GlobalTheory.PolDeg.exists_symmetric_pol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R), IsCN R → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ IsGrpPullback P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) := by
  intro R _ _ _ Q hR
  haveI := hR.1
  have hM := Q.M.isLB
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  obtain ⟨a, ha⟩ := GlobalTheory.T.primitive_bundle_eq_translate_ample_noetherian_local R Q.B Q.g Q.M.L _ Q.isAb Q.smoothDim hM Q.ample Q.ktriv hΘ
    (LB.isLB_linComb hM _ _) (GlobalTheory.T.exists_generator_mumfordBundle_inv_pullback_primitive R Q.B Q.M Q.cub Q.isAb)
  have ea := (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb hM _ _)).2 ha
  rw [cls_linComb hM, cls_linComb hM, Fin.sum_univ_two, Fin.sum_univ_two] at ea
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, add_left_inj] at ea
  obtain ⟨R', _, _, _, ρ, b, hR', hinj, hfin, hloc, hb⟩ := GlobalTheory.T.exists_halving_point_abelianScheme_finite_ext R Q.B a hR Q.isAb
  haveI := hR'.1
  have h := isGrpPullback_pullback Q.B (spMap ρ)
  have hA : IsAbelianScheme ((Over.pullback (spMap ρ)).obj Q.B) := by
    have := Q.isAb.comm
    have hc : IsCommMonObj ((Over.pullback (spMap ρ)).obj Q.B) := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) h.1 Q.isAb.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 Q.isAb.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 Q.isAb.geomConnected⟩
  haveI := hA.comm
  obtain ⟨b', hb'⟩ := exists_half h a b hb
  have hM' := pull_isLB hM (pullback.fst Q.B.hom (spMap ρ))
  have hid := (cls_eq_iff hM' hM').1 rfl
  obtain ⟨w, hw⟩ := id hid
  obtain ⟨L, hL, hrig, hsym, hamp, hK, hΛ⟩ := GlobalTheory.T.exists_symmetric_rigidified_translate_ample_K_trivial R' _ _ b' hA hM'
    (relAmple_pull h.1 hM hM' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) Q.ample)
    (kTriv_pull h hM hM' ((isGen_iff w).1 hw) Q.ktriv) (exists_gen_theta_pull h hΘ)
    ((cls_eq_iff (pull_isLB hM' _) (pull_isLB hM' _)).1 (by
      rw [cls_pull hM', cls_pull hM', cls_pull hM, ← pull_comp, ← pull_comp, inv_comm h, hb', pull_comp, pull_comp, ea]))
  obtain ⟨β₂, hβ₂⟩ := SiegPull.exists_isSquare h.1.w
  exact ⟨R', _, _, _, ρ,
    { A := (Over.pullback (spMap ρ)).obj Q.B, isAb := hA, g := Q.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 Q.smoothDim
      L := L, isLB := hL, rigid := hrig, sym := hsym, ample := hamp, ktriv := hK }, _, β₂, hR', hinj, hfin, hloc, h, hβ₂,
    LBIso.trans (LB.isLB_linComb hL _ _) (LB.isLB_linComb hM' _ _) (pull_isLB (LB.isLB_linComb hM _ _) _) hΛ
      (SiegPull.lbIso_lam_pull h hid hβ₂)⟩

end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan.KSUniv

theorem spMap_comp_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

noncomputable def reparam {K : Type} [Field K] (F : Type) [Field F] [Algebra F K] {ι : Type} [Fintype ι]
    (P : Matrix ι ι K) : TrivSqZeroExt K (ι → K) →ₐ[F] TrivSqZeroExt K (ι → K) :=
  (TrivSqZeroExt.map (Matrix.mulVecLin P.transpose)).restrictScalars F

theorem isTanX_dir {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K}
    {ι : Type} [Fintype ι] {X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X} (h1 : X ≫ Xo.s = sOf c _)
    (h2 : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x) (M : ι → K) :
    GlobalTheory.FlagTan.IsTanX y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, sOf, sOf, spMap_comp_spMap']
    congr 1
    rw [← RingHom.comp_assoc]
    congr 1
    exact (GlobalTheory.FlagTan.dir c M).comp_algebraMap
  · rw [← Category.assoc, spMap_comp_spMap', ← h2]
    congr 2
    ext z
    simp

theorem dir_comp_reparam {K : Type} [Field K] {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l : Level H} {c : Coeff l} [Algebra c.F K] {ι : Type} [Fintype ι] (P : Matrix ι ι K) (M : ι → K) :
    (GlobalTheory.FlagTan.dir c M).toRingHom.comp (reparam c.F P).toRingHom = (GlobalTheory.FlagTan.dir c (P.mulVec M)).toRingHom := by
  ext z
  · simp [reparam]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, GlobalTheory.FlagTan.snd_dir, reparam,
      AlgHom.restrictScalars_apply, GlobalTheory.FlagTan.fst_dir, TrivSqZeroExt.snd_map, Matrix.mulVecLin_apply]
    have e := Matrix.dotProduct_mulVec z.snd P M
    rw [← Matrix.mulVec_transpose] at e
    simpa [dotProduct, mul_comm] using e.symm


open GlobalTheory.FlagTan in
theorem ksUniv : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → ∃ X : Sp (TrivSqZeroExt K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)).toRingHom ≫ X = y.x ∧ ∀ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) M := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y hpq
  classical
  obtain ⟨X₀, h1, h2, hinj⟩ :=
    GlobalTheory.T.exists_moduliPoint_trivSqZeroExt_tangentBasis E H Dw l Xo c K y (HIx Dw (psiSet H)) (card_HIx (isHalf_psiSet H))
  choose N hN using fun k : HIx Dw (psiSet H) =>
    GlobalTheory.T.kodaira_spencer_matrix_exists hP E H Dw l Xo c K y _ hpq (isTanX_dir h1 h2 (Pi.single k 1))
  have hL := GlobalTheory.T.tangent_flag_hodge_index_vanishing hP E H Dw l Xo c K y _ X₀ hpq h1 h2 N hN
  let L : (HIx Dw (psiSet H) → K) →ₗ[K] (HIx Dw (psiSet H) → K) := Fintype.linearCombination K N
  have hLa : ∀ M, L M = ∑ k, M k • N k := fun M => Fintype.linearCombination_apply _ _ _
  have h0 : spMap (dir c (0 : HIx Dw (psiSet H) → K)).toRingHom ≫ X₀ =
      spMap (algebraMap K (DualNumber K)) ≫ y.x := by
    rw [← h2, ← Category.assoc, spMap_comp_spMap']
    congr 2
    ext z <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have Linj : Function.Injective L := (injective_iff_map_eq_zero L).2 fun M hM =>
    hinj ((GlobalTheory.T.kodaira_spencer_zero_tangent_trivial hP hG E H Dw l Xo c K y _ hpq (isTanX_dir h1 h2 M)
      (by rw [← hM, hLa]; exact hL M)).trans h0.symm)
  let e := LinearEquiv.ofInjectiveEndo L Linj
  let P := LinearMap.toMatrix' (e.symm : (HIx Dw (psiSet H) → K) →ₗ[K] (HIx Dw (psiSet H) → K))
  have hP' : ∀ M, P.mulVec M = e.symm M := fun M => LinearMap.toMatrix'_mulVec _ M
  refine ⟨spMap (reparam c.F P).toRingHom ≫ X₀, ?_, ?_, fun M => ?_⟩
  · rw [Category.assoc, h1, sOf, spMap_comp_spMap']
    congr 1
    rw [← RingHom.comp_assoc]
    congr 1
    exact (reparam c.F P).comp_algebraMap
  · rw [← Category.assoc, spMap_comp_spMap', ← h2]
    congr 2
    ext z
    simp [reparam]
  · rw [← Category.assoc, spMap_comp_spMap', dir_comp_reparam, hP']
    have := hL (e.symm M)
    rwa [← hLa, show L (e.symm M) = M from e.apply_symm_apply M] at this

end GlobalTheory.FlagTan.KSUniv
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

theorem _root_.GlobalTheory.T.heat_operator_values_of_sections_complete_local_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ) (hx' : x' ≫ t.G.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∃ (e : Ωˣ) (p0 p0' : Ω), ∀ (k : ℕ), 1 ≤ k → ∀ (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), IsValue (𝟙 _) t.PP.L x' g k σ ω → ∃ (r : R) (σ' : SecM (𝟙 t.G.left) t.PP.L k) (ω' : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ' ω' ∧ ω' = φ r * ((e : Ω) ^ k * ringOp ⇑dΩ (fun a => ⇑(δ a)) (φ.mapMatrix h.Θ) (fun a => φ (h.u a)) p0 p0' k (((e⁻¹ : Ωˣ) : Ω) ^ k * ω)) := by
  first | exact @GlobalTheory.HeatValues.heat_values_at_point | exact GlobalTheory.HeatValues.heat_values_at_point | (intros; apply GlobalTheory.HeatValues.heat_values_at_point <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.Heat.HxLift

theorem exists_invLift : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ d : Fld Y.H.left, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V.1) d ∧ ∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f) := by
  intro R _ _ Q O _ _ _ oa Y V D
  obtain ⟨δ₀, h0a, h0m, h0c⟩ := GlobalTheory.T.exists_derivation_lift_raynaud_preimage_affine R Q O oa Y V D
  obtain ⟨δ, ha, hm, hc, hw⟩ := GlobalTheory.T.exists_weight_preserving_lift_of_base_derivation R Q O oa Y V D δ₀ h0a h0m h0c
  obtain ⟨d, hd, hdU⟩ := GlobalTheory.T.exists_vectorField_extending_affineDerivation Y.H.left _ (GlobalTheory.T.isAffineOpen_preimage_projection_abelianPart R Q O oa Y V) δ ha hm
  refine ⟨d, ⟨hd, fun O' hO' r => ?_⟩, ?_⟩
  · rw [← GlobalTheory.ZH.FormSec.res_constFn Y.H.hom hO' r, ← GlobalTheory.ZH.FormSec.res_constFn Y.H.hom hO' (D r),
      hd.2.2 _ _ hO' le_rfl, hdU, hc]
  · refine GlobalTheory.T.weight_preserving_vectorField_on_smaller_preimages R Q O oa Y V d hd (fun α f hf => ?_)
    rw [hdU]
    exact hw α f hf

end GlobalTheory.Heat.HxLift
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

theorem _root_.GlobalTheory.T.kodairaSpencer_matrix_zero_derivation_eq_zero : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ M : Matrix (Fin n) (Fin n) K, KSRel P₀.A (𝟙 P₀.A.left) P₀.L dd (fun _ => 0) M → M = 0 := by
  first | exact @GlobalTheory.KSZeroDer.main | exact GlobalTheory.KSZeroDer.main | (intros; apply GlobalTheory.KSZeroDer.main <;> assumption)
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

theorem _root_.GlobalTheory.T.heatOperator_const_mul_derivation_term : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (vv : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vv a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Q.P.L dd ⇑D) (k : ℕ) (c : R) (τ τ' τu τu' : SecM Y.q.left Q.P.L k), h.Acts k τ τ' → h.Acts k τu τu' → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval τu r z J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ' r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval τu' r z J + gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (2 * (k : R) * D c)) * sval τu r z J := by
  first | exact @GlobalTheory.HeatOpConst.heat_const_mul | exact GlobalTheory.HeatOpConst.heat_const_mul | (intros; apply GlobalTheory.HeatOpConst.heat_const_mul <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kodairaSpencer_relation_matrix_symmetric_local_domain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (P : Out.PolAV (Sp R)) (g : ℕ) (w : Module.Basis (Fin g) R (TanM (𝟙 (Sp R)) P.A)) (e : Fin g → Fld P.A.left), (∀ c, IsInv P.A (w c) (e c)) → ∀ (D : Derivation ℤ R R) (M : Matrix (Fin g) (Fin g) R), KSRel P.A (𝟙 P.A.left) P.L e ⇑D M → Mᵀ = M := by
  first | exact @GlobalTheory.KSRelSymm.ksRel_symm | exact GlobalTheory.KSRelSymm.ksRel_symm | (intros; apply GlobalTheory.KSRelSymm.ksRel_symm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
open Classical

namespace GlobalTheory.Poinc.IntTerm

theorem exists_rig_torsFrame_of_match : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∃ ρA : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A)), ρA.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x fr hx hfr
  have gp := 𝔪.cart
  have hw := 𝔪.wl_gen
  obtain ⟨rig', hrig', Hr⟩ := GlobalTheory.ConstFam.exists_gen_through (K := PUnit) (φ' := fun _ => eSec 𝔪.A.A)
    (φ := fun _ => eSec X₁.ρ.P.A) (ε := fun _ => 1) (h := spMap 𝔪.yK) hw X₁.ρ.P.isLB 𝔪.A.isLB
    (fun _ => PolBaseChange.eSec_comm gp) X₁.ρ.rig X₁.ρ.rig_gen
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over _)).left) (z : Z) J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      GlobalTheory.FrameMove.rval X₁.ρ.rig (r ≫ spMap 𝔪.yK) z J = GlobalTheory.ConstFam.wVal 𝔪.wl z J J' (r ≫ eSec 𝔪.A.A) * GlobalTheory.FrameMove.rval rig' r z J' :=
    fun Z r z J J' hJ hJ' =>
      (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))
  refine ⟨rig', hrig', fun a => ?_⟩
  exact GlobalTheory.FrameMove.isTorsFrame_move gp hw hr (hx a) (X₁.ρ.fr_tors a) (hfr a).1
    (fun z J J' hJ hJ' => ((hfr a).2 z J J' hJ hJ').symm)

end GlobalTheory.Poinc.IntTerm
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

theorem unit_ne_zero_dvd (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z)
    (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V]
    [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) :
    X₁.M.Div X₁.S.th x₀ z₁ → IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) ∧ 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 ∧
      ∀ a, ∃ r : V, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ =
        algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
  intro hdiv
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  set y' : Sp V ⟶ X₁.M.Z := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy'
  set y : Sp (FractionRing V) ⟶ X₁.M.Z := jK V ≫ y' with hy
  have h1 : y' (closedPoint V) ⤳ z₁ := sp _
  set ξ := y (closedPoint (FractionRing V)) with hξ
  have hξz : ξ ⤳ z₁ := sp _
  have hyξ : ∀ w, y w ⤳ ξ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hx₀ : X₁.S.th x₀ ∈ X₁.M.O ξ := 𝔪.reg _ (X₁.S.th_mem x₀)
  have key : ∀ a, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ =
      algebraMap V (FractionRing V) (RatModel.valLoc y' z₁ h1 ⟨_, hdiv.2 a⟩) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    intro a
    have hq : X₁.S.th a / X₁.S.th x₀ ∈ X₁.M.O ξ := RatModel.O_le_of_specializes hξz (hdiv.2 a)
    have e : X₁.S.th a = X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀ := (div_mul_cancel₀ _ hdiv.1).symm
    rw [𝔪.yK_eq, 𝔪.yK_eq]
    change X₁.M.val y (X₁.S.th a) = _ * X₁.M.val y (X₁.S.th x₀)
    rw [show X₁.M.val y (X₁.S.th a) = X₁.M.val y (X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀) from congrArg _ e,
      RatModel.val_mul hyξ hq hx₀]
    congr 1
    exact RatModel.val_spMap_comp (algebraMap V (FractionRing V)) y' h1 ⟨_, hdiv.2 a⟩
  refine ⟨?_, ?_, fun a => ⟨_, key a⟩⟩
  · have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  · intro h0
    obtain ⟨c, -, hc⟩ := GoodOut.exists_th_notMem abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 X₁.ρ
      ⟨RingHom.ker 𝔪.yK, RingHom.ker_isPrime _⟩ x₀
    exact hc (by
      change 𝔪.yK _ = 0
      rw [key, h0, mul_zero])

end GlobalTheory.Poinc.IntTerm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep

theorem UMem.yK_th_ne_zero : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x₀ hd h0
  obtain ⟨c, -, h⟩ := GlobalTheory.ZH.GoodOut.exists_th_notMem GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 X₁.ρ
    ⟨RingHom.ker 𝔪.yK, RingHom.ker_isPrime 𝔪.yK⟩ 0
  refine h (RingHom.mem_ker.2 ?_)
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd' := hd.of_specializes
    (ξ := (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) (sp _)
  have hs : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have e := RatModel.val_mul hs (hd'.2 (0 + c)) (𝔪.reg _ (X₁.S.th_mem x₀))
  rw [div_mul_cancel₀ _ hd.1] at e
  rw [𝔪.yK_eq] at h0 ⊢
  exact e.trans ((congrArg (_ * ·) h0).trans (mul_zero _))

end GlobalTheory.Poinc.Sep
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep

theorem UMem.exists_th_ne_zero : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0})
    (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type)
    [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ)
    (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ),
    ∃ b, 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0 := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI : CharZero (FractionRing V) :=
    (RingHom.charZero_iff (IsFractionRing.injective V (FractionRing V))).1 inferInstance
  exact GlobalTheory.ThetaGeneric.exists_th_ne_zero GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 _ _ X₁.S X₁.ρ
    (FractionRing V) 𝔪.yK

end GlobalTheory.Poinc.Sep

end
end
