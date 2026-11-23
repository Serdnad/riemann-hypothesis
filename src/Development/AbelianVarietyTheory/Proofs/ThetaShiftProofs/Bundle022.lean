module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle068
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QkRelQkScaleEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle100
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpTan

open GlobalTheory.HolHom GlobalTheory.TorusModel

theorem le_wchart_iff {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (x : Z ⟶ Y)
    (j : K → L.ι) : ⊤ ≤ LB.wchart L (fun k => x ≫ ψ k) j ↔ ⊤ ≤ x ⁻¹ᵁ LB.wchart L ψ j :=
  ⟨fun h _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h hy) k,
    fun h _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h hy) k⟩

theorem valR_of_corr {A : Type} [CommRing A] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Sp A ⟶ X)} {ψ : K → (Y ⟶ X)} {ε : K → ℤ} {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen)
    {t : LB.Gen (LB.LinComb L ψ ε)} (ht : t.IsGen) (x : Sp A ⟶ Y) (hφ : φ = fun k => x ≫ ψ k)
    (h : LB.Gen.Corr L _ _ _ _ u (LB.pullGen L _ _ t x)) (j : K → L.ι) :
    valR (𝟙 (Sp A)) (LB.wchart L φ j) (u.s j).val = valR x (LB.wchart L ψ j) (t.s j).val := by
  subst hφ
  obtain rfl := TorusCoord.gen_eq_of_corr hL hu (DVR.pullGen_isGen _ _ _ _ ht x) h
  by_cases hj : ⊤ ≤ x ⁻¹ᵁ LB.wchart L ψ j
  · have hj' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart L (fun k => x ≫ ψ k) j := (le_wchart_iff L ψ x j).2 hj
    refine (valR_res (U := x ⁻¹ᵁ LB.wchart L ψ j) (𝟙 (Sp A)) _ _ hj').trans ?_
    exact (valR_comp (𝟙 (Sp A)) x (LB.wchart L ψ j) _).symm.trans (by rw [Category.id_comp])
  · have h₀ : valR x (LB.wchart L ψ j) (t.s j).val = 0 := dite_eq_right hj
    exact (dite_eq_right (fun h => hj ((le_wchart_iff L ψ x j).1 h))).trans h₀.symm

section Coord

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (c : GtCoord I D e G)
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]


open CoordToExt in
theorem holAt_of_coord {x : V → (Sp ℂ ⟶ (thickObj R I e G).left)} {z : V}
    (hb : HolAt (fun t => x t ≫ c.q.left) z)
    (hs : ∀ χ a, ⊤ ≤ x z ⁻¹ᵁ LB.wchart D.P.L (D.Oφ c.pG χ) a →
      DifferentiableAt ℂ (fun t => valAt' (x t) (LB.wchart D.P.L (D.Oφ c.pG χ) a) ((c.t χ).s a).val) z) :
    HolAt x z := by
  let b := Module.Free.chooseBasis ℤ D.X
  let p := (x z ≫ c.q.left) (default : PrimeSpectrum ℂ)
  choose a ha using fun k => exists_chart (DVR.linComb_isLB (Y := (thickObj R I e D.P.A).left) D.P.L D.P.isLB
    (D.Oφ (D.prBe I e) (b k)) Oε) p
  have hW : ⊤ ≤ (x z ≫ c.q.left) ⁻¹ᵁ ⨅ k, (bundle I D e (b k)).U (a k) := by
    rw [le_preimage_iff, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.2 ha
  obtain ⟨P, hP, hxP, hle⟩ := exists_affine _ hW
  have hl : ∀ k, c.q.left ⁻¹ᵁ P ≤ c.q.left ⁻¹ᵁ (bundle I D e (b k)).U (a k) := fun k =>
    Scheme.Hom.preimage_mono _ (hle.trans (iInf_le _ k))
  let u : ∀ k, Γ((thickObj R I e G).left, c.q.left ⁻¹ᵁ P)ˣ := fun k => res (hl k) (coordUnit c (b k) (a k))
  have := c.q_hom
  have := c.q_affine
  have bij := bijective_of_basis b c.q c.i c.q_hom c.i_hom c.q_flat c.q_surj c.q_affine c.isKernel P hP u
    (fun k Z t g w hw => by
      have hw' := GtBaseChange.translate_mem c.q c.i c.isKernel t g P w hw
      exact (gm_res _ w (hl k) hw' _).trans ((coordUnit_weight c (b k) (a k) Z t g w (hl k hw)).trans
        (congrArg _ (gm_res _ w (hl k) hw _).symm)))
  have ev : ∀ᶠ t in 𝓝 z, ⊤ ≤ x t ⁻¹ᵁ (c.q.left ⁻¹ᵁ P) := (hb P hxP).1
  let S : Subring Γ((thickObj R I e G).left, c.q.left ⁻¹ᵁ P) :=
    { carrier := {f | DifferentiableAt ℂ (fun t => valAt' (x t) _ f) z}
      mul_mem' := fun {f f'} h h' => (h.mul h').congr_of_eventuallyEq (ev.mono fun t ht => by
        simp only [valAt'_eq_valR, valR_eq _ _ ht, map_mul, Pi.mul_apply])
      add_mem' := fun {f f'} h h' => (h.add h').congr_of_eventuallyEq (ev.mono fun t ht => by
        simp only [valAt'_eq_valR, valR_eq _ _ ht, map_add (f := _), Pi.add_apply])
      neg_mem' := fun {f} h => h.neg.congr_of_eventuallyEq (ev.mono fun t ht => by
        simp only [valAt'_eq_valR, valR_eq _ _ ht, map_neg, Pi.neg_apply])
      one_mem' := (differentiableAt_const (1 : ℂ)).congr_of_eventuallyEq (ev.mono fun t ht => by
        simp only [valAt'_eq_valR, valR_eq _ _ ht, map_one])
      zero_mem' := (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq (ev.mono fun t ht => by
        simp only [valAt'_eq_valR, valR_eq _ _ ht, map_zero]) }
  have hu : ∀ k, (u k).val ∈ S := fun k => by
    have h₁ := hs (b k) (a k) (fun y hy => mem_chart c _ _ _ (hl k (hxP hy)))
    refine h₁.congr_of_eventuallyEq (ev.mono fun t ht => ?_)
    exact (valR_res (x t) (hl k) _ ht).trans (valR_res (x t) _ _ (fun y hy => hl k (ht hy)))
  have hi : ∀ w : Γ((thickObj R I e G).left, c.q.left ⁻¹ᵁ P)ˣ, w.val ∈ S → (w⁻¹).val ∈ S := fun w hw => by
    have hne : valAt' (x z) _ w.val ≠ 0 := by
      rw [valAt'_eq_valR, valR_eq (x z) (c.q.left ⁻¹ᵁ P) hxP]
      exact (w.isUnit.map _).ne_zero
    refine (DifferentiableAt.inv hw hne).congr_of_eventuallyEq (ev.mono fun t ht => ?_)
    simp only [valAt'_eq_valR, valR_eq _ _ ht, Pi.inv_apply, map_units_inv]
  refine holAt_of_affine (hP.preimage c.q.left) hxP ev fun f => ?_
  obtain ⟨f, rfl⟩ := bij.2 f
  change _ ∈ S
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add f f' h h' => rw [map_add (f := _)]; exact add_mem h h'
  | single χ r =>
    have hχ : ∀ χ : D.X, ((b.constr ℤ (fun k => Additive.ofMul (u k)) χ).toMul).val ∈ S := fun χ => by
      have : χ ∈ Submodule.span ℤ (Set.range b) := b.mem_span χ
      induction this using Submodule.span_induction with
      | mem _ h => obtain ⟨k, rfl⟩ := h; rw [b.constr_basis]; exact hu k
      | zero => rw [map_zero]; exact one_mem _
      | add _ _ _ _ h h' => rw [map_add (f := _)]; exact mul_mem h h'
      | smul n w _ h =>
        rw [map_smul, toMul_zsmul]
        cases n with
        | ofNat n => simpa using pow_mem h n
        | negSucc n => rw [zpow_negSucc]; exact hi _ (by simpa using pow_mem h (n + 1))
    rw [AddMonoidAlgebra.liftNCRingHom_single]
    refine mul_mem ?_ (hχ χ)
    exact ((hb P hxP).2 r).congr_of_eventuallyEq (Eventually.of_forall fun t => (valR_comp (x t) c.q.left P r).symm)

end Coord

theorem exists_represents {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {H : Over (Spec (CommRingCat.of R))}
    [GrpObj H] [IsCommMonObj H] (hG : GlobalFnsSt) (c : GtCoord ⊥ D 0 H) :
    ∃ Φ : ∀ T, (T ⟶ H) ≃ GtPt D T, Represents Φ ∧
      ∀ T (x : T ⟶ H), TorusCoord.IsPointOf c (x.left ≫ inv (fstG (⊥ : Ideal R) 0 H).left) (Φ T x) := by
  let j := inv (fstG (⊥ : Ideal R) 0 H).left
  have hj : j ≫ (thickObj R ⊥ 0 H).hom ≫ thick R ⊥ 0 = H.hom :=
    (congrArg (j ≫ ·) (Over.w (fstG (⊥ : Ideal R) 0 H)).symm).trans (IsIso.inv_hom_id_assoc _ _)
  choose φ hφ using fun T (x : T ⟶ H) => TorusCoord.exists_isPointOf c (T := T) (x.left ≫ j)
    (by rw [Category.assoc, hj, Over.w])
  have bij : ∀ T, Function.Bijective (φ T) := fun T => by
    refine ⟨fun x x' e => Over.OverMorphism.ext ((cancel_mono j).1
      ((hφ T x).unique_left c (e ▸ hφ T x'))), fun ξ => ?_⟩
    obtain ⟨y, hy⟩ := TorusCoord.exists_point c (T.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
    refine ⟨Over.homMk (y ≫ (fstG (⊥ : Ideal R) 0 H).left) ((Category.assoc _ _ _).trans
      ((congrArg (y ≫ ·) (Over.w (fstG (⊥ : Ideal R) 0 H))).trans (hy.comp_hom c))), (hφ T _).unique_right c ?_⟩
    have : (y ≫ (fstG (⊥ : Ideal R) 0 H).left) ≫ j = y := by simp [j]
    exact this.symm ▸ hy
  refine ⟨fun T => Equiv.ofBijective _ (bij T), ⟨fun T' T k x => (hφ T x).isPull c ?_, fun T x x' => ?_⟩, hφ⟩
  · have := hφ T' (k ≫ x)
    rwa [Over.comp_left, Category.assoc] at this
  · obtain ⟨T, ⟨⟨⟩⟩, s⟩ := T
    change T ⟶ Spec (CommRingCat.of R) at s
    obtain ⟨σ, rfl⟩ : ∃ σ, s = σ ≫ thick R ⊥ 0 := ⟨s ≫ inv (thick R ⊥ 0), by simp⟩
    let Z : Over (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1)))) := Over.mk σ
    obtain ⟨a, ha⟩ := FormalPoint.exists_lift_fstG (Z := Z) x
    obtain ⟨a', ha'⟩ := FormalPoint.exists_lift_fstG (Z := Z) x'
    have key : ∀ (b : Z ⟶ thickObj R ⊥ 0 H) (w : (Over.map (thick R ⊥ 0)).obj Z ⟶ H),
        (Over.map (thick R ⊥ 0)).map b ≫ fstG ⊥ 0 H = w → φ _ w = TorusCoord.pointsEquiv c Z b := by
      rintro b _ rfl
      refine ((TorusCoord.toGtPt_eq_iff c b _).2 ?_).symm
      have e : ((Over.map (thick R ⊥ 0)).map b ≫ fstG ⊥ 0 H).left ≫ j = b.left := by
        rw [Over.comp_left, Category.assoc, IsIso.hom_inv_id, Category.comp_id]; rfl
      exact e ▸ hφ _ _
    have e₁ := key a x ha
    have e₂ := key a' x' ha'
    have e₃ := key (a * a') (x * x') (by rw [FormalPoint.map_mul_fstG, ha, ha'])
    have := TorusCoord.isAdd_pointsEquiv c hG a a'
    rw [← e₁, ← e₂, ← e₃] at this
    exact this

theorem exists_model (hG : GlobalFnsSt) (D : DegPre ℂ) :
    ∃ (H : Over (Sp ℂ)) (_ : GrpObj H) (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), Smooth H.hom ∧ Represents Φ ∧
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (y : Sp ℂ ⟶ Sp ℂ) (e : V → (Over.mk y ⟶ H)) (z : V),
        HolAt (fun t => (show Sp ℂ ⟶ _ from (Φ _ (e t)).b.left)) z →
        (∀ χ j, ⊤ ≤ LB.wchart D.P.L (DegPre.gtφT D _ (Φ _ (e z)).b χ) j → DifferentiableAt ℂ (fun t =>
          valR (A := ℂ) (𝟙 _) (LB.wchart D.P.L (DegPre.gtφT D _ (Φ _ (e t)).b χ) j)
            (((Φ _ (e t)).s χ).s j).val) z) →
        HolAt (fun t => (show Sp ℂ ⟶ _ from (e t).left)) z := by
  obtain ⟨H, _, _, h⟩ := exists_isGt hG (splitExt D)
  obtain ⟨c⟩ := nonempty_gtCoord hG h ⊥ 0
  obtain ⟨Φ, h₁, h₂⟩ := exists_represents hG c
  refine ⟨H, inferInstance, Φ, (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ H h).1, h₁, fun V _ _ y e z hb hs => ?_⟩
  let j := inv (fstG (⊥ : Ideal ℂ) 0 H).left
  have hφ : ∀ t χ, DegPre.gtφT D _ (Φ _ (e t)).b χ = fun k => ((e t).left ≫ j) ≫ D.Oφ c.pG χ k := fun t χ =>
    funext fun k => (Category.id_comp _).symm.trans ((TorusCoord.comp_eq_of_left (Φ _ (e t)).b c.pG (𝟙 _)
      ((e t).left ≫ j) ((Category.id_comp _).trans (h₂ _ (e t)).1)).1 χ k)
  have H₁ : HolAt (fun t => (show Sp ℂ ⟶ _ from (e t).left ≫ j)) z := by
    refine holAt_of_coord c ?_ fun χ a ha => ?_
    · have := hb.comp (inv (fstG (⊥ : Ideal ℂ) 0 D.P.A).left)
      refine (congrArg (fun q => HolAt q z) (funext fun t => ?_)).mp this
      exact ((IsIso.eq_comp_inv (fstG (⊥ : Ideal ℂ) 0 D.P.A).left).2
        ((h₂ _ (e t)).1.trans (Category.assoc _ _ _).symm).symm).symm
    · have := hs χ a (by rw [hφ]; exact (le_wchart_iff _ _ _ a).2 ha)
      convert this using 2 with t
      exact (valR_of_corr (A := ℂ) D.P.isLB ((Φ _ (e t)).isGen χ) (c.t_gen χ) _ (hφ t χ) ((h₂ _ (e t)).2 χ) a).symm
  have := H₁.comp (fstG (⊥ : Ideal ℂ) 0 H).left
  convert this using 2 with t
  simp [j]

end GlobalTheory.ExpTan
end
end

section

noncomputable section

namespace GlobalTheory.TauTwist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusExt

section Sections

variable {X Y Z : Scheme.{0}} {L : LB X} {K K₁ K₂ K₃ : Type} [Fintype K] [Fintype K₁] [Fintype K₂] [Fintype K₃]

def scaleSec {M : LB Y} (c : Γ(Y, ⊤)ˣ) (s : LB.Sec M) : LB.Sec M where
  f j := (res (le_top : M.U j ≤ ⊤) c).val * s.f j
  compat i j := by
    have e : ∀ {W W' : Y.Opens} (h : W' ≤ W), (Y.presheaf.map (homOfLE h).op).hom (res (le_top : W ≤ ⊤) c).val =
        (res (le_top : W' ≤ ⊤) c).val := fun h => congrArg Units.val (res_res' _ _ c)
    rw [map_mul, map_mul, s.compat i j, e, e, mul_left_comm]

theorem sval_scaleSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : Γ(Y, ⊤)ˣ) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : sval (scaleSec c s) r z J = (gm r z ⊤ c).val * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ (hJ.mem φ r) _).trans
    (congrArg Units.val (gm_res r z le_top (hJ.mem φ r) c))) rfl)

variable {F : Type} [Field F]

def constUnit (p : Y ⟶ Sp F) (a : Fˣ) : Γ(Y, ⊤)ˣ := pullU p ⊤ (unitOn a)

theorem gm_constUnit (p : Y ⟶ Sp F) (a : Fˣ) (r : Z ⟶ Y) (z : Z) : gm r z ⊤ (constUnit p a) = unitAt (r ≫ p) z a :=
  gm_pull r p z ⊤ trivial (unitOn a)

theorem secRel_scale (hL : L.IsLB) (p : Y ⟶ Sp F) {h : Y ⟶ Y} (hp : h ≫ p = p) {e : Sp F ⟶ Y} (he : e ≫ p = 𝟙 _)
    {φ₁ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {φ₃ : K₃ → (Y ⟶ X)} {ε₃ : K₃ → ℤ}
    {φ : K → (Sp F ⟶ X)} {ε : K → ℤ} (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)) (s₂ : LB.Sec (LB.LinComb L φ₂ ε₂))
    {v v' : LB.Gen (LB.LinComb L φ ε)} {a b c : Fˣ} (habc : a = b * c)
    (hv : ∀ y J, Good L y J → val v' (𝟙 _) y J = unitAt (𝟙 _) y c * val v (𝟙 _) y J)
    (H : ∀ u : LB.Gen (LB.LinComb L φ₃ ε₃), u.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u e) v →
      GeneratorPullback.SecRel L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h φ₃ ε₃ u)
    (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen) (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u e) v') :
    GeneratorPullback.SecRel L φ₁ ε₁ (scaleSec (constUnit p a) s₁) φ₂ ε₂ (scaleSec (constUnit p b) s₂) h φ₃ ε₃ u := by
  have H₀ := (secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 (H (scaleGen (constUnit p c⁻¹) u) (scaleGen_isGen _ _ hu)
    (corr_of_val hL fun y J hJ => by
      have e₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ hc (𝟙 _)).trans (hv y J hJ))
      rw [val_pull hJ, val_scaleGen _ _ _ hJ, gm_constUnit, e₁, Category.assoc, he, Category.id_comp, map_inv,
        inv_mul_cancel_left]))
  refine (secRel_iff hL _ _ _ _ _ _ _ _ _ _).2 fun y J hJ => ?_
  rw [sval_scaleSec _ _ _ hJ, sval_scaleSec _ _ _ hJ, H₀ _ _ y J hJ, val_scaleGen _ _ _ hJ, gm_constUnit, gm_constUnit,
    gm_constUnit, Category.assoc, hp, habc, map_mul, map_inv, Units.val_mul, Units.val_mul]
  have := (unitAt (𝟙 Y ≫ p) y c).mul_inv
  linear_combination ((unitAt (𝟙 Y ≫ p) y b).val * sval s₂ (𝟙 Y ≫ h) y J * (val u (𝟙 Y) y J).val) * this

end Sections

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {ψ : PsiFam D} {hψ : ∀ χ, (ψ χ).IsGen}
  {F : Type} [Field F] [Algebra (FractionRing R) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.X] {w : O} {t : D.X → D.X → (FractionRing R)ˣ} {k : ℕ}
  {r : D.X → D.X → Fˣ}

def famScale (hw : w + star w = 1) (ht : IsScalarForm O t) (hq : PsiRel D ψ fun y => t y (w • y))
    (hr : IsRootForm O k t r) (hψ : ∀ χ, (ψ χ).IsGen) (s : Fam D F k) : Fam (withPsi D ψ hψ) F k where
  s α := scaleSec (constUnit (fst (TF (R := R) F) D.P.A).left (r α (w • α))) (s.s α)
  fe mu α := by
    refine secRel_scale D.P.isLB (fst (TF (R := R) F) D.P.A).left
      (congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trF D F mu ≫ _ = _))
      (congrArg (fun q => q.left) (lift_fst _ _ : DegPre.zF D F ≫ _ = _)) _ _
      (c := Units.map (algebraMap (FractionRing R) F).toMonoidHom (t mu α * t mu (w • mu) ^ k)) ?_
      (fun y J hJ => ?_) (s.fe mu α)
    · rw [hr.1.refine_add hw, map_mul, map_pow, ← hr.2, ← hr.2, smul_comm w k mu, hr.1.nsmul_left, hr.1.nsmul_right,
        hr.1.nsmul_right, hr.1.symm α mu]
      ac_rfl
    · have key : ∀ (y : (TF (R := R) F).left) J, Good D.P.L y J →
          val (DegPre.famMult (withPsi D ψ hψ) F k mu α) (𝟙 (TF (R := R) F) :).left y J =
          unitAt ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) y (t mu α * t mu (w • mu) ^ k) *
            val (DegPre.famMult D F k mu α) (𝟙 (TF (R := R) F) :).left y J := fun y J hJ => by
        rw [val_famMult (D := D) (𝟙 (TF (R := R) F)) hJ k mu α]
        refine (val_famMult (D := withPsi D ψ hψ) (𝟙 (TF (R := R) F)) hJ k mu α).trans ?_
        refine (congrArg₂ (· * ·) (hq.val_tau (ht.refine_add hw mu α) _ hJ) (congrArg₂ (· * ·)
          ((val_powGen _ _ _ _ _).trans (congrArg (· ^ k) (hq mu _ _ y J hJ))) rfl)).trans ?_
        rw [map_mul, map_pow, mul_pow, val_powGen (D.psi mu), _root_.mul_assoc (_ ^ k), _root_.mul_mul_mul_comm]
        rfl
      exact (key y J hJ).trans (congrArg₂ (· * ·) (unitAt_spMap _ (algebraMap (FractionRing R) F) y _) rfl)

variable (hw : w + star w = 1) (ht : IsScalarForm O t) (hq : PsiRel D ψ fun y => t y (w • y)) (hr : IsRootForm O k t r)

theorem phiRel_famScale (p : QkPt D F k)
    (v : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) {s s' : Fam D F k}
    (h : PhiRel D F k p v s s') :
    PhiRel (withPsi D ψ hψ) F k (qkScale hw ht hq hr hψ p) (scaleGen (unitOn (r p.y (w • p.y))) v)
      (famScale hw ht hq hr hψ s) (famScale hw ht hq hr hψ s') := fun α => by
  refine secRel_scale D.P.isLB (fst (TF (R := R) F) D.P.A).left
    (congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trPt D F p.g.b ≫ _ = _))
    (congrArg (fun q => q.left) (lift_fst _ _ : DegPre.zF D F ≫ _ = _)) _ _
    (c := r p.y α * r p.y (w • p.y)) ?_ (fun y J hJ => ?_) (h α)
  · show r (α + p.y) (w • (α + p.y)) = _
    rw [hr.1.refine_add hw, hr.1.symm α p.y]
    ac_rfl
  · refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_scale (r p.y α) (p.g.s α) _ hJ)
      (val_scale (r p.y (w • p.y)) v _ hJ)).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_mul hJ _ _ _).symm)))
    rw [map_mul, _root_.mul_mul_mul_comm]

include hw ht hq hr

theorem QkRel.weilQkIs_of {p q : QkPt D F k} {p' q' : QkPt (withPsi D ψ hψ) F k} (hp : QkRel r p p') (hq' : QkRel r q q')
    {ζ : F} (h : WeilQkIs (withPsi D ψ hψ) F k p' q' ζ) : WeilQkIs D F k p q ζ := by
  obtain rfl := (qkRel_qkScale hw ht hq hr p).unique hp
  obtain rfl := (qkRel_qkScale hw ht hq hr q).unique hq'
  intro v v' hv hv' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ α j
  have e := h _ _ (scaleGen_isGen _ _ hv) (scaleGen_isGen _ _ hv') _ _ _ _ _ (phiRel_famScale hw ht hq hr q v' h₁)
    (phiRel_famScale hw ht hq hr p v h₂) (phiRel_famScale hw ht hq hr p v h₃) (phiRel_famScale hw ht hq hr q v' h₄) α j
  exact (Units.mul_right_inj _).1 (e.trans (mul_left_comm _ _ _))

theorem QkRel.weilQkIs_iff {p q : QkPt D F k} {p' q' : QkPt (withPsi D ψ hψ) F k} (hp : QkRel r p p')
    (hq' : QkRel r q q') (ζ : F) : WeilQkIs (withPsi D ψ hψ) F k p' q' ζ ↔ WeilQkIs D F k p q ζ :=
  ⟨hp.weilQkIs_of hw ht hq hr hq',
    QkRel.weilQkIs_of (D := withPsi D ψ hψ) hw ht.inv hq.symm hr.inv hp.symm hq'.symm⟩

end GlobalTheory.TauTwist
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.existsUnique_lift_coords_localSubring : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (L : LB G.left) (U : S.Opens) (N n : ℕ) (b : Fin n → LB.Sec (Out.powOver G L U N)) (R K : Type) [CommRing R] [IsLocalRing R] [CommRing K] [IsLocalRing K] (f : R →+* K) (y : Sp R ⟶ S) (x : Sp K ⟶ (G.hom ⁻¹ᵁ U).toScheme) (cf : Fin n → R) (j : L.ι) (u : Kˣ), L.IsLB → IsAffineOpen U → AmpleSpan.EmbedsBy (G.hom ∣_ U) b → Function.Injective f → ⊤ ≤ y ⁻¹ᵁ U → x ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = spMap f ≫ y → ⊤ ≤ (x ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → (∀ i, valR x ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = f (cf i) * u) → (∃ i, IsUnit (cf i)) → ∃! x' : Sp R ⟶ (G.hom ⁻¹ᵁ U).toScheme, x' ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = y ∧ spMap f ≫ x' = x ∧ ∀ j', ⊤ ≤ (x' ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j' → ∃ u' : Rˣ, ∀ i, valR x' ((Out.powOver G L U N).U (fun _ => j')) ((b i).f (fun _ => j')) = cf i * u' := by
  first | exact @GlobalTheory.LiftPoint.existsUnique_lift | exact GlobalTheory.LiftPoint.existsUnique_lift | (intros; apply GlobalTheory.LiftPoint.existsUnique_lift <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.TwoFrames

theorem valR_eq_valAt' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valR x U f = valAt' x U f := by
  unfold valR valAt' valAt
  congr

theorem map_map {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (f : Γ(X, U)) :
    (X.presheaf.map (homOfLE k).op).hom ((X.presheaf.map (homOfLE h).op).hom f) =
      (X.presheaf.map (homOfLE (k.trans h)).op).hom f := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem exists_sec_of_pow_one {Z Z' : Scheme.{0}} {L : LB Z} {p : Z' ⟶ Z} (σ : SecP L p 1) :
    ∃ s : (L.pull p).Sec, ∀ (j : L.ι) (x : Sp ℂ ⟶ Z'), ⊤ ≤ (x ≫ p) ⁻¹ᵁ L.U j →
      valAt' x ((L.pull p).U (fun _ => j)) (s.f (fun _ => j)) = ArcPts.sval σ x j := by
  have le : ∀ J : PUnit → L.ι, (L.pull p).U J ≤ LB.wchart L (fun _ : Fin 1 => p) (fun _ => J PUnit.unit) :=
    fun J y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy PUnit.unit
  refine ⟨⟨fun J => (Z'.presheaf.map (homOfLE (le J)).op).hom (σ.f (fun _ => J PUnit.unit)), fun J J' => ?_⟩,
    fun j x hx => ?_⟩
  · have h := congrArg (Z'.presheaf.map (homOfLE (inf_le_inf (le J) (le J'))).op).hom
      (σ.compat (fun _ => J PUnit.unit) (fun _ => J' PUnit.unit))
    refine ((map_map _ _ _).trans (map_map _ _ _).symm).trans (h.trans ((map_mul _ _ _).trans ?_))
    refine congrArg₂ (· * ·) ?_ ((map_map _ _ _).trans (map_map _ _ _).symm)
    simp only [LB.LinComb, Finset.univ_unique, Finset.prod_singleton, Nat.cast_one, zpow_one]
    refine (map_map _ _ _).trans ?_
    symm
    refine Eq.trans (congrArg Units.val (?_ : (L.pull p).g J J' = res (le_inf (inf_le_left.trans
      (LB.wchart_le L _ J PUnit.unit)) (inf_le_right.trans (LB.wchart_le L _ J' PUnit.unit)))
      (pullU p _ (L.g (J PUnit.unit) (J' PUnit.unit))))) rfl
    show ∏ k : PUnit, _ = _
    have hp : ∀ {G : Type} [CommGroup G] (x : G), ∏ _k : PUnit.{1}, x ^ (1 : ℤ) = x := fun x => by simp
    exact hp _
  · refine Eq.trans ?_ (valR_eq_valAt' x _ _).symm
    exact GlobalTheory.valAt'_map x _ _ (fun q hq => mem_pull.2 ((top_le_preimage_comp _ _ _).1 hx hq))

theorem two_frames : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (A : AnArc (𝓞 E)) lin cst (w : ℂ) (y₀ : Sp ℂ ⟶ Xo.X) (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) fr (g : ℕ) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left)) (ϑ : (Fin g → ℂ) → ℂ) fr', IsFibAt A Xo.univ.t lin cst w y₀ π fr → (∀ v, e (h v) = (π v).left) → IsThetaFrameAt Xo.univ.t.PP y₀ e ϑ fr' → (∃ z, ϑ z ≠ 0) → ∀ th ∈ A.Theta 1 0, (∃ v, A.Sum 1 0 th w v ≠ 0) → ∃ (lam : ℂ) (f : A.V → ℂ), lam ≠ 0 ∧ Differentiable ℂ f ∧ (∀ v, f v ≠ 0) ∧ f 0 = 1 ∧ (∀ v j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h v) = f v * fr j v) ∧ ∀ v, A.Sum 1 0 th w v = lam * ϑ (h v) * f v := by
  intro hL _ E _ _ _ H _ D l Xo A lin cst w y₀ π fr g h e ϑ fr' hF he hT hϑ th hth hS
  obtain ⟨d', n', c', r', s', hs'⟩ := hT
  have ch : ∀ v, ∃ j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun v => by
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB ((π v).left (default : PrimeSpectrum ℂ))
    exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩
  choose J hJ using ch
  have n : ∀ v j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j v ≠ 0 := fun v j hj => ((hF.frm v).1 j hj).ne_zero
  have key : ∀ v j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h v) = fr' (J v) (h v) / fr (J v) v * fr j v := by
    intro v j hj
    have hi := (top_le_preimage_inf _ _ _).2 ⟨hj, hJ v⟩
    have a := (hF.frm v).2 j (J v) hi
    have b := c' j (J v) (h v) (by rw [he]; exact hi)
    rw [he] at b
    rw [valR_eq_valAt'] at a
    beta_reduce at a
    have := n v _ (hJ v)
    rw [b, a]
    field_simp
  obtain ⟨σ, hσ⟩ := hF.sec th hth
  obtain ⟨s, hs⟩ := exists_sec_of_pow_one σ
  obtain ⟨u, hu⟩ := ThetaFamily.exists_values_line_fibre hL.globalSectionsRank Xo.univ y₀
  obtain ⟨a, ha⟩ := hu s
  obtain ⟨a', ha'⟩ := hu s'
  have f1 : ∀ v, fib (π v) ≫ pullback.fst _ _ = (π v).left := fun v => pullback.lift_fst _ _ _
  have f2 : ∀ v, fib (π v) ≫ pullback.snd _ _ = 𝟙 _ := fun v => pullback.lift_snd _ _ _
  have m : ∀ v, ⊤ ≤ (fib (π v) ≫ pullback.fst _ _) ⁻¹ᵁ Xo.univ.t.PP.L.U (J v) := fun v => by
    rw [f1]; exact hJ v
  have m' : ∀ v, ⊤ ≤ fib (π v) ⁻¹ᵁ (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y₀)).U (fun _ => J v) :=
    fun v q hq => mem_pull.2 ((top_le_preimage_comp _ _ _).1 (m v) hq)
  have e1 : ∀ v, A.Sum 1 0 th w v * fr (J v) v = a * u (fun _ => J v) (fib (π v)) := fun v => by
    rw [← ha _ _ (f2 v) (m' v), hs _ _ (m v), hσ v _ (m v), pow_one]
  have e2 : ∀ v, ϑ (h v) * fr' (J v) (h v) = a' * u (fun _ => J v) (fib (π v)) := fun v => by
    rw [← ha' _ _ (f2 v) (m' v),
      hs' _ (h v) _ ((f1 v).trans (he v).symm) (f2 v) (by rw [he]; exact hJ v)]
  have n'' : ∀ v, fr' (J v) (h v) ≠ 0 := fun v => n' _ _ (by rw [he]; exact hJ v)
  have a0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := hS
    exact mul_ne_zero hv (n v _ (hJ v)) ((e1 v).trans (zero_mul _))
  have a0' : a' ≠ 0 := by
    rintro rfl
    obtain ⟨z, hz⟩ := hϑ
    obtain ⟨v, rfl⟩ := h.surjective z
    exact mul_ne_zero hz (n'' v) ((e2 v).trans (zero_mul _))
  refine ⟨a / a', fun v => fr' (J v) (h v) / fr (J v) v, div_ne_zero a0 a0', fun v₀ => ?_,
    fun v => div_ne_zero (n'' v) (n v _ (hJ v)), ?_, key, fun v => ?_⟩
  · have op : IsOpen {v | ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U (J v₀)} := by
      simpa using (hF.hol (Xo.univ.t.PP.L.U (J v₀)) 0).1
    have nh := op.mem_nhds (hJ v₀)
    have d1 : DifferentiableOn ℂ (fun v => fr' (J v₀) (h v))
        {v | ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U (J v₀)} :=
      (d' (J v₀)).comp h.differentiable.differentiableOn fun v hv => by
        show ⊤ ≤ e (h v) ⁻¹ᵁ _
        rw [he]; exact hv
    have d2 := ((d1.mul ((hF.fr_hol (J v₀)).inv fun v hv => n v _ hv)).differentiableAt nh)
    refine d2.congr_of_eventuallyEq (Filter.mem_of_superset nh fun v hv => ?_)
    show fr' (J v) (h v) / fr (J v) v = fr' (J v₀) (h v) * (fr (J v₀) v)⁻¹
    rw [key v _ hv, mul_inv_cancel_right₀ (n v _ hv)]
  · show fr' (J 0) (h 0) / fr (J 0) 0 = 1
    have h0 : e 0 = (π 0).left := by rw [← he, map_zero]
    rw [div_eq_one_iff_eq (n 0 _ (hJ 0)), map_zero, r' _ (by rw [h0]; exact hJ 0), hF.rig _ (hJ 0)]
  · have := n v _ (hJ v)
    have b1 := e1 v
    have b2 := e2 v
    field_simp
    linear_combination a' * b1 - a * b2

end GlobalTheory.TwoFrames
end
end
