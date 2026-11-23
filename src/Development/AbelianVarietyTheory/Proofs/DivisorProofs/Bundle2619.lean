module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle035
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle013
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle653
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2609
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle628

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.FibreCmp

theorem isDerivAt0_comp_linear {g g' : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (he : IsHolTo Set.univ e) (L : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (w : Fin g' → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (L z)) w v ↔ IsDerivAt0 e (L w) v := by
  have key : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 →
      ∀ (U : X.Opens) (_ : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (L z)) U f) 0 w =
        fderiv ℂ (fun z => valAt' (e z) U f) 0 (L w) := by
    intro h0 U hU f
    have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e b ⁻¹ᵁ U} := by
      refine ⟨trivial, ?_⟩
      rw [← h0]
      intro x _
      exact hU (Set.mem_univ _)
    have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 :=
      ((he U f).2 0 hmem).differentiableAt ((he U f).1.mem_nhds hmem)
    let L' := LinearMap.toContinuousLinearMap L
    have hd' : HasFDerivAt (fun z => valAt' (e z) U f) (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L' 0) := by
      rw [map_zero]; exact hd.hasFDerivAt
    have := (hd'.comp (0 : Fin g' → ℂ) L'.hasFDerivAt).fderiv
    exact DFunLike.congr_fun this w
  unfold IsDerivAt0
  simp only [map_zero]
  exact and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => by
    rw [key h0 U hU f]

theorem valAt'_comp_app {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [Scheme.Hom.app_eq_appLE]
    exact valAt'_appLE _ _ _ _ _ _ h
  · have h' : ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := h
    unfold valAt'
    rw [dite_eq_right h, dite_eq_right h']

theorem isDerivAt0_of_isDiff {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {Y : Scheme.{0}}
    (φ : A.left ⟶ Y) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)}
    (he : ∀ z, (u.ex z).left ≫ φ = e z) (hv : IsTangent v) (hd : u.IsDiff w v) :
    IsDerivAt0 e w ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ) := by
  obtain rfl : (fun z => (show Sp ℂ ⟶ _ from (u.ex z).left) ≫ φ) = e := funext he
  refine ⟨?_, fun U hU f => ?_⟩
  · rw [← Category.assoc]
    refine congrArg (· ≫ φ) (hv.trans ?_)
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
    simp
  · have := hd (φ ⁻¹ᵁ U) hU ((φ.app U).hom f)
    simp only [valAt'_comp_app] at this
    rw [← this, Scheme.Hom.comp_appLE]
    rfl


open FibreUnif in
theorem exists_equiv_of_polAV {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty)
    (i : Fin FU.n) {Pe : (FU.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (FU.Di i) ty Pe) (P : Out.PolAV (Sp ℂ))
    (φ : P.A.left ⟶ Xo.univ.t.G.left) (hp : IsGrpPullback P.A Xo.univ.t.G (FU.u i Pe) φ)
    (hL : LBIso P.L (Xo.univ.t.PP.L.pull φ)) {g : ℕ} (u : HolUnif P.A P.L g) {Hm : Matrix (Fin g) (Fin g) ℂ}
    {κ : u.Λ → ℂ} (hAH : u.IsAH Hm κ) :
    ∃ F : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ z, (u.ex (F z)).left ≫ φ = (FU.ex i Pe z).left) ∧
      (∀ z, F z ∈ u.Λ ↔ z ∈ Pe.range) ∧
      (∀ a b, (hermForm Hm (F (Pe a)) (F (Pe b))).im = (FU.Di i).EF a b) ∧
      ∀ (w : Fin g₀ → ℂ) (v : epsR ℂ ⟶ P.A), IsTangent v → (u.IsDiff (F w) v ↔
        IsDerivAt0 (fun z => (FU.ex i Pe z).left) w ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ)) := by
  obtain ⟨w, hw⟩ := hL
  obtain ⟨Ef, hEf, -, -, ht₁, ht₂, hweil⟩ := AHWeil.tangent_and_weil_of_isAH thetaUnifAV_all P g u Hm κ hAH
  have inj : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x.left ≫ φ = y.left ≫ φ → x = y := fun x y h =>
    Over.OverMorphism.ext (hp.1.hom_ext h (by rw [Over.w x, Over.w y]))
  have lift : ∀ x₀ : Over.mk (FU.u i Pe) ⟶ Xo.univ.t.G, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x.left ≫ φ = x₀.left := fun x₀ =>
    ⟨Over.homMk (hp.1.lift x₀.left (𝟙 _) ((Over.w x₀).trans (Category.id_comp _).symm)) (hp.1.lift_snd _ _ _),
      hp.1.lift_fst _ _ _⟩
  choose Φ hΦ using lift
  have Φmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y => inj _ _ (by
    rw [hΦ, ← hp.2 _ (Φ x) (Φ y) (pushPt hp.1.w (Φ x)) (pushPt hp.1.w (Φ y)) rfl rfl]
    exact mul_left_congr (Category.id_comp _).symm _ _ _ _ (hΦ x).symm (hΦ y).symm)
  have Φinj : Function.Injective Φ := fun x y h => Over.OverMorphism.ext (by rw [← hΦ, ← hΦ, h])
  have Φsurj : Function.Surjective Φ := fun x =>
    ⟨Over.homMk (x.left ≫ φ) ((Over.w (pushPt hp.1.w x)).trans (Category.id_comp _)), inj _ _ (hΦ _)⟩
  have Φone : Φ 1 = 1 := by
    have := Φmul 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have holG : IsHolTo (Set.univ : Set (Fin g₀ → ℂ)) (fun z => (FU.ex i Pe z).left) := by
    have h := (FU.hol i 0 Set.univ (fun _ => Pe) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
    exact isHolTo_slice h 0
  have hol : IsHolTo (Set.univ : Set (Fin g₀ → ℂ)) (fun z => (Φ (FU.ex i Pe z)).left) :=
    isHolTo_of_isPullback hp.1 (e := fun z => (Φ (FU.ex i Pe z)).left) (fun z => Over.w (Φ (FU.ex i Pe z)))
      (by simpa only [hΦ] using holG)
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L g g₀ u ht₁ ht₂ (fun z => Φ (FU.ex i Pe z))
    (fun z z' => by rw [FU.ex_add i Pe hP, Φmul]) hol
  have hΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ Pe.range := fun z => by
    rw [← u.ker, hF, ← FU.ex_ker i Pe hP, ← Φone, Φinj.eq_iff]
  have cΛ : (u.Λ : Set (Fin g → ℂ)).Countable := by
    have := u.discrete
    exact (countable_of_Lindelof_of_discrete : Countable u.Λ)
  have cP : (Pe.range : Set (Fin g₀ → ℂ)).Countable := by
    have := hP.2.2.1
    exact (countable_of_Lindelof_of_discrete : Countable Pe.range)
  have Finj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun z hz =>
    eq_zero_of_smul_mem_countable cP fun t => (hΛ _).1 (by rw [map_smul, hz, smul_zero]; exact u.Λ.zero_mem)
  have Fsurj : Function.Surjective F := surjective_of_countable F cΛ fun v => by
    obtain ⟨x₀, hx₀⟩ := Φsurj (u.ex v)
    obtain ⟨z, rfl⟩ := FU.ex_onto i Pe hP x₀
    refine ⟨z, (u.ker _).1 ?_⟩
    have := u.ex_add (v - F z) (F z)
    rw [sub_add_cancel, hF, hx₀] at this
    exact right_eq_mul.1 this
  have hex : ∀ z, (u.ex (F z)).left ≫ φ = (FU.ex i Pe z).left := fun z => by rw [hF, hΦ]
  let F' := LinearEquiv.ofBijective F ⟨Finj, Fsurj⟩
  have fwd : ∀ (w : Fin g₀ → ℂ) (v : epsR ℂ ⟶ P.A), IsTangent v → u.IsDiff (F' w) v →
      IsDerivAt0 (fun z => (FU.ex i Pe z).left) w ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ) := fun w v hv hd => by
    have h1 := isDerivAt0_of_isDiff u φ (e := fun z => (FU.ex i Pe (F'.symm.toLinearMap z)).left)
      (fun z => by rw [← hex]; exact congrArg (fun t => (u.ex t).left ≫ φ) (F'.apply_symm_apply z).symm) hv hd
    have h2 := (isDerivAt0_comp_linear _ holG F'.symm.toLinearMap _ _).1 h1
    rwa [LinearEquiv.coe_coe, F'.symm_apply_apply] at h2
  refine ⟨F', hex, hΛ, fun a b => ?_, fun w v hv => ⟨fwd w v hv, fun hd => ?_⟩⟩
  · let a' : u.Λ := ⟨F (Pe a), (hΛ _).2 ⟨a, rfl⟩⟩
    let b' : u.Λ := ⟨F (Pe b), (hΛ _).2 ⟨b, rfl⟩⟩
    refine (hEf a' b').symm.trans (congrArg _ (int_eq_of_exp_eq fun k hk => ?_))
    have h₁ := hweil k a' b' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have h₂ := FU.ex_weil i Pe hP k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
    have h₃ := weil_eq_of_grpPullback hp Xo.univ.t.PP.isLB P.isLB w hw (Z := Sp ℂ) (t := FU.u i Pe) (t' := 𝟙 _)
      (Category.id_comp _).symm k (u.ex ((k : ℂ)⁻¹ • F (Pe a))) (u.ex ((k : ℂ)⁻¹ • F (Pe b))) _ _
      (by rw [← hex, map_smul]) (by rw [← hex, map_smul]) _ _ h₁ h₂
    exact congrArg Units.val (unitOn_injective h₃)
  · obtain ⟨w', hw', -⟩ := ht₁ v hv
    obtain ⟨w₁, rfl⟩ := F'.surjective w'
    have h1 := fwd w₁ v hv hw'
    let a : epsPt (FU.u i Pe) ⟶ Xo.univ.t.G := Over.homMk ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ)
      (by rw [Category.assoc, hp.1.w, ← Category.assoc]; exact congrArg (· ≫ FU.u i Pe) (Over.w v))
    have e : w = w₁ := ((FU.ex_diff i Pe hP).2 a hd.1).unique hd h1
    rwa [e]

theorem exists_equiv_of_isAH : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ' : KA l →+* ℂ) (g₀ : ℕ) (ty : Fin g₀ → (E →+* ℂ)) (Fu : FamilyUnif Xo σ' ty) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g₀ → ℂ)) (y₀ : Sp ℂ ⟶ Xo.X) (s' : Sp ℂ ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s') (m : ObjMap o Xo.univ y₀) (g : ℕ) (u : HolUnif o.t.G o.t.PP.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (κ : u.Λ → ℂ), IsPeriod (Fu.Di i) ty P → y₀ = Fu.u i P → u.IsAH Hm κ → ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ z, (u.ex (h z)).left ≫ m.toSABMap.φ = (Fu.ex i P z).left) ∧ (∀ z, h z ∈ u.Λ ↔ z ∈ P.range) ∧ (∀ a b, (herm Hm (h (P a)) (h (P b))).im = (Fu.Di i).EF a b) ∧ ∀ (w : Fin g₀ → ℂ) (v : epsR ℂ ⟶ o.t.G), IsTangent v → (u.IsDiff (h w) v ↔ IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v.left ≫ m.toSABMap.φ)) := by
  intro E _ _ _ H D l Xo σ' g₀ ty Fu i P y₀ s' o m g u Hm κ hP hy hAH
  subst hy
  obtain ⟨w, hw, -⟩ := m.lin
  exact exists_equiv_of_polAV Fu i hP (GlobalTheory.Obj.toPolAV o) m.toSABMap.φ m.cart ⟨w, hw⟩ u hAH

end GlobalTheory.DetLine.FibreCmp
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem ideal_le_on_basicOpen {X : Scheme.{0}} (a a' : X.IdealSheafData) (U : X.affineOpens)
    (g : Γ(X, U)) (h : ∀ s ∈ a.ideal U, g * s ∈ a'.ideal U) :
    a.ideal (X.affineBasicOpen g) ≤ a'.ideal (X.affineBasicOpen g) := by
  have hu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g) :=
    X.toRingedSpace.isUnit_res_basicOpen g
  have key : (a.ideal U).map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom ≤
      (a'.ideal U).map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom := by
    refine Ideal.map_le_iff_le_comap.2 fun s hs => ?_
    rw [Ideal.mem_comap]
    refine (Ideal.unit_mul_mem_iff_mem _ hu).1 ?_
    rw [← map_mul]
    exact Ideal.mem_map_of_mem _ (h s hs)
  rw [← a.map_ideal_basicOpen, ← a'.map_ideal_basicOpen]
  exact key

theorem exists_affineOpen_mem {X : Scheme.{0}} (x : X) : ∃ U : X.affineOpens, x ∈ U.1 :=
  TopologicalSpace.Opens.mem_iSup.1 ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))

theorem le_of_le_reductions : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ →
    ∀ (V : Scheme.{0}) [IsLocallyNoetherian V] (p : V ⟶ Spec (CommRingCat.of R))
    (a a' : V.IdealSheafData), UniversallyClosed (a'.subschemeι ≫ p) →
    (∀ e : ℕ, a ≤ a' ⊔ baseIdeal p (I ^ (e + 1))) → a ≤ a' := by
  intro R _ I hI V _ p a a' hUC hle
  let S := {U : V.affineOpens // a.ideal U ≤ a'.ideal U}
  have h1 : ∀ x : V, x ∉ a'.support → ∃ U : S, x ∈ U.1.1 := by
    intro x hx
    obtain ⟨U, hU⟩ := exists_affineOpen_mem x
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hU, Scheme.mem_zeroLocus_iff] at hx
    push_neg at hx
    obtain ⟨f, hf, hxf⟩ := hx
    exact ⟨⟨V.affineBasicOpen f, ideal_le_on_basicOpen a a' U f fun s _ => Ideal.mul_mem_right _ _ hf⟩, hxf⟩
  have h2 : ∀ x : V, I ≤ (p x).asIdeal → ∃ U : S, x ∈ U.1.1 := by
    intro x hx
    obtain ⟨U, hU⟩ := exists_affineOpen_mem x
    haveI : IsNoetherianRing Γ(V, U) := IsLocallyNoetherian.component_noetherian U
    obtain ⟨r, hr, hr'⟩ := GlobalTheory.T.krull_intersection_ideal_local_form Γ(V, U) (I.map (cst p U.1)) (a.ideal U) (a'.ideal U)
      (fun e => by
        have := hle e U
        rwa [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, baseIdeal_ideal, Ideal.map_pow] at this)
    refine ⟨⟨V.affineBasicOpen (1 - r), ideal_le_on_basicOpen a a' U _ hr'⟩, ?_⟩
    have hsupp : x ∈ (baseIdeal p I).support := (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.2.2 R V p I x).2 hx
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hU, baseIdeal_ideal, Scheme.mem_zeroLocus_iff]
      at hsupp
    have hxr := hsupp r hr
    show x ∈ V.basicOpen (1 - r)
    rw [Scheme.mem_basicOpen _ _ _ hU] at hxr ⊢
    rw [map_sub, map_one]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hxr
  let O : V.Opens := ⨆ U : S, U.1.1
  have hZ := GlobalTheory.T.eq_empty_of_isClosed_of_universallyClosed_of_le_jacobson R I hI a'.subscheme (a'.subschemeι ≫ p) hUC
    (a'.subschemeι ⁻¹' (O : Set V)ᶜ) (O.isOpen.isClosed_compl.preimage a'.subschemeι.continuous)
    (fun z hz hIz => hz (by
      obtain ⟨U, hU⟩ := h2 (a'.subschemeι z) (by simpa using hIz)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩))
  have hO : O = ⊤ := by
    rw [eq_top_iff]
    intro x _
    by_contra hxO
    by_cases hx : x ∈ a'.support
    · have hx' : x ∈ Set.range a'.subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι]; exact hx
      obtain ⟨z, rfl⟩ := hx'
      have : z ∈ (∅ : Set a'.subscheme) := hZ ▸ hxO
      exact this
    · obtain ⟨U, hU⟩ := h1 x hx
      exact hxO (TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩)
  exact Scheme.IdealSheafData.le_of_iSup_eq_top (fun U : S => U.1) hO (fun U => U.2)

end GlobalTheory.FormalAlg
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem isClosedImmersion_subschemeι_comp {R : Type} [CommRing R] {W W' : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) [IsSeparated f] [IsImmersion π]
    (T : W'.IdealSheafData) [IsProper (T.subschemeι ≫ π ≫ f)] :
    IsClosedImmersion (T.subschemeι ≫ π) := by
  haveI : IsProper ((T.subschemeι ≫ π) ≫ f) := by rw [Category.assoc]; infer_instance
  haveI : IsProper (T.subschemeι ≫ π) := IsProper.of_comp _ f
  exact IsClosedImmersion.of_isPreimmersion _ (T.subschemeι ≫ π).isClosedMap.isClosed_range

theorem isProper_ker_subschemeι_comp {X Y S : Scheme.{0}} (g : X ⟶ Y) [IsClosedImmersion g]
    (f : Y ⟶ S) [IsProper (g ≫ f)] : IsProper (g.ker.subschemeι ≫ f) := by
  change IsProper (g.imageι ≫ f)
  have hg : g.imageι = inv g.toImage ≫ g := (IsIso.eq_inv_comp _).2 g.toImage_imageι
  rw [hg, Category.assoc]
  infer_instance

theorem mapSystem : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W), IsSeparated f → IsImmersion π →
    ∀ t : ℕ → W'.IdealSheafData, IsSystem (π ≫ f) I t → (∀ e, IsProper ((t e).subschemeι ≫ π ≫ f)) →
    IsSystem f I (fun e => (t e).map π) ∧ (∀ e, IsProper (((t e).map π).subschemeι ≫ f)) ∧
      ∀ e, ((t e).map π).comap π = t e := by
  intro R _ I W W' f π hf hπ t ht hp
  have hci : ∀ e, IsClosedImmersion ((t e).subschemeι ≫ π) := fun e =>
    haveI := hp e; isClosedImmersion_subschemeι_comp f π (t e)
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  ·
    show (t e).map π = (t (e + 1)).map π ⊔ baseIdeal f (I ^ (e + 1))
    have hle : t (e + 1) ≤ t e := by rw [ht e]; exact le_sup_left
    have hι : IsClosedImmersion (t (e + 1)).subschemeι := inferInstance
    have h1 : ((t e).comap (t (e + 1)).subschemeι).map (t (e + 1)).subschemeι = t e := by
      have := (GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion _ _ _ hι ⊥ (t e)).1
      rw [bot_sup_eq, Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι,
        sup_eq_right.2 hle] at this
      exact this
    have hbot : (t (e + 1)).comap (t (e + 1)).subschemeι = ⊥ := by
      have := (GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion _ _ _ hι ⊥ ⊥).2
      rwa [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι] at this
    have h2 : (t e).comap (t (e + 1)).subschemeι =
        (baseIdeal f (I ^ (e + 1))).comap ((t (e + 1)).subschemeι ≫ π) := by
      conv_lhs => rw [ht e]
      rw [Scheme.IdealSheafData.comap_sup, hbot, bot_sup_eq, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1,
        Category.assoc]
    have h3 := (GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion _ _ _ (hci (e + 1)) ⊥ (baseIdeal f (I ^ (e + 1)))).1
    rw [bot_sup_eq, Scheme.IdealSheafData.map_bot] at h3
    calc (t e).map π = (((t e).comap (t (e + 1)).subschemeι).map (t (e + 1)).subschemeι).map π := by
          rw [h1]
      _ = ((t e).comap (t (e + 1)).subschemeι).map ((t (e + 1)).subschemeι ≫ π) := by
          rw [Scheme.IdealSheafData.map_comp]
      _ = ((t (e + 1)).subschemeι ≫ π).ker ⊔ baseIdeal f (I ^ (e + 1)) := by rw [h2, h3]
      _ = (t (e + 1)).map π ⊔ baseIdeal f (I ^ (e + 1)) := rfl
  ·
    haveI := hci e
    haveI : IsProper (((t e).subschemeι ≫ π) ≫ f) := by rw [Category.assoc]; exact hp e
    exact isProper_ker_subschemeι_comp ((t e).subschemeι ≫ π) f
  ·
    haveI := hci e
    refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
    show t e ≤ (((t e).subschemeι ≫ π).ker).comap π
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    have h : pullback.fst π ((t e).subschemeι ≫ π) = pullback.snd _ _ ≫ (t e).subschemeι := by
      rw [← cancel_mono π, pullback.condition, Category.assoc]
    rw [h]
    conv_lhs => rw [← (t e).ker_subschemeι]
    exact Scheme.Hom.le_ker_comp _ _

end GlobalTheory.FormalAlg
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ReadCont

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem pow_succ_mem_secZ {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e) (m : ℕ) :
    g ^ (m + 1) ∈ secZ Xo c ((m + 1) • e) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_secZ ih hg

theorem differentiableOn_rdU_of_antitone {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} (hU : IsUnf U)
    (hpq : 1 ≤ Dw.p + Dw.q) {e : Ix Dw → ℤ} (he0 : e none = 0)
    (hanti : ∀ τ (i j : Fin (Dw.mult τ)), i ≤ j → e (some ⟨τ, j⟩) ≤ e (some ⟨τ, i⟩))
    {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (k : U.Comp) : DifferentiableOn ℂ (rdU U f k) (U.X k).dom := by
  intro x hx
  have ho : IsOpen (U.X k).dom := FourierCoefficientDomain.isOpen_dom _
  obtain ⟨n, hn, g, hg, hg0⟩ := GlobalTheory.TrueCx.FlatConst.exists_sec_four hpq (U.un k ⟨x, hx⟩)
  set M : ℕ := ∑ i : Ix Dw, (e i).natAbs with hMdef
  have hM : ∀ i, -(4 * ((M + 1 : ℕ) : ℤ)) ≤ e i := fun i => by
    have h1 : (e i).natAbs ≤ M := Finset.single_le_sum (f := fun i => (e i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
    have h2 : -((e i).natAbs : ℤ) ≤ e i := by
      have := Int.natAbs_abs (e i); rw [← Int.abs_eq_natAbs]; exact neg_abs_le _
    have h3 : ((e i).natAbs : ℤ) ≤ M := by exact_mod_cast h1
    push_cast; linarith
  let a : (E →+* ℂ) × ℕ → ℕ := fun p =>
    if h : p.2 < Dw.mult p.1 then (4 * ((M + 1 : ℕ) : ℤ) + e (some ⟨p.1, ⟨p.2, h⟩⟩)).toNat else 0
  have hdom : Dom a ((M + 1) * n) := by
    refine ⟨fun τ i j hij => ?_, hn.mul_left _⟩
    show a (τ, j) ≤ a (τ, i)
    simp only [a]
    by_cases hj : j < Dw.mult τ
    · have hi : i < Dw.mult τ := lt_of_le_of_lt hij hj
      rw [dif_pos hj, dif_pos hi]
      exact Int.toNat_le_toNat (by linarith [hanti τ ⟨i, hi⟩ ⟨j, hj⟩ hij])
    · rw [dite_eq_right hj]; exact Nat.zero_le _
  have hgp := pow_succ_mem_secZ (Xo := Xo) (c := c) (by rw [secZ_nat]; exact hg) M
  have hgf : g ^ (M + 1) * f ∈ sec Xo c a ((M + 1) * n) := by
    rw [← secZ_nat]
    convert mul_mem_secZ hgp hf using 2
    funext i
    rcases i with _ | ⟨τ, i⟩
    · simp [ex, he0]
    · have hi := i.2
      rw [Pi.add_apply, Pi.smul_apply]
      simp only [ex, a, dif_pos hi, nsmul_eq_mul]
      rw [Int.toNat_of_nonneg (by linarith [hM (some ⟨τ, i⟩)])]
      push_cast
      ring
  have d1 := (hU.2.2.2.2.1 _ n ⟨fun _ _ _ _ => le_rfl, hn⟩ g hg k).1
  have d2 := (hU.2.2.2.2.1 _ _ hdom _ hgf k).1
  have hx0 : rdU U g k x ≠ 0 := by
    have : rdU U g k x = toC (evR Xo c g (U.un k ⟨x, hx⟩)) := dif_pos hx
    rwa [this]
  have a1 := d1.differentiableAt (ho.mem_nhds hx)
  have a2 := d2.differentiableAt (ho.mem_nhds hx)
  refine ((a2.mul ((a1.pow (M + 1)).inv (pow_ne_zero _ hx0))).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [a1.continuousAt.eventually_ne hx0] with y hy0
  have e1 : rdU U (g ^ (M + 1) * f) k y = rdU U g k y ^ (M + 1) * rdU U f k y := by
    rw [_root_.GlobalTheory.AllWt.rdU_mul]
    have : ∀ m : ℕ, rdU U (g ^ (m + 1)) = rdU U g ^ (m + 1) := fun m => by
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ g (m + 1), _root_.GlobalTheory.AllWt.rdU_mul, ih, ← pow_succ]
    rw [this]; rfl
  rw [Pi.mul_apply, Pi.inv_apply, e1, Pi.pow_apply, mul_right_comm, mul_inv_cancel₀ (pow_ne_zero _ hy0), one_mul]

end GlobalTheory.ReadCont

namespace GlobalTheory.ReadCont

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem continuousOn_rdU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (e : Ix Dw → ℤ), e none = 0 → ∀ s ∈ secZ Xo c e, ∀ σ, GoodEmb c σ → ∀ k, ContinuousOn (rdU (U σ) s k) ((U σ).X k).dom := by
  intro E _ _ _ H Dw l Xo c r U x hL e he0 s hs σ hσ k
  by_cases hanti : ∀ τ (i j : Fin (Dw.mult τ)), i ≤ j → e (some ⟨τ, j⟩) ≤ e (some ⟨τ, i⟩)
  · exact (differentiableOn_rdU_of_antitone (hL.unf σ hσ) hL.pos he0 hanti hs k).continuousOn
  · push_neg at hanti
    obtain ⟨τ, i, j, hij, hlt⟩ := hanti
    have hij' : i < j := lt_of_le_of_ne hij (by rintro rfl; exact lt_irrefl _ hlt)
    rw [GlobalTheory.T.integerExponentSection_eq_zero_of_increasing_flag E H Dw l Xo c e τ i j hij' hlt s hs, map_zero]
    exact continuousOn_const

end GlobalTheory.ReadCont
end
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem _root_.GlobalTheory.T.exists_eigenChart_affineOpen_within : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (M : GChart Y) (x : Y.X), x ∈ M.U → ∀ W : Y.X.Opens, x ∈ W → ∃ k : ECh Y p, k.M = M ∧ x ∈ k.V ∧ IsAffineOpen k.V ∧ k.V ≤ W := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.exists_eCh_le | exact GlobalTheory.FlagMod.FieldFlag.exists_eCh_le | (intros; apply GlobalTheory.FlagMod.FieldFlag.exists_eCh_le <;> assumption)
end
