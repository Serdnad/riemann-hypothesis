module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle037
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHalfChar
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle055
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerClassCohomologousAlongEndomorphism
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfHermFormPos
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle116
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.isAffineOpen_nonzeroLocus_of_fibrewise_ample : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (M : LB X) (d : ℕ) (m : ℕ) (u : Fin (m + 1) → LB.Sec (pw M d)), 1 ≤ d → IsProper f → M.IsLB → (⨆ i, Out.nonzeroLocus (u i) = ⊤) → (∀ q : Ideal R, q.IsPrime → ∃ (k : Type) (_ : Field k) (β : R →+* k), RingHom.ker β = q ∧ Out.RelAmple (Over.mk (pullback.snd f (spMap β))) (M.pull (pullback.fst f (spMap β)))) → ∀ i, IsAffineOpen (Out.nonzeroLocus (u i)) := by
  first | exact @GlobalTheory.FibreAmple.isAffineOpen_nonzeroLocus_of_fibres | exact GlobalTheory.FibreAmple.isAffineOpen_nonzeroLocus_of_fibres | (intros; apply GlobalTheory.FibreAmple.isAffineOpen_nonzeroLocus_of_fibres <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.ExCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]; rfl

theorem weilIs_iff {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (s' : Sp ℂ ⟶ S') (s : Sp ℂ ⟶ S) (hs : s = s' ≫ f) (k : ℤ) (x y : Over.mk s' ⟶ t'.G) (x₀ y₀ : Over.mk s ⟶ t.G)
    (c : ℂˣ) (hx : x₀.left = x.left ≫ m.φ) (hy : y₀.left = y.left ≫ m.φ) :
    Out.WeilIs t'.G t'.PP.L k x y (unitOn c) ↔ Out.WeilIs t.G t.PP.L k x₀ y₀ (unitOn c) := by
  subst hs
  have hL : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  exact weilIs_grpPullback_of_comm _ _ _ _ _ m.φ _ _ t.PP.isLB t'.PP.isLB m.cart hL (Over.mk s') k x y x₀ y₀ _ hx hy

theorem exists_isExp_of_family {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ₀ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ₀ ty) (i : Fin FU.n) {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (FU.Di i) ty Pe) {R K : Type} [CommRing R] [Field K] (f : R →+* K) (σ : K →+* ℂ)
    (B : PAT H (Sp R)) {y : Sp K ⟶ Xo.X} {t : SAB H (Sp K)} (m : SABMap t Xo.univ.t y) (n : SABMap t B.t (spMap f))
    (hy : spMap σ ≫ y = FU.u i Pe) :
    ∃ eB : (Fin g → ℂ) → (Over.mk (spMap (σ.comp f)) ⟶ B.t.G), IsExp B (σ.comp f) (FU.Di i) ty Pe eB ∧
      ∀ z, ∃ x : Sp ℂ ⟶ t.G.left, x ≫ t.G.hom = spMap σ ∧ x ≫ n.φ = (eB z).left ∧ x ≫ m.φ = (FU.ex i Pe z).left := by
  obtain ⟨p, hp⟩ := LiePull.exists_pushEquiv m.cart (Over.mk (spMap σ)) (FU.u i Pe) hy.symm
  obtain ⟨q, hq⟩ := LiePull.exists_pushEquiv n.cart (Over.mk (spMap σ)) (spMap (σ.comp f)) (spMap_comp f σ).symm
  have hp' : ∀ z, (p.symm (FU.ex i Pe z)).left ≫ m.φ = (FU.ex i Pe z).left := fun z => by
    rw [← hp, p.apply_symm_apply]
  refine ⟨fun z => q (p.symm (FU.ex i Pe z)), ⟨hP, ?_, fun z w => ?_,
    q.surjective.comp (p.symm.surjective.comp (FU.ex_onto i Pe hP)), fun z => ?_, fun a z => ?_,
    fun k a b c hk hc => ?_⟩, fun z => ⟨(p.symm (FU.ex i Pe z)).left, Over.w _, (hq _).symm, hp' z⟩⟩
  · have hpb := (IsPullback.of_hasPullback t.G.hom (spMap σ)).paste_horiz m.cart.1
    let c : (Fin g → ℂ) → (Sp ℂ ⟶ pullback t.G.hom (spMap σ)) := fun z =>
      pullback.lift (p.symm (FU.ex i Pe z)).left (𝟙 _) ((Over.w _).trans (Category.id_comp _).symm)
    have hc := ThetaPoint.isHolTo_fibre hpb c (fun z => pullback.lift_snd _ _ _) (by
      have e : (fun z => c z ≫ pullback.fst t.G.hom (spMap σ) ≫ m.cm.F) = fun z => (FU.ex i Pe z).left :=
        funext fun z => by rw [← Category.assoc, pullback.lift_fst]; exact hp' z
      rw [e]
      exact ExpUniqFamily.isHolTo_ex FU i Pe hP)
    have e : (fun z => (q (p.symm (FU.ex i Pe z))).left) = fun z => c z ≫ pullback.fst t.G.hom (spMap σ) ≫ n.φ :=
      funext fun z => by rw [← Category.assoc, pullback.lift_fst]; exact hq _
    rw [e]
    exact isHolTo_comp_hom hc _
  · beta_reduce
    rw [FU.ex_add i Pe hP, map_mul, map_mul]
  · exact (map_eq_one_iff q q.injective).trans ((map_eq_one_iff _ p.symm.injective).trans (FU.ex_ker i Pe hP z))
  · have e : p.symm (FU.ex i Pe z ≫ Xo.univ.t.act.act a) = p.symm (FU.ex i Pe z) ≫ t.act.act a := by
      rw [p.symm_apply_eq]
      apply Over.OverMorphism.ext
      rw [hp, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc]
      exact congrArg (· ≫ _) (hp' z).symm
    apply Over.OverMorphism.ext
    beta_reduce
    rw [FU.ex_lin i Pe hP, e, Over.comp_left, hq, hq, Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg _ (n.act a)
  · exact (weilIs_iff n _ _ (spMap_comp f σ).symm k _ _ _ _ c (hq _) (hq _)).1
      ((weilIs_iff m _ _ hy.symm k _ _ _ _ c (hp' _).symm (hp' _).symm).2 (FU.ex_weil i Pe hP k a b c hk hc))

section Comparison₂

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n} {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
  {hP : IsPeriod (FU.Di i) ty Pe}

end Comparison₂

section CMStatement

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n} {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
  {hP : IsPeriod (FU.Di i) ty Pe}

end CMStatement

section Tensor

end Tensor

section TensorStatement

variable {M : Type} [Field M] [NumberField M] {ω : 𝓞 M}

end TensorStatement

end GlobalTheory.CM.ExCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_thetaLevelAbelianScheme_glue_openCover : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (I : Type) (U : I → S.Opens) (t : ∀ i, TObj g k J b ((U i).ι ≫ s)), iSup U = ⊤ → (∀ i j, ∃ u : TObj g k J b ((U i ⊓ U j).ι ≫ s), TMap u (t i) (S.homOfLE inf_le_left) ∧ TMap u (t j) (S.homOfLE inf_le_right)) → (∀ (T : Scheme.{0}) (i : I) (f : T ⟶ (U i).toScheme) (u : TObj g k J b (f ≫ (U i).ι ≫ s)) (φ φ' : u.A.left ⟶ (t i).A.left), IsOpenImmersion f → IsGrpPullback u.A (t i).A f φ → IsGrpPullback u.A (t i).A f φ' → LBIso u.L ((t i).L.pull φ) → LBIso u.L ((t i).L.pull φ') → (∀ a, (u.pt a).left ≫ φ = (u.pt a).left ≫ φ') → φ = φ') → ∃ t₀ : TObj g k J b s, ∀ i, TMap (t i) t₀ (U i).ι := by
  first | exact @GlobalTheory.exists_tobj_of_cover | exact GlobalTheory.exists_tobj_of_cover | (intros; apply GlobalTheory.exists_tobj_of_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.kodairaSpencerClass_cohomologous_along_endomorphism : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D : R → K) d θ (f : X ⟶ X) (f₀ : A₀ ⟶ A₀) (F : Matrix (Fin g) (Fin g) K), KSCoc A₀.hom p m D W dd d θ → IsMonHom f₀ → f ≫ p = p → f₀.left ≫ m = m ≫ f → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → ∀ x, Cohom f₀.left _ (lc A₀.hom (F x) θ) (θ x) := by
  first | exact @GlobalTheory.KS.cohom_ksCoc_of_endomorphism | exact GlobalTheory.KS.cohom_ksCoc_of_endomorphism | (intros; apply GlobalTheory.KS.cohom_ksCoc_of_endomorphism <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

theorem map_sum_nsmul_eq_listProd {V G : Type} [AddCommGroup V] [Group G] (E : V → G)
    (hE : ∀ z w, E (z + w) = E z * E w) : ∀ (n : ℕ) (a : Fin n → ℕ) (z : Fin n → V),
    E (∑ i, a i • z i) = (List.ofFn fun i => E (z i) ^ a i).prod := by
  have h0 : E 0 = 1 := by
    have := hE 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hp : ∀ (m : ℕ) (x : V), E (m • x) = E x ^ m := by
    intro m x
    induction m with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ m ih => rw [succ_nsmul, hE, ih, pow_succ]
  intro n
  induction n with
  | zero => intro a z; simp [h0]
  | succ n ih =>
    intro a z
    rw [Fin.sum_univ_succ, hE, List.ofFn_succ, List.prod_cons, hp, ih]

theorem linearMap_eq_of_span_real {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z ∈ s, F z = F' z) : F = F' := by
  have : F.restrictScalars ℝ = F'.restrictScalars ℝ := LinearMap.ext_on hs h
  exact LinearMap.restrictScalars_injective ℝ this

theorem level_comb_sub_mem {g n k : ℕ} (hk : (k : ℂ) ≠ 0) {La : Type} [AddCommGroup La] (Q : La →+ (Fin g → ℂ))
    (lam : Fin n → La) (m : Fin n → ℤ) (y : La) :
    ∃ x, (k : ℂ)⁻¹ • Q (∑ i, m i • lam i + k • y) =
      ∑ i, ((m i : ZMod k)).val • ((k : ℂ)⁻¹ • Q (lam i)) + Q x := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  haveI : NeZero k := ⟨hk0⟩
  refine ⟨∑ i, (m i / k) • lam i + y, ?_⟩

  rw [map_add (f := _), map_add (f := _), map_sum, map_sum, map_nsmul, smul_add, Finset.smul_sum, ← add_assoc,
  ← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (((m i : ZMod k).val : ℤ) : ℂ) = ((m i % k : ℤ) : ℂ) := by rw [ZMod.val_intCast]
    have h2 : ((m i : ℤ) : ℂ) = ((m i % k : ℤ) : ℂ) + (k : ℂ) * ((m i / k : ℤ) : ℂ) := by
      exact_mod_cast (Int.emod_add_mul_ediv (m i) k).symm
    rw [map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, smul_smul, ← add_smul]
    congr 1
    rw [Int.cast_natCast] at h1
    rw [h1]
    conv_lhs => rw [h2]
    field_simp
  · rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk]

theorem shape_of_uniformised : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ), (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → (∀ j i, ∃ y, ac j (lam i) = ∑ i', Mat j i' i • lam i' + k • y) → (∀ j, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j x)) ∧ ∀ y, y ≠ 0 → (hermForm Hm (F y) (F y)).re < κ * (hermForm Hm y y).re) → t.Shape Mat κ := by
  intro hL hL2 _ hU o _ g k J b em w w' t La _ EF lam ac Q Hm Mat κ ⟨u, χ', hAH, hΛ, _, hpt, hact⟩ hMat hB j
  obtain ⟨F, hFQ, hF⟩ := hact j
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hMat j i
    let E : (Fin g → ℂ) → (Out.baseOver (Sp ℂ) ⟶ t.A) := u.ex
    have hE : ∀ z w, E (z + w) = E z * E w := u.ex_add
    have hpt' : ∀ i₀, t.pt i₀ = E ((k : ℂ)⁻¹ • Q (lam i₀)) := fun i₀ => Over.OverMorphism.ext (hpt i₀)
    have hF' : ∀ z, E (F z) = E z ≫ t.act j := hF
    obtain ⟨x, hx⟩ := level_comb_sub_mem hk Q lam (fun i' => Mat j i' i) y
    have h1 : E (Q x) = 1 := (u.ker _).2 ((hΛ _).2 ⟨x, rfl⟩)
    rw [hpt', ← hF', map_smul, hFQ, hy, hx, hE, h1, _root_.mul_one, map_sum_nsmul_eq_listProd E hE]
    simp only [TObj.lab, Out.linComb, hpt']
  · obtain ⟨F', hFQ', hF'⟩ := hB j
    have hFF : F' = F := linearMap_eq_of_span_real _ u.full _ _ fun z hz => by
      obtain ⟨x, rfl⟩ := (hΛ z).1 hz
      rw [hFQ, hFQ']
    subst hFF
    exact GlobalTheory.relAmple_of_hermForm_pos hL hL2 hU t.pol u Hm χ' (t.act j) F' κ hAH (t.hom j) hF hF'

end GlobalTheory.ZM
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.thetaConstants_unique_up_to_unit : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v v' : Ix g (N' ^ 2) → R), t.HasTh x v → t.HasTh x v' → Ideal.span (Set.range v) = ⊤ → ∃ u : Rˣ, ∀ a, v' a = u * v a := by
  first | exact @GlobalTheory.hasTh_unique_unit | exact GlobalTheory.hasTh_unique_unit | (intros; apply GlobalTheory.hasTh_unique_unit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.thetaCosetNonvanishing_of_hasTh : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (n : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R) (q : Ideal R), 2 ≤ n → n ∣ N' → t.HasTh x v → q.IsPrime → Coset n N' v q := by
  first | exact @GlobalTheory.coset_of_hasTh | exact GlobalTheory.coset_of_hasTh | (intros; apply GlobalTheory.coset_of_hasTh <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.JoinModels

theorem isNormalScheme_of_flat_preimmersion {U X : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U := by
  intro x
  obtain ⟨h1, h2⟩ := h (j x)
  have hf : (j.stalkMap x).hom.Flat := Flat.stalkMap j x
  have hs : Function.Surjective (j.stalkMap x).hom := j.stalkMap_surjective x
  have hi : Function.Injective (j.stalkMap x).hom := by
    letI := (j.stalkMap x).hom.toAlgebra
    have : Module.Flat (X.presheaf.stalk (j x)) (U.presheaf.stalk x) := hf
    have : IsLocalHom (algebraMap (X.presheaf.stalk (j x)) (U.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (j.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (j x))
      (B := U.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j x)) (U.presheaf.stalk x)
  let e := RingEquiv.ofBijective (j.stalkMap x).hom ⟨hi, hs⟩
  have h3 : IsDomain (U.presheaf.stalk x) := e.symm.toMulEquiv.isDomain _
  exact ⟨h3, IsIntegrallyClosed.of_equiv e⟩

theorem isPullback_toImage_comp {U P Z : Scheme.{0}} (j : U ⟶ P) (q : P ⟶ Z) (v : U ⟶ Z)
    (h : j ≫ q = v) [QuasiCompact j] [IsSeparated q] [Flat v] [Mono v] :
    IsPullback (𝟙 U) j.toImage v (j.imageι ≫ q) := by
  have Hu := IsPullback.of_hasPullback v q
  have : Mono (pullback.snd v q) := inferInstance
  let c : U ⟶ pullback v q := pullback.lift (𝟙 U) j (by simpa using h.symm)
  have hc₁ : c ≫ pullback.fst _ _ = 𝟙 U := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd _ _ = j := pullback.lift_snd _ _ _
  have : IsClosedImmersion (c ≫ pullback.fst _ _) := by rw [hc₁]; infer_instance
  have : IsClosedImmersion c := .of_comp c (pullback.fst _ _)
  have H := (GlobalTheory.isPullback_toImage_of_isClosedImmersion j c _ hc₂).paste_horiz Hu
  rwa [hc₁] at H

theorem exists_common_projective {O : Type} [CommRing O] {U : Scheme.{0}} (σ : U ⟶ Sp O) {I : Type}
    [Finite I] [Nonempty I] (X : I → Scheme.{0}) (s : ∀ i, X i ⟶ Sp O) (hs : ∀ i, IsProjOver (s i))
    (u : ∀ i, U ⟶ X i) (hu : ∀ i, u i ≫ s i = σ) :
    ∃ (P : Scheme.{0}) (r : P ⟶ Sp O) (j : U ⟶ P) (p : ∀ i, P ⟶ X i), IsProjOver r ∧ j ≫ r = σ ∧
      ∀ i, p i ≫ s i = r ∧ j ≫ p i = u i := by
  classical
  have key : ∀ S : Finset I, ∃ (P : Scheme.{0}) (r : P ⟶ Sp O) (j : U ⟶ P), IsProjOver r ∧ j ≫ r = σ ∧
      ∀ i ∈ S, ∃ p : P ⟶ X i, p ≫ s i = r ∧ j ≫ p = u i := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      obtain ⟨i⟩ := ‹Nonempty I›
      exact ⟨X i, s i, u i, hs i, hu i, by simp⟩
    | insert k S _ ih =>
      obtain ⟨P, r, j, h1, h2, h3⟩ := ih
      refine ⟨pullback r (s k), pullback.fst _ _ ≫ r, pullback.lift j (u k) (h2.trans (hu k).symm),
        GlobalTheory.ProjSpace.isProjOver_pullback h1 (hs k), by rw [pullback.lift_fst_assoc, h2], fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ⟨pullback.snd _ _, pullback.condition.symm, pullback.lift_snd _ _ _⟩
      · obtain ⟨p, hp1, hp2⟩ := h3 i hi
        exact ⟨pullback.fst _ _ ≫ p, by rw [Category.assoc, hp1], by rw [pullback.lift_fst_assoc, hp2]⟩
  have := Fintype.ofFinite I
  obtain ⟨P, r, j, h1, h2, h3⟩ := key Finset.univ
  choose p hp using fun i => h3 i (Finset.mem_univ i)
  exact ⟨P, r, j, p, h1, h2, hp⟩

theorem isProper_of_proj {O : Type} [CommRing O] {X : Scheme.{0}} {s : X ⟶ Sp O} (h : IsProjOver s) :
    IsProper s := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str O N
  infer_instance

theorem exists_join {O : Type} [CommRing O] {U : Scheme.{0}} (σ : U ⟶ Sp O) {I : Type}
    [Finite I] [Nonempty I] (X : I → Scheme.{0}) (s : ∀ i, X i ⟶ Sp O) (hs : ∀ i, IsProjOver (s i))
    (u : ∀ i, U ⟶ X i) (hu : ∀ i, u i ≫ s i = σ) [∀ i, Flat (u i)] [∀ i, Mono (u i)]
    [∀ i, QuasiCompact (u i)] :
    ∃ (P : Scheme.{0}) (r : P ⟶ Sp O) (j : U ⟶ P) (p : ∀ i, P ⟶ X i), IsProjOver r ∧ j ≫ r = σ ∧
      ∀ i, p i ≫ s i = r ∧ IsPullback (𝟙 U) j (u i) (p i) := by
  obtain ⟨P, r, j, p, h1, h2, h3⟩ := exists_common_projective σ X s hs u hu
  have := isProper_of_proj h1
  have hsep : ∀ i, IsSeparated (p i) := fun i => by
    have : IsSeparated (p i ≫ s i) := by rw [(h3 i).1]; infer_instance
    exact IsSeparated.of_comp (p i) (s i)
  have : QuasiCompact j := by
    obtain ⟨i⟩ := ‹Nonempty I›
    have : QuasiCompact (j ≫ p i) := by rw [(h3 i).2]; infer_instance
    exact QuasiCompact.of_comp j (p i)
  obtain ⟨N, e, he, hr⟩ := h1
  refine ⟨j.image, j.imageι ≫ r, j.toImage, fun i => j.imageι ≫ p i,
    ⟨N, j.imageι ≫ e, inferInstance, by rw [Category.assoc, hr]⟩, by simpa using h2, fun i => ⟨?_, ?_⟩⟩
  · rw [Category.assoc, (h3 i).1]
  · exact isPullback_toImage_comp j (p i) (u i) (h3 i).2

theorem exists_join_scheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → CharZero O → ∃ (X : Scheme.{0}) (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap β)) (f : ∀ i, pullback s (spMap (b i)) ⟶ (C i).X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X ∧ IsProjOver s ∧ Flat s ∧ jQ ≫ pullback.snd _ _ = c ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ ∀ i, f i ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback s (spMap (b i)), g ≫ pullback.fst _ _ = jQ ≫ pullback.fst _ _ → g ≫ f i = (C i).j) ∧ ∀ x : ↥(pullback s (spMap (b i))), f i x ∈ Set.range (C i).j → pullback.fst s (spMap (b i)) x ∈ Set.range (jQ ≫ pullback.fst s (spMap β)) := by
  intro E _ _ _ H U F O _ _ c t β I _ _ R _ a b ω C hβ hR _ _
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hβ
  letI := β.toAlgebra
  have hβ : algebraMap O F = β := rfl
  have hcl : ∀ i, ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp O) (κ : (C i).X ⟶ X'), IsProjOver s' ∧
      IsPullback κ (C i).s s' (spMap (b i)) := fun i => by
    letI := (b i).toAlgebra
    have := (hR i).2.2
    exact GlobalTheory.ProjClosure.exists_projective_closure O (R i) (a i) (C i).X (C i).s (C i).proj
  choose X' s' κ hs' hk using hcl
  have hbo : ∀ i, IsOpenImmersion (spMap (b i)) := fun i => by
    letI := (b i).toAlgebra
    have := (hR i).2.2
    exact IsOpenImmersion.of_isLocalization (a i)
  have hko : ∀ i, IsOpenImmersion (κ i) := fun i => MorphismProperty.of_isPullback (hk i).flip (hbo i)
  have hj : ∀ i, IsPreimmersion (C i).j ∧ Flat (C i).j ∧ QuasiCompact (C i).j ∧ QuasiCompact (κ i) :=
    fun i => by
      obtain ⟨⟨⟨_, _⟩, _, hfr⟩, _, _⟩ := hR i
      letI := (ω i).toAlgebra
      obtain ⟨-, -, -, h1, h2, -, h3⟩ := GlobalTheory.genericPart_dense_proOpen (R i) F (C i).X U (C i).s (C i).jQ
        (C i).flat (C i).proj (C i).jQ_open (C i).jQ_dense
      exact ⟨h1, h2, h3, MorphismProperty.of_isPullback (hk i).flip inferInstance⟩
  have hωb : ∀ i, spMap (ω i) ≫ spMap (b i) = spMap β := fun i => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, (hR i).2.1]
  have hjs : ∀ i, (C i).j ≫ (C i).s = c ≫ spMap (ω i) := fun i => by
    rw [Cpt.j, Category.assoc, pullback.condition, reassoc_of% (C i).jQ_over]
  have h1 := fun i => (hj i).1
  have h2 := fun i => (hj i).2.1
  have h3 := fun i => (hj i).2.2.1
  have h4 := fun i => (hj i).2.2.2
  obtain ⟨P, r, j, p, hr, hjr, hp⟩ := exists_join (c ≫ spMap β) X' s' hs' (fun i => (C i).j ≫ κ i)
    (fun i => by rw [Category.assoc, (hk i).w, reassoc_of% (hjs i), hωb])
  have hjp : ∀ i, j ≫ p i = (C i).j ≫ κ i := fun i => by simpa using (hp i).2.w.symm
  let jP : U ⟶ pullback r (spMap β) := pullback.lift j c hjr
  have hjP₁ : jP ≫ pullback.fst _ _ = j := pullback.lift_fst _ _ _
  have hjP₂ : jP ≫ pullback.snd _ _ = c := pullback.lift_snd _ _ _
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hU : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U :=
    isNormalScheme_of_flat_preimmersion (C i₀).j (C i₀).normal
  have hjPo : IsOpenImmersion jP := by
    have G := (IsPullback.of_hasPullback (C i₀).s (spMap (ω i₀))).flip.paste_vert (hk i₀).flip
    rw [hωb] at G
    let ρ : pullback r (spMap β) ⟶ pullback (C i₀).s (spMap (ω i₀)) :=
      G.lift (pullback.snd _ _) (pullback.fst _ _ ≫ p i₀)
        (by rw [Category.assoc, (hp i₀).1, pullback.condition])
    have hρ₁ : ρ ≫ pullback.snd _ _ = pullback.snd _ _ := G.lift_fst _ _ _
    have hρ₂ : ρ ≫ pullback.fst _ _ ≫ κ i₀ = pullback.fst _ _ ≫ p i₀ := G.lift_snd _ _ _
    have A : IsPullback ρ (pullback.fst r (spMap β)) (pullback.fst _ _ ≫ κ i₀) (p i₀) := by
      refine IsPullback.of_right (h₁₂ := pullback.snd _ _) (h₂₂ := s' i₀) (v₁₃ := spMap β) ?_ hρ₂ G
      rw [hρ₁, (hp i₀).1]
      exact (IsPullback.of_hasPullback _ _).flip
    have B : IsPullback (𝟙 U) jP (C i₀).jQ ρ := by
      refine IsPullback.of_bot (v₂₁ := pullback.fst _ _) (v₂₂ := pullback.fst _ _ ≫ κ i₀) (h₃₁ := p i₀)
        ?_ ?_ A
      · rw [hjP₁, ← Category.assoc]
        exact (hp i₀).2
      · refine G.hom_ext ?_ ?_
        · rw [Category.id_comp, Category.assoc, hρ₁, hjP₂, (C i₀).jQ_over]
        · rw [Category.id_comp, Category.assoc, hρ₂, reassoc_of% hjP₁, hjp, Cpt.j, Category.assoc]
    exact MorphismProperty.of_isPullback B (C i₀).jQ_open
  obtain ⟨Y, π, jQ, -, hY, hproj, hflat, hq₁, hq₂, hqo, hqd, hqr⟩ :=
    GlobalTheory.exists_normal_finite_model_of_finite_over_open O F P U r c j jP.opensRange jP.isoOpensRange.hom hr hU inferInstance
      (by rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]; exact hjP₁)
      (by rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]; exact hjP₂)
  let f : ∀ i, pullback (π ≫ r) (spMap (b i)) ⟶ (C i).X := fun i =>
    (hk i).lift (pullback.fst _ _ ≫ π ≫ p i) (pullback.snd _ _)
      (by rw [Category.assoc, Category.assoc, (hp i).1, pullback.condition])
  have hf : ∀ i, f i ≫ κ i = pullback.fst _ _ ≫ π ≫ p i := fun i => (hk i).lift_fst _ _ _
  refine ⟨Y, π ≫ r, jQ, f, hY, hproj, hflat, hq₁, hqo, hqd, fun i => ⟨(hk i).lift_snd _ _ _, ?_, ?_⟩⟩
  · intro g hg
    have hq₂' : jQ ≫ pullback.fst (π ≫ r) (spMap β) ≫ π = j := hq₂
    rw [← cancel_mono (κ i), Category.assoc, hf, reassoc_of% hg, reassoc_of% hq₂', hjp]
  · rintro x ⟨y, hy⟩
    have e1 : p i (π (pullback.fst (π ≫ r) (spMap (b i)) x)) = ((C i).j ≫ κ i) y := by
      rw [Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply (f i), hf]
      simp only [Scheme.Hom.comp_apply]
    obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback (hp i).2 y _ e1.symm
    obtain ⟨w, hw⟩ : pullback.fst (π ≫ r) (spMap (b i)) x ∈ Set.range (pullback.fst (π ≫ r) (spMap β)) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨c z, ?_⟩
      rw [Scheme.Hom.comp_apply π r, ← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hjr]
    obtain ⟨v, hv⟩ := (hqr w).mpr ⟨jP.isoOpensRange.hom z, by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.isoOpensRange_hom_ι_assoc]
      exact (congrArg (fun m : U ⟶ P => m z) hjP₁).trans (hz.trans (congrArg π hw.symm))⟩
    exact ⟨v, by rw [Scheme.Hom.comp_apply, ← hw]; exact congrArg _ hv⟩

end GlobalTheory.JoinModels
end
end
