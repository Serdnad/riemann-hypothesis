module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueJet
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecAlg

variable {X X₁ X₂ Z : Scheme.{0}} {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂]

def germCst (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a : R) : Z.presheaf.stalk z :=
  gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)

theorem germCst_comp (q : Z ⟶ Spec (CommRingCat.of R₂)) (h : R₁ →+* R₂) (z : Z) (a : R₁) :
    germCst (q ≫ Spec.map (CommRingCat.ofHom h)) z a = germCst q z (h a) := by
  refine (gs_pull q (Spec.map (CommRingCat.ofHom h)) z ⊤ trivial _).symm.trans ?_
  exact congrArg (gs q z ⊤) (congrArg (fun t => t.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom h))).symm

theorem gs_cst (p : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) (r : Z ⟶ X) (z : Z) (hz : r z ∈ W) (a : R) :
    gs r z W (GlobalTheory.AbLaw.cst p W a) = germCst (r ≫ p) z a :=
  (gs_res r z le_top hz _).trans (gs_pull r p z ⊤ trivial _)

variable {p : X ⟶ Spec (CommRingCat.of R)} {N : LB X} (P : Perf p N)

def Given (π : X₁ ⟶ X) (f : X₁ ⟶ Spec (CommRingCat.of R₁)) (v : Fin P.a → R₁) (s : LB.Sec (N.pull π)) : Prop :=
  ∀ i, rs X₁ (le_pull N π (P.le i)) (s.f (fun _ => P.ch i)) =
    ∑ k, GlobalTheory.AbLaw.cst f (π ⁻¹ᵁ P.W i) (v k) * (π.app (P.W i)).hom (P.u k i)

def comb (ψ : Z ⟶ X) (z : Z) (J : (Z ⟶ X) → N.ι) (i : P.I) (c : Fin P.a → Z.presheaf.stalk z) :
    Z.presheaf.stalk z :=
  (gm ψ z (N.U (J ψ) ⊓ N.U (P.ch i)) (N.g (J ψ) (P.ch i))).val * ∑ k, c k * gs ψ z (P.W i) (P.u k i)

variable {P}

theorem Given.sval {π : X₁ ⟶ X} {f : X₁ ⟶ Spec (CommRingCat.of R₁)} {v : Fin P.a → R₁} {s : LB.Sec (N.pull π)}
    (hs : Given P π f v s) (r : Z ⟶ X₁) (z : Z) {J : (Z ⟶ X) → N.ι} (hJ : Good N z J) (i : P.I)
    (hi : (r ≫ π) z ∈ P.W i) :
    sval s r z J = comb P (r ≫ π) z J i (fun k => germCst (r ≫ f) z (v k)) := by
  have hm : r z ∈ π ⁻¹ᵁ P.W i := hi
  refine (sec_trans s r z (hJ.mem _ r) (le_pull N π (P.le i) hm)).trans (congrArg₂ (· * ·) ?_ ?_)
  · simp only [trF, Finset.univ_unique, Finset.prod_singleton, zpow_one]
  · refine (gs_res r z (le_pull N π (P.le i)) hm _).symm.trans ((congrArg (gs r z _) (hs i)).trans ?_)

    rw [gs_eq r z _ hm, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => (gs_eq r z _ hm _).symm.trans ((gs_mul r z _ hm _ _).trans ?_)
    exact congrArg₂ (· * ·) (gs_cst f _ r z hm _) (gs_pull r π z _ hi _)

theorem Given.sval_eq {π₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ Spec (CommRingCat.of R₁)} {v : Fin P.a → R₁}
    {s₁ : LB.Sec (N.pull π₁)} {π₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ Spec (CommRingCat.of R₂)} {s₂ : LB.Sec (N.pull π₂)}
    (h : R₁ →+* R₂) (r : X₂ ⟶ X₁) (hπ : r ≫ π₁ = π₂) (hf : r ≫ f₁ = f₂ ≫ Spec.map (CommRingCat.ofHom h))
    (h₁ : Given P π₁ f₁ v s₁) (h₂ : Given P π₂ f₂ (fun k => h (v k)) s₂) (z : X₂) {J : (X₂ ⟶ X) → N.ι}
    (hJ : Good N z J) : Geo.Tor.sval s₁ r z J = Geo.Tor.sval s₂ (𝟙 _) z J := by
  subst hπ
  have hz : (r ≫ π₁) z ∈ ⨆ i, P.W i := by rw [P.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  rw [h₁.sval r z hJ i hi, h₂.sval (𝟙 _) z hJ i hi, Category.id_comp, Category.id_comp, hf]
  simp only [germCst_comp]

theorem sec_ext {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  obtain ⟨a, ha⟩ := s
  obtain ⟨b, hb⟩ := s'
  obtain rfl : a = b := funext h
  rfl

theorem mulVec_map {a b : ℕ} (D : Matrix (Fin b) (Fin a) R) (g : R →+* R₁) (h : R₁ →+* R₂) {g' : R →+* R₂}
    (hg : h.comp g = g') (v : Fin a → R₁) (j : Fin b) :
    (D.map g').mulVec (fun k => h (v k)) j = h ((D.map g).mulVec v j) := by
  subst hg

  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, RingHom.comp_apply]

theorem sval_eq_iff (hN : N.IsLB) {g₁ : R →+* R₁} {g₂ : R →+* R₂}
    {π₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ Spec (CommRingCat.of R₁)} {π₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ Spec (CommRingCat.of R₂)}
    {E₁ : {v : Fin P.a → R₁ // (P.D₀.map g₁).mulVec v = 0} ≃ LB.Sec (N.pull π₁)}
    {E₂ : {v : Fin P.a → R₂ // (P.D₀.map g₂).mulVec v = 0} ≃ LB.Sec (N.pull π₂)}
    (H₁ : ∀ v, Given P π₁ f₁ v.1 (E₁ v)) (H₂ : ∀ v, Given P π₂ f₂ v.1 (E₂ v))
    (h : R₁ →+* R₂) (hg : h.comp g₁ = g₂) (r : X₂ ⟶ X₁) (hπ : r ≫ π₁ = π₂)
    (hf : r ≫ f₁ = f₂ ≫ Spec.map (CommRingCat.ofHom h)) (s₁ : LB.Sec (N.pull π₁)) (s₂ : LB.Sec (N.pull π₂)) :
    (∀ z J, Good N z J → sval s₁ r z J = sval s₂ (𝟙 _) z J) ↔
      ∀ k, h ((E₁.symm s₁).1 k) = (E₂.symm s₂).1 k := by
  obtain ⟨v₁, rfl⟩ := E₁.surjective s₁
  obtain ⟨v₂, rfl⟩ := E₂.surjective s₂
  rw [E₁.symm_apply_apply, E₂.symm_apply_apply]
  let w : {v : Fin P.a → R₂ // (P.D₀.map g₂).mulVec v = 0} := ⟨fun k => h (v₁.1 k), funext fun j => by
    rw [mulVec_map P.D₀ g₁ h hg, v₁.2, Pi.zero_apply, Pi.zero_apply, map_zero]⟩
  have key : ∀ z J, Good N z J → sval (E₁ v₁) r z J = sval (E₂ w) (𝟙 _) z J :=
    fun z J hJ => Given.sval_eq h r hπ hf (H₁ v₁) (H₂ w) z hJ
  constructor
  · intro H k
    have : E₂ w = E₂ v₂ := sec_ext (sec_ext_val hN fun y J hJ => (key y J hJ).symm.trans (H y J hJ))
    exact congrFun (congrArg Subtype.val (E₂.injective this)) k
  · intro H
    obtain rfl : w = v₂ := Subtype.ext (funext H)
    exact key

theorem eq_of_forall_mk (I : Ideal R) [IsHausdorff I R] {x y : R}
    (h : ∀ e : ℕ, Ideal.Quotient.mk (I ^ (e + 1)) x = Ideal.Quotient.mk (I ^ (e + 1)) y) : x = y := by
  refine sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq.1 (h n))

theorem exists_lim (I : Ideal R) [IsPrecomplete I R] (x : ∀ e : ℕ, R ⧸ I ^ (e + 1))
    (hx : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (x (e + 1)) = x e) :
    ∃ y : R, ∀ e, Ideal.Quotient.mk (I ^ (e + 1)) y = x e := by
  apply _root_.GlobalTheory.SeriesValue.exists_lim <;> assumption

theorem existsUnique_sec : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ N : LB Y.left, N.IsLB → ∀ f : ∀ e, LB.Sec (N.pull (fstG I e Y).left), (∀ e z J, Good N z J → sval (f (e + 1)) (thickMap R I e Y) z J = sval (f e) (𝟙 _) z J) → ∃! s : LB.Sec (N.pull (𝟙 Y.left)), ∀ e z J, Good N z J → sval s (fstG I e Y).left z J = sval (f e) (𝟙 _) z J := by
  intro R _ _ I hI Y hs hp N hN f hf
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R Y.left Y.hom hs hp N hN
  have pb₀ : IsPullback (𝟙 Y.left) Y.hom Y.hom (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E₀, H₀⟩ := P.sec R (RingHom.id R) Y.left (𝟙 _) Y.hom pb₀
  choose E H using fun e => P.sec (R ⧸ I ^ (e + 1)) (Ideal.Quotient.mk _) _ (fstG I e Y).left
    (thickObj R I e Y).hom (IsPullback.of_hasPullback Y.hom (thick R I e))
  have c₁ : ∀ e k, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))
      (((E (e + 1)).symm (f (e + 1))).1 k) = ((E e).symm (f e)).1 k := fun e =>
    (sval_eq_iff (P := P) hN (H (e + 1)) (H e) _ (Ideal.Quotient.factor_comp_mk _) (thickMap R I e Y)
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) (pullback.lift_snd _ _ _) _ _).1 (hf e)
  have c₂ : ∀ e (s : LB.Sec (N.pull (𝟙 Y.left))),
      (∀ z J, Good N z J → sval s (fstG I e Y).left z J = sval (f e) (𝟙 _) z J) ↔
        ∀ k, Ideal.Quotient.mk (I ^ (e + 1)) ((E₀.symm s).1 k) = ((E e).symm (f e)).1 k := fun e s =>
    sval_eq_iff (P := P) hN H₀ (H e) _ (RingHom.comp_id _) (fstG I e Y).left (Category.comp_id _)
      pullback.condition _ _
  choose v hv using fun k => exists_lim I (fun e => ((E e).symm (f e)).1 k) (fun e => c₁ e k)
  have hv₀ : (P.D₀.map (RingHom.id R)).mulVec v = 0 := funext fun j => eq_of_forall_mk I fun e => by
    rw [← mulVec_map P.D₀ (RingHom.id R) _ (RingHom.comp_id _), Pi.zero_apply, map_zero]
    simp only [hv]
    exact congrFun ((E e).symm (f e)).2 j
  refine ⟨E₀ ⟨v, hv₀⟩, fun e => (c₂ e _).2 fun k => ?_, fun s hs => ?_⟩
  · rw [E₀.symm_apply_apply]
    exact hv k e
  · refine (E₀.symm_apply_eq).1 (Subtype.ext (funext fun k => eq_of_forall_mk I fun e => ?_))
    exact ((c₂ e s).1 (hs e) k).trans (hv k e).symm

end GlobalTheory.SecAlg
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TrivRep

theorem eq_zero_of_away {S : Type} [CommRing S] (x : S)
    (h : ∀ q : PrimeSpectrum S, ∃ s ∉ q.asIdeal, algebraMap S (Localization.Away s) x = 0) : x = 0 := by
  by_contra hx
  have hne : LinearMap.ker (LinearMap.mulRight S x) ≠ ⊤ := fun e => hx (by
    have : (1 : S) ∈ LinearMap.ker (LinearMap.mulRight S x) := e ▸ Submodule.mem_top
    simpa using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨s, hs, h0⟩ := h ⟨m, hm.isPrime⟩
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s) _ x).1 h0
  exact hs (hm.isPrime.mem_of_pow_mem n (hle hc))

theorem exists_ideal {R : Type} [CommRing R] (P : ∀ (S : Type) [CommRing S], (R →+* S) → Prop)
    (hP : ∀ (S : Type) [CommRing S] (g : R →+* S) (T : Type) [CommRing T] (h : S →+* T), P S g → P T (h.comp g))
    (H : ∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal, ∃ I : Ideal R, ∀ (S : Type) [CommRing S] (g : R →+* S),
      IsUnit (g r) → (P S g ↔ I ≤ RingHom.ker g)) :
    ∃ I : Ideal R, ∀ (S : Type) [CommRing S] (g : R →+* S),
      (∀ q : PrimeSpectrum S, ∃ s ∉ q.asIdeal, P _ ((algebraMap S (Localization.Away s)).comp g)) ↔
        I ≤ RingHom.ker g := by
  classical
  choose r hr J hJ using H
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p => (PrimeSpectrum.basicOpen (r p) : Set (PrimeSpectrum R)))
    (fun p => (PrimeSpectrum.basicOpen (r p)).isOpen) (fun p _ => Set.mem_iUnion.2 ⟨p, hr p⟩)
  have ht' : ∀ (S : Type) [CommRing S] (g : R →+* S) (q : PrimeSpectrum S), ∃ i ∈ t, g (r i) ∉ q.asIdeal := by
    intro S _ g q
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (PrimeSpectrum.comap g q)))
    exact ⟨i, hi, h⟩
  let T := fun i => Localization.Away (r i) ⧸ (J i).map (algebraMap R (Localization.Away (r i)))
  let φ : ∀ i, R →+* T i := fun i => (Ideal.Quotient.mk _).comp (algebraMap R (Localization.Away (r i)))
  have hφ : ∀ i, P _ (φ i) := fun i =>
    (hJ i _ (φ i) ((IsLocalization.Away.algebraMap_isUnit (r i)).map (Ideal.Quotient.mk _))).2 fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
  have hk : ∀ i (S : Type) [CommRing S] (g : R →+* S), IsUnit (g (r i)) → P S g →
      RingHom.ker (φ i) ≤ RingHom.ker g := by
    intro i S _ g hu hg a ha
    have h₁ : (J i).map (algebraMap R (Localization.Away (r i))) ≤
        RingHom.ker (IsLocalization.Away.lift (S := Localization.Away (r i)) (r i) hu) := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker, IsLocalization.Away.lift_eq]
      exact (hJ i S g hu).1 hg hb
    have h₂ := h₁ (Ideal.Quotient.eq_zero_iff_mem.1 ha)
    rwa [RingHom.mem_ker, IsLocalization.Away.lift_eq] at h₂
  refine ⟨⨅ i ∈ t, RingHom.ker (φ i), fun S _ g => ⟨fun h a ha => ?_, fun h q => ?_⟩⟩
  · refine eq_zero_of_away (g a) fun q => ?_
    obtain ⟨s, hs, hPs⟩ := h q
    obtain ⟨i, hi, hq⟩ := ht' S g q
    have hu : IsUnit (algebraMap S (Localization.Away (s * g (r i))) (s * g (r i))) :=
      IsLocalization.Away.algebraMap_isUnit _
    rw [map_mul, IsUnit.mul_iff] at hu
    have h₁ := hP _ _ _ (IsLocalization.Away.lift (S := Localization.Away s) s hu.1) hPs
    rw [← RingHom.comp_assoc, IsLocalization.Away.lift_comp] at h₁
    refine ⟨s * g (r i), fun hm => (q.isPrime.mem_or_mem hm).elim hs hq, ?_⟩
    exact hk i _ _ hu.2 h₁ ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ha i) hi)
  · obtain ⟨i, hi, hq⟩ := ht' S g q
    have hu : IsUnit (algebraMap S (Localization.Away (g (r i))) (g (r i))) :=
      IsLocalization.Away.algebraMap_isUnit _
    refine ⟨g (r i), hq, (hJ i _ _ hu).2 fun a ha => ?_⟩
    have h₁ : ∀ j, ∃ n : ℕ, φ j (r i ^ n * a) = 0 := fun j => by
      have h₂ := (hJ i _ _ (IsLocalization.Away.algebraMap_isUnit (φ j (r i)))).1
        (hP _ _ _ (algebraMap (T j) (Localization.Away (φ j (r i)))) (hφ j)) ha
      obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (φ j (r i))) _ _).1 h₂
      exact ⟨n, by rw [map_mul, map_pow]; exact hc⟩
    choose n hn using h₁
    have h₃ : r i ^ (∑ j ∈ t, n j) * a ∈ ⨅ i ∈ t, RingHom.ker (φ i) := by
      refine (Submodule.mem_iInf _).2 fun j => (Submodule.mem_iInf _).2 fun hj => ?_
      rw [← Finset.add_sum_erase t n hj, add_comm, pow_add, _root_.mul_assoc]
      exact Ideal.mul_mem_left _ _ (hn j)
    have h₄ : g (r i ^ (∑ j ∈ t, n j) * a) = 0 := h h₃
    rw [RingHom.mem_ker, RingHom.comp_apply, ← (hu.pow (∑ j ∈ t, n j)).mul_right_eq_zero, ← map_pow,
      ← map_mul, ← map_pow, ← map_mul, h₄, map_zero]

variable {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (F : LB X)

def TrivOn (S : Type) [CommRing S] (g : R →+* S) : Prop :=
  Triv (F.pull (pullback.fst f (Spec.map (CommRingCat.ofHom g))))

theorem TrivOn.comp (S : Type) [CommRing S] (g : R →+* S) (T : Type) [CommRing T] (h : S →+* T)
    (H : TrivOn f F S g) : TrivOn f F T (h.comp g) :=
  CubeOpen.triv_comp (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom h))
    (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]))
    (pullback.lift_fst _ _ _) H

theorem trivOn_of_subsingleton (S : Type) [CommRing S] [Subsingleton S] (g : R →+* S) : TrivOn f F S g := by
  have he : IsEmpty (pullback f (Spec.map (CommRingCat.ofHom g)) : Scheme.{0}) :=
    ⟨fun x => (inferInstance : IsEmpty (PrimeSpectrum S)).elim
      ((pullback.snd f (Spec.map (CommRingCat.ofHom g))) x)⟩
  have hs : ∀ U : (pullback f (Spec.map (CommRingCat.ofHom g)) : Scheme.{0}).Opens,
      Subsingleton Γ(pullback f (Spec.map (CommRingCat.ofHom g)), U) := fun U => by
    have : U = ⊥ := TopologicalSpace.Opens.ext (Set.eq_empty_of_isEmpty _)
    subst this
    infer_instance
  exact ⟨⟨fun _ => 1⟩, fun i j => Units.ext (Subsingleton.elim _ _)⟩

theorem loc_iff {S : Type} [CommRing S] {g : R →+* S} {X' : Scheme.{0}} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of S)} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (q : PrimeSpectrum S) :
    (∃ U : (Spec (CommRingCat.of S)).Opens, q ∈ U ∧ Triv ((F.pull π).pull (f' ⁻¹ᵁ U).ι)) ↔
      ∃ s ∉ q.asIdeal, TrivOn f F _ ((algebraMap S (Localization.Away s)).comp g) := by
  have hr : ∀ s : S, Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))) =
      (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum S)) := fun s =>
    PrimeSpectrum.localization_away_comap_range (Localization.Away s) s
  constructor
  · rintro ⟨U, hq, t, ht⟩
    obtain ⟨_, ⟨s, rfl⟩, hs, hU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (u := U.1) hq U.isOpen
    refine ⟨s, hs, ?_⟩
    have ht' : Triv (F.pull ((f' ⁻¹ᵁ U).ι ≫ π)) := exists_isGen_linComb_of_pull F _ _ _ t ht
    let l := h.lift (pullback.fst f (Spec.map (CommRingCat.ofHom ((algebraMap S (Localization.Away s)).comp g))))
      (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s))))
      (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
    have hl : Set.range l ⊆ Set.range (f' ⁻¹ᵁ U).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      apply hU
      change (l ≫ f') y ∈ _
      rw [h.lift_snd]
      exact (hr s).le ⟨_, rfl⟩
    refine CubeOpen.triv_comp (IsOpenImmersion.lift _ l hl) ?_ ht'
    rw [IsOpenImmersion.lift_fac_assoc]
    exact h.lift_fst _ _ _
  · rintro ⟨s, hs, ht⟩
    refine ⟨PrimeSpectrum.basicOpen s, hs, CubeOpen.triv_pull_pull _ _ ?_⟩
    haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))) :=
      IsOpenImmersion.of_isLocalization s
    have hsub : Set.range ((f' ⁻¹ᵁ (PrimeSpectrum.basicOpen s)).ι ≫ f') ⊆
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))) := by
      rintro _ ⟨y, rfl⟩
      rw [hr]
      exact y.2
    refine CubeOpen.triv_comp (pullback.lift _ (IsOpenImmersion.lift _ _ hsub) ?_) (pullback.lift_fst _ _ _) ht
    rw [CommRingCat.ofHom_comp g, Spec.map_comp, IsOpenImmersion.lift_fac_assoc, Category.assoc, Category.assoc, h.w]

theorem exists_ideal_locTriv : GlobalFnsSt → ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ F : LB B.left, F.IsLB → ∃ I : Ideal R, ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) → ((∀ p : Spec (CommRingCat.of R'), ∃ U : (Spec (CommRingCat.of R')).Opens, p ∈ U ∧ Triv ((F.pull π).pull (f' ⁻¹ᵁ U).ι)) ↔ I ≤ RingHom.ker g) := by
  intro hG R _ B _ hB hproj F hF
  haveI := hB.proper
  haveI := hB.geomConnected
  have hP := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R _ B.hom hB.smooth hproj F hF
  have hQ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R _ B.hom hB.smooth hproj _ (isLB_pw hF (-1))
  have hC := GlobalTheory.TrivLocus.isClosed_trivLocus R _ B.hom F hF hP hQ hB.proper
    (GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected)
  obtain ⟨I, hI⟩ := exists_ideal (TrivOn B.hom F) (TrivOn.comp B.hom F) (fun p => by
    by_cases hp : p ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0})
      (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
        IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) ∧ Triv (F.pull π)}
    · obtain ⟨K, _, g₀, X₀, π₀, f₀, hk, h₀, ht⟩ := hp
      obtain ⟨r, I, hr, -, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R _ B.hom F hF hP inferInstance inferInstance K g₀ X₀ π₀ f₀
        h₀ (CubeOpen.bijective_appTop hG B hB h₀) ht
      exact ⟨r, hk ▸ hr, I, fun S _ g hu => H S g _ _ _ (IsPullback.of_hasPullback _ _) hu⟩
    · obtain ⟨_, ⟨r, rfl⟩, hr, hU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (Set.mem_compl hp) hC.isOpen_compl
      refine ⟨r, hr, ⊤, fun S _ g hu => ⟨fun ht => ?_, fun h => ?_⟩⟩
      · rcases subsingleton_or_nontrivial S with _ | _
        · exact fun a _ => Subsingleton.elim _ _
        obtain ⟨m, hm⟩ := Ideal.exists_maximal S
        letI := Ideal.Quotient.field m
        let g' := (Ideal.Quotient.mk m).comp g
        refine (hU (a := ⟨RingHom.ker g', RingHom.ker_isPrime g'⟩) (hu.map (Ideal.Quotient.mk m)).ne_zero ?_).elim
        exact ⟨S ⧸ m, inferInstance, g', _, _, _, rfl, IsPullback.of_hasPullback _ _, ht.comp B.hom F S g _ _⟩
      · haveI : Subsingleton S := subsingleton_of_zero_eq_one
          ((h (Submodule.mem_top (x := 1))).symm.trans (map_one g))
        exact trivOn_of_subsingleton B.hom F S g)
  refine ⟨I, fun S _ g X' π f' h => ?_⟩
  rw [← hI S g]
  exact forall_congr' fun q => loc_iff B.hom F h q

end GlobalTheory.TrivRep
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw.CubeProj

open CubeGen

theorem isProjBy_baseChange {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} (hf : IsProjBy f) {φ : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
    {t : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} (h : IsPullback φ f' f t) : IsProjBy f' := by
  obtain ⟨g, rfl⟩ := Spec.map_surjective t
  obtain ⟨H, hH, n, s, hs⟩ := hf
  have hH' : (H.pull φ).IsLB := DVR.linComb_isLB _ hH _ _
  obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl hH'
  choose s' hs' using fun (j : Fin (n + 1)) => (GlobalTheory.SecPullIso.section_pull X X' φ H _ w hH hH' hw (s j)).1.exists
  refine ⟨_, hH', n, s', GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H n s hH hs R' g.hom X' f' φ h.w ?_
    _ w s' hH' hw hs'⟩
  have e : pullback.lift φ f' h.w = h.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  have : IsClosedImmersion (pullback.lift φ f' h.w) := by rw [e]; infer_instance
  exact this

theorem exists_gen_theta_of_isProjBy (hG : GlobalFnsSt) (R₀ : Type) [CommRing R₀]
    (A : Over (Spec (CommRingCat.of R₀))) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (hp : IsProjBy A.hom) (M : LB A.left) (hM : M.IsLB) : ∃ t : LB.Gen (Theta A M), t.IsGen := by
  have hI := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have hPerf := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj
  have hSegre := GlobalTheory.AbLaw.isProjBy_tensor
  have hClosed := GlobalTheory.TrivLocus.isClosed_trivLocus
  have hOpen := GlobalTheory.AbLaw.CubeOpen.triv_basicOpen_of_triv_fibre hG GlobalTheory.AbLaw.Seesaw.seesaw
    (GlobalTheory.SmallExtLift.exists_gen_of_small_extension hG GlobalTheory.KuennethOne.kuenneth_injective)
  have := hA.geomConnected
  have H := fibTriv_clopen M (thφ A (x3 A)) thε (x3 A 2).left (fun R _ j => by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_cube_chart A j
    have hB := isAb_baseChange hA (j ≫ A.hom)
    have one := one_left_fst (A := A) (j ≫ A.hom)
    have pB : IsProjBy ((Over.pullback (j ≫ A.hom)).obj A).hom :=
      isProjBy_baseChange hp (IsPullback.of_hasPullback A.hom (j ≫ A.hom))
    let B := (Over.pullback (j ≫ A.hom)).obj A
    have : Smooth B.hom := hB.smooth
    have : IsProper B.hom := hB.proper
    have : GeometricallyConnected B.hom := hB.geomConnected
    have sm : Smooth (B ⊗ B).hom := by
      change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have pr : IsProper (B ⊗ B).hom := by
      change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have gc : GeometricallyConnected (B ⊗ B).hom := by
      change GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)
      exact GeometricallyConnected.comp _ _
    have hN : (LB.LinComb M (fun k => q ≫ thφ A (x3 A) k) thε).IsLB := DVR.linComb_isLB _ hM _ _
    have pf := hPerf R _ _ sm (hSegre R B B pB pB)
    refine ⟨_, q, (B ⊗ B).hom, hq, hClosed R _ _ _ hN (pf _ hN) (pf _ (isLB_pw hN _)) pr (hI _ _ _ sm gc),
      fun F _ g Z π f' => hOpen R B hB _ hN (pf _ hN) ?_ ?_ F g Z π f'⟩
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hM _ (prod_face _ 1 (B.hom ≫ j ≫ A.hom) ?_)
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact one B
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hM _ (prod_face _ 0 (B.hom ≫ j ≫ A.hom) ?_)
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact one B)
  have hclopen : IsClopen (fibTriv M (thφ A (x3 A)) thε (x3 A 2).left) :=
    ⟨H.2, by rw [H.1.antisymm (locTriv_subset _ _ _ _)]; exact isOpen_locTriv _ _ _ _⟩
  have all : ∀ t, t ∈ fibTriv M (thφ A (x3 A)) thε (x3 A 2).left := fun t => by
    have hr : Set.range ((Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t)) = {A.hom t} := Scheme.range_fromSpecResidueField _
    obtain ⟨y, hy⟩ := hr.ge rfl
    let g := (Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t) ≫ η[A].left
    have gw : g ≫ A.hom = (Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t) := by
      rw [Category.assoc, Over.w]; exact Category.comp_id _
    refine (A.hom.isConnected_preimage_singleton (A.hom t)).isPreconnected.subset_isClopen hclopen
      ⟨g y, (congrArg (fun m : Spec ((Spec (CommRingCat.of R₀)).residueField (A.hom t)) ⟶ Spec (CommRingCat.of R₀) => m y) gw).trans hy, ?_⟩ rfl
    exact ⟨(Spec (CommRingCat.of R₀)).residueField (A.hom t), inferInstance, g, _, _, _, ⟨y, rfl⟩,
      IsPullback.of_hasPullback (x3 A 2).left g,
      trivAt_of_formal hM _ (prod_face _ 2 (pullback.snd _ g ≫ (Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t))
        (pullback.condition.trans (Category.assoc _ _ _).symm))⟩
  let e : A ⟶ G3 A := lift 1 (lift 1 (𝟙 _))
  have e₀ : e ≫ x3 A 0 = 1 := by simp [e, x3]
  have e₂ : e ≫ x3 A 2 = 𝟙 _ := by simp [e, x3]
  refine triv_of_local hM (thφ A (x3 A)) thε (x3 A 2).left e.left (congrArg (fun q => q.left) e₂)
    (fun Z b => prod_face _ 0 (b ≫ A.hom) ?_) (fun V => ?_) (fun s => H.1 (all s))
  · rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · obtain ⟨q, hq, -⟩ := exists_cube_chart A V.ι
    have hB := isAb_baseChange hA (V.ι ≫ A.hom)
    refine ⟨_, q, _, hq, ?_⟩
    rw [← Over.w (snd _ _)]
    exact surj_comp (surj_snd hG hB _) (hG _ _ hB).2

theorem exists_gen_theta_abelianVariety : GlobalFnsSt → ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ M : LB B.left, M.IsLB → ∃ t : LB.Gen (Theta B M), t.IsGen :=
  fun hG K _ _ B _ _ hB hp M hM => exists_gen_theta_of_isProjBy hG K B hB hp M hM

end GlobalTheory.AbLaw.CubeProj
end
