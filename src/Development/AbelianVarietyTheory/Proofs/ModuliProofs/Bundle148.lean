module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TwistedPowTranslate
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle145
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle140
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle134

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.EmbVA

theorem act_unique (hL : Out.SymLiftSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) (k : ℕ) (z : ℤ)
    (hz : z = k) (ho : Odd k) (hu : IsUnit (k : Γ(S, ⊤))) {T : Over S} (x : T ⟶ P.A) (hx : x ^ k = 1)
    {θ θ' : Out.ThetaGrp P.A P.L z T} (h : Out.SymLift P.A P.L z k x θ) (h' : Out.SymLift P.A P.L z k x θ')
    {s s₁ s₂ : LB.Sec (Out.LPow P.A P.L z T)} (a₁ : Out.IsActOf P.A P.L z θ s s₁)
    (a₂ : Out.IsActOf P.A P.L z θ' s s₂) (j) : s₁.f j = s₂.f j := by
  subst hz
  have hc := (hL S P k ho hu T x hx).2 θ θ' h h'
  refine sec_ext_val P.isLB (s := s₁) (s' := s₂) (fun y J hJ => ?_) j
  have e₁ := GlobalTheory.ThetaPowOrder.act_sval a₁ (𝟙 _) y hJ
  have e₂ := GlobalTheory.ThetaPowOrder.act_sval a₂ (𝟙 _) y hJ
  have e₃ := val_corr hJ hc (𝟙 _)
  have e₄ : θ.pt = θ'.pt := h.pt_eq.trans h'.pt_eq.symm
  refine e₁.trans (Eq.trans ?_ e₂.symm)
  exact congrArg₂ (fun u (p : T ⟶ P.A) => Units.val u * sval (L := P.L) s (𝟙 _ ≫ (Out.translT P.A p).left) y J) e₃ e₄

theorem lbIso_pow {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (n : ℕ) (z : ℤ) (hz : z = n) :
    LBIso (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => z)) ((lbPow L n).pull f) := by
  subst hz
  refine LBIso.chartPull (h := f) (A := lbPow L n) (B := lbPow L n) ?_ (Geo.Tor.chartPullPull _ f f rfl)
    ⟨_, idIso_isGen (LB.isLB_linComb hL _ _)⟩
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => f) j ≤
      f ⁻¹ᵁ LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0
  refine ⟨fun j _ => j 0, le, fun y j j' hj hj' => ?_⟩
  refine (gm_linComb L _ _ (𝟙 Y) y j j' hj hj').trans (Eq.trans ?_
    (gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => (n : ℤ)) f y _ _ (le j hj) (le j' hj')).symm)
  rw [Fin.prod_univ_one, Fintype.prod_unique, Category.id_comp, Category.comp_id]

theorem linComb_pow {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (y : Fin r → (T ⟶ A))
    (a : Fin r → ℕ) (n : ℕ) : Out.linComb y a ^ n = ∏ i, y i ^ (a i * n) := by
  rw [Out.linComb, List.prod_ofFn, ← Finset.prod_pow]
  simp only [pow_mul]

end GlobalTheory.EmbVA

namespace GlobalTheory


open EmbVA in
theorem embSec_veryAmple_periodic : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g (N' ^ 2) J b (spMap β)) (m : ℕ) σ, Odd N' → m ∣ N' → 2 ≤ m → t.Emb m (Over.mk (𝟙 (Sp K))) σ → IsIso (snd (Over.mk (𝟙 (Sp K))) t.A).left ∧ (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 (Sp K)))).IsLB ∧ VAmp (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ ∧ LBIso (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 (Sp K)))) ((lbPow t.L (m ^ 2)).pull (snd (Over.mk (𝟙 (Sp K))) t.A).left) ∧ (∀ a a' : Ix g (N' ^ 2), (∀ i, (a i).val ≡ (a' i).val [MOD m ^ 2]) → ∀ j, (σ a).f j = (σ a').f j) ∧ TorsBasis t.A (N' ^ 2) t.pt ∧ ∀ x : Out.baseOver (Sp K) ⟶ t.A, x ^ N' = 1 → ∃ h, t.lab h ^ N' = x := by
  intro hL hL2 o _ g N' J b K _ _ β t m σ hN hm h2 hE
  haveI := t.ab.comm
  have hN0 : N' ≠ 0 := by rintro rfl; simp at hN
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN0⟩
  have hid : (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) = 𝟙 _ := rfl
  have hbij : ∀ y : Out.baseOver (Sp K) ⟶ t.A, y ^ (N' ^ 2) = 1 →
      ∃! c : Fin (2 * g) → ZMod (N' ^ 2), Out.linComb t.pt (fun i => (c i).val) = y := fun y hy => by
    have := t.bij K (𝟙 _) y hy
    simpa only [hid, Category.id_comp] using this
  refine ⟨?_, LB.isLB_linComb t.isLB _ _, ?_, lbIso_pow t.isLB _ _ _ (by push_cast; rfl), ?_, ⟨Nat.pos_of_neZero _, t.torsion, hbij⟩, ?_⟩
  · show IsIso (pullback.snd (𝟙 (Sp K)) t.A.hom)
    infer_instance
  · refine GlobalTheory.T.isVeryAmpleSectionSystem_of_projectiveCoordinates K _ _ _ _ _ _ (GlobalTheory.T.projCoordRepresentation_geometric_fibre_spanning hL hL2 _ t.pol K (𝟙 _) _ _ σ (by nlinarith) ?_)
    exact GlobalTheory.EmbSpan.emb_span_eq_top hL hL2 o g N' J b _ _ t m K (𝟙 _) σ hN hm h2 hE
  · intro a a' haa j
    obtain ⟨th, s1, α, U, -, -, -, hU, hact⟩ := hE
    obtain ⟨c, rfl⟩ := hm
    have hm0 : 0 < m := by omega
    have hc : m * c / m = c := Nat.mul_div_cancel_left c hm0
    have hlab : t.lab a ^ (c ^ 2) = t.lab a' ^ (c ^ 2) := by
      rw [TObj.lab, TObj.lab, linComb_pow, linComb_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      refine pow_eq_pow_of_modEq ?_ (t.torsion i)
      exact ((haa i).mul_right' _).of_dvd (dvd_of_eq (mul_pow m c 2))
    have htor : (t.lab a ^ (c ^ 2)) ^ (m ^ 2) = 1 := by
      rw [← pow_mul, TObj.lab, linComb_pow]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [show (a i).val * (c ^ 2 * m ^ 2) = (m * c) ^ 2 * (a i).val by ring, pow_mul, t.torsion, one_pow]
    have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
      have h1 := (b.unit.map β).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      rw [map_natCast, map_natCast, mul_pow, Nat.cast_mul] at h1
      exact isUnit_of_mul_isUnit_left h1
    have h₁ := hU a
    have h₂ := hU a'
    simp only [Over.mk_hom, hid, Category.id_comp, hc] at h₁ h₂
    rw [← hlab] at h₂
    exact act_unique hL.symLift t.pol (m ^ 2) _ (by push_cast; rfl) (Odd.of_dvd_nat hN (Dvd.intro c rfl)).pow hu _ htor
      h₁ h₂ (hact a) (hact a') j
  · intro x hx
    obtain ⟨h1, -, h3, -⟩ := hL.mulN _ t.pol N' (Nat.pos_of_ne_zero hN0)
    obtain ⟨d, hd⟩ := TwistTranslate.exists_root t.pol (𝟙 (Sp K)) N' x
    have hd' : (show Out.baseOver (Sp K) ⟶ t.A from d) ^ N' = x := hd
    obtain ⟨h, hh, -⟩ := hbij d ((congrArg (fun n => (show Out.baseOver (Sp K) ⟶ t.A from d) ^ n) (pow_two N')).trans (by rw [pow_mul, hd', hx]))
    exact ⟨h, (congrArg (· ^ N') hh).trans hd'⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

theorem _root_.GlobalTheory.T.abelianLocus_isOpen_of_openImmersion_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, AbOpen (u i).G) → AbOpen t.G := by
  first | exact @GlobalTheory.AbLocusLocal.abOpen_of_cover | exact GlobalTheory.AbLocusLocal.abOpen_of_cover | (intros; apply GlobalTheory.AbLocusLocal.abOpen_of_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

theorem _root_.GlobalTheory.T.fibresSplit_of_openImmersion_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, SplitFib (u i).G) → SplitFib t.G := by
  first | exact @GlobalTheory.splitFib_of_openCover | exact GlobalTheory.splitFib_of_openCover | (intros; apply GlobalTheory.splitFib_of_openCover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

theorem _root_.GlobalTheory.T.hasFibrewiseTheta_of_openImmersion_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, HasTheta (u i).G (u i).PP.L) → HasTheta t.G t.PP.L := by
  first | exact @GlobalTheory.ThetaLocal.hasTheta_of_cover | exact GlobalTheory.ThetaLocal.hasTheta_of_cover | (intros; apply GlobalTheory.ThetaLocal.hasTheta_of_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELFrom

theorem countable_of_finiteType (o : Type) [CommRing o] (h : Algebra.FiniteType ℤ o) : Countable o := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  have hc : Countable (MvPolynomial (Fin n) ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (MvPolynomial.cardinalMk_le_max).trans ?_
    simp
  exact hf.countable

theorem fromC_of_isPEL : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (τ : SAB H S), IsPEL D a bas ρ t τ → ∀ (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ S), FromC em (PELClass (b := b) D a bas ρ em) t x := by
  intro hL _ E _ _ _ H D g J _ a w w' bas _ _ _ _ hcl N' o _ b em ρ _ hb S s t τ hτ K _ _ x
  obtain ⟨β', hβ'⟩ := Spec.map_surjective (x ≫ s)
  obtain ⟨β, hβ⟩ : ∃ β : o →+* K, x ≫ s = spMap β := ⟨β'.hom, hβ'.symm⟩
  obtain ⟨tx, htx⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g (N' ^ 2) J b S (Sp K) s (spMap β) x t hβ
  obtain ⟨τx, hτx⟩ := GlobalTheory.PELPull.isPEL_pull E H D g (N' ^ 2) J a bas o b ρ S (Sp K) s (spMap β) x t tx τ hβ htx hτ
  obtain ⟨K₀, β₀, t₀, hβ₀, hcount, -, ht₀⟩ := GlobalTheory.T.thetaLevel_object_descends_fg_subfield o g (N' ^ 2) J b K β tx
  haveI : Countable K₀ := hcount (countable_of_finiteType o hb.2.1)
  have hcomp : spMap β = spMap K₀.subtype ≫ spMap β₀ := by
    rw [← hβ₀, ← Spec.map_comp]; rfl
  obtain ⟨τ₀, hτ₀⟩ := GlobalTheory.T.pelStructure_descends_field_extension hL E H D g (N' ^ 2) J a bas o b ρ K₀ K K₀.subtype β₀ (spMap β) t₀ tx τx
    hcl hcomp ht₀ hτx
  obtain ⟨-, j, hj⟩ := GlobalTheory.T.exists_ringHom_complex_comp_eq_of_countable_field o em K₀ β₀ hb.1 hb.2.1 hb.2.2
  have hjc : spMap j ≫ spMap β₀ = spMap em := by
    rw [← hj, ← Spec.map_comp]; rfl
  obtain ⟨tc, htc⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g (N' ^ 2) J b (Sp K₀) (Sp ℂ) (spMap β₀) (spMap em) (spMap j) t₀ hjc
  have hc := GlobalTheory.PELPull.isPEL_pull E H D g (N' ^ 2) J a bas o b ρ (Sp K₀) (Sp ℂ) (spMap β₀) (spMap em) (spMap j)
    t₀ tc τ₀ hjc htc hτ₀
  unfold FromC
  rw [hβ]
  exact ⟨K₀, inferInstance, β₀, K₀.subtype, j, t₀, tx, tc, hj, hcomp, htx, ht₀, htc, hc⟩

end GlobalTheory.PELFrom
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory.ZM.GenericTrdeg

theorem exists_hom_of_ker_eq {R K K' : Type} [CommRing R] [Field K] [Field K'] (φ : R →+* K) (θ : R →+* K')
    (hk : RingHom.ker θ = RingHom.ker φ) (hs : ∀ z : K, ∃ a b, z = φ a / φ b) :
    ∃ j : K →+* K', j.comp φ = θ := by
  letI : Algebra (R ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker φ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective φ)
  haveI : IsFractionRing (R ⧸ RingHom.ker φ) K := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨a, b, h⟩ := hs z
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, h⟩
  let g : (R ⧸ RingHom.ker φ) →+* K' := Ideal.Quotient.lift _ θ (fun a ha => by rw [← hk] at ha; exact ha)
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hk]
    exact ha
  refine ⟨IsFractionRing.lift hg, ?_⟩
  ext a
  exact IsFractionRing.lift_algebraMap (K := K) hg (Ideal.Quotient.mk _ a)

theorem exists_local_domain {A K : Type} [CommRing A] [Field K] (e : A →+* K) (P : Ideal A) [P.IsPrime]
    (hP : P ≤ RingHom.ker e) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (ρ : A →+* R') (ψ : R' →+* K),
      RingHom.ker ρ = P ∧ ψ.comp ρ = e ∧ ∀ r, ψ r ≠ 0 → IsUnit r := by
  let e' : A ⧸ P →+* K := Ideal.Quotient.lift P e (fun a ha => hP ha)
  haveI : (RingHom.ker e').IsPrime := RingHom.ker_isPrime e'
  let R' := Localization.AtPrime (RingHom.ker e')
  have hu : ∀ y : (RingHom.ker e').primeCompl, IsUnit (e' y) := fun y =>
    isUnit_iff_ne_zero.2 y.2
  have hinj : Function.Injective (algebraMap (A ⧸ P) R') :=
    IsLocalization.injective R' (RingHom.ker e').primeCompl_le_nonZeroDivisors
  refine ⟨R', inferInstance, inferInstance, (algebraMap (A ⧸ P) R').comp (Ideal.Quotient.mk P),
    IsLocalization.lift hu, ?_, ?_, ?_⟩
  · ext a
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]
  · ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  · intro r hr
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker e').primeCompl r
    rw [IsLocalization.AtPrime.isUnit_mk'_iff R' (RingHom.ker e')]
    intro ha
    apply hr
    rw [IsLocalization.lift_mk']
    rw [show e' a = 0 from ha, zero_mul]

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  unfold spMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_inj {R R' : Type} [CommRing R] [CommRing R'] {f f' : R →+* R'} (h : spMap f = spMap f') : f = f' := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem exists_factor {X : Scheme.{0}} {R R' K : Type} [CommRing R] [CommRing R'] [Field K] (x : Sp R ⟶ X)
    [IsOpenImmersion x] (x' : Sp R' ⟶ X) (φ : R →+* K) (ψ : R' →+* K) (hψ : ∀ r, ψ r ≠ 0 → IsUnit r)
    (h : spMap ψ ≫ x' = spMap φ ≫ x) : ∃ χ : R →+* R', spMap χ ≫ x = x' ∧ ψ.comp χ = φ := by
  have hr : Set.range x' ⊆ Set.range x := by
    rintro _ ⟨q, rfl⟩
    let pt : Sp K := (⊥ : PrimeSpectrum K)
    have hsp : q ⤳ spMap ψ pt := by
      refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
      intro r hr
      change ψ r ∈ (⊥ : Ideal K)
      by_contra hne
      exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hr (hψ r hne))
    have hmem : x' (spMap ψ pt) ∈ Set.range x := by
      rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    exact (hsp.map x'.continuous).mem_open x.isOpenEmbedding.isOpen_range hmem
  have hχ : spMap (Spec.preimage (IsOpenImmersion.lift x x' hr)).hom ≫ x = x' := by
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  refine ⟨_, hχ, spMap_inj ?_⟩
  rw [← cancel_mono x, ← spMap_comp, Category.assoc, hχ, h]

theorem exists_algebraicIndependent : Out.Laws → Out.Laws2 → ∀ (n : ℕ), ∀ (g N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : ThetaFam n em C), ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ F.MM), IsOpenImmersion x → x ≫ F.s = spMap (algebraMap o R) → ∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R → (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y := by
  intro hL hL2 n g N' J Mat κ w w' o _ b em C d F hA hG R _ _ x hx hxs K _ _ φ hmin hsurj
  have hη : (spMap φ.toRingHom ≫ x) ≫ F.s = spMap (algebraMap o K) := by
    rw [Category.assoc, hxs, spMap_comp]
    congr 1
    exact φ.comp_algebraMap
  obtain ⟨v, hv, hvI⟩ := F.loc K (algebraMap o K) _ hη
  let e : MvPolynomial (Ix g (N' ^ 2)) o →+* K := MvPolynomial.eval₂Hom (algebraMap o K) v
  have hN : N' ≠ 0 := by
    rintro rfl
    have := b.unit.map (algebraMap o K)
    simp at this
  obtain ⟨c₁, hc₁⟩ := hvI.2 ⊥ Ideal.isPrime_bot 0
  set a₁ := 0 + (N' / n) • c₁ with ha₁
  have hva₁ : v a₁ ≠ 0 := hc₁
  obtain ⟨P, a₀, a, hP, hIP, hPp, -, hind⟩ := GlobalTheory.ThetaPrime.exists_prime_independent_ratios hL hL2 g N' J Mat κ w w' o b em C d hA hG
    (RingHom.ker e) a₁ hN (RingHom.ker_isPrime e) (fun G hG => hvI.1 G hG)
    (by simpa [e, RingHom.mem_ker] using hva₁)
  obtain ⟨R', _, _, ρ, ψ, hρ, hψρ, hψ⟩ := exists_local_domain e P hPp
  let β' : o →+* R' := ρ.comp MvPolynomial.C
  let v' : Ix g (N' ^ 2) → R' := fun i => ρ (MvPolynomial.X i)
  have hev : MvPolynomial.eval₂Hom β' v' = ρ := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp [β', v']
  have hψv : (fun i => ψ (v' i)) = v := by
    funext i
    have := RingHom.congr_fun hψρ (MvPolynomial.X i)
    simpa [e] using this
  have hψβ : ψ.comp β' = algebraMap o K := by
    ext i
    have := RingHom.congr_fun hψρ (MvPolynomial.C i)
    simpa [e, β'] using this
  have hI' : InMM n N' (thIdeal em C) β' v' := by
    refine ⟨fun G hG => ?_, fun q hq i => ?_⟩
    · have : ρ G = 0 := by rw [← RingHom.mem_ker, hρ]; exact hIP hG
      rw [← hev] at this
      exact this
    · obtain ⟨c, hc⟩ := hvI.2 ⊥ Ideal.isPrime_bot i
      refine ⟨c, fun hm => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (hψ _ ?_))⟩
      rw [congrFun hψv]
      exact hc
  obtain ⟨x', ⟨hx's, hx'v⟩, -⟩ := F.pts R' β' v' hI'
  have hcl : spMap ψ ≫ x' = spMap φ.toRingHom ≫ x := by
    refine (F.pts K (algebraMap o K) v hvI).unique ⟨?_, ?_⟩ ⟨hη, hv⟩
    · rw [Category.assoc, hx's, spMap_comp, hψβ]
    · have := GlobalTheory.hasTh_baseChange hL2 o g N' J b _ _ F.univ R' K ψ x' v' hx'v
      rwa [hψv] at this
  obtain ⟨χ, hχx, hψχ⟩ := exists_factor x x' φ.toRingHom ψ hψ hcl
  let K' := FractionRing R'
  let lam : R' →+* K' := algebraMap R' K'
  have hlam : Function.Injective lam := IsFractionRing.injective R' K'
  have hker : RingHom.ker (lam.comp χ) = RingHom.ker φ.toRingHom := by
    have hle : RingHom.ker (lam.comp χ) ≤ RingHom.ker φ.toRingHom := by
      intro r hr
      rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ hlam] at hr
      rw [RingHom.mem_ker, ← hψχ, RingHom.comp_apply, hr, map_zero]
    exact le_antisymm hle (hmin.2 ⟨RingHom.ker_isPrime _, bot_le⟩ hle)
  obtain ⟨j, hj⟩ := exists_hom_of_ker_eq φ.toRingHom (lam.comp χ) hker hsurj
  have hpt : spMap j ≫ spMap φ.toRingHom ≫ x = spMap lam ≫ x' := by
    rw [← Category.assoc, spMap_comp, hj, ← spMap_comp, Category.assoc, hχx]
  have h1 := GlobalTheory.hasTh_baseChange hL2 o g N' J b _ _ F.univ K K' j _ v hv
  have h2 := GlobalTheory.hasTh_baseChange hL2 o g N' J b _ _ F.univ R' K' lam _ v' hx'v
  rw [hpt] at h1
  obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ F.univ K' _ _ _ h1 h2
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨a₁, rfl⟩)
      (isUnit_iff_ne_zero.2 ((map_ne_zero j).2 hva₁)))
  have hjβ : j.comp (algebraMap o K) = lam.comp β' := by
    apply spMap_inj
    rw [← spMap_comp, ← hη, ← Category.assoc, hpt, Category.assoc, hx's, spMap_comp]
  have hkP : RingHom.ker (MvPolynomial.eval₂Hom (lam.comp β') (fun i => lam (v' i))) = P := by
    rw [← MvPolynomial.comp_eval₂Hom, hev, ← hρ]
    ext G
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ hlam, RingHom.mem_ker]
  refine ⟨fun i => v (a i) / v a₀, algebraicIndependent_iff.2 fun G hG => hind K' _ _ hkP G ?_⟩
  have h3 := congrArg j hG
  rw [MvPolynomial.aeval_def, MvPolynomial.hom_eval₂, hjβ, map_zero] at h3
  rw [← h3]
  congr 1
  funext i
  rw [hu, hu, mul_div_mul_left _ _ u.ne_zero, map_div₀]

end GlobalTheory.ZM.GenericTrdeg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.theta_ideal_prime_avoiding_variable : Out.Laws → Out.Laws2 → ∀ (g N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (p : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (a₁ : Ix g (N' ^ 2)), N' ≠ 0 → p.IsPrime → thIdeal em C ≤ p → MvPolynomial.X a₁ ∉ p → ∃ (P : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (a₀ : Ix g (N' ^ 2)) (a : Fin d → Ix g (N' ^ 2)), P.IsPrime ∧ thIdeal em C ≤ P ∧ P ≤ p ∧ MvPolynomial.X a₀ ∉ P ∧ ∀ (K : Type) [Field K] (β : o →+* K) (v : Ix g (N' ^ 2) → K), RingHom.ker (MvPolynomial.eval₂Hom β v) = P → ∀ G : MvPolynomial (Fin d) o, MvPolynomial.eval₂ β (fun i => v (a i) / v a₀) G = 0 → G = 0 := by
  first | exact @GlobalTheory.ThetaPrime.exists_prime_independent_ratios | exact GlobalTheory.ThetaPrime.exists_prime_independent_ratios | (intros; apply GlobalTheory.ThetaPrime.exists_prime_independent_ratios <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem System.levelStructureConditions_and_splitFibres : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW (i : Idx H p), (S.Y p W hp hW i).LevelStructureConditions p ∧ (S.Y p W hp hW i).SplitFibres := by
  intro hext L1 L2 L3 E _ _ _ H D Xo hpq hlev S p W hp hW i
  obtain ⟨l₀, h, hR⟩ := S.raises p W hp hW i
  have hdvd : l₀.Dvd i.l := ((GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp).2.1 i.l l₀ h).1
  obtain ⟨hded, hunit, -⟩ := (GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H i.l i.c).2.2.2 p W hp hW
  have hgood : Good (S.Y p W hp hW i).t := by
    obtain ⟨b, r, ν, -, -, ⟨A⟩⟩ := hR
    exact good_pullback L3.gtBaseChange E H _ _ _ _ A.π A.mu (S.B (S.ch p) l₀ h.1).good
  refine ⟨⟨?_, fun hA => ?_, ?_, ?_, ?_, ?_⟩, hgood.2.1⟩
  · exact GlobalTheory.T.levelAut_acts_on_raised_model L1 L2 L3 E H D Xo _ _ _ hpq l₀ _ i.l i.c _ _ _ hdvd hded hR
  · exact GlobalTheory.T.raised_model_level_one_descends L1 L2 L3 E H D Xo _ _ _ hlev l₀ _ i.l i.c _ _ _ (S.aux _).1.pos hdvd hA hded hR
  · exact GlobalTheory.T.pushforward_polarisationBundle_invertible_on_model L1 L2 L3 E H D i.l _ _ _ _ _ _ (S.Y p W hp hW i).oF _ _ (ofModel (S.Y p W hp hW i)) hded
      hgood.2.2
  · obtain ⟨U, hU, hσ⟩ := GlobalTheory.torsion_section_extends_abLocus E H D i.l _ i.c _ _ (S.Y p W hp hW i) hded hgood.1
    exact ⟨U, hU, fun a n hn => ⟨hσ _ n (hunit n hn), hσ _ n (hunit n hn)⟩⟩
  · intro V K _ _ _ _ _ _ _
    exact GlobalTheory.goodRedExt_of_isDiscreteValuationRing hext E H D i.l _ i.c _ _ _ V K
  · intro V C _ _ _ _ _ _ _ hV _
    exact GlobalTheory.GoodRedUnitBall.goodRedExt_unitBall hext E H D Xo _ _ _ l₀ _ i.l i.c _ _ _ hR V C hV

end GlobalTheory.Models
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.localModel_oneModel_and_splitFibres : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ (S : System Xo) p W hp hW (i : Idx H p), (S.Y p W hp hW i).LevelStructureConditions p ∧ (S.Y p W hp hW i).SplitFibres := by
  first | exact @GlobalTheory.Models.System.levelStructureConditions_and_splitFibres | exact GlobalTheory.Models.System.levelStructureConditions_and_splitFibres | (intros; apply GlobalTheory.Models.System.levelStructureConditions_and_splitFibres <;> assumption)

end
end
