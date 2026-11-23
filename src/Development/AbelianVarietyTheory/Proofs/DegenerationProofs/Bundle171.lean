module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle110
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle009
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle017
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle082
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle106
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsOfDouble
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section

namespace GlobalTheory.PsiBaseChange

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R} {D' : DegPre V}
  {β : D'.P.A.left ⟶ D.P.A.left} {v : LB.Iso D'.P.L (D.P.L.pull β)} {xe : D'.X ≃+ D.X}

theorem secCmp_val {f : ∀ α, SecBT D (𝟙_ _) 1 α} {f' : ∀ α, SecBT D' (𝟙_ _) 1 α} (h : SecCmp D D' β v xe f f')
    (α : D'.X) {T : Over (Spec (CommRingCat.of V))} (y : T ⟶ D'.P.A) (r : T.left ⟶ (𝟙_ _ ⊗ D.P.A).left)
    (hr : r ≫ (snd _ D.P.A).left = y.left ≫ β) (z : T.left) {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (Ω : (T.left ⟶ D'.P.A.left) → (T.left.presheaf.stalk z)ˣ) (hΩ : ∀ q, Ω q = gw v q z (J (q ≫ β)) (J' q)) :
    sval (f (xe α)) r z J = (Ω (y * cT D' T α).left * (Ω (cT D' T α).left)⁻¹ * Ω (1 : T ⟶ D'.P.A).left).val *
      sval (f' α) (lift (toUnit T) y).left z J' := by
  have a : (lift (toUnit T) y).left ≫ (snd _ D'.P.A).left = y.left := congrArg (fun q => q.left) (lift_snd (toUnit T) y)
  refine (h α _ (lift (toUnit T) y).left r (by rw [hr, ← Category.assoc, a]) z J J' hJ hJ').trans ?_
  refine congrArg (fun u : (T.left.presheaf.stalk z)ˣ => u.val * sval (f' α) (lift (toUnit T) y).left z J') ?_
  simp only [← Category.assoc, ← hΩ, PsiExists.comp_famφT, lift_snd]
  simp [Fin.prod_univ_four, DegPre.famε]

theorem val_psi (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β)
    (hc : ∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) (hrig : RigCmp φ D D' β v)
    {f : ∀ α, SecBT D (𝟙_ _) 1 α} {f' : ∀ α, SecBT D' (𝟙_ _) 1 α} (hf : SecCmp D D' β v xe f f')
    (h : PsiRel D (𝟙_ _) f) (h' : PsiRel D' (𝟙_ _) f') {gam : (TK V).left ⟶ (TK R).left}
    (hg : gam ≫ jK R = jK V ≫ spMap φ) (x : D'.X) {T : Over (Spec (CommRingCat.of V))} [IsIntegral T.left]
    (κ : T ⟶ TK V) (p : T ⟶ D'.P.A) (z : T.left) {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (ne : sval (f' 0) (lift (toUnit T) p).left z J' ≠ 0) :
    val (D.psi (xe x)) (κ.left ≫ gam) z J =
      (gw v (κ.left ≫ D'.xK x) z (J ((κ.left ≫ D'.xK x) ≫ β)) (J' (κ.left ≫ D'.xK x)))⁻¹ *
        val (D'.psi x) κ.left z J' := by
  let T₀ : Over (Spec (CommRingCat.of R)) := Over.mk (T.hom ≫ spMap φ)
  let κ₀ : T₀ ⟶ TK R := Over.homMk (κ.left ≫ gam) (by
    have w : κ.left ≫ jK V = T.hom := Over.w κ
    show (κ.left ≫ gam) ≫ jK R = T.hom ≫ spMap φ
    rw [Category.assoc, hg, ← Category.assoc, w])
  let b : (T ⟶ D'.P.A) →* (T₀ ⟶ D.P.A) := pushHom gp T
  have bc : b (cT D' T x) = cT D T₀ (xe x) := Over.OverMorphism.ext (by
    show (T.hom ≫ (D'.c x).left) ≫ β = (T.hom ≫ spMap φ) ≫ (D.c (xe x)).left
    rw [Category.assoc, hc, Category.assoc])
  let Ω : (T.left ⟶ D'.P.A.left) → (T.left.presheaf.stalk z)ˣ := fun q => gw v q z (J (q ≫ β)) (J' q)
  let y : T ⟶ D'.P.A := p * (cT D' T x)⁻¹
  have hy : y * cT D' T x = p := inv_mul_cancel_right _ _
  have hyb : b y * cT D T₀ (xe x) = b p := by rw [← bc, ← map_mul, hy]
  have sn : ∀ q : T ⟶ D'.P.A, (lift (toUnit T₀) (b q)).left ≫ (snd _ D.P.A).left = q.left ≫ β := fun q =>
    congrArg (fun q => q.left) (lift_snd (toUnit T₀) (b q))
  have e₁ := h (xe x) T₀ (toUnit _) κ₀ (b y) z J hJ
  have e₂ := h' x T (toUnit _) κ y z J' hJ'
  have e₃ := secCmp_val hf x y _ (sn y) z hJ hJ' Ω fun _ => rfl
  have e₄ := secCmp_val hf 0 p _ (sn p) z hJ hJ' Ω fun _ => rfl
  have e₀ : ∀ α : D.X, α = 0 → sval (f α) (lift (toUnit T₀) (b p)).left z J =
      sval (f 0) (lift (toUnit T₀) (b p)).left z J := by
    rintro _ rfl; rfl
  rw [PsiExists.cT_zero, _root_.mul_one, inv_mul_cancel_right] at e₄
  rw [hy] at e₂ e₃
  rw [hyb] at e₁
  have e₅ : @id (T.left.presheaf.stalk z)ˣ (rigV D (T := T₀) z J) = Ω (1 : T ⟶ D'.P.A).left * rigV D' z J' := by
    have := CubTransport.val_pmaps (fun _ => (cubeMapOf gp).e_comm) hrig T.hom hJ hJ'
    rw [Fintype.prod_unique, zpow_one] at this
    exact this
  have e₆ : κ.left ≫ D'.xK x = (cT D' T x).left :=
    congrArg (fun q => q.left) (show κ ≫ cT D' _ x = cT D' _ x by rw [← Category.assoc, comp_toUnit])
  have e₇ := e₃.symm.trans (e₁.trans (congrArg₂ (· * ·)
    (congrArg (fun u : (T.left.presheaf.stalk z)ˣ => (val (D.psi (xe x)) (κ.left ≫ gam) z J * u).val) e₅)
    ((e₀ _ (map_zero xe)).symm.trans e₄)))
  rw [e₂] at e₇
  rw [e₆]
  refine PsiCompare.unit_cancel (a := Ω p.left) (c := Ω (1 : T ⟶ D'.P.A).left) (q := rigV D' z J') ne ?_
  rw [mul_comm (sval _ _ _ _)]
  exact e₇.trans (mul_comm _ _)

end GlobalTheory.PsiBaseChange

namespace GlobalTheory


open PsiBaseChange in
theorem psiCmp_of_secCmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ (f : ∀ α, SecBT D (𝟙_ _) 1 α) (f' : ∀ α, SecBT D' (𝟙_ _) 1 α), SecCmp D D' β v xe f f' → PsiRel D (𝟙_ _) f → PsiRel D' (𝟙_ _) f' → (∃ j, (f' 0).f j ≠ 0) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam := by
  intro R V _ _ _ _ φ D D' β v xe gp hv hc hrig f f' hf h h' hne gam hg x
  have hL := D.P.isLB
  have hL' := D'.P.isLB
  have pg := (isGen_iff v).1 hv
  have := D'.P.isAb.smooth
  have := D'.P.isAb.geomConnected
  have : IsIntegral (TF (R := V) (FractionRing V)).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of _)))
  have : IsIntegral (DegPre.BF D' (FractionRing V)).left :=
    isIntegral_tensor_left_of_smooth_grpObj _ D'.P.A (TF (R := V) (FractionRing V))
  have hx : D'.xK x ≫ β = gam ≫ D.xK (xe x) := by
    show (jK V ≫ (D'.c x).left) ≫ β = gam ≫ jK R ≫ (D.c (xe x)).left
    rw [Category.assoc, hc, ← Category.assoc gam, hg, Category.assoc]
  let T := DegPre.BF D' (FractionRing V)
  let π : T.left ⟶ (TK V).left := (fst (TF (R := V) (FractionRing V)) D'.P.A).left ≫ jFK (R := V) (FractionRing V)
  let κ : T ⟶ TK V := Over.homMk π
    ((Category.assoc _ _ _).trans (Over.w (fst (TF (R := V) (FractionRing V)) D'.P.A)))
  obtain ⟨s, hs⟩ := PsiExists.exists_pullB D' (FractionRing V) (toUnit _) 1 f'
  have hs0 := (pullB_ne_zero_iff V D' _ 1 f' s hs 0).2 hne
  have wl : toUnit (TF (R := V) (FractionRing V)) ▷ D'.P.A = lift (toUnit T) (snd _ D'.P.A) :=
    CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ((whiskerRight_snd _ _).trans (lift_snd _ _).symm)
  have key : ∀ (z : T.left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (D.psi (xe x)) (π ≫ gam) z J =
        (gw v (π ≫ D'.xK x) z (J ((π ≫ D'.xK x) ≫ β)) (J' (π ≫ D'.xK x)))⁻¹ * val (D'.psi x) π z J' :=
    fun z J J' hJ hJ' => val_psi gp hc hrig hf h h' hg x κ (snd _ D'.P.A) z hJ hJ' (by
      rw [← wl, ← hs 0 z J' hJ']
      exact (exists_ne_zero_iff_sval_ne_zero _ hJ').1 hs0)
  obtain ⟨t, ht, hv⟩ := exists_up pg hL hL' (φ' := fun _ : PUnit => D'.xK x) (D'.psi x) (D'.psi_gen x)
  have hcorr : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (D.psi (xe x)) (π ≫ gam))
      (LB.pullGen D.P.L _ _ t π) :=
    corr_of_val hL fun z J hJ => by
      choose J' hJ' using fun ψ : T.left ⟶ D'.P.A.left => exists_chart hL' (ψ z)
      rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp, key z J J' hJ hJ']
      refine Eq.trans ?_ (hv _ π z _ _ (Good.mem hJ _ π) (Good.mem hJ' _ π)).symm
      rw [pw, Fintype.prod_unique, zpow_neg_one, Category.assoc]; rfl
  have hz : (DegPre.zF D' (FractionRing V)).left ≫ π = 𝟙 (TK V).left := PsiCompare.zF_fst D'
  refine EvenPull.pmaps_of_section pg hL hL' gam (fun _ => hx) _ (D'.psi_gen x) _ (D.psi_gen _) (𝟙 _) (𝟙 _)
    (Category.id_comp _) (by rw [Scheme.Hom.id_appTop]; exact Function.surjective_id) fun y J J' hJ hJ' => ?_
  have := val_corr hJ hcorr (DegPre.zF D' (FractionRing V)).left
  rw [val_pull hJ, val_pull hJ, ← Category.assoc, hz] at this
  refine this.trans ((hv _ (𝟙 _) y _ _ (Good.mem hJ _ _) (Good.mem hJ' _ _)).trans ?_)
  refine congrArg₂ (· * ·) ?_ rfl
  rw [pw, Fintype.prod_unique, Fintype.prod_unique, Category.assoc]

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.PsiRing

theorem basis_prod_famφT_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (U : Type) [CommGroup U] (h : ((T ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ k, h (famφT D T 0 k) ^ DegPre.famε 1 k = h (snd T D.P.A).left := by
  have := D.P.isAb.comm
  rw [PsiExists.famφT_eq, PsiExists.cT_zero, _root_.mul_one]
  simp [Fin.prod_univ_four, DegPre.famε]

theorem exists_basis_fibNZ : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), ∃ th : SecBT D (𝟙_ _) 1 0, FibNZ (𝟙_ _ ⊗ D.P.A).hom th ∧ ∀ g : SecBT D (𝟙_ _) 1 0, ∃ b : R, Mult D th g b := by
  intro hT R _ _ _ D
  have := D.P.isAb.comm
  let T : Over (Spec (CommRingCat.of R)) := 𝟙_ _
  have e : translPt D.P.A (1 : T ⟶ D.P.A) = snd T D.P.A := by
    show (fst T D.P.A ≫ 1) * snd T D.P.A = _
    rw [MonObj.comp_one, _root_.one_mul]
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ D.P 1 le_rfl R (𝟙 _) (1 : T ⟶ D.P.A)
  change Fin (1 ^ D.P.g) → LB.Sec (twistLB D.P.A D.P.L 1 (1 : T ⟶ D.P.A)) at b
  change IsSecBasis (T := T) (A := D.P.A) _ b at hb
  have : Subsingleton (Fin (1 ^ D.P.g)) := by rw [one_pow]; infer_instance
  let i₀ : Fin (1 ^ D.P.g) := ⟨0, by simp⟩
  have H : FormEq (K := Fin 2) ![(snd T D.P.A).left, (translPt D.P.A (1 : T ⟶ D.P.A)).left] ![((1 : ℕ) : ℤ) - 1, 1]
      (famφT D T 0) (DegPre.famε 1) := fun U _ h => by
    rw [basis_prod_famφT_zero, e]
    simp [Fin.prod_univ_two]
  obtain ⟨th, hth⟩ := exists_sec D.P.isLB H (b i₀)
  have hf : (fst T D.P.A).left = (T ⊗ D.P.A).hom :=
    (Category.comp_id _).symm.trans (Over.w (fst T D.P.A))
  have key : ∀ g : SecBT D T 1 0, ∃ c : R, Mult D th g c := fun g => by
    obtain ⟨s, hs⟩ := exists_sec D.P.isLB (fun U _ h => (H U h).symm) g
    obtain ⟨c, hc, -⟩ := hb s
    have hc' := fun j => (hc j).trans (Fintype.sum_subsingleton _ i₀)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (c i₀), fun Z r z J hJ => ?_⟩
    refine (hs Z r z J hJ).symm.trans (Eq.trans ?_ (congrArg _ (hth Z r z J hJ).symm))
    refine (congrArg (gs r z _) (hc' _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·)
        ((gs_res r z le_top (hJ.mem _ r) _).trans ((gs_pull r (fst T D.P.A).left z ⊤ trivial _).trans ?_)) rfl))
    exact congrArg₂ (fun (q : Z ⟶ Spec (CommRingCat.of R)) (a : Γ(Spec (CommRingCat.of R), ⊤)) => gs q z ⊤ a)
      (congrArg (r ≫ ·) hf) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply (c i₀)).symm
  refine ⟨th, fun y => ?_, key⟩
  have hp : IsPullback (snd T D.P.A).left (T ⊗ D.P.A).hom D.P.A.hom (𝟙 _) := by
    rw [← hf]
    exact (IsPullback.of_hasPullback T.hom D.P.A.hom).flip
  obtain ⟨t, ht⟩ := KeyPow.exists_sec_fibre_ne_zero hT D.P hp
  obtain ⟨z, hz, hz'⟩ := ht y
  obtain ⟨g, hg⟩ := exists_sec D.P.isLB (K := PUnit) (φ := fun _ => (snd T D.P.A).left) (ε := fun _ => 1)
    (φ' := famφT D T 0) (ε' := DegPre.famε 1) (fun U _ h => by
      rw [basis_prod_famφT_zero]; simp) t
  obtain ⟨c, hc⟩ := key g
  choose J hJ using fun χ : (T ⊗ D.P.A).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  refine ⟨z, hz, (MulPullSec.mem_nonzeroLocus_iff th (𝟙 _) z hJ).2 ?_⟩
  have u := (MulPullSec.mem_nonzeroLocus_iff (K := PUnit) (φ := fun _ => (snd T D.P.A).left) (ε := fun _ => 1)
    t (𝟙 _) z hJ).1 hz'
  rw [← hg _ _ z J hJ, hc _ _ z J hJ] at u
  exact isUnit_of_mul_isUnit_right u

end GlobalTheory.PsiRing
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem tripleSt_of_laws : Laws → ThetaUnifAV → TripleSt := by
  intro laws hθ E _ _ _ H D La _ _ EF g ty P Hm hty hbij hadj hlin hinj hdisc hspan hH hpos him
  letI := H.starRing
  obtain ⟨D', e, -, -, hEF⟩ := PeriodDatum.exists_datum E H La EF D.p D.q g ty P Hm hty hbij hadj hlin hinj hdisc hspan
    hH hpos him
  let P' : D'.La →+ (Fin g → ℂ) := P.comp e.toAddEquiv.toAddMonoidHom
  have hP' : ∀ a, P' a = P (e a) := fun _ => rfl
  have hr : P'.range = P.range := by
    ext z
    exact ⟨fun ⟨a, h⟩ => ⟨e a, h⟩, fun ⟨a, h⟩ => ⟨e.symm a, by rw [hP', e.apply_symm_apply, h]⟩⟩
  have hper : IsPeriod D' ty P' := by
    refine ⟨fun a x i => ?_, hinj.comp e.injective, by rw [hr]; exact hdisc, ?_, Hm, hH, hpos, fun x y => ?_⟩
    · rw [hP', hP', map_smul, hlin]
    · rw [← hspan]; exact congrArg _ (congrArg SetLike.coe hr)
    · rw [hP', hP', him, hEF]
  obtain ⟨T, L, u, hA, hdim, hamp, hK, ht₁, ht₂, hker, hact, hW⟩ :=
    PeriodPoint.exists_triple laws Moduli.cube_of_isLB principalTorus_algebraic (exists_isMonHom_of_map_lattice hθ laws)
      (lbIso_cubeLB_of_pairing_adjoint laws) (PrimNorm.exists_primitive_normalisation laws.globalFns)
      (kTriv_of_descent laws) relAmple_finite_pow_iso D' ty P' hper
  let Q : PolAV (Sp ℂ) :=
    { A := T.G, isAb := hA, g := g, smoothDim := hdim, L := T.PP.L, isLB := T.PP.isLB,
      rigid := ⟨T.PP.rig, T.PP.rigGen⟩, sym := CechPic.sym_of_isSymmetric T.PP T.sym, ample := hamp, ktriv := hK }
  let oa : Q.OAct (𝓞 E) :=
    { T.act.toRingAct with
      rosati := fun a _ => ⟨⊤, trivial, by
        obtain ⟨r, hr⟩ := NormRos.exists_gen_rosati T.PP.isLB _ _ (T.adj a)
        exact ⟨_, DVR.pullGen_isGen _ _ _ _ hr _⟩⟩ }
  obtain ⟨v, hv, heig⟩ := exists_lieBasis_of_holUnif T.G L g u hA.smooth ht₁ ht₂
  have hdet : DetCond D T.act (spMap (RingHom.id ℂ)) H.rt0 :=
    PeriodPoint.detCond_of_eigenbasis lieMult_of_eigenbasis D T ty hty v hv
      (fun i a => heig _ _ (T.act.hom a) (hact a) i) (RingHom.id ℂ)
  rw [show spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) from Spec.map_id _] at hdet
  refine ⟨Q, oa, L, u, rfl, T.prim, hdet, ht₁, ht₂, fun z => hr ▸ hker z, hact, fun k a b c hk hc => ?_⟩
  have := hW k (e.symm a) (e.symm b) c hk (by rw [hEF, e.apply_symm_apply, e.apply_symm_apply, hc])
  rwa [hP', hP', e.apply_symm_apply, e.apply_symm_apply] at this

end GlobalTheory.Ex.Arch
end
end
