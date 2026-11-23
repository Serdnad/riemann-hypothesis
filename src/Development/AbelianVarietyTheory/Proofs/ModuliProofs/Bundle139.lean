module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle099
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle009
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle050
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle135
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyHomNearGoodPrimeOfGraphs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle134

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.RankZero

section
variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)

theorem top_le_wchart (ψ : Fin 0 → (Y ⟶ X)) (j : Fin 0 → L.ι) : (⊤ : Y.Opens) ≤ LB.wchart L ψ j :=
  fun _ _ => Set.mem_iInter.2 fun k => k.elim0

theorem exists_fn (hL : L.IsLB) (hε : ∀ k, ε k = 0) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ f : Γ(Y, ⊤), ∀ y J, Good L y J → sval s (𝟙 Y) y J = gs (𝟙 Y) y ⊤ f := by
  have hF : FormEq φ ε (Fin.elim0 : Fin 0 → (Y ⟶ X)) (Fin.elim0 : Fin 0 → ℤ) := by
    intro U _ h
    simp [hε]
  obtain ⟨s', hs'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sec hL hF s
  refine ⟨(Y.presheaf.map (homOfLE (top_le_wchart (L := L) Fin.elim0 Fin.elim0)).op).hom (s'.f Fin.elim0),
    fun y J hJ => ?_⟩
  rw [← hs' Y (𝟙 Y) y J hJ, sval_of s' (𝟙 Y) y J Fin.elim0 (fun k => k.elim0)]
  exact (gs_res (𝟙 Y) y (top_le_wchart (L := L) Fin.elim0 Fin.elim0) trivial _).symm

theorem exists_sec_of_fn (hε : ∀ k, ε k = 0) (f : Γ(Y, ⊤)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ y J, Good L y J → sval s (𝟙 Y) y J = gs (𝟙 Y) y ⊤ f := by
  have hle : ∀ j : K → L.ι, LB.wchart L φ j ≤ ⊤ := fun _ => le_top
  have h1 : ∀ y j j', trF (L := L) φ ε (𝟙 Y) y j j' = 1 := fun y j j' => by simp [trF, hε]
  refine ⟨⟨fun j => (Y.presheaf.map (homOfLE (hle j)).op).hom f, fun (j j' : K → L.ι) => fn_ext fun y hy => ?_⟩,
    fun y J hJ => (gs_res (𝟙 Y) y (hle _) (hJ.mem φ (𝟙 Y)) f)⟩
  have hg : gm (𝟙 Y) y ((L.LinComb φ ε).U j ⊓ (L.LinComb φ ε).U j') ((L.LinComb φ ε).g j j') = 1 :=
    (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2).trans (h1 y j j')
  rw [gs_mul (𝟙 Y) y _ hy, gs_unit (𝟙 Y) y _ hy, hg, Units.val_one, _root_.one_mul]
  exact ((gs_res (𝟙 Y) y inf_le_left hy _).trans (gs_res (𝟙 Y) y (hle j) hy.1 f)).trans
    ((gs_res (𝟙 Y) y inf_le_right hy _).trans (gs_res (𝟙 Y) y (hle j') hy.2 f)).symm

end

theorem eq_one_of_existsUnique {Γ : Type} [CommRing Γ] [Nontrivial Γ] {n : ℕ} (β : Fin n → Γ)
    (h : ∀ a : Γ, ∃! c : Fin n → Γ, a = ∑ i, c i * β i) : n = 1 := by
  let F : (Fin n → Γ) →ₗ[Γ] Γ :=
    { toFun := fun c => ∑ i, c i * β i
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by simp [_root_.mul_assoc] }
  have hF : ∀ c, F c = ∑ i, c i * β i := fun _ => rfl
  have hb : Function.Bijective F := by
    refine ⟨fun c c' hcc => ?_, fun a => ?_⟩
    · obtain ⟨d, -, hd⟩ := h (F c)
      exact (hd c (hF c)).trans (hd c' (hcc.trans (hF c'))).symm
    · obtain ⟨c, hc, -⟩ := h a
      exact ⟨c, (hF c).trans hc.symm⟩
  have e := (LinearEquiv.ofBijective F hb).finrank_eq
  simpa using e

theorem eq_one_of_bijective {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (hL : L.IsLB) (T : Over Z)
    [Nontrivial Γ(T.left, ⊤)] (hb : Function.Bijective (fst T G).left.appTop.hom) {n : ℕ}
    (b : Fin n → LB.Sec (Out.LPow G L ((0 : ℕ) : ℤ) T)) (H : GlobalTheory.LN.BasisAlong G L 0 (𝟙 _) b) : n = 1 := by
  have hpull : ∀ (x : Γ(T.left, ⊤)) (y : (T ⊗ G).left),
      gs (fst T G).left y ⊤ x = gs (𝟙 _) y ⊤ ((fst T G).left.appTop.hom x) := fun x y => by
    have e := gs_pull (𝟙 _) (fst T G).left y ⊤ trivial x
    rw [Category.id_comp] at e
    exact e.symm
  have hρ : ∀ y : (T ⊗ G).left, ∃ ρ : Γ((T ⊗ G).left, ⊤) →+* (T ⊗ G).left.presheaf.stalk y,
      ∀ a, gs (𝟙 _) y ⊤ a = ρ a := fun y =>
    ⟨((T ⊗ G).left.presheaf.germ ((𝟙 (T ⊗ G).left) ⁻¹ᵁ ⊤) y trivial).hom.comp (Scheme.Hom.app (𝟙 (T ⊗ G).left) ⊤).hom,
      fun a => gs_eq _ y ⊤ trivial a⟩
  choose β' hβ' using fun i => exists_fn (L := L) (fun _ : Fin 1 => (snd T G).left) (fun _ => ((0 : ℕ) : ℤ)) hL
    (fun _ => rfl) (b i)
  choose β hβ using fun i => hb.2 (β' i)
  have hR : ∀ (c : Fin n → Γ(T.left, ⊤)) (z : (T ⊗ G).left) (J : ((T ⊗ G).left ⟶ G.left) → L.ι), Good L z J →
      ∑ i, gs (fst T G).left z ⊤ (c i) * sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left)
        (ε := fun _ => ((0 : ℕ) : ℤ)) (b i) (𝟙 T ▷ G).left z J
        = gs (𝟙 _) z ⊤ ((fst T G).left.appTop.hom (∑ i, c i * β i)) := by
    intro c z J hJ
    obtain ⟨ρ, hρz⟩ := hρ z
    rw [MonoidalCategory.id_whiskerRight, Over.id_left]

    simp only [hβ' _ z J hJ, hpull, hρz, map_sum, map_mul, hβ]
  have hiff : ∀ (a : Γ(T.left, ⊤)) (c : Fin n → Γ(T.left, ⊤)) (s : LB.Sec (Out.LPow G L ((0 : ℕ) : ℤ) T)),
      (∀ y J, Good L y J → sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => ((0 : ℕ) : ℤ))
        s (𝟙 _) y J = gs (𝟙 _) y ⊤ ((fst T G).left.appTop.hom a)) →
      (GlobalTheory.LN.Lin G L 0 (𝟙 T) b c s ↔ a = ∑ i, c i * β i) := by
    intro a c s hs
    constructor
    · intro hl
      apply hb.1
      apply fn_ext
      intro z _
      obtain ⟨J, hJ, -⟩ := exists_good L hL z (Fin.elim0 : Fin 0 → ((T ⊗ G).left ⟶ G.left)) Fin.elim0
        (fun a => a.elim0) (fun k => k.elim0)
      rw [← hs z J hJ, hl z J hJ, hR c z J hJ]
    · rintro rfl z J hJ
      rw [hs z J hJ, hR c z J hJ]
  refine eq_one_of_existsUnique β (fun a => ?_)
  obtain ⟨s, hs⟩ := exists_sec_of_fn (L := L) (fun _ : Fin 1 => (snd T G).left) (fun _ => ((0 : ℕ) : ℤ))
    (fun _ => rfl) ((fst T G).left.appTop.hom a)
  obtain ⟨c, hc, hcu⟩ := H s
  exact ⟨c, (hiff a c s hs).1 hc, fun c' hc' => hcu c' ((hiff a c' s hs).2 hc')⟩

end GlobalTheory.RankZero

theorem GlobalTheory.basisAlong_zero_card : Out.GlobalFnsSt → ∀ (R : Type) [CommRing R] [Nontrivial R] (P : Out.PolAV (Sp R)) (n : ℕ) (b : Fin n → LB.Sec (Out.LPow P.A P.L ((0 : ℕ) : ℤ) (Over.mk (𝟙 (Sp R))))), GlobalTheory.LN.BasisAlong P.A P.L 0 (𝟙 _) b → n = 1 := by
  intro hG R _ _ P n b hB
  have : Nontrivial Γ((Over.mk (𝟙 (Sp R))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  refine GlobalTheory.RankZero.eq_one_of_bijective P.A P.L P.isLB (Over.mk (𝟙 (Sp R))) ?_ b hB
  have : IsIso (snd (Over.mk (𝟙 (Sp R))) P.A) := by
    change IsIso (snd (𝟙_ (Over (Sp R))) P.A)
    rw [← CartesianMonoidalCategory.leftUnitor_hom]
    infer_instance
  have : IsIso (snd (Over.mk (𝟙 (Sp R))) P.A).left :=
    (inferInstance : IsIso ((Over.forget _).map (snd (Over.mk (𝟙 (Sp R))) P.A)))
  have e1 : (fst (Over.mk (𝟙 (Sp R))) P.A).left = (snd (Over.mk (𝟙 (Sp R))) P.A).left ≫ P.A.hom := by
    have h1 : (fst (Over.mk (𝟙 (Sp R))) P.A).left ≫ 𝟙 (Sp R) = _ := Over.w (fst (Over.mk (𝟙 (Sp R))) P.A)
    have h2 := Over.w (snd (Over.mk (𝟙 (Sp R))) P.A)
    exact (Category.comp_id _).symm.trans (h1.trans h2.symm)
  have hc : ((snd (Over.mk (𝟙 (Sp R))) P.A).left ≫ P.A.hom).appTop =
      P.A.hom.appTop ≫ (snd (Over.mk (𝟙 (Sp R))) P.A).left.appTop := by
    simp
  have : IsIso (snd (Over.mk (𝟙 (Sp R))) P.A).left.appTop := by
    exact (inferInstance : IsIso ((snd (Over.mk (𝟙 (Sp R))) P.A).left.app ⊤))
  rw [e1, hc, CommRingCat.hom_comp, RingHom.coe_comp]
  exact Function.Bijective.comp (asIso (snd (Over.mk (𝟙 (Sp R))) P.A).left.appTop).commRingCatIsoToRingEquiv.bijective
    (@hG _ P.A P.grp P.isAb)

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ModelSum

theorem exists_pull_LPow_sec {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (hL : L.IsLB) (N : ℕ) {T T' : Over Z}
    (h : T' ⟶ T) (b : LB.Sec (Out.LPow G L (N : ℤ) T)) :
    ∃ b' : LB.Sec (Out.LPow G L (N : ℤ) T'), ∀ (Y : Scheme.{0}) (r : Y ⟶ (T' ⊗ G).left) (z : Y) (J), Good L z J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) b' r z J =
        sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) b (r ≫ (h ▷ G).left) z J := by
  have hu : (LB.oneGen L (Y := (T' ⊗ G).left)).IsGen := by
    intro (i : PEmpty → L.ι) (j : PEmpty → L.ι)
    simp [LB.oneGen, LB.LinComb, res]
    ext
    erw [Units.val_mul, Units.coe_map, Units.coe_map, Units.val_one, _root_.one_mul, map_one, map_one]
  have hf : FormEq (Sum.elim (fun _ : Fin 1 => (h ▷ G).left ≫ (snd T G).left)
      (PEmpty.elim : PEmpty → ((T' ⊗ G).left ⟶ G.left))) (Sum.elim (fun _ => (N : ℤ)) PEmpty.elim)
      (fun _ : Fin 1 => (snd T' G).left) (fun _ => (N : ℤ)) := by
    intro U _ f
    simp [Fintype.prod_sum_type]
  obtain ⟨b', hb'⟩ := exists_sec hL hf
    (pullMulSec (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) b (h ▷ G).left
      (LB.oneGen L (Y := (T' ⊗ G).left)) hu)
  refine ⟨b', fun Y r z J hJ => (hb' Y r z J hJ).trans ((sval_pullMulSec _ _ _ hu r z hJ).trans ?_)⟩
  rw [val_one, Units.val_one, _root_.mul_one]

theorem basisAlong_id_of_basisAlong : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N n : ℕ) (T T' : Over Z) (h : T' ⟶ T) (b : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T)), L.IsLB → GlobalTheory.LN.BasisAlong G L N h b → ∃ b' : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T'), GlobalTheory.LN.BasisAlong G L N (𝟙 T') b' := by
  intro Z G L N n T T' h b hL hB
  choose b' hb' using fun i => exists_pull_LPow_sec G L hL N h (b i)
  have key : ∀ s c, GlobalTheory.LN.Lin G L N (𝟙 T') b' c s ↔ GlobalTheory.LN.Lin G L N h b c s := by
    intro s c
    have e : ∀ i (z : (T' ⊗ G).left) J, Good L z J →
        sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) (b' i) ((𝟙 T') ▷ G).left z J =
          sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) (b i) (h ▷ G).left z J := by
      intro i z J hJ
      rw [hb' i _ _ z J hJ]
      simp
    unfold GlobalTheory.LN.Lin
    refine forall_congr' fun z => forall_congr' fun J => imp_congr_right fun hJ => ?_
    simp only [e _ z J hJ]
  unfold GlobalTheory.LN.BasisAlong at hB ⊢
  refine ⟨b', fun s => ?_⟩
  obtain ⟨c, hc, hu⟩ := hB s
  exact ⟨c, (key s c).2 hc, fun c' hc' => hu c' ((key s c').1 hc')⟩

end GlobalTheory.ModelSum
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaDvr

theorem app_eq_zero_of_not_mem {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (G : Over (Sp V)) [Smooth G.hom]
    {U : G.left.Opens} (a : Γ(G.left, U))
    (h : ∀ x ∈ G.left.basicOpen a, G.hom x ≠ IsLocalRing.closedPoint V) :
    ((fstG (IsLocalRing.maximalIdeal V) 0 G).left.app _).hom a = 0 := by

  have hk : _root_.IsReduced (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := by
    rw [zero_add, pow_one]
    infer_instance
  have : IsReduced (pullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0))

  have hpt : ∀ y : ↥(pullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)),
      G.hom (pullback.fst G.hom (thick V (IsLocalRing.maximalIdeal V) 0) y) = IsLocalRing.closedPoint V := by
    intro y
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    apply PrimeSpectrum.ext
    refine le_antisymm (IsLocalRing.le_maximalIdeal ?_) ?_
    · exact (Ideal.ne_top_iff_one _).mpr (PrimeSpectrum.isPrime _).one_notMem
    · intro r hr
      have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1)) r = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [zero_add, pow_one]; exact hr)
      change Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1)) r ∈
        ((pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) y).asIdeal
      rw [h0]
      exact Ideal.zero_mem _

  have hbot : (fstG (IsLocalRing.maximalIdeal V) 0 G).left ⁻¹ᵁ G.left.basicOpen a = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => (h _ hy (hpt y)).elim
  rw [Scheme.preimage_basicOpen] at hbot
  exact (@basicOpen_eq_bot_iff _ this _ _).mp hbot

private lemma secIsMul_trans' {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    {L : LB Y} {a b : R} {σ τ τ' : LB.Sec L} (h : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p a σ τ)
    (h' : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p b τ τ') : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p (a * b) σ τ' := by
  intro k
  rw [h k, h' k, ← _root_.mul_assoc]
  congr 1
  simp only [resTop, scal, map_mul]

private lemma gs_id_eq_germ_moduli {X : Scheme.{0}} (U : X.Opens) (a : Γ(X, U)) (z : X) (hz : z ∈ U) :
    gs (𝟙 X) z U a = (X.presheaf.germ U z hz).hom a := by
  unfold gs
  rw [dite_eq_left (show (𝟙 X) z ∈ U from hz)]
  rfl

theorem exists_sec_unit_closed_fibre (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V))
    [GrpObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom] (N : LB G.left)
    (hN : N.IsLB) (s : LB.Sec (N.pull (pullback.fst G.hom (jK V)))) (j) (hj : s.f j ≠ 0) :
    ∃ (θ : LB.Sec N) (k : N.ι), ∃ x ∈ G.left.basicOpen (θ.f k), G.hom x = IsLocalRing.closedPoint V := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hflat : (algebraMap V (FractionRing V)).Flat := by
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (FractionRing V) (nonZeroDivisors V))
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  have hpb : IsPullback (pullback.fst G.hom (jK V)) (pullback.snd G.hom (jK V)) G.hom
      (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) := IsPullback.of_hasPullback _ _

  obtain ⟨n, c, u, hu⟩ := GlobalTheory.FlatSec.exists_comb_of_flat V (FractionRing V) _ hflat G.left G.hom _
    (pullback.fst G.hom (jK V)) _ hpb N hN s
  have hne : ∃ i k, (u i).f k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hj
    apply TopCat.Presheaf.section_ext (pullback G.hom (jK V)).sheaf
    intro z hz
    have hj' : j = fun _ => j PUnit.unit := funext fun x => by cases x; rfl
    have hz' : pullback.fst G.hom (jK V) z ∈ N.U (j PUnit.unit) := by
      rw [hj'] at hz
      simpa [LB.pull, LB.LinComb, LB.wchart] using hz
    have h1 := hu z (j PUnit.unit) hz'
    rw [← hj'] at h1
    rw [gs_id_eq_germ_moduli _ _ z hz] at h1
    refine Eq.trans ?_ (map_zero _).symm
    change ((pullback G.hom (jK V)).presheaf.germ _ z hz).hom (s.f j) = 0
    rw [h1]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hcon i (j PUnit.unit)]
    simp [gs]
  obtain ⟨i, k₀, hk₀⟩ := hne
  set θ₀ := u i

  have hjac : IsLocalRing.maximalIdeal V ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hex : ∃ m, ∃ k, ((fstG (IsLocalRing.maximalIdeal V) m G).left.app _).hom (θ₀.f k) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hk₀ ((GlobalTheory.sec_eq_zero_and_hom_eq_of_thickenings V _ hjac G).1 N hN θ₀ hcon k₀)
  classical

  have hunit : ∀ (θ : LB.Sec N) (k : N.ι), ((fstG (IsLocalRing.maximalIdeal V) 0 G).left.app _).hom (θ.f k) ≠ 0 →
      ∃ x ∈ G.left.basicOpen (θ.f k), G.hom x = IsLocalRing.closedPoint V := by
    intro θ k hθ
    by_contra hcon
    push Not at hcon
    exact hθ (app_eq_zero_of_not_mem G (θ.f k) hcon)

  obtain ⟨k₁, hk₁⟩ := Nat.find_spec hex
  rcases hm : Nat.find hex with _ | e
  · rw [hm] at hk₁
    obtain ⟨x, hx, hxc⟩ := hunit θ₀ k₁ hk₁
    exact ⟨θ₀, k₁, x, hx, hxc⟩
  · have hlt : ¬ ∃ k, ((fstG (IsLocalRing.maximalIdeal V) e G).left.app _).hom (θ₀.f k) ≠ 0 :=
      Nat.find_min hex (by omega)
    push Not at hlt
    obtain ⟨τ, hτ⟩ := (GlobalTheory.ThickDiv.main V ϖ hϖ G N θ₀ e).1 hlt
    have hτ0 : ∃ k, ((fstG (IsLocalRing.maximalIdeal V) 0 G).left.app _).hom (τ.f k) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨τ', hτ'⟩ := (GlobalTheory.ThickDiv.main V ϖ hϖ G N τ 0).1 hcon
      have h2 := secIsMul_trans' G.hom hτ hτ'
      rw [← pow_add] at h2
      have h3 := (GlobalTheory.ThickDiv.main V ϖ hϖ G N θ₀ (e + 1)).2 ⟨τ', h2⟩
      rw [hm] at hk₁
      exact hk₁ (h3 k₁)
    obtain ⟨k, hk⟩ := hτ0
    obtain ⟨x, hx, hxc⟩ := hunit τ k hk
    exact ⟨τ, k, x, hx, hxc⟩

theorem thetaNZ_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (t : SAB H (Sp V)), GlobalTheory.LN.PolAt t (jK V) → GlobalTheory.LN.ThetaNZ t.G t.PP.L := by
  intro hL hL2 E _ _ _ H V _ _ _ t ht
  obtain ⟨A, oA, gen, -, hiso, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt hL hL2 E H V t ht
  have hsa := t.4
  have : Smooth t.G.hom := hsa.2
  have : IsSeparated t.G.hom := hsa.3
  have : QuasiCompact t.G.hom := hsa.4
  have : GeometricallyConnected t.G.hom := hsa.5
  have hLt : t.PP.L.IsLB := t.PP.3

  have hP := GlobalTheory.PushInv.pushInvertible_any hL2.1 hL.1 _ A
  obtain ⟨W, hxW, θ, hθ, -, hnz⟩ := hP (IsLocalRing.closedPoint (FractionRing V))
  obtain ⟨g, i, -, hg⟩ := hnz _ hxW
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  have hO : ⊤ ≤ gen.hom.left ⁻¹ᵁ (A.A.hom ⁻¹ᵁ W) := by
    intro y _
    change A.A.hom (gen.hom.left y) ∈ W
    rwa [Subsingleton.elim (A.A.hom (gen.hom.left y)) (IsLocalRing.closedPoint (FractionRing V))]
  obtain ⟨θ', hθ'⟩ := GlobalTheory.ThetaLocal.exists_sec_pull A.isLB (LB.isLB_pull hLt _) gen.hom.left w hw hO θ hθ
  have hgy : gen.hom.left (gen.inv.left g) = g := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, gen.inv_hom_id, Over.id_left]
    rfl
  obtain ⟨k, hk⟩ := hθ' (gen.inv.left g) i (by rwa [hgy])
  have hk0 : θ'.f k ≠ 0 := by
    intro h0
    rw [h0, Scheme.basicOpen_zero] at hk
    exact hk

  obtain ⟨σ, l, x, hx, hxc⟩ := exists_sec_unit_closed_fibre V t.G t.PP.L hLt θ' k hk0

  refine ⟨σ, fun y => ?_⟩
  have hy : y ⤳ t.G.hom x := hxc ▸ IsLocalRing.specializes_closedPoint y
  obtain ⟨x', hx', hx'y⟩ := Flat.generalizingMap t.G.hom hy
  exact ⟨x', l, hx'y, hx'.mem_open (t.G.left.basicOpen (σ.f l)).isOpen hx⟩

end GlobalTheory.ThetaDvr
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN.SecRank

theorem card_eq_of_basisAlong {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (hL : L.IsLB) (N : ℕ)
    {T₁ T₂ T' : Over S} [Nontrivial Γ(T'.left, ⊤)] (h₁ : T' ⟶ T₁) (h₂ : T' ⟶ T₂) {n m : ℕ}
    {a : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T₁)} {b : Fin m → LB.Sec (Out.LPow G L (N : ℤ) T₂)}
    (ha : BasisAlong G L N h₁ a) (hb : BasisAlong G L N h₂ b) : n = m := by
  choose a' ha' _ using fun i => PolFrames.exists_pullSec G L N h₁ (a i)
  choose b' hb' _ using fun i => PolFrames.exists_pullSec G L N h₂ (b i)
  obtain ⟨l₁, s₁⟩ := (PolFrames.basisAlong_iff G L N h₁ hL ha').1 ha
  obtain ⟨l₂, s₂⟩ := (PolFrames.basisAlong_iff G L N h₂ hL hb').1 hb
  have e₁ := Module.finrank_eq_card_basis (Module.Basis.mk l₁ s₁.ge)
  have e₂ := Module.finrank_eq_card_basis (Module.Basis.mk l₂ s₂.ge)
  simpa using e₁.symm.trans e₂

theorem card_basis_eq_pow : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : Out.PolAV (Sp R)) (N n : ℕ) (b : Fin n → LB.Sec (Out.LPow P.A P.L (N : ℤ) (Over.mk (𝟙 (Sp R))))), 1 ≤ N → GlobalTheory.LN.BasisAlong P.A P.L N (𝟙 _) b → n = N ^ P.g := by
  intro _ hL R _ _ P N n b hN hb
  obtain ⟨V, hV, c, hc⟩ := hL.secBaseChangeAny (Sp R) P N hN (IsLocalRing.closedPoint R)
  have hV' : V = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    exact (IsLocalRing.specializes_closedPoint x).mem_open V.isOpen hV
  subst hV'
  let χ : Sp R ⟶ (⊤ : (Sp R).Opens).toScheme := (Sp R).topIso.inv
  choose c' hc' _ using fun i => PolFrames.exists_pullSec P.A P.L N (Out.homAt χ) (c i)
  have H := (PolFrames.basisAlong_iff P.A P.L N (Out.homAt χ) P.isLB hc').2 (hc R χ c' hc')
  have : Nontrivial Γ((Over.mk (𝟙 (Sp R)) : Over (Sp R)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have key : ∀ (f : Sp R ⟶ Sp R) (hf : f = 𝟙 _) (T : Over (Sp R)) (h : Over.mk f ⟶ T)
      (d : Fin (N ^ P.g) → LB.Sec (Out.LPow P.A P.L (N : ℤ) T)), BasisAlong P.A P.L N h d → n = N ^ P.g := by
    rintro _ rfl T h d hd
    exact card_eq_of_basisAlong P.A P.L P.isLB N _ h hb hd
  refine key (Out.baseAt χ).hom ?_ _ (Out.homAt χ) c H
  exact (congrArg (χ ≫ ·) (Category.comp_id (⊤ : (Sp R).Opens).ι)).trans (Sp R).toIso_inv_ι

end GlobalTheory.LN.SecRank
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) Mat κ (w w' : J) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s) (t' : TObj g k J b s'), TMap t' t f → (t.Shape Mat κ → t'.Shape Mat κ) ∧ (t.Prim w w' → t'.Prim w w') ∧ ∀ (K : Type) [Field K] (e : S = Sp K), IsAffine S' → Nonempty S' → (t'.Shape Mat κ → t.Shape Mat κ) ∧ (IsIntegral S' → t'.Prim w w' → t.Prim w w') := by
  first | exact @GlobalTheory.shape_prim_pull_and_descend | exact GlobalTheory.shape_prim_pull_and_descend | (intros; apply GlobalTheory.shape_prim_pull_and_descend <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.nonempty_thetaCoordinateSchemeData : ∀ (o : Type) [CommRing o] [IsDedekindDomain o] (g n N' : ℕ) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)), 0 < N' → I.IsRadical → (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → (∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ I → F ∈ I) → Nonempty (MMPre n N' I) := by
  first | exact @GlobalTheory.ZM.nonempty_MMPre | exact GlobalTheory.ZM.nonempty_MMPre | (intros; apply GlobalTheory.ZM.nonempty_MMPre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_familyHom_near_goodPrime_of_graphs : ∀ (R σ₁ σ₂ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ₁] [Finite σ₂] [Finite Hh] (Z₁ Z₂ : Over (Sp R)) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (p₁ : Hh → σ₁ → R) (p₂ : Hh → σ₂ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z₁.hom (spMap x) ⟶ Z₂.left) → Prop), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsProper Z₁.hom → IsProper Z₂.hom → Smooth Z₁.hom → (∀ (K : Type) [Field K] (x : R →+* K) φ, G K x φ → φ ≫ Z₂.hom = pullback.snd _ _ ≫ spMap x ∧ CutBy (graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ φ) Q d (fun h i => x (p₁ h i.1 * p₂ h i.2))) → DenseP {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (φ : _), RingHom.ker x = q ∧ G K x φ} → ∀ (K₀ : Type) [Field K₀] (x₀ : R →+* K₀) φ₀, G K₀ x₀ φ₀ → ∃ (f : R) (F : pullback Z₁.hom (spMap (algebraMap R (Localization.Away f))) ⟶ Z₂.left), x₀ f ≠ 0 ∧ F ≫ Z₂.hom = pullback.fst _ _ ≫ Z₁.hom ∧ ∀ (K : Type) [Field K] (x : R →+* K) φ, G K x φ → ∀ io : pullback Z₁.hom (spMap x) ⟶ pullback Z₁.hom (spMap (algebraMap R (Localization.Away f))), io ≫ pullback.fst _ _ = pullback.fst _ _ → φ = io ≫ F := by
  first | exact @GlobalTheory.ZM.LocalGraph.exists_hom_near_of_graphs | exact GlobalTheory.ZM.LocalGraph.exists_hom_near_of_graphs | (intros; apply GlobalTheory.ZM.LocalGraph.exists_hom_near_of_graphs <;> assumption)
end
