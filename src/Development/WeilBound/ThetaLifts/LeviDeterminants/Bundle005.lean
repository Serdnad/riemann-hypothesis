module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle003
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle004
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace PositivityTheory.ThKF0.Resc

section Gen

variable {R : Type} [CommRing R] {K : Type} [CommRing K] [Algebra R K] {c : K →ₐ[R] K}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem ug_smul {v : K} (hv : IsUnit v) (J : Matrix β β K) : UG c (v • J) = UG c J := by
  ext g
  change (g : Matrix β β K)ᵀ * (v • J) * (g : Matrix β β K).map c = v • J ↔
    (g : Matrix β β K)ᵀ * J * (g : Matrix β β K).map c = J
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact hv.smul_left_cancel

omit [Fintype β] [DecidableEq β] in
theorem dbl_smul (v : K) (J : Matrix β β K) : dbl (v • J) = v • dbl J := by
  ext (i | i) (j | j) <;> simp [dbl]

omit [DecidableEq α] [DecidableEq β] in
theorem symp_smul {ξ ξ' u v : K} (h : ξ = ξ' * u * v) (JA : Matrix α α K) (JB : Matrix β β K) (x y : Matrix α β K) :
    symp c ξ' (u • JA) (v • JB) x y = symp c ξ JA JB x y := by
  rw [symp, symp, h]
  congr 1
  simp only [hTens, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

variable [Invertible (2 : R)]

theorem isWeilB_resc {ξ ξ' u v : K} (h : ξ = ξ' * u * v) (hv : IsUnit v) {JA JA' : Matrix α α K} {JB JB' : Matrix β β K}
    (hA : JA' = u • JA) (hB : JB' = v • JB) {κ : Type} [Fintype κ] {C : TestClass R} {ψ : AddChar R ℂ}
    {d : Darboux (symp c ξ JA JB) κ} {χ : Kˣ →* Circle} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (hW : IsWeilB c C ψ ξ JA JB d χ om) :
    ∃ (d' : Darboux (symp c ξ' JA' JB') κ) (om' : UG c JB' →* Module.End ℂ ((κ → R) → ℂ)), d'.e = d.e ∧
      IsWeilB c C ψ ξ' JA' JB' d' χ om' ∧ ∀ g : UG c JB, ∃ g' : UG c JB', g'.1 = g.1 ∧ om' g' = om g := by
  subst hA hB
  obtain ⟨hS, dd, omd, hdd, hSd, hR, hbox⟩ := hW
  have hU : UG c (v • JB) = UG c JB := ug_smul hv JB
  have hUd : UG c (dbl (v • JB)) = UG c (dbl JB) := by rw [dbl_smul]; exact ug_smul hv _
  refine ⟨⟨d.e, fun w w' => (symp_smul h JA JB w w').trans (d.form w w')⟩, om.comp (Subgroup.inclusion hU.le), rfl,
    ⟨⟨fun g => hS.pres _, fun g => hS.impl (Subgroup.inclusion hU.le g), fun g => hS.adm _⟩,
      ⟨dd.e, fun w w' => by rw [dbl_smul]; exact (symp_smul h JA _ w w').trans (dd.form w w')⟩,
      omd.comp (Subgroup.inclusion hUd.le), hdd,
      ⟨fun g => hSd.pres _, fun g => hSd.impl (Subgroup.inclusion hUd.le g), fun g => hSd.adm _⟩,
      fun l hl hinv p t hp => hR l hl hinv (Subgroup.inclusion hUd.le p) t hp,
      fun g gd hg => hbox (Subgroup.inclusion hU.le g) (Subgroup.inclusion hUd.le gd) hg⟩,
    fun g => ⟨Subgroup.inclusion hU.ge g, rfl, rfl⟩⟩

end Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_isQuad (hσ : IsCMExt F E σ) : ∃ δ : E, IsQuad σ δ := by
  obtain ⟨-, hc, h2, hτ⟩ := hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hi : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hτ, hτ, star_star])
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra h
    push Not at h
    refine IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_))
    have := hτ τ x
    rw [h] at this
    exact this.symm
  have h0 : x - σ x ≠ 0 := sub_ne_zero.2 hx.symm
  have ha : σ (x - σ x) = -(x - σ x) := by rw [map_sub, hi, neg_sub]
  have hl : LinearIndependent F ![(1 : E), x - σ x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg σ hst
    have h4 := hst
    rw [Algebra.smul_def, Algebra.smul_def] at h1 h4
    rw [map_add (f := _), map_mul, map_mul, σ.commutes, σ.commutes, map_one, ha, map_zero] at h1
    have h3 : algebraMap F E (s + s) = 0 := by
      rw [map_add (f := _)]
      linear_combination h4 + h1
    have hs : s = 0 := add_self_eq_zero.1 ((map_eq_zero _).1 h3)
    rw [hs, zero_smul, zero_add] at hst
    exact ⟨hs, (smul_eq_zero.1 hst).resolve_right h0⟩
  refine ⟨x - σ x, h0.isUnit, ha, basisOfLinearIndependentOfCardEqFinrank hl (by simp [h2]), ?_, ?_⟩ <;>
    simp

theorem exists_ratCoord (h2 : Module.finrank F E = 2) {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ]
    (hκ : Fintype.card κ = Fintype.card α * Fintype.card β)
    (e : Matrix α β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F))
    (he : ∀ x : Matrix α β E, ∃ y z : κ → F,
      e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ d₀ : Matrix α β E ≃ₗ[F] (κ → F) × (κ → F), ∀ x,
      e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F) ((d₀ x).2 i)) := by
  choose y z h using he
  have inj := AdeleRing.algebraMap_injective (𝓞 F) F
  have hadd : ∀ a b : Matrix α β E, incM F (a + b) = incM F a + incM F b := fun a b => by
    ext i j; simp [incM]
  have hsm : ∀ (t : F) (a : Matrix α β E), incM F (t • a) = algebraMap F (AF F) t • incM F a := fun t a => by
    ext i j
    change (1 : AF F) ⊗ₜ[F] (t • a i j) = algebraMap F (AF F) t • ((1 : AF F) ⊗ₜ[F] a i j)
    rw [algebraMap_smul, TensorProduct.tmul_smul]
  let f : Matrix α β E →ₗ[F] (κ → F) × (κ → F) :=
    { toFun := fun x => (y x, z x)
      map_add' := fun a b => by
        have := h (a + b)
        rw [hadd, map_add (f := _), h, h] at this
        refine Prod.ext (funext fun i => inj ?_) (funext fun i => inj ?_)
        · simpa using (congrFun (congrArg Prod.fst this) i).symm
        · simpa using (congrFun (congrArg Prod.snd this) i).symm
      map_smul' := fun t a => by
        have := h (t • a)
        rw [hsm, map_smul, h] at this
        refine Prod.ext (funext fun i => inj ?_) (funext fun i => inj ?_)
        · exact (congrFun (congrArg Prod.fst this) i).symm.trans (map_mul (algebraMap F (AF F)) t (y a i)).symm
        · exact (congrFun (congrArg Prod.snd this) i).symm.trans (map_mul (algebraMap F (AF F)) t (z a i)).symm }
  have hf : Function.Injective f := fun a b hab => by
    have h1 : y a = y b := congrArg Prod.fst hab
    have h3 : z a = z b := congrArg Prod.snd hab
    have : incM F a = incM F b := e.injective (by rw [h, h, h1, h3])
    exact Matrix.map_injective (Algebra.TensorProduct.includeRight_injective inj) this
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ h2
  refine ⟨f.linearEquivOfInjective hf ?_, h⟩
  rw [Module.finrank_matrix, h2, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hκ]
  ring

theorem member (hσ : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {δ a b : E} (hq : IsQuad σ δ)
    (hab : -1 = δ * a * b) {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (hκ : Fintype.card κ = Fintype.card α * Fintype.card β) {JA : Matrix α α E} {JB : Matrix β β E}
    (hA : IsHerm σ (a • JA)) (hB : IsHerm σ (b • JB))
    {d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ}
    (hd : ∀ x : Matrix α β E, ∃ y z : κ → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    {χ : Chr F E} (hχ : IsHecke F E χ) {om : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ)}
    (h : IsWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ om)
    (g : UG (cA σ) (incM F JB)) (γ : Matrix β β E) (hg : (g.1 : Matrix β β (AE F E)) = incM F γ) :
    ∀ Φ ∈ schA F κ, thetaSum F (om g Φ) = thetaSum F Φ := by
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hab
  have hsm : ∀ {ι : Type} (t : E) (J : Matrix ι ι E), incM F (t • J) = inclR (F := F) (AF F) t • incM F J := fun t J => by
    ext i j; simp [incM]
  obtain ⟨d', om', he, hW, hom⟩ := isWeilB_resc (ξ' := inclR (F := F) (AF F) δ)
    (by rw [← map_mul, ← map_mul, ← hab, map_neg, map_one]) (hb.isUnit.map (inclR (F := F) (AF F))) (hsm a JA) (hsm b JB) h
  obtain ⟨d₀, hd₀⟩ := exists_ratCoord hσ.2.2.1 hκ d.e hd
  obtain ⟨g', hg', e⟩ := hom g
  rw [← e]
  refine GlobalTheory.T.seesaw_theta_dual_pair F E σ δ α β κ (a • JA) (b • JB) ψ hψ.1 (isStd_ne_one hψ) hψ.2.1 hq hA hB d' d₀
    (fun x => by rw [← hd₀, ← he]; rfl) χ om' (fun z u hu => ?_) hW g' ⟨γ, by rw [hg']; exact hg⟩
  have : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  have : Nontrivial (AF F ⊗[F] E) := (Algebra.TensorProduct.includeRight_injective (A := AF F) (B := E)
    (algebraMap F (AF F)).injective).nontrivial
  have hz : z ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [hu, TensorProduct.tmul_zero])
  rw [show u = Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 z hz) from Units.ext hu]
  exact hχ.2 _

omit [NumberField E] in
theorem rat_mat {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {γ : UA σ J} (hγ : γ ∈ ratU σ J) :
    ∃ γ₀ : Matrix (Fin n) (Fin n) E, (γ.1 : Matrix (Fin n) (Fin n) (AE F E)) = incM F γ₀ := by
  obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
  exact ⟨g₀, by rw [← hg₀]; rfl⟩

end PositivityTheory.ThKF0.Resc

namespace PositivityTheory.ThKF0

open Resc

theorem darboux_coordinates_rational_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E), (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 → ∀ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW → ∀ om : UA σ JX × UA σ JW →* Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JW) co χX χW om → ∀ γ ∈ ratU σ JX, ∀ γ' ∈ ratU σ JW, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro F E _ _ _ _ _ σ hσ ψ hψ n d JX JW hX hXd hW hWd co hco χX χW hχX hχW om hom γ hγ γ' hγ' Φ hΦ
  obtain ⟨hB, d', hd', hA⟩ := hom.isWeilPair
  obtain ⟨g₀, hg₀⟩ := rat_mat hγ
  obtain ⟨g₀', hg₀'⟩ := rat_mat hγ'
  obtain ⟨δ, hq⟩ := exists_isQuad hσ
  have h0 : δ ≠ 0 := hq.unit.ne_zero
  have eX : IsHerm σ ((1 : E) • JX) := by rw [one_smul]; exact ⟨hX, hXd.isUnit⟩
  have eW : IsHerm σ ((-δ⁻¹) • JW) := by
    refine ⟨fun i j => by simp [hW i j, hq.anti], Ne.isUnit ?_⟩
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) hWd
  have hco' : ∀ x : Matrix (Fin d) (Fin n) E, ∃ y z : Fin n × Fin d → F,
      d'.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun x => by
    have e : incM F x = (incM F xᵀ)ᵀ := rfl
    rw [e, hd']
    exact hco xᵀ
  have e : om (γ, γ') Φ = om.comp (MonoidHom.inl _ _) γ (om.comp (MonoidHom.inr _ _) γ' Φ) := by
    rw [← Module.End.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]
    simp
  rw [e, member hσ hψ hq (by field_simp) (by simp [Nat.mul_comm]) eW eX hco' hχW hA γ g₀ hg₀ _ (hB.1.pres γ' Φ hΦ)]
  exact member hσ hψ hq (by field_simp) (by simp) eX eW hco hχX hB γ' g₀' hg₀' Φ hΦ

end PositivityTheory.ThKF0
end
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace PositivityTheory.ThKF0

def ArchBd : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k

theorem theta_moderate_growth_of_decay (harch : ArchBd) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  have hlat := theta_sum_norm_bound_denominator
  have hfin := weil_rep_bounded_denominator
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨N₀, k₂, C₂, hL⟩ := hlat F (Fin n × Fin d)
  obtain ⟨C₁, k₁, hA⟩ := harch F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ N₀
  obtain ⟨C₃, k₃, hF⟩ := hfin F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  refine ⟨|C₂| * |C₁| * |C₃| ^ k₂, k₁ + k₃ * k₂, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hsupp⟩ := hF g h
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have hb := hL (C₁ * H ^ k₁) m (om (g, h) Φ) hm1 (fun ξ => hA g h _) hsupp
  have hA0 : 0 ≤ C₁ * H ^ k₁ :=
    le_trans (by positivity) (hA g h (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)))
  have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ k₂ := by positivity
  have hmk : (m : ℝ) ^ k₂ ≤ (|C₃| * H ^ k₃) ^ k₂ :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _))) _
  have hC1 : C₁ * H ^ k₁ ≤ |C₁| * H ^ k₁ := mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _)
  show ‖thetaSum F (om (g, h) Φ)‖ ≤ _
  calc ‖thetaSum F (om (g, h) Φ)‖ ≤ C₂ * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ := hb
    _ ≤ |C₂| * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hA0) hm0
    _ ≤ |C₂| * (|C₁| * H ^ k₁) * (|C₃| * H ^ k₃) ^ k₂ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hC1 (abs_nonneg _)) hmk hm0 (mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (pow_nonneg hH0 _)))
    _ = |C₂| * |C₁| * |C₃| ^ k₂ * H ^ (k₁ + k₃ * k₂) := by rw [pow_add, pow_mul]; ring

end PositivityTheory.ThKF0
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

theorem exists_linearEquiv_of_rational {K R E α β κ : Type} [Field K] [CommRing R] [Algebra K R] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Fintype α] [Fintype β] [Fintype κ]
    (hinj : Function.Injective (algebraMap K R))
    (e : Matrix α β (R ⊗[K] E) ≃ₗ[R] (κ → R) × (κ → R))
    (h : ∀ x : Matrix α β E, ∃ y z : κ → K, e (x.map fun t => (1 : R) ⊗ₜ[K] t) =
      (fun i => algebraMap K R (y i), fun i => algebraMap K R (z i))) :
    ∃ d₀ : Matrix α β E ≃ₗ[K] (κ → K) × (κ → K), ∀ x, e (x.map fun t => (1 : R) ⊗ₜ[K] t) =
      (fun i => algebraMap K R ((d₀ x).1 i), fun i => algebraMap K R ((d₀ x).2 i)) := by
  classical
  haveI : Nontrivial R := hinj.nontrivial
  choose y z hyz using h
  have hadd : ∀ a b : Matrix α β E, ((a + b).map fun t => (1 : R) ⊗ₜ[K] t) =
      (a.map fun t => (1 : R) ⊗ₜ[K] t) + b.map fun t => (1 : R) ⊗ₜ[K] t := by
    intro a b
    ext i j
    simp [TensorProduct.tmul_add]
  have hsmul : ∀ (c : K) (a : Matrix α β E), ((c • a).map fun t => (1 : R) ⊗ₜ[K] t) =
      algebraMap K R c • a.map fun t => (1 : R) ⊗ₜ[K] t := by
    intro c a
    ext i j
    change (1 : R) ⊗ₜ[K] (c • a i j) = algebraMap K R c • ((1 : R) ⊗ₜ[K] a i j)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let f : Matrix α β E →ₗ[K] (κ → K) × (κ → K) :=
    { toFun := fun x => (y x, z x)
      map_add' := by
        intro a b
        have key := hyz (a + b)
        rw [hadd, map_add (f := _), hyz a, hyz b] at key
        have h1 : ∀ i, algebraMap K R (y a i) + algebraMap K R (y b i) = algebraMap K R (y (a + b) i) :=
          fun i => congrFun (congrArg Prod.fst key) i
        have h2 : ∀ i, algebraMap K R (z a i) + algebraMap K R (z b i) = algebraMap K R (z (a + b) i) :=
          fun i => congrFun (congrArg Prod.snd key) i
        refine Prod.ext (funext fun i => hinj ?_) (funext fun i => hinj ?_)
        · change algebraMap K R (y (a + b) i) = algebraMap K R (y a i + y b i)
          rw [map_add (f := _), h1]
        · change algebraMap K R (z (a + b) i) = algebraMap K R (z a i + z b i)
          rw [map_add (f := _), h2]
      map_smul' := by
        intro c a
        have key := hyz (c • a)
        rw [hsmul, map_smul, hyz a] at key
        have h1 : ∀ i, algebraMap K R c * algebraMap K R (y a i) = algebraMap K R (y (c • a) i) :=
          fun i => congrFun (congrArg Prod.fst key) i
        have h2 : ∀ i, algebraMap K R c * algebraMap K R (z a i) = algebraMap K R (z (c • a) i) :=
          fun i => congrFun (congrArg Prod.snd key) i
        refine Prod.ext (funext fun i => hinj ?_) (funext fun i => hinj ?_)
        · change algebraMap K R (y (c • a) i) = algebraMap K R (c * y a i)
          rw [map_mul, h1]
        · change algebraMap K R (z (c • a) i) = algebraMap K R (c * z a i)
          rw [map_mul, h2] }
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : y a = y b := congrArg Prod.fst hab
    have h2 : z a = z b := congrArg Prod.snd hab
    have h3 : (a.map fun t => (1 : R) ⊗ₜ[K] t) = b.map fun t => (1 : R) ⊗ₜ[K] t :=
      e.injective (by rw [hyz a, hyz b, h1, h2])
    ext i j
    exact Algebra.TensorProduct.includeRight_injective (R := K) (A := R) (B := E) hinj (congrFun (congrFun h3 i) j)
  have hdim : Module.finrank K (Matrix α β E) = Module.finrank K ((κ → K) × (κ → K)) := by
    have h1 := e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_prod, Module.finrank_pi, Module.finrank_baseChange] at h1
    rw [Module.finrank_matrix, Module.finrank_prod, Module.finrank_pi]
    simpa using h1
  refine ⟨LinearMap.linearEquivOfInjective f hf hdim, fun x => ?_⟩
  simpa [f] using hyz x

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem ratRel_of_good {ψ : AddChar (AF F) ℂ} {M M₁ : Model σ X W} (h : M.IsGood ψ) (h₁ : M₁.IsGood ψ) : RatRel M.co M₁.co := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨d₀, hd⟩ := exists_linearEquiv_of_rational (AdeleRing.algebraMap_injective (𝓞 F) F) M.co.e h.rat
  intro y z
  obtain ⟨x, hx⟩ := d₀.surjective (y, z)
  obtain ⟨y', z', h'⟩ := h₁.rat x
  refine ⟨incM F x, y', z', ?_, h'⟩
  have := hd x
  rw [hx] at this
  exact this

end PositivityTheory.ThKF0

end
end
