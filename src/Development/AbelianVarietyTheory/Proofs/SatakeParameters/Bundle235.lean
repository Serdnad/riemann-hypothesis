module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle060
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle230
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle221
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle130
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMatrixOfOrthonormalLocalBasisAllPlaces
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle220
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle228
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle229
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle224
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.NormVUnderPow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

noncomputable section

namespace GlobalTheory.WeakBaseChange

theorem isSSRep_of_finiteIndex {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (N : Subgroup Γ) [N.FiniteIndex] (h : IsSSRep (r.comp N.subtype)) : IsSSRep r := by
  classical
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W (fun g v hv => hW g v hv)
  let ρ : Γ → (Fin n → k) →ₗ[k] (Fin n → k) := fun g => (r g : Matrix (Fin n) (Fin n) k).mulVecLin
  have hρ : ∀ g h v, ρ g (ρ h v) = ρ (g * h) v := by
    intro g h v; simp [ρ, Matrix.mulVec_mulVec, map_mul]
  have hρ1 : ∀ v, ρ 1 v = v := by intro v; simp [ρ]
  have hWρ : ∀ g, ∀ v ∈ W, ρ g v ∈ W := fun g v hv => hW g v hv
  let p : (Fin n → k) →ₗ[k] (Fin n → k) := W.subtype ∘ₗ W.linearProjOfIsCompl W' hc
  have hpW : ∀ v, p v ∈ W := fun v => (W.linearProjOfIsCompl W' hc v).2
  have hpl : ∀ w ∈ W, p w = w := fun w hw => by
    have e := congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨w, hw⟩)
    exact e
  have hpr : ∀ w ∈ W', p w = 0 := fun w hw => by
    have e := congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩)
    exact e
  have hpN : ∀ m ∈ N, ∀ v, p (ρ m v) = ρ m (p v) := by
    intro m hm v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top : v ∈ W ⊔ W')
    have hb' : ρ m b ∈ W' := hW' ⟨m, hm⟩ b hb
    rw [show p (a + b) = a by rw [map_add (f := _), hpl a ha, hpr b hb, add_zero], map_add (f := _), map_add (f := _), hpl _ (hWρ m a ha),
      hpr _ hb', add_zero]
  let T : Γ → (Fin n → k) →ₗ[k] (Fin n → k) := fun g => ρ g ∘ₗ p ∘ₗ ρ g⁻¹
  have hTN : ∀ g, ∀ m ∈ N, T (g * m) = T g := by
    intro g m hm; refine LinearMap.ext fun v => ?_
    simp only [T, LinearMap.comp_apply]
    rw [mul_inv_rev, ← hρ m⁻¹ g⁻¹ v, hpN _ (inv_mem hm), hρ (g * m), mul_inv_cancel_right]
  have hTc : ∀ h g v, ρ h (T g v) = T (h * g) (ρ h v) := by
    intro h g v
    simp only [T, LinearMap.comp_apply]
    rw [hρ h g, hρ, mul_inv_rev, inv_mul_cancel_right]
  have hTW : ∀ g v, T g v ∈ W := fun g v => hWρ g _ (hpW _)
  have hTfix : ∀ g, ∀ w ∈ W, T g w = w := by
    intro g w hw
    simp only [T, LinearMap.comp_apply]
    rw [hpl _ (hWρ _ w hw), hρ, mul_inv_cancel, hρ1]
  haveI : Fintype (Γ ⧸ N) := Fintype.ofFinite _
  let S : (Fin n → k) →ₗ[k] (Fin n → k) := ∑ q : Γ ⧸ N, T q.out
  have hout : ∀ (h : Γ) (q : Γ ⧸ N), T (h • q).out = T (h * q.out) := by
    intro h q
    have e1 : ((h * q.out : Γ) : Γ ⧸ N) = h • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hm : (h * q.out)⁻¹ * (h • q).out ∈ N := QuotientGroup.eq.mp (e1.trans (QuotientGroup.out_eq' _).symm)
    rw [← hTN (h * q.out) _ hm, mul_inv_cancel_left]
  have hS : ∀ h v, ρ h (S v) = S (ρ h v) := by
    intro h v

    simp only [S, LinearMap.sum_apply, map_sum, hTc h]
    rw [← Equiv.sum_comp (MulAction.toPerm h : Equiv.Perm (Γ ⧸ N)) (fun q => T (Quotient.out q) (ρ h v))]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply]
    rw [hout]
  set c : k := (Fintype.card (Γ ⧸ N) : k) with hc_def
  have hc0 : c ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let P : (Fin n → k) →ₗ[k] (Fin n → k) := c⁻¹ • S
  have hPW : ∀ v, P v ∈ W := fun v => by
    simp only [P, S, LinearMap.smul_apply, LinearMap.sum_apply]
    exact W.smul_mem _ (W.sum_mem fun q _ => hTW _ _)
  have hPfix : ∀ w ∈ W, P w = w := fun w hw => by
    simp only [P, S, LinearMap.smul_apply, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl fun q _ => hTfix q.out w hw, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k,
      smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hP : ∀ h v, ρ h (P v) = P (ρ h v) := fun h v => by
    simp only [P, LinearMap.smul_apply, map_smul, hS]
  refine ⟨LinearMap.ker P, fun g v hv => ?_, ?_⟩
  · show P (ρ g v) = 0
    rw [← hP, LinearMap.mem_ker.mp hv, map_zero]
  · refine ⟨Submodule.disjoint_def.mpr fun v hv hv' => ?_, codisjoint_iff.mpr (eq_top_iff.mpr fun v _ => ?_)⟩
    · rw [← hPfix v hv]; exact hv'
    · have : v = P v + (v - P v) := by abel
      rw [this]
      refine Submodule.add_mem_sup (hPW v) ?_
      rw [LinearMap.mem_ker, map_sub, hPfix _ (hPW v), sub_self]

end GlobalTheory.WeakBaseChange

namespace GlobalTheory.WeakBaseChange

theorem finiteIndex_range_res (E M Ω : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω] [Algebra E M]
    [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω] : (res E Ω M).range.FiniteIndex := by
  classical
  haveI : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite ℚ E M
  let f : _root_.Formalism.ConjugateSelfDual.G E Ω ⧸ (res E Ω M).range → (M →ₐ[E] Ω) := fun q =>
    ((Quotient.out q : _root_.Formalism.ConjugateSelfDual.G E Ω) : Ω →ₐ[E] Ω).comp (IsScalarTower.toAlgHom E M Ω)
  have hf : Function.Injective f := by
    intro q q' hqq
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    apply QuotientGroup.eq.mpr
    set a : _root_.Formalism.ConjugateSelfDual.G E Ω := Quotient.out q
    set b : _root_.Formalism.ConjugateSelfDual.G E Ω := Quotient.out q'
    have hab : ∀ x : M, a (algebraMap M Ω x) = b (algebraMap M Ω x) := fun x => DFunLike.congr_fun hqq x
    let ρ : _root_.Formalism.ConjugateSelfDual.G M Ω := AlgEquiv.ofRingEquiv (f := (a⁻¹ * b).toRingEquiv) (fun x => by
      show a.symm (b (algebraMap M Ω x)) = algebraMap M Ω x
      rw [← hab, AlgEquiv.symm_apply_apply])
    exact ⟨ρ, AlgEquiv.ext fun x => rfl⟩
  haveI : Finite (_root_.Formalism.ConjugateSelfDual.G E Ω ⧸ (res E Ω M).range) := Finite.of_injective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

end GlobalTheory.WeakBaseChange

namespace GlobalTheory.WeakBaseChange

theorem finiteIndex_comap {Γ Γ' : Type} [Group Γ] [Group Γ'] (f : Γ' →* Γ) (N : Subgroup Γ) [N.FiniteIndex] :
    (N.comap f).FiniteIndex := by
  classical
  let g : Γ' ⧸ N.comap f → Γ ⧸ N := fun q => ((f (Quotient.out q) : Γ) : Γ ⧸ N)
  have hg : Function.Injective g := by
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    apply QuotientGroup.eq.mpr
    have := QuotientGroup.eq.mp h
    rw [Subgroup.mem_comap, map_mul, map_inv]
    exact this
  haveI : Finite (Γ' ⧸ N.comap f) := Finite.of_injective g hg
  exact Subgroup.finiteIndex_of_finite_quotient

theorem algSat_pow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  have hr : ((((q : ℝ) ^ f) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ^ f := by
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _), ← Real.rpow_mul_natCast (Nat.cast_nonneg _),
      mul_comm]
  induction B using Multiset.induction_on with
  | empty => rfl
  | cons b B ih =>
    simp only [algSat, Multiset.map_cons] at ih ⊢
    simp [hr, mul_pow] at ih ⊢

end GlobalTheory.WeakBaseChange


open GlobalTheory.WeakBaseChange in
theorem GlobalTheory.GalCut.weak_comp_res : ∀ (E M Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] [Field Ω] [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω] [IsAlgClosure E Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (P : CuspSub M a), IsLift π P → ∀ r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω M)) := by
  intro E M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι a π P hL r hr
  obtain ⟨hc, hss, hatt⟩ := hr
  refine ⟨hc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom E M Ω), ?_, ?_⟩
  · haveI := finiteIndex_range_res E M Ω
    set H := (res E Ω M).range with hH
    haveI : (H.normalCore.comap (res E Ω M)).FiniteIndex := finiteIndex_comap _ _
    refine isSSRep_of_finiteIndex _ (H.normalCore.comap (res E Ω M)) ?_
    have hrange : ((res E Ω M).comp (H.normalCore.comap (res E Ω M)).subtype).range = H.normalCore := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        obtain ⟨y, hy⟩ := (Subgroup.normalCore_le H hx : x ∈ (res E Ω M).range)
        exact ⟨⟨y, by rw [Subgroup.mem_comap, hy]; exact hx⟩, hy⟩
    have := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r ((res E Ω M).comp (H.normalCore.comap (res E Ω M)).subtype)
      (by rw [hrange]; exact Subgroup.normalCore_normal H) hss
    rwa [MonoidHom.comp_assoc]
  · filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under E M).eventually hatt] with w h
    obtain ⟨B, hB, hF⟩ := h
    have h2 := GlobalTheory.AttResTower.normV_under_pow (K := E) w
    set f := w.asIdeal.inertiaDeg (𝓞 E)
    refine ⟨B.map (· ^ f), hL.sat w f B h2 hB, ?_⟩
    have h3 := (UpperTheory.frobenius_power_compatibility E M Ω l ι w f h2).1 a r _ hF
    rw [h2, algSat_pow]
    exact h3
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.CongOne

open GlobalTheory.TopStep GlobalTheory.BlockDecompositionK1

theorem mem_glint_prinCong_of_cols {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
    {n : ℕ} (D : ℕ) (k : Sp E n ≃ₗ[E] Sp E n) (hD : 1 ≤ D)
    (h : ∀ s l, IntAt P (((qOf P : E) ^ D)⁻¹ * (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l))) :
    ∃ hk : k ∈ GLint E n P, (⟨k, hk⟩ : GLint E n P) ∈ GlobalTheory.TopStep.prinCong n P D := by
  classical
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have hqD : ((qOf P : E) ^ D) ≠ 0 := pow_ne_zero _ hq
  have hsingle : ∀ s l, IntAt P ((Pi.single s (1 : E) : Sp E n) l) := fun s l =>
    mem_stdAt.1 (single_mem_stdAt (P := P) s) l
  have hent : ∀ l s, IntAt P (k (Pi.single s (1 : E)) l) := fun l s => by
    have e : k (Pi.single s (1 : E)) l = (qOf P : E) ^ D * (((qOf P : E) ^ D)⁻¹ *
        (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l)) + (Pi.single s (1 : E) : Sp E n) l := by
      field_simp
      ring
    rw [e]
    exact ((intAt_pow (intAt_nat (qOf P)) D).mul (h s l)).add (hsingle s l)
  let A : Matrix (Fin n) (Fin n) E := Matrix.of fun l s => k (Pi.single s (1 : E)) l
  have hA : ∀ l s, IntAt P (A l s) := hent
  have hAx : ∀ x, A.mulVec x = k x := fun x => by
    funext l
    refine Eq.trans ?_ (apply_eq_sum (k : Sp E n →ₗ[E] Sp E n) x l).symm
    show ∑ s, A l s * x s = _
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_comm]
    rfl
  have hred : A.map (redP P) = 1 := by
    ext l s
    rw [Matrix.map_apply]
    have h0 : redP P (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l) = 0 := by
      obtain ⟨c, rfl⟩ : ∃ c, D = c + 1 := ⟨D - 1, by omega⟩
      exact reduction_eq_zero_of_integral_absNorm_pow_inv_mul (h s l)
    rw [reduction_sub (hent l s) (hsingle s l), sub_eq_zero] at h0
    show redP P (k (Pi.single s (1 : E)) l) = _
    rw [h0, Matrix.one_apply, Pi.single_apply]
    split_ifs
    · exact reduction_one₂
    · exact reduction_zero
  have hdet : IsUnit (redP P A.det) := by
    rw [(det_int hA).2, hred, Matrix.det_one]
    exact isUnit_one
  obtain ⟨j, hj⟩ := exists_glint_of_matrix A hA hdet
  have hjk : j.1 = k := LinearEquiv.ext fun x => (hj x).trans (hAx x)
  have hk : k ∈ GLint E n P := hjk ▸ j.2
  refine ⟨hk, fun x hx => ?_⟩
  refine mem_stdAt.2 fun l => ?_
  have e1 := apply_eq_sum (k : Sp E n →ₗ[E] Sp E n) x l
  have e2 := apply_eq_sum (LinearMap.id : Sp E n →ₗ[E] Sp E n) x l
  have e : (((qOf P : E) ^ D)⁻¹ • (k x - x)) l = ∑ s, x s * (((qOf P : E) ^ D)⁻¹ *
      (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l)) := by
    rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    change ((qOf P : E) ^ D)⁻¹ * ((k : Sp E n →ₗ[E] Sp E n) x l - (LinearMap.id : Sp E n →ₗ[E] Sp E n) x l) = _
    rw [e1, e2, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [LinearMap.id_apply, LinearEquiv.coe_coe]
    ring
  rw [e]
  exact intAt_sum _ fun s _ => (mem_stdAt.1 hx s).mul (h s l)

end GlobalTheory.CongOne
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

theorem norm_hK_le_one : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → ∀ w a b₀ i, ‖hK D lam P P' b w a b₀ i‖ ≤ 1 := by
  intro D p _ lam σ hσ hcl N N' L L' P P' hP hP' r b hb w a b₀ i
  obtain ⟨h2, hq, -⟩ := GlobalTheory.InertCompare.ne_of_inert D p hcl
  obtain ⟨ρ, hρ⟩ := exists_ringHom_rhoK D lam σ hσ hcl w
  set τ := tauPl D w with hτ
  have hρK : rhoK D lam w = fun y => ρ y := funext fun y => (hρ y).1
  have hρC : ∀ y, ((ρ y : MaximalUnramifiedExtension p) : ℂ_[p]) = GlobalTheory.KerStd.UnitaryMat.rho D lam τ y := fun y => by
    rw [(hρ y).2, GlobalTheory.KerStd.UnitaryMat.tauEmb_eq]
  have hPW : LocBasisW D (GlobalTheory.KerStd.UnitaryMat.rho D lam τ) L (P τ) := by
    rw [← GlobalTheory.KerStd.UnitaryMat.tauEmb_eq]; exact hP.1 τ
  have hP'W : LocBasisW D (GlobalTheory.KerStd.UnitaryMat.rho D lam τ) L' (P' τ) := by
    rw [← GlobalTheory.KerStd.UnitaryMat.tauEmb_eq]; exact hP'.1 τ
  have hdet : IsUnit (P' τ).det := isUnit_iff_ne_zero.2 hP'W.1
  have hQ : (P' τ)⁻¹ * P' τ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hinv : ((P' τ).map (fun y => ρ y))⁻¹ = ((P' τ)⁻¹).map (fun y => ρ y) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [show ((P' τ)⁻¹).map (fun y => ρ y) = ((P' τ)⁻¹).map ρ from rfl,
      show (P' τ).map (fun y => ρ y) = (P' τ).map ρ from rfl, ← Matrix.map_mul, hQ,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := by
    rw [GlobalTheory.PadicPlaceBound.norm_prime_padicComplex]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hint := GlobalTheory.KerStd.UnitaryMat.intIn_of_locBasis hp1
    (fun x hx => GlobalTheory.EigenGenerator.norm_padicEmbedding_le_one_of_mem_inverseHalfDifferent D h2 hq _ hx) hQ hPW hP'W hb i b₀ a
  have e : hK D lam P P' b w a b₀ i = ρ (((P' τ)⁻¹ * b i * P τ) b₀ a) := by
    unfold hK
    rw [← hτ, hρK, hinv]

    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
  show ‖((hK D lam P P' b w a b₀ i : MaximalUnramifiedExtension p) : ℂ_[p])‖ ≤ 1
  rw [e, hρC]
  exact hint

end GlobalTheory.KerStd.HypCoord
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

theorem _root_.GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsCompact (GlobalTheory.Cong.AdaptLev.intU a w : Set (UA E a)) ∧ IsOpen (((GlobalTheory.Cong.AdaptLev.intU a w).subgroupOf (locU a w)) : Set (locU a w)) := by
  first | (exact @GlobalTheory.Cong.AdaptLev.intU_isCompact_isOpen) | (exact GlobalTheory.Cong.AdaptLev.intU_isCompact_isOpen) | (intros; apply GlobalTheory.Cong.AdaptLev.intU_isCompact_isOpen  <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

theorem _root_.GlobalTheory.T.isLevelAway_definiteUnitaryLevelFromLocalLevels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → IsLevelAway w₀ (GlobalTheory.Cong.AdaptLev.levelOf a w₀ H) := by
  first | (exact @GlobalTheory.Cong.LevAway.isLevelAway_levelOf) | (exact GlobalTheory.Cong.LevAway.isLevelAway_levelOf) | (intros; apply GlobalTheory.Cong.LevAway.isLevelAway_levelOf  <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem upper_inv_diag {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hU : ∀ r s, s < r → M r s = 0) (hd : ∀ r, M r r ≠ 0) :
    (∀ r s, s < r → M⁻¹ r s = 0) ∧ ∀ r, M⁻¹ r r = (M r r)⁻¹ := by
  classical
  have hB : Matrix.BlockTriangular M id := fun i j h => hU i j h
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular hB]
    exact Finset.prod_ne_zero_iff.2 fun r _ => hd r
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
  letI := M.invertibleOfIsUnitDet hunit
  have hBi : Matrix.BlockTriangular M⁻¹ id := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨fun r s h => hBi h, fun i => ?_⟩
  have h := congrFun (congrFun (Matrix.mul_nonsing_inv M hunit) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [Finset.sum_eq_single i] at h
  · exact eq_inv_of_mul_eq_one_right h
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hU i k hk, zero_mul]
    · rw [hBi hk, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem zT_mul {n : ℕ} (x β : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    zT X D pos (fun τ => x τ * β τ) = fun τ => zT X D pos x τ *
      (if IsOddPos (pos.symm τ).2 then ((β τ)⁻¹).transpose.submatrix Fin.rev Fin.rev else β τ) := by
  funext τ
  unfold zT
  split_ifs with h
  · rw [Matrix.mul_inv_rev, Matrix.transpose_mul]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
    exact (Equiv.sum_comp Fin.revPerm (fun k => ((x τ)⁻¹).transpose i k * ((β τ)⁻¹).transpose k (Fin.rev j))).symm
  · rfl

theorem prod_inv_rev_zpow_mul_prod_pow_eq_odd_position {n : ℕ} (b : Fin n → ℂ) (hb : ∀ r, b r ≠ 0) (c : ℤ) (ν : Fin n → ℕ) (h : ∀ r, (ν r : ℤ) ≤ c) :
    (∏ r, (b (Fin.rev r))⁻¹) ^ (-c) * ∏ r, (b (Fin.rev r))⁻¹ ^ ν r = ∏ r, b r ^ (c - (ν (Fin.rev r) : ℤ)).toNat := by
  rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  rw [← Equiv.prod_comp Fin.revPerm (fun r => b r ^ (c - (ν (Fin.rev r) : ℤ)).toNat)]
  refine Finset.prod_congr rfl fun r _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  have e : b (Fin.rev r) ^ (c - (ν r : ℤ)).toNat = b (Fin.rev r) ^ (c - (ν r : ℤ)) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (by linarith [h r])]
  rw [e, inv_zpow', neg_neg, inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (hb _)]
  congr 1

theorem twF_mul_bor : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) (c : D.what₂.Tau → ℤ), (∀ τ r, (ν τ r : ℤ) ≤ c τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∀ (x β : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, (x τ).det ≠ 0) → IsBor β → twF X D pos c Q (fun τ => x τ * β τ) = (∏ τ, ∏ r, β τ r r ^ (if IsOddPos (pos.symm τ).2 then (c τ - (ν τ (Fin.rev r) : ℤ)).toNat else ν τ r)) * twF X D pos c Q x := by
  intro p _ X D pos n ν c hνc Q hQ x β _hx hβ
  classical
  have hbd : ∀ τ r, β τ r r ≠ 0 := fun τ r => (hβ τ).2 r
  have hinv : ∀ τ, (∀ r s, s < r → ((β τ)⁻¹) r s = 0) ∧ ∀ r, ((β τ)⁻¹) r r = (β τ r r)⁻¹ :=
    fun τ => upper_inv_diag (β τ) (hβ τ).1 (hbd τ)
  let β' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := fun τ =>
    if IsOddPos (pos.symm τ).2 then ((β τ)⁻¹).transpose.submatrix Fin.rev Fin.rev else β τ
  have hd' : ∀ τ r, β' τ r r = if IsOddPos (pos.symm τ).2 then (β τ (Fin.rev r) (Fin.rev r))⁻¹ else β τ r r := by
    intro τ r
    simp only [β']
    split_ifs
    · simp [(hinv τ).2]
    · rfl
  have hB' : IsBor β' := by
    intro τ
    refine ⟨fun r s hsr => ?_, fun r => ?_⟩
    · simp only [β']
      split_ifs
      · simp only [Matrix.submatrix_apply, Matrix.transpose_apply]
        exact (hinv τ).1 _ _ (Fin.rev_lt_rev.2 hsr)
      · exact (hβ τ).1 r s hsr
    · rw [hd']
      split_ifs
      · exact inv_ne_zero (hbd τ _)
      · exact hbd τ r
  have hz : zT X D pos (fun τ => x τ * β τ) = fun τ => zT X D pos x τ * β' τ := zT_mul X D pos x β
  have hev : GL3Theta.evFr D Q (fun τ => zT X D pos x τ * β' τ) =
      (∏ τ, ∏ r, β' τ r r ^ ν τ r) * GL3Theta.evFr D Q (zT X D pos x) := by
    have h1 := Formalism.L2.KerInert.SharpPolyP.sp_eval_colSub β' (zT X D pos x) Q
    rw [hQ β' hB', MvPolynomial.smul_eval] at h1
    exact h1.symm
  have key : ∀ τ, (if IsOddPos (pos.symm τ).2 then (zT X D pos x τ * β' τ).det ^ (-(c τ)) else 1) * ∏ r, β' τ r r ^ ν τ r
      = (∏ r, β τ r r ^ (if IsOddPos (pos.symm τ).2 then (c τ - (ν τ (Fin.rev r) : ℤ)).toNat else ν τ r)) *
        (if IsOddPos (pos.symm τ).2 then (zT X D pos x τ).det ^ (-(c τ)) else 1) := by
    intro τ
    by_cases ho : IsOddPos (pos.symm τ).2
    · simp only [if_pos ho]
      rw [Matrix.det_mul, Formalism.L2.KerInert.SharpPolyP.sp_det_bor hB', mul_zpow]
      simp only [hd', if_pos ho]
      rw [← prod_inv_rev_zpow_mul_prod_pow_eq_odd_position (fun r => β τ r r) (hbd τ) (c τ) (ν τ) (hνc τ)]
      ring
    · simp only [if_neg ho, one_mul, mul_one, hd']
  unfold twF
  rw [hz, hev]
  calc (∏ τ, if IsOddPos (pos.symm τ).2 then (zT X D pos x τ * β' τ).det ^ (-(c τ)) else 1) *
        ((∏ τ, ∏ r, β' τ r r ^ ν τ r) * GL3Theta.evFr D Q (zT X D pos x))
      = (∏ τ, (if IsOddPos (pos.symm τ).2 then (zT X D pos x τ * β' τ).det ^ (-(c τ)) else 1) * ∏ r, β' τ r r ^ ν τ r) *
          GL3Theta.evFr D Q (zT X D pos x) := by rw [Finset.prod_mul_distrib]; ring
    _ = _ := by simp_rw [key]; rw [Finset.prod_mul_distrib]; ring

end GlobalTheory.TwV.DelA
end
end
