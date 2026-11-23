module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle057
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply
public import Mathlib.CategoryTheory.Category.Basic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace CompanionTheory.Zuck

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem decomposition_of_injective : DecOfInj := by
  intro O N _ _ Hom C S _ X T hs hj hm hi
  classical
  choose i hi hi0 using hi
  have hp : ∀ s, ∃ p, Hom X (T s) p ∧ p ∘ₗ i s = LinearMap.id ∧ p ≠ 0 := by
    intro s
    obtain ⟨y, hy⟩ : ∃ y, i s y ≠ 0 := by
      by_contra hn
      exact hi0 s (LinearMap.ext fun y => not_not.1 fun h => hn ⟨y, h⟩)
    obtain ⟨t, p, hp, hpy⟩ : ∃ t p, Hom X (T t) p ∧ p (i s y) ≠ 0 := by
      by_contra hn
      exact hy (hj _ fun t p hp => not_not.1 fun h => hn ⟨t, p, hp, h⟩)
    obtain rfl : s = t := by
      by_contra hst
      exact hpy (LinearMap.congr_fun (hs.2.2 s t hst _ (C.comp _ _ _ _ _ (hi s) hp)) y)
    obtain ⟨c, hc⟩ := hs.2.1 s _ (C.comp _ _ _ _ _ (hi s) hp)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hpy (by simpa using LinearMap.congr_fun hc y)
    refine ⟨c⁻¹ • p, C.smul _ _ _ _ hp, ?_, fun h0 => hpy ?_⟩
    · rw [LinearMap.smul_comp, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    · rw [(smul_eq_zero.1 h0).resolve_left (inv_ne_zero hc0)]; rfl
  choose p hp hpi hp0 using hp
  have hne : ∀ s t, s ≠ t → p s ∘ₗ i t = 0 := fun s t hst =>
    hs.2.2 t s (Ne.symm hst) _ (C.comp _ _ _ _ _ (hi t) (hp s))
  refine ⟨i, p, hi, hp, LinearMap.ext fun x => ?_, hpi, hne⟩
  rw [LinearMap.id_apply, eq_comm, ← sub_eq_zero]
  refine hj _ fun t q hq => ?_
  have h0 : p t (x - (∑ s, i s ∘ₗ p s) x) = 0 := by

    rw [map_sub, LinearMap.sum_apply, map_sum, Finset.sum_eq_single t]
    · exact sub_eq_zero.2 (LinearMap.congr_fun (hpi t) (p t x)).symm
    · intro s _ hst
      exact LinearMap.congr_fun (hne t s (Ne.symm hst)) (p s x)
    · simp
  obtain ⟨α, β, hab, h1⟩ := hm t q (p t) hq (hp t)
  have hα : α ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at h1
    exact hp0 t ((smul_eq_zero.1 h1).resolve_left (hab.resolve_left (not_not.2 rfl)))
  have h2 := LinearMap.congr_fun h1 (x - (∑ s, i s ∘ₗ p s) x)
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, h0, smul_zero, add_zero] at h2
  exact (smul_eq_zero.1 h2).resolve_left hα

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem trivial_rep_admissible : OKTriv := fun _ _ =>
  ⟨rfl, fun _ _ _ _ => (Matrix.one_mul _).symm,
    fun _ _ _ _ => ⟨Set.univ, _, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
    ⟨1, fun _ _ _ _ => by simp⟩⟩

theorem vector_rep_admissible : OKVr := by
  intro k r b
  cases b
  · refine ⟨rfl, fun _ _ _ _ => rfl, fun c d _ _ => ?_, ⟨1, fun g _ c d => ?_⟩⟩
    · exact ⟨Set.univ, fun g => g c d, isOpen_univ, trivial,
        (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ c d)).contDiff.contDiffOn, fun _ _ _ => rfl⟩
    · simpa using GlobalTheory.DualFRep.entry_le g c d
  · obtain ⟨-, -, h1, h2, -, -, h3, -⟩ := GlobalTheory.isFRep_dualM k r
    refine ⟨h1, h2, fun c d _ _ => ?_, h3⟩
    let A : Mx k r →ₗ[ℝ] ℂ :=
      { toFun := fun x => (PI.UpqRep.Hpk k r * xᴴ * PI.UpqRep.Hpk k r) d c
        map_add' := fun a b => by rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]; rfl
        map_smul' := fun t a => by
          rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, star_trivial]; rfl }
    refine ⟨Set.univ, A, isOpen_univ, trivial, (LinearMap.toContinuousLinearMap A).contDiff.contDiffOn,
      fun g _ hg => ?_⟩
    show g⁻¹ d c = _
    rw [PI.HwUniqW.inv_eq_UH hg]; rfl

end CompanionTheory.Zuck

end
end

section

open Matrix Finset
open scoped Kronecker

noncomputable section

namespace CompanionTheory.Zuck

open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem mAct_apply {ι ι' : Type} [Fintype ι] {V : Type} [AddCommGroup V] [Module ℂ V] (A : Matrix ι' ι ℂ)
    (x : ι → V) (c : ι') : mAct A x c = ∑ d, A c d • x d := by
  simp [mAct]

theorem mAct_mul {ι ι' ι'' : Type} [Fintype ι] [Fintype ι'] {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : Matrix ι'' ι' ℂ) (B : Matrix ι' ι ℂ) : (mAct (A * B) : (ι → V) →ₗ[ℂ] _) = mAct A ∘ₗ mAct B := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [LinearMap.comp_apply, mAct_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem mAct_smul {ι ι' : Type} [Fintype ι] {V : Type} [AddCommGroup V] [Module ℂ V] (a : ℂ) (A : Matrix ι' ι ℂ) :
    (mAct (a • A) : (ι → V) →ₗ[ℂ] _) = a • mAct A := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [mAct_apply, LinearMap.smul_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Finset.smul_sum,
    smul_smul]

theorem mAct_sub {ι ι' : Type} [Fintype ι] {V : Type} [AddCommGroup V] [Module ℂ V] (A B : Matrix ι' ι ℂ) :
    (mAct (A - B) : (ι → V) →ₗ[ℂ] _) = mAct A - mAct B := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [mAct_apply, LinearMap.sub_apply, Pi.sub_apply, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem mAct_one {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V] :
    (mAct (1 : Matrix ι ι ℂ) : (ι → V) →ₗ[ℂ] _) = LinearMap.id := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [mAct_apply, Matrix.one_apply]

theorem hom_cas (hL : HomLie) {X Y : Obj k r} {f : M X →ₗ[ℂ] M Y} (hX : X.1.OK) (hY : Y.1.OK) (hf : IsHom X Y f)
    (x : M X) : f (cas X x) = cas Y (f x) := by
  have h : ∀ Z x, f (L X Z x) = L Y Z (f x) := fun Z x => LinearMap.congr_fun (hL k r X Y f hX hY hf Z) x

  simp only [cas, LinearMap.sum_apply, Module.End.mul_apply, map_sum, h]

def cM (n : ℕ) : Matrix Unit (Fin n × Fin n) ℂ := fun _ p => if p.1 = p.2 then 1 else 0

theorem cM_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : Aᵀ * B = 1) :
    cM n * (A ⊗ₖ B) = (1 : Matrix Unit Unit ℂ) * cM n := by
  rw [Matrix.one_mul]
  ext _ ⟨c, d⟩
  have := congrFun (congrFun h c) d
  simp only [Matrix.mul_apply, Matrix.one_apply, transpose_apply] at this
  simp only [Matrix.mul_apply, cM, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, kroneckerMap_apply, this]

theorem cM_hom (hM : MatHom) (b : Bool) (B : URep k r) :
    IsHom ((vr k r b).tens (vr k r (!b)), B) (one B) (mAct (cM _)) := by
  refine hM k r _ _ B _ fun g hg => ?_
  have hu : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det _).1 (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg).1
  cases b
  · exact cM_mul (A := g) (B := (g⁻¹)ᵀ) (by rw [← transpose_mul, Matrix.nonsing_inv_mul g hu, transpose_one])
  · exact cM_mul (A := (g⁻¹)ᵀ) (B := g) (by rw [transpose_transpose, Matrix.nonsing_inv_mul g hu])

theorem casimir_kronecker_sum (n : ℕ) :
    (∑ a : Fin n, ∑ b : Fin n, Matrix.single a b (1 : ℂ) ⊗ₖ (-(Matrix.single b a (1 : ℂ))ᵀ) =
      (-1 : ℂ) • ((cM n)ᵀ * cM n)) ∧
    (∑ a : Fin n, ∑ b : Fin n, (-(Matrix.single a b (1 : ℂ))ᵀ) ⊗ₖ Matrix.single b a (1 : ℂ) =
      (-1 : ℂ) • ((cM n)ᵀ * cM n)) := by
  constructor <;> ext ⟨c, d⟩ ⟨c', d'⟩ <;>
    simp only [Matrix.sum_apply, kroneckerMap_apply, Matrix.neg_apply,
      transpose_apply, Matrix.smul_apply, Matrix.mul_apply, cM, Matrix.single_apply] <;>
    by_cases e1 : c = d <;> by_cases e2 : c' = d' <;> simp [e1, e2, ite_and, eq_comm]

theorem qMat_vr (hS : StdD) (b : Bool) :
    qMat (vr k r b) (vr k r (!b)) = (-1 : ℂ) • ((cM _)ᵀ * cM _ : Matrix _ _ ℂ) := by
  cases b
  · refine Eq.trans ?_ (casimir_kronecker_sum _).1
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
      congrArg₂ _ (hS k r _).1 (hS k r _).2
  · refine Eq.trans ?_ (casimir_kronecker_sum _).2
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
      congrArg₂ _ (hS k r _).2 (hS k r _).1

def uM (ι : Type) [DecidableEq ι] : Matrix (Unit × ι) ι ℂ := fun p d => if p.2 = d then 1 else 0

theorem uM_int (F : FRep k r) (g : Mx k r) : uM F.ι * F.ρ g = ((triv k r).tens F).ρ g * uM F.ι := by
  ext ⟨_, c⟩ d
  simp [Matrix.mul_apply, uM, Fintype.sum_prod_type]

theorem multOne_of (hC : HomCat) (hM : MatHom) (hT : TensHom) (hL : HomLie) (hS : CasSplit) (hD : StdD)
    (hK : KerZero) (o1 : OKTriv) (o2 : OKVr) (o3 : OKTens) : MultOne := by
  intro k r b B T S Bt cB cT ct hR hB hTc hBt hne hinj hEnd hDS ⟨κ, hκ, hκ0⟩
  have C := hC k r
  let Φ : (M (one T) →ₗ[ℂ] M (vr k r b, B)) → (M (one B) →ₗ[ℂ] M ((vr k r b).tens (vr k r (!b)), B)) :=
    fun i => on1 i ∘ₗ (mAct (uM _) ∘ₗ κ)
  have Φap : ∀ i v c d, Φ i v (c, d) = i (fun _ => κ v d) c := by
    intro i v c d
    simp only [Φ, on1, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply]
    refine congrFun (congrArg i (funext fun u => ?_)) c
    simp [LinearMap.funLeft_apply, mAct_apply, uM]
  have Φhom : ∀ i, IsHom (one T) (vr k r b, B) i → IsHom (one B) ((vr k r b).tens (vr k r (!b)), B) (Φ i) := by
    intro i hi
    exact C.comp _ ((triv k r).tens (vr k r (!b)), T) _ _ _
      (C.comp _ (vr k r (!b), T) _ _ _ hκ (hM k r _ _ T _ fun g _ => uM_int _ g))
      (hT k r _ _ (vr k r (!b)) _ _ i hi).1
  have chom : IsHom ((vr k r b).tens (vr k r (!b)), B) (one B) (mAct (cM _)) :=
    cM_hom hM b B
  have core : ∀ i, IsHom (one T) (vr k r b, B) i → (∀ v, mAct (cM _) (Φ i v) = 0) → i = 0 := by
    intro i hi h0
    have hz : ∀ v c, (fun d => Φ i v (c, d)) = 0 := by
      intro v c
      have e1 := hom_cas hL (o1 k r) (o3 k r _ _ (o2 k r b) (o2 k r (!b))) (Φhom i hi) v
      rw [hB, hS k r _ _ B (o2 k r b) (o2 k r (!b)), hR, qMat_vr hD, mAct_smul, mAct_mul] at e1
      have e2 : cas1 (vr k r b) (vr k r (!b)) B (Φ i v) = cT • Φ i v := by
        funext ⟨c, d⟩
        have := hom_cas hL (o1 k r) (o2 k r b) hi (fun _ => κ v d)
        rw [hTc] at this
        simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul] at this
        show cas (vr k r b, B) (fun c' => Φ i v (c', d)) c = cT • Φ i v (c, d)
        simp only [Φap]
        exact (congrFun this c).symm
      have e3 : cas2 (vr k r b) (vr k r (!b)) B (Φ i v) = (2 * cB - cT) • Φ i v := by
        simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
          LinearMap.comp_apply, h0, map_zero, smul_zero, add_zero, e2] at e1
        rw [sub_smul, two_mul, add_smul]
        rw [eq_sub_iff_add_eq] at e1
        rw [e1]; abel
      have e4 : cas (vr k r (!b), B) (fun d => Φ i v (c, d)) = (2 * cB - cT) • fun d => Φ i v (c, d) :=
        funext fun d => congrFun e3 (c, d)
      refine hinj _ fun t p hp => ?_
      have e5 := hom_cas hL (o2 k r (!b)) (o1 k r) hp (fun d => Φ i v (c, d))
      rw [e4, hBt, map_smul, LinearMap.smul_apply, LinearMap.id_apply, ← sub_eq_zero, ← sub_smul] at e5
      exact (smul_eq_zero.1 e5).resolve_left (sub_ne_zero.2 (hne t).symm)
    obtain ⟨v, hv⟩ : ∃ v, κ v ≠ 0 := by
      by_contra hn
      exact hκ0 (LinearMap.ext fun v => not_not.1 fun h => hn ⟨v, h⟩)
    obtain ⟨d, hd⟩ := Function.ne_iff.1 hv
    refine hK k r T _ i hDS hi (fun _ => κ v d) (fun h => hd (congrFun h ())) (funext fun c => ?_)
    rw [← Φap]
    exact congrFun (hz v c) d
  intro i i' hi hi'
  obtain ⟨l, hl⟩ := hEnd _ (C.comp _ _ _ _ _ (Φhom i hi) chom)
  obtain ⟨l', hl'⟩ := hEnd _ (C.comp _ _ _ _ _ (Φhom i' hi') chom)
  obtain ⟨α, β, hab, h0⟩ : ∃ α β : ℂ, (α ≠ 0 ∨ β ≠ 0) ∧ α * l + β * l' = 0 := by
    by_cases h : l = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [h]⟩
    · exact ⟨l', -l, Or.inr (neg_ne_zero.2 h), by ring⟩
  refine ⟨α, β, hab, core _ (C.add _ _ _ _ (C.smul _ _ α _ hi) (C.smul _ _ β _ hi')) fun v => ?_⟩
  have e : Φ (α • i + β • i') v = α • Φ i v + β • Φ i' v := by
    funext ⟨c, d⟩
    simp [Φap]
  have a1 := LinearMap.congr_fun hl v
  have a2 := LinearMap.congr_fun hl' v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at a1 a2
  rw [e, map_add (f := _), map_smul, map_smul, a1, a2, smul_smul, smul_smul, ← add_smul, h0, zero_smul]

end CompanionTheory.Zuck

end
end
