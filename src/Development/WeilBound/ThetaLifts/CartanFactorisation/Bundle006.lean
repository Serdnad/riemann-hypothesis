module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle005
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle004
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem exists_section {A P : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup P] [Module ℂ P] (p : A →ₗ[ℂ] P)
    (S : Submodule ℂ A) : ∃ s : P →ₗ[ℂ] A, (∀ y, s y ∈ S) ∧ ∀ x ∈ S, p (s (p x)) = p x := by
  let g := p.domRestrict S
  obtain ⟨t, ht⟩ := g.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict g)
  obtain ⟨q, hq⟩ := (LinearMap.range g).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  refine ⟨S.subtype ∘ₗ t ∘ₗ q, fun y => (t (q y)).2, fun x hx => ?_⟩
  have e : q (p x) = ⟨p x, ⟨x, hx⟩, rfl⟩ := LinearMap.congr_fun hq ⟨p x, ⟨x, hx⟩, rfl⟩
  have := congrArg Subtype.val (LinearMap.congr_fun ht ⟨p x, ⟨x, hx⟩, rfl⟩)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, e]
  exact this

theorem ml_congr {ι : Type} [Fintype ι] {Y : ι → Type} [∀ v, AddCommGroup (Y v)] [∀ v, Module ℂ (Y v)] {Z : Type}
    [AddCommGroup Z] [Module ℂ Z] (l : MultilinearMap (RingHom.id ℂ) Y Z) (S K : ∀ v, Submodule ℂ (Y v))
    (h : ∀ ψ, (∀ v, ψ v ∈ S v) → (∃ v, ψ v ∈ K v) → l ψ = 0) (ψ ψ' : ∀ v, Y v) (hψ : ∀ v, ψ v ∈ S v) (hψ' : ∀ v, ψ' v ∈ S v)
    (hk : ∀ v, ψ v - ψ' v ∈ K v) : l ψ = l ψ' := by
  have e : ψ = (ψ - ψ') + ψ' := (sub_add_cancel _ _).symm
  rw [e, l.map_add_univ, Finset.sum_eq_single ∅, Finset.piecewise_empty]
  · intro s _ hs
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.2 hs
    refine h _ (fun u => ?_) ⟨v, by rw [Finset.piecewise_eq_of_mem _ _ _ hv]; exact hk v⟩
    by_cases hu : u ∈ s
    · rw [Finset.piecewise_eq_of_mem _ _ _ hu]; exact sub_mem (hψ u) (hψ' u)
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hu]; exact hψ' u
  · exact fun h => absurd (Finset.mem_univ _) h

theorem desc {ι : Type} [Fintype ι] {A P Z : Type} {Y Q : ι → Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Z] [Module ℂ Z] [∀ v, AddCommGroup (Y v)] [∀ v, Module ℂ (Y v)] [∀ v, AddCommGroup (Q v)]
    [∀ v, Module ℂ (Q v)] (l : A →ₗ[ℂ] MultilinearMap (RingHom.id ℂ) Y Z) (p : A →ₗ[ℂ] P) (q : ∀ v, Y v →ₗ[ℂ] Q v) (S₀ : Submodule ℂ A)
    (S : ∀ v, Submodule ℂ (Y v)) (h : ∀ f ∈ S₀, ∀ ψ, (∀ v, ψ v ∈ S v) → (p f = 0 ∨ ∃ v, q v (ψ v) = 0) → l f ψ = 0) :
    ∃ L : P ⊗[ℂ] (PiTensorProduct ℂ Q) →ₗ[ℂ] Z, ∀ f ∈ S₀, ∀ ψ, (∀ v, ψ v ∈ S v) →
      L (p f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v => q v (ψ v)) = l f ψ := by
  obtain ⟨s₀, hs₀, hs₀'⟩ := exists_section p S₀
  choose s hs hs' using fun v => exists_section (q v) (S v)
  refine ⟨TensorProduct.lift ((PiTensorProduct.lift (R := ℂ) (s := Q) (E := Z)).toLinearMap ∘ₗ
    (MultilinearMap.compLinearMapₗ s) ∘ₗ l ∘ₗ s₀), fun f hf ψ hψ => ?_⟩
  simp only [TensorProduct.lift.tmul, LinearMap.comp_apply, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMapₗ_apply, MultilinearMap.compLinearMap_apply]
  rw [ml_congr (l (s₀ (p f))) S (fun v => LinearMap.ker (q v)) (fun ψ h1 h2 => h _ (hs₀ _) ψ h1 (Or.inr h2)) _ ψ
    (fun v => hs v _) hψ (fun v => by rw [LinearMap.mem_ker, map_sub, hs' v _ (hψ v), sub_self])]
  have := h (s₀ (p f) - f) (sub_mem (hs₀ _) hf) ψ hψ (Or.inl (by rw [map_sub, hs₀' f hf, sub_self]))
  rwa [map_sub, MultilinearMap.sub_apply, sub_eq_zero] at this

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def Std (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : Prop :=
  ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

theorem Std.congr {φ w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hw : Std w) (h : ∀ᶠ v in cofinite, φ v = w v) : Std φ := by
  filter_upwards [hw, h] with v h1 h2 using h2.trans h1

theorem ev_of_off {φ w : ∀ v : Pl F, (κ → Fv F v) → ℂ} {T : Finset (Pl F)} (h : ∀ v ∉ T, φ v = w v) :
    ∀ᶠ v in cofinite, φ v = w v := by
  filter_upwards [T.eventually_cofinite_notMem] with v hv using h v hv

theorem tens_eq {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hne : ∀ v, w v ≠ 0) (hw : Std w) (T : Finset (Pl F)) {ι ι' : Type}
    [Fintype ι] [Fintype ι'] (f : ι → SInf F κ) (φ : ι → ∀ v : Pl F, (κ → Fv F v) → ℂ) (f' : ι' → SInf F κ)
    (φ' : ι' → ∀ v : Pl F, (κ → Fv F v) → ℂ) (h : ∀ i, ∀ v ∉ T, φ i v = w v) (h' : ∀ i, ∀ v ∉ T, φ' i v = w v)
    (e : ∑ i, pure (f i) (φ i) = ∑ i, pure (f' i) (φ' i)) :
    ∑ i, f i ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => φ i v) =
      ∑ i, f' i ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => φ' i v) := by
  let E := (Fintype.equivFin (ι ⊕ ι')).symm
  let c : ι ⊕ ι' → ℂ := Sum.elim (fun _ => 1) fun _ => -1
  have := tensInj F κ w hne hw T _ (fun i => c (E i)) (fun i => Sum.elim f f' (E i)) (fun i => Sum.elim φ φ' (E i))
    (fun i => by rcases E i with j | j; exacts [h j, h' j])
    (by rw [E.sum_comp (fun j => c j • pure (Sum.elim f f' j) (Sum.elim φ φ' j)), Fintype.sum_sum_type]
        simp [c, e])
  rw [E.sum_comp (fun j => c j • Sum.elim f f' j ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Sum.elim φ φ' j v)),
    Fintype.sum_sum_type] at this
  simpa [c, ← sub_eq_add_neg, sub_eq_zero] using this

theorem tens_eq_map {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hne : ∀ v, w v ≠ 0) (hw : Std w) (T : Finset (Pl F)) {ι ι' : Type}
    [Fintype ι] [Fintype ι'] (f : ι → SInf F κ) (φ : ι → ∀ v : Pl F, (κ → Fv F v) → ℂ) (f' : ι' → SInf F κ)
    (φ' : ι' → ∀ v : Pl F, (κ → Fv F v) → ℂ) (h : ∀ i, ∀ v ∉ T, φ i v = w v) (h' : ∀ i, ∀ v ∉ T, φ' i v = w v)
    (e : ∑ i, pure (f i) (φ i) = ∑ i, pure (f' i) (φ' i)) {P : Type} [AddCommGroup P] [Module ℂ P] {Q : Pl F → Type}
    [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (p : SInf F κ →ₗ[ℂ] P) (q : ∀ v, ((κ → Fv F v) → ℂ) →ₗ[ℂ] Q v) :
    ∑ i, p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => q v (φ i v)) =
      ∑ i, p (f' i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => q v (φ' i v)) := by
  have := congrArg (TensorProduct.map p (PiTensorProduct.map fun v : T => q v)) (tens_eq hne hw T f φ f' φ' h h' e)

  simpa only [map_sum, TensorProduct.map_tmul, PiTensorProduct.map_tprod] using this

def ext (w : ∀ v : Pl F, (κ → Fv F v) → ℂ) (T : Finset (Pl F)) (ψ : ∀ v : T, (κ → Fv F v) → ℂ) (v : Pl F) :
    (κ → Fv F v) → ℂ := if h : v ∈ T then ψ ⟨v, h⟩ else w v

theorem ext_of {w φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} {T : Finset (Pl F)} (h : ∀ v ∉ T, φ v = w v) :
    ext w T (fun v => φ v) = φ := funext fun v => by
  unfold ext; split_ifs with hv
  exacts [rfl, (h v hv).symm]

theorem ext_off (w : ∀ v : Pl F, (κ → Fv F v) → ℂ) (T : Finset (Pl F)) (ψ) : ∀ v ∉ T, ext w T ψ v = w v :=
  fun _ hv => dif_neg hv

theorem pure_ext {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hw : Std w) (T : Finset (Pl F)) (f : SInf F κ) (ψ) (x : κ → AF F) :
    pure f (ext w T ψ) x = f (fun i => evI F (x i)) * ((∏ v : T, ψ v fun i => evFin F v (x i)) *
      ∏ᶠ (v) (_ : v ∉ T), w v fun i => evFin F v (x i)) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  congr 1
  have hf := GlobalTheory.PureFactor.mulSupport_finite _ (hw.congr (ev_of_off (ext_off w T ψ))) x
  rw [← finprod_mem_univ, ← Set.union_compl_self (T : Set (Pl F)),
    finprod_mem_union' disjoint_compl_right (hf.inter_of_right _) (hf.inter_of_right _), finprod_mem_coe_finset,
    ← Finset.prod_coe_sort T]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => by unfold ext; rw [dite_eq_left v.2]
  · exact finprod_congr fun v => finprod_congr fun hv => by rw [ext_off w T ψ v hv]

theorem exists_pureML {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hw : Std w) (T : Finset (Pl F)) :
    ∃ l : SInf F κ →ₗ[ℂ] MultilinearMap (RingHom.id ℂ) (fun v : T => (κ → Fv F v) → ℂ) ((κ → AF F) → ℂ),
      ∀ f ψ, l f ψ = pure f (ext w T ψ) := by
  let m : (κ → AF F) → MultilinearMap (RingHom.id ℂ) (fun v : T => (κ → Fv F v) → ℂ) ℂ := fun x =>
    (MultilinearMap.mkPiAlgebra ℂ T ℂ).compLinearMap fun v => LinearMap.proj fun i => evFin F v (x i)
  refine ⟨{ toFun := fun f => MultilinearMap.pi fun x =>
              (f (fun i => evI F (x i)) * ∏ᶠ (v) (_ : v ∉ T), w v fun i => evFin F v (x i)) • m x
            map_add' := fun f g => ?_, map_smul' := fun a f => ?_ }, fun f ψ => ?_⟩
  · ext ψ x; simp [add_mul]
  · ext ψ x; simp [mul_assoc]
  · funext x
    rw [pure_ext hw]
    simp [m]; ring

theorem exists_factorOp (v : Pl F) (π : Module.End ℂ ((κ → Fv F v) → ℂ)) :
    ∃ O : Module.End ℂ ((κ → AF F) → ℂ), ∀ (f : SInf F κ) φ, Std φ → O (pure f φ) = pure f (Function.update φ v (π (φ v))) := by
  let sh : (κ → AF F) → (κ → Fv F v) → κ → AF F := fun x y i => x i + GlobalTheory.EmbChart.atPlace v (y i - evFin F v (x i))
  refine ⟨{ toFun := fun Φ x => π (fun y => Φ (sh x y)) fun i => evFin F v (x i)
            map_add' := fun Φ Ψ => funext fun x => ?_, map_smul' := fun a Φ => funext fun x => ?_ }, fun f φ hφ => ?_⟩
  · exact congrFun (π.map_add (fun y => Φ (sh x y)) fun y => Ψ (sh x y)) _
  · exact congrFun (π.map_smul a fun y => Φ (sh x y)) _
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hφ
  have e : pure f φ = tens (evFin F v) (φ v) r := by rw [hr', Function.update_eq_self]
  rw [← hr', e]
  funext x
  have e2 : (fun y => tens (evFin F v) (φ v) r (sh x y)) = r x • φ v := by
    funext y
    have h1 : (fun i => evFin F v (sh x y i)) = y := funext fun i => by
      simp only [sh, map_add (f := _), GlobalTheory.EmbChart.evFin_atPlace, add_sub_cancel]
    have h2 : r (sh x y) = r x := hr x (fun i => GlobalTheory.EmbChart.atPlace v (y i - evFin F v (x i))) fun u hu => by
      funext i
      show u * GlobalTheory.EmbChart.atPlace v (y i - evFin F v (x i)) = 0
      refine Prod.ext (mul_zero u.1) (af_ext fun w => ?_)
      show evalV F w (u.2 * singleFin v (y i - evFin F v (x i))) = evalV F w 0
      rw [map_mul, map_zero]
      by_cases h : w = v
      · subst h; rw [show evalV F w u.2 = 0 from hu, zero_mul]
      · rw [evalV_singleFin_ne h, mul_zero]
    simp only [tens, h1, h2, Pi.smul_apply, smul_eq_mul, mul_comm]
  change π (fun y => tens (evFin F v) (φ v) r (sh x y)) _ = _
  rw [e2, map_smul]
  simp only [tens, Pi.smul_apply, smul_eq_mul, mul_comm]

end PositivityTheory.ThKF

end
end

section

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem re_mul {m : ℕ} {Y : Spc F E m} {R : Type} [Zero R] {ev : AF F → R} {g k : UA σ Y.J} (hg : g ∈ UAt σ Y ev)
    (hk : k ∈ UAt σ Y ev) : g * k ∈ UAt σ Y ev := fun u hu => by
  have e : mat (g * k) - 1 = mat g * (mat k - 1) + (mat g - 1) := by
    rw [show mat (g * k) = mat g * mat k from rfl, Matrix.mul_sub, Matrix.mul_one]; abel
  rw [e, smul_add, hg u hu, ← Matrix.mul_smul, hk u hu, Matrix.mul_zero, add_zero]

theorem re_inv {m : ℕ} {Y : Spc F E m} {R : Type} [Zero R] {ev : AF F → R} {g : UA σ Y.J} (hg : g ∈ UAt σ Y ev) :
    g⁻¹ ∈ UAt σ Y ev := fun u hu => by
  have h1 : mat g⁻¹ * mat g = 1 := by rw [← show mat (g⁻¹ * g) = mat g⁻¹ * mat g from rfl, inv_mul_cancel]; rfl
  have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by rw [Matrix.mul_sub, h1, Matrix.mul_one]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

theorem conj_line {m : ℕ} {Y : Spc F E m} {g : UA σ Y.J} (hg : g ∈ UAt σ Y (evI F)) {γ} (hγ : γ ∈ Lines σ Y) :
    (MulAut.conj g).toMonoidHom.comp γ ∈ Lines σ Y :=
  ⟨show Continuous fun t => g * γ t * g⁻¹ from (continuous_const.mul hγ.1).mul continuous_const,
    fun t => re_mul (re_mul hg (hγ.2 t)) (re_inv hg)⟩

theorem commute_conj {G M : Type} [Group G] [Monoid M] (φ : G →* M) {g k : G} {t t₂ : M} (h : φ g * t₂ = t * φ g)
    (hk : Commute (φ k) t₂) : Commute (φ (g * k * g⁻¹)) t := by
  have h' : φ g⁻¹ * t = t₂ * φ g⁻¹ := by
    calc φ g⁻¹ * t = φ g⁻¹ * (t * φ g) * φ g⁻¹ := by rw [mul_assoc, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = t₂ * φ g⁻¹ := by rw [← h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  show _ * t = t * _
  rw [map_mul, map_mul, mul_assoc, h', ← mul_assoc, mul_assoc (φ g), hk.eq, ← mul_assoc, h]
  simp only [mul_assoc]

theorem cj1 {G H : Type} [Group G] [Group H] (g x : G) (h : H) : (g * x * g⁻¹, (1 : H)) * (g, h) = (g, h) * (x, 1) := by simp

theorem cj2 {G H : Type} [Group G] [Group H] (g : G) (h x : H) : ((1 : G), h * x * h⁻¹) * (g, h) = (g, h) * (1, x) := by simp

theorem cj3 {G H : Type} [Group G] [Group H] (g : G) (h x : H) : ((1 : G), x) * (g, h) = (g, h) * (1, h⁻¹ * x * h⁻¹⁻¹) := by
  simp [mul_assoc]

theorem inv_rel {G M : Type} [Group G] [Monoid M] (φ : G →* M) {g : G} {t t₂ : M} (h : φ g * t₂ = t * φ g) :
    φ g⁻¹ * t = t₂ * φ g⁻¹ := by
  calc φ g⁻¹ * t = φ g⁻¹ * (t * φ g) * φ g⁻¹ := by rw [mul_assoc, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = t₂ * φ g⁻¹ := by rw [← h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

def matC {m : ℕ} (J : Matrix (Fin m) (Fin m) E) {w : InfinitePlace F} (τ : EmbOver E w) : UA σ J →* Matrix (Fin m) (Fin m) ℂ :=
  (piInf τ).mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp (Subgroup.subtype _))

def Moves (B : Base F E) {m : ℕ} (Y Y₂ : Spc F E m) (g : UA σ Y.J) : Prop :=
  g ∈ UAt σ Y (evI F) ∧ ∀ w, (mat g).map (piInf (B.emb w)) * Y₂.θ w = Y.θ w * (mat g).map (piInf (B.emb w))

theorem Moves.up {B : Base F E} {m : ℕ} {Y Y₂ : Spc F E m} {g : UA σ Y.J} (h : Moves B Y Y₂ g) {k : UA σ Y.J}
    (hk : k ∈ KInf σ (reS Y Y₂) B.emb) : g * k * g⁻¹ ∈ KInf σ Y B.emb :=
  ⟨re_mul (re_mul h.1 hk.1) (re_inv h.1), fun w => commute_conj (matC Y.J (B.emb w)) (h.2 w) (hk.2 w)⟩

theorem Moves.down {B : Base F E} {m : ℕ} {Y Y₂ : Spc F E m} {g : UA σ Y.J} (h : Moves B Y Y₂ g) {k : UA σ Y.J}
    (hk : k ∈ KInf σ Y B.emb) : g⁻¹ * k * g⁻¹⁻¹ ∈ KInf σ (reS Y Y₂) B.emb :=
  ⟨re_mul (Y := Y) (re_mul (re_inv h.1) hk.1) (re_inv (re_inv h.1)),
    fun w => commute_conj (matC Y.J (B.emb w)) (inv_rel (matC Y.J (B.emb w)) (h.2 w)) (hk.2 w)⟩

section Pair

variable {n d : ℕ} {X X₂ : Spc F E n} {W W₂ : Spc F E d} {B : Base F E} {M : Model σ X W} {M₂ : Model σ (reS X X₂) (reS W W₂)}
  {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem transK (hO : ArchOp) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') {g h T} (hT : IsArchOp om (g, h) T)
    {x₁ x₂ y₁ y₂} (h1 : x₁ ∈ UAt σ X (evI F)) (h2 : x₂ ∈ UAt σ W (evI F)) (e : (x₁, x₂) * (g, h) = (g, h) * (y₁, y₂))
    {f f₁ : SInf F (Fin n × Fin d)} (ha : Acts (evI F) (om (y₁, y₂)) f f₁) : Acts (evI F) (om (x₁, x₂)) (T f) (T f₁) := by
  obtain ⟨T₁, hT₁, -⟩ := hO F E σ B n d X W M χX χW om r s r' s' hp x₁ h1 x₂ h2
  have a := acts_comp hp (hT.2 f) (hT₁.2 (T f))
  rw [e] at a
  rw [(hQ F _ f _ _).1 _ (acts_comp hp ha (hT.2 f₁)) a]
  exact hT₁.2 _

theorem transL (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s')
    (hp₂ : IsPair B M₂ χX χW om r s r' s') {g h T} (hT : IsArchOp om (g, h) T)
    (hP : (M₂.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) = M.Pol B.ψ B.emb) {γ δ γ₂ δ₂} (hγ : γ ∈ Lines σ X) (hδ : δ ∈ Lines σ W)
    (hγ₂ : γ₂ ∈ Lines σ X) (hδ₂ : δ₂ ∈ Lines σ W) (e : ∀ t, (γ t, δ t) * (g, h) = (g, h) * (γ₂ t, δ₂ t))
    {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M₂.Pol B.ψ B.emb)
    (ha : ActsD (evI F) (fun t => om (γ₂ (Multiplicative.ofAdd t), δ₂ (Multiplicative.ofAdd t))) f f₁) :
    ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), δ (Multiplicative.ofAdd t))) (T f) (T f₁) := by
  have hO' := hO
  choose op hop _ using hO F E σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨z, -, z2, z3⟩ := hL F E σ B n d _ _ M₂ χX χW om r s r' s' hp₂ γ₂ hγ₂ δ₂ hδ₂
    (fun t => op _ (hγ₂.2 _) _ (hδ₂.2 _)) (fun t => hop _ _ _ _) f hf
  obtain ⟨y, -, y2, y3⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp γ hγ δ hδ
    (fun t => op _ (hγ.2 _) _ (hδ.2 _)) (fun t => hop _ _ _ _) (T f) (hP ▸ ⟨f, hf, rfl⟩)
  rw [(hQ F _ f f₁ z).2 _ ha z2, sinf_ext (f := T z) (g := y) fun L => ?_]
  · exact y2
  refine HasDerivAt.unique (z3 (L.comp T)) ?_
  refine (y3 L).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  exact congrArg L ((hQ F _ _ _ _).1 _ (transK hO' hQ hp hT (hγ.2 _) (hδ.2 _) (e _) ((hop _ _ _ _).2 f)) ((hop _ _ _ _).2 _))

theorem quot_trans (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s')
    (hp₂ : IsPair B M₂ χX χW om r s r' s') {g h T} (hg : Moves B X X₂ g) (hT : IsArchOp om (g, h) T)
    (hP : (M₂.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) = M.Pol B.ψ B.emb) {P : Type} [AddCommGroup P] [Module ℂ P]
    {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (q : RealQuot B M om p) : RealQuot B M₂ om (p ∘ₗ (T : _ →ₗ[ℂ] _)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Submodule.map_comp, hP, q.onto]
  · exact fun γ hγ f hf f₁ ha => q.lie _ (conj_line hg.1 hγ) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T f₁)
      (transL hO hL hQ hp hp₂ hT hP (conj_line hg.1 hγ) one_line hγ one_line (fun t => cj1 g (γ t) h) hf ha)
  · exact fun k hk f hf f₁ ha => q.cpt _ (hg.up hk) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T f₁)
      (transK hO hQ hp hT (hg.up hk).1 (one_at _) (cj1 g k h) ha)

theorem exists_linop (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') (i) :
    ∃ A : M.Pol B.ψ B.emb →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ x, A x ∈ M.Pol B.ψ B.emb ∧ ∀ y, RInf B om i x y ↔ y = A x := by
  choose op hop hopP using hO F E σ B n d X W M χX χW om r s r' s' hp
  rcases i with δ | k
  · choose D h3 h4 h5 using hL F E σ B n d X W M χX χW om r s r' s' hp 1 one_line δ δ.2
      (fun t => op 1 (one_at _) _ (δ.2.2 _)) fun t => hop 1 _ _ _
    refine ⟨{ toFun := fun x => D x x.2
              map_add' := fun x y => sinf_ext fun L => ?_
              map_smul' := fun c x => sinf_ext fun L => ?_ }, fun x => ⟨h3 x x.2, fun y =>
      ⟨fun h => ((hQ F _ x.1 (D x x.2) y).2 _ (h4 x x.2) h).symm, fun h => by rw [h]; exact h4 x x.2⟩⟩⟩
    · refine (h5 _ (x + y).2 L).unique ?_
      simp only [Submodule.coe_add, map_add (f := _)]
      exact (h5 x x.2 L).add (h5 y y.2 L)
    · refine (h5 _ (c • x).2 L).unique ?_
      simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]
      exact (h5 x x.2 L).const_smul c
  · exact ⟨(op 1 (one_at _) k k.2.1 : _ →ₗ[ℂ] _) ∘ₗ Submodule.subtype _, fun x => ⟨hopP 1 _ k _ (one_kinf _) k.2 x x.2, fun y =>
      ⟨fun h => ((hQ F _ x.1 _ y).1 _ ((hop 1 (one_at _) k k.2.1).2 x) h).symm,
        fun h => by rw [h]; exact (hop 1 (one_at _) k k.2.1).2 x⟩⟩⟩

end Pair

end PositivityTheory.ThKF

end
end
