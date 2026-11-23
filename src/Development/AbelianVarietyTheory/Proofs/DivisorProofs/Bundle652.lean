module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle506
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422

@[expose] public section

section

set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem mulMat_stdLat_le {F : Type} [Field F] [NumberField F]
    (A : Matrix (Fin 2) (Fin 2) ℤ) :
    _root_.GlobalTheory.HilbFam.mulMat (_root_.GlobalTheory.HilbFam.stdLat F) A ≤
      _root_.GlobalTheory.HilbFam.stdLat F := by
  unfold _root_.GlobalTheory.HilbFam.mulMat
  rintro _ ⟨y, hy, rfl⟩
  unfold _root_.GlobalTheory.HilbFam.stdLat at hy ⊢
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies] at hy ⊢
  intro i
  simp only [LinearMap.coe_restrictScalars, Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hj : y j * (A.map Int.cast) j i = ((A j i : 𝓞 F)) • y j := by
    simp [Algebra.smul_def, mul_comm]
  rw [hj]
  exact Submodule.smul_mem _ _ (hy j (Set.mem_univ j))


set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ)
    (L : _root_.GlobalTheory.HilbFam.Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)),
    _root_.GlobalTheory.HilbFam.HasLevel N L → _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.twist N L α) := by
  intro F _ _ _ N L α hL
  obtain ⟨_, hle⟩ := hL
  unfold _root_.GlobalTheory.HilbFam.HasLevel _root_.GlobalTheory.HilbFam.twist
  refine ⟨fun x hx => Submodule.mem_sup_right ?_, sup_le ?_ (mulMat_stdLat_le _)⟩
  · unfold _root_.GlobalTheory.HilbFam.mulMat
    convert Submodule.mem_map_of_mem hx using 1
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Matrix.natCast_apply] <;>
      rw [Algebra.smul_def, map_natCast, mul_comm]
  · unfold _root_.GlobalTheory.HilbFam.mulMat
    exact (Submodule.map_mono hle).trans (mulMat_stdLat_le _)

end GlobalTheory.HilbFam
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sum_range_triangle {A : Type*} [AddCommMonoid A] (G : ℕ → ℕ → A) (N : ℕ) :
    ∑ P ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (P + 1), G p (P - p) =
      ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), G p r := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨x.2, x.1 - x.2⟩) (fun y _ => ⟨y.1 + y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp at h ⊢ <;> omega
  · rintro ⟨a, b⟩ h
    simp at h ⊢ <;> omega
  · rintro ⟨a, b⟩ h
    simp at h ⊢ <;> omega
  · rintro ⟨a, b⟩ h
    simp at h ⊢ <;> omega
  · rintro ⟨a, b⟩ h
    rfl

theorem Sx.sub_congr {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) {j j' l : ℕ} (hj : j = j') (h : j + l ≤ N)
    (h' : j' + l ≤ N) : x.sub j l h = x.sub j' l h' := by
  subst hj
  rfl

theorem Pair.mul_ev_congr {R : Type} [CommRing R] {J K M : Cx R} (μ : Pair J K M) {E : Spc} {k : ℤ}
    (γ : Cochain ((chains R).obj E) K k) {U : Scheme.{0}} {N : ℕ} (x : Sx E N U) (t tu : ℤ) (b : Sec (J.X t) U)
    {a a' j j' : ℕ} (ha : a = a') (hj : j = j') (hx : j + a ≤ N) (hx' : j' + a' ≤ N)
    (h : t + (-(a : ℤ) + k) = tu) (h' : t + (-(a' : ℤ) + k) = tu) :
    μ.mul U t (-(a : ℤ) + k) tu h b (ev γ a _ rfl U (x.sub j a hx)) =
      μ.mul U t (-(a' : ℤ) + k) tu h' b (ev γ a' _ rfl U (x.sub j' a' hx')) := by
  subst ha hj
  rfl

end GlobalTheory.EtC

theorem GlobalTheory.EtC.Pair.cup_assoc_of_mul_assoc : ∀ (R : Type) [CommRing R] {I J K M M' L : Cx R} (μ : Pair I J M) (ν : Pair M K L) (μ' : Pair J K M') (ν' : Pair I M' L), (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c, ν.mul U st u w h2 (μ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) → ∀ (E : Spc) {n m k nm mk w : ℤ} (h1 : n + m = nm) (h2 : nm + k = w) (h3 : m + k = mk) (h4 : n + mk = w) a b c, ν.cup E h2 (μ.cup E h1 a b) c = ν'.cup E h4 a (μ'.cup E h3 b c) := by
  intro R _ I J K M M' L μ ν μ' ν' hA E n m k nm mk w h1 h2 h3 h4 a b c
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
  obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective c
  obtain ⟨δ, hδ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ h1).1 α β
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ h1).2 α β δ hδ]
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R ν h2).1 δ γ
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R ν h2).2 δ γ ε hε]
  obtain ⟨δ', hδ'⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ' h3).1 β γ
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ' h3).2 β γ δ' hδ']
  obtain ⟨ε', hε'⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R ν' h4).1 α δ'
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R ν' h4).2 α δ' ε' hε']
  suffices hh : ε.1 = ε'.1 by rw [show ε = ε' from Subtype.ext hh]
  apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := L) (n := w)).2.2.1
  intro N s hs U x
  rw [hε N s hs U x, hε' N s hs U x]
  have ss := fun {N' : ℕ} (y : Sx E N' U) => (GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite y).1
  let G : ℕ → ℕ → Sec (L.X s) U := fun p r => if hpr : p + r ≤ N then
    (((mk * (p : ℤ) + k * (r : ℤ)).negOnePow : ℤˣ) : ℤ) •
      ν'.mul U (-(p : ℤ) + n) (-((N - p : ℕ) : ℤ) + mk) s (by omega) (ev α.1 p _ rfl U (x.sub 0 p (by omega)))
        (μ'.mul U (-(r : ℤ) + m) (-((N - p - r : ℕ) : ℤ) + k) (-((N - p : ℕ) : ℤ) + mk) (by omega)
          (ev β.1 r _ rfl U (x.sub p r hpr)) (ev γ.1 (N - p - r) _ rfl U (x.sub (p + r) (N - p - r) (by omega))))
    else 0
  trans ∑ P ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (P + 1), G p (P - p)
  · rw [← Fin.sum_univ_eq_sum_range (fun P => ∑ p ∈ Finset.range (P + 1), G p (P - p)) (N + 1)]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hP := P.isLt

    rw [hδ (P : ℕ) _ _ U (x.sub 0 (P : ℕ) (by omega)), map_sum, LinearMap.sum_apply, Finset.smul_sum,
    ← Fin.sum_univ_eq_sum_range (fun p => G p ((P : ℕ) - p)) ((P : ℕ) + 1)]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp := p.isLt
    simp only [G]
    rw [dite_eq_left (by omega), Units.smul_def, Units.smul_def, map_zsmul, LinearMap.smul_apply, smul_smul,
      ← Units.val_mul, ← Int.negOnePow_add]
    rw [hA (tu := -((N - (p : ℕ) : ℕ) : ℤ) + mk)]
    rotate_left
    · omega
    · omega
    rw [ss, ss, GlobalTheory.EtC.Sx.sub_congr x (show 0 + 0 = 0 from rfl) _ (by omega),
      GlobalTheory.EtC.Sx.sub_congr x (show 0 + (p : ℕ) = p by omega) _ (by omega)]
    rw [GlobalTheory.EtC.Pair.mul_ev_congr μ' γ.1 x _ _ _ (a' := N - (p : ℕ) - ((P : ℕ) - (p : ℕ)))
      (j' := (p : ℕ) + ((P : ℕ) - (p : ℕ))) (by omega) (by omega) _ (by omega) _ (by omega)]
    have hsg : (k * ((P : ℕ) : ℤ) + m * ((p : ℕ) : ℤ)).negOnePow =
        (mk * ((p : ℕ) : ℤ) + k * (((P : ℕ) - (p : ℕ) : ℕ) : ℤ)).negOnePow := by
      congr 1
      rw [Nat.cast_sub (by omega), ← h3]
      ring
    rw [hsg]
  trans ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), G p r
  · exact GlobalTheory.EtC.sum_range_triangle G N
  rw [← Fin.sum_univ_eq_sum_range (fun p => ∑ r ∈ Finset.range (N - p + 1), G p r) (N + 1)]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.isLt

  rw [hδ' (N - (p : ℕ)) _ _ U (x.sub (p : ℕ) (N - (p : ℕ)) (by omega)), map_sum, Finset.smul_sum,
  ← Fin.sum_univ_eq_sum_range (fun r => G p r) (N - (p : ℕ) + 1)]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr := r.isLt
  simp only [G]
  rw [dite_eq_left (by omega), Units.smul_def, Units.smul_def, map_zsmul, smul_smul, ← Units.val_mul,
    ← Int.negOnePow_add, ss, ss]
  rfl
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.ProdStep

theorem mem_span_prod {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] (a₁ : A₁) (a₂ : A₂) (x : A₁ × A₂) :
    x ∈ Ideal.span {((a₁, a₂) : A₁ × A₂)} ↔ x.1 ∈ Ideal.span {a₁} ∧ x.2 ∈ Ideal.span {a₂} := by
  simp only [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨⟨c.1, rfl⟩, ⟨c.2, rfl⟩⟩
  · rintro ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩
    exact ⟨(c₁, c₂), Prod.ext h₁ h₂⟩

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Functor.map_comp, ← Spec.map_comp]

theorem prodStep : ∀ (q : ℕ) (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂] (f : B) (I J : Ideal B) (n i : ℤ) (y : Ht q (sp B) n i), IsCoprime I J → (∀ a : A₁, ∃ b : B, a - algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f}) → (∀ b : B, algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f} ↔ b ∈ I) → (∀ a : A₂, ∃ b : B, a - algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f}) → (∀ b : B, algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f} ↔ b ∈ J) → pull _ (spMap (algebraMap B A₁)) _ _ y = 0 → pull _ (spMap (algebraMap B A₂)) _ _ y = 0 → (∀ a : A₁ × A₂, ∃ b : B, a - algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f}) ∧ (∀ b : B, algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f} ↔ b ∈ I ⊓ J) ∧ pull _ (spMap (algebraMap B (A₁ × A₂))) _ _ y = 0 := by
  intro q B A₁ A₂ _ _ _ _ _ f I J n i y hIJ hs₁ hk₁ hs₂ hk₂ hy₁ hy₂
  have hf : algebraMap B (A₁ × A₂) f = (algebraMap B A₁ f, algebraMap B A₂ f) := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro a
    obtain ⟨u, hu, v, hv, huv⟩ := Ideal.isCoprime_iff_exists.1 hIJ
    obtain ⟨b₁, hb₁⟩ := hs₁ a.1
    obtain ⟨b₂, hb₂⟩ := hs₂ a.2
    refine ⟨b₁ * v + b₂ * u, ?_⟩
    rw [hf, mem_span_prod]
    constructor
    · have e : a.1 - algebraMap B A₁ (b₁ * v + b₂ * u) = (a.1 - algebraMap B A₁ b₁) + algebraMap B A₁ ((b₁ - b₂) * u) := by
        have : b₁ * v + b₂ * u = b₁ - (b₁ - b₂) * u := by linear_combination b₁ * huv
        rw [this, map_sub]; ring
      show a.1 - algebraMap B A₁ (b₁ * v + b₂ * u) ∈ _
      rw [e]
      exact Ideal.add_mem _ hb₁ ((hk₁ _).2 (I.mul_mem_left _ hu))
    · have e : a.2 - algebraMap B A₂ (b₁ * v + b₂ * u) = (a.2 - algebraMap B A₂ b₂) + algebraMap B A₂ ((b₂ - b₁) * v) := by
        have : b₁ * v + b₂ * u = b₂ - (b₂ - b₁) * v := by linear_combination b₂ * huv
        rw [this, map_sub]; ring
      show a.2 - algebraMap B A₂ (b₁ * v + b₂ * u) ∈ _
      rw [e]
      exact Ideal.add_mem _ hb₂ ((hk₂ _).2 (J.mul_mem_left _ hv))
  · intro b
    rw [hf, mem_span_prod, Ideal.mem_inf]
    exact and_congr (hk₁ b) (hk₂ b)
  · have hbij := GlobalTheory.EtC.ProdCoh.ht_prod_bijective q A₁ A₂ n i
    apply hbij.1
    have e₁ : (RingHom.fst A₁ A₂).comp (algebraMap B (A₁ × A₂)) = algebraMap B A₁ := by ext; rfl
    have e₂ : (RingHom.snd A₁ A₂).comp (algebraMap B (A₁ × A₂)) = algebraMap B A₂ := by ext; rfl
    simp only [map_zero]
    rw [← pull_comp, ← pull_comp, ← spMap_comp, ← spMap_comp, e₁, e₂, hy₁, hy₂]

end GlobalTheory.EtC.ProdStep
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.ArtCoh

theorem ht_subsingleton_of_ringEquiv (q : ℕ) {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (n i : ℤ)
    [h : Subsingleton (Ht q (sp R) n i)] : Subsingleton (Ht q (sp S) n i) := by
  have hid : spMap (e : R →+* S) ≫ spMap (e.symm : S →+* R) = 𝟙 (sp S) := by
    rw [← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (e : R →+* S).comp (e.symm : S →+* R) = RingHom.id S := by ext x; simp
    rw [this]
    simp
  constructor
  intro x y
  have hx : pull _ (spMap (e : R →+* S)) _ _ (pull _ (spMap (e.symm : S →+* R)) _ _ x) = x := by
    rw [← pull_comp, hid, pull_id]
  have hy : pull _ (spMap (e : R →+* S)) _ _ (pull _ (spMap (e.symm : S →+* R)) _ _ y) = y := by
    rw [← pull_comp, hid, pull_id]
  rw [← hx, ← hy, Subsingleton.elim (pull _ (spMap (e.symm : S →+* R)) _ _ x)
    (pull _ (spMap (e.symm : S →+* R)) _ _ y)]

theorem ht_subsingleton_prod (q : ℕ) (A B : Type) [CommRing A] [CommRing B] (n i : ℤ)
    [Subsingleton (Ht q (sp A) n i)] [Subsingleton (Ht q (sp B) n i)] : Subsingleton (Ht q (sp (A × B)) n i) := by
  constructor
  intro x y
  exact (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q A B n i).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

theorem ht_subsingleton_of_subsingleton (q : ℕ) (Z : Type) [CommRing Z] [Subsingleton Z] (n i : ℤ) :
    Subsingleton (Ht q (sp Z) n i) := by
  have hfs : RingHom.fst Z Z = RingHom.snd Z Z := by ext x; exact Subsingleton.elim _ _
  constructor
  intro a b
  obtain ⟨x, hx⟩ := (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q Z Z n i).2 (a, b)
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [hfs] at h1
  rw [← h1, ← h2]

theorem ht_subsingleton_pi (q : ℕ) (n i : ℤ) (ι : Type) [Finite ι] : ∀ (R : ι → Type) [∀ j, CommRing (R j)],
    (∀ j, Subsingleton (Ht q (sp (R j)) n i)) → Subsingleton (Ht q (sp (∀ j, R j)) n i) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro R _ hR
    have := ih (fun a => R (e a)) (fun a => hR (e a))
    exact ht_subsingleton_of_ringEquiv q (RingEquiv.piCongrLeft R e) n i
  | h_empty =>
    intro R _ _
    exact ht_subsingleton_of_subsingleton q _ n i
  | h_option ih =>
    intro R _ hR
    have h1 := hR none
    have h2 := ih (fun a => R (some a)) (fun a => hR (some a))
    have := ht_subsingleton_prod q (R none) (∀ a, R (some a)) n i
    exact ht_subsingleton_of_ringEquiv q (RingEquiv.piOptionEquivProd (R := R)).symm n i

theorem ht_subsingleton_artinian : ∀ (q : ℕ) (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (n i : ℤ),
    (∀ M : MaximalSpectrum K, Subsingleton (Ht q (sp (K ⧸ M.asIdeal)) n i)) → Subsingleton (Ht q (sp K) n i) := by
  intro q K _ _ _ n i h
  have := ht_subsingleton_pi q n i (MaximalSpectrum K) (fun M => K ⧸ M.asIdeal) h
  exact ht_subsingleton_of_ringEquiv q (IsArtinianRing.equivPi K).toRingEquiv.symm n i

end GlobalTheory.EtC.ArtCoh
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.LaurentFinite

theorem spMap_comp_eq_id {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : B →+* A)
    (h : g.comp f = RingHom.id A) : spMap g ≫ spMap f = 𝟙 (sp A) := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  simp

theorem subsingleton_of_retract (q : ℕ) (n i : ℤ) {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (g : B →+* A) (h : g.comp f = RingHom.id A)
    (hB : Subsingleton (Ht q (sp B) n i)) : Subsingleton (Ht q (sp A) n i) := by
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : Ht q (sp A) n i, pull _ (spMap g) _ _ (pull _ (spMap f) _ _ z) = z := by
    intro z
    rw [← pull_comp, spMap_comp_eq_id f g h, pull_id]
  rw [← key x, ← key y, Subsingleton.elim (pull _ (spMap f) _ _ x) (pull _ (spMap f) _ _ y)]

theorem subsingleton_of_ringEquiv (q : ℕ) (n i : ℤ) {A B : Type} [CommRing A] [CommRing B]
    (e : A ≃+* B) (hB : Subsingleton (Ht q (sp B) n i)) : Subsingleton (Ht q (sp A) n i) :=
  subsingleton_of_retract q n i e.toRingHom e.symm.toRingHom (by ext x; simp) hB

theorem subsingleton_of_subsingleton (q : ℕ) (n i : ℤ) (T : Type) [CommRing T] [Subsingleton T] :
    Subsingleton (Ht q (sp T) n i) := by
  refine ⟨fun a b => ?_⟩
  have hfs : RingHom.fst T T = RingHom.snd T T := RingHom.ext fun _ => Subsingleton.elim _ _
  obtain ⟨x, hx⟩ := (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q T T n i).2 (a, b)
  simp only [Prod.mk.injEq] at hx
  rw [← hx.1, ← hx.2, hfs]

instance laurent_subsingleton (T : Type) [CommRing T] [Subsingleton T] :
    Subsingleton (LaurentPolynomial T) := by
  refine subsingleton_of_zero_eq_one ?_
  rw [← map_one (LaurentPolynomial.C (R := T)), Subsingleton.elim (1 : T) 0, map_zero]

end GlobalTheory.EtC.LaurentFinite

namespace GlobalTheory.EtC.LaurentFinite

noncomputable def laurentProd (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] :
    LaurentPolynomial (T₁ × T₂) →+* LaurentPolynomial T₁ × LaurentPolynomial T₂ :=
  RingHom.prod (AddMonoidAlgebra.mapRingHom ℤ (RingHom.fst T₁ T₂))
    (AddMonoidAlgebra.mapRingHom ℤ (RingHom.snd T₁ T₂))

theorem laurentProd_C_mul_T (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] (c : T₁ × T₂) (n : ℤ) :
    laurentProd T₁ T₂ (LaurentPolynomial.C c * LaurentPolynomial.T n) =
      (LaurentPolynomial.C c.1 * LaurentPolynomial.T n, LaurentPolynomial.C c.2 * LaurentPolynomial.T n) := by
  simp only [← LaurentPolynomial.single_eq_C_mul_T, laurentProd, RingHom.prod_apply,
    AddMonoidAlgebra.mapRingHom_single, RingHom.coe_fst, RingHom.coe_snd]

theorem laurentProd_injective (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] :
    Function.Injective (laurentProd T₁ T₂) := by
  intro x y h
  simp only [laurentProd, RingHom.prod_apply, Prod.mk.injEq] at h
  ext m
  all_goals
    have h1 := congrArg (fun z => AddMonoidAlgebra.coeff z m) h.1
    have h2 := congrArg (fun z => AddMonoidAlgebra.coeff z m) h.2
    simp only [AddMonoidAlgebra.coeff_mapRingHom, RingHom.coe_fst, RingHom.coe_snd] at h1 h2
    assumption

end GlobalTheory.EtC.LaurentFinite

namespace GlobalTheory.EtC.LaurentFinite

theorem laurentProd_surjective (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] :
    Function.Surjective (laurentProd T₁ T₂) := by
  have hl : ∀ f : LaurentPolynomial T₁, (f, 0) ∈ (laurentProd T₁ T₂).range := by
    intro f
    induction f using LaurentPolynomial.induction_on' with
    | add p q hp hq => simpa using add_mem hp hq
    | C_mul_T n a =>
      refine ⟨LaurentPolynomial.C (a, 0) * LaurentPolynomial.T n, ?_⟩
      rw [laurentProd_C_mul_T]; simp
  have hr : ∀ g : LaurentPolynomial T₂, (0, g) ∈ (laurentProd T₁ T₂).range := by
    intro g
    induction g using LaurentPolynomial.induction_on' with
    | add p q hp hq => simpa using add_mem hp hq
    | C_mul_T n a =>
      refine ⟨LaurentPolynomial.C (0, a) * LaurentPolynomial.T n, ?_⟩
      rw [laurentProd_C_mul_T]; simp
  rintro ⟨f, g⟩
  have := add_mem (hl f) (hr g)
  simpa using this

theorem subsingleton_laurent_prod (q : ℕ) (n i : ℤ) (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂]
    (h₁ : Subsingleton (Ht q (sp (LaurentPolynomial T₁)) n i))
    (h₂ : Subsingleton (Ht q (sp (LaurentPolynomial T₂)) n i)) :
    Subsingleton (Ht q (sp (LaurentPolynomial (T₁ × T₂))) n i) := by
  let e := RingEquiv.ofBijective (laurentProd T₁ T₂)
    ⟨laurentProd_injective T₁ T₂, laurentProd_surjective T₁ T₂⟩
  refine subsingleton_of_ringEquiv q n i e ⟨fun x y => ?_⟩
  exact (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q _ _ n i).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

end GlobalTheory.EtC.LaurentFinite


open GlobalTheory.EtC.LaurentFinite in
theorem GlobalTheory.EtC.laurent_vanishing_finite : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 2 ≤ s → s < n → Subsingleton (Ht q (sp (LaurentPolynomial T)) s i) := by
  intro q _ n hyp A _ _ hA hq
  refine GlobalTheory.T.finiteAlgebra_strictlyHenselian_induction A hA (fun T _ _ => ∀ s i : ℤ, 2 ≤ s → s < n →
      Subsingleton (Ht q (sp (LaurentPolynomial T)) s i)) ?_ ?_ ?_ ?_
  · intro T T' _ _ _ _ e hT s i h2 hs
    exact subsingleton_of_ringEquiv q s i
      (AddMonoidAlgebra.mapRingEquiv ℤ e.symm.toRingEquiv) (hT s i h2 hs)
  · intro T _ _ _ s i _ _
    exact subsingleton_of_subsingleton q s i _
  · intro T₁ T₂ _ _ _ _ _ _ h₁ h₂ s i h2 hs
    exact subsingleton_laurent_prod q s i T₁ T₂ (h₁ s i h2 hs) (h₂ s i h2 hs)
  · intro T _ _ hfin hT s i h2 hs
    haveI : IsNoetherian A T := isNoetherian_of_isNoetherianRing_of_finite A T
    haveI : IsNoetherianRing T := isNoetherian_of_tower A inferInstance
    have hqT : IsUnit (q : T) := by
      simpa using hq.map (algebraMap A T)
    exact hyp T hT hqT s i h2 hs
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b := by
  first | (exact @GlobalTheory.EtC.exactIff) | (exact GlobalTheory.EtC.exactIff) | (intros; apply GlobalTheory.EtC.exactIff  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem cup_natural_in_pairing : ∀ (R : Type) [CommRing R] {I J K I' J' K' : Cx R} (μ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u : K ⟶ K'), μ.Compat ν f g u → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) a b, cpush _ u k (μ.cup E hk a b) = ν.cup E hk (cpush _ f n a) (cpush _ g m b) := by
  intro R _ I J K I' J' K' μ ν f g u hc E n m k hk a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ hk).1 α β
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ hk).2 α β γ hγ]
  simp only [cpush, cpost_mk]
  refine ((GlobalTheory.T.cup_eq_class_of_isAW R ν hk).2 _ _ _ ?_).symm
  intro N w h U x
  have hm := fun {L L' : Cx R} (φ : L ⟶ L') {d : ℤ} (c : Cochain ((chains R).obj E) L d) p s hs U x =>
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := L) (n := d)).2.2.2.2 φ c p s hs U x
  change ev (γ.1.comp (Cochain.ofHom u) (add_zero k)) N w h U x = _
  rw [hm, hγ N w h U x]
  refine (map_sum ((u.f w).hom.app (op U)).hom _ _).trans ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  change Sec.map (u.f w) _ = _ • ν.mul U _ _ w _ (ev (α.1.comp (Cochain.ofHom f) (add_zero n)) _ _ _ U _) (ev (β.1.comp (Cochain.ofHom g) (add_zero m)) _ _ _ U _)
  rw [hm, hm, Units.smul_def, Units.smul_def, ← hc]
  exact map_zsmul ((u.f w).hom.app (op U)).hom _ _

end GlobalTheory
end
