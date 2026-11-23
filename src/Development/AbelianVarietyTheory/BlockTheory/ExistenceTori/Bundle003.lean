module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MvPolynomial
open scoped Pointwise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def stdForm (x y : Fin n → E) : E := ∑ j, x j * IsCMField.complexConj E (y j)

def stdMod (E : Type) [Field E] (n : ℕ) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

structure Lat (E : Type) [Field E] (n : ℕ) where
  L : Submodule (𝓞 E) (Fin n → E)
  fg : L.FG
  span_top : Submodule.span E (L : Set (Fin n → E)) = ⊤

omit [NumberField E] [IsCMField E] in
theorem mem_stdMod {x : Fin n → E} : x ∈ stdMod E n ↔ ∀ j, ∃ a : 𝓞 E, (a : E) = x j := by
  simp only [stdMod, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]

omit [NumberField E] [IsCMField E] in
theorem single_mem_stdMod (j : Fin n) : (Pi.single j 1 : Fin n → E) ∈ stdMod E n := by
  rw [mem_stdMod]
  intro i
  by_cases h : i = j
  · subst h
    exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

def Lat.std (E : Type) [Field E] (n : ℕ) : Lat E n where
  L := stdMod E n
  fg := Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  span_top := by
    classical
    rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    simpa using single_mem_stdMod j

def Lat.inter (Λ : Lat E n) : Submodule (𝓞 E) (Fin n → E) := stdMod E n ⊓ Λ.L

def Lat.SelfDual (Λ : Lat E n) : Prop :=
  ∀ x : Fin n → E, x ∈ Λ.L ↔ ∀ y ∈ Λ.L, ∃ a : 𝓞 E, (a : E) = stdForm x y

def EqAtPrime (p : ℕ) (L₁ L₂ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  (∀ x ∈ L₁, ∃ k : ℕ, ¬ p ∣ k ∧ k • x ∈ L₂) ∧ ∀ x ∈ L₂, ∃ k : ℕ, ¬ p ∣ k ∧ k • x ∈ L₁

def Lat.StdAt (Λ : Lat E n) (s : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ s → EqAtPrime p Λ.L (stdMod E n)

def mulStd (E : Type) [Field E] (n N : ℕ) : Submodule (𝓞 E) (Fin n → E) := (N : 𝓞 E) • stdMod E n

def Lat.Admissible (Λ : Lat E n) (M N : ℕ) : Prop :=
  Odd N ∧ M ∣ N ∧ mulStd E n N ≤ Λ.inter

def Lat.cardCenterZero (Λ : Lat E n) (r N : ℕ) : ℕ :=
  (mulStd E n N).toAddSubgroup.relIndex Λ.inter.toAddSubgroup ^ r

def halfPart {H : Host E} (l : Level H) (N : ℕ) : Ideal (𝓞 E) :=
  ⨅ k : ℕ, Ideal.span {(N : 𝓞 E)} ⊔ l.Mb ^ k

def IsUnitary (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Prop := ∀ x y, stdForm (γ x) (γ y) = stdForm x y

def Lat.map (Λ : Lat E n) (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Lat E n where
  L := Λ.L.map (γ.toLinearMap.restrictScalars (𝓞 E))
  fg := Λ.fg.map _
  span_top := by
    have h : ((Λ.L.map (γ.toLinearMap.restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
        γ.toLinearMap '' (Λ.L : Set (Fin n → E)) := rfl
    rw [h, ← Submodule.map_span, Λ.span_top, Submodule.map_top, LinearEquiv.range]

def Lat.InGenus (Λ : Lat E n) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
    IsUnitary γ ∧ EqAtPrime p Λ.L ((Lat.std E n).map γ).L

section Poly

variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

def letter (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (b : Fin n → E) : MvPolynomial (LtN Dw n) c.F :=
  ∑ j, C (embF c σ (b j)) * X ⟨σ, i, j⟩

def symLat (Λ : Lat E n) : Subalgebra (integralClosure ℤ c.F) (MvPolynomial (LtN Dw n) c.F) :=
  Algebra.adjoin (integralClosure ℤ c.F) {P | ∃ σ i, ∃ b ∈ Λ.L, P = letter Dw c σ i b}

def harmSpace (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (MvPolynomial (LtN Dw n) c.F) :=
  HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i)

def harmLat (a : (E →+* ℂ) × ℕ → ℕ) (Λ : Lat E n) : Set (MvPolynomial (LtN Dw n) c.F) :=
  {P | P ∈ harmSpace Dw c a n ∧ P ∈ symLat Dw c Λ}

def push (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  aeval fun ℓ => letter Dw c ℓ.1 ℓ.2.1 (γ (Pi.single ℓ.2.2 1))

end Poly


end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def conjHalf (l : Level H) : Ideal (𝓞 E) := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  have h1 := H.bar_eq (H.bar a)
  have h2 := H.bar_eq a
  rw [h1, h2, IsCMField.complexConj_apply_apply]

theorem bar_mem_of_mem_conjHalf (l : Level H) {a : 𝓞 E} (ha : a ∈ conjHalf l) : H.bar a ∈ l.Mb := by
  obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 ha
  have : H.bar ((H.bar : 𝓞 E →+* 𝓞 E) b) = b := bar_bar H b
  rwa [this]

theorem mul_mem_span_level (l : Level H) {a b : 𝓞 E} (ha : a ∈ l.Mb) (hb : b ∈ conjHalf l) :
    ∃ z : 𝓞 E, a * b = (l.M : 𝓞 E) * z := by
  have h : a * b ∈ Ideal.span {(l.M : 𝓞 E)} := l.prod ▸ Ideal.mul_mem_mul ha hb
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨z, by rw [← hz, mul_comm]⟩

def IsSep (l : Level H) (c : 𝓞 E) : Prop := c ∈ conjHalf l ∧ c - 1 ∈ l.Mb

theorem exists_isSep (l : Level H) : ∃ c, IsSep l c := by
  have h : (1 : 𝓞 E) ∈ l.Mb ⊔ conjHalf l := by
    rw [conjHalf, l.coprime]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h
  refine ⟨b, hb, ?_⟩
  have : b - 1 = -a := by rw [← hab]; ring
  rw [this]; exact neg_mem ha

def sep (l : Level H) : 𝓞 E := (exists_isSep l).choose

theorem sep_spec (l : Level H) : IsSep l (sep l) := (exists_isSep l).choose_spec

variable (D : Datum H) (l : Level H)

abbrev NamedCl : Type := D.La ⧸ (l.Mb • (⊤ : Submodule (𝓞 E) D.La))

abbrev ConjCl : Type := D.La ⧸ (conjHalf l • (⊤ : Submodule (𝓞 E) D.La))

theorem finite_quot (I : Ideal (𝓞 E)) (hI : (l.M : 𝓞 E) ∈ I) :
    Finite (D.La ⧸ (I • (⊤ : Submodule (𝓞 E) D.La))) := by
  haveI := D.fin
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have hM : (l.M : ℤ) ≠ 0 := by have := l.three_le; omega
  refine Module.finite_of_fg_torsion _ fun x => ⟨⟨(l.M : ℤ), mem_nonZeroDivisors_of_ne_zero hM⟩, ?_⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (l.M : ℤ) • (Submodule.Quotient.mk y : D.La ⧸ (I • (⊤ : Submodule (𝓞 E) D.La))) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, natCast_zsmul,
    ← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hI Submodule.mem_top

theorem level_mem_mul : (l.M : 𝓞 E) ∈ l.Mb * conjHalf l := by
  rw [conjHalf, l.prod]; exact Ideal.mem_span_singleton_self _

instance finite_namedCl : Finite (NamedCl D l) := finite_quot D l _
  (Ideal.mul_le_inf (level_mem_mul l)).1

instance finite_conjCl : Finite (ConjCl D l) := finite_quot D l _
  (Ideal.mul_le_inf (level_mem_mul l)).2

theorem ef_smul_eq_zero {a b : 𝓞 E} (ha : a ∈ l.Mb) (hb : b ∈ conjHalf l) (u v : D.La) :
    ((D.EF u ((a * b) • v) : ℤ) : ZMod l.M) = 0 := by
  obtain ⟨z, hz⟩ := mul_mem_span_level l ha hb
  rw [hz, mul_smul, Nat.cast_smul_eq_nsmul, map_nsmul]
  simp

theorem ef_left_zero {c : 𝓞 E} (hc : c ∈ conjHalf l) {u : D.La}
    (hu : u ∈ conjHalf l • (⊤ : Submodule (𝓞 E) D.La)) (v : D.La) :
    ((D.EF u (c • v) : ℤ) : ZMod l.M) = 0 := by
  refine Submodule.smul_induction_on hu (fun m hm w _ => ?_) (fun x y hx hy => ?_)
  · rw [D.adj, ← mul_smul]
    exact ef_smul_eq_zero D l (bar_mem_of_mem_conjHalf l hm) hc w v
  · rw [map_add (f := _), LinearMap.add_apply, Int.cast_add, hx, hy, add_zero]

theorem ef_right_zero {c : 𝓞 E} (hc : c ∈ conjHalf l) (u : D.La) {v : D.La}
    (hv : v ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    ((D.EF u (c • v) : ℤ) : ZMod l.M) = 0 := by
  refine Submodule.smul_induction_on hv (fun m hm w _ => ?_) (fun x y hx hy => ?_)
  · rw [← mul_smul, mul_comm]
    exact ef_smul_eq_zero D l hm hc u w
  · rw [smul_add, map_add (f := _), Int.cast_add, hx, hy, add_zero]

def pairOne (a : ConjCl D l) (x : NamedCl D l) : ZMod l.M :=
  Quotient.liftOn₂' a x (fun u v => ((D.EF u (sep l • v) : ℤ) : ZMod l.M)) (by
    intro u v u' v' hu hv
    have hu' := (Submodule.quotientRel_def _).1 hu
    have hv' := (Submodule.quotientRel_def _).1 hv
    have h1 := ef_left_zero D l (sep_spec l).1 hu' v
    have h2 := ef_right_zero D l (sep_spec l).1 u' hv'
    rw [map_sub, LinearMap.sub_apply, Int.cast_sub, sub_eq_zero] at h1
    rw [smul_sub, map_sub, Int.cast_sub, sub_eq_zero] at h2
    exact h1.trans h2)

def pairing {n : ℕ} (a : Fin n → ConjCl D l) (t : Fin n → NamedCl D l) : ZMod l.M :=
  ∑ b, pairOne D l (a b) (t b)

theorem zeta_level_mem (c : Coeff l) : zeta l.M ∈ c.F := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero hM l.A_pos.ne'
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hM' hk
  have : zeta l.M = zeta l.M' ^ k := by
    rw [zeta, zeta, ← Complex.exp_nat_mul, hk]
    congr 1
    have : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk0
    have : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM
    push_cast
    field_simp
  rw [this]
  exact pow_mem c.zeta_mem k


variable {l} in
def zetaM (c : Coeff l) : c.F := ⟨zeta l.M, zeta_level_mem l c⟩



variable {l}

def eChar (c : Coeff l) {n : ℕ} (a : Fin n → ConjCl D l) (t : Fin n → NamedCl D l) : c.F :=
  zetaM c ^ (pairing D l a t).val

variable {D}

def levPtCl (Xo : Moduli D l) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) (x : NamedCl D l) :
    ptO Xo x0 ⟶ Xo.univ.t.G :=
  Quotient.liftOn' x (fun u => levPt Xo x0 u) (by
    intro u v huv
    have h := (Submodule.quotientRel_def _).1 huv
    have : Xo.univ.eta u = Xo.univ.eta v := by
      have h2 := Xo.univ.eta_add (u - v) v
      rw [sub_add_cancel, Xo.univ.eta_ker _ h, _root_.one_mul] at h2
      exact h2
    simp only [levPt, this])


variable (D l) in
def levelIndex (n : ℕ) : Finset (Fin n → NamedCl D l) := (Set.finite_univ).toFinset

def SpansAtEvery {n : ℕ} (s : Set (Fin n)) (x₀ : Fin n → ConjCl D l) : Prop :=
  ∀ 𝔭 : Ideal (𝓞 E), 𝔭.IsMaximal → conjHalf l ≤ 𝔭 →
    Submodule.span (𝓞 E) (x₀ '' s) ⊔ 𝔭 • (⊤ : Submodule (𝓞 E) (ConjCl D l)) = ⊤

def FirstInv {n : ℕ} (x₀ : Fin n → ConjCl D l) : Prop :=
  D.p + D.q ≤ n ∧ SpansAtEvery {b : Fin n | (b : ℕ) < D.p + D.q} x₀

def RankFull {n : ℕ} (x₀ : Fin n → ConjCl D l) : Prop := SpansAtEvery Set.univ x₀


open Classical in
def Admissible (nV : ℕ) {n : ℕ} (x₀ : Fin n → ConjCl D l) : Prop :=
  if n = nV then RankFull x₀ else FirstInv x₀

def fourier (c : Coeff l) {n : ℕ} (φ : (Fin n → ConjCl D l) → c.F) (t : Fin n → NamedCl D l) : c.F :=
  (Nat.card (Fin n → NamedCl D l) : c.F)⁻¹ *
    ∑ a ∈ (Set.finite_univ : (Set.univ : Set (Fin n → ConjCl D l)).Finite).toFinset, φ a * (eChar D c a t)⁻¹

def indicatorCl (c : Coeff l) {n : ℕ} (x₀ : Fin n → ConjCl D l) : (Fin n → ConjCl D l) → c.F :=
  Set.indicator {x₀} 1




end GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev tyOf (c : Coeff l) (σ : c.F →+* ℂ) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    Fin g → (E →+* ℂ) := fun j => relab c σ (e j).1

abbrev FamAt (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :=
  FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (tyOf c σ e)

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}

variable {F : FamAt Xo c σ e} {r : ℕ}

end GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies
end
end
