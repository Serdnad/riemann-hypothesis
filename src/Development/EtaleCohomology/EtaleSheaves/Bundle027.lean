module

public import Development.EtaleCohomology.EtaleSheaves.Bundle012
public import Development.EtaleCohomology.EtaleSheaves.Bundle013
public import Development.EtaleCohomology.TateTwists.Bundle015
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Development.EtaleCohomology.EtaleSheaves.LineHigh
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2.WhitneyPf

theorem alg {A : Type*} [CommRing A] (C D : ℕ → A) (x : A) (a b : ℕ) (hC : ∀ i, a < i → C i = 0)
    (hD : ∀ j, b < j → D j = 0) :
    ∑ k ∈ Finset.range (a + b + 1), (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, C p.1 * D p.2) * x ^ (a + b - k) =
      (∑ i ∈ Finset.range (a + 1), C i * x ^ (a - i)) * (∑ j ∈ Finset.range (b + 1), D j * x ^ (b - j)) := by
  set f : ℕ → ℕ → A := fun i j => C i * D j * x ^ (a + b - (i + j)) with hf
  have h1 : ∀ k, (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, C p.1 * D p.2) * x ^ (a + b - k) =
      ∑ i ∈ Finset.range (k + 1), f i (k - i) := by
    intro k
    rw [Finset.sum_mul, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ f k]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [hf, hp]
  simp_rw [h1]
  rw [Finset.sum_range_diag_flip (a + b + 1) f, Finset.sum_mul_sum]
  have h2 : ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), C i * x ^ (a - i) * (D j * x ^ (b - j)) =
      ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), f i j := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hi hj
    simp only [hf]
    rw [show a + b - (i + j) = (a - i) + (b - j) by omega, pow_add]; ring
  rw [h2]
  symm
  calc ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), f i j
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (a + b + 1 - i), f i j := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_subset ?_ ?_
        · simp only [Finset.mem_range] at hi
          intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
        · intro j _ hnj
          simp only [Finset.mem_range] at hnj
          simp only [hf]; rw [hD j (by omega)]; ring
    _ = ∑ i ∈ Finset.range (a + b + 1), ∑ j ∈ Finset.range (a + b + 1 - i), f i j := by
        refine Finset.sum_subset ?_ ?_
        · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
        · intro i _ hni
          simp only [Finset.mem_range] at hni
          refine Finset.sum_eq_zero fun j _ => ?_
          simp only [hf]; rw [hC i (by omega)]; ring

variable {q : ℕ}

def ccup {E : Spc} {i j k : ℕ} (a : Ht q E (2 * i) i) (b : Ht q E (2 * j) j) (hk : i + j = k) : Ht q E (2 * k) k :=
  (cup q a b).cast (by subst hk; push_cast; ring) (by subst hk; push_cast; ring)

theorem ι_ccup (P : Collected q) {E : Spc} (h : Inv q E) {i j k : ℕ} (a : Ht q E (2 * i) i) (b : Ht q E (2 * j) j)
    (hk : i + j = k) : P.ι h k (ccup a b hk) = P.ι h i a * P.ι h j b := by
  subst hk; exact P.ι_mul h i j a b

theorem cast_zero {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn; subst hi; rfl

theorem pull_cast {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast (q := q) (E := E) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem ccup_zero_left {E : Spc} {i j k : ℕ} (b : Ht q E (2 * j) j) (hk : i + j = k) :
    ccup (0 : Ht q E (2 * i) i) b hk = 0 := by
  unfold ccup; rw [map_zero, AddMonoidHom.zero_apply, cast_zero]

theorem ccup_zero_right {E : Spc} {i j k : ℕ} (a : Ht q E (2 * i) i) (hk : i + j = k) :
    ccup a (0 : Ht q E (2 * j) j) hk = 0 := by
  unfold ccup; rw [map_zero, cast_zero]

section
variable [NeZero q]

theorem pull_ccup (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') {i j k : ℕ} (a : Ht q E' (2 * i) i)
    (b : Ht q E' (2 * j) j) (hk : i + j = k) : pull _ f _ _ (ccup a b hk) = ccup (pull _ f _ _ a) (pull _ f _ _ b) hk := by
  subst hk; unfold ccup; rw [pull_cast, (hA q).1]

theorem pull_cpow (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') (x : Ht q E' 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast, (hA q).2.1 f hE']
  | succ k ih => rw [cpow_succ, cpow_succ, pull_cast, (hA q).1, ih]

def yExpr {E E' : Spc} (g : E' ⟶ E) (L : E' ⟶ ofCat (glCat 1)) (c : ∀ j : ℕ, Ht q E (2 * j) j) (a : ℕ) :
    Ht q E' (2 * a) a :=
  ∑ j : Fin (a + 1), ccup (pull _ g _ _ (c j)) (cpow q (c1 q L) (a - j)) (by have := j.isLt; omega)

theorem ι_yExpr (P : Collected q) {E E' : Spc} (hE : Inv q E) (hE' : Inv q E') (g : E' ⟶ E) (L : E' ⟶ ofCat (glCat 1))
    (c : ∀ j : ℕ, Ht q E (2 * j) j) (a : ℕ) :
    P.ι hE' a (yExpr g L c a) = ∑ j ∈ Finset.range (a + 1), P.map g hE' hE (P.ι hE j (c j)) * P.deg1 hE' (c1 q L) ^ (a - j) := by
  unfold yExpr

  rw [map_sum, ← Fin.sum_univ_eq_sum_range (fun j => P.map g hE' hE (P.ι hE j (c j)) * P.deg1 hE' (c1 q L) ^ (a - j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ι_ccup, P.map_ι, P.ι_cpow]

theorem pull_yExpr (hA : DivisorNaturality) {E E' E'' : Spc} (f : E'' ⟶ E') (hE' : Inv q E') (g : E' ⟶ E)
    (L : E' ⟶ ofCat (glCat 1)) (c : ∀ j : ℕ, Ht q E (2 * j) j) (a : ℕ) :
    pull _ f _ _ (yExpr g L c a) = yExpr (f ≫ g) (f ≫ L) c a := by
  unfold yExpr

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_ccup hA, pull_cpow hA f hE', (hA q).2.2.1 f L hE', pull_comp]

theorem yExpr_eq_zero (P : Collected q) {E : Spc} (h : Inv q E) {a : ℕ} (V : E ⟶ ofCat (glCat a))
    (c : ∀ j : ℕ, Ht q E (2 * j) j) (hc : IsChern P h V c) : yExpr (PB.pr V) (PB.line V) c a = 0 := by
  have := ι_yExpr P h (inv_of (PB.pr V) h) (PB.pr V) (PB.line V) c a
  rw [hc.2.2] at this
  rw [← P.π_ι (inv_of (PB.pr V) h) a (yExpr (PB.pr V) (PB.line V) c a), this, map_zero]

end

def eExpr {E : Spc} (c d : ∀ j : ℕ, Ht q E (2 * j) j) (k : ℕ) : Ht q E (2 * k) k :=
  ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal k).attach,
    ccup (c p.1.1) (d p.1.2) (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2)

theorem ι_eExpr (P : Collected q) {E : Spc} (h : Inv q E) (c d : ∀ j : ℕ, Ht q E (2 * j) j) (k : ℕ) :
    P.ι h k (eExpr c d k) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, P.ι h p.1 (c p.1) * P.ι h p.2 (d p.2) := by
  unfold eExpr

  rw [map_sum, ← Finset.sum_attach (Finset.HasAntidiagonal.antidiagonal k)
  (fun p => P.ι h p.1 (c p.1) * P.ι h p.2 (d p.2))]
  exact Finset.sum_congr rfl fun p _ => ι_ccup P h _ _ _

end LateralTheory.E.D2.WhitneyPf

namespace LateralTheory.E.D2
open WhitneyPf

theorem LeafWhitney_of (hG : LeafGeom) (hC2 : LeafCover2) (hS : LeafA6supp) (hA : LeafA6nat) : LeafWhitney := by
  intro q _ P E h a b V W c d hc hd
  classical
  have he := ι_eExpr P h c d
  refine ⟨eExpr c d, ⟨?_, ?_, ?_⟩, he⟩
  · rw [he]; simp [hc.1, hd.1]
  · intro j hj
    unfold eExpr
    refine Finset.sum_eq_zero fun p _ => ?_
    have hp := Finset.HasAntidiagonal.mem_antidiagonal.1 p.2
    by_cases ha : a < p.1.1
    · rw [hc.2.1 _ ha, ccup_zero_left]
    · rw [hd.2.1 _ (by omega), ccup_zero_right]
  · have hX := inv_of (PB.pr (bsumOf V W)) h
    obtain ⟨U₁, U₂, f₁, f₂, p₁, p₂, m₁, m₂, lc, e1, e2, e3, e4⟩ := hG V W
    have hcov := hC2 (ZMod q) f₁ f₂ m₁ m₂ lc
    have hy : pull _ f₁ _ _ (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) c a) = 0 := by
      rw [pull_yExpr hA f₁ hX, ← e1, ← e2, ← pull_yExpr hA p₁ (inv_of (PB.pr V) h), yExpr_eq_zero P h V c hc,
        map_zero]
    have hz : pull _ f₂ _ _ (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) d b) = 0 := by
      rw [pull_yExpr hA f₂ hX, ← e3, ← e4, ← pull_yExpr hA p₂ (inv_of (PB.pr W) h), yExpr_eq_zero P h W d hd,
        map_zero]
    have h0 := hS q f₁ f₂ hcov _ _ hy hz
    have key : P.ι hX (a + b) (ccup (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) c a)
        (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) d b) rfl) = 0 := by
      unfold ccup; rw [h0, cast_zero, map_zero]
    rw [ι_ccup, ι_yExpr P h hX, ι_yExpr P h hX,
      ← alg (fun i => P.map (PB.pr (bsumOf V W)) hX h (P.ι h i (c i)))
        (fun j => P.map (PB.pr (bsumOf V W)) hX h (P.ι h j (d j))) _ a b
        (fun i hi => by simp only [hc.2.1 i hi, map_zero])
        (fun j hj => by simp only [hd.2.1 j hj, map_zero])] at key
    refine Eq.trans ?_ key
    refine Finset.sum_congr rfl fun k _ => ?_

    rw [he, map_sum]
    simp only [map_mul]

end LateralTheory.E.D2
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.E.LeafTensFactorPf

theorem lift_lof {R : Type} [CommRing R] {I J T : Cx R} (τ : Pair I J T) (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    τ.lift U w (DirectSum.of (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)
      ⟨(s, t), hw⟩ (a ⊗ₜ b)) = τ.mul U s t w hw a b := by
  classical
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  simp only [Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]

theorem uniq_mul {R : Type} [CommRing R] {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) {M : Shv R}
    (ψ ψ' : ∀ U : Scheme.{0}, Sec (T.X w) U →+ Sec M U)
    (hψ : ∀ {V U : Scheme.{0}} (g : V ⟶ U) y, Sec.res g (ψ U y) = ψ V (Sec.res g y))
    (hψ' : ∀ {V U : Scheme.{0}} (g : V ⟶ U) y, Sec.res g (ψ' U y) = ψ' V (Sec.res g y))
    (h : ∀ U s t (hw : s + t = w) a b, ψ U (τ.mul U s t w hw a b) = ψ' U (τ.mul U s t w hw a b))
    (U : Scheme.{0}) (y : Sec (T.X w) U) : ψ U y = ψ' U y := by
  have hl : ∀ V (x : Tens I J V w), ψ V (τ.lift V w x) = ψ' V (τ.lift V w x) := by
    intro V x
    classical
    induction x using DirectSum.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _)]; rw [ha, hb]
    | of p z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _)]; rw [ha, hb]
      | tmul a c =>
        obtain ⟨⟨s, t⟩, hw⟩ := p
        rw [lift_lof]
        exact h V s t hw a c
  apply LateralTheory.EtaleFoundations.TensFam.sep M
  obtain ⟨S, hS, h1⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := h1 V g hg
  rw [hψ, hψ', ← hx, hl]

theorem secMap_nat {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map f y) = Sec.map f (Sec.res g y) := by
  have := f.hom.naturality g.op
  exact (congrArg (fun φ => (ModuleCat.Hom.hom φ) y) this).symm

theorem addHom_usmul {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B) (n : ℤˣ) (x : A) :
    φ (n • x) = n • φ x := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

end LateralTheory.E.LeafTensFactorPf

namespace LateralTheory.E.LeafTensFactorPf

theorem phi_exists {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (ν : Pair I J K) (w : ℤ) :
    ∃ φ : ∀ U : Scheme.{0}, Sec (T.X w) U →+ Sec (K.X w) U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) ∧
      ∀ U s t (hw : s + t = w) a b, φ U (τ.mul U s t w hw a b) = ν.mul U s t w hw a b := by
  obtain ⟨φ, h1, h2⟩ := LateralTheory.EtaleFoundations.etale_tensor_hom_descends_along_tensor_pairing R R τ hτ w (K.X w)
    (fun U => (ν.lift U w).toAddMonoidHom) (fun V U g x => LateralTheory.EtaleFoundations.TensFam.lift_res ν g w x)
  refine ⟨φ, h1, fun U s t hw a b => ?_⟩
  have := h2 U (DirectSum.of _ ⟨(s, t), hw⟩ (a ⊗ₜ b))
  rw [lift_lof] at this
  rw [this]
  exact lift_lof ν U s t w hw a b

theorem phi_smul {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (ν : Pair I J K) (w : ℤ)
    (φ : ∀ U : Scheme.{0}, Sec (T.X w) U →+ Sec (K.X w) U)
    (h1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y))
    (h2 : ∀ U s t (hw : s + t = w) a b, φ U (τ.mul U s t w hw a b) = ν.mul U s t w hw a b)
    (U : Scheme.{0}) (r : ULift.{1} R) (y : Sec (T.X w) U) : φ U (r • y) = r • φ U y := by
  refine uniq_mul τ hτ w (fun U => (φ U).comp (DistribSMul.toAddMonoidHom _ r))
    (fun U => (DistribSMul.toAddMonoidHom _ r).comp (φ U)) ?_ ?_ ?_ U y
  · intro V U g y
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [h1]; congr 1; exact map_smul _ r y
  · intro V U g y
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [← h1]; exact map_smul _ r _
  · intro U s t hw a b
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [← LinearMap.map_smul₂, h2, h2, LinearMap.map_smul₂]

def toHom {R : Type} [CommRing R] {F G : Shv R} (φ : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (hnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y))
    (hsm : ∀ U (r : ULift.{1} R) y, φ U (r • y) = r • φ U y) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom { toFun := φ (unop U), map_add' := map_add _, map_smul' := hsm (unop U) }
      naturality := fun U V g => by
        ext y
        exact (hnat _ _ g.unop y).symm }

theorem sheafHom_ext {R : Type} [CommRing R] {F G : Shv R} (f g : F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (y : Sec F U), Sec.map f y = Sec.map g y) : f = g := by
  apply Sheaf.hom_ext
  ext U y
  exact h (unop U) y

theorem factor {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (ν : Pair I J K) :
    ∃ u : T ⟶ K, τ.Compat ν (𝟙 I) (𝟙 J) u := by
  choose φ h1 h2 using fun w => phi_exists τ hτ ν w
  have hsm : ∀ w U (r : ULift.{1} R) y, φ w U (r • y) = r • φ w U y :=
    fun w => phi_smul τ hτ ν w (φ w) (h1 w) (h2 w)
  refine ⟨{ f := fun w => toHom (φ w) (h1 w) (hsm w), comm' := ?_ }, ?_⟩
  · intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    apply sheafHom_ext
    intro U y
    show Sec.map (K.d i (i + 1)) (φ i U y) = φ (i + 1) U (Sec.map (T.d i (i + 1)) y)
    refine uniq_mul τ hτ i (M := K.X (i + 1))
      (fun U => ((K.d i (i + 1)).hom.app (op U)).hom.toAddMonoidHom.comp (φ i U))
      (fun U => (φ (i + 1) U).comp ((T.d i (i + 1)).hom.app (op U)).hom.toAddMonoidHom) ?_ ?_ ?_ U y
    · intro V U g y
      show Sec.res g (Sec.map (K.d i (i + 1)) (φ i U y)) = Sec.map (K.d i (i + 1)) (φ i V (Sec.res g y))
      rw [secMap_nat, h1]
    · intro V U g y
      show Sec.res g (φ (i + 1) U (Sec.map (T.d i (i + 1)) y)) = φ (i + 1) V (Sec.map (T.d i (i + 1)) (Sec.res g y))
      rw [h1, secMap_nat]
    · intro U s t hw a b
      show Sec.map (K.d i (i + 1)) (φ i U (τ.mul U s t i hw a b)) = φ (i + 1) U (Sec.map (T.d i (i + 1)) (τ.mul U s t i hw a b))
      rw [h2, ν.leibniz, τ.leibniz, map_add (f := _), addHom_usmul, h2, h2]
  · intro U s t w hw a b
    rw [LateralTheory.E.LeafTwPairHtpyPf.secMap_id_f, LateralTheory.E.LeafTwPairHtpyPf.secMap_id_f]
    exact h2 w U s t hw a b

end LateralTheory.E.LeafTensFactorPf

theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor_of : LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor := by
  intro R _ I J T K τ hτ ν
  exact LateralTheory.E.LeafTensFactorPf.factor τ hτ ν
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwResHtpyPf

theorem res_isKInj (R : Type) [CommRing R] (F : Shv R) : (res R F).IsKInjective := by
  unfold res InjectiveResolution.cochainComplex
  infer_instance

theorem htpy_of_qiso {C : Type*} [Category C] [Abelian C] {K L I : CochainComplex C ℤ}
    (f : K ⟶ L) [QuasiIso f] [I.IsKInjective] (u u' : L ⟶ I) (h : f ≫ u = f ≫ u') :
    Nonempty (Homotopy u u') := by
  have hY := IsKInjective.rightOrthogonal I
  rw [← ObjectProperty.isLocal_trW] at hY
  have hf : (HomotopyCategory.subcategoryAcyclic C).trW
      ((HomotopyCategory.quotient C _).map f) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      HomotopyCategory.quotient_map_mem_quasiIso_iff]
    assumption
  have hb := (hY _ hf).1
  have : (HomotopyCategory.quotient C _).map u = (HomotopyCategory.quotient C _).map u' := by
    apply hb
    simp only [← Functor.map_comp, h]
  exact ⟨HomotopyCategory.homotopyOfEq _ _ this⟩

theorem sh_ext {R : Type} [CommRing R] {P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} {X : Shv R}
    (φ ψ : (presheafToSheaf Scheme.etaleTopology.{0} _).obj P ⟶ X)
    (h : toSheafify Scheme.etaleTopology.{0} P ≫ φ.hom = toSheafify Scheme.etaleTopology.{0} P ≫ ψ.hom) : φ = ψ := by
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} _).homEquiv P X).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h

theorem tw_hom_ext (q : ℕ) (i : ℤ) {X : Shv (ZMod q)} (φ ψ : tw q i ⟶ X)
    (h : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen i ζ) = Sec.map ψ (twGen i ζ)) : φ = ψ := by
  apply sh_ext
  ext U : 2
  apply ModuleCat.hom_ext
  refine Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun ζ => LinearMap.ext_ring ?_)
  exact h U.unop ζ

end LateralTheory.E.LeafTwResHtpyPf

open LateralTheory.E.LeafTwResHtpyPf in
theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy_of : LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy := by
  intro q _ k T e hT u u' hu
  obtain ⟨_, ε, hε, he⟩ := hT
  have := res_isKInj (ZMod q) (tw q k)
  refine htpy_of_qiso ε u u' ?_
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  have key : sglι (tw q k) ≫ ε.f 0 ≫ u.f 0 = sglι (tw q k) ≫ ε.f 0 ≫ u'.f 0 := by
    apply tw_hom_ext
    intro U ζ
    have := hu U ζ
    rw [← he U ζ] at this
    exact this
  have h1 : ε.f 0 ≫ u.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q k)).hom ≫
      (sglι (tw q k) ≫ ε.f 0 ≫ u.f 0) := by
    unfold sglι; exact (Iso.hom_inv_id_assoc _ _).symm
  have h2 : ε.f 0 ≫ u'.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q k)).hom ≫
      (sglι (tw q k) ≫ ε.f 0 ≫ u'.f 0) := by
    unfold sglι; exact (Iso.hom_inv_id_assoc _ _).symm
  exact h1.trans ((congrArg _ key).trans h2.symm)
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.CoverCut

def ClopenSys {Y : Scheme.{0}} (y : Y) {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0}) (c : Cone D)
    (ι : ∀ j, D.obj j ⟶ Y) : Prop :=
  Nonempty (IsLimit c) ∧ (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
    ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)

def Build : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P],
  ∃ (Y : Scheme.{0}) (k : Y ⟶ P), IsIntegralHom k ∧ Surjective k ∧
    ∀ y : Y, ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
      ClopenSys y D c ι ∧ AICSch c.pt ∧ ∀ j, IsIntegralHom ((c.π.app j ≫ ι j) ≫ k)

def ProEqv : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)),
  (∀ y : Y, ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
      ClopenSys y D c ι ∧ ∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) →
  PB q i g

theorem goal_of (hB : Build) (hP : ProEqv) : Cover := by
  intro H q i A _ _ hq P _ _ p hZ
  obtain ⟨Y, k, hk, hs, hY⟩ := hB (P := P)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace k
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated k
  refine ⟨Y, k, hk, hs, hP H q i A hq (k ≫ p) fun y => ?_⟩
  obtain ⟨J, _, _, D, c, ι, hc, hA, hint⟩ := hY y
  refine ⟨J, inferInstance, inferInstance, D, c, ι, hc, fun j => ?_⟩
  have := hZ c.pt ((c.π.app j ≫ ι j) ≫ k) (hint j) hA
  simpa only [Category.assoc] using this

end LateralTheory.E.CoverCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.IntPBPf

def IntHens : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] (φ : A →+* B), φ.IsIntegral →
  HenselianRing B ((IsLocalRing.maximalIdeal A).map φ)

def IntFib : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)), IsIntegralHom p →
  ∃ (B : Type) (_ : CommRing B) (φ : A →+* B), φ.IsIntegral ∧ ∀ (q : ℕ) (i : ℤ),
    Eqv _ (spMap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map φ))) (tw q i) →
    Eqv _ (sch.map (pullback.fst p (LateralTheory.E.t_E2Cut.cpt A))) (tw q i)

theorem IntPB_of (hH : IntHens) (hF : IntFib) : LateralTheory.E.t_E2Cut.IntPB := by
  intro hyp q i A _ _ hSH hq X p hp
  obtain ⟨hA, -⟩ := hSH
  obtain ⟨B, _, φ, hφ, hE⟩ := hF A p hp
  have : HenselianRing B ((IsLocalRing.maximalIdeal A).map φ) := hH A B φ hφ
  have hqB : IsUnit ((q : ℕ) : B) := by simpa using hq.map φ
  exact hE q i (hyp.e1 q B _ hqB i)

end LateralTheory.E.IntPBPf
end
end
