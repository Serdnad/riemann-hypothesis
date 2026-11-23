module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle004
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

def LeafPur : Prop := Hyp → ∀ d, ∃ pur : ∀ (q : ℕ) (P : SP d) (n i : ℤ),
    Ht q (sch.obj P.Z) n i →+ Hs q (opn P.U) (n + 2 * d) (i + d),
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  (∀ n i : ℤ, Function.Bijective (pur q P n i)) ∧
  (∀ (P' : SP d) (φ : P'.Hom P) (n i : ℤ) (a : Ht q (sch.obj P.Z) n i),
    Hs.pull q (opnMap φ.f _ _ φ.le) _ _ (pur q P n i a) = pur q P' n i (pull _ (sch.map φ.g) _ _ a)) ∧
  (∀ (n m i j : ℤ) (a : Ht q (sch.obj P.X) n i) (b : Ht q (sch.obj P.Z) m j),
    (Hs.fgt q (opn P.U) (n + m + 2 * d) (i + j + d) (pur q P (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b)) :
      Ht q (sch.obj P.X) (n + m + 2 * d) (i + j + d)) =
      (cup q a (Hs.fgt q (opn P.U) (m + 2 * d) (j + d) (pur q P m j b) : Ht q (sch.obj P.X) (m + 2 * d) (j + d))).cast
        (by ring) (by ring)) ∧
  ∀ r : ℕ, r ∣ q → ∀ (n i : ℤ) (a : Ht q (sch.obj P.Z) n i),
    (pur r P n i (red q r _ _ _ a)).1 = red q r _ _ _ (pur q P n i a).1

namespace GysinPf

theorem mono_opn {X : Scheme.{0}} (U : X.Opens) : Mono (opn U).hom := by
  change Mono (sch.map U.ι)
  haveI : ∀ k, Mono ((sch.map U.ι).app k) := fun _ => by
    change Mono (yoneda.map U.ι); infer_instance
  exact NatTrans.mono_of_mono_app _

def castHs {q : ℕ} {P : Arrow Spc} {a b : ℤ} (i : ℤ) (h : a = b) : Hs q P a i →+ Hs q P b i := by
  subst h; exact AddMonoidHom.id _

theorem castHs_bij {q : ℕ} {P : Arrow Spc} {a b : ℤ} (i : ℤ) (h : a = b) :
    Function.Bijective (castHs (q := q) (P := P) i h) := by
  subst h; exact Function.bijective_id

theorem castHs_pull {q : ℕ} {P' P : Arrow Spc} (φ : P' ⟶ P) {a b : ℤ} (i : ℤ) (h : a = b) (x : Hs q P a i) :
    Hs.pull q φ b i (castHs i h x) = castHs i h (Hs.pull q φ a i x) := by
  subst h; rfl

theorem castHs_val {Q q : ℕ} {P : Arrow Spc} {a b : ℤ} (i : ℤ) (h : a = b) (x : Hs Q P a i) (y : Hs q P a i)
    (hxy : y.1 = red Q q _ a i x.1) : (castHs i h y).1 = red Q q _ b i (castHs i h x).1 := by
  subst h; exact hxy

theorem fgt_pull {q : ℕ} {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.fgt q P' n i (Hs.pull q φ n i x) = pull _ φ.right _ _ (Hs.fgt q P n i x) := by
  change pull _ (dbl.inl P') _ n (pull _ (dbl.map φ) _ n x.1) = pull _ φ.right _ n (pull _ (dbl.inl P) _ n x.1)
  rw [← pull_comp, ← pull_comp,
    show dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P from pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _]

theorem fgt_red {Q q : ℕ} {P : Arrow Spc} (n i : ℤ) (x : Hs Q P n i) (y : Hs q P n i)
    (h : y.1 = red Q q _ n i x.1) : Hs.fgt q P n i y = red Q q _ n i (Hs.fgt Q P n i x) := by
  change pull _ (dbl.inl P) _ n y.1 = red Q q _ n i (pull _ (dbl.inl P) _ n x.1)
  rw [h, pull_red]

theorem exact_cast {q : ℕ} {P : Arrow Spc} {a b : ℤ} (i : ℤ) (h : a = b) {M : Type*} [AddCommGroup M]
    (f : M →+ Hs q P a i) (hf : Function.Exact f (Hs.fgt q P a i)) :
    Function.Exact ((castHs i h).comp f) (Hs.fgt q P b i) := by
  subst h; exact hf

end GysinPf


open GysinPf in
theorem LeafGysin_of (hBd : LeafBd) (hPur : LeafPur) : LeafGysin := by
  intro hH d
  obtain ⟨δ, hex, hnatδ, hredδ⟩ := hBd
  obtain ⟨pur, hp⟩ := hPur hH d
  classical
  let gys : ∀ (q : ℕ) (P : SP d) (n i : ℤ), Ht q (sch.obj P.Z) n i →+ Ht q (sch.obj P.X) (n + 2 * d) (i + d) :=
    fun q P n i => (Hs.fgt q (opn P.U) (n + 2 * d) (i + d)).comp (pur q P n i)
  let rs : ∀ (q : ℕ) (P : SP d) (n i : ℤ), Ht q (sch.obj P.U) (n + 2 * d - 1) (i + d) →+ Ht q (sch.obj P.Z) n i :=
    fun q P n i => if h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) then
      (AddEquiv.ofBijective _ ((@hp q ⟨h.1⟩ P h.2).1 n i)).symm.toAddMonoidHom.comp
        ((castHs (i + d) (show n + 2 * d - 1 + 1 = n + 2 * d by ring)).comp (δ q (opn P.U) (n + 2 * d - 1) (i + d)))
      else 0
  have hrs : ∀ (q : ℕ) [NeZero q] (P : SP d) (_ : IsUnit (q : Γ(P.X, ⊤))) (n i : ℤ) u,
      pur q P n i (rs q P n i u) =
        castHs (i + d) (show n + 2 * d - 1 + 1 = n + 2 * d by ring) (δ q (opn P.U) (n + 2 * d - 1) (i + d) u) := by
    intro q _ P hq n i u
    simp only [rs, dif_pos (⟨NeZero.ne q, hq⟩ : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)))]
    exact AddEquiv.ofBijective_apply_symm_apply (pur q P n i) ((hp q P hq).1 n i)
  refine ⟨gys, rs, ?_⟩
  intro q _ P hq
  obtain ⟨hbij, hnat, hproj, hred⟩ := hp q P hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n i
    have ex := hex q (opn P.U) (mono_opn _) (n + 2 * d - 1) (i + d)
    have ex' := hex q (opn P.U) (mono_opn _) (n + 2 * d) (i + d)
    refine ⟨?_, ?_, ?_⟩
    · intro x
      refine Iff.trans ?_ (ex.2.1 x)
      constructor
      · intro h
        have h2 := congrArg (pur q P n i) h
        rw [hrs q P hq, map_zero] at h2
        exact (castHs_bij _ _).1 (by rw [h2, map_zero])
      · intro h
        apply (hbij n i).1
        rw [hrs q P hq, h, map_zero, map_zero]
    · intro y
      refine (exact_cast (i + d) (show n + 2 * d - 1 + 1 = n + 2 * d by ring) _ ex.2.2 (pur q P n i y)).trans ?_
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, (hbij n i).1 ((hrs q P hq n i x).trans hx)⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, (hrs q P hq n i x).symm⟩
    · intro z
      refine (ex'.1 z).trans ?_
      constructor
      · rintro ⟨s, rfl⟩
        obtain ⟨y, rfl⟩ := (hbij n i).2 s
        exact ⟨y, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨_, rfl⟩
  · intro P' φ n i
    have hq' : IsUnit (q : Γ(P'.X, ⊤)) := by
      have := hq.map (φ.f.appTop).hom
      rwa [map_natCast] at this
    refine ⟨?_, ?_⟩
    · intro a
      change _ = Hs.fgt q (opn P'.U) _ _ (pur q P' n i _)
      rw [← hnat, fgt_pull]
      rfl
    · intro u
      apply ((hp q P' hq').1 n i).1
      rw [← hnat, hrs q P hq, hrs q P' hq', castHs_pull]
      exact congrArg _ (hnatδ q _ _ (opnMap φ.f _ _ φ.le) (mono_opn _) (mono_opn _) _ _ u)
  · exact hproj
  · intro r hr n i
    have : NeZero r := ⟨fun h => by subst h; exact NeZero.ne q (Nat.eq_zero_of_zero_dvd hr)⟩
    have hr' : IsUnit (r : Γ(P.X, ⊤)) := by
      obtain ⟨k, hk⟩ := hr
      rw [hk, Nat.cast_mul] at hq
      exact isUnit_of_mul_isUnit_left hq
    refine ⟨?_, ?_⟩
    · intro a
      exact fgt_red _ _ _ _ (hred r hr n i a)
    · intro u
      apply ((hp r P hr').1 n i).1
      apply Subtype.ext
      rw [hrs r P hr', hred r hr, hrs q P hq]
      exact castHs_val _ _ _ _ (hredδ q r hr _ (mono_opn _) _ _ u)

end LateralTheory.CohomologicalPurity
end
end

section

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

def LocStd (e d : ℕ) {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) : Prop :=
  RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (e + d)) φ ∧
  RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension e) ((Ideal.Quotient.mk I).comp φ)

def Std (e d : ℕ) {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) : Prop :=
  φ.IsStandardSmoothOfRelativeDimension (e + d) ∧ ((Ideal.Quotient.mk I).comp φ).IsStandardSmoothOfRelativeDimension e

def IsCoord {e d : ℕ} {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) (x : Fin d → A)
    (y : Fin e → A) : Prop :=
  (MvPolynomial.eval₂Hom φ (Sum.elim x y)).Etale ∧ I = Ideal.span (Set.range x)

def LeafLoc : Prop := ∀ (d : ℕ) (P : SP d) (x : P.X) (W : P.X.Opens), x ∈ W →
  ∃ V : P.X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W ∧
    ∃ (R : Type) (_ : CommRing R) (φ : R →+* Γ(P.X, V.1)), LocStd P.e d φ (P.ι.ker.ideal V)

def LeafShrink : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (I p : Ideal A), p.IsPrime → I ≤ p →
  LocStd e d φ I → ∃ f, f ∉ p ∧ ∀ (A' : Type) [CommRing A'] [Algebra A A'] [IsLocalization.Away f A'],
    Std e d ((algebraMap A A').comp φ) (I.map (algebraMap A A'))

def LeafRank : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (I p : Ideal A) [p.IsPrime], I ≤ p →
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) R A → Algebra.IsStandardSmoothOfRelativeDimension e R (A ⧸ I) →
  Module.finrank p.ResidueField (p.ResidueField ⊗[A] I) = d

def LeafPick : Prop := ∀ (d : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M] (p : Ideal A)
  [p.IsPrime], Module.finrank p.ResidueField (p.ResidueField ⊗[A] M) = d →
  ∃ (x : Fin d → M) (f : A), f ∉ p ∧ ∀ m : M, f • m ∈ Submodule.span A (Set.range x)

def LeafSpan : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
  (I p : Ideal A), p.IsPrime → I ≤ p → Algebra.IsStandardSmoothOfRelativeDimension e R (A ⧸ I) →
  ∀ (x : Fin d → A) (f : A), (∀ j, x j ∈ I) → f ∉ p → (∀ a ∈ I, f * a ∈ Ideal.span (Set.range x)) →
  ∃ (y : Fin e → A) (g : A), g ∉ p ∧ ∀ ω : Ω[A⁄R],
    g • ω ∈ Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (Sum.elim x y k))

def LeafEt : Prop := ∀ (n : ℕ) (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] (z : ι → A),
  Fintype.card ι = n → Algebra.IsStandardSmoothOfRelativeDimension n R A →
  Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (z k)) = ⊤ →
  (MvPolynomial.eval₂Hom (algebraMap R A) z).Etale

def LeafCoord : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (I p : Ideal A), p.IsPrime → I ≤ p →
  Std e d φ I → ∃ f, f ∉ p ∧ ∀ (A' : Type) [CommRing A'] [Algebra A A'] [IsLocalization.Away f A'],
    ∃ (x : Fin d → A') (y : Fin e → A'), IsCoord ((algebraMap A A').comp φ) (I.map (algebraMap A A')) x y

def LeafSec : Prop := ∀ (A T : Type) [CommRing A] [CommRing T] (φ : A →+* T) (I : Ideal A) (μ : T →+* A ⧸ I), φ.Etale →
  μ.comp φ = Ideal.Quotient.mk I → ∃ t : T, μ t = 1 ∧ ∀ s : T, μ s = 0 → t * s ∈ I.map φ

def LeafPoly : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) (x : Fin d → A)
  (y : Fin e → A), IsCoord φ I x y →
  (MvPolynomial.eval₂Hom ((MvPolynomial.C : A ⧸ I →+* MvPolynomial (Fin d) (A ⧸ I)).comp ((Ideal.Quotient.mk I).comp φ))
    (Sum.elim MvPolynomial.X fun i => MvPolynomial.C (Ideal.Quotient.mk I (y i)))).Etale

def LeafNbhd : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) (x : Fin d → A)
  (y : Fin e → A), IsCoord φ I x y → Chart d A I

theorem etale_of_subsingleton {A B : Type} [CommRing A] [CommRing B] [Subsingleton B] (φ : A →+* B) : φ.Etale := by
  algebraize [φ]
  exact RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale A B)

theorem chart_top (d : ℕ) (A : Type) [CommRing A] : Chart d A ⊤ := by
  have : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  refine ⟨A ⧸ (⊤ : Ideal A), inferInstance, Ideal.Quotient.mk ⊤, MvPolynomial.constantCoeff,
    ⟨etale_of_subsingleton _, ?_⟩, etale_of_subsingleton _, Subsingleton.elim _ _, fun a => ?_⟩
  · have := (Ideal.Quotient.mk_surjective (I := (⊤ : Ideal A).map (Ideal.Quotient.mk (⊤ : Ideal A)))).subsingleton
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  · rw [Subsingleton.elim (_ - _) 0]; exact zero_mem _

theorem mem_basicOpen_of_notMem {X : Scheme.{0}} (V : X.affineOpens) (x : X) (hx : x ∈ V.1) (f : Γ(X, V.1))
    (hf : f ∉ (V.2.primeIdealOf ⟨x, hx⟩).asIdeal) : x ∈ X.basicOpen f := by
  have h : V.2.primeIdealOf ⟨x, hx⟩ ∈ V.2.fromSpec ⁻¹ᵁ X.basicOpen f := by
    rw [V.2.fromSpec_preimage_basicOpen]; exact hf
  have h2 : V.2.fromSpec (V.2.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f := h
  rwa [V.2.fromSpec_primeIdealOf] at h2

theorem shrink {X : Scheme.{0}} (I : X.IdealSheafData) (V : X.affineOpens) (x : X) (hx : x ∈ V.1) (f : Γ(X, V.1))
    (hf : f ∉ (V.2.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ (V' : X.affineOpens) (_ : Algebra Γ(X, V.1) Γ(X, V'.1)), x ∈ V'.1 ∧ V'.1 ≤ V.1 ∧ IsLocalization.Away f Γ(X, V'.1) ∧
      I.ideal V' = (I.ideal V).map (algebraMap Γ(X, V.1) Γ(X, V'.1)) :=
  ⟨X.affineBasicOpen f, (inferInstance : Algebra Γ(X, V.1) Γ(X, X.basicOpen f)), mem_basicOpen_of_notMem V x hx f hf,
    X.basicOpen_le f, V.2.isLocalization_basicOpen f, (I.map_ideal_basicOpen V f).symm⟩

theorem off_case (d : ℕ) {X : Scheme.{0}} (I : X.IdealSheafData) (V : X.affineOpens) (x : X) (hx : x ∈ V.1)
    (h : ¬ I.ideal V ≤ (V.2.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ V' : X.affineOpens, x ∈ V'.1 ∧ V'.1 ≤ V.1 ∧ (I.ideal V').FG ∧ Chart d Γ(X, V'.1) (I.ideal V') := by
  obtain ⟨f, hfI, hf⟩ := SetLike.not_le_iff_exists.mp h
  obtain ⟨V', _, hx', hle, _, hI⟩ := shrink I V x hx f hf
  have ht : I.ideal V' = ⊤ := by
    rw [hI]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hfI) (IsLocalization.Away.algebraMap_isUnit f)
  refine ⟨V', hx', hle, ?_, ?_⟩
  · rw [ht]; exact Ideal.fg_top _
  · rw [ht]; exact chart_top d _

theorem goal_of (hL : LeafLoc) (hS : LeafShrink) (hC : LeafCoord) (hN : LeafNbhd) : LeafChart := by
  intro d P x W hx
  obtain ⟨V, hxV, hVW, R, _, φ, hφ⟩ := hL d P x W hx
  by_cases h : P.ι.ker.ideal V ≤ (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal
  swap
  · obtain ⟨V', a, b, c⟩ := off_case d P.ι.ker V x hxV h
    exact ⟨V', a, b.trans hVW, c⟩
  obtain ⟨f, hf, H⟩ := hS P.e d R _ φ _ _ (V.2.primeIdealOf ⟨x, hxV⟩).isPrime h hφ
  obtain ⟨V₁, _, hx₁, hle₁, _, hI₁⟩ := shrink P.ι.ker V x hxV f hf
  have H₁ := H Γ(P.X, V₁.1)
  rw [← hI₁] at H₁
  by_cases h₁ : P.ι.ker.ideal V₁ ≤ (V₁.2.primeIdealOf ⟨x, hx₁⟩).asIdeal
  swap
  · obtain ⟨V', a, b, c⟩ := off_case d P.ι.ker V₁ x hx₁ h₁
    exact ⟨V', a, b.trans (hle₁.trans hVW), c⟩
  obtain ⟨g, hg, G⟩ := hC P.e d R _ _ _ _ (V₁.2.primeIdealOf ⟨x, hx₁⟩).isPrime h₁ H₁
  obtain ⟨V₂, _, hx₂, hle₂, _, hI₂⟩ := shrink P.ι.ker V₁ x hx₁ g hg
  obtain ⟨u, v, G₂⟩ := G Γ(P.X, V₂.1)
  rw [← hI₂] at G₂
  refine ⟨V₂, hx₂, hle₂.trans (hle₁.trans hVW), ?_, hN P.e d R _ _ _ u v G₂⟩
  rw [G₂.2]
  exact Submodule.fg_span (Set.finite_range u)

end LateralTheory.CohomologicalPurity.ChartCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem LeafSemi_of : LeafSemi := by
  intro hA9 hG
  intro q _ X Z S p ι _ d e _ _ hq U hU N i
  obtain ⟨gys, rs, hgys⟩ := hG d
  let P : SP d := ⟨X, Z, S, p, ι, e, U, inferInstance, inferInstance, inferInstance, hU⟩
  have hqX : IsUnit (q : Γ(P.X, ⊤)) := by
    simpa using hq.map p.appTop.hom
  have hex := (hgys q P hqX).1
  have hsub : ∀ m j : ℤ, m < 0 → Subsingleton (Ht q (sch.obj Z) m j) :=
    fun m j hm => (hA9 (ZMod q) (tw q j)).1 _ m hm
  obtain ⟨j, rfl⟩ : ∃ j, i = j + d := ⟨i - d, by ring⟩
  constructor
  · intro hN
    refine ⟨?_, ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 * d := ⟨N - 2 * d, by ring⟩
      have hm : m < 0 := by omega
      have := hsub m j hm
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨b, rfl⟩ := ((hex m j).2.2 a).1 ha
      rw [Subsingleton.elim b 0, map_zero]
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 * d - 1 := ⟨N - 2 * d + 1, by ring⟩
      have hm : m < 0 := by omega
      have := hsub m j hm
      intro u
      exact ((hex m j).1 u).1 (Subsingleton.elim _ _)
  · intro hN
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 * d := ⟨N - 2 * d, by ring⟩
    have hm : m < 0 := by omega
    have := hsub m j hm
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨b, rfl⟩ := ((hex m j).2.2 a).1 ha
    rw [Subsingleton.elim b 0, map_zero]

end LateralTheory.CohomologicalPurity
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def LeafNbhdExc : Prop := A1 → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A),
  Nbhd φ I → IsUnit (q : A) → ∀ h, Exc q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B (I.map φ)) (off A I) h)

def LeafHsCont : Prop := A1 → A4 → B1 → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A),
  I.FG → IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D) (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ,
  (∀ x : Hs q (opn (off B (I.map φ))) n i, ∃ j h, ∃ y,
    Hs.pull q (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h) n i y = x) ∧
  (∀ j h y, Hs.pull q (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h) n i y = 0 →
    ∃ (k : J) (f : j ⟶ k) (h' : _), Hs.pull q (opnMap (Spec.map (D.map f)) (off (D.obj k) (I.map (s.app k).hom))
      (off (D.obj j) (I.map (s.app j).hom)) h') n i y = 0)

theorem off_map {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (J : Ideal R) :
    off S (J.map ψ) = Spec.map (CommRingCat.ofHom ψ) ⁻¹ᵁ off R J := by
  ext x
  show ¬ ((Ideal.map ψ J : Set S) ⊆ (x : PrimeSpectrum S).asIdeal) ↔
    ¬ ((J : Set R) ⊆ (PrimeSpectrum.comap ψ x).asIdeal)
  simp only [SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap]
  exact Iff.rfl

theorem dbl.inl_map' {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

theorem dbl.map_comp' {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) :
    dbl.map (φ ≫ ψ) = dbl.map φ ≫ dbl.map ψ := by
  set_option synthInstance.maxHeartbeats 200000 in
  apply pushout.hom_ext
  · change dbl.inl P'' ≫ dbl.map (φ ≫ ψ) = dbl.inl P'' ≫ dbl.map φ ≫ dbl.map ψ
    rw [dbl.inl_map', ← Category.assoc, dbl.inl_map', Category.assoc, dbl.inl_map', Arrow.comp_right,
      Category.assoc]
  · change dbl.inr P'' ≫ dbl.map (φ ≫ ψ) = dbl.inr P'' ≫ dbl.map φ ≫ dbl.map ψ
    rw [dbl.inr_map, ← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, Arrow.comp_right,
      Category.assoc]

theorem Hs.pull_comp' (q : ℕ) {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q (φ ≫ ψ) n i x = Hs.pull q φ n i (Hs.pull q ψ n i x) := by
  apply Subtype.ext
  change GlobalTheory.EtC.pull _ (dbl.map (φ ≫ ψ)) _ n x.1 = GlobalTheory.EtC.pull _ (dbl.map φ) _ n (GlobalTheory.EtC.pull _ (dbl.map ψ) _ n x.1)
  rw [dbl.map_comp', pull_comp]

theorem opnMap_comp {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) (U'' : X''.Opens) (U' : X'.Opens)
    (U : X.Opens) (h1 : U'' ≤ f ⁻¹ᵁ U') (h2 : U' ≤ g ⁻¹ᵁ U) (h : U'' ≤ (f ≫ g) ⁻¹ᵁ U) :
    opnMap (f ≫ g) U'' U h = opnMap f U'' U' h1 ≫ opnMap g U' U h2 := by
  apply Arrow.hom_ext
  · change sch.map _ = sch.map _ ≫ sch.map _
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map _ = sch.map _ ≫ sch.map _
    rw [Functor.map_comp]

theorem opnMap_congr {X' X : Scheme.{0}} {f g : X' ⟶ X} (e : f = g) (U' : X'.Opens) (U : X.Opens) (h : U' ≤ f ⁻¹ᵁ U)
    (h' : U' ≤ g ⁻¹ᵁ U) : opnMap f U' U h = opnMap g U' U h' := by
  subst e; rfl

theorem leafIndExc_of (hN : LeafNbhdExc) (hC : LeafHsCont) : LeafIndExc := by
  intro a1 a4 b1 q A B _ _ φ I hI hInd hq h n i
  obtain ⟨J, _, _, D, s, t, ⟨hcol⟩, hst⟩ := hInd
  have hs : ∀ j, Nbhd (A := A) (s.app j).hom I := fun j => (hst j).1
  have he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ := fun j => (hst j).2
  obtain ⟨hsurj, hinj⟩ := hC a1 a4 b1 q φ I hI hq J D s t hcol he n i
  have hsle : ∀ j, off (D.obj j) (I.map (s.app j).hom) ≤ Spec.map (s.app j) ⁻¹ᵁ off A I := fun j =>
    le_of_eq (off_map (s.app j).hom I)
  have hE : ∀ j, Function.Bijective (Hs.pull q (opnMap (Spec.map (s.app j)) _ _ (hsle j)) n i) := fun j =>
    hN a1 q (s.app j).hom I (hs j) hq (hsle j) n i
  have hB : ∀ j, off B (I.map φ) ≤ Spec.map (t.app j) ⁻¹ᵁ off (D.obj j) (I.map (s.app j).hom) := fun j => by
    intro x hx
    have hx' := h hx
    rw [← he j, Spec.map_comp] at hx'
    have e := off_map (s.app j).hom I
    simp only [CommRingCat.ofHom_hom] at e
    rw [e]
    exact hx'
  have hfac : ∀ j (h1 : off B (I.map φ) ≤ Spec.map (t.app j) ⁻¹ᵁ off (D.obj j) (I.map (s.app j).hom)),
      opnMap (Spec.map (CommRingCat.ofHom φ)) (off B (I.map φ)) (off A I) h =
        opnMap (Spec.map (t.app j)) _ _ h1 ≫ opnMap (Spec.map (s.app j)) _ _ (hsle j) := by
    intro j h1
    have hcomp : off B (I.map φ) ≤ (Spec.map (t.app j) ≫ Spec.map (s.app j)) ⁻¹ᵁ off A I := by
      rw [← Spec.map_comp, he j]; exact h
    exact (opnMap_congr (by rw [← Spec.map_comp, he j]) _ _ _ hcomp).trans
      (opnMap_comp _ _ _ _ _ h1 (hsle j) hcomp)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    rw [hfac j (hB j), Hs.pull_comp'] at hz
    obtain ⟨k, f, h', hk⟩ := hinj j (hB j) _ hz
    have hn : s.app k = s.app j ≫ D.map f := by
      have := s.naturality f
      simpa using this
    have hk' : opnMap (Spec.map (s.app k)) _ _ (hsle k) =
        opnMap (Spec.map (D.map f)) _ _ h' ≫ opnMap (Spec.map (s.app j)) _ _ (hsle j) := by
      have hcomp : off (D.obj k) (I.map (s.app k).hom) ≤ (Spec.map (D.map f) ≫ Spec.map (s.app j)) ⁻¹ᵁ off A I := by
        rw [← Spec.map_comp, ← hn]; exact hsle k
      exact (opnMap_congr (by rw [← Spec.map_comp, ← hn]) _ _ _ hcomp).trans
        (opnMap_comp _ _ _ _ _ h' (hsle j) hcomp)
    apply (injective_iff_map_eq_zero _).1 (hE k).1
    rw [hk', Hs.pull_comp', hk]
  · intro x
    obtain ⟨j, h1, y, hy⟩ := hsurj x
    obtain ⟨z, hz⟩ := (hE j).2 y
    exact ⟨z, by rw [hfac j h1, Hs.pull_comp', hz, hy]⟩

end LateralTheory.CohomologicalPurity
end
end

section

namespace LateralTheory.CohomologicalPurity

theorem goal_of (hG : LeafGysin) (hS : LeafSemi) : Goal :=
  fun H => ⟨hG H, hS H.2.2.2.2.2.2.1 (hG H)⟩

end LateralTheory.CohomologicalPurity
end
