module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Frames

variable {S : Scheme.{0}} {R : Type} [CommRing R]

def IsComb {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {n : ℕ} (c : Fin n → R) (v : Fin n → (epsAt x ⟶ G))
    (w : epsAt x ⟶ G) : Prop :=
  ∃ u : Fin n → (epsAt x ⟶ G), (∀ i, (u i).left = spMap (epsMul (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod

def IsEigVec {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (x : Sp R ⟶ S) (τ : O →+* R)
    (v : epsAt x ⟶ G) : Prop :=
  IsTanAt G x v ∧ ∀ a, (v ≫ act.act a).left = spMap (epsMul (τ a)) ≫ v.left

def IsEigFrame {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (x : Sp R ⟶ S) (τ : O →+* R)
    {n : ℕ} (v : Fin n → (epsAt x ⟶ G)) : Prop :=
  (∀ i, IsEigVec act x τ (v i)) ∧ ∀ w, IsEigVec act x τ w → ∃! c : Fin n → R, IsComb c v w

def IsHodgeGram (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) {n : ℕ} (v : Fin n → (epsAt x ⟶ G))
    (Γ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ G.left) (v' : Fin n → (epsR ℂ ⟶ Q.A)) (u : HolUnif Q.A Q.L Q.g)
    (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ) (W : Fin n → Fin Q.g → ℂ),
    IsGrpPullback Q.A G x ψ ∧ LBIso (L.pull ψ) Q.L ∧ u.IsAH Hm χ ∧
      (∀ i, (v' i).left ≫ ψ = (v i).left ∧ u.IsDiff (W i) (v' i)) ∧ ∀ i j, Γ i j = Real.pi * hermForm Hm (W i) (W j)

end Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def tauIn {l : Level H} (c : Coeff l) (τ : E →+* ℂ) : 𝓞 E →+* c.F :=
  ((τ.codRestrict c.F.toSubfield (c.conj τ)).comp (algebraMap (𝓞 E) E) :)

def sesq (D : Datum H) (x y : D.La) : E :=
  ∑ k, (D.EF (RingOfIntegers.basis E k • x) y : E) * HT.dualInt E k

def tyPart {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ) (z : Fin g → ℂ) : Fin g → ℂ :=
  open Classical in fun k => if ty k = τ then z k else 0

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusModel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem charVal_eq {A : Type} [CommRing A] {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal t χ = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (GlobalTheory.splitTorusPointsEquiv S X (Over.mk a) t (Multiplicative.ofAdd χ)).val := by
  unfold charVal
  set g : Sp A ⟶ Spec (torusRing ZU X) := t.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) with hg
  have h : (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      = Spec.preimage g := by
    conv_lhs => rw [← Spec.map_preimage g]
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [← h]
  rfl

theorem charVal_mul {A : Type} [CommRing A] {a : Sp A ⟶ S} (t t' : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal (t * t') χ = charVal t χ * charVal t' χ := by
  simp only [charVal_eq, map_mul, MonoidHom.mul_apply, Units.val_mul]

theorem charVal_one {A : Type} [CommRing A] {a : Sp A ⟶ S} (χ : X) :
    charVal (1 : Over.mk a ⟶ splitTorus S X) χ = 1 := by
  simp only [charVal_eq, map_one, MonoidHom.one_apply, Units.val_one]

theorem charVal_add {A : Type} [CommRing A] {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) (χ χ' : X) :
    charVal t (χ + χ') = charVal t χ * charVal t χ' := by
  simp only [charVal_eq, ofAdd_add, map_mul, Units.val_mul]

theorem charVal_zero {A : Type} [CommRing A] {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) :
    charVal t 0 = 1 := by
  simp only [charVal_eq, ofAdd_zero, map_one, Units.val_one]

theorem charVal_ext {A : Type} [CommRing A] {a : Sp A ⟶ S} {t t' : Over.mk a ⟶ splitTorus S X}
    (h : ∀ χ, charVal t χ = charVal t' χ) : t = t' := by
  apply (GlobalTheory.splitTorusPointsEquiv S X (Over.mk a)).injective
  ext χ
  have := h χ
  rw [charVal_eq, charVal_eq] at this
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective this

theorem exists_charVal {A : Type} [CommRing A] (a : Sp A ⟶ S) (u : Multiplicative X →* Aˣ) :
    ∃ t : Over.mk a ⟶ splitTorus S X, ∀ χ, charVal t χ = (u (Multiplicative.ofAdd χ)).val := by
  refine ⟨(GlobalTheory.splitTorusPointsEquiv S X (Over.mk a)).symm
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom).comp u), fun χ => ?_⟩
  rw [charVal_eq, MulEquiv.apply_symm_apply]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply _

theorem charVal_comp {A B : Type} [CommRing A] [CommRing B] {a : Sp A ⟶ S} {b : Sp B ⟶ S} (g : A →+* B)
    (t : Over.mk a ⟶ splitTorus S X) (t' : Over.mk b ⟶ splitTorus S X)
    (h : t'.left = spMap g ≫ t.left) (χ : X) : charVal t' χ = g (charVal t χ) := by
  unfold charVal
  have e : (t'.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) : Sp B ⟶ Spec (torusRing ZU X)) =
      Spec.map (CommRingCat.ofHom g) ≫
        (t.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) : Sp A ⟶ Spec (torusRing ZU X)) := by
    rw [h]; exact Category.assoc _ _ _
  rw [e, Spec.preimage_comp, Spec.preimage_map]
  rfl

theorem left_eq_of_charVal {A B : Type} [CommRing A] [CommRing B] {a : Sp A ⟶ S} {b : Sp B ⟶ S} (g : A →+* B)
    (hg : spMap g ≫ a = b) (t : Over.mk a ⟶ splitTorus S X) (t' : Over.mk b ⟶ splitTorus S X)
    (h : ∀ χ, charVal t' χ = g (charVal t χ)) : t'.left = spMap g ≫ t.left := by
  let k : Over.mk b ⟶ Over.mk a := Over.homMk (spMap g) hg
  have : t' = k ≫ t := charVal_ext fun χ => by rw [h, charVal_comp g t (k ≫ t) rfl]
  rw [this]; rfl

def epsUnit {R : Type} [CommRing R] (δ : X →+ R) : Multiplicative X →* (DualNumber R)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun χ => TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ.toAdd)
      map_one' := by ext <;> simp
      map_mul' := fun a b => by ext <;> simp [add_comm] }

def tanPt {R : Type} [CommRing R] (x : Sp R ⟶ S) (δ : X →+ R) : epsAt x ⟶ splitTorus S X :=
  (exists_charVal _ (epsUnit δ)).choose

theorem charVal_tanPt {R : Type} [CommRing R] (x : Sp R ⟶ S) (δ : X →+ R) (χ : X) :
    charVal (tanPt x δ) χ = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ) :=
  (exists_charVal _ (epsUnit δ)).choose_spec χ

theorem spMap_comp_eps {R A : Type} [CommRing R] [CommRing A] (x : Sp R ⟶ S) (g : DualNumber R →+* A)
    (f : R →+* A) (h : g.comp (algebraMap R (DualNumber R)) = f) :
    spMap g ≫ (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x) = spMap f ≫ x := by
  rw [← Category.assoc, ← Spec.map_comp, ← h]; rfl

theorem fst_eps {R : Type} [CommRing R] (x : Sp R ⟶ S) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x) = x := by
  rw [spMap_comp_eps x _ (RingHom.id R) (by ext; simp)]
  simp [spMap]

def lieModel {R : Type} [CommRing R] (x : Sp R ⟶ S) : LieModel (splitTorus S X) x (X →+ R) where
  pt := tanPt x
  tan δ := (left_eq_of_charVal _ (fst_eps x) (tanPt x δ) 1 fun χ => by
    rw [charVal_one, charVal_tanPt]; simp).symm
  inj δ δ' h := by
    ext χ
    have := congrArg (fun t => (charVal t χ).snd) h
    simpa [charVal_tanPt] using this
  onto v hv := by
    have h1 : ∀ χ, (charVal v χ).fst = 1 := fun χ => by
      have := charVal_comp (TrivSqZeroExt.fstHom R R R).toRingHom v (1 : Over.mk x ⟶ splitTorus S X)
        (Eq.symm hv) χ
      rw [charVal_one] at this
      exact this.symm
    refine ⟨AddMonoidHom.mk' (fun χ => (charVal v χ).snd) fun a b => ?_, charVal_ext fun χ => ?_⟩
    · simp [charVal_add, TrivSqZeroExt.snd_mul, h1, add_comm]
    · rw [charVal_tanPt]; ext <;> simp [h1]
  add δ δ' := charVal_ext fun χ => by
    rw [charVal_mul, charVal_tanPt, charVal_tanPt, charVal_tanPt]
    ext <;> simp [add_comm]
  smul c δ := left_eq_of_charVal (epsMul c)
    (spMap_comp_eps x _ _ (by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])) _ _ fun χ => by
      rw [charVal_tanPt, charVal_tanPt]
      ext <;> simp [epsMul, mul_comm]

theorem isCocharLie_lieModel {R : Type} [CommRing R] (x : Sp R ⟶ S) :
    IsCocharLie (lieModel (X := X) x) := charVal_tanPt x

end GlobalTheory.CompanionTheory.Ar.TorusModel
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure IsEmbedded {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : Ideal (MRing ι))
    (U : X → Set X) (lam : X → X → (Σ k, ι k) → ℂ) : Prop where
  isOpen : ∀ x, IsOpen (U x)
  mem_U : ∀ x, x ∈ U x
  holo : ∀ x p, A.HoloOn (U x) fun y => lam x y p
  mem : ∀ x, ∀ y ∈ U x, lam x y ∈ mcPts P
  compat : ∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lam x y) (lam x' y)
  surj : ∀ z ∈ mcPts P, ∃ x, SameOrbit (lam x x) z
  inj : ∀ x x', SameOrbit (lam x x) (lam x' x') → x = x'
  immersion : ∀ x, ∀ p : (k : K) → ι k, (∀ k, lam x x ⟨k, p k⟩ ≠ 0) → ∀ j, x ∈ (A.chart j).source →
    (fderiv ℂ (fun y => affCoord p (lam x ((A.chart j).symm y))) (A.chart j x)).ker = ⊥

def IsSncModel {Ω : Type} [Field Ω] [Algebra ℚ Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)) : Prop :=
  ∀ c : (k : K) → ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (m : ℕ) (f a : Fin m → Ω),
    (∀ l, f l ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) ∧
    (∀ l, a l ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) ∧
    ∑ l, a l * f l = 1 ∧ ∀ l, f l ≠ 0 → ∀ S : Subalgebra ℚ Ω,
      S = Algebra.adjoin ℚ (insert (f l)⁻¹ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) →
      Algebra.Smooth ℚ S ∧ ∃ (z : Fin e → S) (n : ℕ), n ≤ e ∧
        LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) ∧
        Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧
        ∀ q : Ideal S, q.IsPrime →
          ((∀ g ∈ J, ∀ s : S, (s : Ω) = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g → s ∈ q) ↔
            ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)

def AlgOver {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) : Prop :=
  ∃ (K₀ : Type) (_ : Fintype K₀) (ι₀ : K₀ → Type) (_ : ∀ k, Fintype (ι₀ k)) (κ : K₀ → K)
    (v : (Σ k, ι₀ k) → Σ k, ι k) (U : S.X → Set S.X) (lam : S.X → S.X → (Σ k, ι₀ k) → ℂ) (β : MRing ι₀) (b : K₀ → ℕ),
    IsBlockMap κ v ∧ IsEmbedded S.A (imageZ v P) U lam ∧
    (∀ x, SameOrbit (lam (Re.π x) (Re.π x)) fun p => Re.R.lift x x (v p)) ∧
    IsMultiHomog β b ∧ β ∉ imageZ v P ∧ ∀ x ∈ bdry S.s, evC (lam x x) β = 0

section Same

variable {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

def SameSing {D : ℕ} {σ₁ σ₂ : Type} {S₁ : AnSys D σ₁} {S₂ : AnSys D σ₂} {P₁ : Ideal (MRing ι₁)}
    {P₂ : Ideal (MRing ι₂)} (Re₁ : Realis S₁ P₁) (Re₂ : Realis S₂ P₂) (P : Ideal (MRing ι)) (κ₁ : K₁ → K)
    (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (β : MRing ι) (a₁ : σ₁) (a₂ : σ₂) :
    Prop :=
  ∃ f g : MRing ι, IsLineIso P (pullDeg κ₁ (Re₁.ref a₁).a) (pullDeg κ₂ (Re₂.ref a₂).a) f g ∧
    ∀ z ∈ mcPts P, evC z β ≠ 0 → ∀ (x₁ : Re₁.R.X) (x₂ : Re₂.R.X),
      SameOrbit (Re₁.R.lift x₁ x₁) (fun p => z (v₁ p)) → SameOrbit (Re₂.R.lift x₂ x₂) (fun p => z (v₂ p)) →
      Re₁.π x₁ ∉ bdry S₁.s → Re₂.π x₂ ∉ bdry S₂.s →
      ∀ u v : MRing ι, u * f - v * g ∈ P → evC z u ≠ 0 →
        Real.log (‖evC z v‖ / ‖evC z u‖ * (Re₂.ref a₂).h (fun p => z (v₂ p)) / (Re₁.ref a₁).h fun p => z (v₁ p)) =
          S₁.ph a₁ (Re₁.π x₁) - S₂.ph a₂ (Re₂.π x₂)

end Same

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end
