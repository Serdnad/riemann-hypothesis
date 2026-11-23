module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct Topology

section Period

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}


open Classical in
def sigMult (D : Datum H) (τ : E →+* ℂ) : ℕ := if τ (H.rt : E) = H.rt0 then D.p else D.q

def IsTypeFn (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) : Prop :=
  ∀ τ : E →+* ℂ, Nat.card {i : Fin g // ty i = τ} = sigMult D τ

def tyAct {g : ℕ} (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (z : Fin g → ℂ) : Fin g → ℂ :=
  fun i => ty i (a : E) * z i

def actR (D : Datum H) (a : 𝓞 E) : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
  (DistribSMul.toLinearMap ℤ D.La a).baseChange ℝ

def sigTrace (D : Datum H) (a : 𝓞 E) : ℂ :=
  ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
    ((D.p : ℂ) * τ (a : E) + (D.q : ℂ) * starRingEnd ℂ (τ (a : E)))

def domain (D : Datum H) : Set (ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La) :=
  {J | (∀ x, J (J x) = -x) ∧
    (∀ a : 𝓞 E, J ∘ₗ actR D a = actR D a ∘ₗ J) ∧
    (∀ x y, D.EF.baseChange ℝ (J x) (J y) = D.EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < D.EF.baseChange ℝ (J x) x) ∧
    ∀ a : 𝓞 E, ((LinearMap.trace ℝ _ (actR D a) : ℝ) : ℂ) / 2 -
      Complex.I * ((LinearMap.trace ℝ _ (J ∘ₗ actR D a) : ℝ) : ℂ) / 2 = sigTrace D a}

def Presents (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ))
    (J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La) : Prop :=
  ∃ φ : (ℝ ⊗[ℤ] D.La) ≃ₗ[ℝ] (Fin g → ℂ),
    (∀ x : D.La, φ ((1 : ℝ) ⊗ₜ[ℤ] x) = P x) ∧ (∀ v, φ (J v) = Complex.I • φ v) ∧
      ∀ (a : 𝓞 E) v, φ (actR D a v) = tyAct ty a (φ v)

theorem domain_nonempty (D : Datum H) : (domain D).Nonempty := by
  obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
  have key := fun a : 𝓞 E => h4 a (actR D a) (sigTrace D a) (fun x => rfl) rfl
  refine ⟨J, h1, fun a => (key a).1, h2, h3, fun a => ?_⟩
  rw [(key a).2.1, (key a).2.2]
  apply Complex.ext
  · simp
  · simp; ring

end Period

section Hol

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

def HolOn (B : Set V) (y : V → (Sp ℂ ⟶ X)) : Prop :=
  ∀ (U : X.Opens), ∀ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ U →
    (∀ᶠ b' in 𝓝[B] b, ⊤ ≤ y b' ⁻¹ᵁ U) ∧
      ∀ f : Γ(X, U), DifferentiableWithinAt ℂ (fun b' => valAt' (y b') U f) B b

end Hol

section Theta

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {S : Scheme.{0}} {G : Over S} [GrpObj G] {g : ℕ}

abbrev fibre (G : Over S) (y : Sp ℂ ⟶ S) : Scheme.{0} := pullback G.hom y

def fibrePt {y : Sp ℂ ⟶ S} (x : Over.mk y ⟶ G) : Sp ℂ ⟶ fibre G y :=
  pullback.lift x.left (𝟙 (Sp ℂ)) (by simpa using Over.w x)

def IsRigFrame (L : RigLB G) (B : Set V) (y : V → (Sp ℂ ⟶ S))
    (ex : ∀ b : V, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (fr : L.L.ι → V → (Fin g → ℂ) → ℂ) : Prop :=
  HolOn (B ×ˢ (Set.univ : Set (Fin g → ℂ))) (fun p => ((ex p.1 p.2).left : Sp ℂ ⟶ G.left)) ∧
  (∀ b ∈ B, (ex b 0).left = y b ≫ eSec G) ∧
  (∀ i, DifferentiableOn ℂ (fun p : V × (Fin g → ℂ) => fr i p.1 p.2)
    {p | p.1 ∈ B ∧ ⊤ ≤ (ex p.1 p.2).left ⁻¹ᵁ L.L.U i}) ∧
  (∀ i, ∀ b ∈ B, ∀ z, ⊤ ≤ (ex b z).left ⁻¹ᵁ L.L.U i → fr i b z ≠ 0) ∧
  (∀ i j, ∀ b ∈ B, ∀ z, ⊤ ≤ (ex b z).left ⁻¹ᵁ (L.L.U i ⊓ L.L.U j) →
    fr i b z = valAt' (X := G.left) (ex b z).left (L.L.U i ⊓ L.L.U j) (L.L.g i j).val * fr j b z) ∧
  ∀ (j : (L.L.pull (eSec G)).ι), ∀ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ (L.L.pull (eSec G)).U j →
    fr (j PUnit.unit) b 0 = valAt' (X := S) (y b) ((L.L.pull (eSec G)).U j) (L.rig.s j).val

def IsFibreFn (L : LB G.left) (y : Sp ℂ ⟶ S) (ex : (Fin g → ℂ) → (Over.mk y ⟶ G))
    (fr : L.ι → (Fin g → ℂ) → ℂ) (s : (L.pull (pullback.fst G.hom y)).Sec) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (j : (L.pull (pullback.fst G.hom y)).ι) (z : Fin g → ℂ),
    ⊤ ≤ fibrePt (ex z) ⁻¹ᵁ (L.pull (pullback.fst G.hom y)).U j →
      valAt' (fibrePt (ex z)) ((L.pull (pullback.fst G.hom y)).U j) (s.f j) = θ z * fr (j PUnit.unit) z

def IsThetaFrame (L : RigLB G) (B : Set V) (y : V → (Sp ℂ ⟶ S))
    (ex : ∀ b : V, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)) (θ : V → (Fin g → ℂ) → ℂ)
    (fr : L.L.ι → V → (Fin g → ℂ) → ℂ) : Prop :=
  IsRigFrame L B y ex fr ∧
    ∀ b ∈ B, ∃ s : (L.L.pull (pullback.fst G.hom (y b))).Sec, IsFibreFn L.L (y b) (ex b) (fun i => fr i b) s (θ b)

end Theta

end GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

def zhatSubring : Subring (∀ n : ℕ+, ZMod n) where
  carrier := {f | ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n), ZMod.castHom h (ZMod m) (f n) = f m}
  mul_mem' {a b} ha hb m n h := by rw [Pi.mul_apply, map_mul, ha m n h, hb m n h, Pi.mul_apply]
  one_mem' m n h := by rw [Pi.one_apply, map_one, Pi.one_apply]
  add_mem' {a b} ha hb m n h := by rw [Pi.add_apply, map_add (f := _), ha m n h, hb m n h, Pi.add_apply]
  zero_mem' m n h := by rw [Pi.zero_apply, map_zero, Pi.zero_apply]
  neg_mem' {a} ha m n h := by rw [Pi.neg_apply, map_neg, ha m n h, Pi.neg_apply]

abbrev Zhat : Type := zhatSubring

def Zhat.red (n : ℕ+) : Zhat →+* ZMod n := (Pi.evalRingHom (fun m : ℕ+ => ZMod m) n).comp zhatSubring.subtype

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev Lhat (D : Datum H) : Type := Zhat ⊗[ℤ] D.La

def hatMul (D : Datum H) (c : 𝓞 E) : Lhat D →ₗ[Zhat] Lhat D :=
  (DistribSMul.toLinearMap ℤ D.La c).baseChange Zhat

def hatForm (D : Datum H) : LinearMap.BilinForm Zhat (Lhat D) := D.EF.baseChange Zhat

def hatSub (D : Datum H) (𝔞 : Ideal (𝓞 E)) : Submodule Zhat (Lhat D) :=
  Submodule.span Zhat ((fun a : D.La => (1 : Zhat) ⊗ₜ[ℤ] a) '' (𝔞 • (⊤ : Submodule (𝓞 E) D.La) : Submodule (𝓞 E) D.La))

def simGroup (D : Datum H) (l : Level H) : Subgroup (Lhat D ≃ₗ[Zhat] Lhat D) where
  carrier := {g | (∀ c x, g (hatMul D c x) = hatMul D c (g x)) ∧
    ∃ ν : Zhatˣ, Zhat.red ⟨l.A, l.A_pos⟩ ν = 1 ∧ ∀ x y, hatForm D (g x) (g y) = ν * hatForm D x y}
  mul_mem' := by
    rintro g h ⟨hg, ν, hν, eg⟩ ⟨hh, ν', hν', eh⟩
    refine ⟨fun c x => ?_, ν * ν', by rw [Units.val_mul, map_mul, hν, hν', _root_.mul_one], fun x y => ?_⟩
    · show g (h _) = hatMul D c (g (h x))
      rw [hh, hg]
    · show hatForm D (g (h x)) (g (h y)) = _
      rw [eg, eh, Units.val_mul, _root_.mul_assoc]
  one_mem' := ⟨fun _ _ => rfl, 1, map_one _, fun x y => by simp⟩
  inv_mem' := by
    rintro g ⟨hg, ν, hν, eg⟩
    refine ⟨fun c x => ?_, ν⁻¹, ?_, fun x y => ?_⟩
    · apply g.injective
      show g (g.symm _) = g (hatMul D c (g.symm x))
      rw [hg, g.apply_symm_apply, g.apply_symm_apply]
    · have := congrArg (Zhat.red ⟨l.A, l.A_pos⟩) ν.inv_mul
      rwa [map_mul, hν, _root_.mul_one, map_one] at this
    · have := eg (g.symm x) (g.symm y)
      rw [g.apply_symm_apply, g.apply_symm_apply] at this
      show hatForm D (g.symm x) (g.symm y) = _
      rw [this, Units.inv_mul_cancel_left]

def congSub (D : Datum H) (𝔞 : Ideal (𝓞 E)) : Subgroup (Lhat D ≃ₗ[Zhat] Lhat D) where
  carrier := {g | ∀ x, g x - x ∈ hatSub D 𝔞}
  mul_mem' {g h} hg hh x := by
    have := (hatSub D 𝔞).add_mem (hg (h x)) (hh x)
    rwa [sub_add_sub_cancel] at this
  one_mem' x := by simp
  inv_mem' {g} hg x := by
    have := (hatSub D 𝔞).neg_mem (hg (g.symm x))
    rwa [g.apply_symm_apply, neg_sub] at this

def trivAt (D : Datum H) (l : Level H) : Subgroup (Lhat D ≃ₗ[Zhat] Lhat D) :=
  congSub D l.Mb ⊓ congSub D (Ideal.span {(l.A : 𝓞 E)})

def relGroup (D : Datum H) (l l₂ : Level H) : Subgroup (Lhat D ≃ₗ[Zhat] Lhat D) := simGroup D l₂ ⊓ trivAt D l

theorem zeta_pow_div {m n : ℕ} (hn : 0 < n) (h : m ∣ n) : zeta n ^ (n / m) = zeta m := by
  obtain ⟨k, rfl⟩ := h
  have hm : 0 < m := Nat.pos_of_mul_pos_right hn
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn
  rw [Nat.mul_div_cancel_left k hm]
  unfold zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  push_cast
  field_simp

theorem KA_le {l l₂ : Level H} (h : l.Dvd l₂) : KA l ≤ KA l₂ := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  rintro x (rfl | rfl)
  · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  · have hz : zeta l₂.A ∈ IntermediateField.adjoin ℚ ({H.rt0, zeta l₂.A} : Set ℂ) :=
      IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rw [SetLike.mem_coe, ← zeta_pow_div l₂.A_pos h.2.2]
    exact pow_mem hz _

def lowerCoeff {l l₂ : Level H} (h : l.Dvd l₂) (c : Coeff l₂) : Coeff l where
  F := c.F
  fin := c.fin
  conj := c.conj
  zeta_mem := by
    have hp : 0 < l₂.M' := Nat.lcm_pos (by have := l₂.three_le; omega) l₂.A_pos
    have hd : l.M' ∣ l₂.M' := Nat.lcm_dvd (h.1.trans (Nat.dvd_lcm_left _ _)) (h.2.2.trans (Nat.dvd_lcm_right _ _))
    rw [← zeta_pow_div hp hd]
    exact pow_mem c.zeta_mem _
  le := (KA_le h).trans c.le

variable {D : Datum H} {l l₂ : Level H}

def IsOver (h : l.Dvd l₂) (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (π : Xo₂.X ⟶ Xo.X) : Prop :=
  π ≫ Xo.s = Xo₂.s ≫ spMap (IntermediateField.inclusion (KA_le h)).toRingHom

def PullsBack (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (π : Xo₂.X ⟶ Xo.X) : Prop :=
  ∃ m : SABMap Xo₂.univ.t Xo.univ.t π,
    (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (Xo.univ.eta a).left) ∧
    (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (Xo.univ.etaA a).left)

def ChangesLevelBy (Xo : Moduli D l) (g : Lhat D ≃ₗ[Zhat] Lhat D) (r : Xo.X ⟶ Xo.X) : Prop :=
  ∃ m : SABMap Xo.univ.t Xo.univ.t r,
    (∀ a b : D.La, g (1 ⊗ₜ a) - 1 ⊗ₜ b ∈ hatSub D l.Mb →
      (Xo.univ.eta b).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧
    (∀ a b : D.La, g (1 ⊗ₜ a) - 1 ⊗ₜ b ∈ hatSub D (Ideal.span {(l.A : 𝓞 E)}) →
      (Xo.univ.etaA b).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)

theorem spMap_inclusion_comp {A B C : IntermediateField ℚ ℂ} (h₁ : A ≤ B) (h₂ : B ≤ C) :
    spMap (IntermediateField.inclusion h₂).toRingHom ≫ spMap (IntermediateField.inclusion h₁).toRingHom =
      spMap (IntermediateField.inclusion (h₁.trans h₂)).toRingHom := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

def levelMapF (h : l.Dvd l₂) {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {π : Xo₂.X ⟶ Xo.X} (hπ : IsOver h Xo Xo₂ π)
    (c : Coeff l₂) : Xo₂.XF c ⟶ Xo.XF (lowerCoeff h c) :=
  pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by
    rw [Category.assoc, hπ, ← Category.assoc, pullback.condition, Category.assoc, spMap_inclusion_comp]
    rfl)

def endF {Xo : Moduli D l} (r : Xo.X ⟶ Xo.X) (hr : r ≫ Xo.s = Xo.s) (c : Coeff l) : Xo.XF c ⟶ Xo.XF c :=
  pullback.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc, hr, pullback.condition])

def IsLevelCovering (h : l.Dvd l₂) {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {π : Xo₂.X ⟶ Xo.X}
    (hπ : IsOver h Xo Xo₂ π) : Prop :=
  ∃ (ρ : relGroup D l l₂ → (Xo₂.X ≅ Xo₂.X)) (hρ : ∀ g, (ρ g).hom ≫ Xo₂.s = Xo₂.s),
    ρ 1 = Iso.refl _ ∧ (∀ g g', ρ (g * g') = ρ g ≪≫ ρ g') ∧
    (∀ g, ChangesLevelBy Xo₂ g.1 (ρ g).hom) ∧
    (∀ g, (ρ g).hom ≫ π = π) ∧
    ∀ c : Coeff l₂,
      IsFinite (levelMapF h hπ c) ∧ Etale (levelMapF h hπ c) ∧ Surjective (levelMapF h hπ c) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Xo₂.XF c),
        (∀ y : Sp k ⟶ Xo₂.XF c, y ≫ levelMapF h hπ c = x ≫ levelMapF h hπ c →
          ∃ g, x ≫ endF (ρ g).hom (hρ g) c = y) ∧
        ∀ g, x ≫ endF (ρ g).hom (hρ g) c = x ↔ g.1 ∈ trivAt D l₂

end GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

section Prim

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

def graphφ (f : A ⟶ A) : Fin 5 → (A.left ⟶ A.left) :=
  ![(padd A (𝟙 A) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left, 𝟙 A.left]

def graphε : Fin 5 → ℤ := ![1, -1, -1, 1, -1]

end Prim

variable {R : Type} [CommRing R] [IsDomain R]

section Data

variable {O : Type} [Ring O] [StarRing O] {D : DegPre R} [Module O D.X]

def IsRigGraphIso (D : DegPre R) (f : D.P.A ⟶ D.P.A)
    (v : LB.Gen (LB.LinComb D.P.L (graphφ D.P.A f) graphε)) : Prop :=
  v.IsGen ∧ LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ v (eSec D.P.A))
    (LB.invGen D.P.L _ _ D.rig)

def PsiThrough (ac : D.OAct O) (w : O) : Prop :=
  ∃ v : LB.Gen (LB.LinComb D.P.L (graphφ D.P.A (ac.onB.act w)) graphε),
    IsRigGraphIso D (ac.onB.act w) v ∧
    ∀ y : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau y (w • y)) (LB.pullGen D.P.L _ _ v (D.xK y)))
      (D.psi y)

end Data

def PsiGenOn (D : DegPre R) (χ : D.X) (U : Set (Spec (CommRingCat.of R))) : Prop :=
  ∀ x ∈ U, ∃ (j : PUnit → D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens), x ∈ V ∧
    V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) ∧
    ∃ (h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j)
      (r : Γ(Spec (CommRingCat.of R), V)ˣ), pullU (jK R) V r = res h ((D.psi χ).s j)

section Points

variable {O : Type} [Ring O] [StarRing O] {D : DegPre R} [Module O D.X]
variable {F : Type} [Field F] [Algebra (FractionRing R) F]

def IsRigAdjIso (D : DegPre R) (f g : D.P.A ⟶ D.P.A)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) : Prop :=
  u.IsGen ∧ LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)

def GtSmul (ac : D.OAct O) (a : O) (g g' : GtPtF D F) : Prop :=
  g'.b = g.b ≫ ac.onB.act a ∧
    ∃ u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (ac.onB.act a) (ac.onB.act (star a))) rosatiε),
      IsRigAdjIso D (ac.onB.act a) (ac.onB.act (star a)) u ∧
      ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (g'.s χ)
          (LB.pullGen D.P.L _ _ u (lift g.b (DegPre.cF D F χ)).left))
        (g.s (star a • χ))

def QkAdd {k : ℕ} (p p' p'' : QkPt D F k) : Prop :=
  ∃ q : QkPt D F k, q.y = p.y + p'.y ∧ GtPtF.IsAdd p.g p'.g q.g ∧ QkPt.Equiv D F q p''

def QkSmul (ac : D.OAct O) (a : O) {k : ℕ} (p p' : QkPt D F k) : Prop :=
  ∃ q : QkPt D F k, q.y = a • p.y ∧ GtSmul ac a p.g q.g ∧ QkPt.Equiv D F q p'

variable {F' : Type} [Field F'] [Algebra (FractionRing R) F']

abbrev specExt (σ : F →ₐ[FractionRing R] F') : (TF (R := R) F').left ⟶ (TF (R := R) F).left :=
  Spec.map (CommRingCat.ofHom (σ : F →+* F'))

def GtMap (σ : F →ₐ[FractionRing R] F') (g : GtPtF D F) (g' : GtPtF D F') : Prop :=
  g'.b.left = specExt σ ≫ g.b.left ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (g'.s χ) (LB.pullGen D.P.L _ _ (g.s χ) (specExt σ))

def QkMap (σ : F →ₐ[FractionRing R] F') {k : ℕ} (p : QkPt D F k) (p' : QkPt D F' k) : Prop :=
  ∃ q : QkPt D F' k, q.y = p.y ∧ GtMap σ p.g q.g ∧ QkPt.Equiv D F' q p'

end Points

section Host

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply Subtype.ext
  have h1 := H.bar_eq (H.bar a)
  rw [H.bar_eq a, IsCMField.complexConj_apply_apply] at h1
  exact h1

@[reducible] def hostStar (H : Host E) : StarRing (𝓞 E) where
  star := H.bar
  star_involutive := bar_bar H
  star_mul := fun a b => by
    change H.bar (a * b) = H.bar b * H.bar a
    rw [map_mul, _root_.mul_comm]
  star_add := fun a b => map_add H.bar a b

def PsiThroughHost (H : Host E) {D : DegPre R} [Module (𝓞 E) D.X]
    (ac : letI := hostStar H; D.OAct (𝓞 E)) : Prop :=
  letI := hostStar H; PsiThrough ac H.w0

end Host

end GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
end
end
