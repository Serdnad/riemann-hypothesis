module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle866
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle878
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle811
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle324
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.ThickLoc

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}}
  {s : X ⟶ Sp R} (T : Thick κ s) (b : T.B)

abbrev locJ : Ideal (Localization.Away b) := T.J.map (algebraMap T.B (Localization.Away b))

def locφ₀ : T.B₀ →+* Localization.Away b ⧸ locJ T b :=
  T.π.liftOfSurjective T.surj
    ⟨(Ideal.Quotient.mk (locJ T b)).comp (algebraMap T.B (Localization.Away b)), fun x hx ↦ by
      rw [RingHom.mem_ker] at hx ⊢
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ((T.ker x).1 hx))⟩

theorem locφ₀_π (x : T.B) :
    locφ₀ T b (T.π x) = Ideal.Quotient.mk (locJ T b) (algebraMap T.B (Localization.Away b) x) := by
  unfold locφ₀
  exact RingHom.liftOfSurjective_comp_apply _ _ _ x

@[reducible] def loc : Thick κ s where
  B := Localization.Away b
  J := locJ T b
  δ := DPLoc.dp (Submonoid.powers b) T.δ
  nil := DPLoc.isNilDP _ _ T.nil
  dp := by
    rw [IsScalarTower.algebraMap_eq R T.B (Localization.Away b)]
    exact IsDPMorphism.comp _ (DPLoc.isDPMorphism _ T.δ) T.dp
  B₀ := Localization.Away b ⧸ locJ T b
  π := Ideal.Quotient.mk _
  surj := Ideal.Quotient.mk_surjective
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := spMap (locφ₀ T b) ≫ T.x
  w := by
    rw [Category.assoc, T.w, ← Cris.spMap_comp]
    congr 1
    ext r
    simp only [RingHom.comp_apply, locφ₀_π]
    rw [← IsScalarTower.algebraMap_apply]

def toLoc : T ⟶ loc T b where
  φ := IsScalarTower.toAlgHom R T.B (Localization.Away b)
  φ₀ := locφ₀ T b
  comm := locφ₀_π T b
  dp := DPLoc.isDPMorphism (S := Localization.Away b) (Submonoid.powers b) T.δ
  pt := rfl

variable {T b} {S : Thick κ s} (u : T ⟶ S) (hu : IsUnit (u.φ b))

def liftφ : Localization.Away b →ₐ[R] S.B where
  toRingHom := IsLocalization.Away.lift b (g := (u.φ : T.B →+* S.B)) hu
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply R T.B (Localization.Away b)]
    exact (IsLocalization.Away.lift_eq b (g := (u.φ : T.B →+* S.B)) hu _).trans (u.φ.commutes r)

theorem liftφ_algebraMap (x : T.B) :
    liftφ u hu (algebraMap T.B (Localization.Away b) x) = u.φ x := by
  show IsLocalization.Away.lift b (g := (u.φ : T.B →+* S.B)) hu
      (algebraMap T.B (Localization.Away b) x) = u.φ x
  exact IsLocalization.Away.lift_eq b hu x

theorem liftφ_dp : IsDPMorphism (DPLoc.dp (S := Localization.Away b) (Submonoid.powers b) T.δ) S.δ
    (liftφ u hu : Localization.Away b →+* S.B) := by
  have h : (liftφ u hu : Localization.Away b →+* S.B).comp (algebraMap T.B (Localization.Away b)) =
      (u.φ : T.B →+* S.B) :=
    RingHom.ext fun x => liftφ_algebraMap u hu x
  exact DPLoc.isDPMorphism_of_comp (S := Localization.Away b) (Submonoid.powers b) T.δ S.δ _
    (by rw [h]; exact u.dp)

def liftφ₀ : Localization.Away b ⧸ locJ T b →+* S.B₀ :=
  Ideal.Quotient.lift _ (S.π.comp (liftφ u hu : Localization.Away b →+* S.B)) fun _ ha ↦
    (S.ker _).2 ((liftφ_dp u hu).1 (Ideal.mem_map_of_mem _ ha))

def lift : loc T b ⟶ S where
  φ := liftφ u hu
  φ₀ := liftφ₀ u hu
  comm _ := rfl
  dp := liftφ_dp u hu
  pt := by
    have : (liftφ₀ u hu).comp (locφ₀ T b) = u.φ₀ := RingHom.ext fun x ↦ by
      obtain ⟨x, rfl⟩ := T.surj x
      rw [RingHom.comp_apply, locφ₀_π, u.comm, ← liftφ_algebraMap u hu]
      rfl
    change spMap (liftφ₀ u hu) ≫ spMap (locφ₀ T b) ≫ T.x = S.x
    rw [← Category.assoc, ← Cris.spMap_comp, this, u.pt]

theorem exists_localization : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (s : X ⟶ Sp R) (T : Thick κ s) (b : T.B), ∃ (T' : Thick κ s) (l : T ⟶ T'), IsUnit (l.φ b) ∧ (∀ y : T'.B, ∃ (n : ℕ) (x : T.B), y * l.φ b ^ n = l.φ x) ∧ (∀ x : T.B, l.φ x = 0 → ∃ n : ℕ, b ^ n * x = 0) ∧ ∀ (S : Thick κ s) (u : T ⟶ S), IsUnit (u.φ b) → ∃! v : T' ⟶ S, l ≫ v = u := by
  intro R _ I κ X s T b
  refine ⟨loc T b, toLoc T b, ?_, ?_, ?_, ?_⟩
  · exact IsLocalization.Away.algebraMap_isUnit b
  · intro y
    obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers b) y
    obtain ⟨n, hn⟩ := m.2
    refine ⟨n, a, ?_⟩
    change y * algebraMap T.B (Localization.Away b) b ^ n = algebraMap T.B (Localization.Away b) a
    rw [← map_pow, show b ^ n = ↑m from hn]
    exact hm
  · intro x hx
    change algebraMap T.B (Localization.Away b) x = 0 at hx
    obtain ⟨⟨_, n, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers b) (Localization.Away b) x).1 hx
    exact ⟨n, hm⟩
  · intro S u hu
    refine ⟨lift u hu, ?_, ?_⟩
    · apply Thick.Hom.ext'
      ext c
      simp only [Thick.comp_φ]
      exact liftφ_algebraMap u hu c
    · intro v hv
      have h : (v.φ : Localization.Away b →+* S.B).comp (algebraMap T.B (Localization.Away b)) =
          (liftφ u hu : Localization.Away b →+* S.B).comp (algebraMap T.B (Localization.Away b)) := by
        ext c
        have hc : (toLoc T b ≫ v).φ c = u.φ c := by rw [hv]
        simp only [Thick.comp_φ] at hc
        show v.φ (algebraMap T.B (Localization.Away b) c) =
          liftφ u hu (algebraMap T.B (Localization.Away b) c)
        exact hc.trans (liftφ_algebraMap u hu c).symm
      apply Thick.Hom.ext'
      exact AlgHom.ext fun y ↦
        RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers b) h) y

end GlobalTheory.ThickLoc
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

namespace GlobalTheory.TransportFrame

open ReciprocityTheory.ChartRestriction.G.TB.ValAt

variable {X : Scheme.{0}}

theorem pspec_eq (p q : PrimeSpectrum ℂ) : p = q :=
  PrimeSpectrum.ext ((Ideal.eq_bot_of_prime p.asIdeal).trans (Ideal.eq_bot_of_prime q.asIdeal).symm)

theorem chart_pt (L : LB X) (hL : L.IsLB) (y : Sp ℂ ⟶ X) : ∃ j, ⊤ ≤ y ⁻¹ᵁ L.U j := by
  let p0 : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have hmem : y p0 ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨j, fun q _ => ?_⟩
  have : q = p0 := pspec_eq q p0
  rw [this]
  exact hj

theorem val_res_unit (x : Sp ℂ ⟶ X) {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)ˣ) :
    valAt' x V (res hVU a : Γ(X, V)) = valAt' x U (a : Γ(X, U)) :=
  ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_res x hVU h (a : Γ(X, U))

theorem val_inv_unit (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    valAt' x U ((a⁻¹ : Γ(X, U)ˣ) : Γ(X, U)) = (valAt' x U (a : Γ(X, U)))⁻¹ :=
  map_units_inv (valHom x U h) a

theorem val_unit_ne (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    valAt' x U (a : Γ(X, U)) ≠ 0 :=
  (a.isUnit.map (valHom x U h)).ne_zero

theorem val_gen {L L' : LB X} (w : LB.Iso L' L) (hw : w.IsGen) (x : Sp ℂ ⟶ X) (i i₂ : L.ι) (j j₂ : L'.ι)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L'.U j)) (h₂ : ⊤ ≤ x ⁻¹ᵁ (L.U i₂ ⊓ L'.U j₂)) :
    valAt' x (L.U i ⊓ L'.U j) (w.s (i, j)).val =
      valAt' x (L.U i ⊓ L.U i₂) (L.g i i₂).val * (valAt' x (L'.U j ⊓ L'.U j₂) (L'.g j j₂).val)⁻¹ *
        valAt' x (L.U i₂ ⊓ L'.U j₂) (w.s (i₂, j₂)).val := by
  have hW : ⊤ ≤ x ⁻¹ᵁ ((L.U i ⊓ L'.U j) ⊓ (L.U i₂ ⊓ L'.U j₂)) := fun p hp => ⟨h₁ hp, h₂ hp⟩
  have E : res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i ⊓ L'.U j from inf_le_left)
      (w.s (i, j) : Γ(X, L.U i ⊓ L'.U j)ˣ) =
      (res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i ⊓ L.U i₂ from
          le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) (L.g i i₂) *
        (res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L'.U j ⊓ L'.U j₂ from
          le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) (L'.g j j₂))⁻¹) *
      res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i₂ ⊓ L'.U j₂ from inf_le_right)
        (w.s (i₂, j₂) : Γ(X, L.U i₂ ⊓ L'.U j₂)ˣ) := hw (i, j) (i₂, j₂)
  have e := congrArg (fun a : Γ(X, (L.U i ⊓ L'.U j) ⊓ (L.U i₂ ⊓ L'.U j₂))ˣ =>
    valAt' x _ (a : Γ(X, (L.U i ⊓ L'.U j) ⊓ (L.U i₂ ⊓ L'.U j₂)))) E
  simp only [Units.val_mul, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_mul, val_inv_unit x _ hW, val_res_unit x _ hW] at e
  have a1 := val_res_unit x (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i ⊓ L'.U j from inf_le_left) hW
    (w.s (i, j) : Γ(X, L.U i ⊓ L'.U j)ˣ)
  have a2 := val_res_unit x (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i₂ ⊓ L'.U j₂ from inf_le_right) hW
    (w.s (i₂, j₂) : Γ(X, L.U i₂ ⊓ L'.U j₂)ˣ)
  exact a1.symm.trans (e.trans (congrArg (fun t => _ * t) a2))

end GlobalTheory.TransportFrame

namespace GlobalTheory.TransportFrame

open ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem val_g_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (x : Sp ℂ ⟶ X) (i : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    valAt' x (L.U i ⊓ L.U i) (L.g i i).val = 1 := by
  have e := val_res_unit x (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) h (L.g i i)
  rw [hL.g_self i, Units.val_one, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_one x _ h] at e
  exact e.symm

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} {L L' : LB A.left}

def chartOf (hL' : L'.IsLB) (y : Sp ℂ ⟶ A.left) : L'.ι := (chart_pt L' hL' y).choose

theorem chartOf_spec (hL' : L'.IsLB) (y : Sp ℂ ⟶ A.left) : ⊤ ≤ y ⁻¹ᵁ L'.U (chartOf hL' y) :=
  (chart_pt L' hL' y).choose_spec

def frT (u' : HolUnif A L' g) (hL' : L'.IsLB) (w : LB.Iso L' L) (i : L.ι) (z : Fin g → ℂ) : ℂ :=
  valAt' (u'.ex z).left (L.U i ⊓ L'.U (chartOf hL' (u'.ex z).left)) (w.s (i, chartOf hL' (u'.ex z).left)).val *
    u'.fr (chartOf hL' (u'.ex z).left) z

theorem frT_eq (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i : L.ι) (j : L'.ι)
    (z : Fin g → ℂ) (hi : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i) (hj : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U j) :
    frT u' hL' w i z = valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z := by
  have h0 := chartOf_spec hL' (u'.ex z).left
  have hij0 : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U (chartOf hL' (u'.ex z).left)) := fun p hp => ⟨hi hp, h0 hp⟩
  have hij : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j) := fun p hp => ⟨hi hp, hj hp⟩
  have h0j : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L'.U (chartOf hL' (u'.ex z).left) ⊓ L'.U j) := fun p hp => ⟨h0 hp, hj hp⟩
  have G := val_gen w hw (u'.ex z).left i i (chartOf hL' (u'.ex z).left) j hij0 hij
  have C := u'.fr_compat (chartOf hL' (u'.ex z).left) j z h0j
  have hne := val_unit_ne (u'.ex z).left _ h0j (L'.g (chartOf hL' (u'.ex z).left) j)
  have hs := val_g_self hL (u'.ex z).left i hi
  unfold frT
  rw [G, hs, C]
  have hc := inv_mul_cancel₀ hne
  linear_combination (valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z) * hc

theorem frT_hol (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i : L.ι) :
    DifferentiableOn ℂ (frT u' hL' w i) {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i} := by
  intro z0 hz0
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z0).left
  have hT := u'.hol (L.U i ⊓ L'.U j) (w.s (i, j)).val
  have hz0' : ⊤ ≤ (u'.ex z0).left ⁻¹ᵁ L.U i := hz0
  have hz0T : z0 ∈ {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)} :=
    show ⊤ ≤ (u'.ex z0).left ⁻¹ᵁ (L.U i ⊓ L'.U j) from fun p hp => ⟨hz0' hp, hj hp⟩
  have hd : DifferentiableOn ℂ (fun z => valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z)
      {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)} :=
    hT.2.mul ((u'.fr_hol j).mono fun z (hz : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)) p hp => (hz hp).2)
  have hev : frT u' hL' w i =ᶠ[nhds z0]
      fun z => valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z :=
    Filter.eventually_of_mem (hT.1.mem_nhds hz0T) fun z (hz : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)) =>
      frT_eq u' hL hL' w hw i j z (fun p hp => (hz hp).1) (fun p hp => (hz hp).2)
  exact (((hd z0 hz0T).differentiableAt (hT.1.mem_nhds hz0T)).congr_of_eventuallyEq hev).differentiableWithinAt

theorem frT_ne (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i : L.ι)
    (z : Fin g → ℂ) (hi : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i) : frT u' hL' w i z ≠ 0 := by
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z).left
  rw [frT_eq u' hL hL' w hw i j z hi hj]
  have hij : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j) := fun p hp => ⟨hi hp, hj hp⟩
  exact mul_ne_zero (val_unit_ne _ _ hij (w.s (i, j) : Γ(A.left, L.U i ⊓ L'.U j)ˣ)) (u'.fr_ne j z hj)

theorem frT_compat (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i i₂ : L.ι)
    (z : Fin g → ℂ) (h : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L.U i₂)) :
    frT u' hL' w i z = valAt' (u'.ex z).left (L.U i ⊓ L.U i₂) (L.g i i₂).val * frT u' hL' w i₂ z := by
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z).left
  have hi : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i := fun p hp => (h hp).1
  have hi₂ : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i₂ := fun p hp => (h hp).2
  rw [frT_eq u' hL hL' w hw i j z hi hj, frT_eq u' hL hL' w hw i₂ j z hi₂ hj,
    val_gen w hw (u'.ex z).left i i₂ j j (fun p hp => ⟨hi hp, hj hp⟩) (fun p hp => ⟨hi₂ hp, hj hp⟩),
    val_g_self hL' (u'.ex z).left j hj]
  ring

def transport (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) :
    HolUnif A L g where
  ex := u'.ex
  ex_add := u'.ex_add
  ex_onto := u'.ex_onto
  Λ := u'.Λ
  ker := u'.ker
  discrete := u'.discrete
  full := u'.full
  hol := u'.hol
  fr := frT u' hL' w
  fr_hol := frT_hol u' hL hL' w hw
  fr_ne := frT_ne u' hL hL' w hw
  fr_compat := frT_compat u' hL hL' w hw

theorem isFactorAH_transport (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ' : u'.Λ → ℂ} (h : GlobalTheory.TorusRM.IsFactorAH u' Hm χ') :
    GlobalTheory.TorusRM.IsFactorAH (transport u' hL hL' w hw) Hm χ' := by
  refine ⟨h.1, h.2.1, fun (l : u'.Λ) i z hz => ?_⟩
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z).left
  have he : u'.ex (z + l) = u'.ex z := by rw [u'.ex_add, (u'.ker l).2 l.2, _root_.mul_one]
  have hz0 : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i := hz
  have hz' : ⊤ ≤ (u'.ex (z + l)).left ⁻¹ᵁ L.U i := he ▸ hz0
  have hj' : ⊤ ≤ (u'.ex (z + l)).left ⁻¹ᵁ L'.U j := he ▸ hj
  show frT u' hL' w i z = χ' l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * frT u' hL' w i (z + l)
  rw [frT_eq u' hL hL' w hw i j z hz0 hj, frT_eq u' hL hL' w hw i j (z + l) hz' hj', h.2.2 l j z hj, he]
  ring

theorem exists_holUnif_isFactorAH_of_lbIso : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L L' : LB A.left)
    (u' : HolUnif A L' g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ), L.IsLB → L'.IsLB → LBIso L L' →
    GlobalTheory.TorusRM.IsFactorAH u' Hm χ' → ∃ (u : HolUnif A L g) (χ : u.Λ → ℂ), u.ex = u'.ex ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  intro A _ g L L' u' Hm χ' hL hL' hiso h
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  exact ⟨transport u' hL hL' w hw, χ', rfl, isFactorAH_transport u' hL hL' w hw h⟩

end GlobalTheory.TransportFrame
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM
open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RiemInt

open GlobalTheory.AppellHumbertTrivial

theorem im_hermForm_int {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (hL : L.IsLB) (u : HolUnif A L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : IsFactorAH u Hm χ) (l m : u.Λ) :
    ∃ n : ℤ, (hermForm Hm l m).im = n := by
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex 0).left hL
  have hil : ⊤ ≤ (u.ex (0 + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have him : ⊤ ≤ (u.ex (0 + m)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have hlm : ⊤ ≤ (u.ex (0 + l + m)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have h1 := h.2.2 l i 0 hi
  have h2 := h.2.2 m i _ hil
  have h3 := h.2.2 m i 0 hi
  have h4 := h.2.2 l i _ him
  have hne := u.fr_ne i _ hlm
  have hs : hermForm Hm m l = star (hermForm Hm l m) := by
    unfold hermForm
    rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, h.1.eq, Matrix.dotProduct_mulVec]
  have hχl : χ l ≠ 0 := norm_ne_zero_iff.1 (by rw [h.2.1]; exact one_ne_zero)
  have hχm : χ m ≠ 0 := norm_ne_zero_iff.1 (by rw [h.2.1]; exact one_ne_zero)
  rw [h2] at h1
  rw [h4, h1] at h3
  simp only [zero_add, zero_dotProduct, mul_zero] at h3 hne
  rw [add_comm (m : Fin g → ℂ) l] at h3
  unfold hermForm at hs ⊢
  rw [hs] at h3
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)) = a at h3
  generalize (m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = b at h3
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = c at h3 ⊢
  simp only [Complex.exp_add] at h3
  have he : Complex.exp (Real.pi * c) = Complex.exp (Real.pi * star c) := by
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hχl hχm)
      (Complex.exp_ne_zero (Real.pi / 2 * a))) (Complex.exp_ne_zero (Real.pi / 2 * b))) hne) ?_
    linear_combination h3
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  have hp := Real.pi_pos
  refine mul_left_cancel₀ (a := 2 * Real.pi) (by positivity) ?_
  linear_combination this

variable {g : ℕ}

end GlobalTheory.RiemInt

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.AffGlue

namespace GlobalTheory.DeRhamSheaf

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

section Data

variable {A} (H : GlobalTheory.Published.AbelianDeRham) {g : ℕ} (hA : IsAbelianScheme A)
  (hg : SmoothOfRelativeDimension g A.hom)

include hA in
theorem isAbelianScheme_onAff {V : T.Opens} (hV : IsAffineOpen V) : IsAbelianScheme (onAff A hV) :=
  isAbelianScheme_pullback_obj hV.fromSpec A hA



end Data

end GlobalTheory.DeRhamSheaf

namespace GlobalTheory.AffGlue

variable {T : Scheme.{0}}

end GlobalTheory.AffGlue

namespace GlobalTheory.DeRhamSheaf

end GlobalTheory.DeRhamSheaf
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg


open MvPolynomial in
theorem _root_.GlobalTheory.FockAlg.fock_lie_and_commute : ∀ (p q r s : ℕ),
    (∀ Y Z, _root_.Formalism.BasicNotions.TH.omAct p q r s (Y * Z - Z * Y) =
      _root_.Formalism.BasicNotions.TH.omAct p q r s Y * _root_.Formalism.BasicNotions.TH.omAct p q r s Z - _root_.Formalism.BasicNotions.TH.omAct p q r s Z * _root_.Formalism.BasicNotions.TH.omAct p q r s Y) ∧
    _root_.Formalism.BasicNotions.TH.IsLieAct (_root_.Formalism.BasicNotions.TH.fockAct1 p q r s) ∧ _root_.Formalism.BasicNotions.TH.IsLieAct (_root_.Formalism.BasicNotions.TH.fockAct2 p q r s) ∧
    ∀ Y Z, _root_.Formalism.BasicNotions.TH.fockAct1 p q r s Y * _root_.Formalism.BasicNotions.TH.fockAct2 p q r s Z = _root_.Formalism.BasicNotions.TH.fockAct2 p q r s Z * _root_.Formalism.BasicNotions.TH.fockAct1 p q r s Y :=
  fun p q r s => ⟨_root_.GlobalTheory.FockLie.omAct_lie p q r s,
    _root_.GlobalTheory.FockPair.pair_lie_commute p q r s⟩

end GlobalTheory.FockAlg
end
