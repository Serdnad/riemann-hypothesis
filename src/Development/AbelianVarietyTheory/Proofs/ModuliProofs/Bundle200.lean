module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle197
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleHeckeKernelLists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle051
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle040
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle119
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle140
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle194
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle088
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle109
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle182
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle139
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle087
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle101
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle004

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkPerm

theorem lists_perm {S : Scheme.{0}} {G : Over S} [GrpObj G] {N n : ℕ} {σ : Fin n → (𝟙_ (Over S) ⟶ G)}
    {K : Set G.left} (h : Lists N σ K) (g : Equiv.Perm (Fin n)) : Lists N (fun j => σ (g j)) K := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨fun j => h₁ _, ?_, fun k _ _ x => (h₃ k x).comp g.injective⟩
  rw [h₂]
  exact (g.surjective.iUnion_comp (fun j => Set.range (σ j).left)).symm

theorem exists_perm {α : Type} {n : ℕ} {u v : Fin n → α} (hu : Function.Injective u) (hv : Function.Injective v)
    (h : Set.range u = Set.range v) : ∃ g : Equiv.Perm (Fin n), ∀ j, u (g j) = v j := by
  have : ∀ j, ∃ i, u i = v j := fun j => by
    have : v j ∈ Set.range u := h ▸ Set.mem_range_self j
    exact this
  choose g hg using this
  have gi : Function.Injective g := fun a b e => hv (by rw [← hg, ← hg, e])
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 gi), hg⟩

theorem exists_lists_mod_perm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ), admitted l 𝔓 p → ∃ (Y Hk : Scheme.{0}) (q : Y ⟶ Hk) (π₁ : Hk ⟶ Xo.X) (oY : Ob D l ((q ≫ π₁) ≫ Xo.s)) (m : ObjMap oY Xo.univ (q ≫ π₁)) (σ : Fin n → (𝟙_ (Over Y) ⟶ oY.t.G)) (K : Set oY.t.G.left), IsFinite q ∧ Etale q ∧ Surjective q ∧ IsFinite π₁ ∧ Etale π₁ ∧ Lists (p ^ 2) σ K ∧ HeckeSet D oY.t 𝔓 p i K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q ↔ Set.range (fun j => y ≫ (σ j).left ≫ m.toSABMap.φ) = Set.range (fun j => y' ≫ (σ j).left ≫ m.toSABMap.φ) ∧ y ≫ q ≫ π₁ = y' ≫ q ≫ π₁) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ Xo.X) (t : SAB H T) (mu : SABMap t Xo.univ.t f) (τ : Fin n → (𝟙_ (Over T) ⟶ t.G)) (K' : Set t.G.left), Lists (p ^ 2) τ K' → HeckeSet D t 𝔓 p i K' → ∃ h : T ⟶ Y, h ≫ q ≫ π₁ = f ∧ ∀ j, h ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := by
  intro E _ _ _ H D l Xo P p i n hA
  obtain ⟨Y, a, oY, m, σ, K, fa, ea, hL, hK, hu⟩ := GlobalTheory.T.exists_finiteEtale_heckeKernel_lists E H D l P p i n Xo.X Xo.s Xo.univ hA
  have hρ := fun g : Equiv.Perm (Fin n) => hu Y a oY.t m.toSABMap (fun j => σ (g j)) K (lists_perm hL g) hK
  choose ρ hρ₁ hρ₂ using hρ
  have r₁ : ∀ g, ρ g ≫ a = a := fun g => (hρ₁ g).1
  have r₂ : ∀ g j, ρ g ≫ (σ j).left ≫ m.toSABMap.φ = (σ (g j)).left ≫ m.toSABMap.φ := fun g => (hρ₁ g).2
  have one : ρ 1 = 𝟙 Y := (hρ₂ 1 _ ⟨by simp, fun j => by simp⟩).symm
  have mul : ∀ g c, ρ (g * c) = ρ g ≫ ρ c := fun g c =>
    (hρ₂ (g * c) _ ⟨by rw [Category.assoc, r₁, r₁], fun j => by
      rw [Category.assoc, r₂, r₂]; rfl⟩).symm
  have inj : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y),
      Function.Injective fun j => y ≫ (σ j).left ≫ m.toSABMap.φ := by
    intro k _ _ y b c e
    apply hL.2.2 k y
    have w : ∀ j, (σ j).left ≫ oY.t.G.hom = 𝟙 Y := fun j => Over.w _
    refine m.toSABMap.cart.1.hom_ext ?_ ?_
    · simpa only [Category.assoc] using e
    · simp only [Category.assoc, w]
  have free : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y) (g : Equiv.Perm (Fin n)), y ≫ ρ g = y → g = 1 := by
    intro k _ _ y g e
    ext1 j
    apply inj k y
    change y ≫ (σ (g j)).left ≫ m.toSABMap.φ = y ≫ (σ j).left ≫ m.toSABMap.φ
    rw [← r₂, ← Category.assoc, e]
  have uq : ∀ (T : Scheme.{0}) (y y' : T ⟶ Y), y ≫ a = y' ≫ a →
      (∀ j, y ≫ (σ j).left ≫ m.toSABMap.φ = y' ≫ (σ j).left ≫ m.toSABMap.φ) → y = y' := by
    intro T y y' e₁ e₂
    obtain ⟨_, _, _, _, _, m', -⟩ := sabPull Out.CubePf.cubePull y oY.t
    obtain ⟨mu, hmu⟩ := GlobalTheory.ObjMaps.exists_sab_comp m.toSABMap m'
    obtain ⟨τ, hτ, hL'⟩ := GlobalTheory.HkSetPull.lists_pull m'.cart K _ n σ hL
    have hτ' : ∀ j, y ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := fun j => by
      rw [hmu, ← Category.assoc, ← hτ, Category.assoc]
    exact (hu T (y ≫ a) _ mu τ _ hL' (GlobalTheory.HkSetPull.heckeSet_pull D P p i m' K hK)).unique ⟨rfl, hτ'⟩
      ⟨e₁.symm, fun j => (e₂ j).symm.trans (hτ' j)⟩
  have hq := GlobalTheory.isQProjOver_comp_of_isFinite_noetherian (KA l) Y Xo.X a Xo.s fa Xo.qproj
  obtain ⟨Hk, q, sH, hs, hG, sep, lft, -⟩ := GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver (KA l) Y (a ≫ Xo.s)
    (Equiv.Perm (Fin n)) ρ hq one mul (fun g => by rw [← Category.assoc, r₁]) free
  have hd := (GlobalTheory.ZM.galoisCover_descent Y Hk q _ ρ hG).1
  obtain ⟨π₁, rfl, -⟩ := hd Xo.X a r₁
  have hs' : π₁ ≫ Xo.s = sH := (hd _ ((q ≫ π₁) ≫ Xo.s) (fun g => by rw [← Category.assoc, r₁])).unique
    (Category.assoc _ _ _).symm hs
  subst hs'
  have : IsSeparated π₁ := IsSeparated.of_comp π₁ Xo.s
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : LocallyOfFiniteType π₁ := locallyOfFiniteType_of_comp π₁ Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  obtain ⟨f₁, e₁⟩ := isFinite_and_etale_of_comp_of_finite_etale_cover Y Hk Xo.X q π₁ hG.fin hG.etale hG.onto fa ea
    inferInstance inferInstance
  refine ⟨Y, Hk, q, π₁, oY, m, σ, K, hG.fin, hG.etale, hG.onto, f₁, e₁, hL, hK, fun k _ _ y y' => ⟨fun e => ?_, fun e => ?_⟩,
    fun T f t mu τ K' h₁ h₂ => (hu T f t mu τ K' h₁ h₂).exists⟩
  · obtain ⟨g, rfl, -⟩ := hG.fibre k y y' e
    refine ⟨?_, by rw [← Category.assoc, e, Category.assoc]⟩
    simp only [Category.assoc, r₂]
    exact (g.surjective.range_comp (fun j => y ≫ (σ j).left ≫ m.toSABMap.φ)).symm
  · obtain ⟨g, hg⟩ := exists_perm (inj k y) (inj k y') e.1
    have : y ≫ ρ g = y' := uq _ _ _ (by rw [Category.assoc, r₁]; exact e.2) fun j => by
      rw [Category.assoc, r₂]; exact hg j
    rw [← this, Category.assoc, hG.inv]

end GlobalTheory.HkPerm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.GenericObject

theorem isThetaPt_unit_mul {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (v v' : I → Γ(T.left, ⊤)) (c : Γ(T.left, ⊤)) (hc : IsUnit c) (hv : ∀ i, v' i = c * v i)
    (h : Out.IsThetaPt P k x v) : Out.IsThetaPt P k x v' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hp, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  have hc1 : IsUnit (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom c) := hc.map V.ι.appTop.hom
  obtain ⟨c', hc'⟩ := hc1
  refine ⟨V, hp, th, s1, α, τ, U, s2, w, c' * u, a1, a2, a3, a4, a5, a6, a7, fun i => ?_⟩
  have e1 : (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom (v' i)) =
      (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom c) * (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom (v i)) := by
    rw [hv i]
    exact map_mul V.ι.appTop.hom c (v i)
  have e2 : (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom (v i)) = u * w i := a8 i
  rw [← hc', e2, ← _root_.mul_assoc] at e1
  exact e1

theorem hasTh_unit_mul {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s) {R : Type} [CommRing R] (x : Sp R ⟶ S) (v v' : Ix g (N' ^ 2) → R) (c : R) (hc : IsUnit c)
    (hv : ∀ a, v' a = c * v a) (h : t.HasTh x v) : t.HasTh x v' := by
  refine isThetaPt_unit_mul _ _ _ _ _ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) (hc.map _) (fun a => ?_) h
  rw [hv a]
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c (v a)

theorem countable_of_finiteType (o : Type) [CommRing o] (h : Algebra.FiniteType ℤ o) : Countable o := by
  obtain ⟨m, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  have : Countable (MvPolynomial (Fin m) ℤ) :=
    (MvPolynomial.basisMonomials (Fin m) ℤ).repr.injective.countable
  exact hf.countable

theorem exists_generic_object : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (Y : MMPre n (n ^ j) (thIdeal em C)) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), IsOpenImmersion x → x ≫ Y.s = spMap β → SecCoord Y.de Y.th x v → ∀ q ∈ minimalPrimes R, ∃ (K : Type) (_ : Field K) (y : R →+* K) (e : K →+* ℂ) (t : TObj g ((n ^ j) ^ 2) J b (spMap y ≫ spMap β)) (tc : TObj g ((n ^ j) ^ 2) J b (spMap em)), RingHom.ker y = q ∧ e.comp (y.comp β) = em ∧ C tc ∧ TMap tc t (spMap e) ∧ t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => y (v a)) := by
  intro L1 L2 g J _ Mat κ n w w' hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.descend_to_thetaConstant_field L1 L2 g J Mat κ n w w' hn hodd
  refine ⟨max j₀ 1, fun j hj o _ b em C d har hC Y R _ β x v hx hxs hv q hq => ?_⟩
  have hj0 : j ≥ j₀ := le_trans (le_max_left _ _) hj
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    obtain ⟨m, hm⟩ := hodd
    omega
  have hN3 : 3 ≤ n ^ j := le_trans hn3 (Nat.le_self_pow (by omega) n)
  have hNodd : Odd (n ^ j) := hodd.pow
  haveI hqp : q.IsPrime := hq.1.1
  let K := FractionRing (R ⧸ q)
  let y : R →+* K := (algebraMap (R ⧸ q) K).comp (Ideal.Quotient.mk q)
  have hy0 : ∀ r, y r = 0 ↔ r ∈ q := fun r => by
    simp only [y, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ q) K), Ideal.Quotient.eq_zero_iff_mem]
  have hker : RingHom.ker y = q := Ideal.ext fun r => by rw [RingHom.mem_ker, hy0]
  have hfrac : ∀ k : K, ∃ r r' : R, y r' ≠ 0 ∧ k * y r' = y r := by
    intro k
    obtain ⟨a, a', ha', rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ q) k
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective a'
    have h0 : algebraMap (R ⧸ q) K (Ideal.Quotient.mk q r') ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := K) ha'
    exact ⟨r, r', h0, div_mul_cancel₀ _ h0⟩
  obtain ⟨c₀, hc₀⟩ := (Y.loc R β x v hxs hv).2 q hqp 0
  set a₀ := (0 : Ix g ((n ^ j) ^ 2)) + (n ^ j / n) • c₀ with ha₀
  have hva : y (v a₀) ≠ 0 := fun h => hc₀ ((hy0 _).1 h)
  obtain ⟨hcl, hmin⟩ := GlobalTheory.CoordChart.residue_generic o g n (n ^ j) (thIdeal em C) Y R β x v K y a₀ (by omega) hx hxs hv hfrac hva
  have hmin' := hmin (by rw [hker]; exact hq)
  obtain ⟨-, hhom, -⟩ := GlobalTheory.T.thetaPointsVanishingIdeal_radical_homogeneous o g (n ^ j) J b em C har.2.2
  have hu : (fun a => y (v a) / y (v a₀)) a₀ = 1 := div_self hva
  have hP := GlobalTheory.ker_cone_mem_minimalPrimes o _ K (thIdeal em C) (y.comp β) (fun a => y (v a) / y (v a₀)) a₀ hhom hu hmin'
  obtain ⟨tc, wv, htc, hth, hkw⟩ := GlobalTheory.ZM.exists_object_at_minimalPrime o g (n ^ j) J b em C Mat κ w w' d L1 L2 hN3 hNodd
    (countable_of_finiteType o har.2.1) hC _ hP
  obtain ⟨e, c, hc, he, hec⟩ := GlobalTheory.T.exists_complex_embedding_scaling_of_ker_eval_eq o K _ (y.comp β) em (fun a => y (v a) / y (v a₀)) wv a₀
    (div_ne_zero hva hva) (by simpa only [div_self hva, div_one] using hcl) hkw.symm
  have heva : e (y (v a₀)) ≠ 0 := (map_ne_zero e).2 hva
  have hth' : tc.HasTh (𝟙 _) (fun a => e (y (v a))) := by
    refine hasTh_unit_mul tc _ wv _ (e (y (v a₀)) * c) (IsUnit.mk0 _ (mul_ne_zero heva hc)) (fun a => ?_) hth
    have := hec a
    simp only [map_div₀] at this
    rw [_root_.mul_assoc, ← this]
    field_simp
  have hs : spMap em = spMap e ≫ spMap (y.comp β) := by
    rw [← he]
    exact Spec.map_comp (CommRingCat.ofHom (y.comp β)) (CommRingCat.ofHom e)
  have hs' : spMap (y.comp β) = spMap y ≫ spMap β :=
    Spec.map_comp (CommRingCat.ofHom β) (CommRingCat.ofHom y)
  have key := hj₀ j hj0 o b K ℂ (y.comp β) e (spMap em) tc (fun a => y (v a)) hs (hC.shape tc htc).1 (hC.shape tc htc).2 hth'
  rw [hs'] at key
  obtain ⟨t, h1, h2, h3, h4⟩ := key
  exact ⟨K, inferInstance, y, e, t, tc, hker, he, htc, h1, h2, h3, h4⟩

end GlobalTheory.GenericObject
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory
namespace ClosedPts

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

theorem jacobson_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_bot]
    by_contra h0
    have h1 := Ideal.mem_jacobson_bot.1 hx x
    have h2 : 0 < x * x := mul_self_pos.2 h0
    rcases Int.isUnit_iff.1 h1 with h3 | h3 <;> omega
  · have := Ring.DimensionLEOne.maximalOfPrime h hP
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem exists_maximal_notMem {R : Type} [CommRing R] [IsJacobsonRing R] (q : Ideal R) (f : R) (hq : q.IsPrime)
    (hf : f ∉ q) : ∃ m : Ideal R, m.IsMaximal ∧ q ≤ m ∧ f ∉ m := by
  by_contra hc
  push Not at hc
  apply hf
  rw [← IsJacobsonRing.out inferInstance hq.isRadical, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨h1, h2⟩
  exact hc m h2 h1

theorem charZero_quotient {o R : Type} [CommRing o] [IsDomain o] [CharZero o] [CommRing R] [Algebra o R]
    [Module.Flat o R] {q : Ideal R} (hq : q ∈ minimalPrimes R) : CharZero (R ⧸ q) := by
  have hp : q.IsPrime := hq.1.1
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra h0
  have h1 : (n : o) ∈ nonZeroDivisors o := mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast h0)
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) h1
  have h2 : (n : R) ∈ q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hn
  refine Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq) h2 ?_
  refine mem_nonZeroDivisors_iff_left.2 fun x hx => hreg ?_
  simpa [Algebra.smul_def] using hx

theorem finiteType_int_of_surjective {A B : Type} [CommRing A] [CommRing B] [Algebra.FiniteType ℤ A] (f : A →+* B)
    (hf : Function.Surjective f) : Algebra.FiniteType ℤ B :=
  Algebra.FiniteType.of_surjective f.toIntAlgHom hf

theorem range_spMap_fraction (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] :
    Set.range (spMap (algebraMap V K)) = {genericPoint (Sp V)} := by
  rw [genericPoint_eq_bot_of_affine]
  have key : ∀ y : Sp K, spMap (algebraMap V K) y = (⊥ : PrimeSpectrum V) := fun y => by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap V K) y.asIdeal = ⊥
    have hy : y.asIdeal = (⊥ : Ideal K) := Ideal.eq_bot_of_prime (K := K) y.asIdeal (h := y.isPrime)
    rw [hy]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact key y
  · rintro rfl
    exact ⟨(⊥ : PrimeSpectrum K), key _⟩

theorem exists_pull (h2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) {A B : Type} [CommRing A] [CommRing B] (e : A →+* B)
    {s : Sp A ⟶ Sp o} (s' : Sp B ⟶ Sp o) (hs : spMap e ≫ s = s') (t : TObj g (N' ^ 2) J b s)
    (v : Ix g (N' ^ 2) → A) (hsh : t.Shape Mat κ) (hv : t.HasTh (𝟙 _) v) :
    ∃ t' : TObj g (N' ^ 2) J b s', t'.Shape Mat κ ∧ t'.HasTh (𝟙 _) (fun a => e (v a)) ∧
      ∀ w w' : J, t.Prim w w' → t'.Prim w w' := by
  obtain ⟨t', ht'⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g _ J b _ _ s s' (spMap e) t hs
  refine ⟨t', ?_, ?_, fun w w' => (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w w' _ _ s s' _ t t' ht').2.1⟩
  · intro j
    exact (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ j j _ _ s s' _ t t' ht').1 hsh j
  · rw [GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ s t _ s' t' _ B (𝟙 _) _ ht', Category.id_comp]
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange h2 o g N' J b _ s t A B e (𝟙 _) v hv
    rwa [Category.comp_id] at this

end ClosedPts


open ClosedPts in
theorem veryDense_objPrimes_of_minimalPrimes : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (v : Ix g ((n ^ j) ^ 2) → R), Algebra.FiniteType o R → IsReduced R → Module.Flat o R → InMM n (n ^ j) (thIdeal em C) (algebraMap o R) v → (∀ q ∈ minimalPrimes R, ∃ (K : Type) (_ : Field K) (x : R →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap (algebraMap o R))), RingHom.ker x = q ∧ t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => x (v a))) → VeryDense (objPrimes b Mat κ (algebraMap o R) v) := by
  intro h1 h2 crit g J _ Mat κ n w w' hn hodd
  obtain ⟨j₁, crit⟩ := crit g n J w w' hn hodd
  obtain ⟨j₂, desc⟩ := GlobalTheory.T.descend_to_thetaConstant_field h1 h2 g J Mat κ n w w' hn hodd
  refine ⟨max j₁ j₂, fun j hj o _ b em C d har _ R _ _ v hft _ hflat hMM hmin q f hq hf => ?_⟩
  obtain ⟨hded, hfo, hinj⟩ := har
  have : CharZero o := em.charZero
  have : Algebra.FiniteType ℤ R := Algebra.FiniteType.trans hfo hft
  have := jacobson_int
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := ℤ)
  obtain ⟨m, hm, hqm, hfm⟩ := exists_maximal_notMem q f hq hf
  refine ⟨m, ?_, hm.isPrime, hqm, hfm⟩
  have := hm.isPrime
  obtain ⟨q₀, hq₀, hq₀m⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := m) bot_le
  have hp₀ : q₀.IsPrime := hq₀.1.1
  have : CharZero (R ⧸ q₀) := charZero_quotient (o := o) hq₀
  have := finiteType_int_of_surjective (Ideal.Quotient.mk q₀) Ideal.Quotient.mk_surjective
  obtain ⟨K, _, x, t, hx, hsh, hpr, hth⟩ := hmin q₀ hq₀

  let Ω := AlgebraicClosure K
  obtain ⟨tΩ, hshΩ, hthΩ, hprΩ⟩ := exists_pull h2 Mat κ (algebraMap K Ω) _ rfl t _ hsh hth

  let R₀ := R ⧸ q₀
  let K₀ := FractionRing R₀
  let π : R →+* R₀ := Ideal.Quotient.mk q₀
  let x₀ : R₀ →+* Ω := Ideal.Quotient.lift q₀ ((algebraMap K Ω).comp x) fun a ha => by
    rw [← hx, RingHom.mem_ker] at ha
    simp [ha]
  have hx₀ : Function.Injective x₀ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : algebraMap K Ω (x a) = 0 := ha
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hx, RingHom.mem_ker]
    exact (map_eq_zero _).1 this
  let e : K₀ →+* Ω := IsFractionRing.lift hx₀
  have he : ∀ a : R, e (algebraMap R₀ K₀ (π a)) = algebraMap K Ω (x a) := fun a => by
    simp only [e, IsFractionRing.lift_algebraMap]
    rfl
  let β₀ : o →+* R₀ := π.comp (algebraMap o R)
  obtain ⟨t₀, -, hsh₀, hpr₀, hth₀⟩ := desc j (le_of_max_le_right hj) o b K₀ Ω ((algebraMap R₀ K₀).comp β₀) e _ tΩ
    (fun a => algebraMap R₀ K₀ (π (v a))) (by
      simp only [spMap_spMap]
      congr 1
      ext a
      exact (he _).symm) hshΩ (hprΩ w w' hpr) (by simpa only [he] using hthΩ)
  obtain ⟨t₁, hsh₁, hth₁, hpr₁⟩ := exists_pull h2 Mat κ (RingHom.id K₀) (spMap (algebraMap R₀ K₀) ≫ spMap β₀)
    (by simp only [spMap_spMap, RingHom.id_comp]) t₀ _ hsh₀ hth₀

  have hker : RingHom.ker π ≤ m := by rwa [Ideal.mk_ker]
  have hm₀ : (m.map π).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective π Ideal.Quotient.mk_surjective hm).resolve_left fun h => by
      have := Ideal.comap_map_of_surjective' π Ideal.Quotient.mk_surjective m
      rw [h, Ideal.comap_top, sup_eq_left.2 hker] at this
      exact hm.ne_top this.symm
  have hcm : (m.map π).comap π = m := by
    rw [Ideal.comap_map_of_surjective' π Ideal.Quotient.mk_surjective m, sup_eq_left.2 hker]
  obtain ⟨V, F, _, _, _, _, _, _, _, _, _, y, tF, hy, hshF, hprF, hthF⟩ :=
    GlobalTheory.T.exists_thetaObject_over_complete_dvr_specialisation h1 h2 o g (n ^ j) J b Mat κ w w' R₀ K₀ β₀ (fun a => π (v a)) t₁ (m.map π) hm₀ hth₁ hsh₁ (hpr₁ w w' hpr₀)
  have hmem : ∀ a : R, y (π a) ∈ IsLocalRing.maximalIdeal V ↔ a ∈ m := fun a => by
    rw [← Ideal.mem_comap, hy, ← Ideal.mem_comap, hcm]
  have hcos : Coset n (n ^ j) (fun a => y (π (v a))) (IsLocalRing.maximalIdeal V) := fun a => by
    obtain ⟨c, hc⟩ := hMM.2 m hm.isPrime a
    exact ⟨c, fun h => hc ((hmem _).1 h)⟩

  obtain ⟨V', K', _, _, _, _, _, _, φ, ψ, t', tK, hφ, -, hK, hK', hth'⟩ :=
    crit j (le_of_max_le_left hj) o b V F (y.comp β₀) tF _ hprF hthF hcos
  have hshK : tK.Shape Mat κ :=
    (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w w' _ _ _ _ _ tF tK hK).1 hshF
  have hsh' : t'.Shape Mat κ :=
    GlobalTheory.T.thetaLevelShape_of_generic_point h1 h2 o g _ J b Mat κ (Sp V') _ t' K' _ _ tK (range_spMap_fraction V' K') hK' hshK

  let k := AlgebraicClosure (IsLocalRing.ResidueField V')
  let r : V' →+* k := (algebraMap (IsLocalRing.ResidueField V') k).comp (IsLocalRing.residue V')
  let z : R →+* k := r.comp (φ.comp (y.comp π))
  obtain ⟨tk, hshk, hthk, -⟩ := exists_pull h2 Mat κ r (spMap z ≫ spMap (algebraMap o R))
    (by simp only [spMap_spMap]) t' _ hsh' hth'
  refine ⟨k, inferInstance, inferInstance, z, tk, ?_, hshk, hthk⟩
  ext a
  rw [RingHom.mem_ker, ← hmem]
  change algebraMap (IsLocalRing.ResidueField V') k (IsLocalRing.residue V' (φ (y (π a)))) = 0 ↔ _
  rw [map_eq_zero, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

theorem cmExists_closed : CMExistsSt :=
  GlobalTheory.T.cmPointObject_exists_of_laws GlobalTheory.T.exists_cmEllipticCurve_withPeriod GlobalTheory.cmPoint_closed GlobalTheory.thetaUnifAV_closed
    GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    (GlobalTheory.CM.homExtDvr_of_card_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional)
    GlobalTheory.kernelFiniteFlat_holds

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors

theorem torsionIso_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), P.TorsionIso :=
  GlobalTheory.UT.torsionIso_of_pelUnif GlobalTheory.firstFiveLaws
    GlobalTheory.twistBaseChange_and_valuation_statements.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.2.2

end GlobalTheory.FlatTors
end
