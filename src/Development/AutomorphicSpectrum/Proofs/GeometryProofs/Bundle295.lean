module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle164
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle678
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormNotInCoordIdeal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMap
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle118
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle294
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_periodQuot_transport {V P : Type} [AddCommGroup V] [Module ℂ V] [CommGroup P] (E : V → P)
    (hadd : ∀ z w, E (z + w) = E z * E w) (hsurj : Function.Surjective E) (Γ₀ : Submodule ℤ V)
    (hΓ : (Γ₀ : Set V) = {z | E z = 1}) (N : ℕ) (hN : 0 < N) (T₀ : Set P) (hT₀ : ∀ τ ∈ T₀, τ ^ N = 1) :
    ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))),
      Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) = Nat.card {p : P // p ^ N = 1} ∧
      Nat.card T = Nat.card T₀ ∧
      (∀ x : Γ₀, Submodule.Quotient.mk x ∈ T → E ((N : ℂ)⁻¹ • (x : V)) ∈ T₀) ∧
      ∀ x : Γ₀, E ((N : ℂ)⁻¹ • (x : V)) ^ N = 1 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hmem : ∀ z : V, z ∈ Γ₀ ↔ E z = 1 := fun z => by
    have := Set.ext_iff.1 hΓ z
    simpa using this
  have h0 : E 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hpow : ∀ (k : ℕ) (z : V), E ((k : ℂ) • z) = E z ^ k := by
    intro k z
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  have hdiv : ∀ z : V, (N : ℂ) • (N : ℂ)⁻¹ • z = z := fun z => by rw [smul_smul, mul_inv_cancel₀ hNc, one_smul]
  let Eh : V →+ Additive P := AddMonoidHom.mk' (fun z => Additive.ofMul (E z)) (fun a b => by
    rw [hadd]; rfl)
  let d : Γ₀ →+ V := (((N : ℂ)⁻¹ • (LinearMap.id : V →ₗ[ℂ] V)).toAddMonoidHom).comp Γ₀.subtype.toAddMonoidHom
  let f : Γ₀ →ₗ[ℤ] Additive P := (Eh.comp d).toIntLinearMap
  have hf : ∀ x : Γ₀, f x = Additive.ofMul (E ((N : ℂ)⁻¹ • (x : V))) := fun x => rfl
  have hle : LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) ≤ LinearMap.ker f := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, hf]
    have : (N : ℂ)⁻¹ • (((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) y : Γ₀)) : V) = y := by
      have : ((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) y : Γ₀) : V) = (N : ℂ) • (y : V) := by
        simp [Nat.cast_smul_eq_nsmul]
      rw [this, smul_smul, inv_mul_cancel₀ hNc, one_smul]
    rw [this, (hmem _).1 y.2]
    rfl
  let φ := Submodule.liftQ _ f hle
  have hφ : ∀ x : Γ₀, φ (Submodule.Quotient.mk x) = Additive.ofMul (E ((N : ℂ)⁻¹ • (x : V))) := fun x => rfl
  have hφN : ∀ q, (Additive.toMul (φ q)) ^ N = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hφ, toMul_ofMul, ← hpow, hdiv]
    exact (hmem _).1 x.2
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hφ] at hq
    have h1 : E ((N : ℂ)⁻¹ • (x : V)) = 1 := hq
    have h2 : (N : ℂ)⁻¹ • (x : V) ∈ Γ₀ := (hmem _).2 h1
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨_, h2⟩, Subtype.ext ?_⟩
    have : ((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) ⟨_, h2⟩ : Γ₀) : V) = (N : ℂ) • (N : ℂ)⁻¹ • (x : V) := by
      simp [Nat.cast_smul_eq_nsmul]
    rw [this, hdiv]
  have hrange : ∀ p : P, p ^ N = 1 → ∃ q, Additive.toMul (φ q) = p := by
    intro p hp
    obtain ⟨z, rfl⟩ := hsurj p
    have h1 : (N : ℂ) • z ∈ Γ₀ := (hmem _).2 (by rw [hpow, hp])
    refine ⟨Submodule.Quotient.mk ⟨_, h1⟩, ?_⟩
    rw [hφ, toMul_ofMul]
    congr 1
    change (N : ℂ)⁻¹ • (N : ℂ) • z = z
    rw [smul_smul, inv_mul_cancel₀ hNc, one_smul]
  let ψ : (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) → P := fun q => Additive.toMul (φ q)
  have hψ : Function.Injective ψ := fun a b h => hinj (Additive.toMul.injective h)
  refine ⟨ψ ⁻¹' T₀, ?_, ?_, ?_, fun x => hφN (Submodule.Quotient.mk x)⟩
  · refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨ψ q, hφN q⟩) ⟨?_, ?_⟩)
    · exact fun a b h => hψ (congrArg Subtype.val h)
    · rintro ⟨p, hp⟩
      obtain ⟨q, hq⟩ := hrange p hp
      exact ⟨q, Subtype.ext hq⟩
  · refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨ψ q.1, q.2⟩) ⟨?_, ?_⟩)
    · exact fun a b h => Subtype.ext (hψ (congrArg Subtype.val h))
    · rintro ⟨p, hp⟩
      obtain ⟨q, hq⟩ := hrange p (hT₀ p hp)
      refine ⟨⟨q, ?_⟩, Subtype.ext hq⟩
      change ψ q ∈ T₀
      rw [show ψ q = p from hq]
      exact hp
  · intro x hx
    exact hx

theorem toric_torsion_radical_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp t.G M B ψ), SmoothOfRelativeDimension g t.G.hom → ∀ b₀ ∈ B, ∀ Γ₀ : Submodule ℤ (Fin g → ℂ), (Γ₀ : Set (Fin g → ℂ)) = e.per b₀ → ∀ N : ℕ, 0 < N → ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))), Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) * Nat.card T = N ^ (2 * g) ∧ ∀ x y : Γ₀, Submodule.Quotient.mk x ∈ T → GlobalTheory.UU.CubWeil t.cub N (e.ex b₀ ((N : ℂ)⁻¹ • (x : Fin g → ℂ))) (e.ex b₀ ((N : ℂ)⁻¹ • (y : Fin g → ℂ))) 1 := by
  intro E _ _ _ H R _ t g n M B ψ e dG b₀ hb₀ Γ₀ hΓ N hN
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨T₀, hT₁, hT₂, hT₃⟩ := GlobalTheory.exists_toric_torsion_cubWeil_one GlobalTheory.firstFiveLaws.2.2.1 (Sp R) t.G t.semi t.PP t.cub g N ℂ
    (spMap (ψ b₀)) dG hNc
  have hsurj := GlobalTheory.T.exponential_surjective_semiabelian R t.G g n M B ψ e t.semi b₀ hb₀
  obtain ⟨T, h₁, h₂, h₃, h₄⟩ := exists_periodQuot_transport (e.ex b₀) (e.add b₀ hb₀) hsurj Γ₀ hΓ N hN T₀ hT₁
  refine ⟨T, by rw [h₁, h₂, hT₃], fun x y hx => ?_⟩
  exact hT₂ _ (h₃ x hx) _ (h₄ y)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem _root_.GlobalTheory.T.flag_atlas_projective_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : GlobalTheory.FlagMod.LowRank.Proj (RingHom.id c.F)) (A : GlobalTheory.FlagMod.FieldFlag.Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : GlobalTheory.FlagEmb.En Dw.mult, Z ⟶ PSpace c.F (GlobalTheory.FlagEmb.plN A.N en.1)) (κ : ∀ b, GlobalTheory.FlagEmb.Pm Dw.mult → (Sp (GlobalTheory.FlagEmb.CR Dw.mult (A.V b)) ⟶ Z)), (∀ b w, IsOpenImmersion (κ b w)) → GlobalTheory.FlagMod.FieldFlag.Cells A π g κ → SmoothOfRelativeDimension Dw.dim Y.s → ∃ d : ℕ, SmoothOfRelativeDimension d (π ≫ Y.s) ∧ IsProjOver (π ≫ Y.s) := by
  first | exact @GlobalTheory.CompanionTheory.FlagMod.cells_smooth_proj | exact GlobalTheory.CompanionTheory.FlagMod.cells_smooth_proj | (intros; apply GlobalTheory.CompanionTheory.FlagMod.cells_smooth_proj <;> assumption)
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.HInterior

open GlobalTheory.CompanionTheory.Ar.Flat.CptIn.Intr GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

section Noeth

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {κ : Type} [Finite κ]

theorem isNoetherianRing_chart (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : κ → Ω) (hT : CoordTie ℤ ξ x) (c : κ)
    (hc : x c ≠ 0) (U : X.Opens) (hU : IsAffineOpen U)
    (hUm : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) (hη : genPt ξ ∈ U) :
    IsNoetherianRing Γ(X, U) := by
  have sp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => ((hUm q).1 hq).1
  let A : Subalgebra ℤ Ω := Algebra.adjoin ℤ (Set.range fun j => x j / x c)
  have hreg : ∀ a : Ω, a ∈ A ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
    intro a
    refine (hT.ring c hc a).trans (forall_congr' fun q => imp_congr ?_ Iff.rfl)
    exact ⟨fun hq => (hUm q.1).2 ⟨q.2, hq⟩, fun hq => ((hUm q.1).1 hq).2⟩
  let ρ : Γ(X, U) →+* A := (ev ξ U hη).codRestrict A
    fun s => (hreg _).2 fun q hq => ⟨_, _root_.GlobalTheory.CompanionTheory.Ar.Flat.CptIn.Intr.genMap_germ hη q hq s⟩
  have hinj : Function.Injective ρ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro s hs
    have h0 : ev ξ U hη s = 0 := congrArg Subtype.val hs
    refine TopCat.Presheaf.section_ext X.sheaf U s 0 fun q hq => ?_
    apply hT.gen.inj ⟨q, sp q hq⟩
    have h1 := _root_.GlobalTheory.CompanionTheory.Ar.Flat.CptIn.Intr.genMap_germ hη ⟨q, sp q hq⟩ hq s
    rw [h0] at h1
    refine h1.trans ?_
    simp only [map_zero]
  have hsurj : Function.Surjective ρ := by
    rintro ⟨a, ha⟩
    obtain ⟨s, hs⟩ := exists_ev_eq hU hη sp a ((hreg a).1 ha)
    exact ⟨s, Subtype.ext hs⟩
  haveI : Algebra.FiniteType ℤ A :=
    (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  exact isNoetherianRing_of_ringEquiv A (RingEquiv.ofBijective ρ ⟨hinj, hsurj⟩).symm

theorem isLocallyNoetherian_of_coordTie (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : κ → Ω) (hT : CoordTie ℤ ξ x)
    (hall : ∀ q : X, genPt ξ ⤳ q) : IsLocallyNoetherian X := by
  have key : ∀ p : X, ∃ U : X.affineOpens, p ∈ U.1 ∧ IsNoetherianRing Γ(X, U.1) := by
    intro p
    obtain ⟨c, hch⟩ := hT.cover ⟨p, hall p⟩
    obtain ⟨U, hU, hUm⟩ := hT.affine c hch.1
    have hp : p ∈ U := (hUm p).2 ⟨hall p, hch⟩
    exact ⟨⟨U, hU⟩, hp, isNoetherianRing_chart ξ x hT c hch.1 U hU hUm ((hall p).mem_open U.isOpen hp)⟩
  choose S hS hN using key
  exact isLocallyNoetherian_of_affine_cover (S := S)
    (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hS p⟩) hN

end Noeth

section Form

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem exists_homog_form_point (ξ : Spec (CommRingCat.of Ω) ⟶ X) (y : (Σ k, J k) → Ω)
    (hT : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) (V : X.Opens) (hV : genPt ξ ∈ V) :
    ∃ (f : MRing J) (d : K → ℕ), IsMultiHomog f d ∧ f ∉ mCoordIdeal y ∧ ∀ w ∈ mcPts (mCoordIdeal y), evC w f ≠ 0 →
      ∃ z : Spec (CommRingCat.of ℂ) ⟶ X, CoordsAt ξ y z w ∧ centre z ∈ V := by
  classical
  obtain ⟨c, hch⟩ := hT.cover ⟨genPt ξ, specializes_rfl⟩
  have hcx := hch.1
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hcx k (Finset.mem_univ k)
  obtain ⟨U, hU, hUm⟩ := hT.affine c hcx
  have hη : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, hch⟩
  have sp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => ((hUm q).1 hq).1
  have hreg : ∀ a : Ω, a ∈ chartRingZ y c ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
    intro a
    have h := hT.ring c hcx a
    rw [show (Algebra.adjoin ℤ (Set.range fun j : (∀ k, J k) => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) =
      chartRingZ y c from segre_chart y c hc] at h
    refine h.trans (forall_congr' fun q => imp_congr ?_ Iff.rfl)
    exact ⟨fun hq => (hUm q.1).2 ⟨q.2, hq⟩, fun hq => ((hUm q.1).1 hq).2⟩
  let ρ : Γ(X, U) →+* chartRingZ y c := (ev ξ U hη).codRestrict (chartRingZ y c)
    fun s => (hreg _).2 fun q hq => ⟨_, _root_.GlobalTheory.CompanionTheory.Ar.Flat.CptIn.Intr.genMap_germ hη q hq s⟩
  obtain ⟨s, hsV, hsη⟩ := hU.exists_basicOpen_le (V := V) ⟨genPt ξ, hV⟩ hη
  have ha0 : ev ξ U hη s ≠ 0 :=
    (((Scheme.mem_basicOpen X s _ hη).1 hsη).map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  obtain ⟨g₀, hg₀⟩ := ratMap_surjective y c (ρ s)
  obtain ⟨m, G₀, hG₀, eG⟩ := exists_form c g₀
  have hy₀ : aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) g₀ = ev ξ U hη s := by
    rw [← ratMap_coe, hg₀]
    rfl
  have hf0 : aeval y (G₀ * cMon c 1) ≠ 0 := by
    rw [map_mul, aeval_cMon, ← eG Ω y hc, hy₀]
    exact mul_ne_zero (mul_ne_zero ha0 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)))
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))
  refine ⟨G₀ * cMon c 1, m + 1, homog_mul hG₀ (homog_cMon c 1), fun hmem => hf0 ?_, fun w hw hne => ?_⟩
  · have h := aeval_scaled y (fun _ => 1) (G₀ * cMon c 1)
    have h0 : mConeMap y (G₀ * cMon c 1) = 0 := hmem
    rw [h0, map_zero] at h
    simpa only [mul_one] using h
  have hne' : aeval w (G₀ * cMon c 1) ≠ 0 := by
    rw [← evC_eq_aeval]
    exact hne
  rw [map_mul, aeval_cMon] at hne'
  have hwc : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by
    have := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hne') k (Finset.mem_univ k)
    simpa using this
  obtain ⟨e, he⟩ := exists_chartEval y c hc w hw hwc
  obtain ⟨z, hz, hval⟩ := exists_pt hU (e.comp ρ)
  have hval' : ∀ k i, ∃ s : Γ(X, U), ev ξ U hη s = y ⟨k, i⟩ / y ⟨k, c k⟩ ∧
      (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz s) = w ⟨k, i⟩ / w ⟨k, c k⟩ := by
    intro k i
    have hm : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c := Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩
    obtain ⟨s, hs⟩ := exists_ev_eq hU hη sp _ ((hreg _).1 hm)
    refine ⟨s, hs, ?_⟩
    have e1 : ρ s = ratMap y c (MvPolynomial.X ⟨k, i⟩) := Subtype.ext (by rw [ratMap_coe, aeval_X]; exact hs)
    rw [hval]
    change e (ρ s) = _
    rw [e1, he, aeval_X]
  have hs0 : (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz s) ≠ 0 := by
    rw [hval]
    change e (ρ s) ≠ 0
    rw [← hg₀, he]
    intro h0
    apply left_ne_zero_of_mul hne'
    rw [← eG ℂ w hwc, h0, zero_mul]
  refine ⟨z, ⟨fun k => ⟨c k, (IsUnit.mk0 _ (hwc k))⟩, fun k c₀ hu => ?_⟩, hsV ?_⟩
  · have hw0 : w ⟨k, c₀⟩ ≠ 0 := hu.ne_zero
    obtain ⟨sv, hsv, hev⟩ := hval' k c₀
    have hev0 : (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz sv) ≠ 0 := by
      rw [hev]
      exact div_ne_zero hw0 (hwc k)
    have hy0 : y ⟨k, c₀⟩ ≠ 0 := by
      intro h0
      apply hev0
      have h1 : ρ sv = 0 := Subtype.ext (by
        change ev ξ U hη sv = 0
        rw [hsv, h0, zero_div])
      rw [hval]
      change e (ρ sv) = 0
      rw [h1, map_zero]
    refine ⟨hy0, fun i => ?_⟩
    obtain ⟨su, hsu, heu⟩ := hval' k i
    refine ⟨w ⟨k, i⟩ / w ⟨k, c₀⟩, ?_, by field_simp⟩
    have h := valAt_quot hη sp z hz su sv hev0
    rw [hsu, hsv, heu, hev, div_div_div_cancel_right₀ (hc k), div_div_div_cancel_right₀ (hwc k)] at h
    exact h
  · exact (Scheme.mem_basicOpen X s _ hz).2
      (isUnit_of_map_unit (Scheme.stalkClosedPointTo z).hom _ (IsUnit.mk0 _ hs0))

end Form

end GlobalTheory.CompanionTheory.Ar.Cmp.HInterior

theorem GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_form_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c), A.ξ ≫ A.f = x ≫ Y.j → Mono (spMap β) → ∃ (b : MRing ι) (d : K → ℕ), IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ ∀ w ∈ mcPts (mCoordIdeal y), evC w b ≠ 0 → ∃ z : Spec (CommRingCat.of ℂ) ⟶ A.X, CoordsAt A.ξ y z w ∧ A.Interior z := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ ι _ y A x hx _
  haveI : IsLocallyNoetherian A.X := GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.isLocallyNoetherian_of_coordTie A.ξ _ A.tie A.all
  let V : A.X.Opens := ⟨abLocus A.t.G, GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian A.t.G A.t.semi⟩
  have hV : genPt A.ξ ∈ V := by
    refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 (genPt A.ξ)).1 ?_
    have h1 : A.f (genPt A.ξ) = Y.j (x (IsLocalRing.closedPoint Ω)) := by
      have := congrArg (fun g : Sp Ω ⟶ Y.X => g (IsLocalRing.closedPoint Ω)) hx
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans (this.trans (Scheme.Hom.comp_apply _ _ _))
    rw [h1]
    exact GlobalTheory.ModelScope.range_j_subset_abLocus Y ⟨_, rfl⟩
  obtain ⟨b, d, hb, hbI, hw⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_homog_form_point A.ξ y A.tie V hV
  refine ⟨b, d, hb, hbI, fun w hwm hne => ?_⟩
  obtain ⟨z, hz, hzV⟩ := hw w hwm hne
  exact ⟨z, hz, hzV⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.boundary_chart_hodge_map : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (jj : Sp C.R ⟶ 𝔐.X) (m : SABMap C.t 𝔐.t jj) (B₀ : Set (Fin n → ℂ)) (e : Flat.FamExp C.t.G C.M B₀ C.ψ) (b : Fin n → ℂ) (Bb : 𝓞 E →+* Module.End ℂ (Fin C.g → ℂ)) (Hm : Matrix (Fin C.g) (Fin C.g) ℂ), 1 ≤ D.p + D.q → b ∈ B₀ → 𝔐.Interior (spMap (C.ψ b) ≫ jj) → C.IsRiem b Hm → (∀ a' x, e.ex b (Bb a' x) = e.ex b x ≫ C.t.act.act a') → ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ 𝔐.t.G.left) (u : HolUnif A (𝔐.t.PP.L.pull φ) C.g) (χ : u.Λ → ℂ), IsGrpPullback A 𝔐.t.G (spMap (C.ψ b) ≫ jj) φ ∧ u.IsAH Hm χ ∧ (∀ x, (u.ex x).left ≫ φ = (e.ex b x).left ≫ m.φ) ∧ (∀ x, x ∈ u.Λ ↔ x ∈ e.per b) ∧ (∀ (x : Fin C.g → ℂ) (v : Sp (DualNumber ℂ) ⟶ C.t.G.left), IsDerivAt0 (fun x => (e.ex b x).left) x v → ∃ v' : epsR ℂ ⟶ A, v'.left ≫ φ = v ≫ m.φ ∧ u.IsDiff x v') ∧ ∀ a' a'' : 𝓞 E, (a'' : E) = IsCMField.complexConj E (a' : E) → ∀ x x', hermForm Hm (Bb a' x) x' = hermForm Hm x (Bb a'' x') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ChartUnif.exists_unif_of_interior | exact GlobalTheory.CompanionTheory.Ar.Cusp.ChartUnif.exists_unif_of_interior | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ChartUnif.exists_unif_of_interior <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.tower_origin_component_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : TowerOrigin Y T) (κ : Comp Xo c ≃ T.Comp), CompOf o κ → ∀ (B : ℕ) (Z : Comp Xo c), ∃ (Fr : Small.GenFrame (o.Or B (κ Z))) (Rd : Reading Fr h Z), GeoRead Rd := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.exists_geoRead | exact GlobalTheory.CompanionTheory.Ar.Plug.exists_geoRead | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.exists_geoRead <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl


theorem _root_.GlobalTheory.T.key_input_from_pp_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), 1 ≤ D.g → ∀ (s : Out.H0 D.t.PP.L 1) (e : Fin D.g → D.B.carrier), KeyDeg.NonVan D.t.G.hom s → LinearIndependent (𝓞 L) e → Submodule.span (𝓞 L) (Set.range e) = ⊤ → ∃ (x : KeyIn L) (th : D.t.PP.L.Sec) (hg : x.P.g = D.g) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ D.t.G)), KeyDeg.SameSec s th ∧ KeyDeg.NonVan D.t.G.hom th ∧ KeyOver (algebraMap (𝓞 L) L) D.t th x v ∧ IsLieBasis v ∧ ∀ i, (v i).left = (D.MB.pt (e (i.cast hg))).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDatum.exists_keyIn | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDatum.exists_keyIn | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDatum.exists_keyIn <;> assumption)
end
