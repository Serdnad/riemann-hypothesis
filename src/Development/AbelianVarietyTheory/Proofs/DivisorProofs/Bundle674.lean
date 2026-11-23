module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle634
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle635
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.ChartPointCongruence.EqOfMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilRigidity

theorem exists_preimage_quotient {R : Type} [CommRing R] (I : Ideal R) (hI : I ≤ nilradical R) (t : Sp R) :
    ∃ t₀ : Sp (R ⧸ I), spMap (Ideal.Quotient.mk I) t₀ = t := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hmem : t ∈ PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk I) : Set R) := by
    rw [Ideal.mk_ker]
    intro x hx
    exact (@nilradical_le_prime _ _ t.asIdeal t.isPrime) (hI hx)
  rw [← range_comap_of_surjective _ _ hsurj] at hmem
  obtain ⟨t₀, ht₀⟩ := hmem
  exact ⟨t₀, ht₀⟩

theorem eq_of_eq_on_quotient {R : Type} [CommRing R] (I : Ideal R) (hI : I ≤ nilradical R)
    (B B' : Over (Sp R)) [GrpObj B] [GrpObj B'] (hB : IsAbelianScheme B) (f g : B ⟶ B')
    (hfg : pullback.fst B.hom (spMap (Ideal.Quotient.mk I)) ≫ f.left =
      pullback.fst B.hom (spMap (Ideal.Quotient.mk I)) ≫ g.left)
    (hη : η[B] ≫ f = η[B] ≫ g) : f = g := by
  haveI := hB.proper
  let π := spMap (Ideal.Quotient.mk I)
  let c : B ⟶ B' := f * g⁻¹
  let j := pullback.fst B.hom π
  let j' : Over.mk (j ≫ B.hom) ⟶ B := Over.homMk j rfl
  have h1 : j' ≫ f = j' ≫ g := Over.OverMorphism.ext hfg
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[B] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  have hpt : ∀ x : B.left, c.left x = (η[B'] : 𝟙_ (Over (Sp R)) ⟶ B').left (B.hom x) := by
    intro x
    obtain ⟨t₀, ht₀⟩ := exists_preimage_quotient I hI (B.hom x)
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback B.hom π) x t₀ ht₀.symm
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    rfl
  have hη' : (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left ≫ B.hom = 𝟙 _ := Over.w η[B]
  have key : c.left = B.hom ≫ (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left ≫ c.left := by
    refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
    obtain ⟨V, hV, hV'⟩ := GlobalTheory.local_rigidity B.left (Sp R) B'.left B.hom _ c.left hη' inferInstance
      (GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.globalFns_holds B hB) (B.hom x)
      ((η[B'] : 𝟙_ (Over (Sp R)) ⟶ B').left (B.hom x)) (fun x' hx' ↦ by rw [hpt, hx'])
    exact ⟨B.hom ⁻¹ᵁ V, hV, hV'⟩
  have key' : c = toUnit B ≫ η[B] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

theorem eq_of_pullback_quotient_eq {R : Type} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    (B B' : Over (Sp R)) [GrpObj B] [GrpObj B'] (hB : IsAbelianScheme B) (f g : B ⟶ B') [IsMonHom f] [IsMonHom g]
    (h : (Over.pullback (spMap (Ideal.Quotient.mk I))).map f = (Over.pullback (spMap (Ideal.Quotient.mk I))).map g) :
    f = g := by
  have hI' : I ≤ nilradical R := by
    obtain ⟨n, hn⟩ := hI
    intro x hx
    exact ⟨n, by
      have : x ^ n ∈ I ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at this
      simpa using this⟩
  refine eq_of_eq_on_quotient I hI' B B' hB f g ?_ (by rw [IsMonHom.one_hom, IsMonHom.one_hom])
  have e := congrArg (fun k ↦ k.left ≫ pullback.fst B'.hom (spMap (Ideal.Quotient.mk I))) h
  simp only [Over.pullback_map_left, pullback.lift_fst] at e
  exact e

end GlobalTheory.NilRigidity
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.PinchUnitLift

theorem unit_lift (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀)
    (h : IsPullback f₁ f₂ g₁ g₂) [IsLocalRing P] (h₁ : Function.Surjective g₁) (h₂ : Function.Surjective g₂)
    (r : R₀) (hr : IsUnit r) : ∃ s : R₁, IsUnit s ∧ g₁ s = r := by
  rcases subsingleton_or_nontrivial R₀ with h0 | h0
  · exact ⟨1, isUnit_one, Subsingleton.elim _ _⟩
  have hf : Function.Surjective f₁ := by
    intro a
    obtain ⟨b, hb⟩ := h₂ (g₁ a)
    obtain ⟨p, hp, -⟩ := Types.exists_of_isPullback (h.map (forget CommRingCat)) a b hb.symm
    exact ⟨p, hp⟩
  haveI : Nontrivial R₁ := g₁.hom.domain_nontrivial
  haveI : IsLocalRing R₁ := IsLocalRing.of_surjective' f₁.hom hf
  haveI : IsLocalHom g₁.hom := IsLocalHom.of_surjective g₁.hom h₁
  obtain ⟨s, rfl⟩ := h₁ r
  exact ⟨s, IsUnit.of_map g₁.hom s hr, rfl⟩

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (B : Over (Spec R₀)) [GrpObj B], IsAbelianScheme B → ∀ (X₁ : Scheme.{0}) (q : X₁ ⟶ Spec R₁) (ρ : B.left ⟶ X₁), ρ ≫ q = B.hom ≫ Spec.map g₁ → ∀ u : Γ(B.left, ⊤)ˣ, ∃ v : Γ(X₁, ⊤)ˣ, ∀ x : B.left, gm ρ x ⊤ v = gm (𝟙 B.left) x ⊤ u := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h hP _ h₁ h₂ B _ hB X₁ q ρ hρ u
  have hb := GlobalTheory.globalFns_holds _ B hB
  obtain ⟨t, ht⟩ := hb.2 u.val
  obtain ⟨t', ht'⟩ := hb.2 (u⁻¹).val
  have htu : IsUnit t := by
    refine IsUnit.of_mul_eq_one t' (hb.1 ?_)
    rw [map_mul, map_one, ht, ht']
    exact u.mul_inv
  obtain ⟨s, hs, hst⟩ := unit_lift P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h h₁ h₂ ((Scheme.ΓSpecIso R₀).hom t)
    (htu.map (Scheme.ΓSpecIso R₀).hom.hom)
  have hv : IsUnit (q.appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s)) := (hs.map _).map _
  refine ⟨hv.unit, fun x => Units.ext ?_⟩
  rw [gm_val ρ x ⊤ trivial, gm_val (𝟙 B.left) x ⊤ trivial]
  have e : ρ.appTop.hom (q.appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s)) = u.val := by
    have e1 : ρ.appTop.hom (q.appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s)) =
        (ρ ≫ q).appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s) := by
      rw [Scheme.Hom.comp_appTop]; rfl
    have e2 : (Spec.map g₁).appTop.hom ((Scheme.ΓSpecIso R₁).inv.hom s) = t := by
      have := congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso_inv_naturality g₁)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [← this]
      have hst' : g₁.hom s = (Scheme.ΓSpecIso R₀).hom.hom t := hst
      rw [hst']
      exact (Scheme.ΓSpecIso R₀).hom_inv_id_apply t
    rw [e1, hρ, Scheme.Hom.comp_appTop, ← ht, ← e2]
    rfl
  exact congrArg (B.left.presheaf.germ ⊤ x trivial).hom e

end GlobalTheory.PinchUnitLift
end

section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_section_descent_flat_surjective_quasiCompact : ∀ {X B H : Scheme.{0}} (L : LB X), L.IsLB → ∀ (q : H ⟶ B), Flat q → Surjective q → QuasiCompact q → ∀ {K : Type} [Fintype K] (ψ : K → (B ⟶ X)) (ε : K → ℤ) (σ : LB.Sec (LB.LinComb L (fun k => q ≫ ψ k) ε)), (∀ (S : Type) [CommRing S] [IsLocalRing S] (g₁ g₂ : Sp S ⟶ H), g₁ ≫ q = g₂ ≫ q → ∀ J, Good L (closedPoint S) J → sval σ g₁ (closedPoint S) J = sval σ g₂ (closedPoint S) J) → ∃ b : LB.Sec (LB.LinComb L ψ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z) J, Good L z J → sval σ r z J = sval b (r ≫ q) z J := by
  first | exact @GlobalTheory.LocDescent.exists_sec_descend | exact GlobalTheory.LocDescent.exists_sec_descend | (intros; apply GlobalTheory.LocDescent.exists_sec_descend <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torusCoordinate_value_eq_of_maps : ∀ {R' : Type} [CommRing R'] [IsDomain R'] {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G'] (g : GtCoord I' D' e G') (F : D'.P.A.left ⟶ D'.P.A.left) (w : LB.Iso D'.P.L (D'.P.L.pull F)) (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left) (x : D'.X) (hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG x k) (hψ' : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f' ≫ D'.Oφ g.pG x k), LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t x)) → LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f' _ Oinvε _ hψ' (g.t x)) → ∀ (z : (thickObj R' I' e G').left) (J : ((thickObj R' I' e G').left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (g.t x) f z J = val (g.t x) f' z J := by
  first | exact @GlobalTheory.Mum.gtCoord_val_eq_of_maps | exact GlobalTheory.Mum.gtCoord_val_eq_of_maps | (intros; apply GlobalTheory.Mum.gtCoord_val_eq_of_maps <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_globalGenerator_div_baseUnit_eq_generic : ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K), φ ≫ X.hom = p ≫ spMap (algebraMap R K) → ∀ (M : LB X.left) (c : LB.Gen (M.pull φ)) (a : Kˣ) (b : Rˣ), algebraMap R K (b : R) = (a : K) → ∀ (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), φ (r z) ∈ M.U i → (gm (r ≫ φ) z (M.U i) (u.s i)).val = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull φ).U fun _ => i) (c.s fun _ => i)).val) → ∃ r' : LB.Gen M, r'.IsGen ∧ LB.genPull M r' φ = c := by
  first | exact @GlobalTheory.DivConst.exists_genPull_eq | exact GlobalTheory.DivConst.exists_genPull_eq | (intros; apply GlobalTheory.DivConst.exists_genPull_eq <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.frameSection_slice_eq_poly_div_det_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) [DecidableEq X.Ψ], (∀ x : Frame X.Ψ r, x ∈ X.dom ↔ ∀ τ, (mat x τ).det ≠ 0) → ∀ (la : Wt X.Ψ r) (N : ℕ), (∀ τ i, 0 ≤ la τ i + N) → ∀ P : Frame X.Ψ r → ℂ, X.IsSec la P → ∀ x ∈ X.dom, ∀ τ : X.Ψ, ∃ F : MvPolynomial (Fin r × Fin r) ℂ, F.IsHomogeneous (∑ i, (la τ i + N).toNat) ∧ ∀ y : Fin r → Fin r → ℂ, (Matrix.of y).det ≠ 0 → P (Function.update x τ y) = MvPolynomial.eval (fun ij => y ij.1 ij.2) F * ((Matrix.of y).det)⁻¹ ^ N := by
  first | exact @GlobalTheory.section_slice_eq_poly_div_det_pow | exact GlobalTheory.section_slice_eq_poly_div_det_pow | (intros; apply GlobalTheory.section_slice_eq_poly_div_det_pow <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdicPt

open IsLocalRing

private theorem factor_range {S : Type} [CommRing S] {Y : Scheme.{0}} {A : CommRingCat.{0}} (j : Spec A ⟶ Y)
    [IsOpenImmersion j] (f : Spec (CommRingCat.of S) ⟶ Y) (h : Set.range f ⊆ Set.range j) :
    ∃ φ : A ⟶ CommRingCat.of S, Spec.map φ ≫ j = f :=
  ⟨Spec.preimage (IsOpenImmersion.lift j f h), by rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩

private theorem range_subset {S : Type} [CommRing S] [IsLocalRing S] {Y : Scheme.{0}} {A : CommRingCat.{0}}
    (j : Spec A ⟶ Y) [IsOpenImmersion j] (f : Spec (CommRingCat.of S) ⟶ Y)
    (h : f (closedPoint S) ∈ Set.range j) : Set.range f ⊆ Set.range j := by
  rintro _ ⟨y, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint y).map f.continuous).mem_open j.isOpenEmbedding.isOpen_range h

variable {R : Type} [CommRing R] [IsLocalRing R] {a : R}

private theorem quot_local (ha : ¬ IsUnit a) (m : ℕ) : IsLocalRing (R ⧸ Ideal.span {a ^ (m + 1)}) := by
  haveI : Nontrivial (R ⧸ Ideal.span {a ^ (m + 1)}) := by
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun h => ha (isUnit_of_dvd_unit (dvd_pow_self a (Nat.succ_ne_zero m)) h)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

private theorem spec_closed {S S' : Type} [CommRing S] [CommRing S'] [IsLocalRing S] [IsLocalRing S']
    (f : S →+* S') (hf : Function.Surjective f) {Y : Scheme.{0}} (g : Spec (CommRingCat.of S) ⟶ Y) :
    (Spec.map (CommRingCat.ofHom f) ≫ g) (closedPoint S') = g (closedPoint S) := by
  haveI : IsLocalHom f := IsLocalHom.of_surjective f hf
  haveI : IsLocalHom (CommRingCat.ofHom f).hom := this
  exact congrArg g (Spec_closedPoint (f := CommRingCat.ofHom f))

theorem scheme_ext (ha : ¬ IsUnit a) (hc : IsAdicComplete (Ideal.span {a}) R) {Y : Scheme.{0}}
    (f g : Spec (CommRingCat.of R) ⟶ Y)
    (h : ∀ m : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a ^ m}))) ≫ f =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a ^ m}))) ≫ g) : f = g := by
  haveI := quot_local ha 0
  have hcl : f (closedPoint R) = g (closedPoint R) := by
    rw [← spec_closed (Ideal.Quotient.mk (Ideal.span {a ^ (0 + 1)})) Ideal.Quotient.mk_surjective f,
      ← spec_closed (Ideal.Quotient.mk (Ideal.span {a ^ (0 + 1)})) Ideal.Quotient.mk_surjective g, h]
  obtain ⟨A, j, _, hx, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := f (closedPoint R)) (U := ⊤) trivial
  obtain ⟨φ, rfl⟩ := factor_range j f (range_subset j f hx)
  obtain ⟨ψ, rfl⟩ := factor_range j g (range_subset j g (hcl ▸ hx))
  congr 2
  ext z
  refine ChPt.eq_of_mod a hc.toIsHausdorff _ _ fun m => ?_
  have e := h m
  rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at e
  exact congrArg (fun k => k.hom z) (Spec.map_injective e)

theorem scheme_lim (ha : ¬ IsUnit a) (hc : IsAdicComplete (Ideal.span {a}) R) {Y : Scheme.{0}}
    (y : ∀ m : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {a ^ m})) ⟶ Y)
    (hy : ∀ m : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (Nat.le_succ m))))) ≫ y (m + 1) = y m) :
    ∃ Q : Spec (CommRingCat.of R) ⟶ Y, ∀ m : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a ^ m}))) ≫ Q = y m := by
  haveI := quot_local ha
  obtain ⟨A, j, _, hx, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := y (0 + 1) (closedPoint _)) (U := ⊤) trivial
  have hcl : ∀ m : ℕ, y (m + 1) (closedPoint _) ∈ Set.range j := by
    intro m
    induction m with
    | zero => exact hx
    | succ m ih =>
      have e := spec_closed _ (Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow a (Nat.le_succ (m + 1))))) (y (m + 1 + 1))
      rw [hy (m + 1)] at e
      obtain ⟨u, hu⟩ := ih
      exact ⟨u, hu.trans e⟩
  have hr : ∀ m : ℕ, Set.range (y m) ⊆ Set.range j := by
    intro m
    rw [← hy m]
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact range_subset j _ (hcl m) ⟨_, rfl⟩
  choose φ hφ using fun m => factor_range j (y m) (hr m)
  obtain ⟨L, hL⟩ := ChPt.algLimSt ℤ A R a hc (fun m => (φ m).hom.toIntAlgHom) (by
    intro m z w hw
    have e := hy m
    rw [← hφ, ← hφ, ← Category.assoc, cancel_mono, ← Spec.map_comp] at e
    have e' := congrArg (fun k => k.hom z) (Spec.map_injective e)
    exact (congrArg (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (Nat.le_succ m)))) hw).trans e')
  refine ⟨Spec.map (CommRingCat.ofHom L.toRingHom) ≫ j, fun m => ?_⟩
  rw [← hφ m, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext z
  exact congrArg (fun k => k z) (hL m)

theorem existsUnique_lim : ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] (a : R), ¬ IsUnit a → IsAdicComplete (Ideal.span {a}) R → ∀ (X : Over (Spec (CommRingCat.of O))) (x : ∀ m : ℕ, specO O (R ⧸ Ideal.span {a ^ m}) ⟶ X), (∀ m : ℕ, ptMap (Ideal.Quotient.factorₐ O (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (Nat.le_succ m)))) ≫ x (m + 1) = x m) → ∃! Q : specO O R ⟶ X, ∀ m : ℕ, ptMap (Ideal.Quotient.mkₐ O (Ideal.span {a ^ m})) ≫ Q = x m := by
  intro O R _ _ _ _ a ha hc X x hx
  obtain ⟨Q, hQ⟩ := scheme_lim ha hc (Y := X.left) (fun m => (x m).left)
    (fun m => congrArg CommaMorphism.left (hx m))
  have hw : Q ≫ X.hom = (specO O R).hom := by
    refine scheme_ext ha hc _ _ fun m => ?_
    rw [← Category.assoc, hQ]
    exact (Over.w (x m)).trans (Over.w (ptMap (Ideal.Quotient.mkₐ O (Ideal.span {a ^ m})))).symm
  refine ⟨Over.homMk Q hw, fun m => Over.OverMorphism.ext (hQ m), fun Q' hQ' => Over.OverMorphism.ext ?_⟩
  refine scheme_ext ha hc _ _ fun m => ?_
  exact (congrArg CommaMorphism.left (hQ' m)).trans (hQ m).symm

end GlobalTheory.AdicPt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT


theorem _root_.GlobalTheory.T.exists_linearization_prod : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ga Gb : Type) [Group Ga] [Group Gb] (ρ₁ : Ga → (X ⟶ X)) (ρ₂ : Gb → (X ⟶ X)) (ρ : Ga × Gb → (X ⟶ X)), (∀ p, ρ p = ρ₁ p.1 ≫ ρ₂ p.2) → (∀ a b, ρ₁ a ≫ ρ₂ b = ρ₂ b ≫ ρ₁ a) → (∀ a c, ρ₁ (a * c) = ρ₁ a ≫ ρ₁ c) → (∀ b d, ρ₂ (b * d) = ρ₂ b ≫ ρ₂ d) → ∀ (v₁ : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ₁ a] ![1, -1])) (v₂ : ∀ b, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ₂ b] ![1, -1])), (∀ a, (v₁ a).IsGen) → (∀ b, (v₂ b).IsGen) → (∀ a c, LB.Gen.Corr L _ _ _ _ (v₁ (a * c)) (LB.mulGen L _ _ _ _ (v₁ a) (LB.pullGen L _ _ (v₁ c) (ρ₁ a)))) → (∀ b d, LB.Gen.Corr L _ _ _ _ (v₂ (b * d)) (LB.mulGen L _ _ _ _ (v₂ b) (LB.pullGen L _ _ (v₂ d) (ρ₂ b)))) → (∀ a b, LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ (v₁ a) (LB.pullGen L _ _ (v₂ b) (ρ₁ a))) (LB.mulGen L _ _ _ _ (v₂ b) (LB.pullGen L _ _ (v₁ a) (ρ₂ b)))) → ∃ u : ∀ p : Ga × Gb, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ p] ![1, -1]), (∀ p, (u p).IsGen) ∧ ∀ p q, LB.Gen.Corr L _ _ _ _ (u (p * q)) (LB.mulGen L _ _ _ _ (u p) (LB.pullGen L _ _ (u q) (ρ p))) := by
  first | exact @GlobalTheory.ProdLin.exists_linearisation_prod | exact GlobalTheory.ProdLin.exists_linearisation_prod | (intros; apply GlobalTheory.ProdLin.exists_linearisation_prod <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.exists_typicalCurve_basis_adapted_to_saturated_frame : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d h : ℕ), 0 < h → ∀ (ty : Fin d → ZMod h) (G : LogFGL v d), MuAction G p h ty → ∀ (τ : ZMod h) (j i : ℕ), (Finset.univ.filter fun a => ty a = τ + 1).card ≤ j → ∀ u : Fin i → Fin d → C, IsSatFrame v u → (∀ a e, ty e ≠ τ → u a e = 0) → ∃ (γ : Fin d → Fin d → PowerSeries C) (r : Fin i ↪ Fin d) (g : Matrix (Fin i) (Fin i) C), IsBasis G p ty γ ∧ (∀ a b, IsIntV v (g a b)) ∧ v g.det = 0 ∧ (∀ a, tangent (γ (r a)) = ∑ a', g a a' • u a') ∧ ∀ a : Fin i, j ≤ a.val → G.lc p (γ (r a)) 1 = 0 := by
  first | exact @GlobalTheory.FGDepth.exists_basis_adapted_frame | exact GlobalTheory.FGDepth.exists_basis_adapted_frame | (intros; apply GlobalTheory.FGDepth.exists_basis_adapted_frame <;> assumption)
end
