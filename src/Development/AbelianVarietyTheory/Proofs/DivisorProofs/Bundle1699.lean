module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle875
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle984
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamUnifHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle939
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Etale
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.DiagLimit

theorem isIntHom_diagonal_of_limit :
    ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d : ℕ) (G : LogFGL v d) (κ : Type) [Fintype κ] [DecidableEq κ] (U : Matrix (Fin d) κ C) (L : Matrix κ (Fin d) C), (∀ a b, IsIntV v (U a b)) → (∀ a b, IsIntV v (L a b)) → U * L = 1 → ∀ t : κ → C, (∀ r : ℝ, ∃ (t' : κ → C) (A : Matrix (Fin d) (Fin d) C) (φ : Fin d → MvPowerSeries (Fin d) C), IsIntHom G G φ A ∧ (∀ ℓ, A.mulVec (fun e => U e ℓ) = t' ℓ • fun e => U e ℓ) ∧ ∀ ℓ, (r : WithTop ℝ) ≤ v (t' ℓ - t ℓ)) → ∃ φ, IsIntHom G G φ (U * Matrix.diagonal t * L) := by
  intro C _ _ v d G κ _ _ U L hU hL hUL t h
  obtain ⟨φ, h1, h2, h3⟩ := GlobalTheory.IntegralEndLimit.integral_of_limit C v d G
    (U * Matrix.diagonal t * L) (fun r => by
      obtain ⟨t', A, φ, hφ, hA, ht⟩ := h r
      refine ⟨A, fun a b => ?_, φ, hφ.2.1, hφ.1, hφ.2.2⟩
      have e1 : A * U = U * Matrix.diagonal t' := by
        ext e ℓ
        have := congrFun (hA ℓ) e
        rw [Matrix.mul_diagonal, mul_comm]
        exact this
      have e2 : A = U * Matrix.diagonal t' * L := by
        rw [← e1, Matrix.mul_assoc, hUL, Matrix.mul_one]
      have e3 : (U * Matrix.diagonal t * L) a b - A a b =
          ∑ ℓ, U a ℓ * -(t' ℓ - t ℓ) * L ℓ b := by
        rw [e2, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
        ring
      rw [e3]
      refine v.map_le_sum fun ℓ _ => ?_
      rw [v.map_mul, v.map_mul, v.map_neg]
      have := add_le_add (add_le_add (show (0 : WithTop ℝ) ≤ v (U a ℓ) from hU a ℓ) (ht ℓ))
        (show (0 : WithTop ℝ) ≤ v (L ℓ b) from hL ℓ b)
      rwa [zero_add, add_zero] at this)
  exact ⟨φ, h2, h1, h3⟩

end GlobalTheory.DiagLimit
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isUnit_res_of_le_basicOpen {X : Scheme.{0}} {U V : X.Opens} (f : Γ(X, U)) (hVU : V ≤ U)
    (h : V ≤ X.basicOpen f) : IsUnit ((X.presheaf.map (homOfLE hVU).op).hom f) := by
  have hu := (X.toRingedSpace.isUnit_res_basicOpen f).map (X.presheaf.map (homOfLE h).op).hom
  have e : X.presheaf.map (homOfLE hVU).op =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op ≫ X.presheaf.map (homOfLE h).op := by
    rw [← Functor.map_comp]; rfl
  rw [e]
  exact hu

theorem ratio_periodic_isReg : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (n : ℕ) (W : Fin n → A.left.Opens) (r : ∀ k, Fin n → Γ(A.left, W k)), IsRatioCover u.ex W r → ∀ (N : ℕ) (σ : Fin n → (Fin g → ℂ) → ℂ), (∀ k, DifferentiableOn ℂ (σ k) (pre u.ex (W k))) → (∀ k (l : u.Λ), ∀ z ∈ pre u.ex (W k), σ k (z + l) = σ k z) → (∀ k j, ∀ z ∈ pre u.ex (W k), z ∈ pre u.ex (W j) → σ k z = val u.ex _ (r k j) z ^ N * σ j z) → ∀ k, IsReg u.ex (W k) (σ k) := by
  intro A _ g L u hA n W r hR N σ hhol hper htr
  obtain ⟨-, -, -, -, hinf, hmono, -, -, hres, hev, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨-, hcov, hbasic, hself, hcoc⟩ := hR
  have hv : ∀ (U V : A.left.Opens) (h : V ≤ U) (b : Γ(A.left, U)), ∀ z ∈ pre u.ex V,
      val u.ex V ((A.left.presheaf.map (homOfLE h).op).hom b) z = val u.ex U b z :=
    fun U V h b z hz => hres U V h b z hz
  have hmul : ∀ (U : A.left.Opens), ∀ z ∈ pre u.ex U, ∀ a b : Γ(A.left, U),
      val u.ex U (a * b) z = val u.ex U a z * val u.ex U b z := by
    intro U z hz a b
    obtain ⟨e, he⟩ := hev U z hz
    rw [he, he, he]; exact map_mul e (a : Sec (str A) U) b
  have hsub : ∀ (U : A.left.Opens), ∀ z ∈ pre u.ex U, ∀ a b : Γ(A.left, U),
      val u.ex U (a - b) z = val u.ex U a z - val u.ex U b z := by
    intro U z hz a b
    obtain ⟨e, he⟩ := hev U z hz
    rw [he, he, he]; exact map_sub e (a : Sec (str A) U) b
  have hpow : ∀ (U : A.left.Opens), ∀ z ∈ pre u.ex U, ∀ (a : Γ(A.left, U)) (m : ℕ),
      val u.ex U (a ^ m) z = val u.ex U a z ^ m := by
    intro U z hz a m
    obtain ⟨e, he⟩ := hev U z hz
    rw [he, he]; exact map_pow e (a : Sec (str A) U) m
  have hunit : ∀ k j, IsUnit ((A.left.presheaf.map (homOfLE (inf_le_left : W k ⊓ W j ≤ W k)).op).hom (r k j)) :=
    fun k j => isUnit_res_of_le_basicOpen _ _ (hbasic k j).ge
  let M : LB A.left := ⟨Fin n, W, fun k j => (hunit k j).unit ^ N⟩
  have hMg : ∀ k j, ((M.g k j : Γ(A.left, W k ⊓ W j))) =
      ((A.left.presheaf.map (homOfLE (inf_le_left : W k ⊓ W j ≤ W k)).op).hom (r k j)) ^ N := by
    intro k j
    change (((hunit k j).unit ^ N : Γ(A.left, W k ⊓ W j)ˣ) : Γ(A.left, W k ⊓ W j)) = _
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]

  have hval : ∀ k j (V : A.left.Opens) (h : V ≤ W k ⊓ W j), ∀ z ∈ pre u.ex V,
      val u.ex V ((res h (M.g k j) : Γ(A.left, V))) z = val u.ex (W k) (r k j) z ^ N := by
    intro k j V h z hz
    have hz' : z ∈ pre u.ex (W k ⊓ W j) := hmono _ _ h hz
    have e1 : ((res h (M.g k j) : Γ(A.left, V))) =
        (A.left.presheaf.map (homOfLE h).op).hom (M.g k j : Γ(A.left, W k ⊓ W j)) := rfl
    rw [e1, hv _ _ h _ z hz, hMg, hpow _ z hz', hv _ _ _ _ z hz']
  have hM : M.IsLB := by
    refine ⟨hcov, fun k => ?_, fun k j l => ?_⟩
    · apply Units.ext
      change (A.left.presheaf.map _).hom (M.g k k : Γ(A.left, W k ⊓ W k)) = 1
      rw [hMg, hself k, map_one, one_pow, map_one]
    · apply Units.ext
      rw [Units.val_mul]
      apply sub_eq_zero.mp
      apply GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA
      intro z hz
      have hk : z ∈ pre u.ex (W k) := hmono _ _ (inf_le_left.trans inf_le_left) hz
      have hj : z ∈ pre u.ex (W j) := hmono _ _ (inf_le_left.trans inf_le_right) hz
      rw [hsub _ z hz, hmul _ z hz, hval _ _ _ _ z hz, hval _ _ _ _ z hz, hval _ _ _ _ z hz,
        hcoc k j l z hk hj, mul_pow, sub_self]
  have htrans : ∀ i j, ∀ z ∈ pre u.ex (M.U i ⊓ M.U j),
      σ i z = val u.ex _ (M.g i j).val z * σ j z := by
    intro i j z hz
    have hz' : z ∈ pre u.ex (W i ⊓ W j) := hz
    rw [hinf] at hz'
    have e := hval i j (W i ⊓ W j) le_rfl z hz
    have e2 : ((res (le_rfl : W i ⊓ W j ≤ W i ⊓ W j) (M.g i j) : Γ(A.left, W i ⊓ W j))) = (M.g i j).val := by
      change (A.left.presheaf.map (homOfLE le_rfl).op).hom _ = _
      have : (homOfLE (le_rfl : W i ⊓ W j ≤ W i ⊓ W j)).op = 𝟙 _ := rfl
      rw [this, CategoryTheory.Functor.map_id]; rfl
    rw [e2] at e
    change σ i z = val u.ex (W i ⊓ W j) (M.g i j).val z * σ j z
    rw [e]
    exact htr i j z hz'.1 hz'.2
  exact GlobalTheory.T.periodic_holomorphic_sections_regular_abelianVariety A g L u hA M hM σ hhol hper htrans

end GlobalTheory.CechPer
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem smooth_of_openImm {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (g : ℕ) (hs : SmoothOfRelativeDimension g s) (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B))
    [IsOpenImmersion x] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap R B) ∧ Algebra.Smooth R B := by
  have h : SmoothOfRelativeDimension g (x ≫ s) := by
    have := smoothOfRelativeDimension_comp 0 g x s
    simpa using this
  rw [hx] at h
  constructor
  · exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension g)).1 h
  · have h2 : Smooth (spMap (algebraMap R B)) := SmoothOfRelativeDimension.smooth g _
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 h2)

theorem rankAtStalk_kaehler_of_locally {R B : Type} [CommRing R] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (g : ℕ) (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap R B))
    (p : PrimeSpectrum B) : Module.rankAtStalk Ω[B⁄R] p = g := by
  obtain ⟨s, hs, H⟩ := h
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p.asIdeal := by
    by_contra! hc
    exact p.2.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  let Bt := Localization.Away t
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension g R Bt :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap g).1
      (by rw [IsScalarTower.algebraMap_eq R B Bt]; exact H t ht)
  have : Algebra.FormallyEtale B Bt := .of_isLocalization (Submonoid.powers t)
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B Bt
  obtain ⟨q, hq⟩ : ∃ q : PrimeSpectrum Bt, PrimeSpectrum.comap (algebraMap B Bt) q = p := by
    have : p ∈ Set.range (PrimeSpectrum.comap (algebraMap B Bt)) := by
      rw [PrimeSpectrum.localization_away_comap_range Bt t]
      exact htp
    exact this
  have : Nontrivial Bt := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨q⟩
  have : Algebra.IsStandardSmooth R Bt := hstd.isStandardSmooth
  have : Module.Free Bt Ω[Bt⁄R] := Algebra.IsStandardSmooth.free_kaehlerDifferential
  have h1 := Module.rankAtStalk_baseChange (R := B) (S := Bt) (M := Ω[B⁄R]) q
  rw [hq] at h1
  rw [← h1, Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_eq_finrank_of_free]
  have hf : Module.finrank Bt Ω[Bt⁄R] = g := by
    rw [Module.finrank, Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := Bt) g]
    simp
  simp [hf]

theorem globForm_FP : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → FP R (GlobForm A.hom) g := by
  intro R _ A _ g hA hg
  obtain ⟨hF, h0, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hg
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.glob1_finite_and_projective R _ (OAff A.hom) hF h0
  refine ⟨hfin, hproj, fun p ↦ ?_⟩

  have hη : (η[A]).left ≫ A.hom = 𝟙 _ := by simpa using Over.w η[A]
  let x : A.left := (η[A]).left.base p
  have hxp : A.hom.base x = p := by
    change ((η[A]).left ≫ A.hom).base p = p
    rw [hη]; rfl
  obtain ⟨U, hU⟩ : ∃ U : A.left.affineOpens, x ∈ U.1 := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x)
      isOpen_univ
    exact ⟨⟨V, hV⟩, hxV⟩
  let T : AffOp A.left := Opposite.op U
  let B := (OAff A.hom).obj T
  have hUa : IsAffineOpen U.1 := U.2
  obtain ⟨q, hq⟩ : ∃ q : Sp (Sec A.hom U.1), (affPt A.hom U).base q = x := by
    have : x ∈ Set.range hUa.fromSpec.base := by
      rw [hUa.range_fromSpec]; exact hU
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq⟩
  have hqp : PrimeSpectrum.comap (algebraMap R (Sec A.hom U.1)) q = p := by
    have := congrArg (fun f ↦ f.base q) (affPt_w A.hom U)
    change A.hom.base ((affPt A.hom U).base q) = _ at this
    rw [hq, hxp] at this
    exact this.symm
  haveI : IsOpenImmersion (affPt A.hom U) := IsAffineOpen.isOpenImmersion_fromSpec hUa
  obtain ⟨hloc, hsm⟩ := smooth_of_openImm A.hom g hg (affPt A.hom U) (affPt_w A.hom U)
  have hrk := rankAtStalk_kaehler_of_locally g hloc q
  let e : Glob1 (OAff A.hom) →ₗ[R] Ω[B⁄R] := (LinearMap.proj T).comp (Glob1 (OAff A.hom)).subtype
  have he : IsBaseChange B e := GlobalTheory.T.isBaseChange_compatibleGlobalOneForms R _ (OAff A.hom) hF h0 T e (fun _ ↦ rfl)
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := Glob1 (OAff A.hom)) (S := B) q
  rw [Module.rankAtStalk_eq_of_equiv he.equiv] at h1
  rw [← hqp]
  exact h1.symm.trans hrk

end GlobalTheory.AbCoh
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.IsogDim

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

def frobImage {N : Type} [AddCommGroup N] [Module (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N)
    (X : Submodule (WittVector p k) N) : Submodule (WittVector p k) N where
  carrier := {m | ∃ n ∈ X, F n = m}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, X.add_mem ha hb, map_add F a b⟩
  zero_mem' := ⟨0, X.zero_mem, map_zero F⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    obtain ⟨d, rfl⟩ := (WittVector.frobeniusEquiv p k).surjective c
    refine ⟨d • a, X.smul_mem d ha, ?_⟩
    rw [map_smulₛₗ, WittVector.frobeniusEquiv_apply]

theorem mem_frobImage {N : Type} [AddCommGroup N] [Module (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N)
    (X : Submodule (WittVector p k) N) (m : N) : m ∈ frobImage F X ↔ ∃ n ∈ X, F n = m := Iff.rfl

theorem length_frobImage {N : Type} [AddCommGroup N] [Module (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N) (hF : Function.Injective F)
    (X : Submodule (WittVector p k) N) :
    Module.length (WittVector p k)
        (frobImage F ⊤ ⧸ Submodule.comap (frobImage F ⊤).subtype (frobImage F X)) =
      Module.length (WittVector p k) (N ⧸ X) := by
  haveI : RingHomSurjective (WittVector.frobenius : WittVector p k →+* WittVector p k) :=
    ⟨fun c => by
      obtain ⟨d, rfl⟩ := (WittVector.frobeniusEquiv p k).surjective c
      exact ⟨d, by rw [WittVector.frobeniusEquiv_apply]⟩⟩
  let f : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] frobImage F ⊤ :=
    LinearMap.codRestrict (frobImage F ⊤) F (fun c => ⟨c, Submodule.mem_top, rfl⟩)
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => hF (congrArg Subtype.val h), ?_⟩
    rintro ⟨m, n, -, rfl⟩
    exact ⟨n, rfl⟩
  have hX : Submodule.orderIsoMapComapOfBijective f hf X =
      Submodule.comap (frobImage F ⊤).subtype (frobImage F X) := by
    ext ⟨m, hm⟩
    change (⟨m, hm⟩ : frobImage F ⊤) ∈ Submodule.map f X ↔ _
    rw [Submodule.mem_map, Submodule.mem_comap]
    constructor
    · rintro ⟨n, hn, h⟩
      exact ⟨n, hn, congrArg Subtype.val h⟩
    · rintro ⟨n, hn, h⟩
      exact ⟨n, hn, Subtype.ext h⟩
  rw [Module.length_quotient, Module.length_quotient, ← hX, Order.coheight_orderIso]

theorem finite_of_frob_surj {N U : Type} [AddCommGroup N] [Module (WittVector p k) N]
    [Module.Finite (WittVector p k) N] [AddCommGroup U] [Module k U] (θ : N →+ U)
    (hθ : Function.Surjective θ)
    (hs : ∀ (a : WittVector p k) n, θ (WittVector.frobenius a • n) = WittVector.constantCoeff a • θ n) :
    Module.Finite k U := by
  classical
  obtain ⟨s, hs'⟩ := (Module.Finite.fg_top : (⊤ : Submodule (WittVector p k) N).FG)
  refine ⟨⟨s.image θ, ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro u -
  obtain ⟨n, rfl⟩ := hθ u
  have hn : n ∈ Submodule.span (WittVector p k) (s : Set N) := hs' ▸ Submodule.mem_top
  induction hn using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    obtain ⟨b, rfl⟩ := (WittVector.frobeniusEquiv p k).surjective a
    rw [WittVector.frobeniusEquiv_apply, hs]
    exact Submodule.smul_mem _ _ hx

end GlobalTheory.Dieu.IsogDim

namespace GlobalTheory.Dieu.IsogDim

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem isog_core (T : GlobalTheory.Dieu.Theory p) {G H : PDivGroup p k} (q : G ⟶ H)
    (hq : IsIsog q) :
    Function.Injective (T.map q) ∧
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ ∧
    Module.finrank k G.omega = Module.finrank k H.omega := by
  obtain ⟨n, q', h1, h2⟩ := hq
  have huv : ∀ m : T.M G, T.map q (T.map q' m) = p ^ n • m := by
    intro m
    rw [← LinearMap.comp_apply, ← T.base.map_comp' trivial trivial trivial q q', h1,
      T.base.map_pow_smul trivial trivial, T.base.map_id' trivial, LinearMap.id_apply]
  have hvu : ∀ m : T.M H, T.map q' (T.map q m) = p ^ n • m := by
    intro m
    rw [← LinearMap.comp_apply, ← T.base.map_comp' trivial trivial trivial q' q, h2,
      T.base.map_pow_smul trivial trivial, T.base.map_id' trivial, LinearMap.id_apply]
  have hinj : Function.Injective (T.map q) := by
    intro a b hab
    have h := congrArg (T.map q') hab
    rw [hvu a, hvu b] at h
    have h0 : p ^ n • (a - b) = 0 := by rw [smul_sub, h, sub_self]
    exact sub_eq_zero.1 (T.base.eq_zero_of_pow_smul (G := H) trivial n _ h0)
  have LA := (GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M H) (T.M G)).1 (T.map q) (T.map q') hinj
  have LB := (GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M G) (T.M G)).2.1 (T.base.free G trivial)
    (T.base.finite G trivial) n (T.map q ∘ₗ T.map q') (fun a => huv a)
  rw [LB] at LA
  have hfin : Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ := by
    intro h
    rw [h, top_add] at LA
    exact ENat.natCast_ne_top _ LA
  refine ⟨hinj, hfin, ?_⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k
  have dimω : ∀ K : PDivGroup p k,
      Module.length (WittVector p k) (T.M K ⧸ frobImage (T.F K) ⊤) = Module.finrank k K.omega := by
    intro K
    obtain ⟨-, hs, hk, hl, -⟩ := hθ K
    haveI : Module.Finite (WittVector p k) (T.M K) := T.base.finite K trivial
    haveI := finite_of_frob_surj (θ K) hs hl
    refine (GlobalTheory.T.length_ge_finrank_of_semilinear_surjective p k (T.M K) K.omega (WittVector.frobeniusEquiv p k) (θ K) hs ?_
      (frobImage (T.F K) ⊤)).2 ?_
    · intro a m
      rw [WittVector.frobeniusEquiv_apply]
      exact hl a m
    · intro m
      rw [hk, mem_frobImage]
      constructor
      · rintro ⟨c, -, h⟩
        exact ⟨c, h.symm⟩
      · rintro ⟨c, h⟩
        exact ⟨c, Submodule.mem_top, h.symm⟩
  have hF : ∀ y : T.M H, T.map q (T.F H y) = T.F G (T.map q y) :=
    T.base.map_F trivial trivial q
  set X := LinearMap.range (T.map q) with hXdef
  set L3 := frobImage (T.F G) X with hL3
  set FG := frobImage (T.F G) ⊤ with hFG
  set FH := frobImage (T.F H) ⊤ with hFH
  have hle : L3 ≤ FG := by
    rintro m ⟨c, -, rfl⟩
    exact ⟨c, Submodule.mem_top, rfl⟩
  have hr1 : LinearMap.range (FG.subtype ∘ₗ (Submodule.comap FG.subtype L3).subtype) = L3 := by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hle]
  have hr2 : LinearMap.range (T.map q ∘ₗ FH.subtype) = L3 := by
    ext m
    rw [LinearMap.mem_range, hL3, mem_frobImage]
    constructor
    · rintro ⟨⟨x, y, -, rfl⟩, rfl⟩
      exact ⟨T.map q y, LinearMap.mem_range.2 ⟨y, rfl⟩, (hF y).symm⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hz
      exact ⟨⟨T.F H y, y, Submodule.mem_top, rfl⟩, hF y⟩
  have eA := (GlobalTheory.T.witt_module_length_composition p k (T.M G) FG (Submodule.comap FG.subtype L3)).1
    FG.subtype (Submodule.comap FG.subtype L3).subtype (Submodule.injective_subtype _)
  rw [hr1, Submodule.range_subtype, Submodule.range_subtype] at eA
  have eB := (GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M H) FH).1 (T.map q) FH.subtype hinj
  rw [hr2, Submodule.range_subtype] at eB
  have hC : Module.length (WittVector p k) (FG ⧸ Submodule.comap FG.subtype L3) =
      Module.length (WittVector p k) (T.M G ⧸ X) :=
    length_frobImage (T.F G) (GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G).1 X
  rw [hC, hFG, dimω G] at eA
  rw [hFH, dimω H] at eB
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 hfin
  rw [← hd] at eA eB
  have h' : ((Module.finrank k G.omega + d : ℕ) : ℕ∞) = ((d + Module.finrank k H.omega : ℕ) : ℕ∞) := by
    push_cast
    exact eA.symm.trans eB
  have h'' := Nat.cast_injective h'
  omega

end GlobalTheory.Dieu.IsogDim

namespace GlobalTheory.Dieu

theorem isog_finrank_omega : ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
    (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H),
    IsIsog q → Function.Injective (T.map q) ∧
      Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ ∧
      Module.finrank k G.omega = Module.finrank k H.omega ∧
      Module.finrank k G.dual.omega = Module.finrank k H.dual.omega := by
  intro p _ T k _ _ _ G H q hq
  obtain ⟨h1, h2, h3⟩ := IsogDim.isog_core T q hq
  obtain ⟨-, hd, -⟩ := GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k G H q hq
  exact ⟨h1, h2, h3, (IsogDim.isog_core T (dualHom G H q) hd).2.2.symm⟩

end GlobalTheory.Dieu
end
end

section

namespace GlobalTheory.AnPer

theorem gaussManinPeriods_of_span_taylor : PSpan → PTaylor → GlobalTheory.Published.GaussManinPeriods :=
  fun HS HT ↦ gaussManinPeriods_of_parts (-1) GlobalTheory.PeriodFamily.famUnif_holds GlobalTheory.T.periods_exist_affine_zero_section GlobalTheory.T.exists_integrationOverCyclesHom HS
    GlobalTheory.T.integrationOverCycles_lifts_lieLattice GlobalTheory.T.periodHom_push_end' GlobalTheory.T.pChern_neg_one GlobalTheory.T.fibrePeriod_eq_familyPeriod_value HT

end GlobalTheory.AnPer
end
