module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle488
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle866
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle364
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureUnitaryLatticeFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle835
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle868
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory


open GlobalTheory.PDivGroup.CotDim in
theorem GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] (hp : (p : k) = 0) (Γ : PDivGroup p k) :
    Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1)) ≤ Γ.height := by
  letI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 hp
  have hdimD := finrank_level_one Γ.dual
  have hmulP : Function.Injective (Γ.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := Γ.dual_mulP_surjective 1 φ
    change ψ.ofConv (Γ.mulP 1 a) = ψ.ofConv (Γ.mulP 1 b)
    rw [e]

  have hord := finrank_eq_ker_mul_range k (Γ.dual.A 1) _ ((PDivGroup.relFrob hp Γ.dual).app 1)
  have hcot (G : PDivGroup p k) :
      p ^ Module.finrank k (Cot k (G.A 1)) ≤
        Module.finrank k (G.A 1 ⧸ kerIdeal ((PDivGroup.relFrob hp G).app 1)) :=
    (FrobKerOrder.pow_finrank_cot_le (p := p) (k := k) (H := G.A 1)).trans
      (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp G 1))

  have hker : LinearMap.ker ((PDivGroup.verschiebung hp Γ).app 1 :
        Γ.A 1 →ₐ[k] (PDivGroup.frobTwist hp Γ).A 1).toLinearMap ≤
      (kerIdeal ((PDivGroup.relFrob hp Γ).app 1)).restrictScalars k := by
    intro a ha
    have h := GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero p k hp Γ a ha
    rw [kerIdeal_comp] at h
    change a ∈ kerIdeal ((PDivGroup.relFrob hp Γ).app 1)
    rw [← GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf k _ _ (Γ.mulP 1) hmulP
      (kerIdeal ((PDivGroup.relFrob hp Γ).app 1))]
    exact h
  have hV := GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung p k hp Γ
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((PDivGroup.relFrob hp Γ).app 1)).restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k (kerIdeal ((PDivGroup.relFrob hp Γ).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have hrD : Module.finrank k (Γ.A 1 ⧸ kerIdeal ((PDivGroup.relFrob hp Γ).app 1)) ≤
      Module.finrank k (LinearMap.range ((PDivGroup.relFrob hp Γ.dual).app 1 :
        (PDivGroup.frobTwist hp Γ.dual).A 1 →ₐ[k] Γ.dual.A 1).toLinearMap) := by omega
  apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1
  change _ ≤ p ^ Γ.dual.height
  rw [pow_add, mul_comm, ← hdimD, hord]
  exact Nat.mul_le_mul (hcot Γ.dual) ((hcot Γ).trans hrD)
end
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

noncomputable section

namespace GlobalTheory.SizeRat

theorem norm_ratCast (l : ℕ) [Fact l.Prime] (q : ℚ) : ‖(q : ℂ_[l])‖ = (padicNorm l q : ℝ) := by
  have e : ((q : ℚ_[l]) : ℂ_[l]) = (q : ℂ_[l]) := by simp only [PadicComplex.coe_eq, map_ratCast]
  rw [← e, PadicComplex.norm_extends', Padic.eq_padicNorm]

theorem sz_ratCast (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (q : ℚ) (r : ℝ)
    (hr : -(padicValRat l q : ℝ) ≤ r) : Sz l lam r (q : ℂ) := by
  have hmem : (q : ℂ) ∈ algebraicClosure ℚ ℂ := SubfieldClass.ratCast_mem _ q
  refine ⟨hmem, ?_⟩
  have e : (⟨(q : ℂ), hmem⟩ : algebraicClosure ℚ ℂ) = (q : algebraicClosure ℚ ℂ) := by
    apply Subtype.ext; simp
  have hl : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  rw [e, map_ratCast, norm_ratCast]
  by_cases hq : q = 0
  · subst hq; simp only [padicNorm.zero, Rat.cast_zero]; exact Real.rpow_nonneg (by linarith) r
  · rw [padicNorm.eq_zpow_of_nonzero hq, Rat.cast_zpow, Rat.cast_natCast, ← Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le hl (by push_cast; exact hr)

theorem sz_exp (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (q : ℚ) :
    Sz l lam 0 (Complex.exp ((2 * Real.pi * Complex.I) * (q : ℂ))) := by
  set ζ := Complex.exp ((2 * Real.pi * Complex.I) * (q : ℂ)) with hζ
  have hpow : ζ ^ q.den = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    have : (q.den : ℂ) * ((2 * Real.pi * Complex.I) * (q : ℂ)) = (q.num : ℂ) * (2 * Real.pi * Complex.I) := by
      have hq : (q : ℂ) = (q.num : ℂ) / (q.den : ℂ) := by exact_mod_cast (Rat.num_div_den q).symm
      have hd : (q.den : ℂ) ≠ 0 := by exact_mod_cast q.den_nz
      rw [hq]; field_simp
    rw [this]; exact Complex.exp_int_mul_two_pi_mul_I q.num
  have hmem : ζ ∈ algebraicClosure ℚ ℂ := by
    rw [mem_algebraicClosure_iff]
    exact (IsIntegral.of_pow q.den_pos (by rw [hpow]; exact isIntegral_one)).isAlgebraic
  refine ⟨hmem, ?_⟩
  have h1 : (⟨ζ, hmem⟩ : algebraicClosure ℚ ℂ) ^ q.den = 1 := by
    apply Subtype.ext; simp [hpow]
  have h2 : ‖lam ⟨ζ, hmem⟩‖ ^ q.den = 1 := by
    rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  have h3 : ‖lam ⟨ζ, hmem⟩‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) q.den_nz).mp h2
  rw [h3, Real.rpow_zero]

theorem sz_rat_exp : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]),
    (∀ (q : ℚ) (r : ℝ), (-(padicValRat l q : ℝ) ≤ r) → Sz l lam r (q : ℂ)) ∧
      ∀ q : ℚ, Sz l lam 0 (Complex.exp ((2 * Real.pi * Complex.I) * (q : ℂ))) :=
  fun l _ lam => ⟨sz_ratCast l lam, sz_exp l lam⟩

end GlobalTheory.SizeRat
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN)
open GlobalTheory.DeRham (spOver spOver_comp)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PDiv

universe u

theorem mono_of_injective_affinePts {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hinj : ∀ (R : CommRingCat.{u}) (a b : Spec R ⟶ X), a ≫ f = b ≫ f → a = b) : Mono f :=
  ⟨fun {W} a b h => W.affineOpenCover.openCover.hom_ext a b fun i =>
    hinj (W.affineOpenCover.X i) (W.affineOpenCover.f i ≫ a) (W.affineOpenCover.f i ≫ b)
      ((Category.assoc _ _ _).trans ((congrArg _ h).trans (Category.assoc _ _ _).symm))⟩

theorem isIso_of_bijective_affinePts {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ (R : CommRingCat.{u}), Function.Bijective fun a : Spec R ⟶ X => a ≫ f) : IsIso f := by
  have hm : Mono f := mono_of_injective_affinePts f fun R a b e => (h R).1 e
  let 𝒰 : Y.OpenCover := Y.affineOpenCover.openCover
  have hs : ∀ i : 𝒰.I₀, ∃ a : 𝒰.X i ⟶ X, a ≫ f = 𝒰.f i := fun i =>
    (h (Y.affineOpenCover.X i)).2 (Y.affineOpenCover.f i)
  choose g hg using hs
  have hc : ∀ i j : 𝒰.I₀, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j :=
    fun i j => (cancel_mono f).1 (by
      simp only [Category.assoc, hg]
      exact pullback.condition)
  let k : Y ⟶ X := 𝒰.glueMorphisms g hc
  have hk : k ≫ f = 𝟙 Y := 𝒰.hom_ext _ _ fun i => by
    have e := 𝒰.ι_glueMorphisms g hc i
    simp only [k, ← Category.assoc, e, hg, Category.comp_id]
  refine ⟨k, ?_, hk⟩
  exact (cancel_mono f).1 (by simp only [Category.assoc, hk, Category.comp_id, Category.id_comp])

end PDiv

end GlobalTheory

namespace GlobalTheory

namespace PDiv

variable {O : Type} [CommRing O]

theorem exists_spOver {B D : Type} [CommRing B] [Algebra O B] [CommRing D] [Algebra O D]
    (v : Over.mk (spMap (algebraMap O B)) ⟶ Over.mk (spMap (algebraMap O D))) :
    ∃ ψ : D →ₐ[O] B, spOver ψ = v := by
  let f : Sp B ⟶ Sp D := v.left
  let ψ₀ : D →+* B := (Spec.preimage f).hom
  have h0 : spMap ψ₀ = f := (congrArg Spec.map (CommRingCat.ofHom_hom _)).trans
    (Spec.map_preimage f)
  have e : CommRingCat.ofHom (ψ₀.comp (algebraMap O D)) = CommRingCat.ofHom (algebraMap O B) :=
    Spec.map_injective (by
      change spMap (ψ₀.comp (algebraMap O D)) = spMap (algebraMap O B)
      rw [Cris.spMap_comp, h0]
      exact Over.w v)
  have h1 : ψ₀.comp (algebraMap O D) = algebraMap O B := congrArg CommRingCat.Hom.hom e
  exact ⟨{ ψ₀ with commutes' := RingHom.congr_fun h1 }, Over.OverMorphism.ext h0⟩

theorem spMap_preimage_toAlgebra {R : CommRingCat.{0}} (s : Spec R ⟶ Sp O) :
    @spMap O R _ _ (@algebraMap O R _ _ (Spec.preimage s).hom.toAlgebra) = s :=
  (congrArg Spec.map (CommRingCat.ofHom_hom _)).trans (Spec.map_preimage s)

end PDiv

namespace PDivGroup.TorsionTower

open PDiv ReciprocityTheory.ChartRestriction.G.Semi

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {A : Over (Sp O)} [GrpObj A]
  (t : TorsionTower G A)

theorem y_comp_mulN (n : ℕ) : t.y n ≫ mulN A (p ^ n) = toUnit _ ≫ η[A] := by
  rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, t.y_pow]
  rfl

def toTorsion (n : ℕ) : SpAlg O (G.A n) ⟶ torsion A (p ^ n) :=
  pullback.lift (t.y n) (toUnit _) (t.y_comp_mulN n)

@[reassoc (attr := simp)] theorem toTorsion_ι (n : ℕ) :
    t.toTorsion n ≫ torsion.ι A (p ^ n) = t.y n :=
  pullback.lift_fst _ _ _

theorem toTorsion_left_injective (n : ℕ) (R : CommRingCat.{0}) :
    Function.Injective fun a : Spec R ⟶ (SpAlg O (G.A n)).left => a ≫ (t.toTorsion n).left := by
  intro a b e
  change a ≫ (t.toTorsion n).left = b ≫ (t.toTorsion n).left at e
  let s := a ≫ (SpAlg O (G.A n)).hom
  have hb : b ≫ (SpAlg O (G.A n)).hom = s := by
    simp only [s, ← Over.w (t.toTorsion n), ← Category.assoc, e]
  let _ : Algebra O R := (Spec.preimage s).hom.toAlgebra
  have hs : spMap (algebraMap O R) = s := spMap_preimage_toAlgebra s
  let a' : SpAlg O R ⟶ SpAlg O (G.A n) := Over.homMk a hs.symm
  let b' : SpAlg O R ⟶ SpAlg O (G.A n) := Over.homMk b (hb.trans hs.symm)
  obtain ⟨φ, hφ⟩ := exists_spOver a'
  obtain ⟨ψ, hψ⟩ := exists_spOver b'
  have hy : a' ≫ t.y n = b' ≫ t.y n := by
    have hab : a' ≫ t.toTorsion n = b' ≫ t.toTorsion n := Over.OverMorphism.ext e
    simpa only [Category.assoc, toTorsion_ι] using
      congrArg (fun q => q ≫ torsion.ι A (p ^ n)) hab
  rw [← hφ, ← hψ] at hy
  have h : φ = ψ := t.inj n R φ ψ hy
  exact congrArg Over.Hom.left (hφ.symm.trans ((congrArg spOver h).trans hψ))

theorem toTorsion_left_surjective (n : ℕ) (R : CommRingCat.{0}) :
    Function.Surjective fun a : Spec R ⟶ (SpAlg O (G.A n)).left => a ≫ (t.toTorsion n).left := by
  intro w
  let s := w ≫ (torsion A (p ^ n)).hom
  let _ : Algebra O R := (Spec.preimage s).hom.toAlgebra
  have hs : spMap (algebraMap O R) = s := spMap_preimage_toAlgebra s
  let z : SpAlg O R ⟶ torsion A (p ^ n) := Over.homMk w hs.symm
  have hx : (z ≫ torsion.ι A (p ^ n)) ^ p ^ n = 1 := by
    have hc : torsion.ι A (p ^ n) ≫ mulN A (p ^ n) = toUnit _ ≫ η[A] :=
      pullback.condition.trans (congrArg (· ≫ η[A]) (toUnit_unique _ _))
    rw [← Category.comp_id (z ≫ torsion.ι A (p ^ n)), ← MonObj.comp_pow,
      ← GrpTangent.mulN_eq_pow, Category.assoc, hc, ← Category.assoc]
    exact (congrArg (· ≫ η[A]) (toUnit_unique _ _)).trans rfl
  obtain ⟨φ, hφ⟩ := t.surj n R _ hx
  have e : spOver φ ≫ t.toTorsion n = z := by
    refine pullback.hom_ext ?_ (toUnit_unique _ _)
    change spOver φ ≫ t.toTorsion n ≫ torsion.ι A (p ^ n) = z ≫ torsion.ι A (p ^ n)
    rw [toTorsion_ι, hφ]
  exact ⟨(spOver φ).left, congrArg Over.Hom.left e⟩

instance isIso_toTorsion (n : ℕ) : IsIso (t.toTorsion n) := by
  have : IsIso ((Over.forget _).map (t.toTorsion n)) :=
    isIso_of_bijective_affinePts _ fun R =>
      ⟨t.toTorsion_left_injective n R, t.toTorsion_left_surjective n R⟩
  exact isIso_of_reflects_iso _ (Over.forget _)

def torsionIso (n : ℕ) : SpAlg O (G.A n) ≅ torsion A (p ^ n) :=
  haveI := t.isIso_toTorsion n
  asIso (t.toTorsion n)

@[reassoc (attr := simp)] theorem torsionIso_hom_ι (n : ℕ) :
    (t.torsionIso n).hom ≫ torsion.ι A (p ^ n) = t.y n :=
  t.toTorsion_ι n

theorem isPullback_y : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O))
    [GrpObj A] (t : TorsionTower G A) (n : ℕ), IsPullback (t.y n) (toUnit _) (mulN A (p ^ n)) η[A] := by
  intro p O _ G A _ t n
  exact IsPullback.of_iso_pullback ⟨t.y_comp_mulN n⟩ (t.torsionIso n) (t.torsionIso_hom_ι n)
    (pullback.lift_snd _ _ _)

end PDivGroup.TorsionTower

end GlobalTheory
end
end

section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

theorem _root_.GlobalTheory.T.exists_common_finiteExtension_galoisReps_characters : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n a t : ℕ) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (ρ : G E Ω →* GL (Fin a) (PadicAlgCl l)) (χ : Fin t → G E Ω →* (PadicAlgCl l)ˣ), Continuous r → Continuous ρ → (∀ s, Continuous (GlobalTheory.TripleGal.rk1 (χ s))) → ∃ LL : FinExt l, (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) ∧ (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) ∧ (∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ (∀ g i j, (ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j ∈ LL.1) ∧ ∀ s g, ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ∈ LL.1 := by
  first | exact @GlobalTheory.RepFinExtJoint.finext_joint | exact GlobalTheory.RepFinExtJoint.finext_joint | (intros; apply GlobalTheory.RepFinExtJoint.finext_joint <;> assumption)
end

section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

theorem _root_.GlobalTheory.T.norm_galoisCharacter_padicAlgClosure_eq_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (χ : G E Ω →* (PadicAlgCl l)ˣ), Continuous (GlobalTheory.TripleGal.rk1 χ) → ∀ g, ‖((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1 := by
  first | exact @GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one | exact GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one | (intros; apply GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.MVGlue

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem etale_awayMap : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] [Algebra.Etale A C] (f : A), @Algebra.Etale (Localization.Away f) (Localization.Away (algebraMap A C f)) _ _ (Localization.awayMap (algebraMap A C) f).toAlgebra := by
  intro A C _ _ _ _ f
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap A C f)) :=
    (Localization.awayMap (algebraMap A C) f).toAlgebra
  haveI : Algebra.Etale C (Localization.Away (algebraMap A C f)) := Algebra.Etale.of_isLocalizationAway (algebraMap A C f)
  haveI : Algebra.Etale A (Localization.Away f) := Algebra.Etale.of_isLocalizationAway f
  haveI : Algebra.Etale A (Localization.Away (algebraMap A C f)) := Algebra.Etale.comp A C _
  haveI : IsScalarTower A (Localization.Away f) (Localization.Away (algebraMap A C f)) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    show _ = Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) a)
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq, IsScalarTower.algebraMap_apply A C (Localization.Away (algebraMap A C f))]
  exact Algebra.Etale.of_restrictScalars A _ _

theorem pull_spMap_comp (q : ℕ) {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (n i : ℤ) (x : Ht q (sp A) n i) :
    pull _ (spMap (g.comp f)) _ _ x = pull _ (spMap g) _ _ (pull _ (spMap f) _ _ x) := by
  rw [spMap_comp', pull_comp]

theorem pull_spMap_id (q : ℕ) {A : Type} [CommRing A] (n i : ℤ) (x : Ht q (sp A) n i) :
    pull _ (spMap (RingHom.id A)) _ _ x = x := by
  have : spMap (RingHom.id A) = 𝟙 (sp A) := by
    simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
    exact sch.map_id _
  rw [this, pull_id]

theorem glue : ∀ (q : ℕ) (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → IsExcisionNbhd A C g → ∀ (n i : ℤ) (a : Ht q (sp (Localization.Away (f * g))) n i), pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → ∃ b : Ht q (sp (Localization.Away f)) n i, ∀ ρ : Localization.Away f →+* Localization.Away (f * g), ρ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ρ) _ _ b = a := by
  intro q A C _ _ _ f g hfg hC n i a ha
  obtain ⟨hEt, h1, h2⟩ := hC
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap A C f)) :=
    (Localization.awayMap (algebraMap A C) f).toAlgebra
  haveI : Algebra.Etale (Localization.Away f) (Localization.Away (algebraMap A C f)) := etale_awayMap A C f
  have hB : algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) =
      Localization.awayMap (algebraMap A C) f := rfl
  set h : Localization.Away f := algebraMap A (Localization.Away f) g with hh
  have c1 := GlobalTheory.T.away_congr_mod_of_isCoprime A C f g hfg h1
  have c2 := GlobalTheory.T.awayMap_span_singleton_divisibility_descends A C f g h2
  rw [← hB] at c1 c2

  have hu1 : IsUnit (((algebraMap (Localization.Away f) (Localization.Away h)).comp
      (algebraMap A (Localization.Away f))) (f * g)) := by
    rw [map_mul, RingHom.comp_apply, RingHom.comp_apply]
    refine IsUnit.mul ?_ ?_
    · exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f).map
        (algebraMap (Localization.Away f) (Localization.Away h))
    · exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away h) h
  let ψ : Localization.Away (f * g) →+* Localization.Away h :=
    IsLocalization.Away.lift (S := Localization.Away (f * g)) (f * g) hu1
  have hψ : ∀ x : A, ψ (algebraMap A _ x) = algebraMap _ _ (algebraMap A (Localization.Away f) x) := fun x => by
    simp only [ψ, IsLocalization.Away.lift_eq, RingHom.comp_apply]
  have hgB : algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) h =
      algebraMap C (Localization.Away (algebraMap A C f)) (algebraMap A C g) := by
    rw [hB, hh]
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have hu2 : IsUnit (((algebraMap (Localization.Away (algebraMap A C f))
      (Localization.Away (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) h))).comp
      (algebraMap C (Localization.Away (algebraMap A C f)))) (algebraMap A C (f * g))) := by
    rw [map_mul, map_mul, RingHom.comp_apply, RingHom.comp_apply, ← hgB]
    refine IsUnit.mul ?_ (IsLocalization.Away.algebraMap_isUnit _)
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap A C f)) (algebraMap A C f)).map _
  let χ : Localization.Away (algebraMap A C (f * g)) →+*
      Localization.Away (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) h) :=
    IsLocalization.Away.lift (S := Localization.Away (algebraMap A C (f * g))) (algebraMap A C (f * g)) hu2
  have hsq : (Localization.awayMap (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f))) h).comp ψ =
      χ.comp (Localization.awayMap (algebraMap A C) (f * g)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f * g))
    ext x
    simp only [RingHom.comp_apply, hψ, χ]
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq, IsLocalization.Away.lift_eq, hB]
  obtain ⟨b, hb, -⟩ := GlobalTheory.T.localization_pullback_injective q (Localization.Away f) (Localization.Away (algebraMap A C f)) h c1 c2 n i
    (pull _ (spMap ψ) _ _ a) 0 (by
      rw [map_zero, ← pull_spMap_comp, hsq, pull_spMap_comp, ha, map_zero])
  refine ⟨b, fun ρ hρ => ?_⟩
  have hρu : IsUnit (ρ h) := by
    rw [hh, ← RingHom.comp_apply, hρ, map_mul] at *
    exact isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (f * g))
  let ψ' : Localization.Away h →+* Localization.Away (f * g) :=
    IsLocalization.Away.lift (S := Localization.Away h) h hρu
  have h1' : ψ'.comp (algebraMap (Localization.Away f) (Localization.Away h)) = ρ :=
    IsLocalization.Away.lift_comp _ _
  have h2' : ψ'.comp ψ = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f * g))
    ext x
    simp only [RingHom.comp_apply, hψ, ψ', IsLocalization.Away.lift_eq, RingHom.id_apply]
    rw [← RingHom.comp_apply ρ, hρ]
  rw [← h1', pull_spMap_comp, hb, ← pull_spMap_comp, h2', pull_spMap_id]

end GlobalTheory.MVGlue
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal


theorem _root_.GlobalTheory.T.signature_unitary_lattice_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M p0 : ℕ) (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) (ι : Type) (S : Finset ι) (s : ι → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (Δ : ι → Subgroup (GL (Fin r) E)), 2 ≤ r → 1 ≤ M → SelfDualLat G L → (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → (∀ i ∈ S, IsSA G (s i)) → (∀ i ∈ S, ∀ j ∈ S, SEquiv G (L : Set (Fin r → E)) M (s i) (s j) → i = j) → (∀ i ∈ S, ∀ δ : GL (Fin r) E, (δ : Matrix (Fin r) (Fin r) E).det = 1 → (∀ u v, herm G ((δ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((δ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) → (δ ∈ Δ i ↔ IsKM (IsCMField.complexConj E) G (L : Set (Fin r → E)) M ((s i)⁻¹ * ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) * s i))) → ∃ (J : Type) (t : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), IsSReps G (L : Set (Fin r → E)) 1 t ∧ ∑ i ∈ S, covolume (inReal Ψ G (Δ i)) (realSU Ψ G) (riemHaar Ψ G x) ≤ (M : ℝ≥0∞) ^ (2 * fdeg E * r ^ 2) * ∑' j, covolume (inReal Ψ G (ratStab G (L : Set (Fin r → E)) (t j))) (realSU Ψ G) (riemHaar Ψ G x) := by
  first | exact @GlobalTheory.SUCount.sum_covolume_le_pow_mul_tsum | exact GlobalTheory.SUCount.sum_covolume_le_pow_mul_tsum | (intros; apply GlobalTheory.SUCount.sum_covolume_le_pow_mul_tsum <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.frameWeight_singularWeight_smooth_leviNonneg : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ δ : ℝ, (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → (∀ y ∈ U, y ∉ A.zeroSet s) → SmoothR n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y) ∧ SmoothR n (fun y : U => z y) (fun y : U => psi A L s y) ∧ ∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y + α * psi A L s y) := by
  first | exact @GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg | exact GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg | (intros; apply GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg <;> assumption)
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem _root_.GlobalTheory.T.specialUnitary_near_one_eq_chart_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (σ : V (nd X) → realSU X.Ψ X.Gm) (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (ρ : ℝ), IsOrth X x → 0 < ρ → σ 0 = 1 → ContinuousOn σ (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) → (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) → (∀ θ θ', t (θ + θ') = t θ * t θ') → Continuous t → (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) → ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ grpBall (realSU X.Ψ X.Gm) ε, ∃ w : ChartSp X, ‖w‖ < δ ∧ σ w.1 * t w.2 = g := by
  first | exact @GlobalTheory.eq_chart_mul_of_near_one | exact GlobalTheory.eq_chart_mul_of_near_one | (intros; apply GlobalTheory.eq_chart_mul_of_near_one <;> assumption)
end
