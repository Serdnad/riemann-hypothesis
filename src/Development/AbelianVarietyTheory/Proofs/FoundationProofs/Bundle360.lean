module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle340
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle341
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLevFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle347
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUpperTriangularConjIntegralCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad

theorem _root_.GlobalTheory.T.forall_ad_invariant_eq_zero_of_isIrr : ∀ {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) K), IsIrr ρ → ∀ v : Fin 3 → K, (∀ g, ad (ρ g) *ᵥ v = v) → v = 0 := by
  first | exact @GlobalTheory.ad_invariant_eq_zero_of_isIrr | exact GlobalTheory.ad_invariant_eq_zero_of_isIrr | (intros; apply GlobalTheory.ad_invariant_eq_zero_of_isIrr <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad

theorem _root_.GlobalTheory.T.traceForm_ne_zero_of_stable_line_irreducible : ∀ {K : Type} [Field K] [CharZero K] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) K), IsIrr ρ → ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, ad (ρ g) *ᵥ y = c • y) → form y y ≠ 0 := by
  first | exact @GlobalTheory.Sl2Ad.form_ne_zero_of_isIrr | exact GlobalTheory.Sl2Ad.form_ne_zero_of_isIrr | (intros; apply GlobalTheory.Sl2Ad.form_ne_zero_of_isIrr <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

theorem _root_.GlobalTheory.T.inertia_transports_kaehler_relations_over_invariants : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (s : G ℚ Ω), s ∈ Ine (F := ℚ) A → ∀ a b a' b' c d c' d' : A, (c : Ω) = s a → (d : Ω) = s b → (c' : Ω) = s a' → (d' : Ω) = s b' → a • dA A b = a' • dA A b' → c • dA A d = c' • dA A d' := by
  first | (exact @GlobalTheory.RecOne.transp_rel) | (exact GlobalTheory.RecOne.transp_rel) | (intros; apply GlobalTheory.RecOne.transp_rel  <;> assumption)
end

section




noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

abbrev ResL (c : Coef l) : Type := c.O ⧸ Ideal.span {((l : ℕ) : c.O)}


open Classical in
def redL (c : Coef l) (x : Qbar l) : ResL c :=
  if h : x ∈ c.O then Ideal.Quotient.mk _ ⟨x, h⟩ else 0

theorem redL_of_mem (c : Coef l) {x : Qbar l} (h : x ∈ c.O) :
    redL c x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : c.O)}) ⟨x, h⟩ := by
  simp [redL, h]

theorem redL_add (c : Coef l) {x y : Qbar l} (hx : x ∈ c.O) (hy : y ∈ c.O) :
    redL c (x + y) = redL c x + redL c y := by
  rw [redL_of_mem c hx, redL_of_mem c hy, redL_of_mem c (c.O.add_mem hx hy), ← map_add (f := _)]; rfl

theorem redL_sub (c : Coef l) {x y : Qbar l} (hx : x ∈ c.O) (hy : y ∈ c.O) :
    redL c (x - y) = redL c x - redL c y := by
  rw [redL_of_mem c hx, redL_of_mem c hy, redL_of_mem c (c.O.sub_mem hx hy), ← map_sub]; rfl

theorem redL_mul (c : Coef l) {x y : Qbar l} (hx : x ∈ c.O) (hy : y ∈ c.O) :
    redL c (x * y) = redL c x * redL c y := by
  rw [redL_of_mem c hx, redL_of_mem c hy, redL_of_mem c (c.O.mul_mem hx hy), ← map_mul]; rfl

theorem redL_zero (c : Coef l) : redL c 0 = 0 := by
  rw [redL_of_mem c c.O.zero_mem]; exact map_zero _

theorem redL_one (c : Coef l) : redL c 1 = 1 := by
  rw [redL_of_mem c c.O.one_mem]; exact map_one _

theorem redL_eq_zero_iff (c : Coef l) {x : Qbar l} (h : x ∈ c.O) :
    redL c x = 0 ↔ ∃ o ∈ c.O, x = (l : Qbar l) * o := by
  rw [redL_of_mem c h, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨o, ho⟩
    refine ⟨o, o.2, ?_⟩
    have : ((o * ((l : ℕ) : c.O) : c.O) : Qbar l) = x := congrArg Subtype.val ho
    rw [← this]; push_cast; ring
  · rintro ⟨o, ho, rfl⟩
    refine ⟨⟨o, ho⟩, Subtype.ext ?_⟩
    push_cast; ring

def ResPlane (c : Coef l) : Type := Fin 2 → ResL c

instance (c : Coef l) : AddCommGroup (ResPlane c) := inferInstanceAs (AddCommGroup (Fin 2 → ResL c))
instance (c : Coef l) : TopologicalSpace (ResPlane c) := ⊥
instance (c : Coef l) : DiscreteTopology (ResPlane c) := ⟨rfl⟩

theorem resL_natCast_l (c : Coef l) : ((l : ℕ) : ResL c) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : c.O)})), Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

theorem resPlane_smul_eq_zero (c : Coef l) (m : ResPlane c) : (l ^ 1) • m = 0 := by
  funext i
  show (l ^ 1) • (m i : ResL c) = 0
  rw [nsmul_eq_mul, pow_one, resL_natCast_l, zero_mul]

instance (c : Coef l) : Module (ZMod (l ^ 1)) (ResPlane c) := AddCommGroup.zmodModule (resPlane_smul_eq_zero c)

instance (c : Coef l) : Finite (ResPlane c) := by
  have : CharZero c.O := charZero_of_injective_algebraMap (UpperTheory.V.Base.dvrFacts l c.O).1
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have := (UpperTheory.V.X.So.levFacts l c.O ((l : ℕ) : c.O) hl0 (ResL c) ⟨LinearEquiv.refl _ _⟩).1
  exact inferInstanceAs (Finite (Fin 2 → ResL c))

def wRed (c : Coef l) (W : R2 Ω l) (s : G ℚ Ω) : Matrix (Fin 2) (Fin 2) (ResL c) := fun i j => redL c (mat W s i j)

def resMV (c : Coef l) (B : Matrix (Fin 2) (Fin 2) (ResL c)) : ResPlane c →+ ResPlane c where
  toFun m := B *ᵥ (m : Fin 2 → ResL c)
  map_zero' := Matrix.mulVec_zero B
  map_add' m m' := Matrix.mulVec_add B m m'

theorem wRed_one (c : Coef l) (W : R2 Ω l) : wRed c W 1 = 1 := by
  ext i j
  simp only [wRed, mat, map_one, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact redL_one c
  · exact redL_zero c

theorem wRed_mul (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) (s t : G ℚ Ω) :
    wRed c W (s * t) = wRed c W s * wRed c W t := by
  ext i j
  have e : mat W (s * t) i j = mat W s i 0 * mat W t 0 j + mat W s i 1 * mat W t 1 j := by
    simp only [mat, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [wRed, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e, redL_add c (c.O.mul_mem (hO _ _ _) (hO _ _ _)) (c.O.mul_mem (hO _ _ _) (hO _ _ _)),
    redL_mul c (hO _ _ _) (hO _ _ _), redL_mul c (hO _ _ _) (hO _ _ _)]

def resAct (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) :
    G ℚ Ω →* (ResPlane c →ₗ[ZMod (l ^ 1)] ResPlane c) where
  toFun s := AddMonoidHom.toZModLinearMap (l ^ 1) (resMV c (wRed c W s))
  map_one' := by
    refine LinearMap.ext fun m => ?_
    show wRed c W 1 *ᵥ (m : Fin 2 → ResL c) = m
    rw [wRed_one]; exact Matrix.one_mulVec _
  map_mul' s t := by
    refine LinearMap.ext fun m => ?_
    show wRed c W (s * t) *ᵥ (m : Fin 2 → ResL c) = wRed c W s *ᵥ (wRed c W t *ᵥ (m : Fin 2 → ResL c))
    rw [wRed_mul c W hO]; exact (Matrix.mulVec_mulVec _ _ _).symm

theorem resAct_apply (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) (s : G ℚ Ω) (m : ResPlane c) :
    resAct c W hO s m = (wRed c W s *ᵥ (m : Fin 2 → ResL c) : Fin 2 → ResL c) := rfl

theorem resAct_eq_one (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) {a : G ℚ Ω} (ha : W a = 1) :
    resAct c W hO a = 1 := by
  refine LinearMap.ext fun m => ?_
  show wRed c W a *ᵥ (m : Fin 2 → ResL c) = m
  have : wRed c W a = wRed c W 1 := by unfold wRed mat; rw [ha, map_one]
  rw [this, wRed_one]; exact Matrix.one_mulVec _

def resRep (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) :
    Representation (ZMod (l ^ 1)) (GS Ω (S : Set Pl)) (ResPlane c) :=
  QuotientGroup.lift (NS Ω (S : Set Pl)) (resAct c W hO) fun a ha =>
    resAct_eq_one c W hO (hN a ((QuotientGroup.eq_one_iff a).2 ha))

theorem resRep_toGS (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) (s : G ℚ Ω) :
    resRep c W hO S hN (toGS Ω (S : Set Pl) s) = resAct c W hO s := rfl

def descS (S : Finset Pl) {X : Type} (f : G ℚ Ω → X) : GS Ω (S : Set Pl) → X := fun g => f g.out

def resCoc (c : Coef l) (W : R2 Ω l) (z : G ℚ Ω → Fin 2 → Qbar l) (y : Fin 2 → Qbar l) : G ℚ Ω → ResPlane c :=
  fun s i => redL c ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i)

theorem resCoc_mul_ker (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) (y : Fin 2 → Qbar l)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) (s a : G ℚ Ω)
    (ha : a ∈ (toGS Ω (S : Set Pl)).ker) : resCoc c W z y (s * a) = resCoc c W z y s := by
  obtain ⟨-, h2, -, h4, -, -⟩ := hz
  funext i
  have hWa : mat W (s * a) = mat W s := by simp only [mat, map_mul, hN a ha, mul_one]
  have hza : (mat W s *ᵥ z a) i ∈ c.O := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.add_mem (c.O.mul_mem (hO _ _ _) (h4 a ha 0)) (c.O.mul_mem (hO _ _ _) (h4 a ha 1))
  have hd : z (s * a) i - z s i ∈ c.O := by
    have := c.O.add_mem (h2 s a i) hza
    simpa using this
  have e : (l : Qbar l) * z (s * a) i - (mat W (s * a) *ᵥ y - y) i =
      ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) + (l : Qbar l) * (z (s * a) i - z s i) := by
    rw [hWa]; ring
  show redL c _ = redL c _
  rw [e, redL_add c (hzy s i) (c.O.mul_mem (c.O.natCast_mem l) hd), (redL_eq_zero_iff c (c.O.mul_mem (c.O.natCast_mem l) hd)).2 ⟨_, hd, rfl⟩, add_zero]

theorem descS_resCoc_toGS (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) (y : Fin 2 → Qbar l)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) (s : G ℚ Ω) :
    descS S (resCoc c W z y) (toGS Ω (S : Set Pl) s) = resCoc c W z y s := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (NS Ω (S : Set Pl)) s
  show resCoc c W z y ((toGS Ω (S : Set Pl) s).out) = _
  have e : (toGS Ω (S : Set Pl) s).out = s * h := hh
  rw [e]
  exact resCoc_mul_ker c W S A hO hN hz y hzy s h ((QuotientGroup.eq_one_iff (h : G ℚ Ω)).2 h.2)

end GlobalTheory.Ord2

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.character_pow_pred_eq_one_of_killsPrimeRoots : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (C : Type) [Monoid C] (χ : G ℚ Ω →* C) (s : G ℚ Ω), KillsMu l χ → χ s ^ (l - 1) = 1 := by
  first | exact @GlobalTheory.KillsMuOrd.charPow_sub_one_eq_one | exact GlobalTheory.KillsMuOrd.charPow_sub_one_eq_one | (intros; apply GlobalTheory.KillsMuOrd.charPow_sub_one_eq_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

theorem _root_.GlobalTheory.T.hasWeight_neg_of_cyclotomic_pow_on_inertia : ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ), Continuous (fun σ => (κ σ : Qbar l)) → ∀ (e m : ℕ), 1 ≤ m → (∀ σ ∈ Loc.Iq l, (κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ)) ^ m = 1) → Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
  first | exact @GlobalTheory.hasWeight_neg_of_pow_cyc_inertia | exact GlobalTheory.hasWeight_neg_of_pow_cyc_inertia | (intros; apply GlobalTheory.hasWeight_neg_of_pow_cyc_inertia <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.LimCoc

theorem norm_l_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    rw [map_natCast]
  rw [h]
  have := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [this, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem ultra3 {K : Type*} [NormedField K] [IsUltrametricDist K] (a b c e : K) (ε : ℝ)
    (ha : ‖a‖ ≤ ε) (hb : ‖b‖ ≤ ε) (hc : ‖c‖ ≤ ε) (he : ‖e‖ ≤ ε) :
    ‖a + b - c - e‖ ≤ ε := by
  have hsub : ∀ u v : K, ‖u‖ ≤ ε → ‖v‖ ≤ ε → ‖u - v‖ ≤ ε := fun u v hu hv => by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu (by rwa [norm_neg]))
  exact hsub _ _ (hsub _ _ ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)) hc) he

theorem mulVec_small {K : Type*} [NormedField K] [IsUltrametricDist K]
    (A : Matrix (Fin 2) (Fin 2) K) (w : Fin 2 → K) (ε : ℝ) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (hw : ∀ j, ‖w j‖ ≤ ε) (i : Fin 2) : ‖(A *ᵥ w) i‖ ≤ ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hw 0)
  have key : ∀ j, ‖A i j * w j‖ ≤ ε := fun j => by
    rw [norm_mul]
    calc ‖A i j‖ * ‖w j‖ ≤ 1 * ε := mul_le_mul (hA i j) (hw j) (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (key 0) (key 1))

theorem limit_cocycle : ∀ (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] (M : Γ → Matrix (Fin 2) (Fin 2) (Qbar l)) (z : ℕ → Γ → Fin 2 → Qbar l) (y : Γ → Fin 2 → Qbar l), (∀ s i j, ‖M s i j‖ ≤ 1) → (∀ r s i, ‖z r s i‖ ≤ 1) → (∀ r s t i, ‖z r (s * t) i - (z r s + M s *ᵥ z r t) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r s i, ‖y s i - z r s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ s t, y (s * t) = y s + M s *ᵥ y t := by
  intro l _ Γ _ M z y hM _ hz hy s t
  funext i
  rw [← sub_eq_zero, ← norm_eq_zero]
  have hbound : ∀ r : ℕ, ‖y (s * t) i - (y s + M s *ᵥ y t) i‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ r := by
    intro r
    rw [← norm_pow]
    have hdecomp : y (s * t) i - (y s + M s *ᵥ y t) i =
        (y (s * t) i - z r (s * t) i) + (z r (s * t) i - (z r s + M s *ᵥ z r t) i)
          - (y s i - z r s i) - (M s *ᵥ (y t - z r t)) i := by
      simp only [Pi.add_apply, Matrix.mulVec_sub, Pi.sub_apply]
      ring
    rw [hdecomp]
    exact ultra3 _ _ _ _ _ (hy r (s * t) i) (hz r s t i) (hy r s i)
      (mulVec_small (M s) (y t - z r t) _ (hM s) (fun j => by simpa using hy r t j) i)
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one l)
  exact le_antisymm (ge_of_tendsto' hlim hbound) (norm_nonneg _)

end GlobalTheory.LimCoc
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.PowCong

variable {l : ℕ} [Fact l.Prime]

theorem norm_intCast_eq (k : ℤ) : ‖(k : Qbar l)‖ = ‖(k : ℚ_[l])‖ := by
  rw [show (k : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (k : ℚ_[l]) from (map_intCast _ k).symm]
  exact PadicAlgCl.norm_extends l _

theorem norm_natCast_eq (n : ℕ) : ‖(n : Qbar l)‖ = ‖(n : ℚ_[l])‖ := by
  have := norm_intCast_eq (l := l) (n : ℤ)
  simpa using this

theorem norm_l_pow (r : ℕ) : ‖((l : ℕ) : Qbar l) ^ r‖ = (l : ℝ) ^ (-(r : ℤ)) := by
  rw [norm_pow, norm_natCast_eq, Padic.norm_p, zpow_neg, zpow_natCast, inv_pow]

theorem norm_intCast_le_of_dvd (r : ℕ) (k : ℤ) (h : ((l : ℤ) ^ r) ∣ k) : ‖(k : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  rw [norm_intCast_eq, norm_l_pow]
  exact (Padic.norm_int_le_pow_iff_dvd k r).mpr h

theorem norm_natCast_eq_one {n : ℕ} (h : ¬ l ∣ n) : ‖(n : Qbar l)‖ = 1 := by
  rw [norm_natCast_eq, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h

theorem key (r e a b : ℕ) (ha : ¬ l ∣ a) (hb : b = a % l ^ r) (hb' : 1 ≤ r → ¬ l ∣ b) :
    ‖((a : Qbar l) ^ e)⁻¹ - ((b : Qbar l) ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ ∧
      ‖(a : Qbar l) ^ e - (b : Qbar l) ^ e‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have hcong : ((l : ℤ) ^ r) ∣ (((a ^ e : ℕ) : ℤ) - ((b ^ e : ℕ) : ℤ)) := by
    have h1 := (Nat.mod_modEq a (l ^ r)).pow e
    have h2 := (Nat.modEq_iff_dvd.mp h1)
    rw [hb]
    push_cast at h2 ⊢
    exact h2
  have hsub : ‖(a : Qbar l) ^ e - (b : Qbar l) ^ e‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
    have := norm_intCast_le_of_dvd (l := l) r _ hcong
    push_cast at this
    exact this
  refine ⟨?_, hsub⟩
  have hna : ‖(a : Qbar l)‖ = 1 := norm_natCast_eq_one ha
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hb0 : b = 0 := by rw [hb, pow_zero, Nat.mod_one]
    subst hb0
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; simp
    · rw [Nat.cast_zero, zero_pow he.ne', inv_zero, sub_zero, norm_inv, norm_pow, hna]
      simp
  · have hnb : ‖(b : Qbar l)‖ = 1 := norm_natCast_eq_one (hb' hr)
    have ha0 : ((a : Qbar l) ^ e) ≠ 0 := by
      intro h; have := congrArg norm h; rw [norm_pow, hna] at this; simp at this
    have hb0 : ((b : Qbar l) ^ e) ≠ 0 := by
      intro h; have := congrArg norm h; rw [norm_pow, hnb] at this; simp at this
    rw [inv_sub_inv ha0 hb0, norm_div, norm_mul, norm_pow, norm_pow, hna, hnb, one_pow, mul_one, div_one,
      norm_sub_rev]
    exact hsub

theorem powCong : ∀ (l : ℕ) [Fact l.Prime] (e r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ), ‖(((x : ZMod (l ^ (r + 1))).val : Qbar l) ^ e)⁻¹ - (((((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : Qbar l) ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ ∧ ‖((x : ZMod (l ^ (r + 1))).val : Qbar l) ^ e - ((((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : Qbar l) ^ e‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  intro l hl e r x
  have hp : l.Prime := hl.out
  haveI : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have notdvd : ∀ {k : ℕ}, 1 ≤ k → (u : (ZMod (l ^ k))ˣ) → ¬ l ∣ (u : ZMod (l ^ k)).val := by
    intro k hk u hd
    have hc := ZMod.val_coe_unit_coprime u
    have : l ∣ Nat.gcd (u : ZMod (l ^ k)).val (l ^ k) := Nat.dvd_gcd hd (dvd_pow_self l (by omega))
    rw [hc] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  refine key (l := l) r e _ _ (notdvd (by omega) x) ?_ (fun hr => notdvd hr _)
  rw [Units.coe_map]
  simp only [MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, ZMod.castHom_apply]
  rw [ZMod.cast_eq_val, ZMod.val_natCast]

end GlobalTheory.PowCong
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_annihilatorDepth_of_not_coboundary : ∀ (l : ℕ) [Fact l.Prime] {Γ : Type} (H : Set Γ) (k a : Γ → Qbar l), (∃ s ∈ H, k s ≠ 1) → (¬ ∃ X : Qbar l, ∀ s ∈ H, a s = k s * X - X) → ∃ r : ℕ, ∀ (n : ℕ) (x y : Qbar l), ‖x‖ ≤ 1 → (∀ s ∈ H, ‖x * a s - (k s * y - y)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) → ‖x‖ ≤ ‖((l : ℕ) : Qbar l) ^ (n - r)‖ := by
  first | exact @GlobalTheory.LocCharAnn.exists_depth_of_not_coboundary | exact GlobalTheory.LocCharAnn.exists_depth_of_not_coboundary | (intros; apply GlobalTheory.LocCharAnn.exists_depth_of_not_coboundary <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_dotProduct_eq_of_primePow_approx_qbarL : ∀ (l : ℕ) [Fact l.Prime] (X : Type) (m : ℕ) (M : X → Fin m → Qbar l) (z : X → Qbar l), (∀ n : ℕ, ∃ y : Fin m → Qbar l, ∀ x, ‖z x - M x ⬝ᵥ y‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) → ∃ y : Fin m → Qbar l, ∀ x, z x = M x ⬝ᵥ y := by
  first | exact @GlobalTheory.exists_dotProduct_eq_of_approx_prime_pow | exact GlobalTheory.exists_dotProduct_eq_of_approx_prime_pow | (intros; apply GlobalTheory.exists_dotProduct_eq_of_approx_prime_pow <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.padicHom_small_on_deep_congruence_subgroups : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]), Continuous r → Continuous lam → r.ker ≤ lam.ker → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g : Γ, (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖) → ‖(lam g).toAdd‖ ≤ ε := by
  first | exact @GlobalTheory.lam_small_of_deep_congruence | exact GlobalTheory.lam_small_of_deep_congruence | (intros; apply GlobalTheory.lam_small_of_deep_congruence <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_upperTriangular_conj_integral_compact : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (E : IntermediateField ℚ_[l] (Qbar l)) (r : Γ →* GL (Fin 2) (Qbar l)), FiniteDimensional ℚ_[l] E → Continuous r → (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ E) → ∃ B : GL (Fin 2) (Qbar l), (B : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0 ∧ ∀ g i j, ((B * r g * B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ E ∧ ‖((B * r g * B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) i j‖ ≤ 1 := by
  first | exact @GlobalTheory.StableLatticeTriangular.exists_upperTriangular_conj_integral | exact GlobalTheory.StableLatticeTriangular.exists_upperTriangular_conj_integral | (intros; apply GlobalTheory.StableLatticeTriangular.exists_upperTriangular_conj_integral <;> assumption)
end

end

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

theorem _root_.GlobalTheory.T.isCocycle_of_padic_limit_of_approx_cocycles : ∀ (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] (M : Γ → Matrix (Fin 2) (Fin 2) (Qbar l)) (z : ℕ → Γ → Fin 2 → Qbar l) (y : Γ → Fin 2 → Qbar l), (∀ s i j, ‖M s i j‖ ≤ 1) → (∀ r s i, ‖z r s i‖ ≤ 1) → (∀ r s t i, ‖z r (s * t) i - (z r s + M s *ᵥ z r t) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r s i, ‖y s i - z r s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ s t, y (s * t) = y s + M s *ᵥ y t := by
  first | exact @GlobalTheory.LimCoc.limit_cocycle | exact GlobalTheory.LimCoc.limit_cocycle | (intros; apply GlobalTheory.LimCoc.limit_cocycle <;> assumption)

end
end
