module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle233
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle257
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle258
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilInvariantJumpDescendsFinExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
public import Mathlib.RingTheory.Flat.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle254
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle253
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle061
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle004
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PHomogeneousDifferenceLinear
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory

theorem units_map_toZModPow_eq_one_iff (l : ℕ) [Fact l.Prime] (m : ℕ) (u : ℤ_[l]ˣ) :
    Units.map (PadicInt.toZModPow (p := l) m).toMonoidHom u = 1 ↔
      ‖(u : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ m := by
  rw [PadicInt.norm_p, inv_pow, ← zpow_natCast, ← zpow_neg,
    PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    map_one, sub_eq_zero, Units.ext_iff]
  simp

theorem congruence_chain_of_character {G : Type*} [Group G] (l : ℕ) [Fact l.Prime]
    (η : G →* ℤ_[l]ˣ) (γ : G) (k : ℕ) (hk : 2 ≤ k)
    (hγ : ‖(η γ : ℤ_[l]) - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k) :
    ∃ H : ℕ → Subgroup G,
      (∀ n g, g ∈ H n ↔ ‖(η g : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n)) ∧
      (∀ n, (H n).Normal) ∧ (∀ n, (H n).index ≠ 0) ∧ (∀ n, (H n).index ≤ l ^ (k + n)) ∧
      (∀ n, γ ^ l ^ n ∈ H n) ∧
      ∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1) := by
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  let φ : ∀ n : ℕ, G →* (ZMod (l ^ (k + n)))ˣ := fun n =>
    (Units.map (PadicInt.toZModPow (p := l) (k + n)).toMonoidHom).comp η
  have hmem : ∀ n g, g ∈ (φ n).ker ↔
      ‖(η g : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) := fun n g => by
    rw [MonoidHom.mem_ker]
    exact units_map_toZModPow_eq_one_iff l (k + n) (η g)
  have hlte : ∀ n, ‖(η (γ ^ l ^ n) : ℤ_[l]) - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) := fun n => by
    rw [map_pow, Units.val_pow_eq_pow_val]
    exact GlobalTheory.T.norm_pow_prime_pow_sub_one_of_norm_sub_one l _ k hk hγ n
  refine ⟨fun n => (φ n).ker, hmem, fun n => inferInstance, fun n => ?_, fun n => ?_,
    fun n => ?_, fun n h hh => ?_⟩
  · have : NeZero (l ^ (k + n)) := ⟨pow_ne_zero _ hl⟩
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  · have : NeZero (l ^ (k + n)) := ⟨pow_ne_zero _ hl⟩
    rw [Subgroup.index_ker]
    calc Nat.card (φ n).range ≤ Nat.card (ZMod (l ^ (k + n))) :=
          Nat.card_le_card_of_injective (fun x => ((x : (ZMod (l ^ (k + n)))ˣ) : ZMod (l ^ (k + n))))
            (fun x y hxy => Subtype.ext (Units.ext hxy))
      _ = l ^ (k + n) := Nat.card_zmod _
  · exact (hmem n _).2 (hlte n).le
  · obtain ⟨i, hi⟩ := GlobalTheory.T.padicInt_exists_pow_sub_norm_le_of_exact_level' l (η (γ ^ l ^ n) : ℤ_[l]) (η h : ℤ_[l]) (k + n) (by omega)
      (hlte n) ((hmem n h).1 hh)
    refine ⟨i, (hmem (n + 1) _).2 ?_⟩
    set w : ℤ_[l]ˣ := η ((γ ^ l ^ n) ^ i) with hw
    have hwv : (w : ℤ_[l]) = (η (γ ^ l ^ n) : ℤ_[l]) ^ i := by
      rw [hw, map_pow η (γ ^ l ^ n) i, Units.val_pow_eq_pow_val]
    have key : ((η (((γ ^ l ^ n) ^ i)⁻¹ * h) : ℤ_[l]ˣ) : ℤ_[l]) - 1 =
        -((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * ((w : ℤ_[l]) - (η h : ℤ_[l])) := by
      rw [map_mul, map_inv, ← hw, Units.val_mul, mul_sub, neg_mul, neg_mul, Units.inv_mul]
      ring
    rw [key, norm_mul, norm_neg, hwv]
    calc _ ≤ 1 * ‖(η (γ ^ l ^ n) : ℤ_[l]) ^ i - (η h : ℤ_[l])‖ :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hi

theorem galois_congruence_chain : ∀ (l : ℕ) [Fact l.Prime] (η : GQ l →* ℤ_[l]ˣ) (γ : GQ l) (k : ℕ), 2 ≤ k → ‖(η γ : ℤ_[l]) - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k → ∃ H : ℕ → Subgroup (GQ l), (∀ n g, g ∈ H n ↔ ‖(η g : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n)) ∧ (∀ n, (H n).Normal) ∧ (∀ n, (H n).index ≠ 0) ∧ (∀ n, (H n).index ≤ l ^ (k + n)) ∧ (∀ n, γ ^ l ^ n ∈ H n) ∧ ∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1) :=
  fun l _ η γ k hk hγ => congruence_chain_of_character l η γ k hk hγ

end GlobalTheory
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

theorem _root_.GlobalTheory.T.potentiallyCrystalline_module_eq_crystalline_restriction : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (pc P h hN hF hS).Dpcris ρ = Dcris (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) ∧ ((pc P h hN hF hS).IsPotCrys ρ ↔ IsCrys (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) := by
  first | exact @GlobalTheory.PcRes.main | exact GlobalTheory.PcRes.main | (intros; apply GlobalTheory.PcRes.main <;> assumption)
end

section

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.PassPolyPow

theorem aeval_mul_apply {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (p q : L[X]) (x : M) : Polynomial.aeval f (p * q) x = Polynomial.aeval f p (Polynomial.aeval f q x) := by
  rw [map_mul, Module.End.mul_apply]

theorem eigen_of_pow_of_separable {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (c : L) (m : ℕ) (r : L[X]) (hr : r.Separable) (x : M)
    (h1 : Polynomial.aeval f ((X - C c) ^ m) x = 0) (h2 : Polynomial.aeval f r x = 0) :
    Polynomial.aeval f (X - C c) x = 0 := by
  obtain ⟨t, hrt, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr.ne_zero c
  have hle := Polynomial.rootMultiplicity_le_one_of_separable hr c
  have hcop : IsCoprime ((X - C c) ^ m) t :=
    ((Polynomial.irreducible_X_sub_C c).coprime_iff_not_dvd.2 hnd).pow_left
  obtain ⟨A, B', hAB⟩ := hcop
  have hs : ∃ s : L[X], (X - C c) * t = s * r := by
    interval_cases hj : r.rootMultiplicity c
    · exact ⟨X - C c, by rw [hrt]; ring⟩
    · exact ⟨1, by rw [hrt]; ring⟩
  obtain ⟨s, hs⟩ := hs
  have : (X - C c) = (A * (X - C c)) * (X - C c) ^ m + (B' * s) * r := by
    rw [mul_assoc (B') s r, ← hs]
    linear_combination (-(X - C c)) * hAB
  rw [this, map_add (f := _), LinearMap.add_apply, aeval_mul_apply, h1, map_zero, aeval_mul_apply, h2, map_zero, add_zero]

theorem mem_iSup_eigen_pow {L M ι : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (D : Submodule L M) (hD : ∀ x ∈ D, f x ∈ D) (r : L[X]) (hr : r.Separable)
    (hrD : ∀ x ∈ D, Polynomial.aeval f r x = 0) (c : ι → L) (m : ℕ) (s : Finset ι) :
    (∀ a ∈ s, ∀ b ∈ s, c a = c b → a = b) → ∀ d ∈ D,
      Polynomial.aeval f ((∏ a ∈ s, (X - C (c a))) ^ m) d = 0 →
      d ∈ ⨆ a ∈ s, (D ⊓ LinearMap.ker (f - c a • LinearMap.id)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ d _ h
    simp at h
    simp [h]
  | insert a t hat ih =>
    intro hinj d hd h
    rw [Finset.prod_insert hat, mul_pow] at h
    have hcop : IsCoprime ((X - C (c a)) ^ m) ((∏ b ∈ t, (X - C (c b))) ^ m) := by
      refine IsCoprime.pow (IsCoprime.prod_right fun b hb => ?_)
      refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub (IsUnit.mk0 _ (sub_ne_zero.2 fun e => hat ?_))
      rw [hinj a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb) e]
      exact hb
    obtain ⟨u, v, huv⟩ := hcop
    set Q := (∏ b ∈ t, (X - C (c b))) ^ m with hQ
    have hdec : d = Polynomial.aeval f (u * (X - C (c a)) ^ m) d + Polynomial.aeval f (v * Q) d := by
      rw [← LinearMap.add_apply, ← map_add (f := _), huv, map_one, Module.End.one_apply]
    rw [Finset.iSup_insert, hdec, add_comm]
    refine Submodule.add_mem_sup ?_ ?_
    · have hmem := GlobalTheory.PassPoly.aeval_mem_of_stable f D hD (v * Q) d hd
      refine ⟨hmem, ?_⟩
      have h1 : Polynomial.aeval f ((X - C (c a)) ^ m) (Polynomial.aeval f (v * Q) d) = 0 := by
        rw [← aeval_mul_apply, show (X - C (c a)) ^ m * (v * Q) = v * ((X - C (c a)) ^ m * Q) by ring,
          aeval_mul_apply, h, map_zero]
      have := eigen_of_pow_of_separable f (c a) m r hr _ h1 (hrD _ hmem)
      simpa [Module.algebraMap_end_apply] using this
    · refine ih (fun x hx y hy => hinj x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)) _
        (GlobalTheory.PassPoly.aeval_mem_of_stable f D hD _ d hd) ?_
      rw [← aeval_mul_apply, show Q * (u * (X - C (c a)) ^ m) = u * ((X - C (c a)) ^ m * Q) by ring,
        aeval_mul_apply, h, map_zero]

section
variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem actVB_pow (g : G) (n : ℕ) (x : V ⊗[Qp] B) :
    (actVB PC.PD ρ g ^ n) x = actVB PC.PD ρ (g ^ n) x := by
  induction n generalizing x with
  | zero => simp [GlobalTheory.PassPoly.actVB_one']
  | succ n ih => rw [pow_succ, Module.End.mul_apply, ih, pow_succ, GlobalTheory.PassPoly.actVB_mul']

theorem aeval_index_kill (g : G) : ∀ x ∈ PC.Dpcris ρ,
    Polynomial.aeval (actVB PC.PD ρ g) (X ^ PC.H.index - C (1 : LL)) x = 0 := by
  intro x hx
  haveI := PC.normal
  have hg : g ^ PC.H.index ∈ PC.H := Subgroup.pow_index_mem PC.H g
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply]
  rw [actVB_pow, (GlobalTheory.PassPoly.mem_Dpcris_iff PC ρ x).1 hx _ hg, sub_self]

theorem separable_index [CharZero LL] : (X ^ PC.H.index - C (1 : LL)).Separable := by
  haveI := PC.finiteIndex
  exact Polynomial.separable_X_pow_sub_C 1 (Nat.cast_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero) one_ne_zero

theorem inertiaThrough_of_poly_pow [CharZero LL] (Sig : Finset (PC.Iner →* LLˣ))
    (h1 : ∀ a ∈ Sig, ∀ g : PC.Iner, (g : G) ∈ PC.H → a g = 1)
    (h2 : ∀ a ∈ Sig, Nat.Coprime (orderOf a) PC.PD.p)
    (h3 : ∀ (g : PC.Iner), ∃ m : ℕ, ∀ d ∈ PC.Dpcris ρ, (Polynomial.aeval (actVB PC.PD ρ (g : G))
      ((∏ a ∈ Sig, (X - C ((a g : LLˣ) : LL))) ^ m)) d = 0)
    (h4 : ∃ γ : PC.Iner, (∀ a ∈ Sig, ∀ b ∈ Sig, a γ = b γ → a = b) ∧
      ∀ g : PC.Iner, ∃ (n : ℕ) (u : PC.Iner), (∀ a ∈ Sig, a u = 1) ∧ g = γ ^ n * u) :
    PC.InertiaThrough ρ Sig := by

  have htriv : ∀ u : PC.Iner, (∀ a ∈ Sig, a u = 1) → ∀ x ∈ PC.Dpcris ρ,
      actVB PC.PD ρ (u : G) x = x := by
    intro u hu x hx
    obtain ⟨m, hm⟩ := h3 u
    have hprod : (∏ a ∈ Sig, (X - C ((a u : LLˣ) : LL))) ^ m = (X - C (1 : LL)) ^ (Sig.card * m) := by
      rw [Finset.prod_congr rfl (fun a ha => by rw [hu a ha, Units.val_one]), Finset.prod_const, pow_mul]
    have hk := hm x hx
    rw [hprod] at hk
    have := eigen_of_pow_of_separable _ 1 _ _ (separable_index PC) x hk (aeval_index_kill PC ρ _ x hx)
    simpa [Module.algebraMap_end_apply, sub_eq_zero] using this
  refine ⟨h1, h2, le_antisymm ?_ ?_⟩
  · obtain ⟨γ, hsep, hgen⟩ := h4
    intro d hd
    obtain ⟨m, hm⟩ := h3 γ
    have := mem_iSup_eigen_pow (actVB PC.PD ρ (γ : G)) (PC.Dpcris ρ) (GlobalTheory.PassPoly.Dpcris_stable PC ρ γ)
      _ (separable_index PC) (aeval_index_kill PC ρ _)
      (fun a : PC.Iner →* LLˣ => ((a γ : LLˣ) : LL)) m Sig
      (fun a ha b hb e => hsep a ha b hb (Units.ext e)) d hd (hm d hd)
    refine (iSup₂_mono (fun a ha => ?_) : _ ≤ ⨆ a ∈ Sig, PC.Eig ρ PC.Iner a) this
    rintro x ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    have hγ : actVB PC.PD ρ (γ : G) x = ((a γ : LLˣ) : LL) • x := by
      simpa [sub_eq_zero] using hx'
    have hn : ∀ n : ℕ, actVB PC.PD ρ ((γ : G) ^ n) x = ((a γ : LLˣ) : LL) ^ n • x := by
      intro n
      induction n with
      | zero => simp [GlobalTheory.PassPoly.actVB_one']
      | succ n ih => rw [pow_succ, GlobalTheory.PassPoly.actVB_mul', hγ, map_smul, ih, smul_smul, pow_succ, mul_comm]
    simp only [Submodule.coe_iInf, Set.mem_iInter, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    intro g
    obtain ⟨n, u, hu, rfl⟩ := hgen g
    rw [map_mul, hu a ha, mul_one, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, GlobalTheory.PassPoly.actVB_mul',
      htriv u hu x hx, hn, Units.val_pow_eq_pow_val]
  · exact iSup₂_le fun a _ => inf_le_left

end

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)), (∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK K)) ∈ (pc P h hN hF hS).H → a g = 1) → (∀ a ∈ Sig, Nat.Coprime (orderOf a) l) → (∀ (g : (pc P h hN hF hS).Iner), ∃ m : ℕ, ∀ d ∈ (pc P h hN hF hS).Dpcris ρ, (Polynomial.aeval (actVB (P.PD K) ρ (g : ↥(GK K))) ((∏ a ∈ Sig, (X - C ((a g : (↥LL.1)ˣ) : ↥LL.1))) ^ m)) d = 0) → (∃ γ : (pc P h hN hF hS).Iner, (∀ a ∈ Sig, ∀ b ∈ Sig, a γ = b γ → a = b) ∧ ∀ g : (pc P h hN hF hS).Iner, ∃ (n : ℕ) (u : (pc P h hN hF hS).Iner), (∀ a ∈ Sig, a u = 1) ∧ g = γ ^ n * u) → (pc P h hN hF hS).InertiaThrough ρ Sig := by
  intro l _ P K K' LL h hN hF hS V _ _ _ _ ρ Sig h1 h2 h3 h4
  haveI : CharZero ↥LL.1 := charZero_of_injective_algebraMap (algebraMap ℚ_[l] ↥LL.1).injective
  refine inertiaThrough_of_poly_pow (pc P h hN hF hS) ρ Sig h1 ?_ h3 h4
  have hp : (pc P h hN hF hS).PD.p = l := P.PD_p K
  rw [hp]
  exact h2

end GlobalTheory.PassPolyPow

end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem _root_.GlobalTheory.T.deRhamFil_invariant_jump_descends_finExt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K E : FinExt l), K.1 ≤ E.1 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) ℚ_[l]), (∀ g ∈ GK K, ∀ h ∈ GK K, M (g * h) = M g * M h) → ∀ (a : ℤ) (y : Fin d → P.R.BdR), (∀ g ∈ GK E, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (y i)) = y) → (∀ i, y i ∈ (P.PD K).Fil a) → ¬ (∀ i, y i ∈ (P.PD K).Fil (a + 1)) → ∃ z : Fin d → P.R.BdR, (∀ g ∈ GK K, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (z i)) = z) ∧ (∀ i, z i ∈ (P.PD K).Fil a) ∧ ¬ (∀ i, z i ∈ (P.PD K).Fil (a + 1)) := by
  first | exact @GlobalTheory.InvDescent.jump_descends | exact GlobalTheory.InvDescent.jump_descends | (intros; apply GlobalTheory.InvDescent.jump_descends <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

theorem _root_.GlobalTheory.T.frobeniusIntegrality_wittTilt_ainf : ∀ (l : ℕ) [Fact l.Prime] (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q (WCb l)) (S : Matrix p p (Ainf l)) (S' : Matrix q q (Ainf l)) (Y : Matrix p q (Ainf l)), Z.map (frobW l) = S.map (inclW l) * Z * S'.map (inclW l) + Y.map (inclW l) → ∀ a b, Z a b ∈ Set.range (inclW l) := by
  first | exact @GlobalTheory.FrobInt.frobenius_integrality | exact GlobalTheory.FrobInt.frobenius_integrality | (intros; apply GlobalTheory.FrobInt.frobenius_integrality <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

theorem _root_.GlobalTheory.T.isAlgClosed_tiltField_and_valuationRing : ∀ (l : ℕ) [Fact l.Prime], IsAlgClosed (Cb l) ∧ ValuationRing (OCb l) := by
  first | exact @GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing | exact GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing | (intros; apply GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing <;> assumption)
end

section

namespace GlobalTheory.UnramValue

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct IsLocalRing Polynomial

theorem exists_pow_card_eq {S : Type*} [CommRing S] [IsLocalRing S]
    [IsAdicComplete (maximalIdeal S) S] [Fintype (ResidueField S)] (x : S) :
    ∃ t : S, t ^ Fintype.card (ResidueField S) = t ∧ t - x ∈ maximalIdeal S := by
  have h1 : 1 < Fintype.card (ResidueField S) := Fintype.one_lt_card
  have hm : (X ^ Fintype.card (ResidueField S) - X : S[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  obtain ⟨t, ht, htx⟩ := (IsAdicComplete.henselianRing S (maximalIdeal S)).is_henselian _ hm x
    (by
      rw [← residue_eq_zero_iff]
      simp [FiniteField.pow_card])
    (by
      change IsUnit (residue S _)
      rw [derivative_sub, derivative_X_pow]
      simp)
  refine ⟨t, ?_, htx⟩
  simpa [sub_eq_zero] using ht

variable {l : ℕ} [Fact l.Prime]

theorem norm_natCast_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap', Padic.norm_p]

theorem integral_mem (L : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] L]
    (h : ∀ x ∈ L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k) (x : integralClosure ℤ_[l] L) :
    ((x : L) : Om l) ∈ MaximalUnramifiedExtension l := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : L) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  letI : IsLocalRing (integralClosure ℤ_[l] L) :=
    (GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt l L).toIsLocalRing
  have hmax : ∀ y : integralClosure ℤ_[l] L,
      y ∈ maximalIdeal (integralClosure ℤ_[l] L) ↔ ‖((y : L) : Om l)‖ < 1 := fun y => by
    rw [GlobalTheory.DiscEval.mem_maximalIdeal_iff_norm, GlobalTheory.DiscEval.intEmb_apply,
      GlobalTheory.DiscEval.fieldEmb_apply, PadicComplex.norm_extends]
  have hint : ∀ y : L, y ∈ integralClosure ℤ_[l] L ↔ ‖(y : Om l)‖ ≤ 1 := fun y => by
    rw [GlobalTheory.DiscEval.mem_integralClosure_iff_norm, GlobalTheory.DiscEval.fieldEmb_apply,
      PadicComplex.norm_extends]
  let N : Submodule ℤ_[l] (integralClosure ℤ_[l] L) :=
    { carrier := {y | ((y : L) : Om l) ∈ MaximalUnramifiedExtension l}
      add_mem' := fun ha hb => (MaximalUnramifiedExtension l).add_mem ha hb
      zero_mem' := (MaximalUnramifiedExtension l).zero_mem
      smul_mem' := fun c y hy => (MaximalUnramifiedExtension l).smul_mem (x := (c : ℚ_[l])) hy }
  have := GlobalTheory.DiscEval.isAdicComplete_integralClosure L
  have := GlobalTheory.DiscEval.finite_residueField_integralClosure L
  let _ := Fintype.ofFinite (ResidueField (integralClosure ℤ_[l] L))
  have hle : (⊤ : Submodule ℤ_[l] (integralClosure ℤ_[l] L)) ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal ℤ_[l])
      Module.Finite.fg_top (maximalIdeal_le_jacobson _) fun y _ => ?_
    obtain ⟨t, ht, hty⟩ := exists_pow_card_eq y
    have htN : t ∈ N := by
      change ((t : L) : Om l) ∈ MaximalUnramifiedExtension l
      by_cases h0 : ((t : L) : Om l) = 0
      · rw [h0]; exact zero_mem _
      have h1 : 1 < Fintype.card (ResidueField (integralClosure ℤ_[l] L)) := Fintype.one_lt_card
      refine IntermediateField.subset_adjoin _ _
        ⟨Fintype.card (ResidueField (integralClosure ℤ_[l] L)) - 1, by omega, ?_, ?_⟩
      · rintro ⟨c, hc⟩
        have h2 : (l : ResidueField (integralClosure ℤ_[l] L)) = 0 := by
          rw [← map_natCast (residue _), residue_eq_zero_iff, hmax]
          push_cast
          rw [norm_natCast_l]
          exact inv_lt_one_of_one_lt₀ hl1
        have h3 := congrArg (Nat.cast : ℕ → ResidueField (integralClosure ℤ_[l] L)) hc
        rw [Nat.cast_sub h1.le] at h3
        simp [h2] at h3
      · have h2 := congrArg (fun z : integralClosure ℤ_[l] L => ((z : L) : Om l)) ht
        push_cast at h2
        apply mul_right_cancel₀ h0
        rw [← pow_succ, Nat.sub_add_cancel h1.le, h2, one_mul]
    have hd : ((t - y : integralClosure ℤ_[l] L) : L) / l ∈ integralClosure ℤ_[l] L := by
      rw [hint]
      rw [hmax] at hty
      generalize ((t - y : integralClosure ℤ_[l] L) : L) = z at hty
      push_cast
      by_cases h0 : (z : Om l) = 0
      · simp [h0]
      obtain ⟨k, hk⟩ := h _ z.2 h0
      rw [hk, zpow_lt_one_iff_right₀ hl1] at hty
      rw [norm_div, hk, norm_natCast_l, div_inv_eq_mul, ← zpow_add_one₀ (by positivity)]
      exact zpow_le_one_of_nonpos₀ hl1.le (by omega)
    have he : y = t - (l : ℤ_[l]) • (⟨_, hd⟩ : integralClosure ℤ_[l] L) := by
      apply Subtype.ext
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      push_cast
      field_simp
      ring
    rw [he]
    refine sub_mem (Submodule.mem_sup_left htN) (Submodule.mem_sup_right
      (Submodule.smul_mem_smul ?_ Submodule.mem_top))
    exact PadicInt.irreducible_p.not_isUnit
  exact hle Submodule.mem_top

theorem le_Kur_of_norm : ∀ (l : ℕ) [Fact l.Prime] (M : FinExt l),
    (∀ x ∈ M.1, x ≠ 0 → ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k) → M.1 ≤ MaximalUnramifiedExtension l := by
  intro l _ M h x hx
  obtain ⟨L, hL⟩ := M
  obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := integralClosure ℤ_[l] L) (⟨x, hx⟩ : L)
  have h1 : x = ((a : L) : Om l) / ((b : L) : Om l) := (congrArg Subtype.val hab).symm
  rw [h1]
  exact div_mem (integral_mem L h a) (integral_mem L h b)

end GlobalTheory.UnramValue
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.flat_over_product_power_series_ring : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (n : ℕ) [NeZero n] (E : Type) [CommRing E] [Algebra (LetA O n) E] (p : ℕ), IsUnit (algebraMap (LetA O n) E letπ) → IsAdicComplete (Ideal.span {(p : E)}) E → (∀ (x : E) (k : ℕ), ∃ (a : LetA O n) (m : ℕ), x * algebraMap (LetA O n) E (letπ ^ m) - algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k}) → (∀ (a : LetA O n) (k : ℕ), algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} → ∃ b : LetA O n, a = (p : LetA O n) ^ k * b) → Module.Flat (LetA O n) E := by
  first | exact @GlobalTheory.FlatLocCompl.flat_letA | exact GlobalTheory.FlatLocCompl.flat_letA | (intros; apply GlobalTheory.FlatLocCompl.flat_letA <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.admDecomp_iff_decomp : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π ↔ ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
  first | exact @GlobalTheory.DecompForms.main | exact GlobalTheory.DecompForms.main | (intros; apply GlobalTheory.DecompForms.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.BridgeTie

theorem localCoefficientCompatibility : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i :=
  fun D i => coefficient_compatibility_of D i (fun w hw => GlobalTheory.bridge_degW D.nbr i w hw)

end GlobalTheory.BridgeTie
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_int_sub_mul_eq_int_mul_of_homogeneous : ∀ (p h s m : ℕ), 2 ≤ p → s < h → 1 ≤ m → ∀ A B : ℝ → ℝ, ConcaveOn ℝ (Set.Ioc 0 1) A → ConcaveOn ℝ (Set.Ioc 0 1) B → ContinuousOn A (Set.Ioc 0 1) → ContinuousOn B (Set.Ioc 0 1) → (∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧ ∀ t ∈ Set.Icc r (r + δ), A t = A r + k * (t - r)) → (∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧ ∀ t ∈ Set.Icc r (r + δ), B t = B r + k * (t - r)) → (∀ r ∈ Set.Ioc (0 : ℝ) 1, (p : ℝ) ^ h * B (r / (p : ℝ) ^ h) = B r + s * r) → (∀ r ∈ Set.Ioc (0 : ℝ) (1 / p), A (p * r) - m * B (p * r) = p * (A r - m * B r)) → ∃ n : ℤ, ∀ r ∈ Set.Ioc (0 : ℝ) 1, A r - m * B r = n * r := by
  first | exact @GlobalTheory.PHomCalc.p_homogeneous_difference_linear | exact GlobalTheory.PHomCalc.p_homogeneous_difference_linear | (intros; apply GlobalTheory.PHomCalc.p_homogeneous_difference_linear <;> assumption)
end
