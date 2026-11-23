module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffineOpenAndIsPushout
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle012
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle296
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle093
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle030
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
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle017

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

open CategoryTheory.Limits ReciprocityTheory.ChartRestriction.G.DVR.FlatBC

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Gaga

theorem mem_closure_of_isPushout {R A B C : CommRingCat.{0}} {f : R ⟶ A} {g : R ⟶ B} {i : A ⟶ C}
    {j : B ⟶ C} (h : IsPushout f g i j) (c : C) :
    c ∈ AddSubmonoid.closure {x : C | ∃ (a : A) (b : B), x = i a * j b} := by
  letI : Algebra R A := f.hom.toAlgebra
  letI : Algebra R B := g.hom.toAlgebra
  letI : Algebra A C := i.hom.toAlgebra
  letI : Algebra B C := j.hom.toAlgebra
  letI : Algebra R C := (f ≫ i).hom.toAlgebra
  haveI : IsScalarTower R A C := .of_algebraMap_eq fun r => rfl
  haveI : IsScalarTower R B C := .of_algebraMap_eq fun r => congr($(h.w) r)
  haveI : Algebra.IsPushout R B A C := CommRingCat.isPushout_iff_isPushout.mp h.flip
  obtain ⟨t, rfl⟩ := (Algebra.IsPushout.equiv R B A C).surjective c
  induction t with
  | tmul b a =>
    rw [Algebra.IsPushout.equiv_tmul]
    exact AddSubmonoid.subset_closure ⟨a, b, mul_comm _ _⟩
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact add_mem hx hy

theorem appLE_surjective {X Z : Scheme.{0}} (d : X ⟶ Z) [IsClosedImmersion d] {O : Z.Opens}
    (hO : IsAffineOpen O) {D : X.Opens} (hD : D = d ⁻¹ᵁ O) (e : D ≤ d ⁻¹ᵁ O) :
    Function.Surjective (d.appLE O D e) := by
  subst hD
  rw [← Scheme.Hom.app_eq_appLE]
  exact d.app_surjective O hO

theorem mem_closure_inf {S Y : Scheme.{0}} [IsAffine S] (p : Y ⟶ S) [IsSeparated p] {V W : Y.Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (g : Γ(Y, V ⊓ W)) :
    g ∈ AddSubmonoid.closure {x : Γ(Y, V ⊓ W) | ∃ (a : Γ(Y, V)) (b : Γ(Y, W)),
      x = resG Y inf_le_left a * resG Y inf_le_right b} := by
  have H := IsPullback.of_hasPullback p p
  obtain ⟨hO, po⟩ := Conormal.isAffineOpen_and_isPushout H (U := ⊤) (T₀ := W) (W := V)
    (isAffineOpen_top _) hW hV le_top le_top
  have d1 : pullback.diagonal p ≫ pullback.fst p p = 𝟙 Y := pullback.diagonal_fst p
  have d2 : pullback.diagonal p ≫ pullback.snd p p = 𝟙 Y := pullback.diagonal_snd p
  have hD : V ⊓ W = pullback.diagonal p ⁻¹ᵁ (pullback.fst p p ⁻¹ᵁ V ⊓ pullback.snd p p ⁻¹ᵁ W) := by
    rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, d1, d2]
    simp
  obtain ⟨c, rfl⟩ := appLE_surjective (pullback.diagonal p) hO hD hD.le g
  have hc := mem_closure_of_isPushout po c
  induction hc using AddSubmonoid.closure_induction with
  | zero => simp
  | mem x hx =>
    obtain ⟨a, b, rfl⟩ := hx
    rw [map_mul]
    refine AddSubmonoid.subset_closure ⟨a, b, ?_⟩
    have e₁ := Conormal.appLE_appLE d1 (U := V) (V := pullback.fst p p ⁻¹ᵁ V ⊓ pullback.snd p p ⁻¹ᵁ W)
      (W := V ⊓ W) inf_le_left hD.le (by simpa using inf_le_left) a
    have e₂ := Conormal.appLE_appLE d2 (U := W) (V := pullback.fst p p ⁻¹ᵁ V ⊓ pullback.snd p p ⁻¹ᵁ W)
      (W := V ⊓ W) inf_le_right hD.le (by simpa using inf_le_right) b
    rw [e₁, e₂]
    exact congrArg₂ (· * ·) (Conormal.id_appLE _ a) (Conormal.id_appLE _ b)
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact add_mem hx hy

variable {Y : Scheme.{0}} {p : Y ⟶ Sp ℂ}

def GensBdd (V W : Y.Opens) {n : ℕ} (u : Fin n → Γ(Y, V))
    (F : CxPts p (RingHom.id ℂ) → ℂ) : Prop :=
  ∃ (r m : ℕ) (w : Fin r → Γ(Y, W)), ∀ y ∈ ptsIn p (RingHom.id ℂ) (V ⊓ W),
    ‖F y‖ ≤ (∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) *
      (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m

variable {V W : Y.Opens} {n : ℕ} {u : Fin n → Γ(Y, V)}

theorem GensBdd.add {F G : CxPts p (RingHom.id ℂ) → ℂ} (hF : GensBdd V W u F)
    (hG : GensBdd V W u G) : GensBdd V W u fun y => F y + G y := by
  obtain ⟨r₁, m₁, w₁, h₁⟩ := hF
  obtain ⟨r₂, m₂, w₂, h₂⟩ := hG
  refine ⟨r₁ + r₂, max m₁ m₂, Fin.append w₁ w₂, fun y hy => ?_⟩
  have hB : (1 : ℝ) ≤ 1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖ :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have s₁ : 0 ≤ ∑ k, ‖ev p (RingHom.id ℂ) W (w₁ k) y‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have s₂ : 0 ≤ ∑ k, ‖ev p (RingHom.id ℂ) W (w₂ k) y‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc ‖F y + G y‖ ≤ ‖F y‖ + ‖G y‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (h₁ y hy) (h₂ y hy)
    _ ≤ (∑ k, ‖ev p (RingHom.id ℂ) W (w₁ k) y‖) *
            (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ max m₁ m₂ +
          (∑ k, ‖ev p (RingHom.id ℂ) W (w₂ k) y‖) *
            (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ max m₁ m₂ :=
        add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (le_max_left _ _)) s₁)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (le_max_right _ _)) s₂)
    _ = _ := by ring

theorem gensBdd_eval₂ (f : MvPolynomial (Fin n) ℂ) (b : Γ(Y, W)) :
    GensBdd V W u fun y => ev p (RingHom.id ℂ) V (MvPolynomial.eval₂Hom (algX p V) u f) y *
      ev p (RingHom.id ℂ) W b y := by
  induction f using MvPolynomial.induction_on generalizing b with
  | C a =>
    refine ⟨1, 0, fun _ => algX p W a * b, fun y hy => ?_⟩
    have hy' := mem_ptsIn_inf.1 hy
    simp [ev_mul, ev_algX hy'.1, ev_algX hy'.2]
  | add f g hf hg =>
    simpa only [map_add (f := _), ev_add, add_mul] using (hf b).add (hg b)
  | mul_X f l hf =>
    obtain ⟨r, m, w, h⟩ := hf b
    refine ⟨r, m + 1, w, fun y hy => ?_⟩
    have hB : ‖ev p (RingHom.id ℂ) V (u l) y‖ ≤ 1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖ :=
      (Finset.single_le_sum (f := fun l => ‖ev p (RingHom.id ℂ) V (u l) y‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ l)).trans (le_add_of_nonneg_left zero_le_one)
    have s : 0 ≤ (∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) *
        (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m :=
      (norm_nonneg _).trans (h y hy)
    have e : ev p (RingHom.id ℂ) V (MvPolynomial.eval₂Hom (algX p V) u (f * MvPolynomial.X l)) y *
        ev p (RingHom.id ℂ) W b y =
        (ev p (RingHom.id ℂ) V (MvPolynomial.eval₂Hom (algX p V) u f) y *
          ev p (RingHom.id ℂ) W b y) * ev p (RingHom.id ℂ) V (u l) y := by
      rw [map_mul, MvPolynomial.eval₂Hom_X', ev_mul]
      ring
    beta_reduce
    rw [e, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (h y hy) hB (norm_nonneg _) s

theorem exists_gens_bound : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsSeparated p → LocallyOfFiniteType p → ∀ (V : Y.Opens), IsAffineOpen V → ∃ (n : ℕ) (u : Fin n → Γ(Y, V)), ∀ (W : Y.Opens), IsAffineOpen W → ∀ g : Γ(Y, V ⊓ W), ∃ (r m : ℕ) (w : Fin r → Γ(Y, W)), ∀ y ∈ ptsIn p (RingHom.id ℂ) (V ⊓ W), ‖ev p (RingHom.id ℂ) (V ⊓ W) g y‖ ≤ (∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := by
  intro Y p hs hl V hV
  have hc : (algX p V).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  letI : Algebra ℂ Γ(Y, V) := (algX p V).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(Y, V) := hc
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType ℂ Γ(Y, V))
  have hφe (f : MvPolynomial (Fin n) ℂ) :
      φ f = MvPolynomial.eval₂Hom (algX p V) (fun l => φ (MvPolynomial.X l)) f := by
    conv_lhs => rw [MvPolynomial.aeval_unique φ]
    rfl
  refine ⟨n, fun l => φ (MvPolynomial.X l), fun W hW g => ?_⟩
  have key : GensBdd V W (p := p) (fun l => φ (MvPolynomial.X l))
      (ev p (RingHom.id ℂ) (V ⊓ W) g) := by
    induction mem_closure_inf p hV hW g using AddSubmonoid.closure_induction with
    | zero =>
      refine ⟨0, 0, Fin.elim0, fun y hy => ?_⟩
      simp [ev_eq hy]
    | mem x hx =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨f, rfl⟩ := hφ a
      obtain ⟨r, m, w, h⟩ := gensBdd_eval₂ (V := V) (W := W) (p := p)
        (u := fun l => φ (MvPolynomial.X l)) f b
      refine ⟨r, m, w, fun y hy => ?_⟩
      have hy' := mem_ptsIn_inf.1 hy
      rw [ev_mul, ev_res _ hy, ev_res _ hy, hφe]
      exact h y hy
    | add x y _ _ hx hy =>
      have e : ev p (RingHom.id ℂ) (V ⊓ W) (x + y) =
          fun z => ev p (RingHom.id ℂ) (V ⊓ W) x z + ev p (RingHom.id ℂ) (V ⊓ W) y z :=
        funext fun z => ev_add x y z
      rw [e]
      exact hx.add hy
  exact key

end GlobalTheory.CompanionTheory.Gaga
end
end

section

open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists

section Generators

variable (K : Type) [Field K] [Fintype K]

theorem exists_root_over {F : Type} [Field F] {N M : ℕ} (hM : 0 < M) (hNM : N ∣ M) {z w : F}
    (hz : IsPrimitiveRoot z N) (hw : IsPrimitiveRoot w M) : ∃ z' : F, IsPrimitiveRoot z' M ∧ z' ^ (M / N) = z := by
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNM hM
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  have hw' : IsPrimitiveRoot (w ^ (M / N)) N := hw.pow hM (Nat.div_mul_cancel hNM).symm
  obtain ⟨a, -, ha, hza⟩ := (hw'.isPrimitiveRoot_iff).1 hz
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hNM (ZMod.unitOfCoprime a ha)
  have h1 : ((u : ZMod M).val : ZMod N) = (a : ZMod N) := by
    have := congrArg (fun v : (ZMod N)ˣ => (v : ZMod N)) hu
    simpa [ZMod.unitsMap_val] using this
  refine ⟨w ^ (u : ZMod M).val, hw.pow_of_coprime _ (ZMod.val_coe_unit_coprime u), ?_⟩
  rw [← pow_mul, mul_comm, pow_mul, ← hza]
  exact pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff _ _ _).1 h1) hw'.pow_eq_one

theorem lev_pos {d : ℕ} (hd : 0 < d) : 0 < Fintype.card K ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' Fintype.one_lt_card)

theorem exists_prim {d : ℕ} (hd : 0 < d) :
    ∃ w : AlgebraicClosure K, IsPrimitiveRoot w (Fintype.card K ^ d - 1) := by
  have h1 : 1 ≤ Fintype.card K ^ d := Nat.one_le_pow _ _ Fintype.card_pos
  have hq : ((Fintype.card K : ℕ) : AlgebraicClosure K) = 0 := by
    rw [← map_natCast (algebraMap K (AlgebraicClosure K)), Nat.cast_card_eq_zero, map_zero]
  haveI : NeZero ((Fintype.card K ^ d - 1 : ℕ) : AlgebraicClosure K) := ⟨by
    rw [Nat.cast_sub h1, Nat.cast_pow, hq, zero_pow hd.ne']
    simp⟩
  haveI : NeZero (Fintype.card K ^ d - 1) := ⟨(lev_pos K hd).ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot _ _

noncomputable def tower : (k : ℕ) → {z : AlgebraicClosure K // IsPrimitiveRoot z (Fintype.card K ^ k.factorial - 1)}
  | 0 => ⟨(exists_prim K (Nat.factorial_pos 0)).choose, (exists_prim K (Nat.factorial_pos 0)).choose_spec⟩
  | k + 1 =>
    have h := exists_root_over (lev_pos K (Nat.factorial_pos (k + 1)))
      (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial (Nat.le_succ k))) (tower k).2
      (exists_prim K (Nat.factorial_pos (k + 1))).choose_spec
    ⟨h.choose, h.choose_spec.1⟩

theorem tower_succ (k : ℕ) :
    (tower K (k + 1)).1 ^ ((Fintype.card K ^ (k + 1).factorial - 1) / (Fintype.card K ^ k.factorial - 1)) =
      (tower K k).1 :=
  (exists_root_over (lev_pos K (Nat.factorial_pos (k + 1)))
      (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial (Nat.le_succ k))) (tower K k).2
      (exists_prim K (Nat.factorial_pos (k + 1))).choose_spec).choose_spec.2

theorem tower_le {k l : ℕ} (h : k ≤ l) :
    (tower K l).1 ^ ((Fintype.card K ^ l.factorial - 1) / (Fintype.card K ^ k.factorial - 1)) = (tower K k).1 := by
  induction l, h using Nat.le_induction with
  | base => rw [Nat.div_self (lev_pos K (Nat.factorial_pos k)), pow_one]
  | succ l hl ih =>
    rw [← Nat.div_mul_div (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial (Nat.le_succ l)))
      (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial hl)), pow_mul, tower_succ, ih]

theorem exists_genSys : ∃ ζ : ℕ → AlgebraicClosure K, ∀ d, 0 < d → orderOf (ζ d) = Fintype.card K ^ d - 1 ∧
    ∀ d', d ∣ d' → 0 < d' → ζ d' ^ ((Fintype.card K ^ d' - 1) / (Fintype.card K ^ d - 1)) = ζ d := by
  refine ⟨fun d => (tower K d).1 ^ ((Fintype.card K ^ d.factorial - 1) / (Fintype.card K ^ d - 1)),
    fun d hd => ⟨?_, fun d' hdd hd' => ?_⟩⟩
  · have hdv := Nat.pow_sub_one_dvd_pow_sub_one (Fintype.card K) (Nat.dvd_factorial hd le_rfl)
    exact ((tower K d).2.pow (lev_pos K (Nat.factorial_pos d)) (Nat.div_mul_cancel hdv).symm).eq_orderOf.symm
  · have hle : d ≤ d' := Nat.le_of_dvd hd' hdd
    show ((tower K d').1 ^ _) ^ _ = (tower K d).1 ^ _
    rw [← pow_mul, Nat.div_mul_div (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.dvd_factorial hd' le_rfl))
      (Nat.pow_sub_one_dvd_pow_sub_one _ hdd), ← tower_le K hle, ← pow_mul,
      Nat.div_mul_div (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.factorial_dvd_factorial hle))
        (Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.dvd_factorial hd le_rfl))]

theorem nonempty_labelConv [DecidableEq K] : Nonempty (Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.CuspGL.TeichEmb.exists_teichmuller K
  obtain ⟨ζ, hζ⟩ := exists_genSys K
  exact ⟨{ ι := θ, ι_inj := hθ, gen := ζ, gen_order := fun d hd => (hζ d hd).1
           gen_norm := fun d e hd he => (hζ d hd).2 (d * e) (Dvd.intro _ rfl) (Nat.mul_pos hd he) }⟩

theorem exists_monic_irreducible (d : ℕ) (hd : 1 ≤ d) :
    ∃ P : K[X], P.Monic ∧ Irreducible P ∧ P ≠ X ∧ P.natDegree = d := by
  haveI : Fact (Nat.Prime (ringChar K)) := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : NeZero d := ⟨by omega⟩
  let E := FiniteField.Extension K (ringChar K) d
  have hfin : Module.finrank K E = d := FiniteField.finrank_extension K (ringChar K) d
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element K E
  obtain ⟨α, hα0, hα⟩ : ∃ α : E, α ≠ 0 ∧ IntermediateField.adjoin K {α} = ⊤ := by
    by_cases h : β = 0
    · refine ⟨1, one_ne_zero, ?_⟩
      subst h
      rw [IntermediateField.adjoin_one]
      rwa [IntermediateField.adjoin_zero] at hβ
    · exact ⟨β, h, hβ⟩
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  refine ⟨minpoly K α, minpoly.monic hint, minpoly.irreducible hint, fun h => hα0 ?_, ?_⟩
  · have h0 := minpoly.aeval K α
    rwa [h, aeval_X] at h0
  · rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top', hfin]

end Generators

section Transport

variable {G V W : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def transportRep (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) : Representation ℂ G W where
  toFun g := e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem transportRep_apply (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) (g : G) (w : W) :
    transportRep ρ e g w = e (ρ g (e.symm w)) := rfl

end Transport

theorem isIrreducible_transportRep {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) (hV : Nontrivial V)
    (h : ∀ U : Submodule ℂ V, (∀ g, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤) : (transportRep ρ e).IsIrreducible := by
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨e.symm.toEquiv.nontrivial, fun U hU => ?_⟩
  have hinv : ∀ g, ∀ v ∈ U.comap e.toLinearMap, ρ g v ∈ U.comap e.toLinearMap := by
    intro g v hv
    have h1 := hU g (e v) hv
    rw [transportRep_apply, e.symm_apply_apply] at h1
    exact h1
  rcases h _ hinv with h0 | h0
  · left
    refine (Submodule.eq_bot_iff _).2 fun w hw => ?_
    have h1 : e.symm w ∈ U.comap e.toLinearMap := by
      show e (e.symm w) ∈ U
      rwa [e.apply_symm_apply]
    rw [h0, Submodule.mem_bot] at h1
    simpa using h1
  · right
    refine (Submodule.eq_top_iff').2 fun w => ?_
    have h1 : e.symm w ∈ U.comap e.toLinearMap := by rw [h0]; trivial
    have h2 : e (e.symm w) ∈ U := h1
    rwa [e.apply_symm_apply] at h2

theorem isCuspidal_transportRep {K : Type} [Field K] [Fintype K] [DecidableEq K] {N : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (τ : FDRep ℂ (GL (Fin N) K)) (h : Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ) (e : τ ≃ₗ[ℂ] W) :
    GlobalTheory.FiniteGL.IsCuspidal (transportRep τ.ρ e) := by
  rw [GlobalTheory.FiniteGL.isCuspidal_iff_twoBlocks]
  intro a ha haN w hw
  let b : Fin N → Fin 2 := fun i => if (i : ℕ) < a then 0 else 1
  have hs : Function.Surjective b := by
    intro c
    fin_cases c
    · exact ⟨⟨0, by omega⟩, by simp [b, ha]⟩
    · exact ⟨⟨a, haN⟩, by simp [b]⟩
  have h0 := h 2 b hs le_rfl (e.symm w) (fun u hu => ?_)
  · simpa using h0
  · obtain ⟨⟨hUT, -⟩, hdiag⟩ := hu
    have hu' : u ∈ GlobalTheory.FiniteGL.unipRadical K (GlobalTheory.FiniteGL.twoBlocks N a) := by
      intro i j hij
      have hlt : b i = b j ∨ b j < b i := by
        simp only [b, GlobalTheory.FiniteGL.twoBlocks] at hij ⊢
        split_ifs at hij ⊢ <;> simp_all
      rcases hlt with hb | hb
      · rw [Matrix.sub_apply, hdiag i j hb, Matrix.one_apply, sub_self]
      · have hne : i ≠ j := fun e' => by rw [e'] at hb; exact lt_irrefl _ hb
        rw [Matrix.sub_apply, hUT i j hb, Matrix.one_apply_ne hne, sub_zero]
    have h1 := hw u hu'
    rw [transportRep_apply] at h1
    apply e.injective
    rw [h1, e.apply_symm_apply]

end GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists

theorem GlobalTheory.CompanionTheory.Hypotheses₂.cuspidalExists_holds : GlobalTheory.Published.CuspidalExists := by
  intro k _ _ n
  classical
  obtain ⟨C⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.nonempty_labelConv k
  obtain ⟨P, h1, h2, h3, h4⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.exists_monic_irreducible k (n + 1) (by omega)
  obtain ⟨τ, hs, hc, -⟩ := GlobalTheory.CompanionTheory.TyFin.CuspLabel.exists_cuspidal_label k C (n + 1) (by omega) P h1 h2 h3 h4
  have hI := (GlobalTheory.CompanionTheory.TyFin.simpleIffIrr.1 _ τ).1 hs
  let e := (Module.finBasis ℂ τ).equivFun
  exact ⟨_, GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.transportRep τ.ρ e,
    GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.isIrreducible_transportRep τ.ρ e hI.1 hI.2,
    GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists.isCuspidal_transportRep τ hc e⟩
end
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.shintani_values_negative_integers_rational : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (u : (Fin r → ℕ) → ℚ) (cs : List (Fin r)) (N p : ℕ), Fintype.card ι * p < N →
  (∀ i, cs.count i = N ∨ ∀ m, m i ≠ 0 → u m = 0) →
  (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
  ∃ q : ℚ, ∑' m, (u m : ℂ) * DL cs (coneTerm a b (-(p : ℂ))) m = (q : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.series_value_rational | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.series_value_rational | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.series_value_rational <;> assumption)
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.weight_sum_as_finite_differences : ∀ (r l N : ℕ) (w : (Fin r → ℕ) → ℚ), 0 < l → GoodWeight l w →
  ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ),
    (∀ q, BddW (u q)) ∧ (∀ q i, (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧
    ∀ g : (Fin r → ℕ) → ℂ, Summable g → ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.expansion_all_variables | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.expansion_all_variables | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.expansion_all_variables <;> assumption)
end

section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem _root_.GlobalTheory.T.exists_totally_positive_basis_positive_coords : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : ℝ),
    ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis κ ℚ F), (∀ i, TotPos F (b i)) ∧
      ∀ x : F, TotPos F x → (∀ σ τ : F →+* ℝ, σ x ≤ M * τ x) → ∀ i, 0 < b.repr x i := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens.exists_totPos_basis | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens.exists_totPos_basis | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens.exists_totPos_basis <;> assumption)
end

section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem _root_.GlobalTheory.T.exists_congruence_unit_balancing_embeddings : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∃ M : ℝ, ∀ x : F, TotPos F x → ∃ u : (𝓞 F)ˣ, u ∈ congUnits 𝔣 ∧
      ∀ σ τ : F →+* ℝ, σ (((u : 𝓞 F) : F) * x) ≤ M * τ (((u : 𝓞 F) : F) * x) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance.balance | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance.balance | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance.balance <;> assumption)
end
