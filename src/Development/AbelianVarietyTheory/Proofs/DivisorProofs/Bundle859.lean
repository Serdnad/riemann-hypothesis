module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle769
public import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle557
public import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
public import GroundTheory.AutomorphicForms.GKModules.RightRegular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle614
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle618
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle015
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle002

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem GlobalTheory.DualFrobNil.isNil_dual_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → GlobalTheory.PDivLat.IsConn G.dual → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, IsUnit U → (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hμ k e hB hA hconn U hU hfr
  obtain ⟨m, hmax, hpm⟩ := Ideal.exists_le_maximal (Ideal.span {(p : O)}) (by
    rw [Ne, Ideal.span_singleton_eq_top]; exact Fact.out)
  have hp : (p : O) ∈ m := hpm (Ideal.mem_span_singleton_self _)
  obtain ⟨c', hc'⟩ := GlobalTheory.T.coeff_p_logarithms_congr_inv_frobenius_matrix_mod_p p F.B F.Q F.s F.σ F.s_alg F.frame.inj d k e U hU hfr (fun a => (hA a).2)
    (fun r j => by obtain ⟨b, -, hb⟩ := (hB.1 r).2.1 j; exact ⟨b, hb⟩)
  refine GlobalTheory.T.isNilpotent_dualFrobenius_of_block F.B O F.θ F.σ p m (by rw [map_natCast]; exact hp) hmax.ne_top
    (fun b => by obtain ⟨c, hc⟩ := F.σ_pow b; exact ⟨c, hc⟩) d k U c' (fun a j => (hc' a j).2) ?_
  set Sh : (Fin d → O ⧸ m) → (Fin d → O ⧸ m) :=
    fun w a => ∑ j, Ideal.Quotient.mk m (F.θ (c' a j)) * w j ^ p with hSh
  obtain ⟨n, hlift⟩ := GlobalTheory.T.exists_cartierDual_lift_linearCoefficients_mod p O G d c m hp
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_uniform_convolution_pow_apply_mem_localDual p O G n m hmax (hconn n)
  have hθ : ∀ x ∈ RingHom.ker F.θ ⊔ Ideal.span {(p : F.B)}, F.θ x ∈ m := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    rw [map_add (f := _), RingHom.mem_ker.1 hy, zero_add, map_mul, map_natCast]
    exact m.mul_mem_left _ hp
  have step : ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ Fs, φ (c.ev n Fs) - ∑ i, u i * lin Fs i ∈ m) →
      ∃ u' : Fin d → O, (∀ Fs, (φ ^ p) (c.ev n Fs) - ∑ i, u' i * lin Fs i ∈ m) ∧
        (fun a => Ideal.Quotient.mk m (u' a)) = Sh (fun a => Ideal.Quotient.mk m (u a)) := by
    intro u φ hφ
    refine ⟨fun a => constantCoeff ((invDer c.μ u)^[p] (X a)), fun Fs => ?_, ?_⟩
    · obtain ⟨t, ht⟩ := GlobalTheory.T.constantCoeff_iterate_invariant_derivation_linear p O d c.μ c.isLaw.const c.isLaw.unit c.isLaw.comm u Fs
      have h1 := GlobalTheory.T.convPow_ofConv_sub_constantCoeff_invariantDerivation p O G d c n m hp u φ hφ p Fs
      have h2 : (p : O) * t ∈ m := m.mul_mem_right t hp
      have e1 : (φ ^ p) (c.ev n Fs) - ∑ i, constantCoeff ((invDer c.μ u)^[p] (X i)) * lin Fs i =
          ((φ ^ p) (c.ev n Fs) - constantCoeff ((invDer c.μ u)^[p] Fs)) + p * t := by
        rw [← ht]; simp only [lin]; ring
      rw [e1]; exact m.add_mem h1 h2
    · funext a
      choose ũ hũ using fun i => F.frame.surj (u i)
      have hnat := GlobalTheory.T.map_invariantDerivationFormalGroupLaw_iterate F.B O F.θ d μ' hL.const ũ p (X a)
      have hmu : (fun i => map F.θ (μ' i)) = c.μ := funext hμ
      have hu : (fun i => F.θ (ũ i)) = u := funext hũ
      rw [hmu, hu, map_X] at hnat
      have key := hθ _ (GlobalTheory.T.constantCoeff_pIterate_invariantDerivation_coord p F.B O F.Q F.θ F.frame d μ' hL (e (Sum.inl a)) a (hB.1 _) (hA a).1
        (hA a).2 (c' a) (fun i => (hc' a i).1) ũ)
      have hcc : constantCoeff ((invDer c.μ u)^[p] (X a)) =
          F.θ (constantCoeff ((invDer μ' ũ)^[p] (X a))) := by
        rw [← hnat, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]
      simp only [hSh]
      rw [hcc, ← hu]

      simp only [← map_pow, ← map_mul, ← map_sum]
      rw [Ideal.Quotient.eq]

      simpa [map_sub, map_sum, map_mul, map_pow] using key
  have iter : ∀ t (u : Fin d → O) (φ : G.dual.A n), (∀ Fs, φ (c.ev n Fs) - ∑ i, u i * lin Fs i ∈ m) →
      ∃ u' : Fin d → O, (∀ Fs, (φ ^ (p ^ t)) (c.ev n Fs) - ∑ i, u' i * lin Fs i ∈ m) ∧
        (fun a => Ideal.Quotient.mk m (u' a)) = Sh^[t] (fun a => Ideal.Quotient.mk m (u a)) := by
    intro t
    induction t with
    | zero => intro u φ hφ; exact ⟨u, by simpa using hφ, rfl⟩
    | succ t ih =>
      intro u φ hφ
      obtain ⟨u1, h1, e1⟩ := ih u φ hφ
      obtain ⟨u2, h2, e2⟩ := step u1 _ h1
      refine ⟨u2, fun Fs => ?_, ?_⟩
      · rw [pow_succ, pow_mul]; exact h2 Fs
      · rw [e2, e1, Function.iterate_succ_apply']
  refine ⟨r, fun w => ?_⟩
  obtain ⟨u, rfl⟩ : ∃ u : Fin d → O, (fun a => Ideal.Quotient.mk m (u a)) = w :=
    ⟨fun a => (Ideal.Quotient.mk_surjective (w a)).choose,
      funext fun a => (Ideal.Quotient.mk_surjective (w a)).choose_spec⟩
  obtain ⟨φ, hφ⟩ := hlift u
  obtain ⟨u', h', e'⟩ := iter r u φ hφ
  rw [← e']
  funext a
  have h1 : φ 1 ∈ m := by
    have := hφ 1
    simpa [lin, coeff_one] using this
  have hle : r ≤ p ^ r := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have h3 := hr φ h1 (p ^ r) hle (c.x n a)
  have h4 := h' (X a)
  rw [(c.isEval n).1 a] at h4
  have hs : ∑ i, u' i * lin (X a : MvPowerSeries (Fin d) O) i = u' a := by
    simp [lin, coeff_X, Finsupp.single_eq_single_iff]
  rw [hs] at h4
  have h5 : u' a ∈ m := by
    have := m.sub_mem h3 h4
    simpa using this
  simpa [Ideal.Quotient.eq_zero_iff_mem] using h5
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem point_hol_ext_of_isSeparated : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) {X : Scheme.{0}}, X.IsSeparated → ∀ x x' : Sp (Hol W) ⟶ X, (∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = spMap (Hol.ev p hp).toRingHom ≫ x') → x = x' := by
  intro E _ _ W X hX x x' h
  have : IsSeparated (terminal.from X) := hX.isSeparated_terminal_from
  exact point_hol_ext E W X (⊤_ Scheme) (terminal.from X) x x' (terminal.hom_ext _ _) h

end GlobalTheory.AnPer
end

section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem _root_.GlobalTheory.T.isSmoothFun_and_rightDeriv_eq_leftInvariantVectorField : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (glH E a).IsSmoothFun (fun y : glG E a => f (toL y.1.val)) ∧ ∀ X : glL E a, ContDiffOn ℝ ∞ (vecF E a (toL X.1) f) (invSet E a) ∧ (glH E a).rightDeriv X (fun y : glG E a => f (toL y.1.val)) = fun y : glG E a => vecF E a (toL X.1) f (toL y.1.val) := by
  first | exact @GlobalTheory.GlVec.isSmoothFun_and_rightDeriv_eq_vecF | exact GlobalTheory.GlVec.isSmoothFun_and_rightDeriv_eq_vecF | (intros; apply GlobalTheory.GlVec.isSmoothFun_and_rightDeriv_eq_vecF <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.FrobEmb

theorem norm_le_one_of_isIntegral {C : Type*} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

def compPerm {E C : Type} [Field E] [Field C] (f : C ≃+* C) : Equiv.Perm (E →+* C) where
  toFun τ := f.toRingHom.comp τ
  invFun τ := f.symm.toRingHom.comp τ
  left_inv τ := by ext x; simp
  right_inv τ := by ext x; simp

theorem exists_frobPerm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime], ¬ (l : ℤ) ∣ NumberField.discr E →
    ∃ σ : Equiv.Perm (E →+* PadicAlgCl l), IsFrobPerm σ ∧ ∀ τ, σ (cj τ) = cj (σ τ) := by
  intro E _ _ _ l _ _
  obtain ⟨Fr, hFr⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_isFrob (p := l) (K := ReciprocityTheory.DiscreteGroups.LocalClassField.Q0 l) ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_base_field
  refine ⟨compPerm Fr.toRingEquiv, ?_, fun τ => rfl⟩
  intro τ x
  have hx : ‖τ (x : E)‖ ≤ 1 := norm_le_one_of_isIntegral (map_isIntegral_int τ x.isIntegral_coe)
  have h := hFr (τ (x : E)) hx
  rw [ReciprocityTheory.DiscreteGroups.LocalClassField.residue_cardinality_base_field] at h
  exact h

end GlobalTheory.FrobEmb
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.OccBlock

open Module Module.End

section Gen

variable {L V J : Type} [Field L] [DecidableEq L] [AddCommGroup V] [Module L V]

def jointGen (T : J → End L V) (y : J → L) : Submodule L V := ⨅ j, (T j).maxGenEigenspace (y j)

theorem mem_iSup_filter (T : J → End L V) (p : (J → L) → Submodule L V) (hp : ∀ y, p y ≤ jointGen T y) {θ : J → L} {f : V}
    (hf : ∀ j, T j f = θ j • f) (Y : Finset (J → L)) (j : J) (hY : f ∈ ⨆ y ∈ Y, p y) :
    f ∈ ⨆ y ∈ Y.filter (fun y => y j = θ j), p y := by
  have hsplit : (⨆ y ∈ Y, p y) ≤ (⨆ y ∈ Y.filter (fun y => y j = θ j), p y) ⊔
      (⨆ y ∈ Y.filter (fun y => y j ≠ θ j), p y) := by
    refine iSup₂_le fun y hy => ?_
    by_cases h : y j = θ j
    · exact le_sup_of_le_left (le_biSup p (Finset.mem_filter.2 ⟨hy, h⟩))
    · exact le_sup_of_le_right (le_biSup p (Finset.mem_filter.2 ⟨hy, h⟩))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hsplit hY)
  have hA : (⨆ y ∈ Y.filter (fun y => y j = θ j), p y) ≤ (T j).maxGenEigenspace (θ j) := by
    refine iSup₂_le fun y hy => ?_
    have hyj := (Finset.mem_filter.1 hy).2
    calc p y ≤ jointGen T y := hp y
      _ ≤ (T j).maxGenEigenspace (y j) := iInf_le (fun j => (T j).maxGenEigenspace (y j)) j
      _ = (T j).maxGenEigenspace (θ j) := by rw [hyj]
  have hB : (⨆ y ∈ Y.filter (fun y => y j ≠ θ j), p y) ≤ ⨆ (μ : L) (_ : μ ≠ θ j), (T j).maxGenEigenspace μ := by
    refine iSup₂_le fun y hy => ?_
    calc p y ≤ jointGen T y := hp y
      _ ≤ (T j).maxGenEigenspace (y j) := iInf_le (fun j => (T j).maxGenEigenspace (y j)) j
      _ ≤ _ := le_biSup (fun μ => (T j).maxGenEigenspace μ) (show y j ∈ {μ | μ ≠ θ j} from (Finset.mem_filter.1 hy).2)
  have hfθ : f ∈ (T j).maxGenEigenspace (θ j) := by
    rw [mem_maxGenEigenspace]
    exact ⟨1, by simp [hf j]⟩
  have hb0 : b = 0 := by
    have hb1 : b ∈ (T j).maxGenEigenspace (θ j) := by
      have hbe : b = f - a := by rw [← hab]; abel
      rw [hbe]
      exact Submodule.sub_mem _ hfθ (hA ha)
    exact (Submodule.disjoint_def.1 ((Module.End.independent_maxGenEigenspace (T j)) (θ j))) b hb1 (hB hb)
  rw [← hab, hb0, add_zero]
  exact ha

theorem mem_of_mem_iSup_finset (T : J → End L V) (p : (J → L) → Submodule L V) (hp : ∀ y, p y ≤ jointGen T y)
    {θ : J → L} {f : V} (hf : ∀ j, T j f = θ j • f) (Y : Finset (J → L)) (hY : f ∈ ⨆ y ∈ Y, p y) : f ∈ p θ := by
  induction Y using Finset.strongInduction with
  | H Y ih =>
    by_cases h : ∃ y ∈ Y, y ≠ θ
    · obtain ⟨y0, hy0, hne⟩ := h
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
      exact ih _ (Finset.filter_ssubset.2 ⟨y0, hy0, hj⟩) (mem_iSup_filter T p hp hf Y j hY)
    · push_neg at h
      exact (iSup₂_le fun y hy => by rw [h y hy] : (⨆ y ∈ Y, p y) ≤ p θ) hY

end Gen

section Read

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)

def heckeQ (i : F.I) : End (PadicAlgCl l) (F.G → NablaT (PadicAlgCl l) N lam) where
  toFun h g := F.emb (F.cst i) • ∑ s ∈ F.tr i, h (g * s)
  map_add' h h' := by
    funext g
    simp [Finset.sum_add_distrib, smul_add]
  map_smul' c h := by
    funext g
    simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_smul, smul_smul, mul_comm]

variable {F lam} {K : Type} [Field K] [NumberField K] [StarRing K] {G0 : Type} [Group G0] [Fintype G0] {Pl0 : Type}
  {B : BlockDat K G0 Pl0} {w : HeightOneSpectrum (𝓞 K)}

theorem rd_pow (R : Reads F lam B w) (i : F.I) (a : K) (k : ℕ) (v : B.S.Forms) :
    R.rd (((B.op (R.ix i) - a • (1 : End K B.S.Forms)) ^ k) v) =
      ((heckeQ F lam i - R.e0 a • (1 : End (PadicAlgCl l) (F.G → NablaT (PadicAlgCl l) N lam))) ^ k) (R.rd v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    funext g
    simp [map_sub, map_smulₛₗ, R.hecke, heckeQ]

end Read

theorem hasBlock_of_occurs : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G0 : Type) [Group G0] [Fintype G0] (Pl0 : Type)
    (B : BlockDat K G0 Pl0) (w : HeightOneSpectrum (𝓞 K)) (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N)
    (lam : ι → ℕ → ℕ) (R : Reads F lam B w) (Z : Submodule K B.S.Forms), (∀ P, B.op (P, 0) = 1) →
    Z ≤ B.ZH → ∀ θ, R.Occurs Z θ → R.HasBlock θ ∧ F.IsEig lam θ := by
  intro K _ _ _ G0 _ _ Pl0 B w l _ ι _ N F lam R Z hop hZ θ hocc
  obtain ⟨f, hfspan, hfe⟩ := hocc
  refine ⟨?_, ⟨f, hfe⟩⟩
  classical
  let S : Set (F.I → PadicAlgCl l) :=
    {y | ∃ x : B.Pl × ℕ → K, (∀ P, x (P, 0) = 1) ∧ Formalism.L2.Col.HasBlocks B.n B.q B.t B.bl x ∧ ∀ i, y i = R.e0 (x (R.ix i))}
  let p : (F.I → PadicAlgCl l) → Submodule (PadicAlgCl l) (F.G → NablaT (PadicAlgCl l) N lam) :=
    fun y => ⨆ (_ : y ∈ S), jointGen (heckeQ F lam) y
  have hp : ∀ y, p y ≤ jointGen (heckeQ F lam) y := fun y => iSup_le fun _ => le_rfl
  have key : B.ZH ≤ (⨆ y, p y).comap R.rd := by
    rw [BlockDat.ZH, Formalism.L2.Col.blockSum, Formalism.L2.Col.eigSum]
    refine iSup₂_le fun x hx => ?_
    intro v hv
    rw [Submodule.mem_comap]
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
      exact Submodule.zero_mem _
    have hx1 : ∀ P, x (P, 0) = 1 := fun P =>
      GlobalTheory.ExpFrame.eq_one_of_occurs (op := B.op) ((Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩) (hop P)
    refine Submodule.mem_iSup_of_mem (fun i => R.e0 (x (R.ix i))) ?_
    refine Submodule.mem_iSup_of_mem (show (fun i => R.e0 (x (R.ix i))) ∈ S from ⟨x, hx1, hx, fun i => rfl⟩) ?_
    rw [jointGen, Submodule.mem_iInf]
    intro i
    have hv' := Formalism.L2.Col.eigAt_le B.op x (R.ix i) hv
    rw [mem_maxGenEigenspace] at hv' ⊢
    obtain ⟨k, hk⟩ := hv'
    exact ⟨k, by rw [← rd_pow, hk, map_zero]⟩
  have hspan : Submodule.span (PadicAlgCl l) (R.rd '' Z) ≤ ⨆ y, p y := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact key (hZ hz)
  obtain ⟨Y, hY⟩ := Submodule.mem_iSup_iff_exists_finset.1 (hspan hfspan)
  have hf : ∀ i, heckeQ F lam i f = θ i • f := fun i => by
    funext g
    exact hfe.2.2 i g
  have hθ := mem_of_mem_iSup_finset (heckeQ F lam) p hp hf Y hY
  by_cases hθS : θ ∈ S
  · exact hθS
  · exfalso
    have h0 : p θ = ⊥ := by simp [p, hθS]
    rw [h0, Submodule.mem_bot] at hθ
    exact hfe.1 hθ

end GlobalTheory.OccBlock

end
end

section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpFrame.LevelMap

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ}

theorem grpA_mul (O : Type) [CommRing O] (lam : ι → ℕ → ℕ) (g h : ι → GL (Fin N) O) :
    grpA O N lam (g * h) = grpA O N lam g * grpA O N lam h := by
  apply Subtype.ext
  show grp O N lam (g * h) = grp O N lam g * grp O N lam h
  unfold grp
  exact map_mul _ g h

theorem grpA_one (O : Type) [CommRing O] (lam : ι → ℕ → ℕ) :
    grpA O N lam 1 = 1 := by
  apply Subtype.ext
  show grp O N lam 1 = 1
  unfold grp
  exact map_one _

def jK (F : Frame l ι N) (lam : ι → ℕ → ℕ) : F.K →* alg F.O N lam where
  toFun κ := (F.chi κ : F.O) • grpA F.O N lam (F.kap κ)
  map_one' := by simp [grpA_one]
  map_mul' a b := by
    rw [map_mul, map_mul, grpA_mul, Units.val_mul, smul_mul_smul_comm]

end GlobalTheory.ExpFrame.LevelMap

theorem GlobalTheory.ExpFrame.levelMap_exists : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ), ∃ (jK : F.K →* alg F.O N lam), F.IsJ lam jK := by
  intro l _ ι _ _ N F lam
  exact ⟨GlobalTheory.ExpFrame.LevelMap.jK F lam, fun κ => rfl⟩

end
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD GlobalTheory.ExpFrame

namespace GlobalTheory.HighWt

variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)

def JointWt (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm] (w : ι → Fin N → ℕ) : Prop :=
  ∃ z : Gm, z ≠ 0 ∧ ∀ τ (a : alg O N lam), IsProj O N lam τ (w τ) a → a • z = z

def pot {ι : Type} [Fintype ι] (w : ι → Fin N → ℕ) : ℕ := ∑ τ, ∑ a : Fin N, (N - (a : ℕ)) * w τ a

def extW {ι : Type} (w : ι → Fin N → ℕ) : ι → ℕ → ℕ := fun τ a => if h : a < N then w τ ⟨a, h⟩ else 0

def genSub (f : MvPolynomial (Fin N × Fin N) O) : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  aeval (fun v : Fin N × Fin N => ∑ b : Fin N, X (v.1, b) * C (X (b, v.2))) f

def IsCoef (τ : ι) (m : Fin N × Fin N →₀ ℕ) (a : Module.End O (NablaT O N lam)) : Prop :=
  ∀ (x : ∀ τ, dualWeyl O N N (res N (lam τ))) (y : dualWeyl O N N (res N (lam τ))),
    (y : MvPolynomial (Fin N × Fin N) O) = (genSub O N (x τ : MvPolynomial (Fin N × Fin N) O)).coeff m →
    a (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y)

def CoefIn : Prop := ∀ (τ : ι) (m : Fin N × Fin N →₀ ℕ), ∃ a : alg O N lam, IsCoef O N lam τ m a

def BaseChange : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
    (∀ f ∈ dualWeyl (O ⧸ Ideal.span {ϖ}) N N ν, ∃ g ∈ dualWeyl O N N ν, MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g = f) ∧
    (∀ g ∈ dualWeyl O N N ν, MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g = 0 → ∃ h ∈ dualWeyl O N N ν, g = ϖ • h)

theorem res_extW {ι : Type} (w : ι → Fin N → ℕ) (τ : ι) : res N (extW N w τ) = w τ := by
  funext a
  simp [res, extW, a.isLt]

end GlobalTheory.HighWt

end
end

section

open GlobalTheory.ExpFrame

namespace GlobalTheory.ExpFrame

theorem Frame.prime_not_isUnit : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok → ¬ IsUnit ((l : ℕ) : F.O) := by
  intro l _ ι N F hF hu
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  obtain ⟨L, -, hL⟩ := hF.ring.2
  have hmem : F.emb u ∈ Set.range F.emb := ⟨u, rfl⟩
  rw [hL] at hmem
  have h1 : F.emb u * (l : PadicAlgCl l) = 1 := by
    have := congrArg F.emb hu
    rwa [map_mul, map_natCast, map_one] at this
  have hl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have e : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [e, PadicAlgCl.norm_extends, Padic.norm_p]
  have h2 := congrArg norm h1
  rw [norm_mul, norm_one, hl] at h2
  have hlgt : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlpos : (0 : ℝ) < l := by linarith
  have h3 : ‖F.emb u‖ * (l : ℝ)⁻¹ < 1 := by
    calc ‖F.emb u‖ * (l : ℝ)⁻¹ ≤ 1 * (l : ℝ)⁻¹ := by gcongr; exact hmem.2
      _ = (l : ℝ)⁻¹ := one_mul _
      _ < 1 := inv_lt_one_of_one_lt₀ hlgt
  linarith

end GlobalTheory.ExpFrame
end
