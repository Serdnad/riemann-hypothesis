module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle128
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle121
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle125
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle098
public import Formalism.HermitianLattices.StatementLat
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle135
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_unit_tauCoordinate_add_nsmul_first_variable : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.TauBimult →
    ∀ (a z b : D.X) (k : ℕ) (x x' x'' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b x →
      GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D z b x' → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D (a + k • z) b x'' →
      ∃ u : Rˣ, x'' = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * (x * x' ^ k) := by
  first | exact @GlobalTheory.TauShift.main | exact GlobalTheory.TauShift.main | (intros; apply GlobalTheory.TauShift.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_injective_lift_field {R S K : Type} [CommRing R] [CommRing S] [CommRing K] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (hK : IsField K) (g : R →+* K) (hg : Function.Injective g)
    (hM : ∀ y ∈ M, y ≠ 0) :
    ∃ ι : S →+* K, (∀ x : R, ι (algebraMap R S x) = g x) ∧ Function.Injective ι := by
  have hu : ∀ y : M, IsUnit (g y) := by
    intro y
    have h : g y ≠ 0 := fun h => hM y y.2 (hg (by rw [h, map_zero]))
    obtain ⟨b, hb⟩ := hK.mul_inv_cancel h
    exact IsUnit.of_mul_eq_one b hb
  refine ⟨IsLocalization.lift hu, fun x => IsLocalization.lift_eq hu x, ?_⟩
  rw [IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h
    rw [← IsLocalization.lift_eq (S := S) hu x, h, IsLocalization.lift_eq]
  · intro h
    rw [hg h]

theorem algebraMap_ainf_acris_eq {l : ℕ} [Fact l.Prime] (x : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.Acris l) x =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) :=
  GlobalTheory.RingIface.tower l x

theorem algebraMap_ainf_acris_ne_zero_pt {l : ℕ} [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l)
    (hj : IsCrisP j) (x : Per.Ainf l) (hx0 : x ≠ 0) : algebraMap (Per.Ainf l) (Per.Acris l) x ≠ 0 := by
  obtain ⟨hd, -, hi⟩ := GlobalTheory.T.usage l
  intro h'
  apply hx0
  have h1 := hj.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x)
  rw [← algebraMap_ainf_acris_eq] at h1
  rw [h', map_zero] at h1
  have h2 : ((algebraMap (Per.Ainf l) (Per.Acris0 l) x : Per.Acris0 l) : Per.AinfP l) = 0 :=
    GlobalTheory.T.algebraMap_ainfInvPrime_bdRPlus_injective l (by rw [map_zero]; exact h1.symm)
  exact hi (by rw [map_zero]; exact h2)

theorem pow_root_ne_zero {l : ℕ} [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j)
    (e : Per.Fl l) (hne : e ≠ 1) (n : ℕ) :
    algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1) ^ n ≠ 0 := by
  obtain ⟨hd, -, -⟩ := GlobalTheory.T.usage l
  rw [← map_pow]
  refine algebraMap_ainf_acris_ne_zero_pt j hj _ (pow_ne_zero n fun h => ?_)
  exact GlobalTheory.CrisLoc.constantCoeff_root_ne_zero l e hne (by rw [h, map_zero])

theorem exists_iota_cris_dR : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j →
    ∃ ι : Per.Bcris l →+* Per.BdR l, (∀ x : Per.Acris l, ι (algebraMap (Per.Acris l) (Per.Bcris l) x) =
      algebraMap (Per.BdRp l) (Per.BdR l) (j x)) ∧ Function.Injective ι := by
  intro l _ j hj
  obtain ⟨-, hi, hK, -⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  haveI := GlobalTheory.CrisLoc.bcris_away l e he hne
  refine exists_injective_lift_field
    (Submonoid.powers (algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1))) hK
    ((algebraMap (Per.BdRp l) (Per.BdR l)).comp j) (hi.comp (GlobalTheory.T.acrisToBdRPlus_injective l j hj)) ?_
  rintro _ ⟨n, rfl⟩
  exact pow_root_ne_zero j hj e hne n

end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogKer

theorem exists_sum_factorial {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (l : ℕ) (hl : 0 < l)
    (hA : IsAdicComplete (Ideal.span {(l : A)}) A) (γ : ℕ → R) :
    ∃ Y : A, ∀ r n : ℕ, l ^ r ≤ n → ∃ w : A,
      Y = f (∑ k ∈ Finset.range n, (-1) ^ k * ((k.factorial : ℕ) : R) * γ k) + (l : A) ^ r * w := by
  obtain ⟨Y, hY⟩ := LogEx.exists_sum (l : A) (fun k => f ((-1) ^ k * ((k.factorial : ℕ) : R) * γ k))
    (fun r => l ^ r) (fun a b hab => Nat.pow_le_pow_right hl hab) (fun r k hk => by
      obtain ⟨m, hm⟩ := Nat.dvd_factorial (pow_pos hl r) hk
      refine ⟨f ((-1) ^ k * (m : R) * γ k), ?_⟩
      simp only [hm, map_mul, map_natCast, Nat.cast_mul, Nat.cast_pow, map_pow]
      ring)
  refine ⟨Y, fun r n hn => ?_⟩
  obtain ⟨w, hw⟩ := hY r n hn
  exact ⟨w, by rw [map_sum, ← hw]; ring⟩

theorem sum_eq {P : Type} [CommRing P] (u γ : ℕ → P) (x : P) (hu : ∀ k : ℕ, ((k + 1 : ℕ) : P) * u k = 1)
    (hγ : ∀ k : ℕ, (((k + 1).factorial : ℕ) : P) * γ k = x ^ (k + 1)) (n : ℕ) :
    ∑ k ∈ Finset.range n, (-1) ^ k * ((k.factorial : ℕ) : P) * γ k =
      ∑ k ∈ Finset.range n, (-1) ^ k * u k * x ^ (k + 1) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hγ k, Nat.factorial_succ, Nat.cast_mul]
  linear_combination (-((-1) ^ k * ((k.factorial : ℕ) : P) * γ k)) * hu k

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris

theorem exists_log : ∀ (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l), IsCrisP j → ∀ z : Per.Ainf l, Per.θ l z = 0 → ∃ Y : Per.Acris l, ∀ n : ℕ, ((n.factorial : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) * Per.ev l n (j Y) = Ideal.Quotient.mk _ (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1)) := by
  intro l _ j hj z hz
  have hu : ∀ k : ℕ, ∃ u : Per.AinfP l, ((k + 1 : ℕ) : Per.AinfP l) * u = 1 := fun k =>
    (GlobalTheory.RingBasics.isUnit_nat l _ k.succ_ne_zero).exists_right_inv
  choose u hu using hu
  have hf : ∀ k : ℕ, IsUnit ((k.factorial : ℕ) : Per.AinfP l) := fun k =>
    GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero
  have hγ : ∀ k : ℕ, ∃ γ : Per.Acris0 l, (((k + 1).factorial : ℕ) : Per.AinfP l) * (γ : Per.AinfP l) =
      (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1) := fun k => by
    obtain ⟨d, hd⟩ := (hf (k + 1)).exists_right_inv
    have h : (((k + 1).factorial : ℕ) : Per.AinfP l) *
        (d * (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1)) =
        (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1) := by rw [← mul_assoc, hd, one_mul]
    exact ⟨⟨_, GlobalTheory.RingIface.dividedPower_mem_Acris0 l z (k + 1) _ hz h⟩, h⟩
  choose γ hγ using hγ
  have hmem : algebraMap (Per.Ainf l) (Per.AinfP l) z ∈ Per.kerP l :=
    GlobalTheory.RingIface.alg_mem_kerP l hz
  obtain ⟨Y, hY⟩ := exists_sum_factorial (algebraMap (Per.Acris0 l) (Per.Acris l)) l
    (Fact.out : l.Prime).pos (acris_basic l).1 γ
  refine ⟨Y, fun n => ?_⟩
  have hs : ∀ m : ℕ, ((∑ k ∈ Finset.range m, (-1) ^ k * ((k.factorial : ℕ) : Per.Acris0 l) * γ k :
      Per.Acris0 l) : Per.AinfP l) =
      ∑ k ∈ Finset.range m, (-1) ^ k * u k * (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1) := by
    intro m
    rw [← sum_eq u (fun k => (γ k : Per.AinfP l)) _ hu hγ m]
    change (Per.Acris0 l).val _ = _

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, map_pow, map_natCast, map_neg, map_one]
    rfl
  obtain ⟨d, hd⟩ := (hf n).exists_right_inv
  obtain ⟨c, hc⟩ : ∃ c : Per.AinfP l, ((n.factorial : ℕ) : Per.AinfP l) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1) :=
    ⟨d * _, by rw [← mul_assoc, hd, one_mul]⟩
  have key := (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l j hj).2.2 n Y (algebraMap (Per.AinfP l) (Per.BdRp l) c) (by
    intro r
    obtain ⟨w, hw⟩ := hY r (max (l ^ r) n) (le_max_left _ _)
    refine ⟨_, w, 0, hw, ?_⟩
    rw [map_zero, mul_zero, map_zero, ← map_sub, LogFun.ev_alg, Ideal.Quotient.eq_zero_iff_mem,
      hs, LogFun.partial_eq u hu _ _ _ (hf _) hc, ← neg_sub]
    exact neg_mem (LogFun.partial_sub_mem _ u _ hmem (le_max_right _ _)))
  rw [key, LogFun.ev_alg]
  simpa only [map_mul, map_natCast] using congrArg (Ideal.Quotient.mk (Per.kerP l ^ n)) hc

end GlobalTheory.MemLoc.LogKer
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR : ∀ (l : ℕ) [Fact l.Prime], ∀ (e : Per.Fl l) (t : Per.Acris l), e.untilt = 1 → IsLogA e t → (∀ t' : Per.Acris l, IsLogA e t' → t' = t) ∧ (∀ g : Per.Gq l, IsLogA (Per.σF g e) (sigA g t)) ∧ IsLogA (e ^ l) (phiA l t) ∧ ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → Per.IsLog l e (j t) := by
  first | exact @GlobalTheory.MemLoc.LogFun.log_fun | exact GlobalTheory.MemLoc.LogFun.log_fun | (intros; apply GlobalTheory.MemLoc.LogFun.log_fun <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.algebraicHeckeChar_values_in_numberField : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → ∀ (χ : Formalism.L2.Host.HChar L) (n : I → ℤ) (r : ℤ), χ.HasInf φ n → (∀ i, Even (n i - r)) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ χ.ValuesIn ((r : ℝ) / 2) M.val.toRingHom := by
  first | exact @GlobalTheory.Mem.ValAlg.values_in_numberField | exact GlobalTheory.Mem.ValAlg.values_in_numberField | (intros; apply GlobalTheory.Mem.ValAlg.values_in_numberField <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.torusCharacterRestriction_commutes_ringAction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t')
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    ∀ (a : 𝓞 E) (x : P.D.toPre.X), ρ (a • x) = a • ρ x := by
  first | exact @GlobalTheory.restrict_torus_smul_comm | exact GlobalTheory.restrict_torus_smul_comm | (intros; apply GlobalTheory.restrict_torus_smul_comm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.torusCharacterRestriction_trait_surjective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t')
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    Function.Surjective ρ := by
  first | exact @GlobalTheory.TorusOnto.restrict_surjective | exact GlobalTheory.TorusOnto.restrict_surjective | (intros; apply GlobalTheory.TorusOnto.restrict_surjective <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.SysFin

open GlobalTheory.CoefDuty

section Places
variable {R : Ranks} {H : Host R}

theorem intCast_mem_conj {v w : PlE H} (h : IsConjPl H v w) (n : ℤ) :
    (n : 𝓞 H.E) ∈ v.asIdeal ↔ (n : 𝓞 H.E) ∈ w.asIdeal :=
  h _ _ (by simp [map_intCast])

theorem intCast_mem_over {w : PlE H} {v : HeightOneSpectrum (𝓞 (maximalRealSubfield H.E))}
    (h : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield H.E)) (𝓞 H.E)) = v.asIdeal) (n : ℤ) :
    (n : 𝓞 H.E) ∈ w.asIdeal ↔ (n : 𝓞 (maximalRealSubfield H.E)) ∈ v.asIdeal := by
  rw [← h, Ideal.mem_comap, map_intCast]

end Places

theorem finite_intCast_mem {K : Type} [Field K] [NumberField K] (N : ℤ) (hN : N ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | (N : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(N : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hN
  refine (Ideal.finite_factors h0).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem exists_intCast_mem {K : Type} [Field K] [NumberField K] (q : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℤ, n ≠ 0 ∧ (n : 𝓞 K) ∈ q.asIdeal := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot q.ne_bot
  have h := Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral (R := ℤ) x)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine ⟨n, hn0, ?_⟩
  rw [Ideal.mem_comap, eq_intCast] at hn
  exact hn

theorem intCast_mem_of_dvd {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {n N : ℤ} (hd : n ∣ N)
    (h : (n : 𝓞 K) ∈ v.asIdeal) : (N : 𝓞 K) ∈ v.asIdeal := by
  obtain ⟨b, rfl⟩ := hd
  push_cast
  exact Ideal.mul_mem_right _ _ h

section Eig
variable {D : D7}

theorem genAt_mono {l : ℕ} {Q Q' : Finset (PlE D.host)} (hQ : Q ⊆ Q') {v : PlE D.host} {k : ℕ}
    (h : GenAt D l Q' v k) : GenAt D l Q v k :=
  ⟨h.1, h.2.1, h.2.2.1, fun hv => h.2.2.2.1 (hQ hv), h.2.2.2.2⟩

open Classical in
theorem eigSet_restrict {μ : D.what₂.Tup} {j : ℕ} (X : MtReal D μ j) (l : ℕ) {Q Q' : Finset (PlE D.host)} (hQ : Q ⊆ Q')
    {c : PlE D.host → ℕ → ℂ} (hc : c ∈ EigSet X l Q) :
    (fun v k => if GenAt D l Q' v k then c v k else 0) ∈ EigSet X l Q' := by
  obtain ⟨-, y, hy, hy'⟩ := hc
  refine ⟨fun v k hg => if_neg hg, y, hy, fun v k s ϖ hg hcj hu => ?_⟩
  simp only [if_pos hg]
  exact hy' v k s ϖ (genAt_mono hQ hg) hcj hu

theorem eigSet_transport (M : MtFam D) {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ = μ') (hj : j = j')
    (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) (b1 : 1 ≤ j') (b2 : j' ≤ D.R.m) (l : ℕ) (Q : Finset (PlE D.host))
    (c : PlE D.host → ℕ → ℂ) : c ∈ EigSet (M μ j a1 a2) l Q → c ∈ EigSet (M μ' j' b1 b2) l Q := by
  subst hμ hj; exact id

end Eig


end GlobalTheory.SysFin

end
end

section

open NumberField
open scoped Matrix

theorem _root_.GlobalTheory.T.blockDatum_baseChange_definiteLattice_compatible : ∀ {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}
  (φ : K →+* K'), (∀ x : K, φ (star x) = star (φ x)) → ∀ (e : G ≃* G') (B : Formalism.L2.DIV.BlockDat K G Pl0) (B' : Formalism.L2.DIV.BlockDat K' G' Pl0')
    (ℓ : Formalism.L2.DIV.Lvl K G) (ℓ' : Formalism.L2.DIV.Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (s : ℕ)
    (C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K'), B.Ok s → GlobalTheory.Mem.R3.LiftLatBC.BlockBaseChangeAt φ e B B' ℓ ℓ' Z Z' C →
    ∃ Gm : Matrix (Fin (B'.dZ ℓ' Z')) (Fin (B.dZ ℓ Z)) K', Function.Bijective Gm.mulVec ∧
      B'.Tl ℓ' Z' = Submodule.span (𝓞 K') ((fun x : Fin (B.dZ ℓ Z) → K => Matrix.mulVec Gm (fun k => φ (x k))) '' (B.Tl ℓ Z : Set (Fin (B.dZ ℓ Z) → K))) ∧
      ∀ x : Fin (B.dZ ℓ Z) → K, B'.toF ℓ' Z' (Matrix.mulVec Gm fun k => φ (x k)) = GlobalTheory.Mem.R3.LiftLatBC.bcF φ B B' C (B.toF ℓ Z x) := by
  first | exact @GlobalTheory.Mem.R3.LiftLatBC.tl_bcF_of_blockBCAt | exact GlobalTheory.Mem.R3.LiftLatBC.tl_bcF_of_blockBCAt | (intros; apply GlobalTheory.Mem.R3.LiftLatBC.tl_bcF_of_blockBCAt <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.lattice_index_nonzero_iff_under_field_map : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (φ : K →+* K') (d d' : ℕ) (G : Matrix (Fin d') (Fin d) K'),
  Function.Bijective G.mulVec → ∀ (P : HeightOneSpectrum (𝓞 K)) (P' : HeightOneSpectrum (𝓞 K')),
  (∀ (x : 𝓞 K) (x' : 𝓞 K'), φ (x : K) = (x' : K') → (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) →
  ∀ A B : Submodule (𝓞 K) (Fin d → K), A.FG → B.FG →
    (Formalism.HermitianLatticesTheory.lidx P.asIdeal A B ≠ 0 ↔ Formalism.HermitianLatticesTheory.lidx P'.asIdeal
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (A : Set (Fin d → K))))
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (B : Set (Fin d → K)))) ≠ 0) := by
  first | exact @GlobalTheory.LidxBaseChange.lidx_ne_zero_iff | exact GlobalTheory.LidxBaseChange.lidx_ne_zero_iff | (intros; apply GlobalTheory.LidxBaseChange.lidx_ne_zero_iff <;> assumption)
end

section

open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem oLatTie_fg_span_top : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (σ : K →+* ℂ) {O : Type} [CommRing O] {φO : O →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] (M : Formalism.BasicNotions.Rows.OLat O φO W) (j : (Fin n → K) →ₛₗ[σ] W) (N : Submodule (𝓞 K) (Fin n → K)), (LinearIndependent ℂ fun i => j (Pi.single i 1)) → Formalism.L2.DIV.OLatTie σ M j N → N.FG ∧ Submodule.span K (N : Set (Fin n → K)) = ⊤ := by
  intro K _ _ _ n σ O _ φO W _ _ M j N hli hT
  classical
  obtain ⟨hgen, hmem⟩ := hT
  have hj : ∀ x, j x = ∑ i, σ (x i) • j (Pi.single i 1) := by
    intro x
    conv_lhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ]
    simp
  have hinj : Function.Injective j := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hj] at hx
    have h0 := Fintype.linearIndependent_iff.1 hli _ hx
    funext i
    exact σ.injective (by simpa using h0 i)
  have hgen' : ∀ v, ∃ x, v ∈ M.gen → j x = v := by
    intro v
    by_cases hv : v ∈ M.gen
    · obtain ⟨x, hx⟩ := hgen v hv
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose pre hpre using hgen'
  have hN : N = Submodule.span (𝓞 K) (pre '' (M.gen : Set W)) := by
    ext x
    rw [hmem, Submodule.mem_span_image_finset_iff_exists_fun']
    refine exists_congr fun a => ?_
    have : ∑ v ∈ M.gen, σ ((a v : 𝓞 K) : K) • v = j (∑ v ∈ M.gen, a v • pre v) := by

      rw [map_sum]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← algebraMap_smul K (a v) (pre v), map_smulₛₗ, hpre v hv]
    rw [this]
    exact ⟨fun h => (hinj h).symm, fun h => congrArg j h.symm⟩
  refine ⟨hN ▸ Submodule.fg_span ((M.gen.finite_toSet).image pre), ?_⟩
  rw [hN]
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  let B := Module.Basis.span hli
  let F0 := B.constr ℂ (fun i => σ (f (Pi.single i 1)))
  obtain ⟨F, hFF⟩ := LinearMap.exists_extend F0
  have hFe : ∀ i, F (j (Pi.single i 1)) = σ (f (Pi.single i 1)) := by
    intro i
    have h1 : (B i : W) = j (Pi.single i 1) := by simp [B, Module.Basis.span_apply hli i]
    rw [← h1]
    have h2 := LinearMap.congr_fun hFF (B i)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h2]
    simp [F0]
  have hF : ∀ x, F (j x) = σ (f x) := by
    intro x

    rw [hj, map_sum]
    conv_rhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]

    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hFe]
    simp
  have hF0 : F = 0 := by
    apply LinearMap.ext_on M.span_top
    intro v hv
    rw [← hpre v hv, hF]
    have : f (pre v) ∈ (⊥ : Submodule K K) := by
      rw [← hf]
      exact Submodule.mem_map_of_mem
        (Submodule.subset_span (Submodule.subset_span ⟨v, hv, rfl⟩))
    rw [(Submodule.mem_bot K).1 this]
    simp
  apply hf0
  refine LinearMap.ext fun x => σ.injective ?_
  rw [← hF, hF0]
  simp

end GlobalTheory
end
