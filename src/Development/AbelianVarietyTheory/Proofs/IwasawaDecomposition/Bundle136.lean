module

public import Formalism.LocalToGlobal.Columns.RowForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle131
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle128
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivationDivisibleOfCocomm
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Mathlib.Analysis.Normed.Field.Instances
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualInvariantUnit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle129
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG Formalism.UG.P Formalism.EigenvalueLevelCeiling GlobalTheory.AdeleBaseChange
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwistPlaces

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem valued_int {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (b : 𝓞 K) :
    Valued.v (algebraMap K (P.adicCompletion K) (algebraMap (𝓞 K) K b)) = P.intValuation b := by
  rw [levelaf_valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]

theorem intValuation_eq_one {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K}
    (h : b ∉ P.asIdeal) : P.intValuation b = 1 :=
  le_antisymm (P.intValuation_le_one b) (not_lt.1 fun h' => h ((P.intValuation_lt_one_iff_mem b).1 h'))


variable (F E) in
abbrev toId : (RInt F E)ˣ →* (AfE F E)ˣ := Units.map (RInt F E).subtype.toMonoidHom

theorem exists_toId_eq {x : (AfE F E)ˣ} (hx : x ∈ intU F E) : ∃ u, toId F E u = x :=
  ⟨⟨⟨x, hx.1⟩, ⟨(x⁻¹ : (AfE F E)ˣ), hx.2⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩, Units.ext rfl⟩

section
variable {ι : AfE F E →+* FiniteAdeleRing (𝓞 E) E}
  (hι : ∀ x a, ι (x ⊗ₜ[F] a) = algebraMap E _ x * adMap F E a)
include hι

theorem mem_suppAt (v : HeightOneSpectrum (𝓞 F)) (y : (AfE F E)ˣ) :
    y ∈ suppAt E v ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ≠ v → ι (y : AfE F E) P = 1 := by
  have h1 : y ∈ suppAt E v ↔ ∀ v', v' ≠ v → prV (E := E) v' (y : AfE F E) = 1 := by
    simp only [suppAt, Subgroup.mem_iInf, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  rw [h1]
  simp only [prV_eq_one_iff hι]
  exact ⟨fun h P hP => h _ hP P rfl, fun h v' hv P hP => h P (hP ▸ hv)⟩

end

theorem inertAt_le_congN {v : HeightOneSpectrum (𝓞 F)} {N : ℕ} (hN : (N : 𝓞 F) ∉ v.asIdeal) :
    inertAt E v ≤ congN F E N := by
  obtain ⟨ι, hι⟩ := exists_toAd F E
  rintro x ⟨h1, h2⟩
  obtain ⟨u, rfl⟩ := exists_toId_eq h1
  have hN0 : (N : E) ≠ 0 := by
    rintro h
    obtain rfl : N = 0 := by exact_mod_cast h
    exact hN (by simp)
  refine ⟨u, (mem_kerRed _ u).2 (Ideal.mem_span_singleton'.2
    ⟨⟨((N : E)⁻¹ ⊗ₜ[F] 1 : AfE F E) * (((u : RInt F E) - 1 : RInt F E) : AfE F E), mem_int_of_map hι fun P => ?_⟩, Subtype.ext ?_⟩), rfl⟩
  · rw [map_mul, map_tmul_one hι, afsplit_mul_apply, HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hP : P.under (𝓞 F) = v
    · have hNP : (N : 𝓞 E) ∉ P.asIdeal := fun h => hN (by
        rw [← hP]
        change algebraMap (𝓞 F) (𝓞 E) N ∈ P.asIdeal
        rwa [map_natCast])
      have h3 : Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹) P) = 1 := by
        change Valued.v (algebraMap E (P.adicCompletion E) (N : E)⁻¹) = 1
        rw [map_inv₀, map_inv₀, ← map_natCast (algebraMap (𝓞 E) E), valued_int, intValuation_eq_one P hNP, inv_one]
      rw [map_mul, h3, one_mul]
      exact map_mem_int hι ((u : RInt F E) - 1).2 P
    · have h3 : ι ((u : RInt F E) : AfE F E) P = 1 := (mem_suppAt hι v _).1 h2 P hP
      rw [AddSubgroupClass.coe_sub, map_sub, afsplit_sub_apply, h3, OneMemClass.coe_one, map_one, afsplit_one_apply, sub_self,
        mul_zero, map_zero]
      exact zero_le_one
  · apply map_injective hι
    rw [Subring.coe_mul, SubringClass.coe_natCast, map_mul, map_mul, map_natCast, map_tmul_one hι, mul_right_comm,
      ← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)), ← map_mul, inv_mul_cancel₀ hN0, map_one, one_mul]

variable {L : Type} [Field L]

theorem finite_Qprime {ξ : Chr F E L} (h : ξ ∈ openChr F E L) : (Qprime ξ).Finite := by
  obtain ⟨N, hN, hk⟩ := h
  have h0 : (Ideal.span {(N : 𝓞 F)}) ≠ ⊥ := by simpa using hN.ne'
  refine (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 (by_contra fun hn => hv ?_)
  exact (inertAt_le_congN hn).trans hk

end Local

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem under_eq_iff {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (𝓞 F)} :
    P.under (𝓞 F) = v ↔ P.asIdeal.under (𝓞 F) = v.asIdeal :=
  ⟨fun h => h ▸ rfl, fun h => HeightOneSpectrum.ext h⟩

end Res

section Datum

open Formalism.L2.Col

variable {X : _root_.Formalism.L2.Col.Fields}

theorem exists_of_conj_eq (hX : X.Ok) {a : 𝓞 X.E} (ha : X.conjO a = a) :
    ∃ r : 𝓞 X.F, algebraMap (𝓞 X.F) (𝓞 X.E) r = a := by
  let c : X.E →ₐ[X.F] X.E := { starRingEnd X.E with commutes' := hX.star_F }
  let M : IntermediateField X.F X.E :=
    (AlgHom.equalizer c (AlgHom.id _ _)).toIntermediateField fun x hx => by
      have hx' : star x = x := hx
      change star x⁻¹ = x⁻¹
      rw [star_inv₀, hx']
  have hM : M = ⊥ := by
    have := IntermediateField.isSimpleOrder_of_finrank_prime X.F X.E (by rw [hX.rankE]; exact Nat.prime_two)
    refine (eq_bot_or_eq_top M).resolve_right fun e => ?_
    obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hX.f_pos
    refine hX.emb_ne τ τ (RingHom.ext fun x => ?_)
    have h1 : x ∈ M := e ▸ IntermediateField.mem_top
    exact congrArg (X.emb τ) (show star x = x from h1).symm
  have h2 : (a : X.E) ∈ M := congrArg (fun z : 𝓞 X.E => (z : X.E)) ha
  rw [hM, IntermediateField.mem_bot] at h2
  obtain ⟨x, hx⟩ := h2
  have h3 : IsIntegral ℤ x := by
    rw [← isIntegral_algebraMap_iff (B := X.E), hx]
    exact RingOfIntegers.isIntegral_coe _
  exact ⟨⟨x, h3⟩, RingOfIntegers.ext hx⟩

variable {S : Set ℕ} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}

theorem mem_QE_iff (hsel : _root_.Formalism.L2.Col.IsSel X sel) (ξ : Tup X.F X.E X.K S) {P : HeightOneSpectrum (𝓞 X.E)} :
    P ∈ _root_.Formalism.L2.Col.QE sel (ξ : Chr X.F X.E X.K) ↔
      P.under (𝓞 X.F) ∈ Qprime (ξ : Chr X.F X.E X.K) ∧ sel (P.under (𝓞 X.F)) = P := by
  classical
  have hf := finite_Qprime (ξ := (ξ : Chr X.F X.E X.K)) ξ.2.1.1.1.1.2
  rw [_root_.Formalism.L2.Col.QE, dite_eq_left hf, Finset.mem_image]
  simp only [Set.Finite.mem_toFinset]
  refine ⟨?_, fun h => ⟨_, h.1, h.2⟩⟩
  rintro ⟨v, hv, rfl⟩
  rw [under_eq_iff.2 (hsel v)]
  exact ⟨hv, rfl⟩

end Datum

end GlobalTheory.TwistPlaces
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.unramifiedHeckeChar_idele_value_uniformiser : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E) (h : Formalism.L2.NC.HC E), h.χ = (χ : Ideles E →* ℂˣ) → ∀ (v : HeightOneSpectrum (𝓞 E)), (χ.UnrAt v → h.At v (χ.val v)) ∧ (χ.UnrAt v ↔ h.Unr v) := by
  first | exact @GlobalTheory.HeckeUnifVal.at_val_and_unr_iff | exact GlobalTheory.HeckeUnifVal.at_val_and_unr_iff | (intros; apply GlobalTheory.HeckeUnifVal.at_val_and_unr_iff <;> assumption)
end

section

open CategoryTheory Polynomial

theorem _root_.GlobalTheory.T.isCuspidalCharacterOfPolynomial_of_cuspidalLabel : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (hζ : Formalism.L2.NT.IsGenSys L.gen), t = L.teich → ∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))) (P : (ZMod g)[X]), 1 ≤ d → GlobalTheory.GLq.IsCusp (fun x => V.character x) → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (Formalism.L2.NT.convC t ht L.gen hζ) V P → GlobalTheory.GLq.IsCuspOf L P (fun x => V.character x) := by
  first | exact @GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel | exact GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel | (intros; apply GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel <;> assumption)
end

section

open Formalism.MainNotions.DIV.Cons (intO)

theorem _root_.GlobalTheory.T.derivation_divisible_of_cocomm : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (A : Type) [CommRing A] [Bialgebra ↥(intO C) A] [Coalgebra.IsCocomm ↥(intO C) A] [Module.Finite ↥(intO C) A] [Module.Free ↥(intO C) A] (q : ↥(intO C)), q ≠ 0 → ∀ D : A →ₗ[↥(intO C)] ↥(intO C), (∀ a b : A, q ∣ D (a * b) - Coalgebra.counit (R := ↥(intO C)) a * D b - Coalgebra.counit (R := ↥(intO C)) b * D a) → (∀ u : A, IsGroupLikeElem ↥(intO C) u → q ∣ D u) → ∀ c : ↥(intO C), ‖(c : C)‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) → ∀ a : A, q ∣ c * D a := by
  first | exact @GlobalTheory.GroupLikeDerivation.dvd_mul_of_groupLike | exact GlobalTheory.GroupLikeDerivation.dvd_mul_of_groupLike | (intros; apply GlobalTheory.GroupLikeDerivation.dvd_mul_of_groupLike <;> assumption)
end

section

open GlobalTheory.IntegralityCompare

theorem _root_.GlobalTheory.T.weyl_lattice_dual_invariant_unit : ∀ (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ)
    (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) (F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]),
    ‖c‖ = 1 → (∀ τ a b, ‖g τ a b‖ ≤ 1) → (∀ τ, ‖(g τ).det‖ = 1) →
    ((fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν ↔ F ∈ WeylLatticeDuality.DelW p T N ν) := by
  first | exact @GlobalTheory.WeylTensorSubst.subst_mem_iff | exact GlobalTheory.WeylTensorSubst.subst_mem_iff | (intros; apply GlobalTheory.WeylTensorSubst.subst_mem_iff <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.square_iso_carries_square_cubical : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 G).left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t r z N ^ 2 =
        (∏ k : thK.{0}, gv wL (r ≫ thφ G (x3 G) k) z (fun _ => N (r ≫ thφ G (x3 G) k))
          (fun _ => N' (r ≫ thφ G (x3 G) k)) ^ thε k) *
        val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t r z N' ^ 2 := by
  first | exact @GlobalTheory.sq_iso_carries_sq_cube | exact GlobalTheory.sq_iso_carries_sq_cube | (intros; apply GlobalTheory.sq_iso_carries_sq_cube <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.square_iso_respects_symmetry_pointwise : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U.symG r z N ^ 2 =
        (∏ k : Fin 2, gv wL (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k) z
          (fun _ => N (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k))
          (fun _ => N' (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
        val (L := U'.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U'.symG r z N' ^ 2 := by
  first | exact @GlobalTheory.sq_iso_respects_symmetry_pointwise | exact GlobalTheory.sq_iso_respects_symmetry_pointwise | (intros; apply GlobalTheory.sq_iso_respects_symmetry_pointwise <;> assumption)
end
