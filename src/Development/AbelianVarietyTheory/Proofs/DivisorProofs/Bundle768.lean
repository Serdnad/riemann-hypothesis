module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle731
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle716
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle636
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle500
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle733
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle732
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC
open ClsSpec

theorem one_eq_of_ev (q : ℕ) [NeZero q] (E : Spc) (hE : Inv q E)
    (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0)
    (hα : ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) :
    CohomologyClass.mk α = one q E := by
  obtain ⟨β, hβ, hβv⟩ := one_spec q E hE
  rw [← hβ]
  congr 1
  refine Cocycle.ext ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s h U x => ?_)
  cases p with
  | zero =>
    obtain rfl : s = 0 := by simpa using h.symm
    refine ClsSpec.sep (ClsSpec.loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 (hE U ⟨x⟩)) fun V g hz => ?_)
    obtain ⟨ζ⟩ := hz
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 α.1, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β.1, hα _ _ ζ, hβv _ _ ζ]
  | succ p =>
    have hs : s < 0 := by omega
    haveI := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness (ZMod q) (tw q 0) U).2.2.2 s hs
    exact Subsingleton.elim _ _

theorem pull_one (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') :
    pull _ f _ _ (one q E') = one q E := by
  have hE : Inv q E := fun U ⟨x⟩ => hE' U ⟨x.map f⟩
  obtain ⟨β, hβ, hβv⟩ := one_spec q E' hE'
  rw [← hβ]
  refine one_eq_of_ev q E hE _ fun U x ζ => ?_
  exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 f β.1 0 0 _ U x).trans (hβv U (x.map f) ζ)

theorem rootClass_eq_secClass {q : ℕ} (i : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) :
    rootClass i ζ = secClass (tw q i) (twGen i ζ) := by
  unfold rootClass secClass
  congr 1
  funext c
  apply propext
  constructor
  · rintro ⟨α, hα, h⟩
    exact ⟨α, hα, (h X (𝟙 X)).trans (ClsSpec.res_id _)⟩
  · rintro ⟨α, hα, h⟩
    refine ⟨α, hα, fun U x => ?_⟩
    have e := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 α.1 0 0 (by simp) U X x (𝟙 X)
    rw [h] at e
    refine e.symm.trans ?_
    congr 1

theorem one_root_spec : ∀ (q : ℕ) [NeZero q], (∀ E : Spc, Inv q E → ∃ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, CohomologyClass.mk α = one q E ∧ ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) ∧ (∀ E : Spc, Inv q E → ∀ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, (∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) → CohomologyClass.mk α = one q E) ∧ (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → pull _ f _ _ (one q E') = one q E) ∧ ∀ (i : ℤ) (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)), rootClass i ζ = secClass (tw q i) (twGen i ζ) :=
  fun q _ => ⟨fun E hE => one_spec q E hE, fun E hE α hα => one_eq_of_ev q E hE α hα,
    fun f hE' => pull_one q f hE', fun i _ ζ => rootClass_eq_secClass i ζ⟩

end GlobalTheory.EtC

end
end

section

set_option autoImplicit false

open GlobalTheory GlobalTheory.PDivGroup
open scoped TensorProduct

namespace GlobalTheory.PDiv

theorem exists_aug_dUnit_eq {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A] (w : Cot R A) :
    ∃ a : A, Coalgebra.counit (R := R) a = 0 ∧ dUnit (R := R) a = w := by
  obtain ⟨x, rfl⟩ := (augIdeal R A).toCotangent_surjective w
  exact ⟨x, x.2, AugCot.d_coe _ x⟩

theorem exists_aug_lift_dUnit_eq {R A C : Type*} [CommRing R] [CommRing A] [CommRing C] [Bialgebra R A]
    [Bialgebra R C] {f : C →ₐc[R] A} (hf : Function.Surjective f) (a : A)
    (ha : Coalgebra.counit (R := R) a = 0) (w : Cot R C) (hw : cotMap f w = dUnit (R := R) a) :
    ∃ c : C, Coalgebra.counit (R := R) c = 0 ∧ dUnit (R := R) c = w ∧ f c = a := by
  obtain ⟨y, hy, rfl⟩ := exists_aug_dUnit_eq w
  have h1 : dUnit (R := R) (f y - a) = 0 := by
    rw [dUnit, map_sub, sub_eq_zero]
    exact (cotMap_d f y).symm.trans hw
  have h2 : Bialgebra.counitAlgHom R A (f y - a) = 0 := by simp [hy, ha]
  rw [dUnit, AugCot.d_eq_zero_iff, h2, map_zero, sub_zero] at h1
  have h3 : f y - a ∈ Ideal.map (f : C →ₐ[R] A) (augIdeal R C ^ 2) := by
    rw [Ideal.map_pow]
    have := kerIdeal_of_surjective hf
    rw [kerIdeal] at this
    rw [this]
    exact h1
  obtain ⟨z, hz, hfz⟩ := (Ideal.mem_map_iff_of_surjective (f : C →ₐ[R] A) hf).1 h3
  have hz0 : Bialgebra.counitAlgHom R C z = 0 := Ideal.pow_le_self two_ne_zero hz
  have hz1 : Coalgebra.counit (R := R) z = 0 := hz0
  refine ⟨y - z, by rw [map_sub, hy, hz1, sub_zero], ?_, ?_⟩
  · rw [dUnit, map_sub, (AugCot.d_eq_zero_iff _ z).2 (by rw [hz0, map_zero, sub_zero]; exact hz), sub_zero]
  · have : f z = f y - a := hfz
    rw [map_sub, this, sub_sub_cancel]

theorem exists_compatible_dUnit_eq {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) (w : G.omega) :
    ∃ x : ∀ n, G.A n, (∀ n, Coalgebra.counit (R := O) (x n) = 0) ∧ (∀ n, G.res n (x (n + 1)) = x n) ∧
      ∀ n, dUnit (R := O) (x n) = w.1 n := by
  obtain ⟨a, ha⟩ := exists_aug_dUnit_eq (w.1 0)
  have step : ∀ (n : ℕ) (a : {a : G.A n // Coalgebra.counit (R := O) a = 0 ∧ dUnit (R := O) a = w.1 n}),
      ∃ c : {a : G.A (n + 1) // Coalgebra.counit (R := O) a = 0 ∧ dUnit (R := O) a = w.1 (n + 1)},
        G.res n c.1 = a.1 := fun n a => by
    obtain ⟨c, h1, h2, h3⟩ := exists_aug_lift_dUnit_eq (G.res_surjective n) a.1 a.2.1 (w.1 (n + 1))
      ((w.2 n).trans a.2.2.symm)
    exact ⟨⟨c, h1, h2⟩, h3⟩
  choose s hs using step
  let x : ∀ n, {a : G.A n // Coalgebra.counit (R := O) a = 0 ∧ dUnit (R := O) a = w.1 n} :=
    fun n => Nat.rec ⟨a, ha⟩ s n
  exact ⟨fun n => (x n).1, fun n => (x n).2.1, fun n => hs n (x n), fun n => (x n).2.2⟩

theorem exists_compatible_coordinates (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O) (G : PDivGroup p O) :
    ∃ (d : ℕ) (x : ∀ n, Fin d → G.A n), (∀ n i, Coalgebra.counit (R := O) (x n i) = 0) ∧
      (∀ n i, G.res n (x (n + 1) i) = x n i) ∧
      (∀ n, Submodule.span O (Set.range fun i => PDiv.dUnit (R := O) (x n i)) = ⊤) ∧
      ∀ n, ∃ l : Fin d → (PDiv.Cot O (G.A n) →ₗ[O] O ⧸ Ideal.span {(p : O) ^ n}),
        ∀ i j, l i (PDiv.dUnit (R := O) (x n j)) = if i = j then 1 else 0 := by
  have : ValuationRing O := ValuationRing.of_integers v hv
  obtain ⟨h1, h2⟩ := omega_finite_projective p C v O hv G
  have : Module.Free O G.omega := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis O G.omega
  choose x hx0 hx1 hx2 using fun i => exists_compatible_dUnit_eq G (b i)
  refine ⟨_, fun n i => x i n, fun n i => hx0 i n, fun n i => hx1 i n, fun n => ?_, fun n => ?_⟩
  · have : (fun i => dUnit (R := O) (x i n)) = G.omegaLevel n ∘ b := funext fun i => hx2 i n
    rw [this, Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      LinearMap.range_eq_top.2 (G.omegaLevel_surjective n)]
  · have hker : ∀ i, LinearMap.ker (G.omegaLevel n) ≤
        LinearMap.ker ((Ideal.span {(p : O) ^ n}).mkQ ∘ₗ b.coord i) := fun i w hw => by
      obtain ⟨u, rfl⟩ := (G.omega_val_eq_zero_iff n w).1 hw
      rw [LinearMap.mem_ker, LinearMap.comp_apply, map_smul, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    refine ⟨fun i => ((LinearMap.ker (G.omegaLevel n)).liftQ _ (hker i)) ∘ₗ
      ((G.omegaLevel n).quotKerEquivOfSurjective (G.omegaLevel_surjective n)).symm.toLinearMap, fun i j => ?_⟩
    have h : ((G.omegaLevel n).quotKerEquivOfSurjective (G.omegaLevel_surjective n)).symm (dUnit (R := O) (x j n)) =
        Submodule.Quotient.mk (b j) := by
      rw [LinearEquiv.symm_apply_eq, hx2]
      rfl
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h, Submodule.liftQ_apply, LinearMap.comp_apply,
      Module.Basis.coord_apply, b.repr_self, Finsupp.single_apply]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij.symm]; rfl
    · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]

end GlobalTheory.PDiv
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.ConjCoordToric

theorem lamF_mul {E : Type} [Field E] [NumberField E] (s : ℕ) (χ : HChar E) (y y' : (Af E)ˣ) :
    lamF s χ (y * y') = lamF s χ y * lamF s χ y' := by
  unfold lamF
  rw [map_mul, Units.val_mul, IdeleModule.modF_mul, mul_pow]
  push_cast
  ring

theorem coordIn_eq_mul {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (Ω T : ℂ) :
    coordIn E d s κ Ω T = coordIn E d s κ Ω 1 * T := by
  unfold GlobalTheory.ToricTransport.coordIn
  ring

theorem exists_latSum {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E))
    (h : ∀ q : PicO c, ∃ S, IsLatSum φ (2 * s) κ (lattice c q.out) S) (y : (Af E)ˣ) :
    ∃ S, IsLatSum φ (2 * s) κ (lattice c y) S := by
  classical
  obtain ⟨q, hq⟩ : ∃ q : PicO c, q = QuotientGroup.mk y := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ := h q
  have hq' : (QuotientGroup.mk q.out : PicO c) = QuotientGroup.mk y := by rw [QuotientGroup.out_eq', hq]
  obtain ⟨a, ⟨α, rfl⟩, u, hu, hau⟩ := Subgroup.mem_sup.1 (QuotientGroup.eq.1 hq')
  have hy : y = Units.map (algebraMap E (Af E)).toMonoidHom α * q.out * u := by
    have : y = q.out * (Units.map (algebraMap E (Af E)).toMonoidHom α * u) := by rw [hau]; group
    rw [this]
    ac_rfl
  rw [hy, GlobalTheory.ClassInv.lattice_princ_mul_unit _ α hu]
  exact ⟨_, (GlobalTheory.HomothetyLatSum.homothety E I φ hφ s _ κ α S hS).1⟩

theorem conj_coordIn_toric : ∀ (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ κ' : I → ℕ) (hκ' : IsConjWt φ g κ κ') (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ χ' : HChar E) (T T' : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T) (hV' : IsConjSum φ s κ' 𝔣 Q g χ χ' T'), g (coordIn E d s κ Ω₀ T) = coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ * T') := by
  intro hC K _ _ d δ ι h2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E _ _ _ _ I _ φ hE hφ hφK s hs κ κ' hκ' 𝔣 h𝔣 Q χ χ' T T' hV hV'
  classical
  obtain ⟨hAux, hVal, -, S, hS, rfl⟩ := hV
  obtain ⟨⟨hlam, hInf'⟩, hfin', S'', hS'', rfl⟩ := hV'
  haveI : Fintype (PicO (condQ 𝔣 Q)) := Fintype.ofFinite _
  have hunit' : ∀ u ∈ hatOUnits (condQ 𝔣 Q), finPart χ' u = 1 := by
    intro u hu
    have h1 : lamF s χ' u = 1 := by
      rw [hlam]
      unfold lamF
      rw [GlobalTheory.ClassInv.finPart_unit hVal hu, ObjModel.modF_unit hu]
      simp
    unfold lamF at h1
    rw [ObjModel.modF_unit hu] at h1
    simp at h1
    exact h1
  have hex : ∀ q : PicO (condQ 𝔣 Q), ∃ S', IsLatSum φ (2 * s) κ' (lattice (condQ 𝔣 Q) (q.out * (upIdele K E t)⁻¹)) S' :=
    fun q => exists_latSum hφ s κ' (condQ 𝔣 Q) (fun q => ⟨S'' q, hS'' q⟩) _
  choose S' hS' using hex
  have hLC : ∀ q : PicO (condQ 𝔣 Q), g (coordIn E d s κ Ω₀ 1 * S q 0) =
      coordIn E d s κ Ω₁ 1 * ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * S' q 0) := fun q => by
    rw [← coordIn_eq_mul, ← coordIn_eq_mul]
    exact hC K d δ ι h2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E I φ s 𝔣 Q ⟨hE, hφ, hφK, hs, h𝔣, hAux⟩ κ κ' hκ' q.out (S q) (S' q)
      (hS q) (hS' q)
  have hCI : ∀ q : PicO (condQ 𝔣 Q), (lamF s χ' (q.out * (upIdele K E t)⁻¹))⁻¹ * S' q 0 =
      (lamF s χ' (q * QuotientGroup.mk (upIdele K E t)⁻¹).out)⁻¹ * S'' (q * QuotientGroup.mk (upIdele K E t)⁻¹) 0 := by
    intro q
    refine GlobalTheory.ClassInvAny.classInv_of_unit_trivial E I φ hφ s κ' (condQ 𝔣 Q) χ' hInf' hunit' _ _ (S' q) (S'' _) ?_
      (hS' q) (hS'' _)
    rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
  have hsum : ∀ (ψ : HChar E) (R : PicO (condQ 𝔣 Q) → ℂ → ℂ),
      (∑ᶠ q : PicO (condQ 𝔣 Q), ((finPart ψ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * R q 0) =
        ∑ q, (lamF s ψ q.out)⁻¹ * R q 0 := fun ψ R => by
    rw [finsum_eq_sum_of_fintype]
    rfl
  rw [hsum, hsum, coordIn_eq_mul (E := E) d s κ Ω₀, coordIn_eq_mul (E := E) d s κ Ω₁]
  calc g (coordIn E d s κ Ω₀ 1 * ∑ q, (lamF s χ q.out)⁻¹ * S q 0)
      = ∑ q, (g (lamF s χ q.out))⁻¹ * g (coordIn E d s κ Ω₀ 1 * S q 0) := by

        rw [Finset.mul_sum, map_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [show coordIn E d s κ Ω₀ 1 * ((lamF s χ q.out)⁻¹ * S q 0) =
          (lamF s χ q.out)⁻¹ * (coordIn E d s κ Ω₀ 1 * S q 0) by ring, map_mul, map_inv₀]
    _ = ∑ q, (lamF s χ' q.out)⁻¹ * (coordIn E d s κ Ω₁ 1 * ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * S' q 0)) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hlam, hLC]
    _ = ∑ q, coordIn E d s κ Ω₁ 1 * (((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ *
          ((lamF s χ' (q * QuotientGroup.mk (upIdele K E t)⁻¹).out)⁻¹ * S'' (q * QuotientGroup.mk (upIdele K E t)⁻¹) 0) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← hCI q]
        have hm : lamF s χ' q.out = lamF s χ' (q.out * (upIdele K E t)⁻¹) * lamF s χ' (upIdele K E t) := by
          rw [← lamF_mul, inv_mul_cancel_right]
        rw [hm, mul_inv]
        ring
    _ = coordIn E d s κ Ω₁ 1 * (((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ *
          ∑ q, (lamF s χ' q.out)⁻¹ * S'' q 0 := by
        rw [Finset.mul_sum]
        exact Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk (upIdele K E t)⁻¹ : PicO (condQ 𝔣 Q))) _ _ fun q => rfl
    _ = _ := by ring

end GlobalTheory.ConjCoordToric
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

theorem _root_.GlobalTheory.T.exists_algebraic_of_rational_valuation : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ q : ℚ, ∃ c : ℂ, c ≠ 0 ∧ Sz l lam (-(q : ℝ)) c ∧ Sz l lam q c⁻¹ := by
  first | exact @GlobalTheory.QFam.exists_sz_scale | exact GlobalTheory.QFam.exists_sz_scale | (intros; apply GlobalTheory.QFam.exists_sz_scale <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

theorem _root_.GlobalTheory.T.exists_integrallyClosed_padicIntegralSubring : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∃ R : Subring ℂ, (∀ x, x ∈ R ↔ Sz l lam 0 x) ∧ ∀ x, IsIntegral R x → x ∈ R := by
  first | exact @GlobalTheory.QFam.exists_szRing | exact GlobalTheory.QFam.exists_szRing | (intros; apply GlobalTheory.QFam.exists_szRing <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.degW_blattner_le_of_blattnerCone : ∀ (p q : ℕ) (M : GKMod p q) (lam : Ix p q → ℚ) (c θ : ℚ), ConeTypes M lam → (∀ a, (θ < lam a → 0 ≤ shiftNu c (blattner lam) a) ∧ (lam a ≤ θ → shiftNu c (blattner lam) a ≤ 0)) → ∀ μ v, IsHW M.act μ v → degW c (blattner lam) ≤ degW c μ := by
  first | exact @GlobalTheory.FlowLemma.degW_blattner_le | exact GlobalTheory.FlowLemma.degW_blattner_le | (intros; apply GlobalTheory.FlowLemma.degW_blattner_le <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fock_norm_bounds_mul_X_pderiv : ∀ (σ : Type) [DecidableEq σ] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : MvPolynomial σ ℂ →ₗ[ℂ] H), IsFockIP ι → ∀ (i : σ) (d : ℕ) (P : MvPolynomial σ ℂ), P.totalDegree ≤ d → ‖ι (X i * P)‖ ^ 2 ≤ ((d : ℝ) + 1) * ‖ι P‖ ^ 2 ∧ ‖ι (pderiv i P)‖ ^ 2 ≤ (d : ℝ) * ‖ι P‖ ^ 2 := by
  first | exact @GlobalTheory.FockNormBound.fock_norm_bounds | exact GlobalTheory.FockNormBound.fock_norm_bounds | (intros; apply GlobalTheory.FockNormBound.fock_norm_bounds <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fock_dualPair_swap_symmetry : ∀ (p q r s : ℕ), (∀ (Z : Mat p q) (P : Pol p q r s), rename Prod.swap (fockAct1 p q r s Z P) = fockAct2 r s p q Z (rename Prod.swap P)) ∧ (∀ (Z : Mat r s) (P : Pol p q r s), rename Prod.swap (fockAct2 p q r s Z P) = fockAct1 r s p q Z (rename Prod.swap P)) ∧ (∀ P : Pol p q r s, (P ∈ harm1 p q r s ↔ rename Prod.swap P ∈ harm2 r s p q) ∧ (P ∈ harm2 p q r s ↔ rename Prod.swap P ∈ harm1 r s p q)) := by
  first | exact @GlobalTheory.FockSwap.swap_symmetry | exact GlobalTheory.FockSwap.swap_symmetry | (intros; apply GlobalTheory.FockSwap.swap_symmetry <;> assumption)
end

section

noncomputable section
namespace GlobalTheory.FockAdj
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.FockDeg MvPolynomial Matrix

variable {p q r s : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_pderiv {σ : Type} [DecidableEq σ] {ι : MvPolynomial σ ℂ →ₗ[ℂ] H} (hι : IsFockIP ι)
    (i : σ) (P Q : MvPolynomial σ ℂ) :
    inner ℂ (ι (pderiv i P)) (ι Q) = inner ℂ (ι P) (ι (X i * Q)) := by
  rw [← inner_conj_symm, ← inner_X_mul hι, inner_conj_symm]

theorem inner_raiB {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (raiB l P)) (ι Q) = (if linePos l then 1 else -1) * inner ℂ (ι P) (ι (lowB l Q)) := by
  cases hl : linePos l
  · simp only [raiB, lowB, hl, Bool.false_eq_true, if_false]
    show inner ℂ (ι (-pderiv l P)) (ι Q) = -1 * inner ℂ (ι P) (ι (X l * Q))
    rw [map_neg, inner_neg_left, inner_pderiv hι, neg_one_mul]
  · simp only [raiB, lowB, hl, if_true]
    show inner ℂ (ι (X l * P)) (ι Q) = 1 * inner ℂ (ι P) (ι (pderiv l Q))
    rw [inner_X_mul hι, one_mul]

theorem inner_lowB {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (lowB l P)) (ι Q) = (if linePos l then 1 else -1) * inner ℂ (ι P) (ι (raiB l Q)) := by
  cases hl : linePos l
  · simp only [raiB, lowB, hl, Bool.false_eq_true, if_false]
    show inner ℂ (ι (X l * P)) (ι Q) = -1 * inner ℂ (ι P) (ι (-pderiv l Q))
    rw [map_neg, inner_neg_right, inner_X_mul hι, neg_one_mul, neg_neg]
  · simp only [raiB, lowB, hl, if_true]
    show inner ℂ (ι (pderiv l P)) (ι Q) = 1 * inner ℂ (ι P) (ι (X l * Q))
    rw [inner_pderiv hι, one_mul]

theorem inner_omE {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l l' : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (omE l l' P)) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (omE l' l Q)) := by
  have h1 : inner ℂ (ι (raiB l (lowB l' P))) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (raiB l' (lowB l Q))) := by
    rw [inner_raiB hι, inner_lowB hι, ← mul_assoc]
    congr 1
    cases linePos l <;> cases linePos l' <;> simp
  unfold omE
  simp only [LinearMap.add_apply, Module.End.mul_apply, map_add (f := _), inner_add_left, inner_add_right,
    mul_add, h1]
  congr 1
  by_cases h : l = l'
  · subst h
    simp [inner_smul_left, inner_smul_right, map_ofNat]
  · simp [h, Ne.symm h]

theorem inner_omAct {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι)
    (M N : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (h : ∀ l l', N l' l = (if linePos l = linePos l' then 1 else -1) * star (M l l'))
    (P Q : Pol p q r s) :
    inner ℂ (ι (omAct p q r s M P)) (ι Q) = inner ℂ (ι P) (ι (omAct p q r s N Q)) := by

  simp only [omAct_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, sum_inner,
  inner_sum, inner_smul_left, inner_smul_right]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  rw [inner_omE hι, h, starRingEnd_apply]
  ring

theorem adjZ_apply (Z : Mat p q) (a b : Ix p q) :
    adjZ Z a b = (if sameBlock b a then 1 else -1) * star (Z b a) := by
  have hJ : Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [adjZ, hJ, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock]

theorem fock_adjoints : ∀ (p q r s : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : Pol p q r s →ₗ[ℂ] H), IsFockIP ι →
    (∀ (l l' : Ln p q r s) (P Q : Pol p q r s), inner ℂ (ι (omE l l' P)) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (omE l' l Q))) ∧
    (∀ (Z : Mat p q) (P Q : Pol p q r s), inner ℂ (ι (fockAct1 p q r s Z P)) (ι Q) =
      inner ℂ (ι P) (ι (fockAct1 p q r s (adjZ Z) Q))) ∧
    (∀ (Z : Mat r s) (P Q : Pol p q r s), inner ℂ (ι (fockAct2 p q r s Z P)) (ι Q) =
      inner ℂ (ι P) (ι (fockAct2 p q r s (adjZ Z) Q))) := by
  intro p q r s H _ _ ι hι
  refine ⟨inner_omE hι, fun Z P Q => ?_, fun Z P Q => ?_⟩
  · rw [fockAct1_eq, fockAct1_eq]
    refine inner_omAct hι _ _ ?_ P Q
    rintro ⟨a, c⟩ ⟨b, d⟩
    by_cases e : c = d
    · subst e
      simp [kr1, adjZ_apply, linePos_eq_iff_fst]
    · simp [kr1, e, Ne.symm e]
  · rw [fockAct2_eq, fockAct2_eq]
    refine inner_omAct hι _ _ ?_ P Q
    rintro ⟨a, c⟩ ⟨b, d⟩
    by_cases e : a = b
    · subst e
      simp [kr2, adjZ_apply, linePos_eq_iff_snd]
    · simp [kr2, e, Ne.symm e]

end GlobalTheory.FockAdj
end
end

section

open IsLocalRing GlobalTheory.UT

theorem _root_.GlobalTheory.T.adicSum_maximalIdeal_unique_noetherian_local : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (Ix : Type) (x : Ix → R) (s s' : R), SumI (maximalIdeal R) x s → SumI (maximalIdeal R) x s' → s = s' := by
  first | exact @GlobalTheory.Poinc.sumI_maximalIdeal_unique | exact GlobalTheory.Poinc.sumI_maximalIdeal_unique | (intros; apply GlobalTheory.Poinc.sumI_maximalIdeal_unique <;> assumption)
end
