module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle004
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.RingTheory.RingHom.Unramified
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle008
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsZeroFreeSchOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle013
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle026
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
public import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Etale.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1.Base

variable (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

theorem mapDR_ιMulti (n : ℕ) (v : Fin n → Ω[K⁄k]) :
    mapDR k K L (ExteriorAlgebra.ιMulti K n v) =
      ExteriorAlgebra.ιMulti L n (fun i => KaehlerDifferential.map k k K L (v i)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  exact congrArg (fun l => List.prod l) (congrArg List.ofFn (funext fun i => by
    show mapDR k K L (ExteriorAlgebra.ι K (v i)) = _
    rw [mapDR, ExteriorAlgebra.lift_ι_apply]; rfl))


variable {k K L} in
theorem mapDR_basis {I : Type} [LinearOrder I] (bK : Module.Basis I K Ω[K⁄k]) (bL : Module.Basis I L Ω[L⁄k])
    (h : ∀ i, bL i = KaehlerDifferential.map k k K L (bK i)) (s : Finset I) :
    mapDR k K L (bK.ExteriorAlgebra s) = bL.ExteriorAlgebra s := by
  rw [ExteriorAlgebra.basis_apply_ofCard _ rfl, ExteriorAlgebra.basis_apply_ofCard _ rfl,
    ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_family, mapDR_ιMulti]
  exact congrArg _ (funext fun i => (h _).symm)


variable {k K L} in
theorem repr_mapDR {I : Type} [LinearOrder I] (bK : Module.Basis I K Ω[K⁄k]) (bL : Module.Basis I L Ω[L⁄k])
    (h : ∀ i, bL i = KaehlerDifferential.map k k K L (bK i)) (ω : DR k K) (s : Finset I) :
    bL.ExteriorAlgebra.repr (mapDR k K L ω) s = algebraMap K L (bK.ExteriorAlgebra.repr ω s) := by
  have : ((bL.ExteriorAlgebra.coord s).restrictScalars K ∘ₗ (mapDR k K L).toLinearMap) =
      Algebra.linearMap K L ∘ₗ bK.ExteriorAlgebra.coord s := by
    refine bK.ExteriorAlgebra.ext fun t => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, mapDR_basis bK bL h,
      LinearMap.coe_restrictScalars, Module.Basis.coord_apply, Module.Basis.repr_self, Algebra.linearMap_apply]
    by_cases hts : t = s
    · subst hts; simp
    · simp [Finsupp.single_apply, hts]
  exact congrArg (· ω) this

end GlobalTheory.W1.Base

namespace GlobalTheory.W1.Base

theorem forms_baseChange : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L],
    (∀ y : DR k L, ∃ (m : ℕ) (b : Fin m → L) (ω : Fin m → DR k K), y = ∑ j, b j • mapDR k K L (ω j)) ∧
      ∀ (m : ℕ) (b : Fin m → L) (ω : Fin m → DR k K), LinearIndependent K b →
        ∑ j, b j • mapDR k K L (ω j) = 0 → ∀ j, ω j = 0 := by
  intro k K L _ _ _ _ _ _ _ _ _
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let I := Module.Basis.ofVectorSpaceIndex K Ω[K⁄k]
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let bK : Module.Basis I K Ω[K⁄k] := Module.Basis.ofVectorSpace K Ω[K⁄k]
  let bL : Module.Basis I L Ω[L⁄k] := (bK.baseChange L).map (tensorKaehlerEquivOfFormallyEtale k K L)
  have h : ∀ i, bL i = KaehlerDifferential.map k k K L (bK i) := fun i => by
    simp only [bL, Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply,
      mapBaseChange_tmul, one_smul]
  set BK := bK.ExteriorAlgebra
  set BL := bL.ExteriorAlgebra
  refine ⟨fun y => ?_, fun m b ω hb hsum j => ?_⟩
  · set S := (BL.repr y).support
    refine ⟨S.card, fun j => BL.repr y (S.equivFin.symm j), fun j => BK (S.equivFin.symm j), ?_⟩
    simp only [BK, BL, mapDR_basis bK bL h]
    conv_lhs => rw [← BL.linearCombination_repr y, Finsupp.linearCombination_apply, Finsupp.sum, ← Finset.sum_coe_sort]
    exact (Fintype.sum_equiv S.equivFin _ _ fun _ => by rw [Equiv.symm_apply_apply])
  · have hc : ∀ s, ∀ j, BK.repr (ω j) s = 0 := by
      intro s
      have h0 := congrArg (fun z => BL.repr z s) hsum

      simp only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul,
      map_zero, Finsupp.zero_apply, BK, BL, repr_mapDR bK bL h] at h0
      refine Fintype.linearIndependent_iff.1 hb (fun j => BK.repr (ω j) s) ?_
      simpa [Algebra.smul_def, mul_comm] using h0
    exact BK.repr.injective (Finsupp.ext fun s => by simpa using hc s j)

end GlobalTheory.W1.Base
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.W1

theorem dv_mem_span_of_formallyUnramified : ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) (B' : Subalgebra k L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.FormallyUnramified → ∀ v ∈ B', ∃ (m : ℕ) (b : Fin m → L) (w : Fin m → K), (∀ j, b j ∈ B' ∧ w j ∈ B) ∧ ι1 (D k L v) = ∑ j, b j • mapDR k K L (ι1 (D k K (w j))) := by
  intro k K L _ _ _ _ _ _ _ B B' φ hφ hU v hv
  letI := φ.toAlgebra
  haveI : IsScalarTower k B B' := IsScalarTower.of_algebraMap_eq fun c => by
    apply Subtype.ext
    change algebraMap k L c = ((φ (algebraMap k B c) : B') : L)
    rw [hφ, IsScalarTower.algebraMap_apply k K L]
    rfl
  haveI : Algebra.FormallyUnramified B B' := hU
  have hspan : Submodule.span B' (Set.range fun a : B => KaehlerDifferential.D k B' (φ a)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨y, rfl⟩ :=
      (KaehlerDifferential.exact_mapBaseChange_map k B B' x).mp (Subsingleton.elim _ _)
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | tmul b m =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      refine Submodule.smul_mem _ b ?_
      have hm : m ∈ Submodule.span B (Set.range (KaehlerDifferential.D k B)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        rw [KaehlerDifferential.map_D]
        exact Submodule.subset_span ⟨a, rfl⟩
      | zero => simp
      | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
      | smul a x _ hx =>
        rw [map_smul, ← algebraMap_smul B' a]
        exact Submodule.smul_mem _ _ hx
  have hmem : KaehlerDifferential.D k B' ⟨v, hv⟩ ∈
      Submodule.span B' (Set.range fun a : B => KaehlerDifferential.D k B' (φ a)) := hspan ▸ Submodule.mem_top
  obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.mp hmem
  choose w hw using fun j => (g j).2
  refine ⟨n, fun j => (f j : L), fun j => (w j : K), fun j => ⟨(f j).2, (w j).2⟩, ?_⟩
  have key : KaehlerDifferential.D k L v = ∑ j, (f j : L) • KaehlerDifferential.D k L (algebraMap K L (w j)) := by
    have h := congrArg (KaehlerDifferential.map k k B' L) hsum

    rw [map_sum, KaehlerDifferential.map_D] at h
    refine h.symm.trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ← hw j, KaehlerDifferential.map_D, ← hφ]
    first | rfl | simp [Subalgebra.smul_def]
  have hpull : ∀ a : K, mapDR k K L (ι1 (D k K a)) = ι1 (D k L (algebraMap K L a)) := by
    intro a
    rw [mapDR, ExteriorAlgebra.lift_ι_apply]
    simp [map1]

  simp_rw [hpull, key, map_sum, map_smul]

end GlobalTheory.W1
end
end

section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

namespace GlobalTheory

theorem exists_shift_mod_pow_degOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (θ : 𝓞 E) (D : 𝓞 F), (∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ) → ∀ (m : Ideal (𝓞 F)), m ≠ ⊥ → m ≤ Ideal.span {D} → ∀ (y : 𝓞 E) (N : ℕ), ∃ k : 𝓞 E, k - algebraMap (𝓞 F) (𝓞 E) D * y ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (m ^ N) ∧ ∀ P : HeightOneSpectrum (𝓞 E), ¬ m ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) → k ∈ P.asIdeal → DegOne F P := by
  intro F E _ _ _ _ _ θ D hgen m hm hmD y N
  obtain ⟨u, v, huv⟩ := hgen y
  have hmN : m ^ N ≠ ⊥ := pow_ne_zero N hm
  obtain ⟨a, b, ha, hb, -, hcop⟩ := exists_reps_coprime_outside_modulus (𝓞 F) (m ^ N) u v hmN
  refine ⟨algebraMap (𝓞 F) (𝓞 E) a + algebraMap (𝓞 F) (𝓞 E) b * θ, ?_, ?_⟩
  · rw [huv]
    have e : algebraMap (𝓞 F) (𝓞 E) a + algebraMap (𝓞 F) (𝓞 E) b * θ -
        (algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ) =
        algebraMap (𝓞 F) (𝓞 E) (a - u) + algebraMap (𝓞 F) (𝓞 E) (b - v) * θ := by
      simp only [map_sub]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ ha)
      (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb))
  · intro P hmP hk
    have hPmax : P.asIdeal.IsMaximal := P.isMaximal
    have hpmax : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal
    have hmNp : ¬ m ^ N ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := fun h =>
      hmP (hpmax.isPrime.le_of_pow_le h)
    have hD : algebraMap (𝓞 F) (𝓞 E) D ∉ P.asIdeal := by
      intro h
      apply hmP
      refine hmD.trans ?_
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      exact h
    have hbP : algebraMap (𝓞 F) (𝓞 E) b ∉ P.asIdeal := by
      intro h
      apply hcop _ hpmax hmNp
      refine ⟨?_, Ideal.mem_comap.mpr h⟩
      rw [Ideal.mem_comap]
      have := P.asIdeal.sub_mem hk (P.asIdeal.mul_mem_right θ h)
      simpa using this
    exact residue_degree_one_of_linear_mem (𝓞 F) (𝓞 E) P.asIdeal θ D a b hpmax hgen hD hbP hk
end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite

noncomputable section

namespace GlobalTheory.EtC.Tr

theorem freePresheaf_map_app_freeMk (R : Type) [CommRing R] {P Q : Scheme.{0}ᵒᵖ ⥤ Type} (α : P ⟶ Q) (U : Scheme.{0}ᵒᵖ)
    (x : P.obj U) :
    ConcreteCategory.hom (((GlobalTheory.EtC.freeP R).map α).app U) (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (α.app U x)) :=
  ModuleCat.free_map_apply _ _

theorem freePresheaf_obj_map_freeMk (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ Type) {U V : Scheme.{0}ᵒᵖ} (f : U ⟶ V)
    (x : P.obj U) :
    ConcreteCategory.hom (((GlobalTheory.EtC.freeP R).obj P).map f) (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (P.map f x)) :=
  ModuleCat.free_map_apply _ _

theorem freePresheaf_map_comp_app_freeMk (R : Type) [CommRing R] {P Q : Scheme.{0}ᵒᵖ ⥤ Type}
    {G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (α : P ⟶ Q) (β : (GlobalTheory.EtC.freeP R).obj Q ⟶ G)
    (U : Scheme.{0}ᵒᵖ) (x : P.obj U) :
    ConcreteCategory.hom (((GlobalTheory.EtC.freeP R).map α ≫ β).app U) (ModuleCat.freeMk (ULift.up x)) =
      ConcreteCategory.hom (β.app U) (ModuleCat.freeMk (ULift.up (α.app U x))) :=
  congrArg (ConcreteCategory.hom (β.app U)) (freePresheaf_map_app_freeMk R α U x)

theorem freePresheaf_hom_naturality_freeMk (R : Type) [CommRing R] {P : Scheme.{0}ᵒᵖ ⥤ Type}
    {G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (β : (GlobalTheory.EtC.freeP R).obj P ⟶ G)
    {U V : Scheme.{0}ᵒᵖ} (f : U ⟶ V) (x : P.obj U) :
    ConcreteCategory.hom (G.map f) (ConcreteCategory.hom (β.app U) (ModuleCat.freeMk (ULift.up x))) =
      ConcreteCategory.hom (β.app V) (ModuleCat.freeMk (ULift.up (P.map f x))) := by
  have h := ConcreteCategory.congr_hom (β.naturality f) (ModuleCat.freeMk (ULift.up x))
  exact h.symm.trans (congrArg (ConcreteCategory.hom (β.app V)) (freePresheaf_obj_map_freeMk R P f x))

end GlobalTheory.EtC.Tr

namespace GlobalTheory.EtC.Tr

theorem free_hom_ext_of_covering (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R)
    (φ ψ : GlobalTheory.EtC.Tr.freeSch R S ⟶ F) (T : Sieve S) (hT : T ∈ Scheme.etaleTopology S)
    (h : ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v →
      (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ φ = (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ ψ) : φ = ψ := by
  let adj := sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  apply (adj.homEquiv ((GlobalTheory.EtC.freeP R).obj (yoneda.obj S)) F).injective
  have key : ∀ ⦃W : Scheme.{0}⦄ (v : W ⟶ S), T v →
      ConcreteCategory.hom ((adj.homEquiv _ F φ).app (op W)) (ModuleCat.freeMk (ULift.up v)) =
      ConcreteCategory.hom ((adj.homEquiv _ F ψ).app (op W)) (ModuleCat.freeMk (ULift.up v)) := by
    intro W v hv
    have e : ∀ χ : GlobalTheory.EtC.Tr.freeSch R S ⟶ F,
        adj.homEquiv _ F ((GlobalTheory.EtC.free R).map (yoneda.map v) ≫ χ) =
          (GlobalTheory.EtC.freeP R).map (yoneda.map v) ≫ adj.homEquiv _ F χ := fun χ =>
      adj.homEquiv_naturality_left _ _
    have h' : (GlobalTheory.EtC.freeP R).map (yoneda.map v) ≫ adj.homEquiv _ F φ =
        (GlobalTheory.EtC.freeP R).map (yoneda.map v) ≫ adj.homEquiv _ F ψ := by
      rw [← e φ, ← e ψ]; exact congrArg (adj.homEquiv _ F) (h v hv)
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app h' (op W)) (ModuleCat.freeMk (ULift.up (𝟙 W)))
    rw [freePresheaf_map_comp_app_freeMk, freePresheaf_map_comp_app_freeMk] at h1
    have hv1 : ConcreteCategory.hom ((yoneda.map v).app (op W)) (𝟙 W) = v := Category.id_comp v
    rw [hv1] at h1
    exact h1
  apply NatTrans.ext
  funext U
  apply ModuleCat.free_hom_ext
  rintro ⟨g⟩
  apply Sheaf.isSeparated F U.unop (T.pullback g) (Scheme.etaleTopology.pullback_stable g hT)
  intro W w hw
  have nat : ∀ χ : GlobalTheory.EtC.Tr.freeSch R S ⟶ F,
      ConcreteCategory.hom (F.obj.map w.op) (ConcreteCategory.hom ((adj.homEquiv _ F χ).app U)
        (ModuleCat.freeMk (ULift.up g))) =
        ConcreteCategory.hom ((adj.homEquiv _ F χ).app (op W)) (ModuleCat.freeMk (ULift.up (w ≫ g))) :=
    fun χ => freePresheaf_hom_naturality_freeMk R (adj.homEquiv _ F χ) w.op g
  exact (nat φ).trans ((key (w ≫ g) hw).trans (nat ψ).symm)

end GlobalTheory.EtC.Tr
end
end

section

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published ValuativeRel GlobalTheory.RootEx
open scoped TensorProduct Topology

namespace GlobalTheory.GodementJacquet

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

section Mat

variable {α β : Type} [Fintype α]


open MeasureTheory ValuativeRel in
open scoped TensorProduct Topology in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] in
theorem _root_.GlobalTheory.GodementJacquet.parab_mul_eMat
    (p : _root_.GlobalTheory.SmGL.parab k
      (_root_.GlobalTheory.SmGL.two (_root_.GlobalTheory.SmGL.stdSum (rfl : r + t = r + t)))) :
    (p : GL (Fin (r + t)) k).val * _root_.GlobalTheory.GodementJacquet.eMat k r t =
      _root_.GlobalTheory.GodementJacquet.eMat k r t * (_root_.GlobalTheory.SmGL.leviProj k
        (_root_.GlobalTheory.SmGL.two (_root_.GlobalTheory.SmGL.stdSum (rfl : r + t = r + t))) p false :
          GL (Fin r) k).val := by
  have hE : ∀ (i : Fin (r + t)) (j : Fin r),
      _root_.GlobalTheory.GodementJacquet.eMat k r t i j = if i = Fin.castAdd t j then 1 else 0 := by
    intro i j
    simp [_root_.GlobalTheory.GodementJacquet.eMat, Fin.ext_iff]
  have hlow : ∀ (i : Fin t) (j : Fin r),
      (p : GL (Fin (r + t)) k).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
    intro i j
    have := (_root_.GlobalTheory.SmGL.mem_parab_two k).1 p.2 i j
    simpa [_root_.GlobalTheory.SmGL.stdSum] using this
  have hL : ∀ (i j : Fin r), (_root_.GlobalTheory.SmGL.leviProj k
      (_root_.GlobalTheory.SmGL.two (_root_.GlobalTheory.SmGL.stdSum (rfl : r + t = r + t))) p false :
        GL (Fin r) k).val i j = (p : GL (Fin (r + t)) k).val (Fin.castAdd t i) (Fin.castAdd t j) := by
    intro i j
    rw [_root_.GlobalTheory.SmGL.leviProj_apply]
    rfl
  ext i j
  simp only [Matrix.mul_apply, hE, hL, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [eq_comm]
  · rw [hlow]
    refine (Finset.sum_eq_zero fun x _ => ?_).symm
    rw [if_neg]
    simp only [Fin.ext_iff, Fin.coe_natAdd, Fin.coe_castAdd]
    omega

end Mat

section Coef

variable {σ : Representation ℂ (GL (Fin r) k) V} {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

end Coef

section Law

end Law

section Int

variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

variable (hσ : IsSmooth σ) (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
    (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
include hσ hs hp hu





end Int

section Family

variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}


variable [m.IsMulLeftInvariant] (hσ : IsSmooth σ) (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
    (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
    (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
      Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
      Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)



end Family

section Abstract

variable {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

end Abstract

section Pairing

variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
  [m.IsMulLeftInvariant] [m.IsMulRightInvariant] (hσ : IsSmooth σ)
  (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
  (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
  (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
    Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
    Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)


end Pairing

section NonVanishing

variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
  [m.IsMulLeftInvariant] [m.IsOpenPosMeasure] (hσ : IsSmooth σ)
  (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
  (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
  (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
    Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
    Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)

end NonVanishing

end GlobalTheory.GodementJacquet

end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

theorem _root_.GlobalTheory.T.pulledBackProjCoordinateRatio_overlap_div : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (φ : Z ⟶ PSpace ℂ d) (a i j : Fin (d + 1)), genericPoint Z ∈ φ ⁻¹ᵁ chart d a → genericPoint Z ∈ φ ⁻¹ᵁ chart d i → rat φ a i ≠ 0 ∧ rat φ i j = rat φ a j / rat φ a i := by
  first | (exact @GlobalTheory.PD.XCover.rat_overlap) | (exact GlobalTheory.PD.XCover.rat_overlap) | (intros; apply GlobalTheory.PD.XCover.rat_overlap  <;> assumption)
end
