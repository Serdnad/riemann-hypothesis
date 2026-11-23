module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.DimBasic

theorem dim_image {W T : Type*} [TopologicalSpace W] [TopologicalSpace T] {e : W → T}
    (he : Topology.IsEmbedding e) (S : Set W) :
    topologicalKrullDim (e '' S) = topologicalKrullDim S := by
  have h := topologicalKrullDim_eq_of_isEmbedding (he.comp Topology.IsEmbedding.subtypeVal)
    (Z := e '' S) (by rw [Set.range_comp, Subtype.range_coe])
  exact h

theorem dim_closure_eq_zero_iff {T : Type*} [TopologicalSpace T] [T0Space T] (x : T) :
    topologicalKrullDim (closure ({x} : Set T)) = 0 ↔ IsClosed ({x} : Set T) := by
  constructor
  · intro h
    have hmax := Order.krullDim_nonpos_iff_forall_isMax.1
      (show Order.krullDim (IrreducibleCloseds (closure ({x} : Set T))) ≤ 0 from h.le)
    refine closure_subset_iff_isClosed.1 fun w hw => ?_
    let s : closure ({x} : Set T) := ⟨x, subset_closure rfl⟩
    let t : closure ({x} : Set T) := ⟨w, hw⟩
    have hst : s ⤳ t := Topology.IsInducing.subtypeVal.specializes_iff.1
      (specializes_iff_mem_closure.2 hw)
    let A : IrreducibleCloseds (closure ({x} : Set T)) :=
      ⟨closure {t}, isIrreducible_singleton.closure, isClosed_closure⟩
    let B : IrreducibleCloseds (closure ({x} : Set T)) :=
      ⟨closure {s}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hAB : A ≤ B := specializes_iff_closure_subset.1 hst
    have hBA : B ≤ A := hmax A hAB
    have hts : t ⤳ s := specializes_iff_closure_subset.2 hBA
    have e := (hst.antisymm hts).eq
    exact Set.mem_singleton_iff.2 (congrArg Subtype.val e).symm
  · intro h
    rw [h.closure_eq]
    have : Subsingleton ({x} : Set T) := Set.subsingleton_singleton.coe_sort
    let pt : ({x} : Set T) := ⟨x, rfl⟩
    have : Nonempty (IrreducibleCloseds ({x} : Set T)) :=
      ⟨⟨closure {pt}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    refine le_antisymm (Order.krullDim_nonpos_iff_forall_isMax.2 fun a b _ => ?_) Order.krullDim_nonneg
    intro y _
    have ha : (a : Set ({x} : Set T)) = Set.univ := a.isIrreducible.nonempty.eq_univ
    show y ∈ (a : Set ({x} : Set T))
    rw [ha]; trivial

theorem ringKrullDim_le_one (k : Type) [CommRing k] [Module.Finite ℤ k] : ringKrullDim k ≤ 1 := by
  have : Algebra.IsIntegral ℤ k := inferInstance
  calc ringKrullDim k ≤ ringKrullDim ℤ :=
        Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap ℤ k))
          fun I J h => Ideal.IsIntegral.comap_lt_comap (I := I.asIdeal) (J := J.asIdeal) h
    _ = 1 := IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

theorem dim_pspace_le (k : Type) [CommRing k] [Module.Finite ℤ k] (N : ℕ) :
    topologicalKrullDim (PSpace k N) ≤ (N + 1 : ℕ) := by
  have := IsNoetherianRing.of_finite ℤ k
  have hk := ringKrullDim_le_one k
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart k N x
  refine ⟨_, (ProjSpace.chart k N i).isOpen, hi, ?_⟩
  rw [topologicalKrullDim_eq_of_isEmbedding (ProjSpace.chartι k N i).isOpenEmbedding.isEmbedding
    (congrArg SetLike.coe (ProjSpace.opensRange_chartι k N i))]
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
    (R := MvPolynomial {j // j ≠ i} k)).trans_le ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp
  exact (add_le_add_left hk _).trans_eq (add_comm _ _)

theorem finite_residueField (k : Type) [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}}
    (p : X ⟶ Sp k) (hp : IsProjOver p) {x : X} (hx : IsClosed ({x} : Set X)) :
    Finite (X.residueField x) := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  obtain ⟨N, j, _, hj⟩ := hp
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have hf : IsFinite (X.fromSpecResidueField x ≫ p ≫ spMap (Int.castRingHom k)) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  rw [← Spec.map_preimage (X.fromSpecResidueField x ≫ _), IsFinite.SpecMap_iff,
    RingHom.ext_int (Spec.preimage (X.fromSpecResidueField x ≫ p ≫ spMap (Int.castRingHom k))).hom
      (algebraMap ℤ (X.residueField x)), RingHom.finite_algebraMap] at hf
  obtain ⟨ℓ, _⟩ := CharP.exists (X.residueField x)
  rcases CharP.char_is_prime_or_zero (X.residueField x) ℓ with hℓ | rfl
  · have := Fact.mk hℓ
    let := ZMod.algebra (X.residueField x) ℓ
    have := Module.Finite.of_restrictScalars_finite ℤ (ZMod ℓ) (X.residueField x)
    exact Module.finite_of_finite (ZMod ℓ)
  · have := CharP.charP_to_charZero (X.residueField x)
    exact absurd (isField_of_isIntegral_of_isField (R := ℤ) (S := X.residueField x)
      (RingHom.injective_int _) (Field.toIsField _)) Int.not_isField

theorem hasDim_map_iff {X Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i] (y : Y) (d : ℕ) :
    HasDim (i y) d ↔ HasDim y d := by
  unfold HasDim
  rw [← Set.image_singleton, i.isClosedEmbedding.closure_image_eq,
    dim_image i.isClosedEmbedding.isEmbedding]

theorem hasDim_genericPoint_iff (Y : Scheme.{0}) [IsIntegral Y] (d : ℕ) :
    HasDim (genericPoint Y) d ↔ topologicalKrullDim Y = d := by
  unfold HasDim
  rw [(genericPoint_spec Y).def]
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph]

end GlobalTheory.MixHt.DimBasic

namespace GlobalTheory.MixHt


open DimBasic in
theorem hasDim_basic : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p →
    (∃ m : ℕ, ∀ x : X, ∃ d ≤ m, HasDim x d) ∧
    (∀ (x : X) (d d' : ℕ), HasDim x d → HasDim x d' → d = d') ∧
    (∀ x : X, HasDim x 0 ↔ IsClosed ({x} : Set X)) ∧
    (∀ x : X, IsClosed ({x} : Set X) → Finite (X.residueField x)) ∧
    (∀ (Y : Scheme.{0}) (i : Y ⟶ X) [IsClosedImmersion i] (y : Y) (d : ℕ), HasDim (i y) d ↔ HasDim y d) ∧
    ∀ (Y : Scheme.{0}) [IsIntegral Y] (d : ℕ), HasDim (genericPoint Y) d ↔ topologicalKrullDim Y = d := by
  intro k _ X p h
  have := h.finite
  refine ⟨?_, fun x d d' hd hd' => ?_, fun x => ?_, fun x hx => finite_residueField k p h.isProjOver hx,
    fun Y i _ y d => hasDim_map_iff i y d, fun Y _ d => hasDim_genericPoint_iff Y d⟩
  · obtain ⟨N, j, _, -⟩ := h.isProjOver
    refine ⟨N + 1, fun x => ?_⟩
    have h₁ : topologicalKrullDim (closure ({x} : Set X)) ≤ (N + 1 : ℕ) :=
      (topologicalKrullDim_subspace_le X _).trans
        (j.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans (dim_pspace_le k N))
    let pt : closure ({x} : Set X) := ⟨x, subset_closure rfl⟩
    have : Nonempty (IrreducibleCloseds (closure ({x} : Set X))) :=
      ⟨⟨closure {pt}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have h₂ : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({x} : Set X)) := Order.krullDim_nonneg
    unfold HasDim
    generalize topologicalKrullDim (closure ({x} : Set X)) = a at *
    induction a with
    | bot => exact absurd h₂ (by simp)
    | coe a =>
      induction a with
      | top => exact absurd h₁ (by rw [not_le]; exact WithBot.coe_lt_coe.2 (ENat.coe_lt_top _))
      | coe a => exact ⟨a, by exact_mod_cast h₁, rfl⟩
  · unfold HasDim at hd hd'
    exact_mod_cast hd.symm.trans hd'
  · unfold HasDim
    exact_mod_cast dim_closure_eq_zero_iff x

end GlobalTheory.MixHt
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem archInt_eq_zero_of_isEmpty {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (hq : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) (L M : HermLB q) (e : ℕ)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : L.archInt M e hr = 0 := by
  unfold HermLB.archInt
  refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
  haveI := hq σ
  simp [Weight.chernInt, MeasureTheory.integral_of_isEmpty]

theorem mixArch_eq_zero_of_isEmpty {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (hq : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) {e : ℕ} (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : mixArch L M hr = 0 := by
  unfold mixArch
  simp [archInt_eq_zero_of_isEmpty hq, FibreProj.pol]

theorem mixArch_resArch_eq_zero_of_noCxPts : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), (∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) → ∀ (e : ℕ) (L : Fin e → HermLB q) (M : HermLB q), (∀ (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), mixArch L M hr = 0) ∧ ∀ (t : M.B.Sec) (z : Y), resArch L M t z = 0 := by
  intro k _ Y _ q hq e L M
  refine ⟨fun r hr => mixArch_eq_zero_of_isEmpty hq L M hr, fun t z => ?_⟩
  unfold resArch
  split_ifs with h
  · refine mixArch_eq_zero_of_isEmpty (fun σ => ?_) _ _ _
    exact (Points.PtsOver.map (cloι z) rfl _ : CxPts (cloι z ≫ q) σ → CxPts q σ).isEmpty
  · rfl

end GlobalTheory.MixHt
end

section

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.TensSup

theorem tensAll_sup_le {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (U C : ∀ w, Submodule ℂ (V w)) :
    tensAll (fun w => U w ⊔ C w) ≤ tensAll U ⊔ tensAny C := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  choose u hu c hc huc using fun w => Submodule.mem_sup.1 (hf w)
  have hfe : f = u + c := funext fun w => (huc w).symm
  rw [SetLike.mem_coe, hfe, MultilinearMap.map_add_univ]
  refine Submodule.sum_mem _ fun s _ => ?_
  by_cases hs : s = Finset.univ
  · subst hs
    refine Submodule.mem_sup_left (Submodule.subset_span ⟨u, hu, ?_⟩)
    congr 1
    simp
  · obtain ⟨w, hw⟩ : ∃ w, w ∉ s := by
      by_contra h
      push_neg at h
      exact hs (Finset.eq_univ_of_forall h)
    refine Submodule.mem_sup_right (Submodule.subset_span ⟨s.piecewise u c, ⟨w, ?_⟩, rfl⟩)
    rw [Finset.piecewise_eq_of_notMem _ _ _ hw]
    exact hc w

theorem tensAll_fin {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (U : ∀ w, Submodule ℂ (V w)) (hU : ∀ w, FiniteDimensional ℂ (U w)) :
    FiniteDimensional ℂ (tensAll U) := by
  have : tensAll U ≤ LinearMap.range (PiTensorProduct.map fun w => (U w).subtype) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ fun w => (⟨f w, hf w⟩ : U w), by rw [PiTensorProduct.map_tprod]; rfl⟩
  exact Submodule.finiteDimensional_of_le this

theorem tensAll_span_le {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (v : ∀ w, V w) :
    tensAll (fun w => Submodule.span ℂ {v w}) ≤ Submodule.span ℂ {PiTensorProduct.tprod ℂ v} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  choose a ha using fun w => Submodule.mem_span_singleton.1 (hf w)
  have hfe : f = fun w => a w • v w := funext fun w => (ha w).symm
  rw [SetLike.mem_coe, hfe, MultilinearMap.map_smul_univ]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem main : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)],
    ∀ U C : ∀ w, Submodule ℂ (V w), tensAll (fun w => U w ⊔ C w) ≤ tensAll U ⊔ tensAny C ∧
      ((∀ w, FiniteDimensional ℂ (U w)) → FiniteDimensional ℂ (tensAll U)) ∧
      ∀ v : ∀ w, V w, tensAll (fun w => Submodule.span ℂ {v w}) ≤ Submodule.span ℂ {PiTensorProduct.tprod ℂ v} := by
  intro T _ _ V _ _ U C
  exact ⟨tensAll_sup_le U C, tensAll_fin U, tensAll_span_le⟩

end GlobalTheory.HoweR.TensSup
end
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem unitOn_map : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M')
    (f : M →ₗ[ℂ] M') (U : Submodule ℂ M), (∀ a b, s a = s b → ∀ x ∈ U, f (F a b x) = F' a b (f x)) →
    UnitOn s F U → UnitOn s F' (U.map f) := by
  intro ι M _ _ _ _ s F M' _ _ F' f U hF hU
  obtain ⟨hfd, hst, ip, hherm, hpos, hadj⟩ := hU
  let K : Submodule ℂ M := U ⊓ LinearMap.ker f
  have hKU : ∀ k ∈ K, k ∈ U := fun k hk => (Submodule.mem_inf.mp hk).1
  have hKf : ∀ k ∈ K, f k = 0 := fun k hk => LinearMap.mem_ker.mp (Submodule.mem_inf.mp hk).2
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le (inf_le_left : K ≤ U)
  let n := Module.finrank ℂ K
  let b := Module.finBasis ℂ K
  let ψ : M →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => ip (b i : M))
  let U1 : Submodule ℂ M := U ⊓ LinearMap.ker ψ
  have hU1U : ∀ w ∈ U1, w ∈ U := fun w hw => (Submodule.mem_inf.mp hw).1
  have hA : ∀ w ∈ U1, ∀ k ∈ K, ip k w = 0 := by
    intro w hw k hk
    have hw' : ∀ i, ip (b i : M) w = 0 := fun i => by
      have := congrFun (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hw).2) i
      simpa [ψ] using this
    have h0 : ((ip.flip w).comp K.subtype) = 0 := b.ext (fun i => by simpa using hw' i)
    have := LinearMap.congr_fun h0 ⟨k, hk⟩
    simpa using this
  have hA' : ∀ w ∈ U1, ∀ k ∈ K, ip w k = 0 := by
    intro w hw k hk
    have := hherm k (hKU k hk) w (hU1U w hw)
    rw [hA w hw k hk, star_zero] at this
    exact this.symm
  have hinj : Function.Injective (ψ.comp K.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro k hk
    have hk1 : (k : M) ∈ U1 := Submodule.mem_inf.mpr ⟨hKU k k.2, LinearMap.mem_ker.mpr (by simpa using hk)⟩
    have h0 := hA _ hk1 _ k.2
    by_contra hne
    have hne' : (k : M) ≠ 0 := fun h => hne (Subtype.ext h)
    have := hpos _ (hKU k k.2) hne'
    rw [h0] at this
    simp at this
  have hsurj : Function.Surjective (ψ.comp K.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [n])).mp hinj
  have hdec : ∀ u ∈ U, ∃ k ∈ K, u - k ∈ U1 := by
    intro u hu
    obtain ⟨k, hk⟩ := hsurj (ψ u)
    refine ⟨k, k.2, Submodule.mem_inf.mpr ⟨U.sub_mem hu (hKU k k.2), LinearMap.mem_ker.mpr ?_⟩⟩
    rw [map_sub]
    exact sub_eq_zero.mpr (by simpa using hk.symm)
  have hinj1 : LinearMap.ker (f.comp U1.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hwK : (w : M) ∈ K := Submodule.mem_inf.mpr ⟨hU1U w w.2, LinearMap.mem_ker.mpr (by simpa using hw)⟩
    have h0 := hA _ w.2 _ hwK
    by_contra hne
    have hne' : (w : M) ≠ 0 := fun h => hne (Subtype.ext h)
    have := hpos _ (hU1U w w.2) hne'
    rw [h0] at this
    simp at this
  obtain ⟨h, hh⟩ := LinearMap.exists_leftInverse_of_injective (f.comp U1.subtype) hinj1
  let g : M' →ₗ[ℂ] M := U1.subtype.comp h
  have hg : ∀ w ∈ U1, g (f w) = w := by
    intro w hw
    have := congrArg Subtype.val (LinearMap.congr_fun hh ⟨w, hw⟩)
    simpa [g] using this
  have hkey : ∀ u ∈ U, g (f u) ∈ U1 ∧ u - g (f u) ∈ K := by
    intro u hu
    obtain ⟨k, hk, hw⟩ := hdec u hu
    have hfu : f u = f (u - k) := by rw [map_sub, hKf k hk, sub_zero]
    rw [hfu, hg _ hw, sub_sub_cancel]
    exact ⟨hw, hk⟩
  have hgU1 : ∀ x ∈ U.map f, g x ∈ U1 := by
    rintro x ⟨u, hu, rfl⟩
    exact (hkey u hu).1
  have hfg : ∀ x ∈ U.map f, f (g x) = x := by
    rintro x ⟨u, hu, rfl⟩
    have := hKf _ (hkey u hu).2
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  haveI := hfd
  refine ⟨inferInstance, ?_, (ip.comp g).compl₂ g, ?_, ?_, ?_⟩
  · rintro a b hab _ ⟨u, hu, rfl⟩
    exact ⟨F a b u, hst a b hab u hu, hF a b hab u hu⟩
  · intro x hx y hy
    exact hherm _ (hU1U _ (hgU1 x hx)) _ (hU1U _ (hgU1 y hy))
  · intro x hx hne
    apply hpos _ (hU1U _ (hgU1 x hx))
    intro h0
    apply hne
    rw [← hfg x hx]
    change f (g x) = 0
    rw [h0, map_zero]
  · intro a b hab x hx y hy
    have hu0 := hgU1 x hx
    have hv0 := hgU1 y hy
    have e1 : F' a b x = f (F a b (g x)) := by rw [hF a b hab _ (hU1U _ hu0), hfg x hx]
    have e2 : F' b a y = f (F b a (g y)) := by rw [hF b a hab.symm _ (hU1U _ hv0), hfg y hy]
    change ip (g (F' a b x)) (g y) = ip (g x) (g (F' b a y))
    rw [e1, e2]
    have hk1 := (hkey _ (hst a b hab _ (hU1U _ hu0))).2
    have hk2 := (hkey _ (hst b a hab.symm _ (hU1U _ hv0))).2
    have l1 : ip (g (f (F a b (g x)))) (g y) = ip (F a b (g x)) (g y) := by
      have := hA (g y) hv0 _ hk1
      rw [map_sub, LinearMap.sub_apply] at this
      exact (sub_eq_zero.mp this).symm
    have l2 : ip (g x) (g (f (F b a (g y)))) = ip (g x) (F b a (g y)) := by
      have := hA' (g x) hu0 _ hk2
      rw [map_sub] at this
      exact (sub_eq_zero.mp this).symm
    rw [l1, l2]
    exact hadj a b hab _ (hU1U _ hu0) _ (hU1U _ hv0)

end GlobalTheory.HoweR
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem cas_mul_comm_of_block : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), IsGl F → ∀ a b, s a = s b → cas s F * F a b = F a b * cas s F := by
  intro ι M _ _ _ _ s F hF a b hab
  rw [← sub_eq_zero]
  have key : ∀ c d, F c d * F d c * F a b - F a b * (F c d * F d c) =
      ((if c = a then F c d * F d b else 0) - (if b = d then F c d * F a c else 0)) +
      ((if d = a then F c b * F d c else 0) - (if b = c then F a d * F d c else 0)) := by
    intro c d
    have e : F c d * F d c * F a b - F a b * (F c d * F d c) =
        F c d * (F d c * F a b - F a b * F d c) + (F c d * F a b - F a b * F c d) * F d c := by noncomm_ring
    rw [e, hF d c a b, hF c d a b]
    simp only [mul_sub, sub_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  have h0 : cas s F * F a b - F a b * cas s F = ∑ c, ∑ d, if s c = s d then
      (((if c = a then F c d * F d b else 0) - (if b = d then F c d * F a c else 0)) +
      ((if d = a then F c b * F d c else 0) - (if b = c then F a d * F d c else 0))) else 0 := by
    simp only [cas, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases h : s c = s d
    · simp only [h, if_true]; exact key c d
    · simp only [h, if_false, zero_mul, mul_zero, sub_self]
  have h1 : (∑ c, ∑ d, if s c = s d then (if c = a then F c d * F d b else 0) else 0) =
      ∑ d, if s a = s d then F a d * F d b else 0 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [hc]
    · simp
  have h4 : (∑ c, ∑ d, if s c = s d then (if b = c then F a d * F d c else 0) else 0) =
      ∑ d, if s a = s d then F a d * F d b else 0 := by
    rw [Finset.sum_eq_single b]
    · simp [hab]
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  have h2 : (∑ c, ∑ d, if s c = s d then (if b = d then F c d * F a c else 0) else 0) =
      ∑ c, if s c = s a then F c b * F a c else 0 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single b]
    · simp [hab]
    · intro d _ hd; simp [Ne.symm hd]
    · simp
  have h3 : (∑ c, ∑ d, if s c = s d then (if d = a then F c b * F d c else 0) else 0) =
      ∑ c, if s c = s a then F c b * F a c else 0 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single a]
    · simp
    · intro d _ hd; simp [hd]
    · simp
  rw [h0]
  have split : (∑ c, ∑ d, if s c = s d then
      (((if c = a then F c d * F d b else 0) - (if b = d then F c d * F a c else 0)) +
      ((if d = a then F c b * F d c else 0) - (if b = c then F a d * F d c else 0))) else 0) =
      ((∑ c, ∑ d, if s c = s d then (if c = a then F c d * F d b else 0) else 0) -
        (∑ c, ∑ d, if s c = s d then (if b = d then F c d * F a c else 0) else 0)) +
      ((∑ c, ∑ d, if s c = s d then (if d = a then F c b * F d c else 0) else 0) -
        (∑ c, ∑ d, if s c = s d then (if b = c then F a d * F d c else 0) else 0)) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  rw [split, h1, h2, h3, h4]
  abel

end GlobalTheory.HoweR
end
