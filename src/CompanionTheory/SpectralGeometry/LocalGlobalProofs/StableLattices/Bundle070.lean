module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle026
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle053
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle066
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle068
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.DictLoc

open scoped TensorProduct
open IsDedekindDomain NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

def Cp (A : Type) : Type := A

section Model

theorem exists_model_field {K A : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    [Field A] [Algebra K A] [FiniteDimensional K A] [TopologicalSpace A] [IsModuleTopology K A] :
    ∃ (L : Type) (_ : NontriviallyNormedField L) (_ : IsUltrametricDist L) (_ : ProperSpace L) (e : A ≃+* L),
      Continuous e ∧ Continuous e.symm ∧ ∀ (c : A ≃ₐ[K] A) (x : A), ‖e (c x)‖ = ‖e x‖ := by
  haveI : CompleteSpace K := inferInstance
  letI fL : Field (Cp A) := ‹Field A›
  letI aL : Algebra K (Cp A) := ‹Algebra K A›
  haveI : FiniteDimensional K (Cp A) := ‹FiniteDimensional K A›
  haveI : Algebra.IsAlgebraic K (Cp A) := Algebra.IsAlgebraic.of_finite K (Cp A)
  letI nL : NontriviallyNormedField (Cp A) := spectralNorm.nontriviallyNormedField K (Cp A)
  letI mL : NormedAlgebra K (Cp A) := spectralNorm.normedAlgebra K (Cp A)
  haveI uL : IsUltrametricDist (Cp A) := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := K) (L := Cp A))
  haveI pL : ProperSpace (Cp A) := FiniteDimensional.proper K (Cp A)
  haveI : IsModuleTopology K (Cp A) := isModuleTopologyOfFiniteDimensional
  haveI : ContinuousAdd A := IsModuleTopology.toContinuousAdd K A
  let f : A ≃ₗ[K] Cp A := LinearEquiv.refl K A
  refine ⟨Cp A, nL, uL, pL, RingEquiv.refl A, IsModuleTopology.continuous_of_linearMap f.toLinearMap,
    IsModuleTopology.continuous_of_linearMap f.symm.toLinearMap, fun c x => ?_⟩
  exact (spectralNorm_eq_of_equiv (K := K) (L := Cp A) c x).symm

theorem isField_tensor_of_no_algHom {F K E : Type} [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E]
    (h2 : Module.finrank F E = 2) (hn : IsEmpty (E →ₐ[F] K)) : IsField (K ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hA : Module.finrank K (K ⊗[F] E) = 2 := by rw [Module.finrank_baseChange, h2]
  haveI : Nontrivial (K ⊗[F] E) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[F] E)
  by_cases hb : m = ⊥
  · subst hb
    exact ((RingEquiv.quotientBot (K ⊗[F] E)).symm.toMulEquiv.isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient ⊥).1 hm))
  · exfalso
    letI := Ideal.Quotient.field m
    let φ : (K ⊗[F] E) →ₐ[K] (K ⊗[F] E) ⧸ m := Ideal.Quotient.mkₐ K m
    have hs : Function.Surjective φ := Ideal.Quotient.mkₐ_surjective K m
    have h3 := LinearMap.finrank_range_add_finrank_ker φ.toLinearMap
    rw [LinearMap.range_eq_top.2 hs, finrank_top, hA] at h3
    have hk : 0 < Module.finrank K (LinearMap.ker φ.toLinearMap) := by
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
      haveI : Nontrivial (LinearMap.ker φ.toLinearMap) :=
        ⟨⟨⟨x, (Ideal.Quotient.eq_zero_iff_mem.2 hx)⟩, 0, fun e => hx0 (congrArg Subtype.val e)⟩⟩
      exact Module.finrank_pos
    haveI : Module.Finite K ((K ⊗[F] E) ⧸ m) := Module.Finite.of_surjective φ.toLinearMap hs
    have hq : 0 < Module.finrank K ((K ⊗[F] E) ⧸ m) := Module.finrank_pos
    have h1 : Module.finrank K ((K ⊗[F] E) ⧸ m) = 1 := by omega
    have hbj : Function.Bijective (Algebra.ofId K ((K ⊗[F] E) ⧸ m)) :=
      ⟨(algebraMap K _).injective, fun y => by
        have : (⊥ : Subalgebra K ((K ⊗[F] E) ⧸ m)) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h1
        have hy : y ∈ (⊥ : Subalgebra K ((K ⊗[F] E) ⧸ m)) := this ▸ Algebra.mem_top
        obtain ⟨a, ha⟩ := Algebra.mem_bot.1 hy
        exact ⟨a, ha⟩⟩
    let ε : K ≃ₐ[K] (K ⊗[F] E) ⧸ m := AlgEquiv.ofBijective _ hbj
    exact hn.false (((ε.symm.toAlgHom.comp φ).restrictScalars F).comp Algebra.TensorProduct.includeRight)

end Model

section Main

theorem exists_model {K A : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    [CommRing A] [Algebra K A] [Module.Finite K A] [TopologicalSpace A] [IsModuleTopology K A] (hA : IsField A) :
    ∃ (L : Type) (_ : NontriviallyNormedField L) (_ : IsUltrametricDist L) (_ : ProperSpace L) (e : A ≃+* L),
      Continuous e ∧ Continuous e.symm ∧ ∀ (c : A ≃ₐ[K] A) (x : A), ‖e (c x)‖ = ‖e x‖ :=
  letI := hA.toField
  exists_model_field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

def sigEquiv (K : Type) [Field K] [Algebra F K] (h : ∀ x, σ (σ x) = x) : (K ⊗[F] E) ≃ₐ[K] (K ⊗[F] E) :=
  AlgEquiv.ofAlgHom (Algebra.TensorProduct.map (AlgHom.id K K) σ) (Algebra.TensorProduct.map (AlgHom.id K K) σ)
    (by ext x; simp [h]) (by ext x; simp [h])

theorem sigEquiv_apply (K : Type) [Field K] [Algebra F K] (h : ∀ x, σ (σ x) = x) (y : K ⊗[F] E) :
    sigEquiv K h y = sigR K σ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem sigR_sigR (K : Type) [Field K] [Algebra F K] (h : ∀ x, σ (σ x) = x) (y : K ⊗[F] E) :
    sigR K σ (sigR K σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (h x)

theorem properSpace_Fv (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (Fv F v) := by
  refine Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.2
    ⟨inferInstance, ?_, ?_⟩
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))
  · exact Formalism.UG.P.tjcosets_finite v

theorem charZero_Fv : CharZero (Fv F v) :=
  ((algebraMap F (Fv F v)).charZero_iff (algebraMap F (Fv F v)).injective).1 inferInstance

end Main

section Dict

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}


open Formalism.UG (bc UJ cT) in
theorem exists_equiv_UG {L : Type} [Field L] [TopologicalSpace L] (e : (Fv F v ⊗[F] E) ≃+* L) (he : Continuous e)
    (he' : Continuous e.symm) :
    Nonempty (GLoc σ J v ≃ₜ* CompanionTheory.Rg.Fl.UG (e.toRingHom.comp ((sigR (Fv F v) σ).comp e.symm.toRingHom))
      ((JR (Fv F v) J).map e)) := by
  set s : L →+* L := e.toRingHom.comp ((sigR (Fv F v) σ).comp e.symm.toRingHom) with hs
  have e1 : ∀ x : GL (Fin n) L, bc e.toRingHom (bc e.symm.toRingHom x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => e.apply_symm_apply _)
  have e2 : ∀ x : GL (Fin n) (Fv F v ⊗[F] E), bc e.symm.toRingHom (bc e.toRingHom x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => e.symm_apply_apply _)
  have key : ∀ x : GL (Fin n) (Fv F v ⊗[F] E),
      (cT (sigR (Fv F v) σ) x.1 * JR (Fv F v) J * x.1).map e =
        (((bc e.toRingHom x).1.map s).transpose * (JR (Fv F v) J).map e * (bc e.toRingHom x).1) := fun x => by
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 2
    exact Matrix.ext fun i j => by simp [cT, hs, bc]
  have mem : ∀ x : GL (Fin n) (Fv F v ⊗[F] E), x ∈ HR (Fv F v) σ J ↔
      bc e.toRingHom x ∈ CompanionTheory.Rg.Fl.UG s ((JR (Fv F v) J).map e) := fun x => by
    change cT (sigR (Fv F v) σ) x.1 * JR (Fv F v) J * x.1 = JR (Fv F v) J ↔
      ((bc e.toRingHom x).1.map s).transpose * (JR (Fv F v) J).map e * (bc e.toRingHom x).1 = (JR (Fv F v) J).map e
    rw [← key]
    exact (Matrix.map_injective e.injective).eq_iff.symm
  have c1 : Continuous (bc (n := Fin n) e.toRingHom) := GlobalTheory.LFun.SplitChart.continuous_bc he
  have c2 : Continuous (bc (n := Fin n) e.symm.toRingHom) := GlobalTheory.LFun.SplitChart.continuous_bc he'
  have hemb := isEmbedding_matHom (Fv F v) σ J
  exact ⟨{ toFun := fun g => ⟨bc e.toRingHom (matHom _ σ J g), (mem _).1 g.2⟩
           invFun := fun u => (⟨bc e.symm.toRingHom u.1, (mem _).2 (by rw [e1]; exact u.2)⟩ : HR (Fv F v) σ J)
           left_inv := fun g => matHom_injective _ σ J (e2 _)
           right_inv := fun u => Subtype.ext (e1 _)
           map_mul' := fun g g' => Subtype.ext (by simp only [map_mul, Subgroup.coe_mul])
           continuous_toFun := (c1.comp hemb.continuous).subtype_mk _
           continuous_invFun := hemb.continuous_iff.2 (c2.comp continuous_subtype_val) }⟩

end Dict


open GlobalTheory.LFun.InertChart in
theorem stDict : CompanionTheory.Rg.Fl.StDict := by
  intro F E _ _ _ _ _ σ h n J hJ v
  letI nf : NontriviallyNormedField (Fv F v) :=
    Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  haveI pf : ProperSpace (Fv F v) := properSpace_Fv v
  haveI uf : IsUltrametricDist (Fv F v) := inferInstance
  haveI cf : CharZero (Fv F v) := charZero_Fv
  by_cases hs : Nonempty (E →ₐ[F] Fv F v)
  · obtain ⟨τ⟩ := hs
    exact ⟨Fv F v, nf, uf, pf, cf, Or.inl ⟨splitEquiv h hJ τ⟩⟩
  · have hf : IsField (Fv F v ⊗[F] E) := isField_tensor_of_no_algHom h.2.2.1 (not_nonempty_iff.1 hs)
    haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    obtain ⟨L, nL, uL, pL, e, he, he', hn⟩ := exists_model (K := Fv F v) (A := Fv F v ⊗[F] E) hf
    have hcc : ∀ x, σ (σ x) = x := conj_conj h
    have hss : ∀ y : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := sigR_sigR _ hcc
    have hi : ∀ x : E, sigR (Fv F v) σ (inclR (Fv F v) x) = inclR (Fv F v) (σ x) := fun _ => rfl
    have hinj : Function.Injective (e.toRingHom.comp (inclR (Fv F v))) := RingHom.injective (e.toRingHom.comp (inclR (Fv F v)))
    have hL : CharZero L :=
      let ϕ : Fv F v →+* L := e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom
      (ϕ.charZero_iff ϕ.injective).1 cf
    refine ⟨L, nL, uL, pL, hL, Or.inr ⟨_, (JR (Fv F v) J).map e, fun x => ?_, fun x => ?_, ?_, ?_, ?_,
      exists_equiv_UG e he he'⟩⟩
    · simp [hss]
    · have := hn (sigEquiv (Fv F v) hcc) (e.symm x)
      simpa [sigEquiv_apply] using this
    · obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := not_forall.1 (conj_ne h)
      refine ⟨e (inclR (Fv F v) x), fun ee => hx (hinj ?_)⟩
      simpa [hi] using ee
    · refine Matrix.ext fun i j => ?_
      simp [JR, hi, hJ.1 i j]
    · have : ((JR (Fv F v) J).map e).det = (e.toRingHom.comp (inclR (Fv F v))) J.det := by
        rw [RingHom.map_det]; rfl
      rw [this]
      exact (map_ne_zero_iff _ hinj).2 hJ.2

end GlobalTheory.CompanionTheory.DictLoc

end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

noncomputable section

namespace GlobalTheory.CompanionTheory.PointSurjectivity

theorem exists_acyclic_cechLB_fibre : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsProper a] [Flat a] [IsProper b] (G : LB Z) (hG : G.IsLB)
    (F : Set (Sp k ⟶ T)) (hF : F.Finite)
    (hfib : ∀ (y : Sp k ⟶ T) (σ : X ⟶ Z), y ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X → σ ≫ q = a ≫ y → y ∉ F → FibAc a (G.pull σ))
    (htot : FibAc (p ≫ a) G) (y₀ : Sp k ⟶ T) (σ₀ : X ⟶ Z) (hy : y₀ ≫ b = 𝟙 _) (h₁ : σ₀ ≫ p = 𝟙 X)
    (h₂ : σ₀ ≫ q = a ≫ y₀), ∃ (m : ℕ) (D : Fin m → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ ∧ (cechLB a (G.pull σ₀) D).Acyclic := by
  intro k _ _ X T Z a b p q H ha _ _ _ G hG F hF hfib htot y₀ σ₀ hy h₁ h₂
  have hsepa : IsSeparated a := inferInstance
  have hsepb : IsSeparated b := inferInstance
  have hX : X.IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
  have hT' : T.IsSeparated := ⟨by rw [← terminal.comp_from b]; infer_instance⟩
  have hcX : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have hcT : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace b
  have hpp : IsProper p := MorphismProperty.of_isPullback (P := @IsProper) H.flip inferInstance
  have hcZ : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (p ≫ a)
  have hsepZ : IsSeparated (p ≫ a) := inferInstance
  let q₀ : Sp k := IsLocalRing.closedPoint k
  have huniv : ({q₀} : Set (Sp k)) = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim (α := PrimeSpectrum k) _ _
  have hclosed (y : Sp k ⟶ T) (hy : y ≫ b = 𝟙 _) : IsClosed ({y q₀} : Set T) := by
    have : IsClosedImmersion (y ≫ b) := by rw [hy]; infer_instance
    have : IsClosedImmersion y := IsClosedImmersion.of_comp y b
    rw [← Set.image_singleton]
    refine y.isClosedEmbedding.isClosedMap _ ?_
    rw [huniv]
    exact isClosed_univ
  let F₁ : Set T := (fun y : Sp k ⟶ T => y q₀) '' ({y ∈ F | y ≫ b = 𝟙 _} ∪ {y₀})
  have hF₁ : F₁.Finite := (((hF.subset (Set.sep_subset _ _))).union (Set.finite_singleton _)).image _
  have hF₁c : ∀ x ∈ F₁, IsClosed ({x} : Set T) := by
    rintro _ ⟨y, hyF | rfl, rfl⟩
    · exact hclosed y hyF.2
    · exact hclosed _ hy
  obtain ⟨r, V, hV, hVc, hV₁⟩ := GlobalTheory.T.affine_cover_separating_finite_closed_points T F₁ hF₁ hF₁c
  obtain ⟨m', B, hB, hBc, -⟩ := GlobalTheory.T.affine_cover_separating_finite_closed_points X ∅ Set.finite_empty (by simp)
  obtain ⟨d, D, hD, hDc, -⟩ := GlobalTheory.T.affine_cover_separating_finite_closed_points Z ∅ Set.finite_empty (by simp)
  let U : Fin (m' + 1) → Z.Opens := fun i => p ⁻¹ᵁ B i
  let W : Fin (r + 1) → Z.Opens := fun j => q ⁻¹ᵁ V j
  have hT : ∀ n, Limits.IsZero ((cubeComplex (Cube.trunc₂ (secCube (p ≫ a) G
      fun u : Fin (m' + 1) ⊕ₗ Fin (r + 1) => Sum.elim U W (ofLex u)))).homology (n + 2)) := by
    intro n
    obtain ⟨e⟩ := cechLB_homology_equiv_trunc₂ k Z (p ≫ a) G _ D _ U _ W hG hsepZ hD hDc
      (by simp only [U]; rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top])
      (by simp only [W]; rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_top])
      (fun i _ h => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hB i) h)
      (fun j _ h => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hV j) h)
      (fun i j => (GlobalTheory.T.affine_cover_of_product_fibres a b p q H (hV j) B hB hBc G hG).1 i) n
    have hz := ((htot _ D hD hDc) n).isZero_homology
    have := ModuleCat.subsingleton_of_isZero hz
    have := e.symm.toEquiv.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  have hA : ∀ t : Finset (Fin (r + 1)), 2 ≤ t.card → (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst (secCube (p ≫ a) G
      fun u : Fin (m' + 1) ⊕ₗ Fin (r + 1) => Sum.elim U W (ofLex u)) t)).Acyclic := by
    intro t ht
    have hne : t.Nonempty := Finset.card_pos.1 (by omega)
    have hVt : IsAffineOpen (⨅ j ∈ t, V j) :=
      IsAffineOpen.biInf _ t.finite_toSet hne fun j _ => hV j
    obtain ⟨-, Y, π, f, E, Hy, hE, hEc, ⟨i₁⟩⟩ := GlobalTheory.T.affine_cover_of_product_fibres a b p q H hVt B hB hBc G hG
    obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ a) G U W t _
      (preimage_biInf V q t)
    obtain ⟨j₁, hj₁, j₂, hj₂, hne'⟩ := Finset.one_lt_card.1 ht
    have hfac := GlobalTheory.T.fibrewise_acyclicity_base_change a b p q H ha G hG Γ(T, ⨅ j ∈ t, V j) hVt.fromSpec Y π f Hy
      (fun s σ hs hσ₁ hσ₂ => hfib (s ≫ hVt.fromSpec) σ (by simpa using hs) hσ₁ hσ₂ (by
        intro hmem
        have hp : hVt.fromSpec (s q₀) ∈ (⨅ j ∈ t, V j : T.Opens) :=
          hVt.range_fromSpec.le ⟨_, rfl⟩
        have hx : (s ≫ hVt.fromSpec) q₀ ∈ F₁ :=
          ⟨_, Or.inl ⟨hmem, by simpa using hs⟩, rfl⟩
        have hp' : (s ≫ hVt.fromSpec) q₀ ∈ (⨅ j ∈ t, V j : T.Opens) := by simpa using hp
        exact hne' (hV₁ _ hx j₁ j₂ (biInf_le V hj₁ hp') (biInf_le V hj₂ hp'))))
    have h := hfac _ E hE hEc
    exact fun n => (GlobalTheory.MumfordCohom.acyclic_cechLB_of_acyclic f _ _ E h n).of_iso (i₁ ≪≫ i₂)
  obtain ⟨j₀, hj₀⟩ : ∃ j, y₀ q₀ ∈ V j := by
    have : y₀ q₀ ∈ (⨆ j, V j : T.Opens) := hVc ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hcol := GlobalTheory.T.cech_slice_acyclic_of_truncation _ hA hT j₀
  obtain ⟨-, Y, π, f, E, Hy, hE, hEc, ⟨i₁⟩⟩ := GlobalTheory.T.affine_cover_of_product_fibres a b p q H (hV j₀) B hB hBc G hG
  obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ a) G U W {j₀} (q ⁻¹ᵁ V j₀)
    (by simp [W])
  have hac₁ : (cechLB (f ≫ (hV j₀).fromSpec ≫ b) (G.pull π) E).Acyclic :=
    fun n => (hcol n).of_iso (i₁ ≪≫ i₂).symm
  have hac : (cechLB f (G.pull π) E).Acyclic :=
    GlobalTheory.MumfordCohom.acyclic_cechLB_of_acyclic _ f _ E hac₁
  have hrange : Set.range y₀ ⊆ Set.range (hV j₀).fromSpec := by
    rw [(hV j₀).range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have : x = q₀ := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [this]
    exact hj₀
  let s : Sp k ⟶ Spec Γ(T, V j₀) := IsOpenImmersion.lift (hV j₀).fromSpec y₀ hrange
  have hs : s ≫ (hV j₀).fromSpec = y₀ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨D', hD', hD'c, hD'a⟩ := GlobalTheory.T.exists_affine_cover_cechLB_fibre_acyclic a b p q H G hG Γ(T, V j₀) (hV j₀).fromSpec Y π f Hy E hE hEc hac
    s σ₀ (by rw [← Category.assoc, hs]; exact hy) h₁ (by rw [hs]; exact h₂)
  exact ⟨m' + 1, D', hD', hD'c, hD'a⟩

end GlobalTheory.CompanionTheory.PointSurjectivity
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity


theorem _root_.GlobalTheory.T.fibre_acyclicity_of_sections : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsProper a] [Flat a] [IsProper b] (G : LB Z) (hG : G.IsLB)
    (hfib : ∀ (y : Sp k ⟶ T) (σ : X ⟶ Z), y ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X → σ ≫ q = a ≫ y → FibAc a (G.pull σ)), FibAc (p ≫ a) G := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjTotal.fibAc_comp_of_fibres | exact GlobalTheory.CompanionTheory.PointSurjTotal.fibAc_comp_of_fibres | (intros; apply GlobalTheory.CompanionTheory.PointSurjTotal.fibAc_comp_of_fibres <;> assumption)
end
