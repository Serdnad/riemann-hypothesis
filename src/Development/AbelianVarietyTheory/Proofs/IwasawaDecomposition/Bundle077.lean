module

public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle069
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle004
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle070
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle067
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory

theorem natCast_inv_mem_adicCompletionIntegers {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (hT : (T : 𝓞 F) ∉ v.asIdeal) :
    ((T : v.adicCompletion F) ≠ 0) ∧ (T : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : Valued.v (((T : 𝓞 F) : F) : v.adicCompletion F) = 1 := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) (v := v)).2 hT
  have h2 : (((T : 𝓞 F) : F) : v.adicCompletion F) = (T : v.adicCompletion F) := by
    have : ((T : 𝓞 F) : F) = (T : F) := by push_cast; rfl
    rw [this]
    exact map_natCast (algebraMap F (v.adicCompletion F)) T
  rw [h2] at h1
  have hne : (T : v.adicCompletion F) ≠ 0 := by
    intro h; rw [h, map_zero] at h1; exact zero_ne_one h1
  refine ⟨hne, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem locL_eq_intV_of_dvd_unit {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Fin n → Prop)
    (π c : 𝓞 E) (T : ℕ) (hT : (T : 𝓞 F) ∉ v.asIdeal) (hπc : π * c = (T : 𝓞 E))
    (hΛ : ∀ y, y ∈ Λ ↔ ∀ a, ∃ r : 𝓞 E, y a = r ∧ (P a → π ∣ r)) (y : Fin n → E ⊗[F] v.adicCompletion F) :
    (y ∈ Formalism.L2.Herm.locL v Λ ↔ ∀ a, y a ∈ Formalism.BasicNotions.intV E v) := by
  classical
  have hleft : ∀ r : 𝓞 E, ((r : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ Formalism.BasicNotions.intV E v := fun r =>
    Subring.subset_closure (Or.inl ⟨⟨(r : E), ⟨r, rfl⟩⟩, rfl⟩)
  have hright : ∀ t ∈ v.adicCompletionIntegers F, ((1 : E) ⊗ₜ[F] t) ∈ Formalism.BasicNotions.intV E v := fun t ht =>
    Subring.subset_closure (Or.inr ⟨⟨t, ht⟩, rfl⟩)
  constructor
  · intro hy
    let M : Submodule (Formalism.BasicNotions.intV E v) (Fin n → E ⊗[F] v.adicCompletion F) :=
      { carrier := {y | ∀ a, y a ∈ Formalism.BasicNotions.intV E v}
        add_mem' := fun ha hb a => (Formalism.BasicNotions.intV E v).add_mem (ha a) (hb a)
        zero_mem' := fun _ => (Formalism.BasicNotions.intV E v).zero_mem
        smul_mem' := fun s _ hy a => (Formalism.BasicNotions.intV E v).mul_mem s.2 (hy a) }
    have hle : Formalism.L2.Herm.locL v Λ ≤ M := by
      unfold Formalism.L2.Herm.locL Formalism.UG.latS
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩ a
      obtain ⟨r, hr, -⟩ := (hΛ x).1 hx a
      show Formalism.UG.inclE _ (x a) ∈ Formalism.BasicNotions.intV E v
      rw [hr]; exact hleft r
    exact hle hy
  · intro hy
    obtain ⟨_, hinv⟩ := natCast_inv_mem_adicCompletionIntegers v T hT
    have he : ∀ a, (Pi.single a (1 : E ⊗[F] v.adicCompletion F)) ∈ Formalism.L2.Herm.locL v Λ := by
      intro a
      have hx : (Pi.single a ((π : 𝓞 E) : E) : Fin n → E) ∈ Λ := by
        rw [hΛ]
        intro b
        refine ⟨(Pi.single a π : Fin n → 𝓞 E) b, ?_, fun _ => ?_⟩
        · by_cases h : b = a
          · subst h; simp
          · simp [h]
        · by_cases h : b = a
          · subst h; simp
          · simp [h]
      have hg : (Pi.single a (((π : E)) ⊗ₜ[F] (1 : v.adicCompletion F)) : Fin n → _) ∈
          Formalism.L2.Herm.locL v Λ := by
        unfold Formalism.L2.Herm.locL Formalism.UG.latS
        apply Submodule.subset_span
        refine ⟨_, hx, ?_⟩
        funext b
        by_cases h : b = a
        · subst h; simp [Formalism.UG.inclE]
        · simp [h, Formalism.UG.inclE]
      let s : Formalism.BasicNotions.intV E v :=
        ⟨((c : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹),
          (Formalism.BasicNotions.intV E v).mul_mem (hleft c) (hright _ hinv)⟩
      have hs : (s : E ⊗[F] v.adicCompletion F) * ((π : E) ⊗ₜ[F] (1 : v.adicCompletion F)) = 1 := by
        obtain ⟨hne, -⟩ := natCast_inv_mem_adicCompletionIntegers v T hT
        show ((c : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹) *
          ((π : E) ⊗ₜ[F] (1 : v.adicCompletion F)) = 1
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        have hcπ : (c : E) * (π : E) = (T : E) := by
          rw [mul_comm]; exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hπc
        rw [hcπ]
        have hT1 : (T : E) ⊗ₜ[F] (1 : v.adicCompletion F) = (1 : E) ⊗ₜ[F] (T : v.adicCompletion F) := by
          have e1 := map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E)
            (B := v.adicCompletion F)) T
          have e2 := map_natCast (Algebra.TensorProduct.includeRight (R := F) (A := E)
            (B := v.adicCompletion F)) T
          rw [Algebra.TensorProduct.includeLeftRingHom_apply] at e1
          rw [Algebra.TensorProduct.includeRight_apply] at e2
          rw [e1, e2]
        calc (T : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹
            = ((T : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹) := by
              simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          _ = 1 := by
              rw [hT1, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hne]
              rfl
      have := (Formalism.L2.Herm.locL v Λ).smul_mem s hg
      convert this using 1
      funext b
      by_cases h : b = a
      · subst h
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_same, Pi.single_eq_same, hs]
      · rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, mul_zero]
    have hsum : y = ∑ a, (⟨y a, hy a⟩ : Formalism.BasicNotions.intV E v) • Pi.single a (1 : E ⊗[F] v.adicCompletion F) := by
      funext b
      rw [Finset.sum_apply, Finset.sum_eq_single b]
      · rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_same, mul_one]
      · intro a _ hab
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_of_ne (Ne.symm hab), mul_zero]
      · intro h; exact absurd (Finset.mem_univ b) h
    rw [hsum]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (he a)

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory

open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}

theorem stepLevel_uloc_le_of_agree {bad bad' : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (S' : StepLevel F E σ J T f bad') (Q : Set (HeightOneSpectrum (𝓞 F)))
    (hQ : ∀ x, (∀ v ∈ Q, bc (prV (E := E) v) x = 1) → x ∈ S.U → x ∈ S'.U)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ Q) : S.Uloc v ≤ S'.Uloc v := by
  intro h hh
  have hx1 : bc (prV (E := E) v) (Formalism.UG.P.afsplitU v h 1) = h := Formalism.UG.P.afsplit_right1 v h 1
  have hxw : ∀ w, w ≠ v → bc (prV (E := E) w) (Formalism.UG.P.afsplitU v h 1) = 1 := by
    intro w hw
    apply Units.ext
    rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw,
      Units.val_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hxU : Formalism.UG.P.afsplitU v h 1 ∈ S.U := by
    rw [S.U_eq]
    refine ⟨Formalism.UG.P.afsplitU_mem v σ J h 1 (S.Uloc_le v hh) (one_mem _), fun w => ?_⟩
    by_cases hw : w = v
    · rw [hw, hx1]; exact hh
    · rw [hxw w hw]; exact one_mem _
  have hxQ : ∀ w ∈ Q, bc (prV (E := E) w) (Formalism.UG.P.afsplitU v h 1) = 1 :=
    fun w hw => hxw w (fun he => hv (he ▸ hw))
  have h2 := ((S'.U_eq _).mp (hQ _ hxQ hxU)).2 v
  rwa [hx1] at h2

end

theorem stepLevel_uloc_eq_of_agree : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad bad' : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (S' : StepLevel F E σ J T f bad') (Q : Set (HeightOneSpectrum (𝓞 F))),
    (∀ x, (∀ v ∈ Q, bc (prV (E := E) v) x = 1) → (x ∈ S.U ↔ x ∈ S'.U)) → ∀ v, v ∉ Q → S.Uloc v = S'.Uloc v := by
  intro F E _ _ _ _ _ σ n J T f bad bad' S S' Q hQ v hv
  exact le_antisymm (stepLevel_uloc_le_of_agree S S' Q (fun x hx => (hQ x hx).mp) v hv)
    (stepLevel_uloc_le_of_agree S' S Q (fun x hx => (hQ x hx).mpr) v hv)

end GlobalTheory
end
end

section

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.existsUnique_embedding_eigenspace_sum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (φ : c.F →+* R) (ρ : 𝓞 E →+* Module.End R V) (v : V), ∃! w : (E →+* ℂ) → V, (∀ τ a, ρ a (w τ) = φ (embK c τ a) • w τ) ∧ ∑ τ, w τ = v := by
  first | exact @GlobalTheory.EigDecomp.exists_unique_eigen_sum | exact GlobalTheory.EigDecomp.exists_unique_eigen_sum | (intros; apply GlobalTheory.EigDecomp.exists_unique_eigen_sum <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem (L : Type*) [Field L] [NumberField L] {p : ℕ}
    (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ v.asIdeal := by
  have hP : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨Q, hQm, hQ⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) (Ideal.span {(p : ℤ)})
      (by
        intro x hx
        rw [RingHom.mem_ker, (algebraMap ℤ (𝓞 L)).injective_int.eq_iff' (map_zero _)] at hx
        simp [hx])
  have hmem : ((p : ℕ) : 𝓞 L) ∈ Q := by
    have : (p : ℤ) ∈ Ideal.under ℤ Q := by
      rw [hQ]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQm.isPrime, ?_⟩, hmem⟩
  rintro rfl
  have : (p : ℤ) ∈ (⊥ : Ideal (𝓞 L)).comap (algebraMap ℤ (𝓞 L)) := by simpa using hmem
  rw [Ideal.mem_comap, Ideal.mem_bot] at this
  exact hp.ne_zero (by simpa using this)

open NumberField IsDedekindDomain in
private theorem exists_injective_units_zmod_hom_units_complex (p : ℕ) [Fact p.Prime] :
    ∃ f : (ZMod p)ˣ →* ℂˣ, Function.Injective f := by
  set n := Nat.card (ZMod p)ˣ
  have hn : NeZero n := ⟨Nat.card_pos.ne'⟩
  have hc : Nat.card (ZMod p)ˣ = Nat.card (rootsOfUnity n ℂ) := by
    rw [Complex.card_rootsOfUnity]
  exact ⟨(rootsOfUnity n ℂ).subtype.comp (mulEquivOfCyclicCardEq hc).toMonoidHom,
    Subtype.val_injective.comp (mulEquivOfCyclicCardEq hc).injective⟩


open NumberField IsDedekindDomain in
open Classical in
theorem _root_.GlobalTheory.nonempty_piBar_and_omg :
    ∀ (R : _root_.Formalism.BasicNotions.Ranks) (H : _root_.Formalism.BasicNotions.Host R), Nonempty (_root_.Formalism.L2.Host.PiBar H) ∧ Nonempty (_root_.Formalism.L2.Host.Omg H) := by
  intro R H
  refine ⟨⟨⟨fun k => (_root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem H.K (H.g_prime k)).choose,
    fun k => (_root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem H.K (H.g_prime k)).choose_spec⟩⟩, ?_⟩
  have : ∀ k : Fin 2, ∃ f : (ZMod (H.g k))ˣ →* ℂˣ, Function.Injective f := fun k =>
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    exists_injective_units_zmod_hom_units_complex (H.g k)
  exact ⟨⟨fun k => (this k).choose, fun k => (this k).choose_spec⟩⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeGlue

theorem polishSpace_addCommGroup (G : Type) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] :
    PolishSpace G := by
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  haveI : CompleteSpace G := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace G
  haveI : (uniformity G).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  infer_instance

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem repr_map (φ : R →ₐ[F] R') (z : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem tens_ext {z z' : R ⊗[F] E} (h : ∀ k, (Algebra.TensorProduct.basis R b).repr z k =
    (Algebra.TensorProduct.basis R b).repr z' k) : z = z' :=
  (Algebra.TensorProduct.basis R b).ext_elem h

theorem exists_repr (c : Fin d → R) :
    ∃ z : R ⊗[F] E, ∀ k, (Algebra.TensorProduct.basis R b).repr z k = c k :=
  ⟨(Algebra.TensorProduct.basis R b).equivFun.symm c, fun k => by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]⟩

include b in
theorem continuous_map [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace R']
    [IsTopologicalRing R'] (φ : R →ₐ[F] R') (hφ : Continuous φ) :
    Continuous (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have h1 : Continuous (Algebra.TensorProduct.basis R b).equivFun :=
    IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
  have h2 : Continuous (Algebra.TensorProduct.basis R' b).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R' b).equivFun.symm.toLinearMap
  have h3 : Continuous fun z : R ⊗[F] E => fun k => φ ((Algebra.TensorProduct.basis R b).equivFun z k) :=
    continuous_pi fun k => hφ.comp ((continuous_apply k).comp h1)
  refine (h2.comp h3).congr fun z => ?_
  simp only [Function.comp_apply]
  rw [LinearEquiv.symm_apply_eq]
  funext k
  simp only [Module.Basis.equivFun_apply, repr_map]

end Coord

section Adele

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) {n M : ℕ}

theorem repr_projInf (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X a i) k =
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).1 :=
  repr_map b (fstA F) _ k

theorem repr_projV (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n)
    (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k =
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2 v :=
  (repr_map b (evalV F v) _ k).trans (congrArg (evalV F v) (repr_map b (sndA F) _ k))

theorem continuous_fstA : Continuous (fstA F) := continuous_fst

theorem continuous_sndA : Continuous (sndA F) := continuous_snd

theorem continuous_evalV (v : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F v) :=
  RestrictedProduct.continuous_eval v

theorem adele_ext {x y : AF F} (h1 : x.1 = y.1) (h2 : ∀ v, x.2 v = y.2 v) : x = y :=
  Prod.ext h1 (RestrictedProduct.ext _ _ h2)

theorem exists_adele (x : Ainf F) (y : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (hy : ∀ᶠ v in Filter.cofinite, y v ∈ v.adicCompletionIntegers F) :
    ∃ z : AF F, z.1 = x ∧ ∀ v, z.2 v = y v :=
  ⟨pairA F x ⟨y, hy⟩, rfl, fun _ => rfl⟩

include b in
theorem continuous_projInf : Continuous (projInf (F := F) (E := E) (M := M) (n := n)) :=
  continuous_pi fun a => continuous_pi fun i =>
    (continuous_map b (fstA F) continuous_fstA).comp
      ((continuous_apply i).comp (continuous_apply a))

include b in
theorem continuous_projV (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun X : (Fin n → Fin M → AF F ⊗[F] E) => projV v (projFin X) :=
  continuous_pi fun a => continuous_pi fun i =>
    (continuous_map b (evalV F v) (continuous_evalV v)).comp
      ((continuous_map b (sndA F) continuous_sndA).comp
        ((continuous_apply i).comp (continuous_apply a)))

include b in
theorem injective_glue : Function.Injective (fun X : (Fin n → Fin M → AF F ⊗[F] E) =>
    (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) := by
  intro X X' h
  have h1 : projInf X = projInf X' := congrArg Prod.fst h
  have h2 : ∀ v, projV v (projFin X) = projV v (projFin X') := congrFun (congrArg Prod.snd h)
  funext a i
  refine tens_ext b fun k => adele_ext ?_ fun v => ?_
  · rw [← repr_projInf, ← repr_projInf, h1]
  · rw [← repr_projV, ← repr_projV, h2]

theorem range_glue : Set.range (fun X : (Fin n → Fin M → AF F ⊗[F] E) =>
    (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) =
    {Y | ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Y.2 v ∈ latV b v} := by
  ext Y
  constructor
  · rintro ⟨X, rfl⟩
    have : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ a i k,
        ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2 v ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k =>
        ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2.2
    filter_upwards [this] with v hv a i k
    rw [repr_projV]
    exact hv a i k
  · intro hY
    choose c hc1 hc2 using fun (a : Fin n) (i : Fin M) (k : Fin d) =>
      exists_adele ((Algebra.TensorProduct.basis (Ainf F) b).repr (Y.1 a i) k)
        (fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (Y.2 v a i) k)
        (Filter.Eventually.mono hY fun v hv => hv a i k)
    choose X hX using fun a i => exists_repr b (c a i)
    have h1 : projInf X = Y.1 := by
      funext a i
      refine tens_ext b fun k => ?_
      rw [repr_projInf, hX, hc1]
    have h2 : ∀ v, projV v (projFin X) = Y.2 v := fun v => by
      funext a i
      refine tens_ext b fun k => ?_
      rw [repr_projV, hX, hc2]
    exact ⟨X, Prod.ext h1 (funext h2)⟩

end Adele

theorem adelicTuple_measurableEmbedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), MeasurableEmbedding (fun X : (Fin n → Fin M → AF F ⊗[F] E) => (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) ∧ Set.range (fun X : (Fin n → Fin M → AF F ⊗[F] E) => (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) = {Y | ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Y.2 v ∈ latV b v} ∧ Continuous (projInf (F := F) (E := E) (M := M) (n := n)) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Continuous fun X : (Fin n → Fin M → AF F ⊗[F] E) => projV v (projFin X) := by
  intro F E _ _ _ _ _ d b n M
  refine ⟨?_, range_glue b, continuous_projInf b, continuous_projV b⟩
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  haveI : PolishSpace (Fin n → Fin M → AF F ⊗[F] E) := polishSpace_addCommGroup _
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (Fv F v ⊗[F] E) := fun v =>
    inferInstance
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v =>
    inferInstance
  haveI : BorelSpace (∀ v : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F v ⊗[F] E) :=
    Pi.borelSpace
  haveI : BorelSpace (Fin n → Fin M → Ainf F ⊗[F] E) := inferInstance
  exact ((continuous_projInf b).prodMk (continuous_pi (continuous_projV b))).measurableEmbedding
    (injective_glue b)

end GlobalTheory.GaugeGlue
end

section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

theorem _root_.GlobalTheory.T.exists_rep_lift_of_entries_mem_range : ∀ {k L Γ : Type} [Field k] [Field L] [Group Γ] (f : k →+* L) {b : ℕ} (τ : Γ →* GL (Fin b) L), (∀ g i j, ∃ x, f x = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) i j) → ∃ σ : Γ →* GL (Fin b) k, mapRep f σ = τ := by
  first | exact @GlobalTheory.lift_rep_of_entries_in_image | exact GlobalTheory.lift_rep_of_entries_in_image | (intros; apply GlobalTheory.lift_rep_of_entries_in_image <;> assumption)
end

section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

theorem _root_.GlobalTheory.T.exists_intertwiner_map_eq_of_irrSub : ∀ {Γ L : Type} [Group Γ] [Field L] {a n : ℕ} (τ τ₀ : Γ →* GL (Fin a) L) (P : GL (Fin a) L), (∀ g, ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * (P : Matrix (Fin a) (Fin a) L) = (P : Matrix (Fin a) (Fin a) L) * ((τ₀ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) → IsSSRep τ → ∀ (Vs : Fin n → Submodule L (Fin a → L)), iSup Vs = ⊤ → (∀ j, IsIrrSub τ₀ (Vs j)) → ∀ V, IsIrrSub τ V → ∃ (j : Fin n) (M : Matrix (Fin a) (Fin a) L), (∀ g, ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * M = M * ((τ₀ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) ∧ Submodule.map M.mulVecLin (Vs j) = V ∧ Disjoint (LinearMap.ker M.mulVecLin) (Vs j) := by
  first | exact @GlobalTheory.ConstituentImage.exists_constituent_image | exact GlobalTheory.ConstituentImage.exists_constituent_image | (intros; apply GlobalTheory.ConstituentImage.exists_constituent_image <;> assumption)
end

section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

theorem _root_.GlobalTheory.T.exists_leftInverse_restrict_stable_submodule_matrixRep : ∀ {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L) (V : Submodule L (Fin a → L)), IsInv τ V → ∃ (b : ℕ) (E : Matrix (Fin a) (Fin b) L) (D : Matrix (Fin b) (Fin a) L) (σ : Γ →* GL (Fin b) L), D * E = 1 ∧ LinearMap.range E.mulVecLin = V ∧ ∀ g, ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) = D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E ∧ ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E = E * ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
  first | exact @GlobalTheory.StableSubMat.exists_restrict | exact GlobalTheory.StableSubMat.exists_restrict | (intros; apply GlobalTheory.StableSubMat.exists_restrict <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.lbIso_of_lbIso_on_disjoint_cover : ∀ (Y : Scheme.{0}) (A : Type) (W : A → Y.Opens), (∀ a b y, y ∈ W a → y ∈ W b → a = b) → (∀ y, ∃ a, y ∈ W a) → ∀ (P Q : LB Y), P.IsLB → Q.IsLB → (∀ a, LBIso (P.pull (W a).ι) (Q.pull (W a).ι)) → LBIso P Q := by
  first | exact @GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover | exact GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover | (intros; apply GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover <;> assumption)
end
