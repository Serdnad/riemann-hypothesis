module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsVolumeTransportOfLatticeIsometry
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodular
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle330
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.HermitianForms.Bundle009
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle113
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle122
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle048
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle045
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralPeriodElement
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle008
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003

@[expose] public section

section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

theorem _root_.GlobalTheory.T.compactSubgroup_quotient_invariant_measure : CompactClause := by
  first | exact @GlobalTheory.QuotientMeasureCompact.compactClause | exact GlobalTheory.QuotientMeasureCompact.compactClause | (intros; apply GlobalTheory.QuotientMeasureCompact.compactClause <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicUnimod
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
open Formalism.UG (UJ cT intAd)
open scoped TensorProduct NNReal ENNReal Pointwise RestrictedProduct

noncomputable section

namespace GlobalTheory.FiniteAdelicUnimod

open GlobalTheory.AdelicPointsUnimod (exists_sum_tmul exists_compact_subring congSub isCompact_congSub
  modular_of_mem_compact isCompact_intAd)

section Adeles

variable {F : Type} [Field F] [NumberField F]

theorem exists_split_finiteAdele {κ : Type} [Finite κ] (a : κ → Af F) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra F R) (p : Af F →ₐ[F] R) (e : Af F),
    IsArtinianRing R ∧ Function.Surjective p ∧ p e = 1 ∧ (∀ x, p x = 0 → e * x = 0) ∧
      ∀ k, (1 - e) * a k ∈ intAd F := by
  classical
  let S := ⋃ k, {v : HeightOneSpectrum (𝓞 F) | a k v ∉ v.adicCompletionIntegers F}
  have hS : S.Finite := Set.finite_iUnion fun k => Filter.eventually_cofinite.1 (a k).2
  haveI : Finite S := hS.to_subtype
  let p : Af F →ₐ[F] (∀ v : S, v.1.adicCompletion F) :=
    { toFun := fun x v => x v.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let s : (∀ v : S, v.1.adicCompletion F) → Af F := fun y =>
    ⟨fun v => if h : v ∈ S then y ⟨v, h⟩ else 0, by
      filter_upwards [hS.compl_mem_cofinite] with v hv
      rw [dite_eq_right hv]
      exact zero_mem _⟩
  have hs : ∀ y, p (s y) = y := fun y => funext fun v => dif_pos v.2
  have hs1 : ∀ v, s 1 v = if v ∈ S then 1 else 0 := fun v => by
    show dite _ _ _ = _
    split_ifs <;> rfl
  refine ⟨_, inferInstance, inferInstance, p, s 1, inferInstance, fun y => ⟨_, hs y⟩, hs 1, fun x hx => ?_,
    fun k v => ?_⟩
  · refine FiniteAdeleRing.ext _ fun v => ?_
    show s 1 v * x v = 0
    rw [hs1]
    split_ifs with h
    · rw [one_mul]
      exact congrFun hx ⟨v, h⟩
    · exact zero_mul _
  · show (1 - s 1 v) * a k v ∈ _
    rw [hs1]
    split_ifs with h
    · rw [sub_self, zero_mul]
      exact zero_mem _
    · rw [sub_zero, one_mul]
      exact not_not.1 fun h' => h (Set.mem_iUnion.2 ⟨k, h'⟩)

end Adeles

section Tensor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_split_tensor (σ : E →ₐ[F] E) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) {κ : Type} [Finite κ]
    (C : NonUnitalSubring (Af F ⊗[F] E)) (hC : ∀ r ∈ intAd F, ∀ β : 𝓞 E, r ⊗ₜ[F] (β : E) ∈ C)
    (x : κ → Af F ⊗[F] E) : ∃ (B : Type) (_ : CommRing B) (σ' : B →+* B) (π : Af F ⊗[F] E →+* B)
      (e : Af F ⊗[F] E), (∀ x, π (sigR (Af F) σ x) = σ' (π x)) ∧ Function.Surjective π ∧ π e = 1 ∧
      (∀ x, π x = 0 → e * x = 0) ∧ sigR (Af F) σ e = e ∧ Generic σ' ∧ ∀ k, (1 - e) * x k ∈ C := by
  classical
  choose a ha using fun k => exists_sum_tmul (x k)
  obtain ⟨R, _, _, p, e, hR, hp, hpe, hker, hint⟩ :=
    exists_split_finiteAdele (κ := κ × _) fun q => a q.1 q.2
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R _
  letI : Algebra ℚ (R ⊗[F] E) := ((inclR (F := F) R).comp (algebraMap ℚ E)).toAlgebra
  refine ⟨R ⊗[F] E, inferInstance, sigR R σ, (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom,
    e ⊗ₜ 1, fun y => ?_, Algebra.TensorProduct.map_surjective _ _ hp Function.surjective_id, ?_, fun y hy => ?_, ?_,
    generic_of_semilocal (δ := inclR R δ) (hδ.isUnit.map _) ?_, fun k => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · simp [hpe, Algebra.TensorProduct.one_def]
  · have hy' : y ∈ RingHom.ker (Algebra.TensorProduct.map p (AlgHom.id F E)) := hy
    rw [Algebra.TensorProduct.rTensor_ker _ hp] at hy'
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      simp [hker z hz]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  · simp [sigR]
  · simp [sigR, inclR, hσδ, TensorProduct.tmul_neg]
  · rw [ha k, Finset.mul_sum, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]
    refine sum_mem fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact hC _ (hint (k, i)) _

theorem isUnimodularLC_finiteAdele (σ : E →ₐ[F] E) (hss : ∀ x, σ (σ x) = x) {δ : E} (hδ : δ ≠ 0)
    (hσδ : σ δ = -δ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) :
    IsUnimodularLC (HA (Af F) σ J) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  obtain ⟨h⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Af F)
  haveI : T2Space (Af F ⊗[F] E) := h.isEmbedding.t2Space
  obtain ⟨_, _, _⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Af F) σ n J
  haveI : BorelSpace (HA (Af F) σ J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (Af F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (Af F) σ J))
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Measure.haar, inferInstance⟩, fun μ _ => ?_⟩
  have hσ := GlobalTheory.AdelicUnitaryTop.continuous_sigR (Af F) σ
  obtain ⟨C, hCc, hC⟩ := exists_compact_subring (F := F) (E := E) (intAd F).toNonUnitalSubring
    (isCompact_intAd F)
  obtain ⟨M, hM⟩ := exists_framed (σ := (σ : E →+* E)) hss (J := J) (by ext i j; exact hJ.1 i j) hJ.2
  have hF : Framed (sigR (Af F) σ) (JR (Af F) J) (M.map (inclR (Af F))) :=
    hM.map fun x => by simp [sigR, inclR]
  have hss' := GlobalTheory.AdelicPointsUnimod.sigR_sigR (R := Af F) hss
  obtain ⟨T, hTc, hT, hT'⟩ := exists_involution hσ hss' hF
  refine ⟨fun g => ?_⟩
  obtain ⟨B, _, σ', π, e, h1, h2, h3, h4, h5, h6, h7⟩ := exists_split_tensor σ hδ hσδ
    (κ := Bool × Fin n × Fin n) C hC fun p =>
      (mat (σ := sigR (Af F) σ) (J := JR (Af F) J) (bif p.1 then g else g⁻¹) - 1) p.2.1 p.2.2
  let χ : HA (Af F) σ J →* ℝ≥0 := Measure.modularCharacter
  have hχ := modular_involution (G := HA (Af F) σ J) T hTc hT
  obtain ⟨k, hk, hk', hkg⟩ := exists_char_eq h1 h2 h3 h4 h5 hss' hF h6 χ
    (fun x x' h => by
      rw [hT' x x' h]
      exact hχ x) g
  have hkK : k ∈ congSub (sigR (Af F) σ) (JR (Af F) J) C :=
    ⟨fun i j => by rw [hk]; exact h7 (true, i, j), fun i j => by rw [hk']; exact h7 (false, i, j)⟩
  let K : Subgroup (HA (Af F) σ J) := congSub (sigR (Af F) σ) (JR (Af F) J) C
  have hKc : IsCompact (K : Set (HA (Af F) σ J)) := isCompact_congSub hσ _ C hCc
  have h8 := modular_of_mem_compact K hKc (k := k) hkK
  rw [map_mul_right_eq, show Measure.modularCharacter g = 1 from hkg.symm.trans h8, one_smul]

end Tensor

theorem unimodularOver_finiteAdele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      UnimodularOver (Af F) σ J := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have hss := GlobalTheory.HermLineZeros.conj_invol hσ
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hσ
  exact GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_forall (Af F) hss
    (fun _ _ h => isUnimodularLC_finiteAdele σ hss (sub_ne_zero.2 hd) (by rw [map_sub, hss, neg_sub]) h) hJ

end GlobalTheory.FiniteAdelicUnimod
end
end

section

namespace GlobalTheory.LocalUnitaryUnimod

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

theorem unimodularOver_adicCompletion :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
      IsHermND σ J → ∀ v : HeightOneSpectrum (𝓞 F), UnimodularOver (Fv F v) σ J := by
  intro F E _ _ _ _ _ σ hσ M J hJ v
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  exact GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_artinian (Fv F v) hσ hJ

end GlobalTheory.LocalUnitaryUnimod
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

theorem _root_.GlobalTheory.T.archimedean_unitaryGroup_stabilisers_unimodular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → UnimodularOver (Ainf F) σ J := by
  first | exact @GlobalTheory.ArchUnitaryUnimod.unimodularOver_infinite | exact GlobalTheory.ArchUnitaryUnimod.unimodularOver_infinite | (intros; apply GlobalTheory.ArchUnitaryUnimod.unimodularOver_infinite <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

theorem _root_.GlobalTheory.T.adelic_unitaryGroup_stabilisers_unimodular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → UnimodularOver (AF F) σ J := by
  first | exact @GlobalTheory.AdelicStabUnimod.unimodularOver_adele | exact GlobalTheory.AdelicStabUnimod.unimodularOver_adele | (intros; apply GlobalTheory.AdelicStabUnimod.unimodularOver_adele <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.VolumeIndep

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open GlobalTheory.VolTransport GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence
open scoped TensorProduct Matrix ENNReal

theorem isFundamentalDomain_map {G H : Type} [Group G] [Group H] [MeasurableSpace G] [MeasurableSpace H]
    (φ : G ≃* H) (hc : Measurable φ) (hc' : Measurable φ.symm) (Γ : Subgroup G) (Γ' : Subgroup H)
    (hQ : ∀ g, g ∈ Γ ↔ φ g ∈ Γ') (μ : Measure G) (𝓕 : Set G) :
    IsFundamentalDomain Γ 𝓕 μ ↔ IsFundamentalDomain Γ' (φ '' 𝓕) (μ.map φ) := by
  let ψ : G ≃ᵐ H := ⟨φ.toEquiv, hc, hc'⟩
  have hψ : MeasurePreserving ψ μ (μ.map φ) := ⟨ψ.measurable, rfl⟩
  constructor
  · intro h
    have e : φ '' 𝓕 = φ.symm ⁻¹' 𝓕 := φ.toEquiv.image_eq_preimage_symm 𝓕
    rw [e]
    exact h.preimage_of_equiv (f := φ.symm) (MeasurePreserving.symm ψ hψ).quasiMeasurePreserving
      (e := fun γ => ⟨φ γ, (hQ γ).1 γ.2⟩)
      ⟨fun a b hab => Subtype.ext (φ.injective (congrArg Subtype.val hab)),
        fun b => ⟨⟨φ.symm b, (hQ _).2 (by simp)⟩, Subtype.ext (by simp)⟩⟩
      fun γ y => by
        show φ.symm (φ γ * y) = γ * φ.symm y
        rw [map_mul, φ.symm_apply_apply]
  · intro h
    have e : 𝓕 = φ ⁻¹' (φ '' 𝓕) := (φ.injective.preimage_image 𝓕).symm
    rw [e]
    exact h.preimage_of_equiv (f := φ) hψ.quasiMeasurePreserving
      (e := fun γ => ⟨φ.symm γ, (hQ _).2 (by simp)⟩)
      ⟨fun a b hab => Subtype.ext (φ.symm.injective (congrArg Subtype.val hab)),
        fun b => ⟨⟨φ b, (hQ b).1 b.2⟩, Subtype.ext (by simp)⟩⟩
      fun γ y => by
        show φ (φ.symm γ * y) = γ * φ y
        rw [map_mul, φ.apply_symm_apply]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isoPair_of_isometry (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V)
    (he : ∀ x y, V'.hT (e x) (e y) = V.hT x y) :
    IsoPair (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram V'.gram
      (LinearMap.toMatrix V.frame V'.frame e.toLinearMap)
      (LinearMap.toMatrix V'.frame V.frame e.symm.toLinearMap) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp]; simp
  · rw [← LinearMap.toMatrix_comp]; simp
  · exact GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat_isom D.sp.cm V V' e.toLinearMap he
  · exact GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat_isom D.sp.cm V' V e.symm.toLinearMap (fun x y => by
      have := he (e.symm x) (e.symm y)
      rw [e.apply_symm_apply, e.apply_symm_apply] at this
      exact this.symm)

theorem isVolMeas_map (V V' : HSp D) {T : Matrix (Fin V'.rank) (Fin V.rank) D.host.E}
    {T' : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}
    (h : IsoPair (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram V'.gram T T')
    (hL : ∀ x ∈ L0c D V, T *ᵥ x ∈ L0c D V') (hL' : ∀ x ∈ L0c D V', T' *ᵥ x ∈ L0c D V)
    (P Q : ℕ) (μ : Measure (GA D V)) (hμ : IsVolMeas D V P Q μ) : IsVolMeas D V' P Q (μ.map (conjA h)) := by
  have c1 := conjA_continuous h
  have c2 : Continuous (conjA h).symm := conjA_continuous h.symm
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V'.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V'.gram
  have := hμ.1
  have hτ : ∀ (ρ : D.what₂.Tau) a, embOf D ρ ((D.sp.cm.sig : D.host.E →+* D.host.E) a) =
      starRingEnd ℂ (embOf D ρ a) := fun ρ a => D.sp.cm.cmUnram.2.1 _ a
  refine ⟨MulEquiv.isHaarMeasure_map μ (conjA h) c1 c2, hμ.2.1, fun θ hθ => ⟨?_, ?_⟩⟩
  · obtain ⟨A, hA⟩ := (hμ.2.2 θ hθ).1
    exact ⟨_, fun ρ => frame_transport h.symm (embOf D ρ) (hτ ρ) _ (A ρ) (hA ρ)⟩
  · intro A hA B hB
    have key := (hμ.2.2 θ hθ).2 _
      (fun ρ => frame_transport h (embOf D ρ) (hτ ρ) _ (A ρ) (hA ρ)) B hB
    let H : GA D V ≃ₜ GA D V' := ⟨(conjA h).toEquiv, c1, c2⟩
    refine Eq.trans (H.toMeasurableEquiv.map_apply _) ?_
    refine Eq.trans (congrArg μ ?_) key
    ext g
    refine and_congr (stab_transport h hL hL' g) ?_
    refine forall_congr' fun ρ => exists_congr fun b => and_congr Iff.rfl ?_
    refine Iff.trans ?_ (frame_iff h (embOf D ρ) _ (A ρ) _)
    rw [← conjA_infMat h g (hθ ρ)]
    rfl

theorem latticeIndependence (D : D7) : LatticeIndependence D := by
  intro W P Q _ L L' hL hU hL' hU' μ
  exact ⟨fun h => GlobalTheory.VolumeRatioTypings.isVolMeas_reLat (withLattice W L hL hU) L' hL' hU' h
      (GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D W μ h.1),
    fun h => GlobalTheory.VolumeRatioTypings.isVolMeas_reLat (withLattice W L' hL' hU') L hL hU h
      (GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D W μ h.1)⟩

theorem isometryTransport (D : D7) : IsometryTransport D := by
  intro V V' P Q _ _ e he hL
  have h := isoPair_of_isometry V V' e he
  have c1 := conjA_continuous h
  have c2 : Continuous (conjA h).symm := conjA_continuous h.symm
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V'.gram
  have l1 := mem_std_lattice_iff_integral_coords D V V' e.toLinearMap fun x => (hL x).1
  have l2 := mem_std_lattice_iff_integral_coords D V' V e.symm.toLinearMap fun x hx => (hL _).2 (by simpa using hx)
  have hQ : ∀ g, g ∈ GQ V ↔ conjA h g ∈ GQ V' := fun g => ⟨conjA_rat h g, fun hg => by
    have := conjA_rat h.symm _ hg
    rwa [← conjA_symm h, MulEquiv.symm_apply_apply] at this⟩
  refine ⟨⟨conjA h, c1, c2⟩, fun g => ?_, hQ, fun μ => ⟨isVolMeas_map V V' h l1 l2 P Q μ, fun hμ => ?_⟩,
    fun μ _ 𝓕 => isFundamentalDomain_map (conjA h) c1.measurable c2.measurable (GQ V) (GQ V') hQ μ 𝓕⟩
  · have e1 := conjA_mat h g
    have e2 := h.adelic.2.1
    unfold Intertwines pointMatrix baseChange frameMatrix
    refine (congrArg (· * _) e1).trans ?_
    show _ * _ * _ * _ = _
    rw [Matrix.mul_assoc, e2, Matrix.mul_one]
  · have k := isVolMeas_map V' V h.symm l2 l1 P Q _ hμ
    have e3 : Measure.map (conjA h.symm) (Measure.map (conjA h) μ) = μ := by
      refine (Measure.map_map c2.measurable c1.measurable).trans ?_
      rw [show ((conjA h).symm : _ → _) ∘ (conjA h) = id from funext (conjA h).symm_apply_apply, Measure.map_id]
    exact e3 ▸ k

theorem volumeInvariance (D : D7) : VolumeInvariance D := by
  intro hT V V' P Q hV hV' ⟨e, he⟩
  have pos : ∀ W : HSp D, HasSignatureEverywhere W P Q → 0 < D.vol W := fun W hW => by
    obtain ⟨⟨μ, hμ⟩, hall⟩ := hT W P Q hW.1 hW.2
    obtain ⟨⟨𝓕, h𝓕⟩, hv⟩ := hall μ hμ
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig W.gram
    have := hμ.1
    have : Countable (GQ W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ W)
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ W) μ
    have h𝓕' : IsFundamentalDomain (GQ W) 𝓕 μ := h𝓕
    have := h𝓕'.measure_ne_zero (NeZero.ne μ)
    rw [hv 𝓕 h𝓕] at this
    exact ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 this)
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular.IsVol D V P Q (D.vol V) := ⟨pos V hV, hT V P Q hV.1 hV.2⟩
  have h2 := GlobalTheory.VolumeRatioTypings.isVol_of_isometry V V' e he h1
  obtain ⟨⟨μ, hμ⟩, hall⟩ := hT V' P Q hV'.1 hV'.2
  obtain ⟨⟨𝓕, h𝓕⟩, hv⟩ := hall μ hμ
  exact (ENNReal.ofReal_eq_ofReal_iff (pos V hV).le (pos V' hV').le).1
    (((h2.2.2 μ hμ).2 𝓕 h𝓕).symm.trans (hv 𝓕 h𝓕))

theorem volumeIndependence (D : D7) : VolumeIndependence D :=
  ⟨latticeIndependence D, isometryTransport D, volumeInvariance D⟩

end GlobalTheory.VolumeIndep
end
end

section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem chi_last_step_finite_order_symTie : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), (∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)) → ∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U, (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) := by
  intro D u Ch chOf Tf hζ
  have hpos : ∀ i, 0 < D.host.g i * (D.host.g i - 1) := fun i =>
    Nat.mul_pos (D.host.g_prime i).pos (Nat.sub_pos_of_lt (D.host.g_prime i).one_lt)
  refine ⟨∏ i, D.host.g i * (D.host.g i - 1), Finset.prod_pos fun i _ => hpos i, ?_⟩
  refine GlobalTheory.gLevH_chi_pow_eq_one_and_mem_range _ _ _ _ _ _ _ _ _ _ _ _ _ Tf.glevM D.what₂.LL D.what₂.embLL _ D.host.g_prime ?_
  intro a v h M
  have key : (∃ r : D.what₂.LL, D.what₂.embLL r = ((Tf.lamM a v h M : ℂˣ) : ℂ)) ∧
      (((Tf.lamM a v h M : ℂˣ) : ℂ) ≠ 0 → ((Tf.lamM a v h M : ℂˣ) : ℂ) ^ (D.host.g a * (D.host.g a - 1)) = 1) := by
    rw [Tf.lamM_eq]
    unfold lamSym
    exact GlobalTheory.lamJ_mem_range_and_pow_eq_one _ D.what₂.LL D.what₂.embLL _ (D.host.g_prime a) (GlobalTheory.T.card_residue_field_totally_real_type_prime D a v h) (hζ a).1 (hζ a).2
      _ _ _ _ _ _ _ _
  refine ⟨?_, key.1⟩
  obtain ⟨c, hc⟩ : D.host.g a * (D.host.g a - 1) ∣ ∏ i, D.host.g i * (D.host.g i - 1) :=
    Finset.dvd_prod_of_mem (fun i => D.host.g i * (D.host.g i - 1)) (Finset.mem_univ a)
  rw [hc, pow_mul, key.2 (Units.ne_zero _), one_pow]

end GlobalTheory
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem norm_kappa_sq_mul_norm_det : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∀ u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ‖ι B.kappa‖ ^ 2 * ‖ι (LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))‖ = 1 := by
  intro D cc δ B hcc hδ q _ hq2 hsplit hcop ι u hu h1 h2 h3
  obtain ⟨γ, hγ, hdet⟩ := GlobalTheory.T.unitary_standard_at_q_from_isometry_over_field D cc δ B hcc hδ q hq2 hsplit hcop ι u hu h1 h2 h3
  rw [hdet]
  exact GlobalTheory.T.norm_kappa_sq_mul_det_isometry_eq_one D B.γ₀ γ B.kc q hq2 hsplit hγ ι

end GlobalTheory.MomN
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.translate_normalized_vector_integral_comb_tensor_power : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → EqAt D p (StandardLatticesGL3.stdL D N) L → EqAt D p (StandardLatticesGL3.stdL D N') L' → ∀ t : VC D N N', TorsPrime D p (La D B.tor L L') t → ∃ (m : ℕ) (c : Fin m → ℂ) (s : Fin m → VC D N N'), (∀ k, c k ∈ Qbar ∧ IsIntP (lamC lam (c k))) ∧ (∀ k, TorsPrime D p (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (s k)) ∧ U D B.tor t (B.eNat χ N N' L L') = fun z => ∑ k, c k * U D B.tor (s k) (B.thZero N N') z := by
  first | exact @GlobalTheory.MomN.transl_normVec_int | exact GlobalTheory.MomN.transl_normVec_int | (intros; apply GlobalTheory.MomN.transl_normVec_int <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem _root_.GlobalTheory.T.exists_integral_period_element : EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta → ThetaConstantWeber.ThetaWeberStatement →
    ∀ (D : D7), Formalism.MainNotions.GL3Theta.admJ D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
      [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t →
      ∃ X : M, X ≠ 0 ∧ IsIntegral ℤ (X : ℂ) ∧ ∀ (ρ : M →ₐ[ℚ] ℂ) (ω₁ τ : ℂ), ω₁ ≠ 0 → 0 < τ.im →
        JacobiThetaHalfCharacteristic.IsPeriodLattice (lamConj M ρ (lamOf D cc δ)) ω₁ τ → ∀ a b : Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar a b →
        JacobiThetaHalfCharacteristic.thetaChar a b (t ρ / ω₁) τ = 0 →
        ‖ρ X‖ = (‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ / ‖ModularForm.eta τ‖) ^ 12 := by
  first | exact @GlobalTheory.IntegralX.exists_integral_theta_ratio | exact GlobalTheory.IntegralX.exists_integral_theta_ratio | (intros; apply GlobalTheory.IntegralX.exists_integral_theta_ratio <;> assumption)
end
