module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftSideFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTestFunctionRayAsymptotic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle051
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import GroundTheory.IdeleRoots.TorusPowers.HeckeTensor
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle045
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleBoundedOnCompact
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle735
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle740
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle737
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle741
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle738
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesUniformBoundCompactStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle739
public import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Vanish

open GlobalTheory.CompanionTheory.SW.WBox (cK)

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

theorem cK_tmul_mul (r : R) (y : R ⊗[F] E) (k : Fin d) :
    cK R b ((r ⊗ₜ[F] (1 : E)) * y) k = r * cK R b y k := by
  have e : (r ⊗ₜ[F] (1 : E)) * y = r • y := by
    rw [Algebra.smul_def]
    rfl
  simp [cK, e]

theorem cK_nat_mul (N : ℕ) (y : R ⊗[F] E) (k : Fin d) :
    cK R b ((N : R ⊗[F] E) * y) k = (N : R) * cK R b y k := by
  have e : (N : R ⊗[F] E) = (N : R) ⊗ₜ[F] (1 : E) := by
    exact (map_natCast (algebraMap R (R ⊗[F] E)) N).symm
  rw [e, cK_tmul_mul]

end Coord

section Scale

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem scale_one (v : HeightOneSpectrum (𝓞 F)) (Q : Set (Fv F v)) (hQ : IsCompact Q) :
    ∃ N : ℕ, 0 < N ∧ ∀ t ∈ Q, (N : Fv F v) * t ∈ v.adicCompletionIntegers F := by
  apply _root_.GlobalTheory.CompanionTheory.SW.LS.scale_one <;> assumption

theorem scale_lat [NumberField E] (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (K : Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ Y ∈ K, (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := by
  apply _root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box.scale_lat <;> assumption

theorem nat_mul_latV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    {Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E} (hY : Y ∈ latV b v) :
    (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := fun a i k => by
  change cK (Fv F v) b ((N : Fv F v ⊗[F] E) * Y a i) k ∈ _
  rw [cK_nat_mul]
  exact mul_mem (natCast_mem _ N) (hY a i k)

end Scale

theorem exists_compact {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (J : Matrix (Fin 1) (Fin 1) E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (hT : IsTest σ J b S φ A) :
    ∃ K : Set (Fin 1 → Fin 1 → AF F ⊗[F] E), IsCompact K ∧
      ∀ Y : Fin 1 → Fin 1 → AF F ⊗[F] E, (∀ v, projV v (projFin Y) ∈ A v) → projInf Y ∈ tsupport φ → Y ∈ K := by
  obtain ⟨hφc, hφs, hφ0, -, hAS, hAoff⟩ := hT
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 1
  obtain ⟨u1, u2⟩ := GlobalTheory.T.adelic_tuple_compact_sets F E σ hcm d b 1 1
  have hSc : ∀ v, ∃ N : ℕ, 0 < N ∧ (v ∈ S → ∀ Y ∈ A v, (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v) := fun v => by
    by_cases hv : v ∈ S
    · obtain ⟨N, h0, h1⟩ := scale_lat σ hcm b v (A v) (hAS v hv).1
      exact ⟨N, h0, fun _ => h1⟩
    · exact ⟨1, one_pos, fun h => absurd h hv⟩
  choose n hn0 hn using hSc
  set N1 : ℕ := ∏ v ∈ S, n v with hN1
  have hN1p : 0 < N1 := Finset.prod_pos fun v _ => hn0 v
  have hsc : ∀ v, ∀ Y ∈ A v, (fun a i => (N1 : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := fun v Y hY => by
    by_cases hv : v ∈ S
    · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n hv
      have h1 := nat_mul_latV b v c (hn v hv Y hY)
      have e : (fun a i => (N1 : Fv F v ⊗[F] E) * Y a i) = fun a i => (c : Fv F v ⊗[F] E) * ((n v : Fv F v ⊗[F] E) * Y a i) := by
        funext a i
        rw [hN1, hc]
        push_cast
        ring
      rw [e]
      exact h1
    · rw [hAoff v hv] at hY
      exact nat_mul_latV b v N1 hY
  obtain ⟨r1, hr1⟩ := (IsCompact.image hφs t9).bddAbove
  refine ⟨_, u1 N1 r1 hN1p, fun Y hY hs => ⟨fun v => hsc v _ (hY v), hr1 ⟨_, hs, rfl⟩⟩⟩

theorem mem_of_Psi_ne {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E))
    (Y : Fin 1 → Fin 1 → AF F ⊗[F] E) (h : Psi φ A Y ≠ 0) :
    (∀ v, projV v (projFin Y) ∈ A v) ∧ projInf Y ∈ tsupport φ := by
  unfold Psi at h
  by_cases h1 : ∀ v, projV v (projFin Y) ∈ A v
  · refine ⟨h1, subset_tsupport φ ?_⟩
    rw [Set.indicator_of_mem (by exact h1)] at h
    intro h2
    exact h (by simp [h2])
  · rw [Set.indicator_of_notMem (by exact h1)] at h
    exact absurd rfl h

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cont_f : Continuous fun Y : Fin 1 → Fin 1 → AF F ⊗[F] E => GroundTheory.BlockD.ThmBHecke.adeleEquiv F E (Y 0 0) :=
    GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv.comp (continuous_apply_apply 0 0)

theorem hdiag (t : Eˣ) : GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofE t) = IdeleGroup.diagonal E t := by
    apply Units.ext
    exact GroundTheory.BlockD.ThmBHecke.adeleEquiv_incA (t : E)

theorem mod_mul (y : (AF F ⊗[F] E)ˣ) (t : Eˣ) : (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (y * ofE t)) : ℝ) = (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E y) : ℝ) := by
  rw [map_mul, map_mul, hdiag, IdeleGroup.ideleModule_diagonal, mul_one]

theorem exists_term (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (y : (AF F ⊗[F] E)ˣ)
    (h : Th φ A y ≠ 0) : ∃ X : Fin 1 → Fin 1 → E, X ≠ 0 ∧
      Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X a i)) ≠ 0 := by
  unfold Th at h
  obtain ⟨X, hX⟩ := not_forall.1 (fun hall => h (ENNReal.tsum_eq_zero.2 hall))
  exact ⟨X.1, X.2, hX⟩

theorem entry_ne {X : Fin 1 → Fin 1 → E} (h : X ≠ 0) : X 0 0 ≠ 0 := fun h0 => h (by
  funext a i
  rw [Subsingleton.elim a 0, Subsingleton.elim i 0, h0]
  rfl)

theorem coe_eq (y : (AF F ⊗[F] E)ˣ) {X : Fin 1 → Fin 1 → E} (h : X 0 0 ≠ 0) :
    ((GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (y * ofE (Units.mk0 _ h)) : IdeleGroup E) : AdeleRing (𝓞 E) E) =
      GroundTheory.BlockD.ThmBHecke.adeleEquiv F E ((y : AF F ⊗[F] E) * inclR (AF F) (X 0 0)) := rfl
end

theorem th_eq_zero_of_large_module : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∃ R : ℝ, ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n → R < md n → Th φ A y = 0 := by
  intro F E _ _ _ _ _ σ hcm J hJ d b S φ A hT
  obtain ⟨K, hK, hmem⟩ := exists_compact σ hcm J b S φ A hT
  obtain ⟨R, hR⟩ := GlobalTheory.T.idele_module_bounded_on_compact E _ (hK.image (cont_f (F := F) (E := E)))
  refine ⟨R, fun y n hn hlt => ?_⟩
  by_contra hne
  obtain ⟨X, hX0, hX⟩ := exists_term φ A y hne
  obtain ⟨h1, h2⟩ := mem_of_Psi_ne φ A _ hX
  have hYK := hmem _ h1 h2
  have ht := entry_ne hX0
  have hle := hR (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (y * ofE (Units.mk0 _ ht)))
    (by rw [coe_eq]; exact ⟨_, hYK, rfl⟩)
  rw [mod_mul, GlobalTheory.T.idele_module_eq_norm_module F E σ hcm y n hn] at hle
  exact absurd hle (not_le.2 hlt)

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Vanish

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem isNm_ofF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (u : (AF F)ˣ) : IsNm σ (ofF u : (AF F ⊗[F] E)ˣ) (u * u) := by
  unfold IsNm
  have hs : sigR (AF F) σ ((u : AF F) ⊗ₜ[F] (1 : E)) = (u : AF F) ⊗ₜ[F] (1 : E) := by
    simp [sigR]
  have e : ((ofF u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (u : AF F) ⊗ₜ[F] (1 : E) := rfl
  rw [e, hs, Units.val_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem ideleEquiv_ofE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (t : Eˣ) :
    GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofE t) = IdeleGroup.diagonal E t := by
  apply Units.ext
  rw [GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv]
  exact GroundTheory.BlockD.ThmBHecke.adeleEquiv_incA (t : E)

theorem exists_unit_decomp (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (θ : ℝ →+* Ainf F) (hθ : Continuous θ)
    (r : ℝ → (AF F)ˣ) (hr : IsRay θ r) :
    ∃ K : Set (AF F ⊗[F] E)ˣ, IsCompact K ∧ ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n →
      ∃ (q : Eˣ) (k : (AF F ⊗[F] E)ˣ) (ε : ℝ), k ∈ K ∧ 0 < ε ∧ y = ofE q * (k * ofF (r ε)) ∧
        md n = ε ^ (2 * Module.finrank ℚ F) := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup E
  refine ⟨(GroundTheory.BlockD.ThmBHecke.ideleEquiv F E).symm '' D,
    hD.image GroundTheory.BlockD.ThmBHecke.continuous_ideleEquiv_symm, fun y n hyn => ?_⟩
  have hd : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hm : 2 * Module.finrank ℚ F ≠ 0 := by omega
  have hn : 0 < md n := (IdeleGroup.ideleModule F n).2
  set m := 2 * Module.finrank ℚ F with hmdef
  set ε : ℝ := md n ^ ((m : ℝ)⁻¹) with hεdef
  have hε : 0 < ε := Real.rpow_pos_of_pos hn _
  have hεm : md n = ε ^ m := (Real.rpow_inv_natCast_pow hn.le hm).symm
  have hray : md (r ε * r ε) = ε ^ m := by
    have h1 := ((GlobalTheory.T.ray_norm_and_module_formula F hcm.1 θ hθ r hr).2 ε hε)
    have h2 : md (r ε * r ε) = md (r ε) * md (r ε) := by simp [md, map_mul]
    rw [h2, h1, hmdef, two_mul, pow_add]
  have hy := GlobalTheory.T.idele_module_eq_norm_module F E σ hcm y n hyn
  have hu := GlobalTheory.T.idele_module_eq_norm_module F E σ hcm (ofF (r ε)) (r ε * r ε) (isNm_ofF σ (r ε))
  set I := GroundTheory.BlockD.ThmBHecke.ideleEquiv F E with hI
  have hker : I (y * (ofF (r ε))⁻¹) ∈ IdeleGroup.normOneSubgroup E := by
    refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
    have hpos : (0 : ℝ) < ε ^ m := pow_pos hε m
    rw [map_mul, map_inv, map_mul, map_inv]
    change ((IdeleGroup.ideleModule E (I y) : ℝ)) *
      ((IdeleGroup.ideleModule E (I (ofF (r ε))) : ℝ))⁻¹ = 1
    rw [hy, hu, hray, hεm]
    exact mul_inv_cancel₀ hpos.ne'
  obtain ⟨t, ht⟩ := hxD _ hker
  refine ⟨t⁻¹, I.symm (IdeleGroup.diagonal E t * I (y * (ofF (r ε))⁻¹)), ε, ⟨_, ht, rfl⟩, hε, ?_, hεm⟩
  apply I.injective
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hI, ideleEquiv_ofE, map_inv, ← hI, map_mul, map_inv]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

end
end

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open GroundTheory.Global PositivityTheory.Rg.Base1
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

variable {F : Type} [Field F] [NumberField F]

theorem exists_strictHenselian_absolutely_closed_local_ring (a : (AF F)ˣ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T ∧ ∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧
      ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F := by
  have h1 : ∀ᶠ v in cofinite, (a : AF F).2 v ∈ v.adicCompletionIntegers F := (a : AF F).2.2
  have h2 : ∀ᶠ v in cofinite, ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F :=
    ((a⁻¹ : (AF F)ˣ) : AF F).2.2
  have h3 := h1.and h2
  rw [eventually_cofinite] at h3
  refine ⟨S ∪ h3.toFinset, Finset.subset_union_left, fun v hv => ?_⟩
  by_contra hc
  exact hv (Finset.mem_union_right _ (h3.mem_toFinset.2 hc))

theorem limit (hE : PositivityTheory.Rg.Mass.Equi) (hF : IsTotallyReal F) (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (r : ℝ → (AF F)ˣ)
    (hr : IsRay θ r) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hli : IsStdInf li)
    (hlam : ∀ v, IsStdV v (lam v)) (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (hG : Continuous G) (hGc : HasCompactSupport G)
    (hG0 : ∀ y, 0 ≤ G y) (hg0 : ∀ v y, 0 ≤ g v y) (hgS : ∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v))
    (a : (AF F)ˣ) :
    Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ Module.finrank ℚ F) * th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (a * r δ))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal ((md a)⁻¹ * ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v))))) := by
  obtain ⟨T, hST, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring a S
  have hφ := GlobalTheory.T.archimedean_cutoff_continuous_compact_support F G a hG hGc
  have hψ := GlobalTheory.T.finite_place_cutoff_continuous_compact_support F S g a hgS
  have h := hE F hF θ hθ li lam hli hlam Unit T (phiA G a) (fun v => psiA S g a v) hφ.1 hφ.2 (fun v _ => hψ v)
  rw [GlobalTheory.T.pure_function_enlarge_finite_set F li lam hli hlam S T G g a hST hT] at h
  simp only [Fintype.card_unit, mul_one] at h
  set d := Module.finrank ℚ F with hd
  have hdpos : d ≠ 0 := (Module.finrank_pos (R := ℚ) (M := F)).ne'

  let P : F → Prop := fun x => ∀ v, v ∉ T → algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F
  let q : ℝ → F → ℝ := fun δ x => phiA G a (fun _ => θ δ * algebraMap F (Ainf F) x) *
    ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) x)
  have hq0 : ∀ δ x, 0 ≤ q δ x := fun δ x => mul_nonneg (hG0 _) (Finset.prod_nonneg fun v _ => by
    unfold psiA
    split_ifs
    exacts [hg0 _ _, zero_le_one, le_rfl])
  let H : ℝ → F → ℝ := fun δ x => if P x then q δ x else 0
  have hH0 : ∀ δ x, 0 ≤ H δ x := fun δ x => by
    simp only [H]
    split_ifs
    exacts [hq0 δ x, le_rfl]
  have hsum : ∀ δ : ℝ, (∑' x : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F},
      phiA G a (fun i => θ δ * algebraMap F (Ainf F) (x.1 i)) * ∏ v ∈ T, psiA S g a v fun i => algebraMap F (Fv F v) (x.1 i)) =
      ∑' x : F, H δ x := by
    intro δ
    let e : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} ≃ {x : F // P x} :=
      (Equiv.funUnique Unit F).subtypeEquiv (fun x => by
        simp only [P, Equiv.funUnique_apply]
        exact ⟨fun hx v hv => hx v hv _, fun hx v hv i => by
          have : i = default := Subsingleton.elim _ _
          rw [this]
          exact hx v hv⟩)
    have e1 := e.tsum_eq (fun x : {x : F // P x} => q δ x.1)
    have e2 : (∑' x : F, H δ x) = ∑' x : {x : F // P x}, q δ x.1 := by
      have := tsum_subtype {x : F | P x} (q δ)
      rw [show (∑' x : {x : F // P x}, q δ x.1) = ∑' x : ({x : F | P x} : Set F), q δ x.1 from rfl, this]
      refine tsum_congr fun x => ?_
      simp only [H, Set.indicator, Set.mem_ofPred_eq]
    rw [e2, ← e1]
    refine tsum_congr fun x => ?_
    simp only [q]
    have c1 : (fun i => θ δ * algebraMap F (Ainf F) (x.1 i)) = fun _ => θ δ * algebraMap F (Ainf F) ((e x).1) := by
      funext i
      have : i = default := Subsingleton.elim _ _
      rw [this]
      rfl
    have c2 : ∀ v, (fun i => algebraMap F (Fv F v) (x.1 i)) = fun _ => algebraMap F (Fv F v) ((e x).1) := by
      intro v
      funext i
      have : i = default := Subsingleton.elim _ _
      rw [this]
      rfl
    rw [c1]
    exact congrArg _ (Finset.prod_congr rfl fun v _ => by rw [c2 v])
  have hz : ∀ δ : ℝ, H δ 0 = H 1 0 := fun δ => by
    simp [H, q]
  have hth : ∀ δ : ℝ, 0 < δ → ENNReal.ofReal (∑' x : F, H δ x) =
      ENNReal.ofReal (H 1 0) + th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (a * r δ) := by
    intro δ hδ
    have hfin : (Function.support (H δ)).Finite := by
      refine (GlobalTheory.T.pure_function_theta_series_invariance F hF θ hθ S T G g a hG hGc hgS hST hT δ hδ).subset fun x hx => ?_
      simp only [Function.mem_support, H] at hx
      by_cases hP : P x
      · rw [ite_eq_left hP] at hx
        exact ⟨hP, hx⟩
      · rw [ite_eq_right hP] at hx
        exact absurd rfl hx
    rw [ENNReal.ofReal_tsum_of_nonneg (hH0 δ) (summable_of_hasFiniteSupport hfin),
      ENNReal.tsum_eq_add_tsum_ite (0 : F), hz δ]
    congr 1
    unfold th
    have e1 := (unitsEquivNeZero (G₀ := F)).tsum_eq (fun x : {x : F // x ≠ 0} => ENNReal.ofReal (H δ x.1))
    have e2 := tsum_subtype {x : F | x ≠ 0} (fun x => ENNReal.ofReal (H δ x))
    have e3 : (∑' x : F, if x = 0 then (0 : ℝ≥0∞) else ENNReal.ofReal (H δ x)) =
        ∑' x : {x : F // x ≠ 0}, ENNReal.ofReal (H δ x.1) := by
      rw [show (∑' x : {x : F // x ≠ 0}, ENNReal.ofReal (H δ x.1)) =
        ∑' x : ({x : F | x ≠ 0} : Set F), ENNReal.ofReal (H δ x.1) from rfl, e2]
      refine tsum_congr fun x => ?_
      by_cases hx : x = 0 <;> simp [hx, Set.indicator]
    rw [e3, ← e1]
    refine tsum_congr fun t => ?_
    rw [GlobalTheory.T.pure_function_translate_ray_units F θ r hr S T G g a hST hT δ hδ t]
    simp only [H, P, q, unitsEquivNeZero_apply_coe]
    split_ifs <;> simp
  set z := ENNReal.ofReal (H 1 0) with hzdef
  have hzt : z ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpow : Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ d)) (𝓝[>] 0) (𝓝 0) := by
    have c : Continuous fun δ : ℝ => ENNReal.ofReal (δ ^ d) := ENNReal.continuous_ofReal.comp (continuous_pow d)
    have := (c.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [hdpos] using this
  have h1 := (ENNReal.tendsto_ofReal h)
  have h2 : Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ d) * z) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hpow (Or.inr hzt)
  have h3 := ENNReal.Tendsto.sub h1 h2 (Or.inr ENNReal.zero_ne_top)
  rw [tsub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : (0 : ℝ) < δ := hδ
  have hne : ENNReal.ofReal (δ ^ d) * z ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hzt
  rw [hsum δ, ENNReal.ofReal_mul (by positivity), hth δ hδ', mul_add]
  exact ENNReal.add_sub_cancel_left hne

theorem psiSide_of_equi : PositivityTheory.Rg.Mass.Equi → PsiSide := by
  intro hE F _ _ hF θ hθ r hr li lam hli hlam S G g hG hGc hG0 hg0 hgS
  refine ⟨GlobalTheory.T.measurable_pure_adelic_function F S G g hG fun v hv => (hgS v hv).1, ?_⟩
  obtain ⟨D, hD, hD1, hDk⟩ := IdeleGroup.exists_isCompact_normOneSubgroup F
  obtain ⟨C, hC⟩ := GlobalTheory.T.theta_series_uniform_bound_compact F hF θ hθ r hr S G g hG hGc hgS D hD
  set d := Module.finrank ℚ F with hd
  have hdpos : d ≠ 0 := (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have hmd : ∀ (a : (AF F)ˣ) (δ : ℝ), 0 < δ → ENNReal.ofReal (md (a * r δ)) = ENNReal.ofReal (md a) * ENNReal.ofReal (δ ^ d) := by
    intro a δ hδ
    rw [md_mul, GlobalTheory.T.module_ray_eq_pow_degree F hF θ r hr δ hδ, ENNReal.ofReal_mul (md_pos a).le]
  refine ⟨⟨C, fun a => ?_⟩, GlobalTheory.T.theta_series_vanishes_large_module F S G g hGc fun v hv => (hgS v hv).2, fun a ha => absurd (Subgroup.mem_top a) ha, fun a _ => ?_⟩
  · set δ : ℝ := md a ^ ((d : ℝ)⁻¹) with hδdef
    have hδ : 0 < δ := Real.rpow_pos_of_pos (md_pos a) _
    have hδd : δ ^ d = md a := Real.rpow_inv_natCast_pow (md_pos a).le hdpos
    set x : (AF F)ˣ := a * (r δ)⁻¹ with hx
    have hxr : x * r δ = a := by simp [hx]
    have hx1 : md x = 1 := by
      have h1 := md_mul x (r δ)
      rw [hxr, GlobalTheory.T.module_ray_eq_pow_degree F hF θ r hr δ hδ, hδd] at h1
      have := md_pos a
      field_simp at h1
      nlinarith [h1]
    have hxn : x ∈ IdeleGroup.normOneSubgroup F := by
      rw [IdeleGroup.normOneSubgroup, MonoidHom.mem_ker]
      exact Subtype.ext hx1
    obtain ⟨k, hk⟩ := hDk x hxn
    have hk' : pr k * x ∈ D := hk
    have e : th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) a =
        th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) ((pr k * x) * r δ) := by
      rw [mul_assoc, hxr, th_pr]
    rw [e, ← hδd]
    exact hC _ hk' δ hδ
  · have hl := limit hE hF θ hθ r hr li lam hli hlam S G g hG hGc hG0 hg0 hgS a
    have hm := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (md a)) hl (Or.inr ENNReal.ofReal_ne_top)
    rw [← ENNReal.ofReal_mul (md_pos a).le, ← mul_assoc, mul_inv_cancel₀ (md_pos a).ne', one_mul] at hm
    refine hm.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [hmd a δ hδ, mul_assoc]

end GlobalTheory.CompanionTheory.BasePsi

end
end
