module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle321
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isotropicIntegral_invariant_heisenberg_first_vars : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), (∀ y y', (j y).1 ⬝ᵥ (j y').2 = (j y').1 ⬝ᵥ (j y).2) →
    ∀ (y₀ : Fin N → Fv F v) (φ₁ φ₂ : (κ → Fv F v) → ℂ),
      lagInt ψ μ ν j (boxFun (schr ψ (j y₀) φ₁) φ₂) = lagInt ψ μ ν j (boxFun φ₁ φ₂) := by
  first | exact @GlobalTheory.LagIntTransl.main | exact GlobalTheory.LagIntTransl.main | (intros; apply GlobalTheory.LagIntTransl.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open MeasureTheory

namespace GlobalTheory.BlockForms.CuspConst

theorem continuous_unip (E : Type) [Field E] [NumberField E] (d r' : ℕ) :
    Continuous fun x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E => GlobalTheory.CuspRep.unip x := by
  have hn : Continuous fun x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E => (GlobalTheory.CuspRep.nilM x : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [GlobalTheory.CuspRep.nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add hn
  · exact continuous_const.sub hn


open GlobalTheory.Cusp GlobalTheory.AutomorphicL2Unitary in
theorem isCuspidal_comp_blockEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        GlobalTheory.CuspRep.IsCuspidal (fun x => ψ (ι x * g₀)) := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW K _ S l d h ι hι _ hS hk hl ψ hψ g₀ _
  intro r' hr0 hr1 _ _ μ 𝓕 hμ h𝓕 g
  let k : Fin r := ⟨l + r' - 1, by omega⟩
  have hkv : k.val + 1 = l + r' := by simp only [k]; omega
  have hkS : k ∉ S := hS k (by simp only [k]; omega) (by simp only [k]; omega)
  have hSS : S ⊂ insert k S := Finset.ssubset_insert hkS
  set U := GlobalTheory.StdPar.unip σ J X (insert k S) with hU
  set U₀ := GlobalTheory.StdPar.unip σ J X S with hU₀
  have hle : U₀ ≤ U := GlobalTheory.T.standardParabolicUnipotent_mono F E σ hσ n J hJ r X Y hW _ S (Finset.subset_insert _ _)
  haveI : LocallyCompactSpace U₀ := (GlobalTheory.StdPar.isClosed_unip S hσ hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace U := (GlobalTheory.StdPar.isClosed_unip _ hσ hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have cS := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ hσ n J hJ r X Y hW S
  have cS' := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ hσ n J hJ r X Y hW (insert k S)
  have esub : ∀ {N : Subgroup (GAd σ J)}, N ≤ U → (ratPts σ J ⊓ U).subgroupOf N = (ratPts σ J).subgroupOf N := by
    intro N hN
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, hN x.2⟩⟩
  have cinf : ∀ {N : Subgroup (GAd σ J)}, N ≤ U → Cocompact (ratPts σ J) N → Cocompact (ratPts σ J ⊓ U) N := by
    intro N hN hc
    unfold Cocompact
    rw [esub hN]
    exact hc
  have hfΓ : LeftInv (ratPts σ J ⊓ U) ψ := fun γ hγ g => by
    obtain ⟨m, hm, hmL, ν, hν, e⟩ := GlobalTheory.T.rational_unipotentRadical_eq_levi_mul_unipotent F E σ hσ n J hJ r X Y hW S (insert k S) (Finset.subset_insert _ _) γ hγ.1 hγ.2
    rw [e, mul_assoc, hψ.1.leftM m hm hmL, hψ.1.leftN ν hν]
  have hnorm : ∀ p ∈ U, ∀ u ∈ U₀, p * u * p⁻¹ ∈ U₀ := by
    intro p hp u hu
    by_cases hS0 : S = ∅
    · subst hS0
      rw [hU₀, GlobalTheory.StdPar.unip_empty, Subgroup.mem_bot] at hu ⊢
      simp [hu]
    obtain ⟨mS, hmS, hmS'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS0),
      S.max'_mem _, fun k hk => S.le_max' k hk⟩
    have hσσ := sigma_sigma hσ
    have eS := GlobalTheory.ConstTrans.unip_eq_unipFlag F E σ hσ n J hJ r X Y hW S mS hmS hmS'
    have hCS : IsIsoCols σ J (GlobalTheory.StdPar.initCols X mS) := isIsoCols_of_isWittFrame hW hσσ hJ mS.2
    rw [hU₀, eS] at hu ⊢
    exact conj_mem_unipFlag hJ hσσ hCS _ (GlobalTheory.ConstTrans.unip_le_parFlag F E σ hσ n J hJ r X Y hW (insert k S) S mS
      (Finset.subset_insert _ _) hmS hmS' hp) hu
  obtain ⟨π, hπc, hπm, hπs, hπk, hπr⟩ := GlobalTheory.T.exists_blockProjection_flagUnipotentRadical F E σ hσ n J hJ r X Y hW S l d h ι hι hS hk hl r' hr0 hr1 k hkv
  have hrat := GlobalTheory.T.blockEmbedding_rationalGL_mem_rationalPoints F E σ hσ n J hJ r X Y hW l d h ι hι
  have hιc := GlobalTheory.T.continuous_unitaryGLBlockEmbedding_polynomial_entries F E σ hσ n J hJ r X Y hW l d h ι hι
  have hsN := GlobalTheory.T.blockEmbedding_unipotent_mem_flagUnipotentRadical F E σ hσ n J hJ r X Y hW S l d h ι hι hS hk hl r' hr0 hr1 k hkv

  have h0 : constTermOn (ratPts σ J ⊓ U) U ψ (ι g * g₀) = 0 := by
    obtain ⟨μN, 𝓕N, h1, h2, h3⟩ := exists_mass_one cS'
    rw [constTermOn_eq_of_measure_eq_one ((esub le_rfl).symm ▸ h2) h3 hfΓ]
    exact (hψ.2 _ hSS μN 𝓕N h1 h2 h3 (ι g * g₀)).symm
  have key := GlobalTheory.T.cocompact_normal_subgroup_descent_invariants (GAd σ J) (ratPts σ J ⊓ U) U U₀ hle hnorm (cinf le_rfl cS') (cinf hle cS)
    (GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) (GlobalTheory.CuspRep.ratN E d r') (fun x => ι (GlobalTheory.CuspRep.unip x)) π
    (hιc.comp (continuous_unip E d r')) (fun v w => by rw [GlobalTheory.CuspRep.unip_add, map_mul]) hsN hπc hπm hπs hπk
    (fun v hv => by
      obtain ⟨x, rfl⟩ := hv
      refine ⟨?_, hsN _⟩
      have := GlobalTheory.CuspRep.unip_algebraMap (a := d) (r := r') x
      exact this ▸ hrat _)
    (fun a ha => hπr a ha.1) ψ hfΓ hψ.1.cont (fun m hm g => hψ.1.leftN m hm g) μ 𝓕 hμ h𝓕 (ι g * g₀)
  rw [h0, smul_zero] at key
  simpa only [map_mul, mul_assoc] using key

end GlobalTheory.BlockForms.CuspConst

end
end

section

noncomputable section

open NumberField MeasureTheory
open scoped Classical ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem vacuum_smul_realA : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
    (∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))) →
    ∀ g ∈ GinfC X.A, X.om (g, 1) X.vac = (∏ τ, (compAt X.θ τ (Formalism.L2.Theta.mt X.A g)).det ^ P.n τ) • X.vac := by
  intro D cc δ t0 Q P X hX hb g hg
  have hW := hX.2.weil
  have hθ := hX.2.inf
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic D
  have cart : ∀ (V : HSp D), V.gram = 1 → ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun V hV τ => by
    have : gramAt D V τ = 1 := by rw [gramAt, hV, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [this]
    exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  have hmt1 : Formalism.L2.Theta.mt X.B 1 = 1 := by simp [Formalism.L2.Theta.mt]
  have hc1 : ∀ τ, compAt X.θ τ (Formalism.L2.Theta.mt X.B 1) = 1 := fun τ => by
    rw [hmt1, compAt, Matrix.map_one _ (by simp) (by simp)]
  have hA0 : ∀ τ, (gramAt D X.A τ).det ≠ 0 := fun τ => by
    rw [gramAt, hX.1.gramA, Matrix.map_one _ (map_zero _) (map_one _), Matrix.det_one]; exact one_ne_zero
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ X.A hA0 g hg
  have hy : IsDetRoot X.B 1 1 := by simp [IsDetRoot]
  rw [GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D X.ψ hW.std X.A X.B X.θ hθ X.χA X.χB X.om η ⟨e1, e4, e3, e2⟩ hW (fun _ => 1) (fun _ => 1)
    (cart X.A hX.1.gramA) (cart X.B hX.1.gramB) g hg 1 (one_mem _) (fun τ => by rw [one_mul, mul_one])
    (fun τ => by rw [one_mul, mul_one]) x 1 hx hy X.vac hX.2.vac_theta hX.2.vac_fock]
  congr 1
  let c : D.what₂.Tau → ℤ := fun τ => -((P.n τ : ℤ) + P.d)
  have hν : ∀ τ, HasInfExp D (X.χB * (η ^ X.B.rank)⁻¹) τ ((c τ : ℤ) : ℚ) := by
    intro τ
    have := GlobalTheory.VacuumCharacter.hasInfExp_twist (hb τ) (e2 τ) X.B.rank
    convert this using 1
    rw [X.rkB]
    simp only [c]
    push_cast
    ring
  rw [Circle.coe_mul, Circle.coe_inv, hxv _ c hν, map_one, Circle.coe_one, mul_one, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨p, hp, hd⟩ := GlobalTheory.VacuumCharacter.detPlus_one (n := X.A.rank) (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)
    (by simp)
  obtain ⟨d1, -⟩ := hd (compAt X.θ τ (Formalism.L2.Theta.mt X.A g⁻¹)) (compAt X.θ τ (Formalism.L2.Theta.mt X.B 1))
    (by rw [one_mul, mul_one])
  have hpd : p = P.d := by
    have : (p : ℂ) = X.B.rank := by
      rw [Matrix.trace_one, Fintype.card_fin] at hp
      linear_combination -hp / 2
    exact_mod_cast this.trans (congrArg (Nat.cast) X.rkB)
  have e1' : ((1 / 2 : ℂ) • (1 + 1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ) * 1 + (1 / 2 : ℂ) • (1 - 1)) = 1 := by
    rw [mul_one]; module
  have inv : (compAt X.θ τ (Formalism.L2.Theta.mt X.A g)).det * (compAt X.θ τ (Formalism.L2.Theta.mt X.A g⁻¹)).det = 1 := by
    rw [GlobalTheory.VacuumCharacter.det_compAt, GlobalTheory.VacuumCharacter.det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one, map_one, map_one]
  have g0 := left_ne_zero_of_mul_eq_one inv
  rw [d1, hc1, e1', Matrix.det_one, one_pow, one_mul, hpd, eq_inv_of_mul_eq_one_right inv]
  simp only [c]
  rw [zpow_neg, inv_inv, zpow_add₀ g0, zpow_natCast, zpow_natCast, inv_pow]
  field_simp

end GlobalTheory.NormDict
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertFrameUnimod

theorem selfDual_scaled : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s →
  ∀ {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
  ∃ t : F, t ≠ 0 ∧ GlobalTheory.AdelicU.IsSelfDualAt σ (algebraMap F E t • W.Jᵀ) W.L v := by
  intro F E _ _ _ _ _ σ B d W r s hW v w hw
  obtain ⟨t, ht0, s₁, s₂, h1, h2, c1, c2⟩ := GlobalTheory.T.exists_baseField_generator_localDifferent_inertPlace hw
  exact ⟨t, ht0, GlobalTheory.T.skewHermitianLattice_selfDual_smul_transpose_inert σ B W r s hW hw t ht0 s₁ s₂ h1 h2 c1 c2⟩

theorem isConjAt_conjW {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) :
    IsConjAt σ (under_eq_of_isInertAt hw) (GlobalTheory.InertBigCell.conjW σ hw) := fun y =>
  congrArg (fun z => toCompl (under_eq_of_isInertAt hw) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z))
    ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm_apply_apply y)

theorem exists_frame_unimod : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
  ∀ {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  ∃ (b : GL (Fin d) (w.adicCompletion E)) (δ : w.adicCompletion E),
    (∀ u, u ∈ GlobalTheory.LFun.latAt w W.L ↔ GlobalTheory.InertBigCell.InLat (w.adicCompletionIntegers E) b u) ∧
    GlobalTheory.InertBigCell.conjW σ hw δ = δ ∧
    (∀ i j, (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))) i j ∈ w.adicCompletionIntegers E) ∧
    (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))).det ≠ 0 ∧
    (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))).det⁻¹ ∈ w.adicCompletionIntegers E := by
  intro F E _ _ _ _ _ σ B d W r s _hB hW v w hw
  have hc := isConjAt_conjW σ hw
  obtain ⟨t, ht0, hsd⟩ := selfDual_scaled σ B W r s hW hw
  haveI := hW.lat
  obtain ⟨a, ha⟩ := InertChart.exists_isFrameAt (L := W.L) hw (Submodule.IsLattice.fg E W.L) Submodule.IsLattice.span_eq_top
  have hdet : (algebraMap F E t • W.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ ((map_ne_zero _).2 ht0)) (GlobalTheory.FinUniq.det_ne_zero_skew hW)
  obtain ⟨B0, hB0, eB0⟩ := InertChart.exists_gram hw hc hdet hsd ha
  obtain ⟨C, hC⟩ := hB0
  set δ : w.adicCompletion E := algebraMap E (w.adicCompletion E) (algebraMap F E t) with hδdef
  have hδ : GlobalTheory.InertBigCell.conjW σ hw δ = δ := by
    rw [hδdef, InertChart.conj_algebraMap hc, AlgHom.commutes]
  have key : δ • ((a : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (a : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw)) =
      (B0 : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ := by
    rw [eB0, Matrix.transpose_mul, Matrix.transpose_mul]
    have e1 : ((algebraMap F E t • W.Jᵀ).map (algebraMap E (w.adicCompletion E)))ᵀ =
        δ • W.J.map (algebraMap E (w.adicCompletion E)) := by
      ext i j
      simp only [hδdef, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    have e2 : (Formalism.UG.cT (GlobalTheory.InertBigCell.conjW σ hw) (a : Matrix (Fin d) (Fin d) (w.adicCompletion E)))ᵀ =
        (a : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw) := by
      simp [Formalism.UG.cT]
    rw [e1, e2, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hBC : (B0 : Matrix (Fin d) (Fin d) (w.adicCompletion E)) =
      (C : Matrix (Fin d) (Fin d) (Formalism.UG.Ov E w)).map (Formalism.UG.Ov E w).subtype := by
    rw [← hC]; rfl
  have hdetB : (B0 : Matrix (Fin d) (Fin d) (w.adicCompletion E)).det =
      (Formalism.UG.Ov E w).subtype (C : Matrix (Fin d) (Fin d) (Formalism.UG.Ov E w)).det := by
    rw [hBC, ← RingHom.mapMatrix_apply, RingHom.map_det]
  have hCu : IsUnit (C : Matrix (Fin d) (Fin d) (Formalism.UG.Ov E w)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 C.isUnit
  refine ⟨a, δ, fun u => ?_, hδ, fun i j => ?_, ?_, ?_⟩
  · have h1 := ha ((a⁻¹ : GL (Fin d) (w.adicCompletion E)).1 *ᵥ u)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h1
    exact h1.symm
  · rw [key, Matrix.transpose_apply, hBC, Matrix.map_apply]
    exact (C.1 j i).2
  · rw [key, Matrix.det_transpose, hdetB]
    intro h0
    exact hCu.ne_zero (Subtype.ext h0)
  · rw [key, Matrix.det_transpose, hdetB]
    obtain ⟨u, hu⟩ := hCu
    have : (Formalism.UG.Ov E w).subtype (C : Matrix (Fin d) (Fin d) (Formalism.UG.Ov E w)).det *
        (Formalism.UG.Ov E w).subtype (u⁻¹ : (Formalism.UG.Ov E w)ˣ) = 1 := by
      rw [← map_mul, ← hu, Units.mul_inv, map_one]
    rw [inv_eq_of_mul_eq_one_right this]
    exact (u⁻¹ : (Formalism.UG.Ov E w)ˣ).1.2

end GlobalTheory.InertFrameUnimod
end
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact

theorem closeTo_of_mul {D : D7} {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} {g : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)}
    {g' : GL (Fin N') (Formalism.MainNotions.StandardLatticesGL3.AE D)} {z z' : Matrix (Fin N') (Fin N) D.host.E} (m k : ℕ)
    (h : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc (m * k) g g' z z') : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc m g g' z z' := by
  intro i j
  obtain ⟨y, hy, e⟩ := h i j
  refine ⟨(k : Formalism.MainNotions.StandardLatticesGL3.AE D) * y, ?_, by rw [e]; push_cast; ring⟩
  rw [← nsmul_eq_mul]; exact nsmul_mem hy k

theorem exists_closeTo {D : D7} {cc : Ideal (𝓞 D.host.K)} (hc : cc ≠ ⊥) {N N' : ℕ} (g : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D))
    (g' : GL (Fin N') (Formalism.MainNotions.StandardLatticesGL3.AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) (n : ℕ) (hn : 0 < n) :
    ∃ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n g g' z z' := by
  obtain ⟨c, hc1, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  obtain ⟨a, ha0, ha⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (GlobalTheory.NormSum.MovedLattice.inverseHalfDifferent_ne_zero D)
  set b : D.host.E := ((c : D.host.K) : D.host.E) * algebraMap (𝓞 D.host.E) D.host.E a with hb
  set_option synthInstance.maxHeartbeats 200000 in
  have hb0 : b ≠ 0 := by
    refine mul_ne_zero ?_ ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 ha0)
    intro h0
    apply hc0
    have : (c : D.host.K) = 0 := by exact_mod_cast h0
    exact_mod_cast this
  obtain ⟨v, hv⟩ : ∃ v, Formalism.MainNotions.StandardLatticesGL3.inc D b * v = 1 := by
    have hb1 : b * b⁻¹ = 1 := mul_inv_cancel₀ hb0
    exact ⟨Formalism.MainNotions.StandardLatticesGL3.inc D b⁻¹, by rw [← map_mul, hb1, map_one]⟩
  set t : Matrix (Fin N') (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D) := (g' : Matrix (Fin N') (Fin N') (Formalism.MainNotions.StandardLatticesGL3.AE D)) *
    z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) * ((g⁻¹ : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with ht
  choose e w hw he using fun i j => GlobalTheory.NormSum.Expand.approx (t i j * v) n hn
  refine ⟨Matrix.of fun i j => e i j * b, fun i j => ⟨Formalism.MainNotions.StandardLatticesGL3.inc D b * w i j,
    AddSubgroup.subset_closure ⟨c, hc1, _, ha, w i j, hw i j, rfl⟩, ?_⟩⟩
  have h1 : t i j * v * Formalism.MainNotions.StandardLatticesGL3.inc D b = t i j := by
    rw [mul_assoc, mul_comm v, hv, mul_one]
  rw [Matrix.sub_apply, ← ht, Matrix.map_apply, Matrix.of_apply, map_mul]
  linear_combination (Formalism.MainNotions.StandardLatticesGL3.inc D b) * he i j + h1

theorem reads_om_of_vacuum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d) →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ (c : ℂ) (f₀ : WO S T → ℂ), Reads ψ θ hS hT cc δ r e0 f₀ → Reads ψ θ hS hT cc δ r (c • W.Om x y e0) (om (g, h) f₀) →
  ∀ G ∈ TT D (tor0 D cc δ) a d, ∀ f, Reads ψ θ hS hT cc δ r G f → Reads ψ θ hS hT cc δ r (c • W.Om x y G) (om (g, h) f) := by
  intro D ψ θ S T a d hS hT cc δ r hSet e0 W χS χT om hW he0 x y g h hg hh c f₀ hf₀ hc G hG f hf
  have hC := hSet.crv
  have hSD0 : ∀ N : ℕ, Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D N) := by
    intro N
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    rw [← h2]; exact (h1 1).2
  obtain ⟨-, hWL, hint, -⟩ := GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC a d
    (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D cc δ) a d) (Or.inr ⟨_, _, hSD0 _, hSD0 _, rfl⟩)
  have hfix : ∀ v ∈ Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D cc δ) a d, Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) v e0 = e0 := by
    intro v hv
    rw [hWL v hv]; funext w; exact he0.2 v hv w
  have heT : e0 ∈ TT D (tor0 D cc δ) a d :=
    ⟨he0.1, 1, one_pos, fun v hv => by rw [one_nsmul]; exact hfix v hv⟩
  have hTT : ∀ z, Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0 ∈ TT D (tor0 D cc δ) a d := by
    intro z
    obtain ⟨Q, hQ, hz⟩ := GlobalTheory.NormSum.RatExtend.exists_nsmul_mem hC.1.1 δ z
    refine ⟨GlobalTheory.NormSum.RatExtend.Wd_diff _ he0.1, Q, hQ, fun v hv => ?_⟩
    obtain ⟨m, hm⟩ := hint v hv _ hz
    rw [GlobalTheory.NormSum.RatExtend.Hf_nsmul_right, ← GlobalTheory.NormSum.RatExtend.Hf_nsmul_left] at hm
    rw [GlobalTheory.NormSum.RatExtend.Wd_comm _ _ m hm, hfix _ (nsmul_mem hv _)]
  have hRt : ∀ (F : VC D a d → ℂ) (f' : WO S T → ℂ), Reads ψ θ hS hT cc δ r F f' → ∀ z,
      Reads ψ θ hS hT cc δ r (Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F)
        (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) • heisO ψ S T (finPt hS hT r z) f') := by
    intro F f' hF z
    exact (GlobalTheory.T.heisenbergFinitePoint_reads_classicalTranslation ψ θ S T hS hT cc δ r hSet F f' hF z).smul _
  have hR0 : Reads ψ θ hS hT cc δ r (0 : VC D a d → ℂ) (0 : WO S T → ℂ) :=
    ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  have hRsum : ∀ {k : ℕ} (rr : Fin k → ℂ) (F : Fin k → VC D a d → ℂ) (f' : Fin k → WO S T → ℂ),
      (∀ i, Reads ψ θ hS hT cc δ r (F i) (f' i)) →
        Reads ψ θ hS hT cc δ r (∑ i, rr i • F i) (∑ i, rr i • f' i) := by
    intro k rr F f' hF
    have : ∀ s : Finset (Fin k), Reads ψ θ hS hT cc δ r (∑ i ∈ s, rr i • F i) (∑ i ∈ s, rr i • f' i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hR0
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact ((hF i).smul (rr i)).add ih
    exact this Finset.univ
  have key : ∀ zz : Matrix (Fin d) (Fin a) D.host.E, ∃ z',
      W.Om x y (Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ zz) e0) =
        Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') (W.Om x y e0) ∧
      Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ zz) • om (g, h) (heisO ψ S T (finPt hS hT r zz) f₀) =
        Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') • heisO ψ S T (finPt hS hT r z') (om (g, h) f₀) := by
    intro zz
    obtain ⟨m, hm, hl⟩ := W.lift x y zz e0 heT
    obtain ⟨n, hn, hL⟩ := GlobalTheory.T.weilPair_moves_phasedHeisenbergTranslate ψ θ S T hS hT cc δ r hSet χS χT om hW x y g h hg hh f₀ hf₀.1 zz
    obtain ⟨z', hz'⟩ := exists_closeTo hC.1.1 (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D))
      zz (m * n) (Nat.mul_pos hm hn)
    refine ⟨z', hl z' (closeTo_of_mul m n hz'), hL z' (closeTo_of_mul n m ?_)⟩
    rwa [mul_comm] at hz'
  choose z' hz1 hz2 using key
  obtain ⟨k, rr, z, rfl⟩ := GlobalTheory.ThetaSpan.theta_span D cc δ hC a d e0 he0 W.nz G hG
  have hfG := Reads.unique hf (hRsum rr _ _ fun i => hRt e0 f₀ hf₀ (z i))
  subst hfG
  have e1 : c • W.Om x y (∑ i, rr i • Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) e0) =
      ∑ i, rr i • Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z' (z i))) (c • W.Om x y e0) := by
    rw [(GlobalTheory.NormSum.RatExtend.Om_sum W x y Finset.univ rr _ fun i => hTT (z i)).2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz1, GlobalTheory.NormSum.RatExtend.Wd_smul, smul_comm]
  have e2 : om (g, h) (∑ i, rr i • (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) •
        heisO ψ S T (finPt hS hT r (z i)) f₀)) =
      ∑ i, rr i • (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z' (z i))) •
        heisO ψ S T (finPt hS hT r (z' (z i))) (om (g, h) f₀)) := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, hz2]
  rw [e1, e2]
  exact hRsum rr _ _ fun i => hRt _ _ hc (z' (z i))

end GlobalTheory.NormExact
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

theorem _root_.GlobalTheory.T.exists_algebraicNumbers_extension_curveField_conjLattice : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ), Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ GlobalTheory.KerConjMean.ext D δ t0 σ, ∃ ρ' : Qbar →ₐ[ℚ] ℂ,
      (∀ x, Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (D.what₂.embLL x) = σ x) ∧
      lamConj Qbar ρ' (lamOf D D.host.ccK δ) = lamConj (GlobalTheory.KerConjMean.fld D δ t0) ρ (GlobalTheory.KerConjMean.lat D δ) := by
  first | exact @GlobalTheory.ConjExtend.exists_extension_conj | exact GlobalTheory.ConjExtend.exists_extension_conj | (intros; apply GlobalTheory.ConjExtend.exists_extension_conj <;> assumption)
end
