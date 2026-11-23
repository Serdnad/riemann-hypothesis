module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle052
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedLvalueNeZeroEdge
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalCongruenceFunctionMemAdjoinJSiegelUnits
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle292
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle130
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainEqDlogCombinationFiniteLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle077
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle294
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Doubling

open scoped TensorProduct NNReal Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

theorem eq_one_of_forall_norm_pow_sub_one_le {A : Type} [NormedRing A] [NormedAlgebra ℂ A] {x : A}
    (h : ∀ m : ℕ, ‖x ^ m - 1‖ ≤ 1 / 2) : x = 1 := by
  apply GlobalTheory.SmoothFix.eq_one_of_pow_norm_sub_one_le_half <;> assumption

theorem nonarchimedeanGroup_of_isCompact_isOpen {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TotallyDisconnectedSpace H] {K : Subgroup H} (hc : IsCompact (K : Set H)) (ho : IsOpen (K : Set H)) :
    NonarchimedeanGroup H :=
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  haveI : NonarchimedeanGroup K := ⟨fun U hU => by
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_interior (s := U))
      (mem_interior_iff_mem_nhds.2 hU)
    exact ⟨N.toOpenSubgroup, hN.trans interior_subset⟩⟩
  NonarchimedeanGroup.nonarchimedean_of_emb K.subtype ho.isOpenEmbedding_subtypeVal

section General

variable {G : Type} [Group G] {K : Subgroup G} {Φ : G → ℂ}


variable [TopologicalSpace G] [ContinuousMul G]

end General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

section Groups

variable {m : ℕ} (J : Matrix (Fin m) (Fin m) E)

theorem totallyDisconnectedSpace_GLoc (v : HeightOneSpectrum (𝓞 F)) : TotallyDisconnectedSpace (GLoc σ J v) := by
  haveI : TotallyDisconnectedSpace (Fv F v ⊗[F] E) := by
    obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
    exact e.symm.totallyDisconnectedSpace
  haveI : TotallyDisconnectedSpace (Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin m → Fin m → Fv F v ⊗[F] E))
  exact ⟨isTotallyDisconnected_of_image (f := fun g => (matHom _ σ J g).1)
    (Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous).continuousOn
    (Units.val_injective.comp (matHom_injective _ σ J)) (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem totallyDisconnectedSpace_GFin : TotallyDisconnectedSpace (GFin σ J) :=
  haveI := totallyDisconnectedSpace_GLoc σ J
  ⟨isTotallyDisconnected_of_image (f := fun g v => projFinLoc σ J v g)
    (continuous_pi fun v => continuous_projFinLoc σ J v).continuousOn
    (fun _ _ e => GFin_ext σ J (congrFun e)) (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem nonarchimedeanGroup_GLoc (v : HeightOneSpectrum (𝓞 F)) : NonarchimedeanGroup (GLoc σ J v) :=
  haveI := totallyDisconnectedSpace_GLoc σ J v
  haveI := isLattice_stdLattice (E := E) (n := m)
  nonarchimedeanGroup_of_isCompact_isOpen (isCompact_stabLoc σ J (stdLattice E m) v)
    (isOpen_stabLoc σ J (stdLattice E m) v)

theorem nonarchimedeanGroup_GFin : NonarchimedeanGroup (GFin σ J) :=
  haveI := totallyDisconnectedSpace_GFin σ J
  haveI := isLattice_stdLattice (E := E) (n := m)
  nonarchimedeanGroup_of_isCompact_isOpen (isCompact_levelOffFin σ J (stdLattice E m) ∅)
    (isOpen_levelOffFin_empty σ J (stdLattice E m))

variable {σ J}

end Groups

variable {σ} {n : ℕ} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {L : Submodule (𝓞 E) (Fin n → E)}
  [Submodule.IsLattice E L]

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Record

end GlobalTheory.Doubling

end
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.memLp_two_of_cosh_decay_unitaryPQCover : GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.CoshIntegral → ∀ (p q n : ℕ), p + q < n → ∀ (T : GrpData p q) (f : T.G → ℂ) (C : ℝ), Continuous f → (∀ k ∈ T.Kset, ∀ X ∈ pR p q, ‖f (k * T.expt X)‖ ≤ C * decay n X) → MemLp f 2 T.haar := by
  first | exact @GlobalTheory.CoshSqInt.memLp_two_of_decay | exact GlobalTheory.CoshSqInt.memLp_two_of_decay | (intros; apply GlobalTheory.CoshSqInt.memLp_two_of_decay <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lowestKType_of_irreducible_generated_module : ∀ (p q : ℕ) (M : GKMod p q) (Λ : Ix p q → ℚ) (W : Submodule ℂ M.V), IrrGK M → FiniteDimensional ℂ W → KStable M.act W → (∀ N : Submodule ℂ M.V, N ≤ W → KStable M.act N → N = ⊥ ∨ N = W) → (∃ e ∈ W, IsHW M.act Λ e) → (∀ e ∈ W, KilledByLower M.act e) → genSub M.act (W : Set M.V) = ⊤ → IsLowestType M Λ W ∧ Module.finrank ℂ ↥(hwSub M.act Λ) = 1 ∧ ∃ N : ℕ → Submodule ℂ M.V, (∀ m, FiniteDimensional ℂ (N m)) ∧ (⨆ m, N m) = ⊤ ∧ ∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, M.act (Eab (Sum.inl i) (Sum.inl i)) x = (((∑ i : Fin p, Λ (Sum.inl i) : ℚ) : ℂ) + m) • x := by
  first | exact @GlobalTheory.LowestType.lowest | exact GlobalTheory.LowestType.lowest | (intros; apply GlobalTheory.LowestType.lowest <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

theorem _root_.GlobalTheory.T.sum_norm_entries_le_sum_singularValues : ∀ (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ), ∑ i, ∑ j, ‖B i j‖ ≤ (((p + q : ℕ) : ℝ) + 1) / 2 * ∑ i ∈ Finset.range (min p q), singVal B i := by
  first | exact @GlobalTheory.CartanInt.Frob.sum_norm_le_sum_singVal | exact GlobalTheory.CartanInt.Frob.sum_norm_le_sum_singVal | (intros; apply GlobalTheory.CartanInt.Frob.sum_norm_le_sum_singVal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

theorem _root_.GlobalTheory.T.measurable_coshPow' : ∀ (p q : ℕ) (c : ℝ), Measurable (coshPow c : UpqT p q → ℝ) := by
  first | exact @GlobalTheory.CoshPowMeas.measurable_coshPow | exact GlobalTheory.CoshPowMeas.measurable_coshPow | (intros; apply GlobalTheory.CoshPowMeas.measurable_coshPow <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNRecip

theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (M : ℕ) (f : T.K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f) → ∀ ζ : Ω, IsPrimitiveRoot ζ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s ζ = ζ ^ d → ∀ γ γ' : SL(2, ℤ), Cong M d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  intro Ω _ _ _ ε T M f hM hf ζ hζ s d hsd γ γ' hc
  obtain ⟨N₀, hN₀, hrec⟩ := GlobalTheory.T.exists_level_gal_sl_commute Ω ε T f
  set N := N₀ * M with hNdef
  have hN : 0 < N := Nat.mul_pos hN₀ hM
  obtain ⟨⟨d', hd'⟩, hu⟩ := GlobalTheory.T.galois_exponent_rootOfUnity_expTwoPiI Ω ε s N hN
  obtain ⟨u, hu1, -⟩ := hu d' hd'
  have hunit : IsUnit ((d' : ℤ) : ZMod N) := hu1 ▸ u.isUnit
  set ω := eOm ε (1 / (N : ℚ)) with hω
  have hωp : IsPrimitiveRoot ω N := (GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε).2.2.2.2.1 N hN
  have hωM : IsPrimitiveRoot (ω ^ N₀) M := hωp.pow hN rfl
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨i, -, hi⟩ := hωM.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hsζ : s ζ = ζ ^ d' := by
    rw [← hi, map_pow, map_pow, hd', ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul]
    ring_nf
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
  have hdd : (d : ZMod M) = d' := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    have := (hζ.zpow_eq_one_iff_dvd (d' - d)).1 (by
      rw [zpow_sub₀ hζ0, ← hsd, ← hsζ, div_self]; exact (map_ne_zero s).2 hζ0)
    exact this
  obtain ⟨hl1, hl2⟩ := GlobalTheory.T.slTwoDiagConjCongruence_lift_level M N d d' hN (Dvd.intro_left N₀ rfl) hdd hunit
  obtain ⟨γ'', hc'', hκ⟩ := hl1 γ γ' hc
  have hact := GlobalTheory.T.modularFunctionFractionField_sl_rightAction Ω ε T
  have hinv : ∀ δ' ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL δ') (T.gal s f) = T.gal s f := by
    intro δ' hδ'
    obtain ⟨δ, hδ, hcδ⟩ := hl2 δ' hδ'
    have := hrec N hN (Dvd.intro M rfl) s d' hd' δ δ' hcδ
    rw [hf δ hδ] at this
    exact this.symm
  rw [hrec N hN (Dvd.intro M rfl) s d' hd' γ γ'' hc'']
  have hγ' : γ' = (γ' * γ''⁻¹) * γ'' := by group
  rw [hγ', map_mul, hact.2, hinv _ hκ]

end GlobalTheory.FNRecip
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim : ∀ (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ) (w : ℝ), Odd k → 0 < N → 0 < M → Prim k N χ g → ((k : ℝ) + 1) / 2 ≤ w → χ (-1) = -1 ∧ ∃ v : ℂ, v ≠ 0 ∧ Tendsto (fun s : ℝ => LSeries (fun n => φ n * g n) ((w + s : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 v) := by
  first | exact @GlobalTheory.EisM.twisted_lvalue_ne_zero_edge | exact GlobalTheory.EisM.twisted_lvalue_ne_zero_edge | (intros; apply GlobalTheory.EisM.twisted_lvalue_ne_zero_edge <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.principalCongruenceFunction_mem_adjoin_j_siegelUnits : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (M c : ℕ), 0 < M → 1 < c → Nat.Coprime c 6 → c ≡ 1 [MOD M] → ∀ f : X.K, Inv X (CongruenceSubgroup.Gamma M) f → f ∈ IntermediateField.adjoin Ω ({X.jK} ∪ {g | ∃ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) ∧ g = siegel X c ![(a : ℚ) / M, (b : ℚ) / M]}) := by
  first | exact @GlobalTheory.KZ.FracGen.fracGen | exact GlobalTheory.KZ.FracGen.fracGen | (intros; apply GlobalTheory.KZ.FracGen.fracGen <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.exists_kummerCharacterAtLevel_of_mem_kummerModule : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], JHol X → ∀ (n : ℕ), ∀ x ∈ X.A l, ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ := by
  first | exact @GlobalTheory.KZ.H3.exists_kum_of_mem_A | exact GlobalTheory.KZ.H3.exists_kum_of_mem_A | (intros; apply GlobalTheory.KZ.H3.exists_kum_of_mem_A <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.r1_smul_and_kmap_of_r1_linear_laws : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], (∀ (x x' : X.Khat l) (h h' : ℂ → ℤ_[l]), R1 X l x h → R1 X l x' h' → R1 X l (x + x') (h + h')) ∧ R1 X l 0 0 ∧ (∀ (c : ℤ_[l]) (x : X.Khat l) (h : ℂ → ℤ_[l]), R1 X l x h → R1 X l (c • x) (c • h)) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (x : X.Khat l) (h : ℂ → ℤ_[l]), 0 < m.det → R1 X l x h → R1 X l (X.kmap l (X.sl (toGQ m)).toRingEquiv x) (fun z => h (mob (toGQ m) z))) := by
  first | exact @GlobalTheory.KZ.H3.isKummerPotentialIncrement_linear_laws | exact GlobalTheory.KZ.H3.isKummerPotentialIncrement_linear_laws | (intros; apply GlobalTheory.KZ.H3.isKummerPotentialIncrement_linear_laws <;> assumption)
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.kummerCochain_eq_dlog_combination_finiteLevel : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι →
  ∀ (k : ℤ) (w : (On p n)ˣ) (α β : On p n), IsDlog p n (w : On p n) α β →
  ∀ r : Ω, r ^ (p ^ n) = (T.ζ n - 1) ^ k * ι w →
  ∀ a lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T n) r a →
    IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq →
    Cob1 n (Gn T n) (fun g => (p : Ω) ^ c * ((a g).val : Ω) - (p : Ω) ^ c * ι α * ((lq g).val : Ω) -
      (p : Ω) ^ c * (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1)) * ((lz g).val : Ω)) := by
  first | exact @GlobalTheory.KumDlog.kummer_eq_dlog | exact GlobalTheory.KumDlog.kummer_eq_dlog | (intros; apply GlobalTheory.KumDlog.kummer_eq_dlog <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

theorem _root_.GlobalTheory.T.tensorIdeleNormalizedAbs_ideleHalfAtInfinity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → absE F E (halfE F E) = ((4 : ℝ≥0) ^ Fintype.card (InfinitePlace F))⁻¹ := by
  first | exact @GlobalTheory.Eis.Conv.absE_halfE | exact GlobalTheory.Eis.Conv.absE_halfE | (intros; apply GlobalTheory.Eis.Conv.absE_halfE <;> assumption)
end
