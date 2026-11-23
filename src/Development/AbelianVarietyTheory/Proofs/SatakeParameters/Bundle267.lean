module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle177
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle741
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle183
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeSpacesOrthogonalOfClassSumInner
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle065
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle177
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.Automorphisms.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceOfEmb

theorem norm_le_one_of_isIntegral' {K : Type} [NormedField K] [IsUltrametricDist K] {x : K}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have := (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at this
  exact_mod_cast this

variable {E : Type} [Field E] [NumberField E] {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_map_le_one (τ : E →+* C) (x : 𝓞 E) : ‖τ (x : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral' ((x.isIntegral_coe).map (τ.toIntAlgHom))

def ballIdeal (τ : E →+* C) : Ideal (𝓞 E) where
  carrier := {x | ‖τ (x : E)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change ‖τ (a : E)‖ < 1 at ha
    change ‖τ (b : E)‖ < 1 at hb
    change ‖τ ((a : E) + (b : E))‖ < 1
    rw [map_add (f := _)]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' := by
    intro c x hx
    change ‖τ (x : E)‖ < 1 at hx
    change ‖τ ((c : E) * (x : E))‖ < 1
    rw [map_mul, norm_mul]
    calc ‖τ (c : E)‖ * ‖τ (x : E)‖ ≤ 1 * ‖τ (x : E)‖ :=
          mul_le_mul_of_nonneg_right (norm_map_le_one τ c) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hx

theorem mem_ballIdeal (τ : E →+* C) (x : 𝓞 E) : x ∈ ballIdeal τ ↔ ‖τ (x : E)‖ < 1 := Iff.rfl

theorem ballIdeal_isPrime (τ : E →+* C) : (ballIdeal τ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_ballIdeal]; simp
  · intro a b hab
    change ‖τ ((a : E) * (b : E))‖ < 1 at hab
    rw [map_mul, norm_mul] at hab
    by_contra h
    push_neg at h
    rw [mem_ballIdeal, mem_ballIdeal] at h
    have ha : ‖τ (a : E)‖ = 1 := le_antisymm (norm_map_le_one τ a) (not_lt.1 h.1)
    have hb : ‖τ (b : E)‖ = 1 := le_antisymm (norm_map_le_one τ b) (not_lt.1 h.2)
    rw [ha, hb] at hab; norm_num at hab

end GlobalTheory.PlaceOfEmb

open GlobalTheory.PlaceOfEmb in
theorem GlobalTheory.PlaceOfEmb.exists_place_of_emb : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (τ : D.host.E →+* Qbar l), ∃ w : PlE D.host, w ∈ placesOver D.host.E l ∧ ∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal := by
  intro D l _ τ
  have hl : ((l : 𝓞 D.host.E)) ∈ ballIdeal τ := by
    rw [mem_ballIdeal]
    simp only [map_natCast]
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hne : ballIdeal τ ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hl
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hl
  refine ⟨⟨ballIdeal τ, ballIdeal_isPrime τ, hne⟩, hl, fun x => Iff.rfl⟩
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigAgree

end GlobalTheory.EigAgree

theorem GlobalTheory.EigAgree.cast_ne_zero {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (f : D.what₂.Mt μ a) (hf : f ≠ 0) :
    (h ▸ f : D.what₂.Mt μ b) ≠ 0 := by
  subst h
  exact hf
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypesAtPin

theorem not_over_g_of_mem_Q (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ D.nd.Q i)
    (k : Fin 2) : w ∉ placesOver D.host.E (D.host.g k) := by
  intro hk
  have hS : w ∈ D.nd.S i := (D.nd.S_def i w).2 ⟨by
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk), D.nd.SQ_l i w (Or.inr hw)⟩
  exact Finset.disjoint_left.1 (D.nd.SQ_disj i) hS hw

end GlobalTheory.TypesAtPin
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompactRepField

theorem exists_hom_of_entries_mem {F E Γ : Type} [Field F] [Field E] [Algebra F E] [Group Γ]
    {a : ℕ} (r : Γ →* GL (Fin a) E) (K : IntermediateField F E)
    (h : ∀ g i j, (r g : Matrix (Fin a) (Fin a) E) i j ∈ K) :
    ∃ r₁ : Γ →* GL (Fin a) ↥K, ∀ g i j,
      ((r₁ g : Matrix (Fin a) (Fin a) ↥K) i j : E) = (r g : Matrix (Fin a) (Fin a) E) i j := by
  let m : Γ →* Matrix (Fin a) (Fin a) ↥K :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, h g i j⟩
      map_one' := by
        ext i j
        simp only [Matrix.of_apply, map_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g g' => by
        ext i j
        simp [Matrix.mul_apply] }
  exact ⟨m.toHomUnits, fun g i j => rfl⟩

theorem exists_continuous_model :
    ∀ (D : D7) (l : ℕ) [Fact l.Prime] (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → ∀ L₀ : FinExt l, ∃ (LL' : FinExt l) (_ : L₀.1 ≤ LL'.1) (ρ₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1), Continuous (fun g => ((ρ₁ g : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1)) ∧ mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ₁ = ρ := by
  intro D l _ a ρ hρ L₀
  obtain ⟨L, hL, h⟩ := exists_finExt_entries_mem l (G D.host.E D.nd.Om) a ρ hρ L₀
  obtain ⟨ρ₁, h₁⟩ := exists_hom_of_entries_mem ρ L.1 h
  refine ⟨L, hL, ρ₁, ?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    refine continuous_induced_rng.2 ?_
    exact (hρ.matrix_elem i j).congr fun g => (h₁ g i j).symm
  · refine MonoidHom.ext fun g => Units.ext ?_
    ext i j
    exact h₁ g i j

end GlobalTheory.CompactRepField
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TieGalAssembly

theorem potCrysIffWD (D : D7) : PotCrysIffWD D.nd D.naut := by
  intro i a r w hw hr
  refine ⟨fun hc => ?_, fun h => (D.naut.wdOf_mono0L i r w hw hr h.1).1 h.2⟩
  suffices hd : D.naut.IsdRW i r w from ⟨hd, (D.naut.wdOf_mono0L i r w hw hr hd).2 hc⟩
  have := D.nd.lPrime i
  obtain ⟨L, hle, hL⟩ := GlobalTheory.T.compactGroup_rep_defined_over_finite_extension (D.nd.l i) _ a r hr (D.nbr i w hw).LL
  obtain ⟨ρ, hρ, rfl⟩ := GlobalTheory.CrysWD.exists_descent r hr L hL
  obtain ⟨-, h2, h1, -⟩ := (D.loc_tie i w hw).2.2 L hle a ρ hρ
  have := L.2
  obtain ⟨K', hK, hc'⟩ := h1.1 hc
  have h3 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ L _ _ hc').1
  have h4 := (GlobalTheory.Per.TiedRestrict.isDR_restrict_iff hK _ (D.locT (D.nd.l i))).2 h3
  refine h2.2 ?_
  unfold IsDR at h4
  unfold LocBridge.IsdRE
  simpa using h4

end GlobalTheory.TieGalAssembly
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.IsoComp

open GlobalTheory.CompRed

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem isoTyp_indep (a : NG.AlgWt L n) {ι : Type} (S : ι → Submodule ℂ (GAf L n → a.W))
    (hS : ∀ i, NG.IsIrrRep a.ρ (S i)) (hinj : ∀ i j, NG.IsoRep (S i) (S j) → i = j) :
    iSupIndep fun i => NG.isoTyp a.ρ (S i) := by
  classical
  haveI hW : FiniteDimensional ℂ a.W := a.alg.1
  have hT := GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n
  have hfin : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ
      {f | f ∈ NG.AFall L n a.ρ ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g}) := by
    intro M hM
    haveI := GlobalTheory.AlgFormsFin.fixedForms_finite L n a.ρ hT hM
    refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n a.ρ M) (Submodule.span_le.2 ?_)
    rintro f ⟨hf, hκ⟩
    exact ⟨hf.1, hκ⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.T.algWt_exists_invForm' L n a
  obtain ⟨B, hB, -⟩ := GlobalTheory.T.class_sum_eq_const_mul_petersson L n a β hβ
  have hG : GlobalTheory.TypeOrthogonality.Good a.ρ B := hB
  exact indep_of_orth (fun x => B x) _ (fun i x hx h0 => pos_zero hG (isoTyp_le _ hx) h0)
    (fun i j hij => isoTyp_orth hG hfin (hS i) (hS j) (fun h => hij (hinj i j h)))

variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem heckeD_mem_isoTyp {ρ : Representation ℂ (GQ L n) W} (S : Submodule ℂ (GAf L n → W))
    (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) (f : GAf L n → W)
    (hf : f ∈ NG.isoTyp ρ S) : NG.heckeD J Dset f ∈ NG.isoTyp ρ S := by
  classical
  rw [GlobalTheory.HeckeScalarAll.heckeD_eq_sum J Dset hfin]
  refine Submodule.sum_mem _ fun c _ => ?_
  split_ifs with hc
  · exact isoTyp_stable S _ f hf
  · exact Submodule.zero_mem _

theorem heckeD_finset_sum {ι : Type} (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) (s : Finset ι) (F : ι → GAf L n → W) :
    NG.heckeD J Dset (∑ i ∈ s, F i) = ∑ i ∈ s, NG.heckeD J Dset (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [GlobalTheory.HeckeScalarAll.heckeD_zero J Dset hfin]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.HeckeScalarAll.heckeD_add' J Dset hfin, ih]

end Gen

end GlobalTheory.IsoComp

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PtLocalPin

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_fixed_of_finset {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)}
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (t : Finset (Submodule ℂ (GAf L n → W))) :
    (↑t ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ t, i), f ≠ 0 →
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) →
      ∃ S' ∈ t, ∃ g ∈ S', g ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g = g := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf hf0 _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    exact absurd hf hf0
  | insert a t ha ih =>
    intro hsub f hf hf0 hfix
    have haF : NG.IsIrrRep ρ a ∧ NG.IsoRep S a := hsub (Finset.mem_insert_self a t)
    have htF : (↑t : Set _) ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ t, i), NG.rt L n h g ∈ (⨆ i ∈ t, i) :=
      GlobalTheory.HeckeScalarAll.iSup_finset_stable' t (fun i hi => (htF hi).1.1.stable)
    have hsubrep : NG.IsSubrep ρ (a ⊓ ⨆ i ∈ t, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ y = y := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add (f := _)] at e
        have hd : NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ t, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      have hzfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ z = z := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add (f := _), hyfix κ hκ hκt] at e
        exact add_left_cancel e
      by_cases hy0 : y = 0
      · subst hy0
        rw [zero_add] at hf0
        obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih htF z hz hf0 hzfix
        exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩
      · exact ⟨a, Finset.mem_insert_self a t, y, hy, hy0, hyfix⟩
    · have hle : a ≤ ⨆ i ∈ t, i := inf_eq_left.1 htop
      obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih htF f ((sup_le hle le_rfl) hf) hf0 hfix
      exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩

theorem fixed_of_iso {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (GAf L n → W)} (hS : NG.IsSubrep ρ S)
    (hiso : NG.IsoRep S S') (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g' : GAf L n → W)
    (hg' : g' ∈ S') (hg0 : g' ≠ 0) (hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g' = g') :
    ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g = g := by
  obtain ⟨T, hT⟩ := hiso
  set g : S := T.symm ⟨g', hg'⟩ with hgdef
  have hTg : T g = ⟨g', hg'⟩ := T.apply_symm_apply _
  refine ⟨g, g.2, fun h => hg0 ?_, fun κ hκ ht => ?_⟩
  · have h0 : g = 0 := Subtype.ext h
    rw [h0, map_zero] at hTg
    exact (congrArg Subtype.val hTg).symm
  · have e := hT κ g ⟨_, hS.stable κ _ g.2⟩ rfl
    rw [hTg] at e
    have e' : T ⟨NG.rt L n κ g, hS.stable κ _ g.2⟩ = T g := by
      rw [hTg]
      exact Subtype.ext (e.trans (hfix κ hκ ht))
    exact congrArg Subtype.val (T.injective e')

theorem exists_fixed_of_isoTyp {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)}
    (hS : NG.IsIrrRep ρ S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (f : GAf L n → W)
    (hf : f ∈ NG.isoTyp ρ S) (hf0 : f ≠ 0) (hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) :
    ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g = g := by
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  obtain ⟨S', hS', g', hg', hg0, hgf⟩ := exists_fixed_of_finset v t ht f hft hf0 hfix
  exact fixed_of_iso hS.1 (ht hS').2 v g' hg' hg0 hgf

end Gen

theorem coeff_eq {N n : ℕ} (hN : N ≠ 0) {c c' : ℕ → ℂ}
    (h : (X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) * c k) * X ^ (n - k) : ℂ[X]) =
      X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) * c' k) * X ^ (n - k))
    {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n) : c k = c' k := by
  have key : ∀ d : ℕ → ℂ, (X ^ n + ∑ j ∈ Finset.Icc 1 n,
      C ((-1 : ℂ) ^ j * ((N : ℂ)) ^ (j * (j - 1) / 2) * d j) * X ^ (n - j) : ℂ[X]).coeff (n - k) =
        (-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) * d k := by
    intro d
    rw [coeff_add, coeff_X_pow, if_neg (by omega), zero_add, finsetSum_coeff, Finset.sum_eq_single k]
    · rw [coeff_C_mul_X_pow, if_pos rfl]
    · intro j hj hjk
      rw [Finset.mem_Icc] at hj
      rw [coeff_C_mul_X_pow, if_neg (by omega)]
    · intro hk
      exact absurd (Finset.mem_Icc.2 ⟨h1, h2⟩) hk
  have e := congrArg (fun p : ℂ[X] => p.coeff (n - k)) h
  rw [key c, key c'] at e
  have hne : (-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hN))
  exact mul_left_cancel₀ hne e

end GlobalTheory.PtLocalPin

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjCong

theorem exists_cong_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n N : ℕ) (g : GAf L n), 0 < N → ∃ M : ℕ, 0 < M ∧ ∀ κ, NG.Cong L n (N * M) κ → NG.Cong L n N (g⁻¹ * κ * g) := by
  intro L _ _ _ n N g hN
  obtain ⟨M, hM, h⟩ := Formalism.IndefR.principalLevelFrame.congConj_holds L n g N hN
  exact ⟨M, hM, fun κ hκ => h κ (NG.Cong.of_mul_right L n hκ)⟩

end GlobalTheory.ConjCong
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.OffBad

theorem splitPlace_of_isSplitPl (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) : ∃ s : SplitPlace D.host.E, s.w = w := by
  have hc : ∀ x : 𝓞 D.host.E, ((GlobalTheory.SumWCompare.cj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    intro x; rw [GlobalTheory.SumWCompare.cj_coe, GlobalTheory.DimPartsCompare.star_conj]
  have hcc : ∀ z : D.host.E, D.host.conj (D.host.conj z) = z := by
    intro z; rw [← GlobalTheory.DimPartsCompare.star_conj, ← GlobalTheory.DimPartsCompare.star_conj, star_star]
  obtain ⟨x, hx, hy⟩ := hw
  have hsp : IsSplitPl D.host (GlobalTheory.DimPartsCompare.cPl w) := by
    refine ⟨GlobalTheory.SumWCompare.cj D.host.E x, ?_, fun y e hy' => ?_⟩
    · rw [GlobalTheory.DimPartsCompare.mem_cPl, GlobalTheory.SumWCompare.cj_cj]; exact hx
    · rw [GlobalTheory.DimPartsCompare.mem_cPl] at hy'
      refine hy _ ?_ hy'
      rw [hc, show y = x from RingOfIntegers.ext (by rw [e, hc, hcc])]
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D _ hsp
  refine ⟨s, HeightOneSpectrum.ext (Ideal.ext fun y => ?_)⟩
  have := hs (GlobalTheory.SumWCompare.cj D.host.E y) y (by rw [hc, hcc])
  rw [GlobalTheory.DimPartsCompare.mem_cPl, GlobalTheory.SumWCompare.cj_cj] at this
  exact this.symm

theorem isSplitPl_of_isSplit (D : D7) (w : PlE D.host)
    (h : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F))) : IsSplitPl D.host w := by
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := h
  rw [GlobalTheory.Mem.GoodPlace.isSplitPl_iff]
  by_cases hw : w = P
  · refine ⟨Q, fun e => hPQ (hw.symm.trans e), ?_⟩
    ext1; exact hQ
  · refine ⟨P, hw, ?_⟩
    ext1; exact hP

end GlobalTheory.OffBad

namespace GlobalTheory.OffBad

end GlobalTheory.OffBad
end
