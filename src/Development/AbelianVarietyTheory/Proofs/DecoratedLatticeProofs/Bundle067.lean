module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle131
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockCoefficientIsSphericalHeckeEigen
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle997
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle063
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle057
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.symmetricLevelChain_unfolded_position_exchange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν := by
  first | exact @GlobalTheory.SymChain.ExchangeProof.exchangeAt | exact GlobalTheory.SymChain.ExchangeProof.exchangeAt | (intros; apply GlobalTheory.SymChain.ExchangeProof.exchangeAt <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.TorusLeft

theorem sum_indic {D' : Type} [Fintype D'] [DecidableEq D'] (s : Finset D') : ∑ i, indic s i = (s.card : ℤ) := by
  simp [indic]

theorem zpow_rpow_half (q : ℝ) (hq : 0 ≤ q) (n m : ℕ) :
    ((q ^ (-(n : ℤ)) : ℝ) ^ (-(m : ℝ) / 2)) = (Real.sqrt q) ^ (n * m) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq, ← Real.rpow_intCast, ← Real.rpow_mul hq]
  congr 1
  push_cast; ring

theorem omTwo_torusLeft : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ μS μT : kˣ →* ℂˣ), IsUnram (μS * ξ⁻¹) → ∀ (s : Finset D') (j : GL (A ⊕ D') k), j ∈ parahoric k A D' → ∀ (u : Matrix (A ⊕ D') (A ⊕ D) k → ℂ) (y : Matrix (A ⊕ D') (A ⊕ D) k), omTwo μS μT (1 : GL (A ⊕ D) k) (j * mtor ϖ (indic s)) u y = (μS ϖ : ℂ) ^ s.card * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (s.card * (Fintype.card A + Fintype.card D)) * (ξ (GeneralLinearGroup.det j) : ℂ) * u (((j * mtor ϖ (indic s))⁻¹ : GL (A ⊕ D') k).1 * y) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ μS μT hu s j hj u y
  have hKO : j ∈ KO k (A ⊕ D') := (mem_parahoric.1 hj).1
  have hnj : nabs k (GeneralLinearGroup.det j) = 1 := nabs_det_of_mem_KO hKO
  have hvj : valuation k ((GeneralLinearGroup.det j : kˣ) : k) = 1 := (nabs_eq_one_iff _).1 hnj
  have hξ : μS (GeneralLinearGroup.det j) = ξ (GeneralLinearGroup.det j) := by
    have := hu _ hvj
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at this
    exact this
  have hdm : GeneralLinearGroup.det (mtor ϖ (indic s) : GL (A ⊕ D') k) = ϖ ^ (s.card : ℤ) := by
    rw [GlobalTheory.ChainStepCoef.det_mtor, sum_indic]
  have hnm : nabs k (GeneralLinearGroup.det (mtor ϖ (indic s) : GL (A ⊕ D') k)) = (resCard k : ℝ) ^ (-(s.card : ℤ)) := by
    rw [GlobalTheory.ChainStepCoef.nabs_det_mtor hϖ, sum_indic]
  have hnh : nabs k (GeneralLinearGroup.det (j * mtor ϖ (indic s))) = (resCard k : ℝ) ^ (-(s.card : ℤ)) := by
    rw [map_mul, nabs_mul, hnj, hnm, one_mul]
  have hμh : μS (GeneralLinearGroup.det (j * mtor ϖ (indic s))) = ξ (GeneralLinearGroup.det j) * μS ϖ ^ s.card := by
    rw [map_mul, map_mul, hξ, hdm, zpow_natCast, map_pow]
  have hq : ((nabs k (GeneralLinearGroup.det (j * mtor ϖ (indic s))) ^ (-(Fintype.card (A ⊕ D) : ℝ) / 2) : ℝ) : ℂ)
      = ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (s.card * (Fintype.card A + Fintype.card D)) := by
    rw [hnh, ← Fintype.card_sum, zpow_rpow_half _ (Nat.cast_nonneg _)]
    push_cast; rfl
  have key : (((μS * μT⁻¹) (GeneralLinearGroup.det (j * mtor ϖ (indic s))) : ℂˣ) : ℂ) *
      (((μT⁻¹ (GeneralLinearGroup.det (j * mtor ϖ (indic s))))⁻¹ : ℂˣ) : ℂ) =
      (μS (GeneralLinearGroup.det (j * mtor ϖ (indic s))) : ℂ) := by
    rw [← Units.val_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_inv, inv_mul_cancel_right]
  simp only [omTwo, om, Pi.smul_apply, smul_eq_mul, map_one, Units.val_one, one_mul, nabs_one, Real.one_rpow, Complex.ofReal_one, mul_one, Matrix.mul_one]
  rw [hq, ← mul_assoc, ← mul_assoc, key, hμh, Units.val_mul, Units.val_pow_eq_pow_val]
  ring

end GlobalTheory.TorusLeft
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.lowerBlockCoefficient_isSphericalHeckeEigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (B : Multiset ℂˣ) (x : V) (ℓ : V →ₗ[ℂ] ℂ), IsGen π ξ ϖ B x → IsCoType π ξ ℓ → ∀ H : GL D k → ℝ, IsHgt ϖ H → ∀ f : GL D k → ℂ, (∀ m, f m = (((ξ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * ℓ (π (emb₂ k (Equiv.refl (A ⊕ D)) (1, m)) x) / ((Real.sqrt (H m) : ℝ) : ℂ) ^ Fintype.card A) → (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) ∧ ∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) (B.map (· * (ξ ϖ)⁻¹)) s.card * f m := by
  first | exact @GlobalTheory.LowerHeckeEig.coeff_isEigen | exact GlobalTheory.LowerHeckeEig.coeff_isEigen | (intros; apply GlobalTheory.LowerHeckeEig.coeff_isEigen <;> assumption)
end

section

namespace GlobalTheory.Core.Ht2.StepRowsS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem weights_rows : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : _root_.Formalism.L2.Col.Fields) (s : Seam D X) (Pr : _root_.Formalism.L2.Col.Primes X) (W : _root_.Formalism.L2.Col.Wts X Pr.Word N.R) (Ch : _root_.Formalism.L2.Col.Chars X Pr N.R.m) (G : _root_.Formalism.L2.Col.ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : _root_.Formalism.L2.Col.LocCst X (_root_.Formalism.L2.Col.rowSG Pr sel mu)) (I : _root_.Formalism.L2.Col.ChIdx X Pr N.R (_root_.Formalism.L2.Col.QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i < N.R.m → (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (W.lamTrue u i τ) (W.nuW u (i + 1) τ) (W.lamTrue u (i + 1) τ)) ∧ ∀ (z : RPl N.R) (l : Fin (N.R.N i)), (((W.nuW u (i + 1) (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hyp i hi
  obtain ⟨-, hW, -, -, -, -, -, -, hS⟩ := hyp
  refine ⟨fun τ => StepRows.stepWeights W u hi τ fun l => ?_, fun z l => StepRows.nuW_eq_nu N W pl u δ hW hi z l⟩
  obtain ⟨z, rfl⟩ := pl.surjective τ
  have h1 := StepRows.nuW_eq_nu N W pl u δ hW hi z l
  have h2 := (hS.2.2.2.2.1 (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩) z l.1 l.2).1
  rw [← h1] at h2
  exact_mod_cast h2

end GlobalTheory.Core.Ht2.StepRowsS
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.VolBridge

theorem index_comap_of_dense_image {A B : Type} [Group A] [Group B] (f : A →* B) (H : Subgroup B)
    (hf : ∀ b, ∃ a, (f a)⁻¹ * b ∈ H) : (H.comap f).index = H.index := by
  first
  | exact @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | (apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit ..)

theorem relIndex_comap_of_dense_image {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G)
    (K U : Subgroup G) (h : ∀ g ∈ U, ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) :
    (K.comap φ).relIndex (U.comap φ) = K.relIndex U := by
  let f : U.comap φ →* U := φ.subgroupComap U
  have hc : (K.comap φ).subgroupOf (U.comap φ) = (K.subgroupOf U).comap f := by
    ext x
    exact Iff.rfl
  have key := index_comap_of_dense_image f (K.subgroupOf U) (by
    rintro ⟨b, hb⟩
    obtain ⟨γ, hγK, hγU⟩ := h b hb
    have hγ : φ γ ∈ U := by
      have := U.mul_mem hb (U.inv_mem hγU)
      simpa using this
    refine ⟨⟨γ, hγ⟩, ?_⟩
    exact hγK)
  simp only [Subgroup.relIndex]
  rw [hc, key]

theorem vol_agree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → VolAgree (R := R) sel mu cst σ₀ P ι s W ν := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hok hat
  have hLev := GlobalTheory.T.parahoricLevels_characters_doubleCosets_agree_rational X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hat
  haveI : ν.IsAddHaarMeasure := hν.1
  intro j c h γ g hg
  obtain ⟨e, he, hge⟩ := hg
  have hcc : cOf R j = c + 1 := by unfold cOf; have := hat.steps; omega
  have heR : ∀ i : Fin (c + 1), (e (Sum.inr i)).val = R.N j + i.val := fun i => he (Sum.inr i)
  have hgφ : g = GlobalTheory.VolBridge.locHom ι e γ := Units.ext hge
  have hreg : (W.T s R).Regular := Chain.ofTwist_regular _ _ _ _ _
  obtain ⟨hJo, hJc, -⟩ := hreg.2.2 j (c + 1) h
  set J := ((W.T s R).lev j (c + 1) h).J with hJdef
  set φ := GlobalTheory.VolBridge.locHom ι e with hφ
  have hcompl := hat.compl

  have hIsGL : ∀ x : AutY X R j, IsGL ι (γ⁻¹ * x * γ) (g⁻¹ * φ x * g) := by
    intro x
    refine ⟨e, he, ?_⟩
    rw [hgφ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hC : ∀ x : AutY X R j, x ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ↔ φ x ∈ Cgrp J g := by
    intro x
    rw [mem_Cgrp, ← GlobalTheory.T.mem_R1_iff_local_hom ι e hcc heR x, (hLev j (c + 1) h _ _ (hIsGL x)).1]
    simp [Loc.Cbe, Subgroup.mem_comap, MulAut.conj_apply]
  have hN1 := GlobalTheory.T.mem_N1_iff_locHom_mem_N_one ι e hcc heR
  have hlam : lamYat (Pr := Pr) (R := R) j P.1 = stdAt X.E _ P.1 := by
    ext v
    simp only [lamYat, if_neg hat.nmem, LocE.lamY, LocE.sclLat, Submodule.mem_comap]
    congr! 1
    funext l
    simp [LocE.scE]
  have hKO : ∀ x : AutY X R j, x ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) ↔ φ x ∈ KO k _ := by
    intro x
    rw [hlam]
    exact GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL P.1 ι hcompl.int e x
  have hdN := GlobalTheory.T.exists_N1_locHom_mem_open ι hcompl.dense e hcc heR
  refine ⟨?_, ?_⟩
  ·
    have hH := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 le_rfl (by omega) ν
    haveI : (volN ν (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1).IsHaarMeasure := hH.2.2.1
    haveI : BorelSpace (GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k) :=
      _root_.GlobalTheory.SplitFlip.borel_GL
    haveI : BorelSpace (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1) := Subtype.borelSpace _
    obtain ⟨ho, hAc, hBc⟩ := GlobalTheory.T.isOpen_mirabolicConj_inf_integralGL_unipotent J g hJo hJc
    have hst : stabLat (1 : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k) = KO k _ := by
      ext z; simp [stabLat, Subgroup.mem_comap]
    have hvol : volNat ν 1 (Cgrp J g) =
        (volN ν _ (c + 1) 1 ((Cgrp J g).subgroupOf (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1) :
          Set (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1))).toReal /
        (volN ν _ (c + 1) 1 ((KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1))).subgroupOf (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1) :
          Set (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1))).toReal := by
      rw [volNat, hst]
    rw [hvol, GlobalTheory.T.haar_volume_ratio_compact_eq_relIndex_ratio
      (volN ν (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1) _ _ ho hAc hBc]
    set K := Cgrp J g ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 with hKdef
    set U := KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 with hUdef
    have hA : (Cgrp J g).subgroupOf (N k _ (c + 1) 1) = K.subgroupOf (N k _ (c + 1) 1) :=
      (Subgroup.inf_subgroupOf_right _ _).symm
    have hB : (KO k _).subgroupOf (N k _ (c + 1) 1) = U.subgroupOf (N k _ (c + 1) 1) :=
      (Subgroup.inf_subgroupOf_right _ _).symm
    rw [hA, hB, Subgroup.relIndex_subgroupOf inf_le_right, Subgroup.relIndex_subgroupOf inf_le_right]
    have hKc : K.comap φ = Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ⊓ Loc.N1 X.E (R.N j) (cOf R j) := by
      ext x
      show φ x ∈ Cgrp J g ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 ↔ _
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hC, hN1]
    have hUc : U.comap φ = Loc.N1 X.E (R.N j) (cOf R j) ⊓ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) := by
      ext x
      show φ x ∈ KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 ↔ _
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hKO, hN1]; exact And.comm
    have hden : ∀ z, z ∈ K ∨ z ∈ U → ∃ x, (φ x)⁻¹ * z ∈ K ⊓ U := by
      intro z hz
      have hzN : z ∈ N k _ (c + 1) 1 := by rcases hz with hz | hz; exacts [hz.2, hz.2]
      have hO1 : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
        hJo.preimage (by fun_prop)
      have hO' := hO1.inter (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)))
      have hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | v⁻¹ * z ∈ ({w | g⁻¹ * w * g ∈ J} ∩
          (KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) : Set (GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)))} :=
        hO'.preimage (by fun_prop)
      obtain ⟨x, hx, hxV⟩ := hdN z hzN _ hV (by simp [J.one_mem, one_mem])
      refine ⟨x, ?_⟩
      have hxN := (hN1 x).1 hx
      have hm : (φ x)⁻¹ * z ∈ N k _ (c + 1) 1 := mul_mem (inv_mem hxN) hzN
      have hmR : (φ x)⁻¹ * z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := by unfold GlobalTheory.RootEx.R; exact Subgroup.mem_sup_right hm
      exact ⟨⟨mem_Cgrp.2 ⟨hmR, hxV.1⟩, hm⟩, hxV.2, hm⟩
    have h1 := GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ K U (fun z hz => hden z (Or.inr hz))
    have h2 := GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ U K (fun z hz => by
      obtain ⟨x, hx⟩ := hden z (Or.inl hz); exact ⟨x, by rwa [inf_comm]⟩)
    rw [hKc, hUc] at h1 h2
    rw [← h1, ← h2]
    simp [Loc.volN, map_div₀, map_natCast]
  · intro hle m hm hm1
    haveI := hm
    set e' := GlobalTheory.VolBridge.eX e hcc heR with he'
    set φ' := GlobalTheory.VolBridge.locHom ι e' with hφ'
    have hOo : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
      hJo.preimage (by fun_prop)
    have hOR : ∀ z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1, z ∈ Cgrp J g ↔ z ∈ {w | g⁻¹ * w * g ∈ J} := fun z hz => by
      simp [mem_Cgrp, hz]
    have hCR : Cgrp J g ≤ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := fun z hz => (mem_Cgrp.1 hz).1
    have hP : ∀ y, y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ ↔ φ' y ∈ prX (Cgrp J g) :=
      GlobalTheory.T.mem_mirabolicProjection_iff_colSpaceAutToLocalGL ι e hcc heR hN1 hdN _ _ _ hOo hOR hCR hC
    have hG : ∀ y, y ∈ GLint X.E (R.N j) P.1 ↔ φ' y ∈ KO k _ := fun y =>
      GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL P.1 ι hcompl.int e' y
    have hpo : IsOpen (prX (Cgrp J g) : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)) :=
      GlobalTheory.T.isOpen_mirabolicProjectionToGL _ _ hOo (by simp [J.one_mem]) (fun z hz hzO => (hOR z hz).2 hzO)
    have hden : ∀ z, z ∈ prX (Cgrp J g) ∨ z ∈ KO k _ → ∃ y, (φ' y)⁻¹ * z ∈ prX (Cgrp J g) ⊓ KO k _ := by
      intro z _
      have hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j) k | v⁻¹ * z ∈ ((prX (Cgrp J g) ⊓ KO k _ : Subgroup _) : Set _)} :=
        (hpo.inter GlobalTheory.SplitFlip.isOpen_KO).preimage (by fun_prop)
      obtain ⟨y, hy⟩ := GlobalTheory.T.exists_colSpaceAutToLocalGL_mem_open_dense ι hcompl.dense e' z _ hV (by simp [one_mem])
      exact ⟨y, hy⟩
    have hle' : prX (Cgrp J g) ≤ KO k _ := by
      intro z hz
      obtain ⟨y, hy1, hy2⟩ := hden z (Or.inl hz)
      have hyC : φ' y ∈ prX (Cgrp J g) := by
        have := mul_mem hz (inv_mem hy1); simpa using this
      have hyK : φ' y ∈ KO k _ := (hG y).1 (hle ((hP y).2 hyC))
      have := mul_mem hyK hy2; simpa using this
    have hidx := GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ' (prX (Cgrp J g)) (KO k _)
      (fun z hz => hden z (Or.inr hz))
    have hc1 : (prX (Cgrp J g)).comap φ' = prCat (Pr := Pr) cst.sharp j P.1 γ := by ext y; exact (hP y).symm
    have hc2 : (KO k _).comap φ' = GLint X.E (R.N j) P.1 := by ext y; exact (hG y).symm
    rw [hc1, hc2] at hidx
    rw [hidx]
    exact GlobalTheory.T.haar_open_subgroup_volume_inv_eq_relIndex m _ _ hle' hpo GlobalTheory.SplitFlip.isCompact_KO hm1

end GlobalTheory.VolBridge
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridge


open Classical in
theorem twNext_rep_eq_of_sameDC {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Tup X.F X.E X.K S₀)
    (cst : LocCst X (rowSG Pr sel mu)) {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i)
    (hinj : ∀ d d' : (twNext Ch sel mu cst st).β, (∀ P : rowSG Pr sel mu,
      SameDC (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h d P) ((twNext Ch sel mu cst st).h d' P)) → d = d')
    (d d' : (twNext Ch sel mu cst st).β) (P : rowSG Pr sel mu)
    (hs : SameDC (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h d P) ((twNext Ch sel mu cst st).h d' P)) :
    (twNext Ch sel mu cst st).h d P = (twNext Ch sel mu cst st).h d' P := by
  by_cases hP : P.1 ∈ twQOff (Pr := Pr) sel mu
  · let P₀ : twQOff (Pr := Pr) sel mu := ⟨P.1, hP⟩
    let d'' : (twNext Ch sel mu cst st).β := ⟨Function.update d.1 P₀ (d'.1 P₀), d.2⟩
    have hall : ∀ Q : rowSG Pr sel mu, SameDC (Pr := Pr) cst.sharp (i + 1) Q.1
        ((twNext Ch sel mu cst st).h d Q) ((twNext Ch sel mu cst st).h d'' Q) := by
      intro Q
      by_cases hQ : Q.1 ∈ twQOff (Pr := Pr) sel mu
      · by_cases e : (⟨Q.1, hQ⟩ : twQOff (Pr := Pr) sel mu) = P₀
        · have hQP1 : Q.1 = P.1 := congrArg (fun x : twQOff (Pr := Pr) sel mu => x.1) e
          have hQP : Q = P := Subtype.ext hQP1
          rw [hQP]
          have e1 : (twNext Ch sel mu cst st).h d'' P = (twNext Ch sel mu cst st).h d' P := by
            simp only [twNext, dif_pos hP, d'']
            rw [Function.update_self]
          rw [e1]; exact hs
        · have e1 : (twNext Ch sel mu cst st).h d'' Q = (twNext Ch sel mu cst st).h d Q := by
            simp only [twNext, dif_pos hQ, d'']
            rw [Function.update_of_ne e]
          rw [e1]; exact twDC_refl _ _ _ _
      · have e1 : (twNext Ch sel mu cst st).h d'' Q = (twNext Ch sel mu cst st).h d Q := by
          simp only [twNext, dif_neg hQ]
        rw [e1]; exact twDC_refl _ _ _ _
    have hdd := hinj d d'' hall
    have hc : d.1 P₀ = d'.1 P₀ := by
      have := congrArg (fun x : (twNext Ch sel mu cst st).β => x.1 P₀) hdd
      simpa [d''] using this
    simp only [twNext, dif_pos hP]
    exact congrArg (fun D => twRep Ch sel mu cst st P₀ D.1) hc
  · simp only [twNext, dif_neg hP]

theorem idxProd_twIdx : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ) (G : ChGlob X R.m), (twIdx Ch sel mu cst m2).Ok Ch sel mu cst G m2 → IdxProd sel mu cst (twIdx Ch sel mu cst m2) := by
  intro X Pr R Ch sel S₀ mu cst m2 G hok j b b' P hs
  rcases j with _ | i
  · rfl
  · by_cases hi : i + 1 ≤ m2
    · have key : ∀ st' : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) (i + 1), st' = twNext Ch sel mu cst (twSt Ch sel mu cst m2 i) →
          ∀ b b' : st'.β, (∀ b b' : st'.β, (∀ P : rowSG Pr sel mu,
            SameDC (Pr := Pr) cst.sharp (i + 1) P.1 (st'.h b P) (st'.h b' P)) → b = b') →
          SameDC (Pr := Pr) cst.sharp (i + 1) P.1 (st'.h b P) (st'.h b' P) → st'.h b P = st'.h b' P := by
        rintro st' rfl b b' hinj hs
        exact twNext_rep_eq_of_sameDC Ch sel mu cst _ hinj b b' P hs
      exact key (twSt Ch sel mu cst m2 (i + 1)) (by rw [twSt, if_pos hi]) b b' (hok.inj i (by omega)) hs
    · by_cases hi2 : i + 1 = m2 + 1
      · have key : ∀ st' : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) (i + 1), st' = twUnitSt _ (i + 1) →
            ∀ b b' : st'.β, st'.h b P = st'.h b' P := by
          rintro st' rfl b b'; rfl
        exact key (twSt Ch sel mu cst m2 (i + 1)) (by rw [twSt, if_neg hi, if_pos hi2]) b b'
      · have key : ∀ st' : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) (i + 1), st' = twEmptySt _ (i + 1) →
            ∀ b b' : st'.β, st'.h b P = st'.h b' P := by
          rintro st' rfl b; exact b.elim
        exact key (twSt Ch sel mu cst m2 (i + 1)) (by rw [twSt, if_neg hi, if_neg hi2]) b b'

end GlobalTheory.TwBridge
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.unfoldingIntegral_positionOne_eq_finite_sum : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K]
    [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ) (σ₀ : K →+* ℂ) (ψ : AddChar k Circle) (ν : Measure k)
    (psi : E → K) (N : ℕ),
    GlobalTheory.SymBridge.IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → HasConductor ψ 1 → IsUnitVol ν →
    (∀ a, IntAt P ((q : E) ^ N * a) → (ψ (ι a) : ℂ) = σ₀ (psi a)) →
    ∀ (U' U : Type) [Fintype U'] [DecidableEq U'] [Fintype U] [DecidableEq U] (c n' c' n c₂ A B : ℕ),
      1 ≤ c → c' = c + 1 → c₂ = c → N ≤ A → N ≤ B →
    ∀ (d' : U' ≃ Fin n') (d : U ≃ Fin n) (e' : U' ⊕ Fin (c + 1) ≃ Fin (n' + c')) (e : U ⊕ Fin c ≃ Fin (n + c₂)),
      GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun a => (d' a).val) n') e' →
      GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun a => (d a).val) n) e →
    ∀ (Φ : Matrix (U ⊕ Fin c) (U' ⊕ Fin (c + 1)) k → ℂ) (ΦE : Loc.SF E K (n' + c') (n + c₂)) (C : ℂ),
      (∀ x, Φ (GlobalTheory.SymBridge.toLoc ι e e' x) = C * σ₀ (ΦE x)) →
      (∀ x, Φ x ≠ 0 → ∀ r s, valuation k (x r s) ≤ valuation k (((ϖ ^ N)⁻¹ : kˣ) : k)) →
      (∀ x y, (∀ r s, valuation k (y r s) ≤ valuation k ((ϖ : k) ^ N)) → Φ (x + y) = Φ x) →
      ∀ x₀, opE ψ ν 1 Φ (GlobalTheory.SymBridge.toLoc ι d d' x₀) =
        C * σ₀ (Loc.E1 (n' := n') (c' := c') (n := n) (c := c₂) psi (LocE.valsQ E q A B) (((q : K) ^ B)⁻¹) ΦE x₀) := by
  first | exact @GlobalTheory.UnfoldSumBd.sumAgreeBd | exact GlobalTheory.UnfoldSumBd.sumAgreeBd | (intros; apply GlobalTheory.UnfoldSumBd.sumAgreeBd <;> assumption)
end

section

open MeasureTheory GlobalTheory.Grow

namespace GlobalTheory

theorem quotientIntegral_oneDoubleCoset_eq_mul_value (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (R K : Subgroup G)
    (hR : IsClosed (R : Set G)) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (ρ : Measure R) (μ : Measure G) (hρ : ρ.IsHaarMeasure) (hρr : ρ.IsMulRightInvariant) (hμ : μ.IsHaarMeasure)
    (t : G) : ∃ w : ℂ, w ≠ 0 ∧ ∀ f : G → ℂ, (∀ r ∈ R, ∀ g, f (r * g) = f g) → (∀ k ∈ K, ∀ g, f (g * k) = f g) →
      (∀ g, f g ≠ 0 → ∃ r ∈ R, ∃ k ∈ K, g = r * t * k) → IsQuotIntL1 ρ μ f (w * f t) := by

  set T : Set G := {g | t⁻¹ * g ∈ K} with hT
  set S : Set R := {r | t⁻¹ * ((r : G) * t) ∈ K} with hS
  have hemb : Topology.IsClosedEmbedding (Subtype.val : R → G) := hR.isClosedEmbedding_subtypeVal

  have hAo : ∀ h : G, IsOpen {r : R | t⁻¹ * ((r : G) * h) ∈ K} := fun h =>
    hKo.preimage (continuous_const.mul (continuous_subtype_val.mul continuous_const))
  have hAc : ∀ h : G, IsCompact {r : R | t⁻¹ * ((r : G) * h) ∈ K} := fun h => by
    have h1 : IsCompact ((fun g : G => t⁻¹ * (g * h)) ⁻¹' (K : Set G)) := by
      have e : (fun g : G => t⁻¹ * (g * h)) ⁻¹' (K : Set G) = (fun g => t * g * h⁻¹) '' (K : Set G) := by
        ext g; constructor
        · intro hg; exact ⟨t⁻¹ * (g * h), hg, by group⟩
        · rintro ⟨k, hk, rfl⟩; simpa [mul_assoc] using hk
      rw [e]; exact hKc.image (by fun_prop)
    exact hemb.isCompact_preimage h1
  have hTm : MeasurableSet T := (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμT : μ T = μ K := measure_preimage_mul μ t⁻¹ K
  have hμK0 : μ K ≠ 0 := (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hμKt : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hSo : IsOpen S := by simpa using hAo t
  have hSc : IsCompact S := by simpa using hAc t
  have hρS0 : ρ S ≠ 0 := (hSo.measure_pos ρ ⟨1, by simp [hS]⟩).ne'
  have hρSt : ρ S ≠ ⊤ := hSc.measure_lt_top.ne
  set c : ℝ := ρ.real S with hc
  have hc0 : c ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hρS0, hρSt⟩
  have hμK : μ.real K ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hμK0, hμKt⟩
  refine ⟨(μ.real K : ℂ) / (c : ℂ), div_ne_zero (by exact_mod_cast hμK) (by exact_mod_cast hc0), fun f hfl hfr hfs => ?_⟩
  set a : ℂ := f t / (c : ℂ) with ha
  refine ⟨T.indicator fun _ => a, ?_, fun h => ?_, fun h => ?_, ?_⟩
  · exact (integrable_indicator_iff hTm).2 (integrableOn_const (by rw [hμT]; exact hμKt))
  · have e : (fun r : R => T.indicator (fun _ => a) ((r : G) * h)) =
        {r : R | t⁻¹ * ((r : G) * h) ∈ K}.indicator fun _ => a := by
      rfl
    rw [e]
    exact (integrable_indicator_iff (hAo h).measurableSet).2
      (integrableOn_const (hAc h).measure_lt_top.ne)
  · have e : (fun r : R => T.indicator (fun _ => a) ((r : G) * h)) =
        {r : R | t⁻¹ * ((r : G) * h) ∈ K}.indicator fun _ => a := by
      rfl
    rw [e, integral_indicator_const _ (hAo h).measurableSet]
    by_cases hne : ∃ s ∈ R, ∃ k ∈ K, h = s * t * k
    · obtain ⟨s, hs, k, hk, rfl⟩ := hne
      have eA : {r : R | t⁻¹ * ((r : G) * (s * t * k)) ∈ K} = (fun r : R => r * ⟨s, hs⟩) ⁻¹' S := by
        ext r
        simp only [hS, Set.mem_preimage, Set.mem_ofPred_eq, Subgroup.coe_mul]
        have : t⁻¹ * ((r : G) * (s * t * k)) = t⁻¹ * ((r : G) * s * t) * k := by group
        rw [this, Subgroup.mul_mem_cancel_right _ hk]
      have e1 : ρ.real {r : R | t⁻¹ * ((r : G) * (s * t * k)) ∈ K} = c := by
        rw [eA, hc, measureReal_def, measureReal_def, measure_preimage_mul_right]
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
      rw [e1, ha, mul_assoc, hfl s hs, hfr k hk, Complex.real_smul]
      field_simp
    · have hf : f h = 0 := by
        by_contra hf; exact hne (hfs h hf)
      have eA : {r : R | t⁻¹ * ((r : G) * h) ∈ K} = ∅ := by
        ext r
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hr
        exact hne ⟨(r : G)⁻¹, inv_mem r.2, t⁻¹ * ((r : G) * h), hr, by group⟩
      rw [hf, eA]; simp
  · rw [integral_indicator_const _ hTm]
    have e2 : μ.real T = μ.real K := by simp only [measureReal_def, hμT]
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
    rw [e2, ha, Complex.real_smul]
    field_simp

end GlobalTheory
end
