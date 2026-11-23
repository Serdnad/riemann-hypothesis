module

public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle556
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitOfSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle022
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionExistence.LeOneIffOfMulEqOne
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EigGoodTypes

theorem tw_inv_eta {D : D7} (h0 : SumRepresentations.tie0 D) (h4 : SumRepresentations.ArchimedeanSignatureMatching D) (h5 : SumRepresentations.adm5 D) {a : ℕ} (ha : 1 ≤ a)
    (π : D.naut.CG a) : D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT = π := by
  have hLP : SumRepresentations.At.TieLP D.nd D.naut := h0.1
  have hC := h4.2.2
  have h := h5.1 [⟨a, D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      show isoLoc D.nd D.naut (twistIso D.nd D.naut (twistIso D.nd D.naut [⟨a, π, 1⟩] D.naut.etaTinv) D.naut.etaT) w = _
      rw [GlobalTheory.RowThetaParam.isoLoc_twistIso D.nd D.naut hLP hC, GlobalTheory.RowThetaParam.isoLoc_twistIso D.nd D.naut hLP hC,
        (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hLP _).2])
  rw [List.singleton_perm_singleton] at h
  injection h with _ h2

theorem sig_parC {D : D7} (h0 : SumRepresentations.tie0 D) (h4 : SumRepresentations.ArchimedeanSignatureMatching D) (h5 : SumRepresentations.adm5 D) {i : D.nd.Loc} {P0 : D.naut.AV i}
    {Sig : List (Part D.naut.CG)}
    (hB : IsBCV D.nd D.naut i P0 (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv))
    (hg : goodSig D.nd D.naut Sig) :
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) ∧
    (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).Nodup ∧
    rankIso D.nd D.naut Sig = D.R.r ∧
    ∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).Monic ∧
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := hB
  refine ⟨fun p hp => ?_, ?_, ?_, fun k v => ⟨((hg k).1.1 v).1, ((hg k).1.1 v).2.1⟩⟩
  · have hm : (⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩ : Part D.naut.CG) ∈
        twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv :=
      List.mem_map.2 ⟨p, List.mem_append_left _ hp, rfl⟩
    obtain ⟨ha, hd, hc⟩ := h1 _ hm
    refine ⟨ha, hd, ?_⟩
    have := D.naut.csd_tw _ _ h0.2.1.1.1 hc
    rwa [tw_inv_eta h0 h4 h5 ha] at this
  · have hinj : Function.Injective (fun p : Part D.naut.CG => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)) := by
      rintro ⟨a, π, d⟩ ⟨a', π', d'⟩ h
      simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨⟨rfl, h⟩, rfl⟩ := h
      cases h
      rfl
    have hn : (Sig ++ [muPart D.nd D.naut i]).Nodup := by
      unfold twistIso at h2
      rw [List.map_map] at h2
      exact List.Nodup.of_map _ h2
    exact (hn.sublist (List.sublist_append_left _ _)).map hinj
  · have e1 : (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv).map (fun p => p.a * p.d) =
        (Sig ++ [muPart D.nd D.naut i]).map (fun p => p.a * p.d) := by
      unfold twistIso
      rw [List.map_map]
      rfl
    unfold rankIso at h3 ⊢
    rw [e1, List.map_append, List.sum_append] at h3
    simp only [muPart, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at h3
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega

theorem onMt_cast {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (f : D.what₂.Mt μ a)
    (H : D.ntypes.onMt μ b D.ntypes.e0 (h ▸ f) = h ▸ f) : D.ntypes.onMt μ a D.ntypes.e0 f = f := by
  subst h
  exact H

end GlobalTheory.EigGoodTypes

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwistBridgeDR

open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.TwistAbove

theorem twGL_eq {Γ K : Type} [Group Γ] [CommRing K] {a : ℕ} (r : Γ →* GL (Fin a) K) (μ : Γ →* Kˣ) :
    Formalism.MainNotions.SumRepresentations.At.twGL r μ = GlobalTheory.TwistAbove.twGL μ r := by
  ext g i j
  simp [Formalism.MainNotions.SumRepresentations.At.twGL, GlobalTheory.TwistAbove.twGL, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]

theorem characterAsRankOneRep_det_comp {Γ K : Type} [Group Γ] [CommRing K] (c : Γ →* GL (Fin 1) K) :
    GlobalTheory.TripleGal.rk1 (Matrix.GeneralLinearGroup.det.comp c) = c := by
  ext g i j
  fin_cases i; fin_cases j
  simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a : ℕ}

theorem repE_twGL' {L : FinExt l} (χ : ↥Gw →* (↥L.1)ˣ) (s : ↥Gw →* GL (Fin a) ↥L.1)
    (g : ↥(GK Bw.Kw)) (x : Fin a → ↥L.1) :
    Bw.repE L (GlobalTheory.TwistAbove.twGL χ s) g x = ((χ (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) • Bw.repE L s g x := by
  change Matrix.toLin' ((GlobalTheory.TwistAbove.twGL χ s (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x =
    ((χ (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) •
      Matrix.toLin' ((s (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x
  rw [_root_.GlobalTheory.TwistAbove.twGL_val, Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact Matrix.smul_mulVec _ _ _

theorem isModel_untwist {L : FinExt l} {r : ↥Gw →* GL (Fin a) (Om l)} {c : ↥Gw →* GL (Fin 1) (Om l)}
    {t : ↥Gw →* GL (Fin a) ↥L.1} {cc : ↥Gw →* GL (Fin 1) ↥L.1}
    (mt : IsModel Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) L t)
    (mc : IsModel Bw c L cc) : IsModel Bw r L (GlobalTheory.TwistAbove.twGL (chr cc)⁻¹ t) := by
  refine ⟨mt.1, ?_⟩
  ext g i j
  have e1 := congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) =>
    ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) mt.2
  have e2 := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) =>
    ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) mc.2
  rw [twGL_eq] at e1
  simp only [mapRep] at e1 e2 ⊢
  simp [Matrix.det_unique] at e1 e2 ⊢
  have hne : ((c g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0 ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det (c g)).ne_zero
    simpa [Matrix.det_unique] using this
  rw [e1, e2, inv_mul_cancel_left₀ hne]

theorem isdRAt_twist_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Loc.Om l)) (c : ↥Gw →* GL (Fin 1) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → Continuous (fun g => ((c g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l))) → GlobalTheory.Pst.IsdRAt P Bw c → (GlobalTheory.Pst.IsdRAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) ↔ GlobalTheory.Pst.IsdRAt P Bw r) := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw a r c _ _ hc
  obtain ⟨T⟩ := hT
  obtain ⟨L₂, c₂, m₂, d₂⟩ := hc
  constructor
  · rintro ⟨L₁, t₁, m₁, d₁⟩
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    have mt := m₁.enlarge l₁
    have mc := m₂.enlarge l₂
    have dt := (local_ext P Bw l₁ t₁).2.1.2 d₁
    have dc := (local_ext P Bw l₂ c₂).2.1.2 d₂
    set t := mapRep (IntermediateField.inclusion l₁).toRingHom t₁
    set cc := mapRep (IntermediateField.inclusion l₂).toRingHom c₂
    refine ⟨_, _, isModel_untwist Bw mt mc, ?_⟩
    have hν := repE_rank_one Bw cc
    have hρ : ∀ g x, Bw.repE (supExt L₁ L₂) t g x =
        ((chr cc (Bw.e.symm g) : (↥(supExt L₁ L₂).1)ˣ) : ↥(supExt L₁ L₂).1) •
          Bw.repE (supExt L₁ L₂) (GlobalTheory.TwistAbove.twGL (chr cc)⁻¹ t) g x := by
      intro g x
      rw [repE_twGL', smul_smul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        one_smul]
    rw [← isDR_iff] at dt dc ⊢
    exact (GlobalTheory.TwistDR.isDR_twist_iff l P AI T Bw.Kw (supExt L₁ L₂) (Fin a → ↥(supExt L₁ L₂).1)
      _ _ _ _ hν hρ dc).2 dt
  · rintro ⟨L₁, r₁, m₁, d₁⟩
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    have mc : IsModel Bw (GlobalTheory.TripleGal.rk1 (Matrix.GeneralLinearGroup.det.comp c)) (supExt L₁ L₂)
        (mapRep (IntermediateField.inclusion l₂).toRingHom c₂) := by
      rw [characterAsRankOneRep_det_comp]; exact m₂.enlarge l₂
    refine ⟨_, _, isModel_twGL Bw (r' := Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c))
      (μ := Matrix.GeneralLinearGroup.det.comp c) (fun g => by rw [twGL_eq]; exact _root_.GlobalTheory.TwistAbove.twGL_val _ _ _)
      (m₁.enlarge l₁) mc, (twist_common Bw _ _ T).1 ((local_ext P Bw l₁ r₁).2.1.2 d₁)
        ((local_ext P Bw l₂ c₂).2.1.2 d₂)⟩

end GlobalTheory.TwistBridgeDR
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowPointLoc

theorem continuous_of_adic {A B : Type} [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [IsLocalRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (f : A ≃+* B) :
    Continuous f := by
  have hm : Ideal.map (f : A →+* B) (IsLocalRing.maximalIdeal A) ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro hu
    apply hx
    have := hu.map (f.symm : B →+* A)
    simpa using this
  refine continuous_of_continuousAt_zero (f : A →+ B) ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := ((isAdic_iff.1 hB).2 s hs)
  have hopen := (isAdic_iff.1 hA).1 n
  refine Filter.mem_map.2 (Filter.mem_of_superset (hopen.mem_nhds (Ideal.zero_mem _)) ?_)
  intro x hx
  apply hn
  have h1 : f x ∈ Ideal.map (f : A →+* B) (IsLocalRing.maximalIdeal A ^ n) := Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono hm n h1

end GlobalTheory.RowPointLoc
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitCompl

theorem exists_ringEquiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L),
    ∃ i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous i ∧ Continuous i.symm ∧
      ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x := by
  intro L _ _ _ s

  have hf : ∀ x : L, Valued.v (s.i.toRingHom x) = s.w.valuation L x :=
    fun x => PI.CompAtExist.muV_eq s x
  obtain ⟨φ, hφc, hφ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.w s.v (f := s.i.toRingHom) hf

  let g : maximalRealSubfield L →+* s.w.adicCompletion L :=
    (algebraMap L (s.w.adicCompletion L)).comp (algebraMap (maximalRealSubfield L) L)
  have hg : ∀ a, Valued.v (g a) = s.v.valuation (maximalRealSubfield L) a := by
    intro a
    simp only [g, RingHom.comp_apply]
    rw [GlobalTheory.Idele.valued_algebraMap, ← PI.CompAtExist.muV_eq s, PI.CompAtExist.muV_apply, AlgHom.commutes,
      GlobalTheory.Idele.valued_algebraMap]
  obtain ⟨ψ, hψc, hψ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.v s.w g hg
  have hcomp : ∀ y, φ (ψ y) = y := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) s.v).induction_on
      (p := fun y => φ (ψ y) = y) y (isClosed_eq (hφc.comp hψc) continuous_id) fun a => ?_
    rw [hψ]
    simp only [g, RingHom.comp_apply]
    rw [hφ]
    exact s.i.commutes a
  have hsurj : Function.Surjective φ := fun y => ⟨ψ y, hcomp y⟩
  let e := RingEquiv.ofBijective φ ⟨φ.injective, hsurj⟩
  have he : ∀ y, e.symm y = ψ y := fun y => e.injective (by rw [e.apply_symm_apply]; exact (hcomp y).symm)
  refine ⟨e.symm, ?_, ?_, fun x => ?_⟩
  · exact hψc.congr fun y => (he y).symm
  · exact hφc
  · have h := e.symm_apply_apply (algebraMap L (s.w.adicCompletion L) x)
    exact (congrArg e.symm (hφ x)).symm.trans h

end GlobalTheory.SplitCompl
end
