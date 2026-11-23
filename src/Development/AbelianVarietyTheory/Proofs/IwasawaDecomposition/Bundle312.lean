module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsJunkLiftNotVanishing
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle002
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle326
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle322
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqNegOfCommute
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle211
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle260
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.Bundle001
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle301
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.PrimesCongruentOne
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff Topology

namespace GlobalTheory.Mem.ThetaClosed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.WeilTieCheck GlobalTheory.FockCompare

variable {D : D7}

theorem exists_open_ker {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {ψ : AddChar (AF D.host.F) ℂ} (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) (φ : G →+ AF D.host.F)
    (hφ : Continuous φ) :
    ∃ K : AddSubgroup G, IsOpen (K : Set G) ∧ ∀ w ∈ K, fstA D.host.F (φ w) = 0 → ψ (φ w) = 1 := by
  let q : G →+ AF D.host.F :=
    (AddMonoidHom.inr (Ainf D.host.F) (Af D.host.F)).comp ((AddMonoidHom.snd (Ainf D.host.F) (Af D.host.F)).comp φ)
  let K : AddSubgroup G :=
    { carrier := {w | ψ (q w) = 1}
      zero_mem' := by
        show ψ _ = 1
        rw [map_zero, ψ.map_zero_eq_one]
      add_mem' := fun {a b} ha hb => by
        have ha' : ψ _ = 1 := ha
        have hb' : ψ _ = 1 := hb
        show ψ _ = 1
        rw [map_add (f := _), AddChar.map_add_eq_mul, ha', hb', one_mul]
      neg_mem' := fun {a} ha => by
        have ha' : ψ _ = 1 := ha
        show ψ _ = 1
        have := AddChar.map_add_eq_mul ψ (q a) (q (-a))
        rw [← map_add (f := _), add_neg_cancel, map_zero, ψ.map_zero_eq_one, ha', one_mul] at this
        exact this.symm }
  refine ⟨K, K.isOpen_of_mem_nhds (g := 0) ?_, fun w hw h0 => ?_⟩
  · have h1 : Continuous fun w : G => (φ w).2 := continuous_snd.comp hφ
    exact h1.continuousAt.preimage_mem_nhds (x := 0) (t := {a | ψ (pairA D.host.F 0 a) = 1})
      (by rw [map_zero]; exact GlobalTheory.FinTranslate.ker_mem_nhds hc hn)
  · have h4 : φ w = q w := Prod.ext h0 rfl
    rw [h4]
    exact hw

theorem isThetaFun_heis {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {f : WA V W → ℂ}
    (hf : IsThetaFun ψ V W f) (u : WA V W) : IsThetaFun ψ V W (Heisenberg₂ ψ V W u f) := by
  haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WA V W) := Pi.topologicalAddGroup
  have hc : Continuous ψ := hψ.1.1
  let φ₁ : WA V W →+ AF D.host.F := AddMonoidHom.mk' (fun w => symplH V W w u) fun a b => symplH_add_left V W a b u
  let φ₂ : WA V W →+ AF D.host.F := AddMonoidHom.mk' (fun w => symplH V W u w) fun a b => symplH_add_right V W u a b
  have c₁ : Continuous φ₁ := ThetaCont.continuous_symplH V W continuous_id continuous_const
  have c₂ : Continuous φ₂ := ThetaCont.continuous_symplH V W continuous_const continuous_id
  refine ⟨heis_quasi ψ V W u f hf.quasi, ?_, (hc.comp c₁).mul (hf.cont.comp (continuous_id.add continuous_const)),
    fun k L hL hLf w => ?_⟩
  · obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨K₁, hK₁, h₁⟩ := exists_open_ker hc hψ.1.2.1 φ₁ c₁
    obtain ⟨K₂, hK₂, h₂⟩ := exists_open_ker hc hψ.1.2.1 φ₂ c₂
    refine ⟨U ⊓ (K₁ ⊓ K₂), hU.inter (hK₁.inter hK₂), fun w hw hw' => ?_⟩
    have e₁ : ψ (symplH V W w u) = 1 := h₁ w hw.2.1 (by
      show fstA D.host.F (_ * sympl V W w u) = 0
      rw [map_mul, (sympl_parts D V W w u).2 (Or.inl hw'), mul_zero])
    have e₂ : ψ (symplH V W u w) = 1 := h₂ w hw.2.2 (by
      show fstA D.host.F (_ * sympl V W u w) = 0
      rw [map_mul, (sympl_parts D V W u w).2 (Or.inr hw'), mul_zero])
    conv_rhs => rw [← hUf w hw.1 hw']
    rw [heis_heis, heis_heis, e₁, e₂, add_comm]
  · obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
    let χ : (Fin k → ℝ) →+ ℂ := lam.comp (φ₁.comp L)
    have hχ : ContDiff ℝ ∞ χ := GlobalTheory.WeilVacMove.contDiff_additive χ (hl.comp (c₁.comp hL))
    have : (fun t => Heisenberg₂ ψ V W u f (w + L t)) =
        fun t => ψ (symplH V W w u) * Complex.exp (χ t) * f (w + u + L t) := by
      funext t
      have e : ψ (symplH V W (L t) u) = Complex.exp (χ t) := hlam _ (by
        show sndA D.host.F (_ * sympl V W (L t) u) = 0
        rw [map_mul, (sympl_parts D V W (L t) u).1 (Or.inl (hLf t)), mul_zero])
      rw [Heisenberg₂, symplH_add_left, AddChar.map_add_eq_mul, e, add_right_comm]
    rw [this]
    exact (contDiff_const.mul hχ.cexp).mul (hf.smooth k L hL hLf (w + u))

theorem thetaFun_closed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (f : WA V W → ℂ), (f ∈ ThS ψ V W ↔ IsThetaFun ψ V W f) ∧ (IsThetaFun ψ V W f → ∀ w₀, IsThetaFun ψ V W (Heisenberg₂ ψ V W w₀ f)) ∧ (V.rank ≠ W.rank → IsThetaFun ψ V W f → IsThetaFun ψ W V (fun x => f x.transpose)) := by
  intro D ψ hψ V W f
  refine ⟨⟨fun h => ?_, fun h => Submodule.subset_span h⟩, fun hf u => isThetaFun_heis hψ hf u,
    fun hne hf => isThetaFun_transpose ψ V W hne f hf⟩
  obtain ⟨M, hM⟩ := exists_thetaSubmodule D ψ V W
  exact (hM f).1 (Submodule.span_le.2 (fun g hg => (hM g).2 hg) h)

end GlobalTheory.Mem.ThetaClosed
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.WeilSwap

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.WeilTieCheck

variable {D : D7}

def trEquiv (ψ : AddChar (AF D.host.F) ℂ) {V W : HSp D} (hne : V.rank ≠ W.rank) : ThS ψ V W ≃ₗ[ℂ] ThS ψ W V where
  toFun Φ := ⟨fun y => Φ.1 y.transpose, mem_ThS.2 (isThetaFun_transpose ψ V W hne _ (mem_ThS.1 Φ.2))⟩
  invFun Φ := ⟨fun x => Φ.1 x.transpose, mem_ThS.2 (isThetaFun_transpose ψ W V hne.symm _ (mem_ThS.1 Φ.2))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem heis_transpose (ψ : AddChar (AF D.host.F) ℂ) {V W : HSp D} (hne : V.rank ≠ W.rank) (u : WA V W)
    (f : WA W V → ℂ) :
    (fun x : WA V W => Heisenberg₂ ψ W V u.transpose f x.transpose) = Heisenberg₂ ψ V W u (fun x => f x.transpose) := by
  funext x
  simp only [Heisenberg₂, symplH_transpose V W hne, Matrix.transpose_add]

def swapRep {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (hne : V.rank ≠ W.rank)
    (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)) : GA D W × GA D V →* Module.End ℂ (ThS ψ W V) :=
  ((trEquiv ψ hne).conjRingEquiv.toMonoidHom.comp om).comp (MulEquiv.prodComm (M := GA D W) (N := GA D V)).toMonoidHom

theorem swapRep_apply {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (hne : V.rank ≠ W.rank)
    (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)) (h : GA D W) (g : GA D V) (Φ : ThS ψ W V) :
    swapRep hne om (h, g) Φ = trEquiv ψ hne (om (g, h) ((trEquiv ψ hne).symm Φ)) := rfl

theorem exists_isWeilOn_swap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (χ χ' : IdC D) (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)), V.rank ≠ W.rank → IsWeilOn ψ V W χ χ' om → ∃ om' : GA D W × GA D V →* Module.End ℂ (ThS ψ W V), IsWeilOn ψ W V χ' χ om' ∧ ∀ (g : GA D V) (h : GA D W) (Φ : ThS ψ V W) (Φ' : ThS ψ W V), (∀ x : WA V W, Φ'.1 x.transpose = Φ.1 x) → ∀ x : WA V W, (om' (h, g) Φ').1 x.transpose = (om (g, h) Φ).1 x := by
  intro D ψ _ V W χ χ' om hne H
  refine ⟨swapRep hne om, ⟨fun h g w₀ Φ Φ' e => ?_, fun γ hγ γ' hγ' Φ => ?_, fun Φ w => ?_,
    fun μ 𝓕 hμ h𝓕 p Φ => ?_, fun e he h g hh hg y x hy hx => ?_⟩, fun g h Φ Φ' e x => ?_⟩
  · have k := H.Heisenberg₂ g h w₀.transpose ((trEquiv ψ hne).symm Φ) ((trEquiv ψ hne).symm Φ') (by
      show (fun x : WA V W => Φ'.1 x.transpose) = _
      rw [e]
      exact heis_transpose ψ hne w₀.transpose Φ.1)
    rw [swapRep_apply, swapRep_apply]
    show (fun y : WA W V => (om (g, h) _).1 y.transpose) = _
    rw [k, actHom_swap W V hne.symm]
    exact heis_transpose ψ hne.symm _ _
  · exact H.aut γ' hγ' γ hγ ((trEquiv ψ hne).symm Φ)
  · exact (H.cont ((trEquiv ψ hne).symm Φ) w.transpose).comp continuous_swap
  · haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
    haveI : IsTopologicalAddGroup (WA V W) := Pi.topologicalAddGroup
    haveI : IsTopologicalAddGroup (WA W V) := Pi.topologicalAddGroup
    haveI : BorelSpace (WA V W) := ⟨rfl⟩
    haveI : BorelSpace (WA W V) := ⟨rfl⟩
    obtain ⟨ν, h1, h2, h3⟩ := GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage (WA V W) (WA W V)
      (Matrix.transposeAddEquiv _ _ _) continuous_id.matrix_transpose continuous_id.matrix_transpose
      (ratL V W) (ratL W V) (fun x => ⟨fun ⟨γ, hγ⟩ => ⟨γ.transpose, congrArg Matrix.transpose hγ⟩,
        fun ⟨γ, hγ⟩ => ⟨γ.transpose, congrArg Matrix.transpose hγ⟩⟩) μ 𝓕 hμ h𝓕
    rw [← h3 fun w => ‖(swapRep hne om p Φ).1 w‖ ^ 2, ← h3 fun w => ‖Φ.1 w‖ ^ 2]
    exact H.unit ν _ h1 h2 (p.2, p.1) ((trEquiv ψ hne).symm Φ)
  · obtain ⟨r, hr, k⟩ := H.split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ Φ => ?_⟩
    rw [splitFac_swap V W hne]
    exact k (ℓ.comp (trEquiv ψ hne).toLinearMap) (fun u hu Ψ Ψ' e' =>
      hℓ u.transpose (fun i j => hu j i) (trEquiv ψ hne Ψ) (trEquiv ψ hne Ψ') (by
        show (fun y : WA W V => Ψ'.1 y.transpose) = _
        rw [e']
        exact heis_transpose ψ hne.symm u.transpose Ψ.1)) ((trEquiv ψ hne).symm Φ)
  · have : (trEquiv ψ hne).symm Φ' = Φ := Subtype.ext (funext e)
    rw [swapRep_apply, this]
    rfl

end GlobalTheory.Mem.WeilSwap

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Host Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.AntiChar

theorem exists_split_place (R : Ranks) (H : Formalism.BasicNotions.Host R) :
    ∃ w : HeightOneSpectrum (𝓞 H.E), ¬ GlobalTheory.Mem.Chr.ConjPl H.conj.toRingEquiv w w ∧
      ∃ p : ℕ, p.Prime ∧ Units.torsionOrder H.E + 1 < p ∧ (p : 𝓞 H.E) ∈ w.asIdeal := by
  obtain ⟨p, hp, hp2, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := H.QS * H.q * H.d) (Units.torsionOrder H.E + 1) H.condN_ne_zero
  have hs := GlobalTheory.Mem.Chr.splitsC_of_modEq_one R H p hp hmod
  have hne : {v : HeightOneSpectrum (𝓞 H.E) | ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hs]
    exact Module.finrank_pos.ne'
  obtain ⟨w, hw⟩ := hne
  obtain ⟨-, -, ⟨x, hx, hx'⟩, -⟩ := GlobalTheory.Mem.Chr.splitsC_main R H p hp hs w hw
  refine ⟨w, fun h => ?_, p, hp, hp2, hw⟩
  · have h' := (GlobalTheory.Mem.Chr.conjPl_main.2.1 R H w w).2 h
    let y : 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv x
    exact hx' y rfl ((h' x y rfl).1 hx)

theorem exists_hchar (R : Ranks) (H : Formalism.BasicNotions.Host R) (I : Type) [Fintype I] (e : I ≃ R.Psi) (z : I → ℤ) :
    ∃ χ : HChar H.E, χ.IsUnitary ∧ χ.TrivOn H.F ∧ χ.HasInf (fun i => embPsi H (e i)) (fun i => -2 * z i) ∧
      ∃ T : Finset (HeightOneSpectrum (𝓞 H.E)), ∀ v, v ∉ T → χ.UnrAt v := by
  classical
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hce : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  have hcm' : GlobalTheory.Mem.Chr.CMData H.F c (fun i => embPsi H (e i)) :=
    ⟨hcm.real, hcm.cplx, hcm.rank, hcm.ne, hcm.bij.comp e.bijective⟩
  obtain ⟨w, hw, p, hp, hp2, hpw⟩ := exists_split_place R H
  rw [← hce] at hw
  obtain ⟨ω, -, hω⟩ := UpperTheory.Mu.tame_par w hp hp2 hpw (fun i => embPsi H (e i)) (fun i => -z i)
  obtain ⟨w', -, hw'⟩ := GlobalTheory.Mem.Chr.conjPl_main.1 H.E c.toRingEquiv w
  let θ0 : ∀ v : HeightOneSpectrum (𝓞 H.E), (𝓞 H.E ⧸ v.asIdeal)ˣ →* ℂˣ :=
    Function.update (fun _ => 1) w ω
  obtain ⟨χ, hu, ht, hi, -, hunr, -⟩ := GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn H.F H.E c I _ hcm' z {w} θ0
    (by
      intro v hv v' h hv'
      rw [Finset.mem_singleton] at hv hv'
      subst hv hv'
      exact hw h)
    (fun ζ hζ => by
      rw [Finset.prod_singleton]
      simp only [θ0, Function.update_self]
      exact hω ζ hζ)
  refine ⟨χ, hu, ht, hi, {w, w'}, fun v hv => hunr v ?_ ?_⟩
  · intro h
    exact hv (by rw [Finset.mem_singleton.1 h]; simp)
  · intro u hu' h
    rw [Finset.mem_singleton.1 hu'] at h
    exact hv (by rw [hw' v h]; simp)

theorem val_fin_principal (D : D7) (c : IdC D) (χ : HChar D.host.E) (hc : ChrEq c χ)
    (T : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hT : ∀ v, v ∉ T → χ.UnrAt v) (k : D.host.Eˣ) (x : (AE D)ˣ)
    (h1 : infPart D (x : AE D) = 1) (h2 : finPart D (x : AE D) = finPart D (incA D k)) :
    ((χ.inf k : ℂˣ) : ℂ) * ((c x : Circle) : ℂ) = 1 := by
  classical
  obtain ⟨ι, i1, i2, i3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι i1 i2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι i1 i2 i3) c χ hc
  obtain ⟨S, -, -, hS⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)).toMonoidHom k)
  have hx : ∀ P, ι (finPart D (x : AE D)) P = algebraMap D.host.E (P.adicCompletion D.host.E) k := fun P => by
    rw [h2]
    exact congrArg (fun y : FiniteAdeleRing (𝓞 D.host.E) D.host.E => y P) (i1 k)
  have hS' : ∀ P, P ∉ S ∪ T → P.valuation D.host.E (k : D.host.E) = 1 ∧ (N : 𝓞 D.host.E) ∉ P.asIdeal := fun P hP => by
    have := hS P fun h => hP (Finset.mem_union_left _ h)
    exact ⟨(GlobalTheory.BaseIdeleTriv.val_algebraMap P (k : D.host.E)).symm.trans this.1, this.2⟩
  have h3 := hprod x h1 (S ∪ T) (fun _ => k)
    (fun P _ => ⟨by rw [hx, GlobalTheory.BaseIdeleTriv.val_algebraMap], by rw [hx, sub_self, map_zero]; exact zero_le⟩)
    (fun P hP => ⟨by rw [hx, GlobalTheory.BaseIdeleTriv.val_algebraMap]; exact (hS' P hP).1, (hS' P hP).2⟩)
  have h4 := GlobalTheory.HeckeProduct.hchar_productRule D.host.E χ (S ∪ T)
    (fun v hv => hT v fun h => hv (Finset.mem_union_right _ h)) k
  have h5 : (∏ᶠ (v : HeightOneSpectrum (𝓞 D.host.E)) (_ : v ∉ S ∪ T), χ.val v ^ ordF v k) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => (finprod_congr fun hv => by
      show χ.val v ^ ordF v k = 1
      rw [ordF, (hS' v hv).1]; simp).trans finprod_one
  rw [h5, mul_one] at h4
  rw [h3, ← Units.coe_prod, ← Units.val_mul, h4, Units.val_one]



open GlobalTheory.FockCompare in
theorem val_inf (D : D7) [Fintype D.what₂.Tau] (c : IdC D) (χ : HChar D.host.E) (hc : ChrEq c χ)
    (T : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hT : ∀ v, v ∉ T → χ.UnrAt v) (n : D.what₂.Tau → ℤ)
    (hn : χ.HasInf (tauE D) n) (θ : InfF D) (hθ : IsInfFam θ) (x : (AE D)ˣ) (hx : finPart D (x : AE D) = 1) :
    ((c x : Circle) : ℂ) = ∏ τ, (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ n τ := by
  obtain ⟨s, hs⟩ := GlobalTheory.FockCompare.exists_chart hθ
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  have tc : Continuous t :=
    (hs.cont.comp (continuous_pi fun τ => Units.continuous_val.comp (continuous_apply τ))).add continuous_const
  let U : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have Uc : Continuous U.toHomUnits := Units.continuous_iff.2 ⟨tc, tc.comp continuous_inv⟩
  have hU : ∀ y : (AE D)ˣ, finPart D (y : AE D) = 1 →
      y = U.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom y := fun y hy =>
    Units.ext (ext _ _ (hy.trans (tf _).symm) fun τ =>
      (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom y) τ).symm)
  have hd : DenseRange fun (k : D.host.E) τ => tauE D τ k := by
    intro z
    have := GlobalTheory.HeckeFinTrivial.mem_closure_range (tauE D) θ (fun τ => (hθ τ).1) (fun τ => (hθ τ).2) (infPart D (s z))
    rwa [show (fun i => θ i (infPart D (s z))) = z from funext fun τ => hs.comp z τ] at this
  have key : ∀ z : D.what₂.Tau → ℂˣ, ((c (U.toHomUnits z) : Circle) : ℂ) = ∏ τ, ((z τ : ℂ) / (‖(z τ : ℂ)‖ : ℂ)) ^ n τ := by
    intro z
    refine (GlobalTheory.HeckeFinTrivial.denseRange_units (tauE D) hd).induction_on z
      (isClosed_eq (continuous_subtype_val.comp (hc.1.1.comp Uc)) ?_) fun k => ?_
    · refine continuous_finsetProd _ fun τ _ => ?_
      have h1 : Continuous fun z : D.what₂.Tau → ℂˣ => (z τ : ℂ) := Units.continuous_val.comp (continuous_apply τ)
      have h3 : ∀ z : D.what₂.Tau → ℂˣ, (‖(z τ : ℂ)‖ : ℂ) ≠ 0 := fun z => by
        exact_mod_cast norm_ne_zero_iff.2 (z τ).ne_zero
      exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h3).zpow₀ _
        fun z => Or.inl (div_ne_zero (z τ).ne_zero (h3 z))
    · let y : (AE D)ˣ := Units.map (incA D).toMonoidHom k
      have e1 : a y = U.toHomUnits fun τ => Units.map (tauE D τ).toMonoidHom k := by
        rw [hU (a y) (ha y).2]
        congr 1
        funext τ
        exact Units.ext ((congrArg (θ τ) (ha y).1).trans ((hθ τ).1 k))
      have e2 := val_fin_principal D c χ hc T hT k (b y) (hb y).1 (hb y).2
      have e3 : c (a y) * c (b y) = 1 := by rw [← map_mul, ← hab y]; exact hc.1.2 k
      have e4 : ((c (a y) : Circle) : ℂ) * ((c (b y) : Circle) : ℂ) = 1 := by rw [← Circle.coe_mul, e3, Circle.coe_one]
      rw [← e1]
      exact (mul_right_cancel₀ (Circle.coe_ne_zero _) (e4.trans e2.symm)).trans (hn k)
  exact (congrArg (fun y => ((c y : Circle) : ℂ)) (hU x hx)).trans (key _)

theorem sign_zpow_even {w : ℂ} (hw : starRingEnd ℂ w = w) (h0 : w ≠ 0) (m : ℤ) : (w / (‖w‖ : ℂ)) ^ (-2 * m) = 1 := by
  have h1 : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
  have h2 : (w / (‖w‖ : ℂ)) ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, div_pow, ← Complex.mul_conj', hw, sq]
    exact div_self (mul_ne_zero h0 h0)
  rw [show -2 * m = 2 * -m by ring, _root_.zpow_mul, h2, _root_.one_zpow]



theorem exists_char : ∀ (D : D7) (j : Fin D.R.m),
    ∃ χ : IdC D, IsHeckeChar D χ ∧ (∀ τ, HasInfExp D χ τ (-(D.hc τ).e j)) ∧ ResEta D χ 0 := by
  intro D j
  classical
  letI : Fintype D.what₂.Tau := Fintype.ofEquiv _ D.eTau.symm
  choose z hz using fun τ => (D.hc τ).e_int j
  obtain ⟨χ, hu, ht, hi, T, hT⟩ := exists_hchar D.R D.host D.what₂.Tau D.eTau z
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_cmAdeleUnitCharacter_reading_heckeChar D χ hu
  have hv := val_inf D c χ hc T hT _ hi
  obtain ⟨θ₀, hθ₀⟩ := GlobalTheory.Member.exists_isInfFam_family D
  refine ⟨c, hc.1, fun τ => ⟨-2 * z τ, by rw [hz]; push_cast; ring, ⟨θ₀, hθ₀⟩, fun θ hθ x h1 h2 => ?_⟩,
    GlobalTheory.VolHeckeCompare.exists_isEta D, fun η _ a => ?_⟩
  · rw [hv θ hθ x h1, Finset.prod_eq_single τ (fun τ' _ h => by rw [h2 τ' h]; simp) (by simp)]
  · let p : AF D.host.F →* AF D.host.F := (MonoidHom.inl (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.fst (Ainf D.host.F) (Af D.host.F))
    let q : AF D.host.F →* AF D.host.F := (MonoidHom.inr (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.snd (Ainf D.host.F) (Af D.host.F))
    have e : a = Units.map p a * Units.map q a := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    have e1 : c (idF D (Units.map q a)) = 1 := GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial D c χ hc ht _ rfl
    have e2 : c (idF D (Units.map p a)) = 1 := by
      apply Circle.ext
      rw [hv θ₀ hθ₀ _ rfl, Circle.coe_one]
      refine Finset.prod_eq_one fun τ _ => sign_zpow_even (GlobalTheory.FockCompare.conj_tmul_one hθ₀ τ _) ?_ _
      exact (Units.map ((θ₀ τ).comp (infPart D)).toMonoidHom (idF D (Units.map p a))).ne_zero
    rw [pow_zero, e, map_mul, map_mul, e1, e2, one_mul]

end GlobalTheory.Mem.AntiChar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.SchurTensor

theorem ellT_inclT_tprod {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : ∀ τ, M.H τ) (v : M.Vec) :
    ellT M w (inclT M (PiTensorProduct.tprod ℂ v)) = ∏ τ, ⟪w τ, (v τ : M.H τ)⟫_ℂ := by
  simp [ellT, inclT]

theorem schur_tensor : ∀ (D : D7) (θ : InfF D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurMult θ M J χ μ 𝓕 → IsInfFam θ → IsQuot V μ 𝓕 → ∀ x ∈ MultT θ M J χ, ∀ y ∈ MultT θ M J χ, ∀ (v : SmT M) (w : M.Vec), IsCuspForm θ V (y (PiTensorProduct.tprod ℂ w)) ∧ IntegrableOn (fun g => star (x v g) * y (PiTensorProduct.tprod ℂ w) g) 𝓕 μ ∧ ∫ g in 𝓕, star (x v g) * y (PiTensorProduct.tprod ℂ w) g ∂μ = ipT M μ 𝓕 y x * star (ellT M (fun τ => (w τ : M.H τ)) (inclT M v)) := by
  intro D θ V S M J χ μ 𝓕 hS hθ hq x hx y hy v w
  have hx' := (mem_multT θ M J χ x).1 hx
  have hy' := (mem_multT θ M J χ y).1 hy
  have hm := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ _).1 hy'
  have hI := ipM_spec M μ 𝓕 _ _ (hS hθ hq.1 hq.2 _ hx' _ hy')
  refine ⟨⟨hm.aut w, hm.cusp w⟩, ?_⟩
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c u =>
    obtain ⟨h1, h2⟩ := hI u w
    have e : (fun g => star (x (c • PiTensorProduct.tprod ℂ u) g) * y (PiTensorProduct.tprod ℂ w) g) =
        fun g => star c * (star (x (PiTensorProduct.tprod ℂ u) g) * y (PiTensorProduct.tprod ℂ w) g) := by
      funext g
      rw [map_smul, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]
    rw [e]
    refine ⟨h1.const_mul _, ?_⟩
    rw [integral_const_mul, map_smul, map_smul, ellT_inclT_tprod, smul_eq_mul, star_mul', star_prod]
    refine (congrArg (star c * ·) h2).trans ?_
    have e2 : ∏ τ, star ⟪(w τ : M.H τ), (u τ : M.H τ)⟫_ℂ = ∏ τ, ⟪(u τ : M.H τ), (w τ : M.H τ)⟫_ℂ :=
      Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _
    rw [e2, ipT]
    ring
  | add a b ha hb =>
    have e : (fun g => star (x (a + b) g) * y (PiTensorProduct.tprod ℂ w) g) =
        fun g => star (x a g) * y (PiTensorProduct.tprod ℂ w) g + star (x b g) * y (PiTensorProduct.tprod ℂ w) g := by
      funext g
      rw [map_add (f := _), Pi.add_apply, star_add, add_mul]
    rw [e]
    refine ⟨ha.1.add hb.1, ?_⟩
    rw [integral_add ha.1 hb.1, ha.2, hb.2, map_add (f := _), map_add (f := _), star_add, mul_add]

end GlobalTheory.Mem.SchurTensor
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.exists_definiteUnitaryInfinitePoint_of_unitary_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : InfinitePlace E → GL (Fin n) ℂ), (∀ v, ((g v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ x ∈ infU E n, cAll x = g := by
  first | exact @GlobalTheory.InfSurj.exists_infU_cAll_eq | exact GlobalTheory.InfSurj.exists_infU_cAll_eq | (intros; apply GlobalTheory.InfSurj.exists_infU_cAll_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.iSup_range_weightMaps_eq_top_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (τ : E →+* ℂ) (lam : DomWeight n), HasWeightAt π.V τ lam → (⨆ f : Representation.IntertwiningMap ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) (π.rep.comp (embU n τ).subtype), LinearMap.range f.toLinearMap) = ⊤ := by
  first | exact @GlobalTheory.DefU.iSup_range_weight_eq_top | exact GlobalTheory.DefU.iSup_range_weight_eq_top | (intros; apply GlobalTheory.DefU.iSup_range_weight_eq_top <;> assumption)
end
